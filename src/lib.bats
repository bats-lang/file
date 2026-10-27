(* file -- POSIX file I/O with linear type safety *)
(* Linear fd must be closed exactly once. Reads/writes through arrays. *)
(* Returns result/option types -- errors cannot be ignored. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R

(* ============================================================
   C syscall wrappers (the entire unsafe surface)
   ============================================================ *)

$UNSAFE begin
%{#
#ifndef _FILE_RUNTIME_DEFINED
#define _FILE_RUNTIME_DEFINED
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <dirent.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <limits.h>
#include <sys/file.h>

/* file's own code for an errno (io_error's, decoded once by _io_error
   below): errno's numbers differ between systems (EAGAIN is 11 on Linux
   and 35 on macOS), so they are named here, by their macros. */
static int _file_error_code(int e) {
  switch (e) {
    case ENOENT: return 1;
    case EACCES: case EPERM: return 2;
    case EEXIST: return 3;
    case ENOTDIR: return 4;
    case EISDIR: return 5;
    case ENOTEMPTY: return 6;
    case EROFS: return 7;
    case ELOOP: return 8;
    case ENAMETOOLONG: return 9;
    case EINVAL: return 10;
    case EFBIG: case EOVERFLOW: return 11;
    case ENOSPC:
#ifdef EDQUOT
    case EDQUOT:
#endif
      return 12;
    case EMFILE: case ENFILE: return 13;
    case ENOMEM: return 14;
    case EBUSY: case ETXTBSY: return 15;
    case EPIPE: return 16;
    case EAGAIN:
#if defined(EWOULDBLOCK) && EWOULDBLOCK != EAGAIN
    case EWOULDBLOCK:
#endif
      return 17;
    case EBADF: return 18;
    case EIO: return 19;
    case ENOTSUP:
#if defined(EOPNOTSUPP) && EOPNOTSUPP != ENOTSUP
    case EOPNOTSUPP:
#endif
      return 20;
    case EXDEV: return 21;
    default: return 22;
  }
}
/* The failure errno names, as a negative result */
static int _file_failed(int e) {
  return -_file_error_code(e);
}
/* access and opening are file's own codes, encoded once by
   _access_code and _opening_code below; the host's O_* bits differ
   between systems (O_CREAT is 64 on Linux, 512 on macOS and the BSDs),
   so they are translated here. */
static int _file_open(const char *path, int access, int opening, int mode) {
  int f;
  int fd;
  switch (access) {
    case 0: f = O_RDONLY; break;
    case 1: f = O_WRONLY; break;
    default: f = O_RDWR; break;
  }
  switch (opening) {
    case 0: break;
    case 1: f |= O_CREAT; break;
    case 2: f |= O_CREAT | O_TRUNC; break;
    case 3: f |= O_CREAT | O_APPEND; break;
    case 4: f |= O_TRUNC; break;
    default: f |= O_APPEND; break;
  }
  fd = open(path, f, mode);
  return fd >= 0 ? fd : _file_failed(errno);
}
/* Reads until len bytes or EOF; a failure before any byte is -errno,
   after some bytes those bytes: the next read reports it. EINTR is
   retried, as the readers of Rust do. */
static int _file_read(int fd, void *buf, int len) {
  int total = 0;
  while (total < len) {
    int n = (int)read(fd, (char *)buf + total, (unsigned int)(len - total));
    if (n < 0 && errno == EINTR) continue;
    if (n < 0) return total > 0 ? total : _file_failed(errno);
    if (n == 0) break;
    total += n;
  }
  return total;
}
/* Writes all len bytes (as Rust's write_all): len, or -errno of the
   write that failed. EINTR is retried. */
static int _file_write(int fd, const void *buf, int len) {
  int total = 0;
  while (total < len) {
    int n = (int)write(fd, (const char *)buf + total, (unsigned int)(len - total));
    if (n < 0 && errno == EINTR) continue;
    if (n < 0) return _file_failed(errno);
    if (n == 0) return _file_failed(EIO);
    total += n;
  }
  return total;
}
static int _file_close(int fd) {
  return close(fd) == 0 ? 0 : _file_failed(errno);
}
/* A size that does not fit an int is EFBIG, not a truncated value. */
static int _file_size_of(const struct stat *st) {
  if (st->st_size < 0 || st->st_size > 2147483647) return _file_failed(EFBIG);
  return (int)st->st_size;
}
static int _file_stat_size(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) return _file_failed(errno);
  return _file_size_of(&st);
}
/* The next read of fd is at offset off from the start */
static int _file_seek(int fd, int off) {
  return lseek(fd, (off_t)off, SEEK_SET) < 0 ? _file_failed(errno) : 0;
}
static int _file_fd_size(int fd) {
  struct stat st;
  if (fstat(fd, &st) != 0) return _file_failed(errno);
  return _file_size_of(&st);
}
/* The code of the last failure of a call that returns a pointer (null
   when it fails): opendir and dir_read */
static int _file_last_failure = 0;
static int _file_last_failed(void) {
  return -_file_last_failure;
}
static void *_file_opendir(const char *path) {
  void *d = (void *)opendir(path);
  if (!d) _file_last_failure = _file_error_code(errno);
  return d;
}
static int _file_closedir(void *dirp) {
  return closedir(dirp) == 0 ? 0 : _file_failed(errno);
}
/* All of a directory's entries, read in one pass and sorted by name
   (bytewise, a prefix before its extensions), so walks over them are
   bounded and in the same order on every system. */
typedef struct { char *name; int len; } _file_entry_t;
typedef struct { int n; _file_entry_t *es; } _file_entries_t;
static int _file_entry_cmp(const void *x, const void *y) {
  const _file_entry_t *a = (const _file_entry_t *)x;
  const _file_entry_t *b = (const _file_entry_t *)y;
  int m = a->len < b->len ? a->len : b->len;
  int c = memcmp(a->name, b->name, m);
  if (c != 0) return c;
  return a->len - b->len;
}
static void _file_entries_free(void *p);
/* Null when the directory cannot be opened or read, or when memory for
   its entries cannot be had (_file_last_failure says which); everything
   allocated so far is freed. */
static void *_file_dir_read(const char *path) {
  DIR *d = opendir(path);
  _file_entries_t *r;
  struct dirent *e;
  int cap = 16;
  if (!d) { _file_last_failure = _file_error_code(errno); return (void *)0; }
  _file_last_failure = _file_error_code(ENOMEM);
  r = (_file_entries_t *)malloc(sizeof(_file_entries_t));
  if (!r) { closedir(d); return (void *)0; }
  r->n = 0;
  r->es = (_file_entry_t *)malloc((size_t)cap * sizeof(_file_entry_t));
  if (!r->es) { free(r); closedir(d); return (void *)0; }
  for (;;) {
    int len;
    char *s;
    errno = 0;
    e = readdir(d);
    if (!e) break;
    if (r->n == cap) {
      _file_entry_t *es;
      if ((size_t)cap > ((size_t)INT_MAX / 2) / sizeof(_file_entry_t)) goto fail;
      es = (_file_entry_t *)realloc(r->es, 2 * (size_t)cap * sizeof(_file_entry_t));
      if (!es) goto fail;
      r->es = es;
      cap = 2 * cap;
    }
    len = (int)strlen(e->d_name);
    s = (char *)malloc(len > 0 ? (size_t)len : 1);
    if (!s) goto fail;
    memcpy(s, e->d_name, (size_t)len);
    r->es[r->n].name = s;
    r->es[r->n].len = len;
    r->n++;
  }
  /* readdir returns null at the end and on an error, which sets errno. */
  if (errno != 0) { _file_last_failure = _file_error_code(errno); goto fail; }
  closedir(d);
  qsort(r->es, (size_t)r->n, sizeof(_file_entry_t), _file_entry_cmp);
  return (void *)r;
fail:
  closedir(d);
  _file_entries_free(r);
  return (void *)0;
}
static int _file_entries_count(void *p) {
  return ((_file_entries_t *)p)->n;
}
/* A name is NUL-terminated inside d_name, so strlen(d_name) is less
   than sizeof(d_name), which is at most ENTRY_NAME_MAX (1024) on every
   host we build for (Linux and the BSDs 256, NetBSD 512, macOS 1024);
   a host with a larger or flexible d_name fails to compile here.
   entries_name's buffer holds ENTRY_NAME_MAX bytes, so a name always
   fits. */
_Static_assert(sizeof(((struct dirent *)0)->d_name) <= 1024,
  "d_name must fit ENTRY_NAME_MAX");
static int _file_entries_name(void *p, int i, char *name_buf) {
  _file_entry_t *e = &((_file_entries_t *)p)->es[i];
  memcpy(name_buf, e->name, e->len);
  return e->len;
}
static void _file_entries_free(void *p) {
  _file_entries_t *r = (_file_entries_t *)p;
  int i;
  for (i = 0; i < r->n; i++) free(r->es[i].name);
  free(r->es);
  free(r);
}
static int _file_ptr_nonnull(void *p) {
  return p != (void*)0 ? 1 : 0;
}
static int _file_chdir(const char *path) {
  return chdir(path) == 0 ? 0 : _file_failed(errno);
}
/* 0, with the modification time (seconds since 1970, which may be
   before it) in *mtime, or the failure */
static int _file_mtime(const char *path, int *mtime) {
  struct stat st;
  if (stat(path, &st) != 0) return _file_failed(errno);
  if (st.st_mtime > 2147483647 || st.st_mtime < -2147483647 - 1) return _file_failed(EOVERFLOW);
  *mtime = (int)st.st_mtime;
  return 0;
}
static int _file_exists(const char *path) {
  struct stat st;
  return stat(path, &st) == 0 ? 1 : 0;
}
/* The permission bits (st_mode & 07777) of path, or the failure. */
static int _file_mode(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) return _file_failed(errno);
  return (int)(st.st_mode & 07777);
}
/* 0, or the failure. */
static int _file_chmod(const char *path, int mode) {
  return chmod(path, (mode_t)mode) == 0 ? 0 : _file_failed(errno);
}
static int _file_mkdir(const char *path, int mode) {
  return mkdir(path, mode) == 0 ? 0 : _file_failed(errno);
}
/* flock(2) on fd: kind 0 shared, 1 exclusive; wait 0 waits until the
   lock is free, 1 fails at once (EWOULDBLOCK) when another open file
   holds a lock that conflicts. EINTR is retried. 0, or the failure. */
static int _file_lock(int fd, int kind, int wait) {
  int op = kind == 0 ? LOCK_SH : LOCK_EX;
  if (wait != 0) op |= LOCK_NB;
  while (flock(fd, op) != 0) {
    if (errno != EINTR) return _file_failed(errno);
  }
  return 0;
}
/* Releases fd's flock(2) lock: 0, or the failure. */
static int _file_unlock(int fd) {
  while (flock(fd, LOCK_UN) != 0) {
    if (errno != EINTR) return _file_failed(errno);
  }
  return 0;
}
/* ---- Renaming, removing, links and status (keyword: remove-rename) ---- */

/* rename(2): atomic when both paths are on one file system; 0, or the
   failure (EXDEV across file systems, ENOTEMPTY, ...). */
static int _file_rename(const char *from, const char *to) {
  return rename(from, to) == 0 ? 0 : _file_failed(errno);
}
/* Removes the file or empty directory at path and never follows a
   symlink (a link is unlinked, not its target): 1 for a file or link,
   2 for an empty directory, or the failure. */
static int _file_remove(const char *path) {
  struct stat st;
  if (lstat(path, &st) != 0) return _file_failed(errno);
  if (S_ISDIR(st.st_mode)) return rmdir(path) == 0 ? 2 : _file_failed(errno);
  return unlink(path) == 0 ? 1 : _file_failed(errno);
}
static int _file_symlink(const char *target, const char *path) {
  return symlink(target, path) == 0 ? 0 : _file_failed(errno);
}
/* The target of the symlink at path in buf[0, cap): the number of bytes
   (less than cap), cap when the target has cap bytes or more (it may be
   cut), -100 when path is not a symlink (readlink's EINVAL), or the
   failure. */
static int _file_readlink(const char *path, char *buf, int cap) {
  ssize_t n = readlink(path, buf, (size_t)cap);
  if (n < 0) return errno == EINVAL ? -100 : _file_failed(errno);
  return (int)n;
}
/* What lstat(2) says of path (a symlink is not followed): 0 with the
   kind (0 regular file, 1 directory, 2 symlink, 3 anything else), the
   size, the permission bits (st_mode & 07777) and the owner's user id in
   the four outputs, or the failure; EFBIG/EOVERFLOW when the size or the
   owner does not fit an int. */
static int _file_lstat(const char *path, int *kind, int *size, int *mode, int *owner) {
  struct stat st;
  if (lstat(path, &st) != 0) return _file_failed(errno);
  if (st.st_size < 0 || st.st_size > 2147483647) return _file_failed(EFBIG);
  if ((unsigned long long)st.st_uid > 2147483647ULL) return _file_failed(EOVERFLOW);
  *kind = S_ISREG(st.st_mode) ? 0 : S_ISDIR(st.st_mode) ? 1 : S_ISLNK(st.st_mode) ? 2 : 3;
  *size = (int)st.st_size;
  *mode = (int)(st.st_mode & 07777);
  *owner = (int)st.st_uid;
  return 0;
}
/* Whether the directory at path (not a symlink to one) has no entry
   but . and ..: 1 empty, 0 has entries, 2 not a directory, or the
   failure. */
static int _file_dir_empty(const char *path) {
  struct stat st;
  DIR *d;
  struct dirent *e;
  int empty = 1;
  if (lstat(path, &st) != 0) return _file_failed(errno);
  if (!S_ISDIR(st.st_mode)) return 2;
  d = opendir(path);
  if (!d) return _file_failed(errno);
  for (;;) {
    errno = 0;
    e = readdir(d);
    if (!e) break;
    if (strcmp(e->d_name, ".") != 0 && strcmp(e->d_name, "..") != 0) { empty = 0; break; }
  }
  if (e == (struct dirent *)0 && errno != 0) {
    int saved = errno;
    closedir(d);
    return _file_failed(saved);
  }
  closedir(d);
  return empty;
}
/* mkdir -p: every missing directory of path is made, the last with
   mode and the ones before it with mode | 0300 (as mkdir -p, so the
   walk can go on); one that exists as a directory is left as it is. 0
   with the number made in *created, or the failure (the directories
   made before it stay). EEXIST when a name is there and is not a
   directory. */
static int _file_mkdir_one(char *path, int mode, int *created) {
  struct stat st;
  if (mkdir(path, (mode_t)mode) == 0) { (*created)++; return 0; }
  if (errno == EEXIST && stat(path, &st) == 0 && S_ISDIR(st.st_mode)) return 0;
  return _file_failed(errno);
}
static int _file_mkdirs(const char *path, int mode, int *created) {
  size_t len = strlen(path);
  char *copy = (char *)malloc(len + 1);
  size_t i = 0;
  int r = 0;
  *created = 0;
  if (!copy) return _file_failed(ENOMEM);
  memcpy(copy, path, len + 1);
  while (i < len && copy[i] == '/') i++;
  for (; i < len; i++) {
    if (copy[i] == '/') {
      copy[i] = '\0';
      r = _file_mkdir_one(copy, mode | 0300, created);
      copy[i] = '/';
      if (r != 0) { free(copy); return r; }
    }
  }
  r = _file_mkdir_one(copy, mode, created);
  free(copy);
  return r;
}
/* mkdtemp(3) on prefix (n bytes) followed by XXXXXX: the directory is
   made with mode 0700 and its path, n + 6 bytes, is copied to out. 0, or
   the failure. */
static int _file_mkdtemp(const char *prefix, int n, char *out) {
  char *t = (char *)malloc((size_t)n + 7);
  if (!t) return _file_failed(ENOMEM);
  memcpy(t, prefix, (size_t)n);
  memcpy(t + n, "XXXXXX", 7);
  if (!mkdtemp(t)) { int saved = errno; free(t); return _file_failed(saved); }
  memcpy(out, t, (size_t)n + 6);
  free(t);
  return 0;
}

/* remove_tree (keyword: remove-tree). The walk uses descriptors
   (openat, fstatat, unlinkat with O_NOFOLLOW and AT_SYMLINK_NOFOLLOW), so
   a symlink is unlinked and never entered, and a directory swapped for
   a link during the walk is not followed. A directory on another
   device than the top's is a mount point: it is neither entered nor
   removed. Failures do not stop the walk: each is counted, the first is
   kept. A directory is passed again while a pass removes something, and
   only its last pass counts failures and mounts, so none is counted twice. */
typedef struct { int removed; int kept; int mounts; int first; dev_t dev; } _file_tree_t;
#define _FILE_TREE_DEPTH 256
static void _file_tree_count(int *n) { if (*n < 2147483647) (*n)++; }
static void _file_tree_failed(_file_tree_t *t, int e) {
  _file_tree_count(&t->kept);
  if (t->first == 0) t->first = _file_error_code(e);
}
/* Removes what is inside the directory dfd names; takes dfd (closes it). */
static void _file_tree_empty(_file_tree_t *t, int dfd, int depth) {
  DIR *d = fdopendir(dfd);
  int progress;
  int kept0 = t->kept, mounts0 = t->mounts, first0 = t->first;
  if (!d) { _file_tree_failed(t, errno); close(dfd); return; }
  do {
    struct dirent *e;
    progress = 0;
    /* a pass counts afresh: what failed or was a mount in the last pass is what is left */
    t->kept = kept0; t->mounts = mounts0; t->first = first0;
    rewinddir(d);
    for (;;) {
      struct stat st;
      errno = 0;
      e = readdir(d);
      if (!e) {
        if (errno != 0) _file_tree_failed(t, errno);
        break;
      }
      if (strcmp(e->d_name, ".") == 0 || strcmp(e->d_name, "..") == 0) continue;
      if (fstatat(dirfd(d), e->d_name, &st, AT_SYMLINK_NOFOLLOW) != 0) {
        if (errno != ENOENT) _file_tree_failed(t, errno);
        continue;
      }
      if (S_ISDIR(st.st_mode)) {
        int cfd;
        struct stat cst;
        int clean;
        if (st.st_dev != t->dev) { _file_tree_count(&t->mounts); continue; }
        if (depth >= _FILE_TREE_DEPTH) { _file_tree_failed(t, ENAMETOOLONG); continue; }
        cfd = openat(dirfd(d), e->d_name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW);
        if (cfd < 0) { if (errno != ENOENT) _file_tree_failed(t, errno); continue; }
        if (fstat(cfd, &cst) != 0) { _file_tree_failed(t, errno); close(cfd); continue; }
        if (cst.st_dev != t->dev) { _file_tree_count(&t->mounts); close(cfd); continue; }
        {
          int kept_before = t->kept, mounts_before = t->mounts;
          _file_tree_empty(t, cfd, depth + 1);
          clean = (t->kept == kept_before && t->mounts == mounts_before);
        }
        if (clean) {
          if (unlinkat(dirfd(d), e->d_name, AT_REMOVEDIR) == 0) { _file_tree_count(&t->removed); progress = 1; }
          else if (errno != ENOENT) _file_tree_failed(t, errno);
        }
      } else {
        if (unlinkat(dirfd(d), e->d_name, 0) == 0) { _file_tree_count(&t->removed); progress = 1; }
        else if (errno != ENOENT) _file_tree_failed(t, errno);
      }
    }
  } while (progress);
  closedir(d);
}
/* 1 when path (trailing slashes ignored) names the root or nothing,
   2 when its last name is . or .., else 0: remove_tree refuses these. */
static int _file_tree_refused(const char *path) {
  size_t len = strlen(path);
  size_t start;
  while (len > 0 && path[len - 1] == '/') len--;
  if (len == 0) return 1;
  start = len;
  while (start > 0 && path[start - 1] != '/') start--;
  if (len - start == 1 && path[start] == '.') return 2;
  if (len - start == 2 && path[start] == '.' && path[start + 1] == '.') return 2;
  return 0;
}
/* 0 with the counts (the top included) in the outputs, 1 nothing at
   path, 2 or 3 refused (_file_tree_refused's 1 and 2), or the failure. */
static int _file_remove_tree(const char *path, int *removed, int *kept, int *mounts, int *first) {
  _file_tree_t t;
  struct stat st, up;
  int fd;
  int refused = _file_tree_refused(path);
  t.removed = 0; t.kept = 0; t.mounts = 0; t.first = 0;
  *removed = 0; *kept = 0; *mounts = 0; *first = 0;
  if (refused != 0) return refused + 1;
  if (lstat(path, &st) != 0) return errno == ENOENT ? 1 : _file_failed(errno);
  if (!S_ISDIR(st.st_mode)) {
    if (unlink(path) == 0) t.removed = 1; else _file_tree_failed(&t, errno);
  } else {
    t.dev = st.st_dev;
    fd = open(path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW);
    if (fd < 0) _file_tree_failed(&t, errno);
    else if (fstatat(fd, "..", &up, 0) == 0 && up.st_dev != st.st_dev) {
      /* the top is itself a mount point: left alone */
      _file_tree_count(&t.mounts);
      close(fd);
    } else {
      _file_tree_empty(&t, fd, 0);
      if (t.kept == 0 && t.mounts == 0) {
        if (rmdir(path) == 0) _file_tree_count(&t.removed); else _file_tree_failed(&t, errno);
      }
    }
  }
  *removed = t.removed; *kept = t.kept; *mounts = t.mounts; *first = t.first;
  return 0;
}
#endif
%}
end

(* ============================================================
   How a file is opened, and why an operation failed
   ============================================================ *)

(* What a file is opened for *)
#pub datatype access =
  | ReadOnly
  | WriteOnly
  | ReadWrite

(* What opening does when the file is missing or has bytes: open it as
   it is (it must exist); create it when missing; create it when missing
   and empty it when not; create it when missing and write at its end;
   empty it (it must exist); write at its end (it must exist) *)
#pub datatype opening =
  | OpenExisting
  | CreateOrOpen
  | CreateOrTruncate
  | CreateOrAppend
  | TruncateExisting
  | AppendExisting

(* Why an operation failed: the kinds of errno, named as Rust's
   io::ErrorKind names them (an errno is a different number on each
   system, so it is not kept). Unrecognized is any other errno. *)
#pub datatype io_error =
  | NotFound            (* ENOENT *)
  | PermissionDenied    (* EACCES, EPERM *)
  | AlreadyExists       (* EEXIST *)
  | NotADirectory       (* ENOTDIR *)
  | IsADirectory        (* EISDIR *)
  | DirectoryNotEmpty   (* ENOTEMPTY *)
  | ReadOnlyFilesystem  (* EROFS *)
  | FilesystemLoop      (* ELOOP *)
  | InvalidFilename     (* ENAMETOOLONG *)
  | InvalidInput        (* EINVAL *)
  | FileTooLarge        (* EFBIG, EOVERFLOW: a size or time past an int *)
  | StorageFull         (* ENOSPC, EDQUOT *)
  | TooManyOpenFiles    (* EMFILE, ENFILE *)
  | OutOfMemory         (* ENOMEM *)
  | ResourceBusy        (* EBUSY, ETXTBSY *)
  | BrokenPipe          (* EPIPE *)
  | WouldBlock          (* EAGAIN *)
  | BadDescriptor       (* EBADF *)
  | DeviceError         (* EIO *)
  | Unsupported         (* ENOTSUP *)
  | CrossesDevices      (* EXDEV *)
  | Unrecognized        (* any other errno *)

(* What the error says, in words, for a message *)
#pub fn io_error_text (e: io_error): string

(* ============================================================
   Linear file descriptor
   ============================================================ *)

#pub datavtype fd =
  | fd_mk of (int)

(* ============================================================
   Linear directory handle
   ============================================================ *)

#pub datavtype dir =
  | dir_mk of (ptr)

(* A directory's entries, read in one pass and sorted by name (bytewise):
   n names, so a walk over them is bounded by n. *)
#pub datavtype entries(int) =
  | {n:nat} entries_mk(n) of (ptr, int n)

(* ============================================================
   File operations
   ============================================================ *)

(* The open file, or why it could not be opened. mode is the
   permission bits of a file it creates. *)
#pub fn file_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n,
   access: access, opening: opening, mode: int): $R.result(fd, io_error)

(* Bytes read into buf[0, k), at most len (read(2)'s contract), or
   why a read failed before any byte. *)
#pub fn file_read
  {l:agz}{n:pos}{o:addr}
  (f: !fd, buf: !$A.arrx(byte, l, n, o), len: int n): $R.result([k:nat | k <= n] int k, io_error)

(* Writes all n bytes of buf, retrying short writes (as Rust's
   write_all), or fails with why the write that failed did. *)
#pub fn file_write
  {lb:agz}{n:pos}
  (f: !fd, buf: !$A.borrow(byte, lb, n), len: int n): $R.result(int n, io_error)

#pub fn file_close(f: fd): $R.result(int, io_error)

(* Size in bytes of the file at path, or why it cannot be had:
   FileTooLarge for a size that does not fit an int. *)
#pub fn file_size
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result([s:nat] int s, io_error)

(* Size in bytes of the open file f, as file_size *)
#pub fn fd_size(f: !fd): $R.result([s:nat] int s, io_error)

(* Copies the bytes of src, from its position to the size it has when
   the copy starts (fd_size), to dst; the number copied (less when src
   ends early), or why a read or write failed. *)
#pub fn fd_copy(src: !fd, dst: !fd): $R.result([c:nat] int c, io_error)

(* ============================================================
   Advisory locks
   ============================================================ *)

(* A lock that others may share (readers), or one held alone *)
#pub datatype lock_kind =
  | LockShared
  | LockExclusive

(* Whether taking a lock that another holds waits until it is free, or
   fails at once with WouldBlock *)
#pub datatype lock_wait =
  | LockWaits
  | LockFailsAtOnce

(* Takes an advisory lock (flock(2)) on the open file f, or says why it
   could not: WouldBlock when kind conflicts with a lock another open
   file holds on the same file and wait is LockFailsAtOnce. The lock
   belongs to this open file: it conflicts with a lock taken through any
   other open of the file, in this process or another, and it is
   released by fd_unlock, by closing f, or when the process ends, however
   it ends, so a process that dies holding it never leaves it held.
   Taking it again on f converts it to kind; as flock(2) says, the
   conversion is not atomic (another may take the lock in between, and
   a conversion that fails may leave f holding none). *)
#pub fn fd_lock(f: !fd, kind: lock_kind, wait: lock_wait): $R.result(int, io_error)

(* Releases the lock f holds, if any *)
#pub fn fd_unlock(f: !fd): $R.result(int, io_error)

(* ============================================================
   Directory operations
   ============================================================ *)

#pub fn dir_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(dir, io_error)

#pub fn dir_close(d: dir): $R.result(int, io_error)

(* Every entry of the directory at path (including . and ..), sorted by
   name; err when the directory cannot be opened or read, or when memory
   for its entries cannot be had (OutOfMemory). *)
#pub fn dir_read
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result([k:nat] entries(k), io_error)

#pub fn entries_count {n:int} (es: !entries(n)): int n

(* The most bytes an entry's name has (d_name's size on macOS, the
   largest of the hosts; checked against the host's d_name when this
   package compiles). *)
#pub stadef ENTRY_NAME_MAX = 1024

(* Length of entry i's name, copied whole to name_buf[0, k); the buffer
   holds any name. *)
#pub fn entries_name
  {n:int}{i:nat | i < n}{l:agz}{m:int | m >= ENTRY_NAME_MAX}
  (es: !entries(n), i: int i, name_buf: !$A.arr(byte, l, m), max_len: int m): [k:nat | k < ENTRY_NAME_MAX] int k

#pub fn entries_free {n:int} (es: entries(n)): void

(* ============================================================
   Extra POSIX operations
   ============================================================ *)

#pub fn file_chdir
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(int, io_error)

(* The modification time of the file at path, in seconds since 1970
   (before it, negative) *)
#pub fn file_mtime
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(int, io_error)

#pub fn file_exists
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): bool

#pub fn file_mkdir
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n, mode: int): $R.result(int, io_error)

(* The permission bits (0 to 07777) of the file at path, or why they
   cannot be read. *)
#pub fn file_mode
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result([m:nat | m <= 4095] int m, io_error)

(* Sets the permission bits of the file at path to mode, or says why it
   cannot. *)
#pub fn file_chmod
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n, mode: int): $R.result(int, io_error)

(* ============================================================
   Renaming, removing, links and status (keyword: remove-rename)
   ============================================================ *)

(* None of these follows a symlink at the end of its path (a link is
   itself renamed, removed or read), and each answers with a constructor
   for every outcome; the reasons are io_error's, so Unrecognized is the
   errno none of the others names. A path is n bytes, 1 or more (an empty
   path is a type error), without a NUL. *)

(* How a rename ended *)
#pub datavtype rename_outcome =
  | Renamed                           (* source is now at destination *)
  | RenameFailed of (io_error)        (* nothing moved: CrossesDevices, DirectoryNotEmpty, ... *)

(* rename(2): source becomes destination in one step, replacing a file
   (or an empty directory) already there, so a reader sees one or the
   other and never a half. Both paths must be on one file system, else
   CrossesDevices. *)
#pub fn file_rename
  {ls,ld:agz}{ns,nd:pos | ns < 1048576; nd < 1048576}
  (source: !$A.borrow(byte, ls, ns), source_len: int ns,
   destination: !$A.borrow(byte, ld, nd), destination_len: int nd): rename_outcome

(* What remove took away *)
#pub datavtype remove_outcome =
  | RemovedFile                       (* a file, or a symlink (not its target) *)
  | RemovedEmptyDirectory
  | RemoveFailed of (io_error)        (* DirectoryNotEmpty for a directory with entries *)

(* Removes the file, the symlink or the empty directory at path
   (unlink or rmdir), never a directory's contents. *)
#pub fn file_remove
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): remove_outcome

(* Why remove_tree would not start: the path names the root of the file
   system (or nothing: only slashes), or its last name is . or .. *)
#pub datatype tree_refusal =
  | RefusedRoot
  | RefusedDotName

(* How a recursive removal ended. The counts include the top. A
   directory on another device than the top (a mount point) is neither
   entered nor removed; a directory that still holds one is left. *)
#pub datavtype remove_tree_outcome =
  | TreeRemoved of (int)                           (* everything is gone: how many entries *)
  | TreeAbsent                                     (* nothing was at path *)
  | TreeRefused of (tree_refusal)                  (* nothing was touched *)
  | TreeFailed of (io_error)                       (* path could not be examined *)
  | TreeLeftMounts of (int, int)                   (* removed, mount points left (the rest is gone) *)
  | TreeLeftSome of (int, int, int, io_error)      (* removed, entries that failed, mount points left, the first failure *)

(* Removes the file, symlink or directory at path with everything under
   it. It never follows a symlink (a link is unlinked, not entered), does
   not cross onto another device, refuses the root and a path ending in .
   or .., and does not stop at a failure: it removes what it can, counts
   what it could not and says the first reason. A descent deeper than 256
   directories is a failure (InvalidFilename) for the directory at that
   depth. A directory that gains entries during the walk is passed again
   until a pass removes nothing. *)
#pub fn file_remove_tree
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): remove_tree_outcome

(* What mkdir -p did *)
#pub datavtype make_directories_outcome =
  | DirectoriesCreated of (int)                    (* how many were made, 1 or more *)
  | DirectoryExisted                               (* every one was there already *)
  | MakeDirectoriesFailed of (io_error)            (* AlreadyExists for a name that is not a directory; those made before stay *)

(* Makes the directory at path and every missing one before it, as mkdir
   -p: the last has the permission bits mode (less the umask), the ones
   before it mode with the owner's write and search bits (0300) added. *)
#pub fn file_make_directories
  {lb:agz}{n:pos | n < 1048576}{m:nat | m <= 4095}
  (path: !$A.borrow(byte, lb, n), path_len: int n, mode: int m): make_directories_outcome

(* The temporary directory made, the length of its path being n + 6 *)
#pub datavtype temp_directory_outcome(path_len: int) =
  | TempDirectoryMade(path_len) of ()
  | TempDirectoryFailed(path_len) of (io_error)

(* mkdtemp(3): makes a new directory, mode 0700, named prefix and six
   characters of its own choosing, and writes its path to out[0, n + 6)
   (no NUL). Nothing is written when it fails. *)
#pub fn file_make_temp_directory
  {lb:agz}{n:pos | n < 1048576}{lo:agz}{m:int | m >= n + 6}
  (name_prefix: !$A.borrow(byte, lb, n), name_prefix_len: int n,
   out: !$A.arr(byte, lo, m), out_size: int m): temp_directory_outcome(n + 6)

(* How a symlink was made *)
#pub datavtype symlink_outcome =
  | SymlinkMade
  | SymlinkFailed of (io_error)       (* AlreadyExists when path is there *)

(* symlink(2): makes a link at path holding target, which need not exist *)
#pub fn file_symlink
  {lt,lp:agz}{nt,np:pos | nt < 1048576; np < 1048576}
  (target: !$A.borrow(byte, lt, nt), target_len: int nt,
   path: !$A.borrow(byte, lp, np), path_len: int np): symlink_outcome

(* What a symlink holds, for a buffer of m bytes *)
#pub datavtype read_link_outcome(m: int) =
  | {k:nat | k < m} LinkTarget(m) of (int k)       (* the target is out[0, k) *)
  | LinkTargetTooLong(m) of ()                     (* it has m bytes or more; nothing is relied on in out *)
  | NotASymlink(m) of ()
  | ReadLinkFailed(m) of (io_error)

(* readlink(2): the target of the symlink at path, in out[0, k) (no NUL) *)
#pub fn file_read_link
  {lb:agz}{n:pos | n < 1048576}{lo:agz}{m:pos}
  (path: !$A.borrow(byte, lb, n), path_len: int n,
   out: !$A.arr(byte, lo, m), out_size: int m): read_link_outcome(m)

(* What a name is, as lstat(2) says (a symlink is a Symlink, not what it
   points to) *)
#pub datatype file_kind =
  | RegularFile
  | Directory
  | Symlink
  | OtherFile                         (* a device, a pipe, a socket *)

(* A path's kind, size in bytes (of a symlink, its target's length),
   permission bits (0 to 07777) and owner's user id *)
#pub datavtype file_info_outcome =
  | {s,m,o:nat | m <= 4095} FileInfo of (file_kind, int s, int m, int o)
  | FileInfoFailed of (io_error)      (* FileTooLarge for a size or an owner past an int *)

#pub fn file_info
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): file_info_outcome

(* Whether a mode has an execute bit (owner, group or others) *)
#pub fn mode_is_executable {m:nat | m <= 4095} (mode: int m): bool

(* Whether a directory has any entry but . and .. *)
#pub datavtype emptiness_outcome =
  | DirectoryIsEmpty
  | DirectoryHasEntries
  | PathIsNotADirectory               (* including a symlink to a directory *)
  | EmptinessFailed of (io_error)

#pub fn directory_emptiness
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): emptiness_outcome

(* ============================================================
   Buffered reader
   ============================================================ *)

#pub stadef BUF_SIZE = 4096

(* filled bytes of the buffer are valid; pos <= filled is the next one
   to hand out. Both bounds are in the type, so no access is checked at
   runtime. *)
(* Deprecated, content-io: content_reader is beside it; removed by #81 *)
#pub datavtype buf_reader =
  | {lb:agz}{f,p:nat | p <= f; f <= BUF_SIZE}
    buf_reader_mk of (fd, $A.arr(byte, lb, BUF_SIZE), int f, int p)

(* Deprecated, content-io: removed by #81 *)
#pub fn buf_reader_create(f: fd): buf_reader

(* Deprecated, content-io: removed by #81 *)
#pub fun buf_read
  {l:agz}{n:pos}
  (r: !buf_reader, buf: !$A.arr(byte, l, n), len: int n): $R.option(int)

(* Deprecated, content-io: removed by #81 *)
#pub fun buf_read_line
  {l:agz}{n:pos}
  (r: !buf_reader, buf: !$A.arr(byte, l, n), max_len: int n): $R.option(int)

(* Deprecated, content-io: removed by #81 *)
#pub fn buf_reader_close(r: buf_reader): $R.result(int, io_error)

(* ============================================================
   Buffered writer
   ============================================================ *)

(* pos < BUF_SIZE bytes are pending: a write that fills the buffer
   writes it out. *)
(* Deprecated, content-io: content_writer is beside it; removed by #80 *)
#pub datavtype buf_writer =
  | {lb:agz}{p:nat | p < BUF_SIZE}
    buf_writer_mk of (fd, $A.arr(byte, lb, BUF_SIZE), int p)

(* Deprecated, content-io: removed by #80 *)
#pub fn buf_writer_create(f: fd): buf_writer

(* Deprecated, content-io: removed by #80 *)
#pub fn buf_write
  {lb:agz}{n:pos}
  (w: !buf_writer, data: !$A.borrow(byte, lb, n), len: int n): $R.result(int, io_error)

(* Deprecated, content-io: removed by #80 *)
#pub fn buf_write_byte(w: !buf_writer, b: int): $R.result(int, io_error)

(* Deprecated, content-io: removed by #80 *)
#pub fn buf_flush(w: !buf_writer): $R.result(int, io_error)

(* Deprecated, buffered-writer close (#61): drops the flush error; removed by #74 *)
#pub fn buf_writer_close(w: buf_writer): $R.result(int, io_error)

(* How a close ended, flush and close each answered (#61): the writer is
   closed in every case, and each failure is its own constructor. *)
#pub datavtype close_outcome =
  | Closed                                         (* flushed and closed *)
  | FlushFailed of (io_error)                      (* final write failed, closed *)
  | CloseFailed of (io_error)                      (* flushed, close failed *)
  | FlushAndCloseFailed of (io_error, io_error)    (* flush's, then close's *)

(* Deprecated, content-io: removed by #80 *)
#pub fn buf_writer_close_checked(w: buf_writer): close_outcome

(* ============================================================
   Content writer: the type holds the bytes written (keyword: content-io)
   ============================================================ *)

(* A file this writer made, whose bytes written so far are the cells
   written. It is made empty (created, or emptied), so it indexes the empty
   cells; a write extends the index by APPEND; a flush leaves it. Every call
   that can fail consumes the writer (closed, nothing more is known): the
   failure is its own constructor, with no proof. *)
#pub absvtype content_writer(written: $A.cells)

(* FILE_HOLDS(written): the file holds exactly the cells written, made only by
   content_close; trusted: the file was made empty by content_create, only
   this writer writes it, no write was short (a short write is retried or is
   a failure) and the close succeeded (keyword: content-io) *)
#pub absprop FILE_HOLDS(written: $A.cells)

(* The file at path, created or emptied for writing, with mode as the
   permission bits of a file it creates; its writer indexes no bytes. *)
#pub fn content_create
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n, mode: int)
  : $R.result(content_writer($A.cnil()), io_error)

(* After a write of the cells chunk to the writer of the cells written: the
   writer of both (APPEND), or why the write failed (the writer is closed) *)
#pub datavtype content_write_outcome($A.cells, $A.cells) =
  | {written,chunk,both:$A.cells}
    content_wrote(written, chunk) of ($A.APPEND(written, chunk, both) | content_writer(both))
  | {written,chunk:$A.cells}
    content_write_failed(written, chunk) of (io_error)

(* One byte, a value below the size of a byte *)
#pub fn content_write_byte
  {written:$A.cells}{b:nat | b < 256}
  (cw: content_writer(written), b: int b)
  : content_write_outcome(written, $A.ccons(b, $A.cnil()))

(* The whole run, whose cells are run_cells *)
#pub fn content_write
  {written:$A.cells}{l:agz}{n:pos}{k:pos}{run_cells:$A.cells}
  (cw: content_writer(written), fz: !$A.cfrozen(l, n, k, run_cells),
   run: !$A.cborrow(l, n, run_cells), len: int n)
  : content_write_outcome(written, run_cells)

(* The first bytes of the run, as many as the cells of chunk, which its cells begin with *)
#pub fn content_write_prefix
  {written:$A.cells}{l:agz}{n:pos}{k:pos}{run_cells,chunk:$A.cells}{m:pos | m <= n}
  (holds: $A.HOLDS(run_cells, chunk), size: $A.CLEN(chunk, m) |
   cw: content_writer(written), fz: !$A.cfrozen(l, n, k, run_cells),
   run: !$A.cborrow(l, n, run_cells), count: int m)
  : content_write_outcome(written, chunk)

(* After a flush: the writer, its index unchanged, or why it failed (closed) *)
#pub datavtype content_flush_outcome($A.cells) =
  | {written:$A.cells} content_flushed(written) of (content_writer(written))
  | {written:$A.cells} content_flush_failed(written) of (io_error)

#pub fn content_flush {written:$A.cells} (cw: content_writer(written))
  : content_flush_outcome(written)

(* After a close: the proof that the file holds the cells written (with the
   zero that file_close answers), or why the flush or the close failed (the
   first that failed; no proof) *)
#pub datavtype content_close_outcome($A.cells) =
  | {written:$A.cells} content_closed(written) of (FILE_HOLDS(written) | int)
  | {written:$A.cells} content_close_failed(written) of (io_error)

#pub fn content_close {written:$A.cells} (cw: content_writer(written))
  : content_close_outcome(written)

(* ============================================================
   Content reader: the type holds the bytes consumed (keyword: content-io)
   ============================================================ *)

(* A file opened for reading at the offset start, at most limit bytes of it
   to be read; the bytes consumed so far are the cells consumed. It indexes
   the empty cells. Every call that can fail or end consumes the reader. *)
#pub absvtype content_reader(consumed: $A.cells, start: int, limit: int)

(* FILE_READ(consumed, start, limit): consumed are exactly the file's bytes
   from offset start, up to limit of them or to the end of the file; made
   only where the reader ends; trusted: the bytes read are the bytes the file
   holds at that offset, and nobody changes the file while it is read
   (keyword: content-io) *)
#pub absprop FILE_READ(consumed: $A.cells, start: int, limit: int)

(* The largest limit an int names: the reader of a whole file *)
#pub stadef CONTENT_READ_ALL = 2147483647

(* The file at path opened to read from offset start, limit bytes at most *)
#pub fn content_reader_open_range
  {lb:agz}{n:pos | n < 1048576}{start,limit:nat}
  (path: !$A.borrow(byte, lb, n), path_len: int n, start: int start, limit: int limit)
  : $R.result(content_reader($A.cnil(), start, limit), io_error)

(* The file at path opened to read from its first byte *)
#pub fn content_reader_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n)
  : $R.result(content_reader($A.cnil(), 0, CONTENT_READ_ALL), io_error)

(* After a read into the buffer buf by the reader of the cells
   consumed: k more bytes, which are the cells chunk, at the front of the
   buffer's new cells, the reader's index extended by chunk; the limit
   reached, consumed being limit cells; the end of the file, before the limit;
   or why the read failed (the reader is closed). The buffer is given back in
   every case. *)
#pub datavtype content_read_outcome($A.cells, int, int, addr, int, $A.cells) =
  | {consumed,chunk,more,buf,buf2:$A.cells}{start,limit:nat}{l:agz}{n:pos}{k:pos | k <= n}
    content_read_some(consumed, start, limit, l, n, buf)
      of ($A.CLEN(chunk, k), $A.HOLDS(buf2, chunk), $A.APPEND(consumed, chunk, more) |
          content_reader(more, start, limit), $A.barr(l, n, buf2), int k)
  | {consumed,buf:$A.cells}{start,limit:nat}{l:agz}{n:pos}
    content_read_limit(consumed, start, limit, l, n, buf)
      of (FILE_READ(consumed, start, limit), $A.CLEN(consumed, limit) | $A.barr(l, n, buf))
  | {consumed,buf:$A.cells}{start,limit:nat}{l:agz}{n:pos}
    content_read_eof(consumed, start, limit, l, n, buf)
      of (FILE_READ(consumed, start, limit) | $A.barr(l, n, buf))
  | {consumed,buf:$A.cells}{start,limit:nat}{l:agz}{n:pos}
    content_read_failed(consumed, start, limit, l, n, buf) of (io_error, $A.barr(l, n, buf))

#pub fn content_read
  {consumed,buf:$A.cells}{start,limit:nat}{l:agz}{n:pos}
  (cr: content_reader(consumed, start, limit), buf: $A.barr(l, n, buf), len: int n)
  : content_read_outcome(consumed, start, limit, l, n, buf)

(* Closes the reader before its end: no proof, the file's close is not
   answered *)
#pub fn content_reader_close {consumed:$A.cells}{start,limit:nat}
  (cr: content_reader(consumed, start, limit)): void

(* ============================================================
   Internal helpers
   ============================================================ *)

fn _with_cpath
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): [lc:agz] $A.arr(byte, lc, n+1) = let
  val cpath = $A.alloc<byte>(path_len + 1)
  val () = $A.write_borrow(cpath, 0, path, path_len)
  val () = $A.write_byte(cpath, path_len, 0)
in cpath end

(* The C runtime's code for an access and an opening: the one place
   they are encoded *)
fn _access_code (access: access): int =
  case+ access of
  | ReadOnly() => 0
  | WriteOnly() => 1
  | ReadWrite() => 2

fn _opening_code (opening: opening): int =
  case+ opening of
  | OpenExisting() => 0
  | CreateOrOpen() => 1
  | CreateOrTruncate() => 2
  | CreateOrAppend() => 3
  | TruncateExisting() => 4
  | AppendExisting() => 5

(* The error a C runtime failure (a negative code, _file_error_code's
   negated) names: the one place the codes are decoded *)
fn _io_error (failure: int): io_error = let
  val code = ~failure
in
  if code = 1 then NotFound()
  else if code = 2 then PermissionDenied()
  else if code = 3 then AlreadyExists()
  else if code = 4 then NotADirectory()
  else if code = 5 then IsADirectory()
  else if code = 6 then DirectoryNotEmpty()
  else if code = 7 then ReadOnlyFilesystem()
  else if code = 8 then FilesystemLoop()
  else if code = 9 then InvalidFilename()
  else if code = 10 then InvalidInput()
  else if code = 11 then FileTooLarge()
  else if code = 12 then StorageFull()
  else if code = 13 then TooManyOpenFiles()
  else if code = 14 then OutOfMemory()
  else if code = 15 then ResourceBusy()
  else if code = 16 then BrokenPipe()
  else if code = 17 then WouldBlock()
  else if code = 18 then BadDescriptor()
  else if code = 19 then DeviceError()
  else if code = 20 then Unsupported()
  else if code = 21 then CrossesDevices()
  else Unrecognized()
end

implement io_error_text (e) =
  case+ e of
  | NotFound() => "not found"
  | PermissionDenied() => "permission denied"
  | AlreadyExists() => "already exists"
  | NotADirectory() => "not a directory"
  | IsADirectory() => "is a directory"
  | DirectoryNotEmpty() => "directory not empty"
  | ReadOnlyFilesystem() => "read-only file system"
  | FilesystemLoop() => "too many levels of symbolic links"
  | InvalidFilename() => "file name too long"
  | InvalidInput() => "invalid argument"
  | FileTooLarge() => "file too large"
  | StorageFull() => "no space left"
  | TooManyOpenFiles() => "too many open files"
  | OutOfMemory() => "out of memory"
  | ResourceBusy() => "resource busy"
  | BrokenPipe() => "broken pipe"
  | WouldBlock() => "operation would block"
  | BadDescriptor() => "bad file descriptor"
  | DeviceError() => "input/output error"
  | Unsupported() => "operation not supported"
  | CrossesDevices() => "crosses devices"
  | Unrecognized() => "unrecognized error"

(* ============================================================
   File implementations
   ============================================================ *)

implement file_open {lb}{n} (path, path_len, access, opening, mode) = let
  val cpath = _with_cpath(path, path_len)
  val rawfd = $UNSAFE begin $extfcall(int, "_file_open",
    $UNSAFE.castvwtp1{ptr}(cpath), _access_code(access), _opening_code(opening), mode) end
  val () = $A.free<byte>(cpath)
in
  if rawfd >= 0 then $R.ok(fd_mk(rawfd))
  else $R.err(_io_error(rawfd))
end

implement file_read {l}{n}{o} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  val r = $UNSAFE begin $extfcall([k:int | k <= n] int k, "_file_read", rawfd,
    $UNSAFE.castvwtp1{ptr}(buf), len) end
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(r)
  else $R.err(_io_error(r))
end

implement file_write {lb}{n} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  (* _file_write returns len or a failure *)
  val r = $UNSAFE begin $extfcall([k:int | k == n || k < 0] int k, "_file_write", rawfd,
    $UNSAFE.castvwtp1{ptr}(buf), len) end
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(r)
  else $R.err(_io_error(r))
end

implement file_close(f) = let
  val+ ~fd_mk(rawfd) = f
  val r = $UNSAFE begin $extfcall(int, "_file_close", rawfd) end
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

implement file_size {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val sz = $UNSAFE begin $extfcall([s:int] int s, "_file_stat_size",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if sz >= 0 then $R.ok(sz)
  else $R.err(_io_error(sz))
end

implement fd_size(f) = let
  val+ @fd_mk(rawfd) = f
  val sz = $UNSAFE begin $extfcall([s:int] int s, "_file_fd_size", rawfd) end
  prval () = fold@(f)
in
  if sz >= 0 then $R.ok(sz)
  else $R.err(_io_error(sz))
end

implement fd_lock(f, kind, wait) = let
  val+ @fd_mk(rawfd) = f
  val k = (case+ kind of LockShared() => 0 | LockExclusive() => 1): int
  val w = (case+ wait of LockWaits() => 0 | LockFailsAtOnce() => 1): int
  val r = $UNSAFE begin $extfcall(int, "_file_lock", rawfd, k, w) end
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

implement fd_unlock(f) = let
  val+ @fd_mk(rawfd) = f
  val r = $UNSAFE begin $extfcall(int, "_file_unlock", rawfd) end
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

(* 64 KiB at a time, until r bytes remain to copy. A chunk read past the
   size (the file grew) is copied only up to it; a read of 0 bytes is
   the end of src. *)
implement fd_copy(src, dst) = let
  fun loop {l:agz}{r,c:nat} .<r>.
    (src: !fd, dst: !fd, buf: $A.arr(byte, l, 65536), r: int r, c: int c)
    : @($R.result([c:nat] int c, io_error), $A.arr(byte, l, 65536)) =
    if r <= 0 then @($R.ok(c), buf)
    else (case+ file_read(src, buf, 65536) of
      | ~$R.err(e) => @($R.err(e), buf)
      | ~$R.ok(k) => let
          val k = (if k > r then r else k): [k2:nat | k2 <= r; k2 <= 65536] int k2
        in
          if k <= 0 then @($R.ok(c), buf)
          else let
            val @(fz, bv) = $A.freeze<byte>(buf)
            val @(left, right) = $A.borrow_split<byte>(fz, bv, k)
            val w = file_write(dst, left, k)
            val () = $A.drop<byte>(fz, $A.borrow_join<byte>(fz, left, right))
            val buf = $A.thaw<byte>(fz)
          in
            case+ w of
            | ~$R.ok(_) => loop(src, dst, buf, r - k, c + k)
            | ~$R.err(e) => @($R.err(e), buf)
          end
        end)
in
  case+ fd_size(src) of
  | ~$R.err(e) => $R.err(e)
  | ~$R.ok(s) => let
      val @(res, buf) = loop(src, dst, $A.alloc<byte>(65536), s, 0)
      val () = $A.free<byte>(buf)
    in res end
end

(* ============================================================
   Directory implementations
   ============================================================ *)

implement dir_open {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val dp = $UNSAFE begin $extfcall(ptr, "_file_opendir",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
  val nonnull = $UNSAFE begin $extfcall(int, "_file_ptr_nonnull", dp) end
in
  if nonnull > 0 then $R.ok(dir_mk(dp))
  else $R.err(_io_error($UNSAFE begin $extfcall(int, "_file_last_failed") end))
end

implement dir_read {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val p = $UNSAFE begin $extfcall(ptr, "_file_dir_read",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if ptr_isnot_null(p) then let
    val k = $UNSAFE begin $extfcall([k:nat] int k, "_file_entries_count", p) end
  in $R.ok(entries_mk(p, k)) end
  else $R.err(_io_error($UNSAFE begin $extfcall(int, "_file_last_failed") end))
end

implement entries_count {n} (es) = let
  val+ @entries_mk(_, k) = es
  val r = k
  prval () = fold@(es)
in r end

implement entries_name {n}{i}{l}{m} (es, i, name_buf, max_len) = let
  val+ @entries_mk(p, _) = es
  val r = $UNSAFE begin $extfcall([k:nat | k < ENTRY_NAME_MAX] int k, "_file_entries_name", p, i,
    $UNSAFE.castvwtp1{ptr}(name_buf)) end
  prval () = fold@(es)
in r end

implement entries_free {n} (es) = let
  val+ ~entries_mk(p, _) = es
in $UNSAFE begin $extfcall(void, "_file_entries_free", p) end end

implement dir_close(d) = let
  (* dir_open makes a dir only of a pointer that is not null *)
  val+ ~dir_mk(dp) = d
  val r = $UNSAFE begin $extfcall(int, "_file_closedir", dp) end
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

(* ============================================================
   Extra POSIX operation implementations
   ============================================================ *)

implement file_chdir {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_chdir",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

implement file_mtime {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  var mtime: int = 0
  val r = $UNSAFE begin $extfcall(int, "_file_mtime",
    $UNSAFE.castvwtp1{ptr}(cpath), addr@mtime) end
  val () = $A.free<byte>(cpath)
in
  if r >= 0 then $R.ok(mtime)
  else $R.err(_io_error(r))
end

implement file_exists {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_exists",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in r > 0 end

implement file_mode {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val m = $UNSAFE begin $extfcall([m:int | m <= 4095] int m, "_file_mode",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if m >= 0 then $R.ok(m)
  else $R.err(_io_error(m))
end

implement file_chmod {lb}{n} (path, path_len, mode) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_chmod",
    $UNSAFE.castvwtp1{ptr}(cpath), mode) end
  val () = $A.free<byte>(cpath)
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

implement file_mkdir {lb}{n} (path, path_len, mode) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_mkdir",
    $UNSAFE.castvwtp1{ptr}(cpath), mode) end
  val () = $A.free<byte>(cpath)
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

(* ============================================================
   Renaming, removing, links and status implementations
   ============================================================ *)

implement file_rename {ls,ld}{ns,nd} (source, source_len, destination, destination_len) = let
  val csource = _with_cpath(source, source_len)
  val cdestination = _with_cpath(destination, destination_len)
  val r = $UNSAFE begin $extfcall(int, "_file_rename",
    $UNSAFE.castvwtp1{ptr}(csource), $UNSAFE.castvwtp1{ptr}(cdestination)) end
  val () = $A.free<byte>(csource)
  val () = $A.free<byte>(cdestination)
in
  if r >= 0 then Renamed() else RenameFailed(_io_error(r))
end

implement file_remove {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_remove",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if r = 1 then RemovedFile()
  else if r = 2 then RemovedEmptyDirectory()
  else if r < 0 then RemoveFailed(_io_error(r))
  else RemoveFailed(Unrecognized())
end

implement file_remove_tree {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  var removed: [r:nat] int r = 0
  var kept: [k:nat] int k = 0
  var mounts: [m:nat] int m = 0
  var first: int = 0
  val r = $UNSAFE begin $extfcall(int, "_file_remove_tree",
    $UNSAFE.castvwtp1{ptr}(cpath), addr@removed, addr@kept, addr@mounts, addr@first) end
  val () = $A.free<byte>(cpath)
in
  if r = 0 then
    (if kept > 0 then TreeLeftSome(removed, kept, mounts, _io_error(~first))
     else if mounts > 0 then TreeLeftMounts(removed, mounts)
     else TreeRemoved(removed))
  else if r = 1 then TreeAbsent()
  else if r = 2 then TreeRefused(RefusedRoot())
  else if r = 3 then TreeRefused(RefusedDotName())
  else if r < 0 then TreeFailed(_io_error(r))
  else TreeFailed(Unrecognized())
end

implement file_make_directories {lb}{n}{m} (path, path_len, mode) = let
  val cpath = _with_cpath(path, path_len)
  var created: [c:nat] int c = 0
  val r = $UNSAFE begin $extfcall(int, "_file_mkdirs",
    $UNSAFE.castvwtp1{ptr}(cpath), mode, addr@created) end
  val () = $A.free<byte>(cpath)
in
  if r < 0 then MakeDirectoriesFailed(_io_error(r))
  else if created > 0 then DirectoriesCreated(created)
  else DirectoryExisted()
end

implement file_make_temp_directory {lb}{n}{lo}{m} (name_prefix, name_prefix_len, out, out_size) = let
  val cprefix = _with_cpath(name_prefix, name_prefix_len)
  val r = $UNSAFE begin $extfcall(int, "_file_mkdtemp",
    $UNSAFE.castvwtp1{ptr}(cprefix), name_prefix_len, $UNSAFE.castvwtp1{ptr}(out)) end
  val () = $A.free<byte>(cprefix)
in
  if r >= 0 then TempDirectoryMade()
  else TempDirectoryFailed(_io_error(r))
end

implement file_symlink {lt,lp}{nt,np} (target, target_len, path, path_len) = let
  val ctarget = _with_cpath(target, target_len)
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_symlink",
    $UNSAFE.castvwtp1{ptr}(ctarget), $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(ctarget)
  val () = $A.free<byte>(cpath)
in
  if r >= 0 then SymlinkMade() else SymlinkFailed(_io_error(r))
end

implement file_read_link {lb}{n}{lo}{m} (path, path_len, out, out_size) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall([k:int] int k, "_file_readlink",
    $UNSAFE.castvwtp1{ptr}(cpath), $UNSAFE.castvwtp1{ptr}(out), out_size) end
  val () = $A.free<byte>(cpath)
in
  if r = ~100 then NotASymlink()
  else if r < 0 then ReadLinkFailed(_io_error(r))
  else if r >= out_size then LinkTargetTooLong()
  else LinkTarget(r)
end

implement file_info {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  var kind: int = 0
  var size: [s:nat] int s = 0
  var mode: [m:nat | m <= 4095] int m = 0
  var owner: [o:nat] int o = 0
  val r = $UNSAFE begin $extfcall(int, "_file_lstat",
    $UNSAFE.castvwtp1{ptr}(cpath), addr@kind, addr@size, addr@mode, addr@owner) end
  val () = $A.free<byte>(cpath)
in
  if r < 0 then FileInfoFailed(_io_error(r))
  else FileInfo(
    (if kind = 0 then RegularFile() else if kind = 1 then Directory()
     else if kind = 2 then Symlink() else OtherFile()), size, mode, owner)
end

implement mode_is_executable {m} (mode) =
  (mode / 64) % 2 = 1 || (mode / 8) % 2 = 1 || mode % 2 = 1

implement directory_emptiness {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_dir_empty",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if r = 1 then DirectoryIsEmpty()
  else if r = 0 then DirectoryHasEntries()
  else if r = 2 then PathIsNotADirectory()
  else if r < 0 then EmptinessFailed(_io_error(r))
  else EmptinessFailed(Unrecognized())
end

(* ============================================================
   Buffered reader implementations
   ============================================================ *)

implement buf_reader_create(f) = let
  val buf = $A.alloc<byte>(4096)
in buf_reader_mk(f, buf, 0, 0) end

(* dst[0..c) := src[p..p+c). *)
fun _copy_out {ld,ls:agz}{n:pos}{p,c:nat | p + c <= BUF_SIZE; c <= n}{k:nat | k <= c} .<c - k>.
  (dst: !$A.arr(byte, ld, n), src: !$A.arr(byte, ls, BUF_SIZE),
   p: int p, k: int k, c: int c): void =
  if k >= c then ()
  else let
    val () = $A.set<byte>(dst, k, $A.get<byte>(src, p + k))
  in _copy_out(dst, src, p, k + 1, c) end

(* Refill the buffer from the file. read(2) returns at most the count
   asked for; that contract is stated in the FFI result type, which is
   where this unsafe package vouches for its C code. *)
fn _buf_refill(r: !buf_reader): int = let
  val+ @buf_reader_mk(f, buf, filled, pos) = r
  val+ @fd_mk(rawfd) = f
  val n = $UNSAFE begin $extfcall([k:int | k <= BUF_SIZE] int k, "_file_read", rawfd,
    $UNSAFE.castvwtp1{ptr}(buf), 4096) end
  prval () = fold@(f)
  val nf = (if n > 0 then n else 0): [k:nat | k <= BUF_SIZE] int k
  val () = filled := nf
  val () = pos := 0
  prval () = fold@(r)
in n end

(* Hand out up to len available bytes; none when nothing is buffered. *)
fn _buf_take {l:agz}{n:pos}
  (r: !buf_reader, dst: !$A.arr(byte, l, n), len: int n): $R.option(int) = let
  val+ @buf_reader_mk(f, ibuf, filled, pos) = r
  val avail = filled - pos
in
  if avail <= 0 then let
    prval () = fold@(r)
  in $R.none() end
  else let
    val to_copy = min(avail, len)
    val () = _copy_out(dst, ibuf, pos, 0, to_copy)
    val () = pos := pos + to_copy
    prval () = fold@(r)
  in $R.some(to_copy) end
end

implement buf_read {l}{n} (r, dst, len) = let
  val first = _buf_take(r, dst, len)
in
  case+ first of
  | ~$R.some(k) => $R.some(k)
  | ~$R.none() => let
      val n = _buf_refill(r)
    in
      if n > 0 then _buf_take(r, dst, len) else $R.none()
    end
end

(* Where a scan of buf[i..lim) for a newline stops: at the first
   newline, or at lim when there is none *)
fun _scan_nl {lb:agz}{i,lim:nat | i <= lim; lim <= BUF_SIZE} .<lim - i>.
  (ibuf: !$A.arr(byte, lb, BUF_SIZE), i: int i, lim: int lim)
  : [r:int | i <= r; r <= lim] int r =
  if i >= lim then lim
  else if byte2int0($A.get<byte>(ibuf, i)) = 10 then i
  else _scan_nl(ibuf, i + 1, lim)

(* One line (without the newline) from the buffered bytes, truncated to
   max_len; none when nothing is buffered. Without a newline, the rest of
   the buffer is returned. *)
fn _buf_line {l:agz}{n:pos}
  (r: !buf_reader, buf: !$A.arr(byte, l, n), max_len: int n): $R.option(int) = let
  val+ @buf_reader_mk(f, ibuf, filled, pos) = r
in
  if pos >= filled then let
    prval () = fold@(r)
  in $R.none() end
  else let
    val nl = _scan_nl(ibuf, pos, filled)
  in
    if nl < filled then let
      val line_len = nl - pos
      val copy_len = min(line_len, max_len)
      val () = _copy_out(buf, ibuf, pos, 0, copy_len)
      val () = pos := nl + 1
      prval () = fold@(r)
    in $R.some(copy_len) end
    else let
      val rest = filled - pos
      val copy_len = min(rest, max_len)
      val () = _copy_out(buf, ibuf, pos, 0, copy_len)
      val () = pos := filled
      prval () = fold@(r)
    in $R.some(copy_len) end
  end
end

implement buf_read_line {l}{n} (r, buf, max_len) = let
  val first = _buf_line(r, buf, max_len)
in
  case+ first of
  | ~$R.some(k) => $R.some(k)
  | ~$R.none() => let
      val n = _buf_refill(r)
    in
      if n > 0 then _buf_line(r, buf, max_len) else $R.none()
    end
end

implement buf_reader_close(r) = let
  val+ ~buf_reader_mk(f, buf, _, _) = r
  val () = $A.free<byte>(buf)
in file_close(f) end

(* ============================================================
   Buffered writer implementations
   ============================================================ *)

implement buf_writer_create(f) = let
  val buf = $A.alloc<byte>(4096)
in buf_writer_mk(f, buf, 0) end

(* buf[0, c) written to f: the count, or why it was not *)
fn _write_prefix {lb:agz}{c:pos | c <= BUF_SIZE}
  (f: !fd, buf: $A.arr(byte, lb, BUF_SIZE), c: int c)
  : @($A.arr(byte, lb, BUF_SIZE), $R.result(int, io_error)) = let
  val @(fz, bv) = $A.freeze<byte>(buf)
  val+ @fd_mk(rawfd) = f
  val written = $UNSAFE begin $extfcall(int, "_file_write", rawfd,
    $UNSAFE.castvwtp1{ptr}(bv), c) end
  prval () = fold@(f)
  val () = $A.drop<byte>(fz, bv)
in
  @($A.thaw<byte>(fz), (if written >= 0 then $R.ok(written) else $R.err(_io_error(written))): $R.result(int, io_error))
end

fn _buf_do_flush(w: !buf_writer): $R.result(int, io_error) = let
  val+ @buf_writer_mk(f, buf, pos) = w
in
  if pos <= 0 then let
    prval () = fold@(w)
  in $R.ok(0) end
  else let
    val @(buf2, r) = _write_prefix(f, buf, pos)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in r end
end

implement buf_flush(w) = _buf_do_flush(w)

(* A full buffer is flushed before the byte is stored; the byte is the
   low 8 bits of b, as before, now without a cast. *)
implement buf_write_byte(w, b) = let
  val+ @buf_writer_mk(f, buf, pos) = w
  val () = $A.set<byte>(buf, pos, $A.int2byte($AR.low_byte(b)))
  val np = pos + 1
in
  if np < 4096 then let
    val () = pos := np
    prval () = fold@(w)
  in $R.ok(1) end
  else let
    val @(buf2, r) = _write_prefix(f, buf, np)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in r end
end

(* buf[p..p+c) := src[0..c). *)
fun _copy_in {ld,ls:agz}{n:pos}{p,c:nat | p + c <= BUF_SIZE; c <= n}{k:nat | k <= c} .<c - k>.
  (dst: !$A.arr(byte, ld, BUF_SIZE), src: !$A.borrow(byte, ls, n),
   p: int p, k: int k, c: int c): void =
  if k >= c then ()
  else let
    val () = $A.set<byte>(dst, p + k, $A.read<byte>(src, k))
  in _copy_in(dst, src, p, k + 1, c) end

(* After a flush: buffer the data if it now fits, otherwise (it is larger
   than the buffer) write it straight to the file. No recursion. *)
fn _buf_write_flushed {lb:agz}{n:pos}
  (w: !buf_writer, data: !$A.borrow(byte, lb, n), len: int n): $R.result(int, io_error) = let
  val+ @buf_writer_mk(f, buf, pos) = w
in
  if pos + len < 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val () = pos := pos + len
    prval () = fold@(w)
  in $R.ok(len) end
  else if pos + len = 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val @(buf2, r) = _write_prefix(f, buf, 4096)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in r end
  else let
    val r = file_write(f, data, len)
    prval () = fold@(w)
  in
    case+ r of
    | ~$R.ok(k) => $R.ok(k)
    | ~$R.err(e) => $R.err(e)
  end
end

implement buf_write {lb}{n} (w, data, len) = let
  val+ @buf_writer_mk(f, buf, pos) = w
in
  if pos + len < 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val () = pos := pos + len
    prval () = fold@(w)
  in $R.ok(len) end
  else if pos + len = 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val @(buf2, r) = _write_prefix(f, buf, 4096)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in r end
  else let
    prval () = fold@(w)
    val r = _buf_do_flush(w)
  in
    case+ r of
    | ~$R.ok(_) => _buf_write_flushed(w, data, len)
    | ~$R.err(e) => $R.err(e)
  end
end

(* Flush, then close: the flush's answer and the close's, both kept *)
fn _buf_close_both(w: buf_writer)
  : @($R.result(int, io_error), $R.result(int, io_error)) = let
  val flush_r = _buf_do_flush(w)
  val+ ~buf_writer_mk(f, buf, _) = w
  val () = $A.free<byte>(buf)
  val close_r = file_close(f)
in @(flush_r, close_r) end

(* buffered-writer close (#61): the flush's answer is dropped, as published *)
implement buf_writer_close(w) = let
  val @(flush_r, close_r) = _buf_close_both(w)
  val () = $R.discard<int><io_error>(flush_r)
in close_r end

implement buf_writer_close_checked(w) = let
  val @(flush_r, close_r) = _buf_close_both(w)
in
  case+ flush_r of
  | ~$R.ok(_) =>
    (case+ close_r of
     | ~$R.ok(_) => Closed()
     | ~$R.err(c) => CloseFailed(c))
  | ~$R.err(fe) =>
    (case+ close_r of
     | ~$R.ok(_) => FlushFailed(fe)
     | ~$R.err(c) => FlushAndCloseFailed(fe, c))
end


(* ============================================================
   Content writer and reader implementations (keyword: content-io)
   ============================================================ *)

(* What a content_reader is: the file, and the bytes left to read of its limit *)
datavtype _reader_rep =
  | {r:nat} _reader_mk of (fd, int r)

local

$UNSAFE begin
  assume content_writer(written) = buf_writer
  assume content_reader(consumed, start, limit) = _reader_rep
end

in

(* The writer closed with no proof, after a failed call; a close that fails
   here is not reported, the call's own failure is *)
fn _writer_abandon(w: buf_writer): void = let
  val @(flush_r, close_r) = _buf_close_both(w)
  val () = $R.discard<int><io_error>(flush_r)
  val () = $R.discard<int><io_error>(close_r)
in () end

(* buf_write of the first count bytes of a frozen run: the run's borrow as a
   view of count bytes for the write, then back to the whole view it was *)
fn _write_run_prefix
  {l:agz}{n:pos}{k:pos}{cs:$A.cells}{m:pos | m <= n}
  (w: !buf_writer, fz: !$A.cfrozen(l, n, k, cs),
   run: !$A.cborrow(l, n, cs), count: int m): $R.result(int, io_error) = let
  val view = $A.cborrow_view(fz, run)
  val p = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(view) end
  val head = $UNSAFE begin $UNSAFE.castvwtp0{$A.borrow(byte, l, m)}(p) end
  val r = buf_write(w, head, count)
  val p2 = $UNSAFE begin $UNSAFE.castvwtp0{ptr}(head) end
  val whole = $UNSAFE begin $UNSAFE.castvwtp0{$A.borrow(byte, l, n)}(p2) end
  val () = $A.cborrow_view_drop(fz, whole)
in r end

implement content_create {lb}{n} (path, path_len, mode) =
  (case+ file_open(path, path_len, WriteOnly(), CreateOrTruncate(), mode) of
   | ~$R.ok(f) => $R.ok(buf_writer_create(f))
   | ~$R.err(e) => $R.err(e))

(* The index after the write: both is written then chunk, the one place the
   writer's claim is made (the write itself was answered ok) *)
fn _wrote {written,chunk:$A.cells} (cw: buf_writer): content_write_outcome(written, chunk) = let
  val (appended | _) = $UNSAFE begin
    $UNSAFE.cast{[both:$A.cells] ($A.APPEND(written, chunk, both) | int)}(0) end
in content_wrote(appended | cw) end

fn _write_failed {written,chunk:$A.cells} (cw: buf_writer, e: io_error)
  : content_write_outcome(written, chunk) = let
  val () = _writer_abandon(cw)
in content_write_failed(e) end

implement content_write_byte {written}{b} (cw, b) =
  (case+ buf_write_byte(cw, b) of
   | ~$R.ok(_) => _wrote{written,$A.ccons(b, $A.cnil())}(cw)
   | ~$R.err(e) => _write_failed{written,$A.ccons(b, $A.cnil())}(cw, e))

implement content_write {written}{l}{n}{k}{run_cells} (cw, fz, run, len) =
  (case+ _write_run_prefix(cw, fz, run, len) of
   | ~$R.ok(_) => _wrote{written,run_cells}(cw)
   | ~$R.err(e) => _write_failed{written,run_cells}(cw, e))

implement content_write_prefix {written}{l}{n}{k}{run_cells,chunk}{m} (holds, size | cw, fz, run, count) =
  (case+ _write_run_prefix(cw, fz, run, count) of
   | ~$R.ok(_) => _wrote{written,chunk}(cw)
   | ~$R.err(e) => _write_failed{written,chunk}(cw, e))

implement content_flush {written} (cw) =
  (case+ _buf_do_flush(cw) of
   | ~$R.ok(_) => content_flushed(cw)
   | ~$R.err(e) => let val () = _writer_abandon(cw) in content_flush_failed(e) end)

(* The file holds the cells written: the one place the proof is made, after
   the flush and the close both answered ok *)
implement content_close {written} (cw) = let
  val @(flush_r, close_r) = _buf_close_both(cw)
in
  case+ flush_r of
  | ~$R.err(e) => let
      val () = $R.discard<int><io_error>(close_r)
    in content_close_failed(e) end
  | ~$R.ok(_) =>
    (case+ close_r of
     | ~$R.err(e) => content_close_failed(e)
     | ~$R.ok(_) => let
         val (holds | _) = $UNSAFE begin $UNSAFE.cast{(FILE_HOLDS(written) | int)}(0) end
       in content_closed(holds | 0) end)
end

(* The reader opened and moved to start, with limit bytes left to read *)
implement content_reader_open_range {lb}{n}{start,limit} (path, path_len, start, limit) =
  (case+ file_open(path, path_len, ReadOnly(), OpenExisting(), 0) of
   | ~$R.err(e) => $R.err(e)
   | ~$R.ok(f) => let
       val moved = (if start > 0 then let
           val+ @fd_mk(rawfd) = f
           val r = $UNSAFE begin $extfcall(int, "_file_seek", rawfd, start) end
           prval () = fold@(f)
         in r end
         else 0): int
     in
       if moved >= 0 then $R.ok(_reader_mk(f, limit))
       else let
         val () = $R.discard<int><io_error>(file_close(f))
       in $R.err(_io_error(moved)) end
     end)

implement content_reader_open {lb}{n} (path, path_len) =
  content_reader_open_range(path, path_len, 0, 2147483647)

implement content_reader_close {consumed}{start,limit} (cr) = let
  val+ ~_reader_mk(f, _) = cr
in $R.discard<int><io_error>(file_close(f)) end

(* k more bytes read: the proofs are the reader's claim that they are the
   chunk at the front of the buffer's new cells, appended to the consumed *)
fn _read_some
  {consumed,buf:$A.cells}{start,limit:nat}{l:agz}{n:pos}{r:nat}{k:pos | k <= n; k <= r}
  (f: fd, left: int r, buf: $A.barr(l, n, buf), got: int k)
  : content_read_outcome(consumed, start, limit, l, n, buf) = let
  val (size, holds, appended | buf2) = $UNSAFE begin
    $UNSAFE.castvwtp0{[chunk,buf2,more:$A.cells]
      ($A.CLEN(chunk, k), $A.HOLDS(buf2, chunk), $A.APPEND(consumed, chunk, more) | $A.barr(l, n, buf2))}(buf) end
in content_read_some(size, holds, appended | _reader_mk(f, left - got), buf2, got) end

implement content_read {consumed,buf}{start,limit}{l}{n} (cr, buf, len) = let
  val+ ~_reader_mk{r}(f, left) = cr
in
  if left <= 0 then let
    val () = $R.discard<int><io_error>(file_close(f))
    val (ended, full | _) = $UNSAFE begin
      $UNSAFE.cast{(FILE_READ(consumed, start, limit), $A.CLEN(consumed, limit) | int)}(0) end
  in content_read_limit(ended, full | buf) end
  else let
    val want = (if len < left then len else left): [w:pos | w <= n; w <= r] int w
    val+ @fd_mk(rawfd) = f
    val got = $UNSAFE begin $extfcall([k:int | k <= n; k <= r] int k, "_file_read", rawfd,
      $UNSAFE.castvwtp1{ptr}(buf), want) end
    prval () = fold@(f)
  in
    if got < 0 then let
      val () = $R.discard<int><io_error>(file_close(f))
    in content_read_failed(_io_error(got), buf) end
    else if got = 0 then let
      val () = $R.discard<int><io_error>(file_close(f))
      val (ended | _) = $UNSAFE begin
        $UNSAFE.cast{(FILE_READ(consumed, start, limit) | int)}(0) end
    in content_read_eof(ended | buf) end
    else _read_some{consumed,buf}{start,limit}{l}{n}(f, left, buf, got)
  end
end

end (* local -- content writer and reader *)
