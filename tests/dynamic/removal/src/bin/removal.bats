#include "share/atspre_staload.hats"
#use array as A
#use builder as B
#use file as F
#use list as L
#use process as P
#use result as R

(* Renaming, removing, links and status (keyword: remove-rename), each on
   real files in a directory the test makes with mkdtemp and removes with
   remove_tree at the end. Every outcome of every operation is matched, so
   a constructor the test does not expect is a failure that names the
   check. It runs under valgrind: the C path buffers, the walk's
   descriptors and DIR handles must all be freed. Exits 1 on a wrong
   outcome. *)

fn check (name: string, ok: bool): bool = let
  val () = (if ok then () else println! ("FAIL ", name))
in ok end

(* ---- the code of an error, for comparing ---- *)

#define NOT_FOUND 1
#define ALREADY_EXISTS 3
#define NOT_A_DIRECTORY 4
#define NOT_EMPTY 6
#define INVALID_FILENAME 9

fn ecode (e: $F.io_error): int =
  case+ e of
  | $F.NotFound() => 1
  | $F.PermissionDenied() => 2
  | $F.AlreadyExists() => 3
  | $F.NotADirectory() => 4
  | $F.IsADirectory() => 5
  | $F.DirectoryNotEmpty() => 6
  | $F.ReadOnlyFilesystem() => 7
  | $F.FilesystemLoop() => 8
  | $F.InvalidFilename() => 9
  | $F.InvalidInput() => 10
  | $F.CrossesDevices() => 21
  | _ => 99

(* ---- paths from literals ---- *)

fun fill_text {l:agz}{n:pos}{i:nat | i <= n} .<n - i>.
  (a: !$A.arr(byte, l, n), t: $A.text(n), i: int i, n: int n): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(a, i, $A.text_get(t, i))
  in fill_text(a, t, i + 1, n) end

fn path_of {n:pos | n <= 1048576} (s: string n, n: int n): [l:agz] $A.arr(byte, l, n) = let
  val a = $A.alloc<byte>(n)
  val () = fill_text(a, $A.text_lit(s), 0, n)
in a end

(* "d/d/.../d" with k names: the deep chain of directories *)
fun fill_deep {l:agz}{n:pos}{i:nat | i <= n} .<n - i>.
  (a: !$A.arr(byte, l, n), i: int i, n: int n): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(a, i, (if i % 2 = 0 then $A.int2byte(100) else $A.int2byte(47)))
  in fill_deep(a, i + 1, n) end

fn deep_path {k:pos | k <= 500} (k: int k): [l:agz] $A.arr(byte, l, 2 * k - 1) = let
  val a = $A.alloc<byte>(2 * k - 1)
  val () = fill_deep(a, 0, 2 * k - 1)
in a end

(* ---- the operations, each as one code ---- *)

(* 0 renamed, else 100 + the error *)
fn op_rename {ns,nd:pos | ns < 1048576; nd < 1048576}
  (source: string ns, ns: int ns, destination: string nd, nd: int nd): int = let
  val ps = path_of(source, ns)
  val pd = path_of(destination, nd)
  val @(fs, bs) = $A.freeze<byte>(ps)
  val @(fd, bd) = $A.freeze<byte>(pd)
  val r = (case+ $F.file_rename(bs, ns, bd, nd) of
    | ~$F.Renamed() => 0
    | ~$F.RenameFailed(e) => 100 + ecode(e))
  val () = $A.drop<byte>(fs, bs)
  val () = $A.free<byte>($A.thaw<byte>(fs))
  val () = $A.drop<byte>(fd, bd)
  val () = $A.free<byte>($A.thaw<byte>(fd))
in r end

(* 0 removed a file or link, 1 removed an empty directory, else 100 + the error *)
fn op_remove {n:pos | n < 1048576} (s: string n, n: int n): int = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = (case+ $F.file_remove(b, n) of
    | ~$F.RemovedFile() => 0
    | ~$F.RemovedEmptyDirectory() => 1
    | ~$F.RemoveFailed(e) => 100 + ecode(e))
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* kind: 0 removed, 1 absent, 2 refused root, 3 refused dot name, 4 failed,
   5 left mounts, 6 left some; then removed, kept, mounts, the error *)
fn tree_code {lb:agz}{n:pos | n < 1048576}
  (b: !$A.borrow(byte, lb, n), n: int n): @(int, int, int, int, int) =
  case+ $F.file_remove_tree(b, n) of
  | ~$F.TreeRemoved(r) => @(0, r, 0, 0, 0)
  | ~$F.TreeAbsent() => @(1, 0, 0, 0, 0)
  | ~$F.TreeRefused(why) => (case+ why of
      | $F.RefusedRoot() => @(2, 0, 0, 0, 0)
      | $F.RefusedDotName() => @(3, 0, 0, 0, 0))
  | ~$F.TreeFailed(e) => @(4, 0, 0, 0, ecode(e))
  | ~$F.TreeLeftMounts(r, m) => @(5, r, 0, m, 0)
  | ~$F.TreeLeftSome(r, k, m, e) => @(6, r, k, m, ecode(e))

fn op_tree {n:pos | n < 1048576} (s: string n, n: int n): @(int, int, int, int, int) = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = tree_code(b, n)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* the empty path: one byte, a NUL, which the C side reads as "" *)
fn op_tree_empty (): @(int, int, int, int, int) = let
  val p = $A.alloc<byte>(1)
  val () = $A.set<byte>(p, 0, $A.int2byte(0))
  val @(fz, b) = $A.freeze<byte>(p)
  val r = tree_code(b, 1)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* the tree's code when c holds, else kind -1 (nothing was tried) *)
fn op_tree_when {n:pos | n < 1048576} (c: bool, s: string n, n: int n): @(int, int, int, int, int) =
  if c then op_tree(s, n) else @(~1, 0, 0, 0, 0)

fn op_tree_deep {k:pos | k <= 500} (k: int k): @(int, int, int, int, int) = let
  val p = deep_path(k)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = tree_code(b, 2 * k - 1)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn mkdirs_code {lb:agz}{n:pos | n < 1048576}{m:nat | m <= 4095}
  (b: !$A.borrow(byte, lb, n), n: int n, mode: int m): int =
  case+ $F.file_make_directories(b, n, mode) of
  | ~$F.DirectoriesCreated(c) => c
  | ~$F.DirectoryExisted() => 0
  | ~$F.MakeDirectoriesFailed(e) => 100 + ecode(e)

(* the number made, 0 when all were there, else 100 + the error *)
fn op_mkdirs {n:pos | n < 1048576}{m:nat | m <= 4095} (s: string n, n: int n, mode: int m): int = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = mkdirs_code(b, n, mode)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn op_mkdirs_deep {k:pos | k <= 500} (k: int k): int = let
  val p = deep_path(k)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = mkdirs_code(b, 2 * k - 1, 493)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* 0 made, else 100 + the error *)
fn op_symlink {nt,np:pos | nt < 1048576; np < 1048576}
  (target: string nt, nt: int nt, path: string np, np: int np): int = let
  val pt = path_of(target, nt)
  val pp = path_of(path, np)
  val @(ft, bt) = $A.freeze<byte>(pt)
  val @(fp, bp) = $A.freeze<byte>(pp)
  val r = (case+ $F.file_symlink(bt, nt, bp, np) of
    | ~$F.SymlinkMade() => 0
    | ~$F.SymlinkFailed(e) => 100 + ecode(e))
  val () = $A.drop<byte>(ft, bt)
  val () = $A.free<byte>($A.thaw<byte>(ft))
  val () = $A.drop<byte>(fp, bp)
  val () = $A.free<byte>($A.thaw<byte>(fp))
in r end

(* out[0, k) is the same as the first k bytes of text t, i <= k *)
fun same_bytes {l:agz}{m:pos}{k:nat | k < m}{i:nat | i <= k} .<k - i>.
  (out: !$A.arr(byte, l, m), t: $A.text(k), i: int i, k: int k): bool =
  if i >= k then true
  else if byte2int0($A.get<byte>(out, i)) = byte2int0($A.text_get(t, i)) then same_bytes(out, t, i + 1, k)
  else false

(* 0 the target is the expected, 1 another, 2 too long for the buffer,
   3 not a symlink, else 100 + the error *)
fn read_link_code {lb:agz}{n:pos | n < 1048576}{lo:agz}{ne:pos}{m:pos}
  (b: !$A.borrow(byte, lb, n), n: int n, out: !$A.arr(byte, lo, m), m: int m,
   expected: string ne, ne: int ne): int =
  case+ $F.file_read_link(b, n, out, m) of
  | ~$F.LinkTarget(k) =>
      (if k = ne then (if same_bytes(out, $A.text_lit(expected), 0, ne) then 0 else 1) else 1)
  | ~$F.LinkTargetTooLong() => 2
  | ~$F.NotASymlink() => 3
  | ~$F.ReadLinkFailed(e) => 100 + ecode(e)

fn op_read_link {n:pos | n < 1048576}{ne:pos}{m:pos | m <= 1048576}
  (s: string n, n: int n, expected: string ne, ne: int ne, m: int m): int = let
  val p = path_of(s, n)
  val out = $A.alloc<byte>(m)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = read_link_code(b, n, out, m, expected, ne)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
  val () = $A.free<byte>(out)
in r end

(* code (0 or 100 + the error), kind (0 file, 1 directory, 2 symlink, 3 other),
   size, permission bits, owner *)
fn op_info {n:pos | n < 1048576} (s: string n, n: int n): @(int, int, int, int, int) = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = (case+ $F.file_info(b, n) of
    | ~$F.FileInfo(kind, size, mode, owner) => @(0,
        (case+ kind of
         | $F.RegularFile() => 0 | $F.Directory() => 1 | $F.Symlink() => 2 | $F.OtherFile() => 3),
        size, mode, owner)
    | ~$F.FileInfoFailed(e) => @(100 + ecode(e), 0, 0, 0, 0))
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* 0 empty, 1 has entries, 2 not a directory, else 100 + the error *)
fn op_empty {n:pos | n < 1048576} (s: string n, n: int n): int = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = (case+ $F.directory_emptiness(b, n) of
    | ~$F.DirectoryIsEmpty() => 0
    | ~$F.DirectoryHasEntries() => 1
    | ~$F.PathIsNotADirectory() => 2
    | ~$F.EmptinessFailed(e) => 100 + ecode(e))
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn op_exists {n:pos | n < 1048576} (s: string n, n: int n): bool = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = $F.file_exists(b, n)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* a file of 5 bytes, mode 0644 less the umask; true when made *)
fn op_make_file {n:pos | n < 1048576} (s: string n, n: int n): bool = let
  val p = path_of(s, n)
  val content = $A.alloc<byte>(5)
  val @(fz, b) = $A.freeze<byte>(p)
  val @(fc, bc) = $A.freeze<byte>(content)
  val made = (case+ $F.file_open(b, n, $F.WriteOnly(), $F.CreateOrTruncate(), 420) of
    | ~$R.err(_) => false
    | ~$R.ok(f) => let
        val w = $F.file_write(f, bc, 5)
        val ok = (case+ w of ~$R.ok(_) => true | ~$R.err(_) => false)
        val c = (case+ $F.file_close(f) of ~$R.ok(_) => true | ~$R.err(_) => false)
      in ok && c end)
  val () = $A.drop<byte>(fc, bc)
  val () = $A.free<byte>($A.thaw<byte>(fc))
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in made end

fn op_chmod {n:pos | n < 1048576} (s: string n, n: int n, mode: int): bool = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = (case+ $F.file_chmod(b, n, mode) of ~$R.ok(_) => true | ~$R.err(_) => false)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* 1 when the file at the path has an execute bit, 0 when not, -1 when its
   status could not be had *)
fn op_executable {n:pos | n < 1048576} (s: string n, n: int n): int = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = (case+ $F.file_info(b, n) of
    | ~$F.FileInfo(_, _, mode, _) => (if $F.mode_is_executable(mode) then 1 else 0)
    | ~$F.FileInfoFailed(_) => ~1)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn no (b: bool): bool = if b then false else true

(* the owner bits of a mode: 0 to 7 *)
fn owner_bits (mode: int): int = (mode / 64) % 8

(* The checks run left to right in the directory the caller has changed to,
   and stop at the first that fails (it names itself). *)

fn work_dirs (): bool =
  check("mkdirs three", op_mkdirs("a/b/c", 5, 493) = 3)
  && check("mkdirs again", op_mkdirs("a/b/c", 5, 493) = 0)
  && check("mkdirs one more", op_mkdirs("a/b/c/d", 7, 493) = 1)
  && check("mkdirs trailing slash", op_mkdirs("a/b/c/", 6, 493) = 0)
  && check("make file", op_make_file("a/file", 6))
  && check("mkdirs on a file", op_mkdirs("a/file", 6, 493) = 100 + ALREADY_EXISTS)
  && check("mkdirs under a file", op_mkdirs("a/file/x", 8, 493) = 100 + ALREADY_EXISTS)
  && check("mkdirs mode", op_mkdirs("p1/p2", 5, 292) = 2)
  && check("mkdirs parent has owner write and search", owner_bits((op_info("p1", 2)).3) = 7)
  && check("mkdirs last has the mode", owner_bits((op_info("p1/p2", 5)).3) = 4)
  && check("mkdirs deep", op_mkdirs_deep(260) = 260)
  && check("mkdirs deep again", op_mkdirs_deep(260) = 0)

fn work_info (): bool =
  check("info file", (let val i = op_info("a/file", 6) in
    i.0 = 0 && i.1 = 0 && i.2 = 5 && owner_bits(i.3) = 6 end))
  && check("info directory", (let val i = op_info("a", 1) in i.0 = 0 && i.1 = 1 end))
  && check("info missing", (op_info("nope", 4)).0 = 100 + NOT_FOUND)
  && check("info owner is ours", (op_info("a", 1)).4 = (op_info("a/file", 6)).4)
  && check("not executable", op_executable("a/file", 6) = 0)
  && check("chmod 0755", op_chmod("a/file", 6, 493))
  && check("owner executable", op_executable("a/file", 6) = 1)
  && check("chmod 0010", op_chmod("a/file", 6, 8))
  && check("group executable", op_executable("a/file", 6) = 1)
  && check("chmod 0001", op_chmod("a/file", 6, 1))
  && check("others executable", op_executable("a/file", 6) = 1)
  && check("chmod 0644", op_chmod("a/file", 6, 420))
  && check("not executable again", op_executable("a/file", 6) = 0)

fn work_symlinks (): bool =
  check("symlink", op_symlink("a/file", 6, "ln1", 3) = 0)
  && check("symlink exists", op_symlink("a/file", 6, "ln1", 3) = 100 + ALREADY_EXISTS)
  && check("read_link", op_read_link("ln1", 3, "a/file", 6, 16) = 0)
  && check("read_link buffer of the target's size", op_read_link("ln1", 3, "a/file", 6, 6) = 2)
  && check("read_link buffer of one more", op_read_link("ln1", 3, "a/file", 6, 7) = 0)
  && check("read_link of a file", op_read_link("a/file", 6, "x", 1, 16) = 3)
  && check("read_link of a missing name", op_read_link("nope", 4, "x", 1, 16) = 100 + NOT_FOUND)
  && check("info of a link", (let val i = op_info("ln1", 3) in i.0 = 0 && i.1 = 2 && i.2 = 6 end))
  && check("dangling symlink", op_symlink("missing-target", 14, "ln2", 3) = 0)
  && check("dangling info", (let val i = op_info("ln2", 3) in i.0 = 0 && i.1 = 2 && i.2 = 14 end))
  && check("dangling is not there", no(op_exists("ln2", 3)))
  && check("dangling read_link", op_read_link("ln2", 3, "missing-target", 14, 32) = 0)
  && check("self loop", op_symlink("ln3", 3, "ln3", 3) = 0)
  && check("self loop info", (let val i = op_info("ln3", 3) in i.0 = 0 && i.1 = 2 end))

fn work_remove (): bool =
  check("remove a link", op_remove("ln1", 3) = 0)
  && check("the link's target stays", op_exists("a/file", 6))
  && check("remove a dangling link", op_remove("ln2", 3) = 0)
  && check("remove a self loop", op_remove("ln3", 3) = 0)
  && check("remove a file", op_remove("a/file", 6) = 0)
  && check("remove it again", op_remove("a/file", 6) = 100 + NOT_FOUND)
  && check("make an empty directory", op_mkdirs("e1", 2, 493) = 1)
  && check("remove an empty directory", op_remove("e1", 2) = 1)
  && check("remove a directory with entries", op_remove("a", 1) = 100 + NOT_EMPTY)
  && check("link to a directory", op_symlink("a", 1, "lnd", 3) = 0)
  && check("remove the link to a directory", op_remove("lnd", 3) = 0)
  && check("the directory stays", op_exists("a/b/c", 5))

fn work_rename (): bool =
  check("make r1", op_make_file("r1", 2))
  && check("rename", op_rename("r1", 2, "r2", 2) = 0)
  && check("source is gone", no(op_exists("r1", 2)))
  && check("destination is there", (op_info("r2", 2)).2 = 5)
  && check("rename a missing name", op_rename("nope", 4, "x", 1) = 100 + NOT_FOUND)
  && check("make r3", op_make_file("r3", 2))
  && check("rename over a file", op_rename("r3", 2, "r2", 2) = 0)
  && check("make rd1", op_mkdirs("rd1/x", 5, 493) = 2)
  && check("make rd2", op_mkdirs("rd2/y", 5, 493) = 2)
  && check("rename a directory onto one with entries",
       (let val c = op_rename("rd1", 3, "rd2", 3) in c = 100 + NOT_EMPTY || c = 100 + ALREADY_EXISTS end))
  && check("rename a file onto a directory", op_rename("r2", 2, "rd2", 3) = 100 + 5)
  && check("rename a directory onto a file", op_rename("rd2", 3, "r2", 2) = 100 + NOT_A_DIRECTORY)
  && check("rename a directory to a new name", op_rename("rd1", 3, "rd3", 3) = 0)
  && check("the entries moved with it", op_exists("rd3/x", 5))
  && check("rename a link", op_symlink("rd3", 3, "lrd", 3) = 0 && op_rename("lrd", 3, "lrd2", 4) = 0)
  && check("the link was renamed, not its target", op_read_link("lrd2", 4, "rd3", 3, 8) = 0 && op_exists("rd3/x", 5))

fn work_empty (): bool =
  check("make a directory", op_mkdirs("em", 2, 493) = 1)
  && check("empty", op_empty("em", 2) = 0)
  && check("make a file in it", op_make_file("em/f", 4))
  && check("not empty", op_empty("em", 2) = 1)
  && check("a file is not a directory", op_empty("em/f", 4) = 2)
  && check("link to the directory", op_symlink("em", 2, "lem", 3) = 0)
  && check("a link to a directory is not a directory", op_empty("lem", 3) = 2)
  && check("missing", op_empty("nope", 4) = 100 + NOT_FOUND)

fn work_tree (): bool =
  check("build a tree", op_mkdirs("t/a/b/c", 7, 493) = 4
    && op_make_file("t/a/b/c/file", 12) && op_make_file("t/a/f", 5))
  && check("outside", op_mkdirs("outside", 7, 493) = 1 && op_make_file("outside/keep", 12))
  && check("links in the tree", op_symlink("../outside", 10, "t/link", 6) = 0
    && op_symlink("a/f", 3, "t/linkfile", 10) = 0 && op_symlink("nowhere", 7, "t/dangling", 10) = 0)
  && check("remove_tree removes all 4 directories, 2 files and 3 links",
       (let val r = op_tree("t", 1) in r.0 = 0 && r.1 = 9 end))
  && check("a link in the tree was not followed", op_exists("outside/keep", 12))
  && check("remove_tree of nothing", (op_tree("t", 1)).0 = 1)
  && check("refuses /", (op_tree("/", 1)).0 = 2)
  && check("refuses //", (op_tree("//", 2)).0 = 2)
  && check("refuses the empty path", (op_tree_empty()).0 = 2)
  && check("refuses /./", (op_tree("/./", 3)).0 = 3)
  && check("refuses .", (op_tree(".", 1)).0 = 3)
  && check("refuses ./", (op_tree("./", 2)).0 = 3)
  && check("refuses ..", (op_tree("..", 2)).0 = 3)
  && check("refuses ../", (op_tree("../", 3)).0 = 3)
  && check("refuses t/..", (op_tree("t/..", 4)).0 = 3)
  && check("refuses a/b/../.", (op_tree("a/b/../.", 8)).0 = 3)
  && check("the refusals touched nothing", op_exists("outside/keep", 12) && op_exists("a/b/c", 5))
  && check("a name that starts with dots", op_mkdirs("..x", 3, 493) = 1
    && (let val r = op_tree("..x", 3) in r.0 = 0 && r.1 = 1 end))
  && check("a link at the top is removed alone", op_symlink("outside", 7, "lnk", 3) = 0
    && (let val r = op_tree("lnk", 3) in r.0 = 0 && r.1 = 1 end) && op_exists("outside/keep", 12))
  && check("a file at the top", op_make_file("tf", 2)
    && (let val r = op_tree("tf", 2) in r.0 = 0 && r.1 = 1 end))
  && check("a tree too deep is left in part",
       (let val r = op_tree_deep(1) in
         if r.0 = 6 && r.1 = 0 && r.2 = 1 && r.3 = 0 && r.4 = INVALID_FILENAME then true
         else (println! ("got ", r.0, " ", r.1, " ", r.2, " ", r.3, " ", r.4); false) end))
  && check("its lower part is removed whole", (let val r = op_tree_deep(130) in r.0 = 0 && r.1 = 131 end))
  && check("then the rest", (let val r = op_tree_deep(1) in r.0 = 0 && r.1 = 129 end))

(* ---- mounts, made by the mount program (keyword: remove-tree-mounts) ----
   Two classes need a second file system inside the test's own directory: a
   mount point below the top (TreeLeftMounts) and an unlink the kernel
   refuses even to root (TreeLeftSome, here EROFS from a tmpfs remounted
   read-only). The test mounts a tmpfs there with mount(8), directly or
   through sudo -n, and unmounts it before it ends. Where neither is
   allowed it says SKIP and the reason, and passes: that is not a run of
   the class. *)
fn arg {sn:nat | sn <= 1024} (s: string sn): $P.arg_entry = let
  var b = $B.create()
  val () = $B.bput(b, s)
  val @(arr, len) = $B.to_arr(b)
in @(arr, len) end

fn code (o: $P.child_outcome): int =
  case+ o of
  | ~$P.child_exited(n) => n
  | ~$P.child_signaled(n) => 1000 + n
  | ~$P.child_wait_failed(e) => 2000 + e
  | ~$P.child_wait_unexpected(s) => 3000 + s

(* the program cmd (found on PATH) with argv, its exit status; 3000000 if it could not start *)
fn spawn_code {sn:nat | sn <= 1024} (cmd: string sn, argv: $L.listv($P.arg_entry)): int = let
  val (nul | pa) = $P.path_of_string_proved(cmd)
  val @(fp, bp) = $A.barr_freeze(pa)
  val r = $P.spawn_inherit_env_proved(nul | bp, argv, $P.dev_null(), $P.dev_null(), $P.dev_null())
  val () = $A.cborrow_drop(fp, bp)
  val () = $A.barr_free($A.barr_thaw(fp))
in
  case+ r of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(c, i, o, e) = sp
      val () = $P.pipe_end_close(i)
      val () = $P.pipe_end_close(o)
      val () = $P.pipe_end_close(e)
    in code($P.child_wait_outcome(c)) end
  | ~$R.err(_) => 3000000
end

(* via 0: mount directly, 1: through sudo -n *)
fn mount_tmpfs {sn:nat | sn <= 1024} (via: int, dir: string sn): int =
  if via = 0 then
    spawn_code("mount", $L.list_vt_cons(arg("mount"), $L.list_vt_cons(arg("-t"), $L.list_vt_cons(arg("tmpfs"),
      $L.list_vt_cons(arg("tmpfs"), $L.list_vt_cons(arg(dir), $L.list_vt_nil()))))))
  else
    spawn_code("sudo", $L.list_vt_cons(arg("sudo"), $L.list_vt_cons(arg("-n"), $L.list_vt_cons(arg("mount"),
      $L.list_vt_cons(arg("-t"), $L.list_vt_cons(arg("tmpfs"), $L.list_vt_cons(arg("tmpfs"),
      $L.list_vt_cons(arg(dir), $L.list_vt_nil()))))))))

fn remount_read_only {sn:nat | sn <= 1024} (via: int, dir: string sn): int =
  if via = 0 then
    spawn_code("mount", $L.list_vt_cons(arg("mount"), $L.list_vt_cons(arg("-o"), $L.list_vt_cons(arg("remount,ro"),
      $L.list_vt_cons(arg(dir), $L.list_vt_nil())))))
  else
    spawn_code("sudo", $L.list_vt_cons(arg("sudo"), $L.list_vt_cons(arg("-n"), $L.list_vt_cons(arg("mount"),
      $L.list_vt_cons(arg("-o"), $L.list_vt_cons(arg("remount,ro"), $L.list_vt_cons(arg(dir), $L.list_vt_nil())))))))

fn unmount {sn:nat | sn <= 1024} (via: int, dir: string sn): int =
  if via = 0 then
    spawn_code("umount", $L.list_vt_cons(arg("umount"), $L.list_vt_cons(arg(dir), $L.list_vt_nil())))
  else
    spawn_code("sudo", $L.list_vt_cons(arg("sudo"), $L.list_vt_cons(arg("-n"), $L.list_vt_cons(arg("umount"),
      $L.list_vt_cons(arg(dir), $L.list_vt_nil())))))

(* A mount point at the top is left alone: /proc is one on Linux (its own
   device), where it exists. *)
fn work_mount_top (): bool =
  if op_exists("/proc/self", 10) then
    check("a mount point at the top is left", (let val r = op_tree("/proc", 5) in
      r.0 = 5 && r.1 = 0 && r.3 = 1 end))
  else true

(* A tmpfs mounted at mt/sub, below the top mt: the walk removes what is on
   the top's device, leaves the mount point and what is in it, and says
   TreeLeftMounts (5). After the unmount the rest goes. *)
fn work_mount_below (via: int): bool = let
  val ready = ((op_mkdirs("mt/sub", 6, 493) = 2) && op_make_file("mt/f", 4))
  val mounted = (mount_tmpfs(via, "mt/sub") = 0)
  val inside = (if mounted then op_make_file("mt/sub/inner", 12) else false)
  val r = op_tree_when(mounted, "mt", 2)
  val inner_kept = op_exists("mt/sub/inner", 12)
  val sub_kept = op_exists("mt/sub", 6)
  val unmounted = (if mounted then (unmount(via, "mt/sub") = 0) else false)
  val rest = op_tree("mt", 2)
  val shown = (if r.0 = 5 && r.1 = 1 && r.2 = 0 && r.3 = 1 && r.4 = 0 then true else (println! ("mount below the top: got ", r.0, " ", r.1, " ", r.2, " ", r.3, " ", r.4); false))
in
  check("make mt and mt/f", ready) && check("mount a tmpfs at mt/sub", mounted)
  && check("a file inside the mount", inside)
  && check("a mount point below the top is left: TreeLeftMounts, mt/f removed, one mount",
       shown)
  && check("the mount and what is in it are untouched", inner_kept && sub_kept)
  && check("unmount", unmounted)
  && check("then the rest is removed: mt and mt/sub", rest.0 = 0 && rest.1 = 2)
end

(* A tmpfs mounted at ro, remounted read-only after ro/d/f and ro/d/x/g were
   made: every unlink fails with EROFS (7) even for root. The walk counts
   both, keeps the first reason, leaves the directories and says
   TreeLeftSome (6) with nothing removed. *)
fn work_unlink_refused (via: int): bool = let
  val mounted = ((op_mkdirs("ro", 2, 493) = 1) && (mount_tmpfs(via, "ro") = 0))
  val built = (if mounted then ((op_mkdirs("ro/d/x", 6, 493) = 2) && op_make_file("ro/d/f", 6)
    && op_make_file("ro/d/x/g", 8)) else false)
  val sealed = (if built then (remount_read_only(via, "ro") = 0) else false)
  val r = op_tree_when(sealed, "ro/d", 4)
  val f_kept = op_exists("ro/d/f", 6)
  val g_kept = op_exists("ro/d/x/g", 8)
  val unmounted = (if mounted then (unmount(via, "ro") = 0) else false)
  val shown = (if r.0 = 6 && r.1 = 0 && r.2 = 2 && r.3 = 0 && r.4 = 7 then true else (println! ("refused unlinks: got ", r.0, " ", r.1, " ", r.2, " ", r.3, " ", r.4); false))
in
  check("mount a tmpfs at ro and fill ro/d", mounted && built)
  && check("remount it read-only", sealed)
  && check("failed unlinks are counted and the first errno kept: TreeLeftSome, 0 removed, 2 kept, EROFS",
       shown)
  && check("what failed is still there", f_kept && g_kept)
  && check("unmount", unmounted)
end

(* the probe mount at "probe" when run holds, else ~1 *)
fn probe_mount (run: bool, via: int): int = if run then mount_tmpfs(via, "probe") else ~1
fn probe_unmount (run: bool, via: int): int = if run then unmount(via, "probe") else ~1

(* 0 when mount works directly, 1 through sudo -n, else ~1 (the two codes are printed) *)
fn mount_way (): int = let
  val made = (op_mkdirs("probe", 5, 493) = 1)
  val direct = probe_mount(made, 0)
  val direct_ok = (direct = 0)
  val _ = probe_unmount(direct_ok, 0)
  val sudo = probe_mount(made && not(direct_ok), 1)
  val sudo_ok = (sudo = 0)
  val _ = probe_unmount(sudo_ok, 1)
in
  if direct_ok then 0
  else if sudo_ok then 1
  else let val () = println! ("SKIP mounts: mount exited ", direct, ", sudo -n mount exited ", sudo,
    ": the mount-point and refused-unlink classes were not run here") in ~1 end
end

fn work_mount (): bool =
  work_mount_top() && (let val via = mount_way() in
    if via < 0 then true else work_mount_below(via) && work_unlink_refused(via) end)

fn work (): bool =
  work_dirs() && work_info() && work_symlinks() && work_remove() && work_rename()
  && work_empty() && work_tree() && work_mount()

(* The temporary directory: a name of the prefix and six more, 18 bytes. *)
implement main0 () = let
  val out = $A.alloc<byte>(64)
  val base_name = path_of("/tmp/file53-", 12)
  val @(fp, bp) = $A.freeze<byte>(base_name)
  val made = (case+ $F.file_make_temp_directory(bp, 12, out, 64) of
    | ~$F.TempDirectoryMade() => true
    | ~$F.TempDirectoryFailed(_) => false)
  val () = $A.drop<byte>(fp, bp)
  val () = $A.free<byte>($A.thaw<byte>(fp))
  val ok = (if no(made) then let val () = $A.free<byte>(out) in check("make_temp_directory", false) end else let
    val @(fo, bo) = $A.freeze<byte>(out)
    val @(name, rest) = $A.borrow_split<byte>(fo, bo, 18)
    val entered = (case+ $F.file_chdir(name, 18) of ~$R.ok(_) => true | ~$R.err(_) => false)
    val mode_ok = (case+ $F.file_mode(name, 18) of ~$R.ok(m) => m = 448 | ~$R.err(_) => false)
    val kind_ok = (case+ $F.file_info(name, 18) of
      | ~$F.FileInfo(kind, _, _, _) => (case+ kind of $F.Directory() => true | _ => false)
      | ~$F.FileInfoFailed(_) => false)
    val worked = (if entered && mode_ok && kind_ok then work() else check("enter the temporary directory", false))
    val rootok = (let
      val @(fr, br) = $A.freeze<byte>(path_of("/", 1))
      val r = (case+ $F.file_chdir(br, 1) of ~$R.ok(_) => true | ~$R.err(_) => false)
      val () = $A.drop<byte>(fr, br)
      val () = $A.free<byte>($A.thaw<byte>(fr))
    in r end)
    val removed = (case+ $F.file_remove_tree(name, 18) of
      | ~$F.TreeRemoved(c) => c >= 1
      | ~$F.TreeAbsent() => false
      | ~$F.TreeRefused(_) => false
      | ~$F.TreeFailed(_) => false
      | ~$F.TreeLeftMounts(_, _) => false
      | ~$F.TreeLeftSome(_, _, _, _) => false)
    val () = $A.drop<byte>(fo, $A.borrow_join<byte>(fo, name, rest))
    val () = $A.free<byte>($A.thaw<byte>(fo))
  in
    check("mode 0700", mode_ok) && check("a directory", kind_ok) && worked && rootok
    && check("the temporary directory is removed", removed)
  end)
in if ok then () else exit(1) end
