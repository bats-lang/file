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

(* ---- what an operation answered, as constructors (not numbers) ---- *)

datatype failure =
  | Not_failed
  | Failed_not_found
  | Failed_permission
  | Failed_exists
  | Failed_not_directory
  | Failed_is_directory
  | Failed_not_empty
  | Failed_read_only
  | Failed_loop
  | Failed_invalid_filename
  | Failed_invalid_input
  | Failed_crosses_devices
  | Failed_other

datatype shape =
  | Renamed_it
  | Rename_failed
  | Removed_a_file
  | Removed_an_empty_directory
  | Remove_failed
  | Made_directories
  | Directories_existed
  | Make_directories_failed
  | Symlink_made
  | Symlink_failed
  | Link_target_is_expected
  | Link_target_is_other
  | Link_target_too_long
  | Not_a_symlink
  | Read_link_failed
  | Directory_is_empty
  | Directory_has_entries
  | Path_is_not_a_directory
  | Emptiness_failed
  | Info_regular
  | Info_directory
  | Info_symlink
  | Info_other
  | Info_failed
  | Tree_removed
  | Tree_absent
  | Tree_refused_root
  | Tree_refused_dot_name
  | Tree_failed
  | Tree_left_mounts
  | Tree_left_some
  | Tree_not_tried

fn same_failure (a: failure, b: failure): bool =
  case+ a of
  | Not_failed() => (case+ b of Not_failed() => true | _ => false)
  | Failed_not_found() => (case+ b of Failed_not_found() => true | _ => false)
  | Failed_permission() => (case+ b of Failed_permission() => true | _ => false)
  | Failed_exists() => (case+ b of Failed_exists() => true | _ => false)
  | Failed_not_directory() => (case+ b of Failed_not_directory() => true | _ => false)
  | Failed_is_directory() => (case+ b of Failed_is_directory() => true | _ => false)
  | Failed_not_empty() => (case+ b of Failed_not_empty() => true | _ => false)
  | Failed_read_only() => (case+ b of Failed_read_only() => true | _ => false)
  | Failed_loop() => (case+ b of Failed_loop() => true | _ => false)
  | Failed_invalid_filename() => (case+ b of Failed_invalid_filename() => true | _ => false)
  | Failed_invalid_input() => (case+ b of Failed_invalid_input() => true | _ => false)
  | Failed_crosses_devices() => (case+ b of Failed_crosses_devices() => true | _ => false)
  | Failed_other() => (case+ b of Failed_other() => true | _ => false)

fn same_shape (a: shape, b: shape): bool =
  case+ a of
  | Renamed_it() => (case+ b of Renamed_it() => true | _ => false)
  | Rename_failed() => (case+ b of Rename_failed() => true | _ => false)
  | Removed_a_file() => (case+ b of Removed_a_file() => true | _ => false)
  | Removed_an_empty_directory() => (case+ b of Removed_an_empty_directory() => true | _ => false)
  | Remove_failed() => (case+ b of Remove_failed() => true | _ => false)
  | Made_directories() => (case+ b of Made_directories() => true | _ => false)
  | Directories_existed() => (case+ b of Directories_existed() => true | _ => false)
  | Make_directories_failed() => (case+ b of Make_directories_failed() => true | _ => false)
  | Symlink_made() => (case+ b of Symlink_made() => true | _ => false)
  | Symlink_failed() => (case+ b of Symlink_failed() => true | _ => false)
  | Link_target_is_expected() => (case+ b of Link_target_is_expected() => true | _ => false)
  | Link_target_is_other() => (case+ b of Link_target_is_other() => true | _ => false)
  | Link_target_too_long() => (case+ b of Link_target_too_long() => true | _ => false)
  | Not_a_symlink() => (case+ b of Not_a_symlink() => true | _ => false)
  | Read_link_failed() => (case+ b of Read_link_failed() => true | _ => false)
  | Directory_is_empty() => (case+ b of Directory_is_empty() => true | _ => false)
  | Directory_has_entries() => (case+ b of Directory_has_entries() => true | _ => false)
  | Path_is_not_a_directory() => (case+ b of Path_is_not_a_directory() => true | _ => false)
  | Emptiness_failed() => (case+ b of Emptiness_failed() => true | _ => false)
  | Info_regular() => (case+ b of Info_regular() => true | _ => false)
  | Info_directory() => (case+ b of Info_directory() => true | _ => false)
  | Info_symlink() => (case+ b of Info_symlink() => true | _ => false)
  | Info_other() => (case+ b of Info_other() => true | _ => false)
  | Info_failed() => (case+ b of Info_failed() => true | _ => false)
  | Tree_removed() => (case+ b of Tree_removed() => true | _ => false)
  | Tree_absent() => (case+ b of Tree_absent() => true | _ => false)
  | Tree_refused_root() => (case+ b of Tree_refused_root() => true | _ => false)
  | Tree_refused_dot_name() => (case+ b of Tree_refused_dot_name() => true | _ => false)
  | Tree_failed() => (case+ b of Tree_failed() => true | _ => false)
  | Tree_left_mounts() => (case+ b of Tree_left_mounts() => true | _ => false)
  | Tree_left_some() => (case+ b of Tree_left_some() => true | _ => false)
  | Tree_not_tried() => (case+ b of Tree_not_tried() => true | _ => false)

fn failure_name (a: failure): string =
  case+ a of
  | Not_failed() => "Not_failed"
  | Failed_not_found() => "Failed_not_found"
  | Failed_permission() => "Failed_permission"
  | Failed_exists() => "Failed_exists"
  | Failed_not_directory() => "Failed_not_directory"
  | Failed_is_directory() => "Failed_is_directory"
  | Failed_not_empty() => "Failed_not_empty"
  | Failed_read_only() => "Failed_read_only"
  | Failed_loop() => "Failed_loop"
  | Failed_invalid_filename() => "Failed_invalid_filename"
  | Failed_invalid_input() => "Failed_invalid_input"
  | Failed_crosses_devices() => "Failed_crosses_devices"
  | Failed_other() => "Failed_other"

fn shape_name (a: shape): string =
  case+ a of
  | Renamed_it() => "Renamed_it"
  | Rename_failed() => "Rename_failed"
  | Removed_a_file() => "Removed_a_file"
  | Removed_an_empty_directory() => "Removed_an_empty_directory"
  | Remove_failed() => "Remove_failed"
  | Made_directories() => "Made_directories"
  | Directories_existed() => "Directories_existed"
  | Make_directories_failed() => "Make_directories_failed"
  | Symlink_made() => "Symlink_made"
  | Symlink_failed() => "Symlink_failed"
  | Link_target_is_expected() => "Link_target_is_expected"
  | Link_target_is_other() => "Link_target_is_other"
  | Link_target_too_long() => "Link_target_too_long"
  | Not_a_symlink() => "Not_a_symlink"
  | Read_link_failed() => "Read_link_failed"
  | Directory_is_empty() => "Directory_is_empty"
  | Directory_has_entries() => "Directory_has_entries"
  | Path_is_not_a_directory() => "Path_is_not_a_directory"
  | Emptiness_failed() => "Emptiness_failed"
  | Info_regular() => "Info_regular"
  | Info_directory() => "Info_directory"
  | Info_symlink() => "Info_symlink"
  | Info_other() => "Info_other"
  | Info_failed() => "Info_failed"
  | Tree_removed() => "Tree_removed"
  | Tree_absent() => "Tree_absent"
  | Tree_refused_root() => "Tree_refused_root"
  | Tree_refused_dot_name() => "Tree_refused_dot_name"
  | Tree_failed() => "Tree_failed"
  | Tree_left_mounts() => "Tree_left_mounts"
  | Tree_left_some() => "Tree_left_some"
  | Tree_not_tried() => "Tree_not_tried"

fn failure_of (e: $F.io_error): failure =
  case+ e of
  | $F.NotFound() => Failed_not_found()
  | $F.PermissionDenied() => Failed_permission()
  | $F.AlreadyExists() => Failed_exists()
  | $F.NotADirectory() => Failed_not_directory()
  | $F.IsADirectory() => Failed_is_directory()
  | $F.DirectoryNotEmpty() => Failed_not_empty()
  | $F.ReadOnlyFilesystem() => Failed_read_only()
  | $F.FilesystemLoop() => Failed_loop()
  | $F.InvalidFilename() => Failed_invalid_filename()
  | $F.InvalidInput() => Failed_invalid_input()
  | $F.CrossesDevices() => Failed_crosses_devices()
  | _ => Failed_other()

typedef answer = @{what= shape, why= failure}
typedef dirs_answer = @{what= shape, why= failure, made= int}
typedef info_answer = @{what= shape, why= failure, size= int, mode= int, owner= int}
typedef tree_answer = @{what= shape, why= failure, removed= int, kept= int, mounts= int}

fn answered (s: shape): answer = @{what= s, why= Not_failed()}
fn answered_failing (s: shape, e: $F.io_error): answer = @{what= s, why= failure_of(e)}

fn answer_is (a: answer, s: shape, f: failure): bool = same_shape(a.what, s) && same_failure(a.why, f)
fn answered_with (a: answer, s: shape): bool = answer_is(a, s, Not_failed())

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

(* ---- the operations, each answering with constructors ---- *)

fn op_rename {ns,nd:pos | ns < 1048576; nd < 1048576}
  (source: string ns, ns: int ns, destination: string nd, nd: int nd): answer = let
  val ps = path_of(source, ns)
  val pd = path_of(destination, nd)
  val @(fs, bs) = $A.freeze<byte>(ps)
  val @(fd, bd) = $A.freeze<byte>(pd)
  val r = (case+ $F.file_rename(bs, ns, bd, nd) of
    | ~$F.Renamed() => answered(Renamed_it())
    | ~$F.RenameFailed(e) => answered_failing(Rename_failed(), e))
  val () = $A.drop<byte>(fs, bs)
  val () = $A.free<byte>($A.thaw<byte>(fs))
  val () = $A.drop<byte>(fd, bd)
  val () = $A.free<byte>($A.thaw<byte>(fd))
in r end

fn op_remove {n:pos | n < 1048576} (s: string n, n: int n): answer = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = (case+ $F.file_remove(b, n) of
    | ~$F.RemovedFile() => answered(Removed_a_file())
    | ~$F.RemovedEmptyDirectory() => answered(Removed_an_empty_directory())
    | ~$F.RemoveFailed(e) => answered_failing(Remove_failed(), e))
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn tree_answered (s: shape, f: failure, removed: int, kept: int, mounts: int): tree_answer =
  @{what= s, why= f, removed= removed, kept= kept, mounts= mounts}

fn tree_code {lb:agz}{n:pos | n < 1048576}
  (b: !$A.borrow(byte, lb, n), n: int n): tree_answer =
  case+ $F.file_remove_tree(b, n) of
  | ~$F.TreeRemoved(r) => tree_answered(Tree_removed(), Not_failed(), r, 0, 0)
  | ~$F.TreeAbsent() => tree_answered(Tree_absent(), Not_failed(), 0, 0, 0)
  | ~$F.TreeRefused(why) => (case+ why of
      | $F.RefusedRoot() => tree_answered(Tree_refused_root(), Not_failed(), 0, 0, 0)
      | $F.RefusedDotName() => tree_answered(Tree_refused_dot_name(), Not_failed(), 0, 0, 0))
  | ~$F.TreeFailed(e) => tree_answered(Tree_failed(), failure_of(e), 0, 0, 0)
  | ~$F.TreeLeftMounts(r, m) => tree_answered(Tree_left_mounts(), Not_failed(), r, 0, m)
  | ~$F.TreeLeftSome(r, k, m, e) => tree_answered(Tree_left_some(), failure_of(e), r, k, m)

fn op_tree {n:pos | n < 1048576} (s: string n, n: int n): tree_answer = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = tree_code(b, n)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* the empty path: one byte, a NUL, which the C side reads as "" *)
fn op_tree_empty (): tree_answer = let
  val p = $A.alloc<byte>(1)
  val () = $A.set<byte>(p, 0, $A.int2byte(0))
  val @(fz, b) = $A.freeze<byte>(p)
  val r = tree_code(b, 1)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn op_tree_when {n:pos | n < 1048576} (c: bool, s: string n, n: int n): tree_answer =
  if c then op_tree(s, n) else tree_answered(Tree_not_tried(), Not_failed(), 0, 0, 0)

fn op_tree_deep {k:pos | k <= 500} (k: int k): tree_answer = let
  val p = deep_path(k)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = tree_code(b, 2 * k - 1)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn tree_is (r: tree_answer, s: shape): bool = same_shape(r.what, s)

fn tree_removed (r: tree_answer, removed: int): bool =
  tree_is(r, Tree_removed()) && r.removed = removed

fn dirs_answered (s: shape, f: failure, made: int): dirs_answer = @{what= s, why= f, made= made}

fn mkdirs_code {lb:agz}{n:pos | n < 1048576}{m:nat | m <= 4095}
  (b: !$A.borrow(byte, lb, n), n: int n, mode: int m): dirs_answer =
  case+ $F.file_make_directories(b, n, mode) of
  | ~$F.DirectoriesCreated(c) => dirs_answered(Made_directories(), Not_failed(), c)
  | ~$F.DirectoryExisted() => dirs_answered(Directories_existed(), Not_failed(), 0)
  | ~$F.MakeDirectoriesFailed(e) => dirs_answered(Make_directories_failed(), failure_of(e), 0)

fn op_mkdirs {n:pos | n < 1048576}{m:nat | m <= 4095} (s: string n, n: int n, mode: int m): dirs_answer = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = mkdirs_code(b, n, mode)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn op_mkdirs_deep {k:pos | k <= 500} (k: int k): dirs_answer = let
  val p = deep_path(k)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = mkdirs_code(b, 2 * k - 1, 493)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn made_dirs (r: dirs_answer, made: int): bool =
  same_shape(r.what, Made_directories()) && r.made = made

fn dirs_existed (r: dirs_answer): bool = same_shape(r.what, Directories_existed())

fn dirs_failed (r: dirs_answer, f: failure): bool =
  same_shape(r.what, Make_directories_failed()) && same_failure(r.why, f)

fn op_symlink {nt,np:pos | nt < 1048576; np < 1048576}
  (target: string nt, nt: int nt, path: string np, np: int np): answer = let
  val pt = path_of(target, nt)
  val pp = path_of(path, np)
  val @(ft, bt) = $A.freeze<byte>(pt)
  val @(fp, bp) = $A.freeze<byte>(pp)
  val r = (case+ $F.file_symlink(bt, nt, bp, np) of
    | ~$F.SymlinkMade() => answered(Symlink_made())
    | ~$F.SymlinkFailed(e) => answered_failing(Symlink_failed(), e))
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

fn read_link_code {lb:agz}{n:pos | n < 1048576}{lo:agz}{ne:pos}{m:pos}
  (b: !$A.borrow(byte, lb, n), n: int n, out: !$A.arr(byte, lo, m), m: int m,
   expected: string ne, ne: int ne): answer =
  case+ $F.file_read_link(b, n, out, m) of
  | ~$F.LinkTarget(k) =>
      (if k = ne then
         (if same_bytes(out, $A.text_lit(expected), 0, ne) then answered(Link_target_is_expected())
          else answered(Link_target_is_other()))
       else answered(Link_target_is_other()))
  | ~$F.LinkTargetTooLong() => answered(Link_target_too_long())
  | ~$F.NotASymlink() => answered(Not_a_symlink())
  | ~$F.ReadLinkFailed(e) => answered_failing(Read_link_failed(), e)

fn op_read_link {n:pos | n < 1048576}{ne:pos}{m:pos | m <= 1048576}
  (s: string n, n: int n, expected: string ne, ne: int ne, m: int m): answer = let
  val p = path_of(s, n)
  val out = $A.alloc<byte>(m)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = read_link_code(b, n, out, m, expected, ne)
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
  val () = $A.free<byte>(out)
in r end

fn info_answered (s: shape, f: failure, size: int, mode: int, owner: int): info_answer =
  @{what= s, why= f, size= size, mode= mode, owner= owner}

fn op_info {n:pos | n < 1048576} (s: string n, n: int n): info_answer = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = (case+ $F.file_info(b, n) of
    | ~$F.FileInfo(kind, size, mode, owner) => info_answered(
        (case+ kind of
         | $F.RegularFile() => Info_regular()
         | $F.Directory() => Info_directory()
         | $F.Symlink() => Info_symlink()
         | $F.OtherFile() => Info_other()),
        Not_failed(), size, mode, owner)
    | ~$F.FileInfoFailed(e) => info_answered(Info_failed(), failure_of(e), 0, 0, 0))
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn info_is (i: info_answer, s: shape): bool = same_shape(i.what, s)

fn info_has_size (i: info_answer, s: shape, size: int): bool = info_is(i, s) && i.size = size

fn op_empty {n:pos | n < 1048576} (s: string n, n: int n): answer = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = (case+ $F.directory_emptiness(b, n) of
    | ~$F.DirectoryIsEmpty() => answered(Directory_is_empty())
    | ~$F.DirectoryHasEntries() => answered(Directory_has_entries())
    | ~$F.PathIsNotADirectory() => answered(Path_is_not_a_directory())
    | ~$F.EmptinessFailed(e) => answered_failing(Emptiness_failed(), e))
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

datatype execute_bits =
  | Has_execute_bit
  | Has_no_execute_bit
  | Status_not_had

fn op_executable {n:pos | n < 1048576} (s: string n, n: int n): execute_bits = let
  val p = path_of(s, n)
  val @(fz, b) = $A.freeze<byte>(p)
  val r = (case+ $F.file_info(b, n) of
    | ~$F.FileInfo(_, _, mode, _) => (if $F.mode_is_executable(mode) then Has_execute_bit() else Has_no_execute_bit())
    | ~$F.FileInfoFailed(_) => Status_not_had())
  val () = $A.drop<byte>(fz, b)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fn executable (x: execute_bits): bool = (case+ x of Has_execute_bit() => true | _ => false)
fn not_executable (x: execute_bits): bool = (case+ x of Has_no_execute_bit() => true | _ => false)

fn no (b: bool): bool = if b then false else true

(* the owner bits of a mode: 0 to 7 *)
fn owner_bits (mode: int): int = (mode / 64) % 8

fn renamed (a: answer): bool = answered_with(a, Renamed_it())
fn symlinked (a: answer): bool = answered_with(a, Symlink_made())
fn removed_file (a: answer): bool = answered_with(a, Removed_a_file())
fn removed_empty_directory (a: answer): bool = answered_with(a, Removed_an_empty_directory())

(* The checks run left to right in the directory the caller has changed to,
   and stop at the first that fails (it names itself). *)

fn work_dirs (): bool =
  check("mkdirs three", made_dirs(op_mkdirs("a/b/c", 5, 493), 3))
  && check("mkdirs again", dirs_existed(op_mkdirs("a/b/c", 5, 493)))
  && check("mkdirs one more", made_dirs(op_mkdirs("a/b/c/d", 7, 493), 1))
  && check("mkdirs trailing slash", dirs_existed(op_mkdirs("a/b/c/", 6, 493)))
  && check("make file", op_make_file("a/file", 6))
  && check("mkdirs on a file", dirs_failed(op_mkdirs("a/file", 6, 493), Failed_exists()))
  && check("mkdirs under a file", dirs_failed(op_mkdirs("a/file/x", 8, 493), Failed_exists()))
  && check("mkdirs mode", made_dirs(op_mkdirs("p1/p2", 5, 292), 2))
  && check("mkdirs parent has owner write and search", owner_bits((op_info("p1", 2)).mode) = 7)
  && check("mkdirs last has the mode", owner_bits((op_info("p1/p2", 5)).mode) = 4)
  && check("mkdirs deep", made_dirs(op_mkdirs_deep(260), 260))
  && check("mkdirs deep again", dirs_existed(op_mkdirs_deep(260)))

fn work_info (): bool =
  check("info file", (let val i = op_info("a/file", 6) in
    info_has_size(i, Info_regular(), 5) && owner_bits(i.mode) = 6 end))
  && check("info directory", info_is(op_info("a", 1), Info_directory()))
  && check("info missing", (let val i = op_info("nope", 4) in
    info_is(i, Info_failed()) && same_failure(i.why, Failed_not_found()) end))
  && check("info owner is ours", (op_info("a", 1)).owner = (op_info("a/file", 6)).owner)
  && check("not executable", not_executable(op_executable("a/file", 6)))
  && check("chmod 0755", op_chmod("a/file", 6, 493))
  && check("owner executable", executable(op_executable("a/file", 6)))
  && check("chmod 0010", op_chmod("a/file", 6, 8))
  && check("group executable", executable(op_executable("a/file", 6)))
  && check("chmod 0001", op_chmod("a/file", 6, 1))
  && check("others executable", executable(op_executable("a/file", 6)))
  && check("chmod 0644", op_chmod("a/file", 6, 420))
  && check("not executable again", not_executable(op_executable("a/file", 6)))

fn work_symlinks (): bool =
  check("symlink", symlinked(op_symlink("a/file", 6, "ln1", 3)))
  && check("symlink exists", answer_is(op_symlink("a/file", 6, "ln1", 3), Symlink_failed(), Failed_exists()))
  && check("read_link", answered_with(op_read_link("ln1", 3, "a/file", 6, 16), Link_target_is_expected()))
  && check("read_link buffer of the target's size",
       answered_with(op_read_link("ln1", 3, "a/file", 6, 6), Link_target_too_long()))
  && check("read_link buffer of one more",
       answered_with(op_read_link("ln1", 3, "a/file", 6, 7), Link_target_is_expected()))
  && check("read_link of a file", answered_with(op_read_link("a/file", 6, "x", 1, 16), Not_a_symlink()))
  && check("read_link of a missing name",
       answer_is(op_read_link("nope", 4, "x", 1, 16), Read_link_failed(), Failed_not_found()))
  && check("info of a link", info_has_size(op_info("ln1", 3), Info_symlink(), 6))
  && check("dangling symlink", symlinked(op_symlink("missing-target", 14, "ln2", 3)))
  && check("dangling info", info_has_size(op_info("ln2", 3), Info_symlink(), 14))
  && check("dangling is not there", no(op_exists("ln2", 3)))
  && check("dangling read_link",
       answered_with(op_read_link("ln2", 3, "missing-target", 14, 32), Link_target_is_expected()))
  && check("self loop", symlinked(op_symlink("ln3", 3, "ln3", 3)))
  && check("self loop info", info_is(op_info("ln3", 3), Info_symlink()))

fn work_remove (): bool =
  check("remove a link", removed_file(op_remove("ln1", 3)))
  && check("the link's target stays", op_exists("a/file", 6))
  && check("remove a dangling link", removed_file(op_remove("ln2", 3)))
  && check("remove a self loop", removed_file(op_remove("ln3", 3)))
  && check("remove a file", removed_file(op_remove("a/file", 6)))
  && check("remove it again", answer_is(op_remove("a/file", 6), Remove_failed(), Failed_not_found()))
  && check("make an empty directory", made_dirs(op_mkdirs("e1", 2, 493), 1))
  && check("remove an empty directory", removed_empty_directory(op_remove("e1", 2)))
  && check("remove a directory with entries",
       answer_is(op_remove("a", 1), Remove_failed(), Failed_not_empty()))
  && check("link to a directory", symlinked(op_symlink("a", 1, "lnd", 3)))
  && check("remove the link to a directory", removed_file(op_remove("lnd", 3)))
  && check("the directory stays", op_exists("a/b/c", 5))

fn work_rename (): bool =
  check("make r1", op_make_file("r1", 2))
  && check("rename", renamed(op_rename("r1", 2, "r2", 2)))
  && check("source is gone", no(op_exists("r1", 2)))
  && check("destination is there", info_has_size(op_info("r2", 2), Info_regular(), 5))
  && check("rename a missing name",
       answer_is(op_rename("nope", 4, "x", 1), Rename_failed(), Failed_not_found()))
  && check("make r3", op_make_file("r3", 2))
  && check("rename over a file", renamed(op_rename("r3", 2, "r2", 2)))
  && check("make rd1", made_dirs(op_mkdirs("rd1/x", 5, 493), 2))
  && check("make rd2", made_dirs(op_mkdirs("rd2/y", 5, 493), 2))
  && check("rename a directory onto one with entries",
       (let val a = op_rename("rd1", 3, "rd2", 3) in
         answer_is(a, Rename_failed(), Failed_not_empty()) || answer_is(a, Rename_failed(), Failed_exists()) end))
  && check("rename a file onto a directory",
       answer_is(op_rename("r2", 2, "rd2", 3), Rename_failed(), Failed_is_directory()))
  && check("rename a directory onto a file",
       answer_is(op_rename("rd2", 3, "r2", 2), Rename_failed(), Failed_not_directory()))
  && check("rename a directory to a new name", renamed(op_rename("rd1", 3, "rd3", 3)))
  && check("the entries moved with it", op_exists("rd3/x", 5))
  && check("rename a link", symlinked(op_symlink("rd3", 3, "lrd", 3)) && renamed(op_rename("lrd", 3, "lrd2", 4)))
  && check("the link was renamed, not its target",
       answered_with(op_read_link("lrd2", 4, "rd3", 3, 8), Link_target_is_expected()) && op_exists("rd3/x", 5))

fn work_empty (): bool =
  check("make a directory", made_dirs(op_mkdirs("em", 2, 493), 1))
  && check("empty", answered_with(op_empty("em", 2), Directory_is_empty()))
  && check("make a file in it", op_make_file("em/f", 4))
  && check("not empty", answered_with(op_empty("em", 2), Directory_has_entries()))
  && check("a file is not a directory", answered_with(op_empty("em/f", 4), Path_is_not_a_directory()))
  && check("link to the directory", symlinked(op_symlink("em", 2, "lem", 3)))
  && check("a link to a directory is not a directory",
       answered_with(op_empty("lem", 3), Path_is_not_a_directory()))
  && check("missing", answer_is(op_empty("nope", 4), Emptiness_failed(), Failed_not_found()))

fn work_tree (): bool =
  check("build a tree", made_dirs(op_mkdirs("t/a/b/c", 7, 493), 4)
    && op_make_file("t/a/b/c/file", 12) && op_make_file("t/a/f", 5))
  && check("outside", made_dirs(op_mkdirs("outside", 7, 493), 1) && op_make_file("outside/keep", 12))
  && check("links in the tree", symlinked(op_symlink("../outside", 10, "t/link", 6))
    && symlinked(op_symlink("a/f", 3, "t/linkfile", 10)) && symlinked(op_symlink("nowhere", 7, "t/dangling", 10)))
  && check("remove_tree removes all 4 directories, 2 files and 3 links",
       tree_removed(op_tree("t", 1), 9))
  && check("a link in the tree was not followed", op_exists("outside/keep", 12))
  && check("remove_tree of nothing", tree_is(op_tree("t", 1), Tree_absent()))
  && check("refuses /", tree_is(op_tree("/", 1), Tree_refused_root()))
  && check("refuses //", tree_is(op_tree("//", 2), Tree_refused_root()))
  && check("refuses the empty path", tree_is(op_tree_empty(), Tree_refused_root()))
  && check("refuses /./", tree_is(op_tree("/./", 3), Tree_refused_dot_name()))
  && check("refuses .", tree_is(op_tree(".", 1), Tree_refused_dot_name()))
  && check("refuses ./", tree_is(op_tree("./", 2), Tree_refused_dot_name()))
  && check("refuses ..", tree_is(op_tree("..", 2), Tree_refused_dot_name()))
  && check("refuses ../", tree_is(op_tree("../", 3), Tree_refused_dot_name()))
  && check("refuses t/..", tree_is(op_tree("t/..", 4), Tree_refused_dot_name()))
  && check("refuses a/b/../.", tree_is(op_tree("a/b/../.", 8), Tree_refused_dot_name()))
  && check("the refusals touched nothing", op_exists("outside/keep", 12) && op_exists("a/b/c", 5))
  && check("a name that starts with dots", made_dirs(op_mkdirs("..x", 3, 493), 1)
    && tree_removed(op_tree("..x", 3), 1))
  && check("a link at the top is removed alone", symlinked(op_symlink("outside", 7, "lnk", 3))
    && tree_removed(op_tree("lnk", 3), 1) && op_exists("outside/keep", 12))
  && check("a file at the top", op_make_file("tf", 2) && tree_removed(op_tree("tf", 2), 1))
  && check("a tree too deep is left in part",
       (let val r = op_tree_deep(1) in
         if tree_is(r, Tree_left_some()) && r.removed = 0 && r.kept = 1 && r.mounts = 0
            && same_failure(r.why, Failed_invalid_filename()) then true
         else (println! ("got ", shape_name(r.what), " ", r.removed, " ", r.kept, " ", r.mounts, " ",
           failure_name(r.why)); false) end))
  && check("its lower part is removed whole", tree_removed(op_tree_deep(130), 131))
  && check("then the rest", tree_removed(op_tree_deep(1), 129))

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

datatype spawn_outcome =
  | Spawn_exited_zero
  | Spawn_exited_nonzero
  | Spawn_signaled
  | Spawn_wait_failed
  | Spawn_wait_unexpected
  | Spawn_not_started
  | Spawn_not_run

fn spawn_name (o: spawn_outcome): string =
  case+ o of
  | Spawn_exited_zero() => "Spawn_exited_zero"
  | Spawn_exited_nonzero() => "Spawn_exited_nonzero"
  | Spawn_signaled() => "Spawn_signaled"
  | Spawn_wait_failed() => "Spawn_wait_failed"
  | Spawn_wait_unexpected() => "Spawn_wait_unexpected"
  | Spawn_not_started() => "Spawn_not_started"
  | Spawn_not_run() => "Spawn_not_run"

fn spawned_ok (o: spawn_outcome): bool = (case+ o of Spawn_exited_zero() => true | _ => false)

fn outcome_of (o: $P.child_outcome): spawn_outcome =
  case+ o of
  | ~$P.child_exited(n) => (if n = 0 then Spawn_exited_zero() else Spawn_exited_nonzero())
  | ~$P.child_signaled(_) => Spawn_signaled()
  | ~$P.child_wait_failed(_) => Spawn_wait_failed()
  | ~$P.child_wait_unexpected(_) => Spawn_wait_unexpected()

(* the program cmd (found on PATH) with argv, how it ended *)
fn spawn_code {sn:nat | sn <= 1024} (cmd: string sn, argv: $L.listv($P.arg_entry)): spawn_outcome = let
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
    in outcome_of($P.child_wait_outcome(c)) end
  | ~$R.err(_) => Spawn_not_started()
end

datatype mount_way =
  | Mount_directly
  | Mount_through_sudo
  | Mount_unavailable

fn mount_tmpfs {sn:nat | sn <= 1024} (via: mount_way, dir: string sn): spawn_outcome =
  case+ via of
  | Mount_directly() =>
    spawn_code("mount", $L.list_vt_cons(arg("mount"), $L.list_vt_cons(arg("-t"), $L.list_vt_cons(arg("tmpfs"),
      $L.list_vt_cons(arg("tmpfs"), $L.list_vt_cons(arg(dir), $L.list_vt_nil()))))))
  | Mount_through_sudo() =>
    spawn_code("sudo", $L.list_vt_cons(arg("sudo"), $L.list_vt_cons(arg("-n"), $L.list_vt_cons(arg("mount"),
      $L.list_vt_cons(arg("-t"), $L.list_vt_cons(arg("tmpfs"), $L.list_vt_cons(arg("tmpfs"),
      $L.list_vt_cons(arg(dir), $L.list_vt_nil()))))))))
  | Mount_unavailable() => Spawn_not_run()

fn remount_read_only {sn:nat | sn <= 1024} (via: mount_way, dir: string sn): spawn_outcome =
  case+ via of
  | Mount_directly() =>
    spawn_code("mount", $L.list_vt_cons(arg("mount"), $L.list_vt_cons(arg("-o"), $L.list_vt_cons(arg("remount,ro"),
      $L.list_vt_cons(arg(dir), $L.list_vt_nil())))))
  | Mount_through_sudo() =>
    spawn_code("sudo", $L.list_vt_cons(arg("sudo"), $L.list_vt_cons(arg("-n"), $L.list_vt_cons(arg("mount"),
      $L.list_vt_cons(arg("-o"), $L.list_vt_cons(arg("remount,ro"), $L.list_vt_cons(arg(dir), $L.list_vt_nil())))))))
  | Mount_unavailable() => Spawn_not_run()

fn unmount {sn:nat | sn <= 1024} (via: mount_way, dir: string sn): spawn_outcome =
  case+ via of
  | Mount_directly() =>
    spawn_code("umount", $L.list_vt_cons(arg("umount"), $L.list_vt_cons(arg(dir), $L.list_vt_nil())))
  | Mount_through_sudo() =>
    spawn_code("sudo", $L.list_vt_cons(arg("sudo"), $L.list_vt_cons(arg("-n"), $L.list_vt_cons(arg("umount"),
      $L.list_vt_cons(arg(dir), $L.list_vt_nil())))))
  | Mount_unavailable() => Spawn_not_run()

(* A mount point at the top is left alone: /proc is one on Linux (its own
   device), where it exists. *)
fn work_mount_top (): bool =
  if op_exists("/proc/self", 10) then
    check("a mount point at the top is left", (let val r = op_tree("/proc", 5) in
      tree_is(r, Tree_left_mounts()) && r.removed = 0 && r.mounts = 1 end))
  else true

(* A tmpfs mounted at mt/sub, below the top mt: a rename of mt/f into it
   crosses devices; the walk removes what is on the top's device, leaves the
   mount point and what is in it, and says TreeLeftMounts. After the unmount
   the rest goes. *)
fn work_mount_below (via: mount_way): bool = let
  val ready = (made_dirs(op_mkdirs("mt/sub", 6, 493), 2) && op_make_file("mt/f", 4))
  val mounted = spawned_ok(mount_tmpfs(via, "mt/sub"))
  val inside = (if mounted then op_make_file("mt/sub/inner", 12) else false)
  val crossing = (if mounted then op_rename("mt/f", 4, "mt/sub/moved", 12)
    else answered(Renamed_it()))
  val r = op_tree_when(mounted, "mt", 2)
  val inner_kept = op_exists("mt/sub/inner", 12)
  val sub_kept = op_exists("mt/sub", 6)
  val unmounted = (if mounted then spawned_ok(unmount(via, "mt/sub")) else false)
  val rest = op_tree("mt", 2)
  val shown = (if tree_is(r, Tree_left_mounts()) && r.removed = 1 && r.kept = 0 && r.mounts = 1
      && same_failure(r.why, Not_failed()) then true
    else (println! ("mount below the top: got ", shape_name(r.what), " ", r.removed, " ", r.kept, " ", r.mounts,
      " ", failure_name(r.why)); false))
in
  check("make mt and mt/f", ready) && check("mount a tmpfs at mt/sub", mounted)
  && check("a file inside the mount", inside)
  && check("a rename into the mount crosses devices: CrossesDevices",
       answer_is(crossing, Rename_failed(), Failed_crosses_devices()))
  && check("a mount point below the top is left: TreeLeftMounts, mt/f removed, one mount",
       shown)
  && check("the mount and what is in it are untouched", inner_kept && sub_kept)
  && check("unmount", unmounted)
  && check("then the rest is removed: mt and mt/sub", tree_removed(rest, 2))
end

(* A tmpfs mounted at ro, remounted read-only after ro/d/f and ro/d/x/g were
   made: every unlink fails with EROFS even for root. The walk counts both,
   keeps the first reason, leaves the directories and says TreeLeftSome with
   nothing removed. *)
fn work_unlink_refused (via: mount_way): bool = let
  val mounted = (made_dirs(op_mkdirs("ro", 2, 493), 1) && spawned_ok(mount_tmpfs(via, "ro")))
  val built = (if mounted then (made_dirs(op_mkdirs("ro/d/x", 6, 493), 2) && op_make_file("ro/d/f", 6)
    && op_make_file("ro/d/x/g", 8)) else false)
  val sealed = (if built then spawned_ok(remount_read_only(via, "ro")) else false)
  val r = op_tree_when(sealed, "ro/d", 4)
  val f_kept = op_exists("ro/d/f", 6)
  val g_kept = op_exists("ro/d/x/g", 8)
  val unmounted = (if mounted then spawned_ok(unmount(via, "ro")) else false)
  val shown = (if tree_is(r, Tree_left_some()) && r.removed = 0 && r.kept = 2 && r.mounts = 0
      && same_failure(r.why, Failed_read_only()) then true
    else (println! ("refused unlinks: got ", shape_name(r.what), " ", r.removed, " ", r.kept, " ", r.mounts,
      " ", failure_name(r.why)); false))
in
  check("mount a tmpfs at ro and fill ro/d", mounted && built)
  && check("remount it read-only", sealed)
  && check("failed unlinks are counted and the first errno kept: TreeLeftSome, 0 removed, 2 kept, EROFS",
       shown)
  && check("what failed is still there", f_kept && g_kept)
  && check("unmount", unmounted)
end

fn probe_mount (run: bool, via: mount_way): spawn_outcome = if run then mount_tmpfs(via, "probe") else Spawn_not_run()
fn probe_unmount (run: bool, via: mount_way): spawn_outcome = if run then unmount(via, "probe") else Spawn_not_run()

(* how a tmpfs can be mounted here (the two outcomes are printed when it cannot) *)
fn find_mount_way (): mount_way = let
  val made = made_dirs(op_mkdirs("probe", 5, 493), 1)
  val direct = probe_mount(made, Mount_directly())
  val direct_ok = spawned_ok(direct)
  val _ = probe_unmount(direct_ok, Mount_directly())
  val sudo = probe_mount(made && not(direct_ok), Mount_through_sudo())
  val sudo_ok = spawned_ok(sudo)
  val _ = probe_unmount(sudo_ok, Mount_through_sudo())
in
  if direct_ok then Mount_directly()
  else if sudo_ok then Mount_through_sudo()
  else let val () = println! ("SKIP mounts: mount ended ", spawn_name(direct), ", sudo -n mount ended ", spawn_name(sudo),
    ": the mount-point, refused-unlink and cross-device classes were not run here") in Mount_unavailable() end
end

fn work_mount (): bool =
  work_mount_top() && (let val via = find_mount_way() in
    case+ via of
    | Mount_unavailable() => true
    | _ => work_mount_below(via) && work_unlink_refused(via) end)

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
