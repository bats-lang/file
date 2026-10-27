#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* Every outcome of the new operations, each constructor named: the
   control of the reject fixtures of keyword remove-rename. *)
#pub fn use_read_link {ls:agz}{ns:pos | ns < 1048576}
  (source: !$A.borrow(byte, ls, ns), source_len: int ns): int

fn read_target {ls:agz}{ns:pos | ns < 1048576}{lo:agz}
  (source: !$A.borrow(byte, ls, ns), source_len: int ns, out: !$A.arr(byte, lo, 16)): int =
  case+ $F.file_read_link(source, source_len, out, 16) of
  | ~$F.LinkTarget(k) => byte2int0($A.get<byte>(out, k))
  | ~$F.LinkTargetTooLong() => 1
  | ~$F.NotASymlink() => 2
  | ~$F.ReadLinkFailed(_) => 3

implement use_read_link (source, source_len) = let
  val out = $A.alloc<byte>(16)
  val h = read_target(source, source_len, out)
  val () = $A.free<byte>(out)
in h end

#pub fn use_all {ls,ld:agz}{ns,nd:pos | ns < 1048576; nd < 1048576}
  (source: !$A.borrow(byte, ls, ns), source_len: int ns,
   destination: !$A.borrow(byte, ld, nd), destination_len: int nd): int

implement use_all (source, source_len, destination, destination_len) = let
  val a: int = (case+ $F.file_rename(source, source_len, destination, destination_len) of
    | ~$F.Renamed() => 0
    | ~$F.RenameFailed(_) => 1)
  val b: int = (case+ $F.file_remove(source, source_len) of
    | ~$F.RemovedFile() => 0
    | ~$F.RemovedEmptyDirectory() => 1
    | ~$F.RemoveFailed(_) => 2)
  val c: int = (case+ $F.file_remove_tree(source, source_len) of
    | ~$F.TreeRemoved(n) => n
    | ~$F.TreeAbsent() => 0
    | ~$F.TreeRefused(why) => (case+ why of $F.RefusedRoot() => 1 | $F.RefusedDotName() => 2)
    | ~$F.TreeFailed(_) => 3
    | ~$F.TreeLeftMounts(n, _) => n
    | ~$F.TreeLeftSome(n, _, _, _) => n)
  val d: int = (case+ $F.file_make_directories(source, source_len, 493) of
    | ~$F.DirectoriesCreated(n) => n
    | ~$F.DirectoryExisted() => 0
    | ~$F.MakeDirectoriesFailed(_) => 1)
  val e: int = (case+ $F.file_symlink(source, source_len, destination, destination_len) of
    | ~$F.SymlinkMade() => 0
    | ~$F.SymlinkFailed(_) => 1)
  val f: int = (case+ $F.file_info(source, source_len) of
    | ~$F.FileInfo(kind, size, mode, owner) =>
        (if $F.mode_is_executable(mode) then size + owner else 0)
    | ~$F.FileInfoFailed(_) => 1)
  val g: int = (case+ $F.directory_emptiness(source, source_len) of
    | ~$F.DirectoryIsEmpty() => 0
    | ~$F.DirectoryHasEntries() => 1
    | ~$F.PathIsNotADirectory() => 2
    | ~$F.EmptinessFailed(_) => 3)
  val h = use_read_link(source, source_len)
in a end
