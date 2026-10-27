#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* A mode is the permission bits, 0 to 07777 (4095): 4096 is not one. *)
#pub fn make_with_big_mode {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): int

implement make_with_big_mode (path, path_len) =
  case+ $F.file_make_directories(path, path_len, 4096) of
  | ~$F.DirectoriesCreated(_) => 0
  | ~$F.DirectoryExisted() => 1
  | ~$F.MakeDirectoriesFailed(_) => 2
