#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* A match on how remove_tree ended that names every constructor but
   TreeLeftSome: what could not be removed would go unseen. *)
#pub fn removed_count {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): int

implement removed_count (path, path_len) =
  case+ $F.file_remove_tree(path, path_len) of
  | ~$F.TreeRemoved(c) => c
  | ~$F.TreeAbsent() => 0
  | ~$F.TreeRefused(_) => 0
  | ~$F.TreeFailed(_) => 0
  | ~$F.TreeLeftMounts(c, _) => c
