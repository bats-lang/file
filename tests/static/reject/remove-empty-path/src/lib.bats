#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* An empty path is a type error (n is positive), so remove cannot be asked
   to remove nothing. *)
#pub fn remove_nothing {lb:agz} (path: !$A.borrow(byte, lb, 0)): int

implement remove_nothing (path) =
  case+ $F.file_remove(path, 0) of
  | ~$F.RemovedFile() => 0
  | ~$F.RemovedEmptyDirectory() => 1
  | ~$F.RemoveFailed(_) => 2
