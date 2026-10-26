#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* The target read_link gives has k < m bytes: byte k + 1 may be outside the
   buffer, and only byte k - 1 and below are the target. *)
#pub fn after_target {lb:agz}{n:pos | n < 1048576}{lo:agz}{m:pos}
  (path: !$A.borrow(byte, lb, n), path_len: int n, out: !$A.arr(byte, lo, m), size: int m): int

implement after_target (path, path_len, out, size) =
  case+ $F.file_read_link(path, path_len, out, size) of
  | ~$F.LinkTarget(k) => byte2int0($A.get<byte>(out, k + 1))
  | ~$F.LinkTargetTooLong() => 0
  | ~$F.NotASymlink() => 0
  | ~$F.ReadLinkFailed(_) => 0
