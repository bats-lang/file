#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* Why an operation failed is an io_error, not an errno *)
fn errno_of {lb:agz}{n:pos | n < 1048576} (path: !$A.borrow(byte, lb, n), n: int n): int =
  case+ $F.file_size(path, n) of
  | ~$R.ok(_) => 0
  | ~$R.err(e) => e
