#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* Open flags are an access and an opening, not O_* numbers *)
fn open_for_writing {lb:agz}{n:pos | n < 1048576} (path: !$A.borrow(byte, lb, n), n: int n): void =
  case+ $F.file_open(path, n, 1 + 64 + 512, 420) of
  | ~$R.ok(fd) => $R.discard<int><$F.io_error>($F.file_close(fd))
  | ~$R.err(_) => ()
