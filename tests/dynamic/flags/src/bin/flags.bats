#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* The flag values are file's own (see O_* in lib.bats), translated to
   the host's open(2) flags; these cases check what each one does.
   Writes n bytes of c to path opened with flags; true when all n
   bytes were written. *)
fn put {lp:agz}{np:pos | np < 1048576}{n:pos | n <= 16}
  (p: !$A.borrow(byte, lp, np), np: int np, flags: int, n: int n): bool = let
  val buf = $A.alloc<byte>(n)
  val @(fb, bb) = $A.freeze<byte>(buf)
  val ok = (case+ $F.file_open(p, np, flags, 420) of
    | ~$R.ok(fd) => let
        val w = (case+ $F.file_write(fd, bb, n) of | ~$R.ok(k) => k = n | ~$R.err(_) => false): bool
        val () = $R.discard<int><int>($F.file_close(fd))
      in w end
    | ~$R.err(_) => false): bool
  val () = $A.drop<byte>(fb, bb)
  val () = $A.free<byte>($A.thaw<byte>(fb))
in ok end

fn size {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): int =
  case+ $F.file_size(p, np) of | ~$R.ok(k) => k | ~$R.err(_) => ~1

fn check (name: string, got: int, want: int): bool = let
  val ok = (got = want)
  val () = (if ok then () else println! ("FAIL ", name, ": got ", got, ", want ", want))
in ok end

implement main0 () = let
  var c = @[char][20]('/', 't', 'm', 'p', '/', 'b', 'a', 't', 's', '_', 'f', 'l', 'a', 'g', 's', '.', 'b', 'i', 'n', '\000')
  val @(fp, bp) = $A.freeze<byte>($S.from_char_array(c, 20))
  (* WRONLY | CREAT | TRUNC *)
  val w1 = put(bp, 20, 1 + 64 + 512, 5)
  val r1 = check("create", size(bp, 20), 5)
  val w2 = put(bp, 20, 1 + 64 + 512, 2)
  val r2 = check("truncate", size(bp, 20), 2)
  (* WRONLY | APPEND *)
  val w3 = put(bp, 20, 1 + 1024, 3)
  val r3 = check("append", size(bp, 20), 5)
  (* WRONLY without TRUNC overwrites in place *)
  val w4 = put(bp, 20, 1, 1)
  val r4 = check("no truncate", size(bp, 20), 5)
  (* RDONLY: the write fails *)
  val w5 = put(bp, 20, 0, 1)
  val r5 = check("read-only write", (if w5 then 1 else 0), 0)
  val () = $A.drop<byte>(fp, bp)
  val () = $A.free<byte>($A.thaw<byte>(fp))
  val wrote = check("writes", (if w1 && w2 && w3 && w4 then 1 else 0), 1)
in
  if wrote && r1 && r2 && r3 && r4 && r5 then println! ("flags: all cases pass")
  else exit_void(1)
end
