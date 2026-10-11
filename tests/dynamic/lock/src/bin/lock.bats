#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* fd_lock is flock(2): a lock belongs to an open file, so two opens of
   one file in one process conflict as two processes would. Each case
   is checked on two opens of /tmp/bats_lock.bin. *)

fn opened {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): $R.result($F.fd, $F.io_error) =
  $F.file_open(p, np, $F.ReadWrite(), $F.CreateOrOpen(), 420)

(* 0 when the lock was taken, 1 when it would block, 2 on another
   failure *)
fn take (f: !$F.fd, kind: $F.lock_kind): int =
  case+ $F.fd_lock(f, kind, $F.LockFailsAtOnce()) of
  | ~$R.ok(_) => 0
  | ~$R.err(e) => (case+ e of $F.WouldBlock() => 1 | _ => 2)

fn check (name: string, got: int, want: int): bool = let
  val ok = (got = want)
  val () = (if ok then () else println! ("FAIL ", name, ": got ", got, ", want ", want))
in ok end

fn close (f: $F.fd): void = $R.discard<int><$F.io_error>($F.file_close(f))

implement main0 () = let
  var c = @[char][19]('/', 't', 'm', 'p', '/', 'b', 'a', 't', 's', '_', 'l', 'o', 'c', 'k', '.', 'b', 'i', 'n', '\000')
  val @(fp, bp) = $A.freeze<byte>($S.from_char_array(c, 19))
  val first = opened(bp, 19)
  val second = opened(bp, 19)
  val () = $A.drop<byte>(fp, bp)
  val () = $A.free<byte>($A.thaw<byte>(fp))
in
  case+ (first, second) of
  | (~$R.ok(a), ~$R.ok(b)) => let
      val r1 = check("exclusive", take(a, $F.LockExclusive()), 0)
      val r2 = check("exclusive against exclusive", take(b, $F.LockExclusive()), 1)
      val r3 = check("shared against exclusive", take(b, $F.LockShared()), 1)
      (* unlocked, the other open takes it *)
      val u = (case+ $F.fd_unlock(a) of | ~$R.ok(_) => 0 | ~$R.err(_) => 2): int
      val r4 = check("unlock", u, 0)
      val r5 = check("exclusive after unlock", take(b, $F.LockExclusive()), 0)
      (* converted to shared, it shares *)
      val r6 = check("convert to shared", take(b, $F.LockShared()), 0)
      val r7 = check("shared with shared", take(a, $F.LockShared()), 0)
      val r8 = check("exclusive against shared", take(a, $F.LockExclusive()), 1)
      (* closing an open releases its lock *)
      val () = close(b)
      val r9 = check("exclusive after close", take(a, $F.LockExclusive()), 0)
      val () = close(a)
    in
      if r1 && r2 && r3 && r4 && r5 && r6 && r7 && r8 && r9 then println! ("lock: all cases pass")
      else exit_void(1)
    end
  | (r1, r2) => let
      val () = (case+ r1 of | ~$R.ok(f) => close(f) | ~$R.err(_) => ())
      val () = (case+ r2 of | ~$R.ok(f) => close(f) | ~$R.err(_) => ())
      val () = println! ("FAIL lock: /tmp/bats_lock.bin could not be opened")
    in exit_void(1) end
end
