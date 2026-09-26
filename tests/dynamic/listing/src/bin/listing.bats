#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* dir_read returns every entry of a directory, however many: 300 files
   (more than the 200 a fuel-bounded walk used to stop at) plus . and ..
   (the harness runs this in a scratch directory it owns). *)

(* Creates ls.d/fDDD for i = 0 .. k-1 *)
fun make {k,i:nat | i <= k; k <= 999} .<k - i>.
  (i: int i, k: int k): void =
  if i >= k then ()
  else let
    val p = $A.alloc<byte>(10)
    val () = $A.set<byte>(p, 0, $A.int2byte(108))
    val () = $A.set<byte>(p, 1, $A.int2byte(115))
    val () = $A.set<byte>(p, 2, $A.int2byte(46))
    val () = $A.set<byte>(p, 3, $A.int2byte(100))
    val () = $A.set<byte>(p, 4, $A.int2byte(47))
    val () = $A.set<byte>(p, 5, $A.int2byte(102))
    val () = $A.set<byte>(p, 6, $A.int2byte(48 + ndiv(i, 100)))
    val () = $A.set<byte>(p, 7, $A.int2byte(48 + nmod(ndiv(i, 10), 10)))
    val () = $A.set<byte>(p, 8, $A.int2byte(48 + nmod(i, 10)))
    val @(fz, bp) = $A.freeze<byte>(p)
    val () = (case+ $F.file_open(bp, 10, 65, 420) (* O_WRONLY + O_CREAT *) of
      | ~$R.ok(fd) => $R.discard<int><int>($F.file_close(fd))
      | ~$R.err(_) => println! ("FAIL: create ", i))
    val () = $A.drop<byte>(fz, bp)
    val () = $A.free<byte>($A.thaw<byte>(fz))
  in make(i + 1, k) end

(* Number of names of length 4 starting with f, and of other names *)
fun tally {n,i:nat | i <= n}{l:agz} .<n - i>.
  (es: !$F.entries(n), i: int i, n: int n, buf: !$A.arr(byte, l, 64), fs: int, others: int): @(int, int) =
  if i >= n then @(fs, others)
  else let
    val k = $F.entries_name(es, i, buf, 64)
    val f = (if k = 4 then byte2int0($A.get<byte>(buf, 0)) = 102 else false): bool
  in
    if f then tally(es, i + 1, n, buf, fs + 1, others)
    else tally(es, i + 1, n, buf, fs, others + 1)
  end

implement main0 () = let
  var d = @[char][5]('l', 's', '.', 'd', '\000')
  val @(fd, bd) = $A.freeze<byte>($S.from_char_array(d, 5))
  val () = $R.discard<int><int>($F.file_mkdir(bd, 5, 493))
  val () = make(0, 300)
  val () = (case+ $F.dir_read(bd, 5) of
    | ~$R.ok(es) => let
        val n = $F.entries_count(es)
        val buf = $A.alloc<byte>(64)
        val @(fs, others) = tally(es, 0, n, buf, 0, 0)
        val () = $A.free<byte>(buf)
        val () = $F.entries_free(es)
      in println! ("entries ", n, ", f names ", fs, ", others ", others) end
    | ~$R.err(e) => println! ("FAIL: dir_read ", e))
  var m = @[char][5]('n', 'o', '.', 'd', '\000')
  val @(fm, bm) = $A.freeze<byte>($S.from_char_array(m, 5))
  val () = (case+ $F.dir_read(bm, 5) of
    | ~$R.ok(es) => let val () = $F.entries_free(es) in println! ("FAIL: read no.d") end
    | ~$R.err(e) => println! ("missing directory: err ", e))
  val () = $A.drop<byte>(fm, bm)
  val () = $A.free<byte>($A.thaw<byte>(fm))
  val () = $A.drop<byte>(fd, bd)
in $A.free<byte>($A.thaw<byte>(fd)) end
