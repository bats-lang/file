#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* dir_read returns every entry of a directory, however many: 300 files
   (more than the 200 a fuel-bounded walk used to stop at) plus . and ..,
   sorted by name (the harness runs this in a scratch directory it
   owns). The files are created in reverse, so the order comes from the
   sort. *)

(* Prints entry i's name *)
fn show {n:int}{i:nat | i < n}{l:agz}
  (es: !$F.entries(n), i: int i, buf: !$A.arr(byte, l, 1024)): void = let
  val k = $F.entries_name(es, i, buf, 1024)
  fun put {j,m:nat | j <= m; m <= 1024} .<m - j>. (buf: !$A.arr(byte, l, 1024), j: int j, k: int m): void =
    if j >= k then () else let
      val () = print_char(int2char0(byte2int0($A.get<byte>(buf, j))))
    in put(buf, j + 1, k) end
  val () = put(buf, 0, k)
in print_newline() end

(* Creates ls.d/fDDD for i = k-1 down to 0 *)
fun make {i:nat | i <= 999} .<i>.
  (i: int i): void =
  if i <= 0 then ()
  else let
    val i = i - 1
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
  in make(i) end

(* Prints entries 0, 1, 2 and 301 *)
fn show_ends {n:int}{l:agz}
  (es: !$F.entries(n), n: int n, buf: !$A.arr(byte, l, 1024)): void =
  if n > 301 then let
    val () = show(es, 0, buf)
    val () = show(es, 1, buf)
    val () = show(es, 2, buf)
  in show(es, 301, buf) end
  else println! ("FAIL: only ", n, " entries")

(* Number of names of length 4 starting with f, and of other names *)
fun tally {n,i:nat | i <= n}{l:agz} .<n - i>.
  (es: !$F.entries(n), i: int i, n: int n, buf: !$A.arr(byte, l, 1024), fs: int, others: int): @(int, int) =
  if i >= n then @(fs, others)
  else let
    val k = $F.entries_name(es, i, buf, 1024)
    val f = (if k = 4 then byte2int0($A.get<byte>(buf, 0)) = 102 else false): bool
  in
    if f then tally(es, i + 1, n, buf, fs + 1, others)
    else tally(es, i + 1, n, buf, fs, others + 1)
  end

implement main0 () = let
  var d = @[char][5]('l', 's', '.', 'd', '\000')
  val @(fd, bd) = $A.freeze<byte>($S.from_char_array(d, 5))
  val () = $R.discard<int><int>($F.file_mkdir(bd, 5, 493))
  val () = make(300)
  val () = (case+ $F.dir_read(bd, 5) of
    | ~$R.ok(es) => let
        val n = $F.entries_count(es)
        val buf = $A.alloc<byte>(1024)
        val @(fs, others) = tally(es, 0, n, buf, 0, 0)
        val () = show_ends(es, n, buf)
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
