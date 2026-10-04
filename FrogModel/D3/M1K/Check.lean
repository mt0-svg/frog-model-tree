module

@[expose] public section

/-!
# The kernel checker of the stored M1 run

Proposition 13.3 and Proposition 15.1 (1) of the paper. The stored run is the release asset
frog-model-tree-d3-m1run.txt.xz, which code/m1run writes as out/m1run_V48_P96_h100.txt (its
format: code/m1run/src/bin/m1run.rs); the generator code/m1gen writes it as the Lean data modules
`FrogModel.D3.M1Data`.

A value `n` stands for `n / D`, `D = 2^62`. A row holds the `NL = 4 (V + 1) = 196` lanes `(a, g)`
(`a ≤ V = 48` an answer or up count, `g ≤ 3` a count of unmarked children), lane `4 a + g` in the
bits `[S l, S (l + 1))` of one natural number, `S = 144`. A table holds its rows `p = 0..P + V`
(`P = 96`) at the stride `RB = NL S` bits, the rows past `P` copies of the row `P` (pools clipped at
`P`). From a stored height the checker recomputes the downward evaluation by code/m1run of the R
closure (the 35 multisets of child types, sorted `t0 ≥ t1 ≥ t2`, type `4` the unmarked child `N`,
type `t < 4` the marked child `U_t`) and of the H kernels `Y_f(1)`, every new lane
`⌊⌊num / D⌋ c / D⌋`, the event terms as products of a packed column with a packed table (Kronecker
substitution in two dimensions). Every loop is a `Nat.rec`, every selection a `cond`, the
arithmetic `Nat.*` on naturals.
-/

namespace FrogModel.D3.M1K

/-- `f (n - 1) (… (f 0 init))`. -/
def natFold {α : Type} (n : Nat) (init : α) (f : Nat → α → α) : α :=
  Nat.rec (motive := fun _ => α) init (fun i acc => f i acc) n

/-- `f` along the list, from the head. -/
def listFold {α β : Type} : List β → α → (α → β → α) → α
  | [], a, _ => a
  | b :: l, a, f => listFold l (f a b) f

def minN (a b : Nat) : Nat := Nat.sub a (Nat.sub a b)
def maxN (a b : Nat) : Nat := Nat.add a (Nat.sub b a)

/-! ## The configuration -/

def V : Nat := 48
def P : Nat := 96
def W : Nat := 62
def S : Nat := 144
def NL : Nat := 196
def RB : Nat := 28224
def D : Nat := Nat.pow 2 62

/-! ## Packing -/

/-- `∑_(j < 2^d) f (lo + j) 2^(B j)`, by halving. -/
def packTree (B : Nat) (f : Nat → Nat) (d : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) f
    (fun i r lo => Nat.add (r lo)
      (Nat.shiftLeft (r (Nat.add lo (Nat.pow 2 i))) (Nat.mul B (Nat.pow 2 i)))) d

/-- The `2^d` blocks of `B` bits of `x`, lowest first, followed by `acc`. -/
def blocks (B : Nat) (d : Nat) : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun x acc => Nat.mod x (Nat.pow 2 B) :: acc)
    (fun i r x acc => r (Nat.mod x (Nat.pow 2 (Nat.mul B (Nat.pow 2 i))))
      (r (Nat.shiftRight x (Nat.mul B (Nat.pow 2 i))) acc)) d

/-- Lane `l` of a row. -/
def lane (x l : Nat) : Nat := Nat.mod (Nat.shiftRight x (Nat.mul S l)) (Nat.pow 2 S)

/-- The row with the lanes `f l`, `l < NL`. -/
def mkRow (f : Nat → Nat) : Nat := packTree S (fun l => cond (Nat.blt l NL) (f l) 0) 8 0

/-- The low `W` bits of every lane. -/
def lowMask : Nat := mkRow (fun _ => Nat.sub (Nat.pow 2 W) 1)

/-- The bits `63..S-1` of every lane. -/
def hiMask : Nat := mkRow (fun _ => Nat.sub (Nat.pow 2 S) (Nat.pow 2 63))

/-- `⌊x_l / 2^W⌋` in every lane. -/
def lfloor (x : Nat) : Nat := Nat.shiftRight (Nat.sub x (Nat.land x lowMask)) W

/-- `⌊⌊x_l / D⌋ k / D⌋` in every lane. -/
def rowRound (x k : Nat) : Nat := lfloor (Nat.mul k (lfloor x))

/-- `up`: lane `(a, g)` from lane `(a - 1, g)`, the lanes `a = V` kept (answers clipped at `V`). -/
def upRow (r : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.shiftLeft r (Nat.mul 4 S)) (Nat.pow 2 RB))
    (Nat.shiftLeft (Nat.shiftRight r (Nat.mul (Nat.mul 4 V) S)) (Nat.mul (Nat.mul 4 V) S))

/-- One step of a recurrence: `round(cUp up(prev) + cSame prev + e, k)`. -/
def rowStep (prev e cUp cSame k : Nat) : Nat :=
  rowRound (Nat.add (Nat.add (Nat.mul cUp (upRow prev)) (Nat.mul cSame prev)) e) k

/-- Every lane below `2^63`. -/
def rowOK (r : Nat) : Bool := Nat.beq (Nat.land r hiMask) 0

/-- Entry `p` of a list of rows (`0` past the end). -/
def getR (l : List Nat) (p : Nat) : Nat := (natFold p l (fun _ acc => acc.tail)).headD 0

/-- Entry `i` of a list of lists (`[]` past the end). -/
def getL (l : List (List Nat)) (i : Nat) : List Nat := (natFold i l (fun _ acc => acc.tail)).headD []

/-- Row `p` of a table. -/
def blockAt (T p : Nat) : Nat := Nat.mod (Nat.shiftRight T (Nat.mul RB p)) (Nat.pow 2 RB)

/-- The table of the rows `0..P` of a list, extended by `V` copies of the row `P`. -/
def packTable (rows : List Nat) : Nat :=
  packTree RB (fun p => cond (Nat.ble p (Nat.add P V)) (getR rows (minN p P)) 0) 8 0

/-- The column of the lanes `(V - a, g)` of `law`, `a = 0..V`, at the stride `RB`. -/
def packCol (law g : Nat) : Nat :=
  packTree RB (fun a => cond (Nat.ble a V) (lane law (Nat.add (Nat.mul 4 (Nat.sub V a)) g)) 0) 6 0

/-- The event rows `p = 1..128` of a sum of channel products: its blocks `V .. V + 127`. -/
def eventRows (X : Nat) : List Nat := blocks RB 7 (Nat.shiftRight X (Nat.mul RB V)) []

/-- The rows `0..P` of a recurrence (row `p` at index `p`) from its row `0` and its event rows, and
whether every row has its lanes below `2^63`. -/
def solve (row0 : Nat) (es : List Nat) (cUp cSame k : Nat) : List Nat × Bool :=
  let r := natFold P (row0, es, [row0], rowOK row0) (fun _ st =>
    let nr := rowStep st.1 (st.2.1.headD 0) cUp cSame k
    (nr, st.2.1.tail, nr :: st.2.2.1, and st.2.2.2 (rowOK nr)))
  (r.2.2.1.reverse, r.2.2.2)

/-! ## A height: the stored laws -/

/-- The stored laws of a height: `rho*_h` and `K*_h(t -> .)`, `t = 0..3`. -/
structure St where
  rho : Nat
  k0 : Nat
  k1 : Nat
  k2 : Nat
  k3 : Nat

/-- The answer law of a child of type `t` (`4`: `N`, else `U_t`). -/
def lawOf (s : St) (t : Nat) : Nat :=
  cond (Nat.beq t 4) s.rho (cond (Nat.beq t 3) s.k3 (cond (Nat.beq t 2) s.k2 (cond (Nat.beq t 1) s.k1 s.k0)))

/-- The channels of a child of type `t`: the fresh counts `g < gmax t`. -/
def gmax (t : Nat) : Nat := cond (Nat.beq t 4) 4 t

/-- The code `25 t0 + 5 t1 + t2` of the multiset `{a, b, c}`, `t0 ≥ t1 ≥ t2`. -/
def mcode (a b c : Nat) : Nat :=
  let x := maxN a b
  let y := minN a b
  cond (Nat.ble x c) (Nat.add (Nat.add (Nat.mul 25 c) (Nat.mul 5 x)) y)
    (cond (Nat.ble y c) (Nat.add (Nat.add (Nat.mul 25 x) (Nat.mul 5 c)) y)
      (Nat.add (Nat.add (Nat.mul 25 x) (Nat.mul 5 y)) c))

/-- The first table of code `code` (`0` if there is none). -/
def findTab : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | kv :: rest, code => cond (Nat.beq kv.1 code) kv.2 (findTab rest code)

/-- The event products of a child of type `t` whose two siblings have the types `a`, `b`. -/
def chan (s : St) (tabs : List (Nat × Nat)) (t a b : Nat) : Nat :=
  natFold (gmax t) 0 (fun g acc =>
    Nat.add acc (Nat.mul (packCol (lawOf s t) g) (findTab tabs (mcode a b g))))

/-- The sum of the event products of the three children. -/
def eventX (s : St) (tabs : List (Nat × Nat)) (t0 t1 t2 : Nat) : Nat :=
  Nat.add (Nat.add (chan s tabs t0 t1 t2) (chan s tabs t1 t0 t2)) (chan s tabs t2 t0 t1)

/-- `K(t -> (1, t))` of a marked child (the loop weight), `0` for `N`. -/
def loopW (s : St) (t : Nat) : Nat := cond (Nat.blt t 4) (lane (lawOf s t) (Nat.add 4 t)) 0

/-- `K(t -> (0, t))` of a marked child (the loss weight), `0` for `N`. -/
def lossW (s : St) (t : Nat) : Nat := cond (Nat.blt t 4) (lane (lawOf s t) t) 0

def isN (t : Nat) : Nat := cond (Nat.beq t 4) 1 0

/-- The table `W_sigma(0..P)` of the multiset `(t0, t1, t2)` and whether its lanes are below `2^63`:
`W(0)` the point mass at `(0, #N)`, `W(p) = round(D up(W(p - 1)) + lo W(p - 1) + E(p), ⌊D^2/(4 D - lp)⌋)`. -/
def sigmaTable (s : St) (tabs : List (Nat × Nat)) (t0 t1 t2 : Nat) : Nat × Bool :=
  let lp := Nat.add (Nat.add (loopW s t0) (loopW s t1)) (loopW s t2)
  let lo := Nat.add (Nat.add (lossW s t0) (lossW s t1)) (lossW s t2)
  let nN := Nat.add (Nat.add (isN t0) (isN t1)) (isN t2)
  let k := Nat.div (Nat.mul D D) (Nat.sub (Nat.mul 4 D) lp)
  let r := solve (Nat.shiftLeft D (Nat.mul S nN)) (eventRows (eventX s tabs t0 t1 t2)) D lo k
  (packTable r.1, r.2)

/-- The 35 multiset codes in an order where every event lowers the total type. -/
def sigmaOrder : List Nat :=
  [0, 25, 30, 50, 31, 55, 75, 56, 60, 80, 100, 61, 81, 85, 105, 62, 86, 90, 106, 110, 87, 91, 111,
   115, 92, 112, 116, 120, 93, 117, 121, 118, 122, 123, 124]

/-- All tables of the R closure in the order `sigmaOrder` (code, table), and whether every lane of
every table is below `2^63`. -/
def closure (s : St) : List (Nat × Nat) × Bool :=
  listFold sigmaOrder ([], true) (fun acc code =>
    let r := sigmaTable s acc.1 (Nat.div code 25) (Nat.mod (Nat.div code 5) 5) (Nat.mod code 5)
    (List.append acc.1 [(code, r.1)], and acc.2 r.2))

/-- The first marginal `rhobar(V - a)` of `rho`, `a = 0..V`, at the stride `RB`. -/
def rbCol (s : St) : Nat :=
  packTree RB (fun a => cond (Nat.ble a V)
    (natFold 4 0 (fun g acc => Nat.add acc (lane s.rho (Nat.add (Nat.mul 4 (Nat.sub V a)) g)))) 0) 6 0

/-- The H recursion `Y_f(0..P)`, `f = 0..3` (`kernel_raw` of code/m1run): `Y_f(0)` the point mass at
`(0, f)`, `Y_f(s) = round(3 D up + 2 (3 - f) D same + 3 f acc, ⌊D/(9 + f)⌋)`, `acc` the sum over `b`
of `rhobar(b) Y_(f-1)(min(s - 1 + b, P))`. -/
def yNext (s : St) (f : Nat) (prev : List Nat) : List Nat × Bool :=
  solve (Nat.shiftLeft D (Nat.mul S f))
    (eventRows (Nat.mul (Nat.mul 3 f) (Nat.mul (rbCol s) (packTable prev))))
    (Nat.mul 3 D) (Nat.mul (Nat.mul 2 (Nat.sub 3 f)) D) (Nat.div D (Nat.add 9 f))

def yTabs (s : St) : List (List Nat) × Bool :=
  let y0 := solve D (eventRows 0) (Nat.mul 3 D) (Nat.mul 6 D) (Nat.div D 9)
  let y1 := yNext s 1 y0.1
  let y2 := yNext s 2 y1.1
  let y3 := yNext s 3 y2.1
  ([y0.1, y1.1, y2.1, y3.1], and (and y0.2 y1.2) (and y2.2 y3.2))

/-! ## The checks -/

/-- Equal off the bottom lane `(0, 0)`. -/
def offEq (a b : Nat) : Bool := Nat.beq (Nat.shiftRight a S) (Nat.shiftRight b S)

/-- The sum of the lanes of a row. -/
def sumLanes (r : Nat) : Nat := natFold NL 0 (fun l acc => Nat.add acc (lane r l))

/-- The lanes `(a, g)` with `g > t` are `0`. -/
def zeroAbove (r t : Nat) : Bool :=
  natFold NL true (fun l acc => and acc (or (Nat.ble (Nat.mod l 4) t) (Nat.beq (lane r l) 0)))

/-- A row of `NL` lanes summing to `D`. -/
def validRow (r : Nat) : Bool := and (Nat.blt r (Nat.pow 2 RB)) (Nat.beq (sumLanes r) D)

/-- The stored laws of a height are probability vectors, the kernels without mass at `f' > t`. -/
def validSt (s : St) : Bool :=
  and (and (validRow s.rho) (and (validRow s.k0) (zeroAbove s.k0 0)))
    (and (and (validRow s.k1) (zeroAbove s.k1 1))
      (and (and (validRow s.k2) (zeroAbove s.k2 2)) (and (validRow s.k3) (zeroAbove s.k3 3))))

/-- Height `h` from height `h - 1`: every stored lane off the bottom equals the downward evaluation,
`rho*_h` against `W_NNN(2)` and `K*_h(t -> .)` against `Y_t(1)`, and no lane overflows. -/
def checkStep (prev cur : St) : Bool :=
  let cl := closure prev
  let nnn := findTab cl.1 124
  let y := yTabs prev
  let ys := y.1
  and (and cl.2 y.2)
    (and (offEq cur.rho (blockAt nnn 2))
      (and (and (offEq cur.k0 (getR (getL ys 0) 1)) (offEq cur.k1 (getR (getL ys 1) 1)))
        (and (offEq cur.k2 (getR (getL ys 2) 1)) (offEq cur.k3 (getR (getL ys 3) 1)))))

/-- The top: the stored `Wtil_q` (`q = 2..33`, entry `q - 2` of `wt`) equal `W_NNN(q)` of the
closure on the stored height `99`. -/
def checkTop (s : St) (wt : List Nat) : Bool :=
  let cl := closure s
  let nnn := findTab cl.1 124
  and cl.2 (natFold 32 true (fun i acc => and acc (Nat.beq (getR wt i) (blockAt nnn (Nat.add i 2)))))

/-- Height `0` against `Rhat_0` and `Khat_0` at `L = 60`: off the bottom, `rho*_0` has mass only at
`(1, 0)` and `(2, 0)` (lanes `4`, `8`), at most `c1` and `c2`, and `K*_0(t -> .)` only at `(1, t)` and
`(0, t)` (lanes `4 + t`, `t`), at most `c3` and `c4` (`2^62` times `4/9`, `1/9`, `1/3`, `2/3`, rounded down). -/
def check0 (s : St) : Bool :=
  and (natFold NL true (fun l acc => and acc
      (or (or (Nat.beq l 0) (or (Nat.beq l 4) (Nat.beq l 8))) (Nat.beq (lane s.rho l) 0))))
    (and (and (Nat.ble (lane s.rho 4) 2049638230412172401) (Nat.ble (lane s.rho 8) 512409557603043100))
      (natFold 4 true (fun t acc => and acc
        (and (natFold NL true (fun l acc2 => and acc2
            (or (or (Nat.beq l 0) (or (Nat.beq l t) (Nat.beq l (Nat.add 4 t)))) (Nat.beq (lane (lawOf s t) l) 0))))
          (and (Nat.ble (lane (lawOf s t) (Nat.add 4 t)) 1537228672809129301)
            (or (Nat.beq t 0) (Nat.ble (lane (lawOf s t) t) 3074457345618258602)))))))

/-- Slot `i` of 64 bits. -/
def slot64 (x i : Nat) : Nat := Nat.mod (Nat.shiftRight x (Nat.mul 64 i)) (Nat.pow 2 64)

/-- The packed masses `mpk`: slot `49 (k - 1) + x` holds the sum over `g` of the lanes `(x, g)` of
`Wtil_(k+1)` (entry `k - 1` of `wt`), `k = 1..32`, `x = 0..48`; the mass lines (`mass`, row `k - 1`,
entry `x - 1`, `x = 1..48`) are the same numbers. -/
def checkMass (wt : List Nat) (mpk : Nat) (mass : List (List Nat)) : Bool :=
  natFold 32 true (fun k acc => and acc (natFold 49 true (fun x acc2 =>
    let v := slot64 mpk (Nat.add (Nat.mul 49 k) x)
    and acc2 (and (Nat.beq v (natFold 4 0 (fun g s => Nat.add s (lane (getR wt k) (Nat.add (Nat.mul 4 x) g)))))
      (or (Nat.beq x 0) (Nat.beq (getR (getL mass k) (Nat.sub x 1)) v))))))

end FrogModel.D3.M1K
