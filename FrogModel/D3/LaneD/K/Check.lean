module

public import FrogModel.D3.LaneD.K.SLaws
public import FrogModel.D3.LaneD.K.Conv

@[expose] public section

/-!
# The check of one plain step (or interval check) of the map `Phi^S`

`check L` tests, component by component in the order of Definition 12.3 of the paper, that the
stored output state is at least the named term evaluated on the input state, on the computed deficit
bounds `U(j)` (rounded up at `2^-128`) for the terms `P` and `L`, and on the stored output for `J`
and `G`. Terms: deficits `T`, `P`, `L<J>.<K>`, `S2`; cdf entries `1`, `C`, `L`, `A<n0>`, `S3`, `J`,
`G`. Every comparison is exact in integers; the only rounded quantities are the laws of the lower
closures of Lemma 12.1 (upper bounds at `2^-W`) and `U(j)`.

Values of the states are `n / 2^52`, rows packed in 64-bit slots.
-/

namespace FrogModel.D3.LaneD.K

structure Line where
  E : Nat
  GM : Nat
  VM : Nat
  JM : Nat
  a : Nat
  b : Nat
  /-- The deficits `d0..d1` and the cdf rows `f0..f1` checked by this part of the line. -/
  d0 : Nat
  d1 : Nat
  f0 : Nat
  f1 : Nat
  /-- The terms this part checks: bit 0 the deficits other than `L`, bit 1 the deficits `L` of the
  families `famsB`, bit 2 the cdf entries other than `A` (with the shape of the output state), bit 3
  the cdf entries `A` of the families `famsA`. -/
  mask : Nat
  /-- Rows `k = 0..E` of the input cdf bounds, slots `g = 0..GM`. -/
  inF : List Nat
  /-- The input deficits `k = 0..E`. -/
  inD : Nat
  outF : List Nat
  outD : Nat
  /-- Deficit names, 64-bit slot `j`: `code + 256 J + 2^24 K`; codes `1` T, `2` P, `3` L, `4` S2. -/
  dn : Nat
  /-- Cdf names, rows `j = 0..E`, 32-bit slot `v`: `code + 256 param`; codes `0` one, `1` C, `2` L,
  `4` A (param `n0`), `5` S3, `6` J, `7` G. -/
  fn : List Nat
  /-- The (A) families `(sh, used)`: a cut `sh = n0 - q - 1` and the bitmask of the `v` that use it. -/
  famsA : List (Nat × Nat)
  /-- The (B) families `J + 2^16 sh`, `sh = K - q - 1`. -/
  famsB : List Nat
  /-- The distinct cuts `sh` of the (B) families. -/
  shsB : List Nat
  /-- The deficit bounds `U(j)` at `2^-128`, 128-bit slot `j` (a hint: each part checks the bound of
  its deficits against it, and reads it for the terms `P` and `L`). -/
  uD : Nat
  /-- `rho_j` with `3 rho_j^2 ≥ (a + 2 + j) 2^256`, 256-bit slot `j`. -/
  sq : Nat

def one52 : Nat := Nat.shiftLeft 1 52

def gridOffsets : List Nat := [8, 16, 24, 32, 48, 64, 96, 128, 192, 256]

/-- `n ∈ grid GM q`. -/
def inGrid (GM q n : Nat) : Bool :=
  Nat.beq n (Nat.add (Nat.add q GM) 1) ||
    (Nat.ble n (Nat.add (Nat.add q GM) 1) && Nat.blt q n &&
      gridOffsets.any (fun o => Nat.beq (Nat.sub n q) o))

/-- `r'(k', j) = max((a + 1 + k')(b + 2 + j), (b + 1 + k')(a + 2 + j))`, over `(a + 2 + j)(b + 2 + j)`. -/
def ratioN (a b k j : Nat) : Nat :=
  maxN (Nat.mul (Nat.add (Nat.add a 1) k) (Nat.add (Nat.add b 2) j))
    (Nat.mul (Nat.add (Nat.add b 1) k) (Nat.add (Nat.add a 2) j))
def ratioD (a b j : Nat) : Nat := Nat.mul (Nat.add (Nat.add a 2) j) (Nat.add (Nat.add b 2) j)

/-- `sum over u ≤ v of C(n, u)`. -/
def binSum (n v : Nat) : Nat :=
  (natFold (Nat.add v 1) (0, 1) (fun u (st : Nat × Nat) =>
    (Nat.add st.1 st.2, Nat.div (Nat.mul st.2 (Nat.sub n u)) (Nat.add u 1)))).1

/-- `sum over i < J of C(K, i) 3^(K - i)` (`binLt K (1/4) J` times `4^K`). -/
def binLt4 (K J : Nat) : Nat :=
  (natFold J (0, 1) (fun i (st : Nat × Nat) =>
    (Nat.add st.1 (Nat.mul st.2 (Nat.pow 3 (Nat.sub K i))),
      Nat.div (Nat.mul st.2 (Nat.sub K i)) (Nat.add i 1)))).1

/-- `sum over i ≤ v of C(n, i) b^(n - i)`. -/
def binCdfN (n v b : Nat) : Nat :=
  (natFold (Nat.add v 1) (0, 1) (fun i (st : Nat × Nat) =>
    (Nat.add st.1 (Nat.mul st.2 (Nat.pow b (Nat.sub n i))),
      Nat.div (Nat.mul st.2 (Nat.sub n i)) (Nat.add i 1)))).1

/-- The index of `x` in `l` (`l.length` if absent). -/
def idxN (l : List Nat) (x : Nat) : Nat :=
  (natFold l.length (0, l, false) (fun _ (st : Nat × List Nat × Bool) =>
    cond st.2.2 st (cond (Nat.beq (hd st.2.1) x) (st.1, st.2.1, true) (Nat.add st.1 1, tl st.2.1, false)))).1

/-- `sum over e0 < J of` entry `k` of row `e0`. -/
def sumRows (g : List (List Nat)) (J k : Nat) : Nat :=
  (natFold J (0, g) (fun _ (st : Nat × List (List Nat)) =>
    (Nat.add st.1 (getN (hdL st.2) k), tlL st.2))).1

/-- The (A) vector of the cut `sh` and of `v`, and `0` if it was computed, `1` if not. -/
def findA (l : List (Nat × Nat × List Nat)) (sh v : Nat) : Nat × Nat :=
  match l.find? (fun t => Nat.beq t.1 sh) with
  | some t => (getN t.2.2 v, cond (Nat.beq (Nat.land (Nat.shiftRight t.2.1 v) 1) 1) 0 1)
  | none => (0, 1)

/-- The (B) vector of the family `code`, and its failure count. -/
def findB (l : List (Nat × Nat)) (code : Nat) : Nat × Nat :=
  match l.find? (fun t => Nat.beq t.1 code) with
  | some t => (t.2, 0)
  | none => (0, 1)

/-- Slot width of the convolutions. -/
def convSW (E : Nat) : Nat := cond (Nat.ble E 32) 1024 2048

def WL : Nat := 64

/-- The deficit bound `U(j)` at `2^-128` of the named term, and its failure count. -/
def deficitTerm (L : Line) (c : ConvCfg) (_NN DenB : Nat) (vB : List (Nat × Nat)) (s2row : List Nat)
    (j : Nat) : Nat × Nat :=
  let nm := slot 64 L.dn j
  let code := Nat.land nm 255
  let J := Nat.land (Nat.shiftRight nm 8) 65535
  let K := Nat.shiftRight nm 24
  let q := Nat.add j 1
  let dd := ratioD L.a L.b j
  cond (Nat.beq code 1) (cdiv (Nat.shiftLeft (ratioN L.a L.b 0 j) 128) dd, 0) <|
  cond (Nat.beq code 2) (slot 128 L.uD (Nat.sub j 1), bad 2 j) <|
  cond (Nat.beq code 3)
    (let ok := Nat.ble 1 J && Nat.ble J L.JM && inGrid L.GM q K
     let fb := findB vB (Nat.add J (Nat.shiftLeft (Nat.sub (Nat.sub K q) 1) 16))
     let main := slot c.SW fb.1 (Nat.sub c.Q0 q)
     let e := Nat.add (Nat.sub (Nat.add L.E J) 1) 52
     let nF := slot 64 (getN L.inF L.E) (Nat.sub (Nat.sub K q) 1)
     let db := Nat.shiftLeft DenB (Nat.add e (Nat.mul 2 K))
     let nb := Nat.add (Nat.add (Nat.shiftLeft main (Nat.add e (Nat.mul 2 K)))
         (Nat.shiftLeft (Nat.mul (Nat.mul 2 (binSum (Nat.sub (Nat.add L.E J) 1) (Nat.sub J 1))) (Nat.mul nF DenB)) (Nat.mul 2 K)))
       (Nat.shiftLeft (Nat.mul (binLt4 K J) DenB) e)
     let nJ := slot 64 L.inD J
     (cdiv (Nat.shiftLeft (Nat.mul (Nat.add (Nat.mul nJ db) (Nat.mul nb (Nat.sub one52 nJ))) (ratioN L.a L.b J j)) 76)
        (Nat.mul db dd), Nat.add fb.2 (cond ok 0 1))) <|
  cond (Nat.beq code 4)
    (let sm := (natFold (Nat.add L.E 1) (0, 0, s2row) (fun k (st : Nat × Nat × List Nat) =>
        let x := Nat.mul (cond (Nat.beq k 0) one52 (slot 64 L.inD k)) (ratioN L.a L.b k j)
        let dt := cond (Nat.beq k 0) x (minN st.2.1 x)
        (Nat.add st.1 (Nat.mul (hd st.2.2) dt), dt, tl st.2.2))).1
     (cdiv (Nat.shiftLeft sm 128) (Nat.shiftLeft dd (Nat.add WL 52)), 0))
  (0, 1)

/-- The failure count of the cdf entry `(j, v)` with stored value `n'`. -/
def cdfTerm (L : Line) (c : ConvCfg) (DenA : Nat) (vA : List (Nat × Nat × List Nat)) (U j v nF' nPrevRow nNext s3cum : Nat) :
    Nat :=
  let nm := slot 32 (getN L.fn j) v
  let code := Nat.land nm 255
  let p := Nat.shiftRight nm 8
  let q := Nat.add j 1
  cond (Nat.beq code 0) (bad one52 nF') <|
  cond (Nat.beq code 1)
    (bad (Nat.shiftLeft (binCdfN j v 2) 52) (Nat.mul nF' (Nat.pow 3 j))) <|
  cond (Nat.beq code 2)
    (let N := Nat.add (Nat.add L.a 2) j
     let rho := slot 256 L.sq j
     cond (Nat.blt (Nat.mul 3 (Nat.add v 1)) N)
       (bad (Nat.add (Nat.mul (Nat.mul 2 U) N) (Nat.mul 3 rho))
          (Nat.mul (Nat.shiftLeft nF' 77) (Nat.sub N (Nat.mul 3 (Nat.add v 1)))))
       (bad one52 nF')) <|
  cond (Nat.beq code 4)
    (let n0 := p
     let ok := Nat.ble v L.VM && inGrid L.GM q n0
     let fa := findA vA (Nat.sub (Nat.sub n0 q) 1) v
     let main := slot c.SW fa.1 (Nat.sub c.Q0 q)
     let e := Nat.add (Nat.add L.E v) 52
     let nF := slot 64 (getN L.inF L.E) (Nat.sub (Nat.sub n0 q) 1)
     let lhs := Nat.add (Nat.add (Nat.shiftLeft main (Nat.add e (Nat.mul 2 n0)))
         (Nat.shiftLeft (Nat.mul (Nat.mul 3 (binSum (Nat.add L.E v) v)) (Nat.mul nF DenA)) (Nat.mul 2 n0)))
       (Nat.shiftLeft (Nat.mul (binCdfN n0 v 3) DenA) e)
     let rhs := Nat.shiftLeft (Nat.mul nF' DenA) (Nat.add (Nat.sub e 52) (Nat.mul 2 n0))
     Nat.add (Nat.add (bad lhs rhs) fa.2) (cond ok 0 1)) <|
  cond (Nat.beq code 5) (bad (Nat.shiftLeft s3cum 52) (Nat.shiftLeft nF' WL)) <|
  cond (Nat.beq code 6) (bad nPrevRow nF') <|
  cond (Nat.beq code 7) (bad nNext nF') 1

def bit (m i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

/-- Whether the part checks the deficit `j`: its code is in the mask, and an `L` term is of a family
of `famsB`. -/
def doDef (L : Line) (j : Nat) : Bool :=
  let nm := slot 64 L.dn j
  cond (Nat.beq (Nat.land nm 255) 3)
    (bit L.mask 1 && L.famsB.any (fun f => Nat.beq f (Nat.add (Nat.land (Nat.shiftRight nm 8) 65535)
        (Nat.shiftLeft (Nat.sub (Nat.sub (Nat.shiftRight nm 24) (Nat.add j 1)) 1) 16))))
    (bit L.mask 0)

/-- Whether the part checks the cdf entry `(j, v)`: its code is in the mask, and an `A` term is of a
family of `famsA`. -/
def doCdf (L : Line) (j v : Nat) : Bool :=
  let nm := slot 32 (getN L.fn j) v
  cond (Nat.beq (Nat.land nm 255) 4)
    (bit L.mask 3 && L.famsA.any (fun p =>
      Nat.beq p.1 (Nat.sub (Nat.sub (Nat.shiftRight nm 8) (Nat.add j 1)) 1) && bit p.2 v))
    (bit L.mask 2)

/-- The failure count of the row `0` and the deficit `0` of the output: every slot `2^52`. -/
def row0Bad (L : Line) : Nat :=
  let r0 := getN L.outF 0
  Nat.add (natFold (Nat.add L.GM 1) 0 (fun g acc => Nat.add acc (cond (Nat.beq (slot 64 r0 g) one52) 0 1)))
    (cond (Nat.beq (slot 64 L.outD 0) one52) 0 1)

/-- The failure count of a row of 64-bit slots `0..n-1`: values at most `2^52`, nondecreasing. -/
def shapeRow (n row : Nat) : Nat :=
  (natFold n (0, 0) (fun g (st : Nat × Nat) =>
    let x := slot 64 row g
    (Nat.add st.1 (Nat.add (bad x one52) (bad st.2 x)), x))).1

def shapeVec (n row : Nat) : Nat :=
  natFold n 0 (fun g acc => Nat.add acc (bad (slot 64 row g) one52))

/-- The total failure count of the line. -/
def failures (L : Line) : Nat :=
  let c : ConvCfg := ⟨L.E, L.GM, convSW L.E⟩
  let NN := Nat.add (Nat.add L.E L.GM) 1
  let fE1 := fact (Nat.sub L.E 1)
  let Den := Nat.shiftLeft (Nat.mul fE1 (Nat.mul fE1 fE1)) (Nat.add 156 (Nat.mul 2 NN))
  let X := buildX c L.inF
  let Q := sqQ c X
  let tabA := mkTab c X Q L.E
  let oms := omRows c.SW NN (Nat.sub (Nat.mul 3 L.E) 2)
  let vA := L.famsA.map (fun p => (p.1, p.2, famA c L.VM p.1 p.2 oms tabA))
  -- (B): one table per family `J + 2^16 sh`
  let vB := L.famsB.map (fun f => (f, famB c (Nat.shiftRight f 16) oms (mkTab c X Q (Nat.land f 65535))))
  let f1 := getN L.inF 1
  let s3 := cond (bit L.mask 2) (tl (tl (s3Laws WL L.E L.GM f1))) []
  let s2 := cond (bit L.mask 0) (tl (tl (s2Laws WL L.E L.GM f1))) []
  -- deficits j = d0..d1: `U(j) ≤ uD(j) ≤ delta'(j)`, `P` read on `uD(j - 1)`
  let ds := natFold (Nat.sub (Nat.add L.d1 1) L.d0) (0, dropN (Nat.sub L.d0 1) s2)
    (fun i (st : Nat × List Nat) =>
      let j := Nat.add L.d0 i
      let r := deficitTerm L c NN Den vB (split (Nat.add (Nat.mul 2 WL) 8) (Nat.add L.E 1) (hd st.2)) j
      let u := slot 128 L.uD j
      (Nat.add st.1 (cond (doDef L j)
        (Nat.add r.2 (Nat.add (bad r.1 u) (bad u (Nat.shiftLeft (slot 64 L.outD j) 76)))) 0), tl st.2))
  -- cdf rows j = f0..f1, `L` read on `uD(j)`, with the shape of each row and the
  -- square root witness
  let fs := natFold (Nat.sub (Nat.add L.f1 1) L.f0)
      (0, dropN (Nat.sub L.f0 1) s3, dropN L.f0 L.outF, getN L.outF (Nat.sub L.f0 1))
      (fun i (st : Nat × List Nat × List Nat × Nat) =>
    let j := Nat.add L.f0 i
    let row := hd st.2.2.1
    let prevRow := st.2.2.2
    let U := slot 128 L.uD j
    let s3row := split (Nat.add (Nat.mul 2 WL) 8) (Nat.add L.GM 2) (hd st.2.1)
    let r := natFold (Nat.add L.GM 1) (0, (0 : Nat), s3row) (fun v (t : Nat × Nat × List Nat) =>
      let cum := Nat.add t.2.1 (hd t.2.2)
      (Nat.add t.1 (cond (doCdf L j v) (cdfTerm L c Den vA U j v (slot 64 row v) (slot 64 prevRow v)
          (cond (Nat.beq v L.GM) one52 (slot 64 row (Nat.add v 1))) cum) 0), cum, tl t.2.2))
    let rho := slot 256 L.sq j
    let sh := cond (bit L.mask 2) (Nat.add (shapeRow (Nat.add L.GM 1) row)
      (bad (Nat.shiftLeft (Nat.add (Nat.add L.a 2) j) 256) (Nat.mul 3 (Nat.mul rho rho)))) 0
    (Nat.add st.1 (Nat.add r.1 sh), tl st.2.1, tl st.2.2.1, row))
  -- every slot of the convolutions and envelope sums holds its value
  let sizeBad := bad (Nat.mul (Nat.shiftLeft (Nat.mul fE1 (Nat.mul fE1 fE1)) (Nat.add (Nat.mul 2 NN) 172))
    (Nat.pow 3 (Nat.mul 3 L.E))) (mask c.SW)
  Nat.add (Nat.add (Nat.add ds.1 fs.1) sizeBad)
    (cond (bit L.mask 2) (Nat.add (shapeVec (Nat.add L.E 1) L.outD) (row0Bad L)) 0)

def check (L : Line) : Bool := Nat.beq (failures L) 0

end FrogModel.D3.LaneD.K

namespace FrogModel.D3.LaneD.K

/-- The deficit bounds `U(j)`, `j = 1..E`, packed at 128-bit slots: the hint `uD` of a line, computed
by the generator (compiled evaluation; the kernel only checks them). -/
def deficitBounds (L : Line) : Nat :=
  let c : ConvCfg := ⟨L.E, L.GM, convSW L.E⟩
  let NN := Nat.add (Nat.add L.E L.GM) 1
  let fE1 := fact (Nat.sub L.E 1)
  let Den := Nat.shiftLeft (Nat.mul fE1 (Nat.mul fE1 fE1)) (Nat.add 156 (Nat.mul 2 NN))
  let X := buildX c L.inF
  let Q := sqQ c X
  let oms := omRows c.SW NN (Nat.sub (Nat.mul 3 L.E) 2)
  let vB := L.famsB.map (fun f => (f, famB c (Nat.shiftRight f 16) oms (mkTab c X Q (Nat.land f 65535))))
  let s2 := tl (tl (s2Laws WL L.E L.GM (getN L.inF 1)))
  (natFold L.E (0, s2) (fun i (st : Nat × List Nat) =>
    let j := Nat.add i 1
    let r := deficitTerm { L with uD := st.1 } c NN Den vB
      (split (Nat.add (Nat.mul 2 WL) 8) (Nat.add L.E 1) (hd st.2)) j
    (Nat.add st.1 (Nat.shiftLeft r.1 (Nat.mul 128 j)), tl st.2))).1

end FrogModel.D3.LaneD.K
