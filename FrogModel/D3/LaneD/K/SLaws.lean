module

public import FrogModel.D3.LaneD.K.Basic

@[expose] public section

/-!
# The laws of the lower closures S2 and S3 (Lemma 12.1 of the paper), upper bounds in fixed point

Upper bounds of every mass of the staged recursion `stageLaw` of FrogModel/D3/Interfaces/Step.lean,
at `2^-W`: the coefficients rounded up, every slot rounded up after each row. A law on the counts
`0..n-1` is one natural with slots of `SW = 2 W + 8` bits. The window term of a stage,
`sum over r of pn R(r) A_(f+1)(y - 1 + r)` for every `y`, is one product of the rows of the next stage
(packed at the row stride `n SW`) with the reversed masses `pn R`, read at row `y - 1 + rmax`.
-/

namespace FrogModel.D3.LaneD.K

structure LawCfg where
  W : Nat
  n : Nat

def LawCfg.SW (c : LawCfg) : Nat := Nat.add (Nat.mul 2 c.W) 8
def LawCfg.RS (c : LawCfg) : Nat := Nat.mul c.n c.SW

/-- `2^W - 1` in the low `W` bits of each of the `n` slots. -/
def lowOnes (c : LawCfg) : Nat := Nat.mul (mask c.W) (ones c.SW c.n)
/-- The bits `[W, SW)` of each slot. -/
def hiMask (c : LawCfg) : Nat := Nat.mul (Nat.sub (mask c.SW) (mask c.W)) (ones c.SW c.n)

/-- Every slot divided by `2^W`, rounded up. -/
def ceilK (c : LawCfg) (x : Nat) : Nat :=
  Nat.shiftRight (Nat.land (Nat.add x (lowOnes c)) (hiMask c)) c.W

/-- Counts `k ↦ k + 1`, the count `n - 1` absorbing. -/
def capShift (c : LawCfg) (r : Nat) : Nat :=
  let top := Nat.mul c.SW (Nat.sub c.n 1)
  Nat.add (Nat.land (Nat.shiftLeft r c.SW) (mask c.RS)) (Nat.shiftLeft (Nat.shiftRight r top) top)

/-- `ceil(a 2^W / b)`. -/
def cst (c : LawCfg) (a b : Nat) : Nat := cdiv (Nat.shiftLeft a c.W) b

/-- The point mass at count `0`. -/
def unit (c : LawCfg) : Nat := Nat.shiftLeft 1 c.W

/-- `ceilK (cg prev + cc capShift prev + t)`. -/
def rowStep (c : LawCfg) (cg cc prev t : Nat) : Nat :=
  ceilK c (Nat.add (Nat.add (Nat.mul cg prev) (Nat.mul cc (capShift c prev))) t)

/-- Rows `0..Y` of a stage (`cg`, `cc` the gone and count coefficients), from the window terms
`ts = [t_1, t_2, ...]`. -/
def stageRows (c : LawCfg) (Y cg cc : Nat) (ts : List Nat) : List Nat :=
  (natFold Y ([unit c], ts) (fun _ (st : List Nat × List Nat) =>
    (rowStep c cg cc (hd st.1) (hd st.2) :: st.1, tl st.2))).1.reverse

/-- The window terms `t_y`, `y = 1..`, of a stage: `pnR` the masses `pn R(r)` (`r = 0..rmax`) at
`2^-W`, `nxt` the rows of the next stage. -/
def windows (c : LawCfg) (pnR : List Nat) (nxt : List Nat) : List Nat :=
  let rmax := Nat.sub pnR.length 1
  let T := packRows c.RS nxt
  let RP := packRows c.RS pnR.reverse
  dropN rmax (split c.RS (Nat.add nxt.length rmax) (Nat.mul T RP))

/-- The pseudo-law of a cdf row `F(0..GM)` at `2^-52` (64-bit slots), at `2^-W`: masses
`F(g) - F(g - 1)` and `1 - F(GM)` at `GM + 1`. -/
def pseudoLaw (W GM row : Nat) : List Nat :=
  let st := natFold (Nat.add GM 1) ([], 0) (fun g (st : List Nat × Nat) =>
    let x := slot 64 row g
    (Nat.shiftLeft (Nat.sub x st.2) (Nat.sub W 52) :: st.1, x))
  (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 52) st.2) (Nat.sub W 52) :: st.1).reverse

/-- `ceil(x a / b)` entry by entry. -/
def scaleUp (a b : Nat) (r : List Nat) : List Nat := r.map (fun x => cdiv (Nat.mul x a) b)

/-- S3: upper bounds of the laws of `min(X'', GM + 1)`, `q = 0..E + 1` (rows of `GM + 2` slots). -/
def s3Laws (W E GM : Nat) (f1 : Nat) : List Nat :=
  let c : LawCfg := ⟨W, Nat.add GM 2⟩
  let r := pseudoLaw W GM f1
  let rmax := Nat.add GM 1
  let y0 := Nat.add E 1
  let a3 := stageRows c (Nat.add y0 (Nat.mul 3 rmax)) (cst c 2 3) (cst c 1 3) []
  let a2 := stageRows c (Nat.add y0 (Nat.mul 2 rmax)) (cst c 4 10) (cst c 3 10)
    (windows c (scaleUp 3 10 r) a3)
  let a1 := stageRows c (Nat.add y0 rmax) (cst c 2 11) (cst c 3 11) (windows c (scaleUp 6 11 r) a2)
  stageRows c y0 0 (cst c 1 4) (windows c (scaleUp 3 4 r) a1)

/-- S2: upper bounds of the laws of `min(e''_c, E)`, `q = 0..E + 1` (rows of `E + 1` slots). -/
def s2Laws (W E GM : Nat) (f1 : Nat) : List Nat :=
  let c : LawCfg := ⟨W, Nat.add E 1⟩
  let r := pseudoLaw W GM f1
  let rmax := Nat.add GM 1
  let y0 := Nat.add E 1
  let a2 := stageRows c (Nat.add y0 (Nat.mul 2 rmax)) (cst c 7 10) (cst c 3 10) []
  let a1 := stageRows c (Nat.add y0 rmax) (cst c 5 11) (cst c 3 11) (windows c (scaleUp 3 11 r) a2)
  stageRows c y0 (cst c 1 4) (cst c 1 4) (windows c (scaleUp 1 2 r) a1)

end FrogModel.D3.LaneD.K
