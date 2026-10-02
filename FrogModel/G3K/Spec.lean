module

public import FrogModel.G3K.Table

@[expose] public section

/-!
# The reference checker of a version 4 certificate (code/certificate/FORMAT.md, items 3 to 5)

Readable form, written with `if` and ordinary recursion. `G3K.Fast` is the same checker written
for the Lean kernel and nanoda; `G3K.Equiv` proves the two equal, function by function. The
compiled validation (`g3k TABLE DATA`, code/g3k) runs this form.

The data are one tree `t` (`G3K.Tree`). `checkAll t` checks every leaf of `t` as a state: for a leaf
of key `k`, the entry `s := find t k` must have key `k`, satisfy the lane bounds of its phase, and
pass `stateCheck t s k`: the moves and stops of the state of key `k` are generated from the table
(each weight rounded on its own to 2^-48), each target is resolved through `find` (the reached state
if it is in the data with flag 1, else its lump, which must be in the data), and V'(s) and W'(s) are
compared with the right sides of items 4 and 5, lane by lane with guard bits. Soundness for any
tree: `checkAll_sound`.

Keys. The state `(q, {c1, c2, c3, c4}, p)` with `c1 ≤ c2 ≤ c3 ≤ c4` has the key
`enc q c1 c2 c3 c4 p` (radix 128); `decQ`, `decC1` to `decC4`, `decP` read it back.

Lanes. V' of phase `q` has `(phase q).nL` lanes of 96 bits, in the order of `G3Tool.laneIdx` (by
total, then by tail), so that the exit `x ↦ x - e_q` and the end of a phase are the gathers `gx`,
`cp0`, `cp1` of `phase q`. W' has T + 1 = 9 lanes of 128 bits, lane b the budget b. Bounds (checked
on the entry of each state): every lane of V' below 2^47 and no bit above lane `nL`, every lane of
W' below 2^77 and no bit above lane T. With the bounds of the right sides checked by `final`,
every lane of both sides of each comparison stays below its guard bit, whatever the data.
-/

namespace FrogModel.G3K

/-! The tree. -/

/-- The entry for the key `k`: the leaf reached by the pivots. -/
def Tree.find : Tree → Nat → E
  | .leaf e, _ => e
  | .node p l r, k => if p ≤ k then r.find k else l.find k

/-- `P` holds at every leaf. -/
def Tree.all (P : E → Bool) : Tree → Bool
  | .leaf e => P e
  | .node _ l r => l.all P && r.all P

theorem Tree.all_find {P : E → Bool} {t : Tree} (h : t.all P = true) (k : Nat) :
    P (t.find k) = true := by
  induction t with
  | leaf e => exact h
  | node p l r ihl ihr =>
    simp only [Tree.all, Bool.and_eq_true] at h
    simp only [Tree.find]
    split
    · exact ihr h.2
    · exact ihl h.1

theorem Tree.all_node {P : E → Bool} {p : Nat} {l r : Tree} (hl : l.all P = true)
    (hr : r.all P = true) : (Tree.node p l r).all P = true := by
  simp [Tree.all, hl, hr]

namespace Spec

/-! Keys. -/

def enc (q a b c d p : Nat) : Nat := ((((q * 128 + a) * 128 + b) * 128 + c) * 128 + d) * 128 + p

def decQ (k : Nat) : Nat := k / 2 ^ 35
def decC1 (k : Nat) : Nat := k / 2 ^ 28 % 128
def decC2 (k : Nat) : Nat := k / 2 ^ 21 % 128
def decC3 (k : Nat) : Nat := k / 2 ^ 14 % 128
def decC4 (k : Nat) : Nat := k / 2 ^ 7 % 128
def decP (k : Nat) : Nat := k % 128

/-- The key of (q, {x, y, z, w}, p) for x ≤ y ≤ z: w inserted. -/
def encIns (q x y z w p : Nat) : Nat :=
  if w ≤ x then enc q w x y z p
  else if w ≤ y then enc q x w y z p
  else if w ≤ z then enc q x y w z p
  else enc q x y z w p

/-- `(a, b, c)` sorted. -/
def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  if a ≤ b then
    (if c ≤ a then (c, a, b) else if c ≤ b then (a, c, b) else (a, b, c))
  else
    (if c ≤ b then (c, b, a) else if c ≤ a then (b, c, a) else (b, a, c))

/-- The key of the lump of (q, {c1, c2, c3, c4}, p). -/
def lumpKey4 (q c1 c2 c3 c4 p : Nat) : Nat :=
  let s := sort3 (lumpC c1) (lumpC c2) (lumpC c3)
  encIns q s.1 s.2.1 s.2.2 (lumpC c4) p

/-! Weights. -/

def two40 : Nat := 2 ^ 40
def two48 : Nat := 2 ^ 48

/-- `floor(2^48 n / d)`. -/
def lo48 (n d : Nat) : Nat := n * two48 / d
/-- `ceil(2^48 n / d)`. -/
def up48 (n d : Nat) : Nat := (n * two48 + d - 1) / d

/-! Targets. -/

/-- A failed lookup. -/
def bad : E := ⟨0, 2, 0, 0⟩

/-- The target: the state of key `k` if it is in the data with flag 1, else the state of key `lk`
(the lump), else `bad`. -/
def look (t : Tree) (k lk : Nat) : E :=
  if (t.find k).key = k ∧ (t.find k).flag = 1 then t.find k
  else if (t.find lk).key = lk then t.find lk
  else bad

/-! The accumulator of the right sides: V of the moves in the phase (`vs`, lanes of phase q), of
the moves to the next phase (`vn`, lanes of phase q + 1, gathered at the end), of the absorbed moves
(`av`, a number), W of the moves (`ww`), the stops (`pp`, a number), the sums of the coefficients
of the V terms (`sl`, the `lo`) and of the W terms (`sh`, the `hi`), and whether every target was
found (`ok`). With `sl` and `sh`, `final` bounds every lane of both right sides below its guard
bit. -/

structure Acc where
  vs : Nat
  vn : Nat
  av : Nat
  ww : Nat
  pp : Nat
  sl : Nat
  sh : Nat
  ok : Bool

def acc0 : Acc := ⟨0, 0, 0, 0, 0, 0, 0, true⟩

def addSame (lo hi : Nat) (t : E) (a : Acc) : Acc :=
  ⟨a.vs + lo * t.v, a.vn, a.av, a.ww + hi * t.w, a.pp, a.sl + lo, a.sh + hi,
    a.ok && decide (t.flag ≤ 1)⟩
def addNext (lo hi : Nat) (t : E) (a : Acc) : Acc :=
  ⟨a.vs, a.vn + lo * t.v, a.av, a.ww + hi * t.w, a.pp, a.sl + lo, a.sh + hi,
    a.ok && decide (t.flag ≤ 1)⟩
def addAbs (lo : Nat) (a : Acc) : Acc :=
  ⟨a.vs, a.vn, a.av + lo * two40, a.ww, a.pp, a.sl + lo, a.sh, a.ok⟩
def addStop (x : Nat) (a : Acc) : Acc := ⟨a.vs, a.vn, a.av, a.ww, a.pp + x, a.sl, a.sh, a.ok⟩

/-! Moves. A child state of the state (q, σ, p) is moved; `x ≤ y ≤ z` are the other three
children, `(l1, l2, l3)` their lumps sorted, `n3 / d3` the product of their potentials. -/

/-- The stop of weight `num / pd` reaching (q, {x, y, z, w}, p2), exponent `e = p2 + J - q`. -/
def stopW (n3 d3 w num pd e : Nat) : Nat :=
  up48 (num * phiN ^ e * (n3 * wN w)) (pd * phiD ^ e * (d3 * wD w))

/-- A move with f = 0 of weight `num / pd` from phase `q` to (q, {x, y, z, w}, p2). -/
def move (t : Tree) (q x y z l1 l2 l3 n3 d3 w p2 num pd : Nat) (a : Acc) : Acc :=
  if cTP < p2 then addStop (stopW n3 d3 w num pd (p2 + cJ - q)) a
  else if p2 = 0 then
    if q = cJ then addAbs (lo48 num pd) a
    else addNext (lo48 num pd) (up48 num pd)
      (look t (encIns (q + 1) x y z w 1) (encIns (q + 1) l1 l2 l3 (lumpC w) 1)) a
  else addSame (lo48 num pd) (up48 num pd)
      (look t (encIns q x y z w p2) (encIns q l1 l2 l3 (lumpC w) p2)) a

/-- The moves of one row: child state replaced by `r.next`, pending `p1 + r.delta`, weight
`m r.pn / r.pd`. -/
def rowLoop (t : Tree) (q x y z l1 l2 l3 n3 d3 p1 m : Nat) : List Tr → Acc → Acc
  | [], a => a
  | r :: rs, a => rowLoop t q x y z l1 l2 l3 n3 d3 p1 m rs
      (move t q x y z l1 l2 l3 n3 d3 r.next (p1 + r.delta) (m * r.pn) r.pd a)

/-- `eps (1 - rho) rho^k / 5`, numerator and denominator. -/
def tailN (k : Nat) : Nat := epsN * (rhoD - rhoN) * rhoN ^ k
def tailD (k : Nat) : Nat := 5 * epsD * rhoD ^ (k + 1)

/-- The tail atoms t = T + 1 + k, k from `k` on, `n` of them, reaching the child state `ct`. -/
def tailLoop (t : Tree) (q x y z l1 l2 l3 n3 d3 ct p1 m : Nat) : Nat → Nat → Acc → Acc
  | _, 0, a => a
  | k, n + 1, a => tailLoop t q x y z l1 l2 l3 n3 d3 ct p1 m (k + 1) n
      (move t q x y z l1 l2 l3 n3 d3 ct (p1 + (cT + 1 + k)) (m * tailN k) (tailD k) a)

/-- The closed-form tail at t0 = T + 1 + k0: `m eps (1 - rho) rho^k0 phi^t0 / ((1 - phi rho) 5)`
times `phi^e` and the potentials of {x, y, z, ct}. -/
def cfW (n3 d3 ct m t0 e : Nat) : Nat :=
  up48 (m * tailN (t0 - (cT + 1)) * (phiN ^ t0 * (phiD * rhoD)) * phiN ^ e * (n3 * wN ct))
    (tailD (t0 - (cT + 1)) * (phiD ^ t0 * (phiD * rhoD - phiN * rhoN)) * phiD ^ e * (d3 * wD ct))

/-- The tail atoms of a child state F or B, then its closed-form tail. -/
def withTails (t : Tree) (q x y z l1 l2 l3 n3 d3 ct p m : Nat) (a : Acc) : Acc :=
  addStop (cfW n3 d3 ct m (max (cT + 1) (cTP + 2 - p)) (p - 1 + cJ - q))
    (tailLoop t q x y z l1 l2 l3 n3 d3 ct (p - 1) m 0 (cTP + 1 - (p + cT)) a)

/-- All moves of the child state `c` of multiplicity `m`, the others being x ≤ y ≤ z. -/
def child (t : Tree) (q c x y z p m : Nat) (a : Acc) : Acc :=
  let s := sort3 (lumpC x) (lumpC y) (lumpC z)
  let n3 := wN x * wN y * wN z
  let d3 := wD x * wD y * wD z
  if c ≤ 1 then
    withTails t q x y z s.1 s.2.1 s.2.2 n3 d3 (tailOf c) p m
      (rowLoop t q x y z s.1 s.2.1 s.2.2 n3 d3 (p - 1) m (row c) a)
  else rowLoop t q x y z s.1 s.2.1 s.2.2 n3 d3 (p - 1) m (row c) a

/-- The moves of every distinct child state of {c1, c2, c3, c4}, c1 ≤ c2 ≤ c3 ≤ c4, with its
multiplicity. -/
def moves (t : Tree) (q c1 c2 c3 c4 p : Nat) : Acc :=
  if c4 = c3 then
    (if c3 = c2 then
      (if c2 = c1 then child t q c1 c2 c3 c4 p 4 acc0
      else child t q c2 c1 c3 c4 p 3 (child t q c1 c2 c3 c4 p 1 acc0))
    else
      (if c2 = c1 then child t q c3 c1 c2 c4 p 2 (child t q c1 c2 c3 c4 p 2 acc0)
      else child t q c3 c1 c2 c4 p 2 (child t q c2 c1 c3 c4 p 1 (child t q c1 c2 c3 c4 p 1 acc0))))
  else
    child t q c4 c1 c2 c3 p 1
      (if c3 = c2 then
        (if c2 = c1 then child t q c1 c2 c3 c4 p 3 acc0
        else child t q c2 c1 c3 c4 p 2 (child t q c1 c2 c3 c4 p 1 acc0))
      else
        (if c2 = c1 then child t q c3 c1 c2 c4 p 1 (child t q c1 c2 c3 c4 p 2 acc0)
        else child t q c3 c1 c2 c4 p 1 (child t q c2 c1 c3 c4 p 1 (child t q c1 c2 c3 c4 p 1 acc0))))

/-! Lanes. -/

/-- The lanes `[a, b)` of 96 bits. -/
def laneMask (a b : Nat) : Nat := 2 ^ (96 * b) - 2 ^ (96 * a)

/-- `Σ (u &&& lanes [a, b)) * 2^(96 s)` over the list. -/
def gather (u : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | (a, b, s) :: r => (u &&& laneMask a b) * 2 ^ (96 * s) + gather u r

/-- The lanes of `b` are at least those of `a`, for lanes below the guard bits `G`. -/
def leLanes (G a b : Nat) : Bool := decide ((b + G - a) &&& G = G)

/-- One in each of the T + 1 lanes of 128 bits. -/
def onesW : Nat := (2 ^ (128 * (cT + 1)) - 1) / (2 ^ 128 - 1)
def gW : Nat := 2 ^ 127 * onesW
/-- The lanes 0 to T - 1 of W'. -/
def lowW : Nat := 2 ^ (128 * cT) - 1
/-- Bits 0 to 76 of each lane of W'. -/
def lowWb : Nat := (2 ^ 77 - 1) * onesW

/-- W' of the exit target, moved up one budget. -/
def wUp (t : E) : Nat := (t.w &&& lowW) * 2 ^ 128

/-- Items 4 and 5 at the state `s` of phase `q`, given the exit's parts of the right sides. The
three bounds keep every lane of both right sides below its guard bit: with the lanes of V' below
2^47 and those of W' below 2^77 (`boundsOK` of the targets), a lane of the V side is at most
(sl + exitLo)(2^47 - 1) ≤ 2^48 (2^47 - 1) < 2^95, and a lane of the W side is below
(sh + exitHi) 2^77 + (pp + e0) 2^40 ≤ 2^126 + 2^126 = 2^127. -/
def final (s : E) (q : Nat) (a : Acc) (ev ew e0 : Nat) (eok : Bool) : Bool :=
  a.ok && eok &&
  decide (a.sl + exitLo ≤ two48) && decide (a.sh + exitHi ≤ 2 ^ 49) &&
  decide (a.pp + e0 < 2 ^ 86) &&
  leLanes (phase q).gV (s.v * two48) (a.vs + gather a.vn (phase q).cp0 + (a.av + ev)) &&
  leLanes gW (a.ww + ew + (a.pp * two40 * onesW + e0 * two40)) (s.w * two48)

def exitSame (s : E) (q : Nat) (a : Acc) (e0 : Nat) (t : E) : Bool :=
  final s q a (gather (exitLo * t.v) (phase q).gx) (exitHi * wUp t) e0 (decide (t.flag ≤ 1))
def exitNext (s : E) (q : Nat) (a : Acc) (e0 : Nat) (t : E) : Bool :=
  final s q a (gather (exitLo * t.v) (phase q).cp1) (exitHi * wUp t) e0 (decide (t.flag ≤ 1))

/-- The exit and its stop at budget 0 (weight `e0`), then the comparisons. -/
def finish (t : Tree) (s : E) (q c1 c2 c3 c4 p : Nat) (a : Acc) (e0 : Nat) : Bool :=
  if p = 1 then
    if q = cJ then final s q a (exitLo * two40 * 2 ^ 96) 0 e0 true
    else exitNext s q a e0 (look t (enc (q + 1) c1 c2 c3 c4 1) (lumpKey4 (q + 1) c1 c2 c3 c4 1))
  else exitSame s q a e0 (look t (enc q c1 c2 c3 c4 (p - 1)) (lumpKey4 q c1 c2 c3 c4 (p - 1)))

/-- The weight of the exit stop at budget 0, `(theta / 5) phi^(p - 1 + J - q)` times the
potentials, rounded up. -/
def exitStop (q c1 c2 c3 c4 p : Nat) : Nat :=
  up48 (th5N * phiN ^ (p - 1 + cJ - q) * (wN c1 * wN c2 * wN c3 * wN c4))
    (th5D * phiD ^ (p - 1 + cJ - q) * (wD c1 * wD c2 * wD c3 * wD c4))

/-- Items 3 to 5 at the state (q, {c1, c2, c3, c4}, p) of entry `s`. -/
def checkS (t : Tree) (s : E) (q c1 c2 c3 c4 p : Nat) : Bool :=
  finish t s q c1 c2 c3 c4 p (moves t q c1 c2 c3 c4 p) (exitStop q c1 c2 c3 c4 p)

/-- Items 3 to 5 at the state of key `k`, with the entry `s`. -/
def stateCheck (t : Tree) (s : E) (k : Nat) : Bool :=
  checkS t s (decQ k) (decC1 k) (decC2 k) (decC3 k) (decC4 k) (decP k)

/-- The lane bounds of the entry `s` of phase `q`. -/
def boundsOK (s : E) (q : Nat) : Bool :=
  decide (s.v &&& (phase q).lowV = s.v) && decide (s.w &&& lowWb = s.w)

/-- The check of the leaf `e`: the entry found for its key has that key, its bounds, its state. -/
def stateOK (t : Tree) (e : E) : Bool :=
  decide ((t.find e.key).key = e.key) && boundsOK (t.find e.key) (decQ e.key) &&
    stateCheck t (t.find e.key) e.key

/-- Every leaf of `t` checked as a state. -/
def checkAll (t : Tree) : Bool := t.all (stateOK t)

/-- Soundness of the lookups, for any tree: every entry that `find` returns for its own key passed
its bounds and its state check. -/
theorem checkAll_sound {t : Tree} (h : checkAll t = true) (k : Nat) (hk : (t.find k).key = k) :
    boundsOK (t.find k) (decQ k) = true ∧ stateCheck t (t.find k) k = true := by
  have := Tree.all_find h k
  simp only [stateOK, hk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.2, this.2⟩

end Spec
end FrogModel.G3K
