module

public import FrogModel.Engine.G3Codes
public import FrogModel.Engine.G3Lanes

@[expose] public section

/-!
# What a certificate that passes the G3 checker delivers

A tree `t` of entries (G3K.Spec) defines, on the states of the dominating chain of `cand` with
`T' = 16` and `keep` the states of the data with flag 1 (`keepOf t`):

- `Vs t o`, the sub-solution of the absorption with outputs `o`: on a live unflagged state with
  `e ≤ T`, `1 ≤ p ≤ 16`, well-formed children and its key in the data (`Covered`), and an output
  `o` that extends the recorded outputs, is non-decreasing from `e` on and ends at most at `T`
  (`Fits`), lane `laneIdx (incr o i e)` of V' of its entry, in units of `2^-40`; `0` elsewhere;
- `Ws t`, the super-solution of the system whose reward is `Phi` at the step that sets the flag:
  `theta^e` times lane `T - e` of W' of the entry, in units of `2^-40`, on the covered states; `0`
  on the flagged, absorbed and `e > T` states; `⊤` on the other live states.

The inequalities of items 4 and 5 of code/certificate/FORMAT.md read back through the checker are
`Vs_sub_of_check` (G3StepV) and `Ws_super_of_check` (G3StepW); `domCert_of_check` (G3Cert)
assembles `DomCert` with the start checks of `startOK` (the start in the data, the atoms of `L`
below V' of the start, the stop weight).

Lane order (G3Tool.Parse.laneIdx): the increments `x = (x_q, ..., x_J)` of phase `q`, by total and
then by tail; `cntm L n` is the number of vectors of length `L` with total below `n`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine.G3

open FrogModel.Cert FrogModel.LemmaX

/-! ### Lanes of the outputs -/

/-- The vectors of length `L` with total below `n`: `binom(n - 1 + L, L)`, `0` at `n = 0`. -/
def cntm (L n : ℕ) : ℕ := if n = 0 then 0 else Nat.choose (n - 1 + L) L

/-- The lane of a vector of increments: by total, then by tail. -/
def laneIdx : List ℕ → ℕ
  | [] => 0
  | x :: xs => cntm (xs.length + 1) (x + xs.sum) + laneIdx xs

/-- Coordinate `k` of an output, `0` beyond `3`. -/
def oget (o : Fin 4 → ℕ) (k : ℕ) : ℕ := if h : k < 4 then o ⟨k, h⟩ else 0

/-- The increments of `o` from frog `i` on, from `e`: `(o i - e, o (i + 1) - o i, ...)`. -/
def incr (o : Fin 4 → ℕ) (i e : ℕ) : List ℕ :=
  (List.range (4 - i)).map fun j => oget o (i + j) - if j = 0 then e else oget o (i + j - 1)

/-- `o` can be the output of the chain absorbed unflagged from `x`. -/
def Fits (o : Fin 4 → ℕ) (x : RState CState 4 4) : Prop :=
  (∀ k : Fin 4, (k : ℕ) < x.i → x.out k = (o k : ℕ∞)) ∧ x.e ≤ oget o x.i ∧
    (∀ k, x.i ≤ k → k + 1 < 4 → oget o k ≤ oget o (k + 1)) ∧ o 3 ≤ cand.T

/-! ### The states of the data -/

/-- The entry of the data at the key of `x`. -/
def entry (t : G3K.Tree) (x : RState CState 4 4) : G3K.E := t.find (keyOf x)

/-- The states the dominating chain keeps: in the data with flag 1. -/
def keepOf (t : G3K.Tree) (x : RState CState 4 4) : Bool :=
  decide ((entry t x).key = keyOf x) && decide ((entry t x).flag = 1)

/-- The states the checker covers: live, unflagged, `e ≤ T`, `1 ≤ p ≤ 16`, well-formed children,
the key in the data. -/
def Covered (t : G3K.Tree) (y : RState CState 4 4 × Bool) : Prop :=
  y.2 = false ∧ y.1.i < 4 ∧ y.1.e ≤ cand.T ∧ 1 ≤ y.1.p ∧ y.1.p ≤ 16 ∧
    (∀ c, cand.ChildWF (y.1.σ c)) ∧ (entry t y.1).key = keyOf y.1

open Classical in
/-- **The sub-solution of the absorption with outputs `o`**. -/
noncomputable def Vs (t : G3K.Tree) (o : Fin 4 → ℕ) (y : RState CState 4 4 × Bool) : ℝ≥0∞ :=
  if Covered t y ∧ Fits o y.1 then
    (lane 96 (laneIdx (incr o y.1.i y.1.e)) (entry t y.1).v : ℝ≥0∞) / 2 ^ 40
  else 0

open Classical in
/-- **The super-solution of the flagged weight**. -/
noncomputable def Ws (t : G3K.Tree) (y : RState CState 4 4 × Bool) : ℝ≥0∞ :=
  if y.2 = true ∨ 4 ≤ y.1.i ∨ cand.T < y.1.e then 0
  else if Covered t y then
    thetaC ^ y.1.e * ((lane 128 (cand.T - y.1.e) (entry t y.1).w : ℝ≥0∞) / 2 ^ 40)
  else ⊤

/-- The dominating chain of `cand` that the data drive. -/
noncomputable abbrev gT (t : G3K.Tree) := candDom 16 (keepOf t)

theorem Vs_supp (t : G3K.Tree) (o : Fin 4 → ℕ) (y : RState CState 4 4 × Bool)
    (h : Vs t o y ≠ 0) : y.2 = false ∧ y.1.i < 4 ∧ y.1.e ≤ cand.T := by
  unfold Vs at h
  split_ifs at h with hc
  · exact ⟨hc.1.1, hc.1.2.1, hc.1.2.2.1⟩
  · exact absurd rfl h

/-! ### The start -/

/-- The key of the start: phase 1, four fresh children, one pending frog. -/
def startKey : ℕ := G3K.Spec.enc 1 0 0 0 0 1

theorem keyOf_start : keyOf (start .fresh : RState CState 4 4) = startKey := by
  have h : codeMs (start .fresh : RState CState 4 4).σ = ↑[0, 0, 0, 0] := by
    simp [codeMs, start, code]; rfl
  unfold keyOf
  rw [h, Multiset.coe_sort, List.mergeSort_eq_self _ (by decide)]
  rfl

/-- The lane of a cumulative block `(B(1), ..., B(4))` at the start. -/
def blockLane (x : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  laneIdx [x.1, x.2.1 - x.1, x.2.2.1 - x.2.1, x.2.2.2 - x.2.2.1]

/-- An atom `(x, m)` of `L`: a non-decreasing block ending at most at `T`, with `m` at most the lane
of `x` in V' of the start. -/
def atomOK (v : ℕ) (a : (ℕ × ℕ × ℕ × ℕ) × ℕ) : Bool :=
  decide (a.1.1 ≤ a.1.2.1 ∧ a.1.2.1 ≤ a.1.2.2.1 ∧ a.1.2.2.1 ≤ a.1.2.2.2 ∧ a.1.2.2.2 ≤ 8 ∧
    a.2 ≤ lane 96 (blockLane a.1) v)

/-- (I3b) on the data: lane `T` of W' of the start, `2^-40` units, at most `eps theta^(T + 1)`. -/
def stopOK (w : ℕ) : Bool :=
  decide (lane 128 8 w * G3K.epsD * G3K.th5D ^ 9 ≤ 2 ^ 40 * G3K.epsN * (5 * G3K.th5N) ^ 9)

/-- A block as one number, injective on the blocks with entries below `2^16`. -/
def blockNum (x : ℕ × ℕ × ℕ × ℕ) : ℕ := ((x.1 * 2 ^ 16 + x.2.1) * 2 ^ 16 + x.2.2.1) * 2 ^ 16 + x.2.2.2

/-- The checks at the start: the start in the data, the blocks of `A` strictly increasing, every
atom below V' of the start, the stop weight. -/
def startOK (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (t : G3K.Tree) : Bool :=
  decide ((t.find startKey).key = startKey) &&
    decide (List.IsChain (· < ·) (A.map fun a => blockNum a.1)) &&
    A.all (atomOK (t.find startKey).v) && stopOK (t.find startKey).w

/-- The weight of the flagged part, read at the start. -/
noncomputable def Sov (t : G3K.Tree) : ℝ≥0∞ := (lane 128 8 (t.find startKey).w : ℝ≥0∞) / 2 ^ 40

/-- The start is covered when its key is in the data. -/
theorem covered_start (t : G3K.Tree) (hs : (t.find startKey).key = startKey) :
    Covered t (start .fresh, false) := by
  refine ⟨rfl, by decide, Nat.zero_le _, le_rfl, by decide, fun _ => by show cand.ChildWF CState.fresh; decide, ?_⟩
  show (t.find (keyOf (start .fresh : RState CState 4 4))).key = keyOf (start .fresh)
  rw [keyOf_start]
  exact hs

theorem Ws_start (t : G3K.Tree) (hs : (t.find startKey).key = startKey) :
    Ws t (start .fresh, false) = Sov t := by
  unfold Ws
  rw [if_neg (by simp [start]), if_pos (covered_start t hs)]
  show thetaC ^ 0 * ((lane 128 (cand.T - 0) (t.find (keyOf (start .fresh))).w : ℝ≥0∞) / 2 ^ 40) =
    Sov t
  rw [keyOf_start, pow_zero, one_mul, Nat.sub_zero]
  rfl

theorem toBlock4_inj (x y : ℕ × ℕ × ℕ × ℕ) (h : toBlock4 x = toBlock4 y) : x = y := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [toBlock4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Nat.cast_inj] at h0 h1 h2 h3
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨a', b', c', d'⟩ := y
  simp_all

/-- With strictly increasing blocks, the mass of `latMeasure A` at a point is `0` or the mass of
the one atom there. -/
theorem latMeasure_single (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ))
    (hA : A.Pairwise fun a b => blockNum a.1 < blockNum b.1) (B : Fin 4 → ℕ∞) :
    latMeasure A {B} = 0 ∨ ∃ a ∈ A, B = toBlock4 a.1 ∧ latMeasure A {B} = (a.2 : ℝ≥0∞) / 2 ^ 40 := by
  induction A with
  | nil => left; simp [latMeasure]
  | cons a A ih =>
    rw [List.pairwise_cons] at hA
    have hsplit : latMeasure (a :: A) {B} =
        ((a.2 : ℝ≥0∞) / 2 ^ 40) * (if toBlock4 a.1 = B then 1 else 0) + latMeasure A {B} := by
      unfold latMeasure
      rw [List.map_cons, List.sum_cons, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply' _ (measurableSet_singleton B), smul_eq_mul]
      congr 2
      by_cases hB : toBlock4 a.1 = B
      · simp [hB]
      · simp [hB, Set.indicator]
    by_cases hB : B = toBlock4 a.1
    · rcases ih hA.2 with h0 | ⟨a', ha', hB', -⟩
      · right
        refine ⟨a, List.mem_cons_self .., hB, ?_⟩
        rw [hsplit, h0, if_pos hB.symm, mul_one, add_zero]
      · have := hA.1 a' ha'
        rw [toBlock4_inj _ _ (hB.symm.trans hB')] at this
        exact absurd this (lt_irrefl _)
    · rw [hsplit, if_neg (Ne.symm hB), mul_zero, zero_add]
      rcases ih hA.2 with h0 | ⟨a', ha', hB', h'⟩
      · exact Or.inl h0
      · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hB', h'⟩

theorem latMeasure_le_Vs (t : G3K.Tree) (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (hs : startOK A t = true) (o : Fin 4 → ℕ) :
    latMeasure A {fun k => (o k : ℕ∞)} ≤ Vs t o (start .fresh, false) := by
  have hs' := hs
  simp only [startOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs'
  obtain ⟨⟨⟨hkey, hch⟩, hat⟩, -⟩ := hs'
  have hpw : A.Pairwise fun a b => blockNum a.1 < blockNum b.1 := by
    have := List.isChain_iff_pairwise.1 hch
    rwa [List.pairwise_map] at this
  rcases latMeasure_single A hpw (fun k => (o k : ℕ∞)) with h0 | ⟨a, ha, hB, hm⟩
  · rw [h0]; exact zero_le
  rw [hm]
  have hok := hat a ha
  simp only [atomOK, decide_eq_true_eq] at hok
  obtain ⟨h01, h12, h23, h3T, hlane⟩ := hok
  have ho : ∀ k, (o k : ℕ∞) = toBlock4 a.1 k := fun k => congrFun hB k
  have ho0 : o 0 = a.1.1 := by have := ho 0; simpa [toBlock4] using this
  have ho1 : o 1 = a.1.2.1 := by have := ho 1; simpa [toBlock4] using this
  have ho2 : o 2 = a.1.2.2.1 := by have := ho 2; simpa [toBlock4] using this
  have ho3 : o 3 = a.1.2.2.2 := by have := ho 3; simpa [toBlock4] using this
  have hF : Fits o (start .fresh) := by
    refine ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Nat.zero_le _, fun k _ hk => ?_, ?_⟩
    · have hk3 : k < 3 := by omega
      interval_cases k <;> simp [oget, ho0, ho1, ho2, ho3] <;> omega
    · rw [ho3]; exact h3T
  unfold Vs
  rw [if_pos ⟨covered_start t hkey, hF⟩]
  have hinc : incr o 0 0 = [a.1.1, a.1.2.1 - a.1.1, a.1.2.2.1 - a.1.2.1, a.1.2.2.2 - a.1.2.2.1] := by
    simp [incr, oget, List.range_succ, ho0, ho1, ho2, ho3]
  show (a.2 : ℝ≥0∞) / 2 ^ 40 ≤
    (lane 96 (laneIdx (incr o 0 0)) (t.find (keyOf (start .fresh))).v : ℝ≥0∞) / 2 ^ 40
  rw [keyOf_start, hinc]
  gcongr
  exact_mod_cast hlane

theorem stopWeight_of_check (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (t : G3K.Tree)
    (hs : startOK A t = true) : StopWeight (Sov t) := by
  have hs' := hs
  simp only [startOK, Bool.and_eq_true] at hs'
  have hst := hs'.2
  simp only [stopOK, decide_eq_true_eq] at hst
  obtain ⟨-, -, -, heps, -, -, hth, hepsD, -, -, -, hthD, -⟩ := const_spec
  set L := lane 128 8 (t.find startKey).w with hL
  have hθ : (cand.theta : ℝ) = 5 * (G3K.th5N : ℝ) / G3K.th5D := by
    have : (cand.theta : ℚ) = 5 * ((G3K.th5N : ℚ) / G3K.th5D) := by rw [← hth]; ring
    rw [this]; push_cast; ring
  have hε : (cand.eps : ℝ) = (G3K.epsN : ℝ) / G3K.epsD := by rw [heps]; push_cast; ring
  have hD1 : (0 : ℝ) < G3K.epsD := by exact_mod_cast hepsD
  have hD2 : (0 : ℝ) < G3K.th5D := by exact_mod_cast hthD
  unfold StopWeight Sov epsC thetaC
  rw [show cand.T + 1 = 9 from rfl, hθ, hε, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  rw [show ((L : ℝ≥0∞) / 2 ^ 40) = ENNReal.ofReal ((L : ℝ) / 2 ^ 40) by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow
      (by norm_num), ENNReal.ofReal_ofNat]]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (by positivity), div_pow, div_mul_div_comm, mul_comm, ← mul_div_assoc,
    le_div_iff₀ (by positivity)]
  have : ((L * G3K.epsD * G3K.th5D ^ 9 : ℕ) : ℝ) ≤ ((2 ^ 40 * G3K.epsN * (5 * G3K.th5N) ^ 9 : ℕ) : ℝ) := by
    exact_mod_cast hst
  push_cast at this
  nlinarith [this]

end FrogModel.Engine.G3
