module

public import FrogModel.D3.Interfaces.Closure
public import FrogModel.LemmaR.Walk
public import FrogModel.LemmaR.Planted.Awake
public import FrogModel.ZeroOne.Glue

@[expose] public section

/-!
# The depth walk on `T*` (d = 3)

Lemma 10.2 (1) of the paper and the proof of Lemma 11.5. Off the leaf `y`, a step of `T*` changes
the depth by `-1` (to the parent, `ξ.2 = 0`) or `+1` (to a child). `dW x n` is the depth change after
`n` steps: the walk from `some u` is at depth `|u| + dW x n` until the first time this is `-1`, when
it is at `y` (`walkStar_none_iff`, `length_walkStar`). The depth walk goes down with probability `3/4`:
`P(dW reaches -k) = 3^-k` (`seqLaw_hitsDown`) and `P(dW reaches k) = 1` (`seqLaw_hitsUp`), from the
first-step equations (`LemmaR.seqLaw_head_tail`), the bound `LemmaR.hitStar_le` and the bounded
solutions of the two recurrences (`rec_down`, `rec_up`). Hence `prob_reach` (`prob_reach_proof`),
and the walk from `w` reaches depth `D` with probability at least `2/3` (`one_le_reachD`).

`hitD D x` is the first time the walk from `w` is at depth `D` and `firstD D x` the vertex it is
at then; `hitD D` is a stopping time (`hitD_stop`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface

/-! ### Sets of step sequences read on a prefix -/

/-- A set of step sequences decided by the first `n` steps is measurable. -/
theorem measurableSet_of_prefix {A : Set (ℕ → Step 3)} (n : ℕ)
    (h : ∀ x x' : ℕ → Step 3, (∀ i < n, x i = x' i) → x ∈ A → x' ∈ A) : MeasurableSet A := by
  set r : (ℕ → Step 3) → (Fin n → Step 3) := fun x i => x i with hr
  have hrm : Measurable r := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hA : A = r ⁻¹' (r '' A) := by
    ext x
    refine ⟨fun hx => ⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨x', hx', hxx'⟩
    refine h x' x (fun i hi => ?_) hx'
    have := congrFun hxx' ⟨i, hi⟩
    simpa [hr] using this
  rw [hA]
  exact hrm (Set.to_countable _).measurableSet

/-! ### The depth walk -/

/-- The depth change of one step off the leaf: `-1` to the parent, `+1` to a child. -/
def inc (ξ : Step 3) : ℤ := if ξ.2 = 0 then -1 else 1

/-- The depth walk: the depth change after `n` steps. -/
def dW (x : ℕ → Step 3) : ℕ → ℤ
  | 0 => 0
  | n + 1 => dW x n + inc (x n)

/-- The depth walk reaches `-k`. -/
def HitsDown (k : ℕ) (x : ℕ → Step 3) : Prop := ∃ n, dW x n = -(k : ℤ)

/-- The depth walk reaches `k`. -/
def HitsUp (k : ℕ) (x : ℕ → Step 3) : Prop := ∃ n, dW x n = (k : ℤ)

theorem dW_succ' (x : ℕ → Step 3) (n : ℕ) :
    dW x (n + 1) = inc (x 0) + dW (fun k => x (k + 1)) n := by
  induction n with
  | zero => simp [dW]
  | succ n ih =>
    rw [dW, ih, dW]
    ring

theorem dW_congr (x x' : ℕ → Step 3) (n : ℕ) (h : ∀ i < n, x i = x' i) : dW x n = dW x' n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dW, dW, ih fun i hi => h i (by omega), h n (by omega)]

theorem inc_cases (ξ : Step 3) : (ξ.2 = 0 ∧ inc ξ = -1) ∨ (ξ.2 ≠ 0 ∧ inc ξ = 1) := by
  by_cases h : ξ.2 = 0
  · exact Or.inl ⟨h, by simp [inc, h]⟩
  · exact Or.inr ⟨h, by simp [inc, h]⟩

/-- The walk on `T*` from `some u` and the depth walk: it is at `y` exactly once `|u| + dW` has
been `-1`, and before that its depth is `|u| + dW`. -/
theorem walkStar_dW (u : Vertex 3) (x : ℕ → Step 3) (n : ℕ) :
    (walkStar (some u) x n = none ↔ ∃ i ≤ n, (u.length : ℤ) + dW x i = -1) ∧
      ∀ w, walkStar (some u) x n = some w → (w.length : ℤ) = u.length + dW x n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [walkStar, reduceCtorEq, false_iff, not_exists, not_and]
      intro i hi
      have : i = 0 := by omega
      subst this
      simp [dW]
    · intro w hw
      simp only [walkStar, Option.some.injEq] at hw
      subst hw
      simp [dW]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases hcase : walkStar (some u) x n with _ | w0
    · have hnone : walkStar (some u) x (n + 1) = none := by
        simp [walkStar, hcase, stepStar]
      refine ⟨⟨fun _ => ?_, fun _ => hnone⟩, fun w hw => by rw [hnone] at hw; cases hw⟩
      obtain ⟨i, hi, hi'⟩ := ih1.1 hcase
      exact ⟨i, by omega, hi'⟩
    · have hw0 := ih2 w0 hcase
      have hno : ∀ i ≤ n, (u.length : ℤ) + dW x i ≠ -1 := by
        intro i hi h
        have := ih1.2 ⟨i, hi, h⟩
        rw [hcase] at this
        cases this
      have hstep : walkStar (some u) x (n + 1) = stepStar (some w0) (x n) := by
        simp [walkStar, hcase]
      rcases inc_cases (x n) with ⟨hup, hinc⟩ | ⟨hdown, hinc⟩
      · cases w0 with
        | nil =>
          have hnone : walkStar (some u) x (n + 1) = none := by
            rw [hstep]; simp [stepStar, hup]
          refine ⟨⟨fun _ => ⟨n + 1, le_rfl, ?_⟩, fun _ => hnone⟩,
            fun w hw => by rw [hnone] at hw; cases hw⟩
          simp only [dW, hinc]
          simp at hw0
          omega
        | cons c w1 =>
          have hsome : walkStar (some u) x (n + 1) = some w1 := by
            rw [hstep]; simp [stepStar, hup]
          refine ⟨⟨(fun h => by rw [hsome] at h; cases h), fun hex => ?_⟩, ?_⟩
          · obtain ⟨i, hi, hi'⟩ := hex
            rcases Nat.lt_or_ge i (n + 1) with h1 | h1
            · exact absurd hi' (hno i (by omega))
            · have : i = n + 1 := by omega
              subst this
              simp only [dW, hinc] at hi'
              simp at hw0
              omega
          · intro w hw
            rw [hsome] at hw
            cases hw
            simp only [dW, hinc]
            simp at hw0
            omega
      · have hsome : walkStar (some u) x (n + 1) = some ((x n).2.pred hdown :: w0) := by
          rw [hstep]; simp [stepStar, hdown]
        refine ⟨⟨(fun h => by rw [hsome] at h; cases h), fun hex => ?_⟩, ?_⟩
        · obtain ⟨i, hi, hi'⟩ := hex
          rcases Nat.lt_or_ge i (n + 1) with h1 | h1
          · exact absurd hi' (hno i (by omega))
          · have : i = n + 1 := by omega
            subst this
            simp only [dW, hinc] at hi'
            have : (0 : ℤ) ≤ w0.length := by positivity
            omega
        · intro w hw
          rw [hsome] at hw
          cases hw
          simp only [dW, hinc, List.length_cons]
          push_cast
          omega

theorem walkStar_none_iff (u : Vertex 3) (x : ℕ → Step 3) (n : ℕ) :
    walkStar (some u) x n = none ↔ ∃ i ≤ n, (u.length : ℤ) + dW x i = -1 :=
  (walkStar_dW u x n).1

theorem length_walkStar (u : Vertex 3) (x : ℕ → Step 3) (n : ℕ) (w : Vertex 3)
    (h : walkStar (some u) x n = some w) : (w.length : ℤ) = u.length + dW x n :=
  (walkStar_dW u x n).2 w h

/-- The walk from `some u` reaches `y` iff the depth walk reaches `-(|u| + 1)`. -/
theorem exists_walkStar_none_iff (u : Vertex 3) (x : ℕ → Step 3) :
    (∃ n, walkStar (some u) x n = none) ↔ HitsDown (u.length + 1) x := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨i, -, hi⟩ := (walkStar_none_iff u x n).1 hn
    exact ⟨i, by push_cast; omega⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (walkStar_none_iff u x n).2 ⟨n, le_rfl, by push_cast at hn; omega⟩⟩

theorem measurableSet_dW_eq (n : ℕ) (z : ℤ) : MeasurableSet {x : ℕ → Step 3 | dW x n = z} :=
  measurableSet_of_prefix n fun x x' h hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [← dW_congr x x' n h]
    exact hx

theorem measurableSet_hitsDown (k : ℕ) : MeasurableSet {x : ℕ → Step 3 | HitsDown k x} := by
  have : {x : ℕ → Step 3 | HitsDown k x} = ⋃ n, {x | dW x n = -(k : ℤ)} := by
    ext x; simp [HitsDown]
  rw [this]
  exact MeasurableSet.iUnion fun n => measurableSet_dW_eq n _

theorem measurableSet_hitsUp (k : ℕ) : MeasurableSet {x : ℕ → Step 3 | HitsUp k x} := by
  have : {x : ℕ → Step 3 | HitsUp k x} = ⋃ n, {x | dW x n = (k : ℤ)} := by
    ext x; simp [HitsUp]
  rw [this]
  exact MeasurableSet.iUnion fun n => measurableSet_dW_eq n _

/-! ### First-step equations -/

theorem hitsDown_succ_iff (k : ℕ) (x : ℕ → Step 3) :
    HitsDown (k + 1) x ↔
      if (x 0).2 = 0 then HitsDown k (fun i => x (i + 1)) else HitsDown (k + 2) (fun i => x (i + 1)) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [dW] at hn; omega
    | succ n =>
      rw [dW_succ'] at hn
      rcases inc_cases (x 0) with ⟨h0, hi⟩ | ⟨h0, hi⟩
      · rw [ite_eq_left h0]; exact ⟨n, by rw [hi] at hn; push_cast at hn ⊢; omega⟩
      · rw [ite_eq_right h0]; exact ⟨n, by rw [hi] at hn; push_cast at hn ⊢; omega⟩
  · intro h
    rcases inc_cases (x 0) with ⟨h0, hi⟩ | ⟨h0, hi⟩
    · rw [ite_eq_left h0] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, by rw [dW_succ', hi, hn]; push_cast; ring⟩
    · rw [ite_eq_right h0] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, by rw [dW_succ', hi, hn]; push_cast; ring⟩

theorem hitsUp_succ_iff (k : ℕ) (x : ℕ → Step 3) :
    HitsUp (k + 1) x ↔
      if (x 0).2 = 0 then HitsUp (k + 2) (fun i => x (i + 1)) else HitsUp k (fun i => x (i + 1)) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [dW] at hn; omega
    | succ n =>
      rw [dW_succ'] at hn
      rcases inc_cases (x 0) with ⟨h0, hi⟩ | ⟨h0, hi⟩
      · rw [ite_eq_left h0]; exact ⟨n, by rw [hi] at hn; push_cast at hn ⊢; omega⟩
      · rw [ite_eq_right h0]; exact ⟨n, by rw [hi] at hn; push_cast at hn ⊢; omega⟩
  · intro h
    rcases inc_cases (x 0) with ⟨h0, hi⟩ | ⟨h0, hi⟩
    · rw [ite_eq_left h0] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, by rw [dW_succ', hi, hn]; push_cast; ring⟩
    · rw [ite_eq_right h0] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, by rw [dW_succ', hi, hn]; push_cast; ring⟩

/-- The sum over the twelve step values of `f` up or down, each of mass `1/12`. -/
theorem sum_step_ite (a b : ℝ≥0∞) :
    ∑ ξ : Step 3, LemmaR.seqLaw 3 Set.univ * (stepLaw 3 {ξ} * (if ξ.2 = 0 then a else b)) =
      12⁻¹ * (3 * a + 9 * b) := by
  simp only [measure_univ, one_mul, LemmaR.stepLaw_singleton]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_ne_zero, ite_true, ite_false]
  norm_num
  ring

theorem seqLaw_split (P : Step 3 → (ℕ → Step 3) → Prop)
    (hP : ∀ ξ, MeasurableSet {y : ℕ → Step 3 | P ξ y}) (a b : ℝ≥0∞)
    (ha : ∀ ξ : Step 3, ξ.2 = 0 → LemmaR.seqLaw 3 {y | P ξ y} = a)
    (hb : ∀ ξ : Step 3, ξ.2 ≠ 0 → LemmaR.seqLaw 3 {y | P ξ y} = b) :
    LemmaR.seqLaw 3 {x | P (x 0) (fun k => x (k + 1))} = 12⁻¹ * (3 * a + 9 * b) := by
  rw [LemmaR.seqLaw_head_tail P hP, ← sum_step_ite a b]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [measure_univ, one_mul]
  by_cases h : ξ.2 = 0
  · rw [ite_eq_left h, ha ξ h]
  · rw [ite_eq_right h, hb ξ h]

theorem seqLaw_hitsDown_succ (k : ℕ) :
    LemmaR.seqLaw 3 {x | HitsDown (k + 1) x} =
      12⁻¹ * (3 * LemmaR.seqLaw 3 {x | HitsDown k x} + 9 * LemmaR.seqLaw 3 {x | HitsDown (k + 2) x}) := by
  have hset : {x : ℕ → Step 3 | HitsDown (k + 1) x} =
      {x | (fun ξ y => if ξ.2 = 0 then HitsDown k y else HitsDown (k + 2) y) (x 0)
        (fun i => x (i + 1))} := by
    ext x; exact hitsDown_succ_iff k x
  rw [hset]
  refine seqLaw_split (fun ξ y => if ξ.2 = 0 then HitsDown k y else HitsDown (k + 2) y)
    (fun ξ => ?_) _ _ (fun ξ h => by simp [h]) (fun ξ h => by simp [h])
  by_cases h : ξ.2 = 0
  · simpa [h] using measurableSet_hitsDown k
  · simpa [h] using measurableSet_hitsDown (k + 2)

theorem seqLaw_hitsUp_succ (k : ℕ) :
    LemmaR.seqLaw 3 {x | HitsUp (k + 1) x} =
      12⁻¹ * (3 * LemmaR.seqLaw 3 {x | HitsUp (k + 2) x} + 9 * LemmaR.seqLaw 3 {x | HitsUp k x}) := by
  have hset : {x : ℕ → Step 3 | HitsUp (k + 1) x} =
      {x | (fun ξ y => if ξ.2 = 0 then HitsUp (k + 2) y else HitsUp k y) (x 0)
        (fun i => x (i + 1))} := by
    ext x; exact hitsUp_succ_iff k x
  rw [hset]
  refine seqLaw_split (fun ξ y => if ξ.2 = 0 then HitsUp (k + 2) y else HitsUp k y)
    (fun ξ => ?_) _ _ (fun ξ h => by simp [h]) (fun ξ h => by simp [h])
  by_cases h : ξ.2 = 0
  · simpa [h] using measurableSet_hitsUp (k + 2)
  · simpa [h] using measurableSet_hitsUp k

/-! ### The bounded solutions of the recurrences -/

/-- A solution of `f(k+1) = f(k)/4 + 3 f(k+2)/4` with `f 0 = 1`, `f ≥ 0` and `f 1 ≤ 1/3` is
`3^-k`. -/
theorem rec_down (f : ℕ → ℝ) (h0 : f 0 = 1) (hnn : ∀ k, 0 ≤ f k) (hle : f 1 ≤ 1 / 3)
    (hrec : ∀ k, f (k + 1) = 1 / 4 * f k + 3 / 4 * f (k + 2)) : ∀ k, f k = (1 / 3) ^ k := by
  -- Rewrite the recurrence in a more convenient form
  have hrec' : ∀ k, f (k + 2) = (4/3 : ℝ) * f (k + 1) - (1/3 : ℝ) * f k := by
    intro k
    have h := hrec k
    linarith
  -- The differences g(k) = f(k+1) - f(k) satisfy g(k+1) = g(k)/3
  have h_diff_rec : ∀ k, (f (k + 2) - f (k + 1)) = (1/3 : ℝ) * (f (k + 1) - f k) := by
    intro k
    have h := hrec' k
    linarith
  -- By induction, g(k) = 3^(-k) * (f 1 - f 0)
  have h_diff_formula : ∀ k, f (k + 1) - f k = ((1/3 : ℝ) ^ k) * (f 1 - f 0) := by
    intro k
    induction' k with k ih
    · simp [h0]
    · rw [h_diff_rec k, ih]
      ring
  -- Telescoping sum: f(k) = f(0) + Σ_{i<k} (f(i+1) - f(i))
  have h_telescope : ∀ k, f k = f 0 + ∑ i ∈ Finset.range k, (f (i + 1) - f i) := by
    intro k
    induction' k with k ih
    · simp
    · rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      ring
  -- Geometric sum formula: Σ_{i<k} r^i = (1 - r^k)/(1 - r) for r ≠ 1
  have h_geom_sum : ∀ k, ∑ i ∈ Finset.range k, ((1/3 : ℝ) ^ i) = (1 - ((1/3 : ℝ) ^ k)) / (1 - (1/3 : ℝ)) := by
    intro k
    have hx : (1/3 : ℝ) ≠ 1 := by norm_num
    rw [geom_sum_eq hx k]
    field_simp
    ring
  -- Combine to get closed form: f(k) = 3^(-k) + (3/2)*a*(1 - 3^(-k)) where a = f(1) - 1/3
  set a := f 1 - 1/3 with ha_def
  have ha_nonpos : a ≤ 0 := by linarith
  have h_closed : ∀ k, f k = ((1/3 : ℝ) ^ k) + (3/2) * a * (1 - ((1/3 : ℝ) ^ k)) := by
    intro k
    have h_sum_diff : ∑ i ∈ Finset.range k, (f (i + 1) - f i) =
        ∑ i ∈ Finset.range k, (((1/3 : ℝ) ^ i) * (f 1 - f 0)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_diff_formula i]
    rw [h_telescope k, h0, h_sum_diff]
    -- Goal: 1 + ∑ i ∈ range k, (1/3)^i * (f 1 - f 0) = (1/3)^k + (3/2)*a*(1 - (1/3)^k)
    rw [← Finset.sum_mul]
    -- Now: 1 + (∑ i ∈ range k, (1/3)^i) * (f 1 - f 0) = ...
    rw [h_geom_sum k]
    -- Now: 1 + ((1 - (1/3)^k) / (1 - 1/3)) * (f 1 - f 0) = ...
    rw [h0]
    -- Now: 1 + ((1 - (1/3)^k) / (1 - 1/3)) * (f 1 - 1) = ...
    dsimp [a]
    -- a = f 1 - 1/3
    field_simp
    ring
  -- Now we have two cases: either a = 0 (i.e., f(1) = 1/3) or a < 0
  by_cases ha_zero : a = 0
  · -- If a = 0, then f(k) = 3^(-k) = (1/3)^k
    intro k
    rw [h_closed k, ha_zero]
    simp
  · -- If a < 0, we derive a contradiction with hnn (nonnegativity)
    have ha_neg : a < 0 := by
      by_contra! h
      exact ha_zero (by linarith)
    -- Pick k large enough so that (1/3)^k < -(3/4)*a
    have h_target_pos : 0 < -(3/4) * a := by
      have : 0 < -a := by linarith
      nlinarith
    have h_third_lt_one : (1/3 : ℝ) < 1 := by norm_num
    obtain ⟨k1, hk1⟩ := exists_pow_lt_of_lt_one h_target_pos h_third_lt_one
    -- Take k = max k1 1 to ensure both k ≥ k1 and k ≥ 1
    set k := max k1 1 with hk_def
    have hk_ge_k1 : k1 ≤ k := Nat.le_max_left _ _
    have hk_ge_one : 1 ≤ k := Nat.le_max_right _ _
    -- Since 0 < 1/3 < 1, larger exponent gives smaller value
    have h_third_nonneg : 0 ≤ (1/3 : ℝ) := by norm_num
    have h_third_le_one : (1/3 : ℝ) ≤ 1 := by norm_num
    have h_pow_k_le_pow_k1 : ((1/3 : ℝ) ^ k) ≤ ((1/3 : ℝ) ^ k1) :=
      pow_le_pow_of_le_one h_third_nonneg h_third_le_one hk_ge_k1
    have h_rk_small : ((1/3 : ℝ) ^ k) < -(3/4) * a := by
      linarith
    -- Also (1/3)^k ≤ (1/3)^1 = 1/3, so 1 - (1/3)^k ≥ 2/3 ≥ 1/2
    have h_pow_k_le_third : ((1/3 : ℝ) ^ k) ≤ (1/3 : ℝ) := by
      have := pow_le_pow_of_le_one h_third_nonneg h_third_le_one hk_ge_one
      simpa [pow_one] using this
    have h_one_minus_rk_ge_half : 1/2 ≤ 1 - ((1/3 : ℝ) ^ k) := by
      have : ((1/3 : ℝ) ^ k) ≤ 1/2 := by
        -- (1/3)^k ≤ 1/3 ≤ 1/2
        linarith
      linarith
    -- Now compute f(k) and show it's negative
    have hfk_neg : f k < 0 := by
      rw [h_closed k]
      have h_nonneg_pow : 0 ≤ ((1/3 : ℝ) ^ k) := pow_nonneg (by norm_num) _
      have h_nonpos_coeff : (3/2) * a ≤ 0 := by
        nlinarith
      have h_one_minus_nonneg : 0 ≤ 1 - ((1/3 : ℝ) ^ k) := by
        have : ((1/3 : ℝ) ^ k) ≤ 1 := pow_le_one₀ h_third_nonneg h_third_le_one
        linarith
      -- (3/2)*a*(1 - r^k) ≤ (3/2)*a*(1/2) because a < 0 and 1 - r^k ≥ 1/2
      have h_bound : (3/2) * a * (1 - ((1/3 : ℝ) ^ k)) ≤ (3/2) * a * (1/2) := by
        nlinarith
      -- So f(k) = r^k + (3/2)*a*(1 - r^k) ≤ r^k + (3/4)*a < -(3/4)*a + (3/4)*a = 0
      nlinarith
    -- This contradicts the nonnegativity assumption
    have hfk_nonneg : 0 ≤ f k := hnn k
    linarith

/-- A solution of `f(k+1) = f(k+2)/4 + 3 f(k)/4` with `f 0 = 1` and `0 ≤ f ≤ 1` is `1`. -/
theorem rec_up (f : ℕ → ℝ) (h0 : f 0 = 1) (hnn : ∀ k, 0 ≤ f k) (hle : ∀ k, f k ≤ 1)
    (hrec : ∀ k, f (k + 1) = 1 / 4 * f (k + 2) + 3 / 4 * f k) : ∀ k, f k = 1 := by
  -- Lemma: 1 ≤ 3^n for all n
  have h_one_le_pow_three : ∀ n : ℕ, 1 ≤ (3 : ℝ) ^ n := by
    intro n
    induction' n with m ih
    · norm_num
    · rw [pow_succ]
      have h3 : (1 : ℝ) ≤ 3 := by norm_num
      nlinarith
  -- Rearranged recurrence: f(k+2) = 4*f(k+1) - 3*f(k)
  have hrec' : ∀ k, f (k + 2) = 4 * f (k + 1) - 3 * f k := by
    intro k
    have h := hrec k
    linarith
  -- Differences g(k) = f(k+1) - f(k)
  set g := fun k : ℕ => f (k + 1) - f k with hg_def
  have hg_rec : ∀ k, g (k + 1) = (3 : ℝ) * g k := by
    intro k
    dsimp [g]
    rw [hrec' k]
    ring
  have hg_pow : ∀ k, g k = ((3 : ℝ) ^ k) * g 0 := by
    intro k
    induction' k with k ih
    · dsimp [g]
      ring
    · rw [hg_rec k, ih, pow_succ]
      ring
  -- Telescoping sum: ∑_{i<k} g i = f k - f 0
  have hf_sum : ∀ k, ∑ i ∈ Finset.range k, g i = f k - f 0 := by
    intro k
    induction' k with k ih
    · simp
    · rw [Finset.sum_range_succ, ih]
      dsimp [g]
      ring
  -- Closed form for f(k)
  have hf_formula : ∀ k, f k = 1 + g 0 * (((3 : ℝ) ^ k - 1) / 2) := by
    intro k
    have hsum_eq : f k = 1 + ∑ i ∈ Finset.range k, g i := by
      rw [hf_sum k, h0]
      ring
    rw [hsum_eq]
    rw [show (∑ i ∈ Finset.range k, g i) = g 0 * (∑ i ∈ Finset.range k, ((3 : ℝ) ^ i)) by
      calc
        (∑ i ∈ Finset.range k, g i) = (∑ i ∈ Finset.range k, (((3 : ℝ) ^ i) * g 0)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hg_pow i]
        _ = (∑ i ∈ Finset.range k, ((3 : ℝ) ^ i)) * g 0 := by
          simp [Finset.sum_mul]
        _ = g 0 * (∑ i ∈ Finset.range k, ((3 : ℝ) ^ i)) := by ring
      ]
    have hgeom := geom_sum_mul (3 : ℝ) k
    have hsum : (∑ i ∈ Finset.range k, ((3 : ℝ) ^ i)) = (((3 : ℝ) ^ k - 1) / 2) := by
      field_simp
      linarith
    rw [hsum]
  -- Now show g 0 = 0
  have hg0_eq_zero : g 0 = 0 := by
    by_contra! h
    have h_cases : g 0 < 0 ∨ 0 < g 0 := lt_or_gt_of_ne h
    rcases h_cases with (hneg | hpos)
    · -- Case g 0 < 0: then f 1 < 1, find k with f k < 0, contradiction
      have hc_pos : 0 < -g 0 := by linarith
      have hbound := pow_unbounded_of_one_lt (1 / (-g 0)) (by norm_num : 1 < (3 : ℝ))
      rcases hbound with ⟨n, hn⟩
      -- hn: 1 / (-g 0) < (3 : ℝ) ^ n
      have hineq : (3 : ℝ) ^ n ≤ ((3 : ℝ) ^ (n + 1) - 1) / 2 := by
        have h_pow_succ : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by ring
        rw [h_pow_succ]
        have h_one_le : 1 ≤ (3 : ℝ) ^ n := h_one_le_pow_three n
        nlinarith
      have h_combined : 1 / (-g 0) < ((3 : ℝ) ^ (n + 1) - 1) / 2 := by
        linarith
      have hfn1_neg : f (n + 1) < 0 := by
        rw [hf_formula (n + 1)]
        have h_mul_gt_one : 1 < (-g 0) * (((3 : ℝ) ^ (n + 1) - 1) / 2) := by
          have htemp := mul_lt_mul_of_pos_left h_combined hc_pos
          -- htemp: (-g 0) * (1 / (-g 0)) < (-g 0) * ((3^(n+1) - 1)/2)
          have hleft : (-g 0) * (1 / (-g 0)) = (1 : ℝ) := by
            field_simp [hc_pos.ne.symm]
          rw [hleft] at htemp
          -- htemp: 1 < (-g 0) * ((3^(n+1) - 1)/2)
          exact htemp
        linarith
      have h_nonneg := hnn (n + 1)
      linarith
    · -- Case g 0 > 0: then f 1 > 1, contradicts hle 1
      have h1gt1 : f 1 > 1 := by
        dsimp [g] at hpos
        rw [h0] at hpos
        linarith
      have h1le1 := hle 1
      linarith
  -- Now g 0 = 0, so f k = 1 for all k
  intro k
  rw [hf_formula k, hg0_eq_zero]
  simp

/-! ### Hitting probabilities -/

theorem seqLaw_hitsDown_le (k : ℕ) :
    LemmaR.seqLaw 3 {x | HitsDown (k + 1) x} ≤ (3⁻¹ : ℝ≥0∞) ^ (k + 1) := by
  have h := LemmaR.hitStar_le (d := 3) (List.replicate k 0)
  have hset : {x : ℕ → Step 3 | ∃ n, walkStar (some (List.replicate k 0)) x n = none} =
      {x | HitsDown (k + 1) x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [exists_walkStar_none_iff, List.length_replicate]
  rw [hset] at h
  simpa using h

/-- **The depth walk reaches `-k` with probability `3^-k`.** -/
theorem seqLaw_hitsDown (k : ℕ) : LemmaR.seqLaw 3 {x | HitsDown k x} = (3⁻¹ : ℝ≥0∞) ^ k := by
  set f : ℕ → ℝ := fun k => (LemmaR.seqLaw 3 {x | HitsDown k x}).toReal with hf
  have hfin : ∀ k, LemmaR.seqLaw 3 {x | HitsDown k x} ≠ ⊤ := fun k => measure_ne_top _ _
  have h0 : f 0 = 1 := by
    have : {x : ℕ → Step 3 | HitsDown 0 x} = Set.univ := by
      ext x; exact ⟨fun _ => trivial, fun _ => ⟨0, by simp [dW]⟩⟩
    simp [hf, this]
  have hle1 : f 1 ≤ 1 / 3 := by
    have h := seqLaw_hitsDown_le 0
    have h' := ENNReal.toReal_mono (by simp) h
    simpa [hf] using h'
  have hrec : ∀ k, f (k + 1) = 1 / 4 * f k + 3 / 4 * f (k + 2) := by
    intro k
    simp only [hf]
    rw [seqLaw_hitsDown_succ, ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) (hfin _))
      (ENNReal.mul_ne_top (by norm_num) (hfin _)), ENNReal.toReal_mul, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    ring
  have hsol := rec_down f h0 (fun k => ENNReal.toReal_nonneg) hle1 hrec k
  rw [← ENNReal.ofReal_toReal (hfin k)]
  change ENNReal.ofReal (f k) = _
  rw [hsol, ENNReal.ofReal_pow (by norm_num)]
  simp

/-- **The depth walk reaches every `k ≥ 0` almost surely.** -/
theorem seqLaw_hitsUp (k : ℕ) : LemmaR.seqLaw 3 {x | HitsUp k x} = 1 := by
  set f : ℕ → ℝ := fun k => (LemmaR.seqLaw 3 {x | HitsUp k x}).toReal with hf
  have hfin : ∀ k, LemmaR.seqLaw 3 {x | HitsUp k x} ≠ ⊤ := fun k => measure_ne_top _ _
  have h0 : f 0 = 1 := by
    have : {x : ℕ → Step 3 | HitsUp 0 x} = Set.univ := by
      ext x; exact ⟨fun _ => trivial, fun _ => ⟨0, by simp [dW]⟩⟩
    simp [hf, this]
  have hle : ∀ k, f k ≤ 1 := fun k => by
    simp only [hf]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hrec : ∀ k, f (k + 1) = 1 / 4 * f (k + 2) + 3 / 4 * f k := by
    intro k
    simp only [hf]
    rw [seqLaw_hitsUp_succ, ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) (hfin _))
      (ENNReal.mul_ne_top (by norm_num) (hfin _)), ENNReal.toReal_mul, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    ring
  have hsol := rec_up f h0 (fun k => ENNReal.toReal_nonneg) hle hrec k
  rw [← ENNReal.ofReal_toReal (hfin k)]
  change ENNReal.ofReal (f k) = _
  rw [hsol, ENNReal.ofReal_one]

/-- The walk on `T*` from `some u` reaches `y` with probability `3^-(|u| + 1)`. -/
theorem seqLaw_reach (u : Vertex 3) :
    LemmaR.seqLaw 3 {x | ∃ n, walkStar (some u) x n = none} = (3⁻¹ : ℝ≥0∞) ^ (u.length + 1) := by
  have : {x : ℕ → Step 3 | ∃ n, walkStar (some u) x n = none} = {x | HitsDown (u.length + 1) x} := by
    ext x; exact exists_walkStar_none_iff u x
  rw [this, seqLaw_hitsDown]

theorem pathMeasure_map_eval (φ : PFrog) : pathMeasure.map (fun π => π φ) = LemmaR.seqLaw 3 :=
  Measure.infinitePi_map_eval _ φ

/-- **`prob_reach`** (Lemma 10.2 (1)), proved. -/
theorem prob_reach_proof : prob_reach := by
  intro φ
  have hm : Measurable fun π : PFrog → ℕ → Step 3 => π φ := measurable_pi_apply φ
  have hs : MeasurableSet {x : ℕ → Step 3 | ∃ n, walkStar (some (frogStart φ)) x n = none} :=
    LemmaR.measurableSet_hitStar (frogStart φ)
  have hpre : {π : PFrog → ℕ → Step 3 | ∃ n, pos π φ n = none} =
      (fun π => π φ) ⁻¹' {x | ∃ n, walkStar (some (frogStart φ)) x n = none} := rfl
  rw [hpre, ← Measure.map_apply hm hs, pathMeasure_map_eval, seqLaw_reach]
  cases φ <;> rfl

/-! ### Reaching depth `D` from `w` -/

/-- The walk from `w` reaches depth `D` (before `y`, which is absorbing). -/
abbrev ReachD (D : ℕ) (x : ℕ → Step 3) : Prop :=
  ∃ n v, walkStar (some []) x n = some v ∧ v.length = D

theorem reachD_or_hitsDown (D : ℕ) (x : ℕ → Step 3) (h : HitsUp D x) :
    ReachD D x ∨ HitsDown 1 x := by
  obtain ⟨n, hn⟩ := h
  rcases hw : walkStar (some []) x n with _ | v
  · obtain ⟨i, -, hi⟩ := (walkStar_none_iff [] x n).1 hw
    exact Or.inr ⟨i, by simpa using hi⟩
  · have := length_walkStar [] x n v hw
    exact Or.inl ⟨n, v, hw, by simp at this; omega⟩

theorem measurableSet_atD (n D : ℕ) :
    MeasurableSet {x : ℕ → Step 3 | ∃ v, walkStar (some []) x n = some v ∧ v.length = D} := by
  have : {x : ℕ → Step 3 | ∃ v, walkStar (some []) x n = some v ∧ v.length = D} =
      ⋃ v ∈ {v : Vertex 3 | v.length = D}, {x | walkStar (some []) x n = some v} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩, fun ⟨v, h2, h1⟩ => ⟨v, h1, h2⟩⟩
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun v _ =>
    measurableSet_walkStar_eq 3 [] n (some v)

theorem measurableSet_reachD (D : ℕ) : MeasurableSet {x : ℕ → Step 3 | ReachD D x} := by
  have : {x : ℕ → Step 3 | ReachD D x} =
      ⋃ n, {x | ∃ v, walkStar (some []) x n = some v ∧ v.length = D} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [this]
  exact MeasurableSet.iUnion fun n => measurableSet_atD n D

/-- **The walk from `w` reaches depth `D` with probability at least `2/3`**: `1 ≤ P + 1/3`. -/
theorem one_le_reachD (D : ℕ) : 1 ≤ LemmaR.seqLaw 3 {x | ReachD D x} + 3⁻¹ := by
  calc (1 : ℝ≥0∞) = LemmaR.seqLaw 3 {x | HitsUp D x} := (seqLaw_hitsUp D).symm
    _ ≤ LemmaR.seqLaw 3 ({x | ReachD D x} ∪ {x | HitsDown 1 x}) :=
        measure_mono fun x hx => reachD_or_hitsDown D x hx
    _ ≤ LemmaR.seqLaw 3 {x | ReachD D x} + LemmaR.seqLaw 3 {x | HitsDown 1 x} := measure_union_le _ _
    _ = LemmaR.seqLaw 3 {x | ReachD D x} + 3⁻¹ := by rw [seqLaw_hitsDown]; simp

/-! ### The first time at depth `D` -/

open Classical in
/-- The first time the walk from `w` is at depth `D`, `⊤` if never. -/
noncomputable def hitD (D : ℕ) (x : ℕ → Step 3) : ℕ∞ :=
  if h : ReachD D x then ((Nat.find h : ℕ) : ℕ∞) else ⊤

open Classical in
/-- The first vertex at depth `D` on the walk from `w`, `none` if never. -/
noncomputable def firstD (D : ℕ) (x : ℕ → Step 3) : Option (Vertex 3) :=
  if h : ReachD D x then walkStar (some []) x (Nat.find h) else none

theorem firstD_spec (D : ℕ) (x : ℕ → Step 3) (v : Vertex 3) (h : firstD D x = some v) :
    ∃ n : ℕ, hitD D x = n ∧ walkStar (some []) x n = some v ∧ v.length = D := by
  classical
  by_cases hr : ReachD D x
  · simp only [firstD, hr, dite_true] at h
    refine ⟨Nat.find hr, by simp [hitD, hr], h, ?_⟩
    obtain ⟨w, hw, hwD⟩ := Nat.find_spec hr
    rw [h] at hw
    cases hw
    exact hwD
  · simp [firstD, hr] at h

theorem firstD_eq_none_iff (D : ℕ) (x : ℕ → Step 3) : firstD D x = none ↔ ¬ ReachD D x := by
  classical
  by_cases hr : ReachD D x
  · obtain ⟨w, hw, -⟩ := Nat.find_spec hr
    simp [firstD, hr, hw]
  · simp [firstD, hr]

theorem hitD_eq_iff (D : ℕ) (x : ℕ → Step 3) (k : ℕ) :
    hitD D x = k ↔ (∃ v, walkStar (some []) x k = some v ∧ v.length = D) ∧
      ∀ i < k, ¬ ∃ v, walkStar (some []) x i = some v ∧ v.length = D := by
  classical
  by_cases hr : ReachD D x
  · simp only [hitD, hr, dite_true, Nat.cast_inj]
    exact Nat.find_eq_iff hr
  · simp only [hitD, hr, dite_false, ENat.top_ne_natCast, false_iff, not_and]
    intro h1
    exact absurd ⟨k, h1⟩ hr

/-- `hitD D` is a stopping time. -/
theorem hitD_stop (D : ℕ) (a a' : ℕ → Step 3) (k : ℕ) (h : hitD D a = k)
    (ha : ∀ i < k, a i = a' i) : hitD D a' = k := by
  have hcongr : ∀ n ≤ k, walkStar (some []) a n = walkStar (some []) a' n := fun n hn =>
    ZeroOne.walkStar_prefix (some []) a a' n fun i hi => ha i (by omega)
  rw [hitD_eq_iff] at h ⊢
  refine ⟨?_, fun i hi => ?_⟩
  · rw [← hcongr k le_rfl]; exact h.1
  · rw [← hcongr i hi.le]; exact h.2 i hi

theorem measurable_hitD (D : ℕ) : Measurable (hitD D) := by
  classical
  refine measurable_to_countable' fun k => ?_
  induction k using ENat.recTopCoe with
  | top =>
    have : hitD D ⁻¹' {⊤} = {x | ReachD D x}ᶜ := by
      ext x
      by_cases h : ReachD D x <;> simp [hitD, h]
    rw [this]
    exact (measurableSet_reachD D).compl
  | coe k =>
    have : hitD D ⁻¹' {(k : ℕ∞)} =
        {x | ∃ v, walkStar (some []) x k = some v ∧ v.length = D} ∩
          ⋂ i ∈ Finset.range k, {x | ∃ v, walkStar (some []) x i = some v ∧ v.length = D}ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
        Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
      exact hitD_eq_iff D x k
    rw [this]
    exact (measurableSet_atD k D).inter
      (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ => (measurableSet_atD i D).compl)

theorem firstD_eq_some_iff (D : ℕ) (x : ℕ → Step 3) (v : Vertex 3) :
    firstD D x = some v ↔ ∃ k : ℕ, hitD D x = k ∧ walkStar (some []) x k = some v := by
  classical
  constructor
  · intro h
    obtain ⟨n, hn, hw, -⟩ := firstD_spec D x v h
    exact ⟨n, hn, hw⟩
  · rintro ⟨k, hk, hw⟩
    by_cases hr : ReachD D x
    · simp only [hitD, hr, dite_true, Nat.cast_inj] at hk
      simp only [firstD, hr, dite_true, hk, hw]
    · simp [hitD, hr] at hk

theorem measurable_firstD (D : ℕ) : Measurable (firstD D) := by
  classical
  refine measurable_to_countable' fun o => ?_
  cases o with
  | none =>
    have : firstD D ⁻¹' {none} = {x | ReachD D x}ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
      exact firstD_eq_none_iff D x
    rw [this]
    exact (measurableSet_reachD D).compl
  | some v =>
    have : firstD D ⁻¹' {some v} =
        ⋃ k : ℕ, (hitD D ⁻¹' {(k : ℕ∞)}) ∩ {x | walkStar (some []) x k = some v} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
      exact firstD_eq_some_iff D x v
    rw [this]
    exact MeasurableSet.iUnion fun k =>
      (measurable_hitD D (measurableSet_singleton _)).inter (measurableSet_walkStar_eq 3 [] k _)

/-- `firstD` is `some` iff the walk reaches depth `D`. -/
theorem firstD_isSome_iff (D : ℕ) (x : ℕ → Step 3) : (firstD D x).isSome ↔ ReachD D x := by
  rw [← not_iff_not, Option.not_isSome_iff_eq_none, firstD_eq_none_iff]

end FrogModel.D3.LaneA
