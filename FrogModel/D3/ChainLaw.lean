module

public import FrogModel.Engine.Markov

@[expose] public section

/-!
# The law of the end of a driven chain, from a solution and a time bound

The tool behind the proof of Lemma 13.2 of the paper, in which one step of the chain is one read. A
chain driven by i.i.d. inputs (`Engine.traj`) on a countable state space, with an absorbing set of
ends `E` and an outcome `o` at the end. If a family `U b` (the candidate probability to end with
outcome `b`) is a supersolution of the first-step system on a closed set of states `G`, sums to one
over the finite set of outcomes, and is the indicator of `o = b` at the ends, and if a time bound
`T` decreases by one on average at each step outside `E`, then the chain ends almost surely and
ends with outcome `b` with probability exactly `U b x`. The probability is the least solution
(`Engine.measure_exists_traj_eq_least`), at most `U b` (`LinSys.least_le_of_super`); the expected
time is at most `T` (`Engine.lintegral_tsum_traj_eq_least`), so the probabilities sum to one, as
the `U b` do.
-/

open MeasureTheory ProbabilityTheory FrogModel
open scoped ENNReal

theorem FrogModel.D3.measurableSet_traj_eq {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]
    (f : X → Ξ → X) (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (x : X) (n : ℕ) (y : X) :
    MeasurableSet {w : ℕ → Ξ | FrogModel.Engine.traj f x w n = y} :=
  FrogModel.Engine.measurableSet_traj_eq f hf x n y

/-- Termwise smaller with the same finite total: equal. -/
theorem FrogModel.D3.eq_of_le_of_sum (s : Finset ℕ) (x y : ℕ → ℝ≥0∞) (hxy : ∀ b ∈ s, x b ≤ y b)
    (hy : ∑ b ∈ s, y b ≠ ⊤) (hsum : ∑ b ∈ s, y b ≤ ∑ b ∈ s, x b) : ∀ b ∈ s, x b = y b := by
  -- Each y b is finite (sum is finite, so each term is)
  have hy_fin_lt : ∀ b ∈ s, y b < ⊤ := by
    have hsum_lt : ∑ b ∈ s, y b < ⊤ := lt_top_iff_ne_top.mpr hy
    exact (ENNReal.sum_lt_top.mp hsum_lt)
  -- Each x b is finite because x b ≤ y b < ⊤
  have hx_fin_lt : ∀ b ∈ s, x b < ⊤ := by
    intro b hb
    exact lt_of_le_of_lt (hxy b hb) (hy_fin_lt b hb)
  have hy_ne_top : ∀ b ∈ s, y b ≠ ⊤ := fun b hb => ne_of_lt (hy_fin_lt b hb)
  have hx_ne_top : ∀ b ∈ s, x b ≠ ⊤ := fun b hb => ne_of_lt (hx_fin_lt b hb)
  -- Sum of x is also finite (all terms finite, Finset sum)
  have hsumx_lt : ∑ b ∈ s, x b < ⊤ := by
    rwa [ENNReal.sum_lt_top]
  have hsumy_lt : ∑ b ∈ s, y b < ⊤ := by
    have : ∑ b ∈ s, y b ≠ ⊤ := hy
    rwa [lt_top_iff_ne_top]
  -- From hxy we also have ∑ x ≤ ∑ y, so together with hsum we get equality
  have hsum_le : ∑ b ∈ s, x b ≤ ∑ b ∈ s, y b :=
    Finset.sum_le_sum fun b hb => hxy b hb
  have hsum_eq : ∑ b ∈ s, x b = ∑ b ∈ s, y b :=
    le_antisymm hsum_le hsum
  -- Convert to ℝ via toReal, use Finset.sum_eq_sum_iff_of_le in ℝ
  have hsum_real_eq : (∑ b ∈ s, x b).toReal = (∑ b ∈ s, y b).toReal := by
    rw [hsum_eq]
  have hx_toReal_eq : (∑ b ∈ s, x b).toReal = ∑ b ∈ s, (x b).toReal :=
    ENNReal.toReal_sum hx_ne_top
  have hy_toReal_eq : (∑ b ∈ s, y b).toReal = ∑ b ∈ s, (y b).toReal :=
    ENNReal.toReal_sum hy_ne_top
  rw [hx_toReal_eq, hy_toReal_eq] at hsum_real_eq
  -- In ℝ, x b ≤ y b gives (x b).toReal ≤ (y b).toReal
  have hxy_real : ∀ b ∈ s, (x b).toReal ≤ (y b).toReal := by
    intro b hb
    have h := (ENNReal.toReal_le_toReal (hx_ne_top b hb) (hy_ne_top b hb)).mpr (hxy b hb)
    exact h
  -- Finset.sum_eq_sum_iff_of_le in ℝ (which is an OrderedCancelAddMonoid)
  have h_eq_real : ∀ b ∈ s, (x b).toReal = (y b).toReal :=
    ((Finset.sum_eq_sum_iff_of_le hxy_real).mp hsum_real_eq)
  -- Convert back to ENNReal
  intro b hb
  have hx_eq_y_real := h_eq_real b hb
  exact ((ENNReal.toReal_eq_toReal_iff' (hx_ne_top b hb) (hy_ne_top b hb)).mp hx_eq_y_real)

/-- **Finite expected time before a set: the set is reached almost surely.** -/
theorem FrogModel.D3.ae_exists_traj_mem {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]
    (f : X → Ξ → X) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (D : Set X) (x : X)
    (h : ∫⁻ w, ∑' k, Dᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (FrogModel.Engine.traj f x w k) ∂(FrogModel.Engine.iidMeasure ν) ≠ ⊤) :
    ∀ᵐ w ∂(FrogModel.Engine.iidMeasure ν), ∃ k, FrogModel.Engine.traj f x w k ∈ D := by
  classical
    let μ := FrogModel.Engine.iidMeasure ν
    have : IsProbabilityMeasure μ := by
      dsimp [μ, FrogModel.Engine.iidMeasure]
      infer_instance
    let F : (ℕ → Ξ) → ℝ≥0∞ := fun w =>
      ∑' k, Dᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (FrogModel.Engine.traj f x w k)
    have hF_meas : Measurable F := by
      dsimp [F]
      refine Measurable.tsum ?_
      intro k
      have h_term_eq : (fun (w : ℕ → Ξ) => Dᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (FrogModel.Engine.traj f x w k)) =
          (fun w => ∑' (y : X), (Dᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y) *
            ({ω | FrogModel.Engine.traj f x ω k = y}.indicator (fun _ => (1 : ℝ≥0∞)) w)) := by
        ext w
        let z := FrogModel.Engine.traj f x w k
        have hz : z = FrogModel.Engine.traj f x w k := rfl
        have h_single : ∀ (y : X), y ≠ z →
            (Dᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y) *
            ({ω | FrogModel.Engine.traj f x ω k = y}.indicator (fun _ => (1 : ℝ≥0∞)) w) = 0 := by
          intro y hy_ne
          have h_not_eq : FrogModel.Engine.traj f x w k ≠ y := by
            intro heq; apply hy_ne; rw [← heq, hz]
          have h_indicator : ({ω | FrogModel.Engine.traj f x ω k = y}.indicator (fun _ => (1 : ℝ≥0∞)) w) = 0 := by
            simp [Set.indicator, h_not_eq]
          simp [h_indicator]
        have h_tsum := tsum_eq_single (L := SummationFilter.unconditional X) z h_single
        simp [Set.indicator]
      rw [h_term_eq]
      refine Measurable.tsum ?_
      intro y
      refine Measurable.mul ?_ ?_
      · -- constant function
        exact measurable_const
      · -- indicator of measurable set
        refine Measurable.indicator measurable_const ?_
        exact FrogModel.D3.measurableSet_traj_eq f hf x k (y : X)
    have hF_ae_lt_top : ∀ᵐ w ∂μ, F w < ⊤ := by
      refine MeasureTheory.ae_lt_top hF_meas h
    have hF_ae_ne_top : μ {ω : ℕ → Ξ | F ω = ⊤} = 0 := by
      have h := (MeasureTheory.ae_iff (μ := μ) (p := fun w => F w < ⊤)).mp hF_ae_lt_top
      simpa [not_lt] using h
    have hN_meas : MeasurableSet {w : ℕ → Ξ | ∀ k, FrogModel.Engine.traj f x w k ∉ D} := by
      have h_union : {w : ℕ → Ξ | ∀ k, FrogModel.Engine.traj f x w k ∉ D} =
          (⋃ k, {w : ℕ → Ξ | FrogModel.Engine.traj f x w k ∈ D})ᶜ := by
        ext w; simp
      rw [h_union]
      refine MeasurableSet.compl ?_
      refine MeasurableSet.iUnion ?_
      intro k
      have h_set_eq : {w : ℕ → Ξ | FrogModel.Engine.traj f x w k ∈ D} =
          ⋃ y ∈ D, {w : ℕ → Ξ | FrogModel.Engine.traj f x w k = y} := by
        ext ω
        simp
      rw [h_set_eq]
      refine MeasurableSet.biUnion (Set.countable_univ.mono (by simp)) ?_
      intro y hy
      exact FrogModel.D3.measurableSet_traj_eq f hf x k y
    have hN_null : μ {w : ℕ → Ξ | ∀ k, FrogModel.Engine.traj f x w k ∉ D} = 0 := by
      have h_subset : {w : ℕ → Ξ | ∀ k, FrogModel.Engine.traj f x w k ∉ D} ⊆ {w : ℕ → Ξ | F w = ⊤} := by
        intro w hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        have h_all_one : ∀ k, Dᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (FrogModel.Engine.traj f x w k) = 1 := by
          intro k
          have h_not_mem : FrogModel.Engine.traj f x w k ∉ D := hω k
          simp [Set.indicator, h_not_mem]
        dsimp [F]
        calc
          ∑' k, Dᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (FrogModel.Engine.traj f x w k)
              = ∑' k, (1 : ℝ≥0∞) := by
            refine tsum_congr (fun k => ?_)
            simp [h_all_one k]
          _ = ⊤ := by simp
      exact measure_mono_null h_subset hF_ae_ne_top
    have h_ae_not_N : ∀ᵐ w ∂μ, ¬(∀ k, FrogModel.Engine.traj f x w k ∉ D) := by
      rw [MeasureTheory.ae_iff]
      simpa [not_not] using hN_null
    filter_upwards [h_ae_not_N] with w hw
    push Not at hw
    exact hw

namespace FrogModel.D3

variable {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]

omit [MeasurableSpace Ξ] [Countable X] in
/-- Once in an absorbing set, the chain stays at the same state. -/
theorem traj_absorb (f : X → Ξ → X) (E : Set X) (hE : ∀ x ∈ E, ∀ ξ, f x ξ = x) (x : X)
    (w : ℕ → Ξ) (j t : ℕ) (hj : Engine.traj f x w j ∈ E) (ht : j ≤ t) :
    Engine.traj f x w t = Engine.traj f x w j := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t _ ih =>
    change f (Engine.traj f x w t) (w t) = _
    rw [ih, hE _ hj]

omit [MeasurableSpace Ξ] [Countable X] in
theorem traj_mem_closed (f : X → Ξ → X) (G : Set X) (hG : ∀ x ∈ G, ∀ ξ, f x ξ ∈ G) (x : X)
    (hx : x ∈ G) (w : ℕ → Ξ) (t : ℕ) : Engine.traj f x w t ∈ G := by
  induction t with
  | zero => exact hx
  | succ t ih => exact hG _ ih _

/-- The probability to end with outcome `b` is the least solution of the first-step system. -/
theorem measure_end_eq_least' (f : X → Ξ → X) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (E : Set X) (hE : ∀ x ∈ E, ∀ ξ, f x ξ = x)
    (o : X → ℕ) (b : ℕ) (x : X) (hx : x ∉ E) :
    Engine.iidMeasure ν {w | ∃ t, Engine.traj f x w t ∈ E ∧ o (Engine.traj f x w t) = b} =
      LinSys.least (Engine.fkKernel f (fun _ _ => 1) ν)
        (fun y => ν {ξ | y ∉ E ∧ f y ξ ∈ E ∧ o (f y ξ) = b}) x := by
  classical
  have hmeas : ∀ y, MeasurableSet {ξ | y ∉ E ∧ f y ξ ∈ E ∧ o (f y ξ) = b} := by
    intro y
    have : {ξ | y ∉ E ∧ f y ξ ∈ E ∧ o (f y ξ) = b} =
        ⋃ z ∈ {z : X | y ∉ E ∧ z ∈ E ∧ o z = b}, {ξ | f y ξ = z} := by
      ext ξ
      simp
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun z _ => hf y z
  rw [← Engine.measure_exists_traj_eq_least f ν hf
    (fun y => {ξ | y ∉ E ∧ f y ξ ∈ E ∧ o (f y ξ) = b}) hmeas x]
  · congr 1
    ext w
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, htE, hto⟩
      have hex : ∃ t, Engine.traj f x w t ∈ E := ⟨t, htE⟩
      set t0 := Nat.find hex
      have h0 : Engine.traj f x w t0 ∈ E := Nat.find_spec hex
      have hmin : ∀ s < t0, Engine.traj f x w s ∉ E := fun s hs => Nat.find_min hex hs
      have hle : t0 ≤ t := Nat.find_min' hex htE
      have heq := traj_absorb f E hE x w t0 t h0 hle
      cases ht0' : t0 with
      | zero =>
        rw [ht0'] at h0
        exact (hx h0).elim
      | succ s =>
        refine ⟨s, hmin s (by omega), ?_, ?_⟩
        · rw [ht0'] at h0
          exact h0
        · rw [heq, ht0'] at hto
          exact hto
    · rintro ⟨t, -, htE, hto⟩
      exact ⟨t + 1, htE, hto⟩
  · intro w j k hj hk
    by_contra hne
    have key : ∀ j k, j < k → w j ∈ {ξ | Engine.traj f x w j ∉ E ∧
        f (Engine.traj f x w j) ξ ∈ E ∧ o (f (Engine.traj f x w j) ξ) = b} →
        w k ∈ {ξ | Engine.traj f x w k ∉ E ∧
        f (Engine.traj f x w k) ξ ∈ E ∧ o (f (Engine.traj f x w k) ξ) = b} → False := by
      intro j k hjk hj hk
      have h1 : Engine.traj f x w (j + 1) ∈ E := hj.2.1
      have := traj_absorb f E hE x w (j + 1) k h1 hjk
      exact hk.1 (by rw [this]; exact h1)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key j k h hj hk
    · exact key k j h hk hj

/-- **The law of the end of a chain.** See the module docstring. -/
theorem chain_law (f : X → Ξ → X) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (E : Set X) (hE : ∀ x ∈ E, ∀ ξ, f x ξ = x)
    (o : X → ℕ) (S : Finset ℕ) (G : Set X) (hG : ∀ x ∈ G, ∀ ξ, f x ξ ∈ G)
    (hGo : ∀ x ∈ G, x ∈ E → o x ∈ S) (U : ℕ → X → ℝ≥0∞)
    (hUe : ∀ b, ∀ x ∈ G, x ∈ E → U b x = if o x = b then 1 else 0)
    (hUs : ∀ b, ∀ x ∈ G, x ∉ E → ∫⁻ ξ, U b (f x ξ) ∂ν ≤ U b x)
    (hsum : ∀ x ∈ G, ∑ b ∈ S, U b x = 1) (T : X → ℝ≥0∞)
    (hT : ∀ x ∈ G, E.indicator 0 x + Eᶜ.indicator 1 x + ∫⁻ ξ, T (f x ξ) ∂ν ≤ T x)
    (hTf : ∀ x ∈ G, T x ≠ ⊤) (x : X) (hx : x ∈ G) (hxE : x ∉ E) (b : ℕ) (hb : b ∈ S) :
    Engine.iidMeasure ν {w | ∃ t, Engine.traj f x w t ∈ E ∧ o (Engine.traj f x w t) = b} =
      U b x := by
  classical
  have : IsProbabilityMeasure (Engine.iidMeasure ν) := by
    unfold Engine.iidMeasure; infer_instance
  set K := Engine.fkKernel f (fun _ _ => 1) ν
  have hmE : ∀ y, MeasurableSet {ξ | f y ξ ∈ E} := fun y => by
    have : {ξ | f y ξ ∈ E} = ⋃ z ∈ E, {ξ | f y ξ = z} := by ext; simp
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun z _ => hf y z
  -- each probability is at most `U`
  have hle : ∀ c, Engine.iidMeasure ν {w | ∃ t, Engine.traj f x w t ∈ E ∧
      o (Engine.traj f x w t) = c} ≤ U c x := by
    intro c
    rw [measure_end_eq_least' f ν hf E hE o c x hxE]
    set W : X → ℝ≥0∞ := fun y => if y ∈ G then (if y ∈ E then 0 else U c y) else ⊤ with hW
    refine (LinSys.least_le_of_super _ _ W ?_ x).trans (by simp [W, hx, hxE])
    intro y
    simp only [Pi.add_apply]
    rw [Engine.app_fkKernel_one f ν hf W y]
    by_cases hyG : y ∈ G
    · by_cases hyE : y ∈ E
      · simp [W, hyG, hyE, hE y hyE]
      · have hm : MeasurableSet {ξ | y ∉ E ∧ f y ξ ∈ E ∧ o (f y ξ) = c} := by
          have : {ξ | y ∉ E ∧ f y ξ ∈ E ∧ o (f y ξ) = c} =
              ⋃ z ∈ {z : X | y ∉ E ∧ z ∈ E ∧ o z = c}, {ξ | f y ξ = z} := by
            ext ξ
            simp
          rw [this]
          exact MeasurableSet.biUnion (Set.to_countable _) fun z _ => hf y z
        rw [← lintegral_indicator_one hm,
          ← lintegral_add_left (measurable_one.indicator hm)]
        have hpt : ∀ ξ, {ξ | y ∉ E ∧ f y ξ ∈ E ∧ o (f y ξ) = c}.indicator 1 ξ +
            W (f y ξ) = U c (f y ξ) := by
          intro ξ
          have hG' := hG y hyG ξ
          by_cases hfE : f y ξ ∈ E
          · rw [hUe c _ hG' hfE]
            by_cases ho : o (f y ξ) = c <;> simp [W, hG', hfE, hyE, ho, Set.indicator]
          · simp [W, hG', hfE, Set.indicator]
        simp_rw [hpt]
        simpa [W, hyG, hyE] using hUs c y hyG hyE
    · simp [W, hyG]
  -- the chain ends almost surely
  have hend : ∀ᵐ w ∂(Engine.iidMeasure ν), ∃ t, Engine.traj f x w t ∈ E := by
    refine ae_exists_traj_mem f ν hf E x ?_
    rw [Engine.lintegral_tsum_traj_eq_least f (fun y (_ : Ξ) => Eᶜ.indicator (fun _ => 1) y) ν hf
      (fun _ => measurable_const) x]
    set T' : X → ℝ≥0∞ := fun y => if y ∈ G then T y else ⊤ with hT'
    refine ne_top_of_le_ne_top ?_ (LinSys.least_le_of_super _ _ T' ?_ x)
    · simpa [T', hx] using hTf x hx
    intro y
    simp only [Pi.add_apply, Engine.fkRhs, lintegral_const, measure_univ, mul_one]
    rw [Engine.app_fkKernel_one f ν hf T' y]
    by_cases hyG : y ∈ G
    · have h := hT y hyG
      have hfG : ∀ ξ, T' (f y ξ) = T (f y ξ) := fun ξ => by simp [T', hG y hyG ξ]
      simp only [hfG, T', hyG, ite_true]
      by_cases hyE : y ∈ E
      · simpa [hyE] using h
      · simpa [hyE] using h
    · simp [T', hyG]
  -- the probabilities sum to one
  have hsum_x : ∑ c ∈ S, Engine.iidMeasure ν {w | ∃ t, Engine.traj f x w t ∈ E ∧
      o (Engine.traj f x w t) = c} = 1 := by
    have hmc : ∀ c, MeasurableSet {w : ℕ → Ξ | ∃ t, Engine.traj f x w t ∈ E ∧
        o (Engine.traj f x w t) = c} := by
      intro c
      have : {w : ℕ → Ξ | ∃ t, Engine.traj f x w t ∈ E ∧ o (Engine.traj f x w t) = c} =
          ⋃ t, ⋃ z ∈ {z : X | z ∈ E ∧ o z = c}, {w | Engine.traj f x w t = z} := by
        ext w
        simp [and_comm]
      rw [this]
      exact MeasurableSet.iUnion fun t => MeasurableSet.biUnion (Set.to_countable _) fun z _ =>
        measurableSet_traj_eq f hf x t z
    rw [← measure_biUnion_finset]
    · have hset : (⋃ c ∈ S, {w : ℕ → Ξ | ∃ t, Engine.traj f x w t ∈ E ∧
          o (Engine.traj f x w t) = c}) = {w | ∃ t, Engine.traj f x w t ∈ E} := by
        ext w
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
        constructor
        · rintro ⟨c, -, t, ht, -⟩
          exact ⟨t, ht⟩
        · rintro ⟨t, ht⟩
          exact ⟨_, hGo _ (traj_mem_closed f G hG x hx w t) ht, t, ht, rfl⟩
      rw [hset]
      have hm : MeasurableSet {w : ℕ → Ξ | ∃ t, Engine.traj f x w t ∈ E} := by
        have : {w : ℕ → Ξ | ∃ t, Engine.traj f x w t ∈ E} =
            ⋃ t, ⋃ z ∈ E, {w | Engine.traj f x w t = z} := by
          ext w
          simp
        rw [this]
        exact MeasurableSet.iUnion fun t => MeasurableSet.biUnion (Set.to_countable _) fun z _ =>
          measurableSet_traj_eq f hf x t z
      rw [(ae_iff_measure_eq hm.nullMeasurableSet).1 hend, measure_univ]
    · intro c _ c' _ hcc'
      refine Set.disjoint_left.2 fun w hw hw' => hcc' ?_
      obtain ⟨t, htE, hto⟩ := hw
      obtain ⟨t', htE', hto'⟩ := hw'
      have h1 := traj_absorb f E hE x w t (max t t') htE (le_max_left _ _)
      have h2 := traj_absorb f E hE x w t' (max t t') htE' (le_max_right _ _)
      rw [← hto, ← hto', ← h1, ← h2]
    · intro c _
      exact hmc c
  exact eq_of_le_of_sum S _ (fun c => U c x) (fun c _ => hle c)
    (by rw [hsum x hx]; simp) (by rw [hsum x hx, hsum_x]) b hb

end FrogModel.D3
