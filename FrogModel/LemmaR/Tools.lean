module

public import Mathlib

@[expose] public section

/-!
# Generic probability tools of the second moment method (Lemma 9.2 of the paper)

- `paleyZygmund`: Paley-Zygmund at `θ = 1/2` for `ℝ≥0∞`-valued variables, with a dominating
  variable `U` for the second moment: `(E Z)^2 ≤ 4 P(Z > E Z / 2) E U^2`.
- `lintegral_sq_sum_le`: `E (∑ X_i)^2 ≤ ∑ E X_i^2 + (∑ E X_i)^2` for independent `X_i ≥ 0`.
- `measure_eq_top_ge`: continuity from above for `P(V = ∞)`.
- `frequently_of_limsup_pos`: `limsup f n / n > 0` gives `f n ≥ c n` infinitely often.
- `sq_eq_tsum`, `tsum_odd_geom_le`: `N^2 = ∑ (2m + 1) 1{N > m}` on `ℕ∞` and `∑ (2m + 1) r^m ≤ 6`
  for `r ≤ 1/2`.
- `measure_top_pos_of_linear`: the second moment method along a sequence. Lower models
  `Z n ≤ V` with `E Z n ≥ c n` infinitely often, dominated by `U n` with `E (U n)^2 ≤ K n^2`,
  give `P(V = ∞) > 0`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Paley-Zygmund at `θ = 1/2`, with a dominating variable for the second moment. -/
theorem FrogModel.LemmaR.paleyZygmund {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z U : Ω → ℝ≥0∞) (hZ : AEMeasurable Z μ) (hU : AEMeasurable U μ)
    (hZU : ∀ᵐ ω ∂μ, Z ω ≤ U ω) (hU2 : ∫⁻ ω, U ω ^ 2 ∂μ ≠ ⊤) :
    (∫⁻ ω, Z ω ∂μ) ^ 2 ≤ 4 * μ {ω | (∫⁻ ω, Z ω ∂μ) / 2 < Z ω} * ∫⁻ ω, U ω ^ 2 ∂μ := by
  set a := ∫⁻ ω, Z ω ∂μ with ha
  set A := {ω | a / 2 < Z ω} with hA
  set K := ∫⁻ ω, U ω ^ 2 ∂μ with hK
  -- `E U < ∞`, hence `a < ∞`
  have hU1 : ∫⁻ ω, U ω ∂μ ≤ 1 + K := by
    calc ∫⁻ ω, U ω ∂μ ≤ ∫⁻ ω, 1 + U ω ^ 2 ∂μ := by
          refine lintegral_mono fun ω => ?_
          rcases le_or_gt (U ω) 1 with h | h
          · exact h.trans le_self_add
          · calc U ω = U ω * 1 := (mul_one _).symm
              _ ≤ U ω * U ω := by gcongr
              _ = U ω ^ 2 := (sq _).symm
              _ ≤ 1 + U ω ^ 2 := le_add_self
      _ = 1 + K := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  have hatop : a ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hU2⟩)
      ((lintegral_mono_ae hZU).trans hU1)
  -- `a / 2 ≤ ∫⁻ 1_A Z`
  have hsplit : a ≤ ∫⁻ ω, A.indicator Z ω ∂μ + a / 2 := by
    calc a = ∫⁻ ω, Z ω ∂μ := rfl
      _ ≤ ∫⁻ ω, A.indicator Z ω + a / 2 ∂μ := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ A
          · rw [Set.indicator_of_mem hω]
            exact le_self_add
          · rw [Set.indicator_of_notMem hω, zero_add]
            exact not_lt.1 hω
      _ = ∫⁻ ω, A.indicator Z ω ∂μ + a / 2 := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  have hhalf : a / 2 ≤ ∫⁻ ω, A.indicator Z ω ∂μ := by
    rw [← ENNReal.sub_half hatop]
    exact tsub_le_iff_right.2 hsplit
  -- `∫⁻ 1_A Z ≤ ∫⁻ U 1_A ≤ K^(1/2) (μ A)^(1/2)`
  have hAnull : NullMeasurableSet A μ := nullMeasurableSet_lt aemeasurable_const hZ
  have hind : AEMeasurable (A.indicator (1 : Ω → ℝ≥0∞)) μ :=
    aemeasurable_one.indicator₀ hAnull
  have hCS : ∫⁻ ω, A.indicator Z ω ∂μ ≤ K ^ (1 / (2 : ℝ)) * (μ A) ^ (1 / (2 : ℝ)) := by
    calc ∫⁻ ω, A.indicator Z ω ∂μ ≤ ∫⁻ ω, (U * A.indicator (1 : Ω → ℝ≥0∞)) ω ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hZU] with ω hω
          by_cases hω' : ω ∈ A
          · simp [Set.indicator_of_mem hω', hω]
          · simp [Set.indicator_of_notMem hω']
      _ ≤ (∫⁻ ω, U ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫⁻ ω, A.indicator 1 ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hU hind
      _ = K ^ (1 / (2 : ℝ)) * (∫⁻ ω, A.indicator 1 ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
          congr 2
          exact lintegral_congr fun ω => ENNReal.rpow_two _
      _ ≤ K ^ (1 / (2 : ℝ)) * (μ A) ^ (1 / (2 : ℝ)) := by
          gcongr
          · calc ∫⁻ ω, A.indicator 1 ω ^ (2 : ℝ) ∂μ = ∫⁻ ω, A.indicator 1 ω ∂μ := by
                  refine lintegral_congr fun ω => ?_
                  by_cases hω : ω ∈ A <;> simp [hω]
              _ ≤ μ A := lintegral_indicator_one_le A
  -- square
  have hsq : (a / 2) ^ 2 ≤ K * μ A := by
    calc (a / 2) ^ 2 ≤ (K ^ (1 / (2 : ℝ)) * (μ A) ^ (1 / (2 : ℝ))) ^ 2 := by
          gcongr
          exact hhalf.trans hCS
      _ = K * μ A := by
          rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (μ A ^ (1 / (2 : ℝ))),
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          norm_num
  have h2a : 2 * (a / 2) = a := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  calc a ^ 2 = 4 * (a / 2) ^ 2 := by
        conv_lhs => rw [← h2a]
        rw [mul_pow]
        norm_num
    _ ≤ 4 * (K * μ A) := by gcongr
    _ = 4 * μ A * K := by ring

/-- Second moment of a sum of independent nonnegative variables. -/
theorem FrogModel.LemmaR.lintegral_sq_sum_le {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Finset ι) (X : ι → Ω → ℝ≥0∞) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) :
    ∫⁻ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ ≤
      ∑ i ∈ s, ∫⁻ ω, X i ω ^ 2 ∂μ + (∑ i ∈ s, ∫⁻ ω, X i ω ∂μ) ^ 2 := by
  classical
  have hpair : ∀ i ∈ s, ∀ j ∈ s, ∫⁻ ω, X i ω * X j ω ∂μ ≤
      (if i = j then ∫⁻ ω, X i ω ^ 2 ∂μ else 0) + (∫⁻ ω, X i ω ∂μ) * ∫⁻ ω, X j ω ∂μ := by
    intro i _ j _
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, ← sq]
      exact le_self_add
    · simp only [hij, ite_false, zero_add]
      exact (lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hX i) (hX j)
        (hind.indepFun hij)).le
  calc ∫⁻ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ = ∫⁻ ω, ∑ i ∈ s, ∑ j ∈ s, X i ω * X j ω ∂μ := by
        congr 1
        funext ω
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫⁻ ω, X i ω * X j ω ∂μ := by
        have hm : ∀ i j, Measurable fun ω => X i ω * X j ω := fun i j => (hX i).mul (hX j)
        rw [lintegral_finsetSum s fun i _ => Finset.measurable_sum s fun j _ => hm i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum s fun j _ => hm i j]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ((if i = j then ∫⁻ ω, X i ω ^ 2 ∂μ else 0) +
          (∫⁻ ω, X i ω ∂μ) * ∫⁻ ω, X j ω ∂μ) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ = ∑ i ∈ s, ∫⁻ ω, X i ω ^ 2 ∂μ + (∑ i ∈ s, ∫⁻ ω, X i ω ∂μ) ^ 2 := by
        rw [sq (∑ i ∈ s, ∫⁻ ω, X i ω ∂μ), Finset.sum_mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq s i (fun _ => ∫⁻ ω, X i ω ^ 2 ∂μ)]
        simp [hi]

/-- Continuity from above: `P(V > M) ≥ δ` for every `M` gives `P(V = ∞) ≥ δ`. -/
theorem FrogModel.LemmaR.measure_eq_top_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (V : Ω → ℝ≥0∞) (hV : Measurable V) (δ : ℝ≥0∞)
    (h : ∀ M : ℕ, δ ≤ μ {ω | (M : ℝ≥0∞) < V ω}) : δ ≤ μ {ω | V ω = ⊤} := by
  set s : ℕ → Set Ω := fun M => {ω | (M : ℝ≥0∞) < V ω} with hs_def
  have hmeas : ∀ M, MeasurableSet (s M) := by
    intro M
    dsimp [s]
    exact measurableSet_lt measurable_const hV
  have hnull : ∀ M, NullMeasurableSet (s M) μ := fun M =>
    (hmeas M).nullMeasurableSet
  have hanti : Antitone s := by
    intro a b hle
    dsimp [s]
    refine Set.Subset.trans ?_ (Set.Subset.refl _)
    -- hle : a ≤ b, need {ω | (b:ℝ≥0∞) < V ω} ⊆ {ω | (a:ℝ≥0∞) < V ω}
    -- Since (a:ℝ≥0∞) ≤ (b:ℝ≥0∞), this follows
    intro ω hω
    have hVω : (b : ℝ≥0∞) < V ω := hω
    have ha_le_b : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast Nat.cast_le.mpr hle
    exact lt_of_le_of_lt ha_le_b hVω
  have hfin : ∃ M, μ (s M) ≠ ⊤ := by
    have h_fin : μ Set.univ ≠ ⊤ :=
      (measure_lt_top μ Set.univ).ne
    refine ⟨0, ?_⟩
    exact ne_top_of_le_ne_top h_fin (measure_mono (Set.subset_univ _))
  have h_eq : {ω | V ω = ⊤} = ⋂ M, s M := by
    ext ω
    constructor
    · intro hω
      have hVω : V ω = ⊤ := hω
      refine Set.mem_iInter.mpr fun M => ?_
      dsimp [s]
      rw [hVω]
      exact (ENNReal.natCast_ne_top M).lt_top
    · intro hω
      have h_all : ∀ M : ℕ, (M : ℝ≥0∞) < V ω := by
        intro M
        simpa [s] using Set.mem_iInter.mp hω M
      by_contra h_not_top
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h_not_top
      have h_lt_n : (n : ℝ≥0∞) < V ω := h_all n
      exact lt_irrefl _ (lt_trans hn h_lt_n)
  rw [h_eq]
  have h_measure_eq : μ (⋂ M, s M) = ⨅ M, μ (s M) :=
    Antitone.measure_iInter hanti hnull hfin
  rw [h_measure_eq]
  exact le_iInf h

/-- A positive `limsup` of `f n / n` gives `c n ≤ f n` infinitely often for some finite `c > 0`. -/
theorem FrogModel.LemmaR.frequently_of_limsup_pos (f : ℕ → ℝ≥0∞)
    (h : 0 < limsup (fun n : ℕ => f n / n) atTop) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ᶠ n in atTop, c * n ≤ f n := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp h with ⟨r, hr0, hr⟩
  have hr_top : (r : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h_freq : ∃ᶠ n in atTop, (r : ENNReal) < f n / n :=
    Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hr
  have h_event : ∀ᶠ (n : ℕ) in atTop,
      ((r : ENNReal) < f n / n → (r : ENNReal) * (n : ENNReal) ≤ f n) := by
    refine Filter.eventually_atTop.mpr ⟨0, ?_⟩
    intro n hn hlt
    by_cases hn0 : (n : ENNReal) = 0
    · simp [hn0]
    · have hle : (r : ENNReal) ≤ f n / (n : ENNReal) := le_of_lt hlt
      have h_mul := ENNReal.mul_le_of_le_div hle
      simpa [mul_comm] using h_mul
  have h_freq' : ∃ᶠ (n : ℕ) in atTop, (r : ENNReal) * (n : ENNReal) ≤ f n :=
    h_freq.mp h_event
  exact ⟨(r : ENNReal), hr0, hr_top, h_freq'⟩

/-- `N^2 = ∑_{m ≥ 0} (2m + 1) 1{N ≥ m + 1}` for `N ∈ ℕ∞`. -/
theorem FrogModel.LemmaR.sq_eq_tsum (N : ℕ∞) :
    ((N : ℝ≥0∞)) ^ 2 =
      ∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) * (if ((m + 1 : ℕ) : ℕ∞) ≤ N then 1 else 0) := by
  -- First, prove a helper lemma about the sum of odd numbers
  have h_sum_odd : ∀ k : ℕ, (∑ m ∈ Finset.range k, (2 * m + 1 : ℝ≥0∞)) = ((k : ℕ) ^ 2 : ℝ≥0∞) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  by_cases hN : N = ⊤
  · -- Case N = ⊤
    subst hN
    have htop_pow : ((⊤ : ℕ∞) : ℝ≥0∞) ^ 2 = ⊤ := by
      calc
        ((⊤ : ℕ∞) : ℝ≥0∞) ^ 2 = (⊤ : ℝ≥0∞) ^ 2 := by simp
        _ = ⊤ := ENNReal.top_pow (by norm_num : 2 ≠ 0)
    rw [htop_pow]
    have h_indicator : ∀ m : ℕ, (if ((m + 1 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0) = 1 := by
      intro m; simp
    simp_rw [h_indicator, mul_one]
    -- Need: ∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) = ⊤
    have h_one_le : ∀ m : ℕ, (1 : ℝ≥0∞) ≤ (2 * m + 1 : ℝ≥0∞) := by
      intro m
      have h : (1 : ℕ) ≤ 2 * m + 1 := by omega
      exact_mod_cast h
    have h_tsum_one : (∑' m : ℕ, (1 : ℝ≥0∞)) = ⊤ :=
      ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    have h_tsum_le : (∑' m : ℕ, (1 : ℝ≥0∞)) ≤ ∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) :=
      ENNReal.tsum_le_tsum h_one_le
    rw [h_tsum_one] at h_tsum_le
    exact (top_unique h_tsum_le).symm
  · -- Case N ≠ ⊤, so N is a natural number
    rcases (ENat.ne_top_iff_exists.mp hN) with ⟨k, hk⟩
    subst hk
    -- Goal: ((k : ℕ∞) : ℝ≥0∞)^2 = ∑' m, (2*m+1) * (if (m+1 : ℕ∞) ≤ (k : ℕ∞) then 1 else 0)
    have h_left : ((k : ℕ∞) : ℝ≥0∞) ^ 2 = ((k : ℕ) ^ 2 : ℝ≥0∞) := by
      simp
    rw [h_left]
    -- Now: (k^2 : ℝ≥0∞) = ∑' m, (2*m+1) * (if (m+1 : ℕ∞) ≤ (k : ℕ∞) then 1 else 0)
    -- The indicator is 1 iff m+1 ≤ k, i.e., m < k
    have h_indicator : ∀ m : ℕ, (if ((m + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) then (1 : ℝ≥0∞) else 0) =
        (if m ∈ Finset.range k then (1 : ℝ≥0∞) else 0) := by
      intro m
      have h_le_iff : ((m + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) ↔ m + 1 ≤ k := ENat.natCast_le_natCast
      have h_mem_iff : m + 1 ≤ k ↔ m ∈ Finset.range k := by
        rw [Finset.mem_range]
        omega
      by_cases hle : m + 1 ≤ k
      · have hle' : ((m + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := h_le_iff.mpr hle
        have hmem : m ∈ Finset.range k := h_mem_iff.mp hle
        simp only [hle', hmem, ite_true]
      · have hle' : ¬ ((m + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
          rw [h_le_iff]
          exact hle
        have hmem : m ∉ Finset.range k := mt h_mem_iff.mpr hle
        simp only [hle', hmem, ite_false]
    simp_rw [h_indicator]
    -- Now the term is: (2*m+1) * (if m ∈ range k then 1 else 0)
    have h_tsum_eq_sum :
        (∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) * (if m ∈ Finset.range k then (1 : ℝ≥0∞) else 0)) =
        ∑ m ∈ Finset.range k, (2 * m + 1 : ℝ≥0∞) := by
      let f : ℕ → ℝ≥0∞ := fun m =>
        (2 * m + 1 : ℝ≥0∞) * (if m ∈ Finset.range k then (1 : ℝ≥0∞) else 0)
      have hf : ∀ b ∉ Finset.range k, f b = 0 := by
        intro b hb
        dsimp [f]
        have : (if b ∈ Finset.range k then (1 : ℝ≥0∞) else 0) = 0 := by
          simp [hb]
        rw [this, mul_zero]
      have h := tsum_eq_sum (L := SummationFilter.unconditional ℕ) (f := f) (s := Finset.range k) hf
      rw [h]
      refine Finset.sum_congr rfl fun m hm => ?_
      dsimp [f]
      have : (if m ∈ Finset.range k then (1 : ℝ≥0∞) else 0) = 1 := by
        simp [hm]
      rw [this, mul_one]
    rw [h_tsum_eq_sum]
    rw [h_sum_odd k]

/-- `∑_{m ≥ 0} (2m + 1) r^m ≤ 6` for `r ≤ 1/2`. -/
theorem FrogModel.LemmaR.tsum_odd_geom_le (r : ℝ≥0∞) (hr : r ≤ 2⁻¹) :
    ∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) * r ^ m ≤ 6 := by
  have h1 : Summable (fun m : ℕ => (m : ℝ) * 2⁻¹ ^ m) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(2⁻¹ : ℝ)‖ < 1)
  have h2 : Summable (fun m : ℕ => (2⁻¹ : ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : Summable (fun m : ℕ => (2 * m + 1 : ℝ) * 2⁻¹ ^ m) := by
    simp_rw [add_mul, mul_assoc]
    exact (h1.mul_left 2).add (by simpa using h2)
  have hreal : ∑' m : ℕ, (2 * m + 1 : ℝ) * 2⁻¹ ^ m = 6 := by
    simp_rw [add_mul, mul_assoc, one_mul]
    rw [(h1.mul_left 2).tsum_add h2, tsum_mul_left,
      tsum_coe_mul_geometric_of_norm_lt_one (by norm_num), tsum_geometric_inv_two]
    norm_num
  calc ∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) * r ^ m ≤ ∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) * 2⁻¹ ^ m :=
        ENNReal.tsum_le_tsum fun m => by gcongr
    _ = ∑' m : ℕ, ENNReal.ofReal ((2 * m + 1) * 2⁻¹ ^ m) := by
        congr 1
        ext m
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_inv_of_pos two_pos]
        congr 1
        · rw [show (2 * m + 1 : ℝ) = ((2 * m + 1 : ℕ) : ℝ) by push_cast; ring,
            ENNReal.ofReal_natCast]
          push_cast
          rfl
        · simp
    _ = ENNReal.ofReal (∑' m : ℕ, (2 * m + 1 : ℝ) * 2⁻¹ ^ m) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum).symm
    _ = 6 := by rw [hreal]; simp

/-- The second moment method along a sequence: lower models `Z n ≤ V` with `E Z n ≥ c n` for
infinitely many `n`, dominated by `U n` with `E (U n)^2 ≤ K n^2`, give `P(V = ∞) > 0`. -/
theorem FrogModel.LemmaR.measure_top_pos_of_linear {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → ℝ≥0∞) (hV : Measurable V)
    (Z U : ℕ → Ω → ℝ≥0∞)
    (hZ : ∀ n, AEMeasurable (Z n) μ) (hU : ∀ n, AEMeasurable (U n) μ)
    (hZV : ∀ n, ∀ᵐ ω ∂μ, Z n ω ≤ V ω) (hZU : ∀ n, ∀ᵐ ω ∂μ, Z n ω ≤ U n ω)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) (hU2 : ∀ n : ℕ, 1 ≤ n → ∫⁻ ω, U n ω ^ 2 ∂μ ≤ K * (n : ℝ≥0∞) ^ 2)
    {c : ℝ≥0∞} (hc : 0 < c) (hfreq : ∃ᶠ n in atTop, c * n ≤ ∫⁻ ω, Z n ω ∂μ) :
    0 < μ {ω | V ω = ⊤} := by
  set c' := min c 1 with hc'
  have hc'pos : 0 < c' := lt_min hc one_pos
  have hc'top : c' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hfreq' : ∃ᶠ n in atTop, 1 ≤ n ∧ c' * n ≤ ∫⁻ ω, Z n ω ∂μ := by
    refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono ?_
    rintro n ⟨h1, h2⟩
    exact ⟨h2, le_trans (mul_le_mul_left (min_le_left _ _) _) h1⟩
  set K' : ℝ≥0∞ := 4 * (K + 1) with hK'
  have hK'0 : K' ≠ 0 := by simp [hK']
  have hK'top : K' ≠ ⊤ := ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨hK, by simp⟩)
  set δ : ℝ≥0∞ := c' ^ 2 / K' with hδ
  have key : ∀ n : ℕ, 1 ≤ n → c' * n ≤ ∫⁻ ω, Z n ω ∂μ →
      δ ≤ μ {ω | c' * n / 2 < V ω} := by
    intro n hn hcn
    have hKn : ∫⁻ ω, U n ω ^ 2 ∂μ ≤ (K + 1) * (n : ℝ≥0∞) ^ 2 :=
      (hU2 n hn).trans (by gcongr; exact le_self_add)
    have hKtop : ∫⁻ ω, U n ω ^ 2 ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hK, by simp⟩)
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n))) hKn
    have hPZ := FrogModel.LemmaR.paleyZygmund μ (Z n) (U n) (hZ n) (hU n) (hZU n) hKtop
    set A := {ω | (∫⁻ ω, Z n ω ∂μ) / 2 < Z n ω} with hA
    have hAV : μ A ≤ μ {ω | c' * n / 2 < V ω} := by
      apply measure_mono_ae
      filter_upwards [hZV n] with ω hω hωA
      show c' * n / 2 < V ω
      calc c' * n / 2 ≤ (∫⁻ ω, Z n ω ∂μ) / 2 := by gcongr
        _ < Z n ω := hωA
        _ ≤ V ω := hω
    have h1 : c' ^ 2 * (n : ℝ≥0∞) ^ 2 ≤ (K' * μ A) * (n : ℝ≥0∞) ^ 2 := by
      calc c' ^ 2 * (n : ℝ≥0∞) ^ 2 = (c' * n) ^ 2 := by ring
        _ ≤ (∫⁻ ω, Z n ω ∂μ) ^ 2 := by gcongr
        _ ≤ 4 * μ A * ∫⁻ ω, U n ω ^ 2 ∂μ := hPZ
        _ ≤ 4 * μ A * ((K + 1) * (n : ℝ≥0∞) ^ 2) := by gcongr
        _ = (K' * μ A) * (n : ℝ≥0∞) ^ 2 := by rw [hK']; ring
    have hn0 : (n : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (by omega : n ≠ 0))
    have hnt : (n : ℝ≥0∞) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)
    have h2 : c' ^ 2 ≤ K' * μ A := (ENNReal.mul_le_mul_iff_left hn0 hnt).1 h1
    calc δ = c' ^ 2 / K' := rfl
      _ ≤ μ A := by
        rw [ENNReal.div_le_iff hK'0 hK'top, mul_comm]
        exact h2
      _ ≤ _ := hAV
  have hall : ∀ M : ℕ, δ ≤ μ {ω | (M : ℝ≥0∞) < V ω} := by
    intro M
    have hev : ∀ᶠ n : ℕ in atTop, (M : ℝ≥0∞) ≤ c' * n / 2 := by
      have hne : 2 * (M : ℝ≥0∞) / c' ≠ ⊤ :=
        ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hc'pos.ne'
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hne
      filter_upwards [eventually_ge_atTop N] with n hn
      have hlt : 2 * (M : ℝ≥0∞) / c' < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
      rw [ENNReal.div_lt_iff (Or.inl hc'pos.ne') (Or.inl hc'top)] at hlt
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm,
        mul_comm c']
      exact hlt.le
    obtain ⟨n, ⟨hn1, hcn⟩, hMn⟩ := (hfreq'.and_eventually hev).exists
    calc δ ≤ μ {ω | c' * n / 2 < V ω} := key n hn1 hcn
      _ ≤ μ {ω | (M : ℝ≥0∞) < V ω} := measure_mono fun ω hω => lt_of_le_of_lt hMn hω
  have htop := FrogModel.LemmaR.measure_eq_top_ge μ V hV δ hall
  have hδpos : 0 < δ := ENNReal.div_pos (pow_ne_zero 2 hc'pos.ne') hK'top
  exact lt_of_lt_of_le hδpos htop
