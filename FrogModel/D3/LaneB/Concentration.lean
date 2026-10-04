module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# Concentration for sums of independent indicators (Lemma 11.1 of the paper, parts (1) and (2))

`U = ∑ 1_{A_i}` with independent events, `mu = E U`: `E|U - mu| ≤ mu^(1/2)`, hence
`E(mu - U)_+ ≤ mu^(1/2)/2`; the first bound of Lemma 11.1 (1) follows by Markov's inequality on
`mu - X ≥ 0` split at `U`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- `E|U - mu| ≤ mu^(1/2)` for a sum `U` of indicators of independent events, `mu = E U`. -/
theorem integral_abs_sub_le_sqrt {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) :
    ∫ ω, |∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω - ∑ i ∈ s, (μ (A i)).toReal| ∂μ ≤
      Real.sqrt (∑ i ∈ s, (μ (A i)).toReal) := by
  let X : ι → Ω → ℝ := fun i ω => (A i).indicator (1 : Ω → ℝ) ω
  let p : ι → ℝ := fun i => (μ (A i)).toReal
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i; dsimp [p]; exact ENNReal.toReal_nonneg
  have h_int_X : ∀ i, ∫ ω, X i ω ∂μ = p i := by
    intro i
    dsimp [X, p]
    rw [integral_indicator_one (hA i), MeasureTheory.measureReal_def]
  have h_int_sum : ∫ ω, (∑ i ∈ s, X i ω) ∂μ = ∑ i ∈ s, p i := by
    rw [integral_finsetSum]
    · simp_rw [h_int_X]
    · intro i hi
      have h_meas : AEStronglyMeasurable (X i) μ := by
        dsimp [X]
        have h_const : AEStronglyMeasurable (fun _ : Ω => (1 : ℝ)) μ :=
          aestronglyMeasurable_const
        exact h_const.indicator (hA i)
      have h_bound : ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ (1 : ℝ) := by
        dsimp [X]
        filter_upwards with ω
        by_cases h : ω ∈ A i
        · simp [h]
        · simp [h]
      exact MeasureTheory.Integrable.of_bound h_meas 1 h_bound
  have h_indep : iIndepFun X μ :=
    hind.iIndepFun_indicator
  have h_memLp_X : ∀ i, MemLp (X i) 2 μ := by
    intro i
    dsimp [X]
    have h_ae : AEStronglyMeasurable ((A i).indicator (1 : Ω → ℝ)) μ := by
      have h_const : AEStronglyMeasurable (fun _ : Ω => (1 : ℝ)) μ :=
        aestronglyMeasurable_const
      exact h_const.indicator (hA i)
    have h_bound : ∀ᵐ ω ∂μ, ‖(A i).indicator (1 : Ω → ℝ) ω‖ ≤ (1 : ℝ) := by
      filter_upwards with ω
      by_cases h : ω ∈ A i
      · simp [h]
      · simp [h]
    exact MeasureTheory.MemLp.of_bound h_ae 1 h_bound
  have h_var_sum : variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ := by
    refine ProbabilityTheory.IndepFun.variance_sum (fun i hi => h_memLp_X i) ?_
    intro i hi j hj hne
    exact h_indep.indepFun hne
  have h_var_X : ∀ i, variance (X i) μ = p i * (1 - p i) := by
    intro i
    have h_memLp : MemLp (X i) 2 μ := h_memLp_X i
    have h_sq_eq : (X i ^ 2) = X i := by
      dsimp [X]
      ext ω
      simp [Set.indicator]
    rw [ProbabilityTheory.variance_eq_sub h_memLp, h_int_X i, h_sq_eq, h_int_X i]
    ring
  have h_var_X_le_p : ∀ i, variance (X i) μ ≤ p i := by
    intro i
    rw [h_var_X i]
    nlinarith [hp_nonneg i]
  have h_var_sum_le : variance (∑ i ∈ s, X i) μ ≤ ∑ i ∈ s, p i := by
    rw [h_var_sum]
    exact Finset.sum_le_sum (fun i hi => h_var_X_le_p i)
  -- Key inequality: (∫ |f|)^2 ≤ ∫ f^2
  -- Proof: variance(|f|) = ∫ |f|^2 - (∫ |f|)^2 ≥ 0, and |f|^2 = f^2
  have h_key : (∫ ω, |(∑ i ∈ s, X i ω) - (∑ i ∈ s, p i)| ∂μ)^2 ≤
      ∫ ω, ((∑ i ∈ s, X i ω) - (∑ i ∈ s, p i))^2 ∂μ := by
    set f := fun ω : Ω => (∑ i ∈ s, X i ω) - (∑ i ∈ s, p i) with hf
    have h_memLp_f : MemLp f 2 μ := by
      dsimp [f]
      have h_sum : MemLp (fun ω => ∑ i ∈ s, X i ω) 2 μ := by
        refine MeasureTheory.memLp_finsetSum _ (fun i hi => h_memLp_X i)
      have h_const : MemLp (fun _ : Ω => ∑ i ∈ s, p i) 2 μ :=
        MeasureTheory.memLp_const _
      exact h_sum.sub h_const
    have h_memLp_abs_f : MemLp (|f|) 2 μ :=
      h_memLp_f.abs
    have h_var_abs_eq : variance (|f|) μ = ∫ ω, (|f ω|)^2 ∂μ - (∫ ω, |f ω| ∂μ)^2 := by
      simpa using ProbabilityTheory.variance_eq_sub h_memLp_abs_f
    have h_var_nonneg : 0 ≤ variance (|f|) μ :=
      ProbabilityTheory.variance_nonneg _ _
    rw [h_var_abs_eq] at h_var_nonneg
    have h_abs_sq_eq' : (fun ω => (|f ω|)^2) = (fun ω => (f ω)^2) := by
      ext ω; simp [sq_abs]
    rw [h_abs_sq_eq'] at h_var_nonneg
    nlinarith
  -- Now combine everything
  have h_int_g : ∫ ω, ((∑ i ∈ s, X i ω) - (∑ i ∈ s, p i)) ∂μ = 0 := by
    calc
      ∫ ω, ((∑ i ∈ s, X i ω) - (∑ i ∈ s, p i)) ∂μ
          = (∫ ω, (∑ i ∈ s, X i ω) ∂μ) - (∫ ω, (∑ i ∈ s, p i) ∂μ) := by
        rw [integral_sub]
        · -- integrability of sum
          have h_sum_int : Integrable (fun ω => ∑ i ∈ s, X i ω) μ := by
            refine MeasureTheory.integrable_finsetSum _ (fun i hi => ?_)
            have h_meas : AEStronglyMeasurable (X i) μ := by
              dsimp [X]
              have h_const : AEStronglyMeasurable (fun _ : Ω => (1 : ℝ)) μ :=
                aestronglyMeasurable_const
              exact h_const.indicator (hA i)
            have h_bound : ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ (1 : ℝ) := by
              dsimp [X]
              filter_upwards with ω
              by_cases h : ω ∈ A i
              · simp [h]
              · simp [h]
            exact MeasureTheory.Integrable.of_bound h_meas 1 h_bound
          exact h_sum_int
        · exact MeasureTheory.integrable_const _
      _ = (∑ i ∈ s, p i) - (∑ i ∈ s, p i) := by
        rw [h_int_sum, integral_const, smul_eq_mul, mul_comm, MeasureTheory.probReal_univ, mul_one]
      _ = 0 := by ring
  have h_var_eq : variance (∑ i ∈ s, X i) μ = ∫ ω, ((∑ i ∈ s, X i ω) - (∑ i ∈ s, p i))^2 ∂μ := by
    -- Use variance_eq_integral directly on ∑ X_i
    -- variance(∑ X_i) = ∫ ((∑ X_i) - E[∑ X_i])^2 = ∫ (∑ X_i - ∑ p_i)^2
    have h_ae : AEMeasurable (∑ i ∈ s, X i) μ := by
      refine Finset.aemeasurable_sum s (fun i hi => ?_)
      have h_meas : AEMeasurable (X i) μ := by
        dsimp [X]
        have h_const : AEStronglyMeasurable (fun _ : Ω => (1 : ℝ)) μ :=
          aestronglyMeasurable_const
        exact (h_const.indicator (hA i)).aemeasurable
      exact h_meas
    have h_var_eq' := ProbabilityTheory.variance_eq_integral h_ae
    -- h_var_eq' : variance (∑ X_i) = ∫ ((∑ X_i) - ∫ (∑ X_i))^2
    -- Rewrite the integral inside using Finset.sum_apply and h_int_sum
    simpa [Finset.sum_apply, Pi.sub_apply, h_int_sum] using h_var_eq'
  have h_sqrt_nonneg : 0 ≤ ∑ i ∈ s, p i :=
    Finset.sum_nonneg (fun i _ => hp_nonneg i)
  calc
    ∫ ω, |(∑ i ∈ s, X i ω) - (∑ i ∈ s, p i)| ∂μ
        ≤ Real.sqrt ((∫ ω, |(∑ i ∈ s, X i ω) - (∑ i ∈ s, p i)| ∂μ)^2) := by
      rw [Real.le_sqrt (integral_nonneg (fun ω => abs_nonneg _)) (by positivity)]
    _ ≤ Real.sqrt (∫ ω, ((∑ i ∈ s, X i ω) - (∑ i ∈ s, p i))^2 ∂μ) := by
      rw [Real.sqrt_le_sqrt_iff (by positivity)]
      exact h_key
    _ = Real.sqrt (variance (∑ i ∈ s, X i) μ) := by rw [h_var_eq]
    _ ≤ Real.sqrt (∑ i ∈ s, p i) := by
      rw [Real.sqrt_le_sqrt_iff h_sqrt_nonneg]
      exact h_var_sum_le
    _ = Real.sqrt (∑ i ∈ s, (μ (A i)).toReal) := by simp [p]

/-- `E(mu - U)_+ ≤ mu^(1/2)/2` for a sum `U` of indicators of independent events, `mu = E U`. -/
theorem integral_posPart_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) :
    ∫ ω, max 0 (∑ i ∈ s, (μ (A i)).toReal - ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω) ∂μ ≤
      Real.sqrt (∑ i ∈ s, (μ (A i)).toReal) / 2 := by
  set mu := ∑ i ∈ s, (μ (A i)).toReal with hmu
  set U := fun (ω : Ω) => ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω with hU
  have hmax : ∀ (x : ℝ), max 0 (-x) = (|x| - x) / 2 := by
    intro x
    have h1 : max x 0 + max (-x) 0 = |x| := max_zero_add_max_neg_zero_eq_abs_self x
    have h2 : max x 0 - max (-x) 0 = x := max_zero_sub_max_neg_zero_eq_self x
    calc
      max 0 (-x) = max (-x) 0 := by rw [max_comm]
      _ = (|x| - x) / 2 := by linarith
  have h_int_U : Integrable U μ := by
    rw [hU]
    refine MeasureTheory.integrable_finsetSum _ ?_
    intro i hi
    have h_meas : MeasurableSet (A i) := hA i
    have h_int_on : IntegrableOn (fun (_ : Ω) => (1 : ℝ)) (A i) μ :=
      MeasureTheory.integrableOn_const
    exact h_int_on.integrable_indicator h_meas
  have h_int_const : Integrable (fun (_ : Ω) => mu) μ :=
    MeasureTheory.integrable_const (c := mu)
  have h_eq : (fun (ω : Ω) => max 0 (mu - U ω)) = (fun (ω : Ω) => (|U ω - mu| - (U ω - mu)) / 2) := by
    ext ω
    have h_inner : mu - U ω = -(U ω - mu) := by ring
    rw [h_inner, hmax (U ω - mu)]
  rw [h_eq]
  have h_int_abs : Integrable (fun (ω : Ω) => |U ω - mu|) μ :=
    (h_int_U.sub h_int_const).abs
  have h_int_diff : Integrable (fun (ω : Ω) => (U ω - mu)) μ :=
    h_int_U.sub h_int_const
  rw [MeasureTheory.integral_div]
  rw [MeasureTheory.integral_sub h_int_abs h_int_diff]
  have h_int_U_minus_mu : ∫ ω, (U ω - mu) ∂μ = 0 := by
    rw [MeasureTheory.integral_sub h_int_U h_int_const]
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ]
    have h_int_U_sum : ∫ ω, U ω ∂μ = mu := by
      rw [hU]
      rw [MeasureTheory.integral_finsetSum]
      · simp_rw [MeasureTheory.integral_indicator_one (hA _)]
        simp [hmu, MeasureTheory.measureReal_def]
      · intro i hi
        have h_meas : MeasurableSet (A i) := hA i
        have h_int_on : IntegrableOn (fun (_ : Ω) => (1 : ℝ)) (A i) μ :=
          MeasureTheory.integrableOn_const
        exact h_int_on.integrable_indicator h_meas
    rw [h_int_U_sum]
    simp
  rw [h_int_U_minus_mu, sub_zero]
  have h_abs_le : ∫ ω, |U ω - mu| ∂μ ≤ Real.sqrt mu := by
    simpa [hU, hmu, MeasureTheory.measureReal_def] using
      FrogModel.D3.Iface.integral_abs_sub_le_sqrt μ s A hA hind
  gcongr

/-- The core of the first bound of Lemma 11.1 (1) of the paper: `0 ≤ X ≤ U`, `E U = mu`,
`E(mu - U)_+ ≤ c`, `x < mu` give `P(X < x) ≤ (mu - E X + c)/(mu - x)`. -/
theorem lemma12_of_posPart {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X U : Ω → ℝ) (hX : Measurable X) (hXi : Integrable X μ)
    (hUi : Integrable U μ) (_hX0 : ∀ ω, 0 ≤ X ω) (hXU : ∀ ω, X ω ≤ U ω) (mu c : ℝ)
    (hU : ∫ ω, U ω ∂μ = mu) (hc : ∫ ω, max 0 (mu - U ω) ∂μ ≤ c) (x : ℝ) (hx : x < mu) :
    (μ {ω | X ω < x}).toReal ≤ (mu - ∫ ω, X ω ∂μ + c) / (mu - x) := by
  have hx_mu : x < mu := hx
  have h_pos_denom : 0 < mu - x := sub_pos.mpr hx_mu
  set A : Set Ω := {ω | X ω < x} with hA_def
  have hA_meas : MeasurableSet A := measurableSet_lt hX measurable_const
  -- integrability of mu - X
  have h_int_mu_sub_X : Integrable (fun ω => mu - X ω) μ := by
    have h_negX : Integrable (-X) μ := hXi.neg
    have : (fun ω => mu - X ω) = (fun ω => (-X) ω + mu) := by
      ext ω; simp [sub_eq_add_neg, add_comm]
    rw [this]
    exact (integrable_add_const_iff.mpr h_negX)
  -- integrability of max 0 (mu - X)
  have h_int_pos_part : Integrable (fun ω => max 0 (mu - X ω)) μ := by
    have : (fun ω => max 0 (mu - X ω)) = (fun ω => max (mu - X ω) 0) := by
      ext ω; exact max_comm _ _
    rw [this]
    exact h_int_mu_sub_X.pos_part
  -- integrability of U - X
  have h_int_U_sub_X : Integrable (fun ω => U ω - X ω) μ :=
    hUi.sub hXi
  -- integrability of max 0 (mu - U)
  have h_int_pos_part_U : Integrable (fun ω => max 0 (mu - U ω)) μ := by
    have h_negU : Integrable (-U) μ := hUi.neg
    have h_mu_sub_U : Integrable (fun ω => mu - U ω) μ := by
      have : (fun ω => mu - U ω) = (fun ω => (-U) ω + mu) := by
        ext ω; simp [sub_eq_add_neg, add_comm]
      rw [this]
      exact (integrable_add_const_iff.mpr h_negU)
    have : (fun ω => max 0 (mu - U ω)) = (fun ω => max (mu - U ω) 0) := by
      ext ω; exact max_comm _ _
    rw [this]
    exact h_mu_sub_U.pos_part
  -- integrability of indicator of A (constant 1)
  have h_int_indicator : Integrable (A.indicator (fun _ => (1 : ℝ)) : Ω → ℝ) μ :=
    (integrable_const (1 : ℝ)).indicator hA_meas
  -- pointwise inequality
  have h_pointwise : ∀ ω, A.indicator (fun _ => (1 : ℝ)) ω ≤ (max 0 (mu - X ω)) / (mu - x) := by
    intro ω
    rw [Set.indicator_apply]
    by_cases hω : ω ∈ A
    · -- hω : X ω < x
      simp [hω]
      have hXω : X ω < x := hω
      have hXω_lt_mu : X ω < mu := lt_trans hXω hx_mu
      have h_pos_sub : 0 < mu - X ω := sub_pos.mpr hXω_lt_mu
      have h_max_eq : max 0 (mu - X ω) = mu - X ω := max_eq_right h_pos_sub.le
      rw [h_max_eq]
      apply (one_le_div h_pos_denom).mpr
      linarith
    · -- hω : ω ∉ A, i.e., X ω ≥ x
      simp [hω]
      have h_nonneg : 0 ≤ max 0 (mu - X ω) := le_max_left _ _
      exact div_nonneg h_nonneg h_pos_denom.le
  -- integrability of RHS
  have h_int_rhs : Integrable (fun ω => max 0 (mu - X ω) / (mu - x)) μ := by
    have : (fun ω => max 0 (mu - X ω) / (mu - x)) =
        (fun ω => max 0 (mu - X ω) * (mu - x)⁻¹) := by
      ext ω; simp [div_eq_mul_inv]
    rw [this]
    exact h_int_pos_part.mul_const (mu - x)⁻¹
  have h_int_ineq : (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) ≤
      (∫ ω, max 0 (mu - X ω) / (mu - x) ∂μ) :=
    integral_mono h_int_indicator h_int_rhs h_pointwise
  -- simplify LHS
  have h_left : (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = (μ A).toReal := by
    calc
      (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ) := rfl
      _ = μ.real A := by rw [MeasureTheory.integral_indicator_one hA_meas]
      _ = (μ A).toReal := rfl
  -- simplify RHS: integral of quotient = quotient of integrals
  have h_right : (∫ ω, max 0 (mu - X ω) / (mu - x) ∂μ) =
      (∫ ω, max 0 (mu - X ω) ∂μ) / (mu - x) := by
    have h_eq : (fun ω => max 0 (mu - X ω) / (mu - x)) =
        (fun ω => max 0 (mu - X ω) * (mu - x)⁻¹) := by
      ext ω; simp [div_eq_mul_inv]
    rw [h_eq, integral_mul_const]
    ring
  -- pointwise inequality: max 0 (mu - X) ≤ max 0 (mu - U) + (U - X)
  have h_pos_part_bound : ∀ ω, max 0 (mu - X ω) ≤ max 0 (mu - U ω) + (U ω - X ω) := by
    intro ω
    have h_sum : mu - X ω = (mu - U ω) + (U ω - X ω) := by ring
    have h_nonneg_UX : 0 ≤ U ω - X ω := sub_nonneg.mpr (hXU ω)
    have h_toNNReal_add := Real.toNNReal_add_le (r := mu - U ω) (p := U ω - X ω)
    -- h_toNNReal_add : ((mu - U ω) + (U ω - X ω)).toNNReal ≤ (mu - U ω).toNNReal + (U ω - X ω).toNNReal
    have h_cast : (((mu - U ω) + (U ω - X ω)).toNNReal : ℝ) ≤
        ((mu - U ω).toNNReal : ℝ) + ((U ω - X ω).toNNReal : ℝ) := by
      exact_mod_cast h_toNNReal_add
    have h_toNNReal_UX : ((U ω - X ω).toNNReal : ℝ) = U ω - X ω := by
      rw [Real.coe_toNNReal']
      simp [h_nonneg_UX]
    have h_toNNReal_1 : ((mu - U ω).toNNReal : ℝ) = max (mu - U ω) 0 := Real.coe_toNNReal' _
    have h_toNNReal_sum : (((mu - U ω) + (U ω - X ω)).toNNReal : ℝ) = max ((mu - U ω) + (U ω - X ω)) 0 :=
      Real.coe_toNNReal' _
    rw [h_toNNReal_sum, h_toNNReal_1, h_toNNReal_UX] at h_cast
    -- h_cast : max ((mu - U ω) + (U ω - X ω)) 0 ≤ max (mu - U ω) 0 + (U ω - X ω)
    -- Goal: max 0 (mu - X ω) ≤ max 0 (mu - U ω) + (U ω - X ω)
    rw [h_sum]
    -- Goal: max 0 ((mu - U ω) + (U ω - X ω)) ≤ max 0 (mu - U ω) + (U ω - X ω)
    simpa [max_comm] using h_cast
  -- integrate the bound
  have h_int_bound : (∫ ω, max 0 (mu - X ω) ∂μ) ≤
      (∫ ω, max 0 (mu - U ω) ∂μ) + (∫ ω, (U ω - X ω) ∂μ) := by
    have h_int_sum : Integrable (fun ω => max 0 (mu - U ω) + (U ω - X ω)) μ :=
      h_int_pos_part_U.add h_int_U_sub_X
    have h_int_lhs : Integrable (fun ω => max 0 (mu - X ω)) μ := h_int_pos_part
    calc
      (∫ ω, max 0 (mu - X ω) ∂μ) ≤ (∫ ω, max 0 (mu - U ω) + (U ω - X ω) ∂μ) :=
        integral_mono h_int_lhs h_int_sum h_pos_part_bound
      _ = (∫ ω, max 0 (mu - U ω) ∂μ) + (∫ ω, (U ω - X ω) ∂μ) :=
        integral_add h_int_pos_part_U h_int_U_sub_X
  -- simplify U - X integral
  have h_ux_int : (∫ ω, (U ω - X ω) ∂μ) = mu - (∫ ω, X ω ∂μ) := by
    rw [integral_sub hUi hXi, hU]
  -- combine everything
  calc
    (μ A).toReal = (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) := by rw [h_left]
    _ ≤ (∫ ω, max 0 (mu - X ω) / (mu - x) ∂μ) := h_int_ineq
    _ = (∫ ω, max 0 (mu - X ω) ∂μ) / (mu - x) := h_right
    _ ≤ ((∫ ω, max 0 (mu - U ω) ∂μ) + (∫ ω, (U ω - X ω) ∂μ)) / (mu - x) :=
      div_le_div_of_nonneg_right h_int_bound h_pos_denom.le
    _ = ((∫ ω, max 0 (mu - U ω) ∂μ) + (mu - (∫ ω, X ω ∂μ))) / (mu - x) := by rw [h_ux_int]
    _ ≤ (c + (mu - (∫ ω, X ω ∂μ))) / (mu - x) :=
      div_le_div_of_nonneg_right (by nlinarith) h_pos_denom.le
    _ = (mu - (∫ ω, X ω ∂μ) + c) / (mu - x) := by ring

/-- The core of the second bound of Lemma 11.1 (1) of the paper: `0 ≤ X ≤ U`, `E U = mu`,
`g < (1 - t) mu` and `P(U < (1 - t) mu) ≤ ε` give `P(X ≤ g) ≤ (mu - E X)/((1 - t) mu - g) + ε`. -/
theorem lemma12p_of_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X U : Ω → ℝ) (hX : Measurable X) (hU : Measurable U)
    (hXi : Integrable X μ) (hUi : Integrable U μ) (_hX0 : ∀ ω, 0 ≤ X ω) (hXU : ∀ ω, X ω ≤ U ω)
    (mu : ℝ) (hUm : ∫ ω, U ω ∂μ = mu) (t g ε : ℝ) (hg : g < (1 - t) * mu)
    (hT : (μ {ω | U ω < (1 - t) * mu}).toReal ≤ ε) :
    (μ {ω | X ω ≤ g}).toReal ≤ (mu - ∫ ω, X ω ∂μ) / ((1 - t) * mu - g) + ε := by
  set a := (1 - t) * mu with ha
  set B := {ω | X ω ≤ g} ∩ {ω | a ≤ U ω} with hB
  set C := {ω | U ω < a} with hC
  have h_sub : {ω | X ω ≤ g} ⊆ B ∪ C := by
    intro ω hω
    by_cases hωU : a ≤ U ω
    · apply Set.mem_union_left
      exact ⟨hω, hωU⟩
    · apply Set.mem_union_right
      exact Set.mem_ofPred.mpr (lt_of_not_ge hωU)
  have h_union_le : (μ (B ∪ C)).toReal ≤ (μ B).toReal + (μ C).toReal :=
    measureReal_union_le B C
  have h_sub_le : (μ {ω | X ω ≤ g}).toReal ≤ (μ (B ∪ C)).toReal :=
    measureReal_mono h_sub (measure_ne_top _ _)
  have h_C_le : (μ C).toReal ≤ ε := hT
  have ha_pos : 0 < a - g := by linarith
  have h_sub_meas : MeasurableSet B := by
    have h1 : MeasurableSet {ω | X ω ≤ g} :=
      measurableSet_le hX (measurable_const (a := g))
    have h2 : MeasurableSet {ω | a ≤ U ω} :=
      measurableSet_le (measurable_const (a := a)) hU
    exact h1.inter h2
  have h_int_sub : Integrable (U - X) μ := hUi.sub hXi
  have h_int_indicator : Integrable ((B.indicator (fun _ => (1 : ℝ)) : Ω → ℝ)) μ := by
    have h_on : IntegrableOn (fun _ => (1 : ℝ)) B μ :=
      integrableOn_const (hs := measure_ne_top _ _) (hC := by norm_num)
    rw [integrable_indicator_iff h_sub_meas]
    exact h_on
  have h_int_left_func : Integrable (fun ω => (a - g) * (B.indicator (fun _ => (1 : ℝ)) ω)) μ :=
    h_int_indicator.const_mul (a - g)
  have h_pointwise : (fun ω => (a - g) * (B.indicator (fun _ => (1 : ℝ)) ω)) ≤ (U - X) := by
    classical
    intro ω
    dsimp
    by_cases hωB : ω ∈ B
    · have h_ind : B.indicator (fun _ => (1 : ℝ)) ω = 1 := by
        rw [Set.indicator_apply]
        simp [hωB]
      rw [h_ind]
      have hXω : X ω ≤ g := hωB.1
      have hUω : a ≤ U ω := hωB.2
      linarith
    · have h_ind : B.indicator (fun _ => (1 : ℝ)) ω = 0 := by
        rw [Set.indicator_apply]
        simp [hωB]
      rw [h_ind]
      have hUX : X ω ≤ U ω := hXU ω
      nlinarith
  have h_int_ineq : (∫ ω, (a - g) * (B.indicator (fun _ => (1 : ℝ)) ω) ∂μ) ≤ ∫ ω, (U - X) ω ∂μ :=
    integral_mono h_int_left_func h_int_sub h_pointwise
  have h_int_indicator_eq : (∫ ω, (B.indicator (fun _ => (1 : ℝ)) ω) ∂μ) = (μ B).toReal :=
    integral_indicator_one h_sub_meas
  have h_int_left : (∫ ω, (a - g) * (B.indicator (fun _ => (1 : ℝ)) ω) ∂μ) = (a - g) * (μ B).toReal := by
    calc
      (∫ ω, (a - g) * (B.indicator (fun _ => (1 : ℝ)) ω) ∂μ) = (a - g) * (∫ ω, (B.indicator (fun _ => (1 : ℝ)) ω) ∂μ) := by
        rw [integral_const_mul]
      _ = (a - g) * (μ B).toReal := by rw [h_int_indicator_eq]
  have h_int_right : (∫ ω, (U - X) ω ∂μ) = mu - ∫ ω, X ω ∂μ := by
    calc
      (∫ ω, (U - X) ω ∂μ) = (∫ ω, U ω - X ω ∂μ) := by
        refine integral_congr_ae ?_
        filter_upwards with ω
        simp
      _ = (∫ ω, U ω ∂μ) - (∫ ω, X ω ∂μ) := integral_sub hUi hXi
      _ = mu - ∫ ω, X ω ∂μ := by rw [hUm]
  have h_main : (μ B).toReal ≤ (mu - ∫ ω, X ω ∂μ) / (a - g) := by
    rw [h_int_left, h_int_right] at h_int_ineq
    rw [le_div_iff₀ ha_pos]
    nlinarith
  calc
    (μ {ω | X ω ≤ g}).toReal ≤ (μ (B ∪ C)).toReal := h_sub_le
    _ ≤ (μ B).toReal + (μ C).toReal := h_union_le
    _ ≤ (μ B).toReal + ε := by nlinarith
    _ ≤ ((mu - ∫ ω, X ω ∂μ) / (a - g)) + ε := by nlinarith
    _ = (mu - ∫ ω, X ω ∂μ) / ((1 - t) * mu - g) + ε := by rw [ha]

/-- Chernoff in KL form (Lemma 11.1 (2) of the paper): `P(Bin(n, p) < k) ≤ exp(-n KL(k/n, p))` for
`k < n p`. -/
theorem chernoff_binLt_proof (n k : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hk : (k : ℝ) < n * p) : binLt n p k ≤ Real.exp (-(n * klBern (k / n) p)) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp [binLt]
    positivity
  · have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hqpos : 0 < 1 - p := by linarith
    have hnpos : 0 < (n : ℝ) := by
      by_contra! h
      have hn0 : (n : ℝ) ≤ 0 := by exact mod_cast h
      have : (k : ℝ) ≤ 0 := by nlinarith
      linarith
    have hk_lt_n : (k : ℝ) < (n : ℝ) := by
      nlinarith
    have hk_lt_n_nat : k < n := by
      exact mod_cast hk_lt_n
    have hnkpos : 0 < (n : ℝ) - (k : ℝ) := by linarith
    set q := 1 - p with hqdef
    have ha_lt_p : (k : ℝ) / (n : ℝ) < p := by
      have h := (div_lt_div_iff_of_pos_right hnpos).mpr hk
      -- h : (k : ℝ) / (n : ℝ) < (n * p) / (n : ℝ)
      have h2 : (n * p) / (n : ℝ) = p := by field_simp [ne_of_gt hnpos]
      rwa [h2] at h
    set θ := (k : ℝ) * q / (((n : ℝ) - (k : ℝ)) * p) with hθdef
    have hθpos : 0 < θ := by
      rw [hθdef]
      refine div_pos (mul_pos hkpos hqpos) (mul_pos hnkpos hp0)
    have hθ_lt_one : θ < 1 := by
      rw [hθdef]
      have hnum : (k : ℝ) * q < ((n : ℝ) - (k : ℝ)) * p := by
        dsimp [q]
        nlinarith
      exact (div_lt_one (by nlinarith)).mpr hnum
    have hθ_le_one : θ ≤ 1 := hθ_lt_one.le
    have h_pθ_plus_q : p * θ + q = (n : ℝ) * q / ((n : ℝ) - (k : ℝ)) := by
      rw [hθdef, hqdef]
      field_simp [ne_of_gt hnkpos]
      ring
    have h_main : θ ^ k * binLt n p k ≤ (p * θ + q) ^ n := by
      rw [binLt]
      have h_nonneg_term : ∀ i, 0 ≤ (n.choose i : ℝ) * (p * θ) ^ i * q ^ (n - i) := by
        intro i; positivity
      calc
        θ ^ k * (∑ i ∈ Finset.range k, ((n.choose i : ℝ) * p ^ i * q ^ (n - i)))
            = ∑ i ∈ Finset.range k, ((n.choose i : ℝ) * p ^ i * q ^ (n - i) * θ ^ k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        _ ≤ ∑ i ∈ Finset.range k, ((n.choose i : ℝ) * (p * θ) ^ i * q ^ (n - i)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi_lt_k : i < k := Finset.mem_range.1 hi
          have hi_le_k : i ≤ k := Nat.le_of_lt hi_lt_k
          have hθpow : θ ^ k ≤ θ ^ i :=
            pow_le_pow_of_le_one hθpos.le hθ_le_one hi_le_k
          have h_nonneg : 0 ≤ (n.choose i : ℝ) * p ^ i * q ^ (n - i) := by positivity
          calc
            (n.choose i : ℝ) * p ^ i * q ^ (n - i) * θ ^ k
                = ((n.choose i : ℝ) * p ^ i * q ^ (n - i)) * θ ^ k := by ring
            _ ≤ ((n.choose i : ℝ) * p ^ i * q ^ (n - i)) * θ ^ i :=
              mul_le_mul_of_nonneg_left hθpow h_nonneg
            _ = (n.choose i : ℝ) * (p ^ i * θ ^ i) * q ^ (n - i) := by ring
            _ = (n.choose i : ℝ) * (p * θ) ^ i * q ^ (n - i) := by rw [mul_pow]
        _ ≤ ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * (p * θ) ^ i * q ^ (n - i)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro i hi
            rw [Finset.mem_range] at hi
            rw [Finset.mem_range]
            have : k < n := hk_lt_n_nat
            omega
          · intro i _hi _hnot
            exact h_nonneg_term i
        _ = (p * θ + q) ^ n := by
          rw [add_pow]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
    have h_final_eq : (p * θ + q) ^ n / θ ^ k = Real.exp (-(n * klBern (k / n) p)) := by
      rw [h_pθ_plus_q]
      have hn0' : (n : ℝ) ≠ 0 := by linarith
      have hk0' : (k : ℝ) ≠ 0 := by linarith
      have hp0' : p ≠ 0 := by linarith
      have hq0 : q ≠ 0 := by linarith
      have hnk0 : (n : ℝ) - (k : ℝ) ≠ 0 := by linarith
      have h_one_minus_k_over_n_ne_zero : 1 - (k : ℝ) / (n : ℝ) ≠ 0 := by
        intro hzero
        have : (k : ℝ) / (n : ℝ) = 1 := by linarith
        have hk_eq_n : (k : ℝ) = (n : ℝ) := by
          field_simp [hn0'] at this
          linarith
        have hk_lt_n' : (k : ℝ) < (n : ℝ) := hk_lt_n
        linarith
      have h_log_eq : (n : ℝ) * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) +
          (k : ℝ) * Real.log (((n : ℝ) - (k : ℝ)) * p / ((k : ℝ) * q)) =
          -((n : ℝ) * klBern ((k : ℝ) / (n : ℝ)) p) := by
        dsimp [klBern, q]
        calc
          (n : ℝ) * Real.log ((n : ℝ) * (1 - p) / ((n : ℝ) - (k : ℝ))) +
              (k : ℝ) * Real.log (((n : ℝ) - (k : ℝ)) * p / ((k : ℝ) * (1 - p)))
          = (n : ℝ) * (Real.log ((n : ℝ) * (1 - p)) - Real.log ((n : ℝ) - (k : ℝ))) +
              (k : ℝ) * (Real.log (((n : ℝ) - (k : ℝ)) * p) - Real.log ((k : ℝ) * (1 - p))) := by
            rw [Real.log_div (mul_ne_zero hn0' (by linarith)) hnk0,
              Real.log_div (mul_ne_zero hnk0 hp0') (mul_ne_zero hk0' (by linarith))]
          _ = (n : ℝ) * ((Real.log (n : ℝ) + Real.log (1 - p)) - Real.log ((n : ℝ) - (k : ℝ))) +
              (k : ℝ) * ((Real.log ((n : ℝ) - (k : ℝ)) + Real.log p) - (Real.log (k : ℝ) + Real.log (1 - p))) := by
            rw [Real.log_mul hn0' (by linarith), Real.log_mul hnk0 hp0', Real.log_mul hk0' (by linarith)]
          _ = (n : ℝ) * Real.log (n : ℝ) - (k : ℝ) * Real.log (k : ℝ) -
              ((n : ℝ) - (k : ℝ)) * Real.log ((n : ℝ) - (k : ℝ)) +
              (k : ℝ) * Real.log p + ((n : ℝ) - (k : ℝ)) * Real.log (1 - p) := by
            ring
          _ = -((k : ℝ) * (Real.log ((k : ℝ) / (n : ℝ)) - Real.log p) +
              ((n : ℝ) - (k : ℝ)) * (Real.log (1 - (k : ℝ) / (n : ℝ)) - Real.log (1 - p))) := by
            have h : 1 - (k : ℝ) / (n : ℝ) = ((n : ℝ) - (k : ℝ)) / (n : ℝ) := by field_simp [hn0']
            rw [h]
            rw [Real.log_div hk0' hn0', Real.log_div hnk0 hn0']
            ring
          _ = -((n : ℝ) * (((k : ℝ) / (n : ℝ)) * Real.log (((k : ℝ) / (n : ℝ)) / p) +
              (1 - (k : ℝ) / (n : ℝ)) * Real.log ((1 - (k : ℝ) / (n : ℝ)) / (1 - p)))) := by
            rw [show ((k : ℝ) / (n : ℝ)) * Real.log (((k : ℝ) / (n : ℝ)) / p) =
                ((k : ℝ) / (n : ℝ)) * (Real.log ((k : ℝ) / (n : ℝ)) - Real.log p) by
              rw [Real.log_div (div_ne_zero hk0' hn0') hp0'],
              show (1 - (k : ℝ) / (n : ℝ)) * Real.log ((1 - (k : ℝ) / (n : ℝ)) / (1 - p)) =
                (1 - (k : ℝ) / (n : ℝ)) * (Real.log (1 - (k : ℝ) / (n : ℝ)) - Real.log (1 - p)) by
              rw [Real.log_div h_one_minus_k_over_n_ne_zero (by linarith)]]
            field_simp [hn0']
      calc
        ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) ^ n / θ ^ k
            = (((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) ^ n) * (θ ^ k)⁻¹ := by ring
        _ = (Real.exp (Real.log (((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) ^ n))) *
            (Real.exp (Real.log (θ ^ k)))⁻¹ := by
          rw [Real.exp_log (by positivity), Real.exp_log (by positivity)]
        _ = Real.exp (n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ)))) *
            (Real.exp (k * Real.log θ))⁻¹ := by
          rw [Real.log_pow, Real.log_pow]
        _ = Real.exp (n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ)))) *
            Real.exp (-(k * Real.log θ)) := by rw [Real.exp_neg]
        _ = Real.exp (n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) + (-(k * Real.log θ))) := by
          rw [Real.exp_add]
        _ = Real.exp (n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) - k * Real.log θ) := by ring_nf
        _ = Real.exp (n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) +
            k * Real.log (((n : ℝ) - (k : ℝ)) * p / ((k : ℝ) * q))) := by
          rw [hθdef]
          have h : -k * Real.log ((k : ℝ) * q / (((n : ℝ) - (k : ℝ)) * p)) =
              k * Real.log (((n : ℝ) - (k : ℝ)) * p / ((k : ℝ) * q)) := by
            rw [Real.log_div (mul_ne_zero hk0' (by linarith)) (mul_ne_zero hnk0 hp0'),
              Real.log_div (mul_ne_zero hnk0 hp0') (mul_ne_zero hk0' (by linarith))]
            ring
          have h_inner : n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) - k * Real.log ((k : ℝ) * q / (((n : ℝ) - (k : ℝ)) * p)) =
              n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) + k * Real.log (((n : ℝ) - (k : ℝ)) * p / ((k : ℝ) * q)) := by
            calc
              n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) - k * Real.log ((k : ℝ) * q / (((n : ℝ) - (k : ℝ)) * p))
              = n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) + (-(k * Real.log ((k : ℝ) * q / (((n : ℝ) - (k : ℝ)) * p)))) := by ring
              _ = n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) + ((-k) * Real.log ((k : ℝ) * q / (((n : ℝ) - (k : ℝ)) * p))) := by ring
              _ = n * Real.log ((n : ℝ) * q / ((n : ℝ) - (k : ℝ))) + (k * Real.log (((n : ℝ) - (k : ℝ)) * p / ((k : ℝ) * q))) := by rw [h]
          rw [h_inner]
        _ = Real.exp (-((n : ℝ) * klBern ((k : ℝ) / (n : ℝ)) p)) := by rw [h_log_eq]
    calc
      binLt n p k = (θ ^ k * binLt n p k) / θ ^ k := by
        field_simp [ne_of_gt (pow_pos hθpos k)]
      _ ≤ (p * θ + q) ^ n / θ ^ k := by
        gcongr
      _ = Real.exp (-((n : ℝ) * klBern (k / n) p)) := by
        simpa using h_final_eq

theorem integral_sum_indicator {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Finset ι) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    ∫ ω, ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω ∂μ = ∑ i ∈ s, (μ (A i)).toReal := by
  have hi : ∀ i, Integrable ((A i).indicator (1 : Ω → ℝ)) μ := fun i =>
    (integrable_const (1 : ℝ)).indicator (hA i)
  rw [integral_finsetSum _ fun i _ => hi i]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_indicator_one (hA i), measureReal_def]

theorem integrable_sum_indicator {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Finset ι) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    Integrable (fun ω => ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω) μ :=
  integrable_finsetSum _ fun i _ => ((integrable_const (1 : ℝ)).indicator (hA i) :
    Integrable ((A i).indicator (1 : Ω → ℝ)) μ)

theorem integrable_of_le_sum_indicator {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Finset ι) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXU : ∀ ω, X ω ≤ ∑ i ∈ s, (A i).indicator 1 ω) : Integrable X μ :=
  (integrable_sum_indicator μ s A hA).mono' hX.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
      exact hXU ω)

/-- **Lemma 11.1 (1) of the paper**, its first bound, proved. -/
theorem lemma12_general_proof : lemma12_general := by
  intro Ω ι _ μ _ s A hA hind X hX hX0 hXU mu hmu x hx
  have hU := integral_sum_indicator μ s A hA
  have hc := integral_posPart_le μ s A hA hind
  rw [← hmu] at hU hc
  exact lemma12_of_posPart μ X (fun ω => ∑ i ∈ s, (A i).indicator 1 ω) hX
    (integrable_of_le_sum_indicator μ s A hA X hX hX0 hXU) (integrable_sum_indicator μ s A hA)
    hX0 hXU mu (Real.sqrt mu / 2) hU hc x hx


/-- `t^2/2 ≤ (1 - t) log(1 - t) + t` on `[0, 1)`: the derivative of the difference is `-log(1 - t) - t ≥ 0`. -/
theorem sq_half_le_one_sub_mul_log (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t ^ 2 / 2 ≤ (1 - t) * Real.log (1 - t) + t := by
  set f : ℝ → ℝ := fun x => (1 - x) * Real.log (1 - x) + x - x ^ 2 / 2 with hf
  have hD : Convex ℝ (Set.Ico (0 : ℝ) 1) := convex_Ico 0 1
  have hcont : ContinuousOn f (Set.Ico 0 1) := by
    have h1 : ContinuousOn (fun x : ℝ => Real.log (1 - x)) (Set.Ico 0 1) :=
      ContinuousOn.log (by fun_prop) fun x hx => by linarith [hx.2]
    exact ((continuousOn_const.sub continuousOn_id).mul h1).add continuousOn_id |>.sub
      (by fun_prop)
  have hderiv : ∀ x ∈ interior (Set.Ico (0 : ℝ) 1),
      HasDerivWithinAt f (-Real.log (1 - x) - x) (interior (Set.Ico (0 : ℝ) 1)) x := by
    intro x hx
    rw [interior_Ico] at hx
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((1 - x)⁻¹ * -1) x :=
      (Real.hasDerivAt_log hx1).comp x hsub
    have hall := ((hsub.mul hlog).add (hasDerivAt_id x)).sub ((hasDerivAt_pow 2 x).div_const 2)
    have heq : -1 * Real.log (1 - x) + (1 - x) * ((1 - x)⁻¹ * -1) + 1 - (2 : ℕ) * x ^ (2 - 1) / 2 =
        -Real.log (1 - x) - x := by
      field_simp
      ring
    rw [heq] at hall
    exact hall.hasDerivWithinAt
  have hmono : MonotoneOn f (Set.Ico 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg hD hcont hderiv ?_
    intro x hx
    rw [interior_Ico] at hx
    have := Real.log_le_sub_one_of_pos (show 0 < 1 - x by linarith [hx.2])
    linarith
  have h := hmono ⟨le_refl 0, by norm_num⟩ ⟨ht0, ht1⟩ ht0
  simp only [hf, sub_zero, Real.log_one, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at h
  linarith

/-- The moment generating function of an indicator: `E e^(λ 1_A) ≤ exp(P(A) (e^λ - 1))`. -/
theorem mgf_indicator_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) (l : ℝ) :
    mgf (A.indicator (1 : Ω → ℝ)) μ l ≤ Real.exp ((μ A).toReal * (Real.exp l - 1)) := by
  have h_eq : (fun ω => Real.exp (l * A.indicator (1 : Ω → ℝ) ω)) =
      fun ω => 1 + A.indicator (1 : Ω → ℝ) ω * (Real.exp l - 1) := by
    ext ω
    by_cases h : ω ∈ A <;> simp [h]
  have hint : Integrable (A.indicator (1 : Ω → ℝ)) μ :=
    (integrable_indicator_iff hA).2 (integrableOn_const (measure_ne_top _ _))
  have hm : mgf (A.indicator (1 : Ω → ℝ)) μ l = 1 + (μ A).toReal * (Real.exp l - 1) := by
    rw [mgf, h_eq, integral_add (integrable_const _) (hint.mul_const _), integral_mul_const,
      integral_indicator_one hA, integral_const, measureReal_def, measureReal_def]
    simp
  rw [hm]
  linarith [Real.add_one_le_exp ((μ A).toReal * (Real.exp l - 1))]

/-- The Poisson-binomial lower tail: `P(U < (1 - t) mu) ≤ exp(-t^2 mu/2)` for a sum `U` of
indicators of independent events, `mu = E U`, `t ∈ (0, 1)`. -/
theorem poisson_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (μ {ω | ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω <
        (1 - t) * ∑ i ∈ s, (μ (A i)).toReal}).toReal ≤
      Real.exp (-(t ^ 2 * (∑ i ∈ s, (μ (A i)).toReal) / 2)) := by
  set X : ι → Ω → ℝ := fun i => (A i).indicator (1 : Ω → ℝ) with hX
  have hX_indep : iIndepFun X μ := hind.iIndepFun_indicator
  have hX_meas : ∀ i, Measurable (X i) := fun i => measurable_const.indicator (hA i)
  set mu := ∑ i ∈ s, (μ (A i)).toReal with hmu_def
  have hmu : 0 ≤ mu := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have h1t : 0 < 1 - t := by linarith
  set lam := -Real.log (1 - t) with hlam_def
  have hexp : Real.exp (-lam) = 1 - t := by rw [hlam_def, neg_neg, Real.exp_log h1t]
  have hlam : 0 ≤ lam := by
    have := Real.log_nonpos h1t.le (by linarith)
    linarith
  -- the mgf of the sum
  have hsum : mgf (∑ i ∈ s, X i) μ (-lam) ≤ Real.exp (mu * (Real.exp (-lam) - 1)) := by
    rw [hX_indep.mgf_sum hX_meas s, hmu_def, Finset.sum_mul, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => mgf_indicator_le μ (A i) (hA i) _)
  have hSmeas : Measurable (∑ i ∈ s, X i) := by
    rw [show (∑ i ∈ s, X i) = fun a => ∑ i ∈ s, X i a from by ext a; simp [Finset.sum_apply]]
    exact Finset.measurable_sum s fun i _ => hX_meas i
  have hint : Integrable (fun ω => Real.exp (-lam * (∑ i ∈ s, X i) ω)) μ := by
    refine Integrable.of_bound ((measurable_const.mul hSmeas).exp).aestronglyMeasurable 1
      (ae_of_all _ fun ω => ?_)
    have h0 : 0 ≤ (∑ i ∈ s, X i) ω := by
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  have hch := measure_le_le_exp_mul_mgf ((1 - t) * mu) (by linarith : -lam ≤ 0) hint
  have hsub : {ω | ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω < (1 - t) * mu} ⊆
      {ω | (∑ i ∈ s, X i) ω ≤ (1 - t) * mu} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Finset.sum_apply, hX] at hω ⊢
    exact hω.le
  have hle : (μ {ω | ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω < (1 - t) * mu}).toReal ≤
      Real.exp (lam * ((1 - t) * mu) + mu * (Real.exp (-lam) - 1)) := by
    rw [Real.exp_add]
    calc _ ≤ μ.real {ω | (∑ i ∈ s, X i) ω ≤ (1 - t) * mu} := by
          rw [← measureReal_def]; exact measureReal_mono hsub
      _ ≤ _ := hch
      _ ≤ _ := by
          rw [neg_neg]
          exact mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
  refine hle.trans (Real.exp_le_exp.2 ?_)
  rw [hexp, hlam_def]
  have hq := sq_half_le_one_sub_mul_log t ht0.le ht1
  nlinarith [mul_le_mul_of_nonneg_right hq hmu]

/-- **Lemma 11.1 (1) of the paper**, its second bound, from the Poisson-binomial lower tail. -/
theorem lemma12'_general_proof : lemma12'_general := by
  intro Ω ι _ μ _ s A hA hind X hX hX0 hXU mu hmu t g ht0 ht1 hg
  have hU := integral_sum_indicator μ s A hA
  have hT := poisson_lower_tail μ s A hA hind t ht0 ht1
  rw [← hmu] at hU hT
  have hUm : Measurable fun ω => ∑ i ∈ s, (A i).indicator (1 : Ω → ℝ) ω :=
    Finset.measurable_sum _ fun i _ => measurable_const.indicator (hA i)
  exact lemma12p_of_tail μ X (fun ω => ∑ i ∈ s, (A i).indicator 1 ω) hX hUm
    (integrable_of_le_sum_indicator μ s A hA X hX hX0 hXU) (integrable_sum_indicator μ s A hA)
    hX0 hXU mu hU t g _ hg hT

end FrogModel.D3.Iface
