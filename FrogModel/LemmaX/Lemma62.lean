module

public import FrogModel.LemmaX.CertStatement
public import FrogModel.LemmaX.Coupling
public import FrogModel.Lemmas.Quantile
public import FrogModel.Cert.Sound

@[expose] public section

/-!
# `Phi_4(H*) ≤ H*` from the dominating output, (I3b) and (I4)

The last step of the proof of Theorem 6.5 of the paper. The plan of (I4) couples a part `s ≤ L`
of the dominating output below the finite part of `H*`. The rest
`nu = Out_dom - s = (L - s) + D` has mass `eps`; its last coordinate has upper tails below those
of the tail part `Q` of `H*`: up to `T + 1` because `|nu| = eps = Q(Z ≥ T + 1)`, beyond because
only `D` contributes and `theta^-t S_ov ≤ eps rho^(t - T - 1)` ((I3b), `theta rho ≥ 1`).
The quantile coupling of the last coordinates (`subCoupling_enat`) and `G ≤ Z_t` iff
`G(4) ≤ t` for a non-decreasing `G` (`subCoupling_constLast`) give `nu ≤ Q`.

Couplings of finite measures (`SubCoupling`, no condition on the mass) add, scale, and compose
on a countable type (`subCoupling_trans`, from `couplingLE_trans`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace FrogModel.LemmaX

/-- The coupling order for finite measures: a measure on pairs with marginals `P` and `Q`,
carried by `{p | p.1 ≤ p.2}` (no condition on the mass). -/
def SubCoupling {α : Type*} [MeasurableSpace α] [LE α] (P Q : Measure α) : Prop :=
  ∃ π : Measure (α × α), π.map Prod.fst = P ∧ π.map Prod.snd = Q ∧ ∀ᵐ p ∂π, p.1 ≤ p.2

/-- The constant block `(t, ..., t)`. -/
def constBlock (J : ℕ) (t : ℕ∞) : Fin J → ℕ∞ := fun _ => t

end FrogModel.LemmaX

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaX FrogModel.Cert

/-- Sub-couplings add. -/
theorem FrogModel.LemmaX.subCoupling_add {α : Type*} [MeasurableSpace α] [LE α]
    {P Q P' Q' : Measure α} (h : SubCoupling P Q) (h' : SubCoupling P' Q') :
    SubCoupling (P + P') (Q + Q') := by
  rcases h with ⟨π, hπ_fst, hπ_snd, hπ_le⟩
  rcases h' with ⟨π', hπ'_fst, hπ'_snd, hπ'_le⟩
  refine ⟨π + π', ?_, ?_, ?_⟩
  · rw [Measure.map_add π π' measurable_fst, hπ_fst, hπ'_fst]
  · rw [Measure.map_add π π' measurable_snd, hπ_snd, hπ'_snd]
  · rw [ae_add_measure_iff]
    exact ⟨hπ_le, hπ'_le⟩

/-- Sub-couplings scale. -/
theorem FrogModel.LemmaX.subCoupling_smul {α : Type*} [MeasurableSpace α] [LE α]
    {P Q : Measure α} (c : ℝ≥0∞) (h : SubCoupling P Q) : SubCoupling (c • P) (c • Q) := by
  rcases h with ⟨π, hπ_fst, hπ_snd, hπ_le⟩
  refine ⟨c • π, ?_, ?_, ?_⟩
  · rw [Measure.map_smul c (measurable_fst.aemeasurable (μ := π)), hπ_fst]
  · rw [Measure.map_smul c (measurable_snd.aemeasurable (μ := π)), hπ_snd]
  · exact Measure.ae_smul_measure hπ_le c

/-- The two marginals of a sub-coupling have the same mass. -/
theorem FrogModel.LemmaX.subCoupling_univ {α : Type*} [MeasurableSpace α] [LE α]
    {P Q : Measure α} (h : SubCoupling P Q) : P Set.univ = Q Set.univ := by
  rcases h with ⟨π, hP, hQ, _⟩
  have hP_univ : P Set.univ = π Set.univ := by
    rw [← hP, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  have hQ_univ : Q Set.univ = π Set.univ := by
    rw [← hQ, Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ]
  rw [hP_univ, hQ_univ]

/-- A sub-coupling of a probability measure is a coupling. -/
theorem FrogModel.LemmaX.couplingLE_of_subCoupling {α : Type*} [MeasurableSpace α] [LE α]
    {P Q : Measure α} [IsProbabilityMeasure P] (h : SubCoupling P Q) : CouplingLE P Q := by
  rcases h with ⟨π, hfst, hsnd, hle⟩
  have hπ : IsProbabilityMeasure π := by
    refine ⟨?h⟩
    calc
      π Set.univ = π (Prod.fst ⁻¹' Set.univ) := by simp
      _ = (π.map Prod.fst) Set.univ := by rw [Measure.map_apply measurable_fst MeasurableSet.univ]
      _ = P Set.univ := by rw [hfst]
      _ = 1 := measure_univ
  exact ⟨π, hπ, hfst, hsnd, hle⟩

/-- A coupling is a sub-coupling. -/
theorem FrogModel.LemmaX.subCoupling_of_couplingLE {α : Type*} [MeasurableSpace α] [LE α]
    {P Q : Measure α} (h : CouplingLE P Q) : SubCoupling P Q := by
  rcases h with ⟨π, hπ_prob, hπ_fst, hπ_snd, hπ_le⟩
  exact ⟨π, hπ_fst, hπ_snd, hπ_le⟩

/-- Sub-couplings compose on a countable type: scale to probability measures and glue. -/
theorem FrogModel.LemmaX.subCoupling_trans {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [Preorder α] {P Q R : Measure α}
    [IsFiniteMeasure P] (h₁ : SubCoupling P Q) (h₂ : SubCoupling Q R) : SubCoupling P R := by
  have hPQ := subCoupling_univ h₁
  have hQR := subCoupling_univ h₂
  by_cases h0 : P Set.univ = 0
  · have hP : P = 0 := Measure.measure_univ_eq_zero.1 h0
    have hR : R = 0 := Measure.measure_univ_eq_zero.1 (by rw [← hQR, ← hPQ, h0])
    subst hP hR
    exact ⟨0, by simp, by simp, by simp⟩
  · have hT : P Set.univ ≠ ⊤ := measure_ne_top P _
    have hscale : ∀ μ : Measure α, P Set.univ • ((P Set.univ)⁻¹ • μ) = μ := by
      intro μ
      rw [smul_smul, ENNReal.mul_inv_cancel h0 hT, one_smul]
    have hP' : IsProbabilityMeasure ((P Set.univ)⁻¹ • P) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hT]⟩
    have hQ' : IsProbabilityMeasure ((P Set.univ)⁻¹ • Q) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, ← hPQ, ENNReal.inv_mul_cancel h0 hT]⟩
    have k1 := couplingLE_of_subCoupling (subCoupling_smul (P Set.univ)⁻¹ h₁)
    have k2 := couplingLE_of_subCoupling (subCoupling_smul (P Set.univ)⁻¹ h₂)
    have k3 := subCoupling_smul (P Set.univ)
      (subCoupling_of_couplingLE (couplingLE_trans _ _ _ k1 k2))
    rwa [hscale, hscale] at k3

/-- **The quantile coupling** on `ℕ∞`, in measure form: two finite measures of equal mass whose
upper tails compare are sub-coupled below. -/
theorem FrogModel.LemmaX.subCoupling_enat {μ ν : Measure ℕ∞} [IsFiniteMeasure ν]
    (hmass : μ Set.univ = ν Set.univ) (htail : ∀ t : ℕ∞, μ {x | t ≤ x} ≤ ν {x | t ≤ x}) :
    SubCoupling μ ν := by
  -- ℕ∞ is countable with measurable singletons
  have h_countable : Countable ℕ∞ := by infer_instance
  have h_meas_singleton : MeasurableSingletonClass ℕ∞ := by infer_instance
  -- ν univ is finite
  have hν_univ_ne_top : ν Set.univ ≠ ⊤ := measure_ne_top ν Set.univ
  -- Define the atom functions
  set μ' : ℕ∞ → ENNReal := fun x => μ {x} with hμ'
  set ν' : ℕ∞ → ENNReal := fun x => ν {x} with hν'
  -- The total mass of ν' is finite
  have hν'_fin : ∑' x, ν' x ≠ ⊤ := by
    have hsum : ∑' x : ℕ∞, ν' x = ν Set.univ := by
      calc
        ∑' x : ℕ∞, ν' x = ∑' x : ℕ∞, (Set.univ.indicator (fun x => ν {x}) x) := by simp [hν']
        _ = ν Set.univ := by
          rw [Measure.tsum_indicator_apply_singleton ν Set.univ MeasurableSet.univ]
    rw [hsum]
    exact hν_univ_ne_top
  -- Total masses are equal
  have hmass' : ∑' x, μ' x = ∑' x, ν' x := by
    have hμ_sum : ∑' x : ℕ∞, μ' x = μ Set.univ := by
      calc
        ∑' x : ℕ∞, μ' x = ∑' x : ℕ∞, (Set.univ.indicator (fun x => μ {x}) x) := by simp [hμ']
        _ = μ Set.univ := by
          rw [Measure.tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ]
    have hν_sum : ∑' x : ℕ∞, ν' x = ν Set.univ := by
      calc
        ∑' x : ℕ∞, ν' x = ∑' x : ℕ∞, (Set.univ.indicator (fun x => ν {x}) x) := by simp [hν']
        _ = ν Set.univ := by
          rw [Measure.tsum_indicator_apply_singleton ν Set.univ MeasurableSet.univ]
    rw [hμ_sum, hν_sum, hmass]
  -- Tail condition
  have htail' : ∀ t : ℕ∞, ∑' x, (if t ≤ x then μ' x else 0) ≤ ∑' x, (if t ≤ x then ν' x else 0) := by
    intro t
    have hmeas : MeasurableSet {x : ℕ∞ | t ≤ x} := by
      apply Set.Countable.measurableSet
      apply Set.Countable.mono (fun x _ => Set.mem_univ x)
      exact Set.countable_univ
    have hμ_tail : ∑' x : ℕ∞, (if t ≤ x then μ' x else 0) = μ {x | t ≤ x} := by
      calc
        ∑' x : ℕ∞, (if t ≤ x then μ' x else 0) =
            ∑' x : ℕ∞, ({x | t ≤ x}.indicator (fun x => μ {x}) x) := by
          simp [hμ', Set.indicator]
        _ = μ {x | t ≤ x} := by
          rw [Measure.tsum_indicator_apply_singleton μ {x | t ≤ x} hmeas]
    have hν_tail : ∑' x : ℕ∞, (if t ≤ x then ν' x else 0) = ν {x | t ≤ x} := by
      calc
        ∑' x : ℕ∞, (if t ≤ x then ν' x else 0) =
            ∑' x : ℕ∞, ({x | t ≤ x}.indicator (fun x => ν {x}) x) := by
          simp [hν', Set.indicator]
        _ = ν {x | t ≤ x} := by
          rw [Measure.tsum_indicator_apply_singleton ν {x | t ≤ x} hmeas]
    rw [hμ_tail, hν_tail]
    exact htail t
  -- Apply quantile coupling to get the coupling function
  obtain ⟨π', hπ'_row, hπ'_col, hπ'_support⟩ :=
    FrogModel.Order.quantile_coupling μ' ν' hν'_fin hmass' htail'
  -- Build the measure π from π'
  set π : Measure (ℕ∞ × ℕ∞) :=
    Measure.sum fun (q : ℕ∞ × ℕ∞) => π' q • Measure.dirac q with hπ
  have hmeas_support : MeasurableSet {p : ℕ∞ × ℕ∞ | p.1 ≤ p.2} := by
    apply Set.Countable.measurableSet
    apply Set.Countable.mono (fun p _ => Set.mem_univ p)
    exact Set.countable_univ
  classical
  refine ⟨π, ?_, ?_, ?_⟩
  · -- π.map Prod.fst = μ
    have h_marginal_fst : π.map Prod.fst = μ := by
      ext s hs
      rw [Measure.map_apply measurable_fst hs]
      have h_preimage : Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set ℕ∞) := by
        ext ⟨a, b⟩; simp
      rw [hπ, h_preimage, Measure.sum_apply _ (hs.prod MeasurableSet.univ)]
      simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply]
      -- Now we have: ∑' (p : ℕ∞ × ℕ∞), π' p * (if p ∈ s ×ˢ Set.univ then 1 else 0) = μ s
      calc
        ∑' (p : ℕ∞ × ℕ∞), π' p * (if p ∈ s ×ˢ (Set.univ : Set ℕ∞) then 1 else 0) =
            ∑' (p : ℕ∞ × ℕ∞), (if p.1 ∈ s then π' p else 0) := by
          refine tsum_congr (fun p => ?_)
          simp [Set.mem_prod]
        _ = ∑' (a : ℕ∞) (b : ℕ∞), (if a ∈ s then π' (a, b) else 0) := by
          rw [ENNReal.tsum_prod']
        _ = ∑' (a : ℕ∞), (if a ∈ s then ∑' (b : ℕ∞), π' (a, b) else 0) := by
          refine tsum_congr (fun a => ?_)
          split_ifs with ha
          · simp
          · simp
        _ = ∑' (a : ℕ∞), (if a ∈ s then μ' a else 0) := by
          simp [hπ'_row]
        _ = ∑' (a : ℕ∞), (Set.indicator s (fun x => μ {x}) a) := by
          simp [hμ', Set.indicator]
        _ = μ s := by
          rw [Measure.tsum_indicator_apply_singleton μ s hs]
    exact h_marginal_fst
  · -- π.map Prod.snd = ν
    have h_marginal_snd : π.map Prod.snd = ν := by
      ext s hs
      rw [Measure.map_apply measurable_snd hs]
      have h_preimage : Prod.snd ⁻¹' s = (Set.univ : Set ℕ∞) ×ˢ s := by
        ext ⟨a, b⟩; simp
      rw [hπ, h_preimage, Measure.sum_apply _ (MeasurableSet.univ.prod hs)]
      simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply]
      calc
        ∑' (p : ℕ∞ × ℕ∞), π' p * (if p ∈ (Set.univ : Set ℕ∞) ×ˢ s then 1 else 0) =
            ∑' (p : ℕ∞ × ℕ∞), (if p.2 ∈ s then π' p else 0) := by
          refine tsum_congr (fun p => ?_)
          simp [Set.mem_prod]
        _ = ∑' (a : ℕ∞) (b : ℕ∞), (if b ∈ s then π' (a, b) else 0) := by
          rw [ENNReal.tsum_prod']
        _ = ∑' (b : ℕ∞), ∑' (a : ℕ∞), (if b ∈ s then π' (a, b) else 0) := by
          rw [ENNReal.tsum_comm]
        _ = ∑' (b : ℕ∞), (if b ∈ s then ∑' (a : ℕ∞), π' (a, b) else 0) := by
          refine tsum_congr (fun b => ?_)
          split_ifs with hb
          · simp
          · simp
        _ = ∑' (b : ℕ∞), (if b ∈ s then ν' b else 0) := by
          simp [hπ'_col]
        _ = ∑' (b : ℕ∞), (Set.indicator s (fun x => ν {x}) b) := by
          simp [hν', Set.indicator]
        _ = ν s := by
          rw [Measure.tsum_indicator_apply_singleton ν s hs]
    exact h_marginal_snd
  · -- ∀ᵐ p ∂π, p.1 ≤ p.2
    rw [hπ]
    -- Use ae_sum_iff to reduce to each component
    refine ((Measure.ae_sum_iff (μ := fun q => π' q • Measure.dirac q)).mpr ?_)
    intro q
    by_cases hq : π' q = 0
    · -- If π' q = 0, then 0 • Measure.dirac q = 0, and ae of 0 is ⊤
      rw [hq]
      simp
    · -- If π' q ≠ 0, use ae_ennreal_smul_measure_iff to remove the scalar
      apply ((Measure.ae_ennreal_smul_measure_iff (c := π' q) (μ := Measure.dirac q)
        (p := fun x => x.1 ≤ x.2) hq).mpr)
      -- Now goal: ∀ᵐ x ∂Measure.dirac q, x.1 ≤ x.2
      rw [ae_dirac_iff hmeas_support]
      -- Goal: q.1 ≤ q.2
      exact hπ'_support q.1 q.2 hq

/-- A non-decreasing block lies below the constant block of its last value. -/
theorem FrogModel.LemmaX.subCoupling_constLast (ν : Measure (Fin 4 → ℕ∞))
    (h : ∀ᵐ x ∂ν, Monotone x) :
    SubCoupling ν ((ν.map fun x => x 3).map (constBlock 4)) := by
  set π := ν.map (fun x => (x, constBlock 4 (x 3))) with hπ
  have h_meas_prod : Measurable (fun (x : Fin 4 → ℕ∞) => (x, constBlock 4 (x 3))) := by
    apply Measurable.prodMk measurable_id
    apply measurable_of_countable
  have h_meas_constBlock : Measurable (constBlock 4 : ℕ∞ → Fin 4 → ℕ∞) :=
    measurable_of_countable _
  refine ⟨π, ?_, ?_, ?_⟩
  · -- π.map Prod.fst = ν
    calc
      π.map Prod.fst = (ν.map (fun x => (x, constBlock 4 (x 3)))).map Prod.fst := rfl
      _ = ν.map (Prod.fst ∘ (fun x => (x, constBlock 4 (x 3)))) := by
        rw [MeasureTheory.Measure.map_map measurable_fst h_meas_prod]
      _ = ν.map (fun x => x) := rfl
      _ = ν := MeasureTheory.Measure.map_id
  · -- π.map Prod.snd = (ν.map (fun x => x 3)).map (constBlock 4)
    calc
      π.map Prod.snd = (ν.map (fun x => (x, constBlock 4 (x 3)))).map Prod.snd := rfl
      _ = ν.map (Prod.snd ∘ (fun x => (x, constBlock 4 (x 3)))) := by
        rw [MeasureTheory.Measure.map_map measurable_snd h_meas_prod]
      _ = ν.map (fun x => constBlock 4 (x 3)) := rfl
      _ = ν.map (constBlock 4 ∘ (fun x => x 3)) := rfl
      _ = (ν.map (fun x => x 3)).map (constBlock 4) := by
        rw [MeasureTheory.Measure.map_map h_meas_constBlock (measurable_pi_apply 3)]
  · -- ∀ᵐ p ∂π, p.1 ≤ p.2
    have h_countable : Countable ((Fin 4 → ℕ∞) × (Fin 4 → ℕ∞)) := by
      infer_instance
    have h_measurableSet : MeasurableSet {p : (Fin 4 → ℕ∞) × (Fin 4 → ℕ∞) | p.1 ≤ p.2} := by
      have h_countable_set : Set.Countable (Set.univ : Set ((Fin 4 → ℕ∞) × (Fin 4 → ℕ∞))) :=
        Set.countable_univ
      have h_subset : {p : (Fin 4 → ℕ∞) × (Fin 4 → ℕ∞) | p.1 ≤ p.2} ⊆ Set.univ := by
        intro p hp; exact Set.mem_univ p
      have h_countable_le : Set.Countable {p : (Fin 4 → ℕ∞) × (Fin 4 → ℕ∞) | p.1 ≤ p.2} :=
        Set.Countable.mono h_subset h_countable_set
      exact Set.Countable.measurableSet h_countable_le
    rw [MeasureTheory.ae_map_iff h_meas_prod.aemeasurable h_measurableSet]
    filter_upwards [h] with x hx
    have hx_mono : Monotone x := hx
    intro i
    have hi : i ≤ (3 : Fin 4) := Fin.le_val_last i
    exact hx_mono hi

/-- The constant blocks preserve sub-couplings. -/
theorem FrogModel.LemmaX.subCoupling_map_constBlock (J : ℕ) {μ ν : Measure ℕ∞}
    (h : SubCoupling μ ν) : SubCoupling (μ.map (constBlock J)) (ν.map (constBlock J)) := by
  rcases h with ⟨π, hπ_fst, hπ_snd, hπ_le⟩
  set f : ℕ∞ × ℕ∞ → (Fin J → ℕ∞) × (Fin J → ℕ∞) :=
    fun p => (constBlock J p.1, constBlock J p.2) with hf_def
  have h_constBlock_meas : Measurable (constBlock J) := by
    rw [measurable_pi_iff]
    intro i
    have : (fun x : ℕ∞ => (constBlock J x) i) = id := by
      ext x; simp [constBlock]
    simpa [this] using measurable_id
  have hf_meas : Measurable f := by
    dsimp [f]
    refine Measurable.prodMk ?_ ?_
    · exact h_constBlock_meas.comp measurable_fst
    · exact h_constBlock_meas.comp measurable_snd
  have hf_aemeas : AEMeasurable f π := hf_meas.aemeasurable
  have h_set_le : MeasurableSet {z : (Fin J → ℕ∞) × (Fin J → ℕ∞) | z.1 ≤ z.2} :=
    MeasurableSet.of_discrete
  refine ⟨π.map f, ?_, ?_, ?_⟩
  · -- (π.map f).map Prod.fst = μ.map (constBlock J)
    calc
      (π.map f).map Prod.fst = π.map (Prod.fst ∘ f) := by
        rw [Measure.map_map measurable_fst hf_meas]
      _ = π.map (fun p : ℕ∞ × ℕ∞ => constBlock J p.1) := rfl
      _ = π.map ((constBlock J) ∘ Prod.fst) := rfl
      _ = (π.map Prod.fst).map (constBlock J) := by
        rw [← Measure.map_map h_constBlock_meas measurable_fst]
      _ = μ.map (constBlock J) := by rw [hπ_fst]
  · -- (π.map f).map Prod.snd = ν.map (constBlock J)
    calc
      (π.map f).map Prod.snd = π.map (Prod.snd ∘ f) := by
        rw [Measure.map_map measurable_snd hf_meas]
      _ = π.map (fun p : ℕ∞ × ℕ∞ => constBlock J p.2) := rfl
      _ = π.map ((constBlock J) ∘ Prod.snd) := rfl
      _ = (π.map Prod.snd).map (constBlock J) := by
        rw [← Measure.map_map h_constBlock_meas measurable_snd]
      _ = ν.map (constBlock J) := by rw [hπ_snd]
  · -- ∀ᵐ q ∂π.map f, q.1 ≤ q.2
    rw [ae_map_iff hf_aemeas h_set_le]
    filter_upwards [hπ_le] with p hp
    intro i
    exact hp

/-- The tail law is carried by the constant blocks. -/
theorem FrogModel.Cert.Data.tailLaw_eq_map_const (D : Data) (i : Fin D.J) :
    D.tailLaw = (D.tailLaw.map fun B => B i).map (constBlock D.J) := by
  have hmeas_proj : Measurable fun (B : Fin D.J → ℕ∞) => B i :=
    measurable_pi_apply i
  have hmeas_const : Measurable (constBlock D.J) :=
    measurable_of_countable (constBlock D.J)
  calc
    D.tailLaw = (D.tailLaw.map fun B => B i).map (constBlock D.J) := by
      -- Use Measure.map_map to compose the two maps
      rw [Measure.map_map hmeas_const hmeas_proj]
      -- Now the goal is D.tailLaw = D.tailLaw.map ((constBlock D.J) ∘ (fun B => B i))
      -- But (constBlock D.J) ∘ (fun B => B i) = fun B => fun _ => B i
      -- We need to show that pushing forward tailLaw by this map gives tailLaw back
      dsimp [Data.tailLaw]
      have hmeas_comp : Measurable ((constBlock D.J) ∘ (fun (B : Fin D.J → ℕ∞) => B i)) :=
        hmeas_const.comp hmeas_proj
      rw [Measure.map_sum hmeas_comp.aemeasurable]
      refine Measure.sum_congr fun n => ?_
      rw [Measure.map_smul (ENNReal.ofReal (((1 - D.rho) * D.rho ^ n : ℚ) : ℝ)) hmeas_comp.aemeasurable,
        Measure.map_dirac,
        show (constBlock D.J ∘ (fun (B : Fin D.J → ℕ∞) => B i)) (fun _ : Fin D.J => ((D.T + 1 + n : ℕ) : ℕ∞)) =
          fun _ : Fin D.J => ((D.T + 1 + n : ℕ) : ℕ∞) by
        rfl]

/-- The upper tail of the tail law: `P(Z ≥ T + 1 + n) = rho^n`. -/
theorem FrogModel.Cert.Data.tailLaw_tail (D : Data) (h0 : D.I0) (i : Fin D.J) (n : ℕ) :
    D.tailLaw {B | ((D.T + 1 + n : ℕ) : ℕ∞) ≤ B i} = ENNReal.ofReal ((D.rho : ℝ) ^ n) := by
  rcases h0 with ⟨hJ, hT, heps_pos, heps_lt1, hrho_pos, hrho_lt1, hphi⟩
  have hrho_pos' : 0 ≤ (D.rho : ℝ) := by exact_mod_cast hrho_pos.le
  have hrho_lt1' : (D.rho : ℝ) < 1 := by exact_mod_cast hrho_lt1
  set s := {B : Fin D.J → ℕ∞ | ((D.T + 1 + n : ℕ) : ℕ∞) ≤ B i} with hs
  have h_tailLaw_def : D.tailLaw = Measure.sum fun m : ℕ =>
      ENNReal.ofReal (((1 - D.rho) * D.rho ^ m : ℚ) : ℝ) • Measure.dirac fun _ => ((D.T + 1 + m : ℕ) : ℕ∞) := rfl
  rw [h_tailLaw_def]
  rw [Measure.sum_apply_of_countable]
  simp_rw [Measure.smul_apply]
  simp_rw [Measure.dirac_apply]
  -- Now we have ∑' m, ENNReal.ofReal (((1 - D.rho) * D.rho ^ m : ℚ) : ℝ) • s.indicator 1 (fun _ => ((D.T + 1 + m : ℕ) : ℕ∞))
  have h_indicator : ∀ m : ℕ, s.indicator (1 : (Fin D.J → ℕ∞) → ℝ≥0∞) (fun _ => ((D.T + 1 + m : ℕ) : ℕ∞)) =
      (if n ≤ m then 1 else 0) := by
    intro m
    rw [Set.indicator_apply]
    by_cases hnm : n ≤ m
    · have hmem : (fun _ => (D.T + 1 + m : ℕ∞)) ∈ s := by
        rw [hs, Set.mem_ofPred_eq]
        have hle_nat : D.T + 1 + n ≤ D.T + 1 + m := Nat.add_le_add_left hnm (D.T + 1)
        simpa using (Nat.cast_le (α := ℕ∞)).mpr hle_nat
      simp [hmem, hnm]
    · have hnotmem : (fun _ => (D.T + 1 + m : ℕ∞)) ∉ s := by
        rw [hs, Set.mem_ofPred_eq]
        intro hle
        have hle_nat : D.T + 1 + n ≤ D.T + 1 + m := (Nat.cast_le (α := ℕ∞)).mp hle
        omega
      simp [hnotmem, hnm]
  simp_rw [h_indicator]
  -- Now we have ∑' m, ENNReal.ofReal (((1 - D.rho) * D.rho ^ m : ℚ) : ℝ) • (if n ≤ m then 1 else 0)
  -- Simplify the smul using tsum_congr
  have h_prod_simp : ∀ m : ℕ, ENNReal.ofReal (((1 - D.rho) * D.rho ^ m : ℚ) : ℝ) • (if n ≤ m then (1 : ℝ≥0∞) else 0) =
      (if n ≤ m then ENNReal.ofReal (((1 - D.rho) * D.rho ^ m : ℚ) : ℝ) else 0) := by
    intro m
    by_cases hnm : n ≤ m
    · simp [hnm]
    · simp [hnm]
  rw [tsum_congr h_prod_simp]
  -- Now we have ∑' m, (if n ≤ m then ENNReal.ofReal (((1 - D.rho) * D.rho ^ m : ℚ) : ℝ) else 0)
  -- Reindex using the equivalence k ↦ n + k
  let s_indicator : Set ℕ := {m | n ≤ m}
  let e : ℕ ≃ {m : ℕ // n ≤ m} := {
    toFun := fun k => ⟨n + k, Nat.le_add_right n k⟩
    invFun := fun m => m.val - n
    left_inv := fun k => Nat.add_sub_cancel_left n k
    right_inv := fun m => by
      ext
      exact Nat.add_sub_cancel' m.property
  }
  have h_reindex : ∑' m : ℕ, (if n ≤ m then ENNReal.ofReal (((1 - D.rho) * D.rho ^ m : ℚ) : ℝ) else 0) =
      ∑' k : ℕ, ENNReal.ofReal (((1 - D.rho) * D.rho ^ (n + k) : ℚ) : ℝ) := by
    let f : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (((1 - D.rho) * D.rho ^ m : ℚ) : ℝ)
    have h1 : ∑' m : ℕ, (if n ≤ m then f m else 0) = ∑' m : ℕ, (s_indicator.indicator f m) := by
      refine tsum_congr fun m => ?_
      simp [s_indicator, Set.indicator]
    have h2 : ∑' m : ℕ, (s_indicator.indicator f m) = ∑' (m : {m : ℕ // n ≤ m}), f (m.val) :=
      (tsum_subtype s_indicator f).symm
    have h3 : ∑' (m : {m : ℕ // n ≤ m}), f (m.val) = ∑' k : ℕ, f ((e k).val) := by
      simpa using (Equiv.tsum_eq e (fun (x : {m : ℕ // n ≤ m}) => f (x.val))).symm
    have h4 : ∑' k : ℕ, f ((e k).val) = ∑' k : ℕ, ENNReal.ofReal (((1 - D.rho) * D.rho ^ (n + k) : ℚ) : ℝ) := by
      simp [e, f]
    rw [h1, h2, h3, h4]
  rw [h_reindex]
  -- Now we have ∑' k, ENNReal.ofReal (((1 - D.rho) * D.rho ^ (n + k) : ℚ) : ℝ)
  -- Push the cast through
  have h_push_cast : ∀ k : ℕ, ENNReal.ofReal (((1 - D.rho) * D.rho ^ (n + k) : ℚ) : ℝ) =
      ENNReal.ofReal ((1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ (n + k)) := by
    intro k
    push_cast
    simp
  simp_rw [h_push_cast]
  -- Now we have ∑' k, ENNReal.ofReal ((1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ (n + k))
  -- Use tail_mass to get the HasSum
  have h_tail_mass := FrogModel.Cert.tail_mass (D.rho : ℝ) hrho_pos' hrho_lt1' n
  -- h_tail_mass : HasSum (fun k => (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ (n + k)) ((D.rho : ℝ) ^ n)
  have h_nonneg_real : ∀ k : ℕ, 0 ≤ (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ (n + k) := by
    intro k
    have h1 : 0 ≤ 1 - (D.rho : ℝ) := by linarith
    have h2 : 0 ≤ (D.rho : ℝ) ^ (n + k) := pow_nonneg hrho_pos' _
    nlinarith
  have h_summable : Summable fun k : ℕ => (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ (n + k) :=
    h_tail_mass.summable
  have h_ofReal_tsum := ENNReal.ofReal_tsum_of_nonneg h_nonneg_real h_summable
  -- h_ofReal_tsum : ENNReal.ofReal (∑' k, ...) = ∑' k, ENNReal.ofReal (...)
  have h_tsum_eq := h_tail_mass.tsum_eq
  -- h_tsum_eq : ∑' k, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ (n + k) = (D.rho : ℝ) ^ n
  calc
    ∑' k : ℕ, ENNReal.ofReal ((1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ (n + k))
        = ENNReal.ofReal (∑' k : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ (n + k)) := by rw [h_ofReal_tsum]
    _ = ENNReal.ofReal ((D.rho : ℝ) ^ n) := by rw [h_tsum_eq]

/-- The tail law is a probability law. -/
theorem FrogModel.Cert.Data.tailLaw_univ (D : Data) (h0 : D.I0) : D.tailLaw Set.univ = 1 := by
  unfold tailLaw
  rw [Measure.sum_apply]
  · simp
    have hr_pos : 0 ≤ (D.rho : ℝ) := by exact mod_cast h0.2.2.2.2.1.le
    have hr_lt_one : (D.rho : ℝ) < 1 := by exact mod_cast h0.2.2.2.2.2.1
    have hr_abs_lt_one : |(D.rho : ℝ)| < 1 := by
      rw [abs_of_nonneg hr_pos]
      exact hr_lt_one
    have h_nonneg : ∀ i : ℕ, 0 ≤ (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ i := by
      intro i
      have h1 : 0 ≤ 1 - (D.rho : ℝ) := by linarith
      have h2 : 0 ≤ (D.rho : ℝ) ^ i := pow_nonneg hr_pos i
      nlinarith
    have h_summable : Summable fun i : ℕ => (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ i := by
      have h_geom_summable : Summable fun i : ℕ => (D.rho : ℝ) ^ i := by
        exact summable_geometric_of_abs_lt_one hr_abs_lt_one
      exact Summable.mul_left _ h_geom_summable
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg h_summable]
    have h_tsum : ∑' (i : ℕ), (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ i = 1 := by
      have h_geom : ∑' (i : ℕ), (D.rho : ℝ) ^ i = (1 - (D.rho : ℝ))⁻¹ := by
        exact tsum_geometric_of_lt_one hr_pos hr_lt_one
      calc
        ∑' (i : ℕ), (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ i = (1 - (D.rho : ℝ)) * ∑' (i : ℕ), (D.rho : ℝ) ^ i := by
          rw [tsum_mul_left]
        _ = (1 - (D.rho : ℝ)) * (1 - (D.rho : ℝ))⁻¹ := by rw [h_geom]
        _ = 1 := by
          have h_ne_zero : 1 - (D.rho : ℝ) ≠ 0 := by linarith
          field_simp [h_ne_zero]
    rw [h_tsum]
    simp
  · exact MeasurableSet.univ

/-- The tail law has no mass at `⊤`. -/
theorem FrogModel.Cert.Data.tailLaw_top (D : Data) (i : Fin D.J) :
    D.tailLaw {B | B i = ⊤} = 0 := by
  dsimp [Data.tailLaw]
  have hmeas : MeasurableSet {B : Fin D.J → ℕ∞ | B i = ⊤} := by
    have h_singleton : MeasurableSet ({⊤} : Set ℕ∞) := measurableSet_singleton ⊤
    have h_eval_meas : Measurable fun (B : Fin D.J → ℕ∞) => B i := measurable_pi_apply i
    exact h_eval_meas h_singleton
  rw [MeasureTheory.Measure.sum_apply _ hmeas]
  rw [ENNReal.tsum_eq_zero]
  intro n
  rw [MeasureTheory.Measure.smul_apply]
  rw [MeasureTheory.Measure.dirac_apply]
  simp

/-- `P_tab` is a probability law. -/
theorem FrogModel.Cert.Data.tabLaw_univ (D : Data) (h1 : D.I1) : D.tabLaw Set.univ = 1 := by
  dsimp [tabLaw]
  -- ((D.paths D.J 0 0).map fun π => ENNReal.ofReal (pathProb π : ℝ) • Measure.dirac (pathBlock D.J π)).sum Set.univ = 1
  have h_list_sum_apply : ∀ (L : List (Measure (Fin D.J → ℕ∞))) (s : Set (Fin D.J → ℕ∞)),
    (L.sum) s = (L.map (· s)).sum := by
    intro L s
    induction' L with μ L ih
    · simp
    · simp [Measure.add_apply, ih]
  rw [h_list_sum_apply]
  have h_smul_dirac : ∀ (c : ℝ≥0∞) (x : Fin D.J → ℕ∞),
    (c • Measure.dirac x) Set.univ = c := by
    intro c x
    calc
      (c • Measure.dirac x) Set.univ = c • (Measure.dirac x Set.univ) := by
        rw [Measure.smul_apply]
      _ = c • (1 : ℝ≥0∞) := by rw [Measure.dirac_apply_of_mem (Set.mem_univ x)]
      _ = c := by simp
  -- Simplify the mapped expression
  have h_map : (List.map (fun x => x Set.univ)
      (List.map (fun π => ENNReal.ofReal (pathProb π : ℝ) • Measure.dirac (pathBlock D.J π)) (D.paths D.J 0 0))) =
      (List.map fun π => ENNReal.ofReal (pathProb π : ℝ)) (D.paths D.J 0 0) := by
    simp [List.map_map, h_smul_dirac]
  rw [h_map]
  -- ((D.paths D.J 0 0).map fun π => ENNReal.ofReal (pathProb π : ℝ)).sum = 1
  have h_pos : ∀ π ∈ D.paths D.J 0 0, 0 ≤ (pathProb π : ℝ) := by
    intro π hπ
    have h := FrogModel.Cert.Data.paths_prob_pos D h1 D.J 0 0 π hπ
    exact mod_cast h.le
  have h_ofReal_sum : ∀ (L : List (List Tr)), (∀ π ∈ L, 0 ≤ (pathProb π : ℝ)) →
      (L.map fun π => ENNReal.ofReal (pathProb π : ℝ)).sum =
      ENNReal.ofReal ((L.map fun π => (pathProb π : ℝ)).sum) := by
    intro L hpos
    induction' L with π L ih
    · simp
    · have hπ : 0 ≤ (pathProb π : ℝ) := hpos π (by simp)
      have hL : ∀ π' ∈ L, 0 ≤ (pathProb π' : ℝ) := by
        intro π' hπ'
        apply hpos π'
        simp [hπ']
      have h_sum_nonneg : 0 ≤ (L.map fun π => (pathProb π : ℝ)).sum :=
        List.sum_nonneg fun x hx => by
          rcases List.mem_map.mp hx with ⟨π', hπ', rfl⟩
          exact hL π' hπ'
      simp [List.map_cons, List.sum_cons, ih hL, ENNReal.ofReal_add hπ h_sum_nonneg]
  rw [h_ofReal_sum (D.paths D.J 0 0) h_pos]
  -- ENNReal.ofReal (((D.paths D.J 0 0).map fun π => (pathProb π : ℝ)).sum) = 1
  have h_paths_sum : ((D.paths D.J 0 0).map fun π => (pathProb π : ℝ)).sum = (1 : ℝ) := by
    have hsum := FrogModel.Cert.Data.paths_prob_sum D h1 D.J 0 0 (by simp) (by
      have h0 : D.nLabels 0 = 1 := by
        unfold I1 at h1
        exact h1.2.1
      rw [h0]
      exact Nat.one_pos)
    have hsum' := congrArg (fun x : ℚ => (x : ℝ)) hsum
    -- hsum' : ↑(((D.paths D.J 0 0).map pathProb).sum) = (↑1 : ℝ)
    rw [Rat.cast_list_sum] at hsum'
    -- hsum' : (List.map Rat.cast ((D.paths D.J 0 0).map pathProb)).sum = (↑1 : ℝ)
    rw [List.map_map] at hsum'
    -- hsum' : (List.map (Rat.cast ∘ pathProb) (D.paths D.J 0 0)).sum = (↑1 : ℝ)
    -- Goal: (List.map (fun π => ↑(pathProb π)) (D.paths D.J 0 0)).sum = 1
    have h_cast_eq : (Rat.cast : ℚ → ℝ) ∘ pathProb = (fun π => (pathProb π : ℝ)) := by
      ext π; simp
    rw [h_cast_eq] at hsum'
    -- hsum' : (List.map (fun π => (pathProb π : ℝ)) (D.paths D.J 0 0)).sum = (↑1 : ℝ)
    -- Goal: (List.map (fun π => (pathProb π : ℝ)) (D.paths D.J 0 0)).sum = (1 : ℝ)
    rw [hsum']
    simp
  rw [h_paths_sum]
  simp

/-- **(I3b) against the tail law**: `theta^-(T + 1 + n) S ≤ eps rho^n` when
`S ≤ eps theta^(T + 1)` and `theta rho ≥ 1`. -/
theorem FrogModel.Cert.Data.stop_tail_le (D : Data) (h0 : D.I0) (h2 : D.I2) (S : ℝ≥0∞)
    (hS : S ≤ ENNReal.ofReal (D.eps : ℝ) * ENNReal.ofReal (D.theta : ℝ) ^ (D.T + 1)) (n : ℕ) :
    (ENNReal.ofReal (D.theta : ℝ))⁻¹ ^ (D.T + 1 + n) * S ≤
      ENNReal.ofReal (D.eps : ℝ) * ENNReal.ofReal ((D.rho : ℝ) ^ n) := by
  rcases h0 with ⟨_, _, hεpos, _, hρpos, _, _⟩
  rcases h2 with ⟨_, _, _, hθgt1, hθρge1⟩
  have hθpos_real : 0 < (D.theta : ℝ) := by
    have : (0 : ℚ) < D.theta := by linarith
    exact_mod_cast this
  have hθgt1_real : (1 : ℝ) < (D.theta : ℝ) := by exact_mod_cast hθgt1
  have hθρge1_real : (1 : ℝ) ≤ (D.theta : ℝ) * (D.rho : ℝ) := by
    have : (1 : ℚ) ≤ D.theta * D.rho := hθρge1
    exact_mod_cast this
  set θ := ENNReal.ofReal (D.theta : ℝ) with hθdef
  set ε := ENNReal.ofReal (D.eps : ℝ) with hεdef
  set ρ := ENNReal.ofReal (D.rho : ℝ) with hρdef
  have hθpos' : θ ≠ 0 := by
    rw [hθdef]
    exact (ENNReal.ofReal_ne_zero_iff.mpr hθpos_real)
  have hθfin : θ ≠ ⊤ := by
    rw [hθdef]
    exact ENNReal.ofReal_ne_top
  have hθpow_pos : θ ^ (D.T + 1) ≠ 0 := ENNReal.pow_ne_zero hθpos' (D.T + 1)
  have hθpow_fin : θ ^ (D.T + 1) ≠ ⊤ := ENNReal.pow_ne_top (n := D.T + 1) hθfin
  have h_inv_mul : (θ ^ (D.T + 1))⁻¹ * θ ^ (D.T + 1) = 1 :=
    ENNReal.inv_mul_cancel hθpow_pos hθpow_fin
  -- multiply hS by θ⁻¹ ^ (D.T + 1 + n)
  have h1 : θ⁻¹ ^ (D.T + 1 + n) * S ≤ θ⁻¹ ^ (D.T + 1 + n) * (ε * θ ^ (D.T + 1)) :=
    mul_le_mul_right hS _
  -- rearrange RHS
  have h2 : θ⁻¹ ^ (D.T + 1 + n) * (ε * θ ^ (D.T + 1)) = ε * (θ⁻¹ ^ (D.T + 1 + n) * θ ^ (D.T + 1)) := by
    ring
  -- simplify the product
  have h3 : θ⁻¹ ^ (D.T + 1 + n) * θ ^ (D.T + 1) = θ⁻¹ ^ n := by
    calc
      θ⁻¹ ^ (D.T + 1 + n) * θ ^ (D.T + 1)
          = θ⁻¹ ^ ((D.T + 1) + n) * θ ^ (D.T + 1) := by rw [add_comm (D.T + 1) n]
      _ = (θ⁻¹ ^ (D.T + 1) * θ⁻¹ ^ n) * θ ^ (D.T + 1) := by rw [pow_add]
      _ = (θ⁻¹ ^ (D.T + 1) * θ ^ (D.T + 1)) * θ⁻¹ ^ n := by ring
      _ = ((θ ^ (D.T + 1))⁻¹ * θ ^ (D.T + 1)) * θ⁻¹ ^ n := by rw [ENNReal.inv_pow]
      _ = 1 * θ⁻¹ ^ n := by rw [h_inv_mul]
      _ = θ⁻¹ ^ n := by rw [one_mul]
  -- Now we have: θ⁻¹ ^ (D.T + 1 + n) * S ≤ ε * (θ⁻¹ ^ n)
  have h4 : θ⁻¹ ^ (D.T + 1 + n) * S ≤ ε * (θ⁻¹ ^ n) := by
    calc
      θ⁻¹ ^ (D.T + 1 + n) * S ≤ θ⁻¹ ^ (D.T + 1 + n) * (ε * θ ^ (D.T + 1)) := h1
      _ = ε * (θ⁻¹ ^ (D.T + 1 + n) * θ ^ (D.T + 1)) := by rw [h2]
      _ = ε * (θ⁻¹ ^ n) := by rw [h3]
  -- Now we need to relate θ⁻¹ ^ n to ENNReal.ofReal ((D.rho : ℝ) ^ n)
  have h5 : θ⁻¹ ^ n ≤ ENNReal.ofReal ((D.rho : ℝ) ^ n) := by
    calc
      θ⁻¹ ^ n = (ENNReal.ofReal (D.theta : ℝ))⁻¹ ^ n := rfl
      _ = (ENNReal.ofReal ((D.theta : ℝ)⁻¹)) ^ n := by rw [ENNReal.ofReal_inv_of_pos hθpos_real]
      _ = ENNReal.ofReal (((D.theta : ℝ)⁻¹) ^ n) := by
        rw [ENNReal.ofReal_pow (show 0 ≤ (D.theta : ℝ)⁻¹ from by positivity)]
      _ ≤ ENNReal.ofReal ((D.rho : ℝ) ^ n) :=
        ENNReal.ofReal_le_ofReal (FrogModel.Cert.inv_theta_pow_le (D.theta : ℝ) (D.rho : ℝ) hθgt1_real hθρge1_real n)
  -- Final step: multiply both sides by ε
  have h6 : ε * (θ⁻¹ ^ n) ≤ ε * ENNReal.ofReal ((D.rho : ℝ) ^ n) :=
    mul_le_mul_right h5 ε
  -- Combine
  calc
    θ⁻¹ ^ (D.T + 1 + n) * S ≤ ε * (θ⁻¹ ^ n) := h4
    _ ≤ ε * ENNReal.ofReal ((D.rho : ℝ) ^ n) := h6
    _ = ENNReal.ofReal (D.eps : ℝ) * ENNReal.ofReal ((D.rho : ℝ) ^ n) := rfl

namespace FrogModel.LemmaX

open FrogModel.Cert

/-- The tail part `eps Q` of `H*`. -/
noncomputable def hstarTail : Measure (Fin 4 → ℕ∞) := epsC • cand.tailLaw

theorem hstar_eq_add : Hstar = hstarFin + hstarTail := rfl

theorem measurable_last4 : Measurable fun B : Fin 4 → ℕ∞ => B 3 := measurable_pi_apply 3

theorem measurableSet_enat (S : Set ℕ∞) : MeasurableSet S := (Set.to_countable S).measurableSet

/-- The mass of the finite part of a certificate law. -/
theorem _root_.FrogModel.Cert.Data.finPart_univ (D : Data) (h1 : D.I1) :
    (ENNReal.ofReal ((1 - D.eps : ℚ) : ℝ) • D.tabLaw) Set.univ =
      ENNReal.ofReal ((1 - D.eps : ℚ) : ℝ) := by
  rw [Measure.smul_apply, smul_eq_mul, D.tabLaw_univ h1, mul_one]

/-- The upper tails of the tail part of a certificate law. -/
theorem _root_.FrogModel.Cert.Data.tailPart_tail (D : Data) (h0 : D.I0) (i : Fin D.J) (n : ℕ) :
    (ENNReal.ofReal ((D.eps : ℚ) : ℝ) • D.tailLaw) {B | ((D.T + 1 + n : ℕ) : ℕ∞) ≤ B i} =
      ENNReal.ofReal ((D.eps : ℚ) : ℝ) * ENNReal.ofReal ((D.rho : ℝ) ^ n) := by
  rw [Measure.smul_apply, smul_eq_mul, D.tailLaw_tail h0 i n]

/-- The mass of the tail part of a certificate law. -/
theorem _root_.FrogModel.Cert.Data.tailPart_univ (D : Data) (h0 : D.I0) :
    (ENNReal.ofReal ((D.eps : ℚ) : ℝ) • D.tailLaw) Set.univ = ENNReal.ofReal ((D.eps : ℚ) : ℝ) := by
  rw [Measure.smul_apply, smul_eq_mul, D.tailLaw_univ h0, mul_one]

/-- The tail part of a certificate law is the law of the constant block of any coordinate. -/
theorem _root_.FrogModel.Cert.Data.tailPart_eq_map_const (D : Data) (c : ℝ≥0∞) (i : Fin D.J) :
    ((c • D.tailLaw).map fun B => B i).map (constBlock D.J) = c • D.tailLaw := by
  conv_rhs => rw [D.tailLaw_eq_map_const i]
  rw [Measure.map_smul, Measure.map_smul]
  · exact (measurable_of_countable _).aemeasurable
  · exact (measurable_pi_apply i).aemeasurable

-- `Fin cand.J` against `Fin 4`: the unifier unfolds `cand`.
set_option maxRecDepth 20000 in
/-- The mass of the finite part of `H*`. -/
theorem hstarFin_univ : hstarFin Set.univ = ENNReal.ofReal ((1 - cand.eps : ℚ) : ℝ) :=
  cand.finPart_univ cand_I1

set_option maxRecDepth 20000 in
/-- The upper tails of the tail part of `H*`. -/
theorem hstarTail_tail (n : ℕ) :
    hstarTail {B | ((cand.T + 1 + n : ℕ) : ℕ∞) ≤ B 3} =
      epsC * ENNReal.ofReal ((cand.rho : ℝ) ^ n) :=
  cand.tailPart_tail cand_I0 ⟨3, by decide⟩ n

set_option maxRecDepth 20000 in
/-- The mass of the tail part of `H*`. -/
theorem hstarTail_univ : hstarTail Set.univ = epsC :=
  cand.tailPart_univ cand_I0


instance : IsFiniteMeasure hstarTail := ⟨by rw [hstarTail_univ]; exact ENNReal.ofReal_lt_top⟩

set_option maxRecDepth 20000 in
/-- The tail part of `H*` is the law of the constant block of its last coordinate. -/
theorem hstarTail_eq_map_const :
    (hstarTail.map fun B => B 3).map (constBlock 4) = hstarTail :=
  cand.tailPart_eq_map_const epsC ⟨3, by decide⟩


/-- **The last step of Theorem 6.5 of the paper**: a dominating output split as in `DomSplit`,
with (I3b) and (I4), gives `Phi_4(H*) ≤ H*`. -/
theorem lemma62_holds : Lemma62 := by
  intro Odom L Dres Sov hD hS hP
  obtain ⟨_, _, heps0, heps1, hrho0, hrho1, _⟩ := cand_I0
  have hrho0' : (0 : ℝ) ≤ cand.rho := by exact_mod_cast hrho0.le
  have hrho1' : (cand.rho : ℝ) < 1 := by exact_mod_cast hrho1
  have := hD.prob
  obtain ⟨π, hπ1, hπ2, hπle⟩ := hP
  set s := π.map Prod.fst with hs_def
  set ν := (L - s) + Dres with hν_def
  have h1 : SubCoupling s hstarFin := ⟨π, rfl, hπ2, hπle⟩
  have hs_univ : s Set.univ = ENNReal.ofReal ((1 - cand.eps : ℚ) : ℝ) := by
    rw [subCoupling_univ h1, hstarFin_univ]
  have : IsFiniteMeasure s := ⟨by rw [hs_univ]; exact ENNReal.ofReal_lt_top⟩
  have hOdom : Odom = s + ν := by
    rw [hD.split, hν_def, ← add_assoc, add_comm s, Measure.sub_add_cancel_of_le hπ1]
  -- the mass of `nu`
  have hsplit1 : ENNReal.ofReal ((1 - cand.eps : ℚ) : ℝ) + epsC = 1 := by
    unfold epsC
    have a : (0 : ℝ) ≤ ((1 - cand.eps : ℚ) : ℝ) := by
      have : cand.eps < 1 := heps1
      exact_mod_cast (sub_nonneg.2 this.le)
    have b : (0 : ℝ) ≤ ((cand.eps : ℚ) : ℝ) := by exact_mod_cast heps0.le
    rw [← ENNReal.ofReal_add a b]
    push_cast
    simp
  have hν_univ : ν Set.univ = epsC := by
    have h := hD.prob.measure_univ
    rw [hOdom, Measure.add_apply, hs_univ, ← hsplit1] at h
    exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 h
  have : IsFiniteMeasure ν := ⟨by rw [hν_univ]; exact ENNReal.ofReal_lt_top⟩
  have hνmono : ∀ᵐ B ∂ν, Monotone B := by
    have hle : ν ≤ Odom := hOdom ▸ Measure.le_add_left le_rfl
    exact ae_mono hle hD.mono
  -- the tails of the last coordinate of `nu` beyond `T`
  have hνk : ∀ n : ℕ, ν {B | ((cand.T + 1 + n : ℕ) : ℕ∞) ≤ B 3} ≤
      epsC * ENNReal.ofReal ((cand.rho : ℝ) ^ n) := by
    intro n
    rw [hν_def, Measure.add_apply]
    have hL : (L - s) {B | ((cand.T + 1 + n : ℕ) : ℕ∞) ≤ B 3} = 0 := by
      refine le_antisymm (le_trans (Measure.sub_le _) ?_) zero_le
      refine le_trans (measure_mono fun B hB => ?_) hD.supp.le
      simp only [Set.mem_ofPred_eq] at hB ⊢
      exact lt_of_lt_of_le (by exact_mod_cast (by omega : cand.T < cand.T + 1 + n)) hB
    rw [hL, zero_add]
    exact (hD.tail (cand.T + 1 + n) (by omega)).trans
      (cand.stop_tail_le cand_I0 cand_I2 Sov hS n)
  have hlim : Tendsto (fun n : ℕ => epsC * ENNReal.ofReal ((cand.rho : ℝ) ^ n)) atTop
      (nhds 0) := by
    have : Tendsto (fun n : ℕ => ENNReal.ofReal ((cand.rho : ℝ) ^ n)) atTop (nhds 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one hrho0' hrho1')
    have h := ENNReal.Tendsto.const_mul this (Or.inr (ENNReal.ofReal_ne_top : epsC ≠ ⊤))
    rwa [mul_zero] at h
  have htail : ∀ t : ℕ∞, (ν.map fun B => B 3) {x | t ≤ x} ≤
      (hstarTail.map fun B => B 3) {x | t ≤ x} := by
    intro t
    rw [Measure.map_apply measurable_last4 (measurableSet_enat _),
      Measure.map_apply measurable_last4 (measurableSet_enat _)]
    induction t using ENat.recTopCoe with
    | top =>
      have h0 : ν ((fun B : Fin 4 → ℕ∞ => B 3) ⁻¹' {x | ⊤ ≤ x}) ≤ 0 := by
        refine ge_of_tendsto' hlim fun n => le_trans (measure_mono fun B hB => ?_) (hνk n)
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, top_le_iff] at hB ⊢
        rw [hB]
        exact le_top
      exact le_trans h0 zero_le
    | coe k =>
      by_cases hk : k ≤ cand.T + 1
      · have e1 : ν ((fun B : Fin 4 → ℕ∞ => B 3) ⁻¹' {x | (k : ℕ∞) ≤ x}) ≤ epsC :=
          le_trans (measure_mono (Set.subset_univ _)) hν_univ.le
        have e2 : epsC ≤ hstarTail ((fun B : Fin 4 → ℕ∞ => B 3) ⁻¹' {x | (k : ℕ∞) ≤ x}) := by
          have := hstarTail_tail 0
          rw [pow_zero, ENNReal.ofReal_one, mul_one] at this
          rw [← this]
          refine measure_mono fun B hB => ?_
          simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hB ⊢
          exact le_trans (by exact_mod_cast (by omega : k ≤ cand.T + 1 + 0)) hB
        exact e1.trans e2
      · obtain ⟨n, rfl⟩ : ∃ n, k = cand.T + 1 + n := ⟨k - (cand.T + 1), by omega⟩
        have := hνk n
        rw [← hstarTail_tail n] at this
        exact this
  have hmass : (ν.map fun B => B 3) Set.univ = (hstarTail.map fun B => B 3) Set.univ := by
    rw [Measure.map_apply measurable_last4 MeasurableSet.univ,
      Measure.map_apply measurable_last4 MeasurableSet.univ, Set.preimage_univ, hν_univ,
      hstarTail_univ]
  have hA := subCoupling_constLast ν hνmono
  have hB := subCoupling_map_constBlock 4 (subCoupling_enat hmass htail)
  rw [hstarTail_eq_map_const] at hB
  have h2 : SubCoupling ν hstarTail := subCoupling_trans hA hB
  have h := subCoupling_add h1 h2
  rw [← hOdom, ← hstar_eq_add] at h
  exact couplingLE_trans _ _ _ hD.le_dom (couplingLE_of_subCoupling h)

end FrogModel.LemmaX
