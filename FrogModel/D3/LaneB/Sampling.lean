module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# Tools for optional sampling

Telescoping between two stopping indices, the independence of a coin from a prefix next to an
independent factor, and the resampling of one coordinate of an i.i.d. family.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- Telescoping between two stopping indices `σ ≤ τ`, truncated at `n`. -/
theorem telescope_stop (M : ℕ → ℝ) (σ τ n : ℕ) (h : σ ≤ τ) :
    M (min τ n) - M (min σ n) =
      ∑ i ∈ Finset.range n, if σ ≤ i ∧ i < τ then M (i + 1) - M i else 0 := by
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ, ← ih]
    by_cases hσn : σ ≤ n
    · by_cases hnτ : n < τ
      · -- Case σ ≤ n < τ
        have hτ : n + 1 ≤ τ := by omega
        have hσ : σ ≤ n + 1 := by omega
        have hminτn : min τ n = n := Nat.min_eq_right (by omega)
        have hminσn : min σ n = σ := Nat.min_eq_left hσn
        have hminτsn : min τ (n + 1) = n + 1 := Nat.min_eq_right hτ
        have hminσsn : min σ (n + 1) = σ := Nat.min_eq_left hσ
        rw [hminτsn, hminσsn, hminτn, hminσn]
        simp [hσn, hnτ]
      · -- Case τ ≤ n (since ¬ n < τ)
        have hτn : τ ≤ n := by omega
        have hminτn : min τ n = τ := Nat.min_eq_left hτn
        have hminσn : min σ n = σ := Nat.min_eq_left (Nat.le_trans h hτn)
        have hminτsn : min τ (n + 1) = τ := Nat.min_eq_left (by omega)
        have hminσsn : min σ (n + 1) = σ := Nat.min_eq_left (by omega)
        rw [hminτsn, hminσsn, hminτn, hminσn]
        simp [hnτ]
    · -- Case n < σ
      have hnσ : n < σ := by omega
      have hnτ : n < τ := Nat.lt_of_lt_of_le hnσ h
      have hminτn : min τ n = n := Nat.min_eq_right (by omega)
      have hminσn : min σ n = n := Nat.min_eq_right (by omega)
      have hminτsn : min τ (n + 1) = n + 1 := Nat.min_eq_right (by omega)
      have hminσsn : min σ (n + 1) = n + 1 := Nat.min_eq_right (by omega)
      rw [hminτsn, hminσsn, hminτn, hminσn]
      simp [hσn]

/-- A coin `g` independent of `f` under `μ` stays independent of every event read from `f` and from an
independent factor `r`. -/
theorem indep_section {α β R : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace R] (μ : Measure α) [IsProbabilityMeasure μ] (ρ : Measure R)
    [IsProbabilityMeasure ρ] (f : α → β) (g : α → Bool) (hf : Measurable f) (hg : Measurable g)
    (hind : IndepFun g f μ) (B : Set (β × R)) (hB : MeasurableSet B) :
    (μ.prod ρ) ({x | (f x.1, x.2) ∈ B} ∩ {x | g x.1 = true}) =
      μ {a | g a = true} * (μ.prod ρ) {x | (f x.1, x.2) ∈ B} := by
  set p := μ {a | g a = true} with hp
  let S : Set (α × R) := {x | (f x.1, x.2) ∈ B}
  have hS_meas : MeasurableSet S := by
    have h_meas : Measurable (fun (x : α × R) => (f x.1, x.2)) :=
      (hf.comp measurable_fst).prodMk measurable_snd
    exact h_meas hB
  have h_singleton : MeasurableSet ({true} : Set Bool) := MeasurableSet.singleton _
  have h_gx1_meas : MeasurableSet {x : α × R | g x.1 = true} :=
    (hg.comp measurable_fst) (MeasurableSet.singleton true)
  have h_inter_meas : MeasurableSet (S ∩ {x | g x.1 = true}) :=
    MeasurableSet.inter hS_meas h_gx1_meas
  rw [Measure.prod_apply_symm h_inter_meas, Measure.prod_apply_symm hS_meas]
  have h_section (r : R) : μ ((fun (a : α) => (a, r)) ⁻¹' (S ∩ {x | g x.1 = true})) =
      p * μ ((fun (a : α) => (a, r)) ⁻¹' S) := by
    have hBr : MeasurableSet {b : β | (b, r) ∈ B} :=
      (measurable_prodMk_right (y := r)) hB
    have h_preimage_eq : (fun (a : α) => (a, r)) ⁻¹' S = f ⁻¹' {b | (b, r) ∈ B} := by
      ext a; simp [S]
    have h_gpreimage_eq : (fun (a : α) => (a, r)) ⁻¹' {x : α × R | g x.1 = true} = {a | g a = true} := by
      ext a; simp
    calc
      μ ((fun (a : α) => (a, r)) ⁻¹' (S ∩ {x | g x.1 = true}))
          = μ (((fun (a : α) => (a, r)) ⁻¹' S) ∩ ((fun (a : α) => (a, r)) ⁻¹' {x | g x.1 = true})) := by
            rw [Set.preimage_inter]
      _ = μ (((fun (a : α) => (a, r)) ⁻¹' S) ∩ {a | g a = true}) := by rw [h_gpreimage_eq]
      _ = μ ((f ⁻¹' {b | (b, r) ∈ B}) ∩ {a | g a = true}) := by rw [h_preimage_eq]
      _ = μ ((f ⁻¹' {b | (b, r) ∈ B}) ∩ (g ⁻¹' {true})) := rfl
      _ = μ (g ⁻¹' {true}) * μ (f ⁻¹' {b | (b, r) ∈ B}) := by
            rw [Set.inter_comm, hind.measure_inter_preimage_eq_mul {true} {b | (b, r) ∈ B} h_singleton hBr]
      _ = μ {a | g a = true} * μ (f ⁻¹' {b | (b, r) ∈ B}) := by
        simp [Set.preimage]
      _ = μ {a | g a = true} * μ ((fun (a : α) => (a, r)) ⁻¹' S) := by rw [← h_preimage_eq]
      _ = p * μ ((fun (a : α) => (a, r)) ⁻¹' S) := by rw [hp]
  have h_eq : (fun (r : R) => μ ((fun (a : α) => (a, r)) ⁻¹' (S ∩ {x | g x.1 = true}))) =
      (fun (r : R) => p * μ ((fun (a : α) => (a, r)) ⁻¹' S)) := by
    ext r; exact h_section r
  rw [h_eq]
  rw [lintegral_const_mul p (measurable_measure_prodMk_right hS_meas)]

/-- Resampling one coordinate of a product of probability measures keeps the product. -/
theorem pi_update_map {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (c : ι) :
    (μ.prod (Measure.pi fun _ : ι => μ)).map (fun p => Function.update p.2 c p.1) =
      Measure.pi fun _ : ι => μ := by
  have h_meas : Measurable (fun (p : α × (ι → α)) => Function.update p.2 c p.1) := by
    have h_swap : Measurable (fun (p : α × (ι → α)) => (p.2, p.1)) :=
      Measurable.prodMk measurable_snd measurable_fst
    have h_upd : Measurable (fun (q : (ι → α) × α) => Function.update q.1 c q.2) :=
      measurable_update'
    exact h_upd.comp h_swap
  have h_pi_univ : μ Set.univ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
  refine (MeasureTheory.Measure.pi_eq fun s hs => ?_).symm
  have h_meas_s : ∀ i, MeasurableSet (s i) := hs
  rw [MeasureTheory.Measure.map_apply h_meas (MeasurableSet.univ_pi h_meas_s)]
  -- preimage of Set.univ.pi s under (x, g) ↦ update g c x is (s c) ×ˢ Set.univ.pi (update s c Set.univ)
  have h_preimage : (fun (p : α × (ι → α)) => Function.update p.2 c p.1) ⁻¹' (Set.univ.pi s) =
      (s c) ×ˢ (Set.univ.pi (Function.update s c Set.univ)) := by
    ext ⟨x, g⟩
    constructor
    · intro h
      have hx : x ∈ s c := by simpa using h c
      have hg : g ∈ Set.univ.pi (Function.update s c Set.univ) := by
        intro i
        by_cases hi : i = c
        · subst hi; simp
        · simpa [hi] using h i
      exact Set.mem_prod.mpr ⟨hx, hg⟩
    · intro h
      rcases Set.mem_prod.mp h with ⟨hx, hg⟩
      intro i
      by_cases hi : i = c
      · subst hi; simpa
      · have := Set.mem_pi.mp hg i
        simpa [hi] using this
  rw [h_preimage, MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.pi_pi]
  -- goal: μ (s c) * (∏ i, μ ((Function.update s c Set.univ) i)) = ∏ i, μ (s i)
  have h_prod_update : (∏ i : ι, μ ((Function.update s c Set.univ) i)) =
      (∏ i ∈ (Finset.univ : Finset ι).erase c, μ (s i)) := by
    calc
      (∏ i : ι, μ ((Function.update s c Set.univ) i))
          = (∏ i ∈ (Finset.univ : Finset ι).erase c, μ ((Function.update s c Set.univ) i)) *
            μ ((Function.update s c Set.univ) c) := by
        rw [← Finset.prod_erase_mul (Finset.univ : Finset ι)
          (fun i => μ ((Function.update s c Set.univ) i)) (Finset.mem_univ c)]
      _ = (∏ i ∈ (Finset.univ : Finset ι).erase c, μ (s i)) * μ Set.univ := by
        have h_update_c : μ ((Function.update s c Set.univ) c) = μ Set.univ := by simp
        rw [h_update_c]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        have hi_ne : i ≠ c := Finset.ne_of_mem_erase hi
        simp [hi_ne]
      _ = (∏ i ∈ (Finset.univ : Finset ι).erase c, μ (s i)) * 1 := by rw [h_pi_univ]
      _ = (∏ i ∈ (Finset.univ : Finset ι).erase c, μ (s i)) := by simp
  calc
    μ (s c) * (∏ i : ι, μ ((Function.update s c Set.univ) i))
        = μ (s c) * (∏ i ∈ (Finset.univ : Finset ι).erase c, μ (s i)) := by rw [h_prod_update]
    _ = (∏ i ∈ (Finset.univ : Finset ι).erase c, μ (s i)) * μ (s c) := by ring
    _ = ∏ i : ι, μ (s i) := by
      rw [Finset.prod_erase_mul (Finset.univ : Finset ι) (fun i => μ (s i)) (Finset.mem_univ c)]

/-- Resampling one coordinate of an i.i.d. family, next to an independent factor. -/
theorem prod_update_map {ι α R : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    [MeasurableSpace R] (μ : Measure α) [IsProbabilityMeasure μ] (ρ : Measure R)
    [IsProbabilityMeasure ρ] (c : ι) :
    (μ.prod ((Measure.pi fun _ : ι => μ).prod ρ)).map
        (fun p => (Function.update p.2.1 c p.1, p.2.2)) =
      (Measure.pi fun _ : ι => μ).prod ρ := by
  have hm : Measurable fun p : α × ((ι → α) × R) => (Function.update p.2.1 c p.1, p.2.2) :=
    ((measurable_update' (a := c)).comp ((measurable_fst.comp measurable_snd).prodMk
      measurable_fst)).prodMk (measurable_snd.comp measurable_snd)
  rw [← (measurePreserving_prodAssoc μ (Measure.pi fun _ : ι => μ) ρ).map_eq,
    Measure.map_map hm (MeasurableEquiv.measurable _)]
  have h2 : (fun p : α × ((ι → α) × R) => (Function.update p.2.1 c p.1, p.2.2)) ∘
      MeasurableEquiv.prodAssoc =
        Prod.map (fun p : α × (ι → α) => Function.update p.2 c p.1) id := by
    funext p; rfl
  have hu : Measurable fun p : α × (ι → α) => Function.update p.2 c p.1 :=
    (measurable_update' (a := c)).comp (measurable_snd.prodMk measurable_fst)
  rw [h2, ← Measure.map_prod_map _ _ hu measurable_id, pi_update_map, Measure.map_id]

/-- Integrating a function of the first coordinate of `μ` only. -/
theorem integral_fst_prod {X R : Type*} [MeasurableSpace X] [MeasurableSpace R]
    (μ : Measure ((ℕ → ℕ∞) × X)) [SFinite μ] (ρ : Measure R) [SFinite ρ]
    (h : (ℕ → ℕ∞) × R → ℝ) (hh : Measurable h) :
    ∫ p, h (p.1.1, p.2) ∂(μ.prod ρ) = ∫ p, h p ∂((μ.map Prod.fst).prod ρ) := by
  have : (μ.map Prod.fst).prod ρ = (μ.prod ρ).map (Prod.map Prod.fst id) := by
    rw [← Measure.map_prod_map _ _ measurable_fst measurable_id, Measure.map_id]
  rw [this, integral_map (measurable_fst.prodMap measurable_id).aemeasurable
    hh.aestronglyMeasurable]
  rfl

/-- Resampling the child `c` of the closure from `μc` (whose first marginal is `Q`) keeps the
closure law. -/
theorem closMeasure_update {Ωc : Type*} [MeasurableSpace Ωc]
    (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (μc : Measure ((ℕ → ℕ∞) × Ωc))
    [IsProbabilityMeasure μc] (hμc : μc.map Prod.fst = Q) (c : Fin 3) :
    (μc.prod (closMeasure Q)).map (fun p => (Function.update p.2.1 c p.1.1, p.2.2)) =
      closMeasure Q := by
  have hU : Measurable fun p : (ℕ → ℕ∞) × ClosSample => (Function.update p.2.1 c p.1, p.2.2) :=
    ((measurable_update' (a := c)).comp ((measurable_fst.comp measurable_snd).prodMk
      measurable_fst)).prodMk (measurable_snd.comp measurable_snd)
  have hcomp : (fun p : ((ℕ → ℕ∞) × Ωc) × ClosSample => (Function.update p.2.1 c p.1.1, p.2.2)) =
      (fun p : (ℕ → ℕ∞) × ClosSample => (Function.update p.2.1 c p.1, p.2.2)) ∘
        Prod.map Prod.fst id := rfl
  rw [hcomp, ← Measure.map_map hU (measurable_fst.prodMap measurable_id),
    ← Measure.map_prod_map _ _ measurable_fst measurable_id, Measure.map_id, hμc]
  exact prod_update_map Q dirMeasure c


/-- One step of optional sampling: an increment `Y1 - Y0 ≥ ξ` with a coin `ξ` of probability `1/3`
on an event `A` independent of the coin has nonnegative drift `Y1 - Y0 - 1/3` on `A`. -/
theorem os_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y0 Y1 : Ω → ℕ∞) (ξ : Ω → Bool) (hY0 : Measurable Y0)
    (hY1 : Measurable Y1) (hξ : Measurable ξ) (A : Set Ω) (hA : MeasurableSet A)
    (hAξ : P (A ∩ {ω | ξ ω = true}) = 3⁻¹ * P A)
    (hinc : ∀ᵐ ω ∂P, Y0 ω + (if ξ ω then 1 else 0) ≤ Y1 ω) (C : ℕ)
    (hbd : ∀ᵐ ω ∂P, Y1 ω ≤ (C : ℕ∞)) :
    0 ≤ ∫ ω, A.indicator (fun ω => ((Y1 ω).toNat : ℝ) - (Y0 ω).toNat - 1 / 3) ω ∂P := by
  -- Y1 is finite a.e. (bounded by C)
  have hY1_fin : ∀ᵐ ω ∂P, Y1 ω ≠ ⊤ := by
    filter_upwards [hbd] with ω h
    have hC : (C : ℕ∞) ≠ ⊤ := by simp
    exact ne_top_of_le_ne_top hC h
  -- The sum Y0 + indicator is also finite a.e.
  have hsum_fin : ∀ᵐ ω ∂P, Y0 ω + (if ξ ω then 1 else 0) ≠ ⊤ := by
    filter_upwards [hinc, hbd] with ω hinc' hbd'
    have hC : (C : ℕ∞) ≠ ⊤ := by simp
    have hle : Y0 ω + (if ξ ω then 1 else 0) ≤ (C : ℕ∞) := le_trans hinc' hbd'
    exact ne_top_of_le_ne_top hC hle
  -- Hence Y0 is finite a.e.
  have hY0_fin : ∀ᵐ ω ∂P, Y0 ω ≠ ⊤ := by
    filter_upwards [hsum_fin] with ω h
    intro hY0top
    apply h
    simp [hY0top]
  -- The indicator of ξ is always finite
  have hind_fin : ∀ᵐ ω ∂P, (if ξ ω then (1 : ℕ∞) else 0) ≠ ⊤ := by
    filter_upwards [] with ω
    by_cases h : ξ ω
    · simp [h]
    · simp [h]
  -- Pointwise inequality: (Y0).toNat + (if ξ then 1 else 0) ≤ (Y1).toNat a.e.
  have hineq_nat : ∀ᵐ ω ∂P, (Y0 ω).toNat + (if ξ ω then 1 else 0) ≤ (Y1 ω).toNat := by
    filter_upwards [hinc, hY1_fin, hY0_fin, hind_fin] with ω hinc' hY1fin hY0fin hindfin
    have hsum_le : (Y0 ω + (if ξ ω then 1 else 0)).toNat ≤ (Y1 ω).toNat :=
      ENat.toNat_le_toNat hinc' hY1fin
    have hsum_add : (Y0 ω + (if ξ ω then 1 else 0)).toNat = (Y0 ω).toNat + (if ξ ω then 1 else 0) := by
      rw [ENat.toNat_add hY0fin hindfin]
      cases ξ ω <;> simp
    rw [hsum_add] at hsum_le
    exact hsum_le
  -- Lift to ℝ inequality: ((Y0).toNat : ℝ) + (if ξ then 1 else 0 : ℝ) ≤ ((Y1).toNat : ℝ) a.e.
  have hineq_real : ∀ᵐ ω ∂P, ((Y0 ω).toNat : ℝ) + ((if ξ ω then 1 else 0 : ℕ) : ℝ) ≤ ((Y1 ω).toNat : ℝ) := by
    filter_upwards [hineq_nat] with ω h
    exact_mod_cast h
  -- Measurability helper: any function from ℕ∞ is measurable (discrete sigma-algebra)
  have h_meas_toNat : Measurable (λ (x : ℕ∞) => (x.toNat : ℝ)) := Measurable.of_discrete
  -- Measurability of the ξ indicator
  have h_meas_xi : Measurable (λ ω => ((if ξ ω then (1 : ℕ∞) else 0).toNat : ℝ)) := by
    have h_bool_to_ennat : Measurable (λ (b : Bool) => (if b then (1 : ℕ∞) else 0)) :=
      Measurable.of_discrete
    exact (h_meas_toNat.comp h_bool_to_ennat).comp hξ
  -- Define the two integrands
  set f := A.indicator (λ ω => ((Y1 ω).toNat : ℝ) - (Y0 ω).toNat - 1 / 3) with hf
  set g := A.indicator (λ ω => ((if ξ ω then 1 else 0 : ℕ) : ℝ) - 1 / 3) with hg
  -- g ≤ f a.e. (from hineq_real)
  have hfg : g ≤ᵐ[P] f := by
    filter_upwards [hineq_real] with ω hineq
    dsimp [f, g]
    by_cases hAω : ω ∈ A
    · -- Need to show g ω ≤ f ω when ω ∈ A
      -- g ω = ((if ξ ω then 1 else 0 : ℕ) : ℝ) - 1/3
      -- f ω = ((Y1 ω).toNat : ℝ) - (Y0 ω).toNat - 1/3
      -- So we need: ((if ξ ω then 1 else 0 : ℕ) : ℝ) - 1/3 ≤ ((Y1 ω).toNat : ℝ) - (Y0 ω).toNat - 1/3
      -- Cancel -1/3: ((if ξ ω then 1 else 0 : ℕ) : ℝ) ≤ ((Y1 ω).toNat : ℝ) - (Y0 ω).toNat
      -- From hineq: ((Y0 ω).toNat : ℝ) + ((if ξ ω then 1 else 0 : ℕ) : ℝ) ≤ ((Y1 ω).toNat : ℝ)
      -- Rearranged: ((if ξ ω then 1 else 0 : ℕ) : ℝ) ≤ ((Y1 ω).toNat : ℝ) - ((Y0 ω).toNat : ℝ)
      have hgoal : ((if ξ ω then (1 : ℕ) else 0 : ℕ) : ℝ) - 1/3 ≤ ((Y1 ω).toNat : ℝ) - (Y0 ω).toNat - 1/3 := by
        have hineq' := hineq
        -- hineq: ((Y0 ω).toNat : ℝ) + ((if ξ ω then 1 else 0 : ℕ) : ℝ) ≤ ((Y1 ω).toNat : ℝ)
        linarith
      simpa [hAω] using hgoal
    · simp [hAω]
  -- f is integrable (bounded by C+1 on probability space)
  have h_int_f : Integrable f P := by
    apply Integrable.of_bound (C := (C : ℝ) + 1) ?_ ?_
    · have h_meas_inner : Measurable (λ ω => ((Y1 ω).toNat : ℝ) - (Y0 ω).toNat - 1 / 3) :=
        ((h_meas_toNat.comp hY1).sub (h_meas_toNat.comp hY0)).sub measurable_const
      exact (Measurable.indicator h_meas_inner hA).aestronglyMeasurable
    · filter_upwards [hbd, hinc, hY1_fin, hY0_fin, hsum_fin] with ω hbd' hinc' hY1fin hY0fin hsumfin
      dsimp [f]
      by_cases hAω : ω ∈ A
      · simp [hAω]
        have hY1_le : (Y1 ω).toNat ≤ C := by
          have : (Y1 ω).toNat ≤ (C : ℕ∞).toNat := ENat.toNat_le_toNat hbd' (by simp)
          simpa using this
        have hY0_le : (Y0 ω).toNat ≤ C := by
          have hY0_le_sum : Y0 ω ≤ Y0 ω + (if ξ ω then 1 else 0) :=
            le_add_of_nonneg_right (by cases ξ ω <;> simp)
          have hY0_le_C : Y0 ω ≤ (C : ℕ∞) := le_trans hY0_le_sum (le_trans hinc' hbd')
          have hY0toNat_le : (Y0 ω).toNat ≤ (C : ℕ∞).toNat :=
            ENat.toNat_le_toNat hY0_le_C (by simp)
          simpa using hY0toNat_le
        have h_bound : |((Y1 ω).toNat : ℝ) - (Y0 ω).toNat - 1 / 3| ≤ (C : ℝ) + 1 := by
          have h1 : ((Y1 ω).toNat : ℝ) ≤ (C : ℝ) := by exact_mod_cast hY1_le
          have h2 : ((Y0 ω).toNat : ℝ) ≤ (C : ℝ) := by exact_mod_cast hY0_le
          have hpos1 : 0 ≤ ((Y1 ω).toNat : ℝ) := by exact_mod_cast Nat.zero_le _
          have hpos2 : 0 ≤ ((Y0 ω).toNat : ℝ) := by exact_mod_cast Nat.zero_le _
          have h_upper : ((Y1 ω).toNat : ℝ) - (Y0 ω).toNat - 1 / 3 ≤ (C : ℝ) + 1 := by nlinarith
          have h_lower : -((C : ℝ) + 1) ≤ ((Y1 ω).toNat : ℝ) - (Y0 ω).toNat - 1 / 3 := by nlinarith
          exact abs_le.mpr ⟨h_lower, h_upper⟩
        simpa [Real.norm_eq_abs] using h_bound
      · simp [hAω]
        have h_nonneg : 0 ≤ (C : ℝ) + 1 := by nlinarith [show (0 : ℝ) ≤ C from by exact_mod_cast Nat.zero_le C]
        simp [h_nonneg]
  -- g is integrable (bounded by 1 on probability space)
  have h_int_g : Integrable g P := by
    apply Integrable.of_bound (C := 1) ?_ ?_
    · have h_meas_inner : Measurable (λ ω => ((if ξ ω then 1 else 0 : ℕ) : ℝ) - 1 / 3) := by
        have h_bool_meas : Measurable (λ ω => (if ξ ω then (1 : ℕ) else 0)) := by
          have h_bool_nat : Measurable (λ (b : Bool) => if b then (1 : ℕ) else 0) :=
            Measurable.of_discrete
          exact h_bool_nat.comp hξ
        have h_nat_real : Measurable (Nat.cast : ℕ → ℝ) := measurable_from_nat
        exact h_nat_real.comp h_bool_meas |>.sub measurable_const
      exact (Measurable.indicator h_meas_inner hA).aestronglyMeasurable
    · filter_upwards [] with ω
      dsimp [g]
      by_cases hAω : ω ∈ A
      · simp [hAω]
        cases ξ ω <;> norm_num
      · simp [hAω]
  -- Compute ∫ g = 0 using hAξ
  have h_int_g_eq : ∫ ω, g ω ∂P = 0 := by
    -- Key identity: g = (A ∩ {ξ = true}).indicator 1 - (1/3) * A.indicator 1
    have h_g_eq : g = (A ∩ {ω | ξ ω = true}).indicator (1 : Ω → ℝ) - (1/3 : ℝ) • A.indicator (1 : Ω → ℝ) := by
      ext ω
      dsimp [g]
      by_cases hAω : ω ∈ A
      · by_cases hξω : ξ ω = true
        · have h_inter : ω ∈ A ∩ {ω | ξ ω = true} := Set.mem_inter hAω hξω
          simp [hAω, hξω, h_inter]
        · have h_not_inter : ω ∉ A ∩ {ω | ξ ω = true} := by
            intro h; exact hξω h.2
          simp [hAω, hξω, h_not_inter]
      · have h_not_inter : ω ∉ A ∩ {ω | ξ ω = true} := by intro h; exact hAω h.1
        simp [hAω, h_not_inter]
    rw [h_g_eq]
    -- Rewrite the integral of the difference using integral_sub
    have h_int1 : Integrable ((A ∩ {ω | ξ ω = true}).indicator (1 : Ω → ℝ)) P := by
      have h_meas : MeasurableSet (A ∩ {ω | ξ ω = true}) := by
        have h_set : MeasurableSet {ω | ξ ω = true} := by
          have h_singleton : MeasurableSet ({true} : Set Bool) := MeasurableSet.of_discrete
          exact hξ h_singleton
        exact hA.inter h_set
      rw [integrable_indicator_iff h_meas]
      apply integrableOn_const
      · exact measure_ne_top P (A ∩ {ω | ξ ω = true})
      · simp
    have h_int2 : Integrable ((1/3 : ℝ) • A.indicator (1 : Ω → ℝ)) P := by
      apply Integrable.smul
      rw [integrable_indicator_iff hA]
      apply integrableOn_const
      · exact measure_ne_top P A
      · simp
    -- Rewrite (F - G) ω to F ω - G ω before applying integral_sub
    have h_sub_eq : (((A ∩ {ω | ξ ω = true}).indicator (1 : Ω → ℝ) - (1/3 : ℝ) • A.indicator (1 : Ω → ℝ))) =
        (λ ω => ((A ∩ {ω | ξ ω = true}).indicator (1 : Ω → ℝ)) ω - ((1/3 : ℝ) • A.indicator (1 : Ω → ℝ)) ω) := by
      ext ω; rfl
    rw [h_sub_eq]
    rw [integral_sub h_int1 h_int2]
    -- Now the goal is: (∫ a, (A ∩ {ξ = true}).indicator 1 a ∂P) - (∫ a, ((1/3) • A.indicator 1) a ∂P) = 0
    -- Rewrite the first integral using integral_indicator_one
    have h_first : ∫ a, (A ∩ {ω | ξ ω = true}).indicator (1 : Ω → ℝ) a ∂P = P.real (A ∩ {ω | ξ ω = true}) := by
      rw [integral_indicator_one]
      · have h_set : MeasurableSet {ω | ξ ω = true} := by
          have h_singleton : MeasurableSet ({true} : Set Bool) := MeasurableSet.of_discrete
          exact hξ h_singleton
        exact hA.inter h_set
    -- Rewrite the second integral: ((1/3) • A.indicator 1) a = (1/3) * (A.indicator 1 a)
    have h_second : ∫ a, ((1/3 : ℝ) • A.indicator (1 : Ω → ℝ)) a ∂P = (1/3 : ℝ) * P.real A := by
      calc
        ∫ a, ((1/3 : ℝ) • A.indicator (1 : Ω → ℝ)) a ∂P
            = ∫ a, (1/3 : ℝ) * (A.indicator (1 : Ω → ℝ) a) ∂P := rfl
        _ = (1/3 : ℝ) * ∫ a, A.indicator (1 : Ω → ℝ) a ∂P := integral_const_mul _ _
        _ = (1/3 : ℝ) * P.real A := by rw [integral_indicator_one hA]
    rw [h_first, h_second]
    rw [measureReal_def, measureReal_def]
    rw [hAξ]
    have hPA_ne_top : P A ≠ ⊤ := measure_ne_top P A
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    ring
  -- Conclude: 0 ≤ ∫ f
  have h_nonneg : 0 ≤ ∫ ω, f ω ∂P := by
    have h_le : ∫ ω, g ω ∂P ≤ ∫ ω, f ω ∂P := integral_mono_ae h_int_g h_int_f hfg
    linarith
  exact h_nonneg

/-- Future domination (an inequality for events of the prefix `G(0), ..., G(e)`) extends to events
that also read an independent factor `r`. -/
theorem future_dom_prod {R : Type*} [MeasurableSpace R]
    (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (ρ : Measure R) [IsProbabilityMeasure ρ]
    (e J : ℕ)
    (hfd : ∀ B : Set (Fin (e + 1) → ℕ∞),
      ∫⁻ G in {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ B}, (G J : ℝ≥0∞) ∂Q ≤
        ∫⁻ G in {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ B}, (G e : ℝ≥0∞) ∂Q +
          Q {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ B} * ∫⁻ G, (G (J - e) : ℝ≥0∞) ∂Q)
    (B : Set ((Fin (e + 1) → ℕ∞) × R)) (hB : MeasurableSet B) :
    ∫⁻ p in {p : (ℕ → ℕ∞) × R | ((fun l : Fin (e + 1) => p.1 l), p.2) ∈ B}, (p.1 J : ℝ≥0∞)
        ∂(Q.prod ρ) ≤
      ∫⁻ p in {p : (ℕ → ℕ∞) × R | ((fun l : Fin (e + 1) => p.1 l), p.2) ∈ B}, (p.1 e : ℝ≥0∞)
          ∂(Q.prod ρ) +
        (Q.prod ρ) {p : (ℕ → ℕ∞) × R | ((fun l : Fin (e + 1) => p.1 l), p.2) ∈ B} *
          ∫⁻ G, (G (J - e) : ℝ≥0∞) ∂Q := by
  -- The restriction map
  let restr (G : ℕ → ℕ∞) : Fin (e + 1) → ℕ∞ := fun l => G (l : ℕ)
  have h_meas_restr : Measurable restr := by
    refine Measurable.of_eval fun l => ?_
    exact measurable_pi_apply (a := (l : ℕ))
  -- The map p ↦ (restr p.1, p.2)
  have h_meas_prod_map : Measurable (fun (p : (ℕ → ℕ∞) × R) => (restr p.1, p.2)) := by
    apply Measurable.prod
    · exact h_meas_restr.comp measurable_fst
    · exact measurable_snd
  -- The set S
  let S : Set ((ℕ → ℕ∞) × R) := {p | (restr p.1, p.2) ∈ B}
  have hS_meas : MeasurableSet S :=
    hB.preimage h_meas_prod_map
  -- For each r, the section Sr
  have hSr_meas (r : R) : MeasurableSet {G : ℕ → ℕ∞ | (restr G, r) ∈ B} := by
    have h_map : Measurable (fun (G : ℕ → ℕ∞) => (restr G, r)) :=
      h_meas_prod_map.comp (measurable_prodMk_right (y := r))
    exact hB.preimage h_map
  -- Coercion measurability
  have h_coe_meas : Measurable (fun (x : ℕ∞) => (x : ENNReal)) := Measurable.of_discrete
  -- Measurability of r ↦ Q(Sr)
  have h_meas_QSr : Measurable (fun (r : R) => Q {G : ℕ → ℕ∞ | (restr G, r) ∈ B}) := by
    let f : (ℕ → ℕ∞) × R → ENNReal := fun p =>
      Set.indicator {G : ℕ → ℕ∞ | (restr G, p.2) ∈ B} (fun _ => (1 : ENNReal)) p.1
    have hf_meas : Measurable f := by
      have h_eq : f = (fun (q : (Fin (e + 1) → ℕ∞) × R) =>
        Set.indicator B (fun _ => (1 : ENNReal)) q) ∘ (fun (p : (ℕ → ℕ∞) × R) => (restr p.1, p.2)) := by
        ext p
        simp [f, Set.indicator]
      rw [h_eq]
      exact (Measurable.indicator measurable_const hB).comp h_meas_prod_map
    have h_int_meas : Measurable (fun (r : R) => ∫⁻ G, f (G, r) ∂Q) :=
      Measurable.lintegral_prod_left' hf_meas
    have h_eq (r : R) : (∫⁻ G, f (G, r) ∂Q) = Q {G : ℕ → ℕ∞ | (restr G, r) ∈ B} := by
      dsimp [f]
      rw [lintegral_indicator_const (hSr_meas r) (1 : ENNReal), one_mul]
    convert h_int_meas using 1
    ext r
    simp [h_eq r]
  -- Measurability of r ↦ ∫⁻ G, Sr.indicator (fun G' => (G' e : ENNReal)) G ∂Q
  have h_meas_fe : Measurable (fun (r : R) =>
    ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' e : ENNReal)) G ∂Q) := by
    let f : (ℕ → ℕ∞) × R → ENNReal := fun p =>
      Set.indicator B (fun _ => (1 : ENNReal)) (restr p.1, p.2) * (p.1 e : ENNReal)
    have hf_meas : Measurable f := by
      refine Measurable.mul ?_ ?_
      · exact (Measurable.indicator measurable_const hB).comp h_meas_prod_map
      · have h_eval : Measurable (fun (f' : ℕ → ℕ∞) => (f' e : ENNReal)) :=
          h_coe_meas.comp (measurable_pi_apply (a := e))
        exact h_eval.comp measurable_fst
    have h_int_meas : Measurable (fun (r : R) => ∫⁻ G, f (G, r) ∂Q) :=
      Measurable.lintegral_prod_left' hf_meas
    have h_eq (r : R) : (∫⁻ G, f (G, r) ∂Q) =
      ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' e : ENNReal)) G ∂Q := by
      dsimp [f]
      refine lintegral_congr fun G => ?_
      by_cases h : (restr G, r) ∈ B
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    convert h_int_meas using 1
    ext r
    simp [h_eq r]
  -- Measurability of r ↦ ∫⁻ G, Sr.indicator (fun G' => (G' J : ENNReal)) G ∂Q
  have h_meas_fJ : Measurable (fun (r : R) =>
    ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' J : ENNReal)) G ∂Q) := by
    let f : (ℕ → ℕ∞) × R → ENNReal := fun p =>
      Set.indicator B (fun _ => (1 : ENNReal)) (restr p.1, p.2) * (p.1 J : ENNReal)
    have hf_meas : Measurable f := by
      refine Measurable.mul ?_ ?_
      · exact (Measurable.indicator measurable_const hB).comp h_meas_prod_map
      · have h_eval : Measurable (fun (f' : ℕ → ℕ∞) => (f' J : ENNReal)) :=
          h_coe_meas.comp (measurable_pi_apply (a := J))
        exact h_eval.comp measurable_fst
    have h_int_meas : Measurable (fun (r : R) => ∫⁻ G, f (G, r) ∂Q) :=
      Measurable.lintegral_prod_left' hf_meas
    have h_eq (r : R) : (∫⁻ G, f (G, r) ∂Q) =
      ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' J : ENNReal)) G ∂Q := by
      dsimp [f]
      refine lintegral_congr fun G => ?_
      by_cases h : (restr G, r) ∈ B
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    convert h_int_meas using 1
    ext r
    simp [h_eq r]
  -- Measurability of p ↦ (p.1 J : ENNReal) for the indicator
  have h_meas_pJ : Measurable (fun (p : (ℕ → ℕ∞) × R) => (p.1 J : ENNReal)) := by
    have h_eval : Measurable (fun (f : ℕ → ℕ∞) => (f J : ENNReal)) :=
      h_coe_meas.comp (measurable_pi_apply (a := J))
    have h_fst : Measurable (fun (p : (ℕ → ℕ∞) × R) => p.1) := measurable_fst
    exact h_eval.comp h_fst
  -- Measurability of p ↦ (p.1 e : ENNReal)
  have h_meas_pe : Measurable (fun (p : (ℕ → ℕ∞) × R) => (p.1 e : ENNReal)) := by
    have h_eval : Measurable (fun (f : ℕ → ℕ∞) => (f e : ENNReal)) :=
      h_coe_meas.comp (measurable_pi_apply (a := e))
    have h_fst : Measurable (fun (p : (ℕ → ℕ∞) × R) => p.1) := measurable_fst
    exact h_eval.comp h_fst
  -- Measurability of the indicator of S
  have h_meas_ind_S_J : Measurable (S.indicator (fun (p : (ℕ → ℕ∞) × R) => (p.1 J : ENNReal))) :=
    Measurable.indicator h_meas_pJ hS_meas
  have h_meas_ind_S_e : Measurable (S.indicator (fun (p : (ℕ → ℕ∞) × R) => (p.1 e : ENNReal))) :=
    Measurable.indicator h_meas_pe hS_meas
  -- Rewrite LHS using Tonelli (lintegral_prod_symm gives ∫⁻ r, ∫⁻ G, ... ∂Q ∂ρ)
  have hLHS : ∫⁻ p in S, (p.1 J : ℝ≥0∞) ∂(Q.prod ρ) =
    ∫⁻ r, ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' J : ENNReal)) G ∂Q ∂ρ := by
    calc
      ∫⁻ p in S, (p.1 J : ℝ≥0∞) ∂(Q.prod ρ) = ∫⁻ p, S.indicator (fun (p : (ℕ → ℕ∞) × R) => (p.1 J : ENNReal)) p ∂(Q.prod ρ) := by
        rw [lintegral_indicator hS_meas]
      _ = ∫⁻ r, ∫⁻ G, S.indicator (fun (p : (ℕ → ℕ∞) × R) => (p.1 J : ENNReal)) (G, r) ∂Q ∂ρ := by
        rw [lintegral_prod_symm _ h_meas_ind_S_J.aemeasurable]
      _ = ∫⁻ r, ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' J : ENNReal)) G ∂Q ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr fun G => ?_
        simp [S, restr, Set.indicator]
  -- Rewrite RHS first term using Tonelli
  have hRHS1 : ∫⁻ p in S, (p.1 e : ℝ≥0∞) ∂(Q.prod ρ) =
    ∫⁻ r, ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' e : ENNReal)) G ∂Q ∂ρ := by
    calc
      ∫⁻ p in S, (p.1 e : ℝ≥0∞) ∂(Q.prod ρ) = ∫⁻ p, S.indicator (fun (p : (ℕ → ℕ∞) × R) => (p.1 e : ENNReal)) p ∂(Q.prod ρ) := by
        rw [lintegral_indicator hS_meas]
      _ = ∫⁻ r, ∫⁻ G, S.indicator (fun (p : (ℕ → ℕ∞) × R) => (p.1 e : ENNReal)) (G, r) ∂Q ∂ρ := by
        rw [lintegral_prod_symm _ h_meas_ind_S_e.aemeasurable]
      _ = ∫⁻ r, ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' e : ENNReal)) G ∂Q ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr fun G => ?_
        simp [S, restr, Set.indicator]
  -- Rewrite (Q.prod ρ) S using Tonelli
  have h_prod_apply : (Q.prod ρ) S = ∫⁻ r, Q {G : ℕ → ℕ∞ | (restr G, r) ∈ B} ∂ρ := by
    calc
      (Q.prod ρ) S = (1 : ENNReal) * (Q.prod ρ) S := by simp
      _ = ∫⁻ p, S.indicator (fun _ => (1 : ENNReal)) p ∂(Q.prod ρ) := by
        rw [lintegral_indicator_const hS_meas (1 : ENNReal)]
      _ = ∫⁻ r, ∫⁻ G, S.indicator (fun _ => (1 : ENNReal)) (G, r) ∂Q ∂ρ := by
        rw [lintegral_prod_symm _ (Measurable.indicator measurable_const hS_meas).aemeasurable]
      _ = ∫⁻ r, ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun _ => (1 : ENNReal)) G ∂Q ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr fun G => ?_
        simp [S, restr, Set.indicator]
      _ = ∫⁻ r, Q {G : ℕ → ℕ∞ | (restr G, r) ∈ B} ∂ρ := by
        refine lintegral_congr fun r => ?_
        rw [lintegral_indicator_const (hSr_meas r) (1 : ENNReal), one_mul]
  -- Now the main inequality
  rw [hLHS, hRHS1, h_prod_apply]
  -- Goal: ∫⁻ r, fJ(r) ∂ρ ≤ ∫⁻ r, fe(r) ∂ρ + (∫⁻ r, Q(Sr) ∂ρ) * c
  let c : ENNReal := ∫⁻ G, (G (J - e) : ENNReal) ∂Q
  have h_pointwise (r : R) :
    (∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' J : ENNReal)) G ∂Q) ≤
    (∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' e : ENNReal)) G ∂Q) +
    Q {G : ℕ → ℕ∞ | (restr G, r) ∈ B} * c := by
    -- Apply hfd to Br = {h | (h, r) ∈ B}
    have h_set_eq : {G : ℕ → ℕ∞ | (restr G, r) ∈ B} = {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ {h : Fin (e + 1) → ℕ∞ | (h, r) ∈ B}} := by
      ext G; simp [restr]
    rw [h_set_eq]
    have h_ineq := hfd {h : Fin (e + 1) → ℕ∞ | (h, r) ∈ B}
    have h_left : ∫⁻ G in {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ {h : Fin (e + 1) → ℕ∞ | (h, r) ∈ B}}, (G J : ENNReal) ∂Q =
      ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' J : ENNReal)) G ∂Q := by
      have h_set_eq2 : {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ {h : Fin (e + 1) → ℕ∞ | (h, r) ∈ B}} =
        {G : ℕ → ℕ∞ | (restr G, r) ∈ B} := by
        ext G; simp [restr]
      rw [h_set_eq2, lintegral_indicator (hSr_meas r)]
    have h_right1 : ∫⁻ G in {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ {h : Fin (e + 1) → ℕ∞ | (h, r) ∈ B}}, (G e : ENNReal) ∂Q =
      ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' e : ENNReal)) G ∂Q := by
      have h_set_eq2 : {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ {h : Fin (e + 1) → ℕ∞ | (h, r) ∈ B}} =
        {G : ℕ → ℕ∞ | (restr G, r) ∈ B} := by
        ext G; simp [restr]
      rw [h_set_eq2, lintegral_indicator (hSr_meas r)]
    have h_right2 : Q {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ {h : Fin (e + 1) → ℕ∞ | (h, r) ∈ B}} =
      Q {G : ℕ → ℕ∞ | (restr G, r) ∈ B} := by
      simp [restr]
    rw [h_left, h_right1, h_right2] at h_ineq
    simpa [c] using h_ineq
  -- Now apply the pointwise inequality to the outer integral
  let fe' (r : R) := ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' e : ENNReal)) G ∂Q
  let QSr (r : R) := Q {G : ℕ → ℕ∞ | (restr G, r) ∈ B}
  have h_meas_fe' : Measurable fe' := h_meas_fe
  have h_meas_QSr' : Measurable QSr := h_meas_QSr
  have h_sum' : Measurable (fun (r : R) => fe' r + QSr r * c) := h_meas_fe.add (h_meas_QSr.mul measurable_const)
  calc
    ∫⁻ r, ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' J : ENNReal)) G ∂Q ∂ρ
        ≤ ∫⁻ r, (fe' r + QSr r * c) ∂ρ := by
      refine lintegral_mono fun r => ?_
      simpa [fe', QSr] using h_pointwise r
    _ = (∫⁻ r, fe' r ∂ρ) + (∫⁻ r, QSr r * c ∂ρ) := by
      rw [lintegral_add_right (f := fe') (g := fun r => QSr r * c) (h_meas_QSr'.mul measurable_const)]
    _ = (∫⁻ r, fe' r ∂ρ) + (∫⁻ r, QSr r ∂ρ) * c := by
      rw [lintegral_mul_const c h_meas_QSr']
    _ = (∫⁻ r, ∫⁻ G, ({G' : ℕ → ℕ∞ | (restr G', r) ∈ B}).indicator (fun (G' : ℕ → ℕ∞) => (G' e : ENNReal)) G ∂Q ∂ρ) +
        (∫⁻ r, Q {G : ℕ → ℕ∞ | (restr G, r) ∈ B} ∂ρ) * c := by
      simp [fe', QSr]

end FrogModel.D3.Iface
