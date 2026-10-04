module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# The law of the closure

Each child curve of the closure has law `Q`, and forgetting the extra data of an enriched closure
gives the closure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- Each child curve of the closure has law `Q`. -/
theorem measurePreserving_child (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (c : Fin 3) : MeasurePreserving (fun x : ClosSample => x.1 c) (closMeasure Q) Q := by
  have h_dir_prob : IsProbabilityMeasure (dirMeasure) := by
    unfold dirMeasure
    infer_instance
  have h_fst : MeasurePreserving (Prod.fst : ClosSample → (Fin 3 → ℕ → ℕ∞)) (closMeasure Q) (Measure.pi fun _ : Fin 3 => Q) :=
    measurePreserving_fst
  have h_eval : MeasurePreserving (Function.eval c) (Measure.pi fun _ : Fin 3 => Q) Q :=
    measurePreserving_eval (μ := fun _ : Fin 3 => Q) c
  exact h_eval.comp h_fst

/-- Forgetting the extra data of the children and the auxiliary randomness maps the enriched closure
to the closure. -/
theorem forget_map {Ωc Ωa : Type*} [MeasurableSpace Ωc] [MeasurableSpace Ωa]
    (μc : Measure ((ℕ → ℕ∞) × Ωc)) [IsProbabilityMeasure μc] (ν : Measure Ωa)
    [IsProbabilityMeasure ν] :
    ((Measure.pi fun _ : Fin 3 => μc).prod (dirMeasure.prod ν)).map
        (fun y => ((fun c => (y.1 c).1), y.2.1)) =
      closMeasure (μc.map Prod.fst) := by
  have hf : Measurable (fun (Y : Fin 3 → (ℕ → ℕ∞) × Ωc) (c : Fin 3) => (Y c).1) := by
    refine Measurable.of_eval fun c => ?_
    exact (measurable_fst.comp (measurable_pi_apply c))
  have hg : Measurable (Prod.fst : (ℕ → Fin 4) × Ωa → ℕ → Fin 4) := measurable_fst
  have h_map_eq : (fun y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) =>
      ((fun c => (y.1 c).1), y.2.1)) = Prod.map (fun (Y : Fin 3 → (ℕ → ℕ∞) × Ωc) (c : Fin 3) => (Y c).1) Prod.fst := by
    ext ⟨Y, D⟩ <;> rfl
  have : SFinite dirMeasure := by
    -- dirMeasure is a probability measure, hence SFinite
    have : IsProbabilityMeasure dirMeasure := by
      unfold dirMeasure
      infer_instance
    exact inferInstance
  have : SFinite (dirMeasure.prod ν) := by
    infer_instance
  have : SFinite (μc.map Prod.fst) := by
    have : IsProbabilityMeasure (μc.map Prod.fst) := by
      infer_instance
    exact inferInstance
  rw [h_map_eq]
  rw [← MeasureTheory.Measure.map_prod_map (Measure.pi fun _ : Fin 3 => μc) (dirMeasure.prod ν) hf hg]
  rw [MeasureTheory.Measure.pi_map_pi (μ := fun _ : Fin 3 => μc) (f := fun _ => Prod.fst)]
  · rw [MeasureTheory.Measure.map_fst_prod]
    have hν_univ : ν Set.univ = 1 := by
      simp
    simp [hν_univ, closMeasure]
  · intro i
    exact measurable_fst.aemeasurable

/-- The closure measure is invariant under relabeling the children by a permutation `σ` and the
directions accordingly. -/
theorem closMeasure_perm (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (σ : Equiv.Perm (Fin 3)) :
    (closMeasure Q).map (fun x : ClosSample =>
      ((fun c' => x.1 (σ c')), (fun i => Fin.cases 0 (fun c' => (σ.symm c').succ) (x.2 i)))) =
      closMeasure Q := by
  -- Define τ : Fin 4 → Fin 4 as the relabeling of directions
  let τ : Fin 4 → Fin 4 := fun d => Fin.cases 0 (fun c' => (σ.symm c').succ) d
  let τ_inv : Fin 4 → Fin 4 := fun d => Fin.cases 0 (fun c' => (σ c').succ) d
  have hτ_meas : Measurable τ := measurable_of_finite τ
  -- τ and τ_inv are mutual inverses
  have h_left_inv : τ_inv ∘ τ = id := by
    ext d
    refine Fin.induction ?_ ?_ d
    · simp [τ, τ_inv]
    · intro d' ih
      simp [τ, τ_inv, Fin.cases_succ, Equiv.apply_symm_apply]
  have h_right_inv : τ ∘ τ_inv = id := by
    ext d
    refine Fin.induction ?_ ?_ d
    · simp [τ, τ_inv]
    · intro d' ih
      simp [τ, τ_inv, Fin.cases_succ, Equiv.symm_apply_apply]
  have h_left_inv' : ∀ x, τ_inv (τ x) = x := fun x => congrFun h_left_inv x
  have h_right_inv' : ∀ x, τ (τ_inv x) = x := fun x => congrFun h_right_inv x
  have hτ_inj : Function.Injective τ := by
    intro a b h
    calc
      a = τ_inv (τ a) := by rw [h_left_inv']
      _ = τ_inv (τ b) := by rw [h]
      _ = b := by rw [h_left_inv']
  -- The map on the first component: permute children by σ
  let f : (Fin 3 → ℕ → ℕ∞) ≃ᵐ (Fin 3 → ℕ → ℕ∞) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℕ → ℕ∞) σ.symm
  -- The map on the second component: relabel directions by τ
  let g : (ℕ → Fin 4) → (ℕ → Fin 4) := fun D i => τ (D i)
  have h_map : (fun x : ClosSample =>
      ((fun c' => x.1 (σ c')), (fun i => Fin.cases 0 (fun c' => (σ.symm c').succ) (x.2 i)))) =
      Prod.map (f : (Fin 3 → ℕ → ℕ∞) → (Fin 3 → ℕ → ℕ∞)) g := by
    ext x
    · simp [f, g, τ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    · simp [g, τ]
  rw [h_map]
  rw [closMeasure]
  have h_sfinite_pi : SFinite (Measure.pi fun _ : Fin 3 => Q) := by
    infer_instance
  have h_sfinite_dir : SFinite dirMeasure := by
    unfold dirMeasure
    infer_instance
  rw [← Measure.map_prod_map (μa := Measure.pi fun _ : Fin 3 => Q)
    (μc := dirMeasure) (hf := f.measurable) (hg := ?_)]
  congr 1
  · -- first factor: (Measure.pi fun _ : Fin 3 => Q).map f = Measure.pi fun _ : Fin 3 => Q
    rw [MeasureTheory.Measure.pi_map_piCongrLeft (e := σ.symm) (μ := fun _ : Fin 3 => Q)]
  · -- second factor: dirMeasure.map g = dirMeasure
    unfold dirMeasure
    rw [Measure.infinitePi_map_pi (μ := fun _ : ℕ => (uniformOn Set.univ : Measure (Fin 4)))
      (f := fun (_ : ℕ) => τ) (hf := fun _ => hτ_meas)]
    congr
    ext s hs
    -- need to show (uniformOn Set.univ).map τ = uniformOn Set.univ
    have h_uniformOn_map : (uniformOn (Set.univ : Set (Fin 4))).map τ = uniformOn (Set.univ : Set (Fin 4)) := by
      ext s hs
      rw [Measure.map_apply (measurable_of_finite τ) hs]
      rw [uniformOn_univ, uniformOn_univ]
      -- Goal: count (τ ⁻¹' s) / Fintype.card = count s / Fintype.card
      have h_preimage : τ ⁻¹' s = τ_inv '' s := by
        ext x; constructor
        · intro hx
          refine ⟨τ x, hx, ?_⟩
          rw [h_left_inv' x]
        · rintro ⟨y, hy, rfl⟩
          -- Goal: τ_inv y ∈ τ ⁻¹' s
          -- This is definitionally τ (τ_inv y) ∈ s
          simpa [h_right_inv' y] using hy
      rw [h_preimage]
      -- count (τ_inv '' s) = count s because τ_inv is injective
      have h_inj : Function.Injective τ_inv := by
        intro a b h
        calc
          a = τ (τ_inv a) := by rw [h_right_inv']
          _ = τ (τ_inv b) := by rw [h]
          _ = b := by rw [h_right_inv']
      rw [Measure.count_injective_image h_inj s]
    rw [h_uniformOn_map]
  · -- g is measurable
    refine Measurable.of_eval (fun i => ?_)
    exact hτ_meas.comp (measurable_pi_apply i)

end FrogModel.D3.Iface
