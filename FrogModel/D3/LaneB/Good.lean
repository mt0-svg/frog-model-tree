module

public import FrogModel.D3.LaneB.Lemma12

@[expose] public section

/-!
# The planted curve is good almost surely

A good curve is nondecreasing with `G(k) ≤ k + B` (Lemma 10.2 (2) of the paper); the planted curve at
height `m` is good with `B = (3^(m+1) - 1)/2` (the frogs of the subtree), and so are the three
children of the closure, almost surely.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface


/-- A curve that is nondecreasing and has `G(k) ≤ k + B`. -/
def GoodC (B : ℕ) (G : ℕ → ℕ∞) : Prop := Monotone G ∧ ∀ k, G k ≤ ((k + B : ℕ) : ℕ∞)

theorem measurableSet_goodC (B : ℕ) : MeasurableSet {G : ℕ → ℕ∞ | GoodC B G} := by
  have h : {G : ℕ → ℕ∞ | GoodC B G} =
      (⋂ k, {G : ℕ → ℕ∞ | G k ≤ G (k + 1)}) ∩ ⋂ k, {G : ℕ → ℕ∞ | G k ≤ ((k + B : ℕ) : ℕ∞)} := by
    ext G
    simp only [GoodC, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨fun k => h.1 (Nat.le_succ k), h.2⟩,
      fun h => ⟨monotone_nat_of_le_succ h.1, h.2⟩⟩
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun k => ?_) (MeasurableSet.iInter fun k => ?_)
  · have hk : Measurable fun G : ℕ → ℕ∞ => G k := measurable_pi_apply k
    have hk1 : Measurable fun G : ℕ → ℕ∞ => G (k + 1) := measurable_pi_apply (k + 1)
    have : {G : ℕ → ℕ∞ | G k ≤ G (k + 1)} =
        ⋃ a : ℕ∞, (fun G : ℕ → ℕ∞ => G k) ⁻¹' {a} ∩ (fun G : ℕ → ℕ∞ => G (k + 1)) ⁻¹' Set.Ici a := by
      ext G; simp
    rw [this]
    exact MeasurableSet.iUnion fun a =>
      (hk (measurableSet_singleton a)).inter (hk1 (MeasurableSet.of_discrete))
  · have hk : Measurable fun G : ℕ → ℕ∞ => G k := measurable_pi_apply k
    exact hk (MeasurableSet.of_discrete (s := Set.Iic ((k + B : ℕ) : ℕ∞)))

/-- The planted curve is good, almost surely, with `B = (3^(m+1) - 1)/2`. -/
theorem ae_goodC (hmeas : measurable_plantedPair) (m : ℕ) :
    ∀ᵐ G ∂curveLaw m, GoodC ((3 ^ (m + 1) - 1) / 2) G := by
  unfold curveLaw
  rw [ae_map_iff (hmeas m).fst.aemeasurable (measurableSet_goodC _)]
  refine Filter.Eventually.of_forall fun π =>
    ⟨monotone_nat_of_le_succ fun k => plantedG_mono m k π, fun k => ?_⟩
  exact plantedG_le_frogs_proof m k π

/-- Good children, almost surely in the closure. -/
theorem ae_closGood (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (B : ℕ)
    (h : ∀ᵐ G ∂Q, GoodC B G) : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c) := by
  unfold closMeasure
  have h1 : ∀ᵐ G ∂(Measure.pi fun _ : Fin 3 => Q), ∀ c, GoodC B (G c) :=
    ae_all_iff.2 fun c => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 3 => Q)).eventually h
  exact Measure.quasiMeasurePreserving_fst.ae h1

end FrogModel.D3.Iface
