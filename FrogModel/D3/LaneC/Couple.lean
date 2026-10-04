module

public import FrogModel.D3.LaneC.LowerLaw

@[expose] public section

/-!
# The lower closure read from the children and their coins

Lower curves for the proof of Lemma 12.1 of the paper. Each child of the closure carries its
planted curve `G` and its coins `ξ` (Lemma 10.3, `coin_coupling`). Its lower curve answers the first
entry by `R = min(G(1), GM + 1)` and the entry `i + 2` by the coin `ξ (i + 1)`; it lies below `G`
almost surely (`lcurve_le`). Read from the children and the directions (`toL`), the randomness has
the law `lowMeasure` of the lower closure (`map_toL`), the first answers of law `rhoOf`, whose masses
are the pseudo-law `plR` of the cdf of `G(1)` (`rhoOf_plR`).
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneC.Lower

/-- The first answer of a lower curve: `min(G(1), GM + 1)`. -/
noncomputable def Rof (GM : ℕ) (G : ℕ → ℕ∞) : ℕ := (min (G 1) ((GM + 1 : ℕ) : ℕ∞)).toNat

/-- The coins of a lower curve: the coin of the entry `i + 2` is `ξ (i + 1)`. -/
def ζof (ξ : ℕ → Bool) : ℕ → Bool := fun i => ξ (i + 1)

/-- The randomness of the lower closure read from the children (curves and coins) and the
directions. -/
noncomputable def toL {Ωa : Type*} (GM : ℕ)
    (y : (Fin 3 → (ℕ → ℕ∞) × (ℕ → Bool)) × ((ℕ → Fin 4) × Ωa)) : LSample :=
  (y.2.1, (fun s => Rof GM (y.1 s).1, fun s => ζof (y.1 s).2))

/-- The law of the first answer `min(G(1), GM + 1)` for `G` of law `Q`. -/
noncomputable def rhoOf (Q : Measure (ℕ → ℕ∞)) (GM : ℕ) : Measure ℕ := Q.map (Rof GM)

theorem measurable_Rof (GM : ℕ) : Measurable (Rof GM) :=
  (measurable_of_countable fun x : ℕ∞ => (min x ((GM + 1 : ℕ) : ℕ∞)).toNat).comp
    (measurable_pi_apply 1)

theorem measurable_ζof : Measurable ζof :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1)

instance (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (GM : ℕ) :
    IsProbabilityMeasure (rhoOf Q GM) :=
  by unfold rhoOf; infer_instance

theorem measurable_toL {Ωa : Type*} [MeasurableSpace Ωa] (GM : ℕ) :
    Measurable (toL (Ωa := Ωa) GM) := by
  refine (measurable_fst.comp measurable_snd).prodMk ((measurable_pi_iff.mpr fun s => ?_).prodMk
    (measurable_pi_iff.mpr fun s => ?_))
  · exact (measurable_Rof GM).comp (measurable_fst.comp ((measurable_pi_apply s).comp measurable_fst))
  · exact measurable_ζof.comp (measurable_snd.comp ((measurable_pi_apply s).comp measurable_fst))

theorem Rof_le (GM : ℕ) (G : ℕ → ℕ∞) : Rof GM G ≤ GM + 1 := by
  unfold Rof
  have h : min (G 1) ((GM + 1 : ℕ) : ℕ∞) ≤ ((GM + 1 : ℕ) : ℕ∞) := min_le_right _ _
  have hne : min (G 1) ((GM + 1 : ℕ) : ℕ∞) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) h
  rw [← ENat.natCast_toNat hne, Nat.cast_le] at h
  exact h

theorem rhoOf_zero (Q : Measure (ℕ → ℕ∞)) (GM r : ℕ) (hr : GM + 1 < r) : rhoOf Q GM {r} = 0 := by
  unfold rhoOf
  rw [Measure.map_apply (measurable_Rof GM) (measurableSet_singleton r)]
  convert measure_empty (μ := Q)
  ext G
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  intro h
  have := Rof_le GM G
  omega

/-- The masses of `rhoOf` are the pseudo-law `plR` of the cdf of `G(1)`. -/
theorem rhoOf_plR (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (GM r : ℕ) :
    (rhoOf Q GM {r}).toReal = plR (fun g => (Q {G | G 1 ≤ (g : ℕ∞)}).toReal) GM r := by
  have h1 : Measurable fun G : ℕ → ℕ∞ => G 1 := measurable_pi_apply 1
  have hF : (fun g : ℕ => (Q {G | G 1 ≤ (g : ℕ∞)}).toReal) =
      fun g : ℕ => ((Q.map fun G => G 1) {x | x ≤ (g : ℕ∞)}).toReal := by
    funext g
    rw [Measure.map_apply h1 (MeasurableSet.of_discrete)]
    rfl
  rw [hF, plR_law]
  unfold rhoOf
  rw [Measure.map_apply (measurable_Rof GM) (measurableSet_singleton r),
    Measure.map_apply h1 (MeasurableSet.of_discrete)]
  rfl

section Coupling

variable (μ : Measure ((ℕ → ℕ∞) × (ℕ → Bool))) [IsProbabilityMeasure μ]

/-- One child: its first answer and its later coins have the law `rhoOf Q GM ⊗ coinSeq`. -/
theorem map_child (Q : Measure (ℕ → ℕ∞)) (hQ : μ.map Prod.fst = Q) (GM : ℕ)
    (hξ : ∀ i, μ {z | z.2 i = true} = 3⁻¹)
    (hind : ∀ i, IndepFun (fun z => z.2 i)
      (fun z => ((fun l : Fin (i + 1) => z.1 l), (fun l : Fin i => z.2 l))) μ) :
    μ.map (fun z => (Rof GM z.1, ζof z.2)) = (rhoOf Q GM).prod coinSeq := by
  have h1 : Measurable fun x : ℕ∞ => (min x ((GM + 1 : ℕ) : ℕ∞)).toNat := measurable_of_countable _
  have hP : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => (z.1 1, fun i => z.2 (i + 1)) :=
    ((measurable_pi_apply 1).comp measurable_fst).prodMk (measurable_ζof.comp measurable_snd)
  have hcomp : (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => (Rof GM z.1, ζof z.2)) =
      Prod.map (fun x : ℕ∞ => (min x ((GM + 1 : ℕ) : ℕ∞)).toNat) id ∘
        fun z => (z.1 1, fun i => z.2 (i + 1)) := rfl
  rw [hcomp, ← Measure.map_map (h1.prodMap measurable_id) hP, coins_indep_map μ hξ hind]
  rw [← Measure.map_prod_map _ _ h1 measurable_id, Measure.map_id]
  congr 1
  unfold rhoOf
  rw [← hQ, Measure.map_map (measurable_Rof GM) measurable_fst,
    Measure.map_map h1 ((measurable_pi_apply 1).comp measurable_fst)]
  rfl

/-- **The lower closure read from the children**: under the closure measure with coins, the
randomness `toL` has the law `lowMeasure (rhoOf Q GM)`. -/
theorem map_toL (Q : Measure (ℕ → ℕ∞)) (hQ : μ.map Prod.fst = Q) (GM : ℕ)
    (hξ : ∀ i, μ {z | z.2 i = true} = 3⁻¹)
    (hind : ∀ i, IndepFun (fun z => z.2 i)
      (fun z => ((fun l : Fin (i + 1) => z.1 l), (fun l : Fin i => z.2 l))) μ)
    [IsProbabilityMeasure Q] {Ωa : Type*} [MeasurableSpace Ωa] (ν : Measure Ωa)
    [IsProbabilityMeasure ν] :
    ((Measure.pi fun _ : Fin 3 => μ).prod (dirMeasure.prod ν)).map (toL GM) =
      lowMeasure (rhoOf Q GM) := by
  set Φ : (ℕ → ℕ∞) × (ℕ → Bool) → ℕ × (ℕ → Bool) := fun z => (Rof GM z.1, ζof z.2) with hΦdef
  have hΦ : Measurable Φ := ((measurable_Rof GM).comp measurable_fst).prodMk
    (measurable_ζof.comp measurable_snd)
  have hmapΦ : μ.map Φ = (rhoOf Q GM).prod coinSeq := map_child μ Q hQ GM hξ hind
  have hPhi : Measurable fun (Y : Fin 3 → (ℕ → ℕ∞) × (ℕ → Bool)) (s : Fin 3) => Φ (Y s) :=
    Measurable.of_eval fun s => hΦ.comp (measurable_pi_apply s)
  -- the children
  have hpi : (Measure.pi fun _ : Fin 3 => μ).map (fun Y s => Φ (Y s)) =
      Measure.pi fun _ : Fin 3 => (rhoOf Q GM).prod coinSeq := by
    rw [Measure.pi_map_pi (fun _ => hΦ.aemeasurable), hmapΦ]
  have hU : (Measure.pi fun _ : Fin 3 => μ).map
      ((MeasurableEquiv.arrowProdEquivProdArrow ℕ (ℕ → Bool) (Fin 3)) ∘ fun Y s => Φ (Y s)) =
      (Measure.pi fun _ : Fin 3 => rhoOf Q GM).prod (Measure.pi fun _ : Fin 3 => coinSeq) := by
    rw [← Measure.map_map (MeasurableEquiv.measurable _) hPhi, hpi]
    exact (measurePreserving_arrowProdEquivProdArrow ℕ (ℕ → Bool) (Fin 3)
      (fun _ => rhoOf Q GM) (fun _ => coinSeq)).map_eq
  have hUm : Measurable ((MeasurableEquiv.arrowProdEquivProdArrow ℕ (ℕ → Bool) (Fin 3)) ∘
      fun (Y : Fin 3 → (ℕ → ℕ∞) × (ℕ → Bool)) s => Φ (Y s)) :=
    (MeasurableEquiv.measurable _).comp hPhi
  have hdir : (dirMeasure.prod ν).map Prod.fst = dirMeasure := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have htoL : (toL (Ωa := Ωa) GM) = Prod.swap ∘ Prod.map
      ((MeasurableEquiv.arrowProdEquivProdArrow ℕ (ℕ → Bool) (Fin 3)) ∘ fun Y s => Φ (Y s))
      Prod.fst := rfl
  rw [htoL, ← Measure.map_map measurable_swap (hUm.prodMap measurable_fst),
    ← Measure.map_prod_map _ _ hUm measurable_fst, hU, hdir, Measure.prod_swap]
  rfl

/-- The lower curve of each child lies below its planted curve, almost surely. -/
theorem ae_lcurve_le (hae : ∀ᵐ z ∂μ, z.1 0 = 0 ∧ ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1))
    (GM : ℕ) {Ωa : Type*} [MeasurableSpace Ωa] (ν : Measure Ωa) [IsProbabilityMeasure ν] :
    ∀ᵐ y ∂((Measure.pi fun _ : Fin 3 => μ).prod (dirMeasure.prod ν)),
      ∀ s k, lcurve .fresh (Rof GM (y.1 s).1) (ζof (y.1 s).2) k ≤ (y.1 s).1 k := by
  have hz : ∀ᵐ z ∂μ, ∀ k, lcurve .fresh (Rof GM z.1) (ζof z.2) k ≤ z.1 k :=
    hae.mono fun z hz k => lcurve_le z.1 z.2 GM hz.2 k
  have hY : ∀ᵐ Y ∂(Measure.pi fun _ : Fin 3 => μ),
      ∀ s k, lcurve .fresh (Rof GM (Y s).1) (ζof (Y s).2) k ≤ (Y s).1 k :=
    ae_all_iff.2 fun s =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 3 => μ) (i := s)).eventually hz
  have hfst : ((Measure.pi fun _ : Fin 3 => μ).prod (dirMeasure.prod ν)).map Prod.fst =
      Measure.pi fun _ : Fin 3 => μ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [← hfst] at hY
  exact ae_of_ae_map measurable_fst.aemeasurable hY

end Coupling

end FrogModel.D3.LaneC.Lower
