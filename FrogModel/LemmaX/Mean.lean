module

public import FrogModel.LemmaX.Coupling

@[expose] public section

/-!
# Lemma X: the mean from the block bound

The end of the proof of Theorem 5.3 of the paper. The mean of `X^(K)` is the mean of the first
value of the curve under `N_K` (`lintegral_frozenCountK_eq`: the curve at `1` reads neither the
frog of `r` nor the initial frogs after the first, `curveK_congr`, and replacing the frog of `r` by
an independent copy keeps the law, `map_update_frogMeasure`). With Lemma 4.1 (`meanX_eq_iSup`)
and the block induction (`blockInduction`), a supersolution `Phi_J(H) ≤ H` bounds `E X`
(`lemmaXOfSuper`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaX FrogModel.Recursion

/-- Replacing one coordinate of an i.i.d. family by an independent variable of the same law
keeps the law of the family. -/
theorem FrogModel.LemmaX.infinitePi_update {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (i₀ : ι) :
    ((Measure.infinitePi fun _ : ι => μ).prod μ).map (fun p => Function.update p.1 i₀ p.2) =
      Measure.infinitePi fun _ : ι => μ := by
  have hu : Measurable fun p : (ι → X) × X => Function.update p.1 i₀ p.2 := measurable_update'
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hu (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  by_cases hs : i₀ ∈ s
  · have he : (fun p : (ι → X) × X => Function.update p.1 i₀ p.2) ⁻¹' (Set.pi (↑s) t) =
        Set.pi (↑(s.erase i₀)) t ×ˢ t i₀ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun i ⟨hi, his⟩ => ?_, ?_⟩
        · have := h i his
          rwa [Function.update_of_ne hi] at this
        · have := h i₀ hs
          rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ i his
        by_cases hi : i = i₀
        · subst hi
          rwa [Function.update_self]
        · rw [Function.update_of_ne hi]
          exact h1 i ⟨hi, his⟩
    rw [he, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i),
      Finset.prod_erase_mul _ _ hs]
  · have he : (fun p : (ι → X) × X => Function.update p.1 i₀ p.2) ⁻¹' (Set.pi (↑s) t) =
        Set.pi (↑s) t ×ˢ Set.univ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_univ,
        and_true]
      refine forall_congr' fun i => forall_congr' fun his => ?_
      have hi : i ≠ i₀ := fun h => hs (h ▸ his)
      rw [Function.update_of_ne hi]
    rw [he, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i), measure_univ, mul_one]

/-- The sample with the step sequence at `r` replaced by the first initial frog, independent,
has the law of the sample. -/
theorem FrogModel.LemmaX.map_update_frogMeasure (d : ℕ) [NeZero d] :
    ((frogMeasure d).prod (initMeasure d)).map (fun p => Function.update p.1 [] (p.2 0)) =
      frogMeasure d := by
  classical
  have hs : IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ => stepLaw d) := inferInstance
  have hev : Measurable fun ξ : ℕ → ℕ → Step d => ξ 0 := measurable_pi_apply 0
  have hu : Measurable fun q : Sample d × (ℕ → Step d) => Function.update q.1 [] q.2 :=
    measurable_update'
  have h1 : (fun p : Sample d × (ℕ → ℕ → Step d) => Function.update p.1 [] (p.2 0)) =
      (fun q : Sample d × (ℕ → Step d) => Function.update q.1 [] q.2) ∘
        Prod.map id (fun ξ => ξ 0) :=
    rfl
  have hfrog : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  have hinit : IsProbabilityMeasure (initMeasure d) := by unfold initMeasure; infer_instance
  rw [h1, ← Measure.map_map hu (measurable_id.prodMap hev),
    ← Measure.map_prod_map _ _ measurable_id hev, Measure.map_id]
  have h2 : (initMeasure d).map (fun ξ => ξ 0) = Measure.infinitePi fun _ : ℕ => stepLaw d := by
    unfold initMeasure
    exact Measure.infinitePi_map_eval _ 0
  rw [h2]
  unfold frogMeasure
  exact infinitePi_update _ []

/-- `E X^(K) = E G_K(1)`: the mean of the frozen count at kill depth `K` is the mean of the
first value of the curve under its law `N_K` (the first initial frog plays the frog of `r`). -/
theorem FrogModel.LemmaX.lintegral_frozenCountK_eq (d : ℕ) [NeZero d] (K : ℕ) :
    ∫⁻ ζ, frozenCountK K ζ ∂frogMeasure d = ∫⁻ G, ((G 1 : ℕ∞) : ℝ≥0∞) ∂curveLaw d K := by
  classical
  have hc := measurable_curveK (d := d) K
  have hcoe : Measurable fun x : ℕ∞ => (x : ℝ≥0∞) := measurable_of_countable _
  have hG1 : Measurable fun G : ℕ → ℕ∞ => ((G 1 : ℕ∞) : ℝ≥0∞) :=
    hcoe.comp (measurable_pi_apply 1)
  have hF : Measurable fun ζ : Sample d => ((curveK K ζ (fun _ => ζ []) 1 : ℕ∞) : ℝ≥0∞) := by
    have h0 : Measurable fun ζ : Sample d => (ζ, fun _ : ℕ => ζ []) :=
      measurable_id.prodMk (measurable_pi_iff.2 fun _ => measurable_pi_apply [])
    exact hG1.comp (hc.comp h0)
  have hU0 : Measurable fun q : Sample d × (ℕ → Step d) => Function.update q.1 [] q.2 :=
    measurable_update'
  have hU : Measurable fun p : Sample d × (ℕ → ℕ → Step d) => Function.update p.1 [] (p.2 0) :=
    hU0.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  unfold curveLaw
  rw [lintegral_map hG1 hc]
  simp_rw [frozenCountK_eq_curveK]
  conv_lhs => rw [← map_update_frogMeasure d]
  rw [lintegral_map hF hU]
  refine lintegral_congr fun p => ?_
  congr 1
  refine curveK_congr K 1 _ _ _ _ (fun v hv => Function.update_of_ne hv _ _) ?_
  intro a ha
  have ha0 : a = 0 := by omega
  subst ha0
  exact Function.update_self _ _ _

/-- **The mean from the block bound** (proof of Theorem 5.3 of the paper, with
Lemma 4.1): if `E_K ≤ H` for every `K`, then `E X ≤ E B(1)` for `B` of law `H`. -/
theorem FrogModel.LemmaX.meanOfBlockBound (d : ℕ) [NeZero d] (J : ℕ) (hJ : 0 < J)
    (H : Measure (Fin J → ℕ∞))
    (h : ∀ K, CouplingLE (blockLaw d K J) H) :
    meanX d ≤ ∫⁻ B, ((B ⟨0, hJ⟩ : ℕ∞) : ℝ≥0∞) ∂H := by
  rw [meanX_eq_iSup]
  refine iSup_le fun K => ?_
  have hf : Measurable fun B : Fin J → ℕ∞ => ((B ⟨0, hJ⟩ : ℕ∞) : ℝ≥0∞) :=
    measurable_of_countable _
  rw [lintegral_frozenCountK_eq d K]
  have e : ∫⁻ G, ((G 1 : ℕ∞) : ℝ≥0∞) ∂curveLaw d K =
      ∫⁻ B, ((B ⟨0, hJ⟩ : ℕ∞) : ℝ≥0∞) ∂blockLaw d K J := by
    unfold blockLaw
    rw [lintegral_map hf (measurable_firstValues J)]
    rfl
  rw [e]
  exact lintegral_mono_of_couplingLE (h K) _ hf (fun B B' hB => ENat.toENNReal_le.2 (hB _))

/-- **Lemma X from a supersolution** (Theorem 5.3 of the paper): Lemma 4.3 in domination form,
Claim A at `d` and `J`, and `Phi_J(H) ≤ H` give `E X ≤ E B(1)` for `B` of law `H`. -/
theorem FrogModel.LemmaX.lemmaXOfSuper (d : ℕ) [NeZero d] (J : ℕ) (hJ : 0 < J)
    (H : Measure (Fin J → ℕ∞))
    (h0 : CouplingLE (curveLaw d 0) (psiLaw d (Measure.dirac 0)))
    (hs : ∀ K, CouplingLE (curveLaw d (K + 1)) (psiLaw d (curveLaw d K)))
    (hA : ∀ K, CouplingLE (curveLaw d K) (brLaw J (blockLaw d K J)))
    (hH : CouplingLE (phiLaw d J H) H) : meanX d ≤ ∫⁻ B, ((B ⟨0, hJ⟩ : ℕ∞) : ℝ≥0∞) ∂H :=
  meanOfBlockBound d J hJ H (blockInduction d J H h0 hs hA hH)
