module

public import FrogModel.ZeroOne.Defs
public import FrogModel.Lemmas.Refresh

@[expose] public section

/-!
# Levy's 0-1 law, the filtration of the frogs at depth at most n, independence of the deep frogs

The first two steps of the proof of Theorem 9.3 of the paper: Lévy's upward theorem, and the copy of
`T*` below the first vertex at depth `n + 1` of the root frog, independent of the frogs at depth at
most `n`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.ZeroOne

/-- Lévy's 0-1 law in the form used here: an event of the limit σ-algebra which has
conditional probability at least `q > 0` on every event of every `ℱ n` has probability one. -/
theorem FrogModel.ZeroOne.levy_one {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (R : Set Ω)
    (hR : MeasurableSet[⨆ n, ℱ n] R) (q : ℝ≥0∞) (hq : 0 < q)
    (h : ∀ (n : ℕ) (A : Set Ω), MeasurableSet[ℱ n] A → q * μ A ≤ μ (R ∩ A)) :
    μ R = 1 := by
  have hle : (⨆ n, ℱ n) ≤ m0 := iSup_le fun n => ℱ.le n
  have hRm : MeasurableSet R := hle R hR
  have hq1 : q ≤ 1 := by
    have := h 0 Set.univ MeasurableSet.univ
    rw [measure_univ, mul_one, Set.inter_univ] at this
    exact this.trans prob_le_one
  have hqtop : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq1
  set r := q.toReal with hr
  have hr0 : 0 < r := ENNReal.toReal_pos hq.ne' hqtop
  set g : Ω → ℝ := R.indicator fun _ => (1 : ℝ) with hg
  have hgi : Integrable g μ := (integrable_const (1 : ℝ)).indicator hRm
  have hgm : StronglyMeasurable[⨆ n, ℱ n] g := stronglyMeasurable_const.indicator hR
  have hlim := hgi.tendsto_ae_condExp (ℱ := ℱ) hgm
  -- conditional probabilities are at least `r`
  have hbound : ∀ n, ∀ᵐ x ∂μ, r ≤ (μ[g|ℱ n]) x := by
    intro n
    have hsm : StronglyMeasurable[ℱ n] (μ[g|ℱ n]) := stronglyMeasurable_condExp
    have hA : ∀ ε : ℝ, 0 < ε → μ {x | (μ[g|ℱ n]) x ≤ r - ε} = 0 := by
      intro ε hε
      set A := {x | (μ[g|ℱ n]) x ≤ r - ε} with hAdef
      have hAn : MeasurableSet[ℱ n] A := hsm.measurableSet_le stronglyMeasurable_const
      have hAm : MeasurableSet A := ℱ.le n A hAn
      have h1 : ∫ x in A, (μ[g|ℱ n]) x ∂μ = μ.real (R ∩ A) := by
        rw [setIntegral_condExp (ℱ.le n) hgi hAn, hg, setIntegral_indicator hRm,
          setIntegral_const, smul_eq_mul, mul_one, Set.inter_comm]
      have h2 : ∫ x in A, (μ[g|ℱ n]) x ∂μ ≤ (r - ε) * μ.real A := by
        calc ∫ x in A, (μ[g|ℱ n]) x ∂μ ≤ ∫ x in A, (r - ε) ∂μ :=
              setIntegral_mono_on integrable_condExp.integrableOn (integrableOn_const) hAm
                fun x hx => hx
          _ = (r - ε) * μ.real A := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      have h3 : r * μ.real A ≤ μ.real (R ∩ A) := by
        have := h n A hAn
        have h' := ENNReal.toReal_mono (measure_ne_top μ _) this
        rwa [ENNReal.toReal_mul] at h'
      have h4 : ε * μ.real A ≤ 0 := by nlinarith
      have h5 : μ.real A = 0 := le_antisymm (by
        have := measureReal_nonneg (μ := μ) (s := A)
        nlinarith) measureReal_nonneg
      exact (measureReal_eq_zero_iff (measure_ne_top μ A)).1 h5
    have hU : {x | (μ[g|ℱ n]) x < r} ⊆ ⋃ k : ℕ, {x | (μ[g|ℱ n]) x ≤ r - 1 / ((k : ℝ) + 1)} := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact Set.mem_iUnion.2 ⟨k, by simp only [Set.mem_ofPred_eq]; linarith⟩
    have hnull : μ {x | (μ[g|ℱ n]) x < r} = 0 :=
      measure_mono_null hU (measure_iUnion_null fun k => hA _ (by positivity))
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    simpa using hx
  have hall := ae_all_iff.2 hbound
  have hmem : ∀ᵐ x ∂μ, x ∈ R := by
    filter_upwards [hlim, hall] with x hx hxb
    have hgx : r ≤ g x := ge_of_tendsto' hx hxb
    by_contra hxR
    have : g x = 0 := Set.indicator_of_notMem hxR _
    linarith
  have hc : μ Rᶜ = 0 := by
    rw [ae_iff] at hmem
    exact hmem
  rwa [prob_compl_eq_zero_iff hRm] at hc

/-- The frogs at all depths generate the σ-algebra of the sample space. -/
theorem FrogModel.ZeroOne.iSup_nearFiltration (d : ℕ) :
    (⨆ n, nearFiltration d n) = (inferInstance : MeasurableSpace (Sample d)) := by
  refine le_antisymm (iSup_le fun n => (nearFiltration d).le n) ?_
  change MeasurableSpace.pi ≤ _
  refine iSup_le fun v => ?_
  have h1 : MeasurableSpace.comap (fun ω : Sample d => ω v) inferInstance ≤ nearSigma d v.length :=
    le_iSup₂ (f := fun (u : Vertex d) (_ : u.length ≤ v.length) =>
      MeasurableSpace.comap (fun ω : Sample d => ω u) inferInstance) v le_rfl
  exact h1.trans (le_iSup (fun n => nearFiltration d n) v.length)

/-- The sample of the planted tree at `w` has the law of the frog model. -/
theorem FrogModel.ZeroOne.map_shift {d : ℕ} [NeZero d] (w : Vertex d) :
    (frogMeasure d).map (shift w) = frogMeasure d := by
  unfold frogMeasure shift
  exact FrogModel.infinitePi_map_comp_injective _ (fun v => v ++ w)
    (fun a b h => List.append_cancel_right h)

/-- The frogs at depth `≤ n` are independent of the frogs below depth `n`. -/
theorem FrogModel.ZeroOne.indep_near_far {d : ℕ} [NeZero d] (n : ℕ) :
    Indep (nearSigma d n) (farSigma d n) (frogMeasure d) := by
  have hf : iIndepFun (fun (v : Vertex d) (ω : Sample d) => ω v) (frogMeasure d) := by
    unfold frogMeasure
    exact iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
  have hind := (iIndepFun_iff_iIndep _ _ _).1 hf
  have hdisj : Disjoint {v : Vertex d | v.length ≤ n} {v : Vertex d | n < v.length} :=
    Set.disjoint_left.2 fun v h1 h2 => by
      simp only [Set.mem_ofPred_eq] at h1 h2
      omega
  exact indep_iSup_of_disjoint (fun v => (measurable_pi_apply v).comap_le) hind hdisj

/-- The sample of the planted tree at a vertex at depth `n + 1` is measurable for the frogs
below depth `n`. -/
theorem FrogModel.ZeroOne.measurable_shift_far {d : ℕ} (n : ℕ) (w : Vertex d)
    (hw : w.length = n + 1) :
    Measurable[farSigma d n] (shift w) := by
  refine @measurable_pi_iff _ _ _ (farSigma d n) _ _ |>.mpr fun v => ?_
  have hlen : n < (v ++ w).length := by simp only [List.length_append, hw]; omega
  have h1 : MeasurableSpace.comap (fun ω : Sample d => ω (v ++ w)) inferInstance ≤ farSigma d n :=
    le_iSup₂ (f := fun (u : Vertex d) (_ : n < u.length) =>
      MeasurableSpace.comap (fun ω : Sample d => ω u) inferInstance) (v ++ w) hlen
  exact Measurable.mono (comap_measurable (fun ω : Sample d => ω (v ++ w))) h1 le_rfl

/-- An event of the frogs at depth `≤ n` is independent of the sample of the planted tree at a
vertex at depth `n + 1`. -/
theorem FrogModel.ZeroOne.measure_inter_shift {d : ℕ} [NeZero d] (n : ℕ) (A : Set (Sample d))
    (hA : MeasurableSet[nearSigma d n] A) (w : Vertex d) (hw : w.length = n + 1)
    (S : Set (Sample d)) (hS : MeasurableSet S) :
    frogMeasure d (A ∩ shift w ⁻¹' S) = frogMeasure d A * frogMeasure d S := by
  have hshm : Measurable (shift (d := d) w) :=
    measurable_pi_iff.mpr fun v => measurable_pi_apply (v ++ w)
  have hB : MeasurableSet[farSigma d n] (shift w ⁻¹' S) := measurable_shift_far n w hw hS
  rw [(Indep_iff _ _ _).1 (indep_near_far n) A _ hA hB, ← Measure.map_apply hshm hS, map_shift]

/-- An event of the steps of the root frog is an event of the frogs at depth `≤ n`. -/
theorem FrogModel.ZeroOne.measurableSet_near_root {d : ℕ} (n : ℕ) (T : Set (ℕ → Step d))
    (hT : MeasurableSet T) :
    MeasurableSet[nearSigma d n] ((fun ω : Sample d => ω root) ⁻¹' T) := by
  have h1 : MeasurableSpace.comap (fun ω : Sample d => ω root) inferInstance ≤ nearSigma d n :=
    le_iSup₂ (f := fun (u : Vertex d) (_ : u.length ≤ n) =>
      MeasurableSpace.comap (fun ω : Sample d => ω u) inferInstance) root (Nat.zero_le n)
  exact h1 _ ⟨T, hT, rfl⟩
