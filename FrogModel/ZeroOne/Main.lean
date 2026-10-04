module

public import FrogModel.ZeroOne.Statement
public import FrogModel.ZeroOne.Levy
public import FrogModel.ZeroOne.Glue

@[expose] public section

/-!
# Theorem 9.3 of the paper: recurrence from infinitely many frozen frogs

The proof of Theorem 9.3. `measure_frozen_upRun_finite`: almost surely, when `T*`
has infinitely many frozen frogs, infinitely many of them run straight up for `n` steps after
their exit (the strong Markov property at the exit times, `map_glueExit`, and Borel-Cantelli
over the frozen frogs, `measure_finite_hits`). `near_bound`: given the frogs at depth at most
`n`, the root is visited infinitely often with probability at least `P(X = ∞)` (the root frog
first reaches depth `n + 1` at a vertex `w`; the frogs of the subtree at `w` are independent of
the frogs at depth at most `n` and form a copy of `T*`). Levy's 0-1 law gives
`recurrent_of_frozenCount`, and `recurrentOfFrozenCount_holds` is the frozen statement
`RecurrentOfFrozenCount` (ZeroOne/Statement.lean).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.ZeroOne

theorem FrogModel.ZeroOne.measurableSet_frozen {d : ℕ} (v : Vertex d) :
    MeasurableSet {ζ : Sample d | frozen ζ v} :=
  (measurableSet_reflTransGen_starArc d v).inter (measurableSet_exists_walkStar_none d v)

theorem FrogModel.ZeroOne.measurableSet_upRun_exit {d : ℕ} (n : ℕ) (v : Vertex d) :
    MeasurableSet {ζ : Sample d | upRun n (ζ v) (exitTime v (ζ v)).toNat} := by
  have h : {ζ : Sample d | upRun n (ζ v) (exitTime v (ζ v)).toNat} =
      ⋃ k : ℕ∞, (fun ζ : Sample d => ζ v) ⁻¹'
        ({x | exitTime v x = k} ∩ {x | upRun n x k.toNat}) := by
    ext ζ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_inter_iff]
    constructor
    · exact fun h => ⟨_, rfl, h⟩
    · rintro ⟨k, hk, h⟩
      rw [hk]
      exact h
  rw [h]
  exact MeasurableSet.iUnion fun k => (measurable_pi_apply v)
    (((measurable_exitTime v) (measurableSet_singleton k)).inter (measurableSet_upRun n k.toNat))

theorem FrogModel.ZeroOne.measurableSet_bad {d : ℕ} (n : ℕ) :
    MeasurableSet {ζ : Sample d | frozenCount ζ = ⊤ ∧
      {v | frozen ζ v ∧ upRun n (ζ v) (exitTime v (ζ v)).toNat}.Finite} :=
  (measurable_frozenCount d (measurableSet_singleton ⊤)).inter
    (measurableSet_setOf_finite (fun v => {ζ : Sample d | frozen ζ v ∧
      upRun n (ζ v) (exitTime v (ζ v)).toNat})
      fun v => (measurableSet_frozen v).inter (measurableSet_upRun_exit n v))

theorem FrogModel.ZeroOne.measurable_glueExit {d : ℕ} : Measurable (glueExit (d := d)) := by
  refine measurable_pi_iff.mpr fun v => measurable_pi_iff.mpr fun t => ?_
  have hF : Measurable fun q : (Sample d × Sample d) × ℕ∞ =>
      glueAt q.2 (q.1.1 v) (q.1.2 v) t := by
    refine measurable_from_prod_countable_left fun k => ?_
    by_cases h : (t : ℕ∞) < k
    · simp only [glueAt, h, ite_true]
      exact (measurable_pi_apply t).comp ((measurable_pi_apply v).comp measurable_fst)
    · simp only [glueAt, h, ite_false]
      exact (measurable_pi_apply _).comp ((measurable_pi_apply v).comp measurable_snd)
  exact hF.comp (measurable_id.prodMk
    ((measurable_exitTime v).comp ((measurable_pi_apply v).comp measurable_fst)))

/-- Almost surely, if `T*` has infinitely many frozen frogs, infinitely many of them take `n`
parent steps right after their exit. -/
theorem FrogModel.ZeroOne.measure_frozen_upRun_finite {d : ℕ} [NeZero d] (n : ℕ) :
    frogMeasure d {ζ | frozenCount ζ = ⊤ ∧
      {v | frozen ζ v ∧ upRun n (ζ v) (exitTime v (ζ v)).toNat}.Finite} = 0 := by
  have hP : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  set B' := {p : Sample d × Sample d | {v | frozen p.1 v}.Infinite ∧
      {v | frozen p.1 v ∧ upRun n (p.2 v) 0}.Finite} with hB'
  have hpre : glueExit ⁻¹' {ζ : Sample d | frozenCount ζ = ⊤ ∧
      {v | frozen ζ v ∧ upRun n (ζ v) (exitTime v (ζ v)).toNat}.Finite} = B' := by
    ext p
    simp only [hB', Set.mem_preimage, Set.mem_ofPred_eq]
    have hfr : ∀ v, frozen (glueExit p) v ↔ frozen p.1 v := frozen_glueExit p
    rw [frozenCount_eq_top_iff]
    have hset1 : {v | frozen (glueExit p) v} = {v | frozen p.1 v} := Set.ext fun v => hfr v
    have hset2 : {v | frozen (glueExit p) v ∧
        upRun n (glueExit p v) (exitTime v (glueExit p v)).toNat} =
          {v | frozen p.1 v ∧ upRun n (p.2 v) 0} := by
      ext v
      simp only [Set.mem_ofPred_eq, hfr]
      refine and_congr_right fun hv => ?_
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 ((exitTime_ne_top_iff v (p.1 v)).2 hv.2)
      rw [exitTime_glueExit, ← hk, ENat.toNat_natCast]
      unfold upRun
      refine forall₂_congr fun j _ => ?_
      rw [glueExit_after p v k j hk.symm, zero_add]
    rw [hset1, hset2]
  have hB'm : MeasurableSet B' := by
    have h1 : MeasurableSet {p : Sample d × Sample d | {v | p ∈ {q : Sample d × Sample d |
        frozen q.1 v}}.Finite} :=
      measurableSet_setOf_finite _ fun v => measurable_fst (measurableSet_frozen v)
    have hup : ∀ v, MeasurableSet {q : Sample d × Sample d | upRun n (q.2 v) 0} := fun v => by
      have hm : Measurable fun q : Sample d × Sample d => q.2 v :=
        (measurable_pi_apply v).comp measurable_snd
      exact hm (measurableSet_upRun n 0)
    have h2 : MeasurableSet {p : Sample d × Sample d | {v | p ∈ {q : Sample d × Sample d |
        frozen q.1 v ∧ upRun n (q.2 v) 0}}.Finite} :=
      measurableSet_setOf_finite _ fun v => (measurable_fst (measurableSet_frozen v)).inter (hup v)
    exact h1.compl.inter h2
  rw [← map_glueExit (d := d), Measure.map_apply measurable_glueExit (measurableSet_bad n), hpre,
    Measure.measure_prod_null hB'm]
  refine Filter.Eventually.of_forall fun a => ?_
  simp only [Pi.zero_apply]
  by_cases ha : {v | frozen a v}.Infinite
  · have hsec : Prod.mk a ⁻¹' B' = {b : Sample d | {v | v ∈ {v | frozen a v} ∧
        b v ∈ {x : ℕ → Step d | upRun n x 0}}.Finite} := by
      ext b
      simp only [hB', Set.mem_preimage, Set.mem_ofPred_eq, ha, true_and]
    rw [hsec]
    unfold frogMeasure
    exact measure_finite_hits _ _ (measurableSet_upRun n 0) (seqLaw_upRun_pos n) _ ha
  · have hsec : Prod.mk a ⁻¹' B' = ∅ := by
      ext b
      simp only [hB', Set.mem_preimage, Set.mem_ofPred_eq, ha, false_and, Set.mem_empty_iff_false]
    rw [hsec, measure_empty]

/-- Given the frogs at depth at most `n`, the root is visited infinitely often with
probability at least `P(X = ∞)`. -/
theorem FrogModel.ZeroOne.near_bound {d : ℕ} [NeZero d] (n : ℕ) (A : Set (Sample d))
    (hA : MeasurableSet[nearSigma d n] A) :
    frogMeasure d {ζ | frozenCount ζ = ⊤} * frogMeasure d A ≤
      frogMeasure d ({ω | (visits (paths ω)).Infinite} ∩ A) := by
  have hP : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  set F := {ζ : Sample d | frozenCount ζ = ⊤} with hF
  set Bad := {ζ : Sample d | frozenCount ζ = ⊤ ∧
      {v | frozen ζ v ∧ upRun n (ζ v) (exitTime v (ζ v)).toNat}.Finite} with hBad
  set E : Vertex d → Set (Sample d) := fun w =>
    (fun ω : Sample d => ω root) ⁻¹' {x | firstDeep (n + 1) x = some w} with hE
  set G : Vertex d → Set (Sample d) := fun w => A ∩ E w ∩ shift w ⁻¹' (F \ Bad) with hG
  have hFm : MeasurableSet F := measurable_frozenCount d (measurableSet_singleton ⊤)
  have hBadm : MeasurableSet Bad := measurableSet_bad n
  have hBad0 : frogMeasure d Bad = 0 := measure_frozen_upRun_finite n
  have hAm : MeasurableSet A := (nearFiltration d).le n A hA
  have hEnear : ∀ w, MeasurableSet[nearSigma d n] (E w) := fun w =>
    measurableSet_near_root n _ (measurableSet_firstDeep (n + 1) (some w))
  have hEm : ∀ w, MeasurableSet (E w) := fun w => (nearFiltration d).le n _ (hEnear w)
  have hshm : ∀ w, Measurable (shift (d := d) w) := fun w =>
    measurable_pi_iff.mpr fun v => measurable_pi_apply (v ++ w)
  have hGm : ∀ w, MeasurableSet (G w) := fun w =>
    (hAm.inter (hEm w)).inter (hshm w (hFm.diff hBadm))
  have hGR : ∀ w, G w ⊆ {ω | (visits (paths ω)).Infinite} := by
    rintro w ω ⟨⟨-, hEw⟩, hFB⟩
    obtain ⟨hlen, t, ht⟩ := firstDeep_spec (n + 1) (ω root) w hEw
    have hw : w ≠ [] := by
      rintro rfl
      simp at hlen
    have hR : Reach (paths ω) w := by
      have h := Reach.path (S := paths ω) t Reach.root
      have hpt : paths ω root t = w := ht
      rwa [hpt] at h
    obtain ⟨hF', hB'⟩ := hFB
    apply visits_infinite_of_upRun ω w hw hR
    rw [hlen, Nat.add_sub_cancel]
    intro hfin
    exact hB' ⟨hF', hfin⟩
  have hGμ : ∀ w, frogMeasure d (G w) = frogMeasure d (A ∩ E w) * frogMeasure d F := by
    intro w
    by_cases hw : w.length = n + 1
    · rw [show G w = (A ∩ E w) ∩ shift w ⁻¹' (F \ Bad) from rfl,
        measure_inter_shift n (A ∩ E w) (hA.inter (hEnear w)) w hw _ (hFm.diff hBadm),
        measure_sdiff_null hBad0]
    · have hE0 : E w = ∅ := by
        ext ω
        simp only [hE, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hw (firstDeep_spec _ _ _ h).1
      simp [hG, hE0]
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro w w' hww'
    refine Set.disjoint_left.2 fun ω h1 h2 => hww' ?_
    simp only [hE, Set.mem_preimage, Set.mem_ofPred_eq] at h1 h2
    exact Option.some.inj (h1.symm.trans h2)
  have hdisjG : Pairwise (Function.onFun Disjoint G) := fun w w' h =>
    (hdisj h).mono (fun _ hx => hx.1.2) (fun _ hx => hx.1.2)
  have hEunion : (⋃ w, E w)ᶜ =
      (fun ω : Sample d => ω root) ⁻¹' {x | firstDeep (n + 1) x = none} := by
    ext ω
    simp only [hE, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq,
      not_exists]
    cases firstDeep (n + 1) (ω root) with
    | none => simp
    | some w => simp
  have hEnull : frogMeasure d (⋃ w, E w)ᶜ = 0 := by
    rw [hEunion, ← Measure.map_apply (measurable_pi_apply root) (measurableSet_firstDeep _ none)]
    have hmap : (frogMeasure d).map (fun ω : Sample d => ω root) =
        Measure.infinitePi fun _ : ℕ => stepLaw d := by
      unfold frogMeasure
      exact Measure.infinitePi_map_eval _ root
    rw [hmap]
    exact firstDeep_ne_none (n + 1)
  calc frogMeasure d F * frogMeasure d A
      = frogMeasure d F * frogMeasure d (A ∩ ⋃ w, E w) := by rw [measure_inter_conull hEnull]
    _ = frogMeasure d F * ∑' w, frogMeasure d (A ∩ E w) := by
        rw [Set.inter_iUnion, measure_iUnion
          (fun w w' h => (hdisj h).mono Set.inter_subset_right Set.inter_subset_right)
          (fun w => hAm.inter (hEm w))]
    _ = ∑' w, frogMeasure d (G w) := by
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext w
        rw [hGμ, mul_comm]
    _ = frogMeasure d (⋃ w, G w) := (measure_iUnion hdisjG hGm).symm
    _ ≤ frogMeasure d ({ω | (visits (paths ω)).Infinite} ∩ A) :=
        measure_mono (Set.iUnion_subset fun w ω hω => ⟨hGR w hω, hω.1.1⟩)

/-- Theorem 9.3 of the paper: infinitely many frozen frogs in `T*` with positive probability give recurrence. -/
theorem FrogModel.ZeroOne.recurrent_of_frozenCount (d : ℕ) [NeZero d] (_hd : 2 ≤ d)
    (hX : 0 < frogMeasure d {ζ | frozenCount ζ = ⊤}) :
    ∀ᵐ ω ∂frogMeasure d, (visits (paths ω)).Infinite := by
  have hP : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  have hRm : MeasurableSet {ω : Sample d | (visits (paths ω)).Infinite} := by
    have := (measurableSet_finite_visits (d := d)).compl
    simpa [Set.compl_ofPred] using this
  have h1 : frogMeasure d {ω | (visits (paths ω)).Infinite} = 1 := by
    refine levy_one (frogMeasure d) (nearFiltration d) _ ?_ _ hX fun n A hA => near_bound n A hA
    rw [iSup_nearFiltration]
    exact hRm
  exact (mem_ae_iff_prob_eq_one hRm).2 h1

/-- The frozen statement `RecurrentOfFrozenCount` (ZeroOne/Statement.lean) holds. -/
theorem FrogModel.ZeroOne.recurrentOfFrozenCount_holds (d : ℕ) [NeZero d] :
    RecurrentOfFrozenCount d :=
  fun hd hX => recurrent_of_frozenCount d hd hX
