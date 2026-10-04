module

public import FrogModel.D3.LaneB.Lemma10
public import FrogModel.D3.LaneA.FutureDom
public import FrogModel.LemmaR.Planted.Paths

@[expose] public section

/-!
# Lemma 8.3 of the paper, the Lean planted count (d = 3)

The proof of Lemma 8.3 (the root step). The frog paths of the planted model with one entrant give a sample of
`T*` (`toSample`): the frog at the root `r` follows the entrant `inl 0`, the frog at `v ≠ r` the
frog `inr v`; it has the law `frogMeasure 3` (`map_toSample`). The paths are glued from pieces with
`j = 1`, `D = 1` (Trials.lean): the root frog's piece 0 gives its first step. If it goes up, the
root frog is counted (`root_reach_of_none`). If it goes into the child `c`, the sub-model at `[c]`
is the planted model at height `m` with the root frog as entrant; each of its counted frogs is
reached from the root through arcs of `starArcTrunc (m + 1)` (`reach_lift`), and it reaches `y`
if its next piece does (`reach_none`). Hence `plantedCount_ge`, pathwise. The first step, the
sub-model and the next pieces read disjoint coordinates, so taking expectations gives
`E Z_(m+1) ≥ 1/4 + 3 · (1/4) (1/3) E G_m(1)` (`lemma19_proof`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface FrogModel.ZeroOne

/-! ### The sample of `T*` read from frog paths -/

/-- The frog of `T*` at `v`: the frog at the root is the entrant `inl 0`. -/
def vtx : Vertex 3 → PFrog
  | [] => Sum.inl 0
  | a :: l => Sum.inr (a :: l)

theorem vtx_injective : Function.Injective vtx := by
  rintro (_ | ⟨a, l⟩) (_ | ⟨b, l'⟩) h <;> simp_all [vtx]

theorem vtx_of_ne_nil {v : Vertex 3} (hv : v ≠ []) : vtx v = Sum.inr v := by
  cases v with
  | nil => exact absurd rfl hv
  | cons a l => rfl

/-- The sample of `T*` read from frog paths. -/
def toSample (π : PFrog → ℕ → Step 3) : Sample 3 := fun v => π (vtx v)

theorem measurable_toSample : Measurable toSample := by
  unfold toSample
  exact measurable_pi_iff.2 fun v => measurable_pi_apply (vtx v)

theorem map_toSample : pathMeasure.map toSample = frogMeasure 3 :=
  infinitePi_map_comp (Measure.infinitePi fun _ : ℕ => stepLaw 3) vtx vtx_injective

theorem initF_one_zero : initF 1 0 = Sum.inl 0 := by simp [initF]

theorem vtx_frogStart_liftF (c : Fin 3) (ψ : PFrog) :
    vtx (frogStart (liftF (initF 1 0) [c] ψ)) = liftF (initF 1 0) [c] ψ := by
  cases ψ with
  | inl i =>
    simp only [liftF, initF_one_zero]
    rfl
  | inr u => exact vtx_of_ne_nil (v := u ++ [c]) (by simp)

theorem walkStar_toSample (π : PFrog → ℕ → Step 3) (φ : PFrog) (h : vtx (frogStart φ) = φ)
    (n : ℕ) : walkStar (some (frogStart φ)) (toSample π (frogStart φ)) n = pos π φ n := by
  unfold toSample pos
  rw [h]

theorem encard_eq_tsum_indicator {α : Type*} (s : Set α) :
    (s.encard : ℝ≥0∞) = ∑' a, s.indicator 1 a := by
  rw [← ENNReal.tsum_set_one]
  exact tsum_subtype s 1

/-- `Z_M` counts the vertices reached from the root whose frog reaches `y`. -/
theorem plantedCount_eq_encard (M : ℕ) (ζ : Sample 3) :
    LemmaR.plantedCount M ζ = (({v | Relation.ReflTransGen (LemmaR.starArcTrunc M ζ) [] v ∧
      ∃ n, walkStar (some v) (ζ v) n = none} : Set (Vertex 3)).encard : ℝ≥0∞) := by
  rw [encard_eq_tsum_indicator]
  unfold LemmaR.plantedCount
  congr 1
  ext v
  simp [Set.indicator]

/-! ### The root's first step -/

theorem walkStar_one_of_dir (x : ℕ → Step 3) (c : Fin 3) (hx : (x 0).2 = c.succ) :
    walkStar (some []) x 1 = some [c] := by
  simp [walkStar, stepStar, hx, Fin.succ_ne_zero]

theorem firstD_of_dir (x : ℕ → Step 3) (c : Fin 3) (hx : (x 0).2 = c.succ) :
    firstD 1 x = some [c] := by
  have h1 := walkStar_one_of_dir x c hx
  refine (firstD_eq_some_iff 1 x [c]).2 ⟨1, ?_, h1⟩
  refine (hitD_eq_iff 1 x 1).2 ⟨⟨[c], h1, rfl⟩, fun i hi => ?_⟩
  rintro ⟨v, hv, hlen⟩
  obtain rfl : i = 0 := by omega
  simp only [walkStar, Option.some.injEq] at hv
  subst hv
  simp at hlen

theorem walkStar_one_of_up (x : ℕ → Step 3) (hx : (x 0).2 = 0) : walkStar (some []) x 1 = none := by
  simp [walkStar, stepStar, hx]

theorem firstD_of_up (x : ℕ → Step 3) (hx : (x 0).2 = 0) : firstD 1 x = none := by
  refine (firstD_eq_none_iff 1 x).2 ?_
  rintro ⟨n, v, hv, hlen⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [walkStar, Option.some.injEq] at hv
    subst hv
    simp at hlen
  · rw [walkStar_none_of_le (some []) x (walkStar_one_of_up x hx) hn] at hv
    cases hv

theorem reach_none_of_not_reachD (x : ℕ → Step 3) (h : ¬ ReachD 1 x) :
    ∃ n, walkStar (some []) x n = none := by
  refine ⟨1, ?_⟩
  rcases hw : walkStar (some []) x 1 with _ | v
  · rfl
  · exfalso
    have hl := length_walkStar [] x 1 v hw
    have h1 : dW x 1 = inc (x 0) := by simp [dW]
    simp only [List.length_nil, Nat.cast_zero, zero_add] at hl
    have hlen : v.length = 1 := by
      rcases inc_cases (x 0) with ⟨_, hi⟩ | ⟨_, hi⟩ <;> omega
    exact h ⟨1, v, hw, hlen⟩

theorem card_dir (b : Fin 4) : (Finset.univ.filter fun ξ : Step 3 => ξ.2 = b).card = 3 := by
  revert b
  decide

/-- `P(the first step goes in direction b) = 1/4`. -/
theorem seqLaw_dir (b : Fin 4) : LemmaR.seqLaw 3 {x | (x 0).2 = b} = 4⁻¹ := by
  have hm : MeasurableSet {ξ : Step 3 | ξ.2 = b} := MeasurableSet.of_discrete
  have hpre : {x : ℕ → Step 3 | (x 0).2 = b} = (fun x : ℕ → Step 3 => x 0) ⁻¹' {ξ | ξ.2 = b} :=
    rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) hm, LemmaR.seqLaw,
    Measure.infinitePi_map_eval]
  have hs : {ξ : Step 3 | ξ.2 = b} = ↑(Finset.univ.filter fun ξ : Step 3 => ξ.2 = b) := by
    ext ξ
    simp
  rw [hs, ← sum_measure_singleton]
  simp only [LemmaR.stepLaw_singleton, Finset.sum_const, nsmul_eq_mul]
  rw [card_dir b]
  have h12 : (((3 * (3 + 1) : ℕ)) : ℝ≥0∞) = 3 * 4 := by norm_num
  rw [h12, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
    Nat.cast_ofNat, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-! ### The sub-model below a child of the root -/

section L19

variable {m : ℕ} {ω : PSpace} {c : Fin 3}

theorem pos_lift (hv : firstD 1 (ω (initF 1 0, 0)) = some [c]) (ψ : PFrog)
    (hψ : Woken m 1 (subPaths ω (initF 1 0) [c]) ψ) (u : Vertex 3) (n : ℕ)
    (hpos : pos (subPaths ω (initF 1 0) [c]) ψ n = some u) :
    ∃ N, pos (glueP 1 1 ω) (liftF (initF 1 0) [c] ψ) N = some (u ++ [c]) := by
  obtain ⟨k, hk, hkv, -⟩ := firstD_spec 1 _ [c] hv
  have hvne : ([c] : Vertex 3) ≠ [] := List.cons_ne_nil _ _
  rcases ψ with i' | u''
  · obtain rfl := woken_one_inl hψ
    refine ⟨k + n, ?_⟩
    simp only [liftF]
    rw [pos_init_add 1 1 0 ω [c] k hk hkv n]
    exact walkStar_glue_copy hvne [] u _ _ n hpos
  · refine ⟨n, ?_⟩
    simp only [liftF]
    unfold pos
    rw [glueP_deep 1 1 le_rfl u'' [c] rfl ω]
    exact walkStar_glue_copy hvne u'' u _ _ n hpos

/-- **The sub-model's woken frogs are reached from the root in `Z_(m+1)`.** -/
theorem reach_lift (hv : firstD 1 (ω (initF 1 0, 0)) = some [c]) (ψ : PFrog)
    (hψ : Woken m 1 (subPaths ω (initF 1 0) [c]) ψ) :
    Relation.ReflTransGen (LemmaR.starArcTrunc (m + 1) (toSample (glueP 1 1 ω))) []
      (frogStart (liftF (initF 1 0) [c] ψ)) := by
  induction hψ with
  | ent i' _ =>
    simp only [liftF, frogStart_initF]
    exact Relation.ReflTransGen.refl
  | wake ψ' u n hψ' hu hpos ih =>
    obtain ⟨N, hN⟩ := pos_lift hv ψ' hψ' u n hpos
    refine Relation.ReflTransGen.tail ih ?_
    unfold LemmaR.starArcTrunc starArc
    refine ⟨⟨?_, N, ?_⟩, ?_⟩
    · show u ++ [c] ≠ []
      simp
    · rw [walkStar_toSample _ _ (vtx_frogStart_liftF c ψ') N]
      exact hN
    · show (u ++ [c]).length ≤ m + 1
      simp only [List.length_append, List.length_singleton]
      omega

/-- **A counted sub-model frog whose next piece reaches `y` from the root reaches `y`.** -/
theorem reach_none (hv : firstD 1 (ω (initF 1 0, 0)) = some [c]) (ψ : PFrog)
    (hψ : Woken m 1 (subPaths ω (initF 1 0) [c]) ψ)
    (hreach : ∃ n, pos (subPaths ω (initF 1 0) [c]) ψ n = none)
    (hH : HitsDown 1 (ω (contIdx (initF 1 0) [c] ψ))) :
    ∃ t, pos (glueP 1 1 ω) (liftF (initF 1 0) [c] ψ) t = none := by
  obtain ⟨k, hk, hkv, -⟩ := firstD_spec 1 _ [c] hv
  have hvne : ([c] : Vertex 3) ≠ [] := List.cons_ne_nil _ _
  rcases ψ with i' | u
  · obtain rfl := woken_one_inl hψ
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1
      ((exitTime_ne_top_iff [] (ω (initF 1 0, 1))).2 hreach)
    obtain ⟨s, hs⟩ := (exists_walkStar_none_iff [] (ω (initF 1 0, 2))).2 hH
    refine ⟨k + (r + s), ?_⟩
    simp only [liftF]
    rw [pos_init_add 1 1 0 ω [c] k hk hkv]
    exact (walkStar_glue_exit hvne [] _ _ r hr.symm s).trans hs
  · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1
      ((exitTime_ne_top_iff u (ω (Sum.inr (u ++ [c]), 0))).2 hreach)
    obtain ⟨s, hs⟩ := (exists_walkStar_none_iff [] (ω (Sum.inr (u ++ [c]), 1))).2 hH
    refine ⟨r + s, ?_⟩
    simp only [liftF]
    unfold pos
    rw [glueP_deep 1 1 le_rfl u [c] rfl ω]
    exact (walkStar_glue_exit hvne u _ _ r hr.symm s).trans hs

theorem root_reach_of_none (hv : firstD 1 (ω (initF 1 0, 0)) = none) :
    ∃ n, walkStar (some []) (toSample (glueP 1 1 ω) []) n = none := by
  have hr := (firstD_eq_none_iff 1 _).1 hv
  have htop : hitD 1 (ω (initF 1 0, 0)) = ⊤ := by simp [hitD, hr]
  have hroot : toSample (glueP 1 1 ω) [] = ω (initF 1 0, 0) := by
    show glueP 1 1 ω (vtx []) = _
    rw [show vtx [] = initF 1 0 from initF_one_zero.symm, glueP_init, htop, glueAt_top]
  rw [hroot]
  exact reach_none_of_not_reachD _ hr

end L19

/-! ### The events and the pathwise bound -/

/-- The root frog's first step goes up. -/
def evNone : Set PSpace := {ω | firstD 1 (ω (initF 1 0, 0)) = none}

/-- The root frog's first step goes into the child `c`. -/
def evA (c : Fin 3) : Set PSpace := {ω | firstD 1 (ω (initF 1 0, 0)) = some [c]}

/-- `ψ` is counted by the sub-model below `[c]`. -/
def evB (m : ℕ) (c : Fin 3) (ψ : PFrog) : Set PSpace :=
  {ω | ψ ∈ subCounted ω (initF 1 0) [c] m}

/-- The next piece of `ψ` reaches `y` from the root. -/
def evC (c : Fin 3) (ψ : PFrog) : Set PSpace :=
  {ω | HitsDown 1 (ω (contIdx (initF 1 0) [c] ψ))}

theorem measurableSet_evNone : MeasurableSet evNone := by
  have h : Measurable fun ω : PSpace => firstD 1 (ω (initF 1 0, 0)) :=
    (measurable_firstD 1).comp (measurable_pi_apply _)
  exact h (measurableSet_singleton none)

theorem measurableSet_evA (c : Fin 3) : MeasurableSet (evA c) := by
  have h : Measurable fun ω : PSpace => firstD 1 (ω (initF 1 0, 0)) :=
    (measurable_firstD 1).comp (measurable_pi_apply _)
  exact h (measurableSet_singleton (some [c]))

theorem measurableSet_evB (m : ℕ) (c : Fin 3) (ψ : PFrog) : MeasurableSet (evB m c ψ) :=
  measurableSet_mem_subCounted (initF 1 0) [c] m ψ

theorem measurableSet_evC (c : Fin 3) (ψ : PFrog) : MeasurableSet (evC c ψ) := by
  show MeasurableSet ((fun ω : PSpace => ω (contIdx (initF 1 0) [c] ψ)) ⁻¹' {x | HitsDown 1 x})
  exact measurable_pi_apply (contIdx (initF 1 0) [c] ψ) (measurableSet_hitsDown 1)

/-- **The pathwise bound.** -/
theorem plantedCount_ge (m : ℕ) (ω : PSpace) :
    evNone.indicator 1 ω + ∑ c : Fin 3, ∑' ψ, (evA c ∩ (evB m c ψ ∩ evC c ψ)).indicator 1 ω ≤
      LemmaR.plantedCount (m + 1) (toSample (glueP 1 1 ω)) := by
  rcases hf : firstD 1 (ω (initF 1 0, 0)) with _ | v
  · have hA : ∀ c : Fin 3, ω ∉ evA c := fun c h => by
      simp only [evA, Set.mem_ofPred_eq, hf] at h
      cases h
    have hN : ω ∈ evNone := hf
    have hz : ∀ (c : Fin 3) (ψ : PFrog),
        (evA c ∩ (evB m c ψ ∩ evC c ψ)).indicator (1 : PSpace → ℝ≥0∞) ω = 0 := fun c ψ =>
      Set.indicator_of_notMem (fun h => hA c h.1) _
    simp only [Set.indicator_of_mem hN, Pi.one_apply, hz, tsum_zero, Finset.sum_const_zero,
      add_zero]
    unfold LemmaR.plantedCount
    refine le_trans ?_ (ENNReal.le_tsum ([] : Vertex 3))
    rw [ite_eq_left ⟨Relation.ReflTransGen.refl, root_reach_of_none hf⟩]
  · obtain ⟨k, -, -, hvlen⟩ := firstD_spec 1 _ v hf
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 hvlen
    have hN : ω ∉ evNone := fun h => by
      simp only [evNone, Set.mem_ofPred_eq, hf] at h
      cases h
    rw [Set.indicator_of_notMem hN, zero_add]
    rw [Finset.sum_eq_single c (fun c' _ hc' => ?_) (by simp)]
    · have hAc : ω ∈ evA c := hf
      set S : Set PFrog := {ψ | ψ ∈ subCounted ω (initF 1 0) [c] m ∧
        HitsDown 1 (ω (contIdx (initF 1 0) [c] ψ))} with hS
      have hterm : ∀ ψ, (evA c ∩ (evB m c ψ ∩ evC c ψ)).indicator (1 : PSpace → ℝ≥0∞) ω =
          S.indicator 1 ψ := by
        intro ψ
        by_cases hψ : ψ ∈ S
        · rw [Set.indicator_of_mem hψ, Set.indicator_of_mem
            (show ω ∈ evA c ∩ (evB m c ψ ∩ evC c ψ) from ⟨hAc, hψ.1, hψ.2⟩)]
          rfl
        · rw [Set.indicator_of_notMem hψ, Set.indicator_of_notMem fun h => hψ ⟨h.2.1, h.2.2⟩]
      rw [tsum_congr hterm, ← tsum_subtype S (1 : PFrog → ℝ≥0∞)]
      simp only [Pi.one_apply]
      rw [ENNReal.tsum_set_one, plantedCount_eq_encard]
      refine ENat.toENNReal_le.2 (Set.encard_le_encard_of_injOn
        (f := fun ψ => frogStart (liftF (initF 1 0) [c] ψ)) ?_ ?_)
      · intro ψ hψ
        obtain ⟨t, ht⟩ := reach_none hf ψ hψ.1.1 hψ.1.2 hψ.2
        exact ⟨reach_lift hf ψ hψ.1.1,
          t, (walkStar_toSample _ _ (vtx_frogStart_liftF c ψ) t).trans ht⟩
      · intro a ha b hb hab
        simp only at hab
        rcases a with a | a <;> rcases b with b | b
        · rw [woken_one_inl ha.1.1, woken_one_inl hb.1.1]
        · exfalso
          have h1 : frogStart (liftF (initF 1 0) [c] (Sum.inl a)) = [] := frogStart_initF 1 0
          have h2 : frogStart (liftF (initF 1 0) [c] (Sum.inr b)) = b ++ [c] := rfl
          have h3 : b ++ [c] = [] := h2.symm.trans (hab.symm.trans h1)
          simp at h3
        · exfalso
          have h1 : frogStart (liftF (initF 1 0) [c] (Sum.inl b)) = [] := frogStart_initF 1 0
          have h2 : frogStart (liftF (initF 1 0) [c] (Sum.inr a)) = a ++ [c] := rfl
          have h3 : a ++ [c] = [] := h2.symm.trans (hab.trans h1)
          simp at h3
        · have h3 : a ++ [c] = b ++ [c] := hab
          rw [List.append_cancel_right h3]
    · have hA : ω ∉ evA c' := fun h => by
        simp only [evA, Set.mem_ofPred_eq, hf, Option.some.injEq, List.cons.injEq, and_true] at h
        exact hc' h.symm
      have hz : ∀ ψ : PFrog,
          (evA c' ∩ (evB m c' ψ ∩ evC c' ψ)).indicator (1 : PSpace → ℝ≥0∞) ω = 0 := fun ψ =>
        Set.indicator_of_notMem (fun h => hA h.1) _
      simp only [hz, tsum_zero]

/-! ### Expectations -/

/-- The expected size of a random subset of a countable type. -/
theorem lintegral_encard {Ω α : Type*} [MeasurableSpace Ω] [Countable α] (μ : Measure Ω)
    (S : Ω → Set α) (hS : ∀ a, MeasurableSet {ω | a ∈ S ω}) :
    ∫⁻ ω, ((S ω).encard : ℝ≥0∞) ∂μ = ∑' a, μ {ω | a ∈ S ω} := by
  have h1 : ∀ ω, ((S ω).encard : ℝ≥0∞) = ∑' a, {ω | a ∈ S ω}.indicator 1 ω := by
    intro ω
    rw [encard_eq_tsum_indicator]
    congr 1
  simp_rw [h1]
  rw [lintegral_tsum fun a =>
    ((show Measurable (1 : Ω → ℝ≥0∞) from measurable_one).indicator (hS a)).aemeasurable]
  congr 1
  ext a
  exact lintegral_indicator_one (hS a)

theorem sum_pr_evB (m : ℕ) (c : Fin 3) :
    ∑' ψ, pieceMeasure (evB m c ψ) = ∫⁻ π, (plantedG m 1 π : ℝ≥0∞) ∂pathMeasure := by
  unfold evB
  rw [← lintegral_encard pieceMeasure (fun ω => subCounted ω (initF 1 0) [c] m)
    (fun ψ => measurableSet_mem_subCounted (initF 1 0) [c] m ψ), ← map_subPaths (initF 1 0) [c],
    lintegral_map (measurable_toENNReal_plantedG m 1) (measurable_subPaths _ _)]
  rfl

theorem pr_evC (c : Fin 3) (ψ : PFrog) : pieceMeasure (evC c ψ) = 3⁻¹ := by
  have h := pieceMeasure_eval (contIdx (initF 1 0) [c] ψ) {x | HitsDown 1 x}
    (measurableSet_hitsDown 1)
  rw [seqLaw_hitsDown 1, pow_one] at h
  exact h

theorem pr_evA_ge (c : Fin 3) : 4⁻¹ ≤ pieceMeasure (evA c) := by
  have hm : MeasurableSet {ξ : Step 3 | ξ.2 = c.succ} := MeasurableSet.of_discrete
  have hm' : MeasurableSet {x : ℕ → Step 3 | (x 0).2 = c.succ} := by
    show MeasurableSet ((fun x : ℕ → Step 3 => x 0) ⁻¹' {ξ | ξ.2 = c.succ})
    exact measurable_pi_apply 0 hm
  rw [← seqLaw_dir c.succ, ← pieceMeasure_eval (initF 1 0, 0) _ hm']
  exact measure_mono fun ω hω => firstD_of_dir _ c hω

theorem pr_evNone_ge : 4⁻¹ ≤ pieceMeasure evNone := by
  have hm : MeasurableSet {ξ : Step 3 | ξ.2 = 0} := MeasurableSet.of_discrete
  have hm' : MeasurableSet {x : ℕ → Step 3 | (x 0).2 = 0} := by
    show MeasurableSet ((fun x : ℕ → Step 3 => x 0) ⁻¹' {ξ | ξ.2 = 0})
    exact measurable_pi_apply 0 hm
  rw [← seqLaw_dir 0, ← pieceMeasure_eval (initF 1 0, 0) _ hm']
  exact measure_mono fun ω hω => firstD_of_up _ hω

/-- The first step, the sub-model and the next piece read disjoint coordinates. -/
theorem pr_evABC (m : ℕ) (c : Fin 3) (ψ : PFrog) :
    pieceMeasure (evA c ∩ (evB m c ψ ∩ evC c ψ)) =
      pieceMeasure (evA c) * (pieceMeasure (evB m c ψ) * pieceMeasure (evC c ψ)) := by
  have hsub0 : ∀ ψ', subIdx (initF 1 0) [c] ψ' ≠ (initF 1 0, 0) := fun ψ' =>
    sub_ne_init0 (j := 1) (D := 1) le_rfl rfl 0 0 ψ'
  have hcont0 : contIdx (initF 1 0) [c] ψ ≠ (initF 1 0, 0) := fun h =>
    init0_ne_cont (j := 1) 0 0 [c] ψ h.symm
  have hsubc : ∀ ψ', subIdx (initF 1 0) [c] ψ' ≠ contIdx (initF 1 0) [c] ψ := fun ψ' =>
    sub_ne_cont (j := 1) (D := 1) le_rfl rfl 0 0 [c] ψ ψ'
  have hB : ∀ ω ω' : PSpace, (∀ ψ', ω (subIdx (initF 1 0) [c] ψ') = ω' (subIdx (initF 1 0) [c] ψ'))
      → ω ∈ evB m c ψ → ω' ∈ evB m c ψ := by
    intro ω ω' h hω
    have hs : subPaths ω' (initF 1 0) [c] = subPaths ω (initF 1 0) [c] :=
      funext fun ψ' => (h ψ').symm
    show ψ ∈ subCounted ω' (initF 1 0) [c] m
    unfold subCounted
    rw [hs]
    exact hω
  have h1 := infinitePi_inter_of_dependsOn (LemmaR.seqLaw 3) ({(initF 1 0, 0)} : Set (PFrog × ℕ))
    (evB m c ψ ∩ evC c ψ) (evA c) ((measurableSet_evB m c ψ).inter (measurableSet_evC c ψ))
    (measurableSet_evA c)
    (fun ω ω' h hω => ⟨hB ω ω' (fun ψ' => h _ (hsub0 ψ')) hω.1, by
      show HitsDown 1 (ω' _)
      rw [← h _ hcont0]
      exact hω.2⟩)
    (fun ω ω' h hω => by
      show firstD 1 (ω' (initF 1 0, 0)) = some [c]
      rw [← h _ rfl]
      exact hω)
  have h2 := infinitePi_inter_of_dependsOn (LemmaR.seqLaw 3)
    ({contIdx (initF 1 0) [c] ψ} : Set (PFrog × ℕ)) (evB m c ψ) (evC c ψ)
    (measurableSet_evB m c ψ) (measurableSet_evC c ψ)
    (fun ω ω' h hω => hB ω ω' (fun ψ' => h _ (hsubc ψ')) hω)
    (fun ω ω' h hω => by
      show HitsDown 1 (ω' _)
      rw [← h _ rfl]
      exact hω)
  calc pieceMeasure (evA c ∩ (evB m c ψ ∩ evC c ψ))
      = pieceMeasure ((evB m c ψ ∩ evC c ψ) ∩ evA c) := by rw [Set.inter_comm]
    _ = pieceMeasure (evB m c ψ ∩ evC c ψ) * pieceMeasure (evA c) := h1
    _ = pieceMeasure (evA c) * (pieceMeasure (evB m c ψ) * pieceMeasure (evC c ψ)) := by
      rw [mul_comm]
      exact congrArg _ h2

theorem measurable_evTerm (m : ℕ) (c : Fin 3) :
    Measurable fun ω : PSpace => ∑' ψ, (evA c ∩ (evB m c ψ ∩ evC c ψ)).indicator (1 : PSpace → ℝ≥0∞) ω :=
  Measurable.tsum fun ψ =>
    (show Measurable (1 : PSpace → ℝ≥0∞) from measurable_one).indicator
    ((measurableSet_evA c).inter ((measurableSet_evB m c ψ).inter (measurableSet_evC c ψ)))

theorem lintegral_evTerm (m : ℕ) (c : Fin 3) :
    ∫⁻ ω, ∑' ψ, (evA c ∩ (evB m c ψ ∩ evC c ψ)).indicator 1 ω ∂pieceMeasure =
      pieceMeasure (evA c) * ((∫⁻ π, (plantedG m 1 π : ℝ≥0∞) ∂pathMeasure) * 3⁻¹) := by
  rw [lintegral_tsum fun ψ => ((show Measurable (1 : PSpace → ℝ≥0∞) from measurable_one).indicator ((measurableSet_evA c).inter
    ((measurableSet_evB m c ψ).inter (measurableSet_evC c ψ)))).aemeasurable]
  have hψ : ∀ ψ, ∫⁻ ω, (evA c ∩ (evB m c ψ ∩ evC c ψ)).indicator 1 ω ∂pieceMeasure =
      pieceMeasure (evA c) * (pieceMeasure (evB m c ψ) * 3⁻¹) := fun ψ => by
    rw [lintegral_indicator_one ((measurableSet_evA c).inter
      ((measurableSet_evB m c ψ).inter (measurableSet_evC c ψ))), pr_evABC, pr_evC]
  rw [tsum_congr hψ, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, sum_pr_evB]

/-- **`lemma19`** (Lemma 8.3). -/
theorem lemma19_proof : lemma19 := by
  intro m
  set EG := ∫⁻ π, (plantedG m 1 π : ℝ≥0∞) ∂pathMeasure with hEG
  have hmeas : Measurable fun ω : PSpace => LemmaR.plantedCount (m + 1) (toSample (glueP 1 1 ω)) :=
    (LemmaR.measurable_plantedCount (m + 1)).comp (measurable_toSample.comp (measurable_glueP 1 1))
  have htrans : ∫⁻ ζ, LemmaR.plantedCount (m + 1) ζ ∂frogMeasure 3 =
      ∫⁻ ω, LemmaR.plantedCount (m + 1) (toSample (glueP 1 1 ω)) ∂pieceMeasure := by
    rw [← map_toSample, ← map_glueP 1 1,
      Measure.map_map measurable_toSample (measurable_glueP 1 1),
      lintegral_map (LemmaR.measurable_plantedCount (m + 1))
        (measurable_toSample.comp (measurable_glueP 1 1))]
    rfl
  have hlow : ∫⁻ ω, (evNone.indicator 1 ω +
      ∑ c : Fin 3, ∑' ψ, (evA c ∩ (evB m c ψ ∩ evC c ψ)).indicator 1 ω) ∂pieceMeasure =
      pieceMeasure evNone + ∑ c : Fin 3, pieceMeasure (evA c) * (EG * 3⁻¹) := by
    rw [lintegral_add_left ((show Measurable (1 : PSpace → ℝ≥0∞) from measurable_one).indicator measurableSet_evNone),
      lintegral_indicator_one measurableSet_evNone,
      lintegral_finsetSum _ fun c _ => measurable_evTerm m c]
    simp_rw [lintegral_evTerm]
    rfl
  have h3 : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hsum : ∑ _c : Fin 3, 4⁻¹ * (EG * 3⁻¹) = 4⁻¹ * EG := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    calc (3 : ℝ≥0∞) * (4⁻¹ * (EG * 3⁻¹)) = 4⁻¹ * EG * (3 * 3⁻¹) := by ring
      _ = 4⁻¹ * EG := by rw [h3, mul_one]
  rw [htrans]
  calc (1 + EG) / 4 = 4⁻¹ + ∑ _c : Fin 3, 4⁻¹ * (EG * 3⁻¹) := by
        rw [hsum, div_eq_mul_inv, add_mul, one_mul, mul_comm EG]
    _ ≤ pieceMeasure evNone + ∑ c : Fin 3, pieceMeasure (evA c) * (EG * 3⁻¹) :=
        add_le_add pr_evNone_ge (Finset.sum_le_sum fun c _ => by gcongr; exact pr_evA_ge c)
    _ = ∫⁻ ω, (evNone.indicator 1 ω +
          ∑ c : Fin 3, ∑' ψ, (evA c ∩ (evB m c ψ ∩ evC c ψ)).indicator 1 ω) ∂pieceMeasure :=
        hlow.symm
    _ ≤ ∫⁻ ω, LemmaR.plantedCount (m + 1) (toSample (glueP 1 1 ω)) ∂pieceMeasure :=
        lintegral_mono fun ω => plantedCount_ge m ω

end FrogModel.D3.LaneA
