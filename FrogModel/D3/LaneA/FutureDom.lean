module

public import FrogModel.D3.LaneA.Coins
public import FrogModel.Lemmas.Refresh

@[expose] public section

/-!
# Future domination, Lemma 10.4 of the paper (d = 3)

The proof of Lemma 10.4. The woken set `W_e` with `e` entrants reads only the paths of its own
frogs (`woken_of_agree`), so it is a stopping set of coordinates (`isStoppingSet_woken`), and the
first `e + 1` values of the planted curve are determined by it (`isDetermined_head`). Refresh the
paths of the frogs of `W_e` with an independent copy `π'` and renumber the entrants
`e, e + 1, ...` as `0, 1, ...` (`shiftIdx`). A frog woken by `J` entrants and not by `e` is woken
from the entrants `e, ..., J - 1` through frogs outside `W_e`, whose paths are unchanged, so
`G(J) ≤ G(e) + G'(J - e)` pathwise, `G'` the curve of the refreshed renumbered paths
(`plantedG_le_refresh`). By `Stage.lintegral_refresh` the refreshed paths have the law
`pathMeasure` and are independent of the event, which gives `future_dom` (`future_dom_proof`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface

/-- The woken set reads only the paths of its own frogs. -/
theorem woken_of_agree {m k : ℕ} {π π' : PFrog → ℕ → Step 3}
    (h : ∀ ψ, Woken m k π ψ → π ψ = π' ψ) {φ : PFrog} (hφ : Woken m k π φ) :
    Woken m k π' φ := by
  induction hφ with
  | ent i hi => exact Woken.ent i hi
  | wake ψ v n hψ hv hp ih =>
    refine Woken.wake ψ v n ih hv ?_
    unfold pos at hp ⊢
    rw [← h ψ hψ]
    exact hp

theorem woken_of_agree' {m k : ℕ} {π π' : PFrog → ℕ → Step 3}
    (h : ∀ ψ, Woken m k π ψ → π ψ = π' ψ) {φ : PFrog} (hφ : Woken m k π' φ) :
    Woken m k π φ := by
  induction hφ with
  | ent i hi => exact Woken.ent i hi
  | wake ψ v n _ hv hp ih =>
    refine Woken.wake ψ v n ih hv ?_
    unfold pos at hp ⊢
    rw [h ψ ih]
    exact hp

theorem plantedG_of_agree {m k : ℕ} {π π' : PFrog → ℕ → Step 3}
    (h : ∀ ψ, Woken m k π ψ → π ψ = π' ψ) : plantedG m k π = plantedG m k π' := by
  unfold plantedG
  congr 1
  ext φ
  constructor
  · rintro ⟨hw, n, hn⟩
    refine ⟨woken_of_agree h hw, n, ?_⟩
    unfold pos at hn ⊢
    rw [← h φ hw]
    exact hn
  · rintro ⟨hw, n, hn⟩
    have hw' := woken_of_agree' h hw
    refine ⟨hw', n, ?_⟩
    unfold pos at hn ⊢
    rw [h φ hw']
    exact hn

/-- The woken set with `e` entrants, as a set of coordinates. -/
def wokenSet (m e : ℕ) (π : PFrog → ℕ → Step 3) : Set PFrog := {φ | Woken m e π φ}

theorem isStoppingSet_woken (m e : ℕ) :
    Stage.IsStoppingSet (X := fun _ : PFrog => ℕ → Step 3) (wokenSet m e) := by
  intro π π' h
  ext φ
  exact ⟨woken_of_agree' h, woken_of_agree h⟩

/-- The first `e + 1` values of the planted curve. -/
noncomputable def headCurve (m e : ℕ) (π : PFrog → ℕ → Step 3) : Fin (e + 1) → ℕ∞ :=
  fun l => plantedG m l π

theorem isDetermined_head (m e : ℕ) (B : Set (Fin (e + 1) → ℕ∞)) :
    Stage.IsDetermined (X := fun _ : PFrog => ℕ → Step 3) (wokenSet m e)
      {π | headCurve m e π ∈ B} := by
  intro π π' h
  have heq : headCurve m e π = headCurve m e π' := funext fun l =>
    plantedG_of_agree fun ψ hψ => h ψ (woken_mono (Nat.lt_succ_iff.1 l.2) hψ)
  simp only [Set.mem_ofPred_eq, heq]

theorem measurable_headCurve (m e : ℕ) : Measurable (headCurve m e) :=
  measurable_pi_iff.2 fun l => measurable_plantedG m l

/-- Entrant `i` of the renumbered model is entrant `i + e`. -/
def shiftIdx (e : ℕ) : PFrog → PFrog
  | Sum.inl i => Sum.inl (i + e)
  | Sum.inr v => Sum.inr v

theorem shiftIdx_injective (e : ℕ) : Function.Injective (shiftIdx e) := by
  rintro (i | v) (i' | v') h
  · simp only [shiftIdx, Sum.inl.injEq] at h
    rw [Nat.add_right_cancel h]
  · simp [shiftIdx] at h
  · simp [shiftIdx] at h
  · simp only [shiftIdx, Sum.inr.injEq] at h
    rw [h]

/-- Entrant `i` back to entrant `i - e`. -/
def unshift (e : ℕ) : PFrog → PFrog
  | Sum.inl i => Sum.inl (i - e)
  | Sum.inr v => Sum.inr v

theorem frogStart_unshift (e : ℕ) (φ : PFrog) : frogStart (unshift e φ) = frogStart φ := by
  cases φ <;> rfl

theorem shiftIdx_unshift_of_not_woken {m e : ℕ} {π : PFrog → ℕ → Step 3} {φ : PFrog}
    (h : ¬ Woken m e π φ) : shiftIdx e (unshift e φ) = φ := by
  cases φ with
  | inl i =>
    have hei : e ≤ i := by
      by_contra hlt
      exact h (Woken.ent i (by omega))
    simp [shiftIdx, unshift, Nat.sub_add_cancel hei]
  | inr v => rfl

/-- The refreshed renumbered paths: the frogs of `W_e` follow `π'`, the others `π`, and entrant
`i` is the entrant `i + e`. -/
noncomputable def refreshShift (m e : ℕ) (π π' : PFrog → ℕ → Step 3) : PFrog → ℕ → Step 3 :=
  fun φ => Stage.refresh (wokenSet m e) π π' (shiftIdx e φ)

open Classical in
theorem refreshShift_unshift {m e : ℕ} {π π' : PFrog → ℕ → Step 3} {φ : PFrog}
    (h : ¬ Woken m e π φ) : refreshShift m e π π' (unshift e φ) = π φ := by
  show Stage.refresh (wokenSet m e) π π' (shiftIdx e (unshift e φ)) = π φ
  rw [shiftIdx_unshift_of_not_woken h]
  show (if φ ∈ wokenSet m e π then π' φ else π φ) = π φ
  exact ite_eq_right h

/-- `G(J) ≤ G(e) + G'(J - e)`, pathwise. -/
theorem plantedG_le_refresh (m e J : ℕ) (π π' : PFrog → ℕ → Step 3) :
    plantedG m J π ≤ plantedG m e π + plantedG m (J - e) (refreshShift m e π π') := by
  set ρ := refreshShift m e π π' with hρ
  have hclaim : ∀ φ, Woken m J π φ → ¬ Woken m e π φ → Woken m (J - e) ρ (unshift e φ) := by
    intro φ hφ
    induction hφ with
    | ent i hi =>
      intro hne
      have hei : e ≤ i := by
        by_contra hlt
        exact hne (Woken.ent i (by omega))
      exact Woken.ent (i - e) (by omega)
    | wake ψ v n _ hv hp ih =>
      intro hne
      have hψe : ¬ Woken m e π ψ := fun hw => hne (Woken.wake ψ v n hw hv hp)
      refine Woken.wake (unshift e ψ) v n (ih hψe) hv ?_
      unfold pos at hp ⊢
      rw [frogStart_unshift, hρ, refreshShift_unshift hψe]
      exact hp
  set SJ := {φ | Woken m J π φ ∧ ∃ n, pos π φ n = none} with hSJ
  set Se := {φ | Woken m e π φ ∧ ∃ n, pos π φ n = none} with hSe
  have hsub : SJ ⊆ Se ∪ (SJ \ Se) := fun φ h => by
    by_cases h' : φ ∈ Se
    · exact Or.inl h'
    · exact Or.inr ⟨h, h'⟩
  have hdiff : (SJ \ Se).encard ≤ plantedG m (J - e) ρ := by
    unfold plantedG
    refine Set.encard_le_encard_of_injOn (f := unshift e) ?_ ?_
    · rintro φ ⟨⟨hw, n, hn⟩, hnot⟩
      have hne : ¬ Woken m e π φ := fun hwe => hnot ⟨hwe, n, hn⟩
      refine ⟨hclaim φ hw hne, n, ?_⟩
      unfold pos at hn ⊢
      rw [frogStart_unshift, hρ, refreshShift_unshift hne]
      exact hn
    · rintro φ ⟨⟨_, n, hn⟩, hnot⟩ φ' ⟨⟨_, n', hn'⟩, hnot'⟩ heq
      have h1 := shiftIdx_unshift_of_not_woken (fun hwe => hnot ⟨hwe, n, hn⟩)
      have h2 := shiftIdx_unshift_of_not_woken (fun hwe => hnot' ⟨hwe, n', hn'⟩)
      rw [← h1, ← h2, heq]
  calc plantedG m J π = SJ.encard := rfl
    _ ≤ (Se ∪ (SJ \ Se)).encard := Set.encard_le_encard hsub
    _ ≤ Se.encard + (SJ \ Se).encard := Set.encard_union_le _ _
    _ ≤ plantedG m e π + plantedG m (J - e) ρ := add_le_add le_rfl hdiff

theorem measurable_toENNReal_plantedG (m k : ℕ) :
    Measurable fun π : PFrog → ℕ → Step 3 => (plantedG m k π : ℝ≥0∞) :=
  (Measurable.of_discrete (α := ℕ∞)).comp (measurable_plantedG m k)

/-- Lemma 10.4 on the frog paths. -/
theorem future_dom_paths (m e J : ℕ) (B : Set (Fin (e + 1) → ℕ∞)) :
    ∫⁻ π in {π | headCurve m e π ∈ B}, (plantedG m J π : ℝ≥0∞) ∂pathMeasure ≤
      ∫⁻ π in {π | headCurve m e π ∈ B}, (plantedG m e π : ℝ≥0∞) ∂pathMeasure +
        pathMeasure {π | headCurve m e π ∈ B} *
          ∫⁻ π, (plantedG m (J - e) π : ℝ≥0∞) ∂pathMeasure := by
  set A := {π : PFrog → ℕ → Step 3 | headCurve m e π ∈ B} with hA
  have hAm : MeasurableSet A := by
    show MeasurableSet (headCurve m e ⁻¹' B)
    exact measurable_headCurve m e (Set.to_countable B).measurableSet
  have hshift : Measurable fun ρ : PFrog → ℕ → Step 3 => fun φ => ρ (shiftIdx e φ) :=
    measurable_pi_iff.2 fun φ => measurable_pi_apply _
  set f : (PFrog → ℕ → Step 3) → ℝ≥0∞ :=
    fun ρ => (plantedG m (J - e) (fun φ => ρ (shiftIdx e φ)) : ℝ≥0∞) with hf_def
  have hf : Measurable f := (measurable_toENNReal_plantedG m (J - e)).comp hshift
  have hfint : ∫⁻ ρ, f ρ ∂pathMeasure = ∫⁻ π, (plantedG m (J - e) π : ℝ≥0∞) ∂pathMeasure := by
    have hmap : pathMeasure.map (fun ρ : PFrog → ℕ → Step 3 => fun φ => ρ (shiftIdx e φ)) =
        pathMeasure := infinitePi_map_comp _ (shiftIdx e) (shiftIdx_injective e)
    rw [← lintegral_map (measurable_toENNReal_plantedG m (J - e)) hshift, hmap]
  have hKm : ∀ φ, MeasurableSet {π : PFrog → ℕ → Step 3 | φ ∈ wokenSet m e π} := fun φ =>
    measurableSet_woken m e φ
  have key := Stage.lintegral_refresh (fun _ : PFrog => Measure.infinitePi fun _ : ℕ => stepLaw 3)
    (wokenSet m e) (isStoppingSet_woken m e) hKm A (isDetermined_head m e B) hAm f hf
  have hpt : ∀ π, (plantedG m J π : ℝ≥0∞) ≤
      (plantedG m e π : ℝ≥0∞) + ∫⁻ π', f (Stage.refresh (wokenSet m e) π π') ∂pathMeasure := by
    intro π
    calc (plantedG m J π : ℝ≥0∞) = ∫⁻ _ : PFrog → ℕ → Step 3, (plantedG m J π : ℝ≥0∞) ∂pathMeasure := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ π', ((plantedG m e π : ℝ≥0∞) + f (Stage.refresh (wokenSet m e) π π')) ∂pathMeasure :=
          lintegral_mono fun π' => by
            have h := plantedG_le_refresh m e J π π'
            exact (ENat.toENNReal_le.2 h).trans_eq (ENat.toENNReal_add _ _)
      _ = (plantedG m e π : ℝ≥0∞) + ∫⁻ π', f (Stage.refresh (wokenSet m e) π π') ∂pathMeasure := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  calc ∫⁻ π in A, (plantedG m J π : ℝ≥0∞) ∂pathMeasure
      ≤ ∫⁻ π in A, ((plantedG m e π : ℝ≥0∞) +
          ∫⁻ π', f (Stage.refresh (wokenSet m e) π π') ∂pathMeasure) ∂pathMeasure :=
        lintegral_mono fun π => hpt π
    _ = ∫⁻ π in A, (plantedG m e π : ℝ≥0∞) ∂pathMeasure +
          ∫⁻ π in A, ∫⁻ π', f (Stage.refresh (wokenSet m e) π π') ∂pathMeasure ∂pathMeasure :=
        lintegral_add_left (measurable_toENNReal_plantedG m e) _
    _ = ∫⁻ π in A, (plantedG m e π : ℝ≥0∞) ∂pathMeasure +
          pathMeasure A * ∫⁻ ρ, f ρ ∂pathMeasure := by
        have key' : ∫⁻ π in A, ∫⁻ π', f (Stage.refresh (wokenSet m e) π π') ∂pathMeasure ∂pathMeasure =
            pathMeasure A * ∫⁻ ρ, f ρ ∂pathMeasure := by
          rw [← lintegral_indicator hAm]
          exact key
        rw [key']
    _ = _ := by rw [hfint]

/-- **`future_dom`** (Lemma 10.4). -/
theorem future_dom_proof : future_dom := by
  intro m e J _ B
  have hm : Measurable (plantedCurve m) := measurable_pi_iff.2 fun k => measurable_plantedG m k
  have hr : Measurable fun G : ℕ → ℕ∞ => fun l : Fin (e + 1) => G l := by fun_prop
  have hAm : MeasurableSet {G : ℕ → ℕ∞ | (fun l : Fin (e + 1) => G l) ∈ B} := by
    show MeasurableSet ((fun G : ℕ → ℕ∞ => fun l : Fin (e + 1) => G l) ⁻¹' B)
    exact hr (Set.to_countable B).measurableSet
  have hev : ∀ k, Measurable fun G : ℕ → ℕ∞ => ((G k : ℕ∞) : ℝ≥0∞) := fun k =>
    (Measurable.of_discrete (α := ℕ∞)).comp (measurable_pi_apply k)
  unfold curveLaw
  rw [setLIntegral_map hAm (hev J) hm, setLIntegral_map hAm (hev e) hm,
    Measure.map_apply hm hAm, lintegral_map (hev (J - e)) hm]
  exact future_dom_paths m e J B

end FrogModel.D3.LaneA
