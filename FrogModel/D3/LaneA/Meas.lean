module

public import FrogModel.D3.LaneA.Depth
public import FrogModel.D3.LaneB.Succ

@[expose] public section

/-!
# Measurability of the planted model (d = 3)

The woken set is the union of its finite-round stages (`wokenStage`), each a countable combination
of the events "frog `ψ` is at `v` at time `n`", so every membership event `{π | Woken m k π ψ}` is
measurable (`measurableSet_woken`). The cardinality of a random subset of a countable type with
measurable membership events is measurable (`measurable_encard`); hence `plantedG` and `presN` are
measurable, which is `measurable_plantedPair` (`measurable_plantedPair_proof`). The closure's
curves are measurable as well (`measurable_closPair_proof`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface

/-- The frogs woken within `t` rounds: the entrants, then the frogs of the vertices of depth at
most `m` visited by the path of a frog woken within `t - 1` rounds. -/
def wokenStage (m k : ℕ) (π : PFrog → ℕ → Step 3) : ℕ → Set PFrog
  | 0 => {φ | ∃ i < k, φ = Sum.inl i}
  | t + 1 => wokenStage m k π t ∪
      {φ | ∃ v, φ = Sum.inr v ∧ v.length ≤ m ∧ ∃ ψ ∈ wokenStage m k π t, ∃ n, pos π ψ n = some v}

theorem measurable_pos (φ : PFrog) (n : ℕ) :
    Measurable fun π : PFrog → ℕ → Step 3 => pos π φ n :=
  (measurable_walkStar_at 3 (frogStart φ) n).comp (measurable_pi_apply φ)

theorem measurableSet_pos_eq_some (φ : PFrog) (n : ℕ) (v : Vertex 3) :
    MeasurableSet {π : PFrog → ℕ → Step 3 | pos π φ n = some v} := by
  have h_pos_meas : Measurable (fun (π : PFrog → ℕ → Step 3) => pos π φ n) :=
    measurable_pos φ n
  have h_singleton : MeasurableSet ({some v} : Set (Option (Vertex 3))) :=
    MeasurableSet.of_discrete
  exact h_singleton.preimage h_pos_meas

theorem woken_iff_wokenStage (m k : ℕ) (π : PFrog → ℕ → Step 3) (ψ : PFrog) :
    Woken m k π ψ ↔ ∃ t, ψ ∈ wokenStage m k π t := by
  constructor
  · intro h
    induction' h with i hi φ v n hφ hv hpos ih
    · -- Woken.ent i hi
      refine ⟨0, ?_⟩
      have h_def : wokenStage m k π 0 = {φ | ∃ i < k, φ = Sum.inl i} := rfl
      rw [h_def]
      exact ⟨i, hi, rfl⟩
    · -- Woken.wake φ v n hφ hv hpos
      rcases ih with ⟨t, ht⟩
      refine ⟨t+1, ?_⟩
      have h_def : wokenStage m k π (t+1) = wokenStage m k π t ∪ {φ | ∃ v, φ = Sum.inr v ∧ v.length ≤ m ∧ ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v} := rfl
      rw [h_def]
      right
      refine ⟨v, rfl, hv, φ, ht, n, hpos⟩
  · intro h
    rcases h with ⟨t, ht⟩
    induction' t with t ih generalizing ψ
    · -- t = 0
      have h_def : wokenStage m k π 0 = {φ | ∃ i < k, φ = Sum.inl i} := rfl
      rw [h_def] at ht
      rcases ht with ⟨i, hi, hψ⟩
      subst hψ
      exact Woken.ent i hi
    · -- t+1
      have h_def : wokenStage m k π (t+1) = wokenStage m k π t ∪ {φ | ∃ v, φ = Sum.inr v ∧ v.length ≤ m ∧ ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v} := rfl
      rw [h_def] at ht
      rcases ht with (ht | ht)
      · exact ih ψ ht
      · simp only [Set.mem_ofPred_eq] at ht
        rcases ht with ⟨v, hψ, hv, ψ', ht', n, hpos⟩
        subst hψ
        have h_woken : Woken m k π ψ' := ih ψ' ht'
        exact Woken.wake ψ' v n h_woken hv hpos

theorem measurableSet_wokenStage (m k t : ℕ) (ψ : PFrog) :
    MeasurableSet {π : PFrog → ℕ → Step 3 | ψ ∈ wokenStage m k π t} := by
  induction' t with t ih generalizing ψ
  · -- base case t = 0
    by_cases h : ∃ i < k, ψ = Sum.inl i
    · rcases h with ⟨i, hi, hψ⟩
      subst hψ
      have h_eq : {π : PFrog → ℕ → Step 3 | (Sum.inl i) ∈ wokenStage m k π 0} = Set.univ := by
        ext x; simp [wokenStage, hi]
      rw [h_eq]
      exact MeasurableSet.univ
    · have h_eq : {π : PFrog → ℕ → Step 3 | ψ ∈ wokenStage m k π 0} = ∅ := by
        ext x; simp [wokenStage, h]
      rw [h_eq]
      exact MeasurableSet.empty
  · -- inductive step
    have h_goal : {π : PFrog → ℕ → Step 3 | ψ ∈ wokenStage m k π (t+1)} =
        {π | ψ ∈ wokenStage m k π t} ∪ {π | ψ ∈ {φ | ∃ v, φ = Sum.inr v ∧ v.length ≤ m ∧ ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v}} := by
      ext x; simp [wokenStage]
    rw [h_goal]
    refine MeasurableSet.union (ih ψ) ?_
    simp only [Set.mem_ofPred_eq]
    by_cases h : ∃ v, ψ = Sum.inr v
    · rcases h with ⟨v, hψ⟩
      subst hψ
      simp only [Sum.inr.injEq]
      have h_simp : {π : PFrog → ℕ → Step 3 | ∃ v_1, v = v_1 ∧ v_1.length ≤ m ∧ ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v_1} =
          {π : PFrog → ℕ → Step 3 | v.length ≤ m ∧ ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v} := by
        ext x; simp
      rw [h_simp]
      by_cases hlen : v.length ≤ m
      · have h_eq' : {π : PFrog → ℕ → Step 3 | v.length ≤ m ∧ ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v} =
            {π | ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v} := by
          ext x; simp [hlen]
        rw [h_eq']
        have h_union_eq : {π : PFrog → ℕ → Step 3 | ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v} =
            ⋃ (p : PFrog × ℕ), {π | p.1 ∈ wokenStage m k π t ∧ pos π p.1 p.2 = some v} := by
          ext x; simp
        rw [h_union_eq]
        refine MeasurableSet.iUnion ?_
        intro p
        refine MeasurableSet.inter (ih p.1) ?_
        exact measurableSet_pos_eq_some p.1 p.2 v
      · have h_eq' : {π : PFrog → ℕ → Step 3 | v.length ≤ m ∧ ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v} = ∅ := by
          ext x; simp [hlen]
        rw [h_eq']
        exact MeasurableSet.empty
    · -- ψ is not Sum.inr v for any v
      have h_empty : {π : PFrog → ℕ → Step 3 | ∃ v, ψ = Sum.inr v ∧ v.length ≤ m ∧ ∃ ψ' ∈ wokenStage m k π t, ∃ n, pos π ψ' n = some v} = ∅ := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨v, hψ, _, _, _, _⟩
          exact h ⟨v, hψ⟩
        · intro hx
          exact False.elim hx
      rw [h_empty]
      exact MeasurableSet.empty

-- Measurability of the woken set and of the counts.

/-- The woken set is measurable frog by frog. -/
theorem measurableSet_woken (m k : ℕ) (ψ : PFrog) :
    MeasurableSet {π : PFrog → ℕ → Step 3 | Woken m k π ψ} := by
  have h_eq : {π : PFrog → ℕ → Step 3 | Woken m k π ψ} =
      ⋃ t, {π : PFrog → ℕ → Step 3 | ψ ∈ wokenStage m k π t} := by
    ext π; simp [woken_iff_wokenStage m k π ψ]
  rw [h_eq]
  refine MeasurableSet.iUnion ?_
  intro t
  exact measurableSet_wokenStage m k t ψ

/-- The cardinality of a random subset of a countable type is measurable when each membership
event is. -/
theorem measurable_encard {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (S : Ω → Set α) (hS : ∀ a, MeasurableSet {ω | a ∈ S ω}) :
    Measurable fun ω => (S ω).encard := by
  rw [ENat.measurable_iff]
  intro k
  -- Goal: MeasurableSet ((fun ω => (S ω).encard) ⁻¹' {↑k})
  -- i.e., MeasurableSet {ω | (S ω).encard = (k : ℕ∞)}
  -- {ω | (S ω).encard = (k : ℕ∞)} = {ω | (k : ℕ∞) ≤ (S ω).encard} \ {ω | (k+1 : ℕ∞) ≤ (S ω).encard}
  have h_eq : ((fun ω => (S ω).encard) ⁻¹' {↑k}) =
      {ω | (k : ℕ∞) ≤ (S ω).encard} \ {ω | (k + 1 : ℕ∞) ≤ (S ω).encard} := by
    ext ω
    simp [and_comm, le_antisymm_iff, ENat.lt_add_one_iff (by simp : (k : ℕ∞) ≠ ⊤)]
  rw [h_eq]
  apply MeasurableSet.diff
  · -- {ω | (k : ℕ∞) ≤ (S ω).encard} is measurable
    -- Write as countable union over Finset α with F.card = k
    let T := {F : Finset α // F.card = k}
    have h_eq2 : {ω | (k : ℕ∞) ≤ (S ω).encard} = ⋃ (F : T), {ω | (F.val : Set α) ⊆ S ω} := by
      ext ω
      constructor
      · intro hk
        rcases Set.exists_subset_encard_eq hk with ⟨t, ht, ht_encard⟩
        have hfin : t.Finite := Set.finite_of_encard_eq_coe ht_encard
        let Finset' : Finset α := hfin.toFinset
        have hFcard : Finset'.card = k := by
          have := hfin.encard_eq_coe_toFinset_card
          rw [ht_encard] at this
          simpa [Finset'] using ((ENat.natCast_inj.mp this).symm)
        have hFsub : (Finset' : Set α) ⊆ S ω := by
          rw [hfin.coe_toFinset]
          exact ht
        apply Set.mem_iUnion.mpr
        refine ⟨⟨Finset', hFcard⟩, ?_⟩
        simp [hFsub]
      · intro hk
        rcases Set.mem_iUnion.mp hk with ⟨F, hF⟩
        have hcard' : ((F.val : Finset α) : Set α).encard = (k : ℕ∞) := by
          simp [F.property]
        rw [← hcard']
        exact Set.encard_le_encard hF
    rw [h_eq2]
    apply MeasurableSet.iUnion
    intro F
    have h_eq3 : {ω | (F.val : Set α) ⊆ S ω} = ⋂ a ∈ (F.val : Set α), {ω | a ∈ S ω} := by
      ext ω
      simp [Set.subset_def]
    rw [h_eq3]
    apply MeasurableSet.biInter
    · exact Finset.countable_toSet _
    · intro a ha
      exact hS a
  · -- {ω | (k + 1 : ℕ∞) ≤ (S ω).encard} is measurable
    let T := {F : Finset α // F.card = k + 1}
    have h_eq2 : {ω | (k + 1 : ℕ∞) ≤ (S ω).encard} = ⋃ (F : T), {ω | (F.val : Set α) ⊆ S ω} := by
      ext ω
      constructor
      · intro hk
        rcases Set.exists_subset_encard_eq hk with ⟨t, ht, ht_encard⟩
        have hfin : t.Finite := Set.finite_of_encard_eq_coe ht_encard
        let Finset' : Finset α := hfin.toFinset
        have hFcard : Finset'.card = k + 1 := by
          have := hfin.encard_eq_coe_toFinset_card
          rw [ht_encard] at this
          simpa [Finset'] using ((ENat.natCast_inj.mp this).symm)
        have hFsub : (Finset' : Set α) ⊆ S ω := by
          rw [hfin.coe_toFinset]
          exact ht
        apply Set.mem_iUnion.mpr
        refine ⟨⟨Finset', hFcard⟩, ?_⟩
        simp [hFsub]
      · intro hk
        rcases Set.mem_iUnion.mp hk with ⟨F, hF⟩
        have hcard' : ((F.val : Finset α) : Set α).encard = (k + 1 : ℕ∞) := by
          simp [F.property]
        rw [← hcard']
        exact Set.encard_le_encard hF
    rw [h_eq2]
    apply MeasurableSet.iUnion
    intro F
    have h_eq3 : {ω | (F.val : Set α) ⊆ S ω} = ⋂ a ∈ (F.val : Set α), {ω | a ∈ S ω} := by
      ext ω
      simp [Set.subset_def]
    rw [h_eq3]
    apply MeasurableSet.biInter
    · exact Finset.countable_toSet _
    · intro a ha
      exact hS a

theorem measurableSet_reach (φ : PFrog) :
    MeasurableSet {π : PFrog → ℕ → Step 3 | ∃ n, pos π φ n = none} := by
  have : {π : PFrog → ℕ → Step 3 | ∃ n, pos π φ n = none} =
      ⋃ n, (fun π => pos π φ n) ⁻¹' {none} := by
    ext π
    simp
  rw [this]
  exact MeasurableSet.iUnion fun n => measurable_pos φ n (measurableSet_singleton _)

theorem measurable_plantedG (m k : ℕ) : Measurable (plantedG m k) :=
  measurable_encard (fun π => {φ | Woken m k π φ ∧ ∃ n, pos π φ n = none}) fun φ =>
    (measurableSet_woken m k φ).inter (measurableSet_reach φ)

theorem measurable_presN (m k : ℕ) : Measurable (presN m k) :=
  measurable_encard (fun π => {p : PFrog × ℕ | Woken m k π p.1 ∧ pos π p.1 p.2 = some []})
    fun p => (measurableSet_woken m k p.1).inter
      (measurable_pos p.1 p.2 (measurableSet_singleton _))

/-- **`measurable_plantedPair`** (with Lemma 10.1 of the paper). -/
theorem measurable_plantedPair_proof : measurable_plantedPair := by
  intro m
  exact (Measurable.of_eval fun k => measurable_plantedG m k).prodMk
    (Measurable.of_eval fun k => measurable_presN m k)

/-- **`measurable_closPair`** (with Lemma 10.1 of the paper), `measurable_closCurvePair` of
FrogModel/D3/LaneB/Succ.lean. -/
theorem measurable_closPair_proof :
    Measurable fun x : ClosSample => (closCurve x.1 x.2, closNCurve x.1 x.2) :=
  Iface.measurable_closCurvePair

end FrogModel.D3.LaneA
