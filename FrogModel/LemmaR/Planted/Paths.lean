module

public import FrogModel.LemmaR.Planted.Defs
public import FrogModel.Pieces.Basic

@[expose] public section

/-!
# Lemma 9.2 of the paper: pathwise comparisons and measurability

`Z_m ≤ X` (`plantedCount_le_frozenCount`), `Z_m ≤ U'_m` (`plantedCount_le_plantedAwake`),
`Z_m ≤ Z_(m+1)` (`plantedCount_mono`), measurability of `Z_m` (`measurable_plantedCount`), and the
cross-check of the frozen definition against `ReachStar` (`plantedCount_eq_reachStar`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaR

/-- A frog reached through arcs towards depth at most `m` is at depth at most `m`. -/
theorem FrogModel.LemmaR.reachTrunc_length_le {d : ℕ} (m : ℕ) (ζ : Sample d) (v : Vertex d)
    (h : Relation.ReflTransGen (starArcTrunc m ζ) [] v) : v.length ≤ m := by
  cases h.cases_tail with
  | inl h0 => subst h0; simp
  | inr h1 =>
    obtain ⟨b, _, hb⟩ := h1
    exact hb.2

/-- `Z_m ≤ X` pathwise. -/
theorem FrogModel.LemmaR.plantedCount_le_frozenCount {d : ℕ} (m : ℕ) (ζ : Sample d) :
    plantedCount m ζ ≤ frozenCount ζ := by
  classical
  unfold plantedCount frozenCount
  refine ENNReal.tsum_le_tsum fun v => ?_
  have hmono : Relation.ReflTransGen (starArcTrunc m ζ) [] v →
      Relation.ReflTransGen (starArc ζ) [] v :=
    by
    intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail hbc.1
  split_ifs with h1 h2 h2 <;> first | exact le_rfl | exact zero_le | exact absurd ⟨hmono h1.1, h1.2⟩ h2

/-- `Z_m ≤ U'_m` pathwise. -/
theorem FrogModel.LemmaR.plantedCount_le_plantedAwake {d : ℕ} (m : ℕ) (ζ : Sample d) :
    plantedCount m ζ ≤ plantedAwake m ζ := by
  classical
  unfold plantedCount plantedAwake
  refine ENNReal.tsum_le_tsum fun v => ?_
  split_ifs with h1 h2 h2 <;> first | exact le_rfl | exact zero_le |
    exact absurd ⟨reachTrunc_length_le m ζ v h1.1, h1.2⟩ h2

/-- `Z_m ≤ Z_(m+1)` pathwise. -/
theorem FrogModel.LemmaR.plantedCount_mono {d : ℕ} (m : ℕ) (ζ : Sample d) :
    plantedCount m ζ ≤ plantedCount (m + 1) ζ := by
  classical
  unfold plantedCount
  refine ENNReal.tsum_le_tsum fun v => ?_
  have hmono : Relation.ReflTransGen (starArcTrunc m ζ) [] v →
      Relation.ReflTransGen (starArcTrunc (m + 1) ζ) [] v :=
    by
    intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail ⟨hbc.1, by have := hbc.2; omega⟩
  split_ifs with h1 h2 h2 <;> first | exact le_rfl | exact zero_le | exact absurd ⟨hmono h1.1, h1.2⟩ h2

/-- The frogs reached through arcs towards depth at most `m` form a measurable event. -/
theorem FrogModel.LemmaR.measurableSet_reflTransGen_starArcTrunc {d : ℕ} (m : ℕ) (v : Vertex d) :
    MeasurableSet {ζ : Sample d | Relation.ReflTransGen (starArcTrunc m ζ) [] v} := by
  have harc : ∀ a b : Vertex d, MeasurableSet {ζ : Sample d | starArcTrunc m ζ a b} := by
    intro a b
    by_cases hb : b.length ≤ m
    · simpa [starArcTrunc, hb] using measurableSet_starArc d a b
    · simp [starArcTrunc, hb]
  have hchain : ∀ l : List (Vertex d),
      MeasurableSet {ζ : Sample d | List.IsChain (starArcTrunc m ζ) l} := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
        have h : {ζ : Sample d | List.IsChain (starArcTrunc m ζ) (a :: b :: l)} =
            {ζ | starArcTrunc m ζ a b} ∩ {ζ | List.IsChain (starArcTrunc m ζ) (b :: l)} := by
          ext ζ
          simp [List.isChain_cons_cons]
        rw [h]
        exact (harc a b).inter ih
  have hset : {ζ : Sample d | Relation.ReflTransGen (starArcTrunc m ζ) [] v} =
      ⋃ l : {l : List (Vertex d) // ∃ hl : l ≠ [], l.head hl = [] ∧ l.getLast hl = v},
        {ζ : Sample d | List.IsChain (starArcTrunc m ζ) l.1} := by
    ext ζ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨l, hl, hc, hh, hla⟩ := List.exists_isChain_ne_nil_of_relationReflTransGen h
      exact ⟨⟨l, hl, hh, hla⟩, hc⟩
    · rintro ⟨⟨l, hl, hh, hla⟩, hc⟩
      have := List.relationReflTransGen_of_exists_isChain l hc hl
      rwa [hh, hla] at this
  rw [hset]
  exact MeasurableSet.iUnion fun l => hchain l.1

/-- `Z_m` is measurable. -/
theorem FrogModel.LemmaR.measurable_plantedCount {d : ℕ} (m : ℕ) :
    Measurable (plantedCount (d := d) m) := by
  classical
  unfold plantedCount
  refine Measurable.tsum fun v => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_reflTransGen_starArcTrunc m v).inter
    (measurableSet_exists_walkStar_none d v)

/-- Cross-check of the frozen `plantedCount`: `Z_m` counts the frogs of `ReachStar ζ m` whose
path reaches `y`. -/
theorem FrogModel.LemmaR.plantedCount_eq_reachStar {d : ℕ} (m : ℕ) (ζ : Sample d) :
    plantedCount m ζ = (({v : Vertex d | ReachStar ζ m v ∧
      ∃ n, walkStar (some v) (ζ v) n = none}.encard : ℕ∞) : ℝ≥0∞) := by
  classical
  have hiff : ∀ v, Relation.ReflTransGen (starArcTrunc m ζ) [] v ↔ ReachStar ζ m v := by
    intro v
    constructor
    · intro h
      induction h with
      | refl => exact ReachStar.root
      | tail _ hbc ih =>
        obtain ⟨⟨_, n, hn⟩, hlen⟩ := hbc
        exact ReachStar.path n ih hn hlen
    · intro h
      induction h with
      | root => exact Relation.ReflTransGen.refl
      | @path a b n _ hn hlen ih =>
        by_cases hb : b = []
        · subst hb
          exact Relation.ReflTransGen.refl
        · exact ih.tail ⟨⟨hb, n, hn⟩, hlen⟩
  unfold plantedCount
  rw [← ENNReal.tsum_set_one, tsum_subtype _ (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun v => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, hiff]
