module

public import FrogModel.LemmaX.KillDefs
public import FrogModel.LemmaX.Psi
public import FrogModel.Pieces.Basic

@[expose] public section

/-!
# Lemma X: the kill depth and Lemma 4.1

Monotonicity in the kill depth (`visitsK_mono`, `starArcK_mono`,
`frozenCountK_mono`), every visit happens before the kill at some depth (`exists_visitsK`,
`reflTransGen_starArc_iff`, `frozen_iff_exists`), Lemma 4.1 pathwise and in mean
(`iSup_frozenCountK`, `meanX_eq_iSup`), the curve (`curveK_zero`, `curveK_mono`,
`frozenCountK_eq_curveK`), and the measurability of `frozenCountK`, `curveK` and `psiG`
(`measurable_frozenCountK`, `measurable_curveK`, `measurable_psiG`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaX

/-- A visit before the kill at depth `K` is a visit before the kill at any larger depth. -/
theorem FrogModel.LemmaX.visitsK_mono {d : ℕ} (K K' : ℕ) (h : K ≤ K') (v : Option (Vertex d))
    (x : ℕ → Step d) (b : Option (Vertex d)) (hv : visitsK K v x b) : visitsK K' v x b := by
  obtain ⟨n, h1, h2⟩ := hv
  exact ⟨n, h1, fun i hi => (h2 i hi).trans h⟩

/-- The arcs at kill depth `K` are arcs at any larger depth. -/
theorem FrogModel.LemmaX.starArcK_mono {d : ℕ} (K K' : ℕ) (h : K ≤ K') (ζ : Sample d)
    (a b : Vertex d) (hab : starArcK K ζ a b) : starArcK K' ζ a b := by
  exact ⟨hab.1, visitsK_mono K K' h _ _ _ hab.2⟩

/-- Reachability at kill depth `K` gives reachability at any larger depth. -/
theorem FrogModel.LemmaX.reflTransGen_starArcK_mono {d : ℕ} (K K' : ℕ) (h : K ≤ K')
    (ζ : Sample d) (a b : Vertex d) (hab : Relation.ReflTransGen (starArcK K ζ) a b) :
    Relation.ReflTransGen (starArcK K' ζ) a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih => exact ih.tail (starArcK_mono K K' h ζ _ _ h2)

/-- `X^(K)` is non-decreasing in `K`. -/
theorem FrogModel.LemmaX.frozenCountK_mono {d : ℕ} (ζ : Sample d) :
    Monotone fun K => frozenCountK K ζ := by
  intro K K' h
  refine ENNReal.tsum_le_tsum fun v => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨reflTransGen_starArcK_mono K K' h ζ _ _ h1.1, visitsK_mono K K' h _ _ _ h1.2⟩ h2
  · exact zero_le
  · exact le_rfl

/-- A visit at time `n` is a visit before the kill at some depth. -/
theorem FrogModel.LemmaX.exists_visitsK {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) (n : ℕ)
    (b : Option (Vertex d)) (h : walkStar v x n = b) : ∃ K, visitsK K v x b := by
  refine ⟨(Finset.range (n + 1)).sup fun i => depthStar (walkStar v x i), n, h, fun i hi => ?_⟩
  exact Finset.le_sup (f := fun i => depthStar (walkStar v x i))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- An arc of `T*` is an arc at some kill depth. -/
theorem FrogModel.LemmaX.starArc_iff_exists {d : ℕ} (ζ : Sample d) (a b : Vertex d) :
    starArc ζ a b ↔ ∃ K, starArcK K ζ a b := by
  constructor
  · rintro ⟨hb, n, hn⟩
    obtain ⟨K, hK⟩ := exists_visitsK (some a) (ζ a) n (some b) hn
    exact ⟨K, hb, hK⟩
  · rintro ⟨K, hb, n, hn, -⟩
    exact ⟨hb, n, hn⟩

/-- Reachability in `T*` is reachability at some kill depth. -/
theorem FrogModel.LemmaX.reflTransGen_starArc_iff {d : ℕ} (ζ : Sample d) (a b : Vertex d) :
    Relation.ReflTransGen (starArc ζ) a b ↔ ∃ K, Relation.ReflTransGen (starArcK K ζ) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, Relation.ReflTransGen.refl⟩
    | tail _ hbc ih =>
      obtain ⟨K1, h1⟩ := ih
      obtain ⟨K2, h2⟩ := (starArc_iff_exists ζ _ _).1 hbc
      exact ⟨max K1 K2, (reflTransGen_starArcK_mono K1 _ (le_max_left _ _) ζ _ _ h1).tail
        (starArcK_mono K2 _ (le_max_right _ _) ζ _ _ h2)⟩
  · rintro ⟨K, h⟩
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h2 ih => exact ih.tail ((starArc_iff_exists ζ _ _).2 ⟨K, h2⟩)

/-- A frozen frog of `T*` is frozen at some kill depth. -/
theorem FrogModel.LemmaX.frozen_iff_exists {d : ℕ} (ζ : Sample d) (v : Vertex d) :
    (Relation.ReflTransGen (starArc ζ) [] v ∧ ∃ n, walkStar (some v) (ζ v) n = none) ↔
      ∃ K, Relation.ReflTransGen (starArcK K ζ) [] v ∧ visitsK K (some v) (ζ v) none := by
  constructor
  · rintro ⟨h1, n, hn⟩
    obtain ⟨K1, hK1⟩ := (reflTransGen_starArc_iff ζ [] v).1 h1
    obtain ⟨K2, hK2⟩ := exists_visitsK (some v) (ζ v) n none hn
    exact ⟨max K1 K2, reflTransGen_starArcK_mono K1 _ (le_max_left _ _) ζ _ _ hK1,
      visitsK_mono K2 _ (le_max_right _ _) _ _ _ hK2⟩
  · rintro ⟨K, h1, n, hn, -⟩
    exact ⟨(reflTransGen_starArc_iff ζ [] v).2 ⟨K, h1⟩, n, hn⟩

/-- Lemma 4.1, pathwise: the supremum of `X^(K)` over `K` is `X`. -/
theorem FrogModel.LemmaX.iSup_frozenCountK {d : ℕ} (ζ : Sample d) :
    ⨆ K, frozenCountK K ζ = frozenCount ζ := by
  classical
  set f : ℕ → Vertex d → ℝ≥0∞ := fun K v =>
    if Relation.ReflTransGen (starArcK K ζ) [] v ∧ visitsK K (some v) (ζ v) none then 1 else 0
    with hf
  have hmono : Monotone f := by
    intro K K' h v
    simp only [hf]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨reflTransGen_starArcK_mono K K' h ζ _ _ h1.1, visitsK_mono K K' h _ _ _ h1.2⟩ h2
    · exact zero_le
    · exact le_rfl
  have hK : ∀ K, frozenCountK K ζ = ∫⁻ v, f K v ∂Measure.count := fun K => by
    rw [lintegral_count]
    rfl
  simp_rw [hK]
  rw [← lintegral_iSup (fun K => Measurable.of_discrete) hmono, lintegral_count]
  unfold frozenCount
  congr 1
  ext v
  by_cases h : Relation.ReflTransGen (starArc ζ) [] v ∧ ∃ n, walkStar (some v) (ζ v) n = none
  · simp only [eq_true h, ite_true]
    obtain ⟨K, hK⟩ := (frozen_iff_exists ζ v).1 h
    refine le_antisymm (iSup_le fun K => ?_) (le_iSup_of_le K (by simp [hf, hK]))
    simp only [hf]
    split_ifs <;> simp
  · simp only [eq_false h, ite_false]
    refine le_antisymm (iSup_le fun K => ?_) zero_le
    simp only [hf]
    simp only [eq_false fun hK => h ((frozen_iff_exists ζ v).2 ⟨K, hK⟩), ite_false, le_refl]

/-- A sum of indicators over a countable type is the cardinality of the set. -/
theorem FrogModel.LemmaX.tsum_ite_one_eq_encard {α : Type*} [Countable α] (p : α → Prop)
    [DecidablePred p] : ∑' a, (if p a then 1 else 0 : ℝ≥0∞) = (({a | p a}.encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have h : (fun a => if p a then (1 : ℝ≥0∞) else 0) = Set.indicator {a | p a} 1 := by
    ext a
    simp [Set.indicator_apply]
  rw [h, ← Measure.count_apply (MeasurableSet.of_discrete), ← lintegral_indicator_one
    (MeasurableSet.of_discrete), lintegral_count]

/-- `G_K(0) = 0`. -/
theorem FrogModel.LemmaX.curveK_zero {d : ℕ} (K : ℕ) (ζ : Sample d) (ξ : ℕ → ℕ → Step d) :
    curveK K ζ ξ 0 = 0 := by
  simp [curveK, reachedK]

/-- Nesting: `G_K` is non-decreasing in the number of active frogs. -/
theorem FrogModel.LemmaX.curveK_mono {d : ℕ} (K : ℕ) (ζ : Sample d) (ξ : ℕ → ℕ → Step d) :
    Monotone (curveK K ζ ξ) := by
  intro m m' h
  unfold curveK
  refine add_le_add (Set.encard_le_encard fun a ha => ⟨lt_of_lt_of_le ha.1 h, ha.2⟩)
    (Set.encard_le_encard fun b hb => ⟨?_, hb.2⟩)
  obtain ⟨a, ha, rest⟩ := hb.1
  exact ⟨a, lt_of_lt_of_le ha h, rest⟩

/-- `X^(K)` is the first value of the curve whose active frog follows the frog at `r`. -/
theorem FrogModel.LemmaX.frozenCountK_eq_curveK {d : ℕ} (K : ℕ) (ζ : Sample d) :
    frozenCountK K ζ = (curveK K ζ (fun _ => ζ []) 1 : ℝ≥0∞) := by
  classical
  set Q : Prop := visitsK K (some []) (ζ []) none with hQ
  set B : Set (Vertex d) :=
    {b | reachedK K ζ (fun _ => ζ []) 1 b ∧ visitsK K (some b) (ζ b) none} with hB
  have hBne : ∀ b ∈ B, b ≠ [] := by
    rintro b ⟨⟨a, -, v, hv, -, hvb⟩, -⟩
    rcases Relation.ReflTransGen.cases_tail hvb with rfl | ⟨c, -, hcb⟩
    · exact hv
    · exact hcb.1
  have hsplit : {v : Vertex d | Relation.ReflTransGen (starArcK K ζ) [] v ∧
      visitsK K (some v) (ζ v) none} = {v | v = [] ∧ Q} ∪ B := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_union, hB, hQ]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hv : v = []
      · subst hv
        exact Or.inl ⟨rfl, h2⟩
      · rcases Relation.ReflTransGen.cases_head h1 with h | ⟨c, hc, hcv⟩
        · exact absurd h.symm hv
        · exact Or.inr ⟨⟨0, Nat.zero_lt_one, c, hc.1, hc.2, hcv⟩, h2⟩
    · rintro (⟨rfl, hq⟩ | ⟨⟨a, -, c, hc, hvc, hcv⟩, h2⟩)
      · exact ⟨Relation.ReflTransGen.refl, hq⟩
      · exact ⟨Relation.ReflTransGen.head ⟨hc, hvc⟩ hcv, h2⟩
  have hdisj : Disjoint {v : Vertex d | v = [] ∧ Q} B := by
    rw [Set.disjoint_left]
    rintro v ⟨rfl, -⟩ hvB
    exact hBne _ hvB rfl
  have h1 : {v : Vertex d | v = [] ∧ Q}.encard = {a : ℕ | a < 1 ∧ Q}.encard := by
    by_cases hq : Q
    · have e1 : {v : Vertex d | v = [] ∧ Q} = {[]} := by ext v; simp [hq]
      have e2 : {a : ℕ | a < 1 ∧ Q} = {0} := by ext a; simp [hq]
      rw [e1, e2, Set.encard_singleton, Set.encard_singleton]
    · have e1 : {v : Vertex d | v = [] ∧ Q} = ∅ := by ext v; simp [hq]
      have e2 : {a : ℕ | a < 1 ∧ Q} = ∅ := by ext a; simp [hq]
      rw [e1, e2, Set.encard_empty, Set.encard_empty]
  unfold frozenCountK
  rw [tsum_ite_one_eq_encard, hsplit, Set.encard_union_eq hdisj, h1]
  rfl

/-- The walk on `T*` at a fixed time is measurable in the steps. -/
theorem FrogModel.LemmaX.measurable_walkStar_apply {d : ℕ} (v : Option (Vertex d)) (n : ℕ) :
    Measurable fun x : ℕ → Step d => walkStar v x n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have h_step : Measurable fun p : Option (Vertex d) × Step d => stepStar p.1 p.2 :=
      measurable_of_countable _
    exact h_step.comp (ih.prodMk (measurable_pi_apply n))

/-- Visiting `b` before the kill is a measurable event of the steps. -/
theorem FrogModel.LemmaX.measurableSet_visitsK {d : ℕ} (K : ℕ) (v b : Option (Vertex d)) :
    MeasurableSet {x : ℕ → Step d | visitsK K v x b} := by
  have h : {x : ℕ → Step d | visitsK K v x b} = ⋃ n, ({x | walkStar v x n = b} ∩
      ⋂ i ∈ Finset.range (n + 1), {x | depthStar (walkStar v x i) ≤ K}) := by
    ext x
    simp [visitsK]
  rw [h]
  exact MeasurableSet.iUnion fun n =>
    (measurable_walkStar_apply v n (measurableSet_singleton b)).inter
      (MeasurableSet.biInter (Finset.range _).countable_toSet fun i _ =>
        measurable_walkStar_apply v i
          (MeasurableSet.of_discrete (s := {u : Option (Vertex d) | depthStar u ≤ K})))

/-- An arc at kill depth `K` is a measurable event of the sample. -/
theorem FrogModel.LemmaX.measurableSet_starArcK {d : ℕ} (K : ℕ) (a b : Vertex d) :
    MeasurableSet {ζ : Sample d | starArcK K ζ a b} := by
  by_cases hb : b = []
  · have h : {ζ : Sample d | starArcK K ζ a b} = ∅ := by
      ext ζ
      simp [starArcK, hb]
    rw [h]
    exact MeasurableSet.empty
  · have h : {ζ : Sample d | starArcK K ζ a b} =
        (fun ζ : Sample d => ζ a) ⁻¹' {x | visitsK K (some a) x (some b)} := by
      ext ζ
      simp [starArcK, hb]
    rw [h]
    exact measurable_pi_apply a (measurableSet_visitsK K _ _)

/-- Reachability in a countable digraph whose arcs are measurable events is a measurable
event. -/
theorem FrogModel.LemmaX.measurableSet_reflTransGen {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    (r : Ω → V → V → Prop) (hr : ∀ a b, MeasurableSet {ω | r ω a b}) (a b : V) :
    MeasurableSet {ω | Relation.ReflTransGen (r ω) a b} := by
  let R : ℕ → V → Set Ω := fun n => Nat.rec (fun c => {ω : Ω | a = c})
    (fun _ Rn c => Rn c ∪ ⋃ e, Rn e ∩ {ω | r ω e c}) n
  have hR0 : ∀ c, R 0 c = {ω | a = c} := fun c => rfl
  have hRs : ∀ n c, R (n + 1) c = R n c ∪ ⋃ e, R n e ∩ {ω | r ω e c} := fun n c => rfl
  have hmeas : ∀ n c, MeasurableSet (R n c) := by
    intro n
    induction n with
    | zero => intro c; rw [hR0]; exact MeasurableSet.const _
    | succ n ih =>
      intro c
      rw [hRs]
      exact (ih c).union (MeasurableSet.iUnion fun e => (ih e).inter (hr e c))
  have hiff : ∀ ω c, Relation.ReflTransGen (r ω) a c ↔ ∃ n, ω ∈ R n c := by
    intro ω c
    constructor
    · intro h
      induction h with
      | refl => exact ⟨0, by rw [hR0]; rfl⟩
      | tail _ hbc ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, by rw [hRs]; exact Or.inr (Set.mem_iUnion.2 ⟨_, hn, hbc⟩)⟩
    · rintro ⟨n, hn⟩
      induction n generalizing c with
      | zero =>
        rw [hR0] at hn
        have hac : a = c := hn
        subst hac
        exact Relation.ReflTransGen.refl
      | succ n ih =>
        rw [hRs] at hn
        rcases hn with hn | hn
        · exact ih c hn
        · obtain ⟨e, he, hec⟩ := Set.mem_iUnion.1 hn
          exact (ih e he).tail hec
  have h : {ω | Relation.ReflTransGen (r ω) a b} = ⋃ n, R n b := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact hiff ω b
  rw [h]
  exact MeasurableSet.iUnion fun n => hmeas n b

/-- Reachability at kill depth `K` is a measurable event of the sample. -/
theorem FrogModel.LemmaX.measurableSet_reflTransGen_starArcK {d : ℕ} (K : ℕ) (a b : Vertex d) :
    MeasurableSet {ζ : Sample d | Relation.ReflTransGen (starArcK K ζ) a b} := by
  exact FrogModel.LemmaX.measurableSet_reflTransGen (fun ζ => starArcK K ζ)
    (fun a b => measurableSet_starArcK K a b) a b

/-- `X^(K)` is measurable. -/
theorem FrogModel.LemmaX.measurable_frozenCountK {d : ℕ} (K : ℕ) :
    Measurable (frozenCountK (d := d) K) := by
  unfold frozenCountK
  refine Measurable.tsum fun v => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  have hm : Measurable fun ζ : Sample d => ζ v := measurable_pi_apply v
  have hv : MeasurableSet {ζ : Sample d | visitsK K (some v) (ζ v) none} :=
    hm (measurableSet_visitsK K (some v) none)
  exact (measurableSet_reflTransGen_starArcK K [] v).inter hv

/-- Lemma 4.1 in mean: `E X = sup_K E X^(K)`. -/
theorem FrogModel.LemmaX.meanX_eq_iSup (d : ℕ) [NeZero d] :
    meanX d = ⨆ K, ∫⁻ ζ, frozenCountK K ζ ∂frogMeasure d := by
  unfold meanX
  simp_rw [← iSup_frozenCountK]
  exact lintegral_iSup (fun K => measurable_frozenCountK K) fun K K' h ζ => frozenCountK_mono ζ h

/-- Being reached at kill depth `K` is a measurable event of the sample and the active paths. -/
theorem FrogModel.LemmaX.measurableSet_reachedK {d : ℕ} (K m : ℕ) (b : Vertex d) :
    MeasurableSet {p : Sample d × (ℕ → ℕ → Step d) | reachedK K p.1 p.2 m b} := by
  have h : {p : Sample d × (ℕ → ℕ → Step d) | reachedK K p.1 p.2 m b} =
      ⋃ a ∈ Finset.range m, ⋃ v : Vertex d, ({_p : Sample d × (ℕ → ℕ → Step d) | v ≠ []} ∩
        {p | visitsK K (some []) (p.2 a) (some v)} ∩
        {p | Relation.ReflTransGen (starArcK K p.1) v b}) := by
    ext p
    simp [reachedK, and_assoc]
  rw [h]
  refine MeasurableSet.biUnion (Finset.range m).countable_toSet fun a _ =>
    MeasurableSet.iUnion fun v => ((MeasurableSet.const _).inter ?_).inter ?_
  · have hm : Measurable fun p : Sample d × (ℕ → ℕ → Step d) => p.2 a :=
      (measurable_pi_apply a).comp measurable_snd
    exact hm (measurableSet_visitsK K (some []) (some v))
  · exact measurable_fst (measurableSet_reflTransGen_starArcK K v b)

/-- The curve is measurable in the sample and the paths of the active frogs. -/
theorem FrogModel.LemmaX.measurable_curveK {d : ℕ} (K : ℕ) :
    Measurable fun p : Sample d × (ℕ → ℕ → Step d) => curveK K p.1 p.2 := by
  refine measurable_pi_iff.2 fun m => ?_
  have h1 : Measurable fun p : Sample d × (ℕ → ℕ → Step d) =>
      {a : ℕ | a < m ∧ visitsK K (some []) (p.2 a) none} := by
    refine measurable_set_iff.2 fun a => ?_
    refine measurableSet_setOfPred.1 ?_
    have hm : Measurable fun p : Sample d × (ℕ → ℕ → Step d) => p.2 a :=
      (measurable_pi_apply a).comp measurable_snd
    have hs : MeasurableSet {p : Sample d × (ℕ → ℕ → Step d) | visitsK K (some []) (p.2 a) none} :=
      hm (measurableSet_visitsK K (some []) none)
    exact (MeasurableSet.const _).inter hs
  have h2 : Measurable fun p : Sample d × (ℕ → ℕ → Step d) =>
      {b : Vertex d | reachedK K p.1 p.2 m b ∧ visitsK K (some b) (p.1 b) none} := by
    refine measurable_set_iff.2 fun b => ?_
    refine measurableSet_setOfPred.1 ?_
    have hm : Measurable fun p : Sample d × (ℕ → ℕ → Step d) => p.1 b :=
      (measurable_pi_apply b).comp measurable_fst
    have hs : MeasurableSet {p : Sample d × (ℕ → ℕ → Step d) | visitsK K (some b) (p.1 b) none} :=
      hm (measurableSet_visitsK K (some b) none)
    exact (measurableSet_reachedK K m b).inter hs
  have hadd : Measurable fun q : ℕ∞ × ℕ∞ => q.1 + q.2 := measurable_of_countable _
  exact hadd.comp ((measurable_encard.comp h1).prodMk (measurable_encard.comp h2))

/-- A countable supremum of measurable `ℕ∞`-valued maps is measurable. -/
theorem FrogModel.LemmaX.measurable_iSup_enat {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (f : ι → α → ℕ∞) (hf : ∀ i, Measurable (f i)) : Measurable fun x => ⨆ i, f i x := by
  refine ENat.measurable_iff.2 fun n => ?_
  rcases n with _ | k
  · have h : (fun x => ⨆ i, f i x) ⁻¹' {((0 : ℕ) : ℕ∞)} = ⋂ i, f i ⁻¹' {0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Nat.cast_zero]
      constructor
      · intro h i
        exact le_antisymm (h ▸ le_iSup (fun i => f i x) i) zero_le
      · intro h
        exact le_antisymm (iSup_le fun i => (h i).le) zero_le
    rw [h]
    exact MeasurableSet.iInter fun i => hf i (measurableSet_singleton 0)
  · have h : (fun x => ⨆ i, f i x) ⁻¹' {((k + 1 : ℕ) : ℕ∞)} =
        (⋂ i, f i ⁻¹' Set.Iic ((k + 1 : ℕ) : ℕ∞)) ∩ ⋃ i, f i ⁻¹' {((k + 1 : ℕ) : ℕ∞)} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_Iic, Set.mem_iUnion]
      constructor
      · intro h
        refine ⟨fun i => h ▸ le_iSup (fun i => f i x) i, ?_⟩
        by_contra hne
        push Not at hne
        have hle : ∀ i, f i x ≤ k := by
          intro i
          have h1 : f i x ≤ ((k + 1 : ℕ) : ℕ∞) := h ▸ le_iSup (fun i => f i x) i
          have h2 : f i x < ((k + 1 : ℕ) : ℕ∞) := lt_of_le_of_ne h1 (hne i)
          exact Order.le_of_lt_add_one (by exact_mod_cast h2 : f i x < (k : ℕ∞) + 1)
        have := iSup_le hle
        rw [h] at this
        exact absurd this (by norm_cast; omega)
      · rintro ⟨hle, i, hi⟩
        exact le_antisymm (iSup_le hle) (hi ▸ le_iSup (fun i => f i x) i)
    rw [h]
    exact (MeasurableSet.iInter fun i => hf i MeasurableSet.of_discrete).inter
      (MeasurableSet.iUnion fun i => hf i (measurableSet_singleton _))

/-- The direction count is measurable in the directions. -/
theorem FrogModel.LemmaX.measurable_dirCount {d : ℕ} (a : Fin (d + 1)) (n : ℕ∞) :
    Measurable fun D : ℕ → Fin (d + 1) => dirCount D a n := by
  have h : Measurable fun D : ℕ → Fin (d + 1) => {k : ℕ | (k : ℕ∞) < n ∧ D k = a} := by
    refine measurable_set_iff.2 fun k => measurableSet_setOfPred.1 ?_
    have hm : Measurable fun D : ℕ → Fin (d + 1) => D k := measurable_pi_apply k
    exact (MeasurableSet.const _).inter (hm (measurableSet_singleton a))
  exact measurable_encard.comp h

/-- The extended curve is measurable in the curve. -/
theorem FrogModel.LemmaX.measurable_extCurve (m : ℕ∞) :
    Measurable fun G : ℕ → ℕ∞ => extCurve G m := by
  have hi : ∀ i : ℕ, Measurable fun G : ℕ → ℕ∞ => ⨆ (_ : (i : ℕ∞) ≤ m), G i := by
    intro i
    by_cases h : (i : ℕ∞) ≤ m
    · simp only [iSup_pos h]
      exact measurable_pi_apply i
    · simp only [iSup_neg h]
      exact measurable_const
  exact measurable_iSup_enat (fun (i : ℕ) (G : ℕ → ℕ∞) => ⨆ (_ : (i : ℕ∞) ≤ m), G i) hi

/-- `T_j(n)` is measurable in the child curves and the directions. -/
theorem FrogModel.LemmaX.measurable_psiT {d : ℕ} (j : ℕ) (n : ℕ∞) :
    Measurable fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) => psiT x.1 x.2 j n := by
  have hret : Measurable fun q : (ℕ → ℕ∞) × ℕ∞ => childRet q.1 q.2 := by
    refine measurable_from_prod_countable_left fun m => ?_
    by_cases hm : m = 0
    · simp only [childRet, hm, ite_true]
      exact measurable_const
    · simp only [childRet, hm, ite_false]
      exact measurable_extCurve (m + 1)
  have hv : Measurable fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) =>
      fun c : Fin d => childRet (x.1 c) (dirCount x.2 c.succ n) := by
    refine measurable_pi_iff.2 fun c => ?_
    have h1 : Measurable fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) => x.1 c :=
      (measurable_pi_apply c).comp measurable_fst
    have h2 : Measurable fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) =>
        dirCount x.2 c.succ n :=
      (measurable_dirCount c.succ n).comp measurable_snd
    exact hret.comp (h1.prodMk h2)
  have hs : Measurable fun v : Fin d → ℕ∞ => (j : ℕ∞) + ∑ c, v c := measurable_of_countable _
  exact hs.comp hv

/-- `N(j)` is measurable in the child curves and the directions. -/
theorem FrogModel.LemmaX.measurable_psiN {d : ℕ} (j : ℕ) :
    Measurable fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) => psiN x.1 x.2 j := by
  have hjoint : Measurable fun q : ((Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1))) × ℕ∞ =>
      psiT q.1.1 q.1.2 j q.2 :=
    measurable_from_prod_countable_left fun n => measurable_psiT j n
  have hit : ∀ t : ℕ, Measurable fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) =>
      (psiT x.1 x.2 j)^[t] 0 := by
    intro t
    induction t with
    | zero =>
      simp only [Function.iterate_zero, id]
      exact measurable_const
    | succ t ih =>
      have hc := Measurable.comp (g := fun q : ((Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1))) × ℕ∞ =>
          psiT q.1.1 q.1.2 j q.2)
        (f := fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) => (x, (psiT x.1 x.2 j)^[t] 0))
        hjoint (measurable_id.prodMk ih)
      simp only [Function.iterate_succ_apply']
      exact hc
  have heq : (fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) => psiN x.1 x.2 j) =
      fun x => ⨆ t : ℕ, (psiT x.1 x.2 j)^[t] 0 := by
    funext x
    exact psiN_eq_iSup_iterate x.1 x.2 j
  rw [heq]
  exact measurable_iSup_enat (fun (t : ℕ) (x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1))) =>
    (psiT x.1 x.2 j)^[t] 0) hit

/-- `Psi` is measurable: the curve `G` in the child curves and the directions. -/
theorem FrogModel.LemmaX.measurable_psiG {d : ℕ} :
    Measurable fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) => psiG x.1 x.2 := by
  have hdir : Measurable fun q : (ℕ → Fin (d + 1)) × ℕ∞ => dirCount q.1 0 q.2 :=
    measurable_from_prod_countable_left fun n => measurable_dirCount 0 n
  refine measurable_pi_iff.2 fun j => ?_
  exact hdir.comp (measurable_snd.prodMk (measurable_psiN j))

/-- Reachability from `v ≠ r` at kill depth `K` does not read the sleeping frog at `r`. -/
theorem FrogModel.LemmaX.reflTransGen_starArcK_congr {d : ℕ} (K : ℕ) (ζ ζ' : Sample d)
    (hζ : ∀ v, v ≠ [] → ζ v = ζ' v) (v b : Vertex d) (hv : v ≠ [])
    (h : Relation.ReflTransGen (starArcK K ζ) v b) : Relation.ReflTransGen (starArcK K ζ') v b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c e hvc hce ih =>
    have hc : c ≠ [] := by
      rcases Relation.ReflTransGen.cases_tail hvc with rfl | ⟨_, -, h⟩
      · exact hv
      · exact h.1
    refine ih.tail ⟨hce.1, ?_⟩
    rw [← hζ c hc]
    exact hce.2

/-- The curve reads neither the sleeping frog at `r` nor the active frogs `ξ a`, `a ≥ m`. -/
theorem FrogModel.LemmaX.curveK_congr {d : ℕ} (K m : ℕ) (ζ ζ' : Sample d) (ξ ξ' : ℕ → ℕ → Step d)
    (hζ : ∀ v, v ≠ [] → ζ v = ζ' v) (hξ : ∀ a < m, ξ a = ξ' a) :
    curveK K ζ ξ m = curveK K ζ' ξ' m := by
  have hζ' : ∀ v, v ≠ [] → ζ' v = ζ v := fun v hv => (hζ v hv).symm
  have hξ' : ∀ a < m, ξ' a = ξ a := fun a ha => (hξ a ha).symm
  have hreach : ∀ (ζ₁ ζ₂ : Sample d) (ξ₁ ξ₂ : ℕ → ℕ → Step d),
      (∀ v, v ≠ [] → ζ₁ v = ζ₂ v) → (∀ a < m, ξ₁ a = ξ₂ a) → ∀ b,
      reachedK K ζ₁ ξ₁ m b ∧ visitsK K (some b) (ζ₁ b) none →
        reachedK K ζ₂ ξ₂ m b ∧ visitsK K (some b) (ζ₂ b) none := by
    rintro ζ₁ ζ₂ ξ₁ ξ₂ h1 h2 b ⟨⟨a, ha, v, hv, hav, hvb⟩, hb⟩
    have hb0 : b ≠ [] := by
      rcases Relation.ReflTransGen.cases_tail hvb with rfl | ⟨_, -, h⟩
      · exact hv
      · exact h.1
    refine ⟨⟨a, ha, v, hv, ?_, reflTransGen_starArcK_congr K ζ₁ ζ₂ h1 v b hv hvb⟩, ?_⟩
    · rw [← h2 a ha]
      exact hav
    · rw [← h1 b hb0]
      exact hb
  unfold curveK
  congr 1
  · congr 1
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ha, h⟩
      exact ⟨ha, hξ a ha ▸ h⟩
    · rintro ⟨ha, h⟩
      exact ⟨ha, (hξ a ha).symm ▸ h⟩
  · congr 1
    ext b
    exact ⟨hreach ζ ζ' ξ ξ' hζ hξ b, hreach ζ' ζ ξ' ξ hζ' hξ' b⟩
