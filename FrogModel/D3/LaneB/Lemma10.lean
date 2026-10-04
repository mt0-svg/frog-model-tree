module

public import FrogModel.D3.LaneA.Trials
public import FrogModel.D3.LaneA.Sym
public import FrogModel.D3.LaneB.Words

@[expose] public section

/-!
# Deep fresh trials (Lemma 11.5 of the paper), d = 3

The bound of Lemma 11.5, on the piece space of FrogModel/D3/LaneA/Trials.lean with
`j ≥ 1` entrants, `q = j + 1` initial frogs (trials `i = 0, ..., j`), a depth `1 ≤ D ≤ M` and the
sub-model height `L = M - D`.

Trial `i` succeeds (`Succ`) when the first vertex `v` at depth `D` of its piece 0 exists, is the
first vertex of no earlier trial (`Fresh`) and the sub-model at `v` counts at least `y` frogs.
`Fail i`: the trials before `i` all fail. With `pD = P(G_L(1) ≥ y)` and `c = 3^-D`:

- `fail_succ_le`: `P(Fail (i + 1)) ≤ P(Fail i) (1 - (2/3 - i c) pD)`. The sub-model at a fresh `v`
  reads coordinates no earlier trial reads, so it is independent of the past (`pr_inter_indep`);
  reaching depth `D` has probability at least `2/3` (`pr_reach_ge`) independently of the past, and
  the first vertex there is any given `v` with probability at most `c` (`pr_vI_le`), so it is one
  of the at most `i` earlier vertices with probability at most `i c`.
- `release_le`: `P(Fail i, Succ i, N < x) ≤ P(Fail i, Succ i) P(Bin(y, 3^-(D-1)) < x)`: the presences
  at `w` are at least the counted sub-model frogs whose next piece goes up `D - 1` levels
  (`presN_ge`), a binomial count on pieces nothing else reads (`infinitePi_encard_lt`).
- `pr_presN_lt`: `P(N < x) ≤ P(Fail (j + 1)) + P(Bin(y, 3^-(D-1)) < x)`, and `prod_trial_le`.

`lemma10_of` moves the bound to the closure with `curveLaw_succ`, taken as a hypothesis.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface FrogModel.ZeroOne

/-- The product of the failure bounds of the trials is at most the power of the last one. -/
theorem prod_trial_le (q : ℕ) (c p : ℝ) (hc : 0 ≤ c) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    ∏ i ∈ Finset.range q, (1 - (2 / 3 - (i : ℝ) * c) * p) ≤
      (1 - (2 / 3 - ((q : ℝ) - 1) * c) * p) ^ q := by
  have h0 : ∀ i ∈ Finset.range q, 0 ≤ 1 - (2 / 3 - (i : ℝ) * c) * p := fun i _ => by
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg i) hc) hp0]
  have h1 : ∀ i ∈ Finset.range q, 1 - (2 / 3 - (i : ℝ) * c) * p ≤
      1 - (2 / 3 - ((q : ℝ) - 1) * c) * p := fun i hi => by
    have hiq : (i : ℝ) + 1 ≤ q := by exact_mod_cast Finset.mem_range.1 hi
    have h2 : (i : ℝ) * c ≤ ((q : ℝ) - 1) * c := mul_le_mul_of_nonneg_right (by linarith) hc
    have h3 : (2 / 3 - ((q : ℝ) - 1) * c) * p ≤ (2 / 3 - (i : ℝ) * c) * p :=
      mul_le_mul_of_nonneg_right (by linarith) hp0
    linarith
  calc ∏ i ∈ Finset.range q, (1 - (2 / 3 - (i : ℝ) * c) * p)
      ≤ ∏ _i ∈ Finset.range q, (1 - (2 / 3 - ((q : ℝ) - 1) * c) * p) := Finset.prod_le_prod₀ h0 h1
    _ = (1 - (2 / 3 - ((q : ℝ) - 1) * c) * p) ^ q := by
      rw [Finset.prod_const, Finset.card_range]

/-! ### Words, coordinates, laws -/

/-- The words of length `D`. -/
def wordsD (D : ℕ) : Finset (Vertex 3) :=
  (Finset.univ : Finset (Fin D → Fin 3)).image List.ofFn

theorem mem_wordsD (D : ℕ) (v : Vertex 3) : v ∈ wordsD D ↔ v.length = D := by
  simp only [wordsD, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, rfl⟩
    simp
  · rintro rfl
    exact ⟨fun k => v.get k, List.ofFn_get v⟩

theorem eq_of_append_eq {u u' v v' : Vertex 3} (hl : v.length = v'.length)
    (h : u ++ v = u' ++ v') : v = v' :=
  (List.append_inj' h hl).2

theorem pieceMeasure_eval (p : PFrog × ℕ) (s : Set (ℕ → Step 3)) (hs : MeasurableSet s) :
    pieceMeasure {ω | ω p ∈ s} = LemmaR.seqLaw 3 s := by
  rw [show LemmaR.seqLaw 3 s = (pieceMeasure.map fun ω => ω p) s by
    rw [pieceMeasure, Measure.infinitePi_map_eval], Measure.map_apply (measurable_pi_apply p) hs]
  rfl

theorem toReal_inv_three_pow (n : ℕ) : ((3⁻¹ : ℝ≥0∞) ^ n).toReal = (3 : ℝ)⁻¹ ^ n := by
  simp [ENNReal.toReal_pow, ENNReal.toReal_inv]

/-- Independence on the piece space: an event insensitive to the coordinates in `T` and an event
reading only those. -/
theorem pr_inter_indep (T : Set (PFrog × ℕ)) (A B : Set PSpace) (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hAT : ∀ ω ω' : PSpace, (∀ p, p ∉ T → ω p = ω' p) → ω ∈ A → ω' ∈ A)
    (hBT : ∀ ω ω' : PSpace, (∀ p ∈ T, ω p = ω' p) → ω ∈ B → ω' ∈ B) :
    pieceMeasure.real (A ∩ B) = pieceMeasure.real A * pieceMeasure.real B := by
  simp only [measureReal_def]
  rw [show pieceMeasure (A ∩ B) = pieceMeasure A * pieceMeasure B from
    infinitePi_inter_of_dependsOn (LemmaR.seqLaw 3) T A B hA hB hAT hBT, ENNReal.toReal_mul]

/-! ### The trials -/

section Trials

variable (j D L y : ℕ)

/-- The first vertex at depth `D` of the initial frog `i`. -/
noncomputable def vI (i : ℕ) (ω : PSpace) : Option (Vertex 3) := firstD D (ω (initF j i, 0))

/-- The count of the sub-model of trial `i` at `v`. -/
noncomputable def subG (i : ℕ) (v : Vertex 3) (ω : PSpace) : ℕ∞ :=
  plantedG L 1 (subPaths ω (initF j i) v)

/-- `v` is the first vertex at depth `D` of none of the trials before `i`. -/
def Fresh (i : ℕ) (v : Vertex 3) (ω : PSpace) : Prop := ∀ i' < i, vI j D i' ω ≠ some v

/-- Trial `i` succeeds: its first vertex at depth `D` is new and its sub-model counts at least `y`
frogs. -/
def Succ (i : ℕ) (ω : PSpace) : Prop :=
  ∃ v, vI j D i ω = some v ∧ Fresh j D i v ω ∧ (y : ℕ∞) ≤ subG j L i v ω

/-- The trials before `i` all fail. -/
def Fail (i : ℕ) (ω : PSpace) : Prop := ∀ i' < i, ¬ Succ j D L y i' ω

theorem measurable_vI (i : ℕ) : Measurable (vI j D i) :=
  (measurable_firstD D).comp (measurable_pi_apply _)

theorem measurableSet_vI (i : ℕ) (v : Vertex 3) : MeasurableSet {ω | vI j D i ω = some v} :=
  measurable_vI j D i (measurableSet_singleton (some v))

theorem measurableSet_subG (i : ℕ) (v : Vertex 3) :
    MeasurableSet {ω | (y : ℕ∞) ≤ subG j L i v ω} :=
  ((measurable_plantedG L 1).comp (measurable_subPaths _ v)) (MeasurableSet.of_discrete)

theorem measurableSet_fresh (i : ℕ) (v : Vertex 3) : MeasurableSet {ω | Fresh j D i v ω} := by
  have : {ω | Fresh j D i v ω} = ⋂ i' ∈ Finset.range i, {ω | vI j D i' ω = some v}ᶜ := by
    ext ω
    simp [Fresh]
  rw [this]
  exact Finset.measurableSet_biInter _ fun i' _ => (measurableSet_vI j D i' v).compl

theorem measurableSet_succ (i : ℕ) : MeasurableSet {ω | Succ j D L y i ω} := by
  have : {ω | Succ j D L y i ω} = ⋃ v : Vertex 3,
      {ω | vI j D i ω = some v} ∩ {ω | Fresh j D i v ω} ∩ {ω | (y : ℕ∞) ≤ subG j L i v ω} := by
    ext ω
    simp [Succ, and_assoc]
  rw [this]
  exact MeasurableSet.iUnion fun v =>
    ((measurableSet_vI j D i v).inter (measurableSet_fresh j D i v)).inter
      (measurableSet_subG j L y i v)

theorem measurableSet_fail (i : ℕ) : MeasurableSet {ω | Fail j D L y i ω} := by
  have : {ω | Fail j D L y i ω} = ⋂ i' ∈ Finset.range i, {ω | Succ j D L y i' ω}ᶜ := by
    ext ω
    simp [Fail]
  rw [this]
  exact Finset.measurableSet_biInter _ fun i' _ => (measurableSet_succ j D L y i').compl

/-! ### Reading sets -/

theorem vI_congr {i : ℕ} {ω ω' : PSpace} (h : ω (initF j i, 0) = ω' (initF j i, 0)) :
    vI j D i ω = vI j D i ω' := by
  unfold vI
  rw [h]

theorem subG_congr {i : ℕ} {v : Vertex 3} {ω ω' : PSpace}
    (h : ∀ ψ, ω (subIdx (initF j i) v ψ) = ω' (subIdx (initF j i) v ψ)) :
    subG j L i v ω = subG j L i v ω' := by
  unfold subG
  congr 1
  funext ψ
  exact h ψ

theorem succ_congr {i : ℕ} {ω ω' : PSpace}
    (h0 : ∀ i' ≤ i, ω (initF j i', 0) = ω' (initF j i', 0))
    (hsub : ∀ v, vI j D i ω = some v →
      ∀ ψ, ω (subIdx (initF j i) v ψ) = ω' (subIdx (initF j i) v ψ))
    (h : Succ j D L y i ω) : Succ j D L y i ω' := by
  obtain ⟨v, hv, hfr, hG⟩ := h
  refine ⟨v, (vI_congr j D (h0 i le_rfl)).symm.trans hv, fun i' hi' => ?_, ?_⟩
  · rw [← vI_congr j D (h0 i' hi'.le)]
    exact hfr i' hi'
  · rw [← subG_congr j L (hsub v hv)]
    exact hG

theorem fail_congr {i : ℕ} {ω ω' : PSpace}
    (h0 : ∀ i' < i, ω (initF j i', 0) = ω' (initF j i', 0))
    (hsub : ∀ i' < i, ∀ v, vI j D i' ω' = some v →
      ∀ ψ, ω (subIdx (initF j i') v ψ) = ω' (subIdx (initF j i') v ψ))
    (h : Fail j D L y i ω) : Fail j D L y i ω' := by
  intro i' hi' hS
  refine h i' hi' (succ_congr j D L y (fun i'' hi'' => (h0 i'' (by omega)).symm)
    (fun v hv ψ => (hsub i' hi' v hv ψ).symm) hS)

/-- The depth-`D` vertex of a trial has length `D`. -/
theorem length_of_vI {i : ℕ} {ω : PSpace} {v : Vertex 3} (h : vI j D i ω = some v) :
    v.length = D := by
  obtain ⟨_, _, _, hD⟩ := firstD_spec D _ v h
  exact hD

end Trials

/-! ### One trial -/

section Step

variable {j D L y : ℕ}

theorem pr_vI_le (i : ℕ) (v : Vertex 3) :
    pieceMeasure.real {ω | vI j D i ω = some v} ≤ (3 : ℝ)⁻¹ ^ D := by
  rw [measureReal_def, show {ω : PSpace | vI j D i ω = some v} =
    {ω | ω (initF j i, 0) ∈ {x | firstD D x = some v}} from rfl,
    pieceMeasure_eval _ {x | firstD D x = some v}
      (measurable_firstD D (measurableSet_singleton (some v))),
    ← toReal_inv_three_pow]
  exact ENNReal.toReal_mono (by simp) (seqLaw_firstD_le D v)

theorem pr_reach_ge (i : ℕ) :
    2 / 3 ≤ pieceMeasure.real {ω | ReachD D (ω (initF j i, 0))} := by
  rw [measureReal_def, show {ω : PSpace | ReachD D (ω (initF j i, 0))} =
    {ω | ω (initF j i, 0) ∈ {x | ReachD D x}} from rfl,
    pieceMeasure_eval _ {x | ReachD D x} (measurableSet_reachD D)]
  have h := ENNReal.toReal_mono (by simp) (one_le_reachD D)
  rw [ENNReal.toReal_add (measure_ne_top _ _) (by simp)] at h
  simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h
  linarith

theorem pr_subG (i : ℕ) (v : Vertex 3) :
    pieceMeasure.real {ω | (y : ℕ∞) ≤ subG j L i v ω} = tailG L 1 y := by
  have hm : MeasurableSet {π : PFrog → ℕ → Step 3 | (y : ℕ∞) ≤ plantedG L 1 π} :=
    measurable_plantedG L 1 MeasurableSet.of_discrete
  rw [measureReal_def, tailG, ← map_subPaths (initF j i) v,
    Measure.map_apply (measurable_subPaths _ v) hm]
  rfl

/-- `(initF j i', 0)` is not a coordinate of the sub-model at `v`. -/
theorem init0_ne_sub (hD : 1 ≤ D) {v : Vertex 3} (hv : v.length = D) (i i' : ℕ) (ψ : PFrog) :
    (initF j i', 0) ≠ subIdx (initF j i) v ψ := by
  rcases ψ with (_ | k) | u
  · simp [subIdx]
  · simp [subIdx]
  · intro h
    exact initF_not_below hD hv u (Prod.mk.inj h).1

theorem sub_ne_sub_frog {i i' : ℕ} (hi : i ≤ j) (hi' : i' ≤ j) (hii' : i' ≠ i)
    {v v' : Vertex 3} (hv : v.length = D) (hv' : v'.length = D) (hvv' : v' ≠ v) (ψ ψ' : PFrog) :
    subIdx (initF j i') v' ψ' ≠ subIdx (initF j i) v ψ := by
  rcases ψ with (_ | k) | u <;> rcases ψ' with (_ | k') | u' <;> simp only [subIdx, ne_eq,
    Prod.mk.injEq, not_and]
  all_goals first
    | (intro h; exact absurd (initF_injective hi' hi h) hii')
    | (intro h; exact absurd (eq_of_append_eq (hv'.trans hv.symm)
        (Sum.inr_injective h)) hvv')
    | omega

end Step


/-! ### Measurability helpers -/

theorem measurableSet_setEq {Ω α : Type*} [MeasurableSpace Ω] [Countable α] (f : Ω → Set α)
    (hf : ∀ a, MeasurableSet {ω | a ∈ f ω}) (s : Set α) : MeasurableSet {ω | f ω = s} := by
  have : {ω | f ω = s} = ⋂ a, {ω | a ∈ f ω ↔ a ∈ s} := by
    ext ω
    simp [Set.ext_iff]
  rw [this]
  refine MeasurableSet.iInter fun a => ?_
  by_cases ha : a ∈ s
  · have : {ω | a ∈ f ω ↔ a ∈ s} = {ω | a ∈ f ω} := by
      ext ω
      simp [ha]
    rw [this]
    exact hf a
  · have : {ω | a ∈ f ω ↔ a ∈ s} = {ω | a ∈ f ω}ᶜ := by
      ext ω
      simp [ha]
    rw [this]
    exact (hf a).compl

theorem measurableSet_mem_subCounted (φ : PFrog) (v : Vertex 3) (L : ℕ) (ψ : PFrog) :
    MeasurableSet {ω : PSpace | ψ ∈ subCounted ω φ v L} :=
  measurable_subPaths φ v ((measurableSet_woken L 1 ψ).inter (measurableSet_reach ψ))

theorem measurableSet_cnt (S : Finset (PFrog × ℕ)) (H : Set (ℕ → Step 3)) (hH : MeasurableSet H)
    (x : ℕ) : MeasurableSet {ω : PSpace | ((S : Set (PFrog × ℕ)) ∩ {s | ω s ∈ H}).encard < x} :=
  (measurable_encard (fun ω : PSpace => (S : Set (PFrog × ℕ)) ∩ {s | ω s ∈ H}) fun s =>
    MeasurableSet.const (s ∈ (S : Set (PFrog × ℕ))) |>.inter
      (measurable_pi_apply s hH)) (MeasurableSet.of_discrete (s := Set.Iio (x : ℕ∞)))

theorem tailG_nonneg (L k x : ℕ) : 0 ≤ tailG L k x := ENNReal.toReal_nonneg

theorem tailG_le_one (L k x : ℕ) : tailG L k x ≤ 1 := by
  unfold tailG
  exact measureReal_le_one

/-! ### Coordinates of the trials and of the releases -/

section Coords

variable {j D : ℕ}

theorem init0_ne_cont (i i' : ℕ) (v : Vertex 3) (ψ : PFrog) :
    (initF j i', 0) ≠ contIdx (initF j i) v ψ := by
  rcases ψ with k | u <;> simp [contIdx]

theorem init0_ne_init0 {i i' : ℕ} (hi : i ≤ j) (hi' : i' ≤ j) (h : i' ≠ i) :
    (initF j i', 0) ≠ (initF j i, 0) := fun h' =>
  h (initF_injective hi' hi (Prod.mk.inj h').1)

theorem sub_ne_init0 (hD : 1 ≤ D) {v : Vertex 3} (hv : v.length = D) (i i' : ℕ) (ψ : PFrog) :
    subIdx (initF j i') v ψ ≠ (initF j i, 0) := fun h =>
  init0_ne_sub hD hv i' i ψ h.symm

theorem sub_ne_cont (hD : 1 ≤ D) {v : Vertex 3} (hv : v.length = D) (i i' : ℕ) (v' : Vertex 3)
    (ψ ψ' : PFrog) : subIdx (initF j i') v' ψ' ≠ contIdx (initF j i) v ψ := by
  rcases ψ with k | u <;> rcases ψ' with (_ | k') | u' <;>
    simp only [subIdx, contIdx, ne_eq, Prod.mk.injEq, not_and]
  all_goals first
    | omega
    | (intro h; exact absurd h (initF_not_below hD hv _))

theorem contIdx_injOn (i : ℕ) (v : Vertex 3) :
    Set.InjOn (contIdx (initF j i) v) {ψ | ψ = Sum.inl 0 ∨ ∃ u, ψ = Sum.inr u} := by
  rintro a (rfl | ⟨u, rfl⟩) b (rfl | ⟨u', rfl⟩) h <;> simp only [contIdx, Prod.mk.injEq] at h
  · rfl
  · omega
  · omega
  · rw [List.append_cancel_right (Sum.inr_injective h.1)]

end Coords

/-! ### One more trial -/

section Main

variable {j D L y : ℕ}

theorem fail_zero : {ω : PSpace | Fail j D L y 0 ω} = Set.univ := by
  ext ω
  simp [Fail]

theorem succ_set_eq (i : ℕ) :
    {ω : PSpace | Fail j D L y i ω} ∩ {ω | Succ j D L y i ω} = ⋃ v ∈ wordsD D,
      ({ω | Fail j D L y i ω} ∩ {ω | vI j D i ω = some v} ∩ {ω | Fresh j D i v ω}) ∩
        {ω | (y : ℕ∞) ≤ subG j L i v ω} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hFω, v, hv, hfr, hG⟩
    exact ⟨v, (mem_wordsD D v).2 (length_of_vI j D hv), ⟨⟨hFω, hv⟩, hfr⟩, hG⟩
  · rintro ⟨v, -, ⟨⟨hFω, hv⟩, hfr⟩, hG⟩
    exact ⟨hFω, v, hv, hfr, hG⟩

theorem disjoint_vI (i : ℕ) (E : Vertex 3 → Set PSpace)
    (hE : ∀ v, E v ⊆ {ω | vI j D i ω = some v}) (s : Finset (Vertex 3)) :
    Set.PairwiseDisjoint (↑s) E := by
  intro v _ v' _ hvv'
  refine Set.disjoint_left.2 fun ω h h' => hvv' ?_
  have h1 := hE v h
  have h2 := hE v' h'
  simp only [Set.mem_ofPred_eq] at h1 h2
  exact Option.some.inj (h1.symm.trans h2)

/-- The failure of the trials before `i` does not read the coordinate `(initF j i, 0)`. -/
theorem fail_insens_init (hD : 1 ≤ D) {i : ℕ} (hi : i ≤ j) (ω ω' : PSpace)
    (hag : ∀ p, p ∉ ({(initF j i, 0)} : Set (PFrog × ℕ)) → ω p = ω' p) :
    (∀ i' < i, ω (initF j i', 0) = ω' (initF j i', 0)) ∧
      (∀ i' < i, ∀ v, vI j D i' ω' = some v →
        ∀ ψ, ω (subIdx (initF j i') v ψ) = ω' (subIdx (initF j i') v ψ)) := by
  refine ⟨fun i' hi' => hag _ fun h => init0_ne_init0 hi (by omega) (by omega) h, ?_⟩
  intro i' _ v hv ψ
  exact hag _ fun h => sub_ne_init0 hD (length_of_vI j D hv) i i' ψ h

/-- **One more trial**: `P(Fail (i + 1)) ≤ P(Fail i) (1 - (2/3 - i 3^-D) pD)`. -/
theorem fail_succ_le (hD : 1 ≤ D) (i : ℕ) (hi : i ≤ j) :
    pieceMeasure.real {ω | Fail j D L y (i + 1) ω} ≤
      pieceMeasure.real {ω | Fail j D L y i ω} *
        (1 - (2 / 3 - (i : ℝ) * (3 : ℝ)⁻¹ ^ D) * tailG L 1 y) := by
  classical
  set F := {ω : PSpace | Fail j D L y i ω} with hFdef
  have hF : MeasurableSet F := measurableSet_fail j D L y i
  set c : ℝ := (3 : ℝ)⁻¹ ^ D with hc
  set pD := tailG L 1 y with hpD
  have hpD0 : 0 ≤ pD := tailG_nonneg L 1 y
  have hc0 : 0 ≤ c := by positivity
  set V : ℕ → Vertex 3 → Set PSpace := fun i' v => {ω | vI j D i' ω = some v} with hVdef
  have hV : ∀ i' v, MeasurableSet (V i' v) := fun i' v => measurableSet_vI j D i' v
  set A : Vertex 3 → Set PSpace := fun v => F ∩ V i v ∩ {ω | Fresh j D i v ω} with hAdef
  set B : Vertex 3 → Set PSpace := fun v => {ω | (y : ℕ∞) ≤ subG j L i v ω} with hBdef
  have hA : ∀ v, MeasurableSet (A v) := fun v =>
    (hF.inter (hV i v)).inter (measurableSet_fresh j D i v)
  have hB : ∀ v, MeasurableSet (B v) := fun v => measurableSet_subG j L y i v
  set W := wordsD D with hW
  -- (a) the success of trial `i` as a disjoint union over its vertex
  have hPsucc : pieceMeasure.real (F ∩ {ω | Succ j D L y i ω}) =
      ∑ v ∈ W, pieceMeasure.real (A v ∩ B v) := by
    rw [succ_set_eq i, measureReal_biUnion_finset
      (disjoint_vI i _ (fun v ω h => h.1.1.2) W) fun v _ => (hA v).inter (hB v)]
  -- (b) the sub-model at a fresh vertex is independent of the past
  have hAB : ∀ v ∈ W, pieceMeasure.real (A v ∩ B v) = pieceMeasure.real (A v) * pD := by
    intro v hv
    have hvD := (mem_wordsD D v).1 hv
    rw [pr_inter_indep (Set.range (subIdx (initF j i) v)) (A v) (B v) (hA v) (hB v), pr_subG i v]
    · rintro ω ω' hag ⟨⟨hFω, hvω⟩, hfr⟩
      have h0 : ∀ i'', ω (initF j i'', 0) = ω' (initF j i'', 0) := fun i'' =>
        hag _ fun ⟨ψ, hψ⟩ => init0_ne_sub hD hvD i i'' ψ hψ.symm
      have hvI : ∀ i'', vI j D i'' ω = vI j D i'' ω' := fun i'' => vI_congr j D (h0 i'')
      refine ⟨⟨fail_congr j D L y (fun i' _ => h0 i') ?_ hFω, ?_⟩, fun i' hi' => ?_⟩
      · intro i' hi' v' hv' ψ
        apply hag
        rintro ⟨ψ', hψ'⟩
        have hv'D := length_of_vI j D hv'
        have hvv' : v' ≠ v := fun h => hfr i' hi' ((hvI i').trans (h ▸ hv'))
        exact sub_ne_sub_frog (i := i) (i' := i') hi (by omega) (by omega) hvD hv'D hvv' ψ' ψ
          hψ'.symm
      · show vI j D i ω' = some v
        rw [← hvI i]
        exact hvω
      · show vI j D i' ω' ≠ some v
        rw [← hvI i']
        exact hfr i' hi'
    · intro ω ω' hag hBω
      show (y : ℕ∞) ≤ subG j L i v ω'
      rw [← subG_congr j L fun ψ => hag _ ⟨ψ, rfl⟩]
      exact hBω
  -- (c) reaching depth `D` is independent of the past
  have hreach : pieceMeasure.real (F ∩ {ω | ReachD D (ω (initF j i, 0))}) =
      ∑ v ∈ W, pieceMeasure.real (F ∩ V i v) := by
    have hset : F ∩ {ω | ReachD D (ω (initF j i, 0))} = ⋃ v ∈ W, F ∩ V i v := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, hVdef]
      constructor
      · rintro ⟨hFω, hr⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((firstD_isSome_iff D _).2 hr)
        exact ⟨v, (mem_wordsD D v).2 (length_of_vI j D hv), hFω, hv⟩
      · rintro ⟨v, -, hFω, hv⟩
        refine ⟨hFω, ?_⟩
        by_contra hr
        have := (firstD_eq_none_iff D _).2 hr
        unfold vI at hv
        rw [this] at hv
        cases hv
    rw [hset, measureReal_biUnion_finset (disjoint_vI i _ (fun v ω h => h.2) W)
      fun v _ => hF.inter (hV i v)]
  have hreach2 : pieceMeasure.real (F ∩ {ω | ReachD D (ω (initF j i, 0))}) =
      pieceMeasure.real F * pieceMeasure.real {ω | ReachD D (ω (initF j i, 0))} := by
    refine pr_inter_indep {(initF j i, 0)} F _ hF
      ((measurableSet_reachD D).preimage (measurable_pi_apply _)) ?_ ?_
    · intro ω ω' hag hFω
      obtain ⟨h0, hsub⟩ := fail_insens_init hD hi ω ω' hag
      exact fail_congr j D L y h0 hsub hFω
    · intro ω ω' hag h
      show ReachD D (ω' (initF j i, 0))
      rw [← hag _ rfl]
      exact h
  -- (d) the vertex of trial `i` is an earlier one with probability at most `i c`
  set NF : Vertex 3 → Set PSpace := fun v => F ∩ {ω | ¬ Fresh j D i v ω} with hNFdef
  have hNF : ∀ v, MeasurableSet (NF v) := fun v => hF.inter (measurableSet_fresh j D i v).compl
  have hAsplit : ∀ v, pieceMeasure.real (A v) =
      pieceMeasure.real (F ∩ V i v) - pieceMeasure.real (NF v ∩ V i v) := by
    intro v
    have h := measureReal_inter_add_sdiff (μ := pieceMeasure) (s := F ∩ V i v)
      (measurableSet_fresh j D i v)
    have hset : (F ∩ V i v) \ {ω | Fresh j D i v ω} = NF v ∩ V i v := by
      ext ω
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, hNFdef]
      tauto
    rw [hset] at h
    linarith
  have hNFV : ∀ v ∈ W, pieceMeasure.real (NF v ∩ V i v) ≤ pieceMeasure.real (NF v) * c := by
    intro v _
    rw [pr_inter_indep {(initF j i, 0)} (NF v) (V i v) (hNF v) (hV i v)]
    · exact mul_le_mul_of_nonneg_left (pr_vI_le i v) measureReal_nonneg
    · rintro ω ω' hag ⟨hFω, hfr⟩
      obtain ⟨h0, hsub⟩ := fail_insens_init hD hi ω ω' hag
      refine ⟨fail_congr j D L y h0 hsub hFω, fun hfr' => hfr fun i' hi' => ?_⟩
      show vI j D i' ω ≠ some v
      rw [vI_congr j D (h0 i' hi')]
      exact hfr' i' hi'
    · intro ω ω' hag h
      show vI j D i ω' = some v
      rw [← vI_congr j D (hag _ rfl)]
      exact h
  have hNFsum : ∑ v ∈ W, pieceMeasure.real (NF v) ≤ i * pieceMeasure.real F := by
    have h1 : ∀ v, NF v = ⋃ i' ∈ Finset.range i, F ∩ V i' v := by
      intro v
      ext ω
      simp only [hNFdef, hVdef, Fresh, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion,
        Finset.mem_range, exists_prop, not_forall, not_not]
      constructor
      · rintro ⟨hFω, i', hi', h⟩
        exact ⟨i', hi', hFω, h⟩
      · rintro ⟨i', hi', hFω, h⟩
        exact ⟨hFω, i', hi', h⟩
    calc ∑ v ∈ W, pieceMeasure.real (NF v)
        ≤ ∑ v ∈ W, ∑ i' ∈ Finset.range i, pieceMeasure.real (F ∩ V i' v) :=
          Finset.sum_le_sum fun v _ => by
            rw [h1 v]
            exact measureReal_biUnion_finset_le _ _
      _ = ∑ i' ∈ Finset.range i, ∑ v ∈ W, pieceMeasure.real (F ∩ V i' v) := Finset.sum_comm
      _ ≤ ∑ _i' ∈ Finset.range i, pieceMeasure.real F := Finset.sum_le_sum fun i' _ => by
          rw [← measureReal_biUnion_finset (disjoint_vI i' _ (fun v ω h => h.2) W)
            fun v _ => hF.inter (hV i' v)]
          exact measureReal_mono (Set.iUnion₂_subset fun v _ => Set.inter_subset_left) (measure_ne_top _ _)
      _ = i * pieceMeasure.real F := by simp
  -- (e) combine
  have hsum : ∑ v ∈ W, pieceMeasure.real (A v) ≥
      2 / 3 * pieceMeasure.real F - c * (i * pieceMeasure.real F) := by
    have h1 : ∑ v ∈ W, pieceMeasure.real (A v) = ∑ v ∈ W, pieceMeasure.real (F ∩ V i v) -
        ∑ v ∈ W, pieceMeasure.real (NF v ∩ V i v) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => hAsplit v
    have h2 : ∑ v ∈ W, pieceMeasure.real (NF v ∩ V i v) ≤ c * (i * pieceMeasure.real F) := by
      calc ∑ v ∈ W, pieceMeasure.real (NF v ∩ V i v)
          ≤ ∑ v ∈ W, pieceMeasure.real (NF v) * c := Finset.sum_le_sum hNFV
        _ = c * ∑ v ∈ W, pieceMeasure.real (NF v) := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ c * (i * pieceMeasure.real F) := mul_le_mul_of_nonneg_left hNFsum hc0
    have h3 : 2 / 3 * pieceMeasure.real F ≤ ∑ v ∈ W, pieceMeasure.real (F ∩ V i v) := by
      rw [← hreach, hreach2, mul_comm]
      exact mul_le_mul_of_nonneg_left (pr_reach_ge i) measureReal_nonneg
    linarith
  have hlow : pD * (2 / 3 * pieceMeasure.real F - c * (i * pieceMeasure.real F)) ≤
      pieceMeasure.real (F ∩ {ω | Succ j D L y i ω}) := by
    rw [hPsucc, Finset.sum_congr rfl hAB, ← Finset.sum_mul, mul_comm pD]
    exact mul_le_mul_of_nonneg_right hsum hpD0
  have hsplit := measureReal_inter_add_sdiff (μ := pieceMeasure) (s := F)
    (measurableSet_succ j D L y i)
  have hset : {ω | Fail j D L y (i + 1) ω} = F \ {ω | Succ j D L y i ω} := by
    ext ω
    simp only [hFdef, Fail, Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · intro h
      exact ⟨fun i' hi' => h i' (by omega), h i (by omega)⟩
    · rintro ⟨h1, h2⟩ i' hi'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | rfl
      · exact h1 i' h
      · exact h2
  rw [hset]
  nlinarith

/-- `P(Fail i) ≤ ∏_{i' < i} (1 - (2/3 - i' 3^-D) pD)`. -/
theorem fail_le_prod (hD : 1 ≤ D) (i : ℕ) (hi : i ≤ j + 1) :
    pieceMeasure.real {ω | Fail j D L y i ω} ≤
      ∏ i' ∈ Finset.range i, (1 - (2 / 3 - (i' : ℝ) * (3 : ℝ)⁻¹ ^ D) * tailG L 1 y) := by
  induction i with
  | zero => simp [fail_zero]
  | succ i ih =>
    rw [Finset.prod_range_succ]
    have hp0 := tailG_nonneg L 1 y
    have hp1 := tailG_le_one L 1 y
    have hc : 0 ≤ (i : ℝ) * (3 : ℝ)⁻¹ ^ D := by positivity
    have hf : 0 ≤ 1 - (2 / 3 - (i : ℝ) * (3 : ℝ)⁻¹ ^ D) * tailG L 1 y := by nlinarith
    exact (fail_succ_le hD i (by omega)).trans (mul_le_mul_of_nonneg_right (ih (by omega)) hf)

end Main

/-! ### The release -/

section Release

variable {M j D y : ℕ}

/-- The candidates for the counted frogs of a sub-model of height `L`. -/
def candF (L : ℕ) : Finset PFrog := insert (Sum.inl 0) ((wordsLe L).image Sum.inr)

theorem subCounted_subset (ω : PSpace) (φ : PFrog) (v : Vertex 3) (L : ℕ) :
    subCounted ω φ v L ⊆ ↑(candF L) := by
  intro ψ hψ
  simp only [candF, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
    Finset.mem_coe, mem_wordsLe]
  rcases ψ with k | u
  · left
    rw [woken_one_inl hψ.1]
  · right
    exact ⟨u, woken_inr_length hψ.1, rfl⟩

theorem candF_shape (L : ℕ) :
    (↑(candF L) : Set PFrog) ⊆ {ψ | ψ = Sum.inl 0 ∨ ∃ u, ψ = Sum.inr u} := by
  intro ψ hψ
  simp only [candF, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
    Finset.mem_coe] at hψ
  rcases hψ with rfl | ⟨u, -, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨u, rfl⟩

/-- The law of the release count: binomial. -/
theorem pr_cnt (i : ℕ) (v : Vertex 3) (L : ℕ) (S : Finset PFrog) (hS : S ⊆ candF L) (x : ℕ) :
    pieceMeasure.real {ω | ((↑(S.image (contIdx (initF j i) v)) : Set (PFrog × ℕ)) ∩
        {s | ω s ∈ {a | HitsDown (D - 1) a}}).encard < x} =
      binLt S.card ((3 : ℝ)⁻¹ ^ (D - 1)) x := by
  have hinj : Set.InjOn (contIdx (initF j i) v) ↑S := (contIdx_injOn i v).mono
    ((Finset.coe_subset.2 hS).trans (candF_shape L))
  rw [measureReal_def, pieceMeasure,
    infinitePi_encard_lt (LemmaR.seqLaw 3) _ (measurableSet_hitsDown (D - 1)),
    Finset.card_image_of_injOn hinj, seqLaw_hitsDown, toReal_inv_three_pow]

/-- **The release**: on the success of trial `i`, fewer than `x` presences at `w` has
probability at most `P(Bin(y, 3^-(D-1)) < x)`. -/
theorem release_le (hj : 1 ≤ j) (hD : 1 ≤ D) (hDM : D ≤ M) (i : ℕ) (_hi : i ≤ j) (x : ℕ) :
    pieceMeasure.real ({ω | Fail j D (M - D) y i ω} ∩ {ω | Succ j D (M - D) y i ω} ∩
        {ω | presN M j (glueP j D ω) < x}) ≤
      pieceMeasure.real ({ω | Fail j D (M - D) y i ω} ∩ {ω | Succ j D (M - D) y i ω}) *
        binLt y ((3 : ℝ)⁻¹ ^ (D - 1)) x := by
  classical
  set L := M - D with hL
  set F := {ω : PSpace | Fail j D L y i ω} with hFdef
  have hF : MeasurableSet F := measurableSet_fail j D L y i
  set φ := initF j i with hφ
  set p : ℝ := (3 : ℝ)⁻¹ ^ (D - 1) with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set b := binLt y p x with hb
  have hb0 : 0 ≤ b := binLt_nonneg y x p hp0 hp1
  set H : Set (ℕ → Step 3) := {a | HitsDown (D - 1) a} with hH
  have hHm : MeasurableSet H := measurableSet_hitsDown (D - 1)
  set W := wordsD D with hW
  set A : Vertex 3 → Set PSpace := fun v =>
    F ∩ {ω | vI j D i ω = some v} ∩ {ω | Fresh j D i v ω} with hAdef
  set B : Vertex 3 → Set PSpace := fun v => {ω | (y : ℕ∞) ≤ subG j L i v ω} with hBdef
  set C : Vertex 3 → Finset PFrog → Set PSpace := fun v S =>
    {ω | subCounted ω φ v L = ↑S} with hCdef
  set cnt : Vertex 3 → Finset PFrog → Set PSpace := fun v S =>
    {ω | ((↑(S.image (contIdx φ v)) : Set (PFrog × ℕ)) ∩ {s | ω s ∈ H}).encard < x}
    with hcntdef
  set Ss : Finset (Finset PFrog) := (candF L).powerset.filter fun S => y ≤ S.card with hSs
  have hA : ∀ v, MeasurableSet (A v) := fun v =>
    (hF.inter (measurableSet_vI j D i v)).inter (measurableSet_fresh j D i v)
  have hC : ∀ v S, MeasurableSet (C v S) := fun v S =>
    measurableSet_setEq _ (measurableSet_mem_subCounted φ v L) _
  have hcnt : ∀ v S, MeasurableSet (cnt v S) := fun v S => measurableSet_cnt _ H hHm x
  -- the event lies in the union of the releases
  have hincl : F ∩ {ω | Succ j D L y i ω} ∩ {ω | presN M j (glueP j D ω) < x} ⊆
      ⋃ v ∈ W, ⋃ S ∈ Ss, (A v ∩ C v S) ∩ cnt v S := by
    rintro ω ⟨⟨hFω, v, hv, hfr, hG⟩, hN⟩
    set S := (candF L).filter fun ψ => ψ ∈ subCounted ω φ v L with hSdef
    have hSeq : subCounted ω φ v L = ↑S := by
      ext ψ
      simp only [hSdef, Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨subCounted_subset ω φ v L h, h⟩, fun h => h.2⟩
    have hcard : y ≤ S.card := by
      have : (y : ℕ∞) ≤ (S.card : ℕ∞) := by
        rw [← Set.encard_coe_eq_coe_finsetCard, ← hSeq]
        exact hG
      exact_mod_cast this
    have hinj : Set.InjOn (contIdx φ v) (↑S ∩ {ψ | ω (contIdx φ v ψ) ∈ H}) :=
      (contIdx_injOn i v).mono (Set.inter_subset_left.trans
        ((Finset.coe_subset.2 (Finset.filter_subset _ _)).trans (candF_shape L)))
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨v, (mem_wordsD D v).2 (length_of_vI j D hv), S, ?_, ⟨⟨⟨hFω, hv⟩, hfr⟩, hSeq⟩, ?_⟩
    · simp only [hSs, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.filter_subset _ _, hcard⟩
    · show ((↑(S.image (contIdx φ v)) : Set (PFrog × ℕ)) ∩ {s | ω s ∈ H}).encard < x
      calc ((↑(S.image (contIdx φ v)) : Set (PFrog × ℕ)) ∩ {s | ω s ∈ H}).encard
          = (↑S ∩ {ψ | ω (contIdx φ v ψ) ∈ H}).encard := by
            rw [Finset.coe_image, ← Set.image_inter_preimage]
            exact hinj.encard_image
        _ = (subCounted ω φ v L ∩ {ψ | HitsDown (D - 1) (ω (contIdx φ v ψ))}).encard := by
            rw [hSeq]
            rfl
        _ ≤ presN M j (glueP j D ω) := presN_ge hj hD hDM hv
        _ < x := hN
  -- each release is independent of what decided it
  have hterm : ∀ v ∈ W, ∀ S ∈ Ss,
      pieceMeasure.real ((A v ∩ C v S) ∩ cnt v S) ≤ pieceMeasure.real (A v ∩ C v S) * b := by
    intro v hv S hS
    have hvD := (mem_wordsD D v).1 hv
    simp only [hSs, Finset.mem_filter, Finset.mem_powerset] at hS
    rw [pr_inter_indep (Set.range (contIdx φ v)) (A v ∩ C v S) (cnt v S) ((hA v).inter (hC v S))
      (hcnt v S)]
    · refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
      rw [hcntdef, pr_cnt i v L S hS.1 x]
      exact binLt_anti hS.2 x p hp0 hp1
    · rintro ω ω' hag ⟨⟨⟨hFω, hvω⟩, hfr⟩, hCω⟩
      have h0 : ∀ i'', ω (initF j i'', 0) = ω' (initF j i'', 0) := fun i'' =>
        hag _ fun ⟨ψ, hψ⟩ => init0_ne_cont i i'' v ψ hψ.symm
      have hsub : ∀ i' v' ψ, ω (subIdx (initF j i') v' ψ) = ω' (subIdx (initF j i') v' ψ) :=
        fun i' v' ψ => hag _ fun ⟨ψ', hψ'⟩ => sub_ne_cont hD hvD i i' v' ψ' ψ hψ'.symm
      have hsp : subPaths ω φ v = subPaths ω' φ v := funext fun ψ => hsub i v ψ
      refine ⟨⟨⟨fail_congr j D L y (fun i' _ => h0 i') (fun i' _ v' _ ψ => hsub i' v' ψ) hFω,
        ?_⟩, fun i' hi' => ?_⟩, ?_⟩
      · show vI j D i ω' = some v
        rw [← vI_congr j D (h0 i)]
        exact hvω
      · show vI j D i' ω' ≠ some v
        rw [← vI_congr j D (h0 i')]
        exact hfr i' hi'
      · show subCounted ω' φ v L = ↑S
        unfold subCounted
        rw [← hsp]
        exact hCω
    · intro ω ω' hag hω
      show ((↑(S.image (contIdx φ v)) : Set (PFrog × ℕ)) ∩ {s | ω' s ∈ H}).encard < x
      have : ((↑(S.image (contIdx φ v)) : Set (PFrog × ℕ)) ∩ {s | ω' s ∈ H}) =
          ((↑(S.image (contIdx φ v)) : Set (PFrog × ℕ)) ∩ {s | ω s ∈ H}) := by
        ext s
        simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hs, h⟩
          obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hs
          exact ⟨hs, by rw [hag _ ⟨ψ, rfl⟩]; exact h⟩
        · rintro ⟨hs, h⟩
          obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hs
          exact ⟨hs, by rw [← hag _ ⟨ψ, rfl⟩]; exact h⟩
      rw [this]
      exact hω
  -- the releases of a trial are disjoint and lie in its success
  have hsucc : ∑ v ∈ W, ∑ S ∈ Ss, pieceMeasure.real (A v ∩ C v S) ≤
      pieceMeasure.real (F ∩ {ω | Succ j D L y i ω}) := by
    rw [succ_set_eq i, measureReal_biUnion_finset
      (disjoint_vI i _ (fun v ω h => h.1.1.2) W)
      fun v _ => (hA v).inter (measurableSet_subG j L y i v)]
    refine Finset.sum_le_sum fun v _ => ?_
    have hdS : Set.PairwiseDisjoint (↑Ss) (fun S => A v ∩ C v S) := by
      intro S _ S' _ hSS'
      refine Set.disjoint_left.2 fun ω h h' => hSS' ?_
      exact Finset.coe_inj.1 (h.2.symm.trans h'.2)
    rw [← measureReal_biUnion_finset hdS fun S _ => (hA v).inter (hC v S)]
    refine measureReal_mono (Set.iUnion₂_subset fun S hS => ?_) (measure_ne_top _ _)
    rintro ω ⟨hAω, hCω⟩
    simp only [hSs, Finset.mem_filter, Finset.mem_powerset] at hS
    refine ⟨hAω, ?_⟩
    show (y : ℕ∞) ≤ subG j L i v ω
    unfold subG
    show (y : ℕ∞) ≤ (subCounted ω φ v L).encard
    rw [hCω, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hS.2
  calc pieceMeasure.real (F ∩ {ω | Succ j D L y i ω} ∩ {ω | presN M j (glueP j D ω) < x})
      ≤ pieceMeasure.real (⋃ v ∈ W, ⋃ S ∈ Ss, (A v ∩ C v S) ∩ cnt v S) :=
        measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ v ∈ W, pieceMeasure.real (⋃ S ∈ Ss, (A v ∩ C v S) ∩ cnt v S) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ v ∈ W, ∑ S ∈ Ss, pieceMeasure.real ((A v ∩ C v S) ∩ cnt v S) :=
        Finset.sum_le_sum fun v _ => measureReal_biUnion_finset_le _ _
    _ ≤ ∑ v ∈ W, ∑ S ∈ Ss, pieceMeasure.real (A v ∩ C v S) * b :=
        Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun S hS => hterm v hv S hS
    _ = (∑ v ∈ W, ∑ S ∈ Ss, pieceMeasure.real (A v ∩ C v S)) * b := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun v _ => (Finset.sum_mul _ _ _).symm
    _ ≤ pieceMeasure.real (F ∩ {ω | Succ j D L y i ω}) * b :=
        mul_le_mul_of_nonneg_right hsucc hb0

/-- `P(N < x) ≤ P(all trials fail) + P(Bin(y, 3^-(D-1)) < x)` on the piece space. -/
theorem pr_presN_lt (hj : 1 ≤ j) (hD : 1 ≤ D) (hDM : D ≤ M) (x : ℕ) :
    pieceMeasure.real {ω | presN M j (glueP j D ω) < x} ≤
      pieceMeasure.real {ω | Fail j D (M - D) y (j + 1) ω} +
        binLt y ((3 : ℝ)⁻¹ ^ (D - 1)) x := by
  classical
  set L := M - D with hL
  set b := binLt y ((3 : ℝ)⁻¹ ^ (D - 1)) x with hb
  have hb0 : 0 ≤ b := binLt_nonneg y x _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  set N := {ω : PSpace | presN M j (glueP j D ω) < x} with hNdef
  set E : ℕ → Set PSpace := fun i => {ω | Fail j D L y i ω} ∩ {ω | Succ j D L y i ω} with hEdef
  have hE : ∀ i, MeasurableSet (E i) := fun i =>
    (measurableSet_fail j D L y i).inter (measurableSet_succ j D L y i)
  have hincl : N ⊆ {ω | Fail j D L y (j + 1) ω} ∪ ⋃ i ∈ Finset.range (j + 1), E i ∩ N := by
    intro ω hω
    by_cases hf : Fail j D L y (j + 1) ω
    · exact Or.inl hf
    · right
      have hex : ∃ i, i < j + 1 ∧ Succ j D L y i ω := by
        by_contra h
        push Not at h
        exact hf fun i hi => h i hi
      have hi := Nat.find_spec hex
      simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
      exact ⟨Nat.find hex, hi.1, ⟨fun i' hi' hs => Nat.find_min hex hi' ⟨by omega, hs⟩, hi.2⟩,
        hω⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (j + 1))) E := by
    intro i _ i' _ hii'
    refine Set.disjoint_left.2 fun ω h h' => ?_
    rcases lt_or_gt_of_ne hii' with hlt | hlt
    · exact h'.1 i hlt h.2
    · exact h.1 i' hlt h'.2
  have hsumE : ∑ i ∈ Finset.range (j + 1), pieceMeasure.real (E i) ≤ 1 := by
    rw [← measureReal_biUnion_finset hdisj fun i _ => hE i]
    exact measureReal_le_one
  calc pieceMeasure.real N
      ≤ pieceMeasure.real ({ω | Fail j D L y (j + 1) ω} ∪ ⋃ i ∈ Finset.range (j + 1), E i ∩ N) :=
        measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ pieceMeasure.real {ω | Fail j D L y (j + 1) ω} +
          pieceMeasure.real (⋃ i ∈ Finset.range (j + 1), E i ∩ N) := measureReal_union_le _ _
    _ ≤ pieceMeasure.real {ω | Fail j D L y (j + 1) ω} +
          ∑ i ∈ Finset.range (j + 1), pieceMeasure.real (E i ∩ N) := by
        gcongr
        exact measureReal_biUnion_finset_le _ _
    _ ≤ pieceMeasure.real {ω | Fail j D L y (j + 1) ω} +
          ∑ i ∈ Finset.range (j + 1), pieceMeasure.real (E i) * b := by
        gcongr with i hi
        exact release_le hj hD hDM i (by simp only [Finset.mem_range] at hi; omega) x
    _ ≤ pieceMeasure.real {ω | Fail j D L y (j + 1) ω} + 1 * b := by
        rw [← Finset.sum_mul]
        gcongr
    _ = pieceMeasure.real {ω | Fail j D L y (j + 1) ω} + b := by ring

end Release

/-! ### Lemma 11.5 of the paper -/

/-- **Lemma 11.5 of the paper** (deep fresh trials), with `curveLaw_succ` as a hypothesis. -/
theorem lemma10_of (hcurve : curveLaw_succ) : lemma10 := by
  intro m q D x y hq hD1 hDm hx hy
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  have hj : 1 ≤ j := by omega
  have htr : closProb m {z | closN (j + 1) z.1 z.2 < x} =
      pieceMeasure.real {ω | presN (m + 1) j (glueP j D ω) < x} := by
    set S : Set ((ℕ → ℕ∞) × (ℕ → ℕ∞)) := {p | p.2 j < x} with hSdef
    have hS : MeasurableSet S :=
      ((measurable_pi_apply j).comp measurable_snd) (MeasurableSet.of_discrete (s := Set.Iio _))
    have h1 : {z : ClosSample | closN (j + 1) z.1 z.2 < x} =
        (fun z : ClosSample => (closCurve z.1 z.2, closNCurve z.1 z.2)) ⁻¹' S := by
      ext z
      simp [hSdef, closNCurve, show j ≠ 0 by omega]
    have h2 : {ω : PSpace | presN (m + 1) j (glueP j D ω) < x} = glueP j D ⁻¹'
        ((fun π => (plantedCurve (m + 1) π, presCurve (m + 1) π)) ⁻¹' S) := by
      ext ω
      simp [hSdef, presCurve]
    rw [closProb, h1, ← Measure.map_apply measurable_closPair_proof hS, ← hcurve m,
      Measure.map_apply (measurable_plantedPair_proof (m + 1)) hS, ← map_glueP j D,
      Measure.map_apply (measurable_glueP j D) ((measurable_plantedPair_proof (m + 1)) hS), h2]
    rfl
  rw [htr]
  refine (pr_presN_lt (y := y) hj hD1 hDm x).trans ?_
  gcongr ?_ + _
  have hp0 := tailG_nonneg (m + 1 - D) 1 y
  have hp1 := tailG_le_one (m + 1 - D) 1 y
  exact (fail_le_prod hD1 (j + 1) le_rfl).trans
    (prod_trial_le (j + 1) _ _ (by positivity) hp0 hp1)

end FrogModel.D3.LaneA
