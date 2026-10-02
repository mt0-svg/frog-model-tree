module

public import FrogModel.Pieces.Stage
public import FrogModel.Pieces.Glue

@[expose] public section

/-!
# Theorem A (Theorem 2.2 of the paper, proved in its Section 3)

`theoremA`: if `x = E X < 1` then `E V ≤ (d + 1) x / (1 - x)`, with `V` the number of visits to the
root; `transient_of_meanX_lt_one`: then the frog model on the `d`-ary tree is transient.

- Stages: `Stage.start_mem_stages`, `Stage.succ_mem_stages`, `Stage.stages_mono`, `stage_mono`.
- Lemma 3.3 of the paper: a frog reachable from the root frog has its segment `0` in a stage
  (`reach_mem_stage`, through `walk_glue_segAt` and `stage_of_walk_glue`), its closed segments
  give its returns (`segClosed_of_cutSum`, `mem_stage_of_closed`), and a segment `(u, k + 1)` of a
  stage lies in some `Z_(i+1)` (`mem_closure_of_ne_zero`, `exists_enterSeg`); so the visits are
  the image of the union of the `Z_(i+1)` (`visits_subset`) and `V ≤ Σ_i R_(i+1)` pointwise
  (`encard_visits_glue_le`).
- Lemma 3.6: the children of the root entered from `Z_i` are new at stage `i + 1`
  (`child_mem_stage`), so `Σ_i W_(i+1) ≤ d` (`sum_stageW_le`).
- Integration: `R_0 = 1` (`enterSeg_zero`, `stageR_zero`, `lintegral_stageR_zero`), the law of the
  glued pieces (`lintegral_visits_eq`, through `map_glue`), `sum_lintegral_stageW_le`, and the
  summed recursion `TheoremA.sum_bound` with `lemma31` (Lemma 3.5).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open FrogModel

theorem FrogModel.Stage.start_mem_stages {ι P : Type*} (arc : ι → P → ι → Prop)
    (closed : ι → P → Prop) (succ : ι → ι) (σ₀ : ι) (ω : ι → P) (m : ℕ) :
    σ₀ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω (m + 1) := by
  unfold FrogModel.Stage.stages
  have hbase : σ₀ ∈ insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
      {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ (ω σ) ∧ τ = succ σ}) :=
    Set.mem_insert _ _
  unfold FrogModel.Stage.closure
  rw [Set.mem_sInter]
  intro S hS
  rcases hS with ⟨hbaseS, hclosedS⟩
  exact hbaseS hbase

theorem FrogModel.Stage.succ_mem_stages {ι P : Type*} (arc : ι → P → ι → Prop)
    (closed : ι → P → Prop) (succ : ι → ι) (σ₀ : ι) (ω : ι → P) (m : ℕ) (σ : ι)
    (hσ : σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m) (hc : closed σ (ω σ)) :
    succ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω (m + 1) := by
  simp only [FrogModel.Stage.stages]
  apply FrogModel.Stage.subset_closure
  refine Or.inr (Or.inr ?_)
  exact ⟨σ, hσ, hc, rfl⟩

theorem FrogModel.Stage.stages_mono {ι P : Type*} (arc : ι → P → ι → Prop)
    (closed : ι → P → Prop) (succ : ι → ι) (σ₀ : ι) (ω : ι → P) :
    Monotone (FrogModel.Stage.stages arc closed succ σ₀ ω) := by
  refine monotone_nat_of_le_succ ?_
  intro m
  exact FrogModel.Stage.stages_mono_succ arc closed succ σ₀ ω m

theorem FrogModel.stage_mono {d : ℕ} (ζ : Pieces d) : Monotone (stage ζ) := by
  unfold stage
  exact FrogModel.Stage.stages_mono segArc segClosed segSucc (root, 0) ζ

theorem FrogModel.segClosed_of_cutSum {d : ℕ} (ζ : Pieces d) (u : Vertex d) (k : ℕ)
    (h : cutSum ζ u k ≠ ⊤) (j : ℕ) (hj : j < k) : segClosed (u, j) (ζ (u, j)) := by
  unfold segClosed
  intro hseg
  have hsum : cutSum ζ u (j + 1) = ⊤ := by
    dsimp [cutSum, segCut]
    rw [hseg, add_top]
  have hle' : j + 1 ≤ k := by omega
  have hle : cutSum ζ u (j + 1) ≤ cutSum ζ u k :=
    (FrogModel.cutSum_mono ζ u) hle'
  have hne : cutSum ζ u (j + 1) ≠ ⊤ := ne_top_of_le_ne_top h hle
  exact hne hsum

theorem FrogModel.mem_stage_of_closed {d : ℕ} (ζ : Pieces d) (u : Vertex d) (m k : ℕ)
    (h0 : (u, 0) ∈ stage ζ m) (hc : ∀ j < k, segClosed (u, j) (ζ (u, j))) :
    (u, k) ∈ stage ζ (m + k) := by
  induction' k with k ih
  · simpa using h0
  · have h_closed : segClosed (u, k) (ζ (u, k)) := hc k (Nat.lt_succ_self k)
    have h_mem : (u, k) ∈ stage ζ (m + k) := ih fun j hj => hc j (Nat.lt_of_lt_of_le hj (Nat.le_succ k))
    have h_succ := FrogModel.Stage.succ_mem_stages segArc segClosed segSucc (root, 0) ζ (m + k) (u, k) h_mem h_closed
    simpa [stage, segSucc, add_assoc] using h_succ

theorem FrogModel.walk_glue_segAt {d : ℕ} (ζ : Pieces d) (u : Vertex d) (t : ℕ) :
    cutSum ζ u (segAt ζ u t) ≠ ⊤ ∧
      ((t - (cutSum ζ u (segAt ζ u t)).toNat : ℕ) : ℕ∞) ≤ segCut ζ (u, segAt ζ u t) ∧
      walk u (glue ζ u) t = walk (Seg.start (u, segAt ζ u t)) (ζ (u, segAt ζ u t))
        (t - (cutSum ζ u (segAt ζ u t)).toNat) := by
  set K := segAt ζ u t with hK_def
  have hspec := segAt_spec ζ u t
  rcases hspec with ⟨hle, hlt⟩
  have hle' : cutSum ζ u K ≤ (t : ℕ∞) := by simpa [hK_def] using hle
  have hlt' : (t : ℕ∞) < cutSum ζ u (K + 1) := by simpa [hK_def] using hlt
  have hK_top : cutSum ζ u K ≠ ⊤ := by
    intro h_eq
    have h_top_le : (⊤ : ℕ∞) ≤ (t : ℕ∞) := by
      calc
        (⊤ : ℕ∞) = cutSum ζ u K := by symm; exact h_eq
        _ ≤ (t : ℕ∞) := hle'
    have h_eq_top : (⊤ : ℕ∞) = (t : ℕ∞) := le_antisymm h_top_le le_top
    exact ENat.natCast_ne_top t h_eq_top.symm
  set T := (cutSum ζ u K).toNat with hT_def
  have hT_eq : cutSum ζ u K = (T : ℕ∞) := (ENat.natCast_toNat hK_top).symm
  have hT_le_t : (T : ℕ∞) ≤ (t : ℕ∞) := by
    simpa [hT_eq] using hle'
  have hT_le_t_nat : T ≤ t := by
    simpa using hT_le_t
  have h_cutSum_succ : cutSum ζ u (K + 1) = cutSum ζ u K + segCut ζ (u, K) := by
    simp [cutSum]
  have h_ineq : (t : ℕ∞) < cutSum ζ u K + segCut ζ (u, K) := by
    simpa [h_cutSum_succ] using hlt'
  have h_seg_le : ((t - T : ℕ) : ℕ∞) ≤ segCut ζ (u, K) := by
    by_cases hseg_top : segCut ζ (u, K) = ⊤
    · rw [hseg_top]
      exact le_top
    · set S := (segCut ζ (u, K)).toNat with hS_def
      have hseg_fin : segCut ζ (u, K) = (S : ℕ∞) := by
        rw [hS_def]
        exact (ENat.natCast_toNat hseg_top).symm
      rw [hseg_fin]
      have h_lt_nat : (t : ℕ∞) < ((T + S : ℕ) : ℕ∞) := by
        simpa [hT_eq, hseg_fin, ENat.natCast_add] using h_ineq
      have h_lt_nat' : t < T + S := (ENat.natCast_lt_natCast.mp h_lt_nat)
      have h_sub_le : t - T ≤ S := by
        omega
      exact Nat.cast_le.mpr h_sub_le
  have h_walk : walk u (glue ζ u) t = walk (Seg.start (u, K)) (ζ (u, K)) (t - T) := by
    have h_add : T + (t - T) = t := Nat.add_sub_cancel' hT_le_t_nat
    have h := walk_glue ζ u K T (t - T) hT_eq h_seg_le
    simpa [h_add] using h
  exact And.intro hK_top (And.intro h_seg_le h_walk)

theorem FrogModel.stage_of_walk_glue {d : ℕ} (ζ : Pieces d) (u : Vertex d) (m : ℕ)
    (h0 : (u, 0) ∈ stage ζ m) (t : ℕ) (ht : walk u (glue ζ u) t ≠ root) :
    ∃ m', (walk u (glue ζ u) t, 0) ∈ stage ζ m' := by
  set K := segAt ζ u t with hK
  set n := t - (cutSum ζ u K).toNat with hn
  have hwalk := walk_glue_segAt ζ u t
  rcases hwalk with ⟨hcut_ne_top, hn_le, hwalk_eq⟩
  rw [← hK] at hn_le hwalk_eq
  have hclosed : ∀ j < K, segClosed (u, j) (ζ (u, j)) :=
    fun j hj => segClosed_of_cutSum ζ u K hcut_ne_top j hj
  have hmem : (u, K) ∈ stage ζ (m + K) :=
    mem_stage_of_closed ζ u m K h0 hclosed
  have hsegArc : segArc (u, K) (ζ (u, K)) (walk u (glue ζ u) t, 0) := by
    refine ⟨rfl, ht, ?_⟩
    use n
    have hsegCut_eq : segCut ζ (u, K) = cut (Seg.start (u, K)) (ζ (u, K)) := rfl
    have hn_le' : (n : ℕ∞) ≤ cut (Seg.start (u, K)) (ζ (u, K)) := by
      rw [← hsegCut_eq]
      exact hn_le
    exact ⟨hn_le', hwalk_eq.symm⟩
  have hstage := Stage.stages_arc segArc segClosed segSucc (root, 0) ζ (m + K) (u, K)
    (walk u (glue ζ u) t, 0) hmem hsegArc
  exact ⟨m + K, hstage⟩

theorem FrogModel.reach_mem_stage {d : ℕ} (ζ : Pieces d) (u : Vertex d)
    (h : Reach (paths fun v => glue ζ v) u) : ∃ m, (u, 0) ∈ stage ζ m := by
  induction' h with u n hu ih
  · -- root case
    refine ⟨1, ?_⟩
    -- Goal: (root, 0) ∈ stage ζ 1
    -- We'll prove a helper lemma: base ⊆ closure arc ω base
    have hmem : (root, 0) ∈ FrogModel.Stage.closure segArc ζ ({(root, 0)} : Set (Seg d)) := by
      intro S hS
      exact hS.1 (Set.mem_singleton _)
    -- Need monotonicity of closure
    have hclosure_mono : FrogModel.Stage.closure segArc ζ ({(root, 0)} : Set (Seg d)) ⊆ FrogModel.Stage.closure segArc ζ (insert (root, 0) (stage ζ 0 ∪ {τ | ∃ σ ∈ stage ζ 0, segClosed σ (ζ σ) ∧ τ = segSucc σ})) := by
      intro x hx S hS
      apply hx S
      have hsub : ({(root, 0)} : Set (Seg d)) ⊆ insert (root, 0) (stage ζ 0 ∪ {τ | ∃ σ ∈ stage ζ 0, segClosed σ (ζ σ) ∧ τ = segSucc σ}) := by
        intro x hx
        have hx' : x = (root, 0) := Set.mem_singleton_iff.mp hx
        subst hx'
        exact Set.mem_insert _ _
      exact ⟨Set.Subset.trans hsub hS.1, hS.2⟩
    have hmem' : (root, 0) ∈ FrogModel.Stage.closure segArc ζ (insert (root, 0) (stage ζ 0 ∪ {τ | ∃ σ ∈ stage ζ 0, segClosed σ (ζ σ) ∧ τ = segSucc σ})) :=
      hclosure_mono hmem
    simpa [stage, FrogModel.Stage.stages] using hmem'
  · -- path case: hu : Reach (paths fun v => glue ζ v) u
    -- ih : ∃ m, (u, 0) ∈ stage ζ m
    -- goal: ∃ m', (paths (fun v => glue ζ v) u n, 0) ∈ stage ζ m'
    -- Note: (paths fun v => glue ζ v) u n = walk u (glue ζ u) n
    rcases ih with ⟨m, hm⟩
    -- hm : (u, 0) ∈ stage ζ m
    by_cases hroot : walk u (glue ζ u) n = root
    · -- If the walk reaches root, use the root case
      refine ⟨1, ?_⟩
      -- Goal: (paths (fun v => glue ζ v) u n, 0) ∈ stage ζ 1
      -- Since paths (fun v => glue ζ v) u n = walk u (glue ζ u) n = root
      have hmem : (root, 0) ∈ FrogModel.Stage.closure segArc ζ ({(root, 0)} : Set (Seg d)) := by
        intro S hS
        exact hS.1 (Set.mem_singleton _)
      have hclosure_mono : FrogModel.Stage.closure segArc ζ ({(root, 0)} : Set (Seg d)) ⊆ FrogModel.Stage.closure segArc ζ (insert (root, 0) (stage ζ 0 ∪ {τ | ∃ σ ∈ stage ζ 0, segClosed σ (ζ σ) ∧ τ = segSucc σ})) := by
        intro x hx S hS
        apply hx S
        have hsub : ({(root, 0)} : Set (Seg d)) ⊆ insert (root, 0) (stage ζ 0 ∪ {τ | ∃ σ ∈ stage ζ 0, segClosed σ (ζ σ) ∧ τ = segSucc σ}) := by
          intro x hx
          have hx' : x = (root, 0) := Set.mem_singleton_iff.mp hx
          subst hx'
          exact Set.mem_insert _ _
        exact ⟨Set.Subset.trans hsub hS.1, hS.2⟩
      have hmem' : (root, 0) ∈ FrogModel.Stage.closure segArc ζ (insert (root, 0) (stage ζ 0 ∪ {τ | ∃ σ ∈ stage ζ 0, segClosed σ (ζ σ) ∧ τ = segSucc σ})) :=
        hclosure_mono hmem
      simpa [stage, FrogModel.Stage.stages, paths, hroot] using hmem'
    · -- walk u (glue ζ u) n ≠ root
      have hne : walk u (glue ζ u) n ≠ root := hroot
      -- Use stage_of_walk_glue
      have hstage_glue := FrogModel.stage_of_walk_glue ζ u m hm n hne
      rcases hstage_glue with ⟨m', hm'⟩
      -- hm' : (walk u (glue ζ u) n, 0) ∈ stage ζ m'
      -- Goal: ∃ m', (paths (fun v => glue ζ v) u n, 0) ∈ stage ζ m'
      -- Note: (paths fun v => glue ζ v) u n = walk u (glue ζ u) n
      refine ⟨m', ?_⟩
      simpa [paths] using hm'

theorem FrogModel.mem_closure_of_ne_zero {d : ℕ} (ζ : Pieces d) (base : Set (Seg d))
    (τ : Seg d) (hτ : τ.2 ≠ 0) (h : τ ∈ FrogModel.Stage.closure segArc ζ base) :
    τ ∈ base := by
  have hτ_mem_S : τ ∈ base ∪ {σ | σ.2 = 0} := by
    have hS : base ∪ {σ | σ.2 = 0} ∈ {S | base ⊆ S ∧ ∀ σ' ∈ S, ∀ τ', segArc σ' (ζ σ') τ' → τ' ∈ S} := by
      refine ⟨?_, ?_⟩
      · exact Set.subset_union_left
      · intro σ' hσ' τ' hseg
        have hτ2zero : τ'.2 = 0 := (hseg.1 : τ'.2 = 0)
        exact Set.mem_union_right _ (by simp [hτ2zero])
    have := (Set.mem_sInter.mp h) (base ∪ {σ | σ.2 = 0}) hS
    exact this
  rcases hτ_mem_S with (hbase | hzero)
  · exact hbase
  · exfalso; exact hτ hzero

theorem FrogModel.enterSeg_zero {d : ℕ} (ζ : Pieces d) : enterSeg ζ 0 = {(root, 0)} := by
  ext τ; simp [enterSeg, stageBase, stage, FrogModel.Stage.stages]

theorem FrogModel.stageR_zero {d : ℕ} (ζ : Pieces d) : stageR ζ 0 = 1 := by
  rw [stageR, FrogModel.enterSeg_zero, Set.encard_singleton, ENat.toENNReal_one]

theorem FrogModel.exists_enterSeg {d : ℕ} (ζ : Pieces d) (τ : Seg d) (hτ : τ.2 ≠ 0) (m : ℕ)
    (h : τ ∈ stage ζ m) : ∃ i, τ ∈ enterSeg ζ (i + 1) := by
  classical
  have h_exists : ∃ n, τ ∈ stage ζ n := ⟨m, h⟩
  set n₀ := Nat.find h_exists with hn₀_def
  have hn₀_spec : τ ∈ stage ζ n₀ := Nat.find_spec h_exists
  have hn₀_min : ∀ n, n < n₀ → τ ∉ stage ζ n := by
    intro n hn
    rw [hn₀_def] at hn
    exact Nat.find_min h_exists hn
  have hn₀_ne_zero : n₀ ≠ 0 := by
    intro hzero
    have h_empty : stage ζ 0 = ∅ := rfl
    rw [hzero, h_empty] at hn₀_spec
    have : τ ∉ (∅ : Set (Seg d)) := by simp
    exact this hn₀_spec
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn₀_ne_zero
  have hk_lt_n₀ : k < n₀ := by
    rw [hk]
    exact Nat.lt_succ_self k
  have hk_not_mem : τ ∉ stage ζ k := hn₀_min k hk_lt_n₀
  have hk_succ_mem : τ ∈ stage ζ (k + 1) := by
    rw [hk] at hn₀_spec
    -- hn₀_spec : τ ∈ stage ζ (k.succ), but we need stage ζ (k + 1)
    simpa [add_comm] using hn₀_spec
  rw [FrogModel.stage_succ ζ k] at hk_succ_mem
  have hmem_base : τ ∈ stageBase ζ k :=
    FrogModel.mem_closure_of_ne_zero ζ (stageBase ζ k) τ hτ hk_succ_mem
  have hmem_enter : τ ∈ enterSeg ζ k := by
    rw [FrogModel.enterSeg, Set.mem_sdiff]
    exact ⟨hmem_base, hk_not_mem⟩
  have hk_ne_zero : k ≠ 0 := by
    intro hkzero
    rw [hkzero, FrogModel.enterSeg_zero ζ] at hmem_enter
    have h_eq : τ = (root, 0) := by
      simpa using hmem_enter
    apply hτ
    simp [h_eq]
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne_zero
  exact ⟨i, by rw [hi] at hmem_enter; exact hmem_enter⟩

theorem FrogModel.visits_subset {d : ℕ} (ζ : Pieces d) :
    {p : Vertex d × ℕ | Reach (paths fun v => glue ζ v) p.1 ∧ 1 ≤ p.2 ∧
        paths (fun v => glue ζ v) p.1 p.2 = root} ⊆
      (fun σ : Seg d => (σ.1, (cutSum ζ σ.1 σ.2).toNat)) '' ⋃ i, enterSeg ζ (i + 1) := by
  intro p hp
  rcases hp with ⟨hp_reach, hp_1le, hp_root⟩
  have h_glue_root : walk p.1 (glue ζ p.1) p.2 = root := hp_root
  have h_cutSum := ((glue_root_iff ζ p.1 p.2 hp_1le).mp h_glue_root)
  rcases h_cutSum with ⟨k, hk⟩
  have h_cutSum_ne_top : cutSum ζ p.1 (k + 1) ≠ ⊤ := by
    rw [hk]
    exact ENat.natCast_ne_top _
  have h_closed : ∀ j, j < k + 1 → segClosed (p.1, j) (ζ (p.1, j)) := by
    intro j hj
    apply segClosed_of_cutSum ζ p.1 (k + 1) h_cutSum_ne_top j hj
  have h_reach_stage := reach_mem_stage ζ p.1 hp_reach
  rcases h_reach_stage with ⟨m, hm⟩
  have h_mem_stage : (p.1, k + 1) ∈ stage ζ (m + (k + 1)) := by
    apply mem_stage_of_closed ζ p.1 m (k + 1) hm
    intro j hj
    apply h_closed j hj
  have h_enterSeg : ∃ i, (p.1, k + 1) ∈ enterSeg ζ (i + 1) := by
    apply exists_enterSeg ζ (p.1, k + 1) (by omega) (m + (k + 1)) h_mem_stage
  rcases h_enterSeg with ⟨i, hi⟩
  have hp_eq : p = (fun σ : Seg d => (σ.1, (cutSum ζ σ.1 σ.2).toNat)) (p.1, k + 1) := by
    ext <;> simp [hk, ENat.toNat_natCast]
  rw [hp_eq, Set.mem_image]
  refine ⟨(p.1, k + 1), ?_, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

theorem FrogModel.encard_iUnion_le_tsum {α : Type*} (s : ℕ → Set α) :
    (((⋃ i, s i).encard : ℕ∞) : ℝ≥0∞) ≤ ∑' i, (((s i).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have h_count_union : MeasureTheory.Measure.count (⋃ i, s i) = (((⋃ i, s i).encard : ℕ∞) : ℝ≥0∞) := by
    rw [MeasureTheory.Measure.count_apply MeasurableSpace.measurableSet_top]
  have h_count_each (i : ℕ) : MeasureTheory.Measure.count (s i) = (((s i).encard : ℕ∞) : ℝ≥0∞) := by
    rw [MeasureTheory.Measure.count_apply MeasurableSpace.measurableSet_top]
  calc
    (((⋃ i, s i).encard : ℕ∞) : ℝ≥0∞) = MeasureTheory.Measure.count (⋃ i, s i) := by
      rw [h_count_union]
    _ ≤ ∑' i, MeasureTheory.Measure.count (s i) := MeasureTheory.measure_iUnion_le s
    _ = ∑' i, (((s i).encard : ℕ∞) : ℝ≥0∞) := by simp [h_count_each]

theorem FrogModel.encard_visits_glue_le {d : ℕ} (ζ : Pieces d) :
    (((visits (paths fun v => glue ζ v)).encard : ℕ∞) : ℝ≥0∞) ≤ ∑' i, stageR ζ (i + 1) := by
  set S := paths (fun v => glue ζ v)
  have hS : ∀ u, S u 0 = u := fun u => rfl
  have h_encard := encard_visits S hS
  have h_subset := visits_subset ζ
  have h_tsum : (((⋃ i, enterSeg ζ (i + 1)).encard : ℕ∞) : ℝ≥0∞) ≤ ∑' i, (((enterSeg ζ (i + 1)).encard : ℕ∞) : ℝ≥0∞) := by
    have h := ENNReal.tsum_iUnion_le_tsum (fun _ : Seg d => (1 : ℝ≥0∞)) (fun i => enterSeg ζ (i + 1))
    simpa [ENNReal.tsum_set_one] using h
  calc
    (((visits S).encard : ℕ∞) : ℝ≥0∞) = (({p : Vertex d × ℕ | Reach S p.1 ∧ 1 ≤ p.2 ∧ S p.1 p.2 = root}).encard : ℝ≥0∞) := by
      simp [h_encard]
    _ ≤ (((fun σ : Seg d => (σ.1, (cutSum ζ σ.1 σ.2).toNat)) '' ⋃ i, enterSeg ζ (i + 1)).encard : ℝ≥0∞) := by
      have h_le : {p : Vertex d × ℕ | Reach S p.1 ∧ 1 ≤ p.2 ∧ S p.1 p.2 = root} ⊆
          (fun σ : Seg d => (σ.1, (cutSum ζ σ.1 σ.2).toNat)) '' ⋃ i, enterSeg ζ (i + 1) := h_subset
      have h_encard_le : ({p : Vertex d × ℕ | Reach S p.1 ∧ 1 ≤ p.2 ∧ S p.1 p.2 = root}).encard ≤
          ((fun σ : Seg d => (σ.1, (cutSum ζ σ.1 σ.2).toNat)) '' ⋃ i, enterSeg ζ (i + 1)).encard :=
        Set.encard_le_encard h_le
      exact ENat.toENNReal_le.mpr h_encard_le
    _ ≤ (((⋃ i, enterSeg ζ (i + 1)).encard : ℕ∞) : ℝ≥0∞) := by
      have h_encard_image_le : ((fun σ : Seg d => (σ.1, (cutSum ζ σ.1 σ.2).toNat)) '' ⋃ i, enterSeg ζ (i + 1)).encard ≤
          (⋃ i, enterSeg ζ (i + 1)).encard :=
        Set.encard_image_le _ _
      exact ENat.toENNReal_le.mpr h_encard_image_le
    _ ≤ ∑' i, (((enterSeg ζ (i + 1)).encard : ℕ∞) : ℝ≥0∞) := h_tsum
    _ = ∑' i, stageR ζ (i + 1) := by
      simp [stageR]

theorem FrogModel.child_mem_stage {d : ℕ} (ζ : Pieces d) (i : ℕ) (j : Fin d) (σ : Seg d)
    (hσ : σ ∈ enterAt ζ i j) : ([j], 0) ∈ stage ζ (i + 1) := by
  rcases hσ with ⟨hσ_enter, hσ_step⟩
  have hσ_start : σ.start = root := FrogModel.enterSeg_start ζ i σ hσ_enter
  have hσ_base : σ ∈ stageBase ζ i := hσ_enter.1
  have hσ_stage : σ ∈ stage ζ (i + 1) := by
    rw [FrogModel.stage_succ]
    exact (FrogModel.Stage.subset_closure segArc ζ (stageBase ζ i)) hσ_base
  have h_arc : segArc σ (ζ σ) ([j], 0) := by
    unfold segArc
    refine ⟨rfl, ?_, 1, ?_, ?_⟩
    · simp [FrogModel.root]
    · rw [hσ_start]
      exact FrogModel.one_le_cut [] (ζ σ)
    · rw [hσ_start]
      simp [walk, step, FrogModel.root, hσ_step]
  rw [FrogModel.stage_succ]
  exact FrogModel.Stage.closure_arc segArc ζ (stageBase ζ i) σ ([j], 0) hσ_stage h_arc

theorem FrogModel.sum_stageW_le {d : ℕ} (ζ : Pieces d) : ∑' i, stageW ζ i ≤ d := by
  let U : ℕ → Set (Fin d) := fun n => {j | ([j], 0) ∈ stage ζ n}
  let W_set : ℕ → Set (Fin d) := fun n =>
    {j | (enterAt ζ (n - 1) j).Nonempty ∧ ([j], 0) ∉ stage ζ (n - 1)}
  let W : ℕ → ℕ := fun n => (W_set n).ncard
  have hU : Monotone U := by
    intro a b h
    have h_stage := FrogModel.stage_mono ζ h
    intro j hj
    have hj' : ([j], 0) ∈ stage ζ a := by simpa [U] using hj
    have hj'' : ([j], 0) ∈ stage ζ b := h_stage hj'
    simpa [U] using hj''
  have h0 : U 0 = ∅ := by
    ext j
    simp [U, stage, Stage.stages]
  have hW : ∀ i, W (i + 1) ≤ (U (i + 1) \ U i).ncard := by
    intro i
    have h_sub : W_set (i + 1) ⊆ U (i + 1) \ U i := by
      intro j hj
      rcases hj with ⟨h_enter, h_not_stage⟩
      have h_stage_succ : ([j], 0) ∈ stage ζ (i + 1) := by
        rcases h_enter with ⟨σ, hσ⟩
        exact FrogModel.child_mem_stage ζ i j σ hσ
      refine ⟨?_, h_not_stage⟩
      simpa [U] using h_stage_succ
    have h_fin : (U (i + 1) \ U i).Finite := by
      have : Fintype (Fin d) := inferInstance
      have h_univ : (Set.univ : Set (Fin d)).Finite := Set.finite_univ
      have h_sub : U (i + 1) \ U i ⊆ Set.univ := by intro x; simp
      exact Set.Finite.subset h_univ h_sub
    exact Set.ncard_le_ncard h_sub h_fin
  have h_sum := FrogModel.TheoremA.sum_new_le d U hU h0 W hW
  have h_eq : ∀ i, stageW ζ i = (W (i + 1) : ℝ≥0∞) := by
    intro i
    dsimp [stageW, W, W_set]
    have h_fin : ({j : Fin d | (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i} : Set (Fin d)).Finite := by
      have : Fintype (Fin d) := inferInstance
      have h_univ : (Set.univ : Set (Fin d)).Finite := Set.finite_univ
      exact Set.Finite.subset h_univ (by intro x; simp)
    have h_cast := Set.Finite.cast_ncard_eq h_fin
    -- h_cast : (s.ncard : ℕ∞) = s.encard
    -- Goal: (s.encard : ℝ≥0∞) = (s.ncard : ℝ≥0∞)
    -- From h_cast.symm: s.encard = (s.ncard : ℕ∞)
    rw [h_cast.symm]
    norm_cast
  simpa [tsum_congr h_eq] using h_sum

theorem FrogModel.measurable_encard_visits {d : ℕ} :
    Measurable fun ω : Sample d => (((visits (paths ω)).encard : ℕ∞) : ℝ≥0∞) := by
  have h_eq : (fun ω : Sample d => (((visits (paths ω)).encard : ℕ∞) : ℝ≥0∞)) = fun ω => (∑' p : Vertex d × ℕ, ((visits (paths ω)).indicator (fun _ => (1 : ℝ≥0∞))) p) := by
    ext ω
    rw [← ENNReal.tsum_set_one (visits (paths ω)), tsum_subtype (visits (paths ω)) (fun _ => (1 : ℝ≥0∞))]
  rw [h_eq]
  classical
  refine Measurable.tsum ?_
  intro p
  rcases p with ⟨u, t⟩
  have h_indicator : (fun ω : Sample d => ((visits (paths ω)).indicator (fun _ : Vertex d × ℕ => (1 : ℝ≥0∞))) (u, t)) = (fun ω : Sample d => if (u, t) ∈ visits (paths ω) then (1 : ℝ≥0∞) else 0) := by
    ext ω
    simp [Set.indicator]
  rw [h_indicator]
  refine Measurable.ite ?_ measurable_const measurable_const
  simpa using measurableSet_visits u t

theorem FrogModel.lintegral_visits_eq {d : ℕ} [NeZero d] :
    ∫⁻ ω, (((visits (paths ω)).encard : ℕ∞) : ℝ≥0∞) ∂frogMeasure d =
      ∫⁻ ζ, (((visits (paths fun v => glue ζ v)).encard : ℕ∞) : ℝ≥0∞) ∂piecesMeasure d := by
  have h_map : frogMeasure d = (piecesMeasure d).map (fun ζ u => glue ζ u) := by
    rw [← FrogModel.map_glue]
  rw [h_map]
  rw [MeasureTheory.lintegral_map FrogModel.measurable_encard_visits
    (Measurable.of_eval fun u => Measurable.of_eval fun t => FrogModel.measurable_glue u t)]

theorem FrogModel.sum_lintegral_stageW_le {d : ℕ} [NeZero d] :
    ∑' i, ∫⁻ ζ, stageW ζ i ∂piecesMeasure d ≤ d := by
  have : IsProbabilityMeasure (piecesMeasure d) := by
    unfold piecesMeasure
    infer_instance
  calc
    ∑' i, ∫⁻ ζ, stageW ζ i ∂piecesMeasure d
        = ∫⁻ ζ, ∑' i, stageW ζ i ∂piecesMeasure d := by
      rw [MeasureTheory.lintegral_tsum (fun i => (FrogModel.measurable_stageW i).aemeasurable)]
    _ ≤ ∫⁻ ζ, (d : ℝ≥0∞) ∂piecesMeasure d := by
      refine MeasureTheory.lintegral_mono (fun ζ => ?_)
      exact FrogModel.sum_stageW_le ζ
    _ = (d : ℝ≥0∞) * (piecesMeasure d) Set.univ := by rw [MeasureTheory.lintegral_const]
    _ = (d : ℝ≥0∞) * 1 := by rw [measure_univ]
    _ = d := by simp

theorem FrogModel.lintegral_stageR_zero {d : ℕ} [NeZero d] :
    ∫⁻ ζ, stageR ζ 0 ∂piecesMeasure d = 1 := by
  have hprob : IsProbabilityMeasure (piecesMeasure d) := by
    unfold piecesMeasure
    infer_instance
  calc
    ∫⁻ ζ, stageR ζ 0 ∂piecesMeasure d = ∫⁻ ζ, (1 : ℝ≥0∞) ∂piecesMeasure d := by
      refine lintegral_congr fun ζ => ?_
      simp [FrogModel.stageR_zero ζ]
    _ = (piecesMeasure d) Set.univ := by simp
    _ = 1 := by simp

theorem FrogModel.theoremA {d : ℕ} [NeZero d] (_hd : 2 ≤ d) (hx : meanX d < 1) :
    ∫⁻ ω, (visits (paths ω)).encard ∂frogMeasure d ≤ (d + 1) * meanX d / (1 - meanX d) := by
  set x := meanX d with hx_def
  set r := fun i : ℕ => ∫⁻ ζ, stageR ζ i ∂piecesMeasure d with hr_def
  set w := fun n : ℕ => ∫⁻ ζ, stageW ζ (n - 1) ∂piecesMeasure d with hw_def
  have h0 : r 0 = 1 := by
    simp [hr_def, FrogModel.lintegral_stageR_zero]
  have hstep : ∀ i, r (i + 1) ≤ x * (r i + w (i + 1)) := by
    intro i
    simp [hr_def, hw_def]
    exact FrogModel.lemma31 i
  have hw_sum : ∑' i, w (i + 1) ≤ (d : ℝ≥0∞) := by
    have h_eq : ∑' i, w (i + 1) = ∑' i, ∫⁻ ζ, stageW ζ i ∂piecesMeasure d := by
      refine tsum_congr (fun i => ?_)
      have sub_eq : ((i : ℕ) + 1) - 1 = i := by omega
      simp [hw_def, sub_eq]
    rw [h_eq]
    exact FrogModel.sum_lintegral_stageW_le
  have hD : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  calc
    ∫⁻ ω, (visits (paths ω)).encard ∂frogMeasure d
        = ∫⁻ ω, (((visits (paths ω)).encard : ℕ∞) : ℝ≥0∞) ∂frogMeasure d := by simp
    _ = ∫⁻ ζ, (((visits (paths fun v => glue ζ v)).encard : ℕ∞) : ℝ≥0∞) ∂piecesMeasure d := by
      rw [FrogModel.lintegral_visits_eq]
    _ ≤ ∫⁻ ζ, (∑' i, stageR ζ (i + 1)) ∂piecesMeasure d := by
      refine lintegral_mono (fun ζ => ?_)
      exact FrogModel.encard_visits_glue_le ζ
    _ = ∑' i, ∫⁻ ζ, stageR ζ (i + 1) ∂piecesMeasure d := by
      rw [lintegral_tsum]
      intro i
      exact (FrogModel.measurable_stageR (i + 1)).aemeasurable
    _ = ∑' i, r (i + 1) := by
      simp [hr_def]
    _ ≤ x * (1 + (d : ℝ≥0∞)) / (1 - x) :=
      FrogModel.TheoremA.sum_bound r w x (d : ℝ≥0∞) hx hD h0 hstep hw_sum
    _ = (d + 1) * x / (1 - x) := by
      have h : x * (1 + (d : ℝ≥0∞)) = (d + 1) * x := by
        simp [add_comm, mul_comm]
      rw [h]
    _ = (d + 1) * meanX d / (1 - meanX d) := by rw [hx_def]

theorem FrogModel.transient_of_meanX_lt_one {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (hx : meanX d < 1) : Transient d := by
  unfold Transient
  have h_bound := theoremA hd hx
  have h_finite_bound : (d + 1 : ℝ≥0∞) * meanX d / (1 - meanX d) ≠ ⊤ := by
    refine ENNReal.div_ne_top ?_ ?_
    · refine ENNReal.mul_ne_top (by simp) ?_
      exact ne_top_of_lt hx
    · have hpos : 0 < 1 - meanX d := tsub_pos_of_lt hx
      exact ne_of_gt hpos
  have h_int_ne_top : ∫⁻ ω, (visits (paths ω)).encard ∂frogMeasure d ≠ ⊤ :=
    ne_top_of_le_ne_top h_finite_bound h_bound
  have h_ae : ∀ᵐ ω ∂frogMeasure d, (((visits (paths ω)).encard : ℕ∞) : ℝ≥0∞) < ⊤ :=
    MeasureTheory.ae_lt_top measurable_encard_visits h_int_ne_top
  filter_upwards [h_ae] with ω hω
  rw [← Set.encard_lt_top_iff]
  simpa using hω
