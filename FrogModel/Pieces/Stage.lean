module

public import FrogModel.Pieces.Basic
public import FrogModel.Lemmas.Refresh

@[expose] public section

/-!
# Lemma 3.5 of the paper in integrated form

`lemma31`: `E R_(i+1) ≤ E X (E R_i + E W_(i+1))`, with `R_i = stageR ζ i`, `W_(i+1) = stageW ζ i`
and `X` the frozen count of the planted tree `T*`.

- Stages: `Stage.subset_closure`, `Stage.closure_arc`, `Stage.stages_arc`, `stage_succ`; a segment
  new at stage `i + 1` is reached from `Z_i` by a chain outside `Σ_i` (`exists_chain`), inside the
  subtree of the child `[j]` entered first (`mem_stage_succ_sub`, `inSub_of_chain`, `inSub_unique`).
- The planted tree: a segment of the subtree of `[j]` is a frog of `T*` (`walk_root_succ`,
  `walk_append_le_cut`, `walkStar_none_of_cut`, `cut_root_succ`, `segArc_star`, `segClosed_star`);
  a chain from `a ∈ A_j` is a chain of `T*` in the sample `starSample j a` of the refreshed pieces
  (`starSample_vertex`, `reach_star`).
- Counting: `reach_union_bound_set`, `frozenCount_eq_encard`, `encard_le_frozenCount`,
  `count_enterSet` (`Σ_j |A_j| = R_i + W_(i+1)`), and the deterministic domination
  `stageR_succ_le`.
- Laws: the stages and `Σ_i ∪ Z_i` are stopping sets (`isStoppingSet_stage`,
  `isStoppingSet_stage_enter`), the events of `A_j` are determined by them (`isDetermined_enterSeg`,
  `isDetermined_enterNew`), measurability (`measurableSet_mem_stage`, `measurable_stageR`,
  `measurable_stageW`, ...), and the law of the sample of `T*` attached to `a`
  (`map_starSample_enter`, `map_pair_starSample`); then `lintegral_enterSet` and `lemma31`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open FrogModel

theorem FrogModel.Stage.subset_closure {ι P : Type*} (arc : ι → P → ι → Prop) (ω : ι → P)
    (base : Set ι) : base ⊆ FrogModel.Stage.closure arc ω base := by
  unfold FrogModel.Stage.closure
  exact Set.subset_sInter fun S hS => hS.1

theorem FrogModel.Stage.closure_arc {ι P : Type*} (arc : ι → P → ι → Prop) (ω : ι → P)
    (base : Set ι) (σ τ : ι) (hσ : σ ∈ FrogModel.Stage.closure arc ω base)
    (h : arc σ (ω σ) τ) : τ ∈ FrogModel.Stage.closure arc ω base := by
    unfold FrogModel.Stage.closure at hσ ⊢
    intro S hS
    have hσS := hσ S hS
    exact hS.2 σ hσS τ h

theorem FrogModel.Stage.stages_arc {ι P : Type*} (arc : ι → P → ι → Prop)
    (closed : ι → P → Prop) (succ : ι → ι) (σ₀ : ι) (ω : ι → P) (m : ℕ) (σ τ : ι)
    (hσ : σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m) (h : arc σ (ω σ) τ) :
    τ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m := by
  induction' m with m ih
  · simp [FrogModel.Stage.stages] at hσ
  · rw [FrogModel.Stage.stages]
    exact FrogModel.Stage.closure_arc arc ω (insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
      {τ' | ∃ σ' ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ' (ω σ') ∧ τ' = succ σ'}))
      σ τ hσ h

theorem FrogModel.stage_succ {d : ℕ} (ζ : Pieces d) (i : ℕ) :
    stage ζ (i + 1) = FrogModel.Stage.closure segArc ζ (stageBase ζ i) := by
  rfl

theorem FrogModel.exists_chain {d : ℕ} (ζ : Pieces d) (i : ℕ) (τ : Seg d)
    (h1 : τ ∈ stage ζ (i + 1)) (h2 : τ ∉ stage ζ i) :
    ∃ σ ∈ enterSeg ζ i,
      Relation.ReflTransGen (fun a b => segArc a (ζ a) b ∧ b ∉ stage ζ i) σ τ := by
  rw [FrogModel.stage_succ ζ i] at h1
  have h_closure := FrogModel.Stage.closure_eq_chains segArc ζ (stageBase ζ i)
  rw [h_closure] at h1
  rcases h1 with ⟨σ, hσ_base, hσ_chain⟩
  -- If σ were in stage ζ i, then by stages_arc induction τ would be too, contradicting h2
  have hσ_not_stage : σ ∉ stage ζ i := by
    intro hσ_stage
    apply h2
    -- Use the induction principle directly to avoid generalization issues
    refine Relation.ReflTransGen.rec (motive := λ x _ => x ∈ stage ζ i)
      hσ_stage ?_ hσ_chain
    intro a b _ h_arc ih
    exact FrogModel.Stage.stages_arc segArc segClosed segSucc (root, 0) ζ i a b ih h_arc
  have hσ_enter : σ ∈ enterSeg ζ i := by
    rw [FrogModel.enterSeg]
    exact ⟨hσ_base, hσ_not_stage⟩
  -- Helper: if x is on the chain from σ to τ and x ∈ stage ζ i, then τ ∈ stage ζ i
  have h_key : ∀ {x : Seg d}, Relation.ReflTransGen (fun a b => segArc a (ζ a) b) x τ → x ∉ stage ζ i := by
    intro x hx hx_stage
    apply h2
    refine Relation.ReflTransGen.rec (motive := λ y _ => y ∈ stage ζ i)
      hx_stage ?_ hx
    intro a b _ h_arc ih
    exact FrogModel.Stage.stages_arc segArc segClosed segSucc (root, 0) ζ i a b ih h_arc
  -- Strengthen the chain using head_induction_on
  refine ⟨σ, hσ_enter, ?_⟩
  refine Relation.ReflTransGen.head_induction_on hσ_chain
    (motive := λ a _ => Relation.ReflTransGen (fun a b => segArc a (ζ a) b ∧ b ∉ stage ζ i) a τ)
    ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro a c hab hchain ih
    have hc_not_stage : c ∉ stage ζ i := h_key hchain
    exact Relation.ReflTransGen.head ⟨hab, hc_not_stage⟩ ih

theorem FrogModel.enterSeg_start {d : ℕ} (ζ : Pieces d) (i : ℕ) (σ : Seg d)
    (h : σ ∈ enterSeg ζ i) : σ.start = root := by
  simp [enterSeg, stageBase] at h
  rcases h with ⟨h_or, hnot⟩
  rcases h_or with (hroot | hstage | hsucc)
  · rw [hroot]; rfl
  · exact absurd hstage hnot
  · rcases hsucc with ⟨a, b, hmem, _, hσ⟩
    rw [hσ]; rfl

theorem FrogModel.enterSeg_succ_subset {d : ℕ} (ζ : Pieces d) (i : ℕ) :
    enterSeg ζ (i + 1) ⊆
      segSucc '' {τ | τ ∈ stage ζ (i + 1) ∧ τ ∉ stage ζ i ∧ segClosed τ (ζ τ)} := by
  intro σ hσ
  rcases hσ with ⟨hσ_base, hσ_not_stage⟩
  -- (root, 0) ∈ stageBase ζ i ⊆ stage ζ (i + 1)
  have h_root_stage : (root, 0) ∈ stage ζ (i + 1) := by
    rw [stage_succ]
    have h_root_base : (root, 0) ∈ stageBase ζ i := by
      rw [stageBase]
      exact Set.mem_insert _ _
    exact FrogModel.Stage.subset_closure segArc ζ (stageBase ζ i) h_root_base
  have hσ_ne_root : σ ≠ (root, 0) := by
    intro h_eq; apply hσ_not_stage; rw [h_eq]; exact h_root_stage
  -- σ ∈ stageBase ζ (i+1) = insert (root,0) (stage ζ (i+1) ∪ {segSucc σ' | σ' ∈ stage ζ (i+1), closed})
  rw [stageBase] at hσ_base
  rcases hσ_base with (hσ_root | hσ_in)
  · exact absurd hσ_root hσ_ne_root
  rcases hσ_in with (hσ_stage | hσ_succ)
  · exact absurd hσ_stage hσ_not_stage
  rcases hσ_succ with ⟨τ, hτ_stage, hτ_closed, hσ_eq⟩
  -- Now show τ ∉ stage ζ i
  have hτ_not_stage_i : τ ∉ stage ζ i := by
    intro hτ_stage_i
    apply hσ_not_stage
    rw [hσ_eq]
    -- segSucc τ ∈ stageBase ζ i ⊆ stage ζ (i+1)
    have h_succ_base : segSucc τ ∈ stageBase ζ i := by
      rw [stageBase]
      apply Set.mem_insert_of_mem
      apply Set.mem_union_right (stage ζ i)
      exact ⟨τ, hτ_stage_i, hτ_closed, rfl⟩
    have h_base_subset : stageBase ζ i ⊆ stage ζ (i + 1) := by
      rw [stage_succ]
      exact FrogModel.Stage.subset_closure segArc ζ (stageBase ζ i)
    exact h_base_subset h_succ_base
  refine ⟨τ, ⟨hτ_stage, hτ_not_stage_i, hτ_closed⟩, ?_⟩
  rw [hσ_eq]

theorem FrogModel.walk_root_succ {d : ℕ} (x : ℕ → Step d) (n : ℕ) :
    walk root x (n + 1) = walk [(x 0).1] (fun m => x (m + 1)) n := by
  induction' n with n ih
  · rfl
  · change step (walk root x (n + 1)) (x (n + 1)) = step (walk [(x 0).1] (fun m => x (m + 1)) n) (x (n + 1))
    rw [ih]

theorem FrogModel.walk_append_le_cut {d : ℕ} (j : Fin d) (v : Vertex d) (x : ℕ → Step d) (n : ℕ)
    (hn : (n : ℕ∞) ≤ cut (v ++ [j]) x) :
    walk (v ++ [j]) x n = embedStar j (walkStar (some v) x n) := by
  by_cases h : ∀ i < n, walkStar (some v) x i ≠ none
  · exact walk_append j v x n h
  · push_neg at h
    let i₀ := Nat.find h
    have hi₀_lt_n : i₀ < n := (Nat.find_spec h).1
    have hi₀_eq_none : walkStar (some v) x i₀ = none := (Nat.find_spec h).2
    have hi₀_ne_zero : i₀ ≠ 0 := by
      intro hzero
      have h0 : walkStar (some v) x 0 = some v := rfl
      rw [hzero, h0] at hi₀_eq_none
      exact Option.some_ne_none _ hi₀_eq_none
    have h_lt_i₀ : ∀ i, i < i₀ → walkStar (some v) x i ≠ none := by
      intro i hi
      have hi_lt_n : i < n := lt_trans hi hi₀_lt_n
      by_contra heq
      have hmin := Nat.find_min h hi
      apply hmin
      exact ⟨hi_lt_n, heq⟩
    have h_append := walk_append j v x i₀ h_lt_i₀
    rw [hi₀_eq_none] at h_append
    have hembed_none : embedStar j none = root := rfl
    rw [hembed_none] at h_append
    have hi₀_ge_one : 1 ≤ i₀ := Nat.one_le_iff_ne_zero.mpr hi₀_ne_zero
    have hi₀_cut : (i₀ : ℕ∞) < cut (v ++ [j]) x := by
      have hcast : (i₀ : ℕ∞) < (n : ℕ∞) := by exact_mod_cast hi₀_lt_n
      exact lt_of_lt_of_le hcast hn
    have h_ne_root := walk_ne_root_of_lt_cut (v ++ [j]) x i₀ hi₀_ge_one hi₀_cut
    rw [h_append] at h_ne_root
    exfalso; exact h_ne_root rfl

theorem FrogModel.walkStar_none_of_cut {d : ℕ} (j : Fin d) (v : Vertex d) (x : ℕ → Step d)
    (h : cut (v ++ [j]) x ≠ ⊤) : ∃ n, walkStar (some v) x n = none := by
  rcases ENat.ne_top_iff_exists.mp h with ⟨n, hn⟩
  rcases walk_cut (v ++ [j]) x n hn.symm with ⟨hle, hwalk⟩
  have hle' : (n : ℕ∞) ≤ cut (v ++ [j]) x := by
    rw [hn]
  have h_eq := walk_append_le_cut j v x n hle'
  rw [hwalk] at h_eq
  have hroot : embedStar j (walkStar (some v) x n) = root := by
    simpa [root] using h_eq.symm
  cases hws : walkStar (some v) x n with
  | none =>
    exact ⟨n, hws⟩
  | some w =>
    have h_embed : embedStar j (some w) = w ++ [j] := rfl
    have h_contra : w ++ [j] = root := by
      rw [← h_embed, ← hws, hroot]
    have h_nonempty : w ++ [j] ≠ root := by
      simp [root]
    exact absurd h_contra h_nonempty

theorem FrogModel.cut_root_succ {d : ℕ} (x : ℕ → Step d) :
    cut root x = cut [(x 0).1] (fun m => x (m + 1)) + 1 := by
  set j := (x 0).1 with hj
  set y := fun m => x (m + 1) with hy
  have hwalk1 : walk root x 1 = [j] := by
    simp [walk, step, root, j]
  have hroot_ne_walk1 : walk root x 1 ≠ root := by
    rw [hwalk1]
    simp [root]
  apply le_antisymm
  · -- cut root x ≤ cut [j] y + 1
    match h : cut [j] y with
    | ⊤ =>
      simp
    | some n =>
      have hn : cut [j] y = (n : ℕ∞) := h
      have hn1 : 1 ≤ n := by
        have hle := one_le_cut [j] y
        rw [hn] at hle
        exact_mod_cast hle
      have hwalk_n : walk [j] y n = root := by
        have hres := walk_cut [j] y n hn
        exact hres.2
      have hwalk_root : walk root x (n + 1) = root := by
        rw [walk_root_succ x n, hwalk_n]
      have h1le : 1 ≤ n + 1 := by omega
      have hcut := (cut_le_iff root x (n + 1)).2
      apply hcut
      exact ⟨n + 1, h1le, le_refl _, hwalk_root⟩
  · -- cut [j] y + 1 ≤ cut root x
    match h_top : cut root x with
    | ⊤ =>
      simp
    | some n =>
      have hn : cut root x = (n : ℕ∞) := h_top
      have hn1 : 1 ≤ n := by
        have hle := one_le_cut root x
        rw [hn] at hle
        exact_mod_cast hle
      have hwalk_n : walk root x n = root := by
        have hres := walk_cut root x n hn
        exact hres.2
      have hn_ne_one : n ≠ 1 := by
        intro h_eq
        rw [h_eq, hwalk1] at hwalk_n
        exact hroot_ne_walk1 hwalk_n
      -- n ≥ 2, so n = 1 + k for some k ≥ 1
      have hn_ge_2 : 2 ≤ n := by
        omega
      rcases Nat.exists_eq_add_of_le hn1 with ⟨k, hk⟩
      -- hk: n = 1 + k
      have hk_pos : 1 ≤ k := by
        omega
      have hwalk_k : walk [j] y k = root := by
        rw [← walk_root_succ x k]
        -- goal: walk root x (k + 1) = root
        rw [add_comm, ← hk]
        exact hwalk_n
      have hcut_j : cut [j] y ≤ (k : ℕ∞) := by
        have hle := (cut_le_iff [j] y k).2
        apply hle
        exact ⟨k, hk_pos, le_refl _, hwalk_k⟩
      -- goal is: cut [j] y + 1 ≤ some n  (which is the same as (n : ℕ∞))
      have h_eq : (k : ℕ∞) + 1 = (n : ℕ∞) := by
        -- (k : ℕ∞) + 1 = (k + 1 : ℕ∞) = (1 + k : ℕ∞) = (n : ℕ∞)
        -- hk: n = 1 + k
        -- So: k + 1 = 1 + k = n
        calc
          (k : ℕ∞) + 1 = ((k + 1 : ℕ) : ℕ∞) := by simp
          _ = ((1 + k : ℕ) : ℕ∞) := by simp [add_comm]
          _ = (n : ℕ∞) := by rw [hk]
      apply le_trans (add_le_add_left hcut_j 1) ?_
      rw [h_eq]
      rfl

theorem FrogModel.segArc_star {d : ℕ} (j : Fin d) (σ : Seg d) (x : ℕ → Step d)
    (hσ : (σ.start = root ∧ (x 0).1 = j) ∨ ∃ v : Vertex d, σ = (v ++ [j], 0)) (τ : Seg d)
    (h : segArc σ x τ) :
    ∃ (v : Vertex d) (n : ℕ), τ = (v ++ [j], 0) ∧
      walkStar (some (starVertex σ)) (starSeq σ x) n = some v := by
  rcases hσ with (⟨hσ_start, hσ_step⟩ | ⟨v₀, hσ_eq⟩)
  · -- Case σ.start = root ∧ (x 0).1 = j
    rcases h with ⟨hτ2, hτ1_ne_root, n, hn_cut, hn_walk⟩
    have hn_pos : n ≠ 0 := by
      intro hzero
      rw [hzero] at hn_walk
      have hwalk0 : walk σ.start x 0 = σ.start := rfl
      rw [hwalk0] at hn_walk
      rw [hσ_start] at hn_walk
      exact hτ1_ne_root hn_walk.symm
    rcases Nat.exists_eq_succ_of_ne_zero hn_pos with ⟨m, rfl⟩
    -- n = m + 1
    rw [hσ_start] at hn_cut hn_walk
    -- hn_cut : (m + 1 : ℕ∞) ≤ cut root x
    -- hn_walk : walk root x (m + 1) = τ.1
    have hcut := cut_root_succ x
    -- hcut : cut root x = cut [(x 0).1] (fun m => x (m + 1)) + 1
    rw [hcut] at hn_cut
    rw [hσ_step] at hn_cut
    -- hn_cut : (m + 1 : ℕ∞) ≤ cut [j] (fun m => x (m + 1)) + 1
    have h_one_ne_top : (1 : ℕ∞) ≠ ⊤ := by
      simp
    have hm_le_cut : (m : ℕ∞) ≤ cut [j] (fun m => x (m + 1)) := by
      have := (WithTop.add_le_add_iff_right (x := (m : ℕ∞)) (y := cut [j] (fun m => x (m + 1))) (z := 1) h_one_ne_top).mp hn_cut
      exact this
    -- Use walk_root_succ to relate walk root x (m+1) to walk [j] (shifted) m
    have hwalk_root := walk_root_succ x m
    -- hwalk_root : walk root x (m + 1) = walk [(x 0).1] (fun m => x (m + 1)) m
    rw [hσ_step] at hwalk_root
    -- hwalk_root : walk root x (m + 1) = walk [j] (fun m => x (m + 1)) m
    rw [hwalk_root] at hn_walk
    -- hn_walk : walk [j] (fun m => x (m + 1)) m = τ.1
    -- Now use walk_append_le_cut
    have hwalk_append := walk_append_le_cut j [] (fun m => x (m + 1)) m hm_le_cut
    -- hwalk_append : walk ([] ++ [j]) (fun m => x (m + 1)) m = embedStar j (walkStar (some []) (fun m => x (m + 1)) m)
    simp at hwalk_append
    -- hwalk_append : walk [j] (fun m => x (m + 1)) m = embedStar j (walkStar (some []) (fun m => x (m + 1)) m)
    rw [hwalk_append] at hn_walk
    -- hn_walk : embedStar j (walkStar (some []) (fun m => x (m + 1)) m) = τ.1
    -- Since τ.1 ≠ root, the walkStar must be some w
    have h_embed : embedStar j (walkStar (some []) (fun m => x (m + 1)) m) ≠ root := by
      rw [hn_walk]
      exact hτ1_ne_root
    -- analyze embedStar j
    have h_starStar : walkStar (some []) (fun m => x (m + 1)) m ≠ none := by
      intro hnone
      apply h_embed
      simp [embedStar, hnone]
    -- So walkStar ... = some w for some w
    rcases (Option.eq_none_or_eq_some _).resolve_left h_starStar with ⟨w, hw⟩
    -- hw : walkStar (some []) (fun m => x (m + 1)) m = some w
    have hτ1_eq : τ.1 = w ++ [j] := by
      rw [← hn_walk, hw]
      rfl
    have hstarVertex : starVertex σ = [] := by
      rw [starVertex, hσ_start]
      rfl
    have hstarSeq : starSeq σ x = (fun m => x (m + 1)) := by
      rw [starSeq, hσ_start]
      rfl
    refine ⟨w, m, ?_, ?_⟩
    · -- τ = (w ++ [j], 0)
      ext <;> simp [hτ1_eq, hτ2]
    · -- walkStar (some (starVertex σ)) (starSeq σ x) m = some w
      rw [hstarVertex, hstarSeq]
      exact hw
  · -- Case σ = (v₀ ++ [j], 0)
    rcases h with ⟨hτ2, hτ1_ne_root, n, hn_cut, hn_walk⟩
    rw [hσ_eq] at hn_cut hn_walk
    -- hn_cut : (n : ℕ∞) ≤ cut ((v₀ ++ [j], 0).start) x
    -- hn_walk : walk ((v₀ ++ [j], 0).start) x n = τ.1
    -- ((v₀ ++ [j], 0).start) = v₀ ++ [j]
    dsimp [Seg.start] at hn_cut hn_walk
    -- hn_cut : (n : ℕ∞) ≤ cut (v₀ ++ [j]) x
    -- hn_walk : walk (v₀ ++ [j]) x n = τ.1
    have hwalk_append := walk_append_le_cut j v₀ x n hn_cut
    -- hwalk_append : walk (v₀ ++ [j]) x n = embedStar j (walkStar (some v₀) x n)
    rw [hwalk_append] at hn_walk
    -- hn_walk : embedStar j (walkStar (some v₀) x n) = τ.1
    have h_embed : embedStar j (walkStar (some v₀) x n) ≠ root := by
      rw [hn_walk]
      exact hτ1_ne_root
    have h_starStar : walkStar (some v₀) x n ≠ none := by
      intro hnone
      apply h_embed
      simp [embedStar, hnone]
    rcases (Option.eq_none_or_eq_some _).resolve_left h_starStar with ⟨w, hw⟩
    -- hw : walkStar (some v₀) x n = some w
    have hτ1_eq : τ.1 = w ++ [j] := by
      rw [← hn_walk, hw]
      rfl
    have hstart_ne_root : Seg.start (v₀ ++ [j], 0) ≠ root := by
      dsimp [Seg.start]
      intro h
      have : v₀ ++ [j] = [] := h
      have hlen : (v₀ ++ [j]).length = 0 := by simpa [this]
      have hlen' : (v₀ ++ [j]).length ≥ 1 := by
        simp
      omega
    have hstarVertex : starVertex (v₀ ++ [j], 0) = v₀ := by
      rw [starVertex]
      rw [if_neg hstart_ne_root]
      rw [List.dropLast_concat]
    have hstarSeq : starSeq (v₀ ++ [j], 0) x = x := by
      rw [starSeq]
      rw [if_neg hstart_ne_root]
    refine ⟨w, n, ?_, ?_⟩
    · -- τ = (w ++ [j], 0)
      ext <;> simp [hτ1_eq, hτ2]
    · -- walkStar (some (starVertex σ)) (starSeq σ x) n = some w
      rw [hσ_eq]
      rw [hstarVertex, hstarSeq]
      exact hw

theorem FrogModel.segClosed_star {d : ℕ} (j : Fin d) (σ : Seg d) (x : ℕ → Step d)
    (hσ : (σ.start = root ∧ (x 0).1 = j) ∨ ∃ v : Vertex d, σ = (v ++ [j], 0))
    (h : segClosed σ x) : ∃ n, walkStar (some (starVertex σ)) (starSeq σ x) n = none := by
  rcases hσ with (⟨hstart, hx0⟩ | ⟨v, hσ_eq⟩)
  · -- Case: σ.start = root ∧ (x 0).1 = j
    have hcut : cut σ.start x ≠ ⊤ := by
      rw [FrogModel.segClosed] at h
      exact h
    rw [hstart] at hcut
    have hcut' : cut [j] (fun m => x (m + 1)) ≠ ⊤ := by
      have h_eq := FrogModel.cut_root_succ x
      rw [hx0] at h_eq
      rw [h_eq] at hcut
      intro htop
      apply hcut
      simp [htop]
    have hstarVertex : starVertex σ = ([] : Vertex d) := by
      unfold starVertex
      simp [hstart]
    have hstarSeq : starSeq σ x = fun m => x (m + 1) := by
      unfold starSeq
      simp [hstart]
    rw [hstarVertex, hstarSeq]
    have hwalk : cut ([] ++ [j]) (fun m => x (m + 1)) = cut [j] (fun m => x (m + 1)) := by simp
    have hcut'' : cut ([] ++ [j]) (fun m => x (m + 1)) ≠ ⊤ := by
      rw [hwalk]
      exact hcut'
    exact FrogModel.walkStar_none_of_cut j [] (fun m => x (m + 1)) hcut''
  · -- Case: σ = (v ++ [j], 0)
    subst hσ_eq
    have hstart_ne_root : Seg.start (v ++ [j], 0) ≠ root := by
      simp [Seg.start, root]
    have hstarVertex : starVertex (v ++ [j], 0) = v := by
      unfold starVertex
      simp [hstart_ne_root]
    have hstarSeq : starSeq (v ++ [j], 0) x = x := by
      unfold starSeq
      simp [hstart_ne_root]
    have hcut : segClosed (v ++ [j], 0) x := by
      simpa using h
    rw [FrogModel.segClosed] at hcut
    simp [Seg.start] at hcut
    rw [hstarVertex, hstarSeq]
    exact FrogModel.walkStar_none_of_cut j v x hcut

theorem FrogModel.inSub_of_chain {d : ℕ} (ζ : Pieces d) (j : Fin d) (Q : Seg d → Seg d → Prop)
    (σ τ : Seg d) (hσ : inSub ζ j σ)
    (h : Relation.ReflTransGen (fun a b => segArc a (ζ a) b ∧ Q a b) σ τ) : inSub ζ j τ := by
  induction h with
  | refl => exact hσ
  | @tail b c _ h_step ih =>
      rcases h_step with ⟨h_segArc, h_Q⟩
      rcases FrogModel.segArc_star j b (ζ b) ih c h_segArc with ⟨v, _, hc, _⟩
      exact Or.inr ⟨v, hc⟩

theorem FrogModel.inSub_unique {d : ℕ} (ζ : Pieces d) (j j' : Fin d) (τ : Seg d)
    (h : inSub ζ j τ) (h' : inSub ζ j' τ) : j = j' := by
  rcases h with (⟨hstart, hstep⟩ | ⟨v, hτ⟩)
  · -- h : τ.start = root ∧ (ζ τ 0).1 = j
    rcases h' with (⟨hstart', hstep'⟩ | ⟨v', hτ'⟩)
    · -- both: (ζ τ 0).1 = j and (ζ τ 0).1 = j'
      rw [← hstep, ← hstep']
    · -- h: τ.start = root, h': τ = (v' ++ [j'], 0)
      rw [hτ'] at hstart
      have hstart_eq : Seg.start (v' ++ [j'], 0) = v' ++ [j'] := rfl
      rw [hstart_eq] at hstart
      have hnonempty : v' ++ [j'] ≠ [] := by simp
      exact absurd hstart hnonempty
  · -- h : τ = (v ++ [j], 0)
    rcases h' with (⟨hstart', hstep'⟩ | ⟨v', hτ'⟩)
    · -- h: τ = (v ++ [j], 0), h': τ.start = root
      rw [hτ] at hstart'
      have hstart_eq : Seg.start (v ++ [j], 0) = v ++ [j] := rfl
      rw [hstart_eq] at hstart'
      have hnonempty : v ++ [j] ≠ [] := by simp
      exact absurd hstart' hnonempty
    · -- both: τ = (v ++ [j], 0) = (v' ++ [j'], 0)
      rw [hτ] at hτ'
      have h_eq : v ++ [j] = v' ++ [j'] := by
        injection hτ'
      have h_last : j = j' := by
        have h_len : (v ++ [j]).length = (v' ++ [j']).length := by rw [h_eq]
        simp at h_len
        -- h_len : v.length + 1 = v'.length + 1
        -- So v.length = v'.length
        have h_len_v : v.length = v'.length := by omega
        have h_append := List.append_inj h_eq h_len_v
        rcases h_append with ⟨_, h_singleton⟩
        -- h_singleton : [j] = [j']
        simpa using h_singleton
      exact h_last

theorem FrogModel.mem_stage_succ_sub {d : ℕ} (ζ : Pieces d) (i : ℕ) (τ : Seg d)
    (h1 : τ ∈ stage ζ (i + 1)) (h2 : τ ∉ stage ζ i) :
    ∃ j, inSub ζ j τ ∧ ∃ σ ∈ enterAt ζ i j,
      Relation.ReflTransGen (fun a b => segArc a (ζ a) b ∧ b ∉ stage ζ i) σ τ := by
  obtain ⟨σ, hσ, hchain⟩ := exists_chain ζ i τ h1 h2
  refine ⟨(ζ σ 0).1, ?_, σ, ?_, hchain⟩
  · have hσ_inSub : inSub ζ (ζ σ 0).1 σ := by
      rw [inSub]
      left
      exact ⟨enterSeg_start ζ i σ hσ, rfl⟩
    exact inSub_of_chain ζ (ζ σ 0).1 (fun a b => b ∉ stage ζ i) σ τ hσ_inSub hchain
  · rw [enterAt]
    exact ⟨hσ, rfl⟩

theorem FrogModel.reach_union_bound_set {α : Type*} (r : α → α → Prop) (A : Set α)
    (P : α → Prop) :
    (({w | P w ∧ ∃ a ∈ A, Relation.ReflTransGen r a w}.encard : ℕ∞) : ℝ≥0∞) ≤
      ∑' a, A.indicator (fun a => (({w | P w ∧
        Relation.ReflTransGen (fun x y => r x y ∧ y ∉ A) a w}.encard : ℕ∞) : ℝ≥0∞)) a := by
  set S := {w | P w ∧ ∃ a ∈ A, Relation.ReflTransGen r a w} with hS
  set S' := fun (a : α) => {w | P w ∧ Relation.ReflTransGen (fun x y => r x y ∧ y ∉ A) a w} with hS'
  set T := ⋃ a ∈ A, S' a with hT

  -- Helper lemma: if a ∈ A and Relation.ReflTransGen r a w, then ∃ a' ∈ A with chain in restricted relation
  have h_reach_restricted : ∀ (a w : α), a ∈ A → Relation.ReflTransGen r a w →
      ∃ a' ∈ A, Relation.ReflTransGen (fun x y => r x y ∧ y ∉ A) a' w := by
    intro a w ha hchain
    -- Use the recursor directly with a custom motive
    refine Relation.ReflTransGen.rec ?refl ?tail hchain
    · -- refl case: target is a
      exact ⟨a, ha, Relation.ReflTransGen.refl⟩
    · -- tail case: given h : Relation.ReflTransGen r a b, hstep : r b c, and ih, produce result for c
      intro b c h hstep ih
      -- ih : ∃ a' ∈ A, Relation.ReflTransGen (fun x y => r x y ∧ y ∉ A) a' b
      -- hstep : r b c
      -- Goal: ∃ a' ∈ A, Relation.ReflTransGen (fun x y => r x y ∧ y ∉ A) a' c
      rcases ih with ⟨a', ha', hchain'⟩
      by_cases hc : (fun x y => r x y ∧ y ∉ A) b c
      · exact ⟨a', ha', hchain'.tail hc⟩
      · have hcA : c ∈ A := by
          by_contra hc_not
          apply hc
          exact ⟨hstep, hc_not⟩
        exact ⟨c, hcA, Relation.ReflTransGen.refl⟩

  -- Step 1: S ⊆ T
  have h_sub : S ⊆ T := by
    intro w hw
    rcases hw with ⟨hP, a, ha, hchain⟩
    rcases h_reach_restricted a w ha hchain with ⟨a', ha', hchain'⟩
    exact Set.mem_biUnion ha' ⟨hP, hchain'⟩

  -- Step 2: (encard S : ℝ≥0∞) ≤ (encard T : ℝ≥0∞)
  have h_encard_le : (S.encard : ℝ≥0∞) ≤ (T.encard : ℝ≥0∞) := by
    exact_mod_cast Set.encard_mono h_sub

  -- Step 3: (encard T : ℝ≥0∞) ≤ ∑' a, A.indicator (fun a => (encard (S' a) : ℝ≥0∞)) a
  have h_encard_T_le : (T.encard : ℝ≥0∞) ≤ ∑' a, A.indicator (fun a => ((S' a).encard : ℝ≥0∞)) a := by
    -- (T.encard : ℝ≥0∞) = ∑' x : T, 1
    have h_encard_eq_tsum : (T.encard : ℝ≥0∞) = ∑' x : T, (1 : ℝ≥0∞) := by
      rw [← ENNReal.tsum_set_one T]
    -- ∑' x : T, 1 ≤ ∑' a : A, ∑' x : S' a, 1
    have h_tsum_le : ∑' x : T, (1 : ℝ≥0∞) ≤ ∑' a : A, ∑' x : S' a, (1 : ℝ≥0∞) := by
      -- T = ⋃ a ∈ A, S' a, so this is exactly ENNReal.tsum_biUnion_le_tsum
      rw [hT]
      exact ENNReal.tsum_biUnion_le_tsum (fun _ => 1) A S'
    -- ∑' a : A, ∑' x : S' a, 1 = ∑' a : A, (S' a).encard = ∑' a, A.indicator ... a
    have h_tsum_eq : ∑' a : A, ∑' x : S' a, (1 : ℝ≥0∞) = ∑' a, A.indicator (fun a => ((S' a).encard : ℝ≥0∞)) a := by
      calc
        ∑' a : A, ∑' x : S' a, (1 : ℝ≥0∞) = ∑' a : A, ((S' a).encard : ℝ≥0∞) := by
          refine tsum_congr fun a => ?_
          rw [ENNReal.tsum_set_one (S' a)]
        _ = ∑' a, A.indicator (fun a => ((S' a).encard : ℝ≥0∞)) a := by
          rw [tsum_subtype A (fun a => ((S' a).encard : ℝ≥0∞))]
    rw [h_encard_eq_tsum]
    exact le_trans h_tsum_le (by rw [h_tsum_eq])

  -- Combine the inequalities
  calc
    (S.encard : ℝ≥0∞) ≤ (T.encard : ℝ≥0∞) := h_encard_le
    _ ≤ ∑' a, A.indicator (fun a => ((S' a).encard : ℝ≥0∞)) a := h_encard_T_le

theorem FrogModel.frozenCount_eq_encard {d : ℕ} (ξ : Sample d) :
    frozenCount ξ = (({v | Relation.ReflTransGen (starArc ξ) [] v ∧
      ∃ n, walkStar (some v) (ξ v) n = none}.encard : ℕ∞) : ℝ≥0∞) := by
  classical
  unfold frozenCount
  set s := {v | Relation.ReflTransGen (starArc ξ) [] v ∧ ∃ n, walkStar (some v) (ξ v) n = none}
  calc
    ∑' v : Vertex d, (if Relation.ReflTransGen (starArc ξ) [] v ∧ ∃ n, walkStar (some v) (ξ v) n = none then 1 else 0)
        = ∑' v : Vertex d, (s.indicator (fun _ => 1)) v := by
          refine tsum_congr ?_
          intro v
          simp [s, Set.indicator_apply]
    _ = ∑' (x : s), (1 : ℝ≥0∞) := by
      rw [← tsum_subtype]
    _ = (s.encard : ℝ≥0∞) := by
      rw [ENNReal.tsum_set_one]
    _ = (({v | Relation.ReflTransGen (starArc ξ) [] v ∧
      ∃ n, walkStar (some v) (ξ v) n = none}.encard : ℕ∞) : ℝ≥0∞) := rfl

theorem FrogModel.encard_le_frozenCount {d : ℕ} {α : Type*} (ξ : Sample d) (S : Set α)
    (f : α → Vertex d) (hf : Set.InjOn f S)
    (hS : ∀ a ∈ S, Relation.ReflTransGen (starArc ξ) [] (f a) ∧
      ∃ n, walkStar (some (f a)) (ξ (f a)) n = none) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ frozenCount ξ := by
  have h_image_eq : (f '' S).encard = S.encard := Set.InjOn.encard_image hf
  have h_subset : f '' S ⊆ {v | Relation.ReflTransGen (starArc ξ) [] v ∧ ∃ n, walkStar (some v) (ξ v) n = none} := by
    intro v hv
    rcases hv with ⟨a, ha, rfl⟩
    exact hS a ha
  have h_encard_le : (f '' S).encard ≤ ({v | Relation.ReflTransGen (starArc ξ) [] v ∧ ∃ n, walkStar (some v) (ξ v) n = none} : Set (Vertex d)).encard :=
    Set.encard_mono h_subset
  calc
    ((S.encard : ℕ∞) : ℝ≥0∞) = ((f '' S).encard : ℝ≥0∞) := by
      simp [h_image_eq]
    _ ≤ (({v | Relation.ReflTransGen (starArc ξ) [] v ∧ ∃ n, walkStar (some v) (ξ v) n = none} : Set (Vertex d)).encard : ℝ≥0∞) :=
      ENat.toENNReal_le.mpr h_encard_le
    _ = frozenCount ξ := by
      simp [frozenCount_eq_encard ξ]

theorem FrogModel.enterSet_props {d : ℕ} (ζ : Pieces d) (i : ℕ) (j : Fin d) (a : Seg d)
    (ha : a ∈ enterSet ζ i j) :
    a ∉ stage ζ i ∧ inSub ζ j a ∧ (a.start = root ∨ a = ([j], 0)) := by
  rcases ha with ⟨_h_nonempty, h_cases⟩
  rcases h_cases with (h_enterAt | ⟨h_eq, h_not_stage⟩)
  · -- case a ∈ enterAt ζ i j
    rcases h_enterAt with ⟨h_enterSeg, h_first_step⟩
    have h_not_stage : a ∉ stage ζ i := h_enterSeg.2
    have h_stageBase : a ∈ stageBase ζ i := h_enterSeg.1
    have h_start_root : a.start = root := by
      simp [stageBase] at h_stageBase
      rcases h_stageBase with (h_a_root | h_a_stage | ⟨σ, _h_σ_stage, _h_σ_closed, h_a_eq⟩)
      · rw [h_a_root]; rfl
      · exfalso; exact h_not_stage h_a_stage
      · rcases h_a_eq with ⟨_h_seg_closed, h_a_eq'⟩
        rw [h_a_eq']; rfl
    have h_inSub : inSub ζ j a := Or.inl ⟨h_start_root, h_first_step⟩
    exact ⟨h_not_stage, h_inSub, Or.inl h_start_root⟩
  · -- case a = ([j], 0) ∧ ([j], 0) ∉ stage ζ i
    subst h_eq
    have h_inSub : inSub ζ j ([j], 0) := by
      refine Or.inr ⟨[], ?_⟩
      simp
    exact ⟨h_not_stage, h_inSub, Or.inr rfl⟩

theorem FrogModel.starSample_vertex {d : ℕ} (ζ ζ' : Pieces d) (i : ℕ) (j : Fin d) (a τ : Seg d)
    (ha : a.start = root ∨ a = ([j], 0)) (hτ : τ ∉ stage ζ i)
    (h : τ = a ∨ ∃ v : Vertex d, v ≠ [] ∧ τ = (v ++ [j], 0)) :
    starSample j a (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ') (starVertex τ) =
      starSeq τ (ζ τ) := by
  rcases h with (hτ_eq_a | ⟨v, hv_ne_nil, hτ_eq⟩)
  · -- τ = a
    rcases ha with (ha_root | ha_eq)
    · -- a.start = root, τ = a
      rw [hτ_eq_a]
      have ha_not_stage : a ∉ stage ζ i := by rwa [← hτ_eq_a]
      simp [starSample, starSeq, starVertex, FrogModel.Stage.refresh, ha_root, ha_not_stage]
    · -- a = ([j], 0), τ = a
      rw [ha_eq] at hτ_eq_a ⊢
      rw [hτ_eq_a]
      have ha_not_stage : ([j], 0) ∉ stage ζ i := by rwa [← hτ_eq_a]
      have h_start_ne_root : Seg.start ([j], 0) ≠ root := by
        simp [Seg.start, root]
      simp [starSample, starSeq, starVertex, FrogModel.Stage.refresh, ha_not_stage, h_start_ne_root]
  · -- τ = (v ++ [j], 0), v ≠ []
    rw [hτ_eq]
    have ha_not_stage : (v ++ [j], 0) ∉ stage ζ i := by rwa [← hτ_eq]
    have h_start_ne_root : Seg.start (v ++ [j], 0) ≠ root := by
      simp [Seg.start, root, hv_ne_nil]
    simp [starSample, starSeq, starVertex, FrogModel.Stage.refresh, ha_not_stage, hv_ne_nil, h_start_ne_root]

theorem FrogModel.reach_star {d : ℕ} (ζ ζ' : Pieces d) (i : ℕ) (j : Fin d) (a : Seg d)
    (ha : a ∈ enterSet ζ i j) (τ : Seg d)
    (h : Relation.ReflTransGen
      (fun x y => (segArc x (ζ x) y ∧ y ∉ stage ζ i) ∧ y ∉ enterSet ζ i j) a τ) :
    (τ ∉ stage ζ i ∧ (τ = a ∨ ∃ v : Vertex d, v ≠ [] ∧ τ = (v ++ [j], 0))) ∧
      Relation.ReflTransGen
        (starArc (starSample j a (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ')))
        [] (starVertex τ) ∧
      (segClosed τ (ζ τ) → ∃ n, walkStar (some (starVertex τ))
        (starSample j a (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ') (starVertex τ)) n =
          none) := by
  set ξ := starSample j a (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ') with hξ
  have ha_props := FrogModel.enterSet_props ζ i j a ha
  rcases ha_props with ⟨ha_not_stage, ha_inSub, ha_start⟩
  rcases ha with ⟨h_enterAt_nonempty, h_enterSet_mem⟩
  induction h with
  | refl =>
    have h_starVertex_a : starVertex a = [] := by
      unfold starVertex
      rcases ha_start with (hstart | heq)
      · simp [hstart]
      · simp [heq]
    have hξ_a : ξ (starVertex a) = starSeq a (ζ a) := by
      dsimp [ξ]
      apply FrogModel.starSample_vertex ζ ζ' i j a a ha_start ha_not_stage (Or.inl rfl)
    have h_first : a ∉ stage ζ i ∧ (a = a ∨ ∃ v : Vertex d, v ≠ [] ∧ a = (v ++ [j], 0)) :=
      ⟨ha_not_stage, Or.inl rfl⟩
    have h_second : Relation.ReflTransGen (starArc ξ) [] (starVertex a) := by
      simpa [h_starVertex_a] using Relation.ReflTransGen.refl
    have h_third : segClosed a (ζ a) → ∃ n, walkStar (some (starVertex a)) (ξ (starVertex a)) n = none := by
      intro hsegClosed
      have hsegClosed_star := FrogModel.segClosed_star j a (ζ a) ha_inSub hsegClosed
      rcases hsegClosed_star with ⟨n, hn⟩
      -- hn : walkStar (some (starVertex a)) (starSeq a (ζ a)) n = none
      -- hξ_a : ξ (starVertex a) = starSeq a (ζ a)
      -- We need: walkStar (some (starVertex a)) (ξ (starVertex a)) n = none
      -- From hn and hξ_a, we can rewrite
      have := hn
      rw [← hξ_a] at this
      exact ⟨n, this⟩
    exact ⟨h_first, h_second, h_third⟩
  | @tail b c hb hstep ih =>
    rcases hstep with ⟨⟨hsegArc_bc, hbc_not_stage⟩, hbc_not_enterSet⟩
    rcases ih with ⟨⟨hb_not_stage, hb_form⟩, ih_star, ih_closed⟩
    have hb_inSub : inSub ζ j b := by
      rcases hb_form with (hb_eq_a | ⟨v, hv_ne_nil, hb_eq⟩)
      · rw [hb_eq_a]
        exact ha_inSub
      · rw [hb_eq]
        exact Or.inr ⟨v, rfl⟩
    rcases FrogModel.segArc_star j b (ζ b) hb_inSub c hsegArc_bc with ⟨v, n, hc_eq, hwalk⟩
    have hv_ne_nil : v ≠ [] := by
      intro hv_nil
      have hc_eq' : c = ([j], 0) := by
        rw [hv_nil] at hc_eq
        simpa using hc_eq
      have h_not_stage : ([j], 0) ∉ stage ζ i := by
        rw [← hc_eq']
        exact hbc_not_stage
      have h_enterSet : ([j], 0) ∈ enterSet ζ i j := by
        refine ⟨h_enterAt_nonempty, Or.inr ⟨rfl, h_not_stage⟩⟩
      rw [hc_eq'] at hbc_not_enterSet
      exact hbc_not_enterSet h_enterSet
    have hc_form : c = a ∨ ∃ v' : Vertex d, v' ≠ [] ∧ c = (v' ++ [j], 0) := by
      right
      exact ⟨v, hv_ne_nil, hc_eq⟩
    have hc_not_stage : c ∉ stage ζ i := hbc_not_stage
    have hc_inSub : inSub ζ j c := by
      rw [hc_eq]
      exact Or.inr ⟨v, rfl⟩
    have h_starVertex_c : starVertex c = v := by
      rw [hc_eq]
      unfold starVertex
      have h_start_ne_root : Seg.start (v ++ [j], 0) ≠ root := by
        simp [Seg.start, root]
      simp [h_start_ne_root]
    have hξ_b : ξ (starVertex b) = starSeq b (ζ b) := by
      dsimp [ξ]
      apply FrogModel.starSample_vertex ζ ζ' i j a b ha_start hb_not_stage hb_form
    have hξ_c : ξ (starVertex c) = starSeq c (ζ c) := by
      dsimp [ξ]
      apply FrogModel.starSample_vertex ζ ζ' i j a c ha_start hc_not_stage hc_form
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨hc_not_stage, hc_form⟩
    · rw [h_starVertex_c]
      have h_starArc : starArc ξ (starVertex b) v := by
        refine ⟨hv_ne_nil, n, ?_⟩
        rw [hξ_b]
        exact hwalk
      exact Relation.ReflTransGen.tail ih_star h_starArc
    · intro hsegClosed_c
      have hsegClosed_star := FrogModel.segClosed_star j c (ζ c) hc_inSub hsegClosed_c
      rcases hsegClosed_star with ⟨m, hm⟩
      rw [← hξ_c] at hm
      exact ⟨m, hm⟩

theorem FrogModel.count_enterSet {d : ℕ} (ζ : Pieces d) (i : ℕ) :
    ∑' j : Fin d, (((enterSet ζ i j).encard : ℕ∞) : ℝ≥0∞) = stageR ζ i + stageW ζ i := by
  classical
  classical
  unfold stageR stageW
  rw [tsum_fintype]
  -- For each j, express (enterSet ζ i j).encard
  have h_enterSet_encard (j : Fin d) : (enterSet ζ i j).encard = (enterAt ζ i j).encard +
      (if (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i then (1 : ℕ∞) else 0) := by
    by_cases hA : (enterAt ζ i j).Nonempty
    · by_cases hB : ([j], 0) ∉ stage ζ i
      · -- Case: A nonempty, ([j],0) not in stage
        have h_disjoint : Disjoint (enterAt ζ i j) {([j], 0)} := by
          refine Set.disjoint_singleton_right.mpr ?_
          intro hmem
          have hmem' : ([j], 0) ∈ enterSeg ζ i := hmem.1
          have hstart : Seg.start ([j], 0) = root := enterSeg_start ζ i ([j], 0) hmem'
          have hstart' : Seg.start ([j], 0) = [j] := rfl
          rw [hstart'] at hstart
          have hne : [j] ≠ [] := by simp
          exact hne hstart
        have h_eq : enterSet ζ i j = enterAt ζ i j ∪ {([j], 0)} := by
          ext σ; simp [enterSet, hA, hB, or_comm]
        rw [h_eq, Set.encard_union_eq h_disjoint, Set.encard_singleton]
        simp [hA, hB]
      · -- Case: A nonempty, ([j],0) in stage
        have h_eq : enterSet ζ i j = enterAt ζ i j := by
          ext σ; simp [enterSet, hA, hB]
        rw [h_eq]
        simp [hA, hB]
    · -- Case: A empty
      have h_empty : enterSet ζ i j = ∅ := by
        ext σ; simp [enterSet, hA]
      rw [h_empty, Set.encard_empty]
      have h_encard_empty : (enterAt ζ i j).encard = 0 := by
        rw [Set.encard_eq_zero, Set.not_nonempty_iff_eq_empty.mp hA]
      simp [h_encard_empty, hA]
  -- Now sum the equality over j
  have h_sum_eq : (∑ j : Fin d, ((enterSet ζ i j).encard : ℝ≥0∞)) =
      (∑ j : Fin d, ((enterAt ζ i j).encard : ℝ≥0∞)) +
      (∑ j : Fin d, (if (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i then (1 : ℕ∞) else 0 : ℝ≥0∞)) := by
    simp_rw [h_enterSet_encard]
    simp only [ENat.toENNReal_add, Finset.sum_add_distrib]
    -- Now we have: (∑ j, ↑(enterAt ...)) + (∑ j, ↑(if ...)) = (∑ j, ↑(enterAt ...)) + (∑ j, if ... then ↑1 else 0)
    -- Need to push the cast inside the if
    congr 1
    -- Goal: ∑ j, ↑(if ... then 1 else 0) = ∑ j, (if ... then ↑1 else 0)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i
    · simp [h]
    · simp [h]
  rw [h_sum_eq]
  -- First sum: partition property
  have h_partition : (enterSeg ζ i) = ⋃ j : Fin d, enterAt ζ i j := by
    ext σ
    constructor
    · intro hσ
      refine Set.mem_iUnion.mpr ?_
      use (ζ σ 0).1
      dsimp [enterAt]
      simp [hσ]
    · intro hσ
      rcases Set.mem_iUnion.mp hσ with ⟨j, hj⟩
      dsimp [enterAt] at hj
      exact hj.1
  have h_disjoint : Pairwise (Function.onFun Disjoint (fun (j : Fin d) => enterAt ζ i j)) := by
    intro j k hj_ne
    apply Set.disjoint_left.mpr
    intro σ hσj hσk
    dsimp [enterAt] at hσj hσk
    have h_eq_j : (ζ σ 0).1 = j := hσj.2
    have h_eq_k : (ζ σ 0).1 = k := hσk.2
    rw [h_eq_j] at h_eq_k
    exact hj_ne (h_eq_k.symm ▸ rfl)
  have h_sum_enterAt : (∑ j : Fin d, ((enterAt ζ i j).encard : ℝ≥0∞)) = ((enterSeg ζ i).encard : ℝ≥0∞) := by
    have h_encard_iUnion : (⋃ j : Fin d, enterAt ζ i j).encard = ∑ᶠ j : Fin d, (enterAt ζ i j).encard :=
      Set.encard_iUnion_of_finite h_disjoint
    have h_eq_nat : (enterSeg ζ i).encard = (∑ j : Fin d, (enterAt ζ i j).encard) := by
      calc
        (enterSeg ζ i).encard = ((⋃ j : Fin d, enterAt ζ i j)).encard := by rw [← h_partition]
        _ = ∑ᶠ j : Fin d, (enterAt ζ i j).encard := by rw [h_encard_iUnion]
        _ = ∑ j : Fin d, (enterAt ζ i j).encard := by rw [finsum_eq_sum_of_fintype]
    calc
      (∑ j : Fin d, ((enterAt ζ i j).encard : ℝ≥0∞)) =
          ((∑ j : Fin d, (enterAt ζ i j).encard : ℕ∞) : ℝ≥0∞) :=
        (map_sum ENat.toENNRealRingHom (fun j => (enterAt ζ i j).encard) Finset.univ).symm
      _ = ((enterSeg ζ i).encard : ℝ≥0∞) := by rw [h_eq_nat]
  rw [h_sum_enterAt]
  -- Second sum: the indicator sum equals {j | ...}.encard
  have h_sum_indicator : (∑ j : Fin d, (if (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i then (1 : ℕ∞) else 0 : ℝ≥0∞)) =
      (({j : Fin d | (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i} : Set (Fin d)).encard : ℝ≥0∞) := by
    have h_sum_nat : (∑ j : Fin d, (if (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i then (1 : ℕ∞) else 0)) =
        (({j : Fin d | (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i} : Set (Fin d)).encard : ℕ∞) := by
      simp [Finset.sum_boole, Set.encard_eq_coe_toFinset_card]
    have := congrArg ENat.toENNReal h_sum_nat
    simpa [map_sum ENat.toENNRealRingHom] using this
  rw [h_sum_indicator]

theorem FrogModel.isStoppingSet_stage {d : ℕ} (i : ℕ) :
    FrogModel.Stage.IsStoppingSet (X := fun _ : Seg d => ℕ → Step d) (fun ζ => stage ζ i) := by
  unfold stage
  exact FrogModel.Stage.isStoppingSet_stages segArc segClosed segSucc (root, 0) i

theorem FrogModel.isStoppingSet_stage_enter {d : ℕ} (i : ℕ) :
    FrogModel.Stage.IsStoppingSet (X := fun _ : Seg d => ℕ → Step d)
      (fun ζ => stage ζ i ∪ enterSeg ζ i) := by
  intro ζ ζ' h
  have hs : stage ζ' i = stage ζ i := by
    have h_stage_stopping := FrogModel.isStoppingSet_stage (d := d) i
    apply h_stage_stopping ζ ζ'
    intro σ hσ
    apply h σ
    exact Or.inl hσ
  have h_enter : enterSeg ζ' i = enterSeg ζ i := by
    unfold enterSeg
    have h_stageBase : stageBase ζ' i = stageBase ζ i := by
      unfold stageBase
      rw [hs]
      congr
      ext τ
      constructor
      · rintro ⟨σ, hσ, ⟨hseg, heq⟩⟩
        have h_eq := h σ (Or.inl hσ)
        refine ⟨σ, hσ, ⟨?_, heq⟩⟩
        rw [← h_eq] at hseg
        exact hseg
      · rintro ⟨σ, hσ, ⟨hseg, heq⟩⟩
        have h_eq := h σ (Or.inl hσ)
        refine ⟨σ, hσ, ⟨?_, heq⟩⟩
        rw [h_eq] at hseg
        exact hseg
    rw [h_stageBase, hs]
  simp [hs, h_enter]

theorem FrogModel.measurableSet_mem_stage {d : ℕ} (i : ℕ) (σ : Seg d) :
    MeasurableSet {ζ : Pieces d | σ ∈ stage ζ i} := by
  unfold stage
  apply FrogModel.Stage.measurableSet_stages segArc segClosed segSucc (root, 0)
    (fun σ τ => measurableSet_segArc σ τ) (fun σ => measurableSet_segClosed σ) i σ

theorem FrogModel.measurableSet_mem_enterSeg {d : ℕ} (i : ℕ) (σ : Seg d) :
    MeasurableSet {ζ : Pieces d | σ ∈ enterSeg ζ i} := by
  -- express enterSeg as (A ∪ B ∪ ⋃ τ, (C τ ∩ D τ ∩ E τ)) \ B
  -- where A = {ζ | σ = (root, 0)}, B = {ζ | σ ∈ stage ζ i},
  -- C τ = {ζ | τ ∈ stage ζ i}, D τ = {ζ | segClosed τ (ζ τ)},
  -- E τ = {ζ | σ = segSucc τ}
  have h_eq : {ζ : Pieces d | σ ∈ enterSeg ζ i} =
      ({ζ | σ = (root, 0)} ∪ {ζ | σ ∈ stage ζ i} ∪
        ⋃ τ : Seg d, ({ζ | τ ∈ stage ζ i} ∩ {ζ | segClosed τ (ζ τ)} ∩ {ζ | σ = segSucc τ})) \
      {ζ | σ ∈ stage ζ i} := by
    ext ζ
    simp [enterSeg, stageBase, Set.mem_insert_iff, Set.mem_union,
      Set.mem_iUnion, or_assoc, and_comm, and_assoc, and_left_comm]
  rw [h_eq]
  -- A is constant, hence measurable
  have hA : MeasurableSet {ζ : Pieces d | σ = (root, 0)} :=
    MeasurableSet.const (σ = (root, 0))
  -- B is measurable by the given lemma
  have hB : MeasurableSet {ζ : Pieces d | σ ∈ stage ζ i} :=
    FrogModel.measurableSet_mem_stage i σ
  -- C τ is measurable by the given lemma
  have hC (τ : Seg d) : MeasurableSet {ζ : Pieces d | τ ∈ stage ζ i} :=
    FrogModel.measurableSet_mem_stage i τ
  -- D τ: preimage of measurableSet_segClosed under measurable_pi_apply
  have hD (τ : Seg d) : MeasurableSet {ζ : Pieces d | segClosed τ (ζ τ)} := by
    -- {ζ | segClosed τ (ζ τ)} = (fun x => x τ)⁻¹' {x | segClosed τ x}
    simpa using (FrogModel.measurableSet_segClosed τ).preimage (measurable_pi_apply τ)
  -- E τ is constant, hence measurable
  have hE (τ : Seg d) : MeasurableSet {ζ : Pieces d | σ = segSucc τ} :=
    MeasurableSet.const (σ = segSucc τ)
  -- C τ ∩ D τ ∩ E τ is measurable
  have hCD (τ : Seg d) : MeasurableSet ({ζ : Pieces d | τ ∈ stage ζ i} ∩
      {ζ : Pieces d | segClosed τ (ζ τ)} ∩ {ζ : Pieces d | σ = segSucc τ}) :=
    ((hC τ).inter (hD τ)).inter (hE τ)
  -- ⋃ τ, (C τ ∩ D τ ∩ E τ) is measurable (countable union)
  have hU : MeasurableSet (⋃ τ : Seg d, ({ζ : Pieces d | τ ∈ stage ζ i} ∩
      {ζ : Pieces d | segClosed τ (ζ τ)} ∩ {ζ : Pieces d | σ = segSucc τ})) :=
    MeasurableSet.iUnion hCD
  -- (A ∪ B ∪ U) \ B is measurable
  exact (((hA.union hB).union hU).diff hB)

theorem FrogModel.isDetermined_enterSeg {d : ℕ} (i : ℕ) (a : Seg d) :
    FrogModel.Stage.IsDetermined (X := fun _ : Seg d => ℕ → Step d) (fun ζ => stage ζ i)
      {ζ | a ∈ enterSeg ζ i} := by
  intro ζ ζ' h
  have hstage : stage ζ' i = stage ζ i := FrogModel.isStoppingSet_stage i ζ ζ' h
  have hmem : ∀ σ ∈ stage ζ i, ζ σ = ζ' σ := h
  have henter : enterSeg ζ' i = enterSeg ζ i := by
    unfold enterSeg stageBase
    rw [hstage]
    have hset : {τ | ∃ σ ∈ stage ζ i, segClosed σ (ζ' σ) ∧ τ = segSucc σ} =
               {τ | ∃ σ ∈ stage ζ i, segClosed σ (ζ σ) ∧ τ = segSucc σ} := by
      ext τ
      constructor
      · rintro ⟨σ, hσ, hcl, hrfl⟩
        exact ⟨σ, hσ, by simpa [← hmem σ hσ] using hcl, hrfl⟩
      · rintro ⟨σ, hσ, hcl, hrfl⟩
        exact ⟨σ, hσ, by simpa [hmem σ hσ] using hcl, hrfl⟩
    rw [hset]
  simp [henter]

theorem FrogModel.isDetermined_enterNew {d : ℕ} (i : ℕ) (j : Fin d) :
    FrogModel.Stage.IsDetermined (X := fun _ : Seg d => ℕ → Step d)
      (fun ζ => stage ζ i ∪ enterSeg ζ i)
      {ζ | (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i} := by
  dsimp [FrogModel.Stage.IsDetermined]
  intro ζ ζ' h
  have h_simp : ∀ σ ∈ stage ζ i ∪ enterSeg ζ i, ζ σ = ζ' σ := by
    intro σ hσ
    exact h σ hσ
  have h_stage_eq : stage ζ i = stage ζ' i := by
    have h_stage_agree : ∀ σ ∈ stage ζ i, ζ σ = ζ' σ := by
      intro σ hσ
      exact h_simp σ (Or.inl hσ)
    have h_stopping := FrogModel.isStoppingSet_stage (d := d) i
    simpa using (h_stopping ζ ζ' h_stage_agree).symm
  have h_enterSeg_eq : enterSeg ζ i = enterSeg ζ' i := by
    have h_enter_agree : ∀ σ ∈ stage ζ i ∪ enterSeg ζ i, ζ σ = ζ' σ := h_simp
    have h_stopping := FrogModel.isStoppingSet_stage_enter (d := d) i
    have h_union_eq : stage ζ' i ∪ enterSeg ζ' i = stage ζ i ∪ enterSeg ζ i := by
      simpa using h_stopping ζ ζ' h_enter_agree
    rw [← h_stage_eq] at h_union_eq
    have h_disjoint : Disjoint (stage ζ i) (enterSeg ζ i) := by
      rw [FrogModel.enterSeg]
      rw [Set.disjoint_iff_inter_eq_empty]
      ext σ
      simp
    ext σ
    constructor
    · intro hσ
      have hσ_union : σ ∈ stage ζ i ∪ enterSeg ζ i := Or.inr hσ
      rw [← h_union_eq] at hσ_union
      rcases hσ_union with (hσ_stage | hσ_enter)
      · rw [Set.disjoint_iff_inter_eq_empty] at h_disjoint
        have h_empty : stage ζ i ∩ enterSeg ζ i = ∅ := h_disjoint
        have h_inter : σ ∈ stage ζ i ∩ enterSeg ζ i := ⟨hσ_stage, hσ⟩
        rw [h_empty] at h_inter
        simp at h_inter
      · exact hσ_enter
    · intro hσ
      have hσ_union : σ ∈ stage ζ i ∪ enterSeg ζ' i := Or.inr hσ
      rw [h_union_eq] at hσ_union
      rcases hσ_union with (hσ_stage | hσ_enter)
      · have h_disjoint' : Disjoint (stage ζ i) (enterSeg ζ' i) := by
          rw [FrogModel.enterSeg, h_stage_eq]
          rw [Set.disjoint_iff_inter_eq_empty]
          ext σ'
          simp
        rw [Set.disjoint_iff_inter_eq_empty] at h_disjoint'
        have h_empty : stage ζ i ∩ enterSeg ζ' i = ∅ := h_disjoint'
        have h_inter : σ ∈ stage ζ i ∩ enterSeg ζ' i := ⟨hσ_stage, hσ⟩
        rw [h_empty] at h_inter
        simp at h_inter
      · exact hσ_enter
  have h_enterAt_eq : enterAt ζ i j = enterAt ζ' i j := by
    ext σ
    constructor
    · intro ⟨hσ, hfirst⟩
      have hσ' : σ ∈ enterSeg ζ' i := by
        rw [← h_enterSeg_eq]
        exact hσ
      have h_eq := h_simp σ (Or.inr hσ)
      have hfirst' : (ζ' σ 0).1 = j := by
        rw [← h_eq]
        exact hfirst
      exact ⟨hσ', hfirst'⟩
    · intro ⟨hσ, hfirst⟩
      have hσ_orig : σ ∈ enterSeg ζ i := by
        rw [h_enterSeg_eq]
        exact hσ
      have h_eq := h_simp σ (Or.inr hσ_orig)
      have hfirst' : (ζ σ 0).1 = j := by
        rw [h_eq]
        exact hfirst
      exact ⟨hσ_orig, hfirst'⟩
  constructor
  · intro ⟨henter, hstage⟩
    refine ⟨?_, ?_⟩
    · rw [← h_enterAt_eq]
      exact henter
    · rw [← h_stage_eq]
      exact hstage
  · intro ⟨henter, hstage⟩
    refine ⟨?_, ?_⟩
    · rw [h_enterAt_eq]
      exact henter
    · rw [h_stage_eq]
      exact hstage

theorem FrogModel.measurableSet_enterNew {d : ℕ} (i : ℕ) (j : Fin d) :
    MeasurableSet {ζ : Pieces d | (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i} := by
  have h_nonempty_eq : {ζ : Pieces d | (enterAt ζ i j).Nonempty} =
      ⋃ σ : Seg d, {ζ | σ ∈ enterSeg ζ i ∧ (ζ σ 0).1 = j} := by
    ext ζ; simp [enterAt, Set.Nonempty]
  have h_measurable_nonempty : MeasurableSet {ζ : Pieces d | (enterAt ζ i j).Nonempty} := by
    rw [h_nonempty_eq]
    refine MeasurableSet.iUnion ?_
    intro σ
    have h_enterSeg : MeasurableSet {ζ : Pieces d | σ ∈ enterSeg ζ i} :=
      measurableSet_mem_enterSeg i σ
    have h_fst_eq_j : MeasurableSet {ζ : Pieces d | (ζ σ 0).1 = j} :=
      (measurable_fst.comp ((measurable_pi_apply 0).comp (measurable_pi_apply σ)))
        (measurableSet_singleton j)
    exact h_enterSeg.inter h_fst_eq_j
  have h_measurable_stage_compl : MeasurableSet {ζ : Pieces d | ([j], 0) ∉ stage ζ i} := by
    have h_stage : MeasurableSet {ζ : Pieces d | ([j], 0) ∈ stage ζ i} :=
      measurableSet_mem_stage i ([j], 0)
    exact h_stage.compl
  exact h_measurable_nonempty.inter h_measurable_stage_compl

theorem FrogModel.measurableSet_mem_enterSet {d : ℕ} (i : ℕ) (j : Fin d) (a : Seg d) :
    MeasurableSet {ζ : Pieces d | a ∈ enterSet ζ i j} := by
  have h_mem_enterSeg : MeasurableSet {ζ : Pieces d | a ∈ enterSeg ζ i} :=
    FrogModel.measurableSet_mem_enterSeg i a
  have h_coord (σ : Seg d) : MeasurableSet {ζ : Pieces d | (ζ σ 0).1 = j} := by
    have h_meas : Measurable (fun (ζ : Pieces d) => (ζ σ 0).1) :=
      Measurable.comp measurable_fst (Measurable.comp (measurable_pi_apply (0 : ℕ)) (measurable_pi_apply (σ : Seg d)))
    exact h_meas (MeasurableSet.singleton j)
  have h_mem_enterAt : MeasurableSet {ζ : Pieces d | a ∈ enterAt ζ i j} := by
    have h_eq : {ζ : Pieces d | a ∈ enterAt ζ i j} = {ζ : Pieces d | a ∈ enterSeg ζ i} ∩ {ζ : Pieces d | (ζ a 0).1 = j} := by
      ext ζ; simp [FrogModel.enterAt]
    rw [h_eq]
    exact MeasurableSet.inter h_mem_enterSeg (h_coord a)
  have h_nonempty : MeasurableSet {ζ : Pieces d | (enterAt ζ i j).Nonempty} := by
    have h_eq : {ζ : Pieces d | (enterAt ζ i j).Nonempty} = ⋃ (σ : Seg d), {ζ : Pieces d | σ ∈ enterAt ζ i j} := by
      ext ζ; simp [Set.Nonempty]
    rw [h_eq]
    have h_count : Countable (Seg d) := inferInstance
    refine MeasurableSet.iUnion ?_
    intro σ
    have h_eq2 : {ζ : Pieces d | σ ∈ enterAt ζ i j} = {ζ : Pieces d | σ ∈ enterSeg ζ i} ∩ {ζ : Pieces d | (ζ σ 0).1 = j} := by
      ext ζ; simp [FrogModel.enterAt]
    rw [h_eq2]
    exact MeasurableSet.inter (FrogModel.measurableSet_mem_enterSeg i σ) (h_coord σ)
  have h_eq_singleton : MeasurableSet {ζ : Pieces d | a = ([j], 0)} := by
    by_cases h : a = ([j], 0)
    · subst h
      have : {ζ : Pieces d | ([j], 0) = ([j], 0)} = Set.univ := by
        ext ζ; simp
      rw [this]
      exact MeasurableSet.univ
    · have h_empty : {ζ : Pieces d | a = ([j], 0)} = (∅ : Set (Pieces d)) := by
        ext ζ; simp [h]
      rw [h_empty]
      exact MeasurableSet.empty
  have h_not_stage : MeasurableSet {ζ : Pieces d | ([j], 0) ∉ stage ζ i} := by
    have h_stage : MeasurableSet {ζ : Pieces d | ([j], 0) ∈ stage ζ i} :=
      FrogModel.measurableSet_mem_stage i ([j], 0)
    exact MeasurableSet.compl h_stage
  have h_goal : {ζ : Pieces d | a ∈ enterSet ζ i j} = {ζ : Pieces d | (enterAt ζ i j).Nonempty ∧ (a ∈ enterAt ζ i j ∨ (a = ([j], 0) ∧ ([j], 0) ∉ stage ζ i))} := by
    ext ζ; simp [FrogModel.enterSet]
  rw [h_goal]
  have h_split : {ζ : Pieces d | (enterAt ζ i j).Nonempty ∧ (a ∈ enterAt ζ i j ∨ (a = ([j], 0) ∧ ([j], 0) ∉ stage ζ i))} =
      {ζ : Pieces d | (enterAt ζ i j).Nonempty} ∩ ({ζ : Pieces d | a ∈ enterAt ζ i j} ∪ ({ζ : Pieces d | a = ([j], 0)} ∩ {ζ : Pieces d | ([j], 0) ∉ stage ζ i})) := by
    ext ζ; simp
  rw [h_split]
  exact MeasurableSet.inter h_nonempty (MeasurableSet.union h_mem_enterAt (MeasurableSet.inter h_eq_singleton h_not_stage))

theorem FrogModel.measurable_starSample {d : ℕ} (j : Fin d) (a : Seg d) :
    Measurable (starSample (d := d) j a) := by
  rw [measurable_pi_iff]
  intro v
  unfold starSample
  split_ifs with h
  · -- h : v = [] ∧ a.start = root
    rw [measurable_pi_iff]
    intro n
    have ha : a.start = root := h.2
    unfold starSeq
    simp [ha]
    -- Now we need Measurable (fun ρ => (ρ a) (n + 1))
    exact (measurable_pi_apply (n + 1)).comp (measurable_pi_apply a)
  · -- h : ¬ (v = [] ∧ a.start = root)
    exact measurable_pi_apply (v ++ [j], 0)

theorem FrogModel.measurable_stageR {d : ℕ} (i : ℕ) : Measurable fun ζ : Pieces d => stageR ζ i := by
  -- express stageR as a tsum of measurable indicators
  have h_eq : (fun (ζ : Pieces d) => stageR ζ i) = fun ζ => (∑' (σ : Seg d), (enterSeg ζ i).indicator (fun _ => (1 : ℝ≥0∞)) σ) := by
    ext ζ
    dsimp [stageR]
    rw [(ENNReal.tsum_set_one _).symm]
    exact tsum_subtype (enterSeg ζ i) (fun _ => (1 : ℝ≥0∞))
  rw [h_eq]
  refine Measurable.tsum ?_
  intro σ
  have h_meas : MeasurableSet {ζ : Pieces d | σ ∈ enterSeg ζ i} :=
    FrogModel.measurableSet_mem_enterSeg i σ
  -- the function is ζ ↦ 1 if σ ∈ enterSeg ζ i else 0
  -- which equals {ζ | σ ∈ enterSeg ζ i}.indicator (fun _ => 1) ζ
  have h : Measurable (({ζ : Pieces d | σ ∈ enterSeg ζ i}.indicator fun (_ : Pieces d) => (1 : ℝ≥0∞))) :=
    (measurable_const (a := (1 : ℝ≥0∞))).indicator h_meas
  -- need to relate this to fun ζ => (enterSeg ζ i).indicator (fun _ => 1) σ
  convert h using 1
  ext ζ
  simp [Set.indicator]

theorem FrogModel.measurable_stageW {d : ℕ} (i : ℕ) : Measurable fun ζ : Pieces d => stageW ζ i := by
  classical
  -- Express stageW as a finite sum over Fin d of indicators
  have h_eq : (fun ζ : Pieces d => stageW ζ i) = (fun ζ => Finset.sum Finset.univ fun j => if ((enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i) then (1 : ℝ≥0∞) else 0) := by
    ext ζ
    dsimp [stageW]
    set p := fun j : Fin d => (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i with hp
    have h_set_eq : {j | p j} = ((Finset.filter p Finset.univ : Finset (Fin d)) : Set (Fin d)) := by
      ext j; simp [p]
    have h_card : (Finset.filter p Finset.univ).card = ∑ j ∈ Finset.univ, if p j then 1 else 0 :=
      Finset.card_filter p Finset.univ
    calc
      (({j | p j} : Set (Fin d)).encard : ℝ≥0∞)
          = (((Finset.filter p Finset.univ : Finset (Fin d)) : Set (Fin d)).encard : ℝ≥0∞) := by rw [h_set_eq]
      _ = ((Finset.filter p Finset.univ).card : ℝ≥0∞) := by
        simpa using congrArg (fun x : ℕ∞ => (x : ℝ≥0∞)) (Set.encard_coe_eq_coe_finsetCard (Finset.filter p Finset.univ))
      _ = ((∑ j ∈ Finset.univ, if p j then 1 else 0 : ℕ) : ℝ≥0∞) := by rw [h_card]
      _ = (∑ j ∈ Finset.univ, if p j then (1 : ℝ≥0∞) else 0) := by simp
      _ = (∑ j : Fin d, if p j then (1 : ℝ≥0∞) else 0) := by simp
  rw [h_eq]
  refine Finset.measurable_sum Finset.univ fun j hj => ?_
  -- Each term is measurable: it's the indicator of a measurable set
  have h_meas : MeasurableSet {ζ : Pieces d | (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i} :=
    measurableSet_enterNew i j
  have h_term : (fun ζ : Pieces d => if ((enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i) then (1 : ℝ≥0∞) else 0) =
      ({ζ : Pieces d | (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i} : Set (Pieces d)).indicator (fun (_ : Pieces d) => (1 : ℝ≥0∞)) := by
    ext ζ
    simp [Set.indicator]
  rw [h_term]
  exact (measurable_indicator_const_iff (1 : ℝ≥0∞)).mpr h_meas

theorem FrogModel.enterSet_root {d : ℕ} (ζ : Pieces d) (i : ℕ) (j : Fin d) (a : Seg d)
    (ha : a.start = root) : a ∈ enterSet ζ i j ↔ a ∈ enterSeg ζ i ∧ (ζ a 0).1 = j := by
  constructor
  · intro h
    rcases h with ⟨h_nonempty, h_or⟩
    rcases h_or with (h_at | h_eq)
    · rcases h_at with ⟨h_seg, h_step⟩
      exact ⟨h_seg, h_step⟩
    · rcases h_eq with ⟨h_eq', h_not_stage⟩
      have h_contra : Seg.start ([j], 0) = root := by
        calc
          Seg.start ([j], 0) = Seg.start a := by rw [h_eq']
          _ = root := ha
      have h_start_j : Seg.start ([j], 0) = (j :: []) := by
        simp [Seg.start]
      rw [h_start_j] at h_contra
      have h_root : root = ([] : Vertex d) := by
        simp [root]
      rw [h_root] at h_contra
      have h_ne : (j :: []) ≠ [] := by simp
      exact absurd h_contra h_ne
  · intro ⟨h_seg, h_step⟩
    have h_at : a ∈ enterAt ζ i j := by
      dsimp [enterAt]
      exact ⟨h_seg, h_step⟩
    have h_nonempty : (enterAt ζ i j).Nonempty := ⟨a, h_at⟩
    exact ⟨h_nonempty, Or.inl h_at⟩

theorem FrogModel.enterSet_nonroot {d : ℕ} (ζ : Pieces d) (i : ℕ) (j : Fin d) (a : Seg d)
    (ha : a.start ≠ root) :
    a ∈ enterSet ζ i j ↔ a = ([j], 0) ∧ (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i := by
  constructor
  · intro h
    rcases h with ⟨h_nonempty, h_mem⟩
    have h_not_enterAt : a ∉ enterAt ζ i j := by
      intro h_a_enterAt
      have h_enterSeg : a ∈ enterSeg ζ i := h_a_enterAt.1
      have h_start : a.start = root := enterSeg_start ζ i a h_enterSeg
      exact ha h_start
    rcases h_mem with (h_a_enterAt | h_pair)
    · exact absurd h_a_enterAt h_not_enterAt
    · rcases h_pair with ⟨h_eq, h_not_stage⟩
      exact ⟨h_eq, h_nonempty, h_not_stage⟩
  · intro ⟨h_eq, h_nonempty, h_not_stage⟩
    subst h_eq
    refine ⟨h_nonempty, ?_⟩
    right
    exact ⟨rfl, h_not_stage⟩

theorem FrogModel.starSample_refresh_enter {d : ℕ} (ζ ζ' : Pieces d) (i : ℕ) (j : Fin d) :
    starSample j ([j], 0) (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ') =
      starSample j ([j], 0) (FrogModel.Stage.refresh (fun ζ => stage ζ i ∪ enterSeg ζ i) ζ ζ') := by
  funext v
  unfold starSample
  have h_start_ne_root : Seg.start ([j], 0) ≠ root := by
    unfold Seg.start root
    simp
  simp [h_start_ne_root]
  have h_not_enter : (v ++ [j], 0) ∉ enterSeg ζ i := by
    intro h
    have h_start := enterSeg_start ζ i (v ++ [j], 0) h
    have h_start_val : Seg.start (v ++ [j], 0) = v ++ [j] := rfl
    rw [h_start_val] at h_start
    have h_ne : v ++ [j] ≠ [] := by simp
    exact h_ne h_start
  simp [FrogModel.Stage.refresh]
  by_cases h : (v ++ [j], 0) ∈ stage ζ i
  · simp [h]
  · have h_not_union : (v ++ [j], 0) ∉ stage ζ i ∪ enterSeg ζ i := by
      intro h'; rcases h' with (h' | h')
      · exact h h'
      · exact h_not_enter h'
    simp [h, h_not_union]

theorem FrogModel.map_starSample_enter {d : ℕ} [NeZero d] (j : Fin d) :
    (piecesMeasure d).map (starSample j ([j], 0)) = frogMeasure d := by
  have hstart : ([j] : Vertex d) ≠ root := by
    simp [root]
  have h_eq : starSample j ([j], 0) = fun ρ v => ρ ((v ++ [j], 0) : Seg d) := by
    funext ρ
    funext v
    funext x
    unfold starSample
    have hcond : ¬ (v = [] ∧ Seg.start ([j], 0) = root) := by
      rintro ⟨hv, hseg⟩
      apply hstart
      simpa [Seg.start] using hseg
    simp [hcond]
  rw [h_eq]
  have h_inj : Function.Injective (fun (v : Vertex d) => ((v ++ [j], 0) : Seg d)) := by
    intro v1 v2 h
    apply_fun Prod.fst at h
    simpa using List.append_cancel_right h
  rw [piecesMeasure, frogMeasure]
  exact FrogModel.infinitePi_map_comp_injective (Measure.infinitePi fun _ : ℕ => stepLaw d)
    (fun v => (v ++ [j], 0)) h_inj

/-- The first step of a segment `a` starting at the root, and the sample of `T*` attached to `a`
(the rest of `a`, the segments `(v ++ [j], 0)`), are independent with laws `stepLaw d` and
`frogMeasure d`. -/
theorem FrogModel.map_pair_starSample {d : ℕ} [NeZero d] (j : Fin d) (a : Seg d)
    (ha : a.start = root) :
    (piecesMeasure d).map (fun ρ => (ρ a 0, starSample j a ρ)) =
      (stepLaw d).prod (frogMeasure d) := by
  classical
  -- flat coordinates: the step `n` of piece `σ` is the coordinate `(σ, n)`
  let e : Vertex d × ℕ → Seg d × ℕ := fun p =>
    if p.1 = [] then (a, p.2 + 1) else ((p.1 ++ [j], 0), p.2)
  have hne : ∀ v : Vertex d, ((v ++ [j], 0) : Seg d) ≠ a := by
    intro v h
    have : Seg.start ((v ++ [j], 0) : Seg d) = root := h ▸ ha
    simp [Seg.start, root] at this
  have he : Function.Injective e := by
    rintro ⟨v, n⟩ ⟨v', n'⟩ h
    by_cases hv : v = [] <;> by_cases hv' : v' = [] <;>
      simp only [e, hv, hv', ite_true, ite_false, Prod.mk.injEq] at h
    · simp_all
    · exact absurd h.1.symm (hne v')
    · exact absurd h.1 (hne v)
    · obtain ⟨⟨h1, -⟩, h2⟩ := h
      simp only [Prod.mk.injEq]
      exact ⟨List.append_cancel_right h1, h2⟩
  have hi₀ : ∀ p, e p ≠ (a, 0) := by
    rintro ⟨v, n⟩ h
    by_cases hv : v = []
    · simp [e, hv] at h
    · simp only [e, hv, ite_false, Prod.mk.injEq] at h
      exact hne v h.1
  have hpair := FrogModel.infinitePi_map_pair_injective (stepLaw d) e he (a, 0) hi₀
  have hcurry_p : (Measure.infinitePi fun _ : Seg d × ℕ => stepLaw d).map
      (MeasurableEquiv.curry (Seg d) ℕ (Step d)) = piecesMeasure d :=
    Measure.infinitePi_map_curry (fun (_ : Seg d) (_ : ℕ) => stepLaw d)
  have hcurry_f : (Measure.infinitePi fun _ : Vertex d × ℕ => stepLaw d).map
      (MeasurableEquiv.curry (Vertex d) ℕ (Step d)) = frogMeasure d :=
    Measure.infinitePi_map_curry (fun (_ : Vertex d) (_ : ℕ) => stepLaw d)
  have hfun : (fun ρ : Pieces d => (ρ a 0, starSample j a ρ)) ∘
      (MeasurableEquiv.curry (Seg d) ℕ (Step d)) =
      Prod.map id (MeasurableEquiv.curry (Vertex d) ℕ (Step d)) ∘
        (fun W : Seg d × ℕ → Step d => (W (a, 0), fun p => W (e p))) := by
    funext W
    simp only [Function.comp, Prod.map, id, MeasurableEquiv.coe_curry]
    refine Prod.ext rfl ?_
    funext v n
    by_cases hv : v = []
    · simp [starSample, starSeq, hv, ha, e, Function.curry]
    · simp [starSample, hv, e, Function.curry]
  have hm1 : Measurable (fun ρ : Pieces d => (ρ a 0, starSample j a ρ)) :=
    (measurable_pi_apply 0 |>.comp (measurable_pi_apply a)).prodMk
      (FrogModel.measurable_starSample j a)
  have hg : Measurable (fun W : Seg d × ℕ → Step d => (W (a, 0), fun p => W (e p))) :=
    (measurable_pi_apply _).prodMk (Measurable.of_eval fun p => measurable_pi_apply _)
  have hc : Measurable
      (Prod.map (id : Step d → Step d) (MeasurableEquiv.curry (Vertex d) ℕ (Step d))) :=
    measurable_id.prodMap (MeasurableEquiv.measurable _)
  rw [← hcurry_p, Measure.map_map hm1 (MeasurableEquiv.measurable _), hfun,
    ← Measure.map_map hc hg, hpair, ← hcurry_f,
    ← Measure.map_prod_map _ _ measurable_id (MeasurableEquiv.measurable _), Measure.map_id]

/-- The vertex of `T*` of the segment `(v ++ [j], 0)` is `v`. -/
theorem FrogModel.starVertex_append {d : ℕ} (v : Vertex d) (j : Fin d) :
    starVertex ((v ++ [j], 0) : Seg d) = v := by
  simp [starVertex, Seg.start, root]

/-- The vertex of `T*` of a segment of `A_j` is the root `r = []`. -/
theorem FrogModel.starVertex_of_enter {d : ℕ} (j : Fin d) (a : Seg d)
    (ha : a.start = root ∨ a = ([j], 0)) : starVertex a = [] := by
  rcases ha with ha | rfl
  · simp [starVertex, ha]
  · simpa using FrogModel.starVertex_append (d := d) [] j

/-- **Lemma 3.5, deterministic part.** The closed segments of stage `i + 1` are at most the sum,
over the children `[j]` of the root and the segments `a ∈ A_j`, of the frozen counts of the planted
trees attached to `a`, with the pieces of `Σ_i` replaced by arbitrary fresh pieces `ζ'`. -/
theorem FrogModel.stageR_succ_le {d : ℕ} (ζ ζ' : Pieces d) (i : ℕ) :
    stageR ζ (i + 1) ≤ ∑' j : Fin d, ∑' a : Seg d, (enterSet ζ i j).indicator
      (fun a => frozenCount
        (starSample j a (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ'))) a := by
  classical
  set N : Set (Seg d) := {τ | τ ∈ stage ζ (i + 1) ∧ τ ∉ stage ζ i ∧ segClosed τ (ζ τ)} with hNdef
  set M : Fin d → Set (Seg d) := fun j => {w | segClosed w (ζ w) ∧ ∃ a ∈ enterSet ζ i j,
    Relation.ReflTransGen (fun a b => segArc a (ζ a) b ∧ b ∉ stage ζ i) a w} with hMdef
  have h1 : stageR ζ (i + 1) ≤ (N.encard : ℝ≥0∞) :=
    ENat.toENNReal_le.2 ((Set.encard_le_encard (enterSeg_succ_subset ζ i)).trans
      (Set.encard_image_le _ _))
  have hN : N ⊆ ⋃ j, M j := by
    rintro τ ⟨hτ1, hτ2, hτ3⟩
    obtain ⟨j, -, σ, hσ, hch⟩ := mem_stage_succ_sub ζ i τ hτ1 hτ2
    exact Set.mem_iUnion.2 ⟨j, hτ3, σ, ⟨⟨σ, hσ⟩, Or.inl hσ⟩, hch⟩
  have h2 : (N.encard : ℝ≥0∞) ≤ ∑' j, ((M j).encard : ℝ≥0∞) := by
    rw [tsum_fintype]
    calc (N.encard : ℝ≥0∞) ≤ ((⋃ j, M j).encard : ℝ≥0∞) :=
          ENat.toENNReal_le.2 (Set.encard_le_encard hN)
      _ ≤ ((∑ j, (M j).encard : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_le.2 (Set.encard_iUnion_le_of_fintype _)
      _ = ∑ j, ((M j).encard : ℝ≥0∞) := map_sum ENat.toENNRealRingHom _ _
  have h3 : ∀ j, ((M j).encard : ℝ≥0∞) ≤ ∑' a, (enterSet ζ i j).indicator
      (fun a => frozenCount
        (starSample j a (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ'))) a := by
    intro j
    refine (reach_union_bound_set (fun a b => segArc a (ζ a) b ∧ b ∉ stage ζ i)
      (enterSet ζ i j) (fun w => segClosed w (ζ w))).trans (ENNReal.tsum_le_tsum fun a => ?_)
    by_cases ha : a ∈ enterSet ζ i j
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
      have hstart := (enterSet_props ζ i j a ha).2.2
      refine encard_le_frozenCount _ _ starVertex ?_ ?_
      · rintro τ₁ ⟨-, hτ₁⟩ τ₂ ⟨-, hτ₂⟩ heq
        have f₁ := (reach_star ζ ζ' i j a ha τ₁ hτ₁).1.2
        have f₂ := (reach_star ζ ζ' i j a ha τ₂ hτ₂).1.2
        rcases f₁ with rfl | ⟨v₁, hv₁, rfl⟩ <;> rcases f₂ with h₂ | ⟨v₂, hv₂, rfl⟩
        · exact h₂.symm
        · rw [starVertex_of_enter j _ hstart, starVertex_append] at heq
          exact absurd heq.symm hv₂
        · rw [h₂, starVertex_of_enter j _ hstart, starVertex_append] at heq
          exact absurd heq hv₁
        · rw [starVertex_append, starVertex_append] at heq
          rw [heq]
      · rintro τ ⟨hc, hτ⟩
        obtain ⟨-, hreach, hfz⟩ := reach_star ζ ζ' i j a ha τ hτ
        exact ⟨hreach, hfz hc⟩
    · simp [Set.indicator_of_notMem ha]
  exact h1.trans (h2.trans (ENNReal.tsum_le_tsum h3))

/-- The pieces of `Σ_i` are measurable stage events. -/
theorem FrogModel.measurableSet_mem_stage_enter {d : ℕ} (i : ℕ) (σ : Seg d) :
    MeasurableSet {ζ : Pieces d | σ ∈ stage ζ i ∪ enterSeg ζ i} :=
  (measurableSet_mem_stage i σ).union (measurableSet_mem_enterSeg i σ)

/-- The frozen count of the planted tree attached to `a`, as a function of the pieces and the fresh
pieces, is measurable. -/
theorem FrogModel.measurable_frozenCount_refresh {d : ℕ} (K : Pieces d → Set (Seg d))
    (hKm : ∀ σ, MeasurableSet {ζ : Pieces d | σ ∈ K ζ}) (j : Fin d) (a : Seg d) :
    Measurable fun p : Pieces d × Pieces d =>
      frozenCount (starSample j a (FrogModel.Stage.refresh K p.1 p.2)) :=
  (measurable_frozenCount d).comp ((measurable_starSample j a).comp
    (FrogModel.Stage.measurable_refresh (X := fun _ : Seg d => ℕ → Step d) K hKm))

/-- **Lemma 3.5, one term.** For a fixed child `[j]` and segment `a`, the planted tree attached to
`a` on the event `a ∈ A_j` contributes `P(a ∈ A_j) E X`. -/
theorem FrogModel.lintegral_enterSet {d : ℕ} [NeZero d] (i : ℕ) (j : Fin d) (a : Seg d) :
    ∫⁻ ζ, {ζ | a ∈ enterSet ζ i j}.indicator (fun ζ => ∫⁻ ζ', frozenCount
        (starSample j a (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ')) ∂piecesMeasure d) ζ
        ∂piecesMeasure d =
      piecesMeasure d {ζ | a ∈ enterSet ζ i j} * meanX d := by
  classical
  set μ := piecesMeasure d with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; unfold piecesMeasure; infer_instance
  have : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  by_cases ha : a.start = root
  · -- `a` starts at the root: the stopping set `Σ_i`, and the first step of `a` is independent
    -- of its planted tree
    set G : Set (Pieces d) := {ζ | a ∈ enterSeg ζ i} with hG
    set c : Set (ℕ → Step d) := {x | (x 0).1 = j}
    have hcm : MeasurableSet c :=
      (measurable_fst.comp (measurable_pi_apply 0)) (measurableSet_singleton j)
    set g : Pieces d → ℝ≥0∞ := fun ρ => c.indicator 1 (ρ a)
    set h : Pieces d → ℝ≥0∞ := fun ρ => c.indicator 1 (ρ a) * frozenCount (starSample j a ρ)
    have hρa : ∀ ζ ζ', ζ ∈ G →
        FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ' a = ζ a := by
      intro ζ ζ' hζ
      have : a ∉ stage ζ i := hζ.2
      simp [FrogModel.Stage.refresh, this]
    have hset : {ζ | a ∈ enterSet ζ i j} = G ∩ {ζ | ζ a ∈ c} := by
      ext ζ; simp [enterSet_root ζ i j a ha, G, c]
    have hmeas_a : Measurable fun ρ : Pieces d => ρ a := measurable_pi_apply a
    have hg : Measurable g := (measurable_one.indicator hcm).comp hmeas_a
    have hh : Measurable h :=
      hg.mul ((measurable_frozenCount d).comp (measurable_starSample j a))
    have hGd := isDetermined_enterSeg (d := d) i a
    have hGm : MeasurableSet G := measurableSet_mem_enterSeg i a
    have hKs := isStoppingSet_stage (d := d) i
    have hKm : ∀ σ, MeasurableSet {ζ : Pieces d | σ ∈ stage ζ i} := measurableSet_mem_stage i
    -- both sides through the refresh lemma
    have hL : ∫⁻ ζ, {ζ | a ∈ enterSet ζ i j}.indicator (fun ζ => ∫⁻ ζ', frozenCount
        (starSample j a (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ')) ∂μ) ζ ∂μ =
        ∫⁻ ζ, G.indicator (fun ζ => ∫⁻ ζ', h (FrogModel.Stage.refresh
          (fun ζ => stage ζ i) ζ ζ') ∂μ) ζ ∂μ := by
      refine lintegral_congr fun ζ => ?_
      rw [hset]
      by_cases hζ : ζ ∈ G
      · rw [Set.indicator_of_mem hζ]
        by_cases hc : ζ a ∈ c
        · rw [Set.indicator_of_mem (Set.mem_inter hζ hc)]
          refine lintegral_congr fun ζ' => ?_
          simp [h, hρa ζ ζ' hζ, Set.indicator_of_mem hc]
        · rw [Set.indicator_of_notMem (fun hm => hc hm.2)]
          symm
          refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun ζ' => ?_)
          simp [h, hρa ζ ζ' hζ, Set.indicator_of_notMem hc]
      · rw [Set.indicator_of_notMem hζ, Set.indicator_of_notMem (fun hm => hζ hm.1)]
    have hR : μ {ζ | a ∈ enterSet ζ i j} = ∫⁻ ζ, G.indicator (fun ζ => ∫⁻ ζ',
        g (FrogModel.Stage.refresh (fun ζ => stage ζ i) ζ ζ') ∂μ) ζ ∂μ := by
      rw [← lintegral_indicator_one (measurableSet_mem_enterSet i j a)]
      refine lintegral_congr fun ζ => ?_
      rw [hset]
      by_cases hζ : ζ ∈ G
      · rw [Set.indicator_of_mem hζ]
        by_cases hc : ζ a ∈ c
        · rw [Set.indicator_of_mem (Set.mem_inter hζ hc)]
          simp [g, hρa _ _ hζ, Set.indicator_of_mem hc]
        · rw [Set.indicator_of_notMem (fun hm => hc hm.2)]
          simp [g, hρa _ _ hζ, Set.indicator_of_notMem hc]
      · rw [Set.indicator_of_notMem hζ, Set.indicator_of_notMem (fun hm => hζ hm.1)]
    rw [hL, hR, hμ, piecesMeasure,
      FrogModel.Stage.lintegral_refresh _ _ hKs hKm G hGd hGm h hh,
      FrogModel.Stage.lintegral_refresh _ _ hKs hKm G hGd hGm g hg, mul_assoc]
    congr 1
    -- `E h = E g * E X` by the joint law of the first step of `a` and its planted tree
    have hpair := map_pair_starSample j a ha
    have hm1 : Measurable fun ρ : Pieces d => (ρ a 0, starSample j a ρ) :=
      ((measurable_pi_apply 0).comp hmeas_a).prodMk (measurable_starSample j a)
    set c₀ : Set (Step d) := {s | s.1 = j}
    have hc₀ : MeasurableSet c₀ := measurable_fst (measurableSet_singleton j)
    have hF1 : Measurable fun p : Step d × Sample d => c₀.indicator 1 p.1 * frozenCount p.2 :=
      ((measurable_one.indicator hc₀).comp measurable_fst).mul
        ((measurable_frozenCount d).comp measurable_snd)
    have hF2 : Measurable fun p : Step d × Sample d => c₀.indicator 1 p.1 * (1 : ℝ≥0∞) :=
      ((measurable_one.indicator hc₀).comp measurable_fst).mul measurable_const
    have e1 : ∫⁻ ρ, h ρ ∂piecesMeasure d = ∫⁻ p, c₀.indicator 1 p.1 * frozenCount p.2
        ∂((piecesMeasure d).map fun ρ : Pieces d => (ρ a 0, starSample j a ρ)) :=
      (lintegral_map hF1 hm1).symm
    have e2 : ∫⁻ ρ, g ρ ∂piecesMeasure d = ∫⁻ p, c₀.indicator 1 p.1 * (1 : ℝ≥0∞)
        ∂((piecesMeasure d).map fun ρ : Pieces d => (ρ a 0, starSample j a ρ)) := by
      refine (lintegral_congr fun ρ => ?_).trans (lintegral_map hF2 hm1).symm
      simp [g, c, c₀, Set.indicator_apply]
    rw [← piecesMeasure, e1, e2, hpair,
      lintegral_prod_mul ((measurable_one.indicator hc₀).aemeasurable)
        (measurable_frozenCount d).aemeasurable,
      lintegral_prod_mul ((measurable_one.indicator hc₀).aemeasurable) aemeasurable_const]
    simp [meanX]
  · -- `a` does not start at the root: only `a = ([j], 0)` matters, with the stopping set
    -- `Σ_i ∪ Z_i`
    by_cases haj : a = ([j], 0)
    · subst haj
      set G : Set (Pieces d) := {ζ | (enterAt ζ i j).Nonempty ∧ ([j], 0) ∉ stage ζ i}
      have hset : {ζ | (([j], 0) : Seg d) ∈ enterSet ζ i j} = G := by
        ext ζ; simp [enterSet_nonroot ζ i j _ ha, G]
      have hGd := isDetermined_enterNew (d := d) i j
      have hGm : MeasurableSet G := measurableSet_enterNew i j
      have hKs := isStoppingSet_stage_enter (d := d) i
      have hKm : ∀ σ, MeasurableSet {ζ : Pieces d | σ ∈ stage ζ i ∪ enterSeg ζ i} :=
        measurableSet_mem_stage_enter i
      have hF : Measurable fun ρ : Pieces d => frozenCount (starSample j ([j], 0) ρ) :=
        (measurable_frozenCount d).comp (measurable_starSample j _)
      simp_rw [hset, starSample_refresh_enter]
      rw [hμ, piecesMeasure, FrogModel.Stage.lintegral_refresh _ _ hKs hKm G hGd hGm _ hF,
        ← piecesMeasure, ← lintegral_map (measurable_frozenCount d) (measurable_starSample j _),
        map_starSample_enter, meanX]
    · have hset : {ζ | a ∈ enterSet ζ i j} = ∅ := by
        ext ζ; simp [enterSet_nonroot ζ i j a ha, haj]
      simp [hset]

/-- **Lemma 3.5 (integrated form).** `E R_(i+1) ≤ E X (E R_i + E W_(i+1))`. -/
theorem FrogModel.lemma31 {d : ℕ} [NeZero d] (i : ℕ) :
    ∫⁻ ζ, stageR ζ (i + 1) ∂piecesMeasure d ≤
      meanX d * (∫⁻ ζ, stageR ζ i ∂piecesMeasure d + ∫⁻ ζ, stageW ζ i ∂piecesMeasure d) := by
  classical
  set μ := piecesMeasure d with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; unfold piecesMeasure; infer_instance
  have hKm : ∀ σ, MeasurableSet {ζ : Pieces d | σ ∈ stage ζ i} := measurableSet_mem_stage i
  set F : Fin d → Seg d → Pieces d × Pieces d → ℝ≥0∞ := fun j a p =>
    frozenCount (starSample j a (FrogModel.Stage.refresh (fun ζ => stage ζ i) p.1 p.2))
  have hF : ∀ j a, Measurable (F j a) := fun j a =>
    measurable_frozenCount_refresh (fun ζ => stage ζ i) hKm j a
  set T : Fin d → Seg d → Pieces d → ℝ≥0∞ := fun j a =>
    {ζ | a ∈ enterSet ζ i j}.indicator fun ζ => ∫⁻ ζ', F j a (ζ, ζ') ∂μ
  have hT : ∀ j a, Measurable (T j a) := fun j a =>
    ((hF j a).lintegral_prod_right').indicator (measurableSet_mem_enterSet i j a)
  -- the deterministic bound, integrated over the fresh pieces
  have h1 : ∀ ζ, stageR ζ (i + 1) ≤ ∑' j, ∑' a, T j a ζ := by
    intro ζ
    have hmeas : ∀ j a, Measurable fun ζ' : Pieces d =>
        (enterSet ζ i j).indicator (fun a => F j a (ζ, ζ')) a := by
      intro j a
      by_cases ha : a ∈ enterSet ζ i j
      · simp only [Set.indicator_of_mem ha]
        exact (hF j a).comp measurable_prodMk_left
      · simp only [Set.indicator_of_notMem ha]
        exact measurable_const
    calc stageR ζ (i + 1) = ∫⁻ _ : Pieces d, stageR ζ (i + 1) ∂μ := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ ζ', ∑' j, ∑' a, (enterSet ζ i j).indicator (fun a => F j a (ζ, ζ')) a ∂μ :=
          lintegral_mono fun ζ' => stageR_succ_le ζ ζ' i
      _ = ∑' j, ∑' a, ∫⁻ ζ', (enterSet ζ i j).indicator (fun a => F j a (ζ, ζ')) a ∂μ := by
          rw [lintegral_tsum fun j =>
            (Measurable.tsum fun a => hmeas j a).aemeasurable]
          exact tsum_congr fun j => lintegral_tsum fun a => (hmeas j a).aemeasurable
      _ = ∑' j, ∑' a, T j a ζ := by
          refine tsum_congr fun j => tsum_congr fun a => ?_
          by_cases ha : a ∈ enterSet ζ i j
          · simp [T, ha]
          · simp [T, ha]
  -- each term is `P(a ∈ A_j) E X`
  have h2 : ∫⁻ ζ, ∑' j, ∑' a, T j a ζ ∂μ =
      meanX d * ∫⁻ ζ, ∑' j, ∑' a, {ζ | a ∈ enterSet ζ i j}.indicator 1 ζ ∂μ := by
    rw [lintegral_tsum fun j => (Measurable.tsum fun a => hT j a).aemeasurable,
      lintegral_tsum fun j => (Measurable.tsum fun a =>
        measurable_one.indicator (measurableSet_mem_enterSet i j a)).aemeasurable,
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [lintegral_tsum fun a => (hT j a).aemeasurable, lintegral_tsum fun a =>
      (measurable_one.indicator (measurableSet_mem_enterSet i j a)).aemeasurable,
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun a => ?_
    rw [lintegral_indicator_one (measurableSet_mem_enterSet i j a), mul_comm]
    exact lintegral_enterSet i j a
  -- the count of the planted trees
  have h3 : ∀ ζ, ∑' j, ∑' a, {ζ | a ∈ enterSet ζ i j}.indicator (1 : Pieces d → ℝ≥0∞) ζ =
      stageR ζ i + stageW ζ i := by
    intro ζ
    rw [← count_enterSet ζ i]
    refine tsum_congr fun j => ?_
    rw [← ENNReal.tsum_set_one,
      show (∑' x : ↑(enterSet ζ i j), (1 : ℝ≥0∞)) =
        ∑' a, (enterSet ζ i j).indicator (fun _ => (1 : ℝ≥0∞)) a from
        tsum_subtype (enterSet ζ i j) (fun _ => (1 : ℝ≥0∞))]
    refine tsum_congr fun a => ?_
    by_cases ha : a ∈ enterSet ζ i j <;> simp [ha]
  calc ∫⁻ ζ, stageR ζ (i + 1) ∂μ ≤ ∫⁻ ζ, ∑' j, ∑' a, T j a ζ ∂μ := lintegral_mono h1
    _ = meanX d * ∫⁻ ζ, (stageR ζ i + stageW ζ i) ∂μ := by
        rw [h2]; congr 1; exact lintegral_congr h3
    _ = meanX d * (∫⁻ ζ, stageR ζ i ∂μ + ∫⁻ ζ, stageW ζ i ∂μ) := by
        rw [lintegral_add_left (measurable_stageR i)]
