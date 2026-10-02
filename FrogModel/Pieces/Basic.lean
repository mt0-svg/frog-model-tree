module

public import FrogModel.Pieces.Defs
public import FrogModel.Lemmas.Basic

@[expose] public section

/-!
# Lemmas on the piece space (Sections 2 and 3 of the paper)

- Cut times (`one_le_cut`, `walk_cut`, `walk_ne_root_of_lt_cut`, `cut_le_iff`, `cut_congr`) and
  cumulative cuts (`le_cutSum`, `cutSum_mono`, `segAt_spec`).
- The glued walk follows each piece up to its cut (`walk_glue`), and returns to the root exactly at
  the cut points (`glue_root_iff`).
- The planted tree: `step_append`, `walk_append` (the walk in `T(c)` is the embedded walk on `T*`),
  `walkStar_absorb`.
- Reachability: `reach_union_bound`, `Stage.closure_eq_chains`, `Stage.stages_mono_succ`.
- Measurability: `Stage.measurableSet_closure`, `Stage.measurableSet_stages`,
  `measurableSet_segArc`, `measurableSet_segClosed`, `measurable_frozenCount`.
-/

open MeasureTheory
open scoped ENNReal
open FrogModel

theorem FrogModel.one_le_cut {d : ℕ} (v : Vertex d) (x : ℕ → Step d) : 1 ≤ cut v x := by
  unfold cut
  apply le_sInf
  intro b hb
  rcases hb with ⟨n, hn, rfl⟩
  simp at hn
  exact Nat.cast_le.mpr hn.1

theorem FrogModel.walk_cut {d : ℕ} (v : Vertex d) (x : ℕ → Step d) (n : ℕ)
    (h : cut v x = n) : 1 ≤ n ∧ walk v x n = root := by
  let S : Set ℕ∞ := (fun n : ℕ => (n : ℕ∞)) '' {n | 1 ≤ n ∧ walk v x n = root}
  have h_cut : cut v x = sInf S := rfl
  rw [h_cut] at h
  have hS_nonempty : S.Nonempty := by
    by_contra h_empty
    have h_sInf_top : sInf S = ⊤ := by
      rw [Set.not_nonempty_iff_eq_empty.mp h_empty]
      exact WithTop.sInf_empty
    rw [h_sInf_top] at h
    exact (WithTop.coe_ne_top (a := n)) h.symm
  have h_mem : sInf S ∈ S := csInf_mem hS_nonempty
  rw [h] at h_mem
  rcases h_mem with ⟨m, hm, hm_eq⟩
  have hm_set : 1 ≤ m ∧ walk v x m = root := hm
  rcases hm_set with ⟨hm_le, hm_walk⟩
  have hm_eq' : m = n := (Nat.cast_inj (R := ℕ∞)).mp hm_eq
  rw [hm_eq'] at hm_le hm_walk
  exact ⟨hm_le, hm_walk⟩

theorem FrogModel.walk_ne_root_of_lt_cut {d : ℕ} (v : Vertex d) (x : ℕ → Step d) (n : ℕ)
    (h1 : 1 ≤ n) (h : (n : ℕ∞) < cut v x) : walk v x n ≠ root := by
  intro hwalk
  have hmem : (n : ℕ∞) ∈ ((fun n : ℕ => (n : ℕ∞)) '' {n | 1 ≤ n ∧ walk v x n = root}) := by
    refine ⟨n, ⟨h1, hwalk⟩, rfl⟩
  have hle := sInf_le hmem
  have : (n : ℕ∞) < (n : ℕ∞) := lt_of_lt_of_le h hle
  exact lt_irrefl _ this

theorem FrogModel.cut_le_iff {d : ℕ} (v : Vertex d) (x : ℕ → Step d) (n : ℕ) :
    cut v x ≤ n ↔ ∃ m, 1 ≤ m ∧ m ≤ n ∧ walk v x m = root := by
  unfold cut
  set S : Set ℕ := {m | 1 ≤ m ∧ walk v x m = root} with hS
  by_cases hSne : S.Nonempty
  · set m := sInf S with hm_def
    have hmS : m ∈ S := Nat.sInf_mem hSne
    have hm1 : 1 ≤ m := hmS.1
    have hmwalk : walk v x m = root := hmS.2
    have h_sInf_eq : sInf ((fun n : ℕ => (n : ℕ∞)) '' S) = (m : ℕ∞) := by
      have h_not_sub : ¬ ((fun n : ℕ => (n : ℕ∞)) '' S) ⊆ ({⊤} : Set ℕ∞) := by
        intro hsub
        obtain ⟨a, ha⟩ := hSne
        have ha' : (a : ℕ∞) ∈ ((fun n : ℕ => (n : ℕ∞)) '' S) := ⟨a, ha, rfl⟩
        have htop : (a : ℕ∞) ∈ ({⊤} : Set ℕ∞) := hsub ha'
        simp at htop
      have h_bdd : BddBelow ((fun n : ℕ => (n : ℕ∞)) '' S) := by
        refine ⟨(0 : ℕ∞), ?_⟩
        rintro y ⟨k, hk, rfl⟩
        simp
      have h_eq := WithTop.sInf_eq h_not_sub h_bdd
      rw [hm_def]
      -- Goal: sInf ((fun n => ↑n) '' S) = (sInf S : ℕ∞)
      -- h_eq : sInf ((fun n => ↑n) '' S) = ↑(sInf ((Nat.cast) ⁻¹' ((fun n => ↑n) '' S)))
      -- Use h_eq to rewrite the goal
      apply h_eq.trans
      -- Goal: ↑(sInf ((Nat.cast) ⁻¹' ((fun n => ↑n) '' S))) = (sInf S : ℕ∞)
      -- i.e., sInf ((Nat.cast) ⁻¹' ((fun n => ↑n) '' S)) = sInf S
      -- i.e., (Nat.cast) ⁻¹' ((fun n => ↑n) '' S) = S
      congr 1
      -- Goal: sInf ((Nat.cast) ⁻¹' ((fun n => ↑n) '' S)) = sInf S
      -- We need to show the arguments are equal
      congr 1
      -- Goal: (Nat.cast) ⁻¹' ((fun n => ↑n) '' S) = S
      -- Now prove this using injectivity of Nat.cast
      have h_inj : Function.Injective (Nat.cast : ℕ → ℕ∞) := by
        intro a b h
        apply Option.some_injective
        simpa [Nat.cast] using h
      exact Set.preimage_image_eq S h_inj
    rw [h_sInf_eq]
    constructor
    · intro hle
      have hm_le_n : m ≤ n := (Nat.cast_le (α := ℕ∞)).mp hle
      exact ⟨m, hm1, hm_le_n, hmwalk⟩
    · intro h
      rcases h with ⟨m', hm1', hmn', hmwalk'⟩
      have hm_le_m' : m ≤ m' := by
        rw [hm_def]
        have hm'S : m' ∈ S := ⟨hm1', hmwalk'⟩
        exact Nat.sInf_le hm'S
      have hm_le_n : m ≤ n := Nat.le_trans hm_le_m' hmn'
      exact (Nat.cast_le (α := ℕ∞)).mpr hm_le_n
  · -- S is empty
    have h_empty : ((fun n : ℕ => (n : ℕ∞)) '' S) = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty] at hSne
      simp [S, hSne]
    have h_sInf_top : sInf ((fun n : ℕ => (n : ℕ∞)) '' S) = ⊤ := by
      rw [h_empty]
      simp
    rw [h_sInf_top]
    constructor
    · intro hle
      simp at hle
    · intro h
      rcases h with ⟨m, hm1, hmn, hmwalk⟩
      exfalso
      apply hSne
      exact ⟨m, hm1, hmwalk⟩

theorem FrogModel.cut_congr {d : ℕ} (v : Vertex d) (x y : ℕ → Step d) (n : ℕ)
    (hxy : ∀ i < n, x i = y i) (h : cut v x ≤ n) : cut v y = cut v x := by
  -- First, prove that walk v x m = walk v y m for all m ≤ n
  have hwalk : ∀ m, m ≤ n → walk v x m = walk v y m := by
    intro m hm
    induction' m with m ih
    · rfl
    · have hm_lt_n : m < n := by omega
      rw [walk, walk, ih (by omega), hxy m hm_lt_n]
  -- Define S = {k | 1 ≤ k ∧ walk v x k = root}
  set S : Set ℕ := {k | 1 ≤ k ∧ walk v x k = root} with hS_def
  -- From h : cut v x ≤ n, we know cut v x ≠ ⊤, so S is nonempty
  have hS_nonempty : S.Nonempty := by
    by_contra h_empty
    have h_empty' : ((fun (k : ℕ) => (k : ℕ∞)) '' S) = ∅ := by
      rw [Set.image_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp h_empty
    have h_sInf_empty : sInf ((fun (k : ℕ) => (k : ℕ∞)) '' S) = ⊤ := by
      rw [h_empty', sInf_empty]
    have h_cut_top : cut v x = ⊤ := by
      rw [FrogModel.cut, h_sInf_empty]
    rw [h_cut_top] at h
    have h_n_lt_top : (n : ℕ∞) < ⊤ := WithTop.coe_lt_top n
    exact not_lt.mpr h h_n_lt_top
  -- Let m₀ be the minimum element of S
  let m₀ := Nat.find hS_nonempty
  have hm₀S : m₀ ∈ S := Nat.find_spec hS_nonempty
  have hm₀_min : ∀ k, k < m₀ → k ∉ S := by
    intro k hk
    exact Nat.find_min hS_nonempty hk
  have hm₀_ge_one : 1 ≤ m₀ := hm₀S.1
  have h_walk_m₀ : walk v x m₀ = root := hm₀S.2
  -- Now we need to show cut v x = (m₀ : ℕ∞)
  have h_cut_eq : cut v x = (m₀ : ℕ∞) := by
    rw [FrogModel.cut]
    apply le_antisymm
    · apply csInf_le
      · refine ⟨0, ?_⟩
        intro a ha
        rcases ha with ⟨k, hk, rfl⟩
        exact zero_le (a := (k : ℕ∞))
      · exact ⟨m₀, hm₀S, rfl⟩
    · apply le_csInf
      · exact ⟨(m₀ : ℕ∞), m₀, hm₀S, rfl⟩
      · intro a ha
        rcases ha with ⟨k, hk, rfl⟩
        have hm₀_le_k : m₀ ≤ k := by
          by_contra! h_lt
          exact hm₀_min k (by omega) hk
        exact (WithTop.coe_le_coe (a := k) (b := m₀)).mpr hm₀_le_k
  -- From h : cut v x ≤ n, we get m₀ ≤ n
  have hm₀_le_n : m₀ ≤ n := by
    rw [h_cut_eq] at h
    exact (WithTop.coe_le_coe (a := n) (b := m₀)).mp h
  -- Now for y: since m₀ ≤ n, we have walk v y m₀ = root
  have h_walk_y_m₀ : walk v y m₀ = root := by
    rw [← hwalk m₀ hm₀_le_n, h_walk_m₀]
  -- And for any k < m₀ with 1 ≤ k, walk v y k ≠ root
  have h_no_early_return_y : ∀ k, 1 ≤ k → k < m₀ → walk v y k ≠ root := by
    intro k hk_ge_one hk_lt
    have hk_not_S : k ∉ S := hm₀_min k hk_lt
    rw [hS_def] at hk_not_S
    have h_not_root : walk v x k ≠ root := by
      intro h_eq
      apply hk_not_S
      exact ⟨hk_ge_one, h_eq⟩
    rw [← hwalk k (by omega)]
    exact h_not_root
  -- Now show cut v y = (m₀ : ℕ∞)
  have h_cut_y_eq : cut v y = (m₀ : ℕ∞) := by
    rw [FrogModel.cut]
    apply le_antisymm
    · apply csInf_le
      · refine ⟨0, ?_⟩
        intro a ha
        rcases ha with ⟨k, hk, rfl⟩
        exact zero_le (a := (k : ℕ∞))
      · have hm₀_in_y_set : m₀ ∈ {n | 1 ≤ n ∧ walk v y n = root} := ⟨hm₀_ge_one, h_walk_y_m₀⟩
        exact ⟨m₀, hm₀_in_y_set, rfl⟩
    · apply le_csInf
      · have hm₀_in_y_set : m₀ ∈ {n | 1 ≤ n ∧ walk v y n = root} := ⟨hm₀_ge_one, h_walk_y_m₀⟩
        exact ⟨(m₀ : ℕ∞), m₀, hm₀_in_y_set, rfl⟩
      · intro a ha
        rcases ha with ⟨k, hk, rfl⟩
        rcases hk with ⟨hk_ge_one, hk_root⟩
        by_contra! h_lt
        have hk_lt_m₀ : k < m₀ := (WithTop.coe_lt_coe (a := m₀) (b := k)).mp h_lt
        exact h_no_early_return_y k hk_ge_one hk_lt_m₀ hk_root
  rw [h_cut_y_eq, h_cut_eq]

theorem FrogModel.le_cutSum {d : ℕ} (ζ : Pieces d) (u : Vertex d) (k : ℕ) :
    (k : ℕ∞) ≤ cutSum ζ u k := by
  induction k with
  | zero =>
    simp [cutSum]
  | succ k ih =>
    have h1 : (1 : ℕ∞) ≤ segCut ζ (u, k) := by
      dsimp [segCut, cut]
      refine le_sInf ?_
      intro b hb
      obtain ⟨n, hn, rfl⟩ := hb
      have h1n : (1 : ℕ) ≤ n := hn.1
      have : (1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h1n
      simpa
    rw [cutSum]
    calc
      (k.succ : ℕ∞) = (k : ℕ∞) + 1 := by simp
      _ ≤ cutSum ζ u k + segCut ζ (u, k) := add_le_add ih h1
      _ = cutSum ζ u (k + 1) := by rw [cutSum]

theorem FrogModel.cutSum_mono {d : ℕ} (ζ : Pieces d) (u : Vertex d) : Monotone (cutSum ζ u) := by
  intro a b h
  induction' h with b h ih
  · rfl
  · rw [cutSum]
    have hseg : 0 ≤ segCut ζ (u, b) := zero_le (a := segCut ζ (u, b))
    exact le_trans ih (le_add_of_nonneg_right hseg)

theorem FrogModel.segAt_spec {d : ℕ} (ζ : Pieces d) (u : Vertex d) (t : ℕ) :
    cutSum ζ u (segAt ζ u t) ≤ t ∧ (t : ℕ∞) < cutSum ζ u (segAt ζ u t + 1) := by
  let K := segAt ζ u t
  let S := (Finset.range (t + 1)).filter fun k => cutSum ζ u (k + 1) ≤ (t : ℕ∞)
  have hK : K = S.card := rfl
  have hS_subset : S ⊆ Finset.range (t + 1) := Finset.filter_subset _ _
  have h_bound : ∀ k ∈ S, k < t + 1 := by
    intro k hk
    exact Finset.mem_range.mp (hS_subset hk)
  have h_not_mem_t : t ∉ S := by
    intro ht
    have h_cut_le : cutSum ζ u (t + 1) ≤ (t : ℕ∞) := (Finset.mem_filter.mp ht).2
    have h_le_cut : (t + 1 : ℕ∞) ≤ cutSum ζ u (t + 1) := le_cutSum ζ u (t + 1)
    have h_lt : (t : ℕ∞) < (t + 1 : ℕ∞) := by
      exact mod_cast Nat.lt_succ_self t
    have : (t : ℕ∞) < (t : ℕ∞) := lt_of_lt_of_le h_lt (le_trans h_le_cut h_cut_le)
    exact lt_irrefl _ this
  have h_down : ∀ k ∈ S, ∀ j, j ≤ k → j ∈ S := by
    intro k hk j hj
    rcases Finset.mem_filter.mp hk with ⟨hk_range, hk_cut⟩
    have hj_range : j ∈ Finset.range (t + 1) := by
      apply Finset.mem_range.mpr
      have hk_lt : k < t + 1 := Finset.mem_range.mp hk_range
      omega
    have hj_cut : cutSum ζ u (j + 1) ≤ (t : ℕ∞) :=
      le_trans (cutSum_mono ζ u (by omega)) hk_cut
    exact Finset.mem_filter.mpr ⟨hj_range, hj_cut⟩
  have hS_eq_rangeK : S = Finset.range K := by
    have h_eq : S = Finset.range (S.card) := by
      ext j
      constructor
      · intro hj
        rw [Finset.mem_range]
        by_contra! h_not_lt
        have h_card_le_j : S.card ≤ j := by omega
        have h_range_subset : Finset.range (j + 1) ⊆ S := by
          intro i hi
          rw [Finset.mem_range] at hi
          have h_le : i ≤ j := by omega
          exact h_down j hj i h_le
        have h_card_range : (Finset.range (j + 1)).card = j + 1 := Finset.card_range _
        have h_card_le : (Finset.range (j + 1)).card ≤ S.card := Finset.card_le_card h_range_subset
        rw [h_card_range] at h_card_le
        omega
      · intro hj
        rw [Finset.mem_range] at hj
        by_contra! h_not_mem
        have hS_subset_range_j : S ⊆ Finset.range j := by
          intro k hk
          rw [Finset.mem_range]
          by_contra! h_not_lt_j
          have h_j_le_k : j ≤ k := by omega
          have : j ∈ S := h_down k hk j h_j_le_k
          exact h_not_mem this
        have h_card_le : S.card ≤ (Finset.range j).card := Finset.card_le_card hS_subset_range_j
        rw [Finset.card_range] at h_card_le
        omega
    rw [← hK] at h_eq
    exact h_eq
  have h_cutSum_K_le_t : cutSum ζ u K ≤ (t : ℕ∞) := by
    by_cases hK_zero : K = 0
    · rw [hK_zero]
      simp [cutSum]
    · have hK_pos : 0 < K := Nat.pos_of_ne_zero hK_zero
      have hK_sub_one_lt_K : K - 1 < K := by
        omega
      have hK_sub_one_mem_S : K - 1 ∈ S := by
        rw [hS_eq_rangeK]
        rw [Finset.mem_range]
        omega
      have h_cut_le : cutSum ζ u ((K - 1) + 1) ≤ (t : ℕ∞) := (Finset.mem_filter.mp hK_sub_one_mem_S).2
      have : (K - 1) + 1 = K := by omega
      rw [this] at h_cut_le
      exact h_cut_le
  have h_t_lt_cutSum_K_plus_one : (t : ℕ∞) < cutSum ζ u (K + 1) := by
    have hK_not_mem_S : K ∉ S := by
      rw [hS_eq_rangeK]
      rw [Finset.mem_range]
      omega
    have h_not_cut_le : ¬ (cutSum ζ u (K + 1) ≤ (t : ℕ∞)) := by
      intro hle
      apply hK_not_mem_S
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        have hK_le_t : K ≤ t := by
          -- From S = range K and S ⊆ range(t+1), we get K ≤ t
          -- Actually, we need to show K ≤ t. Since K ∉ S, and S = range K,
          -- this is always true. But we need K < t+1 for the range membership.
          -- Since K = S.card and S ⊆ range(t+1), we have S.card ≤ t+1.
          -- And since K ∉ S (because S = range K), we have K ≠ t+1 (since t ∈ range(t+1) but t ∉ S).
          -- Wait, we only know K ∉ S, not that t ∉ S... but we proved h_not_mem_t.
          -- Actually, we know K = S.card. And S ⊆ range(t+1) and t ∉ S.
          -- So S ⊆ range t. Hence S.card ≤ t. So K ≤ t.
          have hS_subset_range_t : S ⊆ Finset.range t := by
            intro x hx
            apply Finset.mem_range.mpr
            have hx_lt : x < t + 1 := h_bound x hx
            have hx_ne_t : x ≠ t := by
              intro h_eq
              apply h_not_mem_t
              rw [← h_eq]
              exact hx
            omega
          have h_card_le : S.card ≤ (Finset.range t).card := Finset.card_le_card hS_subset_range_t
          rw [Finset.card_range] at h_card_le
          omega
        omega
      · exact hle
    exact lt_of_not_ge h_not_cut_le
  exact And.intro h_cutSum_K_le_t h_t_lt_cutSum_K_plus_one

theorem FrogModel.walk_glue {d : ℕ} (ζ : Pieces d) (u : Vertex d) (k T n : ℕ)
    (hT : cutSum ζ u k = T) (hn : (n : ℕ∞) ≤ segCut ζ (u, k)) :
    walk u (glue ζ u) (T + n) = walk (Seg.start (u, k)) (ζ (u, k)) n := by
  -- at a time `T + n`, `n` before the cut of segment `k`, the glued step is step `n` of piece `k`
  have hseg : ∀ k T n : ℕ, cutSum ζ u k = T → (n : ℕ∞) < segCut ζ (u, k) →
      glue ζ u (T + n) = ζ (u, k) n := by
    intro k T n hT hn
    have hk : segAt ζ u (T + n) = k := by
      obtain ⟨h1, h2⟩ := segAt_spec ζ u (T + n)
      have hlt : ((T + n : ℕ) : ℕ∞) < cutSum ζ u (k + 1) := by
        rw [show cutSum ζ u (k + 1) = cutSum ζ u k + segCut ζ (u, k) from rfl, hT, Nat.cast_add]
        exact (ENat.add_lt_add_iff_left (ENat.natCast_ne_top T)).2 hn
      rcases lt_trichotomy (segAt ζ u (T + n)) k with h | h | h
      · have hmono := cutSum_mono ζ u (Nat.succ_le_of_lt h)
        rw [hT] at hmono
        exact absurd (lt_of_lt_of_le h2 hmono) (not_lt.2 (by exact_mod_cast Nat.le_add_right T n))
      · exact h
      · have hmono := cutSum_mono ζ u (Nat.succ_le_of_lt h)
        exact absurd (lt_of_lt_of_le hlt (hmono.trans h1)) (lt_irrefl _)
    unfold glue
    rw [hk, hT, ENat.toNat_natCast, Nat.add_sub_cancel_left]
  -- from the start of segment `k`, the glued walk follows its piece up to its cut
  have hrun : ∀ k T : ℕ, cutSum ζ u k = T → walk u (glue ζ u) T = Seg.start (u, k) →
      ∀ n : ℕ, (n : ℕ∞) ≤ segCut ζ (u, k) →
        walk u (glue ζ u) (T + n) = walk (Seg.start (u, k)) (ζ (u, k)) n := by
    intro k T hT hbase n
    induction n with
    | zero => intro _; exact hbase
    | succ n ihn =>
      intro hn
      have hlt : (n : ℕ∞) < segCut ζ (u, k) :=
        lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
      rw [← add_assoc]
      show step (walk u (glue ζ u) (T + n)) (glue ζ u (T + n)) =
        step (walk (Seg.start (u, k)) (ζ (u, k)) n) (ζ (u, k) n)
      rw [ihn hlt.le, hseg k T n hT hlt]
  -- segment `k` starts at time `cutSum ζ u k`, at its start vertex
  have hbase : ∀ k T : ℕ, cutSum ζ u k = T → walk u (glue ζ u) T = Seg.start (u, k) := by
    intro k
    induction k with
    | zero =>
      intro T hT
      have hT0 : T = 0 := by
        have h0 : ((T : ℕ) : ℕ∞) = 0 := hT.symm
        exact_mod_cast h0
      subst hT0
      rfl
    | succ k ihk =>
      intro T hT
      have hsum : cutSum ζ u k + segCut ζ (u, k) = T := hT
      have hne : cutSum ζ u k + segCut ζ (u, k) ≠ ⊤ := by rw [hsum]; exact ENat.natCast_ne_top T
      obtain ⟨T₀, hT₀⟩ := ENat.ne_top_iff_exists.1 (WithTop.add_ne_top.1 hne).1
      obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.1 (WithTop.add_ne_top.1 hne).2
      rw [← hT₀, ← hs, ← Nat.cast_add, Nat.cast_inj] at hsum
      subst hsum
      rw [hrun k T₀ hT₀.symm (ihk T₀ hT₀.symm) s (by rw [← hs])]
      exact (walk_cut _ _ s hs.symm).2
  exact hrun k T hT (hbase k T hT) n hn

theorem FrogModel.glue_root_iff {d : ℕ} (ζ : Pieces d) (u : Vertex d) (t : ℕ) (ht : 1 ≤ t) :
    walk u (glue ζ u) t = root ↔ ∃ k, cutSum ζ u (k + 1) = t := by
  set k := segAt ζ u t
  have hseg := segAt_spec ζ u t
  rcases hseg with ⟨hle, hlt⟩
  have hT_ne_top : cutSum ζ u k ≠ ⊤ := by
    intro htop
    have : (⊤ : ℕ∞) ≤ (t : ℕ∞) := htop ▸ hle
    simp at this
  lift cutSum ζ u k to ℕ using hT_ne_top with T hT_eq
  -- hT_eq : (T : ℕ∞) = cutSum ζ u k
  have hT_eq' : cutSum ζ u k = (T : ℕ∞) := hT_eq.symm
  have hT_le_t : T ≤ t := by
    have : (T : ℕ∞) ≤ (t : ℕ∞) := by rw [← hT_eq']; exact hle
    exact_mod_cast this
  set n := t - T with hndef
  have htn : T + n = t := Nat.add_sub_cancel' hT_le_t
  have hn_lt_cut : (n : ℕ∞) < segCut ζ (u, k) := by
    have hsum : cutSum ζ u (k + 1) = cutSum ζ u k + segCut ζ (u, k) := rfl
    have h_eq : (t : ℕ∞) = (T : ℕ∞) + (n : ℕ∞) := by
      rw [← Nat.cast_add, htn]
    have h_lt : (T : ℕ∞) + (n : ℕ∞) < (T : ℕ∞) + segCut ζ (u, k) := by
      rw [← h_eq, ← hT_eq', ← hsum]; exact hlt
    exact (ENat.add_lt_add_iff_left (by simp : (T : ℕ∞) ≠ ⊤)).mp h_lt
  have hn_le_cut : (n : ℕ∞) ≤ segCut ζ (u, k) := le_of_lt hn_lt_cut
  have hwalk_eq : walk u (glue ζ u) t = walk (Seg.start (u, k)) (ζ (u, k)) n := by
    calc
      walk u (glue ζ u) t = walk u (glue ζ u) (T + n) := by rw [htn]
      _ = walk (Seg.start (u, k)) (ζ (u, k)) n := by rw [walk_glue ζ u k T n hT_eq' hn_le_cut]
  constructor
  · intro hwalk_root
    rw [hwalk_eq] at hwalk_root
    by_cases hn0 : n = 0
    · have hT_eq_t : T = t := by
        rw [hn0, add_zero] at htn; exact htn
      have hk_pos : 1 ≤ k := by
        by_contra! hk0
        -- hk0 : k < 1, so k = 0
        have hk0' : k = 0 := by omega
        rw [hk0'] at hT_eq'
        have : cutSum ζ u 0 = (0 : ℕ∞) := rfl
        rw [this] at hT_eq'
        have : (T : ℕ∞) = (0 : ℕ∞) := hT_eq'.symm
        have hT0 : T = 0 := by exact_mod_cast this
        rw [hT0] at hT_eq_t
        omega
      use k - 1
      have hk_sub : (k - 1) + 1 = k := Nat.sub_add_cancel hk_pos
      rw [hk_sub]
      -- Need: cutSum ζ u k = (t : ℕ∞)
      -- hT_eq' : cutSum ζ u k = (T : ℕ∞)
      -- hT_eq_t : T = t
      rw [hT_eq', hT_eq_t]
    · have hn_pos : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn0)
      have hwalk_ne_root : walk (Seg.start (u, k)) (ζ (u, k)) n ≠ root :=
        walk_ne_root_of_lt_cut (Seg.start (u, k)) (ζ (u, k)) n hn_pos hn_lt_cut
      exact absurd hwalk_root hwalk_ne_root
  · intro ⟨j, hj⟩
    have hj_fin : cutSum ζ u j ≠ ⊤ := by
      intro htop
      have : cutSum ζ u (j + 1) = ⊤ := by
        rw [show cutSum ζ u (j + 1) = cutSum ζ u j + segCut ζ (u, j) from rfl, htop]; simp
      rw [hj] at this; simp at this
    lift cutSum ζ u j to ℕ using hj_fin with T' hT'_eq
    -- hT'_eq : (T' : ℕ∞) = cutSum ζ u j
    have hT'_eq' : cutSum ζ u j = (T' : ℕ∞) := hT'_eq.symm
    have hT'_le_t : T' ≤ t := by
      have : (T' : ℕ∞) ≤ (t : ℕ∞) := by
        rw [← hT'_eq']
        calc
          cutSum ζ u j ≤ cutSum ζ u (j + 1) := by
            rw [show cutSum ζ u (j + 1) = cutSum ζ u j + segCut ζ (u, j) from rfl]
            exact le_add_right le_rfl
          _ = (t : ℕ∞) := hj
      exact_mod_cast this
    set m := t - T' with hmdef
    have hT'm : T' + m = t := Nat.add_sub_cancel' hT'_le_t
    have hseg_eq : segCut ζ (u, j) = (m : ℕ∞) := by
      have hsum : cutSum ζ u (j + 1) = cutSum ζ u j + segCut ζ (u, j) := rfl
      -- From hj: cutSum ζ u (j+1) = (t : ℕ∞)
      -- From hT'_eq': cutSum ζ u j = (T' : ℕ∞)
      -- So (t : ℕ∞) = (T' : ℕ∞) + segCut ζ (u, j)
      have ht_eq : (t : ℕ∞) = (T' : ℕ∞) + segCut ζ (u, j) := by
        rw [← hj, hsum, hT'_eq']
      -- Also: (t : ℕ∞) = (T' : ℕ∞) + (m : ℕ∞) (from hT'm)
      have ht_eq' : (t : ℕ∞) = (T' : ℕ∞) + (m : ℕ∞) := by rw [← Nat.cast_add, hT'm]
      rw [ht_eq'] at ht_eq
      -- Now ht_eq: (T' : ℕ∞) + (m : ℕ∞) = (T' : ℕ∞) + segCut ζ (u, j)
      -- Cancel (T' : ℕ∞) from both sides
      have hT'_ne_top : (T' : ℕ∞) ≠ ⊤ := by simp
      -- Rearrange to use WithTop.add_right_cancel
      have h_eq : segCut ζ (u, j) + (T' : ℕ∞) = (m : ℕ∞) + (T' : ℕ∞) := by
        simpa [add_comm] using ht_eq.symm
      exact WithTop.add_right_cancel hT'_ne_top h_eq
    have hm_le_seg : (m : ℕ∞) ≤ segCut ζ (u, j) := by rw [hseg_eq]
    have hwalk_glue : walk u (glue ζ u) t = walk (Seg.start (u, j)) (ζ (u, j)) m := by
      calc
        walk u (glue ζ u) t = walk u (glue ζ u) (T' + m) := by rw [hT'm]
        _ = walk (Seg.start (u, j)) (ζ (u, j)) m := by rw [walk_glue ζ u j T' m hT'_eq' hm_le_seg]
    rw [hwalk_glue]
    have hcut : cut (Seg.start (u, j)) (ζ (u, j)) = (m : ℕ∞) := by
      rw [← hseg_eq, show segCut ζ (u, j) = cut (Seg.start (u, j)) (ζ (u, j)) from rfl]
    have hwalk_cut := walk_cut (Seg.start (u, j)) (ζ (u, j)) m hcut
    rcases hwalk_cut with ⟨_, hwalk_root⟩
    exact hwalk_root

theorem FrogModel.step_append {d : ℕ} (c : Fin d) (v : Vertex d) (ξ : Step d) :
    step (v ++ [c]) ξ = embedStar c (stepStar (some v) ξ) := by
  cases v with
  | nil =>
    simp only [List.nil_append]
    by_cases h : ξ.2 = 0
    · simp [step, stepStar, embedStar, h, root]
    · simp [step, stepStar, embedStar, h, root]
  | cons c' w =>
    simp only [List.cons_append]
    by_cases h : ξ.2 = 0
    · simp [step, stepStar, embedStar, h]
    · simp [step, stepStar, embedStar, h]

theorem FrogModel.walk_append {d : ℕ} (c : Fin d) (v : Vertex d) (x : ℕ → Step d) (n : ℕ)
    (h : ∀ i < n, walkStar (some v) x i ≠ none) :
    walk (v ++ [c]) x n = embedStar c (walkStar (some v) x n) := by
  induction' n with n ih
  · rfl
  · have hn : walkStar (some v) x n ≠ none := h n (Nat.lt_succ_self n)
    match w : walkStar (some v) x n with
    | none => exact (hn w).elim
    | some w' =>
      have hn' : ∀ i < n, walkStar (some v) x i ≠ none := by
        intro i hi
        apply h i
        exact Nat.lt_of_lt_of_le hi (Nat.le_succ n)
      rw [walk, walkStar, ih hn', w]
      simp [embedStar, step_append]

theorem FrogModel.walkStar_absorb {d : ℕ} (v : Option (Vertex d)) (x : ℕ → Step d) (n m : ℕ)
    (h : walkStar v x n = none) (hm : n ≤ m) : walkStar v x m = none := by
  refine Nat.le_induction h (fun k hk hk' => ?_) m hm
  dsimp [walkStar]
  rw [hk']
  simp [stepStar]

namespace FrogModel

private lemma refl_trans_gen_restrict_last {α : Type*} {r : α → α → Prop} {A : Finset α} {a w : α}
    (h : Relation.ReflTransGen r a w) (ha : a ∈ A) :
    ∃ a' ∈ A, Relation.ReflTransGen (fun x y => r x y ∧ y ∉ (A : Set α)) a' w := by
  induction h with
  | refl =>
      exact ⟨a, ha, Relation.ReflTransGen.refl (r := fun x y => r x y ∧ y ∉ (A : Set α))⟩
  | tail h' hstep ih =>
      rename_i b c
      rcases ih with ⟨a', ha', hchain⟩
      by_cases hcA : c ∈ (A : Set α)
      · exact ⟨c, hcA, Relation.ReflTransGen.refl (r := fun x y => r x y ∧ y ∉ (A : Set α))⟩
      · exact ⟨a', ha', Relation.ReflTransGen.tail hchain ⟨hstep, hcA⟩⟩

end FrogModel

theorem FrogModel.reach_union_bound {α : Type*} (r : α → α → Prop) (A : Finset α) (P : α → Prop) :
    {w | P w ∧ ∃ a ∈ A, Relation.ReflTransGen r a w}.encard ≤
      ∑ a ∈ A, {w | P w ∧ Relation.ReflTransGen (fun x y => r x y ∧ y ∉ A) a w}.encard := by
  set r' := fun x y : α => r x y ∧ y ∉ (A : Set α) with hr'
  have hsubset : {w | P w ∧ ∃ a ∈ A, Relation.ReflTransGen r a w} ⊆
      ⋃ a ∈ A, {w | P w ∧ Relation.ReflTransGen r' a w} := by
    intro w hw
    rcases hw with ⟨hP, a, ha, hchain⟩
    have h := refl_trans_gen_restrict_last hchain ha
    rcases h with ⟨a', ha', hchain'⟩
    refine Set.mem_biUnion ha' ?_
    exact ⟨hP, hchain'⟩
  calc
    {w | P w ∧ ∃ a ∈ A, Relation.ReflTransGen r a w}.encard
        ≤ (⋃ a ∈ A, {w | P w ∧ Relation.ReflTransGen r' a w}).encard :=
      Set.encard_mono hsubset
    _ ≤ ∑ a ∈ A, {w | P w ∧ Relation.ReflTransGen r' a w}.encard :=
      Finset.set_encard_biUnion_le A _

theorem FrogModel.Stage.closure_eq_chains {ι P : Type*} (arc : ι → P → ι → Prop) (ω : ι → P)
    (base : Set ι) :
    FrogModel.Stage.closure arc ω base =
      {τ | ∃ σ ∈ base, Relation.ReflTransGen (fun a b => arc a (ω a) b) σ τ} := by
  ext τ
  constructor
  · intro hτ
    rw [FrogModel.Stage.closure, Set.mem_sInter] at hτ
    let RHS : Set ι := {τ | ∃ σ ∈ base, Relation.ReflTransGen (fun a b => arc a (ω a) b) σ τ}
    have hRHS_base : base ⊆ RHS := by
      intro x hx
      exact ⟨x, hx, Relation.ReflTransGen.refl⟩
    have hRHS_closed : ∀ σ ∈ RHS, ∀ τ', arc σ (ω σ) τ' → τ' ∈ RHS := by
      intro σ hσ τ' harc'
      rcases hσ with ⟨ρ, hρ, hchain⟩
      exact ⟨ρ, hρ, Relation.ReflTransGen.tail hchain harc'⟩
    have hRHS_mem : RHS ∈ {S | base ⊆ S ∧ ∀ σ ∈ S, ∀ τ, arc σ (ω σ) τ → τ ∈ S} :=
      ⟨hRHS_base, hRHS_closed⟩
    exact hτ RHS hRHS_mem
  · intro hτ
    rcases hτ with ⟨σ, hσ, hchain⟩
    rw [FrogModel.Stage.closure, Set.mem_sInter]
    intro S hS
    rcases hS with ⟨hbaseS, hclosedS⟩
    induction hchain with
    | refl => exact hbaseS hσ
    | tail hchain' hstep ih => exact hclosedS _ ih _ hstep

theorem FrogModel.Stage.stages_mono_succ {ι P : Type*} (arc : ι → P → ι → Prop)
    (closed : ι → P → Prop) (succ : ι → ι) (σ₀ : ι) (ω : ι → P) (m : ℕ) :
    FrogModel.Stage.stages arc closed succ σ₀ ω m ⊆
      FrogModel.Stage.stages arc closed succ σ₀ ω (m + 1) := by
  simp [FrogModel.Stage.stages]
  have hsub : FrogModel.Stage.stages arc closed succ σ₀ ω m ⊆
      insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
        {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m,
          closed σ (ω σ) ∧ τ = succ σ}) := by
    refine Set.Subset.trans ?_ (Set.subset_insert _ _)
    apply Set.subset_union_left
  have hclosure : insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
      {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m,
        closed σ (ω σ) ∧ τ = succ σ}) ⊆
      FrogModel.Stage.closure arc ω
        (insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
          {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m,
            closed σ (ω σ) ∧ τ = succ σ})) := by
    intro x hx
    rw [FrogModel.Stage.closure]
    apply Set.mem_sInter.mpr
    intro S hS
    rcases hS with ⟨hbase, _hclosed⟩
    exact hbase hx
  exact Set.Subset.trans hsub hclosure

theorem FrogModel.Stage.measurableSet_closure {ι P : Type*} [Countable ι] [MeasurableSpace P]
    (arc : ι → P → ι → Prop) (harc : ∀ σ τ, MeasurableSet {x : P | arc σ x τ})
    (base : (ι → P) → Set ι) (hbase : ∀ σ, MeasurableSet {ω : ι → P | σ ∈ base ω}) (τ : ι) :
    MeasurableSet {ω : ι → P | τ ∈ FrogModel.Stage.closure arc ω (base ω)} := by
  -- characterize closure using ReflTransGen
  have closure_eq_aux : ∀ (ω : ι → P),
      FrogModel.Stage.closure arc ω (base ω) =
      {τ' | ∃ σ ∈ base ω, Relation.ReflTransGen (fun a b => arc a (ω a) b) σ τ'} := by
    intro ω
    ext τ'
    constructor
    · intro h
      let r := fun (a b : ι) => arc a (ω a) b
      let S : Set ι := {x | ∃ σ ∈ base ω, Relation.ReflTransGen r σ x}
      have hS_base : base ω ⊆ S := by
        intro σ hσ
        refine ⟨σ, hσ, Relation.ReflTransGen.refl⟩
      have hS_closed : ∀ σ ∈ S, ∀ τ'', arc σ (ω σ) τ'' → τ'' ∈ S := by
        intro σ' hσ' τ'' harc_st
        rcases hσ' with ⟨σ'', hσ''_base, hchain⟩
        refine ⟨σ'', hσ''_base, Relation.ReflTransGen.tail hchain harc_st⟩
      have hτS : τ' ∈ S := by
        have : τ' ∈ FrogModel.Stage.closure arc ω (base ω) := h
        rw [FrogModel.Stage.closure] at this
        rw [Set.mem_sInter] at this
        have hS_mem : S ∈ {S' | base ω ⊆ S' ∧ ∀ σ ∈ S', ∀ τ, arc σ (ω σ) τ → τ ∈ S'} := by
          refine ⟨hS_base, hS_closed⟩
        exact this S hS_mem
      rcases hτS with ⟨σ, hσ, hchain⟩
      exact ⟨σ, hσ, hchain⟩
    · intro h
      rcases h with ⟨σ, hσ, hchain⟩
      intro S hS
      rcases hS with ⟨hS_base, hS_closed⟩
      induction hchain with
      | refl =>
        exact hS_base hσ
      | tail h_prev h_r ih =>
        exact hS_closed _ ih _ h_r

  -- rewrite the goal using the characterization
  have h_set_eq : {ω : ι → P | τ ∈ FrogModel.Stage.closure arc ω (base ω)} =
      {ω : ι → P | ∃ σ ∈ base ω,
        Relation.ReflTransGen (fun a b => arc a (ω a) b) σ τ} := by
    ext ω; simp [closure_eq_aux ω]
  rw [h_set_eq]

  -- Define the relation r_ω
  let r := fun (ω : ι → P) (a b : ι) => arc a (ω a) b

  -- Use List characterization: ReflTransGen r σ τ ↔ ∃ l ≠ [], IsChain r l ∧ l.head = σ ∧ l.getLast = τ
  have h_list_equiv (ω : ι → P) (σ : ι) :
      Relation.ReflTransGen (r ω) σ τ ↔
      ∃ (l : List ι) (hne : l ≠ []), List.IsChain (r ω) l ∧ l.head hne = σ ∧ l.getLast hne = τ := by
    constructor
    · intro h; exact List.exists_isChain_ne_nil_of_relationReflTransGen h
    · intro ⟨l, hne, hchain, hhead, hlast⟩
      have h := List.relationReflTransGen_of_exists_isChain l hchain hne
      rw [hhead, hlast] at h
      exact h

  -- For any list l, the set {ω | IsChain (r ω) l} is measurable
  have h_measurable_isChain (l : List ι) : MeasurableSet {ω : ι → P | List.IsChain (r ω) l} := by
    induction' l with a l ih
    · have : {ω : ι → P | List.IsChain (r ω) []} = Set.univ := by
        ext ω; simp
      rw [this]; exact MeasurableSet.univ
    · have h_chain_iff (ω : ι → P) : List.IsChain (r ω) (a :: l) ↔
          l = [] ∨ ∃ (b : ι) (l' : List ι), r ω a b ∧ List.IsChain (r ω) (b :: l') ∧ l = b :: l' := by
        simpa using List.isChain_cons_iff (r ω) a l
      have h_set_eq : {ω : ι → P | List.IsChain (r ω) (a :: l)} =
          {ω : ι → P | l = []} ∪
          {ω : ι → P | ∃ (b : ι) (l' : List ι), r ω a b ∧ List.IsChain (r ω) (b :: l') ∧ l = b :: l'} := by
        ext ω; simp [h_chain_iff ω]
      rw [h_set_eq]
      apply MeasurableSet.union
      · by_cases hl : l = []
        · have : {ω : ι → P | l = []} = Set.univ := by ext ω; simp [hl]
          rw [this]; exact MeasurableSet.univ
        · have : {ω : ι → P | l = []} = ∅ := by ext ω; simp [hl]
          rw [this]; exact MeasurableSet.empty
      · by_cases hl : l = []
        · have : {ω : ι → P | ∃ (b : ι) (l' : List ι), r ω a b ∧ List.IsChain (r ω) (b :: l') ∧ l = b :: l'} = ∅ := by
            ext ω; simp [hl]
          rw [this]; exact MeasurableSet.empty
        · rcases List.exists_cons_of_ne_nil hl with ⟨b, l', hl_eq⟩
          have h_set_eq2 : {ω : ι → P | ∃ (b' : ι) (l'' : List ι), r ω a b' ∧ List.IsChain (r ω) (b' :: l'') ∧ l = b' :: l''} =
              {ω : ι → P | r ω a b ∧ List.IsChain (r ω) (b :: l')} := by
            ext ω; simp [hl_eq]
          rw [h_set_eq2]
          have h_meas_ab : MeasurableSet {ω : ι → P | r ω a b} := by
            dsimp [r]
            have : {ω : ι → P | arc a (ω a) b} = (fun (ω : ι → P) => ω a) ⁻¹' {x : P | arc a x b} := by
              ext ω; simp
            rw [this]
            exact measurableSet_preimage (measurable_pi_apply a) (harc a b)
          have h_meas_chain : MeasurableSet {ω : ι → P | List.IsChain (r ω) (b :: l')} := by
            rw [hl_eq] at ih
            exact ih
          exact MeasurableSet.inter h_meas_ab h_meas_chain

  -- Express the target set as a countable union of finite intersections of measurable sets
  -- {ω | ∃ σ ∈ base ω, ReflTransGen (r ω) σ τ}
  -- = ⋃_{l ≠ []} {ω | l.head hne ∈ base ω ∧ IsChain (r ω) l ∧ l.getLast hne = τ}
  have h_target_eq : {ω : ι → P | ∃ σ ∈ base ω, Relation.ReflTransGen (r ω) σ τ} =
      ⋃ (l : List ι), ⋃ (hne : l ≠ []), ⋃ (_ : l.getLast hne = τ),
        {ω : ι → P | l.head hne ∈ base ω ∧ List.IsChain (r ω) l} := by
    ext ω
    constructor
    · intro ⟨σ, hσ, hchain⟩
      rcases (h_list_equiv ω σ).mp hchain with ⟨l, hne, hchain_l, hhead, hlast⟩
      refine Set.mem_iUnion.mpr ⟨l, ?_⟩
      refine Set.mem_iUnion.mpr ⟨hne, ?_⟩
      refine Set.mem_iUnion.mpr ⟨hlast, ?_⟩
      simp [hhead, hσ, hchain_l]
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨l, h'⟩
      rcases Set.mem_iUnion.mp h' with ⟨hne, h''⟩
      rcases Set.mem_iUnion.mp h'' with ⟨hlast, h'''⟩
      rcases h''' with ⟨hσ, hchain⟩
      refine ⟨l.head hne, hσ, ?_⟩
      exact (h_list_equiv ω (l.head hne)).mpr ⟨l, hne, hchain, rfl, hlast⟩

  rw [h_target_eq]

  -- Now we have a countable union of sets, each of which is a finite intersection of measurable sets
  -- The index set is (l : List ι) × (hne : l ≠ []) × (hlast : l.getLast hne = τ)
  -- Since List ι is countable, this is a countable union
  -- Each inner set is {ω | l.head hne ∈ base ω} ∩ {ω | IsChain (r ω) l}
  -- Both are measurable, so their intersection is measurable
  refine MeasurableSet.iUnion ?_
  intro l
  refine MeasurableSet.iUnion ?_
  intro hne
  refine MeasurableSet.iUnion ?_
  intro hlast
  -- The inner set: {ω | l.head hne ∈ base ω ∧ IsChain (r ω) l}
  -- This is the intersection of two measurable sets
  have h1 : MeasurableSet {ω : ι → P | l.head hne ∈ base ω} := hbase (l.head hne)
  have h2 : MeasurableSet {ω : ι → P | List.IsChain (r ω) l} := h_measurable_isChain l
  -- Need to show: MeasurableSet {ω | l.head hne ∈ base ω ∧ List.IsChain (r ω) l}
  -- This is the intersection of the two sets
  -- But note that the set in the union is exactly this intersection
  -- Actually, the set is {ω | l.head hne ∈ base ω ∧ List.IsChain (r ω) l}
  -- which is the intersection of {ω | l.head hne ∈ base ω} and {ω | List.IsChain (r ω) l}
  -- So we can use MeasurableSet.inter
  exact MeasurableSet.inter h1 h2

theorem FrogModel.Stage.measurableSet_stages {ι P : Type*} [Countable ι] [MeasurableSpace P]
    (arc : ι → P → ι → Prop) (closed : ι → P → Prop) (succ : ι → ι) (σ₀ : ι)
    (harc : ∀ σ τ, MeasurableSet {x : P | arc σ x τ})
    (hclosed : ∀ σ, MeasurableSet {x : P | closed σ x}) (m : ℕ) (τ : ι) :
    MeasurableSet {ω : ι → P | τ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m} := by
  -- Helper: iterative reachability from a family of sets under arc
  let reachable (S : (ι → P) → Set ι) (ω : ι → P) (n : ℕ) : Set ι :=
    Nat.rec (S ω) (fun _ R => R ∪ {τ | ∃ σ ∈ R, arc σ (ω σ) τ}) n
  have reachable_zero (S : (ι → P) → Set ι) (ω : ι → P) : reachable S ω 0 = S ω := rfl
  have reachable_succ (S : (ι → P) → Set ι) (ω : ι → P) (n : ℕ) :
      reachable S ω (n + 1) = reachable S ω n ∪ {τ | ∃ σ ∈ reachable S ω n, arc σ (ω σ) τ} := rfl
  have base_sub_closure (S : (ι → P) → Set ι) (ω : ι → P) : S ω ⊆ FrogModel.Stage.closure arc ω (S ω) := by
    intro σ hσ
    rw [FrogModel.Stage.closure, Set.mem_sInter]
    intro T hT
    exact hT.1 hσ
  have closure_closed (S : (ι → P) → Set ι) (ω : ι → P) :
      ∀ σ ∈ FrogModel.Stage.closure arc ω (S ω), ∀ τ', arc σ (ω σ) τ' → τ' ∈ FrogModel.Stage.closure arc ω (S ω) := by
    intro σ hσ τ' harc'
    rw [FrogModel.Stage.closure, Set.mem_sInter] at hσ ⊢
    intro T hT
    have hσT : σ ∈ T := hσ T hT
    exact hT.2 σ hσT τ' harc'
  have reachable_sub_closure (S : (ι → P) → Set ι) (ω : ι → P) (n : ℕ) :
      reachable S ω n ⊆ FrogModel.Stage.closure arc ω (S ω) := by
    induction' n with n ih
    · rw [reachable_zero]
      exact base_sub_closure S ω
    · rw [reachable_succ]
      intro σ hσ
      rcases hσ with (hσ | hσ)
      · exact ih hσ
      · rcases hσ with ⟨σ', hσ', harcσ⟩
        exact closure_closed S ω σ' (ih hσ') σ harcσ
  have closure_eq_union (S : (ι → P) → Set ι) (ω : ι → P) :
      FrogModel.Stage.closure arc ω (S ω) = ⋃ n, reachable S ω n := by
    apply Set.Subset.antisymm
    · -- closure ⊆ union
      have h_union_closed : S ω ⊆ ⋃ n, reachable S ω n := by
        intro σ hσ
        refine Set.mem_iUnion.mpr ⟨(0 : ℕ), ?_⟩
        rw [reachable_zero]
        exact hσ
      have h_union_arc_closed : ∀ σ ∈ ⋃ n, reachable S ω n, ∀ τ', arc σ (ω σ) τ' → τ' ∈ ⋃ n, reachable S ω n := by
        intro σ hσ τ' harc'
        rcases Set.mem_iUnion.1 hσ with ⟨n, hσn⟩
        refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
        rw [reachable_succ]
        exact Or.inr ⟨σ, hσn, harc'⟩
      have h_union_mem : (⋃ n, reachable S ω n) ∈
          {T : Set ι | S ω ⊆ T ∧ ∀ σ ∈ T, ∀ τ', arc σ (ω σ) τ' → τ' ∈ T} := by
        exact ⟨h_union_closed, h_union_arc_closed⟩
      rw [FrogModel.Stage.closure]
      exact Set.sInter_subset_of_mem h_union_mem
    · -- union ⊆ closure
      intro σ hσ
      rcases Set.mem_iUnion.1 hσ with ⟨n, hσn⟩
      exact reachable_sub_closure S ω n hσn
  have reachable_measurable (S : (ι → P) → Set ι) (hS : ∀ σ, MeasurableSet {ω : ι → P | σ ∈ S ω}) :
      ∀ n τ, MeasurableSet {ω : ι → P | τ ∈ reachable S ω n} := by
    intro n
    induction' n with n ih
    · -- n = 0: reachable S ω 0 = S ω
      intro τ
      simp [reachable_zero, hS τ]
    · -- n+1
      intro τ
      have h_eq : {ω : ι → P | τ ∈ reachable S ω (n + 1)} =
          {ω : ι → P | τ ∈ reachable S ω n} ∪
          {ω : ι → P | ∃ σ, σ ∈ reachable S ω n ∧ arc σ (ω σ) τ} := by
        ext ω; simp [reachable_succ]
      rw [h_eq]
      apply MeasurableSet.union
      · exact ih τ
      · have h_set : {ω : ι → P | ∃ σ, σ ∈ reachable S ω n ∧ arc σ (ω σ) τ} =
            ⋃ (σ : ι), ({ω : ι → P | σ ∈ reachable S ω n} ∩ {ω : ι → P | arc σ (ω σ) τ}) := by
          ext ω; simp
        rw [h_set]
        apply MeasurableSet.iUnion
        intro σ
        apply MeasurableSet.inter
        · exact ih σ
        · -- need: MeasurableSet {ω | arc σ (ω σ) τ}
          -- this is the preimage of {x | arc σ x τ} under ω ↦ ω σ
          have h_meas_eval : Measurable fun (ω : ι → P) => ω σ := measurable_pi_apply σ
          exact (harc σ τ).preimage h_meas_eval
  have measurableSet_closure_of_family (S : (ι → P) → Set ι) (hS : ∀ σ, MeasurableSet {ω : ι → P | σ ∈ S ω}) (τ : ι) :
      MeasurableSet {ω : ι → P | τ ∈ FrogModel.Stage.closure arc ω (S ω)} := by
    have h_eq : {ω : ι → P | τ ∈ FrogModel.Stage.closure arc ω (S ω)} =
        ⋃ n, {ω : ι → P | τ ∈ reachable S ω n} := by
      ext ω; simp [closure_eq_union S ω]
    rw [h_eq]
    apply MeasurableSet.iUnion
    intro n
    exact reachable_measurable S hS n τ
  -- Now prove the main theorem by induction on m, generalizing over τ
  revert τ
  induction' m with m ih
  · -- m = 0: stages ... 0 = ∅
    intro τ; simp [FrogModel.Stage.stages]
  · -- m = m+1
    intro τ
    have h_eq : {ω : ι → P | τ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω (m + 1)} =
        {ω : ι → P | τ ∈ FrogModel.Stage.closure arc ω
          (insert σ₀ (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
            {τ | ∃ σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ (ω σ) ∧ τ = succ σ}))} := by
      ext ω; simp [FrogModel.Stage.stages]
    rw [h_eq]
    apply measurableSet_closure_of_family
    intro σ
    -- need to show: MeasurableSet {ω | σ ∈ insert σ₀ (A ω ∪ B ω)}
    -- where A ω = stages ... m ω, B ω = {τ | ∃ σ' ∈ A ω, closed σ' (ω σ') ∧ τ = succ σ'}
    have h_insert : {ω : ι → P | σ ∈ insert σ₀
        (FrogModel.Stage.stages arc closed succ σ₀ ω m ∪
          {τ | ∃ σ' ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ' (ω σ') ∧ τ = succ σ'})} =
        {ω : ι → P | σ = σ₀} ∪
        {ω : ι → P | σ ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m} ∪
        {ω : ι → P | ∃ σ' ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ' (ω σ') ∧ σ = succ σ'} := by
      ext ω; simp [or_assoc]
    rw [h_insert]
    -- Now the goal is: MeasurableSet (A ∪ B ∪ C) where
    -- A = {ω | σ = σ₀}, B = {ω | σ ∈ stages ... m ω}, C = {ω | ∃ σ' ∈ stages ... m ω, closed σ' (ω σ') ∧ σ = succ σ'}
    -- Use MeasurableSet.union twice
    apply MeasurableSet.union
    · -- MeasurableSet (A ∪ B)
      apply MeasurableSet.union
      · -- MeasurableSet A = {ω | σ = σ₀}
        by_cases h : σ = σ₀
        · subst σ; simp
        · simp [h]
      · -- MeasurableSet B = {ω | σ ∈ stages ... m ω}
        -- ih : ∀ τ, MeasurableSet {ω | τ ∈ stages ... m ω}
        exact ih σ
    · -- MeasurableSet C
      have h_set : {ω : ι → P | ∃ σ' ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m, closed σ' (ω σ') ∧ σ = succ σ'} =
          ⋃ (σ' : ι), ({ω : ι → P | σ' ∈ FrogModel.Stage.stages arc closed succ σ₀ ω m} ∩
            {ω : ι → P | closed σ' (ω σ')} ∩ {ω : ι → P | σ = succ σ'}) := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop, and_assoc]
      rw [h_set]
      apply MeasurableSet.iUnion
      intro σ'
      apply MeasurableSet.inter
      · apply MeasurableSet.inter
        · exact ih σ'
        · -- need: MeasurableSet {ω | closed σ' (ω σ')}
          have h_meas_eval : Measurable fun (ω : ι → P) => ω σ' := measurable_pi_apply σ'
          exact (hclosed σ').preimage h_meas_eval
      · by_cases h : σ = succ σ'
        · subst σ; simp
        · simp [h]

namespace FrogModel

-- Helper lemma: the set of x such that walk v x n = w is measurable
lemma measurableSet_walk_eq {d : ℕ} (v : Vertex d) (n : ℕ) (w : Vertex d) :
    MeasurableSet {x : ℕ → Step d | walk v x n = w} := by
  induction' n with n ih generalizing w
  · -- n = 0: walk v x 0 = v always
    by_cases h : v = w
    · have : {x : ℕ → Step d | walk v x 0 = w} = Set.univ := by
        ext x; simp [walk, h]
      rw [this]
      exact MeasurableSet.univ
    · have : {x : ℕ → Step d | walk v x 0 = w} = ∅ := by
        ext x; simp [walk, h]
      rw [this]
      exact MeasurableSet.empty
  · -- n+1: walk v x (n+1) = step (walk v x n) (x n)
    have h_eq : {x : ℕ → Step d | walk v x (n+1) = w} =
      ⋃ w' : Vertex d, {x : ℕ → Step d | walk v x n = w'} ∩ {x : ℕ → Step d | step w' (x n) = w} := by
      ext x; simp [walk]
    rw [h_eq]
    refine MeasurableSet.iUnion ?_
    intro w'
    have h_meas_w' : MeasurableSet {x : ℕ → Step d | walk v x n = w'} := ih w'
    have h_meas_step : MeasurableSet {x : ℕ → Step d | step w' (x n) = w} := by
      -- {x | step w' (x n) = w} = (fun x => step w' (x n)) ⁻¹' {w}
      have h_eval : Measurable fun (x : ℕ → Step d) => x n := measurable_pi_apply n
      have h_step : Measurable (step w' : Step d → Vertex d) := measurable_of_finite _
      have h_singleton : MeasurableSet ({w} : Set (Vertex d)) :=
        MeasurableSet.singleton w
      -- Compose: x ↦ x n ↦ step w' (x n)
      have h_comp : Measurable fun (x : ℕ → Step d) => step w' (x n) :=
        h_step.comp h_eval
      exact h_comp h_singleton
    exact MeasurableSet.inter h_meas_w' h_meas_step

-- Helper lemma: the set of x such that (n : ℕ∞) ≤ cut v x is measurable
lemma measurableSet_cut_ge {d : ℕ} (v : Vertex d) (n : ℕ) :
    MeasurableSet {x : ℕ → Step d | (n : ℕ∞) ≤ cut v x} := by
  -- The condition (n : ℕ∞) ≤ cut v x is equivalent to:
  -- ∀ k < n, 1 ≤ k → walk v x k ≠ root
  -- We prove this equivalence using properties of sInf in ℕ∞
  -- We'll show that the set contains the finite intersection, and vice versa
  let T := ⋂ k ∈ Finset.Ico 1 n, {x : ℕ → Step d | walk v x k ≠ root}
  have hT_meas : MeasurableSet T :=
    Finset.measurableSet_biInter (Finset.Ico 1 n) (fun k hk => by
      refine MeasurableSet.compl ?_
      exact measurableSet_walk_eq v k root)
  have h_subset : T ⊆ {x : ℕ → Step d | (n : ℕ∞) ≤ cut v x} := by
    intro x hx
    -- hx : x ∈ T, i.e., ∀ k ∈ Ico 1 n, walk v x k ≠ root
    have h_forall : ∀ k, k ∈ Finset.Ico 1 n → walk v x k ≠ root := by
      intro k hk
      have := Set.mem_iInter₂.1 hx k hk
      exact this
    -- Need to show (n : ℕ∞) ≤ cut v x
    let S : Set ℕ∞ := ((fun (m : ℕ) => (m : ℕ∞)) '' {m | 1 ≤ m ∧ walk v x m = root})
    by_cases hS : S.Nonempty
    · apply le_csInf hS
      rintro y ⟨k, ⟨hk1, hk_root⟩, rfl⟩
      by_cases hk_lt_n : k < n
      · have h_contra := h_forall k (Finset.mem_Ico.mpr ⟨hk1, hk_lt_n⟩)
        exact absurd hk_root h_contra
      · have hn_le_k : n ≤ k := Nat.le_of_not_lt hk_lt_n
        exact WithTop.coe_le_coe.mpr hn_le_k
    · -- S is empty, so cut v x = ⊤
      have h_cut_top : cut v x = ⊤ := by
        unfold cut
        -- S is defined as a let, so we need to expand it
        show sInf (((fun (m : ℕ) => (m : ℕ∞)) '' {m | 1 ≤ m ∧ walk v x m = root})) = ⊤
        -- Since hS : ¬ S.Nonempty, the set is empty
        have h_empty : ((fun (m : ℕ) => (m : ℕ∞)) '' {m | 1 ≤ m ∧ walk v x m = root}) = ∅ := by
          rw [Set.not_nonempty_iff_eq_empty] at hS
          exact hS
        rw [h_empty]
        exact sInf_empty
      show (n : ℕ∞) ≤ cut v x
      rw [h_cut_top]
      exact le_top
  have h_superset : {x : ℕ → Step d | (n : ℕ∞) ≤ cut v x} ⊆ T := by
    intro x hx
    -- hx : (n : ℕ∞) ≤ cut v x
    -- Need to show: x ∈ T = ⋂ k ∈ Ico 1 n, {x | walk v x k ≠ root}
    -- Using Set.mem_iInter₂
    refine Set.mem_iInter₂.mpr ?_
    intro k hk
    -- hk : k ∈ Finset.Ico 1 n
    rcases Finset.mem_Ico.1 hk with ⟨hk1, hk2⟩
    -- Goal: x ∈ {x | walk v x k ≠ root}, i.e., walk v x k ≠ root
    show walk v x k ≠ root
    by_contra h_eq_root
    -- h_eq_root : walk v x k = root
    -- Then k ∈ S
    -- Inline S for dsimp
    have hk_mem : (k : ℕ∞) ∈ ((fun (m : ℕ) => (m : ℕ∞)) '' {m | 1 ≤ m ∧ walk v x m = root}) := by
      refine ⟨k, ⟨hk1, h_eq_root⟩, rfl⟩
    have h_cut_le_k : cut v x ≤ (k : ℕ∞) := by
      unfold cut
      have h_bdd : BddBelow ((fun (m : ℕ) => (m : ℕ∞)) '' {m | 1 ≤ m ∧ walk v x m = root}) := by
        refine ⟨(0 : ℕ∞), ?_⟩
        rintro y ⟨m, hm, rfl⟩
        exact WithTop.coe_nonneg.mpr (Nat.zero_le m)
      exact csInf_le h_bdd hk_mem
    have h_n_le_cut : (n : ℕ∞) ≤ cut v x := hx
    have h_n_le_k : (n : ℕ∞) ≤ (k : ℕ∞) := le_trans h_n_le_cut h_cut_le_k
    have h_lt : (k : ℕ∞) < (n : ℕ∞) := (WithTop.coe_lt_coe.mpr hk2)
    exact not_le.mpr h_lt h_n_le_k
  -- Now we have T = {x | (n : ℕ∞) ≤ cut v x}
  have h_eq : {x : ℕ → Step d | (n : ℕ∞) ≤ cut v x} = T :=
    Set.Subset.antisymm h_superset h_subset
  rw [h_eq]
  exact hT_meas

end FrogModel

theorem FrogModel.measurableSet_segArc {d : ℕ} (σ τ : Seg d) :
    MeasurableSet {x : ℕ → Step d | segArc σ x τ} := by
  -- First, unfold the definition of segArc
  unfold segArc
  -- The condition is: τ.2 = 0 ∧ τ.1 ≠ root ∧ ∃ n, (n : ℕ∞) ≤ cut σ.start x ∧ walk σ.start x n = τ.1
  -- The first two conjuncts do not depend on x, so they are either Set.univ or ∅
  -- We handle them by case splitting
  by_cases hτ0 : τ.2 = 0
  · by_cases hτ1 : τ.1 ≠ root
    · -- Both conditions hold, so the set is {x | ∃ n, ...}
      -- We need to show this is measurable
      -- The set is a countable union over n of {x | (n : ℕ∞) ≤ cut σ.start x ∧ walk σ.start x n = τ.1}
      -- We'll show each such set is measurable, then take the countable union
      have h_meas : ∀ n : ℕ, MeasurableSet {x : ℕ → Step d | ((n : ℕ∞) ≤ cut σ.start x ∧ walk σ.start x n = τ.1)} := by
        intro n
        -- This is the intersection of two measurable sets
        refine MeasurableSet.inter ?_ ?_
        · exact measurableSet_cut_ge σ.start n
        · exact measurableSet_walk_eq σ.start n τ.1
      -- Now the whole set is the countable union
      rw [show {x | τ.2 = 0 ∧ τ.1 ≠ root ∧ ∃ (n : ℕ), ((n : ℕ∞) ≤ cut σ.start x ∧ walk σ.start x n = τ.1)} =
        ⋃ n : ℕ, {x | ((n : ℕ∞) ≤ cut σ.start x ∧ walk σ.start x n = τ.1)} by
        ext x; simp [hτ0, hτ1]]
      exact MeasurableSet.iUnion h_meas
    · -- τ.1 = root, so the set is empty (since τ.1 ≠ root is false)
      have : {x : ℕ → Step d | τ.2 = 0 ∧ τ.1 ≠ root ∧ ∃ (n : ℕ), ((n : ℕ∞) ≤ cut σ.start x ∧ walk σ.start x n = τ.1)} = ∅ := by
        ext x; simp [hτ1]
      rw [this]
      exact MeasurableSet.empty
  · -- τ.2 ≠ 0, so the set is empty
    have : {x : ℕ → Step d | τ.2 = 0 ∧ τ.1 ≠ root ∧ ∃ (n : ℕ), ((n : ℕ∞) ≤ cut σ.start x ∧ walk σ.start x n = τ.1)} = ∅ := by
      ext x; simp [hτ0]
    rw [this]
    exact MeasurableSet.empty

theorem FrogModel.measurableSet_segClosed {d : ℕ} (σ : Seg d) :
    MeasurableSet {x : ℕ → Step d | segClosed σ x} := by
  have h_eq : {x : ℕ → Step d | segClosed σ x} = ⋃ n : ℕ, {x | 1 ≤ n ∧ walk σ.start x n = root} := by
    ext x
    simp [segClosed, cut, Set.mem_iUnion]
  rw [h_eq]
  refine MeasurableSet.iUnion ?_
  intro n
  by_cases hn : 1 ≤ n
  · have h_set_eq : {x | 1 ≤ n ∧ walk σ.start x n = root} = {x | walk σ.start x n = root} := by
      ext x; simp [hn]
    rw [h_set_eq]
    have h_meas : Measurable (fun (x : ℕ → Step d) => walk σ.start x n) :=
      (measurable_pi_iff.mp (measurable_walk σ.start) n)
    have h_singleton : MeasurableSet ({root} : Set (Vertex d)) :=
      MeasurableSet.singleton root
    exact h_meas h_singleton
  · have h_empty : {x | 1 ≤ n ∧ walk σ.start x n = root} = (∅ : Set (ℕ → Step d)) := by
      ext x; simp [hn]
    rw [h_empty]
    exact MeasurableSet.empty

namespace FrogModel

-- Helper lemma: walkStar at a fixed time is measurable in the step sequence
lemma measurable_walkStar_at (d : ℕ) (v : Vertex d) (n : ℕ) :
    Measurable (fun (x : ℕ → Step d) => walkStar (some v) x n) := by
  induction' n with n ih
  · simp [walkStar]
  · have h_step : Measurable (fun (p : Option (Vertex d) × Step d) => stepStar p.1 p.2) := by
      apply measurable_of_countable
    have h_pair : Measurable (fun (x : ℕ → Step d) => (walkStar (some v) x n, x n)) :=
      Measurable.prodMk ih (measurable_pi_apply n)
    have h_eq : (fun (x : ℕ → Step d) => walkStar (some v) x (n + 1)) =
        (fun (p : Option (Vertex d) × Step d) => stepStar p.1 p.2) ∘
        (fun (x : ℕ → Step d) => (walkStar (some v) x n, x n)) := by
      ext x
      simp [walkStar]
    rw [h_eq]
    exact h_step.comp h_pair

-- Helper lemma: for fixed v, n, the set where walkStar equals a specific value is measurable
lemma measurableSet_walkStar_eq (d : ℕ) (v : Vertex d) (n : ℕ) (b : Option (Vertex d)) :
    MeasurableSet {x : ℕ → Step d | walkStar (some v) x n = b} := by
  have h_meas : Measurable (fun (x : ℕ → Step d) => walkStar (some v) x n) :=
    measurable_walkStar_at d v n
  have h_singleton : MeasurableSet ({b} : Set (Option (Vertex d))) :=
    measurableSet_singleton b
  exact h_meas h_singleton

-- Helper lemma: the projection ζ ↦ ζ v is measurable
lemma measurable_proj (d : ℕ) (v : Vertex d) : Measurable (fun (ζ : Sample d) => ζ v) :=
  measurable_pi_apply v

-- Helper lemma: for fixed v, n, the set {ζ | walkStar (some v) (ζ v) n = b} is measurable
lemma measurableSet_walkStar_zeta_eq (d : ℕ) (v : Vertex d) (n : ℕ) (b : Option (Vertex d)) :
    MeasurableSet {ζ : Sample d | walkStar (some v) (ζ v) n = b} := by
  have h_proj : Measurable (fun (ζ : Sample d) => ζ v) := measurable_proj d v
  have h_set : MeasurableSet {x : ℕ → Step d | walkStar (some v) x n = b} :=
    measurableSet_walkStar_eq d v n b
  exact h_proj h_set

-- Helper lemma: for fixed v, the set {ζ | ∃ n, walkStar (some v) (ζ v) n = none} is measurable
lemma measurableSet_exists_walkStar_none (d : ℕ) (v : Vertex d) :
    MeasurableSet {ζ : Sample d | ∃ n, walkStar (some v) (ζ v) n = none} := by
  have h_union : {ζ : Sample d | ∃ n, walkStar (some v) (ζ v) n = none} =
      ⋃ n, {ζ : Sample d | walkStar (some v) (ζ v) n = none} := by
    ext ζ; simp
  rw [h_union]
  refine MeasurableSet.iUnion ?_
  intro n
  exact measurableSet_walkStar_zeta_eq d v n none

-- Helper lemma: starArc ζ a b is measurable in ζ (for fixed a, b)
lemma measurableSet_starArc (d : ℕ) (a b : Vertex d) :
    MeasurableSet {ζ : Sample d | starArc ζ a b} := by
  have h_de : {ζ : Sample d | starArc ζ a b} = {ζ : Sample d | b ≠ [] ∧ ∃ n, walkStar (some a) (ζ a) n = some b} := by
    ext ζ; simp [starArc]
  rw [h_de]
  by_cases hb : b ≠ []
  · have h_simp : {ζ : Sample d | b ≠ [] ∧ ∃ n, walkStar (some a) (ζ a) n = some b} =
        {ζ : Sample d | ∃ n, walkStar (some a) (ζ a) n = some b} := by
      ext ζ; simp [hb]
    rw [h_simp]
    have h_union : {ζ : Sample d | ∃ n, walkStar (some a) (ζ a) n = some b} =
        ⋃ n, {ζ : Sample d | walkStar (some a) (ζ a) n = some b} := by
      ext ζ; simp
    rw [h_union]
    refine MeasurableSet.iUnion ?_
    intro n
    have h_set : MeasurableSet {x : ℕ → Step d | walkStar (some a) x n = some b} :=
      measurableSet_walkStar_eq d a n (some b)
    have h_proj : Measurable (fun (ζ : Sample d) => ζ a) := measurable_pi_apply a
    exact h_proj h_set
  · have h_simp : {ζ : Sample d | b ≠ [] ∧ ∃ n, walkStar (some a) (ζ a) n = some b} = ∅ := by
      ext ζ; simp [hb]
    rw [h_simp]
    exact MeasurableSet.empty

-- Helper lemma: for a fixed list l, the set {ζ | List.IsChain (starArc ζ) l} is measurable
lemma measurableSet_listIsChain_starArc (d : ℕ) (l : List (Vertex d)) :
    MeasurableSet {ζ : Sample d | List.IsChain (starArc ζ) l} := by
  -- Use strong induction on l.length
  induction' hlen : l.length using Nat.strong_induction_on with k IH generalizing l
  match l with
  | [] =>
    have : {ζ : Sample d | List.IsChain (starArc ζ) []} = Set.univ := by
      ext ζ; simp
    rw [this]
    exact MeasurableSet.univ
  | a :: l' =>
    match l' with
    | [] =>
      have : {ζ : Sample d | List.IsChain (starArc ζ) [a]} = Set.univ := by
        ext ζ; simp
      rw [this]
      exact MeasurableSet.univ
    | b :: l'' =>
      have h_set_eq : {ζ : Sample d | List.IsChain (starArc ζ) (a :: b :: l'')} =
          {ζ : Sample d | starArc ζ a b} ∩ {ζ : Sample d | List.IsChain (starArc ζ) (b :: l'')} := by
        ext ζ; constructor
        · intro h
          cases h with
          | cons_cons h1 h2 =>
            exact ⟨h1, h2⟩
        · intro ⟨h1, h2⟩
          exact List.IsChain.cons_cons h1 h2
      rw [h_set_eq]
      have h_meas1 : MeasurableSet {ζ : Sample d | starArc ζ a b} :=
        measurableSet_starArc d a b
      have h_len_lt : (b :: l'').length < k := by
        have hk : (a :: b :: l'').length = k := hlen
        have : (a :: b :: l'').length = (b :: l'').length + 1 := by simp
        rw [this] at hk
        omega
      have h_meas2 : MeasurableSet {ζ : Sample d | List.IsChain (starArc ζ) (b :: l'')} :=
        IH ((b :: l'').length) h_len_lt (b :: l'') rfl
      exact MeasurableSet.inter h_meas1 h_meas2

-- Helper lemma: for fixed v, the set {ζ | Relation.ReflTransGen (starArc ζ) [] v} is measurable
lemma measurableSet_reflTransGen_starArc (d : ℕ) (v : Vertex d) :
    MeasurableSet {ζ : Sample d | Relation.ReflTransGen (starArc ζ) [] v} := by
  -- Express the set as a countable union over nonempty lists
  let S := Σ l : List (Vertex d), {hl : l ≠ [] // True}
  have h_countable : Countable S := by
    infer_instance

  have h_set_eq : {ζ : Sample d | Relation.ReflTransGen (starArc ζ) [] v} =
      ⋃ (p : S), {ζ : Sample d | List.IsChain (starArc ζ) p.1 ∧ p.1.head p.2.1 = [] ∧ p.1.getLast p.2.1 = v} := by
    ext ζ; constructor
    · intro h
      rcases List.exists_isChain_ne_nil_of_relationReflTransGen h with ⟨l, hl, hchain, hhead, hlast⟩
      refine Set.mem_iUnion.mpr ⟨⟨l, hl, trivial⟩, ?_⟩
      exact ⟨hchain, hhead, hlast⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨⟨l, hl, _⟩, ⟨hchain, hhead, hlast⟩⟩
      have hrefl : Relation.ReflTransGen (starArc ζ) (l.head hl) (l.getLast hl) :=
        List.relationReflTransGen_of_exists_isChain l hchain hl
      rw [hhead, hlast] at hrefl
      exact hrefl

  rw [h_set_eq]

  -- Now use MeasurableSet.iUnion on the countable type S
  refine MeasurableSet.iUnion fun p => ?_

  -- For each p, the set is either empty or {ζ | List.IsChain (starArc ζ) p.1}
  by_cases hhead : p.1.head p.2.1 = []
  · by_cases hlast : p.1.getLast p.2.1 = v
    · -- Both conditions hold
      have h_eq : {ζ : Sample d | List.IsChain (starArc ζ) p.1 ∧ p.1.head p.2.1 = [] ∧ p.1.getLast p.2.1 = v} =
          {ζ : Sample d | List.IsChain (starArc ζ) p.1} := by
        ext ζ; simp [hhead, hlast]
      rw [h_eq]
      exact measurableSet_listIsChain_starArc d p.1
    · -- l.getLast hl ≠ v
      have h_eq : {ζ : Sample d | List.IsChain (starArc ζ) p.1 ∧ p.1.head p.2.1 = [] ∧ p.1.getLast p.2.1 = v} = ∅ := by
        ext ζ; simp [hlast]
      rw [h_eq]
      exact MeasurableSet.empty
  · -- l.head hl ≠ []
    have h_eq : {ζ : Sample d | List.IsChain (starArc ζ) p.1 ∧ p.1.head p.2.1 = [] ∧ p.1.getLast p.2.1 = v} = ∅ := by
      ext ζ; simp [hhead]
    rw [h_eq]
    exact MeasurableSet.empty

end FrogModel

theorem FrogModel.measurable_frozenCount (d : ℕ) : Measurable (frozenCount (d := d)) := by
  -- frozenCount is a tsum over Vertex d (countable) of indicator functions
  -- By Measurable.ennreal_tsum, it suffices to show each term is measurable
  refine Measurable.ennreal_tsum fun v => ?_
  -- The v-th term is fun ζ => if Relation.ReflTransGen (starArc ζ) [] v ∧ ∃ n, walkStar (some v) (ζ v) n = none then 1 else 0
  -- This is Measurable.ite of a measurable condition
  have h_cond : MeasurableSet {ζ : Sample d | Relation.ReflTransGen (starArc ζ) [] v ∧ ∃ n, walkStar (some v) (ζ v) n = none} := by
    have hA : MeasurableSet {ζ : Sample d | Relation.ReflTransGen (starArc ζ) [] v} :=
      measurableSet_reflTransGen_starArc d v
    have hB : MeasurableSet {ζ : Sample d | ∃ n, walkStar (some v) (ζ v) n = none} :=
      measurableSet_exists_walkStar_none d v
    exact MeasurableSet.inter hA hB
  -- Now use Measurable.ite
  refine Measurable.ite h_cond ?_ ?_
  · -- constant 1 is measurable
    exact measurable_const
  · -- constant 0 is measurable
    exact measurable_const
