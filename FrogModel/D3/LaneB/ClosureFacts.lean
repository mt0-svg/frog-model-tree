module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# Deterministic facts about the closure

The closure of FrogModel/D3/Interfaces/Model.lean as a deterministic function of the child curves
and the directions (Sections 10 and 11 of the paper).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- `countAt` at a finite `n` is `dirCount`, dominates `dirCount` below `N`, and is monotone. -/
theorem countAt_facts (D : ℕ → Fin 4) (a : Fin 4) :
    (∀ n : ℕ, countAt D a n = dirCount D a n) ∧
      (∀ (k : ℕ) (N : ℕ∞), (k : ℕ∞) ≤ N → (dirCount D a k : ℕ∞) ≤ countAt D a N) ∧
      Monotone (countAt D a) := by
  have h_dirCount_mono : ∀ {m n : ℕ}, m ≤ n → dirCount D a m ≤ dirCount D a n := by
    intro m n h
    unfold dirCount
    have h_range : Finset.range m ⊆ Finset.range n :=
      (Finset.range_subset_range.2 h)
    have h_filter : ((Finset.range m).filter fun i => D i = a) ⊆
        ((Finset.range n).filter fun i => D i = a) :=
      Finset.filter_subset_filter _ h_range
    exact Finset.card_mono h_filter
  refine ⟨?_, ?_, ?_⟩
  · intro n
    apply le_antisymm
    · apply iSup₂_le
      intro n' hn'
      have hn'_nat : n' ≤ n := Nat.cast_le.mp hn'
      have h_card : dirCount D a n' ≤ dirCount D a n := h_dirCount_mono hn'_nat
      exact_mod_cast h_card
    · exact le_iSup₂ (f := λ n' _ => (dirCount D a n' : ℕ∞)) n le_rfl
  · intro k N hk
    exact le_iSup₂ (f := λ n _ => (dirCount D a n : ℕ∞)) k hk
  · intro N N' h
    apply iSup₂_le
    intro n hn
    apply le_iSup₂ (f := λ n' _ => (dirCount D a n' : ℕ∞)) n
    exact le_trans hn h

/-- The counts of the four directions add up, and each count is nondecreasing. -/
theorem sum_dirCount (D : ℕ → Fin 4) (n : ℕ) :
    ∑ a : Fin 4, dirCount D a n = n ∧ ∀ a, dirCount D a n ≤ dirCount D a (n + 1) := by
  constructor
  · -- ∑ a : Fin 4, dirCount D a n = n
    unfold dirCount
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.range n) (f := D)
      (t := Finset.univ) (by
        intro x hx
        simp)
    rw [Finset.card_range] at h
    rw [← h]
  · -- ∀ a, dirCount D a n ≤ dirCount D a (n + 1)
    intro a
    unfold dirCount
    refine Finset.card_le_card ?_
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.range_mono (Nat.le_succ n) hx.1, hx.2⟩

/-- At a finite end `N = n` of the closure, `q ≤ n` and `T(n) = n` (child curves nondecreasing). -/
theorem closT_closN (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4)
    (hG : ∀ c, Monotone (G c)) (n : ℕ) (hn : closN q G D = n) :
    q ≤ n ∧ closT q G D n = n := by
  -- define the set S = {m | q ≤ m ∧ T(m) ≤ m}
  set S : Set ℕ := {m | q ≤ m ∧ closT q G D m ≤ m} with hS
  -- convert closN to an infimum over S using iInf_subtype
  have hn_subtype : ⨅ (x : S), (x.val : ℕ∞) = (n : ℕ∞) := by
    simpa [closN, S, iInf_subtype] using hn
  -- use the lemma that characterizes when an iInf of ℕ∞ equals a natural number
  have h_eq := (ENat.iInf_eq_natCast_iff (f := fun (x : S) => (x.val : ℕ∞)) (n := n)).mp hn_subtype
  rcases h_eq with ⟨⟨x, hx_eq⟩, h_le⟩
  -- hx_eq : (x.val : ℕ∞) = (n : ℕ∞)
  -- h_le : ∀ (y : S), (n : ℕ∞) ≤ (y.val : ℕ∞)
  have hx_val_eq_n : x.val = n := by
    simpa using (ENat.natCast_inj (a := x.val) (b := n)).mp hx_eq
  -- from x.property we get q ≤ n and T(n) ≤ n
  have h_q_le_n : q ≤ n := by
    simpa [hx_val_eq_n] using x.property.1
  have h_T_le_n : closT q G D n ≤ n := by
    simpa [hx_val_eq_n] using x.property.2
  -- monotonicity of dirCount
  have h_dir_mono : ∀ (a : Fin 4) (m k : ℕ), m ≤ k → dirCount D a m ≤ dirCount D a k := by
    intro a m k hmk
    have h_range : Finset.range m ⊆ Finset.range k := Finset.range_mono hmk
    have h_filter : ((Finset.range m).filter fun i => D i = a) ⊆
        ((Finset.range k).filter fun i => D i = a) :=
      Finset.filter_subset_filter _ h_range
    exact Finset.card_mono h_filter
  -- monotonicity of closT
  have h_T_mono : ∀ (m k : ℕ), m ≤ k → closT q G D m ≤ closT q G D k := by
    intro m k hmk
    dsimp [closT]
    have h_sum : ∑ c : Fin 3, G c (dirCount D c.succ m) ≤
        ∑ c : Fin 3, G c (dirCount D c.succ k) := by
      refine Finset.sum_le_sum fun c _ => ?_
      exact hG c (h_dir_mono c.succ m k hmk)
    exact add_le_add_right h_sum (q : ℕ∞)
  -- now prove n ≤ T(n)
  by_cases h_eq_q : n = q
  · -- case n = q
    have h_q_le_Tq : (q : ℕ∞) ≤ closT q G D q := by
      dsimp [closT]
      have h_sum_nonneg : 0 ≤ ∑ c : Fin 3, G c (dirCount D c.succ q) :=
        Finset.sum_nonneg fun c _ => zero_le (a := G c (dirCount D c.succ q))
      exact le_add_of_nonneg_right h_sum_nonneg
    rw [h_eq_q] at h_T_le_n
    rw [h_eq_q]
    exact ⟨le_rfl, le_antisymm h_T_le_n h_q_le_Tq⟩
  · -- case q < n
    have h_lt_q_n : q < n := Nat.lt_of_le_of_ne h_q_le_n (Ne.symm h_eq_q)
    set m := n - 1 with hm_def
    have hm_lt_n : m < n := by
      omega
    have hm_le_n : m ≤ n := Nat.le_of_lt hm_lt_n
    have h_q_le_m : q ≤ m := by
      omega
    -- Since n is minimal in S, m ∉ S. But q ≤ m, so we must have ¬ (T(m) ≤ m)
    by_cases h_Tm_le_m : closT q G D m ≤ m
    · -- then m ∈ S, contradicting minimality of n
      have hm_mem_S : m ∈ S := by
        dsimp [S]
        exact ⟨h_q_le_m, h_Tm_le_m⟩
      have h_n_le_m : (n : ℕ∞) ≤ (m : ℕ∞) := h_le ⟨m, hm_mem_S⟩
      have h_n_le_m_nat : n ≤ m := by
        simpa using (ENat.natCast_le_natCast (n := n) (m := m)).mp h_n_le_m
      omega
    · -- m < T(m), so m+1 ≤ T(m), i.e., n ≤ T(m)
      have h_m_lt_Tm : (m : ℕ∞) < closT q G D m := lt_of_not_ge h_Tm_le_m
      have h_n_le_Tm : (n : ℕ∞) ≤ closT q G D m := by
        have h_add_one_le : (m : ℕ∞) + 1 ≤ closT q G D m :=
          (ENat.natCast_add_one_le_iff (m := m) (n := closT q G D m)).mpr h_m_lt_Tm
        have hm_add_one_eq_n : m + 1 = n := by
          omega
        have h_eq : (n : ℕ∞) = (m : ℕ∞) + 1 := by
          rw [← hm_add_one_eq_n, Nat.cast_add, Nat.cast_one]
        rw [h_eq]
        exact h_add_one_le
      have h_Tm_le_Tn : closT q G D m ≤ closT q G D n := h_T_mono m n hm_le_n
      have h_n_le_Tn : (n : ℕ∞) ≤ closT q G D n := le_trans h_n_le_Tm h_Tm_le_Tn
      exact ⟨h_q_le_n, le_antisymm h_T_le_n h_n_le_Tn⟩

/-- `N ≥ T(q) = q + ∑_c G_c(k_c(q))` (child curves nondecreasing). -/
theorem closT_q_le_closN (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4)
    (hG : ∀ c, Monotone (G c)) : closT q G D q ≤ closN q G D := by
  by_cases htop : closN q G D = ⊤
  · rw [htop]
    exact le_top
  · have h_exists : ∃ n : ℕ, closN q G D = n := by
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
      exact ⟨m, hm.symm⟩
    rcases h_exists with ⟨n, hn⟩
    have hT := closT_closN q G D hG n hn
    rcases hT with ⟨hq_le_n, hT_eq⟩
    rw [hn, ← hT_eq]
    unfold closT
    have h_dirCount : ∀ (a : Fin 4), dirCount D a q ≤ dirCount D a n := by
      intro a
      unfold dirCount
      refine Finset.card_le_card ?_
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      rcases hx with ⟨hx_range, hx_eq⟩
      refine ⟨?_, hx_eq⟩
      rw [Finset.mem_range] at hx_range ⊢
      omega
    have h_G : ∀ c : Fin 3, G c (dirCount D c.succ q) ≤ G c (dirCount D c.succ n) := by
      intro c
      apply hG c
      exact h_dirCount c.succ
    have h_sum : (∑ c : Fin 3, G c (dirCount D c.succ q)) ≤
                (∑ c : Fin 3, G c (dirCount D c.succ n)) := by
      apply Finset.sum_le_sum
      intro c _
      exact h_G c
    exact add_le_add_right h_sum (q : ℕ∞)

/-- The inclusion of the proof of Lemma 10.6 of the paper: `e_c < J` forces `N < k` or fewer than
`J` directions `c` among the first `k`. -/
theorem lemma8b_incl (q k J : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4)
    (c : Fin 3) (h : closE q G D c < J) : closN q G D < k ∨ dirCount D c.succ k < J := by
  by_cases hN : closN q G D < (k : ℕ∞)
  · left; exact hN
  · right
    have hk_le : (k : ℕ∞) ≤ closN q G D := not_lt.mp hN
    have hdir_le_closE : (dirCount D c.succ k : ℕ∞) ≤ closE q G D c := by
      calc
        (dirCount D c.succ k : ℕ∞) ≤ ⨆ (n : ℕ) (_ : (n : ℕ∞) ≤ closN q G D), (dirCount D c.succ n : ℕ∞) := by
          refine le_iSup₂ (f := fun (n : ℕ) (_ : (n : ℕ∞) ≤ closN q G D) => (dirCount D c.succ n : ℕ∞)) k hk_le
        _ = countAt D c.succ (closN q G D) := rfl
        _ = closE q G D c := rfl
    have h_lt : (dirCount D c.succ k : ℕ∞) < (J : ℕ∞) := lt_of_le_of_lt hdir_le_closE h
    exact_mod_cast h_lt

/-- `{i < e_c}` reads the curve of the child `c` only at `0, ..., i`. -/
theorem closE_stop (q i : ℕ) (c : Fin 3) (G G' : Fin 3 → ℕ → ℕ∞)
    (D : ℕ → Fin 4) (hG : ∀ c', c' ≠ c → G c' = G' c') (hc : ∀ k ≤ i, G c k = G' c k) :
    (i : ℕ∞) < closE q G D c ↔ (i : ℕ∞) < closE q G' D c := by
  let a : Fin 4 := c.succ
  -- Expand closE = countAt D a (closN q G D) = ⨆ n ≤ closN, dirCount D a n
  have h_expand (q i : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) :
      ((i : ℕ∞) < closE q G D c) ↔ ∃ n : ℕ, (n : ℕ∞) ≤ closN q G D ∧ (i : ℕ∞) < (dirCount D a n : ℕ∞) := by
    dsimp [a, closE, countAt]
    constructor
    · intro h
      rcases lt_iSup_iff.mp h with ⟨n, hn⟩
      rcases lt_iSup_iff.mp hn with ⟨hnN, hlt⟩
      exact ⟨n, hnN, hlt⟩
    · intro ⟨n, hnN, hlt⟩
      apply lt_iSup_iff.mpr
      refine ⟨n, ?_⟩
      apply lt_iSup_iff.mpr
      exact ⟨hnN, hlt⟩
  -- t ≤ closN iff t ≤ all n with q ≤ n and closT n ≤ n
  have h_le_closN_iff (t : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) :
      ((t : ℕ∞) ≤ closN q G D) ↔ ∀ n, q ≤ n → closT q G D n ≤ n → t ≤ n := by
    dsimp [closN]
    constructor
    · intro h n hq hT
      have h' := le_iInf_iff.mp h n
      have h'' := le_iInf_iff.mp h'
      have hcond : q ≤ n ∧ closT q G D n ≤ n := ⟨hq, hT⟩
      have hle := h'' hcond
      exact Nat.cast_le.mp hle
    · intro h
      apply le_iInf_iff.mpr
      intro n
      apply le_iInf_iff.mpr
      intro ⟨hq, hT⟩
      have hle : t ≤ n := h n hq hT
      exact Nat.cast_le.mpr hle
  -- Main forward step: if i < closE q G D c, then i < closE q G' D c
  have h_forward (G G' : Fin 3 → ℕ → ℕ∞) (hG : ∀ c', c' ≠ c → G c' = G' c') (hc : ∀ k ≤ i, G c k = G' c k)
      (h : (i : ℕ∞) < closE q G D c) : (i : ℕ∞) < closE q G' D c := by
    -- For n < t (where t is minimal with i < dirCount D a t), we have dirCount D a n ≤ i
    have h_dirCount_le_i (t : ℕ) (ht_min : ∀ m, m < t → ¬ ((i : ℕ∞) < (dirCount D a m : ℕ∞))) {n : ℕ} (hn : n < t) :
        (dirCount D a n : ℕ∞) ≤ (i : ℕ∞) := by
      have h_not_lt := ht_min n hn
      exact le_of_not_gt h_not_lt
    -- For n < t, closT q G D n = closT q G' D n
    have h_closT_eq (t : ℕ) (ht_min : ∀ m, m < t → ¬ ((i : ℕ∞) < (dirCount D a m : ℕ∞))) {n : ℕ} (hn : n < t) :
        closT q G D n = closT q G' D n := by
      dsimp [closT]
      congr 1
      apply Finset.sum_congr rfl
      intro c' _hc'
      by_cases hc'eq : c' = c
      · subst hc'eq
        have h_le_nat : dirCount D a n ≤ i := Nat.cast_le.mp (h_dirCount_le_i t ht_min hn)
        rw [hc (dirCount D a n) h_le_nat]
      · rw [hG c' hc'eq]
    rcases (h_expand q i G D).mp h with ⟨n, hnN, hlt⟩
    -- Let t be minimal with i < dirCount D a t
    let P : ℕ → Prop := λ m => (i : ℕ∞) < (dirCount D a m : ℕ∞)
    have hP_nonempty : ∃ m, P m := ⟨n, hlt⟩
    let t := Nat.find hP_nonempty
    have htP : P t := Nat.find_spec hP_nonempty
    have ht_min := λ m h => Nat.find_min hP_nonempty (m := m) h
    have h_lt_dirCount : (i : ℕ∞) < (dirCount D a t : ℕ∞) := htP
    -- t ≤ n by minimality
    have h_t_le_n : t ≤ n := by
      by_contra! h
      -- h : n < t
      exact ht_min n h hlt
    -- (t : ℕ∞) ≤ closN q G D
    have h_t_le_closN_G : (t : ℕ∞) ≤ closN q G D := by
      have h_t_le_n' : (t : ℕ∞) ≤ (n : ℕ∞) := Nat.cast_le.mpr h_t_le_n
      exact le_trans h_t_le_n' hnN
    -- (t : ℕ∞) ≤ closN q G' D
    have h_t_le_closN_G' : (t : ℕ∞) ≤ closN q G' D := by
      apply (h_le_closN_iff t G' D).mpr
      intro m hq hT'
      by_contra! h_lt
      -- h_lt : m < t
      have h_dirCount_le : (dirCount D a m : ℕ∞) ≤ (i : ℕ∞) := h_dirCount_le_i t ht_min h_lt
      have h_dirCount_le_nat : dirCount D a m ≤ i := Nat.cast_le.mp h_dirCount_le
      have h_closT_eq_m : closT q G D m = closT q G' D m := h_closT_eq t ht_min h_lt
      have hT : closT q G D m ≤ m := by
        rw [h_closT_eq_m]
        exact hT'
      have h_t_le_m : t ≤ m := ((h_le_closN_iff t G D).mp h_t_le_closN_G) m hq hT
      linarith
    -- Conclude i < closE q G' D c
    apply (h_expand q i G' D).mpr
    exact ⟨t, h_t_le_closN_G', h_lt_dirCount⟩
  constructor
  · exact h_forward G G' hG hc
  · -- symmetric: swap G and G'
    have hG' : ∀ c', c' ≠ c → G' c' = G c' := λ c' hne => (hG c' hne).symm
    have hc' : ∀ k ≤ i, G' c k = G c k := λ k hk => (hc k hk).symm
    exact h_forward G' G hG' hc'


lemma closNstop_dirCount_congr {i : ℕ} (D D' : ℕ → Fin 4) (hD : ∀ l < i, D l = D' l) (a : Fin 4) (n : ℕ) (hn : n ≤ i) :
    dirCount D a n = dirCount D' a n := by
  dsimp [dirCount]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x hx
  have hxl : x < i := lt_of_lt_of_le (Finset.mem_range.mp hx) hn
  simp [hD x hxl]

lemma closNstop_closT_congr {i : ℕ} (q : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D D' : ℕ → Fin 4) (hD : ∀ l < i, D l = D' l) (n : ℕ) (hn : n ≤ i) :
    closT q G D n = closT q G D' n := by
  dsimp [closT]
  congr
  ext c
  simp [closNstop_dirCount_congr D D' hD c.succ n hn]

lemma closNstop_lt_iff (q i : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4) :
    (i : ℕ∞) < closN q G D ↔ ¬ ∃ n, n ≤ i ∧ q ≤ n ∧ closT q G D n ≤ n := by
  dsimp [closN]
  constructor
  · intro hlt ⟨n, hn_le, hq, hT⟩
    have h_le : (⨅ (n : ℕ) (_ : q ≤ n ∧ closT q G D n ≤ n), (n : ℕ∞)) ≤ (n : ℕ∞) := by
      apply iInf_le_of_le n
      apply iInf_le_of_le ⟨hq, hT⟩
      rfl
    have h_le' : (n : ℕ∞) ≤ (i : ℕ∞) := ENat.natCast_le_natCast.mpr hn_le
    have : (i : ℕ∞) < (i : ℕ∞) := lt_of_lt_of_le hlt (le_trans h_le h_le')
    exact lt_irrefl _ this
  · intro h
    rw [lt_iInf_iff]
    refine ⟨(i+1 : ℕ∞), ?_, ?_⟩
    · -- (i : ℕ∞) < (i+1 : ℕ∞)
      have : (i : ℕ) < i+1 := Nat.lt_succ_self i
      exact ENat.natCast_lt_natCast.mpr this
    · -- ∀ (n : ℕ), (i+1 : ℕ∞) ≤ iInf (fun (_ : q ≤ n ∧ closT q G D n ≤ n) => (n : ℕ∞))
      intro n
      apply le_iInf
      intro hcond
      rcases hcond with ⟨hq, hT⟩
      have hi_lt_n : i < n := by
        by_contra! hi_ge
        -- hi_ge : n ≤ i
        have h_exists : ∃ n, n ≤ i ∧ q ≤ n ∧ closT q G D n ≤ n :=
          ⟨n, hi_ge, hq, hT⟩
        exact h h_exists
      have : (i+1 : ℕ) ≤ n := by omega
      exact ENat.natCast_le_natCast.mpr this

/-- `{i < N}` reads only the directions before `i`. -/
theorem closN_stop (q i : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D D' : ℕ → Fin 4)
    (hD : ∀ l < i, D l = D' l) : (i : ℕ∞) < closN q G D ↔ (i : ℕ∞) < closN q G D' := by
  rw [closNstop_lt_iff q i G D, closNstop_lt_iff q i G D']
  constructor
  · intro h h'
    rcases h' with ⟨n, hn_le, hq, hT⟩
    apply h
    refine ⟨n, hn_le, hq, ?_⟩
    have hT' := closNstop_closT_congr q G D D' hD n hn_le
    rw [hT']
    exact hT
  · intro h h'
    rcases h' with ⟨n, hn_le, hq, hT⟩
    apply h
    refine ⟨n, hn_le, hq, ?_⟩
    have hT' := closNstop_closT_congr q G D' D (fun l hl => (hD l hl).symm) n hn_le
    rw [hT']
    exact hT

/-- Before the end `N` of the closure, fewer than `q + 3B` ups have occurred when every child curve
satisfies `G_c(k) ≤ k + B`. -/
theorem closN_kup_bound (q B : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4)
    (hG : ∀ c k, G c k ≤ ((k + B : ℕ) : ℕ∞)) (n : ℕ) (hn : (n : ℕ∞) < closN q G D) :
    dirCount D 0 n < q + 3 * B := by
  by_cases h : n < q
  · -- case n < q: dirCount D 0 n ≤ n < q ≤ q + 3*B
    have hcard : dirCount D 0 n ≤ n := by
      dsimp [dirCount]
      calc
        ((Finset.range n).filter fun i => D i = (0 : Fin 4)).card ≤ (Finset.range n).card :=
          Finset.card_filter_le _ _
        _ = n := Finset.card_range n
    omega
  · -- case q ≤ n
    have hq_le_n : q ≤ n := by omega
    -- closT q G D n > n, otherwise closN ≤ n contradicting hn
    have h_closT_gt_n : (n : ℕ∞) < closT q G D n := by
      by_contra! hle
      have hle' : closT q G D n ≤ (n : ℕ∞) := hle
      have h_closN_le_n : closN q G D ≤ (n : ℕ∞) := by
        have := iInf₂_le (f := fun (k : ℕ) (_ : q ≤ k ∧ closT q G D k ≤ k) => (k : ℕ∞)) (i := n) (j := ⟨hq_le_n, hle'⟩)
        simpa [closN] using this
      have : (n : ℕ∞) < (n : ℕ∞) := lt_of_lt_of_le hn h_closN_le_n
      exact lt_irrefl _ this
    -- Let S := ∑_c (dirCount D c.succ n : ℕ∞)
    set S := (∑ c : Fin 3, (dirCount D c.succ n : ℕ∞)) with hS
    -- Partition: dirCount D 0 n + S = n (in ℕ∞)
    have h_partition_nat : (∑ a : Fin 4, dirCount D a n) = n := by
      simp_rw [dirCount]
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      simp
    have h_partition : (dirCount D 0 n : ℕ∞) + S = (n : ℕ∞) := by
      have hsum4 : (∑ a : Fin 4, (dirCount D a n : ℕ∞)) = (n : ℕ∞) := by
        simpa [Nat.cast_sum] using congrArg (fun x : ℕ => (x : ℕ∞)) h_partition_nat
      rw [Fin.sum_univ_four] at hsum4
      have hsum3 : (∑ c : Fin 3, (dirCount D c.succ n : ℕ∞)) =
          (dirCount D 1 n : ℕ∞) + (dirCount D 2 n : ℕ∞) + (dirCount D 3 n : ℕ∞) := by
        rw [Fin.sum_univ_three]
        simp
      rw [hsum3] at hS
      rw [hS]
      simpa [add_assoc] using hsum4
    -- Now: n < q + S + 3*B (from closT bound)
    have h_closT_bound : (n : ℕ∞) < (q : ℕ∞) + S + (3 * B : ℕ∞) := by
      calc
        (n : ℕ∞) < closT q G D n := h_closT_gt_n
        _ = (q : ℕ∞) + (∑ c : Fin 3, G c (dirCount D c.succ n)) := rfl
        _ ≤ (q : ℕ∞) + (∑ c : Fin 3, ((dirCount D c.succ n + B : ℕ) : ℕ∞)) := by
          refine add_le_add_right (Finset.sum_le_sum fun c _ => hG c (dirCount D c.succ n)) (q : ℕ∞)
        _ = (q : ℕ∞) + ((∑ c : Fin 3, (dirCount D c.succ n : ℕ∞)) + (3 * B : ℕ∞)) := by
          simp [Finset.sum_add_distrib]
        _ = (q : ℕ∞) + S + (3 * B : ℕ∞) := by rw [hS]; ring
    -- Cancel S (which is finite) from the inequality
    have h_fin_S : S ≠ ⊤ := by
      rw [hS]
      simp
    have h_ineq : (dirCount D 0 n : ℕ∞) < (q : ℕ∞) + (3 * B : ℕ∞) := by
      have h_temp : (dirCount D 0 n : ℕ∞) + S < (q : ℕ∞) + S + (3 * B : ℕ∞) := by
        rw [h_partition]
        exact h_closT_bound
      have h_rhs : (q : ℕ∞) + S + (3 * B : ℕ∞) = ((q : ℕ∞) + (3 * B : ℕ∞)) + S := by
        simp [add_assoc, add_comm, add_left_comm]
      rw [h_rhs] at h_temp
      exact (ENat.add_lt_add_iff_right h_fin_S).mp h_temp
    -- Cast back to ℕ
    have : (dirCount D 0 n : ℕ∞) < (q + 3 * B : ℕ) := by
      simpa [Nat.cast_add, Nat.cast_mul] using h_ineq
    exact_mod_cast this

/-- At a finite end `N = n`: `n = X + ∑_c e_c`. -/
theorem sum_countAt_closN (q n : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4)
    (hn : closN q G D = n) :
    closX q G D + ∑ c : Fin 3, closE q G D c = (n : ℕ∞) := by
  -- rewrite closX and closE using hn
  have hX : closX q G D = countAt D 0 n := by
    dsimp [closX]
    rw [hn]
  have hE : ∑ c : Fin 3, closE q G D c = ∑ c : Fin 3, countAt D c.succ n := by
    simp [closE, hn]
  rw [hX, hE]
  -- replace countAt with dirCount using countAt_facts
  have h_count (a : Fin 4) : countAt D a n = (dirCount D a n : ℕ∞) :=
    (countAt_facts D a).1 n
  simp_rw [h_count]
  -- combine the sum using Fin.sum_univ_succ
  have h_sum : (dirCount D 0 n : ℕ∞) + ∑ c : Fin 3, (dirCount D c.succ n : ℕ∞) =
      (∑ a : Fin 4, (dirCount D a n : ℕ∞)) := by
    simpa using (Fin.sum_univ_succ (fun a : Fin 4 => (dirCount D a n : ℕ∞))).symm
  rw [h_sum]
  -- use sum_dirCount
  have h_total : (∑ a : Fin 4, dirCount D a n : ℕ∞) = (n : ℕ∞) := by
    simpa using congrArg (fun x : ℕ => (x : ℕ∞)) ((sum_dirCount D n).1)
  simp [h_total]

/-- Relabeling the children by a permutation `σ` (and the directions accordingly) permutes the
entry counts at the end of the closure. -/
theorem closE_perm (σ : Equiv.Perm (Fin 3)) (q : ℕ) (G : Fin 3 → ℕ → ℕ∞)
    (D : ℕ → Fin 4) (c : Fin 3) :
    closE q (fun c' => G (σ c')) (fun i => Fin.cases 0 (fun c' => (σ.symm c').succ) (D i)) c =
      closE q G D (σ c) := by
  -- define the permuted G and D for readability
  let G' : Fin 3 → ℕ → ℕ∞ := fun c' => G (σ c')
  let D' : ℕ → Fin 4 := fun i => Fin.cases 0 (fun c' : Fin 3 => (σ.symm c').succ) (D i)
  have hD'_zero : ∀ i, D' i = 0 ↔ D i = 0 := by
    intro i
    have h_cases : ∀ x : Fin 4,
        Fin.cases (0 : Fin 4) (fun c' : Fin 3 => (σ.symm c').succ) x = (0 : Fin 4) ↔ x = 0 := by
      intro x
      refine Fin.cases ?_ ?_ x
      · simp
      · intro y; simp
    simpa [D'] using h_cases (D i)
  have hD'_succ : ∀ (c' : Fin 3) (i : ℕ),
      D' i = Fin.succ c' ↔ D i = Fin.succ (σ c') := by
    intro c' i
    have h_cases : ∀ x : Fin 4,
        Fin.cases (0 : Fin 4) (fun c' : Fin 3 => (σ.symm c').succ) x = Fin.succ c' ↔
          x = Fin.succ (σ c') := by
      intro x
      refine Fin.cases ?_ ?_ x
      · -- x = 0
        constructor
        · intro h; exact (Fin.succ_ne_zero c').elim h.symm
        · intro h; exact (Fin.succ_ne_zero (σ c')).elim h.symm
      · -- x = Fin.succ y
        intro y
        simp [Fin.succ_inj, Equiv.symm_apply_eq]
    simp [D', h_cases]
  have h_dirCount_succ : ∀ (c' : Fin 3) (n : ℕ),
      dirCount D' (Fin.succ c') n = dirCount D (Fin.succ (σ c')) n := by
    intro c' n
    simp [dirCount]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i hi
    simp [hD'_succ c' i]
  have h_closT : ∀ n : ℕ, closT q G' D' n = closT q G D n := by
    intro n
    simp [closT, G', h_dirCount_succ]
    rw [Equiv.sum_comp σ (fun c => G c (dirCount D c.succ n))]
  have h_closN : closN q G' D' = closN q G D := by
    simp [closN, h_closT]
  calc
    closE q G' D' c = countAt D' (Fin.succ c) (closN q G' D') := rfl
    _ = countAt D' (Fin.succ c) (closN q G D) := by rw [h_closN]
    _ = countAt D (Fin.succ (σ c)) (closN q G D) := by
      simp [countAt, h_dirCount_succ]
    _ = closE q G D (σ c) := rfl

/-- The pathwise bound behind Lemma 10.6 of the paper: for a nondecreasing curve and an entry count
`e`, `(G(J) - J/3) - (G(e ∧ J) - (e ∧ J)/3) ≤ (G(J) - G(e)) 1{e < J}`. -/
theorem lemma8a_pathwise (G : ℕ → ℕ∞) (_hG : Monotone G) (B : ℕ)
    (_hB : ∀ k, G k ≤ ((k + B : ℕ) : ℕ∞)) (e : ℕ∞) (J : ℕ) :
    ((G J).toNat : ℝ) - J / 3 - (((G (minE e J)).toNat : ℝ) - (minE e J : ℝ) / 3) ≤
      if e < J then ((G J).toNat : ℝ) - (G e.toNat).toNat else 0 := by
  by_cases h : e < (J : ℕ∞)
  · rw [ite_eq_left h]
    have hmin : minE e J = e.toNat := by
      dsimp [minE]
      rw [min_eq_left (le_of_lt h)]
    rw [hmin]
    have hJ_ne_top : (J : ℕ∞) ≠ ⊤ := by
      simp
    have hle_nat : e.toNat ≤ J :=
      ENat.toNat_le_toNat (le_of_lt h) hJ_ne_top
    have hle_real : (e.toNat : ℝ) ≤ (J : ℝ) := by exact_mod_cast hle_nat
    nlinarith
  · rw [ite_eq_right h]
    have hmin : minE e J = J := by
      dsimp [minE]
      rw [min_eq_right (le_of_not_gt h), ENat.toNat_natCast]
    rw [hmin]
    nlinarith

end FrogModel.D3.Iface
