module

public import FrogModel.Pieces.Basic

@[expose] public section

/-!
# The gluing lemma (Lemma 3.2 of the paper)

The glued steps of the frogs have the law of the frog model: `map_glue`. No strong Markov
property is used. The position of the glued walk at time `t` (segment index and time since the
segment started) is a function `posOf` of the glued steps before `t` (`posOf_glue`,
`glue_eq_posOf`, `posOf_congr`), and distinct times have distinct positions (`posOf_ne`). So the
event that the glued steps of a frog start with a given prefix is a cylinder over distinct piece
coordinates (`glue_prefix_succ`, `glue_prefix_insens`), whose probability is the product of the
step probabilities (`map_glueOne`), and prefix cylinders determine a law (`ext_of_prefix`).
-/

open MeasureTheory
open scoped ENNReal
open FrogModel

theorem FrogModel.walk_congr {d : ℕ} (u : Vertex d) (x y : ℕ → Step d) (n : ℕ)
    (h : ∀ i < n, x i = y i) : walk u x n = walk u y n := by
  induction' n with n ih
  · rfl
  · rw [walk, walk]
    have hxn : x n = y n := h n (Nat.lt_succ_self n)
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), hxn]

theorem FrogModel.posOf_congr {d : ℕ} (u : Vertex d) (x y : ℕ → Step d) (t : ℕ)
    (h : ∀ i < t, x i = y i) : posOf u x t = posOf u y t := by
  have walk_congr (u : Vertex d) (x y : ℕ → Step d) (n : ℕ) (hwalk : ∀ i < n, x i = y i) :
      walk u x n = walk u y n := by
    induction' n with n ih
    · rfl
    · have hn : x n = y n := hwalk n (Nat.lt_succ_self n)
      have h_ih : ∀ i < n, x i = y i := fun i hi =>
        hwalk i (Nat.lt_of_lt_of_le hi (Nat.le_succ n))
      rw [walk, walk, ih h_ih, hn]
  have h_returns : returns u x t = returns u y t := by
    unfold returns
    refine Finset.filter_congr fun s hs => ?_
    have hs_le_t : s ≤ t := (Finset.mem_Icc.mp hs).right
    have hwalk_eq : walk u x s = walk u y s :=
      walk_congr u x y s fun i hi => h i (lt_of_lt_of_le hi hs_le_t)
    simp [hwalk_eq]
  simp [posOf, h_returns]

theorem FrogModel.posOf_ne {d : ℕ} (u : Vertex d) (x : ℕ → Step d) (s t : ℕ) (hst : s < t) :
    posOf u x s ≠ posOf u x t := by
  intro h_eq
  have h_sub : returns u x s ⊆ returns u x t := by
    intro a ha
    simp [returns, Finset.mem_filter, Finset.mem_Icc] at ha ⊢
    rcases ha with ⟨⟨h1, h2⟩, ha_eq⟩
    exact ⟨⟨h1, Nat.le_of_lt (Nat.lt_of_le_of_lt h2 hst)⟩, ha_eq⟩
  have h_card_eq : (returns u x s).card = (returns u x t).card := by
    have := congr_arg Prod.fst h_eq
    simpa [posOf] using this
  have h_eq_set : returns u x s = returns u x t :=
    Finset.eq_of_subset_of_card_le h_sub (by rw [h_card_eq])
  have h_sup_eq : (returns u x s).sup id = (returns u x t).sup id := by
    rw [h_eq_set]
  have h_sub_s : ∀ a ∈ returns u x s, a ≤ s := by
    intro a ha
    have ha_mem := (Finset.mem_filter.mp ha).1
    rcases Finset.mem_Icc.mp ha_mem with ⟨_, h⟩
    exact h
  have h_sub_t : ∀ a ∈ returns u x t, a ≤ t := by
    intro a ha
    have ha_mem := (Finset.mem_filter.mp ha).1
    rcases Finset.mem_Icc.mp ha_mem with ⟨_, h⟩
    exact h
  have h_sup_le_s : (returns u x s).sup id ≤ s :=
    Finset.sup_le h_sub_s
  have h_sup_le_t : (returns u x t).sup id ≤ t :=
    Finset.sup_le h_sub_t
  have h_sup_le_t' : (returns u x s).sup id ≤ t := by
    rw [h_sup_eq]
    exact h_sup_le_t
  have h_sub_eq : s - (returns u x s).sup id = t - (returns u x s).sup id := by
    calc
      s - (returns u x s).sup id = t - (returns u x t).sup id := by
        simpa [posOf] using congr_arg Prod.snd h_eq
      _ = t - (returns u x s).sup id := by rw [h_sup_eq]
  have hst_eq : s = t := by
    have h1 : (s - (returns u x s).sup id) + (returns u x s).sup id = s :=
      Nat.sub_add_cancel h_sup_le_s
    have h2 : (t - (returns u x s).sup id) + (returns u x s).sup id = t :=
      Nat.sub_add_cancel h_sup_le_t'
    calc
      s = (s - (returns u x s).sup id) + (returns u x s).sup id := by rw [h1]
      _ = (t - (returns u x s).sup id) + (returns u x s).sup id := by rw [h_sub_eq]
      _ = t := by rw [h2]
  exact Nat.lt_irrefl s (hst_eq ▸ hst)

theorem FrogModel.cutSum_lt_succ {d : ℕ} (ζ : Pieces d) (u : Vertex d) (k : ℕ)
    (h : cutSum ζ u (k + 1) ≠ ⊤) : cutSum ζ u k < cutSum ζ u (k + 1) := by
  have h_eq : cutSum ζ u (k + 1) = cutSum ζ u k + segCut ζ (u, k) := rfl
  rw [h_eq]
  have h_ne_top : cutSum ζ u k ≠ ⊤ := by
    intro htop
    apply h
    rw [h_eq, htop]
    simp
  have h_one_le : 1 ≤ segCut ζ (u, k) := by
    dsimp [segCut]
    exact FrogModel.one_le_cut (Seg.start (u, k)) (ζ (u, k))
  rcases ENat.ne_top_iff_exists.mp h_ne_top with ⟨m, hm⟩
  rw [hm.symm]
  have h_lt : (m : ℕ∞) < (m : ℕ∞) + 1 := ENat.natCast_lt_succ
  have h_le : (m : ℕ∞) + 1 ≤ (m : ℕ∞) + segCut ζ (u, k) :=
    add_le_add_right h_one_le (m : ℕ∞)
  exact lt_of_lt_of_le h_lt h_le

theorem FrogModel.cutSum_le_iff {d : ℕ} (ζ : Pieces d) (u : Vertex d) (k t : ℕ) :
    cutSum ζ u k ≤ t ↔ k ≤ segAt ζ u t := by
  have hspec := FrogModel.segAt_spec ζ u t
  have hmono := FrogModel.cutSum_mono ζ u
  constructor
  · intro hle
    by_contra! hlt
    have hlt' : segAt ζ u t + 1 ≤ k := by omega
    have hcut := hmono hlt'
    have hspec' := hspec.2
    have : (t : ℕ∞) < cutSum ζ u k := lt_of_lt_of_le hspec' hcut
    have : cutSum ζ u k ≤ (t : ℕ∞) := hle
    exact not_lt.mpr this ‹_›
  · intro hle
    have hcut := hmono hle
    have hspec' := hspec.1
    exact le_trans hcut hspec'

theorem FrogModel.returns_glue {d : ℕ} (ζ : Pieces d) (u : Vertex d) (t : ℕ) :
    returns u (glue ζ u) t =
      (Finset.range (segAt ζ u t)).image fun k => (cutSum ζ u (k + 1)).toNat := by
  ext s
  constructor
  · intro hs
    unfold returns at hs
    rw [Finset.mem_filter] at hs
    rcases hs with ⟨hs_mem, hs_root⟩
    rw [Finset.mem_Icc] at hs_mem
    rcases hs_mem with ⟨hs_one, hs_t⟩
    have h_exists := ((glue_root_iff ζ u s hs_one).mp hs_root)
    rcases h_exists with ⟨k, hk⟩
    have hk_le : cutSum ζ u (k + 1) ≤ (t : ℕ∞) := by
      rw [hk]
      exact_mod_cast hs_t
    have hk_seg : k + 1 ≤ segAt ζ u t := ((cutSum_le_iff ζ u (k + 1) t).mp hk_le)
    have hk_lt : k < segAt ζ u t := by omega
    have hk_toNat : (cutSum ζ u (k + 1)).toNat = s := by
      rw [hk]
      simp
    apply Finset.mem_image.mpr
    exact ⟨k, Finset.mem_range.mpr hk_lt, hk_toNat⟩
  · intro hs
    rw [Finset.mem_image] at hs
    rcases hs with ⟨k, hk_mem, hk_eq⟩
    rw [Finset.mem_range] at hk_mem
    have hk_seg : k + 1 ≤ segAt ζ u t := by omega
    have hk_cut_le : cutSum ζ u (k + 1) ≤ (t : ℕ∞) := ((cutSum_le_iff ζ u (k + 1) t).mpr hk_seg)
    have hk_not_top : cutSum ζ u (k + 1) ≠ ⊤ := by
      intro htop
      rw [htop] at hk_cut_le
      have : ¬ (⊤ : ℕ∞) ≤ (t : ℕ∞) := by simp
      exact this hk_cut_le
    have h_coe_toNat : ((cutSum ζ u (k + 1)).toNat : ℕ∞) = cutSum ζ u (k + 1) :=
      ENat.natCast_toNat hk_not_top
    let s' := (cutSum ζ u (k + 1)).toNat
    have hs'_one : 1 ≤ s' := by
      have hk_le_cut : (k + 1 : ℕ∞) ≤ cutSum ζ u (k + 1) := le_cutSum ζ u (k + 1)
      rw [← h_coe_toNat] at hk_le_cut
      have : (k + 1 : ℕ) ≤ s' := by
        simpa using ENat.natCast_le_natCast.mp hk_le_cut
      omega
    have hs'_t : s' ≤ t := by
      have : (s' : ℕ∞) ≤ (t : ℕ∞) := by
        rw [h_coe_toNat]
        exact hk_cut_le
      exact_mod_cast this
    have hs'_root : walk u (glue ζ u) s' = root := by
      apply ((glue_root_iff ζ u s' hs'_one).mpr ?_)
      refine ⟨k, ?_⟩
      dsimp [s']; exact h_coe_toNat.symm
    have hs'_eq_s : s' = s := by simpa [s'] using hk_eq
    apply Finset.mem_filter.mpr
    have hmem_Icc : s ∈ Finset.Icc 1 t := by
      rw [← hs'_eq_s]
      exact Finset.mem_Icc.mpr ⟨hs'_one, hs'_t⟩
    have hwalk_root : walk u (glue ζ u) s = root := by
      rw [← hs'_eq_s]
      exact hs'_root
    exact ⟨hmem_Icc, hwalk_root⟩

namespace FrogModel

/-- If `a < b` and `b ≠ ⊤` then `a.toNat < b.toNat`. -/
lemma toNat_lt_toNat_of_ne_top {a b : ℕ∞} (h : a < b) (hb : b ≠ ⊤) : a.toNat < b.toNat := by
  have ha : a ≠ ⊤ := by
    intro htop; rw [htop] at h; exact lt_irrefl _ (h.trans_le le_top)
  have hle : a ≤ b := le_of_lt h
  have hle_toNat : a.toNat ≤ b.toNat := ENat.toNat_le_toNat hle hb
  by_contra! heq
  have heq' : a.toNat = b.toNat := by omega
  have ha_eq : a = (a.toNat : ℕ∞) := by rw [ENat.natCast_toNat ha]
  have hb_eq : b = (b.toNat : ℕ∞) := by rw [ENat.natCast_toNat hb]
  rw [ha_eq, hb_eq, heq'] at h
  exact lt_irrefl _ h

/-- If `cut v x` is finite, it is positive (≥ 1). -/
lemma cut_pos {d : ℕ} {v : Vertex d} {x : ℕ → Step d} (h : cut v x ≠ ⊤) : 0 < cut v x := by
  dsimp [cut] at h
  by_contra! hle
  have hzero : sInf ((fun n : ℕ => (n : ℕ∞)) '' {n | 1 ≤ n ∧ walk v x n = root}) = 0 := by
    apply le_antisymm hle
    apply zero_le
  rw [ENat.sInf_eq_zero] at hzero
  rcases (Set.mem_image (f := fun n : ℕ => (n : ℕ∞)) (s := {n | 1 ≤ n ∧ walk v x n = root}) (y := 0)).mp hzero with ⟨n, hn, hn'⟩
  rcases hn with ⟨hn1, hn2⟩
  have hn0 : n = 0 := by
    simpa using hn'
  rw [hn0] at hn1
  exact Nat.not_succ_le_zero 0 hn1

end FrogModel

theorem FrogModel.card_returns_glue {d : ℕ} (ζ : Pieces d) (u : Vertex d) (t : ℕ) :
    (returns u (glue ζ u) t).card = segAt ζ u t := by
  rw [FrogModel.returns_glue]
  -- Now we need: ((Finset.range (segAt ζ u t)).image fun k => (cutSum ζ u (k + 1)).toNat).card = segAt ζ u t
  -- By card_image_of_injOn, it suffices to show injectivity
  have h_inj : Set.InjOn (fun k : ℕ => (cutSum ζ u (k + 1)).toNat) (Finset.range (segAt ζ u t) : Set ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_range] at hx hy
    -- hx: x < segAt ζ u t, hy: y < segAt ζ u t
    by_contra! hne
    -- hne: x ≠ y
    have hx_lt_y_or : x < y ∨ y < x := Nat.lt_or_gt_of_ne hne
    rcases hx_lt_y_or with (hlt | hlt)
    · -- case x < y
      have hx_seg : cutSum ζ u (x + 1) ≤ (t : ℕ∞) := by
        rw [FrogModel.cutSum_le_iff]
        omega
      have hy_seg : cutSum ζ u (y + 1) ≤ (t : ℕ∞) := by
        rw [FrogModel.cutSum_le_iff]
        omega
      have hx_fin : cutSum ζ u (x + 1) ≠ ⊤ := by
        intro htop; rw [htop] at hx_seg; exact lt_irrefl _ (hx_seg.trans_lt (ENat.natCast_lt_top _))
      have hy_fin : cutSum ζ u (y + 1) ≠ ⊤ := by
        intro htop; rw [htop] at hy_seg; exact lt_irrefl _ (hy_seg.trans_lt (ENat.natCast_lt_top _))
      have hle : cutSum ζ u (x + 1) ≤ cutSum ζ u y := by
        apply FrogModel.cutSum_mono ζ u
        omega
      have hlt' : cutSum ζ u y < cutSum ζ u (y + 1) := by
        apply FrogModel.cutSum_lt_succ ζ u y
        intro htop
        rw [htop] at hy_seg
        exact lt_irrefl _ (hy_seg.trans_lt (ENat.natCast_lt_top _))
      have h_lt : cutSum ζ u (x + 1) < cutSum ζ u (y + 1) :=
        lt_of_le_of_lt hle hlt'
      have h_toNat_lt : (cutSum ζ u (x + 1)).toNat < (cutSum ζ u (y + 1)).toNat :=
        toNat_lt_toNat_of_ne_top h_lt hy_fin
      have hxy' : (cutSum ζ u (x + 1)).toNat = (cutSum ζ u (y + 1)).toNat := by simpa using hxy
      rw [hxy'] at h_toNat_lt
      exact lt_irrefl _ h_toNat_lt
    · -- case y < x: symmetric
      have hy_seg : cutSum ζ u (y + 1) ≤ (t : ℕ∞) := by
        rw [FrogModel.cutSum_le_iff]
        omega
      have hx_seg : cutSum ζ u (x + 1) ≤ (t : ℕ∞) := by
        rw [FrogModel.cutSum_le_iff]
        omega
      have hy_fin : cutSum ζ u (y + 1) ≠ ⊤ := by
        intro htop; rw [htop] at hy_seg; exact lt_irrefl _ (hy_seg.trans_lt (ENat.natCast_lt_top _))
      have hx_fin : cutSum ζ u (x + 1) ≠ ⊤ := by
        intro htop; rw [htop] at hx_seg; exact lt_irrefl _ (hx_seg.trans_lt (ENat.natCast_lt_top _))
      have hle : cutSum ζ u (y + 1) ≤ cutSum ζ u x := by
        apply FrogModel.cutSum_mono ζ u
        omega
      have hlt' : cutSum ζ u x < cutSum ζ u (x + 1) := by
        apply FrogModel.cutSum_lt_succ ζ u x
        intro htop
        rw [htop] at hx_seg
        exact lt_irrefl _ (hx_seg.trans_lt (ENat.natCast_lt_top _))
      have h_lt : cutSum ζ u (y + 1) < cutSum ζ u (x + 1) :=
        lt_of_le_of_lt hle hlt'
      have h_toNat_lt : (cutSum ζ u (y + 1)).toNat < (cutSum ζ u (x + 1)).toNat :=
        toNat_lt_toNat_of_ne_top h_lt hx_fin
      have hxy' : (cutSum ζ u (x + 1)).toNat = (cutSum ζ u (y + 1)).toNat := by simpa using hxy
      rw [hxy'] at h_toNat_lt
      exact lt_irrefl _ h_toNat_lt
  -- Now apply card_image_of_injOn
  have hcard := Finset.card_image_of_injOn h_inj
  rw [hcard, Finset.card_range]

theorem FrogModel.sup_returns_glue {d : ℕ} (ζ : Pieces d) (u : Vertex d) (t : ℕ) :
    (returns u (glue ζ u) t).sup id = (cutSum ζ u (segAt ζ u t)).toNat := by
  rw [FrogModel.returns_glue]
  rw [Finset.sup_image]
  cases' hseg : segAt ζ u t with m
  · -- segAt ζ u t = 0
    simp [FrogModel.cutSum]
  · -- segAt ζ u t = m+1
    have hle : cutSum ζ u (m + 1) ≤ (t : ℕ∞) := by
      rw [FrogModel.cutSum_le_iff ζ u (m+1) t]
      rw [hseg]
    have hfin : cutSum ζ u (m + 1) ≠ ⊤ := by
      intro htop
      rw [htop] at hle
      have hlt : (t : ℕ∞) < ⊤ := ENat.natCast_lt_top t
      have : (⊤ : ℕ∞) < ⊤ := hle.trans_lt hlt
      exact lt_irrefl _ this
    have hm : m ∈ Finset.range (m + 1) := by
      rw [Finset.mem_range]
      omega
    apply le_antisymm
    · -- LHS ≤ RHS
      refine Finset.sup_le ?_
      intro k hk
      rw [Finset.mem_range] at hk
      have hk' : k + 1 ≤ m + 1 := by omega
      have hcut := FrogModel.cutSum_mono ζ u hk'
      exact ENat.toNat_le_toNat hcut hfin
    · -- RHS ≤ LHS
      simpa using Finset.le_sup (s := Finset.range (m+1)) (f := fun k => (cutSum ζ u (k + 1)).toNat) hm

theorem FrogModel.posOf_glue {d : ℕ} (ζ : Pieces d) (u : Vertex d) (t : ℕ) :
    posOf u (glue ζ u) t = (segAt ζ u t, t - (cutSum ζ u (segAt ζ u t)).toNat) := by
  unfold posOf
  rw [card_returns_glue, sup_returns_glue]

theorem FrogModel.glue_eq_posOf {d : ℕ} (ζ : Pieces d) (u : Vertex d) (t : ℕ) :
    glue ζ u t = ζ (u, (posOf u (glue ζ u) t).1) (posOf u (glue ζ u) t).2 := by
  rw [posOf_glue, glue]

theorem FrogModel.glue_prefix_congr {d : ℕ} (ζ ζ' : Pieces d) (u : Vertex d) (N : ℕ)
    (h : ∀ t < N, ζ' (u, (posOf u (glue ζ u) t).1) (posOf u (glue ζ u) t).2 =
      ζ (u, (posOf u (glue ζ u) t).1) (posOf u (glue ζ u) t).2) :
    ∀ t < N, glue ζ' u t = glue ζ u t := by
  intro t ht
  induction' t using Nat.strong_induction_on with t ih
  have h_eq : ∀ s < t, glue ζ' u s = glue ζ u s := by
    intro s hs
    have hs_N : s < N := lt_trans hs ht
    exact ih s hs hs_N
  have h_pos : posOf u (glue ζ' u) t = posOf u (glue ζ u) t :=
    posOf_congr u (glue ζ' u) (glue ζ u) t h_eq
  calc
    glue ζ' u t = ζ' (u, (posOf u (glue ζ' u) t).1) (posOf u (glue ζ' u) t).2 := by
      rw [glue_eq_posOf]
    _ = ζ' (u, (posOf u (glue ζ u) t).1) (posOf u (glue ζ u) t).2 := by rw [h_pos]
    _ = ζ (u, (posOf u (glue ζ u) t).1) (posOf u (glue ζ u) t).2 := by rw [h t ht]
    _ = glue ζ u t := by rw [glue_eq_posOf]

theorem FrogModel.glue_prefix_succ {d : ℕ} (u : Vertex d) (a : ℕ → Step d) (N : ℕ) :
    {ζ : Pieces d | ∀ i < N + 1, glue ζ u i = a i} =
      {ζ : Pieces d | ∀ i < N, glue ζ u i = a i} ∩
        {ζ : Pieces d | ζ (u, (posOf u a N).1) (posOf u a N).2 = a N} := by
  ext ζ
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    have hN : ∀ i < N, glue ζ u i = a i := fun i hi => h i (Nat.lt_succ_of_lt hi)
    refine ⟨hN, ?_⟩
    have hp : posOf u (glue ζ u) N = posOf u a N := posOf_congr u _ _ N hN
    have h' := h N (Nat.lt_succ_self N)
    rw [glue_eq_posOf, hp] at h'
    exact h'
  · rintro ⟨hN, hq⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hN i hi
    · have hp : posOf u (glue ζ u) i = posOf u a i := posOf_congr u _ _ i hN
      rw [glue_eq_posOf, hp]
      exact hq

theorem FrogModel.glue_prefix_insens {d : ℕ} (ζ ζ' : Pieces d) (u : Vertex d)
    (a : ℕ → Step d) (N : ℕ) (ha : ∀ i < N, glue ζ u i = a i)
    (h : ∀ k j, (k, j) ≠ posOf u a N → ζ' (u, k) j = ζ (u, k) j) :
    ∀ i < N, glue ζ' u i = a i := by
  intro i hi
  have h_congr := glue_prefix_congr ζ ζ' u N (by
    intro t ht
    have hpos_eq_t : posOf u (glue ζ u) t = posOf u a t := by
      apply posOf_congr u (glue ζ u) a t
      intro j hj
      exact ha j (lt_of_lt_of_le hj (by omega))
    have hpos_ne_t : posOf u a t ≠ posOf u a N := by
      apply posOf_ne u a t N ht
    have h_eq := h (posOf u a t).1 (posOf u a t).2 hpos_ne_t
    -- h_eq : ζ' (u, (posOf u a t).1) (posOf u a t).2 = ζ (u, (posOf u a t).1) (posOf u a t).2
    -- need to rewrite using hpos_eq_t
    simpa [hpos_eq_t] using h_eq)
  have ha_eq := ha i hi
  rw [h_congr i hi, ha_eq]

theorem FrogModel.glue_congr {d : ℕ} (ζ ζ' : Pieces d) (u : Vertex d)
    (h : ∀ k, ζ (u, k) = ζ' (u, k)) : glue ζ u = glue ζ' u := by
  have h_cutSum : ∀ k, cutSum ζ u k = cutSum ζ' u k := by
    intro k
    induction' k with k ih
    · rfl
    · unfold cutSum
      rw [ih]
      have h_segCut : segCut ζ (u, k) = segCut ζ' (u, k) := by
        unfold segCut
        rw [h k]
      rw [h_segCut]
  have h_cutSum_eq : cutSum ζ u = cutSum ζ' u := funext h_cutSum
  have h_segAt : ∀ t, segAt ζ u t = segAt ζ' u t := by
    intro t
    unfold segAt
    have h_filter_eq : ((Finset.range (t + 1)).filter fun k => cutSum ζ u (k + 1) ≤ t) =
                       ((Finset.range (t + 1)).filter fun k => cutSum ζ' u (k + 1) ≤ t) := by
      apply Finset.filter_congr
      intro k hk
      simp [h_cutSum]
    rw [h_filter_eq]
  funext t
  unfold glue
  rw [h_segAt t]
  have h_cutSum_at_segAt : cutSum ζ u (segAt ζ' u t) = cutSum ζ' u (segAt ζ' u t) := by
    rw [h_cutSum_eq]
  rw [h_cutSum_at_segAt]
  rw [h (segAt ζ' u t)]

theorem FrogModel.measurable_glue {d : ℕ} (u : Vertex d) (t : ℕ) :
    Measurable fun ζ : Pieces d => glue ζ u t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    -- Φ : Pieces d → (Fin t → Step d)
    let Φ : Pieces d → (Fin t → Step d) := fun ζ i => glue ζ u i
    have hΦ_meas : Measurable Φ := by
      refine Measurable.of_eval (fun i => ?_)
      have hi : (i : ℕ) < t := i.2
      exact ih (i : ℕ) hi
    -- p(ζ) := posOf u (glue ζ u) t factors through Φ
    let p : Pieces d → ℕ × ℕ := fun ζ => posOf u (glue ζ u) t
    have hp_factor : ∀ S : Set (ℕ × ℕ), p ⁻¹' S = Φ ⁻¹' (Φ '' (p ⁻¹' S)) := by
      intro S
      ext ζ
      constructor
      · intro h
        exact ⟨ζ, h, rfl⟩
      · intro h
        rcases h with ⟨ζ', hζ', hΦeq⟩
        have hp_eq : p ζ = p ζ' := by
          dsimp [p]
          refine posOf_congr u (glue ζ u) (glue ζ' u) t (fun i hi => ?_)
          have hΦval : Φ ζ ⟨i, hi⟩ = Φ ζ' ⟨i, hi⟩ := by
            simpa [Φ] using (congrFun hΦeq ⟨i, hi⟩).symm
          simpa [Φ] using hΦval
        simpa [hp_eq] using hζ'
    have hp_meas : Measurable p := by
      intro S hS
      rw [hp_factor S]
      have h_finite_univ : Set.Finite (Set.univ : Set (Fin t → Step d)) := by
        have : Finite (Fin t → Step d) := inferInstance
        exact Set.finite_univ
      have h_subset : Φ '' (p ⁻¹' S) ⊆ Set.univ := Set.subset_univ _
      have h_finite : Set.Finite (Φ '' (p ⁻¹' S)) := h_finite_univ.subset h_subset
      have h_meas_set : MeasurableSet (Φ '' (p ⁻¹' S)) := Set.Finite.measurableSet h_finite
      exact hΦ_meas h_meas_set
    -- Now show glue is measurable using the factorization
    have h_glue_fiber : ∀ b : Step d, MeasurableSet {ζ : Pieces d | glue ζ u t = b} := by
      intro b
      have h_eq : {ζ : Pieces d | glue ζ u t = b} =
          ⋃ (q : ℕ × ℕ), (p ⁻¹' {q}) ∩ {ζ : Pieces d | ζ (u, q.1) q.2 = b} := by
        ext ζ
        constructor
        · intro h
          refine Set.mem_iUnion.mpr ⟨p ζ, ?_, ?_⟩
          · exact Set.mem_preimage.mpr rfl
          · dsimp [p]
            rw [← glue_eq_posOf ζ u t, h]
        · intro h
          rcases Set.mem_iUnion.mp h with ⟨q, hq_mem, hq_eq⟩
          rcases q with ⟨a, b'⟩
          have hq_p : p ζ = (a, b') := by
            have := Set.mem_preimage.mp hq_mem
            simpa using this
          have hq_val : ζ (u, a) b' = b := hq_eq
          have ha : (p ζ).1 = a := by simpa using congrArg Prod.fst hq_p
          have hb' : (p ζ).2 = b' := by simpa using congrArg Prod.snd hq_p
          rw [← ha, ← hb'] at hq_val
          -- hq_val : ζ (u, (p ζ).1) (p ζ).2 = b
          -- goal : glue ζ u t = b
          have h_glue_eq : glue ζ u t = ζ (u, (p ζ).1) (p ζ).2 := by
            simpa [p] using glue_eq_posOf ζ u t
          show glue ζ u t = b
          rw [h_glue_eq]
          exact hq_val
      rw [h_eq]
      refine MeasurableSet.iUnion fun q => ?_
      have hp_meas_set : MeasurableSet (p ⁻¹' {q}) :=
        hp_meas (MeasurableSingletonClass.measurableSet_singleton _)
      have h_eval_meas : Measurable fun ζ : Pieces d => ζ (u, q.1) q.2 := by
        have h1 : Measurable fun ζ : Pieces d => ζ (u, q.1) := measurable_pi_apply (u, q.1)
        have h2 : Measurable fun f : ℕ → Step d => f q.2 := measurable_pi_apply q.2
        exact h2.comp h1
      have h_singleton_meas : MeasurableSet ({b} : Set (Step d)) :=
        MeasurableSingletonClass.measurableSet_singleton _
      have h_fiber_meas : MeasurableSet {ζ : Pieces d | ζ (u, q.1) q.2 = b} :=
        h_singleton_meas.preimage h_eval_meas
      exact MeasurableSet.inter hp_meas_set h_fiber_meas
    -- Now use measurable_to_countable' on the target Step d
    refine measurable_to_countable' (fun b => ?_)
    exact h_glue_fiber b

theorem FrogModel.ext_of_prefix {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (μ ν : Measure (ℕ → α)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ (N : ℕ) (a : ℕ → α), μ {x | ∀ i < N, x i = a i} = ν {x | ∀ i < N, x i = a i}) :
    μ = ν := by
  by_cases hα : IsEmpty α
  · have h_empty : IsEmpty (ℕ → α) :=
      ((isEmpty_fun (α := ℕ) (β := α)).mpr ⟨inferInstance, hα⟩)
    have : Subsingleton (Measure (ℕ → α)) := by infer_instance
    exact Subsingleton.elim μ ν
  · have hα' : Nonempty α := not_isEmpty_iff.mp hα
    obtain ⟨a₀⟩ := hα'
    let C : Set (Set (ℕ → α)) := {s | ∃ (N : ℕ) (a : ℕ → α), s = {x | ∀ i < N, x i = a i}}
    have hC : IsPiSystem C := by
      rintro s₁ hs₁ s₂ hs₂ hne
      rcases hs₁ with ⟨N₁, a₁, rfl⟩
      rcases hs₂ with ⟨N₂, a₂, rfl⟩
      -- hne : ({x | ∀ i < N₁, x i = a₁ i} ∩ {x | ∀ i < N₂, x i = a₂ i}).Nonempty
      obtain ⟨x₀, hx₀⟩ := hne
      rcases hx₀ with ⟨hx₁, hx₂⟩
      refine ⟨max N₁ N₂, x₀, ?_⟩
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hx₁', hx₂'⟩
        intro i hi
        rcases lt_max_iff.mp hi with (hiN₁ | hiN₂)
        · rw [hx₁' i hiN₁, hx₁ i hiN₁]
        · rw [hx₂' i hiN₂, hx₂ i hiN₂]
      · intro hx
        have hx₁' : ∀ i < N₁, x i = a₁ i := by
          intro i hi
          have hi' : i < max N₁ N₂ := lt_of_lt_of_le hi (le_max_left _ _)
          rw [hx i hi']
          exact hx₁ i hi
        have hx₂' : ∀ i < N₂, x i = a₂ i := by
          intro i hi
          have hi' : i < max N₁ N₂ := lt_of_lt_of_le hi (le_max_right _ _)
          rw [hx i hi']
          exact hx₂ i hi
        exact ⟨hx₁', hx₂'⟩
    have hA : MeasurableSpace.pi = MeasurableSpace.generateFrom C := by
      apply le_antisymm
      · -- pi ≤ generateFrom C
        rw [MeasurableSpace.pi_eq_generateFrom_projections]
        refine MeasurableSpace.generateFrom_le fun B hB => ?_
        obtain ⟨i, A, hAmeas, rfl⟩ := hB
        -- B = eval i ⁻¹' A = {x | x i ∈ A}
        -- Write as countable union of cylinder sets indexed by Fin (i+1) → α
        have h_countable_A : A.Countable := by
          have : Countable (Subtype (· ∈ A)) := by infer_instance
          rw [← Set.countable_coe_iff]
          exact this
        -- The index set: {c : Fin (i+1) → α | c ⟨i, _⟩ ∈ A}
        let idx : Set (Fin (i + 1) → α) := {c | c ⟨i, by omega⟩ ∈ A}
        have h_countable_idx : idx.Countable := by
          apply Set.Countable.mono _ (Set.countable_univ (α := Fin (i + 1) → α))
          intro c hc
          simp [idx] at hc
          exact Set.mem_univ c
        have h_eq : (fun x : ℕ → α => x i) ⁻¹' A = ⋃ c ∈ idx, {x : ℕ → α | ∀ (j : ℕ) (hj : j < i + 1), x j = c ⟨j, hj⟩} := by
          ext x
          constructor
          · intro hx
            have hx' : x i ∈ A := hx
            -- define c by restricting x to Fin (i+1)
            let c : Fin (i + 1) → α := fun ⟨j, hj⟩ => x j
            have hc : c ∈ idx := by
              dsimp [idx]
              simpa [c] using hx'
            have hx_in : x ∈ {x : ℕ → α | ∀ (j : ℕ) (hj : j < i + 1), x j = c ⟨j, hj⟩} := by
              intro j hj
              simp [c]
            exact Set.mem_iUnion₂.mpr ⟨c, hc, hx_in⟩
          · intro hx
            rcases Set.mem_iUnion₂.mp hx with ⟨c, hc, hx'⟩
            have hi : i < i + 1 := by omega
            have hxi : x i = c ⟨i, hi⟩ := hx' i hi
            -- goal: x i ∈ A
            dsimp [idx] at hc
            simpa [hxi] using hc
        rw [h_eq]
        -- Each cylinder set is in C
        have h_each (c : Fin (i + 1) → α) : {x : ℕ → α | ∀ (j : ℕ) (hj : j < i + 1), x j = c ⟨j, hj⟩} ∈ C := by
          dsimp [C]
          refine ⟨i + 1, fun j => if hj : j < i + 1 then c ⟨j, hj⟩ else a₀, ?_⟩
          ext x
          constructor
          · intro hx j hj
            simp [hj, hx j hj]
          · intro hx j hj
            simp [hj, hx j hj]
        -- Countable union of measurable sets is measurable
        refine MeasurableSet.biUnion h_countable_idx fun c hc => ?_
        have h_mem : {x : ℕ → α | ∀ (j : ℕ) (hj : j < i + 1), x j = c ⟨j, hj⟩} ∈ C := h_each c
        exact MeasurableSpace.measurableSet_generateFrom h_mem
      · -- generateFrom C ≤ pi
        refine MeasurableSpace.generateFrom_le fun s hs => ?_
        obtain ⟨N, a, rfl⟩ := hs
        -- {x | ∀ i < N, x i = a i} is an intersection of measurable sets in pi
        have h_singleton (i : ℕ) : MeasurableSet ({a i} : Set α) :=
          MeasurableSet.singleton _
        have h_preimage (i : ℕ) : MeasurableSet ((fun x : ℕ → α => x i) ⁻¹' {a i}) :=
          (measurable_pi_apply i) (h_singleton i)
        have h_finite : ({i : ℕ | i < N} : Set ℕ).Countable :=
          (Set.finite_lt_nat N).countable
        have h_eq : {x | ∀ i < N, x i = a i} = ⋂ i ∈ ({i : ℕ | i < N} : Set ℕ), (fun x : ℕ → α => x i) ⁻¹' {a i} := by
          ext x; simp
        rw [h_eq]
        exact MeasurableSet.biInter h_finite (fun i hi => h_preimage i)
    have h_univ : μ Set.univ = ν Set.univ := by
      simp [IsProbabilityMeasure.measure_univ]
    refine MeasureTheory.ext_of_generate_finite C hA hC (fun s hs => ?_) h_univ
    obtain ⟨N, a, rfl⟩ := hs
    exact h N a

theorem FrogModel.infinitePi_prefix {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] (N : ℕ)
    (a : ℕ → α) :
    Measure.infinitePi (fun _ : ℕ => μ) {x | ∀ i < N, x i = a i} =
      ∏ i ∈ Finset.range N, μ {a i} := by
  have h_eq : {x | ∀ i < N, x i = a i} = (Finset.range N : Set ℕ).pi (fun i => {a i}) := by
    ext x
    simp [Set.mem_pi]
  rw [h_eq]
  refine MeasureTheory.Measure.infinitePi_pi (fun _ : ℕ => μ) ?_
  intro i hi
  exact measurableSet_singleton (a i)

namespace FrogModel

variable {d : ℕ}

/-- The glued steps of one frog `u` from its pieces `Z k`, `k ∈ ℕ`. -/
noncomputable def glueOne (u : Vertex d) (Z : ℕ → ℕ → Step d) : ℕ → Step d :=
  glue (fun σ => Z σ.2) u

theorem measurable_glueOne (u : Vertex d) : Measurable (glueOne (d := d) u) :=
  Measurable.of_eval fun t =>
    (measurable_glue u t).comp (Measurable.of_eval fun (σ : Seg d) => measurable_pi_apply σ.2)

theorem measurableSet_prefix {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (N : ℕ) (a : ℕ → α) : MeasurableSet {x : ℕ → α | ∀ i < N, x i = a i} := by
  have h : {x : ℕ → α | ∀ i < N, x i = a i} = ⋂ i ∈ Finset.range N, (fun x => x i) ⁻¹' {a i} := by
    ext x; simp
  rw [h]
  exact Finset.measurableSet_biInter _ fun i _ => measurable_pi_apply i (measurableSet_singleton _)

/-- The law of the glued steps of one frog is the law of an i.i.d. step sequence. -/
theorem map_glueOne [NeZero d] (u : Vertex d) :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d).map
        (glueOne u) = Measure.infinitePi fun _ : ℕ => stepLaw d := by
  have hflat : (Measure.infinitePi fun _ : ℕ × ℕ => stepLaw d).map
      (MeasurableEquiv.curry ℕ ℕ (Step d)) =
        Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d :=
    Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : ℕ) => stepLaw d)
  have hmeas : Measurable (glueOne (d := d) u ∘ MeasurableEquiv.curry ℕ ℕ (Step d)) :=
    (measurable_glueOne u).comp (MeasurableEquiv.measurable _)
  rw [← hflat, Measure.map_map (measurable_glueOne u) (MeasurableEquiv.measurable _)]
  apply ext_of_prefix
  intro N a
  rw [Measure.map_apply hmeas (measurableSet_prefix N a), infinitePi_prefix]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ← ih]
    set q := posOf u a N
    set G := (glueOne (d := d) u ∘ MeasurableEquiv.curry ℕ ℕ (Step d)) ⁻¹'
      {x | ∀ i < N, x i = a i} with hGdef
    have hset : (glueOne (d := d) u ∘ MeasurableEquiv.curry ℕ ℕ (Step d)) ⁻¹'
        {x | ∀ i < N + 1, x i = a i} =
          G ∩ {W | ∀ p ∈ ({q} : Finset (ℕ × ℕ)), W p ∈ ({a N} : Set (Step d))} := by
      ext W
      have h := Set.ext_iff.mp (glue_prefix_succ u a N) fun σ j => W (σ.2, j)
      rw [Set.mem_inter_iff]
      simp only [Finset.mem_singleton, forall_eq, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      exact h
    have hins : ∀ W W' : ℕ × ℕ → Step d, (∀ p ∉ ({q} : Finset (ℕ × ℕ)), W p = W' p) →
        (W ∈ G ↔ W' ∈ G) := by
      intro W W' hW
      have key : ∀ V V' : ℕ × ℕ → Step d, (∀ p ∉ ({q} : Finset (ℕ × ℕ)), V p = V' p) →
          V ∈ G → V' ∈ G := by
        intro V V' hV hmem
        exact glue_prefix_insens (fun σ j => V (σ.2, j)) (fun σ j => V' (σ.2, j)) u a N hmem
          fun k j hkj => (hV (k, j) fun h => hkj (Finset.mem_singleton.mp h)).symm
      exact ⟨key W W' hW, key W' W fun p hp => (hW p hp).symm⟩
    rw [hset, Stage.infinitePi_inter_cyl _ {q} G (hmeas (measurableSet_prefix N a)) hins
      (fun _ => {a N}) (fun _ => measurableSet_singleton _), Finset.prod_singleton]

/-- **Gluing lemma.** The glued step sequences of the frogs have the law of the frog model. -/
theorem map_glue [NeZero d] : (piecesMeasure d).map (fun ζ u => glue ζ u) = frogMeasure d := by
  have hcur : (piecesMeasure d).map (MeasurableEquiv.curry (Vertex d) ℕ (ℕ → Step d)) =
      Measure.infinitePi fun _ : Vertex d =>
        Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d :=
    Measure.infinitePi_map_curry
      (fun (_ : Vertex d) (_ : ℕ) => Measure.infinitePi fun _ : ℕ => stepLaw d)
  have hfac : (fun (ζ : Pieces d) (u : Vertex d) => glue ζ u) =
      (fun (Z : Vertex d → ℕ → ℕ → Step d) (u : Vertex d) => glueOne u (Z u)) ∘
        MeasurableEquiv.curry (Vertex d) ℕ (ℕ → Step d) := by
    funext ζ u
    exact glue_congr ζ (fun σ => ζ (u, σ.2)) u fun _ => rfl
  have hg : Measurable fun (Z : Vertex d → ℕ → ℕ → Step d) (u : Vertex d) => glueOne u (Z u) :=
    Measurable.of_eval fun u => (measurable_glueOne u).comp (measurable_pi_apply u)
  rw [hfac, ← Measure.map_map hg (MeasurableEquiv.measurable _), hcur, Measure.infinitePi_map_pi _ measurable_glueOne]
  unfold frogMeasure
  congr 1
  funext u
  exact map_glueOne u

end FrogModel
