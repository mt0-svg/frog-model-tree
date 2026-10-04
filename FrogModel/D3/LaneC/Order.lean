module

public import FrogModel.D3.Interfaces.Step

@[expose] public section

/-!
# The order facts of the step map

Nonnegativity of the bounds and laws that `Phi^S` reads, and its monotonicity in the ratios
`mu_h(k')/mu_(h+1)(j)` and in the parent mean `mu_(a+1)(j)` of the terms of Lemma 11.1 (3) of the
paper: the content of Lemma 12.5 (2), and the algebra of the deficit terms of Lemma 12.5 (1).
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneC

theorem ratio_mono (a b m k j : ℕ) (ham : a ≤ m) (hmb : m ≤ b) :
    ratio m m k j ≤ ratio a b k j := by
  -- Simplify mu x k / mu (x+1) j = (x+1+k)/(x+2+j)
  have h_simplify (x : ℕ) : mu x k / mu (x + 1) j = ((x : ℝ) + 1 + k) / ((x : ℝ) + 2 + j) := by
    dsimp [mu]
    field_simp
    push_cast
    ring
  have hratio_self : ratio m m k j = mu m k / mu (m + 1) j := by
    dsimp [ratio]
    simp
  rw [hratio_self]
  dsimp [ratio]
  rw [h_simplify m, h_simplify a, h_simplify b]
  -- Goal: ((m : ℝ) + 1 + k) / ((m : ℝ) + 2 + j) ≤ max (((a : ℝ) + 1 + k) / ((a : ℝ) + 2 + j)) (((b : ℝ) + 1 + k) / ((b : ℝ) + 2 + j))
  -- Denominators are positive
  have hpos_m : 0 < (m : ℝ) + 2 + j := by positivity
  have hpos_a : 0 < (a : ℝ) + 2 + j := by positivity
  have hpos_b : 0 < (b : ℝ) + 2 + j := by positivity
  -- Convert Nat inequalities to ℝ
  have hm_le_b : (m : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hmb
  have ha_le_m : (a : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr ham
  -- Case on whether k ≤ j+1 or not
  by_cases hkj : (k : ℝ) ≤ (j : ℝ) + 1
  · -- f(h) = (h+1+k)/(h+2+j) is nondecreasing when k ≤ j+1
    -- So f(m) ≤ f(b) (since m ≤ b), and f(b) ≤ max(f(a), f(b))
    have hmb' : ((m : ℝ) + 1 + k) / ((m : ℝ) + 2 + j) ≤ ((b : ℝ) + 1 + k) / ((b : ℝ) + 2 + j) := by
      rw [div_le_div_iff₀ hpos_m hpos_b]
      nlinarith
    have h_le_max : ((b : ℝ) + 1 + k) / ((b : ℝ) + 2 + j) ≤
        max (((a : ℝ) + 1 + k) / ((a : ℝ) + 2 + j)) (((b : ℝ) + 1 + k) / ((b : ℝ) + 2 + j)) :=
      le_max_right _ _
    exact le_trans hmb' h_le_max
  · -- f(h) is nonincreasing when k > j+1, so f(m) ≤ f(a) (since m ≥ a)
    have ham' : ((m : ℝ) + 1 + k) / ((m : ℝ) + 2 + j) ≤ ((a : ℝ) + 1 + k) / ((a : ℝ) + 2 + j) := by
      rw [div_le_div_iff₀ hpos_m hpos_a]
      nlinarith
    have h_le_max : ((a : ℝ) + 1 + k) / ((a : ℝ) + 2 + j) ≤
        max (((a : ℝ) + 1 + k) / ((a : ℝ) + 2 + j)) (((b : ℝ) + 1 + k) / ((b : ℝ) + 2 + j)) :=
      le_max_left _ _
    exact le_trans ham' h_le_max

theorem ratio_nonneg (a b k j : ℕ) : 0 ≤ ratio a b k j := by
  dsimp [ratio]
  have hpos : ∀ m k : ℕ, 0 < mu m k := by
    intro m k
    dsimp [mu]
    positivity
  have h1 : 0 ≤ mu a k / mu (a + 1) j :=
    div_nonneg (le_of_lt (hpos a k)) (le_of_lt (hpos (a + 1) j))
  have h2 : 0 ≤ mu b k / mu (b + 1) j :=
    div_nonneg (le_of_lt (hpos b k)) (le_of_lt (hpos (b + 1) j))
  exact le_max_of_le_left h1

theorem envelope_nonneg (W : ℕ → ℝ) (S s : ℕ) : 0 ≤ envelope W S s := by
  unfold envelope
  rw [Finset.le_fold_max]
  left
  exact le_rfl

theorem plF_nonneg (F : ℕ → ℕ → ℝ) (GM e : ℕ) (h0 : 0 ≤ F e 0)
    (hmono : ∀ g < GM, F e g ≤ F e (g + 1)) (g : ℕ) : 0 ≤ plF F GM e g := by
  dsimp [plF]
  split
  · -- g ≤ GM
    split
    · -- g = 0
      subst ‹_›
      simpa using h0
    · -- g ≠ 0
      rename_i hg_ne
      have hgpos : 0 < g := Nat.pos_of_ne_zero hg_ne
      have hgsub_lt_GM : g - 1 < GM := by
        apply lt_of_lt_of_le (Nat.sub_lt hgpos (by omega)) ‹_›
      have h := hmono (g - 1) hgsub_lt_GM
      -- h : F e (g - 1) ≤ F e ((g - 1) + 1)
      have h_eq : (g - 1) + 1 = g := Nat.sub_add_cancel (Nat.one_le_of_lt hgpos)
      rw [h_eq] at h
      linarith
  · -- ¬ g ≤ GM
    exact le_refl 0

theorem convF_nonneg (F : ℕ → ℕ → ℝ) (GM : ℕ) (e : Fin 3 → ℕ)
    (hpl : ∀ c g, 0 ≤ plF F GM (e c) g) (s : ℕ) : 0 ≤ convF F GM e s := by
  unfold convF
  refine Finset.sum_nonneg fun g1 _ => ?_
  refine Finset.sum_nonneg fun g2 _ => ?_
  split_ifs with h
  · have h0 : 0 ≤ plF F GM (e 0) g1 := hpl 0 g1
    have h1 : 0 ≤ plF F GM (e 1) g2 := hpl 1 g2
    have h2 : 0 ≤ plF F GM (e 2) (s - g1 - g2) := hpl 2 (s - g1 - g2)
    positivity
  · rfl

theorem mem_grid (GM q K : ℕ) (hK : K ∈ grid GM q) : q < K ∧ K - q - 1 ≤ GM := by
  rcases Finset.mem_insert.mp hK with (hK | hK)
  · -- K = q + GM + 1
    subst hK
    constructor
    · omega
    · omega
  · -- K ∈ gridOffsets.image fun o => min (q + o) (q + GM + 1)
    rcases Finset.mem_image.mp hK with ⟨o, ho, rfl⟩
    have ho8 : 8 ≤ o := by
      simp [gridOffsets] at ho
      rcases ho with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega
    have hq_lt_min : q < min (q + o) (q + GM + 1) := by
      rw [Nat.lt_min]
      constructor
      · omega
      · omega
    have h_min_le : min (q + o) (q + GM + 1) ≤ q + GM + 1 := Nat.min_le_right _ _
    constructor
    · exact hq_lt_min
    · omega

theorem boundB_nonneg (F : ℕ → ℕ → ℝ) (E GM q J K : ℕ)
    (h0 : ∀ e ≤ E, ∀ g ≤ GM, 0 ≤ F e g) (hmono : ∀ e ≤ E, ∀ g < GM, F e g ≤ F e (g + 1))
    (hJE : J ≤ E) (hK : K - q - 1 ≤ GM) : 0 ≤ boundB F E GM q J K := by
  unfold boundB
  have hpart1 : 0 ≤ (∑ e ∈ Fintype.piFinset (fun c : Fin 3 => if c = 0 then Finset.range J else Finset.range E),
      ∑ s ∈ Finset.range K, envelope (WB q K e) K s * convF F GM e s) := by
    refine Finset.sum_nonneg fun e he => ?_
    refine Finset.sum_nonneg fun s hs => ?_
    have henvelope : 0 ≤ envelope (WB q K e) K s := by
      unfold envelope
      rw [Finset.le_fold_max]
      left
      rfl
    have hconvF : 0 ≤ convF F GM e s := by
      unfold convF
      refine Finset.sum_nonneg fun g1 hg1 => ?_
      refine Finset.sum_nonneg fun g2 hg2 => ?_
      by_cases hsum : g1 + g2 ≤ s
      · simp [hsum]
        have hpl0 : 0 ≤ plF F GM (e 0) g1 := by
          unfold plF
          by_cases hg1leGM : g1 ≤ GM
          · simp [hg1leGM]
            by_cases hg0 : g1 = 0
            · simp [hg0]
              have he0leE : e 0 ≤ E := by
                have := Fintype.mem_piFinset.mp he
                have hmem := this 0
                simp at hmem
                exact Nat.le_trans (Nat.le_of_lt hmem) hJE
              have h0leGM : (0 : ℕ) ≤ GM := by omega
              exact h0 (e 0) he0leE 0 h0leGM
            · simp [hg0]
              have he0leE : e 0 ≤ E := by
                have := Fintype.mem_piFinset.mp he
                have hmem := this 0
                simp at hmem
                exact Nat.le_trans (Nat.le_of_lt hmem) hJE
              have hg1pos : 0 < g1 := Nat.pos_of_ne_zero hg0
              have hg1ltGM : g1 - 1 < GM := by
                have : g1 - 1 < g1 := Nat.sub_lt hg1pos (by omega)
                exact Nat.lt_of_lt_of_le this hg1leGM
              have hineq : F (e 0) (g1 - 1) ≤ F (e 0) g1 := by
                have h := hmono (e 0) he0leE (g1 - 1) hg1ltGM
                have : (g1 - 1) + 1 = g1 := Nat.sub_add_cancel hg1pos
                simpa [this] using h
              exact hineq
          · simp [hg1leGM]
        have hpl1 : 0 ≤ plF F GM (e 1) g2 := by
          unfold plF
          by_cases hg2leGM : g2 ≤ GM
          · simp [hg2leGM]
            by_cases hg0 : g2 = 0
            · simp [hg0]
              have he1leE : e 1 ≤ E := by
                have := Fintype.mem_piFinset.mp he
                have hmem := this 1
                simp at hmem
                exact Nat.le_of_lt hmem
              have h0leGM : (0 : ℕ) ≤ GM := by omega
              exact h0 (e 1) he1leE 0 h0leGM
            · simp [hg0]
              have he1leE : e 1 ≤ E := by
                have := Fintype.mem_piFinset.mp he
                have hmem := this 1
                simp at hmem
                exact Nat.le_of_lt hmem
              have hg2pos : 0 < g2 := Nat.pos_of_ne_zero hg0
              have hg2ltGM : g2 - 1 < GM := by
                have : g2 - 1 < g2 := Nat.sub_lt hg2pos (by omega)
                exact Nat.lt_of_lt_of_le this hg2leGM
              have hineq : F (e 1) (g2 - 1) ≤ F (e 1) g2 := by
                have h := hmono (e 1) he1leE (g2 - 1) hg2ltGM
                have : (g2 - 1) + 1 = g2 := Nat.sub_add_cancel hg2pos
                simpa [this] using h
              exact hineq
          · simp [hg2leGM]
        have hpl2 : 0 ≤ plF F GM (e 2) (s - g1 - g2) := by
          unfold plF
          by_cases hleGM : s - g1 - g2 ≤ GM
          · simp [hleGM]
            by_cases hg0 : s - g1 - g2 = 0
            · simp [hg0]
              have he2leE : e 2 ≤ E := by
                have := Fintype.mem_piFinset.mp he
                have hmem := this 2
                simp at hmem
                exact Nat.le_of_lt hmem
              have h0leGM : (0 : ℕ) ≤ GM := by omega
              exact h0 (e 2) he2leE 0 h0leGM
            · simp [hg0]
              have he2leE : e 2 ≤ E := by
                have := Fintype.mem_piFinset.mp he
                have hmem := this 2
                simp at hmem
                exact Nat.le_of_lt hmem
              have hpos : 0 < s - g1 - g2 := Nat.pos_of_ne_zero hg0
              have hltGM : (s - g1 - g2) - 1 < GM := by
                have : (s - g1 - g2) - 1 < s - g1 - g2 := Nat.sub_lt hpos (by omega)
                exact Nat.lt_of_lt_of_le this hleGM
              have hineq : F (e 2) ((s - g1 - g2) - 1) ≤ F (e 2) (s - g1 - g2) := by
                have h := hmono (e 2) he2leE ((s - g1 - g2) - 1) hltGM
                have : ((s - g1 - g2) - 1) + 1 = s - g1 - g2 := Nat.sub_add_cancel hpos
                simpa [this] using h
              exact hineq
          · simp [hleGM]
        positivity
      · simp [hsum]
    exact mul_nonneg henvelope hconvF
  have hpart2 : 0 ≤ 2 * binGe (E + J - 1) (1 / 2) E * F E (K - q - 1) := by
    have hbinGe : 0 ≤ binGe (E + J - 1) (1 / 2) E := by
      unfold binGe
      refine Finset.sum_nonneg fun i hi => ?_
      unfold binPmf
      have hchoose : 0 ≤ (Nat.choose (E + J - 1) i : ℝ) :=
        Nat.cast_nonneg _
      have hp : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have h1mp : 0 ≤ (1 - (1 / 2 : ℝ)) := by norm_num
      positivity
    have hF : 0 ≤ F E (K - q - 1) :=
      h0 E (le_refl E) (K - q - 1) hK
    positivity
  have hpart3 : 0 ≤ binLt K (1 / 4) J := by
    unfold binLt
    refine Finset.sum_nonneg fun i hi => ?_
    unfold binPmf
    have hchoose : 0 ≤ (Nat.choose K i : ℝ) := Nat.cast_nonneg _
    have hp : 0 ≤ (1 / 4 : ℝ) := by norm_num
    have h1mp : 0 ≤ (1 - (1 / 4 : ℝ)) := by norm_num
    positivity
  positivity

theorem capShift_nonneg (cap : ℕ) (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (k : ℕ) : 0 ≤ capShift cap A k := by
  unfold capShift
  split_ifs with h1 h2 h3
  · exact le_refl 0
  · apply hA
  · apply add_nonneg
    · apply hA
    · apply hA
  · exact le_refl 0

theorem stageLaw_nonneg (cap : ℕ) (pc pg pn : ℝ) (R : ℕ → ℝ) (Rmax : ℕ)
    (next : ℕ → ℕ → ℝ) (hpc : 0 ≤ pc) (hpg : 0 ≤ pg) (hpn : 0 ≤ pn) (hR : ∀ r, 0 ≤ R r)
    (hnext : ∀ y k, 0 ≤ next y k) (y k : ℕ) : 0 ≤ stageLaw cap pc pg pn R Rmax next y k := by
  induction y generalizing k with
  | zero =>
    unfold stageLaw
    split
    · norm_num
    · norm_num
  | succ y IH =>
    unfold stageLaw
    have hcapShift : 0 ≤ capShift cap (stageLaw cap pc pg pn R Rmax next y) k := by
      unfold capShift
      split
      · norm_num
      · rename_i hk0
        split
        · rename_i hklt
          apply IH
        · rename_i hkge
          split
          · rename_i hkeq
            have h1 : 0 ≤ stageLaw cap pc pg pn R Rmax next y (cap - 1) := IH (cap - 1)
            have h2 : 0 ≤ stageLaw cap pc pg pn R Rmax next y cap := IH cap
            nlinarith
          · rename_i hkne
            norm_num
    have hsum : 0 ≤ ∑ r ∈ Finset.range (Rmax + 1), R r * next (y + r) k := by
      refine Finset.sum_nonneg (fun r hr => ?_)
      have hRr : 0 ≤ R r := hR r
      have hnext' : 0 ≤ next (y + r) k := hnext (y + r) k
      nlinarith
    have h1 : 0 ≤ pc * capShift cap (stageLaw cap pc pg pn R Rmax next y) k := mul_nonneg hpc hcapShift
    have h2 : 0 ≤ pg * stageLaw cap pc pg pn R Rmax next y k := mul_nonneg hpg (IH k)
    have h3 : 0 ≤ pn * ∑ r ∈ Finset.range (Rmax + 1), R r * next (y + r) k := mul_nonneg hpn hsum
    nlinarith

theorem plR_nonneg (F1 : ℕ → ℝ) (GM : ℕ) (hmono : ∀ g < GM, F1 g ≤ F1 (g + 1))
    (h01 : ∀ g ≤ GM, 0 ≤ F1 g ∧ F1 g ≤ 1) (r : ℕ) : 0 ≤ plR F1 GM r := by
  unfold plR
  by_cases h0 : r = 0
  · subst r; simp [Ftil]; exact (h01 0 (by omega)).1
  · by_cases hrgm1 : r ≤ GM + 1
    · by_cases hrg : r ≤ GM
      · -- r ≤ GM, r ≠ 0: plR = F1 r - F1 (r - 1)
        have hprev_lt_gm : r - 1 < GM := by omega
        have hmono' := hmono (r - 1) hprev_lt_gm
        have h_eq : (r - 1 : ℕ) + 1 = r := by omega
        have hmono'' : F1 (r - 1) ≤ F1 r := by simpa [h_eq] using hmono'
        have h_sub_le_gm : r - 1 ≤ GM := by omega
        simp [Ftil, h0, hrgm1, hrg, h_sub_le_gm]
        linarith
      · -- r = GM + 1: plR = 1 - F1 GM
        have h_eq : r = GM + 1 := by omega
        subst r
        rcases h01 GM (le_refl GM) with ⟨_, hle⟩
        have h_not_le : ¬ (GM + 1 ≤ GM) := by omega
        have h_sub : GM + 1 - 1 = GM := by omega
        simp [Ftil, h_not_le, h_sub]
        linarith
    · -- r > GM + 1: plR = 0
      simp [h0, hrgm1]

theorem lterm_bound (Δ' Δ μ δ PB P0 : ℝ)
    (h17 : ∀ P, P0 ≤ P → Δ' ≤ Δ * (1 - P) + μ * P) (hP0 : P0 ≤ PB) (hP01 : P0 ≤ 1)
    (hΔ : Δ ≤ δ * μ) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hμ : 0 ≤ μ) :
    Δ' ≤ (δ * (1 - PB) + PB) * μ := by
  by_cases hPB : PB ≤ 1
  · have hPB' := h17 PB hP0
    have h_nonneg : 0 ≤ 1 - PB := by linarith
    nlinarith
  · have h1 := h17 1 hP01
    have hPB_gt : 1 ≤ PB := by linarith
    have h_ineq : 1 ≤ δ * (1 - PB) + PB := by
      have : δ * (1 - PB) + PB = δ + PB * (1 - δ) := by ring
      rw [this]
      have h_nonneg' : 0 ≤ 1 - δ := by linarith
      nlinarith
    nlinarith

theorem inf'_div (n : ℕ) (f : ℕ → ℝ) (c : ℝ) (hc : 0 < c) :
    (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one (fun k => f k / c) =
      (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one f / c := by
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  apply le_antisymm
  · -- m' ≤ m / c
    have h_mul : (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one (fun k => f k / c) * c ≤
      (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one f := by
      apply Finset.le_inf' Finset.nonempty_range_add_one f
      intro b hb
      have hb' : (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one (fun k => f k / c) ≤ f b / c :=
        Finset.inf'_le (fun k => f k / c) hb
      exact (le_div_iff₀ hc).mp hb'
    exact (le_div_iff₀ hc).mpr h_mul
  · -- m / c ≤ m'
    apply Finset.le_inf' Finset.nonempty_range_add_one (fun k => f k / c)
    intro b hb
    have hb' : (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one f ≤ f b :=
      Finset.inf'_le f hb
    exact div_le_div_of_nonneg_right hb' hc_nonneg

theorem lemma12B_mono (d d' mu mu' : ℝ) (v : ℕ) (hd0 : 0 ≤ d) (hdd : d ≤ d')
    (hmu0 : 0 < mu) (hmu : mu ≤ mu') :
    min 1 (lemma12B (d * mu') mu' v) ≤ min 1 (lemma12B (d' * mu) mu v) := by
  set c := (v : ℝ) + 1 with hc
  have hcpos : 0 < c := by
    rw [hc]
    have h0 : 0 ≤ (v : ℝ) := Nat.cast_nonneg _
    linarith
  by_cases hcmu : c < mu
  · have hcmu' : c < mu' := by linarith
    have hden_pos : 0 < mu - c := by linarith
    have hden_pos' : 0 < mu' - c := by linarith
    have hfrac : (d * mu' + Real.sqrt mu' / 2) / (mu' - c) ≤ (d' * mu + Real.sqrt mu / 2) / (mu - c) := by
      rw [add_div, add_div]
      apply add_le_add
      · rw [div_le_div_iff₀ hden_pos' hden_pos]
        have h1 : d * mu' * (mu - c) ≤ d * mu * (mu' - c) := by
          have : d * (mu' * (mu - c)) ≤ d * (mu * (mu' - c)) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hd0
          nlinarith
        have h_mul : d * mu ≤ d' * mu := mul_le_mul_of_nonneg_right hdd hmu0.le
        have h2 : d * mu * (mu' - c) ≤ d' * mu * (mu' - c) :=
          mul_le_mul_of_nonneg_right h_mul hden_pos'.le
        linarith
      · set s := Real.sqrt mu with hs_def
        set s' := Real.sqrt mu' with hs'_def
        have hsq_mu : s ^ 2 = mu := Real.sq_sqrt hmu0.le
        have hsq_mu' : s' ^ 2 = mu' := Real.sq_sqrt (by linarith : 0 ≤ mu')
        have hs_le_s' : s ≤ s' := Real.sqrt_le_sqrt hmu
        have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
        have hs'_nonneg : 0 ≤ s' := Real.sqrt_nonneg _
        field_simp [hden_pos.ne.symm, hden_pos'.ne.symm]
        rw [← hsq_mu, ← hsq_mu']
        have h_nonneg_prod : 0 ≤ (s' - s) * (c + s * s') :=
          mul_nonneg (by linarith) (by nlinarith)
        nlinarith
    have hgoal : lemma12B (d * mu') mu' v ≤ lemma12B (d' * mu) mu v := by
      unfold lemma12B
      rw [← hc]
      simp [hcmu, hcmu']
      exact hfrac
    exact min_le_min_left _ hgoal
  · have hmu_c : mu ≤ c := by linarith
    have h_not : ¬ ((v : ℝ) + 1 < mu) := by linarith
    have hRHS : lemma12B (d' * mu) mu v = 1 := by
      unfold lemma12B
      simp [h_not]
    rw [hRHS]
    rw [min_self]
    exact min_le_left _ _

theorem lemma12'B_mono (d d' mu mu' t : ℝ) (v : ℕ) (hd0 : 0 ≤ d) (hdd : d ≤ d')
    (hmu0 : 0 < mu) (hmu : mu ≤ mu') (_ht0 : 0 < t) (ht1 : t < 1) :
    min 1 (lemma12'B (d * mu') mu' t v) ≤ min 1 (lemma12'B (d' * mu) mu t v) := by
  let a := 1 - t
  have ha_pos : 0 < a := sub_pos.mpr ht1
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have h_nonneg_v : 0 ≤ (v : ℝ) := Nat.cast_nonneg v
  by_cases h : (v : ℝ) < a * mu
  · -- case h: (v : ℝ) < a * mu
    have h_v_lt_mu' : (v : ℝ) < a * mu' := by
      calc
        (v : ℝ) < a * mu := h
        _ ≤ a * mu' := mul_le_mul_of_nonneg_left hmu ha_nonneg
    have h_left : lemma12'B (d * mu') mu' t v = d * mu' / (a * mu' - (v : ℝ)) + Real.exp (-(t ^ 2 * mu' / 2)) := by
      unfold lemma12'B
      dsimp [a]
      split_ifs with hcond
      · rfl
      · exfalso; exact hcond h_v_lt_mu'
    have h_right : lemma12'B (d' * mu) mu t v = d' * mu / (a * mu - (v : ℝ)) + Real.exp (-(t ^ 2 * mu / 2)) := by
      unfold lemma12'B
      dsimp [a]
      split_ifs with hcond
      · rfl
      · exfalso; exact hcond h
    have h_denom_pos : 0 < a * mu' - (v : ℝ) := sub_pos.mpr h_v_lt_mu'
    have h_denom_pos2 : 0 < a * mu - (v : ℝ) := sub_pos.mpr h
    have h_exp : Real.exp (-(t ^ 2 * mu' / 2)) ≤ Real.exp (-(t ^ 2 * mu / 2)) := by
      refine Real.exp_le_exp.mpr ?_
      have ht_sq_nonneg : 0 ≤ t ^ 2 := pow_two_nonneg t
      nlinarith
    have h_div1 : d * mu' / (a * mu' - (v : ℝ)) ≤ d * mu / (a * mu - (v : ℝ)) := by
      have h_cross : d * mu' * (a * mu - (v : ℝ)) ≤ d * mu * (a * mu' - (v : ℝ)) := by
        have h_mu_v : d * mu * (v : ℝ) ≤ d * mu' * (v : ℝ) := by
          have h_mu_v' : mu * (v : ℝ) ≤ mu' * (v : ℝ) := mul_le_mul_of_nonneg_right hmu h_nonneg_v
          nlinarith
        nlinarith
      exact (div_le_div_iff₀ h_denom_pos h_denom_pos2).mpr h_cross
    have h_div2 : d * mu / (a * mu - (v : ℝ)) ≤ d' * mu / (a * mu - (v : ℝ)) := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      nlinarith
    have h_sum : d * mu' / (a * mu' - (v : ℝ)) + Real.exp (-(t ^ 2 * mu' / 2)) ≤ d' * mu / (a * mu - (v : ℝ)) + Real.exp (-(t ^ 2 * mu / 2)) := by
      nlinarith
    have h_min : min 1 (d * mu' / (a * mu' - (v : ℝ)) + Real.exp (-(t ^ 2 * mu' / 2))) ≤ min 1 (d' * mu / (a * mu - (v : ℝ)) + Real.exp (-(t ^ 2 * mu / 2))) :=
      min_le_min_left 1 h_sum
    simpa [h_left, h_right] using h_min
  · -- case ¬ h: ¬ ((v : ℝ) < a * mu)
    have h_not : ¬ ((v : ℝ) < (1 - t) * mu) := by simpa [a] using h
    have h_right : lemma12'B (d' * mu) mu t v = 1 := by
      unfold lemma12'B
      simp [h_not]
    calc
      min 1 (lemma12'B (d * mu') mu' t v) ≤ 1 := min_le_left _ _
      _ = min 1 1 := by simp
      _ = min 1 (lemma12'B (d' * mu) mu t v) := by simp [h_right]

theorem L12_mono (d d' mu mu' : ℝ) (v : ℕ) (hd0 : 0 ≤ d) (hdd : d ≤ d') (hmu0 : 0 < mu)
    (hmu : mu ≤ mu') : L12 (d * mu') mu' v ≤ L12 (d' * mu) mu v := by
  unfold L12
  set F' := (Finset.Icc (1 : ℕ) 199).fold min 1 fun i : ℕ =>
    lemma12'B (d * mu') mu' ((i : ℝ) / 200) v
  have hF'1 : F' ≤ 1 := by
    rw [Finset.fold_min_le]; exact Or.inl le_rfl
  have hF'i : ∀ i ∈ Finset.Icc (1 : ℕ) 199,
      F' ≤ lemma12'B (d * mu') mu' ((i : ℝ) / 200) v := by
    intro i hi; rw [Finset.fold_min_le]; exact Or.inr ⟨i, hi, le_rfl⟩
  refine le_min ?_ ?_
  · calc min (lemma12B (d * mu') mu' v) F' ≤ min 1 (lemma12B (d * mu') mu' v) :=
          le_min (le_trans (min_le_right _ _) hF'1) (min_le_left _ _)
      _ ≤ min 1 (lemma12B (d' * mu) mu v) := lemma12B_mono d d' mu mu' v hd0 hdd hmu0 hmu
      _ ≤ lemma12B (d' * mu) mu v := min_le_right _ _
  · rw [Finset.le_fold_min]
    refine ⟨le_trans (min_le_right _ _) hF'1, fun i hi => ?_⟩
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have hi2' : (i : ℝ) ≤ 199 := by exact_mod_cast hi2
    have ht0 : (0 : ℝ) < (i : ℝ) / 200 := by positivity
    have ht1 : (i : ℝ) / 200 < 1 := by rw [div_lt_one (by norm_num)]; linarith
    calc min (lemma12B (d * mu') mu' v) F'
        ≤ min 1 (lemma12'B (d * mu') mu' ((i : ℝ) / 200) v) :=
          le_min (le_trans (min_le_right _ _) hF'1) (le_trans (min_le_right _ _) (hF'i i hi))
      _ ≤ min 1 (lemma12'B (d' * mu) mu ((i : ℝ) / 200) v) :=
          lemma12'B_mono d d' mu mu' _ v hd0 hdd hmu0 hmu ht0 ht1
      _ ≤ lemma12'B (d' * mu) mu ((i : ℝ) / 200) v := min_le_right _ _

theorem PB_nonneg (P : StParams) (S : State) (_hP : P.OK) (hW : S.WF P) (j J : ℕ)
    (hJ : J ≤ P.E) : 0 ≤ PB P S j J := by
  have h0 : ∀ k ≤ P.E, ∀ g ≤ P.GM, 0 ≤ S.F k g := fun k hk g hg => (hW.1 k hk g hg).1
  have hmono : ∀ k ≤ P.E, ∀ g < P.GM, S.F k g ≤ S.F k (g + 1) := hW.2.1
  refine Finset.le_inf' (grid_nonempty P.GM (j + 1)) (fun K => boundB S.F P.E P.GM (j + 1) J K) ?_
  intro K hK
  have hKmem := mem_grid P.GM (j + 1) K hK
  have hKsub : K - (j + 1) - 1 ≤ P.GM := hKmem.2
  exact boundB_nonneg S.F P.E P.GM (j + 1) J K h0 hmono hJ hKsub

theorem lawS2_nonneg (GM E : ℕ) (F1 : ℕ → ℝ) (hmono : ∀ g < GM, F1 g ≤ F1 (g + 1))
    (h01 : ∀ g ≤ GM, 0 ≤ F1 g ∧ F1 g ≤ 1) (q k : ℕ) : 0 ≤ lawS2 GM E F1 q k := by
  have hR : ∀ r, 0 ≤ plR F1 GM r := plR_nonneg F1 GM hmono h01
  have h_s2 : ∀ y k, 0 ≤ (stageLaw E (3/10 : ℝ) (7/10 : ℝ) 0 (plR F1 GM) (GM + 1) (fun _ _ => 0)) y k :=
    stageLaw_nonneg E (3/10 : ℝ) (7/10 : ℝ) 0 (plR F1 GM) (GM + 1) (fun _ _ => 0)
      (by norm_num) (by norm_num) (by norm_num) hR (by intro y k; exact le_refl 0)
  have h_s1 : ∀ y k, 0 ≤ (stageLaw E (3/11 : ℝ) (5/11 : ℝ) (3/11 : ℝ) (plR F1 GM) (GM + 1)
      (stageLaw E (3/10 : ℝ) (7/10 : ℝ) 0 (plR F1 GM) (GM + 1) (fun _ _ => 0))) y k :=
    stageLaw_nonneg E (3/11 : ℝ) (5/11 : ℝ) (3/11 : ℝ) (plR F1 GM) (GM + 1)
      (stageLaw E (3/10 : ℝ) (7/10 : ℝ) 0 (plR F1 GM) (GM + 1) (fun _ _ => 0))
      (by norm_num) (by norm_num) (by norm_num) hR h_s2
  have h_s3 : ∀ y k, 0 ≤ (stageLaw E (1/4 : ℝ) (1/4 : ℝ) (1/2 : ℝ) (plR F1 GM) (GM + 1)
      (stageLaw E (3/11 : ℝ) (5/11 : ℝ) (3/11 : ℝ) (plR F1 GM) (GM + 1)
      (stageLaw E (3/10 : ℝ) (7/10 : ℝ) 0 (plR F1 GM) (GM + 1) (fun _ _ => 0)))) y k :=
    stageLaw_nonneg E (1/4 : ℝ) (1/4 : ℝ) (1/2 : ℝ) (plR F1 GM) (GM + 1)
      (stageLaw E (3/11 : ℝ) (5/11 : ℝ) (3/11 : ℝ) (plR F1 GM) (GM + 1)
      (stageLaw E (3/10 : ℝ) (7/10 : ℝ) 0 (plR F1 GM) (GM + 1) (fun _ _ => 0)))
      (by norm_num) (by norm_num) (by norm_num) hR h_s1
  unfold lawS2
  simpa using h_s3 q k

theorem Dt_nonneg (S : State) (a b j k : ℕ) (hδ : ∀ k' ≤ k, 0 ≤ S.delta k') : 0 ≤ Dt S a b j k := by
  unfold Dt
  apply Finset.le_inf' Finset.nonempty_range_add_one
  intro k' hk'
  have hk'_le_k : k' ≤ k := Nat.le_of_lt_succ (Finset.mem_range.1 hk')
  have hdelta : 0 ≤ S.delta k' := hδ k' hk'_le_k
  have hratio : 0 ≤ ratio a b k' j := by
    unfold ratio
    have h1 : 0 ≤ mu a k' / mu (a + 1) j := by
      have hnum : 0 ≤ mu a k' := by unfold mu; positivity
      have hden : 0 ≤ mu (a + 1) j := by unfold mu; positivity
      exact div_nonneg hnum hden
    have h2 : 0 ≤ mu b k' / mu (b + 1) j := by
      have hnum : 0 ≤ mu b k' := by unfold mu; positivity
      have hden : 0 ≤ mu (b + 1) j := by unfold mu; positivity
      exact div_nonneg hnum hden
    exact h1.trans (le_max_left _ _)
  exact mul_nonneg hdelta hratio

theorem Dt_mono (S : State) (a b m j k : ℕ) (hδ : ∀ k' ≤ k, 0 ≤ S.delta k') (ham : a ≤ m)
    (hmb : m ≤ b) : Dt S m m j k ≤ Dt S a b j k := by
  unfold Dt
  let s := Finset.range (k + 1)
  have hne : s.Nonempty := Finset.nonempty_range_add_one
  apply Finset.le_inf' hne
  intro k' hk'
  have hk'_le_k : k' ≤ k := Nat.le_of_lt_succ (Finset.mem_range.1 hk')
  have hδk' : 0 ≤ S.delta k' := hδ k' hk'_le_k
  have hratio : ratio m m k' j ≤ ratio a b k' j := ratio_mono a b m k' j ham hmb
  have hterm : S.delta k' * ratio m m k' j ≤ S.delta k' * ratio a b k' j :=
    mul_le_mul_of_nonneg_left hratio hδk'
  exact le_trans (Finset.inf'_le (fun x => S.delta x * ratio m m x j) hk') hterm

theorem dTerms_nonneg (P : StParams) (S : State) (hP : P.OK) (hW : S.WF P) (a b j : ℕ) :
    0 ≤ dTerms P S a b j := by
  unfold dTerms
  apply le_min
  · rw [Finset.le_fold_min]
    constructor
    · exact ratio_nonneg a b 0 j
    · intro J hJ
      rcases Finset.mem_Icc.mp hJ with ⟨hJ1, hJ2⟩
      have hJE : J ≤ P.E := le_trans hJ2 hP.2.1
      rcases hW.2.2.1 J hJE with ⟨hdeltaJ_nonneg, hdeltaJ_le_one⟩
      have hPB : 0 ≤ PB P S j J := PB_nonneg P S hP hW j J hJE
      have hratio : 0 ≤ ratio a b J j := ratio_nonneg a b J j
      have h_nonneg : 0 ≤ S.delta J * (1 - PB P S j J) + PB P S j J := by
        have h_eq : S.delta J * (1 - PB P S j J) + PB P S j J =
            S.delta J + PB P S j J * (1 - S.delta J) := by ring
        rw [h_eq]
        have h2 : 0 ≤ PB P S j J * (1 - S.delta J) :=
          mul_nonneg hPB (by nlinarith)
        nlinarith
      exact mul_nonneg h_nonneg hratio
  · apply Finset.sum_nonneg
    intro k hk
    rw [Finset.mem_range] at hk
    have hkE : k ≤ P.E := Nat.le_of_lt_succ hk
    have h1E : 1 ≤ P.E := hP.1
    have hlawS2 : 0 ≤ lawS2 P.GM P.E (S.F 1) (j + 1) k :=
      lawS2_nonneg P.GM P.E (S.F 1) (hW.2.1 1 h1E) (hW.1 1 h1E) (j + 1) k
    have hDt : 0 ≤ Dt S a b j k :=
      Dt_nonneg S a b j k fun k' hk' => (hW.2.2.1 k' (le_trans hk' hkE)).1
    exact mul_nonneg hlawS2 hDt


theorem fold_min_mono {α β : Type} [DecidableEq α] [LinearOrder β] {s : Finset α} {b b' : β} {f g : α → β}
    (hb : b ≤ b') (hf : ∀ x ∈ s, f x ≤ g x) : s.fold min b f ≤ s.fold min b' g := by
  induction' s using Finset.induction_on with a s' has ih
  · simp [hb]
  · rw [Finset.fold_insert has, Finset.fold_insert has]
    have hfa : f a ≤ g a := hf a (Finset.mem_insert_self a s')
    have hf_mem : ∀ x ∈ s', f x ≤ g x := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    exact min_le_min hfa (ih hf_mem)


theorem dTerms_mono (P : StParams) (S : State) (hP : P.OK) (hW : S.WF P) (a b m j : ℕ) (ham : a ≤ m)
    (hmb : m ≤ b) : dTerms P S m m j ≤ dTerms P S a b j := by
  have hE : 1 ≤ P.E := hP.1
  have hJM_le_E : P.JM ≤ P.E := hP.2.1
  have hVM_le_GM : P.VM ≤ P.GM := hP.2.2
  have hF_range : ∀ k ≤ P.E, ∀ g ≤ P.GM, 0 ≤ S.F k g ∧ S.F k g ≤ 1 := hW.1
  have hF_mono : ∀ k ≤ P.E, ∀ g < P.GM, S.F k g ≤ S.F k (g + 1) := hW.2.1
  have hδ_range : ∀ k ≤ P.E, 0 ≤ S.delta k ∧ S.delta k ≤ 1 := hW.2.2.1
  have hF0 : ∀ g ≤ P.GM, S.F 0 g = 1 := hW.2.2.2.1
  have hδ0 : S.delta 0 = 1 := hW.2.2.2.2
  have hδ_nonneg : ∀ k ≤ P.E, 0 ≤ S.delta k := fun k hk => (hδ_range k hk).1
  have hδ_le_one : ∀ k ≤ P.E, S.delta k ≤ 1 := fun k hk => (hδ_range k hk).2
  have hPB_nonneg : ∀ J ≤ P.E, 0 ≤ PB P S j J := by
    intro J hJ
    exact PB_nonneg P S hP hW j J hJ
  have hA : (Finset.Icc 1 P.JM).fold min (ratio m m 0 j) (fun J =>
      (S.delta J * (1 - PB P S j J) + PB P S j J) * ratio m m J j) ≤
    (Finset.Icc 1 P.JM).fold min (ratio a b 0 j) (fun J =>
      (S.delta J * (1 - PB P S j J) + PB P S j J) * ratio a b J j) := by
    apply fold_min_mono
    · -- init: ratio m m 0 j ≤ ratio a b 0 j
      exact ratio_mono a b m 0 j ham hmb
    · -- terms: for each J in Icc 1 P.JM
      intro J hJ
      have hJ_le_E : J ≤ P.E := by
        have hJ_le_JM : J ≤ P.JM := (Finset.mem_Icc.mp hJ).2
        exact Nat.le_trans hJ_le_JM hJM_le_E
      have h_nonneg_c : 0 ≤ (S.delta J * (1 - PB P S j J) + PB P S j J) := by
        have hδJ_nonneg : 0 ≤ S.delta J := hδ_nonneg J hJ_le_E
        have hδJ_le_one : S.delta J ≤ 1 := hδ_le_one J hJ_le_E
        have hPB_nonneg_J : 0 ≤ PB P S j J := hPB_nonneg J hJ_le_E
        nlinarith
      have h_ratio_J : ratio m m J j ≤ ratio a b J j := ratio_mono a b m J j ham hmb
      exact mul_le_mul_of_nonneg_left h_ratio_J h_nonneg_c
  have hB : (∑ k ∈ Finset.range (P.E + 1), lawS2 P.GM P.E (S.F 1) (j + 1) k * Dt S m m j k) ≤
            (∑ k ∈ Finset.range (P.E + 1), lawS2 P.GM P.E (S.F 1) (j + 1) k * Dt S a b j k) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hk_le_E : k ≤ P.E := by
      have : k < P.E + 1 := Finset.mem_range.1 hk
      omega
    have h_lawS2_nonneg : 0 ≤ lawS2 P.GM P.E (S.F 1) (j + 1) k := by
      have hF1_mono : ∀ g < P.GM, S.F 1 g ≤ S.F 1 (g + 1) := fun g hg => hF_mono 1 hE g hg
      have hF1_range : ∀ g ≤ P.GM, 0 ≤ S.F 1 g ∧ S.F 1 g ≤ 1 := fun g hg => hF_range 1 hE g hg
      exact lawS2_nonneg P.GM P.E (S.F 1) hF1_mono hF1_range (j + 1) k
    have h_Dt : Dt S m m j k ≤ Dt S a b j k := by
      have hδ_nonneg' : ∀ k' ≤ k, 0 ≤ S.delta k' := by
        intro k' hk'
        have hk'_le_E : k' ≤ P.E := Nat.le_trans hk' hk_le_E
        exact hδ_nonneg k' hk'_le_E
      exact Dt_mono S a b m j k hδ_nonneg' ham hmb
    exact mul_le_mul_of_nonneg_left h_Dt h_lawS2_nonneg
  unfold dTerms
  exact min_le_min hA hB

theorem deltaNew_nonneg (P : StParams) (S : State) (hP : P.OK) (hW : S.WF P) (a b j : ℕ) :
    0 ≤ deltaNew P S a b j := by
  induction' j using Nat.strong_induction_on with j ih
  match j with
  | 0 => unfold deltaNew; norm_num
  | 1 => unfold deltaNew; exact dTerms_nonneg P S hP hW a b 1
  | j+2 =>
    unfold deltaNew
    have h_dt : 0 ≤ dTerms P S a b (j + 2) := dTerms_nonneg P S hP hW a b (j + 2)
    have h_dn : 0 ≤ deltaNew P S a b (j + 1) := ih (j + 1) (by omega)
    exact le_min h_dt h_dn


theorem deltaNew_mono (P : StParams) (S : State) (hP : P.OK) (hW : S.WF P) (a b m : ℕ) (ham : a ≤ m)
    (hmb : m ≤ b) (j : ℕ) : deltaNew P S m m j ≤ deltaNew P S a b j := by
  induction' j using Nat.strong_induction_on with j ih
  match j with
  | 0 => rfl
  | 1 =>
    simp [deltaNew]
    exact dTerms_mono P S hP hW a b m 1 ham hmb
  | k + 2 =>
    simp [deltaNew]
    constructor
    · exact Or.inl (dTerms_mono P S hP hW a b m (k + 2) ham hmb)
    · exact Or.inr (ih (k + 1) (Nat.lt_succ_self _))

theorem preF_mono (P : StParams) (S : State) (a b m j v : ℕ) (p p' : ℝ)
    (hδ0 : 0 ≤ deltaNew P S m m j) (hδ : deltaNew P S m m j ≤ deltaNew P S a b j) (ham : a ≤ m)
    (hpp : p ≤ p') : preF P S m m j v p ≤ preF P S a b j v p' := by
  unfold preF
  apply min_le_min
  · apply min_le_min
    · exact le_refl _
    · apply L12_mono (deltaNew P S m m j) (deltaNew P S a b j) (mu (a + 1) j) (mu (m + 1) j) v
        hδ0 hδ
      · unfold mu
        positivity
      · unfold mu
        have ha : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ham
        have hnum : ((a + 1 : ℕ) : ℝ) + 1 + (j : ℝ) ≤ ((m + 1 : ℕ) : ℝ) + 1 + (j : ℝ) := by
          push_cast
          linarith
        exact (div_le_div_of_nonneg_right hnum (by norm_num : (0 : ℝ) ≤ 3))
  · apply min_le_min
    · exact le_refl _
    · apply min_le_min
      · exact le_refl _
      · exact hpp

theorem Fnew_mono (P : StParams) (S : State) (hP : P.OK) (hW : S.WF P) (a b m : ℕ) (ham : a ≤ m)
    (hmb : m ≤ b) (j v : ℕ) : Fnew P S m m j v ≤ Fnew P S a b j v := by
  induction' j with k ih generalizing v
  · -- j = 0: both sides are 1
    simp [Fnew]
  · -- j = k + 1
    simp [Fnew]
    -- Let L := Finset.Icc v P.GM
    -- Let initL := preF P S m m (k+1) v (Fnew P S m m k v)
    -- Let fL := fun v' => preF P S m m (k+1) v' (Fnew P S m m k v')
    -- Let initR := preF P S a b (k+1) v (Fnew P S a b k v)
    -- Let fR := fun v' => preF P S a b (k+1) v' (Fnew P S a b k v')
    -- Goal: L.fold min initL fL ≤ L.fold min initR fR
    set L := Finset.Icc v P.GM with hL
    set initL := preF P S m m (k + 1) v (Fnew P S m m k v) with hinitL
    set fL := fun v' => preF P S m m (k + 1) v' (Fnew P S m m k v') with hfL
    set initR := preF P S a b (k + 1) v (Fnew P S a b k v) with hinitR
    set fR := fun v' => preF P S a b (k + 1) v' (Fnew P S a b k v') with hfR
    have hδ0 : 0 ≤ deltaNew P S m m (k + 1) :=
      deltaNew_nonneg P S hP hW m m (k + 1)
    have hδ : deltaNew P S m m (k + 1) ≤ deltaNew P S a b (k + 1) :=
      deltaNew_mono P S hP hW a b m ham hmb (k + 1)
    have h_initL_initR : initL ≤ initR := by
      -- preF_mono: preF P S m m (k+1) v (Fnew P S m m k v) ≤ preF P S a b (k+1) v (Fnew P S a b k v)
      simpa [hinitL, hinitR] using
        preF_mono P S a b m (k + 1) v (Fnew P S m m k v) (Fnew P S a b k v) hδ0 hδ ham (ih v)
    have h_fL_fR : ∀ x, x ∈ L → fL x ≤ fR x := by
      intro x hx
      -- preF_mono at x
      have hpp := ih x
      simpa [hfL, hfR] using
        preF_mono P S a b m (k + 1) x (Fnew P S m m k x) (Fnew P S a b k x) hδ0 hδ ham hpp
    -- Now: L.fold min initL fL ≤ L.fold min initR fR
    -- Use Finset.le_fold_min: c ≤ fold min b f s ↔ c ≤ b ∧ ∀ x ∈ s, c ≤ f x
    -- Here c = L.fold min initL fL, b = initR, f = fR, s = L
    rw [Finset.le_fold_min (L.fold min initL fL)]
    -- Need: L.fold min initL fL ≤ initR ∧ ∀ x ∈ L, L.fold min initL fL ≤ fR x
    constructor
    · -- L.fold min initL fL ≤ initR
      rw [Finset.fold_min_le]
      -- Need: initL ≤ initR ∨ ∃ x ∈ L, fL x ≤ initR
      left
      exact h_initL_initR
    · -- ∀ x ∈ L, L.fold min initL fL ≤ fR x
      intro x hx
      rw [Finset.fold_min_le]
      -- Need: initL ≤ fR x ∨ ∃ y ∈ L, fL y ≤ fR x
      right
      -- Take y = x
      refine ⟨x, hx, ?_⟩
      exact h_fL_fR x hx

theorem deltaExt_nonneg (P0 : StParams) (h : ℕ) (S : State) (hδ : ∀ k ≤ P0.E, 0 ≤ S.delta k) (k : ℕ) :
    0 ≤ deltaExt P0 h S k := by
  induction' k with k ih
  · unfold deltaExt; norm_num
  · unfold deltaExt
    have hpos_mu : ∀ i, 0 < mu h i := by
      intro i
      unfold mu
      have hsum : 0 < (h : ℝ) + 1 + (i : ℝ) := by
        have hh : 0 ≤ (h : ℝ) := Nat.cast_nonneg _
        have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
        nlinarith
      have h3 : 0 < (3 : ℝ) := by norm_num
      exact div_pos hsum h3
    have hdiv : 0 ≤ mu h 0 / mu h (k + 1) :=
      div_nonneg (le_of_lt (hpos_mu 0)) (le_of_lt (hpos_mu (k + 1)))
    have hmin1 : 0 ≤ min (1 : ℝ) (mu h 0 / mu h (k + 1)) :=
      le_min (by norm_num) hdiv
    have hmin2 : 0 ≤ min (deltaExt P0 h S k)
        (if k + 1 ≤ P0.E then S.delta (k + 1) else S.delta P0.E * mu h P0.E / mu h (k + 1)) := by
      apply le_min ih
      split_ifs with hle
      · exact hδ (k + 1) hle
      · have hP0E : 0 ≤ S.delta P0.E := hδ P0.E (le_refl P0.E)
        have hnum : 0 ≤ S.delta P0.E * mu h P0.E :=
          mul_nonneg hP0E (le_of_lt (hpos_mu P0.E))
        exact div_nonneg hnum (le_of_lt (hpos_mu (k + 1)))
    exact le_min hmin1 hmin2

end FrogModel.D3.LaneC
