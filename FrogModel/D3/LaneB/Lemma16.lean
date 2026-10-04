module

public import FrogModel.D3.LaneB.Counts
public import FrogModel.D3.LaneB.ClosureFacts
public import FrogModel.D3.LaneB.Tails

@[expose] public section

/-!
# Pieces of Lemmas 11.2 and 11.3 of the paper (the law of `S_e` and its pseudo-law bound)

The law of `S_e = G_1(e_1) + G_2(e_2) + G_3(e_3)` is a triple convolution, the pseudo-law `plF` of a
cdf bound is nonnegative and telescopes back to the bound, and `convF` is its triple convolution.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- `P(S_e = s)` for `S_e = ∑_c G_c(e_c)`, the three curves i.i.d. of law `Q`. -/
noncomputable def probSeQ (Q : Measure (ℕ → ℕ∞)) (e : Fin 3 → ℕ) (s : ℕ) : ℝ :=
  ((Measure.pi fun _ : Fin 3 => Q) {G | ∑ c : Fin 3, G c (e c) = (s : ℕ∞)}).toReal

/-- The convolution of three mass functions on `ℕ` at `s`. -/
def conv3 (p1 p2 p3 : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ g1 ∈ Finset.range (s + 1), ∑ g2 ∈ Finset.range (s + 1 - g1), p1 g1 * p2 g2 * p3 (s - g1 - g2)

/-- The law of `G_1(e_1) + G_2(e_2) + G_3(e_3)` for three i.i.d. curves is the convolution of the
laws of the coordinates. -/
theorem probSeQ_conv (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (e : Fin 3 → ℕ) (s : ℕ) :
    probSeQ Q e s = ∑ g1 ∈ Finset.range (s + 1), ∑ g2 ∈ Finset.range (s + 1 - g1),
      (Q {G | G (e 0) = (g1 : ℕ∞)}).toReal * (Q {G | G (e 1) = (g2 : ℕ∞)}).toReal *
        (Q {G | G (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)}).toReal := by
  let μ := Measure.pi fun _ : Fin 3 => Q
  have hprob : probSeQ Q e s = (μ {G | ∑ c : Fin 3, G c (e c) = (s : ℕ∞)}).toReal := rfl
  rw [hprob]
  -- For each (g1, g2), define the box A(g1, g2)
  let A (g1 g2 : ℕ) : Set ((Fin 3) → (ℕ → ℕ∞)) :=
    {G | G 0 (e 0) = (g1 : ℕ∞) ∧ G 1 (e 1) = (g2 : ℕ∞) ∧ G 2 (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)}
  -- Measurability of A(g1, g2)
  have hA_measurable (g1 g2 : ℕ) : MeasurableSet (A g1 g2) := by
    unfold A
    have h0 : MeasurableSet {G : (Fin 3) → (ℕ → ℕ∞) | G 0 (e 0) = (g1 : ℕ∞)} := by
      have h_meas : Measurable (fun (G : (Fin 3) → (ℕ → ℕ∞)) => G 0 (e 0)) :=
        Measurable.comp (measurable_pi_apply (e 0)) (measurable_pi_apply 0)
      have h_singleton : MeasurableSet ({(g1 : ℕ∞)} : Set ℕ∞) := MeasurableSet.of_discrete
      exact h_meas h_singleton
    have h1 : MeasurableSet {G : (Fin 3) → (ℕ → ℕ∞) | G 1 (e 1) = (g2 : ℕ∞)} := by
      have h_meas : Measurable (fun (G : (Fin 3) → (ℕ → ℕ∞)) => G 1 (e 1)) :=
        Measurable.comp (measurable_pi_apply (e 1)) (measurable_pi_apply 1)
      have h_singleton : MeasurableSet ({(g2 : ℕ∞)} : Set ℕ∞) := MeasurableSet.of_discrete
      exact h_meas h_singleton
    have h2 : MeasurableSet {G : (Fin 3) → (ℕ → ℕ∞) | G 2 (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)} := by
      have h_meas : Measurable (fun (G : (Fin 3) → (ℕ → ℕ∞)) => G 2 (e 2)) :=
        Measurable.comp (measurable_pi_apply (e 2)) (measurable_pi_apply 2)
      have h_singleton : MeasurableSet ({((s - g1 - g2 : ℕ) : ℕ∞)} : Set ℕ∞) := MeasurableSet.of_discrete
      exact h_meas h_singleton
    exact MeasurableSet.inter h0 (MeasurableSet.inter h1 h2)
  -- Define the index set I = {(g1, g2) | g1 < s+1, g2 < s+1-g1}
  let I : Finset (ℕ × ℕ) := ((Finset.range (s + 1)) ×ˢ (Finset.range (s + 1))).filter
    (fun ⟨g1, g2⟩ => g2 ≤ s - g1)
  -- The A(g1,g2) are pairwise disjoint on I
  have hA_disjoint : (I : Set (ℕ × ℕ)).PairwiseDisjoint (fun (p : ℕ × ℕ) => A p.1 p.2) := by
    intro x hx y hy hne
    rcases x with ⟨g1, g2⟩
    rcases y with ⟨g1', g2'⟩
    -- If (g1, g2) ≠ (g1', g2'), then A(g1,g2) ∩ A(g1',g2') = ∅
    by_cases hg1 : g1 = g1'
    · have hg2 : g2 ≠ g2' := by
        intro h; apply hne; simp [hg1, h]
      apply Set.disjoint_left.mpr
      intro G hG hG'
      rcases hG with ⟨hG0, hG1, hG2⟩
      rcases hG' with ⟨hG0', hG1', hG2'⟩
      apply hg2
      have h_eq : (g2 : ℕ∞) = (g2' : ℕ∞) := by
        calc
          (g2 : ℕ∞) = G 1 (e 1) := by symm; exact hG1
          _ = (g2' : ℕ∞) := hG1'
      exact (ENat.natCast_inj (a := g2) (b := g2')).mp h_eq
    · apply Set.disjoint_left.mpr
      intro G hG hG'
      rcases hG with ⟨hG0, hG1, hG2⟩
      rcases hG' with ⟨hG0', hG1', hG2'⟩
      apply hg1
      have h_eq : (g1 : ℕ∞) = (g1' : ℕ∞) := by
        calc
          (g1 : ℕ∞) = G 0 (e 0) := by symm; exact hG0
          _ = (g1' : ℕ∞) := hG0'
      exact (ENat.natCast_inj (a := g1) (b := g1')).mp h_eq
  -- The union of A over I equals the target set
  have h_union_eq : {G | ∑ c : Fin 3, G c (e c) = (s : ℕ∞)} = ⋃ p ∈ I, A p.1 p.2 := by
    ext G
    constructor
    · intro hG
      have hsum : ∑ c : Fin 3, G c (e c) = (s : ℕ∞) := hG
      rw [Fin.sum_univ_three] at hsum
      -- hsum : G 0 (e 0) + G 1 (e 1) + G 2 (e 2) = (s : ℕ∞)
      -- Since s < ⊤, each term is < ⊤, so each G c (e c) is finite
      have hsum_lt : G 0 (e 0) + G 1 (e 1) + G 2 (e 2) < ⊤ := by
        rw [hsum]
        exact ENat.natCast_lt_top s
      have h_fin_ab : G 0 (e 0) + G 1 (e 1) < ⊤ ∧ G 2 (e 2) < ⊤ := by
        simpa [add_assoc] using (ENat.add_lt_top (a := G 0 (e 0) + G 1 (e 1)) (b := G 2 (e 2))).mp hsum_lt
      have h_fin_a : G 0 (e 0) < ⊤ := by
        have := (ENat.add_lt_top (a := G 0 (e 0)) (b := G 1 (e 1))).mp h_fin_ab.1
        exact this.1
      have h_fin_b : G 1 (e 1) < ⊤ := by
        have := (ENat.add_lt_top (a := G 0 (e 0)) (b := G 1 (e 1))).mp h_fin_ab.1
        exact this.2
      have h_fin_c : G 2 (e 2) < ⊤ := h_fin_ab.2
      -- Since each term is < ⊤, it is of the form (n : ℕ∞) for some n : ℕ
      obtain ⟨n0, hn0⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt h_fin_a)
      obtain ⟨n1, hn1⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt h_fin_b)
      obtain ⟨n2, hn2⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt h_fin_c)
      -- hn0 : (n0 : ℕ∞) = G 0 (e 0), etc.
      -- Now hsum : (n0 : ℕ∞) + (n1 : ℕ∞) + (n2 : ℕ∞) = (s : ℕ∞)
      rw [← hn0, ← hn1, ← hn2] at hsum
      -- So n0 + n1 + n2 = s in ℕ
      have hns : n0 + n1 + n2 = s := by
        have h_eq : (n0 + n1 + n2 : ℕ∞) = (s : ℕ∞) := by
          calc
            (n0 + n1 + n2 : ℕ∞) = ((n0 + n1 + n2 : ℕ) : ℕ∞) := rfl
            _ = (n0 : ℕ∞) + (n1 : ℕ∞) + (n2 : ℕ∞) := by simp
            _ = (s : ℕ∞) := hsum
        exact (ENat.natCast_inj (a := n0 + n1 + n2) (b := s)).mp h_eq
      -- Now we have n0 ≤ s and n1 ≤ s - n0
      have hn0_le_s : n0 ≤ s := by
        omega
      have hn1_le_s : n1 ≤ s := by
        omega
      have hn1_le_s_sub_n0 : n1 ≤ s - n0 := by
        omega
      -- So (n0, n1) ∈ I
      have h_mem : (n0, n1) ∈ I := by
        unfold I
        simp [hn0_le_s, hn1_le_s, hn1_le_s_sub_n0, Finset.mem_range, Finset.mem_product, Finset.mem_filter]
      -- And G ∈ A(n0, n1)
      have hG_A : G ∈ A n0 n1 := by
        unfold A
        refine ⟨hn0.symm, hn1.symm, ?_⟩
        calc
          G 2 (e 2) = (n2 : ℕ∞) := hn2.symm
          _ = ((s - n0 - n1 : ℕ) : ℕ∞) := by
            have h_n2 : n2 = s - n0 - n1 := by omega
            simp [h_n2]
      -- Therefore G is in the union
      refine Set.mem_iUnion₂.mpr ⟨(n0, n1), h_mem, hG_A⟩
    · intro hG
      rcases Set.mem_iUnion₂.mp hG with ⟨p, hp, hGp⟩
      rcases p with ⟨g1, g2⟩
      rcases hGp with ⟨hG0, hG1, hG2⟩
      -- Goal: G ∈ {G | ∑ c : Fin 3, G c (e c) = (s : ℕ∞)}
      -- i.e., ∑ c : Fin 3, G c (e c) = (s : ℕ∞)
      have hsum : ∑ c : Fin 3, G c (e c) = (s : ℕ∞) := by
        rw [Fin.sum_univ_three]
        -- From hp, we know g1 ∈ range (s+1) and g2 ≤ s - g1
        have hp_mem_I : (g1, g2) ∈ I := hp
        unfold I at hp_mem_I
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hp_mem_I
        rcases hp_mem_I with ⟨⟨hg1_le_s, hg2_lt_s1⟩, hg2_le_s_sub_g1⟩
        calc
          G 0 (e 0) + G 1 (e 1) + G 2 (e 2) = (g1 : ℕ∞) + (g2 : ℕ∞) + ((s - g1 - g2 : ℕ) : ℕ∞) := by
            simp [hG0, hG1, hG2]
          _ = ((g1 + g2 + (s - g1 - g2) : ℕ) : ℕ∞) := by
            push_cast
            simp [add_assoc]
          _ = (s : ℕ∞) := by
            have h_eq : g1 + g2 + (s - g1 - g2) = s := by
              have h_le : g1 + g2 ≤ s := by
                have := Nat.add_le_of_le_sub (a := g2) (b := g1) (c := s) hg1_le_s hg2_le_s_sub_g1
                simpa [add_comm] using this
              calc
                g1 + g2 + (s - g1 - g2) = (g1 + g2) + (s - (g1 + g2)) := by
                  rw [show s - g1 - g2 = s - (g1 + g2) from by rw [Nat.sub_add_eq]]
                _ = s := Nat.add_sub_cancel' h_le
            simp [h_eq]
      exact hsum
  -- Now compute the measure using the disjoint union
  have h_measure_union : μ (⋃ p ∈ I, A p.1 p.2) = ∑ p ∈ I, μ (A p.1 p.2) :=
    measure_biUnion_finset hA_disjoint (fun p hp => hA_measurable p.1 p.2)
  rw [h_union_eq, h_measure_union]
  -- Now we need to compute ∑ p ∈ I, (μ (A p.1 p.2)).toReal
  -- First, compute μ (A g1 g2) using pi_pi_finset
  have h_measure_box (g1 g2 : ℕ) : μ (A g1 g2) = Q {G | G (e 0) = (g1 : ℕ∞)} * Q {G | G (e 1) = (g2 : ℕ∞)} * Q {G | G (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)} := by
    -- A(g1, g2) = (Set.univ : Set (Fin 3)).pi f where f is defined appropriately
    let f : Fin 3 → Set (ℕ → ℕ∞) := fun i =>
      match i with
      | 0 => {G | G (e 0) = (g1 : ℕ∞)}
      | 1 => {G | G (e 1) = (g2 : ℕ∞)}
      | 2 => {G | G (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)}
    have hA_eq : A g1 g2 = ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).pi f := by
      ext G
      unfold A f
      simp only [Set.mem_pi, Set.mem_ofPred_eq]
      refine ⟨fun ⟨h0, h1, h2⟩ i hi => ?_, fun h => ?_⟩
      · fin_cases i <;> simp [h0, h1, h2]
      · have h0' := h 0 (by simp)
        have h1' := h 1 (by simp)
        have h2' := h 2 (by simp)
        -- h0' : G 0 ∈ f 0, etc.
        -- f 0 = {G | G (e 0) = (g1 : ℕ∞)}, so h0' gives G 0 (e 0) = (g1 : ℕ∞)
        have h0'' : G 0 (e 0) = (g1 : ℕ∞) := by simpa [f] using h0'
        have h1'' : G 1 (e 1) = (g2 : ℕ∞) := by simpa [f] using h1'
        have h2'' : G 2 (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞) := by simpa [f] using h2'
        exact ⟨h0'', h1'', h2''⟩
    rw [hA_eq]
    -- Now use pi_pi_finset
    rw [MeasureTheory.Measure.pi_pi_finset (fun _ : Fin 3 => Q) f Finset.univ]
    rw [Fin.prod_univ_three]
  -- Now rewrite the sum
  have h_term (g1 g2 : ℕ) : (μ (A g1 g2)).toReal =
      (Q {G | G (e 0) = (g1 : ℕ∞)}).toReal * (Q {G | G (e 1) = (g2 : ℕ∞)}).toReal *
        (Q {G | G (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)}).toReal := by
    rw [h_measure_box g1 g2]
    simp [ENNReal.toReal_mul]
  have h_sum_eq : (∑ p ∈ I, (μ (A p.1 p.2)).toReal) =
      ∑ g1 ∈ Finset.range (s + 1), ∑ g2 ∈ Finset.range (s + 1 - g1),
        (Q {G | G (e 0) = (g1 : ℕ∞)}).toReal * (Q {G | G (e 1) = (g2 : ℕ∞)}).toReal *
          (Q {G | G (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)}).toReal := by
    calc
      (∑ p ∈ I, (μ (A p.1 p.2)).toReal) = (∑ p ∈ I,
        (Q {G | G (e 0) = (p.1 : ℕ∞)}).toReal * (Q {G | G (e 1) = (p.2 : ℕ∞)}).toReal *
          (Q {G | G (e 2) = ((s - p.1 - p.2 : ℕ) : ℕ∞)}).toReal) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [h_term p.1 p.2]
      _ = ∑ g1 ∈ Finset.range (s + 1), ∑ g2 ∈ Finset.range (s + 1 - g1),
        (Q {G | G (e 0) = (g1 : ℕ∞)}).toReal * (Q {G | G (e 1) = (g2 : ℕ∞)}).toReal *
          (Q {G | G (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)}).toReal := by
        -- Now relate the sum over I to the double sum
        unfold I
        calc
          (∑ p ∈ ((Finset.range (s + 1) ×ˢ Finset.range (s + 1)).filter (fun ⟨g1, g2⟩ => g2 ≤ s - g1)),
            (Q {G | G (e 0) = (p.1 : ℕ∞)}).toReal * (Q {G | G (e 1) = (p.2 : ℕ∞)}).toReal *
              (Q {G | G (e 2) = ((s - p.1 - p.2 : ℕ) : ℕ∞)}).toReal) =
            (∑ p ∈ Finset.range (s + 1) ×ˢ Finset.range (s + 1),
              if p.2 ≤ s - p.1 then
                (Q {G | G (e 0) = (p.1 : ℕ∞)}).toReal * (Q {G | G (e 1) = (p.2 : ℕ∞)}).toReal *
                  (Q {G | G (e 2) = ((s - p.1 - p.2 : ℕ) : ℕ∞)}).toReal else 0) := by
            rw [Finset.sum_filter]
          _ = ∑ g1 ∈ Finset.range (s + 1), ∑ g2 ∈ Finset.range (s + 1),
              (if g2 ≤ s - g1 then
                (Q {G | G (e 0) = (g1 : ℕ∞)}).toReal * (Q {G | G (e 1) = (g2 : ℕ∞)}).toReal *
                  (Q {G | G (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)}).toReal else 0) := by
            rw [Finset.sum_product]
          _ = ∑ g1 ∈ Finset.range (s + 1), ∑ g2 ∈ Finset.range (s + 1 - g1),
            (Q {G | G (e 0) = (g1 : ℕ∞)}).toReal * (Q {G | G (e 1) = (g2 : ℕ∞)}).toReal *
              (Q {G | G (e 2) = ((s - g1 - g2 : ℕ) : ℕ∞)}).toReal := by
            refine Finset.sum_congr rfl (fun g1 hg1 => ?_)
            have hg1_le_s : g1 ≤ s := by
              simpa [Finset.mem_range] using hg1
            rw [← Finset.sum_filter]
            congr
            ext g2
            simp [Finset.mem_range]
            omega
  have h_toReal_sum : (∑ p ∈ I, μ (A p.1 p.2)).toReal = ∑ p ∈ I, (μ (A p.1 p.2)).toReal :=
    ENNReal.toReal_sum (fun p hp => by
      rw [h_measure_box p.1 p.2]
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact (measure_lt_top Q _).ne
        · exact (measure_lt_top Q _).ne
      · exact (measure_lt_top Q _).ne)
  rw [h_toReal_sum, h_sum_eq]

/-- The pseudo-law of a nonnegative nondecreasing cdf bound is nonnegative. -/
theorem plF_nonneg (F : ℕ → ℕ → ℝ) (GM e : ℕ) (h0 : 0 ≤ F e 0)
    (hmono : ∀ g < GM, F e g ≤ F e (g + 1)) (g : ℕ) : 0 ≤ plF F GM e g := by
  unfold plF
  split
  · case isTrue hle =>
    split
    · case isTrue heq =>
      rw [heq, sub_zero]
      exact h0
    · case isFalse hne =>
      have hpos : 0 < g := Nat.pos_of_ne_zero hne
      have hlt : g - 1 < GM := by
        have : g - 1 < g := Nat.sub_lt hpos (by decide)
        exact lt_of_lt_of_le this hle
      have hmono' := hmono (g - 1) hlt
      have h_eq : (g - 1 : ℕ) + 1 = g := by omega
      rw [h_eq] at hmono'
      linarith
  · case isFalse hnotle =>
    linarith

/-- The pseudo-law `plF` telescopes back to `F` on `0..GM`. -/
theorem sum_plF (F : ℕ → ℕ → ℝ) (GM e u : ℕ) (hu : u ≤ GM) :
    ∑ g ∈ Finset.range (u + 1), plF F GM e g = F e u := by
  revert hu
  induction' u with k ih
  · intro hu
    simp [plF]
  · intro hu
    have hk_le_GM : k ≤ GM := Nat.le_trans (Nat.le_succ k) hu
    rw [Finset.sum_range_succ]
    rw [ih hk_le_GM]
    have h_plF : plF F GM e k.succ = F e k.succ - F e k := by
      rw [plF]
      simp [hu]
    rw [h_plF]
    ring

/-- `convF` is the convolution of the three pseudo-laws. -/
theorem convF_eq (F : ℕ → ℕ → ℝ) (GM : ℕ) (e : Fin 3 → ℕ) (s : ℕ) :
    convF F GM e s = conv3 (plF F GM (e 0)) (plF F GM (e 1)) (plF F GM (e 2)) s := by
  set p1 := plF F GM (e 0) with hp1
  set p2 := plF F GM (e 1) with hp2
  set p3 := plF F GM (e 2) with hp3
  have hplF_zero : ∀ (e : ℕ) (g : ℕ), GM < g → plF F GM e g = 0 := by
    intro e g hg
    unfold plF
    simp [not_le.mpr hg]
  set N := max s GM with hN
  have hN_ge_GM : GM ≤ N := le_max_right _ _
  have hN_ge_s : s ≤ N := le_max_left _ _
  -- convF equals the double sum over range (N+1) × range (N+1) with filter
  have hconvF : convF F GM e s = ∑ g1 ∈ Finset.range (N + 1), ∑ g2 ∈ Finset.range (N + 1),
      if g1 + g2 ≤ s then p1 g1 * p2 g2 * p3 (s - g1 - g2) else 0 := by
    unfold convF
    -- First extend the inner sum for each g1 in range (GM+1)
    have h_inner_extend (g1 : ℕ) (hg1 : g1 ∈ Finset.range (GM + 1)) :
        (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 ≤ s then p1 g1 * p2 g2 * p3 (s - g1 - g2) else 0) =
        (∑ g2 ∈ Finset.range (N + 1), if g1 + g2 ≤ s then p1 g1 * p2 g2 * p3 (s - g1 - g2) else 0) := by
      rw [Finset.mem_range] at hg1
      have h_sub : Finset.range (GM + 1) ⊆ Finset.range (N + 1) := by
        intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      rw [Finset.sum_subset h_sub ?_]
      intro x hx hx'
      rw [Finset.mem_range] at hx hx'
      have hx_gt_GM : GM < x := by omega
      have hp2_zero : p2 x = 0 := hplF_zero (e 1) x hx_gt_GM
      simp [hp2_zero]
    -- Rewrite the outer sum: replace inner sums for g1 in range (GM+1), then extend to range (N+1)
    rw [Finset.sum_congr rfl (fun g1 hg1 => h_inner_extend g1 hg1)]
    have h_outer_sub : Finset.range (GM + 1) ⊆ Finset.range (N + 1) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    rw [Finset.sum_subset h_outer_sub ?_]
    intro g1 hg1 hg1'
    rw [Finset.mem_range] at hg1 hg1'
    have hp1_zero : p1 g1 = 0 := hplF_zero (e 0) g1 (by omega)
    simp [hp1_zero]
  -- conv3 equals the same double sum
  have hconv3 : conv3 p1 p2 p3 s = ∑ g1 ∈ Finset.range (N + 1), ∑ g2 ∈ Finset.range (N + 1),
      if g1 + g2 ≤ s then p1 g1 * p2 g2 * p3 (s - g1 - g2) else 0 := by
    unfold conv3
    -- First extend the outer sum from range (s+1) to range (N+1)
    have h_outer_sub : Finset.range (s + 1) ⊆ Finset.range (N + 1) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    -- For g1 in range (s+1), rewrite the inner sum
    have h_inner_eq (g1 : ℕ) (hg1 : g1 ∈ Finset.range (s + 1)) :
        (∑ g2 ∈ Finset.range (s + 1 - g1), p1 g1 * p2 g2 * p3 (s - g1 - g2)) =
        (∑ g2 ∈ Finset.range (N + 1), if g1 + g2 ≤ s then p1 g1 * p2 g2 * p3 (s - g1 - g2) else 0) := by
      rw [Finset.mem_range] at hg1
      have hg1_le_s : g1 ≤ s := by omega
      -- Use sum_filter to express RHS as sum over filtered set
      rw [← Finset.sum_filter (fun g2 => g1 + g2 ≤ s) (fun g2 => p1 g1 * p2 g2 * p3 (s - g1 - g2))]
      -- Now we need: filter (λ g2, g1+g2 ≤ s) (range (N+1)) = range (s+1-g1)
      have h_filter_eq : (Finset.range (N + 1)).filter (fun g2 => g1 + g2 ≤ s) = Finset.range (s + 1 - g1) := by
        ext g2
        constructor
        · intro h
          rw [Finset.mem_filter, Finset.mem_range] at h
          rcases h with ⟨h_mem, h_le⟩
          rw [Finset.mem_range]
          omega
        · intro h
          rw [Finset.mem_range] at h
          have h_le : g1 + g2 ≤ s := by omega
          refine Finset.mem_filter.mpr ⟨?_, h_le⟩
          rw [Finset.mem_range]
          omega
      rw [h_filter_eq]
    -- Rewrite outer sum for g1 in range (s+1), then extend
    rw [Finset.sum_congr rfl (fun g1 hg1 => h_inner_eq g1 hg1)]
    rw [Finset.sum_subset h_outer_sub ?_]
    intro g1 hg1 hg1'
    rw [Finset.mem_range] at hg1 hg1'
    -- For g1 > s, every term has g1+g2 > s, so the sum is 0
    refine Finset.sum_eq_zero ?_
    intro g2 hg2
    rw [Finset.mem_range] at hg2
    have h_gt : s < g1 + g2 := by omega
    simp [not_le.mpr h_gt]
  rw [hconvF, hconv3]

/-- The direction counts at time `n` and the child curves are independent: the probability that the
counts are `k` and `S_e = s` is `Mult(n; k) P(S_e = s)`. -/
theorem closMeasure_counts_Se (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (n : ℕ) (k : Fin 4 → ℕ) (hk : ∑ a, k a = n) (e : Fin 3 → ℕ) (s : ℕ) :
    (closMeasure Q {x | (∀ a, dirCount x.2 a n = k a) ∧
        ∑ c : Fin 3, x.1 c (e c) = (s : ℕ∞)}).toReal =
      mult4 n (k 0) (k 1) (k 2) (k 3) * probSeQ Q e s := by
  let A : Set (Fin 3 → ℕ → ℕ∞) := {G | ∑ c : Fin 3, G c (e c) = (s : ℕ∞)}
  let B : Set (ℕ → Fin 4) := {D | ∀ a, dirCount D a n = k a}
  have h_set : {x | (∀ a, dirCount x.2 a n = k a) ∧
      ∑ c : Fin 3, x.1 c (e c) = (s : ℕ∞)} = A ×ˢ B := by
    ext ⟨G, D⟩; simp [A, B, and_comm]
  have : SFinite dirMeasure := by
    unfold dirMeasure; infer_instance
  rw [h_set, closMeasure, Measure.prod_prod, ENNReal.toReal_mul]
  dsimp [A, probSeQ]
  rw [dirMeasure_counts n k hk]
  rw [mul_comm]

/-- The cumulative sum of a triple convolution, as nested cumulative sums. -/
theorem cum_conv3_eq (p1 p2 p3 : ℕ → ℝ) (t : ℕ) :
    ∑ s ∈ Finset.range (t + 1), conv3 p1 p2 p3 s =
      ∑ g1 ∈ Finset.range (t + 1), p1 g1 * ∑ g2 ∈ Finset.range (t + 1 - g1),
        p2 g2 * ∑ g3 ∈ Finset.range (t + 1 - g1 - g2), p3 g3 := by
  -- Flatten both sides using sum_sigma
  have hL : ∑ s ∈ Finset.range (t + 1), conv3 p1 p2 p3 s =
      ∑ x ∈ (Finset.range (t+1)).sigma (λ s =>
        (Finset.range (s+1)).sigma (λ g1 => Finset.range (s+1-g1))),
        p1 x.2.1 * p2 x.2.2 * p3 (x.1 - x.2.1 - x.2.2) := by
    simp [conv3, Finset.sum_sigma]
  have hR : ∑ g1 ∈ Finset.range (t + 1), p1 g1 * ∑ g2 ∈ Finset.range (t + 1 - g1),
        p2 g2 * ∑ g3 ∈ Finset.range (t + 1 - g1 - g2), p3 g3 =
      ∑ x ∈ (Finset.range (t+1)).sigma (λ g1 =>
        (Finset.range (t+1-g1)).sigma (λ g2 => Finset.range (t+1-g1-g2))),
        p1 x.1 * p2 x.2.1 * p3 x.2.2 := by
    simp [Finset.mul_sum, Finset.sum_sigma, mul_assoc]
  rw [hL, hR]

  -- Now prove equality of the two sigma sums using sum_bij
  -- Define the bijection f: LHS → RHS
  let f : (Σ s : ℕ, (Σ g1 : ℕ, ℕ)) → (Σ g1 : ℕ, (Σ g2 : ℕ, ℕ)) :=
    λ x => ⟨x.2.1, ⟨x.2.2, x.1 - x.2.1 - x.2.2⟩⟩

  apply Finset.sum_bij (λ x hx => f x)
  · -- hi: f maps into target set
    intro x hx
    simp [Finset.mem_sigma] at hx ⊢
    rcases hx with ⟨hs_le, hg1_le, hg2_lt⟩
    -- hs_le: x.1 ≤ t, hg1_le: x.2.1 ≤ x.1, hg2_lt: x.2.2 < x.1+1-x.2.1
    have hs_lt_t1 : x.1 < t+1 := Nat.lt_succ_of_le hs_le
    have hg1_lt_t1 : x.2.1 < t+1 := Nat.lt_of_le_of_lt hg1_le hs_lt_t1
    have hg2_le : x.2.2 ≤ x.1 - x.2.1 := by
      omega
    have hg2_lt_t1_sub_g1 : x.2.2 < t+1 - x.2.1 := by
      apply Nat.lt_of_le_of_lt hg2_le
      omega
    have hg1_sub_lt : x.1 - x.2.1 < t+1 - x.2.1 := by
      apply Nat.sub_lt_sub_right hg1_le hs_lt_t1
    have hg3_lt_t1_sub_g1_sub_g2 : (x.1 - x.2.1) - x.2.2 < (t+1 - x.2.1) - x.2.2 := by
      apply Nat.sub_lt_sub_right hg2_le hg1_sub_lt

    have h1 : (f x).1 ≤ t := by
      simpa [f] using Nat.le_of_lt_succ hg1_lt_t1
    have h2 : (f x).2.1 < t+1 - (f x).1 := by
      simpa [f] using hg2_lt_t1_sub_g1
    have h3 : (f x).2.2 < t+1 - (f x).1 - (f x).2.1 := by
      simpa [f] using hg3_lt_t1_sub_g1_sub_g2
    exact ⟨h1, h2, h3⟩
  · -- injectivity
    intro x₁ hx₁ x₂ hx₂ h
    simp [Finset.mem_sigma] at hx₁ hx₂
    rcases hx₁ with ⟨hs₁, hg₁, hg₂⟩
    rcases hx₂ with ⟨hs₂, hg₁', hg₂'⟩
    -- h : f x₁ = f x₂
    -- f x₁ = (x₁.2.1, x₁.2.2, x₁.1 - x₁.2.1 - x₁.2.2)
    -- f x₂ = (x₂.2.1, x₂.2.2, x₂.1 - x₂.2.1 - x₂.2.2)
    -- So x₁.2.1 = x₂.2.1, x₁.2.2 = x₂.2.2, x₁.1 - x₁.2.1 - x₁.2.2 = x₂.1 - x₂.2.1 - x₂.2.2
    have h_eq1 : x₁.2.1 = x₂.2.1 := by
      have := congrArg (λ y : (Σ g1 : ℕ, (Σ g2 : ℕ, ℕ)) => y.1) h
      simpa [f] using this
    have h_eq2 : x₁.2.2 = x₂.2.2 := by
      have := congrArg (λ y : (Σ g1 : ℕ, (Σ g2 : ℕ, ℕ)) => y.2.1) h
      simpa [f] using this
    have h_eq3 : x₁.1 - x₁.2.1 - x₁.2.2 = x₂.1 - x₂.2.1 - x₂.2.2 := by
      have := congrArg (λ y : (Σ g1 : ℕ, (Σ g2 : ℕ, ℕ)) => y.2.2) h
      simpa [f] using this

    -- Now we need x₁ = x₂
    -- Using h_eq1, h_eq2, and h_eq3
    have h_fst_eq : x₁.1 = x₂.1 := by
      -- From h_eq3 and h_eq1, h_eq2
      rw [h_eq1, h_eq2] at h_eq3
      -- Now h_eq3: x₁.1 - x₁.2.1 - x₁.2.2 = x₂.1 - x₁.2.1 - x₁.2.2
      -- So x₁.1 = x₂.1
      omega

    -- Now construct the equality x₁ = x₂
    apply Sigma.ext
    · exact h_fst_eq
    · -- Need HEq x₁.2 x₂.2
      -- Since x₁.2 and x₂.2 are both Σ g1 : ℕ, ℕ, we can use Sigma.ext
      apply heq_of_eq
      apply Sigma.ext h_eq1
      -- Need HEq x₁.2.snd x₂.2.snd
      -- x₁.2.snd = x₁.2.2, x₂.2.snd = x₂.2.2
      -- h_eq2 : x₁.2.2 = x₂.2.2
      -- Use heq_of_eq
      exact heq_of_eq h_eq2
  · -- surjectivity
    intro y hy
    simp [Finset.mem_sigma] at hy
    rcases hy with ⟨hg1_le, hg2_lt, hg3_lt⟩
    -- hg1_le: y.1 ≤ t, hg2_lt: y.2.1 < t+1-y.1, hg3_lt: y.2.2 < t+1-y.1-y.2.1
    have hg1_lt_t1 : y.1 < t+1 := Nat.lt_succ_of_le hg1_le
    have h_sum12_le_t : y.1 + y.2.1 ≤ t := by
      -- from hg2_lt: y.2.1 < t+1 - y.1
      -- this implies y.1 + y.2.1 ≤ t
      have hg2_le' : y.2.1 ≤ t - y.1 := by
        -- from hg2_lt: y.2.1 < t+1 - y.1
        -- and t+1 - y.1 = (t - y.1) + 1 when y.1 ≤ t
        omega
      have := Nat.add_le_add_left hg2_le' y.1
      have h_add_sub : y.1 + (t - y.1) = t := Nat.add_sub_cancel' hg1_le
      rw [h_add_sub] at this
      exact this
    have hg2_le : y.2.1 ≤ t - y.1 := by
      omega
    have hg3_le : y.2.2 ≤ t - y.1 - y.2.1 := by
      -- from hg3_lt: y.2.2 < t+1 - y.1 - y.2.1
      -- Note: t+1 - y.1 - y.2.1 = (t - y.1 - y.2.1) + 1 because y.1 + y.2.1 ≤ t
      omega
    have h_sum_le_t : y.1 + y.2.1 + y.2.2 ≤ t := by
      -- From hg3_le: y.2.2 ≤ t - y.1 - y.2.1
      -- Note: t - y.1 - y.2.1 = t - (y.1 + y.2.1) by Nat.sub_sub
      have h_sub_eq : t - y.1 - y.2.1 = t - (y.1 + y.2.1) := by
        rw [Nat.sub_sub]
      rw [h_sub_eq] at hg3_le
      -- Now hg3_le: y.2.2 ≤ t - (y.1 + y.2.1)
      -- So (y.1 + y.2.1) + y.2.2 ≤ (y.1 + y.2.1) + (t - (y.1 + y.2.1)) = t
      have h_sum123_le_t : (y.1 + y.2.1) + y.2.2 ≤ t := by
        have := Nat.add_le_add_left hg3_le (y.1 + y.2.1)
        have h_add_sub' : (y.1 + y.2.1) + (t - (y.1 + y.2.1)) = t := Nat.add_sub_cancel' h_sum12_le_t
        rw [h_add_sub'] at this
        exact this
      simpa [add_assoc] using h_sum123_le_t

    -- The preimage is (y.1 + y.2.1 + y.2.2, y.1, y.2.1)
    let x : Σ s : ℕ, (Σ g1 : ℕ, ℕ) := ⟨y.1 + y.2.1 + y.2.2, ⟨y.1, y.2.1⟩⟩

    have hx_mem : x ∈ (Finset.range (t+1)).sigma (λ s =>
        (Finset.range (s+1)).sigma (λ g1 => Finset.range (s+1-g1))) := by
      simp [Finset.mem_sigma, x]
      refine ⟨?_, ?_, ?_⟩
      · -- x.1 < t+1
        omega
      · -- x.2.1 < x.1+1
        omega
      · -- x.2.2 < x.1+1-x.2.1
        omega

    have h_f_x_eq_y : f x = y := by
      -- f x = (x.2.1, x.2.2, x.1 - x.2.1 - x.2.2) = (y.1, y.2.1, (y.1+y.2.1+y.2.2) - y.1 - y.2.1)
      -- Need to show: (y.1 + y.2.1 + y.2.2) - y.1 - y.2.1 = y.2.2
      simp [f, x]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          simp
          omega

    exact ⟨x, hx_mem, h_f_x_eq_y⟩
  · -- summand equality
    intro x hx
    simp [f, mul_assoc]

/-- `∑_{g ≤ u} P(G e = g) = P(G e ≤ u)` for a random curve `G`. -/
theorem sum_measure_eq (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (e u : ℕ) :
    ∑ g ∈ Finset.range (u + 1), (Q {G | G e = (g : ℕ∞)}).toReal =
      (Q {G | G e ≤ (u : ℕ∞)}).toReal := by
  have h_disjoint : (↑(Finset.range (u + 1)) : Set ℕ).PairwiseDisjoint (fun g => {G : ℕ → ℕ∞ | G e = (g : ℕ∞)}) := by
    rw [Set.pairwiseDisjoint_iff]
    intro i hi j hj hne
    rcases hne with ⟨G, hGi, hGj⟩
    have hi_eq : G e = (i : ℕ∞) := by
      simpa using hGi
    have hj_eq : G e = (j : ℕ∞) := by
      simpa using hGj
    have h_eq : (i : ℕ∞) = (j : ℕ∞) := by
      rw [← hi_eq, hj_eq]
    exact_mod_cast h_eq
  have h_meas : ∀ g ∈ Finset.range (u + 1), MeasurableSet {G : ℕ → ℕ∞ | G e = (g : ℕ∞)} := by
    intro g hg
    have h_meas_eval : Measurable fun (f : ℕ → ℕ∞) => f e := measurable_pi_apply e
    have h_meas_singleton : MeasurableSet ({(g : ℕ∞)} : Set ℕ∞) :=
      measurableSet_singleton (g : ℕ∞)
    exact h_meas_eval h_meas_singleton
  have h_union : (⋃ g ∈ Finset.range (u + 1), {G : ℕ → ℕ∞ | G e = (g : ℕ∞)}) = {G : ℕ → ℕ∞ | G e ≤ (u : ℕ∞)} := by
    ext G
    constructor
    · intro h
      rcases Set.mem_iUnion₂.1 h with ⟨g, hg, hG⟩
      have hGe : G e = (g : ℕ∞) := by simpa using hG
      have hg_le_u : g ≤ u := Finset.mem_range_succ_iff.mp hg
      have h_le : (g : ℕ∞) ≤ (u : ℕ∞) := by exact_mod_cast hg_le_u
      simp [hGe, h_le]
    · intro h
      have hGe : G e ≤ (u : ℕ∞) := by simpa using h
      rcases ENat.le_natCast_iff.mp hGe with ⟨m, hm_eq, hm_le⟩
      have hm_mem : m ∈ Finset.range (u + 1) := Finset.mem_range_succ_iff.mpr hm_le
      apply Set.mem_iUnion₂.mpr
      refine ⟨m, hm_mem, ?_⟩
      simp [hm_eq]
  have h_finite : ∀ g ∈ Finset.range (u + 1), Q {G : ℕ → ℕ∞ | G e = (g : ℕ∞)} ≠ ∞ := by
    intro g hg
    exact (measure_lt_top Q _).ne
  calc
    ∑ g ∈ Finset.range (u + 1), (Q {G | G e = (g : ℕ∞)}).toReal
        = (∑ g ∈ Finset.range (u + 1), Q {G | G e = (g : ℕ∞)}).toReal := by
      rw [ENNReal.toReal_sum h_finite]
    _ = (Q (⋃ g ∈ Finset.range (u + 1), {G | G e = (g : ℕ∞)})).toReal := by
      rw [measure_biUnion_finset h_disjoint h_meas]
    _ = (Q {G | G e ≤ (u : ℕ∞)}).toReal := by rw [h_union]

/-- Coercion of a sum from ℕ∞ to ENNReal commutes with the sum. -/
lemma natCast_finsetSum_toENNReal {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ∞) : ((∑ i ∈ s, f i : ℕ∞) : ENNReal) = ∑ i ∈ s, (f i : ENNReal) := by
  induction' s using Finset.induction with i s his ih
  · simp
  · simp [ih, Finset.sum_insert his]

/-- If `closN q G D < (m : ℕ∞)`, then `closN` is a natural number `n` with `q ≤ n` and `closT q G D n ≤ n`. -/
lemma closN_eq_natCast_of_lt_natCast {q m : ℕ} {G : Fin 3 → ℕ → ℕ∞} {D : ℕ → Fin 4}
    (h : closN q G D < (m : ℕ∞)) : ∃ n : ℕ, closN q G D = (n : ℕ∞) ∧ q ≤ n ∧ closT q G D n ≤ n := by
  set N := closN q G D with hN
  have hN_lt : N < (m : ℕ∞) := h
  have hN_ne_top : N ≠ ⊤ := by
    intro hN_top
    rw [hN_top] at hN_lt
    have : (m : ℕ∞) ≤ ⊤ := le_top
    exact not_lt.mpr this hN_lt
  -- The set of n satisfying the condition is nonempty
  have h_exists_cond : ∃ n : ℕ, q ≤ n ∧ closT q G D n ≤ n := by
    by_contra h_empty
    push Not at h_empty
    have hN_top : N = ⊤ := by
      unfold N closN
      have : (⨅ (n : ℕ) (_ : q ≤ n ∧ closT q G D n ≤ n), (n : ℕ∞)) = ⊤ := by
        refine iInf_eq_top.2 ?_
        intro n
        refine iInf_eq_top.2 ?_
        intro h_cond
        exfalso
        rcases h_cond with ⟨hq, hT⟩
        have h_lt := h_empty n hq
        -- h_lt : (n : ℕ∞) < closT q G D n
        -- hT : closT q G D n ≤ (n : ℕ∞)
        exact not_lt.mpr hT h_lt
      exact this
    rw [hN_top] at hN_lt
    have : (m : ℕ∞) ≤ ⊤ := le_top
    exact not_lt.mpr this hN_lt
  let n := Nat.find h_exists_cond
  have hn_cond : q ≤ n ∧ closT q G D n ≤ n := Nat.find_spec h_exists_cond
  have hn_min : ∀ k, k < n → ¬ (q ≤ k ∧ closT q G D k ≤ k) := fun k hk => Nat.find_min h_exists_cond hk
  refine ⟨n, ?_, hn_cond.1, hn_cond.2⟩
  -- Prove N = (n : ℕ∞)
  apply le_antisymm
  · -- N ≤ (n : ℕ∞)
    unfold N closN
    apply iInf_le_of_le n
    apply iInf_le_of_le hn_cond
    rfl
  · -- (n : ℕ∞) ≤ N
    unfold N closN
    apply le_iInf
    intro k
    apply le_iInf
    intro hk_cond
    have h_le_nk : n ≤ k := by
      by_contra h_lt
      have h_not_cond := hn_min k (Nat.lt_of_not_ge h_lt)
      exact h_not_cond hk_cond
    -- Now (n : ℕ∞) ≤ (k : ℕ∞)
    exact mod_cast h_le_nk


/-- The inclusion of the proof of Lemma 11.2 (A) of the paper: `X ≤ v` forces `N ≥ n0` with few ups
among the first `n0` directions, or some child `c` entered `E` times with at most `v` ups by then and
`G_c(E)` small, or an end at `n = q + s < n0` with counts `(q + s - |e|, e)`, `e ∈ [0, E)^3`, and
`S_e = s`. -/
theorem lemma16A_incl (q v n0 E : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4)
    (hG : ∀ c, Monotone (G c)) (hX : closX q G D ≤ v) :
    dirCount D 0 n0 ≤ v ∨
      (∃ c : Fin 3, (∃ n, E ≤ dirCount D c.succ n ∧ dirCount D 0 n ≤ v) ∧
        G c E ≤ ((n0 - q - 1 : ℕ) : ℕ∞)) ∨
      ∃ e : Fin 3 → ℕ, (∀ c, e c < E) ∧ ∃ s : ℕ, q + s < n0 ∧ e 0 + e 1 + e 2 ≤ q + s ∧
        q + s - (e 0 + e 1 + e 2) ≤ v ∧ dirCount D 0 (q + s) = q + s - (e 0 + e 1 + e 2) ∧
        (∀ c : Fin 3, dirCount D c.succ (q + s) = e c) ∧ ∑ c : Fin 3, G c (e c) = (s : ℕ∞) := by
  set N := closN q G D with hN
  set X := closX q G D with hX_def
  have hX_val : X ≤ (v : ℕ∞) := hX
  by_cases h_le : (n0 : ℕ∞) ≤ N
  · -- Case 1: n0 ≤ N
    left
    have h_count := (countAt_facts D 0).2.1 n0 N h_le
    have h_count' : (dirCount D 0 n0 : ℕ∞) ≤ (v : ℕ∞) := by
      calc
        (dirCount D 0 n0 : ℕ∞) ≤ countAt D 0 N := h_count
        _ = X := by rw [hX_def, closX]
        _ ≤ (v : ℕ∞) := hX_val
    exact mod_cast h_count'
  · -- Case 2: N < n0
    push Not at h_le
    have hN_lt_n0 : N < (n0 : ℕ∞) := h_le
    rcases closN_eq_natCast_of_lt_natCast hN_lt_n0 with ⟨n, hN_eq, hq_le_n, hT_le_n⟩
    have hT_closN := closT_closN q G D hG n hN_eq
    rcases hT_closN with ⟨hq_le_n', hT_eq_n⟩
    -- hT_eq_n : closT q G D n = (n : ℕ∞)
    have hX_eq : X = (dirCount D 0 n : ℕ∞) := by
      rw [hX_def, closX, hN_eq]
      exact (countAt_facts D 0).1 n
    have h_dirCount_le_v : (dirCount D 0 n : ℕ∞) ≤ (v : ℕ∞) := by
      rw [← hX_eq]; exact hX_val
    have h_dirCount_le_v_nat : dirCount D 0 n ≤ v := by exact mod_cast h_dirCount_le_v
    -- Get n < n0 from N < n0
    have hn_lt_n0 : n < n0 := by
      have h_n_lt_n0' : (n : ℕ∞) < (n0 : ℕ∞) := by
        rw [← hN_eq]; exact hN_lt_n0
      exact mod_cast h_n_lt_n0'
    by_cases h_exists_c : ∃ c : Fin 3, E ≤ dirCount D c.succ n
    · -- Second disjunct: some child c has E ≤ dirCount D c.succ n
      rcases h_exists_c with ⟨c, hc⟩
      right; left
      have h_sum_le : G c (dirCount D c.succ n) ≤ ∑ c' : Fin 3, G c' (dirCount D c'.succ n) := by
        simpa using Finset.single_le_sum_of_canonicallyOrdered
          (f := fun c' : Fin 3 => G c' (dirCount D c'.succ n)) (Finset.mem_univ c)
      have hT_sum : (q : ℕ∞) + ∑ c' : Fin 3, G c' (dirCount D c'.succ n) = (n : ℕ∞) := by
        rw [← hT_eq_n, closT]
      have h_sum_eq : ∑ c' : Fin 3, G c' (dirCount D c'.succ n) = (n : ℕ∞) - (q : ℕ∞) := by
        -- Coerce to ENNReal for subtraction lemmas
        have hq_ne_top' : (q : ENNReal) ≠ ∞ := by simp
        have hT_sum' : (q : ENNReal) + (∑ c' : Fin 3, G c' (dirCount D c'.succ n) : ENNReal) = (n : ENNReal) := by
          -- Manually coerce the sum
          have := congrArg (fun x : ℕ∞ => (x : ENNReal)) hT_sum
          simpa [natCast_finsetSum_toENNReal Finset.univ (fun c' => G c' (dirCount D c'.succ n))] using this
        have hS_eq : (∑ c' : Fin 3, G c' (dirCount D c'.succ n) : ENNReal) = (n : ENNReal) - (q : ENNReal) := by
          have hn_eq : (n : ENNReal) = (∑ c' : Fin 3, G c' (dirCount D c'.succ n) : ENNReal) + (q : ENNReal) := by
            rw [add_comm, ← hT_sum', add_comm]
          exact (ENNReal.sub_eq_of_eq_add hq_ne_top' hn_eq).symm
        -- Now use ENat.toENNReal_inj to transfer back to ℕ∞
        apply ENat.toENNReal_inj.mp
        have h_all : ((∑ c' : Fin 3, G c' (dirCount D c'.succ n) : ℕ∞) : ENNReal) = (↑((n : ℕ∞) - (q : ℕ∞)) : ENNReal) := by
          rw [natCast_finsetSum_toENNReal Finset.univ (fun c' => G c' (dirCount D c'.succ n))]
          rw [hS_eq]
          -- goal: (n : ENNReal) - (q : ENNReal) = (↑((n : ℕ∞) - (q : ℕ∞)) : ENNReal)
          calc
            (n : ENNReal) - (q : ENNReal) = ((n - q : ℕ) : ENNReal) := by
              simp
            _ = (↑((n : ℕ∞) - (q : ℕ∞)) : ENNReal) := by
              simp
        exact h_all
      have h_sub_le : (n : ℕ∞) - (q : ℕ∞) ≤ ((n0 - q - 1 : ℕ) : ℕ∞) := by
        have h_sub_nat : n - q ≤ n0 - q - 1 := by
          have hn_le_n0_sub_one : n ≤ n0 - 1 := Nat.le_sub_one_of_lt hn_lt_n0
          omega
        -- Use ENat.natCast_sub for ℕ∞ subtraction
        rw [← ENat.natCast_sub (m := n) (n := q)]
        exact mod_cast h_sub_nat
      have hG_le : G c E ≤ G c (dirCount D c.succ n) := hG c hc
      have h_final : G c E ≤ ((n0 - q - 1 : ℕ) : ℕ∞) := by
        calc
          G c E ≤ G c (dirCount D c.succ n) := hG_le
          _ ≤ ∑ c' : Fin 3, G c' (dirCount D c'.succ n) := h_sum_le
          _ = (n : ℕ∞) - (q : ℕ∞) := h_sum_eq
          _ ≤ ((n0 - q - 1 : ℕ) : ℕ∞) := h_sub_le
      refine ⟨c, ⟨n, hc, h_dirCount_le_v_nat⟩, h_final⟩
    · -- Third disjunct: all children have dirCount D c.succ n < E
      push Not at h_exists_c
      set e := fun c : Fin 3 => dirCount D c.succ n with he
      have he_lt_E : ∀ c, e c < E := h_exists_c
      have h_sum4 := (sum_dirCount D n).1
      -- h_sum4 : ∑ a : Fin 4, dirCount D a n = n (in ℕ)
      have h_sum3 : dirCount D 0 n + (e 0 + e 1 + e 2) = n := by
        have h0 : e 0 = dirCount D 1 n := by
          simp [e, show (0 : Fin 3).succ = (1 : Fin 4) by decide]
        have h1 : e 1 = dirCount D 2 n := by
          simp [e, show (1 : Fin 3).succ = (2 : Fin 4) by decide]
        have h2 : e 2 = dirCount D 3 n := by
          simp [e, show (2 : Fin 3).succ = (3 : Fin 4) by decide]
        calc
          dirCount D 0 n + (e 0 + e 1 + e 2) =
              dirCount D 0 n + (dirCount D 1 n + dirCount D 2 n + dirCount D 3 n) := by
            rw [h0, h1, h2]
          _ = ∑ a : Fin 4, dirCount D a n := by
            simp [Fin.sum_univ_four, add_assoc]
          _ = n := h_sum4
      set s := n - q with hs
      have h_q_add_s : q + s = n := by
        rw [hs]
        exact Nat.add_sub_cancel' hq_le_n
      have h_q_add_s_lt_n0 : q + s < n0 := by
        rw [h_q_add_s]
        exact hn_lt_n0
      have h_sum_e_le_q_add_s : e 0 + e 1 + e 2 ≤ q + s := by
        rw [h_q_add_s]
        omega
      have h_dirCount0_eq : dirCount D 0 n = q + s - (e 0 + e 1 + e 2) := by
        rw [h_q_add_s]
        omega
      have h_dirCount0_le_v : dirCount D 0 n ≤ v := h_dirCount_le_v_nat
      have h_sum_G_eq_s : ∑ c : Fin 3, G c (e c) = (s : ℕ∞) := by
        have hT_sum : (q : ℕ∞) + ∑ c : Fin 3, G c (dirCount D c.succ n) = (n : ℕ∞) := by
          rw [← hT_eq_n, closT]
        -- Coerce to ENNReal for subtraction lemmas
        have hq_ne_top' : (q : ENNReal) ≠ ∞ := by simp
        have hT_sum' : (q : ENNReal) + (∑ c : Fin 3, G c (dirCount D c.succ n) : ENNReal) = (n : ENNReal) := by
          have := congrArg (fun x : ℕ∞ => (x : ENNReal)) hT_sum
          simpa [natCast_finsetSum_toENNReal Finset.univ (fun c => G c (dirCount D c.succ n))] using this
        have hS_eq : (∑ c : Fin 3, G c (dirCount D c.succ n) : ENNReal) = (n : ENNReal) - (q : ENNReal) := by
          have hn_eq : (n : ENNReal) = (∑ c : Fin 3, G c (dirCount D c.succ n) : ENNReal) + (q : ENNReal) := by
            rw [add_comm, ← hT_sum', add_comm]
          exact (ENNReal.sub_eq_of_eq_add hq_ne_top' hn_eq).symm
        apply ENat.toENNReal_inj.mp
        have h_all : ((∑ c : Fin 3, G c (e c) : ℕ∞) : ENNReal) = (s : ENNReal) := by
          rw [natCast_finsetSum_toENNReal Finset.univ (fun c => G c (e c))]
          rw [show (∑ c : Fin 3, (G c (e c) : ENNReal)) = (∑ c : Fin 3, G c (dirCount D c.succ n) : ENNReal) by simp [he]]
          rw [hS_eq]
          -- goal: (n : ENNReal) - (q : ENNReal) = (s : ENNReal)
          calc
            (n : ENNReal) - (q : ENNReal) = ((n - q : ℕ) : ENNReal) := by
              simp
            _ = (s : ENNReal) := by rw [hs]
        exact h_all
      right; right
      refine ⟨e, he_lt_E, s, h_q_add_s_lt_n0, h_sum_e_le_q_add_s, ?_, ?_, ?_, h_sum_G_eq_s⟩
      · -- q + s - (e 0 + e 1 + e 2) ≤ v
        rw [← h_dirCount0_eq]
        exact h_dirCount0_le_v
      · -- dirCount D 0 (q + s) = q + s - (e 0 + e 1 + e 2)
        rw [h_q_add_s]
        rw [h_q_add_s] at h_dirCount0_eq
        exact h_dirCount0_eq
      · -- ∀ c, dirCount D c.succ (q + s) = e c
        intro c
        rw [h_q_add_s]

/-- The inclusion of the proof of Lemma 11.2 (B) of the paper: `e_1 < J ≤ E` forces fewer than `J`
directions `1` among the first `K`, or a child `c ≠ 1` entered `E` times with at most `J - 1`
directions `1` by then and `G_c(E)` small, or an end at `n = q + s < K` with counts
`(q + s - |e|, e)`, `e_1 < J`, `e_2, e_3 < E`, and `S_e = s`. -/
theorem lemma16B_incl (q J K E : ℕ) (hJE : J ≤ E) (G : Fin 3 → ℕ → ℕ∞)
    (D : ℕ → Fin 4) (hG : ∀ c, Monotone (G c)) (he : closE q G D 0 < J) :
    dirCount D 1 K < J ∨
      (∃ c : Fin 3, c ≠ 0 ∧ (∃ n, E ≤ dirCount D c.succ n ∧ dirCount D 1 n ≤ J - 1) ∧
        G c E ≤ ((K - q - 1 : ℕ) : ℕ∞)) ∨
      ∃ e : Fin 3 → ℕ, e 0 < J ∧ e 1 < E ∧ e 2 < E ∧ ∃ s : ℕ, q + s < K ∧
        e 0 + e 1 + e 2 ≤ q + s ∧ dirCount D 0 (q + s) = q + s - (e 0 + e 1 + e 2) ∧
        (∀ c : Fin 3, dirCount D c.succ (q + s) = e c) ∧ ∑ c : Fin 3, G c (e c) = (s : ℕ∞) := by
  let N := closN q G D
  have h_closE_eq : closE q G D 0 = countAt D 1 N := by
    dsimp [closE, N]
  have h_countAt_eq : countAt D 1 N < (J : ℕ∞) := by
    rw [← h_closE_eq]
    exact he
  by_cases hK_le_N : (K : ℕ∞) ≤ N
  · -- Case 1: (K : ℕ∞) ≤ N, then dirCount D 1 K < J
    left
    have h_countAt_facts_1 := countAt_facts D 1
    rcases h_countAt_facts_1 with ⟨h_eq, h_le, h_mono⟩
    have h_dirCount_le : (dirCount D 1 K : ℕ∞) ≤ countAt D 1 N :=
      h_le K N hK_le_N
    have h_lt : (dirCount D 1 K : ℕ∞) < (J : ℕ∞) :=
      lt_of_le_of_lt h_dirCount_le h_countAt_eq
    exact (ENat.natCast_lt_natCast.mp h_lt)
  · -- Case 2: ¬ (K : ℕ∞) ≤ N, then N ≠ ⊤ and N = (n : ℕ∞) for some n < K
    have hN_ne_top : N ≠ ⊤ := by
      intro hN_top
      apply hK_le_N
      rw [hN_top]
      exact le_top
    rcases (ENat.ne_top_iff_exists.mp hN_ne_top) with ⟨n, hn_eq⟩
    -- hn_eq : (n : ℕ∞) = N
    have hn_eq_symm : N = (n : ℕ∞) := hn_eq.symm
    have hn_lt_K : (n : ℕ∞) < (K : ℕ∞) := by
      rw [hn_eq.symm] at hK_le_N
      exact lt_of_not_ge hK_le_N
    have hn_lt_K_nat : n < K := ENat.natCast_lt_natCast.mp hn_lt_K
    -- Get q ≤ n and closT = n from closT_closN
    have h_closT := closT_closN q G D hG n hn_eq_symm
    rcases h_closT with ⟨hq_le_n, h_closT_eq⟩
    -- h_closT_eq : closT q G D n = n
    -- From countAt_facts, countAt D a n = dirCount D a n
    have h_countAt_facts_1 := countAt_facts D 1
    rcases h_countAt_facts_1 with ⟨h_countAt_eq_all, h_countAt_le, h_countAt_mono⟩
    have h_dirCount_1_lt_J : dirCount D 1 n < J := by
      have h_lt : countAt D 1 n < (J : ℕ∞) := by
        calc
          countAt D 1 n = countAt D 1 (n : ℕ∞) := rfl
          _ = countAt D 1 N := by rw [hn_eq_symm]
          _ = closE q G D 0 := by rw [← h_closE_eq]
          _ < (J : ℕ∞) := he
      -- h_lt : countAt D 1 n < (J : ℕ∞)
      -- But countAt D 1 n = (dirCount D 1 n : ℕ∞) by h_countAt_eq_all n
      have h_eq_countAt : countAt D 1 n = (dirCount D 1 n : ℕ∞) := h_countAt_eq_all n
      rw [h_eq_countAt] at h_lt
      exact (ENat.natCast_lt_natCast.mp h_lt)
    have h_dirCount_1_lt_E : dirCount D 1 n < E :=
      lt_of_lt_of_le h_dirCount_1_lt_J hJE
    -- Now case split: is there a c ≠ 0 with E ≤ dirCount D c.succ n?
    by_cases h_exists_c : ∃ c : Fin 3, c ≠ 0 ∧ E ≤ dirCount D c.succ n
    · -- Second disjunct
      rcases h_exists_c with ⟨c, hc_ne_zero, hc_E_le⟩
      have h_dirCount_1_le_J_sub_one : dirCount D 1 n ≤ J - 1 := by
        -- From h_dirCount_1_lt_J, we have dirCount D 1 n < J, so dirCount D 1 n ≤ J - 1
        omega
      have h_GcE_le : G c E ≤ ((K - q - 1 : ℕ) : ℕ∞) := by
        -- G c E ≤ G c (dirCount D c.succ n) by monotonicity
        have h_mono_Gc : G c E ≤ G c (dirCount D c.succ n) := hG c hc_E_le
        -- G c (dirCount D c.succ n) ≤ ∑ c', G c' (dirCount D c'.succ n)
        have h_single_le_sum : G c (dirCount D c.succ n) ≤
            ∑ c' : Fin 3, G c' (dirCount D c'.succ n) := by
          have h_nonneg : ∀ i : Fin 3, 0 ≤ G i (dirCount D i.succ n) := by
            intro i; exact zero_le (a := G i (dirCount D i.succ n))
          exact Finset.single_le_sum (by
            intro i hi
            exact h_nonneg i) (Finset.mem_univ c)
        -- From closT_closN: q + ∑ c', G c' (dirCount D c'.succ n) = n
        -- So ∑ c', G c' (dirCount D c'.succ n) ≤ n - q
        have h_sum_le_n_sub_q : ∑ c' : Fin 3, G c' (dirCount D c'.succ n) ≤ (n - q : ℕ) := by
          have hq_ne_top : (q : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top q
          have h_add_le : (q : ℕ∞) + ∑ c' : Fin 3, G c' (dirCount D c'.succ n) ≤ (n : ℕ∞) := by
            -- h_closT_eq : closT q G D n = (n : ℕ∞)
            -- closT q G D n = q + ∑ c', G c' (dirCount D c'.succ n)
            have h_closT_eq_expanded : (q : ℕ∞) + ∑ c' : Fin 3, G c' (dirCount D c'.succ n) = (n : ℕ∞) := by
              dsimp [closT] at h_closT_eq
              exact h_closT_eq
            rw [h_closT_eq_expanded]
          have h_le_sub := ENat.le_sub_of_add_le_left hq_ne_top h_add_le
          -- h_le_sub : ∑ ... ≤ (n : ℕ∞) - (q : ℕ∞) = ((n - q : ℕ) : ℕ∞)
          simpa [ENat.natCast_sub] using h_le_sub
        -- Now combine the inequalities
        have h_GcE_le_n_sub_q : G c E ≤ (n - q : ℕ) :=
          le_trans h_mono_Gc (le_trans h_single_le_sum h_sum_le_n_sub_q)
        -- And (n - q : ℕ) ≤ (K - q - 1 : ℕ) because n < K
        have h_n_sub_q_le_K_sub_q_sub_one : (n - q : ℕ∞) ≤ ((K - q - 1 : ℕ) : ℕ∞) := by
          have hq_lt_K : q < K := lt_of_le_of_lt hq_le_n hn_lt_K_nat
          have h_n_sub_q_le : n - q ≤ K - q - 1 := by
            omega
          exact mod_cast h_n_sub_q_le
        exact le_trans h_GcE_le_n_sub_q h_n_sub_q_le_K_sub_q_sub_one
      right
      left
      refine ⟨c, hc_ne_zero, ?_, h_GcE_le⟩
      refine ⟨n, hc_E_le, h_dirCount_1_le_J_sub_one⟩
    · -- Third disjunct: all dirCount D c.succ n < E
      have h_all_lt_E : ∀ c : Fin 3, dirCount D c.succ n < E := by
        intro c
        by_contra! hge
        have hc_or : c = 0 ∨ c ≠ 0 := by
          exact em _
        rcases hc_or with (hc0 | hc_ne)
        · -- c = 0, but then dirCount D 1 n = dirCount D c.succ n ≥ E, contradiction with h_dirCount_1_lt_E
          rw [hc0] at hge
          simp at hge
          -- hge : E ≤ dirCount D 1 n, but we know dirCount D 1 n < E
          exact Nat.not_le_of_lt h_dirCount_1_lt_E hge
        · -- c ≠ 0, then this contradicts h_exists_c
          exact h_exists_c ⟨c, hc_ne, hge⟩
      -- Define e c := dirCount D c.succ n
      set e : Fin 3 → ℕ := fun c => dirCount D c.succ n with he_def
      have he0_lt_J : e 0 < J := by
        dsimp [e]
        -- dirCount D 1 n < J
        exact h_dirCount_1_lt_J
      have he1_lt_E : e 1 < E := h_all_lt_E 1
      have he2_lt_E : e 2 < E := h_all_lt_E 2
      -- Set s := n - q
      set s := n - q with hs_def
      have h_qs_eq_n : q + s = n := by
        -- Since q ≤ n, q + (n - q) = n
        omega
      have h_qs_lt_K : q + s < K := by
        rw [h_qs_eq_n]
        exact hn_lt_K_nat
      have h_sum_e_le_qs : e 0 + e 1 + e 2 ≤ q + s := by
        -- From sum_dirCount: dirCount D 0 n + e 0 + e 1 + e 2 = n
        -- And n = q + s
        have h_sum_dirCount := sum_dirCount D n
        rcases h_sum_dirCount with ⟨h_sum_eq, h_dirCount_mono⟩
        -- h_sum_eq : ∑ a : Fin 4, dirCount D a n = n
        -- Expand using Fin.sum_univ_four
        have h_sum_expanded : dirCount D 0 n + dirCount D 1 n + dirCount D 2 n + dirCount D 3 n = n := by
          simpa [Fin.sum_univ_four] using h_sum_eq
        -- h_sum_expanded : dirCount D 0 n + dirCount D 1 n + dirCount D 2 n + dirCount D 3 n = n
        -- Replace dirCount D 1 n, dirCount D 2 n, dirCount D 3 n with e 0, e 1, e 2
        have h_sum_expanded' : dirCount D 0 n + e 0 + e 1 + e 2 = n := by
          calc
            dirCount D 0 n + e 0 + e 1 + e 2 = dirCount D 0 n + dirCount D 1 n + dirCount D 2 n + dirCount D 3 n := by
              simp [e]
            _ = n := h_sum_expanded
        rw [← h_qs_eq_n] at h_sum_expanded'
        -- dirCount D 0 n + e 0 + e 1 + e 2 = q + s
        -- So e 0 + e 1 + e 2 ≤ q + s
        omega
      have h_dirCount_0_eq : dirCount D 0 (q + s) = q + s - (e 0 + e 1 + e 2) := by
        have h_sum_dirCount := sum_dirCount D (q + s)
        rcases h_sum_dirCount with ⟨h_sum_eq, h_dirCount_mono⟩
        have h_sum_expanded : dirCount D 0 (q + s) + dirCount D 1 (q + s) + dirCount D 2 (q + s) + dirCount D 3 (q + s) = q + s := by
          simpa [Fin.sum_univ_four] using h_sum_eq
        -- q + s = n, so we can rewrite
        rw [h_qs_eq_n] at h_sum_expanded
        -- Now h_sum_expanded : dirCount D 0 n + dirCount D 1 n + dirCount D 2 n + dirCount D 3 n = n
        -- Replace dirCount D 1 n, dirCount D 2 n, dirCount D 3 n with e 0, e 1, e 2
        have h_sum_expanded' : dirCount D 0 n + e 0 + e 1 + e 2 = n := by
          calc
            dirCount D 0 n + e 0 + e 1 + e 2 = dirCount D 0 n + dirCount D 1 n + dirCount D 2 n + dirCount D 3 n := by
              simp [e]
            _ = n := h_sum_expanded
        rw [← h_qs_eq_n] at h_sum_expanded'
        -- dirCount D 0 n + e 0 + e 1 + e 2 = q + s
        omega
      have h_dirCount_succ_eq_e : ∀ c : Fin 3, dirCount D c.succ (q + s) = e c := by
        intro c
        rw [h_qs_eq_n]
      have h_sum_G_eq_s : ∑ c : Fin 3, G c (e c) = (s : ℕ∞) := by
        -- From closT_closN: closT q G D n = n
        -- closT q G D n = q + ∑ c, G c (dirCount D c.succ n) = q + ∑ c, G c (e c)
        -- And n = q + s
        -- So q + ∑ c, G c (e c) = q + s
        have h_eq : (q : ℕ∞) + ∑ c : Fin 3, G c (e c) = (q : ℕ∞) + (s : ℕ∞) := by
          calc
            (q : ℕ∞) + ∑ c : Fin 3, G c (e c) = closT q G D n := by
              simp [closT, e]
            _ = (n : ℕ∞) := h_closT_eq
            _ = (q + s : ℕ) := by rw [h_qs_eq_n]
            _ = (q : ℕ∞) + (s : ℕ∞) := by simp
        -- Now cancel q from both sides using toNat
        have hq_ne_top : (q : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top q
        -- The sum is not ⊤ because (q : ℕ∞) + sum = (n : ℕ∞) ≠ ⊤
        have h_sum_ne_top : ∑ c : Fin 3, G c (e c) ≠ ⊤ := by
          intro hsum_top
          have h_closT_top : closT q G D n = ⊤ := by
            dsimp [closT, e]
            rw [hsum_top]
            simp
          rw [h_closT_top] at h_closT_eq
          exact (ENat.natCast_ne_top n) h_closT_eq.symm
        -- Now apply toNat to both sides of h_eq
        have h_toNat_eq : ((q : ℕ∞) + ∑ c : Fin 3, G c (e c)).toNat =
            ((q : ℕ∞) + (s : ℕ∞)).toNat := by
          rw [h_eq]
        -- Use ENat.toNat_add
        have h_toNat_add_left : ((q : ℕ∞) + ∑ c : Fin 3, G c (e c)).toNat =
            (q : ℕ∞).toNat + (∑ c : Fin 3, G c (e c)).toNat :=
          ENat.toNat_add hq_ne_top h_sum_ne_top
        have hs_ne_top : (s : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top (a := s)
        have h_toNat_add_right : ((q : ℕ∞) + (s : ℕ∞)).toNat =
            (q : ℕ∞).toNat + (s : ℕ∞).toNat :=
          ENat.toNat_add hq_ne_top hs_ne_top
        -- (q : ℕ∞).toNat = q, (s : ℕ∞).toNat = s
        have h_q_toNat : (q : ℕ∞).toNat = q := by simp
        have h_s_toNat : (s : ℕ∞).toNat = s := by simp
        rw [h_toNat_add_left, h_toNat_add_right, h_q_toNat, h_s_toNat] at h_toNat_eq
        -- Now h_toNat_eq : q + (∑ c, G c (e c)).toNat = q + s
        -- Cancel q in ℕ
        have h_sum_toNat_eq_s : (∑ c : Fin 3, G c (e c)).toNat = s := by
          omega
        -- Now use ENat.natCast_toNat to get back to ℕ∞
        calc
          ∑ c : Fin 3, G c (e c) = ((∑ c : Fin 3, G c (e c)).toNat : ℕ∞) := by
            rw [ENat.natCast_toNat h_sum_ne_top]
          _ = (s : ℕ∞) := by rw [h_sum_toNat_eq_s]
      right
      right
      refine ⟨e, he0_lt_J, he1_lt_E, he2_lt_E, s, h_qs_lt_K, h_sum_e_le_qs, h_dirCount_0_eq, h_dirCount_succ_eq_e, h_sum_G_eq_s⟩

/-- Abel summation: cumulative domination of `p` by `r` on `[0, n)` gives domination of the sums
weighted by a nonnegative weight nonincreasing on `[0, n)`. -/
theorem sum_mul_le_of_cum (p r : ℕ → ℝ) : ∀ (n : ℕ) (w : ℕ → ℝ), (∀ g < n, 0 ≤ w g) →
    (∀ a b, a ≤ b → b < n → w b ≤ w a) →
    (∀ u < n, ∑ g ∈ Finset.range (u + 1), p g ≤ ∑ g ∈ Finset.range (u + 1), r g) →
    ∑ g ∈ Finset.range n, p g * w g ≤ ∑ g ∈ Finset.range n, r g * w g
  | 0, _, _, _, _ => by simp
  | n + 1, w, hw0, hw, hc => by
    have key : ∀ q : ℕ → ℝ, ∑ g ∈ Finset.range (n + 1), q g * w g =
        ∑ g ∈ Finset.range n, q g * (w g - w n) + w n * ∑ g ∈ Finset.range (n + 1), q g := by
      intro q
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    rw [key p, key r]
    have h1 := sum_mul_le_of_cum p r n (fun g => w g - w n)
      (fun g hg => sub_nonneg.2 (hw g n hg.le (Nat.lt_succ_self n)))
      (fun a b hab hb => sub_le_sub_right (hw a b hab (by omega)) _)
      (fun u hu => hc u (by omega))
    exact add_le_add h1 (mul_le_mul_of_nonneg_left (hc n (Nat.lt_succ_self n))
      (hw0 n (Nat.lt_succ_self n)))

/-- Cumulative domination of each of three nonnegative mass functions gives cumulative domination
of their convolution. -/
theorem cum_conv3_mono (p1 p2 p3 r1 r2 r3 : ℕ → ℝ) (t : ℕ)
    (hp : ∀ g, 0 ≤ p1 g ∧ 0 ≤ p2 g ∧ 0 ≤ p3 g) (hr : ∀ g, 0 ≤ r1 g ∧ 0 ≤ r2 g ∧ 0 ≤ r3 g)
    (h1 : ∀ u ≤ t, ∑ g ∈ Finset.range (u + 1), p1 g ≤ ∑ g ∈ Finset.range (u + 1), r1 g)
    (h2 : ∀ u ≤ t, ∑ g ∈ Finset.range (u + 1), p2 g ≤ ∑ g ∈ Finset.range (u + 1), r2 g)
    (h3 : ∀ u ≤ t, ∑ g ∈ Finset.range (u + 1), p3 g ≤ ∑ g ∈ Finset.range (u + 1), r3 g) :
    ∑ s ∈ Finset.range (t + 1), conv3 p1 p2 p3 s ≤ ∑ s ∈ Finset.range (t + 1), conv3 r1 r2 r3 s := by
  rw [cum_conv3_eq, cum_conv3_eq]
  have hR3 : ∀ a b, a ≤ b → ∑ g ∈ Finset.range a, r3 g ≤ ∑ g ∈ Finset.range b, r3 g :=
    fun a b hab => Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      (fun i _ _ => (hr i).2.2)
  have hR30 : ∀ a, 0 ≤ ∑ g ∈ Finset.range a, r3 g :=
    fun a => Finset.sum_nonneg (fun i _ => (hr i).2.2)
  have hF : ∀ m ≤ t + 1, ∑ g ∈ Finset.range m, p3 g ≤ ∑ g ∈ Finset.range m, r3 g := by
    intro m hm
    cases m with
    | zero => simp
    | succ u => exact h3 u (by omega)
  -- the weight of the outer sum on the right
  set W : ℕ → ℝ := fun g1 => ∑ g2 ∈ Finset.range (t + 1 - g1),
    r2 g2 * ∑ g3 ∈ Finset.range (t + 1 - g1 - g2), r3 g3 with hW
  calc ∑ g1 ∈ Finset.range (t + 1), p1 g1 * ∑ g2 ∈ Finset.range (t + 1 - g1),
          p2 g2 * ∑ g3 ∈ Finset.range (t + 1 - g1 - g2), p3 g3
      ≤ ∑ g1 ∈ Finset.range (t + 1), p1 g1 * ∑ g2 ∈ Finset.range (t + 1 - g1),
          p2 g2 * ∑ g3 ∈ Finset.range (t + 1 - g1 - g2), r3 g3 := by
        refine Finset.sum_le_sum fun g1 _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun g2 _ => mul_le_mul_of_nonneg_left (hF _ (by omega)) (hp g2).2.1)
          (hp g1).1
    _ ≤ ∑ g1 ∈ Finset.range (t + 1), p1 g1 * W g1 := by
        refine Finset.sum_le_sum fun g1 hg1 => mul_le_mul_of_nonneg_left ?_ (hp g1).1
        have hg1' := Finset.mem_range.1 hg1
        exact sum_mul_le_of_cum p2 r2 (t + 1 - g1)
          (fun g2 => ∑ g3 ∈ Finset.range (t + 1 - g1 - g2), r3 g3)
          (fun g _ => hR30 _) (fun a b hab _ => hR3 _ _ (by omega))
          (fun u hu => h2 u (by omega))
    _ ≤ ∑ g1 ∈ Finset.range (t + 1), r1 g1 * W g1 := by
        refine sum_mul_le_of_cum p1 r1 (t + 1) W
          (fun g _ => Finset.sum_nonneg fun g2 _ => mul_nonneg (hr g2).2.1 (hR30 _)) ?_
          (fun u hu => h1 u (by omega))
        intro a b hab _
        simp only [hW]
        calc ∑ g2 ∈ Finset.range (t + 1 - b), r2 g2 * ∑ g3 ∈ Finset.range (t + 1 - b - g2), r3 g3
            ≤ ∑ g2 ∈ Finset.range (t + 1 - b), r2 g2 * ∑ g3 ∈ Finset.range (t + 1 - a - g2), r3 g3 :=
              Finset.sum_le_sum fun g2 _ =>
                mul_le_mul_of_nonneg_left (hR3 _ _ (by omega)) (hr g2).2.1
          _ ≤ ∑ g2 ∈ Finset.range (t + 1 - a), r2 g2 * ∑ g3 ∈ Finset.range (t + 1 - a - g2), r3 g3 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
                (fun g2 _ _ => mul_nonneg (hr g2).2.1 (hR30 _))

end FrogModel.D3.Iface
