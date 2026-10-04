module

public import FrogModel.LemmaR.Walk
public import FrogModel.LemmaR.Tools

@[expose] public section

/-!
# The recurrence criterion on `T_d`: the returns of one frog

By `map_glueOne` the step sequence of a frog is its pieces glued at its returns to the root, and it
returns at least `m` times iff its first `m` pieces are closed (`returnCount_glueOne`). So
`P(N_u ≥ m) = h(u) h(root)^(m - 1)` (`seqLaw_returnCount_ge`) and `E N_u^2 ≤ 6 d^(-|u|)` for
`d ≥ 2` (`lintegral_returnCount_sq_le`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaR

/-- At least `m` returns iff at least `m` returns by some time `t`. -/
theorem FrogModel.LemmaR.le_returnCount_iff {d : ℕ} (u : Vertex d) (x : ℕ → Step d) (m : ℕ) :
    (m : ℕ∞) ≤ returnCount u x ↔ ∃ t, m ≤ (returns u x t).card := by
  constructor
  · intro h
    obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_encard_eq h
    have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard
    obtain ⟨t, ht⟩ := hTfin.bddAbove
    refine ⟨t, ?_⟩
    have hsub : T ⊆ ↑(returns u x t) := fun s hs => by
      simp only [returns, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
      exact ⟨⟨(hTS hs).1, ht hs⟩, (hTS hs).2⟩
    have := Set.encard_le_encard hsub
    rw [hTcard, Set.encard_coe_eq_coe_finsetCard] at this
    exact_mod_cast this
  · rintro ⟨t, ht⟩
    have hsub : (↑(returns u x t) : Set ℕ) ⊆ {s | 1 ≤ s ∧ walk u x s = root} := fun s hs => by
      simp only [returns, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hs
      exact ⟨hs.1.1, hs.2⟩
    calc (m : ℕ∞) ≤ (returns u x t).card := by exact_mod_cast ht
      _ = (↑(returns u x t) : Set ℕ).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
      _ ≤ returnCount u x := Set.encard_le_encard hsub

/-- The glued walk returns to the root at least `m` times iff its first `m` pieces are closed. -/
theorem FrogModel.LemmaR.returnCount_glueOne {d : ℕ} (u : Vertex d) (Z : ℕ → ℕ → Step d)
    (m : ℕ) :
    (m : ℕ∞) ≤ returnCount u (glueOne u Z) ↔ ∀ j < m, cut (Seg.start (u, j)) (Z j) ≠ ⊤ := by
  set ζ : Pieces d := fun σ => Z σ.2 with hζ
  have hg : glueOne u Z = glue ζ u := rfl
  have hcs : ∀ k, cutSum ζ u k ≠ ⊤ ↔ ∀ j < k, cut (Seg.start (u, j)) (Z j) ≠ ⊤ := by
    intro k
    induction k with
    | zero => simp [cutSum]
    | succ k ih =>
      have hk : cutSum ζ u (k + 1) = cutSum ζ u k + cut (Seg.start (u, k)) (Z k) := rfl
      rw [hk, ne_eq, ENat.add_eq_top, not_or, ← ne_eq, ← ne_eq, ih]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h1 j hj
        · exact h2
      · intro h
        exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
  rw [hg, le_returnCount_iff, ← hcs]
  simp_rw [card_returns_glue, ← cutSum_le_iff]
  constructor
  · rintro ⟨t, ht⟩ htop
    rw [htop] at ht
    exact absurd ht (by simp)
  · intro h
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.1 h
    exact ⟨t, ht.symm.le⟩

theorem FrogModel.LemmaR.measurable_returnCount {d : ℕ} (u : Vertex d) :
    Measurable (returnCount (d := d) u) := by
  -- First, show that the ℝ≥0∞-valued version is measurable via a tsum representation
  have h_tsum_eq : ∀ (x : ℕ → Step d),
      (returnCount u x : ℝ≥0∞) = ∑' t : ℕ, (if 1 ≤ t ∧ walk u x t = root then (1 : ℝ≥0∞) else 0) := by
    intro x
    dsimp [returnCount]
    -- (Set.encard s : ℝ≥0∞) = ∑' (x : s), 1
    rw [← ENNReal.tsum_set_one {t : ℕ | 1 ≤ t ∧ walk u x t = root}]
    -- ∑' (x : s), 1 = ∑' x, s.indicator (fun _ => 1) x
    rw [tsum_subtype (s := {t : ℕ | 1 ≤ t ∧ walk u x t = root}) (f := fun _ => (1 : ℝ≥0∞))]
    simp [Set.indicator]
  have h_meas_ennreal : Measurable (fun (x : ℕ → Step d) => (returnCount u x : ℝ≥0∞)) := by
    have h_eq : (fun (x : ℕ → Step d) => (returnCount u x : ℝ≥0∞)) =
        (fun x => ∑' t : ℕ, (if 1 ≤ t ∧ walk u x t = root then (1 : ℝ≥0∞) else 0)) := by
      ext x; exact h_tsum_eq x
    rw [h_eq]
    refine Measurable.tsum (fun t => ?_)
    by_cases h : 1 ≤ t
    · -- 1 ≤ t is true, so the function is the indicator of {x | walk u x t = root}
      have h_meas_indicator : Measurable ({x : ℕ → Step d | walk u x t = root}.indicator (fun _ => (1 : ℝ≥0∞))) :=
        Measurable.indicator measurable_const (measurableSet_walk_eq u t root)
      -- Set.indicator s f x = if x ∈ s then f x else 0
      have h_eq : ({x : ℕ → Step d | walk u x t = root}.indicator (fun _ => (1 : ℝ≥0∞))) =
          (fun x => if walk u x t = root then (1 : ℝ≥0∞) else 0) := by
        ext x; simp [Set.indicator_apply]
      simpa [h, h_eq] using h_meas_indicator
    · -- 1 ≤ t is false, so the function is constant 0
      have h_eq' : (fun (x : ℕ → Step d) => (if 1 ≤ t ∧ walk u x t = root then (1 : ℝ≥0∞) else 0)) = fun _ => 0 := by
        ext x; simp [h]
      rw [h_eq']
      exact measurable_const
  -- Now use measurable_to_countable' to get measurability into ℕ∞
  refine measurable_to_countable' (fun k => ?_)
  have h_preimage_eq : (returnCount u) ⁻¹' {k} =
      (fun (x : ℕ → Step d) => (returnCount u x : ℝ≥0∞)) ⁻¹' {(k : ℝ≥0∞)} := by
    ext x; simp [ENat.toENNReal_inj]
  rw [h_preimage_eq]
  exact h_meas_ennreal (measurableSet_singleton _)

/-- The law of `N_u`: at least `m` returns with the probability of `m` closed independent
pieces. -/
theorem FrogModel.LemmaR.seqLaw_returnCount_ge {d : ℕ} [NeZero d] (u : Vertex d) (m : ℕ) :
    seqLaw d {x | (m : ℕ∞) ≤ returnCount u x} =
      ∏ j ∈ Finset.range m, seqLaw d {y | cut (Seg.start (u, j)) y ≠ ⊤} := by
  have hmeasS : MeasurableSet {x : ℕ → Step d | (m : ℕ∞) ≤ returnCount u x} :=
    (measurable_returnCount u) (MeasurableSet.of_discrete (s := Set.Ici (m : ℕ∞)))
  have hmap : seqLaw d {x | (m : ℕ∞) ≤ returnCount u x} =
      ((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d).map
        (glueOne u)) {x | (m : ℕ∞) ≤ returnCount u x} := by
    rw [map_glueOne]
  rw [hmap, Measure.map_apply (measurable_glueOne u) hmeasS]
  have hpre : glueOne u ⁻¹' {x | (m : ℕ∞) ≤ returnCount u x} =
      Set.pi (Finset.range m : Set ℕ) (fun j => {y | cut (Seg.start (u, j)) y ≠ ⊤}) := by
    ext Z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio]
    exact returnCount_glueOne u Z m
  rw [hpre, Measure.infinitePi_pi]
  intro j _
  exact measurableSet_cut_ne_top _

/-- `E N_u^2 ≤ 6 d^(-|u|)` for `d ≥ 2`. -/
theorem FrogModel.LemmaR.lintegral_returnCount_sq_le {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (u : Vertex d) :
    ∫⁻ x, ((returnCount u x : ℕ∞) : ℝ≥0∞) ^ 2 ∂seqLaw d ≤ 6 * ((d : ℝ≥0∞)⁻¹) ^ u.length := by
  set h : Vertex d → ℝ≥0∞ := fun v => seqLaw d {y | cut v y ≠ ⊤} with hh
  have hmeas : ∀ m : ℕ,
      MeasurableSet {x : ℕ → Step d | ((m + 1 : ℕ) : ℕ∞) ≤ returnCount u x} := fun m =>
    (measurable_returnCount u) (MeasurableSet.of_discrete (s := Set.Ici ((m + 1 : ℕ) : ℕ∞)))
  have hroot : h root ≤ 2⁻¹ :=
    hitProb_root_le.trans (ENNReal.inv_le_inv.2 (by exact_mod_cast hd))
  have hu : h u ≤ ((d : ℝ≥0∞)⁻¹) ^ u.length := by
    by_cases hu : u = root
    · subst hu
      simp only [root, List.length_nil, pow_zero]
      exact prob_le_one
    · exact hitProb_le u hu
  calc ∫⁻ x, ((returnCount u x : ℕ∞) : ℝ≥0∞) ^ 2 ∂seqLaw d
      = ∫⁻ x, ∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) *
          {x | ((m + 1 : ℕ) : ℕ∞) ≤ returnCount u x}.indicator 1 x ∂seqLaw d := by
        refine lintegral_congr fun x => ?_
        rw [sq_eq_tsum]
        congr 1
        funext m
        simp [Set.indicator]
    _ = ∑' m : ℕ, ∫⁻ x, (2 * m + 1 : ℝ≥0∞) *
          {x | ((m + 1 : ℕ) : ℕ∞) ≤ returnCount u x}.indicator 1 x ∂seqLaw d :=
        lintegral_tsum fun m =>
          ((measurable_one.indicator (hmeas m)).const_mul _).aemeasurable
    _ = ∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) * (h u * h root ^ m) := by
        congr 1
        funext m
        rw [lintegral_const_mul _ (measurable_one.indicator (hmeas m)),
          lintegral_indicator_one (hmeas m), seqLaw_returnCount_ge, Finset.prod_range_succ']
        simp only [Seg.start, hh, Finset.prod_const, Finset.card_range]
        ring
    _ = h u * ∑' m : ℕ, (2 * m + 1 : ℝ≥0∞) * h root ^ m := by
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext m
        ring
    _ ≤ ((d : ℝ≥0∞)⁻¹) ^ u.length * 6 := by
        gcongr
        exact tsum_odd_geom_le _ hroot
    _ = 6 * ((d : ℝ≥0∞)⁻¹) ^ u.length := mul_comm _ _
