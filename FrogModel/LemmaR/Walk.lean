module

public import FrogModel.LemmaR.Defs
public import FrogModel.Lemmas.Refresh

@[expose] public section

/-!
# Hitting the root (the bound behind Lemma 9.1 of the paper)

`f(v) = d^(-|v|)` is harmonic for the walk off the root (`sum_step_pow`). With the Markov property
at time `1` (`seqLaw_head_tail`), induction on time gives `P(walk from v at the root by time t) ≤
d^(-|v|)` (`hitWithin_le`), hence `P(hit) ≤ d^(-|v|)` for `v ≠ root` (`hitProb_le`) and
`P(return) ≤ 1/d` from the root (`hitProb_root_le`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaR

/-- The walk after its first step is the walk from the first position driven by the shifted
steps. -/
theorem FrogModel.LemmaR.walk_succ_tail {d : ℕ} (v : Vertex d) (x : ℕ → Step d) (n : ℕ) :
    walk v x (n + 1) = walk (step v (x 0)) (fun k => x (k + 1)) n := by
  induction n with
  | zero =>
    simp [walk]
  | succ n ih =>
    simpa [walk] using congrArg (fun t => step t (x (n + 1))) ih

/-- Each step value has probability `1 / (d (d + 1))`. -/
theorem FrogModel.LemmaR.stepLaw_singleton {d : ℕ} [NeZero d] (ξ : Step d) :
    stepLaw d {ξ} = ((d * (d + 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [stepLaw]
  rw [ProbabilityTheory.uniformOn_univ]
  rw [MeasureTheory.Measure.count_singleton]
  have hcard : Fintype.card (Step d) = d * (d + 1) := by
    simp [Step, Fintype.card_prod, Fintype.card_fin]
  rw [hcard]
  simp

/-- `v ↦ d^(-|v|)` is harmonic off the root: summed over the `d (d + 1)` step values. -/
theorem FrogModel.LemmaR.sum_step_pow {d : ℕ} [NeZero d] (c : Fin d) (w : Vertex d) :
    ∑ ξ : Step d, ((d : ℝ≥0∞)⁻¹) ^ (step (c :: w) ξ).length =
      ((d * (d + 1) : ℕ) : ℝ≥0∞) * ((d : ℝ≥0∞)⁻¹) ^ (c :: w).length := by
  set q := ((d : ℝ≥0∞)⁻¹) with hq
  have hlen : (c :: w).length = w.length + 1 := by simp
  rw [hlen]
  have hd_ne_zero : (d : ℝ≥0∞) ≠ 0 := by
    exact mod_cast NeZero.ne d
  have hd_ne_top : (d : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.natCast_ne_top d
  have hdq : (d : ℝ≥0∞) * q = 1 := by
    rw [hq]
    exact ENNReal.mul_inv_cancel hd_ne_zero hd_ne_top
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_succ]
  have hstep0 : ∀ a : Fin d, step (c :: w) (a, 0) = w := by
    intro a; simp [step]
  have hstep_succ : ∀ a b : Fin d, step (c :: w) (a, Fin.succ b) = b :: c :: w := by
    intro a b; simp [step]
  have hlen0 : ∀ a : Fin d, (step (c :: w) (a, 0)).length = w.length := by
    intro a; simp [hstep0 a]
  have hlen_succ : ∀ a b : Fin d, (step (c :: w) (a, Fin.succ b)).length = w.length + 2 := by
    intro a b; simp [hstep_succ a b]
  simp_rw [hlen0, hlen_succ]
  have hinner : ∀ a : Fin d, (∑ b : Fin d, q ^ (w.length + 2)) = (d : ℝ≥0∞) * q ^ (w.length + 2) := by
    intro a
    rw [Finset.sum_const]
    simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum : (∑ a : Fin d, (q ^ w.length + ∑ b : Fin d, q ^ (w.length + 2))) =
      (∑ a : Fin d, (q ^ w.length + (d : ℝ≥0∞) * q ^ (w.length + 2))) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hinner x]
  rw [hsum]
  have houter : (∑ a : Fin d, (q ^ w.length + (d : ℝ≥0∞) * q ^ (w.length + 2))) =
      (d : ℝ≥0∞) * (q ^ w.length + (d : ℝ≥0∞) * q ^ (w.length + 2)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const]
    simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add]
  rw [houter]
  calc
    (d : ℝ≥0∞) * (q ^ w.length + (d : ℝ≥0∞) * q ^ (w.length + 2))
        = (d : ℝ≥0∞) * q ^ w.length + (d : ℝ≥0∞) * ((d : ℝ≥0∞) * q ^ (w.length + 2)) := by ring
    _ = (d : ℝ≥0∞) * q ^ w.length + (d : ℝ≥0∞) * (d : ℝ≥0∞) * q ^ (w.length + 2) := by ring
    _ = (d : ℝ≥0∞) * q ^ w.length + (d : ℝ≥0∞) * (d : ℝ≥0∞) * (q ^ w.length * q ^ 2) := by
      rw [pow_add, pow_two]
    _ = (d : ℝ≥0∞) * q ^ w.length + ((d : ℝ≥0∞) * (d : ℝ≥0∞) * q ^ w.length) * q ^ 2 := by ring
    _ = (d : ℝ≥0∞) * q ^ w.length + ((d : ℝ≥0∞) * q) * ((d : ℝ≥0∞) * q ^ w.length) * q := by ring
    _ = (d : ℝ≥0∞) * q ^ w.length + 1 * ((d : ℝ≥0∞) * q ^ w.length) * q := by rw [hdq]
    _ = (d : ℝ≥0∞) * q ^ w.length + (d : ℝ≥0∞) * q ^ w.length * q := by simp
    _ = (d : ℝ≥0∞) * q ^ w.length * (1 + q) := by ring
    _ = ((d : ℝ≥0∞) * q ^ w.length) * 1 + ((d : ℝ≥0∞) * q ^ w.length) * q := by ring
    _ = (d : ℝ≥0∞) * q ^ w.length + (d : ℝ≥0∞) * q ^ w.length * q := by simp
    _ = (d : ℝ≥0∞) * q ^ w.length + ((d : ℝ≥0∞) * q) * q ^ w.length := by ring
    _ = (d : ℝ≥0∞) * q ^ w.length + 1 * q ^ w.length := by rw [hdq]
    _ = (d : ℝ≥0∞) * q ^ w.length + q ^ w.length := by simp
    _ = ((d : ℝ≥0∞) + 1) * q ^ w.length := by ring
    _ = ((d + 1 : ℕ) : ℝ≥0∞) * q ^ w.length := by simp
    _ = (((d * (d + 1) : ℕ) : ℝ≥0∞) * q) * q ^ w.length := by
      have h : ((d + 1 : ℕ) : ℝ≥0∞) = ((d * (d + 1) : ℕ) : ℝ≥0∞) * q := by
        calc
          ((d + 1 : ℕ) : ℝ≥0∞) = ((d + 1 : ℕ) : ℝ≥0∞) * 1 := by simp
          _ = ((d + 1 : ℕ) : ℝ≥0∞) * ((d : ℝ≥0∞) * q) := by rw [hdq]
          _ = ((d + 1 : ℕ) : ℝ≥0∞) * (d : ℝ≥0∞) * q := by ring
          _ = ((d * (d + 1) : ℕ) : ℝ≥0∞) * q := by push_cast; ring
      rw [h]
    _ = ((d * (d + 1) : ℕ) : ℝ≥0∞) * (q * q ^ w.length) := by ring
    _ = ((d * (d + 1) : ℕ) : ℝ≥0∞) * q ^ (w.length + 1) := by rw [pow_succ']

/-- Markov property at time `1` for an i.i.d. step sequence. -/
theorem FrogModel.LemmaR.seqLaw_head_tail {d : ℕ} [NeZero d]
    (P : Step d → (ℕ → Step d) → Prop) (hP : ∀ ξ, MeasurableSet {y : ℕ → Step d | P ξ y}) :
    seqLaw d {x | P (x 0) (fun k => x (k + 1))} =
      ∑ ξ : Step d, stepLaw d {ξ} * seqLaw d {y | P ξ y} := by
  set F : (ℕ → Step d) → Step d × (ℕ → Step d) := fun x => (x 0, fun k => x (k + 1)) with hF
  have hFm : Measurable F :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.2 fun k => measurable_pi_apply (k + 1))
  have hmap : (seqLaw d).map F = (stepLaw d).prod (seqLaw d) :=
    FrogModel.infinitePi_map_pair_injective (stepLaw d) Nat.succ Nat.succ_injective 0
      fun a => Nat.succ_ne_zero a
  set S : Set (Step d × (ℕ → Step d)) := ⋃ ξ : Step d, {ξ} ×ˢ {y | P ξ y} with hS
  have hSm : MeasurableSet S :=
    MeasurableSet.iUnion fun ξ => (measurableSet_singleton ξ).prod (hP ξ)
  have hpre : {x : ℕ → Step d | P (x 0) (fun k => x (k + 1))} = F ⁻¹' S := by
    ext x
    simp [hF, hS]
  rw [hpre, ← Measure.map_apply hFm hSm, hmap, measure_iUnion]
  · rw [tsum_fintype]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Measure.prod_prod]
  · intro ξ η hne
    refine Set.disjoint_left.2 fun p hp hq => hne ?_
    simp only [Set.mem_prod, Set.mem_singleton_iff] at hp hq
    rw [← hp.1, ← hq.1]
  · exact fun ξ => (measurableSet_singleton ξ).prod (hP ξ)

/-- The walk from `v` visits the root by time `t` with probability at most `d^(-|v|)`. -/
theorem FrogModel.LemmaR.hitWithin_le {d : ℕ} [NeZero d] (t : ℕ) (v : Vertex d) :
    seqLaw d {x | ∃ s ≤ t, walk v x s = root} ≤ ((d : ℝ≥0∞)⁻¹) ^ v.length := by
  induction t generalizing v with
  | zero =>
    cases v with
    | nil =>
      simp only [List.length_nil, pow_zero]
      exact prob_le_one
    | cons c w =>
      have h0 : {x : ℕ → Step d | ∃ s ≤ 0, walk (c :: w) x s = root} = ∅ := by
        ext x
        simp [walk, root]
      rw [h0, measure_empty]
      exact zero_le
  | succ t ih =>
    cases v with
    | nil =>
      simp only [List.length_nil, pow_zero]
      exact prob_le_one
    | cons c w =>
      have hset : {x : ℕ → Step d | ∃ s ≤ t + 1, walk (c :: w) x s = root} =
          {x | (fun ξ y => ∃ s ≤ t, walk (step (c :: w) ξ) y s = root) (x 0)
            (fun k => x (k + 1))} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨s, hs, hw⟩
          cases s with
          | zero => simp [walk, root] at hw
          | succ s => exact ⟨s, by omega, by rw [← walk_succ_tail]; exact hw⟩
        · rintro ⟨s, hs, hw⟩
          exact ⟨s + 1, by omega, by rw [walk_succ_tail]; exact hw⟩
      have hmeasP : ∀ ξ, MeasurableSet
          {y : ℕ → Step d | ∃ s ≤ t, walk (step (c :: w) ξ) y s = root} := by
        intro ξ
        have : {y : ℕ → Step d | ∃ s ≤ t, walk (step (c :: w) ξ) y s = root} =
            ⋃ s ∈ Finset.range (t + 1), {y | walk (step (c :: w) ξ) y s = root} := by
          ext y
          simp
        rw [this]
        exact Finset.measurableSet_biUnion _ fun s _ => measurableSet_walk_eq _ _ _
      have hD : ((d * (d + 1) : ℕ) : ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.mul_ne_zero (NeZero.ne d) (Nat.succ_ne_zero d))
      rw [hset, seqLaw_head_tail _ hmeasP]
      calc ∑ ξ : Step d, stepLaw d {ξ} *
            seqLaw d {y | ∃ s ≤ t, walk (step (c :: w) ξ) y s = root}
          ≤ ∑ ξ : Step d, ((d * (d + 1) : ℕ) : ℝ≥0∞)⁻¹ *
              ((d : ℝ≥0∞)⁻¹) ^ (step (c :: w) ξ).length := by
            gcongr with ξ
            · exact le_of_eq (stepLaw_singleton ξ)
            · exact ih _
        _ = ((d * (d + 1) : ℕ) : ℝ≥0∞)⁻¹ *
              (((d * (d + 1) : ℕ) : ℝ≥0∞) * ((d : ℝ≥0∞)⁻¹) ^ (c :: w).length) := by
            rw [← Finset.mul_sum, sum_step_pow]
        _ = ((d : ℝ≥0∞)⁻¹) ^ (c :: w).length := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hD (ENNReal.natCast_ne_top _), one_mul]

theorem FrogModel.LemmaR.measurableSet_cut_ne_top {d : ℕ} (v : Vertex d) :
    MeasurableSet {x : ℕ → Step d | cut v x ≠ ⊤} := by
  have h_eq : {x | cut v x ≠ ⊤} = ⋃ n : ℕ, {x | (n : ℕ∞) ≤ cut v x}ᶜ := by
    ext x
    constructor
    · intro hx
      rcases ENat.exists_nat_gt hx with ⟨m, hm⟩
      refine Set.mem_iUnion.mpr ⟨m, ?_⟩
      intro hle
      exact not_lt.mpr hle hm
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      intro htop
      have hle : (n : ℕ∞) ≤ cut v x := by
        simp [htop]
      exact hn hle
  rw [h_eq]
  refine MeasurableSet.iUnion fun n => ?_
  have h_meas : MeasurableSet {x | (n : ℕ∞) ≤ cut v x} :=
    FrogModel.measurableSet_cut_ge v n
  exact h_meas.compl

/-- From `v ≠ root` the walk ever hits the root with probability at most `d^(-|v|)`. -/
theorem FrogModel.LemmaR.hitProb_le {d : ℕ} [NeZero d] (v : Vertex d) (hv : v ≠ root) :
    seqLaw d {x | cut v x ≠ ⊤} ≤ ((d : ℝ≥0∞)⁻¹) ^ v.length := by
  -- First, relate cut ≠ ⊤ to existence of a hitting time
  have h_cut_iff (x : ℕ → Step d) : (cut v x ≠ ⊤) ↔ (∃ n, 1 ≤ n ∧ walk v x n = root) := by
    dsimp [cut]
    set S := ((fun n : ℕ => (n : ℕ∞)) '' {n | 1 ≤ n ∧ walk v x n = root}) with hS
    constructor
    · intro h
      by_contra h_empty
      have hS_empty : S = (∅ : Set ℕ∞) := by
        ext y
        constructor
        · rintro ⟨n, ⟨hn, hw⟩, rfl⟩
          exact h_empty ⟨n, hn, hw⟩
        · intro hy
          simp at hy
      rw [hS_empty] at h
      have : sInf (∅ : Set ℕ∞) = (⊤ : ℕ∞) := WithTop.sInf_empty
      rw [this] at h
      exact h rfl
    · intro h
      rcases h with ⟨n, hn, hw⟩
      have h_mem : (n : ℕ∞) ∈ S := by
        dsimp [S]
        exact ⟨n, ⟨hn, hw⟩, rfl⟩
      have hS_nonempty : S.Nonempty := ⟨(n : ℕ∞), h_mem⟩
      have h_bddBelow : BddBelow S := by
        refine ⟨0, ?_⟩
        intro y hy
        rcases hy with ⟨m, _, rfl⟩
        simp
      have h_le : sInf S ≤ (n : ℕ∞) := csInf_le h_bddBelow h_mem
      intro h_eq
      rw [h_eq] at h_le
      have h_lt : (n : ℕ∞) < ⊤ := ENat.natCast_lt_top n
      exact not_lt.mpr h_le h_lt

  -- Express the set as a union over t
  have h_set_eq : {x | cut v x ≠ ⊤} = ⋃ t : ℕ, {x | ∃ s ≤ t, walk v x s = root} := by
    ext x
    constructor
    · intro hx
      rcases (h_cut_iff x).mp hx with ⟨n, hn, hw⟩
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      exact ⟨n, le_refl n, hw⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨t, ht⟩
      rcases ht with ⟨s, hs, hw⟩
      apply (h_cut_iff x).mpr
      by_cases hs0 : s = 0
      · subst hs0
        have : walk v x 0 = v := rfl
        rw [this] at hw
        exact absurd hw hv
      · have hs1 : 1 ≤ s := Nat.one_le_of_lt (Nat.pos_of_ne_zero hs0)
        exact ⟨s, hs1, hw⟩

  rw [h_set_eq]

  set A := fun (t : ℕ) => {x | ∃ s ≤ t, walk v x s = root} with hA

  have hA_mono : Monotone A := by
    intro t₁ t₂ h_le x hx
    rcases hx with ⟨s, hs, hw⟩
    exact ⟨s, hs.trans h_le, hw⟩

  have h_measure_union : seqLaw d (⋃ t : ℕ, A t) = ⨆ t : ℕ, seqLaw d (A t) := by
    rw [Monotone.measure_iUnion hA_mono]

  rw [h_measure_union]

  refine iSup_le ?_
  intro t
  exact hitWithin_le t v

/-- From the root the walk returns to the root with probability at most `1 / d`. -/
theorem FrogModel.LemmaR.hitProb_root_le {d : ℕ} [NeZero d] :
    seqLaw d {x | cut root x ≠ ⊤} ≤ (d : ℝ≥0∞)⁻¹ := by
  have key : ∀ (v : Vertex d) (y : ℕ → Step d),
      cut v y ≠ ⊤ ↔ ∃ m, 1 ≤ m ∧ walk v y m = root := by
    intro v y
    constructor
    · intro h
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
      exact ⟨n, walk_cut v y n hn.symm⟩
    · rintro ⟨m, hm, hw⟩
      exact ne_top_of_le_ne_top (ENat.natCast_ne_top m) ((cut_le_iff v y m).2 ⟨m, hm, le_rfl, hw⟩)
  have hset : {x : ℕ → Step d | cut root x ≠ ⊤} =
      {x | (fun (ξ : Step d) (y : ℕ → Step d) => cut [ξ.1] y ≠ ⊤) (x 0) (fun k => x (k + 1))} := by
    ext x
    simp only [Set.mem_ofPred_eq, key]
    constructor
    · rintro ⟨n, hn, hw⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [walk_succ_tail] at hw
      refine ⟨m, ?_, hw⟩
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        simp [walk, step, root] at hw
      · exact h
    · rintro ⟨m, _, hw⟩
      refine ⟨m + 1, by omega, ?_⟩
      rw [walk_succ_tail]
      exact hw
  rw [hset, seqLaw_head_tail (fun (ξ : Step d) (y : ℕ → Step d) => cut [ξ.1] y ≠ ⊤)
    (fun ξ => measurableSet_cut_ne_top _)]
  have hcard : ((Fintype.card (Step d) : ℕ) : ℝ≥0∞) * ((d * (d + 1) : ℕ) : ℝ≥0∞)⁻¹ = 1 := by
    have : Fintype.card (Step d) = d * (d + 1) := by simp [Fintype.card_prod]
    rw [this]
    refine ENNReal.mul_inv_cancel ?_ (ENNReal.natCast_ne_top _)
    exact_mod_cast Nat.mul_ne_zero (NeZero.ne d) (Nat.succ_ne_zero d)
  calc ∑ ξ : Step d, stepLaw d {ξ} * seqLaw d {y | cut [ξ.1] y ≠ ⊤}
      ≤ ∑ _ξ : Step d, ((d * (d + 1) : ℕ) : ℝ≥0∞)⁻¹ * (d : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        rw [stepLaw_singleton]
        gcongr
        simpa using hitProb_le [ξ.1] (by simp [root])
    _ = (d : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hcard, one_mul]
