module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# The law of the direction counts (multinomial counts, Wald's identity)

The directions at a vertex are i.i.d. uniform on `Fin 4`; the counts `k_a(n)` at time `n` have the
law `Mult(n; 1/4, 1/4, 1/4, 1/4)`. Proved by induction on `n`: the present direction `D n` is
independent of the past, and the multinomial satisfies `Mult(n + 1; k) = 1/4 ∑_b Mult(n; k - e_b)`.
The same independence gives Wald's identity `E k_a(τ) = E τ / 4` for a bounded stopping time `τ`
of the directions and of independent data.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

theorem dirCount_congr {n : ℕ} {D D' : ℕ → Fin 4} (h : ∀ i < n, D i = D' i) (a : Fin 4) :
    dirCount D a n = dirCount D' a n := by
  unfold dirCount
  congr 1
  exact Finset.filter_congr fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem dirCount_succ (D : ℕ → Fin 4) (a : Fin 4) (n : ℕ) :
    dirCount D a (n + 1) = dirCount D a n + if D n = a then 1 else 0 := by
  unfold dirCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem dirCount_zero (D : ℕ → Fin 4) (a : Fin 4) : dirCount D a 0 = 0 := by
  simp [dirCount]

/-- `k! / k = (k - 1)!` for `k ≥ 1`, in `ℝ`. -/
theorem factorial_pred_real {k : ℕ} (hk : 1 ≤ k) :
    ((k - 1).factorial : ℝ) = k.factorial / k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

/-- The recursion of the multinomial `Mult(n + 1; k) = 1/4 ∑_b Mult(n; k - e_b)`. -/
theorem mult4_succ (n k0 k1 k2 k3 : ℕ) (h : k0 + k1 + k2 + k3 = n + 1) :
    mult4 (n + 1) k0 k1 k2 k3 = 1 / 4 * ((if 1 ≤ k0 then mult4 n (k0 - 1) k1 k2 k3 else 0) +
      (if 1 ≤ k1 then mult4 n k0 (k1 - 1) k2 k3 else 0) +
      (if 1 ≤ k2 then mult4 n k0 k1 (k2 - 1) k3 else 0) +
      (if 1 ≤ k3 then mult4 n k0 k1 k2 (k3 - 1) else 0)) := by
  set C : ℝ := (n.factorial : ℝ) /
    ((k0.factorial : ℝ) * k1.factorial * k2.factorial * k3.factorial) / 4 ^ n with hC
  have hf : ∀ k : ℕ, (k.factorial : ℝ) ≠ 0 := fun k => by positivity
  have hk : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≠ 0 := fun k hk => Nat.cast_ne_zero.2 (by omega)
  have t0 : (if 1 ≤ k0 then mult4 n (k0 - 1) k1 k2 k3 else 0) = k0 * C := by
    split_ifs with h0
    · unfold mult4
      rw [factorial_pred_real h0, hC]
      have := hk k0 h0
      have := hf k0; have := hf k1; have := hf k2; have := hf k3
      field_simp
    · simp [show k0 = 0 by omega]
  have t1 : (if 1 ≤ k1 then mult4 n k0 (k1 - 1) k2 k3 else 0) = k1 * C := by
    split_ifs with h0
    · unfold mult4
      rw [factorial_pred_real h0, hC]
      have := hk k1 h0
      have := hf k0; have := hf k1; have := hf k2; have := hf k3
      field_simp
    · simp [show k1 = 0 by omega]
  have t2 : (if 1 ≤ k2 then mult4 n k0 k1 (k2 - 1) k3 else 0) = k2 * C := by
    split_ifs with h0
    · unfold mult4
      rw [factorial_pred_real h0, hC]
      have := hk k2 h0
      have := hf k0; have := hf k1; have := hf k2; have := hf k3
      field_simp
    · simp [show k2 = 0 by omega]
  have t3 : (if 1 ≤ k3 then mult4 n k0 k1 k2 (k3 - 1) else 0) = k3 * C := by
    split_ifs with h0
    · unfold mult4
      rw [factorial_pred_real h0, hC]
      have := hk k3 h0
      have := hf k0; have := hf k1; have := hf k2; have := hf k3
      field_simp
    · simp [show k3 = 0 by omega]
  rw [t0, t1, t2, t3]
  have hs : (k0 : ℝ) + k1 + k2 + k3 = n + 1 := by exact_mod_cast h
  have hc : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  unfold mult4
  rw [hc, hC, pow_succ]
  have := hf k0; have := hf k1; have := hf k2; have := hf k3
  rw [← hs]
  field_simp

/-- The coordinates of `dirMeasure` are independent. -/
theorem iIndepFun_dir : iIndepFun (fun i (D : ℕ → Fin 4) => D i) dirMeasure :=
  iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

/-- The past `D 0, ..., D (n - 1)` and the present `D n` are independent. -/
theorem indepFun_dir_past (n : ℕ) :
    IndepFun (fun D (i : Finset.range n) => D i) (fun D : ℕ → Fin 4 => D n) dirMeasure := by
  have h := iIndepFun_dir.indepFun_finset (Finset.range n) {n} (by simp)
    (fun i => measurable_pi_apply i)
  exact h.comp (φ := id) (ψ := fun w : ({n} : Finset ℕ) → Fin 4 => w ⟨n, by simp⟩)
    measurable_id (measurable_pi_apply _)

theorem dirMeasure_eval (n : ℕ) (b : Fin 4) : dirMeasure {D | D n = b} = 4⁻¹ := by
  have h : dirMeasure.map (fun D : ℕ → Fin 4 => D n) = uniformOn Set.univ := by
    unfold dirMeasure
    exact Measure.infinitePi_map_eval _ n
  have h2 := congrArg (fun ν => ν {b}) h
  rw [Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton b)] at h2
  rw [show {D : ℕ → Fin 4 | D n = b} = (fun D : ℕ → Fin 4 => D n) ⁻¹' {b} from rfl, h2,
    uniformOn_univ]
  simp

/-- The event `{the counts at time n are k}`, as a preimage of the past. -/
theorem counts_eq_preimage (n : ℕ) (k : Fin 4 → ℕ) :
    {D : ℕ → Fin 4 | ∀ a, dirCount D a n = k a} =
      (fun D (i : Finset.range n) => D i) ⁻¹'
        {w | ∀ a, dirCount (fun i => if h : i ∈ Finset.range n then w ⟨i, h⟩ else 0) a n = k a} := by
  ext D
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  refine forall_congr' fun a => ?_
  rw [dirCount_congr (D' := fun i => if h : i ∈ Finset.range n then D i else 0)
    (fun i hi => by simp [Finset.mem_range.2 hi])]

theorem measurableSet_counts (n : ℕ) (k : Fin 4 → ℕ) :
    MeasurableSet {D : ℕ → Fin 4 | ∀ a, dirCount D a n = k a} := by
  rw [counts_eq_preimage]
  exact (measurable_pi_iff.mpr fun i => measurable_pi_apply _) (Set.to_countable _).measurableSet

theorem counts_succ_eq (n : ℕ) (k : Fin 4 → ℕ) :
    {D : ℕ → Fin 4 | ∀ a, dirCount D a (n + 1) = k a} =
      ⋃ b ∈ Finset.univ.filter (fun b => 1 ≤ k b),
        ({D : ℕ → Fin 4 | ∀ a, dirCount D a n = Function.update k b (k b - 1) a} ∩
          {D | D n = b}) := by
  ext D
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_filter,
    Finset.mem_univ, true_and, exists_prop, dirCount_succ]
  constructor
  · intro h
    refine ⟨D n, ?_, fun a => ?_, rfl⟩
    · have := h (D n); simp at this; omega
    · by_cases ha : a = D n
      · subst ha; have := h (D n); simp at this; simp; omega
      · have := h a; rw [ite_eq_right (Ne.symm ha)] at this
        rw [Function.update_of_ne ha]; omega
  · rintro ⟨b, hb, h, hn⟩ a
    have := h a
    by_cases ha : a = b
    · subst ha; rw [Function.update_self] at this; rw [ite_eq_left hn]; omega
    · rw [Function.update_of_ne ha] at this
      rw [ite_eq_right (by rw [hn]; exact Ne.symm ha)]; omega

/-- **The multinomial law of the direction counts.** -/
theorem dirMeasure_counts (n : ℕ) (k : Fin 4 → ℕ) (hk : ∑ a, k a = n) :
    (dirMeasure {D | ∀ a, dirCount D a n = k a}).toReal = mult4 n (k 0) (k 1) (k 2) (k 3) := by
  induction n generalizing k with
  | zero =>
    have hk0 : ∀ a, k a = 0 := fun a => by
      have := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      omega
    have : {D : ℕ → Fin 4 | ∀ a, dirCount D a 0 = k a} = Set.univ := by
      ext D; simp [dirCount_zero, hk0]
    rw [this, hk0 0, hk0 1, hk0 2, hk0 3]
    simp [mult4]
  | succ n ih =>
    rw [counts_succ_eq, measure_biUnion_finset]
    · rw [ENNReal.toReal_sum (fun b _ => measure_ne_top _ _)]
      have hterm : ∀ b ∈ Finset.univ.filter (fun b => 1 ≤ k b),
          (dirMeasure ({D : ℕ → Fin 4 | ∀ a, dirCount D a n = Function.update k b (k b - 1) a} ∩
            {D | D n = b})).toReal =
          1 / 4 * mult4 n (Function.update k b (k b - 1) 0) (Function.update k b (k b - 1) 1)
            (Function.update k b (k b - 1) 2) (Function.update k b (k b - 1) 3) := by
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hsum : ∑ a, Function.update k b (k b - 1) a = n := by
          rw [Finset.sum_update_of_mem (Finset.mem_univ b), Finset.sdiff_singleton_eq_erase]
          have := Finset.add_sum_erase Finset.univ k (Finset.mem_univ b)
          omega
        rw [counts_eq_preimage n, show {D : ℕ → Fin 4 | D n = b} = (fun D : ℕ → Fin 4 => D n) ⁻¹' {b} from rfl,
          (indepFun_iff_measure_inter_preimage_eq_mul.1 (indepFun_dir_past n)) _ _
            (Set.to_countable _).measurableSet (measurableSet_singleton b)]
        rw [show (fun D : ℕ → Fin 4 => D n) ⁻¹' {b} = {D | D n = b} from rfl, dirMeasure_eval,
          ← counts_eq_preimage, ENNReal.toReal_mul, ih _ hsum]
        simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_filter, Fin.sum_univ_four]
      rw [mult4_succ n (k 0) (k 1) (k 2) (k 3) (by rw [← hk, Fin.sum_univ_four])]
      simp only [Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true,
        Function.update_of_ne]
      split_ifs <;> ring
    · intro b _ b' _ hbb'
      exact Set.disjoint_left.2 fun D h1 h2 => hbb' (h1.2.symm.trans h2.2)
    · exact fun b _ => (measurableSet_counts n _).inter
        (show MeasurableSet ((fun D : ℕ → Fin 4 => D n) ⁻¹' {b}) from
          (measurable_pi_apply n) (measurableSet_singleton b))

/-- A count below `n` as a sum of indicators. -/
theorem dirCount_eq_sum (D : ℕ → Fin 4) (a : Fin 4) (t n : ℕ) (ht : t ≤ n) :
    (dirCount D a t : ℝ) = ∑ i ∈ Finset.range n, if i < t ∧ D i = a then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  unfold dirCount
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem natCast_eq_sum (t n : ℕ) (ht : t ≤ n) :
    (t : ℝ) = ∑ i ∈ Finset.range n, if i < t then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [show (Finset.range n).filter (fun i => i < t) = Finset.range t by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  simp

/-- The direction at time `i` is independent of an event of the past and of independent data. -/
theorem prob_past_dir {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (i : ℕ) (E : Set (X × (ℕ → Fin 4))) (hE : MeasurableSet E)
    (hpast : ∀ x (D D' : ℕ → Fin 4), (∀ l < i, D l = D' l) → ((x, D) ∈ E ↔ (x, D') ∈ E))
    (a : Fin 4) :
    (ν.prod dirMeasure) (E ∩ {z | z.2 i = a}) = 4⁻¹ * (ν.prod dirMeasure) E := by
  have hEa : MeasurableSet (E ∩ {z : X × (ℕ → Fin 4) | z.2 i = a}) :=
    hE.inter ((show Measurable fun z : X × (ℕ → Fin 4) => z.2 i from
      (measurable_pi_apply i).comp measurable_snd) (measurableSet_singleton a))
  rw [Measure.prod_apply hEa, Measure.prod_apply hE, ← lintegral_const_mul _
    (measurable_measure_prodMk_left hE)]
  refine lintegral_congr fun x => ?_
  set ext : (Finset.range i → Fin 4) → ℕ → Fin 4 := fun w l =>
    if h : l ∈ Finset.range i then w ⟨l, h⟩ else 0
  set S : Set (Finset.range i → Fin 4) := {w | (x, ext w) ∈ E}
  have hslice : Prod.mk x ⁻¹' E = (fun D (l : Finset.range i) => D l) ⁻¹' S := by
    ext D
    simp only [Set.mem_preimage, S, Set.mem_ofPred_eq]
    exact hpast x D _ fun l hl => by simp [ext, hl]
  have hslice' : Prod.mk x ⁻¹' (E ∩ {z : X × (ℕ → Fin 4) | z.2 i = a}) =
      (fun D (l : Finset.range i) => D l) ⁻¹' S ∩ (fun D : ℕ → Fin 4 => D i) ⁻¹' {a} := by
    rw [Set.preimage_inter, hslice]
    rfl
  rw [hslice', hslice, (indepFun_iff_measure_inter_preimage_eq_mul.1 (indepFun_dir_past i)) _ _
    (Set.to_countable _).measurableSet (measurableSet_singleton a),
    show (fun D : ℕ → Fin 4 => D i) ⁻¹' {a} = {D | D i = a} from rfl, dirMeasure_eval, mul_comm]

/-- **Wald's identity** for the direction counts. -/
theorem wald_dirCount {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (τ : X × (ℕ → Fin 4) → ℕ) (hτ : Measurable τ)
    (hstop : ∀ (i : ℕ) (x : X) (D D' : ℕ → Fin 4), (∀ l < i, D l = D' l) →
      (i < τ (x, D) ↔ i < τ (x, D')))
    (n : ℕ) (hn : ∀ z, τ z ≤ n) (a : Fin 4) :
    ∫ z, (dirCount z.2 a (τ z) : ℝ) ∂(ν.prod dirMeasure) =
      (1 / 4) * ∫ z, (τ z : ℝ) ∂(ν.prod dirMeasure) := by
  have hlt : ∀ i, MeasurableSet {z : X × (ℕ → Fin 4) | i < τ z} := fun i =>
    hτ (MeasurableSet.of_discrete (s := {k : ℕ | i < k}))
  have hdir : ∀ i, MeasurableSet {z : X × (ℕ → Fin 4) | z.2 i = a} := fun i =>
    (show Measurable fun z : X × (ℕ → Fin 4) => z.2 i from
      (measurable_pi_apply i).comp measurable_snd) (measurableSet_singleton a)
  have h1 : ∀ z : X × (ℕ → Fin 4), (dirCount z.2 a (τ z) : ℝ) = ∑ i ∈ Finset.range n,
      ({z : X × (ℕ → Fin 4) | i < τ z} ∩ {z | z.2 i = a}).indicator 1 z := by
    intro z
    rw [dirCount_eq_sum z.2 a (τ z) n (hn z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq, Pi.one_apply]
  have h2 : ∀ z : X × (ℕ → Fin 4), (τ z : ℝ) = ∑ i ∈ Finset.range n,
      {z : X × (ℕ → Fin 4) | i < τ z}.indicator 1 z := by
    intro z
    rw [natCast_eq_sum (τ z) n (hn z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  have hi : ∀ s, MeasurableSet s →
      Integrable (s.indicator (1 : X × (ℕ → Fin 4) → ℝ)) (ν.prod dirMeasure) := fun s hs =>
    (integrable_const (1 : ℝ)).indicator hs
  simp_rw [h1, h2]
  rw [integral_finsetSum _ fun i _ => hi _ ((hlt i).inter (hdir i)),
    integral_finsetSum _ fun i _ => hi _ (hlt i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator_one ((hlt i).inter (hdir i)), integral_indicator_one (hlt i),
    measureReal_def, measureReal_def,
    prob_past_dir ν i _ (hlt i) (fun x D D' h => hstop i x D D' h) a, ENNReal.toReal_mul]
  norm_num

/-- The count of one direction among the first `n` is `Bin(n, 1/4)`. -/
theorem dirMeasure_dirCount (n i : ℕ) (a : Fin 4) :
    (dirMeasure {D | dirCount D a n = i}).toReal = binPmf n (1 / 4) i := by
  by_cases hle : i ≤ n
  · -- i ≤ n case: use cylinder decomposition
    let μ := fun (_ : ℕ) => (uniformOn (Set.univ : Set (Fin 4)))
    have h_dirMeasure_eq : dirMeasure = Measure.infinitePi μ := rfl

    -- The set of subsets of {0,...,n-1} of size i
    let S := (Finset.range n).powersetCard i
    have hS_card : S.card = (Finset.range n).card.choose i := by
      rw [Finset.card_powersetCard]

    -- Compute (μ j) {a} and (μ j) (univ \ {a})
    have h_mu_a (j : ℕ) : (μ j) ({a} : Set (Fin 4)) = (1/4 : ENNReal) := by
      dsimp [μ]
      rw [uniformOn_univ]
      have hcard : Fintype.card (Fin 4) = 4 := by decide
      rw [hcard]
      have hcount : Measure.count ({a} : Set (Fin 4)) = (1 : ENNReal) := by
        have hfin : Set.Finite ({a} : Set (Fin 4)) := Set.finite_singleton _
        rw [Measure.count_apply_finite _ hfin]
        have htoFinset : hfin.toFinset = ({a} : Finset (Fin 4)) := by
          ext x; simp
        rw [htoFinset]
        simp
      rw [hcount]
      norm_num

    have h_mu_not_a (j : ℕ) : (μ j) ((Set.univ : Set (Fin 4)) \ {a}) = (3/4 : ENNReal) := by
      dsimp [μ]
      rw [uniformOn_univ]
      have hcard : Fintype.card (Fin 4) = 4 := by decide
      rw [hcard]
      have hcount : Measure.count ((Set.univ : Set (Fin 4)) \ {a}) = (3 : ENNReal) := by
        have hfin : Set.Finite ((Set.univ : Set (Fin 4)) \ {a}) := Set.toFinite _
        rw [Measure.count_apply_finite _ hfin]
        have htoFinset : hfin.toFinset = (Finset.univ : Finset (Fin 4)).erase a := by
          ext x; simp
        rw [htoFinset]
        simp
      rw [hcount]
      norm_num

    -- Define the family of cylinders
    let C : Finset ℕ → Set (ℕ → Fin 4) := fun s =>
      (Finset.range n : Set ℕ).pi (fun j =>
        if j ∈ s then ({a} : Set (Fin 4)) else ((Set.univ : Set (Fin 4)) \ {a}))

    -- Compute the measure of a single cylinder
    have h_cyl_measure (s : Finset ℕ) (hs : s ∈ S) :
        (dirMeasure (C s)).toReal = ((1 : ℝ) / 4) ^ i * ((3 : ℝ) / 4) ^ (n - i) := by
      rw [h_dirMeasure_eq]
      let t : ℕ → Set (Fin 4) := fun j' =>
        if j' ∈ s then ({a} : Set (Fin 4)) else ((Set.univ : Set (Fin 4)) \ {a})
      have hmeas : ∀ j ∈ Finset.range n, MeasurableSet (t j) := by
        intro j hj
        dsimp [t]
        by_cases hj_s : j ∈ s
        · rw [ite_eq_left hj_s]
          exact MeasurableSet.singleton _
        · rw [ite_eq_right hj_s]
          apply MeasurableSet.diff MeasurableSet.univ (MeasurableSet.singleton _)
      rw [Measure.infinitePi_pi μ hmeas]
      -- Now compute the product
      have hs_sub : s ⊆ Finset.range n := by
        have hmem := Finset.mem_powersetCard.mp hs
        exact hmem.1
      have h_prod_sdiff := Finset.prod_sdiff hs_sub (f := fun j => (μ j) (t j))

      have h_prod_s : (∏ j ∈ s, (μ j) (t j)) = (∏ j ∈ s, (1/4 : ENNReal)) := by
        apply Finset.prod_congr rfl
        intro j hj
        dsimp [t]
        rw [ite_eq_left hj, h_mu_a j]

      have h_prod_sdiff' : (∏ j ∈ (Finset.range n) \ s, (μ j) (t j)) =
          (∏ j ∈ (Finset.range n) \ s, (3/4 : ENNReal)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hj_not_mem : j ∉ s := (Finset.mem_sdiff.mp hj).2
        dsimp [t]
        rw [ite_eq_right hj_not_mem, h_mu_not_a j]

      rw [← h_prod_sdiff, h_prod_s, h_prod_sdiff']
      rw [Finset.prod_const, Finset.prod_const]
      have h_card_sdiff : ((Finset.range n) \ s).card = n - i := by
        have hmem := Finset.mem_powersetCard.mp hs
        have hs_card : s.card = i := hmem.2
        have h_total := Finset.card_sdiff_add_card_eq_card hs_sub
        rw [hs_card] at h_total
        have h_range_card : (Finset.range n).card = n := by simp
        rw [h_range_card] at h_total
        omega
      rw [h_card_sdiff]
      have hmem := Finset.mem_powersetCard.mp hs
      have hs_card' : s.card = i := hmem.2
      rw [hs_card']
      simp [ENNReal.toReal_mul, ENNReal.toReal_pow]
      ring

    -- Show that the cylinders are pairwise disjoint
    have h_disjoint : (S : Set (Finset ℕ)).PairwiseDisjoint C := by
      intro s₁ hs₁ s₂ hs₂ hne
      have hs₁_mem := Finset.mem_powersetCard.mp hs₁
      have hs₂_mem := Finset.mem_powersetCard.mp hs₂
      have hs₁_sub : s₁ ⊆ Finset.range n := hs₁_mem.1
      have hs₂_sub : s₂ ⊆ Finset.range n := hs₂_mem.1
      -- Find j that distinguishes s₁ and s₂
      have h_diff : ∃ j, (j ∈ s₁ ∧ j ∉ s₂) ∨ (j ∉ s₁ ∧ j ∈ s₂) := by
        have h_ext := (Finset.ext_iff.not.mp hne)
        push Not at h_ext
        exact h_ext
      rcases h_diff with ⟨j, hj⟩
      rcases hj with (⟨hj_s1, hj_s2⟩ | ⟨hj_s1, hj_s2⟩)
      · -- j ∈ s₁, j ∉ s₂
        have hj_range : j ∈ Finset.range n := hs₁_sub hj_s1
        apply Set.disjoint_iff_inter_eq_empty.mpr
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hne'
        rcases hne' with ⟨D, hD⟩
        rcases hD with ⟨hD1, hD2⟩
        have hD1_j : D j ∈ ({a} : Set (Fin 4)) := by
          have h_mem : j ∈ (Finset.range n : Set ℕ) := by simpa using hj_range
          have h_all := Set.mem_pi.mp hD1
          have := h_all j h_mem
          simp [hj_s1] at this
          exact this
        have hD2_j : D j ∈ ((Set.univ : Set (Fin 4)) \ {a}) := by
          have h_mem : j ∈ (Finset.range n : Set ℕ) := by simpa using hj_range
          have h_all := Set.mem_pi.mp hD2
          have := h_all j h_mem
          simpa [hj_s2] using this
        have h_contra : D j ∈ ({a} : Set (Fin 4)) ∩ ((Set.univ : Set (Fin 4)) \ {a}) :=
          Set.mem_inter hD1_j hD2_j
        rcases h_contra with ⟨h_eq, h_ne⟩
        have h_eq_a : D j = a := by simpa using h_eq
        have h_ne_a : D j ≠ a := by simpa using h_ne
        exact h_ne_a h_eq_a
      · -- j ∉ s₁, j ∈ s₂
        have hj_range : j ∈ Finset.range n := hs₂_sub hj_s2
        apply Set.disjoint_iff_inter_eq_empty.mpr
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hne'
        rcases hne' with ⟨D, hD⟩
        rcases hD with ⟨hD1, hD2⟩
        have hD2_j : D j ∈ ({a} : Set (Fin 4)) := by
          have h_mem : j ∈ (Finset.range n : Set ℕ) := by simpa using hj_range
          have h_all := Set.mem_pi.mp hD2
          have := h_all j h_mem
          simp [hj_s2] at this
          exact this
        have hD1_j : D j ∈ ((Set.univ : Set (Fin 4)) \ {a}) := by
          have h_mem : j ∈ (Finset.range n : Set ℕ) := by simpa using hj_range
          have h_all := Set.mem_pi.mp hD1
          have := h_all j h_mem
          simpa [hj_s1] using this
        have h_contra : D j ∈ ({a} : Set (Fin 4)) ∩ ((Set.univ : Set (Fin 4)) \ {a}) :=
          Set.mem_inter hD2_j hD1_j
        rcases h_contra with ⟨h_eq, h_ne⟩
        have h_eq_a : D j = a := by simpa using h_eq
        have h_ne_a : D j ≠ a := by simpa using h_ne
        exact h_ne_a h_eq_a

    -- Show that each cylinder is measurable
    have h_measurable : ∀ s ∈ S, MeasurableSet (C s) := by
      intro s hs
      dsimp [C]
      apply MeasurableSet.pi
      · exact Set.to_countable _
      intro j hj
      by_cases hj_s : j ∈ s
      · rw [ite_eq_left hj_s]
        exact MeasurableSet.singleton _
      · rw [ite_eq_right hj_s]
        apply MeasurableSet.diff MeasurableSet.univ (MeasurableSet.singleton _)

    -- Show that the union of cylinders equals the set we want
    have h_union : ⋃ s ∈ S, C s = {D | dirCount D a n = i} := by
      ext D
      constructor
      · intro h
        rw [Set.mem_iUnion₂] at h
        rcases h with ⟨s, hs, hD⟩
        dsimp [C] at hD
        have hs_mem := Finset.mem_powersetCard.mp hs
        have hs_sub : s ⊆ Finset.range n := hs_mem.1
        have hs_card : s.card = i := hs_mem.2
        dsimp [dirCount]
        have h_filter_eq : (Finset.range n).filter (fun j => D j = a) = s := by
          ext j
          constructor
          · intro hj
            rw [Finset.mem_filter] at hj
            have hj_range : j ∈ Finset.range n := hj.1
            have hj_eq_a : D j = a := hj.2
            have h_pi := hD j hj_range
            by_cases hj_s : j ∈ s
            · exact hj_s
            · simp [hj_s] at h_pi
              exact absurd hj_eq_a h_pi
          · intro hj
            have hj_range : j ∈ Finset.range n := hs_sub hj
            have h_pi := hD j hj_range
            simp [hj] at h_pi
            exact Finset.mem_filter.mpr ⟨hj_range, h_pi⟩
        rw [h_filter_eq, hs_card]
      · intro h
        have h_count : dirCount D a n = i := h
        let s := (Finset.range n).filter (fun j => D j = a)
        have hs_card : s.card = i := by
          simpa [s, dirCount] using h_count
        have hs_mem : s ∈ S := by
          apply Finset.mem_powersetCard.mpr
          constructor
          · exact Finset.filter_subset _ _
          · exact hs_card
        apply Set.mem_biUnion hs_mem
        dsimp [C]
        apply Set.mem_pi.mpr
        intro j hj
        have hj_range : j ∈ Finset.range n := by simpa using hj
        by_cases hj_s : j ∈ s
        · rw [ite_eq_left hj_s]
          have hD_eq_a : D j = a := by
            have : j ∈ (Finset.range n).filter (fun k => D k = a) := hj_s
            rw [Finset.mem_filter] at this
            exact this.2
          rw [hD_eq_a]
          exact Set.mem_singleton _
        · rw [ite_eq_right hj_s]
          have hD_ne_a : D j ≠ a := by
            intro h_eq
            apply hj_s
            apply Finset.mem_filter.mpr
            exact ⟨hj_range, h_eq⟩
          exact ⟨Set.mem_univ _, hD_ne_a⟩

    -- Now apply measure_biUnion_finset
    have h_fin : ∀ s ∈ S, dirMeasure (C s) ≠ ∞ := by
      intro s hs
      have h_prob : IsFiniteMeasure dirMeasure := by
        dsimp [dirMeasure]
        infer_instance
      exact measure_ne_top dirMeasure (C s)

    rw [← h_union]
    have h_measure_eq := measure_biUnion_finset (μ := dirMeasure) h_disjoint h_measurable
    -- h_measure_eq : dirMeasure (⋃ s ∈ S, C s) = ∑ p ∈ S, dirMeasure (C p)
    rw [h_measure_eq]
    rw [ENNReal.toReal_sum h_fin]
    -- Now sum the measures
    calc
      (∑ a ∈ S, (dirMeasure (C a)).toReal) = ∑ a ∈ S, ((1 : ℝ) / 4) ^ i * ((3 : ℝ) / 4) ^ (n - i) := by
        refine Finset.sum_congr rfl (fun s hs => ?_)
        rw [h_cyl_measure s hs]
      _ = binPmf n (1 / 4) i := by
        rw [Finset.sum_const]
        dsimp [S]
        rw [Finset.card_powersetCard, Finset.card_range]
        dsimp [binPmf]
        ring
  · -- i > n case: both sides are zero
    have h_choose_zero : n.choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h_set_empty : {D : ℕ → Fin 4 | dirCount D a n = i} = (∅ : Set (ℕ → Fin 4)) := by
      ext D; constructor
      · intro h
        have h_eq : dirCount D a n = i := h
        have h_count_le : dirCount D a n ≤ n := by
          dsimp [dirCount]
          have : ((Finset.range n).filter fun j => D j = a).card ≤ (Finset.range n).card :=
            Finset.card_filter_le (Finset.range n) (fun j => D j = a)
          simpa [Finset.card_range] using this
        rw [h_eq] at h_count_le
        omega
      · intro h; exfalso; simp at h
    simp [binPmf, h_choose_zero, h_set_empty, dirMeasure]

/-- `P(k_a(n) < J) = P(Bin(n, 1/4) < J)`. -/
theorem dirMeasure_dirCount_lt (n J : ℕ) (a : Fin 4) :
    (dirMeasure {D | dirCount D a n < J}).toReal = binLt n (1 / 4) J := by
  have h_union : {D : ℕ → Fin 4 | dirCount D a n < J} = ⋃ i ∈ Finset.range J, {D | dirCount D a n = i} := by
    ext D; constructor
    · intro h
      have hlt : dirCount D a n < J := h
      have : ∃ i, i < J ∧ dirCount D a n = i := by
        refine ⟨dirCount D a n, hlt, rfl⟩
      rcases this with ⟨i, hi, heq⟩
      refine Set.mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
      exact heq
    · intro h
      rcases Set.mem_iUnion₂.mp h with ⟨i, hi, heq⟩
      have hi' : i < J := Finset.mem_range.mp hi
      have heq' : dirCount D a n = i := heq
      show dirCount D a n < J
      rw [heq']
      exact hi'
  have h_disjoint : Set.PairwiseDisjoint ((Finset.range J : Set ℕ)) (fun i => {D : ℕ → Fin 4 | dirCount D a n = i}) := by
    intro i hi j hj hne
    apply Set.disjoint_left.mpr
    intro D hDi hDj
    have hi_eq : dirCount D a n = i := hDi
    have hj_eq : dirCount D a n = j := hDj
    have : i = j := by rw [← hi_eq, hj_eq]
    exact hne this
  have h_meas_fun : Measurable (fun (D : ℕ → Fin 4) => dirCount D a n) := by
    have h_eq : (fun (D : ℕ → Fin 4) => dirCount D a n) = fun D =>
      ∑ j ∈ Finset.range n, if D j = a then (1 : ℕ) else 0 := by
      ext D
      rw [dirCount]
      simp only [Finset.card_filter]
    rw [h_eq]
    refine Finset.measurable_sum _ (fun j hj => ?_)
    have h_set : MeasurableSet {D : ℕ → Fin 4 | D j = a} := by
      have : {D : ℕ → Fin 4 | D j = a} = Set.pi ({j} : Set ℕ) (fun _ : ℕ => {a}) := by
        ext D; simp
      rw [this]
      refine MeasurableSet.pi (Set.countable_singleton j) (fun i hi => ?_)
      exact measurableSet_singleton a
    refine Measurable.ite h_set (measurable_const) (measurable_const)
  have h_meas_set (i : ℕ) : MeasurableSet ({D : ℕ → Fin 4 | dirCount D a n = i} : Set (ℕ → Fin 4)) := by
    have : ({D : ℕ → Fin 4 | dirCount D a n = i} : Set (ℕ → Fin 4)) = (fun (D : ℕ → Fin 4) => dirCount D a n) ⁻¹' {i} := by
      ext D; simp
    rw [this]
    exact h_meas_fun (measurableSet_singleton i)
  have h_fin (i : ℕ) : dirMeasure {D : ℕ → Fin 4 | dirCount D a n = i} ≠ ∞ := by
    have : IsProbabilityMeasure dirMeasure := by
      unfold dirMeasure
      infer_instance
    have h_lt : dirMeasure {D : ℕ → Fin 4 | dirCount D a n = i} < ∞ :=
      measure_lt_top dirMeasure {D : ℕ → Fin 4 | dirCount D a n = i}
    exact ne_of_lt h_lt
  calc
    (dirMeasure {D | dirCount D a n < J}).toReal
        = (dirMeasure (⋃ i ∈ Finset.range J, {D | dirCount D a n = i})).toReal := by
          rw [h_union]
    _ = (∑ i ∈ Finset.range J, dirMeasure {D | dirCount D a n = i}).toReal := by
      rw [MeasureTheory.measure_biUnion_finset h_disjoint (fun i hi => h_meas_set i)]
    _ = ∑ i ∈ Finset.range J, (dirMeasure {D | dirCount D a n = i}).toReal := by
      refine ENNReal.toReal_sum (fun i hi => ?_)
      exact h_fin i
    _ = ∑ i ∈ Finset.range J, binPmf n (1 / 4) i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [dirMeasure_dirCount]
    _ = binLt n (1 / 4) J := rfl

end FrogModel.D3.Iface
