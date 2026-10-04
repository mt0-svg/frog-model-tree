module

public import FrogModel.LemmaR.Returns

@[expose] public section

/-!
# The recurrence criterion on `T_d`: the all-awake count

`U_n = ∑_{|u| ≤ n} N_u` (`awakeCount_eq_sum`), the `N_u` are independent and there are `d^k`
vertices at depth `k` (`sum_words_pow`), so `E U_n^2 ≤ 6 (n + 1) + 36 (n + 1)^2`
(`lintegral_awakeCount_sq_le`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaR

theorem FrogModel.LemmaR.mem_words {d n : ℕ} (u : Vertex d) : u ∈ words d n ↔ u.length ≤ n := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨k, hk, h⟩
    rcases Finset.mem_image.mp h with ⟨f, _, hf⟩
    have hk_range : k < n + 1 := Finset.mem_range.mp hk
    have hlen : (List.ofFn f).length = k := List.length_ofFn (f := f)
    rw [hf] at hlen
    omega
  · intro hlen
    have hk : u.length < n + 1 := by omega
    apply Finset.mem_biUnion.mpr
    refine ⟨u.length, Finset.mem_range.mpr hk, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨u.get, Finset.mem_univ _, ?_⟩
    exact List.ofFn_get u

/-- `d^k` vertices at depth `k`, so `∑_{|u| ≤ n} d^(-|u|) = n + 1`. -/
theorem FrogModel.LemmaR.sum_words_pow {d : ℕ} [NeZero d] (n : ℕ) :
    ∑ u ∈ words d n, ((d : ℝ≥0∞)⁻¹) ^ u.length = n + 1 := by
  have hd_ne_zero : (d : ℝ≥0∞) ≠ 0 := by
    exact mod_cast NeZero.ne d
  have hd_ne_top : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  have h_inner (k : ℕ) : ∑ u ∈ (Finset.univ : Finset (Fin k → Fin d)).image List.ofFn,
      ((d : ℝ≥0∞)⁻¹) ^ u.length = 1 := by
    rw [Finset.sum_image (fun f _ g _ h => List.ofFn_injective h)]
    simp_rw [List.length_ofFn]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [nsmul_eq_mul, Nat.cast_pow, ← ENNReal.inv_pow]
    exact ENNReal.mul_inv_cancel (ENNReal.pow_ne_zero hd_ne_zero k) (ENNReal.pow_ne_top hd_ne_top)
  have h_disjoint : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint
      (fun k => (Finset.univ : Finset (Fin k → Fin d)).image List.ofFn) := by
    intro k1 hk1 k2 hk2 hne
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨f1, _, hx1'⟩
    rcases Finset.mem_image.mp hx2 with ⟨f2, _, hx2'⟩
    have hlen1 : (List.ofFn f1).length = k1 := List.length_ofFn
    have hlen2 : (List.ofFn f2).length = k2 := List.length_ofFn
    rw [hx1'] at hlen1
    rw [hx2'] at hlen2
    exact hne (hlen1.symm.trans hlen2)
  dsimp [words]
  rw [Finset.sum_biUnion h_disjoint]
  simp [h_inner]

/-- `U_n = ∑_{|u| ≤ n} N_u`. -/
theorem FrogModel.LemmaR.awakeCount_eq_sum {d : ℕ} (n : ℕ) (ω : Sample d) :
    awakeCount n ω = ∑ u ∈ words d n, ((returnCount u (ω u) : ℕ∞) : ℝ≥0∞) := by
  have hset : {p : Vertex d × ℕ | p.1.length ≤ n ∧ 1 ≤ p.2 ∧ paths ω p.1 p.2 = root} =
      ⋃ u ∈ (words d n : Set (Vertex d)),
        ({u} : Set (Vertex d)) ×ˢ {t : ℕ | 1 ≤ t ∧ walk u (ω u) t = root} := by
    ext ⟨u, t⟩
    simp [mem_words, paths, and_left_comm]
  have hdisj : (words d n : Set (Vertex d)).PairwiseDisjoint fun u =>
      ({u} : Set (Vertex d)) ×ˢ {t : ℕ | 1 ≤ t ∧ walk u (ω u) t = root} := by
    intro a _ b _ hab
    exact Set.disjoint_prod.2 (Or.inl (Set.disjoint_singleton.2 hab))
  unfold awakeCount
  rw [hset, (words d n).finite_toSet.encard_biUnion hdisj, finsum_mem_coe_finset]
  change ENat.toENNRealRingHom _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Set.encard_prod, Set.encard_singleton, one_mul]
  rfl

/-- `E U_n^2 ≤ 6 (n + 1) + 36 (n + 1)^2` for `d ≥ 2`. -/
theorem FrogModel.LemmaR.lintegral_awakeCount_sq_le {d : ℕ} [NeZero d] (hd : 2 ≤ d) (n : ℕ) :
    ∫⁻ ω, awakeCount n ω ^ 2 ∂frogMeasure d ≤ 6 * (n + 1) + 36 * (n + 1) ^ 2 := by
  have : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  set X : Vertex d → Sample d → ℝ≥0∞ := fun u ω => ((returnCount u (ω u) : ℕ∞) : ℝ≥0∞)
    with hX
  have hg : ∀ u : Vertex d, Measurable fun x : ℕ → Step d => ((returnCount u x : ℕ∞) : ℝ≥0∞) :=
    fun u => (Measurable.of_discrete (f := fun x : ℕ∞ => (x : ℝ≥0∞))).comp
      (measurable_returnCount u)
  have hXm : ∀ u, Measurable (X u) := fun u => (hg u).comp (measurable_pi_apply u)
  have hind : iIndepFun X (frogMeasure d) :=
    ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : Vertex d => seqLaw d)
      (X := fun u x => ((returnCount u x : ℕ∞) : ℝ≥0∞)) hg
  have hlaw : ∀ (u : Vertex d) (f : (ℕ → Step d) → ℝ≥0∞), Measurable f →
      ∫⁻ ω, f (ω u) ∂frogMeasure d = ∫⁻ x, f x ∂seqLaw d := by
    intro u f hf
    rw [← lintegral_map hf (measurable_pi_apply u)]
    congr 1
    exact Measure.infinitePi_map_eval _ u
  have hX2 : ∀ u, ∫⁻ ω, X u ω ^ 2 ∂frogMeasure d ≤ 6 * ((d : ℝ≥0∞)⁻¹) ^ u.length := by
    intro u
    rw [hlaw u (fun x => ((returnCount u x : ℕ∞) : ℝ≥0∞) ^ 2) ((hg u).pow_const 2)]
    exact lintegral_returnCount_sq_le hd u
  have hX1 : ∀ u, ∫⁻ ω, X u ω ∂frogMeasure d ≤ 6 * ((d : ℝ≥0∞)⁻¹) ^ u.length := by
    intro u
    refine le_trans (lintegral_mono fun ω => ?_) (hX2 u)
    rcases eq_or_ne (returnCount u (ω u)) 0 with h0 | h0
    · simp [hX, h0]
    · have h1 : (1 : ℝ≥0∞) ≤ X u ω := by
        simp only [hX]
        exact_mod_cast Order.one_le_iff_ne_zero.2 h0
      calc X u ω = X u ω * 1 := (mul_one _).symm
        _ ≤ X u ω * X u ω := by gcongr
        _ = X u ω ^ 2 := (sq _).symm
  have hsum : ∑ u ∈ words d n, 6 * ((d : ℝ≥0∞)⁻¹) ^ u.length = 6 * (n + 1) := by
    rw [← Finset.mul_sum, sum_words_pow]
  calc ∫⁻ ω, awakeCount n ω ^ 2 ∂frogMeasure d
      = ∫⁻ ω, (∑ u ∈ words d n, X u ω) ^ 2 ∂frogMeasure d := by
        congr 1
        funext ω
        rw [awakeCount_eq_sum]
    _ ≤ ∑ u ∈ words d n, ∫⁻ ω, X u ω ^ 2 ∂frogMeasure d +
          (∑ u ∈ words d n, ∫⁻ ω, X u ω ∂frogMeasure d) ^ 2 :=
        lintegral_sq_sum_le _ _ X hXm hind
    _ ≤ 6 * (n + 1) + (6 * (n + 1)) ^ 2 := by
        gcongr
        · rw [← hsum]
          exact Finset.sum_le_sum fun u _ => hX2 u
        · rw [← hsum]
          exact Finset.sum_le_sum fun u _ => hX1 u
    _ = 6 * (n + 1) + 36 * (n + 1) ^ 2 := by ring
