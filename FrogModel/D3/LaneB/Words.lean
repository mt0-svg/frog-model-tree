module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# The words of length at most `m`, and independence of coordinate events

`wordsLe m` lists the vertices of depth at most `m` of the 3-ary tree (`Vertex 3 = List (Fin 3)`);
depth `i` holds `3^i` of them. `iIndepSet_infinitePi_preimage`: events reading one coordinate each
of a product measure are independent.
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.D3.Iface

/-- The words of length at most `m` over `Fin 3`. -/
def wordsLe (m : ℕ) : Finset (List (Fin 3)) :=
  (Finset.range (m + 1)).biUnion fun i => (Finset.univ : Finset (Fin i → Fin 3)).image List.ofFn

/-- Membership in `wordsLe`. -/
theorem mem_wordsLe (m : ℕ) (v : List (Fin 3)) : v ∈ wordsLe m ↔ v.length ≤ m := by
  simp only [wordsLe, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, hi, f, rfl⟩
    simp only [List.length_ofFn]
    omega
  · intro h
    exact ⟨v.length, by omega, v.get, List.ofFn_get v⟩

/-- A sum over `wordsLe m` of a function of the length: depth `i` holds `3^i` words. -/
theorem sum_wordsLe_eq {M : Type*} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    ∑ v ∈ wordsLe m, g v.length = ∑ i ∈ Finset.range (m + 1), 3 ^ i • g i := by
  rw [wordsLe, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_image (fun f _ g _ h => List.ofFn_injective h)]
    simp [Finset.card_univ]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv hv'
    obtain ⟨f, rfl⟩ := hv
    obtain ⟨f', hf'⟩ := hv'
    have := congrArg List.length hf'
    simp at this
    exact hij this.symm

/-- `|wordsLe m| = (3^(m+1) - 1)/2`. -/
theorem card_wordsLe (m : ℕ) : (wordsLe m).card = (3 ^ (m + 1) - 1) / 2 := by
  have h := sum_wordsLe_eq m (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [h]
  clear h
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 ≤ 3 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 3 ^ (n + 1 + 1) = 3 * 3 ^ (n + 1) := by ring
    rw [h2]
    omega

/-- `∑ over the words v of length ≤ m of 3^-(|v| + 1) = (m + 1)/3`. -/
theorem sum_wordsLe (m : ℕ) :
    ∑ v ∈ wordsLe m, (3⁻¹ : ℝ) ^ (v.length + 1) = ((m : ℝ) + 1) / 3 := by
  rw [sum_wordsLe_eq m (fun i => (3⁻¹ : ℝ) ^ (i + 1))]
  have : ∀ i : ℕ, (3 ^ i • (3⁻¹ : ℝ) ^ (i + 1)) = 1 / 3 := by
    intro i
    rw [nsmul_eq_mul, pow_succ]
    push_cast
    rw [← mul_assoc, ← mul_pow]
    norm_num
  simp only [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- Events each reading one coordinate of a product measure are independent. -/
theorem iIndepSet_infinitePi_preimage {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    iIndepSet (fun i => {ω : ι → Ω | ω i ∈ B i}) (Measure.infinitePi fun _ : ι => P) := by
  classical
  refine (iIndepSet_iff_meas_biInter (f := fun i => {ω : ι → Ω | ω i ∈ B i})
    fun i => measurable_pi_apply i (hB i)).2 fun s => ?_
  have h1 : (⋂ i ∈ s, {ω : ι → Ω | ω i ∈ B i}) = Set.pi (s : Set ι) B := by
    ext ω; simp
  rw [h1, Measure.infinitePi_pi (μ := fun _ : ι => P) fun i _ => hB i]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : {ω : ι → Ω | ω i ∈ B i} = Set.pi ({i} : Finset ι) B := by
    ext ω; simp
  rw [h2, Measure.infinitePi_pi (μ := fun _ : ι => P) fun j _ => hB j, Finset.prod_singleton]

end FrogModel.D3.Iface
