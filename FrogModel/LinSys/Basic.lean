module

public import FrogModel.LinSys.Defs

@[expose] public section

/-!
# Nonnegative linear systems: the operator, the iterates and the least solution

The operator `app K` is monotone, additive, homogeneous and commutes with suprema of monotone
sequences; the least solution `least K b` is a fixed point, lies below every super-solution, and is
additive and homogeneous in `b`.
-/

open Filter Topology
open scoped ENNReal

theorem FrogModel.LinSys.app_mono {ι : Type*} (K : ι → ι → ℝ≥0∞) {f g : ι → ℝ≥0∞} (h : f ≤ g) :
    FrogModel.LinSys.app K f ≤ FrogModel.LinSys.app K g := by
  intro i
  unfold FrogModel.LinSys.app
  apply ENNReal.tsum_le_tsum
  intro j
  apply mul_le_mul_right
  apply h

theorem FrogModel.LinSys.app_add {ι : Type*} (K : ι → ι → ℝ≥0∞) (f g : ι → ℝ≥0∞) :
    FrogModel.LinSys.app K (f + g) = FrogModel.LinSys.app K f + FrogModel.LinSys.app K g := by
  funext i
  unfold FrogModel.LinSys.app
  simp_rw [Pi.add_apply, mul_add]
  rw [ENNReal.tsum_add]

theorem FrogModel.LinSys.app_const_mul {ι : Type*} (K : ι → ι → ℝ≥0∞) (c : ℝ≥0∞)
    (f : ι → ℝ≥0∞) :
    FrogModel.LinSys.app K (fun i => c * f i) = fun i => c * FrogModel.LinSys.app K f i := by
  funext i
  dsimp [FrogModel.LinSys.app]
  calc
    (∑' j, K i j * (c * f j)) = (∑' j, c * (K i j * f j)) := by
      refine tsum_congr (fun j => ?_)
      ring
    _ = c * (∑' j, K i j * f j) := by rw [ENNReal.tsum_mul_left]

theorem FrogModel.LinSys.app_zero {ι : Type*} (K : ι → ι → ℝ≥0∞) :
    FrogModel.LinSys.app K 0 = 0 := by
  ext i; simp [FrogModel.LinSys.app]

theorem FrogModel.LinSys.app_iSup {ι : Type*} (K : ι → ι → ℝ≥0∞) (f : ℕ → ι → ℝ≥0∞)
    (hf : Monotone f) :
    FrogModel.LinSys.app K (fun i => ⨆ n, f n i) = fun i => ⨆ n, FrogModel.LinSys.app K (f n) i := by
  funext i
  simp only [FrogModel.LinSys.app]
  -- Goal: ∑' j, K i j * (⨆ n, f n j) = ⨆ n, ∑' j, K i j * f n j
  have h_mul (j : ι) : K i j * (⨆ n, f n j) = ⨆ n, K i j * f n j := by
    rw [ENNReal.mul_iSup]
  have h_mono (j : ι) : Monotone (fun (n : ℕ) => K i j * f n j) := by
    intro n m h
    have hfj : f n j ≤ f m j := hf h j
    exact mul_le_mul_right hfj (K i j)
  calc
    ∑' j, K i j * (⨆ n, f n j) = ∑' j, ⨆ n, K i j * f n j := by
      refine tsum_congr fun j => ?_
      rw [h_mul j]
    _ = ⨆ s : Finset ι, ∑ j ∈ s, ⨆ n, K i j * f n j := by
      rw [ENNReal.tsum_eq_iSup_sum]
    _ = ⨆ s : Finset ι, ⨆ n, ∑ j ∈ s, K i j * f n j := by
      refine iSup_congr fun s => ?_
      rw [ENNReal.finsetSum_iSup_of_monotone (fun j => h_mono j)]
    _ = ⨆ n, ⨆ s : Finset ι, ∑ j ∈ s, K i j * f n j := by
      rw [iSup_comm]
    _ = ⨆ n, ∑' j, K i j * f n j := by
      refine iSup_congr fun n => ?_
      rw [ENNReal.tsum_eq_iSup_sum]

theorem FrogModel.LinSys.app_le_of_row {ι : Type*} (K : ι → ι → ℝ≥0∞) (f : ι → ℝ≥0∞) (i : ι)
    (C : ℝ≥0∞) (hf : ∀ j, K i j ≠ 0 → f j ≤ C) :
    FrogModel.LinSys.app K f i ≤ C * ∑' j, K i j := by
  dsimp [app]
  calc
    ∑' j, K i j * f j ≤ ∑' j, K i j * C := by
      refine ENNReal.tsum_le_tsum fun j => ?_
      by_cases h : K i j = 0
      · simp [h]
      · gcongr
        exact hf j h
    _ = (∑' j, K i j) * C := by rw [ENNReal.tsum_mul_right]
    _ = C * ∑' j, K i j := mul_comm _ _

theorem FrogModel.LinSys.iter_mono {ι : Type*} (K : ι → ι → ℝ≥0∞) (b : ι → ℝ≥0∞) :
    Monotone (FrogModel.LinSys.iter K b) := by
  have hstep : ∀ n, FrogModel.LinSys.iter K b n ≤ FrogModel.LinSys.iter K b (n + 1) := by
    intro n
    induction' n with k ih
    · -- iter 0 ≤ iter 1: 0 ≤ b
      simp [FrogModel.LinSys.iter]
    · -- iter (k+1) ≤ iter (k+2)
      have h_app : FrogModel.LinSys.app K (FrogModel.LinSys.iter K b k) ≤
                  FrogModel.LinSys.app K (FrogModel.LinSys.iter K b (k + 1)) := by
        intro i
        simp [FrogModel.LinSys.app]
        refine ENNReal.tsum_le_tsum fun j => ?_
        have hiter : FrogModel.LinSys.iter K b k j ≤ FrogModel.LinSys.iter K b (k + 1) j := ih j
        exact mul_le_mul' (le_refl _) hiter
      simp [FrogModel.LinSys.iter]
      exact add_le_add_right h_app b
  exact monotone_nat_of_le_succ hstep

theorem FrogModel.LinSys.iter_le_least {ι : Type*} (K : ι → ι → ℝ≥0∞) (b : ι → ℝ≥0∞) (n : ℕ) :
    FrogModel.LinSys.iter K b n ≤ FrogModel.LinSys.least K b := by
  intro i
  dsimp [FrogModel.LinSys.least]
  exact le_iSup (fun n => FrogModel.LinSys.iter K b n i) n

theorem FrogModel.LinSys.least_eq {ι : Type*} (K : ι → ι → ℝ≥0∞) (b : ι → ℝ≥0∞) :
    FrogModel.LinSys.least K b = b + FrogModel.LinSys.app K (FrogModel.LinSys.least K b) := by
  ext i
  -- left side: ⨆ n, iter K b n i
  -- right side: b i + ∑' j, K i j * (⨆ n, iter K b n j)
  have hmono : Monotone (FrogModel.LinSys.iter K b) := FrogModel.LinSys.iter_mono K b
  -- use app_iSup to commute app with iSup
  have happ_iSup : FrogModel.LinSys.app K (fun i => ⨆ n, FrogModel.LinSys.iter K b n i) =
      fun i => ⨆ n, FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) i := by
    simpa using FrogModel.LinSys.app_iSup K (FrogModel.LinSys.iter K b) hmono
  calc
    FrogModel.LinSys.least K b i = (⨆ n, FrogModel.LinSys.iter K b n i) := rfl
    _ = (⨆ n, FrogModel.LinSys.iter K b (n + 1) i) := by
      -- Monotone.iSup_nat_add: ⨆ n, f (n + k) = ⨆ n, f n
      simpa using congr_fun (Monotone.iSup_nat_add hmono 1).symm i
    _ = (⨆ n, (b i + FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) i)) := by
      simp [FrogModel.LinSys.iter]
    _ = (⨆ n, b i + FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) i) := rfl
    _ = b i + (⨆ n, FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) i) := by
      -- ENNReal.add_iSup: a + ⨆ i, f i = ⨆ i, a + f i
      simpa using (ENNReal.add_iSup (a := b i) (f := fun n => FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) i)).symm
    _ = b i + FrogModel.LinSys.app K (fun i => ⨆ n, FrogModel.LinSys.iter K b n i) i := by
      simp [happ_iSup]
    _ = (b + FrogModel.LinSys.app K (FrogModel.LinSys.least K b)) i := rfl

theorem FrogModel.LinSys.least_add {ι : Type*} (K : ι → ι → ℝ≥0∞) (b b' : ι → ℝ≥0∞) :
    FrogModel.LinSys.least K (b + b') = FrogModel.LinSys.least K b + FrogModel.LinSys.least K b' := by
  have iter_add : ∀ n, FrogModel.LinSys.iter K (b + b') n = FrogModel.LinSys.iter K b n + FrogModel.LinSys.iter K b' n := by
    intro n
    induction' n with n ih
    · ext i; simp [FrogModel.LinSys.iter]
    · ext i
      simp [FrogModel.LinSys.iter, ih, FrogModel.LinSys.app_add, add_left_comm, add_assoc]
  have iter_succ_le : ∀ (c : ι → ℝ≥0∞) (n : ℕ) (i : ι),
      FrogModel.LinSys.iter K c n i ≤ FrogModel.LinSys.iter K c (n + 1) i := by
    intro c n
    induction' n with k ih
    · intro i; simp [FrogModel.LinSys.iter]
    · intro i
      simp [FrogModel.LinSys.iter]
      have htsum : FrogModel.LinSys.app K (FrogModel.LinSys.iter K c k) i ≤
          FrogModel.LinSys.app K (c + FrogModel.LinSys.app K (FrogModel.LinSys.iter K c k)) i := by
        simp [FrogModel.LinSys.app]
        refine ENNReal.tsum_le_tsum fun j => ?_
        have h := ih j
        have h_mul : K i j * FrogModel.LinSys.iter K c k j ≤
            K i j * FrogModel.LinSys.iter K c (k + 1) j := by
          gcongr
        simpa [FrogModel.LinSys.app, FrogModel.LinSys.iter] using h_mul
      -- htsum : A ≤ B, goal: c i + A ≤ c i + B
      -- add_le_add_left gives A + c i ≤ B + c i, so we use add_comm
      simpa [add_comm] using add_le_add_right htsum (c i)
  have iter_mono : ∀ (c : ι → ℝ≥0∞), ∀ i, Monotone fun n => FrogModel.LinSys.iter K c n i := by
    intro c i
    exact monotone_nat_of_le_succ (fun n => iter_succ_le c n i)
  have mono_b : ∀ i, Monotone fun n => FrogModel.LinSys.iter K b n i := iter_mono b
  have mono_b' : ∀ i, Monotone fun n => FrogModel.LinSys.iter K b' n i := iter_mono b'
  ext i
  calc
    FrogModel.LinSys.least K (b + b') i = ⨆ n, FrogModel.LinSys.iter K (b + b') n i := rfl
    _ = ⨆ n, (FrogModel.LinSys.iter K b n i + FrogModel.LinSys.iter K b' n i) := by
      simp [iter_add]
    _ = (⨆ n, FrogModel.LinSys.iter K b n i) + (⨆ n, FrogModel.LinSys.iter K b' n i) := by
      rw [ENNReal.iSup_add_iSup_of_monotone (mono_b i) (mono_b' i)]
    _ = (FrogModel.LinSys.least K b i) + (FrogModel.LinSys.least K b' i) := rfl
    _ = (FrogModel.LinSys.least K b + FrogModel.LinSys.least K b') i := rfl

namespace FrogModel.LinSys

theorem iter_const_mul {ι : Type*} (K : ι → ι → ℝ≥0∞) (c : ℝ≥0∞) (b : ι → ℝ≥0∞) (n : ℕ) :
    iter K (fun i => c * b i) n = fun i => c * iter K b n i := by
  induction' n with n ih
  · ext i; simp [iter]
  · ext i
    simp [iter, ih, app_const_mul K c (iter K b n), mul_add]

theorem least_const_mul {ι : Type*} (K : ι → ι → ℝ≥0∞) (c : ℝ≥0∞) (b : ι → ℝ≥0∞) :
    least K (fun i => c * b i) = fun i => c * least K b i := by
  ext i
  simp [least, iter_const_mul K c b, ENNReal.mul_iSup]

end FrogModel.LinSys

theorem FrogModel.LinSys.app_le_of_kernel {ι : Type*} (K K' : ι → ι → ℝ≥0∞) (f : ι → ℝ≥0∞)
    (hK : ∀ i j, K i j ≤ K' i j) : FrogModel.LinSys.app K f ≤ FrogModel.LinSys.app K' f := by
  intro i
  dsimp [FrogModel.LinSys.app]
  refine ENNReal.tsum_le_tsum (fun j => ?_)
  apply mul_le_mul (hK i j) (le_refl (f j))
  · exact zero_le
  · exact zero_le

theorem FrogModel.LinSys.least_le_of_super {ι : Type*} (K : ι → ι → ℝ≥0∞) (b W : ι → ℝ≥0∞)
    (h : b + FrogModel.LinSys.app K W ≤ W) : FrogModel.LinSys.least K b ≤ W := by
  have h_iter : ∀ n, FrogModel.LinSys.iter K b n ≤ W := by
    intro n
    induction' n with n ih
    · simp [FrogModel.LinSys.iter]
    · simp [FrogModel.LinSys.iter]
      calc
        b + FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) ≤
            b + FrogModel.LinSys.app K W :=
          add_le_add (le_refl b) (FrogModel.LinSys.app_mono K ih)
        _ ≤ W := h
  intro i
  apply iSup_le
  intro n
  exact h_iter n i

theorem FrogModel.LinSys.least_mono {ι : Type*} (K K' : ι → ι → ℝ≥0∞) (b b' : ι → ℝ≥0∞)
    (hK : ∀ i j, K i j ≤ K' i j) (hb : b ≤ b') :
    FrogModel.LinSys.least K b ≤ FrogModel.LinSys.least K' b' := by
  have h_iter : ∀ n, FrogModel.LinSys.iter K b n ≤ FrogModel.LinSys.iter K' b' n := by
    intro n
    induction' n with n ih
    · simp [FrogModel.LinSys.iter]
    · have h_app : FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) ≤
                  FrogModel.LinSys.app K' (FrogModel.LinSys.iter K' b' n) := by
        calc
          FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) ≤
              FrogModel.LinSys.app K (FrogModel.LinSys.iter K' b' n) :=
            FrogModel.LinSys.app_mono K (h := ih)
          _ ≤ FrogModel.LinSys.app K' (FrogModel.LinSys.iter K' b' n) :=
            FrogModel.LinSys.app_le_of_kernel K K' (FrogModel.LinSys.iter K' b' n) hK
      have h_add : b + FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) ≤
                   b' + FrogModel.LinSys.app K' (FrogModel.LinSys.iter K' b' n) :=
        add_le_add hb h_app
      simpa [FrogModel.LinSys.iter] using h_add
  intro i
  apply iSup_mono
  intro n
  exact h_iter n i

lemma FrogModel.LinSys.app_sum {ι : Type*} (K : ι → ι → ℝ≥0∞) (n : ℕ) (f : ℕ → ι → ℝ≥0∞) :
    FrogModel.LinSys.app K (fun i => ∑ k ∈ Finset.range n, f k i) =
    fun i => ∑ k ∈ Finset.range n, FrogModel.LinSys.app K (f k) i := by
  induction n with
  | zero =>
      ext i
      simp
      have h := FrogModel.LinSys.app_zero K
      exact congrArg (fun f => f i) h
  | succ n ih =>
      ext i
      have hsum : (fun i => ∑ k ∈ Finset.range (n+1), f k i) =
                 (fun i => ∑ k ∈ Finset.range n, f k i) + f n := by
        ext i; simp [Finset.sum_range_succ]
      rw [hsum, FrogModel.LinSys.app_add, ih]
      simp [Finset.sum_range_succ]

theorem FrogModel.LinSys.iter_eq_sum {ι : Type*} (K : ι → ι → ℝ≥0∞) (b : ι → ℝ≥0∞) (n : ℕ) :
    FrogModel.LinSys.iter K b n =
      fun i => ∑ k ∈ Finset.range n, (FrogModel.LinSys.app K)^[k] b i := by
  induction n with
  | zero =>
      ext i
      simp [FrogModel.LinSys.iter]
  | succ n ih =>
      ext i
      rw [FrogModel.LinSys.iter, ih, FrogModel.LinSys.app_sum]
      simp only [Pi.add_apply, Finset.sum_range_succ]
      have h_eq : ∀ k, app K ((app K)^[k] b) i = (app K)^[k+1] b i := by
        intro k
        exact congrArg (fun f => f i) (Function.iterate_succ_apply' (app K) k b).symm
      have h_sum : (∑ k ∈ Finset.range n, app K ((app K)^[k] b) i) =
                   (∑ k ∈ Finset.range n, (app K)^[k+1] b i) := by
        simp [h_eq]
      rw [h_sum]
      rw [← Finset.sum_range_succ (f := fun k => (app K)^[k] b i)]
      rw [Finset.sum_range_succ' (f := fun k => (app K)^[k] b i)]
      simp [Function.iterate_zero, add_comm]

theorem FrogModel.LinSys.least_eq_tsum {ι : Type*} (K : ι → ι → ℝ≥0∞) (b : ι → ℝ≥0∞) :
    FrogModel.LinSys.least K b = fun i => ∑' k, (FrogModel.LinSys.app K)^[k] b i := by
  ext i
  simp_rw [FrogModel.LinSys.least, FrogModel.LinSys.iter_eq_sum]
  rw [ENNReal.tsum_eq_iSup_nat]

theorem FrogModel.LinSys.le_iter_add_pow {ι : Type*} (K : ι → ι → ℝ≥0∞) (b V : ι → ℝ≥0∞)
    (h : V ≤ b + FrogModel.LinSys.app K V) (n : ℕ) :
    V ≤ FrogModel.LinSys.iter K b n + (FrogModel.LinSys.app K)^[n] V := by
  induction n with
  | zero =>
      simp [FrogModel.LinSys.iter]
  | succ n ih =>
      have h_appV : FrogModel.LinSys.app K V ≤
          FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n + (FrogModel.LinSys.app K)^[n] V) :=
        FrogModel.LinSys.app_mono K ih
      have h_app_add : FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n + (FrogModel.LinSys.app K)^[n] V) =
          FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) +
          FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] V) :=
        FrogModel.LinSys.app_add K (FrogModel.LinSys.iter K b n) ((FrogModel.LinSys.app K)^[n] V)
      have h_sum : FrogModel.LinSys.app K V ≤
          FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) +
          FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] V) := by
        calc
          FrogModel.LinSys.app K V ≤
              FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n + (FrogModel.LinSys.app K)^[n] V) := h_appV
          _ = FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) +
              FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] V) := h_app_add
      calc
        V ≤ b + FrogModel.LinSys.app K V := h
        _ ≤ b + (FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n) +
            FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] V)) := by
          gcongr
        _ = (b + FrogModel.LinSys.app K (FrogModel.LinSys.iter K b n)) +
            FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] V) := by
          simp [add_assoc]
        _ = FrogModel.LinSys.iter K b (n + 1) + (FrogModel.LinSys.app K)^[n + 1] V := by
          simp [FrogModel.LinSys.iter, Function.iterate_succ_apply']

theorem FrogModel.LinSys.tsum_pow_one_le {ι : Type*} (K : ι → ι → ℝ≥0∞) (Z : ι → ℝ≥0∞)
    (hZ : (fun _ => 1) + FrogModel.LinSys.app K Z ≤ Z) (i : ι) :
    ∑' n, (FrogModel.LinSys.app K)^[n] (fun _ => 1) i ≤ Z i := by
  have h_least : FrogModel.LinSys.least K (fun _ => 1) ≤ Z :=
    FrogModel.LinSys.least_le_of_super K (fun _ => 1) Z hZ
  have h_iter_le (n : ℕ) : FrogModel.LinSys.iter K (fun _ => 1) n i ≤ Z i := by
    calc
      FrogModel.LinSys.iter K (fun _ => 1) n i ≤ FrogModel.LinSys.least K (fun _ => 1) i :=
        FrogModel.LinSys.iter_le_least K (fun _ => 1) n i
      _ ≤ Z i := h_least i
  have h_sum_le (n : ℕ) : ∑ k ∈ Finset.range n, (FrogModel.LinSys.app K)^[k] (fun _ => 1) i ≤ Z i := by
    calc
      ∑ k ∈ Finset.range n, (FrogModel.LinSys.app K)^[k] (fun _ => 1) i =
          FrogModel.LinSys.iter K (fun _ => 1) n i := by
        symm
        exact congrArg (fun f => f i) (FrogModel.LinSys.iter_eq_sum K (fun _ => 1) n)
      _ ≤ Z i := h_iter_le n
  calc
    ∑' n, (FrogModel.LinSys.app K)^[n] (fun _ => 1) i =
        ⨆ n, ∑ k ∈ Finset.range n, (FrogModel.LinSys.app K)^[k] (fun _ => 1) i := by
      simpa using ENNReal.tsum_eq_iSup_nat (f := fun n => (FrogModel.LinSys.app K)^[n] (fun _ => 1) i)
    _ ≤ Z i := iSup_le h_sum_le

theorem FrogModel.LinSys.tendsto_pow_one {ι : Type*} (K : ι → ι → ℝ≥0∞) (Z : ι → ℝ≥0∞)
    (hZ : (fun _ => 1) + FrogModel.LinSys.app K Z ≤ Z) (hfin : ∀ i, Z i ≠ ⊤) (i : ι) :
    Tendsto (fun n => (FrogModel.LinSys.app K)^[n] (fun _ => 1) i) atTop (𝓝 0) := by
  have h_tsum_ne_top : ∑' n, (FrogModel.LinSys.app K)^[n] (fun _ => 1) i ≠ ⊤ := by
    have hle := FrogModel.LinSys.tsum_pow_one_le K Z hZ i
    have hfinZ : Z i ≠ ⊤ := hfin i
    exact ne_top_of_le_ne_top hfinZ hle
  simpa using ENNReal.tendsto_atTop_zero_of_tsum_ne_top h_tsum_ne_top

theorem FrogModel.LinSys.pow_le_const_mul {ι : Type*} (K : ι → ι → ℝ≥0∞) (V : ι → ℝ≥0∞)
    (C : ℝ≥0∞) (hV : ∀ i, V i ≤ C) (n : ℕ) :
    (FrogModel.LinSys.app K)^[n] V ≤ fun i => C * (FrogModel.LinSys.app K)^[n] (fun _ => 1) i := by
  induction' n with n ih
  · intro i
    simp [hV i]
  · intro i
    calc
      (FrogModel.LinSys.app K)^[n+1] V i = FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] V) i := by
        simp [Function.iterate_succ_apply']
      _ ≤ FrogModel.LinSys.app K (fun i => C * (FrogModel.LinSys.app K)^[n] (fun _ => 1) i) i :=
        FrogModel.LinSys.app_mono K ih i
      _ = (fun i => C * FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] (fun _ => 1)) i) i := by
        simp [FrogModel.LinSys.app_const_mul]
      _ = C * (FrogModel.LinSys.app K)^[n+1] (fun _ => 1) i := by
        simp [Function.iterate_succ_apply']

theorem FrogModel.LinSys.super_of_contract {ι : Type*} (K : ι → ι → ℝ≥0∞) (g : ι → ℝ≥0∞)
    (r : ℝ≥0∞) (hg : FrogModel.LinSys.app K g ≤ fun i => r * g i) (hr : r < 1)
    (hg1 : ∀ i, 1 ≤ g i) :
    (fun _ => 1) + FrogModel.LinSys.app K (fun i => (1 - r)⁻¹ * g i) ≤ fun i => (1 - r)⁻¹ * g i := by
  set s := (1 - r)⁻¹ with hs
  have hpos : 1 - r ≠ 0 := by
    intro hzero
    have : 1 ≤ r := (tsub_eq_zero_iff_le.mp hzero)
    exact not_lt.mpr this hr
  have htop : 1 - r ≠ ⊤ := by
    have hle : 1 - r ≤ 1 := tsub_le_self
    intro h
    have htop' : (1 : ℝ≥0∞) = ⊤ := by
      calc
        1 = 1 - r + r := by rw [tsub_add_cancel_of_le hr.le]
        _ = ⊤ + r := by rw [h]
        _ = ⊤ := by simp
    have h_one_ne_top : (1 : ℝ≥0∞) ≠ ⊤ := by simp
    exact h_one_ne_top htop'
  have hs_eq : s = 1 + r * s := by
    calc
      s = 1 * s := by simp
      _ = ((1 - r) + r) * s := by rw [tsub_add_cancel_of_le hr.le]
      _ = (1 - r) * s + r * s := by rw [add_mul]
      _ = 1 + r * s := by rw [hs, ENNReal.mul_inv_cancel hpos htop]
  intro i
  have h_app : FrogModel.LinSys.app K (fun i => s * g i) i = s * FrogModel.LinSys.app K g i := by
    have := FrogModel.LinSys.app_const_mul K s g
    simpa [hs] using congrFun this i
  have hg_i : FrogModel.LinSys.app K g i ≤ r * g i := hg i
  simp [hs]
  rw [h_app]
  calc
    1 + s * FrogModel.LinSys.app K g i ≤ 1 + s * (r * g i) := by
      gcongr
    _ = 1 + (s * r) * g i := by ring
    _ = 1 + (r * s) * g i := by rw [mul_comm s r]
    _ = 1 + s * (r * g i) := by ring
    _ ≤ g i + s * (r * g i) := by
      gcongr
      exact hg1 i
    _ = (1 + r * s) * g i := by ring
    _ = s * g i := by rw [← hs_eq]

theorem FrogModel.LinSys.iter_le_of_contract {ι : Type*} (K : ι → ι → ℝ≥0∞) (g : ι → ℝ≥0∞)
    (r : ℝ≥0∞) (hg : FrogModel.LinSys.app K g ≤ fun i => r * g i) (n : ℕ) :
    (FrogModel.LinSys.app K)^[n] g ≤ fun i => r ^ n * g i := by
  induction' n with n ih
  · intro i
    simp [Function.iterate_zero, pow_zero, one_mul]
  · intro i
    have h_iter_succ : (FrogModel.LinSys.app K)^[n + 1] g = FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] g) := by
      simp [Function.iterate_succ_apply']
    rw [h_iter_succ]
    have h1 : (FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] g)) i ≤ (FrogModel.LinSys.app K (fun i => r ^ n * g i)) i :=
      FrogModel.LinSys.app_mono K ih i
    have h2 : (FrogModel.LinSys.app K (fun i => r ^ n * g i)) i = r ^ n * (FrogModel.LinSys.app K g i) := by
      simp [FrogModel.LinSys.app_const_mul]
    have h3 : r ^ n * (FrogModel.LinSys.app K g i) ≤ r ^ n * (r * g i) := by
      have hg_i : (FrogModel.LinSys.app K g) i ≤ r * g i := hg i
      exact mul_le_mul_right hg_i (r ^ n)
    have h4 : r ^ n * (r * g i) = r ^ (n + 1) * g i := by
      calc
        r ^ n * (r * g i) = (r ^ n * r) * g i := by ring
        _ = r ^ (n + 1) * g i := by simp [pow_succ]
    calc
      (FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] g)) i ≤ (FrogModel.LinSys.app K (fun i => r ^ n * g i)) i := h1
      _ = r ^ n * (FrogModel.LinSys.app K g i) := h2
      _ ≤ r ^ n * (r * g i) := h3
      _ = r ^ (n + 1) * g i := h4

theorem FrogModel.LinSys.tendsto_iter_of_contract {ι : Type*} (K : ι → ι → ℝ≥0∞) (g : ι → ℝ≥0∞)
    (r : ℝ≥0∞) (hg : FrogModel.LinSys.app K g ≤ fun i => r * g i) (hr : r < 1) (i : ι)
    (hgi : g i ≠ ⊤) : Tendsto (fun n => (FrogModel.LinSys.app K)^[n] g i) atTop (𝓝 0) := by
  have h_pow_tendsto : Tendsto (fun (n : ℕ) => r ^ n) atTop (𝓝 (0 : ℝ≥0∞)) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr
  have h_mul_tendsto : Tendsto (fun (n : ℕ) => r ^ n * g i) atTop (𝓝 ((0 : ℝ≥0∞) * g i)) :=
    ENNReal.Tendsto.mul_const h_pow_tendsto (Or.inr hgi)
  have h_zero_mul : (0 : ℝ≥0∞) * g i = 0 := by simp
  rw [h_zero_mul] at h_mul_tendsto
  have h_bound : (fun (n : ℕ) => (0 : ℝ≥0∞)) ≤ fun n => (FrogModel.LinSys.app K)^[n] g i := by
    intro n
    simp
  have h_bound' : (fun n => (FrogModel.LinSys.app K)^[n] g i) ≤ fun n => r ^ n * g i := by
    intro n
    have h := FrogModel.LinSys.iter_le_of_contract K g r hg n i
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ h_mul_tendsto h_bound h_bound'
  · exact tendsto_const_nhds

theorem FrogModel.LinSys.iter_le_of_dom {ι : Type*} (K : ι → ι → ℝ≥0∞) (f g : ι → ℝ≥0∞)
    (C : ℝ≥0∞) (hfg : ∀ i, f i ≤ C * g i) (n : ℕ) :
    ∀ i, (FrogModel.LinSys.app K)^[n] f i ≤ C * (FrogModel.LinSys.app K)^[n] g i := by
  induction' n with n ih
  · exact hfg
  · intro i
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] f) i ≤
          FrogModel.LinSys.app K (fun j => C * (FrogModel.LinSys.app K)^[n] g j) i := by
        apply FrogModel.LinSys.app_mono
        exact ih
      _ = C * FrogModel.LinSys.app K ((FrogModel.LinSys.app K)^[n] g) i := by
        rw [FrogModel.LinSys.app_const_mul]

theorem FrogModel.LinSys.tendsto_iter_of_dom {ι : Type*} (K : ι → ι → ℝ≥0∞) (f g : ι → ℝ≥0∞)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hfg : ∀ i, f i ≤ C * g i) (i : ι)
    (hg : Tendsto (fun n => (FrogModel.LinSys.app K)^[n] g i) atTop (𝓝 0)) :
    Tendsto (fun n => (FrogModel.LinSys.app K)^[n] f i) atTop (𝓝 0) := by
  have h_upper : Tendsto (fun n => C * (FrogModel.LinSys.app K)^[n] g i) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hg (Or.inr hC)
    simpa [mul_zero] using this
  have h_le : ∀ n, (FrogModel.LinSys.app K)^[n] f i ≤ C * (FrogModel.LinSys.app K)^[n] g i :=
    fun n => FrogModel.LinSys.iter_le_of_dom K f g C hfg n i
  have h_zero_le : ∀ n, 0 ≤ (FrogModel.LinSys.app K)^[n] f i :=
    fun n => zero_le (a := (FrogModel.LinSys.app K)^[n] f i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper h_zero_le h_le

theorem FrogModel.LinSys.le_least_of_sub_tendsto {ι : Type*} (K : ι → ι → ℝ≥0∞) (b V : ι → ℝ≥0∞)
    (h : V ≤ b + FrogModel.LinSys.app K V)
    (hV : ∀ i, Tendsto (fun n => (FrogModel.LinSys.app K)^[n] V i) atTop (𝓝 0)) :
    V ≤ FrogModel.LinSys.least K b := by
  intro i
  have h_iter_add := le_iter_add_pow K b V h
  have h_iter_le := iter_le_least K b
  have h_bound (n : ℕ) : V i ≤ (FrogModel.LinSys.least K b) i + ((FrogModel.LinSys.app K)^[n] V) i := by
    calc
      V i ≤ (FrogModel.LinSys.iter K b n) i + ((FrogModel.LinSys.app K)^[n] V) i := h_iter_add n i
      _ ≤ (FrogModel.LinSys.least K b) i + ((FrogModel.LinSys.app K)^[n] V) i :=
        add_le_add (h_iter_le n i) (le_refl _)
  have h_tendsto : Tendsto (fun n : ℕ => (FrogModel.LinSys.least K b) i + ((FrogModel.LinSys.app K)^[n] V) i) atTop (𝓝 ((FrogModel.LinSys.least K b) i)) := by
    have h_const : Tendsto (fun _ : ℕ => (FrogModel.LinSys.least K b) i) atTop (𝓝 ((FrogModel.LinSys.least K b) i)) := tendsto_const_nhds
    have h_zero : Tendsto (fun n : ℕ => ((FrogModel.LinSys.app K)^[n] V) i) atTop (𝓝 0) := hV i
    simpa [add_zero] using Filter.Tendsto.add h_const h_zero
  exact ge_of_tendsto' h_tendsto h_bound
