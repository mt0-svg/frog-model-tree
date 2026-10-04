module

public import FrogModel.D3.Interfaces.Step
public import FrogModel.D3.LaneD.K.Check

@[expose] public section

/-!
# Packed naturals

The kernel checker (`FrogModel.D3.LaneD.K`) holds vectors and tables in naturals, slot `i` of width
`w` in the bits `[w i, w (i + 1))`. `pk w f n` is the packed natural with slots `f 0, ..., f (n - 1)`
and `pk2 w S f m n` the table with entry `(e, g)` at slot `S e + g`. Products, sums and shifts of
packed naturals are pure algebra (`pk_mul`, `pk2_mul`, `pk_add`, `pk_shiftLeft`); reading a slot,
masking and shifting right need every slot below `2^w` (`slot_pk`, `pk_mod`, `pk_div`). The second
half proves the kernel's helpers (`packTree`, `split`, `packRows`, `ones`, `choose`, `fact`, the
loops) equal to these forms.
-/

namespace FrogModel.D3.LaneD.K

/-- `Nat.div` as `/` (the kernel code calls the function). -/
@[simp] theorem ndiv_eq (x y : ℕ) : Nat.div x y = x / y := rfl

/-- `Nat.mod` as `%`. -/
@[simp] theorem nmod_eq (x y : ℕ) : Nat.mod x y = x % y := rfl

/-- `sum over i < n of f i 2^(w i)`: the packed natural with slots `f 0, ..., f (n - 1)`. -/
def pk (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, f i * 2 ^ (w * i)

/-- The table with entry `(e, g)` at slot `S e + g` (`e < m`, `g < n`). -/
def pk2 (w S : ℕ) (f : ℕ → ℕ → ℕ) (m n : ℕ) : ℕ :=
  ∑ e ∈ Finset.range m, ∑ g ∈ Finset.range n, f e g * 2 ^ (w * (S * e + g))

/-! ## Algebra of packed naturals -/

theorem pk_zero (w : ℕ) (f : ℕ → ℕ) : pk w f 0 = 0 := by simp [pk]

theorem pk_succ (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : pk w f (n + 1) = pk w f n + f n * 2 ^ (w * n) := by
  simp [pk, Finset.sum_range_succ]

theorem pk_congr (w : ℕ) (f g : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, f i = g i) : pk w f n = pk w g n :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem pk_add (w : ℕ) (f g : ℕ → ℕ) (n : ℕ) : pk w f n + pk w g n = pk w (fun i => f i + g i) n := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]

theorem pk_smul (w c : ℕ) (f : ℕ → ℕ) (n : ℕ) : c * pk w f n = pk w (fun i => c * f i) n := by
  simp [pk, Finset.mul_sum, mul_assoc]

theorem pk_sum (w : ℕ) (s : Finset ℕ) (f : ℕ → ℕ → ℕ) (n : ℕ) :
    ∑ M ∈ s, pk w (f M) n = pk w (fun i => ∑ M ∈ s, f M i) n := by
  simp only [pk, Finset.sum_mul]
  exact Finset.sum_comm

theorem pk_extend (w : ℕ) (f : ℕ → ℕ) (n m : ℕ) (hnm : n ≤ m) (hz : ∀ i, n ≤ i → i < m → f i = 0) :
    pk w f m = pk w f n := by
  dsimp [pk]
  have hsum := Finset.sum_range_add_sum_Ico (fun i => f i * 2 ^ (w * i)) hnm
  have hzero : ∑ k ∈ Finset.Ico n m, f k * 2 ^ (w * k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rcases hi with ⟨hni, him⟩
    rw [hz i hni him, zero_mul]
  calc
    ∑ k ∈ Finset.range m, f k * 2 ^ (w * k)
        = (∑ k ∈ Finset.range n, f k * 2 ^ (w * k)) + (∑ k ∈ Finset.Ico n m, f k * 2 ^ (w * k)) := by
      rw [← hsum]
    _ = (∑ k ∈ Finset.range n, f k * 2 ^ (w * k)) + 0 := by rw [hzero]
    _ = ∑ k ∈ Finset.range n, f k * 2 ^ (w * k) := by rw [add_zero]

theorem pk_lt (w : ℕ) (f : ℕ → ℕ) (n : ℕ) (hf : ∀ i < n, f i < 2 ^ w) : pk w f n < 2 ^ (w * n) := by
  induction' n with n ih
  · simp [pk]
  · rw [pk, Finset.sum_range_succ]
    have hfn : f n < 2 ^ w := hf n (Nat.lt_succ_self n)
    have hsum : (∑ i ∈ Finset.range n, f i * 2 ^ (w * i)) < 2 ^ (w * n) := ih (fun i hi => hf i (Nat.lt_succ_of_le (Nat.le_of_lt hi)))
    have h_add : (∑ i ∈ Finset.range n, f i * 2 ^ (w * i)) + f n * 2 ^ (w * n) <
                2 ^ (w * n) + f n * 2 ^ (w * n) :=
      Nat.add_lt_add_right hsum (f n * 2 ^ (w * n))
    have h_eq : 2 ^ (w * n) + f n * 2 ^ (w * n) = (f n + 1) * 2 ^ (w * n) := by
      calc
        2 ^ (w * n) + f n * 2 ^ (w * n) = 1 * 2 ^ (w * n) + f n * 2 ^ (w * n) := by simp
        _ = (1 + f n) * 2 ^ (w * n) := by rw [Nat.add_mul]
        _ = (f n + 1) * 2 ^ (w * n) := by rw [add_comm]
    have h_le : f n + 1 ≤ 2 ^ w := by omega
    have h_mul : (f n + 1) * 2 ^ (w * n) ≤ 2 ^ w * 2 ^ (w * n) :=
      Nat.mul_le_mul_right (2 ^ (w * n)) h_le
    have h_pow : 2 ^ w * 2 ^ (w * n) = 2 ^ (w * (n + 1)) := by
      calc
        2 ^ w * 2 ^ (w * n) = 2 ^ (w + w * n) := by rw [pow_add]
        _ = 2 ^ (w * 1 + w * n) := by simp
        _ = 2 ^ (w * (1 + n)) := by rw [Nat.mul_add]
        _ = 2 ^ (w * (n + 1)) := by rw [add_comm]
    calc
      (∑ i ∈ Finset.range n, f i * 2 ^ (w * i)) + f n * 2 ^ (w * n) <
          2 ^ (w * n) + f n * 2 ^ (w * n) := h_add
      _ = (f n + 1) * 2 ^ (w * n) := h_eq
      _ ≤ 2 ^ w * 2 ^ (w * n) := h_mul
      _ = 2 ^ (w * (n + 1)) := h_pow

theorem pk_mod (w : ℕ) (f : ℕ → ℕ) (n k : ℕ) (hf : ∀ i < n, f i < 2 ^ w) :
    pk w f n % 2 ^ (w * k) = pk w f (min n k) := by
  set m := min n k with hm
  have hmn : m ≤ n := Nat.min_le_left n k
  have hmk : m ≤ k := Nat.min_le_right n k
  have hsplit : pk w f n = pk w f m + ∑ i ∈ Finset.Ico m n, f i * 2 ^ (w * i) := by
    dsimp [pk]
    have h := Finset.sum_range_add_sum_Ico (fun i => f i * 2 ^ (w * i)) hmn
    exact h.symm
  by_cases hle : n ≤ k
  · have hm_eq_n : m = n := Nat.min_eq_left hle
    have h_lt : pk w f n < 2 ^ (w * k) := by
      have h := pk_lt w f n hf
      have hpow : 2 ^ (w * n) ≤ 2 ^ (w * k) :=
        Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w hle)
      exact lt_of_lt_of_le h hpow
    calc
      pk w f n % 2 ^ (w * k) = pk w f n := Nat.mod_eq_of_lt h_lt
      _ = pk w f m := by rw [hm_eq_n]
  · have hk_lt_n : k < n := Nat.lt_of_not_ge hle
    have hm_eq_k : m = k := Nat.min_eq_right (Nat.le_of_lt hk_lt_n)
    have hf' : ∀ i < k, f i < 2 ^ w := fun i hi => hf i (lt_of_lt_of_le hi hk_lt_n.le)
    have h_lt : pk w f k < 2 ^ (w * k) := pk_lt w f k hf'
    have hsum_dvd : 2 ^ (w * k) ∣ ∑ i ∈ Finset.Ico k n, f i * 2 ^ (w * i) := by
      apply Finset.dvd_sum
      intro i hi
      rcases (Finset.mem_Ico.mp hi) with ⟨hki, hin⟩
      have h_dvd : 2 ^ (w * k) ∣ 2 ^ (w * i) :=
        pow_dvd_pow 2 (Nat.mul_le_mul_left w hki)
      exact h_dvd.mul_left (f i)
    rcases hsum_dvd with ⟨c, hc⟩
    calc
      pk w f n % 2 ^ (w * k) = (pk w f k + ∑ i ∈ Finset.Ico k n, f i * 2 ^ (w * i)) % 2 ^ (w * k) := by
        rw [hsplit, hm_eq_k]
      _ = (pk w f k + (2 ^ (w * k) * c)) % 2 ^ (w * k) := by rw [hc]
      _ = pk w f k % 2 ^ (w * k) := by rw [Nat.add_mul_mod_self_left]
      _ = pk w f k := Nat.mod_eq_of_lt h_lt
      _ = pk w f m := by rw [hm_eq_k]

theorem pk_div (w : ℕ) (f : ℕ → ℕ) (n k : ℕ) (hf : ∀ i < n, f i < 2 ^ w) :
    pk w f n / 2 ^ (w * k) = pk w (fun i => f (i + k)) (n - k) := by
  by_cases h : n ≤ k
  · -- case n ≤ k
    have h_lt : pk w f n < 2 ^ (w * k) := by
      have h1 : pk w f n < 2 ^ (w * n) := pk_lt w f n hf
      have h2 : 2 ^ (w * n) ≤ 2 ^ (w * k) := by
        apply Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w h)
      exact lt_of_lt_of_le h1 h2
    rw [Nat.div_eq_of_lt h_lt]
    have hsub : n - k = 0 := Nat.sub_eq_zero_of_le h
    rw [hsub]
    simp [pk]
  · -- case ¬ n ≤ k, i.e., k < n
    have h_lt_nk : k < n := Nat.lt_of_not_ge h
    have h_le_nk : k ≤ n := Nat.le_of_lt h_lt_nk
    have hpos : 0 < 2 ^ (w * k) := by
      apply Nat.pow_pos (by norm_num : 0 < 2)
    have hsum : pk w f n = pk w f k + 2 ^ (w * k) * pk w (fun i => f (i + k)) (n - k) := by
      calc
        pk w f n = ∑ i ∈ Finset.range n, f i * 2 ^ (w * i) := rfl
        _ = ∑ i ∈ Finset.range (k + (n - k)), f i * 2 ^ (w * i) := by
          rw [Nat.add_sub_cancel' h_le_nk]
        _ = (∑ i ∈ Finset.range k, f i * 2 ^ (w * i)) +
            (∑ i ∈ Finset.range (n - k), f (k + i) * 2 ^ (w * (k + i))) := by
          rw [Finset.sum_range_add]
        _ = pk w f k + (∑ i ∈ Finset.range (n - k), f (k + i) * 2 ^ (w * (k + i))) := rfl
        _ = pk w f k + (∑ i ∈ Finset.range (n - k), f (k + i) * 2 ^ (w * k + w * i)) := by
          refine congrArg (fun t => pk w f k + t) (Finset.sum_congr rfl ?_)
          intro i hi
          rw [Nat.mul_add w k i]
        _ = pk w f k + (∑ i ∈ Finset.range (n - k), f (k + i) * (2 ^ (w * k) * 2 ^ (w * i))) := by
          refine congrArg (fun t => pk w f k + t) (Finset.sum_congr rfl ?_)
          intro i hi
          rw [pow_add 2 (w * k) (w * i)]
        _ = pk w f k + (∑ i ∈ Finset.range (n - k), 2 ^ (w * k) * (f (k + i) * 2 ^ (w * i))) := by
          refine congrArg (fun t => pk w f k + t) (Finset.sum_congr rfl ?_)
          intro i hi
          ring
        _ = pk w f k + 2 ^ (w * k) * (∑ i ∈ Finset.range (n - k), f (k + i) * 2 ^ (w * i)) := by
          rw [Finset.mul_sum]
        _ = pk w f k + 2 ^ (w * k) * pk w (fun i => f (i + k)) (n - k) := by
          simp [pk, add_comm]
    rw [hsum]
    rw [Nat.add_mul_div_left _ _ hpos]
    have h_lt_k : pk w f k < 2 ^ (w * k) := pk_lt w f k (by
      intro i hi
      apply hf i
      exact lt_of_lt_of_le hi h_le_nk)
    rw [Nat.div_eq_of_lt h_lt_k]
    simp

theorem pk_shiftLeft (w : ℕ) (f : ℕ → ℕ) (n k : ℕ) :
    pk w f n <<< (w * k) = pk w (fun i => if i < k then 0 else f (i - k)) (n + k) := by
  rw [Nat.shiftLeft_eq, pk, pk]
  rw [add_comm n k, Finset.sum_range_add]
  have hzero : (∑ i ∈ Finset.range k, (if i < k then 0 else f (i - k)) * 2 ^ (w * i)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < k := Finset.mem_range.1 hi
    rw [ite_eq_left hi', zero_mul]
  rw [hzero, zero_add]
  have hterm (i : ℕ) : (if (k + i) < k then 0 else f ((k + i) - k)) = f i := by
    have hle : k ≤ k + i := Nat.le_add_right k i
    have hnotlt : ¬ (k + i < k) := Nat.not_lt.mpr hle
    rw [ite_eq_right hnotlt, Nat.add_sub_cancel_left]
  have hsum : (∑ i ∈ Finset.range n, (if (k + i) < k then 0 else f ((k + i) - k)) * 2 ^ (w * (k + i))) =
             (∑ i ∈ Finset.range n, f i * 2 ^ (w * (k + i))) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hterm i]
  rw [hsum]
  have hpair (i : ℕ) : 2 ^ (w * i) * 2 ^ (w * k) = 2 ^ (w * (k + i)) := by
    calc
      2 ^ (w * i) * 2 ^ (w * k) = 2 ^ (w * k) * 2 ^ (w * i) := mul_comm _ _
      _ = 2 ^ ((w * k) + (w * i)) := by rw [pow_add]
      _ = 2 ^ (w * (k + i)) := by rw [mul_add]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_assoc, hpair i]

theorem pk_mul (w : ℕ) (f : ℕ → ℕ) (n : ℕ) (g : ℕ → ℕ) (m : ℕ) :
    pk w f n * pk w g m =
      pk w (fun k => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, if i + j = k then f i * g j else 0)
        (n + m) := by
  dsimp [pk]
  -- Expand product of sums into double sum
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  -- Now: ∑ i ∈ range n, ∑ j ∈ range m, (f i * 2 ^ (w * i)) * (g j * 2 ^ (w * j))
  -- Rewrite each term using the exponent identity
  have h_exp (i j : ℕ) : 2 ^ (w * i) * 2 ^ (w * j) = 2 ^ (w * (i + j)) := by
    rw [← pow_add 2 (w * i) (w * j), mul_add w i j]
  -- Rearrange products: (f i * 2^(w*i)) * (g j * 2^(w*j)) = f i * g j * 2^(w*(i+j))
  -- Use sum_congr to apply the algebra inside the sum
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => by
    calc
      (f i * 2 ^ (w * i)) * (g j * 2 ^ (w * j)) = f i * g j * (2 ^ (w * i) * 2 ^ (w * j)) := by ring
      _ = f i * g j * 2 ^ (w * (i + j)) := by rw [h_exp i j]
  ))]
  -- Now: ∑ i ∈ range n, ∑ j ∈ range m, f i * g j * 2 ^ (w * (i + j))
  -- For each (i,j), rewrite the term as a sum over k of (if i+j=k then f i * g j * 2^(w*k) else 0)
  have h_mem_range (i j : ℕ) (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range m) : i + j ∈ Finset.range (n + m) := by
    rw [Finset.mem_range] at hi hj ⊢
    exact Nat.add_lt_add hi hj
  have h_term (i j : ℕ) (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range m) : f i * g j * 2 ^ (w * (i + j)) =
      ∑ k ∈ Finset.range (n + m), (if i + j = k then f i * g j * 2 ^ (w * k) else 0) := by
    rw [Finset.sum_ite_eq]
    -- Finset.sum_ite_eq gives: ∑ k, (if i+j = k then b k else 0) = (if i+j ∈ range (n+m) then b (i+j) else 0)
    -- where b k = f i * g j * 2^(w*k)
    -- So we need to show i+j ∈ range (n+m), which we have from h_mem_range
    simp [h_mem_range i j hi hj]
  -- Now rewrite the double sum using h_term
  -- ∑ i, ∑ j, f i * g j * 2^(w*(i+j)) = ∑ i, ∑ j, ∑ k, (if i+j=k then f i * g j * 2^(w*k) else 0)
  -- Use Finset.sum_congr to apply h_term to each (i,j) pair
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => by rw [h_term i j hi hj]))]
  -- Now: ∑ i ∈ range n, ∑ j ∈ range m, ∑ k ∈ range (n+m), (if i+j = k then f i * g j * 2^(w*k) else 0)
  -- Swap sums: bring ∑ k outside
  -- First swap inner ∑ j and ∑ k
  rw [Finset.sum_congr rfl (fun i hi => by rw [Finset.sum_comm])]
  -- Now: ∑ i ∈ range n, ∑ k ∈ range (n+m), ∑ j ∈ range m, (if i+j = k then f i * g j * 2^(w*k) else 0)
  -- Then swap outer ∑ i and ∑ k
  rw [Finset.sum_comm]
  -- Now: ∑ k ∈ range (n+m), ∑ i ∈ range n, ∑ j ∈ range m, (if i+j = k then f i * g j * 2^(w*k) else 0)
  -- Factor out 2^(w*k) from the inner sum
  have h_factor (i j k : ℕ) : (if i + j = k then f i * g j * 2 ^ (w * k) else 0) =
      2 ^ (w * k) * (if i + j = k then f i * g j else 0) := by
    by_cases h : i + j = k
    · simp [h, mul_comm, mul_assoc]
    · simp [h]
  simp_rw [h_factor]
  -- Now: ∑ k ∈ range (n+m), ∑ i ∈ range n, ∑ j ∈ range m, 2^(w*k) * (if i+j=k then f i * g j else 0)
  -- Factor out 2^(w*k) from the inner sums
  simp_rw [← Finset.mul_sum]
  -- Now: ∑ k ∈ range (n+m), 2^(w*k) * (∑ i ∈ range n, ∑ j ∈ range m, if i+j = k then f i * g j else 0)
  -- Rearrange to match RHS: 2^(w*k) * S = S * 2^(w*k)
  simp_rw [mul_comm]
  -- Now: ∑ k ∈ range (n+m), (∑ i ∈ range n, ∑ j ∈ range m, if i+j = k then f i * g j else 0) * 2^(w*k)
  -- This is exactly the RHS (after dsimp [pk])


theorem mask_eq (w : ℕ) : mask w = 2 ^ w - 1 := by
  unfold mask
  simp [Nat.shiftLeft_eq]

theorem and_mask (x w : ℕ) : x &&& mask w = x % 2 ^ w := by
  simp [mask, Nat.shiftLeft_eq, one_mul]

theorem slot_eq (w x i : ℕ) : slot w x i = x / 2 ^ (w * i) % 2 ^ w := by
  unfold slot
  unfold mask
  simp [Nat.land_eq, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq_mul_pow, one_mul, Nat.and_two_pow_sub_one_eq_mod]

theorem slot_pk (w : ℕ) (f : ℕ → ℕ) (n i : ℕ) (hf : ∀ j < n, f j < 2 ^ w) :
    slot w (pk w f n) i = if i < n then f i else 0 := by
  rw [slot_eq]
  rw [pk_div w f n i hf]
  by_cases hi : i < n
  · rw [ite_eq_left hi]
    have hmin : min (n - i) 1 = 1 := by
      omega
    have hmod := pk_mod w (fun j => f (j + i)) (n - i) 1 (by
      intro j hj
      apply hf (j + i)
      omega)
    rw [hmin] at hmod
    have h_one : pk w (fun j => f (j + i)) 1 = f i := by
      simp [pk]
    have hmul : w * 1 = w := by omega
    rw [hmul] at hmod
    rw [h_one] at hmod
    rw [hmod]
  · rw [ite_eq_right hi]
    have hsub : n - i = 0 := by
      omega
    rw [hsub]
    simp [pk]

/-! ## The helpers of the kernel code -/

theorem ones_eq (w n : ℕ) (hw : 0 < w) : ones w n = pk w (fun _ => 1) n := by
  have hm : 2 ≤ 2 ^ w := by
    have h1 : 1 ≤ w := by omega
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) h1
  calc
    ones w n = Nat.div (mask (w * n)) (mask w) := rfl
    _ = Nat.div (Nat.sub (2 ^ (w * n)) 1) (Nat.sub (2 ^ w) 1) := by
      simp [mask, Nat.shiftLeft_eq]
    _ = ∑ k ∈ Finset.range n, (2 ^ w) ^ k := by
      rw [Nat.geomSum_eq hm n, ← Nat.pow_mul 2 w n]
      rfl
    _ = ∑ k ∈ Finset.range n, 2 ^ (w * k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← Nat.pow_mul]
    _ = ∑ k ∈ Finset.range n, (fun _ => 1) k * 2 ^ (w * k) := by
      simp
    _ = pk w (fun _ => 1) n := rfl

theorem packTree_eq (w : ℕ) (f : ℕ → ℕ) (d lo : ℕ) : packTree w f d lo = pk w (fun i => f (lo + i)) (2 ^ d) := by
  induction' d with d ih generalizing lo
  · simp [packTree, pk]
  · have hshift : (1 : ℕ) <<< d = 2 ^ d := by
      simpa using Nat.shiftLeft_eq_mul_pow (1 : ℕ) d
    have hrec : packTree w f (Nat.succ d) lo =
      Nat.add (packTree w f d lo) (Nat.shiftLeft (packTree w f d (Nat.add lo ((1 : ℕ) <<< d))) (Nat.mul w ((1 : ℕ) <<< d))) := by
      rfl
    rw [hrec, hshift, ih lo]
    have htemp := ih (Nat.add lo (2 ^ d))
    rw [htemp]
    unfold pk
    simp
    rw [show (2 : ℕ)^(d+1) = 2^d + 2^d by ring]
    rw [Finset.sum_range_add]
    rw [Nat.shiftLeft_eq_mul_pow]
    have hBC : (∑ x ∈ Finset.range (2 ^ d), f (lo + 2 ^ d + x) * 2 ^ (w * x)) * 2 ^ (w * (2 ^ d)) =
               ∑ x ∈ Finset.range (2 ^ d), f (lo + (2 ^ d + x)) * 2 ^ (w * (2 ^ d + x)) := by
      calc
        (∑ x ∈ Finset.range (2 ^ d), f (lo + 2 ^ d + x) * 2 ^ (w * x)) * 2 ^ (w * (2 ^ d))
            = (∑ x ∈ Finset.range (2 ^ d), f (lo + (2 ^ d + x)) * 2 ^ (w * x)) * 2 ^ (w * (2 ^ d)) := by
              refine congrArg (· * 2 ^ (w * (2 ^ d))) ?_
              refine Finset.sum_congr rfl fun x hx => ?_
              simp [add_assoc]
        _ = ∑ x ∈ Finset.range (2 ^ d), f (lo + (2 ^ d + x)) * 2 ^ (w * x) * 2 ^ (w * (2 ^ d)) := by
              rw [Finset.sum_mul]
        _ = ∑ x ∈ Finset.range (2 ^ d), f (lo + (2 ^ d + x)) * (2 ^ (w * x) * 2 ^ (w * (2 ^ d))) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              ring
        _ = ∑ x ∈ Finset.range (2 ^ d), f (lo + (2 ^ d + x)) * (2 ^ (w * (2 ^ d)) * 2 ^ (w * x)) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              simp [mul_comm]
        _ = ∑ x ∈ Finset.range (2 ^ d), f (lo + (2 ^ d + x)) * 2 ^ (w * (2 ^ d + x)) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              rw [mul_add, pow_add]
    rw [hBC]

theorem clog_spec (n : ℕ) : n ≤ 2 ^ clog n := by
  unfold clog
  by_cases h : n ≤ 1
  · -- n ≤ 1: clog n = 0, and n ≤ 1 = 2^0
    simp [h]
  · -- n > 1: clog n = Nat.log2 (n - 1) + 1
    have hsubpos : Nat.sub n 1 ≠ 0 := by
      intro hzero
      have : n - 1 = 0 := hzero
      omega
    have hlog_lt : Nat.log2 (Nat.sub n 1) < Nat.log2 (Nat.sub n 1) + 1 := by
      omega
    have hineq : Nat.sub n 1 < 2 ^ (Nat.log2 (Nat.sub n 1) + 1) :=
      ((Nat.log2_lt (n := Nat.sub n 1) (k := Nat.log2 (Nat.sub n 1) + 1) hsubpos).mp hlog_lt)
    have hnle : n ≤ 2 ^ (Nat.log2 (Nat.sub n 1) + 1) := by
      have h1le : 1 ≤ n := by omega
      have : n = Nat.sub n 1 + 1 := (Nat.sub_add_cancel h1le).symm
      omega
    simp [h]
    exact hnle

theorem map_congr_aux {α β : Type} {f g : α → β} {l : List α} (h : ∀ a ∈ l, f a = g a) :
    List.map f l = List.map g l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem splitAux_eq (w d N : ℕ) (acc : List ℕ) (hN : N < 2 ^ (w * 2 ^ d)) :
    splitAux w d N acc = (List.range (2 ^ d)).map (fun i => slot w N i) ++ acc := by
  induction d generalizing N acc with
  | zero =>
      have hN' : N < 2 ^ w := by
        simpa [Nat.pow_zero, mul_one] using hN
      have hslot0 : slot w N 0 = N := by
        rw [slot_eq w N 0]
        simp
        exact Nat.mod_eq_of_lt hN'
      simp [splitAux, hslot0]
  | succ d ih =>
      set h := 2 ^ d with hh
      have hN_bound : N < (2 ^ (w * h)) * (2 ^ (w * h)) := by
        have h_exp : w * 2 ^ (d + 1) = (w * h) + (w * h) := by
          rw [hh]
          calc
            w * 2 ^ (d + 1) = w * (2 ^ d * 2) := by rw [Nat.pow_succ]
            _ = (w * 2 ^ d) * 2 := by rw [mul_assoc]
            _ = (w * 2 ^ d) + (w * 2 ^ d) := by rw [Nat.mul_two]
            _ = (w * h) + (w * h) := by rw [hh]
        rw [h_exp] at hN
        rwa [pow_add] at hN
      have hpos_pow : 0 < 2 ^ (w * h) := by
        apply pow_pos (by norm_num) _
      have hL_lt : N &&& mask (w * h) < 2 ^ (w * h) := by
        rw [and_mask]
        exact Nat.mod_lt _ hpos_pow
      have hH_lt : N >>> (w * h) < 2 ^ (w * h) := by
        rw [Nat.shiftRight_eq_div_pow]
        apply (Nat.div_lt_iff_lt_mul hpos_pow).mpr
        simpa [mul_comm] using hN_bound
      -- Key lemma 1: slot of low part equals slot of original for indices < h
      have hL_eq : ∀ i, i < h → slot w (N &&& mask (w * h)) i = slot w N i := by
        intro i hi
        rw [slot_eq w (N &&& mask (w * h)) i, slot_eq w N i, and_mask N (w * h)]
        have h_pow_eq : 2 ^ (w * h) = 2 ^ (w * i) * 2 ^ (w * (h - i)) := by
          have h_mul : w * h = w * i + w * (h - i) := by
            calc
              w * h = w * (i + (h - i)) := by rw [Nat.add_sub_cancel' (Nat.le_of_lt hi)]
              _ = w * i + w * (h - i) := by rw [Nat.mul_add]
          rw [h_mul, pow_add]
        rw [h_pow_eq]
        rw [Nat.mod_mul_right_div_self]
        have h_sub_pos : 0 < h - i := Nat.sub_pos_of_lt hi
        have h_pow_factor : 2 ^ (w * (h - i)) = 2 ^ w * 2 ^ (w * ((h - i) - 1)) := by
          have h_exp : w * (h - i) = w + w * ((h - i) - 1) := by
            calc
              w * (h - i) = w * (1 + ((h - i) - 1)) := by
                rw [Nat.add_sub_cancel' (Nat.one_le_of_lt h_sub_pos)]
              _ = w * 1 + w * ((h - i) - 1) := by rw [Nat.mul_add]
              _ = w + w * ((h - i) - 1) := by rw [mul_one]
          rw [h_exp, pow_add]
        rw [h_pow_factor]
        rw [Nat.mod_mul_right_mod]
      -- Key lemma 2: slot of high part equals shifted slot
      have hH_eq : ∀ i, i < h → slot w (N >>> (w * h)) i = slot w N (h + i) := by
        intro i hi
        rw [slot_eq w (N >>> (w * h)) i, slot_eq w N (h + i)]
        rw [Nat.shiftRight_eq_div_pow]
        rw [Nat.div_div_eq_div_mul]
        have h_exp : w * (h + i) = w * h + w * i := by ring
        rw [h_exp, pow_add]
      -- Expand splitAux for d+1
      have h_split : splitAux w (d + 1) N acc = splitAux w d (N &&& mask (w * h)) (splitAux w d (N >>> (w * h)) acc) := by
        simp [hh, splitAux, Nat.one_shiftLeft, mul_comm]
      rw [h_split]
      rw [ih (N &&& mask (w * h)) (splitAux w d (N >>> (w * h)) acc) hL_lt]
      rw [ih (N >>> (w * h)) acc hH_lt]
      -- Goal: A ++ (B ++ acc) = C ++ acc  where A = map (slot w L) (range h), B = map (slot w H) (range h), C = map (slot w N) (range (2^(d+1)))
      -- Rewrite LHS: A ++ (B ++ acc) = (A ++ B) ++ acc
      rw [← List.append_assoc]
      -- Goal: (A ++ B) ++ acc = C ++ acc
      -- Cancel acc on both sides
      apply congrArg (· ++ acc)
      -- Goal: A ++ B = C
      -- Expand C: C = map (slot w N) (range (2*h)) = map (slot w N) (range (h + h))
      rw [show (2 : ℕ) ^ (d + 1) = 2 * h by
        rw [hh, Nat.pow_succ, mul_comm]]
      rw [show (2 : ℕ) * h = h + h by omega]
      rw [List.range_add]
      rw [List.map_append]
      -- Goal: A ++ B = (map (slot w N) (range h)) ++ (map (slot w N) (map (h + ·) (range h)))
      -- But A = map (slot w (N &&& mask (w*h))) (range h), B = map (slot w (N >>> (w*h))) (range h)
      -- Use hL_eq and hH_eq
      have hA : (List.range h).map (slot w (N &&& mask (w * h))) = (List.range h).map (slot w N) := by
        apply map_congr_aux
        intro i hi
        have hi_lt : i < h := by simpa [List.mem_range] using hi
        apply hL_eq i hi_lt
      have hB : (List.range h).map (slot w (N >>> (w * h))) = (List.range h).map (fun i => slot w N (h + i)) := by
        apply map_congr_aux
        intro i hi
        have hi_lt : i < h := by simpa [List.mem_range] using hi
        apply hH_eq i hi_lt
      rw [hA, hB]
      -- Goal: map (slot w N) (range h) ++ map (fun i => slot w N (h + i)) (range h)
      --     = map (slot w N) (range h) ++ map (slot w N) (map (h + ·) (range h))
      -- Cancel the first term
      apply congrArg (fun xs => (List.range h).map (slot w N) ++ xs)
      -- Goal: map (fun i => slot w N (h + i)) (range h) = map (slot w N) (map (h + ·) (range h))
      simp [List.map_map, Function.comp]

theorem split_eq (w n N : ℕ) (hN : N < 2 ^ (w * 2 ^ clog n)) :
    split w n N = (List.range (2 ^ clog n)).map (fun i => slot w N i) := by
  rw [FrogModel.D3.LaneD.K.split]
  rw [FrogModel.D3.LaneD.K.splitAux_eq w (clog n) N [] hN]
  simp

open Finset in
theorem natFold_inv {α : Type} (n : ℕ) (init : α) (f : ℕ → α → α) (P : ℕ → α → Prop) (h0 : P 0 init)
    (hs : ∀ j a, j < n → P j a → P (j + 1) (f j a)) : P n (natFold n init f) := by
  have key : ∀ j ≤ n, P j (natFold j init f) := by
    intro j
    induction j with
    | zero => intro _; exact h0
    | succ j ih => intro hj; exact hs j _ (by omega) (ih (by omega))
  exact key n le_rfl

open Finset in
theorem lvl_fold (W : ℕ) (L : List ℕ) (j : ℕ) :
    natFold j (([] : List ℕ), L) (fun _ (st : List ℕ × List ℕ) =>
      (Nat.add (hd st.2) (Nat.shiftLeft (hd (tl st.2)) W) :: st.1, tl (tl st.2))) =
    (((List.range j).map fun k => L.getD (2 * k) 0 + L.getD (2 * k + 1) 0 * 2 ^ W).reverse, L.drop (2 * j)) := by
  refine natFold_inv j _ _ (fun j a => a =
    (((List.range j).map fun k => L.getD (2 * k) 0 + L.getD (2 * k + 1) 0 * 2 ^ W).reverse, L.drop (2 * j)))
    rfl ?_
  intro i a _ ha
  subst ha
  have h1 : hd (L.drop (2 * i)) = L.getD (2 * i) 0 := by
    simp only [hd, List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
  have h2 : hd (tl (L.drop (2 * i))) = L.getD (2 * i + 1) 0 := by
    simp only [hd, tl, List.tail_drop, List.headD_eq_head?_getD, List.head?_drop,
      List.getD_eq_getElem?_getD]
  refine Prod.ext ?_ ?_
  · simp only [h1, h2, Nat.add_eq, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [show Nat.shiftLeft (L.getD (2 * i + 1) 0) W = L.getD (2 * i + 1) 0 * 2 ^ W from Nat.shiftLeft_eq _ _]
  · simp only [tl, List.tail_drop]
    congr 1

open Finset in
theorem lvl_eq (W : ℕ) (L : List ℕ) :
    (natFold (Nat.div (Nat.add L.length 1) 2) (([] : List ℕ), L) (fun _ (st : List ℕ × List ℕ) =>
      (Nat.add (hd st.2) (Nat.shiftLeft (hd (tl st.2)) W) :: st.1, tl (tl st.2)))).1.reverse =
    (List.range ((L.length + 1) / 2)).map fun k => L.getD (2 * k) 0 + L.getD (2 * k + 1) 0 * 2 ^ W := by
  rw [lvl_fold, List.reverse_reverse]
  rfl

open Finset in
theorem getD_map_range (n k : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map g).getD k 0 = if k < n then g k else 0 := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

open Finset in
theorem pk_halves (w h : ℕ) (H : ℕ → ℕ) :
    pk w H h + pk w (fun i => H (h + i)) h * 2 ^ (w * h) = pk w H (h + h) := by
  unfold pk
  rw [sum_range_add, sum_mul]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  show H (h + i) * 2 ^ (w * i) * 2 ^ (w * h) = H (h + i) * 2 ^ (w * (h + i))
  rw [mul_assoc, ← pow_add, mul_add, add_comm (w * i)]

open Finset in
theorem packRows_eq (w : ℕ) (l : List ℕ) : packRows w l = pk w (fun i => l.getD i 0) l.length := by
  unfold packRows
  simp only [lvl_eq]
  set P : ℕ → ℕ → ℕ := fun j k => pk w (fun i => l.getD (k * 2 ^ j + i) 0) (2 ^ j) with hP
  have key := natFold_inv (clog l.length) (w, l)
    (fun _ (st : ℕ × List ℕ) => (Nat.mul 2 st.1, (List.range ((st.2.length + 1) / 2)).map
      fun k => st.2.getD (2 * k) 0 + st.2.getD (2 * k + 1) 0 * 2 ^ st.1))
    (fun j a => a.1 = w * 2 ^ j ∧ (∀ k, a.2.getD k 0 = P j k) ∧ l.length ≤ a.2.length * 2 ^ j) ?_ ?_
  · obtain ⟨_, hget, _⟩ := key
    have hhd : ∀ L : List ℕ, L.headD 0 = L.getD 0 0 := fun L => by cases L <;> rfl
    rw [hhd, hget 0, hP]
    simp only [zero_mul, zero_add]
    refine pk_extend w _ _ _ (clog_spec _) fun i hi _ => ?_
    exact List.getD_eq_default _ _ hi
  · refine ⟨by simp, fun k => ?_, by simp⟩
    simp only [hP, pow_zero, mul_one]
    unfold pk
    simp
  · rintro j ⟨W, L⟩ _ ⟨hW, hget, hlen⟩
    simp only at hW hget hlen ⊢
    refine ⟨by rw [Nat.mul_eq, hW, pow_succ]; ring, fun k => ?_, ?_⟩
    · rw [getD_map_range]
      split_ifs with hk
      · rw [hget, hget, hW, hP]
        simp only []
        rw [show w * 2 ^ j = w * 2 ^ j from rfl]
        have := pk_halves w (2 ^ j) (fun i => l.getD (k * 2 ^ (j + 1) + i) 0)
        rw [show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by rw [pow_succ]; ring] at this
        rw [← this]
        congr 1
        · refine pk_congr _ _ _ _ fun i _ => ?_
          rw [show 2 * k * 2 ^ j = k * 2 ^ (j + 1) by rw [pow_succ]; ring]
        · congr 1
          refine pk_congr _ _ _ _ fun i _ => ?_
          rw [show (2 * k + 1) * 2 ^ j + i = k * 2 ^ (j + 1) + (2 ^ j + i) by rw [pow_succ]; ring]
      · rw [hP]
        simp only []
        unfold pk
        refine (sum_eq_zero fun i _ => ?_).symm
        show l.getD (k * 2 ^ (j + 1) + i) 0 * 2 ^ (w * i) = 0
        rw [List.getD_eq_default _ _ ?_, zero_mul]
        have h2 : L.length ≤ 2 * k := by omega
        calc l.length ≤ L.length * 2 ^ j := hlen
          _ ≤ 2 * k * 2 ^ j := Nat.mul_le_mul_right _ h2
          _ = k * 2 ^ (j + 1) := by rw [pow_succ]; ring
          _ ≤ k * 2 ^ (j + 1) + i := Nat.le_add_right _ _
    · simp only [List.length_map, List.length_range]
      calc l.length ≤ L.length * 2 ^ j := hlen
        _ ≤ 2 * ((L.length + 1) / 2) * 2 ^ j := Nat.mul_le_mul_right _ (by omega)
        _ = (L.length + 1) / 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring

theorem minN_eq (a b : ℕ) : minN a b = min a b := by
  unfold minN
  exact tsub_tsub_eq_min a b

theorem maxN_eq (a b : ℕ) : maxN a b = max a b := by
  unfold maxN
  by_cases h : a ≤ b
  · have hsub : Nat.sub a b = 0 := Nat.sub_eq_zero_of_le h
    have hmax : max a b = b := Nat.max_eq_right h
    rw [hsub, hmax]
    simp
  · have hle : b ≤ a := by omega
    have hmax : max a b = a := Nat.max_eq_left hle
    rw [hmax]
    simpa [add_comm] using Nat.sub_add_cancel hle

theorem choose_eq (n k : ℕ) : FrogModel.D3.LaneD.K.choose n k = n.choose k := by
  induction' k with k ih
  · simp [FrogModel.D3.LaneD.K.choose, natFold]
  · rw [FrogModel.D3.LaneD.K.choose]
    dsimp [natFold]
    dsimp [FrogModel.D3.LaneD.K.choose] at ih
    dsimp [natFold] at ih
    rw [ih]
    have h := Nat.choose_succ_right_eq n k
    rw [← h]
    exact Nat.mul_div_cancel (n.choose (k + 1)) (Nat.zero_lt_succ k)

theorem fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      dsimp [fact, natFold] at *
      simp [ih, Nat.factorial_succ, mul_comm]

theorem getN_eq (l : List ℕ) (n : ℕ) : getN l n = l.getD n 0 := by
  have h_dropN_eq_drop : ∀ (l : List ℕ) (n : ℕ), dropN n l = l.drop n := by
    intro l n
    induction' n with n ih generalizing l
    · simp [dropN, natFold]
    · -- goal: dropN (n+1) l = l.drop (n+1)
      -- dropN (n+1) l = tl (dropN n l) = tl (l.drop n) = l.drop (n+1)
      calc
        dropN (n+1) l = tl (dropN n l) := by
          simp [dropN, natFold, tl]
        _ = tl (l.drop n) := by rw [ih l]
        _ = l.drop (n+1) := by simp [tl, List.tail_drop]
  induction' n with n ih generalizing l
  · -- n = 0: getN l 0 = l.getD 0 0
    cases l <;> simp [getN, dropN, hd, tl, natFold, List.getD]
  · -- n = n+1
    rw [getN, h_dropN_eq_drop]
    -- goal: hd (l.drop (n+1)) = l.getD (n+1) 0
    -- hd x = x.headD 0, and simp rewrites (l.drop (n+1)).headD 0 to l.getD (n+1) 0
    simp [hd]

theorem bad_eq_zero (a b : ℕ) : bad a b = 0 ↔ a ≤ b := by
  dsimp [bad]
  constructor
  · intro h
    by_contra! hle
    have : cond (Nat.ble a b) 0 1 = 1 := by
      simp [Nat.ble_eq, hle]
    rw [this] at h
    exact Nat.one_ne_zero h
  · intro h
    have hble : Nat.ble a b = true := by
      simpa [Nat.ble_eq] using h
    simp [hble]

theorem natFold_add (n : ℕ) (g : ℕ → ℕ) : natFold n 0 (fun i acc => Nat.add acc (g i)) = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero =>
      simp [natFold]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simp [natFold]
      simpa [natFold] using ih


/-! ## Tables: rows of packed naturals -/

theorem pk_nest (w S : ℕ) (f : ℕ → ℕ → ℕ) (m n : ℕ) :
    pk (S * w) (fun e => pk w (f e) n) m = pk2 w S f m n := by
  dsimp [pk, pk2]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  refine Finset.sum_congr rfl fun g hg => ?_
  calc
    (f e g * 2 ^ (w * g)) * 2 ^ ((S * w) * e) = f e g * (2 ^ (w * g) * 2 ^ ((S * w) * e)) := by ring
    _ = f e g * 2 ^ ((w * g) + ((S * w) * e)) := by rw [pow_add]
    _ = f e g * 2 ^ (w * (S * e + g)) := by ring

theorem pk2_extend (w S : ℕ) (f : ℕ → ℕ → ℕ) (m n n' : ℕ) (hn : n ≤ n') (hz : ∀ e < m, ∀ g, n ≤ g → g < n' → f e g = 0) :
    pk2 w S f m n' = pk2 w S f m n := by
  simp only [pk2]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_range_add_sum_Ico (f := fun g => f e g * 2 ^ (w * (S * e + g))) hn]
  have hzero : ∑ g ∈ Finset.Ico n n', f e g * 2 ^ (w * (S * e + g)) = 0 := by
    apply Finset.sum_eq_zero
    intro g hg
    rcases Finset.mem_Ico.mp hg with ⟨hgn, hgn'⟩
    rw [hz e (Finset.mem_range.mp he) g hgn hgn', zero_mul]
  rw [hzero, add_zero]

open Finset in
theorem pk2_mul (w S : ℕ) (f : ℕ → ℕ → ℕ) (m n : ℕ) (g : ℕ → ℕ → ℕ) (m' n' : ℕ) :
    pk2 w S f m n * pk2 w S g m' n' =
      pk2 w S (fun e s => ∑ e1 ∈ Finset.range m, ∑ e2 ∈ Finset.range m', ∑ g1 ∈ Finset.range n,
        ∑ g2 ∈ Finset.range n', if e1 + e2 = e ∧ g1 + g2 = s then f e1 g1 * g e2 g2 else 0) (m + m') (n + n') := by
  unfold pk2
  rw [sum_mul_sum]
  simp_rw [sum_mul_sum, sum_mul]
  symm
  conv_lhs =>
    enter [2, e]
    rw [sum_comm]
    enter [2, e1]
    rw [sum_comm]
    enter [2, e2]
    rw [sum_comm]
    enter [2, g1]
    rw [sum_comm]
  conv_lhs =>
    rw [sum_comm]
    enter [2, e1]
    rw [sum_comm]
    enter [2, e2]
    rw [sum_comm]
    enter [2, g1]
    rw [sum_comm]
  refine sum_congr rfl fun e1 he1 => sum_congr rfl fun e2 he2 => sum_congr rfl fun g1 hg1 =>
    sum_congr rfl fun g2 hg2 => ?_
  rw [mem_range] at he1 he2 hg1 hg2
  rw [sum_eq_single (e1 + e2) (fun e _ he => sum_eq_zero fun s _ => by
      rw [ite_eq_right (show ¬(e1 + e2 = e ∧ g1 + g2 = s) by omega), zero_mul])
    (fun h => absurd (mem_range.2 (by omega)) h)]
  rw [sum_eq_single (g1 + g2) (fun s _ hs => by
      rw [ite_eq_right (show ¬(e1 + e2 = e1 + e2 ∧ g1 + g2 = s) by omega), zero_mul])
    (fun h => absurd (mem_range.2 (by omega)) h)]
  rw [ite_eq_left (show e1 + e2 = e1 + e2 ∧ g1 + g2 = g1 + g2 from ⟨rfl, rfl⟩)]
  rw [show w * (S * (e1 + e2) + (g1 + g2)) = w * (S * e1 + g1) + w * (S * e2 + g2) by ring, pow_add]
  ring

theorem pk2_eq_pk (w S : ℕ) (f : ℕ → ℕ → ℕ) (m n : ℕ) (hn : n ≤ S) :
    pk2 w S f m n = pk w (fun i => if i % S < n then f (i / S) (i % S) else 0) (m * S) := by
  induction' m with m ih
  · simp [pk2, pk]
  · -- inductive step: m → m+1
    have hL : pk2 w S f (m+1) n = pk w (fun i => if i % S < n then f (i / S) (i % S) else 0) (m * S) +
        ∑ g ∈ Finset.range n, f m g * 2 ^ (w * (S * m + g)) := by
      rw [pk2, Finset.sum_range_succ, ← ih, pk2]
    have hR : pk w (fun i => if i % S < n then f (i / S) (i % S) else 0) ((m+1)*S) =
        pk w (fun i => if i % S < n then f (i / S) (i % S) else 0) (m * S) +
        ∑ i ∈ Finset.range n, f m i * 2 ^ (w * (m * S + i)) := by
      rw [show ((m+1)*S : ℕ) = m*S + S by rw [Nat.succ_mul, Nat.add_comm], pk, Finset.sum_range_add]
      -- Goal: pk w ... (m*S) + ∑ i ∈ range S, ... = pk w ... (m*S) + ∑ i ∈ range n, f m i * 2 ^ (w * (m*S + i))
      -- Simplify the second sum on LHS
      have hmod : ∀ i, i < S → (m*S + i) % S = i := by
        intro i hi
        calc
          (m*S + i) % S = (i + m*S) % S := by rw [add_comm]
          _ = (i + S*m) % S := by rw [mul_comm m S]
          _ = i % S := by rw [Nat.add_mul_mod_self_left]
          _ = i := Nat.mod_eq_of_lt hi
      have hdiv : ∀ i, i < S → (m*S + i) / S = m := by
        intro i hi
        rcases eq_or_ne S 0 with (hS | hS)
        · exfalso; exact Nat.not_lt_zero i (by rwa [hS] at hi)
        · have hpos : 0 < S := Nat.pos_of_ne_zero hS
          calc
            (m*S + i) / S = (i + m*S) / S := by rw [add_comm]
            _ = (i + S*m) / S := by rw [mul_comm m S]
            _ = i / S + m := by rw [Nat.add_mul_div_left _ _ hpos]
            _ = 0 + m := by rw [Nat.div_eq_of_lt hi]
            _ = m := by simp
      -- Rewrite the second sum using hmod and hdiv
      have hsum2 : (∑ x ∈ Finset.range S, (if (m*S + x) % S < n then f ((m*S + x) / S) ((m*S + x) % S) else 0) * 2 ^ (w * (m*S + x))) =
          ∑ i ∈ Finset.range n, f m i * 2 ^ (w * (m * S + i)) := by
        calc
          (∑ x ∈ Finset.range S, (if (m*S + x) % S < n then f ((m*S + x) / S) ((m*S + x) % S) else 0) * 2 ^ (w * (m*S + x)))
              = (∑ x ∈ Finset.range S, (if x < n then f m x else 0) * 2 ^ (w * (m*S + x))) := by
            refine Finset.sum_congr rfl (fun x hx => ?_)
            rw [Finset.mem_range] at hx
            rw [hmod x hx, hdiv x hx]
          _ = ∑ i ∈ Finset.range n, f m i * 2 ^ (w * (m * S + i)) := by
            calc
              (∑ x ∈ Finset.range S, (if x < n then f m x else 0) * 2 ^ (w * (m * S + x)))
                  = (∑ x ∈ Finset.range S, if x < n then f m x * 2 ^ (w * (m * S + x)) else 0) := by
                refine Finset.sum_congr rfl (fun x hx => ?_)
                by_cases hxn : x < n
                · simp [hxn]
                · simp [hxn]
              _ = ∑ x ∈ (Finset.range S).filter (fun x => x < n), f m x * 2 ^ (w * (m * S + x)) := by
                rw [Finset.sum_filter]
              _ = ∑ x ∈ Finset.range n, f m x * 2 ^ (w * (m * S + x)) := by
                have hfilter : (Finset.range S).filter (fun x => x < n) = Finset.range n := by
                  ext x; simp [Finset.mem_range, Finset.mem_filter]
                  exact fun hxn => Nat.lt_of_lt_of_le hxn hn
                rw [hfilter]
      -- Now the goal is: (sum over range (m*S)) + (sum over range S) = pk w ... (m*S) + (sum over range n)
      -- Fold the RHS pk back to sum, then cancel
      rw [← pk, add_left_cancel_iff]
      -- Goal: (sum over range S) = (sum over range n)
      rw [hsum2]
    rw [hL, hR]
    -- Goal: (pk w ... (m*S) + sum1) = (pk w ... (m*S) + sum2)
    -- where sum1 = ∑ g ∈ range n, f m g * 2 ^ (w * (S * m + g))
    -- and   sum2 = ∑ i ∈ range n, f m i * 2 ^ (w * (m * S + i))
    -- Cancel the common term
    rw [add_left_cancel_iff]
    -- Goal: ∑ g ∈ range n, f m g * 2 ^ (w * (S * m + g)) = ∑ i ∈ range n, f m i * 2 ^ (w * (m * S + i))
    -- These are equal by commutativity of multiplication
    simp [Nat.mul_comm S m, Nat.mul_comm w]

theorem mask_mul (w n : ℕ) : mask (n * w) = pk w (fun _ => 2 ^ w - 1) n := by
  have hm : mask (n * w) = 2 ^ (n * w) - 1 := mask_eq (n * w)
  rw [hm, pk]
  set a := 2 ^ w with ha
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact Nat.one_le_two_pow (n := w)
  revert hm
  induction' n with n ih
  · intro hm; simp
  · intro hm
    rw [Finset.sum_range_succ]
    -- Goal: 2 ^ ((n + 1) * w) - 1 = (∑ i ∈ Finset.range n, (a - 1) * 2 ^ (w * i)) + (a - 1) * 2 ^ (w * n)
    have hpow : 2 ^ ((n + 1) * w) = 2 ^ (n * w) * a := by
      rw [show (n + 1) * w = n * w + w by ring, pow_add, ha]
    rw [hpow]
    -- Goal: 2 ^ (n * w) * a - 1 = (∑ i ∈ Finset.range n, (a - 1) * 2 ^ (w * i)) + (a - 1) * 2 ^ (w * n)
    have h_ih : 2 ^ (n * w) - 1 = ∑ i ∈ Finset.range n, (a - 1) * 2 ^ (w * i) := ih (mask_eq (n * w))
    rw [← h_ih]
    -- Goal: 2 ^ (n * w) * a - 1 = (2 ^ (n * w) - 1) + (a - 1) * 2 ^ (w * n)
    -- Need to show: a * 2^(n*w) - 1 = (2^(n*w) - 1) + (a - 1) * 2^(n*w)
    -- Since 2^(w*n) = 2^(n*w)
    rw [mul_comm w n]
    -- Goal: 2 ^ (n * w) * a - 1 = (2 ^ (n * w) - 1) + (a - 1) * 2 ^ (n * w)
    rw [mul_comm (2 ^ (n * w)) a]
    -- Goal: a * 2 ^ (n * w) - 1 = (2 ^ (n * w) - 1) + (a - 1) * 2 ^ (n * w)
    set b := 2 ^ (n * w) with hb
    have hb1 : 1 ≤ b := by
      rw [hb]
      exact Nat.one_le_two_pow (n := n * w)
    have hsum : (a - 1) * b + b = a * b := by
      calc
        (a - 1) * b + b = ((a - 1) + 1) * b := by ring
        _ = a * b := by rw [Nat.sub_add_cancel ha1]
    calc
      a * b - 1 = ((a - 1) * b + b) - 1 := by rw [hsum]
      _ = (a - 1) * b + (b - 1) := by rw [Nat.add_sub_assoc hb1]
      _ = (b - 1) + (a - 1) * b := by ring

open Finset in
theorem land_split (k a b a' b' : ℕ) (ha : a < 2 ^ k) (ha' : a' < 2 ^ k) :
    (2 ^ k * b + a) &&& (2 ^ k * b' + a') = 2 ^ k * (b &&& b') + (a &&& a') := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ ha',
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow a ha'), Nat.testBit_and, Nat.testBit_and]
  split_ifs <;> rfl

open Finset in
theorem pk_land_sel (w : ℕ) (h : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] (n : ℕ) (hh : ∀ i < n, h i < 2 ^ w) :
    pk w h n &&& pk w (fun i => if p i then 2 ^ w - 1 else 0) n = pk w (fun i => if p i then h i else 0) n := by
  induction n with
  | zero => simp [pk_zero]
  | succ n ih =>
    have hs : ∀ i < n, (if p i then 2 ^ w - 1 else 0) < 2 ^ w := by
      intro i _
      split_ifs
      · exact Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos
      · exact Nat.two_pow_pos w
    rw [pk_succ, pk_succ, pk_succ, add_comm (pk w h n), add_comm (pk w _ n), add_comm (pk w _ n),
      mul_comm (h n), mul_comm (if p n then 2 ^ w - 1 else 0), mul_comm (if p n then h n else 0),
      land_split _ _ _ _ _ (pk_lt w h n fun i hi => hh i (by omega)) (pk_lt w _ n hs),
      ih fun i hi => hh i (by omega)]
    congr 2
    split_ifs
    · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hh n (by omega))]
    · exact Nat.and_zero _

open Finset in
theorem pk_cut (w : ℕ) (G : ℕ → ℕ) (n L : ℕ) (hnL : n ≤ L) (G' : ℕ → ℕ) (hG : ∀ i < n, G' i = G i)
    (hz : ∀ i, n ≤ i → i < L → G' i = 0) : pk w G' L = pk w G n := by
  rw [pk_extend w G' n L hnL hz]
  exact pk_congr _ _ _ _ hG

open Finset in
theorem pk2_land_tmask (w S : ℕ) (f : ℕ → ℕ → ℕ) (m n k r : ℕ) (hn : n ≤ S) (hr : r ≤ S)
    (hf : ∀ e < m, ∀ g < n, f e g < 2 ^ w) :
    pk2 w S f m n &&& (mask (r * w) * ones (S * w) k) = pk2 w S f (min m k) (min n r) := by
  rcases Nat.eq_zero_or_pos (S * w) with h0 | hSw
  · have hz : ∀ (a b : ℕ), a ≤ m → b ≤ n → pk2 w S f a b = 0 := by
      intro a b ha hb
      rcases Nat.mul_eq_zero.1 h0 with hS | hw
      · have : b = 0 := by omega
        subst this
        simp [pk2]
      · refine sum_eq_zero fun e he => sum_eq_zero fun g hg => ?_
        rw [mem_range] at he hg
        have := hf e (by omega) g (by omega)
        rw [hw, pow_zero] at this
        rw [Nat.lt_one_iff.1 this, zero_mul]
    rw [hz m n le_rfl le_rfl, hz _ _ (min_le_left _ _) (min_le_left _ _), Nat.zero_and]
  · have hS : 0 < S := Nat.pos_of_mul_pos_right hSw
    have hw : 0 < w := Nat.pos_of_mul_pos_left hSw
    set L := max m k * S with hL
    have hdivlt : ∀ i a, i / S < a ↔ i < a * S := fun i a => Nat.div_lt_iff_lt_mul hS
    have hB : mask (r * w) * ones (S * w) k =
        pk w (fun i => if i / S < k ∧ i % S < r then 2 ^ w - 1 else 0) L := by
      rw [ones_eq _ _ hSw, pk_smul, mask_mul]
      simp only [mul_one]
      rw [pk_nest w S (fun _ _ => 2 ^ w - 1) k r, pk2_eq_pk w S _ k r hr]
      refine (pk_cut w _ (k * S) L (Nat.mul_le_mul_right _ (le_max_right _ _)) _ (fun i hi => ?_)
        (fun i hi _ => ?_)).symm
      · have : i / S < k := (hdivlt i k).2 hi
        simp only [this, true_and]
      · have : ¬(i / S < k) := fun h => by have := (hdivlt i k).1 h; omega
        simp only [this, false_and, ite_false]
    have hA : pk2 w S f m n = pk w (fun i => if i / S < m ∧ i % S < n then f (i / S) (i % S) else 0) L := by
      rw [pk2_eq_pk w S f m n hn]
      refine (pk_cut w _ (m * S) L (Nat.mul_le_mul_right _ (le_max_left _ _)) _ (fun i hi => ?_)
        (fun i hi _ => ?_)).symm
      · have : i / S < m := (hdivlt i m).2 hi
        simp only [this, true_and]
      · have : ¬(i / S < m) := fun h => by have := (hdivlt i m).1 h; omega
        simp only [this, false_and, ite_false]
    have hC : pk2 w S f (min m k) (min n r) =
        pk w (fun i => if i / S < min m k ∧ i % S < min n r then f (i / S) (i % S) else 0) L := by
      rw [pk2_eq_pk w S f _ _ (le_trans (min_le_left _ _) hn)]
      refine (pk_cut w _ (min m k * S) L (Nat.mul_le_mul_right _ (by omega)) _ (fun i hi => ?_)
        (fun i hi _ => ?_)).symm
      · have : i / S < min m k := (hdivlt i _).2 hi
        simp only [this, true_and]
      · have : ¬(i / S < min m k) := fun h => by have := (hdivlt i _).1 h; omega
        simp only [this, false_and, ite_false]
    rw [hA, hB, hC, pk_land_sel w _ (fun i => i / S < k ∧ i % S < r) L]
    · refine pk_congr _ _ _ _ fun i _ => ?_
      by_cases h1 : i / S < k ∧ i % S < r
      · rw [ite_eq_left h1]
        by_cases h2 : i / S < m ∧ i % S < n
        · rw [ite_eq_left h2, ite_eq_left (show i / S < min m k ∧ i % S < min n r by omega)]
        · rw [ite_eq_right h2, ite_eq_right (show ¬(i / S < min m k ∧ i % S < min n r) by omega)]
      · rw [ite_eq_right h1, ite_eq_right (show ¬(i / S < min m k ∧ i % S < min n r) by omega)]
    · intro i _
      split_ifs with h
      · exact hf _ h.1 _ h.2
      · exact Nat.two_pow_pos w

theorem split_pk2 (w S : ℕ) (f : ℕ → ℕ → ℕ) (n r M : ℕ) (hr : r ≤ S) (hf : ∀ e < n, ∀ g < r, f e g < 2 ^ w) :
    getN (split (S * w) n (pk2 w S f n r)) M = if M < n then pk w (f M) r else 0 := by
  have h_pk_nest : pk2 w S f n r = pk (S * w) (fun e => pk w (f e) r) n := by
    rw [pk_nest]
  rw [h_pk_nest]
  have h_bound : pk (S * w) (fun e => pk w (f e) r) n < 2 ^ ((S * w) * 2 ^ clog n) := by
    have h_lt : pk (S * w) (fun e => pk w (f e) r) n < 2 ^ ((S * w) * n) := by
      apply pk_lt (S * w) (fun e => pk w (f e) r) n
      intro i hi
      have h_lt' : pk w (f i) r < 2 ^ (w * r) := by
        apply pk_lt w (f i) r
        intro j hj
        exact hf i hi j hj
      have h_le : 2 ^ (w * r) ≤ 2 ^ (S * w) := by
        have : w * r ≤ S * w := by
          calc
            w * r ≤ w * S := Nat.mul_le_mul_left w hr
            _ = S * w := Nat.mul_comm w S
        exact Nat.pow_le_pow_right (by omega) this
      exact lt_of_lt_of_le h_lt' h_le
    have h_clog : n ≤ 2 ^ clog n := clog_spec n
    have h_mul : (S * w) * n ≤ (S * w) * 2 ^ clog n :=
      Nat.mul_le_mul_left (S * w) h_clog
    have h_pow : 2 ^ ((S * w) * n) ≤ 2 ^ ((S * w) * 2 ^ clog n) :=
      Nat.pow_le_pow_right (by omega) h_mul
    exact lt_of_lt_of_le h_lt h_pow
  rw [split_eq (S * w) n (pk (S * w) (fun e => pk w (f e) r) n) h_bound]
  rw [getN_eq]
  by_cases hM_lt : M < 2 ^ clog n
  · have h_len : M < ((List.range (2 ^ clog n)).map (fun i => slot (S * w) (pk (S * w) (fun e => pk w (f e) r) n) i)).length := by
      simpa [List.length_map, List.length_range] using hM_lt
    rw [List.getD_eq_getElem _ _ h_len]
    rw [List.getElem_map]
    rw [List.getElem_range (by simpa [List.length_range] using hM_lt)]
    have h_slot_cond : ∀ j < n, (fun e => pk w (f e) r) j < 2 ^ (S * w) := by
      intro j hj
      have h_lt' : pk w (f j) r < 2 ^ (w * r) := by
        apply pk_lt w (f j) r
        intro g hg
        exact hf j hj g hg
      have h_le : 2 ^ (w * r) ≤ 2 ^ (S * w) := by
        have : w * r ≤ S * w := by
          calc
            w * r ≤ w * S := Nat.mul_le_mul_left w hr
            _ = S * w := Nat.mul_comm w S
        exact Nat.pow_le_pow_right (by omega) this
      exact lt_of_lt_of_le h_lt' h_le
    have h_slot := slot_pk (S * w) (fun e => pk w (f e) r) n M h_slot_cond
    rw [h_slot]
  · have h_len : ((List.range (2 ^ clog n)).map (fun i => slot (S * w) (pk (S * w) (fun e => pk w (f e) r) n) i)).length ≤ M := by
      simpa [List.length_map, List.length_range] using hM_lt
    rw [List.getD_eq_default _ _ h_len]
    by_cases hM_n : M < n
    · have : n ≤ 2 ^ clog n := clog_spec n
      have : M < 2 ^ clog n := lt_of_lt_of_le hM_n this
      exact absurd this hM_lt
    · rw [ite_eq_right hM_n]

open Finset in
theorem omQ_rec (X NN M : ℕ) :
    (∑ i ∈ range (NN + 1), (NN - i).choose M * X ^ i) +
        ∑ i ∈ range (NN + 1), (NN - i).choose (M + 1) * X ^ i =
      NN.choose M + NN.choose (M + 1) + X * ∑ i ∈ range (NN + 1), (NN - i).choose (M + 1) * X ^ i := by
  rw [← sum_add_distrib]
  have h1 : ∀ i ∈ range (NN + 1), (NN - i).choose M * X ^ i + (NN - i).choose (M + 1) * X ^ i =
      (NN - i + 1).choose (M + 1) * X ^ i := by
    intro i _
    rw [← add_mul, Nat.choose_succ_succ']
  rw [sum_congr rfl h1, sum_range_succ', mul_sum, sum_range_succ]
  have hA : ∑ i ∈ range NN, (NN - (i + 1) + 1).choose (M + 1) * X ^ (i + 1) =
      ∑ i ∈ range NN, X * ((NN - i).choose (M + 1) * X ^ i) := by
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [show NN - (i + 1) + 1 = NN - i by omega, pow_succ]
    ring
  rw [hA, Nat.sub_self, Nat.choose_zero_succ, Nat.sub_zero, Nat.choose_succ_succ', pow_zero]
  ring

open Finset in
theorem omR_eq (SW NN M : ℕ) :
    pk SW (fun i => (NN - i).choose M * 4 ^ i) (NN + 1) =
      ∑ i ∈ range (NN + 1), (NN - i).choose M * (2 ^ (SW + 2)) ^ i := by
  unfold pk
  refine sum_congr rfl fun i _ => ?_
  rw [mul_assoc]
  congr 1
  rw [← pow_mul, show (SW + 2) * i = SW * i + 2 * i by ring, pow_add, mul_comm, pow_mul]
  norm_num
  rw [pow_mul]
  norm_num

open Finset in
theorem omRows_eq (SW NN m : ℕ) :
    omRows SW NN m = (List.range m).map (fun M => pk SW (fun i => (NN - i).choose M * 4 ^ i) (NN + 1)) := by
  have hshl : ∀ a b : ℕ, Nat.shiftLeft a b = a * 2 ^ b := fun a b => Nat.shiftLeft_eq a b
  set X := 2 ^ (SW + 2) with hX
  set R : ℕ → ℕ := fun M => pk SW (fun i => (NN - i).choose M * 4 ^ i) (NN + 1) with hR
  have hX2 : 2 ≤ X := by
    rw [hX]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (SW + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd : Nat.sub (Nat.shiftLeft 1 (Nat.add SW 2)) 1 = X - 1 := by
    rw [Nat.sub_eq, hshl, one_mul, Nat.add_eq]
  unfold omRows
  simp only []
  rw [hd]
  have key := natFold_inv m (([] : List ℕ), Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul (Nat.add SW 2) (Nat.add NN 1))) 1)
      (X - 1), 1)
    (fun M (st : List ℕ × ℕ × ℕ) =>
      (st.2.1 :: st.1, Nat.div (Nat.sub (Nat.sub st.2.1 st.2.2)
        (Nat.div (Nat.mul st.2.2 (Nat.sub NN M)) (Nat.add M 1))) (X - 1),
        Nat.div (Nat.mul st.2.2 (Nat.sub NN M)) (Nat.add M 1)))
    (fun j a => a = (((List.range j).map R).reverse, R j, NN.choose j)) ?_ ?_
  · rw [key, List.reverse_reverse]
  · refine Prod.ext rfl (Prod.ext ?_ (Nat.choose_zero_right NN).symm)
    show Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul (Nat.add SW 2) (Nat.add NN 1))) 1) (X - 1) = R 0
    rw [ndiv_eq, Nat.sub_eq, hshl, one_mul, Nat.mul_eq, Nat.add_eq, Nat.add_eq, hR]
    simp only []
    rw [omR_eq, pow_mul, ← hX, ← Nat.geomSum_eq hX2]
    simp
  · intro j a _ ha
    subst ha
    have hc1 : Nat.div (Nat.mul (NN.choose j) (Nat.sub NN j)) (Nat.add j 1) = NN.choose (j + 1) := by
      rw [ndiv_eq, Nat.mul_eq, Nat.sub_eq, Nat.add_eq, ← Nat.choose_succ_right_eq,
        Nat.mul_div_cancel _ (Nat.succ_pos j)]
    simp only [hc1]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    · show Nat.div (Nat.sub (Nat.sub (R j) (NN.choose j)) (NN.choose (j + 1))) (X - 1) = R (j + 1)
      have hrec := omQ_rec X NN j
      simp only [hR]
      rw [omR_eq, omR_eq, ← hX, ndiv_eq]
      simp only [Nat.sub_eq]
      set A := ∑ i ∈ range (NN + 1), (NN - i).choose j * X ^ i with hA
      set B := ∑ i ∈ range (NN + 1), (NN - i).choose (j + 1) * X ^ i with hB
      have hpos : 0 < X - 1 := by omega
      have hXB : X * B = B * (X - 1) + B := by
        rw [mul_comm X B, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
      have hsub : A - NN.choose j - NN.choose (j + 1) = B * (X - 1) := by omega
      rw [hsub, Nat.mul_div_cancel _ hpos]

/-! ## Windows of packed naturals -/

section

open Finset

theorem pk_slice (w : ℕ) (f : ℕ → ℕ) (n k m : ℕ) (hf : ∀ i < n, f i < 2 ^ w) :
    (pk w f n >>> (k * w)) &&& mask (m * w) = pk w (fun i => f (i + k)) (min (n - k) m) := by
  rw [Nat.shiftRight_eq_div_pow, mul_comm k w, pk_div w f n k hf, and_mask, mul_comm m w,
    pk_mod w _ _ m (fun i hi => hf _ (by omega))]

theorem pk_shl (w : ℕ) (f : ℕ → ℕ) (n k : ℕ) :
    pk w f n <<< (k * w) = pk w (fun i => if i < k then 0 else f (i - k)) (n + k) := by
  rw [mul_comm k w, pk_shiftLeft]

theorem pk_and_mask (w : ℕ) (f : ℕ → ℕ) (n m : ℕ) (hf : ∀ i < n, f i < 2 ^ w) :
    pk w f n &&& mask (m * w) = pk w f (min n m) := by
  rw [and_mask, mul_comm m w, pk_mod w f n m hf]

/-- A packed natural read on `E` slots with zeros past its length. -/
theorem pk_to (w : ℕ) (f : ℕ → ℕ) (n E : ℕ) (hz : ∀ i, n ≤ i → i < E → f i = 0) :
    pk w f (min n E) = pk w f E := by
  rcases le_total n E with h | h
  · rw [min_eq_left h]; exact (pk_extend w f n E h hz).symm
  · rw [min_eq_right h]

/-- Two packed naturals agree when their slots agree, each read as `0` past its length. -/
theorem pk_eq_pk (w : ℕ) (G H : ℕ → ℕ) (n1 n2 : ℕ)
    (h : ∀ t, t < n1 ∨ t < n2 → (if t < n1 then G t else 0) = (if t < n2 then H t else 0)) :
    pk w G n1 = pk w H n2 := by
  have e1 : pk w G n1 = pk w (fun t => if t < n1 then G t else 0) (max n1 n2) := by
    rw [pk_extend w _ n1 (max n1 n2) (le_max_left _ _) (fun i hi _ => ite_eq_right (by omega))]
    exact pk_congr w _ _ n1 fun i hi => (ite_eq_left hi).symm
  have e2 : pk w H n2 = pk w (fun t => if t < n2 then H t else 0) (max n1 n2) := by
    rw [pk_extend w _ n2 (max n1 n2) (le_max_right _ _) (fun i hi _ => ite_eq_right (by omega))]
    exact pk_congr w _ _ n2 fun i hi => (ite_eq_left hi).symm
  rw [e1, e2]
  exact pk_congr w _ _ _ fun t ht => h t (by omega)

/-- A window of a packed natural moved to slot `d`: slots `k, ..., k + m - 1` of `pk w F n` land on
`d, ..., d + m - 1`. -/
theorem pk_win (w : ℕ) (F : ℕ → ℕ) (n k m d : ℕ) (hf : ∀ i < n, F i < 2 ^ w) :
    ((pk w F n >>> (k * w)) &&& mask (m * w)) <<< (d * w) =
      pk w (fun t => if d ≤ t ∧ t < d + m ∧ t + k < n + d then F (t + k - d) else 0) (d + m) := by
  rw [pk_slice w F n k m hf, pk_shl]
  refine pk_eq_pk w _ _ _ _ fun t _ => ?_
  by_cases h1 : t < min (n - k) m + d
  · rw [ite_eq_left h1, ite_eq_left (show t < d + m by omega)]
    by_cases h2 : t < d
    · rw [ite_eq_left h2, ite_eq_right (by omega)]
    · rw [ite_eq_right h2, ite_eq_left (by omega), show t - d + k = t + k - d by omega]
  · rw [ite_eq_right h1]
    by_cases h3 : t < d + m
    · rw [ite_eq_left h3, ite_eq_right (by omega)]
    · rw [ite_eq_right h3]

/-! ## Sums with one index shifted -/

theorem sum_single_add (n j k : ℕ) (F : ℕ → ℕ) :
    ∑ i ∈ range n, (if i + j = k then F i else 0) = if j ≤ k ∧ k - j < n then F (k - j) else 0 := by
  have h : ∀ i, (i + j = k) ↔ (i = k - j ∧ j ≤ k) := fun i => by omega
  simp_rw [h, ite_and]
  rw [Finset.sum_ite_eq' (range n) (k - j) (fun x => if j ≤ k then F x else 0)]
  simp only [mem_range]
  split_ifs <;> simp_all

theorem sum_range_ind (n N : ℕ) (f : ℕ → ℕ) (h : n ≤ N) :
    ∑ s ∈ range n, f s = ∑ s ∈ range N, if s < n then f s else 0 := by
  rw [← Finset.sum_filter]
  have : (range N).filter (fun s => s < n) = range n := by
    ext s; simp only [mem_filter, mem_range]; omega
  rw [this]

theorem sum_shift_ind (L s0 N : ℕ) (g : ℕ → ℕ) (h : s0 + L ≤ N) :
    ∑ j ∈ range L, g (j + s0) = ∑ s ∈ range N, if s0 ≤ s ∧ s < s0 + L then g s else 0 := by
  rw [← Finset.sum_filter]
  have : (range N).filter (fun s => s0 ≤ s ∧ s < s0 + L) = Ico s0 (s0 + L) := by
    ext s; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-! ## The binomial weights `C(n, M) 4^(NN - n)` are unimodal, with mode `4M/3` -/

theorem om_up (NN M n : ℕ) (hn : n < 4 * M / 3) (hnN : n < NN) :
    n.choose M * 4 ^ (NN - n) ≤ (n + 1).choose M * 4 ^ (NN - (n + 1)) := by
  have hNN : n + 1 ≤ NN := Nat.add_one_le_of_lt hnN
  have hsub : NN - n = (NN - (n + 1)) + 1 := by
    omega
  have h_ineq : n.choose M * 4 ≤ (n + 1).choose M := by
    by_cases h : n < M
    · have hchoose : n.choose M = 0 := Nat.choose_eq_zero_of_lt h
      simp [hchoose]
    · have hM_le_n : M ≤ n := by omega
      have h_eq := Nat.choose_mul_succ_eq n M
      have hpos : 0 < n + 1 - M := by
        omega
      have h_arith : 4 * (n + 1 - M) ≤ n + 1 := by
        have h3 : 3 * (n + 1) ≤ 4 * M := by
          omega
        omega
      by_cases hzero : n.choose M = 0
      · simp [hzero]
      · have h_mul : n.choose M * (4 * (n + 1 - M)) ≤ n.choose M * (n + 1) :=
          Nat.mul_le_mul_left (n.choose M) h_arith
        have h_eq' : (n.choose M * 4) * (n + 1 - M) ≤ (n + 1).choose M * (n + 1 - M) := by
          calc
            (n.choose M * 4) * (n + 1 - M) = n.choose M * (4 * (n + 1 - M)) := by ring
            _ ≤ n.choose M * (n + 1) := h_mul
            _ = (n + 1).choose M * (n + 1 - M) := by rw [← h_eq]
        exact le_of_mul_le_mul_right h_eq' hpos
  calc
    n.choose M * 4 ^ (NN - n) = n.choose M * 4 ^ ((NN - (n + 1)) + 1) := by rw [hsub]
    _ = n.choose M * (4 ^ (NN - (n + 1)) * 4) := by rw [pow_succ]
    _ = (n.choose M * 4) * 4 ^ (NN - (n + 1)) := by ring
    _ ≤ (n + 1).choose M * 4 ^ (NN - (n + 1)) := by
      apply Nat.mul_le_mul_right (4 ^ (NN - (n + 1)))
      exact h_ineq

theorem om_down (NN M n : ℕ) (hn : 4 * M / 3 ≤ n) (hnN : n < NN) :
    (n + 1).choose M * 4 ^ (NN - (n + 1)) ≤ n.choose M * 4 ^ (NN - n) := by
  have hpos3 : 0 < 3 := by decide
  have hdiv : 4 * M ≤ 3 * n + 2 := by
    have := (Nat.div_le_iff_le_mul_add_pred hpos3).mp hn
    omega
  have hNN : n + 1 ≤ NN := by omega
  have hsub : NN - n = (NN - (n + 1)) + 1 := by omega
  have hpow : 4 ^ (NN - n) = 4 * 4 ^ (NN - (n + 1)) := by
    calc
      4 ^ (NN - n) = 4 ^ ((NN - (n + 1)) + 1) := by rw [hsub]
      _ = 4 ^ (NN - (n + 1)) * 4 := by rw [pow_succ]
      _ = 4 * 4 ^ (NN - (n + 1)) := by ring
  rw [hpow]
  by_cases hX : 4 ^ (NN - (n + 1)) = 0
  · rw [hX]; simp
  · have hXpos : 0 < 4 ^ (NN - (n + 1)) := Nat.pos_of_ne_zero hX
    have h_main : (n + 1).choose M ≤ 4 * n.choose M := by
      by_cases hM : M = 0
      · subst hM; simp
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
        have hnM : M ≤ n := by
          by_contra! hlt
          have hMge : n + 1 ≤ M := by omega
          have h4M : 4 * (n + 1) ≤ 4 * M := Nat.mul_le_mul_left 4 hMge
          have : 4 * (n + 1) ≤ 3 * n + 2 := Nat.le_trans h4M hdiv
          omega
        have hdpos : 0 < n + 1 - M := by omega
        have h_eq : n.choose M * (n + 1) = (n + 1).choose M * (n + 1 - M) := by
          rw [Nat.choose_mul_succ_eq]
        have h_ineq : n + 1 ≤ 4 * (n + 1 - M) := by
          omega
        have h_mul_ineq : (n + 1).choose M * (n + 1 - M) ≤ (4 * n.choose M) * (n + 1 - M) := by
          rw [← h_eq]
          have : (4 * n.choose M) * (n + 1 - M) = n.choose M * (4 * (n + 1 - M)) := by
            ring
          rw [this]
          apply Nat.mul_le_mul_left (n.choose M)
          exact h_ineq
        exact le_of_mul_le_mul_right h_mul_ineq hdpos
    have : n.choose M * (4 * 4 ^ (NN - (n + 1))) = (4 * n.choose M) * 4 ^ (NN - (n + 1)) := by
      ring
    rw [this]
    exact Nat.mul_le_mul h_main (by rfl)

end

end FrogModel.D3.LaneD.K
