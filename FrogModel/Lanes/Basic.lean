module

public import FrogModel.Lanes.Defs

@[expose] public section

/-!
# Packed lanes: the arithmetic of `pack`

`pack` is additive, homogeneous, determined by its lanes below `L`, and splits off its top lane.
-/

theorem FrogModel.Lanes.pack_add (W L : ℕ) (f g : ℕ → ℕ) :
    FrogModel.Lanes.pack W L f + FrogModel.Lanes.pack W L g =
      FrogModel.Lanes.pack W L (fun l => f l + g l) := by
  unfold FrogModel.Lanes.pack
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← add_mul]

theorem FrogModel.Lanes.pack_congr (W L : ℕ) (f g : ℕ → ℕ) (h : ∀ l < L, f l = g l) :
    FrogModel.Lanes.pack W L f = FrogModel.Lanes.pack W L g := by
  unfold FrogModel.Lanes.pack
  refine Finset.sum_congr rfl ?_
  intro l hl
  have hl' : l < L := Finset.mem_range.1 hl
  rw [h l hl']

theorem FrogModel.Lanes.pack_succ (W L : ℕ) (f : ℕ → ℕ) :
    FrogModel.Lanes.pack W (L + 1) f = FrogModel.Lanes.pack W L f + f L * 2 ^ (W * L) := by
  unfold FrogModel.Lanes.pack
  rw [Finset.sum_range_succ]

theorem FrogModel.Lanes.pack_const_mul (W L k : ℕ) (f : ℕ → ℕ) :
    k * FrogModel.Lanes.pack W L f = FrogModel.Lanes.pack W L (fun l => k * f l) := by
  simp [FrogModel.Lanes.pack, Finset.mul_sum, mul_assoc]

theorem FrogModel.Lanes.pack_sub (W L : ℕ) (f g : ℕ → ℕ) (h : ∀ l < L, f l ≤ g l) :
    FrogModel.Lanes.pack W L g - FrogModel.Lanes.pack W L f =
      FrogModel.Lanes.pack W L (fun l => g l - f l) := by
  apply Nat.sub_eq_of_eq_add
  calc
    FrogModel.Lanes.pack W L g
        = FrogModel.Lanes.pack W L (fun l => (g l - f l) + f l) := by
      apply FrogModel.Lanes.pack_congr W L g (fun l => (g l - f l) + f l)
      intro l hl
      rw [Nat.sub_add_cancel (h l hl)]
    _ = FrogModel.Lanes.pack W L (fun l => g l - f l) + FrogModel.Lanes.pack W L f := by
      rw [← FrogModel.Lanes.pack_add]

theorem FrogModel.Lanes.pack_lt (W L : ℕ) (f : ℕ → ℕ) (h : ∀ l < L, f l < 2 ^ W) :
    FrogModel.Lanes.pack W L f < 2 ^ (W * L) := by
  induction L with
  | zero =>
      simp [FrogModel.Lanes.pack]
  | succ L ih =>
      rw [FrogModel.Lanes.pack_succ]
      have h_restrict : ∀ l < L, f l < 2 ^ W := fun l hl =>
        h l (Nat.lt_trans hl (Nat.lt_succ_self L))
      have ih_h : FrogModel.Lanes.pack W L f < 2 ^ (W * L) := ih h_restrict
      have hL : f L < 2 ^ W := h L (Nat.lt_succ_self L)
      have hL' : f L + 1 ≤ 2 ^ W := by omega
      have h_eq : 2 ^ (W * L) + f L * 2 ^ (W * L) = (f L + 1) * 2 ^ (W * L) := by
        calc
          2 ^ (W * L) + f L * 2 ^ (W * L) = 1 * 2 ^ (W * L) + f L * 2 ^ (W * L) := by rw [Nat.one_mul]
          _ = (1 + f L) * 2 ^ (W * L) := by rw [Nat.add_mul]
          _ = (f L + 1) * 2 ^ (W * L) := by rw [Nat.add_comm]
      have h_pow : 2 ^ W * 2 ^ (W * L) = 2 ^ (W * (L + 1)) := by
        calc
          2 ^ W * 2 ^ (W * L) = 2 ^ (W + W * L) := by rw [pow_add]
          _ = 2 ^ (W * L + W) := by rw [Nat.add_comm]
          _ = 2 ^ (W * (L + 1)) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      calc
        FrogModel.Lanes.pack W L f + f L * 2 ^ (W * L) < 2 ^ (W * L) + f L * 2 ^ (W * L) :=
          Nat.add_lt_add_right ih_h (f L * 2 ^ (W * L))
        _ = (f L + 1) * 2 ^ (W * L) := h_eq
        _ ≤ 2 ^ W * 2 ^ (W * L) := Nat.mul_le_mul_right (2 ^ (W * L)) hL'
        _ = 2 ^ (W * (L + 1)) := h_pow

theorem FrogModel.Lanes.pack_div_mod (W L : ℕ) (f : ℕ → ℕ) (h : ∀ l < L, f l < 2 ^ W) (l : ℕ)
    (hl : l < L) : FrogModel.Lanes.pack W L f / 2 ^ (W * l) % 2 ^ W = f l := by
  induction' L with L ih generalizing l
  · exact (Nat.not_lt_zero _ hl).elim
  · rw [FrogModel.Lanes.pack_succ]
    have hle : l ≤ L := Nat.le_of_lt_succ hl
    by_cases h_eq : l = L
    · -- case l = L
      rw [h_eq]
      have hfL : f L < 2 ^ W := h L (Nat.lt_succ_self L)
      have hpos : 0 < 2 ^ (W * L) := pow_pos (by omega) _
      have hpack_lt : FrogModel.Lanes.pack W L f < 2 ^ (W * L) :=
        FrogModel.Lanes.pack_lt W L f (fun l' hl' => h l' (Nat.lt_succ_of_lt hl'))
      have hdiv : FrogModel.Lanes.pack W L f / 2 ^ (W * L) = 0 :=
        Nat.div_eq_of_lt hpack_lt
      have hdiv2 : f L * 2 ^ (W * L) / 2 ^ (W * L) = f L :=
        Nat.mul_div_cancel _ hpos
      have hdvd : 2 ^ (W * L) ∣ f L * 2 ^ (W * L) := ⟨f L, by ring⟩
      rw [Nat.add_div_of_dvd_left hdvd, hdiv, hdiv2, zero_add, Nat.mod_eq_of_lt hfL]
    · -- case l < L
      have hlt : l < L := Nat.lt_of_le_of_ne hle h_eq
      have hpos_small : 0 < 2 ^ (W * l) := pow_pos (by omega) _
      have hdvd : 2 ^ (W * l) ∣ f L * 2 ^ (W * L) := by
        have hpow : 2 ^ (W * l) ∣ 2 ^ (W * L) :=
          Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left W (Nat.le_of_lt hlt))
        exact hpow.mul_left (f L)
      rw [Nat.add_div_of_dvd_left hdvd]
      have h_ih : FrogModel.Lanes.pack W L f / 2 ^ (W * l) % 2 ^ W = f l :=
        ih (fun l' hl' => h l' (Nat.lt_succ_of_lt hl')) l hlt
      have hzero : f L * 2 ^ (W * L) / 2 ^ (W * l) % 2 ^ W = 0 := by
        have h_mul_add : W * L = W * l + W * (L - l) := by
          calc
            W * L = W * (l + (L - l)) := by rw [Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
            _ = W * l + W * (L - l) := by rw [Nat.mul_add]
        have h_pow_eq : 2 ^ (W * L) = 2 ^ (W * l) * 2 ^ (W * (L - l)) := by
          rw [h_mul_add, pow_add]
        have h_div_eq : f L * 2 ^ (W * L) / 2 ^ (W * l) = f L * 2 ^ (W * (L - l)) := by
          rw [h_pow_eq]
          rw [mul_comm (2 ^ (W * l)), ← mul_assoc, Nat.mul_div_cancel _ hpos_small]
        rw [h_div_eq]
        have h_dvd_pow : 2 ^ W ∣ 2 ^ (W * (L - l)) := by
          rw [pow_mul]
          have h_exp : 1 ≤ L - l := by omega
          have h_dvd := Nat.pow_dvd_pow (2 ^ W) h_exp
          simpa using h_dvd
        have h_dvd' : 2 ^ W ∣ f L * 2 ^ (W * (L - l)) :=
          h_dvd_pow.mul_left (f L)
        rw [Nat.mod_eq_zero_of_dvd h_dvd']
      rw [Nat.add_mod, h_ih, hzero, add_zero]
      exact Nat.mod_eq_of_lt (h l (Nat.lt_succ_of_lt hlt))

theorem FrogModel.Lanes.pack_inj (W L : ℕ) (f g : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ W)
    (hg : ∀ l < L, g l < 2 ^ W) (h : FrogModel.Lanes.pack W L f = FrogModel.Lanes.pack W L g) :
    ∀ l < L, f l = g l := by
  intro l hl
  calc
    f l = FrogModel.Lanes.pack W L f / 2 ^ (W * l) % 2 ^ W := (FrogModel.Lanes.pack_div_mod W L f hf l hl).symm
    _ = FrogModel.Lanes.pack W L g / 2 ^ (W * l) % 2 ^ W := by rw [h]
    _ = g l := FrogModel.Lanes.pack_div_mod W L g hg l hl

theorem FrogModel.Lanes.testBit_pack (W L : ℕ) (f : ℕ → ℕ) (h : ∀ l < L, f l < 2 ^ W) (l i : ℕ)
    (hl : l < L) (hi : i < W) :
    (FrogModel.Lanes.pack W L f).testBit (W * l + i) = (f l).testBit i := by
  calc
    (FrogModel.Lanes.pack W L f).testBit (W * l + i)
        = ((FrogModel.Lanes.pack W L f) / 2 ^ (W * l)).testBit i := by
      rw [add_comm, ← Nat.testBit_div_two_pow]
    _ = (((FrogModel.Lanes.pack W L f) / 2 ^ (W * l)) % 2 ^ W).testBit i := by
      simp [hi, Nat.testBit_mod_two_pow]
    _ = (f l).testBit i := by rw [FrogModel.Lanes.pack_div_mod W L f h l hl]

theorem FrogModel.Lanes.testBit_pack_high (W L : ℕ) (f : ℕ → ℕ) (h : ∀ l < L, f l < 2 ^ W)
    (n : ℕ) (hn : W * L ≤ n) : (FrogModel.Lanes.pack W L f).testBit n = false := by
  have hlt : FrogModel.Lanes.pack W L f < 2 ^ (W * L) := FrogModel.Lanes.pack_lt W L f h
  have hpow : 2 ^ (W * L) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hlt' : FrogModel.Lanes.pack W L f < 2 ^ n := lt_of_lt_of_le hlt hpow
  exact Nat.testBit_eq_false_of_lt hlt'

theorem FrogModel.Lanes.land_pack (W L : ℕ) (hW : 1 ≤ W) (f g : ℕ → ℕ)
    (hf : ∀ l < L, f l < 2 ^ W) (hg : ∀ l < L, g l < 2 ^ W) :
    FrogModel.Lanes.pack W L f &&& FrogModel.Lanes.pack W L g =
      FrogModel.Lanes.pack W L (fun l => f l &&& g l) := by
  have hWpos : 0 < W := Nat.one_pos.trans_le hW
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < W * L
  · set l := n / W with hl_def
    set i := n % W with hi_def
    have hn_eq : n = W * l + i := by
      rw [hl_def, hi_def, Nat.div_add_mod n W]
    have hl : l < L := by
      rw [hl_def]
      apply (Nat.div_lt_iff_lt_mul hWpos).mpr
      rw [mul_comm L W]
      exact hn
    have hi : i < W := by
      rw [hi_def]
      exact Nat.mod_lt n hWpos
    rw [hn_eq]
    rw [Nat.testBit_land]
    rw [FrogModel.Lanes.testBit_pack W L f hf l i hl hi]
    rw [FrogModel.Lanes.testBit_pack W L g hg l i hl hi]
    rw [← Nat.testBit_land]
    have hland_bound : ∀ l' < L, f l' &&& g l' < 2 ^ W := by
      intro l' hl'
      have hfl := hf l' hl'
      have hland : f l' &&& g l' ≤ f l' := Nat.and_le_left
      exact lt_of_le_of_lt hland hfl
    rw [FrogModel.Lanes.testBit_pack W L (fun l => f l &&& g l) hland_bound l i hl hi]
  · have hn' : W * L ≤ n := Nat.le_of_not_lt hn
    have hland_bound : ∀ l' < L, f l' &&& g l' < 2 ^ W := by
      intro l' hl'
      have hfl := hf l' hl'
      have hland : f l' &&& g l' ≤ f l' := Nat.and_le_left
      exact lt_of_le_of_lt hland hfl
    have h1 : (FrogModel.Lanes.pack W L f &&& FrogModel.Lanes.pack W L g).testBit n = false := by
      rw [Nat.testBit_land]
      rw [FrogModel.Lanes.testBit_pack_high W L f hf n hn',
        FrogModel.Lanes.testBit_pack_high W L g hg n hn']
      rfl
    have h2 : (FrogModel.Lanes.pack W L (fun l => f l &&& g l)).testBit n = false :=
      FrogModel.Lanes.testBit_pack_high W L (fun l => f l &&& g l) hland_bound n hn'
    rw [h1, h2]

theorem FrogModel.Lanes.land_guard_eq_iff (W L : ℕ) (hW : 1 ≤ W) (f : ℕ → ℕ)
    (h : ∀ l < L, f l < 2 ^ W) :
    (FrogModel.Lanes.pack W L f &&& FrogModel.Lanes.guard W L = FrogModel.Lanes.guard W L) ↔
      ∀ l < L, 2 ^ (W - 1) ≤ f l := by
  have h_two_pow_lt : 2 ^ (W - 1) < 2 ^ W := by
    have hW' : W - 1 < W := by
      have hposW : 0 < W := by omega
      exact Nat.sub_lt hposW (by omega)
    exact Nat.pow_lt_pow_right (by norm_num) hW'
  have h_two_pow_W_eq : 2 ^ W = 2 * 2 ^ (W - 1) := by
    have hW' : W = (W - 1) + 1 := by omega
    rw [hW', pow_succ]
    simp [mul_comm]
  have h_guard_lt : ∀ l < L, 2 ^ (W - 1) < 2 ^ W := by
    intro l hl
    exact h_two_pow_lt
  -- Lemma: a &&& 2^k is either 0 or 2^k
  have h_land_two_pow_cases : ∀ a k : ℕ, a &&& 2 ^ k = 0 ∨ a &&& 2 ^ k = 2 ^ k := by
    intro a k
    rw [Nat.and_two_pow]
    set b := a.testBit k with hb
    have h_cases : b.toNat = 0 ∨ b.toNat = 1 := by
      cases b with
      | false => left; rfl
      | true => right; rfl
    rcases h_cases with (h0 | h1)
    · rw [h0]; simp
    · rw [h1]; simp
  -- Key lemma: a &&& 2^(W-1) = 0 when a < 2^(W-1)
  have h_land_zero_of_lt : ∀ a, a < 2 ^ (W - 1) → a &&& 2 ^ (W - 1) = 0 := by
    intro a ha
    have h_test_bit : a.testBit (W - 1) = false := Nat.testBit_eq_false_of_lt ha
    rw [Nat.and_two_pow]
    rw [h_test_bit]
    simp
  -- Key lemma: a &&& 2^(W-1) = 2^(W-1) ↔ 2^(W-1) ≤ a when a < 2^W
  have h_land_eq_iff : ∀ a, a < 2 ^ W → (a &&& 2 ^ (W - 1) = 2 ^ (W - 1) ↔ 2 ^ (W - 1) ≤ a) := by
    intro a ha
    constructor
    · intro h_eq
      by_contra! h_lt
      have h_zero : a &&& 2 ^ (W - 1) = 0 := h_land_zero_of_lt a h_lt
      rw [h_zero] at h_eq
      have h_ne_zero : 2 ^ (W - 1) ≠ 0 := by
        apply pow_ne_zero; norm_num
      exact h_ne_zero h_eq.symm
    · intro h_le
      rcases Nat.exists_eq_add_of_le h_le with ⟨r, hr⟩
      have hr_lt : r < 2 ^ (W - 1) := by
        rw [hr] at ha
        rw [h_two_pow_W_eq] at ha
        omega
      rw [hr]
      rw [Nat.and_comm]
      rw [Nat.two_pow_and]
      have h_test_bit : (2 ^ (W - 1) + r).testBit (W - 1) = true := by
        rw [Nat.testBit_two_pow_add_eq]
        have h_r_test_bit : r.testBit (W - 1) = false := Nat.testBit_eq_false_of_lt hr_lt
        rw [h_r_test_bit]
        rfl
      rw [h_test_bit]
      simp
  constructor
  · intro h_eq
    unfold FrogModel.Lanes.guard at h_eq
    rw [FrogModel.Lanes.land_pack W L hW f (fun _ => 2 ^ (W - 1)) h h_guard_lt] at h_eq
    -- h_eq: pack W L (fun l => f l &&& 2^(W-1)) = pack W L (fun _ => 2^(W-1))
    by_contra! h_not
    rcases h_not with ⟨l, hl, h_lt⟩
    -- h_lt: f l < 2^(W-1)
    have h_land_zero : f l &&& 2 ^ (W - 1) = 0 := h_land_zero_of_lt (f l) h_lt
    have h_guard_ne_zero : 2 ^ (W - 1) ≠ 0 := by
      apply pow_ne_zero; norm_num
    -- Prove the bound for pack_inj
    have h_bound : ∀ l', l' < L → f l' &&& 2 ^ (W - 1) < 2 ^ W := by
      intro l' hl'
      rcases h_land_two_pow_cases (f l') (W - 1) with (h0 | h2)
      · rw [h0]
        exact pow_pos (by norm_num) W
      · rw [h2]
        exact h_two_pow_lt
    have h_pointwise : ∀ l', l' < L → f l' &&& 2 ^ (W - 1) = 2 ^ (W - 1) :=
      FrogModel.Lanes.pack_inj W L (fun l => f l &&& 2 ^ (W - 1)) (fun _ => 2 ^ (W - 1))
        h_bound h_guard_lt h_eq
    have h_contra := h_pointwise l hl
    rw [h_land_zero] at h_contra
    -- h_contra: 0 = 2^(W-1)
    exact h_guard_ne_zero h_contra.symm
  · intro h_le
    have h_land_eq : ∀ l < L, f l &&& 2 ^ (W - 1) = 2 ^ (W - 1) := by
      intro l' hl'
      have ha_lt : f l' < 2 ^ W := h l' hl'
      exact ((h_land_eq_iff (f l') ha_lt).mpr (h_le l' hl'))
    have h_pack_eq : FrogModel.Lanes.pack W L (fun l => f l &&& 2 ^ (W - 1)) =
        FrogModel.Lanes.pack W L (fun _ => 2 ^ (W - 1)) :=
      FrogModel.Lanes.pack_congr W L (fun l => f l &&& 2 ^ (W - 1)) (fun _ => 2 ^ (W - 1)) h_land_eq
    -- Goal: pack W L f &&& guard W L = guard W L
    unfold FrogModel.Lanes.guard
    -- Goal: pack W L f &&& pack W L (fun _ => 2^(W-1)) = pack W L (fun _ => 2^(W-1))
    rw [FrogModel.Lanes.land_pack W L hW f (fun _ => 2 ^ (W - 1)) h h_guard_lt]
    -- Goal: pack W L (fun l => f l &&& 2^(W-1)) = pack W L (fun _ => 2^(W-1))
    exact h_pack_eq

theorem FrogModel.Lanes.leLanes_iff (W L : ℕ) (hW : 1 ≤ W) (f g : ℕ → ℕ)
    (hf : ∀ l < L, f l < 2 ^ (W - 1)) (hg : ∀ l < L, g l < 2 ^ (W - 1)) :
    FrogModel.Lanes.leLanes (FrogModel.Lanes.guard W L) (FrogModel.Lanes.pack W L f)
        (FrogModel.Lanes.pack W L g) = true ↔ ∀ l < L, f l ≤ g l := by
  set G := FrogModel.Lanes.guard W L with hG_def
  have h_leLanes_eq : FrogModel.Lanes.leLanes G (FrogModel.Lanes.pack W L f) (FrogModel.Lanes.pack W L g) =
      Nat.beq (((FrogModel.Lanes.pack W L g) + G - (FrogModel.Lanes.pack W L f)) &&& G) G := rfl
  rw [h_leLanes_eq, Nat.beq_eq]
  have hG_eq : G = FrogModel.Lanes.guard W L := hG_def
  have hpack_add : FrogModel.Lanes.pack W L g + G = FrogModel.Lanes.pack W L (fun l => g l + 2 ^ (W - 1)) := by
    rw [hG_def, FrogModel.Lanes.guard, FrogModel.Lanes.pack_add]
  rw [hpack_add]
  have hf_le_g_add : ∀ l < L, f l ≤ g l + 2 ^ (W - 1) := by
    intro l hl
    have hfl := hf l hl
    exact (Nat.le_of_lt hfl).trans (Nat.le_add_left _ _)
  have h_sub_eq : FrogModel.Lanes.pack W L (fun l => g l + 2 ^ (W - 1)) - FrogModel.Lanes.pack W L f =
      FrogModel.Lanes.pack W L (fun l => g l + 2 ^ (W - 1) - f l) := by
    rw [FrogModel.Lanes.pack_sub W L f (fun l => g l + 2 ^ (W - 1)) hf_le_g_add]
  rw [h_sub_eq]
  have hsum : 2 ^ (W - 1) + 2 ^ (W - 1) = 2 ^ W := by
    calc
      2 ^ (W - 1) + 2 ^ (W - 1) = 2 * 2 ^ (W - 1) := by rw [← Nat.two_mul]
      _ = 2 ^ (W - 1) * 2 := by rw [Nat.mul_comm]
      _ = 2 ^ ((W - 1) + 1) := by rw [← Nat.pow_succ]
      _ = 2 ^ W := by rw [Nat.sub_add_cancel hW]
  have hh_bound : ∀ l < L, (fun l => g l + 2 ^ (W - 1) - f l) l < 2 ^ W := by
    intro l hl
    have hgl := hg l hl
    have hfl := hf l hl
    have hle : g l + 2 ^ (W - 1) - f l ≤ g l + 2 ^ (W - 1) := Nat.sub_le _ _
    have hlt : g l + 2 ^ (W - 1) < 2 ^ (W - 1) + 2 ^ (W - 1) :=
      Nat.add_lt_add_right hgl (2 ^ (W - 1))
    exact lt_of_le_of_lt hle (lt_of_lt_of_eq hlt hsum)
  have h_land_guard := FrogModel.Lanes.land_guard_eq_iff W L hW (fun l => g l + 2 ^ (W - 1) - f l) hh_bound
  rw [← hG_eq] at h_land_guard
  rw [h_land_guard]
  constructor
  · intro h l hl
    have hh := h l hl
    have hle : f l ≤ g l + 2 ^ (W - 1) := by
      have hfl := hf l hl
      exact (Nat.le_of_lt hfl).trans (Nat.le_add_left _ _)
    have hh' := (Nat.le_sub_iff_add_le hle).mp hh
    -- hh' : 2^(W-1) + f l ≤ g l + 2^(W-1)
    -- We need f l ≤ g l
    rw [add_comm (2 ^ (W - 1)) (f l)] at hh'
    exact ((Nat.add_le_add_iff_right (n := 2 ^ (W - 1))).mp hh')
  · intro h l hl
    have hhl := h l hl
    have hsub : g l + 2 ^ (W - 1) - f l = (g l - f l) + 2 ^ (W - 1) := by
      rw [add_comm, Nat.add_sub_assoc hhl, add_comm]
    rw [hsub]
    exact Nat.le_add_left _ _

theorem FrogModel.Lanes.pack_mul_pow (W L k : ℕ) (f : ℕ → ℕ) :
    FrogModel.Lanes.pack W L f * 2 ^ (W * k) =
      FrogModel.Lanes.pack W (L + k) (fun l => if l < k then 0 else f (l - k)) := by
  dsimp [FrogModel.Lanes.pack]
  rw [add_comm L k, Finset.sum_range_add]
  have h_first : (∑ l ∈ Finset.range k, (if l < k then 0 else f (l - k)) * 2 ^ (W * l)) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_range] at hl
    simp [hl]
  rw [h_first, zero_add]
  have h_term : ∀ l, (if k + l < k then 0 else f ((k + l) - k)) = f l := by
    intro l
    have h_not_lt : ¬ (k + l < k) := Nat.not_lt.mpr (Nat.le_add_right k l)
    simp [h_not_lt]
  -- Replace RHS summand using h_term
  have h_sum_eq : (∑ x ∈ Finset.range L, (if k + x < k then 0 else f ((k + x) - k)) * 2 ^ (W * (k + x))) =
                  (∑ x ∈ Finset.range L, f x * 2 ^ (W * (k + x))) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [h_term x]
  rw [h_sum_eq]
  calc
    (∑ l ∈ Finset.range L, f l * 2 ^ (W * l)) * 2 ^ (W * k)
        = ∑ l ∈ Finset.range L, (f l * 2 ^ (W * l)) * 2 ^ (W * k) := by rw [Finset.sum_mul]
    _ = ∑ l ∈ Finset.range L, f l * (2 ^ (W * l) * 2 ^ (W * k)) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    _ = ∑ l ∈ Finset.range L, f l * 2 ^ (W * l + W * k) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [pow_add]
    _ = ∑ l ∈ Finset.range L, f l * 2 ^ (W * (l + k)) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_add]
    _ = ∑ l ∈ Finset.range L, f l * 2 ^ (W * (k + l)) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [add_comm]

theorem FrogModel.Lanes.pack_ite_range (W L a b : ℕ) (hb : b ≤ L) (f : ℕ → ℕ) :
    FrogModel.Lanes.pack W L (fun l => if a ≤ l ∧ l < b then f l else 0) =
      ∑ l ∈ Finset.Ico a b, f l * 2 ^ (W * l) := by
  unfold FrogModel.Lanes.pack
  simp only [ite_mul, Nat.zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext l
  simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem FrogModel.Lanes.mask_eq_pack (W L a b : ℕ) (hab : a ≤ b) (hb : b ≤ L) :
    2 ^ (W * b) - 2 ^ (W * a) =
      FrogModel.Lanes.pack W L (fun l => if a ≤ l ∧ l < b then 2 ^ W - 1 else 0) := by
  have hsum : FrogModel.Lanes.pack W L (fun l => if a ≤ l ∧ l < b then 2 ^ W - 1 else 0) =
      ∑ l ∈ Finset.Ico a b, (2 ^ W - 1) * 2 ^ (W * l) := by
    dsimp [FrogModel.Lanes.pack]
    calc
      ∑ l ∈ Finset.range L, (if a ≤ l ∧ l < b then 2 ^ W - 1 else 0) * 2 ^ (W * l)
          = ∑ l ∈ Finset.range L, (if a ≤ l ∧ l < b then (2 ^ W - 1) * 2 ^ (W * l) else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        by_cases h : a ≤ x ∧ x < b
        · simp [h]
        · simp [h]
      _ = ∑ l ∈ (Finset.range L).filter (fun l => a ≤ l ∧ l < b), (2 ^ W - 1) * 2 ^ (W * l) := by
        rw [Finset.sum_filter]
      _ = ∑ l ∈ Finset.Ico a b, (2 ^ W - 1) * 2 ^ (W * l) := by
        refine Finset.sum_congr ?_ fun x hx => rfl
        ext x
        constructor
        · intro h
          rw [Finset.mem_filter] at h
          exact Finset.mem_Ico.mpr h.2
        · intro h
          have hx_mem := Finset.mem_Ico.mp h
          refine Finset.mem_filter.mpr ⟨?_, hx_mem⟩
          rw [Finset.mem_range]
          exact lt_of_lt_of_le hx_mem.2 hb
  rw [hsum]
  have hmain : 2 ^ (W * b) - 2 ^ (W * a) = ∑ l ∈ Finset.Ico a b, (2 ^ W - 1) * 2 ^ (W * l) := by
    refine Nat.le_induction ?base ?step b hab
    · -- base: n = a
      simp
    · -- step: from k to k+1
      intro k hk ih
      have hpa_le_pk : 2 ^ (W * a) ≤ 2 ^ (W * k) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left W hk)
      have hpk_le_y_pk : 2 ^ (W * k) ≤ 2 ^ W * 2 ^ (W * k) := by
        have h1 : 1 ≤ 2 ^ W := by
          simpa using Nat.one_le_pow' W 1
        calc
          2 ^ (W * k) = 1 * 2 ^ (W * k) := by simp
          _ ≤ 2 ^ W * 2 ^ (W * k) := Nat.mul_le_mul_right _ h1
      have hp_add : 2 ^ (W * (k + 1)) = 2 ^ (W * k) * 2 ^ W := by
        rw [mul_add, mul_one, pow_add]
      have htsub := tsub_add_tsub_cancel hpk_le_y_pk hpa_le_pk
      -- htsub: (2^W * 2^(W*k)) - 2^(W*k) + (2^(W*k) - 2^(W*a)) = (2^W * 2^(W*k)) - 2^(W*a)
      calc
        2 ^ (W * (k + 1)) - 2 ^ (W * a) = (2 ^ (W * k) * 2 ^ W) - 2 ^ (W * a) := by rw [hp_add]
        _ = (2 ^ W * 2 ^ (W * k)) - 2 ^ (W * a) := by rw [mul_comm (2 ^ W)]
        _ = ((2 ^ W * 2 ^ (W * k)) - 2 ^ (W * k)) + (2 ^ (W * k) - 2 ^ (W * a)) := by
          rw [← htsub]
        _ = (2 ^ W - 1) * 2 ^ (W * k) + (2 ^ (W * k) - 2 ^ (W * a)) := by
          rw [tsub_mul, one_mul]
        _ = (2 ^ (W * k) - 2 ^ (W * a)) + (2 ^ W - 1) * 2 ^ (W * k) := add_comm _ _
        _ = (∑ l ∈ Finset.Ico a k, (2 ^ W - 1) * 2 ^ (W * l)) + (2 ^ W - 1) * 2 ^ (W * k) := by
          rw [ih]
        _ = ∑ l ∈ Finset.Ico a (k + 1), (2 ^ W - 1) * 2 ^ (W * l) := by
          rw [Finset.sum_Ico_succ_top hk]
  exact hmain

theorem FrogModel.Lanes.land_mask (W L a b : ℕ) (hW : 1 ≤ W) (hab : a ≤ b) (hb : b ≤ L)
    (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ W) :
    FrogModel.Lanes.pack W L f &&& (2 ^ (W * b) - 2 ^ (W * a)) =
      FrogModel.Lanes.pack W L (fun l => if a ≤ l ∧ l < b then f l else 0) := by
  have hpos : ∀ W : ℕ, 0 < 2 ^ W := by
    intro W
    have h := Nat.one_le_two_pow (n := W)
    omega
  have hg : ∀ l < L, (if a ≤ l ∧ l < b then 2 ^ W - 1 else 0) < 2 ^ W := by
    intro l hl
    by_cases h : a ≤ l ∧ l < b
    · have hsub : 2 ^ W - 1 < 2 ^ W := Nat.sub_lt (hpos W) (by omega)
      simp [h, hsub]
    · simp [h, hpos W]
  have land_two_pow_sub_one_eq_mod : ∀ (n W : ℕ), n &&& (2 ^ W - 1) = n % 2 ^ W := by
    intro n W
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    simp [Bool.and_comm]
  have h_and : ∀ l < L, f l &&& (if a ≤ l ∧ l < b then 2 ^ W - 1 else 0) =
      (if a ≤ l ∧ l < b then f l else 0) := by
    intro l hl
    by_cases h : a ≤ l ∧ l < b
    · simp [h, land_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf l hl)]
    · simp [h]
  calc
    FrogModel.Lanes.pack W L f &&& (2 ^ (W * b) - 2 ^ (W * a))
        = FrogModel.Lanes.pack W L f &&& FrogModel.Lanes.pack W L
            (fun l => if a ≤ l ∧ l < b then 2 ^ W - 1 else 0) := by
      rw [FrogModel.Lanes.mask_eq_pack W L a b hab hb]
    _ = FrogModel.Lanes.pack W L (fun l => f l &&& (if a ≤ l ∧ l < b then 2 ^ W - 1 else 0)) := by
      rw [FrogModel.Lanes.land_pack W L hW f (fun l => if a ≤ l ∧ l < b then 2 ^ W - 1 else 0) hf hg]
    _ = FrogModel.Lanes.pack W L (fun l => if a ≤ l ∧ l < b then f l else 0) := by
      apply FrogModel.Lanes.pack_congr W L (fun l => f l &&& (if a ≤ l ∧ l < b then 2 ^ W - 1 else 0))
        (fun l => if a ≤ l ∧ l < b then f l else 0) h_and

theorem FrogModel.Lanes.pack_mono (W L : ℕ) (f g : ℕ → ℕ) (h : ∀ l < L, f l ≤ g l) :
    FrogModel.Lanes.pack W L f ≤ FrogModel.Lanes.pack W L g := by
  unfold FrogModel.Lanes.pack
  refine Finset.sum_le_sum ?_
  intro l hl
  have hl' := Finset.mem_range.1 hl
  exact Nat.mul_le_mul_right (2 ^ (W * l)) (h l hl')

theorem FrogModel.Lanes.pack_ext_len (W L L' : ℕ) (f : ℕ → ℕ) (hL : L ≤ L') (h : ∀ l, L ≤ l → l < L' → f l = 0) :
    FrogModel.Lanes.pack W L' f = FrogModel.Lanes.pack W L f := by
  unfold FrogModel.Lanes.pack
  refine (Finset.sum_subset (Finset.range_subset.mpr (fun x hx => by
    rw [Finset.mem_range]
    exact lt_of_lt_of_le hx hL)) ?_).symm
  intro l hl hmem
  have hl' : l < L' := Finset.mem_range.1 hl
  have hLl : L ≤ l := by
    have : l ∉ Finset.range L := hmem
    rwa [Finset.mem_range, not_lt] at this
  rw [h l hLl hl', zero_mul]
