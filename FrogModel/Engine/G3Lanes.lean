module

public import FrogModel.G3K.Spec
public import FrogModel.Lanes.Basic

@[expose] public section

/-!
# The packed lanes of the G3 checker, read lane by lane

The vectors of the checker are numbers whose lanes of `W` bits (`lane W j n`) hold the values:
V' has the `nL` lanes of 96 bits of its phase (G3K.Table), W' has `T + 1 = 9` lanes of 128 bits.
`boundsOK` makes an entry the pack of its lanes, below `2^47` (V') and `2^77` (W')
(`boundsOK_sound`). A gather moves lanes `[a, b)` up by `s` lanes (`gather_pack`, with the source
lane `gsrc`). `leLanes` compares two packs lane by lane when every lane of both is below the guard
bit (`leLanes_pack`, from `FrogModel.Lanes.leLanes_iff`). The guards and masks of G3K.Table are
packs of constant lanes (`gV_eq`, `lowV_eq`, `gW_eq`, `lowWb_eq`, `lowW_eq`), and the gathers of
every phase move each lane at most once, inside the phase (`segsOK_phase`).
-/

namespace FrogModel.Engine.G3

open FrogModel.Lanes

/-- Lane `j` of width `W` of `n`. -/
def lane (W j n : ℕ) : ℕ := n / 2 ^ (W * j) % 2 ^ W

theorem lane_lt (W j n : ℕ) : lane W j n < 2 ^ W := Nat.mod_lt _ (Nat.two_pow_pos W)

/-! Helpers of `pack_lane` and `eq_pack_of_land_mask`. -/

lemma lane_mod_eq (W j L n : ℕ) (hj : j < L) :
    FrogModel.Engine.G3.lane W j n = FrogModel.Engine.G3.lane W j (n % 2 ^ (W * L)) := by
  unfold FrogModel.Engine.G3.lane
  have h_exp : W * L = W * j + W * (L - j) := by
    rw [← Nat.add_sub_cancel' (Nat.mul_le_mul_left W (Nat.le_of_lt hj)), Nat.mul_sub_left_distrib]
  have hM : 2 ^ (W * L) = 2 ^ (W * j) * 2 ^ (W * (L - j)) := by
    rw [h_exp, pow_add]
  have hdiv := Nat.mod_mul_right_div_self n (2 ^ (W * j)) (2 ^ (W * (L - j)))
  -- hdiv: n % (2^(W*j) * 2^(W*(L-j))) / 2^(W*j) = n / 2^(W*j) % 2^(W*(L-j))
  have hpos : 1 ≤ L - j := by
    have : 0 < L - j := Nat.sub_pos_of_lt hj
    omega
  have h_dvd : 2 ^ W ∣ 2 ^ (W * (L - j)) := by
    apply Nat.pow_dvd_pow 2
    calc
      W = W * 1 := by simp
      _ ≤ W * (L - j) := Nat.mul_le_mul_left W hpos
  calc
    n / 2 ^ (W * j) % 2 ^ W
        = (n / 2 ^ (W * j) % 2 ^ (W * (L - j))) % 2 ^ W := by
      rw [Nat.mod_mod_of_dvd _ h_dvd]
    _ = (n % (2 ^ (W * j) * 2 ^ (W * (L - j))) / 2 ^ (W * j)) % 2 ^ W := by rw [← hdiv]
    _ = (n % 2 ^ (W * L) / 2 ^ (W * j)) % 2 ^ W := by rw [hM]

private theorem two_pow_sub_one_lt_two_pow_of_le {k W : ℕ} (hk : k ≤ W) : 2 ^ k - 1 < 2 ^ W := by
  by_cases hk0 : k = 0
  · rw [hk0, pow_zero, Nat.sub_self]
    have h := Nat.two_pow_pos W
    omega
  · have hkpos : 1 ≤ k := Nat.one_le_of_lt (Nat.pos_of_ne_zero hk0)
    have hpow : 2 ^ k ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hk
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    omega

private theorem lane_testBit (W j n i : ℕ) : (FrogModel.Engine.G3.lane W j n).testBit i =
    if i < W then n.testBit (W * j + i) else false := by
  rw [FrogModel.Engine.G3.lane]
  by_cases hi : i < W
  · simp [hi, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, add_comm]
  · have hi' : W ≤ i := Nat.le_of_not_lt hi
    have hfalse : (n / 2 ^ (W * j) % 2 ^ W).testBit i = false :=
      Nat.testBit_eq_false_of_lt (by
        have hmod : n / 2 ^ (W * j) % 2 ^ W < 2 ^ W := Nat.mod_lt _ (Nat.two_pow_pos W)
        have hpow : 2 ^ W ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi'
        exact lt_of_lt_of_le hmod hpow)
    simp [hi, hfalse]

/-- The lane of a pack. -/
theorem lane_pack (W L : ℕ) (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ W) (j : ℕ) :
    lane W j (pack W L f) = if j < L then f j else 0 := by
  unfold FrogModel.Engine.G3.lane
  by_cases hj : j < L
  · rw [ite_eq_left hj]
    exact FrogModel.Lanes.pack_div_mod W L f hf j hj
  · rw [ite_eq_right hj]
    have hLj : L ≤ j := Nat.le_of_not_lt hj
    have hpack_lt : FrogModel.Lanes.pack W L f < 2 ^ (W * L) :=
      FrogModel.Lanes.pack_lt W L f hf
    have hpow_le : 2 ^ (W * L) ≤ 2 ^ (W * j) :=
      Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left W hLj)
    have hpack_lt2 : FrogModel.Lanes.pack W L f < 2 ^ (W * j) :=
      lt_of_lt_of_le hpack_lt hpow_le
    have hdiv : FrogModel.Lanes.pack W L f / 2 ^ (W * j) = 0 :=
      Nat.div_eq_of_lt hpack_lt2
    rw [hdiv]
    simp

/-- A number below `2^(W L)` is the pack of its first `L` lanes. -/
theorem pack_lane (W L n : ℕ) (h : n < 2 ^ (W * L)) : pack W L (fun j => lane W j n) = n := by
  induction' L with L ih generalizing n
  · -- L = 0
    have h0 : 2 ^ (W * 0) = 1 := by simp
    rw [h0] at h
    have hn0 : n = 0 := by omega
    rw [hn0]
    simp [FrogModel.Lanes.pack]
  · -- L → L+1
    rw [FrogModel.Lanes.pack_succ]
    have h_lt_succ : n < 2 ^ (W * (L + 1)) := h
    have h_div_lt : n / 2 ^ (W * L) < 2 ^ W := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).2
      calc
        n < 2 ^ (W * (L + 1)) := h_lt_succ
        _ = 2 ^ (W * L + W) := by ring
        _ = 2 ^ (W * L) * 2 ^ W := by rw [pow_add]
        _ = 2 ^ W * 2 ^ (W * L) := by rw [mul_comm]
    have h_lane_eq : FrogModel.Engine.G3.lane W L n = n / 2 ^ (W * L) := by
      rw [FrogModel.Engine.G3.lane]
      exact Nat.mod_eq_of_lt h_div_lt
    rw [h_lane_eq]
    have h_mod_lt : n % 2 ^ (W * L) < 2 ^ (W * L) :=
      Nat.mod_lt _ (by positivity)
    have h_pack_eq : pack W L (fun j => FrogModel.Engine.G3.lane W j n) =
                    pack W L (fun j => FrogModel.Engine.G3.lane W j (n % 2 ^ (W * L))) := by
      apply FrogModel.Lanes.pack_congr W L
      intro j hj
      exact lane_mod_eq W j L n hj
    calc
      pack W L (fun j => FrogModel.Engine.G3.lane W j n) + n / 2 ^ (W * L) * 2 ^ (W * L)
          = pack W L (fun j => FrogModel.Engine.G3.lane W j (n % 2 ^ (W * L))) + n / 2 ^ (W * L) * 2 ^ (W * L) := by rw [h_pack_eq]
      _ = (n % 2 ^ (W * L)) + n / 2 ^ (W * L) * 2 ^ (W * L) := by rw [ih (n % 2 ^ (W * L)) h_mod_lt]
      _ = (n % 2 ^ (W * L)) + 2 ^ (W * L) * (n / 2 ^ (W * L)) := by rw [mul_comm (n / 2 ^ (W * L)) (2 ^ (W * L))]
      _ = n := by rw [Nat.mod_add_div n (2 ^ (W * L))]

/-! ### Guards and masks of the table -/

/-- `(2^(W n) - 1) / (2^W - 1)` is the pack of `n` ones. -/
theorem pack_one_eq (W n : ℕ) (hW : 1 ≤ W) :
    (2 ^ (W * n) - 1) / (2 ^ W - 1) = pack W n fun _ => 1 := by
  have h2W : 2 ≤ 2 ^ W := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) hW
    simpa using h
  calc
    (2 ^ (W * n) - 1) / (2 ^ W - 1) = ((2 ^ W) ^ n - 1) / ((2 ^ W) - 1) := by
      simp [pow_mul]
    _ = ∑ k ∈ Finset.range n, (2 ^ W) ^ k := by
      rw [Nat.geomSum_eq h2W n]
    _ = ∑ k ∈ Finset.range n, 2 ^ (W * k) := by
      simp [pow_mul]
    _ = ∑ k ∈ Finset.range n, (fun _ => 1) k * 2 ^ (W * k) := by simp
    _ = pack W n fun _ => 1 := rfl


theorem gV_eq (q : ℕ) :
    (G3K.phase q).gV = pack 96 (G3K.phase q).nL fun _ => 2 ^ 95 := by
  have h_gV : (G3K.phase q).gV = G3K.gVof (G3K.phase q).nL := by
    unfold G3K.phase
    by_cases h2 : 2 ≤ q
    · simp [h2]
      by_cases h3 : 3 ≤ q
      · simp [h3]
        by_cases h4 : 4 ≤ q
        · simp [h4, G3K.ph4]
        · simp [h4, G3K.ph3]
      · simp [h3, G3K.ph2]
    · simp [h2]
      by_cases h1 : 1 ≤ q
      · simp [h1, G3K.ph1]
      · simp [h1, G3K.ph0]
  rw [h_gV, G3K.gVof]
  have hW : 1 ≤ 96 := by norm_num
  rw [FrogModel.Engine.G3.pack_one_eq 96 ((G3K.phase q).nL) hW]
  rw [FrogModel.Lanes.pack_const_mul 96 ((G3K.phase q).nL) (2 ^ 95) (fun _ => 1)]
  simp

theorem lowV_eq (q : ℕ) :
    (G3K.phase q).lowV = pack 96 (G3K.phase q).nL fun _ => 2 ^ 47 - 1 := by
  have h2pow96_ge2 : 2 ≤ 2 ^ 96 := by
    have h : 1 ≤ 96 := by norm_num
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 96 := Nat.pow_le_pow_right (by norm_num) h
  have h_lowVof_eq_pack (n : ℕ) : G3K.lowVof n = FrogModel.Lanes.pack 96 n fun _ => 2 ^ 47 - 1 := by
    rw [G3K.lowVof, FrogModel.Lanes.pack, ← Finset.mul_sum]
    have hsum : ∑ l ∈ Finset.range n, 2 ^ (96 * l) = (2 ^ (96 * n) - 1) / (2 ^ 96 - 1) := by
      calc
        ∑ l ∈ Finset.range n, 2 ^ (96 * l) = ∑ l ∈ Finset.range n, ((2 : ℕ) ^ 96) ^ l := by
          simp [Nat.pow_mul]
        _ = (((2 : ℕ) ^ 96) ^ n - 1) / (((2 : ℕ) ^ 96) - 1) :=
          Nat.geomSum_eq h2pow96_ge2 n
        _ = (2 ^ (96 * n) - 1) / (2 ^ 96 - 1) := by simp [Nat.pow_mul]
    rw [hsum]
  have h_phase_lowV : (G3K.phase q).lowV = G3K.lowVof ((G3K.phase q).nL) := by
    unfold G3K.phase
    by_cases h2 : 2 ≤ q
    · simp [h2]
      by_cases h3 : 3 ≤ q
      · simp [h3]
        by_cases h4 : 4 ≤ q
        · simp [h4, G3K.ph4]
        · simp [h4, G3K.ph3]
      · simp [h3, G3K.ph2]
    · simp [h2]
      by_cases h1 : 1 ≤ q
      · simp [h1, G3K.ph1]
      · simp [h1, G3K.ph0]
  rw [h_phase_lowV, h_lowVof_eq_pack]

theorem gW_eq : G3K.Spec.gW = pack 128 9 fun _ => 2 ^ 127 := by
  unfold G3K.Spec.gW G3K.Spec.onesW
  have hcT : G3K.cT = 8 := rfl
  rw [hcT]
  have h_geom := Nat.geomSum_eq (by norm_num : 2 ≤ 2 ^ 128) 9
  have h_pow9 : (2 ^ 128) ^ 9 = 2 ^ (128 * 9) := by
    rw [← pow_mul, mul_comm]
  have h_powk (k : ℕ) : (2 ^ 128) ^ k = 2 ^ (128 * k) := by
    rw [← pow_mul, mul_comm]
  rw [h_pow9] at h_geom
  simp_rw [h_powk] at h_geom
  rw [← h_geom]
  rw [Finset.mul_sum]
  unfold pack
  simp

theorem lowWb_eq : G3K.Spec.lowWb = pack 128 9 fun _ => 2 ^ 77 - 1 := by
  unfold G3K.Spec.lowWb G3K.Spec.onesW pack
  have hcT : G3K.cT = 8 := rfl
  rw [hcT]
  have hm : 2 ≤ 2 ^ 128 := by norm_num
  have hgeom := Nat.geomSum_eq hm 9
  -- hgeom: ∑ k ∈ range 9, (2^128)^k = ((2^128)^9 - 1) / ((2^128) - 1)
  have hsum : (∑ k ∈ Finset.range 9, (2 ^ 128) ^ k) = ∑ k ∈ Finset.range 9, 2 ^ (128 * k) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Nat.pow_mul]
  have hpow9 : (2 ^ 128) ^ 9 = 2 ^ (128 * 9) := by rw [Nat.pow_mul]
  rw [hsum, hpow9] at hgeom
  -- hgeom: ∑ k ∈ range 9, 2^(128*k) = (2^(128*9) - 1) / (2^128 - 1)
  -- Now we need: (2^77 - 1) * ((2^(128*9) - 1) / (2^128 - 1)) = ∑ l ∈ range 9, (2^77 - 1) * 2^(128*l)
  rw [← Finset.mul_sum]
  -- Goal: (2^77 - 1) * ((2^(128*9) - 1) / (2^128 - 1)) = (2^77 - 1) * ∑ l ∈ range 9, 2^(128*l)
  rw [hgeom]

theorem lowW_eq : G3K.Spec.lowW = 2 ^ (128 * 8) - 2 ^ (128 * 0) := by
  decide +kernel

theorem nL_phase : (G3K.phase 1).nL = 495 ∧ (G3K.phase 2).nL = 165 ∧ (G3K.phase 3).nL = 45 ∧
    (G3K.phase 4).nL = 9 := by
  decide +kernel

/-- `n &&& pack W L (2^k - 1) = n` makes `n` the pack of `L` lanes below `2^k`. -/
theorem eq_pack_of_land_mask (W L k n : ℕ) (hk : k ≤ W) (hW : 1 ≤ W)
    (h : n &&& pack W L (fun _ => 2 ^ k - 1) = n) :
    pack W L (fun j => lane W j n) = n ∧ ∀ j, lane W j n < 2 ^ k ∧ (L ≤ j → lane W j n = 0) := by
  set M := pack W L (fun _ => 2 ^ k - 1) with hM
  have hM_lt : M < 2 ^ (W * L) := by
    rw [hM]
    apply FrogModel.Lanes.pack_lt
    intro l _
    exact two_pow_sub_one_lt_two_pow_of_le hk
  have hn_lt : n < 2 ^ (W * L) := by
    have hn_le_M : n ≤ M := by
      rw [← h]
      exact Nat.and_le_right
    exact lt_of_le_of_lt hn_le_M hM_lt
  have h_pack : pack W L (fun j => FrogModel.Engine.G3.lane W j n) = n := by
    rw [FrogModel.Engine.G3.pack_lane W L n hn_lt]
  refine And.intro h_pack ?_
  intro j
  have h_bound : FrogModel.Engine.G3.lane W j n < 2 ^ k := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [lane_testBit W j n i]
    by_cases hiW : i < W
    · simp [hiW]
      rw [← h, Nat.testBit_and]
      by_cases hjL : j < L
      · have hM_testBit : M.testBit (W * j + i) = decide (i < k) := by
          rw [hM]
          have hf : ∀ l < L, (2 ^ k - 1) < 2 ^ W := by
            intro l hl; exact two_pow_sub_one_lt_two_pow_of_le hk
          rw [FrogModel.Lanes.testBit_pack W L (fun _ => 2 ^ k - 1) hf j i hjL hiW]
          simp [Nat.testBit_two_pow_sub_one]
        rw [hM_testBit]
        have hik : ¬ i < k := Nat.not_lt.mpr hi
        simp [hik]
      · have hM_testBit : M.testBit (W * j + i) = false := by
          rw [hM]
          apply FrogModel.Lanes.testBit_pack_high W L (fun _ => 2 ^ k - 1)
          · intro l hl; exact two_pow_sub_one_lt_two_pow_of_le hk
          · have hjL' : L ≤ j := Nat.le_of_not_lt hjL
            nlinarith
        rw [hM_testBit]
        simp
    · simp [hiW]
  have h_high : L ≤ j → FrogModel.Engine.G3.lane W j n = 0 := by
    intro hjL
    have h_all_false : ∀ i, (FrogModel.Engine.G3.lane W j n).testBit i = false := by
      intro i
      rw [lane_testBit W j n i]
      by_cases hiW : i < W
      · simp [hiW]
        rw [← h, Nat.testBit_and]
        have hM_testBit : M.testBit (W * j + i) = false := by
          rw [hM]
          apply FrogModel.Lanes.testBit_pack_high W L (fun _ => 2 ^ k - 1)
          · intro l hl; exact two_pow_sub_one_lt_two_pow_of_le hk
          · have hjL' : L ≤ j := hjL
            nlinarith
        rw [hM_testBit]
        simp
      · simp [hiW]
    have h_lt_one : FrogModel.Engine.G3.lane W j n < 1 := by
      apply Nat.lt_pow_two_of_testBit (n := 0)
      intro i hi
      exact h_all_false i
    omega
  exact And.intro h_bound h_high

/-- **The bounds of an entry**. -/
theorem boundsOK_sound (s : G3K.E) (q : ℕ) (h : G3K.Spec.boundsOK s q = true) :
    pack 96 (G3K.phase q).nL (fun j => lane 96 j s.v) = s.v ∧
      (∀ j, lane 96 j s.v < 2 ^ 47 ∧ ((G3K.phase q).nL ≤ j → lane 96 j s.v = 0)) ∧
      pack 128 9 (fun j => lane 128 j s.w) = s.w ∧
      ∀ j, lane 128 j s.w < 2 ^ 77 ∧ (9 ≤ j → lane 128 j s.w = 0) := by
  unfold G3K.Spec.boundsOK at h
  have h_and : decide (s.v &&& (G3K.phase q).lowV = s.v) = true ∧
      decide (s.w &&& G3K.Spec.lowWb = s.w) = true := by
    simpa [Bool.and_eq_true] using h
  rcases h_and with ⟨hv_dec, hw_dec⟩
  have hv_eq : s.v &&& (G3K.phase q).lowV = s.v := by
    simpa [decide_eq_true_eq] using hv_dec
  have hw_eq : s.w &&& G3K.Spec.lowWb = s.w := by
    simpa [decide_eq_true_eq] using hw_dec
  rw [FrogModel.Engine.G3.lowV_eq q] at hv_eq
  rw [FrogModel.Engine.G3.lowWb_eq] at hw_eq
  have hk47 : 47 ≤ 96 := by omega
  have hW96 : 1 ≤ 96 := by omega
  have hk77 : 77 ≤ 128 := by omega
  have hW128 : 1 ≤ 128 := by omega
  have hV := FrogModel.Engine.G3.eq_pack_of_land_mask 96 (G3K.phase q).nL 47 s.v hk47 hW96 hv_eq
  rcases hV with ⟨hV_pack, hV_lane⟩
  have hW := FrogModel.Engine.G3.eq_pack_of_land_mask 128 9 77 s.w hk77 hW128 hw_eq
  rcases hW with ⟨hW_pack, hW_lane⟩
  exact ⟨hV_pack, hV_lane, hW_pack, hW_lane⟩

/-! ### Gathers -/

/-- The source lane of lane `l` under the gather `segs`: lane `l - s` for the first segment
`(a, b, s)` with `a + s ≤ l < b + s`. -/
def gsrc (segs : List (ℕ × ℕ × ℕ)) (l : ℕ) : Option ℕ :=
  (segs.find? fun g => decide (g.1 + g.2.2 ≤ l ∧ l < g.2.1 + g.2.2)).map fun g => l - g.2.2

/-- The segments read lanes below `L`, write lanes below `L'`, and write each lane at most once. -/
def SegsOK (L L' : ℕ) (segs : List (ℕ × ℕ × ℕ)) : Prop :=
  (∀ g ∈ segs, g.1 ≤ g.2.1 ∧ g.2.1 ≤ L ∧ g.2.1 + g.2.2 ≤ L') ∧
    segs.Pairwise fun g h => g.2.1 + g.2.2 ≤ h.1 + h.2.2 ∨ h.2.1 + h.2.2 ≤ g.1 + g.2.2

/-- **A gather of a pack** is the pack of the source lanes. -/
theorem gather_pack (L L' : ℕ) (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ 96)
    (segs : List (ℕ × ℕ × ℕ)) (hs : SegsOK L L' segs) :
    G3K.Spec.gather (pack 96 L f) segs =
      pack 96 L' fun l => match gsrc segs l with
        | some l0 => f l0
        | none => 0 := by
  rcases hs with ⟨hs_mem, hs_disjoint⟩
  have hW : 1 ≤ 96 := by norm_num
  induction' segs with g segs' ih
  · simp [G3K.Spec.gather, FrogModel.Engine.G3.gsrc, FrogModel.Lanes.pack]
  · rcases g with ⟨a, b, s⟩
    have ha_mem : (a, b, s) ∈ ((a, b, s) :: segs') := by simp
    rcases hs_mem (a, b, s) ha_mem with ⟨ha_le_b, hb_le_L, hbs_le_L'⟩
    have h_disjoint' : segs'.Pairwise fun (g h : ℕ × ℕ × ℕ) =>
      g.2.1 + g.2.2 ≤ h.1 + h.2.2 ∨ h.2.1 + h.2.2 ≤ g.1 + g.2.2 :=
      List.Pairwise.of_cons hs_disjoint
    have hs'_mem : ∀ g ∈ segs', g.1 ≤ g.2.1 ∧ g.2.1 ≤ L ∧ g.2.1 + g.2.2 ≤ L' := by
      intro g hg
      apply hs_mem g
      simp [hg]
    have hs'_ok : SegsOK L L' segs' := ⟨hs'_mem, h_disjoint'⟩
    have ih_unfolded : G3K.Spec.gather (pack 96 L f) segs' =
        pack 96 L' fun l => match gsrc segs' l with
          | some l0 => f l0
          | none => 0 := ih hs'_mem h_disjoint'
    -- The key equality for the first segment
    have h_first : ((pack 96 L f) &&& G3K.Spec.laneMask a b) * 2 ^ (96 * s) =
        pack 96 L' (fun l => if a + s ≤ l ∧ l < b + s then f (l - s) else 0) := by
      have h_land : (pack 96 L f) &&& G3K.Spec.laneMask a b =
          pack 96 L (fun l => if a ≤ l ∧ l < b then f l else 0) := by
        rw [G3K.Spec.laneMask]
        exact FrogModel.Lanes.land_mask 96 L a b hW ha_le_b hb_le_L f hf
      rw [h_land]
      set h := fun l : ℕ => if a ≤ l ∧ l < b then f l else 0 with hh
      have h_mul_pow : pack 96 L h * 2 ^ (96 * s) =
          pack 96 (L + s) (fun l => if l < s then 0 else h (l - s)) := by
        rw [FrogModel.Lanes.pack_mul_pow 96 L s h]
      rw [h_mul_pow]
      have h_func_eq : (fun l : ℕ => if l < s then 0 else h (l - s)) =
          (fun l : ℕ => if a + s ≤ l ∧ l < b + s then f (l - s) else 0) := by
        ext l
        dsimp [h]
        by_cases hlt : l < s
        · simp [hlt]
          omega
        · simp [hlt]
          by_cases hcond : a ≤ l - s ∧ l - s < b
          · simp [hcond]
            omega
          · simp [hcond]
            omega
      rw [h_func_eq]
      set g1 := fun l : ℕ => if a + s ≤ l ∧ l < b + s then f (l - s) else 0 with hg1
      have h_zero1 : ∀ l, b + s ≤ l → l < L + s → g1 l = 0 := by
        intro l hl hl'
        dsimp [g1]
        have : ¬ (a + s ≤ l ∧ l < b + s) := by
          intro ⟨h1, h2⟩
          omega
        simp [this]
      have h_bs_le_Ls : b + s ≤ L + s := Nat.add_le_add_right hb_le_L s
      have h_pack1 : pack 96 (L + s) g1 = pack 96 (b + s) g1 :=
        FrogModel.Lanes.pack_ext_len 96 (b + s) (L + s) g1 h_bs_le_Ls h_zero1
      have h_zero2 : ∀ l, b + s ≤ l → l < L' → g1 l = 0 := by
        intro l hl hl'
        dsimp [g1]
        have : ¬ (a + s ≤ l ∧ l < b + s) := by
          intro ⟨h1, h2⟩
          omega
        simp [this]
      have h_pack2 : pack 96 L' g1 = pack 96 (b + s) g1 :=
        FrogModel.Lanes.pack_ext_len 96 (b + s) L' g1 hbs_le_L' h_zero2
      rw [h_pack1, h_pack2]
    -- Now prove h_gsrc_cons
    have h_gsrc_cons : ∀ l : ℕ,
        (match gsrc ((a, b, s) :: segs') l with
        | some l0 => f l0
        | none => 0) =
        (if a + s ≤ l ∧ l < b + s then f (l - s) else 0) +
        (match gsrc segs' l with
        | some l0 => f l0
        | none => 0) := by
      intro l
      have h_cons_eq : gsrc ((a, b, s) :: segs') l =
          if a + s ≤ l ∧ l < b + s then some (l - s) else gsrc segs' l := by
        dsimp [FrogModel.Engine.G3.gsrc]
        by_cases h : a + s ≤ l ∧ l < b + s
        · simp [h]
        · simp [h]
      rw [h_cons_eq]
      by_cases h : a + s ≤ l ∧ l < b + s
      · -- need gsrc segs' l = none
        have h_not_covered : ∀ g ∈ segs', ¬ (g.1 + g.2.2 ≤ l ∧ l < g.2.1 + g.2.2) := by
          intro g hg
          have h_cons := (List.pairwise_cons.mp hs_disjoint).left
          have hR := h_cons g hg
          dsimp at hR
          intro h_covered
          rcases h_covered with ⟨hle1, hle2⟩
          rcases hR with (h_le | h_le)
          · omega
          · omega
        have h_none : gsrc segs' l = none := by
          rw [FrogModel.Engine.G3.gsrc, Option.map_eq_none_iff, List.find?_eq_none]
          intro g hg
          have h := h_not_covered g hg
          simpa using h
        simp [h, h_none]
      · simp [h]
    -- Now compute RHS
    calc
      G3K.Spec.gather (pack 96 L f) ((a, b, s) :: segs')
          = ((pack 96 L f) &&& G3K.Spec.laneMask a b) * 2 ^ (96 * s) +
            G3K.Spec.gather (pack 96 L f) segs' := rfl
      _ = pack 96 L' (fun l => if a + s ≤ l ∧ l < b + s then f (l - s) else 0) +
          G3K.Spec.gather (pack 96 L f) segs' := by rw [h_first]
      _ = pack 96 L' (fun l => if a + s ≤ l ∧ l < b + s then f (l - s) else 0) +
          pack 96 L' fun l => match gsrc segs' l with
            | some l0 => f l0
            | none => 0 := by rw [ih_unfolded]
      _ = pack 96 L' ((fun l => if a + s ≤ l ∧ l < b + s then f (l - s) else 0) +
          (fun l => match gsrc segs' l with
            | some l0 => f l0
            | none => 0)) := by
        rw [FrogModel.Lanes.pack_add 96 L' _ _]
        rfl
      _ = pack 96 L' fun l => match gsrc ((a, b, s) :: segs') l with
          | some l0 => f l0
          | none => 0 := by
        refine FrogModel.Lanes.pack_congr 96 L' _ _ (fun l hl => ?_)
        rw [h_gsrc_cons l]
        rfl

theorem segsOK_phase (q : ℕ) (hq : 1 ≤ q) (hq4 : q ≤ 4) :
    SegsOK (G3K.phase q).nL (G3K.phase q).nL (G3K.phase q).gx ∧
      (q < 4 → SegsOK (G3K.phase (q + 1)).nL (G3K.phase q).nL (G3K.phase q).cp0 ∧
        SegsOK (G3K.phase (q + 1)).nL (G3K.phase q).nL (G3K.phase q).cp1) := by
  unfold SegsOK
  interval_cases q <;> decide +kernel

/-! ### Comparisons -/

/-- **`leLanes` lane by lane**: `a ≤ b` in every lane, both below the guard bit. -/
theorem leLanes_pack (W L : ℕ) (hW : 1 ≤ W) (f g : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ (W - 1))
    (hg : ∀ l < L, g l < 2 ^ (W - 1)) :
    G3K.Spec.leLanes (pack W L fun _ => 2 ^ (W - 1)) (pack W L f) (pack W L g) = true ↔
      ∀ l < L, f l ≤ g l := by
  unfold G3K.Spec.leLanes
  rw [decide_eq_true_eq]
  have h_guard : FrogModel.Lanes.guard W L = pack W L fun _ => 2 ^ (W - 1) := rfl
  have h_eq : (FrogModel.Lanes.leLanes (FrogModel.Lanes.guard W L) (FrogModel.Lanes.pack W L f)
      (FrogModel.Lanes.pack W L g) = true) ↔
      (((pack W L g + (pack W L fun _ => 2 ^ (W - 1)) - pack W L f) &&&
        (pack W L fun _ => 2 ^ (W - 1)) = pack W L fun _ => 2 ^ (W - 1))) := by
    unfold FrogModel.Lanes.leLanes
    rw [h_guard, Nat.beq_eq]
  rw [← h_eq]
  exact FrogModel.Lanes.leLanes_iff W L hW f g hf hg

end FrogModel.Engine.G3
