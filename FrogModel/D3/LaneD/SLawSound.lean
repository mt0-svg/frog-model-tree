module

public import FrogModel.D3.LaneD.Pack
public import FrogModel.D3.LaneC.Order

@[expose] public section

/-!
# Soundness of the S2 and S3 laws of the kernel checker

`s2Laws` and `s3Laws` (FrogModel/D3/LaneD/K/SLaws.lean) bound every mass of the staged recursion
`stageLaw` of the lower closures (FrogModel/D3/Interfaces/Step.lean) from above, at `2^-W`. This file
proves it: every slot of each kernel row is at least `2^W` times the real mass (`s2Laws_sound`,
`s3Laws_sound`), and each row fits its `n` slots (`s2Laws_lt`, `s3Laws_lt`).

The route, stage by stage from the innermost: a row is a packed natural with `n` slots of
`SW = 2 W + 8` bits; `rowStep` maps the slots `g` of a row and `t` of a window term to
`ceil((cg g i + cc kcs(g) i + t i) / 2^W)` (`rowStep_pk`), with `kcs` the slots of the kernel's
`capShift`; the window terms are the sums `sum over r of pnR(r) nxt(y + r)` (`windows_getD`). The masses
of the rows (`lmass`) grow by at most `2 gamma + n` per row, so every slot stays far below `2^SW`
(`rowSeq_inv`); the real bound follows by induction over the rows (`rowSeq_real`). `StageOK`
collects both for the rows of a stage (`stage_last`, `stage_step`).
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.Iface FrogModel.D3.LaneD.K Finset

/-! ## Packed naturals -/

theorem sl_pk_slot (w n N : ℕ) (hN : N < 2 ^ (w * n)) : pk w (fun i => slot w N i) n = N := by
  have key : ∀ m, pk w (fun i => slot w N i) m = N % 2 ^ (w * m) := by
    intro m
    induction m with
    | zero => simp [pk, Nat.mod_one]
    | succ m ih =>
      rw [pk_succ, ih, slot_eq, mul_add, mul_one, pow_add, Nat.mod_mul]
      ring
  rw [key, Nat.mod_eq_of_lt hN]

theorem sl_pk_land (w n : ℕ) (a b : ℕ → ℕ) (ha : ∀ i < n, a i < 2 ^ w) (hb : ∀ i < n, b i < 2 ^ w) :
    pk w a n &&& pk w b n = pk w (fun i => a i &&& b i) n := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ha' : ∀ i < n, a i < 2 ^ w := fun i hi => ha i (by omega)
    have hb' : ∀ i < n, b i < 2 ^ w := fun i hi => hb i (by omega)
    have hA := pk_lt w a n ha'
    have hB := pk_lt w b n hb'
    have hAB : (pk w a n &&& pk w b n) < 2 ^ (w * n) := Nat.and_lt_two_pow _ hB
    rw [pk_succ, pk_succ, pk_succ, ← ih ha' hb']
    have key : ∀ x y : ℕ, x < 2 ^ (w * n) → ∀ i, (x + y * 2 ^ (w * n)).testBit i =
        if i < w * n then x.testBit i else y.testBit (i - w * n) := by
      intro x y hx i
      rw [show x + y * 2 ^ (w * n) = 2 ^ (w * n) * y + x by ring, Nat.testBit_two_pow_mul_add _ hx]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land, key _ _ hA, key _ _ hB, key _ _ hAB]
    split_ifs <;> simp

theorem sl_land_hi (W S y : ℕ) (hWS : W ≤ S) (hy : y < 2 ^ S) :
    y &&& (2 ^ S - 2 ^ W) = y / 2 ^ W * 2 ^ W := by
  have hm : 2 ^ S - 2 ^ W = 2 ^ W * (2 ^ (S - W) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hWS]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, hm, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases h1 : W ≤ i
  · rw [Nat.sub_add_cancel h1]
    by_cases h2 : i < S
    · simp [h1, show i - W < S - W by omega]
    · have : y.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [this]
  · simp [h1]

theorem sl_pk_shiftRight (w W n : ℕ) (f : ℕ → ℕ) : pk w (fun i => f i * 2 ^ W) n >>> W = pk w f n := by
  rw [Nat.shiftRight_eq_div_pow]
  have : pk w (fun i => f i * 2 ^ W) n = 2 ^ W * pk w f n := by
    rw [pk_smul]
    exact pk_congr _ _ _ _ fun i _ => mul_comm _ _
  rw [this, Nat.mul_div_cancel_left _ (by positivity)]

theorem sl_slot_lt (w x i : ℕ) : slot w x i < 2 ^ w := by
  rw [slot_eq]
  exact Nat.mod_lt _ (by positivity)

/-! ## The kernel's row operations -/

theorem sl_SW (c : LawCfg) : c.SW = 2 * c.W + 8 := rfl

theorem sl_ceilK_pk (c : LawCfg) (h : ℕ → ℕ) (hh : ∀ i < c.n, h i + (2 ^ c.W - 1) < 2 ^ c.SW) :
    ceilK c (pk c.SW h c.n) = pk c.SW (fun i => (h i + (2 ^ c.W - 1)) / 2 ^ c.W) c.n := by
  have hSW : 0 < c.SW := by rw [sl_SW]; omega
  have hWS : 2 ^ c.W ≤ 2 ^ c.SW := Nat.pow_le_pow_right (by norm_num) (by rw [sl_SW]; omega)
  have h1 : 1 ≤ 2 ^ c.W := Nat.one_le_two_pow
  have hlow : lowOnes c = pk c.SW (fun _ => 2 ^ c.W - 1) c.n := by
    show mask c.W * ones c.SW c.n = _
    rw [mask_eq, ones_eq _ _ hSW, pk_smul]
    simp
  have hhi : hiMask c = pk c.SW (fun _ => 2 ^ c.SW - 2 ^ c.W) c.n := by
    show (mask c.SW - mask c.W) * ones c.SW c.n = _
    rw [mask_eq, mask_eq, ones_eq _ _ hSW, pk_smul]
    exact pk_congr _ _ _ _ fun i _ => by omega
  show ((pk c.SW h c.n + lowOnes c) &&& hiMask c) >>> c.W = _
  rw [hlow, hhi, pk_add, sl_pk_land _ _ _ _ (fun i hi => hh i hi) (fun i _ => by omega)]
  rw [pk_congr _ _ (fun i => (h i + (2 ^ c.W - 1)) / 2 ^ c.W * 2 ^ c.W) _
    (fun i hi => sl_land_hi _ _ _ (by rw [sl_SW]; omega) (hh i hi))]
  exact sl_pk_shiftRight _ _ _ _

theorem sl_ceilK_lt (c : LawCfg) (x : ℕ) : ceilK c x < 2 ^ (c.SW * c.n) := by
  have hSW : 0 < c.SW := by rw [sl_SW]; omega
  have h1 : 1 ≤ 2 ^ c.SW := Nat.one_le_two_pow
  have hhi : hiMask c ≤ pk c.SW (fun _ => 2 ^ c.SW - 1) c.n := by
    show (mask c.SW - mask c.W) * ones c.SW c.n ≤ _
    rw [mask_eq, mask_eq, ones_eq _ _ hSW, pk_smul]
    unfold pk
    exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (by dsimp only; omega)
  have hlt : pk c.SW (fun _ => 2 ^ c.SW - 1) c.n < 2 ^ (c.SW * c.n) := pk_lt _ _ _ (fun _ _ => by omega)
  show ((x + lowOnes c) &&& hiMask c) >>> c.W < _
  rw [Nat.shiftRight_eq_div_pow]
  calc _ ≤ (x + lowOnes c) &&& hiMask c := Nat.div_le_self _ _
    _ ≤ hiMask c := Nat.and_le_right
    _ < _ := lt_of_le_of_lt hhi hlt

/-- The slots of the kernel's `capShift` on `n` slots: slot `i` gets `g (i - 1)`, the top slot `n - 1`
keeps `g (n - 1)` too. -/
def kcs (n : ℕ) (g : ℕ → ℕ) (i : ℕ) : ℕ :=
  (if i = 0 then 0 else g (i - 1)) + if i = n - 1 then g (n - 1) else 0

theorem sl_capShift_pk (c : LawCfg) (g : ℕ → ℕ) (hn : 1 ≤ c.n) (hg : ∀ i < c.n, g i < 2 ^ c.SW) :
    K.capShift c (pk c.SW g c.n) = pk c.SW (kcs c.n g) c.n := by
  show ((pk c.SW g c.n <<< c.SW) &&& mask c.RS) +
    ((pk c.SW g c.n >>> (c.SW * (c.n - 1))) <<< (c.SW * (c.n - 1))) = _
  have h1 : pk c.SW g c.n <<< c.SW = pk c.SW (fun i => if i < 1 then 0 else g (i - 1)) (c.n + 1) := by
    have := pk_shiftLeft c.SW g c.n 1
    rwa [mul_one] at this
  have h2 : pk c.SW (fun i => if i < 1 then 0 else g (i - 1)) (c.n + 1) &&& mask c.RS =
      pk c.SW (fun i => if i < 1 then 0 else g (i - 1)) c.n := by
    rw [and_mask, show c.RS = c.SW * c.n from Nat.mul_comm _ _, pk_mod]
    · congr 1
      omega
    · intro i hi
      split_ifs
      · positivity
      · exact hg _ (by omega)
  have h3 : pk c.SW g c.n >>> (c.SW * (c.n - 1)) = g (c.n - 1) := by
    rw [Nat.shiftRight_eq_div_pow, pk_div _ _ _ _ hg, show c.n - (c.n - 1) = 1 by omega]
    simp [pk]
  have h4 : g (c.n - 1) <<< (c.SW * (c.n - 1)) =
      pk c.SW (fun i => if i = c.n - 1 then g (c.n - 1) else 0) c.n := by
    rw [Nat.shiftLeft_eq]
    unfold pk
    rw [Finset.sum_eq_single (c.n - 1)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  rw [h1, h2, h3, h4, pk_add]
  refine pk_congr _ _ _ _ fun i _ => ?_
  unfold kcs
  by_cases hi0 : i = 0 <;> simp [hi0]

theorem sl_kcs_sum (n : ℕ) (g : ℕ → ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range n, kcs n g i = ∑ i ∈ range n, g i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [kcs, Finset.sum_add_distrib, Nat.add_sub_cancel]
  rw [Finset.sum_range_succ' (fun i => if i = 0 then 0 else g (i - 1))]
  simp [Finset.sum_range_succ]

theorem sl_kcs_le (n : ℕ) (g : ℕ → ℕ) (i : ℕ) (hi : i < n) : kcs n g i ≤ ∑ j ∈ range n, g j := by
  have single : ∀ j < n, g j ≤ ∑ j ∈ range n, g j :=
    fun j hj => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
  unfold kcs
  split_ifs with h1 h2 h2
  · simpa using single (n - 1) (by omega)
  · simp
  · calc g (i - 1) + g (n - 1) = ∑ j ∈ {i - 1, n - 1}, g j := (Finset.sum_pair (by omega)).symm
      _ ≤ ∑ j ∈ range n, g j := by
        apply Finset.sum_le_sum_of_subset
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [Finset.mem_range]
        omega
  · simpa using single (i - 1) (by omega)

theorem sl_kcs_real (W n : ℕ) (g : ℕ → ℕ) (A : ℕ → ℝ) (hA : ∀ k < n, 2 ^ W * A k ≤ g k)
    (k : ℕ) (hk : k < n) :
    2 ^ W * Iface.capShift (n - 1) A k ≤ (kcs n g k : ℝ) := by
  by_cases h0 : k = 0
  · subst h0
    have : Iface.capShift (n - 1) A 0 = 0 := by simp [Iface.capShift]
    rw [this, mul_zero]
    positivity
  · by_cases hlt : k < n - 1
    · have hne : k ≠ n - 1 := by omega
      simp only [Iface.capShift, kcs, h0, hlt, hne, ↓reduceIte, add_zero]
      exact hA _ (by omega)
    · have heq : k = n - 1 := by omega
      subst heq
      simp only [Iface.capShift, kcs, h0, hlt, ↓reduceIte, Nat.cast_add, mul_add]
      exact add_le_add (hA _ (by omega)) (hA _ (by omega))

theorem sl_rowStep_pk (c : LawCfg) (hn : 1 ≤ c.n) (cg cc : ℕ) (g t : ℕ → ℕ)
    (hg : ∀ i < c.n, g i < 2 ^ c.SW)
    (hov : ∀ i < c.n, cg * g i + cc * kcs c.n g i + t i + (2 ^ c.W - 1) < 2 ^ c.SW) :
    rowStep c cg cc (pk c.SW g c.n) (pk c.SW t c.n) =
      pk c.SW (fun i => (cg * g i + cc * kcs c.n g i + t i + (2 ^ c.W - 1)) / 2 ^ c.W) c.n := by
  show ceilK c (cg * pk c.SW g c.n + cc * K.capShift c (pk c.SW g c.n) + pk c.SW t c.n) = _
  rw [sl_capShift_pk c g hn hg, pk_smul, pk_smul, pk_add, pk_add]
  exact sl_ceilK_pk c _ hov

theorem sl_unit_pk (c : LawCfg) (hn : 1 ≤ c.n) :
    K.unit c = pk c.SW (fun i => if i = 0 then 2 ^ c.W else 0) c.n := by
  show 1 <<< c.W = _
  rw [Nat.shiftLeft_eq, one_mul]
  unfold pk
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_range.2 hn) h

theorem sl_ceil_sum (W n : ℕ) (h : ℕ → ℕ) :
    2 ^ W * ∑ i ∈ range n, (h i + (2 ^ W - 1)) / 2 ^ W ≤ ∑ i ∈ range n, h i + n * 2 ^ W := by
  rw [Finset.mul_sum]
  calc ∑ i ∈ range n, 2 ^ W * ((h i + (2 ^ W - 1)) / 2 ^ W) ≤ ∑ i ∈ range n, (h i + 2 ^ W) :=
        Finset.sum_le_sum fun i _ => (Nat.mul_div_le _ _).trans (by have := Nat.one_le_two_pow (n := W); omega)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem sl_ceil_real (W h : ℕ) : (h : ℝ) / 2 ^ W ≤ (((h + (2 ^ W - 1)) / 2 ^ W : ℕ) : ℝ) := by
  have hX : (0 : ℝ) < 2 ^ W := by positivity
  rw [div_le_iff₀ hX]
  have h1 := Nat.div_add_mod (h + (2 ^ W - 1)) (2 ^ W)
  have h2 := Nat.mod_lt (h + (2 ^ W - 1)) (show 0 < 2 ^ W by positivity)
  have h3 : 1 ≤ 2 ^ W := Nat.one_le_two_pow
  rw [mul_comm] at h1
  have : h ≤ (h + (2 ^ W - 1)) / 2 ^ W * 2 ^ W := by omega
  exact_mod_cast this

theorem sl_cdiv_le (a b : ℕ) (hb : 0 < b) : b * cdiv a b ≤ a + (b - 1) := by
  show b * ((a + b - 1) / b) ≤ _
  have := Nat.mul_div_le (a + b - 1) b
  omega

theorem sl_cdiv_ge (a b : ℕ) (hb : 0 < b) : a ≤ b * cdiv a b := by
  show a ≤ b * ((a + b - 1) / b)
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  omega
theorem sl_cst_eq (c : LawCfg) (a b : ℕ) : cst c a b = cdiv (a * 2 ^ c.W) b := by
  show cdiv (a <<< c.W) b = _
  rw [Nat.shiftLeft_eq]

/-! ## Lists -/

/-- The rows of a stage as a sequence. -/
def rowSeq (c : LawCfg) (cg cc : ℕ) (ts : List ℕ) : ℕ → ℕ
  | 0 => K.unit c
  | y + 1 => rowStep c cg cc (rowSeq c cg cc ts y) (ts.getD y 0)

theorem sl_natFold_succ {α : Type} (n : ℕ) (init : α) (f : ℕ → α → α) :
    natFold (n + 1) init f = f n (natFold n init f) := rfl

theorem sl_hd_eq (l : List ℕ) : hd l = l.getD 0 0 := by
  cases l <;> rfl

/-- The loop of `stageRows` after `m` rows. -/
theorem sl_stageRows_fold (c : LawCfg) (cg cc : ℕ) (ts : List ℕ) (m : ℕ) :
    natFold m ([K.unit c], ts) (fun _ (st : List ℕ × List ℕ) =>
      (rowStep c cg cc (hd st.1) (hd st.2) :: st.1, tl st.2)) =
    (((List.range (m + 1)).map (rowSeq c cg cc ts)).reverse, ts.drop m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sl_natFold_succ, ih]
    have h1 : hd ((List.map (rowSeq c cg cc ts) (List.range (m + 1))).reverse) = rowSeq c cg cc ts m := by
      rw [List.range_succ, List.map_append, List.reverse_append]
      rfl
    have h2 : hd (ts.drop m) = ts.getD m 0 := by
      rw [sl_hd_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
        Nat.add_zero]
    simp only [h1, h2, tl, List.tail_drop]
    congr 1
    rw [List.range_succ (n := m + 1), List.map_append, List.reverse_append]
    rfl

theorem sl_stageRows_length (c : LawCfg) (Y cg cc : ℕ) (ts : List ℕ) :
    (stageRows c Y cg cc ts).length = Y + 1 := by
  unfold stageRows
  rw [sl_stageRows_fold]
  simp

theorem sl_stageRows_getD (c : LawCfg) (Y cg cc : ℕ) (ts : List ℕ) (y : ℕ) (hy : y ≤ Y) :
    (stageRows c Y cg cc ts).getD y 0 = rowSeq c cg cc ts y := by
  unfold stageRows
  rw [sl_stageRows_fold, List.reverse_reverse, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega)]
  rfl

theorem sl_dropN_getD (k : ℕ) (l : List ℕ) (y : ℕ) : (dropN k l).getD y 0 = l.getD (y + k) 0 := by
  have h : dropN k l = l.drop k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      show tl (dropN k l) = _
      rw [ih]
      simp [tl, List.tail_drop]
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, add_comm]

theorem sl_reverse_getD (l : List ℕ) (j : ℕ) :
    l.reverse.getD j 0 = if j < l.length then l.getD (l.length - 1 - j) 0 else 0 := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_reverse h, List.getD_eq_getElem?_getD]
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem sl_scaleUp_length (a b : ℕ) (r : List ℕ) : (scaleUp a b r).length = r.length := by
  simp [scaleUp]

theorem sl_scaleUp_getD (a b : ℕ) (r : List ℕ) (i : ℕ) :
    (scaleUp a b r).getD i 0 = cdiv (r.getD i 0 * a) b := by
  simp only [scaleUp, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases r[i]? with
  | some x => rfl
  | none =>
    show 0 = (0 * a + b - 1) / b
    rcases Nat.eq_zero_or_pos b with hb | hb
    · simp [hb]
    · exact (Nat.div_eq_of_lt (by omega)).symm

/-- The loop of `pseudoLaw` after `m` entries. -/
theorem sl_pseudoLaw_fold (W row : ℕ) (f : ℕ → List ℕ × ℕ → List ℕ × ℕ)
    (hf : ∀ g st, f g st = ((slot 64 row g - st.2) * 2 ^ (W - 52) :: st.1, slot 64 row g)) (m : ℕ) :
    natFold m ([], 0) f = (((List.range m).map fun g =>
        (slot 64 row g - (if g = 0 then 0 else slot 64 row (g - 1))) * 2 ^ (W - 52)).reverse,
      if m = 0 then 0 else slot 64 row (m - 1)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sl_natFold_succ, ih, hf, List.range_succ, List.map_append, List.reverse_append]
    cases m with
    | zero => simp
    | succ m => simp

theorem sl_shiftLeft (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

/-- `pseudoLaw` as a list: the masses `d g` for `g ≤ GM`, then the top mass. -/
theorem sl_pseudoLaw_eq (W GM row : ℕ) :
    pseudoLaw W GM row = (List.range (GM + 1)).map (fun g =>
        (slot 64 row g - (if g = 0 then 0 else slot 64 row (g - 1))) * 2 ^ (W - 52)) ++
      [(2 ^ 52 - slot 64 row GM) * 2 ^ (W - 52)] := by
  unfold pseudoLaw
  rw [sl_pseudoLaw_fold W row _ ?hf]
  · simp only [Nat.add_eq, Nat.sub_eq, sl_shiftLeft, one_mul, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel, List.reverse_cons, List.reverse_reverse]
  · intro g st
    simp only [sl_shiftLeft, Nat.sub_eq]

theorem sl_pseudoLaw_length (W GM row : ℕ) : (pseudoLaw W GM row).length = GM + 2 := by
  rw [sl_pseudoLaw_eq]
  simp

theorem sl_pseudoLaw_getD (W GM row r : ℕ) :
    (pseudoLaw W GM row).getD r 0 =
      (if r ≤ GM then slot 64 row r - (if r = 0 then 0 else slot 64 row (r - 1))
        else if r = GM + 1 then 2 ^ 52 - slot 64 row GM else 0) * 2 ^ (W - 52) := by
  rw [sl_pseudoLaw_eq]
  by_cases h1 : r ≤ GM
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    simp [h1]
  · by_cases h2 : r = GM + 1
    · subst h2
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [h1, h2]

theorem sl_pseudoLaw_sum (W GM row : ℕ) (hW : 52 ≤ W)
    (hmono : ∀ g < GM, slot 64 row g ≤ slot 64 row (g + 1)) (htop : slot 64 row GM ≤ 2 ^ 52) :
    ∑ r ∈ range (GM + 2), (pseudoLaw W GM row).getD r 0 = 2 ^ W := by
  have tele : ∀ m ≤ GM, ∑ r ∈ range (m + 1),
      (slot 64 row r - (if r = 0 then 0 else slot 64 row (r - 1))) = slot 64 row m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have := hmono m (by omega)
      omega
  simp only [sl_pseudoLaw_getD]
  rw [show GM + 2 = GM + 1 + 1 from rfl, Finset.sum_range_succ]
  have h1 : ∑ r ∈ range (GM + 1), (if r ≤ GM then slot 64 row r - (if r = 0 then 0 else
      slot 64 row (r - 1)) else if r = GM + 1 then 2 ^ 52 - slot 64 row GM else 0) * 2 ^ (W - 52) =
      slot 64 row GM * 2 ^ (W - 52) := by
    rw [← Finset.sum_mul, ← tele GM le_rfl]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have : r ≤ GM := by simp only [Finset.mem_range] at hr; omega
    simp [this]
  rw [h1]
  simp only [show ¬ GM + 1 ≤ GM by omega, ↓reduceIte]
  rw [← add_mul, Nat.add_sub_cancel' htop, ← pow_add, Nat.add_sub_cancel' hW]

theorem sl_pseudoLaw_real (W GM row : ℕ) (F1 : ℕ → ℝ) (hW : 52 ≤ W)
    (hF1 : ∀ g ≤ GM, F1 g = (slot 64 row g : ℝ) / 2 ^ 52)
    (hmono : ∀ g < GM, slot 64 row g ≤ slot 64 row (g + 1)) (htop : slot 64 row GM ≤ 2 ^ 52) (r : ℕ) :
    ((pseudoLaw W GM row).getD r 0 : ℝ) = 2 ^ W * plR F1 GM r := by
  rw [sl_pseudoLaw_getD]
  have hpow : (2 : ℝ) ^ W = 2 ^ 52 * 2 ^ (W - 52) := by rw [← pow_add, Nat.add_sub_cancel' hW]
  unfold plR Ftil
  by_cases hr0 : r = 0
  · subst hr0
    simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      hF1 0 (Nat.zero_le _), hpow]
    field_simp
  · by_cases hrG : r ≤ GM
    · have hle : slot 64 row (r - 1) ≤ slot 64 row r := by
        have := hmono (r - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega)] at this
      simp only [hr0, hrG, show r ≤ GM + 1 by omega, show r - 1 ≤ GM by omega, ↓reduceIte,
        hF1 r hrG, hF1 (r - 1) (by omega), Nat.cast_mul, Nat.cast_sub hle, Nat.cast_pow,
        Nat.cast_ofNat, hpow]
      field_simp
    · by_cases hr1 : r = GM + 1
      · subst hr1
        simp only [hr0, hrG, le_refl, ↓reduceIte, Nat.add_sub_cancel, hF1 GM le_rfl, Nat.cast_mul,
          Nat.cast_sub htop, Nat.cast_pow, Nat.cast_ofNat, hpow]
        field_simp
      · simp [hr0, hrG, hr1, show ¬ r ≤ GM + 1 by omega]

/-! ## The window terms -/

theorem sl_conv_pk (w n : ℕ) (rows : ℕ → ℕ) (b : ℕ → ℕ) (L M u : ℕ)
    (hrows : ∀ i, rows i < 2 ^ (w * n)) :
    (∑ i ∈ range L, ∑ j ∈ range M, if i + j = u then rows i * b j else 0) =
      pk w (fun s => ∑ i ∈ range L, ∑ j ∈ range M,
        if i + j = u then slot w (rows i) s * b j else 0) n := by
  have key : ∀ i j, (if i + j = u then rows i * b j else 0) =
      pk w (fun s => if i + j = u then slot w (rows i) s * b j else 0) n := by
    intro i j
    split_ifs
    · conv_lhs => rw [← sl_pk_slot w n (rows i) (hrows i)]
      rw [mul_comm, pk_smul]
      exact pk_congr _ _ _ _ fun s _ => mul_comm _ _
    · simp [pk]
  simp_rw [key]
  rw [Finset.sum_congr rfl fun i _ => pk_sum w (range M) _ n, pk_sum]

theorem sl_conv_le (w : ℕ) (rows : ℕ → ℕ) (b : ℕ → ℕ) (L M u s Bs : ℕ)
    (hslot : ∀ i, slot w (rows i) s ≤ Bs) :
    (∑ i ∈ range L, ∑ j ∈ range M, if i + j = u then slot w (rows i) s * b j else 0) ≤
      (∑ j ∈ range M, b j) * Bs := by
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  calc ∑ i ∈ range L, (if i + j = u then slot w (rows i) s * b j else 0)
      ≤ ∑ i ∈ range L, (if i = u - j then Bs * b j else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h1 h2
        · exact Nat.mul_le_mul_right _ (hslot i)
        · omega
        · exact Nat.zero_le _
        · exact le_rfl
    _ ≤ Bs * b j := by
        rw [Finset.sum_ite_eq']
        split_ifs <;> simp
    _ = b j * Bs := mul_comm _ _

theorem sl_conv_reindex (rm y L : ℕ) (a b : ℕ → ℕ) (hz : ∀ i, L ≤ i → a i = 0) :
    (∑ i ∈ range L, ∑ j ∈ range (rm + 1), if i + j = y + rm then a i * b (rm - j) else 0) =
      ∑ r ∈ range (rm + 1), b r * a (y + r) := by
  rw [Finset.sum_comm]
  have hj : ∀ j ∈ range (rm + 1), (∑ i ∈ range L, if i + j = y + rm then a i * b (rm - j) else 0) =
      a (y + rm - j) * b (rm - j) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [Finset.sum_eq_single (y + rm - j)]
    · simp only [show y + rm - j + j = y + rm by omega, ↓reduceIte]
    · intro i _ hi
      simp only [show ¬ i + j = y + rm by omega, ↓reduceIte]
    · intro h
      simp only [show y + rm - j + j = y + rm by omega, ↓reduceIte]
      rw [hz _ (by simpa using h), zero_mul]
  rw [Finset.sum_congr rfl hj, ← Finset.sum_range_reflect (fun r => b r * a (y + r))]
  refine Finset.sum_congr rfl fun j hj' => ?_
  have := Finset.mem_range.1 hj'
  rw [show rm + 1 - 1 - j = rm - j by omega, show y + rm - j = y + (rm - j) by omega, mul_comm]

theorem sl_windows_getD (c : LawCfg) (pnR nxt : List ℕ) (Bs : ℕ) (hpn : pnR ≠ [])
    (hrow : ∀ i, nxt.getD i 0 < 2 ^ (c.SW * c.n))
    (hslot : ∀ i, ∀ s < c.n, slot c.SW (nxt.getD i 0) s ≤ Bs)
    (hov : (∑ r ∈ range pnR.length, pnR.getD r 0) * Bs < 2 ^ c.SW) (y : ℕ) :
    (windows c pnR nxt).getD y 0 =
      pk c.SW (fun s => ∑ r ∈ range pnR.length, pnR.getD r 0 * slot c.SW (nxt.getD (y + r) 0) s) c.n := by
  have hw : windows c pnR nxt = dropN (pnR.length - 1) (split c.RS (nxt.length + (pnR.length - 1))
      (packRows c.RS nxt * packRows c.RS pnR.reverse)) := rfl
  rw [hw]
  have hm1 : 1 ≤ pnR.length := List.length_pos_iff_ne_nil.2 hpn
  obtain ⟨rmax, hrm⟩ : ∃ rmax, pnR.length = rmax + 1 := ⟨pnR.length - 1, by omega⟩
  rw [hrm, Nat.add_sub_cancel]
  rw [hrm] at hov
  set L := nxt.length with hL
  have hRS : c.RS = c.SW * c.n := Nat.mul_comm _ _
  set b : ℕ → ℕ := fun j => pnR.reverse.getD j 0 with hb
  have hbj : ∀ j < rmax + 1, b j = pnR.getD (rmax - j) 0 := by
    intro j hj
    simp only [hb, sl_reverse_getD, hrm, hj, ↓reduceIte]
    congr 1
  set U : ℕ → ℕ := fun u => ∑ i ∈ range L, ∑ j ∈ range (rmax + 1),
    if i + j = u then nxt.getD i 0 * b j else 0 with hU
  have hprod : packRows c.RS nxt * packRows c.RS pnR.reverse = pk c.RS U (L + (rmax + 1)) := by
    rw [packRows_eq, packRows_eq, List.length_reverse, hrm, pk_mul]
  have hsumb : ∑ j ∈ range (rmax + 1), b j = ∑ r ∈ range (rmax + 1), pnR.getD r 0 := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [hbj _ (by omega)]
    congr 1
    omega
  have hVlt : ∀ u, ∀ s < c.n, (∑ i ∈ range L, ∑ j ∈ range (rmax + 1),
      if i + j = u then slot c.SW (nxt.getD i 0) s * b j else 0) < 2 ^ c.SW := by
    intro u s hs
    calc _ ≤ (∑ j ∈ range (rmax + 1), b j) * Bs :=
          sl_conv_le c.SW (fun i => nxt.getD i 0) b L (rmax + 1) u s Bs (fun i => hslot i s hs)
      _ < 2 ^ c.SW := by rw [hsumb]; exact hov
  have hUpk : ∀ u, U u = pk c.SW (fun s => ∑ i ∈ range L, ∑ j ∈ range (rmax + 1),
      if i + j = u then slot c.SW (nxt.getD i 0) s * b j else 0) c.n :=
    fun u => sl_conv_pk c.SW c.n (fun i => nxt.getD i 0) b L (rmax + 1) u hrow
  have hUlt : ∀ u, U u < 2 ^ c.RS := by
    intro u
    rw [hUpk u, hRS]
    exact pk_lt _ _ _ (hVlt u)
  have hUlast : ∀ u, L + rmax ≤ u → U u = 0 := by
    intro u hu
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    have := Finset.mem_range.1 hi
    have := Finset.mem_range.1 hj
    simp only [show ¬ i + j = u by omega, ↓reduceIte]
  have hext : pk c.RS U (L + (rmax + 1)) = pk c.RS U (L + rmax) :=
    pk_extend _ _ _ _ (by omega) (fun i h1 _ => hUlast i h1)
  have hlt : pk c.RS U (L + rmax) < 2 ^ (c.RS * 2 ^ clog (L + rmax)) :=
    lt_of_lt_of_le (pk_lt _ _ _ (fun i _ => hUlt i))
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (clog_spec _)))
  rw [hprod, hext, sl_dropN_getD, split_eq _ _ _ hlt]
  have key : ((List.range (2 ^ clog (L + rmax))).map fun i => slot c.RS (pk c.RS U (L + rmax)) i).getD
      (y + rmax) 0 = U (y + rmax) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases h : y + rmax < 2 ^ clog (L + rmax)
    · rw [List.getElem?_range h, Option.map_some, Option.getD_some,
        slot_pk _ _ _ _ (fun i _ => hUlt i)]
      split_ifs with h'
      · rfl
      · exact (hUlast _ (by omega)).symm
    · rw [List.getElem?_eq_none (by simpa using h), Option.map_none, Option.getD_none]
      exact (hUlast _ (by have := clog_spec (L + rmax); omega)).symm
  rw [key, hUpk]
  refine pk_congr _ _ _ _ fun s _ => ?_
  have hz : ∀ i, L ≤ i → slot c.SW (nxt.getD i 0) s = 0 := by
    intro i hi
    rw [List.getD_eq_default _ _ hi, slot_eq]
    simp
  rw [← sl_conv_reindex rmax y L (fun i => slot c.SW (nxt.getD i 0) s) (fun r => pnR.getD r 0) hz]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  rw [hbj j (Finset.mem_range.1 hj)]

theorem sl_window_real (W Rmax : ℕ) (pn : ℝ) (R : ℕ → ℝ) (next : ℕ → ℕ → ℝ) (pnR : ℕ → ℕ)
    (sl : ℕ → ℕ → ℕ) (y k : ℕ) (hnext0 : ∀ y k, 0 ≤ next y k)
    (hpnR : ∀ r ≤ Rmax, pn * R r * 2 ^ W ≤ pnR r)
    (hnext : ∀ r ≤ Rmax, 2 ^ W * next (y + r) k ≤ sl (y + r) k) :
    2 ^ W * (2 ^ W * (pn * ∑ r ∈ range (Rmax + 1), R r * next (y + r) k)) ≤
      ((∑ r ∈ range (Rmax + 1), pnR r * sl (y + r) k : ℕ) : ℝ) := by
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hr' : r ≤ Rmax := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have h3 : 0 ≤ 2 ^ W * next (y + r) k := mul_nonneg (by positivity) (hnext0 _ _)
  calc 2 ^ W * (2 ^ W * (pn * (R r * next (y + r) k))) =
        (pn * R r * 2 ^ W) * (2 ^ W * next (y + r) k) := by ring
    _ ≤ (pnR r : ℝ) * (sl (y + r) k : ℝ) := mul_le_mul (hpnR r hr') (hnext r hr') h3 (Nat.cast_nonneg _)

/-! ## The rows of a stage -/

/-- The mass of the `n` slots of a row. -/
def lmass (c : LawCfg) (x : ℕ) : ℕ := ∑ i ∈ range c.n, slot c.SW x i

theorem sl_slot_le_lmass (c : LawCfg) (x i : ℕ) (hi : i < c.n) : slot c.SW x i ≤ lmass c x := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)

theorem sl_lmass_pk (c : LawCfg) (f : ℕ → ℕ) (hf : ∀ i < c.n, f i < 2 ^ c.SW) :
    lmass c (pk c.SW f c.n) = ∑ i ∈ range c.n, f i := by
  unfold lmass
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [slot_pk _ _ _ _ hf]
  simp only [Finset.mem_range.1 hi, ↓reduceIte]

theorem sl_pow_SW (c : LawCfg) : 2 ^ c.SW = 256 * (2 ^ c.W * 2 ^ c.W) := by
  rw [sl_SW, show 2 * c.W + 8 = c.W + c.W + 8 by ring, pow_add, pow_add]
  norm_num
  ring

/-- One row step on abstract rows: the size, the mass and the slots of `rowStep`. -/
theorem row_step (c : LawCfg) (hn : 1 ≤ c.n) (cg cc P B0 γ M row tv : ℕ)
    (hrow : row < 2 ^ (c.SW * c.n)) (htv : tv < 2 ^ (c.SW * c.n))
    (hM : lmass c row ≤ M) (hM2 : M ≤ 2 * 2 ^ c.W) (hBM : B0 ≤ M) (htm : lmass c tv ≤ P * B0)
    (hcoef : cg + cc + P ≤ 2 ^ c.W + γ) (hγ : γ ≤ 2 ^ c.W) :
    rowStep c cg cc row tv < 2 ^ (c.SW * c.n) ∧
      lmass c (rowStep c cg cc row tv) ≤ M + (2 * γ + c.n) ∧
      ∀ i < c.n, slot c.SW (rowStep c cg cc row tv) i =
        (cg * slot c.SW row i + cc * kcs c.n (fun j => slot c.SW row j) i + slot c.SW tv i +
          (2 ^ c.W - 1)) / 2 ^ c.W := by
  have hX : 0 < 2 ^ c.W := by positivity
  have hrow' : pk c.SW (fun j => slot c.SW row j) c.n = row := sl_pk_slot _ _ _ hrow
  have htv' : pk c.SW (fun j => slot c.SW tv j) c.n = tv := sl_pk_slot _ _ _ htv
  have hgle : ∀ j < c.n, slot c.SW row j ≤ M := fun j hj => (sl_slot_le_lmass c _ j hj).trans hM
  have hkle : ∀ j < c.n, kcs c.n (fun j => slot c.SW row j) j ≤ M :=
    fun j hj => (sl_kcs_le c.n _ j hj).trans hM
  have htle : ∀ j < c.n, slot c.SW tv j ≤ P * M :=
    fun j hj => (sl_slot_le_lmass c _ j hj).trans (htm.trans (Nat.mul_le_mul_left _ hBM))
  have hov : ∀ i < c.n, cg * slot c.SW row i + cc * kcs c.n (fun j => slot c.SW row j) i +
      slot c.SW tv i + (2 ^ c.W - 1) < 2 ^ c.SW := by
    intro i hi
    have e1 : cg * slot c.SW row i ≤ cg * (2 * 2 ^ c.W) := Nat.mul_le_mul_left _ ((hgle i hi).trans hM2)
    have e2 : cc * kcs c.n (fun j => slot c.SW row j) i ≤ cc * (2 * 2 ^ c.W) :=
      Nat.mul_le_mul_left _ ((hkle i hi).trans hM2)
    have e3 : slot c.SW tv i ≤ P * (2 * 2 ^ c.W) := (htle i hi).trans (Nat.mul_le_mul_left _ hM2)
    have e4 : (cg + cc + P) * (2 * 2 ^ c.W) ≤ (2 * 2 ^ c.W) * (2 * 2 ^ c.W) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [sl_pow_SW]
    have e5 : 2 ^ c.W - 1 < 2 ^ c.W := by omega
    nlinarith
  have heq : rowStep c cg cc row tv = pk c.SW (fun i => (cg * slot c.SW row i +
      cc * kcs c.n (fun j => slot c.SW row j) i + slot c.SW tv i + (2 ^ c.W - 1)) / 2 ^ c.W) c.n := by
    calc rowStep c cg cc row tv = rowStep c cg cc (pk c.SW (fun j => slot c.SW row j) c.n)
          (pk c.SW (fun j => slot c.SW tv j) c.n) := by rw [hrow', htv']
      _ = _ := sl_rowStep_pk c hn cg cc _ _ (fun i _ => sl_slot_lt _ _ _) hov
  have hlt : ∀ i < c.n, (cg * slot c.SW row i + cc * kcs c.n (fun j => slot c.SW row j) i +
      slot c.SW tv i + (2 ^ c.W - 1)) / 2 ^ c.W < 2 ^ c.SW :=
    fun i hi => lt_of_le_of_lt (Nat.div_le_self _ _) (hov i hi)
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact pk_lt _ _ _ hlt
  · rw [heq, sl_lmass_pk c _ hlt]
    have hs := sl_ceil_sum c.W c.n (fun i => cg * slot c.SW row i +
      cc * kcs c.n (fun j => slot c.SW row j) i + slot c.SW tv i)
    have hsum : ∑ i ∈ range c.n, (cg * slot c.SW row i + cc * kcs c.n (fun j => slot c.SW row j) i +
        slot c.SW tv i) = cg * lmass c row + cc * lmass c row + lmass c tv := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sl_kcs_sum c.n _ hn]
      rfl
    rw [hsum] at hs
    have f1 : cg * lmass c row ≤ cg * M := Nat.mul_le_mul_left _ hM
    have f2 : cc * lmass c row ≤ cc * M := Nat.mul_le_mul_left _ hM
    have f3 : lmass c tv ≤ P * M := htm.trans (Nat.mul_le_mul_left _ hBM)
    have f4 : (cg + cc + P) * M ≤ (2 ^ c.W + γ) * M := Nat.mul_le_mul_right _ hcoef
    have f5 : γ * M ≤ γ * (2 * 2 ^ c.W) := Nat.mul_le_mul_left _ hM2
    refine Nat.le_of_mul_le_mul_left ?_ hX
    nlinarith
  · intro i hi
    rw [heq, slot_pk _ _ _ _ hlt]
    simp only [hi, ↓reduceIte]

/-- The natural invariant of the rows of a stage: each fits its slots, the masses grow by at most
`2 gamma + n` per row, and the slots of row `y + 1` are those of `rowStep`. -/
theorem rowSeq_inv (c : LawCfg) (hn : 1 ≤ c.n) (cg cc : ℕ) (ts : List ℕ) (Y B0 γ P : ℕ)
    (hB0 : 2 ^ c.W ≤ B0) (hBY : B0 + (2 * γ + c.n) * Y ≤ 2 ^ (c.W + 1)) (hγ : γ ≤ 2 ^ c.W)
    (hcoef : cg + cc + P ≤ 2 ^ c.W + γ)
    (hts : ∀ y < Y, ts.getD y 0 < 2 ^ (c.SW * c.n) ∧ lmass c (ts.getD y 0) ≤ P * B0) :
    ∀ y ≤ Y, rowSeq c cg cc ts y < 2 ^ (c.SW * c.n) ∧
      lmass c (rowSeq c cg cc ts y) ≤ B0 + (2 * γ + c.n) * y ∧
      (y < Y → ∀ i < c.n, slot c.SW (rowSeq c cg cc ts (y + 1)) i =
        (cg * slot c.SW (rowSeq c cg cc ts y) i +
          cc * kcs c.n (fun j => slot c.SW (rowSeq c cg cc ts y) j) i +
          slot c.SW (ts.getD y 0) i + (2 ^ c.W - 1)) / 2 ^ c.W) := by
  have h2X : 2 ^ (c.W + 1) = 2 * 2 ^ c.W := by rw [pow_succ, mul_comm]
  have hstep : ∀ y < Y, rowSeq c cg cc ts y < 2 ^ (c.SW * c.n) →
      lmass c (rowSeq c cg cc ts y) ≤ B0 + (2 * γ + c.n) * y →
      rowSeq c cg cc ts (y + 1) < 2 ^ (c.SW * c.n) ∧
        lmass c (rowSeq c cg cc ts (y + 1)) ≤ B0 + (2 * γ + c.n) * (y + 1) ∧
        ∀ i < c.n, slot c.SW (rowSeq c cg cc ts (y + 1)) i =
          (cg * slot c.SW (rowSeq c cg cc ts y) i +
            cc * kcs c.n (fun j => slot c.SW (rowSeq c cg cc ts y) j) i +
            slot c.SW (ts.getD y 0) i + (2 ^ c.W - 1)) / 2 ^ c.W := by
    intro y hy hlt hm
    have hyY : (2 * γ + c.n) * y ≤ (2 * γ + c.n) * Y := Nat.mul_le_mul_left _ hy.le
    obtain ⟨r1, r2, r3⟩ := row_step c hn cg cc P B0 γ (B0 + (2 * γ + c.n) * y) (rowSeq c cg cc ts y)
      (ts.getD y 0) hlt (hts y hy).1 hm (by omega) (Nat.le_add_right _ _) (hts y hy).2 hcoef hγ
    refine ⟨r1, ?_, r3⟩
    calc _ ≤ B0 + (2 * γ + c.n) * y + (2 * γ + c.n) := r2
      _ = _ := by ring
  have hAB : ∀ y ≤ Y, rowSeq c cg cc ts y < 2 ^ (c.SW * c.n) ∧
      lmass c (rowSeq c cg cc ts y) ≤ B0 + (2 * γ + c.n) * y := by
    intro y
    induction y with
    | zero =>
      intro _
      have hu : rowSeq c cg cc ts 0 = pk c.SW (fun i => if i = 0 then 2 ^ c.W else 0) c.n :=
        sl_unit_pk c hn
      have hlt : ∀ i < c.n, (if i = 0 then 2 ^ c.W else 0) < 2 ^ c.SW := by
        intro i _
        split_ifs
        · exact Nat.pow_lt_pow_right (by norm_num) (by rw [sl_SW]; omega)
        · positivity
      rw [hu]
      refine ⟨pk_lt _ _ _ hlt, ?_⟩
      rw [sl_lmass_pk c _ hlt, Finset.sum_ite_eq' (range c.n) 0]
      simp only [Finset.mem_range.2 hn, ↓reduceIte]
      omega
    | succ y ih =>
      intro hy
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨r1, r2, _⟩ := hstep y (by omega) h1 h2
      exact ⟨r1, r2⟩
  intro y hy
  obtain ⟨h1, h2⟩ := hAB y hy
  exact ⟨h1, h2, fun hyY => (hstep y hyY h1 h2).2.2⟩

/-- The real bound of the rows of a stage, from the slots of `rowStep`. -/
theorem rowSeq_real (c : LawCfg) (hn : 1 ≤ c.n) (cap : ℕ) (hcap : cap + 1 = c.n) (cg cc : ℕ)
    (ts : List ℕ) (Y : ℕ) (pc pg pn : ℝ) (R : ℕ → ℝ) (Rmax : ℕ) (next : ℕ → ℕ → ℝ)
    (hpc : 0 ≤ pc) (hpg : 0 ≤ pg) (hpn : 0 ≤ pn) (hR : ∀ r, 0 ≤ R r) (hnext0 : ∀ y k, 0 ≤ next y k)
    (hcg : pg * 2 ^ c.W ≤ cg) (hcc : pc * 2 ^ c.W ≤ cc)
    (hstep : ∀ y < Y, ∀ i < c.n, slot c.SW (rowSeq c cg cc ts (y + 1)) i =
        (cg * slot c.SW (rowSeq c cg cc ts y) i +
          cc * kcs c.n (fun j => slot c.SW (rowSeq c cg cc ts y) j) i +
          slot c.SW (ts.getD y 0) i + (2 ^ c.W - 1)) / 2 ^ c.W)
    (hts : ∀ y < Y, ∀ k < c.n, 2 ^ c.W * (2 ^ c.W * (pn * ∑ r ∈ range (Rmax + 1), R r * next (y + r) k)) ≤
      (slot c.SW (ts.getD y 0) k : ℝ)) :
    ∀ y ≤ Y, ∀ k < c.n, 2 ^ c.W * stageLaw cap pc pg pn R Rmax next y k ≤
      (slot c.SW (rowSeq c cg cc ts y) k : ℝ) := by
  have hX : (0 : ℝ) < 2 ^ c.W := by positivity
  have hL0 : ∀ y k, 0 ≤ stageLaw cap pc pg pn R Rmax next y k :=
    FrogModel.D3.LaneC.stageLaw_nonneg cap pc pg pn R Rmax next hpc hpg hpn hR hnext0
  intro y
  induction y with
  | zero =>
    intro _ k hk
    have hu : slot c.SW (rowSeq c cg cc ts 0) k = if k = 0 then 2 ^ c.W else 0 := by
      rw [show rowSeq c cg cc ts 0 = K.unit c from rfl, sl_unit_pk c hn, slot_pk _ _ _ _ (by
        intro j _
        split_ifs
        · exact Nat.pow_lt_pow_right (by norm_num) (by rw [sl_SW]; omega)
        · positivity)]
      simp only [hk, ↓reduceIte]
    rw [hu]
    simp only [stageLaw]
    split_ifs <;> simp
  | succ y ih =>
    intro hy k hk
    rw [hstep y (by omega) k hk]
    have ih' : ∀ j < c.n, 2 ^ c.W * stageLaw cap pc pg pn R Rmax next y j ≤
        (slot c.SW (rowSeq c cg cc ts y) j : ℝ) := ih (by omega)
    refine le_trans ?_ (sl_ceil_real c.W _)
    rw [le_div_iff₀ hX]
    have hcs : 2 ^ c.W * Iface.capShift cap (stageLaw cap pc pg pn R Rmax next y) k ≤
        (kcs c.n (fun j => slot c.SW (rowSeq c cg cc ts y) j) k : ℝ) := by
      have := sl_kcs_real c.W c.n (fun j => slot c.SW (rowSeq c cg cc ts y) j) _ ih' k hk
      rwa [show c.n - 1 = cap by omega] at this
    have hcs0 : 0 ≤ 2 ^ c.W * Iface.capShift cap (stageLaw cap pc pg pn R Rmax next y) k :=
      mul_nonneg hX.le (FrogModel.D3.LaneC.capShift_nonneg cap _ (hL0 y) k)
    have t1 : pc * 2 ^ c.W * (2 ^ c.W * Iface.capShift cap (stageLaw cap pc pg pn R Rmax next y) k) ≤
        (cc : ℝ) * (kcs c.n (fun j => slot c.SW (rowSeq c cg cc ts y) j) k : ℝ) :=
      mul_le_mul hcc hcs hcs0 (Nat.cast_nonneg _)
    have t2 : pg * 2 ^ c.W * (2 ^ c.W * stageLaw cap pc pg pn R Rmax next y k) ≤
        (cg : ℝ) * (slot c.SW (rowSeq c cg cc ts y) k : ℝ) :=
      mul_le_mul hcg (ih' k hk) (mul_nonneg hX.le (hL0 y k)) (Nat.cast_nonneg _)
    have t3 := hts y (by omega) k hk
    simp only [stageLaw]
    push_cast
    nlinarith

theorem lmass_zero (c : LawCfg) : lmass c 0 = 0 := by
  simp [lmass, slot_eq]

/-- What is known of the rows of a stage: their number, size and masses, and the real bound. -/
structure StageOK (c : LawCfg) (rows : List ℕ) (Y B : ℕ) (L : ℕ → ℕ → ℝ) : Prop where
  len : rows.length = Y + 1
  lt : ∀ y, rows.getD y 0 < 2 ^ (c.SW * c.n)
  mass : ∀ y, lmass c (rows.getD y 0) ≤ B
  real : ∀ y ≤ Y, ∀ k < c.n, 2 ^ c.W * L y k ≤ (slot c.SW (rows.getD y 0) k : ℝ)
  nonneg : ∀ y k, 0 ≤ L y k

theorem stageRows_lt (c : LawCfg) (hn : 1 ≤ c.n) (Y cg cc : ℕ) (ts : List ℕ) (y : ℕ) :
    (stageRows c Y cg cc ts).getD y 0 < 2 ^ (c.SW * c.n) := by
  by_cases hy : y ≤ Y
  · rw [sl_stageRows_getD c Y cg cc ts y hy]
    cases y with
    | zero =>
      rw [show rowSeq c cg cc ts 0 = K.unit c from rfl, sl_unit_pk c hn]
      apply pk_lt
      intro i _
      split_ifs
      · exact Nat.pow_lt_pow_right (by norm_num) (by rw [sl_SW]; omega)
      · positivity
    | succ y => exact sl_ceilK_lt c _
  · rw [List.getD_eq_default _ _ (by rw [sl_stageRows_length]; omega)]
    positivity

/-- The masses of the rows of a stage, from `rowSeq_inv`. -/
theorem stageRows_mass (c : LawCfg) (Y cg cc : ℕ) (ts : List ℕ) (B : ℕ)
    (h : ∀ y ≤ Y, lmass c (rowSeq c cg cc ts y) ≤ B) (y : ℕ) :
    lmass c ((stageRows c Y cg cc ts).getD y 0) ≤ B := by
  by_cases hy : y ≤ Y
  · rw [sl_stageRows_getD c Y cg cc ts y hy]
    exact h y hy
  · rw [List.getD_eq_default _ _ (by rw [sl_stageRows_length]; omega), lmass_zero]
    exact Nat.zero_le _

/-- The innermost stage (no new children). -/
theorem stage_last (c : LawCfg) (hn : 1 ≤ c.n) (cap : ℕ) (hcap : cap + 1 = c.n) (Y cg cc γ : ℕ)
    (pc pg : ℝ) (R : ℕ → ℝ) (Rmax : ℕ) (hpc : 0 ≤ pc) (hpg : 0 ≤ pg) (hR : ∀ r, 0 ≤ R r)
    (hcg : pg * 2 ^ c.W ≤ cg) (hcc : pc * 2 ^ c.W ≤ cc) (hcoef : cg + cc ≤ 2 ^ c.W + γ)
    (hγ : γ ≤ 2 ^ c.W) (hBY : 2 ^ c.W + (2 * γ + c.n) * Y ≤ 2 ^ (c.W + 1)) :
    StageOK c (stageRows c Y cg cc []) Y (2 ^ c.W + (2 * γ + c.n) * Y)
      (stageLaw cap pc pg 0 R Rmax fun _ _ => 0) := by
  have hinv := rowSeq_inv c hn cg cc [] Y (2 ^ c.W) γ 0 le_rfl hBY hγ (by simpa using hcoef)
    (fun y _ => by simp [lmass_zero])
  refine ⟨sl_stageRows_length c Y cg cc [], stageRows_lt c hn Y cg cc [], ?_, ?_, ?_⟩
  · refine stageRows_mass c Y cg cc [] _ (fun y hy => (hinv y hy).2.1.trans ?_)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hy) _
  · intro y hy k hk
    rw [sl_stageRows_getD c Y cg cc [] y hy]
    refine rowSeq_real c hn cap hcap cg cc [] Y pc pg 0 R Rmax (fun _ _ => 0) hpc hpg le_rfl hR
      (fun _ _ => le_rfl) hcg hcc (fun y hy => (hinv y hy.le).2.2 hy) ?_ y hy k hk
    intro y _ k _
    simp
  · exact FrogModel.D3.LaneC.stageLaw_nonneg cap pc pg 0 R Rmax _ hpc hpg le_rfl hR (fun _ _ => le_rfl)

/-- A stage from the next one. -/
theorem stage_step (c : LawCfg) (hn : 1 ≤ c.n) (cap : ℕ) (hcap : cap + 1 = c.n) (Y cg cc γ : ℕ)
    (pnR nxt : List ℕ) (Yn Bn : ℕ) (next : ℕ → ℕ → ℝ) (pc pg pn : ℝ) (R : ℕ → ℝ) (Rmax : ℕ)
    (hnx : StageOK c nxt Yn Bn next) (hYn : Y + Rmax ≤ Yn + 1)
    (hpc : 0 ≤ pc) (hpg : 0 ≤ pg) (hpn : 0 ≤ pn) (hR : ∀ r, 0 ≤ R r)
    (hcg : pg * 2 ^ c.W ≤ cg) (hcc : pc * 2 ^ c.W ≤ cc)
    (hlen : pnR.length = Rmax + 1) (hpnR : ∀ r ≤ Rmax, pn * R r * 2 ^ c.W ≤ pnR.getD r 0)
    (hcoef : cg + cc + ∑ r ∈ range (Rmax + 1), pnR.getD r 0 ≤ 2 ^ c.W + γ) (hγ : γ ≤ 2 ^ c.W)
    (hB0 : 2 ^ c.W ≤ Bn) (hBY : Bn + (2 * γ + c.n) * Y ≤ 2 ^ (c.W + 1)) :
    StageOK c (stageRows c Y cg cc (windows c pnR nxt)) Y (Bn + (2 * γ + c.n) * Y)
      (stageLaw cap pc pg pn R Rmax next) := by
  set P := ∑ r ∈ range (Rmax + 1), pnR.getD r 0 with hP
  have hBn2 : Bn ≤ 2 ^ (c.W + 1) := le_trans (Nat.le_add_right _ _) hBY
  have hP2 : P ≤ 2 ^ (c.W + 1) := by rw [pow_succ]; omega
  have hov : (∑ r ∈ range pnR.length, pnR.getD r 0) * Bn < 2 ^ c.SW := by
    rw [hlen]
    calc P * Bn ≤ 2 ^ (c.W + 1) * 2 ^ (c.W + 1) := Nat.mul_le_mul hP2 hBn2
      _ < 2 ^ c.SW := by
        rw [sl_SW, ← pow_add]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpn_ne : pnR ≠ [] := by
    intro h
    simp [h] at hlen
  have hsl : ∀ i, ∀ s < c.n, slot c.SW (nxt.getD i 0) s ≤ Bn :=
    fun i s hs => (sl_slot_le_lmass c _ s hs).trans (hnx.mass i)
  have hwin := sl_windows_getD c pnR nxt Bn hpn_ne hnx.lt hsl hov
  have hslots : ∀ y, ∀ s < c.n,
      ∑ r ∈ range pnR.length, pnR.getD r 0 * slot c.SW (nxt.getD (y + r) 0) s < 2 ^ c.SW := by
    intro y s hs
    calc _ ≤ (∑ r ∈ range pnR.length, pnR.getD r 0) * Bn := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun r _ => Nat.mul_le_mul_left _ (hsl _ s hs)
      _ < _ := hov
  have hts : ∀ y < Y, (windows c pnR nxt).getD y 0 < 2 ^ (c.SW * c.n) ∧
      lmass c ((windows c pnR nxt).getD y 0) ≤ P * Bn := by
    intro y _
    rw [hwin y]
    refine ⟨pk_lt _ _ _ (hslots y), ?_⟩
    rw [sl_lmass_pk c _ (hslots y), Finset.sum_comm, hlen, hP, Finset.sum_mul]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ (hnx.mass _)
  have hinv := rowSeq_inv c hn cg cc (windows c pnR nxt) Y Bn γ P hB0 hBY hγ hcoef hts
  refine ⟨sl_stageRows_length c Y cg cc _, stageRows_lt c hn Y cg cc _, ?_, ?_, ?_⟩
  · refine stageRows_mass c Y cg cc _ _ (fun y hy => (hinv y hy).2.1.trans ?_)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hy) _
  · intro y hy k hk
    rw [sl_stageRows_getD c Y cg cc _ y hy]
    refine rowSeq_real c hn cap hcap cg cc _ Y pc pg pn R Rmax next hpc hpg hpn hR hnx.nonneg hcg hcc
      (fun y hy => (hinv y hy.le).2.2 hy) ?_ y hy k hk
    intro y hy k hk
    rw [hwin y, slot_pk _ _ _ _ (hslots y), hlen]
    simp only [hk, ↓reduceIte]
    exact sl_window_real c.W Rmax pn R next (fun r => pnR.getD r 0) (fun i s => slot c.SW (nxt.getD i 0) s)
      y k hnx.nonneg hpnR (fun r hr => hnx.real (y + r) (by omega) k hk)
  · exact FrogModel.D3.LaneC.stageLaw_nonneg cap pc pg pn R Rmax next hpc hpg hpn hR hnx.nonneg

/-! ## The coefficients -/

theorem cst_ge (c : LawCfg) (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b * 2 ^ c.W ≤ (cst c a b : ℝ) := by
  have h := sl_cdiv_ge (a * 2 ^ c.W) b hb
  rw [← sl_cst_eq] at h
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_mul_eq_mul_div, div_le_iff₀ hb']
  calc (a : ℝ) * 2 ^ c.W = ((a * 2 ^ c.W : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((b * cst c a b : ℕ) : ℝ) := by exact_mod_cast h
    _ = _ := by push_cast; ring

theorem cst_le (c : LawCfg) (a b : ℕ) (hb : 0 < b) : b * cst c a b ≤ a * 2 ^ c.W + (b - 1) := by
  rw [sl_cst_eq]
  exact sl_cdiv_le _ _ hb

theorem scaleUp_ge (W GM row a b : ℕ) (hb : 0 < b) (F1 : ℕ → ℝ) (hW : 52 ≤ W)
    (hF1 : ∀ g ≤ GM, F1 g = (slot 64 row g : ℝ) / 2 ^ 52)
    (hmono : ∀ g < GM, slot 64 row g ≤ slot 64 row (g + 1)) (htop : slot 64 row GM ≤ 2 ^ 52) (r : ℕ) :
    (a : ℝ) / b * plR F1 GM r * 2 ^ W ≤ ((scaleUp a b (pseudoLaw W GM row)).getD r 0 : ℝ) := by
  rw [sl_scaleUp_getD]
  have h := sl_cdiv_ge ((pseudoLaw W GM row).getD r 0 * a) b hb
  have hreal := sl_pseudoLaw_real W GM row F1 hW hF1 hmono htop r
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hcast : (((pseudoLaw W GM row).getD r 0 * a : ℕ) : ℝ) ≤ (b : ℝ) * (cdiv ((pseudoLaw W GM row).getD r 0 * a) b : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_mul, hreal] at hcast
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hb']
  linarith

theorem scaleUp_sum_le (W GM row a b : ℕ) (hb : 0 < b) (hW : 52 ≤ W)
    (hmono : ∀ g < GM, slot 64 row g ≤ slot 64 row (g + 1)) (htop : slot 64 row GM ≤ 2 ^ 52) :
    b * ∑ r ∈ range (GM + 1 + 1), (scaleUp a b (pseudoLaw W GM row)).getD r 0 ≤
      a * 2 ^ W + (b - 1) * (GM + 2) := by
  rw [show GM + 1 + 1 = GM + 2 from rfl]
  simp only [sl_scaleUp_getD]
  rw [Finset.mul_sum]
  calc ∑ r ∈ range (GM + 2), b * cdiv ((pseudoLaw W GM row).getD r 0 * a) b
      ≤ ∑ r ∈ range (GM + 2), ((pseudoLaw W GM row).getD r 0 * a + (b - 1)) :=
        Finset.sum_le_sum fun r _ => sl_cdiv_le _ _ hb
    _ = a * 2 ^ W + (b - 1) * (GM + 2) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sl_pseudoLaw_sum W GM row hW hmono htop]
        simp [mul_comm]

theorem scaleUp_length (W GM row a b : ℕ) : (scaleUp a b (pseudoLaw W GM row)).length = GM + 1 + 1 := by
  rw [sl_scaleUp_length, sl_pseudoLaw_length]

/-! ## The S2 and S3 laws -/

/-- The pseudo-law of a stored row (at `2^-52`, nondecreasing, at most `1`) is nonnegative. -/
theorem plR_nonneg_of (GM f1 : ℕ) (F1 : ℕ → ℝ) (hF1 : ∀ g ≤ GM, F1 g = (slot 64 f1 g : ℝ) / 2 ^ 52)
    (hmono : ∀ g < GM, slot 64 f1 g ≤ slot 64 f1 (g + 1)) (htop : slot 64 f1 GM ≤ 2 ^ 52) (r : ℕ) :
    0 ≤ plR F1 GM r := by
  have key : ∀ d g, g + d ≤ GM → slot 64 f1 g ≤ slot 64 f1 (g + d) := by
    intro d
    induction d with
    | zero => intro g _; simp
    | succ d ih => intro g hg; exact (ih g (by omega)).trans (hmono (g + d) (by omega))
  have h01 : ∀ g ≤ GM, 0 ≤ F1 g ∧ F1 g ≤ 1 := by
    intro g hg
    rw [hF1 g hg]
    have hle : slot 64 f1 g ≤ 2 ^ 52 := by
      have := key (GM - g) g (by omega)
      rw [Nat.add_sub_cancel' hg] at this
      exact this.trans htop
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      exact_mod_cast hle
  exact FrogModel.D3.LaneC.plR_nonneg F1 GM
    (fun g hg => by rw [hF1 g hg.le, hF1 (g + 1) (by omega)]; gcongr; exact_mod_cast hmono g hg) h01 r

/-- The three stages of `s2Laws`. -/
theorem s2_stages (W E GM f1 : ℕ) (F1 : ℕ → ℝ) (hW : 52 ≤ W)
    (hF1 : ∀ g ≤ GM, F1 g = (slot 64 f1 g : ℝ) / 2 ^ 52)
    (hmono : ∀ g < GM, slot 64 f1 g ≤ slot 64 f1 (g + 1)) (htop : slot 64 f1 GM ≤ 2 ^ 52)
    (hsmall : (2 * GM + E + 9) * (3 * E + 3 * GM + 6) ≤ 2 ^ W) :
    ∃ B, StageOK ⟨W, E + 1⟩ (s2Laws W E GM f1) (E + 1) B (lawS2 GM E F1) := by
  set c : LawCfg := ⟨W, E + 1⟩ with hc
  have hn : 1 ≤ c.n := by simp [hc]
  have hcW : c.W = W := rfl
  have hcn : c.n = E + 1 := rfl
  set X := 2 ^ W with hX
  have hX1 : 2 ^ (c.W + 1) = 2 * X := by rw [hcW, pow_succ, hX, mul_comm]
  have hR : ∀ r, 0 ≤ plR F1 GM r := plR_nonneg_of GM f1 F1 hF1 hmono htop
  -- the sizes
  set δ := 2 * (GM + 4) + c.n with hδ
  have hδ' : δ = 2 * GM + E + 9 := by rw [hδ, hcn]; ring
  have hY : δ * (E + 1 + 2 * (GM + 1)) + δ * (E + 1 + (GM + 1)) + δ * (E + 1) ≤ X := by
    rw [hδ']
    calc _ = (2 * GM + E + 9) * (3 * E + 3 * GM + 6) := by ring
      _ ≤ X := hsmall
  have hγX : GM + 4 ≤ 2 ^ c.W := by
    rw [hcW]
    calc GM + 4 ≤ (2 * GM + E + 9) * (3 * E + 3 * GM + 6) := by nlinarith
      _ ≤ _ := hsmall
  -- stage 2
  have h2 := stage_last c hn E (by rw [hcn]) (E + 1 + 2 * (GM + 1)) (cst c 7 10) (cst c 3 10) (GM + 4)
    (3 / 10) (7 / 10) (plR F1 GM) (GM + 1) (by norm_num) (by norm_num) hR
    (by have := cst_ge c 7 10 (by norm_num); norm_num at this ⊢; exact this)
    (by have := cst_ge c 3 10 (by norm_num); norm_num at this ⊢; exact this)
    (by have h1 := cst_le c 7 10 (by norm_num); have h2 := cst_le c 3 10 (by norm_num); omega)
    hγX (by rw [hX1, ← hδ]; omega)
  -- stage 1
  have h1 := stage_step c hn E (by rw [hcn]) (E + 1 + (GM + 1)) (cst c 5 11) (cst c 3 11) (GM + 4)
    (scaleUp 3 11 (pseudoLaw W GM f1)) _ _ _ _ (3 / 11) (5 / 11) (3 / 11) (plR F1 GM) (GM + 1) h2 (by omega)
    (by norm_num) (by norm_num) (by norm_num) hR
    (by have := cst_ge c 5 11 (by norm_num); norm_num at this ⊢; exact this)
    (by have := cst_ge c 3 11 (by norm_num); norm_num at this ⊢; exact this)
    (scaleUp_length W GM f1 3 11)
    (fun r _ => by
      have := scaleUp_ge W GM f1 3 11 (by norm_num) F1 hW hF1 hmono htop r
      norm_num at this ⊢; exact this)
    (by
      have h1 := cst_le c 5 11 (by norm_num); have h2 := cst_le c 3 11 (by norm_num)
      have h3 := scaleUp_sum_le W GM f1 3 11 (by norm_num) hW hmono htop
      rw [hcW] at h1 h2
      omega)
    hγX (by omega) (by rw [hX1, ← hδ]; omega)
  -- stage 0
  have h0 := stage_step c hn E (by rw [hcn]) (E + 1) (cst c 1 4) (cst c 1 4) (GM + 4)
    (scaleUp 1 2 (pseudoLaw W GM f1)) _ _ _ _ (1 / 4) (1 / 4) (1 / 2) (plR F1 GM) (GM + 1) h1 (by omega)
    (by norm_num) (by norm_num) (by norm_num) hR
    (by have := cst_ge c 1 4 (by norm_num); norm_num at this ⊢; exact this)
    (by have := cst_ge c 1 4 (by norm_num); norm_num at this ⊢; exact this)
    (scaleUp_length W GM f1 1 2)
    (fun r _ => by
      have := scaleUp_ge W GM f1 1 2 (by norm_num) F1 hW hF1 hmono htop r
      norm_num at this ⊢; exact this)
    (by
      have h1 := cst_le c 1 4 (by norm_num)
      have h3 := scaleUp_sum_le W GM f1 1 2 (by norm_num) hW hmono htop
      rw [hcW] at h1
      omega)
    hγX (by omega) (by rw [hX1, ← hδ]; omega)
  exact ⟨_, h0⟩

/-- The four stages of `s3Laws`. -/
theorem s3_stages (W E GM f1 : ℕ) (F1 : ℕ → ℝ) (hW : 52 ≤ W)
    (hF1 : ∀ g ≤ GM, F1 g = (slot 64 f1 g : ℝ) / 2 ^ 52)
    (hmono : ∀ g < GM, slot 64 f1 g ≤ slot 64 f1 (g + 1)) (htop : slot 64 f1 GM ≤ 2 ^ 52)
    (hsmall : (3 * GM + 10) * (4 * E + 6 * GM + 10) ≤ 2 ^ W) :
    ∃ B, StageOK ⟨W, GM + 2⟩ (s3Laws W E GM f1) (E + 1) B (lawS3 GM F1) := by
  set c : LawCfg := ⟨W, GM + 2⟩ with hc
  have hn : 1 ≤ c.n := by simp [hc]
  have hcW : c.W = W := rfl
  have hcn : c.n = GM + 2 := rfl
  set X := 2 ^ W with hX
  have hX1 : 2 ^ (c.W + 1) = 2 * X := by rw [hcW, pow_succ, hX, mul_comm]
  have hR : ∀ r, 0 ≤ plR F1 GM r := plR_nonneg_of GM f1 F1 hF1 hmono htop
  set δ := 2 * (GM + 4) + c.n with hδ
  have hδ' : δ = 3 * GM + 10 := by rw [hδ, hcn]; ring
  have hY : δ * (E + 1 + 3 * (GM + 1)) + δ * (E + 1 + 2 * (GM + 1)) + δ * (E + 1 + (GM + 1)) +
      δ * (E + 1) ≤ X := by
    rw [hδ']
    calc _ = (3 * GM + 10) * (4 * E + 6 * GM + 10) := by ring
      _ ≤ X := hsmall
  have hγX : GM + 4 ≤ 2 ^ c.W := by
    rw [hcW]
    calc GM + 4 ≤ (3 * GM + 10) * (4 * E + 6 * GM + 10) := by nlinarith
      _ ≤ _ := hsmall
  -- stage 3
  have h3 := stage_last c hn (GM + 1) (by rw [hcn]) (E + 1 + 3 * (GM + 1)) (cst c 2 3) (cst c 1 3)
    (GM + 4) (1 / 3) (2 / 3) (plR F1 GM) (GM + 1) (by norm_num) (by norm_num) hR
    (by have := cst_ge c 2 3 (by norm_num); norm_num at this ⊢; exact this)
    (by have := cst_ge c 1 3 (by norm_num); norm_num at this ⊢; exact this)
    (by have h1 := cst_le c 2 3 (by norm_num); have h2 := cst_le c 1 3 (by norm_num); omega)
    hγX (by rw [hX1, ← hδ]; omega)
  -- stage 2
  have h2 := stage_step c hn (GM + 1) (by rw [hcn]) (E + 1 + 2 * (GM + 1)) (cst c 4 10) (cst c 3 10)
    (GM + 4) (scaleUp 3 10 (pseudoLaw W GM f1)) _ _ _ _ (3 / 10) (4 / 10) (3 / 10) (plR F1 GM) (GM + 1)
    h3 (by omega) (by norm_num) (by norm_num) (by norm_num) hR
    (by have := cst_ge c 4 10 (by norm_num); norm_num at this ⊢; exact this)
    (by have := cst_ge c 3 10 (by norm_num); norm_num at this ⊢; exact this)
    (scaleUp_length W GM f1 3 10)
    (fun r _ => by
      have := scaleUp_ge W GM f1 3 10 (by norm_num) F1 hW hF1 hmono htop r
      norm_num at this ⊢; exact this)
    (by
      have h1 := cst_le c 4 10 (by norm_num); have h2 := cst_le c 3 10 (by norm_num)
      have h3 := scaleUp_sum_le W GM f1 3 10 (by norm_num) hW hmono htop
      rw [hcW] at h1 h2
      omega)
    hγX (by omega) (by rw [hX1, ← hδ]; omega)
  -- stage 1
  have h1 := stage_step c hn (GM + 1) (by rw [hcn]) (E + 1 + (GM + 1)) (cst c 2 11) (cst c 3 11)
    (GM + 4) (scaleUp 6 11 (pseudoLaw W GM f1)) _ _ _ _ (3 / 11) (2 / 11) (6 / 11) (plR F1 GM) (GM + 1)
    h2 (by omega) (by norm_num) (by norm_num) (by norm_num) hR
    (by have := cst_ge c 2 11 (by norm_num); norm_num at this ⊢; exact this)
    (by have := cst_ge c 3 11 (by norm_num); norm_num at this ⊢; exact this)
    (scaleUp_length W GM f1 6 11)
    (fun r _ => by
      have := scaleUp_ge W GM f1 6 11 (by norm_num) F1 hW hF1 hmono htop r
      norm_num at this ⊢; exact this)
    (by
      have h1 := cst_le c 2 11 (by norm_num); have h2 := cst_le c 3 11 (by norm_num)
      have h3 := scaleUp_sum_le W GM f1 6 11 (by norm_num) hW hmono htop
      rw [hcW] at h1 h2
      omega)
    hγX (by omega) (by rw [hX1, ← hδ]; omega)
  -- stage 0
  have h0 := stage_step c hn (GM + 1) (by rw [hcn]) (E + 1) 0 (cst c 1 4)
    (GM + 4) (scaleUp 3 4 (pseudoLaw W GM f1)) _ _ _ _ (1 / 4) 0 (3 / 4) (plR F1 GM) (GM + 1)
    h1 (by omega) (by norm_num) le_rfl (by norm_num) hR (by simp)
    (by have := cst_ge c 1 4 (by norm_num); norm_num at this ⊢; exact this)
    (scaleUp_length W GM f1 3 4)
    (fun r _ => by
      have := scaleUp_ge W GM f1 3 4 (by norm_num) F1 hW hF1 hmono htop r
      norm_num at this ⊢; exact this)
    (by
      have h1 := cst_le c 1 4 (by norm_num)
      have h3 := scaleUp_sum_le W GM f1 3 4 (by norm_num) hW hmono htop
      rw [hcW] at h1
      omega)
    hγX (by omega) (by rw [hX1, ← hδ]; omega)
  exact ⟨_, h0⟩

theorem s2Laws_sound (E GM f1 : ℕ) (F1 : ℕ → ℝ)
    (hF1 : ∀ g ≤ GM, F1 g = (slot 64 f1 g : ℝ) / 2 ^ 52)
    (hmono : ∀ g < GM, slot 64 f1 g ≤ slot 64 f1 (g + 1)) (htop : slot 64 f1 GM ≤ 2 ^ 52)
    (hE : E ≤ 64) (hGM : GM ≤ 256) (q k : ℕ) (hq : q ≤ E + 1) (hk : k ≤ E) :
    lawS2 GM E F1 q k ≤ (slot (2 * WL + 8) (getN (s2Laws WL E GM f1) q) k : ℝ) / 2 ^ WL := by
  obtain ⟨B, h⟩ := s2_stages WL E GM f1 F1 (by norm_num [WL]) hF1 hmono htop
    (calc (2 * GM + E + 9) * (3 * E + 3 * GM + 6) ≤ 585 * 966 := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 2 ^ WL := by norm_num [WL])
  rw [getN_eq, le_div_iff₀ (by positivity), mul_comm]
  exact h.real q hq k (by show k < E + 1; omega)

theorem s2Laws_lt (E GM f1 : ℕ) (_hmono : ∀ g < GM, slot 64 f1 g ≤ slot 64 f1 (g + 1))
    (_htop : slot 64 f1 GM ≤ 2 ^ 52) (q : ℕ) (_hq : q ≤ E + 1) :
    getN (s2Laws WL E GM f1) q < 2 ^ ((2 * WL + 8) * (E + 1)) := by
  rw [getN_eq]
  exact stageRows_lt ⟨WL, E + 1⟩ (by show 1 ≤ E + 1; omega) _ _ _ _ q

theorem s3Laws_sound (E GM f1 : ℕ) (F1 : ℕ → ℝ)
    (hF1 : ∀ g ≤ GM, F1 g = (slot 64 f1 g : ℝ) / 2 ^ 52)
    (hmono : ∀ g < GM, slot 64 f1 g ≤ slot 64 f1 (g + 1)) (htop : slot 64 f1 GM ≤ 2 ^ 52)
    (hE : E ≤ 64) (hGM : GM ≤ 256) (q v : ℕ) (hq : q ≤ E + 1) (hv : v ≤ GM) :
    cdfS3 GM F1 q v ≤
      (∑ x ∈ Finset.range (v + 1), slot (2 * WL + 8) (getN (s3Laws WL E GM f1) q) x : ℝ) / 2 ^ WL := by
  obtain ⟨B, h⟩ := s3_stages WL E GM f1 F1 (by norm_num [WL]) hF1 hmono htop
    (calc (3 * GM + 10) * (4 * E + 6 * GM + 10) ≤ 778 * 1802 := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 2 ^ WL := by norm_num [WL])
  rw [getN_eq, cdfS3, Finset.sum_div]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact h.real q hq x (by show x < GM + 2; have := Finset.mem_range.1 hx; omega)

theorem s3Laws_lt (E GM f1 : ℕ) (_hmono : ∀ g < GM, slot 64 f1 g ≤ slot 64 f1 (g + 1))
    (_htop : slot 64 f1 GM ≤ 2 ^ 52) (q : ℕ) (_hq : q ≤ E + 1) :
    getN (s3Laws WL E GM f1) q < 2 ^ ((2 * WL + 8) * (GM + 2)) := by
  rw [getN_eq]
  exact stageRows_lt ⟨WL, GM + 2⟩ (by show 1 ≤ GM + 2; omega) _ _ _ _ q

end FrogModel.D3.LaneD
