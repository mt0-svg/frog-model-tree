module

public import FrogModel.D3.M1K.Pack

@[expose] public section

/-!
# Rows and tables of the checker lane by lane

A row `pack S NL f` (lanes `f l < 2^S`, `S = 144`, `NL = 196`): its lanes, the lane-wise floor,
`up`, the rounding step, the bound test; tables `pack RB n g` (rows `g p < 2^RB`) and their rows;
the small helpers of `Check.lean` (`getR`, `findTab`, `mcode`, `sumLanes`, `zeroAbove`).
-/

open FrogModel.Lanes

namespace FrogModel.D3.M1K

/-- `up` lane by lane: lane `(a, g)` from lane `(a - 1, g)`, plus lane `(V, g)` itself at `a = V`. -/
def upL (f : ℕ → ℕ) (l : ℕ) : ℕ := (if 4 ≤ l then f (l - 4) else 0) + (if 4 * V ≤ l then f l else 0)

/-! ## The raw operations of `Check.lean` in the usual notation -/

theorem raw_mod (a b : ℕ) : Nat.mod a b = a % b := rfl
theorem raw_shiftRight (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
theorem raw_shiftLeft (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

/-! ## Generic lemmas over the lane width -/

/-- Lane `l` of a pack, in the raw form of `lane` and `blockAt`. -/
theorem lane_gen (W n : ℕ) (f : ℕ → ℕ) (hf : ∀ l < n, f l < 2 ^ W) (l : ℕ) :
    Nat.mod (Nat.shiftRight (pack W n f) (Nat.mul W l)) (Nat.pow 2 W) =
      if l < n then f l else 0 := by
  rw [raw_mod, raw_shiftRight, Nat.mul_eq, Nat.pow_eq, Nat.shiftRight_eq_div_pow]
  split_ifs with hl
  · exact pack_div_mod W n f hf l hl
  · rw [pack_div_pow W n l f hf, Nat.sub_eq_zero_of_le (not_lt.mp hl)]; simp [pack]

/-- `lfloor` on a pack of lanes of `S` bits, in its raw form. -/
theorem lfloor_gen (S L W : ℕ) (hS : 1 ≤ S) (hWS : W ≤ S) (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ S) :
    Nat.shiftRight (Nat.sub (pack S L f) (Nat.land (pack S L f)
        (pack S L (fun _ => Nat.sub (Nat.pow 2 W) 1)))) W = pack S L (fun l => f l / 2 ^ W) := by
  rw [raw_shiftRight, Nat.sub_eq, Nat.land_eq]
  simp only [Nat.pow_eq, Nat.sub_eq]
  have hb : ∀ l < L, (fun _ => 2 ^ W - 1) l < 2 ^ S := fun l _ => by
    have h1 : 2 ^ W ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) hWS
    have h2 : 0 < 2 ^ W := by positivity
    simp only; omega
  rw [land_pack S L hS f _ hf hb]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  rw [pack_sub S L _ _ (fun l _ => Nat.mod_le _ _)]
  have h : ∀ l, f l - f l % 2 ^ W = 2 ^ W * (f l / 2 ^ W) := fun l => by
    have := Nat.div_add_mod (f l) (2 ^ W); omega
  simp only [h]
  rw [← pack_const_mul, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (by positivity)]

/-- A pack with every lane zero. -/
theorem pack_eq_zero_iff (W L : ℕ) (f : ℕ → ℕ) : pack W L f = 0 ↔ ∀ l < L, f l = 0 := by
  unfold pack
  rw [Finset.sum_eq_zero_iff]
  simp only [Finset.mem_range, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and,
    or_false]

/-- The bits `k .. S - 1` of `x < 2^S` vanish iff `x < 2^k`. -/
theorem land_hi_eq_zero_iff (S k x : ℕ) (hk : k ≤ S) (hx : x < 2 ^ S) :
    x &&& (2 ^ S - 2 ^ k) = 0 ↔ x < 2 ^ k := by
  have hM : 2 ^ S - 2 ^ k = (2 ^ (S - k) - 1) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel hk]
  rw [hM]
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases hiS : i < S
    · have := congrArg (fun y => y.testBit i) h
      simp only [Nat.testBit_land, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
        Nat.zero_testBit] at this
      have h1 : i ≥ k := hi
      have h2 : i - k < S - k := by omega
      simpa [h1, h2] using this
    · exact Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hiS)))
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_land, Nat.zero_testBit, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hi : k ≤ i
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hi))]
      simp
    · have : ¬ i ≥ k := hi
      simp [this]

/-- `rowOK` on a pack, in its raw form. -/
theorem rowOK_gen (S L k : ℕ) (hS : 1 ≤ S) (hk : k ≤ S) (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ S) :
    Nat.beq (Nat.land (pack S L f) (pack S L (fun _ => Nat.sub (Nat.pow 2 S) (Nat.pow 2 k)))) 0 = true ↔
      ∀ l < L, f l < 2 ^ k := by
  rw [Nat.beq_eq, Nat.land_eq]
  simp only [Nat.pow_eq, Nat.sub_eq]
  have hb : ∀ l < L, (fun _ => 2 ^ S - 2 ^ k) l < 2 ^ S := fun l _ => by
    have h1 : 0 < 2 ^ k := by positivity
    have h2 : 0 < 2 ^ S := by positivity
    simp only; omega
  rw [land_pack S L hS f _ hf hb, pack_eq_zero_iff]
  exact forall₂_congr fun l hl => land_hi_eq_zero_iff S k (f l) hk (hf l hl)

/-- `upRow` on a pack, in its raw form: the lanes move up by `4`, the lanes from `m` on are kept. -/
theorem upRow_gen (S L R m : ℕ) (hR : R = S * L) (hm : m ≤ L) (f : ℕ → ℕ)
    (hf : ∀ l < L, f l < 2 ^ S) :
    Nat.add (Nat.mod (Nat.shiftLeft (pack S L f) (Nat.mul 4 S)) (Nat.pow 2 R))
        (Nat.shiftLeft (Nat.shiftRight (pack S L f) (Nat.mul m S)) (Nat.mul m S)) =
      pack S L (fun l => (if 4 ≤ l then f (l - 4) else 0) + (if m ≤ l then f l else 0)) := by
  rw [Nat.add_eq, raw_mod, raw_shiftLeft, raw_shiftLeft, raw_shiftRight, Nat.mul_eq, Nat.mul_eq,
    Nat.pow_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, hR, mul_comm 4 S,
    mul_comm m S, pack_mul_pow, pack_div_pow S L m f hf, pack_mul_pow, Nat.sub_add_cancel hm,
    pack_add_len S L 4, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt, pack_add]
  · apply pack_congr
    intro l hl
    by_cases h4 : 4 ≤ l <;> by_cases hm' : m ≤ l
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h4, ite_eq_left hm', Nat.sub_add_cancel hm']
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h4, ite_eq_right hm']
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right h4, ite_eq_left hm', Nat.sub_add_cancel hm']
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right h4, ite_eq_right hm']
  · apply pack_lt
    intro l hl
    split_ifs
    · positivity
    · exact hf _ (by omega)

/-! ## Leaves -/

theorem mkRow_eq (f : ℕ → ℕ) : mkRow f = pack S NL f := by
  unfold mkRow
  rw [packTree_eq, pack_ext_len S NL (2 ^ 8) _ (by decide)]
  · apply pack_congr
    intro l hl
    simp [cond_eq_ite, Nat.blt_eq, hl]
  · intro l h1 _
    simp [cond_eq_ite, Nat.blt_eq, not_lt.mpr h1]

theorem lane_pack (n : ℕ) (f : ℕ → ℕ) (hf : ∀ l < n, f l < 2 ^ S) (l : ℕ) :
    lane (pack S n f) l = if l < n then f l else 0 := by
  unfold lane
  exact lane_gen S n f hf l

theorem lfloor_pack (f : ℕ → ℕ) (hf : ∀ l < NL, f l < 2 ^ S) :
    lfloor (pack S NL f) = pack S NL (fun l => f l / 2 ^ W) := by
  unfold lfloor lowMask
  rw [mkRow_eq]
  exact lfloor_gen S NL W (by decide) (by decide) f hf

theorem rowRound_pack (f : ℕ → ℕ) (k : ℕ) (hf : ∀ l < NL, f l < 2 ^ S)
    (hk : ∀ l < NL, k * (f l / 2 ^ W) < 2 ^ S) :
    rowRound (pack S NL f) k = pack S NL (fun l => k * (f l / 2 ^ W) / 2 ^ W) := by
  unfold rowRound
  rw [lfloor_pack f hf, Nat.mul_eq, pack_const_mul]
  exact lfloor_pack (fun l => k * (f l / 2 ^ W)) hk

theorem upRow_pack (f : ℕ → ℕ) (hf : ∀ l < NL, f l < 2 ^ 63) :
    upRow (pack S NL f) = pack S NL (upL f) := by
  unfold upRow
  rw [show Nat.mul (Nat.mul 4 V) S = Nat.mul (4 * V) S from rfl]
  exact upRow_gen S NL RB (4 * V) rfl (by decide) f
    (fun l hl => lt_of_lt_of_le (hf l hl) (Nat.pow_le_pow_right (by norm_num) (by decide)))

theorem rowOK_pack (f : ℕ → ℕ) (hf : ∀ l < NL, f l < 2 ^ S) :
    rowOK (pack S NL f) = true ↔ ∀ l < NL, f l < 2 ^ 63 := by
  unfold rowOK hiMask
  rw [mkRow_eq]
  exact rowOK_gen S NL 63 (by decide) (by decide) f hf

theorem natFold_drop (l : List ℕ) (p : ℕ) : natFold p l (fun _ acc => acc.tail) = l.drop p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [natFold_succ, ih, List.tail_drop]

theorem getR_eq (l : List ℕ) (p : ℕ) : getR l p = l.getD p 0 := by
  unfold getR
  rw [natFold_drop, List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

theorem blockAt_pack (n : ℕ) (g : ℕ → ℕ) (hg : ∀ p < n, g p < 2 ^ RB) (p : ℕ) :
    blockAt (pack RB n g) p = if p < n then g p else 0 := by
  unfold blockAt
  exact lane_gen RB n g hg p

theorem packTable_eq (rows : List ℕ) :
    packTable rows = pack RB 256 (fun p => if p ≤ P + V then rows.getD (min p P) 0 else 0) := by
  unfold packTable
  rw [packTree_eq]
  apply pack_congr
  intro p _
  simp only [zero_add, Nat.add_eq, cond_eq_ite, Nat.ble_eq, getR_eq, minN, Nat.sub_eq,
    Nat.sub_sub_eq_min]

theorem packCol_eq (law g : ℕ) :
    packCol law g = pack RB 64 (fun a => if a ≤ V then lane law (4 * (V - a) + g) else 0) := by
  unfold packCol
  rw [packTree_eq]
  apply pack_congr
  intro a _
  simp only [zero_add, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, cond_eq_ite, Nat.ble_eq]

theorem sumLanes_eq (r : ℕ) : sumLanes r = ∑ l ∈ Finset.range NL, lane r l := by
  unfold sumLanes
  exact natFold_sum NL (lane r)

theorem natFold_and (n : ℕ) (b : ℕ → Bool) :
    natFold n true (fun i acc => and acc (b i)) = true ↔ ∀ i < n, b i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    rw [natFold_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h1 i h
      · exact h ▸ h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem zeroAbove_iff (r t : ℕ) : zeroAbove r t = true ↔ ∀ l < NL, t < l % 4 → lane r l = 0 := by
  unfold zeroAbove
  refine (natFold_and NL _).trans ?_
  refine forall₂_congr fun l _ => ?_
  rw [Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq, raw_mod]
  constructor
  · rintro (h | h) h'
    · omega
    · exact h
  · intro h
    by_cases h' : t < l % 4
    · exact Or.inr (h h')
    · exact Or.inl (by omega)

theorem findTab_append (tabs : List (ℕ × ℕ)) (c t code : ℕ) :
    findTab (tabs ++ [(c, t)]) code =
      if ∃ kv ∈ tabs, kv.1 = code then findTab tabs code else if c = code then t else 0 := by
  induction tabs with
  | nil => simp [findTab, cond_eq_ite, Nat.beq_eq]
  | cons kv rest ih =>
    by_cases hk : kv.1 = code
    · simp [findTab, cond_eq_ite, hk]
    · simp only [List.cons_append, findTab, cond_eq_ite, Nat.beq_eq, hk, ite_false, ih,
        List.mem_cons, exists_eq_or_imp, false_or]

theorem findTab_of_not_mem (tabs : List (ℕ × ℕ)) (code : ℕ) (h : ¬ ∃ kv ∈ tabs, kv.1 = code) :
    findTab tabs code = 0 := by
  induction tabs with
  | nil => rfl
  | cons kv rest ih =>
    simp only [List.mem_cons, exists_eq_or_imp, not_or] at h
    simp only [findTab, cond_eq_ite, Nat.beq_eq, h.1, ite_false]
    exact ih h.2

theorem mcode_eq (a b c : ℕ) : mcode a b c =
    if a + (b - a) ≤ c then 25 * c + 5 * (a + (b - a)) + (a - (a - b))
    else if a - (a - b) ≤ c then 25 * (a + (b - a)) + 5 * c + (a - (a - b))
    else 25 * (a + (b - a)) + 5 * (a - (a - b)) + c := by
  unfold mcode maxN minN
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, cond_eq_ite, Nat.ble_eq]

theorem mcode_swap12 (a b c : ℕ) : mcode a b c = mcode b a c := by
  rw [mcode_eq, mcode_eq]
  split_ifs <;> omega

theorem mcode_swap23 (a b c : ℕ) : mcode a b c = mcode a c b := by
  rw [mcode_eq, mcode_eq]
  split_ifs <;> omega

/-- The code of a sorted triple. -/
theorem mcode_sorted (t0 t1 t2 : ℕ) (h01 : t1 ≤ t0) (h12 : t2 ≤ t1) :
    mcode t1 t2 t0 = 25 * t0 + 5 * t1 + t2 := by
  rw [mcode_eq]
  split_ifs <;> omega

end FrogModel.D3.M1K
