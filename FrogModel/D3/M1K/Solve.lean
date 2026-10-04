module

public import FrogModel.D3.M1K.Row

@[expose] public section

/-!
# The loop `solve` of the checker

`solve row0 es cUp cSame k` lists the rows `rowSeq 0 .. rowSeq P` of the recurrence
`row(j + 1) = rowStep (row j) (es j) cUp cSame k` and tests every one with `rowOK`; on packed rows
with lanes below `2^63`, events below `2^140` and coefficients below `2^65`, `2^66`, `2^63`, the rows
are the packs of the lane recursion `laneSeq` (`solve_lanes`).
-/

open FrogModel.Lanes

namespace FrogModel.D3.M1K

/-- The rows of `solve`. -/
def rowSeq (row0 : ℕ) (es : List ℕ) (cUp cSame k : ℕ) : ℕ → ℕ
  | 0 => row0
  | j + 1 => rowStep (rowSeq row0 es cUp cSame k j) (es.getD j 0) cUp cSame k

theorem solve_fold (row0 : ℕ) (es : List ℕ) (cUp cSame k i : ℕ) :
    natFold i (row0, es, [row0], rowOK row0) (fun _ st =>
      (rowStep st.1 (st.2.1.headD 0) cUp cSame k, st.2.1.tail,
        rowStep st.1 (st.2.1.headD 0) cUp cSame k :: st.2.2.1,
        and st.2.2.2 (rowOK (rowStep st.1 (st.2.1.headD 0) cUp cSame k)))) =
      (rowSeq row0 es cUp cSame k i, es.drop i,
        ((List.range (i + 1)).map (rowSeq row0 es cUp cSame k)).reverse,
        (List.range (i + 1)).all fun j => rowOK (rowSeq row0 es cUp cSame k j)) := by
  induction i with
  | zero => simp [natFold, rowSeq]
  | succ i ih =>
    rw [natFold_succ, ih]
    have hd : (es.drop i).headD 0 = es.getD i 0 := by
      rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
    simp only [hd, List.tail_drop, List.range_succ (n := i + 1), List.map_append, List.map_cons,
      List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.all_append, List.all_cons, List.all_nil, Bool.and_true, rowSeq]

theorem solve_eq (row0 : ℕ) (es : List ℕ) (cUp cSame k : ℕ) :
    solve row0 es cUp cSame k =
      ((List.range (P + 1)).map (rowSeq row0 es cUp cSame k),
        (List.range (P + 1)).all fun j => rowOK (rowSeq row0 es cUp cSame k j)) := by
  dsimp only [solve]
  rw [solve_fold, List.reverse_reverse]

theorem solve_getD (row0 : ℕ) (es : List ℕ) (cUp cSame k p : ℕ) (hp : p ≤ P) :
    (solve row0 es cUp cSame k).1.getD p 0 = rowSeq row0 es cUp cSame k p := by
  rw [solve_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem solve_ok (row0 : ℕ) (es : List ℕ) (cUp cSame k : ℕ) :
    (solve row0 es cUp cSame k).2 = true ↔ ∀ j ≤ P, rowOK (rowSeq row0 es cUp cSame k j) = true := by
  rw [solve_eq]
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩

/-- The value of a lane after one step of a recurrence. -/
def stepL (cUp cSame k : ℕ) (f e : ℕ → ℕ) (l : ℕ) : ℕ :=
  k * ((cUp * upL f l + cSame * f l + e l) / 2 ^ W) / 2 ^ W

theorem upL_lt (f : ℕ → ℕ) (hf : ∀ l < NL, f l < 2 ^ 63) (l : ℕ) (hl : l < NL) : upL f l < 2 ^ 64 := by
  unfold upL
  have h1 : (if 4 ≤ l then f (l - 4) else 0) < 2 ^ 63 := by
    split_ifs
    · exact hf _ (by omega)
    · positivity
  have h2 : (if 4 * V ≤ l then f l else 0) < 2 ^ 63 := by
    split_ifs
    · exact hf _ hl
    · positivity
  have : (2 : ℕ) ^ 64 = 2 ^ 63 + 2 ^ 63 := by norm_num
  omega

theorem num_lt (cUp cSame : ℕ) (f e : ℕ → ℕ) (hf : ∀ l < NL, f l < 2 ^ 63) (he : ∀ l < NL, e l < 2 ^ 140)
    (hcU : cUp < 2 ^ 65) (hcS : cSame < 2 ^ 66) (l : ℕ) (hl : l < NL) :
    cUp * upL f l + cSame * f l + e l < 2 ^ 141 := by
  have h1 : cUp * upL f l < 2 ^ 65 * 2 ^ 64 := Nat.mul_lt_mul'' hcU (upL_lt f hf l hl)
  have h2 : cSame * f l < 2 ^ 66 * 2 ^ 63 := Nat.mul_lt_mul'' hcS (hf l hl)
  have h3 := he l hl
  have : (2 : ℕ) ^ 65 * 2 ^ 64 + 2 ^ 66 * 2 ^ 63 + 2 ^ 140 ≤ 2 ^ 141 := by norm_num
  omega

theorem stepL_lt (cUp cSame k : ℕ) (f e : ℕ → ℕ) (hf : ∀ l < NL, f l < 2 ^ 63)
    (he : ∀ l < NL, e l < 2 ^ 140) (hcU : cUp < 2 ^ 65) (hcS : cSame < 2 ^ 66) (hk : k < 2 ^ 63)
    (l : ℕ) (hl : l < NL) : k * ((cUp * upL f l + cSame * f l + e l) / 2 ^ W) < 2 ^ S := by
  have h1 := num_lt cUp cSame f e hf he hcU hcS l hl
  have h2 : (cUp * upL f l + cSame * f l + e l) / 2 ^ W < 2 ^ 79 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc _ < 2 ^ 141 := h1
      _ = 2 ^ 79 * 2 ^ W := by simp only [W]; norm_num
  calc k * _ < 2 ^ 63 * 2 ^ 79 := Nat.mul_lt_mul'' hk h2
    _ ≤ 2 ^ S := by simp only [S]; norm_num

theorem rowStep_pack (cUp cSame k : ℕ) (f e : ℕ → ℕ) (hf : ∀ l < NL, f l < 2 ^ 63)
    (he : ∀ l < NL, e l < 2 ^ 140) (hcU : cUp < 2 ^ 65) (hcS : cSame < 2 ^ 66) (hk : k < 2 ^ 63) :
    rowStep (pack S NL f) (pack S NL e) cUp cSame k = pack S NL (stepL cUp cSame k f e) := by
  unfold rowStep
  have hnum : Nat.add (Nat.add (Nat.mul cUp (upRow (pack S NL f))) (Nat.mul cSame (pack S NL f)))
      (pack S NL e) = pack S NL (fun l => cUp * upL f l + cSame * f l + e l) := by
    rw [upRow_pack f hf]
    show cUp * pack S NL (upL f) + cSame * pack S NL f + pack S NL e = _
    rw [pack_const_mul, pack_const_mul, pack_add, pack_add]
  rw [hnum, rowRound_pack]
  · rfl
  · intro l hl
    exact (num_lt cUp cSame f e hf he hcU hcS l hl).trans (by simp only [S]; norm_num)
  · exact stepL_lt cUp cSame k f e hf he hcU hcS hk

/-- The lanes of the rows of `solve`. -/
def laneSeq (f0 : ℕ → ℕ) (E : ℕ → ℕ → ℕ) (cUp cSame k : ℕ) : ℕ → ℕ → ℕ
  | 0 => f0
  | j + 1 => stepL cUp cSame k (laneSeq f0 E cUp cSame k j) (E j)

theorem solve_lanes (f0 : ℕ → ℕ) (E : ℕ → ℕ → ℕ) (es : List ℕ) (cUp cSame k : ℕ)
    (hf0 : ∀ l < NL, f0 l < 2 ^ 63) (hes : ∀ j < P, es.getD j 0 = pack S NL (E j))
    (hE : ∀ j < P, ∀ l < NL, E j l < 2 ^ 140) (hcU : cUp < 2 ^ 65) (hcS : cSame < 2 ^ 66)
    (hk : k < 2 ^ 63) (hok : (solve (pack S NL f0) es cUp cSame k).2 = true) :
    ∀ j ≤ P, rowSeq (pack S NL f0) es cUp cSame k j = pack S NL (laneSeq f0 E cUp cSame k j) ∧
      ∀ l < NL, laneSeq f0 E cUp cSame k j l < 2 ^ 63 := by
  have hok' := (solve_ok _ _ _ _ _).1 hok
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, hf0⟩
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    have heq : rowSeq (pack S NL f0) es cUp cSame k (j + 1) =
        pack S NL (laneSeq f0 E cUp cSame k (j + 1)) := by
      show rowStep _ (es.getD j 0) cUp cSame k = _
      rw [h1, hes j (by omega), rowStep_pack cUp cSame k _ _ h2 (hE j (by omega)) hcU hcS hk]
      rfl
    refine ⟨heq, ?_⟩
    have hr := hok' (j + 1) hj
    rw [heq, rowOK_pack] at hr
    · exact hr
    · intro l hl
      exact (Nat.div_le_self _ _).trans_lt
        (stepL_lt cUp cSame k _ _ h2 (hE j (by omega)) hcU hcS hk l hl)

end FrogModel.D3.M1K
