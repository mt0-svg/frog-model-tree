module

public import FrogModel.D3.M1K.Solve

@[expose] public section

/-!
# Tables and event rows of the checker

A table is `TabRows T R`: `T` packs the rows `R 0 .. R P` (lanes below `2^63`) and `V` copies of the
row `P` at the stride `RB`. The product of a column (slot `i` the weight of the answer `V - i`) with
a table is, block by block, the correlation of the column with the rows (Kronecker substitution in two
dimensions); `eventRows` reads the blocks `V + j` of a sum of such products (`eventRows_getD`).
-/

open FrogModel.Lanes

namespace FrogModel.D3.M1K

/-- `T` is the table of the rows `R 0 .. R P`, each lane below `2^63`. -/
def TabRows (T : ℕ) (R : ℕ → ℕ → ℕ) : Prop :=
  T = pack RB 256 (fun p => if p ≤ P + V then pack S NL (R (min p P)) else 0) ∧
    ∀ p ≤ P, ∀ l < NL, R p l < 2 ^ 63

theorem RB_eq : RB = S * NL := rfl

theorem row_lt (f : ℕ → ℕ) (hf : ∀ l < NL, f l < 2 ^ S) : pack S NL f < 2 ^ RB := by
  rw [RB_eq]; exact pack_lt S NL f hf

theorem lt_S_of_lt_63 {a : ℕ} (h : a < 2 ^ 63) : a < 2 ^ S :=
  h.trans (Nat.pow_lt_pow_right (by norm_num) (by simp only [S]; norm_num))

theorem tabRows_zero : TabRows 0 (fun _ _ => 0) := by
  refine ⟨?_, fun _ _ _ _ => by positivity⟩
  symm
  unfold pack
  exact Finset.sum_eq_zero fun p _ => by simp

theorem tabRows_lane (T : ℕ) (R : ℕ → ℕ → ℕ) (h : TabRows T R) (q : ℕ) (hq : q ≤ P) (l : ℕ)
    (hl : l < NL) : lane (blockAt T q) l = R q l := by
  obtain ⟨hT, hR⟩ := h
  rw [hT, blockAt_pack]
  · have hq' : q < 256 := by simp only [P] at hq; omega
    have hqP : q ≤ P + V := by omega
    simp only [hq', hqP, ite_true, Nat.min_eq_left hq]
    rw [lane_pack NL _ (fun l hl => lt_S_of_lt_63 (hR q hq l hl)) l]
    simp [hl]
  · intro p _
    split_ifs
    · exact row_lt _ fun l hl => lt_S_of_lt_63 (hR _ (Nat.min_le_right _ _) l hl)
    · positivity

theorem packTable_rows (rows : List ℕ) (R : ℕ → ℕ → ℕ)
    (h : ∀ p ≤ P, rows.getD p 0 = pack S NL (R p)) (hR : ∀ p ≤ P, ∀ l < NL, R p l < 2 ^ 63) :
    TabRows (packTable rows) R := by
  refine ⟨?_, hR⟩
  rw [packTable_eq]
  refine pack_congr _ _ _ _ fun p _ => ?_
  split_ifs
  · exact h _ (Nat.min_le_right _ _)
  · rfl

/-- Row `q` of the extended table, lane by lane (`0` past `P + V`). -/
def extL (R : ℕ → ℕ → ℕ) (q l : ℕ) : ℕ := if q ≤ P + V then R (min q P) l else 0

/-- **Kronecker substitution in two dimensions**: a column of `64` slots times a table is, at the
block `r`, the pack of the correlations `∑_i col i · R (r - i)` lane by lane. -/
theorem col_mul_tab (col : ℕ → ℕ) (T : ℕ) (R : ℕ → ℕ → ℕ) (hT : TabRows T R) :
    pack RB 64 col * T = pack RB 320 (fun r => pack S NL (fun l =>
      ∑ i ∈ Finset.range 64, if i ≤ r ∧ r - i < 256 then col i * extL R (r - i) l else 0)) := by
  rw [hT.1, pack_mul_pack]
  refine pack_congr _ _ _ _ fun r _ => ?_
  rw [← pack_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h1 h2
    · rw [pack_const_mul]
      refine pack_congr _ _ _ _ fun l _ => ?_
      simp [extL, h2]
    · simp [pack, extL, h2]
    · simp [pack]


/-- The correlation of a column with the rows of a table at the block `r`, lane `l`. -/
def corr (col : ℕ → ℕ) (R : ℕ → ℕ → ℕ) (r l : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 64, if i ≤ r ∧ r - i < 256 then col i * extL R (r - i) l else 0

/-- The column of `packCol law g`: slot `i` the lane `(V - i, g)` of `law`. -/
def colv (law g i : ℕ) : ℕ := if i ≤ V then lane law (4 * (V - i) + g) else 0

/-- The canonical rows of a table. -/
def tabR (T p l : ℕ) : ℕ := lane (blockAt T p) l

/-- `T` is a table, with the rows it holds. -/
theorem zero_lane_aux (a m b n : ℕ) : Nat.mod (Nat.shiftRight (Nat.mod (Nat.shiftRight 0 a) m) b) n = 0 := by
  show (((0 >>> a) % m) >>> b) % n = 0
  simp

theorem tabR_zero (p l : ℕ) : tabR 0 p l = 0 := zero_lane_aux _ _ _ _

def TabOK (T : ℕ) : Prop := TabRows T (tabR T)

theorem tabOK_of_tabRows (T : ℕ) (R : ℕ → ℕ → ℕ) (h : TabRows T R) : TabOK T := by
  have e : ∀ p ≤ P, ∀ l < NL, tabR T p l = R p l := fun p hp l hl => tabRows_lane T R h p hp l hl
  refine ⟨h.1.trans ?_, fun p hp l hl => (e p hp l hl).symm ▸ h.2 p hp l hl⟩
  refine pack_congr _ _ _ _ fun p _ => ?_
  split_ifs
  · exact pack_congr _ _ _ _ fun l hl => (e _ (Nat.min_le_right _ _) l hl).symm
  · rfl

theorem tabOK_zero : TabOK 0 := by
  have h := tabRows_zero
  have e : tabR 0 = fun _ _ => 0 := by
    funext p l
    exact tabR_zero p l
  unfold TabOK
  rw [e]
  exact h

theorem col_mul_tabOK (law g T : ℕ) (hT : TabOK T) :
    packCol law g * T = pack RB 320 (fun r => pack S NL (corr (colv law g) (tabR T) r)) := by
  rw [packCol_eq, col_mul_tab _ T _ hT]
  rfl

/-- The block `V + p` of a correlation: the sum over the answers `b ≤ V` of the slot `V - b` times
the row `min (p + b) P`. -/
theorem corr_at (col : ℕ → ℕ) (hcol : ∀ i, V < i → col i = 0) (R : ℕ → ℕ → ℕ) (p : ℕ) (hp : p ≤ P)
    (l : ℕ) : corr col R (V + p) l = ∑ b ∈ Finset.range (V + 1), col (V - b) * R (min (p + b) P) l := by
  have hV : V = 48 := rfl
  have hP : P = 96 := rfl
  unfold corr
  rw [← Finset.sum_subset (s₁ := Finset.range (V + 1)) (s₂ := Finset.range 64)
    (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega) ?z]
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_range] at hb
    rw [show V + 1 - 1 - b = V - b by omega, ite_eq_left ⟨by omega, by omega⟩]
    unfold extL
    rw [ite_eq_left (by omega), show V + p - (V - b) = p + b by omega]
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [hcol i (by omega)]
    simp

theorem corr_le (col : ℕ → ℕ) (hcol : ∀ i, col i ≤ 2 ^ 62) (R : ℕ → ℕ → ℕ)
    (hR : ∀ p ≤ P, ∀ l < NL, R p l < 2 ^ 63) (r l : ℕ) (hl : l < NL) : corr col R r l ≤ 2 ^ 131 := by
  unfold corr
  calc _ ≤ ∑ i ∈ Finset.range 64, 2 ^ 125 := Finset.sum_le_sum fun i _ => ?_
    _ = 2 ^ 131 := by norm_num
  split_ifs
  · have h2 : extL R (r - i) l ≤ 2 ^ 63 := by
      unfold extL
      split_ifs
      · exact (hR _ (min_le_right _ _) l hl).le
      · exact Nat.zero_le _
    calc col i * extL R (r - i) l ≤ 2 ^ 62 * 2 ^ 63 := Nat.mul_le_mul (hcol i) h2
      _ = 2 ^ 125 := by norm_num
  · exact Nat.zero_le _

theorem eventRows_getD (F : ℕ → ℕ) (hF : ∀ r < 320, F r < 2 ^ RB) (j : ℕ) (hj : j < 128) :
    (eventRows (pack RB 320 F)).getD j 0 = F (V + j) := by
  have hV : V = 48 := rfl
  unfold eventRows
  have hl : V + j < 320 := by omega
  generalize RB = B at hF ⊢
  rw [blocks_eq, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left (show j < 2 ^ 7 by norm_num; omega), Option.getD_some]
  show pack B 320 F >>> (B * V) / 2 ^ (B * j) % 2 ^ B = _
  rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add, ← mul_add]
  exact pack_div_mod B 320 F hF (V + j) hl

/-- The lanes of the channel products of a child of type `t` with siblings `a`, `b`. -/
def chanL (s : St) (tabs : List (ℕ × ℕ)) (t a b r l : ℕ) : ℕ :=
  ∑ g ∈ Finset.range (gmax t), corr (colv (lawOf s t) g) (tabR (findTab tabs (mcode a b g))) r l

theorem chan_eq (s : St) (tabs : List (ℕ × ℕ)) (htabs : ∀ c, TabOK (findTab tabs c)) (t a b : ℕ) :
    chan s tabs t a b = pack RB 320 (fun r => pack S NL (chanL s tabs t a b r)) := by
  unfold chan
  rw [natFold_sum]
  show ∑ g ∈ Finset.range (gmax t), packCol (lawOf s t) g * findTab tabs (mcode a b g) = _
  simp only [col_mul_tabOK _ _ _ (htabs _)]
  rw [pack_sum]
  refine pack_congr _ _ _ _ fun r _ => ?_
  rw [pack_sum]
  rfl

/-- The lanes of the events of the multiset `(t0, t1, t2)`. -/
def evL (s : St) (tabs : List (ℕ × ℕ)) (t0 t1 t2 r l : ℕ) : ℕ :=
  chanL s tabs t0 t1 t2 r l + chanL s tabs t1 t0 t2 r l + chanL s tabs t2 t0 t1 r l

theorem eventX_eq (s : St) (tabs : List (ℕ × ℕ)) (htabs : ∀ c, TabOK (findTab tabs c)) (t0 t1 t2 : ℕ) :
    eventX s tabs t0 t1 t2 = pack RB 320 (fun r => pack S NL (evL s tabs t0 t1 t2 r)) := by
  unfold eventX
  rw [chan_eq s tabs htabs, chan_eq s tabs htabs, chan_eq s tabs htabs]
  show pack RB 320 _ + pack RB 320 _ + pack RB 320 _ = _
  rw [pack_add, pack_add]
  refine pack_congr _ _ _ _ fun r _ => ?_
  rw [pack_add, pack_add]
  rfl

end FrogModel.D3.M1K
