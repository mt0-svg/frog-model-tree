module

public import FrogModel.D3.M1K.Event
public import FrogModel.D3.M1K.Real

@[expose] public section

/-!
# The R closure of the checker is a sub-solution of `Wrec`

On a stored height `s` (`validSt s`), the real laws `rhoR s` and `KR s` are the lanes over `2^62`.
A list of tables `tabs` (code, table) is read as the real table `Tr tabs`: the multiset `σ` reads the
first table of the code `cd σ` (`0` if there is none). The fold `closure s` keeps `Good s tabs`: every
table is a table of rows below `2^63`, and `Tr tabs` is a sub-solution of the R recursion
(`wrec_lower`); appending a table only raises `Tr`, and the new table is below the step of the
recursion read on the tables before it (the step rounds down, as in the remark after Proposition 13.3
of the paper). So the table of the code `124` (`NNN`) is below `Wrec` (`closure_sound`).
-/

open FrogModel.Lanes FrogModel.D3.Iface

namespace FrogModel.D3.M1K

/-! ## The real laws of a stored height -/

/-- `rho*`: lane `(b, f)` over `2^62`. -/
noncomputable def rhoR (s : St) (b f : ℕ) : ℝ :=
  if b ≤ V ∧ f ≤ 3 then (lane s.rho (4 * b + f) : ℝ) / 2 ^ 62 else 0

/-- `K*(t -> .)`: lane `(a, f)` of the law of `t` over `2^62`. -/
noncomputable def KR (s : St) (t a f : ℕ) : ℝ :=
  if a ≤ V ∧ f ≤ 3 then (lane (lawOf s t) (4 * a + f) : ℝ) / 2 ^ 62 else 0

/-- The code of a multiset of child types (`N` is `4`). -/
def cd (σ : Fin 3 → CType) : ℕ := mcode (tval (σ 0)) (tval (σ 1)) (tval (σ 2))

/-- The child type of a number `t ≤ 4`. -/
def dec (t : ℕ) : CType := if h : t < 4 then some ⟨t, h⟩ else none

/-- The child types `(t0, t1, t2)`. -/
def σOf (t0 t1 t2 : ℕ) : Fin 3 → CType := ![dec t0, dec t1, dec t2]

/-- The real table of a list of tables. -/
noncomputable def Tr (tabs : List (ℕ × ℕ)) (σ : Fin 3 → CType) (p x g : ℕ) : ℝ :=
  if p ≤ P ∧ x ≤ V ∧ g ≤ 3 then (tabR (findTab tabs (cd σ)) p (4 * x + g) : ℝ) / 2 ^ 62 else 0

/-! ## Leaves -/

theorem D_eq : D = 2 ^ 62 := rfl

theorem div_pow_zero (r n m : ℕ) (h : r < 2 ^ n) (hnm : n ≤ m) : r / 2 ^ m = 0 :=
  Nat.div_eq_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hnm))

theorem lane_le_of_validRow (r : ℕ) (hr : validRow r = true) (l : ℕ) : lane r l ≤ 2 ^ 62 := by
  unfold validRow at hr
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.pow_eq] at hr
  obtain ⟨hlt, hsum⟩ := hr
  rw [sumLanes_eq] at hsum
  by_cases hl : l < NL
  · have := Finset.single_le_sum (f := fun l => lane r l) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hl)
    rw [hsum] at this
    exact this
  · have : lane r l = 0 := by
      unfold lane
      change (r >>> (S * l)) % 2 ^ S = 0
      have hRl : RB ≤ S * l := by simp only [RB, S, NL] at hl ⊢; omega
      generalize RB = R at hlt hRl
      rw [Nat.shiftRight_eq_div_pow, div_pow_zero r R _ hlt hRl]
      rfl
    rw [this]; exact Nat.zero_le _

theorem validRow_lawOf (s : St) (hs : validSt s = true) (t : ℕ) : validRow (lawOf s t) = true := by
  unfold validSt at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨hr, h0, -⟩, ⟨h1, -⟩, ⟨h2, -⟩, h3, -⟩ := hs
  unfold lawOf
  rcases Nat.lt_or_ge t 5 with ht | ht
  · interval_cases t
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact hr
  · have hb : ∀ i, i < 5 → Nat.beq t i = false := fun i hi =>
      Bool.eq_false_iff.mpr (fun h => by have := Nat.eq_of_beq_eq_true h; omega)
    rw [hb 4 (by norm_num), hb 3 (by norm_num), hb 2 (by norm_num), hb 1 (by norm_num)]
    exact h0

theorem tval_dec (t : ℕ) (ht : t ≤ 4) : tval (dec t) = t := by
  unfold dec
  split_ifs with h
  · rfl
  · simp [tval]; omega

theorem dec_lt (t : ℕ) (h : t < 4) : dec t = some ⟨t, h⟩ := dite_eq_left h

theorem dec_four : dec 4 = none := dite_eq_right (by norm_num)

theorem isN_dec (t : ℕ) (ht : t ≤ 4) : (if dec t = none then 1 else 0) = isN t := by
  rcases Nat.lt_or_ge t 4 with h | h
  · rw [dec_lt t h, ite_eq_right (by simp)]
    unfold isN
    rw [show Nat.beq t 4 = false from Bool.eq_false_iff.mpr (fun e => by have := Nat.eq_of_beq_eq_true e; omega)]
    rfl
  · obtain rfl : t = 4 := by omega
    rw [dec_four]; rfl

theorem lossW_lt (s : St) (t : ℕ) (h : t < 4) : lossW s t = lane (lawOf s t) t := by
  unfold lossW; rw [show Nat.blt t 4 = true from Nat.blt_eq.mpr h]; rfl

theorem loopW_lt (s : St) (t : ℕ) (h : t < 4) : loopW s t = lane (lawOf s t) (4 + t) := by
  unfold loopW; rw [show Nat.blt t 4 = true from Nat.blt_eq.mpr h]; rfl

theorem lost_term (s : St) (t : ℕ) (ht : t ≤ 4) :
    (match dec t with | none => (0 : ℝ) | some u => KR s u 0 u) = (lossW s t : ℝ) / 2 ^ 62 := by
  rcases Nat.lt_or_ge t 4 with h | h
  · rw [dec_lt t h, lossW_lt s t h]
    simp only
    unfold KR
    rw [ite_eq_left ⟨Nat.zero_le _, by omega⟩, show 4 * 0 + t = t by omega]
  · obtain rfl : t = 4 := by omega
    rw [dec_four]; simp only; rw [show lossW s 4 = 0 from rfl]; simp

theorem loop_term (s : St) (t : ℕ) (ht : t ≤ 4) :
    (match dec t with | none => (0 : ℝ) | some u => KR s u 1 u) = (loopW s t : ℝ) / 2 ^ 62 := by
  rcases Nat.lt_or_ge t 4 with h | h
  · rw [dec_lt t h, loopW_lt s t h]
    simp only
    unfold KR
    rw [ite_eq_left ⟨by simp [V], by omega⟩, show 4 * 1 + t = 4 + t by omega]
  · obtain rfl : t = 4 := by omega
    rw [dec_four]; simp only; rw [show loopW s 4 = 0 from rfl]; simp

theorem cd_perm (σ : Fin 3 → CType) (π : Equiv.Perm (Fin 3)) : cd (σ ∘ π) = cd σ := by
  revert σ π
  decide +kernel

theorem numN_perm (σ : Fin 3 → CType) (π : Equiv.Perm (Fin 3)) : numN (σ ∘ π) = numN σ := by
  unfold numN
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp π (fun c => if σ c = none then 1 else 0)

theorem sort_exists (σ : Fin 3 → CType) :
    ∃ π : Equiv.Perm (Fin 3), σ ∘ π = σOf (cd σ / 25) (cd σ / 5 % 5) (cd σ % 5) := by
  revert σ
  decide +kernel

theorem wBody_perm (V P : ℕ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (T : (Fin 3 → CType) → ℕ → ℕ → ℕ → ℝ) (π : Equiv.Perm (Fin 3))
    (hT : ∀ τ, T (τ ∘ π) = T τ) (σ : Fin 3 → CType) (p x g : ℕ) :
    wBody V P ρ K T (σ ∘ π) p x g = wBody V P ρ K T σ p x g := by
  have hu : ∀ c v, Function.update (σ ∘ π) c v = Function.update σ (π c) v ∘ π := fun c v =>
    (Function.update_comp_eq_of_injective σ π.injective c v).symm
  have hevC : ∀ c, evC V P ρ K T (σ ∘ π) c p x g = evC V P ρ K T σ (π c) p x g := by
    intro c
    unfold evC
    simp only [Function.comp_apply, hu, hT]
  have hlost : lostS K (σ ∘ π) = lostS K σ := by
    unfold lostS
    congr 1
    exact Equiv.sum_comp π (fun c => match σ c with | none => 0 | some t => K t 0 t)
  have hloop : loopS K (σ ∘ π) = loopS K σ := by
    unfold loopS
    congr 1
    exact Equiv.sum_comp π (fun c => match σ c with | none => 0 | some t => K t 1 t)
  unfold wBody
  rw [hT, hlost, hloop, Finset.sum_congr rfl (fun c _ => hevC c),
    Equiv.sum_comp π (fun c => evC V P ρ K T σ c p x g)]

theorem numN_sigOf (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ 4) (h2 : t2 ≤ 4) :
    numN (σOf t0 t1 t2) = isN t0 + isN t1 + isN t2 := by
  unfold numN
  rw [Finset.card_filter, Fin.sum_univ_three, ← isN_dec t0 h0, ← isN_dec t1 h1, ← isN_dec t2 h2]
  rfl

theorem cd_sigOf (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ 4) (h2 : t2 ≤ 4) :
    cd (σOf t0 t1 t2) = mcode t0 t1 t2 := by
  show mcode (tval (dec t0)) (tval (dec t1)) (tval (dec t2)) = _
  rw [tval_dec t0 h0, tval_dec t1 h1, tval_dec t2 h2]

theorem cd_update0 (t0 t1 t2 : ℕ) (h1 : t1 ≤ 4) (h2 : t2 ≤ 4) (f : Fin 4) :
    cd (Function.update (σOf t0 t1 t2) 0 (some f)) = mcode t1 t2 f := by
  unfold cd
  rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  show mcode f (tval (dec t1)) (tval (dec t2)) = _
  rw [tval_dec t1 h1, tval_dec t2 h2, mcode_swap12, mcode_swap23]

theorem cd_update1 (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h2 : t2 ≤ 4) (f : Fin 4) :
    cd (Function.update (σOf t0 t1 t2) 1 (some f)) = mcode t0 t2 f := by
  unfold cd
  rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  show mcode (tval (dec t0)) f (tval (dec t2)) = _
  rw [tval_dec t0 h0, tval_dec t2 h2, mcode_swap23]

theorem cd_update2 (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ 4) (f : Fin 4) :
    cd (Function.update (σOf t0 t1 t2) 2 (some f)) = mcode t0 t1 f := by
  unfold cd
  rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  show mcode (tval (dec t0)) (tval (dec t1)) f = _
  rw [tval_dec t0 h0, tval_dec t1 h1]

/-- The point mass at the lane `n`. -/
theorem shiftLeft_eq_pack (n : ℕ) (hn : n < NL) :
    Nat.shiftLeft D (Nat.mul S n) = pack S NL (fun l => if l = n then D else 0) := by
  unfold pack
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range NL) n, ite_eq_left (Finset.mem_range.mpr hn)]
  exact Nat.shiftLeft_eq D (S * n)

theorem stepL_congr (cUp cSame k : ℕ) (f f' e : ℕ → ℕ) (h : ∀ l < NL, f l = f' l) (l : ℕ)
    (hl : l < NL) : stepL cUp cSame k f e l = stepL cUp cSame k f' e l := by
  unfold stepL upL
  rw [h l hl]
  split_ifs with h1 <;> simp only [h (l - 4) (by omega)]

/-! ## Bounds on a valid height -/

theorem lane_lawOf_le (s : St) (hs : validSt s = true) (t l : ℕ) : lane (lawOf s t) l ≤ 2 ^ 62 :=
  lane_le_of_validRow _ (validRow_lawOf s hs t) l

theorem lossW_le (s : St) (hs : validSt s = true) (t : ℕ) : lossW s t ≤ 2 ^ 62 := by
  unfold lossW
  cases Nat.blt t 4
  · exact Nat.zero_le _
  · exact lane_lawOf_le s hs t _

theorem loopW_le (s : St) (hs : validSt s = true) (t : ℕ) : loopW s t ≤ 2 ^ 62 := by
  unfold loopW
  cases Nat.blt t 4
  · exact Nat.zero_le _
  · exact lane_lawOf_le s hs t _

theorem colv_le (s : St) (hs : validSt s = true) (t g i : ℕ) : colv (lawOf s t) g i ≤ 2 ^ 62 := by
  unfold colv
  split_ifs
  · exact lane_lawOf_le s hs t _
  · exact Nat.zero_le _

theorem colv_zero (law g i : ℕ) (hi : V < i) : colv law g i = 0 := by
  unfold colv
  rw [ite_eq_right (by omega)]

theorem chanL_le (s : St) (hs : validSt s = true) (tabs : List (ℕ × ℕ))
    (htabs : ∀ c, TabOK (findTab tabs c)) (t a b r l : ℕ) (ht : t ≤ 4) (hl : l < NL) :
    chanL s tabs t a b r l ≤ 4 * 2 ^ 131 := by
  unfold chanL
  have hg : gmax t ≤ 4 := by
    unfold gmax
    cases Nat.beq t 4
    · exact ht
    · exact le_rfl
  calc _ ≤ ∑ _g ∈ Finset.range (gmax t), 2 ^ 131 :=
        Finset.sum_le_sum fun g _ => corr_le _ (colv_le s hs t g) _ (htabs _).2 r l hl
    _ ≤ 4 * 2 ^ 131 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        exact Nat.mul_le_mul_right _ hg

theorem evL_lt (s : St) (hs : validSt s = true) (tabs : List (ℕ × ℕ))
    (htabs : ∀ c, TabOK (findTab tabs c)) (t0 t1 t2 r l : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ 4) (h2 : t2 ≤ 4)
    (hl : l < NL) : evL s tabs t0 t1 t2 r l < 2 ^ 140 := by
  unfold evL
  have h0 := chanL_le s hs tabs htabs t0 t1 t2 r l h0 hl
  have h1 := chanL_le s hs tabs htabs t1 t0 t2 r l h1 hl
  have h2 := chanL_le s hs tabs htabs t2 t0 t1 r l h2 hl
  have : 3 * (4 * 2 ^ 131) < 2 ^ 140 := by norm_num
  omega

/-! ## A table of the closure, in natural numbers -/

/-- The table of a run of `solve` whose rows are packs of lanes below `2^63`. -/
theorem solve_table (row0 : ℕ) (es : List ℕ) (cUp cSame k : ℕ) (f0 : ℕ → ℕ) (E : ℕ → ℕ → ℕ)
    (hrow : ∀ j ≤ P, rowSeq row0 es cUp cSame k j = pack S NL (laneSeq f0 E cUp cSame k j))
    (hlt : ∀ j ≤ P, ∀ l < NL, laneSeq f0 E cUp cSame k j l < 2 ^ 63) :
    TabOK (packTable (solve row0 es cUp cSame k).1) ∧
      (∀ l < NL, tabR (packTable (solve row0 es cUp cSame k).1) 0 l = f0 l) ∧
      ∀ p < P, ∀ l < NL, tabR (packTable (solve row0 es cUp cSame k).1) (p + 1) l =
        stepL cUp cSame k (tabR (packTable (solve row0 es cUp cSame k).1) p) (E p) l := by
  have hT := packTable_rows (solve row0 es cUp cSame k).1 (laneSeq f0 E cUp cSame k)
    (fun p hp => (solve_getD _ _ _ _ _ p hp).trans (hrow p hp)) hlt
  generalize packTable (solve row0 es cUp cSame k).1 = T at hT ⊢
  have he : ∀ p ≤ P, ∀ l < NL, tabR T p l = laneSeq f0 E cUp cSame k p l :=
    fun p hp l hl => tabRows_lane T _ hT p hp l hl
  refine ⟨tabOK_of_tabRows T _ hT, fun l hl => he 0 (Nat.zero_le _) l hl, fun p hp l hl => ?_⟩
  rw [he (p + 1) hp l hl]
  exact stepL_congr _ _ _ _ _ _ (fun l' hl' => (he p hp.le l' hl').symm) l hl

theorem sigmaTable_eq (s : St) (tabs : List (ℕ × ℕ)) (t0 t1 t2 : ℕ) :
    sigmaTable s tabs t0 t1 t2 =
      (packTable (solve (Nat.shiftLeft D (Nat.mul S (isN t0 + isN t1 + isN t2)))
          (eventRows (eventX s tabs t0 t1 t2)) D (lossW s t0 + lossW s t1 + lossW s t2)
          (D * D / (4 * D - (loopW s t0 + loopW s t1 + loopW s t2)))).1,
        (solve (Nat.shiftLeft D (Nat.mul S (isN t0 + isN t1 + isN t2)))
          (eventRows (eventX s tabs t0 t1 t2)) D (lossW s t0 + lossW s t1 + lossW s t2)
          (D * D / (4 * D - (loopW s t0 + loopW s t1 + loopW s t2)))).2) := rfl

/-- The table of the multiset `(t0, t1, t2)`: its rows are the rows of the rounded recursion, read
on the tables `tabs` for the events. -/
theorem sigmaTable_spec (s : St) (hs : validSt s = true) (tabs : List (ℕ × ℕ))
    (htabs : ∀ c, TabOK (findTab tabs c)) (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ 4) (h2 : t2 ≤ 4)
    (hok : (sigmaTable s tabs t0 t1 t2).2 = true) :
    TabOK (sigmaTable s tabs t0 t1 t2).1 ∧
      (∀ l < NL, tabR (sigmaTable s tabs t0 t1 t2).1 0 l =
        if l = isN t0 + isN t1 + isN t2 then D else 0) ∧
      ∀ p < P, ∀ l < NL, tabR (sigmaTable s tabs t0 t1 t2).1 (p + 1) l =
        stepL D (lossW s t0 + lossW s t1 + lossW s t2)
          (D * D / (4 * D - (loopW s t0 + loopW s t1 + loopW s t2)))
          (tabR (sigmaTable s tabs t0 t1 t2).1 p) (evL s tabs t0 t1 t2 (V + p)) l := by
  have hlo : lossW s t0 + lossW s t1 + lossW s t2 < 2 ^ 66 := by
    have := lossW_le s hs t0; have := lossW_le s hs t1; have := lossW_le s hs t2; omega
  have hlp : loopW s t0 + loopW s t1 + loopW s t2 ≤ 3 * 2 ^ 62 := by
    have := loopW_le s hs t0; have := loopW_le s hs t1; have := loopW_le s hs t2; omega
  have hk : D * D / (4 * D - (loopW s t0 + loopW s t1 + loopW s t2)) < 2 ^ 63 := by
    rw [D_eq]
    calc _ ≤ 2 ^ 62 * 2 ^ 62 / 2 ^ 62 := Nat.div_le_div_left (by omega) (by positivity)
      _ < 2 ^ 63 := by norm_num
  have hn : isN t0 + isN t1 + isN t2 < NL := by
    unfold isN; cases Nat.beq t0 4 <;> cases Nat.beq t1 4 <;> cases Nat.beq t2 4 <;> decide
  have hF : ∀ r < 320, pack S NL (evL s tabs t0 t1 t2 r) < 2 ^ RB := fun r _ =>
    row_lt _ fun l hl => (evL_lt s hs tabs htabs t0 t1 t2 r l h0 h1 h2 hl).trans
      (Nat.pow_lt_pow_right (by norm_num) (by simp only [S]; norm_num))
  have hf0 : ∀ l < NL, (fun l => if l = isN t0 + isN t1 + isN t2 then D else 0) l < 2 ^ 63 := by
    intro l _
    simp only
    split_ifs
    · rw [D_eq]; norm_num
    · positivity
  have hes : ∀ j < P, (eventRows (eventX s tabs t0 t1 t2)).getD j 0 =
      pack S NL (evL s tabs t0 t1 t2 (V + j)) := by
    intro j hj
    rw [eventX_eq s tabs htabs, eventRows_getD _ hF j (by simp only [P] at hj; omega)]
  have hsol := solve_lanes _ (fun j => evL s tabs t0 t1 t2 (V + j)) _ D _ _ hf0 hes
    (fun j _ l hl => evL_lt s hs tabs htabs t0 t1 t2 _ l h0 h1 h2 hl) (by rw [D_eq]; norm_num) hlo hk
  rw [← shiftLeft_eq_pack _ hn] at hsol
  rw [sigmaTable_eq] at hok ⊢
  dsimp only at hok ⊢
  have hsol' := hsol hok
  exact solve_table (Nat.shiftLeft D (Nat.mul S (isN t0 + isN t1 + isN t2)))
    (eventRows (eventX s tabs t0 t1 t2)) D (lossW s t0 + lossW s t1 + lossW s t2)
    (D * D / (4 * D - (loopW s t0 + loopW s t1 + loopW s t2)))
    (fun l => if l = isN t0 + isN t1 + isN t2 then D else 0) (fun j => evL s tabs t0 t1 t2 (V + j))
    (fun j hj => (hsol' j hj).1) (fun j hj => (hsol' j hj).2)


/-! ## The real step -/

theorem rhoR_nonneg (s : St) (b f : ℕ) : 0 ≤ rhoR s b f := by
  unfold rhoR; split_ifs <;> positivity

theorem KR_nonneg (s : St) (t a f : ℕ) : 0 ≤ KR s t a f := by
  unfold KR; split_ifs <;> positivity

theorem KR_le_one (s : St) (hs : validSt s = true) (t a f : ℕ) : KR s t a f ≤ 1 := by
  unfold KR
  split_ifs
  · rw [div_le_one (by positivity)]
    exact_mod_cast lane_lawOf_le s hs t _
  · exact zero_le_one

theorem loopS_lt_one (s : St) (hs : validSt s = true) (σ : Fin 3 → CType) : loopS (KR s) σ < 1 := by
  have h : loopS (KR s) σ ≤ 1 / 4 * ∑ _c : Fin 3, (1 : ℝ) := by
    unfold loopS
    gcongr with c
    split
    · norm_num
    · exact KR_le_one s hs _ _ _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

theorem Tr_nonneg (tabs : List (ℕ × ℕ)) (σ : Fin 3 → CType) (p x g : ℕ) : 0 ≤ Tr tabs σ p x g := by
  unfold Tr; split_ifs <;> positivity

theorem Tr_perm (tabs : List (ℕ × ℕ)) (π : Equiv.Perm (Fin 3)) (σ : Fin 3 → CType) :
    Tr tabs (σ ∘ π) = Tr tabs σ := by
  funext p x g
  unfold Tr
  rw [cd_perm]

theorem sum_fin4_ite (t : ℕ) (ht : t ≤ 4) (L : ℕ → ℝ) :
    ∑ f : Fin 4, (if (f : ℕ) < t then L f else 0) = ∑ f ∈ Finset.range t, L f := by
  rw [Fin.sum_univ_eq_sum_range (fun f => if f < t then L f else 0) 4, ← Finset.sum_filter]
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem gmax_of_lt (t : ℕ) (ht : t < 4) : gmax t = t := by
  have : Nat.beq t 4 = false := by
    cases h : Nat.beq t 4
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
  simp only [gmax, this, Bool.cond_false]

/-- The child `c` of the multiset `σ` of type `t`, with siblings `a`, `b`: its event term read on
`Tr tabs`, as a double sum. -/
theorem evC_eq (s : St) (tabs : List (ℕ × ℕ)) (σ : Fin 3 → CType) (c : Fin 3) (t a b : ℕ)
    (ht : t ≤ 4) (hσ : σ c = dec t)
    (hcd : ∀ f : Fin 4, cd (Function.update σ c (some f)) = mcode a b f)
    (p x g : ℕ) (hx : x ≤ V) (hg : g ≤ 3) :
    evC V P (rhoR s) (KR s) (Tr tabs) σ c p x g =
      ∑ b' ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (gmax t),
        (lane (lawOf s t) (4 * b' + f) : ℝ) / 2 ^ 62 *
          ((tabR (findTab tabs (mcode a b f)) (min (p + b') P) (4 * x + g) : ℝ) / 2 ^ 62) := by
  have hTr : ∀ (f : Fin 4) (b' : ℕ), Tr tabs (Function.update σ c (some f)) (min (p + b') P) x g =
      (tabR (findTab tabs (mcode a b f)) (min (p + b') P) (4 * x + g) : ℝ) / 2 ^ 62 := by
    intro f b'
    unfold Tr
    rw [ite_eq_left ⟨Nat.min_le_right _ _, hx, hg⟩, hcd f]
  have hb4 : ∀ b' ∈ Finset.range (V + 1), b' ≤ V := fun b' hb' =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
  unfold evC
  rcases Nat.lt_or_ge t 4 with h4 | h4
  · have hσ' : σ c = some ⟨t, h4⟩ := by rw [hσ]; simp [dec, h4]
    rw [hσ', gmax_of_lt t h4]
    refine Finset.sum_congr rfl fun b' hb' => ?_
    simp only [hTr]
    rw [← sum_fin4_ite t h4.le]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hf3 : (f : ℕ) ≤ 3 := by have := f.isLt; omega
    by_cases hft : (f : ℕ) < t
    · rw [ite_eq_left (show f < (⟨t, h4⟩ : Fin 4) from hft), ite_eq_left hft]
      unfold KR
      rw [ite_eq_left ⟨hb4 b' hb', hf3⟩]
    · rw [ite_eq_right (show ¬ f < (⟨t, h4⟩ : Fin 4) from hft), ite_eq_right hft]
  · have ht4 : t = 4 := by omega
    subst ht4
    have hσ' : σ c = none := by rw [hσ]; simp [dec]
    rw [hσ', show gmax 4 = 4 from rfl]
    refine Finset.sum_congr rfl fun b' hb' => ?_
    simp only [hTr]
    rw [Fin.sum_univ_eq_sum_range (fun f => rhoR s b' f *
      ((tabR (findTab tabs (mcode a b f)) (min (p + b') P) (4 * x + g) : ℝ) / 2 ^ 62)) 4]
    refine Finset.sum_congr rfl fun f hf => ?_
    unfold rhoR
    rw [ite_eq_left ⟨hb4 b' hb', by simp only [Finset.mem_range] at hf; omega⟩]
    rfl

theorem chanL_real (s : St) (tabs : List (ℕ × ℕ)) (σ : Fin 3 → CType) (c : Fin 3) (t a b : ℕ)
    (ht : t ≤ 4) (hσ : σ c = dec t)
    (hcd : ∀ f : Fin 4, cd (Function.update σ c (some f)) = mcode a b f)
    (p : ℕ) (hp : p < P) (x g : ℕ) (hx : x ≤ V) (hg : g ≤ 3) :
    (chanL s tabs t a b (V + p) (4 * x + g) : ℝ) / 2 ^ 124 =
      evC V P (rhoR s) (KR s) (Tr tabs) σ c p x g := by
  rw [evC_eq s tabs σ c t a b ht hσ hcd p x g hx hg]
  unfold chanL
  simp only [corr_at _ (colv_zero _ _) _ p hp.le]
  push_cast
  simp_rw [Finset.sum_div]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' hb' => ?_
  refine Finset.sum_congr rfl fun f _ => ?_
  have hb : b' ≤ V := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
  have hc : colv (lawOf s t) f (V - b') = lane (lawOf s t) (4 * b' + f) := by
    unfold colv
    rw [ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hb]
  rw [hc]
  field_simp

theorem evL_real (s : St) (tabs : List (ℕ × ℕ)) (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ 4)
    (h2 : t2 ≤ 4) (p : ℕ) (hp : p < P) (x g : ℕ) (hx : x ≤ V) (hg : g ≤ 3) :
    (evL s tabs t0 t1 t2 (V + p) (4 * x + g) : ℝ) / 2 ^ 124 =
      ∑ c : Fin 3, evC V P (rhoR s) (KR s) (Tr tabs) (σOf t0 t1 t2) c p x g := by
  rw [Fin.sum_univ_three, ← chanL_real s tabs _ 0 t0 t1 t2 h0 (by simp [σOf])
      (cd_update0 t0 t1 t2 h1 h2) p hp x g hx hg,
    ← chanL_real s tabs _ 1 t1 t0 t2 h1 (by simp [σOf]) (cd_update1 t0 t1 t2 h0 h2) p hp x g hx hg,
    ← chanL_real s tabs _ 2 t2 t0 t1 h2 (by simp [σOf]) (cd_update2 t0 t1 t2 h0 h1) p hp x g hx hg]
  unfold evL
  push_cast
  ring

/-- The rounded step is at most the exact step on its own arguments: `⌊⌊num/D⌋ k/D⌋ ≤ num/(4 D - lp)`
with `k = ⌊D^2/(4 D - lp)⌋`. -/
theorem stepL_real (lo lp : ℕ) (hlp : lp ≤ 3 * 2 ^ 62) (f e : ℕ → ℕ) (l : ℕ) (E' : ℝ)
    (hE : (e l : ℝ) / 2 ^ 124 ≤ E') :
    (stepL D lo (D * D / (4 * D - lp)) f e l : ℝ) / 2 ^ 62 ≤
      (1 / 4 * ((upL f l : ℝ) / 2 ^ 62) + (lo : ℝ) / (4 * 2 ^ 62) * ((f l : ℝ) / 2 ^ 62) + 1 / 4 * E') /
        (1 - (lp : ℝ) / (4 * 2 ^ 62)) := by
  have hlpR : (lp : ℝ) ≤ 3 * 2 ^ 62 := by exact_mod_cast hlp
  have hlp0 : (0 : ℝ) ≤ lp := Nat.cast_nonneg lp
  have hsub : ((4 * D - lp : ℕ) : ℝ) = 4 * 2 ^ 62 - lp := by
    rw [Nat.cast_sub (by rw [D_eq]; omega), D_eq]; push_cast; ring
  have hdpos : (0 : ℝ) < 4 * 2 ^ 62 - lp := by linarith
  set k := D * D / (4 * D - lp) with hk
  have hkR : (k : ℝ) ≤ 2 ^ 124 / (4 * 2 ^ 62 - lp) := by
    rw [hk, ← hsub]
    calc ((D * D / (4 * D - lp) : ℕ) : ℝ) ≤ ((D * D : ℕ) : ℝ) / ((4 * D - lp : ℕ) : ℝ) := Nat.cast_div_le
      _ = 2 ^ 124 / ((4 * D - lp : ℕ) : ℝ) := by rw [D_eq]; norm_num
  set num := D * upL f l + lo * f l + e l with hnum
  have e1 : (stepL D lo k f e l : ℝ) ≤ (k : ℝ) * ((num : ℝ) / 2 ^ 62) / 2 ^ 62 := by
    have hW : (2 : ℕ) ^ W = 2 ^ 62 := rfl
    unfold stepL
    rw [hW]
    calc ((k * (num / 2 ^ 62) / 2 ^ 62 : ℕ) : ℝ) ≤ ((k * (num / 2 ^ 62) : ℕ) : ℝ) / ((2 ^ 62 : ℕ) : ℝ) :=
          Nat.cast_div_le
      _ ≤ (k : ℝ) * ((num : ℝ) / 2 ^ 62) / 2 ^ 62 := by
          push_cast
          gcongr
          · exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := num) (n := 2 ^ 62))
          all_goals norm_num
  set u : ℝ := (upL f l : ℝ) / 2 ^ 62 with hu
  set w : ℝ := (f l : ℝ) / 2 ^ 62 with hw
  have hu0 : 0 ≤ u := by positivity
  have hw0 : 0 ≤ w := by positivity
  have hE0 : 0 ≤ E' := le_trans (by positivity) hE
  have hN : (num : ℝ) / 2 ^ 124 ≤ u + (lo : ℝ) / 2 ^ 62 * w + E' := by
    have e : (num : ℝ) / 2 ^ 124 = u + (lo : ℝ) / 2 ^ 62 * w + (e l : ℝ) / 2 ^ 124 := by
      rw [hnum, hu, hw, D_eq]; push_cast; field_simp; ring
    rw [e]; linarith
  have hN0 : 0 ≤ u + (lo : ℝ) / 2 ^ 62 * w + E' := by positivity
  have hkd : (k : ℝ) / 2 ^ 62 ≤ 2 ^ 62 / (4 * 2 ^ 62 - lp) := by
    rw [div_le_iff₀ (by positivity)]
    calc (k : ℝ) ≤ 2 ^ 124 / (4 * 2 ^ 62 - lp) := hkR
      _ = 2 ^ 62 / (4 * 2 ^ 62 - lp) * 2 ^ 62 := by ring
  have hden4 : (1 - (lp : ℝ) / (4 * 2 ^ 62)) ≠ 0 := by
    have : (lp : ℝ) / (4 * 2 ^ 62) ≤ 3 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  calc (stepL D lo k f e l : ℝ) / 2 ^ 62
      ≤ (k : ℝ) * ((num : ℝ) / 2 ^ 62) / 2 ^ 62 / 2 ^ 62 := by gcongr
    _ = (k : ℝ) / 2 ^ 62 * ((num : ℝ) / 2 ^ 124) := by ring
    _ ≤ 2 ^ 62 / (4 * 2 ^ 62 - lp) * (u + (lo : ℝ) / 2 ^ 62 * w + E') :=
        mul_le_mul hkd hN (by positivity) (by positivity)
    _ = (1 / 4 * u + (lo : ℝ) / (4 * 2 ^ 62) * w + 1 / 4 * E') / (1 - (lp : ℝ) / (4 * 2 ^ 62)) := by
        have hd : (4 * 2 ^ 62 - (lp : ℝ)) ≠ 0 := hdpos.ne'
        have e2 : (1 - (lp : ℝ) / (4 * 2 ^ 62)) = (4 * 2 ^ 62 - lp) / (4 * 2 ^ 62) := by field_simp
        rw [e2]
        generalize (4 * 2 ^ 62 - (lp : ℝ)) = d at hd ⊢
        field_simp

/-- `up` of a table read in lanes. -/
theorem upV_lanes (F : ℕ → ℕ) (T : ℕ → ℕ → ℝ) (hT : ∀ x' ≤ V, ∀ g' ≤ 3, T x' g' = (F (4 * x' + g') : ℝ) / 2 ^ 62)
    (x g : ℕ) (hx : x ≤ V) (hg : g ≤ 3) :
    upV V T x g = (upL F (4 * x + g) : ℝ) / 2 ^ 62 := by
  have hV : V = 48 := rfl
  unfold upV upL
  by_cases h0 : x = 0
  · subst h0
    rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]; simp
  rw [ite_eq_right h0]
  by_cases h1 : x < V
  · rw [ite_eq_left h1, ite_eq_left (by omega), ite_eq_right (by omega), hT _ (by omega) _ hg,
      show 4 * (x - 1) + g = 4 * x + g - 4 by omega]
    simp
  · have hxV : x = V := by omega
    rw [ite_eq_right h1, ite_eq_left hxV, ite_eq_left (by omega), ite_eq_left (by omega),
      hT _ (by omega) _ hg, hT _ le_rfl _ hg, hxV, show 4 * (V - 1) + g = 4 * V + g - 4 by omega]
    push_cast; ring

theorem upV_Tr (tabs : List (ℕ × ℕ)) (σ : Fin 3 → CType) (p x g : ℕ) (hp : p ≤ P) (hx : x ≤ V)
    (hg : g ≤ 3) :
    upV V (fun x' g' => Tr tabs σ p x' g') x g =
      (upL (tabR (findTab tabs (cd σ)) p) (4 * x + g) : ℝ) / 2 ^ 62 := by
  exact upV_lanes _ _ (fun x' hx' g' hg' => by unfold Tr; rw [ite_eq_left ⟨hp, hx', hg'⟩]) x g hx hg

theorem lostS_sigOf (s : St) (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ 4) (h2 : t2 ≤ 4) :
    lostS (KR s) (σOf t0 t1 t2) = ((lossW s t0 + lossW s t1 + lossW s t2 : ℕ) : ℝ) / (4 * 2 ^ 62) := by
  unfold lostS
  rw [Fin.sum_univ_three]
  show 1 / 4 * ((match dec t0 with | none => (0 : ℝ) | some u => KR s u 0 u) +
    (match dec t1 with | none => (0 : ℝ) | some u => KR s u 0 u) +
    (match dec t2 with | none => (0 : ℝ) | some u => KR s u 0 u)) = _
  rw [lost_term s t0 h0, lost_term s t1 h1, lost_term s t2 h2]
  push_cast; ring

theorem loopS_sigOf (s : St) (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ 4) (h2 : t2 ≤ 4) :
    loopS (KR s) (σOf t0 t1 t2) = ((loopW s t0 + loopW s t1 + loopW s t2 : ℕ) : ℝ) / (4 * 2 ^ 62) := by
  unfold loopS
  rw [Fin.sum_univ_three]
  show 1 / 4 * ((match dec t0 with | none => (0 : ℝ) | some u => KR s u 1 u) +
    (match dec t1 with | none => (0 : ℝ) | some u => KR s u 1 u) +
    (match dec t2 with | none => (0 : ℝ) | some u => KR s u 1 u)) = _
  rw [loop_term s t0 h0, loop_term s t1 h1, loop_term s t2 h2]
  push_cast; ring

/-! ## The invariant of the closure -/

/-- Every table found is a table, and `Tr tabs` is a sub-solution of the R recursion. -/
def Good (s : St) (tabs : List (ℕ × ℕ)) : Prop :=
  (∀ c, TabOK (findTab tabs c)) ∧
    (∀ σ x g, Tr tabs σ 0 x g ≤ Wrec V P (rhoR s) (KR s) σ 0 x g) ∧
    ∀ σ p x g, Tr tabs σ (p + 1) x g ≤ wBody V P (rhoR s) (KR s) (Tr tabs) σ p x g

theorem good_nil (s : St) (hs : validSt s = true) : Good s [] := by
  have hz : ∀ σ p x g, Tr [] σ p x g = 0 := by
    intro σ p x g
    unfold Tr
    split_ifs
    · simp only [findTab, tabR_zero]; norm_num
    · rfl
  refine ⟨fun c => tabOK_zero, fun σ x g => ?_, fun σ p x g => ?_⟩
  · rw [hz, Wrec.eq_1]
    split_ifs <;> norm_num
  · rw [hz]
    exact wBody_nonneg V P _ _ (rhoR_nonneg s) (KR_nonneg s) σ (loopS_lt_one s hs σ) _
      (fun _ _ _ _ => le_of_eq (hz _ _ _ _).symm) p x g

theorem findTab_append_old (tabs : List (ℕ × ℕ)) (c t code : ℕ)
    (h : (∃ kv ∈ tabs, kv.1 = code) ∨ c ≠ code) :
    findTab (tabs ++ [(c, t)]) code = findTab tabs code := by
  rw [findTab_append]
  split_ifs with h1 h2
  · rfl
  · exact absurd h2 (h.resolve_left h1)
  · exact (findTab_of_not_mem tabs code h1).symm

theorem Tr_le_append (tabs : List (ℕ × ℕ)) (c t : ℕ) (σ : Fin 3 → CType) (p x g : ℕ) :
    Tr tabs σ p x g ≤ Tr (tabs ++ [(c, t)]) σ p x g := by
  by_cases h : (∃ kv ∈ tabs, kv.1 = cd σ) ∨ c ≠ cd σ
  · unfold Tr; rw [findTab_append_old tabs c t _ h]
  · simp only [not_or, not_not] at h
    have h0 : findTab tabs (cd σ) = 0 := findTab_of_not_mem tabs _ h.1
    refine le_trans (le_of_eq ?_) (Tr_nonneg _ σ p x g)
    unfold Tr
    rw [h0]
    split_ifs
    · simp only [tabR_zero]; norm_num
    · rfl

theorem mcode_sorted' (t0 t1 t2 : ℕ) (h01 : t1 ≤ t0) (h12 : t2 ≤ t1) :
    mcode t0 t1 t2 = 25 * t0 + 5 * t1 + t2 := by
  rw [mcode_swap12, mcode_swap23, mcode_sorted t0 t1 t2 h01 h12]

theorem isN_le (t : ℕ) : isN t ≤ 1 := by
  unfold isN; cases Nat.beq t 4 <;> simp

/-- The new table is below the step of the R recursion read on the tables after the append. -/
theorem step_new (s : St) (hs : validSt s = true) (tabs : List (ℕ × ℕ))
    (hT : ∀ c, TabOK (findTab tabs c)) (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ 4) (h2 : t2 ≤ 4)
    (hok : (sigmaTable s tabs t0 t1 t2).2 = true) (tabs' : List (ℕ × ℕ))
    (hnew : findTab tabs' (cd (σOf t0 t1 t2)) = (sigmaTable s tabs t0 t1 t2).1)
    (hle : ∀ σ p x g, Tr tabs σ p x g ≤ Tr tabs' σ p x g) (p x g : ℕ) :
    Tr tabs' (σOf t0 t1 t2) (p + 1) x g ≤
      wBody V P (rhoR s) (KR s) (Tr tabs') (σOf t0 t1 t2) p x g := by
  have hW0 : 0 ≤ wBody V P (rhoR s) (KR s) (Tr tabs') (σOf t0 t1 t2) p x g :=
    wBody_nonneg V P _ _ (rhoR_nonneg s) (KR_nonneg s) _ (loopS_lt_one s hs _) _
      (Tr_nonneg tabs') p x g
  by_cases hin : p + 1 ≤ P ∧ x ≤ V ∧ g ≤ 3
  swap
  · unfold Tr; rw [ite_eq_right hin]; exact hW0
  obtain ⟨hp, hx, hg⟩ := hin
  obtain ⟨_, _, hstep⟩ := sigmaTable_spec s hs tabs hT t0 t1 t2 h0 h1 h2 hok
  set Tn := (sigmaTable s tabs t0 t1 t2).1 with hTn
  have hl : 4 * x + g < NL := by simp only [V] at hx; simp only [NL]; omega
  have hTr' : ∀ q, q ≤ P → Tr tabs' (σOf t0 t1 t2) q x g = (tabR Tn q (4 * x + g) : ℝ) / 2 ^ 62 := by
    intro q hq
    unfold Tr
    rw [ite_eq_left ⟨hq, hx, hg⟩, hnew]
  have hlp : loopW s t0 + loopW s t1 + loopW s t2 ≤ 3 * 2 ^ 62 := by
    have := loopW_le s hs t0; have := loopW_le s hs t1; have := loopW_le s hs t2; omega
  have hE : (evL s tabs t0 t1 t2 (V + p) (4 * x + g) : ℝ) / 2 ^ 124 ≤
      ∑ c : Fin 3, evC V P (rhoR s) (KR s) (Tr tabs') (σOf t0 t1 t2) c p x g := by
    rw [evL_real s tabs t0 t1 t2 h0 h1 h2 p (by omega) x g hx hg]
    exact Finset.sum_le_sum fun c _ => evC_mono V P _ _ (rhoR_nonneg s) (KR_nonneg s) _ _ _ c p x g
      fun f' q _ => hle _ q x g
  rw [hTr' (p + 1) hp, hstep p (by omega) (4 * x + g) hl]
  refine (stepL_real _ _ hlp _ _ _ _ hE).trans (le_of_eq ?_)
  unfold wBody
  rw [upV_Tr tabs' _ p x g (by omega) hx hg, hnew, hTr' p (by omega),
    lostS_sigOf s t0 t1 t2 h0 h1 h2, loopS_sigOf s t0 t1 t2 h0 h1 h2]

theorem good_append (s : St) (hs : validSt s = true) (tabs : List (ℕ × ℕ)) (hg : Good s tabs)
    (t0 t1 t2 : ℕ) (h0 : t0 ≤ 4) (h1 : t1 ≤ t0) (h2 : t2 ≤ t1)
    (hok : (sigmaTable s tabs t0 t1 t2).2 = true) :
    Good s (tabs ++ [(25 * t0 + 5 * t1 + t2, (sigmaTable s tabs t0 t1 t2).1)]) := by
  obtain ⟨hT, hW0, hWs⟩ := hg
  have h1' : t1 ≤ 4 := h1.trans h0
  have h2' : t2 ≤ 4 := h2.trans h1'
  set code := 25 * t0 + 5 * t1 + t2 with hcode
  set Tn := (sigmaTable s tabs t0 t1 t2).1 with hTn
  have hle : ∀ σ p x g, Tr tabs σ p x g ≤ Tr (tabs ++ [(code, Tn)]) σ p x g :=
    fun σ p x g => Tr_le_append tabs code Tn σ p x g
  by_cases hfound : ∃ kv ∈ tabs, kv.1 = code
  · have heq : ∀ c', findTab (tabs ++ [(code, Tn)]) c' = findTab tabs c' := fun c' =>
      findTab_append_old tabs code Tn c' (by
        by_cases h : code = c'
        · left; rw [← h]; exact hfound
        · right; exact h)
    have hTr : Tr (tabs ++ [(code, Tn)]) = Tr tabs := by
      funext σ p x g; unfold Tr; rw [heq]
    refine ⟨fun c' => ?_, fun σ x g => ?_, fun σ p x g => ?_⟩
    · rw [heq]; exact hT c'
    · rw [hTr]; exact hW0 σ x g
    · rw [hTr]; exact hWs σ p x g
  have hcdc : cd (σOf t0 t1 t2) = code := by
    rw [cd_sigOf t0 t1 t2 h0 h1' h2', mcode_sorted' t0 t1 t2 h1 h2]
  have hnew : findTab (tabs ++ [(code, Tn)]) code = Tn := by
    rw [findTab_append, ite_eq_right hfound, ite_eq_left rfl]
  have hold : ∀ c', c' ≠ code → findTab (tabs ++ [(code, Tn)]) c' = findTab tabs c' :=
    fun c' h => findTab_append_old _ _ _ _ (Or.inr (Ne.symm h))
  have hTold : ∀ σ, cd σ ≠ code → Tr (tabs ++ [(code, Tn)]) σ = Tr tabs σ := by
    intro σ h; funext p x g; unfold Tr; rw [hold _ h]
  -- the multisets of the code `code`, sorted
  have hsort : ∀ σ, cd σ = code → ∃ π : Equiv.Perm (Fin 3), σ ∘ π = σOf t0 t1 t2 := by
    intro σ h
    obtain ⟨π, hπ⟩ := sort_exists σ
    refine ⟨π, ?_⟩
    have e0 : code / 25 = t0 := by omega
    have e1 : code / 5 % 5 = t1 := by omega
    have e2 : code % 5 = t2 := by omega
    rw [hπ, h, e0, e1, e2]
  obtain ⟨hTnOK, hrow0, -⟩ := sigmaTable_spec s hs tabs hT t0 t1 t2 h0 h1' h2' hok
  refine ⟨fun c' => ?_, fun σ x g => ?_, fun σ p x g => ?_⟩
  · by_cases h : c' = code
    · rw [h, hnew]; exact hTnOK
    · rw [hold c' h]; exact hT c'
  · by_cases h : cd σ = code
    · obtain ⟨π, hπ⟩ := hsort σ h
      have hN : numN σ = isN t0 + isN t1 + isN t2 := by
        rw [← numN_perm σ π, hπ, numN_sigOf t0 t1 t2 h0 h1' h2']
      rw [← Tr_perm _ π σ, hπ, Wrec.eq_1, hN]
      unfold Tr
      rw [hcdc, hnew]
      have := isN_le t0; have := isN_le t1; have := isN_le t2
      split_ifs with hin hxg
      · rw [hrow0 _ (by simp only [V] at hin; simp only [NL]; omega)]
        rw [ite_eq_left (by omega)]
        rw [D_eq]; norm_num
      · rw [hrow0 _ (by simp only [V] at hin; simp only [NL]; omega)]
        rw [ite_eq_right (by omega)]
        simp
      · norm_num
      · norm_num
    · rw [hTold σ h]
      exact hW0 σ x g
  · by_cases h : cd σ = code
    · obtain ⟨π, hπ⟩ := hsort σ h
      rw [← Tr_perm _ π σ, ← wBody_perm V P _ _ _ π (Tr_perm _ π) σ, hπ]
      exact step_new s hs tabs hT t0 t1 t2 h0 h1' h2' hok _ (hcdc ▸ hnew) hle p x g
    · rw [hTold σ h]
      exact (hWs σ p x g).trans (wBody_mono V P _ _ (rhoR_nonneg s) (KR_nonneg s) σ
        (loopS_lt_one s hs σ) _ _ p x g (fun x' g' => hle σ p x' g') fun c f' q _ => hle _ q x g)

theorem listFold_inv {α β : Type} (Q : α → Prop) (l : List β) (a : α) (f : α → β → α) (h0 : Q a)
    (hs : ∀ acc b, b ∈ l → Q acc → Q (f acc b)) : Q (listFold l a f) := by
  induction l generalizing a with
  | nil => exact h0
  | cons b l ih =>
    exact ih (f a b) (hs a b (List.mem_cons_self ..) h0) fun acc b' hb' => hs acc b' (List.mem_cons_of_mem _ hb')

theorem sigmaOrder_sorted : ∀ code ∈ sigmaOrder,
    code / 25 ≤ 4 ∧ code / 5 % 5 ≤ code / 25 ∧ code % 5 ≤ code / 5 % 5 ∧ code < 125 := by
  decide

theorem closure_good (s : St) (hs : validSt s = true) (hok : (closure s).2 = true) :
    Good s (closure s).1 := by
  unfold closure at hok ⊢
  revert hok
  refine listFold_inv (fun acc : List (ℕ × ℕ) × Bool => acc.2 = true → Good s acc.1) sigmaOrder
    ([], true) _ (fun _ => good_nil s hs) ?_
  intro acc code hcode hacc hok'
  obtain ⟨c0, c1, c2, c3⟩ := sigmaOrder_sorted code hcode
  have hok2 : (acc.2 && (sigmaTable s acc.1 (code / 25) (code / 5 % 5) (code % 5)).2) = true := hok'
  rw [Bool.and_eq_true] at hok2
  have he : code = 25 * (code / 25) + 5 * (code / 5 % 5) + code % 5 := by omega
  have := good_append s hs acc.1 (hacc hok2.1) (code / 25) (code / 5 % 5) (code % 5) c0 c1 c2 hok2.2
  rw [← he] at this
  exact this

/-- **The R closure of a valid height is below the R recursion**: the table of `NNN` (code `124`). -/
theorem closure_sound (s : St) (hs : validSt s = true) (hok : (closure s).2 = true) (p x g : ℕ)
    (hp : p ≤ P) (hx : x ≤ V) (hg : g ≤ 3) :
    (tabR (findTab (closure s).1 124) p (4 * x + g) : ℝ) / 2 ^ 62 ≤
      Wrec V P (rhoR s) (KR s) (fun _ => none) p x g := by
  obtain ⟨_, h0, hstep⟩ := closure_good s hs hok
  have := wrec_lower V P (rhoR s) (KR s) (rhoR_nonneg s) (KR_nonneg s) (loopS_lt_one s hs) _ h0 hstep
    (fun _ => none) p x g
  unfold Tr at this
  rw [ite_eq_left ⟨hp, hx, hg⟩] at this
  exact this

end FrogModel.D3.M1K
