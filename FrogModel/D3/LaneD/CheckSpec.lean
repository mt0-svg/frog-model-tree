module

public import FrogModel.D3.LaneD.Pack
public import FrogModel.D3.LaneD.K.Cover

@[expose] public section

/-!
# What a passing check says, in naturals

`failures L` is a sum of failure counts; `check L` says it is `0`, so every count is `0`. This file
names the pieces of `failures` (`lnDs`, `lnFs`, `lnSize`, ...), evaluates its loops as sums, and
reads off the tests of one deficit (`dTest_ok`), of one cdf entry (`cdfTest_ok`) and of the shape of
one row (`rowShape_ok`), and the tests of `covers`.
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.LaneD.K Finset

/-! ## The pieces of `failures` -/

def lnC (L : Line) : ConvCfg := ⟨L.E, L.GM, convSW L.E⟩

def lnNN (L : Line) : ℕ := Nat.add (Nat.add L.E L.GM) 1

def lnDen (L : Line) : ℕ :=
  Nat.shiftLeft (Nat.mul (fact (Nat.sub L.E 1)) (Nat.mul (fact (Nat.sub L.E 1)) (fact (Nat.sub L.E 1))))
    (Nat.add 156 (Nat.mul 2 (lnNN L)))

def lnX (L : Line) : ℕ := buildX (lnC L) L.inF

def lnQ (L : Line) : ℕ := sqQ (lnC L) (lnX L)

def lnOms (L : Line) : List ℕ := omRows (lnC L).SW (lnNN L) (Nat.sub (Nat.mul 3 L.E) 2)

def lnVA (L : Line) : List (ℕ × ℕ × List ℕ) :=
  L.famsA.map (fun p => (p.1, p.2, famA (lnC L) L.VM p.1 p.2 (lnOms L)
    (mkTab (lnC L) (lnX L) (lnQ L) L.E)))

def lnVB (L : Line) : List (ℕ × ℕ) :=
  L.famsB.map (fun f => (f, famB (lnC L) (Nat.shiftRight f 16) (lnOms L)
    (mkTab (lnC L) (lnX L) (lnQ L) (Nat.land f 65535))))

def lnS3 (L : Line) : List ℕ := cond (bit L.mask 2) (tl (tl (s3Laws WL L.E L.GM (getN L.inF 1)))) []

def lnS2 (L : Line) : List ℕ := cond (bit L.mask 0) (tl (tl (s2Laws WL L.E L.GM (getN L.inF 1)))) []

/-- The deficit term of `j` with the S2 law row `l` (packed). -/
def dTerm (L : Line) (j l : ℕ) : ℕ × ℕ :=
  deficitTerm L (lnC L) (lnNN L) (lnDen L) (lnVB L) (split (Nat.add (Nat.mul 2 WL) 8) (Nat.add L.E 1) l) j

/-- The failure count of the deficit `j`. -/
def dTest (L : Line) (j l : ℕ) : ℕ :=
  cond (doDef L j) (Nat.add (dTerm L j l).2 (Nat.add (bad (dTerm L j l).1 (slot 128 L.uD j))
    (bad (slot 128 L.uD j) (Nat.shiftLeft (slot 64 L.outD j) 76)))) 0

def lnDs (L : Line) : ℕ × List ℕ :=
  natFold (Nat.sub (Nat.add L.d1 1) L.d0) (0, dropN (Nat.sub L.d0 1) (lnS2 L))
    (fun i (st : ℕ × List ℕ) => (Nat.add st.1 (dTest L (Nat.add L.d0 i) (hd st.2)), tl st.2))

/-- The failure count of the cdf entry `(j, v)` (stored row `row`, previous row `prevRow`, S3 partial
sum `cum`). -/
def cdfT (L : Line) (j row prevRow v cum : ℕ) : ℕ :=
  cond (doCdf L j v) (cdfTerm L (lnC L) (lnDen L) (lnVA L) (slot 128 L.uD j) j v (slot 64 row v)
    (slot 64 prevRow v) (cond (Nat.beq v L.GM) one52 (slot 64 row (Nat.add v 1))) cum) 0

def vStep (L : Line) (j row prevRow : ℕ) (v : ℕ) (t : ℕ × ℕ × List ℕ) : ℕ × ℕ × List ℕ :=
  (Nat.add t.1 (cdfT L j row prevRow v (Nat.add t.2.1 (hd t.2.2))), Nat.add t.2.1 (hd t.2.2), tl t.2.2)

/-- The failure count of the row `j`: its entries and, with bit 2, its shape and the square root
witness. -/
def rowTest (L : Line) (j row prevRow s3l : ℕ) : ℕ :=
  Nat.add (natFold (Nat.add L.GM 1) (0, (0 : ℕ), split (Nat.add (Nat.mul 2 WL) 8) (Nat.add L.GM 2) s3l)
      (vStep L j row prevRow)).1
    (cond (bit L.mask 2) (Nat.add (shapeRow (Nat.add L.GM 1) row)
      (bad (Nat.shiftLeft (Nat.add (Nat.add L.a 2) j) 256)
        (Nat.mul 3 (Nat.mul (slot 256 L.sq j) (slot 256 L.sq j))))) 0)

def lnFs (L : Line) : ℕ × List ℕ × List ℕ × ℕ :=
  natFold (Nat.sub (Nat.add L.f1 1) L.f0)
    (0, dropN (Nat.sub L.f0 1) (lnS3 L), dropN L.f0 L.outF, getN L.outF (Nat.sub L.f0 1))
    (fun i (st : ℕ × List ℕ × List ℕ × ℕ) =>
      (Nat.add st.1 (rowTest L (Nat.add L.f0 i) (hd st.2.2.1) st.2.2.2 (hd st.2.1)), tl st.2.1,
        tl st.2.2.1, hd st.2.2.1))

def lnSize (L : Line) : ℕ :=
  bad (Nat.mul (Nat.shiftLeft (Nat.mul (fact (Nat.sub L.E 1)) (Nat.mul (fact (Nat.sub L.E 1))
    (fact (Nat.sub L.E 1)))) (Nat.add (Nat.mul 2 (lnNN L)) 172)) (Nat.pow 3 (Nat.mul 3 L.E)))
    (mask (lnC L).SW)

theorem failures_eq (L : Line) :
    failures L = Nat.add (Nat.add (Nat.add (lnDs L).1 (lnFs L).1) (lnSize L))
      (cond (bit L.mask 2) (Nat.add (shapeVec (Nat.add L.E 1) L.outD) (row0Bad L)) 0) := rfl

/-! ## Loops as sums -/

theorem st_natFold_eq_of {α : Type} (n : ℕ) (init : α) (f : ℕ → α → α) (σ : ℕ → α) (h0 : σ 0 = init)
    (hs : ∀ i < n, f i (σ i) = σ (i + 1)) : natFold n init f = σ n := by
  induction n with
  | zero => exact h0.symm
  | succ n ih =>
    show f n (natFold n init f) = σ (n + 1)
    rw [ih fun i hi => hs i (by omega), hs n (by omega)]

theorem st_shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem st_dropN_succ (n : ℕ) (l : List ℕ) : dropN (n + 1) l = tl (dropN n l) := rfl

theorem st_dropN_eq_drop (n : ℕ) (l : List ℕ) : dropN n l = l.drop n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [st_dropN_succ, ih]; simp [tl, List.tail_drop]

theorem st_getN_dropN (k i : ℕ) (l : List ℕ) : getN (dropN k l) i = getN l (k + i) := by
  rw [getN_eq, getN_eq, st_dropN_eq_drop, List.getD_eq_getElem?_getD, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

theorem st_hd_dropN (i : ℕ) (l : List ℕ) : hd (dropN i l) = getN l i := rfl

theorem lnDs_fst (L : Line) :
    (lnDs L).1 = ∑ i ∈ range (L.d1 + 1 - L.d0),
      dTest L (L.d0 + i) (getN (lnS2 L) (L.d0 - 1 + i)) := by
  have h := st_natFold_eq_of (Nat.sub (Nat.add L.d1 1) L.d0) (0, dropN (Nat.sub L.d0 1) (lnS2 L))
    (fun i (st : ℕ × List ℕ) => (Nat.add st.1 (dTest L (Nat.add L.d0 i) (hd st.2)), tl st.2))
    (fun i => (∑ i' ∈ range i, dTest L (L.d0 + i') (getN (lnS2 L) (L.d0 - 1 + i')),
      dropN i (dropN (L.d0 - 1) (lnS2 L)))) (by rw [sum_range_zero]; rfl) (fun i _ => by
        simp only [st_hd_dropN, st_getN_dropN, Prod.mk.injEq]
        exact ⟨(sum_range_succ _ _).symm, rfl⟩)
  exact congrArg Prod.fst h

theorem inner_eval (L : Line) (j row prevRow : ℕ) (l : List ℕ) (n : ℕ) :
    natFold n (0, (0 : ℕ), l) (vStep L j row prevRow) =
      (∑ v ∈ range n, cdfT L j row prevRow v (∑ x ∈ range (v + 1), getN l x),
        ∑ x ∈ range n, getN l x, dropN n l) := by
  refine st_natFold_eq_of _ _ _ (fun n => (∑ v ∈ range n, cdfT L j row prevRow v (∑ x ∈ range (v + 1), getN l x),
    ∑ x ∈ range n, getN l x, dropN n l)) (by rw [sum_range_zero, sum_range_zero]; rfl) fun v _ => ?_
  simp only [vStep, st_hd_dropN, Prod.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · rw [sum_range_succ, sum_range_succ (fun x => getN l x) v]
    rfl
  · rw [sum_range_succ]
    rfl

theorem lnFs_fst (L : Line) :
    (lnFs L).1 = ∑ i ∈ range (L.f1 + 1 - L.f0),
      rowTest L (L.f0 + i) (getN L.outF (L.f0 + i)) (getN L.outF (L.f0 + i - 1))
        (getN (lnS3 L) (L.f0 - 1 + i)) := by
  have h := st_natFold_eq_of (Nat.sub (Nat.add L.f1 1) L.f0)
    (0, dropN (Nat.sub L.f0 1) (lnS3 L), dropN L.f0 L.outF, getN L.outF (Nat.sub L.f0 1))
    (fun i (st : ℕ × List ℕ × List ℕ × ℕ) =>
      (Nat.add st.1 (rowTest L (Nat.add L.f0 i) (hd st.2.2.1) st.2.2.2 (hd st.2.1)), tl st.2.1,
        tl st.2.2.1, hd st.2.2.1))
    (fun i => (∑ i' ∈ range i, rowTest L (L.f0 + i') (getN L.outF (L.f0 + i'))
        (getN L.outF (L.f0 + i' - 1)) (getN (lnS3 L) (L.f0 - 1 + i')),
      dropN i (dropN (L.f0 - 1) (lnS3 L)), dropN i (dropN L.f0 L.outF), getN L.outF (L.f0 + i - 1)))
    (by rw [sum_range_zero]; rfl) (fun i _ => by
        simp only [st_hd_dropN, st_getN_dropN, Prod.mk.injEq]
        refine ⟨(sum_range_succ _ _).symm, rfl, rfl, by congr 1⟩)
  exact congrArg Prod.fst h

/-! ## The tests of a passing check -/

theorem st_sum_zero_of {n : ℕ} {f : ℕ → ℕ} (h : ∑ i ∈ range n, f i = 0) (i : ℕ) (hi : i < n) : f i = 0 :=
  (sum_eq_zero_iff.mp h) i (mem_range.mpr hi)

theorem check_parts (L : Line) (h : check L = true) :
    (lnDs L).1 = 0 ∧ (lnFs L).1 = 0 ∧ lnSize L = 0 ∧
      (bit L.mask 2 = true → shapeVec (L.E + 1) L.outD = 0 ∧ row0Bad L = 0) := by
  have h0 : failures L = 0 := Nat.eq_of_beq_eq_true h
  rw [failures_eq] at h0
  simp only [Nat.add_eq] at h0
  refine ⟨by omega, by omega, by omega, fun hb => ?_⟩
  rw [hb, Bool.cond_true] at h0
  constructor <;> omega

/-- The tests of the deficit `j` (`d0 ≤ j ≤ d1`, checked by the part). -/
theorem dTest_ok (L : Line) (h : check L = true) (hd0 : 1 ≤ L.d0) (j : ℕ) (hj0 : L.d0 ≤ j) (hj1 : j ≤ L.d1)
    (hdo : doDef L j = true) :
    (dTerm L j (getN (lnS2 L) (j - 1))).2 = 0 ∧
      (dTerm L j (getN (lnS2 L) (j - 1))).1 ≤ slot 128 L.uD j ∧
      slot 128 L.uD j ≤ slot 64 L.outD j * 2 ^ 76 := by
  have h1 := (check_parts L h).1
  rw [lnDs_fst] at h1
  have h2 := st_sum_zero_of h1 (j - L.d0) (by omega)
  rw [show L.d0 + (j - L.d0) = j by omega, show L.d0 - 1 + (j - L.d0) = j - 1 by omega] at h2
  unfold dTest at h2
  rw [hdo, Bool.cond_true] at h2
  simp only [Nat.add_eq] at h2
  refine ⟨by omega, (bad_eq_zero _ _).mp (by omega), ?_⟩
  have h3 := (bad_eq_zero _ _).mp (show bad (slot 128 L.uD j) (Nat.shiftLeft (slot 64 L.outD j) 76) = 0
    by omega)
  rwa [st_shl_eq] at h3

/-- The row test of the row `j` (`f0 ≤ j ≤ f1`). -/
theorem rowTest_ok (L : Line) (h : check L = true) (hf0 : 1 ≤ L.f0) (j : ℕ) (hj0 : L.f0 ≤ j) (hj1 : j ≤ L.f1) :
    rowTest L j (getN L.outF j) (getN L.outF (j - 1)) (getN (lnS3 L) (j - 1)) = 0 := by
  have h1 := (check_parts L h).2.1
  rw [lnFs_fst] at h1
  have h2 := st_sum_zero_of h1 (j - L.f0) (by omega)
  rwa [show L.f0 + (j - L.f0) = j by omega, show L.f0 - 1 + (j - L.f0) = j - 1 by omega] at h2

/-- The shape of the row `j` and the square root witness, with bit 2. -/
theorem rowShape_ok (L : Line) (h : check L = true) (hf0 : 1 ≤ L.f0) (j : ℕ) (hj0 : L.f0 ≤ j) (hj1 : j ≤ L.f1)
    (hb : bit L.mask 2 = true) :
    shapeRow (L.GM + 1) (getN L.outF j) = 0 ∧
      (L.a + 2 + j) * 2 ^ 256 ≤ 3 * (slot 256 L.sq j * slot 256 L.sq j) := by
  have h2 := rowTest_ok L h hf0 j hj0 hj1
  unfold rowTest at h2
  rw [hb, Bool.cond_true] at h2
  simp only [Nat.add_eq] at h2
  refine ⟨by omega, ?_⟩
  have h3 := (bad_eq_zero _ _).mp (show bad (Nat.shiftLeft (L.a + 2 + j) 256)
    (Nat.mul 3 (Nat.mul (slot 256 L.sq j) (slot 256 L.sq j))) = 0 by omega)
  rwa [st_shl_eq, Nat.mul_eq, Nat.mul_eq] at h3

/-- The test of the cdf entry `(j, v)` (`f0 ≤ j ≤ f1`, `v ≤ GM`, checked by the part). -/
theorem cdfTest_ok (L : Line) (h : check L = true) (hf0 : 1 ≤ L.f0) (j : ℕ) (hj0 : L.f0 ≤ j) (hj1 : j ≤ L.f1)
    (v : ℕ) (hv : v ≤ L.GM) (hdo : doCdf L j v = true) :
    cdfTerm L (lnC L) (lnDen L) (lnVA L) (slot 128 L.uD j) j v (slot 64 (getN L.outF j) v)
      (slot 64 (getN L.outF (j - 1)) v)
      (cond (Nat.beq v L.GM) one52 (slot 64 (getN L.outF j) (v + 1)))
      (∑ x ∈ range (v + 1), getN (split (2 * WL + 8) (L.GM + 2) (getN (lnS3 L) (j - 1))) x) = 0 := by
  have h2 := rowTest_ok L h hf0 j hj0 hj1
  unfold rowTest at h2
  rw [inner_eval] at h2
  simp only [Nat.add_eq] at h2
  have h3 := st_sum_zero_of (show ∑ v ∈ range (L.GM + 1), cdfT L j (getN L.outF j) (getN L.outF (j - 1)) v
    (∑ x ∈ range (v + 1), getN (split (2 * WL + 8) (L.GM + 2) (getN (lnS3 L) (j - 1))) x) = 0 by
      simp only [Nat.mul_eq] at h2 ⊢; omega) v (by omega)
  unfold cdfT at h3
  rwa [hdo, Bool.cond_true] at h3

/-! ## The tests of `covers` -/

theorem st_allN_spec (n : ℕ) (f : ℕ → Bool) (h : allN n f = true) (i : ℕ) (hi : i < n) : f i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have h' : (allN n f && f n) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ih h'.1 hi
    · exact hi ▸ h'.2

theorem st_inRange_spec (lo hi j : ℕ) (h : inRange lo hi j = true) : lo ≤ j ∧ j ≤ hi := by
  unfold inRange at h
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
  exact h

/-- What `covers` gives, for `1 ≤ j ≤ E` and `v ≤ GM`. -/
theorem covers_spec (L : Line) (ps : List Part) (h : covers L ps = true) :
    (∀ j, 1 ≤ j → j ≤ L.E → ∃ p ∈ ps, p.d0 ≤ j ∧ j ≤ p.d1 ∧ doDef (L.withPart p) j = true) ∧
    (∀ j, 1 ≤ j → j ≤ L.E → ∃ p ∈ ps, p.f0 ≤ j ∧ j ≤ p.f1 ∧ bit p.mask 2 = true) ∧
    (∀ j, 1 ≤ j → j ≤ L.E → ∀ v ≤ L.GM, ∃ p ∈ ps, p.f0 ≤ j ∧ j ≤ p.f1 ∧
      doCdf (L.withPart p) j v = true) ∧
    (∃ p ∈ ps, bit p.mask 2 = true) ∧ (∀ p ∈ ps, 1 ≤ p.d0 ∧ 1 ≤ p.f0) := by
  unfold covers at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hrow : ∀ j, 1 ≤ j → j ≤ L.E → _ := fun j hj1 hjE => by
    have := st_allN_spec _ _ h1 (j - 1) (by omega)
    simp only [Nat.add_eq, show j - 1 + 1 = j by omega, Bool.and_eq_true] at this
    exact this
  refine ⟨fun j hj1 hjE => ?_, fun j hj1 hjE => ?_, fun j hj1 hjE v hv => ?_, ?_, ?_⟩
  · obtain ⟨p, hp, hpj⟩ := List.any_eq_true.mp (hrow j hj1 hjE).1.1
    rw [Bool.and_eq_true] at hpj
    have := st_inRange_spec _ _ _ hpj.1
    exact ⟨p, hp, this.1, this.2, hpj.2⟩
  · obtain ⟨p, hp, hpj⟩ := List.any_eq_true.mp (hrow j hj1 hjE).1.2
    rw [Bool.and_eq_true] at hpj
    have := st_inRange_spec _ _ _ hpj.1
    exact ⟨p, hp, this.1, this.2, hpj.2⟩
  · have := st_allN_spec _ _ (hrow j hj1 hjE).2 v (by show v < L.GM + 1; omega)
    obtain ⟨p, hp, hpj⟩ := List.any_eq_true.mp this
    rw [Bool.and_eq_true] at hpj
    have := st_inRange_spec _ _ _ hpj.1
    exact ⟨p, hp, this.1, this.2, hpj.2⟩
  · obtain ⟨p, hp, hpj⟩ := List.any_eq_true.mp h2
    exact ⟨p, hp, hpj⟩
  · intro p hp
    have := List.all_eq_true.mp h3 p hp
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at this
    exact this

end FrogModel.D3.LaneD
