module

public import FrogModel.D3.LaneD.Pack

@[expose] public section

/-!
# The end-configuration sums of the kernel checker

`FrogModel.D3.LaneD.K.Conv` evaluates the main terms of the bounds `A_F` and `B_F` of Lemma 11.3 (2)
of the paper (`boundA`, `boundB` of the interface) exactly, as packed naturals. This file states and
proves what each step computes:

* the table `X` of the weights `xv e g = (E - 1)!/e! (r(e, g) - r(e, g - 1))` (`buildX_eq`), its square
  `Q` (`sqQ_eq`), the rows `rT J M s` of `X_J Q` (`prodR_eq`), their prefix sums, and the tables of
  `M! rT` (`mkTab_R`, `mkTab_PR`);
* the weights `om NN M n = C(n, M) 4^(NN - n)` (`omRows_eq` of `Pack`);
* one envelope unit (`envUnit_spec`): the vector over `q` of the envelope sum `envS` of one `M`, by
  the unimodality of `om NN M` (`envS_decomp`);
* the families (`famB_eq`, `famA_eq`) and the real values (`boundB_main`, `boundA_main`): the main
  term of `boundB` (or `boundA`) is the slot of the family over `Den = (E - 1)!^3 2^(156 + 2 NN)`.

Every slot stays below `2^SW` under the checker's size guard (`Guard`) and the shape of the input
rows (`RowsOK`).
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.Iface FrogModel.D3.LaneD.K Finset

/-! ## The objects -/

/-- The stored value of row `e` at `g` (at `2^-52`). -/
def rv (rows : List ℕ) (e g : ℕ) : ℕ := slot 64 (getN rows e) g

/-- The input rows `e ≤ E` are at most `2^52` and nondecreasing on `0..GM`. -/
def RowsOK (E GM : ℕ) (rows : List ℕ) : Prop :=
  (∀ e ≤ E, ∀ g ≤ GM, rv rows e g ≤ 2 ^ 52) ∧ ∀ e ≤ E, ∀ g < GM, rv rows e g ≤ rv rows e (g + 1)

/-- The size guard of the checker. -/
def Guard (c : ConvCfg) : Prop :=
  (c.E - 1).factorial ^ 3 * 2 ^ (2 * c.NN + 172) * 3 ^ (3 * c.E) < 2 ^ c.SW

/-- The weight `x_e(g)`: the pseudo-law of row `e` at `2^-52` times `(E - 1)!/e!` (`e < E`, `g ≤ GM`). -/
def xv (E GM : ℕ) (rows : List ℕ) (e g : ℕ) : ℕ :=
  if e < E ∧ g ≤ GM then
    (E - 1).factorial / e.factorial * (rv rows e g - if g = 0 then 0 else rv rows e (g - 1))
  else 0

/-- Entry `(M, s)` of `Q = X^2`. -/
def q2 (E GM : ℕ) (rows : List ℕ) (M s : ℕ) : ℕ :=
  ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
    if e1 + e2 = M ∧ g1 + g2 = s then xv E GM rows e1 g1 * xv E GM rows e2 g2 else 0

/-- Entry `(M, s)` of `X_J X X` (the first factor on the rows `e0 < J`). -/
def rT (E GM J : ℕ) (rows : List ℕ) (M s : ℕ) : ℕ :=
  ∑ e0 ∈ range J, ∑ e1 ∈ range E, ∑ e2 ∈ range E,
    ∑ g0 ∈ range (GM + 1), ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
      if e0 + e1 + e2 = M ∧ g0 + g1 + g2 = s then
        xv E GM rows e0 g0 * xv E GM rows e1 g1 * xv E GM rows e2 g2
      else 0

/-- The prefix sums of `rT` along `s`. -/
def prT (E GM J : ℕ) (rows : List ℕ) (M s : ℕ) : ℕ := ∑ s' ∈ range (s + 1), rT E GM J rows M s'

/-- `omega'(n, M) = C(n, M) 4^(NN - n)`. -/
def om (NN M n : ℕ) : ℕ := n.choose M * 4 ^ (NN - n)

/-- The envelope weight at `s`: the largest `omega'(n, M)` over `n ∈ [q + s, top]` (`0` if empty). -/
def envW (NN M q s top : ℕ) : ℕ := (Icc (q + s) top).sup (om NN M)

/-- The envelope sum of one `M` at `q` with the cut `sh` on `s` and `nh` on `n = q + s`:
`sum over s ≤ sh with q + s ≤ nh of envW(q, s, min(q + sh, nh)) Rv(s)`. -/
def envS (NN M q sh nh : ℕ) (Rv : ℕ → ℕ) : ℕ :=
  ∑ s ∈ range (sh + 1), if q + s ≤ nh then envW NN M q s (min (q + sh) nh) * Rv s else 0

/-- The denominator of the main terms: `(E - 1)!^3 2^(156 + 2 NN)`. -/
def Den (c : ConvCfg) : ℕ := (c.E - 1).factorial ^ 3 * 2 ^ (156 + 2 * c.NN)

theorem om_le (NN M n : ℕ) (hn : n ≤ NN) : om NN M n ≤ 4 ^ NN := by
  unfold om
  calc n.choose M * 4 ^ (NN - n) ≤ 2 ^ n * 4 ^ (NN - n) :=
        Nat.mul_le_mul_right _ (Nat.choose_le_two_pow n M)
    _ ≤ 4 ^ n * 4 ^ (NN - n) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) n)
    _ = 4 ^ NN := by rw [← pow_add, Nat.add_sub_cancel' hn]

theorem om_le_succ (NN M n : ℕ) (hn : n < 4 * M / 3) (hnN : n < NN) : om NN M n ≤ om NN M (n + 1) :=
  om_up NN M n hn hnN

theorem om_succ_le (NN M n : ℕ) (hn : 4 * M / 3 ≤ n) (hnN : n < NN) : om NN M (n + 1) ≤ om NN M n :=
  om_down NN M n hn hnN

/-! ## Sizes of the tables -/

/-- The total weight `sum over e < E, g ≤ GM of x_e(g)`. -/
def Sx (E GM : ℕ) (rows : List ℕ) : ℕ := ∑ e ∈ range E, ∑ g ∈ range (GM + 1), xv E GM rows e g

theorem tele_rv (rows : List ℕ) (e n : ℕ) (hmono : ∀ g < n, rv rows e g ≤ rv rows e (g + 1)) :
    ∑ g ∈ range (n + 1), (rv rows e g - if g = 0 then 0 else rv rows e (g - 1)) = rv rows e n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih (fun g hg => hmono g (by omega)), ite_eq_right (Nat.succ_ne_zero n),
      Nat.add_sub_cancel]
    have := hmono n (by omega)
    omega

theorem xv_sum_le (E GM : ℕ) (rows : List ℕ) (hrows : RowsOK E GM rows) (e : ℕ) (he : e < E) :
    ∑ g ∈ Finset.range (GM + 1), xv E GM rows e g ≤ (E - 1).factorial / e.factorial * 2 ^ 52 := by
  have hx : ∀ g ∈ range (GM + 1), xv E GM rows e g =
      (E - 1).factorial / e.factorial * (rv rows e g - if g = 0 then 0 else rv rows e (g - 1)) := by
    intro g hg
    unfold xv
    rw [ite_eq_left (show e < E ∧ g ≤ GM from ⟨he, Nat.lt_succ_iff.1 (mem_range.1 hg)⟩)]
  rw [sum_congr rfl hx, ← mul_sum, tele_rv rows e GM (fun g hg => hrows.2 e he.le g hg)]
  exact Nat.mul_le_mul_left _ (hrows.1 e he.le GM le_rfl)

/-- The weight of the triple `e` at `s`: `sum over g0 + g1 + g2 = s of x_e0(g0) x_e1(g1) x_e2(g2)`. -/
def xs3 (E GM : ℕ) (rows : List ℕ) (e0 e1 e2 s : ℕ) : ℕ :=
  ∑ g0 ∈ range (GM + 1), ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
    if g0 + g1 + g2 = s then xv E GM rows e0 g0 * xv E GM rows e1 g1 * xv E GM rows e2 g2 else 0

theorem rT_reshape (E GM J : ℕ) (rows : List ℕ) (M s : ℕ) :
    rT E GM J rows M s = ∑ e0 ∈ range J, ∑ e1 ∈ range E, ∑ e2 ∈ range E,
      if e0 + e1 + e2 = M then xs3 E GM rows e0 e1 e2 s else 0 := by
  unfold rT xs3
  refine sum_congr rfl fun e0 _ => sum_congr rfl fun e1 _ => sum_congr rfl fun e2 _ => ?_
  by_cases h : e0 + e1 + e2 = M
  · rw [ite_eq_left h]
    simp only [h, true_and]
  · rw [ite_eq_right h]
    simp only [h, false_and, ite_false, sum_const_zero]

theorem sum_xs3 (E GM : ℕ) (rows : List ℕ) (e0 e1 e2 N : ℕ) (hN : 3 * GM < N) :
    ∑ s ∈ range N, xs3 E GM rows e0 e1 e2 s =
      (∑ g ∈ range (GM + 1), xv E GM rows e0 g) * (∑ g ∈ range (GM + 1), xv E GM rows e1 g) *
        (∑ g ∈ range (GM + 1), xv E GM rows e2 g) := by
  have hR : (∑ g ∈ range (GM + 1), xv E GM rows e0 g) * (∑ g ∈ range (GM + 1), xv E GM rows e1 g) *
        (∑ g ∈ range (GM + 1), xv E GM rows e2 g) = ∑ g0 ∈ range (GM + 1), ∑ g1 ∈ range (GM + 1),
        ∑ g2 ∈ range (GM + 1), xv E GM rows e0 g0 * xv E GM rows e1 g1 * xv E GM rows e2 g2 := by
    rw [sum_mul_sum, sum_mul]
    refine sum_congr rfl fun g0 _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun g1 _ => ?_
    rw [mul_sum]
  rw [hR]
  unfold xs3
  rw [sum_comm]
  refine sum_congr rfl fun g0 hg0 => ?_
  rw [sum_comm]
  refine sum_congr rfl fun g1 hg1 => ?_
  rw [sum_comm]
  refine sum_congr rfl fun g2 hg2 => ?_
  rw [mem_range] at hg0 hg1 hg2
  rw [sum_ite_eq, ite_eq_left (mem_range.2 (by omega))]

theorem multi3 (e0 e1 e2 : ℕ) :
    (e0 + e1 + e2).choose e0 * (e0 + e1 + e2 - e0).choose e1 *
      (e0.factorial * e1.factorial * e2.factorial) = (e0 + e1 + e2).factorial := by
  have h1 : e0 + e1 + e2 - e0 = e1 + e2 := by omega
  have h2 : e1 + e2 - e1 = e2 := by omega
  have A := Nat.choose_mul_factorial_mul_factorial (show e0 ≤ e0 + e1 + e2 by omega)
  have B := Nat.choose_mul_factorial_mul_factorial (show e1 ≤ e1 + e2 by omega)
  rw [h1] at A ⊢
  rw [h2] at B
  calc _ = (e0 + e1 + e2).choose e0 * e0.factorial *
        ((e1 + e2).choose e1 * e1.factorial * e2.factorial) := by ring
    _ = _ := by rw [B, A]

theorem term_id (f M e0 e1 e2 : ℕ) (hM : e0 + e1 + e2 = M) (h0 : e0.factorial ∣ f)
    (h1 : e1.factorial ∣ f) (h2 : e2.factorial ∣ f) :
    M.factorial * (f / e0.factorial * 2 ^ 52 * (f / e1.factorial * 2 ^ 52) * (f / e2.factorial * 2 ^ 52)) =
      f ^ 3 * 2 ^ 156 * (M.choose e0 * (M - e0).choose e1) := by
  subst hM
  have hpos : 0 < e0.factorial * e1.factorial * e2.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have ha := Nat.div_mul_cancel h0
  have hb := Nat.div_mul_cancel h1
  have hc := Nat.div_mul_cancel h2
  calc _ = (e0 + e1 + e2).factorial * (f / e0.factorial * e0.factorial) * (f / e1.factorial * e1.factorial) *
        (f / e2.factorial * e2.factorial) * 2 ^ 156 := by ring
    _ = (e0 + e1 + e2).factorial * f * f * f * 2 ^ 156 := by rw [ha, hb, hc]
    _ = f ^ 3 * 2 ^ 156 * ((e0 + e1 + e2).choose e0 * (e0 + e1 + e2 - e0).choose e1 *
        (e0.factorial * e1.factorial * e2.factorial)) := by rw [multi3]; ring
    _ = _ := by ring

theorem sum_range_le_of_zero (f : ℕ → ℕ) (n N : ℕ) (hz : ∀ k, n < k → f k = 0) :
    ∑ k ∈ range N, f k ≤ ∑ k ∈ range (n + 1), f k := by
  rcases le_total N (n + 1) with h | h
  · exact sum_le_sum_of_subset (range_subset_range.2 h)
  · rw [← sum_range_add_sum_Ico _ h,
      sum_eq_zero (s := Ico _ _) (fun k hk => hz k (by rw [mem_Ico] at hk; omega)), add_zero]

theorem tri_le (J E M : ℕ) :
    ∑ e0 ∈ range J, ∑ e1 ∈ range E, ∑ e2 ∈ range E,
      (if e0 + e1 + e2 = M then M.choose e0 * (M - e0).choose e1 else 0) ≤ 3 ^ M := by
  calc _ ≤ ∑ e0 ∈ range J, ∑ e1 ∈ range E, M.choose e0 * (M - e0).choose e1 := by
        refine sum_le_sum fun e0 _ => sum_le_sum fun e1 _ => ?_
        calc _ ≤ ∑ e2 ∈ range E, if M - e0 - e1 = e2 then M.choose e0 * (M - e0).choose e1 else 0 :=
              sum_le_sum fun e2 _ => by split_ifs <;> omega
          _ ≤ _ := by rw [sum_ite_eq]; split_ifs <;> omega
    _ = ∑ e0 ∈ range J, M.choose e0 * ∑ e1 ∈ range E, (M - e0).choose e1 := by simp only [mul_sum]
    _ ≤ ∑ e0 ∈ range J, M.choose e0 * 2 ^ (M - e0) := by
        refine sum_le_sum fun e0 _ => Nat.mul_le_mul_left _ ?_
        calc _ ≤ ∑ k ∈ range (M - e0 + 1), (M - e0).choose k :=
              sum_range_le_of_zero _ _ _ fun k hk => Nat.choose_eq_zero_of_lt hk
          _ = _ := Nat.sum_range_choose _
    _ ≤ ∑ e0 ∈ range (M + 1), M.choose e0 * 2 ^ (M - e0) :=
        sum_range_le_of_zero _ _ _ fun k hk => by rw [Nat.choose_eq_zero_of_lt hk, zero_mul]
    _ = 3 ^ M := by
        rw [show (3 : ℕ) = 1 + 2 by rfl, add_pow]
        refine sum_congr rfl fun k _ => ?_
        rw [one_pow, one_mul, mul_comm, Nat.cast_id]

theorem rT_total (E GM J : ℕ) (rows : List ℕ) (hrows : RowsOK E GM rows) (hJ : J ≤ E) (M : ℕ) :
    M.factorial * ∑ s ∈ Finset.range (3 * GM + 1), rT E GM J rows M s ≤
      (E - 1).factorial ^ 3 * 2 ^ 156 * 3 ^ M := by
  set X : ℕ → ℕ := fun e => ∑ g ∈ range (GM + 1), xv E GM rows e g with hX
  have h1 : ∑ s ∈ range (3 * GM + 1), rT E GM J rows M s = ∑ e0 ∈ range J, ∑ e1 ∈ range E,
      ∑ e2 ∈ range E, if e0 + e1 + e2 = M then X e0 * X e1 * X e2 else 0 := by
    simp only [rT_reshape]
    rw [sum_comm]
    refine sum_congr rfl fun e0 _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun e1 _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun e2 _ => ?_
    by_cases h : e0 + e1 + e2 = M
    · rw [ite_eq_left h, sum_congr rfl fun s _ => ite_eq_left h]
      exact sum_xs3 E GM rows e0 e1 e2 _ (by omega)
    · rw [ite_eq_right h]
      exact sum_eq_zero fun s _ => ite_eq_right h
  rw [h1, mul_sum]
  calc _ ≤ ∑ e0 ∈ range J, ∑ e1 ∈ range E, ∑ e2 ∈ range E, (E - 1).factorial ^ 3 * 2 ^ 156 *
        (if e0 + e1 + e2 = M then M.choose e0 * (M - e0).choose e1 else 0) := by
        refine sum_le_sum fun e0 he0 => ?_
        rw [mul_sum]
        refine sum_le_sum fun e1 he1 => ?_
        rw [mul_sum]
        refine sum_le_sum fun e2 he2 => ?_
        rw [mem_range] at he0 he1 he2
        by_cases h : e0 + e1 + e2 = M
        · rw [ite_eq_left h, ite_eq_left h,
            ← term_id ((E - 1).factorial) M e0 e1 e2 h (Nat.factorial_dvd_factorial (by omega))
              (Nat.factorial_dvd_factorial (by omega)) (Nat.factorial_dvd_factorial (by omega))]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul
            (xv_sum_le E GM rows hrows e0 (by omega)) (xv_sum_le E GM rows hrows e1 he1))
            (xv_sum_le E GM rows hrows e2 he2))
        · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]
    _ = (E - 1).factorial ^ 3 * 2 ^ 156 * ∑ e0 ∈ range J, ∑ e1 ∈ range E, ∑ e2 ∈ range E,
        (if e0 + e1 + e2 = M then M.choose e0 * (M - e0).choose e1 else 0) := by simp only [mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (tri_le J E M)

theorem conv_comm6 (A B C D X Y : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ x ∈ X, ∑ y ∈ Y, F a b c d x y =
      ∑ c ∈ C, ∑ d ∈ D, ∑ x ∈ X, ∑ y ∈ Y, ∑ a ∈ A, ∑ b ∈ B, F a b c d x y := by
  simp only [Finset.sum_comm (s := A)]
  simp only [Finset.sum_comm (s := B)]

theorem conv_q2_single (E GM : ℕ) (rows : List ℕ) (e s : ℕ) (hs : s ≤ GM) (e0 g0 : ℕ) :
    (∑ e' ∈ range (2 * E - 1), ∑ g' ∈ range (GM + 1),
      if e0 + e' = e ∧ g0 + g' = s then xv E GM rows e0 g0 * q2 E GM rows e' g' else 0) =
    ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
      if e0 + e1 + e2 = e ∧ g0 + g1 + g2 = s then
        xv E GM rows e0 g0 * xv E GM rows e1 g1 * xv E GM rows e2 g2 else 0 := by
  have step1 : ∀ e' g', (if e0 + e' = e ∧ g0 + g' = s then xv E GM rows e0 g0 * q2 E GM rows e' g' else 0) =
      ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
        if (e0 + e' = e ∧ g0 + g' = s) ∧ (e1 + e2 = e' ∧ g1 + g2 = g') then
          xv E GM rows e0 g0 * (xv E GM rows e1 g1 * xv E GM rows e2 g2) else 0 := by
    intro e' g'
    unfold q2
    by_cases h1 : e0 + e' = e ∧ g0 + g' = s
    · rw [ite_eq_left h1]
      simp only [Finset.mul_sum]
      refine sum_congr rfl fun e1 _ => sum_congr rfl fun e2 _ => sum_congr rfl fun g1 _ =>
        sum_congr rfl fun g2 _ => ?_
      by_cases h2 : e1 + e2 = e' ∧ g1 + g2 = g'
      · rw [ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
      · rw [ite_eq_right h2, ite_eq_right (fun h => h2 h.2), mul_zero]
    · rw [ite_eq_right h1]
      symm
      refine sum_eq_zero fun e1 _ => sum_eq_zero fun e2 _ => sum_eq_zero fun g1 _ =>
        sum_eq_zero fun g2 _ => ?_
      exact ite_eq_right (fun h => h1 h.1)
  rw [sum_congr rfl fun e' _ => sum_congr rfl fun g' _ => step1 e' g', conv_comm6]
  refine sum_congr rfl fun e1 he1 => sum_congr rfl fun e2 he2 => sum_congr rfl fun g1 _ =>
    sum_congr rfl fun g2 _ => ?_
  rw [mem_range] at he1 he2
  rw [sum_eq_single (e1 + e2), sum_eq_single (g1 + g2)]
  · by_cases h : e0 + e1 + e2 = e ∧ g0 + g1 + g2 = s
    · rw [ite_eq_left ⟨⟨by omega, by omega⟩, rfl, rfl⟩, ite_eq_left h, mul_assoc]
    · rw [ite_eq_right (fun h' => h ⟨by omega, by omega⟩), ite_eq_right h]
  · intro g' _ hg'
    exact ite_eq_right (fun h => hg' h.2.2.symm)
  · intro hn
    rw [mem_range] at hn
    exact ite_eq_right (fun h => by omega)
  · intro e' _ he'
    exact sum_eq_zero fun g' _ => ite_eq_right (fun h => he' h.2.1.symm)
  · intro hn
    rw [mem_range] at hn
    omega

theorem conv_q2_eq_rT (E GM J : ℕ) (rows : List ℕ) (e s : ℕ) (hs : s ≤ GM) :
    (∑ e0 ∈ Finset.range J, ∑ e' ∈ Finset.range (2 * E - 1), ∑ g0 ∈ Finset.range (GM + 1),
      ∑ g' ∈ Finset.range (GM + 1),
        if e0 + e' = e ∧ g0 + g' = s then xv E GM rows e0 g0 * q2 E GM rows e' g' else 0) =
      rT E GM J rows e s := by
  unfold rT
  refine sum_congr rfl fun e0 _ => ?_
  rw [Finset.sum_comm, sum_congr rfl fun g0 _ => conv_q2_single E GM rows e s hs e0 g0]
  exact Finset.sum_comm.trans (sum_congr rfl fun e1 _ => Finset.sum_comm)

theorem conv_ones_eq (f : ℕ → ℕ → ℕ) (n GM e s : ℕ) (he : e < n) (hs : s ≤ GM) :
    (∑ e1 ∈ Finset.range n, ∑ e2 ∈ Finset.range 1, ∑ g1 ∈ Finset.range (GM + 1),
      ∑ g2 ∈ Finset.range (GM + 1), if e1 + e2 = e ∧ g1 + g2 = s then f e1 g1 * 1 else 0) =
      ∑ s' ∈ Finset.range (s + 1), f e s' := by
  have he_mem : e ∈ Finset.range n := Finset.mem_range.2 he
  calc
    (∑ e1 ∈ Finset.range n, ∑ e2 ∈ Finset.range 1, ∑ g1 ∈ Finset.range (GM + 1),
      ∑ g2 ∈ Finset.range (GM + 1), if e1 + e2 = e ∧ g1 + g2 = s then f e1 g1 * 1 else 0)
    = (∑ e1 ∈ Finset.range n, ∑ g1 ∈ Finset.range (GM + 1),
      ∑ g2 ∈ Finset.range (GM + 1), if e1 + 0 = e ∧ g1 + g2 = s then f e1 g1 * 1 else 0) := by
      simp
    _ = (∑ e1 ∈ Finset.range n, ∑ g1 ∈ Finset.range (GM + 1),
      ∑ g2 ∈ Finset.range (GM + 1), if e1 = e ∧ g1 + g2 = s then f e1 g1 else 0) := by
      simp
    _ = (∑ g1 ∈ Finset.range (GM + 1), ∑ g2 ∈ Finset.range (GM + 1),
        if g1 + g2 = s then f e g1 else 0) := by
      have hsplit : ∀ e1, (∑ g1 ∈ Finset.range (GM + 1), ∑ g2 ∈ Finset.range (GM + 1),
          if e1 = e ∧ g1 + g2 = s then f e1 g1 else 0) =
          (if e1 = e then (∑ g1 ∈ Finset.range (GM + 1), ∑ g2 ∈ Finset.range (GM + 1),
            if g1 + g2 = s then f e1 g1 else 0) else 0) := by
        intro e1
        by_cases he1 : e1 = e
        · subst he1; simp
        · simp [he1]
      rw [Finset.sum_congr rfl (fun e1 _ => hsplit e1)]
      simp [Finset.sum_ite_eq, he_mem, eq_comm]
    _ = (∑ g1 ∈ Finset.range (GM + 1),
        if g1 ≤ s then f e g1 else 0) := by
      refine Finset.sum_congr rfl (fun g1 _ => ?_)
      by_cases hg1 : g1 ≤ s
      · have hg2_mem : s - g1 ∈ Finset.range (GM + 1) := by
          rw [Finset.mem_range]
          have hsub : s - g1 ≤ s := Nat.sub_le _ _
          omega
        have h_eq : (fun (g2 : ℕ) => if g1 + g2 = s then f e g1 else 0) =
            (fun g2 => if g2 = s - g1 then f e g1 else 0) := by
          ext g2
          by_cases hsum : g1 + g2 = s
          · have hg2 : g2 = s - g1 := by omega
            rw [ite_eq_left hsum, ite_eq_left hg2]
          · have hg2_ne : g2 ≠ s - g1 := by
              intro h; apply hsum; omega
            rw [ite_eq_right hsum, ite_eq_right hg2_ne]
        rw [h_eq]
        have hsum_eq : (∑ g2 ∈ Finset.range (GM + 1), if g2 = s - g1 then f e g1 else 0) =
            (∑ g2 ∈ Finset.range (GM + 1), if s - g1 = g2 then f e g1 else 0) := by
          simp [eq_comm]
        rw [hsum_eq]
        rw [Finset.sum_ite_eq (Finset.range (GM + 1)) (s - g1) (fun _ => f e g1)]
        simp [hg2_mem, hg1]
      · have hRHS : (if g1 ≤ s then f e g1 else 0) = 0 := by simp [hg1]
        rw [hRHS]
        apply Finset.sum_eq_zero
        intro g2 hg2
        rw [Finset.mem_range] at hg2
        have hne : g1 + g2 ≠ s := by omega
        simp [hne]
    _ = (∑ s' ∈ Finset.range (s + 1), f e s') := by
      rw [← Finset.sum_filter]
      have hfilter : (Finset.range (GM + 1)).filter (fun g1 => g1 ≤ s) = Finset.range (s + 1) := by
        ext g1
        constructor
        · intro h
          rcases Finset.mem_filter.1 h with ⟨hg1, hle⟩
          rw [Finset.mem_range]
          omega
        · intro h
          rw [Finset.mem_range] at h
          have hle : g1 ≤ s := by omega
          apply Finset.mem_filter.mpr
          constructor
          · rw [Finset.mem_range]; omega
          · exact hle
      rw [hfilter]

theorem conv_ones_le (f : ℕ → ℕ → ℕ) (n GM e s : ℕ) :
    (∑ e1 ∈ Finset.range n, ∑ e2 ∈ Finset.range 1, ∑ g1 ∈ Finset.range (GM + 1),
      ∑ g2 ∈ Finset.range (GM + 1), if e1 + e2 = e ∧ g1 + g2 = s then f e1 g1 * 1 else 0) ≤
      ∑ g ∈ Finset.range (GM + 1), f e g := by
  have h_inner (e1 g1 : ℕ) : (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e1 g1 else 0) ≤ f e1 g1 := by
    by_cases hg1 : g1 ≤ s
    · by_cases hg2 : s - g1 < GM + 1
      · have hmem : (s - g1) ∈ Finset.range (GM + 1) := by
          simp [hg2]
        have hsum : (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e1 g1 else 0) = f e1 g1 := by
          calc
            (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e1 g1 else 0)
            = (∑ g2 ∈ Finset.range (GM + 1), if g2 = s - g1 then f e1 g1 else 0) := by
              refine Finset.sum_congr rfl fun g2 hg2 => ?_
              by_cases h_eq : g1 + g2 = s
              · have h_eq2 : g2 = s - g1 := by omega
                have h_add : g1 + (s - g1) = s := Nat.add_sub_cancel' hg1
                simp [h_eq2, h_add]
              · have h_ne : g2 ≠ s - g1 := by
                  intro h_eq2
                  apply h_eq
                  omega
                simp [h_eq, h_ne]
            _ = f e1 g1 := by simp [hmem]
        rw [hsum]
      · have h_no_sol : ∀ g2, g2 ∈ Finset.range (GM + 1) → g1 + g2 ≠ s := by
          intro g2 hg2
          have hg2_lt : g2 < GM + 1 := Finset.mem_range.1 hg2
          have h_sub_ge : GM + 1 ≤ s - g1 := by omega
          have h_lt : g2 < s - g1 := Nat.lt_of_lt_of_le hg2_lt h_sub_ge
          have h_lt2 : g1 + g2 < g1 + (s - g1) := Nat.add_lt_add_left h_lt g1
          have h_eq : g1 + (s - g1) = s := Nat.add_sub_cancel' hg1
          rw [h_eq] at h_lt2
          omega
        have h_empty : (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e1 g1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro g2 hg2
          have h_ne := h_no_sol g2 hg2
          simp [h_ne]
        rw [h_empty]
        exact Nat.zero_le _
    · have h_no_sol : ∀ g2, g2 ∈ Finset.range (GM + 1) → g1 + g2 ≠ s := by
        intro g2 hg2
        omega
      have h_empty : (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e1 g1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro g2 hg2
        have h_ne := h_no_sol g2 hg2
        simp [h_ne]
      rw [h_empty]
      exact Nat.zero_le _
  calc
    (∑ e1 ∈ Finset.range n, ∑ e2 ∈ Finset.range 1, ∑ g1 ∈ Finset.range (GM + 1),
      ∑ g2 ∈ Finset.range (GM + 1), if e1 + e2 = e ∧ g1 + g2 = s then f e1 g1 * 1 else 0)
    = (∑ e1 ∈ Finset.range n, ∑ g1 ∈ Finset.range (GM + 1),
      ∑ e2 ∈ Finset.range 1, ∑ g2 ∈ Finset.range (GM + 1), if e1 + e2 = e ∧ g1 + g2 = s then f e1 g1 else 0) := by
      apply Finset.sum_congr rfl
      intro e1 h
      rw [Finset.sum_comm (s := Finset.range 1) (t := Finset.range (GM + 1))]
      simp
    _ = (∑ e1 ∈ Finset.range n, ∑ g1 ∈ Finset.range (GM + 1),
      ∑ g2 ∈ Finset.range (GM + 1), if e1 = e ∧ g1 + g2 = s then f e1 g1 else 0) := by
      simp
    _ ≤ (∑ g1 ∈ Finset.range (GM + 1), f e g1) := by
      rw [Finset.sum_comm (s := Finset.range n) (t := Finset.range (GM + 1))]
      refine Finset.sum_le_sum fun g1 _ => ?_
      by_cases he : e < n
      · have h_mem : e ∈ Finset.range n := by simp [he]
        calc
          (∑ e1 ∈ Finset.range n, ∑ g2 ∈ Finset.range (GM + 1), if e1 = e ∧ g1 + g2 = s then f e1 g1 else 0)
          = (∑ e1 ∈ Finset.range n, if e1 = e then (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e1 g1 else 0) else 0) := by
            refine Finset.sum_congr rfl fun e1 _ => ?_
            by_cases h_eq : e1 = e
            · simp [h_eq]
            · simp [h_eq]
          _ = (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e g1 else 0) := by
            calc
              (∑ e1 ∈ Finset.range n, if e1 = e then (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e1 g1 else 0) else 0)
              = (∑ e1 ∈ Finset.range n, if e = e1 then (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e1 g1 else 0) else 0) := by
                refine Finset.sum_congr rfl fun e1 _ => ?_
                simp [eq_comm]
              _ = (∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e g1 else 0) := by
                rw [Finset.sum_ite_eq (s := Finset.range n) (a := e) (b := fun e1 => ∑ g2 ∈ Finset.range (GM + 1), if g1 + g2 = s then f e1 g1 else 0)]
                simp [h_mem]
          _ ≤ f e g1 := h_inner e g1
      · have h_empty : e ∉ Finset.range n := by
          simp [he]
        have h_sum_zero : (∑ e1 ∈ Finset.range n, ∑ g2 ∈ Finset.range (GM + 1), if e1 = e ∧ g1 + g2 = s then f e1 g1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro e1 h1
          have h_ne : e1 ≠ e := by
            rw [Finset.mem_range] at h1
            omega
          simp [h_ne]
        rw [h_sum_zero]
        exact Nat.zero_le _
    _ = ∑ g ∈ Finset.range (GM + 1), f e g := rfl

theorem Sx_le (E GM : ℕ) (rows : List ℕ) (hrows : RowsOK E GM rows) :
    Sx E GM rows ≤ E * (E - 1).factorial * 2 ^ 52 := by
  dsimp [Sx]
  calc
    ∑ e ∈ range E, ∑ g ∈ range (GM + 1), xv E GM rows e g
        ≤ ∑ e ∈ range E, ((E - 1).factorial / e.factorial * 2 ^ 52) :=
      Finset.sum_le_sum fun e he => xv_sum_le E GM rows hrows e (Finset.mem_range.1 he)
    _ ≤ ∑ e ∈ range E, ((E - 1).factorial * 2 ^ 52) :=
      Finset.sum_le_sum fun e he =>
        Nat.mul_le_mul_right (2 ^ 52) (Nat.div_le_self ((E - 1).factorial) (e.factorial))
    _ = E * ((E - 1).factorial * 2 ^ 52) := by
      simp [Finset.sum_const, Finset.card_range]
    _ = E * (E - 1).factorial * 2 ^ 52 := by ring

theorem q2_le_sq (E GM : ℕ) (rows : List ℕ) (M s : ℕ) : q2 E GM rows M s ≤ Sx E GM rows ^ 2 := by
  have h_eq : (∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
      xv E GM rows e1 g1 * xv E GM rows e2 g2) = (Sx E GM rows) ^ 2 := by
    calc
      ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
          xv E GM rows e1 g1 * xv E GM rows e2 g2
      = ∑ e1 ∈ range E, ∑ e2 ∈ range E, (∑ g1 ∈ range (GM + 1), xv E GM rows e1 g1) * (∑ g2 ∈ range (GM + 1), xv E GM rows e2 g2) := by
        refine Finset.sum_congr rfl fun e1 _ => ?_
        refine Finset.sum_congr rfl fun e2 _ => ?_
        rw [← Finset.sum_mul_sum]
      _ = ∑ e1 ∈ range E, (∑ g1 ∈ range (GM + 1), xv E GM rows e1 g1) * (∑ e2 ∈ range E, ∑ g2 ∈ range (GM + 1), xv E GM rows e2 g2) := by
        refine Finset.sum_congr rfl fun e1 _ => ?_
        rw [← Finset.mul_sum]
      _ = (∑ e1 ∈ range E, ∑ g1 ∈ range (GM + 1), xv E GM rows e1 g1) * (∑ e2 ∈ range E, ∑ g2 ∈ range (GM + 1), xv E GM rows e2 g2) := by
        rw [← Finset.sum_mul]
      _ = (Sx E GM rows) ^ 2 := by rw [Sx, sq]
  unfold q2
  calc
    ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
      (if e1 + e2 = M ∧ g1 + g2 = s then xv E GM rows e1 g1 * xv E GM rows e2 g2 else 0)
    ≤ ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
        xv E GM rows e1 g1 * xv E GM rows e2 g2 := by
      refine Finset.sum_le_sum fun e1 _ => ?_
      refine Finset.sum_le_sum fun e2 _ => ?_
      refine Finset.sum_le_sum fun g1 _ => ?_
      refine Finset.sum_le_sum fun g2 _ => ?_
      split_ifs with h
      · rfl
      · exact Nat.zero_le _
    _ = (Sx E GM rows) ^ 2 := by rw [h_eq]

theorem conv_sum3_mul (s t u : Finset ℕ) (a b c : ℕ → ℕ) :
    ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, a i * b j * c k = (∑ i ∈ s, a i) * (∑ j ∈ t, b j) * ∑ k ∈ u, c k := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm

theorem conv_sum_ite_le (n : ℕ) (P : Prop) [Decidable P] (g X : ℕ) :
    ∑ s ∈ range n, (if P ∧ g = s then X else 0) ≤ X := by
  by_cases hP : P
  · simp only [hP, true_and]
    rw [Finset.sum_ite_eq]
    split_ifs <;> omega
  · simp [hP]

theorem rT_sum_le (E GM J : ℕ) (rows : List ℕ) (hJ : J ≤ E) (M n : ℕ) :
    ∑ s ∈ Finset.range n, rT E GM J rows M s ≤ Sx E GM rows ^ 3 := by
  unfold rT
  simp only [Finset.sum_comm (s := range n)]
  calc _ ≤ ∑ e0 ∈ range J, ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ g0 ∈ range (GM + 1),
          ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
            xv E GM rows e0 g0 * xv E GM rows e1 g1 * xv E GM rows e2 g2 := by
        refine Finset.sum_le_sum fun e0 _ => Finset.sum_le_sum fun e1 _ => Finset.sum_le_sum fun e2 _ =>
          Finset.sum_le_sum fun g0 _ => Finset.sum_le_sum fun g1 _ => Finset.sum_le_sum fun g2 _ => ?_
        exact conv_sum_ite_le _ _ _ _
    _ = ∑ e0 ∈ range J, ∑ e1 ∈ range E, ∑ e2 ∈ range E,
          (∑ g ∈ range (GM + 1), xv E GM rows e0 g) * (∑ g ∈ range (GM + 1), xv E GM rows e1 g) *
            ∑ g ∈ range (GM + 1), xv E GM rows e2 g := by
        simp only [conv_sum3_mul]
    _ = (∑ e ∈ range J, ∑ g ∈ range (GM + 1), xv E GM rows e g) * Sx E GM rows * Sx E GM rows :=
        conv_sum3_mul _ _ _ _ _ _
    _ ≤ Sx E GM rows * Sx E GM rows * Sx E GM rows := by
        refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
        exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hJ)
    _ = Sx E GM rows ^ 3 := by ring

theorem conv3_le (E GM J : ℕ) (rows : List ℕ) (hJ : J ≤ E) (e s : ℕ) :
    (∑ e0 ∈ Finset.range J, ∑ e' ∈ Finset.range (2 * E - 1), ∑ g0 ∈ Finset.range (GM + 1),
      ∑ g' ∈ Finset.range (GM + 1),
        if e0 + e' = e ∧ g0 + g' = s then xv E GM rows e0 g0 * q2 E GM rows e' g' else 0) ≤
      Sx E GM rows ^ 3 := by
  -- For each (e0, g0), the inner double sum over (e', g') has at most one nonzero term
  have h_inner_bound (e0 g0 : ℕ) :
      (∑ e' ∈ Finset.range (2 * E - 1), ∑ g' ∈ Finset.range (GM + 1),
        if e0 + e' = e ∧ g0 + g' = s then q2 E GM rows e' g' else 0) ≤ Sx E GM rows ^ 2 := by
    by_cases h_sol : ∃ e' ∈ Finset.range (2 * E - 1), ∃ g' ∈ Finset.range (GM + 1),
        e0 + e' = e ∧ g0 + g' = s
    · rcases h_sol with ⟨e', he', g', hg', ⟨he_eq, hg_eq⟩⟩
      have h_unique : ∀ (e'' g'' : ℕ), e'' ∈ Finset.range (2 * E - 1) → g'' ∈ Finset.range (GM + 1) →
          (e0 + e'' = e ∧ g0 + g'' = s) → e'' = e' ∧ g'' = g' := by
        intro e'' g'' he'' hg'' h
        rcases h with ⟨he2, hg2⟩
        have he''_eq : e'' = e' := by omega
        have hg''_eq : g'' = g' := by omega
        exact ⟨he''_eq, hg''_eq⟩
      have h_sum_eq : (∑ e' ∈ Finset.range (2 * E - 1), ∑ g' ∈ Finset.range (GM + 1),
          if e0 + e' = e ∧ g0 + g' = s then q2 E GM rows e' g' else 0) = q2 E GM rows e' g' := by
        calc
          (∑ e' ∈ Finset.range (2 * E - 1), ∑ g' ∈ Finset.range (GM + 1),
            if e0 + e' = e ∧ g0 + g' = s then q2 E GM rows e' g' else 0)
          = (∑ p ∈ (Finset.range (2 * E - 1)) ×ˢ (Finset.range (GM + 1)),
              if e0 + p.1 = e ∧ g0 + p.2 = s then q2 E GM rows p.1 p.2 else 0) := by
            simp [Finset.sum_product]
          _ = q2 E GM rows e' g' := by
            have h := Finset.sum_eq_single (f := fun (p : ℕ × ℕ) =>
              if e0 + p.1 = e ∧ g0 + p.2 = s then q2 E GM rows p.1 p.2 else 0)
              (e', g')
              (by
                intro p hp h_ne
                rcases Finset.mem_product.1 hp with ⟨hp1, hp2⟩
                have h_not_cond : ¬ (e0 + p.1 = e ∧ g0 + p.2 = s) := by
                  intro hc
                  rcases h_unique p.1 p.2 hp1 hp2 hc with ⟨h_eq1, h_eq2⟩
                  apply h_ne
                  ext <;> assumption
                simp [h_not_cond])
              (by
                intro h_not_mem
                exfalso
                apply h_not_mem
                exact Finset.mem_product.2 ⟨he', hg'⟩)
            simpa [he_eq, hg_eq] using h
      rw [h_sum_eq]
      exact q2_le_sq E GM rows e' g'
    · have h_all_zero : ∀ e' ∈ Finset.range (2 * E - 1), ∀ g' ∈ Finset.range (GM + 1),
          ¬ (e0 + e' = e ∧ g0 + g' = s) := by
        intro e' he' g' hg' h
        apply h_sol
        exact ⟨e', he', g', hg', h⟩
      have h_sum_zero : (∑ e' ∈ Finset.range (2 * E - 1), ∑ g' ∈ Finset.range (GM + 1),
          if e0 + e' = e ∧ g0 + g' = s then q2 E GM rows e' g' else 0) = 0 := by
        refine Finset.sum_eq_zero fun e' he' => ?_
        refine Finset.sum_eq_zero fun g' hg' => ?_
        simp [h_all_zero e' he' g' hg']
      rw [h_sum_zero]
      apply Nat.zero_le
  calc
    (∑ e0 ∈ Finset.range J, ∑ e' ∈ Finset.range (2 * E - 1), ∑ g0 ∈ Finset.range (GM + 1),
      ∑ g' ∈ Finset.range (GM + 1),
        if e0 + e' = e ∧ g0 + g' = s then xv E GM rows e0 g0 * q2 E GM rows e' g' else 0)
    = (∑ e0 ∈ Finset.range J, ∑ g0 ∈ Finset.range (GM + 1),
        xv E GM rows e0 g0 * (∑ e' ∈ Finset.range (2 * E - 1), ∑ g' ∈ Finset.range (GM + 1),
          if e0 + e' = e ∧ g0 + g' = s then q2 E GM rows e' g' else 0)) := by
      apply Finset.sum_congr rfl
      intro e0 hE0
      calc
        (∑ e' ∈ Finset.range (2 * E - 1), ∑ g0 ∈ Finset.range (GM + 1), ∑ g' ∈ Finset.range (GM + 1),
          if e0 + e' = e ∧ g0 + g' = s then xv E GM rows e0 g0 * q2 E GM rows e' g' else 0)
        = (∑ g0 ∈ Finset.range (GM + 1), ∑ e' ∈ Finset.range (2 * E - 1), ∑ g' ∈ Finset.range (GM + 1),
            if e0 + e' = e ∧ g0 + g' = s then xv E GM rows e0 g0 * q2 E GM rows e' g' else 0) := by
          rw [Finset.sum_comm]
        _ = (∑ g0 ∈ Finset.range (GM + 1), xv E GM rows e0 g0 * (∑ e' ∈ Finset.range (2 * E - 1), ∑ g' ∈ Finset.range (GM + 1),
            if e0 + e' = e ∧ g0 + g' = s then q2 E GM rows e' g' else 0)) := by
          refine Finset.sum_congr rfl fun g0 hg0 => ?_
          simp [Finset.mul_sum, mul_ite]
    _ ≤ (∑ e0 ∈ Finset.range J, ∑ g0 ∈ Finset.range (GM + 1),
        xv E GM rows e0 g0 * (Sx E GM rows ^ 2)) := by
      refine Finset.sum_le_sum fun e0 hE0 => ?_
      refine Finset.sum_le_sum fun g0 hg0 => ?_
      exact Nat.mul_le_mul_left _ (h_inner_bound e0 g0)
    _ = (∑ e0 ∈ Finset.range J, ∑ g0 ∈ Finset.range (GM + 1), xv E GM rows e0 g0) * (Sx E GM rows ^ 2) := by
      simp [Finset.sum_mul]
    _ ≤ (∑ e0 ∈ Finset.range E, ∑ g0 ∈ Finset.range (GM + 1), xv E GM rows e0 g0) * (Sx E GM rows ^ 2) := by
      refine Nat.mul_le_mul_right _ ?_
      refine Finset.sum_le_sum_of_subset ?_
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    _ = Sx E GM rows * (Sx E GM rows ^ 2) := rfl
    _ = Sx E GM rows ^ 3 := by ring


lemma conv_le_three_pow (n : ℕ) : n ≤ 3 ^ n := by
  induction' n with k ih
  · exact Nat.zero_le _
  · have hk : k + 1 ≤ 3 ^ k + 1 := Nat.add_le_add_right ih 1
    have hpow : 1 ≤ 3 ^ k := by
      simpa using Nat.one_le_pow' k 2
    have hk' : 3 ^ k + 1 ≤ 3 ^ (k + 1) := by
      calc
        3 ^ k + 1 ≤ 3 ^ k + 3 ^ k := Nat.add_le_add_left hpow _
        _ = 2 * 3 ^ k := by ring
        _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_right _ (by omega)
        _ = 3 ^ (k + 1) := by ring
    exact Nat.le_trans hk hk'


theorem guard_Sx (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c) :
    Sx c.E c.GM rows ^ 3 < 2 ^ c.SW := by
  have hE3 : c.E ≤ 3 ^ c.E := conv_le_three_pow c.E
  have hSx := Sx_le c.E c.GM rows hrows
  have hcube : Sx c.E c.GM rows ^ 3 ≤ (c.E * (c.E - 1).factorial * 2 ^ 52) ^ 3 :=
    Nat.pow_le_pow_left hSx 3
  have h_expand : (c.E * (c.E - 1).factorial * 2 ^ 52) ^ 3 =
      c.E ^ 3 * (c.E - 1).factorial ^ 3 * 2 ^ 156 := by
    calc
      (c.E * (c.E - 1).factorial * 2 ^ 52) ^ 3 = ((c.E * (c.E - 1).factorial) * 2 ^ 52) ^ 3 := by ring
      _ = (c.E * (c.E - 1).factorial) ^ 3 * (2 ^ 52) ^ 3 := by rw [mul_pow]
      _ = (c.E ^ 3 * (c.E - 1).factorial ^ 3) * (2 ^ 52) ^ 3 := by rw [mul_pow]
      _ = c.E ^ 3 * (c.E - 1).factorial ^ 3 * (2 ^ 52) ^ 3 := by ring
      _ = c.E ^ 3 * (c.E - 1).factorial ^ 3 * 2 ^ (52 * 3) := by rw [pow_mul]
      _ = c.E ^ 3 * (c.E - 1).factorial ^ 3 * 2 ^ 156 := by ring
  have hE3_cube : c.E ^ 3 ≤ (3 ^ c.E) ^ 3 := Nat.pow_le_pow_left hE3 3
  have hE3_final : c.E ^ 3 ≤ 3 ^ (3 * c.E) := by
    apply le_trans hE3_cube
    rw [← pow_mul, mul_comm]
  have h_2pow : 2 ^ 156 ≤ 2 ^ (2 * c.NN + 172) := by
    apply Nat.pow_le_pow_right (by omega)
    omega
  have h_mid1 : c.E ^ 3 * (c.E - 1).factorial ^ 3 ≤ 3 ^ (3 * c.E) * (c.E - 1).factorial ^ 3 :=
    Nat.mul_le_mul hE3_final (by rfl)
  have h_mid : c.E ^ 3 * (c.E - 1).factorial ^ 3 * 2 ^ 156 ≤
      3 ^ (3 * c.E) * (c.E - 1).factorial ^ 3 * 2 ^ (2 * c.NN + 172) :=
    Nat.mul_le_mul h_mid1 h_2pow
  have h_reorder : 3 ^ (3 * c.E) * (c.E - 1).factorial ^ 3 * 2 ^ (2 * c.NN + 172) =
      (c.E - 1).factorial ^ 3 * 2 ^ (2 * c.NN + 172) * 3 ^ (3 * c.E) := by ring
  calc
    Sx c.E c.GM rows ^ 3 ≤ (c.E * (c.E - 1).factorial * 2 ^ 52) ^ 3 := hcube
    _ = c.E ^ 3 * (c.E - 1).factorial ^ 3 * 2 ^ 156 := h_expand
    _ ≤ 3 ^ (3 * c.E) * (c.E - 1).factorial ^ 3 * 2 ^ (2 * c.NN + 172) := h_mid
    _ = (c.E - 1).factorial ^ 3 * 2 ^ (2 * c.NN + 172) * 3 ^ (3 * c.E) := h_reorder
    _ < 2 ^ c.SW := hG

theorem guard_four (c : ConvCfg) (hG : Guard c) : 4 ^ c.NN < 2 ^ c.SW := by
  have h2pos : 1 ≤ (2 : ℕ) := by norm_num
  have hfact_pos : 0 < (c.E - 1).factorial := Nat.factorial_pos _
  have hfact3_pos : 0 < (c.E - 1).factorial ^ 3 := pow_pos hfact_pos 3
  calc
    4 ^ c.NN = ((2 : ℕ) ^ 2) ^ c.NN := by norm_num
    _ = (2 : ℕ) ^ (2 * c.NN) := by rw [← pow_mul 2 2 c.NN]
    _ ≤ (2 : ℕ) ^ (2 * c.NN + 172) := by
      refine pow_le_pow_right' h2pos ?_
      exact Nat.le_add_right _ _
    _ ≤ (c.E - 1).factorial ^ 3 * (2 : ℕ) ^ (2 * c.NN + 172) :=
      Nat.le_mul_of_pos_left _ hfact3_pos
    _ ≤ (c.E - 1).factorial ^ 3 * (2 : ℕ) ^ (2 * c.NN + 172) * 3 ^ (3 * c.E) :=
      Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
    _ < 2 ^ c.SW := hG

theorem guard_rT (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c) (J : ℕ) (hJ : J ≤ c.E)
    (M : ℕ) (hM : M ≤ 3 * c.E) :
    4 ^ c.NN * ∑ s ∈ Finset.range (c.GM + 1), M.factorial * rT c.E c.GM J rows M s < 2 ^ c.SW := by
  have h_subset : Finset.range (c.GM + 1) ⊆ Finset.range (3 * c.GM + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have h_sum_le : ∑ s ∈ Finset.range (c.GM + 1), M.factorial * rT c.E c.GM J rows M s ≤
      M.factorial * ∑ s ∈ Finset.range (3 * c.GM + 1), rT c.E c.GM J rows M s := by
    calc
      ∑ s ∈ Finset.range (c.GM + 1), M.factorial * rT c.E c.GM J rows M s
          = M.factorial * ∑ s ∈ Finset.range (c.GM + 1), rT c.E c.GM J rows M s := by
        rw [Finset.mul_sum]
      _ ≤ M.factorial * ∑ s ∈ Finset.range (3 * c.GM + 1), rT c.E c.GM J rows M s :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset h_subset)
  have h_pow4 : (4 : ℕ) ^ c.NN = (2 : ℕ) ^ (2 * c.NN) := by
    calc
      (4 : ℕ) ^ c.NN = ((2 : ℕ) ^ 2) ^ c.NN := by norm_num
      _ = (2 : ℕ) ^ (2 * c.NN) := by rw [Nat.pow_mul]
  have h_pow_add : (2 : ℕ) ^ (2 * c.NN) * (2 : ℕ) ^ 156 = (2 : ℕ) ^ (2 * c.NN + 156) := by
    rw [Nat.pow_add]
  have h_exp_le : 2 * c.NN + 156 ≤ 2 * c.NN + 172 := by omega
  have h_pow_le : (2 : ℕ) ^ (2 * c.NN + 156) ≤ (2 : ℕ) ^ (2 * c.NN + 172) :=
    Nat.pow_le_pow_right (by omega) h_exp_le
  have h_pow3_le : (3 : ℕ) ^ M ≤ (3 : ℕ) ^ (3 * c.E) :=
    Nat.pow_le_pow_right (by omega) hM
  have h_core : (4 : ℕ) ^ c.NN * (2 : ℕ) ^ 156 * (3 : ℕ) ^ M ≤
      (2 : ℕ) ^ (2 * c.NN + 172) * (3 : ℕ) ^ (3 * c.E) := by
    calc
      (4 : ℕ) ^ c.NN * (2 : ℕ) ^ 156 * (3 : ℕ) ^ M
          = ((2 : ℕ) ^ (2 * c.NN)) * (2 : ℕ) ^ 156 * (3 : ℕ) ^ M := by rw [h_pow4]
      _ = ((2 : ℕ) ^ (2 * c.NN) * (2 : ℕ) ^ 156) * (3 : ℕ) ^ M := by ring
      _ = (2 : ℕ) ^ (2 * c.NN + 156) * (3 : ℕ) ^ M := by rw [h_pow_add]
      _ ≤ (2 : ℕ) ^ (2 * c.NN + 172) * (3 : ℕ) ^ M :=
        Nat.mul_le_mul_right _ h_pow_le
      _ ≤ (2 : ℕ) ^ (2 * c.NN + 172) * (3 : ℕ) ^ (3 * c.E) :=
        Nat.mul_le_mul_left _ h_pow3_le
  have h_mul_core : (c.E - 1).factorial ^ 3 * ((4 : ℕ) ^ c.NN * (2 : ℕ) ^ 156 * (3 : ℕ) ^ M) ≤
      (c.E - 1).factorial ^ 3 * ((2 : ℕ) ^ (2 * c.NN + 172) * (3 : ℕ) ^ (3 * c.E)) :=
    Nat.mul_le_mul_left _ h_core
  have h_total := rT_total c.E c.GM J rows hrows hJ M
  have h_final : 4 ^ c.NN * ∑ s ∈ Finset.range (c.GM + 1), M.factorial * rT c.E c.GM J rows M s <
      2 ^ c.SW := by
    calc
      4 ^ c.NN * ∑ s ∈ Finset.range (c.GM + 1), M.factorial * rT c.E c.GM J rows M s
          = (4 : ℕ) ^ c.NN * (∑ s ∈ Finset.range (c.GM + 1), M.factorial * rT c.E c.GM J rows M s) := rfl
      _ ≤ (4 : ℕ) ^ c.NN * (M.factorial * ∑ s ∈ Finset.range (3 * c.GM + 1), rT c.E c.GM J rows M s) :=
        Nat.mul_le_mul_left _ h_sum_le
      _ ≤ (4 : ℕ) ^ c.NN * ((c.E - 1).factorial ^ 3 * 2 ^ 156 * 3 ^ M) :=
        Nat.mul_le_mul_left _ h_total
      _ = (c.E - 1).factorial ^ 3 * ((4 : ℕ) ^ c.NN * 2 ^ 156 * 3 ^ M) := by ring
      _ ≤ (c.E - 1).factorial ^ 3 * ((2 : ℕ) ^ (2 * c.NN + 172) * (3 : ℕ) ^ (3 * c.E)) := h_mul_core
      _ = (c.E - 1).factorial ^ 3 * 2 ^ (2 * c.NN + 172) * 3 ^ (3 * c.E) := by ring
      _ < 2 ^ c.SW := hG
  exact h_final

/-! ## The loops of the checker -/

theorem natFold_step {α : Type} (n : ℕ) (init : α) (f : ℕ → α → α) :
    natFold (n + 1) init f = f n (natFold n init f) := rfl

theorem scaleFact_fold (l : List ℕ) (M : ℕ) :
    natFold M (([] : List ℕ), l, 1) (fun M (st : List ℕ × List ℕ × ℕ) =>
      (Nat.mul st.2.2 (hd st.2.1) :: st.1, tl st.2.1, Nat.mul st.2.2 (Nat.add M 1))) =
    (((List.range M).map fun i => i.factorial * l.getD i 0).reverse, l.drop M, M.factorial) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [natFold_step, ih]
    have hh : hd (l.drop M) = l.getD M 0 := by
      simp only [hd, List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Nat.mul_eq, hh]
    · simp only [tl, List.tail_drop]
    · simp only [Nat.mul_eq, Nat.add_eq, Nat.factorial_succ]
      ring

theorem scaleFact_getN (l : List ℕ) (M : ℕ) : getN (scaleFact l) M = M.factorial * getN l M := by
  have hs : scaleFact l = (List.range l.length).map fun i => i.factorial * l.getD i 0 := by
    unfold scaleFact
    rw [scaleFact_fold, List.reverse_reverse]
  rw [getN_eq, getN_eq, hs]
  by_cases hM : M < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hM)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using hM), List.getD_eq_default _ _ (by omega), mul_zero]

theorem splitAux_length (w d N : ℕ) (acc : List ℕ) : (splitAux w d N acc).length = 2 ^ d + acc.length := by
  induction d generalizing N acc with
  | zero =>
    show (N :: acc).length = 2 ^ 0 + acc.length
    simp only [List.length_cons, pow_zero]
    omega
  | succ d ih =>
    show (splitAux w d (Nat.land N (mask (Nat.mul (Nat.shiftLeft 1 d) w)))
      (splitAux w d (Nat.shiftRight N (Nat.mul (Nat.shiftLeft 1 d) w)) acc)).length = _
    rw [ih, ih, pow_succ]
    omega

theorem split_length (w n N : ℕ) : (split w n N).length = 2 ^ clog n := by
  unfold split
  rw [splitAux_length]
  rfl

theorem scaleFact_length (l : List ℕ) : (scaleFact l).length = l.length := by
  let step : ℕ → List ℕ × List ℕ × ℕ → List ℕ × List ℕ × ℕ :=
    fun M st => (Nat.mul st.2.2 (hd st.2.1) :: st.1, tl st.2.1, Nat.mul st.2.2 (Nat.add M 1))
  have h : ∀ n, ((natFold n ([], l, 1) step).1).length = n := by
    intro n
    induction' n with n ih
    · rfl
    · have h_eq : natFold (n + 1) ([], l, 1) step = step n (natFold n ([], l, 1) step) := rfl
      rw [h_eq]
      have h_proj : (step n (natFold n ([], l, 1) step)).1 =
        Nat.mul (natFold n ([], l, 1) step).2.2 (hd (natFold n ([], l, 1) step).2.1) :: (natFold n ([], l, 1) step).1 := rfl
      rw [h_proj]
      rw [List.length_cons, ih]
  unfold scaleFact
  simpa [step, List.length_reverse] using h l.length

theorem fold4_sum (n a0 : ℕ) (l1 l2 l3 : List ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ) :
    natFold n (a0, l1, l2, l3) (fun M (st : ℕ × List ℕ × List ℕ × List ℕ) =>
      (Nat.add st.1 (f M (hd st.2.1) (hd st.2.2.1) (hd st.2.2.2)), tl st.2.1, tl st.2.2.1, tl st.2.2.2)) =
    (a0 + ∑ M ∈ Finset.range n, f M (getN l1 M) (getN l2 M) (getN l3 M), dropN n l1, dropN n l2, dropN n l3) := by
  induction n generalizing a0 l1 l2 l3 with
  | zero =>
      simp [natFold, dropN, getN]
  | succ n ih =>
      have h_fold : natFold (n + 1) (a0, l1, l2, l3) (fun M (st : ℕ × List ℕ × List ℕ × List ℕ) =>
        (Nat.add st.1 (f M (hd st.2.1) (hd st.2.2.1) (hd st.2.2.2)), tl st.2.1, tl st.2.2.1, tl st.2.2.2)) =
        (fun M (st : ℕ × List ℕ × List ℕ × List ℕ) =>
          (Nat.add st.1 (f M (hd st.2.1) (hd st.2.2.1) (hd st.2.2.2)), tl st.2.1, tl st.2.2.1, tl st.2.2.2)) n
          (natFold n (a0, l1, l2, l3) (fun M (st : ℕ × List ℕ × List ℕ × List ℕ) =>
            (Nat.add st.1 (f M (hd st.2.1) (hd st.2.2.1) (hd st.2.2.2)), tl st.2.1, tl st.2.2.1, tl st.2.2.2))) := rfl
      have h_dropN_succ : ∀ (l : List ℕ), dropN (n + 1) l = tl (dropN n l) := by
        intro l; rfl
      rw [h_fold, h_dropN_succ l1, h_dropN_succ l2, h_dropN_succ l3]
      rw [Finset.sum_range_succ]
      rw [ih]
      simp [getN, add_assoc]

theorem envUnit_zero (c : ConvCfg) (sh M nh Ow O : ℕ) : envUnit c sh M nh Ow O 0 0 = 0 := by
  simp [envUnit, slot]

theorem pk2_rows (w S : ℕ) (f : ℕ → ℕ → ℕ) (m n J : ℕ) (hn : n ≤ S) (hf : ∀ e < m, ∀ g < n, f e g < 2 ^ w) :
    pk2 w S f m n &&& mask (J * (S * w)) = pk2 w S f (min m J) n := by
  rw [← pk_nest w S f m n, ← pk_nest w S f (min m J) n, and_mask, mul_comm J (S * w)]
  exact pk_mod (S * w) (fun e => pk w (f e) n) m J (fun e he =>
    lt_of_lt_of_le (pk_lt w (f e) n (hf e he))
      (Nat.pow_le_pow_right (by omega) (by rw [mul_comm S w]; exact Nat.mul_le_mul_left w hn)))

theorem pk2_ones (w S n : ℕ) (hw : 0 < w) : ones w n = pk2 w S (fun _ _ => 1) 1 n := by
  have hw1 : 1 ≤ w := Nat.one_le_of_lt hw
  have hw2 : 2 ≤ 2 ^ w := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw1
  calc
    ones w n = ((2 ^ w) ^ n - 1) / ((2 ^ w) - 1) := by
      simp [ones, mask, Nat.shiftLeft_eq_mul_pow, ← pow_mul 2 w n]
    _ = ∑ g ∈ Finset.range n, (2 ^ w) ^ g := by
      rw [Nat.geomSum_eq hw2 n]
    _ = ∑ g ∈ Finset.range n, 2 ^ (w * g) := by
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [pow_mul]
    _ = pk2 w S (fun _ _ => 1) 1 n := by
      simp [pk2]

/-! ## The unimodal decomposition of an envelope sum -/

theorem uni_up (f : ℕ → ℕ) (ns NN : ℕ) (hup : ∀ n, n < ns → n < NN → f n ≤ f (n + 1)) (x d : ℕ)
    (h1 : x + d ≤ ns) (h2 : x + d ≤ NN) : f x ≤ f (x + d) := by
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact (ih (by omega) (by omega)).trans (hup (x + d) (by omega) (by omega))

theorem uni_down (f : ℕ → ℕ) (ns NN : ℕ) (hdown : ∀ n, ns ≤ n → n < NN → f (n + 1) ≤ f n) (x d : ℕ)
    (h1 : ns ≤ x) (h2 : x + d ≤ NN) : f (x + d) ≤ f x := by
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact (hdown (x + d) (by omega) (by omega)).trans (ih (by omega))

theorem sup_down (f : ℕ → ℕ) (ns NN : ℕ) (hdown : ∀ n, ns ≤ n → n < NN → f (n + 1) ≤ f n) (x y : ℕ)
    (hx : ns ≤ x) (hxy : x ≤ y) (hy : y ≤ NN) : (Icc x y).sup f = f x := by
  apply le_antisymm
  · refine Finset.sup_le fun n hn => ?_
    rw [mem_Icc] at hn
    have := uni_down f ns NN hdown x (n - x) hx (by omega)
    rwa [Nat.add_sub_cancel' hn.1] at this
  · exact Finset.le_sup (mem_Icc.2 ⟨le_rfl, hxy⟩)

theorem sup_up (f : ℕ → ℕ) (ns NN : ℕ) (hup : ∀ n, n < ns → n < NN → f n ≤ f (n + 1))
    (hdown : ∀ n, ns ≤ n → n < NN → f (n + 1) ≤ f n) (x y : ℕ)
    (hx : x ≤ ns) (hxy : x ≤ y) (hy : y ≤ NN) : (Icc x y).sup f = f (min ns y) := by
  apply le_antisymm
  · refine Finset.sup_le fun n hn => ?_
    rw [mem_Icc] at hn
    by_cases hnp : n ≤ min ns y
    · have := uni_up f ns NN hup n (min ns y - n) (by omega) (by omega)
      rwa [Nat.add_sub_cancel' hnp] at this
    · have hp : min ns y = ns := by omega
      rw [hp]
      have := uni_down f ns NN hdown ns (n - ns) le_rfl (by omega)
      rwa [Nat.add_sub_cancel' (by omega)] at this
  · exact Finset.le_sup (mem_Icc.2 ⟨by omega, by omega⟩)


/-- The envelope sum of a unimodal weight (nondecreasing below `ns`, nonincreasing from `ns`) is
the window `ns < q + s` plus one prefix sum: at `a = min(ns, nh)` if `q + sh ≥ a`, at `q + sh`
otherwise. -/
theorem envS_decomp (NN M q sh nh : ℕ) (Rv : ℕ → ℕ)
    (hup : ∀ n, n < 4 * M / 3 → n < NN → om NN M n ≤ om NN M (n + 1))
    (hdown : ∀ n, 4 * M / 3 ≤ n → n < NN → om NN M (n + 1) ≤ om NN M n) (hNN : q + sh ≤ NN) :
    envS NN M q sh nh Rv =
      (∑ s ∈ range (sh + 1), if 4 * M / 3 < q + s ∧ q + s ≤ nh then om NN M (q + s) * Rv s else 0) +
      (if min (4 * M / 3) nh ≤ q + sh ∧ q ≤ min (4 * M / 3) nh then
        om NN M (min (4 * M / 3) nh) * ∑ s ∈ range (min (4 * M / 3) nh - q + 1), Rv s else 0) +
      (if q + sh < min (4 * M / 3) nh then om NN M (q + sh) * ∑ s ∈ range (sh + 1), Rv s else 0) := by
  set ns := 4 * M / 3 with hns
  set a := min ns nh with ha
  have hterm : ∀ s ∈ range (sh + 1),
      (if q + s ≤ nh then envW NN M q s (min (q + sh) nh) * Rv s else 0) =
      (if ns < q + s ∧ q + s ≤ nh then om NN M (q + s) * Rv s else 0) +
      (if q + s ≤ a then om NN M (min a (q + sh)) * Rv s else 0) := by
    intro s hs
    rw [mem_range] at hs
    by_cases h1 : q + s ≤ nh
    · rw [ite_eq_left h1]
      unfold envW
      by_cases h2 : ns < q + s
      · rw [ite_eq_left (show ns < q + s ∧ q + s ≤ nh from ⟨h2, h1⟩), ite_eq_right (show ¬(q + s ≤ a) by omega),
          add_zero, sup_down (om NN M) ns NN hdown (q + s) _ h2.le (by omega) (by omega)]
      · rw [ite_eq_right (show ¬(ns < q + s ∧ q + s ≤ nh) by omega), ite_eq_left (show q + s ≤ a by omega),
          zero_add, sup_up (om NN M) ns NN hup hdown (q + s) _ (by omega) (by omega) (by omega)]
        congr 2
        omega
    · rw [ite_eq_right h1, ite_eq_right (show ¬(ns < q + s ∧ q + s ≤ nh) by omega),
        ite_eq_right (show ¬(q + s ≤ a) by omega), add_zero]
  unfold envS
  rw [sum_congr rfl hterm, sum_add_distrib, add_assoc]
  congr 1
  by_cases h3 : a ≤ q + sh
  · rw [ite_eq_right (show ¬(q + sh < a) by omega), add_zero]
    by_cases h4 : q ≤ a
    · rw [ite_eq_left (show a ≤ q + sh ∧ q ≤ a from ⟨h3, h4⟩), mul_sum, min_eq_left h3,
        ← sum_range_add_sum_Ico _ (show a - q + 1 ≤ sh + 1 by omega),
        sum_eq_zero (s := Ico _ _) (fun s hs => ite_eq_right (by rw [mem_Ico] at hs; omega)), add_zero]
      exact sum_congr rfl fun s hs => ite_eq_left (by rw [mem_range] at hs; omega)
    · rw [ite_eq_right (show ¬(a ≤ q + sh ∧ q ≤ a) by omega)]
      exact sum_eq_zero fun s _ => ite_eq_right (by omega)
  · rw [ite_eq_right (show ¬(a ≤ q + sh ∧ q ≤ a) by omega), zero_add,
      ite_eq_left (show q + sh < a by omega), mul_sum, min_eq_right (by omega)]
    exact sum_congr rfl fun s hs => ite_eq_left (by rw [mem_range] at hs; omega)

/-! ## The tables -/

theorem plRow_eq (c : ConvCfg) (m row : ℕ) :
    plRow c m row = pk c.SW (fun g => if g ≤ c.GM then
      m * (slot 64 row g - if g = 0 then 0 else slot 64 row (g - 1)) else 0) (c.GM + 1) := by
  unfold plRow
  rw [packTree_eq, pk_extend _ _ (c.GM + 1) _ (clog_spec _)]
  · refine pk_congr _ _ _ _ fun g _ => ?_
    simp only [zero_add, Bool.cond_eq_ite, Nat.ble_eq, Nat.beq_eq, Nat.mul_eq, Nat.sub_eq]
  · intro i hi _
    simp only [zero_add, Bool.cond_eq_ite, Nat.ble_eq]
    rw [ite_eq_right (by omega)]

theorem buildX_eq (c : ConvCfg) (rows : List ℕ) :
    buildX c rows = pk2 c.SW (2 * c.GM + 1) (xv c.E c.GM rows) c.E (c.GM + 1) := by
  unfold buildX
  rw [packTree_eq, pk_extend _ _ c.E _ (clog_spec _), ← pk_nest,
    show c.B2 = (2 * c.GM + 1) * c.SW from rfl]
  · refine pk_congr _ _ _ _ fun e he => ?_
    simp only [zero_add, Bool.cond_eq_ite, Nat.blt_eq, he, ite_true, fact_eq, ndiv_eq]
    rw [plRow_eq]
    refine pk_congr _ _ _ _ fun g hg => ?_
    unfold xv rv
    by_cases hgG : g ≤ c.GM
    · rw [ite_eq_left (show g ≤ c.GM from hgG),
        ite_eq_left (show e < c.E ∧ g ≤ c.GM from ⟨he, hgG⟩)]
      rfl
    · omega
  · intro i hi _
    simp only [zero_add, Bool.cond_eq_ite, Nat.blt_eq]
    rw [ite_eq_right (by omega)]

theorem pk2_congr (w S : ℕ) (f g : ℕ → ℕ → ℕ) (m n : ℕ) (h : ∀ e < m, ∀ s < n, f e s = g e s) :
    pk2 w S f m n = pk2 w S g m n :=
  Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun s hs => by
    rw [h e (mem_range.1 he) s (mem_range.1 hs)]

theorem guard_SW (c : ConvCfg) (hG : Guard c) : 0 < c.SW := by
  rcases Nat.eq_zero_or_pos c.SW with h | h
  · have := guard_four c hG
    rw [h, pow_zero] at this
    exact absurd this (not_lt.2 (Nat.one_le_pow _ _ (by norm_num)))
  · exact h

theorem guard_Sx2 (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c) :
    Sx c.E c.GM rows ^ 2 < 2 ^ c.SW := by
  rcases Nat.eq_zero_or_pos (Sx c.E c.GM rows) with h | h
  · rw [h]; exact pow_pos (by norm_num) _
  · exact lt_of_le_of_lt (Nat.pow_le_pow_right h (by norm_num)) (guard_Sx c rows hrows hG)

theorem xv_le_Sx (E GM : ℕ) (rows : List ℕ) (e g : ℕ) (he : e < E) (hg : g < GM + 1) :
    xv E GM rows e g ≤ Sx E GM rows := by
  unfold Sx
  calc xv E GM rows e g ≤ ∑ g ∈ range (GM + 1), xv E GM rows e g :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 hg)
    _ ≤ _ := Finset.single_le_sum (f := fun e => ∑ g ∈ range (GM + 1), xv E GM rows e g)
        (fun _ _ => Nat.zero_le _) (mem_range.2 he)

theorem guard_xv (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c) :
    ∀ e < c.E, ∀ g < c.GM + 1, xv c.E c.GM rows e g < 2 ^ c.SW := by
  intro e he g hg
  refine lt_of_le_of_lt (xv_le_Sx _ _ _ _ _ he hg) ?_
  rcases Nat.eq_zero_or_pos (Sx c.E c.GM rows) with h | h
  · rw [h]; exact pow_pos (by norm_num) _
  · exact lt_of_le_of_lt (Nat.le_self_pow (by norm_num) _) (guard_Sx c rows hrows hG)

theorem q2_zero (E GM : ℕ) (rows : List ℕ) (M s : ℕ) (hs : 2 * GM < s) : q2 E GM rows M s = 0 := by
  unfold q2
  refine sum_eq_zero fun e1 _ => sum_eq_zero fun e2 _ => sum_eq_zero fun g1 hg1 =>
    sum_eq_zero fun g2 hg2 => ?_
  rw [mem_range] at hg1 hg2
  exact ite_eq_right (by omega)

theorem B2_eq (c : ConvCfg) : c.B2 = (2 * c.GM + 1) * c.SW := rfl

theorem tmask_eq (c : ConvCfg) (k : ℕ) :
    tmask c k = mask ((c.GM + 1) * c.SW) * ones ((2 * c.GM + 1) * c.SW) k := rfl

theorem sqQ_eq (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c) :
    sqQ c (buildX c rows) = pk2 c.SW (2 * c.GM + 1) (q2 c.E c.GM rows) (2 * c.E - 1) (c.GM + 1) := by
  unfold sqQ
  rw [Nat.land_eq, Nat.mul_eq, tmask_eq, buildX_eq, pk2_mul]
  change pk2 c.SW (2 * c.GM + 1) (q2 c.E c.GM rows) (c.E + c.E) (c.GM + 1 + (c.GM + 1)) &&& _ = _
  rw [pk2_extend c.SW (2 * c.GM + 1) _ _ (2 * c.GM + 1) (c.GM + 1 + (c.GM + 1)) (by omega)
    (fun e _ g hg1 hg2 => q2_zero c.E c.GM rows e g (by omega))]
  rw [Nat.sub_eq, Nat.mul_eq, pk2_land_tmask c.SW (2 * c.GM + 1) _ _ _ _ _ le_rfl (by omega)
    (fun e _ g _ => lt_of_le_of_lt (q2_le_sq _ _ _ _ _) (guard_Sx2 c rows hrows hG))]
  rw [show min (c.E + c.E) (2 * c.E - 1) = 2 * c.E - 1 by omega,
    show min (2 * c.GM + 1) (c.GM + 1) = c.GM + 1 by omega]

theorem conv_zero_top (GM n n' : ℕ) (f g : ℕ → ℕ → ℕ) (e s : ℕ) (hs : 2 * GM < s) :
    (∑ e1 ∈ range n, ∑ e2 ∈ range n', ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
      if e1 + e2 = e ∧ g1 + g2 = s then f e1 g1 * g e2 g2 else 0) = 0 := by
  refine sum_eq_zero fun e1 _ => sum_eq_zero fun e2 _ => sum_eq_zero fun g1 hg1 =>
    sum_eq_zero fun g2 hg2 => ?_
  rw [mem_range] at hg1 hg2
  exact ite_eq_right (by omega)

theorem prodR_eq (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c)
    (J : ℕ) (hJ : J ≤ c.E) :
    prodR c (buildX c rows) (sqQ c (buildX c rows)) J =
      pk2 c.SW (2 * c.GM + 1) (rT c.E c.GM J rows) (J + 2 * c.E - 2) (c.GM + 1) := by
  rw [sqQ_eq c rows hrows hG]
  unfold prodR
  rw [Nat.land_eq, Nat.land_eq, Nat.mul_eq, Nat.mul_eq, B2_eq, tmask_eq, buildX_eq,
    pk2_rows c.SW (2 * c.GM + 1) _ _ _ J (by omega) (guard_xv c rows hrows hG),
    show min c.E J = J from min_eq_right hJ, pk2_mul]
  rw [pk2_extend c.SW (2 * c.GM + 1) _ _ (2 * c.GM + 1) _ (by omega)
    (fun e _ g hg1 _ => conv_zero_top c.GM _ _ _ _ e g (by omega))]
  rw [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, pk2_land_tmask c.SW (2 * c.GM + 1) _ _ _ _ _ le_rfl (by omega)
    (fun e _ g _ => lt_of_le_of_lt (conv3_le c.E c.GM J rows hJ e g) (guard_Sx c rows hrows hG))]
  rw [show min (J + (2 * c.E - 1)) (J + (2 * c.E - 2)) = J + 2 * c.E - 2 by omega,
    show min (2 * c.GM + 1) (c.GM + 1) = c.GM + 1 by omega]
  exact pk2_congr _ _ _ _ _ _ fun e _ s hs => conv_q2_eq_rT c.E c.GM J rows e s (by omega)

theorem prefixR_eq (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c)
    (J : ℕ) (hJ : J ≤ c.E) :
    prefixR c (prodR c (buildX c rows) (sqQ c (buildX c rows)) J) J =
      pk2 c.SW (2 * c.GM + 1) (prT c.E c.GM J rows) (J + 2 * c.E - 2) (c.GM + 1) := by
  rw [prodR_eq c rows hrows hG J hJ]
  unfold prefixR
  rw [Nat.land_eq, Nat.mul_eq, tmask_eq, pk2_ones c.SW (2 * c.GM + 1) (c.GM + 1) (guard_SW c hG),
    pk2_mul]
  rw [pk2_extend c.SW (2 * c.GM + 1) _ _ (2 * c.GM + 1) _ (by omega)
    (fun e _ g hg1 _ => conv_zero_top c.GM _ _ _ _ e g (by omega))]
  rw [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, pk2_land_tmask c.SW (2 * c.GM + 1) _ _ _ _ _ le_rfl (by omega)
    (fun e _ g _ => lt_of_le_of_lt ((conv_ones_le _ _ _ e g).trans
      (le_trans (rT_sum_le c.E c.GM J rows hJ e (c.GM + 1)) le_rfl)) (guard_Sx c rows hrows hG))]
  rw [show min (J + 2 * c.E - 2 + 1) (J + (2 * c.E - 2)) = J + 2 * c.E - 2 by omega,
    show min (2 * c.GM + 1) (c.GM + 1) = c.GM + 1 by omega]
  exact pk2_congr _ _ _ _ _ _ fun e he s hs => conv_ones_eq _ _ _ e s he (by omega)

theorem mkTab_R (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c)
    (J : ℕ) (hJ : J ≤ c.E) (M : ℕ) :
    getN (mkTab c (buildX c rows) (sqQ c (buildX c rows)) J).R M =
      if M < J + 2 * c.E - 2 then pk c.SW (fun s => M.factorial * rT c.E c.GM J rows M s) (c.GM + 1)
      else 0 := by
  change getN (scaleFact (split c.B2 (Nat.add J (Nat.sub (Nat.mul 2 c.E) 2))
    (prodR c (buildX c rows) (sqQ c (buildX c rows)) J))) M = _
  have hn : J + 2 * c.E - 2 = Nat.add J (Nat.sub (Nat.mul 2 c.E) 2) := by
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq]; omega
  rw [scaleFact_getN, prodR_eq c rows hrows hG J hJ, B2_eq, hn,
    split_pk2 c.SW (2 * c.GM + 1) _ _ _ M (by omega) (fun e _ g hg =>
      lt_of_le_of_lt ((Finset.single_le_sum (f := fun s => rT c.E c.GM J rows e s)
        (fun _ _ => Nat.zero_le _) (mem_range.2 hg)).trans (rT_sum_le c.E c.GM J rows hJ e _))
        (guard_Sx c rows hrows hG))]
  split_ifs
  · exact pk_smul _ _ _ _
  · exact mul_zero _

theorem mkTab_PR (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c)
    (J : ℕ) (hJ : J ≤ c.E) (M : ℕ) :
    getN (mkTab c (buildX c rows) (sqQ c (buildX c rows)) J).PR M =
      if M < J + 2 * c.E - 2 then pk c.SW (fun s => M.factorial * prT c.E c.GM J rows M s) (c.GM + 1)
      else 0 := by
  change getN (scaleFact (split c.B2 (Nat.add J (Nat.sub (Nat.mul 2 c.E) 2))
    (prefixR c (prodR c (buildX c rows) (sqQ c (buildX c rows)) J) J))) M = _
  have hn : J + 2 * c.E - 2 = Nat.add J (Nat.sub (Nat.mul 2 c.E) 2) := by
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq]; omega
  rw [scaleFact_getN, prefixR_eq c rows hrows hG J hJ, B2_eq, hn,
    split_pk2 c.SW (2 * c.GM + 1) (prT c.E c.GM J rows) _ _ M (by omega) (fun e _ g _ =>
      lt_of_le_of_lt (rT_sum_le c.E c.GM J rows hJ e _) (guard_Sx c rows hrows hG))]
  split_ifs
  · exact pk_smul _ _ _ _
  · exact mul_zero _

/-! ## One envelope unit -/

/-- The window part of `envUnit`. -/
def vWf (c : ConvCfg) (sh M nh Ow R : ℕ) : ℕ :=
  let SW := c.SW
  let Q0 := c.Q0
  let ns := Nat.div (Nat.mul 4 M) 3
  let nw := minN nh c.NN
  let s0 := Nat.sub (Nat.add ns 1) Q0
  let s1 := minN sh (Nat.sub nw 2)
  let Zc := Nat.land (Nat.shiftRight R (Nat.mul s0 SW)) (mask (Nat.mul (Nat.sub (Nat.add s1 1) s0) SW))
  let P := Nat.mul Ow Zc
  let up := Nat.add s0 Q0
  Nat.land
    (cond (Nat.ble up nw) (Nat.shiftRight P (Nat.mul (Nat.sub nw up) SW))
      (Nat.shiftLeft P (Nat.mul (Nat.sub up nw) SW)))
    (mask (Nat.mul c.E SW))

/-- The prefix part of `envUnit` at `a = min(ns, nh)`. -/
def vAf (c : ConvCfg) (sh M nh O PR : ℕ) : ℕ :=
  let SW := c.SW
  let Q0 := c.Q0
  let ns := Nat.div (Nat.mul 4 M) 3
  let a := minN ns nh
  let qlo := maxN 2 (Nat.sub a sh)
  let qhi := minN (minN Q0 ns) a
  let PRx := Nat.land (Nat.shiftRight PR (Nat.mul (Nat.sub a qhi) SW))
    (mask (Nat.mul (Nat.sub (Nat.add qhi 1) qlo) SW))
  Nat.mul (slot SW O (Nat.sub c.NN a)) (Nat.shiftLeft PRx (Nat.mul (Nat.sub Q0 qhi) SW))

/-- The prefix part of `envUnit` at `q + sh`. -/
def vSf (c : ConvCfg) (sh M nh O PR : ℕ) : ℕ :=
  let SW := c.SW
  let Q0 := c.Q0
  let ns := Nat.div (Nat.mul 4 M) 3
  let a := minN ns nh
  let qs := minN (minN Q0 ns) (Nat.sub (Nat.sub a sh) 1)
  let Ox := Nat.land (Nat.shiftRight O (Nat.mul (Nat.sub (Nat.sub c.NN sh) qs) SW))
    (mask (Nat.mul (Nat.sub qs 1) SW))
  Nat.mul (slot SW PR sh) (Nat.shiftLeft Ox (Nat.mul (Nat.sub Q0 qs) SW))

theorem envUnit_split (c : ConvCfg) (sh M nh Ow O R PR : ℕ) :
    envUnit c sh M nh Ow O R PR = vWf c sh M nh Ow R + (vAf c sh M nh O PR + vSf c sh M nh O PR) := rfl

/-- The window part of `envUnit`: slot `t` is the sum over `s ≤ sh` with `ns < q + s ≤ nh` of
`omega'(q + s) Rv(s)`, `q = Q0 - t`. -/
theorem vWf_eq (c : ConvCfg) (sh M nh : ℕ) (Rv : ℕ → ℕ) (hsh : sh ≤ c.GM)
    (hB : 4 ^ c.NN * ∑ s ∈ range (c.GM + 1), Rv s < 2 ^ c.SW) :
    vWf c sh M nh (pk c.SW (fun i => om c.NN M (min nh c.NN - i)) (min nh c.NN - 4 * M / 3))
        (pk c.SW Rv (c.GM + 1)) =
      pk c.SW (fun t => ∑ s ∈ range (sh + 1),
        if 4 * M / 3 < c.Q0 - t + s ∧ c.Q0 - t + s ≤ nh then om c.NN M (c.Q0 - t + s) * Rv s else 0)
        c.E := by
  obtain ⟨E, GM, SW⟩ := c
  simp only [ConvCfg.Q0, ConvCfg.NN, Nat.add_eq] at hB hsh ⊢
  unfold vWf
  simp only [ConvCfg.Q0, ConvCfg.NN, minN_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ndiv_eq,
    Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq', Bool.cond_eq_ite, Nat.ble_eq]
  set NN := E + GM + 1 with hNN
  set ns := 4 * M / 3 with hns
  set nw := min nh NN with hnw
  set s0 := ns + 1 - (E + 1) with hs0
  set s1 := min sh (nw - 2) with hs1
  set LW := nw - ns with hLW
  have hsum1 : ∑ s ∈ range (GM + 1), Rv s ≤ 4 ^ NN * ∑ s ∈ range (GM + 1), Rv s :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hRv : ∀ s < GM + 1, Rv s < 2 ^ SW := fun s hs =>
    lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 hs)) (by omega)
  rw [pk_slice SW Rv (GM + 1) s0 (s1 + 1 - s0) hRv, pk_mul]
  set LZ := min (GM + 1 - s0) (s1 + 1 - s0) with hLZ
  -- one entry of the product
  have hconv : ∀ k, (∑ i ∈ range LW, ∑ j ∈ range LZ,
      if i + j = k then om NN M (nw - i) * Rv (j + s0) else 0) =
      ∑ j ∈ range LZ, if j ≤ k ∧ k - j < LW then om NN M (nw - (k - j)) * Rv (j + s0) else 0 := by
    intro k
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => sum_single_add LW j k (fun i => om NN M (nw - i) * Rv (j + s0))
  simp_rw [hconv]
  -- facts on the cuts, for omega
  have hnw1 : nw ≤ nh := min_le_left _ _
  have hnw2 : nw ≤ NN := min_le_right _ _
  have hnw3 : nw = nh ∨ nw = NN := min_choice _ _
  have hs11 : s1 ≤ sh := min_le_left _ _
  have hs12 : s1 ≤ nw - 2 := min_le_right _ _
  have hs13 : s1 = sh ∨ s1 = nw - 2 := min_choice _ _
  have hLZ1 : LZ ≤ GM + 1 - s0 := min_le_left _ _
  have hLZ2 : LZ ≤ s1 + 1 - s0 := min_le_right _ _
  have hLZ3 : LZ = GM + 1 - s0 ∨ LZ = s1 + 1 - s0 := min_choice _ _
  set conv := fun k => ∑ j ∈ range LZ,
    if j ≤ k ∧ k - j < LW then om NN M (nw - (k - j)) * Rv (j + s0) else 0 with hconvdef
  -- the entries of the product are below `2^SW`
  have hconvB : ∀ k, conv k < 2 ^ SW := by
    intro k
    refine lt_of_le_of_lt ?_ hB
    calc conv k ≤ ∑ j ∈ range LZ, 4 ^ NN * Rv (j + s0) := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs
          · exact Nat.mul_le_mul_right _ (om_le _ _ _ (by omega))
          · exact Nat.zero_le _
      _ = 4 ^ NN * ∑ j ∈ range LZ, Rv (j + s0) := by rw [Finset.mul_sum]
      _ ≤ 4 ^ NN * ∑ s ∈ range (GM + 1), Rv s := by
          refine Nat.mul_le_mul_left _ ?_
          rcases Nat.eq_zero_or_pos LZ with h0 | h0
          · rw [h0]; simp
          rw [sum_shift_ind LZ s0 (GM + 1) Rv (by omega), ← Finset.sum_filter]
          exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hconv0 : ∀ k, LW + LZ ≤ k → conv k = 0 := by
    intro k hk
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [mem_range] at hj
    rw [ite_eq_right (by omega)]
  -- the key identity, entry by entry
  have key : ∀ t < E, (if s0 + (E + 1) ≤ t + nw then conv (t + nw - (s0 + (E + 1))) else 0) =
      ∑ s ∈ range (sh + 1),
        if ns < E + 1 - t + s ∧ E + 1 - t + s ≤ nh then om NN M (E + 1 - t + s) * Rv s else 0 := by
    intro t ht
    have hR : ∀ s, s < sh + 1 → ns < E + 1 - t + s → E + 1 - t + s ≤ nh →
        s0 ≤ s ∧ s < s0 + LZ ∧ E + 1 - t + s ≤ nw := by
      intro s hs h1 h2
      omega
    split_ifs with hc
    · have hg : ∀ j ∈ range LZ, (if j ≤ t + nw - (s0 + (E + 1)) ∧ t + nw - (s0 + (E + 1)) - j < LW
            then om NN M (nw - (t + nw - (s0 + (E + 1)) - j)) * Rv (j + s0) else 0) =
          (fun s => if ns < E + 1 - t + s ∧ E + 1 - t + s ≤ nw then
            om NN M (E + 1 - t + s) * Rv s else 0) (j + s0) := by
        intro j _
        dsimp only
        by_cases hj1 : j ≤ t + nw - (s0 + (E + 1)) ∧ t + nw - (s0 + (E + 1)) - j < LW
        · rw [ite_eq_left hj1, ite_eq_left (by omega),
            show nw - (t + nw - (s0 + (E + 1)) - j) = E + 1 - t + (j + s0) by omega]
        · rw [ite_eq_right hj1, ite_eq_right (by omega)]
      refine (Finset.sum_congr rfl hg).trans ((sum_shift_ind LZ s0 (GM + 1 + s0)
        (fun s => if ns < E + 1 - t + s ∧ E + 1 - t + s ≤ nw then
          om NN M (E + 1 - t + s) * Rv s else 0) (by omega)).trans ?_)
      rw [sum_range_ind (sh + 1) (GM + 1 + s0) _ (by omega)]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases h1 : s < sh + 1 ∧ ns < E + 1 - t + s ∧ E + 1 - t + s ≤ nh
      · obtain ⟨h1a, h1b, h1c⟩ := h1
        have := hR s h1a h1b h1c
        rw [ite_eq_left ⟨this.1, this.2.1⟩, ite_eq_left ⟨h1b, this.2.2⟩, ite_eq_left h1a, ite_eq_left ⟨h1b, h1c⟩]
      · split_ifs <;> first | rfl | (exfalso; omega)
    · refine (Finset.sum_eq_zero fun s hs => ?_).symm
      rw [mem_range] at hs
      rw [ite_eq_right]
      intro h
      have := hR s hs h.1 h.2
      omega
  split_ifs with hup
  · rw [pk_slice SW conv (LW + LZ) (nw - (s0 + (E + 1))) E (fun k _ => hconvB k),
      pk_to SW _ _ E (fun i hi _ => hconv0 _ (by omega))]
    refine pk_congr SW _ _ E fun t ht => ?_
    have h := key t ht
    rw [ite_eq_left (by omega)] at h
    rw [show t + (nw - (s0 + (E + 1))) = t + nw - (s0 + (E + 1)) by omega]
    exact h
  · rw [pk_shl, pk_and_mask SW _ _ E (fun k _ => by
        split_ifs
        · exact pow_pos (by norm_num) _
        · exact hconvB _),
      pk_to SW _ _ E (fun i hi _ => by rw [ite_eq_right (by omega)]; exact hconv0 _ (by omega))]
    refine pk_congr SW _ _ E fun t ht => ?_
    have h := key t ht
    by_cases h1 : t < s0 + (E + 1) - nw
    · rw [ite_eq_right (by omega)] at h
      rw [ite_eq_left h1]
      exact h
    · rw [ite_eq_left (by omega)] at h
      rw [ite_eq_right h1, show t - (s0 + (E + 1) - nw) = t + nw - (s0 + (E + 1)) by omega]
      exact h

/-- The prefix part of `envUnit`: slot `t` is `omega'(a) PR(a - q)` when `a ≤ q + sh` and `q ≤ a`
(`q = Q0 - t`, `a = min(ns, nh)`). -/
theorem vAf_eq (c : ConvCfg) (sh M nh : ℕ) (Rv : ℕ → ℕ) (hsh : sh ≤ c.GM)
    (h4 : 4 ^ c.NN < 2 ^ c.SW) (hB : 4 ^ c.NN * ∑ s ∈ range (c.GM + 1), Rv s < 2 ^ c.SW) :
    vAf c sh M nh (pk c.SW (fun i => om c.NN M (c.NN - i)) (c.NN + 1))
        (pk c.SW (fun s => ∑ s' ∈ range (s + 1), Rv s') (c.GM + 1)) =
      pk c.SW (fun t => if min (4 * M / 3) nh ≤ c.Q0 - t + sh ∧ c.Q0 - t ≤ min (4 * M / 3) nh then
        om c.NN M (min (4 * M / 3) nh) * ∑ s ∈ range (min (4 * M / 3) nh - (c.Q0 - t) + 1), Rv s
        else 0) c.E := by
  obtain ⟨E, GM, SW⟩ := c
  simp only [ConvCfg.Q0, ConvCfg.NN, Nat.add_eq] at hB hsh h4 ⊢
  unfold vAf
  simp only [ConvCfg.Q0, ConvCfg.NN, minN_eq, maxN_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ndiv_eq,
    Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq']
  set NN := E + GM + 1 with hNN
  set ns := 4 * M / 3 with hns
  set a := min ns nh with ha
  have hPR : ∀ s < GM + 1, ∑ s' ∈ range (s + 1), Rv s' < 2 ^ SW := fun s hs =>
    lt_of_le_of_lt (Finset.sum_le_sum_of_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega))
      (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) hB)
  have hO : ∀ i < NN + 1, om NN M (NN - i) < 2 ^ SW := fun i _ =>
    lt_of_le_of_lt (om_le _ _ _ (by omega)) h4
  rw [pk_win SW _ (GM + 1) _ _ _ hPR, pk_smul]
  refine pk_eq_pk SW _ _ _ _ fun t _ => ?_
  by_cases hc : t < E ∧ a ≤ E + 1 - t + sh ∧ E + 1 - t ≤ a
  · obtain ⟨hc1, hc2, hc3⟩ := hc
    split_ifs <;> first | (exfalso; omega) | skip
    rw [slot_pk SW _ _ _ hO, ite_eq_left (show NN - a < NN + 1 by omega)]
    rw [show NN - (NN - a) = a by omega]
    refine Eq.trans ?_ (ite_eq_left ⟨hc2, hc3⟩).symm
    rw [show t + (a - min (min (E + 1) ns) a) - (E + 1 - min (min (E + 1) ns) a) = a - (E + 1 - t) by
      omega]
  · split_ifs <;> first | rfl | (exfalso; omega) | (rw [mul_zero]; done) |
      exact (ite_eq_right (by omega)).symm

/-- The second prefix part of `envUnit`: slot `t` is `omega'(q + sh) PR(sh)` when `q + sh < a`
(`q = Q0 - t`, `a = min(ns, nh)`). -/
theorem vSf_eq (c : ConvCfg) (sh M nh : ℕ) (Rv : ℕ → ℕ) (hsh : sh ≤ c.GM)
    (h4 : 4 ^ c.NN < 2 ^ c.SW) (hB : 4 ^ c.NN * ∑ s ∈ range (c.GM + 1), Rv s < 2 ^ c.SW) :
    vSf c sh M nh (pk c.SW (fun i => om c.NN M (c.NN - i)) (c.NN + 1))
        (pk c.SW (fun s => ∑ s' ∈ range (s + 1), Rv s') (c.GM + 1)) =
      pk c.SW (fun t => if c.Q0 - t + sh < min (4 * M / 3) nh then
        om c.NN M (c.Q0 - t + sh) * ∑ s ∈ range (sh + 1), Rv s else 0) c.E := by
  obtain ⟨E, GM, SW⟩ := c
  simp only [ConvCfg.Q0, ConvCfg.NN, Nat.add_eq] at hB hsh h4 ⊢
  unfold vSf
  simp only [ConvCfg.Q0, ConvCfg.NN, minN_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ndiv_eq,
    Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq']
  set NN := E + GM + 1 with hNN
  set ns := 4 * M / 3 with hns
  set a := min ns nh with ha
  have hPR : ∀ s < GM + 1, ∑ s' ∈ range (s + 1), Rv s' < 2 ^ SW := fun s hs =>
    lt_of_le_of_lt (Finset.sum_le_sum_of_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega))
      (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) hB)
  have hO : ∀ i < NN + 1, om NN M (NN - i) < 2 ^ SW := fun i _ =>
    lt_of_le_of_lt (om_le _ _ _ (by omega)) h4
  rw [pk_win SW _ (NN + 1) _ _ _ hO, pk_smul, slot_pk SW _ _ _ hPR, ite_eq_left (show sh < GM + 1 by omega)]
  refine pk_eq_pk SW _ _ _ _ fun t _ => ?_
  by_cases hc : t < E ∧ E + 1 - t + sh < a
  · obtain ⟨hc1, hc2⟩ := hc
    split_ifs <;> first | (exfalso; omega) | skip
    refine Eq.trans ?_ (ite_eq_left hc2).symm
    rw [mul_comm, show NN - (t + (NN - sh - min (min (E + 1) ns) (a - sh - 1)) -
      (E + 1 - min (min (E + 1) ns) (a - sh - 1))) = E + 1 - t + sh by omega]
  · split_ifs <;> first | rfl | (exfalso; omega) | (rw [mul_zero]; done) |
      exact (ite_eq_right (by omega)).symm

/-- `envUnit` is the vector over `t = Q0 - q` of the envelope sums `envS` at `q`, `q = 2..Q0`. -/
theorem envUnit_spec (c : ConvCfg) (sh M nh : ℕ) (Rv : ℕ → ℕ) (hsh : sh ≤ c.GM)
    (h4 : 4 ^ c.NN < 2 ^ c.SW) (hB : 4 ^ c.NN * ∑ s ∈ range (c.GM + 1), Rv s < 2 ^ c.SW) :
    envUnit c sh M nh
        (pk c.SW (fun i => om c.NN M (min nh c.NN - i)) (min nh c.NN - 4 * M / 3))
        (pk c.SW (fun i => om c.NN M (c.NN - i)) (c.NN + 1))
        (pk c.SW Rv (c.GM + 1)) (pk c.SW (fun s => ∑ s' ∈ range (s + 1), Rv s') (c.GM + 1)) =
      pk c.SW (fun t => envS c.NN M (c.Q0 - t) sh nh Rv) c.E := by
  rw [envUnit_split, vWf_eq c sh M nh Rv hsh hB, vAf_eq c sh M nh Rv hsh h4 hB,
    vSf_eq c sh M nh Rv hsh h4 hB, pk_add, pk_add]
  refine pk_congr _ _ _ _ fun t _ => ?_
  rw [envS_decomp c.NN M (c.Q0 - t) sh nh Rv (om_le_succ c.NN M) (om_succ_le c.NN M)
    (by simp only [ConvCfg.Q0, ConvCfg.NN, Nat.add_eq]; omega), add_assoc]

/-! ## The families -/

theorem omRows_getN (SW NN m M : ℕ) (hM : M < m) :
    getN (omRows SW NN m) M = pk SW (fun i => om NN M (NN - i)) (NN + 1) := by
  rw [getN_eq, omRows_eq]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hM, Option.map_some,
    Option.getD_some]
  refine pk_congr _ _ _ _ fun i hi => ?_
  unfold om
  rw [show NN - (NN - i) = i by omega]

theorem mkTab_R_length (c : ConvCfg) (X Q J : ℕ) :
    (mkTab c X Q J).R.length = 2 ^ clog (J + (2 * c.E - 2)) := by
  change (scaleFact (split c.B2 (Nat.add J (Nat.sub (Nat.mul 2 c.E) 2)) (prodR c X Q J))).length = _
  rw [scaleFact_length, split_length]
  rfl

theorem getN_map_range (m v : ℕ) (f : ℕ → ℕ) (hv : v < m) : getN ((List.range m).map f) v = f v := by
  rw [getN_eq]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv]

theorem natFold_succ {α : Type} (n : ℕ) (init : α) (f : ℕ → α → α) :
    natFold (n + 1) init f = f n (natFold n init f) := rfl

theorem inner_fold (m : ℕ) (acc : List ℕ) (h : ℕ → ℕ → ℕ) :
    natFold m ([], acc) (fun v (u : List ℕ × List ℕ) => (h v (hd u.2) :: u.1, tl u.2)) =
      (((List.range m).map (fun v => h v (getN acc v))).reverse, dropN m acc) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (h m (hd (natFold m ([], acc) (fun v (u : List ℕ × List ℕ) => (h v (hd u.2) :: u.1,
      tl u.2))).2) :: (natFold m ([], acc) (fun v (u : List ℕ × List ℕ) => (h v (hd u.2) :: u.1,
      tl u.2))).1, tl (natFold m ([], acc) (fun v (u : List ℕ × List ℕ) => (h v (hd u.2) :: u.1,
      tl u.2))).2) = _
    rw [ih, List.range_succ, List.map_append, List.reverse_append]
    rfl

theorem outer_fold (n m : ℕ) (l1 l2 l3 : List ℕ) (upd : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (hupd : ∀ M v x O R PR, upd M v x O R PR = x + F M v O R PR) :
    natFold n ((List.range m).map (fun _ => 0), l1, l2, l3)
      (fun M (st : List ℕ × List ℕ × List ℕ × List ℕ) =>
        ((natFold m ([], st.1) (fun v (u : List ℕ × List ℕ) =>
          (upd M v (hd u.2) (hd st.2.1) (hd st.2.2.1) (hd st.2.2.2) :: u.1, tl u.2))).1.reverse,
          tl st.2.1, tl st.2.2.1, tl st.2.2.2)) =
      ((List.range m).map (fun v => ∑ M ∈ range n, F M v (getN l1 M) (getN l2 M) (getN l3 M)),
        dropN n l1, dropN n l2, dropN n l3) := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; rfl
  | succ n ih =>
    rw [natFold_succ, ih]
    dsimp only
    rw [inner_fold m _ (fun v x => upd n v x (hd (dropN n l1)) (hd (dropN n l2)) (hd (dropN n l3))),
      List.reverse_reverse]
    refine Prod.ext ?_ rfl
    refine List.map_congr_left fun v hv => ?_
    rw [List.mem_range] at hv
    rw [hupd, getN_map_range _ _ _ hv, Finset.sum_range_succ]
    rfl

theorem famA_Ow (c : ConvCfg) (M VM v : ℕ) (hv : v ≤ VM) (h4 : 4 ^ c.NN < 2 ^ c.SW) :
    Nat.shiftRight (Nat.land (Nat.shiftRight (pk c.SW (fun i => om c.NN M (c.NN - i)) (c.NN + 1))
      (Nat.mul (Nat.sub c.NN (minN (Nat.add M VM) c.NN)) c.SW))
      (mask (Nat.mul (Nat.sub (minN (Nat.add M VM) c.NN) (Nat.div (Nat.mul 4 M) 3)) c.SW)))
      (Nat.mul (Nat.sub (minN (Nat.add M VM) c.NN) (minN (Nat.add M v) c.NN)) c.SW) =
    pk c.SW (fun i => om c.NN M (min (M + v) c.NN - i)) (min (M + v) c.NN - 4 * M / 3) := by
  have hO : ∀ i < c.NN + 1, om c.NN M (c.NN - i) < 2 ^ c.SW := fun i _ =>
    lt_of_le_of_lt (om_le _ _ _ (by omega)) h4
  simp only [minN_eq, Nat.sub_eq, Nat.mul_eq, ndiv_eq, Nat.land_eq, Nat.shiftRight_eq', Nat.add_eq]
  rw [pk_slice c.SW _ (c.NN + 1) _ _ hO, Nat.shiftRight_eq_div_pow, mul_comm _ c.SW,
    pk_div c.SW _ _ _ (fun i _ => hO _ (by omega))]
  rw [show min (c.NN + 1 - (c.NN - min (M + VM) c.NN)) (min (M + VM) c.NN - 4 * M / 3) -
      (min (M + VM) c.NN - min (M + v) c.NN) = min (M + v) c.NN - 4 * M / 3 by omega]
  refine pk_congr _ _ _ _ fun i hi => ?_
  rw [show c.NN - (i + (min (M + VM) c.NN - min (M + v) c.NN) + (c.NN - min (M + VM) c.NN)) =
    min (M + v) c.NN - i by omega]

theorem famB_eq (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c)
    (J : ℕ) (hJ1 : 1 ≤ J) (hJ : J ≤ c.E) (sh : ℕ) (hsh : sh ≤ c.GM) :
    famB c sh (omRows c.SW c.NN (3 * c.E - 2)) (mkTab c (buildX c rows) (sqQ c (buildX c rows)) J) =
      pk c.SW (fun t => ∑ M ∈ range (J + 2 * c.E - 2),
        envS c.NN M (c.Q0 - t) sh c.NN (fun s => M.factorial * rT c.E c.GM J rows M s)) c.E := by
  set t := mkTab c (buildX c rows) (sqQ c (buildX c rows)) J with ht
  set oms := omRows c.SW c.NN (3 * c.E - 2) with homs
  have hL : J + 2 * c.E - 2 ≤ t.R.length := by
    rw [ht, mkTab_R_length]
    exact le_trans (by omega) (clog_spec _)
  have key := congrArg Prod.fst (fold4_sum t.R.length 0 oms t.R t.PR (fun M O R PR =>
    envUnit c sh M c.NN (Nat.land O (mask (Nat.mul (Nat.sub c.NN (Nat.div (Nat.mul 4 M) 3)) c.SW)))
      O R PR))
  refine Eq.trans key ?_
  dsimp only
  rw [zero_add, ← Finset.sum_range_add_sum_Ico _ hL]
  rw [Finset.sum_eq_zero (s := Ico _ _) (fun M hM => ?_), add_zero, ← pk_sum]
  · refine Finset.sum_congr rfl fun M hM => ?_
    rw [mem_range] at hM
    rw [omRows_getN _ _ _ _ (by omega), mkTab_R c rows hrows hG J hJ M,
      mkTab_PR c rows hrows hG J hJ M, ite_eq_left hM, ite_eq_left hM]
    have hO : ∀ i < c.NN + 1, om c.NN M (c.NN - i) < 2 ^ c.SW := fun i _ =>
      lt_of_le_of_lt (om_le _ _ _ (by omega)) (guard_four c hG)
    have hOw : Nat.land (pk c.SW (fun i => om c.NN M (c.NN - i)) (c.NN + 1))
        (mask (Nat.mul (Nat.sub c.NN (Nat.div (Nat.mul 4 M) 3)) c.SW)) =
        pk c.SW (fun i => om c.NN M (min c.NN c.NN - i)) (min c.NN c.NN - 4 * M / 3) := by
      rw [Nat.land_eq, Nat.mul_eq, Nat.sub_eq, ndiv_eq, Nat.mul_eq, pk_and_mask _ _ _ _ hO, min_self]
      congr 1
      omega
    have hPR : pk c.SW (fun s => M.factorial * prT c.E c.GM J rows M s) (c.GM + 1) =
        pk c.SW (fun s => ∑ s' ∈ range (s + 1), M.factorial * rT c.E c.GM J rows M s') (c.GM + 1) :=
      pk_congr _ _ _ _ fun s _ => by unfold prT; rw [Finset.mul_sum]
    rw [hOw, hPR]
    exact envUnit_spec c sh M c.NN (fun s => M.factorial * rT c.E c.GM J rows M s) hsh
      (guard_four c hG) (guard_rT c rows hrows hG J hJ M (by omega))
  · rw [mem_Ico] at hM
    rw [mkTab_R c rows hrows hG J hJ M, mkTab_PR c rows hrows hG J hJ M, ite_eq_right (by omega),
      ite_eq_right (by omega)]
    exact envUnit_zero _ _ _ _ _ _

theorem famA_eq (c : ConvCfg) (rows : List ℕ) (hrows : RowsOK c.E c.GM rows) (hG : Guard c)
    (VM sh used : ℕ) (hsh : sh ≤ c.GM) (v : ℕ) (hv : v ≤ VM) :
    getN (famA c VM sh used (omRows c.SW c.NN (3 * c.E - 2))
        (mkTab c (buildX c rows) (sqQ c (buildX c rows)) c.E)) v =
      if bit used v then
        pk c.SW (fun t => ∑ M ∈ range (3 * c.E - 2),
          envS c.NN M (c.Q0 - t) sh (M + v) (fun s => M.factorial * rT c.E c.GM c.E rows M s)) c.E
      else 0 := by
  set t := mkTab c (buildX c rows) (sqQ c (buildX c rows)) c.E with ht
  set oms := omRows c.SW c.NN (3 * c.E - 2) with homs
  let Ow : ℕ → ℕ → ℕ → ℕ := fun M v O =>
    Nat.shiftRight (Nat.land (Nat.shiftRight O (Nat.mul (Nat.sub c.NN (minN (Nat.add M VM) c.NN)) c.SW))
      (mask (Nat.mul (Nat.sub (minN (Nat.add M VM) c.NN) (Nat.div (Nat.mul 4 M) 3)) c.SW)))
      (Nat.mul (Nat.sub (minN (Nat.add M VM) c.NN) (minN (Nat.add M v) c.NN)) c.SW)
  let upd : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ := fun M v x O R PR =>
    cond (Nat.beq (Nat.land (Nat.shiftRight used v) 1) 1)
      (Nat.add x (envUnit c sh M (Nat.add M v) (Ow M v O) O R PR)) x
  let F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ := fun M v O R PR =>
    if bit used v then envUnit c sh M (Nat.add M v) (Ow M v O) O R PR else 0
  have hupd : ∀ M v x O R PR, upd M v x O R PR = x + F M v O R PR := by
    intro M v x O R PR
    simp only [upd, F]
    by_cases hb : bit used v = true
    · have hb' : Nat.beq (Nat.land (Nat.shiftRight used v) 1) 1 = true := hb
      rw [hb', Bool.cond_true, ite_eq_left hb]
      rfl
    · have hb' : Nat.beq (Nat.land (Nat.shiftRight used v) 1) 1 = false := Bool.eq_false_iff.mpr hb
      rw [hb', Bool.cond_false, ite_eq_right hb]
      rfl
  have key : famA c VM sh used oms t = (List.range (VM + 1)).map (fun v =>
      ∑ M ∈ range (3 * c.E - 2), F M v (getN oms M) (getN t.R M) (getN t.PR M)) :=
    congrArg Prod.fst (outer_fold (3 * c.E - 2) (VM + 1) oms t.R t.PR upd F hupd)
  rw [key, getN_map_range _ _ _ (by omega)]
  by_cases hb : bit used v = true
  · rw [ite_eq_left hb, ← pk_sum]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [mem_range] at hM
    simp only [F, ite_eq_left hb]
    rw [omRows_getN _ _ _ _ hM, mkTab_R c rows hrows hG c.E le_rfl M,
      mkTab_PR c rows hrows hG c.E le_rfl M, ite_eq_left (by omega), ite_eq_left (by omega)]
    have hPR : pk c.SW (fun s => M.factorial * prT c.E c.GM c.E rows M s) (c.GM + 1) =
        pk c.SW (fun s => ∑ s' ∈ range (s + 1), M.factorial * rT c.E c.GM c.E rows M s')
          (c.GM + 1) :=
      pk_congr _ _ _ _ fun s _ => by unfold prT; rw [Finset.mul_sum]
    simp only [Ow]
    rw [famA_Ow c M VM v hv (guard_four c hG), hPR, Nat.add_eq]
    exact envUnit_spec c sh M (M + v) (fun s => M.factorial * rT c.E c.GM c.E rows M s) hsh
      (guard_four c hG) (guard_rT c rows hrows hG c.E le_rfl M (by omega))
  · rw [ite_eq_right hb]
    exact Finset.sum_eq_zero fun M _ => by simp only [F, ite_eq_right hb]

/-! ## The real values -/

theorem mult4_choose (n M e0 e1 e2 : ℕ) (_hM : e0 + e1 + e2 = M) (hn : M ≤ n) :
    mult4 n (n - M) e0 e1 e2 =
      (n.choose M : ℝ) * ((M.factorial : ℝ) / (e0.factorial * e1.factorial * e2.factorial)) / 4 ^ n := by
  unfold mult4
  have hf : (n.factorial : ℝ) = n.choose M * M.factorial * (n - M).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hn).symm
  rw [hf]
  have h1 : ((n - M).factorial : ℝ) ≠ 0 := by positivity
  have h2 : (e0.factorial : ℝ) ≠ 0 := by positivity
  have h3 : (e1.factorial : ℝ) ≠ 0 := by positivity
  have h4 : (e2.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem om_div (NN M n : ℕ) (hn : n ≤ NN) :
    ((om NN M n : ℕ) : ℝ) / 4 ^ NN = (n.choose M : ℝ) / 4 ^ n := by
  unfold om
  have h4 : (4 : ℝ) ^ NN = 4 ^ n * 4 ^ (NN - n) := by rw [← pow_add, Nat.add_sub_cancel' hn]
  rw [h4, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_mul_right _ _ (by positivity)]

theorem om_zero_of_lt (NN M n : ℕ) (hn : n < M) : om NN M n = 0 := by
  unfold om
  rw [Nat.choose_eq_zero_of_lt hn, zero_mul]

theorem WB_val (q K NN : ℕ) (e : Fin 3 → ℕ) (hK0 : 0 < K) (hK : K ≤ NN + 1) (s' : ℕ) :
    WB q K e s' = if q + s' ≤ K - 1 then
      ((e 0 + e 1 + e 2).factorial / ((e 0).factorial * (e 1).factorial * (e 2).factorial) / 4 ^ NN : ℝ) *
        (om NN (e 0 + e 1 + e 2) (q + s') : ℝ) else 0 := by
  unfold WB
  by_cases h1 : q + s' ≤ K - 1
  · rw [ite_eq_left h1]
    by_cases h2 : e 0 + e 1 + e 2 ≤ q + s'
    · rw [ite_eq_left (show e 0 + e 1 + e 2 ≤ q + s' ∧ q + s' < K from ⟨h2, by omega⟩),
        mult4_choose (q + s') (e 0 + e 1 + e 2) (e 0) (e 1) (e 2) rfl h2]
      have := om_div NN (e 0 + e 1 + e 2) (q + s') (by omega)
      calc _ = ((e 0 + e 1 + e 2).factorial / ((e 0).factorial * (e 1).factorial * (e 2).factorial) : ℝ) *
            (((q + s').choose (e 0 + e 1 + e 2) : ℕ) / 4 ^ (q + s')) := by ring
        _ = _ := by rw [← this]; ring
    · rw [ite_eq_right (show ¬(e 0 + e 1 + e 2 ≤ q + s' ∧ q + s' < K) by omega),
        om_zero_of_lt _ _ _ (by omega)]
      simp
  · rw [ite_eq_right (show ¬(e 0 + e 1 + e 2 ≤ q + s' ∧ q + s' < K) by omega), ite_eq_right h1]

theorem WA_val (q v n0 NN : ℕ) (e : Fin 3 → ℕ) (hn00 : 0 < n0) (hn0 : n0 ≤ NN + 1) (s' : ℕ) :
    WA q v n0 e s' = if q + s' ≤ min (n0 - 1) (e 0 + e 1 + e 2 + v) then
      ((e 0 + e 1 + e 2).factorial / ((e 0).factorial * (e 1).factorial * (e 2).factorial) / 4 ^ NN : ℝ) *
        (om NN (e 0 + e 1 + e 2) (q + s') : ℝ) else 0 := by
  unfold WA
  by_cases h1 : q + s' ≤ min (n0 - 1) (e 0 + e 1 + e 2 + v)
  · rw [ite_eq_left h1]
    by_cases h2 : e 0 + e 1 + e 2 ≤ q + s'
    · rw [ite_eq_left (show e 0 + e 1 + e 2 ≤ q + s' ∧ q + s' - (e 0 + e 1 + e 2) ≤ v ∧ q + s' < n0 from
          ⟨h2, by omega, by omega⟩),
        mult4_choose (q + s') (e 0 + e 1 + e 2) (e 0) (e 1) (e 2) rfl h2]
      have := om_div NN (e 0 + e 1 + e 2) (q + s') (by omega)
      calc _ = ((e 0 + e 1 + e 2).factorial / ((e 0).factorial * (e 1).factorial * (e 2).factorial) : ℝ) *
            (((q + s').choose (e 0 + e 1 + e 2) : ℕ) / 4 ^ (q + s')) := by ring
        _ = _ := by rw [← this]; ring
    · rw [ite_eq_right (show ¬(e 0 + e 1 + e 2 ≤ q + s' ∧ q + s' - (e 0 + e 1 + e 2) ≤ v ∧ q + s' < n0)
          by omega), om_zero_of_lt _ _ _ (by omega)]
      simp
  · rw [ite_eq_right (show ¬(e 0 + e 1 + e 2 ≤ q + s' ∧ q + s' - (e 0 + e 1 + e 2) ≤ v ∧ q + s' < n0)
      by omega), ite_eq_right h1]

theorem fold_max_shift (s S q top : ℕ) (f : ℕ → ℕ) (a : ℝ) (ha : 0 ≤ a) (htop : top ≤ q + S) :
    (Icc s S).fold max 0 (fun s' => if q + s' ≤ top then a * (f (q + s') : ℝ) else 0) =
      a * (((Icc (q + s) top).sup f : ℕ) : ℝ) := by
  apply le_antisymm
  · rw [Finset.fold_max_le]
    refine ⟨by positivity, fun s' hs' => ?_⟩
    rw [mem_Icc] at hs'
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast Finset.le_sup (f := f) (mem_Icc.2 ⟨by omega, h⟩)) ha
    · positivity
  · rcases (Icc (q + s) top).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sup_empty, Finset.le_fold_max]
      left
      simp
    · obtain ⟨n, hn, hsup⟩ := Finset.exists_mem_eq_sup _ hne f
      rw [hsup, Finset.le_fold_max]
      right
      rw [mem_Icc] at hn
      refine ⟨n - q, mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
      rw [ite_eq_left (show q + (n - q) ≤ top by omega), show q + (n - q) = n by omega]

theorem envelope_WB (q K s NN : ℕ) (e : Fin 3 → ℕ) (hK0 : 0 < K) (hK : K ≤ NN + 1) :
    envelope (WB q K e) K s =
      ((e 0 + e 1 + e 2).factorial / ((e 0).factorial * (e 1).factorial * (e 2).factorial) : ℝ) *
        (envW NN (e 0 + e 1 + e 2) q s (K - 1) : ℝ) / 4 ^ NN := by
  have hW : WB q K e = fun s' => if q + s' ≤ K - 1 then
      ((e 0 + e 1 + e 2).factorial / ((e 0).factorial * (e 1).factorial * (e 2).factorial) / 4 ^ NN : ℝ) *
        (om NN (e 0 + e 1 + e 2) (q + s') : ℝ) else 0 := funext (WB_val q K NN e hK0 hK)
  unfold envelope envW
  rw [hW, fold_max_shift s K q (K - 1) (om NN (e 0 + e 1 + e 2)) _ (by positivity) (by omega)]
  ring

theorem envelope_WA (q v n0 s NN : ℕ) (e : Fin 3 → ℕ) (hn00 : 0 < n0) (hn0 : n0 ≤ NN + 1) :
    envelope (WA q v n0 e) n0 s =
      ((e 0 + e 1 + e 2).factorial / ((e 0).factorial * (e 1).factorial * (e 2).factorial) : ℝ) *
        (envW NN (e 0 + e 1 + e 2) q s (min (n0 - 1) (e 0 + e 1 + e 2 + v)) : ℝ) / 4 ^ NN := by
  have hW : WA q v n0 e = fun s' => if q + s' ≤ min (n0 - 1) (e 0 + e 1 + e 2 + v) then
      ((e 0 + e 1 + e 2).factorial / ((e 0).factorial * (e 1).factorial * (e 2).factorial) / 4 ^ NN : ℝ) *
        (om NN (e 0 + e 1 + e 2) (q + s') : ℝ) else 0 := funext (WA_val q v n0 NN e hn00 hn0)
  unfold envelope envW
  rw [hW, fold_max_shift s n0 q _ (om NN (e 0 + e 1 + e 2)) _ (by positivity) (by omega)]
  ring

theorem plF_xv (E GM : ℕ) (rows : List ℕ) (hrows : RowsOK E GM rows) (F : ℕ → ℕ → ℝ)
    (hF : ∀ e ≤ E, ∀ g ≤ GM, F e g = (rv rows e g : ℝ) / 2 ^ 52) (e : ℕ) (he : e < E) (g : ℕ) :
    plF F GM e g = (xv E GM rows e g : ℝ) * e.factorial / ((E - 1).factorial * 2 ^ 52) := by
  unfold plF xv
  have hE : ((E - 1).factorial : ℝ) ≠ 0 := by positivity
  have he' : (e.factorial : ℝ) ≠ 0 := by positivity
  by_cases hg : g ≤ GM
  · rw [ite_eq_left hg, ite_eq_left (show e < E ∧ g ≤ GM from ⟨he, hg⟩)]
    have hdvd : e.factorial ∣ (E - 1).factorial := Nat.factorial_dvd_factorial (by omega)
    have hsub : (if g = 0 then 0 else rv rows e (g - 1)) ≤ rv rows e g := by
      split_ifs with h0
      · exact Nat.zero_le _
      · have := hrows.2 e he.le (g - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega)] at this
    rw [Nat.cast_mul, Nat.cast_div hdvd he', Nat.cast_sub hsub, hF e he.le g hg]
    split_ifs with h0
    · simp only [Nat.cast_zero, sub_zero]
      field_simp
    · rw [hF e he.le (g - 1) (by omega)]
      field_simp
  · rw [ite_eq_right hg, ite_eq_right (show ¬(e < E ∧ g ≤ GM) by omega)]
    simp

theorem convF_xv (E GM : ℕ) (rows : List ℕ) (hrows : RowsOK E GM rows) (F : ℕ → ℕ → ℝ)
    (hF : ∀ e ≤ E, ∀ g ≤ GM, F e g = (rv rows e g : ℝ) / 2 ^ 52) (e : Fin 3 → ℕ) (he : ∀ c, e c < E) (s : ℕ) :
    convF F GM e s =
      (∑ g0 ∈ Finset.range (GM + 1), ∑ g1 ∈ Finset.range (GM + 1), ∑ g2 ∈ Finset.range (GM + 1),
        if g0 + g1 + g2 = s then
          (xv E GM rows (e 0) g0 * xv E GM rows (e 1) g1 * xv E GM rows (e 2) g2 : ℝ) else 0) *
        ((e 0).factorial * (e 1).factorial * (e 2).factorial) / ((E - 1).factorial ^ 3 * 2 ^ 156) := by
  set p : ℕ → ℕ → ℝ := fun e' g => (xv E GM rows e' g : ℝ) * e'.factorial / ((E - 1).factorial * 2 ^ 52)
    with hp
  have hpl : ∀ c g, plF F GM (e c) g = p (e c) g := fun c g => plF_xv E GM rows hrows F hF (e c) (he c) g
  have hz : ∀ c g, GM < g → p (e c) g = 0 := by
    intro c g hg
    simp only [hp, xv, ite_eq_right (show ¬(e c < E ∧ g ≤ GM) by omega)]
    simp
  have h2 : convF F GM e s = ∑ g0 ∈ range (GM + 1), ∑ g1 ∈ range (GM + 1), ∑ g2 ∈ range (GM + 1),
      if g0 + g1 + g2 = s then p (e 0) g0 * p (e 1) g1 * p (e 2) g2 else 0 := by
    unfold convF
    refine sum_congr rfl fun g0 _ => sum_congr rfl fun g1 _ => ?_
    simp only [hpl]
    by_cases h : g0 + g1 ≤ s
    · rw [ite_eq_left h]
      have : ∀ g2 ∈ range (GM + 1), (if g0 + g1 + g2 = s then p (e 0) g0 * p (e 1) g1 * p (e 2) g2 else 0) =
          if s - g0 - g1 = g2 then p (e 0) g0 * p (e 1) g1 * p (e 2) g2 else 0 := by
        intro g2 _
        by_cases h' : g0 + g1 + g2 = s
        · rw [ite_eq_left h', ite_eq_left (show s - g0 - g1 = g2 by omega)]
        · rw [ite_eq_right h', ite_eq_right (show ¬(s - g0 - g1 = g2) by omega)]
      rw [sum_congr rfl this, sum_ite_eq]
      by_cases hm : s - g0 - g1 ∈ range (GM + 1)
      · rw [ite_eq_left hm]
      · rw [ite_eq_right hm, hz 2 _ (by rw [mem_range] at hm; omega), mul_zero]
    · rw [ite_eq_right h]
      exact (sum_eq_zero fun g2 _ => ite_eq_right (by omega)).symm
  rw [h2, mul_div_assoc, sum_mul]
  refine sum_congr rfl fun g0 _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun g1 _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun g2 _ => ?_
  rw [ite_mul, zero_mul]
  by_cases h : g0 + g1 + g2 = s
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [hp]
    have hE : ((E - 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · rw [ite_eq_right h, ite_eq_right h]

theorem sum_piFinset3 (A B C : Finset ℕ) (G : ℕ → ℕ → ℕ → ℝ) :
    ∑ e ∈ Fintype.piFinset (fun c : Fin 3 => if c = 0 then A else if c = 1 then B else C),
        G (e 0) (e 1) (e 2) =
      ∑ e0 ∈ A, ∑ e1 ∈ B, ∑ e2 ∈ C, G e0 e1 e2 := by
  simp_rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun e => (e 0, e 1, e 2)) (fun x => ![x.1, x.2.1, x.2.2]) ?_ ?_ ?_ ?_ ?_
  · intro e he
    rw [Fintype.mem_piFinset] at he
    have h0 := he 0
    have h1 := he 1
    have h2 := he 2
    simp only [Fin.isValue, ite_true, Fin.reduceEq, ite_false] at h0 h1 h2
    simp only [Finset.mem_product]
    exact ⟨h0, h1, h2⟩
  · intro x hx
    simp only [Finset.mem_product] at hx
    rw [Fintype.mem_piFinset]
    intro c
    fin_cases c <;> simp [hx.1, hx.2.1, hx.2.2]
  · intro e _
    funext c
    fin_cases c <;> rfl
  · intro x _
    rfl
  · intro e _
    rfl

theorem envSum_exch (E GM J : ℕ) (rows : List ℕ) (L n : ℕ) (W : ℕ → ℕ → ℕ)
    (hL : ∀ e0 < J, ∀ e1 < E, ∀ e2 < E, e0 + e1 + e2 < L) :
    ∑ M ∈ range L, ∑ s ∈ range n, W M s * (M.factorial * rT E GM J rows M s) =
      ∑ e0 ∈ range J, ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ s ∈ range n,
        W (e0 + e1 + e2) s * ((e0 + e1 + e2).factorial * xs3 E GM rows e0 e1 e2 s) := by
  simp only [rT_reshape, mul_sum, mul_ite, mul_zero]
  conv_lhs =>
    rw [sum_comm]
    enter [2, s]
    rw [sum_comm]
    enter [2, e0]
    rw [sum_comm]
    enter [2, e1]
    rw [sum_comm]
  conv_lhs =>
    rw [sum_comm]
    enter [2, e0]
    rw [sum_comm]
    enter [2, e1]
    rw [sum_comm]
  refine sum_congr rfl fun e0 he0 => sum_congr rfl fun e1 he1 => sum_congr rfl fun e2 he2 =>
    sum_congr rfl fun s _ => ?_
  rw [mem_range] at he0 he1 he2
  rw [sum_ite_eq, ite_eq_left (mem_range.2 (hL e0 he0 e1 he1 e2 he2))]

theorem envW_empty (NN M q s top : ℕ) (h : top < q + s) : envW NN M q s top = 0 := by
  unfold envW
  rw [Icc_eq_empty_of_lt h, sup_empty]
  rfl

theorem real_term (w xs M fE NN a0 a1 a2 : ℕ) :
    ((M.factorial : ℝ) / ((a0.factorial : ℝ) * a1.factorial * a2.factorial)) * (w : ℝ) / 4 ^ NN *
      ((xs : ℝ) * ((a0.factorial : ℝ) * a1.factorial * a2.factorial) / ((fE.factorial : ℝ) ^ 3 * 2 ^ 156)) =
    ((w * (M.factorial * xs) : ℕ) : ℝ) / ((fE.factorial : ℝ) ^ 3 * 2 ^ (156 + 2 * NN)) := by
  have h4 : (2 : ℝ) ^ (156 + 2 * NN) = 2 ^ 156 * 4 ^ NN := by
    rw [pow_add, pow_mul]
    norm_num
  rw [h4]
  push_cast
  field_simp

theorem xs3_cast (E GM : ℕ) (rows : List ℕ) (e0 e1 e2 s : ℕ) :
    ((xs3 E GM rows e0 e1 e2 s : ℕ) : ℝ) = ∑ g0 ∈ range (GM + 1), ∑ g1 ∈ range (GM + 1),
      ∑ g2 ∈ range (GM + 1), if g0 + g1 + g2 = s then
        (xv E GM rows e0 g0 * xv E GM rows e1 g1 * xv E GM rows e2 g2 : ℝ) else 0 := by
  unfold xs3
  push_cast
  rfl


/-- The main term of `boundB` at `q`, `J`, `K` is the envelope sum over `Den`. -/
theorem boundB_main (E GM : ℕ) (rows : List ℕ) (hrows : RowsOK E GM rows) (F : ℕ → ℕ → ℝ)
    (hF : ∀ e ≤ E, ∀ g ≤ GM, F e g = (rv rows e g : ℝ) / 2 ^ 52)
    (q J K : ℕ) (hq : q ≤ E + 1) (hJ1 : 1 ≤ J) (hJ : J ≤ E) (hK : q < K) (hKG : K - q - 1 ≤ GM) :
    ∑ e ∈ Fintype.piFinset (fun c : Fin 3 => if c = 0 then range J else range E),
        ∑ s ∈ range K, envelope (WB q K e) K s * convF F GM e s =
      (∑ M ∈ range (J + 2 * E - 2),
          envS (E + GM + 1) M q (K - q - 1) (E + GM + 1) (fun s => M.factorial * rT E GM J rows M s) : ℝ) /
        ((E - 1).factorial ^ 3 * 2 ^ (156 + 2 * (E + GM + 1))) := by
  set NN := E + GM + 1 with hNN
  set W : ℕ → ℕ → ℕ := fun M s => if q + s ≤ NN then envW NN M q s (min (q + (K - q - 1)) NN) else 0
    with hW
  have hS : ∀ M, envS NN M q (K - q - 1) NN (fun s => M.factorial * rT E GM J rows M s) =
      ∑ s ∈ range (K - q - 1 + 1), W M s * (M.factorial * rT E GM J rows M s) := by
    intro M
    unfold envS
    refine sum_congr rfl fun s _ => ?_
    simp only [hW]
    split_ifs <;> simp
  have key : ∑ M ∈ range (J + 2 * E - 2),
      envS NN M q (K - q - 1) NN (fun s => M.factorial * rT E GM J rows M s) =
      ∑ e0 ∈ range J, ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ s ∈ range (K - q - 1 + 1),
        W (e0 + e1 + e2) s * ((e0 + e1 + e2).factorial * xs3 E GM rows e0 e1 e2 s) := by
    rw [sum_congr rfl fun M _ => hS M]
    exact envSum_exch E GM J rows _ _ W fun e0 h0 e1 h1 e2 h2 => by omega
  rw [← Nat.cast_sum, key]
  have hG := sum_piFinset3 (range J) (range E) (range E) (fun e0 e1 e2 =>
    ∑ s ∈ range (K - q - 1 + 1), ((W (e0 + e1 + e2) s * ((e0 + e1 + e2).factorial *
      xs3 E GM rows e0 e1 e2 s) : ℕ) : ℝ) / ((E - 1).factorial ^ 3 * 2 ^ (156 + 2 * NN)))
  simp only [ite_self] at hG
  simp only [Nat.cast_sum, sum_div]
  rw [← hG]
  refine sum_congr rfl fun e he => ?_
  rw [Fintype.mem_piFinset] at he
  have he' : ∀ c, e c < E := by
    intro c
    have := he c
    split_ifs at this <;> rw [mem_range] at this <;> omega
  rw [← sum_range_add_sum_Ico _ (show K - q - 1 + 1 ≤ K by omega),
    sum_eq_zero (s := Ico _ _) (fun s hs => ?_), add_zero]
  · refine sum_congr rfl fun s hs => ?_
    rw [mem_range] at hs
    rw [envelope_WB q K s NN e (by omega) (by omega), convF_xv E GM rows hrows F hF e he' s,
      ← xs3_cast, real_term]
    simp only [hW]
    rw [ite_eq_left (show q + s ≤ NN by omega), show min (q + (K - q - 1)) NN = K - 1 by omega]
  · rw [mem_Ico] at hs
    rw [envelope_WB q K s NN e (by omega) (by omega), envW_empty _ _ _ _ _ (by omega)]
    simp

/-- The main term of `boundA` at `q`, `v`, `n0` is the envelope sum over `Den`. -/
theorem boundA_main (E GM : ℕ) (rows : List ℕ) (hrows : RowsOK E GM rows) (F : ℕ → ℕ → ℝ)
    (hF : ∀ e ≤ E, ∀ g ≤ GM, F e g = (rv rows e g : ℝ) / 2 ^ 52)
    (q v n0 : ℕ) (hq : q ≤ E + 1) (hE : 1 ≤ E) (hn0 : q < n0) (hnG : n0 - q - 1 ≤ GM) :
    ∑ e ∈ Fintype.piFinset (fun _ : Fin 3 => range E),
        ∑ s ∈ range n0, envelope (WA q v n0 e) n0 s * convF F GM e s =
      (∑ M ∈ range (3 * E - 2),
          envS (E + GM + 1) M q (n0 - q - 1) (M + v) (fun s => M.factorial * rT E GM E rows M s) : ℝ) /
        ((E - 1).factorial ^ 3 * 2 ^ (156 + 2 * (E + GM + 1))) := by
  set NN := E + GM + 1 with hNN
  set W : ℕ → ℕ → ℕ := fun M s =>
    if q + s ≤ M + v then envW NN M q s (min (q + (n0 - q - 1)) (M + v)) else 0 with hW
  have hS : ∀ M, envS NN M q (n0 - q - 1) (M + v) (fun s => M.factorial * rT E GM E rows M s) =
      ∑ s ∈ range (n0 - q - 1 + 1), W M s * (M.factorial * rT E GM E rows M s) := by
    intro M
    unfold envS
    refine sum_congr rfl fun s _ => ?_
    simp only [hW]
    split_ifs <;> simp
  have key : ∑ M ∈ range (3 * E - 2),
      envS NN M q (n0 - q - 1) (M + v) (fun s => M.factorial * rT E GM E rows M s) =
      ∑ e0 ∈ range E, ∑ e1 ∈ range E, ∑ e2 ∈ range E, ∑ s ∈ range (n0 - q - 1 + 1),
        W (e0 + e1 + e2) s * ((e0 + e1 + e2).factorial * xs3 E GM rows e0 e1 e2 s) := by
    rw [sum_congr rfl fun M _ => hS M]
    exact envSum_exch E GM E rows _ _ W fun e0 h0 e1 h1 e2 h2 => by omega
  rw [← Nat.cast_sum, key]
  have hG := sum_piFinset3 (range E) (range E) (range E) (fun e0 e1 e2 =>
    ∑ s ∈ range (n0 - q - 1 + 1), ((W (e0 + e1 + e2) s * ((e0 + e1 + e2).factorial *
      xs3 E GM rows e0 e1 e2 s) : ℕ) : ℝ) / ((E - 1).factorial ^ 3 * 2 ^ (156 + 2 * NN)))
  simp only [ite_self] at hG
  simp only [Nat.cast_sum, sum_div]
  rw [← hG]
  refine sum_congr rfl fun e he => ?_
  rw [Fintype.mem_piFinset] at he
  have he' : ∀ c, e c < E := fun c => mem_range.1 (he c)
  rw [← sum_range_add_sum_Ico _ (show n0 - q - 1 + 1 ≤ n0 by omega),
    sum_eq_zero (s := Ico _ _) (fun s hs => ?_), add_zero]
  · refine sum_congr rfl fun s hs => ?_
    rw [mem_range] at hs
    rw [envelope_WA q v n0 s NN e (by omega) (by omega), convF_xv E GM rows hrows F hF e he' s,
      ← xs3_cast, real_term]
    simp only [hW]
    by_cases hv : q + s ≤ e 0 + e 1 + e 2 + v
    · rw [ite_eq_left hv, show min (q + (n0 - q - 1)) (e 0 + e 1 + e 2 + v) =
        min (n0 - 1) (e 0 + e 1 + e 2 + v) by omega]
    · rw [ite_eq_right hv, envW_empty _ _ _ _ _ (by omega)]
  · rw [mem_Ico] at hs
    rw [envelope_WA q v n0 s NN e (by omega) (by omega), envW_empty _ _ _ _ _ (by omega)]
    simp

end FrogModel.D3.LaneD
