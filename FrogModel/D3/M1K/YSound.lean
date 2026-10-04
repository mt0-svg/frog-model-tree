module

public import FrogModel.D3.M1K.Closure

@[expose] public section

/-!
# The H tables of the checker are below the H recursion of `M1_60`

`yTabs st` computes `Y_f(0..P)`, `f = 0..3`, with `p_L = 1/3`: the step is
`⌊⌊num/D⌋ c_f/D⌋`, `num = 3 D up + 2 (3 - f) D same + 3 f acc`, `c_f = ⌊D/(9 + f)⌋`. Under the
condition (H) at `L = 60`, `2 (3 - f) ≤ 3 (3 - f) (1 - p_L)` and `c_f (12 - 3 (3 - f) p_L) ≤ D`
(`H1`, `H2`), this is at most the exact step of the H recursion of `M1_60` (Section 13 of the paper)
on the same arguments (`ystep_real`), so the computed tables are a sub-solution of `Yrec`
(`yrec_lower`) and the computed kernels `Y_t(1)` are below `KhatH` (`ytabs_sound`).
-/

open FrogModel.Lanes FrogModel.D3.Iface

namespace FrogModel.D3.M1K

/-- The column of `rbCol`: slot `a` the first marginal at `V - a`. -/
def rbv (st : St) (a : ℕ) : ℕ :=
  if a ≤ V then ∑ g ∈ Finset.range 4, lane st.rho (4 * (V - a) + g) else 0

/-- `rhobar(b)` in units of `2^-62`. -/
def rbar (st : St) (b : ℕ) : ℕ := ∑ g ∈ Finset.range 4, lane st.rho (4 * b + g)

/-- The event lanes of the H recursion of the count `f`, read on the rows `R` of `Y_(f-1)`. -/
def yE (st : St) (f : ℕ) (R : ℕ → ℕ → ℕ) (j l : ℕ) : ℕ :=
  3 * f * ∑ b ∈ Finset.range (V + 1), rbar st b * R (min (j + b) P) l

/-- The lanes of `Y_f`, read on the rows `R` of `Y_(f-1)`. -/
def yL (st : St) (f : ℕ) (R : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ :=
  laneSeq (fun l => if l = f then D else 0) (yE st f R) (3 * D) (2 * (3 - f) * D) (D / (9 + f))

/-- The lanes of the four tables `Y_0 .. Y_3`. -/
def YF (st : St) : ℕ → ℕ → ℕ → ℕ
  | 0 => yL st 0 (fun _ _ => 0)
  | f + 1 => yL st (f + 1) (YF st f)

/-! ## Leaves -/

theorem rbCol_eq (st : St) : rbCol st = pack RB 64 (rbv st) := by
  unfold rbCol
  rw [packTree_eq]
  refine pack_congr _ _ _ _ fun a _ => ?_
  unfold rbv
  rw [zero_add]
  by_cases ha : a ≤ V
  · rw [show Nat.ble a V = true from Nat.ble_eq.mpr ha, ite_eq_left ha]
    show natFold 4 0 (fun g acc => Nat.add acc (lane st.rho (Nat.add (Nat.mul 4 (Nat.sub V a)) g))) = _
    rw [natFold_sum]
    rfl
  · rw [show Nat.ble a V = false from Bool.eq_false_iff.mpr (fun e => ha (Nat.ble_eq.mp e)), ite_eq_right ha]
    rfl

theorem rbv_le (st : St) (hs : validSt st = true) (a : ℕ) : rbv st a ≤ 2 ^ 62 := by
  have hr : validRow st.rho = true := by
    unfold validSt at hs
    simp only [Bool.and_eq_true] at hs
    exact hs.1.1
  clear hs
  unfold validRow at hr
  simp only [Bool.and_eq_true, Nat.beq_eq] at hr
  have hsum := hr.2
  rw [sumLanes_eq] at hsum
  unfold rbv
  split_ifs with ha
  · clear hr
    calc ∑ g ∈ Finset.range 4, lane st.rho (4 * (V - a) + g)
        = ∑ l ∈ Finset.Ico (4 * (V - a)) (4 * (V - a) + 4), lane st.rho l := by
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      _ ≤ ∑ l ∈ Finset.range NL, lane st.rho l := Finset.sum_le_sum_of_subset fun l hl => by
          simp only [Finset.mem_Ico, Finset.mem_range] at hl ⊢
          simp only [NL]; simp only [V] at ha hl; omega
      _ = 2 ^ 62 := hsum
  · exact Nat.zero_le _

theorem getL_eq (l : List (List ℕ)) (i : ℕ) : getL l i = l.getD i [] := by
  have h : ∀ i, natFold i l (fun _ acc => acc.tail) = l.drop i := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [natFold_succ, ih, List.tail_drop]
  unfold getL
  rw [h, List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

/-- Condition (H), first part, at `L = 60`. -/
theorem H1 (f : ℕ) (hf : f ≤ 3) : 2 * (3 - (f : ℝ)) ≤ 3 * (3 - (f : ℝ)) * (1 - pL 60) := by
  have h := pL_le_third 60 (by norm_num)
  have hf' : (f : ℝ) ≤ 3 := by exact_mod_cast hf
  nlinarith

/-- Condition (H), second part, at `L = 60`. -/
theorem H2 (f : ℕ) (hf : f ≤ 3) :
    ((2 ^ 62 / (9 + f) : ℕ) : ℝ) * (12 - 3 * (3 - (f : ℝ)) * pL 60) ≤ 2 ^ 62 := by
  unfold pL
  interval_cases f <;> norm_num

/-- The rounded H step is at most the exact H step of `M1_60` on its own arguments. -/
theorem ystep_real (f : ℕ) (hf : f ≤ 3) (F E : ℕ → ℕ) (l : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hE : (E l : ℝ) ≤ 3 * f * 2 ^ 124 * A) :
    (stepL (3 * D) (2 * (3 - f) * D) (D / (9 + f)) F E l : ℝ) / 2 ^ 62 ≤
      (1 / 4 * ((upL F l : ℝ) / 2 ^ 62) + (3 - (f : ℝ)) / 4 * (1 - pL 60) * ((F l : ℝ) / 2 ^ 62) +
          (f : ℝ) / 4 * A) / (1 - (3 - (f : ℝ)) * pL 60 / 4) := by
  have hp0 := pL_nonneg 60 (by norm_num)
  have hp1 := pL_le_third 60 (by norm_num)
  have hf' : (f : ℝ) ≤ 3 := by exact_mod_cast hf
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have h1 := H1 f hf
  have h2 := H2 f hf
  have hden : 0 < 12 - 3 * (3 - (f : ℝ)) * pL 60 := by nlinarith
  have hc : ((D / (9 + f) : ℕ) : ℝ) ≤ 2 ^ 62 / (12 - 3 * (3 - (f : ℝ)) * pL 60) := by
    rw [le_div_iff₀ hden, D_eq]; exact h2
  set c := D / (9 + f) with hcdef
  set num := 3 * D * upL F l + 2 * (3 - f) * D * F l + E l with hnum
  have e1 : (stepL (3 * D) (2 * (3 - f) * D) c F E l : ℝ) ≤ (c : ℝ) * ((num : ℝ) / 2 ^ 62) / 2 ^ 62 := by
    have hW : (2 : ℕ) ^ W = 2 ^ 62 := rfl
    unfold stepL
    rw [hW]
    calc ((c * (num / 2 ^ 62) / 2 ^ 62 : ℕ) : ℝ) ≤ ((c * (num / 2 ^ 62) : ℕ) : ℝ) / ((2 ^ 62 : ℕ) : ℝ) :=
          Nat.cast_div_le
      _ ≤ (c : ℝ) * ((num : ℝ) / 2 ^ 62) / 2 ^ 62 := by
          push_cast
          gcongr
          · exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := num) (n := 2 ^ 62))
          all_goals norm_num
  have hnumR : (num : ℝ) = 3 * 2 ^ 62 * (upL F l : ℝ) + 2 * (3 - (f : ℝ)) * 2 ^ 62 * (F l : ℝ) + E l := by
    rw [hnum, D_eq]; push_cast [Nat.cast_sub hf]; ring
  set u : ℝ := (upL F l : ℝ) / 2 ^ 62 with hu
  set w : ℝ := (F l : ℝ) / 2 ^ 62 with hw
  have hu0 : 0 ≤ u := by positivity
  have hw0 : 0 ≤ w := by positivity
  have hq : 0 ≤ 3 * (3 - (f : ℝ)) * (1 - pL 60) := by
    have : 0 ≤ 3 - (f : ℝ) := by linarith
    have : 0 ≤ 1 - pL 60 := by linarith
    positivity
  have hN : (num : ℝ) / 2 ^ 124 ≤ 3 * u + 3 * (3 - (f : ℝ)) * (1 - pL 60) * w + 3 * f * A := by
    have e : (num : ℝ) / 2 ^ 124 = 3 * u + 2 * (3 - (f : ℝ)) * w + (E l : ℝ) / 2 ^ 124 := by
      rw [hnumR, hu, hw]; field_simp
    have h3 : 2 * (3 - (f : ℝ)) * w ≤ 3 * (3 - (f : ℝ)) * (1 - pL 60) * w :=
      mul_le_mul_of_nonneg_right h1 hw0
    have h4 : (E l : ℝ) / 2 ^ 124 ≤ 3 * f * A := by
      rw [div_le_iff₀ (by positivity)]; linarith
    rw [e]; linarith
  have hN0 : 0 ≤ 3 * u + 3 * (3 - (f : ℝ)) * (1 - pL 60) * w + 3 * f * A :=
    add_nonneg (add_nonneg (by positivity) (mul_nonneg hq hw0)) (mul_nonneg (by positivity) hA)
  have hcd : (c : ℝ) / 2 ^ 62 ≤ 1 / (12 - 3 * (3 - (f : ℝ)) * pL 60) := by
    rw [div_le_iff₀ (by positivity)]
    calc (c : ℝ) ≤ 2 ^ 62 / (12 - 3 * (3 - (f : ℝ)) * pL 60) := hc
      _ = 1 / (12 - 3 * (3 - (f : ℝ)) * pL 60) * 2 ^ 62 := by ring
  have hden4 : (1 - (3 - (f : ℝ)) * pL 60 / 4) ≠ 0 := by nlinarith
  have hden' : (12 - 3 * (3 - (f : ℝ)) * pL 60) ≠ 0 := hden.ne'
  calc (stepL (3 * D) (2 * (3 - f) * D) c F E l : ℝ) / 2 ^ 62
      ≤ (c : ℝ) * ((num : ℝ) / 2 ^ 62) / 2 ^ 62 / 2 ^ 62 := by gcongr
    _ = (c : ℝ) / 2 ^ 62 * ((num : ℝ) / 2 ^ 124) := by ring
    _ ≤ 1 / (12 - 3 * (3 - (f : ℝ)) * pL 60) *
          (3 * u + 3 * (3 - (f : ℝ)) * (1 - pL 60) * w + 3 * f * A) :=
        mul_le_mul hcd hN (by positivity) (by positivity)
    _ = (1 / 4 * u + (3 - (f : ℝ)) / 4 * (1 - pL 60) * w + (f : ℝ) / 4 * A) /
          (1 - (3 - (f : ℝ)) * pL 60 / 4) := by
        rw [eq_div_iff hden4]
        field_simp
        ring

/-! ## The tables in natural numbers -/

theorem yNext_eq (st : St) (f : ℕ) (prev : List ℕ) :
    yNext st f prev = solve (Nat.shiftLeft D (Nat.mul S f))
      (eventRows (3 * f * (rbCol st * packTable prev))) (3 * D) (2 * (3 - f) * D) (D / (9 + f)) := rfl

theorem rbar_le (st : St) (hs : validSt st = true) (b : ℕ) (hb : b ≤ V) : rbar st b ≤ 2 ^ 62 := by
  have h := rbv_le st hs (V - b)
  unfold rbv at h
  rwa [ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hb] at h

theorem yE_lt (st : St) (hs : validSt st = true) (f : ℕ) (hf : f ≤ 3) (R : ℕ → ℕ → ℕ)
    (hR : ∀ j ≤ P, ∀ l < NL, R j l < 2 ^ 63) (j l : ℕ) (hl : l < NL) : yE st f R j l < 2 ^ 140 := by
  unfold yE
  have hs' : ∑ b ∈ Finset.range (V + 1), rbar st b * R (min (j + b) P) l ≤
      ∑ _b ∈ Finset.range (V + 1), 2 ^ 62 * 2 ^ 63 := Finset.sum_le_sum fun b hb =>
    Nat.mul_le_mul (rbar_le st hs b (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)))
      (hR _ (Nat.min_le_right _ _) l hl).le
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs'
  have : 3 * f ≤ 9 := by omega
  calc 3 * f * _ ≤ 9 * ((V + 1) * (2 ^ 62 * 2 ^ 63)) := Nat.mul_le_mul this hs'
    _ < 2 ^ 140 := by simp only [V]; norm_num

theorem yNext_spec (st : St) (hs : validSt st = true) (f : ℕ) (hf : f ≤ 3) (prev : List ℕ)
    (R : ℕ → ℕ → ℕ) (hprev : ∀ j ≤ P, prev.getD j 0 = pack S NL (R j))
    (hR : ∀ j ≤ P, ∀ l < NL, R j l < 2 ^ 63) (hok : (yNext st f prev).2 = true) :
    ∀ j ≤ P, (yNext st f prev).1.getD j 0 = pack S NL (yL st f R j) ∧
      ∀ l < NL, yL st f R j l < 2 ^ 63 := by
  have hT : TabRows (packTable prev) R := packTable_rows prev R hprev hR
  have hX : 3 * f * (rbCol st * packTable prev) =
      pack RB 320 (fun r => pack S NL (fun l => 3 * f * corr (rbv st) R r l)) := by
    rw [rbCol_eq, col_mul_tab _ _ _ hT, pack_const_mul]
    refine pack_congr _ _ _ _ fun r _ => ?_
    rw [pack_const_mul]
    rfl
  have hcl : ∀ r l, l < NL → 3 * f * corr (rbv st) R r l < 2 ^ 140 := by
    intro r l hl
    have := corr_le (rbv st) (rbv_le st hs) R hR r l hl
    calc 3 * f * corr (rbv st) R r l ≤ 9 * 2 ^ 131 := Nat.mul_le_mul (by omega) this
      _ < 2 ^ 140 := by norm_num
  have hF : ∀ r < 320, pack S NL (fun l => 3 * f * corr (rbv st) R r l) < 2 ^ RB := fun r _ =>
    row_lt _ fun l hl => (hcl r l hl).trans
      (Nat.pow_lt_pow_right (by norm_num) (by simp only [S]; norm_num))
  have hes : ∀ j < P, (eventRows (3 * f * (rbCol st * packTable prev))).getD j 0 =
      pack S NL (yE st f R j) := by
    intro j hj
    rw [hX, eventRows_getD _ hF j (by simp only [P] at hj; omega)]
    refine pack_congr _ _ _ _ fun l _ => ?_
    rw [corr_at _ (fun i hi => by unfold rbv; rw [ite_eq_right (by omega)]) R j hj.le]
    unfold yE
    congr 1
  have hf0 : ∀ l < NL, (fun l => if l = f then D else 0) l < 2 ^ 63 := by
    intro l _
    simp only
    split_ifs
    · rw [D_eq]; norm_num
    · positivity
  have hsol := solve_lanes _ (yE st f R) _ (3 * D) (2 * (3 - f) * D) (D / (9 + f)) hf0 hes
    (fun j _ l hl => yE_lt st hs f hf R hR j l hl) (by rw [D_eq]; norm_num)
    (by rw [D_eq]; have : 2 * (3 - f) ≤ 6 := by omega
        calc 2 * (3 - f) * 2 ^ 62 ≤ 6 * 2 ^ 62 := Nat.mul_le_mul_right _ this
          _ < 2 ^ 66 := by norm_num)
    (by rw [D_eq]; exact (Nat.div_le_self _ _).trans_lt (by norm_num))
  rw [← shiftLeft_eq_pack f (by simp only [NL]; omega)] at hsol
  rw [yNext_eq] at hok ⊢
  intro j hj
  exact ⟨(solve_getD _ _ _ _ _ j hj).trans (hsol hok j hj).1, (hsol hok j hj).2⟩

theorem yE_zero (st : St) (R : ℕ → ℕ → ℕ) : yE st 0 R = fun _ _ => 0 := by
  funext j l; simp [yE]

theorem y0_spec (st : St) (hok : (solve D (eventRows 0) (Nat.mul 3 D) (Nat.mul 6 D) (Nat.div D 9)).2 = true) :
    ∀ j ≤ P, (solve D (eventRows 0) (Nat.mul 3 D) (Nat.mul 6 D) (Nat.div D 9)).1.getD j 0 =
      pack S NL (YF st 0 j) ∧ ∀ l < NL, YF st 0 j l < 2 ^ 63 := by
  have hz : (0 : ℕ) = pack RB 320 (fun _ => pack S NL (fun _ => 0)) := by simp [pack]
  have hes : ∀ j < P, (eventRows 0).getD j 0 = pack S NL (yE st 0 (fun _ _ => 0) j) := by
    intro j hj
    rw [yE_zero]
    have he : eventRows 0 = eventRows (pack RB 320 (fun _ => pack S NL (fun _ => 0))) := congrArg eventRows hz
    rw [he, eventRows_getD _ (fun r _ => row_lt _ fun l _ => by positivity) j
      (by simp only [P] at hj; omega)]
  have hf0 : ∀ l < NL, (fun l => if l = 0 then D else 0) l < 2 ^ 63 := by
    intro l _
    simp only
    split_ifs
    · rw [D_eq]; norm_num
    · positivity
  have hsol := solve_lanes _ (yE st 0 (fun _ _ => 0)) _ (3 * D) (2 * (3 - 0) * D) (D / (9 + 0)) hf0
    hes (fun j _ l _ => by rw [yE_zero]; positivity) (by rw [D_eq]; norm_num)
    (by rw [D_eq]; norm_num) (by rw [D_eq]; norm_num)
  have h0 : pack S NL (fun l => if l = 0 then D else 0) = D := by
    rw [← shiftLeft_eq_pack 0 (by simp only [NL]; omega)]
    rfl
  rw [h0] at hsol
  have hc : (2 * (3 - 0) * D, D / (9 + 0)) = (Nat.mul 6 D, Nat.div D 9) := by
    rw [D_eq]; rfl
  simp only [Prod.mk.injEq] at hc
  rw [hc.1, hc.2] at hsol
  intro j hj
  exact ⟨(solve_getD _ _ _ _ _ j hj).trans (hsol hok j hj).1, (hsol hok j hj).2⟩

/-- The rows of the four tables of `yTabs`. -/
theorem ytabs_rows (st : St) (hs : validSt st = true) (hok : (yTabs st).2 = true) (t : ℕ) (ht : t ≤ 3) :
    ∀ j ≤ P, ((yTabs st).1.getD t []).getD j 0 = pack S NL (YF st t j) ∧
      ∀ l < NL, YF st t j l < 2 ^ 63 := by
  unfold yTabs at hok ⊢
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨h0, h1⟩, h2, h3⟩ := hok
  have r0 := y0_spec st h0
  have r1 := yNext_spec st hs 1 (by norm_num) _ (YF st 0) (fun j hj => (r0 j hj).1)
    (fun j hj => (r0 j hj).2) h1
  have r2 := yNext_spec st hs 2 (by norm_num) _ (YF st 1) (fun j hj => (r1 j hj).1)
    (fun j hj => (r1 j hj).2) h2
  have r3 := yNext_spec st hs 3 (by norm_num) _ (YF st 2) (fun j hj => (r2 j hj).1)
    (fun j hj => (r2 j hj).2) h3
  interval_cases t
  · exact r0
  · exact r1
  · exact r2
  · exact r3

/-! ## The real tables -/

/-- The real H tables. -/
noncomputable def Ty (st : St) (f s a f' : ℕ) : ℝ :=
  if f ≤ 3 ∧ s ≤ P ∧ a ≤ V ∧ f' ≤ 3 then (YF st f s (4 * a + f') : ℝ) / 2 ^ 62 else 0

theorem Ty_nonneg (st : St) (f s a f' : ℕ) : 0 ≤ Ty st f s a f' := by
  unfold Ty; split_ifs <;> positivity

theorem rb_eq (st : St) (b : ℕ) (hb : b ≤ V) :
    ∑ f'' ∈ Finset.range 4, rhoR st b f'' = (rbar st b : ℝ) / 2 ^ 62 := by
  unfold rbar rhoR
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [ite_eq_left ⟨hb, by simp only [Finset.mem_range] at hg; omega⟩]

theorem YF_zero (st : St) (f l : ℕ) : YF st f 0 l = if l = f then D else 0 := by
  cases f <;> rfl

/-- The rows read by the events of `Y_f`: those of `Y_(f-1)` (none for `f = 0`). -/
def prevR (st : St) : ℕ → ℕ → ℕ → ℕ
  | 0 => fun _ _ => 0
  | f + 1 => YF st f

theorem YF_succ (st : St) (f s l : ℕ) :
    YF st f (s + 1) l = stepL (3 * D) (2 * (3 - f) * D) (D / (9 + f)) (YF st f s)
      (yE st f (prevR st f) s) l := by
  cases f <;> rfl

theorem yE_real (st : St) (f : ℕ) (hf : 1 ≤ f) (hf3 : f ≤ 3) (s a f' : ℕ) (ha : a ≤ V) (hg : f' ≤ 3) :
    (yE st f (prevR st f) s (4 * a + f') : ℝ) = 3 * f * 2 ^ 124 *
      ∑ b ∈ Finset.range (V + 1), (∑ f'' ∈ Finset.range 4, rhoR st b f'') *
        Ty st (f - 1) (min (s + b) P) a f' := by
  obtain ⟨f1, rfl⟩ : ∃ f1, f = f1 + 1 := ⟨f - 1, by omega⟩
  unfold yE
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' : b ≤ V := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  rw [rb_eq st b hb']
  unfold Ty
  rw [ite_eq_left ⟨by omega, Nat.min_le_right _ _, ha, hg⟩]
  simp only [prevR]
  field_simp

theorem rhobar_nonneg (st : St) (b : ℕ) : 0 ≤ ∑ f'' ∈ Finset.range 4, rhoR st b f'' :=
  Finset.sum_nonneg fun _ _ => rhoR_nonneg st _ _

theorem pL60_pos : 0 ≤ pL 60 := pL_nonneg 60 (by norm_num)

theorem yden_pos (f : ℕ) (hf : f ≤ 3) : 0 < 1 - (3 - (f : ℝ)) * pL 60 / 4 := by
  have hp0 := pL_nonneg 60 (by norm_num)
  have hp1 := pL_le_third 60 (by norm_num)
  have hf' : (f : ℝ) ≤ 3 := by exact_mod_cast hf
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  nlinarith

theorem ycoef_nonneg (f : ℕ) (hf : f ≤ 3) : 0 ≤ (3 - (f : ℝ)) / 4 * (1 - pL 60) := by
  have hp1 := pL_le_third 60 (by norm_num)
  have hf' : (f : ℝ) ≤ 3 := by exact_mod_cast hf
  exact mul_nonneg (by linarith) (by linarith)

theorem ytab_step (st : St) (f : ℕ) (hf : f ≤ 3) (s a f' : ℕ) :
    Ty st f (s + 1) a f' ≤
      yBody V P 60 (fun b => ∑ f'' ∈ Finset.range 4, rhoR st b f'') (Ty st) f s a f' := by
  have hB0 : 0 ≤ yBody V P 60 (fun b => ∑ f'' ∈ Finset.range 4, rhoR st b f'') (Ty st) f s a f' := by
    unfold yBody
    refine div_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) (yden_pos f hf).le
    · exact mul_nonneg (by norm_num) (upV_nonneg V _ (fun _ _ => Ty_nonneg st _ _ _ _) a f')
    · exact mul_nonneg (ycoef_nonneg f hf) (Ty_nonneg st _ _ _ _)
    · split_ifs
      · exact le_rfl
      · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ =>
          mul_nonneg (rhobar_nonneg st b) (Ty_nonneg st _ _ _ _))
  by_cases hin : s + 1 ≤ P ∧ a ≤ V ∧ f' ≤ 3
  swap
  · unfold Ty
    rw [ite_eq_right (fun h => hin ⟨h.2.1, h.2.2.1, h.2.2.2⟩)]
    exact hB0
  obtain ⟨hp, ha, hg⟩ := hin
  have hTy : ∀ q ≤ P, ∀ x ≤ V, ∀ g ≤ 3, Ty st f q x g = (YF st f q (4 * x + g) : ℝ) / 2 ^ 62 :=
    fun q hq x hx g hg => by unfold Ty; rw [ite_eq_left ⟨hf, hq, hx, hg⟩]
  set A : ℝ := if f = 0 then 0 else
    ∑ b ∈ Finset.range (V + 1), (∑ f'' ∈ Finset.range 4, rhoR st b f'') * Ty st (f - 1) (min (s + b) P) a f'
    with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg fun b _ => mul_nonneg (rhobar_nonneg st b) (Ty_nonneg st _ _ _ _)
  have hE : (yE st f (prevR st f) s (4 * a + f') : ℝ) ≤ 3 * f * 2 ^ 124 * A := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, yE_zero]; simp
    · rw [yE_real st f h0 hf s a f' ha hg, hA, ite_eq_right (by omega)]
  have hfA : (f : ℝ) / 4 * A = if f = 0 then 0 else (f : ℝ) / 4 *
      ∑ b ∈ Finset.range (V + 1), (∑ f'' ∈ Finset.range 4, rhoR st b f'') *
        Ty st (f - 1) (min (s + b) P) a f' := by
    rw [hA]
    split_ifs with h
    · rw [h]; simp
    · rfl
  rw [hTy (s + 1) hp a ha f' hg, YF_succ]
  refine (ystep_real f hf _ _ _ A hA0 hE).trans (le_of_eq ?_)
  unfold yBody
  rw [upV_lanes (YF st f s) _ (fun x' hx' g' hg' => hTy s (by omega) x' hx' g' hg') a f' ha hg,
    hTy s (by omega) a ha f' hg, hfA]

/-- **The H tables are below the H recursion of `M1_60`**: the computed `Y_t(1)` is below
`KhatH`. -/
theorem ytabs_sound (st : St) (hs : validSt st = true) (hok : (yTabs st).2 = true) (t : ℕ) (ht : t ≤ 3)
    (a : ℕ) (ha : a ≤ V) (f' : ℕ) (hf' : f' ≤ 3) :
    (lane (((yTabs st).1.getD t []).getD 1 0) (4 * a + f') : ℝ) / 2 ^ 62 ≤
      KhatH V P 60 (rhoR st) t a f' := by
  have hl : 4 * a + f' < NL := by simp only [V] at ha; simp only [NL]; omega
  obtain ⟨h1, h2⟩ := ytabs_rows st hs hok t ht 1 (by simp only [P]; omega)
  rw [h1, lane_pack NL _ (fun l hl => lt_S_of_lt_63 (h2 l hl)) _, ite_eq_left hl]
  have key := yrec_lower V P 60 (by norm_num) (fun b => ∑ f'' ∈ Finset.range 4, rhoR st b f'')
    (rhobar_nonneg st) (Ty st) ?_ (fun f hf s a f' => ytab_step st f hf s a f') t ht 1 a f'
  · unfold Ty at key
    rw [ite_eq_left ⟨ht, by simp only [P]; omega, ha, hf'⟩] at key
    exact key
  · intro f hf a f'
    unfold Ty
    rw [Yrec.eq_1]
    split_ifs with h1 h2 h2
    · rw [YF_zero, ite_eq_left (by omega), D_eq]; norm_num
    · rw [YF_zero, ite_eq_right (by omega)]; simp
    · norm_num
    · norm_num

end FrogModel.D3.M1K
