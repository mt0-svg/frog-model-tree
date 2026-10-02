module

public import FrogModel.LemmaX.ChildBasic
public import FrogModel.Engine.Core
public import FrogModel.Engine.FK
public import FrogModel.Engine.Absorb

@[expose] public section

/-!
# Lemma 6.3 of the paper: the tail of a cascade

Along the root
chain of the child chains of a table, `Phi = theta^e phi^(p + J - i) prod_c w(σ_c)` does not
increase in mean (`one_step_le`: an exit multiplies it by `theta / phi`, an entry into a child by
at most `kappa / phi` in mean, and `(theta / phi + 4 kappa / phi) / 5 = 1`), so
`E Phi(X_n) ≤ Phi(x)` (`lintegral_PhiE_traj_le`). On a run with unbounded exits (almost every
run, `ae_exitCount_unbounded`), `theta^(G(4))` is at most `liminf Phi(X_n)`: at the absorption
`Phi ≥ theta^e = theta^(G(4))`, and a run that never ends has `Phi ≥ theta^e → ⊤`
(`epow_recOut_le`). Fatou's lemma gives `E theta^(G(4)) ≤ Phi(x)` (`lemma61_gen`), with
`theta^⊤ = ⊤`, so the run ends almost surely.

The invariant `Inv61` (a valid state, live or absorbed with `G(4) = e`, well-formed children)
is kept by every step (`inv61_rstep`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace FrogModel.LemmaX

open FrogModel.Engine FrogModel.Cert

/-- The invariant of Lemma 6.3 along the root chain: a valid state, live or absorbed with its
last output equal to its exits, with well-formed children. -/
def Inv61 (D : Data) (x : RState CState 4 4) : Prop :=
  Valid x ∧ (x.i < 4 ∨ (x.i = 4 ∧ x.out 3 = (x.e : ℕ∞))) ∧ ∀ c, D.ChildWF (x.σ c)

/-- `Phi` of Lemma 6.3 in `ℝ≥0∞`. -/
noncomputable def PhiE (D : Data) (x : RState CState 4 4) : ℝ≥0∞ := ENNReal.ofReal (D.PhiQ x : ℝ)

end FrogModel.LemmaX

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaX FrogModel.Cert FrogModel.Engine

/-- `r_q(M_q) ≥ 1`: every max row has weights `≥ 0` summing to `1`, and `phi ≥ 1`. -/
theorem FrogModel.Cert.Data.one_le_rMax (D : Data) (h0 : D.I0) (h1 : D.I1) (q : ℕ) :
    1 ≤ D.rMax q := by
  rcases h0 with ⟨hJ, hT, hεpos, hεlt1, hρpos, hρlt1, hφgt1⟩
  have hφge1 : 1 ≤ D.phi := le_of_lt hφgt1
  have hJpos : 0 < D.J := by omega
  have h_level : ∀ n, 1 ≤ D.rMaxLevel n := by
    intro n
    induction' n with n ih
    · have h0 : D.rMaxLevel 0 = 1 := rfl
      rw [h0]
    · have h_succ : D.rMaxLevel (n + 1) = D.rowMgf (D.maxRow (D.J - (n + 1))) * D.rMaxLevel n := rfl
      rw [h_succ]
      have hq : D.J - (n + 1) < D.J := by omega
      have h_rowmgf : 1 ≤ D.rowMgf (D.maxRow (D.J - (n + 1))) := by
        have hsum_p : ((D.maxRow (D.J - (n + 1))).map FrogModel.Cert.Entry.p).sum = 1 :=
          D.maxRow_sum h1 (D.J - (n + 1)) hq
        have h_nonneg_p : ∀ e ∈ D.maxRow (D.J - (n + 1)), 0 ≤ e.p := by
          intro e he
          rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
          have h_anti : Antitone (D.tailMax (D.J - (n + 1))) := D.tailMax_antitone h1 (D.J - (n + 1))
          have h_le : D.tailMax (D.J - (n + 1)) (k + 1) ≤ D.tailMax (D.J - (n + 1)) k :=
            h_anti (Nat.le_succ k)
          exact sub_nonneg.mpr h_le
        have h_pow_ge_one : ∀ m : ℕ, 1 ≤ D.phi ^ m := by
          intro m
          induction' m with m ih_pow
          · norm_num
          · rw [pow_succ]
            have hφ_nonneg : 0 ≤ D.phi := le_trans (by norm_num) hφge1
            have h_pow_nonneg : 0 ≤ D.phi ^ m := pow_nonneg hφ_nonneg m
            calc
              1 = 1 * 1 := by norm_num
              _ ≤ D.phi ^ m * D.phi := mul_le_mul ih_pow hφge1 (by norm_num) h_pow_nonneg
        have h_phi_pow : ∀ e ∈ D.maxRow (D.J - (n + 1)), 1 ≤ D.phi ^ e.δ := by
          intro e he
          exact h_pow_ge_one e.δ
        have h_mul : ∀ e ∈ D.maxRow (D.J - (n + 1)), e.p ≤ e.p * D.phi ^ e.δ := by
          intro e he
          have hp_nonneg : 0 ≤ e.p := h_nonneg_p e he
          have hp_pow : 1 ≤ D.phi ^ e.δ := h_phi_pow e he
          calc
            e.p = e.p * 1 := by ring
            _ ≤ e.p * (D.phi ^ e.δ) :=
              mul_le_mul (le_refl e.p) hp_pow (by norm_num) hp_nonneg
        calc
          1 = ((D.maxRow (D.J - (n + 1))).map FrogModel.Cert.Entry.p).sum := by rw [hsum_p]
          _ ≤ ((D.maxRow (D.J - (n + 1))).map fun e => e.p * D.phi ^ e.δ).sum :=
            List.sum_le_sum h_mul
          _ = D.rowMgf (D.maxRow (D.J - (n + 1))) := rfl
      have h_rowmgf_nonneg : 0 ≤ D.rowMgf (D.maxRow (D.J - (n + 1))) :=
        le_trans (by norm_num) h_rowmgf
      calc
        1 = 1 * 1 := by ring
        _ ≤ D.rowMgf (D.maxRow (D.J - (n + 1))) * D.rMaxLevel n :=
          mul_le_mul h_rowmgf ih (by norm_num) h_rowmgf_nonneg
  have h_rMax : D.rMax q = D.rMaxLevel (D.J - q) := rfl
  rw [h_rMax]
  exact h_level (D.J - q)

/-- The weight of a well-formed child state is at least `1`. -/
theorem FrogModel.Cert.Data.one_le_wQ (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2)
    (s : CState) (hs : D.ChildWF s) : 1 ≤ D.wQ s := by
  have hkappa : 1 ≤ D.kappa := h2.2.1
  have one_le_pow' : ∀ (a : ℚ), 1 ≤ a → ∀ n : ℕ, 1 ≤ a ^ n := by
    intro a ha n
    induction' n with n ih
    · norm_num
    · rw [pow_succ]
      have ha' : 0 ≤ a := by linarith
      have h1' : 0 ≤ (1 : ℚ) := by norm_num
      have hpos1 : 0 ≤ a ^ n := pow_nonneg ha' n
      have h := mul_le_mul ih ha h1' hpos1
      simpa [mul_one] using h
  cases s with
  | fresh =>
    simp [Data.wQ]
    exact one_le_pow' D.kappa hkappa D.J
  | bdry =>
    simp [Data.wQ]
    exact one_le_pow' D.kappa hkappa (D.J - 1)
  | lab q s =>
    simp [Data.wQ]
    have hs' : 1 ≤ q ∧ q < D.J ∧ s < D.nLabels q := by
      simpa [Data.ChildWF] using hs
    exact one_le_weight D h0 h1 h2 q hs'.1 (by omega) s hs'.2.2
  | tail q =>
    simp [Data.wQ]
    have hs' : 1 ≤ q ∧ q < D.J := by
      simpa [Data.ChildWF] using hs
    exact one_le_pow' D.kappa hkappa (q - 1)
  | maxLab q =>
    simp [Data.wQ]
    have hs' : 1 ≤ q ∧ q < D.J := by
      simpa [Data.ChildWF] using hs
    have hkpow : 1 ≤ D.kappa ^ (q - 1) := one_le_pow' D.kappa hkappa (q - 1)
    have hrMax : 1 ≤ D.rMax q := one_le_rMax D h0 h1 q
    have hpos1 : 0 ≤ D.kappa ^ (q - 1) := pow_nonneg (by linarith) (q - 1)
    have hpos2 : 0 ≤ (1 : ℚ) := by norm_num
    have h := mul_le_mul hkpow hrMax hpos2 hpos1
    simpa [mul_one] using h

/-- `theta^e ≤ Phi(x)` when the children are well formed. -/
theorem FrogModel.Cert.Data.theta_pow_le_PhiQ (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2)
    (x : RState CState 4 4) (hx : ∀ c, D.ChildWF (x.σ c)) : D.theta ^ x.e ≤ D.PhiQ x := by
  have hθ : 0 ≤ D.theta ^ x.e := pow_nonneg (by linarith [h2.2.2.2.1]) _
  have hφ : 1 ≤ D.phi ^ (x.p + 4 - x.i - 1) := one_le_pow₀ h0.2.2.2.2.2.2.le
  have hprod : 1 ≤ ∏ c, D.wQ (x.σ c) :=
    Finset.one_le_prod₀ fun c _ => D.one_le_wQ h0 h1 h2 _ (hx c)
  unfold Data.PhiQ
  calc D.theta ^ x.e = D.theta ^ x.e * 1 * 1 := by ring
    _ ≤ D.theta ^ x.e * D.phi ^ (x.p + 4 - x.i - 1) * ∏ c, D.wQ (x.σ c) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hφ hθ) hprod zero_le_one
        (mul_nonneg hθ (le_trans zero_le_one hφ))

/-- One entry from label `s` of level `q`: `sum p phi^δ w(next) = kappa w(lab q s)`. -/
theorem FrogModel.Cert.Data.labRow_mgf (D : Data) (h1 : D.I1) (q s : ℕ) (hq1 : 1 ≤ q)
    (hq : q < D.J) (hs : s < D.nLabels q) :
    ((D.labRow q s).map fun e => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum =
      D.kappa * D.wQ (.lab q s) := by
  -- keep h1 for r_step
  have h1_copy := h1
  rcases h1 with ⟨hlabels, hnLabels0, hnLabelsJ, hallT, hrowSum⟩
  -- labRow is a permutation of the mapped table row
  have hperm : List.Perm (D.labRow q s) ((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)) := by
    dsimp [labRow]
    -- List.mergeSort_perm returns (mergeSort ...).Perm l, we need l.Perm (mergeSort ...)
    exact (List.mergeSort_perm _ _)
  -- rewrite LHS using permutation
  have hsum_perm : ((D.labRow q s).map fun e => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum =
      (((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)).map fun e => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum :=
    (hperm.map _).sum_eq
  -- key lemma: wQ (nxt (q+1) t.s') = kappa^q * r (q+1) t.s' for t in row q s
  have h_wQ_nxt : ∀ t, t ∈ D.row q s → D.wQ (D.nxt (q + 1) t.s') = D.kappa ^ q * D.r (q + 1) t.s' := by
    intro t ht
    have ht_mem : t ∈ D.table := List.mem_of_mem_filter ht
    have ht_q : t.q = q := by
      have h := (List.mem_filter.mp ht).2
      -- h : decide (t.q = q ∧ t.s = s) = true
      -- we need to extract t.q = q from this
      exact (by simpa using h : t.q = q ∧ t.s = s).1
    have ht_s'_lt : t.s' < D.nLabels (t.q + 1) := (hallT t ht_mem).2.2.1
    rw [ht_q] at ht_s'_lt
    -- now ht_s'_lt : t.s' < D.nLabels (q + 1)
    by_cases h_eq : q + 1 = D.J
    · -- case q + 1 = D.J
      have h_nxt_eq : D.nxt (q + 1) t.s' = .bdry := by
        dsimp [nxt]
        simp [h_eq]
      rw [h_nxt_eq]
      dsimp [wQ]
      -- need: kappa^(D.J - 1) = kappa^q * D.r (q+1) t.s'
      -- since q+1 = D.J, D.J-1 = q (because q ≥ 1)
      have h_exp_eq : D.J - 1 = q := by omega
      rw [h_exp_eq]
      -- need: kappa^q = kappa^q * D.r (q+1) t.s'
      -- i.e., D.r (q+1) t.s' = 1
      -- from ht_s'_lt: t.s' < D.nLabels (q+1) = D.nLabels D.J = 1, so t.s' = 0
      rw [h_eq] at ht_s'_lt
      rw [hnLabelsJ] at ht_s'_lt
      have h_s'_zero : t.s' = 0 := by omega
      rw [h_s'_zero]
      -- D.r D.J 0 = 1 by r_end, and q+1 = D.J
      rw [h_eq]
      rw [FrogModel.Cert.Data.r_end D]
      simp
    · -- case q + 1 < D.J
      have h_nxt_eq : D.nxt (q + 1) t.s' = .lab (q + 1) t.s' := by
        dsimp [nxt]
        simp [h_eq]
      rw [h_nxt_eq]
      have h_exp_eq : (q + 1 - 1) = q := by omega
      simp [wQ, h_exp_eq]
  -- helper lemma: if two functions agree on all elements of a list, their maps are equal
  have h_map_congr_on (l : List Tr) (f g : Tr → ℚ) (h : ∀ x ∈ l, f x = g x) :
      List.map f l = List.map g l := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      have hx : f x = g x := h x List.mem_cons_self
      have hxs : ∀ y ∈ xs, f y = g y := fun y hy => h y (List.mem_cons_of_mem x hy)
      simp [hx, ih hxs]
  -- rewrite using h_wQ_nxt: factor out kappa^q
  have h_sum_factor : ((D.row q s).map fun t => t.p * (D.phi ^ t.δ * D.wQ (D.nxt (q + 1) t.s'))).sum =
      D.kappa ^ q * ((D.row q s).map fun t => t.p * D.phi ^ t.δ * D.r (q + 1) t.s').sum := by
    -- Use List.sum_map_mul_left after showing the maps are equal
    rw [← List.sum_map_mul_left (D.row q s) (fun t => t.p * D.phi ^ t.δ * D.r (q + 1) t.s') (D.kappa ^ q)]
    -- Now need to show: (map f (D.row q s)).sum = (map g (D.row q s)).sum
    -- where f t = t.p * (D.phi ^ t.δ * D.wQ (D.nxt (q+1) t.s'))
    --       g t = D.kappa ^ q * (t.p * D.phi ^ t.δ * D.r (q+1) t.s')
    apply congrArg List.sum
    refine h_map_congr_on (D.row q s) (fun t => t.p * (D.phi ^ t.δ * D.wQ (D.nxt (q + 1) t.s')))
      (fun t => D.kappa ^ q * (t.p * D.phi ^ t.δ * D.r (q + 1) t.s')) ?_
    intro t ht
    rw [h_wQ_nxt t ht]
    ring
  -- use r_step
  have h_rstep : ((D.row q s).map fun t => t.p * D.phi ^ t.δ * D.r (q + 1) t.s').sum = D.r q s :=
    FrogModel.Cert.Data.r_step D h1_copy q hq s hs
  -- compute RHS: kappa * wQ (lab q s) = kappa * (kappa^(q-1) * r q s) = kappa^q * r q s
  have h_rhs : D.kappa * D.wQ (.lab q s) = D.kappa ^ q * D.r q s := by
    dsimp [wQ]
    have h_exp_eq : (q - 1) + 1 = q := Nat.sub_add_cancel hq1
    calc
      D.kappa * (D.kappa ^ (q - 1) * D.r q s) = (D.kappa * D.kappa ^ (q - 1)) * D.r q s := by ring
      _ = D.kappa ^ ((q - 1) + 1) * D.r q s := by rw [pow_succ']
      _ = D.kappa ^ q * D.r q s := by rw [h_exp_eq]
  -- put everything together
  calc
    ((D.labRow q s).map fun e => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum
        = (((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)).map fun e => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum := hsum_perm
    _ = ((D.row q s).map fun t => t.p * (D.phi ^ t.δ * D.wQ (D.nxt (q + 1) t.s'))).sum := by
      rw [List.map_map]
      rfl
    _ = D.kappa ^ q * ((D.row q s).map fun t => t.p * D.phi ^ t.δ * D.r (q + 1) t.s').sum := h_sum_factor
    _ = D.kappa ^ q * D.r q s := by rw [h_rstep]
    _ = D.kappa * D.wQ (.lab q s) := by rw [h_rhs]

/-- One entry from the max label of level `q`: `sum p phi^δ w(next) = kappa w(maxLab q)`. -/
theorem FrogModel.Cert.Data.maxRow_mgf (D : Data) (q : ℕ) (hq1 : 1 ≤ q) (hq : q < D.J) :
    ((D.maxRow q).map fun e => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum =
      D.kappa * D.wQ (.maxLab q) := by
  -- All entries in maxRow q have the same next state
  have h_next : ∀ e ∈ D.maxRow q, e.next = D.nxtMax (q + 1) := by
    intro e he
    rw [Data.maxRow] at he
    rcases List.mem_map.mp he with ⟨k, _, rfl⟩
    rfl
  -- For each entry, the term simplifies
  have h_term : ∀ e ∈ D.maxRow q, e.p * (D.phi ^ e.δ * D.wQ e.next) = (e.p * D.phi ^ e.δ) * D.wQ (D.nxtMax (q + 1)) := by
    intro e he
    have hn := h_next e he
    simp [hn, mul_assoc]
  -- Factor out D.wQ (D.nxtMax (q + 1))
  have h_factor : ((D.maxRow q).map fun e => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum =
      ((D.maxRow q).map fun e => e.p * D.phi ^ e.δ).sum * D.wQ (D.nxtMax (q + 1)) := by
    calc
      ((D.maxRow q).map fun e => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum
          = ((D.maxRow q).map fun e => (e.p * D.phi ^ e.δ) * D.wQ (D.nxtMax (q + 1))).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        exact h_term
      _ = ((D.maxRow q).map fun e => e.p * D.phi ^ e.δ).sum * D.wQ (D.nxtMax (q + 1)) := by
        rw [List.sum_map_mul_right]
  -- Compute wQ (nxtMax (q + 1))
  have h_wQ_nxtMax : D.wQ (D.nxtMax (q + 1)) = D.kappa ^ q * D.rMax (q + 1) := by
    dsimp [Data.nxtMax]
    by_cases h_eq : q + 1 = D.J
    · simp [h_eq]
      dsimp [Data.wQ]
      have h_q_eq : D.J - 1 = q := by omega
      rw [h_q_eq]
      have h_rMax : D.rMax D.J = 1 := by
        dsimp [Data.rMax]
        have h_sub : D.J - D.J = 0 := by omega
        rw [h_sub]
        simp [Data.rMaxLevel]
      rw [h_rMax]
      simp
    · simp [h_eq]
      dsimp [Data.wQ]
  -- Compute rMax q = rowMgf (maxRow q) * rMax (q + 1)
  have h_rMax_eq : D.rMax q = D.rowMgf (D.maxRow q) * D.rMax (q + 1) := by
    dsimp [Data.rMax]
    have h_sub : D.J - q = (D.J - (q + 1)) + 1 := by omega
    rw [h_sub]
    rw [Data.rMaxLevel]
    have h_sub2 : D.J - ((D.J - (q + 1)) + 1) = q := by omega
    rw [h_sub2]
  -- Compute kappa^q = kappa * kappa^(q-1)
  have h_pow : D.kappa ^ q = D.kappa * D.kappa ^ (q - 1) := by
    calc
      D.kappa ^ q = D.kappa ^ ((q - 1) + 1) := by rw [Nat.sub_add_cancel hq1]
      _ = D.kappa ^ (q - 1) * D.kappa := by rw [pow_succ]
      _ = D.kappa * D.kappa ^ (q - 1) := by ring
  -- Final computation
  calc
    ((D.maxRow q).map fun e => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum
        = ((D.maxRow q).map fun e => e.p * D.phi ^ e.δ).sum * D.wQ (D.nxtMax (q + 1)) := h_factor
    _ = D.rowMgf (D.maxRow q) * D.wQ (D.nxtMax (q + 1)) := by rfl
    _ = D.rowMgf (D.maxRow q) * (D.kappa ^ q * D.rMax (q + 1)) := by rw [h_wQ_nxtMax]
    _ = D.kappa ^ q * (D.rowMgf (D.maxRow q) * D.rMax (q + 1)) := by ring
    _ = D.kappa ^ q * D.rMax q := by rw [h_rMax_eq]
    _ = (D.kappa * D.kappa ^ (q - 1)) * D.rMax q := by rw [h_pow]
    _ = D.kappa * (D.kappa ^ (q - 1) * D.rMax q) := by ring
    _ = D.kappa * D.wQ (.maxLab q) := rfl

/-- A row sequence sums over its finite part, then over its tail. -/
theorem FrogModel.LemmaX.rowSeq_hasSum_split (D : Data) (s : CState) (F : Entry → ℝ) (a b : ℝ)
    (hfin : ((D.finRow s).map F).sum = a)
    (htail : HasSum (fun n => F (D.rowSeq s (n + (D.finRow s).length))) b) :
    HasSum (fun n => F (D.rowSeq s n)) (a + b) := by
  refine (hasSum_nat_add_iff' (D.finRow s).length).mp ?_
  have h : ∑ i ∈ Finset.range (D.finRow s).length, F (D.rowSeq s i) = a := by
    rw [Finset.sum_range]
    have h : ∀ i : Fin (D.finRow s).length, D.rowSeq s i = (D.finRow s)[(i : ℕ)] := by
      intro i
      rw [Data.rowSeq, dite_eq_left i.2]
    simp only [h]
    rw [Fin.sum_univ_fun_getElem (D.finRow s) F]
    exact hfin
  rw [h, add_sub_cancel_left]
  exact htail

/-- The tail of the row of `fresh` or `bdry`. -/
theorem FrogModel.LemmaX.rowSeq_tail_eq (D : Data) (s s' : CState) (hs : D.tailNext s = some s')
    (n : ℕ) : D.rowSeq s (n + (D.finRow s).length) = ⟨D.tailW n, D.T + 1 + n, s'⟩ := by
  rw [Data.rowSeq, dite_eq_right (by omega), Nat.add_sub_cancel, hs]

/-- The geometric tail weighted by `phi^δ`, times a constant `w`. -/
theorem FrogModel.LemmaX.tailW_mgf (D : Data) (h0 : D.I0) (h2 : D.I2) (w : ℝ) :
    HasSum (fun n => ((D.tailW n : ℚ) : ℝ) * ((D.phi : ℝ) ^ (D.T + 1 + n) * w))
      (w * (D.eps : ℝ) * ((1 - (D.rho : ℝ)) * (D.phi : ℝ) ^ (D.T + 1) /
        (1 - (D.phi : ℝ) * (D.rho : ℝ)))) := by
  have hr : (0 : ℝ) ≤ D.rho := by exact_mod_cast h0.2.2.2.2.1.le
  have hφ : (0 : ℝ) ≤ D.phi := by
    have : (1 : ℝ) < D.phi := by exact_mod_cast h0.2.2.2.2.2.2
    linarith
  have hφr : (D.phi : ℝ) * D.rho < 1 := by exact_mod_cast h2.1
  have h := (tail_mgf (D.rho : ℝ) (D.phi : ℝ) D.T hr hφ hφr).mul_left (w * (D.eps : ℝ))
  convert h using 2 with n
  simp only [Data.tailW]
  push_cast
  ring

/-- One entry from `bdry`: the mean of `phi^δ w(next)` is `M` (Lemma 6.3). -/
theorem FrogModel.Cert.Data.bdry_mgf (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2) :
    HasSum (fun n => ((D.rowSeq .bdry n).p : ℝ) *
      ((D.phi : ℝ) ^ (D.rowSeq .bdry n).δ * (D.wQ (D.rowSeq .bdry n).next : ℝ))) (D.M : ℝ) := by
  have hJ2 : 2 ≤ D.J := h0.1
  have hw : D.wQ (D.nxtTail 1) = 1 := by
    simp [Data.nxtTail, show (1 : ℕ) ≠ D.J by omega, Data.wQ]
  have hfin : ((D.finRow .bdry).map fun e : Entry => (e.p : ℝ) * ((D.phi : ℝ) ^ e.δ *
      (D.wQ e.next : ℝ))).sum = (((1 - D.eps) * D.r 0 0 : ℚ) : ℝ) := by
    have hq : ((D.finRow .bdry).map fun e : Entry => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum =
        (1 - D.eps) * D.r 0 0 := by
      rw [show D.finRow .bdry = D.bdryRow from rfl, Data.bdryRow, List.map_map]
      rw [← D.r_step h1 0 (by omega) 0 (by rw [h1.2.1]; exact one_pos), ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Data.nxt, zero_add, show (1 : ℕ) ≠ D.J by omega, ite_false,
        Data.wQ, Nat.sub_self, pow_zero, one_mul]
      ring
    rw [← hq, Rat.cast_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp_apply, Rat.cast_mul, Rat.cast_pow]
  have h := rowSeq_hasSum_split D .bdry
    (fun e : Entry => (e.p : ℝ) * ((D.phi : ℝ) ^ e.δ * (D.wQ e.next : ℝ))) _ _ hfin
    (by
      simp only [rowSeq_tail_eq D .bdry (D.nxtTail 1) rfl, hw]
      exact tailW_mgf D h0 h2 ((1 : ℚ) : ℝ))
  convert h using 1
  simp only [Data.M]
  push_cast
  ring

/-- One entry from `fresh`: the mean of `phi^δ w(next)` is `kappa M` (Lemma 6.3). -/
theorem FrogModel.Cert.Data.fresh_mgf (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2) :
    HasSum (fun n => ((D.rowSeq .fresh n).p : ℝ) *
      ((D.phi : ℝ) ^ (D.rowSeq .fresh n).δ * (D.wQ (D.rowSeq .fresh n).next : ℝ)))
      ((D.kappa : ℝ) * (D.M : ℝ)) := by
  have hJ2 : 2 ≤ D.J := h0.1
  have hw : D.wQ (D.nxtTail 2) = D.kappa := by
    by_cases h : 2 = D.J
    · simp [Data.nxtTail, ← h, Data.wQ]
    · simp [Data.nxtTail, h, Data.wQ]
  have hw2 : ∀ s, s < D.nLabels 2 → D.wQ (D.nxt 2 s) = D.kappa * D.r 2 s := by
    intro s hs
    by_cases h : 2 = D.J
    · have hn : D.nLabels 2 = 1 := by rw [h]; exact h1.2.2.1
      have hs0 : s = 0 := by omega
      subst hs0
      have hr : D.r 2 0 = 1 := by rw [h]; exact D.r_end
      simp [Data.nxt, ← h, Data.wQ, hr]
    · simp [Data.nxt, h, Data.wQ]
  have hfin : ((D.finRow .fresh).map fun e : Entry => (e.p : ℝ) * ((D.phi : ℝ) ^ e.δ *
      (D.wQ e.next : ℝ))).sum = ((D.kappa * ((1 - D.eps) * D.r 0 0) : ℚ) : ℝ) := by
    have hq : ((D.finRow .fresh).map fun e : Entry => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum =
        D.kappa * ((1 - D.eps) * D.r 0 0) := by
      rw [show D.finRow .fresh = D.freshRow from rfl, Data.freshRow, List.flatMap_def,
        List.map_flatten, List.sum_flatten, List.map_map]
      rw [← D.r_two_step h1 hJ2, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun t₁ _ => ?_
      simp only [Function.comp_apply, List.map_map]
      rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t₂ ht₂ => ?_
      have hs : t₂.s' < D.nLabels 2 := by
        have hmem := (List.mem_filter.1 ht₂)
        have := (h1.2.2.2.1 t₂ hmem.1).2.2.1
        have hq : t₂.q = 1 := (by simpa using hmem.2 : t₂.q = 1 ∧ t₂.s = t₁.s').1
        rwa [hq] at this
      simp only [Function.comp_apply, hw2 _ hs, pow_add]
      ring
    rw [← hq, Rat.cast_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp_apply, Rat.cast_mul, Rat.cast_pow]
  have h := rowSeq_hasSum_split D .fresh
    (fun e : Entry => (e.p : ℝ) * ((D.phi : ℝ) ^ e.δ * (D.wQ e.next : ℝ))) _ _ hfin
    (by
      simp only [rowSeq_tail_eq D .fresh (D.nxtTail 2) rfl, hw]
      exact tailW_mgf D h0 h2 (D.kappa : ℝ))
  convert h using 1
  simp only [Data.M]
  push_cast
  ring

/-- **One entry of the child chain multiplies `phi^δ w` by at most `kappa` in mean.** -/
theorem FrogModel.Cert.Data.rowSeq_mgf (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2)
    (s : CState) (hs : D.ChildWF s) :
    ∃ m : ℝ, HasSum (fun n => ((D.rowSeq s n).p : ℝ) *
      ((D.phi : ℝ) ^ (D.rowSeq s n).δ * (D.wQ (D.rowSeq s n).next : ℝ))) m ∧
      m ≤ (D.kappa : ℝ) * (D.wQ s : ℝ) := by
  have hJ2 : 2 ≤ D.J := h0.1
  have hκ : (0 : ℝ) ≤ D.kappa := by
    have : (1 : ℝ) ≤ D.kappa := by exact_mod_cast h2.2.1
    linarith
  have hMκ : (D.M : ℝ) ≤ (D.kappa : ℝ) ^ D.J := by exact_mod_cast h2.2.2.1
  set F : Entry → ℝ := fun e => (e.p : ℝ) * ((D.phi : ℝ) ^ e.δ * (D.wQ e.next : ℝ)) with hF
  have hcast : ∀ s, ((D.finRow s).map F).sum =
      ((((D.finRow s).map fun e : Entry => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum : ℚ) : ℝ) := by
    intro s
    rw [Rat.cast_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    simp only [hF, Function.comp_apply, Rat.cast_mul, Rat.cast_pow]
  have hnone : ∀ s, D.tailNext s = none →
      HasSum (fun n => F (D.rowSeq s (n + (D.finRow s).length))) 0 := by
    intro s hn
    have h : ∀ n, D.rowSeq s (n + (D.finRow s).length) = ⟨0, 0, s⟩ := by
      intro n
      rw [Data.rowSeq, dite_eq_right (by omega), Nat.add_sub_cancel, hn]
    simp only [h, hF, Rat.cast_zero, zero_mul]
    exact hasSum_zero
  cases s with
  | fresh =>
    refine ⟨_, D.fresh_mgf h0 h1 h2, ?_⟩
    simp only [Data.wQ]
    push_cast
    exact mul_le_mul_of_nonneg_left hMκ hκ
  | bdry =>
    refine ⟨_, D.bdry_mgf h0 h1 h2, ?_⟩
    simp only [Data.wQ]
    push_cast
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    exact hMκ
  | lab q t =>
    obtain ⟨hq1, hq, ht⟩ := hs
    have h := rowSeq_hasSum_split D (.lab q t) F _ 0
      ((hcast _).trans (congrArg _ (D.labRow_mgf h1 q t hq1 hq ht))) (hnone _ rfl)
    rw [add_zero] at h
    refine ⟨_, h, ?_⟩
    push_cast
    exact le_rfl
  | tail q =>
    obtain ⟨hq1, hq⟩ := hs
    have hw : D.wQ (D.nxtTail (q + 1)) = D.kappa * D.wQ (.tail q) := by
      have hk : D.kappa * D.kappa ^ (q - 1) = D.kappa ^ q := by
        rw [← pow_succ', Nat.sub_add_cancel hq1]
      by_cases h : q + 1 = D.J
      · simp only [Data.nxtTail, h, ite_true, Data.wQ, hk]
        congr 1
        omega
      · simp only [Data.nxtTail, h, ite_false, Data.wQ, hk, Nat.add_sub_cancel]
    have hsum : ((D.finRow (.tail q)).map fun e : Entry => e.p * (D.phi ^ e.δ * D.wQ e.next)).sum =
        D.kappa * D.wQ (.tail q) := by
      simp [Data.finRow, Data.tailRow, hw]
    have h := rowSeq_hasSum_split D (.tail q) F _ 0
      ((hcast _).trans (congrArg _ hsum)) (hnone _ rfl)
    rw [add_zero] at h
    refine ⟨_, h, ?_⟩
    push_cast
    exact le_rfl
  | maxLab q =>
    obtain ⟨hq1, hq⟩ := hs
    have h := rowSeq_hasSum_split D (.maxLab q) F _ 0
      ((hcast _).trans (congrArg _ (D.maxRow_mgf q hq1 hq))) (hnone _ rfl)
    rw [add_zero] at h
    refine ⟨_, h, ?_⟩
    push_cast
    exact le_rfl

/-- **The child step of Lemma 6.3**: `E[phi^δ w(σ')] ≤ kappa w(σ)` from a well-formed state. -/
theorem FrogModel.Cert.Data.child_mean_le (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2)
    (s : CState) (hs : D.ChildWF s) :
    ∫⁻ u, ENNReal.ofReal ((D.phi : ℝ) ^ (D.childStep s u).1 * (D.wQ (D.childStep s u).2 : ℝ))
      ∂lam ≤ ENNReal.ofReal ((D.kappa : ℝ) * (D.wQ s : ℝ)) := by
  have hphi_gt_one : 1 < D.phi := h0.2.2.2.2.2.2
  have hphi_gt_one_real : (1 : ℝ) < (D.phi : ℝ) := by exact_mod_cast hphi_gt_one
  have hphi_nonneg : 0 ≤ (D.phi : ℝ) := le_trans (by norm_num) hphi_gt_one_real.le
  obtain ⟨m, hm_hasSum, hm_bound⟩ := D.rowSeq_mgf h0 h1 h2 s hs
  have h_nonneg : ∀ n, 0 ≤ ((D.rowSeq s n).p : ℝ) * ((D.phi : ℝ) ^ (D.rowSeq s n).δ * (D.wQ (D.rowSeq s n).next : ℝ)) := by
    intro n
    have hp_nonneg_rat : 0 ≤ (D.rowSeq s n).p := D.rowSeq_nonneg h0 h1 s hs n
    have hp_nonneg : 0 ≤ ((D.rowSeq s n).p : ℝ) := by exact_mod_cast hp_nonneg_rat
    have hphi_pow_nonneg : 0 ≤ (D.phi : ℝ) ^ (D.rowSeq s n).δ := pow_nonneg hphi_nonneg _
    have hnext_wf : D.ChildWF (D.rowSeq s n).next := D.rowSeq_next_wf h0 h1 s hs n
    have hwQ_nonneg : 0 ≤ (D.wQ (D.rowSeq s n).next : ℝ) := by
      have h := D.one_le_wQ h0 h1 h2 (D.rowSeq s n).next hnext_wf
      have hwQ_one : (1 : ℝ) ≤ (D.wQ (D.rowSeq s n).next : ℝ) := by exact_mod_cast h
      linarith
    have hprod_nonneg : 0 ≤ (D.phi : ℝ) ^ (D.rowSeq s n).δ * (D.wQ (D.rowSeq s n).next : ℝ) :=
      mul_nonneg hphi_pow_nonneg hwQ_nonneg
    exact mul_nonneg hp_nonneg hprod_nonneg
  calc
    ∫⁻ u, ENNReal.ofReal ((D.phi : ℝ) ^ (D.childStep s u).1 * (D.wQ (D.childStep s u).2 : ℝ)) ∂lam
        = ∑' n, ENNReal.ofReal ((D.rowSeq s n).p : ℝ) * ENNReal.ofReal ((D.phi : ℝ) ^ (D.rowSeq s n).δ * (D.wQ (D.rowSeq s n).next : ℝ)) := by
      simpa using D.lintegral_childStep h0 h1 s hs
        (fun r : ℕ × CState => ENNReal.ofReal ((D.phi : ℝ) ^ r.1 * (D.wQ r.2 : ℝ)))
    _ = ∑' n, ENNReal.ofReal (((D.rowSeq s n).p : ℝ) * ((D.phi : ℝ) ^ (D.rowSeq s n).δ * (D.wQ (D.rowSeq s n).next : ℝ))) := by
      refine tsum_congr (fun n => ?_)
      have hp_nonneg_rat : 0 ≤ (D.rowSeq s n).p := D.rowSeq_nonneg h0 h1 s hs n
      have hp_nonneg : 0 ≤ ((D.rowSeq s n).p : ℝ) := by exact_mod_cast hp_nonneg_rat
      rw [← ENNReal.ofReal_mul hp_nonneg]
    _ = ENNReal.ofReal (∑' n, ((D.rowSeq s n).p : ℝ) * ((D.phi : ℝ) ^ (D.rowSeq s n).δ * (D.wQ (D.rowSeq s n).next : ℝ))) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg hm_hasSum.summable]
    _ = ENNReal.ofReal m := by rw [hm_hasSum.tsum_eq]
    _ ≤ ENNReal.ofReal ((D.kappa : ℝ) * (D.wQ s : ℝ)) := ENNReal.ofReal_le_ofReal hm_bound

/-- An exit multiplies `Phi` by `theta / phi`. -/
theorem FrogModel.Cert.Data.PhiQ_exit (D : Data) (x : RState CState 4 4) (hi : x.i < 4)
    (hp : 1 ≤ x.p) (u : ℝ) :
    D.PhiQ (rstep D.childStep x (0, u)) * D.phi = D.PhiQ x * D.theta := by
  have hmove : move D.childStep x (0 : Fin (4 + 1)) u = (x.e + 1, x.p - 1, x.σ) := by
    unfold move; simp
  have hrstep : rstep D.childStep x (0, u) =
      if x.p - 1 = 0 then
        ⟨x.i + 1, x.e + 1, 1, x.σ, Function.update x.out ⟨x.i, hi⟩ (x.e + 1)⟩
      else
        ⟨x.i, x.e + 1, x.p - 1, x.σ, x.out⟩ := by
    unfold rstep; simp [hi, hmove]
  by_cases hpend : x.p - 1 = 0
  · have hp1 : x.p = 1 := by omega
    rw [hrstep, hpend]
    dsimp [PhiQ]
    rw [hp1]
    have h_exp : (1 + 4 - (x.i + 1) - 1 : ℕ) + 1 = 1 + 4 - x.i - 1 := by omega
    have h_phi_eq1 : D.phi ^ (1 + 4 - (x.i + 1) - 1) * D.phi = D.phi ^ ((1 + 4 - (x.i + 1) - 1 : ℕ) + 1) := by
      rw [← pow_succ]
    calc
      (D.theta ^ (x.e + 1) * D.phi ^ (1 + 4 - (x.i + 1) - 1) * (∏ c, D.wQ (x.σ c))) * D.phi
          = (D.theta ^ x.e * D.theta) * (D.phi ^ (1 + 4 - (x.i + 1) - 1) * D.phi) * (∏ c, D.wQ (x.σ c)) := by
        rw [pow_succ]
        ring
      _ = (D.theta ^ x.e * D.theta) * (D.phi ^ ((1 + 4 - (x.i + 1) - 1 : ℕ) + 1)) * (∏ c, D.wQ (x.σ c)) := by
        rw [h_phi_eq1]
      _ = (D.theta ^ x.e * D.theta) * (D.phi ^ (1 + 4 - x.i - 1)) * (∏ c, D.wQ (x.σ c)) := by
        rw [h_exp]
      _ = (D.theta ^ x.e * D.phi ^ (1 + 4 - x.i - 1) * (∏ c, D.wQ (x.σ c))) * D.theta := by ring
  · rw [hrstep]
    simp [hpend]
    dsimp [PhiQ]
    have h_exp : (x.p - 1 + 4 - x.i - 1 : ℕ) + 1 = x.p + 4 - x.i - 1 := by omega
    have h_phi_eq2 : D.phi ^ (x.p - 1 + 4 - x.i - 1) * D.phi = D.phi ^ ((x.p - 1 + 4 - x.i - 1 : ℕ) + 1) := by
      rw [← pow_succ]
    calc
      (D.theta ^ (x.e + 1) * D.phi ^ (x.p - 1 + 4 - x.i - 1) * (∏ c, D.wQ (x.σ c))) * D.phi
          = (D.theta ^ x.e * D.theta) * (D.phi ^ (x.p - 1 + 4 - x.i - 1) * D.phi) * (∏ c, D.wQ (x.σ c)) := by
        rw [pow_succ]
        ring
      _ = (D.theta ^ x.e * D.theta) * (D.phi ^ ((x.p - 1 + 4 - x.i - 1 : ℕ) + 1)) * (∏ c, D.wQ (x.σ c)) := by
        rw [h_phi_eq2]
      _ = (D.theta ^ x.e * D.theta) * (D.phi ^ (x.p + 4 - x.i - 1)) * (∏ c, D.wQ (x.σ c)) := by
        rw [h_exp]
      _ = (D.theta ^ x.e * D.phi ^ (x.p + 4 - x.i - 1) * (∏ c, D.wQ (x.σ c))) * D.theta := by ring

/-- An entry into child `c` multiplies `Phi` by `phi^(δ - 1) w(σ') / w(σ_c)`. -/
theorem FrogModel.Cert.Data.PhiQ_entry (D : Data) (x : RState CState 4 4) (hi : x.i < 4)
    (hp : 1 ≤ x.p) (c : Fin 4) (u : ℝ) :
    D.PhiQ (rstep D.childStep x (c.succ, u)) * (D.phi * D.wQ (x.σ c)) =
      D.PhiQ x * (D.phi ^ (D.childStep (x.σ c) u).1 * D.wQ (D.childStep (x.σ c) u).2) := by
  set δ := (D.childStep (x.σ c) u).1 with hδ
  set σ' := (D.childStep (x.σ c) u).2 with hσ'
  have hmove : FrogModel.Engine.move D.childStep x (c.succ : Fin (4 + 1)) u =
      (x.e, x.p - 1 + δ, Function.update x.σ c σ') := by
    unfold FrogModel.Engine.move
    simp [Fin.succ_ne_zero c, hδ, hσ']
  unfold FrogModel.Engine.rstep
  dsimp
  rw [hmove]
  -- Simplify the triple projection: .2.1 of (x.e, x.p-1+δ, ...) is x.p-1+δ
  dsimp
  -- Now the goal is: if x.p - 1 + δ = 0 then ... else ...
  split_ifs with hfin
  · -- Case: frog finishes (x.p - 1 + δ = 0)
    have hp1 : x.p = 1 := by omega
    have hδ0 : δ = 0 := by omega
    -- Unfold PhiQ first so x.p is visible
    unfold FrogModel.Cert.Data.PhiQ
    simp
    -- Now the goal has x.p visible
    rw [hp1, hδ0]
    simp
    -- Goal: (theta^e * phi^(1+4-(i+1)-1) * ∏ c', wQ(update σ c σ' c')) * (phi * wQ(σ c))
    --     = (theta^e * phi^(1+4-i-1) * ∏ c, wQ(σ c)) * wQ σ'
    -- Product identity
    have hprod : (∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) * D.wQ (x.σ c) =
        (∏ c' : Fin 4, D.wQ (x.σ c')) * D.wQ σ' := by
      calc
        (∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) * D.wQ (x.σ c) =
            ((∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ ((Function.update x.σ c σ') c')) *
             D.wQ ((Function.update x.σ c σ') c)) * D.wQ (x.σ c) := by
          rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin 4))
            (fun c' => D.wQ ((Function.update x.σ c σ') c')) (Finset.mem_univ c)]
        _ = ((∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) * D.wQ σ') * D.wQ (x.σ c) := by
          have hupdate : (∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ ((Function.update x.σ c σ') c')) =
              (∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) := by
            refine Finset.prod_congr rfl (fun c' hc' => ?_)
            have hc'ne : c' ≠ c := Finset.mem_erase.mp hc' |>.left
            simp [hc'ne]
          rw [hupdate]
          simp
        _ = (∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) * (D.wQ σ' * D.wQ (x.σ c)) := by ring
        _ = (∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) * (D.wQ (x.σ c) * D.wQ σ') := by ring
        _ = ((∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) * D.wQ (x.σ c)) * D.wQ σ' := by ring
        _ = (∏ c' : Fin 4, D.wQ (x.σ c')) * D.wQ σ' := by
          rw [Finset.prod_erase_mul (Finset.univ : Finset (Fin 4)) (fun c' => D.wQ (x.σ c')) (Finset.mem_univ c)]
    -- Now use hprod to rewrite the goal
    -- Goal: (theta^e * phi^(4-i-1) * P) * (phi * wQ(σ c)) = (theta^e * phi^(5-i-1) * Q) * wQ σ'
    -- where P = ∏ c', wQ(update σ c σ' c'), Q = ∏ c, wQ(σ c)
    -- Using hprod: P * wQ(σ c) = Q * wQ σ'
    -- Also: phi^(4-i-1) * phi = phi^(5-i-1)
    have h_exp_eq : D.phi ^ (4 - x.i - 1) * D.phi = D.phi ^ (5 - x.i - 1) := by
      rw [← pow_succ, show (4 - x.i - 1 : ℕ) + 1 = 5 - x.i - 1 by omega]
    -- Rearrange using `simp` with `mul_assoc`, `mul_comm`, `mul_left_comm`
    simp [mul_assoc, mul_comm, mul_left_comm]
    -- Goal: phi * (phi^(4-i-1) * (theta^e * (wQ(σ c) * P))) = phi^(5-i-1) * (theta^e * (wQ σ' * Q))
    -- Remove parentheses to expose phi * phi^(4-i-1)
    rw [← mul_assoc]
    -- Goal: (phi * phi^(4-i-1)) * (theta^e * (wQ(σ c) * P)) = phi^(5-i-1) * (theta^e * (wQ σ' * Q))
    -- Swap phi * phi^(4-i-1) to phi^(4-i-1) * phi, then use h_exp_eq
    rw [mul_comm D.phi (D.phi ^ (4 - x.i - 1)), h_exp_eq]
    -- Goal: phi^(5-i-1) * (theta^e * (wQ(σ c) * P)) = phi^(5-i-1) * (theta^e * (wQ σ' * Q))
    -- Now use hprod: P * wQ(σ c) = Q * wQ σ'
    -- We need to relate wQ(σ c) * P to wQ σ' * Q
    -- hprod gives: P * wQ(σ c) = Q * wQ σ'
    -- By commutativity: wQ(σ c) * P = wQ σ' * Q
    have hprod' : D.wQ (x.σ c) * (∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) =
        D.wQ σ' * (∏ c' : Fin 4, D.wQ (x.σ c')) := by
      simpa [mul_comm] using hprod
    rw [hprod']
  · -- Case: frog does not finish (¬ x.p - 1 + δ = 0)
    -- hfin : ¬ x.p - 1 + δ = 0
    -- Goal: D.PhiQ { i := x.i, e := x.e, p := x.p-1+δ, σ := update x.σ c σ', ... } * (phi * wQ(σ c))
    --     = D.PhiQ x * (phi^δ * wQ σ')
    unfold FrogModel.Cert.Data.PhiQ
    simp
    -- Goal: (theta^e * phi^(x.p-1+δ+4-x.i-1) * P) * (phi * wQ(σ c)) = (theta^e * phi^(x.p+4-x.i-1) * Q) * (phi^δ * wQ σ')
    -- where P = ∏ c', wQ(update σ c σ' c'), Q = ∏ c, wQ(σ c)
    -- Using hprod: P * wQ(σ c) = Q * wQ σ'
    -- Also: phi^(x.p-1+δ+4-x.i-1) * phi = phi^(x.p+4-x.i-1) * phi^δ
    have h_exp_eq : D.phi ^ (x.p - 1 + δ + 4 - x.i - 1) * D.phi = D.phi ^ (x.p + 4 - x.i - 1) * D.phi ^ δ := by
      have hp1 : 1 ≤ x.p := hp
      have hxp : x.p + 3 - x.i = x.p + 4 - x.i - 1 := by omega
      calc
        D.phi ^ (x.p - 1 + δ + 4 - x.i - 1) * D.phi = D.phi ^ (x.p - 1 + δ + 4 - x.i) := by
          rw [← pow_succ, show (x.p - 1 + δ + 4 - x.i - 1 : ℕ) + 1 = x.p - 1 + δ + 4 - x.i by omega]
        _ = D.phi ^ (x.p + δ + 3 - x.i) := by
          congr 1
          omega
        _ = D.phi ^ ((x.p + 3 - x.i) + δ) := by
          congr 1
          omega
        _ = D.phi ^ (x.p + 3 - x.i) * D.phi ^ δ := by rw [pow_add]
        _ = D.phi ^ (x.p + 4 - x.i - 1) * D.phi ^ δ := by rw [hxp]
    have hprod : (∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) * D.wQ (x.σ c) =
        (∏ c' : Fin 4, D.wQ (x.σ c')) * D.wQ σ' := by
      calc
        (∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) * D.wQ (x.σ c) =
            ((∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ ((Function.update x.σ c σ') c')) *
             D.wQ ((Function.update x.σ c σ') c)) * D.wQ (x.σ c) := by
          rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin 4))
            (fun c' => D.wQ ((Function.update x.σ c σ') c')) (Finset.mem_univ c)]
        _ = ((∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) * D.wQ σ') * D.wQ (x.σ c) := by
          have hupdate : (∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ ((Function.update x.σ c σ') c')) =
              (∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) := by
            refine Finset.prod_congr rfl (fun c' hc' => ?_)
            have hc'ne : c' ≠ c := Finset.mem_erase.mp hc' |>.left
            simp [hc'ne]
          rw [hupdate]
          simp
        _ = (∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) * (D.wQ σ' * D.wQ (x.σ c)) := by ring
        _ = (∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) * (D.wQ (x.σ c) * D.wQ σ') := by ring
        _ = ((∏ c' ∈ (Finset.univ : Finset (Fin 4)).erase c, D.wQ (x.σ c')) * D.wQ (x.σ c)) * D.wQ σ' := by ring
        _ = (∏ c' : Fin 4, D.wQ (x.σ c')) * D.wQ σ' := by
          rw [Finset.prod_erase_mul (Finset.univ : Finset (Fin 4)) (fun c' => D.wQ (x.σ c')) (Finset.mem_univ c)]
    -- Now use hprod and h_exp_eq to rewrite the goal
    -- Goal: (theta^e * phi^(x.p-1+δ+4-x.i-1) * P) * (phi * wQ(σ c)) = (theta^e * phi^(x.p+4-x.i-1) * Q) * (phi^δ * wQ σ')
    -- We'll prove this using h_exp_eq and hprod
    have hgoal : (D.theta ^ x.e * D.phi ^ (x.p - 1 + δ + 4 - x.i - 1) * ∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) * (D.phi * D.wQ (x.σ c)) =
        (D.theta ^ x.e * D.phi ^ (x.p + 4 - x.i - 1) * ∏ c' : Fin 4, D.wQ (x.σ c')) * (D.phi ^ δ * D.wQ σ') := by
      have hprod' : (∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) * D.wQ (x.σ c) =
          (∏ c' : Fin 4, D.wQ (x.σ c')) * D.wQ σ' := hprod
      calc
        (D.theta ^ x.e * D.phi ^ (x.p - 1 + δ + 4 - x.i - 1) * ∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) * (D.phi * D.wQ (x.σ c))
            = D.theta ^ x.e * (D.phi ^ (x.p - 1 + δ + 4 - x.i - 1) * D.phi) * ((∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) * D.wQ (x.σ c)) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        _ = D.theta ^ x.e * (D.phi ^ (x.p + 4 - x.i - 1) * D.phi ^ δ) * ((∏ c' : Fin 4, D.wQ ((Function.update x.σ c σ') c')) * D.wQ (x.σ c)) := by rw [h_exp_eq]
        _ = (D.theta ^ x.e * D.phi ^ (x.p + 4 - x.i - 1) * ∏ c' : Fin 4, D.wQ (x.σ c')) * (D.phi ^ δ * D.wQ σ') := by
          rw [hprod']
          simp [mul_assoc, mul_comm, mul_left_comm]
    exact hgoal

/-- Integrating against a uniform direction and an independent input. -/
theorem FrogModel.LemmaX.lintegral_unifDir_prod {U : Type*} [MeasurableSpace U] (d : ℕ)
    (ν : Measure U) [IsProbabilityMeasure ν] (f : Fin (d + 1) × U → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ξ, f ξ ∂((unifDir d).prod ν) = ∑ a, ((d : ℝ≥0∞) + 1)⁻¹ * ∫⁻ u, f (a, u) ∂ν := by
  have hunifDir_singleton (a : Fin (d + 1)) : (unifDir d) {a} = ((d : ℝ≥0∞) + 1)⁻¹ := by
    have hcard : (Fintype.card (Fin (d + 1)) : ℝ≥0∞) = (d : ℝ≥0∞) + 1 := by
      simp
    calc
      (unifDir d) {a} = (ProbabilityTheory.uniformOn Set.univ) {a} := rfl
      _ = Measure.count {a} / (Fintype.card (Fin (d + 1)) : ℝ≥0∞) := by
        rw [ProbabilityTheory.uniformOn_univ]
      _ = 1 / (Fintype.card (Fin (d + 1)) : ℝ≥0∞) := by simp
      _ = 1 / ((d : ℝ≥0∞) + 1) := by rw [hcard]
      _ = ((d : ℝ≥0∞) + 1)⁻¹ := by simp
  calc
    ∫⁻ ξ, f ξ ∂((unifDir d).prod ν) = ∫⁻ a, ∫⁻ u, f (a, u) ∂ν ∂(unifDir d) := by
      rw [MeasureTheory.lintegral_prod]
      exact hf.aemeasurable
    _ = ∑ a, (∫⁻ u, f (a, u) ∂ν) * (unifDir d) {a} := by
      rw [MeasureTheory.lintegral_fintype]
    _ = ∑ a, (∫⁻ u, f (a, u) ∂ν) * (((d : ℝ≥0∞) + 1)⁻¹) := by
      simp [hunifDir_singleton]
    _ = ∑ a, ((d : ℝ≥0∞) + 1)⁻¹ * ∫⁻ u, f (a, u) ∂ν := by
      simp [mul_comm]

/-- The invariant of Lemma 6.3 is kept by every step. -/
theorem FrogModel.LemmaX.inv61_rstep (D : Data) (h0 : D.I0) (h1 : D.I1) (x : RState CState 4 4)
    (hx : Inv61 D x) (ξ : Fin 5 × ℝ) : Inv61 D (rstep D.childStep x ξ) := by
  rcases hx with ⟨hvalid, habs, hchildren⟩
  have hvalid' : Valid (rstep D.childStep x ξ) := rstep_valid D.childStep x hvalid ξ
  have hchildren' : ∀ c, D.ChildWF ((rstep D.childStep x ξ).σ c) := by
    intro c
    by_cases hi : x.i < 4
    · dsimp [rstep]
      simp [hi]
      by_cases hfin : (move D.childStep x ξ.1 ξ.2).2.1 = 0
      · simp [hfin]
        by_cases hξ0 : ξ.1 = 0
        · simp [move, hξ0]
          exact hchildren c
        · simp [move, hξ0]
          by_cases hc : c = ξ.1.pred hξ0
          · subst hc
            simp [Function.update_self]
            apply FrogModel.Cert.Data.childWF_step D h0 h1 (x.σ (ξ.1.pred hξ0)) (hchildren (ξ.1.pred hξ0)) ξ.2
          · simp [hc]
            exact hchildren c
      · simp [hfin]
        by_cases hξ0 : ξ.1 = 0
        · simp [move, hξ0]
          exact hchildren c
        · simp [move, hξ0]
          by_cases hc : c = ξ.1.pred hξ0
          · subst hc
            simp [Function.update_self]
            apply FrogModel.Cert.Data.childWF_step D h0 h1 (x.σ (ξ.1.pred hξ0)) (hchildren (ξ.1.pred hξ0)) ξ.2
          · simp [hc]
            exact hchildren c
    · have heq : rstep D.childStep x ξ = x := rstep_of_absorbed D.childStep x (by omega) ξ
      rw [heq]
      exact hchildren c
  refine ⟨hvalid', ?_, hchildren'⟩
  by_cases hi : x.i < 4
  · dsimp [rstep]
    simp [hi]
    by_cases hfin : (move D.childStep x ξ.1 ξ.2).2.1 = 0
    · simp [hfin]
      by_cases hi3 : x.i < 3
      · left; omega
      · have hi_eq_3 : x.i = 3 := by omega
        right
        constructor
        · omega
        · have h3 : (⟨x.i, hi⟩ : Fin 4) = (3 : Fin 4) := by
            ext
            simp [hi_eq_3]
          rw [h3]
          simp
    · simp [hfin]
      left
      exact hi
  · have heq : rstep D.childStep x ξ = x := rstep_of_absorbed D.childStep x (by omega) ξ
    rw [heq]
    exact habs

/-- A function of the state after `n` steps of a driven system on a countable type is
measurable in the inputs, when each step is. -/
theorem FrogModel.LemmaX.measurable_comp_traj {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]
    (f : X → Ξ → X) (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (g : X → ℝ≥0∞) (n : ℕ) (x : X) :
    Measurable fun w : ℕ → Ξ => g (traj f x w n) := by
  classical
    induction' n with n ih generalizing x
    · -- n = 0: traj f x w 0 = x, constant function is measurable
      simp [traj]
    · -- n + 1: use traj_succ_shift to reduce to induction hypothesis
      -- Rewrite inside the lambda using congrArg
      have h_traj : (fun (w : ℕ → Ξ) => g (traj f x w (n + 1))) =
          (fun w => g (traj f (f x (w 0)) (fun k => w (k + 1)) n)) := by
        ext w
        simp [traj_succ_shift]
      rw [h_traj]
      -- Write the function as a countable sum of indicator functions
      have h_eq : (fun (w : ℕ → Ξ) => g (traj f (f x (w 0)) (fun k => w (k + 1)) n)) =
          (fun w => ∑' (y : X), (Set.indicator {w' | f x (w' 0) = y}
            (fun w' => g (traj f y (fun k => w' (k + 1)) n)) w)) := by
        ext w
        simp only [Set.indicator, Set.mem_ofPred_eq]
        let F : X → ℝ≥0∞ := fun y =>
          if f x (w 0) = y then g (traj f y (fun k => w (k + 1)) n) else 0
        have hF0 : F (f x (w 0)) = g (traj f (f x (w 0)) (fun k => w (k + 1)) n) := by
          simp [F]
        have hFz : ∀ y, y ≠ f x (w 0) → F y = 0 := by
          intro y hy
          simp [F, hy.symm]
        have h := tsum_eq_single (L := SummationFilter.unconditional X) (f x (w 0)) hFz
        calc
          g (traj f (f x (w 0)) (fun k => w (k + 1)) n) = F (f x (w 0)) := by
            rw [hF0]
          _ = ∑' (y : X), F y := by rw [← h]
          _ = ∑' (y : X), (if f x (w 0) = y then g (traj f y (fun k => w (k + 1)) n) else 0) := rfl
      rw [h_eq]
      refine Measurable.tsum ?_
      intro y
      refine Measurable.indicator ?_ ?_
      · -- The function fun w' => g (traj f y (fun k => w' (k + 1)) n) is measurable
        have h_shift : Measurable fun (w' : ℕ → Ξ) (k : ℕ) => w' (k + 1) := by
          apply measurable_pi_iff.2
          intro k
          exact measurable_pi_apply (k + 1)
        exact (ih y).comp h_shift
      · -- The set {w' | f x (w' 0) = y} is measurable
        have h_proj : Measurable fun (w' : ℕ → Ξ) => w' 0 := measurable_pi_apply 0
        have h_set : MeasurableSet {ξ | f x ξ = y} := hf x y
        exact measurableSet_preimage h_proj h_set

/-- **One step of the root chain does not increase `Phi` in mean** (Lemma 6.3). -/
theorem FrogModel.LemmaX.one_step_le (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2)
    (x : RState CState 4 4) (hx : Inv61 D x) :
    ∫⁻ ξ, PhiE D (rstep D.childStep x ξ) ∂((unifDir 4).prod lam) ≤ PhiE D x := by
  have hφ1 : 1 < D.phi := h0.2.2.2.2.2.2
  have hφ0 : (0 : ℚ) < D.phi := by linarith
  by_cases hi : x.i < 4
  swap
  · have hrs : ∀ ξ, rstep D.childStep x ξ = x := fun ξ =>
      rstep_of_absorbed D.childStep x (by omega) ξ
    simp only [hrs, lintegral_const, measure_univ, mul_one, le_refl]
  have hp : 1 ≤ x.p := hx.1.1 hi
  have hwf := hx.2.2
  have hθ1 : 1 < D.theta := h2.2.2.2.1
  have hκ1 : 1 ≤ D.kappa := h2.2.1
  have hPpos : 0 < D.PhiQ x :=
    (pow_pos (by linarith) _).trans_le (D.theta_pow_le_PhiQ h0 h1 h2 x hwf)
  have hwpos : ∀ c, 0 < D.wQ (x.σ c) := fun c =>
    lt_of_lt_of_le zero_lt_one (D.one_le_wQ h0 h1 h2 _ (hwf c))
  have hf : ∀ y, MeasurableSet {ξ : Fin 5 × ℝ | rstep D.childStep x ξ = y} := fun y =>
    measurableSet_rstep_eq D.childStep (fun s r => D.measurableSet_childStep_eq s r) x y
  have hmeas : Measurable fun ξ => PhiE D (rstep D.childStep x ξ) := by
    intro s _
    have e : (fun ξ => PhiE D (rstep D.childStep x ξ)) ⁻¹' s =
        ⋃ y ∈ {y : RState CState 4 4 | PhiE D y ∈ s}, {ξ | rstep D.childStep x ξ = y} := by
      ext ξ
      simp
    rw [e]
    exact MeasurableSet.biUnion (Set.to_countable _) fun y _ => hf y
  have hexit : ∫⁻ u, PhiE D (rstep D.childStep x (0, u)) ∂lam =
      ENNReal.ofReal ((D.PhiQ x * D.theta / D.phi : ℚ) : ℝ) := by
    have h : ∀ u, D.PhiQ (rstep D.childStep x (0, u)) = D.PhiQ x * D.theta / D.phi := fun u => by
      rw [eq_div_iff hφ0.ne']
      exact D.PhiQ_exit x hi hp u
    simp only [PhiE, h, lintegral_const, measure_univ, mul_one]
  have hentry : ∀ c : Fin 4, ∫⁻ u, PhiE D (rstep D.childStep x (c.succ, u)) ∂lam ≤
      ENNReal.ofReal ((D.PhiQ x * D.kappa / D.phi : ℚ) : ℝ) := by
    intro c
    have hw : 0 < D.phi * D.wQ (x.σ c) := mul_pos hφ0 (hwpos c)
    have h : ∀ u, D.PhiQ (rstep D.childStep x (c.succ, u)) =
        D.PhiQ x / (D.phi * D.wQ (x.σ c)) *
          (D.phi ^ (D.childStep (x.σ c) u).1 * D.wQ (D.childStep (x.σ c) u).2) := fun u => by
      rw [div_mul_eq_mul_div, eq_div_iff hw.ne']
      exact D.PhiQ_entry x hi hp c u
    have hK : (0 : ℝ) ≤ ((D.PhiQ x / (D.phi * D.wQ (x.σ c)) : ℚ) : ℝ) := by
      exact_mod_cast (div_pos hPpos hw).le
    calc ∫⁻ u, PhiE D (rstep D.childStep x (c.succ, u)) ∂lam
        = ∫⁻ u, ENNReal.ofReal ((D.PhiQ x / (D.phi * D.wQ (x.σ c)) : ℚ) : ℝ) *
            ENNReal.ofReal ((D.phi : ℝ) ^ (D.childStep (x.σ c) u).1 *
              (D.wQ (D.childStep (x.σ c) u).2 : ℝ)) ∂lam := by
          refine lintegral_congr fun u => ?_
          rw [PhiE, h u, ← ENNReal.ofReal_mul hK]
          push_cast
          rfl
      _ = ENNReal.ofReal ((D.PhiQ x / (D.phi * D.wQ (x.σ c)) : ℚ) : ℝ) *
            ∫⁻ u, ENNReal.ofReal ((D.phi : ℝ) ^ (D.childStep (x.σ c) u).1 *
              (D.wQ (D.childStep (x.σ c) u).2 : ℝ)) ∂lam :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((D.PhiQ x / (D.phi * D.wQ (x.σ c)) : ℚ) : ℝ) *
            ENNReal.ofReal ((D.kappa : ℝ) * (D.wQ (x.σ c) : ℝ)) := by
          gcongr
          exact D.child_mean_le h0 h1 h2 _ (hwf c)
      _ = ENNReal.ofReal ((D.PhiQ x * D.kappa / D.phi : ℚ) : ℝ) := by
          rw [← ENNReal.ofReal_mul hK]
          congr 1
          have := (hwpos c).ne'
          push_cast
          field_simp
  have hA : (0 : ℝ) ≤ ((D.PhiQ x * D.theta / D.phi : ℚ) : ℝ) := by
    exact_mod_cast (div_pos (mul_pos hPpos (by linarith)) hφ0).le
  have hB : (0 : ℝ) ≤ ((D.PhiQ x * D.kappa / D.phi : ℚ) : ℝ) := by
    exact_mod_cast (div_pos (mul_pos hPpos (by linarith)) hφ0).le
  have h5 : (((4 : ℕ) : ℝ≥0∞) + 1)⁻¹ = ENNReal.ofReal (1 / 5) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [lintegral_unifDir_prod 4 lam _ hmeas, Fin.sum_univ_succ, h5, hexit]
  calc ENNReal.ofReal (1 / 5) * ENNReal.ofReal ((D.PhiQ x * D.theta / D.phi : ℚ) : ℝ) +
        ∑ c : Fin 4, ENNReal.ofReal (1 / 5) *
          ∫⁻ u, PhiE D (rstep D.childStep x (c.succ, u)) ∂lam
      ≤ ENNReal.ofReal (1 / 5) * ENNReal.ofReal ((D.PhiQ x * D.theta / D.phi : ℚ) : ℝ) +
        ∑ c : Fin 4, ENNReal.ofReal (1 / 5) *
          ENNReal.ofReal ((D.PhiQ x * D.kappa / D.phi : ℚ) : ℝ) := by
        gcongr with c
        exact hentry c
    _ = ENNReal.ofReal (1 / 5 * ((D.PhiQ x * D.theta / D.phi : ℚ) : ℝ) +
          ∑ c : Fin 4, 1 / 5 * ((D.PhiQ x * D.kappa / D.phi : ℚ) : ℝ)) := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun _ _ => by positivity),
          ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, ENNReal.ofReal_mul (by norm_num)]
        simp only [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / 5 by norm_num)]
    _ = PhiE D x := by
        rw [PhiE]
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        simp only [Data.theta]
        push_cast
        field_simp
        ring

/-- **`Phi` along the root chain is a supermartingale**: `E Phi(X_n) ≤ Phi(x)`. -/
theorem FrogModel.LemmaX.lintegral_PhiE_traj_le (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2)
    (n : ℕ) (x : RState CState 4 4) (hx : Inv61 D x) :
    ∫⁻ w, PhiE D (traj (rstep D.childStep) x w n) ∂(iidMeasure ((unifDir 4).prod lam)) ≤
      PhiE D x := by
  have hprob : IsProbabilityMeasure (iidMeasure ((unifDir 4).prod lam)) := by
    unfold iidMeasure; infer_instance
  have hf : ∀ (x : RState CState 4 4) y,
      MeasurableSet {ξ : Fin 5 × ℝ | rstep D.childStep x ξ = y} := fun x y =>
    measurableSet_rstep_eq D.childStep (fun s r => D.measurableSet_childStep_eq s r) x y
  have hcons : Measurable fun p : (Fin 5 × ℝ) × (ℕ → Fin 5 × ℝ) => consSeq p.1 p.2 := by
    refine measurable_pi_iff.2 fun k => ?_
    cases k with
    | zero => exact measurable_fst
    | succ k => exact (measurable_pi_apply k).comp measurable_snd
  induction n generalizing x with
  | zero =>
    simp only [traj, lintegral_const, measure_univ, mul_one, le_refl]
  | succ n ih =>
    have hF : Measurable (Function.uncurry fun (ξ : Fin 5 × ℝ) (w : ℕ → Fin 5 × ℝ) =>
        PhiE D (traj (rstep D.childStep) x (consSeq ξ w) (n + 1))) :=
      (measurable_comp_traj (rstep D.childStep) hf (PhiE D) (n + 1) x).comp hcons
    have hshift : ∀ w : ℕ → Fin 5 × ℝ, consSeq (w 0) (fun k => w (k + 1)) = w := by
      intro w; funext k; cases k <;> rfl
    calc ∫⁻ w, PhiE D (traj (rstep D.childStep) x w (n + 1)) ∂(iidMeasure ((unifDir 4).prod lam))
        = ∫⁻ ξ, ∫⁻ w, PhiE D (traj (rstep D.childStep) x (consSeq ξ w) (n + 1))
            ∂(iidMeasure ((unifDir 4).prod lam)) ∂((unifDir 4).prod lam) := by
          rw [← lintegral_iid_cons _ _ hF]
          simp only [hshift]
      _ = ∫⁻ ξ, ∫⁻ w, PhiE D (traj (rstep D.childStep) (rstep D.childStep x ξ) w n)
            ∂(iidMeasure ((unifDir 4).prod lam)) ∂((unifDir 4).prod lam) := by
          simp only [traj_succ_shift]
          rfl
      _ ≤ ∫⁻ ξ, PhiE D (rstep D.childStep x ξ) ∂((unifDir 4).prod lam) :=
          lintegral_mono fun ξ => ih _ (inv61_rstep D h0 h1 x hx ξ)
      _ ≤ PhiE D x := one_step_le D h0 h1 h2 x hx

/-- While the run is live, the exits are those of the inputs. -/
theorem FrogModel.LemmaX.e_traj_of_live {S U : Type*} (cstep : S → U → ℕ × S)
    (x : RState S 4 4) (w : ℕ → Fin 5 × U) (n : ℕ)
    (h : ∀ k < n, (traj (rstep cstep) x w k).i < 4) :
    (traj (rstep cstep) x w n).e = x.e + exitCount w n := by
  induction' n with n ih
  · simp [traj, exitCount]
  · have hn : (traj (rstep cstep) x w n).i < 4 := h n (Nat.lt_succ_self n)
    have h_ind : ∀ k < n, (traj (rstep cstep) x w k).i < 4 := by
      intro k hk
      exact h k (Nat.lt_of_lt_of_le hk (Nat.le_succ n))
    have h_exit : exitCount w (n + 1) = exitCount w n + (if (w n).1 = 0 then 1 else 0) := by
      dsimp [exitCount]
      rw [Finset.range_add_one, Finset.filter_insert]
      split <;> simp
    have h_live : (rstep cstep (traj (rstep cstep) x w n) (w n)).e =
        (traj (rstep cstep) x w n).e + (if (w n).1 = 0 then 1 else 0) := by
      set y := traj (rstep cstep) x w n with hy
      have hy_live : y.i < 4 := hn
      have h_e_eq : (rstep cstep y (w n)).e = (move cstep y (w n).1 (w n).2).1 := by
        unfold rstep
        simp [hy_live]
        by_cases hmove : (move cstep y (w n).1 (w n).2).2.1 = 0
        · simp [hmove]
        · simp [hmove]
      have h_move_e : (move cstep y (w n).1 (w n).2).1 = y.e + (if (w n).1 = 0 then 1 else 0) := by
        unfold move
        by_cases h : (w n).1 = 0
        · simp [h]
        · simp [h]
      calc
        (rstep cstep y (w n)).e = (move cstep y (w n).1 (w n).2).1 := h_e_eq
        _ = y.e + (if (w n).1 = 0 then 1 else 0) := h_move_e
    calc
      (traj (rstep cstep) x w (n + 1)).e = (rstep cstep (traj (rstep cstep) x w n) (w n)).e := rfl
      _ = (traj (rstep cstep) x w n).e + (if (w n).1 = 0 then 1 else 0) := h_live
      _ = (x.e + exitCount w n) + (if (w n).1 = 0 then 1 else 0) := by rw [ih h_ind]
      _ = x.e + (exitCount w n + (if (w n).1 = 0 then 1 else 0)) := by ring
      _ = x.e + exitCount w (n + 1) := by rw [h_exit]

/-- **Pathwise bound of Lemma 6.3**: on a run with unbounded exits, `theta^(G(4))` is at most
the lower limit of `Phi` along the run (`⊤` if the run never ends). -/
theorem FrogModel.LemmaX.epow_recOut_le (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2)
    (x : RState CState 4 4) (hx : Inv61 D x) (w : ℕ → Fin 5 × ℝ)
    (hw : ∀ m, ∃ n, m ≤ exitCount w n) :
    epow (ENNReal.ofReal (D.theta : ℝ)) (recOut (traj (rstep D.childStep) x w) 3) ≤
      liminf (fun n => PhiE D (traj (rstep D.childStep) x w n)) atTop := by
  set X := traj (rstep D.childStep) x w with hX
  have hinv : ∀ n, Inv61 D (X n) := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => exact inv61_rstep D h0 h1 (X n) ih (w n)
  have hθ1 : (1 : ℝ) < D.theta := by exact_mod_cast h2.2.2.2.1
  have hθ0 : (0 : ℝ) ≤ D.theta := by linarith
  have hlow : ∀ n, ENNReal.ofReal (D.theta : ℝ) ^ (X n).e ≤ PhiE D (X n) := by
    intro n
    unfold PhiE
    rw [← ENNReal.ofReal_pow hθ0]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast D.theta_pow_le_PhiQ h0 h1 h2 (X n) (hinv n).2.2)
  by_cases hab : ∃ N, ¬ (X N).i < 4
  · obtain ⟨N, hN⟩ := hab
    have hstay : ∀ k, X (N + k) = X N := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        show rstep D.childStep (X (N + k)) (w (N + k)) = X N
        rw [ih]
        exact rstep_of_absorbed D.childStep (X N) (by omega) _
    obtain ⟨_, hout⟩ := (hinv N).2.1.resolve_left hN
    have hrec : recOut X 3 ≤ ((X N).e : ℕ∞) := by
      rw [← hout]
      exact iInf_le _ N
    have hlim : liminf (fun n => PhiE D (X n)) atTop = PhiE D (X N) := by
      apply Filter.Tendsto.liminf_eq
      apply tendsto_atTop_of_eventually_const (i₀ := N)
      intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [hstay]
    rw [hlim]
    refine le_trans ?_ (hlow N)
    have hne : recOut X 3 ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hrec
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 hne
    unfold epow
    rw [ite_eq_right hne, ← hr, ENat.toNat_natCast]
    rw [← hr] at hrec
    exact pow_le_pow_right₀ (ENNReal.one_le_ofReal.2 hθ1.le) (Nat.cast_le.1 hrec)
  · have hlive : ∀ n, (X n).i < 4 := fun n => by
      by_contra h
      exact hab ⟨n, h⟩
    have hrec : recOut X 3 = ⊤ := by
      unfold recOut
      refine iInf_eq_top.2 fun n => ?_
      exact (hinv n).1.2 3 (by have := hlive n; change (X n).i ≤ 3; omega)
    rw [hrec]
    unfold epow
    rw [ite_eq_left rfl]
    have he : ∀ n, (X n).e = x.e + exitCount w n := fun n =>
      e_traj_of_live D.childStep x w n (fun k _ => hlive k)
    have hE : Tendsto (fun n => (X n).e) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun m => ?_
      obtain ⟨n, hn⟩ := hw m
      refine ⟨n, fun k hk => ?_⟩
      rw [he]
      have : exitCount w n ≤ exitCount w k :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hk))
      omega
    have htend : Tendsto (fun n => ENNReal.ofReal (D.theta : ℝ) ^ (X n).e) atTop (nhds ⊤) :=
      (ENNReal.tendsto_pow_atTop_nhds_top_iff.2 (by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hθ1)).comp hE
    calc (⊤ : ℝ≥0∞) = liminf (fun n => ENNReal.ofReal (D.theta : ℝ) ^ (X n).e) atTop :=
          htend.liminf_eq.symm
      _ ≤ liminf (fun n => PhiE D (X n)) atTop := liminf_le_liminf (Eventually.of_forall hlow)

namespace FrogModel.LemmaX

open FrogModel.Engine FrogModel.Cert

/-- **Lemma 6.3** for a table satisfying (I0), (I1), (I2): from a state of the invariant,
`E theta^(G(4)) ≤ Phi(state)` with `theta^⊤ = ⊤`. -/
theorem lemma61_gen (D : Data) (h0 : D.I0) (h1 : D.I1) (h2 : D.I2) (x : RState CState 4 4)
    (hx : Inv61 D x) :
    ∫⁻ w, epow (ENNReal.ofReal (D.theta : ℝ)) (recOut (traj (rstep D.childStep) x w) 3)
      ∂(iidMeasure ((unifDir 4).prod lam)) ≤ PhiE D x := by
  have hf : ∀ y z : RState CState 4 4,
      MeasurableSet {ξ : Fin 5 × ℝ | rstep D.childStep y ξ = z} :=
    fun y z => measurableSet_rstep_eq D.childStep D.measurableSet_childStep_eq y z
  have hν : ((unifDir 4).prod lam) {ξ : Fin 5 × ℝ | ξ.1 = 0} ≠ 0 := by
    have e : {ξ : Fin 5 × ℝ | ξ.1 = 0} = ({0} : Set (Fin 5)) ×ˢ Set.univ := by
      ext ξ; simp
    rw [e, Measure.prod_prod, measure_univ, mul_one]
    simp [ProbabilityTheory.uniformOn_univ]
  have hae := ae_exitCount_unbounded ((unifDir 4).prod lam) hν
  calc ∫⁻ w, epow (ENNReal.ofReal (D.theta : ℝ)) (recOut (traj (rstep D.childStep) x w) 3)
        ∂(iidMeasure ((unifDir 4).prod lam))
      ≤ ∫⁻ w, liminf (fun n => PhiE D (traj (rstep D.childStep) x w n)) atTop
          ∂(iidMeasure ((unifDir 4).prod lam)) :=
        lintegral_mono_ae (hae.mono fun w hw => epow_recOut_le D h0 h1 h2 x hx w hw)
    _ ≤ liminf (fun n => ∫⁻ w, PhiE D (traj (rstep D.childStep) x w n)
          ∂(iidMeasure ((unifDir 4).prod lam))) atTop :=
        lintegral_liminf_le fun n => measurable_comp_traj _ hf _ n x
    _ ≤ liminf (fun _ : ℕ => PhiE D x) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => lintegral_PhiE_traj_le D h0 h1 h2 n x hx)
    _ = PhiE D x := liminf_const _

/-- **Lemma 6.3 of the paper for `cand`**. -/
theorem lemma61_holds : Lemma61 := fun x hv hi hwf =>
  lemma61_gen cand cand_I0 cand_I1 cand_I2 x ⟨hv, hi, hwf⟩

end FrogModel.LemmaX
