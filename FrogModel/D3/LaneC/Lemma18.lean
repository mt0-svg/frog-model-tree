module

public import FrogModel.D3.LaneC.Order

@[expose] public section

/-!
# Lemma 12.5 of the paper, parts (1), (2) and (3)

`lemma18_3_proof` is Lemma 12.5 (2) (worst case over the children heights), from the order facts of
`FrogModel.D3.LaneC.Order`. `lemma18_1_of` (one step, Lemma 12.5 (1)) and `ext_valid_of` (the
extension, Lemma 12.5 (3)) take the statements they use as hypotheses (the `Prop` statements of the
interfaces); FrogModel/D3/Assembly.lean instantiates them with their proofs.

One step: the deficits in the order `j = 1, 2, ...` (`T` is Lemma 10.7 (2) at `J = 0`, `L` is
Lemma 10.7 (2) with Lemmas 11.2 (B) and 11.3, `S2` is Lemma 12.1 (1), `P` is Lemma 10.7 (1)), then
the cdf rows (`C` the coins, `L` and `t<i>` the bounds of Lemma 11.1 (3) on the new deficits, `A<n0>`
Lemmas 11.2 (A) and 11.3, `S3` Lemma 12.1 (2), `J` the monotonicity of `G_(m+1)` in the number of
entrants, `G` that of a cdf).
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneC

/-! ## Facts on the planted curve -/

theorem cdfG_le_one' (m k v : ℕ) : cdfG m k v ≤ 1 := by
  unfold cdfG
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem cdfG_mono_g (m k : ℕ) {g g' : ℕ} (h : g ≤ g') : cdfG m k g ≤ cdfG m k g' := by
  unfold cdfG
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun π hπ => ?_)
  simp only [Set.mem_ofPred_eq] at hπ ⊢
  exact hπ.trans (by exact_mod_cast h)

theorem cdfG_succ_le (m k g : ℕ) : cdfG m (k + 1) g ≤ cdfG m k g := by
  unfold cdfG
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun π hπ => ?_)
  simp only [Set.mem_ofPred_eq] at hπ ⊢
  exact (plantedG_mono m k π).trans hπ

theorem closProb_le_one (m : ℕ) (A : Set ClosSample) : closProb m A ≤ 1 := by
  unfold closProb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem mu_pos (m k : ℕ) : 0 < mu m k := by unfold mu; positivity

theorem mu_le_mu_succ (m k : ℕ) : mu m k ≤ mu m (k + 1) := by
  unfold mu; push_cast; linarith

theorem meanG_nonneg' (m k : ℕ) : 0 ≤ meanG m k := ENNReal.toReal_nonneg

theorem deficit_le_mu (m k : ℕ) : deficit m k ≤ mu m k := by
  unfold deficit; linarith [meanG_nonneg' m k]

theorem ratio_self (m k j : ℕ) : ratio m m k j = mu m k / mu (m + 1) j := max_self _

/-- `Delta_m` is nonincreasing (Lemma 10.7 (1) of the paper, iterated). -/
theorem deficit_anti (h17a : lemma17a) (m : ℕ) {k k' : ℕ} (h : k ≤ k') :
    deficit m k' ≤ deficit m k := by
  induction k', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k' _ ih => exact (h17a m k').trans ih

/-- `Delta_m(k) ≥ 0`: `E G_m(k) ≤ mu_m(k)`. -/
theorem deficit_nonneg (hle : lintegral_plantedG_le) (m k : ℕ) : 0 ≤ deficit m k := by
  unfold deficit meanG
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hle m k)
  rw [ENNReal.toReal_ofReal (mu_pos m k).le] at h
  linarith

/-! ## Lemma 12.5 (2) of the paper -/

/-- **Lemma 12.5 (2) of the paper** (worst case): `Phi^S_m(S) ≤ Phi^S_[a, b](S)` for `m ∈ [a, b]`. -/
theorem lemma18_3_proof : lemma18_3 := by
  intro P a b m S hP hW ham hmb
  exact ⟨fun k _ g _ => Fnew_mono P S hP hW a b m ham hmb k g,
    fun k _ => deltaNew_mono P S hP hW a b m ham hmb k⟩

/-! ## Lemma 12.5 (1) of the paper: the deficits -/

section OneStep

variable (h17a : lemma17a) (h17b : lemma17b)
  (h16AC : lemma16AC) (h16BC : lemma16BC) (hS2 : lemmaS2)
  (hS3 : lemmaS3) (h12 : lemma12_G) (h12' : lemma12'_G)
  (hC : cdfG_le_binCdf)
  (P : StParams) (m : ℕ) (S : State) (hP : P.OK) (hW : S.WF P) (hS : Valid P m S)

include h17b h16BC hS2 hP hW hS in
/-- The terms `T`, `L` and `S2` of `delta'(j)` bound `Delta_(m+1)(j)`. -/
theorem deficit_le_dTerms (j : ℕ) (hj : 1 ≤ j) :
    deficit (m + 1) j ≤ dTerms P S m m j * mu (m + 1) j := by
  have hμ := mu_pos (m + 1) j
  have hE : 1 ≤ P.E := hP.1
  unfold dTerms
  rw [min_mul_of_nonneg _ _ hμ.le]
  refine le_min ?_ ?_
  · rw [← div_le_iff₀ hμ, Finset.le_fold_min]
    refine ⟨?_, fun J hJ => ?_⟩
    · -- `T`: Lemma 10.7 (2) of the paper at `J = 0`, `P = 1`
      rw [ratio_self]
      refine div_le_div_of_nonneg_right ?_ hμ.le
      have := h17b m j 0 hj 1 (closProb_le_one _ _)
      simpa using this
    · -- `L`: Lemma 10.7 (2) of the paper with `P_B(j, J) ≥ P(e_1 < J)` (Lemmas 11.2 (B) and 11.3)
      obtain ⟨hJ1, hJM⟩ := Finset.mem_Icc.mp hJ
      have hJE : J ≤ P.E := hJM.trans hP.2.1
      have hP0 : closProb m {x | closE (j + 1) x.1 x.2 0 < J} ≤ PB P S j J := by
        unfold PB
        refine Finset.le_inf' _ _ fun K hK => ?_
        obtain ⟨h1, h2⟩ := mem_grid P.GM (j + 1) K hK
        exact h16BC m j J K P.E P.GM S.F hj hJ1 hJE h1 h2 hS.1 hW.2.1 hW.1
      have key := lterm_bound (deficit (m + 1) j) (deficit m J) (mu m J) (S.delta J) (PB P S j J)
        _ (fun P hP => h17b m j J hj P hP) hP0 (closProb_le_one _ _) (hS.2 J hJE)
        (hW.2.2.1 J hJE).1 (hW.2.2.1 J hJE).2 (mu_pos m J).le
      rw [ratio_self]
      calc deficit (m + 1) j / mu (m + 1) j
          ≤ (S.delta J * (1 - PB P S j J) + PB P S j J) * mu m J / mu (m + 1) j :=
            div_le_div_of_nonneg_right key hμ.le
        _ = (S.delta J * (1 - PB P S j J) + PB P S j J) * (mu m J / mu (m + 1) j) := by ring
  · -- `S2`: Lemma 12.1 (1) of the paper with `D(k) = delta(k) mu_m(k)`
    have key := hS2 m j P.E P.GM hj hE (S.F 1) (fun g hg => hS.1 1 hE g hg)
      (fun g hg => hW.2.1 1 hE g hg) (fun g hg => hW.1 1 hE g hg) (fun k => S.delta k * mu m k)
      (fun k hk => hS.2 k hk)
    refine key.trans (le_of_eq ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hdiv := inf'_div k (fun k' => S.delta k' * mu m k') (mu (m + 1) j) hμ
    have hDt : Dt S m m j k =
        (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
          (fun k' => S.delta k' * mu m k') / mu (m + 1) j := by
      unfold Dt
      simp_rw [ratio_self, ← mul_div_assoc]
      exact hdiv
    rw [hDt]
    field_simp

include h17a h17b h16BC hS2 hP hW hS in
/-- The deficits of `Phi^S_m(S)` are valid at `m + 1`. -/
theorem deficit_le_deltaNew :
    ∀ j, deficit (m + 1) j ≤ deltaNew P S m m j * mu (m + 1) j
  | 0 => by
      rw [deltaNew, one_mul]
      exact deficit_le_mu _ _
  | 1 => by
      rw [deltaNew]
      exact deficit_le_dTerms h17b h16BC hS2 P m S hP hW hS 1 le_rfl
  | j + 2 => by
      rw [deltaNew, min_mul_of_nonneg _ _ (mu_pos _ _).le]
      refine le_min (deficit_le_dTerms h17b h16BC hS2 P m S hP hW hS (j + 2) (by omega)) ?_
      calc deficit (m + 1) (j + 2) ≤ deficit (m + 1) (j + 1) := h17a (m + 1) (j + 1)
        _ ≤ deltaNew P S m m (j + 1) * mu (m + 1) (j + 1) := deficit_le_deltaNew (j + 1)
        _ ≤ deltaNew P S m m (j + 1) * mu (m + 1) (j + 2) :=
            mul_le_mul_of_nonneg_left (mu_le_mu_succ _ _) (deltaNew_nonneg P S hP hW m m _)

/-! ## Lemma 12.5 (1) of the paper: the cdf rows -/

include h16AC hS3 h12 h12' hC hP hW hS in
/-- The terms of `F'(j, v)` bound `P(G_(m+1)(j) ≤ v)`, given the new deficits and a bound `prev`
on `P(G_(m+1)(j) ≤ v)` (the term `J`). -/
theorem cdfG_le_preF (hD : ∀ j, deficit (m + 1) j ≤ deltaNew P S m m j * mu (m + 1) j)
    (j v : ℕ) (hj : 1 ≤ j) (hv : v ≤ P.GM) (prev : ℝ) (hprev : cdfG (m + 1) j v ≤ prev) :
    cdfG (m + 1) j v ≤ preF P S m m j v prev := by
  have hE : 1 ≤ P.E := hP.1
  unfold preF
  refine le_min (le_min (hC (m + 1) j v) ?_) (le_min ?_ (le_min ?_ hprev))
  · -- `L` and `t<i>`: the bounds of Lemma 11.1 (3) of the paper
    unfold L12
    refine le_min (h12 (m + 1) j v _ (hD j)) ?_
    rw [Finset.le_fold_min]
    refine ⟨cdfG_le_one' _ _ _, fun i hi => ?_⟩
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have hi2' : (i : ℝ) ≤ 199 := by exact_mod_cast hi2
    exact h12' (m + 1) j v _ _ (hD j) (by positivity) (by rw [div_lt_one (by norm_num)]; linarith)
  · -- `A<n0>`: Lemmas 11.2 (A) and 11.3 of the paper
    split_ifs with hvVM
    · unfold PA
      refine Finset.le_inf' _ _ fun n0 hn0 => ?_
      obtain ⟨h1, h2⟩ := mem_grid P.GM (j + 1) n0 hn0
      exact h16AC m j v n0 P.E P.GM S.F hj hE h1 h2 hS.1 hW.2.1 hW.1
    · exact cdfG_le_one' _ _ _
  · -- `S3`: Lemma 12.1 (2) of the paper
    exact hS3 m j P.GM v hj hv (S.F 1) (fun g hg => hS.1 1 hE g hg) (fun g hg => hW.2.1 1 hE g hg)
      (fun g hg => hW.1 1 hE g hg)

include h16AC hS3 h12 h12' hC hP hW hS in
/-- The cdf rows of `Phi^S_m(S)` are valid at `m + 1`. -/
theorem cdfG_le_Fnew (hD : ∀ j, deficit (m + 1) j ≤ deltaNew P S m m j * mu (m + 1) j) :
    ∀ j, ∀ v ≤ P.GM, cdfG (m + 1) j v ≤ Fnew P S m m j v
  | 0, v, _ => by
      simp only [Fnew]
      exact cdfG_le_one' _ _ _
  | j + 1, v, hv => by
      simp only [Fnew]
      rw [Finset.le_fold_min]
      refine ⟨cdfG_le_preF h16AC hS3 h12 h12' hC P m S hP hW hS hD (j + 1) v (by omega) hv _
        ((cdfG_succ_le _ _ _).trans (cdfG_le_Fnew hD j v hv)), fun v' hv' => ?_⟩
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hv'
      exact (cdfG_mono_g _ _ h1).trans (cdfG_le_preF h16AC hS3 h12 h12' hC P m S hP hW hS hD
        (j + 1) v' (by omega) h2 _ ((cdfG_succ_le _ _ _).trans (cdfG_le_Fnew hD j v' h2)))

end OneStep

/-- **Lemma 12.5 (1) of the paper** (one step), from the statements of Lemmas 10.7, 11.1, 11.3 and
12.1. -/
theorem lemma18_1_of (h17a : lemma17a) (h17b : lemma17b)
    (h16AC : lemma16AC) (h16BC : lemma16BC) (hS2 : lemmaS2)
    (hS3 : lemmaS3) (h12 : lemma12_G) (h12' : lemma12'_G)
    (hC : cdfG_le_binCdf) : lemma18_1 := by
  intro P m S hP hW hS
  have hD := deficit_le_deltaNew h17a h17b h16BC hS2 P m S hP hW hS
  exact ⟨fun k _ g hg => cdfG_le_Fnew h16AC hS3 h12 h12' hC P m S hP hW hS hD k g hg,
    fun k _ => hD k⟩

/-! ## The extension (Lemma 12.5 (3) of the paper) -/

section Ext

variable (h17a : lemma17a) (hle : lintegral_plantedG_le)
  (h12 : lemma12_G) (h12' : lemma12'_G) (hC : cdfG_le_binCdf)
  (P0 P : StParams) (h : ℕ) (S : State) (hS : Valid P0 h S)

include hle hS in
theorem delta_nonneg_of_valid (k : ℕ) (hk : k ≤ P0.E) : 0 ≤ S.delta k := by
  have h1 := (deficit_nonneg hle h k).trans (hS.2 k hk)
  exact nonneg_of_mul_nonneg_left h1 (mu_pos h k)

include h17a hle hS in
/-- The deficits of `ext_h(S)` are valid at `h`. -/
theorem deficit_le_deltaExt : ∀ k, deficit h k ≤ deltaExt P0 h S k * mu h k
  | 0 => by
      rw [deltaExt, one_mul]
      exact deficit_le_mu _ _
  | k + 1 => by
      have hμ := mu_pos h (k + 1)
      rw [deltaExt, min_mul_of_nonneg _ _ hμ.le, min_mul_of_nonneg _ _ hμ.le,
        min_mul_of_nonneg _ _ hμ.le, one_mul]
      refine le_min (le_min (deficit_le_mu _ _) ?_) (le_min ?_ ?_)
      · -- `T`: `Delta_h(k + 1) ≤ Delta_h(0) ≤ mu_h(0)`
        rw [div_mul_cancel₀ _ hμ.ne']
        exact (deficit_anti h17a h (Nat.zero_le _)).trans (deficit_le_mu _ _)
      · -- `P`
        calc deficit h (k + 1) ≤ deficit h k := h17a h k
          _ ≤ deltaExt P0 h S k * mu h k := deficit_le_deltaExt k
          _ ≤ deltaExt P0 h S k * mu h (k + 1) :=
              mul_le_mul_of_nonneg_left (mu_le_mu_succ _ _)
                (deltaExt_nonneg P0 h S (fun k hk => delta_nonneg_of_valid hle P0 h S hS k hk) k)
      · split_ifs with hk
        · exact hS.2 (k + 1) hk
        · -- `X`: `Delta_h(k + 1) ≤ Delta_h(E0) ≤ delta(E0) mu_h(E0)`
          rw [div_mul_cancel₀ _ hμ.ne']
          exact (deficit_anti h17a h (by omega)).trans (hS.2 P0.E le_rfl)

include h12 h12' hC hS in
theorem cdfG_le_preExt (hD : ∀ k, deficit h k ≤ deltaExt P0 h S k * mu h k) (k g : ℕ)
    (prev : ℝ) (hprev : cdfG h k g ≤ prev) : cdfG h k g ≤ preExt P0 h S k g prev := by
  unfold preExt
  refine le_min (le_min ?_ (hC h k g)) (le_min ?_ hprev)
  · split_ifs with hk
    · exact hS.1 k hk.1 g hk.2
    · exact cdfG_le_one' _ _ _
  · unfold L12
    refine le_min (h12 h k g _ (hD k)) ?_
    rw [Finset.le_fold_min]
    refine ⟨cdfG_le_one' _ _ _, fun i hi => ?_⟩
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have hi2' : (i : ℝ) ≤ 199 := by exact_mod_cast hi2
    exact h12' h k g _ _ (hD k) (by positivity) (by rw [div_lt_one (by norm_num)]; linarith)

include h12 h12' hC hS in
theorem cdfG_le_FExt (hD : ∀ k, deficit h k ≤ deltaExt P0 h S k * mu h k) :
    ∀ k, ∀ g ≤ P.GM, cdfG h k g ≤ FExt P0 P h S k g
  | 0, g, _ => by
      simp only [FExt]
      exact cdfG_le_one' _ _ _
  | k + 1, g, hg => by
      simp only [FExt]
      rw [Finset.le_fold_min]
      refine ⟨cdfG_le_preExt h12 h12' hC P0 h S hS hD (k + 1) g _
        ((cdfG_succ_le _ _ _).trans (cdfG_le_FExt hD k g hg)), fun g' hg' => ?_⟩
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hg'
      exact (cdfG_mono_g _ _ h1).trans (cdfG_le_preExt h12 h12' hC P0 h S hS hD (k + 1) g' _
        ((cdfG_succ_le _ _ _).trans (cdfG_le_FExt hD k g' h2)))

end Ext

/-- **The extension lemma** (Lemma 12.5 (3) of the paper), from the statements of Lemmas 10.2, 10.7
and 11.1. -/
theorem ext_valid_of (h17a : lemma17a) (hle : lintegral_plantedG_le)
    (h12 : lemma12_G) (h12' : lemma12'_G) (hC : cdfG_le_binCdf) :
    ext_valid := by
  intro P0 P h S _ _ hS
  have hD := deficit_le_deltaExt h17a hle P0 h S hS
  exact ⟨fun k _ g hg => cdfG_le_FExt h12 h12' hC P0 P h S hS hD k g hg, fun k _ => hD k⟩

end FrogModel.D3.LaneC
