module

public import FrogModel.LemmaX.CertStatement
public import FrogModel.LemmaX.LawMain
public import FrogModel.Cert.Sound
public import FrogModel.TheoremA

@[expose] public section

/-!
# Lemma X at `d = 4` from `Phi_4(H*) ≤ H*`

`meanHstar_holds`: `E B*(1) = c` under the certificate law of `cand` (from `c_eq_tsum` of
FrogModel.Cert.Sound). `lemmaXFour_of`: `CurveLawZero 4` and `CurveLawSucc 4`
(Lemma 4.3 of the paper), Claim A and `PhiSuper` give `E X ≤ c` (`lemmaXOfSuper_holds`), and
`transient_four_of` gives `Transient 4` through Theorem A, Theorem 2.2 of the paper
(`transient_of_meanX_lt_one`).
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.LemmaX

open FrogModel.Cert

/-- The integral against a finite sum of measures. -/
theorem lintegral_list_sum_measure {α : Type*} [MeasurableSpace α] (f : α → ℝ≥0∞)
    (l : List (Measure α)) : ∫⁻ x, f x ∂l.sum = (l.map fun μ => ∫⁻ x, f x ∂μ).sum := by
  induction l with
  | nil => simp
  | cons μ l ih => simp [lintegral_add_measure, ih]

/-- `ofReal` of a sum of nonnegative reals. -/
theorem ofReal_list_sum {β : Type*} (l : List β) (f : β → ℝ) (hf : ∀ b ∈ l, 0 ≤ f b) :
    ENNReal.ofReal (l.map f).sum = (l.map fun b => ENNReal.ofReal (f b)).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.ofReal_add (hf b (List.mem_cons_self ..)) (List.sum_nonneg fun x hx => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      exact hf c (List.mem_cons_of_mem _ hc)), ih fun c hc => hf c (List.mem_cons_of_mem _ hc)]

/-- The first coordinate of the block of a path is its first increment. -/
theorem pathBlock_zero (J : ℕ) (hJ : 0 < J) (π : List Tr) :
    pathBlock J π ⟨0, hJ⟩ = (firstInc π : ℕ∞) := by
  cases π with
  | nil => simp [pathBlock, firstInc]
  | cons t π => simp [pathBlock, firstInc]

/-- `E_tab B(1)` as an integral. -/
theorem lintegral_first_tabLaw (D : Data) (hJ : 0 < D.J) :
    ∫⁻ B, ((B ⟨0, hJ⟩ : ℕ∞) : ℝ≥0∞) ∂D.tabLaw =
      ((D.paths D.J 0 0).map fun π =>
        ENNReal.ofReal (pathProb π : ℝ) * ((firstInc π : ℕ) : ℝ≥0∞)).sum := by
  unfold Data.tabLaw
  rw [lintegral_list_sum_measure, List.map_map]
  congr 1
  refine List.map_congr_left fun π _ => ?_
  simp only [Function.comp_apply, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_dirac, pathBlock_zero D.J hJ π]
  rfl

/-- The mean of the first coordinate under the tail law. -/
theorem lintegral_first_tailLaw (D : Data) (hJ : 0 < D.J) :
    ∫⁻ B, ((B ⟨0, hJ⟩ : ℕ∞) : ℝ≥0∞) ∂D.tailLaw =
      ∑' n : ℕ, ENNReal.ofReal (((1 - D.rho) * D.rho ^ n : ℚ) : ℝ) *
        ((D.T + 1 + n : ℕ) : ℝ≥0∞) := by
  unfold Data.tailLaw
  rw [lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rfl

/-- **`E B*(1) = c`** for the certificate law of a table satisfying (I0) and (I1). -/
theorem lintegral_first_hstar (D : Data) (h0 : D.I0) (h1 : D.I1) (hJ : 0 < D.J) :
    ∫⁻ B, ((B ⟨0, hJ⟩ : ℕ∞) : ℝ≥0∞) ∂D.hstar = ENNReal.ofReal (D.c : ℝ) := by
  obtain ⟨_, _, heps0, heps1, hrho0, hrho1, _⟩ := h0
  have hrho0' : (0 : ℝ) ≤ D.rho := by exact_mod_cast hrho0.le
  have hrho1' : (D.rho : ℝ) < 1 := by exact_mod_cast hrho1
  have heps0' : (0 : ℝ) ≤ D.eps := by exact_mod_cast heps0.le
  have heps1' : (0 : ℝ) ≤ 1 - D.eps := by
    have : (D.eps : ℝ) < 1 := by exact_mod_cast heps1
    linarith
  unfold Data.hstar
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_first_tabLaw D hJ, lintegral_first_tailLaw D hJ, Data.c_eq_tsum D ⟨‹_›, ‹_›,
      heps0, heps1, hrho0, hrho1, ‹_›⟩ h1]
  have hpos : ∀ π ∈ D.paths D.J 0 0, (0 : ℝ) ≤ (pathProb π : ℝ) * (firstInc π : ℝ) := by
    intro π hπ
    have := D.paths_prob_pos h1 D.J 0 0 π hπ
    have : (0 : ℝ) ≤ (pathProb π : ℝ) := by exact_mod_cast this.le
    positivity
  have hfin : ENNReal.ofReal ((((D.paths D.J 0 0).map fun π =>
      pathProb π * (firstInc π : ℚ)).sum : ℚ) : ℝ) = ((D.paths D.J 0 0).map fun π =>
        ENNReal.ofReal (pathProb π : ℝ) * ((firstInc π : ℕ) : ℝ≥0∞)).sum := by
    rw [Rat.cast_list_sum, List.map_map]
    have hc : ((Rat.cast : ℚ → ℝ) ∘ fun π => pathProb π * (firstInc π : ℚ)) =
        fun π => (pathProb π : ℝ) * (firstInc π : ℝ) := by
      funext π; simp
    rw [hc, ofReal_list_sum _ _ hpos]
    congr 1
    refine List.map_congr_left fun π hπ => ?_
    have := D.paths_prob_pos h1 D.J 0 0 π hπ
    have : (0 : ℝ) ≤ (pathProb π : ℝ) := by exact_mod_cast this.le
    rw [ENNReal.ofReal_mul this, ENNReal.ofReal_natCast]
  have hterm : ∀ n : ℕ, (0 : ℝ) ≤ (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * ((D.T : ℝ) + 1 + n) := by
    intro n
    have : (0 : ℝ) ≤ 1 - (D.rho : ℝ) := by linarith
    positivity
  have hsum : Summable fun n : ℕ => (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * ((D.T : ℝ) + 1 + n) :=
    (tail_mean (D.rho : ℝ) D.T hrho0' hrho1').summable
  have htail : ENNReal.ofReal (∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n *
      ((D.T : ℝ) + 1 + n)) = ∑' n : ℕ, ENNReal.ofReal (((1 - D.rho) * D.rho ^ n : ℚ) : ℝ) *
        ((D.T + 1 + n : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hterm hsum]
    refine tsum_congr fun n => ?_
    have : (0 : ℝ) ≤ (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n := by
      have : (0 : ℝ) ≤ 1 - (D.rho : ℝ) := by linarith
      positivity
    rw [ENNReal.ofReal_mul this]
    congr 1
    · push_cast; rfl
    · rw [show ((D.T : ℝ) + 1 + n) = ((D.T + 1 + n : ℕ) : ℝ) by push_cast; ring,
        ENNReal.ofReal_natCast]
  have hfin0 : (0 : ℝ) ≤ ((((D.paths D.J 0 0).map fun π =>
      pathProb π * (firstInc π : ℚ)).sum : ℚ) : ℝ) := by
    rw [Rat.cast_list_sum, List.map_map]
    exact List.sum_nonneg fun x hx => by
      obtain ⟨π, hπ, rfl⟩ := List.mem_map.1 hx
      simpa using hpos π hπ
  have htail0 : (0 : ℝ) ≤ ∑' n : ℕ, (1 - (D.rho : ℝ)) * (D.rho : ℝ) ^ n * ((D.T : ℝ) + 1 + n) :=
    tsum_nonneg hterm
  rw [ENNReal.ofReal_add (mul_nonneg heps1' hfin0) (mul_nonneg heps0' htail0),
    ENNReal.ofReal_mul heps1', ENNReal.ofReal_mul heps0', hfin, htail]
  push_cast
  rfl

/-- **`E B*(1) = c`** for `cand`. -/
theorem meanHstar_holds : MeanHstar := by
  have h := lintegral_first_hstar cand cand_I0 cand_I1 (by decide)
  rw [cand_c] at h
  unfold MeanHstar Hstar
  refine h.trans ?_
  congr 1
  norm_num

/-- **Lemma X at `d = 4`** from the recursion (Lemma 4.3 of the paper) and `Phi_4(H*) ≤ H*`. -/
theorem lemmaXFour_of (h0 : FrogModel.Recursion.CurveLawZero 4)
    (hs : FrogModel.Recursion.CurveLawSucc 4) (hφ : PhiSuper) : LemmaXFour := by
  have hc0 : CouplingLE (FrogModel.Recursion.curveLaw 4 0)
      (FrogModel.Recursion.psiLaw 4 (Measure.dirac 0)) := by
    have := isProbabilityMeasure_curveLaw (d := 4) 0
    rw [← h0]
    exact couplingLE_refl _ measurableSet_le_curve
  have hcs : ∀ K, CouplingLE (FrogModel.Recursion.curveLaw 4 (K + 1))
      (FrogModel.Recursion.psiLaw 4 (FrogModel.Recursion.curveLaw 4 K)) := by
    intro K
    have := isProbabilityMeasure_curveLaw (d := 4) (K + 1)
    rw [← hs K]
    exact couplingLE_refl _ measurableSet_le_curve
  have h := lemmaXOfSuper_holds 4 4 (by norm_num) Hstar hc0 hcs
    (fun K => claimA_holds 4 K 4 (by norm_num)) hφ
  unfold LemmaXFour
  rw [← meanHstar_holds]
  exact h

/-- **The frog model on the 4-ary tree is transient**, from the recursion (Lemma 4.3 of the paper)
and `Phi_4(H*) ≤ H*`. -/
theorem transient_four_of (h0 : FrogModel.Recursion.CurveLawZero 4)
    (hs : FrogModel.Recursion.CurveLawSucc 4) (hφ : PhiSuper) : Transient 4 := by
  refine FrogModel.transient_of_meanX_lt_one (by norm_num) ?_
  refine lt_of_le_of_lt (lemmaXFour_of h0 hs hφ) ?_
  rw [ENNReal.ofReal_lt_one]
  norm_num

end FrogModel.LemmaX
