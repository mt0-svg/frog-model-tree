module

public import FrogModel.D3.Interfaces.Assembly
public import FrogModel.D3.LaneA.Delivered
public import FrogModel.D3.LaneA.Lemma19
public import FrogModel.D3.LaneA.FutureDom
public import FrogModel.D3.LaneA.Depth
public import FrogModel.D3.LaneB.Lemma12
public import FrogModel.D3.LaneB.Lemma17
public import FrogModel.D3.LaneB.Lemma16Prob
public import FrogModel.D3.LaneB.Coins
public import FrogModel.D3.LaneB.Lemma9
public import FrogModel.D3.LaneB.Lemma8
public import FrogModel.D3.LaneB.Lemma8a
public import FrogModel.D3.LaneB.Concentration
public import FrogModel.D3.LaneB.ClosMean
public import FrogModel.D3.LaneC.Lemma18
public import FrogModel.D3.LaneC.S2S3
public import FrogModel.D3.LaneC.Seed
public import FrogModel.D3.LaneE.Table
public import FrogModel.D3.LaneE.Induction
public import FrogModel.D3.LaneE.Tail
public import FrogModel.D3.M1L.F3LMain

@[expose] public section

/-!
# The d = 3 route

Section 15 of the paper, and the proof of Theorem 1.3 in Section 8. The interface statements
(`Prop` definitions of FrogModel/D3/Interfaces) are proved here from their proofs in
FrogModel/D3/LaneA to FrogModel/D3/LaneE, the hypotheses of each `_of` theorem filled the same way,
down to the proofs with no hypothesis. Theorem 8.4 (`linear_three`) and `recurrent_three_of_m1`
take as hypothesis the one statement not proved here, the run and the certificate of
Proposition 15.1 (`m1run_certS`, proved in FrogModel/D3/Chain/Final.lean).
-/

namespace FrogModel.D3.Assembly

/-! ## The planted model and the closure (Sections 8 and 10 of the paper) -/

theorem lintegral_plantedG_le_proof : Iface.lintegral_plantedG_le :=
  Iface.lintegral_plantedG_le_of LaneA.prob_reach_proof

/-! ## Tails and the closure bounds (Sections 10 and 11 of the paper) -/

universe u v in
theorem lemmaS2'_proof : Iface.lemmaS2'.{u, v} :=
  Iface.lemmaS2'_of LaneA.measurable_plantedPair_proof LaneA.Pool.curveLaw_succ_proof
    LaneA.coin_coupling_proof lintegral_plantedG_le_proof

theorem lemma17a_proof : Iface.lemma17a :=
  Iface.lemma17a_of LaneA.measurable_plantedPair_proof LaneA.coin_coupling_proof
    lintegral_plantedG_le_proof

theorem d1_proof : Iface.d1 :=
  Iface.d1_of LaneA.measurable_plantedPair_proof LaneA.Pool.curveLaw_succ_proof
    LaneA.coin_coupling_proof

theorem lemma8a_proof : Iface.lemma8a :=
  Iface.lemma8a_of LaneA.measurable_plantedPair_proof LaneA.future_dom_proof

theorem lemma17b_proof : Iface.lemma17b :=
  Iface.lemma17b_of d1_proof lemma8a_proof

theorem lemma16A_proof : Iface.lemma16A :=
  Iface.lemma16A_of LaneA.measurable_plantedPair_proof LaneA.Pool.curveLaw_succ_proof

theorem lemma16B_proof : Iface.lemma16B :=
  Iface.lemma16B_of LaneA.measurable_plantedPair_proof

theorem lemma16C_proof : Iface.lemma16C :=
  Iface.lemma16C_of LaneA.measurable_plantedPair_proof

theorem lemma16AC_proof : Iface.lemma16AC :=
  Iface.lemma16AC_of lemma16A_proof lemma16C_proof

theorem lemma16BC_proof : Iface.lemma16BC :=
  Iface.lemma16BC_of lemma16B_proof lemma16C_proof

theorem lemma12_G_proof : Iface.lemma12_G :=
  Iface.lemma12_G_of Iface.lemma12_general_proof LaneA.measurable_plantedPair_proof
    LaneA.prob_reach_proof

theorem lemma12'_G_proof : Iface.lemma12'_G :=
  Iface.lemma12'_G_of Iface.lemma12'_general_proof LaneA.measurable_plantedPair_proof
    LaneA.prob_reach_proof

theorem cdfG_le_binCdf_proof : Iface.cdfG_le_binCdf :=
  Iface.cdfG_le_binCdf_of LaneA.measurable_plantedPair_proof LaneA.coin_coupling_proof

theorem lemma9_proof : Iface.lemma9 :=
  Iface.lemma9_of LaneA.measurable_plantedPair_proof

theorem lemma9_two_proof : Iface.lemma9_two :=
  Iface.lemma9_two_of lemma9_proof

/-! ## The lower closures, the step map and the seed (Sections 12 and 13 of the paper) -/

theorem lemmaS2_proof : Iface.lemmaS2 :=
  LaneC.lemmaS2_of LaneA.measurable_plantedPair_proof LaneA.coin_coupling_proof
    lintegral_plantedG_le_proof lemma17a_proof lemmaS2'_proof

theorem lemmaS3_proof : Iface.lemmaS3 :=
  LaneC.lemmaS3_of LaneA.measurable_plantedPair_proof LaneA.Pool.curveLaw_succ_proof
    LaneA.coin_coupling_proof

theorem lemma18_1_proof : Iface.lemma18_1 :=
  LaneC.lemma18_1_of lemma17a_proof lemma17b_proof lemma16AC_proof lemma16BC_proof lemmaS2_proof
    lemmaS3_proof lemma12_G_proof lemma12'_G_proof cdfG_le_binCdf_proof

theorem ext_valid_proof : Iface.ext_valid :=
  LaneC.ext_valid_of lemma17a_proof lintegral_plantedG_le_proof lemma12_G_proof lemma12'_G_proof
    cdfG_le_binCdf_proof

theorem seed_valid_proof : Iface.seed_valid :=
  LaneC.seed_valid_of lemma17a_proof lemma12_G_proof lemma12'_G_proof cdfG_le_binCdf_proof

/-! ## Theorem 14.1 of the paper -/

theorem thmDprime1_proof : Iface.thmDprime1 :=
  LaneE.thmDprime1_of LaneA.measurable_plantedPair_proof lintegral_plantedG_le_proof
    lemma12_G_proof LaneA.lemma10_proof lemma9_two_proof lemma8a_proof Iface.lemma8b_of d1_proof

/-! ## The route -/

section Route

open MeasureTheory Filter Iface
open scoped ENNReal

/-- **Theorem 8.4 of the paper** (its proof in Section 15): `E G_m(1) ≥ (3/5) mu_m(1) = (m + 2)/5`
for every `m > m1 - 30`, `m1 = 1778279`, from the run and the certificate of Proposition 15.1
(`m1run_certS`). The seed at 100 (Lemma 13.4), the certified chain to `m1` (Lemma 12.5 (5)), then
Theorem 14.1 on the parameters of the table below `10^30` (Proposition 15.2) and of Lemma 14.3
above. -/
theorem linear_three (hD1 : Iface.m1run_certS) :
    ∀ m, m1 - 30 < m → c0 * mu m 1 ≤ meanG m 1 := by
  -- The seed at 100 from the run (Proposition 13.3 and Lemma 13.4).
  obtain ⟨R, hR, hcert⟩ := hD1
  have hkP : ∀ k, k ≤ P0.E → k + 1 ≤ 96 := fun k hk => by simp only [P0] at hk; omega
  have hF' : ∀ k, 1 ≤ k → k ≤ P0.E → _ := fun k hk1 hkE =>
    f3L_holds 48 96 60 100 (by norm_num) (by norm_num) (by norm_num) (by norm_num) R hR.1 k hk1
      (hkP k hkE) (R.Wt (k + 1))
      (fun x hx f hf => hR.2 (k + 1) (by omega) (by simp only [P0] at hkE; omega) x hx f hf)
  have hs : Valid P0 100 (seedState 48 100 96 (topMass R)) :=
    seed_valid_proof 48 100 P0 (topMass R) (fun k hk1 hkE g hg => (hF' k hk1 hkE).1 g hg)
      (fun k hk1 hkE => (hF' k hk1 hkE).2)
  -- The certificate (Proposition 15.1 (2)) and Lemma 12.5 (5).
  obtain ⟨S0', P, hn, Sn, T, hle0, hW0, hchain, hSnT, hWT, hOK, hfix, hhn, hE62, hd1, hd62⟩ :=
    hcert
  have hval : ∀ m, hn ≤ m → m ≤ m1 → Valid P m T :=
    lemma18_6_of lemma18_1_proof LaneC.lemma18_3_proof ext_valid_proof P0 100 S0'
      (valid_mono hs hle0) hW0 P hn Sn hchain T hSnT hWT hOK m1 hfix
  -- The assumptions of Theorem 14.1 from the validity of `T` (Section 15).
  have hB1 : ∀ h, m1 - 30 < h → h ≤ m1 → c0 * mu h 1 ≤ meanG h 1 := by
    intro h h1 h2
    have hv := (hval h (by omega) h2).2 1 (by omega)
    have := mul_le_mul_of_nonneg_right hd1 (mu_pos h 1).le
    unfold deficit at hv
    unfold c0
    linarith
  have hB62 : b1 ≤ meanG m1 62 := by
    have hv := (hval m1 (by omega) le_rfl).2 62 hE62
    have hmu : mu m1 62 = 1778342 / 3 := by unfold mu m1; norm_num
    unfold deficit at hv
    rw [hmu] at hv
    have := mul_le_mul_of_nonneg_right hd62 (by norm_num : (0 : ℝ) ≤ 1778342 / 3)
    unfold b1
    linarith
  -- Theorem 14.1 on the glued parameters (Proposition 15.2 below `10^30`, Lemma 14.3 above).
  obtain ⟨J, D, k, y, k1, hJ62, hJmono, hJ140, hcond⟩ := LaneE.dcheck1_holds
  have hJ'62 : Iface.glue J Jtail m1 = 62 := by rw [Iface.glue, ite_eq_left m1_lt]; exact hJ62
  have hJ'mono : MonotoneOn (Iface.glue J Jtail) (Set.Ici m1) := by
    intro a ha b hb hab
    have hm1 : m1 ≤ 10 ^ 30 := m1_lt.le
    simp only [Iface.glue]
    by_cases hb' : b < 10 ^ 30
    · have ha' : a < 10 ^ 30 := lt_of_le_of_lt hab hb'
      rw [ite_eq_left ha', ite_eq_left hb']
      exact hJmono ⟨ha, ha'.le⟩ ⟨hb, hb'.le⟩ hab
    · rw [ite_eq_right hb']
      by_cases ha' : a < 10 ^ 30
      · rw [ite_eq_left ha']
        calc J a ≤ J (10 ^ 30) := hJmono ⟨ha, ha'.le⟩ ⟨hm1, le_rfl⟩ ha'.le
          _ ≤ 140 := hJ140
          _ ≤ Jtail b := le_max_left _ _
      · rw [ite_eq_right ha']
        unfold Jtail
        refine max_le_max le_rfl (Nat.ceil_mono (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
        have hapos : (0 : ℝ) < a :=
          Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) (not_lt.mp ha'))
        exact Real.log_le_log hapos (by exact_mod_cast hab)
  have hcond' : ∀ m, m1 ≤ m →
      DCond (Iface.glue J Jtail) (Iface.glue D Dtail) (Iface.glue k ktail) (Iface.glue y ytail)
        (Iface.glue k1 ktail) m := by
    intro m hm
    by_cases h : m < 10 ^ 30
    · have := hcond m hm h.le
      unfold DCond at this ⊢
      simp only [Iface.glue, ite_eq_left h]
      exact this
    · have := LaneE.dprime_tail_holds m (not_lt.mp h)
      unfold DCond at this ⊢
      simp only [Iface.glue, ite_eq_right h]
      exact this
  exact thmDprime1_proof (Iface.glue J Jtail) (Iface.glue D Dtail) (Iface.glue k ktail)
    (Iface.glue y ytail) (Iface.glue k1 ktail) hJ'62 hJ'mono hcond' hB1 hB62

/-- Theorem 8.4 in the form of the paper: `E G_m(1) ≥ (m + 2)/5` for every `m > m1 - 30`. -/
theorem linear_three' (hD1 : Iface.m1run_certS) :
    ∀ m, m1 - 30 < m → ((m : ℝ) + 2) / 5 ≤ meanG m 1 := by
  intro m hm
  have h := linear_three hD1 m hm
  have : c0 * mu m 1 = ((m : ℝ) + 2) / 5 := by unfold c0 mu; push_cast; ring
  linarith

/-- **The d = 3 route** (Theorem 1.3 of the paper): `Recurrent 3` from Theorem 8.4 and Lemma 8.3
(`E Z_(m+1) ≥ (1 + E G_m(1))/4`), so `E Z_n / n ≥ 1/20` for `n > m1`, through Theorem 8.2. Its
hypotheses are those of `linear_three`. -/
theorem recurrent_three_of_m1 (hD1 : Iface.m1run_certS) : FrogModel.Recurrent 3 := by
  have hlin := linear_three' hD1
  apply recurrent_three_of_plantedCount
  have hev : ∀ᶠ m : ℕ in atTop,
      (1 / 20 : ℝ≥0∞) ≤ (∫⁻ ζ, LemmaR.plantedCount m ζ ∂frogMeasure 3) / m := by
    filter_upwards [eventually_ge_atTop m1] with m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by unfold m1 at hm; omega⟩
    have h19 := LaneA.lemma19_proof n
    have hfin := lintegral_plantedG_le_proof n 1
    have heq : ∫⁻ π, (Iface.plantedG n 1 π : ℝ≥0∞) ∂pathMeasure =
        ENNReal.ofReal (meanG n 1) := by
      unfold meanG
      rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin)]
    rw [heq] at h19
    exact ratio_bound n (meanG n 1) (hlin n (by unfold m1 at hm ⊢; omega)) _ h19
  have hle : (1 / 20 : ℝ≥0∞) ≤
      limsup (fun m : ℕ => (∫⁻ ζ, LemmaR.plantedCount m ζ ∂frogMeasure 3) / m) atTop :=
    le_limsup_of_frequently_le hev.frequently
  exact lt_of_lt_of_le (by norm_num) hle

end Route

end FrogModel.D3.Assembly
