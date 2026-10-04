module

public import FrogModel.D3.M1L.Height1

@[expose] public section

/-!
# M1_L at height 1: the law on the chain

The law of the run at `m = 1` (the case `m = 1` of Lemma 13.2 of the paper), on the stream: the chain
`h1step` reads i.i.d. directions and coins (`map_dc_iid`); from a state of `G1` that is not an end
it ends with `b` top ups with probability `W1 p b` (`law_height1`), an instance of `chain_law`.
The supersolution identities are `W1_round`, `W1_inner` (Height1.lean) and `W1_kill`; the time bound
`T1` drops by one on average at each read (`T1_round`, `T1_inner`, `T1_kill`).
-/

open MeasureTheory ProbabilityTheory FrogModel
open scoped ENNReal

namespace FrogModel.D3


/-- An integral against the law of a direction and a coin: the mean over the four directions. -/
theorem lintegral_dc (F : Fin 4 × ℕ → ℝ≥0∞) :
    ∫⁻ x, F x ∂(dirLaw.prod coinLaw) =
      ∑ d : Fin 4, (∫⁻ j, F (d, j) ∂coinLaw) / 4 := by
  have hmeas : AEMeasurable F (dirLaw.prod coinLaw) :=
    (Measurable.of_discrete (α := Fin 4 × ℕ)).aemeasurable
  rcases lintegral_dirLaw with ⟨_, h⟩
  calc
    ∫⁻ x, F x ∂(dirLaw.prod coinLaw) = ∫⁻ d, ∫⁻ j, F (d, j) ∂coinLaw ∂dirLaw := by
      rw [MeasureTheory.lintegral_prod F hmeas]
    _ = (∑ d : Fin 4, (∫⁻ j, F (d, j) ∂coinLaw)) / 4 := by rw [h]
    _ = ∑ d : Fin 4, (∫⁻ j, F (d, j) ∂coinLaw) / 4 := by rw [ENNReal.sum_div]


/-- The kill coin: an integral of a two-valued function of a coin. -/
theorem lintegral_coin_bool (g : ℕ → Bool) (A B : ℝ≥0∞) :
    ∫⁻ j, (if g j = true then A else B) ∂coinLaw =
      coinLaw {j | g j = true} * A + (1 - coinLaw {j | g j = true}) * B := by
  set S := {j | g j = true} with hS
  have hS_meas : MeasurableSet S := MeasurableSet.of_discrete
  have h_indicator_eq : (fun (j : ℕ) => if g j = true then A else B) = S.indicator (fun _ => A) + Sᶜ.indicator (fun _ => B) := by
    ext j
    by_cases hj : g j = true
    · simp [S, hj]
    · simp [S, hj]
  calc
    ∫⁻ j, (if g j = true then A else B) ∂coinLaw
        = ∫⁻ j, (S.indicator (fun _ => A) + Sᶜ.indicator (fun _ => B)) j ∂coinLaw := by rw [h_indicator_eq]
    _ = (∫⁻ j, S.indicator (fun _ => A) j ∂coinLaw) + (∫⁻ j, Sᶜ.indicator (fun _ => B) j ∂coinLaw) := by
      simpa using lintegral_add_left (Measurable.indicator measurable_const hS_meas) (Sᶜ.indicator (fun _ => B))
    _ = (A * coinLaw S) + (B * coinLaw (Sᶜ)) := by
      rw [lintegral_indicator_const hS_meas A, lintegral_indicator_const hS_meas.compl B]
    _ = (A * coinLaw S) + (B * (1 - coinLaw S)) := by rw [prob_compl_eq_one_sub hS_meas]
    _ = coinLaw S * A + (1 - coinLaw S) * B := by ring


/-- The directions and coins read form an i.i.d. sequence of law `dirLaw.prod coinLaw`. -/
theorem map_dc_iid :
    (FrogModel.Engine.iidMeasure valLaw).map (fun y (n : ℕ) => ((y n).1.2, (y n).2)) =
      FrogModel.Engine.iidMeasure (dirLaw.prod coinLaw) := by
  unfold FrogModel.Engine.iidMeasure
  let f : ℕ → Val → Fin 4 × ℕ := fun n x => (x.1.2, x.2)
  have hmeas : ∀ n : ℕ, Measurable (f n) := by
    intro n
    apply measurable_of_countable
  have h_pi := Measure.infinitePi_map_pi (μ := fun _ : ℕ => valLaw) hmeas
  have h_target : (Measure.infinitePi fun _ : ℕ => valLaw).map (fun y (n : ℕ) => ((y n).1.2, (y n).2)) =
      Measure.infinitePi fun n => (valLaw.map (f n)) := by
    simpa [f] using h_pi
  rw [h_target]
  congr! with n
  -- Goal: valLaw.map (f n) = dirLaw.prod coinLaw
  have h_fun_eq : f n = (fun (x : Val) => (x.1.2, x.2)) := by rfl
  rw [h_fun_eq]
  calc
    valLaw.map (fun (x : Val) => (x.1.2, x.2)) = valLaw.map (Prod.map Prod.snd id) := by
      refine congrArg (fun g => valLaw.map g) ?_
      funext x
      apply Prod.ext
      · rfl
      · rfl
    _ = ((stepLaw 3).map (fun (x : Step 3) => x.2)).prod (coinLaw.map id) := by
      rw [show valLaw = (stepLaw 3).prod coinLaw from rfl]
      rw [← Measure.map_prod_map (stepLaw 3) coinLaw measurable_snd measurable_id]
    _ = ((stepLaw 3).map (fun (x : Step 3) => x.2)).prod coinLaw := by simp
    _ = dirLaw.prod coinLaw := by
      have h_snd : (stepLaw 3).map (fun (x : Step 3) => x.2) = dirLaw := by
        have h_map_dir := map_dir_valLaw
        rw [show valLaw = (stepLaw 3).prod coinLaw from rfl] at h_map_dir
        have h_fun_eq2 : (fun (x : Val) => x.1.2) = Prod.snd ∘ Prod.fst := by
          funext x; rfl
        rw [h_fun_eq2] at h_map_dir
        rw [← Measure.map_map measurable_snd measurable_fst] at h_map_dir
        rw [Measure.map_fst_prod] at h_map_dir
        have h_coin_univ : coinLaw Set.univ = 1 := by
          have : IsProbabilityMeasure coinLaw := inferInstance
          exact measure_univ
        rw [h_coin_univ, one_smul] at h_map_dir
        exact h_map_dir
      rw [h_snd]


/-- The candidate at height 1 is nonnegative. -/
theorem W1_nonneg (p : Params) (hL : 2 ≤ p.L) (hV : 2 ≤ p.V) (b : ℕ)
    (x : S1) : 0 ≤ W1 p b x := by
  rcases x with ⟨n, a, σ, _ | ⟨r, c, y, _ | _⟩⟩
  · -- case none
    unfold W1
    exact Wt_nonneg p hL hV b σ n a
  · -- case some (r, c, y, false)
    unfold W1
    refine Finset.sum_nonneg fun b' _ => ?_
    have hU0 := U0_nonneg_sum p.V p.L hL y
    have hU0b' : 0 ≤ U0 p.V p.L b' y := hU0.1 b'
    have hK1 : 0 ≤ K1 p b r c b' n a σ := by
      unfold K1
      have hκ := κ1_mem p r (f0of σ c) b'
      rcases hκ with ⟨hκl, hκu⟩
      have hWt1 : 0 ≤ Wt p b σ (min (n + b') p.P) a :=
        Wt_nonneg p hL hV b σ (min (n + b') p.P) a
      have hWt2 : 0 ≤ Wt p b (Function.update σ c 2) n a :=
        Wt_nonneg p hL hV b (Function.update σ c 2) n a
      nlinarith
    exact mul_nonneg hU0b' hK1
  · -- case some (r, c, y, true)
    unfold W1
    unfold K1
    have hκ := κ1_mem p r (f0of σ c) y.2.1
    rcases hκ with ⟨hκl, hκu⟩
    have hWt1 : 0 ≤ Wt p b σ (min (n + y.2.1) p.P) a :=
      Wt_nonneg p hL hV b σ (min (n + y.2.1) p.P) a
    have hWt2 : 0 ≤ Wt p b (Function.update σ c 2) n a :=
      Wt_nonneg p hL hV b (Function.update σ c 2) n a
    nlinarith


/-- The time bound at height 1 is nonnegative. -/
theorem T1_nonneg (p : Params) (hL : 2 ≤ p.L) (x : S1) :
    0 ≤ T1 p x := by
  match x with
  | (n, a, σ, none) =>
    unfold T1 Φ1
    positivity
  | (n, a, σ, some ic) =>
    match ic with
    | (r, c, y, false) =>
      unfold T1
      have hT0 : 0 ≤ (T0 p.L y : ℝ) := Nat.cast_nonneg _
      have hU0 (b' : ℕ) : 0 ≤ U0 p.V p.L b' y := (U0_nonneg_sum p.V p.L hL y).1 b'
      have hKT1 (b' : ℕ) : 0 ≤ KT1 p r c b' n σ := by
        unfold KT1
        have hκ1 := κ1_mem p r (f0of σ c) b'
        have hΦ1₁ : 0 ≤ Φ1 p σ (min (n + b') p.P) := by unfold Φ1; positivity
        have hΦ1₂ : 0 ≤ Φ1 p (Function.update σ c 2) n := by unfold Φ1; positivity
        have h1mκ1 : 0 ≤ 1 - κ1 p r (f0of σ c) b' := by linarith [hκ1.2]
        exact add_nonneg (mul_nonneg hκ1.1 hΦ1₁) (mul_nonneg h1mκ1 hΦ1₂)
      have hsum : 0 ≤ ∑ b' ∈ Finset.range (p.V + 1), U0 p.V p.L b' y * KT1 p r c b' n σ :=
        Finset.sum_nonneg (λ b' _ => mul_nonneg (hU0 b') (hKT1 b'))
      nlinarith
    | (r, c, y, true) =>
      unfold T1
      have hKT1 : 0 ≤ KT1 p r c y.2.1 n σ := by
        unfold KT1
        have hκ1 := κ1_mem p r (f0of σ c) y.2.1
        have hΦ1₁ : 0 ≤ Φ1 p σ (min (n + y.2.1) p.P) := by unfold Φ1; positivity
        have hΦ1₂ : 0 ≤ Φ1 p (Function.update σ c 2) n := by unfold Φ1; positivity
        have h1mκ1 : 0 ≤ 1 - κ1 p r (f0of σ c) y.2.1 := by linarith [hκ1.2]
        exact add_nonneg (mul_nonneg hκ1.1 hΦ1₁) (mul_nonneg h1mκ1 hΦ1₂)
      nlinarith


/-- The candidate at height 1 is a probability law on `{0, ..., V}` at every state with ups within the cap. -/
theorem W1_sum (p : Params) (hL : 2 ≤ p.L) (hV : 2 ≤ p.V)
    (x : S1) (ha : x.2.1 ≤ p.V) :
    ∑ b ∈ Finset.range (p.V + 1), W1 p b x = 1 := by
  rcases x with ⟨n, a, σ, h⟩
  rcases h with (none | ⟨r, c, y, fl⟩)
  · -- none case: W1 = Wt, use Wt_sum
    simp [W1]
    exact Wt_sum p hL hV σ n a ha
  · -- some (r, c, y, fl) case
    rcases fl with (false | true)
    · -- false case: W1 = ∑ b' U0 b' y * K1 b' ...
      simp [W1]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      have hinner : ∀ b', ∑ b ∈ Finset.range (p.V + 1), K1 p b r c b' n a σ = 1 := by
        intro b'
        simp [K1]
        have hsum1 : ∑ b ∈ Finset.range (p.V + 1), Wt p b σ (min (n + b') p.P) a = 1 :=
          Wt_sum p hL hV σ (min (n + b') p.P) a ha
        have hsum2 : ∑ b ∈ Finset.range (p.V + 1), Wt p b (Function.update σ c 2) n a = 1 :=
          Wt_sum p hL hV (Function.update σ c 2) n a ha
        calc
          ∑ b ∈ Finset.range (p.V + 1),
            (κ1 p r (f0of σ c) b' * Wt p b σ (min (n + b') p.P) a +
             (1 - κ1 p r (f0of σ c) b') * Wt p b (Function.update σ c 2) n a)
              = (κ1 p r (f0of σ c) b') *
                (∑ b ∈ Finset.range (p.V + 1), Wt p b σ (min (n + b') p.P) a) +
                (1 - κ1 p r (f0of σ c) b') *
                (∑ b ∈ Finset.range (p.V + 1), Wt p b (Function.update σ c 2) n a) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
          _ = (κ1 p r (f0of σ c) b') * 1 + (1 - κ1 p r (f0of σ c) b') * 1 := by
            simp [hsum1, hsum2]
          _ = 1 := by ring
      simp_rw [hinner, mul_one]
      have hU0sum := (U0_nonneg_sum p.V p.L hL y).2.2
      simp [hU0sum]
    · -- true case: W1 = K1
      simp [W1, K1]
      have hsum1 : ∑ b ∈ Finset.range (p.V + 1), Wt p b σ (min (n + y.2.1) p.P) a = 1 :=
        Wt_sum p hL hV σ (min (n + y.2.1) p.P) a ha
      have hsum2 : ∑ b ∈ Finset.range (p.V + 1), Wt p b (Function.update σ c 2) n a = 1 :=
        Wt_sum p hL hV (Function.update σ c 2) n a ha
      calc
        ∑ b ∈ Finset.range (p.V + 1),
          (κ1 p r (f0of σ c) y.2.1 * Wt p b σ (min (n + y.2.1) p.P) a +
           (1 - κ1 p r (f0of σ c) y.2.1) * Wt p b (Function.update σ c 2) n a)
            = (κ1 p r (f0of σ c) y.2.1) *
              (∑ b ∈ Finset.range (p.V + 1), Wt p b σ (min (n + y.2.1) p.P) a) +
              (1 - κ1 p r (f0of σ c) y.2.1) *
              (∑ b ∈ Finset.range (p.V + 1), Wt p b (Function.update σ c 2) n a) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
        _ = (κ1 p r (f0of σ c) y.2.1) * 1 + (1 - κ1 p r (f0of σ c) y.2.1) * 1 := by
          simp [hsum1, hsum2]
        _ = 1 := by ring


/-- The run at height 1 stays in `G1`. -/
theorem G1_closed (p : Params) (hL : 2 ≤ p.L) (x : S1)
    (hx : x ∈ G1 p) (ξ : Fin 4 × ℕ) : h1step p x ξ ∈ G1 p := by
  rcases x with ⟨n, a, σ, _ | ⟨r, c, y, _ | _⟩⟩
  · -- top round: x = (n, a, σ, none)
    rcases ξ with ⟨d, k⟩
    simp only [G1, Set.mem_ofPred_eq] at hx ⊢
    simp only [h1step]
    split_ifs with hn hz hσ0
    · -- n = 0: goal becomes a ≤ p.V ∧ n ≤ p.P
      rcases hx with ⟨haV, hnP, _⟩
      simp
      exact ⟨haV, hnP⟩
    · -- n ≠ 0, d = 0, a < p.V: goal becomes a < p.V ∧ n ≤ p.P + 1
      rcases hx with ⟨haV, hnP, _⟩
      simp
      exact ⟨by omega, by omega⟩
    · -- n ≠ 0, d = 0, ¬ a < p.V: goal becomes a ≤ p.V ∧ n ≤ p.P + 1
      rcases hx with ⟨haV, hnP, _⟩
      simp
      exact ⟨haV, by omega⟩
    · -- n ≠ 0, d ≠ 0, (σ (d.pred hz)).val = 0: goal becomes a ≤ p.V ∧ n ≤ p.P + 1
      rcases hx with ⟨haV, hnP, _⟩
      simp
      exact ⟨haV, by omega⟩
    · -- n ≠ 0, d ≠ 0, (σ (d.pred hz)).val ≠ 0: goal becomes a ≤ p.V ∧ n ≤ p.P + 1
      rcases hx with ⟨haV, hnP, _⟩
      simp
      exact ⟨haV, by omega⟩
  · -- inner read: x = (n, a, σ, some (r, c, y, false)), no if in h1step result
    rcases ξ with ⟨d, k⟩
    simp only [G1, Set.mem_ofPred_eq] at hx ⊢
    rcases hx with ⟨haV, hnP, hinner⟩
    have hinner_y := hinner r c y false (rfl : some (r, c, y, false) = some (r, c, y, false))
    rcases hinner_y with ⟨hy_depth, hy_ups, _⟩
    simp only [h1step]
    -- goal: a ≤ p.V ∧ n ≤ p.P ∧ (∀ r' c' y' fl, ...)
    refine ⟨haV, hnP, ?_⟩
    intro r' c' y' fl h
    -- h : some (r, c, hstep ..., decide (...)) = some (r', c', y', fl)
    -- injection on some gives equality of the inner tuples
    have h_inj := Option.some_inj.mp h
    -- h_inj : (r, c, hstep p.V p.L y d, decide (...)) = (r', c', y', fl)
    have hr_eq := congrArg (fun t => t.1) h_inj
    have hrest := congrArg (fun t => t.2.1) h_inj
    have hyz_eq := congrArg (fun t => t.2.2.1) h_inj
    have hfl_eq := congrArg (fun t => t.2.2.2) h_inj
    subst hr_eq; subst hrest; subst hyz_eq; subst hfl_eq
    -- Now we need: y'.2.2 < p.L ∧ y'.2.1 ≤ p.V ∧ (fl = true ↔ y'.1 = 0 ∧ y'.2.2 = 0)
    have h_depth := (T0_drift p.V p.L hL y hy_depth).2 d
    have h_ups := hstep_ups_le p.V p.L y hy_ups d
    simp
    exact ⟨h_depth, h_ups⟩
  · -- kill: x = (n, a, σ, some (r, c, y, true))
    rcases ξ with ⟨d, k⟩
    simp only [G1, Set.mem_ofPred_eq] at hx ⊢
    rcases hx with ⟨haV, hnP, hinner⟩
    have hinner_y := hinner r c y true (rfl : some (r, c, y, true) = some (r, c, y, true))
    rcases hinner_y with ⟨_, _, h_ended⟩
    have hy_ended : y.1 = 0 ∧ y.2.2 = 0 := by
      simpa using h_ended
    rcases hy_ended with ⟨hy1, hy2⟩
    simp [h1step]
    split_ifs with hkeep
    · -- keep case: output = (min (n + y.2.1) p.P, a, σ, none), goal: a ≤ p.V
      simp
      exact haV
    · -- don't keep case: output = (n, a, Function.update σ c 2, none), goal: a ≤ p.V ∧ n ≤ p.P
      simp
      exact ⟨haV, hnP⟩

theorem KT1_le (p : Params) (r : Bool) (c : Fin 3) (b n : ℕ) (σ : Fin 3 → Fin 3) (B : ℝ)
    (h1 : Φ1 p σ (min (n + b) p.P) ≤ B) (h2 : Φ1 p (Function.update σ c 2) n ≤ B) :
    KT1 p r c b n σ ≤ B := by
  unfold KT1
  have hk := κ1_mem p r (f0of σ c) b
  nlinarith [mul_le_mul_of_nonneg_left h1 hk.1, mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hk.2)]

theorem sum_U0_le (p : Params) (hL : 2 ≤ p.L) (y : ℕ × ℕ × ℕ) (k : ℕ)
    (hy : ∀ b, k ≤ b → U0 p.V p.L b y = 0) (F : ℕ → ℝ) (B : ℝ) (hF : ∀ b < k, F b ≤ B) :
    ∑ b ∈ Finset.range (p.V + 1), U0 p.V p.L b y * F b ≤ B := by
  have hnn := (U0_nonneg_sum p.V p.L hL y).1
  calc ∑ b ∈ Finset.range (p.V + 1), U0 p.V p.L b y * F b
      ≤ ∑ b ∈ Finset.range (p.V + 1), U0 p.V p.L b y * B := Finset.sum_le_sum fun b _ => by
        by_cases hb : b < k
        · exact mul_le_mul_of_nonneg_left (hF b hb) (hnn b)
        · rw [hy b (by omega), zero_mul, zero_mul]
    _ = B := by rw [← Finset.sum_mul, (U0_nonneg_sum p.V p.L hL y).2.2, one_mul]

theorem Φ1_le (p : Params) (σ σ' : Fin 3 → Fin 3) (n n' k : ℕ) (hn : n ≤ n' + k)
    (hr : rank1 σ + k ≤ rank1 σ') : Φ1 p σ n ≤ Φ1 p σ' n' - (4 * p.L + 3) * k := by
  unfold Φ1
  have hn' : (n : ℝ) ≤ n' + k := by exact_mod_cast hn
  have hr' : (rank1 σ : ℝ) + k ≤ rank1 σ' := by exact_mod_cast hr
  have hL : (0 : ℝ) ≤ p.L := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hn' (by positivity : (0 : ℝ) ≤ 4 * p.L + 3),
    mul_le_mul_of_nonneg_left hr' (by positivity : (0 : ℝ) ≤ 8 * p.L + 6)]

/-- The time bound after a top read into an unmarked child at height 1 drops by two. -/
theorem T1_child_unmarked (p : Params) (hL : 2 ≤ p.L) (m a : ℕ) (σ : Fin 3 → Fin 3) (c : Fin 3)
    (h0 : (σ c).val = 0) :
    T1 p (m, a, Function.update σ c 1, some (true, c, (2, 0, 0), false)) ≤ Φ1 p σ (m + 1) - 2 := by
  have hr1 := rank1_update_eq σ c 1
  have hr2 := rank1_update_eq σ c 2
  rw [h0] at hr1 hr2
  simp only [Fin.val_one, Fin.val_two, add_zero] at hr1 hr2
  have hr1' : (rank1 (Function.update σ c 1) : ℝ) + 1 = rank1 σ := by exact_mod_cast hr1
  have hr2' : (rank1 (Function.update σ c 2) : ℝ) + 2 = rank1 σ := by exact_mod_cast hr2
  have hB : ∀ b < 3, KT1 p true c b m (Function.update σ c 1) ≤
      Φ1 p σ (m + 1) - (4 * p.L + 3) := by
    intro b hb
    apply KT1_le
    · have := Φ1_le p (Function.update σ c 1) σ (min (m + b) p.P) (m + 1) 1 (by omega) (by omega)
      push_cast at this
      linarith
    · rw [Function.update_idem]
      have := Φ1_le p (Function.update σ c 2) σ m (m + 1) 1 (by omega) (by omega)
      push_cast at this
      linarith
  have hs := sum_U0_le p hL (2, 0, 0) 3 (fun b hb => rhoR_zero p b hb) _ _ hB
  simp only [T1, T0]
  push_cast
  linarith

/-- The time bound after a top read into a marked child at height 1 does not grow. -/
theorem T1_child_marked (p : Params) (hL : 2 ≤ p.L) (hV : 1 ≤ p.V) (m a : ℕ) (σ : Fin 3 → Fin 3)
    (c : Fin 3) :
    T1 p (m, a, σ, some (false, c, (1, 0, 0), false)) ≤ Φ1 p σ (m + 1) := by
  have hr2 := rank1_update_eq σ c 2
  simp only [Fin.val_two] at hr2
  have hY : Φ1 p (Function.update σ c 2) m ≤ Φ1 p σ m := by
    have := Φ1_le p (Function.update σ c 2) σ m m 0 (by omega) (by have := (σ c).isLt; omega)
    simpa using this
  have hm1 : Φ1 p σ (m + 1) = Φ1 p σ m + (4 * p.L + 3) := by unfold Φ1; push_cast; ring
  have hK0 : KT1 p false c 0 m σ ≤ Φ1 p σ m := by
    apply KT1_le _ _ _ _ _ _ _ _ hY
    have := Φ1_le p σ σ (min (m + 0) p.P) m 0 (by omega) (by omega)
    simpa using this
  have hK1 : KT1 p false c 1 m σ ≤ Φ1 p σ m + (4 * p.L + 3) := by
    apply KT1_le
    · rw [← hm1]
      have := Φ1_le p σ σ (min (m + 1) p.P) (m + 1) 0 (by omega) (by omega)
      simpa using this
    · have hL0 : (0 : ℝ) ≤ p.L := by positivity
      linarith
  obtain ⟨e0, e1, -⟩ := rhoH_vals p hV
  obtain ⟨-, -, -, -, hq0, hq1, -⟩ := pL_qL_facts p.L hL
  simp only [T1, T0]
  rw [sum_range_U0 p _ 2 (by omega) (fun b hb => rhoH_zero p b hb)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change (↑(2 * p.L * 1) : ℝ) + 1 + (ρH1 p 0 * KT1 p false c 0 m σ + ρH1 p 1 * KT1 p false c 1 m σ) ≤ _
  rw [e0, e1, hm1]
  push_cast
  have hL0 : (2 : ℝ) ≤ p.L := by exact_mod_cast hL
  nlinarith [mul_le_mul_of_nonneg_left hK0 (by linarith : (0 : ℝ) ≤ 1 - qL p.L),
    mul_le_mul_of_nonneg_left hK1 hq0.le,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 3 - qL p.L) (by linarith : (0 : ℝ) ≤ 4 * p.L + 3)]

theorem T1_child (p : Params) (hL : 2 ≤ p.L) (hV : 1 ≤ p.V) (m a : ℕ) (σ : Fin 3 → Fin 3)
    (c : Fin 3) (j : ℕ) : T1 p (h1step p (m + 1, a, σ, none) (c.succ, j)) ≤ Φ1 p σ (m + 1) := by
  have hsucc : (c.succ : Fin 4) ≠ 0 := Fin.succ_ne_zero c
  simp only [h1step, Nat.add_one_ne_zero, ↓reduceIte, hsucc, ↓reduceDIte, Fin.pred_succ,
    Nat.add_sub_cancel]
  split_ifs with h0
  · linarith [T1_child_unmarked p hL m a σ c h0]
  · exact T1_child_marked p hL hV m a σ c

/-- **Drift of the time bound at a top read at height 1.** -/
theorem T1_round (p : Params) (hL : 2 ≤ p.L) (hV : 1 ≤ p.V) (m a : ℕ) (σ : Fin 3 → Fin 3) (j : ℕ) :
    1 + ∑ d : Fin 4, 1 / 4 * T1 p (h1step p (m + 1, a, σ, none) (d, j)) ≤ T1 p (m + 1, a, σ, none) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_three]
  have h0 : T1 p (h1step p (m + 1, a, σ, none) (0, j)) = Φ1 p σ m := by
    simp [h1step, T1]
  have hm1 : Φ1 p σ (m + 1) = Φ1 p σ m + (4 * p.L + 3) := by unfold Φ1; push_cast; ring
  have := T1_child p hL hV m a σ 0 j
  have := T1_child p hL hV m a σ 1 j
  have := T1_child p hL hV m a σ 2 j
  have hL0 : (2 : ℝ) ≤ p.L := by exact_mod_cast hL
  rw [h0]
  change _ ≤ Φ1 p σ (m + 1)
  linarith

/-- **Drift of the time bound at an inner read at height 1.** -/
theorem T1_inner (p : Params) (hL : 2 ≤ p.L) (n a : ℕ) (σ : Fin 3 → Fin 3) (r : Bool) (c : Fin 3)
    (y : ℕ × ℕ × ℕ) (hd : y.2.2 < p.L) (hu : y.2.1 ≤ p.V) (hne : ¬(y.1 = 0 ∧ y.2.2 = 0)) (j : ℕ) :
    1 + ∑ d : Fin 4, 1 / 4 * T1 p (h1step p (n, a, σ, some (r, c, y, false)) (d, j)) ≤
      T1 p (n, a, σ, some (r, c, y, false)) := by
  set S : ℕ × ℕ × ℕ → ℝ := fun z =>
    ∑ b' ∈ Finset.range (p.V + 1), U0 p.V p.L b' z * KT1 p r c b' n σ with hSdef
  have hnext : ∀ d : Fin 4, T1 p (h1step p (n, a, σ, some (r, c, y, false)) (d, j)) =
      (T0 p.L (hstep p.V p.L y d) : ℝ) + 1 + S (hstep p.V p.L y d) := by
    intro d
    simp only [h1step]
    by_cases he : (hstep p.V p.L y d).1 = 0 ∧ (hstep p.V p.L y d).2.2 = 0
    · rw [decide_eq_true he]
      simp only [T1, hSdef]
      have hu' := hstep_ups_le p.V p.L y hu d
      rcases hy : hstep p.V p.L y d with ⟨y1, y2, y3⟩
      rw [hy] at he hu'
      simp only at he hu'
      obtain ⟨rfl, rfl⟩ := he
      rw [sum_U0_ended p hL y2 hu']
      simp [T0]
    · rw [decide_eq_false he]
      rfl
  rw [Finset.sum_congr rfl fun d _ => by rw [hnext d]]
  have hT := (T0_drift p.V p.L hL y hd).1
  rw [ite_eq_right hne] at hT
  have hT' : (4 : ℝ) + ∑ d : Fin 4, (T0 p.L (hstep p.V p.L y d) : ℝ) ≤ 4 * T0 p.L y := by
    exact_mod_cast hT
  have hS : ∑ d : Fin 4, 1 / 4 * S (hstep p.V p.L y d) = S y := by
    simp only [hSdef, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [U0_step p.V p.L b' hL y hd hu hne, Fin.sum_univ_four, hstep_dir p.V p.L y 2 (by decide),
      hstep_dir p.V p.L y 3 (by decide)]
    ring
  have hsplit : ∑ d : Fin 4, 1 / 4 * ((T0 p.L (hstep p.V p.L y d) : ℝ) + 1 + S (hstep p.V p.L y d)) =
      1 / 4 * ∑ d : Fin 4, (T0 p.L (hstep p.V p.L y d) : ℝ) + 1 +
        ∑ d : Fin 4, 1 / 4 * S (hstep p.V p.L y d) := by
    simp only [Fin.sum_univ_four]
    ring
  rw [hsplit, hS]
  change _ ≤ (T0 p.L y : ℝ) + 1 + S y
  linarith

instance : IsProbabilityMeasure (dirLaw.prod coinLaw) := inferInstance

/-- An integral of a function of the direction only. -/
theorem lintegral_ofReal_dir (F : Fin 4 → ℝ) (hF : ∀ d, 0 ≤ F d) (G : Fin 4 × ℕ → ℝ≥0∞)
    (hG : ∀ d j, G (d, j) = ENNReal.ofReal (F d)) :
    ∫⁻ ξ, G ξ ∂(dirLaw.prod coinLaw) = ENNReal.ofReal (∑ d, 1 / 4 * F d) := by
  rw [lintegral_dc]
  simp only [hG, lintegral_const, measure_univ, mul_one]
  rw [ENNReal.ofReal_sum_of_nonneg fun d _ => by have := hF d; positivity]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.div_eq_inv_mul]
  congr 1
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- An integral of a two-valued function of the coin only. -/
theorem lintegral_ofReal_coin (g : ℕ → Bool) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (G : Fin 4 × ℕ → ℝ≥0∞) (hG : ∀ d j, G (d, j) = ENNReal.ofReal (if g j = true then A else B)) :
    ∫⁻ ξ, G ξ ∂(dirLaw.prod coinLaw) = ENNReal.ofReal ((coinLaw {j | g j = true}).toReal * A +
      (1 - (coinLaw {j | g j = true}).toReal) * B) := by
  have hc : ∀ d, ∫⁻ j, G (d, j) ∂coinLaw = ENNReal.ofReal ((coinLaw {j | g j = true}).toReal * A +
      (1 - (coinLaw {j | g j = true}).toReal) * B) := by
    intro d
    have hG' : (fun j => G (d, j)) = fun j => if g j = true then ENNReal.ofReal A else ENNReal.ofReal B := by
      funext j; rw [hG]; split_ifs <;> rfl
    rw [hG', lintegral_coin_bool]
    have hS : coinLaw {j | g j = true} ≤ 1 := prob_le_one
    have hSt : (coinLaw {j | g j = true}).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hS)
    rw [ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hA) (mul_nonneg (by linarith) hB),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_one]
  rw [lintegral_dc]
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]

/-- **A kill read at height 1** keeps the candidate on average. -/
theorem W1_kill (p : Params) (b : ℕ) (n a : ℕ) (σ : Fin 3 → Fin 3) (r : Bool) (c : Fin 3)
    (y : ℕ × ℕ × ℕ) (hL : 2 ≤ p.L) (hV : 2 ≤ p.V) :
    ∫⁻ ξ, ENNReal.ofReal (W1 p b (h1step p (n, a, σ, some (r, c, y, true)) ξ)) ∂(dirLaw.prod coinLaw) =
      ENNReal.ofReal (W1 p b (n, a, σ, some (r, c, y, true))) := by
  rw [lintegral_ofReal_coin (fun j => p.keep r 0 (f0of σ c) y.2.1 (f0of σ c) j)
    (Wt p b σ (min (n + y.2.1) p.P) a) (Wt p b (Function.update σ c 2) n a)
    (Wt_nonneg p hL hV _ _ _ _) (Wt_nonneg p hL hV _ _ _ _)]
  · rfl
  · intro d j
    simp only [h1step]
    split_ifs <;> rfl

theorem T1_kill (p : Params) (hL : 2 ≤ p.L) (n a : ℕ) (σ : Fin 3 → Fin 3) (r : Bool) (c : Fin 3)
    (y : ℕ × ℕ × ℕ) :
    1 + ∫⁻ ξ, ENNReal.ofReal (T1 p (h1step p (n, a, σ, some (r, c, y, true)) ξ)) ∂(dirLaw.prod coinLaw) =
      ENNReal.ofReal (T1 p (n, a, σ, some (r, c, y, true))) := by
  rw [lintegral_ofReal_coin (fun j => p.keep r 0 (f0of σ c) y.2.1 (f0of σ c) j)
    (Φ1 p σ (min (n + y.2.1) p.P)) (Φ1 p (Function.update σ c 2) n)
    (T1_nonneg p hL (min (n + y.2.1) p.P, a, σ, none)) (T1_nonneg p hL (n, a, Function.update σ c 2, none))]
  · have hk := κ1_mem p r (f0of σ c) y.2.1
    have h1 := T1_nonneg p hL (min (n + y.2.1) p.P, a, σ, none)
    have h2 := T1_nonneg p hL (n, a, Function.update σ c 2, none)
    simp only [T1] at h1 h2
    have hK : 0 ≤ KT1 p r c y.2.1 n σ := by unfold KT1; nlinarith [hk.1, hk.2]
    change 1 + ENNReal.ofReal (KT1 p r c y.2.1 n σ) = ENNReal.ofReal (1 + KT1 p r c y.2.1 n σ)
    rw [ENNReal.ofReal_add zero_le_one hK, ENNReal.ofReal_one]
  · intro d j
    simp only [h1step]
    split_ifs <;> rfl

theorem h1step_ended (p : Params) (x : S1) (hx : x ∈ E1) (ξ : Fin 4 × ℕ) : h1step p x ξ = x := by
  obtain ⟨n, a, σ, i⟩ := x
  obtain ⟨h1, h2⟩ := hx
  simp only at h1 h2
  subst h1 h2
  simp [h1step]

/-- **The law at height 1, on the stream of directions and coins**, an instance of `chain_law`. From
a reachable state that is not an end, the chain ends with `b` top ups with probability `W1 p b`. -/
theorem law_height1 (p : Params) (hL : 2 ≤ p.L) (hV : 2 ≤ p.V) (x : S1) (hx : x ∈ G1 p)
    (hxE : x ∉ E1) (b : ℕ) (hb : b ≤ p.V) :
    Engine.iidMeasure (dirLaw.prod coinLaw)
        {w | ∃ t, Engine.traj (h1step p) x w t ∈ E1 ∧ (Engine.traj (h1step p) x w t).2.1 = b} =
      ENNReal.ofReal (W1 p b x) := by
  refine chain_law (h1step p) (dirLaw.prod coinLaw) (fun _ _ => (Set.to_countable _).measurableSet)
    E1 (h1step_ended p) (fun z => z.2.1) (Finset.range (p.V + 1)) (G1 p) (G1_closed p hL)
    (fun z hz _ => Finset.mem_range.2 (Nat.lt_succ_of_le hz.1))
    (fun b z => ENNReal.ofReal (W1 p b z)) ?_ ?_ ?_ (fun z => ENNReal.ofReal (T1 p z)) ?_
    (fun _ _ => ENNReal.ofReal_ne_top) x hx hxE b (Finset.mem_range.2 (Nat.lt_succ_of_le hb))
  · rintro c ⟨n, a, σ, i⟩ - ⟨h1, h2⟩
    simp only at h1 h2
    subst h1 h2
    simp only [W1, Wt, W1top_zero]
    split_ifs <;> simp
  · rintro c ⟨n, a, σ, _ | ⟨r, d, y, _ | _⟩⟩ ⟨ha, hn, hi⟩ hzE
    · rcases n with _ | m
      · exact absurd ⟨rfl, rfl⟩ hzE
      rw [lintegral_ofReal_dir (fun e => W1 p c (h1step p (m + 1, a, σ, none) (e, 0)))
        (fun e => W1_nonneg p hL hV c _)]
      · rw [W1_round p hL hV c m a σ hn 0]
      · intro e j
        simp only [h1step]
    · obtain ⟨hd, hu, hf⟩ := hi r d y false rfl
      rw [lintegral_ofReal_dir (fun e => W1 p c (h1step p (n, a, σ, some (r, d, y, false)) (e, 0)))
        (fun e => W1_nonneg p hL hV c _)]
      · rw [W1_inner p hL c n a σ r d y hd hu (by simpa using hf) 0]
      · intro e j
        rfl
    · exact (W1_kill p c n a σ r d y hL hV).le
  · rintro z hz
    rw [← ENNReal.ofReal_sum_of_nonneg fun c _ => W1_nonneg p hL hV c z, W1_sum p hL hV z hz.1,
      ENNReal.ofReal_one]
  · rintro ⟨n, a, σ, _ | ⟨r, d, y, _ | _⟩⟩ ⟨ha, hn, hi⟩
    · rcases n with _ | m
      · have hE : ((0, a, σ, none) : S1) ∈ E1 := ⟨rfl, rfl⟩
        rw [Set.indicator_of_mem hE, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hE)]
        simp only [Pi.zero_apply, zero_add, h1step_ended p _ hE, lintegral_const, measure_univ, mul_one,
          le_refl]
      · have hE : ((m + 1, a, σ, none) : S1) ∉ E1 := fun h => by simp [E1] at h
        rw [Set.indicator_of_notMem hE, Set.indicator_of_mem (Set.mem_compl hE),
          Pi.one_apply, zero_add, lintegral_ofReal_dir (fun e => T1 p (h1step p (m + 1, a, σ, none) (e, 0)))
          (fun e => T1_nonneg p hL _), ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
          (Finset.sum_nonneg fun e _ => by have := T1_nonneg p hL (h1step p (m + 1, a, σ, none) (e, 0)); positivity)]
        · exact ENNReal.ofReal_le_ofReal (T1_round p hL (by omega) m a σ 0)
        · intro e j
          simp only [h1step]
    · obtain ⟨hd, hu, hf⟩ := hi r d y false rfl
      have hE : ((n, a, σ, some (r, d, y, false)) : S1) ∉ E1 := fun h => by simp [E1] at h
      rw [Set.indicator_of_notMem hE, Set.indicator_of_mem (Set.mem_compl hE),
        Pi.one_apply, zero_add, lintegral_ofReal_dir
        (fun e => T1 p (h1step p (n, a, σ, some (r, d, y, false)) (e, 0))) (fun e => T1_nonneg p hL _),
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
        (Finset.sum_nonneg fun e _ => by
          have := T1_nonneg p hL (h1step p (n, a, σ, some (r, d, y, false)) (e, 0)); positivity)]
      · exact ENNReal.ofReal_le_ofReal (T1_inner p hL n a σ r d y hd hu (by simpa using hf) 0)
      · intro e j
        rfl
    · have hE : ((n, a, σ, some (r, d, y, true)) : S1) ∉ E1 := fun h => by simp [E1] at h
      rw [Set.indicator_of_notMem hE, Set.indicator_of_mem (Set.mem_compl hE),
        Pi.one_apply, zero_add]
      exact (T1_kill p hL n a σ r d y).le

end FrogModel.D3
