module

public import FrogModel.Engine.DomChain
public import FrogModel.Engine.CandSim
public import FrogModel.Engine.Law
public import FrogModel.Cert.Cheap

@[expose] public section

/-!
# The dominating output of `cand` splits (proof of Theorem 6.5 of the paper)

The dominating chain of `cand` (`candDom T' keep`) is `domStep` with the child chain of `cand`,
its stop thresholds `T` (exits, from the table) and `T'` (pending frogs), the states `keep` that
the data keep, and the lump of `CandSim`. Its output law from the start is `odomC T' keep`.

`DomCert T' keep A Sov` is what the checker of the certificate delivers (Section 8.2 of the
paper): the atoms `A` lie in `F_T`; a family of sub-solutions `V o` of the systems of absorption unflagged with the
outputs `o`, supported on the live unflagged states with at most `T` exits and bounded, with
`L {o} ≤ V o (start)`; and a super-solution `W` of the system whose reward is `Phi` at the step
that sets the flag, with `W (start) ≤ Sov`.

**`domSplit_of_domCert`**: with Lemma 6.1 of the paper (`ChildPsiLaw`), Lemma 6.3 (`Lemma61`)
and the simulation of the labels by their max labels, `DomCert` gives
`DomSplit (odomC T' keep) (latMeasure A) (odomC T' keep - latMeasure A) Sov`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine

open FrogModel.Cert FrogModel.LemmaX

/-- The law of one input of the root chain of `cand`: a uniform direction and a uniform. -/
noncomputable abbrev nuC : Measure (Fin 5 × ℝ) := (unifDir 4).prod lam

/-- The dominating chain of `cand`, with pending bound `T'` and the states `keep` of the data. -/
noncomputable abbrev candDom (T' : ℕ) (keep : RState CState 4 4 → Bool) :
    RState CState 4 4 × Bool → Fin 5 × ℝ → RState CState 4 4 × Bool :=
  domStep cand.childStep cand.T T' keep (lumpState cand)

/-- The output law of the dominating chain of `cand` from the start. -/
noncomputable def odomC (T' : ℕ) (keep : RState CState 4 4 → Bool) : Measure (Fin 4 → ℕ∞) :=
  (iidMeasure nuC).map (domOut (candDom T' keep) (start .fresh, false))

/-- `Phi` of Lemma 6.3 of the paper, in `ℝ≥0∞`. -/
noncomputable def phiC (x : RState CState 4 4) : ℝ≥0∞ := ENNReal.ofReal (cand.PhiQ x)

/-- **What the checker delivers** (Section 8.2 of the paper). -/
def DomCert (T' : ℕ) (keep : RState CState 4 4 → Bool) (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ))
    (Sov : ℝ≥0∞) : Prop :=
  (∀ a ∈ A, a.1.2.2.2 ≤ cand.T) ∧
  (∃ (V : (Fin 4 → ℕ) → RState CState 4 4 × Bool → ℝ≥0∞) (C : ℝ≥0∞), C ≠ ⊤ ∧
    (∀ o, V o ≤ (fun y => nuC (absUnflagged (candDom T' keep) o y)) +
      FrogModel.LinSys.app (fkKernel (candDom T' keep) (fun _ _ => 1) nuC) (V o)) ∧
    (∀ o y, V o y ≠ 0 → y.2 = false ∧ y.1.i < 4 ∧ y.1.e ≤ cand.T) ∧ (∀ o y, V o y ≤ C) ∧
    ∀ o : Fin 4 → ℕ, latMeasure A {fun k => (o k : ℕ∞)} ≤ V o (start .fresh, false)) ∧
  ∃ W : RState CState 4 4 × Bool → ℝ≥0∞,
    fkRhs (flagReward (candDom T' keep) phiC) nuC +
      FrogModel.LinSys.app (fkKernel (candDom T' keep) (fun _ _ => 1) nuC) W ≤ W ∧
    W (start .fresh, false) ≤ Sov

/-! ### Facts on the start, the inputs and `theta` -/

theorem valid_start {S : Type*} {d J : ℕ} (F : S) : Valid (start F : RState S d J) :=
  ⟨fun _ => le_rfl, fun _ _ => rfl⟩

theorem nuC_exit_ne_zero : nuC {ξ : Fin 5 × ℝ | ξ.1 = 0} ≠ 0 := by
  have : {ξ : Fin 5 × ℝ | ξ.1 = 0} = ({0} : Set (Fin 5)) ×ˢ Set.univ := by ext; simp
  rw [this, Measure.prod_prod, measure_univ, mul_one, ProbabilityTheory.uniformOn_univ]
  simp

theorem one_le_thetaC : 1 ≤ thetaC := by
  have h := cand_I2.2.2.2.1
  unfold thetaC
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h.le)

theorem le_epow_thetaC (t : ℕ) (v : ℕ∞) (hv : (t : ℕ∞) ≤ v) : thetaC ^ t ≤ epow thetaC v := by
  unfold epow
  split_ifs with h
  · exact le_top
  · lift v to ℕ using h
    simp only [ENat.toNat_natCast]
    exact pow_le_pow_right₀ one_le_thetaC (by exact_mod_cast hv)

/-! ### The atoms -/

theorem toBlock4_eq (x : ℕ × ℕ × ℕ × ℕ) :
    toBlock4 x = fun k => ((![x.1, x.2.1, x.2.2.1, x.2.2.2] k : ℕ) : ℕ∞) := by
  funext k
  fin_cases k <;> rfl

theorem latMeasure_singleton_ne_zero (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (B : Fin 4 → ℕ∞)
    (h : latMeasure A {B} ≠ 0) : ∃ a ∈ A, B = toBlock4 a.1 := by
  induction A with
  | nil => simp [latMeasure] at h
  | cons a A ih =>
    unfold latMeasure at h
    rw [List.map_cons, List.sum_cons, Measure.add_apply] at h
    by_cases hB : B = toBlock4 a.1
    · exact ⟨a, List.mem_cons_self .., hB⟩
    · have h1 : (((a.2 : ℝ≥0∞) / 2 ^ 40) • Measure.dirac (toBlock4 a.1)) {B} = 0 := by
        rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton B)]
        simp [Set.indicator, Ne.symm hB]
      rw [h1, zero_add] at h
      obtain ⟨a', ha', hB'⟩ := ih h
      exact ⟨a', List.mem_cons_of_mem _ ha', hB'⟩

theorem latMeasure_supp (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (T : ℕ)
    (hA : ∀ a ∈ A, a.1.2.2.2 ≤ T) : latMeasure A {B | ((T : ℕ) : ℕ∞) < B 3} = 0 := by
  induction A with
  | nil => simp [latMeasure]
  | cons a A ih =>
    unfold latMeasure at ih ⊢
    rw [List.map_cons, List.sum_cons, Measure.add_apply,
      ih fun a' ha' => hA a' (List.mem_cons_of_mem _ ha'), add_zero, Measure.smul_apply,
      Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
    have : toBlock4 a.1 ∉ {B : Fin 4 → ℕ∞ | ((T : ℕ) : ℕ∞) < B 3} := by
      simp only [Set.mem_ofPred_eq, not_lt]
      have h3 : toBlock4 a.1 3 = ((a.1.2.2.2 : ℕ) : ℕ∞) := rfl
      rw [h3]
      exact_mod_cast hA a (List.mem_cons_self ..)
    simp [Set.indicator_of_notMem this]

/-! ### Along the dominating chain -/

/-- The invariant of the states reached from the start: valid, well-formed children, outputs
monotone, recorded below the exit count, `⊤` from `i` on. -/
def CandInv (y : RState CState 4 4 × Bool) : Prop :=
  Valid y.1 ∧ (∀ c, cand.ChildWF (y.1.σ c)) ∧ Monotone y.1.out ∧
    (∀ k : Fin 4, (k : ℕ) < y.1.i → y.1.out k ≤ y.1.e) ∧ ∀ k : Fin 4, y.1.i ≤ k → y.1.out k = ⊤

theorem candInv_start : CandInv (start .fresh, false) := by
  unfold CandInv
  refine ⟨valid_start _, fun _ => trivial, fun _ _ _ => le_rfl, fun k hk => ?_, fun _ _ => rfl⟩
  exact absurd hk (Nat.not_lt_zero _)

theorem childWF_rstep (x : RState CState 4 4) (hx : ∀ c, cand.ChildWF (x.σ c))
    (ξ : Fin 5 × ℝ) : ∀ c, cand.ChildWF ((rstep cand.childStep x ξ).σ c) := by
  have hm : ∀ c, cand.ChildWF ((move cand.childStep x ξ.1 ξ.2).2.2 c) := by
    intro c
    unfold move
    split_ifs with ha
    · exact hx c
    · by_cases hc : c = ξ.1.pred ha
      · subst hc
        simp only [Function.update_self]
        exact cand.childWF_step cand_I0 cand_I1 _ (hx _) _
      · simp only [Function.update_of_ne hc]
        exact hx c
  intro c
  unfold rstep
  split_ifs
  · exact hm c
  · exact hm c
  · exact hx c

theorem childWF_lumpC (s : CState) (hs : cand.ChildWF s) : cand.ChildWF (lumpC cand s) := by
  cases s with
  | lab q t =>
    by_cases h : cand.ChildWF (.lab q t)
    · rw [show lumpC cand (.lab q t) = .maxLab q by simp [lumpC, h]]
      exact ⟨h.1, h.2.1⟩
    · rw [show lumpC cand (.lab q t) = .lab q t by simp [lumpC, h]]
      exact hs
  | _ => exact hs

theorem candInv_step (T' : ℕ) (keep : RState CState 4 4 → Bool) (y : RState CState 4 4 × Bool)
    (ξ : Fin 5 × ℝ) (hy : CandInv y) : CandInv (candDom T' keep y ξ) := by
  unfold CandInv at hy ⊢
  obtain ⟨hv, hwf, hm, hle, htop⟩ := hy
  have hr := rstep_outInv cand.childStep y.1 ξ ⟨hm, hle, htop⟩
  have hrv := rstep_valid cand.childStep y.1 hv ξ
  have hrwf := childWF_rstep y.1 hwf ξ
  unfold candDom domStep
  split_ifs
  · exact ⟨hrv, hrwf, hr⟩
  · exact ⟨hrv, hrwf, hr⟩
  · exact ⟨hrv, hrwf, hr⟩
  · exact ⟨hrv, fun c => childWF_lumpC _ (hrwf c), hr⟩

/-- At the step that sets the flag, the chain takes the root step from a live state. -/
theorem candDom_of_flag (T' : ℕ) (keep : RState CState 4 4 → Bool)
    (y : RState CState 4 4 × Bool) (ξ : Fin 5 × ℝ) (hξ : ξ ∈ flagSet (candDom T' keep) y) :
    (candDom T' keep y ξ).1 = rstep cand.childStep y.1 ξ ∧ y.1.i < 4 := by
  obtain ⟨h2, h2'⟩ := hξ
  unfold candDom domStep at h2' ⊢
  split_ifs at h2' ⊢ with h1 h3 h4
  all_goals first
    | exact ⟨rfl, by push Not at h1; exact h1.2.2⟩
    | simp_all

/-- The output recorded at the absorption is the exit count. -/
theorem rstep_out_last (x : RState CState 4 4) (ξ : Fin 5 × ℝ) (hx : x.i < 4)
    (habs : 4 ≤ (rstep cand.childStep x ξ).i) :
    (rstep cand.childStep x ξ).out 3 = ((rstep cand.childStep x ξ).e : ℕ∞) := by
  unfold rstep at habs ⊢
  simp only [hx, ↓reduceDIte] at habs ⊢
  split_ifs at habs ⊢ with h0
  · have hi : x.i = 3 := by simp at habs; omega
    have : (⟨x.i, hx⟩ : Fin 4) = 3 := Fin.ext (by simp [hi])
    simp only [this, Function.update_self]
  · simp at habs; omega

/-! ### The split -/

theorem domSplit_of_domCert (T' : ℕ) (keep : RState CState 4 4 → Bool)
    (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (Sov : ℝ≥0∞) (h7 : ChildPsiLaw) (h61 : Lemma61)
    (hsim : IsSim cand.childStep (simRel cand)) (h : DomCert T' keep A Sov) :
    DomSplit (odomC T' keep) (latMeasure A) (odomC T' keep - latMeasure A) Sov := by
  obtain ⟨hAT, ⟨V, C, hC, hV, hVsupp, hVbd, hAV⟩, ⟨W, hW, hWS⟩⟩ := h
  have hc : ∀ s r, MeasurableSet {u : ℝ | cand.childStep s u = r} :=
    fun s r => cand.measurableSet_childStep_eq s r
  set g := candDom T' keep with hg
  have hgm : ∀ y y', MeasurableSet {ξ | g y ξ = y'} :=
    measurableSet_domStep_eq cand.childStep hc cand.T T' keep (lumpState cand)
  have hmeas : Measurable (domOut g (start .fresh, false)) :=
    measurable_recOut_traj g hgm _
  have hprob : IsProbabilityMeasure (odomC T' keep) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 (by unfold iidMeasure; infer_instance)
  have hlump := dom_lumpState (d := 4) (J := 4) cand
  -- (V): the atoms lie below the output law
  have hLle : latMeasure A ≤ odomC T' keep := by
    refine measure_le_of_singleton _ _ fun B => ?_
    by_cases hB : latMeasure A {B} = 0
    · rw [hB]; exact zero_le
    obtain ⟨a, -, rfl⟩ := latMeasure_singleton_ne_zero A B hB
    set o : Fin 4 → ℕ := ![a.1.1, a.1.2.1, a.1.2.2.1, a.1.2.2.2]
    rw [toBlock4_eq]
    refine (hAV o).trans ((le_absUnflagged_of_sub cand.childStep hc cand.T T' keep (lumpState cand)
      (simRel cand) hlump nuC nuC_exit_ne_zero o (V o) (hV o) (hVsupp o) C hC (hVbd o)
      (start .fresh, false)).trans ?_)
    unfold odomC
    rw [Measure.map_apply hmeas (measurableSet_singleton _)]
    refine measure_mono fun w hw => ?_
    obtain ⟨k, hk⟩ := hw
    exact domOut_eq_of_absUnflagged cand.childStep cand.T T' keep (lumpState cand) (simRel cand)
      hlump o _ (valid_start _) w k hk
  have hLfin : IsFiniteMeasure (latMeasure A) := isFiniteMeasure_of_le _ hLle
  -- (W): the flagged part
  have hInvT : ∀ y ξ, CandInv y → CandInv (g y ξ) := fun y ξ hy => candInv_step T' keep y ξ hy
  have hΦ : ∀ y ξ, CandInv y → ξ ∈ flagSet g y →
      ∫⁻ w, epow thetaC (recOut (traj (rstep cand.childStep) (g y ξ).1 w) 3) ∂(iidMeasure nuC) ≤
        phiC (g y ξ).1 := by
    intro y ξ hy hξ
    obtain ⟨heq, hlive⟩ := candDom_of_flag T' keep y ξ hξ
    rw [heq]
    refine h61 _ (rstep_valid cand.childStep y.1 hy.1 ξ) ?_ (childWF_rstep y.1 hy.2.1 ξ)
    by_cases hi : (rstep cand.childStep y.1 ξ).i < 4
    · exact Or.inl hi
    · push Not at hi
      have hle : (rstep cand.childStep y.1 ξ).i ≤ y.1.i + 1 := by
        unfold rstep; simp only [hlive, ↓reduceDIte]; split_ifs <;> simp
      exact Or.inr ⟨by omega, rstep_out_last y.1 ξ hlive hi⟩
  have hflag := lintegral_flagged_le_of_super cand.childStep hc cand.T T' keep (lumpState cand)
    (simRel cand) hlump nuC (epow thetaC) 3 phiC CandInv hInvT hΦ W hW (start .fresh, false)
    candInv_start (valid_start _) rfl
  refine ⟨?_, ?_, hprob, ?_, latMeasure_supp A cand.T hAT, ?_⟩
  · -- domination of the output law of the root chain
    have hlaw := law_outPsi_start (d := 4) (J := 4) cand.childStep hc lam CState.fresh
    have hphi : phiLaw 4 4 Hstar =
        (iidMeasure nuC).map (fun w => outPsi cand.childStep (start .fresh : RState CState 4 4) w) := by
      rw [hlaw, phiLaw, ← h7]
    rw [hphi]
    exact couplingLE_domOut cand.childStep hc cand.T T' keep (lumpState cand) (simRel cand) hsim
      (simRel_refl cand) hlump nuC nuC_exit_ne_zero _ (valid_start _)
  · rw [add_comm]; exact (Measure.sub_add_cancel_of_le hLle).symm
  · -- the outputs are monotone
    unfold odomC
    have hset : MeasurableSet {B : Fin 4 → ℕ∞ | Monotone B} := MeasurableSet.of_discrete
    rw [ae_map_iff hmeas.aemeasurable hset]
    refine Filter.Eventually.of_forall fun w => monotone_recOut _ fun n => ?_
    have : ∀ n, CandInv (traj g (start .fresh, false) w n) := by
      intro n
      induction n with
      | zero => exact candInv_start
      | succ n ih => exact hInvT _ _ ih
    exact (this n).2.2.1
  · -- the tail
    intro t ht
    have htail := map_domOut_tail_le cand.childStep hc cand.T T' keep (lumpState cand)
      (simRel cand) hlump nuC nuC_exit_ne_zero thetaC
      (ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_thetaC)) ENNReal.ofReal_ne_top 3
      (start .fresh, false) (valid_start _) rfl (Nat.zero_le _) (fun k hk => absurd hk (Nat.not_lt_zero _))
      t (by omega) (epow thetaC) (le_epow_thetaC t)
    calc (odomC T' keep - latMeasure A) {B | (t : ℕ∞) ≤ B 3}
        ≤ odomC T' keep {B | (t : ℕ∞) ≤ B 3} := Measure.sub_le _
      _ ≤ thetaC⁻¹ ^ t * W (start .fresh, false) := htail.trans (by gcongr)
      _ ≤ thetaC⁻¹ ^ t * Sov := by gcongr

end FrogModel.Engine
