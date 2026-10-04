module

public import FrogModel.D3.M1L.F3L

@[expose] public section

/-!
# Proposition 13.3: the assembly

The keep functions `kappa = rho*/Rhat` of a run `R` of the interface (`paramsR`), the stored laws
of M1_L for them (`laws_stored`), the top law (`top_stored`), the law of the frog paths
(`map_fp_paths`), and `f3L_holds`, the statement `Iface.f3L`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3

/-! ## The law of the frog paths -/

/-- The steps of the frog-path space have the law of the planted model. -/
theorem map_fpPaths : fpMeasure.map fpPaths = Iface.pathMeasure := by
  have hm : Measurable fun ω : Option Frog × ℕ → Val => fun q : Frog × ℕ => (ω (some q.1, q.2)).1 :=
    measurable_pi_iff.2 fun q => measurable_fst.comp (measurable_pi_apply _)
  have hf : fpPaths = (MeasurableEquiv.curry Frog ℕ (Step 3)) ∘
      (fun ω : Option Frog × ℕ → Val => fun q : Frog × ℕ => (ω (some q.1, q.2)).1) := by
    funext ω _ _
    rfl
  rw [hf, ← Measure.map_map (MeasurableEquiv.measurable _) hm, map_fp_paths,
    Measure.infinitePi_map_curry (fun (_ : Frog) (_ : ℕ) => stepLaw 3)]
  rfl

theorem measurable_fpPaths : Measurable fpPaths :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
    measurable_fst.comp (measurable_pi_apply _)

/-- The planted count `plantedG` of M1L/Planted.lean and that of the interface agree. -/
theorem plantedG_iface (m k : ℕ) (π : Frog → ℕ → Step 3) :
    Iface.plantedG m k π = plantedG m k π := by
  unfold Iface.plantedG plantedG
  congr 1
  ext φ
  simp only [Set.mem_ofPred_eq, woken_iff]
  rfl

/-! ## The keep functions of a run -/

/-- The law before the kill that the keep coins of height `h` divide by: `Rhat_0` and
`Khat_0(0 -> .)` at height `0`, where every child of a closure is marked, and `Rhat_h`,
`Khat_h(t -> .)` above. -/
noncomputable def preI (V P L : ℕ) (R : Iface.M1Run) (r : Bool) (h t a g : ℕ) : ℝ :=
  if h = 0 then (if r then Iface.Rhat0 V L a g else Iface.Khat0 L 0 a g)
  else if r then Iface.Rhat V P (R.rho (h - 1)) (R.K (h - 1)) a g
  else Iface.KhatH V P L (R.rho (h - 1)) t a g

/-- The stored law: `rho*_h` for an R closure, `K*_h(t -> .)` for an H closure. -/
noncomputable def tgtI (R : Iface.M1Run) (r : Bool) (h t a g : ℕ) : ℝ :=
  if r then R.rho h a g else R.K h t a g

/-- The keep probability: the stored law over the law before the kill; at height `0` it reads
neither the type nor the count of unmarked children. -/
noncomputable def κR (V P L : ℕ) (R : Iface.M1Run) (r : Bool) (h t a g : ℕ) : ℝ :=
  if h = 0 then ratio01 (tgtI R r 0 0 a 0) (preI V P L R r 0 0 a 0)
  else ratio01 (tgtI R r h t a g) (preI V P L R r h t a g)

open Classical in
/-- M1_L with the keep coins of a run. -/
noncomputable def paramsR (V P L m : ℕ) (R : Iface.M1Run) : Params :=
  ⟨m, V, P, L, fun r h t a g j => decide (j ∈ coinSet (κR V P L R r h t a g))⟩

theorem paramsR_keep0 (V P L m : ℕ) (R : Iface.M1Run) :
    ∀ r f a f' n, (paramsR V P L m R).keep r 0 f a f' n = (paramsR V P L m R).keep r 0 0 a 0 n := by
  intro r f a f' n
  rfl

theorem κR_mem (V P L : ℕ) (R : Iface.M1Run) (r : Bool) (h t a g : ℕ) :
    0 ≤ κR V P L R r h t a g ∧ κR V P L R r h t a g ≤ 1 := by
  unfold κR
  split_ifs
  · exact ratio01_mem _ _
  · exact ratio01_mem _ _

theorem κm_paramsR (V P L m : ℕ) (R : Iface.M1Run) (r : Bool) (h t a g : ℕ) :
    κm (paramsR V P L m R) r h t a g = κR V P L R r h t a g := by
  have hs : {j | (paramsR V P L m R).keep r h t a g j = true} = coinSet (κR V P L R r h t a g) := by
    ext j
    simp [paramsR]
  rw [κm, hs]
  exact coinLaw_coinSet _ (κR_mem V P L R r h t a g).1 (κR_mem V P L R r h t a g).2

/-! ## The stored laws -/

/-- The laws of M1_L at height `h` agree with the stored laws of the run on `{0..V} × {0..3}`;
at height `0` the H laws only for `t = 0`, the only type that a closure at height `1` reads. -/
def Stored (V P L m : ℕ) (R : Iface.M1Run) (h : ℕ) : Prop :=
  (∀ b ≤ V, ∀ f < 4, (laws (paramsR V P L m R) h).1 b f = R.rho h b f) ∧
    ∀ t ≤ 3, (h = 0 → t = 0) → ∀ a ≤ V, ∀ f < 4, (laws (paramsR V P L m R) h).2 t a f = R.K h t a f

/-- `rho*_0` has no mass at `f ≠ 0`. -/
theorem rho0_off (V P L m : ℕ) (R : Iface.M1Run) (hm : 1 ≤ m) (hR : Iface.F3Hyp V P L m R)
    (b f : ℕ) (hb : b ≤ V) (hf : f < 4) (hf0 : f ≠ 0) : R.rho 0 b f = 0 := by
  obtain ⟨hpR, -, h0R, -, -⟩ := hR
  have h1 := h0R b hb f (by omega) (Or.inr hf0)
  have h2 := (hpR 0 (by omega)).1 b f
  simp only [Iface.Rhat0, hf0, ↓reduceIte] at h1
  linarith

/-- The R recursion on the laws of M1_L at a stored height is the R recursion on the run. -/
theorem wrec_stored (V P L m : ℕ) (R : Iface.M1Run) (hV : 1 ≤ V) (hm : 1 ≤ m)
    (hR : Iface.F3Hyp V P L m R) (h : ℕ) (hS : Stored V P L m R h) (n x g : ℕ) :
    Iface.Wrec V P (laws (paramsR V P L m R) h).1 (laws (paramsR V P L m R) h).2 (fun _ => none)
        n x g = Iface.Wrec V P (R.rho h) (R.K h) (fun _ => none) n x g := by
  refine Wrec_congr V P hV _ _ _ _ (fun t => h = 0 → t = 0) hS.1 ?_ ?_ ?_ _ ?_ n x g
  · intro b hb f hf hne h0
    subst h0
    by_contra hf0
    exact hne ((hS.1 b hb f hf).trans (rho0_off V P L m R hm hR b f hb hf hf0))
  · intro t ht hRc a ha f hf
    exact hS.2 t (by omega) hRc a ha f hf
  · intro t _ hRc a _ f hf _ h0
    have := hRc h0
    omega
  · intro c t hc
    exact absurd hc (by simp)

/-- The R law before the kill at height `h` is `preI`. -/
theorem preR_eq (V P L m : ℕ) (R : Iface.M1Run) (hV : 1 ≤ V) (hL : 1 ≤ L) (hm : 1 ≤ m)
    (hR : Iface.F3Hyp V P L m R) (h : ℕ) (hS : h ≠ 0 → Stored V P L m R (h - 1)) (a g : ℕ)
    (ha : a ≤ V) :
    GenH (paramsR V P L m R) h true (inp (paramsR V P L m R) h) (fun _ => 0) (ind a g) (initK h) 2 0 =
      preI V P L R true h 3 a g := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have hk : initK 0 = fun _ => some 0 := by funext c; simp [initK]
    have hn : nN (fun _ : Fin 3 => (some 0 : Option (Fin 4))) = 0 := by simp [nN]
    show Gen V P false (pL L) _ _ (fun _ => 0) (ind a g) (initK 0) 2 0 = _
    rw [Gen_Yrec V P L hV _ _ g _ 2 a ha, hk, hn, Yrec_zero_two V P L hV hL]
    simp [preI]
  · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    have hk : initK (h' + 1) = fun _ => none := by funext c; simp [initK]
    show Gen V P (isRe (h' + 1) true) (pL L) (laws (paramsR V P L m R) h').1
      (laws (paramsR V P L m R) h').2 (fun _ => 0) (ind a g) (initK (h' + 1)) 2 0 = _
    rw [show isRe (h' + 1) true = true by simp [isRe], hk, Gen_Wrec V P hV _ _ _ g _ 2 a ha,
      wrec_stored V P L m R hV hm hR h' (hS (by omega)) 2 a g]
    simp [preI, Iface.Rhat]

/-- The H law of type `t` before the kill at height `h` is `preI`. -/
theorem preK_eq (V P L m : ℕ) (R : Iface.M1Run) (hV : 1 ≤ V) (hL : 1 ≤ L)
    (h : ℕ) (hS : h ≠ 0 → Stored V P L m R (h - 1)) (t : ℕ) (ht : t ≤ 3) (a g : ℕ) (ha : a ≤ V) :
    GenH (paramsR V P L m R) h false (inp (paramsR V P L m R) h) (fun _ => 0) (ind a g)
        (kidOf h t) 1 0 = preI V P L R false h t a g := by
  show Gen V P false (pL L) _ _ (fun _ => 0) (ind a g) (kidOf h t) 1 0 = _
  rw [Gen_Yrec V P L hV _ _ g _ 1 a ha, nN_kidOf h t ht]
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp only [↓reduceIte]
    rw [Yrec_zero_one V P L hV hL]
    simp [preI]
  · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    simp only [show h' + 1 ≠ 0 by omega, ↓reduceIte]
    simp only [preI, show h' + 1 ≠ 0 by omega, Bool.false_eq_true, ↓reduceIte,
      Nat.add_sub_cancel, Iface.KhatH]
    refine Yrec_congr V P L _ _ (fun b hb => Finset.sum_congr rfl fun f hf => ?_) t 1 a g
    exact (hS (by omega)).1 b hb f (Finset.mem_range.1 hf)

/-- Off the bottom, the law before the kill times the keep probability is the stored law. -/
theorem pre_mul_κ (V P L m : ℕ) (R : Iface.M1Run) (hR : Iface.F3Hyp V P L m R) (r : Bool)
    (h t : ℕ) (hh : h < m) (ht : t ≤ 3) (ht0 : h = 0 → r = false → t = 0) (b f : ℕ) (hb : b ≤ V)
    (hf : f ≤ (if r then 3 else t)) (hbf : b ≠ 0 ∨ f ≠ 0) :
    preI V P L R r h t b f * κR V P L R r h t b f = tgtI R r h t b f := by
  obtain ⟨hpR, hpK, h0R, h0K, hH⟩ := hR
  have hnn : 0 ≤ tgtI R r h t b f := by
    cases r
    · exact (hpK h hh t ht).1 b f
    · exact (hpR h hh).1 b f
  have hle : tgtI R r h t b f ≤ preI V P L R r h t b f := by
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · cases r
      · have := ht0 rfl rfl
        subst this
        simpa [tgtI, preI] using h0K 0 (by omega) b hb f hf hbf
      · simpa [tgtI, preI] using h0R b hb f hf hbf
    · cases r
      · simpa [tgtI, preI, show h ≠ 0 by omega] using (hH h hpos hh).2 t ht b hb f hf hbf
      · simpa [tgtI, preI, show h ≠ 0 by omega] using (hH h hpos hh).1 b hb f hf hbf
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · by_cases hf0 : f = 0
    · subst hf0
      have ht' : r = false → t = 0 := ht0 rfl
      have e1 : preI V P L R r 0 t b 0 = preI V P L R r 0 0 b 0 := by simp [preI]
      have e2 : tgtI R r 0 t b 0 = tgtI R r 0 0 b 0 := by
        cases r
        · rw [ht' rfl]
        · simp [tgtI]
      simp only [κR, ↓reduceIte]
      rw [e1, e2] at hle ⊢
      rw [e2] at hnn
      exact mul_ratio01 _ _ hnn hle
    · have hp0 : preI V P L R r 0 t b f = 0 := by
        cases r <;> simp [preI, Iface.Rhat0, Iface.Khat0, hf0]
      rw [hp0, zero_mul]
      rw [hp0] at hle
      linarith
  · simp only [κR, show h ≠ 0 by omega, ↓reduceIte]
    exact mul_ratio01 _ _ hnn hle

/-- One height of the induction: the stored laws below give the stored laws at `h`. -/
theorem stored_step (V P L m : ℕ) (R : Iface.M1Run) (hV : 1 ≤ V) (hL : 1 ≤ L) (hm : 1 ≤ m)
    (hR : Iface.F3Hyp V P L m R) (h : ℕ) (hh : h < m) (hS : h ≠ 0 → Stored V P L m R (h - 1)) :
    Stored V P L m R h := by
  have hok : InpOK V (laws (paramsR V P L m R) h) := inp_ok (paramsR V P L m R) hL hV (h + 1)
  have hpR := hR.1
  have hpK := hR.2.1
  constructor
  · have hoff : ∀ b ≤ V, ∀ f ≤ 3, (b ≠ 0 ∨ f ≠ 0) →
        (laws (paramsR V P L m R) h).1 b f = R.rho h b f := by
      intro b hb f hf hbf
      rw [laws_eq, lawsAt_R, kill_off (paramsR V P L m R).V
        (fun a g => GenH (paramsR V P L m R) h true (inp (paramsR V P L m R) h) (fun _ => 0)
          (ind a g) (initK h) 2 0)
        (fun a g => κm (paramsR V P L m R) true h 3 a g) b f hb (by omega) hbf]
      rw [preR_eq V P L m R hV hL hm hR h hS b f hb, κm_paramsR]
      exact pre_mul_κ V P L m R hR true h 3 hh le_rfl (fun _ h => absurd h (by simp)) b f hb
        (by simpa using hf) hbf
    have hs : ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (3 + 1),
        (laws (paramsR V P L m R) h).1 a f =
        ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (3 + 1), R.rho h a f := by
      rw [inpOK_sumR V _ hok, (hpR h hh).2.2]
    intro b hb f hf
    exact eq_of_off_bottom V 3 _ _ hoff hs b hb f (by omega)
  · intro t ht ht0 a ha f hf
    have hoff : ∀ b ≤ V, ∀ f ≤ t, (b ≠ 0 ∨ f ≠ 0) →
        (laws (paramsR V P L m R) h).2 t b f = R.K h t b f := by
      intro b hb f hf hbf
      rw [laws_eq, lawsAt_K, kill_off (paramsR V P L m R).V
        (fun a g => GenH (paramsR V P L m R) h false (inp (paramsR V P L m R) h) (fun _ => 0)
          (ind a g) (kidOf h t) 1 0)
        (fun a g => κm (paramsR V P L m R) false h t a g) b f hb (by omega) hbf]
      rw [preK_eq V P L m R hV hL h hS t ht b f hb, κm_paramsR]
      exact pre_mul_κ V P L m R hR false h t hh ht (fun h0 _ => ht0 h0) b f hb
        (by simpa using hf) hbf
    have hs : ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (t + 1),
        (laws (paramsR V P L m R) h).2 t a f =
        ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (t + 1), R.K h t a f := by
      rw [inpOK_sumK V hV _ hok t ht, (hpK h hh t ht).2.2]
    by_cases hft : f ≤ t
    · exact eq_of_off_bottom V t _ _ hoff hs a ha f hft
    · rw [hok.2.2.2.2.2.1 t a f (by omega), (hpK h hh t ht).2.1 a f (Or.inr (by omega))]

/-- **The stored laws.** With the keep coins of a run satisfying (i) and (ii) of Proposition 13.3 of
the paper, the laws of M1_L at every height below `m` are the stored laws of the run. -/
theorem laws_stored (V P L m : ℕ) (R : Iface.M1Run) (hV : 1 ≤ V) (hL : 1 ≤ L) (hm : 1 ≤ m)
    (hR : Iface.F3Hyp V P L m R) : ∀ h < m, Stored V P L m R h := by
  intro h
  induction h with
  | zero => exact fun hh => stored_step V P L m R hV hL hm hR 0 hh fun h0 => absurd rfl h0
  | succ h ih => exact fun hh => stored_step V P L m R hV hL hm hR (h + 1) hh fun _ => ih (by omega)

/-- **The top law.** The value of the top closure for the end value `[a = b]` is
`sum over f of Wtop_(k+1)[rho*_(m-1), K*_(m-1)](b, f)`. -/
theorem top_stored (V P L m : ℕ) (R : Iface.M1Run) (hV : 1 ≤ V) (hL : 1 ≤ L) (hm : 1 ≤ m)
    (hR : Iface.F3Hyp V P L m R) (q b : ℕ) (hb : b ≤ V) :
    GenH (paramsR V P L m R) m true (inp (paramsR V P L m R) m) (fun _ => 0)
        (fun _ a => if a = b then 1 else 0) (initK m) q 0 =
      ∑ f ∈ Finset.range 4, Iface.Wtop V P (R.rho (m - 1)) (R.K (m - 1)) q b f := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hS := laws_stored V P L (m' + 1) R hV hL hm hR m' (by omega)
  have hk : initK (m' + 1) = fun _ => none := by funext c; simp [initK]
  have hT : (fun (_ : Kid) (a : ℕ) => if a = b then (1 : ℝ) else 0) =
      fun k a => ∑ g ∈ Finset.range 4, (1 : ℝ) * ind b g k a := by
    funext k a
    simp only [ind, one_mul]
    by_cases hab : a = b
    · simp only [hab, true_and, ↓reduceIte]
      simp only [Finset.sum_ite_eq, Finset.mem_range, nN_lt k, ↓reduceIte]
    · simp [hab]
  show Gen V P (isRe (m' + 1) true) (pL L) (laws (paramsR V P L (m' + 1) R) m').1
    (laws (paramsR V P L (m' + 1) R) m').2 (fun _ => 0) _ (initK (m' + 1)) q 0 = _
  rw [show isRe (m' + 1) true = true by simp [isRe], hk, hT, Gen_sum0]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [one_mul, Gen_Wrec V P hV _ _ _ g _ q b hb,
    wrec_stored V P L (m' + 1) R hV hm hR m' hS q b g]
  rfl

/-! ## The end events of the run -/

instance : IsProbabilityMeasure fpMeasure := by
  unfold fpMeasure Pool.poolMeasure
  infer_instance

/-- The run ends with `b` ups. -/
def endEv (p : Params) (k b : ℕ) : Set (Option Frog × ℕ → Val) :=
  {ω | ∃ n, (run p k (Pool.poolSeq (sel p k) ω) n).stack = [] ∧
    count (run p k (Pool.poolSeq (sel p k) ω) n) = b}

theorem measurableSet_endEv (p : Params) (k b : ℕ) : MeasurableSet (endEv p k b) := by
  have hpm := (Pool.measurable_poolSeq (sel p k) (measurableSet_sel p k)).1
  have h1 : endEv p k b = Pool.poolSeq (sel p k) ⁻¹'
      ⋃ n, {y : ℕ → Val | (run p k y n).stack = [] ∧ count (run p k y n) = b} := by
    ext ω
    simp [endEv]
  rw [h1]
  refine hpm (MeasurableSet.iUnion fun n => ?_)
  have h2 : {y : ℕ → Val | (run p k y n).stack = [] ∧ count (run p k y n) = b} =
      (fun y : ℕ → Val => fun j : Fin n => y j) ⁻¹'
        {z : Fin n → Val | (runFin p k z).stack = [] ∧ count (runFin p k z) = b} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, runFin_eq_run]
  rw [h2]
  exact (measurable_pi_iff.2 fun j => measurable_pi_apply _) (measurableSet_finVal _)

theorem upd_nil (p : Params) (s : St) (hs : s.stack = []) (x : Val) : upd p s x = s := by
  obtain ⟨stack, marks, out⟩ := s
  simp only at hs
  subst hs
  rfl

/-- Once the run has ended it stays put. -/
theorem run_absorb (p : Params) (k : ℕ) (y : ℕ → Val) (n : ℕ) (h : (run p k y n).stack = [])
    (j : ℕ) : run p k y (n + j) = run p k y n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show upd p (run p k y (n + j)) (y (n + j)) = _
    rw [ih, upd_nil p _ h]

theorem endEv_disjoint (p : Params) (k b b' : ℕ) (hb : b ≠ b') :
    Disjoint (endEv p k b) (endEv p k b') := by
  rw [Set.disjoint_left]
  rintro ω ⟨n, hn, hc⟩ ⟨n', hn', hc'⟩
  have e1 := run_absorb p k (Pool.poolSeq (sel p k) ω) n hn n'
  have e2 := run_absorb p k (Pool.poolSeq (sel p k) ω) n' hn' n
  rw [Nat.add_comm n' n, e1] at e2
  rw [e2] at hc
  exact hb (hc.symm.trans hc')

/-- On the end event with `b` ups, the planted count is at least `b` (Lemma 13.1 of the paper). -/
theorem endEv_le (p : Params) (k b : ℕ) (hk : 1 ≤ k) (ω : Option Frog × ℕ → Val)
    (h : ω ∈ endEv p k b) : (b : ℕ∞) ≤ plantedG p.m k (fpPaths ω) := by
  obtain ⟨n, -, hc⟩ := h
  rw [← hc]
  exact f1_gen p k hk ω n

/-! ## Proposition 13.3 -/

/-- **Proposition 13.3 of the paper**, the statement `Iface.f3L` of the interface. -/
theorem f3L_holds : Iface.f3L := by
  intro V P L m hV hP hL hm R hR k hk hkP Wtil hW
  have hL1 : 1 ≤ L := by omega
  have hEv : ∀ b ≤ V, fpMeasure (endEv (paramsR V P L m R) k b) = ENNReal.ofReal
      (∑ f ∈ Finset.range 4, Iface.Wtop V P (R.rho (m - 1)) (R.K (m - 1)) (k + 1) b f) := by
    intro b hb
    rw [← top_stored V P L m R hV hL1 hm hR (k + 1) b hb]
    exact top_law_gen (paramsR V P L m R) (paramsR_keep0 V P L m R) hL hV hP k b hkP hb
  have hWle : ∀ x ≤ V, ∑ f ∈ Finset.range 4, Wtil x f ≤
      (fpMeasure (endEv (paramsR V P L m R) k x)).toReal := by
    intro x hx
    rw [hEv x hx, ENNReal.toReal_ofReal']
    exact le_trans (Finset.sum_le_sum fun f hf => hW x hx f (by simp at hf; omega)) (le_max_left _ _)
  have hcount : ∀ b ω, ω ∈ endEv (paramsR V P L m R) k b → (b : ℕ∞) ≤ plantedG m k (fpPaths ω) :=
    fun b ω h => endEv_le (paramsR V P L m R) k b hk ω h
  have hmeasG : Measurable fun π : Frog → ℕ → Step 3 => plantedG m k π := measurable_plantedG m k
  constructor
  · intro g hg
    have hA : MeasurableSet {π : Frog → ℕ → Step 3 | plantedG m k π ≤ (g : ℕ∞)} :=
      hmeasG (MeasurableSet.of_discrete : MeasurableSet (Set.Iic (g : ℕ∞)))
    have hcdf : Iface.cdfG m k g = (fpMeasure {ω | plantedG m k (fpPaths ω) ≤ (g : ℕ∞)}).toReal := by
      have e : {π : Iface.PFrog → ℕ → Step 3 | Iface.plantedG m k π ≤ (g : ℕ∞)} =
          {π : Frog → ℕ → Step 3 | plantedG m k π ≤ (g : ℕ∞)} := by
        ext π
        simp only [Set.mem_ofPred_eq, plantedG_iface]
      unfold Iface.cdfG
      rw [e, ← map_fpPaths, Measure.map_apply measurable_fpPaths hA]
      rfl
    rw [hcdf]
    have hBm : MeasurableSet {ω | plantedG m k (fpPaths ω) ≤ (g : ℕ∞)} := measurable_fpPaths hA
    have hdB : Disjoint {ω | plantedG m k (fpPaths ω) ≤ (g : ℕ∞)}
        (⋃ x ∈ Finset.Ioc g V, endEv (paramsR V P L m R) k x) := by
      rw [Set.disjoint_left]
      intro ω hωB hωE
      simp only [Set.mem_iUnion, Finset.mem_Ioc] at hωE
      obtain ⟨x, hx, hωx⟩ := hωE
      have h1 : (x : ℕ∞) ≤ g := (hcount x ω hωx).trans hωB
      have h2 : x ≤ g := by exact_mod_cast h1
      omega
    have hpd : Set.PairwiseDisjoint (↑(Finset.Ioc g V)) (endEv (paramsR V P L m R) k) :=
      fun x _ y _ hxy => endEv_disjoint _ k x y hxy
    have hsum : fpMeasure {ω | plantedG m k (fpPaths ω) ≤ (g : ℕ∞)} +
        ∑ x ∈ Finset.Ioc g V, fpMeasure (endEv (paramsR V P L m R) k x) ≤ 1 := by
      rw [← measure_biUnion_finset hpd fun x _ => measurableSet_endEv _ k x,
        ← measure_union hdB (Finset.measurableSet_biUnion _ fun x _ => measurableSet_endEv _ k x)]
      exact prob_le_one
    have h3 := ENNReal.toReal_mono ENNReal.one_ne_top hsum
    rw [ENNReal.toReal_add (measure_ne_top _ _)
      (ENNReal.sum_ne_top.2 fun _ _ => measure_ne_top _ _),
      ENNReal.toReal_sum fun _ _ => measure_ne_top _ _, ENNReal.toReal_one] at h3
    have h4 := Finset.sum_le_sum fun x (hx : x ∈ Finset.Ioc g V) =>
      hWle x (Finset.mem_Ioc.1 hx).2
    linarith
  · have hF : Measurable fun π : Frog → ℕ → Step 3 => ((plantedG m k π : ℕ∞) : ℝ≥0∞) :=
      (measurable_of_countable _).comp hmeasG
    have hmean : Iface.meanG m k =
        (∫⁻ ω, ((plantedG m k (fpPaths ω) : ℕ∞) : ℝ≥0∞) ∂fpMeasure).toReal := by
      have e : (fun π : Iface.PFrog → ℕ → Step 3 => ((Iface.plantedG m k π : ℕ∞) : ℝ≥0∞)) =
          fun π : Frog → ℕ → Step 3 => ((plantedG m k π : ℕ∞) : ℝ≥0∞) := by
        funext π
        rw [plantedG_iface]
      unfold Iface.meanG
      rw [e, ← map_fpPaths, lintegral_map hF measurable_fpPaths]
    rw [hmean]
    have hfin : ∫⁻ ω, ((plantedG m k (fpPaths ω) : ℕ∞) : ℝ≥0∞) ∂fpMeasure ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ((frogsF m k).card : ℝ≥0∞)) (ENNReal.natCast_ne_top _) ?_
      calc ∫⁻ ω, ((plantedG m k (fpPaths ω) : ℕ∞) : ℝ≥0∞) ∂fpMeasure
          ≤ ∫⁻ _, ((frogsF m k).card : ℝ≥0∞) ∂fpMeasure := by
            refine lintegral_mono fun ω => ?_
            have := ENat.toENNReal_le.2 (plantedG_le_card m k (fpPaths ω))
            simpa using this
        _ = (frogsF m k).card := by simp
    have hpt : ∀ ω, ∑ x ∈ Finset.range (V + 1),
        (endEv (paramsR V P L m R) k x).indicator (fun _ => (x : ℝ≥0∞)) ω ≤
          ((plantedG m k (fpPaths ω) : ℕ∞) : ℝ≥0∞) := by
      intro ω
      by_cases h : ∃ x ∈ Finset.range (V + 1), ω ∈ endEv (paramsR V P L m R) k x
      · obtain ⟨x0, hx0, hω⟩ := h
        rw [Finset.sum_eq_single x0 (fun x _ hne => Set.indicator_of_notMem
          (Set.disjoint_left.1 (endEv_disjoint _ k x0 x (Ne.symm hne)) hω) _)
          (fun h => absurd hx0 h), Set.indicator_of_mem hω]
        have := ENat.toENNReal_le.2 (hcount x0 ω hω)
        simpa using this
      · push Not at h
        rw [Finset.sum_eq_zero fun x hx => Set.indicator_of_notMem (h x hx) _]
        exact zero_le
    have hlow : ∑ x ∈ Finset.range (V + 1), (x : ℝ≥0∞) * fpMeasure (endEv (paramsR V P L m R) k x) ≤
        ∫⁻ ω, ((plantedG m k (fpPaths ω) : ℕ∞) : ℝ≥0∞) ∂fpMeasure := by
      calc ∑ x ∈ Finset.range (V + 1), (x : ℝ≥0∞) * fpMeasure (endEv (paramsR V P L m R) k x)
          = ∑ x ∈ Finset.range (V + 1), ∫⁻ ω,
              (endEv (paramsR V P L m R) k x).indicator (fun _ => (x : ℝ≥0∞)) ω ∂fpMeasure := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [lintegral_indicator_const (measurableSet_endEv _ k x)]
        _ = ∫⁻ ω, ∑ x ∈ Finset.range (V + 1),
              (endEv (paramsR V P L m R) k x).indicator (fun _ => (x : ℝ≥0∞)) ω ∂fpMeasure := by
            rw [lintegral_finsetSum _ fun x _ =>
              measurable_const.indicator (measurableSet_endEv _ k x)]
        _ ≤ _ := lintegral_mono hpt
    have h3 := ENNReal.toReal_mono hfin hlow
    rw [ENNReal.toReal_sum fun x _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (measure_ne_top _ _)] at h3
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h3
    refine le_trans (Finset.sum_le_sum fun x hx => ?_) h3
    exact mul_le_mul_of_nonneg_left (hWle x (by simpa [Nat.lt_succ_iff] using hx)) (Nat.cast_nonneg _)

end FrogModel.D3
