module

public import FrogModel.D3.LaneB.ClosureFacts
public import FrogModel.D3.LaneB.Coins
public import FrogModel.D3.LaneB.Good
public import FrogModel.D3.LaneB.Measurability
public import FrogModel.D3.LaneB.Succ
public import FrogModel.D3.LaneB.Counts
public import FrogModel.D3.LaneB.Sampling
public import FrogModel.D3.LaneB.ClosLaw
public import FrogModel.D3.LaneB.ClosIdentity

@[expose] public section

/-!
# Optional sampling in the closure (proofs of Lemmas 10.5 and 10.8 of the paper)

Along the entries of one child, `G(k) - k/3` is a submartingale (the coins of Lemma 10.3); stopped at a
bounded index read from the child's past and an independent factor, its mean does not decrease
(`os_core`). In the closure the stopping index is the number `e_c` of entries of the child `c` before
`N ∧ n` (`os_closure`), and `n → ∞` gives `E[G_c(e_c) - e_c/3] ≥ 0` (`os_closure_limit`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-! ## Optional sampling along the entries of one child (proofs of Lemmas 10.5 and 10.8 of the paper) -/

/-- The curve with its coins, the rest of the closure in `R`: `G(min σ n) - min σ n / 3`. -/
noncomputable def stopVal {R : Type*} (σ : (ℕ → ℕ∞) × R → ℕ) (n : ℕ)
    (p : ((ℕ → ℕ∞) × (ℕ → Bool)) × R) : ℝ :=
  ((p.1.1 (min (σ (p.1.1, p.2)) n)).toNat : ℝ) - ((min (σ (p.1.1, p.2)) n : ℕ) : ℝ) / 3

theorem toNat_le_of_le_natCast {a : ℕ∞} {b : ℕ} (h : a ≤ b) : a.toNat ≤ b := by
  have hne : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top b) h
  rw [← ENat.natCast_le_natCast, ENat.natCast_toNat hne]
  exact h

/-- The prefix `G(0), ..., G(i)` extended constantly. -/
def extPrefix (i : ℕ) (h : Fin (i + 1) → ℕ∞) : ℕ → ℕ∞ := fun k => h ⟨min k i, by omega⟩

theorem measurable_extPrefix (i : ℕ) : Measurable (extPrefix i) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem measurable_stopVal {R : Type*} [MeasurableSpace R] (σ : (ℕ → ℕ∞) × R → ℕ)
    (hσ : Measurable σ) (n : ℕ) : Measurable (stopVal σ n) := by
  have hpair : Measurable fun p : ((ℕ → ℕ∞) × (ℕ → Bool)) × R => (p.1.1, p.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hs : Measurable fun p : ((ℕ → ℕ∞) × (ℕ → Bool)) × R => min (σ (p.1.1, p.2)) n :=
    (Measurable.of_discrete (f := fun k : ℕ => min k n)).comp (hσ.comp hpair)
  have h1 : Measurable fun p : ((ℕ → ℕ∞) × (ℕ → Bool)) × R => p.1.1 (min (σ (p.1.1, p.2)) n) :=
    measurable_comp_nat (fun p k => p.1.1 k)
      (fun k => (measurable_pi_apply k).comp (measurable_fst.comp measurable_fst)) _ hs
  exact ((Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp h1).sub
    (((Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp hs).div_const 3)

theorem stopVal_abs_le {R : Type*} (σ : (ℕ → ℕ∞) × R → ℕ) (n B : ℕ)
    (p : ((ℕ → ℕ∞) × (ℕ → Bool)) × R) (hp : ∀ i, p.1.1 i ≤ ((i + B : ℕ) : ℕ∞)) :
    |stopVal σ n p| ≤ 2 * n + B := by
  unfold stopVal
  set k := min (σ (p.1.1, p.2)) n
  have hk : k ≤ n := min_le_right _ _
  have h1 : (p.1.1 k).toNat ≤ k + B := by
    have := hp k
    have hne : p.1.1 k ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) this
    rw [← ENat.natCast_le_natCast, ENat.natCast_toNat hne]
    exact this
  have h1' : ((p.1.1 k).toNat : ℝ) ≤ k + B := by exact_mod_cast h1
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ (p.1.1 k).toNat := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

/-- **Optional sampling** for a curve with own-path coins: for stopping indices `σ ≤ τ` of the
filtration of the curve prefixes and an independent factor `R`,
`E[G(σ ∧ n) - (σ ∧ n)/3] ≤ E[G(τ ∧ n) - (τ ∧ n)/3]`. -/
theorem os_core (μc : Measure ((ℕ → ℕ∞) × (ℕ → Bool))) [IsProbabilityMeasure μc]
    (hξ : ∀ i, μc {z | z.2 i = true} = 3⁻¹)
    (hind : ∀ i, IndepFun (fun z => z.2 i) (fun z => fun l : Fin (i + 1) => z.1 l) μc)
    (hinc : ∀ᵐ z ∂μc, ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1))
    (B : ℕ) (hbd : ∀ᵐ z ∂μc, ∀ i, z.1 i ≤ ((i + B : ℕ) : ℕ∞))
    {R : Type*} [MeasurableSpace R] (ρ : Measure R) [IsProbabilityMeasure ρ]
    (σ τ : (ℕ → ℕ∞) × R → ℕ) (hσ : Measurable σ) (hτ : Measurable τ) (hστ : ∀ p, σ p ≤ τ p)
    (hstop : ∀ (i : ℕ) (G G' : ℕ → ℕ∞) (r : R), (∀ k ≤ i, G k = G' k) →
      ((σ (G, r) ≤ i ∧ i < τ (G, r)) ↔ (σ (G', r) ≤ i ∧ i < τ (G', r)))) (n : ℕ) :
    ∫ p, stopVal σ n p ∂(μc.prod ρ) ≤ ∫ p, stopVal τ n p ∂(μc.prod ρ) := by
  set P := μc.prod ρ
  have hbdP : ∀ᵐ p ∂P, ∀ i, p.1.1 i ≤ ((i + B : ℕ) : ℕ∞) :=
    Measure.quasiMeasurePreserving_fst.ae hbd
  have hincP : ∀ᵐ p ∂P, ∀ i, p.1.1 i + (if p.1.2 i then 1 else 0) ≤ p.1.1 (i + 1) :=
    Measure.quasiMeasurePreserving_fst.ae hinc
  have hint : ∀ (s : (ℕ → ℕ∞) × R → ℕ), Measurable s → Integrable (stopVal s n) P := fun s hs =>
    (integrable_const ((2 * n + B : ℕ) : ℝ)).mono' (measurable_stopVal s hs n).aestronglyMeasurable
      (hbdP.mono fun p hp => by
        rw [Real.norm_eq_abs]; push_cast; exact stopVal_abs_le s n B p hp)
  rw [← sub_nonneg, ← integral_sub (hint τ hτ) (hint σ hσ)]
  -- the increments
  set Y : ℕ → ((ℕ → ℕ∞) × (ℕ → Bool)) × R → ℕ∞ := fun i p => p.1.1 i
  set A : ℕ → Set (((ℕ → ℕ∞) × (ℕ → Bool)) × R) :=
    fun i => {p | σ (p.1.1, p.2) ≤ i ∧ i < τ (p.1.1, p.2)}
  have htel : ∀ p, stopVal τ n p - stopVal σ n p = ∑ i ∈ Finset.range n,
      (A i).indicator (fun p => ((Y (i + 1) p).toNat : ℝ) - (Y i p).toNat - 1 / 3) p := by
    intro p
    have := telescope_stop (fun i => ((p.1.1 i).toNat : ℝ) - (i : ℝ) / 3)
      (σ (p.1.1, p.2)) (τ (p.1.1, p.2)) n (hστ _)
    unfold stopVal
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [A, Y, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> push_cast <;> ring
  simp_rw [htel]
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
  have hpair : Measurable fun p : ((ℕ → ℕ∞) × (ℕ → Bool)) × R => (p.1.1, p.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hAm : ∀ i, MeasurableSet (A i) := fun i =>
    (measurableSet_le (Measurable.of_discrete (f := id) |>.comp (hσ.comp hpair))
      measurable_const).inter (measurableSet_lt measurable_const (hτ.comp hpair))
  have hterm : ∀ i, Integrable (fun p => (A i).indicator
      (fun p => ((Y (i + 1) p).toNat : ℝ) - (Y i p).toNat - 1 / 3) p) P := by
    intro i
    refine (integrable_const ((2 * (i + 1) + 2 * B + 1 : ℕ) : ℝ)).mono' ?_ (hbdP.mono fun p hp => ?_)
    · exact (((Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp (hYm (i + 1))).sub
        ((Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp (hYm i)) |>.sub
          measurable_const).indicator (hAm i) |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have h1 : ((Y (i + 1) p).toNat : ℝ) ≤ (i + 1 + B : ℕ) := by
        exact_mod_cast toNat_le_of_le_natCast (hp (i + 1))
      have h0 : ((Y i p).toNat : ℝ) ≤ (i + B : ℕ) := by
        exact_mod_cast toNat_le_of_le_natCast (hp i)
      have h1' : (0 : ℝ) ≤ (Y (i + 1) p).toNat := Nat.cast_nonneg _
      have h0' : (0 : ℝ) ≤ (Y i p).toNat := Nat.cast_nonneg _
      push_cast at h1 h0 ⊢
      by_cases hA : p ∈ A i
      · rw [Set.indicator_of_mem hA, abs_le]
        constructor <;> linarith
      · rw [Set.indicator_of_notMem hA, abs_zero]
        positivity
  rw [integral_finsetSum _ fun i _ => hterm i]
  refine Finset.sum_nonneg fun i _ => ?_
  -- independence of the coin `ξ_i` from `A i`
  have hAξ : P (A i ∩ {p | p.1.2 i = true}) = 3⁻¹ * P (A i) := by
    set Bs : Set ((Fin (i + 1) → ℕ∞) × R) :=
      {hr | σ (extPrefix i hr.1, hr.2) ≤ i ∧ i < τ (extPrefix i hr.1, hr.2)}
    have hBs : MeasurableSet Bs := by
      have he : Measurable fun hr : (Fin (i + 1) → ℕ∞) × R => (extPrefix i hr.1, hr.2) :=
        ((measurable_extPrefix i).comp measurable_fst).prodMk measurable_snd
      exact (measurableSet_le (Measurable.of_discrete (f := id) |>.comp (hσ.comp he))
        measurable_const).inter (measurableSet_lt measurable_const (hτ.comp he))
    have hA : A i = {p | ((fun l : Fin (i + 1) => p.1.1 l), p.2) ∈ Bs} := by
      ext p
      simp only [A, Bs, Set.mem_ofPred_eq]
      exact hstop i _ _ p.2 fun k hk => by simp [extPrefix, Nat.min_eq_left hk]
    rw [hA, indep_section μc ρ (fun z => fun l : Fin (i + 1) => z.1 l) (fun z => z.2 i)
      (measurable_pi_iff.mpr fun l => (measurable_pi_apply _).comp measurable_fst)
      ((measurable_pi_apply i).comp measurable_snd) (hind i) Bs hBs, hξ i]
  exact os_step P (Y i) (Y (i + 1)) (fun p => p.1.2 i) (hYm i) (hYm (i + 1))
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)) (A i) (hAm i) hAξ
    (hincP.mono fun p hp => hp i) (i + 1 + B) (hbdP.mono fun p hp => by
      have := hp (i + 1); simpa [add_comm, add_left_comm, add_assoc] using this)

/-! ## Optional sampling in the closure -/

/-- The closure with the child `c` replaced by `p.1`. -/
def asm (c : Fin 3) (p : (ℕ → ℕ∞) × ClosSample) : ClosSample :=
  (Function.update p.2.1 c p.1, p.2.2)

theorem measurable_asm (c : Fin 3) : Measurable (asm c) :=
  ((measurable_update' (a := c)).comp ((measurable_fst.comp measurable_snd).prodMk
    measurable_fst)).prodMk (measurable_snd.comp measurable_snd)

/-- `e_c ∧ n` as a natural number. -/
noncomputable def eN (q : ℕ) (c : Fin 3) (n : ℕ) (x : ClosSample) : ℕ :=
  (min (closE q x.1 x.2 c) (n : ℕ∞)).toNat

theorem eN_cast (q : ℕ) (c : Fin 3) (n : ℕ) (x : ClosSample) :
    (eN q c n x : ℕ∞) = min (closE q x.1 x.2 c) (n : ℕ∞) :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (min_le_right _ _))

theorem eN_le (q : ℕ) (c : Fin 3) (n : ℕ) (x : ClosSample) : eN q c n x ≤ n := by
  rw [← ENat.natCast_le_natCast, eN_cast]; exact min_le_right _ _

theorem lt_eN_iff (q : ℕ) (c : Fin 3) (n i : ℕ) (x : ClosSample) :
    i < eN q c n x ↔ (i : ℕ∞) < closE q x.1 x.2 c ∧ i < n := by
  rw [← ENat.natCast_lt_natCast, eN_cast, lt_min_iff, ENat.natCast_lt_natCast]

theorem measurable_eN (q : ℕ) (c : Fin 3) (n : ℕ) : Measurable (eN q c n) :=
  (Measurable.of_discrete (f := fun y : ℕ∞ => (min y (n : ℕ∞)).toNat)).comp (measurable_closE q c)

/-- `G_c(s) - s/3`. -/
noncomputable def osVal (c : Fin 3) (s : ClosSample → ℕ) (x : ClosSample) : ℝ :=
  ((x.1 c (s x)).toNat : ℝ) - (s x : ℝ) / 3

theorem measurable_osVal (c : Fin 3) (s : ClosSample → ℕ) (hs : Measurable s) :
    Measurable (osVal c s) := by
  have h1 : Measurable fun x : ClosSample => x.1 c (s x) :=
    measurable_comp_nat (fun x k => x.1 c k) (measurable_child c) s hs
  have h2 : Measurable fun x : ClosSample => ((x.1 c (s x)).toNat : ℝ) :=
    (Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp h1
  have h3 : Measurable fun x : ClosSample => ((s x : ℕ) : ℝ) :=
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp hs
  exact h2.sub (h3.div_const 3)

theorem stopVal_asm (c : Fin 3) (n : ℕ) (s : ClosSample → ℕ) (hs : ∀ x, s x ≤ n)
    (p : ((ℕ → ℕ∞) × (ℕ → Bool)) × ClosSample) :
    stopVal (fun g => s (asm c g)) n p = osVal c s (asm c (p.1.1, p.2)) := by
  unfold stopVal osVal asm
  rw [min_eq_left (hs _)]
  simp

/-- Optional sampling in the closure: `E[G_c(e_c ∧ J ∧ n) - ...] ≤ E[G_c(e_c ∧ n) - ...]`. -/
theorem os_closure (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (μc : Measure ((ℕ → ℕ∞) × (ℕ → Bool))) [IsProbabilityMeasure μc] (hμc : μc.map Prod.fst = Q)
    (hξ : ∀ i, μc {z | z.2 i = true} = 3⁻¹)
    (hind : ∀ i, IndepFun (fun z => z.2 i) (fun z => fun l : Fin (i + 1) => z.1 l) μc)
    (hinc : ∀ᵐ z ∂μc, ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1))
    (B : ℕ) (hbd : ∀ᵐ z ∂μc, ∀ i, z.1 i ≤ ((i + B : ℕ) : ℕ∞)) (q : ℕ) (c : Fin 3) (J n : ℕ) :
    ∫ x, osVal c (fun x => min (eN q c n x) J) x ∂closMeasure Q ≤
      ∫ x, osVal c (eN q c n) x ∂closMeasure Q := by
  have hmap := closMeasure_update Q μc hμc c
  have hφ : Measurable fun p : ((ℕ → ℕ∞) × (ℕ → Bool)) × ClosSample => asm c (p.1.1, p.2) :=
    (measurable_asm c).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hmap' : (μc.prod (closMeasure Q)).map (fun p => asm c (p.1.1, p.2)) = closMeasure Q := hmap
  have hm1 : Measurable fun x : ClosSample => min (eN q c n x) J :=
    (Measurable.of_discrete (f := fun k : ℕ => min k J)).comp (measurable_eN q c n)
  rw [← hmap', integral_map hφ.aemeasurable (measurable_osVal c _ hm1).aestronglyMeasurable,
    integral_map hφ.aemeasurable (measurable_osVal c _ (measurable_eN q c n)).aestronglyMeasurable]
  have h1 := os_core μc hξ hind hinc B hbd (closMeasure Q)
    (fun g => min (eN q c n (asm c g)) J) (fun g => eN q c n (asm c g))
    ((Measurable.of_discrete (f := fun k : ℕ => min k J)).comp ((measurable_eN q c n).comp
      (measurable_asm c)))
    ((measurable_eN q c n).comp (measurable_asm c)) (fun g => min_le_left _ _)
    (fun i G G' r hGG' => by
      have key : (i : ℕ∞) < closE q (asm c (G, r)).1 (asm c (G, r)).2 c ↔
          (i : ℕ∞) < closE q (asm c (G', r)).1 (asm c (G', r)).2 c :=
        closE_stop q i c _ _ r.2 (fun c' hc' => by simp [asm, Function.update_of_ne hc'])
          (fun k hk => by simp [asm, hGG' k hk])
      simp only [not_lt.symm, lt_min_iff, lt_eN_iff, key]) n
  have e1 : ∀ p, stopVal (fun g => min (eN q c n (asm c g)) J) n p =
      osVal c (fun x => min (eN q c n x) J) (asm c (p.1.1, p.2)) := fun p =>
    stopVal_asm c n (fun x => min (eN q c n x) J)
      (fun x => (min_le_left _ _).trans (eN_le q c n x)) p
  have e2 : ∀ p, stopVal (fun g => eN q c n (asm c g)) n p =
      osVal c (eN q c n) (asm c (p.1.1, p.2)) := fun p => stopVal_asm c n _ (eN_le q c n) p
  simp only [e1, e2] at h1
  exact h1

theorem ae_le_closN (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    ∀ᵐ x ∂closMeasure Q, closN q x.1 x.2 < ⊤ ∧ closX q x.1 x.2 ≤ closN q x.1 x.2 ∧
      ∀ c, closE q x.1 x.2 c ≤ closN q x.1 x.2 ∧ gE q c x ≤ closN q x.1 x.2 := by
  filter_upwards [ae_closN_eq Q q B hgood] with x hx
  refine ⟨hx.1, ?_, fun c => ⟨?_, ?_⟩⟩
  · rw [hx.2.2]; exact le_self_add
  · rw [hx.2.2]
    exact le_add_left (Finset.single_le_sum (f := fun c => closE q x.1 x.2 c)
      (fun _ _ => bot_le) (Finset.mem_univ c))
  · rw [hx.2.1]
    exact le_add_left (Finset.single_le_sum (f := fun c => gE q c x)
      (fun _ _ => bot_le) (Finset.mem_univ c))

theorem toReal_toENNReal (y : ℕ∞) : ((y : ℝ≥0∞)).toReal = (y.toNat : ℝ) := by
  induction y using ENat.recTopCoe with
  | top => simp
  | coe k => simp

theorem integrable_closN (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    Integrable (fun x => ((closN q x.1 x.2).toNat : ℝ)) (closMeasure Q) := by
  have h := integrable_toReal_of_lintegral_ne_top
    ((Measurable.of_discrete (f := fun y : ℕ∞ => (y : ℝ≥0∞))).comp (measurable_closN q)).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_closN_le Q q B hgood))
  simpa only [Function.comp, toReal_toENNReal] using h

/-- Dominated convergence for `E[G_c(e_c ∧ n) - (e_c ∧ n)/3]` as `n → ∞`. -/
theorem tendsto_osVal_eN (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) (q : ℕ) (c : Fin 3) :
    Filter.Tendsto (fun n => ∫ x, osVal c (eN q c n) x ∂closMeasure Q) Filter.atTop
      (nhds (∫ x, (((gE q c x).toNat : ℝ) - ((closE q x.1 x.2 c).toNat : ℝ) / 3)
        ∂closMeasure Q)) := by
  have hbound := integrable_closN Q q B hgood
  exact tendsto_integral_of_dominated_convergence
    (F := fun n => osVal c (eN q c n)) (μ := closMeasure Q)
    (f := fun x => ((gE q c x).toNat : ℝ) - ((closE q x.1 x.2 c).toNat : ℝ) / 3)
    (fun x => 2 * ((closN q x.1 x.2).toNat : ℝ))
    (fun n => (measurable_osVal c _ (measurable_eN q c n)).aestronglyMeasurable)
    (hbound.const_mul 2)
    (fun n => by
      filter_upwards [ae_le_closN Q q B hgood, hgood] with x hx hg
      obtain ⟨hN, -, hc⟩ := hx
      have hNne := hN.ne
      have hEne : closE q x.1 x.2 c ≠ ⊤ := ne_top_of_le_ne_top hNne (hc c).1
      have h1 : eN q c n x ≤ (closE q x.1 x.2 c).toNat := by
        rw [← ENat.natCast_le_natCast, eN_cast, ENat.natCast_toNat hEne]; exact min_le_left _ _
      have h2 : (x.1 c (eN q c n x)).toNat ≤ (closN q x.1 x.2).toNat :=
        (ENat.toNat_le_toNat ((hg c).1 h1) (ne_top_of_le_ne_top hNne (hc c).2)).trans
          (ENat.toNat_le_toNat (hc c).2 hNne)
      have h3 : (closE q x.1 x.2 c).toNat ≤ (closN q x.1 x.2).toNat :=
        ENat.toNat_le_toNat (hc c).1 hNne
      have h2' : ((x.1 c (eN q c n x)).toNat : ℝ) ≤ (closN q x.1 x.2).toNat := by exact_mod_cast h2
      have h1' : ((eN q c n x : ℕ) : ℝ) ≤ (closN q x.1 x.2).toNat := by exact_mod_cast h1.trans h3
      have h0 : (0 : ℝ) ≤ (x.1 c (eN q c n x)).toNat := Nat.cast_nonneg _
      have h0' : (0 : ℝ) ≤ (eN q c n x : ℕ) := Nat.cast_nonneg _
      rw [Real.norm_eq_abs, abs_le]
      unfold osVal
      constructor <;> linarith)
    (by
      filter_upwards [ae_le_closN Q q B hgood] with x hx
      have hEne : closE q x.1 x.2 c ≠ ⊤ := ne_top_of_le_ne_top hx.1.ne (hx.2.2 c).1
      refine tendsto_atTop_of_eventually_const (i₀ := (closE q x.1 x.2 c).toNat) fun n hn => ?_
      have : eN q c n x = (closE q x.1 x.2 c).toNat := by
        rw [← ENat.natCast_inj, eN_cast, ENat.natCast_toNat hEne]
        exact min_eq_left (by rw [← ENat.natCast_toNat hEne]; exact_mod_cast hn)
      simp only [osVal, this, gE])

/-- **Optional sampling at `e_c ∧ J ≤ e_c`** (proof of Lemma 10.5 of the paper): `E[G_c(e_c ∧ J) - (e_c ∧ J)/3] ≤
E[G_c(e_c) - e_c/3]`. -/
theorem os_closure_limit (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (μc : Measure ((ℕ → ℕ∞) × (ℕ → Bool))) [IsProbabilityMeasure μc] (hμc : μc.map Prod.fst = Q)
    (hξ : ∀ i, μc {z | z.2 i = true} = 3⁻¹)
    (hind : ∀ i, IndepFun (fun z => z.2 i) (fun z => fun l : Fin (i + 1) => z.1 l) μc)
    (hinc : ∀ᵐ z ∂μc, ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1))
    (B : ℕ) (hbd : ∀ᵐ z ∂μc, ∀ i, z.1 i ≤ ((i + B : ℕ) : ℕ∞))
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) (q : ℕ) (c : Fin 3) (J : ℕ) :
    ∫ x, osVal c (fun x => minE (closE q x.1 x.2 c) J) x ∂closMeasure Q ≤
      ∫ x, (((gE q c x).toNat : ℝ) - ((closE q x.1 x.2 c).toNat : ℝ) / 3) ∂closMeasure Q := by
  have hJ : ∀ n, J ≤ n → ∀ x, min (eN q c n x) J = minE (closE q x.1 x.2 c) J := by
    intro n hn x
    unfold eN minE
    generalize closE q x.1 x.2 c = e
    induction e using ENat.recTopCoe with
    | top => simp; omega
    | coe k =>
      have h1 : min (k : ℕ∞) (n : ℕ∞) = ((min k n : ℕ) : ℕ∞) := by
        rcases le_total k n with h | h <;> simp [h]
      have h2 : min (k : ℕ∞) (J : ℕ∞) = ((min k J : ℕ) : ℕ∞) := by
        rcases le_total k J with h | h <;> simp [h]
      rw [h1, h2, ENat.toNat_natCast, ENat.toNat_natCast]
      omega
  have hlim := tendsto_osVal_eN Q B hgood q c
  refine ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨J, fun n hn => ?_⟩)
  have h := os_closure Q μc hμc hξ hind hinc B hbd q c J n
  have hfun : (fun x => min (eN q c n x) J) = fun x => minE (closE q x.1 x.2 c) J :=
    funext (hJ n hn)
  rw [hfun] at h
  exact h


end FrogModel.D3.Iface
