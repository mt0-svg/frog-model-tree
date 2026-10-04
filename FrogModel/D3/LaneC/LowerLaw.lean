module

public import FrogModel.D3.LaneC.LowerMeas

@[expose] public section

/-!
# The law of a lower closure by first-step analysis

For the proof of Lemma 12.1 of the paper. `lawV_step`: the law of the capped count from `q ≥ 1`
frogs is the average over the first direction of the laws after one step: up or a dead child (one
frog less, the count shifted when that direction is counted), a fresh child (one frog less plus its
first answer, the child now a coin child), a coin child (one frog less plus its coin, which keeps
the pool with probability `1/3`: a self-loop). The self-loop is solved algebraically, so no
absorption argument is needed. `lawV_S2`, `lawV_S3`: the solutions are the stage laws of `lawS2` and
`lawS3` of FrogModel/D3/Interfaces/Step.lean.
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneC.Lower

section Step

variable (ρ : Measure ℕ) [IsProbabilityMeasure ρ]

/-- The contribution of the child `s` to the first step of the lower closure. -/
noncomputable def branch (b : Fin 4) (cap q Rmax : ℕ) (τ : Fin 3 → Ty) (k : ℕ) (s : Fin 3) : ℝ :=
  match τ s with
  | .dead => if b = s.succ then capShift cap (lawV ρ b cap (q - 1) τ) k
      else lawV ρ b cap (q - 1) τ k
  | .fresh => ∑ r ∈ Finset.range (Rmax + 1),
      (ρ {r}).toReal * lawV ρ b cap (q - 1 + r) (Function.update τ s .coin) k
  | .coin => (1 / 3) * lawV ρ b cap q τ k + (2 / 3) * lawV ρ b cap (q - 1) τ k

theorem lawV_zero (b : Fin 4) (cap : ℕ) (τ : Fin 3 → Ty) (k : ℕ) :
    lawV ρ b cap 0 τ k = if k = 0 then 1 else 0 := by
  unfold lawV
  have h : {ω : LSample | minE (cnt b 0 τ ω) cap = k} =
      if k = 0 then Set.univ else ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [cnt_zero]
    have h0 : minE 0 cap = 0 := by simp [minE]
    split_ifs with hk <;> simp [h0, hk, eq_comm]
  rw [h]
  split_ifs <;> simp

theorem measurable_cnt_gen (b : Fin 4) (τ : Fin 3 → Ty) (f : LSample → ℕ) (hf : Measurable f)
    (g : LSample → LSample) (hg : Measurable g) :
    Measurable fun ω => cnt b (f ω) τ (g ω) := by
  have hk : ∀ k, Measurable fun ω : LSample => cnt b k τ ω := fun k => measurable_cnt b k τ
  have h : Measurable fun p : LSample × ℕ => cnt b p.2 τ p.1 :=
    measurable_from_prod_countable_left hk
  have h3 := h.comp (hg.prodMk hf)
  exact h3

theorem measurable_coinShift (s : Fin 3) :
    Measurable fun ω : LSample =>
      ((ω.1, ω.2.1, Function.update ω.2.2 s fun i => ω.2.2 s (i + 1)) : LSample) := by
  refine measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk ?_)
  have h2 : Measurable fun ω : LSample => ω.2.2 := measurable_snd.comp measurable_snd
  have hs : Measurable fun ω : LSample => fun i => ω.2.2 s (i + 1) :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply (i + 1)).comp
      ((measurable_pi_apply s).comp h2)
  exact (measurable_update' (a := s)).comp (h2.prodMk hs)

theorem measurable_stepA_cnt (b a : Fin 4) (q : ℕ) (τ : Fin 3 → Ty) :
    Measurable fun ω => cnt b (stepA a q τ ω).1 (stepA a q τ ω).2.1 (stepA a q τ ω).2.2 := by
  induction a using Fin.cases with
  | zero => simpa [stepA] using measurable_cnt b (q - 1) τ
  | succ s =>
    cases h : τ s with
    | dead => simpa [stepA, h] using measurable_cnt b (q - 1) τ
    | fresh =>
      simp only [stepA, Fin.cases_succ, h]
      exact measurable_cnt_gen b _ (fun ω => q - 1 + ω.2.1 s)
        (measurable_of_countable (fun r : ℕ => q - 1 + r) |>.comp
          ((measurable_pi_apply s).comp (measurable_fst.comp measurable_snd))) id measurable_id
    | coin =>
      simp only [stepA, Fin.cases_succ, h]
      exact measurable_cnt_gen b _ (fun ω => q - 1 + (ω.2.2 s 0).toNat)
        (measurable_of_countable (fun x : Bool => q - 1 + x.toNat) |>.comp
          ((measurable_pi_apply 0).comp ((measurable_pi_apply s).comp
            (measurable_snd.comp measurable_snd)))) _ (measurable_coinShift s)

/-- The event of the capped count after a first step in the direction `a`. -/
def stepEvent (b : Fin 4) (cap q : ℕ) (τ : Fin 3 → Ty) (k : ℕ) (a : Fin 4) : Set LSample :=
  {ω | minE ((if a = b then 1 else 0) +
    cnt b (stepA a q τ ω).1 (stepA a q τ ω).2.1 (stepA a q τ ω).2.2) cap = k}

theorem measurableSet_stepEvent (b : Fin 4) (cap q : ℕ) (τ : Fin 3 → Ty) (k : ℕ) (a : Fin 4) :
    MeasurableSet (stepEvent b cap q τ k a) :=
  (measurable_of_countable (fun x : ℕ∞ => minE ((if a = b then 1 else 0) + x) cap)).comp
    (measurable_stepA_cnt b a q τ) (measurableSet_singleton k)

theorem uniformOn_fin4 (a : Fin 4) : (uniformOn Set.univ : Measure (Fin 4)) {a} = 4⁻¹ := by
  rw [uniformOn_univ]
  simp

/-- The decomposition along the first direction. -/
theorem measure_step (b : Fin 4) (cap q : ℕ) (τ : Fin 3 → Ty) (k : ℕ) (hq : 1 ≤ q) :
    lowMeasure ρ {ω | minE (cnt b q τ ω) cap = k} =
      ∑ a : Fin 4, 4⁻¹ * lowMeasure ρ (stepEvent b cap q τ k a) := by
  set S : Set (Fin 4 × LSample) := ⋃ a, {a} ×ˢ stepEvent b cap q τ k a with hSdef
  have hS : MeasurableSet S :=
    MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod
      (measurableSet_stepEvent b cap q τ k a)
  have hmem : ∀ a ω, (a, ω) ∈ S ↔ ω ∈ stepEvent b cap q τ k a := by
    intro a ω
    simp [hSdef]
  have hset : {ω : LSample | minE (cnt b q τ ω) cap = k} = {ω | (ω.1 0, shiftD ω) ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hmem, stepEvent]
    rw [cnt_step b q τ ω hq]
  have hh : Measurable fun ω : LSample => ω.1 0 := (measurable_pi_apply 0).comp measurable_fst
  have hg : Measurable shiftD :=
    (measurable_pi_iff.mpr fun i => (measurable_pi_apply (i + 1)).comp measurable_fst).prodMk
      measurable_snd
  rw [hset, measure_decomp (lowMeasure ρ) (uniformOn Set.univ) (fun ω => ω.1 0) shiftD hh hg
    (map_dir_shift ρ) S hS, tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [uniformOn_fin4, show {ω : LSample | (a, ω) ∈ S} = stepEvent b cap q τ k a from
    Set.ext (hmem a)]

/-- A direction that is not a child: the closure with one frog less. -/
theorem stepEvent_plain (b : Fin 4) (cap q : ℕ) (hcap : 1 ≤ cap) (τ : Fin 3 → Ty) (k : ℕ)
    (a : Fin 4) (hst : ∀ ω, stepA a q τ ω = (q - 1, τ, ω)) :
    (lowMeasure ρ (stepEvent b cap q τ k a)).toReal =
      if a = b then capShift cap (lawV ρ b cap (q - 1) τ) k else lawV ρ b cap (q - 1) τ k := by
  have hev : stepEvent b cap q τ k a =
      {ω | minE ((if a = b then 1 else 0) + cnt b (q - 1) τ ω) cap = k} := by
    ext ω
    simp [stepEvent, hst]
  rw [hev]
  split_ifs with hab
  · exact measure_capShift (lowMeasure ρ) _ (measurable_cnt b (q - 1) τ) cap hcap k
  · simp [lawV]

/-- A fresh child: one frog less plus its first answer, the child becomes a coin child. -/
theorem stepEvent_fresh (b : Fin 4) (cap q Rmax : ℕ) (τ : Fin 3 → Ty) (k : ℕ) (s : Fin 3)
    (hs : τ s = .fresh) (hb : b ≠ s.succ) (hρ : ∀ r, Rmax < r → ρ {r} = 0) :
    (lowMeasure ρ (stepEvent b cap q τ k s.succ)).toReal =
      ∑ r ∈ Finset.range (Rmax + 1),
        (ρ {r}).toReal * lawV ρ b cap (q - 1 + r) (Function.update τ s .coin) k := by
  set τ' := Function.update τ s Ty.coin with hτ'
  have hτ's : τ' s ≠ .fresh := by simp [hτ']
  set SR : Set (ℕ × LSample) := {p | minE (cnt b (q - 1 + p.1) τ' p.2) cap = k} with hSR
  have hSRm : MeasurableSet SR := by
    have h : Measurable fun p : ℕ × LSample => cnt b (q - 1 + p.1) τ' p.2 :=
      measurable_from_prod_countable_right fun r => measurable_cnt b (q - 1 + r) τ'
    exact (measurable_of_countable (fun x : ℕ∞ => minE x cap)).comp h (measurableSet_singleton k)
  have hinv : ∀ r r' ω, (r, ω) ∈ SR ↔
      (r, ((ω.1, Function.update ω.2.1 s r', ω.2.2) : LSample)) ∈ SR := by
    intro r r' ω
    simp only [hSR, Set.mem_ofPred_eq, cnt, curves_update_R τ' s hτ's ω r']
  have hev : stepEvent b cap q τ k s.succ = {ω | (ω.2.1 s, ω) ∈ SR} := by
    ext ω
    have hb' : (s.succ = b) = False := by simp [Ne.symm hb]
    simp [stepEvent, stepA, hs, hSR, hτ', hb']
  rw [hev, measure_R_decomp ρ s SR hSRm hinv]
  rw [tsum_eq_sum (s := Finset.range (Rmax + 1)) (fun r hr => by
    rw [hρ r (by simpa using hr), zero_mul])]
  rw [ENNReal.toReal_sum (fun r _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ENNReal.toReal_mul]
  rfl

theorem coinLaw_true : coinLaw {true} = 3⁻¹ := by
  simp [coinLaw]

theorem coinLaw_false : coinLaw {false} = 1 - 3⁻¹ := by
  simp [coinLaw]

/-- A coin child: one frog less plus its coin; the coin keeps the pool with probability `1/3`. -/
theorem stepEvent_coin (b : Fin 4) (cap q : ℕ) (hq : 1 ≤ q) (τ : Fin 3 → Ty) (k : ℕ) (s : Fin 3)
    (hs : τ s = .coin) (hb : b ≠ s.succ) :
    (lowMeasure ρ (stepEvent b cap q τ k s.succ)).toReal =
      (1 / 3) * lawV ρ b cap q τ k + (2 / 3) * lawV ρ b cap (q - 1) τ k := by
  set SC : Set (Bool × LSample) := {p | minE (cnt b (q - 1 + p.1.toNat) τ p.2) cap = k} with hSC
  have hSCm : MeasurableSet SC := by
    have h : Measurable fun p : Bool × LSample => cnt b (q - 1 + p.1.toNat) τ p.2 :=
      measurable_from_prod_countable_right fun x => measurable_cnt b (q - 1 + x.toNat) τ
    exact (measurable_of_countable (fun x : ℕ∞ => minE x cap)).comp h (measurableSet_singleton k)
  have hev : stepEvent b cap q τ k s.succ =
      {ω | (ω.2.2 s 0, ((ω.1, ω.2.1, Function.update ω.2.2 s fun i => ω.2.2 s (i + 1)) :
        LSample)) ∈ SC} := by
    ext ω
    have hb' : (s.succ = b) = False := by simp [Ne.symm hb]
    simp [stepEvent, stepA, hs, hSC, hb']
  have hh : Measurable fun ω : LSample => ω.2.2 s 0 :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply s).comp (measurable_snd.comp measurable_snd))
  rw [hev, measure_decomp (lowMeasure ρ) coinLaw (fun ω => ω.2.2 s 0) _ hh
    (measurable_coinShift s) (map_coin_shift ρ s) SC hSCm, tsum_fintype]
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, coinLaw_true, coinLaw_false, hSC, Set.mem_ofPred_eq,
    Bool.toNat_true, Bool.toNat_false, add_zero]
  have hq1 : q - 1 + 1 = q := by omega
  rw [hq1]
  have h3 : (3⁻¹ : ℝ≥0∞) ≠ ⊤ := by simp
  have h3' : (1 - 3⁻¹ : ℝ≥0∞) ≠ ⊤ := by simp
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top h3 (measure_ne_top _ _))
    (ENNReal.mul_ne_top h3' (measure_ne_top _ _)), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.2 (by norm_num)) ENNReal.one_ne_top,
    ENNReal.toReal_inv]
  simp only [lawV, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  ring

/-- **First-step analysis** of the lower closure, for `q ≥ 1` frogs, when the counted direction
`b` is up or a dead child. -/
theorem lawV_step (b : Fin 4) (cap q Rmax : ℕ) (hcap : 1 ≤ cap) (hq : 1 ≤ q) (τ : Fin 3 → Ty)
    (hb : ∀ s, b = s.succ → τ s = .dead) (hρ : ∀ r, Rmax < r → ρ {r} = 0) (k : ℕ) :
    lawV ρ b cap q τ k =
      4⁻¹ * ((if b = 0 then capShift cap (lawV ρ b cap (q - 1) τ) k else lawV ρ b cap (q - 1) τ k) +
        ∑ s : Fin 3, branch ρ b cap q Rmax τ k s) := by
  have hm := measure_step ρ b cap q τ k hq
  have hfin : ∀ a, 4⁻¹ * lowMeasure ρ (stepEvent b cap q τ k a) ≠ ⊤ := fun a =>
    ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  unfold lawV
  rw [hm, ENNReal.toReal_sum fun a _ => hfin a, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  congr 1
  · rw [stepEvent_plain ρ b cap q hcap τ k 0 (fun ω => by simp [stepA])]
    simp only [eq_comm (a := (0 : Fin 4))]
    try rfl
  · refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    unfold branch
    cases h : τ s with
    | dead =>
      rw [stepEvent_plain ρ b cap q hcap τ k s.succ (fun ω => by simp [stepA, h])]
      simp only [eq_comm (a := s.succ)]
      try rfl
    | fresh =>
      exact stepEvent_fresh ρ b cap q Rmax τ k s h (fun hbs => by simp [hb s hbs] at h) hρ
    | coin =>
      exact stepEvent_coin ρ b cap q hq τ k s h (fun hbs => by simp [hb s hbs] at h)

end Step

/-! ## Counting the children by type -/

theorem sum_comp_ty (τ : Fin 3 → Ty) (g : Ty → ℝ) :
    ∑ s, g (τ s) = ((Finset.univ.filter fun s => τ s = .dead).card : ℝ) * g .dead +
      ((Finset.univ.filter fun s => τ s = .fresh).card : ℝ) * g .fresh +
      ((Finset.univ.filter fun s => τ s = .coin).card : ℝ) * g .coin := by
  simp only [Finset.card_filter, Fin.sum_univ_three, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  cases τ 0 <;> cases τ 1 <;> cases τ 2 <;> simp <;> ring

theorem card_ty (τ : Fin 3 → Ty) :
    (Finset.univ.filter fun s => τ s = .dead).card + (Finset.univ.filter fun s => τ s = .fresh).card +
      (Finset.univ.filter fun s => τ s = .coin).card = 3 := by
  simp only [Finset.card_filter, Fin.sum_univ_three]
  cases τ 0 <;> cases τ 1 <;> cases τ 2 <;> simp

theorem card_coin_update (τ : Fin 3 → Ty) (s : Fin 3) (hs : τ s = .fresh) :
    (Finset.univ.filter fun t => Function.update τ s Ty.coin t = .coin).card =
      (Finset.univ.filter fun t => τ t = .coin).card + 1 := by
  simp only [Finset.card_filter, Fin.sum_univ_three]
  fin_cases s <;> simp_all <;> omega

theorem card_dead_eq_one (τ : Fin 3 → Ty) (c : Fin 3) (hc : τ c = .dead)
    (hlive : ∀ s, s ≠ c → τ s ≠ .dead) : (Finset.univ.filter fun s => τ s = .dead).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨c, Finset.ext fun s => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => by_contra fun hsc => hlive s hsc h, fun h => h ▸ hc⟩

theorem card_dead_eq_zero (τ : Fin 3 → Ty) (hlive : ∀ s, τ s ≠ .dead) :
    (Finset.univ.filter fun s => τ s = .dead).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun s _ => hlive s

/-! ## The solutions -/

section Solve

variable (ρ : Measure ℕ) [IsProbabilityMeasure ρ]

/-- The types of the S2 lower closure at stage `f`: the child `c` dead, the two others live, `f` of
them already entered. -/
def ClassS2 (c : Fin 3) (f : ℕ) (τ : Fin 3 → Ty) : Prop :=
  τ c = .dead ∧ (∀ s, s ≠ c → τ s ≠ .dead) ∧ (Finset.univ.filter fun s => τ s = .coin).card = f

/-- The types of the S3 lower closure at stage `f`: three live children, `f` of them entered. -/
def ClassS3 (f : ℕ) (τ : Fin 3 → Ty) : Prop :=
  (∀ s, τ s ≠ .dead) ∧ (Finset.univ.filter fun s => τ s = .coin).card = f

theorem stageLaw_zero (cap : ℕ) (pc pg pn : ℝ) (R : ℕ → ℝ) (Rmax : ℕ) (next : ℕ → ℕ → ℝ)
    (k : ℕ) : stageLaw cap pc pg pn R Rmax next 0 k = if k = 0 then 1 else 0 := rfl

theorem stageLaw_succ (cap : ℕ) (pc pg pn : ℝ) (R : ℕ → ℝ) (Rmax : ℕ) (next : ℕ → ℕ → ℝ)
    (y k : ℕ) : stageLaw cap pc pg pn R Rmax next (y + 1) k =
      pc * capShift cap (stageLaw cap pc pg pn R Rmax next y) k +
        pg * stageLaw cap pc pg pn R Rmax next y k +
        pn * ∑ r ∈ Finset.range (Rmax + 1), R r * next (y + r) k := rfl

/-- One stage of the S2 lower closure: at stage `f ≤ 2`, the law is the stage law with the jump
chain probabilities `(3, 3 + 2f, 3 (2 - f))/(12 - f)`, given the law at stage `f + 1`. -/
theorem lawV_S2_stage (c : Fin 3) (E GM : ℕ) (hE : 1 ≤ E) (R : ℕ → ℝ)
    (hρ0 : ∀ r, GM + 1 < r → ρ {r} = 0) (hρR : ∀ r, (ρ {r}).toReal = R r) (f : ℕ) (hf : f ≤ 2)
    (pc pg pn : ℝ) (hpc : pc * (12 - f) = 3) (hpg : pg * (12 - f) = 3 + 2 * f)
    (hpn : pn * (12 - f) = 3 * (2 - f)) (next : ℕ → ℕ → ℝ)
    (hnext : f < 2 → ∀ τ, ClassS2 c (f + 1) τ → ∀ y k, lawV ρ c.succ E y τ k = next y k)
    (τ : Fin 3 → Ty) (hτ : ClassS2 c f τ) (y k : ℕ) :
    lawV ρ c.succ E y τ k = stageLaw E pc pg pn R (GM + 1) next y k := by
  obtain ⟨hc, hlive, hcoin⟩ := hτ
  induction y generalizing k with
  | zero => rw [lawV_zero, stageLaw_zero]
  | succ y ih =>
    have hb : ∀ s, c.succ = s.succ → τ s = .dead := fun s hs => by
      obtain rfl := Fin.succ_inj.1 hs; exact hc
    have hstep := lawV_step ρ c.succ E (y + 1) (GM + 1) hE (by omega) τ hb hρ0 k
    simp only [Fin.succ_ne_zero, ite_false, Nat.add_sub_cancel] at hstep
    have hP : lawV ρ c.succ E y τ = stageLaw E pc pg pn R (GM + 1) next y := funext ih
    set N := ∑ r ∈ Finset.range (GM + 1 + 1), R r * next (y + r) k with hN
    set L := lawV ρ c.succ E (y + 1) τ k with hL
    set g : Ty → ℝ := fun t => match t with
      | .dead => capShift E (lawV ρ c.succ E y τ) k
      | .fresh => N
      | .coin => 1 / 3 * L + 2 / 3 * lawV ρ c.succ E y τ k with hg
    have hbr : ∑ s, branch ρ c.succ E (y + 1) (GM + 1) τ k s = ∑ s, g (τ s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      unfold branch
      cases h : τ s with
      | dead =>
        have hsc : s = c := by_contra fun hsc => hlive s hsc h
        subst hsc
        simp [hg]
      | fresh =>
        have hsc : s ≠ c := fun hsc => by rw [hsc, hc] at h; exact Ty.noConfusion h
        have hf2 : f < 2 := by
          have h3 := card_ty τ
          have hd := card_dead_eq_one τ c hc hlive
          have hfr : 1 ≤ (Finset.univ.filter fun t => τ t = .fresh).card :=
            Finset.card_pos.2 ⟨s, by simp [h]⟩
          omega
        have hcl : ClassS2 c (f + 1) (Function.update τ s .coin) := by
          refine ⟨by rw [Function.update_of_ne (Ne.symm hsc)]; exact hc, fun t ht => ?_, ?_⟩
          · by_cases hts : t = s
            · subst hts; simp
            · rw [Function.update_of_ne hts]; exact hlive t ht
          · rw [card_coin_update τ s h, hcoin]
        simp only [hg, Nat.add_sub_cancel]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hρR, hnext hf2 _ hcl]
      | coin => simp [hg, hL]
    rw [hbr, sum_comp_ty, card_dead_eq_one τ c hc hlive, hcoin] at hstep
    have hfr : ((Finset.univ.filter fun t => τ t = .fresh).card : ℝ) = 2 - f := by
      have h3 := card_ty τ
      rw [card_dead_eq_one τ c hc hlive, hcoin] at h3
      have : (Finset.univ.filter fun t => τ t = .fresh).card = 2 - f := by omega
      rw [this, Nat.cast_sub hf]
      norm_num
    rw [hfr] at hstep
    simp only [hg] at hstep
    rw [hP] at hstep
    rw [stageLaw_succ, ← hN]
    have hf' : (f : ℝ) ≤ 2 := by exact_mod_cast hf
    have h12 : (12 : ℝ) - f ≠ 0 := by linarith
    -- hstep : L = 4⁻¹ * (S + (1 * C + (2 - f) * N + f * (1/3 * L + 2/3 * S)))
    set S := stageLaw E pc pg pn R (GM + 1) next y k
    set C := capShift E (stageLaw E pc pg pn R (GM + 1) next y) k
    have key : L * (12 - f) = 3 * C + (3 + 2 * f) * S + 3 * (2 - f) * N := by
      push_cast at hstep
      linarith
    have hL' : L * (12 - f) = (pc * C + pg * S + pn * N) * (12 - f) := by
      rw [key]
      linear_combination (-C) * hpc - S * hpg - N * hpn
    exact mul_right_cancel₀ h12 hL'

/-- One stage of the S3 lower closure: at stage `f ≤ 3`, the law is the stage law with the jump
chain probabilities `(3, 2f, 3 (3 - f))/(12 - f)`, given the law at stage `f + 1`. -/
theorem lawV_S3_stage (GM : ℕ) (R : ℕ → ℝ)
    (hρ0 : ∀ r, GM + 1 < r → ρ {r} = 0) (hρR : ∀ r, (ρ {r}).toReal = R r) (f : ℕ) (hf : f ≤ 3)
    (pc pg pn : ℝ) (hpc : pc * (12 - f) = 3) (hpg : pg * (12 - f) = 2 * f)
    (hpn : pn * (12 - f) = 3 * (3 - f)) (next : ℕ → ℕ → ℝ)
    (hnext : f < 3 → ∀ τ, ClassS3 (f + 1) τ → ∀ y k, lawV ρ 0 (GM + 1) y τ k = next y k)
    (τ : Fin 3 → Ty) (hτ : ClassS3 f τ) (y k : ℕ) :
    lawV ρ 0 (GM + 1) y τ k = stageLaw (GM + 1) pc pg pn R (GM + 1) next y k := by
  obtain ⟨hlive, hcoin⟩ := hτ
  induction y generalizing k with
  | zero => rw [lawV_zero, stageLaw_zero]
  | succ y ih =>
    have hb : ∀ s, (0 : Fin 4) = s.succ → τ s = .dead := fun s hs =>
      absurd hs.symm (Fin.succ_ne_zero s)
    have hstep := lawV_step ρ 0 (GM + 1) (y + 1) (GM + 1) (by omega) (by omega) τ hb hρ0 k
    simp only [ite_true, Nat.add_sub_cancel] at hstep
    have hP : lawV ρ 0 (GM + 1) y τ = stageLaw (GM + 1) pc pg pn R (GM + 1) next y := funext ih
    set N := ∑ r ∈ Finset.range (GM + 1 + 1), R r * next (y + r) k with hN
    set L := lawV ρ 0 (GM + 1) (y + 1) τ k with hL
    set g : Ty → ℝ := fun t => match t with
      | .dead => 0
      | .fresh => N
      | .coin => 1 / 3 * L + 2 / 3 * lawV ρ 0 (GM + 1) y τ k with hg
    have hbr : ∑ s, branch ρ 0 (GM + 1) (y + 1) (GM + 1) τ k s = ∑ s, g (τ s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      unfold branch
      cases h : τ s with
      | dead => exact absurd h (hlive s)
      | fresh =>
        have hf3 : f < 3 := by
          have h3 := card_ty τ
          have hd := card_dead_eq_zero τ hlive
          have hfr : 1 ≤ (Finset.univ.filter fun t => τ t = .fresh).card :=
            Finset.card_pos.2 ⟨s, by simp [h]⟩
          omega
        have hcl : ClassS3 (f + 1) (Function.update τ s .coin) := by
          refine ⟨fun t => ?_, ?_⟩
          · by_cases hts : t = s
            · subst hts; simp
            · rw [Function.update_of_ne hts]; exact hlive t
          · rw [card_coin_update τ s h, hcoin]
        simp only [hg, Nat.add_sub_cancel]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hρR, hnext hf3 _ hcl]
      | coin => simp [hg, hL]
    rw [hbr, sum_comp_ty, card_dead_eq_zero τ hlive, hcoin] at hstep
    have hfr : ((Finset.univ.filter fun t => τ t = .fresh).card : ℝ) = 3 - f := by
      have h3 := card_ty τ
      rw [card_dead_eq_zero τ hlive, hcoin] at h3
      have : (Finset.univ.filter fun t => τ t = .fresh).card = 3 - f := by omega
      rw [this, Nat.cast_sub hf]
      norm_num
    rw [hfr] at hstep
    simp only [hg] at hstep
    rw [hP] at hstep
    rw [stageLaw_succ, ← hN]
    have hf' : (f : ℝ) ≤ 3 := by exact_mod_cast hf
    have h12 : (12 : ℝ) - f ≠ 0 := by linarith
    set S := stageLaw (GM + 1) pc pg pn R (GM + 1) next y k
    set C := capShift (GM + 1) (stageLaw (GM + 1) pc pg pn R (GM + 1) next y) k
    have key : L * (12 - f) = 3 * C + 2 * f * S + 3 * (3 - f) * N := by
      push_cast at hstep
      linarith
    have hL' : L * (12 - f) = (pc * C + pg * S + pn * N) * (12 - f) := by
      rw [key]
      linear_combination (-C) * hpc - S * hpg - N * hpn
    exact mul_right_cancel₀ h12 hL'

/-- The types of the S2 lower closure at the start: the child `c` dead, the two others fresh. -/
def tyS2 (c : Fin 3) : Fin 3 → Ty := fun s => if s = c then .dead else .fresh

/-- **The law of the S2 lower closure** (proof of Lemma 12.1 (1) of the paper): the entries into the
dead child, capped at `E`, have the law `lawS2` computed from the pseudo-law of the first answers. -/
theorem lawV_lawS2 (c : Fin 3) (E GM : ℕ) (hE : 1 ≤ E) (F1 : ℕ → ℝ)
    (hρ0 : ∀ r, GM + 1 < r → ρ {r} = 0) (hρR : ∀ r, (ρ {r}).toReal = plR F1 GM r) (q k : ℕ) :
    lawV ρ c.succ E q (tyS2 c) k = lawS2 GM E F1 q k := by
  simp only [lawS2]
  have P2 := lawV_S2_stage ρ c E GM hE (plR F1 GM) hρ0 hρR 2 le_rfl (3 / 10) (7 / 10) 0
    (by norm_num) (by norm_num) (by norm_num) (fun _ _ => 0) (fun h => absurd h (lt_irrefl 2))
  have P1 := lawV_S2_stage ρ c E GM hE (plR F1 GM) hρ0 hρR 1 (by norm_num) (3 / 11) (5 / 11)
    (3 / 11) (by norm_num) (by norm_num) (by norm_num) _ (fun _ τ hτ => P2 τ hτ)
  have P0 := lawV_S2_stage ρ c E GM hE (plR F1 GM) hρ0 hρR 0 (by norm_num) (1 / 4) (1 / 4)
    (1 / 2) (by norm_num) (by norm_num) (by norm_num) _ (fun _ τ hτ => P1 τ hτ)
  refine P0 (tyS2 c) ⟨by simp [tyS2], fun s hs => by simp [tyS2, hs], ?_⟩ q k
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _
  unfold tyS2
  split_ifs <;> simp

/-- **The law of the S3 lower closure** (proof of Lemma 12.1 (2) of the paper): the frogs frozen
above, capped at `GM + 1`, have the law `lawS3`. -/
theorem lawV_lawS3 (GM : ℕ) (F1 : ℕ → ℝ) (hρ0 : ∀ r, GM + 1 < r → ρ {r} = 0)
    (hρR : ∀ r, (ρ {r}).toReal = plR F1 GM r) (q k : ℕ) :
    lawV ρ 0 (GM + 1) q (fun _ => .fresh) k = lawS3 GM F1 q k := by
  simp only [lawS3]
  have P3 := lawV_S3_stage ρ GM (plR F1 GM) hρ0 hρR 3 le_rfl (1 / 3) (2 / 3) 0
    (by norm_num) (by norm_num) (by norm_num) (fun _ _ => 0) (fun h => absurd h (lt_irrefl 3))
  have P2 := lawV_S3_stage ρ GM (plR F1 GM) hρ0 hρR 2 (by norm_num) (3 / 10) (4 / 10) (3 / 10)
    (by norm_num) (by norm_num) (by norm_num) _ (fun _ τ hτ => P3 τ hτ)
  have P1 := lawV_S3_stage ρ GM (plR F1 GM) hρ0 hρR 1 (by norm_num) (3 / 11) (2 / 11) (6 / 11)
    (by norm_num) (by norm_num) (by norm_num) _ (fun _ τ hτ => P2 τ hτ)
  have P0 := lawV_S3_stage ρ GM (plR F1 GM) hρ0 hρR 0 (by norm_num) (1 / 4) 0 (3 / 4)
    (by norm_num) (by norm_num) (by norm_num) _ (fun _ τ hτ => P1 τ hτ)
  refine P0 (fun _ => .fresh) ⟨fun s => by simp, ?_⟩ q k
  simp
end Solve

end FrogModel.D3.LaneC.Lower
