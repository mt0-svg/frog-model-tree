module

public import FrogModel.D3.LaneA.Walk
public import FrogModel.D3.LaneB.Coins
public import FrogModel.Recursion.LawGen

@[expose] public section

/-!
# I.i.d. families of step sequences (d = 3)

Generic facts on products `Measure.infinitePi`: an injective reindexing keeps the i.i.d. law
(`infinitePi_map_comp`); gluing three pieces per index at stopping times keeps it
(`map_glue3`, the strong Markov property `ZeroOne.map_glueAt` twice); events reading disjoint sets
of coordinates are independent (`infinitePi_inter_of_dependsOn`); the number of coordinates of a
finite set falling in a set `H` is binomial (`infinitePi_encard_lt`), and the binomial lower tail
decreases in the number of trials (`binLt_succ_le`, `binLt_anti`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface

/-- An injective reindexing of an i.i.d. family is an i.i.d. family. -/
theorem infinitePi_map_comp {ι α E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (f : α → ι) (hf : Function.Injective f) :
    (Measure.infinitePi fun _ : ι => ν).map (fun ω a => ω (f a)) =
      Measure.infinitePi fun _ : α => ν := by
  exact Measure.map_infinitePi_infinitePi_of_inj hf

/-- Strong Markov property for a family of frogs with three pieces each: frog `i` follows piece
`(i, 0)` up to the stopping time `e0 i`, then piece `(i, 1)` up to its stopping time `e1 i`, then
piece `(i, 2)`; the glued family has the law of an i.i.d. family. -/
theorem map_glue3 {ι α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (ν : Measure α) [IsProbabilityMeasure ν] (e0 e1 : ι → (ℕ → α) → ℕ∞)
    (he0 : ∀ i (a a' : ℕ → α) (k : ℕ), e0 i a = k → (∀ j < k, a j = a' j) → e0 i a' = k)
    (he1 : ∀ i (a a' : ℕ → α) (k : ℕ), e1 i a = k → (∀ j < k, a j = a' j) → e1 i a' = k)
    (hm0 : ∀ i, Measurable (e0 i)) (hm1 : ∀ i, Measurable (e1 i)) :
    (Measure.infinitePi fun _ : ι × ℕ => Measure.infinitePi fun _ : ℕ => ν).map
        (fun ω i => ZeroOne.glueAt (e0 i (ω (i, 0))) (ω (i, 0))
          (ZeroOne.glueAt (e1 i (ω (i, 1))) (ω (i, 1)) (ω (i, 2)))) =
      Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : ℕ => ν := by
  set P := Measure.infinitePi fun _ : ℕ => ν with hP
  set Q := Measure.infinitePi fun _ : ℕ => P with hQ
  let g : ι → (ℕ → ℕ → α) → (ℕ → α) := fun i Z =>
    ZeroOne.glueAt (e0 i (Z 0)) (Z 0) (ZeroOne.glueAt (e1 i (Z 1)) (Z 1) (Z 2))
  have hin : ∀ i, Measurable fun p : (ℕ → α) × (ℕ → α) => ZeroOne.glueAt (e1 i p.1) p.1 p.2 :=
    fun i => ZeroOne.measurable_glueAt (e1 i) (hm1 i)
  have hout : ∀ i, Measurable fun p : (ℕ → α) × (ℕ → α) => ZeroOne.glueAt (e0 i p.1) p.1 p.2 :=
    fun i => ZeroOne.measurable_glueAt (e0 i) (hm0 i)
  have h12 : Measurable fun Z : ℕ → ℕ → α => (Z 1, Z 2) :=
    (measurable_pi_apply 1).prodMk (measurable_pi_apply 2)
  have hinZ : ∀ i, Measurable fun Z : ℕ → ℕ → α => ZeroOne.glueAt (e1 i (Z 1)) (Z 1) (Z 2) :=
    fun i => (hin i).comp h12
  have h0in : ∀ i, Measurable fun Z : ℕ → ℕ → α =>
      (Z 0, ZeroOne.glueAt (e1 i (Z 1)) (Z 1) (Z 2)) :=
    fun i => (measurable_pi_apply 0).prodMk (hinZ i)
  have hg : ∀ i, Measurable (g i) := fun i => (hout i).comp (h0in i)
  have hindep : iIndepFun (fun n (Z : ℕ → ℕ → α) => Z n) Q :=
    iIndepFun_infinitePi (P := fun _ : ℕ => P) (X := fun _ => id) (fun _ => measurable_id)
  have hmarg : ∀ n, Q.map (fun Z : ℕ → ℕ → α => Z n) = P := fun n =>
    Measure.infinitePi_map_eval (fun _ : ℕ => P) n
  have hlaw : ∀ i, Q.map (g i) = P := by
    intro i
    have hj12 : Q.map (fun Z : ℕ → ℕ → α => (Z 1, Z 2)) = P.prod P := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 1).aemeasurable
        (measurable_pi_apply 2).aemeasurable).1 (hindep.indepFun (by norm_num : (1 : ℕ) ≠ 2)),
        hmarg, hmarg]
    have hinlaw : Q.map (fun Z : ℕ → ℕ → α => ZeroOne.glueAt (e1 i (Z 1)) (Z 1) (Z 2)) = P := by
      have hc : (fun Z : ℕ → ℕ → α => ZeroOne.glueAt (e1 i (Z 1)) (Z 1) (Z 2)) =
          (fun p : (ℕ → α) × (ℕ → α) => ZeroOne.glueAt (e1 i p.1) p.1 p.2) ∘
            (fun Z : ℕ → ℕ → α => (Z 1, Z 2)) := rfl
      rw [hc, ← Measure.map_map (hin i) h12, hj12]
      exact ZeroOne.map_glueAt ν (e1 i) (he1 i) (hm1 i)
    have hind0 : IndepFun (fun Z : ℕ → ℕ → α => Z 0)
        (fun Z : ℕ → ℕ → α => ZeroOne.glueAt (e1 i (Z 1)) (Z 1) (Z 2)) Q := by
      have h := (hindep.indepFun_prodMk (fun n => measurable_pi_apply n) 1 2 0 (by norm_num)
        (by norm_num)).symm
      exact h.comp measurable_id (hin i)
    have hj0 : Q.map (fun Z : ℕ → ℕ → α => (Z 0, ZeroOne.glueAt (e1 i (Z 1)) (Z 1) (Z 2))) =
        P.prod P := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
        (hinZ i).aemeasurable).1 hind0, hmarg, hinlaw]
    have hgi : g i = (fun p : (ℕ → α) × (ℕ → α) => ZeroOne.glueAt (e0 i p.1) p.1 p.2) ∘
        (fun Z : ℕ → ℕ → α => (Z 0, ZeroOne.glueAt (e1 i (Z 1)) (Z 1) (Z 2))) := rfl
    rw [hgi, ← Measure.map_map (hout i) (h0in i), hj0]
    exact ZeroOne.map_glueAt ν (e0 i) (he0 i) (hm0 i)
  have hcurry : (Measure.infinitePi fun _ : ι × ℕ => P).map (MeasurableEquiv.curry ι ℕ (ℕ → α)) =
      Measure.infinitePi fun _ : ι => Q :=
    Measure.infinitePi_map_curry (fun (_ : ι) (_ : ℕ) => P)
  have hfun : (fun ω : ι × ℕ → ℕ → α => fun i => ZeroOne.glueAt (e0 i (ω (i, 0))) (ω (i, 0))
        (ZeroOne.glueAt (e1 i (ω (i, 1))) (ω (i, 1)) (ω (i, 2)))) =
      (fun Z : ι → ℕ → ℕ → α => fun i => g i (Z i)) ∘ MeasurableEquiv.curry ι ℕ (ℕ → α) := by
    funext ω i
    rfl
  have hG : Measurable fun Z : ι → ℕ → ℕ → α => fun i => g i (Z i) :=
    measurable_pi_iff.2 fun i => (hg i).comp (measurable_pi_apply i)
  rw [hfun, ← Measure.map_map hG (MeasurableEquiv.measurable _), hcurry,
    Measure.infinitePi_map_pi (fun _ : ι => Q) hg]
  simp_rw [hlaw]

/-- Under a product measure, an event reading only the coordinates outside `T` and an event
reading only the coordinates in `T` are independent. -/
theorem infinitePi_inter_of_dependsOn {ι E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (T : Set ι) (A B : Set (ι → E))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAT : ∀ ω ω' : ι → E, (∀ i, i ∉ T → ω i = ω' i) → ω ∈ A → ω' ∈ A)
    (hBT : ∀ ω ω' : ι → E, (∀ i ∈ T, ω i = ω' i) → ω ∈ B → ω' ∈ B) :
    Measure.infinitePi (fun _ : ι => ν) (A ∩ B) =
      Measure.infinitePi (fun _ : ι => ν) A * Measure.infinitePi (fun _ : ι => ν) B := by
  classical
  set μ := Measure.infinitePi fun _ : ι => ν with hμ
  obtain ⟨x0, -⟩ := MeasureTheory.nonempty_of_measure_ne_zero (μ := ν) (s := Set.univ) (by simp)
  let R : (ι → E) → ({i // i ∉ T} → E) × ({i // i ∈ T} → E) :=
    fun ω => (fun a => ω a.1, fun b => ω b.1)
  have hR : Measurable R :=
    (measurable_pi_iff.2 fun a => measurable_pi_apply _).prodMk
      (measurable_pi_iff.2 fun b => measurable_pi_apply _)
  have hpair : μ.map R = (Measure.infinitePi fun _ : {i // i ∉ T} => ν).prod
      (Measure.infinitePi fun _ : {i // i ∈ T} => ν) :=
    Recursion.map_infinitePi_pair (fun _ : ι => ν) (Subtype.val : {i // i ∉ T} → ι)
      (Subtype.val : {i // i ∈ T} → ι) Subtype.val_injective Subtype.val_injective
      (fun a b h => a.2 (by rw [h]; exact b.2))
  let ext1 : ({i // i ∉ T} → E) → (ι → E) := fun a i => if h : i ∈ T then x0 else a ⟨i, h⟩
  let ext2 : ({i // i ∈ T} → E) → (ι → E) := fun b i => if h : i ∈ T then b ⟨i, h⟩ else x0
  have hext1 : Measurable ext1 := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases h : i ∈ T
    · simp only [ext1, dite_eq_left h]
      exact measurable_const
    · simp only [ext1, dite_eq_right h]
      exact measurable_pi_apply _
  have hext2 : Measurable ext2 := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases h : i ∈ T
    · simp only [ext2, dite_eq_left h]
      exact measurable_pi_apply _
    · simp only [ext2, dite_eq_right h]
      exact measurable_const
  set A' := ext1 ⁻¹' A with hA'
  set B' := ext2 ⁻¹' B with hB'
  have hA'm : MeasurableSet A' := hext1 hA
  have hB'm : MeasurableSet B' := hext2 hB
  have memA : ∀ ω, ω ∈ A ↔ (R ω).1 ∈ A' := fun ω =>
    ⟨hAT ω _ (fun i hi => by simp [ext1, R, hi]), hAT _ ω (fun i hi => by simp [ext1, R, hi])⟩
  have memB : ∀ ω, ω ∈ B ↔ (R ω).2 ∈ B' := fun ω =>
    ⟨hBT ω _ (fun i hi => by simp [ext2, R, hi]), hBT _ ω (fun i hi => by simp [ext2, R, hi])⟩
  have hAB : A ∩ B = R ⁻¹' (A' ×ˢ B') := by
    ext ω
    exact and_congr (memA ω) (memB ω)
  have hAu : A = R ⁻¹' (A' ×ˢ Set.univ) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact memA ω
  have hBu : B = R ⁻¹' (Set.univ ×ˢ B') := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    exact memB ω
  have key : ∀ s : Set (({i // i ∉ T} → E) × ({i // i ∈ T} → E)), MeasurableSet s →
      μ (R ⁻¹' s) = ((Measure.infinitePi fun _ : {i // i ∉ T} => ν).prod
        (Measure.infinitePi fun _ : {i // i ∈ T} => ν)) s := fun s hs => by
    rw [← hpair, Measure.map_apply hR hs]
  rw [hAB, key _ (hA'm.prod hB'm), Measure.prod_prod]
  conv_rhs => rw [hAu, hBu]
  rw [key _ (hA'm.prod MeasurableSet.univ), key _ (MeasurableSet.univ.prod hB'm),
    Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, one_mul]

/-- `P(Bin(0, p) < x + 1) = 1`. -/
theorem binLt_zero_succ (p : ℝ) (x : ℕ) : binLt 0 p (x + 1) = 1 := by
  unfold binLt
  rw [Finset.sum_range_succ']
  simp [binPmf]

/-- Pascal's rule for the binomial lower tail. -/
theorem binLt_succ_succ (n x : ℕ) (p : ℝ) :
    binLt (n + 1) p (x + 1) = p * binLt n p x + (1 - p) * binLt n p (x + 1) := by
  rcases x with _ | v
  · show binCdf (n + 1) p 0 = p * binLt n p 0 + (1 - p) * binCdf n p 0
    rw [(binCdf_succ n 0 p).2]
    simp [binLt]
  · exact (binCdf_succ n v p).1

/-- The number of coordinates of a finite set `S` falling in `H`, as a natural number. -/
theorem encard_inter_eq_card {ι E : Type*} (H : Set E) (S : Finset ι) (ω : ι → E)
    [DecidablePred fun s => ω s ∈ H] :
    ((S : Set ι) ∩ {s | ω s ∈ H}).encard = ((S.filter fun s => ω s ∈ H).card : ℕ∞) := by
  rw [← Set.encard_coe_eq_coe_finsetCard, Finset.coe_filter]
  congr 1

/-- The number of coordinates `s ∈ S` of an i.i.d. family falling in `H` is binomial:
`P(#{s ∈ S : ω s ∈ H} < x) = P(Bin(|S|, ν H) < x)`. -/
theorem infinitePi_encard_lt {ι E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (H : Set E) (hH : MeasurableSet H)
    (S : Finset ι) (x : ℕ) :
    (Measure.infinitePi (fun _ : ι => ν) {ω | ((S : Set ι) ∩ {s | ω s ∈ H}).encard < x}).toReal =
      binLt S.card (ν H).toReal x := by
  classical
  set μ := Measure.infinitePi fun _ : ι => ν with hμ
  have hset : ∀ (T : Finset ι) (y : ℕ),
      {ω : ι → E | ((T : Set ι) ∩ {s | ω s ∈ H}).encard < y} =
        {ω | (T.filter fun s => ω s ∈ H).card < y} := by
    intro T y
    ext ω
    simp only [Set.mem_ofPred_eq, encard_inter_eq_card, Nat.cast_lt]
  have hcoord : ∀ a : ι, MeasurableSet {ω : ι → E | ω a ∈ H} := fun a =>
    measurable_pi_apply a hH
  have hμa : ∀ a, μ {ω | ω a ∈ H} = ν H := by
    intro a
    have h := Measure.infinitePi_map_eval (fun _ : ι => ν) a
    rw [show {ω : ι → E | ω a ∈ H} = (fun ω : ι → E => ω a) ⁻¹' H from rfl,
      ← Measure.map_apply (measurable_pi_apply a) hH, h]
  have hμa' : ∀ a, μ {ω | ω a ∉ H} = 1 - ν H := by
    intro a
    have h := Measure.infinitePi_map_eval (fun _ : ι => ν) a
    rw [show {ω : ι → E | ω a ∉ H} = (fun ω : ι → E => ω a) ⁻¹' Hᶜ from rfl,
      ← Measure.map_apply (measurable_pi_apply a) hH.compl, h, prob_compl_eq_one_sub hH]
  have key : ∀ T : Finset ι, ∀ y : ℕ,
      MeasurableSet {ω : ι → E | (T.filter fun s => ω s ∈ H).card < y} ∧
        (μ {ω : ι → E | (T.filter fun s => ω s ∈ H).card < y}).toReal =
          binLt T.card (ν H).toReal y := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro y
      rcases y with _ | y
      · simp [binLt]
      · simp [binLt_zero_succ]
    | insert a T haT ih =>
      intro y
      rcases y with _ | y
      · simp [binLt]
      have hsplit : {ω : ι → E | ((insert a T).filter fun s => ω s ∈ H).card < y + 1} =
          ({ω | (T.filter fun s => ω s ∈ H).card < y} ∩ {ω | ω a ∈ H}) ∪
            ({ω | (T.filter fun s => ω s ∈ H).card < y + 1} ∩ {ω | ω a ∉ H}) := by
        ext ω
        have hnot : a ∉ T.filter fun s => ω s ∈ H := fun h => haT (Finset.mem_filter.1 h).1
        by_cases h : ω a ∈ H
        · simp only [Finset.filter_insert, h, ite_true, Finset.card_insert_of_notMem hnot,
            Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, not_true_eq_false, and_false,
            or_false, and_true]
          omega
        · simp [Finset.filter_insert, h]
      have hdep : ∀ z : ℕ, ∀ ω ω' : ι → E, (∀ i, i ∉ ({a} : Set ι) → ω i = ω' i) →
          ω ∈ {ω : ι → E | (T.filter fun s => ω s ∈ H).card < z} →
          ω' ∈ {ω : ι → E | (T.filter fun s => ω s ∈ H).card < z} := by
        intro z ω ω' hω hmem
        have hf : (T.filter fun s => ω s ∈ H) = T.filter fun s => ω' s ∈ H := by
          refine Finset.filter_congr fun s hs => ?_
          have hsa : s ∉ ({a} : Set ι) := by
            rintro rfl
            exact haT hs
          rw [hω s hsa]
        simpa only [Set.mem_ofPred_eq, hf] using hmem
      have hA1 := infinitePi_inter_of_dependsOn ν {a} _ _ (ih y).1 (hcoord a) (hdep y)
        (fun ω ω' h hm => by
          simp only [Set.mem_ofPred_eq] at hm ⊢
          rwa [← h a rfl])
      have hA2 := infinitePi_inter_of_dependsOn ν {a} _ _ (ih (y + 1)).1 (hcoord a).compl
        (hdep (y + 1))
        (fun ω ω' h hm hm' => hm (show ω a ∈ H by rw [h a rfl]; exact hm'))
      have hdisj : Disjoint ({ω : ι → E | (T.filter fun s => ω s ∈ H).card < y} ∩
          {ω | ω a ∈ H}) ({ω | (T.filter fun s => ω s ∈ H).card < y + 1} ∩ {ω | ω a ∉ H}) :=
        Set.disjoint_left.2 fun ω h1 h2 => h2.2 h1.2
      refine ⟨?_, ?_⟩
      · rw [hsplit]
        exact ((ih y).1.inter (hcoord a)).union ((ih (y + 1)).1.inter (hcoord a).compl)
      · rw [hsplit, measure_union hdisj ((ih (y + 1)).1.inter (hcoord a).compl)]
        change μ _ = _ at hA1 hA2
        have hcompl : {ω : ι → E | ω a ∈ H}ᶜ = {ω | ω a ∉ H} := rfl
        rw [hcompl] at hA2
        rw [hA1, hA2, hμa, hμa', ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le prob_le_one
            ENNReal.one_ne_top, ENNReal.toReal_one, (ih y).2, (ih (y + 1)).2,
          Finset.card_insert_of_notMem haT, binLt_succ_succ]
        ring
  rw [hset]
  exact (key S x).2

/-- `P(Bin(n + 1, p) < x) ≤ P(Bin(n, p) < x)`. -/
theorem binLt_succ_le (n x : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binLt (n + 1) p x ≤ binLt n p x := by
  have h1p : 0 ≤ 1 - p := by linarith
  have hpmf_nonneg (i : ℕ) : 0 ≤ binPmf n p i := by
    dsimp [binPmf]
    have h_choose : 0 ≤ (n.choose i : ℝ) := by exact mod_cast Nat.zero_le _
    have hp_pow : 0 ≤ p ^ i := pow_nonneg hp0 i
    have h1p_pow : 0 ≤ (1 - p) ^ (n - i) := pow_nonneg h1p (n - i)
    positivity
  have hcdf_nonneg (v : ℕ) : 0 ≤ binCdf n p v := by
    dsimp [binCdf]
    exact Finset.sum_nonneg (fun i _ => hpmf_nonneg i)
  have hcdf_mono (v : ℕ) : binCdf n p v ≤ binCdf n p (v + 1) := by
    have h_eq : binCdf n p (v + 1) = binCdf n p v + binPmf n p (v + 1) := by
      dsimp [binCdf]
      rw [Finset.sum_range_succ]
    rw [h_eq]
    have h := hpmf_nonneg (v + 1)
    nlinarith
  have hcdf_succ_le (v : ℕ) : binCdf (n + 1) p v ≤ binCdf n p v := by
    induction' v with v ih
    · rcases binCdf_succ n 0 p with ⟨_, h_zero⟩
      rw [h_zero]
      have h := hcdf_nonneg 0
      nlinarith
    · rcases binCdf_succ n v p with ⟨h_eq, _⟩
      rw [h_eq]
      have h_mono : binCdf n p v ≤ binCdf n p (v + 1) := hcdf_mono v
      nlinarith
  by_cases hx : x = 0
  · subst x
    simp [binLt]
  · have hx' : ∃ v, x = v + 1 := Nat.exists_eq_succ_of_ne_zero hx
    rcases hx' with ⟨v, rfl⟩
    have h := hcdf_succ_le v
    simpa [binLt, binCdf] using h

theorem binLt_anti {n n' : ℕ} (h : n ≤ n') (x : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binLt n' p x ≤ binLt n p x := by
  induction n', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n' _ ih => exact (binLt_succ_le n' x p hp0 hp1).trans ih

theorem binLt_nonneg (n x : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binLt n p x :=
  Finset.sum_nonneg fun i _ => by
    unfold binPmf
    have : 0 ≤ 1 - p := by linarith
    positivity

end FrogModel.D3.LaneA
