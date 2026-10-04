module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# Measurability of the closure quantities

`ℕ∞` carries the discrete σ-algebra, so a map into `ℕ∞` is measurable as soon as its composition
with the embedding into `ℝ≥0∞` is; infima and suprema of countable families are then measurable
through `ℝ≥0∞`. This gives the measurability of the end `N` of the closure, of the counts at `N`,
and of a curve read at a measurable index.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- A map into `ℕ∞` is measurable when its image in `ℝ≥0∞` is. -/
theorem measurable_of_toENNReal {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℕ∞}
    (h : Measurable fun ω => (g ω : ℝ≥0∞)) : Measurable g := by
  refine measurable_to_countable' fun m => ?_
  have hm := h (measurableSet_singleton (m : ℝ≥0∞))
  convert hm using 1
  ext ω
  simp [ENat.toENNReal_inj]

theorem measurable_dirCount (a : Fin 4) (n : ℕ) :
    Measurable fun D : ℕ → Fin 4 => dirCount D a n := by
  have h : (fun D : ℕ → Fin 4 => dirCount D a n) =
      fun D => ∑ i ∈ Finset.range n, (fun b : Fin 4 => if b = a then 1 else 0) (D i) := by
    funext D
    simp only [dirCount, Finset.card_filter]
  rw [h]
  exact Finset.measurable_sum _ fun i _ =>
    (Measurable.of_discrete (f := fun b : Fin 4 => if b = a then 1 else 0)).comp
      (measurable_pi_apply i)

/-- A family read at a measurable natural index. -/
theorem measurable_comp_nat {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    (g : Ω → ℕ → γ) (hg : ∀ k, Measurable fun ω => g ω k) (f : Ω → ℕ) (hf : Measurable f) :
    Measurable fun ω => g ω (f ω) :=
  (measurable_from_prod_countable_left (f := fun p : Ω × ℕ => g p.1 p.2) hg).comp
    (measurable_id.prodMk hf)

theorem measurable_child (c : Fin 3) (k : ℕ) : Measurable fun x : ClosSample => x.1 c k :=
  (measurable_pi_apply k).comp ((measurable_pi_apply c).comp measurable_fst)

theorem measurable_closT (q n : ℕ) : Measurable fun x : ClosSample => closT q x.1 x.2 n := by
  have h : Measurable fun x : ClosSample => fun c : Fin 3 => x.1 c (dirCount x.2 c.succ n) :=
    measurable_pi_iff.mpr fun c => measurable_comp_nat (fun (x : ClosSample) k => x.1 c k)
      (measurable_child c) (fun x : ClosSample => dirCount x.2 c.succ n)
      ((measurable_dirCount c.succ n).comp measurable_snd)
  exact (Measurable.of_discrete (f := fun v : Fin 3 → ℕ∞ => (q : ℕ∞) + ∑ c, v c)).comp h

/-- The end `N` of the closure is measurable. -/
theorem measurable_closN (q : ℕ) : Measurable fun x : ClosSample => closN q x.1 x.2 := by
  refine measurable_of_toENNReal ?_
  have h : (fun x : ClosSample => ((closN q x.1 x.2 : ℕ∞) : ℝ≥0∞)) = fun x =>
      ⨅ n : ℕ, if q ≤ n ∧ closT q x.1 x.2 n ≤ n then (n : ℝ≥0∞) else ⊤ := by
    funext x
    simp only [closN, ENat.toENNReal_iInf]
    refine iInf_congr fun n => ?_
    split_ifs with hc
    · simp [hc]
    · simp [hc]
  rw [h]
  refine Measurable.iInf fun n => Measurable.ite ?_ measurable_const measurable_const
  have h1 : MeasurableSet {x : ClosSample | closT q x.1 x.2 n ≤ n} :=
    (measurable_closT q n) (MeasurableSet.of_discrete (s := {y : ℕ∞ | y ≤ n}))
  by_cases hq : q ≤ n
  · simpa [hq] using h1
  · simp [hq]

/-- The count of a direction at a measurable time in `ℕ∞`. -/
theorem measurable_countAt {Ω : Type*} [MeasurableSpace Ω] (D : Ω → ℕ → Fin 4)
    (hD : Measurable D) (a : Fin 4) (N : Ω → ℕ∞) (hN : Measurable N) :
    Measurable fun ω => countAt (D ω) a (N ω) := by
  refine measurable_of_toENNReal ?_
  have h : (fun ω => ((countAt (D ω) a (N ω) : ℕ∞) : ℝ≥0∞)) = fun ω =>
      ⨆ n : ℕ, if (n : ℕ∞) ≤ N ω then (dirCount (D ω) a n : ℝ≥0∞) else 0 := by
    funext ω
    simp only [countAt, ENat.toENNReal_iSup]
    refine iSup_congr fun n => ?_
    split_ifs with hc
    · simp [hc]
    · simp [hc]
  rw [h]
  refine Measurable.iSup fun n => Measurable.ite ?_ ?_ measurable_const
  · exact hN (MeasurableSet.of_discrete (s := {y : ℕ∞ | (n : ℕ∞) ≤ y}))
  · exact (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ≥0∞))).comp
      ((measurable_dirCount a n).comp hD)

theorem measurable_countAt_closN (q : ℕ) (a : Fin 4) :
    Measurable fun x : ClosSample => countAt x.2 a (closN q x.1 x.2) :=
  measurable_countAt (fun x : ClosSample => x.2) measurable_snd a _ (measurable_closN q)

theorem measurable_closE (q : ℕ) (c : Fin 3) :
    Measurable fun x : ClosSample => closE q x.1 x.2 c :=
  measurable_countAt_closN q c.succ

theorem measurable_closX (q : ℕ) : Measurable fun x : ClosSample => closX q x.1 x.2 :=
  measurable_countAt_closN q 0

end FrogModel.D3.Iface
