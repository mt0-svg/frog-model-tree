module

public import FrogModel.D3.M1L.Defs
public import FrogModel.Engine.Pools

@[expose] public section

/-!
# The bridge: what M1_L reads from the frog paths is i.i.d.

The first step of the proof of Lemma 13.2 of the paper: the values read are independent. The
frog-path space `fpMeasure` has one pool per frog (pool `some φ`: the steps of the path of `φ`,
with coins that are never read) and one pool of kill coins (`none`), every value of law `valLaw`
and all independent. M1_L reads, at each step, the first unused value of the pool `sel` names
(`Pool.poolSeq`), so a frog's reads are the steps of its own path in order. By
`Engine.map_poolSeq_const` (Pool's `map_readGen_eq` with the pool and fresh coordinates, both
injective along every label sequence) the values read are i.i.d. of law `valLaw`: the law of
anything the rule computes from them is its law on the i.i.d. stream.
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.D3

/-- The law of a kill coin: geometric, `P(n) = 2^-(n+1)`. -/
noncomputable def coinLaw : Measure ℕ := geometricMeasure ⟨1 / 2, by norm_num, by norm_num⟩

instance : IsProbabilityMeasure coinLaw := by unfold coinLaw; infer_instance

/-- The law of a value read: a uniform step and an independent coin. -/
noncomputable def valLaw : Measure Val := (stepLaw 3).prod coinLaw

instance : IsProbabilityMeasure valLaw := by unfold valLaw; infer_instance

/-- The frog-path space: every pool an i.i.d. sequence of law `valLaw`. -/
noncomputable def fpMeasure : Measure (Option Frog × ℕ → Val) :=
  Pool.poolMeasure fun _ => valLaw

/-- Every set of finite value sequences is measurable. -/
theorem measurableSet_finVal {n : ℕ} (A : Set (Fin n → Val)) : MeasurableSet A :=
  (Set.to_countable A).measurableSet

theorem measurableSet_sel (p : Params) (k n : ℕ) (i : Option Frog) :
    MeasurableSet {y : Fin n → Val | sel p k n y = i} :=
  measurableSet_finVal _

/-- The state after the first `n` values of a sequence is the run at time `n`. -/
theorem runFin_eq_run (p : Params) (k : ℕ) (y : ℕ → Val) (n : ℕ) :
    runFin p k (fun j : Fin n => y j) = run p k y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runFin, run, FrogModel.Engine.traj] at ih ⊢
    rw [List.ofFn_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]

theorem sel_eq_req (p : Params) (k : ℕ) (y : ℕ → Val) (n : ℕ) :
    sel p k n (fun j : Fin n => y j) = req (run p k y n) := by
  rw [sel, runFin_eq_run]

/-- The `n`-th value read from the pools: the first unused value of the pool of `req`. -/
theorem poolSeq_apply (p : Params) (k : ℕ) (ω : Option Frog × ℕ → Val) (n : ℕ) :
    Pool.poolSeq (sel p k) ω n =
      ω (req (run p k (Pool.poolSeq (sel p k) ω) n),
        ((Finset.range n).filter fun j => req (run p k (Pool.poolSeq (sel p k) ω) j) =
          req (run p k (Pool.poolSeq (sel p k) ω) n)).card) := by
  set y := Pool.poolSeq (sel p k) ω
  have hpre : ∀ j, Pool.poolRead (sel p k) ω j = fun i : Fin j => y i := fun j =>
    (Pool.prefix_poolSeq (sel p k) ω j).symm
  have h1 : y n = Pool.poolRead (sel p k) ω (n + 1) (Fin.last n) := rfl
  rw [h1, Pool.poolRead, Fin.snoc_last, hpre n, sel_eq_req]
  congr 2
  refine Finset.card_bij (fun (j : Fin n) _ => (j : ℕ)) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_filter, Finset.mem_range, j.isLt, true_and]
    rw [← sel_eq_req, ← hj]
    rfl
  · intro a _ b _ h
    exact Fin.ext h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show sel p k j (fun i : Fin j => y i) = _
    rw [sel_eq_req]
    exact hj.2

/-- **The bridge.** The values M1_L reads from the frog paths are i.i.d. of law `valLaw`. -/
theorem map_fp_read (p : Params) (k : ℕ) :
    fpMeasure.map (Pool.poolSeq (sel p k)) = FrogModel.Engine.iidMeasure valLaw :=
  FrogModel.Engine.map_poolSeq_const valLaw (sel p k) (measurableSet_sel p k)

/-- The law under the frog paths of any function of the values read is its law on the i.i.d.
stream. -/
theorem map_fp_comp {β : Type*} [MeasurableSpace β] (p : Params) (k : ℕ) (F : (ℕ → Val) → β)
    (hF : Measurable F) :
    fpMeasure.map (fun ω => F (Pool.poolSeq (sel p k) ω)) =
      (FrogModel.Engine.iidMeasure valLaw).map F := by
  rw [← map_fp_read p k, Measure.map_map hF
    (Pool.measurable_poolSeq (sel p k) (measurableSet_sel p k)).1]
  rfl

end FrogModel.D3
