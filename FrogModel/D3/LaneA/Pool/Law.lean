module

public import FrogModel.D3.LaneA.Pool.Copy
public import FrogModel.D3.LaneA.Pool.Bridge

@[expose] public section

/-!
# The pool argument, the law of the closure (d = 3)

The pieces `ω : StarSeg 3 → ℕ → Step 3` are i.i.d. (`Recursion.pieceMeasure 3`), and the planted
paths glued from them have the law `pathMeasure` (`map_plantedPaths`). The root segments of the
planted model of height `m + 1` are processed in the order `procP m ω` (Recursion/Process.lean),
`dirP m ω` are the directions of the root steps, `entryP m ω c` the entries into the child `c` in
order, and `childP m ω c` the planted curve of the copy below `c` fed with these entries
(Copy.lean).

- Pathwise (`plantedG_eq_closX`, `presN_eq_closN`): when infinitely many root steps go up,
  `G_(m+1)(j)` and `N_(m+1)(j)` of the glued paths are the `X` and the `N` of the closure with
  `j + 1` initial frogs, child curves `childP m ω` and directions `dirP m ω`.
- Adapted reading (`map_readP`): the root segment processed at step `k` depends only on the
  parameter (the segments `0` of the frogs below `w`, `isParamP`) and on the pieces read before
  (`procP_congr`), so the parameter and the pieces read are independent i.i.d. families. The
  directions and the shifted pieces are independent (`Recursion.map_dirTail`), the entries into
  each child are an injective reindexing (`Recursion.map_thinS`), and the copies are independent
  with law `curveLaw m` (`map_copyCurvesP_pi`). Hence `map_childP_dirP`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA.Pool

open FrogModel FrogModel.D3.Iface
open FrogModel.Recursion (StarSeg starStart isRootSeg subSeg dirSeg starPieces segStart segPiece
  gluePath subClosure entrySet dirTail thinS served)

/-! ### Definitions -/

/-- The root segments of the planted model of height `m + 1`, in processing order. -/
noncomputable def procP (m : ℕ) (ω : StarSeg 3 → ℕ → Step 3) : ℕ → StarSeg 3 :=
  Recursion.proc initP (dirSeg ω) (outP (m + 1) ω)

/-- The directions of the root steps. -/
noncomputable def dirP (m : ℕ) (ω : StarSeg 3 → ℕ → Step 3) : ℕ → Fin 4 :=
  fun k => dirSeg ω (procP m ω k)

/-- The `i`-th entry into the child `c`. -/
noncomputable def entryP (m : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3) : ℕ → StarSeg 3 :=
  fun i => procP m ω (Nat.nth (fun k => dirP m ω k = c.succ) i)

/-- The child curves: the planted curves of the copies below the children. -/
noncomputable def childP (m : ℕ) (ω : StarSeg 3 → ℕ → Step 3) : Fin 3 → ℕ → ℕ∞ :=
  fun c => plantedCurve m (copyPaths ω c (entryP m ω c))

/-- The parameter segments: the segments `0` of the frogs below `w`. -/
def isParamP (x : StarSeg 3) : Prop := ∃ v : Vertex 3, v ≠ [] ∧ x = (Sum.inl v, 0)

/-- The parameter: the pieces of the parameter segments. -/
def paramOfP (ω : StarSeg 3 → ℕ → Step 3) : {u : StarSeg 3 // isParamP u} → ℕ → Step 3 :=
  fun u => ω u

/-- The pieces read at the root steps. -/
noncomputable def readP (m : ℕ) (ω : StarSeg 3 → ℕ → Step 3) : ℕ → ℕ → Step 3 :=
  fun k => ω (procP m ω k)

/-- The paths of the copy below `c` from the parameter and the thinned pieces. -/
def copyPathsP (p : {u : StarSeg 3 // isParamP u} → ℕ → Step 3) (V : Fin 3 × ℕ → ℕ → Step 3)
    (c : Fin 3) : PFrog → ℕ → Step 3
  | Sum.inl i => V (c, i)
  | Sum.inr v => p ⟨(Sum.inl (v ++ [c]), 0), v ++ [c], by simp, rfl⟩

/-- The copy curves from the parameter and the thinned pieces. -/
noncomputable def copyCurvesP (m : ℕ) (p : {u : StarSeg 3 // isParamP u} → ℕ → Step 3)
    (V : Fin 3 × ℕ → ℕ → Step 3) : Fin 3 → ℕ → ℕ∞ :=
  fun c => plantedCurve m (copyPathsP p V c)

/-! ### The gluing -/

/-- **The planted paths glued from i.i.d. pieces have the law of the frog paths.** -/
theorem map_plantedPaths : (Recursion.pieceMeasure 3).map plantedPaths = pathMeasure := by
  have hsp : Measurable fun ω : StarSeg 3 → ℕ → Step 3 => fun f => starPieces ω f :=
    measurable_pi_iff.2 fun f => measurable_pi_iff.2 fun p =>
      (measurable_pi_apply p.2).comp (measurable_pi_apply (f, p.1))
  have hG : Measurable fun Z : Vertex 3 ⊕ ℕ → ℕ × ℕ → Step 3 =>
      fun f => gluePath (Recursion.frogStart f) (Z f) :=
    measurable_pi_iff.2 fun f =>
      (Recursion.measurable_gluePath (Recursion.frogStart f)).comp (measurable_pi_apply f)
  have hR : Measurable fun Y : Vertex 3 ⊕ ℕ → ℕ → Step 3 => fun φ : PFrog => Y (toStar φ) :=
    measurable_pi_iff.2 fun φ => measurable_pi_apply _
  have h2 : (Measure.infinitePi fun _ : Vertex 3 ⊕ ℕ =>
        Measure.infinitePi fun _ : ℕ × ℕ => stepLaw 3).map
        (fun Z f => gluePath (Recursion.frogStart f) (Z f)) =
      Measure.infinitePi fun _ : Vertex 3 ⊕ ℕ => Measure.infinitePi fun _ : ℕ => stepLaw 3 := by
    rw [Measure.infinitePi_map_pi _ (fun f => Recursion.measurable_gluePath _)]
    congr 1
    funext f
    exact Recursion.map_gluePath _
  have hfun : plantedPaths = (fun Y : Vertex 3 ⊕ ℕ → ℕ → Step 3 => fun φ : PFrog => Y (toStar φ)) ∘
      (fun Z : Vertex 3 ⊕ ℕ → ℕ × ℕ → Step 3 => fun f => gluePath (Recursion.frogStart f) (Z f)) ∘
      (fun ω : StarSeg 3 → ℕ → Step 3 => fun f => starPieces ω f) := rfl
  rw [hfun, ← Measure.map_map hR (hG.comp hsp), ← Measure.map_map hG hsp,
    Recursion.map_starPieces, h2,
    Measure.map_infinitePi_infinitePi_of_inj toStar_injective]
  rfl

theorem measurable_plantedPaths : Measurable plantedPaths := by
  refine measurable_pi_iff.2 fun φ => ?_
  have hZ : Measurable fun ω : StarSeg 3 → ℕ → Step 3 => starPieces ω (toStar φ) :=
    measurable_pi_iff.2 fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply (_, p.1))
  exact (Recursion.measurable_gluePath _).comp hZ

/-! ### The processing -/

section Processing

variable (m : ℕ) (ω : StarSeg 3 → ℕ → Step 3)

theorem isRootSeg_procP (k : ℕ) : isRootSeg (procP m ω k) := by
  rcases Recursion.proc_cases initP (dirSeg ω) (outP (m + 1) ω) k with
    ⟨hmem, -, -⟩ | ⟨-, hproc, -⟩
  · rcases hmem with ⟨a, -, ha⟩ | hmem
    · rw [procP, ← ha]
      exact initP_root a
    · simp only [Set.mem_iUnion] at hmem
      obtain ⟨c, hc⟩ := hmem
      exact hc.1
  · rw [procP, hproc]
    exact initP_root _

theorem not_isParamP_of_root {x : StarSeg 3} (h : isRootSeg x) : ¬ isParamP x := by
  rintro ⟨v, hv, rfl⟩
  have h' : starStart ((Sum.inl v, 0) : StarSeg 3) = some [] := h
  simp [starStart, segStart, Recursion.frogStart] at h'
  exact hv h'

theorem procP_injective : Function.Injective (procP m ω) :=
  Recursion.proc_injective initP (dirSeg ω) (outP (m + 1) ω) initP_injective
    (fun c S a => initP_not_mem_outP (m + 1) ω c S a)

end Processing

/-! ### The pathwise identity -/

section Pathwise

variable (m : ℕ) (ω : StarSeg 3 → ℕ → Step 3)

theorem childP_mono (c : Fin 3) : Monotone (childP m ω c) :=
  monotone_nat_of_le_succ fun k => plantedG_mono m k _

theorem childP_zero (c : Fin 3) : childP m ω c 0 = 0 :=
  plantedG_zero m _

/-- The returns of child `c` after `n` root steps are the child curve at its entry count. -/
theorem childRet_childP (c : Fin 3) (n : ℕ) :
    LemmaX.childRet (shiftC (childP m ω) c) (LemmaX.dirCount (dirP m ω) c.succ n) =
      (outP (m + 1) ω c
        {x | x ∈ served initP (dirSeg ω) (outP (m + 1) ω) n ∧ dirSeg ω x = c.succ}).encard := by
  classical
  set p : ℕ → Prop := fun k => dirP m ω k = c.succ with hp
  set S := {x | x ∈ served initP (dirSeg ω) (outP (m + 1) ω) n ∧ dirSeg ω x = c.succ} with hS
  set M := Nat.count p n with hM
  have hcount : dirCount (dirP m ω) c.succ n = M := by
    rw [hM, Nat.count_eq_card_filter_range]
    rfl
  have hmem : ∀ i < M, ∀ hf : (Set.ofPred p).Finite, i < hf.toFinset.card :=
    fun i hi hf => hi.trans_le (Nat.count_le_card hf n)
  have hSeq : S = entryP m ω c '' {i | i < M} := by
    ext x
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hd⟩
      exact ⟨Nat.count p k, Nat.count_strict_mono hd hk, by
        simp only [entryP]; rw [Nat.nth_count hd]; rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨Nat.nth p i, Nat.nth_lt_of_lt_count hi, rfl⟩, Nat.nth_mem i (hmem i hi)⟩
  have hentry : entrySet ω c S = S := by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      refine ⟨hx, ?_, hx.2⟩
      obtain ⟨⟨k, -, rfl⟩, -⟩ := hx
      exact isRootSeg_procP m ω k
  have heinj : Set.InjOn (entryP m ω c) {i | i < M} := by
    intro i hi j hj h
    have h' := procP_injective m ω h
    rcases (Set.ofPred p).finite_or_infinite with hf | hf
    · exact Nat.nth_injOn hf (hmem i hi hf) (hmem j hj hf) h'
    · exact Nat.nth_injective hf h'
  rw [lx_dirCount_coe, hcount]
  show LemmaX.childRet (fun e => childP m ω c (e - 1)) (M : ℕ∞) = _
  rw [childRet_shift _ (childP_mono m ω c) (childP_zero m ω c),
    encard_outP m ω c S M (entryP m ω c) (hentry.trans hSeq) heinj]
  rfl

/-- **`G_(m+1)(j)` is the `X` of the closure, pathwise.** -/
theorem plantedG_eq_closX (h0 : {k | dirP m ω k = 0}.Infinite) {j : ℕ} (hj : 1 ≤ j) :
    plantedG (m + 1) j (plantedPaths ω) = closX (j + 1) (childP m ω) (dirP m ω) := by
  rw [plantedG_eq_arrSet (m + 1) ω hj, ← psiG_shiftC (j + 1) (childP m ω) (childP_mono m ω)
    (childP_zero m ω)]
  exact (Recursion.psiG_proc_eq initP (dirSeg ω) (outP (m + 1) ω) initP_injective
    (outP_mono (m + 1) ω) (fun c S a => initP_not_mem_outP (m + 1) ω c S a)
    (fun c c' S S' h => outP_disjoint (m + 1) ω c c' S S' h) (shiftC (childP m ω))
    (childRet_childP m ω) h0 (j + 1)).symm

/-- **`N_(m+1)(j)` is the `N` of the closure, pathwise.** -/
theorem presN_eq_closN {j : ℕ} (hj : 1 ≤ j) :
    presN (m + 1) j (plantedPaths ω) = closN (j + 1) (childP m ω) (dirP m ω) := by
  rw [presN_eq_arrSet (m + 1) ω hj, ← psiN_shiftC (j + 1) (childP m ω) (childP_mono m ω)
    (childP_zero m ω)]
  show _ = LemmaX.psiN (shiftC (childP m ω))
    (fun k => dirSeg ω (Recursion.proc initP (dirSeg ω) (outP (m + 1) ω) k)) (j + 1)
  have hmono := outP_mono (m + 1) ω
  have hinit := initP_injective
  have hout := fun c S a => initP_not_mem_outP (m + 1) ω c S a
  have hdisj := fun c c' S S' (h : c ≠ c') => outP_disjoint (m + 1) ω c c' S S' h
  rcases Recursion.released_cases initP (dirSeg ω) (outP (m + 1) ω) (j + 1) with hall | ⟨n, hn, hn'⟩
  · rw [Recursion.psiN_proc_top initP (dirSeg ω) (outP (m + 1) ω) hinit hmono hout hdisj
      (shiftC (childP m ω)) (childRet_childP m ω) hall]
    refine ENat.eq_top_iff_forall_ge.2 fun n => ?_
    rw [← Recursion.encard_served initP (dirSeg ω) (outP (m + 1) ω) hinit hout n]
    exact Set.encard_le_encard (Recursion.served_subset_arrSet initP (dirSeg ω) (outP (m + 1) ω)
      hmono (hall n))
  · rw [Recursion.psiN_proc_eq initP (dirSeg ω) (outP (m + 1) ω) hinit hmono hout hdisj
      (shiftC (childP m ω)) (childRet_childP m ω) hn hn',
      Recursion.arrSet_eq_served initP (dirSeg ω) (outP (m + 1) ω) hmono hn hn',
      Recursion.encard_served initP (dirSeg ω) (outP (m + 1) ω) hinit hout n]

end Pathwise

/-! ### Adapted reading -/

/-- The returns of a child read the pieces of the segments given and of the parameter only. -/
theorem outP_congr (M : ℕ) (ω ω' : StarSeg 3 → ℕ → Step 3) (c : Fin 3)
    (S : Set (StarSeg 3)) (h : ∀ x, x ∈ S ∨ isParamP x → ω' x = ω x) :
    outP M ω' c {x | x ∈ S ∧ dirSeg ω' x = c.succ} =
      outP M ω c {x | x ∈ S ∧ dirSeg ω x = c.succ} := by
  have hdir : ∀ x ∈ S, dirSeg ω' x = dirSeg ω x := fun x hx => by
    simp only [dirSeg, h x (Or.inl hx)]
  have hT : {x | x ∈ S ∧ dirSeg ω' x = c.succ} = {x | x ∈ S ∧ dirSeg ω x = c.succ} := by
    ext x
    constructor
    · rintro ⟨hx, hd⟩
      exact ⟨hx, (hdir x hx).symm.trans hd⟩
    · rintro ⟨hx, hd⟩
      exact ⟨hx, (hdir x hx).trans hd⟩
  rw [hT]
  set T := {x | x ∈ S ∧ dirSeg ω x = c.succ} with hTdef
  have hbase : {x | x ∈ T ∧ isRootSeg x ∧ dirSeg ω' x = c.succ} =
      {x | x ∈ T ∧ isRootSeg x ∧ dirSeg ω x = c.succ} := by
    ext x
    constructor
    · rintro ⟨hx, hr, hd⟩
      exact ⟨hx, hr, (hdir x hx.1).symm.trans hd⟩
    · rintro ⟨hx, hr, hd⟩
      exact ⟨hx, hr, (hdir x hx.1).trans hd⟩
  have hin : ∀ x ∈ subClosure (dirSeg ω) (genP M) ω isRootSeg subSeg c T, ω' x = ω x := by
    intro x hx
    rcases Recursion.subClosure_subset (dirSeg ω) (genP M) ω isRootSeg subSeg c T hx with
      ⟨hxT, -, -⟩ | ⟨w, rfl⟩
    · exact h x (Or.inl hxT.1)
    · exact h _ (Or.inr ⟨w ++ [c], by simp, rfl⟩)
  have hcl : subClosure (dirSeg ω') (genP M) ω' isRootSeg subSeg c T =
      subClosure (dirSeg ω) (genP M) ω isRootSeg subSeg c T := by
    unfold subClosure
    rw [hbase]
    refine Stage.closure_eq_of_agree _ ω ω' _ {x | ω' x ≠ ω x} ?_ ?_
    · intro σ hσ
      simp only [Set.mem_ofPred_eq, not_not] at hσ
      exact hσ.symm
    · rw [Set.disjoint_left]
      intro x hx hxB
      exact hxB (hin x hx)
  unfold outP Recursion.outGen
  rw [hcl]
  ext y
  constructor
  · rintro ⟨hy, x, hx, hg⟩
    exact ⟨hy, x, hx, by rwa [← hin x hx]⟩
  · rintro ⟨hy, x, hx, hg⟩
    exact ⟨hy, x, hx, by rwa [hin x hx]⟩

/-- **Adaptedness.** The segment processed at step `k` depends only on the parameter and on the
pieces processed before. -/
theorem procP_congr (m k : ℕ) (ω ω' : StarSeg 3 → ℕ → Step 3)
    (hpar : ∀ u, isParamP u → ω' u = ω u) (hread : ∀ i < k, ω' (procP m ω i) = ω (procP m ω i)) :
    procP m ω' k = procP m ω k := by
  unfold procP Recursion.proc
  rw [Recursion.procHist_congr initP (dirSeg ω) (dirSeg ω') (outP (m + 1) ω) (outP (m + 1) ω')
    (k + 1) ?_]
  intro j hj c
  apply outP_congr
  rintro x (⟨i, hi, rfl⟩ | hx)
  · exact hread i (by omega)
  · exact hpar x hx

/-- The relation `genP` is measurable in the piece. -/
theorem measurableSet_genP (M : ℕ) (x y : StarSeg 3) :
    MeasurableSet {p : ℕ → Step 3 | genP M x p y} := by
  have hP : ∀ (P : Option (Vertex 3) → Prop) (v : Option (Vertex 3)) (n : ℕ),
      Measurable fun p : ℕ → Step 3 => P (walkStar v p n) :=
    fun P v n => (measurable_of_countable P).comp (LemmaX.measurable_walkStar_apply v n)
  have hret : Measurable fun p : ℕ → Step 3 => retP (starStart x) p :=
    Measurable.exists fun c => measurable_const.and (hP (· = some []) _ c)
  have hseg : ∀ u : Vertex 3, Measurable fun p : ℕ → Step 3 => segVisP (starStart x) p (some u) :=
    fun u => Measurable.exists fun n => (hP (· = some u) _ n).and (Measurable.forall fun i =>
      Measurable.imp measurable_const (Measurable.imp measurable_const
        (hP (· ≠ some []) _ i)))
  refine measurableSet_setOfPred.2 ?_
  unfold genP
  exact (measurable_const.and hret).or (Measurable.exists fun u =>
    measurable_const.and (measurable_const.and (measurable_const.and (hseg u))))

/-- Membership in the returns of a child given a finite list is measurable in the pieces. -/
theorem measurableSet_mem_outP (M : ℕ) (c : Fin 3) (L : List (StarSeg 3)) (y : StarSeg 3) :
    MeasurableSet {ω : StarSeg 3 → ℕ → Step 3 |
      y ∈ outP M ω c {x | x ∈ L ∧ dirSeg ω x = c.succ}} := by
  have hdir : ∀ σ : StarSeg 3, Measurable fun ω : StarSeg 3 → ℕ → Step 3 =>
      dirSeg ω σ = c.succ :=
    fun σ => (measurable_snd.comp ((measurable_pi_apply 0).comp (measurable_pi_apply σ))).eq_const _
  have harc : ∀ σ τ : StarSeg 3, MeasurableSet {p : ℕ → Step 3 | genP M σ p τ ∧ subSeg c τ} :=
    fun σ τ => (measurableSet_genP M σ τ).inter (MeasurableSet.const _)
  have hbase : ∀ σ : StarSeg 3, MeasurableSet {ω : StarSeg 3 → ℕ → Step 3 |
      σ ∈ {x | x ∈ {x | x ∈ L ∧ dirSeg ω x = c.succ} ∧ isRootSeg x ∧ dirSeg ω x = c.succ}} :=
    fun σ => measurableSet_setOfPred.2 ((measurable_const.and (hdir σ)).and
      (measurable_const.and (hdir σ)))
  refine measurableSet_setOfPred.2 ?_
  unfold outP Recursion.outGen
  refine measurable_const.and (Measurable.exists fun x => Measurable.and ?_ ?_)
  · exact measurableSet_setOfPred.1 (Stage.measurableSet_closure
      (fun x p y => genP M x p y ∧ subSeg c y) harc
      (fun ω => {x | x ∈ {x | x ∈ L ∧ dirSeg ω x = c.succ} ∧ isRootSeg x ∧ dirSeg ω x = c.succ})
      hbase x)
  · exact measurableSet_setOfPred.1 ((measurableSet_genP M x y).preimage
      (measurable_pi_apply x))

theorem measurableSet_procP_eq (m k : ℕ) (u : StarSeg 3) :
    MeasurableSet {ω : StarSeg 3 → ℕ → Step 3 | procP m ω k = u} := by
  have hset : {ω : StarSeg 3 → ℕ → Step 3 | procP m ω k = u} =
      ⋃ st : List (StarSeg 3) × ℕ, ⋃ (_ : st.1.getLastD (initP 0) = u),
        {ω | Recursion.procHist initP (dirSeg ω) (outP (m + 1) ω) (k + 1) = st} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨st, hst, h⟩
      rw [← hst, ← h]
      rfl
  rw [hset]
  exact MeasurableSet.iUnion fun st => MeasurableSet.iUnion fun _ =>
    Recursion.measurableSet_procHist_eq initP (fun ω => dirSeg ω) (fun ω => outP (m + 1) ω)
      (fun c L y => measurableSet_mem_outP (m + 1) c L y) (k + 1) st

/-- **Adapted reading.** The parameter and the pieces read are independent i.i.d. families. -/
theorem map_readP (m : ℕ) :
    (Recursion.pieceMeasure 3).map (fun ω => (paramOfP ω, readP m ω)) =
      (Measure.infinitePi fun _ : {u : StarSeg 3 // isParamP u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw 3).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw 3) := by
  unfold Recursion.pieceMeasure paramOfP readP
  exact Recursion.map_adapted (Measure.infinitePi fun _ : ℕ => stepLaw 3) isParamP
    (fun k ω => procP m ω k) (fun k ω => not_isParamP_of_root (isRootSeg_procP m ω k))
    (fun ω => procP_injective m ω) (fun k ω ω' hpar hread => procP_congr m k ω ω' hpar hread)
    (fun k u => measurableSet_procP_eq m k u)

theorem measurable_readP (m : ℕ) :
    Measurable fun ω : StarSeg 3 → ℕ → Step 3 => readP m ω :=
  measurable_pi_iff.2 fun k => Recursion.measurable_read (fun ω => procP m ω k)
    (fun u => measurableSet_procP_eq m k u)

/-! ### The copies -/

theorem measurable_plantedCurve (m : ℕ) : Measurable (plantedCurve m) :=
  measurable_pi_iff.2 fun k => measurable_plantedG m k

/-- **The copies.** The copy curves are i.i.d. with law `curveLaw m`. -/
theorem map_copyCurvesP_pi (m : ℕ) :
    ((Measure.infinitePi fun _ : {u : StarSeg 3 // isParamP u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw 3).prod
        (Measure.infinitePi fun _ : Fin 3 × ℕ => Measure.infinitePi fun _ : ℕ => stepLaw 3)).map
        (fun q => copyCurvesP m q.1 q.2) =
      Measure.pi fun _ : Fin 3 => curveLaw m := by
  set ν := Measure.infinitePi fun _ : ℕ => stepLaw 3 with hν
  set U := {u : StarSeg 3 // isParamP u} ⊕ (Fin 3 × ℕ)
  -- (1) the two families as one i.i.d. family over the sum
  have hsplit := Recursion.map_infinitePi_pair (fun _ : U => ν) Sum.inl Sum.inr
    Sum.inl_injective Sum.inr_injective (fun a b => Sum.inl_ne_inr)
  -- (2) the index of each coordinate of the copies
  let ι : Fin 3 × PFrog → U := fun cφ => match cφ.2 with
    | Sum.inl i => Sum.inr (cφ.1, i)
    | Sum.inr v => Sum.inl ⟨(Sum.inl (v ++ [cφ.1]), 0), v ++ [cφ.1], by simp, rfl⟩
  have hι : Function.Injective ι := by
    rintro ⟨c, i | v⟩ ⟨c', i' | v'⟩ h
    · have h' : (c, i) = (c', i') := Sum.inr_injective h
      simp only [Prod.mk.injEq] at h'
      rw [h'.1, h'.2]
    · simp [ι] at h
    · simp [ι] at h
    · have h' := congrArg Subtype.val (Sum.inl_injective h)
      simp only [Prod.mk.injEq, Sum.inl.injEq, and_true] at h'
      have hc : c = c' := by
        have := congrArg List.getLast? h'
        simpa using this
      subst hc
      rw [List.append_cancel_right h']
  have hcur : Measurable (MeasurableEquiv.curry (Fin 3) PFrog (ℕ → Step 3)) :=
    (MeasurableEquiv.curry (Fin 3) PFrog (ℕ → Step 3)).measurable
  have hre : Measurable fun ω : U → ℕ → Step 3 => fun cφ : Fin 3 × PFrog => ω (ι cφ) :=
    measurable_pi_iff.2 fun cφ => measurable_pi_apply _
  have hpaths : (Measure.infinitePi fun _ : U => ν).map
      ((MeasurableEquiv.curry (Fin 3) PFrog (ℕ → Step 3)) ∘
        fun ω : U → ℕ → Step 3 => fun cφ : Fin 3 × PFrog => ω (ι cφ)) =
      Measure.infinitePi fun _ : Fin 3 => pathMeasure := by
    rw [← Measure.map_map hcur hre, Measure.map_infinitePi_infinitePi_of_inj hι,
      Measure.infinitePi_map_curry (μ := fun _ _ => ν)]
    rfl
  have hPC : Measurable fun z : Fin 3 → PFrog → ℕ → Step 3 => fun c => plantedCurve m (z c) :=
    measurable_pi_iff.2 fun c => (measurable_plantedCurve m).comp (measurable_pi_apply c)
  have hcurves : (Measure.infinitePi fun _ : Fin 3 => pathMeasure).map
      (fun z c => plantedCurve m (z c)) = Measure.infinitePi fun _ : Fin 3 => curveLaw m := by
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_plantedCurve m)]
    rfl
  have hS : Measurable fun ω : U → ℕ → Step 3 =>
      ((fun a => ω (Sum.inl a), fun b => ω (Sum.inr b)) :
        ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) × (Fin 3 × ℕ → ℕ → Step 3)) :=
    (measurable_pi_iff.2 fun a => measurable_pi_apply _).prodMk
      (measurable_pi_iff.2 fun b => measurable_pi_apply _)
  have hcc : Measurable fun q : ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
      (Fin 3 × ℕ → ℕ → Step 3) => copyCurvesP m q.1 q.2 := by
    refine measurable_pi_iff.2 fun c => (measurable_plantedCurve m).comp ?_
    refine measurable_pi_iff.2 fun φ => ?_
    cases φ with
    | inl i => exact (measurable_pi_apply (c, i)).comp measurable_snd
    | inr v => exact (measurable_pi_apply _).comp measurable_fst
  have hfun : (fun q : ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
      (Fin 3 × ℕ → ℕ → Step 3) => copyCurvesP m q.1 q.2) ∘
      (fun ω : U → ℕ → Step 3 =>
        ((fun a => ω (Sum.inl a), fun b => ω (Sum.inr b)) :
          ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) × (Fin 3 × ℕ → ℕ → Step 3))) =
      (fun z : Fin 3 → PFrog → ℕ → Step 3 => fun c => plantedCurve m (z c)) ∘
        ((MeasurableEquiv.curry (Fin 3) PFrog (ℕ → Step 3)) ∘
          fun ω : U → ℕ → Step 3 => fun cφ : Fin 3 × PFrog => ω (ι cφ)) := by
    funext ω c
    simp only [Function.comp, copyCurvesP]
    congr 1
    funext φ
    cases φ <;> rfl
  rw [← hsplit, Measure.map_map hcc hS, hfun, ← Measure.map_map hPC (hcur.comp hre), hpaths,
    hcurves, Measure.infinitePi_eq_pi]

end FrogModel.D3.LaneA.Pool
