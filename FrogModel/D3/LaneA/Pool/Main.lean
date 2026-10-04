module

public import FrogModel.D3.LaneA.Pool.Law
public import FrogModel.D3.LaneA.Meas

@[expose] public section

/-!
# The pool argument, `curveLaw_succ` (d = 3)

The proof of Lemma 10.1 of the paper. The glued planted paths have the law `pathMeasure`
(`map_plantedPaths`); their planted and presence curves at height `m + 1` are, almost surely, the
parent and presence curves of the closure fed with the child curves `childP m ω` and the
directions `dirP m ω` (`plantedG_eq_closX`, `presN_eq_closN`, every direction occurs infinitely
often: `ae_dirP_infinite`); and these have the law `closMeasure (curveLaw m)`
(`map_childP_dirP`). Hence `curveLaw_succ_proof`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA.Pool

open FrogModel FrogModel.D3.Iface
open FrogModel.Recursion (StarSeg dirSeg dirTail thinS)

/-! ### The law of the child curves and the directions -/

/-- The copy curves are measurable. -/
theorem measurable_copyCurvesP (m : ℕ) :
    Measurable fun q : ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
      (Fin 3 × ℕ → ℕ → Step 3) => copyCurvesP m q.1 q.2 := by
  refine measurable_pi_iff.2 fun c => (measurable_plantedCurve m).comp ?_
  refine measurable_pi_iff.2 fun φ => ?_
  cases φ with
  | inl i => exact (measurable_pi_apply (c, i)).comp measurable_snd
  | inr v => exact (measurable_pi_apply _).comp measurable_fst

/-- The copy curves and the directions. -/
theorem map_copyCurvesP (m : ℕ) :
    (((Measure.infinitePi fun _ : {u : StarSeg 3 // isParamP u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw 3).prod (Recursion.dirMeasure 3)).prod
        (Measure.infinitePi fun _ : Fin 3 × ℕ => Measure.infinitePi fun _ : ℕ => stepLaw 3)).map
        (fun q => (copyCurvesP m q.1.1 q.2, q.1.2)) =
      (Measure.pi fun _ : Fin 3 => curveLaw m).prod (Recursion.dirMeasure 3) := by
  set P := Measure.infinitePi fun _ : {u : StarSeg 3 // isParamP u} =>
    Measure.infinitePi fun _ : ℕ => stepLaw 3 with hP
  set V := Measure.infinitePi fun _ : Fin 3 × ℕ => Measure.infinitePi fun _ : ℕ => stepLaw 3
    with hV
  have hcc := measurable_copyCurvesP m
  have e1 := (measurePreserving_prodAssoc P (Recursion.dirMeasure 3) V).map_eq
  have e2 : (P.prod ((Recursion.dirMeasure 3).prod V)).map (Prod.map id Prod.swap) =
      P.prod (V.prod (Recursion.dirMeasure 3)) := by
    rw [← Measure.map_prod_map _ _ measurable_id measurable_swap, Measure.map_id,
      Measure.prod_swap]
  have e3 := (measurePreserving_prodAssoc P V (Recursion.dirMeasure 3)).symm.map_eq
  have e4 : ((P.prod V).prod (Recursion.dirMeasure 3)).map
      (Prod.map (fun q => copyCurvesP m q.1 q.2) id) =
      (Measure.pi fun _ : Fin 3 => curveLaw m).prod (Recursion.dirMeasure 3) := by
    rw [← Measure.map_prod_map _ _ hcc measurable_id, map_copyCurvesP_pi, Measure.map_id]
  have hfun : (fun q : (({u : StarSeg 3 // isParamP u} → ℕ → Step 3) × (ℕ → Fin (3 + 1))) ×
      (Fin 3 × ℕ → ℕ → Step 3) => (copyCurvesP m q.1.1 q.2, q.1.2)) =
      Prod.map (fun q => copyCurvesP m q.1 q.2) id ∘
        (MeasurableEquiv.prodAssoc (α := {u : StarSeg 3 // isParamP u} → ℕ → Step 3)
          (β := Fin 3 × ℕ → ℕ → Step 3) (γ := ℕ → Fin (3 + 1))).symm ∘
        Prod.map id Prod.swap ∘
        (MeasurableEquiv.prodAssoc (α := {u : StarSeg 3 // isParamP u} → ℕ → Step 3)
          (β := ℕ → Fin (3 + 1)) (γ := Fin 3 × ℕ → ℕ → Step 3)) := by
    funext q
    rfl
  have m1 := (MeasurableEquiv.prodAssoc (α := {u : StarSeg 3 // isParamP u} → ℕ → Step 3)
    (β := ℕ → Fin (3 + 1)) (γ := Fin 3 × ℕ → ℕ → Step 3)).measurable
  have m2 : Measurable (Prod.map id Prod.swap : ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
      ((ℕ → Fin (3 + 1)) × (Fin 3 × ℕ → ℕ → Step 3)) → _) :=
    measurable_id.prodMap measurable_swap
  have m3 := (MeasurableEquiv.prodAssoc (α := {u : StarSeg 3 // isParamP u} → ℕ → Step 3)
    (β := Fin 3 × ℕ → ℕ → Step 3) (γ := ℕ → Fin (3 + 1))).symm.measurable
  have m4 : Measurable (Prod.map (fun q : ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
      (Fin 3 × ℕ → ℕ → Step 3) => copyCurvesP m q.1 q.2) (id : (ℕ → Fin (3 + 1)) → _)) :=
    hcc.prodMap measurable_id
  rw [hfun, ← Measure.map_map m4 (m3.comp (m2.comp m1)), ← Measure.map_map m3 (m2.comp m1),
    ← Measure.map_map m2 m1, e1, e2, e3, e4]

/-- The child curves and the directions through the parameter and the pieces read. -/
theorem childP_dirP_eq (m : ℕ) (ω : StarSeg 3 → ℕ → Step 3) :
    (childP m ω, dirP m ω) =
      (copyCurvesP m (paramOfP ω) (thinS (dirTail (readP m ω)).1 (dirTail (readP m ω)).2),
        (dirTail (readP m ω)).1) := by
  refine Prod.ext ?_ rfl
  funext c
  simp only [childP, copyCurvesP]
  congr 1

/-- **The law of the child curves and the directions.** -/
theorem map_childP_dirP (m : ℕ) :
    (Recursion.pieceMeasure 3).map (fun ω => (childP m ω, dirP m ω)) =
      (Measure.pi fun _ : Fin 3 => curveLaw m).prod (Recursion.dirMeasure 3) := by
  have hdt0 : Measurable (dirTail (d := 3)) := by unfold dirTail; fun_prop
  have hread : Measurable fun ω : StarSeg 3 → ℕ → Step 3 => (paramOfP ω, readP m ω) :=
    (measurable_pi_iff.2 fun u => measurable_pi_apply _).prodMk (measurable_readP m)
  have hdt : Measurable fun q : ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
      (ℕ → ℕ → Step 3) => (q.1, dirTail q.2) := measurable_fst.prodMk (hdt0.comp measurable_snd)
  have hassoc : Measurable fun q : ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
      ((ℕ → Fin (3 + 1)) × (ℕ → ℕ → Step 3)) => ((q.1, q.2.1), q.2.2) := by fun_prop
  have hthin : Measurable fun q : (({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
      (ℕ → Fin (3 + 1))) × (ℕ → ℕ → Step 3) => (q.1, thinS q.1.2 q.2) :=
    measurable_fst.prodMk (Recursion.measurable_thinS.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hΦ : Measurable fun q : (({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
      (ℕ → Fin (3 + 1))) × (Fin 3 × ℕ → ℕ → Step 3) => (copyCurvesP m q.1.1 q.2, q.1.2) :=
    ((measurable_copyCurvesP m).comp ((measurable_fst.comp measurable_fst).prodMk
      measurable_snd)).prodMk (measurable_snd.comp measurable_fst)
  have hfun : (fun ω => (childP m ω, dirP m ω)) =
      (fun q : (({u : StarSeg 3 // isParamP u} → ℕ → Step 3) × (ℕ → Fin (3 + 1))) ×
        (Fin 3 × ℕ → ℕ → Step 3) => (copyCurvesP m q.1.1 q.2, q.1.2)) ∘
      (fun q : (({u : StarSeg 3 // isParamP u} → ℕ → Step 3) × (ℕ → Fin (3 + 1))) ×
        (ℕ → ℕ → Step 3) => (q.1, thinS q.1.2 q.2)) ∘
      (fun q : ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) ×
        ((ℕ → Fin (3 + 1)) × (ℕ → ℕ → Step 3)) => ((q.1, q.2.1), q.2.2)) ∘
      (fun q : ({u : StarSeg 3 // isParamP u} → ℕ → Step 3) × (ℕ → ℕ → Step 3) =>
        (q.1, dirTail q.2)) ∘
      (fun ω => (paramOfP ω, readP m ω)) := by
    funext ω
    exact childP_dirP_eq m ω
  have h2 : ((Measure.infinitePi fun _ : {u : StarSeg 3 // isParamP u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw 3).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw 3)).map
        (fun q => (q.1, dirTail q.2)) =
      (Measure.infinitePi fun _ : {u : StarSeg 3 // isParamP u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw 3).prod ((Recursion.dirMeasure 3).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw 3)) := by
    rw [← Recursion.map_dirTail, ← Measure.map_id (μ := Measure.infinitePi fun _ :
      {u : StarSeg 3 // isParamP u} => Measure.infinitePi fun _ : ℕ => stepLaw 3),
      Measure.map_prod_map _ _ measurable_id hdt0, Measure.map_id]
    rfl
  have h3 := (MeasureTheory.measurePreserving_prodAssoc (Measure.infinitePi fun _ :
    {u : StarSeg 3 // isParamP u} => Measure.infinitePi fun _ : ℕ => stepLaw 3)
    (Recursion.dirMeasure 3)
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw 3)).symm.map_eq
  rw [hfun, ← Measure.map_map hΦ (hthin.comp (hassoc.comp (hdt.comp hread))),
    ← Measure.map_map hthin (hassoc.comp (hdt.comp hread)),
    ← Measure.map_map hassoc (hdt.comp hread), ← Measure.map_map hdt hread, map_readP, h2]
  erw [h3]
  rw [Recursion.map_thinS, map_copyCurvesP]

/-- The child curves and the directions are measurable in the pieces. -/
theorem measurable_childP_dirP (m : ℕ) :
    Measurable fun ω : StarSeg 3 → ℕ → Step 3 => (childP m ω, dirP m ω) := by
  have hdt0 : Measurable (dirTail (d := 3)) := by unfold dirTail; fun_prop
  have hfun : (fun ω : StarSeg 3 → ℕ → Step 3 => (childP m ω, dirP m ω)) = fun ω =>
      (copyCurvesP m (paramOfP ω) (thinS (dirTail (readP m ω)).1 (dirTail (readP m ω)).2),
        (dirTail (readP m ω)).1) := funext (childP_dirP_eq m)
  rw [hfun]
  have hY : Measurable fun ω : StarSeg 3 → ℕ → Step 3 => dirTail (readP m ω) :=
    hdt0.comp (measurable_readP m)
  have hT : Measurable fun ω : StarSeg 3 → ℕ → Step 3 =>
      thinS (dirTail (readP m ω)).1 (dirTail (readP m ω)).2 := Recursion.measurable_thinS.comp hY
  have hp : Measurable fun ω : StarSeg 3 → ℕ → Step 3 => paramOfP ω :=
    measurable_pi_iff.2 fun u => measurable_pi_apply _
  exact ((measurable_copyCurvesP m).comp (hp.prodMk hT)).prodMk hY.fst

/-- Infinitely many root steps go up, almost surely. -/
theorem ae_dirP_infinite (m : ℕ) :
    ∀ᵐ ω ∂(Recursion.pieceMeasure 3), {k | dirP m ω k = 0}.Infinite := by
  have hs : ((Measure.pi fun _ : Fin 3 => curveLaw m).prod (Recursion.dirMeasure 3)).map
      Prod.snd = Recursion.dirMeasure 3 := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hae : ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => curveLaw m).prod (Recursion.dirMeasure 3)),
      {k | x.2 k = 0}.Infinite := by
    refine ae_of_ae_map (p := fun D : ℕ → Fin (3 + 1) => {k | D k = 0}.Infinite)
      measurable_snd.aemeasurable ?_
    rw [hs]
    unfold Recursion.dirMeasure
    filter_upwards [Recursion.ae_infinite_eq (A := Fin (3 + 1))] with D hD
    exact hD 0
  rw [← map_childP_dirP m] at hae
  exact ae_of_ae_map (p := fun x : (Fin 3 → ℕ → ℕ∞) × (ℕ → Fin (3 + 1)) =>
    {k | x.2 k = 0}.Infinite) (measurable_childP_dirP m).aemeasurable hae

/-! ### `curveLaw_succ` -/

theorem presN_zero (M : ℕ) (π : PFrog → ℕ → Step 3) : presN M 0 π = 0 :=
  Set.encard_eq_zero.2 (Set.eq_empty_of_forall_notMem fun _ hp => not_woken_zero hp.1)

/-- **`curveLaw_succ`** (Lemma 10.1): the planted and presence curves at height `m + 1` have the
joint law of the parent and presence curves of the closure with i.i.d. children of law
`curveLaw m`. -/
theorem curveLaw_succ_proof : curveLaw_succ := by
  intro m
  have hF : Measurable fun π : PFrog → ℕ → Step 3 =>
      (plantedCurve (m + 1) π, presCurve (m + 1) π) := measurable_plantedPair_proof (m + 1)
  have hC : Measurable fun x : ClosSample => (closCurve x.1 x.2, closNCurve x.1 x.2) :=
    measurable_closPair_proof
  have hcl : closMeasure (curveLaw m) =
      (Measure.pi fun _ : Fin 3 => curveLaw m).prod (Recursion.dirMeasure 3) := rfl
  rw [← map_plantedPaths, Measure.map_map hF measurable_plantedPaths, hcl, ← map_childP_dirP m,
    Measure.map_map hC (measurable_childP_dirP m)]
  apply Measure.map_congr
  filter_upwards [ae_dirP_infinite m] with ω hω
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · show plantedG (m + 1) j (plantedPaths ω) = closCurve (childP m ω) (dirP m ω) j
    unfold closCurve
    split_ifs with hj
    · subst hj
      exact plantedG_zero _ _
    · exact plantedG_eq_closX m ω hω (by omega)
  · show presN (m + 1) j (plantedPaths ω) = closNCurve (childP m ω) (dirP m ω) j
    unfold closNCurve
    split_ifs with hj
    · subst hj
      exact presN_zero _ _
    · exact presN_eq_closN m ω (by omega)

end FrogModel.D3.LaneA.Pool
