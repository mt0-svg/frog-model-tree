module

public import FrogModel.Engine.Exact
public import FrogModel.Engine.Drive
public import FrogModel.LemmaX.Kill
public import FrogModel.LemmaX.LawDefs

@[expose] public section

/-!
# The root engine: the law of the output (Lemma 6.2 of the paper)

Under i.i.d. inputs (a uniform direction and an independent uniform `u` of law `λ` at each step),
the outputs of the root chain from `start F` have the law `Psi(N)|_J`, `N` the law of the curve of
the child chain from `F` under i.i.d. uniforms: `law_outPsi_start`.

The proof reads the inputs from pools (`FrogModel.Pool`): piece `2 t` gives the direction of step
`t`, piece `2 t + 1` the uniform of step `t`, from the pool of the direction just read
(`driveSel`). The pieces read are i.i.d. (`map_poolSeq_const`), so the inputs are i.i.d.
(`map_pairs_iid`); on the pool space they are `poolDrive D V` with the directions `D` and the
uniforms `V a` of each pool independent (`map_split_pools`), and `outPsi` of `poolDrive D V` is
`psiG` of the child curves, almost surely (`outPsi_start_eq_psiG`, the directions exit infinitely
often).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.Engine

variable {S U : Type*} {d J : ℕ}

/-! ### The inputs read from pools -/

/-- The inputs of the pieces read in the order of `driveSel` are `poolDrive` of the directions
and the uniforms of the pools. -/
theorem pairs_poolSeq_driveSel [MeasurableSpace U]
    (ω : Option (Fin (d + 1)) × ℕ → Fin (d + 1) × U) :
    (fun k => pairInput (FrogModel.Pool.poolSeq driveSel ω (2 * k))
        (FrogModel.Pool.poolSeq driveSel ω (2 * k + 1))) = poolDrive (poolDir ω) (poolUnif ω) := by
  funext t
  obtain ⟨h0, h1⟩ := poolSeq_driveSel ω t
  rw [h0, h1]
  rfl

/-- **I.i.d. inputs from pools.** The inputs `poolDrive D V`, with i.i.d. uniform directions `D`
and independent i.i.d. uniforms `V a` for each direction `a`, are i.i.d. of law
`unifDir d ⊗ λ`. -/
theorem map_poolDrive [MeasurableSpace U] (lam : Measure U) [IsProbabilityMeasure lam] :
    ((Measure.infinitePi fun _ : ℕ => unifDir d).prod
        (Measure.infinitePi fun _ : Fin (d + 1) => Measure.infinitePi fun _ : ℕ => lam)).map
        (fun p => poolDrive p.1 p.2) =
      iidMeasure ((unifDir d).prod lam) := by
  set μ : Measure (Fin (d + 1) × U) := (unifDir d).prod lam
  have hsel : ∀ (k : ℕ) (i : Option (Fin (d + 1))),
      MeasurableSet {y : Fin k → Fin (d + 1) × U | driveSel k y = i} :=
    fun k i => measurableSet_driveSel k i
  have hseq := (FrogModel.Pool.measurable_poolSeq (driveSel (d := d) (U := U)) hsel).1
  have hpairs : Measurable fun (ω : ℕ → Fin (d + 1) × U) (k : ℕ) =>
      pairInput (ω (2 * k)) (ω (2 * k + 1)) :=
    measurable_pi_iff.2 fun k =>
      ((measurable_pi_apply (2 * k)).fst).prodMk (measurable_pi_apply (2 * k + 1)).snd
  have hDV : Measurable fun ω : Option (Fin (d + 1)) × ℕ → Fin (d + 1) × U =>
      (poolDir ω, poolUnif ω) :=
    (measurable_pi_iff.2 fun t => (measurable_pi_apply _).fst).prodMk
      (measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun m => (measurable_pi_apply _).snd)
  have hsplit := map_split_pools (ι := Fin (d + 1)) (unifDir d) lam
  have hpool : (FrogModel.Pool.poolMeasure fun _ : Option (Fin (d + 1)) => μ) =
      Measure.infinitePi fun _ : Option (Fin (d + 1)) × ℕ => μ := rfl
  have hμ : (μ.prod μ).map (Function.uncurry (pairInput (d := d) (U := U))) = μ :=
    map_pair_fst_snd (unifDir d) lam
  calc ((Measure.infinitePi fun _ : ℕ => unifDir d).prod
        (Measure.infinitePi fun _ : Fin (d + 1) => Measure.infinitePi fun _ : ℕ => lam)).map
        (fun p => poolDrive p.1 p.2)
      = ((FrogModel.Pool.poolMeasure fun _ : Option (Fin (d + 1)) => μ).map
          (fun ω => (poolDir ω, poolUnif ω))).map (fun p => poolDrive p.1 p.2) := by
        rw [hpool]; exact congrArg _ hsplit.symm
    _ = (FrogModel.Pool.poolMeasure fun _ : Option (Fin (d + 1)) => μ).map
          (fun ω => poolDrive (poolDir ω) (poolUnif ω)) := by
        rw [Measure.map_map measurable_poolDrive hDV]; rfl
    _ = ((FrogModel.Pool.poolMeasure fun _ : Option (Fin (d + 1)) => μ).map
          (FrogModel.Pool.poolSeq driveSel)).map
          (fun (ω : ℕ → Fin (d + 1) × U) (k : ℕ) => pairInput (ω (2 * k)) (ω (2 * k + 1))) := by
        rw [Measure.map_map hpairs hseq]
        congr 1
        funext ω
        exact (pairs_poolSeq_driveSel ω).symm
    _ = iidMeasure μ := by
        rw [map_poolSeq_const μ driveSel hsel, map_pairs_iid μ pairInput
          (measurable_fst.fst.prodMk measurable_snd.snd), hμ]
        rfl


/-! ### The law of the outputs -/

/-- **The law of the root chain (Lemma 6.2 of the paper).** Under i.i.d. inputs, a uniform
direction and an independent uniform of law `lam` at each step, the outputs of the root chain from
`start F` have the law `Psi(N)|_J`, `N` the law of the curve of the child chain from `F` under
i.i.d. uniforms of law `lam`. -/
theorem law_outPsi_start [MeasurableSpace U] [Countable S] (cstep : S → U → ℕ × S)
    (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (lam : Measure U) [IsProbabilityMeasure lam]
    (F : S) :
    (iidMeasure ((unifDir d).prod lam)).map (fun w => outPsi cstep (start F : RState S d J) w) =
      (FrogModel.Recursion.psiLaw d ((iidMeasure lam).map (chainCurve cstep F))).map
        (FrogModel.LemmaX.firstValues J) := by
  set DM : Measure (ℕ → Fin (d + 1)) := Measure.infinitePi fun _ : ℕ => unifDir d
  set VM : Measure (Fin (d + 1) → ℕ → U) :=
    Measure.infinitePi fun _ : Fin (d + 1) => Measure.infinitePi fun _ : ℕ => lam
  set curves : (Fin (d + 1) → ℕ → U) → Fin d → ℕ → ℕ∞ :=
    fun V c => chainCurve cstep F (V c.succ)
  have hcurves : Measurable curves :=
    measurable_pi_iff.2 fun c => (measurable_chainCurve cstep hc F).comp (measurable_pi_apply _)
  have hfv : Measurable (FrogModel.LemmaX.firstValues J) :=
    measurable_pi_iff.2 fun s => measurable_pi_apply _
  have hpsi := FrogModel.LemmaX.measurable_psiG (d := d)
  -- the inputs are `poolDrive` of independent directions and pools
  rw [← map_poolDrive (d := d) lam, Measure.map_map (measurable_outPsi cstep hc _)
    measurable_poolDrive]
  -- almost surely the directions exit infinitely often, and then `outPsi` is `psiG`
  have hae : ((fun w => outPsi cstep (start F : RState S d J) w) ∘
      fun p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) => poolDrive p.1 p.2) =ᵐ[DM.prod VM]
      (FrogModel.LemmaX.firstValues J ∘ fun x => FrogModel.LemmaX.psiG x.1 x.2) ∘
        fun p => (curves p.2, p.1) := by
    filter_upwards [Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst
      (ae_dirCountN_unbounded d)] with p hp
    funext k
    exact outPsi_start_eq_psiG cstep F p.1 p.2 hp k
  have hm : Measurable fun p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) => (curves p.2, p.1) :=
    (hcurves.comp measurable_snd).prodMk measurable_fst
  rw [Measure.map_congr hae, FrogModel.Recursion.psiLaw,
    Measure.map_map hfv hpsi, ← Measure.map_map (hfv.comp hpsi) hm]
  congr 1
  -- the child curves and the directions are independent, the curves i.i.d. of law `N`
  have hsw : (fun p : (ℕ → Fin (d + 1)) × (Fin (d + 1) → ℕ → U) => (curves p.2, p.1)) =
      Prod.map curves id ∘ Prod.swap := rfl
  rw [hsw, ← Measure.map_map (hcurves.prodMap measurable_id) measurable_swap,
    Measure.prod_swap, ← Measure.map_prod_map _ _ hcurves measurable_id, Measure.map_id]
  congr 1
  exact map_pi_succ (Measure.infinitePi fun _ : ℕ => lam) (chainCurve cstep F)
    (measurable_chainCurve cstep hc F) d

end FrogModel.Engine
