module

public import FrogModel.Engine.CandDom

@[expose] public section

/-!
# One step of the dominating chain of `cand`, as a finite sum over the moves

The right sides of the systems of `DomCert` are integrals over one input `ξ = (a, u)` of a
function of the step. The direction `a` is uniform on `Fin 5`: `a = 0` is the exit, which does not
read `u`; `a = c + 1` moves child `c` by `r = cstep (σ c) u` (`rstep_succ`, with `rstepR` the root
step with the move given). Under `lam`, the move of a well-formed child is entry `n` of its row
sequence with probability its weight (`lintegral_childStep`), and the row
sequence is the finite row followed, for `fresh` and `bdry`, by the geometric tail
(`tsum_rowSeq_split`). The dominating chain is a function of the root step (`domNext`).

**`lintegral_candDom`**: for a state with well-formed children,
`∫ F (candDom y ξ) dν = 5⁻¹ F (exit) + Σ_c 5⁻¹ (Σ_(e ∈ finRow (σ c)) e.p F (move e) + tail)`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine

open FrogModel.Cert FrogModel.LemmaX

variable {S U : Type*} {d J : ℕ}

/-- The root step that moves child `c` by `r = (δ, next)`. -/
def rstepR (x : RState S d J) (c : Fin d) (r : ℕ × S) : RState S d J :=
  if h : x.i < J then
    if x.p - 1 + r.1 = 0 then
      ⟨x.i + 1, x.e, 1, Function.update x.σ c r.2, Function.update x.out ⟨x.i, h⟩ x.e⟩
    else ⟨x.i, x.e, x.p - 1 + r.1, Function.update x.σ c r.2, x.out⟩
  else x

/-- The step of the dominating chain from `y` once the root step `x'` is known. -/
def domNext (T T' : ℕ) (keep : RState S d J → Bool) (lump : RState S d J → RState S d J)
    (y : RState S d J × Bool) (x' : RState S d J) : RState S d J × Bool :=
  if y.2 = true ∨ T < y.1.e ∨ J ≤ y.1.i then (x', y.2)
  else if T < x'.e ∨ T' < x'.p then (x', true)
  else if J ≤ x'.i ∨ keep x' = true then (x', false)
  else (lump x', false)

theorem domStep_eq_domNext (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (y : RState S d J × Bool) (ξ : Fin (d + 1) × U) :
    domStep cstep T T' keep lump y ξ = domNext T T' keep lump y (rstep cstep y.1 ξ) := rfl

theorem rstep_succ (cstep : S → U → ℕ × S) (x : RState S d J) (c : Fin d) (u : U) :
    rstep cstep x (c.succ, u) = rstepR x c (cstep (x.σ c) u) := by
  unfold FrogModel.Engine.rstep FrogModel.Engine.rstepR FrogModel.Engine.move
  simp [Fin.succ_ne_zero c]

theorem rstep_zero (cstep : S → U → ℕ × S) (x : RState S d J) (u u' : U) :
    rstep cstep x (0, u) = rstep cstep x (0, u') := by
  unfold rstep
  have hmove : move cstep x (0 : Fin (d + 1)) u = move cstep x (0 : Fin (d + 1)) u' := by
    unfold move
    simp
  rw [hmove]

/-- An integral against a uniform direction times `μ`, direction by direction. -/
theorem lintegral_unifDir_prod [MeasurableSpace U] (μ : Measure U) [SFinite μ]
    (G : Fin (d + 1) × U → ℝ≥0∞) (hG : ∀ a, Measurable fun u => G (a, u)) :
    ∫⁻ ξ, G ξ ∂((unifDir d).prod μ) = ∑ a : Fin (d + 1), (d + 1 : ℝ≥0∞)⁻¹ * ∫⁻ u, G (a, u) ∂μ := by
  have hG_meas : Measurable G :=
    measurable_from_prod_countable_right hG
  rw [lintegral_prod_symm' G hG_meas]
  have h_inner (u : U) : ∫⁻ a, G (a, u) ∂(FrogModel.Engine.unifDir d) =
      ∑ a : Fin (d + 1), G (a, u) * ((d + 1 : ℝ≥0∞)⁻¹) := by
    rw [lintegral_fintype]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [FrogModel.Engine.unifDir, ProbabilityTheory.uniformOn_univ]
    simp [Measure.count_apply, Fintype.card_fin]
  simp_rw [h_inner]
  have h_factor (y : U) : (∑ a : Fin (d + 1), G (a, y) * ((d + 1 : ℝ≥0∞)⁻¹)) =
      ((d + 1 : ℝ≥0∞)⁻¹) * (∑ a : Fin (d + 1), G (a, y)) := by
    calc
      (∑ a : Fin (d + 1), G (a, y) * ((d + 1 : ℝ≥0∞)⁻¹))
          = (∑ a : Fin (d + 1), G (a, y)) * ((d + 1 : ℝ≥0∞)⁻¹) := by rw [Finset.sum_mul]
      _ = ((d + 1 : ℝ≥0∞)⁻¹) * (∑ a : Fin (d + 1), G (a, y)) := by rw [mul_comm]
  simp_rw [h_factor]
  have h_sum_meas : Measurable (fun (y : U) => ∑ a : Fin (d + 1), G (a, y)) := by
    refine Finset.measurable_sum _ (fun a ha => hG a)
  rw [lintegral_const_mul ((d + 1 : ℝ≥0∞)⁻¹) h_sum_meas]
  rw [lintegral_finsetSum (Finset.univ : Finset (Fin (d + 1))) (fun a ha => hG a)]
  simp [Finset.mul_sum]

/-- A geometric series of nonnegative reals, in `ℝ≥0∞`. -/
theorem tsum_ofReal_geom (a r : ℝ) (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' k : ℕ, ENNReal.ofReal (a * r ^ k) = ENNReal.ofReal (a / (1 - r)) := by
  have hpos : 0 < 1 - r := by linarith
  calc
    ∑' k : ℕ, ENNReal.ofReal (a * r ^ k) = ∑' k : ℕ, (ENNReal.ofReal a * ENNReal.ofReal (r ^ k)) := by
      refine tsum_congr fun k => ?_
      rw [ENNReal.ofReal_mul ha]
    _ = ∑' k : ℕ, (ENNReal.ofReal a * (ENNReal.ofReal r) ^ k) := by
      refine tsum_congr fun k => ?_
      rw [ENNReal.ofReal_pow hr0]
    _ = ENNReal.ofReal a * ∑' k : ℕ, ((ENNReal.ofReal r) ^ k) := by
      rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal a * ((1 - ENNReal.ofReal r)⁻¹) := by
      rw [ENNReal.tsum_geometric]
    _ = ENNReal.ofReal a / (1 - ENNReal.ofReal r) := by
      rw [div_eq_mul_inv]
    _ = ENNReal.ofReal a / ENNReal.ofReal (1 - r) := by
      rw [ENNReal.ofReal_sub 1 hr0, ENNReal.ofReal_one]
    _ = ENNReal.ofReal (a / (1 - r)) := by
      rw [ENNReal.ofReal_div_of_pos hpos]

/-- The row sequence: the finite row, then the geometric tail for `fresh` and `bdry`. -/
theorem tsum_rowSeq_split (D : Data) (s : CState) (g : ℕ × CState → ℝ≥0∞) :
    ∑' n, ENNReal.ofReal ((D.rowSeq s n).p : ℝ) * g ((D.rowSeq s n).δ, (D.rowSeq s n).next) =
      ((D.finRow s).map fun e => ENNReal.ofReal (e.p : ℝ) * g (e.δ, e.next)).sum +
        match D.tailNext s with
        | some s' => ∑' k, ENNReal.ofReal (D.tailW k : ℝ) * g (D.T + 1 + k, s')
        | none => 0 := by
  set F : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal ((D.rowSeq s n).p : ℝ) * g ((D.rowSeq s n).δ, (D.rowSeq s n).next) with hF
  set L := (D.finRow s).length with hL
  have h : HasSum F (∑ i ∈ Finset.range L, F i + ∑' n, F (n + L)) :=
    HasSum.sum_range_add (f := F) (k := L) (ENNReal.summable.hasSum)
  rw [h.tsum_eq]
  congr 1
  · rw [Finset.sum_range, hL, ← Fin.sum_univ_fun_getElem]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hF, Data.rowSeq, dif_pos i.2]
  · cases ht : D.tailNext s with
    | none =>
      refine (tsum_congr fun k => ?_).trans tsum_zero
      have hk : ¬ k + L < (D.finRow s).length := by omega
      simp [hF, Data.rowSeq, ht, hk]
    | some s' =>
      refine tsum_congr fun k => ?_
      simp [hF, hL, Data.rowSeq, ht]

/-- The sum over the moves of one child: its finite row, then its geometric tail. -/
noncomputable def moveSum (D : Data) (s : CState) (g : ℕ × CState → ℝ≥0∞) : ℝ≥0∞ :=
  ((D.finRow s).map fun e => ENNReal.ofReal (e.p : ℝ) * g (e.δ, e.next)).sum +
    match D.tailNext s with
    | some s' => ∑' k, ENNReal.ofReal (D.tailW k : ℝ) * g (D.T + 1 + k, s')
    | none => 0

/-- **One root step** of the child chains of a table, as the exit and the moves of each child. -/
theorem lintegral_rstep_childStep (D : Data) (h0 : D.I0) (h1 : D.I1)
    (H : RState CState d J → ℝ≥0∞) (x : RState CState d J) (hwf : ∀ c, D.ChildWF (x.σ c)) :
    ∫⁻ ξ, H (rstep D.childStep x ξ) ∂((unifDir d).prod lam) =
      (d + 1 : ℝ≥0∞)⁻¹ * H (rstep D.childStep x (0, 0)) +
        ∑ c : Fin d, (d + 1 : ℝ≥0∞)⁻¹ * moveSum D (x.σ c) fun r => H (rstepR x c r) := by
  have hG : ∀ a, Measurable (fun (u : ℝ) => H (FrogModel.Engine.rstep D.childStep x (a, u))) := by
    intro a
    refine Fin.cases ?_ ?_ a
    · -- a = 0
      have hconst : (fun (u : ℝ) => H (FrogModel.Engine.rstep D.childStep x (0, u))) =
                   fun _ => H (FrogModel.Engine.rstep D.childStep x (0, 0)) := by
        ext u; simp [FrogModel.Engine.rstep_zero D.childStep x u 0]
      rw [hconst]
      exact measurable_const
    · intro c
      have h_eq : (fun (u : ℝ) => H (FrogModel.Engine.rstep D.childStep x (c.succ, u))) =
                 fun u => H (FrogModel.Engine.rstepR x c (D.childStep (x.σ c) u)) := by
        ext u; simp [FrogModel.Engine.rstep_succ D.childStep x c u]
      rw [h_eq]
      have h_childStep_meas : Measurable (D.childStep (x.σ c)) := by
        refine measurable_to_countable' ?_
        intro r
        simpa [Set.preimage, Set.mem_singleton_iff] using
          FrogModel.Cert.Data.measurableSet_childStep_eq D (x.σ c) r
      have h_comp_meas : Measurable (H ∘ (FrogModel.Engine.rstepR x c)) :=
        Measurable.of_discrete
      exact h_comp_meas.comp h_childStep_meas
  rw [FrogModel.Engine.lintegral_unifDir_prod lam (fun ξ => H (FrogModel.Engine.rstep D.childStep x ξ)) hG]
  rw [Fin.sum_univ_succ]
  have h0_term : ∫⁻ u, H (FrogModel.Engine.rstep D.childStep x (0, u)) ∂lam =
      H (FrogModel.Engine.rstep D.childStep x (0, 0)) := by
    have hconst : (fun (u : ℝ) => H (FrogModel.Engine.rstep D.childStep x (0, u))) =
                 fun _ => H (FrogModel.Engine.rstep D.childStep x (0, 0)) := by
      ext u; simp [FrogModel.Engine.rstep_zero D.childStep x u 0]
    rw [hconst]
    rw [lintegral_const]
    simp [lam]
  rw [h0_term]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  have h_succ_term : ∫⁻ u, H (FrogModel.Engine.rstep D.childStep x (c.succ, u)) ∂lam =
      FrogModel.Engine.moveSum D (x.σ c) (fun r => H (FrogModel.Engine.rstepR x c r)) := by
    calc
      ∫⁻ u, H (FrogModel.Engine.rstep D.childStep x (c.succ, u)) ∂lam =
          ∫⁻ u, H (FrogModel.Engine.rstepR x c (D.childStep (x.σ c) u)) ∂lam := by
        refine lintegral_congr (fun u => ?_)
        simp [FrogModel.Engine.rstep_succ D.childStep x c u]
      _ = ∑' n, ENNReal.ofReal ((D.rowSeq (x.σ c) n).p : ℝ) *
          H (FrogModel.Engine.rstepR x c ((D.rowSeq (x.σ c) n).δ, (D.rowSeq (x.σ c) n).next)) := by
        rw [FrogModel.Cert.Data.lintegral_childStep D h0 h1 (x.σ c) (hwf c) (fun r => H (FrogModel.Engine.rstepR x c r))]
      _ = FrogModel.Engine.moveSum D (x.σ c) (fun r => H (FrogModel.Engine.rstepR x c r)) := by
        rw [FrogModel.Engine.tsum_rowSeq_split D (x.σ c) (fun r => H (FrogModel.Engine.rstepR x c r)),
          FrogModel.Engine.moveSum]
  rw [h_succ_term]

/-- **One root step of `cand`**. -/
theorem lintegral_nuC_rstep (H : RState CState 4 4 → ℝ≥0∞) (x : RState CState 4 4)
    (hwf : ∀ c, cand.ChildWF (x.σ c)) :
    ∫⁻ ξ, H (rstep cand.childStep x ξ) ∂nuC =
      5⁻¹ * H (rstep cand.childStep x (0, 0)) +
        ∑ c : Fin 4, 5⁻¹ * moveSum cand (x.σ c) fun r => H (rstepR x c r) := by
  have h := lintegral_rstep_childStep cand cand_I0 cand_I1 H x hwf
  norm_num at h
  exact h

/-- **One step of the dominating chain of `cand`**. -/
theorem lintegral_candDom (T' : ℕ) (keep : RState CState 4 4 → Bool)
    (F : RState CState 4 4 × Bool → ℝ≥0∞) (y : RState CState 4 4 × Bool)
    (hwf : ∀ c, cand.ChildWF (y.1.σ c)) :
    ∫⁻ ξ, F (candDom T' keep y ξ) ∂nuC =
      5⁻¹ * F (domNext cand.T T' keep (lumpState cand) y (rstep cand.childStep y.1 (0, 0))) +
        ∑ c : Fin 4, 5⁻¹ * moveSum cand (y.1.σ c) fun r =>
          F (domNext cand.T T' keep (lumpState cand) y (rstepR y.1 c r)) := by
  exact lintegral_nuC_rstep (fun x' => F (domNext cand.T T' keep (lumpState cand) y x')) y.1 hwf

end FrogModel.Engine
