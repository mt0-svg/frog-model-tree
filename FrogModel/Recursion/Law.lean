module

public import FrogModel.Recursion.Copy
public import FrogModel.Recursion.LawGen
public import FrogModel.Recursion.Statement

@[expose] public section

/-!
# The law of the child curves (Lemma 4.3 of the paper)

The pieces `π : StarSeg d → ℕ → Step d` are i.i.d. (`pieceMeasure`); the glued sample has law
`frogMeasure d ⊗ initMeasure d` (`map_glue`).

- Pathwise (`curveK_succ_eq_psiG`): `curveK (K + 1)` of the glued sample is
  `psiG (childS K π) (dirS K π)`, where `procS K π` are the root segments in processing order
  (Process.lean), `dirS` their directions, and `childS K π c` the curve of the copy below `c`
  (Copy.lean), fed with the entries into `c` in order (`entryS`).
- Adapted reading (`map_readS`): `procS K π k` depends only on the parameter (the segments `0`
  of the sleeping frogs, `isParamSeg`) and on the pieces read before (`procS_congr`). So the
  parameter and the pieces read (`readS`) are independent i.i.d. families.
- The directions and the shifted pieces read are independent (`map_dirTail`), the entries into
  each child are an injective reindexing (`map_thinS`), and the copies are independent with law
  `curveLaw d K` (`map_copyCurves`). Hence `map_childS_dirS`.
- Kill depth `0`: `curveK_zero_eq`, `map_dirZero`, `psiLaw_dirac_zero`.
-/

open MeasureTheory ProbabilityTheory FrogModel.LemmaX

namespace FrogModel.Recursion

/-- The law of the pieces: i.i.d. step sequences, one per segment. -/
noncomputable def pieceMeasure (d : ℕ) [NeZero d] : Measure (StarSeg d → ℕ → Step d) :=
  Measure.infinitePi fun _ : StarSeg d => Measure.infinitePi fun _ : ℕ => stepLaw d

instance {d : ℕ} [NeZero d] : IsProbabilityMeasure (frogMeasure d) := by
  unfold frogMeasure; infer_instance

instance {d : ℕ} [NeZero d] : IsProbabilityMeasure (initMeasure d) := by
  unfold initMeasure; infer_instance

instance {d : ℕ} : IsProbabilityMeasure (dirMeasure d) := by
  unfold dirMeasure; infer_instance

instance {d : ℕ} [NeZero d] : IsProbabilityMeasure (pieceMeasure d) := by
  unfold pieceMeasure; infer_instance

instance {d : ℕ} [NeZero d] (K : ℕ) : IsProbabilityMeasure (curveLaw d K) := by
  unfold curveLaw; infer_instance

/-- The root segments of `T*` at kill depth `K + 1`, in processing order. -/
noncomputable def procS {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) : ℕ → StarSeg d :=
  proc starInit (dirSeg π) (starOut (K + 1) π)

/-- The directions of the root steps. -/
noncomputable def dirS {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) : ℕ → Fin (d + 1) :=
  fun k => dirSeg π (procS K π k)

/-- The `i`-th entry into child `c`. -/
noncomputable def entryS {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d) :
    ℕ → StarSeg d :=
  fun i => procS K π (Nat.nth (fun k => dirS K π k = c.succ) i)

/-- The child curves: the curves of the copies below the children. -/
noncomputable def childS {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) : Fin d → ℕ → ℕ∞ :=
  fun c => curveK K (copyZeta π c) (copyXi π c (entryS K π c))

/-- The parameter segments: the segments `0` of the sleeping frogs. -/
def isParamSeg {d : ℕ} (x : StarSeg d) : Prop := ∃ v : Vertex d, x = (Sum.inl v, 0)

/-- The parameter: the pieces of the parameter segments. -/
def paramOf {d : ℕ} (π : StarSeg d → ℕ → Step d) : {u : StarSeg d // isParamSeg u} → ℕ → Step d :=
  fun u => π u

/-- The pieces read at the root steps. -/
noncomputable def readS {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) : ℕ → ℕ → Step d :=
  fun k => π (procS K π k)

/-- The directions and the shifted pieces of a sequence of pieces. -/
def dirTail {d : ℕ} (Y : ℕ → ℕ → Step d) : (ℕ → Fin (d + 1)) × (ℕ → ℕ → Step d) :=
  (fun k => (Y k 0).2, fun k t => Y k (t + 1))

/-- Thinning: the shifted pieces of the `i`-th entry into `c`. -/
noncomputable def thinS {d : ℕ} (D : ℕ → Fin (d + 1)) (W : ℕ → ℕ → Step d) :
    Fin d × ℕ → ℕ → Step d :=
  fun ci => W (Nat.nth (fun k => D k = ci.1.succ) ci.2)

/-- The curve of a copy whose first active frog is the sleeping frog of its root. -/
noncomputable def consCurve {d : ℕ} (K : ℕ) (z : Sample d) (x : ℕ → ℕ → Step d) : ℕ → ℕ∞ :=
  curveK K z (seqCons (z []) x)

/-- The copy curves from the parameter and the thinned pieces. -/
noncomputable def copyCurves {d : ℕ} (K : ℕ) (p : {u : StarSeg d // isParamSeg u} → ℕ → Step d)
    (V : Fin d × ℕ → ℕ → Step d) : Fin d → ℕ → ℕ∞ :=
  fun c => consCurve K (fun w => p ⟨(Sum.inl (w ++ [c]), 0), w ++ [c], rfl⟩) fun i => V (c, i)

/-! ### The gluing -/

/-- The pieces of each frog are i.i.d., independent across frogs. -/
theorem map_starPieces {d : ℕ} [NeZero d] :
    (pieceMeasure d).map (fun π f => starPieces π f) =
      Measure.infinitePi fun _ : Vertex d ⊕ ℕ => Measure.infinitePi fun _ : ℕ × ℕ => stepLaw d := by
  unfold pieceMeasure
  have hg : Function.Injective
      (fun a : (Vertex d ⊕ ℕ) × (ℕ × ℕ) => (((a.1, a.2.1), a.2.2) : StarSeg d × ℕ)) := by
    rintro ⟨f, s, i⟩ ⟨f', s', i'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  have m1 := (MeasurableEquiv.curry (StarSeg d) ℕ (Step d)).symm.measurable
  have m2 : Measurable fun (ω : StarSeg d × ℕ → Step d) (a : (Vertex d ⊕ ℕ) × (ℕ × ℕ)) =>
      ω ((a.1, a.2.1), a.2.2) :=
    measurable_pi_iff.2 fun a => measurable_pi_apply _
  have m3 := (MeasurableEquiv.curry (Vertex d ⊕ ℕ) (ℕ × ℕ) (Step d)).measurable
  have hfun : (fun π : StarSeg d → ℕ → Step d => fun f => starPieces π f) =
      ⇑(MeasurableEquiv.curry (Vertex d ⊕ ℕ) (ℕ × ℕ) (Step d)) ∘
        (fun (ω : StarSeg d × ℕ → Step d) (a : (Vertex d ⊕ ℕ) × (ℕ × ℕ)) =>
          ω ((a.1, a.2.1), a.2.2)) ∘
        ⇑(MeasurableEquiv.curry (StarSeg d) ℕ (Step d)).symm := by
    funext π f p
    rfl
  rw [hfun, ← Measure.map_map m3 (m2.comp m1), ← Measure.map_map m2 m1,
    Measure.infinitePi_map_curry_symm (fun _ _ => stepLaw d),
    Measure.map_infinitePi_infinitePi_of_inj hg]
  exact Measure.infinitePi_map_curry (fun _ _ => stepLaw d)

/-- The glued sample is measurable in the pieces. -/
theorem measurable_glue {d : ℕ} [NeZero d] :
    Measurable fun π : StarSeg d → ℕ → Step d => (glueZeta π, glueXi π) := by
  have hsp : Measurable fun π : StarSeg d → ℕ → Step d => fun f => starPieces π f :=
    measurable_pi_iff.2 fun f => measurable_pi_iff.2 fun p =>
      (measurable_pi_apply p.2).comp (measurable_pi_apply (f, p.1))
  have hG : Measurable fun Z : Vertex d ⊕ ℕ → ℕ × ℕ → Step d =>
      fun f => gluePath (frogStart f) (Z f) :=
    measurable_pi_iff.2 fun f => (measurable_gluePath (frogStart f)).comp (measurable_pi_apply f)
  have hS : Measurable fun Y : Vertex d ⊕ ℕ → ℕ → Step d =>
      ((fun v => Y (Sum.inl v), fun a => Y (Sum.inr a)) : Sample d × (ℕ → ℕ → Step d)) :=
    (measurable_pi_iff.2 fun v => measurable_pi_apply (Sum.inl v)).prodMk
      (measurable_pi_iff.2 fun a => measurable_pi_apply (Sum.inr a))
  have h := hS.comp (hG.comp hsp)
  exact h

/-- **The glued sample is a sample of the frog model with i.i.d. initial frogs.** -/
theorem map_glue {d : ℕ} [NeZero d] :
    (pieceMeasure d).map (fun π => (glueZeta π, glueXi π)) =
      (frogMeasure d).prod (initMeasure d) := by
  have hsp : Measurable fun π : StarSeg d → ℕ → Step d => fun f => starPieces π f :=
    measurable_pi_iff.2 fun f => measurable_pi_iff.2 fun p =>
      (measurable_pi_apply p.2).comp (measurable_pi_apply (f, p.1))
  have hG : Measurable fun Z : Vertex d ⊕ ℕ → ℕ × ℕ → Step d =>
      fun f => gluePath (frogStart f) (Z f) :=
    measurable_pi_iff.2 fun f => (measurable_gluePath (frogStart f)).comp (measurable_pi_apply f)
  have hS : Measurable fun Y : Vertex d ⊕ ℕ → ℕ → Step d =>
      ((fun v => Y (Sum.inl v), fun a => Y (Sum.inr a)) : Sample d × (ℕ → ℕ → Step d)) :=
    (measurable_pi_iff.2 fun v => measurable_pi_apply (Sum.inl v)).prodMk
      (measurable_pi_iff.2 fun a => measurable_pi_apply (Sum.inr a))
  have h2 : (Measure.infinitePi fun _ : Vertex d ⊕ ℕ =>
        Measure.infinitePi fun _ : ℕ × ℕ => stepLaw d).map
        (fun Z f => gluePath (frogStart f) (Z f)) =
      Measure.infinitePi fun _ : Vertex d ⊕ ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d := by
    rw [Measure.infinitePi_map_pi _ (fun f => measurable_gluePath (frogStart f))]
    congr 1
    funext f
    exact map_gluePath _
  have h3 := map_infinitePi_pair
    (fun _ : Vertex d ⊕ ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d) Sum.inl Sum.inr
    Sum.inl_injective Sum.inr_injective (fun a b => Sum.inl_ne_inr)
  have hfun : (fun π : StarSeg d → ℕ → Step d => (glueZeta π, glueXi π)) =
      (fun Y : Vertex d ⊕ ℕ → ℕ → Step d =>
        ((fun v => Y (Sum.inl v), fun a => Y (Sum.inr a)) : Sample d × (ℕ → ℕ → Step d))) ∘
      (fun Z : Vertex d ⊕ ℕ → ℕ × ℕ → Step d => fun f => gluePath (frogStart f) (Z f)) ∘
      (fun π : StarSeg d → ℕ → Step d => fun f => starPieces π f) := by
    funext π
    rfl
  rw [hfun, ← Measure.map_map hS (hG.comp hsp), ← Measure.map_map hG hsp, map_starPieces, h2]
  exact h3

/-! ### The processing of `T*` -/

/-- The returns of a child are monotone in the segments given. -/
theorem starOut_mono {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d) :
    Monotone (starOut K π c) := by
  exact fun _ _ h => outGen_mono (dirSeg π) (starGen K) π isRootSeg subSeg c h

/-- The initial segments are distinct. -/
theorem starInit_injective {d : ℕ} : Function.Injective (starInit (d := d)) := by
  intro a b h
  simpa [starInit] using h

/-- No initial segment is returned. -/
theorem starInit_not_mem_starOut {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d)
    (S : Set (StarSeg d)) (a : ℕ) : starInit a ∉ starOut K π c S := by
  exact init_not_mem_outGen starInit (dirSeg π) (starGen K) π isRootSeg subSeg
    (fun x a => not_starGen_init K π x a) c S a

/-- Two children return disjoint sets. -/
theorem starOut_disjoint {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c c' : Fin d)
    (S S' : Set (StarSeg d)) (h : c ≠ c') : Disjoint (starOut K π c S) (starOut K π c' S') := by
  exact outGen_disjoint (dirSeg π) (starGen K) π isRootSeg subSeg not_isRootSeg_of_subSeg subSeg_unique
    (fun x x' y hy hx hx' => starGen_pred K π x x' y hy hx hx') c c' S S' h

/-- The returned segments are root segments and not parameter segments. -/
theorem starOut_root_not_param {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d)
    (S : Set (StarSeg d)) (y : StarSeg d) (hy : y ∈ starOut K π c S) :
    isRootSeg y ∧ ¬ isParamSeg y := by
  obtain ⟨hroot, x, -, hgen⟩ := hy
  refine ⟨hroot, ?_⟩
  rintro ⟨v, rfl⟩
  rcases hgen with ⟨heq, -⟩ | ⟨u, hu, heq, -⟩
  · have := congrArg Prod.snd heq
    simp only at this
    omega
  · simp only [Prod.mk.injEq, Sum.inl.injEq, and_true] at heq
    subst heq
    apply hu
    simpa [isRootSeg, starStart, segStart, frogStart] using hroot

/-- The processed segments are root segments and not parameter segments. -/
theorem procS_root_not_param {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (k : ℕ) :
    isRootSeg (procS K π k) ∧ ¬ isParamSeg (procS K π k) := by
  have hinit : ∀ a : ℕ, isRootSeg (starInit (d := d) a) ∧ ¬ isParamSeg (starInit (d := d) a) := by
    intro a
    refine ⟨by simp [isRootSeg, starStart, segStart, frogStart, starInit], ?_⟩
    rintro ⟨v, hv⟩
    simp [starInit] at hv
  rcases proc_cases starInit (dirSeg π) (starOut (K + 1) π) k with ⟨hmem, -, -⟩ | ⟨-, hproc, -⟩
  · rcases hmem with ⟨a, -, ha⟩ | hmem
    · rw [procS, ← ha]
      exact hinit a
    · simp only [Set.mem_iUnion] at hmem
      obtain ⟨c, hc⟩ := hmem
      exact starOut_root_not_param (K + 1) π c _ _ hc
  · rw [procS, hproc]
    exact hinit _

/-- The processed segments are distinct. -/
theorem procS_injective {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) :
    Function.Injective (procS K π) := by
  exact proc_injective starInit (dirSeg π) (starOut (K + 1) π) starInit_injective
    (fun c S a => starInit_not_mem_starOut (K + 1) π c S a)

/-- The returns of child `c` after `n` root steps are the child curve at its entry count. -/
theorem childRet_childS {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) (c : Fin d) (n : ℕ) :
    childRet (childS K π c) (dirCount (dirS K π) c.succ n) =
      (starOut (K + 1) π c
        {x | x ∈ served starInit (dirSeg π) (starOut (K + 1) π) n ∧ dirSeg π x = c.succ}).encard := by
  classical
  set p : ℕ → Prop := fun k => dirS K π k = c.succ with hp
  set S := {x | x ∈ served starInit (dirSeg π) (starOut (K + 1) π) n ∧ dirSeg π x = c.succ}
    with hS
  set M := Nat.count p n with hM
  have hcount : dirCount (dirS K π) c.succ n = (M : ℕ∞) := by
    unfold dirCount
    have : {k : ℕ | (k : ℕ∞) < (n : ℕ∞) ∧ dirS K π k = c.succ} =
        (((Finset.range n).filter p : Finset ℕ) : Set ℕ) := by
      ext k
      simp [p, Nat.cast_lt]
    rw [this, Set.encard_coe_eq_coe_finsetCard, hM, Nat.count_eq_card_filter_range]
  have hmem : ∀ i < M, ∀ hf : (Set.ofPred p).Finite, i < hf.toFinset.card :=
    fun i hi hf => hi.trans_le (Nat.count_le_card hf n)
  have hSeq : S = entryS K π c '' {i | i < M} := by
    ext x
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hd⟩
      exact ⟨Nat.count p k, Nat.count_strict_mono hd hk, by
        simp only [entryS]; rw [Nat.nth_count hd]; rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨Nat.nth p i, Nat.nth_lt_of_lt_count hi, rfl⟩, Nat.nth_mem i (hmem i hi)⟩
  have hentry : entrySet π c S = S := by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      refine ⟨hx, ?_, hx.2⟩
      obtain ⟨⟨k, -, rfl⟩, -⟩ := hx
      exact (procS_root_not_param K π k).1
  by_cases hM0 : M = 0
  · rw [hcount, hM0, Nat.cast_zero, childRet, ite_eq_left rfl, starOut_eq_empty, Set.encard_empty]
    rw [hentry, hSeq, hM0]
    simp
  · have hm1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 hM0
    have heinj : Set.InjOn (entryS K π c) {i | i < M} := by
      intro i hi j hj h
      have h' := procS_injective K π h
      rcases (Set.ofPred p).finite_or_infinite with hf | hf
      · exact Nat.nth_injOn hf (hmem i hi hf) (hmem j hj hf) h'
      · exact Nat.nth_injective hf h'
    rw [hcount, childRet, ite_eq_right (by exact_mod_cast hM0), ← Nat.cast_succ,
      extCurve_coe (childS K π c) (curveK_mono _ _ _),
      encard_starOut K π c S M hm1 (entryS K π c) (hentry.trans hSeq) heinj]
    rfl

/-- **The exact recursion, pathwise.** -/
theorem curveK_succ_eq_psiG {d : ℕ} [NeZero d] (K : ℕ) (π : StarSeg d → ℕ → Step d)
    (h0 : {k | dirS K π k = 0}.Infinite) :
    curveK (K + 1) (glueZeta π) (glueXi π) = psiG (childS K π) (dirS K π) := by
  funext j
  rw [curveK_eq_arrSet (K + 1) π j]
  exact (psiG_proc_eq starInit (dirSeg π) (starOut (K + 1) π) starInit_injective
    (starOut_mono (K + 1) π) (fun c S a => starInit_not_mem_starOut (K + 1) π c S a)
    (fun c c' S S' h => starOut_disjoint (K + 1) π c c' S S' h) (childS K π)
    (childRet_childS K π) h0 j).symm

/-! ### Adapted reading -/

/-- The returns of a child read the pieces of the segments given and of the parameter only. -/
theorem starOut_congr {d : ℕ} (K : ℕ) (π π' : StarSeg d → ℕ → Step d) (c : Fin d)
    (S : Set (StarSeg d)) (h : ∀ x, x ∈ S ∨ isParamSeg x → π' x = π x) :
    starOut K π' c {x | x ∈ S ∧ dirSeg π' x = c.succ} =
      starOut K π c {x | x ∈ S ∧ dirSeg π x = c.succ} := by
  have hdir : ∀ x ∈ S, dirSeg π' x = dirSeg π x := fun x hx => by
    simp only [dirSeg, h x (Or.inl hx)]
  have hT : {x | x ∈ S ∧ dirSeg π' x = c.succ} = {x | x ∈ S ∧ dirSeg π x = c.succ} := by
    ext x
    constructor
    · rintro ⟨hx, hd⟩
      exact ⟨hx, (hdir x hx).symm.trans hd⟩
    · rintro ⟨hx, hd⟩
      exact ⟨hx, (hdir x hx).trans hd⟩
  rw [hT]
  set T := {x | x ∈ S ∧ dirSeg π x = c.succ} with hTdef
  have hbase : {x | x ∈ T ∧ isRootSeg x ∧ dirSeg π' x = c.succ} =
      {x | x ∈ T ∧ isRootSeg x ∧ dirSeg π x = c.succ} := by
    ext x
    constructor
    · rintro ⟨hx, hr, hd⟩
      exact ⟨hx, hr, (hdir x hx.1).symm.trans hd⟩
    · rintro ⟨hx, hr, hd⟩
      exact ⟨hx, hr, (hdir x hx.1).trans hd⟩
  have hin : ∀ x ∈ subClosure (dirSeg π) (starGen K) π isRootSeg subSeg c T, π' x = π x := by
    intro x hx
    rcases subClosure_subset (dirSeg π) (starGen K) π isRootSeg subSeg c T hx with
      ⟨hxT, -, -⟩ | ⟨w, rfl⟩
    · exact h x (Or.inl hxT.1)
    · exact h _ (Or.inr ⟨w ++ [c], rfl⟩)
  have hcl : subClosure (dirSeg π') (starGen K) π' isRootSeg subSeg c T =
      subClosure (dirSeg π) (starGen K) π isRootSeg subSeg c T := by
    unfold subClosure
    rw [hbase]
    refine FrogModel.Stage.closure_eq_of_agree _ π π' _ {x | π' x ≠ π x} ?_ ?_
    · intro σ hσ
      simp only [Set.mem_ofPred_eq, not_not] at hσ
      exact hσ.symm
    · rw [Set.disjoint_left]
      intro x hx hxB
      exact hxB (hin x hx)
  unfold starOut outGen
  rw [hcl]
  ext y
  constructor
  · rintro ⟨hy, x, hx, hg⟩
    exact ⟨hy, x, hx, by rwa [← hin x hx]⟩
  · rintro ⟨hy, x, hx, hg⟩
    exact ⟨hy, x, hx, by rwa [hin x hx]⟩

/-- The processing reads the returns of the served arrivals only. -/
theorem procHist_congr {d : ℕ} {α : Type*} [Encodable α] (init : ℕ → α)
    (dir dir' : α → Fin (d + 1)) (out out' : Fin d → Set α → Set α) (n : ℕ)
    (h : ∀ m < n, ∀ c, out' c {x | x ∈ served init dir out m ∧ dir' x = c.succ} =
      out c {x | x ∈ served init dir out m ∧ dir x = c.succ}) :
    procHist init dir' out' n = procHist init dir out n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have ih' := ih (fun m' hm' c => h m' (by omega) c)
    have hS : {x | x ∈ (procHist init dir out m).1} = served init dir out m := by
      ext x
      exact mem_procHist init dir out m x
    have havail : availSet init dir' out' {x | x ∈ (procHist init dir out m).1}
          (procHist init dir out m).2 =
        availSet init dir out {x | x ∈ (procHist init dir out m).1} (procHist init dir out m).2 := by
      rw [hS]
      unfold availSet
      congr 1
      exact Set.iUnion_congr fun c => h m (by omega) c
    show procStep init dir' out' (procHist init dir' out' m) =
      procStep init dir out (procHist init dir out m)
    rw [ih']
    have hmin : ∀ (W W' : Set α) (hW : W.Nonempty) (hW' : W'.Nonempty), W = W' →
        minCode W hW = minCode W' hW' := by
      rintro W _ hW hW' rfl
      rfl
    unfold procStep
    split_ifs with h1 h2 h2
    · rw [hmin _ _ h1 h2 (by rw [havail])]
    · exact absurd (by rwa [havail] at h1) h2
    · exact absurd (by rwa [havail]) h1
    · rfl

/-- **Adaptedness.** The segment processed at step `k` depends only on the parameter and on
the pieces processed before. -/
theorem procS_congr {d : ℕ} (K : ℕ) (k : ℕ) (π π' : StarSeg d → ℕ → Step d)
    (hpar : ∀ u, isParamSeg u → π' u = π u) (hread : ∀ i < k, π' (procS K π i) = π (procS K π i)) :
    procS K π' k = procS K π k := by
  unfold procS proc
  rw [procHist_congr starInit (dirSeg π) (dirSeg π') (starOut (K + 1) π) (starOut (K + 1) π')
    (k + 1) ?_]
  intro m hm c
  apply starOut_congr
  rintro x (⟨i, hi, rfl⟩ | hx)
  · exact hread i (by omega)
  · exact hpar x hx

/-- The relation `starGen` is measurable in the piece. -/
theorem measurableSet_starGen {d : ℕ} (K : ℕ) (x y : StarSeg d) :
    MeasurableSet {p : ℕ → Step d | starGen K x p y} := by
  have hP : ∀ (P : Option (Vertex d) → Prop) (v : Option (Vertex d)) (n : ℕ),
      Measurable fun p : ℕ → Step d => P (walkStar v p n) :=
    fun P v n => (measurable_of_countable P).comp (measurable_walkStar_apply v n)
  have hdep : ∀ (v : Option (Vertex d)) (n : ℕ),
      Measurable fun p : ℕ → Step d => ∀ i ≤ n, depthStar (walkStar v p i) ≤ K :=
    fun v n => Measurable.forall fun i => Measurable.imp measurable_const
      (hP (fun o => depthStar o ≤ K) v i)
  have hret : Measurable fun p : ℕ → Step d => retK K (starStart x) p :=
    Measurable.exists fun c => measurable_const.and ((hP (· = some []) _ c).and (hdep _ c))
  have hseg : ∀ u : Vertex d, Measurable fun p : ℕ → Step d => segVis K (starStart x) p (some u) :=
    fun u => Measurable.exists fun n => (hP (· = some u) _ n).and ((Measurable.forall fun i =>
      Measurable.imp measurable_const (Measurable.imp measurable_const
        (hP (· ≠ some []) _ i))).and (hdep _ n))
  refine measurableSet_setOfPred.2 ?_
  unfold starGen
  exact (measurable_const.and hret).or (Measurable.exists fun u =>
    measurable_const.and (measurable_const.and (hseg u)))

/-- Membership in the returns of a child given a finite list is measurable in the pieces. -/
theorem measurableSet_mem_starOut {d : ℕ} (K : ℕ) (c : Fin d) (L : List (StarSeg d))
    (y : StarSeg d) :
    MeasurableSet {π : StarSeg d → ℕ → Step d |
      y ∈ starOut K π c {x | x ∈ L ∧ dirSeg π x = c.succ}} := by
  have hdir : ∀ σ : StarSeg d, Measurable fun π : StarSeg d → ℕ → Step d => dirSeg π σ = c.succ :=
    fun σ => (measurable_snd.comp ((measurable_pi_apply 0).comp (measurable_pi_apply σ))).eq_const _
  have harc : ∀ σ τ : StarSeg d, MeasurableSet {p : ℕ → Step d | starGen K σ p τ ∧ subSeg c τ} :=
    fun σ τ => (measurableSet_starGen K σ τ).inter (MeasurableSet.const _)
  have hbase : ∀ σ : StarSeg d, MeasurableSet {π : StarSeg d → ℕ → Step d |
      σ ∈ {x | x ∈ {x | x ∈ L ∧ dirSeg π x = c.succ} ∧ isRootSeg x ∧ dirSeg π x = c.succ}} :=
    fun σ => measurableSet_setOfPred.2 ((measurable_const.and (hdir σ)).and
      (measurable_const.and (hdir σ)))
  refine measurableSet_setOfPred.2 ?_
  unfold starOut outGen
  refine measurable_const.and (Measurable.exists fun x => Measurable.and ?_ ?_)
  · exact measurableSet_setOfPred.1 (FrogModel.Stage.measurableSet_closure
      (fun x p y => starGen K x p y ∧ subSeg c y) harc
      (fun π => {x | x ∈ {x | x ∈ L ∧ dirSeg π x = c.succ} ∧ isRootSeg x ∧ dirSeg π x = c.succ})
      hbase x)
  · exact measurableSet_setOfPred.1 ((measurableSet_starGen K x y).preimage
      (measurable_pi_apply x))

/-- The processing is measurable in a parameter that measurably drives the returns. -/
theorem measurableSet_procHist_eq {d : ℕ} {Ω α : Type*} [MeasurableSpace Ω] [Encodable α]
    (init : ℕ → α) (dir : Ω → α → Fin (d + 1)) (out : Ω → Fin d → Set α → Set α)
    (hout : ∀ c (L : List α) y, MeasurableSet {ω | y ∈ out ω c {x | x ∈ L ∧ dir ω x = c.succ}})
    (n : ℕ) (st : List α × ℕ) :
    MeasurableSet {ω | procHist init (dir ω) (out ω) n = st} := by
  classical
  have hW : ∀ (L : List α) (r : ℕ) (y : α), MeasurableSet
      {ω | y ∈ availSet init (dir ω) (out ω) {x | x ∈ L} r \ {x | x ∈ L}} := by
    intro L r y
    by_cases hyL : y ∈ L
    · have : {ω | y ∈ availSet init (dir ω) (out ω) {x | x ∈ L} r \ {x | x ∈ L}} = ∅ := by
        ext ω
        simp [hyL]
      rw [this]
      exact MeasurableSet.empty
    · have : {ω | y ∈ availSet init (dir ω) (out ω) {x | x ∈ L} r \ {x | x ∈ L}} =
          {_ω | y ∈ init '' {a | a < r}} ∪
            ⋃ c : Fin d, {ω | y ∈ out ω c {x | x ∈ L ∧ dir ω x = c.succ}} := by
        ext ω
        simp [availSet, hyL]
      rw [this]
      exact (MeasurableSet.const _).union (MeasurableSet.iUnion fun c => hout c L y)
  induction n generalizing st with
  | zero =>
    simp only [procHist]
    exact MeasurableSet.const _
  | succ n ih =>
    have hsplit : {ω | procHist init (dir ω) (out ω) (n + 1) = st} =
        ⋃ st' : List α × ℕ, {ω | procHist init (dir ω) (out ω) n = st'} ∩
          {ω | procStep init (dir ω) (out ω) st' = st} := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨_, rfl, h⟩
      · rintro ⟨st', h1, h2⟩
        rw [← h1] at h2
        exact h2
    rw [hsplit]
    refine MeasurableSet.iUnion fun st' => (ih st').inter ?_
    obtain ⟨L, r⟩ := st'
    set W : Ω → Set α := fun ω => availSet init (dir ω) (out ω) {x | x ∈ L} r \ {x | x ∈ L}
      with hWdef
    have hne : MeasurableSet {ω | (W ω).Nonempty} := by
      have : {ω | (W ω).Nonempty} = ⋃ y, {ω | y ∈ W ω} := by
        ext ω
        simp [Set.Nonempty]
      rw [this]
      exact MeasurableSet.iUnion fun y => hW L r y
    have hmin : ∀ z, MeasurableSet {ω | ∃ h : (W ω).Nonempty, minCode (W ω) h = z} := by
      intro z
      have : {ω | ∃ h : (W ω).Nonempty, minCode (W ω) h = z} =
          {ω | z ∈ W ω} ∩ ⋂ y : α, ⋂ (_ : Encodable.encode y < Encodable.encode z),
            {ω | y ∉ W ω} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
        constructor
        · rintro ⟨h, rfl⟩
          refine ⟨WellFounded.min_mem _ _ _, fun y hy hyW => ?_⟩
          exact (WellFounded.not_lt_min (measure (Encodable.encode : α → ℕ)).wf (W ω) hyW) hy
        · rintro ⟨hz, hlt⟩
          refine ⟨⟨z, hz⟩, ?_⟩
          have hm : minCode (W ω) ⟨z, hz⟩ ∈ W ω := WellFounded.min_mem _ _ _
          have h1 : ¬ Encodable.encode (minCode (W ω) ⟨z, hz⟩) < Encodable.encode z :=
            fun h => hlt _ h hm
          have h2 : ¬ Encodable.encode z < Encodable.encode (minCode (W ω) ⟨z, hz⟩) :=
            WellFounded.not_lt_min (measure (Encodable.encode : α → ℕ)).wf (W ω) hz
          exact Encodable.encode_injective (by omega)
      rw [this]
      exact (hW L r z).inter (MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
        (hW L r y).compl)
    have hstep : {ω | procStep init (dir ω) (out ω) (L, r) = st} =
        (⋃ z : α, ⋃ (_ : (L ++ [z], r) = st), {ω | ∃ h : (W ω).Nonempty, minCode (W ω) h = z}) ∪
          ({ω | (W ω).Nonempty}ᶜ ∩ {_ω | (L ++ [init r], r + 1) = st}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_compl_iff, procStep]
      by_cases h : (W ω).Nonempty
      · rw [dite_eq_left h]
        constructor
        · intro hst
          exact Or.inl ⟨_, hst, h, rfl⟩
        · rintro (⟨z, hst, h', hz⟩ | ⟨hn, -⟩)
          · rw [← hst, ← hz]
          · exact absurd h hn
      · rw [dite_eq_right h]
        constructor
        · intro hst
          exact Or.inr ⟨h, hst⟩
        · rintro (⟨z, -, h', -⟩ | ⟨-, hst⟩)
          · exact absurd h' h
          · exact hst
    rw [hstep]
    refine (MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _ => hmin z).union
      (hne.compl.inter (MeasurableSet.const _))

/-- The processed segments are measurable in the pieces. -/
theorem measurableSet_procS_eq {d : ℕ} (K k : ℕ) (u : StarSeg d) :
    MeasurableSet {π : StarSeg d → ℕ → Step d | procS K π k = u} := by
  have hset : {π : StarSeg d → ℕ → Step d | procS K π k = u} =
      ⋃ st : List (StarSeg d) × ℕ, ⋃ (_ : st.1.getLastD (starInit 0) = u),
        {π | procHist starInit (dirSeg π) (starOut (K + 1) π) (k + 1) = st} := by
    ext π
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨st, hst, h⟩
      rw [← hst, ← h]
      rfl
  rw [hset]
  exact MeasurableSet.iUnion fun st => MeasurableSet.iUnion fun _ =>
    measurableSet_procHist_eq starInit (fun π => dirSeg π) (fun π => starOut (K + 1) π)
      (fun c L y => measurableSet_mem_starOut (K + 1) c L y) (k + 1) st

/-- **Adapted reading.** The parameter and the pieces read are independent i.i.d. families. -/
theorem map_readS {d : ℕ} [NeZero d] (K : ℕ) :
    (pieceMeasure d).map (fun π => (paramOf π, readS K π)) =
      (Measure.infinitePi fun _ : {u : StarSeg d // isParamSeg u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw d).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d) := by
  unfold pieceMeasure paramOf readS
  exact map_adapted (Measure.infinitePi fun _ : ℕ => stepLaw d) isParamSeg (fun k π => procS K π k)
    (fun k π => (procS_root_not_param K π k).2) (fun π => procS_injective K π)
    (fun k π π' hpar hread => procS_congr K k π π' hpar hread)
    (fun k u => measurableSet_procS_eq K k u)

/-! ### Directions, thinning, copies -/

/-- The direction of a step is uniform. -/
theorem map_snd_stepLaw {d : ℕ} [NeZero d] :
    (stepLaw d).map Prod.snd = (uniformOn Set.univ : Measure (Fin (d + 1))) := by
  unfold stepLaw
  ext s hs
  rw [Measure.map_apply measurable_snd hs, uniformOn_univ, uniformOn_univ]
  have hpre : (Prod.snd ⁻¹' s : Set (Fin d × Fin (d + 1))) = Set.univ ×ˢ s := by
    ext p; simp
  rw [hpre, Measure.count_apply (MeasurableSet.univ.prod hs), Measure.count_apply hs,
    Set.encard_prod, Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hd : (d : ENNReal) ≠ 0 := by exact_mod_cast NeZero.ne d
  push_cast
  exact ENNReal.mul_div_mul_left _ _ hd (ENNReal.natCast_ne_top d)

/-- The directions and the shifted pieces are independent. -/
theorem map_dirTail {d : ℕ} [NeZero d] :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d).map dirTail =
      (dirMeasure d).prod (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d) := by
  set ν := Measure.infinitePi fun _ : ℕ => stepLaw d with hν
  have hf : Measurable fun y : ℕ → Step d => (y 0).2 := (measurable_pi_apply 0).snd
  have hg : Measurable fun y : ℕ → Step d => fun t => y (t + 1) :=
    measurable_pi_iff.2 fun t => measurable_pi_apply (t + 1)
  have hht := map_infinitePi_head_tail (stepLaw d)
  have hh : Measurable fun x : ℕ → Step d => (x 0, fun t => x (t + 1)) :=
    (measurable_pi_apply 0).prodMk hg
  have hpair : ν.map (fun y => ((y 0).2, fun t => y (t + 1))) =
      (uniformOn Set.univ : Measure (Fin (d + 1))).prod ν := by
    have hc : (fun y : ℕ → Step d => ((y 0).2, fun t => y (t + 1))) =
        Prod.map Prod.snd id ∘ fun x : ℕ → Step d => (x 0, fun t => x (t + 1)) := rfl
    rw [hc, ← Measure.map_map (measurable_snd.prodMap measurable_id) hh, hht,
      ← Measure.map_prod_map _ _ measurable_snd measurable_id, map_snd_stepLaw, Measure.map_id]
  have hmf : ν.map (fun y => (y 0).2) = (uniformOn Set.univ : Measure (Fin (d + 1))) := by
    have h := congrArg (fun m => m.map Prod.fst) hpair
    rw [Measure.map_map measurable_fst (hf.prodMk hg), Measure.map_fst_prod, measure_univ,
      one_smul] at h
    exact h
  have hmg : ν.map (fun y => fun t => y (t + 1)) = ν := by
    have h := congrArg (fun m => m.map Prod.snd) hpair
    rw [Measure.map_map measurable_snd (hf.prodMk hg), Measure.map_snd_prod, measure_univ,
      one_smul] at h
    exact h
  have hfg : ν.map (fun y => ((y 0).2, fun t => y (t + 1))) =
      (ν.map fun y => (y 0).2).prod (ν.map fun y => fun t => y (t + 1)) := by
    rw [hpair, hmf, hmg]
  have hmain := map_infinitePi_prodMk (ι := ℕ) ν (fun y => (y 0).2) (fun y => fun t => y (t + 1))
    hf hg hfg
  rw [hmf, hmg] at hmain
  exact hmain

/-- The index of the `i`-th occurrence of a value is measurable in the sequence. -/
theorem measurableSet_nth_eq {d : ℕ} (a : Fin (d + 1)) (i n : ℕ) :
    MeasurableSet {D : ℕ → Fin (d + 1) | Nat.nth (fun k => D k = a) i = n} := by
  have hcount : ∀ m, Measurable fun D : ℕ → Fin (d + 1) => Nat.count (fun k => D k = a) m := by
    intro m
    induction m with
    | zero => simp only [Nat.count_zero]; exact measurable_const
    | succ m ih =>
      have hg : Measurable fun q : ℕ × Fin (d + 1) => q.1 + if q.2 = a then 1 else 0 :=
        measurable_of_countable _
      have h := hg.comp (ih.prodMk (measurable_pi_apply m))
      simp only [Nat.count_succ]
      exact h
  have hchar : ∀ D : ℕ → Fin (d + 1), Nat.nth (fun k => D k = a) i = n ↔
      (D n = a ∧ Nat.count (fun k => D k = a) n = i) ∨
        (n = 0 ∧ ∀ m, ¬ (D m = a ∧ Nat.count (fun k => D k = a) m = i)) := by
    intro D
    constructor
    · intro h
      by_cases hB : ∃ hf : {k | D k = a}.Finite, hf.toFinset.card ≤ i
      · obtain ⟨hf, hc⟩ := hB
        right
        refine ⟨by rw [← h, Nat.nth_of_card_le hf hc], ?_⟩
        rintro m ⟨hm, hcm⟩
        have := Nat.count_lt_card hf hm
        omega
      · push Not at hB
        left
        subst h
        exact ⟨Nat.nth_mem i hB, Nat.count_nth hB⟩
    · rintro (⟨hn, hc⟩ | ⟨rfl, hno⟩)
      · rw [← hc]
        exact Nat.nth_count hn
      · by_cases hB : ∃ hf : {k | D k = a}.Finite, hf.toFinset.card ≤ i
        · obtain ⟨hf, hc⟩ := hB
          exact Nat.nth_of_card_le hf hc
        · push Not at hB
          exact absurd ⟨Nat.nth_mem i hB, Nat.count_nth hB⟩ (hno _)
  have hset : {D : ℕ → Fin (d + 1) | Nat.nth (fun k => D k = a) i = n} =
      {D | (D n = a ∧ Nat.count (fun k => D k = a) n = i) ∨
        (n = 0 ∧ ∀ m, ¬ (D m = a ∧ Nat.count (fun k => D k = a) m = i))} := by
    ext D
    exact hchar D
  rw [hset]
  refine measurableSet_setOfPred.2 ?_
  exact (((measurable_pi_apply n).eq_const a).and ((hcount n).eq_const i)).or
    (measurable_const.and (Measurable.forall fun m =>
      (((measurable_pi_apply m).eq_const a).and ((hcount m).eq_const i)).not))

/-- **Thinning.** The shifted pieces of the entries into the children are i.i.d., independent
of the directions. -/
theorem map_thinS {d : ℕ} [NeZero d] {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    ((μ.prod (dirMeasure d)).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d)).map
        (fun q => (q.1, thinS q.1.2 q.2)) =
      (μ.prod (dirMeasure d)).prod
        (Measure.infinitePi fun _ : Fin d × ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d) := by
  have hidx : ∀ (ci : Fin d × ℕ) (n : ℕ), MeasurableSet
      {x : X × (ℕ → Fin (d + 1)) | Nat.nth (fun k => x.2 k = ci.1.succ) ci.2 = n} :=
    fun ci n => measurable_snd (measurableSet_nth_eq ci.1.succ ci.2 n)
  have h0 : ∀ᵐ D ∂(dirMeasure d), ∀ a, {k | D k = a}.Infinite := by
    unfold dirMeasure
    exact ae_infinite_eq
  have hs : (μ.prod (dirMeasure d)).map Prod.snd = dirMeasure d := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have h1 : ∀ᵐ x ∂(μ.prod (dirMeasure d)), ∀ a, {k | x.2 k = a}.Infinite := by
    rw [← hs] at h0
    exact ae_of_ae_map (p := fun D : ℕ → Fin (d + 1) => ∀ a, {k | D k = a}.Infinite)
      measurable_snd.aemeasurable h0
  have hinj : ∀ᵐ x ∂(μ.prod (dirMeasure d)),
      Function.Injective (fun ci : Fin d × ℕ => Nat.nth (fun k => x.2 k = ci.1.succ) ci.2) := by
    filter_upwards [h1] with x hx
    rintro ⟨c, i⟩ ⟨c', i'⟩ h
    simp only at h
    have hm : x.2 (Nat.nth (fun k => x.2 k = c.succ) i) = c.succ :=
      Nat.nth_mem_of_infinite (hx c.succ) i
    have hm' : x.2 (Nat.nth (fun k => x.2 k = c'.succ) i') = c'.succ :=
      Nat.nth_mem_of_infinite (hx c'.succ) i'
    rw [h] at hm
    have hc : c = c' := Fin.succ_injective _ (hm.symm.trans hm')
    subst hc
    rw [Nat.nth_injective (hx c.succ) h]
  exact map_prod_reindex (μ.prod (dirMeasure d)) (Measure.infinitePi fun _ : ℕ => stepLaw d)
    (fun x (ci : Fin d × ℕ) => Nat.nth (fun k => x.2 k = ci.1.succ) ci.2) hidx hinj

/-- Replacing the sleeping frog of `r` by an independent path keeps the law of the frog model. -/
theorem map_update_frog {d : ℕ} [NeZero d] :
    ((frogMeasure d).prod (Measure.infinitePi fun _ : ℕ => stepLaw d)).map
        (fun q => Function.update q.1 [] q.2) = frogMeasure d := by
  have hmeas : Measurable fun q : Sample d × (ℕ → Step d) => Function.update q.1 [] q.2 :=
    measurable_update'
  conv_rhs => unfold frogMeasure
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  by_cases hs : [] ∈ s
  · have hpre : (fun q : Sample d × (ℕ → Step d) => Function.update q.1 [] q.2) ⁻¹'
        (Set.pi (↑s) t) = Set.pi (↑(s.erase [])) t ×ˢ t [] := by
      ext ⟨z, y⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun v ⟨hv, hvs⟩ => ?_, ?_⟩
        · simpa [Function.update_of_ne hv] using h v hvs
        · simpa using h [] hs
      · rintro ⟨h, hy⟩ v hvs
        by_cases hv : v = []
        · subst hv
          simpa using hy
        · simpa [Function.update_of_ne hv] using h v ⟨hv, hvs⟩
    rw [hpre, Measure.prod_prod, frogMeasure, Measure.infinitePi_pi _ (fun i _ => ht i),
      ← Finset.prod_erase_mul _ _ hs]
  · have hpre : (fun q : Sample d × (ℕ → Step d) => Function.update q.1 [] q.2) ⁻¹'
        (Set.pi (↑s) t) = Set.pi (↑s) t ×ˢ Set.univ := by
      ext ⟨z, y⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_univ,
        and_true]
      refine forall₂_congr fun v hvs => ?_
      have hv : v ≠ [] := fun h => hs (h ▸ hvs)
      simp [Function.update_of_ne hv]
    rw [hpre, Measure.prod_prod, measure_univ, mul_one, frogMeasure,
      Measure.infinitePi_pi _ (fun i _ => ht i)]

/-- The curve of a copy is measurable in its sample and its entries. -/
theorem measurable_consCurve {d : ℕ} (K : ℕ) :
    Measurable fun q : Sample d × (ℕ → ℕ → Step d) => consCurve K q.1 q.2 := by
  have hseq : Measurable fun q : (ℕ → Step d) × (ℕ → ℕ → Step d) => seqCons q.1 q.2 := by
    refine measurable_pi_iff.2 fun i => ?_
    cases i with
    | zero => exact measurable_fst
    | succ i => exact (measurable_pi_apply i).comp measurable_snd
  have hcurve : Measurable fun p : Sample d × (ℕ → ℕ → Step d) => curveK K p.1 p.2 :=
    measurable_curveK K
  have hhead : Measurable fun q : Sample d × (ℕ → ℕ → Step d) => (q.1 [], q.2) :=
    ((measurable_pi_apply (X := fun _ : Vertex d => ℕ → Step d) []).comp measurable_fst).prodMk
      measurable_snd
  have hpair : Measurable fun q : Sample d × (ℕ → ℕ → Step d) => (q.1, seqCons (q.1 []) q.2) :=
    measurable_fst.prodMk (hseq.comp hhead)
  have h := hcurve.comp hpair
  exact h

/-- The curve with the sleeping frog of the root as first active frog has law `curveLaw d K`. -/
theorem curveLaw_eq_cons {d : ℕ} [NeZero d] (K : ℕ) :
    curveLaw d K = ((frogMeasure d).prod (initMeasure d)).map (fun q => consCurve K q.1 q.2) := by
  set ν := Measure.infinitePi fun _ : ℕ => stepLaw d with hν
  have hseq : Measurable fun q : (ℕ → Step d) × (ℕ → ℕ → Step d) => seqCons q.1 q.2 := by
    refine measurable_pi_iff.2 fun i => ?_
    cases i with
    | zero => exact measurable_fst
    | succ i => exact (measurable_pi_apply i).comp measurable_snd
  have hcurve : Measurable fun p : Sample d × (ℕ → ℕ → Step d) => curveK K p.1 p.2 :=
    measurable_curveK K
  have hU0 : Measurable fun q : Sample d × (ℕ → Step d) => Function.update q.1 [] q.2 :=
    measurable_update'
  have hhead : Measurable fun q : Sample d × (ℕ → ℕ → Step d) => (q.1 [], q.2) :=
    ((measurable_pi_apply (X := fun _ : Vertex d => ℕ → Step d) []).comp measurable_fst).prodMk
      measurable_snd
  have hpair : Measurable fun q : Sample d × (ℕ → ℕ → Step d) => (q.1, seqCons (q.1 []) q.2) :=
    measurable_fst.prodMk (hseq.comp hhead)
  have hcc : Measurable fun q : Sample d × (ℕ → ℕ → Step d) => consCurve K q.1 q.2 := by
    have h := hcurve.comp hpair
    exact h
  have hcons : (ν.prod (initMeasure d)).map (fun q => seqCons q.1 q.2) = initMeasure d :=
    map_cons_infinitePi ν
  have e1 : ((frogMeasure d).prod (ν.prod (initMeasure d))).map
      (Prod.map id fun q => seqCons q.1 q.2) = (frogMeasure d).prod (initMeasure d) := by
    rw [← Measure.map_prod_map _ _ measurable_id hseq, Measure.map_id, hcons]
  have e2 : (((frogMeasure d).prod ν).prod (initMeasure d)).map
      (Prod.map (fun q => Function.update q.1 [] q.2) id) =
        (frogMeasure d).prod (initMeasure d) := by
    rw [← Measure.map_prod_map _ _ hU0 measurable_id, map_update_frog, Measure.map_id]
  calc curveLaw d K
      = ((frogMeasure d).prod (initMeasure d)).map (fun p => curveK K p.1 p.2) := rfl
    _ = (((frogMeasure d).prod (ν.prod (initMeasure d))).map
          (Prod.map id fun q => seqCons q.1 q.2)).map (fun p => curveK K p.1 p.2) := by
        rw [e1]
    _ = ((frogMeasure d).prod (ν.prod (initMeasure d))).map
          (fun q => curveK K q.1 (seqCons q.2.1 q.2.2)) := by
        rw [Measure.map_map hcurve (measurable_id.prodMap hseq)]
        rfl
    _ = ((frogMeasure d).prod (ν.prod (initMeasure d))).map
          (fun q => consCurve K (Function.update q.1 [] q.2.1) q.2.2) := by
        congr 1
        funext q
        unfold consCurve
        rw [Function.update_self]
        funext m
        exact curveK_congr K m _ _ _ _ (fun v hv => (Function.update_of_ne hv _ _).symm)
          (fun _ _ => rfl)
    _ = (((frogMeasure d).prod ν).prod (initMeasure d)).map
          (fun q => consCurve K (Function.update q.1.1 [] q.1.2) q.2) := by
        rw [← (measurePreserving_prodAssoc (frogMeasure d) ν (initMeasure d)).map_eq,
          Measure.map_map]
        · rfl
        · have hA : Measurable fun q : Sample d × ((ℕ → Step d) × (ℕ → ℕ → Step d)) =>
              (Function.update q.1 [] q.2.1, q.2.2) :=
            (hU0.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
              (measurable_snd.comp measurable_snd)
          have hB := hcc.comp hA
          exact hB
        · exact MeasurableEquiv.measurable _
    _ = ((((frogMeasure d).prod ν).prod (initMeasure d)).map
          (Prod.map (fun q => Function.update q.1 [] q.2) id)).map
          (fun q => consCurve K q.1 q.2) := by
        rw [Measure.map_map hcc (hU0.prodMap measurable_id)]
        rfl
    _ = ((frogMeasure d).prod (initMeasure d)).map (fun q => consCurve K q.1 q.2) := by
        rw [e2]

/-- The parameters of the copies are independent samples of the frog model. -/
theorem map_copyParams {d : ℕ} [NeZero d] :
    (Measure.infinitePi fun _ : {u : StarSeg d // isParamSeg u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw d).map
        (fun p (c : Fin d) (w : Vertex d) => p ⟨(Sum.inl (w ++ [c]), 0), w ++ [c], rfl⟩) =
      Measure.infinitePi fun _ : Fin d => frogMeasure d := by
  let ι : Fin d × Vertex d → {u : StarSeg d // isParamSeg u} :=
    fun ⟨c, w⟩ => ⟨(Sum.inl (w ++ [c]), 0), w ++ [c], rfl⟩
  have hι_inj : Function.Injective ι := by
    intro x y h
    rcases x with ⟨c₁, w₁⟩
    rcases y with ⟨c₂, w₂⟩
    have h_subtype : ι (c₁, w₁) = ι (c₂, w₂) := h
    have h_subtype' := Subtype.mk.inj h_subtype
    -- h_subtype' : (Sum.inl (w₁ ++ [c₁]), 0) = (Sum.inl (w₂ ++ [c₂]), 0)
    have h_sum : (Sum.inl (w₁ ++ [c₁]) : Vertex d ⊕ ℕ) = Sum.inl (w₂ ++ [c₂]) := by
      have := Prod.mk.inj h_subtype'
      exact this.1
    have h_list : w₁ ++ [c₁] = w₂ ++ [c₂] := by
      injection h_sum
    -- From w₁ ++ [c₁] = w₂ ++ [c₂], we get c₁ = c₂ and w₁ = w₂
    have h_c_eq : c₁ = c₂ := by
      have h_last : (w₁ ++ [c₁]).getLast? = (w₂ ++ [c₂]).getLast? := by rw [h_list]
      simpa using h_last
    have h_w_eq : w₁ = w₂ := by
      rw [h_c_eq] at h_list
      -- Now w₁ ++ [c₂] = w₂ ++ [c₂], cancel the suffix
      exact List.append_cancel_right h_list
    rw [h_w_eq, h_c_eq]
  -- The map in the goal is: (infinitePi P).map (fun p c w => p (ι (c, w)))
  -- This equals (infinitePi P).map (curry ∘ (fun p i => p (ι i)))
  -- where curry = MeasurableEquiv.curry (Fin d) (Vertex d) (ℕ → Step d)
  let curry := MeasurableEquiv.curry (Fin d) (Vertex d) (ℕ → Step d)
  have h_map_eq : (fun (p : ({u : StarSeg d // isParamSeg u} → ℕ → Step d))
      (c : Fin d) (w : Vertex d) => p (ι (c, w))) =
      curry ∘ (fun (p : ({u : StarSeg d // isParamSeg u} → ℕ → Step d))
      (i : Fin d × Vertex d) => p (ι i)) := by
    ext p c w x
    · dsimp [curry, ι, Function.comp]
      rw [MeasurableEquiv.curry_apply]
    · dsimp [curry, ι, Function.comp]
      rw [MeasurableEquiv.curry_apply]
  rw [h_map_eq]
  -- Target: Measure.map (curry ∘ (fun p i => p (ι i))) μ = infinitePi fun _ : Fin d => frogMeasure d
  -- Use map_map backward: μ.map (g ∘ f) = (μ.map f).map g
  rw [← MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  -- Now target: Measure.map curry (Measure.map (fun p i => p (ι i)) μ) = infinitePi fun _ : Fin d => frogMeasure d
  rw [MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj hι_inj]
  -- Now target: Measure.map curry (infinitePi fun (i : Fin d × Vertex d) => infinitePi fun _ : ℕ => stepLaw d) = infinitePi fun _ : Fin d => frogMeasure d
  -- Use infinitePi_map_curry
  -- infinitePi_map_curry: (infinitePi fun p : ι × κ => μ p.1 p.2).map (curry ι κ X) = infinitePi fun i : ι => infinitePi fun j : κ => μ i j
  -- The LHS matches our target's LHS (after unfolding curry)
  have h_curry := MeasureTheory.Measure.infinitePi_map_curry (μ := fun (_ : Fin d) (_ : Vertex d) => Measure.infinitePi fun _ : ℕ => stepLaw d)
  -- h_curry: (infinitePi fun p : Fin d × Vertex d => ...).map (MeasurableEquiv.curry ...) = infinitePi fun i : Fin d => infinitePi fun j : Vertex d => ...
  simpa [curry, frogMeasure] using h_curry

/-- **The copies.** The copy curves are i.i.d. with law `curveLaw d K`. -/
theorem map_copyCurves_pi {d : ℕ} [NeZero d] (K : ℕ) :
    ((Measure.infinitePi fun _ : {u : StarSeg d // isParamSeg u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw d).prod
        (Measure.infinitePi fun _ : Fin d × ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d)).map
        (fun q => copyCurves K q.1 q.2) =
      Measure.pi fun _ : Fin d => curveLaw d K := by
  set ν := Measure.infinitePi fun _ : ℕ => stepLaw d with hν
  set P := Measure.infinitePi fun _ : {u : StarSeg d // isParamSeg u} => ν with hP
  set V := Measure.infinitePi fun _ : Fin d × ℕ => ν with hV
  set Zf : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) → Fin d → Sample d :=
    fun p c w => p ⟨(Sum.inl (w ++ [c]), 0), w ++ [c], rfl⟩ with hZf
  have hZ : Measurable Zf :=
    measurable_pi_iff.2 fun c => measurable_pi_iff.2 fun w => measurable_pi_apply _
  have hcur : Measurable (MeasurableEquiv.curry (Fin d) ℕ (ℕ → Step d)) :=
    (MeasurableEquiv.curry (Fin d) ℕ (ℕ → Step d)).measurable
  -- (1) the parameters of the copies and their entries
  have h1 : (P.prod V).map (Prod.map Zf (MeasurableEquiv.curry (Fin d) ℕ (ℕ → Step d))) =
      (Measure.infinitePi fun _ : Fin d => frogMeasure d).prod
        (Measure.infinitePi fun _ : Fin d => initMeasure d) := by
    rw [← Measure.map_prod_map _ _ hZ hcur, hP, hV, map_copyParams,
      Measure.infinitePi_map_curry (μ := fun _ _ => ν)]
    rfl
  -- (2) zip
  set zip : (Fin d → Sample d) × (Fin d → ℕ → ℕ → Step d) →
      (Fin d → Sample d × (ℕ → ℕ → Step d)) := fun q c => (q.1 c, q.2 c) with hzip
  have hzipm : Measurable zip := measurable_pi_iff.2 fun c =>
    ((measurable_pi_apply c).comp measurable_fst).prodMk ((measurable_pi_apply c).comp measurable_snd)
  have hunzip : Measurable fun z : Fin d → Sample d × (ℕ → ℕ → Step d) =>
      ((fun i => (z i).1, fun i => (z i).2) : (Fin d → Sample d) × (Fin d → ℕ → ℕ → Step d)) :=
    (measurable_pi_iff.2 fun i => (measurable_pi_apply i).fst).prodMk
      (measurable_pi_iff.2 fun i => (measurable_pi_apply i).snd)
  have h2 : ((Measure.infinitePi fun _ : Fin d => frogMeasure d).prod
        (Measure.infinitePi fun _ : Fin d => initMeasure d)).map zip =
      Measure.infinitePi fun _ : Fin d => (frogMeasure d).prod (initMeasure d) := by
    rw [← infinitePi_prod_map (frogMeasure d) (initMeasure d), Measure.map_map hzipm hunzip]
    have hid : zip ∘ (fun z : Fin d → Sample d × (ℕ → ℕ → Step d) =>
        ((fun i => (z i).1, fun i => (z i).2) : (Fin d → Sample d) × (Fin d → ℕ → ℕ → Step d))) =
        id := rfl
    rw [hid, Measure.map_id]
  -- (3) the curves of the copies
  have hcc := measurable_consCurve (d := d) K
  have h3 : (Measure.infinitePi fun _ : Fin d => (frogMeasure d).prod (initMeasure d)).map
      (fun z c => consCurve K (z c).1 (z c).2) = Measure.infinitePi fun _ : Fin d => curveLaw d K := by
    rw [Measure.infinitePi_map_pi _ (fun _ => hcc), ← curveLaw_eq_cons]
  have hC : Measurable fun z : Fin d → Sample d × (ℕ → ℕ → Step d) =>
      fun c => consCurve K (z c).1 (z c).2 :=
    measurable_pi_iff.2 fun c => hcc.comp (measurable_pi_apply c)
  have hA : Measurable (Prod.map Zf (MeasurableEquiv.curry (Fin d) ℕ (ℕ → Step d))) :=
    hZ.prodMap hcur
  have hfun : (fun q : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) × (Fin d × ℕ → ℕ → Step d) =>
      copyCurves K q.1 q.2) =
      (fun z : Fin d → Sample d × (ℕ → ℕ → Step d) => fun c => consCurve K (z c).1 (z c).2) ∘
        zip ∘ Prod.map Zf (MeasurableEquiv.curry (Fin d) ℕ (ℕ → Step d)) := by
    funext q
    rfl
  rw [hfun, ← Measure.map_map hC (hzipm.comp hA), ← Measure.map_map hzipm hA, h1, h2, h3,
    Measure.infinitePi_eq_pi]

/-- The copy curves are measurable. -/
theorem measurable_copyCurves {d : ℕ} (K : ℕ) :
    Measurable fun q : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) × (Fin d × ℕ → ℕ → Step d) =>
      copyCurves K q.1 q.2 := by
  have hcc := measurable_consCurve (d := d) K
  refine measurable_pi_iff.2 fun c => ?_
  have hpair : Measurable fun q : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) ×
      (Fin d × ℕ → ℕ → Step d) =>
      (((fun w => q.1 ⟨(Sum.inl (w ++ [c]), 0), w ++ [c], rfl⟩) : Sample d),
        fun i => q.2 (c, i)) :=
    (measurable_pi_iff.2 fun w => (measurable_pi_apply _).comp measurable_fst).prodMk
      (measurable_pi_iff.2 fun i => (measurable_pi_apply (c, i)).comp measurable_snd)
  have h := hcc.comp hpair
  exact h

/-- The copy curves and the directions. -/
theorem map_copyCurves {d : ℕ} [NeZero d] (K : ℕ) :
    (((Measure.infinitePi fun _ : {u : StarSeg d // isParamSeg u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw d).prod (dirMeasure d)).prod
        (Measure.infinitePi fun _ : Fin d × ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d)).map
        (fun q => (copyCurves K q.1.1 q.2, q.1.2)) =
      (Measure.pi fun _ : Fin d => curveLaw d K).prod (dirMeasure d) := by
  set P := Measure.infinitePi fun _ : {u : StarSeg d // isParamSeg u} =>
    Measure.infinitePi fun _ : ℕ => stepLaw d with hP
  set V := Measure.infinitePi fun _ : Fin d × ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d
    with hV
  have hcc := measurable_copyCurves (d := d) K
  have e1 := (measurePreserving_prodAssoc P (dirMeasure d) V).map_eq
  have e2 : (P.prod ((dirMeasure d).prod V)).map (Prod.map id Prod.swap) =
      P.prod (V.prod (dirMeasure d)) := by
    rw [← Measure.map_prod_map _ _ measurable_id measurable_swap, Measure.map_id,
      Measure.prod_swap]
  have e3 := (measurePreserving_prodAssoc P V (dirMeasure d)).symm.map_eq
  have e4 : ((P.prod V).prod (dirMeasure d)).map
      (Prod.map (fun q => copyCurves K q.1 q.2) id) =
      (Measure.pi fun _ : Fin d => curveLaw d K).prod (dirMeasure d) := by
    rw [← Measure.map_prod_map _ _ hcc measurable_id, map_copyCurves_pi, Measure.map_id]
  have hfun : (fun q : (({u : StarSeg d // isParamSeg u} → ℕ → Step d) × (ℕ → Fin (d + 1))) ×
      (Fin d × ℕ → ℕ → Step d) => (copyCurves K q.1.1 q.2, q.1.2)) =
      Prod.map (fun q => copyCurves K q.1 q.2) id ∘
        (MeasurableEquiv.prodAssoc (α := {u : StarSeg d // isParamSeg u} → ℕ → Step d)
          (β := Fin d × ℕ → ℕ → Step d) (γ := ℕ → Fin (d + 1))).symm ∘
        Prod.map id Prod.swap ∘
        (MeasurableEquiv.prodAssoc (α := {u : StarSeg d // isParamSeg u} → ℕ → Step d)
          (β := ℕ → Fin (d + 1)) (γ := Fin d × ℕ → ℕ → Step d)) := by
    funext q
    rfl
  have m1 := (MeasurableEquiv.prodAssoc (α := {u : StarSeg d // isParamSeg u} → ℕ → Step d)
    (β := ℕ → Fin (d + 1)) (γ := Fin d × ℕ → ℕ → Step d)).measurable
  have m2 : Measurable (Prod.map id Prod.swap : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) ×
      ((ℕ → Fin (d + 1)) × (Fin d × ℕ → ℕ → Step d)) → _) := measurable_id.prodMap measurable_swap
  have m3 := (MeasurableEquiv.prodAssoc (α := {u : StarSeg d // isParamSeg u} → ℕ → Step d)
    (β := Fin d × ℕ → ℕ → Step d) (γ := ℕ → Fin (d + 1))).symm.measurable
  have m4 : Measurable (Prod.map (fun q : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) ×
      (Fin d × ℕ → ℕ → Step d) => copyCurves K q.1 q.2) (id : (ℕ → Fin (d + 1)) → _)) :=
    hcc.prodMap measurable_id
  rw [hfun, ← Measure.map_map m4 (m3.comp (m2.comp m1)), ← Measure.map_map m3 (m2.comp m1),
    ← Measure.map_map m2 m1, e1, e2, e3, e4]

/-- The child curves and the directions through the parameter and the pieces read. -/
theorem childS_dirS_eq {d : ℕ} (K : ℕ) (π : StarSeg d → ℕ → Step d) :
    (childS K π, dirS K π) =
      (copyCurves K (paramOf π) (thinS (dirTail (readS K π)).1 (dirTail (readS K π)).2),
        (dirTail (readS K π)).1) := by
  refine Prod.ext ?_ rfl
  funext c
  simp only [childS, copyCurves, consCurve]
  congr 1

/-- The pieces read are measurable in the pieces. -/
theorem measurable_readS {d : ℕ} (K : ℕ) :
    Measurable fun π : StarSeg d → ℕ → Step d => readS K π := by
  exact measurable_pi_iff.2 fun k => measurable_read (fun π => procS K π k)
    (fun u => measurableSet_procS_eq K k u)

/-- Thinning is measurable. -/
theorem measurable_thinS {d : ℕ} :
    Measurable fun q : (ℕ → Fin (d + 1)) × (ℕ → ℕ → Step d) => thinS q.1 q.2 := by
  refine measurable_pi_iff.2 fun ci => ?_
  have hidx : Measurable fun D : ℕ → Fin (d + 1) => Nat.nth (fun k => D k = ci.1.succ) ci.2 :=
    measurable_to_countable' fun n => measurableSet_nth_eq ci.1.succ ci.2 n
  have hF : Measurable fun q : ℕ × (ℕ → ℕ → Step d) => q.2 q.1 :=
    measurable_from_prod_countable_right fun n => measurable_pi_apply n
  have h := hF.comp ((hidx.comp measurable_fst).prodMk measurable_snd)
  exact h

/-- **The law of the child curves and the directions.** -/
theorem map_childS_dirS {d : ℕ} [NeZero d] (K : ℕ) :
    (pieceMeasure d).map (fun π => (childS K π, dirS K π)) =
      (Measure.pi fun _ : Fin d => curveLaw d K).prod (dirMeasure d) := by
  have hdt0 : Measurable (dirTail (d := d)) := by unfold dirTail; fun_prop
  have hread : Measurable fun π : StarSeg d → ℕ → Step d => (paramOf π, readS K π) :=
    (measurable_pi_iff.2 fun u => measurable_pi_apply _).prodMk (measurable_readS K)
  have hdt : Measurable fun q : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) ×
      (ℕ → ℕ → Step d) => (q.1, dirTail q.2) := measurable_fst.prodMk (hdt0.comp measurable_snd)
  have hassoc : Measurable fun q : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) ×
      ((ℕ → Fin (d + 1)) × (ℕ → ℕ → Step d)) => ((q.1, q.2.1), q.2.2) := by fun_prop
  have hthin : Measurable fun q : (({u : StarSeg d // isParamSeg u} → ℕ → Step d) ×
      (ℕ → Fin (d + 1))) × (ℕ → ℕ → Step d) => (q.1, thinS q.1.2 q.2) :=
    measurable_fst.prodMk (measurable_thinS.comp ((measurable_snd.comp measurable_fst).prodMk
      measurable_snd))
  have hΦ : Measurable fun q : (({u : StarSeg d // isParamSeg u} → ℕ → Step d) ×
      (ℕ → Fin (d + 1))) × (Fin d × ℕ → ℕ → Step d) => (copyCurves K q.1.1 q.2, q.1.2) :=
    ((measurable_copyCurves K).comp ((measurable_fst.comp measurable_fst).prodMk
      measurable_snd)).prodMk (measurable_snd.comp measurable_fst)
  have hfun : (fun π => (childS K π, dirS K π)) =
      (fun q : (({u : StarSeg d // isParamSeg u} → ℕ → Step d) × (ℕ → Fin (d + 1))) ×
        (Fin d × ℕ → ℕ → Step d) => (copyCurves K q.1.1 q.2, q.1.2)) ∘
      (fun q : (({u : StarSeg d // isParamSeg u} → ℕ → Step d) × (ℕ → Fin (d + 1))) ×
        (ℕ → ℕ → Step d) => (q.1, thinS q.1.2 q.2)) ∘
      (fun q : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) ×
        ((ℕ → Fin (d + 1)) × (ℕ → ℕ → Step d)) => ((q.1, q.2.1), q.2.2)) ∘
      (fun q : ({u : StarSeg d // isParamSeg u} → ℕ → Step d) × (ℕ → ℕ → Step d) =>
        (q.1, dirTail q.2)) ∘
      (fun π => (paramOf π, readS K π)) := by
    funext π
    exact childS_dirS_eq K π
  have h2 : ((Measure.infinitePi fun _ : {u : StarSeg d // isParamSeg u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw d).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d)).map
        (fun q => (q.1, dirTail q.2)) =
      (Measure.infinitePi fun _ : {u : StarSeg d // isParamSeg u} =>
        Measure.infinitePi fun _ : ℕ => stepLaw d).prod ((dirMeasure d).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d)) := by
    rw [← map_dirTail, ← Measure.map_id (μ := Measure.infinitePi fun _ : {u : StarSeg d //
      isParamSeg u} => Measure.infinitePi fun _ : ℕ => stepLaw d), Measure.map_prod_map _ _
      measurable_id hdt0, Measure.map_id]
    rfl
  have h3 := (MeasureTheory.measurePreserving_prodAssoc (Measure.infinitePi fun _ :
    {u : StarSeg d // isParamSeg u} => Measure.infinitePi fun _ : ℕ => stepLaw d) (dirMeasure d)
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d)).symm.map_eq
  rw [hfun, ← Measure.map_map hΦ (hthin.comp (hassoc.comp (hdt.comp hread))),
    ← Measure.map_map hthin (hassoc.comp (hdt.comp hread)),
    ← Measure.map_map hassoc (hdt.comp hread), ← Measure.map_map hdt hread, map_readS, h2]
  erw [h3]
  rw [map_thinS, map_copyCurves]

/-- The child curves and the directions are measurable in the pieces. -/
theorem measurable_childS_dirS {d : ℕ} (K : ℕ) :
    Measurable fun π : StarSeg d → ℕ → Step d => (childS K π, dirS K π) := by
  have hdt0 : Measurable (dirTail (d := d)) := by unfold dirTail; fun_prop
  have hfun : (fun π : StarSeg d → ℕ → Step d => (childS K π, dirS K π)) = fun π =>
      (copyCurves K (paramOf π) (thinS (dirTail (readS K π)).1 (dirTail (readS K π)).2),
        (dirTail (readS K π)).1) := funext (childS_dirS_eq K)
  rw [hfun]
  have hY : Measurable fun π : StarSeg d → ℕ → Step d => dirTail (readS K π) :=
    hdt0.comp (measurable_readS K)
  have hT : Measurable fun π : StarSeg d → ℕ → Step d =>
      thinS (dirTail (readS K π)).1 (dirTail (readS K π)).2 := measurable_thinS.comp hY
  have hp : Measurable fun π : StarSeg d → ℕ → Step d => paramOf π :=
    measurable_pi_iff.2 fun u => measurable_pi_apply _
  have hpair : Measurable fun π : StarSeg d → ℕ → Step d =>
      (paramOf π, thinS (dirTail (readS K π)).1 (dirTail (readS K π)).2) := hp.prodMk hT
  have hC := (measurable_copyCurves K).comp hpair
  exact hC.prodMk hY.fst

/-- Every direction occurs infinitely often, almost surely. -/
theorem ae_dirS_infinite {d : ℕ} [NeZero d] (K : ℕ) :
    ∀ᵐ π ∂(pieceMeasure d), {k | dirS K π k = 0}.Infinite := by
  have hs : ((Measure.pi fun _ : Fin d => curveLaw d K).prod (dirMeasure d)).map Prod.snd =
      dirMeasure d := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hae : ∀ᵐ x ∂((Measure.pi fun _ : Fin d => curveLaw d K).prod (dirMeasure d)),
      {k | x.2 k = 0}.Infinite := by
    refine ae_of_ae_map (p := fun D : ℕ → Fin (d + 1) => {k | D k = 0}.Infinite)
      measurable_snd.aemeasurable ?_
    rw [hs]
    unfold dirMeasure
    filter_upwards [ae_infinite_eq (A := Fin (d + 1))] with D hD
    exact hD 0
  rw [← map_childS_dirS K] at hae
  exact ae_of_ae_map (p := fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) => {k | x.2 k = 0}.Infinite)
    (measurable_childS_dirS K).aemeasurable hae

/-! ### Kill depth `0` -/

/-- At kill depth `0` the curve counts the initial frogs whose first step goes to the parent. -/
theorem curveK_zero_eq {d : ℕ} (ζ : Sample d) (ξ : ℕ → ℕ → Step d) (j : ℕ) :
    curveK 0 ζ ξ j = dirCount (fun a => (ξ a 0).2) 0 j := by
  unfold curveK
  have h_visits_none_iff {d : ℕ} (x : ℕ → Step d) :
      visitsK 0 (some []) x none ↔ (x 0).2 = (0 : Fin (d + 1)) := by
    constructor
    · intro h
      rcases h with ⟨n, hn, h_depth⟩
      by_contra! h_ne
      have hn_pos : 1 ≤ n := by
        by_contra! h_not
        have hn0 : n = 0 := by omega
        subst hn0
        simp [walkStar] at hn
      have h_depth_1 : depthStar (walkStar (some []) x 1) ≤ 0 := h_depth 1 hn_pos
      have h_walk_1 : walkStar (some []) x 1 = stepStar (some []) (x 0) := rfl
      have h_step : stepStar (some []) (x 0) = some ((x 0).2.pred h_ne :: []) := by
        simp [stepStar, h_ne]
      rw [h_walk_1, h_step] at h_depth_1
      unfold depthStar at h_depth_1
      simp at h_depth_1
    · intro h
      refine ⟨1, ?_, ?_⟩
      · calc
          walkStar (some []) x 1 = stepStar (some []) (x 0) := rfl
          _ = none := by
            simp [stepStar, h]
      · intro i hi
        have hi_le : i ≤ 1 := hi
        rcases Nat.eq_zero_or_pos i with (rfl | h_pos)
        · simp [depthStar, walkStar]
        · have hi_le' : i = 1 := by omega
          subst hi_le'
          have h_walk : walkStar (some []) x 1 = none := by
            calc
              walkStar (some []) x 1 = stepStar (some []) (x 0) := rfl
              _ = none := by
                simp [stepStar, h]
          simp [h_walk, depthStar]
  have h_visits_some_ne_nil {d : ℕ} (x : ℕ → Step d) (v : Vertex d) (hv : v ≠ []) :
      ¬ visitsK 0 (some []) x (some v) := by
    intro h
    rcases h with ⟨n, hn, h_depth⟩
    have h_depth_v : depthStar (walkStar (some []) x n) ≤ 0 := h_depth n (le_refl n)
    rw [hn] at h_depth_v
    unfold depthStar at h_depth_v
    have h_len : v.length = 0 := Nat.eq_zero_of_le_zero h_depth_v
    have h_empty : v = [] := by
      apply List.eq_nil_of_length_eq_zero h_len
    exact hv h_empty
  have h_second_empty : {b : Vertex d | reachedK 0 ζ ξ j b ∧ visitsK 0 (some b) (ζ b) none}.encard = 0 := by
    apply Set.encard_eq_zero.mpr
    ext b
    simp
    intro h_reached h_visits
    rcases h_reached with ⟨a, ha, v, hv_ne, hv_visits, h_refl⟩
    exact h_visits_some_ne_nil (ξ a) v hv_ne hv_visits
  rw [h_second_empty, add_zero]
  have h_first_set_eq : {a : ℕ | a < j ∧ visitsK 0 (some []) (ξ a) none} =
      {k : ℕ | (k : ℕ∞) < (j : ℕ∞) ∧ (ξ k 0).2 = (0 : Fin (d + 1))} := by
    ext a
    constructor
    · intro ⟨ha, h_visits⟩
      have h_dir : (ξ a 0).2 = (0 : Fin (d + 1)) := (h_visits_none_iff (ξ a)).mp h_visits
      have ha_cast : (a : ℕ∞) < (j : ℕ∞) := by exact_mod_cast ha
      exact ⟨ha_cast, h_dir⟩
    · intro ⟨ha_cast, h_dir⟩
      have ha : a < j := by exact_mod_cast ha_cast
      have h_visits : visitsK 0 (some []) (ξ a) none := (h_visits_none_iff (ξ a)).mpr h_dir
      exact ⟨ha, h_visits⟩
  rw [h_first_set_eq]
  rfl

/-- The first directions of the initial frogs are i.i.d. uniform. -/
theorem map_dirZero {d : ℕ} [NeZero d] :
    (initMeasure d).map (fun ξ a => (ξ a 0).2) = dirMeasure d := by
  have hmeas : ∀ (a : ℕ), Measurable (fun (y : ℕ → Step d) => (y 0).2) := by
    intro a
    have h1 : Measurable (fun (y : ℕ → Step d) => y 0) := measurable_pi_apply 0
    -- h1 : Measurable (fun y => y 0) where y 0 : Step d = Fin d × Fin (d+1)
    -- measurable_snd : Measurable (Prod.snd : Step d → Fin (d+1))
    -- We need: Measurable (Prod.snd ∘ (fun y => y 0)) = Measurable (fun y => (y 0).2)
    have h2 : Measurable (Prod.snd : Step d → Fin (d + 1)) := measurable_snd
    exact h2.comp h1
  rw [initMeasure]
  have h := Measure.infinitePi_map_pi (μ := fun (_ : ℕ) => (Measure.infinitePi fun _ : ℕ => stepLaw d))
    (f := fun (_ : ℕ) => (fun (y : ℕ → Step d) => (y 0).2)) hmeas
  rw [h, dirMeasure]
  have h_inner : (fun (a : ℕ) => ((Measure.infinitePi fun _ : ℕ => stepLaw d).map fun y => (y 0).2)) =
      (fun (_ : ℕ) => (uniformOn Set.univ : Measure (Fin (d + 1)))) := by
    funext a
    have h_eval : (Measure.infinitePi fun _ : ℕ => stepLaw d).map (fun (y : ℕ → Step d) => y 0) = stepLaw d := by
      simpa using Measure.infinitePi_map_eval (μ := fun _ : ℕ => stepLaw d) 0
    calc
      ((Measure.infinitePi fun _ : ℕ => stepLaw d).map fun y => (y 0).2)
          = ((Measure.infinitePi fun _ : ℕ => stepLaw d).map fun y => y 0).map Prod.snd := by
        rw [Measure.map_map (g := Prod.snd) (f := fun (y : ℕ → Step d) => y 0)]
        · rfl
        · exact measurable_snd
        · exact measurable_pi_apply 0
      _ = (stepLaw d).map Prod.snd := by rw [h_eval]
      _ = (uniformOn Set.univ : Measure (Fin (d + 1))) := map_snd_stepLaw
  rw [h_inner]

/-- The counts of the direction `0` are measurable in the directions. -/
theorem measurable_dirCount_zero {d : ℕ} :
    Measurable fun D : ℕ → Fin (d + 1) => fun j : ℕ => dirCount D 0 j := by
  exact measurable_pi_iff.2 fun j => FrogModel.LemmaX.measurable_dirCount 0 (j : ℕ∞)

/-- `Psi` of the zero curve. -/
theorem psiLaw_dirac_zero {d : ℕ} [NeZero d] :
    psiLaw d (Measure.dirac 0) = (dirMeasure d).map (fun D (j : ℕ) => dirCount D 0 j) := by
  unfold psiLaw
  have hpi : (Measure.pi fun _ : Fin d => Measure.dirac (0 : ℕ → ℕ∞)) =
      Measure.dirac (fun _ : Fin d => (0 : ℕ → ℕ∞)) := by
    rw [← Measure.infinitePi_eq_pi]
    exact Measure.infinitePi_dirac (fun _ : Fin d => (0 : ℕ → ℕ∞))
  rw [hpi, Measure.dirac_prod, Measure.map_map measurable_psiG measurable_prodMk_left]
  congr 1
  funext D j
  simp only [Function.comp_apply, psiG]
  rw [show (fun _ : Fin d => (0 : ℕ → ℕ∞)) = (fun _ _ => 0 : Fin d → ℕ → ℕ∞) from rfl,
    psiN_of_zero]

end FrogModel.Recursion
