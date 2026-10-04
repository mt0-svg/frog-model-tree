module

public import FrogModel.D3.LaneA.Indep
public import FrogModel.D3.LaneA.Meas

@[expose] public section

/-!
# The piece space of Lemma 11.5 of the paper and its sub-models (d = 3)

The proof of Lemma 11.5. With `j` entrants and a depth `D ≥ 1`, every frog path is
glued from three pieces (`PSpace`, law `pieceMeasure`): an initial frog (`initF j i`, the entrants
and the frog of `w`) follows piece 0 up to its first time at depth `D` (`hitD D`), piece 1 up to its
first time back at depth `D - 1` (`exitTime []` of piece 1, read from the vertex reached), then
piece 2; the frog of a vertex `u ++ v` with `|v| = D` follows piece 0 up to its first time at depth
`D - 1` (`exitTime u`), then piece 1; the other frogs follow piece 0. The glued paths have the law
`pathMeasure` (`map_glueP`).

When the initial frog `i` first reaches depth `D` at `v` (`firstD D` of its piece 0), the planted
model of height `M - D` at `v` with one entrant reads its piece 1 and the pieces 0 of the frogs of
`T(v)` (`subPaths`, an injective reindexing, law `pathMeasure`: `map_subPaths`). Its woken frogs
are woken in the glued model at height `M` (`woken_lift`), and those whose sub-path reaches the
parent of `v` and whose next piece reaches depth `-(D - 1)` are at `w` at some time
(`reach_root`), so they give distinct presences at `w` (`presN_ge`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA

open FrogModel FrogModel.D3.Iface FrogModel.ZeroOne

/-- The piece space: one step sequence for every pair (frog, piece index). -/
abbrev PSpace := PFrog × ℕ → ℕ → Step 3

/-- The law of the pieces: all i.i.d. -/
noncomputable def pieceMeasure : Measure PSpace :=
  Measure.infinitePi fun _ : PFrog × ℕ => LemmaR.seqLaw 3

instance : IsProbabilityMeasure pieceMeasure := by unfold pieceMeasure; infer_instance

/-- The initial frogs at `w` with `j` entrants: `inl i` for `i < j`, and the frog `inr []` of `w`
for `i = j`. -/
def initF (j i : ℕ) : PFrog := if i < j then Sum.inl i else Sum.inr []

theorem frogStart_initF (j i : ℕ) : frogStart (initF j i) = [] := by
  unfold initF
  split_ifs <;> rfl

theorem initF_injective {j i i' : ℕ} (hi : i ≤ j) (hi' : i' ≤ j) (h : initF j i = initF j i') :
    i = i' := by
  unfold initF at h
  split_ifs at h with h1 h2 h2 <;> first | omega | exact Sum.inl_injective h

theorem initF_ne_inr (j i : ℕ) {w : Vertex 3} (hw : w ≠ []) : initF j i ≠ Sum.inr w := by
  unfold initF
  split_ifs
  · exact Sum.inl_ne_inr
  · intro h
    exact hw (Sum.inr_injective h).symm

open Classical in
/-- The stopping time of piece 0. -/
noncomputable def e0 (j D : ℕ) : PFrog → (ℕ → Step 3) → ℕ∞
  | Sum.inl i => if i < j then hitD D else fun _ => ⊤
  | Sum.inr w =>
    if w = [] then hitD D else if D ≤ w.length then exitTime (w.take (w.length - D))
    else fun _ => ⊤

open Classical in
/-- The stopping time of piece 1. -/
noncomputable def e1 (j : ℕ) : PFrog → (ℕ → Step 3) → ℕ∞
  | Sum.inl i => if i < j then exitTime [] else fun _ => ⊤
  | Sum.inr w => if w = [] then exitTime [] else fun _ => ⊤

/-- The glued frog paths. -/
noncomputable def glueP (j D : ℕ) (ω : PSpace) : PFrog → ℕ → Step 3 := fun φ =>
  glueAt (e0 j D φ (ω (φ, 0))) (ω (φ, 0)) (glueAt (e1 j φ (ω (φ, 1))) (ω (φ, 1)) (ω (φ, 2)))

/-- A stopping time of a step sequence. -/
def IsStop (e : (ℕ → Step 3) → ℕ∞) : Prop :=
  ∀ (a a' : ℕ → Step 3) (k : ℕ), e a = k → (∀ i < k, a i = a' i) → e a' = k

theorem isStop_top : IsStop fun _ => ⊤ := fun _ _ k h _ => (ENat.top_ne_natCast k h).elim

theorem isStop_hitD (D : ℕ) : IsStop (hitD D) := hitD_stop D

theorem isStop_exitTime (u : Vertex 3) : IsStop (exitTime u) := exitTime_eq_of_prefix u

theorem isStop_e0 (j D : ℕ) (φ : PFrog) : IsStop (e0 j D φ) := by
  cases φ with
  | inl i =>
    simp only [e0]
    split_ifs
    · exact isStop_hitD D
    · exact isStop_top
  | inr w =>
    simp only [e0]
    split_ifs
    · exact isStop_hitD D
    · exact isStop_exitTime _
    · exact isStop_top

theorem isStop_e1 (j : ℕ) (φ : PFrog) : IsStop (e1 j φ) := by
  cases φ with
  | inl i =>
    simp only [e1]
    split_ifs
    · exact isStop_exitTime _
    · exact isStop_top
  | inr w =>
    simp only [e1]
    split_ifs
    · exact isStop_exitTime _
    · exact isStop_top

theorem measurable_e0 (j D : ℕ) (φ : PFrog) : Measurable (e0 j D φ) := by
  cases φ with
  | inl i =>
    simp only [e0]
    split_ifs
    · exact measurable_hitD D
    · exact measurable_const
  | inr w =>
    simp only [e0]
    split_ifs
    · exact measurable_hitD D
    · exact measurable_exitTime _
    · exact measurable_const

theorem measurable_e1 (j : ℕ) (φ : PFrog) : Measurable (e1 j φ) := by
  cases φ with
  | inl i =>
    simp only [e1]
    split_ifs
    · exact measurable_exitTime _
    · exact measurable_const
  | inr w =>
    simp only [e1]
    split_ifs
    · exact measurable_exitTime _
    · exact measurable_const

theorem measurable_glueP (j D : ℕ) : Measurable (glueP j D) := by
  refine Measurable.of_eval fun φ => ?_
  have hp1 : Measurable fun ω : PSpace => (ω (φ, 1), ω (φ, 2)) :=
    (measurable_pi_apply (φ, 1)).prodMk (measurable_pi_apply (φ, 2))
  have h1 : Measurable fun ω : PSpace =>
      glueAt (e1 j φ (ω (φ, 1))) (ω (φ, 1)) (ω (φ, 2)) :=
    (measurable_glueAt _ (measurable_e1 j φ)).comp hp1
  have hp0 : Measurable fun ω : PSpace =>
      (ω (φ, 0), glueAt (e1 j φ (ω (φ, 1))) (ω (φ, 1)) (ω (φ, 2))) :=
    (measurable_pi_apply (φ, 0)).prodMk h1
  exact (measurable_glueAt _ (measurable_e0 j D φ)).comp hp0

/-- **The glued paths have the law of the frog paths.** -/
theorem map_glueP (j D : ℕ) : pieceMeasure.map (glueP j D) = pathMeasure :=
  map_glue3 (stepLaw 3) (e0 j D) (e1 j) (fun φ => isStop_e0 j D φ) (fun φ => isStop_e1 j φ)
    (fun φ => measurable_e0 j D φ) (fun φ => measurable_e1 j φ)

/-! ### The glued paths of the initial frogs and of the frogs below depth `D` -/

theorem e0_initF (j D i : ℕ) : e0 j D (initF j i) = hitD D := by
  unfold initF
  split_ifs with h
  · simp only [e0]
    rw [ite_eq_left h]
  · simp only [e0]
    rw [ite_eq_left trivial]

theorem e1_initF (j i : ℕ) : e1 j (initF j i) = exitTime [] := by
  unfold initF
  split_ifs with h
  · simp only [e1]
    rw [ite_eq_left h]
  · simp only [e1]
    rw [ite_eq_left trivial]

theorem glueP_init (j D i : ℕ) (ω : PSpace) :
    glueP j D ω (initF j i) = glueAt (hitD D (ω (initF j i, 0))) (ω (initF j i, 0))
      (glueAt (exitTime [] (ω (initF j i, 1))) (ω (initF j i, 1)) (ω (initF j i, 2))) := by
  unfold glueP
  rw [e0_initF, e1_initF]

theorem glueP_deep (j D : ℕ) (hD : 1 ≤ D) (u v : Vertex 3) (hv : v.length = D) (ω : PSpace) :
    glueP j D ω (Sum.inr (u ++ v)) = glueAt (exitTime u (ω (Sum.inr (u ++ v), 0)))
      (ω (Sum.inr (u ++ v), 0)) (ω (Sum.inr (u ++ v), 1)) := by
  have hne : u ++ v ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_nil] at this
    omega
  have hle : D ≤ (u ++ v).length := by
    rw [List.length_append]
    omega
  have htake : (u ++ v).take ((u ++ v).length - D) = u := by
    have : (u ++ v).length - D = u.length := by
      rw [List.length_append]
      omega
    rw [this, List.take_left]
  have h0 : e0 j D (Sum.inr (u ++ v)) = exitTime u := by
    simp only [e0]
    rw [ite_eq_right hne, ite_eq_left hle, htake]
  have h1 : e1 j (Sum.inr (u ++ v)) = fun _ => ⊤ := by
    simp only [e1]
    rw [ite_eq_right hne]
  unfold glueP
  rw [h0, h1, glueAt_top]

/-- Position of an initial frog after its first time `k` at depth `D`. -/
theorem pos_init_add (j D i : ℕ) (ω : PSpace) (v : Vertex 3) (k : ℕ)
    (hk : hitD D (ω (initF j i, 0)) = k) (hkv : walkStar (some []) (ω (initF j i, 0)) k = some v)
    (s : ℕ) :
    pos (glueP j D ω) (initF j i) (k + s) =
      walkStar (some v)
        (glueAt (exitTime [] (ω (initF j i, 1))) (ω (initF j i, 1)) (ω (initF j i, 2))) s := by
  unfold pos
  rw [frogStart_initF, glueP_init j D i ω, hk, walkStar_glueAt_add, hkv]

/-! ### The sub-model at a vertex of depth `D` -/

/-- The coordinates read by the sub-model at `v` with entrant `φ`: its entrant `inl 0` reads piece
1 of `φ` (the entrants `inl (i + 1)`, never woken, read the unused pieces `i + 3`), the frog `inr u`
reads piece 0 of the frog of `u ++ v`. -/
def subIdx (φ : PFrog) (v : Vertex 3) : PFrog → PFrog × ℕ
  | Sum.inl 0 => (φ, 1)
  | Sum.inl (i + 1) => (φ, i + 3)
  | Sum.inr u => (Sum.inr (u ++ v), 0)

/-- The frog paths of the sub-model at `v` with entrant `φ`. -/
def subPaths (ω : PSpace) (φ : PFrog) (v : Vertex 3) : PFrog → ℕ → Step 3 :=
  fun ψ => ω (subIdx φ v ψ)

/-- The piece that continues the path of a sub-model frog after it reaches the parent of `v`. -/
def contIdx (φ : PFrog) (v : Vertex 3) : PFrog → PFrog × ℕ
  | Sum.inl _ => (φ, 2)
  | Sum.inr u => (Sum.inr (u ++ v), 1)

/-- The frog of the glued model for a frog of the sub-model. -/
def liftF (φ : PFrog) (v : Vertex 3) : PFrog → PFrog
  | Sum.inl _ => φ
  | Sum.inr u => Sum.inr (u ++ v)

theorem subIdx_injective (φ : PFrog) (v : Vertex 3) :
    Function.Injective (subIdx φ v) := by
  intro a b h
  rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;>
    simp only [subIdx, Prod.mk.injEq] at h
  all_goals first
    | rfl
    | (exfalso; obtain ⟨-, h2⟩ := h; omega)
    | (obtain ⟨-, h2⟩ := h; congr 1; omega)
    | exact absurd h.1 (hφ _)
    | exact absurd h.1.symm (hφ _)
    | (congr 1; exact List.append_cancel_right (Sum.inr_injective h.1))

theorem measurable_subPaths (φ : PFrog) (v : Vertex 3) :
    Measurable fun ω : PSpace => subPaths ω φ v :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **The sub-model has the law of the frog paths.** -/
theorem map_subPaths (φ : PFrog) (v : Vertex 3) :
    pieceMeasure.map (fun ω => subPaths ω φ v) = pathMeasure :=
  infinitePi_map_comp (LemmaR.seqLaw 3) (subIdx φ v) (subIdx_injective φ v)

/-- A woken frog of a model with one entrant is the entrant `inl 0` or the frog of a vertex. -/
theorem woken_one_inl {m : ℕ} {π : PFrog → ℕ → Step 3} {i : ℕ} (h : Woken m 1 π (Sum.inl i)) :
    i = 0 := by
  cases h with
  | ent i hi => omega

theorem woken_inr_length {m k : ℕ} {π : PFrog → ℕ → Step 3} {u : Vertex 3}
    (h : Woken m k π (Sum.inr u)) : u.length ≤ m := by
  cases h with
  | wake φ v n _ hv _ => exact hv

theorem initF_woken (M j i : ℕ) (hj : 1 ≤ j) (π : PFrog → ℕ → Step 3) :
    Woken M j π (initF j i) := by
  unfold initF
  split_ifs with h
  · exact Woken.ent i h
  · exact Woken.wake (Sum.inl 0) [] 0 (Woken.ent 0 hj) (by simp) rfl

section Lift

variable {M j D i : ℕ} {ω : PSpace} {v : Vertex 3}

theorem v_ne_nil (hD : 1 ≤ D) (hvD : v.length = D) : v ≠ [] := by
  rintro rfl
  simp at hvD
  omega

theorem initF_not_below (hD : 1 ≤ D) (hvD : v.length = D) (u : Vertex 3) :
    initF j i ≠ Sum.inr (u ++ v) :=
  initF_ne_inr j i fun h => v_ne_nil hD hvD (List.append_eq_nil_iff.1 h).2

/-- **The sub-model's woken frogs are woken in the glued model.** -/
theorem woken_lift (hj : 1 ≤ j) (hD : 1 ≤ D) (hDM : D ≤ M)
    (hv : firstD D (ω (initF j i, 0)) = some v) (ψ : PFrog)
    (hψ : Woken (M - D) 1 (subPaths ω (initF j i) v) ψ) :
    Woken M j (glueP j D ω) (liftF (initF j i) v ψ) := by
  obtain ⟨k, hk, hkv, hvD⟩ := firstD_spec D _ v hv
  have hvne := v_ne_nil hD hvD
  induction hψ with
  | ent i' hi' =>
    exact initF_woken M j i hj _
  | wake ψ' u n hψ' hu hpos ih =>
    have hlen : (u ++ v).length ≤ M := by
      rw [List.length_append]
      omega
    rcases ψ' with i' | u''
    · obtain rfl := woken_one_inl hψ'
      refine Woken.wake (liftF (initF j i) v (Sum.inl 0)) (u ++ v) (k + n) ih hlen ?_
      simp only [liftF]
      rw [pos_init_add j D i ω v k hk hkv n]
      exact walkStar_glue_copy hvne [] u _ _ n hpos
    · refine Woken.wake (liftF (initF j i) v (Sum.inr u'')) (u ++ v) n ih hlen ?_
      simp only [liftF]
      unfold pos
      rw [glueP_deep j D hD u'' v hvD ω]
      exact walkStar_glue_copy hvne u'' u _ _ n hpos

/-- **A counted sub-model frog whose next piece goes up `D - 1` levels is at `w`.** -/
theorem reach_root (hD : 1 ≤ D)
    (hv : firstD D (ω (initF j i, 0)) = some v) (ψ : PFrog)
    (hψ : Woken (M - D) 1 (subPaths ω (initF j i) v) ψ)
    (hreach : ∃ n, pos (subPaths ω (initF j i) v) ψ n = none)
    (hH : HitsDown (D - 1) (ω (contIdx (initF j i) v ψ))) :
    ∃ t, pos (glueP j D ω) (liftF (initF j i) v ψ) t = some [] := by
  obtain ⟨k, hk, hkv, hvD⟩ := firstD_spec D _ v hv
  have hvne := v_ne_nil hD hvD
  have htail : v.tail.length = D - 1 := by simp [hvD]
  rcases ψ with i' | u
  · obtain rfl := woken_one_inl hψ
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1
      ((exitTime_ne_top_iff [] (ω (initF j i, 1))).2 hreach)
    obtain ⟨s, hs⟩ := exists_walkStar_root v.tail (ω (initF j i, 2)) (by rw [htail]; exact hH)
    refine ⟨k + (r + s), ?_⟩
    simp only [liftF]
    rw [pos_init_add j D i ω v k hk hkv]
    exact (walkStar_glue_exit hvne [] _ _ r hr.symm s).trans hs
  · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1
      ((exitTime_ne_top_iff u (ω (Sum.inr (u ++ v), 0))).2 hreach)
    obtain ⟨s, hs⟩ := exists_walkStar_root v.tail (ω (Sum.inr (u ++ v), 1))
      (by rw [htail]; exact hH)
    refine ⟨r + s, ?_⟩
    simp only [liftF]
    unfold pos
    rw [glueP_deep j D hD u v hvD ω]
    exact (walkStar_glue_exit hvne u _ _ r hr.symm s).trans hs

/-- The sub-model's counted frogs: woken, and their sub-path reaches the parent of `v`. -/
def subCounted (ω : PSpace) (φ : PFrog) (v : Vertex 3) (m : ℕ) : Set PFrog :=
  {ψ | Woken m 1 (subPaths ω φ v) ψ ∧ ∃ n, pos (subPaths ω φ v) ψ n = none}

/-- **The presences at `w` are at least the counted sub-model frogs whose next piece goes up
`D - 1` levels.** -/
theorem presN_ge (hj : 1 ≤ j) (hD : 1 ≤ D) (hDM : D ≤ M)
    (hv : firstD D (ω (initF j i, 0)) = some v) :
    (subCounted ω (initF j i) v (M - D) ∩
        {ψ | HitsDown (D - 1) (ω (contIdx (initF j i) v ψ))}).encard ≤
      presN M j (glueP j D ω) := by
  classical
  obtain ⟨k, hk, hkv, hvD⟩ := firstD_spec D _ v hv
  set S := subCounted ω (initF j i) v (M - D) ∩
    {ψ | HitsDown (D - 1) (ω (contIdx (initF j i) v ψ))}
  have ht : ∀ ψ ∈ S, ∃ t, pos (glueP j D ω) (liftF (initF j i) v ψ) t = some [] :=
    fun ψ hψ => reach_root hD hv ψ hψ.1.1 hψ.1.2 hψ.2
  choose! t ht using ht
  unfold presN
  refine Set.encard_le_encard_of_injOn (f := fun ψ => (liftF (initF j i) v ψ, t ψ)) ?_ ?_
  · intro ψ hψ
    exact ⟨woken_lift hj hD hDM hv ψ hψ.1.1, ht ψ hψ⟩
  · intro a ha b hb hab
    have hl : liftF (initF j i) v a = liftF (initF j i) v b := (Prod.mk.inj hab).1
    rcases a with a | a <;> rcases b with b | b
    · rw [woken_one_inl ha.1.1, woken_one_inl hb.1.1]
    · exact absurd hl (initF_not_below hD hvD b)
    · exact absurd hl.symm (initF_not_below hD hvD a)
    · simp only [liftF, Sum.inr.injEq] at hl
      rw [List.append_cancel_right hl]

end Lift

end FrogModel.D3.LaneA
