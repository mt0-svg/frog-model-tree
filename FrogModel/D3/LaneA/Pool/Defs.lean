module

public import FrogModel.D3.LaneA.Coins
public import FrogModel.Recursion.Law

@[expose] public section

/-!
# The pool argument, segments and arcs of the planted model (d = 3)

The pool argument of the proof of Lemma 10.1 of the paper. The frog paths of the planted model at
`w = some []` are glued from segments (Recursion/Glue.lean): segment `s` of a frog runs from its
`s`-th return to `w` (from its start for `s = 0`) to the next one. The segments are indexed by
`StarSeg 3` (Recursion/Arrive.lean): `(Sum.inl v, s)` is segment `s` of the frog of `v` (`v = []` is
the frog of `w`), `(Sum.inr a, s)` segment `s` of the entrant `a`. The planted paths are
`plantedPaths ω`, the glued paths of the pieces `ω`.

The arcs of the planted model of height `M` (`genP M`): a segment generates the next segment of
its frog when it returns to `w` (`retP`), and the segment `0` of the frog of a vertex `u ≠ []` of
depth at most `M` that it visits before its return (`segVisP`). No kill depth here: the
segment-level facts of the kill model (`retK`, `segVis`, `visitsK`) transfer through "some kill
depth", since a finite stretch of walk has a bounded depth (`retP_iff`, `segVisP_iff`,
`visits_gluePath_iff`). The initial segments are the segment `0` of the frog of `w`, then those
of the entrants (`initP`), so the closure with `j + 1` initial segments is the planted model with
`j` entrants. `arrSet_eq_actP` identifies the root arrivals of the processing (Process.lean) with
the active root segments.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA.Pool

open FrogModel FrogModel.D3.Iface
open FrogModel.Recursion (StarSeg starStart isRootSeg subSeg dirSeg starPieces segStart segPiece
  gluePath retK segVis outGen)
open FrogModel.LemmaX (depthStar visitsK)

/-! ### Definitions -/

/-- The walk from `u` returns to `w` at some time `≥ 1`. -/
def retP (u : Option (Vertex 3)) (p : ℕ → Step 3) : Prop :=
  ∃ c, 1 ≤ c ∧ walkStar u p c = some []

/-- The walk from `u` visits `b` before its first return to `w` at a time `≥ 1`. -/
def segVisP (u : Option (Vertex 3)) (p : ℕ → Step 3) (b : Option (Vertex 3)) : Prop :=
  ∃ n, walkStar u p n = b ∧ ∀ i, 1 ≤ i → i < n → walkStar u p i ≠ some []

/-- Segment `x` with piece `p` generates `y` in the planted model of height `M`. -/
def genP (M : ℕ) (x : StarSeg 3) (p : ℕ → Step 3) (y : StarSeg 3) : Prop :=
  (y = (x.1, x.2 + 1) ∧ retP (starStart x) p) ∨
    ∃ u : Vertex 3, u ≠ [] ∧ u.length ≤ M ∧ y = (Sum.inl u, 0) ∧
      segVisP (starStart x) p (some u)

/-- The initial segments: the segment `0` of the frog of `w`, then those of the entrants. -/
def initP : ℕ → StarSeg 3
  | 0 => (Sum.inl [], 0)
  | a + 1 => (Sum.inr a, 0)

/-- The active segments with `q` initial segments. -/
def actP (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (q : ℕ) : Set (StarSeg 3) :=
  Stage.closure (genP M) ω (initP '' {a | a < q})

/-- The root segments returned by child `c` given the segments `S`. -/
def outP (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3) (S : Set (StarSeg 3)) :
    Set (StarSeg 3) :=
  outGen (dirSeg ω) (genP M) ω isRootSeg subSeg c S

/-- The frog of the segment index of a frog of the planted model. -/
def toStar : PFrog → Vertex 3 ⊕ ℕ
  | Sum.inl i => Sum.inr i
  | Sum.inr v => Sum.inl v

/-- The frog of the planted model of a segment index frog. -/
def ofStar : Vertex 3 ⊕ ℕ → PFrog
  | Sum.inl v => Sum.inr v
  | Sum.inr i => Sum.inl i

/-- The planted paths glued from the pieces. -/
noncomputable def plantedPaths (ω : StarSeg 3 → ℕ → Step 3) : PFrog → ℕ → Step 3 :=
  fun φ => gluePath (Recursion.frogStart (toStar φ)) (starPieces ω (toStar φ))

/-- The segments before `s` of frog `f` return. -/
def segAliveP (ω : StarSeg 3 → ℕ → Step 3) (f : Vertex 3 ⊕ ℕ) (s : ℕ) : Prop :=
  ∀ s' < s, retP (starStart (f, s')) (ω (f, s'))

/-! ### Frogs -/

@[simp] theorem ofStar_toStar (φ : PFrog) : ofStar (toStar φ) = φ := by
  cases φ <;> rfl

@[simp] theorem toStar_ofStar (f : Vertex 3 ⊕ ℕ) : toStar (ofStar f) = f := by
  cases f <;> rfl

theorem toStar_injective : Function.Injective toStar :=
  Function.LeftInverse.injective ofStar_toStar

theorem frogStart_toStar (φ : PFrog) :
    Recursion.frogStart (toStar φ) = some (D3.Iface.frogStart φ) := by
  cases φ <;> rfl

theorem pos_plantedPaths (ω : StarSeg 3 → ℕ → Step 3) (φ : PFrog) (n : ℕ) :
    pos (plantedPaths ω) φ n =
      walkStar (Recursion.frogStart (toStar φ))
        (gluePath (Recursion.frogStart (toStar φ)) (starPieces ω (toStar φ))) n := by
  unfold pos plantedPaths
  rw [frogStart_toStar]

/-! ### Some kill depth -/

theorem exists_depth_bound (u : Option (Vertex 3)) (p : ℕ → Step 3) (n : ℕ) :
    ∃ K, ∀ i ≤ n, depthStar (walkStar u p i) ≤ K :=
  ⟨(Finset.range (n + 1)).sup fun i => depthStar (walkStar u p i), fun i hi =>
    Finset.le_sup (f := fun i => depthStar (walkStar u p i)) (Finset.mem_range.2 (by omega))⟩

theorem retP_iff (u : Option (Vertex 3)) (p : ℕ → Step 3) : retP u p ↔ ∃ K, retK K u p := by
  constructor
  · rintro ⟨c, hc1, hc⟩
    obtain ⟨K, hK⟩ := exists_depth_bound u p c
    exact ⟨K, c, hc1, hc, hK⟩
  · rintro ⟨K, c, hc1, hc, -⟩
    exact ⟨c, hc1, hc⟩

theorem segVisP_iff (u : Option (Vertex 3)) (p : ℕ → Step 3) (b : Option (Vertex 3)) :
    segVisP u p b ↔ ∃ K, segVis K u p b := by
  constructor
  · rintro ⟨n, hn, hret⟩
    obtain ⟨K, hK⟩ := exists_depth_bound u p n
    exact ⟨K, n, hn, hret, hK⟩
  · rintro ⟨K, n, hn, hret, -⟩
    exact ⟨n, hn, hret⟩

theorem retK_mono {K K' : ℕ} (hK : K ≤ K') {u : Option (Vertex 3)} {p : ℕ → Step 3}
    (h : retK K u p) : retK K' u p := by
  obtain ⟨c, hc1, hc, hd⟩ := h
  exact ⟨c, hc1, hc, fun i hi => (hd i hi).trans hK⟩

theorem segVis_mono {K K' : ℕ} (hK : K ≤ K') {u : Option (Vertex 3)} {p : ℕ → Step 3}
    {b : Option (Vertex 3)} (h : segVis K u p b) : segVis K' u p b := by
  obtain ⟨n, hn, hret, hd⟩ := h
  exact ⟨n, hn, hret, fun i hi => (hd i hi).trans hK⟩

/-- **Visits of a glued frog.** The glued frog visits `b` iff some segment whose earlier segments
all return visits `b` before its own return. -/
theorem visits_gluePath_iff (v : Option (Vertex 3)) (Z : ℕ × ℕ → Step 3)
    (b : Option (Vertex 3)) :
    (∃ n, walkStar v (gluePath v Z) n = b) ↔
      ∃ s, (∀ s' < s, retP (segStart v s') (segPiece Z s')) ∧
        segVisP (segStart v s) (segPiece Z s) b := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨K, hK⟩ := exists_depth_bound v (gluePath v Z) n
    obtain ⟨s, halive, hvis⟩ := (Recursion.visitsK_gluePath K v Z b).1 ⟨n, hn, hK⟩
    exact ⟨s, fun s' hs' => (retP_iff _ _).2 ⟨K, halive s' hs'⟩, (segVisP_iff _ _ _).2 ⟨K, hvis⟩⟩
  · rintro ⟨s, halive, hvis⟩
    choose Kf hKf using fun s' (hs' : s' < s) => (retP_iff _ _).1 (halive s' hs')
    obtain ⟨K0, hK0⟩ := (segVisP_iff _ _ _).1 hvis
    let f : ℕ → ℕ := fun s' => if h : s' < s then Kf s' h else 0
    have hf : ∀ s' (hs' : s' < s), Kf s' hs' ≤ (Finset.range s).sup f := by
      intro s' hs'
      have := Finset.le_sup (f := f) (Finset.mem_range.2 hs')
      simpa [f, hs'] using this
    obtain ⟨n, hn, -⟩ := (Recursion.visitsK_gluePath (K0 + (Finset.range s).sup f) v Z b).2
      ⟨s, fun s' hs' => retK_mono ((hf s' hs').trans (Nat.le_add_left _ _)) (hKf s' hs'),
        segVis_mono (Nat.le_add_right _ _) hK0⟩
    exact ⟨n, hn⟩

/-! ### The arcs -/

theorem exists_starGen_of_genP {M : ℕ} {x y : StarSeg 3} {p : ℕ → Step 3}
    (h : genP M x p y) : ∃ K, Recursion.starGen K x p y := by
  rcases h with ⟨hy, hret⟩ | ⟨u, hu, -, hy, hvis⟩
  · obtain ⟨K, hK⟩ := (retP_iff _ _).1 hret
    exact ⟨K, Or.inl ⟨hy, hK⟩⟩
  · obtain ⟨K, hK⟩ := (segVisP_iff _ _ _).1 hvis
    exact ⟨K, Or.inr ⟨u, hu, hy, hK⟩⟩

/-- A root segment of direction `0` generates nothing. -/
theorem genP_root_zero (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (x y : StarSeg 3)
    (hx : isRootSeg x) (h0 : dirSeg ω x = 0) : ¬ genP M x (ω x) y := by
  intro h
  obtain ⟨K, hK⟩ := exists_starGen_of_genP h
  exact Recursion.starGen_root_zero K ω x y hx h0 hK

/-- A root segment of direction `c.succ` generates root segments and segments of subtree `c`. -/
theorem genP_root_succ (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3) (x y : StarSeg 3)
    (hx : isRootSeg x) (hc : dirSeg ω x = c.succ) (h : genP M x (ω x) y) :
    isRootSeg y ∨ subSeg c y := by
  obtain ⟨K, hK⟩ := exists_starGen_of_genP h
  exact Recursion.starGen_root_succ K ω c x y hx hc hK

/-- A segment of subtree `c` generates root segments and segments of subtree `c`. -/
theorem genP_sub (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3) (x y : StarSeg 3)
    (hx : subSeg c x) (h : genP M x (ω x) y) : isRootSeg y ∨ subSeg c y := by
  obtain ⟨K, hK⟩ := exists_starGen_of_genP h
  exact Recursion.starGen_sub K ω c x y hx hK

/-- A root segment generated by `x` is the next segment of the frog of `x`. -/
theorem eq_succ_of_genP_root {M : ℕ} {ω : StarSeg 3 → ℕ → Step 3} {x y : StarSeg 3}
    (hy : isRootSeg y) (h : genP M x (ω x) y) : y = (x.1, x.2 + 1) := by
  rcases h with ⟨hy', -⟩ | ⟨u, hu, -, hy', -⟩
  · exact hy'
  · exfalso
    apply hu
    subst hy'
    simpa [isRootSeg, starStart, segStart, Recursion.frogStart] using hy

/-- A root segment has at most one generator, the previous segment of its frog. -/
theorem genP_pred (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (x x' y : StarSeg 3)
    (hy : isRootSeg y) (h : genP M x (ω x) y) (h' : genP M x' (ω x') y) : x = x' := by
  have h1 := eq_succ_of_genP_root hy h
  have h2 := eq_succ_of_genP_root hy h'
  rw [h1] at h2
  obtain ⟨a, s⟩ := x
  obtain ⟨a', s'⟩ := x'
  simp only [Prod.mk.injEq] at h2
  obtain ⟨rfl, h⟩ := h2
  simp only [Prod.mk.injEq, true_and]
  omega

/-- No segment generates an initial segment. -/
theorem not_genP_initP (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (x : StarSeg 3) (a : ℕ) :
    ¬ genP M x (ω x) (initP a) := by
  rintro (⟨hy, -⟩ | ⟨u, hu, -, hy, -⟩)
  · have := congrArg Prod.snd hy
    cases a <;> simp [initP] at this
  · cases a with
    | zero =>
      simp only [initP, Prod.mk.injEq, Sum.inl.injEq, and_true] at hy
      exact hu hy.symm
    | succ a => simp [initP] at hy

theorem initP_root (a : ℕ) : isRootSeg (initP a) := by
  cases a <;> rfl

theorem initP_injective : Function.Injective initP := by
  intro a b h
  cases a <;> cases b <;> simp_all [initP]

/-- **The active root segments are the arrivals.** -/
theorem arrSet_eq_actP (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (q : ℕ) :
    Recursion.arrSet initP (dirSeg ω) (outP M ω) q = {x | isRootSeg x} ∩ actP M ω q :=
  Recursion.arrSet_eq_closure initP (dirSeg ω) (genP M) ω isRootSeg subSeg initP_root
    (fun c x h => Recursion.not_isRootSeg_of_subSeg c x h) (genP_root_zero M ω)
    (genP_root_succ M ω) (genP_sub M ω) q

theorem outP_mono (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3) : Monotone (outP M ω c) :=
  fun _ _ h => Recursion.outGen_mono (dirSeg ω) (genP M) ω isRootSeg subSeg c h

theorem initP_not_mem_outP (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3)
    (S : Set (StarSeg 3)) (a : ℕ) : initP a ∉ outP M ω c S :=
  Recursion.init_not_mem_outGen initP (dirSeg ω) (genP M) ω isRootSeg subSeg
    (fun x a => not_genP_initP M ω x a) c S a

theorem outP_disjoint (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (c c' : Fin 3)
    (S S' : Set (StarSeg 3)) (h : c ≠ c') : Disjoint (outP M ω c S) (outP M ω c' S') :=
  Recursion.outGen_disjoint (dirSeg ω) (genP M) ω isRootSeg subSeg
    (fun c x h => Recursion.not_isRootSeg_of_subSeg c x h) Recursion.subSeg_unique
    (fun x x' y hy hx hx' => genP_pred M ω x x' y hy hx hx') c c' S S' h

end FrogModel.D3.LaneA.Pool
