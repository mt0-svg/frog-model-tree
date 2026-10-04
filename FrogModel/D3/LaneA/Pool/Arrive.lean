module

public import FrogModel.D3.LaneA.Pool.Defs

@[expose] public section

/-!
# The pool argument, the planted counts as root arrivals (d = 3)

With `j ≥ 1` entrants and the planted paths glued from the pieces `ω`, the active segments with
`j + 1` initial segments are the segments of the woken frogs whose earlier segments all return
(`mem_actP_iff`). A woken frog reaches `y` iff one of its live segments is a root segment of
direction `0`, and it has at most one (`reach_none_iff`, `frozen_seg_unique`), so
`G_M(j)` counts the root arrivals of direction `0` (`plantedG_eq_arrSet`). Every presence at `w` of
a woken frog starts a live root segment, and every live root segment of a woken frog starts at a
presence (`posStar` numbers the segments), so `N_M(j)` counts the root arrivals
(`presN_eq_arrSet`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA.Pool

open FrogModel FrogModel.D3.Iface
open FrogModel.Recursion (StarSeg starStart isRootSeg subSeg dirSeg starPieces segStart segPiece
  gluePath retK segVis posStar)
open FrogModel.LemmaX (depthStar visitsK)

/-! ### Live segments -/

/-- A common kill depth for finitely many returning segments. -/
theorem exists_retK_all (v : Option (Vertex 3)) (Z : ℕ × ℕ → Step 3) (s : ℕ)
    (halive : ∀ s' < s, retP (segStart v s') (segPiece Z s')) :
    ∃ K, ∀ s' < s, retK K (segStart v s') (segPiece Z s') := by
  choose Kf hKf using fun s' (hs' : s' < s) => (retP_iff _ _).1 (halive s' hs')
  let f : ℕ → ℕ := fun s' => if h : s' < s then Kf s' h else 0
  refine ⟨(Finset.range s).sup f, fun s' hs' => retK_mono ?_ (hKf s' hs')⟩
  have := Finset.le_sup (f := f) (Finset.mem_range.2 hs')
  simpa [f, hs'] using this

theorem segVisP_none_iff (w : Vertex 3) (p : ℕ → Step 3) :
    segVisP (some w) p none ↔ w = [] ∧ (p 0).2 = 0 := by
  rw [segVisP_iff]
  constructor
  · rintro ⟨K, h⟩
    exact (Recursion.segVis_none_iff K w p).1 h
  · intro h
    exact ⟨0, (Recursion.segVis_none_iff 0 w p).2 h⟩

theorem not_retP_of_dir_zero (p : ℕ → Step 3) (h : (p 0).2 = 0) : ¬ retP (some []) p := by
  intro hret
  obtain ⟨K, hK⟩ := (retP_iff _ _).1 hret
  exact Recursion.not_retK_of_dir_zero K p h hK

theorem exists_starStart (x : StarSeg 3) : ∃ w : Vertex 3, starStart x = some w := by
  obtain ⟨f, s⟩ := x
  cases f <;> cases s <;> simp [starStart, segStart, Recursion.frogStart]

/-! ### Active segments and woken frogs -/

section Active

variable (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) {j : ℕ}

/-- The frog of `w` is woken by the first entrant. -/
theorem woken_root (hj : 1 ≤ j) : Woken M j (plantedPaths ω) (Sum.inr []) :=
  Woken.wake (Sum.inl 0) [] 0 (Woken.ent 0 (by omega)) (Nat.zero_le _) rfl

/-- An active segment belongs to a woken frog and all segments before it return. -/
theorem actP_subset (hj : 1 ≤ j) :
    actP M ω (j + 1) ⊆
      {x | Woken M j (plantedPaths ω) (ofStar x.1) ∧ segAliveP ω x.1 x.2} := by
  intro x hx
  refine hx _ ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    cases a with
    | zero => exact ⟨woken_root M ω hj, fun s' hs' => absurd hs' (Nat.not_lt_zero _)⟩
    | succ a =>
      exact ⟨Woken.ent a (by simp only [Set.mem_ofPred_eq] at ha; omega),
        fun s' hs' => absurd hs' (Nat.not_lt_zero _)⟩
  · rintro ⟨f, s⟩ ⟨hfrog, hseg⟩ τ hτ
    rcases hτ with ⟨rfl, hret⟩ | ⟨u, hu_ne, hu_len, rfl, hvis⟩
    · refine ⟨hfrog, fun s' hs' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs' with hlt | rfl
      · exact hseg s' hlt
      · exact hret
    · refine ⟨?_, fun s' hs' => absurd hs' (Nat.not_lt_zero _)⟩
      obtain ⟨n, hn⟩ := (visits_gluePath_iff (Recursion.frogStart f) (starPieces ω f)
        (some u)).2 ⟨s, hseg, hvis⟩
      have hpos : pos (plantedPaths ω) (ofStar f) n = some u := by
        rw [pos_plantedPaths, toStar_ofStar]
        exact hn
      exact Woken.wake (ofStar f) u n hfrog hu_len hpos

/-- From the active segment `0` of a frog, its live segments are active. -/
theorem mem_actP_of_alive (q : ℕ) (f : Vertex 3 ⊕ ℕ) (h0 : (f, 0) ∈ actP M ω q) (s : ℕ)
    (hs : segAliveP ω f s) : (f, s) ∈ actP M ω q := by
  induction s with
  | zero => exact h0
  | succ s ih =>
    have hmem := ih fun s' hs' => hs s' (Nat.lt_succ_of_lt hs')
    exact Stage.closure_arc (genP M) ω _ (f, s) (f, s + 1) hmem
      (Or.inl ⟨rfl, hs s (Nat.lt_succ_self s)⟩)

/-- The segment `0` of a woken frog is active. -/
theorem mem_actP_of_woken (hj : 1 ≤ j) (φ : PFrog) (h : Woken M j (plantedPaths ω) φ) :
    (toStar φ, 0) ∈ actP M ω (j + 1) := by
  induction h with
  | ent i hi =>
    exact Stage.subset_closure (genP M) ω _ ⟨i + 1, by simp only [Set.mem_ofPred_eq]; omega, rfl⟩
  | wake φ v n _ hv hpos ih =>
    by_cases hv0 : v = []
    · subst hv0
      exact Stage.subset_closure (genP M) ω _ ⟨0, by simp only [Set.mem_ofPred_eq]; omega, rfl⟩
    · rw [pos_plantedPaths] at hpos
      obtain ⟨s, halive, hvis⟩ := (visits_gluePath_iff _ _ (some v)).1 ⟨n, hpos⟩
      have hs : (toStar φ, s) ∈ actP M ω (j + 1) :=
        mem_actP_of_alive M ω (j + 1) (toStar φ) ih s halive
      exact Stage.closure_arc (genP M) ω _ (toStar φ, s) (Sum.inl v, 0) hs
        (Or.inr ⟨v, hv0, hv, rfl, hvis⟩)

/-- **The active segments**: the live segments of the woken frogs. -/
theorem mem_actP_iff (hj : 1 ≤ j) (x : StarSeg 3) :
    x ∈ actP M ω (j + 1) ↔
      Woken M j (plantedPaths ω) (ofStar x.1) ∧ segAliveP ω x.1 x.2 := by
  refine ⟨fun h => actP_subset M ω hj h, fun ⟨hf, hs⟩ => ?_⟩
  have h0 := mem_actP_of_woken M ω hj (ofStar x.1) hf
  rw [toStar_ofStar] at h0
  exact mem_actP_of_alive M ω (j + 1) x.1 h0 x.2 hs

end Active

/-! ### Frozen frogs -/

/-- A glued frog reaches `y` iff one of its live segments is a root segment of direction `0`. -/
theorem reach_none_iff (ω : StarSeg 3 → ℕ → Step 3) (f : Vertex 3 ⊕ ℕ) :
    (∃ n, walkStar (Recursion.frogStart f) (gluePath (Recursion.frogStart f) (starPieces ω f)) n =
        none) ↔
      ∃ s, segAliveP ω f s ∧ isRootSeg (f, s) ∧ dirSeg ω (f, s) = 0 := by
  rw [visits_gluePath_iff]
  constructor
  · rintro ⟨s, halive, hvis⟩
    obtain ⟨w, hw⟩ := exists_starStart (f, s)
    have hvis' : segVisP (some w) (ω (f, s)) none := hw ▸ hvis
    obtain ⟨rfl, hdir⟩ := (segVisP_none_iff w _).1 hvis'
    exact ⟨s, halive, hw, hdir⟩
  · rintro ⟨s, halive, hroot, hdir⟩
    refine ⟨s, halive, ?_⟩
    have hroot' : starStart (f, s) = some [] := hroot
    show segVisP (starStart (f, s)) (ω (f, s)) none
    rw [hroot']
    exact (segVisP_none_iff [] _).2 ⟨rfl, hdir⟩

/-- A frog has at most one live root segment of direction `0`. -/
theorem frozen_seg_unique (ω : StarSeg 3 → ℕ → Step 3) (f : Vertex 3 ⊕ ℕ) (s s' : ℕ)
    (hs : segAliveP ω f s) (hs' : segAliveP ω f s') (hr : isRootSeg (f, s))
    (h0 : dirSeg ω (f, s) = 0) (hr' : isRootSeg (f, s')) (h0' : dirSeg ω (f, s') = 0) :
    s = s' := by
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · have hret := hs' s hlt
    have hroot : starStart (f, s) = some [] := hr
    rw [hroot] at hret
    exact absurd hret (not_retP_of_dir_zero _ h0)
  · exact heq
  · have hret := hs s' hgt
    have hroot : starStart (f, s') = some [] := hr'
    rw [hroot] at hret
    exact absurd hret (not_retP_of_dir_zero _ h0')

/-- **`G_M(j)` counts the root arrivals of direction `0`.** -/
theorem plantedG_eq_arrSet (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) {j : ℕ} (hj : 1 ≤ j) :
    plantedG M j (plantedPaths ω) =
      {x | x ∈ Recursion.arrSet initP (dirSeg ω) (outP M ω) (j + 1) ∧ dirSeg ω x = 0}.encard := by
  rw [arrSet_eq_actP]
  set S : Set (StarSeg 3) :=
    {x | x ∈ {x | isRootSeg x} ∩ actP M ω (j + 1) ∧ dirSeg ω x = 0} with hS
  have h_image : (fun x : StarSeg 3 => ofStar x.1) '' S =
      {φ | Woken M j (plantedPaths ω) φ ∧ ∃ n, pos (plantedPaths ω) φ n = none} := by
    ext φ
    constructor
    · rintro ⟨x, ⟨⟨hroot, hact⟩, hdir⟩, rfl⟩
      rw [mem_actP_iff M ω hj] at hact
      refine ⟨hact.1, ?_⟩
      simp only [pos_plantedPaths, toStar_ofStar]
      exact (reach_none_iff ω x.1).2 ⟨x.2, hact.2, hroot, hdir⟩
    · rintro ⟨hfrog, hreach⟩
      simp only [pos_plantedPaths] at hreach
      obtain ⟨s, halive, hroot, hdir⟩ := (reach_none_iff ω (toStar φ)).1 hreach
      refine ⟨(toStar φ, s), ⟨⟨hroot, ?_⟩, hdir⟩, ofStar_toStar φ⟩
      rw [mem_actP_iff M ω hj]
      exact ⟨by rwa [ofStar_toStar], halive⟩
  have h_inj : Set.InjOn (fun x : StarSeg 3 => ofStar x.1) S := by
    rintro ⟨f, s⟩ ⟨⟨hr, ha⟩, hd⟩ ⟨f', s'⟩ ⟨⟨hr', ha'⟩, hd'⟩ hff
    have hf : f = f' := by simpa using congrArg toStar hff
    subst hf
    rw [mem_actP_iff M ω hj] at ha ha'
    rw [frozen_seg_unique ω f s s' ha.2 ha'.2 hr hd hr' hd']
  unfold plantedG
  rw [← h_image, h_inj.encard_image]

/-! ### Presences -/

/-- The segment index of the time `t` of the glued frog `f`. -/
noncomputable def segAt (ω : StarSeg 3 → ℕ → Step 3) (f : Vertex 3 ⊕ ℕ) (t : ℕ) : ℕ :=
  (posStar (Recursion.frogStart f) (gluePath (Recursion.frogStart f) (starPieces ω f)) t).1

/-- At a time at `w`, the position in the current segment is `0`. -/
theorem posStar_snd_of_root (v : Option (Vertex 3)) (x : ℕ → Step 3) (t : ℕ)
    (ht : walkStar v x t = some []) : (posStar v x t).2 = 0 := by
  cases t with
  | zero => rw [Recursion.posStar_zero]
  | succ t =>
    rw [Recursion.posStar_succ]
    simp [ht]

/-- **`N_M(j)` counts the root arrivals.** -/
theorem presN_eq_arrSet (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) {j : ℕ} (hj : 1 ≤ j) :
    presN M j (plantedPaths ω) =
      (Recursion.arrSet initP (dirSeg ω) (outP M ω) (j + 1)).encard := by
  rw [arrSet_eq_actP]
  set P : Set (PFrog × ℕ) :=
    {p | Woken M j (plantedPaths ω) p.1 ∧ pos (plantedPaths ω) p.1 p.2 = some []} with hP
  let g : PFrog × ℕ → StarSeg 3 := fun p => (toStar p.1, segAt ω (toStar p.1) p.2)
  have h_inj : Set.InjOn g P := by
    rintro ⟨φ, t⟩ ⟨-, ht⟩ ⟨φ', t'⟩ ⟨-, ht'⟩ hg
    simp only [g, Prod.mk.injEq] at hg
    obtain ⟨hφ, hs⟩ := hg
    have hφ' : φ = φ' := toStar_injective hφ
    subst hφ'
    simp only [pos_plantedPaths] at ht ht'
    have h1 := posStar_snd_of_root _ _ t ht
    have h2 := posStar_snd_of_root _ _ t' ht'
    have : t = t' := Recursion.posStar_injective _ _ (Prod.ext hs (h1.trans h2.symm))
    rw [this]
  have h_image : g '' P = {x | isRootSeg x} ∩ actP M ω (j + 1) := by
    ext ⟨f, s⟩
    constructor
    · rintro ⟨⟨φ, t⟩, ⟨hfrog, ht⟩, hgx⟩
      simp only [g, Prod.mk.injEq] at hgx
      obtain ⟨rfl, rfl⟩ := hgx
      simp only [pos_plantedPaths] at ht
      set v := Recursion.frogStart (toStar φ)
      set Z := starPieces ω (toStar φ)
      obtain ⟨K, hK⟩ := exists_depth_bound v (gluePath v Z) t
      have halive := Recursion.retK_of_posStar K v Z t hK
      obtain ⟨-, -, hstart, -⟩ := Recursion.posStar_start v (gluePath v Z) t
      rw [posStar_snd_of_root _ _ t ht, Nat.sub_zero, ht] at hstart
      refine ⟨hstart.symm, ?_⟩
      rw [mem_actP_iff M ω hj]
      refine ⟨by rwa [ofStar_toStar], fun s' hs' => (retP_iff _ _).2 ⟨K, halive s' hs'⟩⟩
    · rintro ⟨hroot, hact⟩
      rw [mem_actP_iff M ω hj] at hact
      obtain ⟨hfrog, halive⟩ := hact
      set v := Recursion.frogStart f
      set Z := starPieces ω f
      obtain ⟨K, hK⟩ := exists_retK_all v Z s halive
      obtain ⟨T, hT, hwalk, -⟩ := Recursion.exists_segStart_time K v Z s hK
      refine ⟨(ofStar f, T), ⟨hfrog, ?_⟩, ?_⟩
      · rw [pos_plantedPaths, toStar_ofStar]
        exact hwalk.trans hroot
      · simp only [g, toStar_ofStar, segAt]
        rw [hT]
  unfold presN
  rw [← h_image, h_inj.encard_image]

end FrogModel.D3.LaneA.Pool
