module

public import FrogModel.D3.LaneA.Pool.Arrive

@[expose] public section

/-!
# The pool argument, the copy below a child (d = 3)

Below the child `c` of `w`, the vertex `v ++ [c]` of `T*` is the vertex `v` of a copy of `T*`
whose leaf is `w` (`walkStar_append`, Recursion/Arrive.lean). The copy is the planted model of
height `m` at `[c]` with the paths `copyPaths ω c e`: the entrant `i` follows the entry `e i` into
`c` from its second step, and the frog of `v` the segment `0` of the frog of `v ++ [c]`
(`copySeg` names the segment of each frog of the copy).

The subtree closure of the entries `e 0, ..., e (n - 1)` (Recursion/Closure.lean) is the image of
the woken set of the copy with `n` entrants (`subClosure_eq_copy`), and its returning segments are
the images of the copy frogs that reach the copy's leaf, so child `c` returns `G_m(n)` of the copy
(`encard_outP`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.LaneA.Pool

open FrogModel FrogModel.D3.Iface
open FrogModel.Recursion (StarSeg starStart isRootSeg subSeg dirSeg starPieces segStart segPiece
  gluePath retK segVis subClosure entrySet)
open FrogModel.LemmaX (depthStar visitsK)

/-- The paths of the copy below `c`: the entrant `i` follows the entry `e i` from its second step,
the frog of `v` the segment `0` of the frog of `v ++ [c]`. -/
def copyPaths (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3) (e : ℕ → StarSeg 3) :
    PFrog → ℕ → Step 3
  | Sum.inl i => fun t => ω (e i) (t + 1)
  | Sum.inr v => ω (Sum.inl (v ++ [c]), 0)

/-- The segment of a frog of the copy. -/
def copySeg (c : Fin 3) (e : ℕ → StarSeg 3) : PFrog → StarSeg 3
  | Sum.inl i => e i
  | Sum.inr v => (Sum.inl (v ++ [c]), 0)

/-! ### Walks in the copy -/

theorem copy_visit_iff (c : Fin 3) (w w' : Vertex 3) (p : ℕ → Step 3) :
    (∃ n, walkStar (some w) p n = some w') ↔
      segVisP (some (w ++ [c])) p (some (w' ++ [c])) := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨K, hK⟩ := exists_depth_bound (some w) p n
    exact (segVisP_iff _ _ _).2 ⟨K + 1, (Recursion.visitsK_copy_iff K c w w' p).1 ⟨n, hn, hK⟩⟩
  · intro h
    obtain ⟨K, hK⟩ := (segVisP_iff _ _ _).1 h
    obtain ⟨n, hn, -⟩ :=
      (Recursion.visitsK_copy_iff K c w w' p).2 (segVis_mono (Nat.le_succ K) hK)
    exact ⟨n, hn⟩

theorem copy_none_iff (c : Fin 3) (w : Vertex 3) (p : ℕ → Step 3) :
    (∃ n, walkStar (some w) p n = none) ↔ retP (some (w ++ [c])) p := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨K, hK⟩ := exists_depth_bound (some w) p n
    exact (retP_iff _ _).2 ⟨K + 1, (Recursion.visitsK_copy_none_iff K c w p).1 ⟨n, hn, hK⟩⟩
  · intro h
    obtain ⟨K, hK⟩ := (retP_iff _ _).1 h
    obtain ⟨n, hn, -⟩ :=
      (Recursion.visitsK_copy_none_iff K c w p).2 (retK_mono (Nat.le_succ K) hK)
    exact ⟨n, hn⟩

theorem segVisP_root_succ_iff (c : Fin 3) (p : ℕ → Step 3) (hp : (p 0).2 = c.succ)
    (u : Vertex 3) (hu : u ≠ []) :
    segVisP (some []) p (some u) ↔ segVisP (some [c]) (fun t => p (t + 1)) (some u) := by
  rw [segVisP_iff, segVisP_iff]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K + 1,
      (Recursion.segVis_root_succ_iff K c p hp u hu).1 (segVis_mono (Nat.le_succ K) hK)⟩
  · rintro ⟨K, hK⟩
    exact ⟨K + 1,
      (Recursion.segVis_root_succ_iff K c p hp u hu).2 (segVis_mono (Nat.le_succ K) hK)⟩

theorem retP_root_succ_iff (c : Fin 3) (p : ℕ → Step 3) (hp : (p 0).2 = c.succ) :
    retP (some []) p ↔ retP (some [c]) (fun t => p (t + 1)) := by
  rw [retP_iff, retP_iff]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K + 1, (Recursion.retK_root_succ_iff K c p hp).1 (retK_mono (Nat.le_succ K) hK)⟩
  · rintro ⟨K, hK⟩
    exact ⟨K + 1, (Recursion.retK_root_succ_iff K c p hp).2 (retK_mono (Nat.le_succ K) hK)⟩

section Copy

variable (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3) (e : ℕ → StarSeg 3)

/-- The frogs of the copy whose segment is an entry into `c` (or a frog of the subtree). -/
def CopyValid (φ : PFrog) : Prop :=
  ∀ i, φ = Sum.inl i → isRootSeg (e i) ∧ dirSeg ω (e i) = c.succ

/-- A visit of a frog of the copy is a visit of its segment before the return to `w`. -/
theorem copy_vis (φ : PFrog) (hφ : CopyValid ω c e φ) (v : Vertex 3) :
    (∃ n, pos (copyPaths ω c e) φ n = some v) ↔
      segVisP (starStart (copySeg c e φ)) (ω (copySeg c e φ)) (some (v ++ [c])) := by
  cases φ with
  | inl i =>
    obtain ⟨hroot, hdir⟩ := hφ i rfl
    have hroot' : starStart (e i) = some [] := hroot
    simp only [copySeg, hroot']
    rw [segVisP_root_succ_iff c (ω (e i)) hdir (v ++ [c]) (by simp)]
    have := copy_visit_iff c [] v (fun t => ω (e i) (t + 1))
    simpa [pos, copyPaths, D3.Iface.frogStart] using this
  | inr w =>
    have := copy_visit_iff c w v (ω (Sum.inl (w ++ [c]), 0))
    simpa [pos, copyPaths, copySeg, D3.Iface.frogStart, starStart, segStart,
      Recursion.frogStart] using this

/-- A frog of the copy reaches its leaf iff its segment returns to `w`. -/
theorem copy_ret (φ : PFrog) (hφ : CopyValid ω c e φ) :
    (∃ n, pos (copyPaths ω c e) φ n = none) ↔
      retP (starStart (copySeg c e φ)) (ω (copySeg c e φ)) := by
  cases φ with
  | inl i =>
    obtain ⟨hroot, hdir⟩ := hφ i rfl
    have hroot' : starStart (e i) = some [] := hroot
    simp only [copySeg, hroot']
    rw [retP_root_succ_iff c (ω (e i)) hdir]
    have := copy_none_iff c [] (fun t => ω (e i) (t + 1))
    simpa [pos, copyPaths, D3.Iface.frogStart] using this
  | inr w =>
    have := copy_none_iff c w (ω (Sum.inl (w ++ [c]), 0))
    simpa [pos, copyPaths, copySeg, D3.Iface.frogStart, starStart, segStart,
      Recursion.frogStart] using this

variable {ω c e} (m : ℕ) (S : Set (StarSeg 3)) (n : ℕ)

theorem copyValid_of_woken (he : entrySet ω c S = e '' {i | i < n}) (φ : PFrog)
    (hφ : Woken m n (copyPaths ω c e) φ) : CopyValid ω c e φ := by
  rintro i rfl
  have hi : i < n := woken_inl_lt hφ
  have hei : e i ∈ entrySet ω c S := by rw [he]; exact ⟨i, hi, rfl⟩
  exact ⟨hei.2.1, hei.2.2⟩

/-- The subtree closure lies in the image of the woken set of the copy. -/
theorem subClosure_subset_copy (he : entrySet ω c S = e '' {i | i < n}) :
    subClosure (dirSeg ω) (genP (m + 1)) ω isRootSeg subSeg c S ⊆
      copySeg c e '' {φ | Woken m n (copyPaths ω c e) φ} := by
  intro x hx
  refine hx _ ⟨?_, ?_⟩
  · intro y hy
    have hy' : y ∈ entrySet ω c S := hy
    rw [he] at hy'
    obtain ⟨i, hi, rfl⟩ := hy'
    exact ⟨Sum.inl i, Woken.ent i hi, rfl⟩
  · rintro σ ⟨φ, hφ, rfl⟩ τ ⟨hgen, hsub⟩
    obtain ⟨w', rfl⟩ := hsub
    rcases hgen with ⟨hτ, -⟩ | ⟨u, -, hu_len, hτ, hvis⟩
    · have := congrArg Prod.snd hτ
      simp at this
    · simp only [Prod.mk.injEq, Sum.inl.injEq, and_true] at hτ
      subst hτ
      obtain ⟨t, ht⟩ := (copy_vis ω c e φ (copyValid_of_woken m S n he φ hφ) w').2 hvis
      have hlen : w'.length ≤ m := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hu_len
        omega
      exact ⟨Sum.inr w', Woken.wake φ w' t hφ hlen ht, rfl⟩

/-- The image of the woken set of the copy lies in the subtree closure. -/
theorem copy_subset_subClosure (he : entrySet ω c S = e '' {i | i < n}) :
    copySeg c e '' {φ | Woken m n (copyPaths ω c e) φ} ⊆
      subClosure (dirSeg ω) (genP (m + 1)) ω isRootSeg subSeg c S := by
  rintro _ ⟨φ, hφ, rfl⟩
  induction hφ with
  | ent i hi =>
    apply Stage.subset_closure
    show e i ∈ entrySet ω c S
    rw [he]
    exact ⟨i, hi, rfl⟩
  | wake φ v t hφ hv hpos ih =>
    have hvis := (copy_vis ω c e φ (copyValid_of_woken m S n he φ hφ) v).1 ⟨t, hpos⟩
    refine Stage.closure_arc _ ω _ (copySeg c e φ) (Sum.inl (v ++ [c]), 0) ih ⟨?_, v, rfl⟩
    refine Or.inr ⟨v ++ [c], by simp, ?_, rfl, hvis⟩
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem subClosure_eq_copy (he : entrySet ω c S = e '' {i | i < n}) :
    subClosure (dirSeg ω) (genP (m + 1)) ω isRootSeg subSeg c S =
      copySeg c e '' {φ | Woken m n (copyPaths ω c e) φ} :=
  Set.Subset.antisymm (subClosure_subset_copy m S n he) (copy_subset_subClosure m S n he)

end Copy

/-- The returns of child `c` are the next segments of the returning segments of its closure. -/
theorem outP_eq_image (M : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3) (S : Set (StarSeg 3)) :
    outP M ω c S = (fun x : StarSeg 3 => (x.1, x.2 + 1)) ''
      {x | x ∈ subClosure (dirSeg ω) (genP M) ω isRootSeg subSeg c S ∧
        retP (starStart x) (ω x)} := by
  ext y
  constructor
  · rintro ⟨hroot, x, hx, hgen⟩
    have hy := eq_succ_of_genP_root hroot hgen
    rcases hgen with ⟨-, hret⟩ | ⟨u, hu, -, hyu, -⟩
    · exact ⟨x, ⟨hx, hret⟩, hy.symm⟩
    · exfalso
      rw [hy] at hyu
      have := congrArg Prod.snd hyu
      simp at this
  · rintro ⟨x, ⟨hx, hret⟩, rfl⟩
    refine ⟨?_, x, hx, Or.inl ⟨rfl, hret⟩⟩
    show starStart (x.1, x.2 + 1) = some []
    simp [starStart, segStart]

/-- **The returns of child `c` are the planted curve of the copy.** -/
theorem encard_outP (m : ℕ) (ω : StarSeg 3 → ℕ → Step 3) (c : Fin 3) (S : Set (StarSeg 3))
    (n : ℕ) (e : ℕ → StarSeg 3) (he : entrySet ω c S = e '' {i | i < n})
    (heinj : Set.InjOn e {i | i < n}) :
    (outP (m + 1) ω c S).encard = plantedG m n (copyPaths ω c e) := by
  rw [outP_eq_image, Set.InjOn.encard_image (fun x _ y _ h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)), subClosure_eq_copy m S n he]
  have hset : {x | x ∈ copySeg c e '' {φ | Woken m n (copyPaths ω c e) φ} ∧
      retP (starStart x) (ω x)} =
      copySeg c e '' {φ | Woken m n (copyPaths ω c e) φ ∧
        ∃ t, pos (copyPaths ω c e) φ t = none} := by
    ext x
    constructor
    · rintro ⟨⟨φ, hφ, rfl⟩, hret⟩
      exact ⟨φ, ⟨hφ, (copy_ret ω c e φ (copyValid_of_woken m S n he φ hφ)).2 hret⟩, rfl⟩
    · rintro ⟨φ, ⟨hφ, hreach⟩, rfl⟩
      exact ⟨⟨φ, hφ, rfl⟩, (copy_ret ω c e φ (copyValid_of_woken m S n he φ hφ)).1 hreach⟩
  have hinj : Set.InjOn (copySeg c e)
      {φ | Woken m n (copyPaths ω c e) φ ∧ ∃ t, pos (copyPaths ω c e) φ t = none} := by
    rintro (i | v) ⟨hφ, -⟩ (i' | v') ⟨hφ', -⟩ h
    · exact congrArg Sum.inl (heinj (woken_inl_lt hφ) (woken_inl_lt hφ') h)
    · exfalso
      have hroot := (copyValid_of_woken m S n he _ hφ i rfl).1
      simp only [copySeg] at h
      rw [h] at hroot
      have hr : starStart ((Sum.inl (v' ++ [c]), 0) : StarSeg 3) = some [] := hroot
      simp [starStart, segStart, Recursion.frogStart] at hr
    · exfalso
      have hroot := (copyValid_of_woken m S n he _ hφ' i' rfl).1
      simp only [copySeg] at h
      rw [← h] at hroot
      have hr : starStart ((Sum.inl (v ++ [c]), 0) : StarSeg 3) = some [] := hroot
      simp [starStart, segStart, Recursion.frogStart] at hr
    · simp only [copySeg, Prod.mk.injEq, Sum.inl.injEq, and_true] at h
      rw [List.append_cancel_right h]
  rw [hset, hinj.encard_image]
  rfl

end FrogModel.D3.LaneA.Pool
