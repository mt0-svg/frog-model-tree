module

public import FrogModel.Engine.G3Sem

@[expose] public section

/-!
# The right sides of the systems at one state, as sums over the moves

The right side of the absorption system at `y` is the integral over one input of `tauV`, the
reward of the absorption unflagged with outputs `o` plus `Vs` at the state reached
(`rhsV_eq`); the right side of the flagged system is the integral of `tauW`, the reward `Phi` at
the step that sets the flag plus `Ws` (`rhsW_eq`). By `lintegral_candDom` both are the exit plus
the moves of each child.

The values at the state reached depend on its children only through the multiset of their codes
(`Vs_congr`, `Ws_congr`, `keepOf_congr`, `domNext_congr`): the sum over the four children is a
sum over the multiset of codes (`sum_children`).
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine.G3

open FrogModel.Cert FrogModel.LemmaX

open Classical in
/-- The reward of the absorption unflagged with outputs `o` at the step from `y` to `z`. -/
noncomputable def absInd (o : Fin 4 → ℕ) (y z : RState CState 4 4 × Bool) : ℝ≥0∞ :=
  if y.2 = false ∧ y.1.i < 4 ∧ z.2 = false ∧ 4 ≤ z.1.i ∧ z.1.out = (fun k => (o k : ℕ∞)) then 1
  else 0

/-- The integrand of the absorption system. -/
noncomputable def tauV (t : G3K.Tree) (o : Fin 4 → ℕ) (y z : RState CState 4 4 × Bool) : ℝ≥0∞ :=
  absInd o y z + Vs t o z

open Classical in
/-- The integrand of the flagged system. -/
noncomputable def tauW (t : G3K.Tree) (y z : RState CState 4 4 × Bool) : ℝ≥0∞ :=
  (if y.2 = false ∧ z.2 = true then phiC z.1 else 0) + Ws t z

theorem measurable_gT (t : G3K.Tree) (y : RState CState 4 4 × Bool)
    (F : RState CState 4 4 × Bool → ℝ≥0∞) : Measurable fun ξ => F (gT t y ξ) :=
  measurable_comp_of_fibers (gT t y)
    (fun z => measurableSet_domStep_eq cand.childStep cand.measurableSet_childStep_eq cand.T 16
      (keepOf t) (lumpState cand) y z) F

theorem absInd_eq_indicator (t : G3K.Tree) (o : Fin 4 → ℕ) (y : RState CState 4 4 × Bool)
    (ξ : Fin 5 × ℝ) :
    absInd o y (gT t y ξ) = (absUnflagged (gT t) o y).indicator 1 ξ := by
  classical
  unfold absInd
  rw [Set.indicator_apply]
  by_cases h : y.2 = false ∧ y.1.i < 4 ∧ (gT t y ξ).2 = false ∧ 4 ≤ (gT t y ξ).1.i ∧
      (gT t y ξ).1.out = (fun k => (o k : ℕ∞))
  · rw [if_pos h, if_pos (show ξ ∈ absUnflagged (gT t) o y from h), Pi.one_apply]
  · rw [if_neg h, if_neg (show ξ ∉ absUnflagged (gT t) o y from h)]

theorem rhsV_eq (t : G3K.Tree) (o : Fin 4 → ℕ) (y : RState CState 4 4 × Bool) :
    nuC (absUnflagged (gT t) o y) +
        FrogModel.LinSys.app (fkKernel (gT t) (fun _ _ => 1) nuC) (Vs t o) y =
      ∫⁻ ξ, tauV t o y (gT t y ξ) ∂nuC := by
  have hf : ∀ y z, MeasurableSet {ξ | gT t y ξ = z} := fun y z =>
    measurableSet_domStep_eq cand.childStep cand.measurableSet_childStep_eq cand.T 16 (keepOf t)
      (lumpState cand) y z
  rw [app_fkKernel_one (gT t) nuC hf, ← lintegral_indicator_one
    (measurableSet_absUnflagged cand.childStep cand.measurableSet_childStep_eq cand.T 16
      (keepOf t) (lumpState cand) o y),
    ← lintegral_add_left' (measurable_one.indicator (measurableSet_absUnflagged cand.childStep
      cand.measurableSet_childStep_eq cand.T 16 (keepOf t) (lumpState cand) o y)).aemeasurable]
  refine lintegral_congr fun ξ => ?_
  rw [tauV, absInd_eq_indicator]

theorem flag_eq (t : G3K.Tree) (y : RState CState 4 4 × Bool) (ξ : Fin 5 × ℝ) :
    flagReward (gT t) phiC y ξ =
      if y.2 = false ∧ (gT t y ξ).2 = true then phiC (gT t y ξ).1 else 0 := rfl

theorem rhsW_eq (t : G3K.Tree) (y : RState CState 4 4 × Bool) :
    fkRhs (flagReward (gT t) phiC) nuC y +
        FrogModel.LinSys.app (fkKernel (gT t) (fun _ _ => 1) nuC) (Ws t) y =
      ∫⁻ ξ, tauW t y (gT t y ξ) ∂nuC := by
  have hf : ∀ y z, MeasurableSet {ξ | gT t y ξ = z} := fun y z =>
    measurableSet_domStep_eq cand.childStep cand.measurableSet_childStep_eq cand.T 16 (keepOf t)
      (lumpState cand) y z
  rw [app_fkKernel_one (gT t) nuC hf, fkRhs]
  exact (lintegral_add_left' (measurable_gT t y fun z =>
    (if y.2 = false ∧ z.2 = true then phiC z.1 else 0 : ℝ≥0∞)).aemeasurable _).symm

/-! ### The states a step reaches -/

theorem rstepR_same (X : RState CState 4 4) (c : Fin 4) (δ : ℕ) (s : CState) (hi : X.i < 4)
    (h : X.p - 1 + δ ≠ 0) :
    rstepR X c (δ, s) = ⟨X.i, X.e, X.p - 1 + δ, Function.update X.σ c s, X.out⟩ := by
  simp only [rstepR, hi, ↓reduceDIte, h, ↓reduceIte]

theorem rstepR_next (X : RState CState 4 4) (c : Fin 4) (δ : ℕ) (s : CState) (hi : X.i < 4)
    (h : X.p - 1 + δ = 0) :
    rstepR X c (δ, s) = ⟨X.i + 1, X.e, 1, Function.update X.σ c s,
      Function.update X.out ⟨X.i, hi⟩ (X.e : ℕ∞)⟩ := by
  simp only [rstepR, hi, ↓reduceDIte, h, ↓reduceIte]

/-- The exit: one more exit, one pending frog less; the frog finishes when it was the last. -/
theorem rstep_exit (X : RState CState 4 4) (hi : X.i < 4) :
    rstep cand.childStep X (0, 0) =
      if X.p - 1 = 0 then ⟨X.i + 1, X.e + 1, 1, X.σ, Function.update X.out ⟨X.i, hi⟩ ((X.e + 1 : ℕ) : ℕ∞)⟩
      else ⟨X.i, X.e + 1, X.p - 1, X.σ, X.out⟩ := by
  simp only [rstep, move, hi, ↓reduceDIte]

/-! ### Keys of the states reached -/

theorem code_lumpC (s : CState) (hs : cand.ChildWF s) : code (lumpC cand s) = G3K.lumpC (code s) := by
  have h := lump_spec (code s) (code_lt s hs)
  rw [decC_code s hs] at h
  rw [← h.2, code_decC _ h.1]

theorem codeMs_update (σ : Fin 4 → CState) (c : Fin 4) (s : CState) (u1 u2 u3 : ℕ)
    (h : codeMs σ = {u1, u2, u3, code (σ c)}) :
    codeMs (Function.update σ c s) = {u1, u2, u3, code s} := by
  have huniv : (Finset.univ : Finset (Fin 4)).val = c ::ₘ ((Finset.univ : Finset (Fin 4)).erase c).val := by
    have hmem : c ∈ (Finset.univ : Finset (Fin 4)) := Finset.mem_univ c
    have h_insert : insert c ((Finset.univ : Finset (Fin 4)).erase c) = (Finset.univ : Finset (Fin 4)) :=
      Finset.insert_erase hmem
    calc
      (Finset.univ : Finset (Fin 4)).val = (insert c ((Finset.univ : Finset (Fin 4)).erase c)).val := by rw [h_insert]
      _ = c ::ₘ ((Finset.univ : Finset (Fin 4)).erase c).val := by
        rw [Finset.insert_val_of_notMem]
        exact Finset.notMem_erase c _
  let M : Multiset ℕ := Multiset.map (fun (k : Fin 4) => FrogModel.Engine.G3.code (σ k)) ((Finset.univ : Finset (Fin 4)).erase c).val
  have hcodeMs : FrogModel.Engine.G3.codeMs σ = FrogModel.Engine.G3.code (σ c) ::ₘ M := by
    dsimp [FrogModel.Engine.G3.codeMs]
    rw [huniv, Multiset.map_cons]
  have hcodeMs_up : FrogModel.Engine.G3.codeMs (Function.update σ c s) = FrogModel.Engine.G3.code s ::ₘ M := by
    dsimp [FrogModel.Engine.G3.codeMs]
    rw [huniv, Multiset.map_cons]
    rw [Function.update_self]
    dsimp [M]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    have hx_ne_c : x ≠ c := by
      have hx' : x ∈ (Finset.univ : Finset (Fin 4)).erase c := hx
      exact Finset.ne_of_mem_erase hx'
    rw [Function.update_of_ne hx_ne_c]
  rw [hcodeMs] at h
  rw [hcodeMs_up]
  have hM : M = {u1, u2, u3} := by
    have h_cons_swap : ({u1, u2, u3, FrogModel.Engine.G3.code (σ c)} : Multiset ℕ) = FrogModel.Engine.G3.code (σ c) ::ₘ {u1, u2, u3} := by
      simp [Multiset.cons_swap]
      apply Multiset.cons_swap
    rw [h_cons_swap] at h
    exact (Multiset.cons_inj_right (FrogModel.Engine.G3.code (σ c))).mp h
  rw [hM]
  simp [Multiset.cons_swap]
  apply Multiset.cons_swap

theorem codeMs_lump (σ : Fin 4 → CState) (hwf : ∀ c, cand.ChildWF (σ c)) :
    codeMs (fun c => lumpC cand (σ c)) = (codeMs σ).map G3K.lumpC := by
  simp only [codeMs, Multiset.map_map, Function.comp_def, code_lumpC _ (hwf _)]

theorem keyOf_encIns (X : RState CState 4 4) (u1 u2 u3 w : ℕ) (h12 : u1 ≤ u2) (h23 : u2 ≤ u3)
    (h : codeMs X.σ = {u1, u2, u3, w}) :
    keyOf X = G3K.Spec.encIns (X.i + 1) u1 u2 u3 w X.p := by
  rw [encIns_eq _ _ _ _ _ _ h12 h23, keyOf, h]

theorem keyOf_lump_encIns (X : RState CState 4 4) (u1 u2 u3 w : ℕ)
    (hwf : ∀ c, cand.ChildWF (X.σ c)) (h : codeMs X.σ = {u1, u2, u3, w}) :
    keyOf (lumpState cand X) = G3K.Spec.encIns (X.i + 1)
      (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).1
      (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.1
      (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.2 (G3K.lumpC w) X.p := by
  set a := G3K.lumpC u1
  set b := G3K.lumpC u2
  set c := G3K.lumpC u3
  set d := G3K.lumpC w
  set s := G3K.Spec.sort3 a b c
  have hsort := FrogModel.Engine.G3.sort3_eq a b c
  have hpair : List.Pairwise (· ≤ ·) [s.1, s.2.1, s.2.2] := by
    rw [hsort]
    exact Multiset.pairwise_sort _ _
  have hs1s2 : s.1 ≤ s.2.1 := by
    have := List.Pairwise.rel_get_of_lt hpair (by decide : (0 : Fin 3) < 1)
    simpa using this
  have hs2s3 : s.2.1 ≤ s.2.2 := by
    have := List.Pairwise.rel_get_of_lt hpair (by decide : (1 : Fin 3) < 2)
    simpa using this
  have hencIns := FrogModel.Engine.G3.encIns_eq (X.i + 1) s.1 s.2.1 s.2.2 d X.p hs1s2 hs2s3
  have hms : ({a, b, c} : Multiset ℕ) = ({s.1, s.2.1, s.2.2} : Multiset ℕ) := by
    calc
      ({a, b, c} : Multiset ℕ) = ↑(({a, b, c} : Multiset ℕ).sort (· ≤ ·)) := by rw [Multiset.sort_eq]
      _ = ↑[s.1, s.2.1, s.2.2] := by rw [← hsort]
      _ = ({s.1, s.2.1, s.2.2} : Multiset ℕ) := rfl
  calc
    keyOf (lumpState cand X) = encL (X.i + 1) ((codeMs (fun c => lumpC cand (X.σ c))).sort (· ≤ ·)) X.p := rfl
    _ = encL (X.i + 1) (((codeMs X.σ).map G3K.lumpC).sort (· ≤ ·)) X.p := by rw [FrogModel.Engine.G3.codeMs_lump X.σ hwf]
    _ = encL (X.i + 1) ((Multiset.map G3K.lumpC {u1, u2, u3, w}).sort (· ≤ ·)) X.p := by rw [h]
    _ = encL (X.i + 1) (({a, b, c, d} : Multiset ℕ).sort (· ≤ ·)) X.p := by
      simp [a, b, c, d, Multiset.map_cons, Multiset.map_singleton, Multiset.insert_eq_cons]
    _ = encL (X.i + 1) (({s.1, s.2.1, s.2.2, d} : Multiset ℕ).sort (· ≤ ·)) X.p := by
      have hms' : ({a, b, c, d} : Multiset ℕ) = ({s.1, s.2.1, s.2.2, d} : Multiset ℕ) := by
        calc
          ({a, b, c, d} : Multiset ℕ) = ({a, b, c} : Multiset ℕ) + {d} := by simp
          _ = ({s.1, s.2.1, s.2.2} : Multiset ℕ) + {d} := by rw [hms]
          _ = ({s.1, s.2.1, s.2.2, d} : Multiset ℕ) := by simp
      rw [hms']
    _ = G3K.Spec.encIns (X.i + 1) s.1 s.2.1 s.2.2 d X.p := by rw [hencIns]

theorem keyOf_enc (X : RState CState 4 4) (c1 c2 c3 c4 : ℕ)
    (h : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) :
    keyOf X = G3K.Spec.enc (X.i + 1) c1 c2 c3 c4 X.p := by
  simp only [keyOf, h, encL, List.getD_cons_succ, List.getD_cons_zero]

theorem keyOf_lump_enc (X : RState CState 4 4) (c1 c2 c3 c4 : ℕ)
    (hwf : ∀ c, cand.ChildWF (X.σ c)) (h : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) :
    keyOf (lumpState cand X) = G3K.Spec.lumpKey4 (X.i + 1) c1 c2 c3 c4 X.p := by
  have hm : codeMs X.σ = {c1, c2, c3, c4} := by
    rw [← Multiset.sort_eq (codeMs X.σ) (· ≤ ·), h]; rfl
  rw [keyOf_lump_encIns X c1 c2 c3 c4 hwf hm, G3K.Spec.lumpKey4]

/-! ### Targets -/

/-- The state the dominating chain takes for `X`: `X` if it is in the data with flag 1, else its
lump. -/
def keptOf (t : G3K.Tree) (X : RState CState 4 4) : RState CState 4 4 :=
  if keepOf t X = true then X else lumpState cand X

theorem keptOf_fields (t : G3K.Tree) (X : RState CState 4 4) :
    (keptOf t X).i = X.i ∧ (keptOf t X).e = X.e ∧ (keptOf t X).p = X.p ∧
      (keptOf t X).out = X.out := by
  unfold keptOf; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem keptOf_wf (t : G3K.Tree) (X : RState CState 4 4) (hwf : ∀ c, cand.ChildWF (X.σ c)) :
    ∀ c, cand.ChildWF ((keptOf t X).σ c) := by
  unfold keptOf; split_ifs
  · exact hwf
  · exact fun c => childWF_lumpC _ (hwf c)

/-- **The lookup of the checker** finds the state the chain takes, or fails. -/
theorem look_cases (t : G3K.Tree) (X : RState CState 4 4) :
    G3K.Spec.look t (keyOf X) (keyOf (lumpState cand X)) = G3K.Spec.bad ∨
      (G3K.Spec.look t (keyOf X) (keyOf (lumpState cand X)) = entry t (keptOf t X) ∧
        (entry t (keptOf t X)).key = keyOf (keptOf t X)) := by
  unfold G3K.Spec.look
  split_ifs with h1 h2
  · -- h1: (t.find (keyOf X)).key = keyOf X ∧ (t.find (keyOf X)).flag = 1
    by_cases hkeep : keepOf t X = true
    · -- keptOf t X = X
      simp [keptOf, hkeep, entry, h1.1]
    · -- keptOf t X = lumpState cand X (but h1 says key matches, so keepOf should be true, contradiction)
      have : keepOf t X = true := by
        unfold keepOf entry
        simp [h1.1, h1.2]
      exact absurd this hkeep
  · -- h1 fails, h2: (t.find (keyOf (lumpState cand X))).key = keyOf (lumpState cand X)
    by_cases hkeep : keepOf t X = true
    · -- keptOf t X = X, but h1 says key doesn't match, contradiction with hkeep
      unfold keepOf entry at hkeep
      simp at hkeep
      rcases hkeep with ⟨hk, hf⟩
      exact absurd (And.intro hk hf) h1
    · -- keptOf t X = lumpState cand X
      simp [keptOf, hkeep, entry, h2]
  · -- both h1 and h2 fail
    by_cases hkeep : keepOf t X = true
    · -- keptOf t X = X
      simp [keptOf, hkeep, entry]
    · -- keptOf t X = lumpState cand X
      simp [keptOf, hkeep, entry]

theorem decQ_keyOf (X : RState CState 4 4) (hwf : ∀ c, cand.ChildWF (X.σ c)) (hp : X.p < 128) :
    G3K.Spec.decQ (keyOf X) = X.i + 1 := by
  unfold keyOf encL
  let L := (codeMs X.σ).sort (· ≤ ·)
  have hbound (k : ℕ) : L.getD k 0 < 128 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : L[k]?
    · simp
    · rename_i a
      simp
      have ha_mem : a ∈ L := List.mem_of_getElem? h
      have ha_mem_codeMs : a ∈ codeMs X.σ := by
        rw [Multiset.mem_sort] at ha_mem
        exact ha_mem
      rw [codeMs] at ha_mem_codeMs
      rcases ((Multiset.mem_map (f := fun c => code (X.σ c)) (s := Finset.univ.val)).mp ha_mem_codeMs) with ⟨c, hc, ha_eq⟩
      rw [← ha_eq]
      have hcode_lt : code (X.σ c) < 38 := FrogModel.Engine.G3.code_lt (X.σ c) (hwf c)
      omega
  have h := FrogModel.Engine.G3.dec_enc (X.i + 1) (L.getD 0 0) (L.getD 1 0) (L.getD 2 0) (L.getD 3 0) X.p
    (hbound 0) (hbound 1) (hbound 2) (hbound 3) hp
  exact h.1

/-- The entry of a state in the data passed its bounds. -/
theorem entry_bounds (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hwf : ∀ c, cand.ChildWF (X.σ c)) (hp : X.p < 128) (hk : (entry t X).key = keyOf X) :
    G3K.Spec.boundsOK (entry t X) (X.i + 1) = true := by
  have := (G3K.Spec.checkAll_sound h (keyOf X) hk).1
  rwa [decQ_keyOf X hwf hp] at this

/-! ### The step of the dominating chain from a covered state -/

theorem domNext_live (t : G3K.Tree) (X X' : RState CState 4 4) (hi : X.i < 4) (he : X.e ≤ cand.T)
    (hi' : X'.i < 4) (he' : X'.e ≤ cand.T) (hp' : X'.p ≤ 16) :
    domNext cand.T 16 (keepOf t) (lumpState cand) (X, false) X' = (keptOf t X', false) := by
  unfold domNext keptOf
  have h1 : ¬ ((X, false).2 = true ∨ cand.T < (X, false).1.e ∨ 4 ≤ (X, false).1.i) := by
    simp only [Bool.false_eq_true, false_or, not_or, not_lt]; omega
  have h2 : ¬ (cand.T < X'.e ∨ 16 < X'.p) := by omega
  rw [if_neg h1, if_neg h2]
  by_cases hk : keepOf t X' = true
  · rw [if_pos (Or.inr hk), if_pos hk]
  · rw [if_neg (fun h => h.elim (by omega) hk), if_neg hk]

theorem domNext_flag (t : G3K.Tree) (X X' : RState CState 4 4) (hi : X.i < 4) (he : X.e ≤ cand.T)
    (h : cand.T < X'.e ∨ 16 < X'.p) :
    domNext cand.T 16 (keepOf t) (lumpState cand) (X, false) X' = (X', true) := by
  unfold domNext
  have h1 : ¬ ((X, false).2 = true ∨ cand.T < (X, false).1.e ∨ 4 ≤ (X, false).1.i) := by
    simp only [Bool.false_eq_true, false_or, not_or, not_lt]; omega
  rw [if_neg h1, if_pos h]

theorem domNext_abs (t : G3K.Tree) (X X' : RState CState 4 4) (hi : X.i < 4) (he : X.e ≤ cand.T)
    (he' : X'.e ≤ cand.T) (hp' : X'.p ≤ 16) (hi' : 4 ≤ X'.i) :
    domNext cand.T 16 (keepOf t) (lumpState cand) (X, false) X' = (X', false) := by
  unfold domNext
  have h1 : ¬ ((X, false).2 = true ∨ cand.T < (X, false).1.e ∨ 4 ≤ (X, false).1.i) := by
    simp only [Bool.false_eq_true, false_or, not_or, not_lt]; omega
  have h2 : ¬ (cand.T < X'.e ∨ 16 < X'.p) := by omega
  rw [if_neg h1, if_neg h2, if_pos (Or.inl hi')]

/-! ### Outputs -/

theorem incr_cons (o : Fin 4 → ℕ) (i e : ℕ) (hi : i < 4) :
    incr o i e = (oget o i - e) :: incr o (i + 1) (oget o i) := by
  interval_cases i
  · simp [FrogModel.Engine.G3.incr, FrogModel.Engine.G3.oget, List.range_succ]
  · simp [FrogModel.Engine.G3.incr, FrogModel.Engine.G3.oget, List.range_succ]
  · simp [FrogModel.Engine.G3.incr, FrogModel.Engine.G3.oget, List.range_succ]
  · simp [FrogModel.Engine.G3.incr, FrogModel.Engine.G3.oget, List.range_succ]

theorem laneIdx_single (n : ℕ) : laneIdx [n] = n := by
  simp only [laneIdx, List.length_nil, zero_add, List.sum_nil, add_zero, cntm]
  split_ifs with h
  · exact h.symm
  · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h), Nat.choose_one_right]

/-- The output `o` still fits after the frog `X.i` finishes at `e'`, iff `o` gives it `e'`. -/
theorem fits_succ (o : Fin 4 → ℕ) (X : RState CState 4 4) (hF : Fits o X) (hi : X.i + 1 < 4)
    (e' p' : ℕ) (σ' : Fin 4 → CState) (he : X.e ≤ e') :
    Fits o ⟨X.i + 1, e', p', σ', Function.update X.out ⟨X.i, by omega⟩ (e' : ℕ∞)⟩ ↔
      oget o X.i = e' := by
  have hi_lt : X.i < 4 := by omega
  constructor
  · intro hF'
    have hout := hF'.1 ⟨X.i, hi_lt⟩ (by simp)
    have h_eq : (e' : ℕ∞) = (o ⟨X.i, hi_lt⟩ : ℕ∞) := by
      simpa [Fits] using hout
    have h_oget : oget o X.i = o ⟨X.i, hi_lt⟩ := by
      unfold oget
      simp [hi_lt]
    have h_nat : e' = o ⟨X.i, hi_lt⟩ := by exact_mod_cast h_eq
    rw [h_oget, h_nat]
  · intro h_eq
    have h_oget_val : oget o X.i = e' := h_eq
    have h_oget : oget o X.i = o ⟨X.i, hi_lt⟩ := by
      unfold oget
      simp [hi_lt]
    have h_o_eq : o ⟨X.i, hi_lt⟩ = e' := by
      rw [← h_oget, h_oget_val]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- first conjunct: ∀ k, (k : ℕ) < X.i + 1 → X'.out k = (o k : ℕ∞)
      intro k hk_lt
      by_cases hk_eq : (k : ℕ) = X.i
      · -- k = X.i case
        have hk_fin_eq : k = ⟨X.i, hi_lt⟩ := by
          apply Fin.ext
          simpa
        subst hk_fin_eq
        simp [h_o_eq]
      · -- k < X.i case
        have hk_lt_Xi : (k : ℕ) < X.i :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk_lt) hk_eq
        have hk_fin_ne : k ≠ ⟨X.i, hi_lt⟩ := by
          intro h_eq_fin
          apply hk_eq
          simpa using congrArg Fin.val h_eq_fin
        simp [hk_fin_ne, hF.1 k hk_lt_Xi]
    · -- second conjunct: X'.e ≤ oget o X'.i, i.e., e' ≤ oget o (X.i + 1)
      have h_mono := hF.2.2.1 X.i (by rfl) hi
      rw [h_oget_val] at h_mono
      exact h_mono
    · -- third conjunct: monotonicity from X.i + 1
      intro k hk_le hk_succ
      simp at hk_le
      -- hk_le : X.i + 1 ≤ k
      have hX_le_k : X.i ≤ k := by omega
      exact hF.2.2.1 k hX_le_k hk_succ
    · -- fourth conjunct: o 3 ≤ cand.T
      exact hF.2.2.2

/-- The output `o` still fits a state of the same phase with `e'` exits iff `e' ≤ o_i`. -/
theorem fits_same (o : Fin 4 → ℕ) (X : RState CState 4 4) (hF : Fits o X) (e' p' : ℕ)
    (σ' : Fin 4 → CState) :
    Fits o ⟨X.i, e', p', σ', X.out⟩ ↔ e' ≤ oget o X.i := by
  constructor
  · intro h
    exact h.2.1
  · intro h
    exact ⟨hF.1, h, hF.2.2.1, hF.2.2.2⟩

/-- The last frog finishes at `e'`: the outputs are `o` iff `o_3 = e'`. -/
theorem fits_abs (o : Fin 4 → ℕ) (X : RState CState 4 4) (hF : Fits o X) (hi : X.i = 3) (e' : ℕ) :
    Function.update X.out ⟨X.i, by omega⟩ (e' : ℕ∞) = (fun k => (o k : ℕ∞)) ↔ o 3 = e' := by
  have hX : (⟨X.i, by omega⟩ : Fin 4) = (⟨3, by omega⟩ : Fin 4) := by
    ext; simp [hi]
  constructor
  · intro h
    have h3 := congrFun h (⟨3, by omega⟩ : Fin 4)
    simp [hX, Function.update_self] at h3
    have : (o 3 : ℕ∞) = (e' : ℕ∞) := by simpa using h3.symm
    exact ENat.natCast_inj.mp this
  · intro h
    subst h
    ext k
    by_cases hk : (k : ℕ) = 3
    · have hk_eq : k = (⟨3, by omega⟩ : Fin 4) := by ext; exact hk
      rw [hk_eq]
      simp [hX, Function.update_self]
    · have hlt : (k : ℕ) < X.i := by
        have : (k : ℕ) < 4 := k.2
        omega
      have h_update_ne : Function.update X.out ⟨X.i, by omega⟩ (o 3 : ℕ∞) k = X.out k := by
        apply Function.update_of_ne
        intro h_eq
        apply hk
        have : (k : ℕ) = (⟨X.i, by omega⟩ : Fin 4) := by
          exact congrArg Fin.val h_eq
        simpa [hi] using this
      rw [h_update_ne, hF.1 k hlt]

theorem incr_length (o : Fin 4 → ℕ) (i e : ℕ) : (incr o i e).length = 4 - i := by
  simp [incr]

theorem incr_sum (o : Fin 4 → ℕ) (X : RState CState 4 4) (hF : Fits o X) (hi : X.i < 4) :
    (incr o X.i X.e).sum ≤ cand.T := by
  rcases hF with ⟨hout, he, hmono, hT⟩
  have hcases : X.i = 0 ∨ X.i = 1 ∨ X.i = 2 ∨ X.i = 3 := by omega
  rcases hcases with (h | h | h | h)
  · -- X.i = 0
    rw [h] at he ⊢
    unfold incr
    simp [oget, List.range_succ, List.sum_cons, List.sum_nil, -tsub_le_iff_right, -Nat.sub_le_iff_le_add]
    have h01 : o 0 ≤ o 1 := hmono 0 (by omega) (by omega)
    have h12 : o 1 ≤ o 2 := hmono 1 (by omega) (by omega)
    have h23 : o 2 ≤ o 3 := hmono 2 (by omega) (by omega)
    have hX0 : X.e ≤ o 0 := by simpa [oget] using he
    have hX1 : X.e ≤ o 1 := le_trans hX0 h01
    have hX2 : X.e ≤ o 2 := le_trans hX1 h12
    have htemp1 : (o 0 - X.e) + (o 1 - o 0) = o 1 - X.e := by
      rw [add_comm, Nat.sub_add_sub_cancel h01 hX0]
    have htemp2 : (o 1 - X.e) + (o 2 - o 1) = o 2 - X.e := by
      rw [add_comm, Nat.sub_add_sub_cancel h12 hX1]
    have htemp3 : (o 2 - X.e) + (o 3 - o 2) = o 3 - X.e := by
      rw [add_comm, Nat.sub_add_sub_cancel h23 hX2]
    rw [← add_assoc, htemp1, ← add_assoc, htemp2, htemp3]
    apply le_trans (Nat.sub_le (o 3) X.e)
    exact hT
  · -- X.i = 1
    rw [h] at he ⊢
    unfold incr
    simp [oget, List.range_succ, List.sum_cons, List.sum_nil, -tsub_le_iff_right, -Nat.sub_le_iff_le_add]
    have h12 : o 1 ≤ o 2 := hmono 1 (by omega) (by omega)
    have h23 : o 2 ≤ o 3 := hmono 2 (by omega) (by omega)
    have hX1 : X.e ≤ o 1 := by simpa [oget] using he
    have hX2 : X.e ≤ o 2 := le_trans hX1 h12
    have htemp1 : (o 1 - X.e) + (o 2 - o 1) = o 2 - X.e := by
      rw [add_comm, Nat.sub_add_sub_cancel h12 hX1]
    have htemp2 : (o 2 - X.e) + (o 3 - o 2) = o 3 - X.e := by
      rw [add_comm, Nat.sub_add_sub_cancel h23 hX2]
    rw [← add_assoc, htemp1, htemp2]
    apply le_trans (Nat.sub_le (o 3) X.e)
    exact hT
  · -- X.i = 2
    rw [h] at he ⊢
    unfold incr
    simp [oget, List.range_succ, List.sum_cons, List.sum_nil, -tsub_le_iff_right, -Nat.sub_le_iff_le_add]
    have h23 : o 2 ≤ o 3 := hmono 2 (by omega) (by omega)
    have hX2 : X.e ≤ o 2 := by simpa [oget] using he
    have htemp : (o 2 - X.e) + (o 3 - o 2) = o 3 - X.e := by
      rw [add_comm, Nat.sub_add_sub_cancel h23 hX2]
    rw [htemp]
    apply le_trans (Nat.sub_le (o 3) X.e)
    exact hT
  · -- X.i = 3
    rw [h] at he ⊢
    unfold incr
    simp [oget, List.range_succ, List.sum_cons, List.sum_nil, -tsub_le_iff_right, -Nat.sub_le_iff_le_add]
    have hX3 : X.e ≤ o 3 := by simpa [oget] using he
    apply le_trans (Nat.sub_le (o 3) X.e)
    exact hT

/-! ### The lanes of the increments -/

/-- The vectors of length `L` with total at most `n`. -/
def allVecs : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | L + 1, n => (List.range (n + 1)).flatMap fun x => (allVecs L (n - x)).map (x :: ·)

theorem mem_allVecs (L n : ℕ) (v : List ℕ) (hl : v.length = L) (hs : v.sum ≤ n) :
    v ∈ allVecs L n := by
  induction' L with L IH generalizing v n
  · -- L = 0, so v.length = 0, hence v = []
    have hv_nil : v = [] := by
      simpa using List.eq_nil_of_length_eq_zero (by simpa [hl])
    subst hv_nil
    simp [FrogModel.Engine.G3.allVecs]
  · -- L + 1
    match v with
    | [] =>
      -- v = [], but v.length = L+1 > 0, contradiction
      simp at hl
    | x :: xs =>
      have hlen : (x :: xs).length = L + 1 := hl
      simp at hlen
      -- hlen gives: xs.length = L
      have hlen_xs : xs.length = L := by
        simpa using hlen
      have hsum : (x :: xs).sum ≤ n := hs
      simp [List.sum_cons] at hsum
      -- hsum : x + xs.sum ≤ n
      have hx_le_n : x ≤ n := by
        omega
      have hxs_sum_le : xs.sum ≤ n - x := by
        omega
      -- Now use the definition of allVecs (L+1) n
      rw [FrogModel.Engine.G3.allVecs]
      -- Need: x :: xs ∈ (List.range (n + 1)).flatMap fun x => (allVecs L (n - x)).map (x :: ·)
      -- Use List.mem_flatMap
      -- Need to find a witness a in List.range (n+1) such that x :: xs ∈ (allVecs L (n - a)).map (a :: ·)
      -- The witness is a = x
      have hx_mem_range : x ∈ List.range (n + 1) := by
        rw [List.mem_range]
        omega
      refine List.mem_flatMap.mpr ?_
      refine ⟨x, hx_mem_range, ?_⟩
      -- Now need: x :: xs ∈ (allVecs L (n - x)).map (x :: ·)
      rw [List.mem_map]
      -- Need ∃ a, a ∈ allVecs L (n - x) ∧ (x :: ·) a = x :: xs
      -- That is: ∃ a, a ∈ allVecs L (n - x) ∧ x :: a = x :: xs
      -- So a = xs
      refine ⟨xs, ?_, rfl⟩
      -- Need: xs ∈ allVecs L (n - x)
      -- By IH: for any v', n' such that v'.length = L and v'.sum ≤ n', we have v' ∈ allVecs L n'
      -- Here v' = xs, n' = n - x
      -- We have hlen_xs: xs.length = L
      -- And hxs_sum_le: xs.sum ≤ n - x
      -- So apply IH
      exact IH (n - x) xs hlen_xs hxs_sum_le

/-- The lanes of phase `q`: below `nL`; the exit `gx` sends `(x + 1, xs)` to `(x, xs)`... read as
sources: lane `(x, xs)` of the exit comes from lane `(x - 1, xs)`; `cp0` and `cp1` take lane
`(0, xs)` and `(1, xs)` from lane `xs` of phase `q + 1`. -/
def LanesOK (q : ℕ) : Prop :=
  ∀ v ∈ allVecs (5 - q) 8, laneIdx v < (G3K.phase q).nL ∧
    gsrc (G3K.phase q).gx (laneIdx v) =
      (if 1 ≤ v.headD 0 then some (laneIdx ((v.headD 0 - 1) :: v.tail)) else none) ∧
    (q < 4 → gsrc (G3K.phase q).cp0 (laneIdx v) =
      if v.headD 0 = 0 then some (laneIdx v.tail) else none) ∧
    (q < 4 → gsrc (G3K.phase q).cp1 (laneIdx v) =
      if v.headD 0 = 1 then some (laneIdx v.tail) else none)

set_option maxRecDepth 100000 in
theorem lanesOK_1 : LanesOK 1 := by unfold LanesOK; decide +kernel
set_option maxRecDepth 100000 in
theorem lanesOK_2 : LanesOK 2 := by unfold LanesOK; decide +kernel
set_option maxRecDepth 100000 in
theorem lanesOK_3 : LanesOK 3 := by unfold LanesOK; decide +kernel
set_option maxRecDepth 100000 in
theorem lanesOK_4 : LanesOK 4 := by unfold LanesOK; decide +kernel

theorem lanesOK (q : ℕ) (hq : 1 ≤ q) (hq4 : q ≤ 4) : LanesOK q := by
  interval_cases q
  exacts [lanesOK_1, lanesOK_2, lanesOK_3, lanesOK_4]

/-! ### The children, through their codes -/

/-- The children of `X` permuted by `π`. -/
def permS (π : Equiv.Perm (Fin 4)) (X : RState CState 4 4) : RState CState 4 4 :=
  ⟨X.i, X.e, X.p, X.σ ∘ π, X.out⟩

theorem keyOf_permS (π : Equiv.Perm (Fin 4)) (Z : RState CState 4 4) :
    keyOf (permS π Z) = keyOf Z := by
  simp only [keyOf, permS]
  have h : codeMs (Z.σ ∘ π) = codeMs Z.σ := by
    dsimp [codeMs]
    calc
      Multiset.map (fun c => code ((Z.σ ∘ π) c)) Finset.univ.val
          = Multiset.map (code ∘ Z.σ ∘ π) Finset.univ.val := rfl
      _ = Multiset.map ((code ∘ Z.σ) ∘ (⇑π)) Finset.univ.val := rfl
      _ = Multiset.map (code ∘ Z.σ) (Multiset.map (⇑π) Finset.univ.val) := by
        rw [← Multiset.map_map (code ∘ Z.σ) (⇑π)]
      _ = Multiset.map (code ∘ Z.σ) Finset.univ.val := by
        rw [Multiset.map_univ_val_equiv π]
      _ = Multiset.map (fun c => code (Z.σ c)) Finset.univ.val := rfl
  rw [h]

theorem keepOf_permS (t : G3K.Tree) (π : Equiv.Perm (Fin 4)) (X : RState CState 4 4) :
    keepOf t (permS π X) = keepOf t X := by
  unfold keepOf entry
  rw [keyOf_permS π X]

theorem lumpState_permS (D : Data) (π : Equiv.Perm (Fin 4)) (X : RState CState 4 4) :
    lumpState D (permS π X) = permS π (lumpState D X) :=
  rfl

theorem entry_permS (t : G3K.Tree) (π : Equiv.Perm (Fin 4)) (Z : RState CState 4 4) :
    entry t (permS π Z) = entry t Z := by
  unfold entry; rw [keyOf_permS]

theorem covered_permS (t : G3K.Tree) (π : Equiv.Perm (Fin 4)) (Z : RState CState 4 4) (b : Bool) :
    Covered t (permS π Z, b) ↔ Covered t (Z, b) := by
  unfold Covered
  simp only [entry_permS, keyOf_permS]
  have h : (∀ c, cand.ChildWF ((permS π Z).σ c)) ↔ ∀ c, cand.ChildWF (Z.σ c) :=
    Equiv.forall_congr_right π (q := fun c => cand.ChildWF (Z.σ c))
  rw [h]; rfl

theorem tauV_perm (t : G3K.Tree) (o : Fin 4 → ℕ) (y : RState CState 4 4 × Bool)
    (π : Equiv.Perm (Fin 4)) (Z : RState CState 4 4) (b : Bool) :
    tauV t o y (permS π Z, b) = tauV t o y (Z, b) := by
  have hF : Fits o (permS π Z) ↔ Fits o Z := Iff.rfl
  have hA : absInd o y (permS π Z, b) = absInd o y (Z, b) := rfl
  unfold tauV
  rw [hA]
  congr 1
  unfold Vs
  have hC := covered_permS t π Z b
  rw [entry_permS]
  by_cases h : Covered t (Z, b) ∧ Fits o Z
  · rw [ite_eq_left (by rwa [hC, hF]), ite_eq_left h]; rfl
  · rw [ite_eq_right (by rwa [hC, hF]), ite_eq_right h]

theorem tauW_perm (t : G3K.Tree) (y : RState CState 4 4 × Bool) (π : Equiv.Perm (Fin 4))
    (Z : RState CState 4 4) (b : Bool) : tauW t y (permS π Z, b) = tauW t y (Z, b) := by
  unfold tauW Ws Covered entry keyOf
  simp [permS]
  have h_codeMs : codeMs (Z.σ ∘ π) = codeMs Z.σ := by
    unfold codeMs
    calc
      Multiset.map (fun c => code ((Z.σ ∘ π) c)) Finset.univ.val
          = Multiset.map (fun c => code (Z.σ (π c))) Finset.univ.val := rfl
      _ = Multiset.map ((code ∘ Z.σ) ∘ π) Finset.univ.val := rfl
      _ = Multiset.map (code ∘ Z.σ) (Multiset.map π Finset.univ.val) := by
        rw [Multiset.map_map]
      _ = Multiset.map (code ∘ Z.σ) Finset.univ.val := by
        rw [Multiset.map_univ_val_equiv π]
      _ = Multiset.map (fun c => code (Z.σ c)) Finset.univ.val := rfl
  have h_keyOf : (encL (Z.i + 1) ((codeMs (Z.σ ∘ π)).sort (· ≤ ·)) Z.p) =
      (encL (Z.i + 1) ((codeMs Z.σ).sort (· ≤ ·)) Z.p) := by
    rw [h_codeMs]
  have h_childWF : (∀ (c : Fin 4), cand.ChildWF (Z.σ (π c))) ↔ (∀ (c : Fin 4), cand.ChildWF (Z.σ c)) :=
    Equiv.forall_congr_right π (q := fun c => cand.ChildWF (Z.σ c))
  have h_phiC : phiC (permS π Z) = phiC Z := by
    unfold phiC
    have h1 : cand.PhiQ (permS π Z) = cand.PhiQ Z := by
      unfold Data.PhiQ
      simp [permS]
      have h_prod : (∏ c : Fin 4, cand.wQ (Z.σ (π c))) = (∏ c : Fin 4, cand.wQ (Z.σ c)) :=
        Fintype.prod_equiv π (fun c => cand.wQ (Z.σ (π c))) (fun c => cand.wQ (Z.σ c)) (fun _ => rfl)
      simp [h_prod]
    rw [h1]
  by_cases hcond : b = true ∨ 4 ≤ Z.i ∨ cand.T < Z.e
  · dsimp [permS] at *
    rw [h_phiC]
    simp [hcond]
  · simp [hcond]
    by_cases hcovered : b = false ∧ Z.i < 4 ∧ Z.e ≤ cand.T ∧ 1 ≤ Z.p ∧ Z.p ≤ 16 ∧
        (∀ (c : Fin 4), cand.ChildWF (Z.σ (π c))) ∧
        (t.find (encL (Z.i + 1) ((codeMs (Z.σ ∘ π)).sort (· ≤ ·)) Z.p)).key =
          encL (Z.i + 1) ((codeMs (Z.σ ∘ π)).sort (· ≤ ·)) Z.p
    · have hcovered' : b = false ∧ Z.i < 4 ∧ Z.e ≤ cand.T ∧ 1 ≤ Z.p ∧ Z.p ≤ 16 ∧
          (∀ (c : Fin 4), cand.ChildWF (Z.σ c)) ∧
          (t.find (encL (Z.i + 1) ((codeMs Z.σ).sort (· ≤ ·)) Z.p)).key =
            encL (Z.i + 1) ((codeMs Z.σ).sort (· ≤ ·)) Z.p := by
        rcases hcovered with ⟨hb, hi, he, hp1, hp2, hchild, hkey⟩
        refine ⟨hb, hi, he, hp1, hp2, h_childWF.mp hchild, ?_⟩
        simpa [h_keyOf] using hkey
      simp [hcovered, hcovered', h_keyOf]
    · have hcovered' : ¬ (b = false ∧ Z.i < 4 ∧ Z.e ≤ cand.T ∧ 1 ≤ Z.p ∧ Z.p ≤ 16 ∧
          (∀ (c : Fin 4), cand.ChildWF (Z.σ c)) ∧
          (t.find (encL (Z.i + 1) ((codeMs Z.σ).sort (· ≤ ·)) Z.p)).key =
            encL (Z.i + 1) ((codeMs Z.σ).sort (· ≤ ·)) Z.p) := by
        intro h
        apply hcovered
        rcases h with ⟨hb, hi, he, hp1, hp2, hchild, hkey⟩
        refine ⟨hb, hi, he, hp1, hp2, h_childWF.mpr hchild, ?_⟩
        simpa [h_keyOf] using hkey
      simp [hcovered, hcovered']

theorem domNext_perm (t : G3K.Tree) (y : RState CState 4 4 × Bool) (π : Equiv.Perm (Fin 4))
    (X' : RState CState 4 4) :
    domNext cand.T 16 (keepOf t) (lumpState cand) y (permS π X') =
      (permS π (domNext cand.T 16 (keepOf t) (lumpState cand) y X').1,
        (domNext cand.T 16 (keepOf t) (lumpState cand) y X').2) := by
  unfold domNext
  rw [keepOf_permS t π X']
  have he : (permS π X').e = X'.e := rfl
  have hp : (permS π X').p = X'.p := rfl
  have hi : (permS π X').i = X'.i := rfl
  rw [he, hp, hi]
  by_cases h1 : y.2 = true ∨ cand.T < y.1.e ∨ 4 ≤ y.1.i
  · simp [h1]
  · by_cases h2 : cand.T < X'.e ∨ 16 < X'.p
    · simp [h1, h2]
    · by_cases h3 : 4 ≤ X'.i ∨ keepOf t X' = true
      · simp [h1, h2, h3]
      · simp [h1, h2, h3, lumpState_permS cand π X']

theorem rstepR_swap (X : RState CState 4 4) (c c' : Fin 4) (r : ℕ × CState)
    (h : X.σ c = X.σ c') : rstepR X c' r = permS (Equiv.swap c c') (rstepR X c r) := by
  dsimp [rstepR, FrogModel.Engine.G3.permS]
  split_ifs with h_i h_p
  · apply RState.injective_tuple; simp
    funext k; simp [Function.comp_apply]
    by_cases hk_c' : k = c'
    · subst hk_c'; rw [Function.update_self, Equiv.swap_apply_right, Function.update_self]
    · by_cases hk_c : k = c
      · subst hk_c; rw [Equiv.swap_apply_left, Function.update_of_ne hk_c', Function.update_of_ne (Ne.symm hk_c')]; exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hk_c hk_c', Function.update_of_ne hk_c, Function.update_of_ne hk_c']
  · apply RState.injective_tuple; simp
    funext k; simp [Function.comp_apply]
    by_cases hk_c' : k = c'
    · subst hk_c'; rw [Function.update_self, Equiv.swap_apply_right, Function.update_self]
    · by_cases hk_c : k = c
      · subst hk_c; rw [Equiv.swap_apply_left, Function.update_of_ne hk_c', Function.update_of_ne (Ne.symm hk_c')]; exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hk_c hk_c', Function.update_of_ne hk_c, Function.update_of_ne hk_c']
  · apply RState.injective_tuple; simp
    funext k; simp [Function.comp_apply]
    by_cases hk_c' : k = c'
    · subst hk_c'; rw [Equiv.swap_apply_right]; exact h.symm
    · by_cases hk_c : k = c
      · subst hk_c; rw [Equiv.swap_apply_left]; exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hk_c hk_c']

/-- The moves of child `c` under a reward `Φ` of the state reached that ignores the order of the
children: equal for two children in the same state. -/
theorem moveSum_congr (t : G3K.Tree) (X : RState CState 4 4)
    (Φ : RState CState 4 4 × Bool → ℝ≥0∞) (hΦ : ∀ π Z b, Φ (permS π Z, b) = Φ (Z, b))
    (c c' : Fin 4) (h : X.σ c = X.σ c') :
    moveSum cand (X.σ c') (fun r => Φ (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        (rstepR X c' r))) =
      moveSum cand (X.σ c) (fun r => Φ (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        (rstepR X c r))) := by
  rw [← h]
  congr 1
  funext r
  calc
    Φ (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false) (rstepR X c' r))
        = Φ (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
            (permS (Equiv.swap c c') (rstepR X c r))) := by
      rw [rstepR_swap X c c' r h]
    _ = Φ ((permS (Equiv.swap c c') ((domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
            (rstepR X c r)).1)),
          (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
            (rstepR X c r)).2) := by
      rw [domNext_perm t (X, false) (Equiv.swap c c') (rstepR X c r)]
    _ = Φ ((domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
            (rstepR X c r)).1,
          (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
            (rstepR X c r)).2) := by
      rw [hΦ (Equiv.swap c c') ((domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
            (rstepR X c r)).1) ((domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
            (rstepR X c r)).2)]
    _ = Φ (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
            (rstepR X c r)) := rfl

theorem code_inj_of_wf (X : RState CState 4 4) (hwf : ∀ c, cand.ChildWF (X.σ c)) :
    ∀ c c', code (X.σ c) = code (X.σ c') → X.σ c = X.σ c' := by
  intro c c' h
  rw [← decC_code _ (hwf c), ← decC_code _ (hwf c'), h]

open Classical in
/-- The value of a function of the children at a child of code `a`, `0` if there is none. -/
noncomputable def perCode (X : RState CState 4 4) (F : Fin 4 → ℝ≥0∞) (a : ℕ) : ℝ≥0∞ :=
  if h : ∃ c, code (X.σ c) = a then F h.choose else 0

theorem perCode_eq (X : RState CState 4 4)
    (hinj : ∀ c c', code (X.σ c) = code (X.σ c') → X.σ c = X.σ c')
    (F : Fin 4 → ℝ≥0∞) (hF : ∀ c c', X.σ c = X.σ c' → F c = F c') (c : Fin 4) :
    perCode X F (code (X.σ c)) = F c := by
  unfold FrogModel.Engine.G3.perCode
  have h : ∃ c', FrogModel.Engine.G3.code (X.σ c') = FrogModel.Engine.G3.code (X.σ c) := ⟨c, rfl⟩
  rw [dite_eq_left h]
  have hspec := h.choose_spec
  have hσ := hinj h.choose c hspec
  have hF' := hF h.choose c hσ
  rw [hF']

/-- **The sum over the children** is the sum over their sorted codes. -/
theorem sum_perCode (X : RState CState 4 4)
    (hinj : ∀ c c', code (X.σ c) = code (X.σ c') → X.σ c = X.σ c')
    (F : Fin 4 → ℝ≥0∞) (hF : ∀ c c', X.σ c = X.σ c' → F c = F c') (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) :
    ∑ c, F c = perCode X F c1 + perCode X F c2 + perCode X F c3 + perCode X F c4 := by
  have h_eq : ∀ c : Fin 4, F c = FrogModel.Engine.G3.perCode X F (FrogModel.Engine.G3.code (X.σ c)) := by
    intro c
    dsimp [FrogModel.Engine.G3.perCode]
    split
    · rename_i h
      rw [← hF h.choose c (hinj _ _ h.choose_spec)]
    · rename_i h
      exfalso
      apply h
      exact ⟨c, rfl⟩
  have h_ms_eq : FrogModel.Engine.G3.codeMs X.σ = (↑[c1, c2, c3, c4] : Multiset ℕ) := by
    calc
      FrogModel.Engine.G3.codeMs X.σ = ↑((FrogModel.Engine.G3.codeMs X.σ).sort (· ≤ ·)) := by
        rw [Multiset.sort_eq]
      _ = ↑[c1, c2, c3, c4] := by rw [hL]
  have h_sum_eq : ∑ c, F c = ((FrogModel.Engine.G3.codeMs X.σ).map (FrogModel.Engine.G3.perCode X F)).sum := by
    have h1 : ∑ c, F c = ∑ c, FrogModel.Engine.G3.perCode X F (FrogModel.Engine.G3.code (X.σ c)) :=
      Finset.sum_congr rfl (fun c _ => by rw [h_eq c])
    have h2 : ∑ c, FrogModel.Engine.G3.perCode X F (FrogModel.Engine.G3.code (X.σ c)) =
        ((FrogModel.Engine.G3.codeMs X.σ).map (FrogModel.Engine.G3.perCode X F)).sum := by
      dsimp [FrogModel.Engine.G3.codeMs]
      simp [Finset.sum]
    rw [h1, h2]
  rw [h_sum_eq, h_ms_eq]
  simp [add_assoc]

/-- A code of the sorted list is the code of a child, and the other three are the rest. -/
theorem exists_child_of_code (X : RState CState 4 4) (a u1 u2 u3 : ℕ)
    (h : ({u1, u2, u3, a} : Multiset ℕ) = codeMs X.σ) :
    ∃ c, code (X.σ c) = a ∧ codeMs X.σ = {u1, u2, u3, code (X.σ c)} := by
  have ha_mem : a ∈ ({u1, u2, u3, a} : Multiset ℕ) := by
    simp
  have ha_mem_code : a ∈ FrogModel.Engine.G3.codeMs X.σ := by
    rw [← h]
    exact ha_mem
  rcases Multiset.mem_map.mp ha_mem_code with ⟨c, hc_mem, hc_code⟩
  refine ⟨c, hc_code, ?_⟩
  calc
    FrogModel.Engine.G3.codeMs X.σ = ({u1, u2, u3, a} : Multiset ℕ) := h.symm
    _ = ({u1, u2, u3, FrogModel.Engine.G3.code (X.σ c)} : Multiset ℕ) := by simp [hc_code]

theorem ms4_rot (a b c d : ℕ) : ({b, c, d, a} : Multiset ℕ) = {a, b, c, d} := by
  ext x; simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

theorem ms4_rot3 (a b c d : ℕ) : ({a, c, d, b} : Multiset ℕ) = {a, b, c, d} := by
  ext x; simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

theorem ms4_swap (a b c d : ℕ) : ({a, b, d, c} : Multiset ℕ) = {a, b, c, d} := by
  ext x; simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- **The moves of the checker** keep an invariant `P` that each child keeps, with the
contribution of each code counted with its multiplicity. -/
theorem moves_inv {ι : Type*} (P : G3K.Spec.Acc → (ι → ℝ≥0∞) → Prop) (t : G3K.Tree)
    (q p c1 c2 c3 c4 : ℕ) (Gc : ℕ → ι → ℝ≥0∞) (h12 : c1 ≤ c2) (h23 : c2 ≤ c3) (h34 : c3 ≤ c4)
    (h0 : P G3K.Spec.acc0 0)
    (hch : ∀ a u1 u2 u3 m acc R, u1 ≤ u2 → u2 ≤ u3 →
      ({u1, u2, u3, a} : Multiset ℕ) = {c1, c2, c3, c4} → P acc R →
      P (G3K.Spec.child t q a u1 u2 u3 p m acc) (fun i => R i + m * Gc a i)) :
    P (G3K.Spec.moves t q c1 c2 c3 c4 p) (fun i => Gc c1 i + Gc c2 i + Gc c3 i + Gc c4 i) := by
  have hs : ∀ a u1 u2 u3 (m : ℕ) acc R R', u1 ≤ u2 → u2 ≤ u3 →
      ({u1, u2, u3, a} : Multiset ℕ) = {c1, c2, c3, c4} → P acc R →
      (∀ i, R' i = R i + m * Gc a i) → P (G3K.Spec.child t q a u1 u2 u3 p m acc) R' := by
    intro a u1 u2 u3 m acc R R' h1 h2 hm hP hR
    have e : R' = fun i => R i + m * Gc a i := funext hR
    subst e
    exact hch a u1 u2 u3 m acc R h1 h2 hm hP
  have hA := ms4_rot c1 c2 c3 c4
  have hB := ms4_rot3 c1 c2 c3 c4
  have hC := ms4_swap c1 c2 c3 c4
  have h13 : c1 ≤ c3 := h12.trans h23
  have h24 : c2 ≤ c4 := h23.trans h34
  have h1 := hs c1 c2 c3 c4 1 _ 0 (fun i => Gc c1 i) h23 h34 hA h0 (fun i => by simp)
  have h2 := hs c1 c2 c3 c4 2 _ 0 (fun i => 2 * Gc c1 i) h23 h34 hA h0 (fun i => by simp)
  have h3 := hs c1 c2 c3 c4 3 _ 0 (fun i => 3 * Gc c1 i) h23 h34 hA h0 (fun i => by simp)
  unfold G3K.Spec.moves
  split_ifs with h43 h32 h21 h32' h21' h21''
  · exact hs c1 c2 c3 c4 4 _ 0 _ h23 h34 hA h0 (fun i => by subst_vars; simp; ring)
  · exact hs c2 c1 c3 c4 3 _ _ _ h13 h34 hB h1 (fun i => by subst_vars; push_cast; ring)
  · exact hs c3 c1 c2 c4 2 _ _ _ h12 h24 hC h2 (fun i => by subst_vars; push_cast; ring)
  · exact hs c3 c1 c2 c4 2 _ (fun i => Gc c1 i + Gc c2 i) _ h12 h24 hC
      (hs c2 c1 c3 c4 1 _ _ _ h13 h34 hB h1 (fun i => by simp)) (fun i => by subst_vars; push_cast; ring)
  · exact hs c4 c1 c2 c3 1 _ (fun i => 3 * Gc c1 i) _ h12 h23 rfl h3 (fun i => by subst_vars; push_cast; ring)
  · exact hs c4 c1 c2 c3 1 _ (fun i => Gc c1 i + 2 * Gc c2 i) _ h12 h23 rfl
      (hs c2 c1 c3 c4 2 _ _ _ h13 h34 hB h1 (fun i => by simp)) (fun i => by subst_vars; push_cast; ring)
  · exact hs c4 c1 c2 c3 1 _ (fun i => 2 * Gc c1 i + Gc c3 i) _ h12 h23 rfl
      (hs c3 c1 c2 c4 1 _ _ _ h12 h24 hC h2 (fun i => by simp)) (fun i => by subst_vars; push_cast; ring)
  · exact hs c4 c1 c2 c3 1 _ (fun i => Gc c1 i + Gc c2 i + Gc c3 i) _ h12 h23 rfl
      (hs c3 c1 c2 c4 1 _ (fun i => Gc c1 i + Gc c2 i) _ h12 h24 hC
        (hs c2 c1 c3 c4 1 _ _ _ h13 h34 hB h1 (fun i => by simp)) (fun i => by simp))
      (fun i => by push_cast; ring)

end FrogModel.Engine.G3
