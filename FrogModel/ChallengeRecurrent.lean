module

public import Mathlib

@[expose] public section

-- The frozen statement of the model, verbatim from its second line, less the definition `Transient` and its two
-- theorems (the case d = 4, in FrogModel/Challenge.lean), then the definition `Recurrent` and the target of the
-- case d = 3, verbatim. The docstring below is the frozen one, written for d = 4. The `sorry` is the target.

/-!
# Frozen statement: the frog model on the rooted 4-ary tree is transient

On the rooted 4-ary tree, one active frog at the root and one sleeping frog at every
other vertex; active frogs perform independent simple random walks and wake every sleeping frog
they visit. Claim: the root is visited only finitely often almost surely. Lean, for every `d`:
`Vertex d` = words over `Fin d`, root `[]`, children of `v` the words `c :: v` (graph `tree d`).
`step v ξ` is one walk step driven by `ξ = (a, b) : Fin d × Fin (d + 1)` with uniform law
`stepLaw d`: from the root to the child `a`, elsewhere `b = 0` parent, `b = c + 1` child `c`; its
law is uniform on the neighbours of `v` (`map_step_eq_uniformOn`). `frogMeasure d`: independent
step variables for every (frog, time); frog `u` walks from `u` on its own (`paths`). `wake`: the
synchronous wake times, by recursion on time. `visits`: pairs (frog, time `≥ 1`) at the root.
`Transient d`: `visits` is finite almost surely. Target: `transient_four : Transient 4`.
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel

/-- Vertices of the rooted `d`-ary tree: finite words over `Fin d`; `c :: v` is the child `c`
of `v`. -/
abbrev Vertex (d : ℕ) := List (Fin d)

/-- A countable type, with every set measurable. -/
instance (d : ℕ) : MeasurableSpace (Vertex d) := ⊤

instance (d : ℕ) : DiscreteMeasurableSpace (Vertex d) := ⟨fun _ => trivial⟩

variable {d : ℕ}

/-- The root: the empty word. -/
def root : Vertex d := []

/-- The rooted `d`-ary tree as a graph: `v` and `w` are adjacent when one is a child of the
other. -/
def tree (d : ℕ) : SimpleGraph (Vertex d) where
  Adj v w := (∃ c, w = c :: v) ∨ ∃ c, v = c :: w
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun v h => by
    rcases h with ⟨c, h⟩ | ⟨c, h⟩ <;> exact List.cons_ne_self c v h.symm⟩

/-- The step variable of a frog at one time: `a` is used at the root, `b` elsewhere. -/
abbrev Step (d : ℕ) := Fin d × Fin (d + 1)

/-- One step of the walk from `v` driven by `ξ = (a, b)`: from the root to its child `a`; from
any other vertex to its parent if `b = 0`, to its child `c` if `b = c + 1`. -/
def step : Vertex d → Step d → Vertex d
  | [], ξ => [ξ.1]
  | c :: w, ξ => if h : ξ.2 = 0 then w else ξ.2.pred h :: c :: w

/-- The walk from `u` driven by the step sequence `x`. -/
def walk (u : Vertex d) (x : ℕ → Step d) : ℕ → Vertex d
  | 0 => u
  | n + 1 => step (walk u x n) (x n)

/-- The law of one step variable: uniform on `Fin d × Fin (d + 1)`. -/
noncomputable def stepLaw (d : ℕ) : Measure (Step d) := uniformOn Set.univ

instance [NeZero d] : IsProbabilityMeasure (stepLaw d) := by
  unfold stepLaw
  infer_instance

/-- The sample space: one step variable for every frog (named by its starting vertex) and every
time. -/
abbrev Sample (d : ℕ) := Vertex d → ℕ → Step d

/-- The law of the frog model: all step variables independent, each with law `stepLaw d`. -/
noncomputable def frogMeasure (d : ℕ) [NeZero d] : Measure (Sample d) :=
  Measure.infinitePi fun _ : Vertex d => Measure.infinitePi fun _ : ℕ => stepLaw d

/-- The path of frog `u`: the walk from `u` driven by its own step variables. -/
def paths (ω : Sample d) (u : Vertex d) : ℕ → Vertex d := walk u (ω u)

open Classical in
/-- Wake times, by recursion on time, for frogs with paths `S`: `wake S t u = some s` when frog
`u` is active at time `t` and was woken at time `s ≤ t` (it is then at `S u (t - s)`), `none`
when it is still asleep at time `t`. At time `0` only the root frog is active; a sleeping frog `u`
wakes at time `t + 1` when a frog active at time `t` is at `u` at time `t + 1`. -/
noncomputable def wake (S : Vertex d → ℕ → Vertex d) : ℕ → Vertex d → Option ℕ
  | 0, u => if u = root then some 0 else none
  | t + 1, u =>
    match wake S t u with
    | some s => some s
    | none => if ∃ w s, wake S t w = some s ∧ S w (t + 1 - s) = u then some (t + 1) else none

/-- The visits to the root after time `0`: the pairs `(u, t)`, `t ≥ 1`, such that frog `u` is
active at time `t` and at the root at time `t`. -/
def visits (S : Vertex d → ℕ → Vertex d) : Set (Vertex d × ℕ) :=
  {p | 1 ≤ p.2 ∧ ∃ s, wake S p.2 p.1 = some s ∧ S p.1 (p.2 - s) = root}


/-! ## Sanity lemmas -/

section Sanity

/-! ### The tree -/

/-- Every vertex has `d` children. -/
theorem ncard_children (v : Vertex d) : {w : Vertex d | ∃ c : Fin d, w = c :: v}.ncard = d := by
  have : {w : Vertex d | ∃ c : Fin d, w = c :: v} = Set.range (· :: v) := by
    ext w; simp [eq_comm]
  rw [this, Set.ncard_range_of_injective (fun a b h => List.head_eq_of_cons_eq h)]
  simp

/-- The root has `d` neighbours. -/
theorem ncard_adj_root {d : ℕ} : {w : Vertex d | (tree d).Adj root w}.ncard = d := by
  have h : {w : Vertex d | (tree d).Adj root w} = {w : Vertex d | ∃ c : Fin d, w = c :: root} := by
    ext w; simp [tree, root]
  rw [h]
  exact ncard_children root

/-- Every vertex other than the root has `d + 1` neighbours. -/
theorem ncard_adj_cons {d : ℕ} (c : Fin d) (v : Vertex d) :
    {w : Vertex d | (tree d).Adj (c :: v) w}.ncard = d + 1 := by
  have h_set_eq : {w : Vertex d | (tree d).Adj (c :: v) w} =
      {v} ∪ {w | ∃ c' : Fin d, w = c' :: c :: v} := by
    ext w
    constructor
    · intro h
      rcases h with (⟨c', h⟩ | ⟨c', h⟩)
      · exact Or.inr ⟨c', h⟩
      · have hw : w = v := by
          injection h with hc hv
          subst hc hv
          rfl
        exact Or.inl hw
    · intro h
      rcases h with (hw | ⟨c', hw⟩)
      · subst hw
        exact Or.inr ⟨c, rfl⟩
      · subst hw
        exact Or.inl ⟨c', rfl⟩
  rw [h_set_eq]
  have h_disjoint : Disjoint ({v} : Set (Vertex d)) {w | ∃ c' : Fin d, w = c' :: c :: v} := by
    refine Set.disjoint_singleton_left.mpr ?_
    intro h
    rcases h with ⟨c', h⟩
    have h_len := congrArg List.length h
    simp at h_len
    omega
  have h_finite_singleton : ({v} : Set (Vertex d)).Finite := by
    exact Set.finite_singleton _
  have h_finite_children : ({w | ∃ c' : Fin d, w = c' :: c :: v} : Set (Vertex d)).Finite := by
    have : {w | ∃ c' : Fin d, w = c' :: c :: v} = Set.range (· :: c :: v) := by
      ext w; simp [eq_comm]
    rw [this]
    exact Set.finite_range _
  have h_ncard_union := Set.ncard_union_add_ncard_inter _ _ h_finite_singleton h_finite_children
  have h_inter_empty : ({v} : Set (Vertex d)) ∩ {w | ∃ c' : Fin d, w = c' :: c :: v} = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp h_disjoint
  rw [h_inter_empty, Set.ncard_empty] at h_ncard_union
  have h_singleton_ncard : ({v} : Set (Vertex d)).ncard = 1 := Set.ncard_singleton _
  have h_children_ncard : {w | ∃ c' : Fin d, w = c' :: c :: v}.ncard = d := by
    simpa using ncard_children (c :: v)
  rw [h_singleton_ncard, h_children_ncard] at h_ncard_union
  -- h_ncard_union : (s ∪ t).ncard + 0 = 1 + d
  -- We need (s ∪ t).ncard = d + 1
  have h_result : ({v} ∪ {w | ∃ c' : Fin d, w = c' :: c :: v}).ncard = 1 + d := by
    omega
  rw [h_result, add_comm]

/-! ### The walk and its law -/

/-- A step of the walk goes to a neighbour. -/
theorem tree_adj_step (v : Vertex d) (ξ : Step d) : (tree d).Adj v (step v ξ) := by
  cases v with
  | nil => exact Or.inl ⟨ξ.1, rfl⟩
  | cons c w =>
    simp only [step]
    split_ifs with h
    · exact Or.inr ⟨c, rfl⟩
    · exact Or.inl ⟨_, rfl⟩

/-- Every frog's path starts at its vertex. -/
theorem paths_zero (ω : Sample d) (u : Vertex d) : paths ω u 0 = u := rfl

/-- Every frog's path moves along edges of the tree. -/
theorem tree_adj_paths (ω : Sample d) (u : Vertex d) (n : ℕ) :
    (tree d).Adj (paths ω u n) (paths ω u (n + 1)) :=
  tree_adj_step _ _

/-- The root frog's first step goes to a child of the root. -/
theorem paths_root_one (ω : Sample d) : ∃ c : Fin d, paths ω root 1 = [c] :=
  ⟨(ω root 0).1, rfl⟩

open Finset in
/-- The neighbours of `v`, as a finset. -/
def nbrs : Vertex d → Finset (Vertex d)
  | [] => univ.image fun c => [c]
  | c :: w => insert w (univ.image fun c' => c' :: c :: w)

/-- `nbrs v` is the neighbourhood of `v` in the tree. -/
theorem coe_nbrs (v : Vertex d) : (nbrs v : Set (Vertex d)) = {w | (tree d).Adj v w} := by
  cases v with
  | nil =>
    ext w
    simp [nbrs, tree, eq_comm]
  | cons c w0 =>
    ext w
    simp [nbrs, tree, eq_comm, or_comm]

/-- The number of steps leading from `v` to each of its neighbours. -/
def mult : Vertex d → ℕ
  | [] => d + 1
  | _ :: _ => d

/-- The steps from `v` to `w`: `mult v` of them for a neighbour `w`, none otherwise. -/
theorem card_fiber (v w : Vertex d) :
    (Finset.univ.filter fun ξ : Step d => step v ξ = w).card =
      if w ∈ nbrs v then mult v else 0 := by
  cases v with
  | nil =>
    by_cases hw : ∃ c, w = [c]
    · obtain ⟨c, rfl⟩ := hw
      have : (Finset.univ.filter fun ξ : Step d => step [] ξ = [c]) = {c} ×ˢ Finset.univ := by
        ext ξ
        rw [Finset.mem_filter, Finset.mem_product]
        simp [step]
      rw [this, Finset.card_product]
      simp [nbrs, mult]
    · have hn : w ∉ nbrs [] := by
        simp only [nbrs, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
        exact fun c h => hw ⟨c, h.symm⟩
      simp only [hn, ↓reduceIte, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ξ _ h
      exact hw ⟨ξ.1, h.symm⟩
  | cons c w0 =>
    by_cases h0 : w = w0
    · subst h0
      have : (Finset.univ.filter fun ξ : Step d => step (c :: w) ξ = w) =
          Finset.univ ×ˢ {0} := by
        ext ξ
        rw [Finset.mem_filter, Finset.mem_product]
        simp only [step, Finset.mem_univ, true_and, Finset.mem_singleton]
        by_cases h : ξ.2 = 0
        · simp [h]
        · simp only [h, dite_false, iff_false]
          intro hc
          have := congrArg List.length hc
          simp only [List.length_cons] at this
          omega
      rw [this, Finset.card_product]
      simp [nbrs, mult]
    · by_cases hc : ∃ c', w = c' :: c :: w0
      · obtain ⟨c', rfl⟩ := hc
        have : (Finset.univ.filter fun ξ : Step d => step (c :: w0) ξ = c' :: c :: w0) =
            Finset.univ ×ˢ {c'.succ} := by
          ext ξ
          rw [Finset.mem_filter, Finset.mem_product]
          simp only [step, Finset.mem_univ, true_and, Finset.mem_singleton]
          by_cases h : ξ.2 = 0
          · simp only [h, dite_true]
            constructor
            · intro hc
              have := congrArg List.length hc
              simp only [List.length_cons] at this
              omega
            · intro hc
              exact absurd hc.symm (Fin.succ_ne_zero c')
          · simp only [h, dite_false]
            constructor
            · intro hc
              obtain ⟨h1, -⟩ := List.cons_eq_cons.1 hc
              rw [← h1]
              simp
            · intro hc
              simp [hc]
        rw [this, Finset.card_product]
        simp [nbrs, mult]
      · have hn : w ∉ nbrs (c :: w0) := by
          simp only [nbrs, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
            not_or, not_exists]
          exact ⟨h0, fun c' h => hc ⟨c', h.symm⟩⟩
        simp only [hn, ↓reduceIte, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro ξ _ h
        simp only [step] at h
        split_ifs at h with h'
        · exact h0 h.symm
        · exact hc ⟨_, h.symm⟩

/-- The root has `d` neighbours. -/
theorem card_nbrs_nil : (nbrs ([] : Vertex d)).card = d := by
  rw [nbrs, Finset.card_image_of_injective _ (fun a b h => List.head_eq_of_cons_eq h)]
  simp

/-- A vertex other than the root has `d + 1` neighbours. -/
theorem card_nbrs_cons (c : Fin d) (w : Vertex d) : (nbrs (c :: w)).card = d + 1 := by
  rw [nbrs, Finset.card_insert_of_notMem, Finset.card_image_of_injective _
    (fun a b h => List.head_eq_of_cons_eq h)]
  · simp
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro c' h
    have := congrArg List.length h
    simp only [List.length_cons] at this
    omega

/-- The steps from `v` are spread evenly over its neighbours. -/
theorem card_nbrs_mul_mult (v : Vertex d) : (nbrs v).card * mult v = d * (d + 1) := by
  cases v with
  | nil => simp [card_nbrs_nil, mult]
  | cons c w0 => simp [card_nbrs_cons, mult, mul_comm]

open scoped ENNReal in
/-- The step kernel: from `v`, the walk moves to a uniform neighbour of `v`. -/
theorem map_step_eq_uniformOn [NeZero d] (v : Vertex d) :
    (stepLaw d).map (step v) = uniformOn {w : Vertex d | (tree d).Adj v w} := by
  classical
  rw [← coe_nbrs]
  refine Measure.ext_of_singleton fun w => ?_
  have hR : uniformOn (nbrs v : Set (Vertex d)) {w} = (nbrs v ∩ {w}).card / (nbrs v).card := by
    rw [← Finset.coe_singleton, uniformOn_apply_finset]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton w), stepLaw,
    uniformOn_univ, hR]
  have hpre : step v ⁻¹' {w} = ↑(Finset.univ.filter fun ξ : Step d => step v ξ = w) := by
    ext ξ
    simp
  rw [hpre, Measure.count_apply_finset, card_fiber]
  by_cases hw : w ∈ nbrs v
  · have hcard : Fintype.card (Step d) = (nbrs v).card * mult v := by
      rw [card_nbrs_mul_mult]
      simp [Step]
    have hm : (mult v : ℝ≥0∞) ≠ 0 := by
      cases v <;> simp [mult, NeZero.ne]
    simp only [hw, ↓reduceIte]
    rw [Finset.inter_singleton_of_mem hw, Finset.card_singleton, hcard, Nat.cast_mul]
    simpa using ENNReal.mul_div_mul_right 1 ((nbrs v).card : ℝ≥0∞) hm (ENNReal.natCast_ne_top _)
  · simp [hw]

open scoped ENNReal in
/-- One step from `v` reaches a given neighbour of `v` with probability one over the number of
neighbours of `v`, and a non-neighbour with probability zero. -/
theorem stepLaw_preimage [NeZero d] (v w : Vertex d) :
    stepLaw d (step v ⁻¹' {w}) = if w ∈ nbrs v then ((nbrs v).card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [← Measure.map_apply (measurable_of_countable _) (measurableSet_singleton w),
    map_step_eq_uniformOn, ← coe_nbrs, ← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases hw : w ∈ nbrs v
  · simp [hw, Finset.inter_singleton_of_mem hw]
  · simp [hw]

/-- The step probabilities at `d = 4`: `1 / 4` from the root to each child, `1 / 5` elsewhere to
the parent and to each child. -/
theorem stepLaw_four (c c' : Fin 4) (v : Vertex 4) :
    stepLaw 4 (step root ⁻¹' {[c]}) = 1 / 4 ∧
      stepLaw 4 (step (c :: v) ⁻¹' {v}) = 1 / 5 ∧
      stepLaw 4 (step (c :: v) ⁻¹' {c' :: c :: v}) = 1 / 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [stepLaw_preimage]
  · simp only [root]
    rw [card_nbrs_nil]
    simp [nbrs]
  · rw [card_nbrs_cons]
    simp [nbrs]
  · rw [card_nbrs_cons]
    simp [nbrs]

/-- The walk is a measurable function of its step sequence. -/
theorem measurable_walk {d : ℕ} (u : Vertex d) :
    Measurable (walk u : (ℕ → Step d) → ℕ → Vertex d) := by
  rw [measurable_pi_iff]
  intro n
  induction' n with n ih
  · simp [walk]
  · have h_step_meas : Measurable (fun (p : Vertex d × Step d) => step p.1 p.2) := by
      apply measurable_of_countable
    have h_pair : Measurable (fun (x : ℕ → Step d) => (walk u x n, x n)) := by
      apply Measurable.prodMk ih
      exact measurable_pi_apply n
    have : (fun (x : ℕ → Step d) => walk u x (n + 1)) =
        (fun (p : Vertex d × Step d) => step p.1 p.2) ∘ (fun (x : ℕ → Step d) => (walk u x n, x n)) := by
      ext x; simp [walk]
    rw [this]
    exact h_step_meas.comp h_pair

/-- The step variables are independent ... -/
theorem iIndepFun_steps {d : ℕ} [NeZero d] :
    iIndepFun (fun (p : Vertex d × ℕ) (ω : Sample d) => ω p.1 p.2) (frogMeasure d) := by
  unfold frogMeasure
  refine ProbabilityTheory.iIndepFun_uncurry_infinitePi'
    (μ := fun (_ : Vertex d) (_ : ℕ) => stepLaw d)
    (X := fun (_ : Vertex d) (_ : ℕ) => id)
    (mX := fun (_ : Vertex d) (_ : ℕ) => ?_)
  exact measurable_id

/-- ... and each has law `stepLaw d`. -/
theorem map_eval_frogMeasure {d : ℕ} [NeZero d] (u : Vertex d) (n : ℕ) :
    (frogMeasure d).map (fun ω => ω u n) = stepLaw d := by
  unfold frogMeasure
  have hcomp : (fun (ω : Sample d) => ω u n) = (fun (x : ℕ → Step d) => x n) ∘ (fun (ω : Sample d) => ω u) := by
    funext ω; rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_eval (fun (_ : Vertex d) => Measure.infinitePi (fun (_ : ℕ) => stepLaw d)) u,
    Measure.infinitePi_map_eval (fun (_ : ℕ) => stepLaw d) n]

/-- The paths of the frogs are independent. -/
theorem iIndepFun_paths {d : ℕ} [NeZero d] :
    iIndepFun (fun (u : Vertex d) (ω : Sample d) => paths ω u) (frogMeasure d) := by
  have h_meas : ∀ (u : Vertex d), Measurable (walk u) := by
    intro u
    refine measurable_pi_iff.mpr fun n => ?_
    induction' n with n ih
    · simp [walk]
    · have h_eq : (fun (x : ℕ → Step d) => walk u x (n + 1)) =
                 (fun (x : ℕ → Step d) => step (walk u x n) (x n)) := by
        ext x; simp [walk]
      rw [h_eq]
      have h_step_meas : Measurable (fun (p : Vertex d × Step d) => step p.1 p.2) :=
        Measurable.of_discrete
      refine h_step_meas.comp (Measurable.prodMk ih (measurable_pi_apply n))
  have h_indep := ProbabilityTheory.iIndepFun_infinitePi
    (P := fun (_ : Vertex d) => Measure.infinitePi fun (_ : ℕ) => stepLaw d) h_meas
  simpa [frogMeasure, paths] using h_indep

/-- The finite-dimensional laws of a path: the path of frog `u` follows `v` up to time `n` with
probability the product of the one-step probabilities (`0` unless `v` starts at `u`). -/
theorem frogMeasure_paths_eq [NeZero d] (u : Vertex d) (v : ℕ → Vertex d) (n : ℕ) :
    frogMeasure d {ω | ∀ i ≤ n, paths ω u i = v i} =
      if v 0 = u then
        ∏ i ∈ Finset.range n, uniformOn {w : Vertex d | (tree d).Adj (v i) w} {v (i + 1)}
      else 0 := by
  by_cases h0 : v 0 = u
  · simp only [h0, ↓reduceIte]
    have h_set_eq : {ω : Sample d | ∀ i ≤ n, paths ω u i = v i} =
        (fun ω : Sample d => ω u) ⁻¹'
          Set.pi (Finset.range n) (fun i => step (v i) ⁻¹' {v (i + 1)}) := by
      ext ω
      constructor
      · intro h i hi
        have hi_lt_n : i < n := Finset.mem_range.1 hi
        have hpath := h i (by omega)
        have hpath_next := h (i + 1) (by omega)
        simp only [paths, walk] at hpath hpath_next
        rw [hpath] at hpath_next
        simpa using hpath_next
      · intro h i hi
        induction i with
        | zero => simp [paths, walk, h0]
        | succ k ih =>
          have hstep := h k (Finset.mem_range.2 (by omega))
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hstep
          have hpath_k : paths ω u k = v k := ih (by omega)
          dsimp only [paths] at hpath_k
          dsimp only [paths, walk]
          rw [hpath_k, hstep]
    have hmeas (i : ℕ) : MeasurableSet (step (v i) ⁻¹' {v (i + 1)}) :=
      (measurable_of_countable (step (v i))) (measurableSet_singleton _)
    rw [h_set_eq, ← Measure.map_apply (measurable_pi_apply u)
      (MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => hmeas i))]
    have h_pushforward : (frogMeasure d).map (fun ω : Sample d => ω u) =
        Measure.infinitePi (fun _ : ℕ => stepLaw d) := by
      have := Measure.infinitePi_map_eval (ι := Vertex d) (X := fun _ => ℕ → Step d)
        (μ := fun (_ : Vertex d) => Measure.infinitePi (fun _ : ℕ => stepLaw d)) u
      simpa [frogMeasure] using this
    rw [h_pushforward, Measure.infinitePi_pi (μ := fun _ : ℕ => stepLaw d)
      (mt := fun i _ => hmeas i)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
      map_step_eq_uniformOn]
  · simp only [h0, ↓reduceIte]
    have hempty : {ω : Sample d | ∀ i ≤ n, paths ω u i = v i} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨0, Nat.zero_le _, by simpa [paths, walk] using Ne.symm h0⟩
    simp [hempty]

/-! ### Wake times -/

/-- At time `0` only the root frog is active. -/
theorem wake_zero (S : Vertex d → ℕ → Vertex d) (u : Vertex d) :
    wake S 0 u = if u = root then some 0 else none := by
  simp [wake]

/-- The root frog is active from time `0` on, with wake time `0`. -/
theorem wake_root {d : ℕ} (S : Vertex d → ℕ → Vertex d) (t : ℕ) :
    wake S t root = some 0 := by
  induction' t with t ih
  · rfl
  · rw [wake, ih]

/-- A wake time is at most the current time, so `t - s` in `wake` and `visits` is a true
difference. -/
theorem wake_le {S : Vertex d → ℕ → Vertex d} {t : ℕ} {u : Vertex d} {s : ℕ}
    (h : wake S t u = some s) : s ≤ t := by
  induction' t with t ih generalizing u s
  · unfold wake at h
    by_cases hu : u = root
    · simp [hu] at h
      omega
    · simp [hu] at h
  · unfold wake at h
    cases h' : wake S t u with
    | none =>
      rw [h'] at h
      by_cases hcond : ∃ w s, wake S t w = some s ∧ S w (t + 1 - s) = u
      · simp [hcond] at h
        omega
      · simp [hcond] at h
    | some s' =>
      rw [h'] at h
      injection h with hs
      subst hs
      exact (ih h').trans (Nat.le_succ t)

/-- An active frog stays active, with the same wake time. -/
theorem wake_mono {d : ℕ} {S : Vertex d → ℕ → Vertex d} {t t' : ℕ} {u : Vertex d}
    {s : ℕ} (h : wake S t u = some s) (htt' : t ≤ t') : wake S t' u = some s := by
  induction t' with
  | zero =>
      have ht0 : t = 0 := Nat.eq_zero_of_le_zero htt'
      subst ht0
      exact h
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le htt' with (rfl | hlt)
      · exact h
      · have htk : t ≤ k := Nat.le_of_lt_succ hlt
        have hk : wake S k u = some s := ih htk
        unfold wake
        simp [hk]

/-- The wake time of a frog is the first time it is active. -/
theorem wake_self {S : Vertex d → ℕ → Vertex d} {t : ℕ} {u : Vertex d} {s : ℕ}
    (h : wake S t u = some s) : wake S s u = some s := by
  induction' t with k IH generalizing u s
  · unfold wake at h
    by_cases hu : u = root
    · simp [hu] at h
      subst h
      unfold wake
      simp [hu]
    · simp [hu] at h
  · have h_cases := h
    unfold wake at h_cases
    cases h_wake_k : wake S k u with
    | some s' =>
        rw [h_wake_k] at h_cases
        injection h_cases with h_eq
        subst h_eq
        exact IH h_wake_k
    | none =>
        rw [h_wake_k] at h_cases
        by_cases h_cond : ∃ w s, wake S k w = some s ∧ S w (k + 1 - s) = u
        · simp [h_cond] at h_cases
          subst h_cases
          exact h
        · simp [h_cond] at h_cases

/-- Finitely many frogs are active at each time. -/
theorem finite_active {d : ℕ} (S : Vertex d → ℕ → Vertex d) (t : ℕ) :
    {u : Vertex d | wake S t u ≠ none}.Finite := by
  induction' t with t ih
  · -- t = 0: only the root is active
    have h_eq : {u : Vertex d | wake S 0 u ≠ none} = {root} := by
      ext u; simp [wake]
    rw [h_eq]
    exact Set.finite_singleton _
  · -- t + 1: active frogs are either still active from time t, or newly woken
    set A := {u : Vertex d | wake S t u ≠ none} with hA
    have hA_fin : A.Finite := ih
    have h_wake_succ_iff (u : Vertex d) : wake S (t + 1) u ≠ none ↔
        (wake S t u ≠ none) ∨ (∃ w s, wake S t w = some s ∧ S w (t + 1 - s) = u) := by
      simp [wake]
      by_cases h : wake S t u = none
      · rw [h]
        simp
      · rcases Option.ne_none_iff_exists'.mp h with ⟨s, hs⟩
        rw [hs]
        simp
    have h_sub : {u : Vertex d | wake S (t + 1) u ≠ none} ⊆
        A ∪ (⋃ w ∈ A, {u | ∃ s, wake S t w = some s ∧ S w (t + 1 - s) = u}) := by
      intro u hu
      rw [Set.mem_ofPred_eq] at hu
      rw [h_wake_succ_iff u] at hu
      rcases hu with (hu_A | ⟨w, s, hw, hu_eq⟩)
      · -- u ∈ A: still active from time t
        refine Or.inl ?_
        rw [hA]
        exact hu_A
      · -- u = S w (t + 1 - s) for some w with wake S t w = some s
        have hw_mem_A : w ∈ A := by
          rw [hA]
          simp [hw]
        refine Or.inr ?_
        refine Set.mem_biUnion hw_mem_A ?_
        exact ⟨s, hw, hu_eq⟩
    have h_union_fin : (A ∪ (⋃ w ∈ A, {u | ∃ s, wake S t w = some s ∧ S w (t + 1 - s) = u})).Finite := by
      apply Set.Finite.union hA_fin
      refine hA_fin.biUnion ?_
      intro w hw
      have hw_ne_none : wake S t w ≠ none := by
        rw [hA] at hw
        exact hw
      rcases Option.ne_none_iff_exists'.mp hw_ne_none with ⟨s, hs⟩
      have h_singleton : {u | ∃ s', wake S t w = some s' ∧ S w (t + 1 - s') = u} = {S w (t + 1 - s)} := by
        ext u
        constructor
        · rintro ⟨s', hs', hu_eq⟩
          have h_eq : some s = some s' := by rw [← hs, hs']
          have hss' : s = s' := Option.some.inj h_eq
          subst hss'
          rw [Set.mem_singleton_iff, hu_eq]
        · intro hu_mem
          rw [Set.mem_singleton_iff] at hu_mem
          subst hu_mem
          exact ⟨s, hs, rfl⟩
      rw [h_singleton]
      exact Set.finite_singleton _
    exact h_union_fin.subset h_sub

/-- Finitely many visits as (frog, time) pairs iff finitely many times with a frog at the root. -/
theorem visits_finite_iff_times {d : ℕ} (S : Vertex d → ℕ → Vertex d) :
    (visits S).Finite ↔ {t : ℕ | ∃ u, (u, t) ∈ visits S}.Finite := by
  constructor
  · intro h
    have h_image : {t : ℕ | ∃ u, (u, t) ∈ visits S} = Prod.snd '' (visits S) := by
      ext t; simp
    rw [h_image]
    exact Set.Finite.image Prod.snd h
  · intro h
    let T := {t : ℕ | ∃ u, (u, t) ∈ visits S}
    have hT : T.Finite := h
    have h_cover : visits S ⊆ ⋃ t ∈ T, {u | wake S t u ≠ none} ×ˢ {t} := by
      intro p hp
      rcases p with ⟨u, t⟩
      have hp_saved := hp
      rcases hp with ⟨h_one, s, hw, hS⟩
      have hw_ne_none : wake S t u ≠ none := by
        rw [hw]
        exact Option.some_ne_none s
      have ht : t ∈ T := by
        dsimp [T]
        exact ⟨u, hp_saved⟩
      refine Set.mem_biUnion ht ?_
      simp [hw_ne_none]
    have h_union_fin : (⋃ t ∈ T, {u | wake S t u ≠ none} ×ˢ {t}).Finite := by
      refine Set.Finite.biUnion hT ?_
      intro t ht
      have h_active_fin : {u : Vertex d | wake S t u ≠ none}.Finite := finite_active S t
      have h_singleton_fin : ({t} : Set ℕ).Finite := by simp
      exact Set.Finite.prod h_active_fin h_singleton_fin
    exact Set.Finite.subset h_union_fin h_cover

/-! ### Order independence: the woken frogs are the frogs reachable from the root frog -/

/-- The frogs reachable from the root frog: the least set containing the root and closed under
the ranges of the paths. -/
inductive Reach (S : Vertex d → ℕ → Vertex d) : Vertex d → Prop
  | root : Reach S root
  | path {u : Vertex d} (n : ℕ) : Reach S u → Reach S (S u n)

/-- A frog is ever woken iff it is reachable from the root frog: the woken set does not depend
on the order or the timing of the moves. -/
theorem woken_iff_reach (S : Vertex d → ℕ → Vertex d) (hS : ∀ u, S u 0 = u)
    (u : Vertex d) : (∃ t s, wake S t u = some s) ↔ Reach S u := by
  constructor
  · -- forward direction: (∃ t s, wake S t u = some s) → Reach S u
    rintro ⟨t, s, h⟩
    induction' t with k IH generalizing u s
    · -- t = 0
      unfold wake at h
      by_cases hu : u = root
      · simp [hu] at h
        subst h
        subst hu
        exact Reach.root
      · simp [hu] at h
    · -- t = k + 1
      have h_cases := h
      unfold wake at h_cases
      cases h_wake_k : wake S k u with
      | some s' =>
          rw [h_wake_k] at h_cases
          injection h_cases with h_eq
          subst h_eq
          exact IH u s' h_wake_k
      | none =>
          rw [h_wake_k] at h_cases
          by_cases h_cond : ∃ w s, wake S k w = some s ∧ S w (k + 1 - s) = u
          · simp [h_cond] at h_cases
            subst h_cases
            rcases h_cond with ⟨w, s', ⟨h_wake_w, h_eq_u⟩⟩
            have h_reach_w : Reach S w := IH w s' h_wake_w
            rw [← h_eq_u]
            exact Reach.path (k + 1 - s') h_reach_w
          · simp [h_cond] at h_cases
  · -- backward direction: Reach S u → (∃ t s, wake S t u = some s)
    intro h_reach
    induction' h_reach with u n h_reach_u IH
    · -- Reach.root
      refine ⟨0, 0, ?_⟩
      unfold wake
      simp [root]
    · -- Reach.path n h_reach_u
      rcases IH with ⟨t, s, h_wake⟩
      have h_wake_self : wake S s u = some s := wake_self h_wake
      by_cases hn : n = 0
      · subst hn
        rw [hS u]
        exact ⟨t, s, h_wake⟩
      · rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, hm⟩
        subst hm
        have h_wake_sm : wake S (s + m) u = some s :=
          wake_mono h_wake_self (Nat.le_add_right s m)
        have h_exists : ∃ s', wake S ((s + m) + 1) (S u (m + 1)) = some s' := by
          unfold wake
          cases h_wake_sm' : wake S (s + m) (S u (m + 1)) with
          | some s' => exact ⟨s', rfl⟩
          | none =>
              refine ⟨(s + m) + 1, ?_⟩
              have h_cond : ∃ w s', wake S (s + m) w = some s' ∧ S w ((s + m) + 1 - s') = S u (m + 1) := by
                refine ⟨u, s, h_wake_sm, ?_⟩
                have h_sub : (s + m) + 1 - s = m + 1 := by
                  rw [add_assoc, Nat.add_sub_cancel_left]
                rw [h_sub]
              simp [h_cond]
        rcases h_exists with ⟨s', h_target⟩
        exact ⟨(s + m) + 1, s', h_target⟩

/-- A frog has a single wake time. -/
theorem wake_unique {S : Vertex d → ℕ → Vertex d} {t t' : ℕ} {u : Vertex d} {s s' : ℕ}
    (h : wake S t u = some s) (h' : wake S t' u = some s') : s = s' := by
  rcases le_total t t' with htt' | htt'
  · rw [wake_mono h htt'] at h'
    exact Option.some_injective _ h'
  · rw [wake_mono h' htt'] at h
    exact (Option.some_injective _ h).symm

/-- The number of visits to the root does not depend on the order of the moves: it counts the
pairs (frog reachable from the root frog, time `n ≥ 1` of its own path at the root). -/
theorem encard_visits (S : Vertex d → ℕ → Vertex d) (hS : ∀ u, S u 0 = u) :
    (visits S).encard =
      {p : Vertex d × ℕ | Reach S p.1 ∧ 1 ≤ p.2 ∧ S p.1 p.2 = root}.encard := by
  set F : Vertex d × ℕ → Vertex d × ℕ := fun p => (p.1, p.2 - (wake S p.2 p.1).getD 0)
  have hinj : Set.InjOn F (visits S) := by
    rintro ⟨u, t⟩ ⟨-, s, hs, -⟩ ⟨u', t'⟩ ⟨-, s', hs', -⟩ hF
    simp only [F, Prod.mk.injEq, hs, hs', Option.getD_some] at hF
    obtain ⟨rfl, ht⟩ := hF
    have := wake_unique hs hs'
    subst this
    have := wake_le hs
    have := wake_le hs'
    simp only [Prod.mk.injEq, true_and]
    omega
  rw [← hinj.encard_image]
  congr 1
  ext ⟨u, n⟩
  simp only [Set.mem_image, Prod.exists]
  constructor
  · rintro ⟨u', t, ⟨ht, s, hs, hroot⟩, hF⟩
    simp only [F, hs, Option.getD_some, Prod.mk.injEq] at hF
    obtain ⟨rfl, rfl⟩ := hF
    refine ⟨(woken_iff_reach S hS u').1 ⟨t, s, hs⟩, ?_, hroot⟩
    by_contra h0
    have h0 : t - s = 0 := by omega
    rw [h0, hS] at hroot
    subst hroot
    rw [wake_root] at hs
    cases hs
    omega
  · rintro ⟨hu, hn, hroot⟩
    obtain ⟨t, s, hs⟩ := (woken_iff_reach S hS u).2 hu
    have hs' : wake S (n + s) u = some s := wake_mono (wake_self hs) (by omega)
    refine ⟨u, n + s, ⟨by omega, s, hs', by simpa using hroot⟩, ?_⟩
    simp [F, hs']

/-! ### The event of the target -/

/-- For each u, n, the function ω ↦ paths ω u n is measurable. -/
lemma measurable_paths (u : Vertex d) (n : ℕ) : Measurable fun (ω : Sample d) => paths ω u n := by
  induction' n with n ih
  · -- n = 0: paths ω u 0 = u (constant)
    simp [paths, walk, measurable_const]
  · -- n+1: paths ω u (n+1) = step (paths ω u n) (ω u n)
    have h_step : Measurable (fun (p : Vertex d × Step d) => step p.1 p.2) :=
      measurable_of_countable _
    have h_eval_n : Measurable fun (ω : Sample d) => (ω u) n :=
      (measurable_pi_apply n).comp (measurable_pi_apply u)
    -- combine: ω ↦ (paths ω u n, ω u n) is measurable
    have h_pair : Measurable fun (ω : Sample d) => (paths ω u n, (ω u) n) :=
      Measurable.prodMk ih h_eval_n
    -- compose with step
    have h_eq : (fun (ω : Sample d) => paths ω u (n + 1)) =
        (fun (p : Vertex d × Step d) => step p.1 p.2) ∘ (fun ω => (paths ω u n, (ω u) n)) := by
      ext ω; simp [paths, walk]
    rw [h_eq]
    exact h_step.comp h_pair

/-- For each u, n, v, the set {ω | paths ω u n = v} is measurable. -/
lemma measurableSet_paths_eq (u : Vertex d) (n : ℕ) (v : Vertex d) :
    MeasurableSet {ω : Sample d | paths ω u n = v} := by
  have h_meas : Measurable fun (ω : Sample d) => paths ω u n := measurable_paths u n
  -- {ω | paths ω u n = v} = (fun ω => paths ω u n)⁻¹' {v}
  -- and {v} is measurable in the discrete σ-algebra
  have h_singleton : MeasurableSet ({v} : Set (Vertex d)) := by
    -- discrete measurable space: all sets are measurable
    apply MeasurableSet.of_discrete
  exact h_singleton.preimage h_meas

/-- For each t, u, s, the set {ω | wake (paths ω) t u = some s} is measurable. -/
lemma measurableSet_wake_eq_some (t : ℕ) (u : Vertex d) (s : ℕ) :
    MeasurableSet {ω : Sample d | wake (paths ω) t u = some s} := by
  induction' t with t ih generalizing u s
  · -- t = 0
    simp [wake]
  · -- t+1
    have h_eq_set : {ω : Sample d | wake (paths ω) (t + 1) u = some s} =
        {ω | wake (paths ω) t u = some s} ∪
        ({ω | wake (paths ω) t u = none} ∩ {ω | s = t + 1} ∩
          {ω | ∃ (w : Vertex d) (s' : ℕ), wake (paths ω) t w = some s' ∧ paths ω w (t + 1 - s') = u}) := by
      ext ω
      simp [wake]
      cases h : wake (paths ω) t u
      · simp [and_comm, eq_comm]
      · rename_i val; simp
    rw [h_eq_set]
    have h1 : MeasurableSet {ω | wake (paths ω) t u = some s} := ih u s
    have h_none : MeasurableSet {ω | wake (paths ω) t u = none} := by
      have h_union : {ω | wake (paths ω) t u = none} =
          (⋃ (s' : ℕ), {ω | wake (paths ω) t u = some s'})ᶜ := by
        ext ω
        cases h : wake (paths ω) t u
        · simp [h]
        · rename_i val; simp [h]
      rw [h_union]
      refine MeasurableSet.compl ?_
      refine MeasurableSet.iUnion ?_
      intro s'
      exact ih u s'
    have h_s_eq : MeasurableSet {ω : Sample d | s = t + 1} := by
      by_cases hst : s = t + 1
      · subst hst; simp
      · simp [hst]
    have h_exists : MeasurableSet {ω : Sample d |
        ∃ (w : Vertex d) (s' : ℕ), wake (paths ω) t w = some s' ∧ paths ω w (t + 1 - s') = u} := by
      -- This is a countable union over w and s' of intersections
      have h_union : {ω : Sample d |
          ∃ (w : Vertex d) (s' : ℕ), wake (paths ω) t w = some s' ∧ paths ω w (t + 1 - s') = u} =
          ⋃ (w : Vertex d), ⋃ (s' : ℕ),
            ({ω | wake (paths ω) t w = some s'} ∩ {ω | paths ω w (t + 1 - s') = u}) := by
        ext ω; simp
      rw [h_union]
      refine MeasurableSet.iUnion fun w => ?_
      refine MeasurableSet.iUnion fun s' => ?_
      have h_wake : MeasurableSet {ω | wake (paths ω) t w = some s'} := ih w s'
      have h_paths : MeasurableSet {ω | paths ω w (t + 1 - s') = u} :=
        measurableSet_paths_eq w (t + 1 - s') u
      exact MeasurableSet.inter h_wake h_paths
    -- Now combine: h1 ∪ (h_none ∩ h_s_eq ∩ h_exists)
    have h_inter : MeasurableSet ({ω | wake (paths ω) t u = none} ∩ {ω | s = t + 1} ∩
        {ω | ∃ (w : Vertex d) (s' : ℕ), wake (paths ω) t w = some s' ∧ paths ω w (t + 1 - s') = u}) :=
      MeasurableSet.inter (MeasurableSet.inter h_none h_s_eq) h_exists
    exact MeasurableSet.union h1 h_inter

/-- For each u, t, the set {ω | (u, t) ∈ visits (paths ω)} is measurable. -/
lemma measurableSet_visits (u : Vertex d) (t : ℕ) :
    MeasurableSet {ω : Sample d | (u, t) ∈ visits (paths ω)} := by
  simp [visits]
  by_cases ht : 1 ≤ t
  · -- goal: MeasurableSet {ω | 1 ≤ t ∧ ∃ s, wake (paths ω) t u = some s ∧ paths ω u (t - s) = root}
    -- which is equivalent to Measurable fun ω => 1 ≤ t ∧ ∃ s, ...
    -- Since 1 ≤ t is constant, we can drop it
    have h_meas : MeasurableSet {ω : Sample d | ∃ s : ℕ, wake (paths ω) t u = some s ∧ paths ω u (t - s) = root} := by
      have h_exists : {ω : Sample d | ∃ s : ℕ, wake (paths ω) t u = some s ∧ paths ω u (t - s) = root} =
          ⋃ (s : ℕ), ({ω | wake (paths ω) t u = some s} ∩ {ω | paths ω u (t - s) = root}) := by
        ext ω; simp
      rw [h_exists]
      refine MeasurableSet.iUnion fun s => ?_
      have h_wake : MeasurableSet {ω | wake (paths ω) t u = some s} :=
        measurableSet_wake_eq_some t u s
      have h_paths : MeasurableSet {ω | paths ω u (t - s) = root} :=
        measurableSet_paths_eq u (t - s) root
      exact MeasurableSet.inter h_wake h_paths
    -- Now we need to relate this to the goal which has the extra 1 ≤ t condition
    -- Since ht : 1 ≤ t, the two sets are equal
    have h_fun_eq : (fun (ω : Sample d) => 1 ≤ t ∧ ∃ s : ℕ, wake (paths ω) t u = some s ∧ paths ω u (t - s) = root) =
        (fun (ω : Sample d) => ∃ s : ℕ, wake (paths ω) t u = some s ∧ paths ω u (t - s) = root) := by
      ext ω; simp [ht]
    rw [h_fun_eq]
    simpa using h_meas
  · -- t < 1, so the set is empty
    simp [ht]

/-- The event of the target is measurable, so "almost surely" means "with probability one"
(`transient_iff`). -/
theorem measurableSet_finite_visits :
    MeasurableSet {ω : Sample d | (visits (paths ω)).Finite} := by
  -- A set is finite iff it is contained in some finset
  have h_finite_iff (s : Set (Vertex d × ℕ)) : s.Finite ↔ ∃ F : Finset (Vertex d × ℕ), s ⊆ (F : Set (Vertex d × ℕ)) := by
    constructor
    · intro h
      refine ⟨h.toFinset, ?_⟩
      rw [h.coe_toFinset]
    · intro ⟨F, hF⟩
      exact Set.Finite.subset (F.finite_toSet) hF
  -- Express the target set as a countable union
  have h_target_eq : {ω : Sample d | (visits (paths ω)).Finite} =
      ⋃ (F : Finset (Vertex d × ℕ)), {ω : Sample d | visits (paths ω) ⊆ (F : Set (Vertex d × ℕ))} := by
    ext ω
    simp [h_finite_iff (visits (paths ω))]
  rw [h_target_eq]
  -- Now we need to show this countable union is measurable
  refine MeasurableSet.iUnion fun F => ?_
  -- For each F, the set {ω | visits (paths ω) ⊆ F} is a countable intersection
  have h_subset_eq : {ω : Sample d | visits (paths ω) ⊆ (F : Set (Vertex d × ℕ))} =
      ⋂ (p : ((F : Set (Vertex d × ℕ))ᶜ : Set (Vertex d × ℕ))), {ω : Sample d | p.val ∉ visits (paths ω)} := by
    ext ω
    simp [Set.subset_def, Set.mem_compl_iff, Set.mem_iInter, not_imp_not, Set.mem_ofPred_eq]
  rw [h_subset_eq]
  -- The intersection over the countable subtype is measurable
  refine MeasurableSet.iInter fun p => ?_
  -- {ω | p.val ∉ visits (paths ω)} is the complement of {ω | p.val ∈ visits (paths ω)}
  have h_compl : {ω : Sample d | p.val ∉ visits (paths ω)} =
      ({ω : Sample d | p.val ∈ visits (paths ω)} : Set (Sample d))ᶜ := by
    ext ω; simp
  rw [h_compl]
  refine MeasurableSet.compl ?_
  -- Now we need to show {ω | (u, t) ∈ visits (paths ω)} is measurable for p.val = (u, t)
  rcases p.val with ⟨u, t⟩
  exact measurableSet_visits u t

end Sanity

/-- The frog model on the rooted `d`-ary tree is recurrent: almost surely the root is visited
infinitely often. -/
def Recurrent (d : ℕ) [NeZero d] : Prop :=
  ∀ᵐ ω ∂frogMeasure d, (visits (paths ω)).Infinite

/-- **Target.** The Hoffman-Johnson-Junge conjecture at `d = 3`: the frog model on the rooted
3-ary tree is recurrent. -/
theorem recurrent_three : Recurrent 3 := by
  sorry

end FrogModel
