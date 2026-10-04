module

public import FrogModel.D3.M1L.Defs
public import FrogModel.Pieces.Defs

@[expose] public section

/-!
# The planted curve on the frog paths

Definition 8.1 of the paper, on the frog paths. The vertex `w` (the vertex `r` of the paper) is
`some []` of `T*` (Pieces/Defs.lean), its parent the leaf `y = none`. Frog `φ` follows its own
steps `π φ` from its start: `w` for an entrant, `v` for the frog of `v`. The woken set at height
`m` with `k` entrants is the least set containing the entrants and the frog of every vertex `v` of
depth at most `m` that the path of a woken frog visits; `plantedG m k π` (`G_m(k)`) is the number
of woken frogs whose path reaches `y`.
-/

namespace FrogModel.D3

/-- Where a frog starts: an entrant at `w`, the frog of `v` at `v`. -/
def frogStart : Frog → Vertex 3
  | Sum.inl _ => []
  | Sum.inr v => v

/-- The position on `T*` of frog `φ` after `i` steps of its path. -/
def pos (π : Frog → ℕ → Step 3) (φ : Frog) (i : ℕ) : Option (Vertex 3) :=
  walkStar (some (frogStart φ)) (π φ) i

/-- The woken set of the planted model at height `m` with `k` entrants. -/
inductive Woken (m k : ℕ) (π : Frog → ℕ → Step 3) : Frog → Prop
  | ent (i : ℕ) : i < k → Woken m k π (Sum.inl i)
  | wake (φ : Frog) (v : Vertex 3) (n : ℕ) :
      Woken m k π φ → v.length ≤ m → pos π φ n = some v → Woken m k π (Sum.inr v)

/-- `G_m(k)`: the woken frogs whose path reaches `y`. -/
noncomputable def plantedG (m k : ℕ) (π : Frog → ℕ → Step 3) : ℕ∞ :=
  {φ | Woken m k π φ ∧ ∃ n, pos π φ n = none}.encard

/-- The frogs of the top closure at the start: the entrants and the frog of `w`. -/
def initPool (k : ℕ) : List Frog := (List.range k).map Sum.inl ++ [Sum.inr []]

/-- With at least one entrant, the frogs of the initial pool are woken. -/
theorem woken_of_mem_initPool {m k : ℕ} (hk : 1 ≤ k) (π : Frog → ℕ → Step 3) {φ : Frog}
    (h : φ ∈ initPool k) : Woken m k π φ := by
  simp only [initPool, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨i, hi, rfl⟩ | rfl
  · exact Woken.ent i hi
  · exact Woken.wake (Sum.inl 0) [] 0 (Woken.ent 0 hk) (Nat.zero_le _) rfl

/-- A step of `T*` from a vertex strictly below `w` is a ghost step. -/
theorem stepStar_cons (c : Fin 3) (u : Vertex 3) (ξ : Step 3) :
    stepStar (some (c :: u)) ξ = some (ghostStep (c :: u) ξ) := by
  unfold stepStar ghostStep
  by_cases h : ξ.2 = 0 <;> simp [h]

end FrogModel.D3
