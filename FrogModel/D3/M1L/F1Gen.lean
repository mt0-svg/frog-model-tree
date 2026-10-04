module

public import FrogModel.D3.M1L.F1Zero

@[expose] public section

/-!
# Domination at every height: the count of M1_L is at most `G_m(k)` on the frog paths

Lemma 13.1 of the paper (domination) for M1_L at every height. On the frog-path space the rule reads,
at each step, the next step of the path of the frog it names (`poolSeq_apply`). Invariant
(`InvF`): the frogs held by the state (pools, ghost frogs and ups of the open closures, or the
final ups) are distinct woken frogs; each frog of a pool is at the vertex of its closure, a ghost
frog at its vertex strictly below the vertex of its closure, a frog of the ups at the parent of the
vertex of its closure (`y` for the top closure), each at the position its own path has after the
steps read so far; the stack is a chain of parents that ends at `w`, within height `m`; the frog
of a vertex `z` is read or held only once `z` is marked (or `z = w`). Then the ups of the top
closure, and the final ups, are distinct woken frogs whose paths reach `y`: at most `G_m(k)`.
-/

namespace FrogModel.D3

/-- The parent of a vertex on `T*`: `none` is `y`, the parent of `w`. -/
def parentStar : Vertex 3 → Option (Vertex 3)
  | [] => none
  | _ :: v => some v

/-- The frogs held by a closure: its pool, its ghost frog and its ups. -/
def heldF (f : Frame) : List Frog := f.pool ++ (f.ghost.map Prod.fst).toList ++ f.ups

/-- The frogs held by a state: those of its closures, or the final ups. -/
def heldS (s : St) : List Frog := if s.stack = [] then s.out else s.stack.flatMap heldF

/-- The frogs of a closure are where the rule left them, for the paths `π` and the read
counts `c`. -/
def FramePos (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (f : Frame) : Prop :=
  (∀ φ ∈ f.pool, pos π φ (c φ) = some f.v) ∧
  (∀ φ u, f.ghost = some (φ, u) →
    pos π φ (c φ) = some u ∧ f.v <:+ u ∧ f.v.length < u.length) ∧
  (∀ φ ∈ f.ups, pos π φ (c φ) = parentStar f.v)

/-- The stack is a chain of parents that ends at `w`. -/
def ChainW : List Frame → Prop
  | [] => True
  | [f] => f.v = []
  | f :: g :: rest => f.v = f.v.headD 0 :: g.v ∧ ChainW (g :: rest)

/-- The last closure of a chain is at `w`. -/
theorem chainW_last : ∀ (l : List Frame), ChainW l → ∀ f, l.getLast? = some f → f.v = []
  | [], _, f, h => by simp at h
  | [g], h, f, hf => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hf
    subst hf
    exact h
  | g :: g2 :: rest, h, f, hf => chainW_last (g2 :: rest) h.2 f (by simpa using hf)

/-- The invariant of the run on the frog paths `π`, with the read counts `c`. -/
def InvF (m k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (s : St) : Prop :=
  (heldS s).Nodup ∧ (∀ φ ∈ heldS s, Woken m k π φ) ∧
  (s.stack = [] → ∀ φ ∈ s.out, ∃ i, pos π φ i = none) ∧
  ChainW s.stack ∧ (∀ f ∈ s.stack, FramePos π c f ∧ f.v.length ≤ m) ∧
  (∀ z, c (Sum.inr z) ≠ 0 → z = [] ∨ z ∈ s.marks) ∧
  (∀ z, Sum.inr z ∈ heldS s → z = [] ∨ z ∈ s.marks)

/-- The frogs held by a stack: those of its head, then those of the rest. -/
theorem heldS_cons (f : Frame) (rest : List Frame) (marks : Finset (Vertex 3)) (out : List Frog) :
    heldS ⟨f :: rest, marks, out⟩ = heldF f ++ rest.flatMap heldF := by
  simp [FrogModel.D3.heldS, List.flatMap_cons]

/-- A read of a frog not held by a closure keeps the positions of its frogs. -/
theorem framePos_bump (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (g : Frame) (φ : Frog)
    (h : FramePos π c g) (hφ : φ ∉ heldF g) : FramePos π (bump c (some φ)) g := by
  rcases h with ⟨hpool, hghost, hups⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ψ hψ
    have hψ_held : ψ ∈ heldF g := by
      unfold heldF
      exact List.mem_append_left _ (List.mem_append_left _ hψ)
    have hne : some φ ≠ some ψ := by
      intro heq
      have : φ = ψ := by
        injection heq
      apply hφ
      subst this
      exact hψ_held
    simpa [bump_ne hne] using hpool ψ hψ
  · intro ψ u hg
    have hψ_held : ψ ∈ heldF g := by
      unfold heldF
      simp [hg]
    have hne : some φ ≠ some ψ := by
      intro heq
      have : φ = ψ := by
        injection heq
      apply hφ
      subst this
      exact hψ_held
    rcases hghost ψ u hg with ⟨hpos, hlt1, hlt2⟩
    refine ⟨?_, hlt1, hlt2⟩
    simpa [bump_ne hne] using hpos
  · intro ψ hψ
    have hψ_held : ψ ∈ heldF g := by
      unfold heldF
      exact List.mem_append_right (g.pool ++ (g.ghost.map Prod.fst).toList) hψ
    have hne : some φ ≠ some ψ := by
      intro heq
      have : φ = ψ := by
        injection heq
      apply hφ
      subst this
      exact hψ_held
    simpa [bump_ne hne] using hups ψ hψ

/-- The invariant at the start. -/
theorem invF_init (m k : ℕ) (hk : 1 ≤ k) (π : Frog → ℕ → Step 3) :
    InvF m k π (fun _ => 0) (init k) := by
  dsimp [init, InvF, heldS, heldF, frogStart, pos, walkStar, parentStar]
  simp [heldF]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Nodup
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Nodup.map Sum.inl_injective List.nodup_range
    · exact List.nodup_singleton _
    · intro a ha b hb
      simp only [List.mem_map, List.mem_singleton] at ha hb
      rcases ha with ⟨i, hi, rfl⟩
      rcases hb with rfl
      intro h
      injection h
  · -- Woken
    refine ⟨?_, ?_⟩
    · intro a ha
      exact Woken.ent a ha
    · exact Woken.wake (Sum.inl 0) [] 0 (Woken.ent 0 hk) (Nat.zero_le _) rfl
  · -- ChainW
    simp [ChainW]
  · -- FramePos
    refine ⟨?_, ?_, ?_⟩
    · intro φ hφ
      simp at hφ
      rcases hφ with (⟨a, ha, rfl⟩ | rfl)
      · simp [pos, walkStar, frogStart]
      · simp [pos, walkStar, frogStart]
    · intro φ u h
      simp at h
    · intro φ hφ
      simp at hφ

/-- A closure that ends keeps the invariant: it ends the run if it is the top one, and
otherwise waits for its kill coin. -/
theorem invF_settle (m k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ)
    (marks : Finset (Vertex 3)) (f : Frame) (rest : List Frame)
    (h : InvF m k π c ⟨f :: rest, marks, []⟩) : InvF m k π c (settle marks (f :: rest)) := by
  rcases h with ⟨hnodup, hwoken, hout, hchain, hframe, hmark1, hmark2⟩
  have hframe_f : FramePos π c f ∧ f.v.length ≤ m := by
    simpa using hframe f (by simp)
  rcases hframe_f with ⟨hfpos, hfm⟩
  match rest with
  | [] =>
    have hchain_f : f.v = [] := by
      simpa [ChainW] using hchain
    have hparent : parentStar f.v = none := by
      rw [hchain_f]
      rfl
    unfold settle
    by_cases hfg : f.pool = [] ∧ f.ghost = none
    · rcases hfg with ⟨hpool, hghost⟩
      have h_heldF_eq_ups : heldF f = f.ups := by
        unfold heldF
        simp [hpool, hghost]
      have h_heldS_input_eq : heldS ⟨f :: [], marks, []⟩ = f.ups := by
        unfold heldS
        simp [h_heldF_eq_ups]
      have h_nodup : (f.ups).Nodup := by
        rw [← h_heldS_input_eq]
        exact hnodup
      have h_woken : ∀ φ ∈ f.ups, Woken m k π φ := by
        rw [← h_heldS_input_eq]
        exact hwoken
      have h_out_clause : ([] : List Frame) = [] → ∀ φ ∈ f.ups, ∃ i, pos π φ i = none := by
        intro _ φ hφ
        have hpos := hfpos.2.2 φ hφ
        rw [hparent] at hpos
        exact ⟨c φ, hpos⟩
      have h_chain : ChainW ([] : List Frame) := by
        simp [ChainW]
      have h_frame : ∀ f' ∈ ([] : List Frame), FramePos π c f' ∧ f'.v.length ≤ m := by
        simp
      have h_mark2 : ∀ z, Sum.inr z ∈ f.ups → z = [] ∨ z ∈ marks := by
        rw [h_heldS_input_eq] at hmark2
        exact hmark2
      simp [hpool, hghost]
      exact ⟨h_nodup, h_woken, h_out_clause, h_chain, h_frame, hmark1, h_mark2⟩
    · simp [hfg]
      exact ⟨hnodup, hwoken, hout, hchain, hframe, hmark1, hmark2⟩
  | g :: s =>
    -- Don't unfold settle yet; compute what it simplifies to
    by_cases hfg : f.pool = [] ∧ f.ghost = none
    · rcases hfg with ⟨hpool, hghost⟩
      -- settle marks (f :: g :: s) = { stack := {f with killing := true} :: g :: s, marks := marks, out := [] }
      have h_settle_eq : settle marks (f :: g :: s) =
          { stack := {f with killing := true} :: g :: s, marks := marks, out := [] } := by
        unfold settle
        simp [hpool, hghost]
      rw [h_settle_eq]
      unfold InvF
      -- Now the goal is a 7-way conjunction
      -- Key lemma: heldF is unchanged by killing
      have h_heldF_kill : heldF ({f with killing := true}) = heldF f := by
        unfold heldF; rfl
      have h_frame_kill (f' : Frame) (hf' : f' ∈ ({f with killing := true} :: g :: s)) :
          FramePos π c f' ∧ f'.v.length ≤ m := by
        simp at hf'
        rcases hf' with (rfl | hf')
        · -- f' = {f with killing := true}
          rcases hfpos with ⟨hpool_pos, hghost_pos, hups_pos⟩
          refine ⟨?_, ?_⟩
          · refine ⟨?_, ?_, ?_⟩
            · simpa [Frame.killing] using hpool_pos
            · simpa [Frame.killing] using hghost_pos
            · simpa [Frame.killing] using hups_pos
          · simpa [Frame.killing] using hfm
        · -- f' ∈ g :: s
          have := hframe f' (by simp [hf'])
          simpa [Frame.killing] using this
      -- Now build the 7 parts
      have h_nodup : (heldS { stack := {f with killing := true} :: g :: s, marks := marks, out := [] }).Nodup := by
        have h_eq : heldS { stack := {f with killing := true} :: g :: s, marks := marks, out := [] } =
                   heldS { stack := f :: g :: s, marks := marks, out := [] } := by
          unfold heldS
          simp [h_heldF_kill]
        rw [h_eq]
        simpa [heldS] using hnodup
      have h_woken : ∀ φ ∈ heldS { stack := {f with killing := true} :: g :: s, marks := marks, out := [] },
                      Woken m k π φ := by
        have h_eq : heldS { stack := {f with killing := true} :: g :: s, marks := marks, out := [] } =
                   heldS { stack := f :: g :: s, marks := marks, out := [] } := by
          unfold heldS
          simp [h_heldF_kill]
        rw [h_eq]
        simpa [heldS] using hwoken
      have h_out_clause : ({f with killing := true} :: g :: s) = [] →
                          ∀ φ ∈ ([] : List Frog), ∃ i, pos π φ i = none := by
        simp
      have h_chain : ChainW ({f with killing := true} :: g :: s) := by
        -- ChainW only depends on .v, which is unchanged by killing
        simpa [ChainW] using hchain
      have h_frame' : ∀ f' ∈ ({f with killing := true} :: g :: s),
                      FramePos π c f' ∧ f'.v.length ≤ m :=
        h_frame_kill
      have h_mark1' : ∀ z, c (Sum.inr z) ≠ 0 → z = [] ∨ z ∈ marks := by
        simpa using hmark1
      have h_mark2 : ∀ z, Sum.inr z ∈ heldS { stack := {f with killing := true} :: g :: s, marks := marks, out := [] } →
                      z = [] ∨ z ∈ marks := by
        have h_eq : heldS { stack := {f with killing := true} :: g :: s, marks := marks, out := [] } =
                   heldS { stack := f :: g :: s, marks := marks, out := [] } := by
          unfold heldS
          simp [h_heldF_kill]
        rw [h_eq]
        simpa [heldS] using hmark2
      exact ⟨h_nodup, h_woken, h_out_clause, h_chain, h_frame', h_mark1', h_mark2⟩
    · -- f.pool ≠ [] or f.ghost ≠ none
      unfold settle
      simp [hfg]
      exact ⟨hnodup, hwoken, hout, hchain, hframe, hmark1, hmark2⟩

/-- `ChainW` reads only the vertices of the frames. -/
theorem chainW_head (f g : Frame) (rest : List Frame) (h : g.v = f.v) (hc : ChainW (f :: rest)) :
    ChainW (g :: rest) := by
  cases rest with
  | nil => simpa [ChainW, h] using hc
  | cons f2 rest => exact ⟨by rw [h]; exact hc.1, hc.2⟩

/-- A closure with fewer frogs at the same places keeps their positions. -/
theorem framePos_sub (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (f g : Frame)
    (hpool : ∀ ψ ∈ g.pool, ψ ∈ f.pool) (hghost : g.ghost = f.ghost) (hups : g.ups = f.ups)
    (hv : g.v = f.v) (h : FramePos π c f) : FramePos π c g := by
  refine ⟨fun ψ hψ => hv ▸ h.1 ψ (hpool ψ hψ), fun ψ u hg' => ?_, fun ψ hψ => ?_⟩
  · rw [hghost] at hg'
    rw [hv]
    exact h.2.1 ψ u hg'
  · rw [hv]
    exact h.2.2 ψ (hups ▸ hψ)

/-- The frogs held by a state whose head has the pool `φ :: ps` and no ghost. -/
theorem heldS_head (f : Frame) (rest : List Frame) (marks : Finset (Vertex 3)) (out : List Frog)
    (φ : Frog) (ps : List Frog) (hg : f.ghost = none) (hp : f.pool = φ :: ps) :
    heldS ⟨f :: rest, marks, out⟩ = φ :: (ps ++ f.ups ++ rest.flatMap heldF) := by
  rw [heldS_cons]
  simp [heldF, hp, hg]

/-- After a read of `φ` with a child direction, `φ` is at the child. -/
theorem pos_child (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (φ : Frog) (v : Vertex 3)
    (hφ : pos π φ (c φ) = some v) (x : Val) (hx : x.1 = π φ (c φ)) (hx0 : x.1.2 ≠ 0) :
    pos π φ (bump c (some φ) φ) = some (x.1.2.pred hx0 :: v) := by
  rw [bump_self, pos_succ, hφ, ← hx]
  simp [stepStar, hx0]

/-- The read counts after a read of a held frog keep the marks clause. -/
theorem marks_bump (c : Frog → ℕ) (φ : Frog) (marks M : Finset (Vertex 3)) (hM : marks ⊆ M)
    (held : List Frog) (hφ : φ ∈ held)
    (hcm : ∀ z, c (Sum.inr z) ≠ 0 → z = [] ∨ z ∈ marks)
    (hhm : ∀ z, Sum.inr z ∈ held → z = [] ∨ z ∈ marks) :
    ∀ z, bump c (some φ) (Sum.inr z) ≠ 0 → z = [] ∨ z ∈ M := by
  intro z hz
  by_cases h : φ = Sum.inr z
  · subst h
    exact (hhm z hφ).imp_right fun h => hM h
  · rw [bump_ne (fun e => h (Option.some.inj e))] at hz
    exact (hcm z hz).imp_right fun h => hM h

/-- A ghost step that does not come back to `v` stays strictly below `v`. -/
theorem ghost_suffix (v u : Vertex 3) (ξ : Step 3) (hsuf : v <:+ u) (h1 : v.length < u.length)
    (hne : ghostStep u ξ ≠ v) : v <:+ ghostStep u ξ ∧ v.length < (ghostStep u ξ).length := by
  obtain ⟨w, rfl⟩ := hsuf
  simp only [List.length_append] at h1
  by_cases hx : ξ.2 = 0
  · have hstep : ghostStep (w ++ v) ξ = w.tail ++ v := by
      simp only [ghostStep, hx, ↓reduceDIte]
      cases w with
      | nil => simp at h1
      | cons a w => rfl
    rw [hstep] at hne ⊢
    have hwt : w.tail ≠ [] := fun h => hne (by rw [h, List.nil_append])
    have hpos : 0 < w.tail.length := List.length_pos_iff.mpr hwt
    exact ⟨⟨w.tail, rfl⟩, by simp only [List.length_append]; omega⟩
  · have hstep : ghostStep (w ++ v) ξ = (ξ.2.pred hx :: w) ++ v := by
      simp [ghostStep, hx]
    rw [hstep]
    exact ⟨⟨_, rfl⟩, by simp only [List.length_append, List.length_cons]; omega⟩

/-- A read sending the head's frog up keeps the invariant. -/
theorem invF_up (p : Params) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (f : Frame)
    (rest : List Frame) (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : InvF p.m k π c ⟨f :: rest, marks, out⟩) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) (hx0 : x.1.2 = 0)
    (hx : x.1 = π φ (c φ)) :
    InvF p.m k π (bump c (some φ)) (upd p ⟨f :: rest, marks, out⟩ x) := by
  obtain ⟨hnd, hwk, -, hch, hfp, hcm, hhm⟩ := hs
  have hf := hfp f (List.mem_cons_self ..)
  have hφv : pos π φ (c φ) = some f.v := hf.1.1 φ (by rw [hp]; exact List.mem_cons_self ..)
  have hold := heldS_head f rest marks out φ ps hg hp
  rw [hold] at hnd hwk hhm
  obtain ⟨hφT, -⟩ := List.nodup_cons.1 hnd
  have hne : ∀ ψ, ψ ∈ ps ∨ ψ ∈ f.ups → some φ ≠ some ψ := by
    rintro ψ h e
    cases Option.some.inj e
    exact hφT (by rcases h with h | h <;> simp [h])
  have hφr : ∀ g ∈ rest, φ ∉ heldF g := fun g hg' h =>
    hφT (List.mem_append_right _ (List.mem_flatMap.2 ⟨g, hg', h⟩))
  have hpos : pos π φ (bump c (some φ) φ) = parentStar f.v := by
    rw [bump_self, pos_succ, hφv, ← hx]
    cases hv : f.v with
    | nil => simp [stepStar, hx0, parentStar]
    | cons a w => simp [stepStar, hx0, parentStar]
  have hupd : upd p ⟨f :: rest, marks, out⟩ x =
      settle marks ({f with pool := ps, ups := if f.ups.length < p.V then f.ups ++ [φ] else f.ups} ::
        rest) := by
    simp only [upd, hk, hg, hp, hx0, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  rw [hupd]
  generalize hu : (if f.ups.length < p.V then f.ups ++ [φ] else f.ups) = ups'
  have hus : ups'.Sublist (f.ups ++ [φ]) := by
    rw [← hu]
    split_ifs
    · exact List.Sublist.refl _
    · exact List.sublist_append_left _ _
  have hnew : heldS ⟨{f with pool := ps, ups := ups'} :: rest, marks, []⟩ =
      ps ++ ups' ++ rest.flatMap heldF := by
    rw [heldS_cons]
    simp [heldF, hg]
  have hsub : (ps ++ ups' ++ rest.flatMap heldF).Sublist (ps ++ (f.ups ++ [φ]) ++ rest.flatMap heldF) :=
    (hus.append_left ps).append_right _
  have hperm : (ps ++ (f.ups ++ [φ]) ++ rest.flatMap heldF).Perm
      (φ :: (ps ++ f.ups ++ rest.flatMap heldF)) := by
    simp only [List.append_assoc, List.singleton_append]
    rw [← List.append_assoc ps f.ups]
    exact List.perm_middle.trans (by rw [List.append_assoc])
  have hsp : ∀ ψ ∈ ps ++ ups' ++ rest.flatMap heldF, ψ ∈ φ :: (ps ++ f.ups ++ rest.flatMap heldF) :=
    fun ψ h => hperm.subset (hsub.subset h)
  refine invF_settle p.m k π _ marks _ rest ⟨?_, ?_, fun h => absurd h (List.cons_ne_nil _ _),
    chainW_head f _ rest rfl hch, ?_, marks_bump c φ marks marks subset_rfl _
      (List.mem_cons_self ..) hcm hhm, ?_⟩
  · rw [hnew]
    exact hsub.nodup (hperm.nodup_iff.2 hnd)
  · rw [hnew]
    exact fun ψ h => hwk ψ (hsp ψ h)
  · intro fr hfr
    rcases List.mem_cons.1 hfr with rfl | hfr
    · refine ⟨⟨fun ψ hψ => ?_, fun _ _ h => absurd h (by simp [hg]), fun ψ hψ => ?_⟩, hf.2⟩
      · rw [bump_ne (hne ψ (Or.inl hψ))]
        exact hf.1.1 ψ (by rw [hp]; exact List.mem_cons_of_mem _ hψ)
      · rcases List.mem_append.1 (hus.subset hψ) with h | h
        · rw [bump_ne (hne ψ (Or.inr h))]
          exact hf.1.2.2 ψ h
        · rw [List.mem_singleton] at h
          subst h
          exact hpos
    · have := hfp fr (List.mem_cons_of_mem _ hfr)
      exact ⟨framePos_bump π c fr φ this.1 (hφr fr hfr), this.2⟩
  · rw [hnew]
    exact fun z h => hhm z (hsp _ h)

/-- A read starting a ghost walk from the head keeps the invariant. -/
theorem invF_ghost_entry (p : Params) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ)
    (f : Frame) (rest : List Frame) (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : InvF p.m k π c ⟨f :: rest, marks, out⟩) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) (hx0 : x.1.2 ≠ 0)
    (hge : f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx0 :: f.v ∈ marks))
    (hx : x.1 = π φ (c φ)) :
    InvF p.m k π (bump c (some φ)) (upd p ⟨f :: rest, marks, out⟩ x) := by
  obtain ⟨hnd, hwk, -, hch, hfp, hcm, hhm⟩ := hs
  have hupd : upd p ⟨f :: rest, marks, out⟩ x =
      ⟨{f with pool := ps, ghost := some (φ, x.1.2.pred hx0 :: f.v)} :: rest, marks, []⟩ := by
    simp only [upd, hk, hg, hp, hx0, hge, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  rw [hupd]
  generalize hzd : x.1.2.pred hx0 :: f.v = z at hge ⊢
  have hold := heldS_head f rest marks out φ ps hg hp
  have hperm : (heldS ⟨{f with pool := ps, ghost := some (φ, z)} :: rest, marks, []⟩).Perm
      (heldS ⟨f :: rest, marks, out⟩) := by
    rw [hold, heldS_cons]
    simp only [heldF, Option.map_some, Option.toList_some, List.append_assoc, List.singleton_append]
    exact List.perm_middle
  rw [hold] at hhm
  have hf := hfp f (List.mem_cons_self ..)
  have hφv : pos π φ (c φ) = some f.v := hf.1.1 φ (by rw [hp]; exact List.mem_cons_self ..)
  have hpos : pos π φ (bump c (some φ) φ) = some z := by
    rw [← hzd]; exact pos_child π c φ f.v hφv x hx hx0
  have hnd' := hnd
  rw [hold] at hnd'
  obtain ⟨hφT, -⟩ := List.nodup_cons.1 hnd'
  have hφr : ∀ g ∈ rest, φ ∉ heldF g := fun g hg' h =>
    hφT (List.mem_append_right _ (List.mem_flatMap.2 ⟨g, hg', h⟩))
  have hne : ∀ ψ, ψ ∈ ps ∨ ψ ∈ f.ups → some φ ≠ some ψ := by
    rintro ψ h e
    cases Option.some.inj e
    exact hφT (by rcases h with h | h <;> simp [h])
  refine ⟨hperm.nodup_iff.2 hnd, fun ψ h => hwk ψ (hperm.mem_iff.1 h), ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact absurd h (List.cons_ne_nil _ _)
  · exact chainW_head f _ rest rfl hch
  · intro fr hfr
    rcases List.mem_cons.1 hfr with rfl | hfr
    · refine ⟨⟨fun ψ hψ => ?_, fun ψ u h => ?_, fun ψ hψ => ?_⟩, hf.2⟩
      · rw [bump_ne (hne ψ (Or.inl hψ))]
        exact hf.1.1 ψ (by rw [hp]; exact List.mem_cons_of_mem _ hψ)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hpos, ?_, ?_⟩
        · rw [← hzd]; exact List.suffix_cons _ _
        · rw [← hzd, List.length_cons]; exact Nat.lt_succ_self _
      · rw [bump_ne (hne ψ (Or.inr hψ))]
        exact hf.1.2.2 ψ hψ
    · have := hfp fr (List.mem_cons_of_mem _ hfr)
      exact ⟨framePos_bump π c fr φ this.1 (hφr fr hfr), this.2⟩
  · exact marks_bump c φ marks _ subset_rfl _ (List.mem_cons_self ..) hcm hhm
  · intro z' h
    exact hhm z' (hold ▸ hperm.mem_iff.1 h)

/-- A read entering an unmarked child keeps the invariant: the frog of the child is woken. -/
theorem invF_R (p : Params) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ)
    (f : Frame) (rest : List Frame) (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : InvF p.m k π c ⟨f :: rest, marks, out⟩) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) (hx0 : x.1.2 ≠ 0)
    (hnot : ¬(f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx0 :: f.v ∈ marks)))
    (hz : x.1.2.pred hx0 :: f.v ∉ marks) (hx : x.1 = π φ (c φ)) :
    InvF p.m k π (bump c (some φ)) (upd p ⟨f :: rest, marks, out⟩ x) := by
  obtain ⟨hnd, hwk, -, hch, hfp, hcm, hhm⟩ := hs
  have hupd : upd p ⟨f :: rest, marks, out⟩ x =
      ⟨⟨x.1.2.pred hx0 :: f.v, true, 3, [φ, Sum.inr (x.1.2.pred hx0 :: f.v)], [], none, false⟩ ::
        {f with pool := ps} :: rest, insert (x.1.2.pred hx0 :: f.v) marks, []⟩ := by
    have hm : ¬ f.v.length = p.m := fun h => hnot (Or.inl h)
    simp only [upd, hk, hg, hp, hx0, hm, hz, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
      not_false_eq_true, and_false, or_self]
  rw [hupd]
  generalize hzd : x.1.2.pred hx0 :: f.v = z at hz hnot ⊢
  have hold := heldS_head f rest marks out φ ps hg hp
  rw [hold] at hnd hwk hhm
  have hnew : heldS ⟨⟨z, true, 3, [φ, Sum.inr z], [], none, false⟩ :: {f with pool := ps} :: rest,
      insert z marks, []⟩ = φ :: Sum.inr z :: (ps ++ f.ups ++ rest.flatMap heldF) := by
    rw [heldS_cons]
    simp [heldF, hg]
  have hf := hfp f (List.mem_cons_self ..)
  have hφv : pos π φ (c φ) = some f.v := hf.1.1 φ (by rw [hp]; exact List.mem_cons_self ..)
  have hpos : pos π φ (bump c (some φ) φ) = some z := by
    rw [← hzd]; exact pos_child π c φ f.v hφv x hx hx0
  have hlen : z.length ≤ p.m := by
    rw [← hzd, List.length_cons]
    have := hf.2
    have : f.v.length ≠ p.m := fun h => hnot (Or.inl h)
    omega
  have hz0 : z ≠ [] := by rw [← hzd]; exact List.cons_ne_nil _ _
  have hzn : Sum.inr z ∉ φ :: (ps ++ f.ups ++ rest.flatMap heldF) := fun h => by
    rcases hhm z h with h | h
    · exact hz0 h
    · exact hz h
  have hcz : c (Sum.inr z) = 0 := by
    by_contra h
    rcases hcm z h with h | h
    · exact hz0 h
    · exact hz h
  have hφz : φ ≠ Sum.inr z := fun h => hzn (h ▸ List.mem_cons_self ..)
  obtain ⟨hφT, hTnd⟩ := List.nodup_cons.1 hnd
  have hφr : ∀ g ∈ rest, φ ∉ heldF g := fun g hg' h =>
    hφT (by exact List.mem_append_right _ (List.mem_flatMap.2 ⟨g, hg', h⟩))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnew]
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨fun h => hzn (List.mem_cons_of_mem _ h), hTnd⟩⟩
    intro h
    rcases List.mem_cons.1 h with h | h
    · exact hφz h
    · exact hφT h
  · rw [hnew]
    intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact hwk ψ (List.mem_cons_self ..)
    rcases List.mem_cons.1 hψ with rfl | hψ
    · rw [bump_self] at hpos
      exact Woken.wake φ z (c φ + 1) (hwk φ (List.mem_cons_self ..)) hlen hpos
    · exact hwk ψ (List.mem_cons_of_mem _ hψ)
  · intro h
    exact absurd h (List.cons_ne_nil _ _)
  · exact ⟨by rw [← hzd]; rfl, chainW_head f _ rest rfl hch⟩
  · intro fr hfr
    rcases List.mem_cons.1 hfr with rfl | hfr
    · refine ⟨⟨?_, fun _ _ h => absurd h (by simp), fun _ h => absurd h (by simp)⟩, hlen⟩
      intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hpos
      · rw [List.mem_singleton] at hψ
        subst hψ
        rw [bump_ne (fun e => hφz (Option.some.inj e)), hcz]
        rfl
    rcases List.mem_cons.1 hfr with rfl | hfr
    · refine ⟨framePos_bump π c _ φ (framePos_sub π c f _ (fun ψ hψ => by
        rw [hp]; exact List.mem_cons_of_mem _ hψ) rfl rfl rfl hf.1) ?_, hf.2⟩
      intro h
      simp only [heldF, hg, Option.map_none, Option.toList_none, List.append_nil,
        List.mem_append] at h
      exact hφT (by rcases h with h | h <;> simp [h])
    · have := hfp fr (List.mem_cons_of_mem _ hfr)
      exact ⟨framePos_bump π c fr φ this.1 (hφr fr hfr), this.2⟩
  · exact marks_bump c φ marks _ (Finset.subset_insert _ _) _ (List.mem_cons_self ..) hcm hhm
  · rw [hnew]
    intro z' hz'
    rcases List.mem_cons.1 hz' with h | hz'
    · exact (hhm z' (h ▸ List.mem_cons_self ..)).imp_right (Finset.mem_insert_of_mem)
    rcases List.mem_cons.1 hz' with h | hz'
    · cases h
      exact Or.inr (Finset.mem_insert_self _ _)
    · exact (hhm z' (List.mem_cons_of_mem _ hz')).imp_right (Finset.mem_insert_of_mem)

/-- A read entering a marked child of an R closure keeps the invariant. -/
theorem invF_H (p : Params) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ)
    (f : Frame) (rest : List Frame) (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : InvF p.m k π c ⟨f :: rest, marks, out⟩) (hk : f.killing = false)
    (hg : f.ghost = none) (φ : Frog) (ps : List Frog) (hp : f.pool = φ :: ps) (hx0 : x.1.2 ≠ 0)
    (hnot : ¬(f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx0 :: f.v ∈ marks)))
    (hz : x.1.2.pred hx0 :: f.v ∈ marks) (hx : x.1 = π φ (c φ)) :
    InvF p.m k π (bump c (some φ)) (upd p ⟨f :: rest, marks, out⟩ x) := by
  obtain ⟨hnd, hwk, -, hch, hfp, hcm, hhm⟩ := hs
  have hm : ¬ f.v.length = p.m := fun h => hnot (Or.inl h)
  have hisR : f.isR = true := by
    cases h : f.isR
    · exact absurd (Or.inr ⟨h, hz⟩) hnot
    · rfl
  have hupd : upd p ⟨f :: rest, marks, out⟩ x =
      ⟨⟨x.1.2.pred hx0 :: f.v, false, unmarked marks (x.1.2.pred hx0 :: f.v), [φ], [], none, false⟩ ::
        {f with pool := ps} :: rest, marks, []⟩ := by
    simp only [upd, hk, hg, hp, hx0, hm, hz, hisR, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, ↓reduceDIte, not_true_eq_false, and_true, or_self]
  rw [hupd]
  generalize hzd : x.1.2.pred hx0 :: f.v = z at hz hnot ⊢
  have hold := heldS_head f rest marks out φ ps hg hp
  have hnew : heldS ⟨⟨z, false, unmarked marks z, [φ], [], none, false⟩ :: {f with pool := ps} :: rest,
      marks, []⟩ = heldS ⟨f :: rest, marks, out⟩ := by
    rw [hold, heldS_cons]
    simp [heldF, hg]
  rw [hold] at hhm
  have hf := hfp f (List.mem_cons_self ..)
  have hφv : pos π φ (c φ) = some f.v := hf.1.1 φ (by rw [hp]; exact List.mem_cons_self ..)
  have hpos : pos π φ (bump c (some φ) φ) = some z := by
    rw [← hzd]; exact pos_child π c φ f.v hφv x hx hx0
  have hlen : z.length ≤ p.m := by
    rw [← hzd, List.length_cons]
    have := hf.2
    omega
  have hnd' := hnd
  rw [hold] at hnd'
  obtain ⟨hφT, -⟩ := List.nodup_cons.1 hnd'
  have hφr : ∀ g ∈ rest, φ ∉ heldF g := fun g hg' h =>
    hφT (List.mem_append_right _ (List.mem_flatMap.2 ⟨g, hg', h⟩))
  refine ⟨hnew ▸ hnd, hnew ▸ hwk, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact absurd h (List.cons_ne_nil _ _)
  · exact ⟨by rw [← hzd]; rfl, chainW_head f _ rest rfl hch⟩
  · intro fr hfr
    rcases List.mem_cons.1 hfr with rfl | hfr
    · refine ⟨⟨?_, fun _ _ h => absurd h (by simp), fun _ h => absurd h (by simp)⟩, hlen⟩
      intro ψ hψ
      rw [List.mem_singleton] at hψ
      subst hψ
      exact hpos
    rcases List.mem_cons.1 hfr with rfl | hfr
    · refine ⟨framePos_bump π c _ φ (framePos_sub π c f _ (fun ψ hψ => by
        rw [hp]; exact List.mem_cons_of_mem _ hψ) rfl rfl rfl hf.1) ?_, hf.2⟩
      intro h
      simp only [heldF, hg, Option.map_none, Option.toList_none, List.append_nil,
        List.mem_append] at h
      exact hφT (by rcases h with h | h <;> simp [h])
    · have := hfp fr (List.mem_cons_of_mem _ hfr)
      exact ⟨framePos_bump π c fr φ this.1 (hφr fr hfr), this.2⟩
  · exact marks_bump c φ marks _ subset_rfl _ (List.mem_cons_self ..) hcm hhm
  · rw [hnew, hold]
    exact hhm

/-- A step of the ghost walk of the head keeps the invariant. -/
theorem invF_ghost (p : Params) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ)
    (f : Frame) (rest : List Frame) (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : InvF p.m k π c ⟨f :: rest, marks, out⟩) (hk : f.killing = false) (φ : Frog)
    (u : Vertex 3) (hg : f.ghost = some (φ, u)) (hx : x.1 = π φ (c φ)) :
    InvF p.m k π (bump c (some φ)) (upd p ⟨f :: rest, marks, out⟩ x) := by
  obtain ⟨hnd, hwk, -, hch, hfp, hcm, hhm⟩ := hs
  have hf := hfp f (List.mem_cons_self ..)
  obtain ⟨hφu, hsuf, hlt⟩ := hf.1.2.1 φ u hg
  have hold : heldS ⟨f :: rest, marks, out⟩ = f.pool ++ φ :: (f.ups ++ rest.flatMap heldF) := by
    rw [heldS_cons]
    simp [heldF, hg]
  rw [hold] at hnd hwk hhm
  have hu0 : u ≠ [] := by
    intro h
    rw [h] at hlt
    simp at hlt
  have hpos : pos π φ (bump c (some φ) φ) = some (ghostStep u x.1) := by
    rw [bump_self, pos_succ, hφu, ← hx]
    obtain ⟨a, u0, rfl⟩ := List.exists_cons_of_ne_nil hu0
    exact stepStar_cons a u0 _
  have hnd2 := List.nodup_middle.1 hnd
  obtain ⟨hφT, hTnd⟩ := List.nodup_cons.1 hnd2
  have hne : ∀ ψ, ψ ∈ f.pool ∨ ψ ∈ f.ups → some φ ≠ some ψ := by
    rintro ψ h e
    cases Option.some.inj e
    exact hφT (by rcases h with h | h <;> simp [h])
  have hφr : ∀ g ∈ rest, φ ∉ heldF g := fun g hg' h =>
    hφT (List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨g, hg', h⟩)))
  have hrest : ∀ fr ∈ rest, FramePos π (bump c (some φ)) fr ∧ fr.v.length ≤ p.m := fun fr hfr =>
    ⟨framePos_bump π c fr φ (hfp fr (List.mem_cons_of_mem _ hfr)).1 (hφr fr hfr),
      (hfp fr (List.mem_cons_of_mem _ hfr)).2⟩
  have hmk := marks_bump c φ marks marks subset_rfl _ (List.mem_append_right _ (List.mem_cons_self ..))
    hcm hhm
  have hupd : upd p ⟨f :: rest, marks, out⟩ x =
      if ghostStep u x.1 = f.v then ⟨{f with pool := φ :: f.pool, ghost := none} :: rest, marks, []⟩
      else if (ghostStep u x.1).length = f.v.length + p.L then
        settle marks ({f with ghost := none} :: rest)
      else ⟨{f with ghost := some (φ, ghostStep u x.1)} :: rest, marks, []⟩ := by
    simp only [upd, hk, hg, Bool.false_eq_true, ↓reduceIte]
  rw [hupd]
  split_ifs with h1 h2
  · have hperm : (heldS ⟨{f with pool := φ :: f.pool, ghost := none} :: rest, marks, []⟩).Perm
        (f.pool ++ φ :: (f.ups ++ rest.flatMap heldF)) := by
      rw [heldS_cons]
      simp only [heldF, Option.map_none, Option.toList_none, List.append_nil, List.cons_append,
        List.append_assoc]
      exact List.perm_middle.symm
    refine ⟨hperm.nodup_iff.2 hnd, fun ψ h => hwk ψ (hperm.mem_iff.1 h), fun h => absurd h
      (List.cons_ne_nil _ _), chainW_head f _ rest rfl hch, ?_, hmk,
      fun z h => hhm z (hperm.mem_iff.1 h)⟩
    intro fr hfr
    rcases List.mem_cons.1 hfr with rfl | hfr
    · refine ⟨⟨fun ψ hψ => ?_, fun _ _ h => absurd h (by simp), fun ψ hψ => ?_⟩, hf.2⟩
      · rcases List.mem_cons.1 hψ with rfl | hψ
        · rw [hpos, h1]
        · rw [bump_ne (hne ψ (Or.inl hψ))]
          exact hf.1.1 ψ hψ
      · rw [bump_ne (hne ψ (Or.inr hψ))]
        exact hf.1.2.2 ψ hψ
    · exact hrest fr hfr
  · refine invF_settle p.m k π _ marks _ rest ⟨?_, ?_, fun h => absurd h (List.cons_ne_nil _ _),
      chainW_head f _ rest rfl hch, ?_, hmk, ?_⟩
    · rw [heldS_cons]
      simpa [heldF, List.append_assoc] using hTnd
    · intro ψ h
      rw [heldS_cons] at h
      simp only [heldF, Option.map_none, Option.toList_none, List.append_nil, List.mem_append] at h
      exact hwk ψ (by rcases h with (h | h) | h <;> simp [h])
    · intro fr hfr
      rcases List.mem_cons.1 hfr with rfl | hfr
      · refine ⟨⟨fun ψ hψ => ?_, fun _ _ h => absurd h (by simp), fun ψ hψ => ?_⟩, hf.2⟩
        · rw [bump_ne (hne ψ (Or.inl hψ))]
          exact hf.1.1 ψ hψ
        · rw [bump_ne (hne ψ (Or.inr hψ))]
          exact hf.1.2.2 ψ hψ
      · exact hrest fr hfr
    · intro z h
      rw [heldS_cons] at h
      simp only [heldF, Option.map_none, Option.toList_none, List.append_nil, List.mem_append] at h
      exact hhm z (by rcases h with (h | h) | h <;> simp [h])
  · obtain ⟨hs1, hs2⟩ := ghost_suffix f.v u x.1 hsuf hlt h1
    have heq : heldS ⟨{f with ghost := some (φ, ghostStep u x.1)} :: rest, marks, []⟩ =
        f.pool ++ φ :: (f.ups ++ rest.flatMap heldF) := by
      rw [heldS_cons]
      simp [heldF]
    refine ⟨heq ▸ hnd, heq ▸ hwk, fun h => absurd h (List.cons_ne_nil _ _),
      chainW_head f _ rest rfl hch, ?_, hmk, heq ▸ hhm⟩
    intro fr hfr
    rcases List.mem_cons.1 hfr with rfl | hfr
    · refine ⟨⟨fun ψ hψ => ?_, fun ψ u' h => ?_, fun ψ hψ => ?_⟩, hf.2⟩
      · rw [bump_ne (hne ψ (Or.inl hψ))]
        exact hf.1.1 ψ hψ
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hpos, hs1, hs2⟩
      · rw [bump_ne (hne ψ (Or.inr hψ))]
        exact hf.1.2.2 ψ hψ
    · exact hrest fr hfr

/-- The kill coin of the head keeps the invariant: kept, its ups go to the pool of its parent
(capped at `P`); killed, its ups are discarded and its children marked. -/
theorem invF_kill (p : Params) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ)
    (f : Frame) (rest : List Frame) (marks : Finset (Vertex 3)) (out : List Frog) (x : Val)
    (hs : InvF p.m k π c ⟨f :: rest, marks, out⟩) (hk : f.killing = true) :
    InvF p.m k π c (upd p ⟨f :: rest, marks, out⟩ x) := by
  obtain ⟨hnd, hwk, -, hch, hfp, hcm, hhm⟩ := hs
  have hf := hfp f (List.mem_cons_self ..)
  rw [heldS_cons] at hnd hwk hhm
  generalize hkept : p.keep f.isR (p.m - f.v.length) f.f0 f.ups.length (unmarked marks f.v) x.2 = kept
  have hM : marks ⊆ (if kept then marks else marks ∪ kids f.v) := by
    split_ifs
    · exact subset_rfl
    · exact Finset.subset_union_left
  have hrets : (if kept then f.ups else []).Sublist f.ups := by
    split_ifs
    · exact List.Sublist.refl _
    · exact List.nil_sublist _
  have hups_held : ∀ ψ ∈ f.ups, ψ ∈ heldF f := fun ψ h => List.mem_append_right _ h
  cases rest with
  | nil =>
    have hupd : upd p ⟨[f], marks, out⟩ x =
        ⟨[], if kept then marks else marks ∪ kids f.v, if kept then f.ups else []⟩ := by
      simp only [upd, hk, ↓reduceIte, hkept]
    rw [hupd]
    have hv : f.v = [] := hch
    simp only [List.flatMap_nil, List.append_nil] at hnd hwk hhm
    refine ⟨?_, ?_, ?_, trivial, fun _ h => absurd h (List.not_mem_nil), fun z h => (hcm z h).imp_right
      fun h => hM h, ?_⟩
    · simp only [heldS, ↓reduceIte]
      exact (hrets.trans (List.sublist_append_right _ _)).nodup hnd
    · intro ψ h
      simp only [heldS, ↓reduceIte] at h
      exact hwk ψ (hups_held ψ (hrets.subset h))
    · intro _ ψ h
      refine ⟨c ψ, ?_⟩
      rw [hf.1.2.2 ψ (hrets.subset h), hv]
      rfl
    · intro z h
      simp only [heldS, ↓reduceIte] at h
      exact (hhm z (hups_held _ (hrets.subset h))).imp_right fun h => hM h
  | cons g rest' =>
    have hupd : upd p ⟨f :: g :: rest', marks, out⟩ x =
        settle (if kept then marks else marks ∪ kids f.v)
          ({g with pool := (g.pool ++ if kept then f.ups else []).take p.P} :: rest') := by
      simp only [upd, hk, ↓reduceIte, hkept]
    rw [hupd]
    have hg := hfp g (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain ⟨hvfg, hch'⟩ := hch
    have hpar : parentStar f.v = some g.v := by rw [hvfg]; rfl
    set X := (g.ghost.map Prod.fst).toList ++ g.ups ++ rest'.flatMap heldF with hX
    have hold : heldF f ++ (g :: rest').flatMap heldF =
        (f.pool ++ (f.ghost.map Prod.fst).toList) ++ (f.ups ++ (g.pool ++ X)) := by
      simp [heldF, hX, List.append_assoc]
    rw [hold] at hnd hwk hhm
    have h1 : (f.ups ++ (g.pool ++ X)).Nodup := hnd.sublist (List.sublist_append_right _ _)
    have h2 : (g.pool ++ f.ups ++ X).Nodup := by
      rw [← List.append_assoc] at h1
      exact (List.perm_append_comm.append_right X).nodup_iff.1 h1
    have hsub : ((g.pool ++ if kept then f.ups else []).take p.P ++ X).Sublist
        (g.pool ++ f.ups ++ X) :=
      ((List.take_sublist _ _).trans (hrets.append_left g.pool)).append_right X
    have hmem : ∀ ψ ∈ (g.pool ++ if kept then f.ups else []).take p.P ++ X,
        ψ ∈ (f.pool ++ (f.ghost.map Prod.fst).toList) ++ (f.ups ++ (g.pool ++ X)) := by
      intro ψ h
      have := hsub.subset h
      simp only [List.mem_append] at this ⊢
      tauto
    have hnew : heldS ⟨{g with pool := (g.pool ++ if kept then f.ups else []).take p.P} :: rest',
        if kept then marks else marks ∪ kids f.v, []⟩ =
        (g.pool ++ if kept then f.ups else []).take p.P ++ X := by
      rw [heldS_cons]
      simp [heldF, hX, List.append_assoc]
    refine invF_settle p.m k π c _ _ rest' ⟨?_, ?_, fun h => absurd h (List.cons_ne_nil _ _),
      chainW_head g _ rest' rfl hch', ?_, fun z h => (hcm z h).imp_right fun h => hM h, ?_⟩
    · rw [hnew]
      exact hsub.nodup h2
    · rw [hnew]
      exact fun ψ h => hwk ψ (hmem ψ h)
    · intro fr hfr
      rcases List.mem_cons.1 hfr with rfl | hfr
      · refine ⟨⟨fun ψ hψ => ?_, hg.1.2.1, hg.1.2.2⟩, hg.2⟩
        rcases List.mem_append.1 (List.mem_of_mem_take hψ) with h | h
        · exact hg.1.1 ψ h
        · rw [hf.1.2.2 ψ (hrets.subset h), hpar]
      · exact hfp fr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hfr))
    · rw [hnew]
      exact fun z h => (hhm z (hmem _ h)).imp_right fun h => hM h

/-- **One read keeps the invariant**, the read counts bumped at the frog read. -/
theorem invF_step (p : Params) (k : ℕ) (π : Frog → ℕ → Step 3) (c : Frog → ℕ) (s : St) (x : Val)
    (h : InvF p.m k π c s) (hx : ∀ φ, req s = some φ → x.1 = π φ (c φ)) :
    InvF p.m k π (bump c (req s)) (upd p s x) := by
  have hb0 : bump c none = c := by funext ψ; simp [bump]
  obtain ⟨stack, marks, out⟩ := s
  cases stack with
  | nil =>
    have hr : req ⟨[], marks, out⟩ = none := rfl
    rw [hr, hb0]
    exact h
  | cons f rest =>
    cases hk : f.killing
    · cases hg : f.ghost with
      | some pu =>
        obtain ⟨φ, u⟩ := pu
        have hr : req ⟨f :: rest, marks, out⟩ = some φ := by simp [req, hk, hg]
        rw [hr]
        exact invF_ghost p k π c f rest marks out x h hk φ u hg (hx φ hr)
      | none =>
        cases hp : f.pool with
        | nil =>
          have hr : req ⟨f :: rest, marks, out⟩ = none := by simp [req, hk, hg, hp]
          have hu : upd p ⟨f :: rest, marks, out⟩ x = ⟨f :: rest, marks, out⟩ := by
            simp [upd, hk, hg, hp]
          rw [hr, hb0, hu]
          exact h
        | cons φ ps =>
          have hr : req ⟨f :: rest, marks, out⟩ = some φ := by simp [req, hk, hg, hp]
          rw [hr]
          have hxφ := hx φ hr
          by_cases hx0 : x.1.2 = 0
          · exact invF_up p k π c f rest marks out x h hk hg φ ps hp hx0 hxφ
          · by_cases hge : f.v.length = p.m ∨ (f.isR = false ∧ x.1.2.pred hx0 :: f.v ∈ marks)
            · exact invF_ghost_entry p k π c f rest marks out x h hk hg φ ps hp hx0 hge hxφ
            · by_cases hz : x.1.2.pred hx0 :: f.v ∈ marks
              · exact invF_H p k π c f rest marks out x h hk hg φ ps hp hx0 hge hz hxφ
              · exact invF_R p k π c f rest marks out x h hk hg φ ps hp hx0 hge hz hxφ
    · have hr : req ⟨f :: rest, marks, out⟩ = none := by simp [req, hk]
      rw [hr, hb0]
      exact invF_kill p k π c f rest marks out x h hk

/-- **The invariant along the run on the frog paths.** -/
theorem invF_run (p : Params) (k : ℕ) (hk : 1 ≤ k) (ω : Option Frog × ℕ → Val) (n : ℕ) :
    InvF p.m k (fpPaths ω) (reads p k (Pool.poolSeq (sel p k) ω) n)
      (run p k (Pool.poolSeq (sel p k) ω) n) := by
  set y := Pool.poolSeq (sel p k) ω with hy
  induction n with
  | zero => exact invF_init p.m k hk (fpPaths ω)
  | succ n ih =>
    rw [reads_succ]
    refine invF_step p k (fpPaths ω) _ _ (y n) ih fun φ hφ => ?_
    have h := poolSeq_apply p k ω n
    rw [← hy, hφ] at h
    rw [h]
    rfl

/-- **Lemma 13.1 of the paper (domination).** On the frog paths, the count of M1_L after any
number of reads is at most `G_m(k)`. -/
theorem f1_gen (p : Params) (k : ℕ) (hk : 1 ≤ k) (ω : Option Frog × ℕ → Val) (n : ℕ) :
    (count (run p k (Pool.poolSeq (sel p k) ω) n) : ℕ∞) ≤ plantedG p.m k (fpPaths ω) := by
  obtain ⟨hnd, hW, hout, hch, hpos, -, -⟩ := invF_run p k hk ω n
  set s := run p k (Pool.poolSeq (sel p k) ω) n
  -- the frogs counted: distinct, woken, at `y`
  suffices h : ∃ l : List Frog, count s = l.length ∧ l.Nodup ∧
      ∀ φ ∈ l, Woken p.m k (fpPaths ω) φ ∧ ∃ i, pos (fpPaths ω) φ i = none by
    obtain ⟨l, hc, hl, hlW⟩ := h
    rw [hc, ← List.toFinset_card_of_nodup hl, ← Set.encard_coe_eq_coe_finsetCard, plantedG]
    refine Set.encard_le_encard fun φ hφ => ?_
    simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hφ
    exact hlW φ hφ
  by_cases hst : s.stack = []
  · refine ⟨s.out, by simp [count, hst], by simpa [heldS, hst] using hnd, fun φ hφ => ?_⟩
    exact ⟨hW φ (by simp [heldS, hst, hφ]), hout hst φ hφ⟩
  · obtain ⟨f, hf⟩ : ∃ f, s.stack.getLast? = some f := by
      cases h : s.stack.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h) hst
      | some f => exact ⟨f, rfl⟩
    have hmem : f ∈ s.stack := List.mem_of_getLast? hf
    have hv : f.v = [] := chainW_last _ hch f hf
    have hH : heldS s = s.stack.flatMap heldF := by simp [heldS, hst]
    have hsub : ∀ φ ∈ f.ups, φ ∈ heldS s := fun φ hφ => by
      rw [hH, List.mem_flatMap]
      exact ⟨f, hmem, by simp [heldF, hφ]⟩
    refine ⟨f.ups, by simp [count, hf], ?_, fun φ hφ => ⟨hW φ (hsub φ hφ), reads p k (Pool.poolSeq (sel p k) ω) n φ, ?_⟩⟩
    · rw [hH] at hnd
      exact ((List.nodup_flatMap.1 hnd).1 f hmem).sublist (List.sublist_append_right _ _)
    · rw [(hpos f hmem).1.2.2 φ hφ, hv]
      rfl

end FrogModel.D3
