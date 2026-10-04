module

public import FrogModel.D3.M1L.GenBasic
public import FrogModel.D3.M1L.GenFold

@[expose] public section

/-!
# M1_L at every height: auxiliary facts on the kill, the child types read from the marks, the
costs and a round
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.D3

/-- The kill is a law: its probabilities sum to one. -/
theorem killP_sum (V : ℕ) (κ : ℝ) (a g : ℕ) (ha : a ≤ V) (hg : g < 4) :
    ∑ b ∈ Finset.range (V + 1), ∑ f : Fin 4, killP κ a g b f = 1 := by
  unfold FrogModel.D3.killP
  simp only [Finset.sum_add_distrib]
  have ha_mem : a ∈ Finset.range (V + 1) := by
    rw [Finset.mem_range]
    omega
  have h0_mem : (0 : ℕ) ∈ Finset.range (V + 1) := by
    rw [Finset.mem_range]
    omega
  have hsum1 : ∑ b ∈ Finset.range (V + 1), ∑ f : Fin 4, (if a = b ∧ g = (f : ℕ) then κ else 0) = κ := by
    have h_inner : ∀ b, ∑ f : Fin 4, (if a = b ∧ g = (f : ℕ) then κ else 0) =
      (if a = b then κ else 0) := by
      intro b
      by_cases h_eq : a = b
      · subst h_eq
        have h_cases : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by omega
        rcases h_cases with (rfl|rfl|rfl|rfl)
        · simp [Fin.sum_univ_four]
        · simp [Fin.sum_univ_four]
        · simp [Fin.sum_univ_four]
        · simp [Fin.sum_univ_four]
      · simp [h_eq]
    simp_rw [h_inner]
    simp [ha_mem]
  have hsum2 : ∑ b ∈ Finset.range (V + 1), ∑ f : Fin 4, (if b = 0 ∧ (f : ℕ) = 0 then 1 - κ else 0) = 1 - κ := by
    have h_inner : ∀ b, ∑ f : Fin 4, (if b = 0 ∧ (f : ℕ) = 0 then 1 - κ else 0) =
      (if b = 0 then 1 - κ else 0) := by
      intro b
      by_cases hb : b = 0
      · subst hb
        simp
      · simp [hb]
    simp_rw [h_inner]
    simp [h0_mem]
  rw [hsum1, hsum2]
  ring

/-- The mean of a function after the kill. -/
theorem killP_mul_sum (V : ℕ) (κ : ℝ) (a g : ℕ) (ha : a ≤ V) (hg : g < 4)
    (Y : ℕ → Fin 4 → ℝ) :
    ∑ b ∈ Finset.range (V + 1), ∑ f : Fin 4, killP κ a g b f * Y b f =
      κ * Y a ⟨g, hg⟩ + (1 - κ) * Y 0 0 := by
  unfold FrogModel.D3.killP
  have ha_mem : a ∈ Finset.range (V + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ha
  have h0_mem : (0 : ℕ) ∈ Finset.range (V + 1) := by
    rw [Finset.mem_range]
    exact Nat.zero_lt_succ _
  -- Split the inner sum using sum_add_distrib, then the outer sum
  simp_rw [add_mul, Finset.sum_add_distrib]
  -- Goal: (∑ b, ∑ f, A b f) + (∑ b, ∑ f, B b f) = κ * Y a ⟨g, hg⟩ + (1 - κ) * Y 0 0
  -- where A b f = (if a = b ∧ g = ↑f then κ else 0) * Y b f
  -- and   B b f = (if b = 0 ∧ ↑f = 0 then 1 - κ else 0) * Y b f
  congr 1
  · -- First double sum = κ * Y a ⟨g, hg⟩
    -- Outer sum: only b = a contributes
    refine (Finset.sum_eq_single a ?_ ?_).trans ?_
    · intro b hb_mem hb_ne
      apply Finset.sum_eq_zero
      intro f hf
      have hne : a ≠ b := Ne.symm hb_ne
      simp [hne]
    · intro h_not_mem
      exfalso; exact h_not_mem ha_mem
    · -- Inner sum: only f = ⟨g, hg⟩ contributes
      refine (Finset.sum_eq_single (⟨g, hg⟩ : Fin 4) ?_ ?_).trans ?_
      · intro f hf_mem hf_ne
        -- hf_ne : f ≠ ⟨g, hg⟩
        -- Then g ≠ (f : ℕ), so the condition fails
        have h_ne : (f : ℕ) ≠ g := by
          intro h_eq
          apply hf_ne
          exact Fin.ext h_eq
        simp [h_ne.symm]
      · intro h_not_mem
        exfalso; apply h_not_mem; exact Finset.mem_univ _
      · simp
  · -- Second double sum = (1 - κ) * Y 0 0
    -- Outer sum: only b = 0 contributes
    refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
    · intro b hb_mem hb_ne
      apply Finset.sum_eq_zero
      intro f hf
      have hne : b ≠ 0 := hb_ne
      simp [hne]
    · intro h_not_mem
      exfalso; exact h_not_mem h0_mem
    · -- Inner sum: only f = 0 contributes
      refine (Finset.sum_eq_single (0 : Fin 4) ?_ ?_).trans ?_
      · intro f hf_mem hf_ne
        have h_ne : (f : ℕ) ≠ 0 := by
          intro h_eq
          apply hf_ne
          exact Fin.ext h_eq
        simp [h_ne]
      · intro h_not_mem
        exfalso; apply h_not_mem; exact Finset.mem_univ _
      · simp

/-- The kill probabilities are nonnegative. -/
theorem killP_nonneg (κ : ℝ) (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (a g b f : ℕ) :
    0 ≤ killP κ a g b f := by
  unfold FrogModel.D3.killP
  split_ifs with h1 h2
  · -- case: a = b ∧ g = f, and b = 0 ∧ f = 0
    linarith
  · -- case: a = b ∧ g = f, and ¬(b = 0 ∧ f = 0)
    linarith
  · -- case: ¬(a = b ∧ g = f), and b = 0 ∧ f = 0
    linarith
  · -- case: ¬(a = b ∧ g = f), and ¬(b = 0 ∧ f = 0)
    linarith

/-- Two children of `v` of which one is a suffix of the other are equal. -/
theorem suffix_cons_eq (m c : Fin 3) (v : Vertex 3) (h : (m :: v) <:+ (c :: v)) : m = c := by
  have heq : m :: v = c :: v := List.IsSuffix.eq_of_length h (by simp)
  exact ((List.cons.injEq m v c v).mp heq).left



/-- A child of `v` that is a suffix of a grandchild of `v` is its parent. -/
theorem suffix_cons2_eq (m c x : Fin 3) (v : Vertex 3) (h : (m :: v) <:+ (x :: c :: v)) :
    m = c := by
  rcases List.suffix_cons_iff.1 h with (h_eq | h_suf)
  · -- h_eq : m :: v = x :: c :: v, impossible: the lengths differ
    have h_len := congrArg List.length h_eq
    simp [List.length_cons] at h_len
  · -- h_suf : m :: v <:+ c :: v
    have h_eq' : m :: v = c :: v := List.IsSuffix.eq_of_length h_suf (by simp)
    exact (List.cons.injEq _ _ _ _).mp h_eq' |>.left



/-- The masked child types do not see marks in the subtree of the masked child. -/
theorem kidM_congr (p : Params) (marks marks' : Finset (Vertex 3)) (v : Vertex 3)
    (m : Fin 3) (hM : ∀ w, (w ∈ marks' ↔ w ∈ marks) ∨ (m :: v) <:+ w) :
    kidM p marks' v (some m) = kidM p marks v (some m) := by
  apply funext
  intro c
  unfold kidM
  by_cases h0 : p.m - v.length = 0
  · simp [h0]
  · by_cases h_eq : (some m : Option (Fin 3)) = some c
    · simp [h_eq]
    · simp [h0, h_eq]
      have hM_cv := hM (c :: v)
      by_cases hmem : c :: v ∈ marks'
      · -- hmem : c :: v ∈ marks'
        have hmem_mark : c :: v ∈ marks := by
          rcases hM_cv with (hM_cv | hM_cv)
          · exact hM_cv.mp hmem
          · -- hM_cv : m :: v <:+ c :: v → m = c, contradicting h_eq
            have h_eq' : m = c := by
              have h' := (List.mem_tails (m :: v) (c :: v)).mpr hM_cv
              rw [List.tails_cons] at h'
              simp at h'
              rcases h' with (h' | h')
              · exact h'
              · rcases h' with ⟨t, ht⟩
                have hlen : v.length < (t ++ (m :: v)).length := by
                  calc
                    v.length < (m :: v).length := by simp
                    _ ≤ (t ++ (m :: v)).length := by
                      rw [List.length_append]
                      omega
                rw [ht] at hlen
                exact absurd hlen (lt_irrefl _)
            exfalso
            apply h_eq
            simp [h_eq']
        simp [hmem, hmem_mark]
        by_cases h1 : p.m - v.length = 1
        · simp [h1]
        · simp [h1]
          -- goal: unmarked marks' (c :: v) = unmarked marks (c :: v)
          dsimp [unmarked]
          -- goal: (Finset.univ.filter fun c' => c' :: c :: v ∉ marks').card = (Finset.univ.filter fun c' => c' :: c :: v ∉ marks).card
          apply congrArg Finset.card
          apply Finset.filter_congr
          intro c'' hc''
          have hM_c''cv := hM (c'' :: c :: v)
          rcases hM_c''cv with (hM_c''cv | hM_c''cv)
          · simpa using (not_iff_not.mpr hM_c''cv)
          · -- hM_c''cv : m :: v <:+ c'' :: c :: v → m = c, contradicting h_eq
            have h_eq' : m = c := by
              have h' := (List.mem_tails (m :: v) (c'' :: c :: v)).mpr hM_c''cv
              rw [List.tails_cons] at h'
              simp at h'
              rcases h' with (h' | h')
              · exact h'
              · rcases h' with ⟨t, ht⟩
                have hlen : v.length < (t ++ (m :: v)).length := by
                  calc
                    v.length < (m :: v).length := by simp
                    _ ≤ (t ++ (m :: v)).length := by
                      rw [List.length_append]
                      omega
                rw [ht] at hlen
                exact absurd hlen (lt_irrefl _)
            exfalso
            apply h_eq
            simp [h_eq']
      · -- hmem : c :: v ∉ marks'
        have hmem_mark : c :: v ∉ marks := by
          rcases hM_cv with (hM_cv | hM_cv)
          · exact mt (hM_cv.mpr) hmem
          · -- hM_cv : m :: v <:+ c :: v → m = c, contradicting h_eq
            have h_eq' : m = c := by
              have h' := (List.mem_tails (m :: v) (c :: v)).mpr hM_cv
              rw [List.tails_cons] at h'
              simp at h'
              rcases h' with (h' | h')
              · exact h'
              · rcases h' with ⟨t, ht⟩
                have hlen : v.length < (t ++ (m :: v)).length := by
                  calc
                    v.length < (m :: v).length := by simp
                    _ ≤ (t ++ (m :: v)).length := by
                      rw [List.length_append]
                      omega
                rw [ht] at hlen
                exact absurd hlen (lt_irrefl _)
            exfalso
            apply h_eq
            simp [h_eq']
        simp [hmem, hmem_mark]

/-- The parent's child types right after an R entry into `c`: the entered child is masked. -/
theorem kidM_push (p : Params) (marks : Finset (Vertex 3)) (v : Vertex 3) (c : Fin 3)
    (hv : p.m - v.length ≠ 0) :
    kidM p (insert (c :: v) marks) v (some c) =
      Function.update (kidM p marks v none) c none := by
  funext c'
  simp only [kidM, Function.update_apply]
  by_cases h0 : p.m - v.length = 0
  · exact (hv h0).elim
  · -- h0: p.m - v.length ≠ 0
    simp [h0]
    -- goal: (if c = c' then none else if ¬c' = c ∧ c' :: v ∉ marks then none else ...) = (if c' = c then none else if c' :: v ∈ marks then ... else none)
    by_cases hc_eq : c' = c
    · subst hc_eq; simp
    · have hc_ne : c ≠ c' := Ne.symm hc_eq
      simp [hc_eq, hc_ne]
      -- goal: (if c' :: v ∉ marks then none else if p.m - v.length = 1 then some 0 else ...) = (if c' :: v ∈ marks then if p.m - v.length = 1 then some 0 else ... else none)
      by_cases hm : c' :: v ∈ marks
      · simp [hm]
        -- goal: (if p.m - v.length = 1 then some 0 else ...) = (if p.m - v.length = 1 then some 0 else ...)
        by_cases h1 : p.m - v.length = 1
        · simp [h1]
        · simp [h1]
          -- goal: unmarked (insert (c :: v) marks) (c' :: v) = unmarked marks (c' :: v)
          unfold unmarked
          apply congrArg Finset.card
          apply Finset.filter_congr
          intro c'' _
          have hne : c'' :: (c' :: v) ≠ c :: v := by
            intro h_eq
            have hlen := congrArg List.length h_eq
            simp only [List.length_cons] at hlen
            omega
          simp [Finset.mem_insert, hne]
      · simp [hm]

/-- Masking a child is updating it to `none`, at a height `≥ 1`. -/
theorem kidM_mask (p : Params) (marks : Finset (Vertex 3)) (v : Vertex 3) (c : Fin 3)
    (hv : p.m - v.length ≠ 0) :
    kidM p marks v (some c) = Function.update (kidM p marks v none) c none := by
  ext c'
  unfold FrogModel.D3.kidM
  simp [hv, Function.update_apply]
  by_cases h : c' = c
  · subst h
    simp
  · intro hmem heq
    exact ⟨Ne.symm, Ne.symm⟩

/-- A fresh R closure at an unmarked vertex sees its three children unmarked. -/
theorem kidM_fresh (p : Params) (marks : Finset (Vertex 3))
    (hM : MarksAnc marks) (z : Vertex 3) (hz : z ≠ []) (hzm : z ∉ marks) :
    kidM p (insert z marks) z none = initK (p.m - z.length) := by
  funext c
  unfold FrogModel.D3.kidM FrogModel.D3.initK
  by_cases h : p.m - z.length = 0
  · simp [h]
  · have h_not_mem : c :: z ∉ insert z marks := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with (heq | hmem')
      · exact List.cons_ne_self c z heq
      · rcases hM (c :: z) hmem' with ⟨_, htail'⟩
        have htail_eq : (c :: z).tail = z := by simp
        have hz_in_marks : z ∈ marks := htail' (by simpa [htail_eq] using hz)
        exact hzm hz_in_marks
    simp [h, h_not_mem]

/-- The count of unmarked children read by the keep function. -/
theorem nN_kidM (p : Params) (marks : Finset (Vertex 3)) (v : Vertex 3)
    (hv : p.m - v.length ≠ 0) :
    nN (kidM p marks v none) = unmarked marks v := by
  unfold FrogModel.D3.nN FrogModel.D3.unmarked FrogModel.D3.kidM
  congr 1
  ext c
  simp
  split_ifs with h0 hmask hnotmark
  · exfalso; exact hv h0
  · simp [hmask]
  · simp [hmask]
  · simp [hmask]



/-- At height `0` the count of unmarked children is `0`. -/
theorem nN_kidM_zero (p : Params) (marks : Finset (Vertex 3)) (v : Vertex 3)
    (msk : Option (Fin 3)) (hv : p.m - v.length = 0) : nN (kidM p marks v msk) = 0 := by
  simp [nN, kidM, hv]

/-- The parent's child types after its child at `c` ends and is kept. -/
theorem kidM_pop_kept (p : Params) (marks : Finset (Vertex 3)) (g : Vertex 3) (c : Fin 3)
    (hg : p.m - g.length ≠ 0) (hc : c :: g ∈ marks)
    (hlt : nN (kidM p marks (c :: g) none) < 4) :
    kidM p marks g none = Function.update (kidM p marks g (some c)) c
      (some ⟨nN (kidM p marks (c :: g) none), hlt⟩) := by
  apply funext
  intro i
  simp only [Function.update_apply]
  by_cases hi : i = c
  · simp [hi]
    by_cases hlen1 : p.m - g.length = 1
    · -- p.m - g.length = 1 → left side is some 0, and nN = 0
      have hlen0 : p.m - (c :: g).length = 0 := by
        have : (c :: g).length = g.length + 1 := by simp
        omega
      -- compute nN of kidM at (c::g) with mask none: all children are some 0, so nN = 0
      have hnN : FrogModel.D3.nN (FrogModel.D3.kidM p marks (c :: g) none) = 0 := by
        unfold FrogModel.D3.nN FrogModel.D3.kidM
        rw [Finset.card_eq_zero]
        apply Finset.filter_eq_empty_iff.mpr
        intro x hx
        have hlen0' : p.m - (List.length g + 1) = 0 := by simpa [List.length_cons] using hlen0
        simp [hlen0']
      -- now compute both sides of the goal
      have hleft : FrogModel.D3.kidM p marks g none c = some 0 := by
        unfold FrogModel.D3.kidM
        simp [hc, hlen1]
      have hright : some (⟨FrogModel.D3.nN (FrogModel.D3.kidM p marks (c :: g) none), hlt⟩ : Fin 4) = some 0 := by
        simp [hnN]
      simp [hleft, hright]
    · -- p.m - g.length ≠ 1
      have hnN : FrogModel.D3.nN (FrogModel.D3.kidM p marks (c :: g) none) =
          FrogModel.D3.unmarked marks (c :: g) :=
        FrogModel.D3.nN_kidM p marks (c :: g) (by
          intro hzero
          apply hlen1
          have : (c :: g).length = g.length + 1 := by simp
          omega)
      have hleft : FrogModel.D3.kidM p marks g none c =
          some (⟨FrogModel.D3.unmarked marks (c :: g), FrogModel.D3.unmarked_lt marks (c :: g)⟩ : Fin 4) := by
        unfold FrogModel.D3.kidM
        simp [hg, hc, hlen1]
      have hright : some (⟨FrogModel.D3.nN (FrogModel.D3.kidM p marks (c :: g) none), hlt⟩ : Fin 4) =
          some (⟨FrogModel.D3.unmarked marks (c :: g), FrogModel.D3.unmarked_lt marks (c :: g)⟩ : Fin 4) := by
        simp [hnN]
      simp [hleft, hright]
  · -- i ≠ c: both sides are equal because the mask some c doesn't match i
    by_cases hzero : p.m - g.length = 0
    · -- p.m - g.length = 0: both sides are some 0
      unfold FrogModel.D3.kidM
      simp [hzero, hi]
    · -- p.m - g.length ≠ 0: the mask some c doesn't match i
      unfold FrogModel.D3.kidM
      simp [hzero]
      -- Now: (if i :: g ∉ marks then none else ...) = (if i = c then ... else (if some c = some i then none else ...))
      -- But wait, none = some i is always false, so it's simplified away
      by_cases hmem : i :: g ∈ marks
      · -- hmem: i :: g ∈ marks
        simp [hmem]
        by_cases h1 : p.m - g.length = 1
        · simp [h1, hi, Ne.symm hi]
        · simp [h1, hi, Ne.symm hi]
      · -- hmem: i :: g ∉ marks
        simp [hmem, hi]

/-- The parent's child types after its child at `c` ends and is killed. -/
theorem kidM_pop_killed (p : Params) (marks : Finset (Vertex 3)) (g : Vertex 3) (c : Fin 3)
    (hg : p.m - g.length ≠ 0) (hc : c :: g ∈ marks) :
    kidM p (marks ∪ kids (c :: g)) g none =
      Function.update (kidM p marks g (some c)) c (some 0) := by
  have hmem : ∀ i : Fin 3, i ≠ c → (i :: g ∈ marks ∪ kids (c :: g) ↔ i :: g ∈ marks) := by
    intro i hi
    simp only [Finset.mem_union, kids, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (h | ⟨x, hx⟩)
      · exact h
      · exact absurd (congrArg List.length hx) (by simp)
    · exact Or.inl
  have hun : ∀ i : Fin 3, i ≠ c →
      unmarked (marks ∪ kids (c :: g)) (i :: g) = unmarked marks (i :: g) := by
    intro i hi
    unfold unmarked
    congr 1
    apply Finset.filter_congr
    intro j _
    simp only [Finset.mem_union, kids, Finset.mem_image, Finset.mem_univ, true_and, not_or]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rintro ⟨x, hx⟩
      simp only [List.cons.injEq] at hx
      exact hi hx.2.1.symm
  funext i
  rw [Function.update_apply]
  by_cases hi : i = c
  · subst hi
    rw [ite_eq_left rfl]
    unfold kidM
    have hc2 : i :: g ∈ marks ∪ kids (i :: g) := Finset.mem_union_left _ hc
    simp only [hg, ↓reduceIte, hc2, not_true_eq_false, reduceCtorEq]
    split_ifs with h1
    · rfl
    · have h0 : unmarked (marks ∪ kids (i :: g)) (i :: g) = 0 := by
        unfold unmarked
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _
        simp [kids]
      simp [h0]
  · rw [ite_eq_right hi]
    unfold kidM
    have hne : ¬(some c = some i) := by simpa using Ne.symm hi
    simp only [hg, ↓reduceIte, hmem i hi, hun i hi, hne, reduceCtorEq]

/-- At most three unmarked children. -/
theorem nN_lt (k : Kid) : nN k < 4 := by
  unfold FrogModel.D3.nN
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin 3)) fun c => k c = none
  have huniv : (Finset.univ : Finset (Fin 3)).card = 3 :=
    Finset.card_fin 3
  omega

/-- The count of a fresh R closure. -/
theorem nN_initK (h : ℕ) : nN (initK h) = if h = 0 then 0 else 3 := by
  unfold FrogModel.D3.nN FrogModel.D3.initK
  by_cases h0 : h = 0
  · subst h0
    simp
  · simp [h0]

/-- The count of the representative child types of an H closure. -/
theorem nN_kidOf (h t : ℕ) (ht : t ≤ 3) :
    nN (kidOf h t) = if h = 0 then 0 else t := by
  unfold FrogModel.D3.nN FrogModel.D3.kidOf
  by_cases h0 : h = 0
  · simp [h0]
  · simp [h0]
    interval_cases t <;> decide

/-- The additive term of an H closure depends on its child types through their count only. -/
theorem addC_H (p : Params) (c : ℝ) (h : ℕ) (τ : ℝ × (ℕ → ℝ)) (k : Kid) :
    addC p c h false τ k =
      c + ((nN k : ℝ) * τ.1 + (3 - (nN k : ℝ)) * (c * gcost p.L 1)) / 4 := by
  unfold FrogModel.D3.addC
  have hisRe : FrogModel.D3.isRe h false = false := by
    simp [FrogModel.D3.isRe]
  simp [hisRe, Fin.sum_univ_three]
  cases hk0 : k 0 <;> cases hk1 : k 1 <;> cases hk2 : k 2
  · -- all none, nN = 3
    simp
    have hnN : FrogModel.D3.nN k = 3 := by
      unfold FrogModel.D3.nN
      have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [huniv]
      have hfilter : (Finset.filter (fun c => k c = none) {0, 1, 2}) = {0, 1, 2} := by
        ext c
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        fin_cases c <;> simp [hk0, hk1, hk2]
      rw [hfilter]
      decide
    simp [hnN]
    ring
  · -- 0,1 none; 2 some, nN = 2
    simp
    have hnN : FrogModel.D3.nN k = 2 := by
      unfold FrogModel.D3.nN
      have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [huniv]
      have hfilter : (Finset.filter (fun c => k c = none) {0, 1, 2}) = {0, 1} := by
        ext c
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        fin_cases c <;> simp [hk0, hk1, hk2]
      rw [hfilter]
      decide
    simp [hnN]
    ring
  · -- 0 none; 1 some; 2 none, nN = 2
    simp
    have hnN : FrogModel.D3.nN k = 2 := by
      unfold FrogModel.D3.nN
      have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [huniv]
      have hfilter : (Finset.filter (fun c => k c = none) {0, 1, 2}) = {0, 2} := by
        ext c
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        fin_cases c <;> simp [hk0, hk1, hk2]
      rw [hfilter]
      decide
    simp [hnN]
    ring
  · -- 0 none; 1,2 some, nN = 1
    simp
    have hnN : FrogModel.D3.nN k = 1 := by
      unfold FrogModel.D3.nN
      have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [huniv]
      have hfilter : (Finset.filter (fun c => k c = none) {0, 1, 2}) = {0} := by
        ext c
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        fin_cases c <;> simp [hk0, hk1, hk2]
      rw [hfilter]
      decide
    simp [hnN]
    ring
  · -- 0 some; 1,2 none, nN = 2
    simp
    have hnN : FrogModel.D3.nN k = 2 := by
      unfold FrogModel.D3.nN
      have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [huniv]
      have hfilter : (Finset.filter (fun c => k c = none) {0, 1, 2}) = {1, 2} := by
        ext c
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        fin_cases c <;> simp [hk0, hk1, hk2]
      rw [hfilter]
      decide
    simp [hnN]
    ring
  · -- 0 some; 1 none; 2 some, nN = 1
    simp
    have hnN : FrogModel.D3.nN k = 1 := by
      unfold FrogModel.D3.nN
      have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [huniv]
      have hfilter : (Finset.filter (fun c => k c = none) {0, 1, 2}) = {1} := by
        ext c
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        fin_cases c <;> simp [hk0, hk1, hk2]
      rw [hfilter]
      decide
    simp [hnN]
    ring
  · -- 0,1 some; 2 none, nN = 1
    simp
    have hnN : FrogModel.D3.nN k = 1 := by
      unfold FrogModel.D3.nN
      have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [huniv]
      have hfilter : (Finset.filter (fun c => k c = none) {0, 1, 2}) = {2} := by
        ext c
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        fin_cases c <;> simp [hk0, hk1, hk2]
      rw [hfilter]
      decide
    simp [hnN]
    ring
  · -- all some, nN = 0
    simp
    have hnN : FrogModel.D3.nN k = 0 := by
      unfold FrogModel.D3.nN
      have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [huniv]
      have hfilter : (Finset.filter (fun c => k c = none) {0, 1, 2}) = ∅ := by
        ext c
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        fin_cases c <;> simp [hk0, hk1, hk2]
      rw [hfilter]
      decide
    simp [hnN]
    ring

/-- With cost `0` per read every cost is `0`. -/
theorem costs_zero (p : Params) (h : ℕ) :
    costs p 0 h = (0, fun _ => 0) := by
  induction' h with h ih
  · -- h = 0
    unfold FrogModel.D3.costs FrogModel.D3.costsAt FrogModel.D3.GenH
    have h_addC_true : FrogModel.D3.addC p 0 0 true (0, fun _ => (0 : ℝ)) = fun (_ : Kid) => (0 : ℝ) := by
      ext k
      unfold FrogModel.D3.addC
      simp [FrogModel.D3.isRe]
      apply Finset.sum_eq_zero
      intro x hx
      cases k x <;> simp
    have h_addC_false : FrogModel.D3.addC p 0 0 false (0, fun _ => (0 : ℝ)) = fun (_ : Kid) => (0 : ℝ) := by
      ext k
      unfold FrogModel.D3.addC
      simp [FrogModel.D3.isRe]
      apply Finset.sum_eq_zero
      intro x hx
      cases k x <;> simp
    rw [h_addC_true, h_addC_false]
    have h_gen_true : Gen p.V p.P (isRe 0 true) (pL p.L) (FrogModel.D3.inp p 0).1 (FrogModel.D3.inp p 0).2
        (fun (_ : Kid) => (0 : ℝ)) (fun (_ : Kid) (_ : ℕ) => (0 : ℝ)) (FrogModel.D3.initK 0) 2 0 = 0 := by
      apply FrogModel.D3.Gen_zero_zero
    have h_gen_false : ∀ t, Gen p.V p.P (isRe 0 false) (pL p.L) (FrogModel.D3.inp p 0).1 (FrogModel.D3.inp p 0).2
        (fun (_ : Kid) => (0 : ℝ)) (fun (_ : Kid) (_ : ℕ) => (0 : ℝ)) (FrogModel.D3.kidOf 0 t) 1 0 = 0 := by
      intro t
      apply FrogModel.D3.Gen_zero_zero
    rw [h_gen_true]
    have h_pair : ((0 : ℝ), fun t => Gen p.V p.P (isRe 0 false) (pL p.L) (FrogModel.D3.inp p 0).1 (FrogModel.D3.inp p 0).2
        (fun (_ : Kid) => (0 : ℝ)) (fun (_ : Kid) (_ : ℕ) => (0 : ℝ)) (FrogModel.D3.kidOf 0 t) 1 0) = ((0 : ℝ), fun _ => (0 : ℝ)) := by
      ext <;> simp [h_gen_false]
    exact h_pair
  · -- h = h.succ
    unfold FrogModel.D3.costs
    rw [ih]
    unfold FrogModel.D3.costsAt FrogModel.D3.GenH
    have h_addC_true : FrogModel.D3.addC p 0 (Nat.succ h) true (0, fun _ => (0 : ℝ)) = fun (_ : Kid) => (0 : ℝ) := by
      ext k
      unfold FrogModel.D3.addC
      simp [FrogModel.D3.isRe]
      apply Finset.sum_eq_zero
      intro x hx
      cases k x <;> simp
    have h_addC_false : FrogModel.D3.addC p 0 (Nat.succ h) false (0, fun _ => (0 : ℝ)) = fun (_ : Kid) => (0 : ℝ) := by
      ext k
      unfold FrogModel.D3.addC
      simp [FrogModel.D3.isRe]
      apply Finset.sum_eq_zero
      intro x hx
      cases k x <;> simp
    rw [h_addC_true, h_addC_false]
    have h_gen_true : Gen p.V p.P (isRe (Nat.succ h) true) (pL p.L) (FrogModel.D3.inp p (Nat.succ h)).1 (FrogModel.D3.inp p (Nat.succ h)).2
        (fun (_ : Kid) => (0 : ℝ)) (fun (_ : Kid) (_ : ℕ) => (0 : ℝ)) (FrogModel.D3.initK (Nat.succ h)) 2 0 = 0 := by
      apply FrogModel.D3.Gen_zero_zero
    have h_gen_false : ∀ t, Gen p.V p.P (isRe (Nat.succ h) false) (pL p.L) (FrogModel.D3.inp p (Nat.succ h)).1 (FrogModel.D3.inp p (Nat.succ h)).2
        (fun (_ : Kid) => (0 : ℝ)) (fun (_ : Kid) (_ : ℕ) => (0 : ℝ)) (FrogModel.D3.kidOf (Nat.succ h) t) 1 0 = 0 := by
      intro t
      apply FrogModel.D3.Gen_zero_zero
    rw [h_gen_true]
    have h_pair : ((0 : ℝ), fun t => Gen p.V p.P (isRe (Nat.succ h) false) (pL p.L) (FrogModel.D3.inp p (Nat.succ h)).1 (FrogModel.D3.inp p (Nat.succ h)).2
        (fun (_ : Kid) => (0 : ℝ)) (fun (_ : Kid) (_ : ℕ) => (0 : ℝ)) (FrogModel.D3.kidOf (Nat.succ h) t) 1 0) = ((0 : ℝ), fun _ => (0 : ℝ)) := by
      ext <;> simp [h_gen_false]
    exact h_pair

/-- The machine reads only the direction and the coin of a value. -/
theorem upd_dc (p : Params) (s : St) (x : Val) :
    upd p s x = upd p s ((0, x.1.2), x.2) := by
  rcases s with ⟨stack, marks, out⟩
  simp [FrogModel.D3.upd, FrogModel.D3.ghostStep]

/-- The machine states form a countable type. -/
theorem countable_St : Countable St := by
  let frameToTuple : Frame →
      Vertex 3 × Bool × ℕ × List Frog × List Frog × Option (Frog × Vertex 3) × Bool :=
    fun fr => (fr.v, fr.isR, fr.f0, fr.pool, fr.ups, fr.ghost, fr.killing)
  let β := (List (Vertex 3 × Bool × ℕ × List Frog × List Frog × Option (Frog × Vertex 3) × Bool)) ×
    (Finset (Vertex 3)) × (List Frog)
  have h_countable : Countable β := by infer_instance
  let f : St → β := fun s => (s.stack.map frameToTuple, s.marks, s.out)
  have hf : Function.Injective f := by
    intro a b h
    have h_stack_map : a.stack.map frameToTuple = b.stack.map frameToTuple := by
      have := congrArg (fun x => x.1) h; exact this
    have h_marks : a.marks = b.marks := by
      have := congrArg (fun x => x.2.1) h; exact this
    have h_out : a.out = b.out := by
      have := congrArg (fun x => x.2.2) h; exact this
    have h_frame_inj : Function.Injective frameToTuple := by
      intro x y hxy
      have hv : x.v = y.v := by
        have := congrArg (fun z => z.1) hxy; exact this
      have hisR : x.isR = y.isR := by
        have := congrArg (fun z => z.2.1) hxy; exact this
      have hf0 : x.f0 = y.f0 := by
        have := congrArg (fun z => z.2.2.1) hxy; exact this
      have hpool : x.pool = y.pool := by
        have := congrArg (fun z => z.2.2.2.1) hxy; exact this
      have hup : x.ups = y.ups := by
        have := congrArg (fun z => z.2.2.2.2.1) hxy; exact this
      have hghost : x.ghost = y.ghost := by
        have := congrArg (fun z => z.2.2.2.2.2.1) hxy; exact this
      have hkilling : x.killing = y.killing := by
        have := congrArg (fun z => z.2.2.2.2.2.2) hxy; exact this
      cases x; cases y
      simp at hv hisR hf0 hpool hup hghost hkilling
      simp [hv, hisR, hf0, hpool, hup, hghost, hkilling]
    have h_stack_inj : Function.Injective (List.map frameToTuple) :=
      (List.map_injective_iff.mpr h_frame_inj)
    have h_stack : a.stack = b.stack :=
      h_stack_inj h_stack_map
    cases a; cases b
    simp at h_stack h_marks h_out
    simp [h_stack, h_marks, h_out]
  exact Function.Injective.countable hf

/-- After a kill at `v` every child of `v` is marked. -/
theorem unmarked_union_kids (marks : Finset (Vertex 3)) (v : Vertex 3) :
    unmarked (marks ∪ kids v) v = 0 := by
  unfold FrogModel.D3.unmarked FrogModel.D3.kids
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro c _
  simp

/-- The return probability of a ghost walk is a probability. -/
theorem pL_mem (L : ℕ) (hL : 1 ≤ L) : 0 ≤ pL L ∧ pL L ≤ 1 := by
  have hLpos : L ≠ 0 := by omega
  have h3pos : (1 : ℝ) < (3 : ℝ) := by norm_num
  have h3one : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
  have h_den_pos : 0 < (3 : ℝ) ^ L - 1 := by
    have h : 1 < (3 : ℝ) ^ L := one_lt_pow₀ h3pos hLpos
    linarith
  have h_num_nonneg : 0 ≤ (3 : ℝ) ^ (L - 1) - 1 := by
    have h : 1 ≤ (3 : ℝ) ^ (L - 1) := one_le_pow₀ h3one
    linarith
  have h_den_nonneg : 0 ≤ (3 : ℝ) ^ L - 1 := by linarith
  have h_num_le_den : (3 : ℝ) ^ (L - 1) - 1 ≤ (3 : ℝ) ^ L - 1 := by
    have h_le : L - 1 ≤ L := Nat.sub_le _ _
    have h_pow : (3 : ℝ) ^ (L - 1) ≤ (3 : ℝ) ^ L := pow_le_pow_right₀ h3one h_le
    linarith
  have h_nonneg : 0 ≤ FrogModel.D3.pL L := by
    unfold FrogModel.D3.pL
    exact div_nonneg h_num_nonneg h_den_nonneg
  have h_le_one : FrogModel.D3.pL L ≤ 1 := by
    unfold FrogModel.D3.pL
    rw [div_le_one h_den_pos]
    exact h_num_le_den
  exact And.intro h_nonneg h_le_one



/-- A round of a closure: the up, then each child with its entry cost and its loop. -/
theorem round_id (p : Params) (hL : 1 ≤ p.L) (c : ℝ) (h : ℕ) (r : Bool)
    (T : Kid → ℕ → ℝ) (hK0 : ∀ t : ℕ, 0 ≤ (inp p h).2 t 1 t)
    (hK1 : ∀ t : ℕ, (inp p h).2 t 1 t ≤ 1) (k : Kid) (n a : ℕ) (hn : n ≠ 0) :
    GenH p h r (inp p h) (addC p c h r (cinp p c h)) T k n a =
      c + 1 / 4 * GenH p h r (inp p h) (addC p c h r (cinp p c h)) T
          k (n - 1) (upA p.V a) +
        ∑ c', 1 / 4 * childV p c h r T k n a c' := by
  have h_one_le_three_pow : ∀ n : ℕ, (1 : ℝ) ≤ (3 : ℝ) ^ n := by
    intro n
    have h : (1 : ℕ) ≤ (3 : ℕ) ^ n := Nat.one_le_pow n 3 (by norm_num)
    exact_mod_cast h
  have hp0 : 0 ≤ FrogModel.D3.pL p.L := by
    unfold FrogModel.D3.pL
    have hnum : 0 ≤ (3 : ℝ) ^ (p.L - 1) - 1 := by
      have h : (1 : ℝ) ≤ (3 : ℝ) ^ (p.L - 1) := h_one_le_three_pow (p.L - 1)
      linarith
    have hden : 0 ≤ (3 : ℝ) ^ p.L - 1 := by
      have h : (1 : ℝ) ≤ (3 : ℝ) ^ p.L := h_one_le_three_pow p.L
      linarith
    exact div_nonneg hnum hden
  have hp1 : FrogModel.D3.pL p.L ≤ 1 := by
    unfold FrogModel.D3.pL
    have hnum : (3 : ℝ) ^ (p.L - 1) - 1 ≤ (3 : ℝ) ^ p.L - 1 := by
      have hpow : (3 : ℝ) ^ (p.L - 1) ≤ (3 : ℝ) ^ p.L := by
        have h_exp : p.L - 1 ≤ p.L := Nat.sub_le _ _
        have h_nat : (3 : ℕ) ^ (p.L - 1) ≤ (3 : ℕ) ^ p.L :=
          Nat.pow_le_pow_right (by norm_num) h_exp
        exact_mod_cast h_nat
      linarith
    have hden_pos : 0 < (3 : ℝ) ^ p.L - 1 := by
      have h : (1 : ℝ) < (3 : ℝ) ^ p.L := by
        have h_one : (1 : ℝ) < (3 : ℝ) ^ 1 := by norm_num
        have h_nat : (3 : ℕ) ^ 1 ≤ (3 : ℕ) ^ p.L :=
          Nat.pow_le_pow_right (by norm_num) hL
        have hpow_le : (3 : ℝ) ^ 1 ≤ (3 : ℝ) ^ p.L := by exact_mod_cast h_nat
        linarith
      linarith
    exact (div_le_one (by linarith)).mpr hnum
  have hGen_eq := FrogModel.D3.Gen_eq p.V p.P (FrogModel.D3.isRe h r) (FrogModel.D3.pL p.L)
    (FrogModel.D3.inp p h).1 (FrogModel.D3.inp p h).2 (FrogModel.D3.addC p c h r (FrogModel.D3.cinp p c h)) T
    hp0 hp1 hK0 hK1 k n a hn
  -- hGen_eq is about `Gen`, but goal uses `GenH`. Unfold GenH.
  unfold FrogModel.D3.GenH
  -- Now goal: Gen ... k n a = c + 1/4 * Gen ... k (n-1) (upA ...) + ∑ c', 1/4 * childV ... c'
  -- Use hGen_eq to rewrite LHS
  rw [hGen_eq]
  -- Now goal: addC ... k + 1/4 * Gen ... (n-1) (upA ...) + ∑ c', 1/4 * bodyG ... c' + loopK * Gen ... k n a
  --   = c + 1/4 * Gen ... k (n-1) (upA ...) + ∑ c', 1/4 * childV ... c'
  -- Cancel 1/4 * Gen ... (n-1) (upA ...) from both sides (it appears on both)
  -- So we need: addC ... k + ∑ c', 1/4 * bodyG ... c' + loopK * Gen ... k n a = c + ∑ c', 1/4 * childV ... c'
  -- Unfold addC, childV, loopK and do algebra
  simp only [FrogModel.D3.addC, FrogModel.D3.childV, FrogModel.D3.loopK]
  simp only [Fin.sum_univ_three]
  have hk0 := k 0; have hk1 := k 1; have hk2 := k 2
  cases hk0 : k 0 with
  | none =>
    cases hk1 : k 1 with
    | none =>
      cases hk2 : k 2 with
      | none =>
        -- All none: simplify GenH and use ring
        simp [FrogModel.D3.GenH]
        ring
      | some t2 =>
        simp [FrogModel.D3.GenH]
        split_ifs <;> ring
    | some t1 =>
      cases hk2 : k 2 with
      | none =>
        simp [FrogModel.D3.GenH]
        split_ifs <;> ring
      | some t2 =>
        simp [FrogModel.D3.GenH]
        split_ifs <;> ring
  | some t0 =>
    cases hk1 : k 1 with
    | none =>
      cases hk2 : k 2 with
      | none =>
        simp [FrogModel.D3.GenH]
        split_ifs <;> ring
      | some t2 =>
        simp [FrogModel.D3.GenH]
        split_ifs <;> ring
    | some t1 =>
      cases hk2 : k 2 with
      | none =>
        simp [FrogModel.D3.GenH]
        split_ifs <;> ring
      | some t2 =>
        simp [FrogModel.D3.GenH]
        split_ifs <;> ring

/-- The representative child types of an H closure have at most `t` unmarked children. -/
theorem nN_kidOf_le (h t : ℕ) : nN (kidOf h t) ≤ t := by
  by_cases ht : t ≤ 3
  · rw [nN_kidOf h t ht]
    split_ifs <;> omega
  · have := nN_lt (kidOf h t)
    omega

/-- The mean of a function of the outcome of an H entry from `U_t`, split by the support of `K`:
the lost frog `(0, t)`, the loop `(1, t)` and the outcomes that lower the type. -/
theorem K_split (V : ℕ) (hV : 1 ≤ V) (K : ℕ → ℕ → ℕ → ℝ) (t : Fin 4)
    (hf : ∀ (a : ℕ) (f : Fin 4), t < f → K t a f = 0) (ha : ∀ a : ℕ, 2 ≤ a → K t a t = 0)
    (Y : ℕ → Fin 4 → ℝ) :
    ∑ b ∈ Finset.range (V + 1), ∑ f : Fin 4, K t b f * Y b f =
      K t 0 t * Y 0 t + K t 1 t * Y 1 t +
        ∑ f : Fin 4, (if f < t then ∑ b ∈ Finset.range (V + 1), K t b f * Y b f else 0) := by
  have hcol : ∀ f : Fin 4, ∑ b ∈ Finset.range (V + 1), K t b f * Y b f =
      (if f = t then K t 0 t * Y 0 t + K t 1 t * Y 1 t else 0) +
        (if f < t then ∑ b ∈ Finset.range (V + 1), K t b f * Y b f else 0) := by
    intro f
    rcases lt_trichotomy f t with hlt | rfl | hgt
    · rw [ite_eq_right (ne_of_lt hlt), ite_eq_left hlt, zero_add]
    · rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _), add_zero,
        show V + 1 = (V - 1) + 1 + 1 by omega, Finset.sum_range_succ', Finset.sum_range_succ',
        Finset.sum_eq_zero fun b _ => by rw [ha (b + 1 + 1) (by omega), zero_mul]]
      simp only [zero_add]
      ring
    · rw [ite_eq_right (ne_of_gt hgt), ite_eq_right (not_lt.mpr hgt.le), add_zero]
      exact Finset.sum_eq_zero fun b _ => by rw [hf b f hgt, zero_mul]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun f _ => hcol f, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ t, ite_eq_left (Finset.mem_univ _)]

end FrogModel.D3
