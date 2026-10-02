module

public import FrogModel.Engine.DomDefs
public import FrogModel.Engine.Dominate
public import FrogModel.Engine.Markov
public import FrogModel.LinSys.Basic

@[expose] public section

/-!
# The dominating chain

The redirected chain of the proof of Theorem 6.5 of the paper, for the chain `domStep`
of FrogModel.Engine.DomDefs with `lump` dominating its argument (`Dom R x (lump x)`):

- it dominates the root chain (`couplingLE_domOut`, from `couplingLE_redirect`, Lemma 6.4);
- (V) a sub-solution of the absorption system, supported on the live unflagged states with at
  most `T` exits and bounded, lies below the probability of being absorbed unflagged with the
  outputs `o` (`le_absUnflagged_of_sub`), by the contraction `contrW`; on that event the output
  of the chain is `o` (`domOut_eq_of_absUnflagged`);
- (W) a super-solution of the system whose reward is `Phi` at the step that sets the flag bounds
  `E[F(B); flagged]` whenever `E_x F(B) ≤ Phi(x)` from the states where the flag is set
  (`lintegral_flagged_le_of_super`), and the tail of the output beyond `T` is carried by the
  flagged part (`map_domOut_tail_le`).
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine

variable {S U : Type*} {d J : ℕ}

/-! ### One step -/

theorem domStep_of_free (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (y : RState S d J × Bool) (ξ : Fin (d + 1) × U)
    (hy : domFree T y) : domStep cstep T T' keep lump y ξ = (rstep cstep y.1 ξ, y.2) := by
  unfold FrogModel.Engine.domFree at hy
  simp [FrogModel.Engine.domStep, hy]

theorem domFree_domStep (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (y : RState S d J × Bool) (ξ : Fin (d + 1) × U)
    (hy : domFree T y) : domFree T (domStep cstep T T' keep lump y ξ) := by
  have hstep : FrogModel.Engine.domStep cstep T T' keep lump y ξ = (FrogModel.Engine.rstep cstep y.1 ξ, y.2) :=
    FrogModel.Engine.domStep_of_free cstep T T' keep lump y ξ hy
  rw [hstep]
  unfold FrogModel.Engine.domFree
  rcases hy with (hy_flag | hy_e | hy_i)
  · left; exact hy_flag
  · by_cases h : y.1.i < J ∧ ξ.1 = 0
    · have he : (FrogModel.Engine.rstep cstep y.1 ξ).e = y.1.e + 1 := by
        rw [FrogModel.Engine.rstep_e cstep y.1 ξ, if_pos h]
      right; left; rw [he]; omega
    · have he : (FrogModel.Engine.rstep cstep y.1 ξ).e = y.1.e := by
        rw [FrogModel.Engine.rstep_e cstep y.1 ξ, if_neg h]
      right; left; rw [he]; exact hy_e
  · have hstep_eq : FrogModel.Engine.rstep cstep y.1 ξ = y.1 :=
      FrogModel.Engine.rstep_of_absorbed cstep y.1 hy_i ξ
    right; right; rw [hstep_eq]; exact hy_i

theorem domStep_dom (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hR : ∀ s, R s s)
    (hlump : ∀ x, Dom R x (lump x)) (x : RState S d J) (z : Bool) (ξ : Fin (d + 1) × U) :
    Dom R (rstep cstep x ξ) (domStep cstep T T' keep lump (x, z) ξ).1 := by
  unfold FrogModel.Engine.domStep
  by_cases h1 : z = true ∨ T < x.e ∨ J ≤ x.i
  · -- case 1: domStep returns (rstep cstep x ξ, z)
    simp [h1]
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro c
    exact hR _
  · -- h1 is false
    simp [h1]
    by_cases h2 : T < (rstep cstep x ξ).e ∨ T' < (rstep cstep x ξ).p
    · -- case 2: domStep returns (rstep cstep x ξ, true)
      simp [h2]
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      intro c
      exact hR _
    · -- h2 is false
      simp [h2]
      by_cases h3 : J ≤ (rstep cstep x ξ).i ∨ keep (rstep cstep x ξ) = true
      · -- case 3: domStep returns (rstep cstep x ξ, false)
        simp [h3]
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        intro c
        exact hR _
      · -- case 4: domStep returns (lump (rstep cstep x ξ), false)
        simp [h3]
        exact hlump (rstep cstep x ξ)

theorem measurableSet_domStep_eq [MeasurableSpace U] [Countable S] (cstep : S → U → ℕ × S)
    (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (y y' : RState S d J × Bool) :
    MeasurableSet {ξ : Fin (d + 1) × U | domStep cstep T T' keep lump y ξ = y'} := by
  set F : RState S d J → RState S d J × Bool :=
    λ x =>
      if y.2 = true ∨ T < y.1.e ∨ J ≤ y.1.i then (x, y.2)
      else if T < x.e ∨ T' < x.p then (x, true)
      else if J ≤ x.i ∨ keep x = true then (x, false)
      else (lump x, false)
  with hF
  have h_eq : ∀ ξ, domStep cstep T T' keep lump y ξ = F (rstep cstep y.1 ξ) := by
    intro ξ; rfl
  have h_set_eq : {ξ : Fin (d + 1) × U | domStep cstep T T' keep lump y ξ = y'} =
      ⋃ x ∈ {x | F x = y'}, {ξ : Fin (d + 1) × U | rstep cstep y.1 ξ = x} := by
    ext ξ; constructor
    · intro h
      simp at h
      have h_eq' := h_eq ξ
      have hF := h_eq' ▸ h
      refine Set.mem_iUnion₂.mpr ⟨rstep cstep y.1 ξ, hF, ?_⟩
      rfl
    · intro h
      rcases Set.mem_iUnion₂.mp h with ⟨x, hx, hξ⟩
      simp at hx hξ
      have h_eq' := h_eq ξ
      rw [hξ] at h_eq'
      rw [hx] at h_eq'
      simp [h_eq']
  rw [h_set_eq]
  refine MeasurableSet.biUnion (Set.to_countable _) ?_
  intro x hx
  exact measurableSet_rstep_eq cstep hc y.1 x

/-- A step keeps the counts and outputs of a valid state valid, and records no output twice. -/
theorem valid_domStep (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hlump : ∀ x, Dom R x (lump x))
    (y : RState S d J × Bool) (ξ : Fin (d + 1) × U) (hy : Valid y.1) :
    Valid (domStep cstep T T' keep lump y ξ).1 ∧
      (domStep cstep T T' keep lump y ξ).1.out ≤ y.1.out ∧
      y.1.i ≤ (domStep cstep T T' keep lump y ξ).1.i := by
  unfold FrogModel.Engine.domStep
  split_ifs with h1 h2 h3
  · -- case 1: y.2 = true ∨ T < y.1.e ∨ J ≤ y.1.i → (rstep .., y.2)
    have hvalid := rstep_valid cstep y.1 hy ξ
    have hout := rstep_out_le cstep y.1 hy ξ
    have hi := le_rstep_i cstep y.1 ξ
    exact ⟨hvalid, hout, hi⟩
  · -- case 2: ¬h1 and (T < (rstep ..).e ∨ T' < (rstep ..).p) → (rstep .., true)
    have hvalid := rstep_valid cstep y.1 hy ξ
    have hout := rstep_out_le cstep y.1 hy ξ
    have hi := le_rstep_i cstep y.1 ξ
    exact ⟨hvalid, hout, hi⟩
  · -- case 3: ¬h1, ¬h2, (J ≤ (rstep ..).i ∨ keep (rstep ..) = true) → (rstep .., false)
    have hvalid := rstep_valid cstep y.1 hy ξ
    have hout := rstep_out_le cstep y.1 hy ξ
    have hi := le_rstep_i cstep y.1 ξ
    exact ⟨hvalid, hout, hi⟩
  · -- case 4: otherwise → (lump (rstep ..), false)
    have hlump_r : FrogModel.Engine.Dom R (rstep cstep y.1 ξ) (lump (rstep cstep y.1 ξ)) :=
      hlump (rstep cstep y.1 ξ)
    rcases hlump_r with ⟨hi_eq, he_eq, hp_eq, hout_eq, hσ⟩
    have hvalid_r := rstep_valid cstep y.1 hy ξ
    rcases hvalid_r with ⟨h_imp, h_forall⟩
    have hvalid : FrogModel.Engine.Valid (lump (rstep cstep y.1 ξ)) := by
      constructor
      · intro h_lt
        rw [← hp_eq]
        apply h_imp
        rwa [← hi_eq] at h_lt
      · intro k hk
        rw [← hout_eq]
        apply h_forall
        rwa [← hi_eq] at hk
    have hout : (lump (rstep cstep y.1 ξ)).out ≤ y.1.out := by
      rw [← hout_eq]
      exact rstep_out_le cstep y.1 hy ξ
    have hi : y.1.i ≤ (lump (rstep cstep y.1 ξ)).i := by
      rw [← hi_eq]
      exact le_rstep_i cstep y.1 ξ
    exact ⟨hvalid, hout, hi⟩

/-! ### Along a trajectory -/

theorem traj_domStep_flag_mono (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (y : RState S d J × Bool) (w : ℕ → Fin (d + 1) × U)
    (n m : ℕ) (hnm : n ≤ m) (hn : (traj (domStep cstep T T' keep lump) y w n).2 = true) :
    (traj (domStep cstep T T' keep lump) y w m).2 = true := by
  refine Nat.le_induction hn (fun k hk hflag => ?_) m hnm
  rw [FrogModel.Engine.traj]
  simp [FrogModel.Engine.domStep, hflag]

theorem flagSet_unique (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (y : RState S d J × Bool) (w : ℕ → Fin (d + 1) × U)
    (j k : ℕ)
    (hj : w j ∈ flagSet (domStep cstep T T' keep lump) (traj (domStep cstep T T' keep lump) y w j))
    (hk : w k ∈ flagSet (domStep cstep T T' keep lump) (traj (domStep cstep T T' keep lump) y w k)) :
    j = k := by
  set g := FrogModel.Engine.domStep cstep T T' keep lump
  have hj_unfold : (FrogModel.Engine.traj g y w j).2 = false ∧ (g (FrogModel.Engine.traj g y w j) (w j)).2 = true := by
    simpa [FrogModel.Engine.flagSet] using hj
  have hk_unfold : (FrogModel.Engine.traj g y w k).2 = false ∧ (g (FrogModel.Engine.traj g y w k) (w k)).2 = true := by
    simpa [FrogModel.Engine.flagSet] using hk
  rcases hj_unfold with ⟨hj_false, hj_true⟩
  rcases hk_unfold with ⟨hk_false, hk_true⟩
  have hj_flagged : (FrogModel.Engine.traj g y w (j + 1)).2 = true := by
    simpa [FrogModel.Engine.traj] using hj_true
  have hk_flagged : (FrogModel.Engine.traj g y w (k + 1)).2 = true := by
    simpa [FrogModel.Engine.traj] using hk_true
  rcases lt_trichotomy j k with (h_lt | h_eq | h_gt)
  · have h_le : j + 1 ≤ k := by omega
    have h_mono := FrogModel.Engine.traj_domStep_flag_mono cstep T T' keep lump y w (j + 1) k h_le hj_flagged
    exact Bool.noConfusion (h_mono.symm ▸ hk_false)
  · exact h_eq
  · have h_le : k + 1 ≤ j := by omega
    have h_mono := FrogModel.Engine.traj_domStep_flag_mono cstep T T' keep lump y w (k + 1) j h_le hk_flagged
    exact Bool.noConfusion (h_mono.symm ▸ hj_false)

/-- From a state where the chain is free, it is the root chain. -/
theorem traj_domStep_of_free (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (y : RState S d J × Bool) (hy : domFree T y)
    (w : ℕ → Fin (d + 1) × U) (n : ℕ) :
    traj (domStep cstep T T' keep lump) y w n = (traj (rstep cstep) y.1 w n, y.2) := by
  induction' n with n ih
  · rfl
  · rw [FrogModel.Engine.traj]
    rw [ih]
    have h_domFree : FrogModel.Engine.domFree T (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) y.1 w n, y.2) := by
      rcases hy with (hflag | hT | hJ)
      · left; exact hflag
      · right; left
        have h_e_mono : ∀ k, y.1.e ≤ (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) y.1 w k).e := by
          intro k
          induction' k with k ih_e
          · rfl
          · rw [FrogModel.Engine.traj]
            have h := FrogModel.Engine.rstep_e cstep (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) y.1 w k) (w k)
            rw [h]
            split
            · omega
            · exact ih_e
        exact lt_of_lt_of_le hT (h_e_mono n)
      · right; right
        have h_i_mono : ∀ k, y.1.i ≤ (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) y.1 w k).i := by
          intro k
          induction' k with k ih_i
          · rfl
          · rw [FrogModel.Engine.traj]
            exact le_trans ih_i (FrogModel.Engine.le_rstep_i cstep (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) y.1 w k) (w k))
        exact le_trans hJ (h_i_mono n)
    have h_domFree_cond : (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) y.1 w n, y.2).2 = true ∨
      T < (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) y.1 w n, y.2).1.e ∨
      J ≤ (FrogModel.Engine.traj (FrogModel.Engine.rstep cstep) y.1 w n, y.2).1.i := by
      rcases h_domFree with (h | h | h)
      · left; exact h
      · right; left; exact h
      · right; right; exact h
    rw [FrogModel.Engine.domStep]
    simp [h_domFree_cond]
    rw [FrogModel.Engine.traj]

/-- The outputs of a valid trajectory are those of any of its tails. -/
theorem domOut_eq_tail (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hlump : ∀ x, Dom R x (lump x))
    (y : RState S d J × Bool) (hy : Valid y.1) (w : ℕ → Fin (d + 1) × U) (n : ℕ) :
    domOut (domStep cstep T T' keep lump) y w =
      domOut (domStep cstep T T' keep lump) (traj (domStep cstep T T' keep lump) y w n)
        (fun j => w (n + j)) := by
  set g := FrogModel.Engine.domStep cstep T T' keep lump with hg
  have h_valid_traj : ∀ m, FrogModel.Engine.Valid (FrogModel.Engine.traj g y w m).1 := by
    intro m
    induction' m with m ih
    · exact hy
    · have hstep := FrogModel.Engine.valid_domStep cstep T T' keep lump R hlump
        (FrogModel.Engine.traj g y w m) (w m) ih
      simpa [FrogModel.Engine.traj] using hstep.1
  have h_out_le : ∀ m, (FrogModel.Engine.traj g y w (m + 1)).1.out ≤ (FrogModel.Engine.traj g y w m).1.out := by
    intro m
    have hstep := FrogModel.Engine.valid_domStep cstep T T' keep lump R hlump
      (FrogModel.Engine.traj g y w m) (w m) (h_valid_traj m)
    simpa [FrogModel.Engine.traj] using hstep.2.1
  have h_antitone : ∀ m m', m ≤ m' → (FrogModel.Engine.traj g y w m').1.out ≤ (FrogModel.Engine.traj g y w m).1.out := by
    intro m m' hle
    refine Nat.le_induction (le_refl _) (fun k hk hle' => le_trans (h_out_le k) hle') m' hle
  ext i
  have hRHS : FrogModel.Engine.domOut g (FrogModel.Engine.traj g y w n) (fun j => w (n + j)) i =
      ⨅ j, (FrogModel.Engine.traj g y w (n + j)).1.out i := by
    simp [FrogModel.Engine.domOut, FrogModel.Engine.recOut, FrogModel.Engine.traj_add]
  rw [hRHS]
  apply le_antisymm
  · refine le_iInf (fun j => ?_)
    apply iInf_le
  · refine le_iInf (fun m => ?_)
    by_cases hm : m < n
    · have hle_antitone : (FrogModel.Engine.traj g y w n).1.out i ≤
        (FrogModel.Engine.traj g y w m).1.out i :=
        (h_antitone m n (Nat.le_of_lt hm)) i
      have hinf : (⨅ j, (FrogModel.Engine.traj g y w (n + j)).1.out i) ≤
          (FrogModel.Engine.traj g y w n).1.out i := by
        simpa using iInf_le (fun j => (FrogModel.Engine.traj g y w (n + j)).1.out i) 0
      exact le_trans hinf hle_antitone
    · have hnle : n ≤ m := Nat.le_of_not_lt hm
      rcases Nat.exists_eq_add_of_le hnle with ⟨d, hd⟩
      have hinf : (⨅ j, (FrogModel.Engine.traj g y w (n + j)).1.out i) ≤
          (FrogModel.Engine.traj g y w (n + d)).1.out i := by
        simpa using iInf_le (fun j => (FrogModel.Engine.traj g y w (n + j)).1.out i) d
      simpa [hd] using hinf

/-- An unflagged state reached from an unflagged state with at most `T` exits has at most `T`
exits. -/
theorem traj_domStep_e_le (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hlump : ∀ x, Dom R x (lump x))
    (y : RState S d J × Bool) (hy2 : y.2 = false) (hye : y.1.e ≤ T) (w : ℕ → Fin (d + 1) × U)
    (n : ℕ) (hn : (traj (domStep cstep T T' keep lump) y w n).2 = false) :
    (traj (domStep cstep T T' keep lump) y w n).1.e ≤ T := by
  induction n generalizing y with
  | zero =>
      simpa [FrogModel.Engine.traj] using hye
  | succ k ih =>
      set g := FrogModel.Engine.domStep cstep T T' keep lump with hg
      set z := FrogModel.Engine.traj g y w k with hz
      have hzn : (g z (w k)).2 = false := by
        simpa [hz, FrogModel.Engine.traj] using hn
      have hz2 : z.2 = false := by
        by_contra! H
        have hz2true : z.2 = true := Bool.eq_true_of_not_eq_false H
        have h_g_val : g z (w k) = (FrogModel.Engine.rstep cstep z.1 (w k), z.2) := by
          unfold g FrogModel.Engine.domStep
          simp [hz2true]
        rw [h_g_val] at hzn
        simp [hz2true] at hzn
      have h_traj_k_false : (FrogModel.Engine.traj g y w k).2 = false := by
        rw [← hz]
        exact hz2
      have hz_e_le_T : z.1.e ≤ T := ih y hy2 hye h_traj_k_false
      have h_goal_expr : (FrogModel.Engine.traj g y w (k + 1)) = g z (w k) := by
        simp [hz, FrogModel.Engine.traj]
      rw [h_goal_expr]
      unfold g FrogModel.Engine.domStep
      split_ifs with h1 h2 h3
      · rcases h1 with (hz2true | hTlt | hJle)
        · -- z.2 = true contradicts hz2: z.2 = false
          have : False := by
            rw [hz2] at hz2true
            exact Bool.false_ne_true hz2true
          exact False.elim this
        · -- T < z.1.e contradicts hz_e_le_T
          omega
        · -- J ≤ z.1.i, so rstep cstep z.1 (w k) = z.1
          have hrstep_eq : FrogModel.Engine.rstep cstep z.1 (w k) = z.1 :=
            FrogModel.Engine.rstep_of_absorbed cstep z.1 hJle (w k)
          simp [hrstep_eq]
          exact hz_e_le_T
      · have h_g_val : g z (w k) = (FrogModel.Engine.rstep cstep z.1 (w k), true) := by
          unfold g FrogModel.Engine.domStep
          simp [h1, h2]
        rw [h_g_val] at hzn
        simp at hzn
      · -- Goal: (rstep cstep z.1 (w k), false).1.e ≤ T
        simp
        have h_not_T_lt : ¬ T < (FrogModel.Engine.rstep cstep z.1 (w k)).e := by
          intro hTlt; apply h2; left; exact hTlt
        omega
      · -- Goal: (lump (rstep cstep z.1 (w k)), false).1.e ≤ T
        simp
        have h_not_T_lt : ¬ T < (FrogModel.Engine.rstep cstep z.1 (w k)).e := by
          intro hTlt; apply h2; left; exact hTlt
        have h_e_le_T : (FrogModel.Engine.rstep cstep z.1 (w k)).e ≤ T := by omega
        have hdom := hlump (FrogModel.Engine.rstep cstep z.1 (w k))
        rcases hdom with ⟨_, heq, _, _, _⟩
        rw [← heq]
        exact h_e_le_T

/-- A trajectory never flagged, under unbounded exits, is absorbed. -/
theorem exists_absorbed_of_unflagged (cstep : S → U → ℕ × S) (T T' : ℕ)
    (keep : RState S d J → Bool) (lump : RState S d J → RState S d J) (R : S → S → Prop)
    (hlump : ∀ x, Dom R x (lump x)) (y : RState S d J × Bool) (hy2 : y.2 = false)
    (hye : y.1.e ≤ T) (w : ℕ → Fin (d + 1) × U) (hw : ∀ m, ∃ n, m ≤ exitCount w n)
    (hunf : ∀ n, (traj (domStep cstep T T' keep lump) y w n).2 = false) :
    ∃ n, J ≤ (traj (domStep cstep T T' keep lump) y w n).1.i := by
  by_contra! h
  -- h: ∀ n, (traj ... n).1.i < J
  set g := FrogModel.Engine.domStep cstep T T' keep lump with hg
  have h_induction : ∀ n, y.1.e + FrogModel.Engine.exitCount w n ≤ (FrogModel.Engine.traj g y w n).1.e := by
    intro n
    induction' n with n ih
    · simp [FrogModel.Engine.traj, FrogModel.Engine.exitCount]
    · set z := FrogModel.Engine.traj g y w n with hz
      have hz_flag : z.2 = false := hunf n
      have hz_i_lt_J : z.1.i < J := h n
      have hz_e_le_T : z.1.e ≤ T :=
        FrogModel.Engine.traj_domStep_e_le cstep T T' keep lump R hlump y hy2 hye w n (hunf n)
      have hg_flag : (g z (w n)).2 = false := by
        dsimp [g]
        rw [hz]
        exact hunf (n+1)
      have h_not_flag1 : ¬ (z.2 = true ∨ T < z.1.e ∨ J ≤ z.1.i) := by
        simp [hz_flag, hz_e_le_T, hz_i_lt_J]
      have h_not_flag2 : ¬ (T < (FrogModel.Engine.rstep cstep z.1 (w n)).e ∨
        T' < (FrogModel.Engine.rstep cstep z.1 (w n)).p) := by
        intro hflag2
        have hflag : (g z (w n)).2 = true := by
          dsimp [g]
          unfold FrogModel.Engine.domStep
          simp [h_not_flag1, hflag2]
        rw [hg_flag] at hflag
        exact Bool.false_ne_true hflag
      have h_e_eq : (g z (w n)).1.e = z.1.e + (if (w n).1 = 0 then 1 else 0) := by
        dsimp [g]
        unfold FrogModel.Engine.domStep
        simp [h_not_flag1, h_not_flag2]
        by_cases hcase : J ≤ (FrogModel.Engine.rstep cstep z.1 (w n)).i ∨
          keep (FrogModel.Engine.rstep cstep z.1 (w n)) = true
        · simp [hcase]
          rw [FrogModel.Engine.rstep_e cstep z.1 (w n)]
          by_cases hzero : (w n).1 = 0
          · simp [hz_i_lt_J, hzero]
          · simp [hz_i_lt_J, hzero]
        · simp [hcase]
          have hlump_e := (hlump (FrogModel.Engine.rstep cstep z.1 (w n))).2.1
          rw [← hlump_e, FrogModel.Engine.rstep_e cstep z.1 (w n)]
          by_cases hzero : (w n).1 = 0
          · simp [hz_i_lt_J, hzero]
          · simp [hz_i_lt_J, hzero]
      rw [FrogModel.Engine.traj, FrogModel.Engine.exitCount_succ]
      rw [h_e_eq]
      omega
  rcases hw (T + 1) with ⟨n, hn⟩
  have h_le : FrogModel.Engine.exitCount w n ≤ (FrogModel.Engine.traj g y w n).1.e := by
    have := h_induction n
    omega
  have h_e_le_T : (FrogModel.Engine.traj g y w n).1.e ≤ T :=
    FrogModel.Engine.traj_domStep_e_le cstep T T' keep lump R hlump y hy2 hye w n (hunf n)
  omega

/-- The last output of a trajectory absorbed unflagged is at most `T`. -/
theorem domOut_le_of_absorbed_unflagged (cstep : S → U → ℕ × S) (T T' : ℕ)
    (keep : RState S d J → Bool) (lump : RState S d J → RState S d J) (R : S → S → Prop)
    (hlump : ∀ x, Dom R x (lump x)) (y : RState S d J × Bool) (hyv : Valid y.1)
    (hy2 : y.2 = false) (hye : y.1.e ≤ T)
    (hyo : ∀ k : Fin J, (k : ℕ) < y.1.i → y.1.out k ≤ y.1.e) (w : ℕ → Fin (d + 1) × U) (n : ℕ)
    (hn : J ≤ (traj (domStep cstep T T' keep lump) y w n).1.i)
    (hn2 : (traj (domStep cstep T T' keep lump) y w n).2 = false) (k : Fin J) :
    domOut (domStep cstep T T' keep lump) y w k ≤ T := by
  let g := FrogModel.Engine.domStep cstep T T' keep lump
  -- e does not decrease through a domStep
  have h_domStep_e_ge : ∀ (x : FrogModel.Engine.RState S d J) (flag : Bool) (ξ : Fin (d + 1) × U),
      (x.e : ℕ∞) ≤ (g (x, flag) ξ).1.e := by
    intro x flag ξ
    unfold g FrogModel.Engine.domStep
    by_cases h1 : flag = true ∨ T < x.e ∨ J ≤ x.i
    · simp [h1]
      rw [FrogModel.Engine.rstep_e]
      split
      · simp
      · simp
    · simp [h1]
      by_cases h2 : T < (FrogModel.Engine.rstep cstep x ξ).e ∨ T' < (FrogModel.Engine.rstep cstep x ξ).p
      · simp [h2]
        rw [FrogModel.Engine.rstep_e]
        split
        · simp
        · simp
      · simp [h2]
        by_cases h3 : J ≤ (FrogModel.Engine.rstep cstep x ξ).i ∨ keep (FrogModel.Engine.rstep cstep x ξ) = true
        · simp [h3]
          rw [FrogModel.Engine.rstep_e]
          split
          · simp
          · simp
        · simp [h3]
          have h_dom := hlump (FrogModel.Engine.rstep cstep x ξ)
          rcases h_dom with ⟨_, he, _, _, _⟩
          have h_rstep_e_ge : (x.e : ℕ∞) ≤ (FrogModel.Engine.rstep cstep x ξ).e := by
            rw [FrogModel.Engine.rstep_e]
            split
            · simp
            · simp
          simpa [he] using h_rstep_e_ge
  -- when i increases through rstep, the finished frog's out equals e
  have h_rstep_out_eq_e_of_i_increase (x : FrogModel.Engine.RState S d J) (ξ : Fin (d + 1) × U)
      (hJ : x.i < J) (hp : (FrogModel.Engine.move cstep x ξ.1 ξ.2).2.1 = 0) (k : Fin J)
      (hk : (k : ℕ) = x.i) : (FrogModel.Engine.rstep cstep x ξ).out k = (FrogModel.Engine.rstep cstep x ξ).e := by
    have hk_eq : k = ⟨x.i, hJ⟩ := Fin.ext (by simpa using hk)
    rw [hk_eq]
    unfold FrogModel.Engine.rstep
    simp [hJ, hp]
  -- rstep increases i by at most 1
  have h_rstep_i_le_succ : ∀ (x : FrogModel.Engine.RState S d J) (ξ : Fin (d + 1) × U),
      (FrogModel.Engine.rstep cstep x ξ).i ≤ x.i + 1 := by
    intro x ξ
    unfold FrogModel.Engine.rstep
    split
    · -- x.i < J branch
      split
      · -- move.p = 0 branch: returns ⟨x.i + 1, ...⟩
        simp
      · -- move.p ≠ 0 branch: returns ⟨x.i, ...⟩
        simp
    · -- J ≤ x.i branch: returns x
      simp
  -- domStep also increases i by at most 1
  have h_domStep_i_le_succ : ∀ (x : FrogModel.Engine.RState S d J) (flag : Bool) (ξ : Fin (d + 1) × U),
      (g (x, flag) ξ).1.i ≤ x.i + 1 := by
    intro x flag ξ
    unfold g FrogModel.Engine.domStep
    by_cases h1 : flag = true ∨ T < x.e ∨ J ≤ x.i
    · simp [h1]
      exact h_rstep_i_le_succ x ξ
    · simp [h1]
      by_cases h2 : T < (FrogModel.Engine.rstep cstep x ξ).e ∨ T' < (FrogModel.Engine.rstep cstep x ξ).p
      · simp [h2]
        exact h_rstep_i_le_succ x ξ
      · simp [h2]
        by_cases h3 : J ≤ (FrogModel.Engine.rstep cstep x ξ).i ∨ keep (FrogModel.Engine.rstep cstep x ξ) = true
        · simp [h3]
          exact h_rstep_i_le_succ x ξ
        · simp [h3]
          have h_dom := hlump (FrogModel.Engine.rstep cstep x ξ)
          rcases h_dom with ⟨hi, _, _, _, _⟩
          rw [← hi]
          exact h_rstep_i_le_succ x ξ
  -- invariant: out k ≤ e for all k < i, and state is valid
  have h_inv : ∀ m, FrogModel.Engine.Valid ((FrogModel.Engine.traj g y w m).1) ∧
      ∀ (k' : Fin J), (k' : ℕ) < ((FrogModel.Engine.traj g y w m).1).i →
      ((FrogModel.Engine.traj g y w m).1).out k' ≤ ((FrogModel.Engine.traj g y w m).1).e := by
    intro m
    induction' m with m ih
    · constructor
      · simpa [FrogModel.Engine.traj] using hyv
      · intro k' hk'
        simpa [FrogModel.Engine.traj] using hyo k' hk'
    · rcases ih with ⟨h_valid, h_bound⟩
      set s := (FrogModel.Engine.traj g y w m).1 with hs
      set flag := (FrogModel.Engine.traj g y w m).2 with hflag
      have h_step := FrogModel.Engine.valid_domStep cstep T T' keep lump R hlump
        (s, flag) (w m) h_valid
      rcases h_step with ⟨h_valid', h_out_le, h_i_le⟩
      have h_e_le : (s.e : ℕ∞) ≤ (g (s, flag) (w m)).1.e := h_domStep_e_ge s flag (w m)
      constructor
      · exact h_valid'
      · intro k' hk'
        have hk'_lt_new_i : (k' : ℕ) < ((g (s, flag) (w m)).1).i := by
          simpa [FrogModel.Engine.traj, hs, hflag] using hk'
        by_cases hk'_lt_old_i : (k' : ℕ) < s.i
        · -- k' < old_i: use induction hypothesis
          have h_out_k' : s.out k' ≤ (s.e : ℕ∞) := h_bound k' hk'_lt_old_i
          have h_domOut_le : (g (s, flag) (w m)).1.out k' ≤ s.out k' := by
            simpa using h_out_le k'
          have h_le_e : (g (s, flag) (w m)).1.out k' ≤ (s.e : ℕ∞) :=
            le_trans h_domOut_le h_out_k'
          have h_le_new_e : (g (s, flag) (w m)).1.out k' ≤ (g (s, flag) (w m)).1.e :=
            le_trans h_le_e h_e_le
          simpa [FrogModel.Engine.traj, hs, hflag] using h_le_new_e
        · -- old_i ≤ k' and k' < new_i, so i increased and k' = old_i
          have h_old_i_le_k' : s.i ≤ (k' : ℕ) := by omega
          have h_i_increased : s.i < ((g (s, flag) (w m)).1).i := by omega
          have h_new_i_le_succ : ((g (s, flag) (w m)).1).i ≤ s.i + 1 :=
            h_domStep_i_le_succ s flag (w m)
          have h_new_i_eq_succ : ((g (s, flag) (w m)).1).i = s.i + 1 := by omega
          have hk'_eq_old_i : (k' : ℕ) = s.i := by omega
          -- Since i increased, we must have s.i < J and move.p = 0 in rstep
          have hJ : s.i < J := by
            by_contra! hJ'
            have h_rstep_i : (FrogModel.Engine.rstep cstep s (w m)).i = s.i := by
              unfold FrogModel.Engine.rstep
              split
              · -- h : s.i < J, but hJ' says J ≤ s.i
                omega
              · -- ¬ s.i < J
                rfl
            have h_dom_i : (g (s, flag) (w m)).1.i = (FrogModel.Engine.rstep cstep s (w m)).i := by
              unfold g FrogModel.Engine.domStep
              by_cases h1 : flag = true ∨ T < s.e ∨ J ≤ s.i
              · simp [h1]
              · simp [h1]
                by_cases h2 : T < (FrogModel.Engine.rstep cstep s (w m)).e ∨ T' < (FrogModel.Engine.rstep cstep s (w m)).p
                · simp [h2]
                · simp [h2]
                  by_cases h3 : J ≤ (FrogModel.Engine.rstep cstep s (w m)).i ∨ keep (FrogModel.Engine.rstep cstep s (w m)) = true
                  · simp [h3]
                  · simp [h3]
                    have h_dom := hlump (FrogModel.Engine.rstep cstep s (w m))
                    rcases h_dom with ⟨hi, _, _, _, _⟩
                    rw [hi]
            rw [h_dom_i, h_rstep_i] at h_new_i_eq_succ
            omega
          have hp_zero : (FrogModel.Engine.move cstep s (w m).1 (w m).2).2.1 = 0 := by
            by_contra! hp_ne_zero
            have h_rstep_i : (FrogModel.Engine.rstep cstep s (w m)).i = s.i := by
              unfold FrogModel.Engine.rstep
              simp [hJ, hp_ne_zero]
            have h_dom_i : (g (s, flag) (w m)).1.i = (FrogModel.Engine.rstep cstep s (w m)).i := by
              unfold g FrogModel.Engine.domStep
              by_cases h1 : flag = true ∨ T < s.e ∨ J ≤ s.i
              · simp [h1]
              · simp [h1]
                by_cases h2 : T < (FrogModel.Engine.rstep cstep s (w m)).e ∨ T' < (FrogModel.Engine.rstep cstep s (w m)).p
                · simp [h2]
                · simp [h2]
                  by_cases h3 : J ≤ (FrogModel.Engine.rstep cstep s (w m)).i ∨ keep (FrogModel.Engine.rstep cstep s (w m)) = true
                  · simp [h3]
                  · simp [h3]
                    have h_dom := hlump (FrogModel.Engine.rstep cstep s (w m))
                    rcases h_dom with ⟨hi, _, _, _, _⟩
                    rw [hi]
            rw [h_dom_i, h_rstep_i] at h_new_i_eq_succ
            omega
          have hk'_eq : k' = ⟨s.i, hJ⟩ := Fin.ext (by simpa using hk'_eq_old_i)
          rw [hk'_eq]
          -- Goal: (traj g y w (m+1)).1.out ⟨s.i, hJ⟩ ≤ (traj g y w (m+1)).1.e
          -- Rewrite traj to expose the domStep application
          simp [FrogModel.Engine.traj, hs, hflag]
          -- Now goal: (g (s, flag) (w m)).1.out ⟨s.i, hJ⟩ ≤ (g (s, flag) (w m)).1.e
          have h_rstep_out_eq_e : (FrogModel.Engine.rstep cstep s (w m)).out ⟨s.i, hJ⟩ =
              (FrogModel.Engine.rstep cstep s (w m)).e :=
            h_rstep_out_eq_e_of_i_increase s (w m) hJ hp_zero ⟨s.i, hJ⟩ rfl
          have h_dom_out_eq : (g (s, flag) (w m)).1.out ⟨s.i, hJ⟩ =
              (FrogModel.Engine.rstep cstep s (w m)).out ⟨s.i, hJ⟩ := by
            unfold g FrogModel.Engine.domStep
            by_cases h1 : flag = true ∨ T < s.e ∨ J ≤ s.i
            · simp [h1]
            · simp [h1]
              by_cases h2 : T < (FrogModel.Engine.rstep cstep s (w m)).e ∨ T' < (FrogModel.Engine.rstep cstep s (w m)).p
              · simp [h2]
              · simp [h2]
                by_cases h3 : J ≤ (FrogModel.Engine.rstep cstep s (w m)).i ∨ keep (FrogModel.Engine.rstep cstep s (w m)) = true
                · simp [h3]
                · simp [h3]
                  have h_dom := hlump (FrogModel.Engine.rstep cstep s (w m))
                  rcases h_dom with ⟨_, _, _, h_out, _⟩
                  simpa [h_out] using rfl
          have h_dom_e_eq : (g (s, flag) (w m)).1.e = (FrogModel.Engine.rstep cstep s (w m)).e := by
            unfold g FrogModel.Engine.domStep
            by_cases h1 : flag = true ∨ T < s.e ∨ J ≤ s.i
            · simp [h1]
            · simp [h1]
              by_cases h2 : T < (FrogModel.Engine.rstep cstep s (w m)).e ∨ T' < (FrogModel.Engine.rstep cstep s (w m)).p
              · simp [h2]
              · simp [h2]
                by_cases h3 : J ≤ (FrogModel.Engine.rstep cstep s (w m)).i ∨ keep (FrogModel.Engine.rstep cstep s (w m)) = true
                · simp [h3]
                · simp [h3]
                  have h_dom := hlump (FrogModel.Engine.rstep cstep s (w m))
                  rcases h_dom with ⟨_, he, _, _, _⟩
                  simpa [he] using rfl
          rw [h_dom_out_eq, h_dom_e_eq]
          rw [h_rstep_out_eq_e]
  have h_at_n := h_inv n
  rcases h_at_n with ⟨_, h_bound_n⟩
  have hk_lt_J : (k : ℕ) < J := Fin.is_lt k
  have hk_lt_i : (k : ℕ) < ((FrogModel.Engine.traj g y w n).1).i := by
    have h_i_ge_J : J ≤ ((FrogModel.Engine.traj g y w n).1).i := hn
    omega
  have h_out_k_le_e : ((FrogModel.Engine.traj g y w n).1).out k ≤ ((FrogModel.Engine.traj g y w n).1).e :=
    h_bound_n k hk_lt_i
  have h_e_le_T : ((FrogModel.Engine.traj g y w n).1).e ≤ T :=
    FrogModel.Engine.traj_domStep_e_le cstep T T' keep lump R hlump y hy2 hye w n hn2
  have h_out_k_le_T : ((FrogModel.Engine.traj g y w n).1).out k ≤ T := by
    exact le_trans h_out_k_le_e (by exact_mod_cast h_e_le_T)
  unfold FrogModel.Engine.domOut FrogModel.Engine.recOut
  apply le_trans (iInf_le (fun m => ((FrogModel.Engine.traj g y w m).1).out k) n) h_out_k_le_T

/-! ### Measurability -/

/-- A function of the state at time `n` and of the inputs is measurable when it is for every
state. -/
theorem measurable_traj_comp {X Ξ β : Type*} [MeasurableSpace Ξ] [Countable X]
    [MeasurableSpace β] (f : X → Ξ → X) (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (x : X)
    (n : ℕ) (G : X → (ℕ → Ξ) → β) (hG : ∀ z, Measurable (G z)) :
    Measurable fun w => G (traj f x w n) w := by
  intro s hs
  have : (fun w => G (traj f x w n) w) ⁻¹' s = ⋃ z, {w | traj f x w n = z} ∩ G z ⁻¹' s := by
    ext w; simp
  rw [this]
  exact MeasurableSet.iUnion fun z => (measurableSet_traj_eq f hf x n z).inter (hG z hs)

/-- A function of a map to a countable type with measurable fibers is measurable. -/
theorem measurable_comp_of_fibers {Ξ X β : Type*} [MeasurableSpace Ξ] [Countable X]
    [MeasurableSpace β] (h : Ξ → X) (hh : ∀ x, MeasurableSet {ξ | h ξ = x}) (G : X → β) :
    Measurable fun ξ => G (h ξ) := by
  intro s _
  have : (fun ξ => G (h ξ)) ⁻¹' s = ⋃ x ∈ G ⁻¹' s, {ξ | h ξ = x} := by ext ξ; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun x _ => hh x

/-! ### Domination -/

theorem couplingLE_domOut [MeasurableSpace U] [Countable S] (cstep : S → U → ℕ × S)
    (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hR : IsSim cstep R)
    (hRrefl : ∀ s, R s s) (hlump : ∀ x, Dom R x (lump x)) (ν : Measure (Fin (d + 1) × U))
    [IsProbabilityMeasure ν] (hν : ν {ξ | ξ.1 = 0} ≠ 0) (x : RState S d J) (hx : Valid x) :
    FrogModel.LemmaX.CouplingLE ((iidMeasure ν).map (outPsi cstep x))
      ((iidMeasure ν).map (domOut (domStep cstep T T' keep lump) (x, false))) := by
  exact couplingLE_redirect cstep hc R hR (domStep cstep T T' keep lump)
    (measurableSet_domStep_eq cstep hc T T' keep lump)
    (fun x z ξ => domStep_dom cstep T T' keep lump R hRrefl hlump x z ξ) (domFree T)
    (fun y ξ hy => ⟨by rw [domStep_of_free cstep T T' keep lump y ξ hy],
      domFree_domStep cstep T T' keep lump y ξ hy⟩) T (fun y hy => Or.inr hy) ν hν x hx false

/-! ### (V): absorbed unflagged -/

theorem measurableSet_absUnflagged [MeasurableSpace U] [Countable S] (cstep : S → U → ℕ × S)
    (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (o : Fin J → ℕ) (y : RState S d J × Bool) :
    MeasurableSet (absUnflagged (domStep cstep T T' keep lump) o y) := by
  have hset : absUnflagged (domStep cstep T T' keep lump) o y =
      ⋃ z ∈ {z : RState S d J × Bool | y.2 = false ∧ y.1.i < J ∧ z.2 = false ∧ J ≤ z.1.i ∧
        z.1.out = fun k => (o k : ℕ∞)}, {ξ | domStep cstep T T' keep lump y ξ = z} := by
    ext ξ
    simp [absUnflagged]
  rw [hset]
  exact MeasurableSet.biUnion (Set.to_countable _) fun z _ =>
    measurableSet_domStep_eq cstep hc T T' keep lump y z

theorem absUnflagged_unique (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hlump : ∀ x, Dom R x (lump x))
    (o : Fin J → ℕ) (y : RState S d J × Bool) (w : ℕ → Fin (d + 1) × U) (j k : ℕ)
    (hj : w j ∈ absUnflagged (domStep cstep T T' keep lump) o
      (traj (domStep cstep T T' keep lump) y w j))
    (hk : w k ∈ absUnflagged (domStep cstep T T' keep lump) o
      (traj (domStep cstep T T' keep lump) y w k)) : j = k := by
  set g := FrogModel.Engine.domStep cstep T T' keep lump
  -- extract conditions from hj
  have hj_mem : (FrogModel.Engine.traj g y w j).2 = false ∧
    (FrogModel.Engine.traj g y w j).1.i < J ∧
    (g (FrogModel.Engine.traj g y w j) (w j)).2 = false ∧
    J ≤ (g (FrogModel.Engine.traj g y w j) (w j)).1.i ∧
    (g (FrogModel.Engine.traj g y w j) (w j)).1.out = fun k => (o k : ℕ∞) := by
    simpa [FrogModel.Engine.absUnflagged] using hj
  rcases hj_mem with ⟨_, hj_i_lt, _, hj_J_le, _⟩
  -- traj property: traj g y w (n+1) = g (traj g y w n) (w n)
  have traj_succ : ∀ n, FrogModel.Engine.traj g y w (n + 1) = g (FrogModel.Engine.traj g y w n) (w n) := by
    intro n; simp [FrogModel.Engine.traj]
  have hJ_le_succ : J ≤ (FrogModel.Engine.traj g y w (j + 1)).1.i := by
    simpa [traj_succ] using hj_J_le
  -- i is preserved by lump
  have lump_i_eq : ∀ x : FrogModel.Engine.RState S d J, (lump x).i = x.i := by
    intro x; exact ((hlump x).1).symm
  -- key lemma: (domStep ... y ξ).1.i = (rstep cstep y.1 ξ).i
  have domStep_i_eq : ∀ (y' : FrogModel.Engine.RState S d J × Bool) (ξ' : Fin (d + 1) × U),
      (g y' ξ').1.i = (FrogModel.Engine.rstep cstep y'.1 ξ').i := by
    intro y' ξ'
    dsimp [g]
    unfold FrogModel.Engine.domStep
    by_cases h1 : y'.2 = true ∨ T < y'.1.e ∨ J ≤ y'.1.i
    · simp [h1]
    · by_cases h2 : T < (FrogModel.Engine.rstep cstep y'.1 ξ').e ∨ T' < (FrogModel.Engine.rstep cstep y'.1 ξ').p
      · simp [h1, h2]
      · by_cases h3 : J ≤ (FrogModel.Engine.rstep cstep y'.1 ξ').i ∨ keep (FrogModel.Engine.rstep cstep y'.1 ξ') = true
        · simp [h1, h2, h3]
        · simp [h1, h2, h3, lump_i_eq]
  -- i doesn't decrease along trajectory of g
  have i_nondec : ∀ n m, n ≤ m → (FrogModel.Engine.traj g y w n).1.i ≤ (FrogModel.Engine.traj g y w m).1.i := by
    intro n m hnm
    refine Nat.le_induction (le_refl _) (fun m' hm' hle => ?_) m hnm
    have hstep : (FrogModel.Engine.traj g y w m').1.i ≤ (FrogModel.Engine.traj g y w (m' + 1)).1.i := by
      calc
        (FrogModel.Engine.traj g y w m').1.i ≤ (FrogModel.Engine.rstep cstep (FrogModel.Engine.traj g y w m').1 (w m')).i :=
          FrogModel.Engine.le_rstep_i cstep (FrogModel.Engine.traj g y w m').1 (w m')
        _ = (g (FrogModel.Engine.traj g y w m') (w m')).1.i := by
          rw [domStep_i_eq]
        _ = (FrogModel.Engine.traj g y w (m' + 1)).1.i := by simp [FrogModel.Engine.traj]
    exact le_trans hle hstep
  -- Now the main argument: show j = k by contradiction
  by_cases hjk : j < k
  · -- j < k case: derive J ≤ (traj g y w k).1.i from i_nondec, contradicting hk
    have hJ_le_k : J ≤ (FrogModel.Engine.traj g y w k).1.i := by
      have h := i_nondec (j + 1) k (by omega)
      exact le_trans hJ_le_succ h
    -- extract condition from hk
    have hk_mem : (FrogModel.Engine.traj g y w k).2 = false ∧
      (FrogModel.Engine.traj g y w k).1.i < J ∧
      (g (FrogModel.Engine.traj g y w k) (w k)).2 = false ∧
      J ≤ (g (FrogModel.Engine.traj g y w k) (w k)).1.i ∧
      (g (FrogModel.Engine.traj g y w k) (w k)).1.out = fun k => (o k : ℕ∞) := by
      simpa [FrogModel.Engine.absUnflagged] using hk
    rcases hk_mem with ⟨_, hk_i_lt, _, _, _⟩
    omega
  · -- j ≥ k case
    by_cases hkj : k < j
    · -- k < j case: symmetric argument
      have hk_mem : (FrogModel.Engine.traj g y w k).2 = false ∧
        (FrogModel.Engine.traj g y w k).1.i < J ∧
        (g (FrogModel.Engine.traj g y w k) (w k)).2 = false ∧
        J ≤ (g (FrogModel.Engine.traj g y w k) (w k)).1.i ∧
        (g (FrogModel.Engine.traj g y w k) (w k)).1.out = fun k => (o k : ℕ∞) := by
        simpa [FrogModel.Engine.absUnflagged] using hk
      rcases hk_mem with ⟨_, _, _, hk_J_le, _⟩
      have hk_J_le_succ : J ≤ (FrogModel.Engine.traj g y w (k + 1)).1.i := by
        simpa [traj_succ] using hk_J_le
      have hJ_le_j : J ≤ (FrogModel.Engine.traj g y w j).1.i := by
        have h := i_nondec (k + 1) j (by omega)
        exact le_trans hk_J_le_succ h
      have hj_i_lt : (FrogModel.Engine.traj g y w j).1.i < J := hj_i_lt
      omega
    · -- neither j < k nor k < j, so j = k
      omega

theorem domOut_eq_of_absUnflagged (cstep : S → U → ℕ × S) (T T' : ℕ)
    (keep : RState S d J → Bool) (lump : RState S d J → RState S d J) (R : S → S → Prop)
    (hlump : ∀ x, Dom R x (lump x)) (o : Fin J → ℕ) (y : RState S d J × Bool) (hy : Valid y.1)
    (w : ℕ → Fin (d + 1) × U) (k : ℕ)
    (hk : w k ∈ absUnflagged (domStep cstep T T' keep lump) o
      (traj (domStep cstep T T' keep lump) y w k)) :
    domOut (domStep cstep T T' keep lump) y w = fun k => (o k : ℕ∞) := by
  let g := FrogModel.Engine.domStep cstep T T' keep lump
  have hk_mem := hk
  rw [FrogModel.Engine.absUnflagged] at hk_mem
  simp at hk_mem
  rcases hk_mem with ⟨hk_unflagged, hk_i_lt_J, hk_next_flag, hk_next_i_ge_J, hk_next_out⟩
  let z := g (FrogModel.Engine.traj g y w k) (w k)
  have h_fixed : ∀ ξ, g z ξ = z := by
    intro ξ
    dsimp [g, FrogModel.Engine.domStep]
    have h_first_cond : z.2 = true ∨ T < z.1.e ∨ J ≤ z.1.i := by
      right; right; exact hk_next_i_ge_J
    simp [h_first_cond, FrogModel.Engine.rstep_of_absorbed cstep z.1 hk_next_i_ge_J ξ]
  have h_traj_z : ∀ m, FrogModel.Engine.traj g z (fun j => w (k + 1 + j)) m = z := by
    intro m
    induction' m with m ih
    · rfl
    · rw [FrogModel.Engine.traj]
      rw [ih]
      exact h_fixed (w (k + 1 + m))
  have h_domOut_shift : FrogModel.Engine.domOut g y w = FrogModel.Engine.domOut g z (fun j => w (k + 1 + j)) := by
    rw [FrogModel.Engine.domOut_eq_tail cstep T T' keep lump R hlump y hy w (k + 1)]
    rfl
  have h_domOut_z : FrogModel.Engine.domOut g z (fun j => w (k + 1 + j)) = fun k' => (o k' : ℕ∞) := by
    ext k' : 1
    dsimp [FrogModel.Engine.domOut, FrogModel.Engine.recOut]
    have h_eq : (fun n : ℕ => ((FrogModel.Engine.traj g z (fun j => w (k + 1 + j)) n).1).out k') = fun _ => z.1.out k' := by
      ext n; rw [h_traj_z n]
    rw [h_eq, iInf_const, hk_next_out]
  rw [h_domOut_shift, h_domOut_z]

theorem contrW_domStep_of_free (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (y : RState S d J × Bool) (ξ : Fin (d + 1) × U)
    (hy : domFree T y) : contrW T (domStep cstep T T' keep lump y ξ) = 0 := by
  rw [domStep_of_free cstep T T' keep lump y ξ hy]
  unfold contrW
  rw [ite_eq_right]
  rintro ⟨h2, hi, hle⟩
  have he := rstep_e cstep y.1 ξ
  dsimp only at h2 hi hle
  rcases hy with h | h | h
  · simp_all
  · rw [he] at hle; split_ifs at hle <;> omega
  · rw [rstep_of_absorbed cstep y.1 h] at hi; omega

theorem domStep_e (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hlump : ∀ x, Dom R x (lump x))
    (y : RState S d J × Bool) (ξ : Fin (d + 1) × U) :
    (domStep cstep T T' keep lump y ξ).1.e = (rstep cstep y.1 ξ).e := by
  unfold domStep
  split_ifs
  · rfl
  · rfl
  · rfl
  · exact ((hlump _).2.1).symm

theorem contrW_le_pow (T : ℕ) (z : RState S d J × Bool) : contrW T z ≤ 2 ^ (T + 1 - z.1.e) := by
  unfold contrW
  split_ifs
  · exact le_rfl
  · exact zero_le

theorem contrW_domStep_le (cstep : S → U → ℕ × S) (T T' : ℕ)
    (keep : RState S d J → Bool) (lump : RState S d J → RState S d J)
    (R : S → S → Prop) (hlump : ∀ x, Dom R x (lump x))
    (y : RState S d J × Bool) (ξ : Fin (d + 1) × U) :
    contrW T (domStep cstep T T' keep lump y ξ) ≤
      (if ξ.1 = (0 : Fin (d + 1)) then 2 ^ (T - y.1.e) else 2 ^ (T + 1 - y.1.e)) := by
  by_cases hy : domFree T y
  · rw [contrW_domStep_of_free cstep T T' keep lump y ξ hy]
    exact zero_le
  · unfold domFree at hy
    push Not at hy
    refine (contrW_le_pow T _).trans (le_of_eq ?_)
    rw [domStep_e cstep T T' keep lump R hlump y ξ, rstep_e]
    by_cases h0 : ξ.1 = 0
    · rw [ite_eq_left ⟨hy.2.2, h0⟩, ite_eq_left h0]
      congr 1
      omega
    · rw [ite_eq_right (fun h => h0 h.2), ite_eq_right h0]

theorem app_contrW_le [MeasurableSpace U] [Countable S] (cstep : S → U → ℕ × S)
    (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hlump : ∀ x, Dom R x (lump x))
    (ν : Measure (Fin (d + 1) × U)) [IsProbabilityMeasure ν] :
    FrogModel.LinSys.app (fkKernel (domStep cstep T T' keep lump) (fun _ _ => 1) ν) (contrW T) ≤
      fun y => (1 - ν {ξ | ξ.1 = 0} / 2) * contrW T y := by
  intro y
  rw [app_fkKernel_one _ ν (measurableSet_domStep_eq cstep hc T T' keep lump) (contrW T) y]
  by_cases hy : domFree T y
  · have h0 : ∀ ξ, contrW T (domStep cstep T T' keep lump y ξ) = 0 := fun ξ =>
      contrW_domStep_of_free cstep T T' keep lump y ξ hy
    simp only [h0, lintegral_zero]
    exact zero_le
  · unfold domFree at hy
    push Not at hy
    have hcy : contrW T y = 2 ^ (T + 1 - y.1.e) := by
      unfold contrW
      rw [ite_eq_left ⟨by simpa using hy.1, hy.2.2, hy.2.1⟩]
    show ∫⁻ ξ, _ ∂ν ≤ (1 - ν {ξ | ξ.1 = 0} / 2) * contrW T y
    rw [hcy]
    set a : ℝ≥0∞ := 2 ^ (T - y.1.e) with ha
    have hb : (2 : ℝ≥0∞) ^ (T + 1 - y.1.e) = 2 * a := by
      rw [ha, show T + 1 - y.1.e = (T - y.1.e) + 1 by omega, pow_succ, mul_comm]
    set A : Set (Fin (d + 1) × U) := {ξ | ξ.1 = 0} with hAdef
    have hA : MeasurableSet A := measurable_fst (measurableSet_singleton 0)
    set p := ν A with hp
    have hp1 : p ≤ 1 := prob_le_one
    have hpt : p ≠ ⊤ := measure_ne_top ν A
    have hcompl : ν Aᶜ = 1 - p := prob_compl_eq_one_sub hA
    rw [hb]
    calc ∫⁻ ξ, contrW T (domStep cstep T T' keep lump y ξ) ∂ν
        ≤ ∫⁻ ξ, (A.indicator (fun _ => a) ξ + Aᶜ.indicator (fun _ => 2 * a) ξ) ∂ν := by
          refine lintegral_mono fun ξ => ?_
          have h := contrW_domStep_le cstep T T' keep lump R hlump y ξ
          rw [hb] at h
          by_cases h0 : ξ.1 = 0
          · have hm : ξ ∈ A := h0
            rw [ite_eq_left h0] at h
            rw [Set.indicator_of_mem hm, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hm), add_zero]
            exact h
          · have hm : ξ ∉ A := h0
            rw [ite_eq_right h0] at h
            rw [Set.indicator_of_notMem hm, Set.indicator_of_mem (Set.mem_compl hm), zero_add]
            exact h
      _ = a * p + 2 * a * (1 - p) := by
          rw [lintegral_add_left (measurable_const.indicator hA), lintegral_indicator_const hA,
            lintegral_indicator_const hA.compl, hcompl]
      _ = (1 - p / 2) * (2 * a) := by
          have h1 : 1 - p / 2 = (1 - p) + p / 2 := by
            rw [← tsub_add_tsub_cancel hp1 ENNReal.half_le_self, ENNReal.sub_half hpt]
          rw [h1, add_mul, show p / 2 * (2 * a) = p * a by
            rw [← mul_assoc, ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]]
          ring

theorem le_absUnflagged_of_sub [MeasurableSpace U] [Countable S] (cstep : S → U → ℕ × S)
    (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hlump : ∀ x, Dom R x (lump x))
    (ν : Measure (Fin (d + 1) × U)) [IsProbabilityMeasure ν] (hν : ν {ξ | ξ.1 = 0} ≠ 0)
    (o : Fin J → ℕ) (V : RState S d J × Bool → ℝ≥0∞)
    (hV : V ≤ (fun y => ν (absUnflagged (domStep cstep T T' keep lump) o y)) +
      FrogModel.LinSys.app (fkKernel (domStep cstep T T' keep lump) (fun _ _ => 1) ν) V)
    (hVsupp : ∀ y, V y ≠ 0 → y.2 = false ∧ y.1.i < J ∧ y.1.e ≤ T) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hVbd : ∀ y, V y ≤ C) (y : RState S d J × Bool) :
    V y ≤ iidMeasure ν {w | ∃ k, w k ∈ absUnflagged (domStep cstep T T' keep lump) o
      (traj (domStep cstep T T' keep lump) y w k)} := by
  have hgm := measurableSet_domStep_eq cstep hc T T' keep lump
  rw [measure_exists_traj_eq_least (domStep cstep T T' keep lump) ν hgm
    (absUnflagged (domStep cstep T T' keep lump) o)
    (measurableSet_absUnflagged cstep hc T T' keep lump o) y
    (fun w j k hj hk => absUnflagged_unique cstep T T' keep lump R hlump o y w j k hj hk)]
  refine FrogModel.LinSys.le_least_of_sub_contract _ _ V (contrW T) _ C hV
    (app_contrW_le cstep hc T T' keep lump R hlump ν) ?_ (fun i => ?_) hC (fun i => ?_) y
  · exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (ENNReal.div_ne_zero.2 ⟨hν, ENNReal.ofNat_ne_top⟩)
  · unfold contrW
    split_ifs
    · exact ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    · exact ENNReal.zero_ne_top
  · by_cases hVi : V i = 0
    · simp [hVi]
    · obtain ⟨h1, h2, h3⟩ := hVsupp i hVi
      have hc1 : contrW T i = 2 ^ (T + 1 - i.1.e) := by simp [contrW, h1, h2, h3]
      rw [hc1]
      exact (hVbd i).trans (le_mul_of_one_le_right zero_le (one_le_pow₀ (by norm_num)))

/-! ### (W): the flagged part -/

open Classical in
theorem lintegral_flagged_le_of_super [MeasurableSpace U] [Countable S]
    (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (T T' : ℕ)
    (keep : RState S d J → Bool) (lump : RState S d J → RState S d J) (R : S → S → Prop)
    (hlump : ∀ x, Dom R x (lump x)) (ν : Measure (Fin (d + 1) × U)) [IsProbabilityMeasure ν]
    (F : ℕ∞ → ℝ≥0∞) (k : Fin J) (Φ : RState S d J → ℝ≥0∞) (Inv : RState S d J × Bool → Prop)
    (hInv : ∀ y ξ, Inv y → Inv (domStep cstep T T' keep lump y ξ))
    (hΦ : ∀ y ξ, Inv y → ξ ∈ flagSet (domStep cstep T T' keep lump) y →
      ∫⁻ w, F (recOut (traj (rstep cstep) (domStep cstep T T' keep lump y ξ).1 w) k)
        ∂(iidMeasure ν) ≤ Φ (domStep cstep T T' keep lump y ξ).1)
    (W : RState S d J × Bool → ℝ≥0∞)
    (hW : fkRhs (flagReward (domStep cstep T T' keep lump) Φ) ν +
      FrogModel.LinSys.app (fkKernel (domStep cstep T T' keep lump) (fun _ _ => 1) ν) W ≤ W)
    (y : RState S d J × Bool) (hy : Inv y) (hyv : Valid y.1) (hy2 : y.2 = false) :
    ∫⁻ w, (if ∃ n, (traj (domStep cstep T T' keep lump) y w n).2 = true then
        F (domOut (domStep cstep T T' keep lump) y w k) else 0) ∂(iidMeasure ν) ≤ W y := by
  set g := domStep cstep T T' keep lump with hg
  have hgm : ∀ x y, MeasurableSet {ξ | g x ξ = y} := measurableSet_domStep_eq cstep hc T T' keep lump
  have hflag : ∀ z, MeasurableSet (flagSet g z) := by
    intro z
    have : flagSet g z =
        ⋃ z' ∈ {z' : RState S d J × Bool | z.2 = false ∧ z'.2 = true}, {ξ | g z ξ = z'} := by
      ext ξ; simp [flagSet]
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun z' _ => hgm z z'
  set A : RState S d J × Bool → Fin (d + 1) × U → ℝ≥0∞ := fun z ξ => (flagSet g z).indicator 1 ξ
  have hA : ∀ z, Measurable (A z) := fun z => measurable_one.indicator (hflag z)
  set H : RState S d J × Bool → (ℕ → Fin (d + 1) × U) → ℝ≥0∞ := fun z w => F (domOut g z w k)
  have hH : ∀ z, Measurable (H z) := fun z =>
    (Measurable.of_discrete (f := F)).comp ((measurable_pi_apply k).comp
      (measurable_recOut_traj g hgm z))
  have hInvT : ∀ w n, Inv (traj g y w n) := by
    intro w n
    induction n with
    | zero => exact hy
    | succ n ih => exact hInv _ _ ih
  have hR : ∀ z, Measurable (flagReward g Φ z) := fun z =>
    measurable_comp_of_fibers (g z) (hgm z)
      (fun z' => if z.2 = false ∧ z'.2 = true then Φ z'.1 else 0)
  -- the integrand is the sum over the step that sets the flag
  have hpt : ∀ w, (if ∃ n, (traj g y w n).2 = true then F (domOut g y w k) else 0) =
      ∑' n, A (traj g y w n) (w n) * H (traj g y w (n + 1)) (fun j => w (n + 1 + j)) := by
    intro w
    by_cases hFl : ∃ n, (traj g y w n).2 = true
    · simp only [hFl, ↓reduceIte]
      have hm0 : Nat.find hFl ≠ 0 := by
        intro h0
        have := Nat.find_spec hFl
        rw [h0] at this
        simp [traj, hy2] at this
      obtain ⟨n0, hn0⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hfl0 : w n0 ∈ flagSet g (traj g y w n0) := by
        refine ⟨?_, ?_⟩
        · have := Nat.find_min hFl (show n0 < Nat.find hFl by omega)
          simpa using this
        · have := Nat.find_spec hFl
          rw [hn0] at this
          exact this
      rw [tsum_eq_single n0]
      · simp only [A, Set.indicator_of_mem hfl0, Pi.one_apply, one_mul, H]
        rw [← domOut_eq_tail cstep T T' keep lump R hlump y hyv w (n0 + 1)]
      · intro n hn
        have : w n ∉ flagSet g (traj g y w n) := fun h =>
          hn (flagSet_unique cstep T T' keep lump y w n n0 h hfl0)
        simp [A, Set.indicator_of_notMem this]
    · simp only [hFl, ↓reduceIte]
      symm
      refine ENNReal.tsum_eq_zero.2 fun n => ?_
      have : w n ∉ flagSet g (traj g y w n) := fun h => hFl ⟨n + 1, h.2⟩
      simp [A, Set.indicator_of_notMem this]
  have hfn : ∀ n, Measurable fun w =>
      A (traj g y w n) (w n) * H (traj g y w (n + 1)) (fun j => w (n + 1 + j)) := fun n =>
    (measurable_traj_comp g hgm y n (fun z w => A z (w n))
      fun z => (hA z).comp (measurable_pi_apply n)).mul
    (measurable_traj_comp g hgm y (n + 1) (fun z w => H z (fun j => w (n + 1 + j)))
      fun z => (hH z).comp (measurable_pi_iff.2 fun j => measurable_pi_apply (n + 1 + j)))
  have hrn : ∀ n, Measurable fun w : ℕ → Fin (d + 1) × U => flagReward g Φ (traj g y w n) (w n) :=
    fun n => measurable_traj_comp g hgm y n (fun z w => flagReward g Φ z (w n))
      fun z => (hR z).comp (measurable_pi_apply n)
  calc ∫⁻ w, (if ∃ n, (traj g y w n).2 = true then F (domOut g y w k) else 0) ∂(iidMeasure ν)
      = ∑' n, ∫⁻ w, A (traj g y w n) (w n) * H (traj g y w (n + 1)) (fun j => w (n + 1 + j))
          ∂(iidMeasure ν) := by
        simp_rw [hpt]
        exact lintegral_tsum fun n => (hfn n).aemeasurable
    _ ≤ ∑' n, ∫⁻ w, flagReward g Φ (traj g y w n) (w n) ∂(iidMeasure ν) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [lintegral_traj_markov g ν hgm A hA H hH y n]
        refine lintegral_mono fun w => ?_
        by_cases hfl : w n ∈ flagSet g (traj g y w n)
        · simp only [A, Set.indicator_of_mem hfl, Pi.one_apply, one_mul]
          have hfree : domFree T (g (traj g y w n) (w n)) := Or.inl hfl.2
          have hH' : ∀ w', H (traj g y w (n + 1)) w' =
              F (recOut (traj (rstep cstep) (g (traj g y w n) (w n)).1 w') k) := by
            intro w'
            simp only [H, domOut]
            congr 2
            funext t
            rw [show traj g y w (n + 1) = g (traj g y w n) (w n) from rfl,
              traj_domStep_of_free cstep T T' keep lump _ hfree w' t]
          simp_rw [hH']
          have hrw : flagReward g Φ (traj g y w n) (w n) = Φ (g (traj g y w n) (w n)).1 := by
            simp only [flagReward, hfl.1, hfl.2, and_self, ↓reduceIte]
          rw [hrw]
          exact hΦ _ _ (hInvT w n) hfl
        · simp [A, Set.indicator_of_notMem hfl]
    _ = ∫⁻ w, ∑' n, flagReward g Φ (traj g y w n) (w n) ∂(iidMeasure ν) :=
        (lintegral_tsum fun n => (hrn n).aemeasurable).symm
    _ = FrogModel.LinSys.least (fkKernel g (fun _ _ => 1) ν) (fkRhs (flagReward g Φ) ν) y :=
        lintegral_tsum_traj_eq_least g (flagReward g Φ) ν hgm hR y
    _ ≤ W y := FrogModel.LinSys.least_le_of_super _ _ W hW y

open Classical in
theorem map_domOut_tail_le [MeasurableSpace U] [Countable S] (cstep : S → U → ℕ × S)
    (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (R : S → S → Prop) (hlump : ∀ x, Dom R x (lump x))
    (ν : Measure (Fin (d + 1) × U)) [IsProbabilityMeasure ν] (hν : ν {ξ | ξ.1 = 0} ≠ 0)
    (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ⊤) (k : Fin J)
    (y : RState S d J × Bool) (hyv : Valid y.1) (hy2 : y.2 = false) (hye : y.1.e ≤ T)
    (hyo : ∀ k : Fin J, (k : ℕ) < y.1.i → y.1.out k ≤ y.1.e) (t : ℕ) (ht : T < t) (F : ℕ∞ → ℝ≥0∞) (hF : ∀ v : ℕ∞, (t : ℕ∞) ≤ v → θ ^ t ≤ F v) :
    (iidMeasure ν).map (domOut (domStep cstep T T' keep lump) y) {B | (t : ℕ∞) ≤ B k} ≤
      θ⁻¹ ^ t * ∫⁻ w, (if ∃ n, (traj (domStep cstep T T' keep lump) y w n).2 = true then
        F (domOut (domStep cstep T T' keep lump) y w k) else 0)
        ∂(iidMeasure ν) := by
  set g := domStep cstep T T' keep lump with hg
  have hgm : ∀ x y, MeasurableSet {ξ | g x ξ = y} := measurableSet_domStep_eq cstep hc T T' keep lump
  have hmeas : Measurable (domOut g y) := measurable_recOut_traj g hgm y
  have hset : MeasurableSet {B : Fin J → ℕ∞ | (t : ℕ∞) ≤ B k} :=
    (measurable_pi_apply k) (MeasurableSet.of_discrete (s := Set.Ici (t : ℕ∞)))
  rw [Measure.map_apply hmeas hset]
  have hFl : MeasurableSet {w : ℕ → Fin (d + 1) × U | ∃ n, (traj g y w n).2 = true} := by
    have : {w : ℕ → Fin (d + 1) × U | ∃ n, (traj g y w n).2 = true} =
        ⋃ n, ⋃ z ∈ {z : RState S d J × Bool | z.2 = true}, {w | traj g y w n = z} := by
      ext w; simp
    rw [this]
    exact MeasurableSet.iUnion fun n =>
      MeasurableSet.biUnion (Set.to_countable _) fun z _ => measurableSet_traj_eq g hgm y n z
  have hf : Measurable fun w : ℕ → Fin (d + 1) × U =>
      if ∃ n, (traj g y w n).2 = true then F (domOut g y w k) else 0 :=
    Measurable.ite hFl ((Measurable.of_discrete (f := F)).comp ((measurable_pi_apply k).comp hmeas))
      measurable_const
  have hsub : (iidMeasure ν) (domOut g y ⁻¹' {B | (t : ℕ∞) ≤ B k}) ≤
      (iidMeasure ν) {w | θ ^ t ≤ if ∃ n, (traj g y w n).2 = true then
        F (domOut g y w k) else 0} := by
    refine measure_mono_ae ?_
    filter_upwards [ae_exitCount_unbounded ν hν] with w hw hwt
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hwt ⊢
    by_cases hF' : ∃ n, (traj g y w n).2 = true
    · simp only [hF', ↓reduceIte]
      exact hF _ hwt
    · exfalso
      have hunf : ∀ n, (traj g y w n).2 = false := fun n => by
        simpa using fun h => hF' ⟨n, h⟩
      obtain ⟨n, hn⟩ :=
        exists_absorbed_of_unflagged cstep T T' keep lump R hlump y hy2 hye w hw hunf
      have hle := domOut_le_of_absorbed_unflagged cstep T T' keep lump R hlump y hyv hy2 hye hyo w n
        hn (hunf n) k
      have : ((t : ℕ) : ℕ∞) ≤ (T : ℕ∞) := hwt.trans hle
      exact absurd (Nat.cast_le.1 this) (not_le.2 ht)
  have hm := mul_meas_ge_le_lintegral (μ := iidMeasure ν) hf (θ ^ t)
  calc (iidMeasure ν) (domOut g y ⁻¹' {B | (t : ℕ∞) ≤ B k})
      ≤ (iidMeasure ν) {w | θ ^ t ≤ if ∃ n, (traj g y w n).2 = true then
          F (domOut g y w k) else 0} := hsub
    _ = θ⁻¹ ^ t * (θ ^ t * (iidMeasure ν) {w | θ ^ t ≤ if ∃ n, (traj g y w n).2 = true then
          F (domOut g y w k) else 0}) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel hθ0 hθtop, one_pow, one_mul]
    _ ≤ θ⁻¹ ^ t * ∫⁻ w, (if ∃ n, (traj g y w n).2 = true then F (domOut g y w k) else 0)
          ∂(iidMeasure ν) := by gcongr

end FrogModel.Engine
