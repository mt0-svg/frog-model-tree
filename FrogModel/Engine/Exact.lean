module

public import FrogModel.Engine.Core
public import FrogModel.LemmaX.Psi

@[expose] public section

/-!
# The root engine: the root chain computes `Psi` (Lemma 6.2 of the paper, deterministic part)

Drive the root chain from the pools: step `t` takes the direction `D t` and the next unused
uniform of the pool of that direction (`poolDrive`). Then child `c` sees exactly the uniforms
`V c.succ 0, V c.succ 1, ...` in order (`childAt_poolDrive`), the returns delivered are the sums of
the curves of the children alone (`cumDeliv_poolDrive`), and the output of frog `k` from the start
is `psiG` of the child curves at `k + 1` (`outPsi_start_eq_psiG`), the map `Psi` of
Lemma 4.2 of the paper (`FrogModel.LemmaX.psiG`), whenever the directions exit infinitely often
(otherwise `psiG` counts the finitely many exits where the chain records `⊤`; this event is null).
-/

open scoped ENNReal
open FrogModel.LemmaX

namespace FrogModel.Engine

variable {S U : Type*} {d J : ℕ}

theorem dirCountN_succ (D : ℕ → Fin (d + 1)) (a : Fin (d + 1)) (n : ℕ) :
    dirCountN D a (n + 1) = dirCountN D a n + if D n = a then 1 else 0 := by
  unfold dirCountN
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem chainDeliv_succ (cstep : S → U → ℕ × S) (s : S) (v : ℕ → U) (m : ℕ) :
    chainDeliv cstep s v (m + 1) =
      chainDeliv cstep s v m + (cstep (chainState cstep s v m) (v m)).1 := by
  unfold chainDeliv
  rw [Finset.sum_range_succ]

theorem chainDeliv_mono (cstep : S → U → ℕ × S) (s : S) (v : ℕ → U) :
    Monotone (chainDeliv cstep s v) :=
  monotone_nat_of_le_succ fun m => by rw [chainDeliv_succ]; omega

theorem chainCurve_mono (cstep : S → U → ℕ × S) (s : S) (v : ℕ → U) :
    Monotone (chainCurve cstep s v) := fun i i' h => by
  unfold chainCurve
  exact_mod_cast chainDeliv_mono cstep s v (Nat.sub_le_sub_right h 1)

theorem childAt_succ_of_exit (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U)
    (n : ℕ) (h : (w n).1 = 0) : childAt cstep σ w (n + 1) = childAt cstep σ w n := by
  rw [childAt, dite_eq_left h]

theorem childAt_succ_of_entry (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U)
    (n : ℕ) (c₀ : Fin d) (h : (w n).1 = c₀.succ) :
    childAt cstep σ w (n + 1) = Function.update (childAt cstep σ w n) c₀
      (cstep (childAt cstep σ w n c₀) (w n).2).2 := by
  have h0 : (w n).1 ≠ 0 := h ▸ Fin.succ_ne_zero c₀
  have hp : (w n).1.pred h0 = c₀ := by simp [h]
  rw [childAt, dite_eq_right h0, hp]

theorem delivAt_of_exit (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U)
    (n : ℕ) (h : (w n).1 = 0) : delivAt cstep σ w n = 0 := by
  rw [delivAt, dite_eq_left h]

theorem delivAt_of_entry (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U)
    (n : ℕ) (c₀ : Fin d) (h : (w n).1 = c₀.succ) :
    delivAt cstep σ w n = (cstep (childAt cstep σ w n c₀) (w n).2).1 := by
  have h0 : (w n).1 ≠ 0 := h ▸ Fin.succ_ne_zero c₀
  have hp : (w n).1.pred h0 = c₀ := by simp [h]
  rw [delivAt, dite_eq_right h0, hp]

/-- Child `c` sees the uniforms of its pool in order. -/
theorem childAt_poolDrive (cstep : S → U → ℕ × S) (σ : Fin d → S) (D : ℕ → Fin (d + 1))
    (V : Fin (d + 1) → ℕ → U) (n : ℕ) (c : Fin d) :
    childAt cstep σ (poolDrive D V) n c = chainState cstep (σ c) (V c.succ) (dirCountN D c.succ n) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [dirCountN_succ]
    rcases Fin.eq_zero_or_eq_succ (D n) with h0 | ⟨c₀, hc₀⟩
    · rw [childAt_succ_of_exit cstep σ _ n h0, ih,
        ite_eq_right fun (e : D n = c.succ) => Fin.succ_ne_zero c (e ▸ h0)]
      rfl
    · rw [childAt_succ_of_entry cstep σ _ n c₀ hc₀]
      by_cases hc : c = c₀
      · subst hc
        rw [Function.update_self, ite_eq_left hc₀, ih]
        simp only [poolDrive, hc₀]
        rfl
      · rw [Function.update_of_ne hc, ih, ite_eq_right fun (e : D n = c.succ) => hc (Fin.succ_injective _ (e ▸ hc₀))]
        rfl

/-- The returns delivered are the sums of the curves of the children alone. -/
theorem cumDeliv_poolDrive (cstep : S → U → ℕ × S) (σ : Fin d → S) (D : ℕ → Fin (d + 1))
    (V : Fin (d + 1) → ℕ → U) (n : ℕ) :
    cumDeliv cstep σ (poolDrive D V) n =
      ∑ c : Fin d, chainDeliv cstep (σ c) (V c.succ) (dirCountN D c.succ n) := by
  induction n with
  | zero => simp [cumDeliv, dirCountN, chainDeliv]
  | succ n ih =>
    rw [cumDeliv, Finset.sum_range_succ, ← cumDeliv, ih]
    simp only [dirCountN_succ]
    have hterm : ∀ c : Fin d,
        chainDeliv cstep (σ c) (V c.succ) (dirCountN D c.succ n + if D n = c.succ then 1 else 0) =
          chainDeliv cstep (σ c) (V c.succ) (dirCountN D c.succ n) +
            if D n = c.succ then
              (cstep (chainState cstep (σ c) (V c.succ) (dirCountN D c.succ n))
                (V c.succ (dirCountN D c.succ n))).1 else 0 := fun c => by
      split_ifs
      · exact chainDeliv_succ cstep _ _ _
      · simp
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_add_distrib]
    congr 1
    rcases Fin.eq_zero_or_eq_succ (D n) with h0 | ⟨c₀, hc₀⟩
    · rw [delivAt_of_exit cstep σ _ n h0]
      symm
      exact Finset.sum_eq_zero fun c _ => ite_eq_right fun (e : D n = c.succ) => Fin.succ_ne_zero c (e ▸ h0)
    · rw [delivAt_of_entry cstep σ _ n c₀ hc₀, Finset.sum_eq_single c₀]
      · rw [ite_eq_left hc₀, childAt_poolDrive]
        simp only [poolDrive, hc₀]
      · intro c _ hc
        exact ite_eq_right fun (e : D n = c.succ) => hc (Fin.succ_injective _ (e ▸ hc₀))
      · simp

theorem exitCount_poolDrive (D : ℕ → Fin (d + 1)) (V : Fin (d + 1) → ℕ → U) (n : ℕ) :
    exitCount (poolDrive D V) n = dirCountN D 0 n := rfl

theorem dirCount_eq_dirCountN (D : ℕ → Fin (d + 1)) (a : Fin (d + 1)) (n : ℕ) :
    dirCount D a n = dirCountN D a n := by
  rw [dirCount_coe]; rfl

/-- `T_j` of `Psi` at a finite `n`, for the curves of the chain from the pools. -/
theorem psiT_chainCurve (cstep : S → U → ℕ × S) (F : S) (D : ℕ → Fin (d + 1))
    (V : Fin (d + 1) → ℕ → U) (j n : ℕ) :
    psiT (fun c => chainCurve cstep F (V c.succ)) D j n =
      ((j + cumDeliv cstep (fun _ => F) (poolDrive D V) n : ℕ) : ℕ∞) := by
  rw [cumDeliv_poolDrive]
  unfold psiT
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dirCount_eq_dirCountN]
  unfold childRet
  split_ifs with h0
  · have : dirCountN D c.succ n = 0 := by exact_mod_cast h0
    simp [this, chainDeliv]
  · rw [show ((dirCountN D c.succ n : ℕ∞) + 1) = ((dirCountN D c.succ n + 1 : ℕ) : ℕ∞) by push_cast; rfl,
      extCurve_coe _ (chainCurve_mono cstep F _)]
    simp [chainCurve]

/-- `N(j)` of `Psi` is the least finite `n` with `T_j(n) ≤ n`, and `⊤` if there is none. -/
theorem psiN_eq_find (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ)
    (h : ∃ n : ℕ, psiT G D j n ≤ n) : psiN G D j = (Nat.find h : ℕ) := by
  refine le_antisymm (psiN_le G D j _ (Nat.find_spec h)) ?_
  refine le_sInf fun m hm => ?_
  induction m using ENat.recTopCoe with
  | top => exact le_top
  | coe m => exact_mod_cast Nat.find_min' h hm

theorem psiN_eq_top_of_not (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ)
    (h : ¬ ∃ n : ℕ, psiT G D j n ≤ n) : psiN G D j = ⊤ :=
  (psiN_eq_top_iff G D j).2 fun n => lt_of_not_ge fun hn => h ⟨n, hn⟩

/-- **The root chain driven by the pools computes `Psi`.** -/
theorem outPsi_start_eq_psiG (cstep : S → U → ℕ × S) (F : S) (D : ℕ → Fin (d + 1))
    (V : Fin (d + 1) → ℕ → U) (hD : ∀ m, ∃ n, m ≤ dirCountN D 0 n) (k : Fin J) :
    outPsi cstep (start F) (poolDrive D V) k =
      psiG (fun c => chainCurve cstep F (V c.succ)) D (k + 1) := by
  have hneed : ∀ n, need cstep (start F : RState S d J) (poolDrive D V) k n =
      (k + 1) + cumDeliv cstep (fun _ => F) (poolDrive D V) n := fun n => by
    simp only [need, start]; omega
  have hiff : ∀ n : ℕ, (psiT (fun c => chainCurve cstep F (V c.succ)) D (k + 1) n ≤ n ↔
      need cstep (start F : RState S d J) (poolDrive D V) k n ≤ n) := fun n => by
    rw [psiT_chainCurve, hneed]; exact_mod_cast Iff.rfl
  have hk : ¬ (k : ℕ) < (start F : RState S d J).i := by simp [start]
  unfold outPsi psiG
  rw [ite_eq_right hk]
  by_cases h : ∃ n, need cstep (start F : RState S d J) (poolDrive D V) k n ≤ n
  · have h' : ∃ n : ℕ, psiT (fun c => chainCurve cstep F (V c.succ)) D (k + 1) n ≤ n :=
      let ⟨n, hn⟩ := h; ⟨n, (hiff n).2 hn⟩
    rw [dite_eq_left h, psiN_eq_find _ _ _ h', dirCount_eq_dirCountN, exitCount_poolDrive]
    have : Nat.find h' = Nat.find h := by
      rw [Nat.find_eq_iff]
      exact ⟨(hiff _).2 (Nat.find_spec h), fun n hn hn' => Nat.find_min h hn ((hiff n).1 hn')⟩
    simp [this, start]
  · have h' : ¬ ∃ n : ℕ, psiT (fun c => chainCurve cstep F (V c.succ)) D (k + 1) n ≤ n :=
      fun ⟨n, hn⟩ => h ⟨n, (hiff n).1 hn⟩
    rw [dite_eq_right h, psiN_eq_top_of_not _ _ _ h']
    -- infinitely many exits: the count of exits over all steps is `⊤`
    symm
    refine ENat.eq_top_iff_forall_ge.2 fun m => ?_
    obtain ⟨n, hn⟩ := hD m
    calc (m : ℕ∞) ≤ dirCountN D 0 n := by exact_mod_cast hn
      _ = dirCount D 0 n := (dirCount_eq_dirCountN D 0 n).symm
      _ ≤ dirCount D 0 ⊤ := dirCount_mono D 0 le_top

end FrogModel.Engine
