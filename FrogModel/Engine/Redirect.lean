module

public import FrogModel.Engine.Core

@[expose] public section

/-!
# The root engine: the redirected chain dominates (Lemma 6.4 of the paper)

A redirected chain moves on `RState S d J × Z` (`Z` carries anything the rule reads, a stop flag
for instance) by a step `g` whose state part is always a real step followed by a redirect to a
dominating state: `Dom R (rstep cstep x ξ) (g (x, z) ξ).1`, with `R` a simulation of the child
chain. If it redirects only before some time `n` along the inputs `w` (after `n` its state part
moves as the real chain), its recorded outputs are at least the real outputs, for the same
inputs: `le_recOut_of_redirect`. The proof is an induction on `n`: the real formula `outPsi` is
unchanged by a real step (`outPsi_rstep`) and increases under a redirect (`outPsi_le_of_dom`).
-/

open scoped ENNReal

namespace FrogModel.Engine

variable {S U Z : Type*} {d J : ℕ}

theorem childAt_sim (cstep : S → U → ℕ × S) (R : S → S → Prop) (hR : IsSim cstep R)
    (σ σ' : Fin d → S) (hσ : ∀ c, R (σ c) (σ' c)) (w : ℕ → Fin (d + 1) × U) (n : ℕ) (c : Fin d) :
    R (childAt cstep σ w n c) (childAt cstep σ' w n c) := by
  induction n generalizing c with
  | zero => exact hσ c
  | succ n ih =>
    simp only [childAt]
    split_ifs with h
    · exact ih c
    · by_cases hc : c = (w n).1.pred h
      · subst hc
        simp only [Function.update_self]
        exact (hR _ _ (ih _) (w n).2).2
      · simp only [Function.update_of_ne hc]
        exact ih c

theorem cumDeliv_le_of_sim (cstep : S → U → ℕ × S) (R : S → S → Prop) (hR : IsSim cstep R)
    (σ σ' : Fin d → S) (hσ : ∀ c, R (σ c) (σ' c)) (w : ℕ → Fin (d + 1) × U) (n : ℕ) :
    cumDeliv cstep σ w n ≤ cumDeliv cstep σ' w n := by
  unfold cumDeliv
  refine Finset.sum_le_sum fun t _ => ?_
  unfold delivAt
  split_ifs with h
  · exact le_rfl
  · exact (hR _ _ (childAt_sim cstep R hR σ σ' hσ w t _) (w t).2).1

/-- **The formula is monotone under domination**: the output is monotone in the
future deliveries of the children (proof of Lemma 6.4), pathwise. -/
theorem outPsi_le_of_dom (cstep : S → U → ℕ × S) (R : S → S → Prop) (hR : IsSim cstep R)
    (x y : RState S d J) (hxy : Dom R x y) (w : ℕ → Fin (d + 1) × U) :
    outPsi cstep x w ≤ outPsi cstep y w := by
  intro k
  obtain ⟨hi, he, hp, hout, hσ⟩ := hxy
  have hneed : ∀ n, need cstep x w k n ≤ need cstep y w k n := fun n => by
    unfold need
    rw [hi, hp]
    exact Nat.add_le_add_left (cumDeliv_le_of_sim cstep R hR x.σ y.σ hσ w n) _
  unfold outPsi
  by_cases hk : (k : ℕ) < x.i
  · rw [ite_eq_left hk, ite_eq_left (hi ▸ hk), hout]
  rw [ite_eq_right hk, ite_eq_right (hi ▸ hk)]
  by_cases h' : ∃ n, need cstep y w k n ≤ n
  · have h : ∃ n, need cstep x w k n ≤ n := ⟨Nat.find h', (hneed _).trans (Nat.find_spec h')⟩
    rw [dite_eq_left h, dite_eq_left h', he]
    have hf : Nat.find h ≤ Nat.find h' := Nat.find_min' h ((hneed _).trans (Nat.find_spec h'))
    exact Nat.cast_le.2 (Nat.add_le_add_left (exitCount_mono w hf) _)
  · rw [dite_eq_right h']
    exact le_top

theorem valid_of_dom (R : S → S → Prop) (x y : RState S d J) (hxy : Dom R x y) (hx : Valid x) :
    Valid y := by
  obtain ⟨hi, -, hp, hout, -⟩ := hxy
  exact ⟨fun h => hp ▸ hx.1 (hi ▸ h), fun k hk => hout ▸ hx.2 k (hi ▸ hk)⟩

theorem iInf_succ_of_le {α : Type*} [CompleteLattice α] (f : ℕ → α) (h : f 1 ≤ f 0) :
    ⨅ t, f t = ⨅ t, f (t + 1) := by
  refine le_antisymm (le_iInf fun t => iInf_le _ (t + 1)) (le_iInf fun t => ?_)
  cases t with
  | zero => exact (iInf_le _ 0).trans h
  | succ t => exact iInf_le _ t

/-- The real chain and a chain that follows it step by step have the same trajectory. -/
theorem traj_fst_eq (cstep : S → U → ℕ × S)
    (g : RState S d J × Z → Fin (d + 1) × U → RState S d J × Z) (x : RState S d J) (z : Z)
    (w : ℕ → Fin (d + 1) × U)
    (hg : ∀ k, (traj g (x, z) w (k + 1)).1 = rstep cstep (traj g (x, z) w k).1 (w k)) (k : ℕ) :
    (traj g (x, z) w k).1 = traj (rstep cstep) x w k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [hg k, ih]; rfl

/-- **Lemma 6.4, pathwise.** A chain that redirects to dominating states, and only before time
`n`, has outputs at least the outputs of the real chain, for the same inputs. -/
theorem le_recOut_of_redirect (cstep : S → U → ℕ × S) (R : S → S → Prop) (hR : IsSim cstep R)
    (g : RState S d J × Z → Fin (d + 1) × U → RState S d J × Z)
    (hg : ∀ x z ξ, Dom R (rstep cstep x ξ) (g (x, z) ξ).1) (n : ℕ) :
    ∀ (x : RState S d J) (z : Z) (w : ℕ → Fin (d + 1) × U), Valid x →
      (∀ k, n ≤ k → (traj g (x, z) w (k + 1)).1 = rstep cstep (traj g (x, z) w k).1 (w k)) →
      outPsi cstep x w ≤ recOut fun t => (traj g (x, z) w t).1 := by
  induction n with
  | zero =>
    intro x z w hx hn
    have e : (fun t => (traj g (x, z) w t).1) = traj (rstep cstep) x w :=
      funext (traj_fst_eq cstep g x z w fun k => hn k (Nat.zero_le k))
    rw [e, recOut_eq_outPsi cstep x hx w]
  | succ n ih =>
    intro x z w hx hn
    set y := g (x, z) (w 0) with hy
    have hdom := hg x z (w 0)
    have hvy : Valid y.1 := valid_of_dom R _ _ hdom (rstep_valid cstep x hx (w 0))
    have hshift : ∀ k, traj g (x, z) w (k + 1) = traj g y (fun t => w (t + 1)) k :=
      fun k => traj_succ_shift g (x, z) w k
    have hn' : ∀ k, n ≤ k → (traj g (y.1, y.2) (fun t => w (t + 1)) (k + 1)).1 =
        rstep cstep (traj g (y.1, y.2) (fun t => w (t + 1)) k).1 (w (k + 1)) := by
      intro k hk
      rw [Prod.mk.eta, ← hshift, ← hshift]
      exact hn (k + 1) (by omega)
    have hrec : (recOut fun t => (traj g (x, z) w t).1) =
        recOut fun t => (traj g (y.1, y.2) (fun t => w (t + 1)) t).1 := by
      funext k
      unfold recOut
      rw [iInf_succ_of_le (fun t => (traj g (x, z) w t).1.out k)]
      · simp only [hshift, Prod.mk.eta]
      · show (g (x, z) (w 0)).1.out k ≤ x.out k
        rw [← hdom.2.2.2.1]
        exact rstep_out_le cstep x hx (w 0) k
    rw [hrec, outPsi_rstep cstep x hx w]
    exact (outPsi_le_of_dom cstep R hR _ _ hdom _).trans (ih y.1 y.2 _ hvy hn')

end FrogModel.Engine
