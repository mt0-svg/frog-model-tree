module

public import FrogModel.D3.M1K.YSound
public import FrogModel.D3.M1K.Height0
public import FrogModel.D3.Interfaces.Checks

@[expose] public section

/-!
# A run that passes the checker satisfies `M1Run.Holds`

`runOf stAt wt` reads the stored heights `stAt h` and the top rows `wt` as an `M1Run` (lanes over
`2^62`). If every height `h < 100` is valid (`validSt`), height `0` passes `check0`, every height
`1 ≤ h < 100` passes `checkStep` on height `h - 1`, and the top passes `checkTop` on height `99`, then
the run satisfies `M1Run.Holds` (`runOf_holds`): the hypotheses of Proposition 13.3 of the paper at
`(V, P, L, m) = (48, 96, 60, 100)` and the top `Wtil_q ≤ Wtop_q`, `q = 2..33`. If moreover
`checkMass wt mpk mass`, the masses `topMass` are the slots of `mpk` over `2^62` (`topMass_runOf`).
-/

open FrogModel.Lanes FrogModel.D3.Iface

namespace FrogModel.D3.M1K

/-- The run of the stored heights `stAt h` and the top rows `wt` (entry `q - 2` the row `Wtil_q`). -/
noncomputable def runOf (stAt : ℕ → St) (wt : List ℕ) : M1Run where
  rho h := rhoR (stAt h)
  K h := KR (stAt h)
  Wt q x f := if 2 ≤ q ∧ q ≤ 33 ∧ x ≤ V ∧ f ≤ 3 then (lane (getR wt (q - 2)) (4 * x + f) : ℝ) / 2 ^ 62 else 0

/-! ## Leaves -/

theorem offEq_lane (a b : ℕ) (h : offEq a b = true) (l : ℕ) (hl : 1 ≤ l) : lane a l = lane b l := by
  unfold offEq at h
  have h' := Nat.eq_of_beq_eq_true h
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have e : ∀ x, lane x (k + 1) =
      Nat.mod (Nat.shiftRight (Nat.shiftRight x S) (Nat.mul S k)) (Nat.pow 2 S) := by
    intro x
    show (x >>> (S * (k + 1))) % 2 ^ S = ((x >>> S) >>> (S * k)) % 2 ^ S
    rw [Nat.mul_succ, Nat.add_comm, Nat.shiftRight_add]
  rw [e a, e b, h']

theorem sum_quad (g : ℕ → ℝ) (n : ℕ) :
    ∑ a ∈ Finset.range n, ∑ f ∈ Finset.range 4, g (4 * a + f) = ∑ l ∈ Finset.range (4 * n), g l := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 4 * (n + 1) = 4 * n + 4 by ring, Finset.sum_range_add]

theorem lane_sum_real (r : ℕ) (hr : validRow r = true) :
    ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range 4, (lane r (4 * a + f) : ℝ) / 2 ^ 62 = 1 := by
  unfold validRow at hr
  simp only [Bool.and_eq_true, Nat.beq_eq] at hr
  have hsum := hr.2
  clear hr
  rw [sumLanes_eq] at hsum
  rw [sum_quad (fun l => (lane r l : ℝ) / 2 ^ 62), ← Finset.sum_div,
    show 4 * (V + 1) = NL from rfl, ← Nat.cast_sum, hsum, D_eq]
  norm_num

theorem zeroAbove_lawOf (s : St) (hs : validSt s = true) (t : ℕ) (ht : t ≤ 3) :
    zeroAbove (lawOf s t) t = true := by
  unfold validSt at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨-, -, h0⟩, ⟨-, h1⟩, ⟨-, h2⟩, -, h3⟩ := hs
  interval_cases t
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem probvec_rho (s : St) (hs : validSt s = true) : IsProbVec V 3 (rhoR s) := by
  have hr : validRow s.rho = true := by
    unfold validSt at hs
    simp only [Bool.and_eq_true] at hs
    exact hs.1.1
  clear hs
  refine ⟨fun a f => ?_, fun a f h => ?_, ?_⟩
  · unfold rhoR; split_ifs <;> positivity
  · unfold rhoR; rw [ite_eq_right (by omega)]
  · rw [← lane_sum_real s.rho hr]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun f hf => ?_
    simp only [Finset.mem_range] at ha hf
    unfold rhoR
    rw [ite_eq_left ⟨by omega, by omega⟩]

theorem probvec_K (s : St) (hs : validSt s = true) (t : ℕ) (ht : t ≤ 3) : IsProbVec V t (KR s t) := by
  have hr := validRow_lawOf s hs t
  have hz := (zeroAbove_iff _ _).mp (zeroAbove_lawOf s hs t ht)
  clear hs
  have hV : V = 48 := rfl
  have hNL : NL = 196 := rfl
  have hzero : ∀ a f, a ≤ V → f ≤ 3 → t < f → lane (lawOf s t) (4 * a + f) = 0 := fun a f ha hf htf =>
    hz _ (by omega) (by omega)
  refine ⟨fun a f => ?_, fun a f h => ?_, ?_⟩
  · unfold KR; split_ifs <;> positivity
  · unfold KR
    split_ifs with h'
    · rw [hzero a f h'.1 h'.2 (by omega)]; simp
    · rfl
  · rw [← lane_sum_real _ hr]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_range] at ha
    rw [← Finset.sum_range_add_sum_Ico _ (show t + 1 ≤ 4 by omega)]
    have : ∑ f ∈ Finset.Ico (t + 1) 4, (lane (lawOf s t) (4 * a + f) : ℝ) / 2 ^ 62 = 0 :=
      Finset.sum_eq_zero fun f hf => by
        simp only [Finset.mem_Ico] at hf
        rw [hzero a f (by omega) (by omega) (by omega)]; simp
    rw [this, add_zero]
    refine Finset.sum_congr rfl fun f hf => ?_
    simp only [Finset.mem_range] at hf
    unfold KR
    rw [ite_eq_left ⟨by omega, by omega⟩]

/-! ## The heights and the top -/

theorem step_sound (prev cur : St) (hp : validSt prev = true) (h : checkStep prev cur = true) :
    OffBottomLe V 3 (rhoR cur) (Rhat V P (rhoR prev) (KR prev)) ∧
      ∀ t ≤ 3, OffBottomLe V t (KR cur t) (KhatH V P 60 (rhoR prev) t) := by
  unfold checkStep at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hcl, hy⟩, hrho, ⟨hk0, hk1⟩, hk2, hk3⟩ := h
  refine ⟨fun a ha f hf hoff => ?_, fun t ht a ha f hf hoff => ?_⟩
  · have hl1 : 1 ≤ 4 * a + f := by omega
    unfold rhoR
    rw [ite_eq_left ⟨ha, hf⟩, offEq_lane _ _ hrho _ hl1]
    exact closure_sound prev hp hcl 2 a f (by simp only [P]; omega) ha hf
  · have hl1 : 1 ≤ 4 * a + f := by omega
    have hk : offEq (lawOf cur t) (getR (getL (yTabs prev).1 t) 1) = true := by
      interval_cases t
      · exact hk0
      · exact hk1
      · exact hk2
      · exact hk3
    unfold KR
    rw [ite_eq_left ⟨ha, by omega⟩, offEq_lane _ _ hk _ hl1, getR_eq, getL_eq]
    exact ytabs_sound prev hp hy t ht a ha f (by omega)

theorem top_sound (s : St) (wt : List ℕ) (hs : validSt s = true) (h : checkTop s wt = true) (q : ℕ)
    (hq2 : 2 ≤ q) (hq : q ≤ 33) (x : ℕ) (hx : x ≤ V) (f : ℕ) (hf : f ≤ 3) :
    (lane (getR wt (q - 2)) (4 * x + f) : ℝ) / 2 ^ 62 ≤ Wtop V P (rhoR s) (KR s) q x f := by
  unfold checkTop at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hcl, hw⟩ := h
  rw [natFold_and] at hw
  have hq' := hw (q - 2) (by omega)
  simp only [Nat.beq_eq, Nat.add_eq] at hq'
  rw [hq', Nat.sub_add_cancel hq2]
  exact closure_sound s hs hcl q x f (by simp only [P]; omega) hx hf

/-- **A run that passes the checker satisfies `M1Run.Holds`.** -/
theorem runOf_holds (stAt : ℕ → St) (wt : List ℕ) (hv : ∀ h < 100, validSt (stAt h) = true)
    (h0 : check0 (stAt 0) = true)
    (hstep : ∀ h, 1 ≤ h → h < 100 → checkStep (stAt (h - 1)) (stAt h) = true)
    (htop : checkTop (stAt 99) wt = true) : (runOf stAt wt).Holds := by
  obtain ⟨hr0, hk0⟩ := height0_sound _ h0
  refine ⟨⟨fun h hh => probvec_rho _ (hv h hh), fun h hh t ht => probvec_K _ (hv h hh) t ht, hr0, hk0,
    fun h h1 hh => step_sound _ _ (hv (h - 1) (by omega)) (hstep h h1 hh)⟩, ?_⟩
  intro q hq2 hq x hx f hf
  show (if 2 ≤ q ∧ q ≤ 33 ∧ x ≤ V ∧ f ≤ 3 then (lane (getR wt (q - 2)) (4 * x + f) : ℝ) / 2 ^ 62 else 0) ≤ _
  rw [ite_eq_left ⟨hq2, hq, hx, hf⟩]
  exact top_sound _ wt (hv 99 (by norm_num)) htop q hq2 hq x hx f hf

/-! ## The masses -/

theorem checkMass_slots (wt : List ℕ) (mpk : ℕ) (mass : List (List ℕ)) (h : checkMass wt mpk mass = true)
    (k : ℕ) (hk : k < 32) (x : ℕ) (hx : x < 49) :
    slot64 mpk (49 * k + x) = ∑ g ∈ Finset.range 4, lane (getR wt k) (4 * x + g) := by
  unfold checkMass at h
  rw [natFold_and] at h
  have h1 := h k hk
  rw [natFold_and] at h1
  have h2 := h1 x hx
  simp only [Bool.and_eq_true, Nat.beq_eq] at h2
  have e1 : slot64 mpk (49 * k + x) = slot64 mpk ((Nat.mul 49 k).add x) := rfl
  rw [e1, h2.1, natFold_sum]
  rfl

/-- **The masses of the top**: `topMass` of the run is the slot `49 (k - 1) + x` of `mpk` over `2^62`. -/
theorem topMass_runOf (stAt : ℕ → St) (wt : List ℕ) (mpk : ℕ) (mass : List (List ℕ))
    (h : checkMass wt mpk mass = true) :
    ∀ k, 1 ≤ k → k ≤ 32 → ∀ x ≤ 48, topMass (runOf stAt wt) k x =
      ((mpk >>> (64 * (49 * (k - 1) + x))) % 2 ^ 64 : ℕ) / 2 ^ 62 := by
  intro k hk1 hk x hx
  have hs := checkMass_slots wt mpk mass h (k - 1) (by omega) x (by omega)
  have hs' : (mpk >>> (64 * (49 * (k - 1) + x))) % 2 ^ 64 = slot64 mpk (49 * (k - 1) + x) := rfl
  rw [hs', hs]
  unfold topMass
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf' : f ≤ 3 := by simp only [Finset.mem_range] at hf; omega
  show (if 2 ≤ k + 1 ∧ k + 1 ≤ 33 ∧ x ≤ V ∧ f ≤ 3 then
    (lane (getR wt (k + 1 - 2)) (4 * x + f) : ℝ) / 2 ^ 62 else 0) = _
  rw [ite_eq_left ⟨by omega, by omega, by simp only [V]; omega, hf'⟩,
    show k + 1 - 2 = k - 1 by omega]

end FrogModel.D3.M1K
