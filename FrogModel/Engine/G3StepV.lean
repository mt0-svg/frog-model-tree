module

public import FrogModel.Engine.G3Step

@[expose] public section

/-!
# The V side of the checker, move by move

Along the moves of a covered state `X` of phase `q = X.i + 1`, the accumulator of the checker holds
the moves in the phase (`vs`, the pack of `Fs`), the moves to the next phase (`vn`, the pack of
`Fn`), the absorbed moves (`av`). `InvV X a R` says that, for every output `o` that fits `X`, the
lane of `o` read off the accumulator (`valV`), in units of `2^-88`, is at most `R o`, a part of the
right side of the absorption system at `X`; and every lane is at most `sl (2^47 - 1)`, which keeps
the lanes apart at the end. Each move keeps the invariant with `R` raised by the weight of the
move times `tauV` at the state reached (`move_V`); so do the rows (`rowLoop_V`), the tail atoms
(`tailLoop_V`), the moves of a child (`child_V`) and of all children (`moves_V`).
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine.G3

open FrogModel.Cert FrogModel.LemmaX FrogModel.Lanes

/-- The lane of the V side at the increments `v`. -/
def valV (Fs Fn : ℕ → ℕ) (av : ℕ) (v : List ℕ) : ℕ :=
  Fs (laneIdx v) + (if v.headD 0 = 0 then Fn (laneIdx v.tail) else 0) +
    (if laneIdx v = 0 then av else 0)

/-- **The invariant of the V side** along the moves of `X`. -/
def InvV (X : RState CState 4 4) (a : G3K.Spec.Acc) (R : (Fin 4 → ℕ) → ℝ≥0∞) : Prop :=
  ∃ Fs Fn : ℕ → ℕ, a.vs = pack 96 (G3K.phase (X.i + 1)).nL Fs ∧
    a.vn = pack 96 (G3K.phase (X.i + 2)).nL Fn ∧
    (∀ l l', Fs l + Fn l' + a.av ≤ a.sl * (2 ^ 47 - 1)) ∧
    ∀ o, Fits o X → (valV Fs Fn a.av (incr o X.i X.e) : ℝ≥0∞) ≤ 2 ^ 88 * R o

theorem invV_zero (X : RState CState 4 4) : InvV X G3K.Spec.acc0 0 :=
  ⟨fun _ => 0, fun _ => 0, by simp [G3K.Spec.acc0, pack], by simp [G3K.Spec.acc0, pack],
    by simp [G3K.Spec.acc0], fun o _ => by simp [valV, G3K.Spec.acc0]⟩

theorem invV_mono (X : RState CState 4 4) (a : G3K.Spec.Acc) (R R' : (Fin 4 → ℕ) → ℝ≥0∞)
    (h : InvV X a R) (hR : ∀ o, R o ≤ R' o) : InvV X a R' := by
  obtain ⟨Fs, Fn, h1, h2, h3, h4⟩ := h
  exact ⟨Fs, Fn, h1, h2, h3, fun o ho => (h4 o ho).trans (by gcongr; exact hR o)⟩

/-- `floor(2^48 n / d) ≤ 2^48 n / d`. -/
theorem lo48_le (n d : ℕ) : (G3K.Spec.lo48 n d : ℝ≥0∞) ≤ 2 ^ 48 * n / d := by
  unfold G3K.Spec.lo48
  have h_two48 : G3K.Spec.two48 = 2 ^ 48 := by
    unfold G3K.Spec.two48
    norm_num
  rw [h_two48]
  by_cases hd0 : d = 0
  · rw [hd0]
    simp
  · have hd_pos : (d : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hd0
    have hd_ne_top : (d : ℝ≥0∞) ≠ ⊤ := by
      exact ENNReal.natCast_ne_top _
    rw [ENNReal.le_div_iff_mul_le (Or.inl hd_pos) (Or.inl hd_ne_top)]
    have h := Nat.div_mul_le_self (n * 2 ^ 48) d
    have h' : (n * 2 ^ 48 / d) * d ≤ 2 ^ 48 * n := by
      apply le_trans h
      rw [Nat.mul_comm]
    exact_mod_cast h'

/-- `ceil(2^48 n / d) ≥ 2^48 n / d`. -/
theorem up48_ge (n d : ℕ) (hd : 0 < d) : 2 ^ 48 * (n : ℝ≥0∞) / d ≤ G3K.Spec.up48 n d := by
  have hineq : n * 2 ^ 48 ≤ ((n * 2 ^ 48 + d - 1) / d) * d := by
    have hceil := Nat.ceilDiv_eq_add_pred_div (n * 2 ^ 48) d
    have hle := le_smul_ceilDiv (a := d) (b := n * 2 ^ 48) hd
    rw [hceil] at hle
    simpa [smul_eq_mul, mul_comm] using hle
  apply ENNReal.div_le_of_le_mul
  unfold G3K.Spec.up48
  unfold G3K.Spec.two48
  norm_num at *
  simpa [Nat.cast_mul, mul_comm] using Nat.mono_cast (α := ℝ≥0∞) hineq

/-- `Fits` reads only `i`, `e` and the outputs. -/
theorem fits_congr (o : Fin 4 → ℕ) (X X' : RState CState 4 4) (hi : X'.i = X.i) (he : X'.e = X.e)
    (hout : X'.out = X.out) : Fits o X' ↔ Fits o X := by
  unfold Fits; rw [hi, he, hout]

/-- **A target found by the checker**: its V' is the pack of lanes below `2^47`, and lane `o` of
it, in units of `2^-40`, is at most `Vs` at the state the chain takes. -/
theorem look_V (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X' : RState CState 4 4)
    (hi' : X'.i < 4) (he' : X'.e ≤ cand.T) (hp1 : 1 ≤ X'.p) (hp' : X'.p ≤ 16)
    (hwf : ∀ c, cand.ChildWF (X'.σ c)) :
    (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).v =
        pack 96 (G3K.phase (X'.i + 1)).nL
          (fun l => lane 96 l (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).v) ∧
      (∀ l, lane 96 l (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).v < 2 ^ 47) ∧
      ∀ o, Fits o X' →
        (lane 96 (laneIdx (incr o X'.i X'.e))
          (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).v : ℝ≥0∞) / 2 ^ 40 ≤
          Vs t o (keptOf t X', false) := by
  rcases look_cases t X' with hb | ⟨hl, hk⟩
  · rw [hb]
    refine ⟨?_, fun l => ?_, fun o _ => ?_⟩
    · simp [G3K.Spec.bad, lane, pack]
    · simp [G3K.Spec.bad, lane]
    · simp [G3K.Spec.bad, lane]
  · rw [hl]
    obtain ⟨hi2, he2, hp2, hout2⟩ := keptOf_fields t X'
    have hwf2 := keptOf_wf t X' hwf
    have hb := boundsOK_sound _ _ (entry_bounds t h (keptOf t X') hwf2 (by omega) hk)
    rw [hi2] at hb
    refine ⟨hb.1.symm, fun l => (hb.2.1 l).1, fun o ho => ?_⟩
    have hcov : Covered t (keptOf t X', false) :=
      ⟨rfl, show (keptOf t X').i < 4 by omega, show (keptOf t X').e ≤ cand.T by omega,
        show 1 ≤ (keptOf t X').p by omega, show (keptOf t X').p ≤ 16 by omega, hwf2, hk⟩
    have hF : Fits o (keptOf t X') := (fits_congr o X' _ hi2 he2 hout2).2 ho
    unfold Vs
    rw [if_pos ⟨hcov, hF⟩, hi2, he2]

/-- A lane added with the weight `lo48 num pd`: at most `2^88 num / pd` times the value it stands
for. -/
theorem add_lo_le (V L num pd : ℕ) (R τ : ℝ≥0∞) (hV : (V : ℝ≥0∞) ≤ 2 ^ 88 * R)
    (hL : (L : ℝ≥0∞) / 2 ^ 40 ≤ τ) :
    ((V + G3K.Spec.lo48 num pd * L : ℕ) : ℝ≥0∞) ≤ 2 ^ 88 * (R + num / pd * τ) := by
  push_cast
  rw [mul_add]
  refine add_le_add hV ?_
  have hL' : (L : ℝ≥0∞) = 2 ^ 40 * ((L : ℝ≥0∞) / 2 ^ 40) :=
    (ENNReal.mul_div_cancel (by positivity) (by simp)).symm
  calc (G3K.Spec.lo48 num pd : ℝ≥0∞) * L ≤ 2 ^ 48 * num / pd * L := by gcongr; exact lo48_le num pd
    _ = 2 ^ 88 * (num / pd * ((L : ℝ≥0∞) / 2 ^ 40)) := by
        set Y := (L : ℝ≥0∞) / 2 ^ 40
        rw [hL', mul_div_assoc]
        ring
    _ ≤ 2 ^ 88 * (num / pd * τ) := by gcongr

theorem valV_av (Fs Fn : ℕ → ℕ) (av x : ℕ) (v : List ℕ) :
    valV Fs Fn (av + x) v = valV Fs Fn av v + (if laneIdx v = 0 then x else 0) := by
  simp only [valV]; split_ifs <;> omega

theorem valV_fn (Fs Fn G : ℕ → ℕ) (av : ℕ) (v : List ℕ) :
    valV Fs (fun l => Fn l + G l) av v =
      valV Fs Fn av v + (if v.headD 0 = 0 then G (laneIdx v.tail) else 0) := by
  simp only [valV]; split_ifs <;> omega

theorem valV_fs (Fs Fn G : ℕ → ℕ) (av : ℕ) (v : List ℕ) :
    valV (fun l => Fs l + G l) Fn av v = valV Fs Fn av v + G (laneIdx v) := by
  simp only [valV]; omega

theorem lane_le (l n : ℕ) (h : lane 96 l n < 2 ^ 47) : lane 96 l n ≤ 2 ^ 47 - 1 := by omega

theorem two40_eq : G3K.Spec.two40 = 2 ^ 40 := by unfold G3K.Spec.two40; norm_num

/-! The fields after each kind of addition, stated on variables: the checker's arguments are
terms whose unfolding is costly, so the proofs rewrite with these and never unify an accumulator
with another. -/

section Fields
variable (x lo hi : ℕ) (tt : G3K.E) (a : G3K.Spec.Acc)

theorem addStop_vs : (G3K.Spec.addStop x a).vs = a.vs := by unfold G3K.Spec.addStop; rfl
theorem addStop_vn : (G3K.Spec.addStop x a).vn = a.vn := by unfold G3K.Spec.addStop; rfl
theorem addStop_av : (G3K.Spec.addStop x a).av = a.av := by unfold G3K.Spec.addStop; rfl
theorem addStop_ww : (G3K.Spec.addStop x a).ww = a.ww := by unfold G3K.Spec.addStop; rfl
theorem addStop_pp : (G3K.Spec.addStop x a).pp = a.pp + x := by unfold G3K.Spec.addStop; rfl
theorem addStop_sl : (G3K.Spec.addStop x a).sl = a.sl := by unfold G3K.Spec.addStop; rfl
theorem addStop_sh : (G3K.Spec.addStop x a).sh = a.sh := by unfold G3K.Spec.addStop; rfl
theorem addStop_ok : (G3K.Spec.addStop x a).ok = a.ok := by unfold G3K.Spec.addStop; rfl

theorem addAbs_vs : (G3K.Spec.addAbs lo a).vs = a.vs := by unfold G3K.Spec.addAbs; rfl
theorem addAbs_vn : (G3K.Spec.addAbs lo a).vn = a.vn := by unfold G3K.Spec.addAbs; rfl
theorem addAbs_av : (G3K.Spec.addAbs lo a).av = a.av + lo * 2 ^ 40 := by
  unfold G3K.Spec.addAbs; rw [← two40_eq]
theorem addAbs_ww : (G3K.Spec.addAbs lo a).ww = a.ww := by unfold G3K.Spec.addAbs; rfl
theorem addAbs_pp : (G3K.Spec.addAbs lo a).pp = a.pp := by unfold G3K.Spec.addAbs; rfl
theorem addAbs_sl : (G3K.Spec.addAbs lo a).sl = a.sl + lo := by unfold G3K.Spec.addAbs; rfl
theorem addAbs_sh : (G3K.Spec.addAbs lo a).sh = a.sh := by unfold G3K.Spec.addAbs; rfl
theorem addAbs_ok : (G3K.Spec.addAbs lo a).ok = a.ok := by unfold G3K.Spec.addAbs; rfl

theorem addNext_vs : (G3K.Spec.addNext lo hi tt a).vs = a.vs := by unfold G3K.Spec.addNext; rfl
theorem addNext_vn : (G3K.Spec.addNext lo hi tt a).vn = a.vn + lo * tt.v := by
  unfold G3K.Spec.addNext; rfl
theorem addNext_av : (G3K.Spec.addNext lo hi tt a).av = a.av := by unfold G3K.Spec.addNext; rfl
theorem addNext_ww : (G3K.Spec.addNext lo hi tt a).ww = a.ww + hi * tt.w := by
  unfold G3K.Spec.addNext; rfl
theorem addNext_pp : (G3K.Spec.addNext lo hi tt a).pp = a.pp := by unfold G3K.Spec.addNext; rfl
theorem addNext_sl : (G3K.Spec.addNext lo hi tt a).sl = a.sl + lo := by
  unfold G3K.Spec.addNext; rfl
theorem addNext_sh : (G3K.Spec.addNext lo hi tt a).sh = a.sh + hi := by
  unfold G3K.Spec.addNext; rfl
theorem addNext_ok : (G3K.Spec.addNext lo hi tt a).ok = (a.ok && decide (tt.flag ≤ 1)) := by
  unfold G3K.Spec.addNext; rfl

theorem addSame_vs : (G3K.Spec.addSame lo hi tt a).vs = a.vs + lo * tt.v := by
  unfold G3K.Spec.addSame; rfl
theorem addSame_vn : (G3K.Spec.addSame lo hi tt a).vn = a.vn := by unfold G3K.Spec.addSame; rfl
theorem addSame_av : (G3K.Spec.addSame lo hi tt a).av = a.av := by unfold G3K.Spec.addSame; rfl
theorem addSame_ww : (G3K.Spec.addSame lo hi tt a).ww = a.ww + hi * tt.w := by
  unfold G3K.Spec.addSame; rfl
theorem addSame_pp : (G3K.Spec.addSame lo hi tt a).pp = a.pp := by unfold G3K.Spec.addSame; rfl
theorem addSame_sl : (G3K.Spec.addSame lo hi tt a).sl = a.sl + lo := by
  unfold G3K.Spec.addSame; rfl
theorem addSame_sh : (G3K.Spec.addSame lo hi tt a).sh = a.sh + hi := by
  unfold G3K.Spec.addSame; rfl
theorem addSame_ok : (G3K.Spec.addSame lo hi tt a).ok = (a.ok && decide (tt.flag ≤ 1)) := by
  unfold G3K.Spec.addSame; rfl

end Fields

theorem invV_addStop (X : RState CState 4 4) (x : ℕ) (a : G3K.Spec.Acc) (R : (Fin 4 → ℕ) → ℝ≥0∞)
    (h : InvV X a R) : InvV X (G3K.Spec.addStop x a) R := by
  obtain ⟨Fs, Fn, h1, h2, h3, h4⟩ := h
  refine ⟨Fs, Fn, ?_, ?_, ?_, ?_⟩
  · rw [addStop_vs]; exact h1
  · rw [addStop_vn]; exact h2
  · rw [addStop_av, addStop_sl]; exact h3
  · rw [addStop_av]; exact h4

theorem invV_addAbs (X : RState CState 4 4) (lo : ℕ) (a : G3K.Spec.Acc)
    (R : (Fin 4 → ℕ) → ℝ≥0∞) (Fs Fn : ℕ → ℕ) (hvs : a.vs = pack 96 (G3K.phase (X.i + 1)).nL Fs)
    (hvn : a.vn = pack 96 (G3K.phase (X.i + 2)).nL Fn)
    (hb : ∀ l l', Fs l + Fn l' + (a.av + lo * 2 ^ 40) ≤ (a.sl + lo) * (2 ^ 47 - 1))
    (hval : ∀ o, Fits o X →
      (valV Fs Fn (a.av + lo * 2 ^ 40) (incr o X.i X.e) : ℝ≥0∞) ≤ 2 ^ 88 * R o) :
    InvV X (G3K.Spec.addAbs lo a) R := by
  refine ⟨Fs, Fn, ?_, ?_, ?_, ?_⟩
  · rw [addAbs_vs]; exact hvs
  · rw [addAbs_vn]; exact hvn
  · rw [addAbs_av, addAbs_sl]; exact hb
  · rw [addAbs_av]; exact hval

theorem invV_addNext (X : RState CState 4 4) (lo hi : ℕ) (tt : G3K.E) (a : G3K.Spec.Acc)
    (R : (Fin 4 → ℕ) → ℝ≥0∞) (Fs Fn : ℕ → ℕ) (hvs : a.vs = pack 96 (G3K.phase (X.i + 1)).nL Fs)
    (hvn : a.vn + lo * tt.v = pack 96 (G3K.phase (X.i + 2)).nL Fn)
    (hb : ∀ l l', Fs l + Fn l' + a.av ≤ (a.sl + lo) * (2 ^ 47 - 1))
    (hval : ∀ o, Fits o X → (valV Fs Fn a.av (incr o X.i X.e) : ℝ≥0∞) ≤ 2 ^ 88 * R o) :
    InvV X (G3K.Spec.addNext lo hi tt a) R := by
  refine ⟨Fs, Fn, ?_, ?_, ?_, ?_⟩
  · rw [addNext_vs]; exact hvs
  · rw [addNext_vn]; exact hvn
  · rw [addNext_av, addNext_sl]; exact hb
  · rw [addNext_av]; exact hval

theorem invV_addSame (X : RState CState 4 4) (lo hi : ℕ) (tt : G3K.E) (a : G3K.Spec.Acc)
    (R : (Fin 4 → ℕ) → ℝ≥0∞) (Fs Fn : ℕ → ℕ)
    (hvs : a.vs + lo * tt.v = pack 96 (G3K.phase (X.i + 1)).nL Fs)
    (hvn : a.vn = pack 96 (G3K.phase (X.i + 2)).nL Fn)
    (hb : ∀ l l', Fs l + Fn l' + a.av ≤ (a.sl + lo) * (2 ^ 47 - 1))
    (hval : ∀ o, Fits o X → (valV Fs Fn a.av (incr o X.i X.e) : ℝ≥0∞) ≤ 2 ^ 88 * R o) :
    InvV X (G3K.Spec.addSame lo hi tt a) R := by
  refine ⟨Fs, Fn, ?_, ?_, ?_, ?_⟩
  · rw [addSame_vs]; exact hvs
  · rw [addSame_vn]; exact hvn
  · rw [addSame_av, addSame_sl]; exact hb
  · rw [addSame_av]; exact hval

/-- **One move** keeps the invariant of the V side. -/
theorem move_V (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c : Fin 4) (u1 u2 u3 : ℕ) (h12 : u1 ≤ u2) (h23 : u2 ≤ u3)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (n3 d3 δ w num pd : ℕ) (hw : w < 38)
    (a : G3K.Spec.Acc) (R : (Fin 4 → ℕ) → ℝ≥0∞) (hI : InvV X a R) :
    InvV X (G3K.Spec.move t (X.i + 1) u1 u2 u3
        (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).1
        (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.1
        (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.2 n3 d3 w
        (X.p - 1 + δ) num pd a)
      (fun o => R o + (num : ℝ≥0∞) / pd * tauV t o (X, false)
        (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false) (rstepR X c (δ, decC w)))) := by
  obtain ⟨-, hi, he, hp1, hp16, hwf, -⟩ := hX
  change X.i < 4 at hi
  change X.e ≤ cand.T at he
  obtain ⟨Fs, Fn, hvs, hvn, hb, hval⟩ := hI
  have hT : cand.T = 8 := rfl
  have hσ' : codeMs (Function.update X.σ c (decC w)) = {u1, u2, u3, w} := by
    rw [codeMs_update X.σ c (decC w) u1 u2 u3 hms, code_decC w hw]
  have hwf' : ∀ c', cand.ChildWF (Function.update X.σ c (decC w) c') := by
    intro c'
    by_cases hc : c' = c
    · subst hc; rw [Function.update_self]; exact childWF_decC w hw
    · rw [Function.update_of_ne hc]; exact hwf c'
  have hR : ∀ o, R o ≤ R o + (num : ℝ≥0∞) / pd * tauV t o (X, false)
      (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false) (rstepR X c (δ, decC w))) :=
    fun o => le_self_add
  unfold G3K.Spec.move
  split_ifs with hstop hzero hJ
  · -- the move sets the flag: the V side does not change
    exact invV_mono X _ R _ (invV_addStop X _ a R ⟨Fs, Fn, hvs, hvn, hb, hval⟩) hR
  · -- the move absorbs the chain: lane `0` of the last phase
    have h3 : X.i = 3 := by have : G3K.cJ = 4 := rfl; omega
    have hX' := rstepR_next X c δ (decC w) hi hzero
    have hdn := domNext_abs t X (rstepR X c (δ, decC w)) hi he (by rw [hX']; exact he) (by rw [hX']; show 1 ≤ 16; omega)
      (by rw [hX']; show 4 ≤ X.i + 1; omega)
    rw [hX'] at hdn
    rw [hX', hdn]
    have hVs : ∀ o, Vs t o (⟨X.i + 1, X.e, 1, Function.update X.σ c (decC w),
        Function.update X.out ⟨X.i, hi⟩ (X.e : ℕ∞)⟩, false) = 0 := by
      intro o
      unfold Vs; rw [if_neg]; rintro ⟨⟨-, h4, -⟩, -⟩; change X.i + 1 < 4 at h4; omega
    refine invV_addAbs X _ a _ Fs Fn hvs hvn (fun l l' => ?_) (fun o ho => ?_)
    · have := hb l l'
      calc Fs l + Fn l' + (a.av + G3K.Spec.lo48 num pd * 2 ^ 40)
          = (Fs l + Fn l' + a.av) + G3K.Spec.lo48 num pd * 2 ^ 40 := by ring
        _ ≤ a.sl * (2 ^ 47 - 1) + G3K.Spec.lo48 num pd * (2 ^ 47 - 1) :=
            add_le_add this (Nat.mul_le_mul_left _ (by norm_num))
        _ = (a.sl + G3K.Spec.lo48 num pd) * (2 ^ 47 - 1) := by ring
    · rw [valV_av]
      have hinc : incr o X.i X.e = [oget o 3 - X.e] := by
        rw [incr_cons o X.i X.e hi, h3]; simp [incr]
      have hv := hval o ho
      rw [hinc] at hv
      rw [hinc, laneIdx_single]
      have hFe : X.e ≤ oget o 3 := by have := ho.2.1; rwa [h3] at this
      by_cases ho3 : oget o 3 - X.e = 0
      · rw [if_pos ho3]
        have habs : absInd o (X, false) (⟨X.i + 1, X.e, 1, Function.update X.σ c (decC w),
            Function.update X.out ⟨X.i, hi⟩ (X.e : ℕ∞)⟩, false) = 1 := by
          unfold absInd
          rw [if_pos]
          refine ⟨rfl, hi, rfl, show 4 ≤ X.i + 1 by omega, ?_⟩
          rw [fits_abs o X ho h3 X.e]
          have : oget o 3 = o 3 := rfl
          omega
        rw [tauV, habs, hVs, add_zero]
        exact add_lo_le _ (2 ^ 40) num pd _ 1 hv (le_of_eq (by
          rw [Nat.cast_pow, Nat.cast_ofNat]; exact ENNReal.div_self (by positivity) (by simp)))
      · rw [if_neg ho3, add_zero]
        exact hv.trans (by gcongr; exact le_self_add)
  · -- the move ends the phase
    have hi3 : X.i + 1 < 4 := by have : G3K.cJ = 4 := rfl; omega
    have hX' := rstepR_next X c δ (decC w) hi hzero
    set X' : RState CState 4 4 := ⟨X.i + 1, X.e, 1, Function.update X.σ c (decC w),
      Function.update X.out ⟨X.i, hi⟩ (X.e : ℕ∞)⟩ with hX'def
    have hk1 : keyOf X' = G3K.Spec.encIns (X.i + 1 + 1) u1 u2 u3 w 1 :=
      keyOf_encIns X' u1 u2 u3 w h12 h23 hσ'
    have hk2 := keyOf_lump_encIns X' u1 u2 u3 w hwf' hσ'
    rw [← hk1, ← hk2]
    obtain ⟨hpack, hlt, hle⟩ := look_V t h X' hi3 he le_rfl (show 1 ≤ 16 by norm_num) hwf'
    have hph : X'.i + 1 = X.i + 2 := rfl
    rw [hph] at hpack
    set tt := G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X')) with htt
    have hdn := domNext_live t X X' hi he hi3 he (show 1 ≤ 16 by norm_num)
    rw [hX', hdn]
    refine invV_addNext X _ _ tt a _ Fs (fun l => Fn l + G3K.Spec.lo48 num pd * lane 96 l tt.v)
      hvs ?_ (fun l l' => ?_) (fun o ho => ?_)
    · rw [hvn]; conv_lhs => rw [hpack]
      rw [pack_const_mul, pack_add]
    · have := hb l l'
      have hl := lane_le l' tt.v (hlt l')
      calc Fs l + (Fn l' + G3K.Spec.lo48 num pd * lane 96 l' tt.v) + a.av
          = (Fs l + Fn l' + a.av) + G3K.Spec.lo48 num pd * lane 96 l' tt.v := by ring
        _ ≤ a.sl * (2 ^ 47 - 1) + G3K.Spec.lo48 num pd * (2 ^ 47 - 1) :=
            add_le_add this (Nat.mul_le_mul_left _ hl)
        _ = (a.sl + G3K.Spec.lo48 num pd) * (2 ^ 47 - 1) := by ring
    · rw [valV_fn]
      have hinc := incr_cons o X.i X.e hi
      have hFe : X.e ≤ oget o X.i := ho.2.1
      have hv := hval o ho
      by_cases h0 : (incr o X.i X.e).headD 0 = 0
      · rw [if_pos h0]
        rw [hinc] at h0 hv ⊢
        simp only [List.headD_cons, List.tail_cons] at h0 ⊢
        have hoe : oget o X.i = X.e := by omega
        have hF' : Fits o X' := (fits_succ o X ho hi3 X.e 1 _ le_rfl).2 hoe
        have := hle o hF'
        rw [hoe] at hv ⊢
        refine add_lo_le _ _ num pd _ _ hv (this.trans ?_)
        rw [tauV]; exact le_add_self
      · rw [if_neg h0, add_zero]
        exact hv.trans (by gcongr; exact le_self_add)
  · -- the move stays in the phase
    have hp2 : X.p - 1 + δ ≤ 16 := by have : G3K.cTP = 16 := rfl; omega
    have hX' := rstepR_same X c δ (decC w) hi hzero
    set X' : RState CState 4 4 := ⟨X.i, X.e, X.p - 1 + δ, Function.update X.σ c (decC w),
      X.out⟩ with hX'def
    have hk1 : keyOf X' = G3K.Spec.encIns (X.i + 1) u1 u2 u3 w (X.p - 1 + δ) :=
      keyOf_encIns X' u1 u2 u3 w h12 h23 hσ'
    have hk2 := keyOf_lump_encIns X' u1 u2 u3 w hwf' hσ'
    rw [← hk1, ← hk2]
    obtain ⟨hpack, hlt, hle⟩ := look_V t h X' hi he (show 1 ≤ X.p - 1 + δ by omega) hp2 hwf'
    have hph : X'.i + 1 = X.i + 1 := rfl
    rw [hph] at hpack
    set tt := G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X')) with htt
    have hdn := domNext_live t X X' hi he hi he hp2
    rw [hX', hdn]
    refine invV_addSame X _ _ tt a _ (fun l => Fs l + G3K.Spec.lo48 num pd * lane 96 l tt.v) Fn
      ?_ hvn (fun l l' => ?_) (fun o ho => ?_)
    · rw [hvs]; conv_lhs => rw [hpack]
      rw [pack_const_mul, pack_add]
    · have := hb l l'
      have hl := lane_le l tt.v (hlt l)
      calc Fs l + G3K.Spec.lo48 num pd * lane 96 l tt.v + Fn l' + a.av
          = (Fs l + Fn l' + a.av) + G3K.Spec.lo48 num pd * lane 96 l tt.v := by ring
        _ ≤ a.sl * (2 ^ 47 - 1) + G3K.Spec.lo48 num pd * (2 ^ 47 - 1) :=
            add_le_add this (Nat.mul_le_mul_left _ hl)
        _ = (a.sl + G3K.Spec.lo48 num pd) * (2 ^ 47 - 1) := by ring
    · rw [valV_fs]
      have hF' : Fits o X' := (fits_same o X ho X.e _ _).2 ho.2.1
      have := hle o hF'
      refine add_lo_le _ _ num pd _ _ (hval o ho) (this.trans ?_)
      rw [tauV]; exact le_add_self

/-! ### The rows, the tail atoms, a child -/

/-- `tauV` at the state the chain reaches when child `c` of `X` moves by `r`. -/
noncomputable def tgtV (t : G3K.Tree) (o : Fin 4 → ℕ) (X : RState CState 4 4) (c : Fin 4)
    (r : ℕ × CState) : ℝ≥0∞ :=
  tauV t o (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false) (rstepR X c r))

/-- **The moves of a row** keep the invariant of the V side. -/
theorem rowLoop_V (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c : Fin 4) (u1 u2 u3 : ℕ) (h12 : u1 ≤ u2) (h23 : u2 ≤ u3)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (n3 d3 m : ℕ) :
    ∀ (rs : List G3K.Tr) (a : G3K.Spec.Acc) (R : (Fin 4 → ℕ) → ℝ≥0∞),
      (∀ r ∈ rs, r.next < 38) → InvV X a R →
      InvV X (G3K.Spec.rowLoop t (X.i + 1) u1 u2 u3
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).1
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.1
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.2 n3 d3 (X.p - 1) m rs a)
        (fun o => R o + (rs.map fun r =>
          ((m * r.pn : ℕ) : ℝ≥0∞) / r.pd * tgtV t o X c (r.delta, decC r.next)).sum)
  | [], a, R, _, hI => by
      rw [G3K.Spec.rowLoop]
      exact invV_mono X a R _ hI (fun o => by simp)
  | r :: rs, a, R, hr, hI => by
      rw [G3K.Spec.rowLoop]
      have h1 := move_V t h X hX c u1 u2 u3 h12 h23 hms n3 d3 r.delta r.next (m * r.pn) r.pd
        (hr r List.mem_cons_self) a R hI
      have h2 := rowLoop_V t h X hX c u1 u2 u3 h12 h23 hms n3 d3 m rs _ _
        (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr')) h1
      refine invV_mono X _ _ _ h2 (fun o => le_of_eq ?_)
      simp only [List.map_cons, List.sum_cons, tgtV]
      ring

/-- **The tail atoms** keep the invariant of the V side. -/
theorem tailLoop_V (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c : Fin 4) (u1 u2 u3 : ℕ) (h12 : u1 ≤ u2) (h23 : u2 ≤ u3)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (n3 d3 m ct : ℕ) (hct : ct < 38) :
    ∀ (n k : ℕ) (a : G3K.Spec.Acc) (R : (Fin 4 → ℕ) → ℝ≥0∞), InvV X a R →
      InvV X (G3K.Spec.tailLoop t (X.i + 1) u1 u2 u3
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).1
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.1
          (G3K.Spec.sort3 (G3K.lumpC u1) (G3K.lumpC u2) (G3K.lumpC u3)).2.2 n3 d3 ct (X.p - 1) m
          k n a)
        (fun o => R o + ∑ j ∈ Finset.range n,
          ((m * G3K.Spec.tailN (k + j) : ℕ) : ℝ≥0∞) / G3K.Spec.tailD (k + j) *
            tgtV t o X c (G3K.cT + 1 + (k + j), decC ct))
  | 0, k, a, R, hI => by
      rw [G3K.Spec.tailLoop]
      exact invV_mono X a R _ hI (fun o => by simp)
  | n + 1, k, a, R, hI => by
      rw [G3K.Spec.tailLoop]
      have h1 := move_V t h X hX c u1 u2 u3 h12 h23 hms n3 d3 (G3K.cT + 1 + k) ct
        (m * G3K.Spec.tailN k) (G3K.Spec.tailD k) hct a R hI
      have h2 := tailLoop_V t h X hX c u1 u2 u3 h12 h23 hms n3 d3 m ct hct n (k + 1) _ _ h1
      refine invV_mono X _ _ _ h2 (fun o => le_of_eq ?_)
      rw [Finset.sum_range_succ' _ n]
      simp only [tgtV, add_zero, Nat.add_assoc, Nat.add_comm 1]
      ring

/-! ### Weights -/

theorem ofReal_ratDiv (n d : ℕ) (hd : 0 < d) :
    ENNReal.ofReal (((n : ℚ) / d : ℚ) : ℝ) = (n : ℝ≥0∞) / d := by
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast,
    ENNReal.ofReal_div_of_pos (by exact_mod_cast hd), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

theorem ofReal_div5 (p : ℚ) : ENNReal.ofReal ((p / 5 : ℚ) : ℝ) = 5⁻¹ * ENNReal.ofReal (p : ℝ) := by
  rw [Rat.cast_div, ENNReal.ofReal_div_of_pos (by norm_num), div_eq_mul_inv, mul_comm]
  norm_num

theorem natMul_div (m n d : ℕ) : ((m * n : ℕ) : ℝ≥0∞) / d = m * ((n : ℝ≥0∞) / d) := by
  push_cast; rw [mul_div_assoc]

/-- The weight of tail atom `j` of the checker is `tailW j / 5`. -/
theorem tail_weight (j : ℕ) :
    ((G3K.Spec.tailN j : ℚ) / G3K.Spec.tailD j) = cand.tailW j / 5 := by
  obtain ⟨-, -, -, heps, hrho, -, -, hepsD, hrhoD, hlt, -⟩ := const_spec
  unfold G3K.Spec.tailN G3K.Spec.tailD Data.tailW
  rw [heps, hrho]
  have h1 : (G3K.rhoD : ℚ) ≠ 0 := by exact_mod_cast hrhoD.ne'
  have h2 : (G3K.epsD : ℚ) ≠ 0 := by exact_mod_cast hepsD.ne'
  push_cast [Nat.cast_sub hlt.le]
  rw [div_pow]
  field_simp
  ring

/-- The row of a child in the checker, weighted, is `5⁻¹` times its finite row. -/
theorem rowSum_eq (c : ℕ) (hc : c < 38) (m : ℕ) (g : ℕ × CState → ℝ≥0∞) :
    ((G3K.row c).map fun r => ((m * r.pn : ℕ) : ℝ≥0∞) / r.pd * g (r.delta, decC r.next)).sum =
      m * (5⁻¹ * ((cand.finRow (decC c)).map fun e =>
        ENNReal.ofReal (e.p : ℝ) * g (e.δ, e.next)).sum) := by
  obtain ⟨hrs, hr⟩ := row_spec c hc
  set G : ℚ × ℕ × CState → ℝ≥0∞ := fun x => m * (ENNReal.ofReal (x.1 : ℝ) * g (x.2.1, x.2.2))
    with hG
  have e1 : ((G3K.row c).map fun r => ((m * r.pn : ℕ) : ℝ≥0∞) / r.pd * g (r.delta, decC r.next)) =
      ((G3K.row c).map fun r => ((r.pn : ℚ) / r.pd, r.delta, decC r.next)).map G := by
    rw [List.map_map]
    refine List.map_congr_left fun r hrr => ?_
    simp only [Function.comp, hG]
    rw [ofReal_ratDiv _ _ (hr r hrr).2, natMul_div, mul_assoc]
  rw [e1, hrs, List.map_map]
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp, hG]
  rw [ofReal_div5, mul_assoc]

/-- **The moves of one child** of code `code (X.σ c)` with multiplicity `m` keep the invariant
of the V side, with `R` raised by `m` times the moves of child `c`. -/
theorem child_V (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c : Fin 4) (u1 u2 u3 : ℕ) (h12 : u1 ≤ u2) (h23 : u2 ≤ u3)
    (hms : codeMs X.σ = {u1, u2, u3, code (X.σ c)}) (m : ℕ) (a : G3K.Spec.Acc)
    (R : (Fin 4 → ℕ) → ℝ≥0∞) (hI : InvV X a R) :
    InvV X (G3K.Spec.child t (X.i + 1) (code (X.σ c)) u1 u2 u3 X.p m a)
      (fun o => R o + m * (5⁻¹ * moveSum cand (X.σ c) (fun r => tgtV t o X c r))) := by
  have hwf : ∀ c, cand.ChildWF (X.σ c) := hX.2.2.2.2.2.1
  have hcc : code (X.σ c) < 38 := code_lt _ (hwf c)
  have hdec : decC (code (X.σ c)) = X.σ c := decC_code _ (hwf c)
  obtain ⟨-, hr38⟩ := row_spec _ hcc
  have hrow := rowLoop_V t h X hX c u1 u2 u3 h12 h23 hms (G3K.wN u1 * G3K.wN u2 * G3K.wN u3)
    (G3K.wD u1 * G3K.wD u2 * G3K.wD u3) m (G3K.row (code (X.σ c))) a R
    (fun r hr => (hr38 r hr).1) hI
  have hsum : ∀ o, ((G3K.row (code (X.σ c))).map fun r =>
      ((m * r.pn : ℕ) : ℝ≥0∞) / r.pd * tgtV t o X c (r.delta, decC r.next)).sum =
      m * (5⁻¹ * ((cand.finRow (X.σ c)).map fun e =>
        ENNReal.ofReal (e.p : ℝ) * tgtV t o X c (e.δ, e.next)).sum) := by
    intro o
    rw [rowSum_eq _ hcc m (fun r => tgtV t o X c r), hdec]
  obtain ⟨ht0, ht1, htn, ht0l, ht1l⟩ := tail_spec
  unfold G3K.Spec.child
  dsimp only
  split_ifs with hc1
  · -- `F` or `B`: the row, the tail atoms, the closed form of the tail (W side only)
    have hct : G3K.tailOf (code (X.σ c)) < 38 := by
      interval_cases hcode : code (X.σ c)
      · exact ht0l
      · exact ht1l
    have hnext : cand.tailNext (X.σ c) = some (decC (G3K.tailOf (code (X.σ c)))) := by
      rw [← hdec]
      interval_cases hcode : code (X.σ c)
      · exact ht0
      · exact ht1
    unfold G3K.Spec.withTails
    apply invV_addStop
    have htail := tailLoop_V t h X hX c u1 u2 u3 h12 h23 hms (G3K.wN u1 * G3K.wN u2 * G3K.wN u3)
      (G3K.wD u1 * G3K.wD u2 * G3K.wD u3) m _ hct (G3K.cTP + 1 - (X.p + G3K.cT)) 0 _ _ hrow
    refine invV_mono X _ _ _ htail (fun o => ?_)
    rw [hsum o, add_assoc]
    gcongr R o + ?_
    unfold moveSum
    rw [hnext, mul_add, mul_add]
    gcongr _ + ?_
    have hT : cand.T = G3K.cT := rfl
    calc ∑ j ∈ Finset.range (G3K.cTP + 1 - (X.p + G3K.cT)),
          ((m * G3K.Spec.tailN (0 + j) : ℕ) : ℝ≥0∞) / G3K.Spec.tailD (0 + j) *
            tgtV t o X c (G3K.cT + 1 + (0 + j), decC (G3K.tailOf (code (X.σ c))))
        = ∑ j ∈ Finset.range (G3K.cTP + 1 - (X.p + G3K.cT)), m * (5⁻¹ *
            (ENNReal.ofReal (cand.tailW j : ℝ) *
              tgtV t o X c (cand.T + 1 + j, decC (G3K.tailOf (code (X.σ c)))))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [zero_add, natMul_div, ← ofReal_ratDiv _ _ (by
            unfold G3K.Spec.tailD
            have : 0 < G3K.epsD := by decide
            have : 0 < G3K.rhoD := by decide
            positivity),
            tail_weight, ofReal_div5, hT]
          ring
      _ = m * (5⁻¹ * ∑ j ∈ Finset.range (G3K.cTP + 1 - (X.p + G3K.cT)),
            ENNReal.ofReal (cand.tailW j : ℝ) *
              tgtV t o X c (cand.T + 1 + j, decC (G3K.tailOf (code (X.σ c))))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ m * (5⁻¹ * ∑' k, ENNReal.ofReal (cand.tailW k : ℝ) *
            tgtV t o X c (cand.T + 1 + k, decC (G3K.tailOf (code (X.σ c))))) := by
          gcongr
          exact ENNReal.sum_le_tsum _
  · -- a label, a tail or a max label: the row alone, no tail
    have hnext : cand.tailNext (X.σ c) = none := by
      rw [← hdec]; exact htn _ hcc (by omega)
    refine invV_mono X _ _ _ hrow (fun o => ?_)
    rw [hsum o]
    unfold moveSum
    rw [hnext, add_zero]

/-- **The moves of the checker** at a covered state keep the invariant of the V side, with `R` the
moves of every child. -/
theorem moves_V (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) :
    InvV X (G3K.Spec.moves t (X.i + 1) c1 c2 c3 c4 X.p)
      (fun o => ∑ c, 5⁻¹ * moveSum cand (X.σ c) (fun r => tgtV t o X c r)) := by
  have hwf : ∀ c, cand.ChildWF (X.σ c) := hX.2.2.2.2.2.1
  have hinj := code_inj_of_wf X hwf
  have hsort := Multiset.pairwise_sort (codeMs X.σ) (· ≤ ·)
  rw [hL] at hsort
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true] at hsort
  have h12 : c1 ≤ c2 := by omega
  have h23 : c2 ≤ c3 := by omega
  have h34 : c3 ≤ c4 := by omega
  have hms : ({c1, c2, c3, c4} : Multiset ℕ) = codeMs X.σ := by
    rw [← Multiset.sort_eq (codeMs X.σ) (· ≤ ·), hL]; rfl
  set F : (Fin 4 → ℕ) → Fin 4 → ℝ≥0∞ :=
    fun o c => 5⁻¹ * moveSum cand (X.σ c) (fun r => tgtV t o X c r) with hFdef
  have hF : ∀ o c c', X.σ c = X.σ c' → F o c = F o c' := by
    intro o c c' hcc
    simp only [hFdef, tgtV]
    rw [moveSum_congr t X (tauV t o (X, false)) (fun π Z b => tauV_perm t o _ π Z b) c c' hcc]
  have key := moves_inv (fun a R => InvV X a R) t (X.i + 1) X.p c1 c2 c3 c4
    (fun a o => perCode X (F o) a) h12 h23 h34 (invV_zero X)
    (by
      intro a u1 u2 u3 m acc R hu12 hu23 hu hP
      obtain ⟨c, hca, hms2⟩ := exists_child_of_code X a u1 u2 u3 (hu.trans hms)
      subst hca
      have hc := child_V t h X hX c u1 u2 u3 hu12 hu23 hms2 m acc R hP
      have e : (fun i => R i + (m : ℝ≥0∞) * perCode X (F i) (code (X.σ c))) =
          fun o => R o + m * (5⁻¹ * moveSum cand (X.σ c) (fun r => tgtV t o X c r)) := by
        funext o
        rw [perCode_eq X hinj (F o) (hF o) c]
      rw [e]
      exact hc)
  refine invV_mono X _ _ _ key (fun o => le_of_eq ?_)
  exact (sum_perCode X hinj (F o) (hF o) c1 c2 c3 c4 hL).symm

/-! ### The comparison at the end -/

/-- `gather_pack` with the source lane read through `Option.elim`. -/
theorem gather_pack' (L L' : ℕ) (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ 96)
    (segs : List (ℕ × ℕ × ℕ)) (hs : SegsOK L L' segs) :
    G3K.Spec.gather (pack 96 L f) segs = pack 96 L' fun l => (gsrc segs l).elim 0 f := by
  rw [gather_pack L L' f hf segs hs]
  congr 1
  funext l
  cases gsrc segs l <;> rfl

theorem segsOK_cp0 (X : RState CState 4 4) (hi : X.i < 4) :
    SegsOK (G3K.phase (X.i + 2)).nL (G3K.phase (X.i + 1)).nL (G3K.phase (X.i + 1)).cp0 := by
  by_cases h3 : X.i + 1 < 4
  · exact ((segsOK_phase (X.i + 1) (by omega) (by omega)).2 h3).1
  · have h4 : X.i = 3 := by omega
    rw [h4]
    unfold SegsOK
    decide +kernel

/-- `x` added to lane `0` of `L ≥ 1` lanes. -/
theorem eq_pack_lane0 (W L x : ℕ) (hL : 0 < L) : x = pack W L (fun l => if l = 0 then x else 0) := by
  unfold pack
  rw [Finset.sum_eq_single 0 (fun l _ hl => by simp [hl])
    (fun h => absurd (Finset.mem_range.2 hL) h)]
  simp

/-- The lanes of the right side of the final comparison stay below the guard bit. -/
theorem sum_lt_guard (x y z w sl av : ℕ) (hxy : x + y + av ≤ sl * (2 ^ 47 - 1)) (hz : z ≤ av)
    (hw : w ≤ G3K.exitLo * (2 ^ 47 - 1)) (hsl : sl + G3K.exitLo ≤ 2 ^ 48) :
    x + y + (z + w) < 2 ^ 95 := by
  have h3 : sl * (2 ^ 47 - 1) + G3K.exitLo * (2 ^ 47 - 1) ≤ 2 ^ 48 * (2 ^ 47 - 1) := by
    rw [← add_mul]; exact Nat.mul_le_mul_right _ hsl
  have h5 : 2 ^ 48 * (2 ^ 47 - 1) < 2 ^ 95 := by norm_num
  omega

/-- **The lane of the state read off the final comparison**: `2^48` times lane `o` of V' is at
most the lane of the moves plus the lane `Ev` of the exit. -/
theorem final_V (s : G3K.E) (X : RState CState 4 4) (hi : X.i < 4) (a : G3K.Spec.Acc)
    (R : (Fin 4 → ℕ) → ℝ≥0∞) (hI : InvV X a R) (Ev : ℕ → ℕ)
    (hEv : ∀ l, Ev l ≤ G3K.exitLo * (2 ^ 47 - 1)) (ew e0 : ℕ) (eok : Bool)
    (hfin : G3K.Spec.final s (X.i + 1) a (pack 96 (G3K.phase (X.i + 1)).nL Ev) ew e0 eok = true)
    (hsv : pack 96 (G3K.phase (X.i + 1)).nL (fun l => lane 96 l s.v) = s.v)
    (hsl : ∀ l, lane 96 l s.v < 2 ^ 47) (o : Fin 4 → ℕ) (hF : Fits o X) :
    (lane 96 (laneIdx (incr o X.i X.e)) s.v : ℝ≥0∞) / 2 ^ 40 ≤
      R o + (Ev (laneIdx (incr o X.i X.e)) : ℝ≥0∞) / 2 ^ 88 := by
  obtain ⟨Fs, Fn, hvs, hvn, hbd, hval⟩ := hI
  unfold G3K.Spec.final at hfin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfin
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hsl48⟩, -⟩, -⟩, hleV⟩, -⟩ := hfin
  have h48 : G3K.Spec.two48 = 2 ^ 48 := rfl
  rw [h48] at hsl48
  have hq1 : 1 ≤ X.i + 1 := by omega
  have hq4 : X.i + 1 ≤ 4 := by omega
  have hvmem : incr o X.i X.e ∈ allVecs (5 - (X.i + 1)) 8 :=
    mem_allVecs _ _ _ (by rw [incr_length]; omega)
      (by have := incr_sum o X hF hi; rwa [show cand.T = 8 from rfl] at this)
  obtain ⟨hlt, -, hcp0, -⟩ := lanesOK (X.i + 1) hq1 hq4 _ hvmem
  have hK : ∀ l', Fn l' ≤ a.sl * (2 ^ 47 - 1) := fun l' => by have := hbd 0 l'; omega
  have hFn : ∀ l', Fn l' < 2 ^ 96 := fun l' =>
    calc Fn l' ≤ a.sl * (2 ^ 47 - 1) := hK l'
      _ ≤ 2 ^ 48 * (2 ^ 47 - 1) := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ 96 := by norm_num
  have hG := gather_pack' _ _ Fn (fun l _ => hFn l) _ (segsOK_cp0 X hi)
  rw [← hvn] at hG
  have hGl : ∀ l, ∃ l', (gsrc (G3K.phase (X.i + 1)).cp0 l).elim 0 Fn ≤ Fn l' := by
    intro l
    cases gsrc (G3K.phase (X.i + 1)).cp0 l with
    | none => exact ⟨0, Nat.zero_le _⟩
    | some l0 => exact ⟨l0, le_rfl⟩
  have hGv : (gsrc (G3K.phase (X.i + 1)).cp0 (laneIdx (incr o X.i X.e))).elim 0 Fn ≤
      if (incr o X.i X.e).headD 0 = 0 then Fn (laneIdx (incr o X.i X.e).tail) else 0 := by
    by_cases h3 : X.i + 1 < 4
    · rw [hcp0 h3]
      split_ifs <;> exact le_rfl
    · have hc : (G3K.phase (X.i + 1)).cp0 = [] := by
        rw [show X.i = 3 by omega]; rfl
      rw [hc]
      exact Nat.zero_le _
  have hav := eq_pack_lane0 96 (G3K.phase (X.i + 1)).nL a.av (by omega)
  have hsum : a.vs + G3K.Spec.gather a.vn (G3K.phase (X.i + 1)).cp0 +
      (a.av + pack 96 (G3K.phase (X.i + 1)).nL Ev) =
      pack 96 (G3K.phase (X.i + 1)).nL (fun l => Fs l +
        (gsrc (G3K.phase (X.i + 1)).cp0 l).elim 0 Fn + ((if l = 0 then a.av else 0) + Ev l)) := by
    rw [hvs, hG]
    conv_lhs => rw [hav]
    rw [pack_add, pack_add, pack_add]
  have hlhs : s.v * G3K.Spec.two48 =
      pack 96 (G3K.phase (X.i + 1)).nL (fun l => 2 ^ 48 * lane 96 l s.v) := by
    conv_lhs => rw [← hsv]
    rw [h48, mul_comm, pack_const_mul]
  rw [gV_eq, hlhs, hsum] at hleV
  have hle := (leLanes_pack 96 _ (by norm_num) _ _ (fun l _ => by
      have := hsl l
      calc 2 ^ 48 * lane 96 l s.v < 2 ^ 48 * 2 ^ 47 := by gcongr
        _ = 2 ^ (96 - 1) := by norm_num)
    (fun l _ => by
      obtain ⟨l', hl'⟩ := hGl l
      have h1 := hbd l l'
      exact sum_lt_guard _ _ _ _ a.sl a.av (by omega)
        (by split_ifs <;> [exact le_rfl; exact Nat.zero_le _]) (hEv l) hsl48)).1 hleV
  have hmain : 2 ^ 48 * lane 96 (laneIdx (incr o X.i X.e)) s.v ≤
      valV Fs Fn a.av (incr o X.i X.e) + Ev (laneIdx (incr o X.i X.e)) := by
    have := hle _ hlt
    unfold valV
    omega
  have hv88 := hval o hF
  calc (lane 96 (laneIdx (incr o X.i X.e)) s.v : ℝ≥0∞) / 2 ^ 40
      = ((2 ^ 48 * lane 96 (laneIdx (incr o X.i X.e)) s.v : ℕ) : ℝ≥0∞) / 2 ^ 88 := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          show (2 : ℝ≥0∞) ^ 88 = 2 ^ 48 * 2 ^ 40 by norm_num,
          ENNReal.mul_div_mul_left _ _ (by positivity) (by simp)]
    _ ≤ ((valV Fs Fn a.av (incr o X.i X.e) + Ev (laneIdx (incr o X.i X.e)) : ℕ) : ℝ≥0∞) /
        2 ^ 88 := by gcongr
    _ ≤ (2 ^ 88 * R o + Ev (laneIdx (incr o X.i X.e))) / 2 ^ 88 := by
        rw [Nat.cast_add]; gcongr
    _ = R o + (Ev (laneIdx (incr o X.i X.e)) : ℝ≥0∞) / 2 ^ 88 := by
        rw [ENNReal.add_div, mul_comm, ENNReal.mul_div_cancel_right (by positivity) (by simp)]

/-- The weight of the exit: `exitLo x`, in units of `2^-88`, is at most a fifth of `x` in units of
`2^-40`. -/
theorem exitLo_le (x : ℕ) :
    ((G3K.exitLo * x : ℕ) : ℝ≥0∞) / 2 ^ 88 ≤ 5⁻¹ * ((x : ℝ≥0∞) / 2 ^ 40) := by
  have h5 : G3K.exitLo * 5 ≤ 2 ^ 48 := by decide
  have hE : (G3K.exitLo : ℝ≥0∞) ≤ 5⁻¹ * 2 ^ 48 := by
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (by simp) (by simp)]
    exact_mod_cast h5
  have hx : (x : ℝ≥0∞) / 2 ^ 40 * 2 ^ 88 = x * 2 ^ 48 := by
    rw [show (2 : ℝ≥0∞) ^ 88 = 2 ^ 40 * 2 ^ 48 by norm_num, ← mul_assoc,
      ENNReal.div_mul_cancel (by positivity) (by simp)]
  apply ENNReal.div_le_of_le_mul
  rw [mul_assoc, hx, Nat.cast_mul]
  calc (G3K.exitLo : ℝ≥0∞) * x ≤ (5⁻¹ * 2 ^ 48) * x := by gcongr
    _ = 5⁻¹ * (x * 2 ^ 48) := by ring

/-! ### The exit -/

/-- **A target found by the checker** is the pack of its lanes, each below `2^47`. -/
theorem look_pack (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X' : RState CState 4 4)
    (hp' : X'.p < 128) (hwf : ∀ c, cand.ChildWF (X'.σ c)) :
    pack 96 (G3K.phase (X'.i + 1)).nL
        (fun l => lane 96 l (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).v) =
        (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).v ∧
      ∀ l, lane 96 l (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).v < 2 ^ 47 := by
  rcases look_cases t X' with hb | ⟨hl, hk⟩
  · rw [hb]
    refine ⟨?_, fun l => ?_⟩
    · simp [G3K.Spec.bad, lane, pack]
    · simp [G3K.Spec.bad, lane]
  · rw [hl]
    obtain ⟨hi2, -, hp2, -⟩ := keptOf_fields t X'
    have hb := boundsOK_sound _ _ (entry_bounds t h (keptOf t X') (keptOf_wf t X' hwf) (by omega) hk)
    rw [hi2] at hb
    exact ⟨hb.1, fun l => (hb.2.1 l).1⟩

theorem oget_eq (o : Fin 4 → ℕ) (k : ℕ) (hk : k < 4) : oget o k = o ⟨k, hk⟩ := dif_pos hk

/-- The output of the frog of `X` is at most `T`. -/
theorem oget_le_T (o : Fin 4 → ℕ) (X : RState CState 4 4) (hF : Fits o X) (hi : X.i < 4) :
    oget o X.i ≤ cand.T := by
  have key : ∀ n, X.i + n ≤ 3 → oget o X.i ≤ oget o (X.i + n) := by
    intro n
    induction n with
    | zero => intro _; exact le_rfl
    | succ n ih =>
      intro hn
      exact (ih (by omega)).trans (hF.2.2.1 (X.i + n) (by omega) (by omega))
  have h3 := key (3 - X.i) (by omega)
  rw [show X.i + (3 - X.i) = 3 by omega, oget_eq o 3 (by norm_num)] at h3
  exact h3.trans hF.2.2.2

/-- The lanes of a target times `exitLo`, gathered by `segs`. -/
theorem gather_exit (L L' : ℕ) (u : ℕ) (hu : pack 96 L (fun l => lane 96 l u) = u)
    (hul : ∀ l, lane 96 l u < 2 ^ 47) (segs : List (ℕ × ℕ × ℕ)) (hs : SegsOK L L' segs) :
    G3K.Spec.gather (G3K.exitLo * u) segs =
      pack 96 L' (fun l => (gsrc segs l).elim 0 (fun l0 => G3K.exitLo * lane 96 l0 u)) := by
  conv_lhs => rw [← hu]
  rw [pack_const_mul]
  refine gather_pack' _ _ _ (fun l _ => ?_) _ hs
  have h5 : G3K.exitLo < 2 ^ 48 := by decide
  calc G3K.exitLo * lane 96 l u < 2 ^ 48 * 2 ^ 47 := Nat.mul_lt_mul'' h5 (hul l)
    _ ≤ 2 ^ 96 := by norm_num

theorem exit_le (u : ℕ) (hul : ∀ l, lane 96 l u < 2 ^ 47) (segs : List (ℕ × ℕ × ℕ)) (l : ℕ) :
    (gsrc segs l).elim 0 (fun l0 => G3K.exitLo * lane 96 l0 u) ≤ G3K.exitLo * (2 ^ 47 - 1) := by
  cases gsrc segs l with
  | none => exact Nat.zero_le _
  | some l0 => exact Nat.mul_le_mul_left _ (by have := hul l0; omega)

/-- The lane of a live target, weighted by `exitLo`, is at most a fifth of `tauV` there. -/
theorem exit_lane (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X X' : RState CState 4 4)
    (hi : X.i < 4) (he : X.e ≤ cand.T) (hi' : X'.i < 4) (he' : X'.e ≤ cand.T) (hp1 : 1 ≤ X'.p)
    (hp16 : X'.p ≤ 16) (hwf : ∀ c, cand.ChildWF (X'.σ c)) (o : Fin 4 → ℕ) (hF' : Fits o X') :
    ((G3K.exitLo * lane 96 (laneIdx (incr o X'.i X'.e))
        (G3K.Spec.look t (keyOf X') (keyOf (lumpState cand X'))).v : ℕ) : ℝ≥0∞) / 2 ^ 88 ≤
      5⁻¹ * tauV t o (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false) X') := by
  rw [domNext_live t X X' hi he hi' he' hp16]
  refine (exitLo_le _).trans ?_
  gcongr
  unfold tauV
  exact ((look_V t h X' hi' he' hp1 hp16 hwf).2.2 o hF').trans le_add_self

/-- **The exit in the phase** (`p ≥ 2`). -/
theorem finSame_V (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) (s : G3K.E)
    (hsv : pack 96 (G3K.phase (X.i + 1)).nL (fun l => lane 96 l s.v) = s.v)
    (hsl : ∀ l, lane 96 l s.v < 2 ^ 47) (a : G3K.Spec.Acc) (R : (Fin 4 → ℕ) → ℝ≥0∞)
    (hI : InvV X a R) (e0 : ℕ) (hp : X.p ≠ 1)
    (hfin : G3K.Spec.exitSame s (X.i + 1) a e0
      (G3K.Spec.look t (G3K.Spec.enc (X.i + 1) c1 c2 c3 c4 (X.p - 1))
        (G3K.Spec.lumpKey4 (X.i + 1) c1 c2 c3 c4 (X.p - 1))) = true)
    (o : Fin 4 → ℕ) (hF : Fits o X) :
    (lane 96 (laneIdx (incr o X.i X.e)) s.v : ℝ≥0∞) / 2 ^ 40 ≤
      R o + 5⁻¹ * tauV t o (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        ⟨X.i, X.e + 1, X.p - 1, X.σ, X.out⟩) := by
  have hi : X.i < 4 := hX.2.1
  have he : X.e ≤ cand.T := hX.2.2.1
  have hp1 : 1 ≤ X.p := hX.2.2.2.1
  have hp16 : X.p ≤ 16 := hX.2.2.2.2.1
  have hwf : ∀ c, cand.ChildWF (X.σ c) := hX.2.2.2.2.2.1
  set X' : RState CState 4 4 := ⟨X.i, X.e + 1, X.p - 1, X.σ, X.out⟩ with hX'
  have hk1 : G3K.Spec.enc (X.i + 1) c1 c2 c3 c4 (X.p - 1) = keyOf X' :=
    (keyOf_enc X' c1 c2 c3 c4 hL).symm
  have hk2 : G3K.Spec.lumpKey4 (X.i + 1) c1 c2 c3 c4 (X.p - 1) = keyOf (lumpState cand X') :=
    (keyOf_lump_enc X' c1 c2 c3 c4 hwf hL).symm
  rw [hk1, hk2] at hfin
  obtain ⟨hupk, hul⟩ := look_pack t h X' (show X.p - 1 < 128 by omega) hwf
  unfold G3K.Spec.exitSame at hfin
  rw [gather_exit _ _ _ hupk hul _ (segsOK_phase (X.i + 1) (by omega) (by omega)).1] at hfin
  refine (final_V s X hi a R hI _ (exit_le _ hul _) _ _ _ hfin hsv hsl o hF).trans
    (add_le_add le_rfl ?_)
  have hvmem : incr o X.i X.e ∈ allVecs (5 - (X.i + 1)) 8 :=
    mem_allVecs _ _ _ (by rw [incr_length]; omega)
      (by have := incr_sum o X hF hi; rwa [show cand.T = 8 from rfl] at this)
  obtain ⟨-, hgx, -, -⟩ := lanesOK (X.i + 1) (by omega) (by omega) _ hvmem
  rw [hgx]
  split_ifs with h1
  · have hc := incr_cons o X.i X.e hi
    have hc' := incr_cons o X.i (X.e + 1) hi
    rw [hc] at h1
    simp only [List.headD_cons] at h1
    have hv' : ((incr o X.i X.e).headD 0 - 1) :: (incr o X.i X.e).tail = incr o X'.i X'.e := by
      show _ = incr o X.i (X.e + 1)
      rw [hc, hc']
      simp only [List.headD_cons, List.tail_cons]
      congr 1
    simp only [Option.elim_some]
    rw [hv']
    have he' : X'.e ≤ cand.T := by
      show X.e + 1 ≤ cand.T; have := oget_le_T o X hF hi; omega
    exact exit_lane t h X X' hi he hi he' (show 1 ≤ X.p - 1 by omega) (show X.p - 1 ≤ 16 by omega)
      hwf o ((fits_same o X hF (X.e + 1) (X.p - 1) X.σ).2 (by omega))
  · simp

/-- **The exit to the next phase** (`p = 1`, `q < J`). -/
theorem finNext_V (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) (s : G3K.E)
    (hsv : pack 96 (G3K.phase (X.i + 1)).nL (fun l => lane 96 l s.v) = s.v)
    (hsl : ∀ l, lane 96 l s.v < 2 ^ 47) (a : G3K.Spec.Acc) (R : (Fin 4 → ℕ) → ℝ≥0∞)
    (hI : InvV X a R) (e0 : ℕ) (hq : X.i + 1 < 4)
    (hfin : G3K.Spec.exitNext s (X.i + 1) a e0
      (G3K.Spec.look t (G3K.Spec.enc (X.i + 1 + 1) c1 c2 c3 c4 1)
        (G3K.Spec.lumpKey4 (X.i + 1 + 1) c1 c2 c3 c4 1)) = true)
    (o : Fin 4 → ℕ) (hF : Fits o X) :
    (lane 96 (laneIdx (incr o X.i X.e)) s.v : ℝ≥0∞) / 2 ^ 40 ≤
      R o + 5⁻¹ * tauV t o (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        ⟨X.i + 1, X.e + 1, 1, X.σ,
          Function.update X.out ⟨X.i, hX.2.1⟩ ((X.e + 1 : ℕ) : ℕ∞)⟩) := by
  have hi : X.i < 4 := hX.2.1
  have he : X.e ≤ cand.T := hX.2.2.1
  have hwf : ∀ c, cand.ChildWF (X.σ c) := hX.2.2.2.2.2.1
  set X' : RState CState 4 4 := ⟨X.i + 1, X.e + 1, 1, X.σ,
    Function.update X.out ⟨X.i, hX.2.1⟩ ((X.e + 1 : ℕ) : ℕ∞)⟩ with hX'
  have hk1 : G3K.Spec.enc (X.i + 1 + 1) c1 c2 c3 c4 1 = keyOf X' :=
    (keyOf_enc X' c1 c2 c3 c4 hL).symm
  have hk2 : G3K.Spec.lumpKey4 (X.i + 1 + 1) c1 c2 c3 c4 1 = keyOf (lumpState cand X') :=
    (keyOf_lump_enc X' c1 c2 c3 c4 hwf hL).symm
  rw [hk1, hk2] at hfin
  obtain ⟨hupk, hul⟩ := look_pack t h X' (show 1 < 128 by norm_num) hwf
  unfold G3K.Spec.exitNext at hfin
  rw [gather_exit _ _ _ hupk hul _ ((segsOK_phase (X.i + 1) (by omega) (by omega)).2 hq).2] at hfin
  refine (final_V s X hi a R hI _ (exit_le _ hul _) _ _ _ hfin hsv hsl o hF).trans
    (add_le_add le_rfl ?_)
  have hvmem : incr o X.i X.e ∈ allVecs (5 - (X.i + 1)) 8 :=
    mem_allVecs _ _ _ (by rw [incr_length]; omega)
      (by have := incr_sum o X hF hi; rwa [show cand.T = 8 from rfl] at this)
  obtain ⟨-, -, -, hcp1⟩ := lanesOK (X.i + 1) (by omega) (by omega) _ hvmem
  rw [hcp1 hq]
  split_ifs with h1
  · have hc := incr_cons o X.i X.e hi
    rw [hc] at h1
    simp only [List.headD_cons] at h1
    have hv' : (incr o X.i X.e).tail = incr o X'.i X'.e := by
      show _ = incr o (X.i + 1) (X.e + 1)
      rw [hc, List.tail_cons, show oget o X.i = X.e + 1 by omega]
    simp only [Option.elim_some]
    rw [hv']
    have he' : X'.e ≤ cand.T := by
      show X.e + 1 ≤ cand.T; have := oget_le_T o X hF hi; omega
    exact exit_lane t h X X' hi he hq he' le_rfl (by norm_num) hwf o
      ((fits_succ o X hF hq (X.e + 1) 1 X.σ (by omega)).2 (by omega))
  · simp

/-- `x` in lane `1` of `L ≥ 2` lanes. -/
theorem eq_pack_lane1 (W L x : ℕ) (hL : 1 < L) :
    x * 2 ^ W = pack W L (fun l => if l = 1 then x else 0) := by
  unfold pack
  rw [Finset.sum_eq_single 1 (fun l _ hl => by simp [hl])
    (fun h => absurd (Finset.mem_range.2 hL) h)]
  simp

/-- **The exit of the last frog** (`p = 1`, `q = J`): the chain is absorbed, with outputs `o` iff
the last frog finishes at `o_3`. -/
theorem finAbs_V (t : G3K.Tree) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (s : G3K.E)
    (hsv : pack 96 (G3K.phase (X.i + 1)).nL (fun l => lane 96 l s.v) = s.v)
    (hsl : ∀ l, lane 96 l s.v < 2 ^ 47) (a : G3K.Spec.Acc) (R : (Fin 4 → ℕ) → ℝ≥0∞)
    (hI : InvV X a R) (e0 : ℕ) (hq : X.i + 1 = G3K.cJ)
    (hfin : G3K.Spec.final s (X.i + 1) a (G3K.exitLo * G3K.Spec.two40 * 2 ^ 96) 0 e0 true = true)
    (o : Fin 4 → ℕ) (hF : Fits o X) :
    (lane 96 (laneIdx (incr o X.i X.e)) s.v : ℝ≥0∞) / 2 ^ 40 ≤
      R o + 5⁻¹ * tauV t o (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        ⟨X.i + 1, X.e + 1, 1, X.σ,
          Function.update X.out ⟨X.i, hX.2.1⟩ ((X.e + 1 : ℕ) : ℕ∞)⟩) := by
  have hi : X.i < 4 := hX.2.1
  have he : X.e ≤ cand.T := hX.2.2.1
  have hX3 : X.i = 3 := by have : G3K.cJ = 4 := rfl; omega
  have hnL : 1 < (G3K.phase (X.i + 1)).nL := by rw [hX3]; decide
  rw [show G3K.exitLo * G3K.Spec.two40 * 2 ^ 96 = G3K.exitLo * 2 ^ 40 * 2 ^ 96 from rfl,
    eq_pack_lane1 96 _ _ hnL] at hfin
  refine (final_V s X hi a R hI _ (fun l => by
      split_ifs
      · exact Nat.mul_le_mul_left _ (by norm_num)
      · exact Nat.zero_le _) _ _ _ hfin hsv hsl o hF).trans (add_le_add le_rfl ?_)
  have hv : incr o X.i X.e = [oget o X.i - X.e] := by
    rw [incr_cons o X.i X.e hi]
    congr 1
    simp [incr, hX3]
  rw [hv, laneIdx_single]
  split_ifs with h1
  · have ho3 : o 3 = X.e + 1 := by
      have := oget_eq o X.i hi
      rw [show (⟨X.i, hi⟩ : Fin 4) = 3 from Fin.ext hX3] at this
      omega
    have he' : X.e + 1 ≤ cand.T := ho3 ▸ hF.2.2.2
    rw [domNext_abs t X _ hi he he' (by norm_num) (by show 4 ≤ X.i + 1; omega)]
    calc ((G3K.exitLo * 2 ^ 40 : ℕ) : ℝ≥0∞) / 2 ^ 88 ≤ 5⁻¹ * (((2 ^ 40 : ℕ) : ℝ≥0∞) / 2 ^ 40) :=
          exitLo_le _
      _ = 5⁻¹ * 1 := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_self (by positivity) (by simp)]
      _ ≤ 5⁻¹ * tauV t o (X, false) (⟨X.i + 1, X.e + 1, 1, X.σ,
            Function.update X.out ⟨X.i, hX.2.1⟩ ((X.e + 1 : ℕ) : ℕ∞)⟩, false) := by
          gcongr
          unfold tauV absInd
          rw [if_pos ⟨rfl, hi, rfl, by show 4 ≤ X.i + 1; omega,
            (fits_abs o X hF hX3 (X.e + 1)).2 ho3⟩]
          exact le_self_add
  · simp

/-- **The exit and the comparisons** of the checker at a covered state. -/
theorem finish_V (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (c1 c2 c3 c4 : ℕ)
    (hL : (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4]) (s : G3K.E)
    (hsv : pack 96 (G3K.phase (X.i + 1)).nL (fun l => lane 96 l s.v) = s.v)
    (hsl : ∀ l, lane 96 l s.v < 2 ^ 47) (a : G3K.Spec.Acc) (R : (Fin 4 → ℕ) → ℝ≥0∞)
    (hI : InvV X a R) (e0 : ℕ)
    (hfin : G3K.Spec.finish t s (X.i + 1) c1 c2 c3 c4 X.p a e0 = true)
    (o : Fin 4 → ℕ) (hF : Fits o X) :
    (lane 96 (laneIdx (incr o X.i X.e)) s.v : ℝ≥0∞) / 2 ^ 40 ≤
      R o + 5⁻¹ * tauV t o (X, false) (domNext cand.T 16 (keepOf t) (lumpState cand) (X, false)
        (rstep cand.childStep X (0, 0))) := by
  have hi : X.i < 4 := hX.2.1
  rw [rstep_exit X hi]
  unfold G3K.Spec.finish at hfin
  by_cases hp : X.p = 1
  · rw [if_pos hp] at hfin
    rw [if_pos (show X.p - 1 = 0 by omega)]
    by_cases hq : X.i + 1 = G3K.cJ
    · rw [if_pos hq] at hfin
      exact finAbs_V t X hX s hsv hsl a R hI e0 hq hfin o hF
    · rw [if_neg hq] at hfin
      have hq4 : X.i + 1 < 4 := by have : G3K.cJ = 4 := rfl; omega
      exact finNext_V t h X hX c1 c2 c3 c4 hL s hsv hsl a R hI e0 hq4 hfin o hF
  · rw [if_neg hp] at hfin
    rw [if_neg (show X.p - 1 ≠ 0 by have : 1 ≤ X.p := hX.2.2.2.1; omega)]
    exact finSame_V t h X hX c1 c2 c3 c4 hL s hsv hsl a R hI e0 hp hfin o hF

/-- The sorted codes of four children. -/
theorem sort_codes (X : RState CState 4 4) :
    ∃ c1 c2 c3 c4, (codeMs X.σ).sort (· ≤ ·) = [c1, c2, c3, c4] := by
  have hlen : ((codeMs X.σ).sort (· ≤ ·)).length = 4 := by
    rw [Multiset.length_sort]; simp [codeMs]
  generalize (codeMs X.σ).sort (· ≤ ·) = l at hlen ⊢
  rcases l with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, l⟩⟩⟩⟩⟩ <;> simp at hlen
  exact ⟨c1, c2, c3, c4, rfl⟩

/-- **Item 4 at a covered state**: `Vs` is at most the right side of the absorption system. -/
theorem Vs_sub_cov (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (X : RState CState 4 4)
    (hX : Covered t (X, false)) (o : Fin 4 → ℕ) (hF : Fits o X) :
    Vs t o (X, false) ≤ ∫⁻ ξ, tauV t o (X, false) (gT t (X, false) ξ) ∂nuC := by
  have hwf : ∀ c, cand.ChildWF (X.σ c) := hX.2.2.2.2.2.1
  have hp16 : X.p ≤ 16 := hX.2.2.2.2.1
  have hk : (entry t X).key = keyOf X := hX.2.2.2.2.2.2
  obtain ⟨c1, c2, c3, c4, hL⟩ := sort_codes X
  have hmem : ∀ x ∈ [c1, c2, c3, c4], x < 38 := by
    intro x hx
    rw [← hL, Multiset.mem_sort] at hx
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hx
    exact code_lt _ (hwf c)
  have h1 := hmem c1 (by simp)
  have h2 := hmem c2 (by simp)
  have h3 := hmem c3 (by simp)
  have h4 := hmem c4 (by simp)
  have hk' : keyOf X = G3K.Spec.enc (X.i + 1) c1 c2 c3 c4 X.p := keyOf_enc X c1 c2 c3 c4 hL
  obtain ⟨hdq, hd1, hd2, hd3, hd4, hdp⟩ :=
    dec_enc (X.i + 1) c1 c2 c3 c4 X.p (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hbnd, hst⟩ := G3K.Spec.checkAll_sound h (keyOf X) hk
  have hent : entry t X = t.find (keyOf X) := rfl
  generalize hs : t.find (keyOf X) = s at hbnd hst hent
  rw [hk', hdq] at hbnd
  rw [hk'] at hst
  unfold G3K.Spec.stateCheck at hst
  rw [hdq, hd1, hd2, hd3, hd4, hdp] at hst
  unfold G3K.Spec.checkS at hst
  obtain ⟨hsv, hsl0, -, -⟩ := boundsOK_sound s (X.i + 1) hbnd
  have key := finish_V t h X hX c1 c2 c3 c4 hL s hsv (fun l => (hsl0 l).1) _ _
    (moves_V t h X hX c1 c2 c3 c4 hL) _ hst o hF
  unfold Vs
  rw [if_pos ⟨hX, hF⟩]
  rw [show gT t = candDom 16 (keepOf t) from rfl,
    lintegral_candDom 16 (keepOf t) (tauV t o (X, false)) (X, false) hwf, add_comm]
  rw [hent]
  exact key

/-- **Item 4 (V)** from the checker: `Vs t o` is a sub-solution. -/
theorem Vs_sub_of_check (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (o : Fin 4 → ℕ) :
    Vs t o ≤ (fun y => nuC (absUnflagged (gT t) o y)) +
      FrogModel.LinSys.app (fkKernel (gT t) (fun _ _ => 1) nuC) (Vs t o) := by
  intro y
  show Vs t o y ≤ nuC (absUnflagged (gT t) o y) +
    FrogModel.LinSys.app (fkKernel (gT t) (fun _ _ => 1) nuC) (Vs t o) y
  rw [rhsV_eq]
  by_cases hc : Covered t y ∧ Fits o y.1
  · obtain ⟨X, b⟩ := y
    have hb : b = false := hc.1.1
    subst hb
    exact Vs_sub_cov t h X hc.1 o hc.2
  · unfold Vs
    rw [if_neg hc]
    exact zero_le

/-- `Vs` is at most `128`: its lanes are below `2^47`, in units of `2^-40`. -/
theorem Vs_le_of_check (t : G3K.Tree) (h : G3K.Spec.checkAll t = true) (o : Fin 4 → ℕ)
    (y : RState CState 4 4 × Bool) : Vs t o y ≤ 128 := by
  unfold Vs
  split_ifs with hc
  · have hb := boundsOK_sound _ _ (entry_bounds t h y.1 hc.1.2.2.2.2.2.1
      (by have := hc.1.2.2.2.2.1; omega) hc.1.2.2.2.2.2.2)
    have hl := (hb.2.1 (laneIdx (incr o y.1.i y.1.e))).1
    refine ENNReal.div_le_of_le_mul ?_
    calc (lane 96 (laneIdx (incr o y.1.i y.1.e)) (entry t y.1).v : ℝ≥0∞) ≤ ((2 ^ 47 : ℕ) : ℝ≥0∞) := by
          exact_mod_cast hl.le
      _ = 128 * 2 ^ 40 := by norm_num
  · exact zero_le

end FrogModel.Engine.G3
