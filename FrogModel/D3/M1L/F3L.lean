module

public import FrogModel.D3.M1L.GenIface
public import FrogModel.D3.M1L.F1Gen
public import FrogModel.D3.M1L.Laws

@[expose] public section

/-!
# Proposition 13.3: the bounds from a stored run

Proposition 13.3 of the paper, against the statement `Iface.f3L` of
FrogModel/D3/Interfaces/Seed.lean. Stored laws `rho*_h`, `K*_h` below the recursions of Section 13
off the bottom are the laws of M1_L for the keep functions `kappa = rho*/Rhat` (`keepF`, realized by
coin sets); then the top law of Lemma 13.2 (`top_law_gen`) is `Wtop_(k+1)[rho*_(m-1), K*_(m-1)]`,
and Lemma 13.1 (`f1_gen`) puts the count under `G_m(k)` on the frog paths, whose law is the planted
model.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3

/-! ## The recursions of the interface: height 0 and congruence -/

/-- The H recursion of the interface with no unmarked child, one frog: `Khat_0(0 -> .)`. -/
theorem Yrec_zero_one (V P L : ℕ) (hV : 1 ≤ V) (hL : 1 ≤ L) (rb : ℕ → ℝ) (a f : ℕ) :
    Iface.Yrec V P L rb 0 1 a f = Iface.Khat0 L 0 a f := by
  have hpL_lt_one : Iface.pL L < 1 := by
    rw [Iface.pL]
    have h_denom_pos : 0 < (3 : ℝ) ^ L - 1 := by
      have h_one_lt_pow : 1 < (3 : ℝ) ^ L :=
        one_lt_pow₀ (by norm_num : 1 < (3 : ℝ)) (by omega : L ≠ 0)
      linarith
    have h_num_lt_denom : (3 : ℝ) ^ (L - 1) - 1 < (3 : ℝ) ^ L - 1 := by
      have h_pow_lt : (3 : ℝ) ^ (L - 1) < (3 : ℝ) ^ L := by
        by_cases hL0 : L = 0
        · omega
        · have hL1 : L - 1 < L := by omega
          exact pow_lt_pow_right₀ (by norm_num : 1 < (3 : ℝ)) hL1
      linarith
    exact (div_lt_one h_denom_pos).mpr h_num_lt_denom
  have hden_ne_zero : 4 - 3 * Iface.pL L ≠ 0 := by
    intro hzero
    have : Iface.pL L = 4/3 := by linarith
    linarith [hpL_lt_one, this]
  have hden2_ne_zero : 1 - 3 * Iface.pL L / 4 ≠ 0 := by
    intro hzero
    apply hden_ne_zero
    linarith
  simp only [Iface.Yrec, Iface.Khat0, Iface.upV]
  by_cases hf : f = 0
  · subst hf
    simp
    by_cases ha0 : a = 0
    · subst ha0
      simp
      field_simp [hden_ne_zero]
      rw [Iface.qL]
      field_simp [hden_ne_zero]
      ring
    · by_cases ha1 : a = 1
      · subst ha1
        simp
        by_cases hV1 : V = 1
        · subst hV1
          simp
          field_simp [hden_ne_zero]
          rw [Iface.qL]
          field_simp [hden_ne_zero]
        · have hV_gt1 : 1 < V := by omega
          simp [hV_gt1]
          field_simp [hden_ne_zero]
          rw [Iface.qL]
          field_simp [hden_ne_zero]
      · have ha_ge2 : 2 ≤ a := by omega
        simp [ha0, ha1]
        field_simp [hden2_ne_zero]
        split_ifs with hlt heq heq2
        · -- a < V, a-1 = 0: impossible since a ≥ 2
          have h_ne_zero : a - 1 ≠ 0 := by omega
          exfalso; exact h_ne_zero heq
        · -- a < V, a-1 ≠ 0: numerator = 0
          simp
        · -- ¬ a < V, a = V, V-1 = 0, V = 0: impossible
          omega
        · -- ¬ a < V, a = V, V-1 = 0, V ≠ 0: V = 1 contradicts V ≥ 2
          have hV_ge2 : 2 ≤ V := by rw [← heq2]; exact ha_ge2
          omega
        · -- ¬ a < V, a = V, V-1 ≠ 0, V = 0: impossible
          omega
        · -- ¬ a < V, a = V, V-1 ≠ 0, V ≠ 0: numerator = 0
          simp
        · -- ¬ a < V, a ≠ V: numerator = 0
          simp
  · simp [hf]

/-- The H recursion of the interface with no unmarked child, two frogs: `Rhat_0`. -/
theorem Yrec_zero_two (V P L : ℕ) (hV : 1 ≤ V) (hL : 1 ≤ L) (rb : ℕ → ℝ) (b f : ℕ) :
    Iface.Yrec V P L rb 0 2 b f = Iface.Rhat0 V L b f := by
  have hpL : Iface.pL L < 1 := by
    rw [Iface.pL]
    have h1 : (1 : ℝ) < 3 ^ L := one_lt_pow₀ (by norm_num) (by omega)
    have h2 : (3 : ℝ) ^ (L - 1) < 3 ^ L := pow_lt_pow_right₀ (by norm_num) (by omega)
    exact (div_lt_one (by linarith)).2 (by linarith)
  have hd : (4 : ℝ) - 3 * Iface.pL L ≠ 0 := by linarith
  have hY1 : (fun a f' => Iface.Yrec V P L rb 0 1 a f') = fun a f' => Iface.Khat0 L 0 a f' := by
    funext a f'
    exact Yrec_zero_one V P L hV hL rb a f'
  have hstep : Iface.Yrec V P L rb 0 2 b f =
      Iface.qL L * Iface.upV V (fun a f' => Iface.Khat0 L 0 a f') b f +
        (1 - Iface.qL L) * Iface.Khat0 L 0 b f := by
    rw [Iface.Yrec.eq_2, hY1, Yrec_zero_one V P L hV hL rb b f]
    simp only [CharP.cast_eq_zero, sub_zero, ↓reduceDIte, add_zero, Iface.qL]
    field_simp
    ring
  rw [hstep]
  by_cases hf : f = 0
  · subst hf
    have hR : Iface.Rhat0 V L b 0 = (if 0 = b then (1 - Iface.qL L) ^ 2 else 0) +
        (if 1 = b then 2 * Iface.qL L * (1 - Iface.qL L) else 0) +
        (if min 2 V = b then Iface.qL L ^ 2 else 0) := by
      simp only [Iface.Rhat0, ↓reduceIte, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have e0 : min 0 V = 0 := by omega
      have e1 : min 1 V = 1 := by omega
      rw [e0, e1]
      simp only [Nat.choose]
      split_ifs <;> push_cast <;> ring
    rw [hR]
    simp only [Iface.upV, Iface.Khat0, ↓reduceIte]
    split_ifs <;> first | ring1 | (exfalso; omega)
  · simp [Iface.upV, Iface.Khat0, Iface.Rhat0, hf]

/-- The H recursion reads its input at answers `≤ V` only. -/
theorem Yrec_congr (V P L : ℕ) (rb rb' : ℕ → ℝ) (h : ∀ b ≤ V, rb b = rb' b) (f s a g : ℕ) :
    Iface.Yrec V P L rb f s a g = Iface.Yrec V P L rb' f s a g := by
  induction f using Nat.strong_induction_on generalizing s a g with
  | h f IHf =>
    induction s generalizing a g with
    | zero => rw [Iface.Yrec.eq_1, Iface.Yrec.eq_1]
    | succ s IHs =>
      rw [Iface.Yrec.eq_2, Iface.Yrec.eq_2]
      have hfun : (fun a' f'' => Iface.Yrec V P L rb f s a' f'') =
          fun a' f'' => Iface.Yrec V P L rb' f s a' f'' := by
        funext a' f''
        exact IHs a' f''
      rw [hfun, IHs a g]
      congr 2
      split_ifs with hf
      · rfl
      · congr 1
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [h b (Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)), IHf (f - 1) (by omega)]

/-- The R recursion reads its inputs at answers `≤ V`, at types `< 4`, and the kernels only at the
types it can reach (`Rc`): those of its children, of the outcomes of `rho` and of the outcomes of
the kernels it reads. -/
theorem Wrec_congr (V P : ℕ) (hV : 1 ≤ V) (ρ ρ' : ℕ → ℕ → ℝ) (K K' : ℕ → ℕ → ℕ → ℝ)
    (Rc : ℕ → Prop)
    (hρ : ∀ b ≤ V, ∀ f < 4, ρ b f = ρ' b f)
    (hρR : ∀ b ≤ V, ∀ f < 4, ρ b f ≠ 0 → Rc f)
    (hK : ∀ t < 4, Rc t → ∀ a ≤ V, ∀ f < 4, K t a f = K' t a f)
    (hKR : ∀ t < 4, Rc t → ∀ a ≤ V, ∀ f < t, K t a f ≠ 0 → Rc f)
    (σ : Kid) (hσ : ∀ (c : Fin 3) (t : Fin 4), σ c = some t → Rc t) (n x g : ℕ) :
    Iface.Wrec V P ρ K σ n x g = Iface.Wrec V P ρ' K' σ n x g := by
  have key : ∀ r (σ : Kid), Iface.rankS σ = r → (∀ (c : Fin 3) (t : Fin 4), σ c = some t → Rc t) →
      ∀ n x g, Iface.Wrec V P ρ K σ n x g = Iface.Wrec V P ρ' K' σ n x g := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r IH =>
      intro σ hr hσ n
      induction n with
      | zero => intro x g; rw [Iface.Wrec.eq_1, Iface.Wrec.eq_1]
      | succ n IHn =>
        intro x g
        have hupd : ∀ (c : Fin 3) (f' : Fin 4), Rc f' →
            ∀ (c' : Fin 3) (t : Fin 4), Function.update σ c (some f') c' = some t → Rc t := by
          intro c f' hf' c' t h
          by_cases hcc : c' = c
          · subst hcc
            rw [Function.update_self, Option.some.injEq] at h
            exact h ▸ hf'
          · rw [Function.update_of_ne hcc] at h
            exact hσ c' t h
        have hloop : Iface.loopS K σ = Iface.loopS K' σ := by
          unfold Iface.loopS
          congr 1
          refine Finset.sum_congr rfl fun c _ => ?_
          rcases hc : σ c with _ | t
          · rfl
          · exact hK t t.isLt (hσ c t hc) 1 hV t t.isLt
        have hlost : Iface.lostS K σ = Iface.lostS K' σ := by
          unfold Iface.lostS
          congr 1
          refine Finset.sum_congr rfl fun c _ => ?_
          rcases hc : σ c with _ | t
          · rfl
          · exact hK t t.isLt (hσ c t hc) 0 (Nat.zero_le _) t t.isLt
        rw [Iface.Wrec.eq_2, Iface.Wrec.eq_2, hloop, hlost]
        congr 2
        · have hfun : (fun x' g' => Iface.Wrec V P ρ K σ n x' g') =
              fun x' g' => Iface.Wrec V P ρ' K' σ n x' g' := by
            funext x' g'
            exact IHn x' g'
          rw [hfun, IHn x g]
        · congr 1
          refine Finset.sum_congr rfl fun c _ => ?_
          rcases hc : σ c with _ | t
          · simp only
            refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun f' _ => ?_
            have hbV : b ≤ V := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
            by_cases h0 : ρ b f' = 0
            · rw [h0, ← hρ b hbV f' f'.isLt, h0, zero_mul, zero_mul]
            · rw [hρ b hbV f' f'.isLt]
              congr 1
              refine IH _ ?_ _ rfl (hupd c f' (hρR b hbV f' f'.isLt h0)) _ x g
              rw [← hr]
              exact Iface.rankS_update_lt σ c _ (by rw [hc]; simp only [Iface.tval]; omega)
          · simp only
            refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun f' _ => ?_
            have haV : a ≤ V := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
            split_ifs with hf
            · have hRt := hσ c t hc
              rw [← hK t t.isLt hRt a haV f' f'.isLt]
              by_cases h0 : K t a f' = 0
              · rw [h0, zero_mul, zero_mul]
              · congr 1
                refine IH _ ?_ _ rfl (hupd c f' (hKR t t.isLt hRt a haV f' hf h0)) _ x g
                rw [← hr]
                exact Iface.rankS_update_lt σ c _ (by rw [hc]; simp only [Iface.tval]; exact hf)
            · rfl
  exact key _ σ rfl hσ n x g

/-! ## The kill -/

/-- An end value of `Gen` at ups `≤ V` is the combination of the indicators of its outcomes. -/
theorem term_ind (V : ℕ) (T : ℕ → ℕ → ℝ) (k : Kid) (a : ℕ) (ha : a ≤ V) :
    T a (nN k) = ∑ x ∈ Finset.range (V + 1), ∑ g ∈ Finset.range 4, ind x g k a * T x g := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single (nN k)]
  · simp [ind]
  · intro g _ hg; simp [ind, Ne.symm hg]
  · intro h; exact absurd (Finset.mem_range.2 (nN_lt k)) h
  · intro x _ hx
    refine Finset.sum_eq_zero fun g _ => ?_
    simp [ind, Ne.symm hx]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- The R law at height `h` after the kill, from the law before it. -/
theorem lawsAt_R (p : Params) (h : ℕ) (q : LawIn) (b f : ℕ) :
    (lawsAt p h q).1 b f = ∑ a ∈ Finset.range (p.V + 1), ∑ g ∈ Finset.range 4,
      GenH p h true q (fun _ => 0) (ind a g) (initK h) 2 0 * killP (κm p true h 3 a g) a g b f := by
  show GenH p h true q (fun _ => 0)
      (fun k a => killP (κm p true h 3 a (nN k)) a (nN k) b f) (initK h) 2 0 = _
  unfold GenH
  rw [Gen_congr _ _ _ _ _ _ _ _ (fun k a => ∑ i ∈ Finset.range (p.V + 1) ×ˢ Finset.range 4,
      killP (κm p true h 3 i.1 i.2) i.1 i.2 b f * ind i.1 i.2 k a)
    (fun k a ha => by
      rw [Finset.sum_product, term_ind p.V (fun x g => killP (κm p true h 3 x g) x g b f) k a ha]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun g _ => mul_comm _ _)
    _ _ _ (Nat.zero_le _), Gen_sum0, Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun g _ => mul_comm _ _

/-- The H law of type `t` at height `h` after the kill, from the law before it. -/
theorem lawsAt_K (p : Params) (h : ℕ) (q : LawIn) (t b f : ℕ) :
    (lawsAt p h q).2 t b f = ∑ a ∈ Finset.range (p.V + 1), ∑ g ∈ Finset.range 4,
      GenH p h false q (fun _ => 0) (ind a g) (kidOf h t) 1 0 * killP (κm p false h t a g) a g b f := by
  show GenH p h false q (fun _ => 0)
      (fun k a => killP (κm p false h t a (nN k)) a (nN k) b f) (kidOf h t) 1 0 = _
  unfold GenH
  rw [Gen_congr _ _ _ _ _ _ _ _ (fun k a => ∑ i ∈ Finset.range (p.V + 1) ×ˢ Finset.range 4,
      killP (κm p false h t i.1 i.2) i.1 i.2 b f * ind i.1 i.2 k a)
    (fun k a ha => by
      rw [Finset.sum_product, term_ind p.V (fun x g => killP (κm p false h t x g) x g b f) k a ha]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun g _ => mul_comm _ _)
    _ _ _ (Nat.zero_le _), Gen_sum0, Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun g _ => mul_comm _ _

/-- The kill off the bottom outcome: the mass of the outcome times its keep probability. -/
theorem kill_off (V : ℕ) (pre κ : ℕ → ℕ → ℝ) (b f : ℕ) (hb : b ≤ V) (hf : f < 4)
    (hbf : b ≠ 0 ∨ f ≠ 0) :
    ∑ a ∈ Finset.range (V + 1), ∑ g ∈ Finset.range 4, pre a g * killP (κ a g) a g b f =
      pre b f * κ b f := by
  have h0 : ¬(b = 0 ∧ f = 0) := by omega
  simp only [killP, h0, ↓reduceIte, add_zero, mul_ite, mul_zero, ite_and]
  rw [Finset.sum_eq_single b, Finset.sum_eq_single f]
  · simp
  · intro g _ hg; simp [hg]
  · intro h; exact absurd (Finset.mem_range.2 hf) h
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- Two laws of the same total mass that agree off the bottom agree. -/
theorem eq_of_off_bottom (V n : ℕ) (w w' : ℕ → ℕ → ℝ)
    (hoff : ∀ a ≤ V, ∀ f ≤ n, (a ≠ 0 ∨ f ≠ 0) → w a f = w' a f)
    (hs : ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (n + 1), w a f =
      ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (n + 1), w' a f) :
    ∀ a ≤ V, ∀ f ≤ n, w a f = w' a f := by
  intro a ha f hf
  by_cases h : a ≠ 0 ∨ f ≠ 0
  · exact hoff a ha f hf h
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ f = 0 := by omega
    have hd : ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (n + 1), (w a f - w' a f) = 0 := by
      simp only [Finset.sum_sub_distrib]
      linarith
    rw [Finset.sum_eq_single 0 (fun a ha ha0 => Finset.sum_eq_zero fun f hf => sub_eq_zero.2
        (hoff a (by simp at ha; omega) f (by simp at hf; omega) (Or.inl ha0)))
        (fun h => absurd (by simp) h),
      Finset.sum_eq_single 0 (fun f hf hf0 => sub_eq_zero.2
        (hoff 0 (Nat.zero_le _) f (by simp at hf; omega) (Or.inr hf0)))
        (fun h => absurd (by simp) h)] at hd
    linarith

/-- An R law of the recursion has total mass `1`. -/
theorem inpOK_sumR (V : ℕ) (q : LawIn) (hq : InpOK V q) :
    ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range 4, q.1 a f = 1 := by
  rw [Finset.sum_comm, ← hq.2.1, Fin.sum_univ_eq_sum_range (fun f => ∑ b ∈ Finset.range (V + 1), q.1 b f) 4]

/-- An H law of type `t` of the recursion has total mass `1` on `{0..V} × {0..t}`. -/
theorem inpOK_sumK (V : ℕ) (hV : 1 ≤ V) (q : LawIn) (hq : InpOK V q) (t : ℕ) (ht : t ≤ 3) :
    ∑ a ∈ Finset.range (V + 1), ∑ f ∈ Finset.range (t + 1), q.2 t a f = 1 := by
  obtain ⟨-, -, -, -, h5, -, h7⟩ := hq
  have hcol : ∑ a ∈ Finset.range (V + 1), q.2 t a t = q.2 t 0 t + q.2 t 1 t := by
    obtain ⟨V', rfl⟩ : ∃ V', V = V' + 1 := ⟨V - 1, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    rw [Finset.sum_eq_zero fun i _ => h7 t (i + 1 + 1) (by omega)]
    ring
  have h5t := h5 ⟨t, by omega⟩
  have hrest : (∑ f : Fin 4, if f < (⟨t, by omega⟩ : Fin 4) then
      ∑ a' ∈ Finset.range (V + 1), q.2 t a' f else 0) =
      ∑ f ∈ Finset.range t, ∑ a ∈ Finset.range (V + 1), q.2 t a f := by
    have e : (∑ f : Fin 4, if f < (⟨t, by omega⟩ : Fin 4) then
        ∑ a' ∈ Finset.range (V + 1), q.2 t a' f else 0) =
        ∑ f : Fin 4, (fun i : ℕ => if i < t then ∑ a' ∈ Finset.range (V + 1), q.2 t a' i else 0) f :=
      Finset.sum_congr rfl fun f _ => by
        by_cases hf : (f : ℕ) < t
        · have h1 : f < (⟨t, by omega⟩ : Fin 4) := hf
          simp only [h1, hf, ↓reduceIte]
        · have h1 : ¬ f < (⟨t, by omega⟩ : Fin 4) := hf
          simp only [h1, hf, ↓reduceIte]
    rw [e, Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < t then
      ∑ a' ∈ Finset.range (V + 1), q.2 t a' i else 0) 4, ← Finset.sum_filter]
    congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only at h5t
  rw [Finset.sum_comm, Finset.sum_range_succ, hcol]
  linarith

/-! ## The keep functions -/

/-- `x / y` clamped to `[0, 1]`, and `0` when `y ≤ 0`. -/
noncomputable def ratio01 (x y : ℝ) : ℝ := if y ≤ 0 then 0 else min 1 (max 0 (x / y))

theorem ratio01_mem (x y : ℝ) : 0 ≤ ratio01 x y ∧ ratio01 x y ≤ 1 := by
  unfold ratio01
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem mul_ratio01 (x y : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ y) : y * ratio01 x y = x := by
  unfold ratio01
  split_ifs with hy
  · linarith
  · have hy' : 0 < y := lt_of_not_ge hy
    have hq0 : 0 ≤ x / y := div_nonneg h0 hy'.le
    have hq1 : x / y ≤ 1 := (div_le_one hy').2 h1
    rw [max_eq_right hq0, min_eq_right hq1]
    field_simp

/-- A set of coins of mass `x ∈ [0, 1]`. -/
noncomputable def coinSet (x : ℝ) : Set ℕ :=
  if h : ENNReal.ofReal x ≤ 1 then Classical.choose (exists_coin_set _ h) else Set.univ

theorem coinLaw_coinSet (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : (coinLaw (coinSet x)).toReal = x := by
  have h : ENNReal.ofReal x ≤ 1 := ENNReal.ofReal_le_one.2 h1
  simp only [coinSet, h, ↓reduceDIte]
  rw [Classical.choose_spec (exists_coin_set _ h), ENNReal.toReal_ofReal h0]

/-! ## The planted model -/

/-- The woken set `Woken` of M1L/Planted.lean and that of the interface agree. -/
theorem woken_iff (m k : ℕ) (π : Frog → ℕ → Step 3) (φ : Frog) :
    Woken m k π φ ↔ Iface.Woken m k π φ := by
  constructor
  · intro h
    induction h with
    | ent i hi => exact .ent i hi
    | wake φ v n _ hv hp ih => exact .wake φ v n ih hv hp
  · intro h
    induction h with
    | ent i hi => exact .ent i hi
    | wake φ v n _ hv hp ih => exact .wake φ v n ih hv hp

/-- The frogs that can wake at height `m` with `k` entrants. -/
noncomputable def frogsF (m k : ℕ) : Finset Frog :=
  (Finset.range k).image Sum.inl ∪ (List.finite_length_le (Fin 3) m).toFinset.image Sum.inr

theorem woken_mem_frogsF (m k : ℕ) (π : Frog → ℕ → Step 3) (φ : Frog) (h : Woken m k π φ) :
    φ ∈ frogsF m k := by
  induction h with
  | ent i hi =>
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩)
  | wake φ v n _ hv _ _ =>
    exact Finset.mem_union_right _ (Finset.mem_image.2
      ⟨v, (Set.Finite.mem_toFinset _).2 hv, rfl⟩)

/-- The planted count is at most the number of frogs that can wake. -/
theorem plantedG_le_card (m k : ℕ) (π : Frog → ℕ → Step 3) :
    plantedG m k π ≤ ((frogsF m k).card : ℕ∞) := by
  unfold plantedG
  rw [← Set.encard_coe_eq_coe_finsetCard]
  exact Set.encard_le_encard fun φ hφ => woken_mem_frogsF m k π φ hφ.1

/-- The planted count as a finite sum of indicators. -/
theorem plantedG_eq_sum (m k : ℕ) (π : Frog → ℕ → Step 3) :
    plantedG m k π = ∑ φ ∈ frogsF m k,
      ({π' | Woken m k π' φ ∧ ∃ n, pos π' φ n = none} : Set (Frog → ℕ → Step 3)).indicator
        (fun _ => (1 : ℕ∞)) π := by
  classical
  have hS : {φ | Woken m k π φ ∧ ∃ n, pos π φ n = none} =
      ↑((frogsF m k).filter fun φ => Woken m k π φ ∧ ∃ n, pos π φ n = none) := by
    ext φ
    simp only [Set.mem_ofPred_eq, Finset.coe_filter]
    exact ⟨fun h => ⟨woken_mem_frogsF m k π φ h.1, h⟩, fun h => h.2⟩
  unfold plantedG
  rw [hS, Set.encard_coe_eq_coe_finsetCard, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp

/-- The woken set reached in `j` rounds of waking. -/
def wIter (m k : ℕ) (π : Frog → ℕ → Step 3) : ℕ → Frog → Prop
  | 0, φ => ∃ i < k, φ = Sum.inl i
  | j + 1, φ => wIter m k π j φ ∨
      ∃ ψ v n, φ = Sum.inr v ∧ v.length ≤ m ∧ wIter m k π j ψ ∧ pos π ψ n = some v

theorem woken_iff_iter (m k : ℕ) (π : Frog → ℕ → Step 3) (φ : Frog) :
    Woken m k π φ ↔ ∃ j, wIter m k π j φ := by
  have mono : ∀ j j', j ≤ j' → ∀ ψ, wIter m k π j ψ → wIter m k π j' ψ := by
    intro j j' hjj'
    induction hjj' with
    | refl => exact fun _ h => h
    | step _ ih => exact fun ψ h => Or.inl (ih ψ h)
  constructor
  · intro h
    induction h with
    | ent i hi => exact ⟨0, i, hi, rfl⟩
    | wake ψ v n _ hv hp ih =>
      obtain ⟨j, hj⟩ := ih
      exact ⟨j + 1, Or.inr ⟨ψ, v, n, rfl, hv, hj, hp⟩⟩
  · rintro ⟨j, hj⟩
    induction j generalizing φ with
    | zero =>
      obtain ⟨i, hi, rfl⟩ := hj
      exact .ent i hi
    | succ j ih =>
      rcases hj with hj | ⟨ψ, v, n, rfl, hv, hψ, hp⟩
      · exact ih φ hj
      · exact .wake ψ v n (ih ψ hψ) hv hp

/-- A position of a frog is an event of finitely many steps. -/
theorem measurable_pos (φ : Frog) (n : ℕ) (o : Option (Vertex 3)) :
    MeasurableSet {π : Frog → ℕ → Step 3 | pos π φ n = o} := by
  have hm : ∀ n, Measurable fun π : Frog → ℕ → Step 3 => pos π φ n := by
    intro n
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      have h2 : Measurable fun π : Frog → ℕ → Step 3 => (pos π φ n, π φ n) :=
        ih.prodMk ((measurable_pi_apply n).comp (measurable_pi_apply φ))
      exact (measurable_of_countable (fun z : Option (Vertex 3) × Step 3 => stepStar z.1 z.2)).comp h2
  exact hm n (MeasurableSet.of_discrete : MeasurableSet ({o} : Set (Option (Vertex 3))))

theorem measurable_wIter (m k j : ℕ) (φ : Frog) :
    MeasurableSet {π : Frog → ℕ → Step 3 | wIter m k π j φ} := by
  induction j generalizing φ with
  | zero => exact MeasurableSet.const _
  | succ j ih =>
    have e : {π : Frog → ℕ → Step 3 | wIter m k π (j + 1) φ} =
        {π | wIter m k π j φ} ∪ ⋃ ψ : Frog, ⋃ v : Vertex 3, ⋃ n : ℕ,
          ({_π : Frog → ℕ → Step 3 | φ = Sum.inr v ∧ v.length ≤ m} ∩
            {π | wIter m k π j ψ} ∩ {π | pos π ψ n = some v}) := by
      ext π
      simp only [wIter, Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro (h | ⟨ψ, v, n, h1, h2, h3, h4⟩)
        · exact Or.inl h
        · exact Or.inr ⟨ψ, v, n, ⟨⟨h1, h2⟩, h3⟩, h4⟩
      · rintro (h | ⟨ψ, v, n, ⟨⟨h1, h2⟩, h3⟩, h4⟩)
        · exact Or.inl h
        · exact Or.inr ⟨ψ, v, n, h1, h2, h3, h4⟩
    rw [e]
    exact (ih φ).union (MeasurableSet.iUnion fun ψ => MeasurableSet.iUnion fun v =>
      MeasurableSet.iUnion fun n => ((MeasurableSet.const _).inter (ih ψ)).inter
        (measurable_pos ψ n (some v)))

theorem measurable_woken (m k : ℕ) (φ : Frog) :
    MeasurableSet {π : Frog → ℕ → Step 3 | Woken m k π φ} := by
  have e : {π : Frog → ℕ → Step 3 | Woken m k π φ} = ⋃ j, {π | wIter m k π j φ} := by
    ext π
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, woken_iff_iter]
  rw [e]
  exact MeasurableSet.iUnion fun j => measurable_wIter m k j φ

/-- The planted count is measurable in the paths. -/
theorem measurable_plantedG (m k : ℕ) :
    Measurable fun π : Frog → ℕ → Step 3 => plantedG m k π := by
  have e : (fun π : Frog → ℕ → Step 3 => plantedG m k π) = fun π => ∑ φ ∈ frogsF m k,
      ({π' | Woken m k π' φ ∧ ∃ n, pos π' φ n = none} : Set (Frog → ℕ → Step 3)).indicator
        (fun _ => (1 : ℕ∞)) π := funext (plantedG_eq_sum m k)
  rw [e]
  refine Finset.measurable_sum _ fun φ _ => measurable_const.indicator ?_
  have e2 : {π' : Frog → ℕ → Step 3 | Woken m k π' φ ∧ ∃ n, pos π' φ n = none} =
      {π' | Woken m k π' φ} ∩ ⋃ n, {π' | pos π' φ n = none} := by
    ext π
    simp
  rw [e2]
  exact (measurable_woken m k φ).inter (MeasurableSet.iUnion fun n => measurable_pos φ n none)

end FrogModel.D3
