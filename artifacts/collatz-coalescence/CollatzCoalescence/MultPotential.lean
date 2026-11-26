import CollatzCoalescence.MultChain
import CollatzCoalescence.Generic

/-!
# Saturation for the multiplier `5`

For `x ↦ x / 2, (5 x + 1) / 2` the neighbour pair chain is *not* absorbed almost surely: the bounded
function `phi5 = min 1 ((1 + (2/3)^d) * (8 / w)^(1/4))` (with `w = |μ| / 5^d`) is superharmonic at
every state and equals `1` at the absorbing state, so it dominates the absorption probability.  It is
`< 1` at the state `(0, 310)`, which is reached from `(0, 1)` by thirteen `true` coins.

The fourth root is written with `Real.rpow`, exactly as `x ^ (1 / 4 : ℝ)`.
-/

namespace Coalescence.Mult
open Generic

/-- The potential for the multiplier 5: `min 1 ((1 + (2/3)^d) * (8 / w)^(1/4))`, and `1` when `μ = 0`. -/
noncomputable def phi5 (s : State) : ℝ :=
  if s.mu = 0 then 1 else min 1 ((1 + (2 / 3 : ℝ) ^ s.d) * (8 / wA 5 s) ^ (1 / 4 : ℝ))

theorem phi5_nonneg (s : State) : 0 ≤ phi5 s := by
  unfold phi5
  split_ifs
  · exact zero_le_one
  · have h1 : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ s.d := by positivity
    have h2 : (0 : ℝ) ≤ (8 / wA 5 s) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by unfold wA; positivity) _
    exact le_min zero_le_one (mul_nonneg (by linarith) h2)

theorem phi5_le_one (s : State) : phi5 s ≤ 1 := by
  unfold phi5
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem phi5_absorbed : phi5 absorbed = 1 := by
  simp [phi5, absorbed]

/-! ## Fourth roots -/

/-- `(y^4)^(1/4) = y` for `y ≥ 0`. -/
theorem pow_four_rpow_quarter {y : ℝ} (hy : 0 ≤ y) : (y ^ 4) ^ (1 / 4 : ℝ) = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

/-- Rational certificate for a fourth root: `x ≤ y^4` gives `x^(1/4) ≤ y`. -/
theorem rpow_quarter_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ y ^ 4) :
    x ^ (1 / 4 : ℝ) ≤ y := by
  have h1 : x ^ (1 / 4 : ℝ) ≤ (y ^ 4) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hx h (by norm_num)
  rwa [pow_four_rpow_quarter hy] at h1

/-- If `w' ≥ ρ w` and `1/ρ ≤ y^4`, the fourth root of `8 / w'` is at most `y` times that of `8 / w`. -/
theorem quarter_child {w w' ρ y : ℝ} (hw : 0 < w) (hρ : 0 < ρ) (hy : 0 ≤ y)
    (hρy : 1 ≤ ρ * y ^ 4) (h : ρ * w ≤ w') :
    (8 / w') ^ (1 / 4 : ℝ) ≤ y * (8 / w) ^ (1 / 4 : ℝ) := by
  have hw' : 0 < w' := lt_of_lt_of_le (mul_pos hρ hw) h
  have hy4 : (0 : ℝ) ≤ y ^ 4 := by positivity
  have h1 : 8 / w' ≤ y ^ 4 * (8 / w) := by
    have e : y ^ 4 * (8 / w) = 8 * y ^ 4 / w := by ring
    rw [e, div_le_div_iff₀ hw' hw]
    have h2 : w ≤ y ^ 4 * w' := by
      calc w = 1 * w := (one_mul w).symm
        _ ≤ ρ * y ^ 4 * w := mul_le_mul_of_nonneg_right hρy hw.le
        _ = y ^ 4 * (ρ * w) := by ring
        _ ≤ y ^ 4 * w' := mul_le_mul_of_nonneg_left h hy4
    linarith
  calc (8 / w') ^ (1 / 4 : ℝ) ≤ (y ^ 4 * (8 / w)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    _ = (y ^ 4) ^ (1 / 4 : ℝ) * (8 / w) ^ (1 / 4 : ℝ) := Real.mul_rpow hy4 (by positivity)
    _ = y * (8 / w) ^ (1 / 4 : ℝ) := by rw [pow_four_rpow_quarter hy]

/-- The bound for `phi5` at a child whose weight is at least `ρ w`. -/
theorem phi5_child_le {t : State} {w ρ y : ℝ} (hw : 0 < w) (hρ : 0 < ρ) (hy : 0 ≤ y)
    (hρy : 1 ≤ ρ * y ^ 4) (h : ρ * w ≤ wA 5 t) :
    phi5 t ≤ (1 + (2 / 3 : ℝ) ^ t.d) * (y * (8 / w) ^ (1 / 4 : ℝ)) := by
  have hwt : 0 < wA 5 t := lt_of_lt_of_le (mul_pos hρ hw) h
  have hmu : t.mu ≠ 0 := by
    intro h0
    simp [wA, h0] at hwt
  have hc : (0 : ℝ) ≤ 1 + (2 / 3 : ℝ) ^ t.d := by positivity
  unfold phi5
  rw [if_neg hmu]
  exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (quarter_child hw hρ hy hρy h) hc)

/-! ## Superharmonicity -/

/-- `phi5` is superharmonic at every state, given the level and weight bounds for the children. -/
theorem phi5_super_of
    (hde : ∀ s : State, s.mu % 2 = 0 → ∀ c : Bool, (stepA 5 s c).d = s.d)
    (hdof : ∀ s : State, s.mu % 2 = 1 → (stepA 5 s false).d = s.d + 1)
    (hdot : ∀ s : State, s.mu % 2 = 1 → 0 < s.d → (stepA 5 s true).d = s.d - 1)
    (hdot0 : ∀ s : State, s.mu % 2 = 1 → s.d = 0 → (stepA 5 s true).d = 1)
    (hwf : ∀ s : State, wA 5 s / 2 - 1 / (2 * ((5 : ℕ) : ℝ)) ≤ wA 5 (stepA 5 s false))
    (hwt : ∀ s : State, ¬ (s.d = 0 ∧ s.mu % 2 = 1) →
      (((5 : ℕ) : ℝ) * wA 5 s - 1) / 2 ≤ wA 5 (stepA 5 s true))
    (hwt0 : ∀ m : ℤ, m % 2 = 1 →
      wA 5 ⟨0, m⟩ / 2 - 1 / (2 * ((5 : ℕ) : ℝ)) ≤ wA 5 (stepA 5 ⟨0, m⟩ true))
    (s : State) : (phi5 (stepA 5 s false) + phi5 (stepA 5 s true)) / 2 ≤ phi5 s := by
  have h0 := phi5_le_one (stepA 5 s false)
  have h1 := phi5_le_one (stepA 5 s true)
  by_cases hmu : s.mu = 0
  · have hs : phi5 s = 1 := by simp [phi5, hmu]
    linarith
  by_cases hψ : 1 ≤ (1 + (2 / 3 : ℝ) ^ s.d) * (8 / wA 5 s) ^ (1 / 4 : ℝ)
  · have hs : phi5 s = 1 := by
      unfold phi5
      rw [if_neg hmu, min_eq_left hψ]
    linarith
  replace hψ := not_le.mp hψ
  have hphi : phi5 s = (1 + (2 / 3 : ℝ) ^ s.d) * (8 / wA 5 s) ^ (1 / 4 : ℝ) := by
    unfold phi5
    rw [if_neg hmu, min_eq_right hψ.le]
  have hwpos : 0 < wA 5 s := by
    unfold wA
    have : (0 : ℝ) < |(s.mu : ℝ)| := abs_pos.mpr (by exact_mod_cast hmu)
    positivity
  have hQ0 : (0 : ℝ) ≤ (8 / wA 5 s) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hr0 : (0 : ℝ) < (2 / 3 : ℝ) ^ s.d := by positivity
  have hw8 : 8 < wA 5 s := by
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have h8 : 1 ≤ 8 / wA 5 s := by
      rw [le_div_iff₀ hwpos]; linarith
    have hQ1 : 1 ≤ (8 / wA 5 s) ^ (1 / 4 : ℝ) := Real.one_le_rpow h8 (by norm_num)
    nlinarith
  have hf := hwf s
  have hcast : ((5 : ℕ) : ℝ) = 5 := by norm_num
  rw [hcast] at hf
  have hf' : 39 / 80 * wA 5 s ≤ wA 5 (stepA 5 s false) := by linarith
  have hA0 : (0 : ℝ) ≤ 1.0064 * 1.1893 := by norm_num
  have hB0 : (0 : ℝ) ≤ 1.0064 * 0.7953 := by norm_num
  have hA4 : (1 : ℝ) ≤ 39 / 80 * (1.0064 * 1.1893) ^ 4 := by norm_num
  have hB4 : (1 : ℝ) ≤ 39 / 16 * (1.0064 * 0.7953) ^ 4 := by norm_num
  have b0 := phi5_child_le hwpos (by norm_num) hA0 hA4 hf'
  rw [hphi]
  generalize hQ : (8 / wA 5 s) ^ (1 / 4 : ℝ) = Q at *
  rcases Int.emod_two_eq_zero_or_one s.mu with hpar | hpar
  · -- `μ` even: both children at level `d`
    have ht := hwt s (by omega)
    rw [hcast] at ht
    have ht' : 39 / 16 * wA 5 s ≤ wA 5 (stepA 5 s true) := by linarith
    have b1 := phi5_child_le hwpos (by norm_num) hB0 hB4 ht'
    rw [hQ] at b1
    rw [hde s hpar] at b0 b1
    generalize (2 / 3 : ℝ) ^ s.d = x at *
    have key : (1 + x) * (1.0064 * 1.1893) + (1 + x) * (1.0064 * 0.7953) ≤ 2 * (1 + x) := by
      nlinarith
    have := mul_le_mul_of_nonneg_right key hQ0
    linarith
  · obtain ⟨d, m⟩ := s
    simp only at hpar hmu hwpos hw8 hf' b0 hr0 ⊢
    cases d with
    | zero =>
      -- `μ` odd, level `0`: both children at level `1`
      have ht := hwt0 m hpar
      rw [hcast] at ht
      have ht' : 39 / 80 * wA 5 ⟨0, m⟩ ≤ wA 5 (stepA 5 ⟨0, m⟩ true) := by linarith
      have b1 := phi5_child_le hwpos (by norm_num) hA0 hA4 ht'
      rw [hQ] at b1
      rw [hdof ⟨0, m⟩ hpar] at b0
      rw [hdot0 ⟨0, m⟩ hpar rfl] at b1
      norm_num at b0 b1 ⊢
      nlinarith
    | succ d' =>
      -- `μ` odd, level `d' + 1`: children at levels `d' + 2` and `d'`
      have ht := hwt ⟨d' + 1, m⟩ (by simp)
      rw [hcast] at ht
      have ht' : 39 / 16 * wA 5 ⟨d' + 1, m⟩ ≤ wA 5 (stepA 5 ⟨d' + 1, m⟩ true) := by linarith
      have b1 := phi5_child_le hwpos (by norm_num) hB0 hB4 ht'
      rw [hQ] at b1
      rw [hdof ⟨d' + 1, m⟩ hpar] at b0
      rw [hdot ⟨d' + 1, m⟩ hpar (Nat.succ_pos d')] at b1
      simp only [Nat.add_sub_cancel] at b1
      have hx0 : (0 : ℝ) < (2 / 3 : ℝ) ^ d' := by positivity
      have e1 : (2 / 3 : ℝ) ^ (d' + 1) = 2 / 3 * (2 / 3 : ℝ) ^ d' := by ring
      have e2 : (2 / 3 : ℝ) ^ (d' + 1 + 1) = 4 / 9 * (2 / 3 : ℝ) ^ d' := by ring
      rw [e2] at b0
      rw [e1]
      generalize (2 / 3 : ℝ) ^ d' = x at *
      have key : (1 + 4 / 9 * x) * (1.0064 * 1.1893) + (1 + x) * (1.0064 * 0.7953)
          ≤ 2 * (1 + 2 / 3 * x) := by
        nlinarith
      have := mul_le_mul_of_nonneg_right key hQ0
      linarith

/-! ## The generic comparison -/

/-- Generic: a globally superharmonic function that is `≥ 1` at the absorbing state bounds the
absorption probability. -/
theorem pAbs_le_of_super {S : Type*} [DecidableEq S] (step : S → Bool → S) (abs : S) (φ : S → ℝ)
    (h0 : ∀ s, 0 ≤ φ s) (habs : 1 ≤ φ abs)
    (hsuper : ∀ s, (φ (step s false) + φ (step s true)) / 2 ≤ φ s) (k : ℕ) (s : S) :
    pAbs step abs k s ≤ φ s := by
  induction k generalizing s with
  | zero =>
    rw [pAbs_zero]
    split_ifs with h
    · subst h; exact habs
    · exact h0 s
  | succ k ih =>
    have i0 := ih (step s false)
    have i1 := ih (step s true)
    have hs := hsuper s
    rw [pAbs_succ]
    linarith

/-- Following a fixed coin word `w` has probability `2^(-|w|)`; every other word contributes at
most `1`. -/
theorem pAbs_word_le {S : Type*} [DecidableEq S] (step : S → Bool → S) (abs : S) (j : ℕ) :
    ∀ (w : List Bool) (s : S),
      pAbs step abs (w.length + j) s
        ≤ 1 - (1 / 2 : ℝ) ^ w.length * (1 - pAbs step abs j (List.foldl step s w))
  | [], s => by simp
  | b :: w, s => by
    have hrec := pAbs_word_le step abs j w (step s b)
    have h0 := pAbs_le_one step abs (w.length + j) (step s false)
    have h1 := pAbs_le_one step abs (w.length + j) (step s true)
    have hlen : (b :: w).length + j = (w.length + j) + 1 := by simp; omega
    rw [hlen, pAbs_succ, List.length_cons, pow_succ, List.foldl_cons]
    cases b <;> linarith

/-! ## Saturation -/

theorem runA_five_thirteen : runA 5 ⟨0, 1⟩ (List.replicate 13 true) = ⟨0, 310⟩ := by decide

theorem phi5_310_le : phi5 ⟨0, 310⟩ ≤ 0.81 := by
  have hw : wA 5 ⟨0, 310⟩ = 310 := by simp [wA]
  have hq : ((8 : ℝ) / 310) ^ (1 / 4 : ℝ) ≤ 0.401 :=
    rpow_quarter_le (by norm_num) (by norm_num) (by norm_num)
  have hmu : (⟨0, 310⟩ : State).mu ≠ 0 := by decide
  unfold phi5
  rw [if_neg hmu, hw]
  refine (min_le_right _ _).trans ?_
  norm_num
  linarith

/-- Saturation, given that `phi5` is superharmonic. -/
theorem saturation_five_of
    (hsuper : ∀ s : State, (phi5 (stepA 5 s false) + phi5 (stepA 5 s true)) / 2 ≤ phi5 s) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, pAbs (stepA 5) absorbed k ⟨0, 1⟩ ≤ 1 - ε := by
  refine ⟨0.19 / 8192, by norm_num, fun k => ?_⟩
  have hmono := pAbs_mono (stepA 5) absorbed (stepA_absorbed 5)
    (show k ≤ (List.replicate 13 true).length + k by omega) ⟨0, 1⟩
  have hword := pAbs_word_le (stepA 5) absorbed k (List.replicate 13 true) ⟨0, 1⟩
  have hrun : List.foldl (stepA 5) ⟨0, 1⟩ (List.replicate 13 true) = ⟨0, 310⟩ :=
    runA_five_thirteen
  rw [hrun] at hword
  have hphi := pAbs_le_of_super (stepA 5) absorbed phi5 phi5_nonneg phi5_absorbed.ge hsuper k
    ⟨0, 310⟩
  have h310 := phi5_310_le
  have hlen : (List.replicate 13 true).length = 13 := by simp
  rw [hlen] at hword hmono
  norm_num at hword ⊢
  linarith

/-! ## Headlines -/

/-- `phi5` is superharmonic at EVERY state. -/
theorem phi5_super (s : State) : (phi5 (stepA 5 s false) + phi5 (stepA 5 s true)) / 2 ≤ phi5 s :=
  phi5_super_of (fun s h c => stepA_d_even 5 s h c) (fun s h => stepA_d_odd_false 5 s h)
    (fun s h hd => stepA_d_odd_true 5 s h hd) (fun s h hd => stepA_d_odd_true_zero 5 s h hd)
    (fun s => wA_step_false_ge 5 (by norm_num) s)
    (fun s h => wA_step_true_ge_of_odd 5 (by norm_num) (by norm_num) s h)
    (fun m hm => wA_step_true_zero_odd 5 (by norm_num) m hm) s

/-- **Saturation for `5x+1`.** The neighbour pair chain for `x ↦ x/2, (5x+1)/2` is absorbed with
probability bounded away from `1`. -/
theorem saturation_five : ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, pAbs (stepA 5) absorbed k ⟨0, 1⟩ ≤ 1 - ε :=
  saturation_five_of phi5_super

end Coalescence.Mult

#print axioms Coalescence.Mult.phi5_nonneg
#print axioms Coalescence.Mult.phi5_le_one
#print axioms Coalescence.Mult.phi5_absorbed
#print axioms Coalescence.Mult.phi5_super
#print axioms Coalescence.Mult.pAbs_le_of_super
#print axioms Coalescence.Mult.saturation_five
