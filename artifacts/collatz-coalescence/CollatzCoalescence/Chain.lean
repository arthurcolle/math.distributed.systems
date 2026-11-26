import CollatzCoalescence.Defs

/-!
# One step of the pair chain

`step_rel`: applying `T` to both members of a pair in relation `s` gives a pair in relation `step s c`,
up to swapping the roles (Lemma 1 of `main.tex`).  `step_dom`: the domination inequality (Lemma 3).
-/

namespace Coalescence


/-! ### Sanity checks -/

example : step ⟨0, 1⟩ false = ⟨1, 2⟩ := by decide
example : step ⟨1, 2⟩ false = ⟨1, 1⟩ := by decide
example : step ⟨1, 1⟩ true = ⟨0, 0⟩ := by decide
example : step ⟨0, 1⟩ true = ⟨1, -1⟩ := by decide
example : step ⟨1, 2⟩ true = ⟨1, 2⟩ := by decide
example : step ⟨1, 1⟩ false = ⟨2, 2⟩ := by decide

/-! ### Item 1: one step of `T` on both members moves the state by `step` -/

theorem three_pow_emod_two (d : ℕ) : (3 : ℤ) ^ d % 2 = 1 :=
  Int.odd_iff.mp (Odd.pow (by decide))

theorem two_mul_T_of_even {x : ℤ} (hx : x % 2 = 0) : 2 * T x = x := by
  unfold T
  rw [if_pos hx]
  omega

theorem two_mul_T_of_odd {x : ℤ} (hx : x % 2 = 1) : 2 * T x = 3 * x + 1 := by
  have hx' : ¬ x % 2 = 0 := by omega
  unfold T
  rw [if_neg hx']
  omega

theorem rel_norm_or (s : State) (x y : ℤ) (h : y = 3 ^ s.d * x + s.mu) :
    Rel s.norm x y ∨ Rel s.norm y x := by
  unfold State.norm
  split_ifs with hd
  · rw [hd, pow_zero, one_mul] at h
    rcases abs_cases s.mu with ⟨ha, _⟩ | ⟨ha, _⟩
    · left
      show y = 3 ^ 0 * x + |s.mu|
      rw [ha, pow_zero, one_mul]
      exact h
    · right
      show x = 3 ^ 0 * y + |s.mu|
      rw [ha, pow_zero, one_mul]
      omega
  · exact Or.inl h

theorem step_rel (s : State) (p q : ℤ) (h : Rel s p q) :
    Rel (step s (decide (p % 2 = 1))) (T p) (T q) ∨
      Rel (step s (decide (p % 2 = 1))) (T q) (T p) := by
  obtain ⟨d, μ⟩ := s
  change q = 3 ^ d * p + μ at h
  have h3 := three_pow_emod_two d
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (3 : ℤ) ^ d = 2 * t + 1 := ⟨(3 : ℤ) ^ d / 2, by omega⟩
  have hq : q % 2 = (p + μ) % 2 := by
    have e : q = 2 * (t * p) + (p + μ) := by rw [h, ht]; ring
    rw [e]
    omega
  rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ <;>
    rcases Int.emod_two_eq_zero_or_one p with hp | hp
  · -- `μ` even, `p` even: both halve
    have hc : decide (p % 2 = 1) = false := decide_eq_false (by omega)
    have hTp := two_mul_T_of_even hp
    have hTq := two_mul_T_of_even (x := q) (by omega)
    have hν : 2 * (μ / 2) = μ := by omega
    rw [hc, step_even_false d μ hμ]
    apply rel_norm_or
    show T q = 3 ^ d * T p + μ / 2
    have key : 2 * T q = 2 * (3 ^ d * T p + μ / 2) := by
      linear_combination hTq + h - (3 : ℤ) ^ d * hTp - hν
    exact mul_left_cancel₀ two_ne_zero key
  · -- `μ` even, `p` odd: both take the odd branch
    have hc : decide (p % 2 = 1) = true := decide_eq_true hp
    have hTp := two_mul_T_of_odd hp
    have hTq := two_mul_T_of_odd (x := q) (by omega)
    have hν : 2 * ((3 * μ + 1 - 3 ^ d) / 2) = 3 * μ + 1 - 3 ^ d := by omega
    rw [hc, step_even_true d μ hμ]
    apply rel_norm_or
    show T q = 3 ^ d * T p + (3 * μ + 1 - 3 ^ d) / 2
    have key : 2 * T q = 2 * (3 ^ d * T p + (3 * μ + 1 - 3 ^ d) / 2) := by
      linear_combination hTq + 3 * h - (3 : ℤ) ^ d * hTp - hν
    exact mul_left_cancel₀ two_ne_zero key
  · -- `μ` odd, `p` even: `q` takes the odd branch and gains a factor 3
    have hc : decide (p % 2 = 1) = false := decide_eq_false (by omega)
    have hTp := two_mul_T_of_even hp
    have hTq := two_mul_T_of_odd (x := q) (by omega)
    have hν : 2 * ((3 * μ + 1) / 2) = 3 * μ + 1 := by omega
    rw [hc, step_odd_false d μ hμ]
    left
    show T q = 3 ^ (d + 1) * T p + (3 * μ + 1) / 2
    have key : 2 * T q = 2 * (3 ^ (d + 1) * T p + (3 * μ + 1) / 2) := by
      rw [pow_succ]
      linear_combination hTq + 3 * h - 3 * (3 : ℤ) ^ d * hTp - hν
    exact mul_left_cancel₀ two_ne_zero key
  · -- `μ` odd, `p` odd: `p` takes the odd branch
    have hc : decide (p % 2 = 1) = true := decide_eq_true hp
    have hTp := two_mul_T_of_odd hp
    have hTq := two_mul_T_of_even (x := q) (by omega)
    rw [hc]
    cases d with
    | zero =>
      -- roles swap: `T p = 3 * T q + (1 - 3μ)/2`
      rw [pow_zero, one_mul] at h
      have hν : 2 * ((1 - 3 * μ) / 2) = 1 - 3 * μ := by omega
      rw [step_odd_true_zero μ hμ]
      right
      show T p = 3 ^ 1 * T q + (1 - 3 * μ) / 2
      have key : 2 * T p = 2 * (3 ^ 1 * T q + (1 - 3 * μ) / 2) := by
        linear_combination hTp - 3 * hTq - 3 * h - hν
      exact mul_left_cancel₀ two_ne_zero key
    | succ d' =>
      have h3' := three_pow_emod_two d'
      have hν : 2 * ((μ - 3 ^ d') / 2) = μ - 3 ^ d' := by omega
      rw [step_odd_true_succ d' μ hμ]
      apply rel_norm_or
      show T q = 3 ^ d' * T p + (μ - 3 ^ d') / 2
      have key : 2 * T q = 2 * (3 ^ d' * T p + (μ - 3 ^ d') / 2) := by
        rw [pow_succ] at h
        linear_combination hTq + h - (3 : ℤ) ^ d' * hTp - hν
      exact mul_left_cancel₀ two_ne_zero key

/-! ### Items 2 and 3: the diagonal state is absorbing and encodes equality -/

theorem step_absorbed (c : Bool) : step ⟨0, 0⟩ c = ⟨0, 0⟩ := by
  cases c <;> decide

theorem rel_zero_iff (p q : ℤ) : Rel ⟨0, 0⟩ p q ↔ q = p := by
  simp [Rel]

/-! ### Item 4: domination by an affine random recursion -/

/-- Weight `|μ| / 3^d` of a state. -/
def w (s : State) : ℚ := |(s.mu : ℚ)| / 3 ^ s.d

/-- Multiplier of the dominating affine recursion. -/
def a (c : Bool) : ℚ := if c then 3 / 2 else 1 / 2

theorem w_norm (s : State) : w s.norm = w s := by
  unfold State.norm
  split_ifs with hd
  · simp [w, hd]
  · rfl

theorem cast_half {x : ℤ} (hx : x % 2 = 0) : ((x / 2 : ℤ) : ℚ) = (x : ℚ) / 2 := by
  have h : 2 * (x / 2) = x := by omega
  have h' : (2 : ℚ) * ((x / 2 : ℤ) : ℚ) = (x : ℚ) := by exact_mod_cast h
  linarith

theorem step_dom (s : State) (c : Bool) : w (step s c) ≤ a c * w s + 1 / 2 := by
  obtain ⟨d, μ⟩ := s
  have h3 := three_pow_emod_two d
  have hP : (0 : ℚ) < 3 ^ d := by positivity
  have hP1 : (1 : ℚ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have hle := le_abs_self (μ : ℚ)
  have hge := neg_abs_le (μ : ℚ)
  have habs := abs_nonneg (μ : ℚ)
  rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ <;> cases c
  · -- `μ` even, `c = false`
    rw [step_even_false d μ hμ, w_norm]
    show |(((μ / 2 : ℤ)) : ℚ)| / 3 ^ d ≤ (1 / 2 : ℚ) * (|(μ : ℚ)| / 3 ^ d) + 1 / 2
    rw [cast_half hμ, div_le_iff₀ hP]
    have e : ((1 / 2 : ℚ) * (|(μ : ℚ)| / 3 ^ d) + 1 / 2) * 3 ^ d
        = |(μ : ℚ)| / 2 + 3 ^ d / 2 := by
      field_simp
    rw [e]
    have : |(μ : ℚ) / 2| ≤ |(μ : ℚ)| / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · -- `μ` even, `c = true`
    rw [step_even_true d μ hμ, w_norm]
    show |((((3 * μ + 1 - 3 ^ d) / 2 : ℤ)) : ℚ)| / 3 ^ d
        ≤ (3 / 2 : ℚ) * (|(μ : ℚ)| / 3 ^ d) + 1 / 2
    rw [cast_half (by omega), div_le_iff₀ hP]
    have e : ((3 / 2 : ℚ) * (|(μ : ℚ)| / 3 ^ d) + 1 / 2) * 3 ^ d
        = 3 * |(μ : ℚ)| / 2 + 3 ^ d / 2 := by
      field_simp
    rw [e]
    push_cast
    have : |(3 * (μ : ℚ) + 1 - 3 ^ d) / 2| ≤ 3 * |(μ : ℚ)| / 2 + 3 ^ d / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact this
  · -- `μ` odd, `c = false`
    rw [step_odd_false d μ hμ]
    show |((((3 * μ + 1) / 2 : ℤ)) : ℚ)| / 3 ^ (d + 1)
        ≤ (1 / 2 : ℚ) * (|(μ : ℚ)| / 3 ^ d) + 1 / 2
    have hP' : (0 : ℚ) < 3 ^ (d + 1) := by positivity
    rw [cast_half (by omega), div_le_iff₀ hP']
    have e : ((1 / 2 : ℚ) * (|(μ : ℚ)| / 3 ^ d) + 1 / 2) * 3 ^ (d + 1)
        = 3 * |(μ : ℚ)| / 2 + 3 * 3 ^ d / 2 := by
      rw [pow_succ]
      field_simp
    rw [e]
    push_cast
    have : |(3 * (μ : ℚ) + 1) / 2| ≤ 3 * |(μ : ℚ)| / 2 + 3 * 3 ^ d / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact this
  · -- `μ` odd, `c = true`
    cases d with
    | zero =>
      rw [step_odd_true_zero μ hμ]
      show |((((1 - 3 * μ) / 2 : ℤ)) : ℚ)| / 3 ^ 1
          ≤ (3 / 2 : ℚ) * (|(μ : ℚ)| / 3 ^ 0) + 1 / 2
      rw [cast_half (by omega), pow_one, pow_zero, div_one, div_le_iff₀ (by norm_num)]
      push_cast
      have : |(1 - 3 * (μ : ℚ)) / 2| ≤ ((3 / 2 : ℚ) * |(μ : ℚ)| + 1 / 2) * 3 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      exact this
    | succ d' =>
      have h3' := three_pow_emod_two d'
      have hP' : (0 : ℚ) < 3 ^ d' := by positivity
      rw [step_odd_true_succ d' μ hμ, w_norm]
      show |((((μ - 3 ^ d') / 2 : ℤ)) : ℚ)| / 3 ^ d'
          ≤ (3 / 2 : ℚ) * (|(μ : ℚ)| / 3 ^ (d' + 1)) + 1 / 2
      rw [cast_half (by omega), div_le_iff₀ hP']
      have e : ((3 / 2 : ℚ) * (|(μ : ℚ)| / 3 ^ (d' + 1)) + 1 / 2) * 3 ^ d'
          = |(μ : ℚ)| / 2 + 3 ^ d' / 2 := by
        rw [pow_succ]
        field_simp
      rw [e]
      push_cast
      have : |((μ : ℚ) - 3 ^ d') / 2| ≤ |(μ : ℚ)| / 2 + 3 ^ d' / 2 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      exact this

/-- At `d = 0` with odd offset the next weight is at most `w/2 + 1/6`, whatever the coin.
(The hypothesis `0 ≤ m` is not needed.) -/
theorem step_dom_zero_odd' (m : ℤ) (hm : m % 2 = 1) (c : Bool) :
    w (step ⟨0, m⟩ c) ≤ w ⟨0, m⟩ / 2 + 1 / 6 := by
  have hle := le_abs_self (m : ℚ)
  have hge := neg_abs_le (m : ℚ)
  cases c
  · rw [step_odd_false 0 m hm]
    show |((((3 * m + 1) / 2 : ℤ)) : ℚ)| / 3 ^ (0 + 1) ≤ |(m : ℚ)| / 3 ^ 0 / 2 + 1 / 6
    rw [cast_half (by omega), zero_add, pow_one, pow_zero, div_one, div_le_iff₀ (by norm_num)]
    push_cast
    have : |(3 * (m : ℚ) + 1) / 2| ≤ (|(m : ℚ)| / 2 + 1 / 6) * 3 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact this
  · rw [step_odd_true_zero m hm]
    show |((((1 - 3 * m) / 2 : ℤ)) : ℚ)| / 3 ^ 1 ≤ |(m : ℚ)| / 3 ^ 0 / 2 + 1 / 6
    rw [cast_half (by omega), pow_one, pow_zero, div_one, div_le_iff₀ (by norm_num)]
    push_cast
    have : |(1 - 3 * (m : ℚ)) / 2| ≤ (|(m : ℚ)| / 2 + 1 / 6) * 3 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact this

theorem step_dom_zero_odd (m : ℤ) (hm : m % 2 = 1) (_hm0 : 0 ≤ m) (c : Bool) :
    w (step ⟨0, m⟩ c) ≤ w ⟨0, m⟩ / 2 + 1 / 6 :=
  step_dom_zero_odd' m hm c

end Coalescence

#print axioms Coalescence.step_rel
#print axioms Coalescence.step_absorbed
#print axioms Coalescence.rel_zero_iff
#print axioms Coalescence.step_dom
#print axioms Coalescence.step_dom_zero_odd
