import CollatzCoalescence.MultDefs

/-!
# One step of the pair chain for a general odd multiplier

`stepA_rel`: applying `Ta a` to both members of a pair in relation `s` gives a pair in relation
`stepA a s c`, up to swapping the roles.  `stepA_d_*`: the levels of the children.  `wA_step_*`: lower
bounds on the sizes `|μ| / a^d` of the children.

All helper lemmas are `private`, so that this file cannot clash with its siblings.
-/

namespace Coalescence.Mult

/-! ### Parity -/

private theorem pow_emod_two' (a : ℕ) (ha : a % 2 = 1) (d : ℕ) : (a : ℤ) ^ d % 2 = 1 := by
  have h : Odd (a : ℤ) := Int.odd_iff.mpr (by omega)
  exact Int.odd_iff.mp h.pow

private theorem mul_emod_two_of_odd {a : ℤ} (ha : a % 2 = 1) (x : ℤ) : a * x % 2 = x % 2 := by
  rw [Int.mul_emod, ha, one_mul]
  omega

private theorem two_mul_Ta_of_even (a : ℤ) {x : ℤ} (hx : x % 2 = 0) : 2 * Ta a x = x := by
  unfold Ta
  rw [if_pos hx]
  omega

private theorem two_mul_Ta_of_odd {a : ℤ} (ha : a % 2 = 1) {x : ℤ} (hx : x % 2 = 1) :
    2 * Ta a x = a * x + 1 := by
  have hx' : ¬ x % 2 = 0 := by omega
  have h := mul_emod_two_of_odd ha x
  unfold Ta
  rw [if_neg hx']
  generalize a * x = y at h ⊢
  omega

private theorem relA_norm_or (a : ℕ) (s : State) (x y : ℤ) (h : y = (a : ℤ) ^ s.d * x + s.mu) :
    RelA a s.norm x y ∨ RelA a s.norm y x := by
  unfold State.norm
  split_ifs with hd
  · rw [hd, pow_zero, one_mul] at h
    rcases abs_cases s.mu with ⟨ha, _⟩ | ⟨ha, _⟩
    · left
      show y = (a : ℤ) ^ 0 * x + |s.mu|
      rw [ha, pow_zero, one_mul]
      exact h
    · right
      show x = (a : ℤ) ^ 0 * y + |s.mu|
      rw [ha, pow_zero, one_mul]
      omega
  · exact Or.inl h

/-! ### One step of `Ta a` on both members moves the state by `stepA a` -/

/-- One step of `Ta a` on both members of a pair moves the state by `stepA a`, up to swapping roles. -/
theorem stepA_rel (a : ℕ) (ha : a % 2 = 1) (s : State) (p q : ℤ) (h : RelA a s p q) :
    RelA a (stepA a s (decide (p % 2 = 1))) (Ta a p) (Ta a q) ∨
      RelA a (stepA a s (decide (p % 2 = 1))) (Ta a q) (Ta a p) := by
  obtain ⟨d, μ⟩ := s
  change q = (a : ℤ) ^ d * p + μ at h
  have haZ : (a : ℤ) % 2 = 1 := by omega
  have h3 := pow_emod_two' a ha d
  have hamu := mul_emod_two_of_odd haZ μ
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (a : ℤ) ^ d = 2 * t + 1 := ⟨(a : ℤ) ^ d / 2, by omega⟩
  have hq : q % 2 = (p + μ) % 2 := by
    have e : q = 2 * (t * p) + (p + μ) := by rw [h, ht]; ring
    rw [e]
    omega
  rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ <;>
    rcases Int.emod_two_eq_zero_or_one p with hp | hp
  · -- `μ` even, `p` even: both halve
    have hc : decide (p % 2 = 1) = false := decide_eq_false (by omega)
    have hTp := two_mul_Ta_of_even (a : ℤ) hp
    have hTq := two_mul_Ta_of_even (a : ℤ) (x := q) (by omega)
    have hν : 2 * (μ / 2) = μ := by omega
    rw [hc, stepA_even_false a d μ hμ]
    apply relA_norm_or
    show Ta a q = (a : ℤ) ^ d * Ta a p + μ / 2
    have key : 2 * Ta a q = 2 * ((a : ℤ) ^ d * Ta a p + μ / 2) := by
      linear_combination hTq + h - (a : ℤ) ^ d * hTp - hν
    exact mul_left_cancel₀ two_ne_zero key
  · -- `μ` even, `p` odd: both take the odd branch
    have hc : decide (p % 2 = 1) = true := decide_eq_true hp
    have hTp := two_mul_Ta_of_odd haZ hp
    have hTq := two_mul_Ta_of_odd haZ (x := q) (by omega)
    have hν : 2 * (((a : ℤ) * μ + 1 - (a : ℤ) ^ d) / 2) = (a : ℤ) * μ + 1 - (a : ℤ) ^ d := by
      generalize (a : ℤ) * μ = y at hamu ⊢
      generalize (a : ℤ) ^ d = P at h3 ⊢
      omega
    rw [hc, stepA_even_true a d μ hμ]
    apply relA_norm_or
    show Ta a q = (a : ℤ) ^ d * Ta a p + ((a : ℤ) * μ + 1 - (a : ℤ) ^ d) / 2
    have key : 2 * Ta a q
        = 2 * ((a : ℤ) ^ d * Ta a p + ((a : ℤ) * μ + 1 - (a : ℤ) ^ d) / 2) := by
      linear_combination hTq + (a : ℤ) * h - (a : ℤ) ^ d * hTp - hν
    exact mul_left_cancel₀ two_ne_zero key
  · -- `μ` odd, `p` even: `q` takes the odd branch and gains a factor `a`
    have hc : decide (p % 2 = 1) = false := decide_eq_false (by omega)
    have hTp := two_mul_Ta_of_even (a : ℤ) hp
    have hTq := two_mul_Ta_of_odd haZ (x := q) (by omega)
    have hν : 2 * (((a : ℤ) * μ + 1) / 2) = (a : ℤ) * μ + 1 := by
      generalize (a : ℤ) * μ = y at hamu ⊢
      omega
    rw [hc, stepA_odd_false a d μ hμ]
    left
    show Ta a q = (a : ℤ) ^ (d + 1) * Ta a p + ((a : ℤ) * μ + 1) / 2
    have key : 2 * Ta a q = 2 * ((a : ℤ) ^ (d + 1) * Ta a p + ((a : ℤ) * μ + 1) / 2) := by
      rw [pow_succ]
      linear_combination hTq + (a : ℤ) * h - (a : ℤ) * (a : ℤ) ^ d * hTp - hν
    exact mul_left_cancel₀ two_ne_zero key
  · -- `μ` odd, `p` odd: `p` takes the odd branch
    have hc : decide (p % 2 = 1) = true := decide_eq_true hp
    have hTp := two_mul_Ta_of_odd haZ hp
    have hTq := two_mul_Ta_of_even (a : ℤ) (x := q) (by omega)
    rw [hc]
    cases d with
    | zero =>
      -- roles swap: `Ta p = a * Ta q + (1 - a μ)/2`
      rw [pow_zero, one_mul] at h
      have hν : 2 * ((1 - (a : ℤ) * μ) / 2) = 1 - (a : ℤ) * μ := by
        generalize (a : ℤ) * μ = y at hamu ⊢
        omega
      rw [stepA_odd_true_zero a μ hμ]
      right
      show Ta a p = (a : ℤ) ^ 1 * Ta a q + (1 - (a : ℤ) * μ) / 2
      have key : 2 * Ta a p = 2 * ((a : ℤ) ^ 1 * Ta a q + (1 - (a : ℤ) * μ) / 2) := by
        linear_combination hTp - (a : ℤ) * hTq - (a : ℤ) * h - hν
      exact mul_left_cancel₀ two_ne_zero key
    | succ d' =>
      have h3' := pow_emod_two' a ha d'
      have hν : 2 * ((μ - (a : ℤ) ^ d') / 2) = μ - (a : ℤ) ^ d' := by
        generalize (a : ℤ) ^ d' = P at h3' ⊢
        omega
      rw [stepA_odd_true_succ a d' μ hμ]
      apply relA_norm_or
      show Ta a q = (a : ℤ) ^ d' * Ta a p + (μ - (a : ℤ) ^ d') / 2
      have key : 2 * Ta a q = 2 * ((a : ℤ) ^ d' * Ta a p + (μ - (a : ℤ) ^ d') / 2) := by
        rw [pow_succ] at h
        linear_combination hTq + h - (a : ℤ) ^ d' * hTp - hν
      exact mul_left_cancel₀ two_ne_zero key

/-! ### Levels of the children -/

private theorem norm_d_eq (s : State) : s.norm.d = s.d := by
  unfold State.norm
  split_ifs with hd
  · exact hd.symm
  · rfl

theorem stepA_d_even (a : ℕ) (s : State) (h : s.mu % 2 = 0) (c : Bool) :
    (stepA a s c).d = s.d := by
  obtain ⟨d, μ⟩ := s
  have hμ : μ % 2 = 0 := h
  cases c
  · rw [stepA_even_false a d μ hμ, norm_d_eq]
  · rw [stepA_even_true a d μ hμ, norm_d_eq]

theorem stepA_d_odd_false (a : ℕ) (s : State) (h : s.mu % 2 = 1) :
    (stepA a s false).d = s.d + 1 := by
  obtain ⟨d, μ⟩ := s
  have hμ : μ % 2 = 1 := h
  rw [stepA_odd_false a d μ hμ]

theorem stepA_d_odd_true (a : ℕ) (s : State) (h : s.mu % 2 = 1) (hd : 0 < s.d) :
    (stepA a s true).d = s.d - 1 := by
  obtain ⟨d, μ⟩ := s
  have hμ : μ % 2 = 1 := h
  have hd' : 0 < d := hd
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [stepA_odd_true_succ a d' μ hμ, norm_d_eq]
  rfl

theorem stepA_d_odd_true_zero (a : ℕ) (s : State) (h : s.mu % 2 = 1) (hd : s.d = 0) :
    (stepA a s true).d = 1 := by
  obtain ⟨d, μ⟩ := s
  have hμ : μ % 2 = 1 := h
  have hd' : d = 0 := hd
  subst hd'
  rw [stepA_odd_true_zero a μ hμ]

/-! ### Sizes of the children -/

private theorem wA_norm (a : ℕ) (s : State) : wA a s.norm = wA a s := by
  unfold State.norm
  split_ifs with hd
  · simp [wA, hd]
  · rfl

private theorem cast_half_real {x : ℤ} (hx : x % 2 = 0) : ((x / 2 : ℤ) : ℝ) = (x : ℝ) / 2 := by
  have h : 2 * (x / 2) = x := by omega
  have h' : (2 : ℝ) * ((x / 2 : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast h
  linarith

/-- `|⌊x/2⌋| ≥ (|x| - 1)/2`. -/
private theorem abs_half_ge (x : ℤ) : (|(x : ℝ)| - 1) / 2 ≤ |((x / 2 : ℤ) : ℝ)| := by
  have h : |x| - 1 ≤ 2 * |x / 2| := by
    rcases abs_cases x with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases abs_cases (x / 2) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> omega
  have h' : |(x : ℝ)| - 1 ≤ 2 * |((x / 2 : ℤ) : ℝ)| := by exact_mod_cast h
  linarith

/-- `|⌊(y+1)/2⌋| ≥ (|y| - 1)/2`. -/
private theorem abs_succ_half_ge (y : ℤ) :
    (|(y : ℝ)| - 1) / 2 ≤ |(((y + 1) / 2 : ℤ) : ℝ)| := by
  have h : |y| - 1 ≤ 2 * |(y + 1) / 2| := by
    rcases abs_cases y with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases abs_cases ((y + 1) / 2) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> omega
  have h' : |(y : ℝ)| - 1 ≤ 2 * |(((y + 1) / 2 : ℤ) : ℝ)| := by exact_mod_cast h
  linarith

/-- `|⌊(1-y)/2⌋| ≥ (|y| - 1)/2`. -/
private theorem abs_one_sub_half_ge (y : ℤ) :
    (|(y : ℝ)| - 1) / 2 ≤ |(((1 - y) / 2 : ℤ) : ℝ)| := by
  have h : |y| - 1 ≤ 2 * |(1 - y) / 2| := by
    rcases abs_cases y with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases abs_cases ((1 - y) / 2) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> omega
  have h' : |(y : ℝ)| - 1 ≤ 2 * |(((1 - y) / 2 : ℤ) : ℝ)| := by exact_mod_cast h
  linarith

private theorem abs_cast_natCast_mul (a : ℕ) (μ : ℤ) :
    |(((a : ℤ) * μ : ℤ) : ℝ)| = (a : ℝ) * |(μ : ℝ)| := by
  push_cast
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg a)]

private theorem real_false_bound {A P m F : ℝ} (hA : 1 ≤ A) (hP : 1 ≤ P)
    (hF : (A * m - 1) / 2 ≤ F) : m / P / 2 - 1 / (2 * A) ≤ F / (P * A) := by
  have hA0 : 0 < A := by linarith
  have hP0 : 0 < P := by linarith
  rw [le_div_iff₀ (mul_pos hP0 hA0)]
  have e : (m / P / 2 - 1 / (2 * A)) * (P * A) = A * m / 2 - P / 2 := by
    field_simp
  rw [e]
  linarith

private theorem real_true_bound {A P m F : ℝ} (hP : 0 < P) (hF : (A * m - P) / 2 ≤ F) :
    (A * (m / P) - 1) / 2 ≤ F / P := by
  rw [le_div_iff₀ hP]
  have e : (A * (m / P) - 1) / 2 * P = (A * m - P) / 2 := by
    field_simp
  rw [e]
  exact hF

private theorem real_true_bound_succ {A P m F : ℝ} (hA : 0 < A) (hP : 0 < P)
    (hF : (m - P) / 2 ≤ F) : (A * (m / (P * A)) - 1) / 2 ≤ F / P := by
  rw [le_div_iff₀ hP]
  have e : (A * (m / (P * A)) - 1) / 2 * P = (m - P) / 2 := by
    field_simp
  rw [e]
  exact hF

/-- Coin `false`: the size at least halves, up to `1/(2a)`. -/
theorem wA_step_false_ge (a : ℕ) (ha : 1 ≤ a) (s : State) :
    wA a s / 2 - 1 / (2 * (a : ℝ)) ≤ wA a (stepA a s false) := by
  obtain ⟨d, μ⟩ := s
  have hA1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hP1 : (1 : ℝ) ≤ (a : ℝ) ^ d := one_le_pow₀ hA1
  rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
  · rw [stepA_even_false a d μ hμ, wA_norm]
    show |(μ : ℝ)| / (a : ℝ) ^ d / 2 - 1 / (2 * (a : ℝ)) ≤ |((μ / 2 : ℤ) : ℝ)| / (a : ℝ) ^ d
    rw [cast_half_real hμ, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h0 : (0 : ℝ) ≤ 1 / (2 * (a : ℝ)) := by positivity
    have e : |(μ : ℝ)| / 2 / (a : ℝ) ^ d = |(μ : ℝ)| / (a : ℝ) ^ d / 2 := by ring
    rw [e]
    linarith
  · rw [stepA_odd_false a d μ hμ]
    show |(μ : ℝ)| / (a : ℝ) ^ d / 2 - 1 / (2 * (a : ℝ))
        ≤ |((((a : ℤ) * μ + 1) / 2 : ℤ) : ℝ)| / (a : ℝ) ^ (d + 1)
    have hF := abs_succ_half_ge ((a : ℤ) * μ)
    rw [abs_cast_natCast_mul] at hF
    rw [pow_succ]
    exact real_false_bound hA1 hP1 hF

/-- Coin `true`, even offset: no parity assumption on `a`. -/
theorem wA_step_true_ge_even (a : ℕ) (ha : 1 ≤ a) (d : ℕ) (μ : ℤ) (hμ : μ % 2 = 0) :
    ((a : ℝ) * wA a ⟨d, μ⟩ - 1) / 2 ≤ wA a (stepA a ⟨d, μ⟩ true) := by
  have hA1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hP1 : (1 : ℝ) ≤ (a : ℝ) ^ d := one_le_pow₀ hA1
  have hP : (0 : ℝ) < (a : ℝ) ^ d := by linarith
  rw [stepA_even_true a d μ hμ, wA_norm]
  show ((a : ℝ) * (|(μ : ℝ)| / (a : ℝ) ^ d) - 1) / 2
      ≤ |((((a : ℤ) * μ + 1 - (a : ℤ) ^ d) / 2 : ℤ) : ℝ)| / (a : ℝ) ^ d
  apply real_true_bound hP
  have hF := abs_half_ge ((a : ℤ) * μ + 1 - (a : ℤ) ^ d)
  have hx : (a : ℝ) * |(μ : ℝ)| - (a : ℝ) ^ d + 1
      ≤ |((((a : ℤ) * μ + 1 - (a : ℤ) ^ d : ℤ)) : ℝ)| := by
    push_cast
    have h1 := le_abs_self ((a : ℝ) * (μ : ℝ) + 1 - (a : ℝ) ^ d)
    have h2 := neg_abs_le ((a : ℝ) * (μ : ℝ) + 1 - (a : ℝ) ^ d)
    rcases abs_cases (μ : ℝ) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  linarith

/-- Coin `true`, odd offset above level `0`: here `a` must be odd. -/
theorem wA_step_true_ge_odd_succ (a : ℕ) (ha : a % 2 = 1) (d' : ℕ) (μ : ℤ) (hμ : μ % 2 = 1) :
    ((a : ℝ) * wA a ⟨d' + 1, μ⟩ - 1) / 2 ≤ wA a (stepA a ⟨d' + 1, μ⟩ true) := by
  have ha1 : 1 ≤ a := by omega
  have hA1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  have hA : (0 : ℝ) < (a : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ (a : ℝ) ^ d' := one_le_pow₀ hA1
  have hP : (0 : ℝ) < (a : ℝ) ^ d' := by linarith
  have h3 := pow_emod_two' a ha d'
  have hev : (μ - (a : ℤ) ^ d') % 2 = 0 := by
    generalize (a : ℤ) ^ d' = Q at h3 ⊢
    omega
  rw [stepA_odd_true_succ a d' μ hμ, wA_norm]
  show ((a : ℝ) * (|(μ : ℝ)| / (a : ℝ) ^ (d' + 1)) - 1) / 2
      ≤ |(((μ - (a : ℤ) ^ d') / 2 : ℤ) : ℝ)| / (a : ℝ) ^ d'
  rw [pow_succ, cast_half_real hev]
  apply real_true_bound_succ hA hP
  push_cast
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 := le_abs_self ((μ : ℝ) - (a : ℝ) ^ d')
  have h2 := neg_abs_le ((μ : ℝ) - (a : ℝ) ^ d')
  rcases abs_cases (μ : ℝ) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- Coin `true` away from (level `0`, odd offset), for an ODD multiplier.

The requested statement `wA_step_true_ge` (with only `1 ≤ a`) is false: see
`wA_step_true_ge_fails_two` below. -/
theorem wA_step_true_ge_of_odd (a : ℕ) (ha : 1 ≤ a) (ha2 : a % 2 = 1) (s : State)
    (h : ¬ (s.d = 0 ∧ s.mu % 2 = 1)) :
    ((a : ℝ) * wA a s - 1) / 2 ≤ wA a (stepA a s true) := by
  obtain ⟨d, μ⟩ := s
  rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
  · exact wA_step_true_ge_even a ha d μ hμ
  · cases d with
    | zero => exact absurd ⟨rfl, hμ⟩ h
    | succ d' => exact wA_step_true_ge_odd_succ a ha2 d' μ hμ

/-- Counterexample to `wA_step_true_ge` for an even multiplier: `a = 2`, `s = (2, 5)`.  The child is
`(1, ⌊(5 - 2)/2⌋) = (1, 1)` of size `1/2`, while `(a w - 1)/2 = (2 · 5/4 - 1)/2 = 3/4`. -/
theorem wA_step_true_ge_fails_two :
    ¬ (∀ (a : ℕ), 1 ≤ a → ∀ s : State, ¬ (s.d = 0 ∧ s.mu % 2 = 1) →
      ((a : ℝ) * wA a s - 1) / 2 ≤ wA a (stepA a s true)) := by
  intro H
  have h := H 2 (by norm_num) ⟨2, 5⟩ (by decide)
  have e : stepA 2 ⟨2, 5⟩ true = ⟨1, 1⟩ := by decide
  rw [e] at h
  norm_num [wA] at h

/-- Coin `true` at level `0` with odd offset. -/
theorem wA_step_true_zero_odd (a : ℕ) (ha : 1 ≤ a) (m : ℤ) (hm : m % 2 = 1) :
    wA a ⟨0, m⟩ / 2 - 1 / (2 * (a : ℝ)) ≤ wA a (stepA a ⟨0, m⟩ true) := by
  have hA1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  rw [stepA_odd_true_zero a m hm]
  show |(m : ℝ)| / (a : ℝ) ^ 0 / 2 - 1 / (2 * (a : ℝ))
      ≤ |(((1 - (a : ℤ) * m) / 2 : ℤ) : ℝ)| / (a : ℝ) ^ 1
  have hF := abs_one_sub_half_ge ((a : ℤ) * m)
  rw [abs_cast_natCast_mul] at hF
  have h := real_false_bound hA1 (le_refl (1 : ℝ)) hF
  rw [one_mul] at h
  rw [pow_zero, pow_one]
  exact h

end Coalescence.Mult

#print axioms Coalescence.Mult.stepA_rel
#print axioms Coalescence.Mult.stepA_d_even
#print axioms Coalescence.Mult.stepA_d_odd_false
#print axioms Coalescence.Mult.stepA_d_odd_true
#print axioms Coalescence.Mult.stepA_d_odd_true_zero
#print axioms Coalescence.Mult.wA_step_false_ge
#print axioms Coalescence.Mult.wA_step_true_ge_of_odd
#print axioms Coalescence.Mult.wA_step_true_ge_fails_two
#print axioms Coalescence.Mult.wA_step_true_zero_odd
