import Mathlib
import CollatzCoalescence.Chain

/-- Shortcut Collatz map on the natural numbers. -/
def Tn (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

theorem Tn_two_mul (y : ℕ) : Tn (2 * y) = y := by
  unfold Tn
  rw [if_pos (by omega)]
  omega

theorem Tn_of_even {x : ℕ} (hx : x % 2 = 0) : Tn x = x / 2 := by
  unfold Tn
  rw [if_pos hx]

theorem Tn_of_odd {x : ℕ} (hx : x % 2 = 1) : Tn x = (3 * x + 1) / 2 := by
  have hx' : ¬ x % 2 = 0 := by omega
  unfold Tn
  rw [if_neg hx']

/-- (a) `j` halvings strip a factor `2^j`. -/
theorem Tn_iterate_two_pow_mul (j x : ℕ) : Tn^[j] (2 ^ j * x) = x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    have e : 2 ^ (j + 1) * x = 2 * (2 ^ j * x) := by ring
    rw [Function.iterate_succ_apply, e, Tn_two_mul, ih]

/-- (c), first orbit: `j` halvings then one odd step. -/
theorem Tn_iterate_succ_two_pow_mul_odd (j o : ℕ) (ho : o % 2 = 1) :
    Tn^[j + 1] (2 ^ j * o) = (3 * o + 1) / 2 := by
  rw [Function.iterate_succ_apply', Tn_iterate_two_pow_mul, Tn_of_odd ho]

/-- (c), second orbit: one odd step, `j - 1` halvings, one more halving. -/
theorem Tn_iterate_succ_two_pow_mul_odd_add (j s m o : ℕ) (hj : 1 ≤ j) (hm : m % 2 = 1)
    (hjs : 3 * m + 1 = 2 ^ j * s) (hs : s % 2 = 1) (ho : o % 2 = 1) :
    Tn^[j + 1] (2 ^ j * o + m) = (3 * o + s) / 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hodd : (2 ^ (i + 1) * o + m) % 2 = 1 := by
    have e : 2 ^ (i + 1) * o = 2 * (2 ^ i * o) := by ring
    rw [e]
    omega
  have hfirst : Tn (2 ^ (i + 1) * o + m) = 2 ^ i * (3 * o + s) := by
    rw [Tn_of_odd hodd]
    have e : 3 * (2 ^ (i + 1) * o + m) + 1 = 2 * (2 ^ i * (3 * o + s)) := by
      have e1 : 3 * (2 ^ (i + 1) * o + m) + 1 = 3 * (2 ^ (i + 1) * o) + (3 * m + 1) := by ring
      rw [e1, hjs]
      ring
    rw [e]
    omega
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply, hfirst,
    Tn_iterate_two_pow_mul, Tn_of_even (by omega)]

theorem two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    rw [pow_succ]
    omega

/-- Solve `3 * o + 1 = A + B * t` when `3 ∤ B`. -/
theorem exists_three_mul_add_one (A B : ℕ) (hB : B % 3 = 1 ∨ B % 3 = 2) :
    ∃ t o : ℕ, 3 * o + 1 = A + B * t := by
  have hA : A % 3 = 0 ∨ A % 3 = 1 ∨ A % 3 = 2 := by omega
  rcases hA with hA | hA | hA
  · rcases hB with hB | hB
    · exact ⟨1, (A + B * 1 - 1) / 3, by omega⟩
    · exact ⟨2, (A + B * 2 - 1) / 3, by omega⟩
  · exact ⟨0, (A + B * 0 - 1) / 3, by omega⟩
  · rcases hB with hB | hB
    · exact ⟨2, (A + B * 2 - 1) / 3, by omega⟩
    · exact ⟨1, (A + B * 1 - 1) / 3, by omega⟩

/-- Every positive offset coalesces on a full residue class. -/
theorem every_offset_merges (m : ℕ) (hm : 0 < m) :
    ∃ k r : ℕ, ∀ q : ℕ, Tn^[k] (r + 2 ^ k * q) = Tn^[k] (r + m + 2 ^ k * q) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨m', rfl | rfl⟩
    · -- (b) even offset `2 * m'`
      obtain ⟨k, r, hkr⟩ := ih m' (by omega) (by omega)
      refine ⟨k + 1, 2 * r, fun q => ?_⟩
      have e1 : 2 * r + 2 ^ (k + 1) * q = 2 * (r + 2 ^ k * q) := by ring
      have e2 : 2 * r + 2 * m' + 2 ^ (k + 1) * q = 2 * (r + m' + 2 ^ k * q) := by ring
      rw [e1, e2, Function.iterate_succ_apply, Function.iterate_succ_apply, Tn_two_mul,
        Tn_two_mul]
      exact hkr q
    · -- (c) odd offset `m = 2 * m' + 1`, with `3 * m + 1 = 2 ^ j * s`, `s` odd
      obtain ⟨j, s, hsodd, hjs⟩ :=
        Nat.exists_eq_two_pow_mul_odd (n := 3 * (2 * m' + 1) + 1) (by omega)
      obtain ⟨m₁, rfl⟩ := hsodd
      have hmodd : (2 * m' + 1) % 2 = 1 := by omega
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [pow_zero, one_mul] at hjs
          omega
        · exact hj
      have hs : (2 * m₁ + 1) % 2 = 1 := by omega
      rcases Nat.eq_zero_or_pos m₁ with rfl | hm₁
      · -- `s = 1`
        refine ⟨j + 1, 2 ^ j, fun q => ?_⟩
        have ho : (1 + 2 * q) % 2 = 1 := by omega
        have e1 : 2 ^ j + 2 ^ (j + 1) * q = 2 ^ j * (1 + 2 * q) := by ring
        have e2 : 2 ^ j + (2 * m' + 1) + 2 ^ (j + 1) * q
            = 2 ^ j * (1 + 2 * q) + (2 * m' + 1) := by ring
        rw [e1, e2, Tn_iterate_succ_two_pow_mul_odd j _ ho,
          Tn_iterate_succ_two_pow_mul_odd_add j _ _ _ hj hmodd hjs hs ho]
        rfl
      · -- `s > 1`: recurse on `m₁ = (s - 1) / 2 < m`
        have hlt : m₁ < 2 * m' + 1 := by
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          have hpos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
          have hle : 2 * (2 * m₁ + 1) ≤ 2 ^ (i + 1) * (2 * m₁ + 1) := by
            rw [pow_succ]
            nlinarith
          omega
        obtain ⟨k₁, r₁, h₁⟩ := ih m₁ hlt hm₁
        obtain ⟨t₀, o₀, hto⟩ :=
          exists_three_mul_add_one (2 * r₁) (2 ^ (k₁ + 1)) (two_pow_mod_three (k₁ + 1))
        refine ⟨k₁ + (j + 1), 2 ^ j * o₀, fun q => ?_⟩
        have ho : (o₀ + 2 ^ (k₁ + 1) * q) % 2 = 1 := by
          have e : 2 ^ (k₁ + 1) * q = 2 * (2 ^ k₁ * q) := by ring
          have e' : 2 ^ (k₁ + 1) * t₀ = 2 * (2 ^ k₁ * t₀) := by ring
          rw [e]
          rw [e'] at hto
          omega
        have e1 : 2 ^ j * o₀ + 2 ^ (k₁ + (j + 1)) * q
            = 2 ^ j * (o₀ + 2 ^ (k₁ + 1) * q) := by ring
        have e2 : 2 ^ j * o₀ + (2 * m' + 1) + 2 ^ (k₁ + (j + 1)) * q
            = 2 ^ j * (o₀ + 2 ^ (k₁ + 1) * q) + (2 * m' + 1) := by ring
        have e3 : 3 * (o₀ + 2 ^ (k₁ + 1) * q) + 1
            = 2 * (r₁ + 2 ^ k₁ * (t₀ + 3 * q)) := by
          have e : 3 * (o₀ + 2 ^ (k₁ + 1) * q) + 1
              = (3 * o₀ + 1) + 3 * (2 ^ (k₁ + 1) * q) := by ring
          rw [e, hto]
          ring
        have e4 : 3 * (o₀ + 2 ^ (k₁ + 1) * q) + (2 * m₁ + 1)
            = 2 * (r₁ + m₁ + 2 ^ k₁ * (t₀ + 3 * q)) := by
          have e : 3 * (o₀ + 2 ^ (k₁ + 1) * q) + (2 * m₁ + 1)
              = (3 * (o₀ + 2 ^ (k₁ + 1) * q) + 1) + 2 * m₁ := by ring
          rw [e, e3]
          ring
        rw [e1, e2, Function.iterate_add_apply Tn k₁ (j + 1),
          Function.iterate_add_apply Tn k₁ (j + 1),
          Tn_iterate_succ_two_pow_mul_odd j _ ho,
          Tn_iterate_succ_two_pow_mul_odd_add j _ _ _ hj hmodd hjs hs ho, e3, e4,
          Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
          Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
        exact h₁ (t₀ + 3 * q)

/-- Bridge to the integer map of `Chain.lean`. -/
theorem T_natCast (x : ℕ) : Coalescence.T (x : ℤ) = ((Tn x : ℕ) : ℤ) := by
  unfold Coalescence.T Tn
  split_ifs <;> omega

#print axioms every_offset_merges
#print axioms T_natCast
