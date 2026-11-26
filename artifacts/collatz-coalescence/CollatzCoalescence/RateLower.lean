import CollatzCoalescence.Defs
import CollatzCoalescence.Generic

/-!
# A polynomial lower bound for the survival probability

Started from `⟨0, 1⟩`, the chain is not absorbed within `k` steps with probability at least
`1 / (4 * √(2k + 2))`.  The level coordinate dominates a simple random walk killed below
level `2`, whose survival probability is a central binomial coefficient.
-/

namespace Coalescence
open Generic

namespace RateLower

/-! ## Survival of the simple random walk -/

/-- Probability that a simple random walk started at height `h` stays `≥ 0` for `j` steps. -/
noncomputable def r : ℕ → ℕ → ℝ
  | 0, _ => 1
  | j + 1, h => (r j (h + 1) + (if h = 0 then 0 else r j (h - 1))) / 2

theorem r_zero (h : ℕ) : r 0 h = 1 := rfl

theorem r_succ (j h : ℕ) :
    r (j + 1) h = (r j (h + 1) + (if h = 0 then 0 else r j (h - 1))) / 2 := rfl

theorem r_succ_zero (j : ℕ) : r (j + 1) 0 = r j 1 / 2 := by
  rw [r_succ]; simp

theorem r_succ_succ (j h : ℕ) : r (j + 1) (h + 1) = (r j (h + 2) + r j h) / 2 := by
  rw [r_succ]; simp

theorem r_anti : ∀ (j h : ℕ), r (j + 1) h ≤ r j h
  | 0, h => by
    rcases h with _ | h
    · rw [r_succ_zero, r_zero, r_zero]; norm_num
    · rw [r_succ_succ, r_zero, r_zero, r_zero]; norm_num
  | j + 1, h => by
    rcases h with _ | h
    · rw [r_succ_zero (j + 1), r_succ_zero j]
      have := r_anti j 1
      linarith
    · have e1 := r_succ_succ (j + 1) h
      have e2 := r_succ_succ j h
      have h1 := r_anti j (h + 2)
      have h2 := r_anti j h
      linarith

/-! ## Comparison with the chain -/

/-- From level `d + 2` the chain survives at least as long as the walk started at `d`. -/
theorem r_le_survival : ∀ (j d : ℕ) (μ : ℤ),
    r j d ≤ 1 - pAbs step absorbed j ⟨d + 2, μ⟩
  | 0, d, μ => by
    have hne : (⟨d + 2, μ⟩ : State) ≠ absorbed := by
      intro h
      have := congrArg State.d h
      simp [absorbed] at this
    rw [pAbs_zero, if_neg hne, r_zero]; norm_num
  | j + 1, d, μ => by
    rw [pAbs_succ]
    rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
    · rw [step_even_false _ _ hμ, step_even_true _ _ hμ,
        State.norm_of_pos _ _ (by omega), State.norm_of_pos _ _ (by omega)]
      have h0 := r_le_survival j d (μ / 2)
      have h1 := r_le_survival j d ((3 * μ + 1 - 3 ^ (d + 2)) / 2)
      have h2 := r_anti j d
      linarith
    · rw [step_odd_false _ _ hμ, step_odd_true_succ _ _ hμ,
        State.norm_of_pos _ _ (by omega)]
      have h0 : r j (d + 1) ≤ 1 - pAbs step absorbed j ⟨d + 2 + 1, (3 * μ + 1) / 2⟩ :=
        r_le_survival j (d + 1) ((3 * μ + 1) / 2)
      rcases d with _ | d
      · have h1 := pAbs_le_one step absorbed j ⟨0 + 1, (μ - 3 ^ (0 + 1)) / 2⟩
        rw [r_succ_zero]
        linarith
      · have h1 : r j d ≤ 1 - pAbs step absorbed j ⟨d + 1 + 1, (μ - 3 ^ (d + 1 + 1)) / 2⟩ :=
          r_le_survival j d ((μ - 3 ^ (d + 1 + 1)) / 2)
        rw [r_succ_succ]
        linarith

/-- Two forced-probability-`1/4` steps lead from `⟨0, 1⟩` to level `2`. -/
theorem start_bound (k : ℕ) : r k 0 / 4 ≤ 1 - pAbs step absorbed k ⟨0, 1⟩ := by
  have e1 : step ⟨0, 1⟩ true = ⟨1, -1⟩ := by decide
  have e2 : step ⟨1, -1⟩ false = ⟨2, -1⟩ := by decide
  have hmono := pAbs_mono step absorbed step_absorbed' (Nat.le_add_right k 2) ⟨0, 1⟩
  have h2 : pAbs step absorbed (k + 2) ⟨0, 1⟩ =
      (pAbs step absorbed (k + 1) (step ⟨0, 1⟩ false) +
        pAbs step absorbed (k + 1) (step ⟨0, 1⟩ true)) / 2 :=
    pAbs_succ step absorbed (k + 1) ⟨0, 1⟩
  have h1 : pAbs step absorbed (k + 1) ⟨1, -1⟩ =
      (pAbs step absorbed k (step ⟨1, -1⟩ false) +
        pAbs step absorbed k (step ⟨1, -1⟩ true)) / 2 :=
    pAbs_succ step absorbed k ⟨1, -1⟩
  rw [e1] at h2
  rw [e2] at h1
  have ha := pAbs_le_one step absorbed (k + 1) (step ⟨0, 1⟩ false)
  have hb := pAbs_le_one step absorbed k (step ⟨1, -1⟩ true)
  have hc : r k 0 ≤ 1 - pAbs step absorbed k ⟨0 + 2, -1⟩ := r_le_survival k 0 (-1)
  have hc' : r k 0 ≤ 1 - pAbs step absorbed k ⟨2, -1⟩ := hc
  linarith

/-! ## Closed form by the reflection principle -/

/-- Binomial "distribution function": total weight of the endpoints `2 i - j ≤ m`. -/
noncomputable def F (j : ℕ) (m : ℤ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), if 2 * (i : ℤ) - j ≤ m then (j.choose i : ℝ) else 0

theorem F_zero (m : ℤ) : F 0 m = if 0 ≤ m then 1 else 0 := by
  unfold F
  simp

theorem F_succ (j : ℕ) (m : ℤ) : F (j + 1) m = F j (m + 1) + F j (m - 1) := by
  have hA : F (j + 1) m =
      (∑ i ∈ Finset.range (j + 1),
          if 2 * (i : ℤ) - j ≤ m - 1 then ((j + 1).choose (i + 1) : ℝ) else 0)
        + (if -(j : ℤ) ≤ m + 1 then 1 else 0) := by
    unfold F
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have hiff : (2 * ((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) ≤ m) ↔
          (2 * (i : ℤ) - j ≤ m - 1) := by omega
      simp only [hiff]
    · have hiff : (2 * ((0 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) ≤ m) ↔ (-(j : ℤ) ≤ m + 1) := by omega
      simp only [hiff, Nat.choose_zero_right, Nat.cast_one]
  have hB : F j (m + 1) =
      (∑ i ∈ Finset.range j,
          if 2 * (i : ℤ) - j ≤ m - 1 then (j.choose (i + 1) : ℝ) else 0)
        + (if -(j : ℤ) ≤ m + 1 then 1 else 0) := by
    unfold F
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have hiff : (2 * ((i + 1 : ℕ) : ℤ) - (j : ℤ) ≤ m + 1) ↔
          (2 * (i : ℤ) - j ≤ m - 1) := by omega
      simp only [hiff]
    · have hiff : (2 * ((0 : ℕ) : ℤ) - (j : ℤ) ≤ m + 1) ↔ (-(j : ℤ) ≤ m + 1) := by omega
      simp only [hiff, Nat.choose_zero_right, Nat.cast_one]
  have hC : (∑ i ∈ Finset.range (j + 1),
        if 2 * (i : ℤ) - j ≤ m - 1 then (j.choose (i + 1) : ℝ) else 0)
      = ∑ i ∈ Finset.range j,
        if 2 * (i : ℤ) - j ≤ m - 1 then (j.choose (i + 1) : ℝ) else 0 := by
    rw [Finset.sum_range_succ]
    simp [Nat.choose_succ_self]
  have hD : (∑ i ∈ Finset.range (j + 1),
        if 2 * (i : ℤ) - j ≤ m - 1 then ((j + 1).choose (i + 1) : ℝ) else 0)
      = F j (m - 1) + ∑ i ∈ Finset.range (j + 1),
        if 2 * (i : ℤ) - j ≤ m - 1 then (j.choose (i + 1) : ℝ) else 0 := by
    unfold F
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    · rw [Nat.choose_succ_succ]; push_cast; ring
    · simp
  rw [hA, hB, hD, hC]; ring

/-- Reflection principle: the number of nonnegative paths is a window of binomial weights. -/
theorem r_mul_two_pow_aux : ∀ (j h : ℕ) (a b : ℤ), a = (h : ℤ) + 1 → b = -(h : ℤ) - 1 →
    r j h * 2 ^ j = F j a - F j b
  | 0, h, a, b, ha, hb => by
    rw [r_zero, F_zero, F_zero, if_pos (by omega), if_neg (by omega)]; norm_num
  | j + 1, h, a, b, ha, hb => by
    rw [F_succ, F_succ, pow_succ]
    rcases h with _ | h
    · have ih := r_mul_two_pow_aux j 1 (a + 1) (b - 1) (by omega) (by omega)
      have e : a - 1 = b + 1 := by omega
      rw [r_succ_zero, e]
      linarith
    · have ih1 := r_mul_two_pow_aux j (h + 2) (a + 1) (b - 1) (by omega) (by omega)
      have ih2 := r_mul_two_pow_aux j h (a - 1) (b + 1) (by omega) (by omega)
      rw [r_succ_succ]
      linarith

/-- The walk started at `0` survives `k` steps with probability `C(k, ⌈k/2⌉) / 2^k`. -/
theorem r_zero_mul_two_pow (k : ℕ) : r k 0 * 2 ^ k = (k.choose ((k + 1) / 2) : ℝ) := by
  rw [r_mul_two_pow_aux k 0 1 (-1) (by simp) (by simp)]
  have hmem : (k + 1) / 2 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  unfold F
  rw [← Finset.sum_sub_distrib]
  calc ∑ i ∈ Finset.range (k + 1),
        ((if 2 * (i : ℤ) - k ≤ 1 then (k.choose i : ℝ) else 0) -
          (if 2 * (i : ℤ) - k ≤ -1 then (k.choose i : ℝ) else 0))
      = ∑ i ∈ Finset.range (k + 1), if i = (k + 1) / 2 then (k.choose i : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = (k + 1) / 2
        · rw [if_pos h, if_pos (by omega), if_neg (by omega)]; ring
        · rw [if_neg h]
          by_cases h2 : 2 * (i : ℤ) - k ≤ -1
          · rw [if_pos h2, if_pos (by omega)]; ring
          · rw [if_neg h2, if_neg (by omega)]; ring
    _ = (k.choose ((k + 1) / 2) : ℝ) := by
        rw [Finset.sum_ite_eq', if_pos hmem]

/-! ## The central binomial coefficient -/

theorem four_pow_le_centralBinom_sq (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n * 4 ^ n ≤ n.centralBinom ^ 2 * (4 * n) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.centralBinom, Nat.choose]
  | succ n hn ih =>
    have hrec := Nat.succ_mul_centralBinom_succ n
    have hpos : 0 < (n + 1) ^ 2 := by positivity
    apply Nat.le_of_mul_le_mul_left _ hpos
    calc (n + 1) ^ 2 * (4 ^ (n + 1) * 4 ^ (n + 1))
        = 16 * (n + 1) ^ 2 * (4 ^ n * 4 ^ n) := by ring
      _ ≤ 16 * (n + 1) ^ 2 * (n.centralBinom ^ 2 * (4 * n)) := Nat.mul_le_mul_left _ ih
      _ = 16 * (n + 1) * n.centralBinom ^ 2 * (4 * n * (n + 1)) := by ring
      _ ≤ 16 * (n + 1) * n.centralBinom ^ 2 * ((2 * n + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (by nlinarith)
      _ = (2 * (2 * n + 1) * n.centralBinom) ^ 2 * (4 * (n + 1)) := by ring
      _ = ((n + 1) * (n + 1).centralBinom) ^ 2 * (4 * (n + 1)) := by rw [hrec]
      _ = (n + 1) ^ 2 * ((n + 1).centralBinom ^ 2 * (4 * (n + 1))) := by ring

theorem four_pow_le_choose_sq (k : ℕ) :
    4 ^ k ≤ (k.choose ((k + 1) / 2)) ^ 2 * (2 * k + 2) := by
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · have h1 : (2 * n + 1) / 2 = n := by omega
    rw [h1]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have h := four_pow_le_centralBinom_sq n hn
      rw [Nat.centralBinom_eq_two_mul_choose] at h
      calc 4 ^ (2 * n) = 4 ^ n * 4 ^ n := by ring
        _ ≤ (2 * n).choose n ^ 2 * (4 * n) := h
        _ ≤ (2 * n).choose n ^ 2 * (2 * (2 * n) + 2) := Nat.mul_le_mul_left _ (by omega)
  · have h1 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    rw [h1]
    have hc : (n + 1).centralBinom = 2 * (2 * n + 1).choose (n + 1) := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
        Nat.choose_succ_succ, ← Nat.choose_symm_half n]
      ring
    have h := four_pow_le_centralBinom_sq (n + 1) (by omega)
    rw [hc] at h
    have e : 4 ^ (n + 1) * 4 ^ (n + 1) = 4 * 4 ^ (2 * n + 1) := by ring
    have e2 : (2 * (2 * n + 1).choose (n + 1)) ^ 2 * (4 * (n + 1)) =
        4 * ((2 * n + 1).choose (n + 1) ^ 2 * (2 * (2 * n + 1) + 2)) := by ring
    rw [e, e2] at h
    exact Nat.le_of_mul_le_mul_left h (by norm_num)

theorem two_pow_le_choose_mul_sqrt (k : ℕ) :
    (2 : ℝ) ^ k ≤ (k.choose ((k + 1) / 2) : ℝ) * Real.sqrt (2 * (k : ℝ) + 2) := by
  have h := four_pow_le_choose_sq k
  have h' : ((2 : ℝ) ^ k) ^ 2 ≤ (k.choose ((k + 1) / 2) : ℝ) ^ 2 * (2 * (k : ℝ) + 2) := by
    have hcast : ((4 ^ k : ℕ) : ℝ) ≤ (((k.choose ((k + 1) / 2)) ^ 2 * (2 * k + 2) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at hcast
    calc ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ _ := hcast
  have hc : (0 : ℝ) ≤ (k.choose ((k + 1) / 2) : ℝ) := Nat.cast_nonneg _
  calc (2 : ℝ) ^ k = Real.sqrt (((2 : ℝ) ^ k) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt ((k.choose ((k + 1) / 2) : ℝ) ^ 2 * (2 * (k : ℝ) + 2)) :=
        Real.sqrt_le_sqrt h'
    _ = (k.choose ((k + 1) / 2) : ℝ) * Real.sqrt (2 * (k : ℝ) + 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

end RateLower

/-- **Polynomial lower bound for survival.** Started from `⟨0, 1⟩`, the chain has not been
absorbed after `k` steps with probability at least `1 / (4 √(2k + 2))`. -/
theorem survival_lower (k : ℕ) :
    1 / (4 * Real.sqrt (2 * (k : ℝ) + 2)) ≤ 1 - pAbs step absorbed k ⟨0, 1⟩ := by
  have h1 := RateLower.start_bound k
  have h2 := RateLower.r_zero_mul_two_pow k
  have h3 := RateLower.two_pow_le_choose_mul_sqrt k
  have hs : 0 < Real.sqrt (2 * (k : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h4 : 1 ≤ RateLower.r k 0 * Real.sqrt (2 * (k : ℝ) + 2) := by
    rw [← h2] at h3
    have h3' : 1 * (2 : ℝ) ^ k ≤ RateLower.r k 0 * Real.sqrt (2 * (k : ℝ) + 2) * 2 ^ k := by
      linarith
    exact le_of_mul_le_mul_right h3' hp
  have h5 : 1 / Real.sqrt (2 * (k : ℝ) + 2) ≤ RateLower.r k 0 := by
    rw [div_le_iff₀ hs]; exact h4
  calc 1 / (4 * Real.sqrt (2 * (k : ℝ) + 2))
      = 1 / Real.sqrt (2 * (k : ℝ) + 2) / 4 := by
        rw [div_div, mul_comm]
    _ ≤ RateLower.r k 0 / 4 := by linarith
    _ ≤ 1 - pAbs step absorbed k ⟨0, 1⟩ := h1

end Coalescence

#print axioms Coalescence.survival_lower
