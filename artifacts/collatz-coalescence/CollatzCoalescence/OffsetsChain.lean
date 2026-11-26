import CollatzCoalescence.Chain

/-!
# Every offset can merge, at the level of the pair chain

`offset_absorbable`: from every level-zero state `⟨0, μ⟩` some coin word leads to the absorbed
state `⟨0, 0⟩` (Lemma "Every offset can merge" of `main.tex`, stated for the chain `step`,
and for every integer offset, including the non-canonical negative ones).
-/

namespace Coalescence

theorem run_nil (s : State) : run s [] = s := rfl

theorem run_cons (s : State) (c : Bool) (w : List Bool) :
    run s (c :: w) = run (step s c) w := rfl

theorem run_append (s : State) (w₁ w₂ : List Bool) :
    run s (w₁ ++ w₂) = run (run s w₁) w₂ := by
  simp [run, List.foldl_append]

/-- At level one, `i` coins `false` strip a factor `2^i` from the offset. -/
theorem run_replicate_false (i : ℕ) (ν : ℤ) :
    run ⟨1, 2 ^ i * ν⟩ (List.replicate i false) = ⟨1, ν⟩ := by
  induction i with
  | zero => simp [run]
  | succ i ih =>
    have e : (2 : ℤ) ^ (i + 1) * ν = 2 * (2 ^ i * ν) := by ring
    have hmod : (2 : ℤ) ^ (i + 1) * ν % 2 = 0 := by rw [e]; omega
    have hdiv : (2 : ℤ) ^ (i + 1) * ν / 2 = 2 ^ i * ν := by rw [e]; omega
    rw [List.replicate_succ, run_cons, step_even_false 1 _ hmod,
      State.norm_of_pos 1 _ (by norm_num), hdiv]
    exact ih

/-- From `⟨1, 2^i σ⟩` with `σ` odd, the word `false^i true` leads to `⟨0, |(σ - 1) / 2|⟩`. -/
theorem run_strip (i : ℕ) (σ : ℤ) (hσ : σ % 2 = 1) (w : List Bool) :
    run ⟨1, 2 ^ i * σ⟩ (List.replicate i false ++ true :: w) = run ⟨0, |(σ - 1) / 2|⟩ w := by
  rw [run_append, run_replicate_false, run_cons]
  have h := step_odd_true_succ 0 σ hσ
  rw [State.norm_zero, pow_zero] at h
  have h' : step ⟨1, σ⟩ true = ⟨0, |(σ - 1) / 2|⟩ := h
  rw [h']

/-- **Every offset can merge.** From every level-zero state some coin word leads to the
absorbed state. -/
theorem offset_absorbable (μ : ℤ) : ∃ w : List Bool, run ⟨0, μ⟩ w = absorbed := by
  induction hn : μ.natAbs using Nat.strong_induction_on generalizing μ with
  | _ n ih =>
    subst hn
    by_cases h0 : μ = 0
    · subst h0
      exact ⟨[], rfl⟩
    rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
    · -- even offset: halve
      have hlt : (|μ / 2|).natAbs < μ.natAbs := by
        rw [Int.natAbs_abs]
        omega
      obtain ⟨w, hw⟩ := ih _ hlt (|μ / 2|) rfl
      refine ⟨false :: w, ?_⟩
      rw [run_cons, step_even_false 0 μ hμ, State.norm_zero]
      exact hw
    · -- odd offset: `3 |μ| + 1 = 2^j s` with `s` odd
      obtain ⟨j, s, hsodd, hjs⟩ :=
        Nat.exists_eq_two_pow_mul_odd (n := 3 * μ.natAbs + 1) (by omega)
      obtain ⟨s₁, rfl⟩ := hsodd
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [pow_zero, one_mul] at hjs
          omega
        · exact hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hjs' : 3 * μ.natAbs + 1 = 2 * (2 ^ i * (2 * s₁ + 1)) := by
        rw [hjs]
        ring
      have hpos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      have hle : 2 * s₁ + 1 ≤ 2 ^ i * (2 * s₁ + 1) := Nat.le_mul_of_pos_left _ hpos
      -- the same identity over `ℤ`
      have hZ : 3 * (μ.natAbs : ℤ) + 1 = 2 * (2 ^ i * (2 * (s₁ : ℤ) + 1)) := by
        exact_mod_cast hjs'
      have hσ : (2 * (s₁ : ℤ) + 1) % 2 = 1 := by omega
      have hν : |(2 * (s₁ : ℤ) + 1 - 1) / 2| = (s₁ : ℤ) := by
        have e : (2 * (s₁ : ℤ) + 1 - 1) / 2 = (s₁ : ℤ) := by omega
        rw [e]
        exact abs_of_nonneg (Int.natCast_nonneg s₁)
      have hlt : ((s₁ : ℤ)).natAbs < μ.natAbs := by
        rw [Int.natAbs_natCast]
        omega
      obtain ⟨w, hw⟩ := ih _ hlt (s₁ : ℤ) rfl
      -- first coin: `false` for positive offsets, `true` for negative ones
      rcases lt_or_gt_of_ne h0 with hneg | hpos'
      · have habs : (μ.natAbs : ℤ) = -μ := by omega
        refine ⟨true :: (List.replicate i false ++ true :: w), ?_⟩
        have hfirst : step ⟨0, μ⟩ true = ⟨1, 2 ^ i * (2 * (s₁ : ℤ) + 1)⟩ := by
          rw [step_odd_true_zero μ hμ]
          have e : (1 - 3 * μ) / 2 = 2 ^ i * (2 * (s₁ : ℤ) + 1) := by
            rw [habs] at hZ
            omega
          rw [e]
        rw [run_cons, hfirst, run_strip i _ hσ, hν]
        exact hw
      · have habs : (μ.natAbs : ℤ) = μ := by omega
        refine ⟨false :: (List.replicate i false ++ true :: w), ?_⟩
        have hfirst : step ⟨0, μ⟩ false = ⟨1, 2 ^ i * (2 * (s₁ : ℤ) + 1)⟩ := by
          rw [step_odd_false 0 μ hμ]
          have e : (3 * μ + 1) / 2 = 2 ^ i * (2 * (s₁ : ℤ) + 1) := by
            rw [habs] at hZ
            omega
          rw [e]
        rw [run_cons, hfirst, run_strip i _ hσ, hν]
        exact hw

end Coalescence

#print axioms Coalescence.offset_absorbable
