import Statement

/-!
# What is claimed

The theorems of `Solution.lean`, with `sorry` in place of their proofs, for the tool Comparator.
This file imports `Statement.lean` alone, and that file imports Mathlib alone.  Nothing imports this file.
-/

namespace Solution

open Classical in
/-- **Rate.** The number of residues `r` mod `2^k` on whose class the orbits of `x` and `x + 1` under
the shortcut map have not merged after `k` steps is between `c₁ 2^k / √k` and `c₂ 2^k / √k`. -/
theorem neighbour_merge_rate :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 1 ≤ k →
      c₁ * 2 ^ k / Real.sqrt k ≤
        (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, Statement.T^[k] ((r : ℤ) + 2 ^ k * t) = Statement.T^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ) ∧
      (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, Statement.T^[k] ((r : ℤ) + 2 ^ k * t) = Statement.T^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ) ≤
        c₂ * 2 ^ k / Real.sqrt k := by
  sorry

open Classical in
/-- **Rate, for integers.** For each `k ≥ 1` the `n` with `Statement.Tn^[k] n ≠ Statement.Tn^[k] (n + 1)` have lower and
upper natural density between `c₁ / √k` and `c₂ / √k`. -/
theorem unmerged_density_rate :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (c₁ / Real.sqrt k - ε) * (N : ℝ) ≤
          (((Finset.range N).filter fun n : ℕ => Statement.Tn^[k] n ≠ Statement.Tn^[k] (n + 1)).card : ℝ) ∧
        (((Finset.range N).filter fun n : ℕ => Statement.Tn^[k] n ≠ Statement.Tn^[k] (n + 1)).card : ℝ) ≤
          (c₂ / Real.sqrt k + ε) * (N : ℝ) := by
  sorry

open Classical in
/-- **Density one with the time bound** (`m = 1` is Gao's 1993 conjecture, first proved by
O. J. Said Duran): almost every `n` has `Statement.Cn^[j] n = Statement.Cn^[j] (n + m)` for some `j` with `2^j ≤ n`. -/
theorem coalescence_density_one_log (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (1 - ε) * (N : ℝ) ≤
      (((Finset.range N).filter fun n : ℕ =>
        ∃ j : ℕ, 2 ^ j ≤ n ∧ Statement.Cn^[j] n = Statement.Cn^[j] (n + m)).card : ℝ) := by
  sorry

/-- **Every offset merges** on a full residue class. -/
theorem every_offset_merges (m : ℕ) (hm : 0 < m) :
    ∃ k r : ℕ, ∀ q : ℕ, Statement.Tn^[k] (r + 2 ^ k * q) = Statement.Tn^[k] (r + m + 2 ^ k * q) := by
  sorry

end Solution
