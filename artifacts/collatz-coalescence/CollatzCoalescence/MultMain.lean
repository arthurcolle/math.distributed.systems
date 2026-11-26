import CollatzCoalescence.MultLink
import CollatzCoalescence.MultPotential

/-!
# `5x+1`: a positive proportion of neighbouring classes never merge

For the map `x ↦ x / 2` (even `x`), `(5x + 1) / 2` (odd `x`), the proportion of residue classes mod
`2^k` on which the orbits of `x` and `x + 1` have merged after `k` steps is at most `1 - ε` for every
`k`, with one `ε > 0`.  For the multiplier `3` the same proportion tends to `1`
(`Coalescence.merged_proportion_tendsto`).
-/

namespace Coalescence.Mult
open Generic

/-- Merged residue classes are counted by the chain, for every odd multiplier `a ≥ 3`. -/
theorem card_mergedA_eq (a : ℕ) (ha : a % 2 = 1) (ha2 : 2 ≤ a) : ∀ (k : ℕ) (s : State),
    ((mergedA a s k).card : ℝ) = pAbs (stepA a) absorbed k s * 2 ^ k
  | 0, s => by
      rw [card_mergedA_zero a ha2, pAbs_zero]
      split_ifs <;> simp
  | k + 1, s => by
      rw [card_mergedA_succ a ha, Nat.cast_add, card_mergedA_eq a ha ha2 k,
        card_mergedA_eq a ha ha2 k, pAbs_succ]
      ring

open Classical in
/-- **Saturation for `5x+1`.** There is `ε > 0` such that for every `k` at most `(1 - ε) 2^k` residues
`r` mod `2^k` satisfy `(Ta 5)^[k] (r + 2^k t) = (Ta 5)^[k] (r + 2^k t + 1)` for all integers `t`. -/
theorem five_merged_bounded :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ,
      (((Finset.range (2 ^ k)).filter fun r : ℕ =>
        ∀ t : ℤ, (Ta 5)^[k] ((r : ℤ) + 2 ^ k * t) = (Ta 5)^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ) ≤
        (1 - ε) * 2 ^ k := by
  obtain ⟨ε, hε, h⟩ := saturation_five
  refine ⟨ε, hε, fun k => ?_⟩
  have heq : mergedA 5 ⟨0, 1⟩ k = (Finset.range (2 ^ k)).filter fun r : ℕ =>
      ∀ t : ℤ, (Ta 5)^[k] ((r : ℤ) + 2 ^ k * t) = (Ta 5)^[k] ((r : ℤ) + 2 ^ k * t + 1) := by
    unfold mergedA
    refine Finset.filter_congr fun r _ => ?_
    simp only [pow_zero, one_mul, Nat.cast_ofNat]
  rw [← heq, card_mergedA_eq 5 (by norm_num) (by norm_num)]
  exact mul_le_mul_of_nonneg_right (h k) (by positivity)

#print axioms card_mergedA_eq
#print axioms five_merged_bounded

end Coalescence.Mult
