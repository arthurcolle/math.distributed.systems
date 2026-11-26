import CollatzCoalescence.MultGeneral

/-!
# The multiplier 3 is characterized by neighbour merging

For an odd multiplier `a ≥ 3` and the map `x ↦ x / 2` (even `x`), `(a x + 1) / 2` (odd `x`): the
proportion of residue classes mod `2^k` on which the orbits of `x` and `x + 1` have merged after `k`
steps tends to `1` if and only if `a = 3`.
-/

namespace Coalescence.Mult
open Generic Filter Topology

open Classical in
/-- **Merging with density one happens exactly for the multiplier 3.** -/
theorem merged_fraction_tendsto_one_iff (a : ℕ) (ha : a % 2 = 1) (ha3 : 3 ≤ a) :
    Tendsto (fun k : ℕ =>
        (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ∀ t : ℤ, (Ta a)^[k] ((r : ℤ) + 2 ^ k * t) = (Ta a)^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ)
          / 2 ^ k) atTop (𝓝 1) ↔ a = 3 := by
  have hfun : (fun k : ℕ =>
        (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ∀ t : ℤ, (Ta a)^[k] ((r : ℤ) + 2 ^ k * t) = (Ta a)^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ)
          / 2 ^ k) = fun k : ℕ => pAbs (stepA a) absorbed k ⟨0, 1⟩ := by
    funext k
    have heq : mergedA a ⟨0, 1⟩ k = (Finset.range (2 ^ k)).filter fun r : ℕ =>
        ∀ t : ℤ, (Ta a)^[k] ((r : ℤ) + 2 ^ k * t) = (Ta a)^[k] ((r : ℤ) + 2 ^ k * t + 1) := by
      unfold mergedA
      refine Finset.filter_congr fun r _ => ?_
      simp only [pow_zero, one_mul]
    rw [← heq, card_mergedA_eq a ha (by omega)]
    field_simp
  rw [hfun]
  exact absorbed_tendsto_one_iff a ha ha3

#print axioms merged_fraction_tendsto_one_iff

end Coalescence.Mult
