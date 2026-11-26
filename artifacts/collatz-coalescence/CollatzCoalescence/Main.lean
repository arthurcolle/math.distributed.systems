import CollatzCoalescence.Assembly
import CollatzCoalescence.Potential
import CollatzCoalescence.Escape
import CollatzCoalescence.OffsetsChain
import CollatzCoalescence.Link
import CollatzCoalescence.Density
import CollatzCoalescence.Bridge

/-!
# Almost all consecutive integers have coalescing `3x+1` trajectories

`T x = x / 2` for even `x` and `(3x + 1) / 2` for odd `x`.

* `merged_proportion_tendsto`: for every pair state `s = (d, μ)`, the proportion of residues `p` mod
  `2^k` on whose class `T^[k] x = T^[k] (3^d x + μ)` holds identically tends to `1`.
* `offset_classes`: for every `m` and `ε > 0`, for all large `k` at least `(1 - ε) 2^k` residues
  `r` mod `2^k` satisfy `T^[k] (r + 2^k t) = T^[k] (r + 2^k t + m)` for every integer `t`.
* `coalescence_density_one`: for every `m`, the set of `n` with `Tn^[k] n = Tn^[k] (n + m)` for some
  `k` has natural density one.  For `m = 1` this is the statement that almost all consecutive
  integers have coalescing trajectories.

The mathematics is in `main.tex`.  Prior work: O. J. Said Duran, doi:10.5281/zenodo.23003524 (2026-09-27),
proves the `m = 1` density statement with a Lean formalization; this development is independent of it.
-/

namespace Coalescence
open Filter Topology Generic

/-- The pair chain is absorbed with probability tending to one, from every state. -/
theorem absorbed_tendsto (s : State) :
    Tendsto (fun k => pAbs step absorbed k s) atTop (𝓝 1) :=
  absorption_tendsto V_nonneg V_superharmonic escape offset_absorbable s

/-- Merged residue classes are counted by the chain. -/
theorem card_merged_eq : ∀ (k : ℕ) (s : State),
    ((merged s k).card : ℝ) = pAbs step absorbed k s * 2 ^ k
  | 0, s => by
      rw [card_merged_zero, pAbs_zero]
      split_ifs <;> simp
  | k + 1, s => by
      rw [card_merged_succ, Nat.cast_add, card_merged_eq k, card_merged_eq k, pAbs_succ]
      ring

theorem merged_proportion_tendsto (s : State) :
    Tendsto (fun k => ((merged s k).card : ℝ) / 2 ^ k) atTop (𝓝 1) := by
  have h : (fun k => ((merged s k).card : ℝ) / 2 ^ k) = fun k => pAbs step absorbed k s := by
    funext k
    rw [card_merged_eq]
    field_simp
  rw [h]
  exact absorbed_tendsto s

/-- For large `k`, all but an `ε` proportion of the residue classes mod `2^k` have merged. -/
theorem merged_card_ge (s : State) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (1 - ε) * (2 : ℝ) ^ k ≤ ((merged s k).card : ℝ) := by
  have h := absorbed_tendsto s
  rw [Metric.tendsto_atTop] at h
  obtain ⟨K, hK⟩ := h ε hε
  refine ⟨K, fun k hk => ?_⟩
  have h1 := hK k hk
  rw [Real.dist_eq, abs_lt] at h1
  rw [card_merged_eq]
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  nlinarith [h1.1]

open Classical in
/-- **Offsets.** For every `m` and `ε > 0`, for all large `k` at least `(1 - ε) 2^k` residues `r`
mod `2^k` satisfy `T^[k] (r + 2^k t) = T^[k] (r + 2^k t + m)` for every integer `t`. -/
theorem offset_classes (m : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (1 - ε) * (2 : ℝ) ^ k ≤
      (((Finset.range (2 ^ k)).filter fun r : ℕ =>
        ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + m)).card : ℝ) := by
  obtain ⟨K, hK⟩ := merged_card_ge ⟨0, m⟩ ε hε
  refine ⟨K, fun k hk => ?_⟩
  have h := hK k hk
  have heq : merged ⟨0, m⟩ k = (Finset.range (2 ^ k)).filter fun r : ℕ =>
      ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + m) := by
    unfold merged
    refine Finset.filter_congr fun r _ => ?_
    simp only [pow_zero, one_mul]
  rw [heq] at h
  exact h

open Classical in
/-- **Natural density one.** For every `m`, almost every `n` has `Tn^[k] n = Tn^[k] (n + m)` for
some `k`.  With `m = 1`: almost all consecutive integers have coalescing trajectories. -/
theorem coalescence_density_one (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (1 - ε) * (N : ℝ) ≤
      (((Finset.range N).filter fun n : ℕ => ∃ k : ℕ, Tn^[k] n = Tn^[k] (n + m)).card : ℝ) := by
  refine density_one_of_classes (fun n : ℕ => ∃ k : ℕ, Tn^[k] n = Tn^[k] (n + m)) ?_ ε hε
  intro δ hδ
  obtain ⟨K, hK⟩ := merged_card_ge ⟨0, (m : ℤ)⟩ δ hδ
  refine ⟨K, merged ⟨0, (m : ℤ)⟩ K, ?_, hK K le_rfl, ?_⟩
  · intro g hg
    unfold merged at hg
    exact Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  · intro n hn
    unfold merged at hn
    have h := (Finset.mem_filter.mp hn).2 ((n / 2 ^ K : ℕ) : ℤ)
    simp only [pow_zero, one_mul] at h
    have hn' : ((n % 2 ^ K : ℕ) : ℤ) + 2 ^ K * ((n / 2 ^ K : ℕ) : ℤ) = (n : ℤ) := by
      have := Nat.mod_add_div n (2 ^ K)
      exact_mod_cast this
    rw [hn'] at h
    exact ⟨K, Tn_iterate_eq_of_T K n m h⟩

#print axioms absorbed_tendsto
#print axioms merged_proportion_tendsto
#print axioms offset_classes
#print axioms coalescence_density_one

end Coalescence
