import Statement
import CollatzCoalescence

/-!
# The claimed theorems, proved

Each theorem has exactly the statement of its namesake in `Challenge.lean` and is obtained from the
library `CollatzCoalescence`, whose maps are definitionally the ones of `Statement.lean`.
-/

namespace Solution

theorem T_eq : Statement.T = Coalescence.T := rfl
theorem Tn_eq : Statement.Tn = _root_.Tn := rfl
theorem Cn_eq : Statement.Cn = Coalescence.Cn := rfl
theorem Ta_eq : Statement.Ta = Coalescence.Mult.Ta := rfl

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
  rw [T_eq]
  exact Coalescence.neighbour_merge_rate

open Classical in
/-- **Rate for every offset.** The same two-sided bound for the pair `x`, `x + m`, any `m ≠ 0`. -/
theorem offset_merge_rate (m : ℤ) (hm : m ≠ 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 1 ≤ k →
      c₁ * 2 ^ k / Real.sqrt k ≤
        (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, Statement.T^[k] ((r : ℤ) + 2 ^ k * t) = Statement.T^[k] ((r : ℤ) + 2 ^ k * t + m)).card : ℝ) ∧
      (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, Statement.T^[k] ((r : ℤ) + 2 ^ k * t) = Statement.T^[k] ((r : ℤ) + 2 ^ k * t + m)).card : ℝ) ≤
        c₂ * 2 ^ k / Real.sqrt k := by
  rw [T_eq]
  exact Coalescence.offset_merge_rate m hm

open Classical in
/-- **Rate, for integers.** For each `k ≥ 1` the `n` with `Tn^[k] n ≠ Tn^[k] (n + 1)` have lower and
upper natural density between `c₁ / √k` and `c₂ / √k`. -/
theorem unmerged_density_rate :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (c₁ / Real.sqrt k - ε) * (N : ℝ) ≤
          (((Finset.range N).filter fun n : ℕ => Statement.Tn^[k] n ≠ Statement.Tn^[k] (n + 1)).card : ℝ) ∧
        (((Finset.range N).filter fun n : ℕ => Statement.Tn^[k] n ≠ Statement.Tn^[k] (n + 1)).card : ℝ) ≤
          (c₂ / Real.sqrt k + ε) * (N : ℝ) := by
  rw [Tn_eq]
  exact Coalescence.unmerged_density_rate

open Classical in
/-- **Density one with the time bound** (`m = 1` is Gao's 1993 conjecture, first proved by
O. J. Said Duran): almost every `n` has `Cn^[j] n = Cn^[j] (n + m)` for some `j` with `2^j ≤ n`. -/
theorem coalescence_density_one_log (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (1 - ε) * (N : ℝ) ≤
      (((Finset.range N).filter fun n : ℕ =>
        ∃ j : ℕ, 2 ^ j ≤ n ∧ Statement.Cn^[j] n = Statement.Cn^[j] (n + m)).card : ℝ) := by
  rw [Cn_eq]
  exact Coalescence.coalescence_density_one_log m ε hε

/-- **Every offset merges** on a full residue class. -/
theorem every_offset_merges (m : ℕ) (hm : 0 < m) :
    ∃ k r : ℕ, ∀ q : ℕ, Statement.Tn^[k] (r + 2 ^ k * q) = Statement.Tn^[k] (r + m + 2 ^ k * q) := by
  rw [Tn_eq]
  exact _root_.every_offset_merges m hm

open Classical in
/-- **Exceptions to Gao's conjecture.** The number of `n < N` whose `3n+1` orbit does not meet that
of `n + 1` within `log₂ n` steps is of exact order `N / √(log₂ N)`. -/
theorem gao_exceptions_rate :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ N : ℕ, 4 ≤ N →
      c₁ * N / Real.sqrt (Nat.log 2 N) ≤
        (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Statement.Cn^[j] n = Statement.Cn^[j] (n + 1)).card : ℝ) ∧
      (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Statement.Cn^[j] n = Statement.Cn^[j] (n + 1)).card : ℝ) ≤
        c₂ * N / Real.sqrt (Nat.log 2 N) := by
  rw [Cn_eq]
  exact Coalescence.gao_exceptions_rate

open Classical in
/-- The same for the shortcut map: no meeting within `log₂ n` shortcut steps. -/
theorem gao_exceptions_rate_T :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ N : ℕ, 4 ≤ N →
      c₁ * N / Real.sqrt (Nat.log 2 N) ≤
        (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Statement.Tn^[k] n = Statement.Tn^[k] (n + 1)).card : ℝ) ∧
      (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Statement.Tn^[k] n = Statement.Tn^[k] (n + 1)).card : ℝ) ≤
        c₂ * N / Real.sqrt (Nat.log 2 N) := by
  rw [Tn_eq]
  exact Coalescence.gao_exceptions_rate_T

open Classical in
/-- **Saturation for every odd multiplier `a ≥ 5`.** For `x ↦ x/2`, `(a x + 1)/2` at most
`(1 - ε) 2^k` residue classes mod `2^k` have merged after `k` steps, for one `ε > 0` and every `k`. -/
theorem odd_merged_bounded (a : ℕ) (ha : a % 2 = 1) (ha5 : 5 ≤ a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ,
      (((Finset.range (2 ^ k)).filter fun r : ℕ =>
        ∀ t : ℤ, (Statement.Ta a)^[k] ((r : ℤ) + 2 ^ k * t) = (Statement.Ta a)^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ) ≤
        (1 - ε) * 2 ^ k := by
  rw [Ta_eq]
  exact Coalescence.Mult.odd_merged_bounded a ha ha5

open Classical in
/-- **The multiplier 3 is characterized by neighbour merging.** For odd `a ≥ 3` the proportion of
merged residue classes tends to `1` if and only if `a = 3`. -/
theorem merged_fraction_tendsto_one_iff (a : ℕ) (ha : a % 2 = 1) (ha3 : 3 ≤ a) :
    Filter.Tendsto (fun k : ℕ =>
        (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ∀ t : ℤ, (Statement.Ta a)^[k] ((r : ℤ) + 2 ^ k * t) = (Statement.Ta a)^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ)
          / 2 ^ k) Filter.atTop (nhds 1) ↔ a = 3 := by
  rw [Ta_eq]
  exact Coalescence.Mult.merged_fraction_tendsto_one_iff a ha ha3

#print axioms neighbour_merge_rate
#print axioms offset_merge_rate
#print axioms unmerged_density_rate
#print axioms coalescence_density_one_log
#print axioms every_offset_merges
#print axioms gao_exceptions_rate
#print axioms gao_exceptions_rate_T
#print axioms odd_merged_bounded
#print axioms merged_fraction_tendsto_one_iff

end Solution
