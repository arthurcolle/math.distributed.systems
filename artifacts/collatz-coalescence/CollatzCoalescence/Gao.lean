import CollatzCoalescence.Main

/-!
# Gao's conjecture

The density-one coalescence theorem for the unaccelerated `3n+1` map `Cn`, with the coalescence
time bounded by `log₂ n`.

* `Cn_iterate_eq_Tn`: `k` steps of the shortcut map `Tn` are `k + oddCountN k x` steps of `Cn`.
* `oddCount_eq_of_class`: on a merged class the two orbits have the same number of odd terms.
* `coalescence_density_one_log`: for every `m`, almost every `n` has `Cn^[j] n = Cn^[j] (n + m)`
  for some `j` with `2^j ≤ n`.
* `gao_conjecture`: the case `m = 1`.
-/

namespace Coalescence

/-- The 3n+1 map without the shortcut. -/
def Cn (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- Number of odd terms among `x, Tn x, …, Tn^[k-1] x`. -/
def oddCountN : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x => (if x % 2 = 0 then 0 else 1) + oddCountN k (Tn x)

theorem oddCountN_le (k x : ℕ) : oddCountN k x ≤ k := by
  induction k generalizing x with
  | zero => simp [oddCountN]
  | succ k ih =>
    have h := ih (Tn x)
    simp only [oddCountN]
    split_ifs <;> omega

theorem oddCountN_eq (k x : ℕ) : oddCountN k x = oddCount k (x : ℤ) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [oddCountN, oddCount]
    rw [T_natCast, ih]
    by_cases hx : x % 2 = 0
    · have hx' : (x : ℤ) % 2 = 0 := by omega
      rw [if_pos hx, if_pos hx']
    · have hx' : ¬ (x : ℤ) % 2 = 0 := by omega
      rw [if_neg hx, if_neg hx']

/-- `k` steps of the shortcut map are `k + oddCountN k x` steps of the unaccelerated map. -/
theorem Cn_iterate_eq_Tn (k x : ℕ) : Cn^[k + oddCountN k x] x = Tn^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    by_cases hx : x % 2 = 0
    · have hC : Cn x = Tn x := by
        unfold Cn Tn
        rw [if_pos hx, if_pos hx]
      have e : k + 1 + oddCountN (k + 1) x = (k + oddCountN k (Tn x)) + 1 := by
        simp only [oddCountN, if_pos hx]
        omega
      rw [e, Function.iterate_succ_apply, Function.iterate_succ_apply, hC, ih]
    · have h1 : Cn x = 3 * x + 1 := by
        unfold Cn
        rw [if_neg hx]
      have h2 : Cn (3 * x + 1) = (3 * x + 1) / 2 := by
        unfold Cn
        rw [if_pos (by omega)]
      have h3 : Tn x = (3 * x + 1) / 2 := by
        unfold Tn
        rw [if_neg hx]
      have e : k + 1 + oddCountN (k + 1) x = (k + oddCountN k (Tn x)) + 1 + 1 := by
        simp only [oddCountN, if_neg hx]
        omega
      rw [e, Function.iterate_succ_apply, Function.iterate_succ_apply, h1, h2, ← h3,
        Function.iterate_succ_apply, ih]

/-- On a class mod `2^k` where the orbits of `x` and `x + m` have merged after `k` steps of `T`,
the two orbits have the same number of odd terms. -/
theorem oddCount_eq_of_class (k : ℕ) (y m : ℤ)
    (H : ∀ t : ℤ, T^[k] (y + 2 ^ k * t) = T^[k] (y + 2 ^ k * t + m)) :
    oddCount k y = oddCount k (y + m) := by
  have h0 := H 0
  have h1 := H 1
  have e : y + 2 ^ k * 1 + m = (y + m) + 2 ^ k * 1 := by ring
  rw [e, T_iterate_add, T_iterate_add] at h1
  simp only [mul_zero, add_zero] at h0
  have h3 : (3 : ℤ) ^ oddCount k y = 3 ^ oddCount k (y + m) := by
    linear_combination h1 - h0
  exact Int.pow_right_injective (by norm_num) h3

open Classical in
/-- Membership of `n % 2^K` in the merged set gives the class statement based at `n`. -/
theorem merged_class (K n m : ℕ) (hn : n % 2 ^ K ∈ merged ⟨0, (m : ℤ)⟩ K) :
    ∀ t : ℤ, T^[K] ((n : ℤ) + 2 ^ K * t) = T^[K] ((n : ℤ) + 2 ^ K * t + m) := by
  intro t
  unfold merged at hn
  have h := (Finset.mem_filter.mp hn).2 (((n / 2 ^ K : ℕ) : ℤ) + t)
  simp only [pow_zero, one_mul] at h
  have h2 : ((n % 2 ^ K : ℕ) : ℤ) + 2 ^ K * ((n / 2 ^ K : ℕ) : ℤ) = (n : ℤ) := by
    have := Nat.mod_add_div n (2 ^ K)
    exact_mod_cast this
  have hn' : ((n % 2 ^ K : ℕ) : ℤ) + 2 ^ K * (((n / 2 ^ K : ℕ) : ℤ) + t)
      = (n : ℤ) + 2 ^ K * t := by
    linear_combination h2
  rw [hn'] at h
  exact h

/-- On a merged class the unaccelerated orbits of `n` and `n + m` meet within `2K` steps. -/
theorem Cn_merge (K n m : ℕ) (hn : n % 2 ^ K ∈ merged ⟨0, (m : ℤ)⟩ K) :
    ∃ j : ℕ, j ≤ 2 * K ∧ Cn^[j] n = Cn^[j] (n + m) := by
  have H := merged_class K n m hn
  have hT : Tn^[K] n = Tn^[K] (n + m) := by
    have h := H 0
    simp only [mul_zero, add_zero] at h
    exact Tn_iterate_eq_of_T K n m h
  have hodd : oddCountN K n = oddCountN K (n + m) := by
    rw [oddCountN_eq, oddCountN_eq, oddCount_eq_of_class K n m H]
    push_cast
    rfl
  refine ⟨K + oddCountN K n, ?_, ?_⟩
  · have := oddCountN_le K n
    omega
  · calc Cn^[K + oddCountN K n] n = Tn^[K] n := Cn_iterate_eq_Tn K n
      _ = Tn^[K] (n + m) := hT
      _ = Cn^[K + oddCountN K (n + m)] (n + m) := (Cn_iterate_eq_Tn K (n + m)).symm
      _ = Cn^[K + oddCountN K n] (n + m) := by rw [hodd]

/-- Counting on residue classes, allowing the property to fail below a threshold `B`. -/
theorem card_filter_ge_of_classes (P : ℕ → Prop) [DecidablePred P] (M B : ℕ) (hM : 0 < M)
    (G : Finset ℕ) (hG : ∀ g ∈ G, g < M) (hP : ∀ n : ℕ, B ≤ n → n % M ∈ G → P n) (N : ℕ) :
    G.card * (N / M) ≤ ((Finset.range N).filter P).card + B := by
  have hsub : ((Finset.range N).filter (fun n => n % M ∈ G)) \ Finset.range B ⊆
      (Finset.range N).filter P := by
    intro n hn
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Finset.mem_range, not_lt] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hn.1.1, hP n hn.2 hn.1.2⟩
  have h1 := card_filter_mod_ge M hM G hG N
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.le_card_sdiff (Finset.range B)
    ((Finset.range N).filter (fun n => n % M ∈ G))
  rw [Finset.card_range] at h3
  omega

open Classical in
/-- Density one, with the unaccelerated map and the time bound `j ≤ log₂ n` (written `2^j ≤ n`). -/
theorem coalescence_density_one_log (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (1 - ε) * (N : ℝ) ≤
      (((Finset.range N).filter fun n : ℕ =>
        ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + m)).card : ℝ) := by
  obtain ⟨K, hK⟩ := merged_card_ge ⟨0, (m : ℤ)⟩ (ε / 2) (by positivity)
  have hcard := hK K le_rfl
  have hG : ∀ g ∈ merged ⟨0, (m : ℤ)⟩ K, g < 2 ^ K := by
    intro g hg
    unfold merged at hg
    exact Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  have hP : ∀ n : ℕ, 4 ^ K ≤ n → n % 2 ^ K ∈ merged ⟨0, (m : ℤ)⟩ K →
      ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + m) := by
    intro n hB hn
    obtain ⟨j, hj, hjeq⟩ := Cn_merge K n m hn
    refine ⟨j, ?_, hjeq⟩
    calc 2 ^ j ≤ 2 ^ (2 * K) := Nat.pow_le_pow_right (by norm_num) hj
      _ = 4 ^ K := by rw [pow_mul]; norm_num
      _ ≤ n := hB
  refine ⟨⌈2 * ((2 : ℝ) ^ K + 4 ^ K) / ε⌉₊, fun N hN => ?_⟩
  by_cases h1 : 1 ≤ ε
  · have hle : (1 - ε) * (N : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg N)
    exact hle.trans (Nat.cast_nonneg _)
  · have h1' : ε < 1 := lt_of_not_ge h1
    have hNreal : 2 * ((2 : ℝ) ^ K + 4 ^ K) / ε ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hN)
    have hN2 : 2 * ((2 : ℝ) ^ K + 4 ^ K) ≤ ε * N := by
      rw [div_le_iff₀ hε] at hNreal
      linarith
    have hnat := card_filter_ge_of_classes
      (fun n : ℕ => ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + m))
      (2 ^ K) (4 ^ K) (by positivity) (merged ⟨0, (m : ℤ)⟩ K) hG hP N
    have hreal : ((merged ⟨0, (m : ℤ)⟩ K).card : ℝ) * ((N / 2 ^ K : ℕ) : ℝ) ≤
        (((Finset.range N).filter fun n : ℕ =>
          ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + m)).card : ℝ) + (4 : ℝ) ^ K := by
      exact_mod_cast hnat
    have hdiv : (N : ℝ) ≤ (2 : ℝ) ^ K * ((N / 2 ^ K : ℕ) : ℝ) + (2 : ℝ) ^ K := by
      have hlt : N < 2 ^ K * (N / 2 ^ K + 1) := Nat.lt_mul_div_succ N (by positivity)
      have hlt' : (N : ℝ) < ((2 ^ K * (N / 2 ^ K + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] at hlt'
      linarith
    have hq0 : (0 : ℝ) ≤ ((N / 2 ^ K : ℕ) : ℝ) := Nat.cast_nonneg _
    generalize ((N / 2 ^ K : ℕ) : ℝ) = q at hreal hdiv hq0
    generalize (((Finset.range N).filter fun n : ℕ =>
      ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + m)).card : ℝ) = c at hreal ⊢
    generalize ((merged ⟨0, (m : ℤ)⟩ K).card : ℝ) = g at hreal hcard
    have hM : 0 < (2 : ℝ) ^ K := by positivity
    have hc : 0 ≤ 1 - ε / 2 := by linarith
    have hstep1 : (1 - ε / 2) * ((N : ℝ) - (2 : ℝ) ^ K) ≤ (1 - ε / 2) * ((2 : ℝ) ^ K * q) :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    have hstep2 : (1 - ε / 2) * (2 : ℝ) ^ K * q ≤ g * q :=
      mul_le_mul_of_nonneg_right hcard hq0
    have hεM : 0 ≤ ε * (2 : ℝ) ^ K := by positivity
    nlinarith

open Classical in
/-- Gao's conjecture (Discrete Math. 112 (1993)), in the form recorded by Lagarias: the case `m = 1`.
First proved, with a Lean formalization, by O. J. Said Duran (Zenodo, 2026-09-27,
doi:10.5281/zenodo.23003524); this is an independent proof found without knowledge of that work. -/
theorem gao_conjecture (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (1 - ε) * (N : ℝ) ≤
      (((Finset.range N).filter fun n : ℕ =>
        ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) :=
  coalescence_density_one_log 1 ε hε

#print axioms Cn_iterate_eq_Tn
#print axioms coalescence_density_one_log
#print axioms gao_conjecture

end Coalescence
