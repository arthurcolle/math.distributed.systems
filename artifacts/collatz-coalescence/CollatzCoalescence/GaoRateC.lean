import CollatzCoalescence.GaoRateT

/-!
# Exceptions to Gao's conjecture: the rate for the unaccelerated map

* `Tn_meet_of_Cn_meet`: inside the window `2^j ≤ n`, a meeting of the `3n+1` orbits of `n` and
  `n + 1` at time `j` gives a meeting of the shortcut orbits at a time `k ≤ j`.
* `gao_exceptions_rate`: the number of `n < N` whose `3n+1` orbit does not meet that of `n + 1`
  within `log₂ n` steps is of exact order `N / √(log₂ N)`.
-/

namespace Coalescence

/-- Number of odd terms among `x, Cn x, …, Cn^[j-1] x`. -/
def oddC : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, x => oddC j x + (if Cn^[j] x % 2 = 0 then 0 else 1)

theorem Cn_of_even {x : ℕ} (hx : x % 2 = 0) : Cn x = x / 2 := by
  unfold Cn
  rw [if_pos hx]

theorem Cn_of_odd {x : ℕ} (hx : ¬ x % 2 = 0) : Cn x = 3 * x + 1 := by
  unfold Cn
  rw [if_neg hx]

theorem Cn_two_mul (y : ℕ) : Cn (2 * y) = y := by
  rw [Cn_of_even (by omega)]
  omega

/-- **Size of the iterates.** `2^j Cn^[j] x = 6^a x + γ` with `a` the number of odd terms and
`2 γ ≤ (3^a - 1) 2^j`. -/
theorem Cn_iterate_size (j x : ℕ) :
    ∃ γ : ℕ, 2 ^ j * Cn^[j] x = 6 ^ oddC j x * x + γ ∧
      2 * γ + 2 ^ j ≤ 3 ^ oddC j x * 2 ^ j := by
  induction j with
  | zero => exact ⟨0, by simp [oddC], by simp [oddC]⟩
  | succ j ih =>
    obtain ⟨γ, h1, h2⟩ := ih
    rw [Function.iterate_succ_apply']
    by_cases hv : Cn^[j] x % 2 = 0
    · have ha : oddC (j + 1) x = oddC j x := by
        simp only [oddC, if_pos hv, add_zero]
      rw [ha, Cn_of_even hv]
      refine ⟨γ, ?_, ?_⟩
      · have e : 2 ^ (j + 1) * (Cn^[j] x / 2) = 2 ^ j * (2 * (Cn^[j] x / 2)) := by ring
        rw [e, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hv), h1]
      · have h4 : 2 ^ j ≤ 3 ^ oddC j x * 2 ^ j := Nat.le_mul_of_pos_left _ (by positivity)
        rw [pow_succ]
        nlinarith
    · have ha : oddC (j + 1) x = oddC j x + 1 := by
        simp only [oddC, if_neg hv]
      rw [ha, Cn_of_odd hv]
      refine ⟨6 * γ + 2 ^ (j + 1), ?_, ?_⟩
      · rw [pow_succ, pow_succ]
        nlinarith
      · rw [pow_succ, pow_succ]
        nlinarith

/-- **Equal odd counts.** Inside the window, a meeting forces the two orbits to have the same
number of odd terms. -/
theorem oddC_eq_of_meet (n j : ℕ) (hj : 2 ^ j ≤ n) (h : Cn^[j] n = Cn^[j] (n + 1)) :
    oddC j n = oddC j (n + 1) := by
  obtain ⟨γ, h1, h2⟩ := Cn_iterate_size j n
  obtain ⟨γ', h1', h2'⟩ := Cn_iterate_size j (n + 1)
  rw [← h, h1] at h1'
  have hP : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have hn1 : 1 ≤ n := hP.trans hj
  rcases lt_trichotomy (oddC j n) (oddC j (n + 1)) with hlt | heq | hgt
  · exfalso
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
    rw [hd] at h1'
    generalize oddC j n = a at h1' h2
    have hD : 1 ≤ 6 ^ d := Nat.one_le_pow _ _ (by norm_num)
    have e1 : 6 ^ a * (n + 1) * 6 ≤ 6 ^ (a + d + 1) * (n + 1) := by
      calc 6 ^ a * (n + 1) * 6 = 6 ^ a * 1 * 6 * (n + 1) := by ring
        _ ≤ 6 ^ a * 6 ^ d * 6 * (n + 1) := by gcongr
        _ = 6 ^ (a + d + 1) * (n + 1) := by ring
    have e2 : 3 ^ a * 2 ^ j ≤ 6 ^ a * n :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) a) hj
    nlinarith
  · exact heq
  · exfalso
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hgt
    rw [hd] at h1'
    generalize oddC j (n + 1) = a at h1' h2'
    have hD : 1 ≤ 6 ^ d := Nat.one_le_pow _ _ (by norm_num)
    have e1 : 6 ^ a * n * 6 ≤ 6 ^ (a + d + 1) * n := by
      calc 6 ^ a * n * 6 = 6 ^ a * 1 * 6 * n := by ring
        _ ≤ 6 ^ a * 6 ^ d * 6 * n := by gcongr
        _ = 6 ^ (a + d + 1) * n := by ring
    have e2 : 3 ^ a * 2 ^ j ≤ 6 ^ a * n :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) a) hj
    have e3 : 6 ^ a ≤ 6 ^ a * n := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith

/-- `oddCountN`, stepping at the end. -/
theorem oddCountN_succ' (k x : ℕ) :
    oddCountN (k + 1) x = oddCountN k x + (if Tn^[k] x % 2 = 0 then 0 else 1) := by
  induction k generalizing x with
  | zero =>
    show (if x % 2 = 0 then 0 else 1) + 0 = 0 + (if x % 2 = 0 then 0 else 1)
    rw [add_zero, zero_add]
  | succ k ih =>
    have h := ih (Tn x)
    have e1 : oddCountN (k + 1 + 1) x
        = (if x % 2 = 0 then 0 else 1) + oddCountN (k + 1) (Tn x) := rfl
    have e2 : oddCountN (k + 1) x = (if x % 2 = 0 then 0 else 1) + oddCountN k (Tn x) := rfl
    rw [e1, h, e2, Function.iterate_succ_apply, add_assoc]

/-- **Alignment of `Cn`-time and shortcut time.** After `j` steps of `Cn` the orbit is either at a
shortcut iterate (`e = 0`), or at twice a shortcut iterate, the halving that completes the last
odd shortcut step being still pending (`e = 1`). -/
theorem Cn_align (j x : ℕ) :
    ∃ k e : ℕ, j + e = k + oddCountN k x ∧ oddC j x = oddCountN k x ∧
      ((e = 0 ∧ Cn^[j] x = Tn^[k] x) ∨
        (e = 1 ∧ Cn^[j] x = 2 * Tn^[k] x ∧ 1 ≤ oddC j x)) := by
  induction j with
  | zero => exact ⟨0, 0, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | succ j ih =>
    obtain ⟨k, e, he, ha, hcase⟩ := ih
    rcases hcase with ⟨rfl, hv⟩ | ⟨rfl, hv, h1⟩
    · by_cases hy : Tn^[k] x % 2 = 0
      · have hk : oddCountN (k + 1) x = oddCountN k x := by
          rw [oddCountN_succ', if_pos hy, add_zero]
        have hc : oddC (j + 1) x = oddC j x := by
          simp only [oddC]
          rw [hv, if_pos hy, add_zero]
        refine ⟨k + 1, 0, by omega, by omega, Or.inl ⟨rfl, ?_⟩⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hv, Cn_of_even hy,
          Tn_of_even hy]
      · have hk : oddCountN (k + 1) x = oddCountN k x + 1 := by
          rw [oddCountN_succ', if_neg hy]
        have hc : oddC (j + 1) x = oddC j x + 1 := by
          simp only [oddC]
          rw [hv, if_neg hy]
        refine ⟨k + 1, 1, by omega, by omega, Or.inr ⟨rfl, ?_, by omega⟩⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hv, Cn_of_odd hy,
          Tn_of_odd (by omega)]
        omega
    · have hc : oddC (j + 1) x = oddC j x := by
        simp only [oddC]
        rw [hv, if_pos (by omega), add_zero]
      refine ⟨k, 0, by omega, by omega, Or.inl ⟨rfl, ?_⟩⟩
      rw [Function.iterate_succ_apply', hv, Cn_two_mul]

/-- Inside the window, a meeting of the `3n+1` orbits is a meeting of the shortcut orbits. -/
theorem Tn_meet_of_Cn_meet (n j : ℕ) (hj : 2 ^ j ≤ n) (h : Cn^[j] n = Cn^[j] (n + 1)) :
    ∃ k : ℕ, k ≤ j ∧ Tn^[k] n = Tn^[k] (n + 1) := by
  have ha := oddC_eq_of_meet n j hj h
  obtain ⟨k, e, he, hc, hcase⟩ := Cn_align j n
  obtain ⟨k', e', he', hc', hcase'⟩ := Cn_align j (n + 1)
  rcases hcase with ⟨rfl, hv⟩ | ⟨rfl, hv, h1⟩ <;>
    rcases hcase' with ⟨rfl, hv'⟩ | ⟨rfl, hv', h1'⟩
  · have hk : k = k' := by omega
    subst hk
    exact ⟨k, by omega, by rw [← hv, ← hv', h]⟩
  · have hk : k' = k + 1 := by omega
    subst hk
    refine ⟨k + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply' (f := Tn) k n, ← hv, h, hv', Tn_two_mul]
  · have hk : k = k' + 1 := by omega
    subst hk
    refine ⟨k' + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply' (f := Tn) k' (n + 1), ← hv', ← h, hv, Tn_two_mul]
  · have hk : k = k' := by omega
    subst hk
    refine ⟨k, by omega, ?_⟩
    have h2 : 2 * Tn^[k] n = 2 * Tn^[k] (n + 1) := by rw [← hv, ← hv', h]
    omega

open Classical in
/-- An exception for the shortcut map is an exception for the `3n+1` map. -/
theorem gao_exceptions_mono (N : ℕ) :
    ((Finset.range N).filter fun n : ℕ =>
        ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)).card ≤
      ((Finset.range N).filter fun n : ℕ =>
        ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card := by
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  refine ⟨hn.1, fun ⟨j, hj, hjeq⟩ => hn.2 ?_⟩
  obtain ⟨k, hk, hkeq⟩ := Tn_meet_of_Cn_meet n j hj hjeq
  exact ⟨k, (Nat.pow_le_pow_right (by norm_num) hk).trans hj, hkeq⟩

open Classical in
/-- An exception below `N` is below `4^K` or lies in an unmerged class mod `2^K`. -/
theorem gao_exceptions_count_le (K N : ℕ) :
    ((Finset.range N).filter fun n : ℕ =>
        ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card ≤
      4 ^ K + ((Finset.range (2 ^ K)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[K] ((r : ℤ) + 2 ^ K * t) = T^[K] ((r : ℤ) + 2 ^ K * t + 1)).card
        * (N / 2 ^ K + 1) := by
  have hsub : ((Finset.range N).filter fun n : ℕ =>
        ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)) ⊆
      Finset.range (4 ^ K) ∪ (Finset.range N).filter (fun n => n % 2 ^ K ∈
        (Finset.range (2 ^ K)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[K] ((r : ℤ) + 2 ^ K * t) = T^[K] ((r : ℤ) + 2 ^ K * t + 1)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_filter]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h4, hnU⟩ := hcon
    have h4' : 4 ^ K ≤ n := not_lt.mp h4
    have hlt : n % 2 ^ K < 2 ^ K := Nat.mod_lt _ (by positivity)
    have hall : ∀ t : ℤ, T^[K] (((n % 2 ^ K : ℕ) : ℤ) + 2 ^ K * t)
        = T^[K] (((n % 2 ^ K : ℕ) : ℤ) + 2 ^ K * t + 1) := by
      by_contra hne
      exact hnU ⟨Finset.mem_range.mp hn.1, hlt, hne⟩
    have hmem : n % 2 ^ K ∈ merged ⟨0, ((1 : ℕ) : ℤ)⟩ K := by
      unfold merged
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hlt, fun t => ?_⟩
      simp only [pow_zero, one_mul, Nat.cast_one]
      exact hall t
    obtain ⟨j, hj, hjeq⟩ := Cn_merge K n 1 hmem
    refine hn.2 ⟨j, ?_, hjeq⟩
    calc 2 ^ j ≤ 2 ^ (2 * K) := Nat.pow_le_pow_right (by norm_num) hj
      _ = 4 ^ K := by rw [pow_mul]; norm_num
      _ ≤ n := h4'
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_range]
  exact Nat.add_le_add_left (card_filter_mod_le (2 ^ K) _ N) _

theorem eight_mul_add_le_pow (K : ℕ) (hK : 1 ≤ K) : 8 * K + 8 ≤ 64 ^ K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K _ ih =>
    rw [pow_succ]
    omega

open Classical in
/-- **Upper bound.** -/
theorem gao_exceptions_upper :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ N : ℕ, 4 ≤ N →
      (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) ≤
        c₂ * N / Real.sqrt (Nat.log 2 N) := by
  obtain ⟨c₁, c₂, h1, h2, h⟩ := neighbour_merge_rate
  refine ⟨4 + 8 * c₂, by linarith, fun N hN => ?_⟩
  have hJ2 : 2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hN)
  have hJN : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  generalize Nat.log 2 N = J at hJ2 hJN
  have hJ1 : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast (by omega : 1 ≤ J)
  have hsJ : 0 < Real.sqrt J := Real.sqrt_pos.mpr (by linarith)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [le_div_iff₀ hsJ]
  have hcN : (((Finset.range N).filter fun n : ℕ =>
      ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) ≤ (N : ℝ) := by
    have h3 := Finset.card_filter_le (Finset.range N)
      (fun n : ℕ => ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1))
    rw [Finset.card_range] at h3
    exact_mod_cast h3
  by_cases hJ16 : J < 16
  · have hs4 : Real.sqrt J ≤ 4 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      have : (J : ℝ) ≤ 16 := by exact_mod_cast (by omega : J ≤ 16)
      linarith
    have hc0 : (0 : ℝ) ≤ (((Finset.range N).filter fun n : ℕ =>
      ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) := Nat.cast_nonneg _
    generalize (((Finset.range N).filter fun n : ℕ =>
      ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) = c at hcN hc0 ⊢
    have p1 : c * Real.sqrt J ≤ (N : ℝ) * 4 := mul_le_mul hcN hs4 hsJ.le hN0
    have p2 : 0 ≤ c₂ * (N : ℝ) := mul_nonneg h2.le hN0
    linarith
  · obtain ⟨K, hK⟩ : ∃ K, K = J / 8 := ⟨_, rfl⟩
    have hK2 : 2 ≤ K := by omega
    have hK8 : 8 * K ≤ J := by omega
    have hKJ : J < 8 * K + 8 := by omega
    have hnat := gao_exceptions_count_le K N
    have hU := (h K (by omega)).2
    have hreal : (((Finset.range N).filter fun n : ℕ =>
        ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) ≤
        (4 : ℝ) ^ K + (((Finset.range (2 ^ K)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[K] ((r : ℤ) + 2 ^ K * t) = T^[K] ((r : ℤ) + 2 ^ K * t + 1)).card : ℝ)
          * (((N / 2 ^ K : ℕ) : ℝ) + 1) := by
      exact_mod_cast hnat
    have hu0 : (0 : ℝ) ≤ (((Finset.range (2 ^ K)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[K] ((r : ℤ) + 2 ^ K * t) = T^[K] ((r : ℤ) + 2 ^ K * t + 1)).card : ℝ) :=
      Nat.cast_nonneg _
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
    have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr (by linarith)
    rw [le_div_iff₀ hsK] at hU
    -- `2^K q ≤ N` and `2^K ≤ N`
    have hdiv1 : (2 : ℝ) ^ K * ((N / 2 ^ K : ℕ) : ℝ) ≤ (N : ℝ) := by
      have hle : 2 ^ K * (N / 2 ^ K) ≤ N := Nat.mul_div_le N (2 ^ K)
      have hle' : ((2 ^ K * (N / 2 ^ K) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hle'
      exact hle'
    have hMN : (2 : ℝ) ^ K ≤ (N : ℝ) := by
      have hle : 2 ^ K ≤ N := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hJN
      exact_mod_cast hle
    -- `√J ≤ 4 √K`
    have hS : Real.sqrt J ≤ 4 * Real.sqrt K := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      have : (J : ℝ) ≤ 16 * (K : ℝ) := by exact_mod_cast (by omega : J ≤ 16 * K)
      linarith
    -- `4^K √J ≤ N`
    have h4 : (4 : ℝ) ^ K * Real.sqrt J ≤ (N : ℝ) := by
      have hSJ : Real.sqrt J ≤ (J : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by linarith, ?_⟩
        nlinarith
      have hJ64 : (J : ℝ) ≤ (64 : ℝ) ^ K := by
        have := eight_mul_add_le_pow K (by omega)
        exact_mod_cast (by omega : J ≤ 64 ^ K)
      have hpow : 4 ^ K * 64 ^ K ≤ N := by
        calc 4 ^ K * 64 ^ K = 2 ^ (8 * K) := by
              rw [← mul_pow, pow_mul]
              norm_num
          _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hK8
          _ ≤ N := hJN
      have hpow' : (4 : ℝ) ^ K * (64 : ℝ) ^ K ≤ (N : ℝ) := by exact_mod_cast hpow
      have h40 : (0 : ℝ) ≤ (4 : ℝ) ^ K := by positivity
      calc (4 : ℝ) ^ K * Real.sqrt J ≤ (4 : ℝ) ^ K * (64 : ℝ) ^ K :=
            mul_le_mul_of_nonneg_left (hSJ.trans hJ64) h40
        _ ≤ (N : ℝ) := hpow'
    have hq0 : (0 : ℝ) ≤ ((N / 2 ^ K : ℕ) : ℝ) := Nat.cast_nonneg _
    have hM : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
    generalize (((Finset.range N).filter fun n : ℕ =>
      ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) = c at hreal ⊢
    generalize (((Finset.range (2 ^ K)).filter fun r : ℕ =>
      ¬ ∀ t : ℤ, T^[K] ((r : ℤ) + 2 ^ K * t) = T^[K] ((r : ℤ) + 2 ^ K * t + 1)).card : ℝ) = u
      at hreal hU hu0
    generalize ((N / 2 ^ K : ℕ) : ℝ) = q at hreal hdiv1 hq0
    generalize (2 : ℝ) ^ K = M at hU hdiv1 hMN hM
    generalize (4 : ℝ) ^ K = F at hreal h4
    generalize Real.sqrt K = s at hU hS hsK
    generalize Real.sqrt J = S at hS h4 hsJ ⊢
    generalize (N : ℝ) = n at hreal hdiv1 hMN h4 hN0 ⊢
    have p1 : c * S ≤ (F + u * (q + 1)) * S := mul_le_mul_of_nonneg_right hreal hsJ.le
    have p2 : u * (q + 1) * S ≤ u * (q + 1) * (4 * s) :=
      mul_le_mul_of_nonneg_left hS (mul_nonneg hu0 (by linarith))
    have p3 : u * s * (q + 1) ≤ c₂ * M * (q + 1) :=
      mul_le_mul_of_nonneg_right hU (by linarith)
    have p4 : c₂ * (M * q + M) ≤ c₂ * (2 * n) :=
      mul_le_mul_of_nonneg_left (by linarith) h2.le
    nlinarith

open Classical in
/-- The rate, given the lower bound for the shortcut map. -/
theorem gao_exceptions_rate_of_T
    (hT : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ N : ℕ, 4 ≤ N →
      c₁ * N / Real.sqrt (Nat.log 2 N) ≤
        (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)).card : ℝ)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ N : ℕ, 4 ≤ N →
      c₁ * N / Real.sqrt (Nat.log 2 N) ≤
        (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) ∧
      (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) ≤
        c₂ * N / Real.sqrt (Nat.log 2 N) := by
  obtain ⟨c₁, h1, hlo⟩ := hT
  obtain ⟨c₂, h2, hhi⟩ := gao_exceptions_upper
  refine ⟨c₁, c₂, h1, h2, fun N hN => ⟨(hlo N hN).trans ?_, hhi N hN⟩⟩
  exact_mod_cast gao_exceptions_mono N

open Classical in
/-- **Exceptions to Gao's conjecture.** The number of `n < N` whose `3n+1` orbit does not meet that
of `n + 1` within `log₂ n` steps is of exact order `N / √(log₂ N)`. -/
theorem gao_exceptions_rate :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ N : ℕ, 4 ≤ N →
      c₁ * N / Real.sqrt (Nat.log 2 N) ≤
        (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) ∧
      (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ j : ℕ, 2 ^ j ≤ n ∧ Cn^[j] n = Cn^[j] (n + 1)).card : ℝ) ≤
        c₂ * N / Real.sqrt (Nat.log 2 N) := by
  obtain ⟨c₁, c₂, h1, h2, h⟩ := gao_exceptions_rate_T
  exact gao_exceptions_rate_of_T ⟨c₁, h1, fun N hN => (h N hN).1⟩

#print axioms Tn_meet_of_Cn_meet
#print axioms gao_exceptions_rate

end Coalescence
