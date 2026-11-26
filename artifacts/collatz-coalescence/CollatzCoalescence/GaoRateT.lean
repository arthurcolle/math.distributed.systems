import CollatzCoalescence.RateDensity

/-!
# Exceptions to Gao's conjecture, shortcut form: exact order `N / √(log₂ N)`

* `class_merged_of_meet`: there is no accidental meeting inside the window.  If `2^k ≤ n` and
  `Tn^[k] n = Tn^[k] (n + 1)`, then the whole class of `n` mod `2^k` has merged at time `k`.
* `gao_exceptions_rate_T`: the number of `n < N` whose shortcut orbit does not meet that of `n + 1`
  within `log₂ n` steps lies between `c₁ N / √(log₂ N)` and `c₂ N / √(log₂ N)`.

The first statement rests on the size bounds
`3^a x ≤ 2^k Tn^[k] x ≤ 3^a x + (3^a - 2^a) 2^(k-a)`, `a = oddCountN k x`, which force the two
orbits to have the same number of odd terms.
-/

namespace Coalescence

/-- Lower size bound: `3^a x ≤ 2^k Tn^[k] x`, where `a` is the number of odd terms. -/
theorem three_pow_mul_le_iterate (k x : ℕ) : 3 ^ oddCountN k x * x ≤ 2 ^ k * Tn^[k] x := by
  induction k generalizing x with
  | zero => simp [oddCountN]
  | succ k ih =>
    have h := ih (Tn x)
    rw [Function.iterate_succ_apply]
    by_cases hx : x % 2 = 0
    · have hT : x = 2 * Tn x := by rw [Tn_of_even hx]; omega
      have ho : oddCountN (k + 1) x = oddCountN k (Tn x) := by
        simp only [oddCountN, if_pos hx, zero_add]
      rw [ho, pow_succ]
      generalize Tn^[k] (Tn x) = V at h ⊢
      generalize oddCountN k (Tn x) = a at h ⊢
      generalize Tn x = y at h hT ⊢
      subst hT
      calc 3 ^ a * (2 * y) = 2 * (3 ^ a * y) := by ring
        _ ≤ 2 * (2 ^ k * V) := Nat.mul_le_mul_left 2 h
        _ = 2 ^ k * 2 * V := by ring
    · have hx1 : x % 2 = 1 := by omega
      have hT : 2 * Tn x = 3 * x + 1 := by rw [Tn_of_odd hx1]; omega
      have ho : oddCountN (k + 1) x = oddCountN k (Tn x) + 1 := by
        simp only [oddCountN, if_neg hx]
        omega
      rw [ho, pow_succ, pow_succ]
      generalize Tn^[k] (Tn x) = V at h ⊢
      generalize oddCountN k (Tn x) = a at h ⊢
      generalize Tn x = y at h hT ⊢
      calc 3 ^ a * 3 * x ≤ 3 ^ a * (3 * x + 1) := by
            rw [mul_assoc]
            exact Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (3 ^ a * y) := by rw [← hT]; ring
        _ ≤ 2 * (2 ^ k * V) := Nat.mul_le_mul_left 2 h
        _ = 2 ^ k * 2 * V := by ring

/-- Upper size bound: `2^k Tn^[k] x ≤ 3^a x + (3^a - 2^a) 2^(k-a)`, cleared of subtractions by
multiplying through by `2^a`. -/
theorem two_pow_mul_iterate_le (k x : ℕ) :
    2 ^ oddCountN k x * (2 ^ k * Tn^[k] x) + 2 ^ oddCountN k x * 2 ^ k
      ≤ 3 ^ oddCountN k x * (2 ^ oddCountN k x * x) + 3 ^ oddCountN k x * 2 ^ k := by
  induction k generalizing x with
  | zero => simp [oddCountN]
  | succ k ih =>
    have h := ih (Tn x)
    have hAP : 2 ^ oddCountN k (Tn x) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (oddCountN_le k (Tn x))
    rw [Function.iterate_succ_apply]
    by_cases hx : x % 2 = 0
    · have hT : x = 2 * Tn x := by rw [Tn_of_even hx]; omega
      have ho : oddCountN (k + 1) x = oddCountN k (Tn x) := by
        simp only [oddCountN, if_pos hx, zero_add]
      rw [ho, pow_succ]
      generalize Tn^[k] (Tn x) = V at h ⊢
      generalize oddCountN k (Tn x) = a at h hAP ⊢
      generalize Tn x = y at h hT ⊢
      subst hT
      generalize (2 : ℕ) ^ a = A at h hAP ⊢
      generalize (3 : ℕ) ^ a = B at h ⊢
      generalize (2 : ℕ) ^ k = P at h hAP ⊢
      nlinarith [h]
    · have hx1 : x % 2 = 1 := by omega
      have hT : 2 * Tn x = 3 * x + 1 := by rw [Tn_of_odd hx1]; omega
      have ho : oddCountN (k + 1) x = oddCountN k (Tn x) + 1 := by
        simp only [oddCountN, if_neg hx]
        omega
      rw [ho, pow_succ, pow_succ, pow_succ]
      generalize Tn^[k] (Tn x) = V at h ⊢
      generalize oddCountN k (Tn x) = a at h hAP ⊢
      generalize Tn x = y at h hT ⊢
      generalize (2 : ℕ) ^ a = A at h hAP ⊢
      generalize (3 : ℕ) ^ a = B at h ⊢
      generalize (2 : ℕ) ^ k = P at h hAP ⊢
      have hBA : B * A ≤ B * P := Nat.mul_le_mul_left B hAP
      have hy : B * A * (2 * y) = B * A * (3 * x + 1) := by rw [hT]
      nlinarith [h, hBA, hy]

/-- If the orbits of `n` and `n + 1` agree at a time `k` with `2^k ≤ n`, they have the same number
of odd terms up to time `k`. -/
theorem oddCountN_eq_of_meet (n k : ℕ) (hk : 2 ^ k ≤ n) (h : Tn^[k] n = Tn^[k] (n + 1)) :
    oddCountN k n = oddCountN k (n + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rfl
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkpos
  have L1 := three_pow_mul_le_iterate k n
  have U1 := two_pow_mul_iterate_le k n
  have L2 := three_pow_mul_le_iterate k (n + 1)
  have U2 := two_pow_mul_iterate_le k (n + 1)
  rw [← h] at L2 U2
  generalize Tn^[k] n = V at L1 U1 L2 U2
  generalize oddCountN k n = a at L1 U1 ⊢
  generalize oddCountN k (n + 1) = b at L2 U2 ⊢
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    have h3 : 3 * 3 ^ a ≤ 3 ^ b := by
      calc 3 * 3 ^ a = 3 ^ (a + 1) := by ring
        _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hab
    have hA : 0 < 2 ^ a := by positivity
    have hB : 0 < 3 ^ a := by positivity
    have key : 3 ^ a * (3 * (2 ^ a * (n + 1))) ≤ 3 ^ a * (2 ^ a * n + 2 ^ k) := by
      calc 3 ^ a * (3 * (2 ^ a * (n + 1))) = (3 * 3 ^ a) * (2 ^ a * (n + 1)) := by ring
        _ ≤ 3 ^ b * (2 ^ a * (n + 1)) := Nat.mul_le_mul_right _ h3
        _ = 2 ^ a * (3 ^ b * (n + 1)) := by ring
        _ ≤ 2 ^ a * (2 ^ k * V) := Nat.mul_le_mul_left _ L2
        _ ≤ 3 ^ a * (2 ^ a * n) + 3 ^ a * 2 ^ k := by omega
        _ = 3 ^ a * (2 ^ a * n + 2 ^ k) := by ring
    have key' := Nat.le_of_mul_le_mul_left key hB
    have hn : n ≤ 2 ^ a * n := Nat.le_mul_of_pos_left n hA
    have e : 2 ^ a * (n + 1) = 2 ^ a * n + 2 ^ a := by ring
    rw [e] at key'
    generalize 2 ^ a * n = X at key' hn
    omega
  · exact hab
  · exfalso
    have h3 : 3 * 3 ^ b ≤ 3 ^ a := by
      calc 3 * 3 ^ b = 3 ^ (b + 1) := by ring
        _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) hab
    have hA : 0 < 2 ^ b := by positivity
    have hB : 0 < 3 ^ b := by positivity
    have key : 3 ^ b * (3 * (2 ^ b * n)) ≤ 3 ^ b * (2 ^ b * (n + 1) + 2 ^ k) := by
      calc 3 ^ b * (3 * (2 ^ b * n)) = (3 * 3 ^ b) * (2 ^ b * n) := by ring
        _ ≤ 3 ^ a * (2 ^ b * n) := Nat.mul_le_mul_right _ h3
        _ = 2 ^ b * (3 ^ a * n) := by ring
        _ ≤ 2 ^ b * (2 ^ k * V) := Nat.mul_le_mul_left _ L1
        _ ≤ 3 ^ b * (2 ^ b * (n + 1)) + 3 ^ b * 2 ^ k := by omega
        _ = 3 ^ b * (2 ^ b * (n + 1) + 2 ^ k) := by ring
    have key' := Nat.le_of_mul_le_mul_left key hB
    have hn : n ≤ 2 ^ b * n := Nat.le_mul_of_pos_left n hA
    have hn2 : 2 ^ b * 2 ≤ 2 ^ b * n := Nat.mul_le_mul_left _ (h2k.trans hk)
    have e : 2 ^ b * (n + 1) = 2 ^ b * n + 2 ^ b := by ring
    rw [e] at key'
    generalize 2 ^ b * n = X at key' hn hn2
    omega

/-- No accidental meeting inside the window: if `2^k ≤ n` and the shortcut orbits of `n` and `n + 1`
agree at time `k`, then the whole residue class of `n` mod `2^k` has merged at time `k`. -/
theorem class_merged_of_meet (n k : ℕ) (hk : 2 ^ k ≤ n) (h : Tn^[k] n = Tn^[k] (n + 1)) :
    ∀ t : ℤ, T^[k] ((n : ℤ) + 2 ^ k * t) = T^[k] ((n : ℤ) + 2 ^ k * t + 1) := by
  intro t
  have ho := oddCountN_eq_of_meet n k hk h
  rw [oddCountN_eq, oddCountN_eq] at ho
  have e : (n : ℤ) + 2 ^ k * t + 1 = ((n + 1 : ℕ) : ℤ) + 2 ^ k * t := by push_cast; ring
  rw [e, T_iterate_add, T_iterate_add, ← ho, T_iterate_natCast, T_iterate_natCast, h]

/-- A class merged at time `k` stays merged, as a class mod `2^J`, at every later time `J`. -/
theorem class_merged_mono (x : ℤ) (k J : ℕ) (hkJ : k ≤ J)
    (H : ∀ t : ℤ, T^[k] (x + 2 ^ k * t) = T^[k] (x + 2 ^ k * t + 1)) :
    ∀ t : ℤ, T^[J] (x + 2 ^ J * t) = T^[J] (x + 2 ^ J * t + 1) := by
  intro t
  obtain ⟨d, rfl⟩ : ∃ d, J = d + k := ⟨J - k, by omega⟩
  have e : x + 2 ^ (d + k) * t = x + 2 ^ k * (2 ^ d * t) := by ring
  rw [e, Function.iterate_add_apply, Function.iterate_add_apply, H]

/-- A representative `r < 2^J` of a class unmerged at time `J` is an exception. -/
theorem exception_of_unmerged (J r : ℕ) (hr : r < 2 ^ J)
    (hU : ¬ ∀ t : ℤ, T^[J] ((r : ℤ) + 2 ^ J * t) = T^[J] ((r : ℤ) + 2 ^ J * t + 1)) :
    ¬ ∃ k : ℕ, 2 ^ k ≤ r ∧ Tn^[k] r = Tn^[k] (r + 1) := by
  rintro ⟨k, hk, hmeet⟩
  apply hU
  have hkJ : k ≤ J := by
    have hlt : 2 ^ k < 2 ^ J := lt_of_le_of_lt hk hr
    exact le_of_lt ((Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt)
  exact class_merged_mono r k J hkJ (class_merged_of_meet r k hk hmeet)

/-- An exception `n ≥ 2^k` lies in a class unmerged at time `k`. -/
theorem unmerged_of_exception (k n : ℕ) (hk : 2 ^ k ≤ n)
    (hE : ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)) :
    ¬ ∀ t : ℤ, T^[k] (((n % 2 ^ k : ℕ) : ℤ) + 2 ^ k * t)
      = T^[k] (((n % 2 ^ k : ℕ) : ℤ) + 2 ^ k * t + 1) := by
  intro H
  apply hE
  refine ⟨k, hk, Tn_iterate_eq_of_T k n 1 ?_⟩
  have h := H ((n / 2 ^ k : ℕ) : ℤ)
  have d : ((n % 2 ^ k : ℕ) : ℤ) + 2 ^ k * ((n / 2 ^ k : ℕ) : ℤ) = (n : ℤ) := by
    have := Nat.mod_add_div n (2 ^ k)
    exact_mod_cast this
  rw [d] at h
  rw [Nat.cast_one]
  exact h

/-- Counting, lower bound: representatives below `M ≤ N` with `P` are among the `n < N` with `E`. -/
theorem card_filter_le_card_filter_of_imp (P E : ℕ → Prop) [DecidablePred P] [DecidablePred E]
    (M N : ℕ) (hMN : M ≤ N) (h : ∀ r : ℕ, r < M → P r → E r) :
    ((Finset.range M).filter P).card ≤ ((Finset.range N).filter E).card := by
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_filter, Finset.mem_range] at hr ⊢
  exact ⟨lt_of_lt_of_le hr.1 hMN, h r hr.1 hr.2⟩

/-- Counting, upper bound: if every `n ≥ m` with `E` reduces mod `m` into the residues with `P`,
then at most `m + #P * (N / m + 1)` of the `n < N` have `E`. -/
theorem card_filter_le_of_residues (P E : ℕ → Prop) [DecidablePred P] [DecidablePred E]
    (m N : ℕ) (hm : 0 < m) (h : ∀ n : ℕ, m ≤ n → E n → P (n % m)) :
    ((Finset.range N).filter E).card
      ≤ m + ((Finset.range m).filter P).card * (N / m + 1) := by
  have hsub : (Finset.range N).filter E ⊆
      Finset.range m ∪ (Finset.range N).filter (fun n => n % m ∈ (Finset.range m).filter P) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_filter, Finset.mem_range,
      Finset.mem_filter, Finset.mem_range]
    by_cases hnm : n < m
    · exact Or.inl hnm
    · exact Or.inr ⟨hn.1, Nat.mod_lt _ hm, h n (not_lt.mp hnm) hn.2⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.range m)
    ((Finset.range N).filter (fun n => n % m ∈ (Finset.range m).filter P))
  have h3 := card_filter_mod_le m ((Finset.range m).filter P) N
  rw [Finset.card_range] at h2
  omega

open Classical in
/-- **Exceptions to Gao's conjecture, shortcut form.** The number of `n < N` whose orbit does not
meet that of `n + 1` within `log₂ n` shortcut steps is of exact order `N / √(log₂ N)`. -/
theorem gao_exceptions_rate_T :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ N : ℕ, 4 ≤ N →
      c₁ * N / Real.sqrt (Nat.log 2 N) ≤
        (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)).card : ℝ) ∧
      (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)).card : ℝ) ≤
        c₂ * N / Real.sqrt (Nat.log 2 N) := by
  obtain ⟨c₁, c₂, h1, h2, hrate⟩ := neighbour_merge_rate
  refine ⟨c₁ / 2, 3 + 6 * c₂, by positivity, by positivity, fun N hN => ?_⟩
  have hN0 : N ≠ 0 := by omega
  have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
  have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  generalize Nat.log 2 N = J at hpow hlt ⊢
  have hJ2 : 2 ≤ J := by
    by_contra hcon
    have hle : 2 ^ (J + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast (by omega : 0 < J)
  have hsJ : 0 < Real.sqrt (J : ℝ) := Real.sqrt_pos.mpr hJpos
  have hNr0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  constructor
  · -- lower bound: unmerged representatives below `2^J` are exceptions
    have hlo := (hrate J (by omega)).1
    have hge := card_filter_le_card_filter_of_imp
      (fun r : ℕ => ¬ ∀ t : ℤ, T^[J] ((r : ℤ) + 2 ^ J * t) = T^[J] ((r : ℤ) + 2 ^ J * t + 1))
      (fun n : ℕ => ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)) (2 ^ J) N hpow
      (fun r hr hU => exception_of_unmerged J r hr hU)
    have hNle : (N : ℝ) ≤ 2 * (2 : ℝ) ^ J := by
      have hnat : N ≤ 2 * 2 ^ J := by
        rw [pow_succ] at hlt
        omega
      exact_mod_cast hnat
    refine le_trans ?_ (le_trans hlo (by exact_mod_cast hge))
    apply div_le_div_of_nonneg_right _ hsJ.le
    nlinarith
  · -- upper bound
    by_cases hJ8 : J < 8
    · have hcard : (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)).card : ℝ) ≤ (N : ℝ) := by
        have hnat := Finset.card_filter_le (Finset.range N)
          (fun n : ℕ => ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1))
        rw [Finset.card_range] at hnat
        exact_mod_cast hnat
      have hs3 : Real.sqrt (J : ℝ) ≤ 3 := by
        rw [Real.sqrt_le_iff]
        refine ⟨by norm_num, ?_⟩
        have hJ9 : (J : ℝ) ≤ 8 := by exact_mod_cast (by omega : J ≤ 8)
        linarith
      refine hcard.trans ?_
      rw [le_div_iff₀ hsJ]
      nlinarith [mul_le_mul_of_nonneg_left hs3 hNr0, mul_nonneg h2.le hNr0]
    · have hJ8' : 8 ≤ J := not_lt.mp hJ8
      have hk2 : 2 ≤ J / 4 := by omega
      have hkJ : J / 4 ≤ J := Nat.div_le_self J 4
      have hhi := (hrate (J / 4) (by omega)).2
      have hle := card_filter_le_of_residues
        (fun r : ℕ => ¬ ∀ t : ℤ, T^[J / 4] ((r : ℤ) + 2 ^ (J / 4) * t)
          = T^[J / 4] ((r : ℤ) + 2 ^ (J / 4) * t + 1))
        (fun n : ℕ => ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)) (2 ^ (J / 4)) N
        (by positivity) (fun n hn hE => unmerged_of_exception (J / 4) n hn hE)
      have hJ9 : J ≤ 9 * (J / 4) := by omega
      have hJk : J ≤ (J - J / 4) * 2 := by omega
      generalize J / 4 = k at hk2 hkJ hJ9 hJk hhi hle
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
      have hM : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      -- `√J ≤ 3 √k`
      have he : Real.sqrt (J : ℝ) ≤ 3 * Real.sqrt (k : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt hk0.le]
        have hJ9' : (J : ℝ) ≤ 9 * (k : ℝ) := by exact_mod_cast hJ9
        linarith
      -- `2^k √J ≤ N`
      have hf : (2 : ℝ) ^ k * Real.sqrt (J : ℝ) ≤ (N : ℝ) := by
        have hs : Real.sqrt (J : ℝ) ≤ (2 : ℝ) ^ (J - k) := by
          rw [Real.sqrt_le_iff]
          refine ⟨by positivity, ?_⟩
          have hnat : J ≤ (2 ^ (J - k)) ^ 2 := by
            rw [← pow_mul]
            exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) hJk)
          exact_mod_cast hnat
        have hnat : 2 ^ k * 2 ^ (J - k) ≤ N := by
          rw [← pow_add]
          have hkk : k + (J - k) = J := by omega
          rw [hkk]
          exact hpow
        have hcast : (2 : ℝ) ^ k * (2 : ℝ) ^ (J - k) ≤ (N : ℝ) := by exact_mod_cast hnat
        exact (mul_le_mul_of_nonneg_left hs hM.le).trans hcast
      have hd : (2 : ℝ) ^ k ≤ (N : ℝ) := by
        have hnat : 2 ^ k ≤ N := (Nat.pow_le_pow_right (by norm_num) hkJ).trans hpow
        exact_mod_cast hnat
      have hc : (2 : ℝ) ^ k * ((N / 2 ^ k : ℕ) : ℝ) ≤ (N : ℝ) := by
        have hnat : 2 ^ k * (N / 2 ^ k) ≤ N := Nat.mul_div_le N (2 ^ k)
        exact_mod_cast hnat
      have hq0 : (0 : ℝ) ≤ ((N / 2 ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
      have ha : (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)).card : ℝ) ≤
          (2 : ℝ) ^ k + (((Finset.range (2 ^ k)).filter fun r : ℕ =>
            ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ)
            * (((N / 2 ^ k : ℕ) : ℝ) + 1) := by
        exact_mod_cast hle
      have hu0 : (0 : ℝ) ≤ (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ) :=
        Nat.cast_nonneg _
      rw [le_div_iff₀ hsk] at hhi
      rw [le_div_iff₀ hsJ]
      generalize (((Finset.range (2 ^ k)).filter fun r : ℕ =>
          ¬ ∀ t : ℤ, T^[k] ((r : ℤ) + 2 ^ k * t) = T^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ) = u
        at hhi ha hu0
      generalize (((Finset.range N).filter fun n : ℕ =>
          ¬ ∃ k : ℕ, 2 ^ k ≤ n ∧ Tn^[k] n = Tn^[k] (n + 1)).card : ℝ) = cnt at ha ⊢
      generalize ((N / 2 ^ k : ℕ) : ℝ) = q at hc hq0 ha
      generalize Real.sqrt (J : ℝ) = s at hsJ he hf ⊢
      generalize Real.sqrt (k : ℝ) = sk at hsk he hhi
      generalize (2 : ℝ) ^ k = M at hM hf hd hc ha hhi
      generalize (N : ℝ) = n at hNr0 hf hd hc ⊢
      have g1 : cnt * s ≤ (M + u * (q + 1)) * s := mul_le_mul_of_nonneg_right ha hsJ.le
      have g2 : u * (q + 1) * s ≤ u * (q + 1) * (3 * sk) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      have g3 : (q + 1) * (u * sk) ≤ (q + 1) * (c₂ * M) :=
        mul_le_mul_of_nonneg_left hhi (by positivity)
      have g4 : c₂ * (M * q) ≤ c₂ * n := mul_le_mul_of_nonneg_left hc h2.le
      have g5 : c₂ * M ≤ c₂ * n := mul_le_mul_of_nonneg_left hd h2.le
      nlinarith

#print axioms class_merged_of_meet
#print axioms gao_exceptions_rate_T

end Coalescence
