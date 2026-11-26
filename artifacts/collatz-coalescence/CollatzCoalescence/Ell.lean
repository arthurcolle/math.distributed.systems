import CollatzCoalescence.PotentialDefs

/-!
# The even-phase potential `ell`

Covers Lemma `ell` of `main.tex` (Section 4): `1 ≤ e d < 2 d`, `ell ≤ 2 d`, `ell = 0` iff the offset
is odd, and the drop `ell (d, μ/2) + ell (d, (3μ+1-3^d)/2) + 2 ≤ 2 ell (d, μ)` for even `μ`.
-/

namespace Coalescence

theorem three_pow_sub_one_pos (d : ℕ) (hd : 0 < d) : 0 < 3 ^ d - 1 := by
  have h : 3 ^ 1 ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  omega

theorem two_pow_e_dvd (d : ℕ) : 2 ^ e d ∣ 3 ^ d - 1 := pow_padicValNat_dvd

theorem two_pow_e_succ_not_dvd (d : ℕ) (hd : 0 < d) : ¬ 2 ^ (e d + 1) ∣ 3 ^ d - 1 :=
  pow_succ_padicValNat_not_dvd (three_pow_sub_one_pos d hd).ne'

theorem e_pos (d : ℕ) (hd : 0 < d) : 1 ≤ e d := by
  have h0 : 3 ^ d - 1 ≠ 0 := (three_pow_sub_one_pos d hd).ne'
  have h2 : 2 ∣ 3 ^ d - 1 := by
    have h : 3 ^ d % 2 = 1 := by
      rw [Nat.pow_mod]
      simp
    omega
  exact one_le_padicValNat_of_dvd h0 h2

theorem e_lt (d : ℕ) (hd : 0 < d) : e d < 2 * d := by
  have h1 : 2 ^ e d ≤ 3 ^ d - 1 := Nat.le_of_dvd (three_pow_sub_one_pos d hd) (two_pow_e_dvd d)
  have h2 : 3 ^ d < 4 ^ d := Nat.pow_lt_pow_left (by norm_num) hd.ne'
  have h3 : (4 : ℕ) ^ d = 2 ^ (2 * d) := by
    rw [pow_mul]
    norm_num
  have h0 := three_pow_sub_one_pos d hd
  have h1' : 2 ^ e d < 3 ^ d := by omega
  have h4 : 2 ^ e d < 2 ^ (2 * d) := by
    rw [← h3]
    exact lt_trans h1' h2
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h4

theorem ell_le (s : State) : ell s ≤ 2 * s.d := by
  unfold ell
  by_cases hd : s.d = 0
  · simp [hd]
  · rw [if_neg hd]
    have h1 := e_lt s.d (Nat.pos_of_ne_zero hd)
    have h2 : ((Finset.Icc 1 (e s.d)).filter (fun j => (2 : ℤ) ^ j ∣ s.mu)).card ≤ e s.d := by
      calc ((Finset.Icc 1 (e s.d)).filter (fun j => (2 : ℤ) ^ j ∣ s.mu)).card
          ≤ (Finset.Icc 1 (e s.d)).card := Finset.card_filter_le _ _
        _ = e s.d := by simp
    split_ifs <;> omega

theorem ell_eq_zero_iff (s : State) (hd : 0 < s.d) : ell s = 0 ↔ s.mu % 2 = 1 := by
  have hd0 : s.d ≠ 0 := hd.ne'
  have he := e_pos s.d hd
  unfold ell
  rw [if_neg hd0]
  constructor
  · intro h
    have h1 : ((Finset.Icc 1 (e s.d)).filter (fun j => (2 : ℤ) ^ j ∣ s.mu)).card = 0 := by omega
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    have h2 := h1 (Finset.mem_Icc.mpr ⟨le_refl 1, he⟩)
    rw [pow_one] at h2
    omega
  · intro h
    have hodd : ∀ j : ℕ, 1 ≤ j → ¬ (2 : ℤ) ^ j ∣ s.mu := by
      intro j hj hdiv
      have h2 : (2 : ℤ) ∣ s.mu := dvd_trans (dvd_pow_self 2 (by omega)) hdiv
      omega
    have h1 : (Finset.Icc 1 (e s.d)).filter (fun j => (2 : ℤ) ^ j ∣ s.mu) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j hj
      exact hodd j (Finset.mem_Icc.mp hj).1
    rw [h1, if_neg (hodd _ he)]
    simp

/-- Peeling the top index off a filtered initial segment. -/
theorem cnt_succ (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    ((Finset.Icc 1 (n + 1)).filter p).card
      = ((Finset.Icc 1 n).filter p).card + (if p (n + 1) then 1 else 0) := by
  have h : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [h, Finset.filter_insert]
  split_ifs with hp
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

/-- Dividing by two shifts the divisibility count. -/
theorem cnt_two_mul (m : ℤ) (n : ℕ) :
    ((Finset.Icc 1 (n + 1)).filter (fun j => (2 : ℤ) ^ j ∣ 2 * m)).card
      = 1 + ((Finset.Icc 1 n).filter (fun j => (2 : ℤ) ^ j ∣ m)).card := by
  induction n with
  | zero => simp [Finset.filter_singleton]
  | succ n ih =>
    rw [cnt_succ, ih, cnt_succ (fun j => (2 : ℤ) ^ j ∣ m)]
    have h : (2 : ℤ) ^ (n + 1 + 1) ∣ 2 * m ↔ (2 : ℤ) ^ (n + 1) ∣ m := by
      rw [pow_succ' (2 : ℤ) (n + 1), mul_dvd_mul_iff_left (two_ne_zero)]
    simp only [h]
    omega

theorem ell_even_step (d : ℕ) (hd : 0 < d) (μ : ℤ) (hμ : μ % 2 = 0) :
    ell ⟨d, μ / 2⟩ + ell ⟨d, (3 * μ + 1 - 3 ^ d) / 2⟩ + 2 ≤ 2 * ell ⟨d, μ⟩ := by
  obtain ⟨n, hn⟩ : ∃ n, e d = n + 1 := ⟨e d - 1, by have := e_pos d hd; omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, μ = 2 * m := ⟨μ / 2, by omega⟩
  -- the 2-adic facts about `3^d - 1`, transported to `ℤ`
  have hcast : (((3 ^ d - 1 : ℕ)) : ℤ) = (3 : ℤ) ^ d - 1 := by
    have h1 : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
    push_cast [Nat.cast_sub h1]
    ring
  have hD1 : (2 : ℤ) ^ (n + 1) ∣ (3 : ℤ) ^ d - 1 := by
    have h := two_pow_e_dvd d
    rw [hn] at h
    rw [← hcast]
    exact_mod_cast h
  have hD2 : ¬ (2 : ℤ) ^ (n + 1 + 1) ∣ (3 : ℤ) ^ d - 1 := by
    have h := two_pow_e_succ_not_dvd d hd
    rw [hn] at h
    rw [← hcast]
    exact_mod_cast h
  obtain ⟨D', hD'⟩ : ∃ D' : ℤ, (3 : ℤ) ^ d - 1 = 2 * D' := by
    obtain ⟨k, hk⟩ := hD1
    exact ⟨2 ^ n * k, by rw [hk]; ring⟩
  have hD'1 : (2 : ℤ) ^ n ∣ D' := by
    rw [hD', pow_succ' (2 : ℤ) n, mul_dvd_mul_iff_left two_ne_zero] at hD1
    exact hD1
  have hD'2 : ¬ (2 : ℤ) ^ (n + 1) ∣ D' := by
    rw [hD', pow_succ' (2 : ℤ) (n + 1), mul_dvd_mul_iff_left two_ne_zero] at hD2
    exact hD2
  have hm : 2 * m / 2 = m := by omega
  have hν : (3 * (2 * m) + 1 - 3 ^ d) / 2 = 3 * m - D' := by omega
  rw [hm, hν]
  have hd0 : d ≠ 0 := hd.ne'
  -- divisibility of `ν = 3m - D'` by small powers of two agrees with that of `m`
  have hcop : ∀ j : ℕ, (2 : ℤ) ^ j ∣ 3 * m → (2 : ℤ) ^ j ∣ m := by
    intro j h
    have hc : IsCoprime ((2 : ℤ) ^ j) 3 := IsCoprime.pow_left (by decide)
    exact hc.dvd_of_dvd_mul_left h
  have hlow : ∀ j : ℕ, j ≤ n → ((2 : ℤ) ^ j ∣ 3 * m - D' ↔ (2 : ℤ) ^ j ∣ m) := by
    intro j hj
    have hjD : (2 : ℤ) ^ j ∣ D' := dvd_trans (pow_dvd_pow 2 hj) hD'1
    constructor
    · intro h
      have h3 : (2 : ℤ) ^ j ∣ 3 * m := by
        have := dvd_add h hjD
        simpa using this
      exact hcop j h3
    · intro h
      exact dvd_sub (dvd_mul_of_dvd_right h 3) hjD
  have hfilt : (Finset.Icc 1 n).filter (fun j => (2 : ℤ) ^ j ∣ 3 * m - D')
      = (Finset.Icc 1 n).filter (fun j => (2 : ℤ) ^ j ∣ m) := by
    apply Finset.filter_congr
    intro j hj
    exact hlow j (Finset.mem_Icc.mp hj).2
  have hμdvd : (2 : ℤ) ^ (n + 1) ∣ 2 * m ↔ (2 : ℤ) ^ n ∣ m := by
    rw [pow_succ' (2 : ℤ) n, mul_dvd_mul_iff_left two_ne_zero]
  -- unfold the three values of `ell`
  have e1 : ell ⟨d, 2 * m⟩
      = 1 + ((Finset.Icc 1 n).filter (fun j => (2 : ℤ) ^ j ∣ m)).card
        + (if (2 : ℤ) ^ n ∣ m then 1 else 0) := by
    simp only [ell, hd0, if_false, hn]
    rw [cnt_two_mul]
    simp only [hμdvd]
  have e2 : ell ⟨d, m⟩
      = ((Finset.Icc 1 n).filter (fun j => (2 : ℤ) ^ j ∣ m)).card
        + (if (2 : ℤ) ^ (n + 1) ∣ m then 1 else 0) + (if (2 : ℤ) ^ (n + 1) ∣ m then 1 else 0) := by
    simp only [ell, hd0, if_false, hn]
    rw [cnt_succ (fun j => (2 : ℤ) ^ j ∣ m)]
  have e3 : ell ⟨d, 3 * m - D'⟩
      = ((Finset.Icc 1 n).filter (fun j => (2 : ℤ) ^ j ∣ m)).card
        + (if (2 : ℤ) ^ (n + 1) ∣ 3 * m - D' then 1 else 0)
        + (if (2 : ℤ) ^ (n + 1) ∣ 3 * m - D' then 1 else 0) := by
    simp only [ell, hd0, if_false, hn]
    rw [cnt_succ (fun j => (2 : ℤ) ^ j ∣ 3 * m - D'), hfilt]
  rw [e1, e2, e3]
  -- the indicator inequality `[2^(E) ∣ m] + [2^E ∣ ν] ≤ [2^(E-1) ∣ m]`
  by_cases hA : (2 : ℤ) ^ n ∣ m
  · have hnot : ¬ ((2 : ℤ) ^ (n + 1) ∣ m ∧ (2 : ℤ) ^ (n + 1) ∣ 3 * m - D') := by
      rintro ⟨h1, h2⟩
      apply hD'2
      have := dvd_sub (dvd_mul_of_dvd_right h1 3) h2
      simpa using this
    by_cases hB : (2 : ℤ) ^ (n + 1) ∣ m
    · have hC : ¬ (2 : ℤ) ^ (n + 1) ∣ 3 * m - D' := fun h => hnot ⟨hB, h⟩
      simp only [if_pos hA, if_pos hB, if_neg hC]
      omega
    · by_cases hC : (2 : ℤ) ^ (n + 1) ∣ 3 * m - D'
      · simp only [if_pos hA, if_neg hB, if_pos hC]
        omega
      · simp only [if_pos hA, if_neg hB, if_neg hC]
        omega
  · have hB : ¬ (2 : ℤ) ^ (n + 1) ∣ m := fun h => hA (dvd_trans (pow_dvd_pow 2 (Nat.le_succ n)) h)
    have hC : ¬ (2 : ℤ) ^ (n + 1) ∣ 3 * m - D' := by
      intro h
      have h' : (2 : ℤ) ^ n ∣ 3 * m - D' := dvd_trans (pow_dvd_pow 2 (Nat.le_succ n)) h
      exact hA ((hlow n le_rfl).mp h')
    simp only [if_neg hA, if_neg hB, if_neg hC]
    omega

end Coalescence

#print axioms Coalescence.e_pos
#print axioms Coalescence.e_lt
#print axioms Coalescence.ell_le
#print axioms Coalescence.ell_eq_zero_iff
#print axioms Coalescence.ell_even_step
