import CollatzCoalescence.RatePotentials

/-!
# An expected-time potential for the strip of levels below `L`

`QL L s = qL L d + ell s + L * Gam2 s` on the strip `d ≤ L` (and `0` above it) drops by at least `1`
in expectation at every state of level `< L` outside the target set `F`.  The quadratic profile
`qL` is built from the second antiderivative `E2` of `ehat j = v₂(3^j - 1)`, whose partial sums are
at most `3 d`.
-/

namespace Coalescence

/-- `ehat j = e j = v₂(3^j - 1)` for `j ≥ 1`, and `ehat 0 = 0`. -/
def ehat (j : ℕ) : ℕ := if j = 0 then 0 else e j

/-- Second antiderivative of `ehat`: `E2 n = ∑_{j < n} (n - j) ehat j`. -/
def E2 (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, (n - j) * ehat j

namespace RateTime

/-! ### The 2-adic valuation of `3^j - 1` -/

theorem e_odd_le (j : ℕ) (hj : j % 2 = 1) : e j ≤ 1 := by
  by_contra h
  have h2 : 2 ≤ e j := by omega
  have hdvd : 2 ^ 2 ∣ 3 ^ j - 1 := dvd_trans (pow_dvd_pow 2 h2) (two_pow_e_dvd j)
  have h3 : 3 ^ j % 4 = 3 := by
    obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hdvd
  generalize 3 ^ j = x at hdvd h3
  omega

theorem e_even_eq (j : ℕ) (hj0 : j ≠ 0) (hj : Even j) : e j = 2 + padicValNat 2 j := by
  have h := padicValNat.pow_two_sub_one (x := 3) (n := j) (by norm_num) (by norm_num) hj0 hj
  have h4 : padicValNat 2 (3 + 1) = 2 := by
    have h22 : (3 + 1 : ℕ) = 2 ^ 2 := by norm_num
    rw [h22, padicValNat.prime_pow]
  have h2 : padicValNat 2 (3 - 1) = 1 := by
    have h21 : (3 - 1 : ℕ) = 2 := by norm_num
    rw [h21, padicValNat_self]
  unfold e
  omega

theorem ehat_le (j : ℕ) : ehat j ≤ (if j = 0 then 0 else 2) + padicValNat 2 j := by
  unfold ehat
  by_cases hj0 : j = 0
  · simp [hj0]
  · rw [if_neg hj0, if_neg hj0]
    rcases Nat.even_or_odd j with hev | hodd
    · rw [e_even_eq j hj0 hev]
    · have := e_odd_le j (Nat.odd_iff.mp hodd)
      omega

theorem sum_padicValNat_range (d : ℕ) :
    ∑ j ∈ Finset.range (d + 1), padicValNat 2 j = padicValNat 2 d.factorial := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero d) (Nat.factorial_ne_zero d)]
    exact Nat.add_comm _ _

theorem sum_two_range (d : ℕ) :
    ∑ j ∈ Finset.range (d + 1), (if j = 0 then 0 else 2) = 2 * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, if_neg (Nat.succ_ne_zero d)]
    omega

end RateTime

/-- `e j = 1` for odd `j`, `e j = 2 + v₂(j)` for even `j ≥ 2`; summed: -/
theorem sum_ehat_le (d : ℕ) : ∑ j ∈ Finset.range (d + 1), ehat j ≤ 3 * d := by
  have h1 : ∑ j ∈ Finset.range (d + 1), ehat j
      ≤ ∑ j ∈ Finset.range (d + 1), ((if j = 0 then 0 else 2) + padicValNat 2 j) :=
    Finset.sum_le_sum (fun j _ => RateTime.ehat_le j)
  rw [Finset.sum_add_distrib, RateTime.sum_two_range, RateTime.sum_padicValNat_range] at h1
  have h3 := padicValNat_factorial_le 2 d
  omega

namespace RateTime

/-! ### The second antiderivative `E2` -/

theorem E2_zero : E2 0 = 0 := by simp [E2]

theorem E2_one : E2 1 = 0 := by simp [E2, ehat]

theorem E2_succ (n : ℕ) : E2 (n + 1) = E2 n + ∑ j ∈ Finset.range (n + 1), ehat j := by
  unfold E2
  rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => ehat j)]
  have h : ∑ j ∈ Finset.range n, (n + 1 - j) * ehat j
      = ∑ j ∈ Finset.range n, (n - j) * ehat j + ∑ j ∈ Finset.range n, ehat j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hsub : n + 1 - j = (n - j) + 1 := by omega
    rw [hsub]
    ring
  have h1 : n + 1 - n = 1 := by omega
  rw [h, h1]
  ring

theorem E2_le_succ (n : ℕ) : E2 n ≤ E2 (n + 1) := by
  rw [E2_succ]
  exact Nat.le_add_right _ _

theorem E2_mono : Monotone E2 := monotone_nat_of_le_succ E2_le_succ

theorem E2_second_diff (n : ℕ) : E2 (n + 1 + 1) + E2 n = 2 * E2 (n + 1) + ehat (n + 1) := by
  have h1 := E2_succ (n + 1)
  have h2 := E2_succ n
  rw [Finset.sum_range_succ] at h1
  omega

theorem E2_second_diff' (n : ℕ) : E2 (n + 1) + E2 (n - 1) = 2 * E2 n + ehat n := by
  cases n with
  | zero => simp [E2_zero, E2_one, ehat]
  | succ n =>
    rw [Nat.add_sub_cancel]
    exact E2_second_diff n

theorem E2_le (d : ℕ) : E2 (d + 1) ≤ 3 * d * (d + 1) := by
  induction d with
  | zero => simp [E2_one]
  | succ d ih =>
    have h1 := E2_succ (d + 1)
    have h2 := sum_ehat_le (d + 1)
    nlinarith

end RateTime

/-- The quadratic level profile of the strip potential. -/
noncomputable def qL (L d : ℕ) : ℝ :=
  (8 * (L : ℝ) + 14) * d + 6 - 2 * (d : ℝ) ^ 2 - (E2 (d + 1) : ℝ) - (E2 (d - 1) : ℝ)

namespace RateTime

/-! ### The profile `qL` -/

theorem qL_zero (L : ℕ) : qL L 0 = 6 := by
  simp [qL, E2_zero, E2_one]

theorem qL_one_le (L : ℕ) : qL L 1 ≤ 8 * (L : ℝ) + 18 := by
  have h1 : (0 : ℝ) ≤ (E2 (1 + 1) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (E2 (1 - 1) : ℝ) := Nat.cast_nonneg _
  unfold qL
  rw [Nat.cast_one]
  linarith

theorem qL_le (L d : ℕ) : qL L d ≤ (8 * (L : ℝ) + 14) * d + 6 := by
  unfold qL
  have h1 : (0 : ℝ) ≤ (E2 (d + 1) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (E2 (d - 1) : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  linarith

theorem qL_ge (L d : ℕ) (hd : d ≤ L) : 6 ≤ qL L d := by
  unfold qL
  have h1 : (E2 (d + 1) : ℝ) ≤ 3 * (d : ℝ) * ((d : ℝ) + 1) := by exact_mod_cast E2_le d
  have h2 : (E2 (d - 1) : ℝ) ≤ (E2 (d + 1) : ℝ) := by
    exact_mod_cast E2_mono (show d - 1 ≤ d + 1 by omega)
  have h3 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have h4 : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast hd
  have h5 : 0 ≤ (d : ℝ) * ((L : ℝ) - (d : ℝ)) := mul_nonneg h3 (by linarith)
  nlinarith

theorem qL_second_diff (L n : ℕ) :
    qL L (n + 1 + 1) + qL L n
      = 2 * qL L (n + 1) - 4 - (ehat (n + 1 + 1) : ℝ) - (ehat n : ℝ) := by
  have h1 : E2 (n + 1 + 1 + 1) + E2 (n + 1) = 2 * E2 (n + 1 + 1) + ehat (n + 1 + 1) :=
    E2_second_diff (n + 1)
  have h2 : E2 (n + 1) + E2 (n - 1) = 2 * E2 n + ehat n := E2_second_diff' n
  have h1' : (E2 (n + 1 + 1 + 1) : ℝ) + (E2 (n + 1) : ℝ)
      = 2 * (E2 (n + 1 + 1) : ℝ) + (ehat (n + 1 + 1) : ℝ) := by exact_mod_cast h1
  have h2' : (E2 (n + 1) : ℝ) + (E2 (n - 1) : ℝ) = 2 * (E2 n : ℝ) + (ehat n : ℝ) := by
    exact_mod_cast h2
  have e1 : n + 1 + 1 - 1 = n + 1 := by omega
  have e2 : n + 1 - 1 = n := by omega
  unfold qL
  rw [e1, e2]
  push_cast
  linarith

/-! ### `ell` and the level of the children -/

theorem ell_le_ehat (s : State) : ell s ≤ ehat s.d + 1 := by
  unfold ell ehat
  by_cases hd : s.d = 0
  · simp [hd]
  · rw [if_neg hd, if_neg hd]
    have h2 : ((Finset.Icc 1 (e s.d)).filter (fun j => (2 : ℤ) ^ j ∣ s.mu)).card ≤ e s.d := by
      calc ((Finset.Icc 1 (e s.d)).filter (fun j => (2 : ℤ) ^ j ∣ s.mu)).card
          ≤ (Finset.Icc 1 (e s.d)).card := Finset.card_filter_le _ _
        _ = e s.d := by simp
    split_ifs <;> omega

theorem stepd_even (s : State) (h : s.mu % 2 = 0) (c : Bool) : (step s c).d = s.d := by
  obtain ⟨d, μ⟩ := s
  cases c
  · rw [step_even_false d μ h, norm_d]
  · rw [step_even_true d μ h, norm_d]

theorem stepd_odd_false (s : State) (h : s.mu % 2 = 1) : (step s false).d = s.d + 1 := by
  obtain ⟨d, μ⟩ := s
  rw [step_odd_false d μ h]

theorem stepd_odd_true (s : State) (h : s.mu % 2 = 1) (hd : 0 < s.d) :
    (step s true).d = s.d - 1 := by
  obtain ⟨d, μ⟩ := s
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by
    have hd' : 0 < d := hd
    omega⟩
  rw [step_odd_true_succ d' μ h, norm_d]
  rfl

theorem stepd_odd_true_zero (s : State) (h : s.mu % 2 = 1) (hd : s.d = 0) :
    (step s true).d = 1 := by
  obtain ⟨d, μ⟩ := s
  have hd' : d = 0 := hd
  subst hd'
  rw [step_odd_true_zero μ h]

theorem stepd_le (s : State) (c : Bool) : (step s c).d ≤ s.d + 1 := by
  rcases Int.emod_two_eq_zero_or_one s.mu with hμ | hμ
  · rw [stepd_even s hμ c]
    exact Nat.le_succ _
  · cases c
    · rw [stepd_odd_false s hμ]
    · rcases Nat.eq_zero_or_pos s.d with hd | hd
      · rw [stepd_odd_true_zero s hμ hd]
        omega
      · rw [stepd_odd_true s hμ hd]
        omega

/-! ### The level-`0` odd drop, for the explicit formula of `Gam2` -/

theorem drop_zero_odd_aux (G : State → ℝ)
    (hG : ∀ s : State, G s = A * (1 - lam ^ s.d) + theta ^ s.d / Real.sqrt 2 * (ell s : ℝ)
      + theta ^ s.d * Real.sqrt (size s))
    (s : State) (hd : s.d = 0) (hs : s ∉ F) (hμ : s.mu % 2 = 1) :
    (G (step s false) + G (step s true)) / 2 + 24 ≤ G s := by
  obtain ⟨d, μ⟩ := s
  have hd' : d = 0 := hd
  subst hd'
  have hμ' : μ % 2 = 1 := hμ
  have hM : M < |μ| := by
    by_contra h
    exact hs ((mem_F _).mpr ⟨rfl, not_lt.mp h⟩)
  have key : ∀ c : Bool, G (step ⟨0, μ⟩ c) + 24 ≤ G ⟨0, μ⟩ := by
    intro c
    have hsz := sqrt_size_step_zero_odd μ hμ' c
    have hdc : (step ⟨0, μ⟩ c).d = 1 := by
      cases c
      · rw [step_odd_false _ _ hμ']
      · rw [step_odd_true_zero _ hμ']
    have hl : (ell (step ⟨0, μ⟩ c) : ℝ) ≤ 2 := by
      have h := ell_le (step ⟨0, μ⟩ c)
      rw [hdc] at h
      exact_mod_cast h
    have hl0 : (0 : ℝ) ≤ (ell (step ⟨0, μ⟩ c) : ℝ) := Nat.cast_nonneg _
    rw [hG (step ⟨0, μ⟩ c), hG ⟨0, μ⟩, hdc, ell_of_d_zero ⟨0, μ⟩ rfl]
    have hA : A = 250000 := rfl
    have hth : theta = 19 / 20 := rfl
    have hlam : lam = 39 / 40 := rfl
    simp only [pow_one, pow_zero, hA, hth, hlam, div_eq_mul_inv (19 / 20 : ℝ) (Real.sqrt 2),
      div_eq_mul_inv (1 : ℝ) (Real.sqrt 2), ← sqrt_half_eq]
    have hσ := sqrt_size_zero_ge μ hM
    have hk := sqrt_half_pos
    have hk' := sqrt_half_lt
    generalize Real.sqrt (1 / 2) = k at *
    generalize Real.sqrt (size ⟨0, μ⟩) = σ at *
    generalize Real.sqrt (size (step ⟨0, μ⟩ c)) = σc at *
    generalize (ell (step ⟨0, μ⟩ c) : ℝ) = l at *
    have p1 : σ * k ≤ σ * 0.7072 := mul_le_mul_of_nonneg_left hk'.le (by linarith)
    have p2 : k * l ≤ k * 2 := mul_le_mul_of_nonneg_left hl hk.le
    norm_num
    linarith
  have h0 := key false
  have h1 := key true
  linarith

/-! ### The one-step drop of the strip potential, for an abstract `G` -/

theorem QL_step_aux (G : State → ℝ)
    (hsuper : ∀ s : State, 0 < s.d → (G (step s false) + G (step s true)) / 2 ≤ G s)
    (hdrop : ∀ s : State, s.d = 0 → s ∉ F → (G (step s false) + G (step s true)) / 2 + 1 ≤ G s)
    (hdrop_odd : ∀ s : State, s.d = 0 → s ∉ F → s.mu % 2 = 1 →
      (G (step s false) + G (step s true)) / 2 + 24 ≤ G s)
    (L : ℕ) (hL : 1 ≤ L) (s : State) (hs : s ∉ F) (hd : s.d < L) :
    ((qL L (step s false).d + (ell (step s false) : ℝ) + (L : ℝ) * G (step s false))
      + (qL L (step s true).d + (ell (step s true) : ℝ) + (L : ℝ) * G (step s true))) / 2 + 1
      ≤ qL L s.d + (ell s : ℝ) + (L : ℝ) * G s := by
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by linarith
  rcases Nat.eq_zero_or_pos s.d with hd0 | hdpos
  · rcases Int.emod_two_eq_zero_or_one s.mu with hμ | hμ
    · -- level `0`, even offset: `qL` and `ell` are unchanged, `L * G` drops by `L ≥ 1`
      have hdf := stepd_even s hμ false
      have hdt := stepd_even s hμ true
      rw [hd0] at hdf hdt
      rw [hdf, hdt, hd0, ell_of_d_zero _ hdf, ell_of_d_zero _ hdt, ell_of_d_zero _ hd0]
      have h := mul_le_mul_of_nonneg_left (hdrop s hd0 hs) hL0
      push_cast
      linarith
    · -- level `0`, odd offset: both children at level `1`, paid for by the drop `24 L`
      have hdf := stepd_odd_false s hμ
      have hdt := stepd_odd_true_zero s hμ hd0
      rw [hd0] at hdf
      have hl0 : (ell (step s false) : ℝ) ≤ 2 := by
        have h := ell_le (step s false)
        rw [hdf] at h
        exact_mod_cast h
      have hl1 : (ell (step s true) : ℝ) ≤ 2 := by
        have h := ell_le (step s true)
        rw [hdt] at h
        exact_mod_cast h
      rw [hdf, hdt, hd0, ell_of_d_zero _ hd0]
      have hq1 := qL_one_le L
      have hq0 := qL_zero L
      have h := mul_le_mul_of_nonneg_left (hdrop_odd s hd0 hs hμ) hL0
      push_cast
      linarith
  · rcases Int.emod_two_eq_zero_or_one s.mu with hμ | hμ
    · -- level `≥ 1`, even offset: `ell` drops by `1`
      have hdf := stepd_even s hμ false
      have hdt := stepd_even s hμ true
      have hG := mul_le_mul_of_nonneg_left (hsuper s hdpos) hL0
      rw [hdf, hdt]
      obtain ⟨d, μ⟩ := s
      have hdpos' : 0 < d := hdpos
      have hμ' : μ % 2 = 0 := hμ
      have hell := ell_even_step d hdpos' μ hμ'
      have e0 : step ⟨d, μ⟩ false = ⟨d, μ / 2⟩ := by
        rw [step_even_false d μ hμ', State.norm_of_pos d _ hdpos']
      have e1 : step ⟨d, μ⟩ true = ⟨d, (3 * μ + 1 - 3 ^ d) / 2⟩ := by
        rw [step_even_true d μ hμ', State.norm_of_pos d _ hdpos']
      rw [← e0, ← e1] at hell
      have hell' : (ell (step ⟨d, μ⟩ false) : ℝ) + (ell (step ⟨d, μ⟩ true) : ℝ) + 2
          ≤ 2 * (ell ⟨d, μ⟩ : ℝ) := by exact_mod_cast hell
      linarith
    · -- level `≥ 1`, odd offset: the second difference of `qL` pays for the children's `ell`
      have hdf := stepd_odd_false s hμ
      have hdt := stepd_odd_true s hμ hdpos
      have hell : ell s = 0 := (ell_eq_zero_iff s hdpos).mpr hμ
      have hl0 := ell_le_ehat (step s false)
      have hl1 := ell_le_ehat (step s true)
      have hG := mul_le_mul_of_nonneg_left (hsuper s hdpos) hL0
      obtain ⟨n, hn⟩ : ∃ n, s.d = n + 1 := ⟨s.d - 1, by omega⟩
      have e1 : n + 1 - 1 = n := by omega
      rw [hn, e1] at hdt
      rw [hn] at hdf
      rw [hdf] at hl0
      rw [hdt] at hl1
      rw [hdf, hdt, hell, hn]
      have hq := qL_second_diff L n
      have hl0' : (ell (step s false) : ℝ) ≤ (ehat (n + 1 + 1) : ℝ) + 1 := by exact_mod_cast hl0
      have hl1' : (ell (step s true) : ℝ) ≤ (ehat n : ℝ) + 1 := by exact_mod_cast hl1
      push_cast
      linarith

end RateTime

/-- At level `0` outside `F` with an odd offset, `Gam2` drops by at least `24`. -/
theorem Gam2_drop_zero_odd (s : State) (hd : s.d = 0) (hs : s ∉ F) (hμ : s.mu % 2 = 1) :
    (Gam2 (step s false) + Gam2 (step s true)) / 2 + 24 ≤ Gam2 s :=
  RateTime.drop_zero_odd_aux Gam2 (fun _ => rfl) s hd hs hμ

/-- Expected-time potential for the strip of levels below `L`. -/
noncomputable def QL (L : ℕ) (s : State) : ℝ :=
  if s.d ≤ L then qL L s.d + (ell s : ℝ) + (L : ℝ) * Gam2 s else 0

theorem QL_nonneg (L : ℕ) (s : State) : 0 ≤ QL L s := by
  unfold QL
  split_ifs with h
  · have h1 := RateTime.qL_ge L s.d h
    have h2 : (0 : ℝ) ≤ (ell s : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ (L : ℝ) * Gam2 s := mul_nonneg (Nat.cast_nonneg _) (Gam2_nonneg s)
    linarith
  · exact le_rfl

theorem QL_step (L : ℕ) (hL : 1 ≤ L) (s : State) (hs : s ∉ F) (hd : s.d < L) :
    (QL L (step s false) + QL L (step s true)) / 2 + 1 ≤ QL L s := by
  have h0 : (step s false).d ≤ L := le_trans (RateTime.stepd_le s false) hd
  have h1 : (step s true).d ≤ L := le_trans (RateTime.stepd_le s true) hd
  unfold QL
  rw [if_pos h0, if_pos h1, if_pos hd.le]
  exact RateTime.QL_step_aux Gam2 Gam2_super_pos Gam2_drop_zero Gam2_drop_zero_odd L hL s hs hd

theorem QL_le (L : ℕ) (s : State) (hd : s.d ≤ L) :
    QL L s ≤ (8 * (L : ℝ) + 16) * s.d + 6 + (L : ℝ) * Gam2 s := by
  unfold QL
  rw [if_pos hd]
  have h1 := RateTime.qL_le L s.d
  have h2 : (ell s : ℝ) ≤ 2 * (s.d : ℝ) := by exact_mod_cast ell_le s
  linarith

end Coalescence

#print axioms Coalescence.sum_ehat_le
#print axioms Coalescence.Gam2_drop_zero_odd
#print axioms Coalescence.QL_nonneg
#print axioms Coalescence.QL_step
#print axioms Coalescence.QL_le
