import CollatzCoalescence.MultMain
import CollatzCoalescence.Main

/-!
# Saturation for every odd multiplier `a ≥ 5`

For `x ↦ x / 2, (a x + 1) / 2` with `a` odd and `a ≥ 5` the neighbour pair chain is not absorbed
almost surely.  The potential `phiA a = min 1 ((1 + (2/3)^d) * (8 / w)^(1/4))` with `w = |μ| / a^d` is
superharmonic at every state; it is `≤ 2/3` at a state reached from `(0, 1)` by a word of `true`
coins, because the all-`true` orbit stays in the family `(0, m)`, `m ≥ 1` and `(1, -m)`, `m ≥ 1`, with
`m` growing without bound.

Consequently `3` is the only odd multiplier `≥ 3` for which neighbours merge with probability
tending to `1`.
-/

namespace Coalescence.Mult
open Generic Filter Topology

/-- The potential for the multiplier `a`: `min 1 ((1 + (2/3)^d) * (8 / w)^(1/4))`, and `1` when
`μ = 0`. -/
noncomputable def phiA (a : ℕ) (s : State) : ℝ :=
  if s.mu = 0 then 1 else min 1 ((1 + (2 / 3 : ℝ) ^ s.d) * (8 / wA a s) ^ (1 / 4 : ℝ))

theorem phiA_five : phiA 5 = phi5 := rfl

theorem phiA_nonneg (a : ℕ) (s : State) : 0 ≤ phiA a s := by
  unfold phiA
  split_ifs
  · exact zero_le_one
  · have h1 : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ s.d := by positivity
    have h2 : (0 : ℝ) ≤ (8 / wA a s) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by unfold wA; positivity) _
    exact le_min zero_le_one (mul_nonneg (by linarith) h2)

theorem phiA_le_one (a : ℕ) (s : State) : phiA a s ≤ 1 := by
  unfold phiA
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem phiA_absorbed (a : ℕ) : phiA a absorbed = 1 := by
  simp [phiA, absorbed]

/-- The bound for `phiA a` at a child whose weight is at least `ρ w`. -/
theorem phiA_child_le {a : ℕ} {t : State} {w ρ y : ℝ} (hw : 0 < w) (hρ : 0 < ρ) (hy : 0 ≤ y)
    (hρy : 1 ≤ ρ * y ^ 4) (h : ρ * w ≤ wA a t) :
    phiA a t ≤ (1 + (2 / 3 : ℝ) ^ t.d) * (y * (8 / w) ^ (1 / 4 : ℝ)) := by
  have hwt : 0 < wA a t := lt_of_lt_of_le (mul_pos hρ hw) h
  have hmu : t.mu ≠ 0 := by
    intro h0
    simp [wA, h0] at hwt
  have hc : (0 : ℝ) ≤ 1 + (2 / 3 : ℝ) ^ t.d := by positivity
  unfold phiA
  rw [if_neg hmu]
  exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (quarter_child hw hρ hy hρy h) hc)

/-! ## Weights of the children, for `a ≥ 5` and `w ≥ 8` -/

/-- Coin `false`: `w' ≥ (39/40) (w/2)`. -/
theorem wA_false_ge_of_five_le (a : ℕ) (ha5 : 5 ≤ a) (s : State) (hw : 8 ≤ wA a s) :
    39 / 80 * wA a s ≤ wA a (stepA a s false) := by
  have hA5 : (5 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha5
  have hf := wA_step_false_ge a (by omega) s
  have hinv : 1 / (2 * (a : ℝ)) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- Coin `true` away from (level `0`, odd offset): `w' ≥ (39/40) (5w/2)`. -/
theorem wA_true_ge_of_five_le (a : ℕ) (ha : a % 2 = 1) (ha5 : 5 ≤ a) (s : State)
    (hw : 8 ≤ wA a s) (h : ¬ (s.d = 0 ∧ s.mu % 2 = 1)) :
    39 / 16 * wA a s ≤ wA a (stepA a s true) := by
  have hA5 : (5 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha5
  have ht := wA_step_true_ge_of_odd a (by omega) ha s h
  have haw : 5 * wA a s ≤ (a : ℝ) * wA a s := mul_le_mul_of_nonneg_right hA5 (by linarith)
  linarith

/-- Coin `true` at level `0` with odd offset: `w' ≥ (39/40) (w/2)`. -/
theorem wA_true_zero_ge_of_five_le (a : ℕ) (ha5 : 5 ≤ a) (m : ℤ) (hm : m % 2 = 1)
    (hw : 8 ≤ wA a ⟨0, m⟩) : 39 / 80 * wA a ⟨0, m⟩ ≤ wA a (stepA a ⟨0, m⟩ true) := by
  have hA5 : (5 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha5
  have ht := wA_step_true_zero_odd a (by omega) m hm
  have hinv : 1 / (2 * (a : ℝ)) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-! ## Superharmonicity -/

/-- `phiA a` is superharmonic at every state, for every odd `a ≥ 5`. -/
theorem phiA_super (a : ℕ) (ha : a % 2 = 1) (ha5 : 5 ≤ a) (s : State) :
    (phiA a (stepA a s false) + phiA a (stepA a s true)) / 2 ≤ phiA a s := by
  have h0 := phiA_le_one a (stepA a s false)
  have h1 := phiA_le_one a (stepA a s true)
  by_cases hmu : s.mu = 0
  · have hs : phiA a s = 1 := by simp [phiA, hmu]
    linarith
  by_cases hψ : 1 ≤ (1 + (2 / 3 : ℝ) ^ s.d) * (8 / wA a s) ^ (1 / 4 : ℝ)
  · have hs : phiA a s = 1 := by
      unfold phiA
      rw [if_neg hmu, min_eq_left hψ]
    linarith
  replace hψ := not_le.mp hψ
  have hphi : phiA a s = (1 + (2 / 3 : ℝ) ^ s.d) * (8 / wA a s) ^ (1 / 4 : ℝ) := by
    unfold phiA
    rw [if_neg hmu, min_eq_right hψ.le]
  have hA0' : (0 : ℝ) < (a : ℝ) := by
    have : (5 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha5
    linarith
  have hwpos : 0 < wA a s := by
    unfold wA
    have : (0 : ℝ) < |(s.mu : ℝ)| := abs_pos.mpr (by exact_mod_cast hmu)
    exact div_pos this (pow_pos hA0' _)
  have hQ0 : (0 : ℝ) ≤ (8 / wA a s) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hr0 : (0 : ℝ) < (2 / 3 : ℝ) ^ s.d := by positivity
  have hw8 : 8 < wA a s := by
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have h8 : 1 ≤ 8 / wA a s := by
      rw [le_div_iff₀ hwpos]; linarith
    have hQ1 : 1 ≤ (8 / wA a s) ^ (1 / 4 : ℝ) := Real.one_le_rpow h8 (by norm_num)
    nlinarith
  have hf' : 39 / 80 * wA a s ≤ wA a (stepA a s false) :=
    wA_false_ge_of_five_le a ha5 s hw8.le
  have hA0 : (0 : ℝ) ≤ 1.0064 * 1.1893 := by norm_num
  have hB0 : (0 : ℝ) ≤ 1.0064 * 0.7953 := by norm_num
  have hA4 : (1 : ℝ) ≤ 39 / 80 * (1.0064 * 1.1893) ^ 4 := by norm_num
  have hB4 : (1 : ℝ) ≤ 39 / 16 * (1.0064 * 0.7953) ^ 4 := by norm_num
  have b0 := phiA_child_le hwpos (by norm_num) hA0 hA4 hf'
  rw [hphi]
  generalize hQ : (8 / wA a s) ^ (1 / 4 : ℝ) = Q at *
  rcases Int.emod_two_eq_zero_or_one s.mu with hpar | hpar
  · -- `μ` even: both children at level `d`
    have ht' : 39 / 16 * wA a s ≤ wA a (stepA a s true) :=
      wA_true_ge_of_five_le a ha ha5 s hw8.le (by omega)
    have b1 := phiA_child_le hwpos (by norm_num) hB0 hB4 ht'
    rw [hQ] at b1
    rw [stepA_d_even a s hpar] at b0 b1
    generalize (2 / 3 : ℝ) ^ s.d = x at *
    have key : (1 + x) * (1.0064 * 1.1893) + (1 + x) * (1.0064 * 0.7953) ≤ 2 * (1 + x) := by
      nlinarith
    have := mul_le_mul_of_nonneg_right key hQ0
    linarith
  · obtain ⟨d, m⟩ := s
    simp only at hpar hmu hwpos hw8 hf' b0 hr0 ⊢
    cases d with
    | zero =>
      -- `μ` odd, level `0`: both children at level `1`
      have ht' : 39 / 80 * wA a ⟨0, m⟩ ≤ wA a (stepA a ⟨0, m⟩ true) :=
        wA_true_zero_ge_of_five_le a ha5 m hpar hw8.le
      have b1 := phiA_child_le hwpos (by norm_num) hA0 hA4 ht'
      rw [hQ] at b1
      rw [stepA_d_odd_false a ⟨0, m⟩ hpar] at b0
      rw [stepA_d_odd_true_zero a ⟨0, m⟩ hpar rfl] at b1
      norm_num at b0 b1 ⊢
      nlinarith
    | succ d' =>
      -- `μ` odd, level `d' + 1`: children at levels `d' + 2` and `d'`
      have ht' : 39 / 16 * wA a ⟨d' + 1, m⟩ ≤ wA a (stepA a ⟨d' + 1, m⟩ true) :=
        wA_true_ge_of_five_le a ha ha5 ⟨d' + 1, m⟩ hw8.le (by simp)
      have b1 := phiA_child_le hwpos (by norm_num) hB0 hB4 ht'
      rw [hQ] at b1
      rw [stepA_d_odd_false a ⟨d' + 1, m⟩ hpar] at b0
      rw [stepA_d_odd_true a ⟨d' + 1, m⟩ hpar (Nat.succ_pos d')] at b1
      simp only [Nat.add_sub_cancel] at b1
      have hx0 : (0 : ℝ) < (2 / 3 : ℝ) ^ d' := by positivity
      have e1 : (2 / 3 : ℝ) ^ (d' + 1) = 2 / 3 * (2 / 3 : ℝ) ^ d' := by ring
      have e2 : (2 / 3 : ℝ) ^ (d' + 1 + 1) = 4 / 9 * (2 / 3 : ℝ) ^ d' := by ring
      rw [e2] at b0
      rw [e1]
      generalize (2 / 3 : ℝ) ^ d' = x at *
      have key : (1 + 4 / 9 * x) * (1.0064 * 1.1893) + (1 + x) * (1.0064 * 0.7953)
          ≤ 2 * (1 + 2 / 3 * x) := by
        nlinarith
      have := mul_le_mul_of_nonneg_right key hQ0
      linarith

/-! ## The all-`true` orbit of `(0, 1)` is unbounded -/

/-- The family of states `(0, m)` and `(1, -m)`; `m ≥ 1` is the size. -/
def Fam (s : State) (m : ℤ) : Prop := s = ⟨0, m⟩ ∨ s = ⟨1, -m⟩

private theorem natCast_mul_emod_two (a : ℕ) (ha : a % 2 = 1) (m : ℤ) :
    (a : ℤ) * m % 2 = m % 2 := by
  have haZ : (a : ℤ) % 2 = 1 := by omega
  rw [Int.mul_emod, haZ, one_mul]
  omega

/-- One `true` step from `(0, m)`, `m ≥ 1`: a state of the family of size `m' ≥ (5m - 1)/2`. -/
theorem stepA_true_level_zero (a : ℕ) (ha : a % 2 = 1) (ha5 : 5 ≤ a) (m : ℤ) (hm : 1 ≤ m) :
    ∃ m' : ℤ, 1 ≤ m' ∧ 5 * m - 1 ≤ 2 * m' ∧ Fam (stepA a ⟨0, m⟩ true) m' := by
  have hA5 : (5 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha5
  have hp : 5 * m ≤ (a : ℤ) * m := mul_le_mul_of_nonneg_right hA5 (by omega)
  have hpm := natCast_mul_emod_two a ha m
  rcases Int.emod_two_eq_zero_or_one m with hpar | hpar
  · -- `m` even: `(0, a m / 2)`
    have hst : stepA a ⟨0, m⟩ true = ⟨0, (a : ℤ) * m / 2⟩ := by
      rw [stepA_even_true a 0 m hpar, State.norm_zero, pow_zero]
      have e : (a : ℤ) * m + 1 - 1 = (a : ℤ) * m := by ring
      rw [e, abs_of_nonneg]
      generalize (a : ℤ) * m = p at hp
      omega
    refine ⟨(a : ℤ) * m / 2, ?_, ?_, Or.inl hst⟩
    · generalize (a : ℤ) * m = p at hp hpm
      omega
    · generalize (a : ℤ) * m = p at hp hpm
      omega
  · -- `m` odd: `(1, -(a m - 1)/2)`
    have hst : stepA a ⟨0, m⟩ true = ⟨1, -(((a : ℤ) * m - 1) / 2)⟩ := by
      rw [stepA_odd_true_zero a m hpar]
      congr 1
      generalize (a : ℤ) * m = p at hp hpm
      omega
    refine ⟨((a : ℤ) * m - 1) / 2, ?_, ?_, Or.inr hst⟩
    · generalize (a : ℤ) * m = p at hp hpm
      omega
    · generalize (a : ℤ) * m = p at hp hpm
      omega

/-- One `true` step from `(1, -m)`, `m ≥ 1` even: `(1, -m')` with `m' ≥ m + 1`. -/
theorem stepA_true_level_one_even (a : ℕ) (ha : a % 2 = 1) (ha5 : 5 ≤ a) (m : ℤ) (hm : 1 ≤ m)
    (hpar : m % 2 = 0) : ∃ m' : ℤ, m + 1 ≤ m' ∧ stepA a ⟨1, -m⟩ true = ⟨1, -m'⟩ := by
  have hA5 : (5 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha5
  have haZ : (a : ℤ) % 2 = 1 := by omega
  have hp : 5 * m ≤ (a : ℤ) * m := mul_le_mul_of_nonneg_right hA5 (by omega)
  have hpm := natCast_mul_emod_two a ha m
  have hneg : (-m) % 2 = 0 := by omega
  refine ⟨((a : ℤ) * m + (a : ℤ) - 1) / 2, ?_, ?_⟩
  · generalize (a : ℤ) * m = p at hp hpm
    omega
  · rw [stepA_even_true a 1 (-m) hneg, State.norm_of_pos 1 _ (by norm_num), pow_one]
    congr 1
    have e : (a : ℤ) * -m = -((a : ℤ) * m) := by ring
    rw [e]
    generalize (a : ℤ) * m = p at hp hpm
    omega

/-- One `true` step from `(1, -m)`, `m ≥ 1` odd: `(0, (m + 1)/2)`. -/
theorem stepA_true_level_one_odd (a : ℕ) (m : ℤ) (hm : 1 ≤ m) (hpar : m % 2 = 1) :
    stepA a ⟨1, -m⟩ true = ⟨0, (m + 1) / 2⟩ := by
  have hneg : (-m) % 2 = 1 := by omega
  rw [stepA_odd_true_succ a 0 (-m) hneg, State.norm_zero, pow_zero]
  congr 1
  rw [abs_of_nonpos (by omega)]
  omega

/-- From a state of the family of size `m ≥ 1`, one or two `true` steps reach a state of the family
of size at least `m + 1`. -/
theorem fam_grow (a : ℕ) (ha : a % 2 = 1) (ha5 : 5 ≤ a) (s : State) (m : ℤ) (hm : 1 ≤ m)
    (h : Fam s m) : ∃ (w : List Bool) (m' : ℤ), m + 1 ≤ m' ∧ Fam (runA a s w) m' := by
  rcases h with rfl | rfl
  · obtain ⟨m', _, h2, h3⟩ := stepA_true_level_zero a ha ha5 m hm
    exact ⟨[true], m', by omega, h3⟩
  · rcases Int.emod_two_eq_zero_or_one m with hpar | hpar
    · obtain ⟨m', h1, h2⟩ := stepA_true_level_one_even a ha ha5 m hm hpar
      exact ⟨[true], m', h1, Or.inr h2⟩
    · have h1 := stepA_true_level_one_odd a m hm hpar
      obtain ⟨m', _, h3, h4⟩ := stepA_true_level_zero a ha ha5 ((m + 1) / 2) (by omega)
      refine ⟨[true, true], m', by omega, ?_⟩
      show Fam (stepA a (stepA a ⟨1, -m⟩ true) true) m'
      rw [h1]
      exact h4

/-- The family is reached from `(0, 1)` at arbitrarily large sizes. -/
theorem fam_reach (a : ℕ) (ha : a % 2 = 1) (ha5 : 5 ≤ a) :
    ∀ n : ℕ, ∃ (w : List Bool) (m : ℤ), (n : ℤ) + 1 ≤ m ∧ Fam (runA a ⟨0, 1⟩ w) m
  | 0 => ⟨[], 1, by norm_num, Or.inl rfl⟩
  | n + 1 => by
    obtain ⟨w, m, hm, hF⟩ := fam_reach a ha ha5 n
    obtain ⟨w', m', hm', hF'⟩ := fam_grow a ha ha5 _ m (by omega) hF
    refine ⟨w ++ w', m', by push_cast; omega, ?_⟩
    have e : runA a ⟨0, 1⟩ (w ++ w') = runA a (runA a ⟨0, 1⟩ w) w' := by
      unfold runA
      rw [List.foldl_append]
    rw [e]
    exact hF'

/-- At a state of the family of size `≥ 648 a` the potential is at most `2/3`. -/
theorem phiA_fam_le (a : ℕ) (ha1 : 1 ≤ a) (s : State) (m : ℤ) (hm : 648 * (a : ℤ) ≤ m)
    (h : Fam s m) : phiA a s ≤ 2 / 3 := by
  have hA1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  have hmR : 648 * (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hw : 648 ≤ wA a s ∧ 1 + (2 / 3 : ℝ) ^ s.d ≤ 2 := by
    rcases h with rfl | rfl
    · refine ⟨?_, by norm_num⟩
      simp only [wA, pow_zero, div_one]
      rw [abs_of_pos hm0]
      linarith
    · refine ⟨?_, by norm_num⟩
      simp only [wA, pow_one]
      push_cast
      rw [abs_neg, abs_of_pos hm0, le_div_iff₀ (by linarith)]
      linarith
  have hwpos : 0 < wA a s := by linarith [hw.1]
  have hmu : s.mu ≠ 0 := by
    intro h0
    simp [wA, h0] at hwpos
  have hq : (8 / wA a s) ^ (1 / 4 : ℝ) ≤ 1 / 3 := by
    refine rpow_quarter_le (by positivity) (by norm_num) ?_
    rw [div_le_iff₀ hwpos]
    have := hw.1
    norm_num
    linarith
  unfold phiA
  rw [if_neg hmu]
  refine (min_le_right _ _).trans ?_
  calc (1 + (2 / 3 : ℝ) ^ s.d) * (8 / wA a s) ^ (1 / 4 : ℝ)
      ≤ 2 * (1 / 3) := mul_le_mul hw.2 hq (Real.rpow_nonneg (by positivity) _) (by norm_num)
    _ = 2 / 3 := by norm_num

/-! ## Headlines -/

/-- Saturation for every odd multiplier `a ≥ 5`. -/
theorem saturation_odd (a : ℕ) (ha : a % 2 = 1) (ha5 : 5 ≤ a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, pAbs (stepA a) absorbed k ⟨0, 1⟩ ≤ 1 - ε := by
  obtain ⟨w, m, hm, hF⟩ := fam_reach a ha ha5 (648 * a)
  have hstar : phiA a (runA a ⟨0, 1⟩ w) ≤ 2 / 3 :=
    phiA_fam_le a (by omega) _ m (by push_cast at hm; omega) hF
  refine ⟨(1 / 2 : ℝ) ^ w.length * (1 / 3), by positivity, fun k => ?_⟩
  have hmono := pAbs_mono (stepA a) absorbed (stepA_absorbed a)
    (show k ≤ w.length + k by omega) ⟨0, 1⟩
  have hword := pAbs_word_le (stepA a) absorbed k w ⟨0, 1⟩
  have hphi := pAbs_le_of_super (stepA a) absorbed (phiA a) (phiA_nonneg a)
    (phiA_absorbed a).ge (phiA_super a ha ha5) k (runA a ⟨0, 1⟩ w)
  have hrun : List.foldl (stepA a) ⟨0, 1⟩ w = runA a ⟨0, 1⟩ w := rfl
  rw [hrun] at hword
  have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w.length := by positivity
  have hmul : (1 / 2 : ℝ) ^ w.length * (1 / 3)
      ≤ (1 / 2 : ℝ) ^ w.length * (1 - pAbs (stepA a) absorbed k (runA a ⟨0, 1⟩ w)) :=
    mul_le_mul_of_nonneg_left (by linarith) hpow
  linarith

open Classical in
/-- For every odd `a ≥ 5` a positive proportion of neighbouring classes never merge under
`x ↦ x/2, (a x + 1)/2`. -/
theorem odd_merged_bounded (a : ℕ) (ha : a % 2 = 1) (ha5 : 5 ≤ a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ,
      (((Finset.range (2 ^ k)).filter fun r : ℕ =>
        ∀ t : ℤ, (Ta a)^[k] ((r : ℤ) + 2 ^ k * t) = (Ta a)^[k] ((r : ℤ) + 2 ^ k * t + 1)).card : ℝ) ≤
        (1 - ε) * 2 ^ k := by
  obtain ⟨ε, hε, h⟩ := saturation_odd a ha ha5
  refine ⟨ε, hε, fun k => ?_⟩
  have heq : mergedA a ⟨0, 1⟩ k = (Finset.range (2 ^ k)).filter fun r : ℕ =>
      ∀ t : ℤ, (Ta a)^[k] ((r : ℤ) + 2 ^ k * t) = (Ta a)^[k] ((r : ℤ) + 2 ^ k * t + 1) := by
    unfold mergedA
    refine Finset.filter_congr fun r _ => ?_
    simp only [pow_zero, one_mul]
  rw [← heq, card_mergedA_eq a ha (by omega)]
  exact mul_le_mul_of_nonneg_right (h k) (by positivity)

/-- **3 is the only odd multiplier `≥ 3` for which neighbours merge with probability tending to 1.** -/
theorem absorbed_tendsto_one_iff (a : ℕ) (ha : a % 2 = 1) (ha3 : 3 ≤ a) :
    Tendsto (fun k => pAbs (stepA a) absorbed k ⟨0, 1⟩) atTop (𝓝 1) ↔ a = 3 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨ε, hε, hb⟩ := saturation_odd a ha (by omega)
    have h1 : (1 : ℝ) ≤ 1 - ε := le_of_tendsto' h hb
    linarith
  · rintro rfl
    have e : stepA 3 = step := funext fun s => funext fun c => stepA_three s c
    rw [e]
    exact absorbed_tendsto ⟨0, 1⟩

end Coalescence.Mult

#print axioms Coalescence.Mult.phiA_super
#print axioms Coalescence.Mult.saturation_odd
#print axioms Coalescence.Mult.odd_merged_bounded
#print axioms Coalescence.Mult.absorbed_tendsto_one_iff
