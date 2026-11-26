import CollatzCoalescence.Potential

/-!
# Rate potentials `Gam2` and `Gam`

`Gam2` is `V` without the `√d` term and `Gam s = d + Gam2 s`.  Above level `0` the function
`Gam2` is superharmonic, at level `0` outside `F` it drops by at least `1`, and `Gam` is
superharmonic off `F`.
-/

namespace Coalescence

/-- `V` without the `√d` term. -/
noncomputable def Gam2 (s : State) : ℝ :=
  A * (1 - lam ^ s.d) + theta ^ s.d / Real.sqrt 2 * (ell s : ℝ) + theta ^ s.d * Real.sqrt (size s)

noncomputable def Gam (s : State) : ℝ := (s.d : ℝ) + Gam2 s

/-! ### Basic facts about `Gam2` -/

theorem V_eq_sqrt_add_Gam2 (s : State) : V s = Real.sqrt s.d + Gam2 s := by
  unfold V Gam2
  ring

theorem Gam2_eq (s : State) :
    Gam2 s = A * (1 - lam ^ s.d) + theta ^ s.d * Real.sqrt (1 / 2) * (ell s : ℝ)
      + theta ^ s.d * Real.sqrt (size s) := by
  unfold Gam2
  rw [sqrt_half_eq]
  ring

theorem Gam2_of_d_zero (s : State) (h : s.d = 0) : Gam2 s = Real.sqrt (size s) := by
  rw [Gam2_eq, ell_of_d_zero s h, h]
  simp

theorem Gam2_le_of (s : State) (n : ℕ) (hn : s.d = n) (l σ : ℝ) (hl : (ell s : ℝ) ≤ l)
    (hσ : Real.sqrt (size s) ≤ σ) :
    Gam2 s ≤ A * (1 - lam ^ n) + theta ^ n * Real.sqrt (1 / 2) * l + theta ^ n * σ := by
  rw [Gam2_eq, hn]
  have hT := theta_pow_nonneg n
  have h1 : theta ^ n * Real.sqrt (1 / 2) * (ell s : ℝ) ≤ theta ^ n * Real.sqrt (1 / 2) * l :=
    mul_le_mul_of_nonneg_left hl (mul_nonneg hT sqrt_half_pos.le)
  have h2 : theta ^ n * Real.sqrt (size s) ≤ theta ^ n * σ := mul_le_mul_of_nonneg_left hσ hT
  linarith

theorem Gam2_nonneg (s : State) : 0 ≤ Gam2 s := by
  rw [Gam2_eq]
  have h1 := lam_pow_le_one s.d
  have h2 : 0 ≤ A * (1 - lam ^ s.d) := mul_nonneg (by unfold A; norm_num) (by linarith)
  have h3 := theta_pow_nonneg s.d
  have h4 : 0 ≤ theta ^ s.d * Real.sqrt (1 / 2) * (ell s : ℝ) :=
    mul_nonneg (mul_nonneg h3 sqrt_half_pos.le) (Nat.cast_nonneg _)
  have h5 : 0 ≤ theta ^ s.d * Real.sqrt (size s) := mul_nonneg h3 (Real.sqrt_nonneg _)
  linarith

/-! ### Levels of the children -/

theorem step_d_even (s : State) (h : s.mu % 2 = 0) (c : Bool) : (step s c).d = s.d := by
  obtain ⟨d, μ⟩ := s
  have hμ : μ % 2 = 0 := h
  cases c
  · rw [step_even_false d μ hμ, norm_d]
  · rw [step_even_true d μ hμ, norm_d]

theorem step_d_odd_false (s : State) (h : s.mu % 2 = 1) : (step s false).d = s.d + 1 := by
  obtain ⟨d, μ⟩ := s
  have hμ : μ % 2 = 1 := h
  rw [step_odd_false d μ hμ]

theorem step_d_odd_true (s : State) (h : s.mu % 2 = 1) (hd : 0 < s.d) :
    (step s true).d = s.d - 1 := by
  obtain ⟨d, μ⟩ := s
  have hμ : μ % 2 = 1 := h
  have hd' : 0 < d := hd
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [step_odd_true_succ d' μ hμ, norm_d]
  rfl

theorem step_d_odd_true_zero (s : State) (h : s.mu % 2 = 1) (hd : s.d = 0) :
    (step s true).d = 1 := by
  obtain ⟨d, μ⟩ := s
  have hμ : μ % 2 = 1 := h
  have hd' : d = 0 := hd
  subst hd'
  rw [step_odd_true_zero μ hμ]

/-! ### Above level `0` -/

/-- Level `d ≥ 1`, even offset: case (i) of `V_superharmonic` with the common `√d` removed. -/
theorem Gam2_super_even_pos (d : ℕ) (hd : 0 < d) (μ : ℤ) (hμ : μ % 2 = 0) :
    (Gam2 (step ⟨d, μ⟩ false) + Gam2 (step ⟨d, μ⟩ true)) / 2 ≤ Gam2 ⟨d, μ⟩ := by
  have h := super_even_pos d hd μ hμ
  have e0 : (step ⟨d, μ⟩ false).d = d := step_d_even ⟨d, μ⟩ hμ false
  have e1 : (step ⟨d, μ⟩ true).d = d := step_d_even ⟨d, μ⟩ hμ true
  have v0 := V_eq_sqrt_add_Gam2 (step ⟨d, μ⟩ false)
  have v1 := V_eq_sqrt_add_Gam2 (step ⟨d, μ⟩ true)
  have v : V ⟨d, μ⟩ = Real.sqrt d + Gam2 ⟨d, μ⟩ := V_eq_sqrt_add_Gam2 ⟨d, μ⟩
  rw [e0] at v0
  rw [e1] at v1
  linarith

/-- Level `d ≥ 1`, odd offset: case (ii) of `V_superharmonic` without the concavity step. -/
theorem Gam2_super_odd_pos (d' : ℕ) (μ : ℤ) (hμ : μ % 2 = 1) :
    (Gam2 (step ⟨d' + 1, μ⟩ false) + Gam2 (step ⟨d' + 1, μ⟩ true)) / 2 ≤ Gam2 ⟨d' + 1, μ⟩ := by
  have hs0 := sqrt_size_step_false ⟨d' + 1, μ⟩
  have hs1 := sqrt_size_step_true ⟨d' + 1, μ⟩
  have hd0 : (step ⟨d' + 1, μ⟩ false).d = d' + 2 := by rw [step_odd_false _ _ hμ]
  have hd1 : (step ⟨d' + 1, μ⟩ true).d = d' := by rw [step_odd_true_succ _ _ hμ, norm_d]
  have hl0 : (ell (step ⟨d' + 1, μ⟩ false) : ℝ) ≤ 2 * ((d' : ℝ) + 2) := by
    have h := ell_le (step ⟨d' + 1, μ⟩ false)
    rw [hd0] at h
    exact_mod_cast h
  have hl1 : (ell (step ⟨d' + 1, μ⟩ true) : ℝ) ≤ 2 * (d' : ℝ) := by
    have h := ell_le (step ⟨d' + 1, μ⟩ true)
    rw [hd1] at h
    exact_mod_cast h
  have hV0 := Gam2_le_of _ (d' + 2) hd0 _ _ hl0 hs0
  have hV1 := Gam2_le_of _ d' hd1 _ _ hl1 hs1
  have hell : ell ⟨d' + 1, μ⟩ = 0 := (ell_eq_zero_iff ⟨d' + 1, μ⟩ (Nat.succ_pos _)).mpr hμ
  rw [Gam2_eq ⟨d' + 1, μ⟩, hell]
  simp only
  have hT2 : theta ^ (d' + 2) = theta ^ d' * (361 / 400) := by
    rw [pow_add]
    unfold theta
    norm_num
  have hT1 : theta ^ (d' + 1) = theta ^ d' * (19 / 20) := by
    rw [pow_add]
    unfold theta
    norm_num
  have hL2 : lam ^ (d' + 2) = lam ^ d' * (1521 / 1600) := by
    rw [pow_add]
    unfold lam
    norm_num
  have hL1 : lam ^ (d' + 1) = lam ^ d' * (39 / 40) := by
    rw [pow_add]
    unfold lam
    norm_num
  have hA : A = 250000 := rfl
  have hB := theta_lam_bernoulli d'
  rw [hT2, hL2, hA] at hV0
  rw [hA] at hV1
  rw [hT1, hL1, hA, Nat.cast_zero]
  have hT := theta_pow_nonneg d'
  have hL := lam_pow_nonneg d'
  have hk := sqrt_half_pos
  have hk' := sqrt_half_lt
  have h32 := sqrt_three_half_lt
  have hσ := Real.sqrt_nonneg (size ⟨d' + 1, μ⟩)
  have hn : (0 : ℝ) ≤ (d' : ℝ) := Nat.cast_nonneg _
  generalize theta ^ d' = T at *
  generalize lam ^ d' = L at *
  generalize Real.sqrt (1 / 2) = k at *
  generalize Real.sqrt (3 / 2) = r at *
  generalize Real.sqrt (size ⟨d' + 1, μ⟩) = σ at *
  generalize Gam2 (step ⟨d' + 1, μ⟩ false) = G0 at *
  generalize Gam2 (step ⟨d' + 1, μ⟩ true) = G1 at *
  generalize (d' : ℝ) = n at *
  have hTk : 0 ≤ T * k := mul_nonneg hT hk.le
  have hTkn : 0 ≤ T * k * n := mul_nonneg hTk hn
  have hTσ : 0 ≤ T * σ := mul_nonneg hT hσ
  have p2 : T * σ * (361 / 400 * k + r) ≤ T * σ * (19 / 10) :=
    mul_le_mul_of_nonneg_left (by linarith) hTσ
  have p3 : k * (T * (2 * n + 3)) ≤ k * (76 * L) := mul_le_mul_of_nonneg_left hB hk.le
  have p4 : k * L ≤ 0.7072 * L := mul_le_mul_of_nonneg_right hk'.le hL
  linarith

/-! ### Level `0` outside `F` -/

/-- Level `0`, even offset outside `F`. -/
theorem Gam2_drop_even_zero (μ : ℤ) (hμ : μ % 2 = 0) (hM : M < |μ|) :
    (Gam2 (step ⟨0, μ⟩ false) + Gam2 (step ⟨0, μ⟩ true)) / 2 + 1 ≤ Gam2 ⟨0, μ⟩ := by
  have hs0 := sqrt_size_step_false ⟨0, μ⟩
  have hs1 := sqrt_size_step_true ⟨0, μ⟩
  have hd0 : (step ⟨0, μ⟩ false).d = 0 := by rw [step_even_false _ _ hμ, norm_d]
  have hd1 : (step ⟨0, μ⟩ true).d = 0 := by rw [step_even_true _ _ hμ, norm_d]
  rw [Gam2_of_d_zero _ hd0, Gam2_of_d_zero _ hd1, Gam2_of_d_zero ⟨0, μ⟩ rfl]
  have hσ := sqrt_size_zero_ge μ hM
  have hk := sqrt_half_pos
  have hk' := sqrt_half_lt
  have h32 := sqrt_three_half_lt
  generalize Real.sqrt (1 / 2) = k at *
  generalize Real.sqrt (3 / 2) = r at *
  generalize Real.sqrt (size ⟨0, μ⟩) = σ at *
  have p1 : k * σ ≤ 0.7072 * σ := mul_le_mul_of_nonneg_right hk'.le (by linarith)
  have p2 : r * σ ≤ 1.2248 * σ := mul_le_mul_of_nonneg_right h32.le (by linarith)
  linarith

/-- Level `0`, odd offset outside `F`. -/
theorem Gam2_drop_odd_zero (μ : ℤ) (hμ : μ % 2 = 1) (hM : M < |μ|) :
    (Gam2 (step ⟨0, μ⟩ false) + Gam2 (step ⟨0, μ⟩ true)) / 2 + 1 ≤ Gam2 ⟨0, μ⟩ := by
  have key : ∀ c : Bool, Gam2 (step ⟨0, μ⟩ c) + 1 ≤ Gam2 ⟨0, μ⟩ := by
    intro c
    have hs := sqrt_size_step_zero_odd μ hμ c
    have hd : (step ⟨0, μ⟩ c).d = 1 := by
      cases c
      · rw [step_odd_false _ _ hμ]
      · rw [step_odd_true_zero _ hμ]
    have hl : (ell (step ⟨0, μ⟩ c) : ℝ) ≤ 2 := by
      have h := ell_le (step ⟨0, μ⟩ c)
      rw [hd] at h
      exact_mod_cast h
    have hV := Gam2_le_of _ 1 hd _ _ hl hs
    rw [Gam2_of_d_zero ⟨0, μ⟩ rfl]
    have hA : A = 250000 := rfl
    have hth : theta = 19 / 20 := rfl
    have hlam : lam = 39 / 40 := rfl
    rw [pow_one, pow_one, hA, hth, hlam] at hV
    have hσ := sqrt_size_zero_ge μ hM
    have hk := sqrt_half_pos
    have hk' := sqrt_half_lt
    generalize Real.sqrt (1 / 2) = k at *
    generalize Real.sqrt (size ⟨0, μ⟩) = σ at *
    have p1 : σ * k ≤ σ * 0.7072 := mul_le_mul_of_nonneg_left hk'.le (by linarith)
    linarith
  have h0 := key false
  have h1 := key true
  linarith

/-! ### Headlines -/

/-- Above level 0, `Gam2` is superharmonic (no condition on `F`). -/
theorem Gam2_super_pos (s : State) (hd : 0 < s.d) :
    (Gam2 (step s false) + Gam2 (step s true)) / 2 ≤ Gam2 s := by
  obtain ⟨d, μ⟩ := s
  have hd' : 0 < d := hd
  rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
  · exact Gam2_super_even_pos d hd' μ hμ
  · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    exact Gam2_super_odd_pos d' μ hμ

/-- At level 0 outside `F`, `Gam2` drops by at least `1`. -/
theorem Gam2_drop_zero (s : State) (hd : s.d = 0) (hs : s ∉ F) :
    (Gam2 (step s false) + Gam2 (step s true)) / 2 + 1 ≤ Gam2 s := by
  obtain ⟨d, μ⟩ := s
  have hd' : d = 0 := hd
  subst hd'
  have hM : M < |μ| := by
    by_contra h
    exact hs ((mem_F _).mpr ⟨rfl, not_lt.mp h⟩)
  rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
  · exact Gam2_drop_even_zero μ hμ hM
  · exact Gam2_drop_odd_zero μ hμ hM

theorem Gam_super (s : State) (hs : s ∉ F) :
    (Gam (step s false) + Gam (step s true)) / 2 ≤ Gam s := by
  unfold Gam
  rcases Nat.eq_zero_or_pos s.d with hd | hd
  · have h := Gam2_drop_zero s hd hs
    rcases Int.emod_two_eq_zero_or_one s.mu with hμ | hμ
    · rw [step_d_even s hμ false, step_d_even s hμ true]
      linarith
    · rw [step_d_odd_false s hμ, step_d_odd_true_zero s hμ hd, hd]
      push_cast
      linarith
  · have h := Gam2_super_pos s hd
    rcases Int.emod_two_eq_zero_or_one s.mu with hμ | hμ
    · rw [step_d_even s hμ false, step_d_even s hμ true]
      linarith
    · have hc : ((s.d - 1 : ℕ) : ℝ) = (s.d : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ s.d), Nat.cast_one]
      rw [step_d_odd_false s hμ, step_d_odd_true s hμ hd, hc]
      push_cast
      linarith

end Coalescence

#print axioms Coalescence.Gam2_nonneg
#print axioms Coalescence.V_eq_sqrt_add_Gam2
#print axioms Coalescence.Gam2_super_pos
#print axioms Coalescence.Gam2_drop_zero
#print axioms Coalescence.Gam_super
#print axioms Coalescence.step_d_even
#print axioms Coalescence.step_d_odd_false
#print axioms Coalescence.step_d_odd_true
#print axioms Coalescence.step_d_odd_true_zero
