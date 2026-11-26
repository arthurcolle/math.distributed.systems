import CollatzCoalescence.Chain
import CollatzCoalescence.Ell

/-!
# The potential `V` is superharmonic off the finite set `F`

Covers Proposition `super` of `main.tex` (Section 4): for every state `s ∉ F`,
`(V (step s false) + V (step s true)) / 2 ≤ V s`, together with `0 ≤ V`, `√d ≤ V` and
`√|μ| ≤ V (0, μ)`.
-/

namespace Coalescence

/-! ### Numerical constants -/

theorem sqrt_half_eq : Real.sqrt (1 / 2) = (Real.sqrt 2)⁻¹ := by
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.sqrt_inv]

theorem sqrt_half_pos : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt_half_lt : Real.sqrt (1 / 2) < 0.7072 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

theorem sqrt_three_half_lt : Real.sqrt (3 / 2) < 1.2248 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

theorem sqrt_sixth_lt : Real.sqrt (1 / 6) < 0.41 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

theorem theta_pow_nonneg (n : ℕ) : 0 ≤ theta ^ n := pow_nonneg (by unfold theta; norm_num) n

theorem lam_pow_nonneg (n : ℕ) : 0 ≤ lam ^ n := pow_nonneg (by unfold lam; norm_num) n

theorem lam_pow_le_one (n : ℕ) : lam ^ n ≤ 1 :=
  pow_le_one₀ (by unfold lam; norm_num) (by unfold lam; norm_num)

theorem sqrt_add_le_add (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-! ### `size` and the domination inequality over `ℝ` -/

theorem size_eq_w (s : State) : size s = ((w s : ℚ) : ℝ) := by
  simp [size, w]

theorem size_nonneg (s : State) : 0 ≤ size s := by
  unfold size
  positivity

theorem size_step_false (s : State) : size (step s false) ≤ 1 / 2 * size s + 1 / 2 := by
  have h := step_dom s false
  have ha : a false = 1 / 2 := by simp [a]
  rw [ha] at h
  have h' : ((w (step s false) : ℚ) : ℝ) ≤ ((1 / 2 * w s + 1 / 2 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  rw [size_eq_w, size_eq_w]
  exact h'

theorem size_step_true (s : State) : size (step s true) ≤ 3 / 2 * size s + 1 / 2 := by
  have h := step_dom s true
  have ha : a true = 3 / 2 := by simp [a]
  rw [ha] at h
  have h' : ((w (step s true) : ℚ) : ℝ) ≤ ((3 / 2 * w s + 1 / 2 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  rw [size_eq_w, size_eq_w]
  exact h'

theorem size_step_zero_odd (m : ℤ) (hm : m % 2 = 1) (c : Bool) :
    size (step ⟨0, m⟩ c) ≤ size ⟨0, m⟩ * (1 / 2) + 1 / 6 := by
  have h := step_dom_zero_odd' m hm c
  have h' : ((w (step ⟨0, m⟩ c) : ℚ) : ℝ) ≤ ((w ⟨0, m⟩ / 2 + 1 / 6 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  rw [size_eq_w, size_eq_w]
  linarith

theorem sqrt_size_step_false (s : State) :
    Real.sqrt (size (step s false))
      ≤ Real.sqrt (1 / 2) * Real.sqrt (size s) + Real.sqrt (1 / 2) := by
  have h0 := size_nonneg s
  calc Real.sqrt (size (step s false))
      ≤ Real.sqrt (1 / 2 * size s + 1 / 2) := Real.sqrt_le_sqrt (size_step_false s)
    _ ≤ Real.sqrt (1 / 2 * size s) + Real.sqrt (1 / 2) :=
        sqrt_add_le_add _ _ (by positivity) (by norm_num)
    _ = Real.sqrt (1 / 2) * Real.sqrt (size s) + Real.sqrt (1 / 2) := by
        rw [Real.sqrt_mul (by norm_num)]

theorem sqrt_size_step_true (s : State) :
    Real.sqrt (size (step s true))
      ≤ Real.sqrt (3 / 2) * Real.sqrt (size s) + Real.sqrt (1 / 2) := by
  have h0 := size_nonneg s
  calc Real.sqrt (size (step s true))
      ≤ Real.sqrt (3 / 2 * size s + 1 / 2) := Real.sqrt_le_sqrt (size_step_true s)
    _ ≤ Real.sqrt (3 / 2 * size s) + Real.sqrt (1 / 2) :=
        sqrt_add_le_add _ _ (by positivity) (by norm_num)
    _ = Real.sqrt (3 / 2) * Real.sqrt (size s) + Real.sqrt (1 / 2) := by
        rw [Real.sqrt_mul (by norm_num)]

theorem sqrt_size_step_zero_odd (m : ℤ) (hm : m % 2 = 1) (c : Bool) :
    Real.sqrt (size (step ⟨0, m⟩ c))
      ≤ Real.sqrt (size ⟨0, m⟩) * Real.sqrt (1 / 2) + 0.41 := by
  have h0 := size_nonneg ⟨0, m⟩
  calc Real.sqrt (size (step ⟨0, m⟩ c))
      ≤ Real.sqrt (size ⟨0, m⟩ * (1 / 2) + 1 / 6) :=
        Real.sqrt_le_sqrt (size_step_zero_odd m hm c)
    _ ≤ Real.sqrt (size ⟨0, m⟩ * (1 / 2)) + Real.sqrt (1 / 6) :=
        sqrt_add_le_add _ _ (by positivity) (by norm_num)
    _ = Real.sqrt (size ⟨0, m⟩) * Real.sqrt (1 / 2) + Real.sqrt (1 / 6) := by
        rw [Real.sqrt_mul h0]
    _ ≤ Real.sqrt (size ⟨0, m⟩) * Real.sqrt (1 / 2) + 0.41 := by
        linarith [sqrt_sixth_lt]

theorem sqrt_size_zero_ge (μ : ℤ) (hM : M < |μ|) : 20000 ≤ Real.sqrt (size ⟨0, μ⟩) := by
  have h1 : ((M : ℤ) : ℝ) < ((|μ| : ℤ) : ℝ) := by exact_mod_cast hM
  have h2 : (400000000 : ℝ) < |(μ : ℝ)| := by
    have hMe : ((M : ℤ) : ℝ) = 400000000 := by
      unfold M
      norm_num
    rw [hMe, Int.cast_abs] at h1
    exact h1
  have h3 : size ⟨0, μ⟩ = |(μ : ℝ)| := by simp [size]
  rw [h3, Real.le_sqrt' (by norm_num)]
  norm_num
  linarith

/-! ### Basic facts about `V` -/

theorem norm_d (s : State) : s.norm.d = s.d := by
  unfold State.norm
  split_ifs with h
  · exact h.symm
  · rfl

theorem ell_of_d_zero (s : State) (h : s.d = 0) : ell s = 0 := by
  simp [ell, h]

theorem V_eq (s : State) :
    V s = Real.sqrt s.d + A * (1 - lam ^ s.d) + theta ^ s.d * Real.sqrt (1 / 2) * (ell s : ℝ)
      + theta ^ s.d * Real.sqrt (size s) := by
  unfold V
  rw [sqrt_half_eq]
  ring

theorem V_of_d_zero (s : State) (h : s.d = 0) : V s = Real.sqrt (size s) := by
  rw [V_eq, ell_of_d_zero s h, h]
  simp

theorem V_le_of (s : State) (n : ℕ) (hn : s.d = n) (l σ : ℝ) (hl : (ell s : ℝ) ≤ l)
    (hσ : Real.sqrt (size s) ≤ σ) :
    V s ≤ Real.sqrt n + A * (1 - lam ^ n) + theta ^ n * Real.sqrt (1 / 2) * l + theta ^ n * σ := by
  rw [V_eq, hn]
  have hT := theta_pow_nonneg n
  have h1 : theta ^ n * Real.sqrt (1 / 2) * (ell s : ℝ) ≤ theta ^ n * Real.sqrt (1 / 2) * l :=
    mul_le_mul_of_nonneg_left hl (mul_nonneg hT sqrt_half_pos.le)
  have h2 : theta ^ n * Real.sqrt (size s) ≤ theta ^ n * σ := mul_le_mul_of_nonneg_left hσ hT
  linarith

theorem V_nonneg (s : State) : 0 ≤ V s := by
  rw [V_eq]
  have h1 := lam_pow_le_one s.d
  have h2 : 0 ≤ A * (1 - lam ^ s.d) := mul_nonneg (by unfold A; norm_num) (by linarith)
  have h3 := theta_pow_nonneg s.d
  have h4 : 0 ≤ theta ^ s.d * Real.sqrt (1 / 2) * (ell s : ℝ) :=
    mul_nonneg (mul_nonneg h3 sqrt_half_pos.le) (Nat.cast_nonneg _)
  have h5 : 0 ≤ theta ^ s.d * Real.sqrt (size s) := mul_nonneg h3 (Real.sqrt_nonneg _)
  have h6 := Real.sqrt_nonneg (s.d : ℝ)
  linarith

theorem sqrt_le_V (s : State) : Real.sqrt s.d ≤ V s := by
  rw [V_eq]
  have h1 := lam_pow_le_one s.d
  have h2 : 0 ≤ A * (1 - lam ^ s.d) := mul_nonneg (by unfold A; norm_num) (by linarith)
  have h3 := theta_pow_nonneg s.d
  have h4 : 0 ≤ theta ^ s.d * Real.sqrt (1 / 2) * (ell s : ℝ) :=
    mul_nonneg (mul_nonneg h3 sqrt_half_pos.le) (Nat.cast_nonneg _)
  have h5 : 0 ≤ theta ^ s.d * Real.sqrt (size s) := mul_nonneg h3 (Real.sqrt_nonneg _)
  linarith

theorem sqrt_mu_le_V (μ : ℤ) : Real.sqrt |(μ : ℝ)| ≤ V ⟨0, μ⟩ := by
  rw [V_of_d_zero _ rfl]
  simp [size]

/-! ### The four cases of Proposition `super` -/

/-- Case (i): level `d ≥ 1`, even offset. -/
theorem super_even_pos (d : ℕ) (hd : 0 < d) (μ : ℤ) (hμ : μ % 2 = 0) :
    (V (step ⟨d, μ⟩ false) + V (step ⟨d, μ⟩ true)) / 2 ≤ V ⟨d, μ⟩ := by
  have hs0 := sqrt_size_step_false ⟨d, μ⟩
  have hs1 := sqrt_size_step_true ⟨d, μ⟩
  rw [step_even_false d μ hμ, State.norm_of_pos d _ hd] at hs0 ⊢
  rw [step_even_true d μ hμ, State.norm_of_pos d _ hd] at hs1 ⊢
  have hell := ell_even_step d hd μ hμ
  have hell' : (ell ⟨d, μ / 2⟩ : ℝ) + (ell ⟨d, (3 * μ + 1 - 3 ^ d) / 2⟩ : ℝ) + 2
      ≤ 2 * (ell ⟨d, μ⟩ : ℝ) := by exact_mod_cast hell
  rw [V_eq, V_eq, V_eq]
  simp only
  have hT := theta_pow_nonneg d
  have hk := sqrt_half_pos
  have hk' := sqrt_half_lt
  have h32 := sqrt_three_half_lt
  have hσ := Real.sqrt_nonneg (size ⟨d, μ⟩)
  generalize theta ^ d = T at *
  generalize Real.sqrt (1 / 2) = k at *
  generalize Real.sqrt (3 / 2) = r at *
  generalize Real.sqrt (size ⟨d, μ⟩) = σ at *
  generalize Real.sqrt (size ⟨d, μ / 2⟩) = σ0 at *
  generalize Real.sqrt (size ⟨d, (3 * μ + 1 - 3 ^ d) / 2⟩) = σ1 at *
  generalize (ell ⟨d, μ⟩ : ℝ) = l at *
  generalize (ell ⟨d, μ / 2⟩ : ℝ) = l0 at *
  generalize (ell ⟨d, (3 * μ + 1 - 3 ^ d) / 2⟩ : ℝ) = l1 at *
  have h1 : T * k * (l0 + l1) ≤ T * k * (2 * l - 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hT hk.le)
  have h3 : (k + r) * σ ≤ 2 * σ := mul_le_mul_of_nonneg_right (by linarith) hσ
  have h2 : T * (σ0 + σ1) ≤ T * (2 * σ + 2 * k) :=
    mul_le_mul_of_nonneg_left (by linarith) hT
  linarith

/-- Bernoulli step: `(1 + 2d) θ^(d-1) ≤ 76 λ^(d-1)` with `d = d' + 1`. -/
theorem theta_lam_bernoulli (d' : ℕ) : theta ^ d' * (2 * (d' : ℝ) + 3) ≤ 76 * lam ^ d' := by
  have hb : 1 + (d' : ℝ) * (1 / 38) ≤ (1 + 1 / 38 : ℝ) ^ d' :=
    one_add_mul_le_pow (by norm_num) d'
  have hL : lam ^ d' = theta ^ d' * (1 + 1 / 38 : ℝ) ^ d' := by
    rw [← mul_pow]
    congr 1
    unfold lam theta
    norm_num
  have hT := theta_pow_nonneg d'
  have h := mul_le_mul_of_nonneg_left hb hT
  rw [hL]
  nlinarith

/-- Concavity of the square root at consecutive integers. -/
theorem sqrt_mid (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x + 2) + Real.sqrt x ≤ 2 * Real.sqrt (x + 1) := by
  have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ x + 2 by linarith)
  have h2 := Real.sq_sqrt hx
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by linarith)
  have p1 := Real.sqrt_nonneg (x + 2)
  have p2 := Real.sqrt_nonneg x
  have p3 := Real.sqrt_nonneg (x + 1)
  generalize Real.sqrt (x + 2) = u at *
  generalize Real.sqrt x = v at *
  generalize Real.sqrt (x + 1) = z at *
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [sq_nonneg (u - v), mul_pos (sub_pos.mpr hcon) (show 0 < u + v + 2 * z by linarith)]

/-- Case (ii): level `d ≥ 1`, odd offset. -/
theorem super_odd_pos (d' : ℕ) (μ : ℤ) (hμ : μ % 2 = 1) :
    (V (step ⟨d' + 1, μ⟩ false) + V (step ⟨d' + 1, μ⟩ true)) / 2 ≤ V ⟨d' + 1, μ⟩ := by
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
  have hV0 := V_le_of _ (d' + 2) hd0 _ _ hl0 hs0
  have hV1 := V_le_of _ d' hd1 _ _ hl1 hs1
  have hell : ell ⟨d' + 1, μ⟩ = 0 := (ell_eq_zero_iff ⟨d' + 1, μ⟩ (Nat.succ_pos _)).mpr hμ
  rw [V_eq ⟨d' + 1, μ⟩, hell]
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
  have hmid := sqrt_mid (d' : ℝ) (Nat.cast_nonneg _)
  rw [hT2, hL2, hA] at hV0
  rw [hA] at hV1
  rw [hT1, hL1, hA]
  push_cast at hV0 ⊢
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
  generalize V (step ⟨d' + 1, μ⟩ false) = V0 at *
  generalize V (step ⟨d' + 1, μ⟩ true) = V1 at *
  generalize Real.sqrt ((d' : ℝ) + 2) = x at *
  generalize Real.sqrt (d' : ℝ) = y at *
  generalize Real.sqrt ((d' : ℝ) + 1) = z at *
  generalize (d' : ℝ) = n at *
  have hTk : 0 ≤ T * k := mul_nonneg hT hk.le
  have hTkn : 0 ≤ T * k * n := mul_nonneg hTk hn
  have hTσ : 0 ≤ T * σ := mul_nonneg hT hσ
  have p2 : T * σ * (361 / 400 * k + r) ≤ T * σ * (19 / 10) :=
    mul_le_mul_of_nonneg_left (by linarith) hTσ
  have p3 : k * (T * (2 * n + 3)) ≤ k * (76 * L) := mul_le_mul_of_nonneg_left hB hk.le
  have p4 : k * L ≤ 0.7072 * L := mul_le_mul_of_nonneg_right hk'.le hL
  linarith

/-- Case (iii): level `0`, even offset outside `F`. -/
theorem super_even_zero (μ : ℤ) (hμ : μ % 2 = 0) (hM : M < |μ|) :
    (V (step ⟨0, μ⟩ false) + V (step ⟨0, μ⟩ true)) / 2 ≤ V ⟨0, μ⟩ := by
  have hs0 := sqrt_size_step_false ⟨0, μ⟩
  have hs1 := sqrt_size_step_true ⟨0, μ⟩
  have hd0 : (step ⟨0, μ⟩ false).d = 0 := by rw [step_even_false _ _ hμ, norm_d]
  have hd1 : (step ⟨0, μ⟩ true).d = 0 := by rw [step_even_true _ _ hμ, norm_d]
  rw [V_of_d_zero _ hd0, V_of_d_zero _ hd1, V_of_d_zero ⟨0, μ⟩ rfl]
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

/-- Case (iv): level `0`, odd offset outside `F`. -/
theorem super_odd_zero (μ : ℤ) (hμ : μ % 2 = 1) (hM : M < |μ|) :
    (V (step ⟨0, μ⟩ false) + V (step ⟨0, μ⟩ true)) / 2 ≤ V ⟨0, μ⟩ := by
  have key : ∀ c : Bool, V (step ⟨0, μ⟩ c) ≤ V ⟨0, μ⟩ := by
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
    have hV := V_le_of _ 1 hd _ _ hl hs
    rw [V_of_d_zero ⟨0, μ⟩ rfl]
    have hA : A = 250000 := rfl
    have hth : theta = 19 / 20 := rfl
    have hlam : lam = 39 / 40 := rfl
    rw [pow_one, pow_one, hA, hth, hlam, Nat.cast_one, Real.sqrt_one] at hV
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

/-! ### Headline -/

theorem V_superharmonic (s : State) (hs : s ∉ F) :
    (V (step s false) + V (step s true)) / 2 ≤ V s := by
  obtain ⟨d, μ⟩ := s
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hM : M < |μ| := by
      by_contra h
      exact hs ((mem_F _).mpr ⟨rfl, not_lt.mp h⟩)
    rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
    · exact super_even_zero μ hμ hM
    · exact super_odd_zero μ hμ hM
  · rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
    · exact super_even_pos d hd μ hμ
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      exact super_odd_pos d' μ hμ

end Coalescence

#print axioms Coalescence.V_nonneg
#print axioms Coalescence.sqrt_le_V
#print axioms Coalescence.sqrt_mu_le_V
#print axioms Coalescence.V_superharmonic
