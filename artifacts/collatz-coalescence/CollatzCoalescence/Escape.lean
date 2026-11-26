import CollatzCoalescence.Ell

/-!
# Escape from the sublevel sets of `V`

From every state outside `F` with `V < Λ`, some coin word of bounded length (depending only on
`Λ`) reaches `F` or a state with `V ≥ Λ`.  See `main.tex`, proof of Lemma `hitF`.
-/

namespace Coalescence

/-! ### Elementary lower bounds on `V` -/

theorem esc_sqrt_le_V (s : State) : Real.sqrt s.d ≤ V s := by
  unfold V
  have hlam : lam ^ s.d ≤ 1 := pow_le_one₀ (by norm_num [lam]) (by norm_num [lam])
  have hA : (0 : ℝ) ≤ A := by norm_num [A]
  have h1 : 0 ≤ A * (1 - lam ^ s.d) := mul_nonneg hA (by linarith)
  have hθ : (0 : ℝ) ≤ theta ^ s.d := pow_nonneg (by norm_num [theta]) _
  have h2 : 0 ≤ theta ^ s.d / Real.sqrt 2 * (ell s : ℝ) :=
    mul_nonneg (div_nonneg hθ (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
  have h3 : 0 ≤ theta ^ s.d * Real.sqrt (size s) := mul_nonneg hθ (Real.sqrt_nonneg _)
  linarith

theorem esc_sqrt_mu_le_V (μ : ℤ) : Real.sqrt |(μ : ℝ)| ≤ V ⟨0, μ⟩ := by
  simp [V, ell, size]

/-! ### The budget -/

/-- The budget: it strictly decreases along the escape strategy. -/
def escB (D : ℕ) (s : State) : ℕ :=
  (∑ d' ∈ Finset.Ico s.d (D + 1), (2 * d' + 3)) + ell s + (if s.d = 0 then s.mu.natAbs else 0)

section Strategy

variable (hle : ∀ s : State, ell s ≤ 2 * s.d)
variable (heven : ∀ d : ℕ, 0 < d → ∀ μ : ℤ, μ % 2 = 0 →
  ell ⟨d, μ / 2⟩ + ell ⟨d, (3 * μ + 1 - 3 ^ d) / 2⟩ + 2 ≤ 2 * ell ⟨d, μ⟩)

include hle heven

/-- One coin of the escape strategy lowers the budget. -/
theorem esc_step_aux (D : ℕ) (s : State) (hF : s ∉ F) (hd : s.d ≤ D) :
    ∃ c : Bool, escB D (step s c) < escB D s := by
  obtain ⟨d, μ⟩ := s
  simp only at hd
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
    · refine ⟨false, ?_⟩
      rw [step_even_false _ _ hμ, State.norm_zero]
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        apply hF
        rw [mem_F]
        simp [M]
      simp only [escB, ell, if_true, Int.natAbs_abs]
      omega
    · refine ⟨false, ?_⟩
      rw [step_odd_false _ _ hμ]
      have h1 := hle ⟨0 + 1, (3 * μ + 1) / 2⟩
      have h2 := Finset.sum_eq_sum_Ico_succ_bot (show 0 < D + 1 by omega) (fun d' => 2 * d' + 3)
      simp only [escB, ell, if_true] at h1 h2 ⊢
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] at h1 h2 ⊢
      omega
  · have hne : d ≠ 0 := by omega
    rcases Int.emod_two_eq_zero_or_one μ with hμ | hμ
    · have h := heven d hdpos μ hμ
      by_cases hc : ell ⟨d, μ / 2⟩ < ell ⟨d, μ⟩
      · refine ⟨false, ?_⟩
        rw [step_even_false _ _ hμ, State.norm_of_pos _ _ hdpos]
        simp only [escB, hne, if_false]
        omega
      · refine ⟨true, ?_⟩
        rw [step_even_true _ _ hμ, State.norm_of_pos _ _ hdpos]
        simp only [escB, hne, if_false]
        omega
    · refine ⟨false, ?_⟩
      rw [step_odd_false _ _ hμ]
      have h1 := hle ⟨d + 1, (3 * μ + 1) / 2⟩
      have h2 := Finset.sum_eq_sum_Ico_succ_bot (show d < D + 1 by omega) (fun d' => 2 * d' + 3)
      simp only [escB, hne, if_false, Nat.add_eq_zero_iff, one_ne_zero, and_false] at h1 h2 ⊢
      omega

/-- Following the strategy reaches `F` or level `D` within `escB D s` steps. -/
theorem esc_reach_aux (D : ℕ) : ∀ n : ℕ, ∀ s : State, escB D s ≤ n →
    ∃ w : List Bool, w.length ≤ n ∧ (run s w ∈ F ∨ D ≤ (run s w).d) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    by_cases hF : s ∈ F
    · exact ⟨[], le_rfl, Or.inl hF⟩
    by_cases hD : D ≤ s.d
    · exact ⟨[], le_rfl, Or.inr hD⟩
    obtain ⟨c, hc⟩ := esc_step_aux hle heven D s hF (by omega)
    omega
  | succ n ih =>
    intro s hs
    by_cases hF : s ∈ F
    · exact ⟨[], Nat.zero_le _, Or.inl hF⟩
    by_cases hD : D ≤ s.d
    · exact ⟨[], Nat.zero_le _, Or.inr hD⟩
    obtain ⟨c, hc⟩ := esc_step_aux hle heven D s hF (by omega)
    obtain ⟨w, hw, h⟩ := ih (step s c) (by omega)
    exact ⟨c :: w, by simpa using hw, h⟩

theorem escape_aux (Λ : ℝ) : ∃ L : ℕ, ∀ s : State, s ∉ F → V s < Λ →
    ∃ w : List Bool, w.length ≤ L ∧ (run s w ∈ F ∨ Λ ≤ V (run s w)) := by
  obtain ⟨D, hD⟩ := exists_nat_ge (Λ ^ 2)
  refine ⟨(∑ d' ∈ Finset.range (D + 1), (2 * d' + 3)) + 2 * D + D, ?_⟩
  intro s hF hV
  have hΛ : 0 < Λ := lt_of_le_of_lt ((Real.sqrt_nonneg _).trans (esc_sqrt_le_V s)) hV
  have hd : s.d < D := by
    have h1 : Real.sqrt s.d < Λ := lt_of_le_of_lt (esc_sqrt_le_V s) hV
    rw [Real.sqrt_lt' hΛ] at h1
    exact_mod_cast h1.trans_le hD
  have hB : escB D s ≤ (∑ d' ∈ Finset.range (D + 1), (2 * d' + 3)) + 2 * D + D := by
    have h1 : ∑ d' ∈ Finset.Ico s.d (D + 1), (2 * d' + 3)
        ≤ ∑ d' ∈ Finset.range (D + 1), (2 * d' + 3) := by
      apply Finset.sum_le_sum_of_subset
      intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      exact hx.2
    have h2 := hle s
    have h3 : (if s.d = 0 then s.mu.natAbs else 0) ≤ D := by
      split_ifs with h0
      · obtain ⟨d, μ⟩ := s
        simp only at h0
        subst h0
        have h4 : Real.sqrt |(μ : ℝ)| < Λ := lt_of_le_of_lt (esc_sqrt_mu_le_V μ) hV
        rw [Real.sqrt_lt' hΛ] at h4
        have h5 : |(μ : ℝ)| < D := h4.trans_le hD
        have h6 : ((μ.natAbs : ℕ) : ℝ) = |(μ : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        have h7 : ((μ.natAbs : ℕ) : ℝ) < D := h6 ▸ h5
        exact_mod_cast h7.le
      · exact Nat.zero_le _
    simp only [escB]
    omega
  obtain ⟨w, hw, h⟩ := esc_reach_aux hle heven D _ s le_rfl
  refine ⟨w, hw.trans hB, ?_⟩
  rcases h with h | h
  · exact Or.inl h
  · right
    have h1 : Λ ≤ Real.sqrt D := by
      rw [Real.le_sqrt' hΛ]
      exact hD
    have h2 : Real.sqrt D ≤ Real.sqrt (run s w).d := Real.sqrt_le_sqrt (by exact_mod_cast h)
    exact h1.trans (h2.trans (esc_sqrt_le_V _))

end Strategy

/-- **Escape.** From every state outside `F` with `V < Λ`, some coin word of length at most
`L = L(Λ)` reaches `F` or a state with `V ≥ Λ`. -/
theorem escape (Λ : ℝ) : ∃ L : ℕ, ∀ s : State, s ∉ F → V s < Λ →
    ∃ w : List Bool, w.length ≤ L ∧ (run s w ∈ F ∨ Λ ≤ V (run s w)) :=
  escape_aux ell_le ell_even_step Λ

end Coalescence

#print axioms Coalescence.escape
