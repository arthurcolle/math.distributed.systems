import Mathlib

/-!
A finite positive-operator contraction lemma for the weighted recursion in
Proposition 11.8 (`prop:recursion-solution`) of the Wilson-loop manuscript.
The manuscript's substantive RG work must establish the row bound `hrow` and
the recurrence `hrec`; this theorem proves their finite-dimensional consequence.
-/

namespace WilsonLoopContinuum

/-- If a nonnegative finite recursion has weighted operator norm at most
`q < 1` and source at most `C` times the weight, then every component is at
most `C/(1-q)` times its weight. -/
theorem finite_weighted_recursion_bound {n : ℕ}
    (u w : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (q C : ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 ≤ u i)
    (hA : ∀ i j, 0 ≤ A i j) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, A i j * w j ≤ q * w i)
    (hrec : ∀ i, u i ≤ (∑ j, A i j * u j) + C * w i) :
    ∀ i, u i ≤ (C / (1 - q)) * w i := by
  by_cases hn : n = 0
  · subst n
    intro i
    exact Fin.elim0 i
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero hn⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun i : Fin n => u i / w i)
      hne
  let M : ℝ := u i₀ / w i₀
  have hM : 0 ≤ M := div_nonneg (hu i₀) (hw i₀).le
  have hubound (i : Fin n) : u i ≤ M * w i := by
    exact (div_le_iff₀ (hw i)).mp (hmax i (Finset.mem_univ i))
  have hstep (i : Fin n) : u i ≤ (q * M + C) * w i := by
    have hsum : (∑ j, A i j * u j) ≤ M * (∑ j, A i j * w j) := by
      calc
        (∑ j, A i j * u j) ≤ ∑ j, A i j * (M * w j) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hubound j) (hA i j)
        _ = M * (∑ j, A i j * w j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    calc
      u i ≤ (∑ j, A i j * u j) + C * w i := hrec i
      _ ≤ M * (∑ j, A i j * w j) + C * w i := by linarith
      _ ≤ M * (q * w i) + C * w i := by
        have hmul := mul_le_mul_of_nonneg_left (hrow i) hM
        linarith
      _ = (q * M + C) * w i := by ring
  have hMineq : M ≤ q * M + C := by
    exact (div_le_iff₀ (hw i₀)).mpr (hstep i₀)
  have hqpos : 0 < 1 - q := by linarith
  have hMbound : M ≤ C / (1 - q) := by
    apply (le_div_iff₀ hqpos).mpr
    nlinarith
  intro i
  exact (hubound i).trans
    (mul_le_mul_of_nonneg_right hMbound (hw i).le)

/-- The manuscript uses a weighted contraction factor of one quarter and records
the convenient weaker bound `2 * C * w`. -/
theorem finite_weighted_recursion_quarter {n : ℕ}
    (u w : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (C : ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 ≤ u i)
    (hA : ∀ i j, 0 ≤ A i j) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, A i j * w j ≤ (1 / 4 : ℝ) * w i)
    (hrec : ∀ i, u i ≤ (∑ j, A i j * u j) + C * w i) :
    ∀ i, u i ≤ 2 * C * w i := by
  have hmain := finite_weighted_recursion_bound u w A (1 / 4 : ℝ) C
    hw hu hA (by norm_num) hrow hrec
  have hconst : C / (1 - (1 / 4 : ℝ)) ≤ 2 * C := by
    norm_num
    linarith
  intro i
  exact (hmain i).trans
    (mul_le_mul_of_nonneg_right hconst (hw i).le)

end WilsonLoopContinuum
