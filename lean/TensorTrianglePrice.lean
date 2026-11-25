import Mathlib

/-!
A finite metric consequence of the three-site price identity reported in
OpenAI's November 24 tensor-geometry scope. This file proves only the real
arithmetic implication from the triangle inequalities. It does not import
or verify the upstream tensor-price construction.
-/

namespace MathDistributed

/-- Half the perimeter of a triangle is at least its longest side. -/
theorem semiperimeter_ge_longest (a b c : ℝ)
    (hab : a ≤ b + c) (hbc : b ≤ c + a) (hca : c ≤ a + b) :
    max a (max b c) ≤ (a + b + c) / 2 := by
  simp only [max_le_iff]
  constructor
  · linarith
  · constructor <;> linarith

/-- When `c` is a longest side, the premium is exactly half the slack in
the corresponding triangle inequality. -/
theorem semiperimeter_premium (a b c : ℝ)
    (ha : a ≤ c) (hb : b ≤ c) :
    (a + b + c) / 2 - max a (max b c) = (a + b - c) / 2 := by
  have hmax : max a (max b c) = c := by
    apply le_antisymm
    · simp only [max_le_iff]
      exact ⟨ha, hb, le_refl c⟩
    · exact le_max_of_le_right (le_max_right b c)
  rw [hmax]
  ring

/-- Strict triangle inequality gives a strictly positive three-site
premium over every pair price. -/
theorem semiperimeter_gt_longest (a b c : ℝ)
    (hab : a < b + c) (hbc : b < c + a) (hca : c < a + b) :
    max a (max b c) < (a + b + c) / 2 := by
  simp only [max_lt_iff]
  constructor
  · linarith
  · constructor <;> linarith

#print axioms semiperimeter_ge_longest
#print axioms semiperimeter_premium
#print axioms semiperimeter_gt_longest

end MathDistributed
