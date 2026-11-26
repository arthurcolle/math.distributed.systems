import CollatzCoalescence.Offsets

/-!
# Two small examples

The orbits of `3` and `4` never meet: both reach the cycle `1, 2`, in opposite phase.  So no statement
of the form "every `n` merges with `n + 1`" can hold.  The orbits of `4` and `5` meet after three steps.
-/

namespace Coalescence

/-- The orbits of `3` and `4` under the shortcut map are never equal at the same time. -/
theorem three_four_never (k : ℕ) : Tn^[k] 3 ≠ Tn^[k] 4 := by
  have h3 : ∀ j, Tn^[2 * j + 5] 3 = 1 ∧ Tn^[2 * j + 6] 3 = 2 := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      obtain ⟨a, b⟩ := ih
      constructor
      · rw [show 2 * (j + 1) + 5 = (2 * j + 6) + 1 by ring, Function.iterate_succ_apply', b]; decide
      · rw [show 2 * (j + 1) + 6 = (2 * j + 5) + 1 + 1 + 1 by ring, Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', a]; decide
  have h4 : ∀ j, Tn^[2 * j + 5] 4 = 2 ∧ Tn^[2 * j + 6] 4 = 1 := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      obtain ⟨a, b⟩ := ih
      constructor
      · rw [show 2 * (j + 1) + 5 = (2 * j + 6) + 1 by ring, Function.iterate_succ_apply', b]; decide
      · rw [show 2 * (j + 1) + 6 = (2 * j + 5) + 1 + 1 + 1 by ring, Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', a]; decide
  by_cases hk : k < 5
  · interval_cases k <;> decide
  · obtain ⟨j, hj | hj⟩ : ∃ j, k = 2 * j + 5 ∨ k = 2 * j + 6 := ⟨(k - 5) / 2, by omega⟩
    · rw [hj, (h3 j).1, (h4 j).1]; decide
    · rw [hj, (h3 j).2, (h4 j).2]; decide

/-- The orbits of `4` and `5` meet after three steps. -/
theorem four_five_meet : Tn^[3] 4 = Tn^[3] 5 := by decide

#print axioms three_four_never
#print axioms four_five_meet

end Coalescence
