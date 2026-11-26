import CollatzCoalescence.Defs

/-!
# The pair chain for a general odd multiplier

`Ta a x = x / 2` for even `x` and `(a x + 1) / 2` for odd `x`.  For `a = 3` this is the shortcut Collatz
map.  The pair state `(d, μ)` now means `q = a^d p + μ`.
-/

namespace Coalescence.Mult

/-- `x ↦ x / 2` (even `x`), `(a x + 1) / 2` (odd `x`). -/
def Ta (a : ℤ) (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (a * x + 1) / 2

/-- One step of the pair chain for the multiplier `a`. -/
def stepA (a : ℕ) (s : State) (c : Bool) : State :=
  if s.mu % 2 = 0 then
    (if c then ⟨s.d, ((a : ℤ) * s.mu + 1 - (a : ℤ) ^ s.d) / 2⟩ else ⟨s.d, s.mu / 2⟩ : State).norm
  else if c then
    (match s.d with
     | 0 => ⟨1, (1 - (a : ℤ) * s.mu) / 2⟩
     | d' + 1 => (⟨d', (s.mu - (a : ℤ) ^ d') / 2⟩ : State).norm)
  else ⟨s.d + 1, ((a : ℤ) * s.mu + 1) / 2⟩

/-- The state reached from `s` along the coin word `w`. -/
def runA (a : ℕ) (s : State) (w : List Bool) : State := w.foldl (stepA a) s

/-- `q = a^d p + μ`. -/
def RelA (a : ℕ) (s : State) (p q : ℤ) : Prop := q = (a : ℤ) ^ s.d * p + s.mu

/-- `|μ| / a^d`. -/
noncomputable def wA (a : ℕ) (s : State) : ℝ := |(s.mu : ℝ)| / (a : ℝ) ^ s.d

theorem stepA_even_false (a d : ℕ) (μ : ℤ) (hμ : μ % 2 = 0) :
    stepA a ⟨d, μ⟩ false = (⟨d, μ / 2⟩ : State).norm := by
  simp only [stepA, if_pos hμ]
  rfl

theorem stepA_even_true (a d : ℕ) (μ : ℤ) (hμ : μ % 2 = 0) :
    stepA a ⟨d, μ⟩ true = (⟨d, ((a : ℤ) * μ + 1 - (a : ℤ) ^ d) / 2⟩ : State).norm := by
  simp only [stepA, if_pos hμ]
  rfl

theorem stepA_odd_false (a d : ℕ) (μ : ℤ) (hμ : μ % 2 = 1) :
    stepA a ⟨d, μ⟩ false = ⟨d + 1, ((a : ℤ) * μ + 1) / 2⟩ := by
  have hμ' : ¬ μ % 2 = 0 := by omega
  simp only [stepA, if_neg hμ']
  rfl

theorem stepA_odd_true_zero (a : ℕ) (μ : ℤ) (hμ : μ % 2 = 1) :
    stepA a ⟨0, μ⟩ true = ⟨1, (1 - (a : ℤ) * μ) / 2⟩ := by
  have hμ' : ¬ μ % 2 = 0 := by omega
  simp only [stepA, if_neg hμ']
  rfl

theorem stepA_odd_true_succ (a d' : ℕ) (μ : ℤ) (hμ : μ % 2 = 1) :
    stepA a ⟨d' + 1, μ⟩ true = (⟨d', (μ - (a : ℤ) ^ d') / 2⟩ : State).norm := by
  have hμ' : ¬ μ % 2 = 0 := by omega
  simp only [stepA, if_neg hμ']
  rfl

theorem stepA_absorbed (a : ℕ) (c : Bool) : stepA a absorbed c = absorbed := by
  cases c <;> simp [stepA, absorbed, State.norm]

/-- For `a = 3` this is the chain of `Defs.lean`. -/
theorem stepA_three (s : State) (c : Bool) : stepA 3 s c = step s c := by
  simp only [stepA, step]
  rfl

example : stepA 5 ⟨0, 1⟩ false = ⟨1, 3⟩ := by decide
example : runA 5 ⟨0, 1⟩ (List.replicate 13 true) = ⟨0, 310⟩ := by decide

end Coalescence.Mult
