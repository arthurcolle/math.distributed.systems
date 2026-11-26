import Mathlib

namespace Coalescence

/-- Shortcut Collatz map on the integers. -/
def T (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

structure State where
  d : ℕ
  mu : ℤ
deriving DecidableEq, Repr

def State.norm (s : State) : State := if s.d = 0 then ⟨0, |s.mu|⟩ else s

def step (s : State) (c : Bool) : State :=
  if s.mu % 2 = 0 then
    (if c then ⟨s.d, (3 * s.mu + 1 - 3 ^ s.d) / 2⟩ else ⟨s.d, s.mu / 2⟩ : State).norm
  else if c then
    (match s.d with
     | 0 => ⟨1, (1 - 3 * s.mu) / 2⟩
     | d' + 1 => (⟨d', (s.mu - 3 ^ d') / 2⟩ : State).norm)
  else ⟨s.d + 1, (3 * s.mu + 1) / 2⟩

/-- `q = 3^d p + μ`. -/
def Rel (s : State) (p q : ℤ) : Prop := q = 3 ^ s.d * p + s.mu

/-- The merged state. -/
def absorbed : State := ⟨0, 0⟩

/-- The state reached from `s` along the coin word `w`. -/
def run (s : State) (w : List Bool) : State := w.foldl step s


/-! ### Unfolding lemmas for `step` -/

theorem step_even_false (d : ℕ) (μ : ℤ) (hμ : μ % 2 = 0) :
    step ⟨d, μ⟩ false = (⟨d, μ / 2⟩ : State).norm := by
  simp only [step, if_pos hμ]
  rfl

theorem step_even_true (d : ℕ) (μ : ℤ) (hμ : μ % 2 = 0) :
    step ⟨d, μ⟩ true = (⟨d, (3 * μ + 1 - 3 ^ d) / 2⟩ : State).norm := by
  simp only [step, if_pos hμ]
  rfl

theorem step_odd_false (d : ℕ) (μ : ℤ) (hμ : μ % 2 = 1) :
    step ⟨d, μ⟩ false = ⟨d + 1, (3 * μ + 1) / 2⟩ := by
  have hμ' : ¬ μ % 2 = 0 := by omega
  simp only [step, if_neg hμ']
  rfl

theorem step_odd_true_zero (μ : ℤ) (hμ : μ % 2 = 1) :
    step ⟨0, μ⟩ true = ⟨1, (1 - 3 * μ) / 2⟩ := by
  have hμ' : ¬ μ % 2 = 0 := by omega
  simp only [step, if_neg hμ']
  rfl

theorem step_odd_true_succ (d' : ℕ) (μ : ℤ) (hμ : μ % 2 = 1) :
    step ⟨d' + 1, μ⟩ true = (⟨d', (μ - 3 ^ d') / 2⟩ : State).norm := by
  have hμ' : ¬ μ % 2 = 0 := by omega
  simp only [step, if_neg hμ']
  rfl

theorem State.norm_of_pos (d : ℕ) (μ : ℤ) (hd : 0 < d) : (⟨d, μ⟩ : State).norm = ⟨d, μ⟩ := by
  simp [State.norm, Nat.pos_iff_ne_zero.mp hd]

theorem State.norm_zero (μ : ℤ) : (⟨0, μ⟩ : State).norm = ⟨0, |μ|⟩ := by
  simp [State.norm]

theorem step_absorbed' (c : Bool) : step absorbed c = absorbed := by
  cases c <;> decide

end Coalescence
