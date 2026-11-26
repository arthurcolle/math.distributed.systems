import Mathlib

/-!
# Definitions used by the trusted statements

Only Mathlib is imported.  `T` is the shortcut Collatz map on the integers, `Tn` the same map on the
natural numbers, and `Cn` the `3n+1` map without the shortcut.
-/

namespace Statement

/-- Shortcut Collatz map on the integers. -/
def T (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- Shortcut Collatz map on the natural numbers. -/
def Tn (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- The `3n+1` map. -/
def Cn (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

end Statement
