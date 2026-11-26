import CollatzCoalescence.Offsets

/-!
# Integers versus naturals

`T` on `ℤ` restricted to `ℕ` is `Tn`.
-/

namespace Coalescence

theorem T_iterate_natCast (k : ℕ) (x : ℕ) : T^[k] (x : ℤ) = ((Tn^[k] x : ℕ) : ℤ) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T_natCast, ih]

/-- If the integer orbits of `n` and `n + m` agree at time `k`, so do the natural-number orbits. -/
theorem Tn_iterate_eq_of_T (k n m : ℕ) (h : T^[k] (n : ℤ) = T^[k] ((n : ℤ) + m)) :
    Tn^[k] n = Tn^[k] (n + m) := by
  have h2 : ((n : ℤ) + m) = ((n + m : ℕ) : ℤ) := by push_cast; ring
  rw [h2, T_iterate_natCast, T_iterate_natCast] at h
  exact_mod_cast h

#print axioms T_iterate_natCast
#print axioms Tn_iterate_eq_of_T

end Coalescence
