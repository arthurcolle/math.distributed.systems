import Solution
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Field.Basic

/-!
The Lean interface for the permanent-to-PIT argument.

The permanent border lower bound is imported from `Solution`. This file proves
basic substitution and evaluation facts and a corollary of that lower bound.
It does not yet formalize the published approximative factor theorem, the
generator reconstruction, or the asymptotic parameter choices.
-/

namespace PermanentPIT

open MvPolynomial Statement

universe u
noncomputable section

/-- Substitute the generator-coordinate polynomials into the tested polynomial. -/
def pullback {F : Type u} [Field F] {n t : ℕ}
    (g : Fin n → MvPolynomial (Fin t) F)
    (f : MvPolynomial (Fin n) F) : MvPolynomial (Fin t) F :=
  aeval g f

/-- The values of the generator at a seed. -/
def generatorValue {F : Type u} [Field F] {n t : ℕ}
    (g : Fin n → MvPolynomial (Fin t) F)
    (z : Fin t → F) : Fin n → F :=
  fun i => eval z (g i)

/-- Evaluation after polynomial substitution is evaluation at the generator. -/
theorem eval_pullback {F : Type u} [Field F] {n t : ℕ}
    (g : Fin n → MvPolynomial (Fin t) F)
    (f : MvPolynomial (Fin n) F) (z : Fin t → F) :
    eval z (pullback g f) = eval (generatorValue g z) f := by
  change eval z (aeval g f) = eval (fun i => eval z (g i)) f
  simpa only [aeval_eq_eval] using
    (MvPolynomial.comp_aeval_apply (f := g) (φ := aeval z) f)

/-- The actual finite set of tested points, allowing duplicate generator outputs. -/
def hittingSet {F : Type u} [Field F] {n t : ℕ}
    (g : Fin n → MvPolynomial (Fin t) F) (S : Finset F) :
    Finset (Fin n → F) :=
  by
    classical
    exact (Fintype.piFinset fun _ : Fin t => S).image (generatorValue g)

/-- A nonzero pullback gives a hit as soon as the seed grid hits that pullback. -/
theorem hit_of_seed_hit {F : Type u} [Field F] {n t : ℕ}
    (g : Fin n → MvPolynomial (Fin t) F) (S : Finset F)
    (f : MvPolynomial (Fin n) F)
    (z : Fin t → F)
    (hz : z ∈ Fintype.piFinset fun _ : Fin t => S)
    (hnz : eval z (pullback g f) ≠ 0) :
    ∃ x ∈ hittingSet g S, eval x f ≠ 0 := by
  classical
  refine ⟨generatorValue g z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
  simpa only [eval_pullback] using hnz

/-- The image of a seed grid cannot have more points than the grid itself. -/
theorem hittingSet_card_le {F : Type u} [Field F] {n t : ℕ}
    (g : Fin n → MvPolynomial (Fin t) F) (S : Finset F) :
    (hittingSet g S).card ≤ S.card ^ t := by
  classical
  unfold hittingSet
  calc
    _ ≤ (Fintype.piFinset (fun _ : Fin t => S)).card := Finset.card_image_le
    _ = S.card ^ t := Fintype.card_piFinset_const S t

/-- A nonzero polynomial of total degree below the grid side length has a
nonzero evaluation on that grid. -/
theorem grid_hits_of_card_gt_totalDegree {F : Type u} [Field F] {t : ℕ}
    (p : MvPolynomial (Fin t) F) (hp : p ≠ 0) (S : Finset F)
    (hcard : p.totalDegree < S.card) :
    ∃ z ∈ Fintype.piFinset (fun _ : Fin t => S), eval z p ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hfilter : (Fintype.piFinset (fun _ : Fin t => S)).filter
      (fun z => eval z p = 0) = Fintype.piFinset (fun _ : Fin t => S) :=
    Finset.filter_eq_self.mpr h
  have hne : ((S.card : ℚ≥0) ^ t) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hcard)))
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp S
  have hleft : (1 : ℚ≥0) ≤ (p.totalDegree : ℚ≥0) / (S.card : ℚ≥0) := by
    simpa [hfilter, Fintype.card_piFinset_const, hne] using hsz
  have hcast : (p.totalDegree : ℚ≥0) < (S.card : ℚ≥0) := by
    exact_mod_cast hcard
  have hpos : (0 : ℚ≥0) < (S.card : ℚ≥0) := by
    exact_mod_cast (Nat.zero_lt_of_lt hcard)
  have hright : (p.totalDegree : ℚ≥0) / (S.card : ℚ≥0) < 1 :=
    (div_lt_one hpos).2 hcast
  exact (not_lt_of_ge hleft) hright

/-- The precise conditional PIT bridge: if a circuit's pullback is nonzero
and its seed degree fits the grid, the finite generator image hits it. -/
theorem hit_of_pullback_nonzero {F : Type u} [Field F] {n t : ℕ}
    (g : Fin n → MvPolynomial (Fin t) F) (S : Finset F)
    (f : MvPolynomial (Fin n) F)
    (hnz : pullback g f ≠ 0)
    (hdegree : (pullback g f).totalDegree < S.card) :
    ∃ x ∈ hittingSet g S, eval x f ≠ 0 := by
  obtain ⟨z, hz, heval⟩ :=
    grid_hits_of_card_gt_totalDegree (pullback g f) hnz S hdegree
  exact hit_of_seed_hit g S f z hz heval

/-- The rebuilt upstream border theorem gives a uniform characteristic-zero
    prohibition whenever a proposed approximation size is below its bound. -/
theorem permanent_no_approx :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ,
      ∀ (F : Type u) [Field F] [CharP F 0], ∀ m ≥ m₀, ∀ s : ℕ,
        ¬ Beyond c m s → ¬ Approximates (perm F m) s := by
  obtain ⟨c, hc, h⟩ := Solution.mainTheoremApprox.{u}
  obtain ⟨m₀, hm₀⟩ := h 0
  refine ⟨c, hc, m₀, ?_⟩
  intro F _ _ m hm s hsmall happrox
  exact hsmall ((hm₀ F m hm s).2 (by decide) happrox)

end
end PermanentPIT
