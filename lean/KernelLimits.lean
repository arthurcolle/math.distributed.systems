import Mathlib

/-!
Finite positive kernels and pointwise limits. This is a reusable interface for
reflection positivity of cutoff Wilson observables, covariance kernels, and
positive definite kernels in analysis. It does not assert that a particular
Yang–Mills construction satisfies reflection positivity or convergence.
-/

namespace MathDistributed

open Filter

/-- Every finite Gram form of a real kernel is nonnegative. -/
def FinitePSD {X : Type*} (K : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j * K (x i) (x j)

/-- Multiplicative renormalization by a factor for each observable preserves
positive semidefiniteness: it is diagonal congruence of each finite Gram form. -/
theorem finitePSD_congruence {X : Type*} (K : X → X → ℝ) (a : X → ℝ)
    (hK : FinitePSD K) :
    FinitePSD (fun x y => a x * a y * K x y) := by
  intro n x c
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (hK n x (fun i => c i * a (x i)))

/-- Pointwise limits preserve finite positive semidefiniteness. -/
theorem finitePSD_of_pointwise_limit {X : Type*}
    (K : ℕ → X → X → ℝ) (k : X → X → ℝ)
    (hK : ∀ N, FinitePSD (K N))
    (hlim : ∀ x y, Tendsto (fun N => K N x y) atTop (nhds (k x y))) :
    FinitePSD k := by
  intro n x c
  have hterm (i j : Fin n) :
      Tendsto (fun N => c i * c j * K N (x i) (x j)) atTop
        (nhds (c i * c j * k (x i) (x j))) :=
    tendsto_const_nhds.mul (hlim (x i) (x j))
  have hinner (s : Finset (Fin n)) (i : Fin n) :
      Tendsto (fun N => s.sum (fun j => c i * c j * K N (x i) (x j))) atTop
        (nhds (s.sum (fun j => c i * c j * k (x i) (x j)))) := by
    induction s using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    | @insert a s ha ih => simpa [Finset.sum_insert ha] using (hterm i a).add ih
  have houter (s : Finset (Fin n)) :
      Tendsto (fun N => s.sum (fun i => ∑ j, c i * c j * K N (x i) (x j))) atTop
        (nhds (s.sum (fun i => ∑ j, c i * c j * k (x i) (x j)))) := by
    induction s using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    | @insert a s ha ih =>
        simpa [Finset.sum_insert ha] using (hinner Finset.univ a).add ih
  exact ge_of_tendsto (houter Finset.univ)
    (Eventually.of_forall (fun N => hK N n x c))

#print axioms finitePSD_congruence
#print axioms finitePSD_of_pointwise_limit

/-- A reusable reflection-positivity interface: positive cutoff kernels may be
renormalized by factors on individual observables, then passed to a pointwise
limit. The application must provide the cutoff positivity and convergence. -/
theorem finitePSD_of_renormalized_limit {X : Type*}
    (K : ℕ → X → X → ℝ) (a : ℕ → X → ℝ) (k : X → X → ℝ)
    (hK : ∀ N, FinitePSD (K N))
    (hlim : ∀ x y, Tendsto (fun N => a N x * a N y * K N x y)
      atTop (nhds (k x y))) :
    FinitePSD k := by
  apply finitePSD_of_pointwise_limit
    (K := fun N x y => a N x * a N y * K N x y)
  · intro N
    exact finitePSD_congruence (K N) (a N) (hK N)
  · exact hlim

#print axioms finitePSD_of_renormalized_limit

end MathDistributed
