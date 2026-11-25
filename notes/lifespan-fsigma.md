# Finite lifespan sets are Fσ under lower semicontinuity

Let `X` be a topological space and let `τ : X → (0, ∞]` be a maximal-lifespan function. Assume `τ` is lower semicontinuous. The finite-lifespan set is

`B = {x : τ(x) < ∞} = ⋃_{m≥1} {x : τ(x) ≤ m}`.

Each sublevel set `{x : τ(x) ≤ m}` is closed, hence `B` is Fσ. If `X` is Polish, this particular `B` is Borel and therefore cannot be Π¹₁-complete under continuous reductions from Polish spaces. The conclusion requires the stated topology and lower semicontinuity; it does not cover arbitrary weak-solution relations or encodings.

The paper argument is short. The Lean signature from the original field-pair notes was a sketch, not a checked proof. A formalization task must identify the exact Mathlib lower-semicontinuity API and prove the countable union identity.
