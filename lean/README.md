# Finite kernel positivity check

`KernelLimits.lean` proves three statements over real kernels:

1. Finite quadratic-form nonnegativity is preserved by diagonal
   congruence `K(x,y) ↦ a(x)a(y)K(x,y)`.
2. It is preserved by pointwise limits.
3. Therefore it is preserved by a pointwise limit of such renormalized
   kernels.

The local definition `FinitePSD` means **nonnegative finite real quadratic
forms**. It does not separately assert symmetry of the kernel. An application
requiring a symmetric or Hermitian kernel must establish that property too.

On 2026-11-24, the complete file compiled using the pinned Wilson-loop
Lean project on `ufo`. `#print axioms` for all three theorems reported only
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry` or
project-specific axiom in this file. Two lint warnings suggested replacing
`simpa` by `simp` in induction base cases; compilation exited 0.

The hypotheses `hK` and `hlim` are **assumptions** of the application theorem.
The local Wilson-loop manuscript's cutoff positivity, factorized
normalization, and continuum convergence have not been derived here.

`TensorTrianglePrice.lean` was also compiled on the same pinned project
on 2026-11-24. All three theorem axiom reports were exactly
`propext`, `Classical.choice`, and `Quot.sound`. It proves the real-arithmetic
consequence of the upstream three-site tensor-price identity, not that
identity itself.
