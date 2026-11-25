# November 24 OpenAI release: exact scope and a cross-paper corollary

At upstream commit `3344da59991ed94f9ba711217b29c1d760badfa6`, the
OpenAI mathematics catalog has a revised result family
379 and a new family 380. The local `openai-math/CONTENTS.md` still describes
family 379 as “Separation of VP and VNP over every field” and has no family
380. The site therefore indexes the upstream entries separately, preserving
the local snapshot rather than silently rewriting it.

Primary sources read on 2026-11-24:

- [Family 379 Lean scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/379.md)
  and [matrix multiplication manuscript](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf).
- [Sunflower manuscript](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/An-exponential-bound-for-sunflowers-November-24-2026/paper.pdf).
- [Family 380 Lean scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/380.md),
  [LP manuscript](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Strongly-polynomial-linear-programming-November-24-2026/paper.pdf),
  and [polytope diameter manuscript](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Superpolynomial-graph-diameter-of-simple-polytopes-November-24-2026/paper.pdf).

## Scope corrections

**Matrix multiplication.** The source reports exponent \(\omega_F=9/4\)
over every field. Here “exponent” means an infimum of achievable asymptotic
exponents: it gives \(O_\varepsilon(n^{9/4+\varepsilon})\) algorithms for
every \(\varepsilon>0\), not by itself an \(O(n^{9/4})\) algorithm. The
manuscript states a finite lower bound of at least
\(\lceil n^{9/4}/2\rceil\) nonscalar multiplication or division gates for
\(n\ge2\). The scope document says the exact exponent is in Lean, while
that finite lower bound remains unformalized. The HN title “Θ(n^2.25)” is
therefore stronger than the exponent statement if read as a literal uniform
big-Theta bound without lower-order losses.

**Linear programming.** The manuscript states a strongly polynomial
algorithm for arbitrary real coefficients. The Lean scope explicitly covers
fixed rational RAM programs on rational input, with polynomial instruction
counts and intermediate bit lengths. The scope does not itself claim a Lean
formalization of the arbitrary-real model. The paper also discusses
mean-payoff games; the primary README inspected here does not establish the
HN comment's separate parity-game and simple-stochastic-game claims as
consequences of this paper.

**Sunflowers.** For each fixed \(r\ge3\), the Lean scope gives an
exponential \(C_r^k\) threshold for distinct \(k\)-element sets. The
manuscript's quantitative dependence of the base on \(r\), and its version
for sets of size at most \(k\), remain outside that formalized scope.

**Polytope diameter.** The Lean scope states simple rational polytope
families with superpolynomial edge diameter and stronger lower bounds when
each move may cross a face of subpolynomial dimension. This refutes a
polynomial Hirsch-style *diameter* bound within the stated model. It does
not refute strongly polynomial LP algorithms that use algebraic operations
instead of an edge or bounded-face walk.

I read the upstream README files and Lean scope documents, not the entire
proofs, and did not replay their Lean development. The primary documents
report formalization; this note is a statement and scope audit only.

## Cross-paper lemma

Let \(P_n\) be a polytope with \(n\) facets and designated vertices
\(u_n,v_n\). For an allowed face dimension \(s(n)\), define
\(d_s(u_n,v_n)\) as the least number of vertex-to-vertex steps between them,
each step crossing a face of dimension at most \(s(n)\). If the new
polytope theorem supplies \(d_s(u_n,v_n)>n^c\) eventually for every fixed
\(c\), then **every algorithm whose complete trajectory consists of such
steps from \(u_n\) to \(v_n\)** takes superpolynomially many steps. Its
trajectory is an admissible path, and by definition no admissible path is
shorter than \(d_s\).

The quantifiers matter: the obstruction applies to that restricted path
model and designated endpoints. A nonlocal strongly polynomial solver is
consistent with it. This is a local synthesis, not a global novelty claim.

## Tensor-price triangle slack

Family 379's scope reports that a bit shared by two sites costs their
Euclidean distance and a bit shared among three sites costs half the
perimeter of their triangle. Sort the three side lengths as
\(a\le b\le c\). The **exact premium over the most expensive pair** is

\[
\frac{a+b+c}{2}-c=\frac{a+b-c}{2}.
\]

This is nonnegative by the triangle inequality, strictly positive for a
nondegenerate Euclidean triangle, and zero in the collinear equality case.
`lean/TensorTrianglePrice.lean` proves the real-arithmetic consequence. It
does not rebuild the upstream tensor-price construction.
