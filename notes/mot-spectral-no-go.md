# Covariance spectra do not determine basket prices

Let two assets start at zero and end at random vector (X=(X_1,X_2)).
Consider the two martingale laws

| Law | Terminal states | Probabilities |
| --- | --- | --- |
| A | ((1,1),(-1,-1)) | (1/2,1/2) |
| B | ((1,-1),(-1,1)) | (1/2,1/2) |

Both coordinates are mean-zero Rademacher variables under both laws. The
covariance matrices are respectively

\[
\Sigma_A=\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
\Sigma_B=\begin{pmatrix}1&-1\\-1&1\end{pmatrix}.
\]

Both have eigenvalue multiset \(\{0,2\}\). Yet for
\(h(x_1,x_2)=(x_1+x_2-1)_+\),
\(\mathbb E_Ah=1/2\) and \(\mathbb E_Bh=0\).

Thus marginal laws and the *unordered covariance spectrum* cannot recover
all basket prices, even in a one-period finite martingale model. The
counterexample targets spectral-only MOT/free-probability proposals. It does
not rule out descriptions retaining eigenvectors or the full joint law.

This finite construction is a local stress test, not a claim of literature
priority. A Lean proof would use a two-element probability space and exact
rational arithmetic; it has not yet been written.
