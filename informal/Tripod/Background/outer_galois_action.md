# Outer Galois Action From The Fundamental Exact Sequence

Let `X := P^1_{\mathbf Q} \ {0,1,\infty}` and choose a geometric basepoint `\bar x`.
The fundamental exact sequence of etale fundamental groups provides a short exact sequence
of profinite groups

`1 \to \pi_1^{\mathrm{et}}(X_{\bar{\mathbf Q}}, \bar x)
   \to \pi_1^{\mathrm{et}}(X, \bar x)
   \to \mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q) \to 1`.

From any short exact sequence `1 \to N \to E \to Q \to 1` one obtains an outer action
`Q \to \mathrm{Out}(N)` by the standard construction: choose a lift `\tilde q \in E` of
`q \in Q`, let `\tilde q` act on `N` by conjugation, and pass to the quotient
`\mathrm{Out}(N) = \mathrm{Aut}(N)/\mathrm{Inn}(N)`. Different choices of lifts differ by an
element of `N` and therefore induce the same class in `\mathrm{Out}(N)`.

Applied to the sequence above, this yields the (basepoint-independent) outer Galois
representation

`\rho : \mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q) \to \mathrm{Out}(\pi_1^{\mathrm{et}}(X_{\bar{\mathbf Q}}))`.

See `informal/Tripod/Conventions.md#outer-actions-from-short-exact-sequences`.
