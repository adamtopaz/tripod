# Tripod.Constructions.pi1_exact_sequence_tripod_over_Q

Let `X := P^1_{\mathbf Q} \ {0,1,\infty}` and fix a geometric basepoint `\bar x` of `X`.
Write `\bar{\mathbf Q}` for an algebraic closure of `\mathbf Q`. The standard theory of
etale fundamental groups provides a canonical continuous surjection

`\pi_1^{\mathrm{et}}(X, \bar x) \twoheadrightarrow \mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q)`,

and identifies its kernel with the geometric fundamental group

`\pi_1^{\mathrm{et}}(X_{\bar{\mathbf Q}}, \bar x)`.

Equivalently, there is an exact sequence of profinite groups

`1 \to \pi_1^{\mathrm{et}}(X_{\bar{\mathbf Q}}, \bar x)
   \to \pi_1^{\mathrm{et}}(X, \bar x)
   \to \mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q) \to 1`,

with the first map injective with closed image, the last map surjective, and the image of
the first equal to the kernel of the last.

Reference: SGA1, Expose IX, Theoreme 6.1 ("suite exacte fondamentale").

Conventions on basepoints and canonicity up to conjugacy are recorded in
`informal/Tripod/Conventions.md#geometric-basepoints-and-conjugacy`.
