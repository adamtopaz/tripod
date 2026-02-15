# Tripod.Objects.arithPi1_tripod_over_Q

Let `X := P^1_{\mathbf Q} \ {0,1,\infty}`. Fix a geometric basepoint `\bar x` of `X` (i.e.
an algebraic geometric point `\operatorname{Spec}(\Omega) \to X` with `\Omega` separably
closed). The object referred to here is the arithmetic etale fundamental group

`\pi_1^{\mathrm{et}}(X, \bar x)`,

as a profinite group.

See `informal/Tripod/Conventions.md#geometric-basepoints-and-conjugacy`.

When `X` is geometrically connected (as it is here), the canonical map `X_{\bar{\mathbf Q}}
\to X` induces a closed normal subgroup

`\pi_1^{\mathrm{et}}(X_{\bar{\mathbf Q}}, \bar x) \trianglelefteq \pi_1^{\mathrm{et}}(X, \bar x)`,

and the quotient identifies with the absolute Galois group. This is the fundamental exact
sequence of etale fundamental groups (SGA1, Expose IX, 6.1).

See `informal/Tripod/Conventions.md#fundamental-exact-sequence-over-a-field`.
