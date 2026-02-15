# Tripod.Objects.geomPi1_tripod_over_Qbar

Let `\bar{\mathbf Q}` be an algebraic closure of `\mathbf Q` and set
`X := P^1_{\bar{\mathbf Q}} \ {0,1,\infty}`. Fix a geometric basepoint `\bar x` of `X`.
The object referred to here is the geometric etale fundamental group

`\pi_1^{\mathrm{et}}(X, \bar x)`,

as a profinite group, again well-defined up to inner automorphism when the basepoint is
suppressed.

See `informal/Tripod/Conventions.md#geometric-basepoints-and-conjugacy`.

More generally, if `Y` is a connected scheme of finite type over an algebraically closed
field `k` and `k \to k'` is an extension of algebraically closed fields, then invariance of
the etale fundamental group under algebraically closed base change (SGA1, Expose X) gives an
isomorphism (well-defined up to conjugacy)

`\pi_1^{\mathrm{et}}(Y_{k'}, \bar y') \cong \pi_1^{\mathrm{et}}(Y, \bar y)`.

Applied to the tripod, an embedding `\bar{\mathbf Q} \hookrightarrow \mathbf C` yields a
comparison between `\pi_1^{\mathrm{et}}(P^1_{\bar{\mathbf Q}} \setminus \{0,1,\infty\})` and
`\pi_1^{\mathrm{et}}(P^1_{\mathbf C} \setminus \{0,1,\infty\})`.

See `informal/Tripod/Conventions.md#algebraically-closed-base-change`.
