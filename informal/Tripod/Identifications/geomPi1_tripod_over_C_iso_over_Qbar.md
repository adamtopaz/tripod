# Tripod.Identifications.geomPi1_tripod_over_C_iso_over_Qbar

Let `X_0 := P^1_{\mathbf Q} \setminus \{0,1,\infty\}`. Choose an embedding
`\bar{\mathbf Q} \hookrightarrow \mathbf C`. Consider the two base changes

`X_{\bar{\mathbf Q}} := X_0 \times_{\mathbf Q} \bar{\mathbf Q}`  and  `X_{\mathbf C} := X_0 \times_{\mathbf Q} \mathbf C`.

Invariance of the etale fundamental group under algebraically closed base change yields an
isomorphism of profinite groups

`\pi_1^{\mathrm{et}}(X_{\mathbf C}) \cong \pi_1^{\mathrm{et}}(X_{\bar{\mathbf Q}})`.

More precisely, after fixing compatible geometric basepoints, there is an isomorphism of
fundamental groups; changing basepoints conjugates the resulting isomorphism. This is why
the induced identification on outer automorphism groups is canonical.

See `informal/Tripod/Conventions.md#algebraically-closed-base-change` and
`informal/Tripod/Conventions.md#geometric-basepoints-and-conjugacy`.

Reference: SGA1, Expose X ("changement de base" for `\pi_1`).
