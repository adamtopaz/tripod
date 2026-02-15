# Tripod.Theorems.galois_action_on_geomPi1_tripod_faithful

Let `X := P^1_{\bar{\mathbf Q}} \ {0,1,\infty}` and consider the outer Galois representation
arising from the fundamental exact sequence:

`\rho : \mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q) \to \mathrm{Out}(\pi_1^{\mathrm{et}}(X))`.

Claim. The homomorphism `\rho` is injective (equivalently: the Galois action on
`\pi_1^{\mathrm{et}}(X)` is faithful).

Sketch. An element of `\mathrm{Out}(\pi_1^{\mathrm{et}}(X))` is determined by its effect on all
finite quotients of `\pi_1^{\mathrm{et}}(X)`, hence on the category of finite etale covers of
`X`. Therefore, if `\sigma \in \mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q)` acts trivially via
`\rho`, then `\sigma` acts trivially on the Galois category of finite etale covers of `X`
(i.e. it preserves every cover up to isomorphism; equivalently, it fixes every dessin).

See `informal/Tripod/Conventions.md#covers-quotients-and-dessins`.

By Belyi's theorem, every smooth projective curve over `\bar{\mathbf Q}` admits a finite
morphism to `P^1` branched only over `{0,1,\infty}`; equivalently, Belyi maps correspond to
finite etale covers of `X` (after removing the ramification locus). In the language of
Grothendieck, these are dessins d'enfants.

It is a classical theorem (often stated as: the action of
`\mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q)` on dessins d'enfants is faithful) that for
`\sigma \neq 1` there exists some dessin moved by `\sigma`. Hence if `\sigma` fixes every
finite etale cover of `X` up to isomorphism, then `\sigma = 1`.

References: Grothendieck's *Esquisse d'un Programme*; Szamuely, *Galois Groups and
Fundamental Groups* (discussion of the faithful Galois action on the tripod).
