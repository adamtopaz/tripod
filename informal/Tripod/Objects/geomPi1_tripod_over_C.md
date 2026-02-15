# Tripod.Objects.geomPi1_tripod_over_C

Let `X := P^1_C \ {0,1,\infty}`. Fix a geometric basepoint `\bar x` of `X` (for example a
complex point, or a tangential basepoint). The object referred to here is the geometric
etale fundamental group

`\pi_1^{\mathrm{et}}(X, \bar x)`,

viewed as a profinite group. Different choices of `\bar x` give isomorphic groups, but the
isomorphism is only well-defined up to inner automorphism (conjugation); consequently,
constructions landing in `\mathrm{Out}(\pi_1^{\mathrm{et}}(X, \bar x))` are the natural
basepoint-independent ones.

See `informal/Tripod/Conventions.md#geometric-basepoints-and-conjugacy`.

Over `\mathbf C`, Riemann's existence theorem identifies finite etale covers of `X` with
finite topological covering spaces of the Riemann surface `X(\mathbf C)`. It follows that

`\pi_1^{\mathrm{et}}(X, \bar x) \cong \widehat{\pi_1^{\mathrm{top}}(X(\mathbf C), x)}`,

the profinite completion of the topological fundamental group. Since `X(\mathbf C)` is the
thrice-punctured Riemann sphere, `\pi_1^{\mathrm{top}}(X(\mathbf C))` is the free group on
two generators.
