# Tripod

## geometricPi1OverC

The profinite etale fundamental group of the thrice-punctured projective line
`P^1_C \ {0, 1, ∞}` with base point over `C`. By Riemann's existence theorem
(SGA1 XII), this is canonically isomorphic to the profinite completion of the
topological fundamental group `pi_1^top(P^1(C) \ {0,1,∞})`, which is the free
group on two generators.

## geometricPi1OverQbar

The profinite etale fundamental group of the thrice-punctured projective line
`P^1_{Qbar} \ {0, 1, ∞}` with base point over `Qbar = AlgebraicClosure Q`.
By the base-change theorem for etale fundamental groups (SGA1 X.1.8), this is
isomorphic to `geometricPi1OverC` via the embedding `Qbar ↪ C`.

## arithPi1OverQ

The profinite etale fundamental group of the thrice-punctured projective line
`P^1_Q \ {0, 1, ∞}` with base point over `Q`. This is the "arithmetic"
fundamental group: it fits into the homotopy exact sequence
`1 → π_1^geom(X_{Qbar}) → π_1(X_Q) → Gal(Qbar/Q) → 1`
from SGA1 IX.6.1, where the geometric fundamental group is a closed normal
subgroup and the quotient is the absolute Galois group.

## fundamentalExactSequence

The short exact sequence of profinite groups (SGA1 IX.6.1)
`1 → π_1(X_{Qbar}) → π_1(X_Q) → Gal(Qbar/Q) → 1`
for `X = P^1 \ {0, 1, ∞}`. The inclusion `π_1(X_{Qbar}) ↪ π_1(X_Q)` is
the base-change map and the projection `π_1(X_Q) ↠ Gal(Qbar/Q)` is the
structure morphism. Both are continuous homomorphisms of profinite groups, and
the sequence is exact: the image of the inclusion equals the kernel of the
projection.

## step1

### freeProfiniteGroupOnTwoIsoGeomPi1OverC

The canonical isomorphism between the free profinite group on two generators
`F̂_2` and the geometric etale fundamental group `π_1(P^1_C \ {0,1,∞})`.
This follows from the classical presentation of the topological fundamental
group of the thrice-punctured sphere as the free group on two generators
(the loops around `0` and `1`), combined with Riemann's existence theorem
identifying the profinite completion of the topological fundamental group
with the etale fundamental group.

## step2

### geomPi1OverCIsoGeomPi1OverQbar

The base-change isomorphism between the geometric etale fundamental groups
over `C` and over `Qbar`: `π_1(P^1_C \ {0,1,∞}) ≅ π_1(P^1_{Qbar} \ {0,1,∞})`.
This is an instance of the invariance of the etale fundamental group under
algebraically closed base change (SGA1 X.1.8). The isomorphism is induced by
the embedding `Qbar ↪ C`.

## step3

### rhoQToOutGeomPi1OverQbar

The outer Galois representation `ρ : Gal(Qbar/Q) →* Out(π_1(X_{Qbar}))`.
This is the outer action arising from the fundamental exact sequence
`1 → π_1(X_{Qbar}) → π_1(X_Q) → Gal(Qbar/Q) → 1` via the general
construction `ProfiniteGrp.GroupExtension.outerAction`: each element
`σ ∈ Gal(Qbar/Q)` lifts to an element of `π_1(X_Q)`, and conjugation by
that lift gives a well-defined outer automorphism of the geometric
fundamental group.

## step4

### rhoQToOutGeomPi1OverQbarInjective

The outer Galois representation `ρ : Gal(Qbar/Q) →* Out(π_1(X_{Qbar}))` is
injective. The proof uses Belyi's theorem: every algebraic curve defined over
`Qbar` admits a Belyi map to `P^1 \ {0,1,∞}`, so the action of `Gal(Qbar/Q)`
on the etale fundamental group of the tripod determines the action on all
algebraic curves over `Qbar`. If `σ` acts trivially on `Out(π_1(X_{Qbar}))`,
then `σ` acts trivially on the function fields of all curves over `Qbar`,
forcing `σ = 1`.
