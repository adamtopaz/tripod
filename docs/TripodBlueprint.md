# Blueprint for `Tripod.lean`

This file records the high-level proof plan for
`exists_injective_hom_absoluteGaloisQ_to_outFreeProfiniteGroupOnTwo`.

Current Lean placeholder names used in `Tripod.lean`:

- `geomPi1ThreePuncturedLineOverC`
- `geomPi1ThreePuncturedLineOverQbar`
- `rhoQToOutGeomPi1OverQbar`
- `rhoQToOutGeomPi1OverC`
- `rhoQToOutFreeProfiniteGroupOnTwo`

Dependency note: in Informalize descriptions, `{declName}` interpolation is
used to record explicit artifact dependencies.

<!-- informalize:id=geometric-pi1-over-c -->
## Geometric pi_1 over C

Introduce a placeholder object for the geometric etale fundamental group
of `P^1 - {0,1,infinity}` over `C`, viewed as a profinite group.

<!-- informalize:id=geometric-pi1-over-qbar -->
## Geometric pi_1 over Qbar

Introduce a placeholder object for the geometric etale fundamental group
of `P^1 - {0,1,infinity}` over `Qbar = AlgebraicClosure Q`.

<!-- informalize:id=step-1-free-profinite-group-over-c -->
## Step 1: free profinite group as geometric etale pi_1 over C

Identify the free profinite group on two generators with the etale
fundamental group of `P^1 - {0,1,infinity}` over `C` as an isomorphism
of profinite groups.

<!-- informalize:id=step-2-base-change-c-to-qbar -->
## Step 2: compare geometric etale pi_1 over C and over Qbar

Identify the etale fundamental group of `P^1 - {0,1,infinity}` over `C`
with the corresponding geometric etale fundamental group over
`Qbar = AlgebraicClosure Q`.

<!-- informalize:id=out-iso-from-group-iso -->
## Transport to outer automorphism groups

Show that an isomorphism of profinite groups induces an isomorphism
between their outer automorphism groups.
This is implemented as `ProfiniteGrp.outEquivOfIso` in
`ToMathlib/ProfiniteGrp/Out.lean`.

<!-- informalize:id=step-3-fundamental-exact-sequence -->
## Step 3: construct rho from the fundamental exact sequence over Q

Use the fundamental exact sequence for `P^1 - {0,1,infinity}` over `Q`
to obtain the outer action of `Gal(Qbar/Q)` on the geometric etale
fundamental group. Via the identifications from Steps 1 and 2, this
produces the homomorphism

`rho : Gal(Qbar/Q) ->* Out(FreeProfiniteGroupOnTwo)`.

<!-- informalize:id=step-3-rho-to-out-geometric-pi1-over-qbar -->
## Step 3a: outer action on geometric pi_1 over Qbar

First define the outer Galois action

`Gal(Qbar/Q) ->* Out(pi_1_geom over Qbar)`

from the fundamental exact sequence over `Q`.

<!-- informalize:id=step-3-rho-to-out-geometric-pi1-over-c -->
## Step 3b: transport the action to geometric pi_1 over C

Use the comparison isomorphism between geometric etale fundamental groups
over `C` and `Qbar` to obtain

`Gal(Qbar/Q) ->* Out(pi_1_geom over C)`.

<!-- informalize:id=step-3-rho-to-out-free-profinite-group -->
## Step 3c: transport to the target outer automorphism group

Use the identification between `FreeProfiniteGroupOnTwo` and the
geometric etale fundamental group over `C` to obtain the target map
into `Out(FreeProfiniteGroupOnTwo)`.

<!-- informalize:id=step-4-belyi-injectivity -->
## Step 4: prove injectivity of rho using Belyi

Show that `rho` is injective, with the key arithmetic input given by
Belyi's theorem.

<!-- informalize:id=step-4-belyi-injectivity-qbar -->
## Step 4a: Belyi injectivity over Qbar

Prove injectivity for the action

`Gal(Qbar/Q) ->* Out(pi_1_geom over Qbar)`

using Belyi's theorem.

<!-- informalize:id=step-4-transport-injectivity -->
## Step 4b: transport injectivity to the target rho

Deduce injectivity of the final target map by transporting the `Qbar`
injectivity statement through the isomorphisms from Steps 1 and 2.
Concretely, this is composition with maps induced by group isomorphisms,
which preserves injectivity.

<!-- informalize:id=target-theorem-assembly -->
## Target theorem assembly

Combine the construction of `rho` from Step 3 with injectivity from
Step 4 to conclude the target theorem in `Tripod.lean`.
