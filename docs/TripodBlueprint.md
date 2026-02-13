# Blueprint for `Tripod.lean`

This document records the high-level proof plan for
`exists_injective_hom_absoluteGaloisQ_to_outFreeProfiniteGroupOnTwo`.

## Informalize ids used in Lean

The current Informalize version resolves ids from `informal/*.md` headings.
In this project, placeholders in `Tripod.lean` use ids rooted at
`informal/Tripod.md`:

- `Tripod.geometricPi1OverC`
- `Tripod.geometricPi1OverQbar`
- `Tripod.step1.freeProfiniteGroupOnTwoIsoGeomPi1OverC`
- `Tripod.step2.geomPi1OverCIsoGeomPi1OverQbar`
- `Tripod.step3.rhoQToOutGeomPi1OverQbar`
- `Tripod.step4.rhoQToOutGeomPi1OverQbarInjective`

The canonical markdown source for these ids is `informal/Tripod.md`.

## Step plan

### Geometric inputs

Introduce placeholders for geometric etale fundamental groups of
`P^1 - {0,1,infinity}` over `C` and over `Qbar = AlgebraicClosure Q`.

### Step 1: free profinite group over C

Identify `FreeProfiniteGroupOnTwo` with geometric etale `pi_1` over `C`.

### Step 2: compare C and Qbar geometric groups

Identify geometric etale `pi_1` over `C` with geometric etale `pi_1` over
`Qbar`.

### Step 3: build and transport rho

1. Define the outer Galois action
   `Gal(Qbar/Q) ->* Out(pi_1_geom over Qbar)`.
2. Transport to `Out(pi_1_geom over C)`.
3. Transport to `Out(FreeProfiniteGroupOnTwo)`.

The transport infrastructure uses
`ProfiniteGrp.outEquivOfIso` from `ToMathlib/ProfiniteGrp/Out.lean`.

### Step 4: injectivity

1. Prove injectivity over `Qbar` using arithmetic input from Belyi.
2. Transport injectivity through the two comparison isomorphisms.

### Target theorem assembly

Combine the constructed `rho` with transported injectivity to conclude the
target existence + injectivity theorem.
