# Blueprint for `Tripod.lean`

This document records the high-level proof plan for
`exists_injective_hom_absoluteGaloisQ_to_outFreeProfiniteGroupOnTwo`.

## Informalize ids used in Lean

In this project, placeholders in `Tripod.lean` use dotted ids `Tripod.*` that resolve to
markdown files under `informal/Tripod/**` (see `docs/README.md` for the mapping rule).

Current tracked locations:

- Objects:
  - `Tripod.Objects.geomPi1_tripod_over_C`
  - `Tripod.Objects.geomPi1_tripod_over_Qbar`
  - `Tripod.Objects.arithPi1_tripod_over_Q`

- Constructions:
  - `Tripod.Constructions.pi1_exact_sequence_tripod_over_Q`

- Identifications:
  - `Tripod.Identifications.Fhat2_iso_geomPi1_tripod_over_C`
  - `Tripod.Identifications.geomPi1_tripod_over_C_iso_over_Qbar`

- Theorems:
  - `Tripod.Theorems.galois_action_on_geomPi1_tripod_faithful`

The index/roadmap for the informal material is `informal/Tripod.md`, and shared conventions
(basepoints, conjugacy, `Out`, etc.) live in `informal/Tripod/Conventions.md`.

## Step plan

### Geometric inputs

Introduce placeholders for the etale fundamental groups of
`P^1 - {0,1,infinity}` over `C`, over `Qbar = AlgebraicClosure Q`, and over `Q`, together
with the fundamental exact sequence over `Q`.

### Step 1: free profinite group over C

Identify `FreeProfiniteGroupOnTwo` with geometric etale `pi_1` over `C`.

### Step 2: compare C and Qbar geometric groups

Identify geometric etale `pi_1` over `C` with geometric etale `pi_1` over
`Qbar`.

### Step 3: build and transport rho

1. Define the outer Galois action from the fundamental exact sequence as
   `Gal(Qbar/Q) ->* Out(pi_1^{et}(X_{Qbar}))`.
2. Transport to `Out(pi_1^{et}(X_C))` via algebraically closed base change.
3. Transport to `Out(FreeProfiniteGroupOnTwo)` via the identification over `C`.

In `Tripod.lean` this step is implemented formally using
`ProfiniteGrp.GroupExtension.outerAction` (construction from a short exact sequence) and
transport via `ProfiniteGrp.outEquivOfIso` from `ToMathlib/ProfiniteGrp/Out.lean`.
See `informal/Tripod/Background/outer_galois_action.md` for the mathematical explanation.

### Step 4: injectivity

1. Prove injectivity over `Qbar` using arithmetic input from Belyi / dessins d'enfants.
2. Transport injectivity through the two comparison isomorphisms.

### Target theorem assembly

Combine the constructed `rho` with transported injectivity to conclude the
target existence + injectivity theorem.
