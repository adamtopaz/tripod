# tripod

This repository is a Lean 4 project centered on a single target theorem in arithmetic/profinite group theory.

## Target theorem

The main statement is in `Tripod.lean`:

- there exists an injective homomorphism
  `Gal((AlgebraicClosure Q) / Q) ->* ProfiniteGrp.Out FreeProfiniteGroupOnTwo`

where `FreeProfiniteGroupOnTwo` is the profinite completion of the free group on two generators.

The declaration currently exists as:

- `Tripod.exists_injective_hom_absoluteGaloisQ_to_outFreeProfiniteGroupOnTwo`

and is assembled from staged Informalize placeholders (not from `sorry`).

## Repository structure

- `Tripod.lean`: target theorem statement and core abbreviations.
- `informal/Tripod/`: natural-language mathematics notes (one file per `informal[...]` location id).
- `informal/Tripod.md`: index/roadmap for the `Tripod` informal locations.
- `informal/Tripod/Conventions.md`: shared conventions (basepoints, conjugacy, `Out`, etc.).
- `ToMathlib/ProfiniteGrp/Out.lean`: local construction of `ProfiniteGrp.Out` and supporting lemmas.
- `ToMathlib.lean`: entry point for local helper modules.
- `lakefile.lean`: Lake package configuration.
- `lean-toolchain`: pinned Lean toolchain version.
- `docs/`: extra project notes (not used by Informalize location checking).

## Prerequisites

- `elan` and `lake` installed
- C toolchain available (for normal Lean package builds)

Toolchain pin:

- `leanprover/lean4:v4.28.0-rc1`

## Build and check

```bash
lake exe cache get
lake build
```

Useful focused checks:

```bash
lake build Tripod
lake build ToMathlib

lake env lean Tripod.lean
lake env lean ToMathlib/ProfiniteGrp/Out.lean
```

## Current status

- The target theorem statement is in place.
- The supporting outer automorphism quotient setup for profinite groups is in place.
- The final arithmetic injectivity input is still represented by an informal placeholder.
