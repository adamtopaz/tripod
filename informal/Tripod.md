# Tripod

This directory is the natural-language companion to the formal development in
`Tripod.lean`. The formal side defines profinite groups and maps between them; the
`informal[...]` tags point to mathematical statements and proof sketches recorded here.

The motivating object is the "tripod"

`X := P^1 \ {0,1,\infty}`,

viewed over various base fields. The classical Grothendieck--Teichmuller/Galois
representation is the outer action of `\mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q)` on the
geometric etale fundamental group of `X`.

In the current file layout, location ids are organized by mathematical role:

- General conventions (basepoints, conjugacy, `\mathrm{Out}`):
  - `informal/Tripod/Conventions.md`

- Objects (definitions of the fundamental groups):
  - `Tripod.Objects.geomPi1_tripod_over_C`: `informal/Tripod/Objects/geomPi1_tripod_over_C.md`
  - `Tripod.Objects.geomPi1_tripod_over_Qbar`:
    `informal/Tripod/Objects/geomPi1_tripod_over_Qbar.md`
  - `Tripod.Objects.arithPi1_tripod_over_Q`: `informal/Tripod/Objects/arithPi1_tripod_over_Q.md`

- Constructions (standard exact sequence and resulting action):
  - `Tripod.Constructions.pi1_exact_sequence_tripod_over_Q`:
    `informal/Tripod/Constructions/pi1_exact_sequence_tripod_over_Q.md`

- Identifications (comparison with the free profinite group and base change):
  - `Tripod.Identifications.Fhat2_iso_geomPi1_tripod_over_C`:
    `informal/Tripod/Identifications/Fhat2_iso_geomPi1_tripod_over_C.md`
  - `Tripod.Identifications.geomPi1_tripod_over_C_iso_over_Qbar`:
    `informal/Tripod/Identifications/geomPi1_tripod_over_C_iso_over_Qbar.md`

- Theorems (arithmetic input):
  - `Tripod.Theorems.galois_action_on_geomPi1_tripod_faithful`:
    `informal/Tripod/Theorems/galois_action_on_geomPi1_tripod_faithful.md`

Background note (not referenced by an `informal[...]` tag, but useful context):

- `informal/Tripod/Background/outer_galois_action.md`
