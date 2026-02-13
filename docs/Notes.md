# Tripod Blueprint Notes

This file is a planning notebook for long-form prose.
Informalize location checks do not read this file directly; they read
`informal/Tripod.md` through dotted ids used in `Tripod.lean`.

## Tripod overview

Goal: formalize the target theorem in `Tripod.lean` while keeping intermediate
declarations organized with explicit informal placeholders.

## Main theorem plan

- Build the geometric objects over `C` and `Qbar`.
- Build and transport the outer action of `Gal(Qbar/Q)`.
- Prove injectivity over `Qbar` and transport it to the target representation.

## Supporting lemmas plan

Track helper lemmas and transport lemmas in `ToMathlib/**/*.lean`, keeping
`Tripod.lean` focused on theorem-level orchestration.

## Informalize checklist

- Keep each placeholder tagged as `informal[Tripod....]`.
- Keep heading paths in `informal/Tripod.md` synchronized with Lean ids.
- Use CLI checks:
  - `lake exe informalize status --module Tripod`
  - `lake exe informalize deps --module Tripod`
  - `lake exe informalize decls --module Tripod --with-locations`
  - `lake exe informalize locations --module Tripod`
- Check final soundness with `#print axioms` for key declarations.
