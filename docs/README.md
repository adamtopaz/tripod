## docs/ folder

This folder contains human-facing notes about the project blueprint.

The Informalize package no longer reads doc references from `docs/*.md`.
Location checking now uses dotted ids inside `informal[...]` and resolves
them against markdown headings under `informal/*.md`.

### Informalize id mapping

Use this Lean syntax:

```lean
informal[Tripod.step1.freeProfiniteGroupOnTwoIsoGeomPi1OverC]
```

This resolves to:

- markdown file: `informal/Tripod.md`
- heading path: `step1` then `freeProfiniteGroupOnTwoIsoGeomPi1OverC`

### Conventions

- Keep ids stable once referenced in Lean.
- Use heading titles that exactly match id components.
- Keep one clear heading path per placeholder declaration.
