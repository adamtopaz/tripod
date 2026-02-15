## docs/ folder

This folder contains extra human-facing notes about the project blueprint. It is not used
by Informalize.

Informalize location checking uses dotted ids inside `informal[...]` and resolves them to
markdown files under `informal/`.

### Informalize id mapping

In this repository, a location id of the form `Tripod.<A>.<B>. ... .<Z>` resolves to a file

`informal/Tripod/A/B/.../Z.md`.

For example, the Lean term

```lean
informal[Tripod.Objects.geomPi1_tripod_over_C]
```

resolves to the markdown file `informal/Tripod/Objects/geomPi1_tripod_over_C.md`.

### Conventions

- Keep ids stable once referenced in Lean.
- Keep one markdown file per location id under `informal/Tripod/**`.
- Use `# <full.location.id>` as the file title.
- Put shared basepoint/`Out` conventions in `informal/Tripod/Conventions.md` and link to it.
