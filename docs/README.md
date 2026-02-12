## docs/ folder

This folder contains markdown notes used by the Informalize toolkit.
Each expandable explanation should live in a markdown file and include
an inline marker id that Lean declarations can reference.

### Marker format

Use this exact HTML comment format above the relevant section:

```md
<!-- informalize:id=my-marker-id -->
```

### Referencing from Lean

Reference a marker with a repo-relative path plus `#id`:

```lean
informal "proof sketch" from "docs/Notes.md#my-marker-id"
formalized "proof sketch" from "docs/Notes.md#my-marker-id" as by
  -- proof term
  sorry
```

### Naming conventions

- Use lowercase kebab-case ids.
- Keep ids stable once referenced in Lean.
- Prefer one marker per conceptual step in a proof plan.
