# AGENTS Guide for tripod

This file is for autonomous coding agents working in this repository.
It documents practical commands and coding conventions used here.

## Scope and goals
- Repository type: Lean 4 + mathlib formalization project.
- Primary goal: formalize a target theorem in `Tripod.lean`.
- Keep edits focused on `Tripod.lean` and `ToMathlib/**/*.lean` unless task says otherwise.
- Do not edit generated files under `.lake/`.
- Avoid touching workflow/release files unless the task is CI-related.

## Repository map
- `Tripod.lean`: main theorem statement and top-level project declarations.
- `ToMathlib/ProfiniteGrp/Out.lean`: local definitions/lemmas for outer automorphisms.
- `ToMathlib.lean`: umbrella import for local helper modules.
- `lakefile.lean`: package config and Lean options.
- `lean-toolchain`: pinned Lean version.
- `.github/workflows/*.yml`: CI automation and dependency/update workflows.

## Toolchain
- Lean toolchain pin: `leanprover/lean4:v4.28.0-rc1`.
- Package manager/build tool: `lake`.
- Main dependencies: `mathlib`, `informalize` (pinned by `lake-manifest.json`).
- First-time setup requires `elan`, `lake`, and a working C toolchain.
- Use `lake env ...` when invoking Lean tools so project dependencies are in scope.

## Build, lint, and test commands
- Fetch prebuilt dependency cache (recommended before first build):
```bash
lake exe cache get
```
- Full project build (closest local equivalent to CI compile checks):
```bash
lake build
```
- Build only the main library target:
```bash
lake build Tripod
```
- Build only local helper library target:
```bash
lake build ToMathlib
```
- Type-check a single Lean file (best "single test" equivalent in this repo):
```bash
lake env lean Tripod.lean
lake env lean ToMathlib/ProfiniteGrp/Out.lean
```
- If a module uses `Informalize`, run module-scoped informalization checks:
```bash
lake exe informalize status --module Tripod
lake exe informalize deps --module Tripod
lake exe informalize decls --module Tripod --with-locations
lake exe informalize locations --module Tripod
```
- There is currently no separate unit-test framework configured.
- Treat file/module elaboration as the test signal.
- Linting is integrated into elaboration via Lean options (see below).

## Informalize tooling (gradual formalization)
- `informalize` is an intentionally unsound staging framework based on `Informalize.Informal`.
- Current syntax is centered on term elaboration via `informal` (there is no
  `formalized` wrapper in the current release).
- Add `import Informalize` in files that use `informal` placeholders.
- Definitions using `informal` should usually be marked `noncomputable`.
- Soundness gate for final claims: run `#print axioms <DeclName>` and ensure `Informalize.Informal` is absent.
- **IMPORTANT**: Never replace `informal` placeholders with `axiom`, `opaque`, `sorry`, or
  any other mechanism. The whole point of the `informal` elaborator is to serve as the
  staging/placeholder system for unformalized mathematics. Declarations stay as `informal`
  until they are genuinely formalized with real definitions and proofs.
- **IMPORTANT**: Do not "stub" missing mathematics with oversimplified/trivial definitions
  (e.g. defining a complex group as `PUnit`, using `by trivial`, etc.) even temporarily.
  Use the `informal[...]` elaborator for placeholders so the intended content is tracked
  and documented in `informal/*.md`.

- Core syntax (term forms):
```lean
informal
informal x y
informal[Tripod.Objects.geomPi1_tripod_over_C]
informal[Tripod.Theorems.galois_action_on_geomPi1_tripod_faithful] x
```

- Location ids are dotted names that map to markdown files:
  - `informal[Tripod.Objects.geomPi1_tripod_over_C]` resolves to
    `informal/Tripod/Objects/geomPi1_tripod_over_C.md`.
  - Validation happens during elaboration; missing files are hard errors.

- Writing style for `informal/`:
  - Prefer research-mathematics prose over "project management" language.
  - Keep basepoint/`Out` conventions consistent; see `informal/Tripod/Conventions.md`.

- Informal markdown source:
  - Keep one markdown file per location id under `informal/<Root>/...`.
  - For this repo, placeholder ids are rooted in `informal/Tripod/**/*.md`.
  - Using `# <full.location.id>` as the file title is recommended for clarity.

- CLI equivalents (outside Lean files):
```bash
lake exe informalize status --module Tripod
lake exe informalize deps --module Tripod
lake exe informalize decls --module Tripod
lake exe informalize decls --module Tripod --with-locations
lake exe informalize decl --module Tripod --decl geomPi1ThreePuncturedLineOverC
lake exe informalize locations --module Tripod
lake exe informalize location --module Tripod --location Tripod.Objects.geomPi1_tripod_over_C
```

- Dependency verification workflow:
  - Run `lake exe informalize deps --module <Module.Name>` to inspect dependency edges among
    informal declarations.
  - Use `lake exe informalize decls --module <Module.Name> --with-locations` and
    `lake exe informalize locations --module <Module.Name>` to verify location coverage.
  - Dependencies are inferred from used constants, including transitive traversal through
    non-informal bridge declarations.

- CLI flag rules:
  - `--module` / `-m` is required and repeatable.
  - `--decl` is required for `decl`.
  - `--location` is required for `location`.
  - `--bare-only` and `--with-locations` are only for `decls`.

## Single-test workflow guidance
- For a change in one file, run `lake env lean path/to/File.lean` first.
- Then run `lake build Tripod` or `lake build ToMathlib` for target-level confidence.
- If `Informalize` syntax/metadata changed, also run `lake exe informalize status --module <Module.Name>`
  and `lake exe informalize deps --module <Module.Name>`.
- Before finalizing substantial changes, run full `lake build`.
- If a declaration is complex, isolate proof experiments in a temporary scratch file, then port final proof.
- Delete temporary scratch files before finishing.

## CI behavior you should match locally
- `.github/workflows/lean_action_ci.yml` runs `leanprover/lean-action@v1` and `leanprover-community/docgen-action@v1`.
- `.github/workflows/update.yml` handles mathlib dependency update PRs.
- `.github/workflows/create-release.yml` tags releases when `lean-toolchain` changes on `main`/`master`.
- Local minimum for CI parity: run `lake build` successfully.

## Lean options and their implications
- Configured in `lakefile.lean`:
- `relaxedAutoImplicit = false`.
- `weak.linter.mathlibStandardSet = true`.
- `maxSynthPendingDepth = 3`.
- Practical consequences:
- Be explicit with binders/implicit arguments when needed.
- Do not rely on permissive auto-implicit behavior.
- Resolve linter warnings instead of ignoring them.
- Keep typeclass search manageable; add annotations when inference stalls.

## Import conventions
- Keep imports at the top of the file.
- Use one import per line.
- Prefer explicit imports over broad umbrella imports.
- In this repo, local imports often appear before `Mathlib.*` imports; follow existing file style.
- Group related imports and keep ordering stable (usually lexical by module path).
- Remove unused imports introduced during refactors.

## Naming conventions
- Use `UpperCamelCase` for structures/types/type abbreviations.
- Use `lowerCamelCase` for defs and many lemmas, matching existing files.
- For long theorem names, keep descriptive underscore-separated segments when helpful.
- Keep names specific to the mathematical object and morphism direction.
- Avoid single-letter names except for local binders in short scopes.

## Declaration and proof style
- Add docstrings (`/-- ... -/`) for public or non-obvious declarations.
- Keep theorem statements readable with aligned continuation indentation.
- Prefer structured tactic proofs (`by` blocks with `intro`, `refine`, `rcases`, `ext`).
- Use `have` for intermediate claims that clarify proof intent.
- Prefer `simp`/`simpa` with explicit rewrite sets for fragile goals.
- Use `rfl` when definitional equality suffices.
- Use `noncomputable` explicitly where required.
- Keep namespace boundaries explicit (`namespace ... end ...`).
- Minimize `open` directives; open only what is needed.

## Formatting conventions
- Indentation: 2 spaces for continuation lines in declarations/proofs.
- Keep line lengths readable (around 100 chars; split long statements/proofs).
- Preserve blank lines between top-level declarations.
- Keep notation and unicode consistent with existing Lean/mathlib usage.
- Do not reformat unrelated code while making targeted edits.

## Error handling and quality bar
- In Lean code, "error handling" means managing proof obligations and inference failures clearly.
- Prefer explicit type annotations over brittle coercion chains.
- When `simp` or typeclass search fails, narrow the goal with helper lemmas.
- Avoid adding `set_option` directives to silence problems unless explicitly requested.
- Do not introduce new `sorry` placeholders unless the task explicitly allows it.
- The project uses `informal[...]` placeholders for unfinished mathematics; do not replace them with `sorry`.

## Working with this repository as an agent
- Read `Tripod.lean` and relevant `ToMathlib/**/*.lean` files before editing.
- Keep changes minimal and mathematically local.
- Prefer extending existing local helpers over duplicating near-identical lemmas.
- If a proof depends on upstream mathlib facts, import the narrowest module that works.
- After edits, run at least one focused file check plus one target build.
- For larger edits, run full `lake build`.

## Cursor and Copilot instruction files
- Checked for Cursor rules in `.cursor/rules/` and `.cursorrules`: none found.
- Checked for Copilot instructions in `.github/copilot-instructions.md`: none found.
- If any of these files are added later, treat them as higher-priority repository instructions.
- Update this `AGENTS.md` summary when such files appear.

## Quick command cheat sheet
```bash
# bootstrap dependencies
lake exe cache get

# full build
lake build

# focused builds
lake build Tripod
lake build ToMathlib

# informalize checks
lake exe informalize status --module Tripod
lake exe informalize deps --module Tripod
lake exe informalize decls --module Tripod --with-locations
lake exe informalize locations --module Tripod

# single-file check (single-test equivalent)
lake env lean Tripod.lean
lake env lean ToMathlib/ProfiniteGrp/Out.lean
```

Keep this file accurate as commands or conventions evolve.
