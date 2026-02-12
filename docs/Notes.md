# Tripod Blueprint Notes

This file is the initial blueprint notebook for expanded proof text.
Sections in this file are meant to be referenced from `informal` and
`formalized` declarations in Lean.

<!-- informalize:id=tripod-overview -->
## Tripod overview

Goal: formalize the target theorem in `Tripod.lean` with a clear path
from informal plan to fully formal proof.

<!-- informalize:id=main-theorem-plan -->
## Main theorem plan

Draft the high-level argument structure here before splitting into lemmas.
Use this section for the top-level strategy and dependencies.

<!-- informalize:id=supporting-lemmas-plan -->
## Supporting lemmas plan

Track helper lemmas, where they belong (`Tripod.lean` vs
`ToMathlib/**/*.lean`), and how each one supports the final theorem.

<!-- informalize:id=formalization-checklist -->
## Formalization checklist

- Replace informal placeholders with `formalized` entries.
- Confirm references remain valid with `lake exe informalize lint --module Tripod`.
- Check final soundness with `#print axioms` for key declarations.
