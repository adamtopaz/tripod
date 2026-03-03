import Lake

open Lake DSL

package tripod where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions :=
  #[⟨`pp.unicode.fun, true⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, 3⟩]

require "leanprover-community" / mathlib @ git "v4.28.0"
require informalize from git "https://github.com/adamtopaz/aftk" @ "main"

@[default_target] lean_lib Tripod

lean_lib ToMathlib
