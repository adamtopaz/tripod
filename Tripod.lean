import Tripod.Basic

import ToMathlib.ProfiniteGrp.Out

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-- The absolute Galois group `Gal(ℚ̄/ℚ)`. -/
abbrev AbsoluteGaloisGroupQ : Type :=
  Gal((AlgebraicClosure ℚ) / ℚ)

/-- The free profinite group on two generators. -/
noncomputable abbrev FreeProfiniteGroupOnTwo : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup (Fin 2)))

/--
Target theorem: there exists an injective homomorphism from the absolute Galois group of `ℚ`
to the outer automorphism group of the free profinite group on two generators.
-/
theorem exists_injective_hom_absoluteGaloisQ_to_outFreeProfiniteGroupOnTwo :
    ∃ ρ : AbsoluteGaloisGroupQ →* ProfiniteGrp.Out FreeProfiniteGroupOnTwo,
      Function.Injective ρ := by
  sorry
