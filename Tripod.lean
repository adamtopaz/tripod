import ToMathlib.ProfiniteGrp.Out
import ToMathlib.ProfiniteGrp.OutAction
import Informalize

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-- The absolute Galois group `Gal(ℚ̄/ℚ)`. -/
abbrev AbsoluteGaloisGroupQ : Type :=
  Gal((AlgebraicClosure ℚ) / ℚ)

/-- The free profinite group on two generators. -/
noncomputable abbrev FreeProfiniteGroupOnTwo : ProfiniteGrp.{0} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup (Fin 2)))

/--
Blueprint placeholder for the geometric etale fundamental group of
`P^1 - {0,1,infinity}` over `C`.
-/
noncomputable def geomPi1ThreePuncturedLineOverC : ProfiniteGrp.{0} :=
  informal[Tripod.Objects.geomPi1_tripod_over_C]

/--
Blueprint placeholder for the geometric etale fundamental group of
`P^1 - {0,1,infinity}` over `AlgebraicClosure ℚ`.
-/
noncomputable def geomPi1ThreePuncturedLineOverQbar : ProfiniteGrp.{0} :=
  informal[Tripod.Objects.geomPi1_tripod_over_Qbar]

/--
The arithmetic etale fundamental group of `P^1 - {0,1,infinity}` over `ℚ`.

This fits into the fundamental exact sequence
`1 → π₁(X_Q̄) → π₁(X_Q) → Gal(Q̄/Q) → 1`
from SGA1, where the geometric fundamental group is a normal subgroup of the
arithmetic one, with quotient the absolute Galois group.
-/
noncomputable def arithPi1ThreePuncturedLineOverQ : ProfiniteGrp.{0} :=
  informal[Tripod.Objects.arithPi1_tripod_over_Q]

/--
The fundamental exact sequence of etale fundamental groups:
`1 → π₁(X_Q̄) → π₁(X_Q) → Gal(Q̄/Q) → 1`

This is a short exact sequence of profinite groups (SGA1, IX.6.1) for
`X = P^1 - {0,1,infinity}`. It encodes the data that:
- `geomPi1ThreePuncturedLineOverQbar` embeds into `arithPi1ThreePuncturedLineOverQ`,
- the quotient is `AbsoluteGaloisGroupQ`,
- the inclusion and projection are continuous group homomorphisms.
-/
noncomputable def fundamentalExactSequence :
    ProfiniteGrp.GroupExtension
      geomPi1ThreePuncturedLineOverQbar
      arithPi1ThreePuncturedLineOverQ
      (ProfiniteGrp.of AbsoluteGaloisGroupQ) :=
  informal[Tripod.Constructions.pi1_exact_sequence_tripod_over_Q]

/--
Identify `FreeProfiniteGroupOnTwo` with the geometric etale fundamental group of
`P^1 - {0,1,infinity}` over `C` (Riemann existence + `π₁` of the thrice-punctured sphere).
-/
noncomputable def freeProfiniteGroupOnTwoIsoGeomPi1OverC :
    FreeProfiniteGroupOnTwo ≅ geomPi1ThreePuncturedLineOverC :=
  informal[Tripod.Identifications.Fhat2_iso_geomPi1_tripod_over_C]

/--
Identify the geometric etale fundamental group over `C` with the one over `AlgebraicClosure ℚ`
(invariance under algebraically closed base change).
-/
noncomputable def geomPi1OverCIsoGeomPi1OverQbar :
    geomPi1ThreePuncturedLineOverC ≅ geomPi1ThreePuncturedLineOverQbar :=
  informal[Tripod.Identifications.geomPi1_tripod_over_C_iso_over_Qbar]

/--
Blueprint step 3a: define the outer Galois action on the geometric etale fundamental group
over `Qbar`.

This is the outer action `Gal(Q̄/Q) →* Out(π₁(X_Q̄))` arising from the
fundamental exact sequence via the general construction
`ProfiniteGrp.GroupExtension.outerAction`.
-/
noncomputable def rhoQToOutGeomPi1OverQbar :
    AbsoluteGaloisGroupQ →* ProfiniteGrp.Out geomPi1ThreePuncturedLineOverQbar :=
  fundamentalExactSequence.outerAction

/-- Blueprint step 3b: transport that outer action from `Qbar` to `C`. -/
noncomputable def rhoQToOutGeomPi1OverC :
    AbsoluteGaloisGroupQ →* ProfiniteGrp.Out geomPi1ThreePuncturedLineOverC :=
  (ProfiniteGrp.outEquivOfIso geomPi1OverCIsoGeomPi1OverQbar).symm.toMonoidHom.comp
    rhoQToOutGeomPi1OverQbar

/--
Blueprint step 3c: construct `ρ` in `Out(FreeProfiniteGroupOnTwo)` by transporting the
geometric action through the identifications.
-/
noncomputable def rhoQToOutFreeProfiniteGroupOnTwo :
    AbsoluteGaloisGroupQ →* ProfiniteGrp.Out FreeProfiniteGroupOnTwo :=
  (ProfiniteGrp.outEquivOfIso freeProfiniteGroupOnTwoIsoGeomPi1OverC).symm.toMonoidHom.comp
    rhoQToOutGeomPi1OverC

/--
Faithfulness of the outer Galois action on the geometric fundamental group over `Qbar`
(arithmetic input from Belyi's theorem / dessins d'enfants).
-/
theorem rhoQToOutGeomPi1OverQbar_injective :
    Function.Injective rhoQToOutGeomPi1OverQbar := by
  exact informal[Tripod.Theorems.galois_action_on_geomPi1_tripod_faithful]

/--
Blueprint step 4b: deduce injectivity of `ρ` from injectivity over `Qbar` via transport.
-/
theorem rhoQToOutFreeProfiniteGroupOnTwo_injective :
    Function.Injective rhoQToOutFreeProfiniteGroupOnTwo := by
  let outQbarToC :
      ProfiniteGrp.Out geomPi1ThreePuncturedLineOverQbar →*
        ProfiniteGrp.Out geomPi1ThreePuncturedLineOverC :=
    (ProfiniteGrp.outEquivOfIso geomPi1OverCIsoGeomPi1OverQbar).symm.toMonoidHom
  let outCToFree :
      ProfiniteGrp.Out geomPi1ThreePuncturedLineOverC →*
        ProfiniteGrp.Out FreeProfiniteGroupOnTwo :=
    (ProfiniteGrp.outEquivOfIso freeProfiniteGroupOnTwoIsoGeomPi1OverC).symm.toMonoidHom
  have hOutQbarToC : Function.Injective outQbarToC := by
    simpa [outQbarToC] using
      (ProfiniteGrp.outEquivOfIso geomPi1OverCIsoGeomPi1OverQbar).symm.injective
  have hOutCToFree : Function.Injective outCToFree := by
    simpa [outCToFree] using
      (ProfiniteGrp.outEquivOfIso freeProfiniteGroupOnTwoIsoGeomPi1OverC).symm.injective
  have hToC : Function.Injective rhoQToOutGeomPi1OverC := by
    simpa [rhoQToOutGeomPi1OverC, outQbarToC] using
      hOutQbarToC.comp rhoQToOutGeomPi1OverQbar_injective
  simpa [rhoQToOutFreeProfiniteGroupOnTwo, outCToFree] using
    hOutCToFree.comp hToC

/--
Target theorem: there exists an injective homomorphism from the absolute Galois group of `ℚ`
to the outer automorphism group of the free profinite group on two generators.
-/
theorem exists_injective_hom_absoluteGaloisQ_to_outFreeProfiniteGroupOnTwo :
    ∃ ρ : AbsoluteGaloisGroupQ →* ProfiniteGrp.Out FreeProfiniteGroupOnTwo,
      Function.Injective ρ := by
  refine ⟨rhoQToOutFreeProfiniteGroupOnTwo, ?_⟩
  exact rhoQToOutFreeProfiniteGroupOnTwo_injective
