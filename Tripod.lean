import ToMathlib.ProfiniteGrp.Out
import Informalize

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
Blueprint placeholder for the geometric etale fundamental group of
`P^1 - {0,1,infinity}` over `C`.
-/
noncomputable def geomPi1ThreePuncturedLineOverC : ProfiniteGrp :=
  informal "Geometric etale pi_1 of P^1 minus 0, 1, infinity over C."
    from "docs/TripodBlueprint.md#geometric-pi1-over-c"

/--
Blueprint placeholder for the geometric etale fundamental group of
`P^1 - {0,1,infinity}` over `AlgebraicClosure ℚ`.
-/
noncomputable def geomPi1ThreePuncturedLineOverQbar : ProfiniteGrp :=
  informal "Geometric etale pi_1 of P^1 minus 0, 1, infinity over Qbar."
    from "docs/TripodBlueprint.md#geometric-pi1-over-qbar"

/--
Blueprint step 1: identify `FreeProfiniteGroupOnTwo` with the geometric etale fundamental
group of `P^1 - {0,1,infinity}` over `C`.
-/
noncomputable def freeProfiniteGroupOnTwoIsoGeomPi1OverC :
    FreeProfiniteGroupOnTwo ≅ geomPi1ThreePuncturedLineOverC :=
  informal "Identify {FreeProfiniteGroupOnTwo} with {geomPi1ThreePuncturedLineOverC}."
    from "docs/TripodBlueprint.md#step-1-free-profinite-group-over-c"

/--
Blueprint step 2: identify the geometric etale fundamental group over `C` with the one over
`AlgebraicClosure ℚ`.
-/
noncomputable def geomPi1OverCIsoGeomPi1OverQbar :
    geomPi1ThreePuncturedLineOverC ≅ geomPi1ThreePuncturedLineOverQbar :=
  informal "Identify {geomPi1ThreePuncturedLineOverC} with {geomPi1ThreePuncturedLineOverQbar}."
    from "docs/TripodBlueprint.md#step-2-base-change-c-to-qbar"

/--
Blueprint step 3a: define the outer Galois action on the geometric etale fundamental group
over `Qbar`.
-/
noncomputable def rhoQToOutGeomPi1OverQbar :
    AbsoluteGaloisGroupQ →* ProfiniteGrp.Out geomPi1ThreePuncturedLineOverQbar :=
  informal "Define the outer Galois action on {geomPi1ThreePuncturedLineOverQbar}."
    from "docs/TripodBlueprint.md#step-3-rho-to-out-geometric-pi1-over-qbar"

/-- Blueprint step 3b: transport that outer action from `Qbar` to `C`. -/
noncomputable def rhoQToOutGeomPi1OverC :
    AbsoluteGaloisGroupQ →* ProfiniteGrp.Out geomPi1ThreePuncturedLineOverC :=
  formalized
    "Transport {rhoQToOutGeomPi1OverQbar} along {geomPi1OverCIsoGeomPi1OverQbar}."
    from "docs/TripodBlueprint.md#step-3-rho-to-out-geometric-pi1-over-c"
    as
      (ProfiniteGrp.outEquivOfIso geomPi1OverCIsoGeomPi1OverQbar).symm.toMonoidHom.comp
        rhoQToOutGeomPi1OverQbar

/--
Blueprint step 3c: construct `ρ` in `Out(FreeProfiniteGroupOnTwo)` by transporting the
geometric action through the identifications.
-/
noncomputable def rhoQToOutFreeProfiniteGroupOnTwo :
    AbsoluteGaloisGroupQ →* ProfiniteGrp.Out FreeProfiniteGroupOnTwo :=
  formalized
    "Transport {rhoQToOutGeomPi1OverC} along {freeProfiniteGroupOnTwoIsoGeomPi1OverC}."
    from "docs/TripodBlueprint.md#step-3-rho-to-out-free-profinite-group"
    as
      (ProfiniteGrp.outEquivOfIso freeProfiniteGroupOnTwoIsoGeomPi1OverC).symm.toMonoidHom.comp
        rhoQToOutGeomPi1OverC

/--
Blueprint step 4a: injectivity over `Qbar`, with arithmetic input from Belyi's theorem.
-/
theorem rhoQToOutGeomPi1OverQbar_injective :
    Function.Injective rhoQToOutGeomPi1OverQbar := by
  informal "Prove injectivity of {rhoQToOutGeomPi1OverQbar} via Belyi."
    from "docs/TripodBlueprint.md#step-4-belyi-injectivity-qbar"

/--
Blueprint step 4b: deduce injectivity of `ρ` from injectivity over `Qbar` via transport.
-/
theorem rhoQToOutFreeProfiniteGroupOnTwo_injective :
    Function.Injective rhoQToOutFreeProfiniteGroupOnTwo := by
  formalized
    "Deduce injectivity of {rhoQToOutFreeProfiniteGroupOnTwo} \
      from {rhoQToOutGeomPi1OverQbar_injective}."
    from "docs/TripodBlueprint.md#step-4-transport-injectivity"
    as
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
