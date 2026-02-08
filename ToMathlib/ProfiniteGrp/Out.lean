import Mathlib.CategoryTheory.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Group.Basic

open CategoryTheory

namespace ProfiniteGrp

/-- Conjugation by `g` as a continuous multiplicative equivalence of `G`. -/
noncomputable def conjContinuousMulEquiv (G : ProfiniteGrp) (g : G) : G ≃ₜ* G where
  toMulEquiv := MulAut.conj g
  continuous_toFun := IsTopologicalGroup.continuous_conj g
  continuous_invFun := by
    simpa [MulAut.conj_symm_apply, inv_inv] using
      (IsTopologicalGroup.continuous_conj (G := G) g⁻¹)

/-- Conjugation by `g` as an automorphism in `ProfiniteGrp`. -/
noncomputable def conjAut (G : ProfiniteGrp) (g : G) : CategoryTheory.Aut G :=
  ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso (conjContinuousMulEquiv G g)

@[simp] lemma conjAut_hom_apply (G : ProfiniteGrp) (g x : G) :
    (conjAut G g).hom x = g * x * g⁻¹ := by
  rfl

@[simp] lemma conjAut_inv_apply (G : ProfiniteGrp) (g x : G) :
    (conjAut G g).inv x = g⁻¹ * x * g := by
  rfl

/-- The homomorphism sending `g` to conjugation by `g`. -/
noncomputable def conjAutHom (G : ProfiniteGrp) : G →* CategoryTheory.Aut G where
  toFun := conjAut G
  map_one' := by
    ext x
    have h1 : (conjAut G 1).hom x = x := by
      simp [conjAut_hom_apply]
    have h2 : x = (𝟙 G : G ⟶ G) x := (ProfiniteGrp.id_apply G x).symm
    exact h1.trans h2
  map_mul' g h := by
    ext x
    simp [CategoryTheory.Aut.Aut_mul_def, conjAut_hom_apply, mul_assoc]

/-- The inner automorphism subgroup of a profinite group. -/
noncomputable def Inn (G : ProfiniteGrp) : Subgroup (CategoryTheory.Aut G) :=
  (conjAutHom G).range

instance innNormal (G : ProfiniteGrp) : (Inn G).Normal := by
  refine ⟨?_⟩
  intro a ha b
  rcases ha with ⟨g, rfl⟩
  refine ⟨b.hom g, ?_⟩
  ext x
  suffices hx : x = (Hom.hom b.hom) ((Hom.hom b⁻¹.hom) x) by
    simpa [conjAutHom, CategoryTheory.Aut.Aut_mul_def, conjAut_hom_apply, mul_assoc] using hx
  exact (ProfiniteGrp.hom_inv_apply (e := b) (x := x)).symm

/-- The outer automorphism group of a profinite group. -/
abbrev Out (G : ProfiniteGrp) : Type _ :=
  CategoryTheory.Aut G ⧸ Inn G

instance outGroup (G : ProfiniteGrp) : Group (Out G) := by
  infer_instance

end ProfiniteGrp
