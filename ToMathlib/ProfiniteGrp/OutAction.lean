import ToMathlib.ProfiniteGrp.Out
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.Topology.Separation.Hausdorff

/-!
# Outer action from a short exact sequence of profinite groups

Given a short exact sequence of profinite groups `1 → N → E → Q → 1`,
we construct the outer action homomorphism `Q →* Out(N)`.

## Mathematical outline

The construction proceeds in three stages:

1. **Conjugation lifts to `Aut(N)`**: For each `e : E`, the abstract conjugation
   automorphism `conjAct(e) : MulAut(N)` (from `GroupExtension.conjAct`) is continuous,
   giving `E →* Aut(N)` in `ProfiniteGrp`.

2. **Compose with quotient**: Composing with `Aut(N) → Out(N)` gives `E →* Out(N)`.
   The kernel contains `inl(N)` because conjugation by `inl(n)` is an inner automorphism.

3. **Factor through `Q`**: Since `ker(π) = range(inl) ⊆ ker(E →* Out(N))`,
   the map factors through `Q ≅ E/ker(π)`, giving `Q →* Out(N)`.

## Main definitions

* `ProfiniteGrp.GroupExtension` : A short exact sequence of profinite groups, bundling
  `GroupExtension` data with continuous structure maps.
* `ProfiniteGrp.GroupExtension.outerAction` : the outer action `Q →* Out(N)`.
-/

open CategoryTheory Topology

namespace ProfiniteGrp

/-- A short exact sequence of profinite groups `1 → N → E → Q → 1`.

This bundles a `GroupExtension` (abstract group SES) with the data that
`N`, `E`, `Q` are profinite groups and the structure maps are continuous. -/
structure GroupExtension (N E Q : ProfiniteGrp) where
  /-- The underlying abstract group extension. -/
  ext : _root_.GroupExtension N E Q
  /-- The inclusion `N →* E` is continuous. -/
  inl_continuous : Continuous ext.inl
  /-- The projection `E →* Q` is continuous. -/
  rightHom_continuous : Continuous ext.rightHom

namespace GroupExtension

variable {N E Q : ProfiniteGrp} (S : ProfiniteGrp.GroupExtension N E Q)

/-- The inclusion `inl : N → E` is a closed embedding, since it is a continuous injection
from a compact space to a Hausdorff space. -/
theorem inl_isClosedEmbedding : IsClosedEmbedding S.ext.inl :=
  S.inl_continuous.isClosedEmbedding S.ext.inl_injective

/-- The conjugation action of `E` on `N` as abstract `MulAut`, inherited from
`_root_.GroupExtension.conjAct`. -/
noncomputable def conjMulAut : E →* MulAut N :=
  S.ext.conjAct

/-- Conjugation by `e : E` is continuous on `N`.

The proof uses that `inl` is an embedding: `conjAct e` is continuous iff
`inl ∘ conjAct e` is continuous, and `inl ∘ conjAct e = (· * · * ·⁻¹) ∘ inl`
which is continuous by `inl_conjAct_comm`. -/
private theorem conjMulAut_continuous (e : E) : Continuous (S.conjMulAut e) := by
  rw [(inl_isClosedEmbedding S).isEmbedding.continuous_iff]
  have h_eq : S.ext.inl ∘ S.conjMulAut e = fun n => e * S.ext.inl n * e⁻¹ := by
    ext n
    exact S.ext.inl_conjAct_comm
  rw [h_eq]
  exact (IsTopologicalGroup.continuous_conj (G := E) e).comp S.inl_continuous

/-- Conjugation by `e : E` as a `ContinuousMulEquiv` of `N`. -/
noncomputable def conjContinuousMulEquiv (e : E) : N ≃ₜ* N where
  toMulEquiv := S.conjMulAut e
  continuous_toFun := S.conjMulAut_continuous e
  continuous_invFun := by
    simp only [MulEquiv.invFun_eq_symm]
    -- We show (conjMulAut e).symm = conjMulAut e⁻¹, then use continuity of the latter.
    suffices h : ⇑(S.conjMulAut e).symm = ⇑(S.conjMulAut e⁻¹) by
      rw [h]
      exact S.conjMulAut_continuous e⁻¹
    ext n
    apply S.ext.inl_injective
    -- LHS: inl ((conjAct e).symm n)
    -- From inl_conjAct_comm applied at (e, (conjAct e).symm n):
    -- inl (conjAct e ((conjAct e).symm n)) = e * inl ((conjAct e).symm n) * e⁻¹
    -- which simplifies to: inl n = e * inl ((conjAct e).symm n) * e⁻¹
    have h1 := S.ext.inl_conjAct_comm (e := e) (n := (S.conjMulAut e).symm n)
    simp only [conjMulAut] at h1 ⊢
    rw [MulEquiv.apply_symm_apply] at h1
    -- h1 : inl n = e * inl ((conjAct e).symm n) * e⁻¹
    -- RHS: inl (conjAct e⁻¹ n) = e⁻¹ * inl n * (e⁻¹)⁻¹  (by inl_conjAct_comm)
    rw [S.ext.inl_conjAct_comm (e := e⁻¹) (n := n), inv_inv]
    -- Goal: inl ((conjAct e).symm n) = e⁻¹ * inl n * e
    -- From h1: inl ((conjAct e).symm n) = e⁻¹ * inl n * e
    -- From h1: inl n = e * inl (symm n) * e⁻¹
    -- We derive: inl (symm n) = e⁻¹ * inl n * e
    -- Rearrange h1:
    have key : e⁻¹ * S.ext.inl n * e =
        S.ext.inl ((S.ext.conjAct e).symm n) := by
      have := h1
      calc e⁻¹ * S.ext.inl n * e
          = e⁻¹ * (e * S.ext.inl ((S.ext.conjAct e).symm n) * e⁻¹) * e := by rw [this]
        _ = e⁻¹ * e * S.ext.inl ((S.ext.conjAct e).symm n) * (e⁻¹ * e) := by
            simp only [mul_assoc]
        _ = S.ext.inl ((S.ext.conjAct e).symm n) := by
            simp [inv_mul_cancel]
    exact key.symm

/-- Conjugation by `e : E` as a ProfiniteGrp automorphism of `N`. -/
noncomputable def conjAut (e : E) : CategoryTheory.Aut N :=
  ContinuousMulEquiv.toProfiniteGrpIso (S.conjContinuousMulEquiv e)

/-- `conjAut` applied to `x` gives the same value as the abstract `conjMulAut`. -/
@[simp]
theorem conjAut_hom_apply (e : E) (x : N) :
    (S.conjAut e).hom x = S.conjMulAut e x := by
  rfl

/-- The conjugation homomorphism `E →* Aut(N)` in `ProfiniteGrp`. -/
noncomputable def conjAutHom : E →* CategoryTheory.Aut N where
  toFun := S.conjAut
  map_one' := by
    ext x
    have h1 : (S.conjAut 1).hom x = x := by
      simp [conjAut_hom_apply, conjMulAut, _root_.GroupExtension.conjAct]
    have h2 : x = (𝟙 N : N ⟶ N) x := (ProfiniteGrp.id_apply N x).symm
    exact h1.trans h2
  map_mul' g h := by
    ext x
    simp only [conjAut_hom_apply, CategoryTheory.Aut.Aut_mul_def]
    change S.conjMulAut (g * h) x = S.conjMulAut g (S.conjMulAut h x)
    simp [conjMulAut, map_mul, MulAut.mul_apply]

/-- The composite `E →* Out(N)`, sending `e` to the class of conjugation by `e`
in the outer automorphism group. -/
noncomputable def toOutHom : E →* Out N :=
  (QuotientGroup.mk' (Inn N)).comp S.conjAutHom

/-- The kernel of `toOutHom` contains the image of `N` in `E` (via `inl`).

Conjugation by `inl(n)` restricts to conjugation by `n` on `N`,
which is an inner automorphism, hence trivial in `Out(N)`. -/
theorem toOutHom_comp_inl :
    S.toOutHom.comp S.ext.inl = 1 := by
  ext n
  simp only [toOutHom, MonoidHom.comp_apply, MonoidHom.one_apply]
  apply (QuotientGroup.eq_one_iff _).mpr
  -- Need: conjAutHom S (inl n) ∈ Inn N = range(ProfiniteGrp.conjAutHom N)
  refine ⟨n, ?_⟩
  ext x
  simp only [conjAutHom, MonoidHom.coe_mk, OneHom.coe_mk]
  -- Goal: (ProfiniteGrp.conjAutHom N n).hom x = (conjAut S (inl n)).hom x
  apply S.ext.inl_injective
  -- RHS: inl (conjAct (inl n) x) = inl(n) * inl(x) * inl(n)⁻¹
  conv_rhs =>
    rw [show (S.conjAut (S.ext.inl n)).hom x = S.ext.conjAct (S.ext.inl n) x from rfl]
    rw [S.ext.inl_conjAct_comm]
  -- LHS: inl ((conjAutHom N n).hom x) = inl(n * x * n⁻¹) = inl(n) * inl(x) * inl(n)⁻¹
  change S.ext.inl ((ProfiniteGrp.conjAut N n).hom x) = _
  rw [ProfiniteGrp.conjAut_hom_apply, map_mul, map_mul, map_inv]

/-- The outer action `Q →* Out(N)` arising from a short exact sequence
`1 → N → E → Q → 1` of profinite groups.

Each `q ∈ Q` lifts to some `e ∈ E`, and conjugation by `e` restricts to
a continuous automorphism of `N`. The image in `Out(N) = Aut(N)/Inn(N)` is
independent of the choice of lift because different lifts differ by an element
of `N`, which acts by inner automorphisms. -/
noncomputable def outerAction : Q →* Out N :=
  S.ext.rightHom.liftOfSurjective S.ext.rightHom_surjective
    ⟨S.toOutHom, by
      intro e he
      rw [MonoidHom.mem_ker]
      have hmem : e ∈ S.ext.inl.range := by
        rwa [S.ext.range_inl_eq_ker_rightHom]
      obtain ⟨n, rfl⟩ := hmem
      exact DFunLike.congr_fun S.toOutHom_comp_inl n⟩

end GroupExtension

end ProfiniteGrp
