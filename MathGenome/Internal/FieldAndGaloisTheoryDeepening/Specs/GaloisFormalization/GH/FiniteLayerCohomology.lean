import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import Mathlib.Algebra.Colimit.Module

/-! The ordinary finite-layer diagram and its comparison with continuous cohomology. -/

namespace Specs.GaloisFormalization.GH.FiniteLayerCohomology

open KrullLayers
open GaloisFormalization.GH.Model

universe u v w

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.checkUnivs false

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
variable (M : Type w) [AddCommGroup M] [DistribMulAction Gal(L/k) M]
variable (E : FiniteGaloisIntermediateField k L)

/-- The coefficients at a finite Galois layer are the points fixed by its kernel. -/
abbrev LayerCoefficients : Submodule ℤ M :=
  fixedCoefficients Gal(L/k) M (layerKernel E)

/-- Identify the quotient by the fixing subgroup with the finite Galois group. -/
def quotientLayerEquiv : (Gal(L/k) ⧸ layerKernel E) ≃* LayerGroup E :=
  QuotientGroup.liftEquiv _
    (AlgEquiv.restrictNormalHom_surjective L)
    (E.toIntermediateField.restrictNormalHom_ker.symm)

@[simp]
theorem quotientLayerEquiv_mk (g : Gal(L/k)) :
    quotientLayerEquiv E (QuotientGroup.mk' (layerKernel E) g) = restrict E g := rfl

/-- The action transported from the quotient on the same fixed coefficients. -/
instance layerAction : DistribMulAction (LayerGroup E) (LayerCoefficients M E) :=
  DistribMulAction.compHom _ (quotientLayerEquiv E).symm.toMonoidHom

theorem layerAction_restrict (g : Gal(L/k)) (m : LayerCoefficients M E) :
    ((restrict E g • m : LayerCoefficients M E) : M) = g • (m : M) := by
  change (((quotientLayerEquiv E).symm (restrict E g) • m : LayerCoefficients M E) : M) = _
  rw [← quotientLayerEquiv_mk, MulEquiv.symm_apply_apply, quotientFixedAction_mk]

variable {E} {F : FiniteGaloisIntermediateField k L}

/-- Raising the layer includes its fixed coefficients into those of the larger layer. -/
def includeCoefficients (h : E ≤ F) : LayerCoefficients M E →+ LayerCoefficients M F :=
  (Submodule.inclusion (show LayerCoefficients M E ≤ LayerCoefficients M F from
    fun _ hm g => hm ⟨g, IntermediateField.fixingSubgroup_le h g.property⟩)).toAddMonoidHom

omit [IsGalois k L] in
@[simp]
theorem includeCoefficients_apply (h : E ≤ F) (m : LayerCoefficients M E) :
    ((includeCoefficients M h m : LayerCoefficients M F) : M) = (m : M) := rfl

private theorem restrict_transition (h : E ≤ F) (g : Gal(L/k)) :
    transition h (restrict F g) = restrict E g := by
  ext x
  change ((transition h (restrict F g)) x : L) = (restrict E g x : L)
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq' rfl
  calc
    ((transition h (restrict F g)) x : L) =
        (restrict F g (IntermediateField.inclusion h x) : L) :=
      congrArg (fun y : F => (y : L)) (AlgEquiv.restrictNormal_commutes (restrict F g) E x)
    _ = g (x : L) :=
      AlgEquiv.restrictNormalHom_apply F.toIntermediateField g (IntermediateField.inclusion h x)
    _ = (restrict E g x : L) := (AlgEquiv.restrictNormalHom_apply E.toIntermediateField g x).symm

theorem includeCoefficients_equivariant (h : E ≤ F) (g : LayerGroup F)
    (m : LayerCoefficients M E) :
    includeCoefficients M h (transition h g • m) = g • includeCoefficients M h m := by
  have hsurj : Function.Surjective (restrict F) := AlgEquiv.restrictNormalHom_surjective L
  obtain ⟨g, rfl⟩ := hsurj g
  change includeCoefficients M h (transition h (restrict F g) • m) =
    restrict F g • includeCoefficients M h m
  apply Subtype.ext
  rw [restrict_transition, includeCoefficients_apply, layerAction_restrict, layerAction_restrict,
    includeCoefficients_apply]

variable (E F)

/-- Ordinary cohomology of the discrete finite Galois group, with all types
lifted to the common universe used by Mathlib's group cohomology. -/
abbrev LayerH (q : ℕ) :=
  groupCohomology (integralRepresentation.{v,w,max v w} (LayerGroup E) (LayerCoefficients M E)) q

/-- The transition is ordinary inflation through the two restriction and inclusion maps. -/
def stageTransition (q : ℕ) (h : E ≤ F) : LayerH M E q →ₗ[ℤ] LayerH M F q :=
  (groupCohomology.map (liftGroupHom.{v,max v w,v} (transition h).toMonoidHom)
    (liftCoefficientMap.{v,w,v,v,w} (transition h).toMonoidHom (includeCoefficients M h)
      (includeCoefficients_equivariant M h)) q).hom.toAddMonoidHom.toIntLinearMap

variable [TopologicalSpace M] [DiscreteTopology M]

/-- The ordinary class represented by a finite-layer cocycle. -/
def stageClass (q : ℕ) (c : continuousCocycles (LayerGroup E) (LayerCoefficients M E) q) :
    LayerH M E q :=
  groupCohomology.π _ q (ordinaryCyclesMk.{v,w,0} _ _ q c)

variable [ContinuousSMul Gal(L/k) M]

/-- Inflate the finite-layer cocycle by restriction in each group variable
and inclusion of the fixed coefficients. -/
def inflateCocycle (q : ℕ) :
    continuousCocycles (LayerGroup E) (LayerCoefficients M E) q →ₗ[ℤ]
      continuousCocycles Gal(L/k) M q :=
  continuousCocycleMap (restrict E).toMonoidHom (restrict E).continuous
    (LayerCoefficients M E).subtype.toAddMonoidHom (layerAction_restrict M E) q

noncomputable local instance : DecidableEq (FiniteGaloisIntermediateField k L) := Classical.decEq _

/-- The colimit of ordinary finite-stage cohomology under inflation. -/
abbrev LayerLimit (q : ℕ) :=
  Module.DirectLimit (fun E : FiniteGaloisIntermediateField k L => LayerH M E q)
    (fun E F h => stageTransition M E F q h)

/-- The canonical map of a finite stage into the colimit. -/
def limitOf (q : ℕ) : LayerH M E q →ₗ[ℤ] LayerLimit (k := k) (L := L) M q :=
  Module.DirectLimit.of ℤ (FiniteGaloisIntermediateField k L)
    (fun F => ↑(LayerH M F q)) (fun F D h => stageTransition M F D q h) E

private abbrev declarationType {α : Sort*} (_ : α) : Sort _ := α

def LayerCoefficients_type := declarationType (@LayerCoefficients.{u,v,w})
def layerAction_type := declarationType (@layerAction.{u,v,w})
def includeCoefficients_type := declarationType (@includeCoefficients.{u,v,w})
def LayerH_type := declarationType (@LayerH.{u,v,w})
def stageTransition_type := declarationType (@stageTransition.{u,v,w})
def stageClass_type := declarationType (@stageClass.{u,v,w})
def inflateCocycle_type := declarationType (@inflateCocycle.{u,v,w})
def LayerLimit_type := declarationType (@LayerLimit.{u,v,w})
def limitOf_type := declarationType (@limitOf.{u,v,w})

def DirectedTransitions : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (M : Type w) [AddCommGroup M] [DistribMulAction Gal(L/k) M] (q : ℕ),
    DirectedSystem (fun E : FiniteGaloisIntermediateField k L => LayerH M E q)
      (fun ⦃E F⦄ h => stageTransition M E F q h)

def StageClassesSurjective : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (M : Type w) [AddCommGroup M] [DistribMulAction Gal(L/k) M]
    (E : FiniteGaloisIntermediateField k L)
    [TopologicalSpace M] [DiscreteTopology M] (q : ℕ),
    Function.Surjective (stageClass M E q)

def InflationFormula : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (M : Type w) [AddCommGroup M] [DistribMulAction Gal(L/k) M]
    (E : FiniteGaloisIntermediateField k L)
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul Gal(L/k) M] (q : ℕ)
    (c : continuousCocycles (LayerGroup E) (LayerCoefficients M E) q) (g : Fin q → Gal(L/k)),
    (inflateCocycle M E q c).val.val g = (c.val.val (fun j => restrict E (g j)) : M)

/-- GH01 in the abelian case, including the canonical comparison on classes. -/
def FiniteLayerComparison : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (M : Type w) [AddCommGroup M] [DistribMulAction Gal(L/k) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul Gal(L/k) M] (q : ℕ),
    ∃ e : LayerLimit (k := k) (L := L) M q ≃ₗ[ℤ] ContinuousH Gal(L/k) M q,
      ∀ (E : FiniteGaloisIntermediateField k L)
        (c : continuousCocycles (LayerGroup E) (LayerCoefficients M E) q),
        e (limitOf M E q (stageClass M E q c)) =
          continuousClass Gal(L/k) M q (inflateCocycle M E q c)

end

end Specs.GaloisFormalization.GH.FiniteLayerCohomology
