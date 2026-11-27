import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.NonabelianH1
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Order.DirectedInverseSystem

/-! The pointed direct limit of ordinary degree-one cohomology at the finite Galois layers. -/

namespace Specs.GaloisFormalization.GH.FiniteLayerPointedCohomology

open Specs.GaloisFormalization.GH.KrullLayers
open GaloisFormalization.GH.NonabelianH1.Spec hiding restrict

universe u v w

noncomputable section

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
variable (B : Type w) [Group B] [MulDistribMulAction Gal(L/k) B]

/-- The fixed coefficient subgroup at a finite Galois layer. -/
abbrev Coefficients (E : FiniteGaloisIntermediateField k L) := Fixed (layerKernel E) B

private def layerQuotientEquiv (E : FiniteGaloisIntermediateField k L) :
    (Gal(L/k) ⧸ layerKernel E) ≃* LayerGroup E :=
  QuotientGroup.liftEquiv (layerKernel E)
    (φ := (restrict E).toMonoidHom) (AlgEquiv.restrictNormalHom_surjective L)
    E.toIntermediateField.restrictNormalHom_ker.symm

/-- The action of the finite Galois group via the quotient by its fixing subgroup. -/
scoped instance layerAction (E : FiniteGaloisIntermediateField k L) :
    MulDistribMulAction (LayerGroup E) (Coefficients B E) :=
  MulDistribMulAction.compHom (Coefficients B E) (layerQuotientEquiv E).symm.toMonoidHom

theorem restrict_smul (E : FiniteGaloisIntermediateField k L) (g : Gal(L/k))
    (b : Coefficients B E) : ((restrict E g • b : Coefficients B E) : B) = g • (b : B) := by
  change (((layerQuotientEquiv E).symm (restrict E g) • b : Coefficients B E) : B) =
    g • (b : B)
  have h : layerQuotientEquiv E (QuotientGroup.mk g) = restrict E g := rfl
  rw [← h, MulEquiv.symm_apply_apply]
  rfl

/-- Ordinary pointed degree-one cohomology at a finite Galois layer. -/
abbrev Stage (E : FiniteGaloisIntermediateField k L) :=
  OrdinaryH1 (LayerGroup E) (Coefficients B E)

def stageBasepoint (E : FiniteGaloisIntermediateField k L) : Stage B E :=
  ordinaryBasepoint (LayerGroup E) (Coefficients B E)

variable {B} {E F D : FiniteGaloisIntermediateField k L}

def coefficientsInclusion (h : E ≤ F) : Coefficients B E →* Coefficients B F :=
  Subgroup.inclusion fun _ hb g =>
    hb ⟨g, IntermediateField.fixingSubgroup_le h g.property⟩

omit [IsGalois k L] in
private theorem restrict_transition (h : E ≤ F) (g : Gal(L/k)) :
    transition h (restrict F g) = restrict E g := by
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq' rfl
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F g).symm

private theorem transition_compatible (h : E ≤ F) :
    Compatible (transition h).toMonoidHom (coefficientsInclusion (B := B) h) := by
  intro σ b
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
  apply Subtype.ext
  change ((transition h (restrict F g) • b : Coefficients B E) : B) =
    ((restrict F g • coefficientsInclusion h b : Coefficients B F) : B)
  rw [restrict_transition, restrict_smul, restrict_smul]
  rfl

def stageCocycleMap (h : E ≤ F) (c : OrdinaryCocycle (LayerGroup E) (Coefficients B E)) :
    OrdinaryCocycle (LayerGroup F) (Coefficients B F) :=
  ⟨fun σ => coefficientsInclusion h (c (transition h σ)), by
    intro σ τ
    change coefficientsInclusion h (c ((transition h).toMonoidHom (σ * τ))) =
      coefficientsInclusion h (c (transition h σ)) *
        σ • coefficientsInclusion h (c (transition h τ))
    rw [map_mul, c.property, map_mul, transition_compatible]
    rfl⟩

variable (B) in
/-- The transition precomposes with restriction and includes the fixed coefficients. -/
def stageMap (h : E ≤ F) : TypeCat.Fun (Stage B E) (Stage B F) :=
  ⟨Quotient.map (stageCocycleMap h) (by
    rintro c d ⟨b, hb⟩
    refine ⟨coefficientsInclusion h b, fun σ => ?_⟩
    change coefficientsInclusion h (d (transition h σ)) =
      (coefficientsInclusion h b)⁻¹ * coefficientsInclusion h (c (transition h σ)) *
        σ • coefficientsInclusion h b
    rw [hb, twistFunction, map_mul, map_mul, map_inv, ← transition_compatible]
    rfl)⟩

theorem stageMap_classOf (h : E ≤ F)
    (c : OrdinaryCocycle (LayerGroup E) (Coefficients B E)) :
    stageMap B h (ordinaryClassOf c) = ordinaryClassOf (stageCocycleMap h c) := rfl

theorem stageMap_basepoint (h : E ≤ F) :
    stageMap B h (stageBasepoint B E) = stageBasepoint B F := by
  change stageMap B h (ordinaryClassOf (ordinaryTrivial _ _)) =
    ordinaryClassOf (ordinaryTrivial _ _)
  rw [stageMap_classOf]
  apply congrArg ordinaryClassOf
  exact Subtype.ext (funext fun _ => map_one (coefficientsInclusion h))

variable (B)

instance stageDirectedSystem :
    DirectedSystem (Stage (k := k) (L := L) B) (fun _ _ h x => stageMap B h x) where
  map_self := by
    intro E x
    refine Quotient.inductionOn x fun c => ?_
    change stageMap B le_rfl (ordinaryClassOf c) = ordinaryClassOf c
    rw [stageMap_classOf]
    apply congrArg ordinaryClassOf
    apply Subtype.ext
    funext σ
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    change coefficientsInclusion (le_refl E) (c (transition (le_refl E) (restrict E g))) =
      c (restrict E g)
    rw [restrict_transition]
    rfl
  map_map := by
    intro D F E hEF hFD x
    refine Quotient.inductionOn x fun c => ?_
    change stageMap B hFD (stageMap B hEF (ordinaryClassOf c)) =
      stageMap B (hEF.trans hFD) (ordinaryClassOf c)
    simp only [stageMap_classOf]
    apply congrArg ordinaryClassOf
    apply Subtype.ext
    funext σ
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    change coefficientsInclusion hFD (coefficientsInclusion hEF
      (c (transition hEF (transition hFD (restrict D g))))) =
        coefficientsInclusion (hEF.trans hFD) (c (transition (hEF.trans hFD) (restrict D g)))
    rw [restrict_transition, restrict_transition, restrict_transition]
    rfl

/-- The directed colimit of the underlying types. -/
abbrev Colimit :=
  DirectLimit (Stage (k := k) (L := L) B) (fun _ _ h => stageMap B h)

def ofStage (E : FiniteGaloisIntermediateField k L) (x : Stage B E) :
    Colimit (k := k) (L := L) B :=
  ⟦⟨E, x⟩⟧

def colimitBasepoint : Colimit (k := k) (L := L) B :=
  ofStage B ⊥ (stageBasepoint B ⊥)

theorem ofStage_basepoint (E : FiniteGaloisIntermediateField k L) :
    ofStage B E (stageBasepoint B E) = colimitBasepoint (k := k) (L := L) B := by
  unfold colimitBasepoint ofStage
  rw [DirectLimit.eq_of_le (f := fun _ _ h => stageMap B h) ⟨⊥, stageBasepoint B ⊥⟩ E bot_le,
    stageMap_basepoint]

section Inflation

variable [TopologicalSpace B] [DiscreteTopology B]

/-- Inflation on representatives uses restriction on the argument and the subgroup inclusion. -/
def inflateCocycle (E : FiniteGaloisIntermediateField k L)
    (c : OrdinaryCocycle (LayerGroup E) (Coefficients B E)) : Cocycle Gal(L/k) B :=
  mapCocycle (restrict E).toMonoidHom (restrict E).continuous (Coefficients B E).subtype
    (restrict_smul B E) (discreteCocycleEquiv.symm c)

/-- Inflation from a stage to continuous cohomology on the full Krull group. -/
def stageInflation (E : FiniteGaloisIntermediateField k L) : Stage B E → H1 Gal(L/k) B :=
  fun x => map (restrict E).toMonoidHom (restrict E).continuous (Coefficients B E).subtype
    (restrict_smul B E) (discreteEquiv.symm x)

theorem stageInflation_classOf (E : FiniteGaloisIntermediateField k L)
    (c : OrdinaryCocycle (LayerGroup E) (Coefficients B E)) :
    stageInflation B E (ordinaryClassOf c) = classOf (inflateCocycle B E c) := rfl

end Inflation

/-- The canonical comparison is a pointed bijection and restricts to inflation at each stage. -/
def comparison_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (B : Type w) [Group B] [MulDistribMulAction Gal(L/k) B]
    [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul Gal(L/k) B],
    ∃ e : Colimit (k := k) (L := L) B ≃ H1 Gal(L/k) B,
      (∀ (E : FiniteGaloisIntermediateField k L) (x : Stage B E),
        e (ofStage B E x) = stageInflation B E x) ∧
      e (colimitBasepoint (k := k) (L := L) B) = basepoint Gal(L/k) B

end

end Specs.GaloisFormalization.GH.FiniteLayerPointedCohomology
