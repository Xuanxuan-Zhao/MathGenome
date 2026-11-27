import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.Algebra.Group.Quotient

/-! The intrinsic Krull group, its finite restrictions, and its discrete field coefficients. -/

namespace Specs.GaloisFormalization.GH.KrullLayers

universe u v

open scoped Topology
open IntermediateField

noncomputable section

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]

abbrev GaloisGroup := Gal(L/k)

abbrev AbsoluteGaloisGroup [IsSepClosure k L] := Gal(L/k)

abbrev profiniteGroup [IsGalois k L] : ProfiniteGrp :=
  InfiniteGalois.profiniteGalGrp k L

variable {k L}

abbrev LayerGroup (E : FiniteGaloisIntermediateField k L) := Gal(E/k)

abbrev layerKernel (E : FiniteGaloisIntermediateField k L) : Subgroup Gal(L/k) :=
  E.toIntermediateField.fixingSubgroup

abbrev OpenNormalSubgroup (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] :=
  {H : Subgroup Gal(L/k) // IsOpen (H : Set Gal(L/k)) ∧ H.Normal}

def restrict (E : FiniteGaloisIntermediateField k L) : Gal(L/k) →ₜ* Gal(E/k) where
  toMonoidHom := AlgEquiv.restrictNormalHom E.toIntermediateField
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField

def transition {E F : FiniteGaloisIntermediateField k L} (h : E ≤ F) :
    Gal(F/k) →ₜ* Gal(E/k) :=
  letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq' rfl
  { toMonoidHom := AlgEquiv.restrictNormalHom E
    continuous_toFun := continuous_of_discreteTopology }

section DefinitionTypes

-- These wrappers package a full dependent function type in one sort.
set_option linter.checkUnivs false

def GaloisGroup_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L], Type v

def AbsoluteGaloisGroup_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] [IsSepClosure k L], Type v

def profiniteGroup_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] [IsGalois k L], ProfiniteGrp.{v}

def LayerGroup_type :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L],
    FiniteGaloisIntermediateField k L → Type v

def layerKernel_type :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L],
    FiniteGaloisIntermediateField k L → Subgroup Gal(L/k)

def OpenNormalSubgroup_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L], Type v

def restrict_type :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (E : FiniteGaloisIntermediateField k L), Gal(L/k) →ₜ* Gal(E/k)

def transition_type :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {E F : FiniteGaloisIntermediateField k L}, E ≤ F → (Gal(F/k) →ₜ* Gal(E/k))

end DefinitionTypes

def layers_directed_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L],
    Nonempty (FiniteGaloisIntermediateField k L) ∧
      Directed (· ≤ ·) (id : FiniteGaloisIntermediateField k L →
        FiniteGaloisIntermediateField k L)

def layer_finite_discrete_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (E : FiniteGaloisIntermediateField k L),
    Finite Gal(E/k) ∧ DiscreteTopology Gal(E/k)

def restrict_apply_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (E : FiniteGaloisIntermediateField k L) (σ : Gal(L/k)) (x : E),
    (restrict E σ x : L) = σ (x : L)

def restrict_units_apply_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (E : FiniteGaloisIntermediateField k L) (σ : Gal(L/k)) (u : Eˣ),
    Units.map (algebraMap E L).toMonoidHom (restrict E σ • u) =
      σ • Units.map (algebraMap E L).toMonoidHom u

def transition_apply_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {E F : FiniteGaloisIntermediateField k L} (h : E ≤ F) (σ : Gal(F/k)) (x : E),
    (transition h σ x : L) = (σ (IntermediateField.inclusion h x) : L)

def restrict_surjective_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (E : FiniteGaloisIntermediateField k L), Function.Surjective (restrict E)

def transition_surjective_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {E F : FiniteGaloisIntermediateField k L} (h : E ≤ F),
    Function.Surjective (transition h)

def restrict_comp_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {E F : FiniteGaloisIntermediateField k L} (h : E ≤ F),
    restrict E = (transition h).comp (restrict F)

def transition_refl_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (E : FiniteGaloisIntermediateField k L),
    transition (le_refl E) = ContinuousMonoidHom.id Gal(E/k)

def transition_comp_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {E F D : FiniteGaloisIntermediateField k L} (hEF : E ≤ F) (hFD : F ≤ D),
    transition (hEF.trans hFD) = (transition hEF).comp (transition hFD)

def layerKernel_isOpen_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (E : FiniteGaloisIntermediateField k L), IsOpen (layerKernel E : Set Gal(L/k))

def layerKernel_normal_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (E : FiniteGaloisIntermediateField k L), (layerKernel E).Normal

def restrict_ker_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (E : FiniteGaloisIntermediateField k L), (restrict E).toMonoidHom.ker = layerKernel E

def quotient_restriction_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (E : FiniteGaloisIntermediateField k L),
    ∃! e : (Gal(L/k) ⧸ layerKernel E) ≃ₜ* Gal(E/k),
      ∀ σ : Gal(L/k), e (QuotientGroup.mk σ) = restrict E σ

def layerKernels_basis_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] [IsGalois k L],
    (𝓝 (1 : Gal(L/k))).HasBasis
      (fun _ : FiniteGaloisIntermediateField k L => True)
      (fun E => (layerKernel E : Set Gal(L/k)))

def openNormalCorrespondence_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] [IsGalois k L],
    ∃ e : FiniteGaloisIntermediateField k L ≃o (OpenNormalSubgroup k L)ᵒᵈ,
      (∀ E, (OrderDual.ofDual (e E)).val = layerKernel E) ∧
      (∀ H : OpenNormalSubgroup k L,
        (e.symm (OrderDual.toDual H)).toIntermediateField = fixedField H.val)

def layerKernel_bot_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L],
    layerKernel (⊥ : FiniteGaloisIntermediateField k L) = ⊤

def fixedField_layerKernel_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (E : FiniteGaloisIntermediateField k L),
    fixedField (layerKernel E) = E.toIntermediateField

def layerKernel_le_iff_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    {E F : FiniteGaloisIntermediateField k L},
    layerKernel F ≤ layerKernel E ↔ E ≤ F

def fixedField_top_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] [IsGalois k L],
    fixedField (⊤ : Subgroup Gal(L/k)) = (⊥ : IntermediateField k L)

def mem_range_algebraMap_iff_fixed_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L] (x : L),
    x ∈ Set.range (algebraMap k L) ↔ ∀ σ : Gal(L/k), σ x = x

def exists_layer_mem_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L] (x : L),
    ∃ E : FiniteGaloisIntermediateField k L, x ∈ E.toIntermediateField

def continuous_fieldAction_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    [TopologicalSpace L] [DiscreteTopology L], ContinuousSMul Gal(L/k) L

def continuous_unitsAction_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    [TopologicalSpace Lˣ] [DiscreteTopology Lˣ], ContinuousSMul Gal(L/k) Lˣ

def fixedUnits_layer_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (E : FiniteGaloisIntermediateField k L),
    ∃ e : Eˣ ≃* FixedPoints.subgroup (layerKernel E) Lˣ,
      ∀ u : Eˣ, (e u : Lˣ) = Units.map (algebraMap E L) u

def fixedUnits_base_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] [IsGalois k L],
    ∃ e : kˣ ≃* FixedPoints.subgroup Gal(L/k) Lˣ,
      ∀ u : kˣ, (e u : Lˣ) = Units.map (algebraMap k L) u

end

end Specs.GaloisFormalization.GH.KrullLayers
