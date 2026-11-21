import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Characters
import Mathlib.Topology.ContinuousMap.Compact

/-!
The transform stage of `fa2:p2:gelfand` (paper.tex:10196–10229).
The chapter convention (9907–9914) is complex, complete, nonzero and ‖1‖ = 1.
The carrier is the shared algebraic character space, with exactly the weak-star
(evaluation) topology of the upstream character theorem. No star structure,
semisimplicity or surjectivity of the transform is required.
-/
noncomputable section

namespace Specs.ExpandedFA.BanachAlgebra.GelfandTransform

open Specs.ExpandedFA.BanachAlgebra.Characters
open Specs.ExpandedFA.BanachAlgebra.Conventions

universe u

local instance characterTop (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A] :
    TopologicalSpace (Character A) := CharacterTopologyValue A

local instance characterCompact (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A] : CompactSpace (Character A) :=
  (_root_.ExpandedFA.BanachAlgebra.Characters.compact_hausdorff A).1

/-- A scalar-algebra homomorphism to continuous functions on the actual Δ. -/
def TransformType :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A], A →ₐ[ℂ] C(Character A, ℂ)

/-- The canonical evaluation construction, independently of the candidate. -/
def TransformValue : TransformType.{u} := fun A _ _ _ _ _ =>
  { toFun := fun a =>
      { toFun := fun χ => χ.val a
        continuous_toFun := (continuous_apply a).comp continuous_induced_dom }
    map_zero' := by ext χ; exact χ.val.map_zero
    map_one' := by ext χ; exact _root_.ExpandedFA.BanachAlgebra.Characters.character_map_one χ
    map_add' := by intro a b; ext χ; exact χ.val.map_add a b
    map_mul' := by intro a b; ext χ; exact χ.property.2 a b
    commutes' := by
      intro z
      ext χ
      exact (_root_.ExpandedFA.BanachAlgebra.Characters.characterAlgHom χ).commutes z }

def Evaluation : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A] (a : A) (χ : Character A),
    TransformValue A a χ = χ.val a

def NormContractive : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A] (a : A),
    ‖TransformValue A a‖ ≤ ‖a‖

def Lipschitz : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A],
    LipschitzWith 1 (TransformValue A)

/-- The radius is the manuscript's real supremum of the spectral moduli. -/
def NormSpectralRadius : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A] (a : A),
    ‖TransformValue A a‖ = AlgebraSpectralRadiusValue ℂ A a

/-- Equality of ideals, with the intersection over all maximal ideals. -/
def KernelIntersection : Prop :=
  ∀ (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A],
    RingHom.ker (TransformValue A) = ⨅ I : {I : Ideal A // I.IsMaximal}, I.val

end Specs.ExpandedFA.BanachAlgebra.GelfandTransform
