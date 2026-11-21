import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VermaModules
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightData
import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.UniversalEnveloping
import Mathlib.Algebra.DirectSum.Module

/-! LA-G02, Chapter 7. The Lie action on the Verma module is the restriction
of its canonical left enveloping action along `UniversalEnvelopingAlgebra.ι`. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal

open VermaModules HighestWeightData SerreRelations
open SolvableRadical (IsSemisimple_value)
open scoped Classical

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)
variable (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev inducedRepresentation : _root_.Shared.Lie.Representation ℂ L (induced_value H φ χ) :=
  ((Algebra.lsmul ℂ ℂ (induced_value H φ χ) :
    U L →ₐ[ℂ] Module.End ℂ (induced_value H φ χ)) :
    U L →ₗ⁅ℂ⁆ Module.End ℂ (induced_value H φ χ)).comp (UniversalEnvelopingAlgebra.ι ℂ)

abbrev inducedLieRingModule : LieRingModule L (induced_value H φ χ) :=
  _root_.Shared.Lie.representationLieRingModule ℂ L _ (inducedRepresentation H φ χ)

abbrev inducedLieModule :
    @LieModule ℂ L (induced_value H φ χ) _ _ _ _ _ (inducedLieRingModule H φ χ) :=
  _root_.Shared.Lie.representationLieModule ℂ L _ (inducedRepresentation H φ χ)

/-- The full ordinary weight-space decomposition, spectrum, and highest line. -/
def verma_weights_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ → ∀ (lam : Module.Dual ℂ H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ), IsWeightCharacter H φ lam χ →
    letI := inducedLieRingModule H φ χ
    letI := inducedLieModule H φ χ
    let W := weightSpace_value (induced_value H φ χ) H
    DirectSum.IsInternal W ∧
    (∀ μ, FiniteDimensional ℂ (W μ)) ∧
    (∀ μ, W μ ≠ ⊥ ↔ lam - μ ∈ positiveRootCone_value (fun i : simple H φ => i.val)) ∧
    W lam = ℂ ∙ highestVector_value H φ χ

/-- A highest-weight vector in any Lie module determines a unique Lie-module map.
For a nonzero cyclic highest-weight vector this map is surjective. -/
def verma_universal_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ → ∀ (lam : Module.Dual ℂ H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ), IsWeightCharacter H φ lam χ →
    ∀ (e : simple H φ → L), (∀ i, e i ∈ RootDecomposition.rootSpace_value H i.val ∧ e i ≠ 0) →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    (w : V), (∀ h : H, ⁅(h : L), w⁆ = lam h • w) → (∀ i, ⁅e i, w⁆ = 0) →
    letI := inducedLieRingModule H φ χ
    letI := inducedLieModule H φ χ
    (∃! f : induced_value H φ χ →ₗ⁅ℂ,L⁆ V, f (highestVector_value H φ χ) = w) ∧
    (w ≠ 0 → LieSubmodule.lieSpan ℂ L ({w} : Set V) = ⊤ →
      ∃ f : induced_value H φ χ →ₗ⁅ℂ,L⁆ V,
        f (highestVector_value H φ χ) = w ∧ Function.Surjective f)

end Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
