import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalCharacterDefinitions
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir

/-! The truncated expansion in LA-H02, source lines 3578–3581 and 3623–3650. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.TruncatedVermaExpansion

open FormalCharacters HighestWeightCasimir SerreRelations VermaModules VermaWeightsUniversal
open HighestWeightData (weightSpace_value)
open SolvableRadical (IsSemisimple_value)
open _root_.LieAlgebrasAndRepresentations.ModuleCasimir (action)
open scoped Classical

universe u v i

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A sum of at most `N` simple roots, counted with repetitions. -/
def HeightAtMost (β : Module.Dual ℂ H) (N : ℕ) : Prop :=
  ∃ roots : List (simple H φ), (roots.map Subtype.val).sum = β ∧ roots.length ≤ N

/-- The coefficient of the actual induced Verma module's character. -/
def vermaMultiplicity (χ : U (borel_value H φ) →ₐ[ℂ] ℂ) :
    Module.Dual ℂ H → ℤ :=
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  multiplicity H (induced_value H φ χ)

/-- Coefficientwise agreement with a finite integral sum of Verma characters
through the prescribed height. The ambient weight group is the full Cartan dual. -/
def truncated_verma_expansion_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (B : Form (L := L)) (hB : B.Nondegenerate), B.lieInvariant L → PositiveOnRealRoots H B →
    ∀ {I : Type i} [Fintype I] (b : Module.Basis I ℂ L)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    (lam : Module.Dual ℂ H) (c : ℂ) (N : ℕ),
    DirectSum.IsInternal (weightSpace_value V H) →
    (∀ μ, FiniteDimensional ℂ (weightSpace_value V H μ)) →
    (∀ μ, weightSpace_value V H μ ≠ ⊥ → lam - μ ∈ cone H φ) →
    (∀ v : V, action ℂ L V (casimir_value B hB b) v = c • v) →
    ∃ χ : Module.Dual ℂ H → (U (borel_value H φ) →ₐ[ℂ] ℂ),
      (∀ μ, IsWeightCharacter H φ μ (χ μ)) ∧
      ∃ coefficients : Module.Dual ℂ H →₀ ℤ,
        (∀ μ, coefficients μ ≠ 0 → lam - μ ∈ cone H φ ∧ eigenvalue_value H φ B μ = c) ∧
        ∀ ν, HeightAtMost H φ (lam - ν) N →
          multiplicity H V ν =
            (Finsupp.linearCombination ℤ (fun μ => vermaMultiplicity H φ (χ μ)) coefficients) ν

end Specs.LieAlgebrasAndRepresentations.TruncatedVermaExpansion
