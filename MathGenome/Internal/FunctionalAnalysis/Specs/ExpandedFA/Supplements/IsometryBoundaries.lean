import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
Independent statements for the example at paper.tex:6416–6422.
The product `ℝ × ℝ` has Mathlib's sup norm, not the Euclidean norm.
Affineness and linearity mean agreement everywhere with the corresponding
bundled map, as in the upstream Mazur--Ulam statements.
-/

namespace ExpandedFA.Supplements.IsometryBoundariesSpec

open scoped ComplexConjugate

/-- The particular embedding in the source. -/
noncomputable def sineGraph (t : ℝ) : ℝ × ℝ := (t, Real.sin t)

/-- Make the norm on the target plane explicit. -/
def SupNormConclusion : Prop :=
  ∀ p : ℝ × ℝ, ‖p‖ = max |p.1| |p.2|

def SineGraphIsometryConclusion : Prop := Isometry sineGraph

def SineGraphNotAffineConclusion : Prop :=
  ¬ ∃ A : ℝ →ᵃ[ℝ] (ℝ × ℝ), ∀ t : ℝ, A t = sineGraph t

/-- The first example fails exactly the surjectivity hypothesis. -/
def SineGraphNotSurjectiveConclusion : Prop := ¬ Function.Surjective sineGraph

def ConjugationRealConclusion : Prop :=
  Isometry (conj : ℂ → ℂ) ∧ Function.Surjective (conj : ℂ → ℂ) ∧
    ∃ L : ℂ →ₗ[ℝ] ℂ, ∀ z : ℂ, L z = conj z

def ConjugationNotComplexLinearConclusion : Prop :=
  ¬ ∃ L : ℂ →ₗ[ℂ] ℂ, ∀ z : ℂ, L z = conj z

end ExpandedFA.Supplements.IsometryBoundariesSpec
