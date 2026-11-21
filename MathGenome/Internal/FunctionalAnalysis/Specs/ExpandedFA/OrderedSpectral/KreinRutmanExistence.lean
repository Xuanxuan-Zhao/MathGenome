import Mathlib.Analysis.Convex.Cone.Basic
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions

/-! Independent specifications for the existence and cone uniqueness clauses of
paper.tex:11772–11830, `fa2:p2:krein-rutman`.  A cone here is not assumed
normal or salient.  Mathlib calls the source's pointedness `Salient`;
Mathlib's `Pointed` means only that the cone contains zero. -/
namespace ExpandedFA.OrderedSpectral.KreinRutmanExistence.Spec
universe u

/-- Strong positivity forces the cone to contain no nonzero vector together
with its negative. Compactness and completeness are unnecessary for this clause. -/
def ForcedPointedness : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : ConvexCone ℝ X), (P : Set X) ≠ Set.univ →
    ∀ (T : X →ₗ[ℝ] X),
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) → P.Salient

/-- Existence under exactly the source's compactness and solid-cone hypotheses.
Compactness is in the original normed target, as in the shared definition. -/
def PositiveEigenpair : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) →
    (interior (P : Set X)).Nonempty → (P : Set X) ≠ Set.univ →
    ∀ (T : X →ₗ[ℝ] X),
      Compactness.DefinitionsSpec.IsCompactLinearMapValue T →
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) →
      ∃ (μ : ℝ) (u : X), 0 < μ ∧ u ∈ interior (P : Set X) ∧
        u ≠ 0 ∧ T u = μ • u

/-- All nonzero cone eigenvectors have the same eigenvalue and positive ray.
The competing eigenvalue ν is arbitrary real; its positivity is a conclusion. -/
def ConeEigenvectorUniqueness : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) → (P : Set X) ≠ Set.univ →
    ∀ (T : X →ₗ[ℝ] X),
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) →
      ∀ (μ : ℝ) (u : X), 0 < μ → u ∈ interior (P : Set X) →
        u ≠ 0 → T u = μ • u →
      ∀ (ν : ℝ) (x : X), x ∈ P → x ≠ 0 → T x = ν • x →
        ν = μ ∧ ∃ a : ℝ, 0 < a ∧ x = a • u

/-- The complete assigned conclusion, including forced pointedness. -/
def ExistenceAndUniqueness : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) →
    (interior (P : Set X)).Nonempty → (P : Set X) ≠ Set.univ →
    ∀ (T : X →ₗ[ℝ] X),
      Compactness.DefinitionsSpec.IsCompactLinearMapValue T →
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) →
      P.Salient ∧ ∃ (μ : ℝ) (u : X), 0 < μ ∧
        u ∈ interior (P : Set X) ∧ u ≠ 0 ∧ T u = μ • u ∧
        ∀ (ν : ℝ) (x : X), x ∈ P → x ≠ 0 → T x = ν • x →
          ν = μ ∧ ∃ a : ℝ, 0 < a ∧ x = a • u
end ExpandedFA.OrderedSpectral.KreinRutmanExistence.Spec
