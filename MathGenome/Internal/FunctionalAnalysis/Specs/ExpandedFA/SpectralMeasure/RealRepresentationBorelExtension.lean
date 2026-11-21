import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.ContinuousMap.Star

/-! Real coefficient measures and the real bounded Borel extension in
`fa2:p2:representation-pvm`. All vectors belong to the original real Hilbert
space; no complexification, PVM, control measure or countability is assumed. -/

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace ExpandedFA.SpectralMeasure.RealRepresentationBorelExtension.Spec

universe u v
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec

/-- Pointwise boundedness, including on an empty space. -/
def IsBoundedBorel {S : Type u} [MeasurableSpace S] (g : S → ℝ) : Prop :=
  Measurable g ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ s, |g s| ≤ C

variable {S : Type u} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Continuous tests use the ordinary scalar integral, with integrability
against total variation explicit. -/
def RepresentsCoefficient (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (x y : H) (ν : VectorMeasure S ℝ) : Prop :=
  FiniteScalarRadon ν ∧
    ∀ f : C(S, ℝ), Integrable f ν.variation ∧
      ⟪x, π f y⟫_ℝ = scalarIntegral ν f

/-- All coefficient measures are conclusions, with uniqueness among every
finite regular signed representing measure, not just a chosen family. -/
def CoefficientSystem (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (μ : H → H → VectorMeasure S ℝ) : Prop :=
  (∀ x y, RepresentsCoefficient π x y (μ x y) ∧
    (μ x y).variation.real univ ≤ ‖x‖ * ‖y‖ ∧
    ∀ ν, RepresentsCoefficient π x y ν → ν = μ x y) ∧
  (∀ x z y, μ (x + z) y = μ x y + μ z y) ∧
  (∀ (a : ℝ) x y, μ (a • x) y = a • μ x y) ∧
  (∀ x y z, μ x (y + z) = μ x y + μ x z) ∧
  (∀ (a : ℝ) x y, μ x (a • y) = a • μ x y) ∧
  (∀ x y, μ x y = μ y x) ∧
  (∀ x B, MeasurableSet B → 0 ≤ μ x x B)

/-- These identities characterize the actual operator at each bounded Borel
function. They assert existence and uniqueness without an a.e. quotient. -/
def OperatorRepresents (μ : H → H → VectorMeasure S ℝ) (g : S → ℝ)
    (A : H →L[ℝ] H) : Prop :=
  ∀ x y, Integrable g (μ x y).variation ∧
    ⟪x, A y⟫_ℝ = scalarIntegral (μ x y) g

/-- Algebraic laws hold for two arbitrary bounded Borel factors. Involution
on real functions is pointwise the identity and on operators is the Hilbert
adjoint. Uniqueness concerns precisely the coefficient integral identities. -/
def BorelExtension (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (μ : H → H → VectorMeasure S ℝ)
    (Φ : (S → ℝ) → (H →L[ℝ] H)) : Prop :=
  (∀ g, IsBoundedBorel g → OperatorRepresents μ g (Φ g) ∧
    ∀ A, OperatorRepresents μ g A → A = Φ g) ∧
  (∀ f : C(S, ℝ), Φ f = π f) ∧
  Φ (fun _ => 1) = 1 ∧
  (∀ g h, IsBoundedBorel g → IsBoundedBorel h →
    Φ (fun s => g s + h s) = Φ g + Φ h) ∧
  (∀ (a : ℝ) g, IsBoundedBorel g → Φ (fun s => a * g s) = a • Φ g) ∧
  (∀ g h, IsBoundedBorel g → IsBoundedBorel h →
    Φ (fun s => g s * h s) = (Φ g) * (Φ h)) ∧
  (∀ g, IsBoundedBorel g → Φ (fun s => star (g s)) = star (Φ g)) ∧
  (∀ g, IsBoundedBorel g → ∀ C : ℝ, 0 ≤ C → (∀ s, |g s| ≤ C) → ‖Φ g‖ ≤ C) ∧
  (∀ Ψ : (S → ℝ) → (H →L[ℝ] H),
    (∀ g, IsBoundedBorel g → OperatorRepresents μ g (Ψ g)) →
    ∀ g, IsBoundedBorel g → Ψ g = Φ g)

def AutomaticContractivity : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (f : C(S, ℝ)), ‖π f‖ ≤ ‖f‖

def CoefficientExistence : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [MeasurableSpace S] [BorelSpace S]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)),
    ∃ μ : H → H → VectorMeasure S ℝ, CoefficientSystem π μ

def RealRepresentationExtension : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [MeasurableSpace S] [BorelSpace S]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)),
    (∀ f, ‖π f‖ ≤ ‖f‖) ∧
    ∃ (μ : H → H → VectorMeasure S ℝ) (Φ : (S → ℝ) → (H →L[ℝ] H)),
      CoefficientSystem π μ ∧ BorelExtension π μ Φ

end ExpandedFA.SpectralMeasure.RealRepresentationBorelExtension.Spec
