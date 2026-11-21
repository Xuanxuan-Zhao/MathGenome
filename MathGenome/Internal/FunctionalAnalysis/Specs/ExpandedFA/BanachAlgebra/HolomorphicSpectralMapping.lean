import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.HolomorphicHomomorphism

/-!
The Riesz–Dunford theorem, paper.tex:10090–10135, with the chapter conventions
at 9907–9914. The value is the actual finite-cycle contour integral from the
upstream interface. Holomorphy is required only on an arbitrary open neighborhood
of the spectrum; neither that neighborhood nor the spectrum must be connected.
-/

noncomputable section
namespace ExpandedFA.BanachAlgebra.HolomorphicSpectralMapping.Spec

open Set Filter
open scoped Topology
open Specs.ExpandedFA.BanachAlgebra.Conventions
open ContourCalculus.Spec

universe u

/-- Full holomorphic spectral mapping, including constant functions. -/
def SpectralMapping : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (f : ℂ → ℂ),
      IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U → DifferentiableOn ℂ f U →
      AlgebraSpectrumValue ℂ A (HolomorphicValueValue A a U f) =
        f '' AlgebraSpectrumValue ℂ A a

/-- Uniform convergence on one admissible cycle gives convergence of calculus
values, allowing the individual holomorphy neighborhoods to vary with n. -/
def HolomorphicFixedContourConvergence : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (V : ℕ → Set ℂ) (f : ℂ → ℂ) (F : ℕ → ℂ → ℂ),
      IsOpen U → (∀ n, IsOpen (V n)) →
      AlgebraSpectrumValue ℂ A a ⊆ U → (∀ n, AlgebraSpectrumValue ℂ A a ⊆ V n) →
      DifferentiableOn ℂ f U → (∀ n, DifferentiableOn ℂ (F n) (V n)) →
      ∀ Γ : ContourCalculus.Cycle,
        Γ.Admissible (AlgebraSpectrumValue ℂ A a) U →
        (∀ n, Γ.Admissible (AlgebraSpectrumValue ℂ A a) (V n)) →
        TendstoUniformlyOn F f atTop Γ.trace →
        Tendsto (fun n => HolomorphicValueValue A a (V n) (F n)) atTop
          (𝓝 (HolomorphicValueValue A a U f))

/-- All conclusions concern the same contour integral and its selected value.
The independent upstream types spell out existence, both forms of independence,
the algebra operations, polynomial/resolvent agreement, the contour bound and
uniform convergence, and commutation (including operators on the zero space). -/
def RieszDunfordCalculus : Prop :=
  AdmissibleCyclesExist ∧
  SelectedCycleAdmissible.{u} ∧
  HolomorphicFormula.{u} ∧
  CycleIndependence.{u} ∧
  NeighborhoodIndependence.{u} ∧
  HolomorphicHomomorphism.Spec.ScalarLinearity.{u} ∧
  HolomorphicHomomorphism.Spec.Unitality.{u} ∧
  HolomorphicHomomorphism.Spec.Coordinate.{u} ∧
  HolomorphicHomomorphism.Spec.Multiplicativity.{u} ∧
  HolomorphicHomomorphism.Spec.PolynomialAgreement.{u} ∧
  HolomorphicHomomorphism.Spec.ResolventAgreement.{u} ∧
  SpectralMapping.{u} ∧
  ContourNormEstimate.{u} ∧
  FixedContourConvergence.{u} ∧
  HolomorphicFixedContourConvergence.{u} ∧
  HolomorphicHomomorphism.Spec.Commutation.{u} ∧
  HolomorphicHomomorphism.Spec.OperatorCommutation.{u}

end ExpandedFA.BanachAlgebra.HolomorphicSpectralMapping.Spec
