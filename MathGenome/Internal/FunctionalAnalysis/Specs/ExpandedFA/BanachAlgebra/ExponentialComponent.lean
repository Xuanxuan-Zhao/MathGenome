import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.HolomorphicSpectralMapping
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Connected.LocallyPathConnected

/-! Banach-algebra part of paper.tex, fa2:p2:exponentials (10252–10273).
The chapter is complex, nonzero and normalized. The topology on units is the
native units topology, identified with the norm subspace topology in the proof.
A logarithm branch is arbitrary; no principal-branch or connected-spectrum
restriction is imposed. The Hilbert-space two-exponential assertion is allocated
separately to HilbertTwoExponentials. -/
noncomputable section
namespace ExpandedFA.BanachAlgebra.ExponentialComponent.Spec

open Specs.ExpandedFA.BanachAlgebra.Conventions
open ContourCalculus.Spec

universe u

def ExponentialIdentityComponent : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ u : Aˣ, u ∈ connectedComponent (1 : Aˣ) ↔
      ∃ l : List A, (l.map NormedSpace.exp).prod = (u : A)

def InvertiblesLocallyPathConnected : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    LocallyPathConnectedSpace Aˣ ∧
      ∀ u : Aˣ, connectedComponent u = pathComponent u

/-- Exponential compatibility concerns the same contour calculus fixed upstream. -/
def HolomorphicExponential : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (f : ℂ → ℂ),
      IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U → DifferentiableOn ℂ f U →
      NormedSpace.exp (HolomorphicValueValue A a U f) =
        HolomorphicValueValue A a U (fun z => Complex.exp (f z))

def HolomorphicLogarithm : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (L : ℂ → ℂ),
      IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U → DifferentiableOn ℂ L U →
      (∀ z ∈ U, Complex.exp (L z) = z) →
      a = NormedSpace.exp (HolomorphicValueValue A a U L)

/-- Any holomorphic nth-root branch gives an nth root under the calculus. -/
def HolomorphicRoot : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (f : ℂ → ℂ) (n : ℕ), 0 < n →
      IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U → DifferentiableOn ℂ f U →
      (∀ z ∈ U, f z ^ n = z) → HolomorphicValueValue A a U f ^ n = a

/-- A logarithm branch supplies a holomorphic root of every positive order. -/
def RootsFromLogarithm : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (L : ℂ → ℂ),
      IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U → DifferentiableOn ℂ L U →
      (∀ z ∈ U, Complex.exp (L z) = z) → ∀ n : ℕ, 0 < n →
      HolomorphicValueValue A a U (fun z => Complex.exp (L z / (n : ℂ))) ^ n = a

end ExpandedFA.BanachAlgebra.ExponentialComponent.Spec
