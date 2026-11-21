import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.ContourCalculus
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
Algebra stage of Riesz–Dunford calculus, paper.tex:10084–10122.
These are statements about the actual finite contour integral defined upstream,
not about an unspecified homomorphism or an assumed calculus certificate.
The complex unital Banach algebra convention includes nonzeroness and ‖1‖=1.
The operator commutation statement also includes the zero Banach space.
-/

noncomputable section
namespace ExpandedFA.BanachAlgebra.HolomorphicHomomorphism.Spec

open Set
open Specs.ExpandedFA.BanachAlgebra.Conventions
open ContourCalculus.Spec

universe u

def ScalarLinearity : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (f g : ℂ → ℂ) (α β : ℂ),
      IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U →
      DifferentiableOn ℂ f U → DifferentiableOn ℂ g U →
      HolomorphicValueValue A a U (fun z => α * f z + β * g z) =
        α • HolomorphicValueValue A a U f + β • HolomorphicValueValue A a U g

def Unitality : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ), IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U →
      HolomorphicValueValue A a U (fun _ => 1) = 1

def Coordinate : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ), IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U →
      HolomorphicValueValue A a U id = a

def Multiplicativity : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (f g : ℂ → ℂ),
      IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U →
      DifferentiableOn ℂ f U → DifferentiableOn ℂ g U →
      HolomorphicValueValue A a U (fun z => f z * g z) =
        HolomorphicValueValue A a U f * HolomorphicValueValue A a U g

def PolynomialAgreement : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (p : Polynomial ℂ),
      IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U →
      HolomorphicValueValue A a U (fun z => p.eval z) = Polynomial.aeval a p

/-- The resolvent convention is (lam1-a)⁻¹, so the scalar function is (lam-z)⁻¹.
The pole is outside the stated holomorphy neighborhood; lam itself is any
resolvent point. Neighborhood independence handles arbitrary smaller domains. -/
def ResolventAgreement : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (U : Set ℂ) (lam : ℂ), IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U →
      lam ∉ U → lam ∈ AlgebraResolventSetValue ℂ A a →
      HolomorphicValueValue A a U (fun z => (lam - z)⁻¹) = AlgebraResolventValue ℂ A a lam

def Commutation : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a b : A) (U : Set ℂ) (f : ℂ → ℂ),
      IsOpen U → AlgebraSpectrumValue ℂ A a ⊆ U → DifferentiableOn ℂ f U →
      Commute b a → Commute b (HolomorphicValueValue A a U f)

def OperatorCommutation : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T S : X →L[ℂ] X) (U : Set ℂ) (f : ℂ → ℂ),
    IsOpen U → AlgebraSpectrumValue ℂ (X →L[ℂ] X) T ⊆ U → DifferentiableOn ℂ f U →
    S * T = T * S →
    S * HolomorphicValueValue (X →L[ℂ] X) T U f =
      HolomorphicValueValue (X →L[ℂ] X) T U f * S

end ExpandedFA.BanachAlgebra.HolomorphicHomomorphism.Spec
