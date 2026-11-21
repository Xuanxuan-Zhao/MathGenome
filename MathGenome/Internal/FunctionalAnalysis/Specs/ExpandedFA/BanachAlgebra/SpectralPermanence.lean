import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
Independent statements for the permanence part of paper.tex:10158–10187.
A `Subalgebra ℂ A` has the same identity as A, with the inherited norm.
Closedness is explicit; no inverse-closedness or commutativity is assumed.
The generated-algebra conclusion is allocated separately.
-/

namespace Specs.ExpandedFA.BanachAlgebra.SpectralPermanence

open Conventions
open scoped Topology

universe u

def PolynomialHullType := Set ℂ → Set ℂ

/-- The one-variable polynomial hull, expressed by all polynomial modulus
upper bounds on K. On a nonempty compact K these are precisely the inequalities
`‖p.eval z‖ ≤ max (w ∈ K), ‖p.eval w‖`. This also defines the empty hull correctly. -/
def PolynomialHullValue : PolynomialHullType :=
  fun K => {z | ∀ (p : Polynomial ℂ) (M : ℝ),
    (∀ w ∈ K, ‖p.eval w‖ ≤ M) → ‖p.eval z‖ ≤ M}

/-- Explicit identification with the conventional supremum formulation. -/
def PolynomialHullModulus : Prop :=
  ∀ (K : Set ℂ), IsCompact K → K.Nonempty → ∀ z : ℂ,
    z ∈ PolynomialHullValue K ↔
      ∀ p : Polynomial ℂ, ‖p.eval z‖ ≤ sSup ((fun w => ‖p.eval w‖) '' K)

def SpectrumInclusion : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (B : Subalgebra ℂ A), IsClosed (B : Set A) → ∀ a : B,
      AlgebraSpectrumValue ℂ A (a : A) ⊆ AlgebraSpectrumValue ℂ B a

def SpectrumBoundaryInclusion : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (B : Subalgebra ℂ A), IsClosed (B : Set A) → ∀ a : B,
      frontier (AlgebraSpectrumValue ℂ B a) ⊆ frontier (AlgebraSpectrumValue ℂ A (a : A))

def SpectrumPolynomialHulls : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (B : Subalgebra ℂ A), IsClosed (B : Set A) → ∀ a : B,
      PolynomialHullValue (AlgebraSpectrumValue ℂ A (a : A)) =
        PolynomialHullValue (AlgebraSpectrumValue ℂ B a)

/-- Every component of the ambient resolvent is wholly spectral or wholly
resolvent in B. Choosing z in that resolvent parametrizes all its components. -/
def SpectrumComponents : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (B : Subalgebra ℂ A), IsClosed (B : Set A) → ∀ (a : B) (z : ℂ),
      z ∉ AlgebraSpectrumValue ℂ A (a : A) →
      (connectedComponentIn (AlgebraSpectrumValue ℂ A (a : A))ᶜ z ⊆
        AlgebraSpectrumValue ℂ B a) ∨
      Disjoint (connectedComponentIn (AlgebraSpectrumValue ℂ A (a : A))ᶜ z)
        (AlgebraSpectrumValue ℂ B a)

end Specs.ExpandedFA.BanachAlgebra.SpectralPermanence
