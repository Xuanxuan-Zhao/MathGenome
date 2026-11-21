import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Conventions
import Mathlib.Topology.Algebra.StarSubalgebra

/-!
Independent statements for C*-permanence in `fa2:p2:commutative-cstar`,
paper.tex:12201–12226. A `StarSubalgebra ℂ A` contains the ambient identity
and uses the inherited norm, operations and involution. Closedness expresses
that it is a C*-subalgebra, rather than merely an algebraic *-subalgebra.
Neither algebra is assumed commutative, and no nonzero hypothesis is needed.
-/

namespace ExpandedFA.CStar.SpectralPermanence.Spec

universe u

/-- Ambient invertibility is equivalent to invertibility in the C*-subalgebra. -/
def InvertibilityPermanence : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (B : StarSubalgebra ℂ A),
    IsClosed (B : Set A) → ∀ a : B, IsUnit (a : A) ↔ IsUnit a

/-- The two spectra, computed using the common identity, coincide for every a. -/
def SpectrumEquality : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (B : StarSubalgebra ℂ A),
    IsClosed (B : Set A) → ∀ a : B,
      spectrum ℂ a = spectrum ℂ (a : A)

end ExpandedFA.CStar.SpectralPermanence.Spec
