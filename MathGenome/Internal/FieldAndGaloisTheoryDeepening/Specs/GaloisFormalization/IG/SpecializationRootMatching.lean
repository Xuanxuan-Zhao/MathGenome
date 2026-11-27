import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationCoefficients
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
# Root matching under good specialization

The Laurent series field carries the `k(t)`-algebra structure given by
substitution at the specified point. Power-series roots are taken for the
coefficientwise lift, and reduced roots are taken for ordinary specialization.
-/

open scoped Polynomial

namespace Specs.GaloisFormalization.IG.SpecializationRootMatching

open SpecializationData SpecializationCoefficients

universe uk uℓ uL

/-- The images in the Laurent series field of the power-series lifts of the fibre roots. -/
def liftedRootImages {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f) : Set (LaurentSeries ℓ) :=
  {x | ∃ r ∈ (specialize a f hf).rootSet ℓ, ∃ F : PowerSeries ℓ,
    PowerSeries.constantCoeff F = r ∧ (polynomialLift ℓ a f hf).eval F = 0 ∧
      powerToLaurent ℓ F = x}

set_option linter.checkUnivs false in
def LiftedRootImagesType :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]), PolynomialRegularAt a f → Set (LaurentSeries ℓ)

/-- Each root of the separable fibre determines a unique power-series root. -/
def LiftSpecializedRoot : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f),
    (specialize a f hf).Separable →
    ∀ r ∈ (specialize a f hf).rootSet ℓ,
      ∃! F : PowerSeries ℓ,
        PowerSeries.constantCoeff F = r ∧ (polynomialLift ℓ a f hf).eval F = 0

/-- The lifts account for every Laurent root, and the generic polynomial is separable. -/
def LaurentSpecializationRoots : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f)
    [Polynomial.IsSplittingField k ℓ (specialize a f hf)],
    f.Monic → (specialize a f hf).Separable →
    letI := substitutionAlgebra ℓ a
    f.Separable ∧ (f.map (algebraMap (RatFunc k) (LaurentSeries ℓ))).Splits ∧
      f.rootSet (LaurentSeries ℓ) = liftedRootImages ℓ a f hf

/-- Every embedding over the specified substitution has the same root images and field image. -/
def PointEmbeddingRoots : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f)
    [Polynomial.IsSplittingField k ℓ (specialize a f hf)]
    (L : Type uL) [Field L] [Algebra (RatFunc k) L] [Polynomial.IsSplittingField (RatFunc k) L f],
    f.Monic → (specialize a f hf).Separable →
    letI := substitutionAlgebra ℓ a
    ∀ i : PointEmbedding (ℓ := ℓ) a L,
      MatchesRoots i f hf ∧
        i '' f.rootSet L = liftedRootImages ℓ a f hf ∧
        i.fieldRange = IntermediateField.adjoin (RatFunc k) (liftedRootImages ℓ a f hf)

/-- Existence of a generic splitting-field embedding that reduces roots bijectively. -/
def ExistsRootMatchingEmbedding : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f)
    [Polynomial.IsSplittingField k ℓ (specialize a f hf)]
    (L : Type uL) [Field L] [Algebra (RatFunc k) L] [Polynomial.IsSplittingField (RatFunc k) L f],
    f.Monic → (specialize a f hf).Separable →
    ∃ i : PointEmbedding (ℓ := ℓ) a L, MatchesRoots i f hf

end Specs.GaloisFormalization.IG.SpecializationRootMatching
