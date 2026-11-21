import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LocusDefinitions
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! SM-13: equality of the neighborhood smooth loci under flat base change. -/
namespace Specs.AdvCommAlg.Smooth.FlatBaseChangeLocus

universe u v w
open TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Comparison at every existing prime upstairs; the base extension is only flat. -/
def pointwise : Prop := ∀ (A : Type u) (B : Type v) (A' : Type w)
  [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  [Algebra.FinitePresentation A B] [Module.Flat A A']
  (q' : PrimeSpectrum (A' ⊗[A] B)),
  isSmoothAtValue A' (A' ⊗[A] B) q' ↔
    isSmoothAtValue A B (PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) q')

/-- Equality as sets of primes, using the canonical tensor-product projection. -/
def locus : Prop := ∀ (A : Type u) (B : Type v) (A' : Type w)
  [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  [Algebra.FinitePresentation A B] [Module.Flat A A'],
  smoothLocusValue A' (A' ⊗[A] B) =
    PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) ⁻¹' smoothLocusValue A B

end Specs.AdvCommAlg.Smooth.FlatBaseChangeLocus
