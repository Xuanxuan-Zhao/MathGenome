import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.StandardAndPointwiseDefinitions
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! ET-14, the locus assertion (paper.tex:1916–1917, 1926–1935).
Étaleness at a prime means the existence of an étale principal neighborhood,
as in ET-06. The base extension is flat; faithful flatness is not assumed.
All rings are commutative and unital, and zero rings are allowed. -/
namespace Specs.AdvCommAlg.Etale.FlatBaseChangeLocus

universe u v w
open TensorProduct
open StandardAndPointwise
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Étaleness at each prime upstairs is equivalent to étaleness at its contraction. -/
def pointwise : Prop := ∀ (A : Type u) (B : Type v) (A' : Type w)
  [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  [Algebra.FinitePresentation A B] [Module.Flat A A']
  (q' : PrimeSpectrum (A' ⊗[A] B)),
  isEtaleAtValue A' (A' ⊗[A] B) q' ↔
    isEtaleAtValue A B (PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) q')

/-- The neighborhood étale locus is the inverse image under the canonical map of spectra. -/
def locus : Prop := ∀ (A : Type u) (B : Type v) (A' : Type w)
  [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  [Algebra.FinitePresentation A B] [Module.Flat A A'],
  etaleLocusValue A' (A' ⊗[A] B) =
    PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) ⁻¹' etaleLocusValue A B

end Specs.AdvCommAlg.Etale.FlatBaseChangeLocus
