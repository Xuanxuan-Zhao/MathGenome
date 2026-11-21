import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Independent specifications for ET-06 (paper.tex, lines 1657–1663),
with the principal-neighborhood convention also used in ET-04.
Rings may be zero. Monicity is part of standard form; it is not needed
for the equivalence between invertibility and the polynomial identity.
-/
namespace Specs.AdvCommAlg.Etale.StandardAndPointwise

universe u v
open Polynomial

/-- The quotient by `(f)`, localized at the image of `g`. -/
abbrev LocalizedQuotient {A : Type u} [CommRing A] (f g : A[X]) :=
  Localization.Away (AdjoinRoot.mk f g)

/-- The image of the derivative in the localized quotient. -/
noncomputable def derivativeImage {A : Type u} [CommRing A] (f g : A[X]) : LocalizedQuotient f g :=
  algebraMap (AdjoinRoot f) (LocalizedQuotient f g) (AdjoinRoot.mk f f.derivative)

def standardEtaleValue : FormalLifting.propertyType.{u,v} :=
  fun A B _ _ _ => ∃ (f : A[X]), f.Monic ∧ ∃ (g : A[X]),
    IsUnit (derivativeImage f g) ∧ Nonempty (B ≃ₐ[A] LocalizedQuotient f g)

def atPrimeType := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B], PrimeSpectrum B → Prop

/-- An étale principal neighborhood; no finiteness assumption on `B`. -/
def isEtaleAtValue : atPrimeType.{u,v} := fun A B _ _ _ q =>
  ∃ b : B, b ∉ q.asIdeal ∧ etaleValue A (Localization.Away b)

def locusType := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B], Set (PrimeSpectrum B)

def etaleLocusValue : locusType.{u,v} := fun A B _ _ _ =>
  {q | isEtaleAtValue A B q}

/-- Denominator clearing in the quotient, including zero localizations. -/
def derivativeUnitIff : Prop := ∀ (A : Type u) [CommRing A] (f g : A[X]),
  IsUnit (derivativeImage f g) ↔
    ∃ (p₁ p₂ : A[X]) (n : ℕ), f.derivative * p₁ + f * p₂ = g ^ n

/-- Match the localized-quotient definition to the canonical predicate. -/
def standardEtaleIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  standardEtaleValue A B ↔ Algebra.IsStandardEtale A B

/-- Match to the actual presentation structure, not just its name. -/
def standardEtalePresentationIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  standardEtaleValue A B ↔ Nonempty (StandardEtalePresentation A B)

/-- The neighborhood locus is the union of all étale principal opens. -/
def locusEqUnion : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  etaleLocusValue A B = ⋃ (b : B) (_ : etaleValue A (Localization.Away b)),
    (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B))

end Specs.AdvCommAlg.Etale.StandardAndPointwise
