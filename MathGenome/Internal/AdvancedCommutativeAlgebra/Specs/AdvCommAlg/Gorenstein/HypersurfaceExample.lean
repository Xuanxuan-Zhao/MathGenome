import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CanonicalQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.RegularReduction
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! The hypersurface assertion of GC-14 (paper.tex:4860–4866).
`IsRegularLocalRing` includes Noetherianity and nonzero locality.
`FirstExt` is actual Ext with the action induced by its quotient-ring first
argument, and `omega` is exactly the construction specified in GC-10. -/
noncomputable section
universe u

namespace AdvCommAlg.Gorenstein.HypersurfaceExampleSpecs
open CanonicalQuotient ConcentratedChangeOfRings

/-- Quotienting by the given nonzerodivisor drops dimension by one. -/
def dimensionDropType : Prop :=
  ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (f : S) (hf : f ∈ IsLocalRing.maximalIdeal S), IsSMulRegular S f →
    letI := RegularReduction.quotientLocalRing f hf
    ringKrullDim (S ⧸ Ideal.span {f}) + 1 = ringKrullDim S

/-- Every hypersurface in a regular local ring is Gorenstein. -/
def gorensteinType : Prop :=
  ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (f : S) (hf : f ∈ IsLocalRing.maximalIdeal S), IsSMulRegular S f →
    letI := RegularReduction.quotientLocalRing f hf
    Specs.LocalGorensteinValue (S ⧸ Ideal.span {f})

/-- The two-term resolution computes Ext in degree one, with the natural
quotient action, as the quotient ring itself. -/
def extOneType : Prop :=
  ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (f : S), f ∈ IsLocalRing.maximalIdeal S → IsSMulRegular S f →
    Nonempty (coefficient (Ideal.Quotient.mk (Ideal.span {f}))
      (ModuleCat.of S S) 1 ≃ₗ[S ⧸ Ideal.span {f}] (S ⧸ Ideal.span {f}))

/-- The GC-10 construction has degree one and is canonical, and its
identification with the quotient is linear for the natural quotient action.
The finite dimensions are exhibited, rather than assumed. -/
def canonicalType : Prop :=
  ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (f : S) (hf : f ∈ IsLocalRing.maximalIdeal S), IsSMulRegular S f →
    letI := RegularReduction.quotientLocalRing f hf
    ∃ s d : ℕ, ringKrullDim S = (s : WithBot ℕ∞) ∧
      ringKrullDim (S ⧸ Ideal.span {f}) = (d : WithBot ℕ∞) ∧
      s = d + 1 ∧ s - d = 1 ∧
      ∃ hfin : Module.Finite (S ⧸ Ideal.span {f})
          (omega S (S ⧸ Ideal.span {f}) s d),
        letI := hfin
        Specs.IsCanonicalModuleValue (S ⧸ Ideal.span {f})
            (omega S (S ⧸ Ideal.span {f}) s d) ∧
          Nonempty (omega S (S ⧸ Ideal.span {f}) s d ≃ₗ[S ⧸ Ideal.span {f}]
            coefficient (Ideal.Quotient.mk (Ideal.span {f})) (ModuleCat.of S S) 1) ∧
          Nonempty (omega S (S ⧸ Ideal.span {f}) s d ≃ₗ[S ⧸ Ideal.span {f}]
            (S ⧸ Ideal.span {f}))

end AdvCommAlg.Gorenstein.HypersurfaceExampleSpecs
