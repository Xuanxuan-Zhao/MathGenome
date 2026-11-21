import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.RegularReduction
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.RegularLocalStructure

/-! GC-07, paper.tex:4594–4605: regular local rings and quotients by finite
regular sequences. The chapter convention is nonzero Noetherian local rings.
The canonical sequence predicate includes properness. Lists may be empty.
Localization is allocated separately. -/

universe u

namespace AdvCommAlg.Gorenstein

/-- The quotient by a list in the maximal ideal is again a nonzero local ring. -/
@[instance_reducible] def sequenceQuotientLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] (x : List R)
    (hm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.ofList x) := by
  have hle : Ideal.ofList x ≤ IsLocalRing.maximalIdeal R := Ideal.span_le.mpr hm
  letI : Nontrivial (R ⧸ Ideal.ofList x) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

namespace Specs

def localGorenstein_regularSequence_quotient_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : List R) (hm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R),
    RingTheory.Sequence.IsRegular R x →
    letI := sequenceQuotientLocalRing R x hm
    LocalGorensteinValue R ↔ LocalGorensteinValue (R ⧸ Ideal.ofList x)

def regularLocal_gorensteinType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], LocalGorensteinValue R

def completeIntersection_gorensteinType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (x : List R) (hm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R),
    RingTheory.Sequence.IsRegular R x →
    letI := sequenceQuotientLocalRing R x hm
    LocalGorensteinValue (R ⧸ Ideal.ofList x)

/-- The conclusion also holds for any ring with such a quotient presentation. -/
def gorenstein_of_completeIntersection_presentationType : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (x : List R) (hm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R),
    RingTheory.Sequence.IsRegular R x →
    (R ⧸ Ideal.ofList x ≃+* S) → LocalGorensteinValue S

end Specs
end AdvCommAlg.Gorenstein
