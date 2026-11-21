import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! The regular-element assertion of GC-06 (paper.tex:4569–4570).
The Gorenstein predicate means finite self-injective dimension. -/

universe u

namespace AdvCommAlg.Gorenstein.RegularReduction

/-- A quotient by an element of the maximal ideal is a nonzero local ring. -/
@[instance_reducible] def quotientLocalRing {R : Type u} [CommRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.span {x}) := by
  have hle : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (by simpa using hx)
  letI : Nontrivial (R ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

namespace Specs

def localGorenstein_quotient_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R), IsSMulRegular R x →
    letI := quotientLocalRing x hx
    Gorenstein.Specs.LocalGorensteinValue R ↔
      Gorenstein.Specs.LocalGorensteinValue (R ⧸ Ideal.span {x})

end Specs
end AdvCommAlg.Gorenstein.RegularReduction
