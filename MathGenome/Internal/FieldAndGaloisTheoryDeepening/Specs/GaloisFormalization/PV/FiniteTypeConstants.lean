import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorLocalization
import Mathlib.RingTheory.FiniteType

namespace GaloisFormalization.PV.Specs

universe u v w

/-- The inclusion from the base field identifies its constants with the constants
of a simple finite-type operator algebra. -/
def finiteTypeConstants : Prop :=
  ∀ {kind : OperatorKind} {k : Type u} {S : Type v}
    [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (D : operatorField kind k) (E : operator kind S),
    isBaseField D → isSimple E →
    ∀ h : isAlgebra D E,
      Function.Bijective (mapConstants (D := D) (E := E) ⟨algebraMap k S, h⟩)

/-- The inclusion from the base field also identifies its constants with the
constants in the total ring of fractions, equipped with the extended operator. -/
def finiteTypeFractionConstants : Prop :=
  ∀ {kind : OperatorKind} {k : Type u} {S : Type v} {Q : Type w}
    [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    [CommRing Q] [Algebra S Q] [IsFractionRing S Q]
    (D : operatorField kind k) (E : operator kind S) (F : operator kind Q),
    isBaseField D → isSimple E →
    ∀ (h : isAlgebra D E) (hQ : commutes E F (algebraMap S Q)),
      Function.Bijective
        ((mapConstants (D := E) (E := F) ⟨algebraMap S Q, hQ⟩).comp
          (mapConstants (D := D) (E := E) ⟨algebraMap k S, h⟩))

end GaloisFormalization.PV.Specs
