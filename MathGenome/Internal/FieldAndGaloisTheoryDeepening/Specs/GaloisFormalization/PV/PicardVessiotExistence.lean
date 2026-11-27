import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotRing

namespace GaloisFormalization.PV.Specs

universe u

/-- Every linear system over an operator field of characteristic zero with algebraically
closed constants has a Picard–Vessiot ring. The base constants map bijectively to the
constants of the ring and, by the composite inclusion, to those of its total extension. -/
def picardVessiotExists : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
    (D : operatorField kind K) (A : linearSystem kind K n), isBaseField D →
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra K R),
    ∃ (E : operator kind R) (F : operator kind (totalQuotientRing R)),
    ∃ h : isPicardVessiotTotalExtension D A E F,
      Function.Bijective (mapConstants (D := D) (E := E) ⟨algebraMap K R, h.1.1.1⟩) ∧
      Function.Bijective
        ((mapConstants (D := E) (E := F) ⟨algebraMap R (totalQuotientRing R), h.2.1⟩).comp
          (mapConstants (D := D) (E := E) ⟨algebraMap K R, h.1.1.1⟩))

end GaloisFormalization.PV.Specs
