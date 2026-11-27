import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.IntermediateTotalRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor

namespace GaloisFormalization.PV.Specs

open scoped Matrix

universe u v

/-- Every base-field operator automorphism of an intermediate total ring lifts to
the Picard–Vessiot Galois group. The compatibility with the actual inclusion of
the intermediate ring specifies its induced operator. -/
def intermediateAutomorphismLift : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (T : operator kind (totalQuotientRing R)) (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let Q := totalQuotientRing R
    letI : Algebra K Q := Algebra.compHom Q (algebraMap K R)
    ∀ (F : Subalgebra K Q), isIntermediateTotalRing T F →
    ∀ (EF : operator kind (F : Type v)), isAlgebra EF T →
    ∀ τ : operatorAutomorphisms K EF,
      ∃ g : matrixGaloisGroup δ E Y,
        ∀ x : F, matrixFractionAutomorphism δ E Y g (x : Q) = (τ.val x : Q)

end GaloisFormalization.PV.Specs
