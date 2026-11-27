import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor

namespace GaloisFormalization.PV.Specs

open scoped Matrix MatrixGroupCoordinates.Specs

universe u v

/-- Lemma 2.6. Every element of the matrix Galois group outside a Zariski
closed subgroup moves an element of the total quotient ring fixed by that
subgroup. -/
def rationalInvariantSeparation : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotRing δ A E → isFundamental A E Y →
    let G := matrixGaloisGroup δ E Y
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
      ∀ g : G, g ∉ H →
        ∃ q : totalQuotientRing R,
          (∀ h : H, matrixFractionAutomorphism δ E Y h.val q = q) ∧
          matrixFractionAutomorphism δ E Y g q ≠ q

end GaloisFormalization.PV.Specs
