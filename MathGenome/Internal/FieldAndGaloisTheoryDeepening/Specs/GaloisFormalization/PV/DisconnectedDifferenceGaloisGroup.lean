import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.DisconnectedDifferenceRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor

namespace GaloisFormalization.PV.Specs.DisconnectedDifference

open scoped Matrix MatrixGroupCoordinates.Specs

universe u

/-- The matrix group, action and fixed ring of the difference extension given by
the quotient by `X² - 1`. The product coordinates are evaluation at the two roots. -/
def disconnectedGaloisGroup : Prop :=
  ∀ {C : Type u} [Field C] [CharZero C] [IsAlgClosed C] (q : Cˣ), orderOf q = 0 →
    let k := RatFunc C
    let R := quotientRing C
    let δ := rationalDilationOperator q
    ∃ (E : operator .difference R) (e : R ≃ₐ[k] k × k) (Y : GL (Fin 1) R),
      commutes E (productOperator q) e ∧
      (∀ p : Polynomial k,
        e (AdjoinRoot.mk (Polynomial.X ^ 2 - 1) p) = (p.eval 1, p.eval (-1))) ∧
      Y.val 0 0 = quotientRoot C ∧
      isFundamental (negativeSystem C) E Y ∧
      let G := matrixGaloisGroup δ E Y
      (∀ g : GL (Fin 1) (constantSubfield δ), g ∈ G ↔ g = 1 ∨ g = -1) ∧
      (∀ g : G,
        let act := (matrixAutomorphism δ E Y g).val
        (g.val = 1 → ∀ x : R, act x = x) ∧
        (g.val = -1 → (∀ x : R, e (act x) = (e x).swap) ∧
          act (quotientRoot C) = -quotientRoot C)) ∧
      (∀ x : R, (∀ g : G, (matrixAutomorphism δ E Y g).val x = x) ↔
        x ∈ Set.range (algebraMap k R)) ∧
      (∀ z : totalQuotientRing R, (∀ g : G, matrixFractionAutomorphism δ E Y g z = z) ↔
        z ∈ Set.range ((algebraMap R (totalQuotientRing R)).comp (algebraMap k R))) ∧
      ¬ ConnectedSpace G

end GaloisFormalization.PV.Specs.DisconnectedDifference
