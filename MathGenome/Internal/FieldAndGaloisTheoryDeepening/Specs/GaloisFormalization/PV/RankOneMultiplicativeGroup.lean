import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorGaloisCorrespondence
import Mathlib.RingTheory.RootsOfUnity.Basic

namespace GaloisFormalization.PV.Specs

open scoped Matrix

/-- The rank-one Picard–Vessiot group in the unit group of the constant field.
For a one-by-one matrix, its determinant is its unique entry, so the image
under the determinant gives the scalar multipliers and `y` is the fundamental unit.
The coefficient in the difference case comes from an invertible matrix. -/
def rankOneMultiplicativeGroup.{u, v} : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R]
    (δ : operatorField kind K) (A : linearSystem kind K 1) (E : operator kind R)
    (T : operator kind (totalQuotientRing R)) (Y : GL (Fin 1) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let Q := totalQuotientRing R
    letI : Algebra K Q := Algebra.compHom Q (algebraMap K R)
    let C := constantSubfield δ
    let G := matrixGaloisGroup δ E Y
    let H := G.map Matrix.GeneralLinearGroup.det
    let y := Units.map (algebraMap R Q).toMonoidHom (Matrix.GeneralLinearGroup.det Y)
    let a := coefficientMatrix A 0 0
    let HasPowerSolution := fun m : ℕ => ∃ b : Kˣ,
      apply δ (b : K) =
        match kind with
        | .differential => (m : K) * a * (b : K)
        | .difference => a ^ m * (b : K)
    (H = ⊤ ∨ ∃ m : ℕ, 0 < m ∧ H = rootsOfUnity m C) ∧
    (∀ m : ℕ, 0 < m →
      let inBase := ∃ b : Kˣ, algebraMap K Q (b : K) = ((y ^ m : Qˣ) : Q)
      let fixed := ((y ^ m : Qˣ) : Q) ∈ matrixFixedSubalgebra δ E Y (Set.univ : Set G)
      (H ≤ rootsOfUnity m C ↔ fixed) ∧ (fixed ↔ inBase) ∧ (inBase ↔ HasPowerSolution m)) ∧
    (Finite G ↔ ∃ m : ℕ, 0 < m ∧ HasPowerSolution m) ∧
    (Finite G → IsLeast {m : ℕ | 0 < m ∧ HasPowerSolution m} (Nat.card G))

end GaloisFormalization.PV.Specs
