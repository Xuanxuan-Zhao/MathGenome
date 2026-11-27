import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor

namespace GaloisFormalization.PV.Specs

open scoped Matrix
open Matrix (GeneralLinearGroup)
open MatrixGroupCoordinates.Specs (IsRegularRepresentation)

/-- A finite-dimensional regular representation of the matrix Galois group
is realized by an invertible matrix over the Picard–Vessiot ring. The
matrix is fundamental for a system over the base, with an invertible
coefficient matrix in the difference case. -/
def descendedRepresentationMatrix.{u, v} : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (T : operator kind (totalQuotientRing R)) (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    ∀ {m : ℕ} (ρ : matrixGaloisGroup δ E Y →* GL (Fin m) (constantSubfield δ)),
      IsRegularRepresentation ρ →
      ∃ (W : GL (Fin m) R) (Aρ : linearSystem kind K m),
        isFundamental Aρ E W ∧
        ∀ g : matrixGaloisGroup δ E Y,
          GeneralLinearGroup.map (matrixAutomorphism δ E Y g).val.toRingHom W =
            W * GeneralLinearGroup.map
              ((algebraMap K R).comp (constantSubfield δ).subtype) (ρ g)

end GaloisFormalization.PV.Specs
