import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor
import Mathlib.FieldTheory.Galois.Basic

/-! Specialization of the first factor of the Picard–Vessiot torsor. -/

namespace GaloisFormalization.PV.Specs

open scoped TensorProduct
open Matrix (GeneralLinearGroup)
open Algebra.TensorProduct (includeLeftRingHom includeRight)
open MatrixGroupCoordinates.Specs (CoordinateRing coordinateMap evalAt evalCoordinate)

universe u v w

/-- The coordinate identification at an ordinary algebra point, with (G) acting
on the ring factor and by pullback along right translation on coordinates. -/
def isTorsorSpecialization
    {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (E : operator kind R) (Y : GeneralLinearGroup (Fin n) R)
    {L : Type w} [Field L] [Algebra K L] (point : R →ₐ[K] L) : Prop :=
  let C := constantSubfield δ
  letI : Algebra C L := Algebra.compHom L (constantSubfield δ).subtype
  let G := matrixGaloisGroup δ E Y
  let S : Set (GeneralLinearGroup (Fin n) C) := G
  let B := CoordinateRing S
  letI : CommRing B := inferInstanceAs (CommRing (CoordinateRing S))
  letI : Algebra C B := inferInstanceAs (Algebra C (CoordinateRing S))
  let V := L ⊗[C] B
  letI : CommRing V := Algebra.TensorProduct.instCommRing
  letI : Algebra L V := Algebra.TensorProduct.leftAlgebra
  let T := L ⊗[K] R
  letI : CommRing T := Algebra.TensorProduct.instCommRing
  letI : Algebra C T := Algebra.TensorProduct.leftAlgebra
  letI : Algebra L T := Algebra.TensorProduct.leftAlgebra
  let U := GeneralLinearGroup.map point.toRingHom Y
  let Z := (GeneralLinearGroup.map (includeLeftRingHom : L →+* T) U)⁻¹ *
    GeneralLinearGroup.map (includeRight : R →ₐ[K] T).toRingHom Y
  ∃ (e : V ≃ₐ[L] T) (translate : G →* (B ≃ₐ[C] B)),
    (∀ p, e (1 ⊗ₜ[C] coordinateMap S p) = evalAt (C := C) Z p) ∧
    (∀ (g x : G) (b : B), evalCoordinate x (translate g b) = evalCoordinate (x * g) b) ∧
    ∀ (g : G) (a : L) (b : B),
      e (a ⊗ₜ[C] translate g b) =
        Algebra.TensorProduct.map (AlgHom.id L L)
          (matrixAutomorphism δ E Y g).val.toAlgHom (e (a ⊗ₜ[C] b))

/-- The torsor identification and its action formula hold over every field
extension carrying a point of the Picard–Vessiot ring. -/
def torsorSpecialization : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (Y : GeneralLinearGroup (Fin n) R),
    isBaseField δ → isPicardVessiotRing δ A E → isFundamental A E Y →
    ∀ {L : Type w} [Field L] [Algebra K L] (point : R →ₐ[K] L),
      isTorsorSpecialization δ E Y point

/-- A maximal-ideal residue field supplies a finite separable point. Its
embedding into a finite Galois extension gives the same specialization there. -/
def torsorSpecializationAtResidue : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (Y : GeneralLinearGroup (Fin n) R),
    isBaseField δ → isPicardVessiotRing δ A E → isFundamental A E Y →
    ∃ (m : Ideal R) (hm : m.IsMaximal),
      letI : m.IsMaximal := hm
      letI : Field (R ⧸ m) := Ideal.Quotient.field m
      let point := Ideal.Quotient.mkₐ K m
      Module.Finite K (R ⧸ m) ∧ Algebra.IsSeparable K (R ⧸ m) ∧
      isTorsorSpecialization δ E Y point ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
        Module.Finite K L ∧ IsGalois K L ∧
        ∃ embedding : (R ⧸ m) →ₐ[K] L, isTorsorSpecialization δ E Y (embedding.comp point)

end GaloisFormalization.PV.Specs
