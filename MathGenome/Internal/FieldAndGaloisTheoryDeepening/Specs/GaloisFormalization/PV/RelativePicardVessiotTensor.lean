import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.IntermediateTotalRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor

namespace GaloisFormalization.PV.Specs

open scoped Matrix TensorProduct MatrixGroupCoordinates.Specs
open Matrix (GeneralLinearGroup)
open Algebra.TensorProduct (includeLeftRingHom includeRight lift)
open MatrixGroupCoordinates.Specs (IsAlgebraicSubgroup evalAt zeroLocus)

noncomputable section

/-- The ratio of the fundamental matrices in the two factors of the relative tensor. -/
def relativeTensorRatio (F : Type*) {Q B : Type*}
    [CommRing F] [CommRing Q] [CommRing B] [Algebra F Q] [Algebra F B]
    {n : ℕ} (YQ : GL (Fin n) Q) (YB : GL (Fin n) B) : GL (Fin n) (Q ⊗[F] B) :=
  (GeneralLinearGroup.map includeLeftRingHom YQ)⁻¹ *
    GeneralLinearGroup.map (includeRight : B →ₐ[F] Q ⊗[F] B).toRingHom YB

/-- The elements of the original matrix Galois group whose action on the total
ring fixes the given intermediate algebra pointwise. -/
def relativeStabilizer.{u, v} {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (E : operator kind R) (Y : GL (Fin n) R) :
    Subalgebra K (totalQuotientRing R) → Set (matrixGaloisGroup δ E Y) :=
  fun F => {g | ∀ x : F, matrixFractionAutomorphism δ E Y g (x : totalQuotientRing R) = x}

/-- Evaluation on the second factor, with the identity on the first. -/
def evaluateConstantTensor {C Q D : Type*}
    [CommRing C] [CommRing Q] [CommRing D] [Algebra C Q] [Algebra C D]
    (f : D →ₐ[C] C) : Q ⊗[C] D →ₐ[Q] Q :=
  lift (AlgHom.id Q Q) ((Algebra.ofId C Q).comp f) (fun _ _ => Commute.all _ _)

section Presentation

variable {kind : OperatorKind} {C F Q B : Type*} {n : ℕ}
  [Field C] [CommRing F] [CommRing Q] [CommRing B]
  [Algebra F Q] [Algebra F B] [Algebra B Q] [Algebra C Q]

/-- Evaluation of the constant algebra corresponds to the pointwise stabilizer, and the
relative tensor evaluates by multiplying the first factor by the action on the second. -/
def relativeTensorEvaluations (T : operator kind Q) (EB : operator kind B)
    (YQ : GL (Fin n) Q) (YB : GL (Fin n) B)
    (G : Subgroup (GL (Fin n) C)) (S : Set G) (act : G → Q ≃+* Q)
    {D : Type*} [CommRing D] [Algebra C D]
    (e : Q ⊗[C] D ≃ₐ[Q] Q ⊗[F] B) (ZD : GL (Fin n) D) : Prop :=
  ∃ points : (D →ₐ[C] C) ≃ S,
    (∀ f, ((points f : G) : GL (Fin n) C) =
      GeneralLinearGroup.map f.toRingHom ZD) ∧
    ∀ f, let g : G := points f
      let evaluate := (evaluateConstantTensor (Q := Q) f).comp e.symm.toAlgHom
      ∃ σ : algHom F EB EB,
        Function.Bijective σ.val ∧ commutes T T (act g) ∧
        (∀ q : Q, ∀ b : B, evaluate (q ⊗ₜ[F] b) = q * algebraMap B Q (σ.val b)) ∧
        (∀ b : B, act g (algebraMap B Q b) = algebraMap B Q (σ.val b)) ∧
        GeneralLinearGroup.map ((algebraMap B Q).comp σ.val.toRingHom) YB =
          YQ * GeneralLinearGroup.map (algebraMap C Q) (g : GL (Fin n) C)

/-- The constant algebra of the relative ratio and the canonical multiplication
isomorphism, with the subgroup defined by the ratio's relations. -/
def relativeTensorPresentation
    (T : operator kind Q) (EB : operator kind B) (EP : operator kind (Q ⊗[F] B))
    (YQ : GL (Fin n) Q) (YB : GL (Fin n) B)
    (G : Subgroup (GL (Fin n) C)) (S : Set G) (act : G → Q ≃+* Q) : Prop :=
  let P := Q ⊗[F] B
  letI : Algebra C P := Algebra.compHom P (algebraMap C Q)
  let Z := relativeTensorRatio F YQ YB
  let D := matrixGeneratedSubalgebra C Z
  let U := Q ⊗[C] D
  letI : CommRing U := Algebra.TensorProduct.instCommRing
  letI : Algebra Q U := Algebra.TensorProduct.leftAlgebra
  (∀ j k, isConstant EP (Z.val j k)) ∧ isConstant EP (determinantInverse Z) ∧
  (∀ d : D, isConstant EP (d : P)) ∧
  IsReduced P ∧ IsReduced D ∧ Algebra.FiniteType C D ∧
  ∃ (EU : operator kind U) (e : algEquiv Q EU EP) (ZD : GL (Fin n) D),
    tensorLaws (R := C) T (trivial kind D) EU ∧
    (∀ q : Q, ∀ d : D, e.val (q ⊗ₜ[C] d) = algebraMap Q P q * (d : P)) ∧
    GeneralLinearGroup.map D.val.toRingHom ZD = Z ∧
    relativeTensorEvaluations T EB YQ YB G S act e.val ZD ∧
    ∃ H : Subgroup (GL (Fin n) C),
      (H : Set (GL (Fin n) C)) = Subtype.val '' S ∧
      (H : Set (GL (Fin n) C)) = zeroLocus (RingHom.ker (evalAt (C := C) Z) : Set _) ∧
      IsAlgebraicSubgroup H

end Presentation

/-- The relative tensor and its constant algebra for an intermediate total ring
in the original Picard–Vessiot extension. -/
def relativePicardVessiotTensor.{u, v} : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (T : operator kind (totalQuotientRing R)) (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let Q := totalQuotientRing R
    ∀ (F : Subalgebra K Q), isIntermediateTotalRing T F →
    let C := constantSubfield δ
    letI : Algebra C Q := Algebra.compHom Q (constantSubfield δ).subtype
    let YQ := GeneralLinearGroup.map (algebraMap R Q) Y
    let B := relativePicardVessiotSubalgebra F YQ
    let P := Q ⊗[F] B
    letI : CommRing P := Algebra.TensorProduct.instCommRing
    letI : Algebra Q P := Algebra.TensorProduct.leftAlgebra
    ∃ (EF : operator kind F) (EB : operator kind B) (EP : operator kind P)
      (i : R →+* B),
      isExtension EF T ∧ isExtension EF EB ∧ isExtension EB T ∧
      commutes E EB i ∧ (∀ r, (i r : Q) = algebraMap R Q r) ∧
      IsFractionRing B Q ∧
      tensorLaws (R := F) T EB EP ∧
      Function.Injective (algebraMap Q P) ∧ isSimple T ∧
      relativeTensorPresentation T EB EP YQ (GeneralLinearGroup.map i Y)
        (matrixGaloisGroup δ E Y) (relativeStabilizer δ E Y F)
        (matrixFractionAutomorphism δ E Y)

end

end GaloisFormalization.PV.Specs
