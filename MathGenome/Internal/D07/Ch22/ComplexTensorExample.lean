import MathGenome.Internal.Specs.D07.Ch22.ComplexTensorExample
import MathGenome.Internal.D07.Ch22.ComplexTensorExampleComplexTensorSplitter

/-! K07.22.complex_tensor_example. Multiplication is constructed by the
bilinear tensor map (itself obtained by tensor lifts), and is identified
with the canonical tensor algebra multiplication. The complex splitting
uses the proved upstream equivalence for these very same algebra structures. -/

noncomputable section
universe u v w
namespace D07.Ch22.ComplexTensorExample
open Specs.D07.Ch22.ComplexTensorExample
open scoped TensorProduct

/-- Extend the two factor multiplications through the tensor universal
property. No multiplication on representatives is assumed well-defined. -/
def tensorMultiplication (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] :
    (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) :=
  TensorProduct.map₂ (LinearMap.mul R A) (LinearMap.mul R B)

@[simp] theorem tensorMultiplication_tmul (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B]
    (a a' : A) (b b' : B) :
    tensorMultiplication R A B (a ⊗ₜ[R] b) (a' ⊗ₜ[R] b') =
      (a * a') ⊗ₜ[R] (b * b') := rfl

/-- Equality on elementary tensors identifies the lifted multiplication
on every tensor, since the elementary tensors generate each input. -/
theorem tensorMultiplication_eq_mul (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] (x y : A ⊗[R] B) :
    tensorMultiplication R A B x y = x * y := by
  have h : tensorMultiplication R A B = LinearMap.mul R (A ⊗[R] B) := by
    ext a b a' b'
    simp
  exact congrArg (fun μ => μ x y) h

theorem multiplicationConstruction : MultiplicationConstruction.{u, v, w} := by
  intro R _ A _ _ B _ _
  refine ⟨tensorMultiplication R A B,
    ⟨tensorMultiplication_tmul R A B, tensorMultiplication_eq_mul R A B⟩, ?_⟩
  intro ν hν
  ext a b a' b'
  exact (hν.1 a a' b b').trans (tensorMultiplication_tmul R A B a a' b b').symm

theorem algebraLaws : AlgebraLaws.{u, v, w} := by
  intro R _ A _ _ B _ _
  exact ⟨Algebra.TensorProduct.one_def, mul_assoc, mul_comm,
    fun x => ⟨one_mul x, mul_one x⟩, mul_add, add_mul,
    Algebra.smul_def, fun _ _ _ => rfl⟩

theorem canonicalMaps : CanonicalMaps.{u, v, w} := by
  intro R _ A _ _ B _ _
  refine ⟨Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight,
    fun _ => rfl, fun _ => rfl, fun _ _ => Commute.all _ _, ?_⟩
  intro a b
  simp

theorem firstFactorAction : FirstFactorAction.{u, v, w} := by
  intro R _ A _ _ B _ _
  exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩

theorem complexBalanced : ComplexBalanced := by
  let F := ComplexTensorExampleComplexTensorSplitter.splitHom
  have hF (z w : ℂ) : F (z ⊗ₜ[ℝ] w) = (z * w, z * starRingEnd ℂ w) := rfl
  constructor
  · intro z z' w
    rw [← hF, TensorProduct.add_tmul, map_add, hF, hF]
  · intro z w w'
    rw [← hF, TensorProduct.tmul_add, map_add, hF, hF]
  · intro r z w
    rw [← hF, ← hF, TensorProduct.smul_tmul]

theorem complexExample : ComplexExample :=
  ⟨ComplexTensorExampleComplexTensorSplitter.splitting,
    ComplexTensorExampleComplexTensorSplitter.uniqueNormalForm,
    ComplexTensorExampleComplexTensorSplitter.idempotents,
    ComplexTensorExampleComplexTensorSplitter.notDomain⟩

end D07.Ch22.ComplexTensorExample
