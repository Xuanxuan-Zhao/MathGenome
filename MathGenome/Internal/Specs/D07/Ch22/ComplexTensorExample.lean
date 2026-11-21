import MathGenome.Internal.Specs.D07.Ch22.ComplexTensorExampleComplexTensorSplitter
import MathGenome.Internal.Specs.D07.Ch22.TensorConstruction

/-!
Independent specification of K07.22.complex_tensor_example,
paper.tex:6907–6944. All three rings are commutative and unital; no
nontriviality, injectivity, freeness or finiteness is imposed. The tensor
is the canonical tensor module identified with the balanced quotient by
K07.22.tensor_construction. Its existing additive structure and R-action
are retained by the tensor algebra construction.
-/

universe u v w
namespace Specs.D07.Ch22.ComplexTensorExample
open scoped TensorProduct

/-- The elementary formula extends uniquely to a bilinear multiplication on
all tensors. That extension is the canonical tensor ring multiplication. -/
def MultiplicationConstruction : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B],
    ∃! μ : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) →ₗ[R] (A ⊗[R] B),
      (∀ (a a' : A) (b b' : B),
        μ (a ⊗ₜ[R] b) (a' ⊗ₜ[R] b') = (a * a') ⊗ₜ[R] (b * b')) ∧
      (∀ x y, μ x y = x * y)

/-- All multiplicative ring laws hold on the original tensor module, with
the stated identity. The R-algebra action agrees with the module action. -/
def AlgebraLaws : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B],
    (1 : A ⊗[R] B) = (1 : A) ⊗ₜ[R] (1 : B) ∧
    (∀ x y z : A ⊗[R] B, (x * y) * z = x * (y * z)) ∧
    (∀ x y : A ⊗[R] B, x * y = y * x) ∧
    (∀ x : A ⊗[R] B, 1 * x = x ∧ x * 1 = x) ∧
    (∀ x y z : A ⊗[R] B, x * (y + z) = x * y + x * z) ∧
    (∀ x y z : A ⊗[R] B, (x + y) * z = x * z + y * z) ∧
    (∀ (r : R) (x : A ⊗[R] B), r • x = algebraMap R (A ⊗[R] B) r * x) ∧
    (∀ (r : R) (a : A) (b : B), r • (a ⊗ₜ[R] b) = (r • a) ⊗ₜ[R] b)

/-- The maps from the factors preserve one, addition, multiplication and
R-scalars, have the specified values, and have commuting images. -/
def CanonicalMaps : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B],
    ∃ (ιA : A →ₐ[R] A ⊗[R] B) (ιB : B →ₐ[R] A ⊗[R] B),
      (∀ a, ιA a = a ⊗ₜ[R] (1 : B)) ∧
      (∀ b, ιB b = (1 : A) ⊗ₜ[R] b) ∧
      (∀ a b, Commute (ιA a) (ιB b)) ∧
      (∀ a b, ιA a * ιB b = a ⊗ₜ[R] b)

/-- Regarding the tensor as an A-algebra uses its first factor. This is the
scalar-extension action, including when the base ring is the zero ring. -/
def FirstFactorAction : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B],
    (∀ a : A, algebraMap A (A ⊗[R] B) a = a ⊗ₜ[R] (1 : B)) ∧
    (∀ (a' a : A) (b : B), a' • (a ⊗ₜ[R] b) = (a' * a) ⊗ₜ[R] b)

/-- The formula defining the complex example is real-balanced; balanced
here includes biadditivity, with exactly the real actions on both factors. -/
def ComplexBalanced : Prop :=
  TensorConstruction.IsBalanced ℝ ℂ ℂ
    (fun z w : ℂ => (z * w, z * starRingEnd ℂ w))

/-- The full specialized conclusion, reusing the upstream independent
specification of the same complex tensor, normal form and idempotents. -/
def ComplexExample : Prop :=
  ComplexTensorExampleComplexTensorSplitter.Splitting ∧
  ComplexTensorExampleComplexTensorSplitter.UniqueNormalForm ∧
  ComplexTensorExampleComplexTensorSplitter.Idempotents ∧
  ComplexTensorExampleComplexTensorSplitter.NotDomain

end Specs.D07.Ch22.ComplexTensorExample
