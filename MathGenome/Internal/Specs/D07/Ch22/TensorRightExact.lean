import MathGenome.Internal.Specs.D07.Ch22.TensorQuotients

/-!
Independent statements for K07.22.tensor_right_exact, paper.tex:6855–6882.
Exactness includes surjectivity onto C. The coefficient ring may be the
zero ring, and no finiteness or flatness assumption is imposed on any module.
The counterexample uses the same integer ideal quotient as TensorQuotients.
-/

noncomputable section
universe u v w t s
namespace Specs.D07.Ch22.TensorRightExact
open scoped TensorProduct
attribute [-instance] AddCommGroup.toIntModule

/-- Right exactness, stated directly in terms of the canonical tensor maps. -/
def RightExactness : Prop :=
  ∀ (R : Type u) [CommRing R]
    (A : Type v) [AddCommGroup A] [Module R A]
    (B : Type w) [AddCommGroup B] [Module R B]
    (C : Type t) [AddCommGroup C] [Module R C]
    (N : Type s) [AddCommGroup N] [Module R N]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C),
    Function.Surjective g → LinearMap.range f = LinearMap.ker g →
    Function.Surjective (TensorProduct.map g (LinearMap.id : N →ₗ[R] N)) ∧
    LinearMap.range (TensorProduct.map f (LinearMap.id : N →ₗ[R] N)) =
      LinearMap.ker (TensorProduct.map g (LinearMap.id : N →ₗ[R] N))

/-- The actual linear map x ↦ 2x on the integers. -/
def doubling : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id

abbrev ModTwo := TensorQuotients.cyclic 2

/-- Tensoring the displayed injection with the identity on ℤ/(2). -/
def tensorDoubling : (ℤ ⊗[ℤ] ModTwo) →ₗ[ℤ] (ℤ ⊗[ℤ] ModTwo) :=
  TensorProduct.map doubling LinearMap.id

def DoublingFormula : Prop := ∀ x : ℤ, doubling x = 2 * x

def DoublingInjective : Prop := Function.Injective doubling

/-- The source's identification ℤ ⊗ ℤ/(2) ≃ ℤ/(2), with both formulas. -/
def CounterexampleUnit : Prop :=
  ∃ e : (ℤ ⊗[ℤ] ModTwo) ≃ₗ[ℤ] ModTwo,
    (∀ (a : ℤ) (n : ModTwo), e (a ⊗ₜ[ℤ] n) = a • n) ∧
    (∀ n : ModTwo, e.symm n = (1 : ℤ) ⊗ₜ[ℤ] n)

def TensorDoublingZero : Prop := tensorDoubling = 0

def TensorSourceNontrivial : Prop := Nontrivial (ℤ ⊗[ℤ] ModTwo)

def LeftExactnessFailure : Prop := ¬ Function.Injective tensorDoubling

end Specs.D07.Ch22.TensorRightExact
