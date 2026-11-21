import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RepresentationModules
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.BalancedTensor
import Mathlib.LinearAlgebra.Trace

/-! Basic character constructions for arbitrary groups and fields. The binary
sum is realized by the product vector space, which is also the finite direct sum.
The tensor realization is tied to the common balanced tensor by `BalancedModel`. -/
noncomputable section
universe u v w x
namespace P103.Ch08.CharacterSpecs

variable {k : Type u} {G : Type v} {V : Type w} {W : Type x}
  [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

def characterValue (ρ : Representation k G V) : G → k :=
  fun g => LinearMap.trace k V (ρ g)

def dualValue (ρ : Representation k G V) : Representation k G (Module.Dual k V) :=
  ρ.dual

def sumValue (ρ : Representation k G V) (σ : Representation k G W) :
    Representation k G (V × W) := ρ.prod σ

def tensorValue (ρ : Representation k G V) (σ : Representation k G W) :
    Representation k G (TensorProduct k V W) := ρ.tprod σ

/-- A diagonal action on the shared balanced tensor, with a scalar-compatible
comparison preserving elementary tensors and intertwining the two actions.
Finite dimensionality and the character formula hold for this very action. -/
def BalancedModel [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) : Prop :=
  letI := BalancedTensor.commRightModule k V
  ∃ m : Module k (BalancedTensor.Tensor k V W),
    letI := m
    (∀ (c : k) (a : V) (b : W), c • BalancedTensor.tmul k a b =
      BalancedTensor.tmul k (c • a) b) ∧
    (∀ (c : k) (a : V) (b : W), c • BalancedTensor.tmul k a b =
      BalancedTensor.tmul k a (c • b)) ∧
    FiniteDimensional k (BalancedTensor.Tensor k V W) ∧
    ∃ (τ : Representation k G (BalancedTensor.Tensor k V W))
      (e : BalancedTensor.Tensor k V W ≃ₗ[k] TensorProduct k V W),
      (∀ a b, e (BalancedTensor.tmul k a b) = TensorProduct.tmul k a b) ∧
      (∀ a b, e.symm (TensorProduct.tmul k a b) = BalancedTensor.tmul k a b) ∧
      (∀ g a b, τ g (BalancedTensor.tmul k a b) =
        BalancedTensor.tmul k (ρ g a) (σ g b)) ∧
      (∀ g z, e (τ g z) = tensorValue ρ σ g (e z)) ∧
      (∀ g, characterValue τ g = characterValue ρ g * characterValue σ g)

def characterType :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V), G → k

def contragredientType :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V), Representation k G (Module.Dual k V)

def directSumRepresentationType :=
  ∀ {k : Type u} {G : Type v} {V : Type w} {W : Type x} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W), Representation k G (V × W)

def diagonalRepresentationType :=
  ∀ {k : Type u} {G : Type v} {V : Type w} {W : Type x} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W), Representation k G (TensorProduct k V W)

def character_conjugateType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) (g h : G),
    characterValue ρ (h * g * h⁻¹) = characterValue ρ g

def contragredient_applyType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (g : G) (f : Module.Dual k V) (a : V),
    dualValue ρ g f a = f (ρ g⁻¹ a)

def directSum_applyType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] {W : Type x} [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W) (g : G) (a : V) (b : W),
    sumValue ρ σ g (a,b) = (ρ g a, σ g b)

def diagonal_applyType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] {W : Type x} [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W) (g : G) (a : V) (b : W),
    tensorValue ρ σ g (TensorProduct.tmul k a b) = TensorProduct.tmul k (ρ g a) (σ g b)

def character_contragredientType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) (g : G),
    characterValue (dualValue ρ) g = characterValue ρ g⁻¹

def character_directSumType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G),
    characterValue (sumValue ρ σ) g = characterValue ρ g + characterValue σ g

def character_diagonalType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G),
    characterValue (tensorValue ρ σ) g = characterValue ρ g * characterValue σ g

def balancedTensor_constructionType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W), BalancedModel ρ σ

end P103.Ch08.CharacterSpecs
