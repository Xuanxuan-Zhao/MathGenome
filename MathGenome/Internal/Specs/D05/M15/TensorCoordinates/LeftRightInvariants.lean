import MathGenome.Internal.Specs.D05.M15.TensorDualHom
import MathGenome.Internal.Specs.D05.M15.TensorCoordinates.TraceDeterminant
import MathGenome.Internal.Specs.D05.M07.DualMatrix

/-! Independent statements for paper.tex:2759–2761. The dual is algebraic.
All finite-dimensional spaces, including the zero space, are allowed; A and B
may be singular and the field may have any characteristic. -/
namespace Specs.D05.M15.TensorCoordinates.LeftRightInvariants

open scoped TensorProduct

/-- Alias of the upstream canonical left/right multiplication operator. -/
abbrev leftRight {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A B : Module.End K V) : Module.End K (Module.End K V) :=
  Specs.D05.M15.TensorCoordinates.sandwich A B

def leftRight_type :=
  {K V : Type*} → [Field K] → [AddCommGroup V] → [Module K V] →
    Module.End K V → Module.End K V → Module.End K (Module.End K V)

def leftRight_value : leftRight_type := @leftRight

def leftRight_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A B X : Module.End K V) (x : V), leftRight A B X x = A (X (B x))

/-- The rank-one calculation fixes the order of the dual and vector factors. -/
def rank_one_action : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A B : Module.End K V) (φ : Module.Dual K V) (v : V),
    leftRight A B (Specs.D05.M15.TensorDualHom.phi K V V (φ ⊗ₜ[K] v)) =
      Specs.D05.M15.TensorDualHom.phi K V V (B.dualMap φ ⊗ₜ[K] A v)

/-- Equality on all tensors, with the shared canonical tensor–Hom map. -/
def intertwining : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A B : Module.End K V),
    (leftRight A B).comp (Specs.D05.M15.TensorDualHom.phi K V V) =
      (Specs.D05.M15.TensorDualHom.phi K V V).comp (TensorProduct.map B.dualMap A)

/-- In finite dimension the correspondence is actual conjugacy. -/
def conjugacy : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : Module.End K V),
    (dualTensorHomEquiv K V V).conj (TensorProduct.map B.dualMap A) = leftRight A B

/-- Removal of the ordinary dual from the trace formula. -/
def trace_dual : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : Module.End K V),
    LinearMap.trace K (Module.Dual K V) B.dualMap = LinearMap.trace K V B

/-- Removal of the ordinary dual from the determinant formula. -/
def det_dual : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : Module.End K V),
    LinearMap.det B.dualMap = LinearMap.det B

def trace_leftRight : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : Module.End K V),
    LinearMap.trace K (Module.End K V) (leftRight A B) =
      LinearMap.trace K V A * LinearMap.trace K V B

def det_leftRight : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : Module.End K V),
    LinearMap.det (leftRight A B) =
      (LinearMap.det A * LinearMap.det B) ^ Module.finrank K V

end Specs.D05.M15.TensorCoordinates.LeftRightInvariants
