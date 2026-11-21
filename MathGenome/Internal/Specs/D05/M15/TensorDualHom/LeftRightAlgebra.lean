import MathGenome.Internal.Specs.D05.M03.HomDimension
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! Independent statements for paper.tex:2831–2837.

`Module.End K V` is the original endomorphism algebra, with multiplication
given by composition. The ordinary tensor product and the tensor product with
the opposite algebra have the same underlying linear construction, but different
multiplications. The maps below specify the action, without assuming that it is
bijective. All isomorphism assertions include the zero-dimensional case.
-/

namespace Specs.D05.M15.TensorDualHom.LeftRightAlgebra

open scoped TensorProduct
open MulOpposite
open Specs.D05.M03.HomDimension (elementaryMap)

/-- The left/right action with the multiplication-compatible source algebra. -/
noncomputable def oppositeAction (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] :
    (Module.End K V ⊗[K] (Module.End K V)ᵐᵒᵖ) →ₐ[K]
      Module.End K (Module.End K V) :=
  AlgHom.mulLeftRight K (Module.End K V)

def oppositeAction_type :=
  (K V : Type*) → [Field K] → [AddCommGroup V] → [Module K V] →
    (Module.End K V ⊗[K] (Module.End K V)ᵐᵒᵖ) →ₐ[K]
      Module.End K (Module.End K V)

noncomputable def oppositeAction_value : oppositeAction_type := @oppositeAction

/-- The paper's linear map from the ordinary tensor product. -/
noncomputable def leftRight (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    (Module.End K V ⊗[K] Module.End K V) →ₗ[K]
      Module.End K (Module.End K V) :=
  (oppositeAction K V).toLinearMap.comp
    (TensorProduct.congr (LinearEquiv.refl K (Module.End K V))
      (opLinearEquiv K)).toLinearMap

def leftRight_type :=
  (K V : Type*) → [Field K] → [AddCommGroup V] → [Module K V] →
    (Module.End K V ⊗[K] Module.End K V) →ₗ[K]
      Module.End K (Module.End K V)

noncomputable def leftRight_value : leftRight_type := @leftRight

def leftRight_tmul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a b X : Module.End K V),
    leftRight K V (a ⊗ₜ[K] b) X = a * X * b

def oppositeAction_tmul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a b X : Module.End K V),
    oppositeAction K V (a ⊗ₜ[K] op b) X = a * X * b

/-- Bijectivity of the specified ordinary-tensor action, not just an equality
of the dimensions of two abstract spaces. -/
def linear_isomorphism : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    ∃ e : (Module.End K V ⊗[K] Module.End K V) ≃ₗ[K]
      Module.End K (Module.End K V), e.toLinearMap = leftRight K V

/-- The algebra isomorphism has the canonical left/right action as its map. -/
def algebra_isomorphism : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    ∃ e : (Module.End K V ⊗[K] (Module.End K V)ᵐᵒᵖ) ≃ₐ[K]
      Module.End K (Module.End K V), e.toAlgHom = oppositeAction K V

/-- The displayed two Kronecker deltas, including repeated indices and every
characteristic, expressed as an if-then-else. -/
def matrix_unit_action : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Module.Basis (Fin n) K V) (i j a b k l : Fin n),
    leftRight K V (elementaryMap e e i j ⊗ₜ[K] elementaryMap e e k l)
      (elementaryMap e e a b) =
      if j = a ∧ b = k then elementaryMap e e i l else 0

/-- These images form the full matrix-unit basis on the endomorphism space.
The output index is `(i,l)` and the input index is `(j,k)`. -/
def matrix_unit_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Module.Basis (Fin n) K V),
    ∃ B : Module.Basis ((Fin n × Fin n) × (Fin n × Fin n)) K
      (Module.End K (Module.End K V)),
      ∀ i j k l,
        leftRight K V (elementaryMap e e i j ⊗ₜ[K] elementaryMap e e k l) =
          B ((i, l), (j, k))

/-- Composition reverses the order of the two right multipliers. -/
def composition_rule : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a b c d : Module.End K V),
    leftRight K V (a ⊗ₜ[K] b) * leftRight K V (c ⊗ₜ[K] d) =
      leftRight K V ((a * c) ⊗ₜ[K] (d * b))

/-- On elementary tensors, the opposite tensor algebra has exactly the
reversed second-factor multiplication required by the composition rule. -/
def opposite_tensor_product : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a b c d : Module.End K V),
    (a ⊗ₜ[K] op b) * (c ⊗ₜ[K] op d) =
      (a * c) ⊗ₜ[K] op (d * b)

/-- The empty dimension is retained explicitly; both vector spaces in the
ordinary linear isomorphism are zero. -/
def zero_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], Module.finrank K V = 0 →
    (∀ z : Module.End K V ⊗[K] Module.End K V, z = 0) ∧
      (∀ T : Module.End K (Module.End K V), T = 0)

/-- In dimension at least two the ordinary tensor multiplication does not
make the canonical linear map multiplicative. Two distinct basis indices
express precisely the noncommutative case, avoiding a false claim in
dimensions zero and one. -/
def ordinary_not_multiplicative : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Module.Basis (Fin n) K V) (i j : Fin n), i ≠ j →
    ¬ (∀ s t : Module.End K V ⊗[K] Module.End K V,
      leftRight K V (s * t) = leftRight K V s * leftRight K V t)

end Specs.D05.M15.TensorDualHom.LeftRightAlgebra
