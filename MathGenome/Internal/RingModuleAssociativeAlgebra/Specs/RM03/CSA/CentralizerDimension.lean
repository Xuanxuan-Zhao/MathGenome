import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.RingTheory.SimpleRing.Basic

/-! The simplicity and dimension assertions of RM03-C04.08. -/

namespace Specs.RM03.CSA

open scoped TensorProduct
open MulOpposite

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

/-- The action of the tensor product through left and right multiplication in A. -/
abbrev centralizerTensorAction (B : Subalgebra k A) :
    (A ⊗[k] Bᵐᵒᵖ) →ₐ[k] Module.End k A :=
  (AlgHom.mulLeftRight k A).comp (Algebra.TensorProduct.map (AlgHom.id k A) B.val.op)

/-- The left tensor module on the underlying vector space of A. -/
abbrev centralizerTensorModule (B : Subalgebra k A) : Module (A ⊗[k] Bᵐᵒᵖ) A :=
  Module.compHom A (centralizerTensorAction B).toRingHom

/-- Restricting the tensor module to the base field recovers the given field action. -/
theorem centralizerTensorScalarTower (B : Subalgebra k A) :
    letI := centralizerTensorModule B
    IsScalarTower k (A ⊗[k] Bᵐᵒᵖ) A := by
  let := centralizerTensorModule B
  constructor
  intro r z x
  change centralizerTensorAction B (r • z) x = r • centralizerTensorAction B z x
  rw [map_smul]
  rfl

/-- Right multiplication identifies the opposite centralizer with the tensor-module endomorphisms. -/
def CentralizerEndType : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] (B : Subalgebra k A),
    letI := centralizerTensorModule B
    letI := centralizerTensorScalarTower B
    ∃ e : (Subalgebra.centralizer k (B : Set A))ᵐᵒᵖ ≃ₐ[k] Module.End (A ⊗[k] Bᵐᵒᵖ) A,
      ∀ (c : Subalgebra.centralizer k (B : Set A)) (x : A), e (op c) x = x * (c : A)

/-- The centralizer of a simple subalgebra is simple and its dimension is the complementary factor. -/
def CentralizerSimpleAndFinrankType : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    (_hA : isCentralSimple k A) (B : Subalgebra k A),
    IsSimpleRing B →
      IsSimpleRing (Subalgebra.centralizer k (B : Set A)) ∧
        Module.finrank k B * Module.finrank k (Subalgebra.centralizer k (B : Set A)) =
          Module.finrank k A

end Specs.RM03.CSA
