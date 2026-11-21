import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.Equivalence

/-! Specifications for the group law in RM03-C04.11. -/

universe u v w

namespace Specs.RM03.Brauer

open scoped TensorProduct
open MulOpposite

/-- An algebra equivalence already identifies the classes without stabilization. -/
def ClassOfEqOfAlgEquiv : Prop :=
  ∀ {k : Type u} [Field k] {A B : _root_.CSA.{u, v} k},
    (A ≃ₐ[k] B) → classOf A = classOf B

/-- Tensor product respects the same positive-size matrix relation in both factors. -/
def TensorRespectsEquivalence : Prop :=
  ∀ {k : Type u} [Field k] {A A' : Type v} [Ring A] [Ring A']
    [Algebra k A] [Algebra k A'] {B B' : Type w} [Ring B] [Ring B']
    [Algebra k B] [Algebra k B'],
    equivalent k A A' → equivalent k B B' → equivalent k (A ⊗[k] B) (A' ⊗[k] B')

def OppositeRespectsEquivalence : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {B : Type w} [Ring B] [Algebra k B],
    equivalent k A B → equivalent k Aᵐᵒᵖ Bᵐᵒᵖ

/-- The product of an algebra and its opposite is split over the original field. -/
def TensorOppositeSplit : Prop :=
  ∀ {k : Type u} [Field k] (A : _root_.CSA.{u, v} k), CSA.isSplit k (A ⊗[k] Aᵐᵒᵖ)

/-- The additive operations on the quotient are prescribed on the original algebra data.
The carrier universe contains the base field and therefore also its chosen lift. -/
def GroupLaws (k : Type u) [Field k] (g : AddCommGroup (BrauerGroup.{u, max u v} k)) :
    Prop :=
  letI := g
  (0 : BrauerGroup.{u, max u v} k) = classOf (scalarCSA.{u, v} k) ∧
  (∀ A B : _root_.CSA.{u, max u v} k,
    ∃ C : _root_.CSA.{u, max u v} k, C.toAlgCat = AlgCat.of k (A ⊗[k] B) ∧
      classOf A + classOf B = classOf C) ∧
  (∀ A : _root_.CSA.{u, max u v} k,
    ∃ B : _root_.CSA.{u, max u v} k, B.toAlgCat = AlgCat.of k Aᵐᵒᵖ ∧
      -classOf A = classOf B) ∧
  (∀ A : _root_.CSA.{u, max u v} k, classOf A = 0 ↔ CSA.isSplit k A)

/-- An abelian group on Mathlib's actual quotient, with the specified operations. -/
def GroupLaw : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ g : AddCommGroup (BrauerGroup.{u, max u v} k), GroupLaws.{u, v} k g

end Specs.RM03.Brauer
