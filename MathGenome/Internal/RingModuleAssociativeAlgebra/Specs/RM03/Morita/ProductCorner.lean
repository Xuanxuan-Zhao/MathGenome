import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.Corner
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Ring.Prod
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! The product-ring example of a non-full corner in RM03-C05.02. -/

universe u v

namespace RM03.Morita

open CategoryTheory CategoryTheory.Limits MulOpposite

/-- The idempotent `(1, 0)` of the product ring. -/
def productIdempotent (A : Type u) (B : Type v) [Ring A] [Ring B] : Idempotent (A × B) :=
  ⟨(1, 0), by
    change ((1 : A) * 1, (0 : B) * 0) = (1, 0)
    simp⟩

/-- The regular right `B`-module regarded as a right `A × B`-module by second projection. -/
def productRightModule (A : Type u) (B : Type v) [Ring A] [Ring B] : ModuleCat.{v} (A × B)ᵐᵒᵖ :=
  letI : Module (A × B)ᵐᵒᵖ B := Module.compHom B (RingHom.op (RingHom.snd A B))
  ModuleCat.of (A × B)ᵐᵒᵖ B

namespace ProductCornerSpec

def cornerEquivType : Prop :=
  ∀ (A : Type u) (B : Type v) [Ring A] [Ring B] [Nontrivial A] [Nontrivial B],
    ∃ φ : Corner (productIdempotent A B) ≃+* A,
      (∀ x, φ x = x.val.1) ∧ (∀ a, (φ.symm a).val = (a, 0))

def idealType : Prop :=
  ∀ (A : Type u) (B : Type v) [Ring A] [Ring B] [Nontrivial A] [Nontrivial B],
    let I := TwoSidedIdeal.span ({(productIdempotent A B).val} : Set (A × B))
    (I : Set (A × B)) = Set.univ ×ˢ ({0} : Set B) ∧ I ≠ ⊤

def functorType : Prop :=
  ∀ (A : Type u) (B : Type v) [Ring A] [Ring B] [Nontrivial A] [Nontrivial B],
    let e := productIdempotent A B
    let M := productRightModule A B
    let F := CornerSpec.cornerFunctorValue.{max u v, v} e
    Nontrivial M ∧ (∀ b : M, op e.val • b = 0) ∧ IsZero (F.obj M) ∧ ¬ F.IsEquivalence

end ProductCornerSpec
end RM03.Morita
