import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! Converse in paper.tex 754–819. Right modules are left modules over the
opposite ring. The regular module below has underlying `Sᵐᵒᵖ`; unop identifies
it with `S_S`. ULift places it in the universe of the module category.
No additivity or linearity of the equivalence is assumed. -/

universe u v w

namespace P103.Specs.Ch03.MoritaConverse

open CategoryTheory Limits
open scoped DirectSum

/-- The right regular module, in any larger module universe. -/
abbrev regular (S : Type u) [Ring S] : ModuleCat.{max u v} Sᵐᵒᵖ :=
  ModuleCat.of Sᵐᵒᵖ (ULift.{v} Sᵐᵒᵖ)

/-- Explicit identification with the usual right regular action on S. -/
def regularEquiv (S : Type u) [Ring S] : regular.{u,v} S ≃ₗ[Sᵐᵒᵖ] S :=
  ULift.moduleEquiv.trans (MulOpposite.opLinearEquiv Sᵐᵒᵖ (M := S)).symm

/-- Every module is a quotient of a direct sum of copies of P. -/
def Generator {R : Type u} [Ring R] (P : ModuleCat.{v} Rᵐᵒᵖ) : Prop :=
  ∀ M : ModuleCat.{v} Rᵐᵒᵖ,
    ∃ (I : Type v) (q : (⨁ _j : I, P) →ₗ[Rᵐᵒᵖ] M), Function.Surjective q

/-- Maps out of P into a sum use only finitely many summands. The formula is
independent of the chosen colimit and exhibits a factorization through the
finite subsum. -/
def FiniteSumFactorization {C : Type u} [Category.{v} C] [Preadditive C] (P : C) : Prop :=
  ∀ (I : Type w) (X : I → C) (c : Cofan X), IsColimit c →
    ∀ f : P ⟶ c.pt, ∃ (s : Finset I) (g : ∀ i, P ⟶ X i),
      f = ∑ i ∈ s, g i ≫ c.inj i

/-- Preservation and recovery of categorical structure, including all small
sums and quotient maps. -/
def preservationType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (E : ModuleCat.{max u v w} Sᵐᵒᵖ ≌ ModuleCat.{max u v w} Rᵐᵒᵖ),
    E.functor.Additive ∧ E.inverse.Additive ∧
    PreservesColimitsOfSize.{max u v w, max u v w} E.functor ∧
    PreservesColimitsOfSize.{max u v w, max u v w} E.inverse ∧
    (∀ (X Y : ModuleCat.{max u v w} Sᵐᵒᵖ) (f : X ⟶ Y),
      Function.Surjective f ↔ Function.Surjective (E.functor.map f))

/-- Preservation and recovery of the lifting property against all surjections,
expressed by the standard module-projectivity predicate. -/
def projectivityType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (E : ModuleCat.{max u v w} Sᵐᵒᵖ ≌ ModuleCat.{max u v w} Rᵐᵒᵖ)
    (A : ModuleCat.{max u v w} Sᵐᵒᵖ),
    Module.Projective Sᵐᵒᵖ A ↔ Module.Projective Rᵐᵒᵖ (E.functor.obj A)

/-- Full progenerator conclusion for any named object isomorphic to the image
of the regular module. The ring isomorphism is required to agree with the
map on endomorphisms induced by the original equivalence. -/
def converseType : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (E : ModuleCat.{max u v w} Sᵐᵒᵖ ≌ ModuleCat.{max u v w} Rᵐᵒᵖ)
    (P : ModuleCat.{max u v w} Rᵐᵒᵖ)
    (i : E.functor.obj (regular.{v, max u w} S) ≅ P),
    Module.Finite Rᵐᵒᵖ P ∧ Module.Projective Rᵐᵒᵖ P ∧ Generator P ∧
    FiniteSumFactorization.{max u v w + 1, max u v w, max u v w} P ∧
    ∃ e : Module.End Rᵐᵒᵖ P ≃+* S,
      ∀ f : Module.End Sᵐᵒᵖ (regular.{v, max u w} S),
        e (i.hom.hom.comp ((E.functor.map (ModuleCat.ofHom f)).hom.comp i.inv.hom)) =
          MulOpposite.unop ((f ⟨1⟩).down)

end P103.Specs.Ch03.MoritaConverse
