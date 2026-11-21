import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! Independent interfaces for paper.tex, `lem:p202-free-chain-dual`, 1751–1773.
All complexes are integer graded; the lower bound can be any integer, and
there is no upper bound or restriction on the rank of a free module.
For a noncommutative ring the dual is naturally a complex of abelian groups.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite

universe u v

namespace P202Specs.FreeChainDual

/-- Vanishing below an arbitrary integer, up to the unique isomorphism with zero. -/
def BoundedBelow {R : Type u} [Ring R] (C : ChainComplex (ModuleCat.{v} R) ℤ) : Prop :=
  ∃ b : ℤ, ∀ n : ℤ, n < b → IsZero (C.X n)

/-- Algebraic cochains, with differential `a ↦ a ∘ ∂`, without an extra sign. -/
noncomputable def dual {R : Type u} [Ring R]
    (C : ChainComplex (ModuleCat.{v} R) ℤ) (A : ModuleCat.{v} R) :
    CochainComplex Ab.{v} ℤ :=
  ((preadditiveYoneda.obj A).mapHomologicalComplex (.up ℤ)).obj C.op

/-- In every degree this is precomposition by the given chain map. -/
noncomputable def dualMap {R : Type u} [Ring R]
    {C D : ChainComplex (ModuleCat.{v} R) ℤ} (f : C ⟶ D) (A : ModuleCat.{v} R) :
    dual D A ⟶ dual C A :=
  ((preadditiveYoneda.obj A).mapHomologicalComplex (.up ℤ)).map
    ((opFunctor (ModuleCat.{v} R) (.down ℤ)).map f.op)

/-- A reverse chain map and both actual chain homotopies are supplied by `e`. -/
def HomotopyEquivalenceType : Prop :=
  ∀ {R : Type u} [Ring R] (C D : ChainComplex (ModuleCat.{v} R) ℤ)
    [∀ n, Module.Free R (C.X n)] [∀ n, Module.Free R (D.X n)],
    BoundedBelow C → BoundedBelow D → ∀ (f : C ⟶ D) [QuasiIso f],
      ∃ e : HomotopyEquiv C D, e.hom = f

/-- Precomposition induces an isomorphism on cohomology in every integer degree
for every coefficient module, with no projectivity condition on the coefficients. -/
def DualCohomologyType : Prop :=
  ∀ {R : Type u} [Ring R] (C D : ChainComplex (ModuleCat.{v} R) ℤ)
    [∀ n, Module.Free R (C.X n)] [∀ n, Module.Free R (D.X n)],
    BoundedBelow C → BoundedBelow D → ∀ (f : C ⟶ D) [QuasiIso f]
      (A : ModuleCat.{v} R) (n : ℤ), IsIso (homologyMap (dualMap f A) n)

end P202Specs.FreeChainDual
