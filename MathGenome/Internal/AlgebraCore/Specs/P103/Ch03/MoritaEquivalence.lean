import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.MoritaEvaluations
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Matrix.Basic

/-! Independent statements for the forward Morita theorem, paper.tex 754–819.
The equivalence includes its natural isomorphisms and triangle laws. The
additive identifications below specify the actual tensor functors, their outer
actions, their maps on morphisms, and the two evaluation contractions.
The converse is allocated to c03_morita_converse. -/
noncomputable section
universe u v w
namespace P103.Morita.EquivalenceSpec
open CategoryTheory MulOpposite P103.BalancedTensor

variable (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- Tensor on the right with the dual and with P, including the canonical
unit inverse and counit formulas. Module universes can be arbitrarily large. -/
def RightTensorEquivalence : Prop :=
  ∃ E : ModuleCat.{max u v w} Rᵐᵒᵖ ≌ ModuleCat.{max u v w} (S R P)ᵐᵒᵖ,
  ∃ eF : ∀ X, (E.functor.obj X) ≃+ Tensor R X (Q R P),
  ∃ eG : ∀ Y, (E.inverse.obj Y) ≃+ Tensor (S R P) Y P,
    (∀ X (s : (S R P)ᵐᵒᵖ) x q,
      eF X (s • (eF X).symm (tmul R x q)) = tmul R x (s • q)) ∧
    (∀ Y (r : Rᵐᵒᵖ) y p,
      eG Y (r • (eG Y).symm (tmul (S R P) y p)) = tmul (S R P) y (r • p)) ∧
    (∀ X X' (f : X ⟶ X') x q,
      eF X' (E.functor.map f ((eF X).symm (tmul R x q))) = tmul R (f x) q) ∧
    (∀ Y Y' (g : Y ⟶ Y') y p,
      eG Y' (E.inverse.map g ((eG Y).symm (tmul (S R P) y p))) =
        tmul (S R P) (g y) p) ∧
    (∀ X x q p,
      E.unitIso.inv.app X ((eG (E.functor.obj X)).symm
        (tmul (S R P) ((eF X).symm (tmul R x q)) p)) = op (q p) • x) ∧
    (∀ Y y p q,
      E.counitIso.hom.app Y ((eF (E.inverse.obj Y)).symm
        (tmul R ((eG Y).symm (tmul (S R P) y p)) q)) =
          op (theta R P p q) • y)

def rightEquivalenceType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P],
    IsGenerator R P → RightTensorEquivalence.{u,v,w} R P

/-- Left generators use the same quotient-of-sums convention without an
opposite-ring action on their elements. -/
def IsLeftGenerator (R : Type u) [Ring R] (P : Type v)
    [AddCommGroup P] [Module R P] : Prop :=
  ∀ (M : Type (max u v)) [AddCommGroup M] [Module R M],
    ∃ (J : Type (max u v)) (f : (J →₀ P) →ₗ[R] M), Function.Surjective f

/-- The endomorphism ring in the left form is explicitly opposite. -/
def leftEquivalenceType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P],
    IsLeftGenerator R P →
    Nonempty (ModuleCat.{max u v w} R ≌ ModuleCat.{max u v w} (Module.End R P)ᵐᵒᵖ)

/-- The matrix specialization includes the progenerator and the actual
endomorphism ring identification, with column convention and composition
multiplication, as well as equivalences on both module sides. -/
def matrixEquivalenceType : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ), 0 < n →
    Module.Finite Rᵐᵒᵖ (Fin n → R) ∧
    Module.Projective Rᵐᵒᵖ (Fin n → R) ∧
    IsGenerator R (Fin n → R) ∧
    (∃ e : Module.End Rᵐᵒᵖ (Fin n → R) ≃+* Matrix (Fin n) (Fin n) R,
      ∀ f i j, e f i j = f (Pi.single j 1) i) ∧
    Nonempty (ModuleCat.{max u w} Rᵐᵒᵖ ≌
      ModuleCat.{max u w} (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ) ∧
    Nonempty (ModuleCat.{max u w} R ≌ ModuleCat.{max u w} (Matrix (Fin n) (Fin n) R))

end P103.Morita.EquivalenceSpec
