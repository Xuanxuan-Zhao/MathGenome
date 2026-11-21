import Mathlib.Algebra.Module.Injective
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.HomTensorExactness
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.SplitSequences

/-! Theorem 2.2, paper.tex 303–329. All modules and the ring range over an
arbitrary common adequate universe. No finiteness, commutativity or nonzero
hypothesis is imposed. Hom is an abelian group over a noncommutative ring.
A right R-module is a left Rᵐᵒᵖ-module; its ideals are `Ideal Rᵐᵒᵖ`.
-/
namespace P103.Specs.Ch02.Injective

universe u

/-- Extension along every injective linear map. -/
def Extension (R E : Type u) [Ring R] [AddCommGroup E] [Module R E] : Prop :=
  ∀ (U M : Type u) [AddCommGroup U] [AddCommGroup M] [Module R U] [Module R M]
    (i : U →ₗ[R] M), Function.Injective i →
    ∀ f : U →ₗ[R] E, ∃ g : M →ₗ[R] E, g.comp i = f

/-- Baer's test, for all left ideals, with their actual inclusion in R. -/
def IdealExtension (R E : Type u) [Ring R] [AddCommGroup E] [Module R E] : Prop :=
  ∀ (I : Ideal R) (f : I →ₗ[R] E), ∃ g : R →ₗ[R] E, g.comp I.subtype = f

/-- The complete reversed short exact sequence of abelian Hom groups. -/
def HomExact (R E : Type u) [Ring R] [AddCommGroup E] [Module R E] : Prop :=
  ∀ (A B C : Type u) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C] (i : A →ₗ[R] B) (p : B →ₗ[R] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    Function.Injective (P103.HomTensorExactness.pre (Q := E) p) ∧
    Function.Exact (P103.HomTensorExactness.pre (Q := E) p)
      (P103.HomTensorExactness.pre (Q := E) i) ∧
    Function.Surjective (P103.HomTensorExactness.pre (Q := E) i)

/-- Every short exact sequence beginning in E has a section of its quotient.
The upstream splitting theorem identifies this with a retraction of E and an
isomorphism with the standard split sequence, fixing both endpoints. -/
def Splits (R E : Type u) [Ring R] [AddCommGroup E] [Module R E] : Prop :=
  ∀ (B C : Type u) [AddCommGroup B] [AddCommGroup C] [Module R B] [Module R C]
    (i : E →ₗ[R] B) (p : B →ₗ[R] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∃ s : C →ₗ[R] B, p.comp s = LinearMap.id

def extension_iff_injectiveType : Prop :=
  ∀ (R E : Type u) [Ring R] [AddCommGroup E] [Module R E],
    Extension R E ↔ Module.Injective R E

def baerCriterionType : Prop :=
  ∀ (R E : Type u) [Ring R] [AddCommGroup E] [Module R E],
    Extension R E ↔ IdealExtension R E

def homExact_iffType : Prop :=
  ∀ (R E : Type u) [Ring R] [AddCommGroup E] [Module R E],
    Extension R E ↔ HomExact R E

def splits_iffType : Prop :=
  ∀ (R E : Type u) [Ring R] [AddCommGroup E] [Module R E],
    Extension R E ↔ Splits R E

/-- All four conditions for right modules; the ideal test here quantifies over
right ideals, represented by left ideals in the opposite ring. -/
def rightModuleCriterionType : Prop :=
  ∀ (R E : Type u) [Ring R] [AddCommGroup E] [Module Rᵐᵒᵖ E],
    (Extension Rᵐᵒᵖ E ↔ Module.Injective Rᵐᵒᵖ E) ∧
    (Extension Rᵐᵒᵖ E ↔ IdealExtension Rᵐᵒᵖ E) ∧
    (Extension Rᵐᵒᵖ E ↔ HomExact Rᵐᵒᵖ E) ∧
    (Extension Rᵐᵒᵖ E ↔ Splits Rᵐᵒᵖ E)

end P103.Specs.Ch02.Injective
