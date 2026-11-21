import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
The free-module part of paper.tex, Proposition 1.4 (lines 113–127).
Rings are associative and unital, may be zero, and need not be commutative.
An arbitrary type represents the generating set, including the empty set.
Right modules are left modules over the opposite ring, as in the conventions.
-/

universe u v w

namespace P103.Ch01

/-- The direct sum of copies of `R`, rather than the unrestricted product `X → R`. -/
abbrev FreeModule (R : Type u) (X : Type v) [Ring R] := X →₀ R

/-- The standard generator at `x`. -/
noncomputable def freeGenerator (R : Type u) (X : Type v) [Ring R] (x : X) :
    FreeModule R X := Finsupp.single x 1

/-- A right free module is represented using opposite coefficients. Under `unop`,
left multiplication by `op r` on these coefficients is right multiplication by `r`. -/
abbrev FreeRightModule (R : Type u) (X : Type v) [Ring R] := FreeModule Rᵐᵒᵖ X

end P103.Ch01

namespace Specs.P103.Ch01.FreeModules

open _root_.P103.Ch01

/-- The standard generators form an actual basis, even over the zero ring. -/
def standardBasis : Prop :=
  ∀ (R : Type u) (X : Type v) [Ring R],
    ∃ b : Module.Basis X R (FreeModule R X), ∀ x, b x = freeGenerator R X x

/-- Existence and uniqueness are for every function, with no support restriction on it. -/
def uniqueExtension : Prop :=
  ∀ (R : Type u) (X : Type v) (M : Type w) [Ring R] [AddCommGroup M] [Module R M]
    (f : X → M),
    ∃! L : FreeModule R X →ₗ[R] M, ∀ x, L (freeGenerator R X x) = f x

/-- The extension is exactly the finite sum over the coefficient support. -/
def extensionFormula : Prop :=
  ∀ (R : Type u) (X : Type v) (M : Type w) [Ring R] [AddCommGroup M] [Module R M]
    (f : X → M) (L : FreeModule R X →ₗ[R] M)
    (_ : ∀ x, L (freeGenerator R X x) = f x) (c : FreeModule R X),
    L c = ∑ x ∈ c.support, c x • f x

/-- The inclusion into the full product consists exactly of finite-support functions. -/
def productInclusion : Prop :=
  ∀ (R : Type u) (X : Type v) [Ring R],
    Function.Injective (fun c : FreeModule R X => (c : X → R)) ∧
    ∀ g : X → R,
      (∃ c : FreeModule R X, (c : X → R) = g) ↔ (Function.support g).Finite

/-- Finite direct sums and products coincide under the canonical inclusion. -/
def finiteProduct : Prop :=
  ∀ (R : Type u) (X : Type v) [Ring R] [Finite X],
    ∃ e : FreeModule R X ≃ₗ[R] (X → R), ∀ c, e c = (c : X → R)

/-- For an infinite generating set and a nonzero ring, the constant-one product
vector is not in the direct sum. Nontriviality is used only for this distinction. -/
def infiniteProduct : Prop :=
  ∀ (R : Type u) (X : Type v) [Ring R] [Nontrivial R] [Infinite X],
    ¬ ∃ c : FreeModule R X, (c : X → R) = fun _ => 1

/-- Empty generating sets give the zero module; zero rings do so for every set. -/
def boundaryCases : Prop :=
  (∀ (R : Type u) (X : Type v) [Ring R] [IsEmpty X] (c : FreeModule R X), c = 0) ∧
  (∀ (R : Type u) (X : Type v) [Ring R] [Subsingleton R] (c : FreeModule R X), c = 0)

/-- Full right-module assertion, including its standard basis and finite-sum formula.
`Module Rᵐᵒᵖ M` is precisely the convention for a right `R`-module. -/
def rightModule : Prop :=
  ∀ (R : Type u) (X : Type v) (M : Type w) [Ring R] [AddCommGroup M]
    [Module Rᵐᵒᵖ M],
    (∃ b : Module.Basis X Rᵐᵒᵖ (FreeRightModule R X),
      ∀ x, b x = freeGenerator Rᵐᵒᵖ X x) ∧
    ∀ f : X → M,
      ∃! L : FreeRightModule R X →ₗ[Rᵐᵒᵖ] M,
        (∀ x, L (freeGenerator Rᵐᵒᵖ X x) = f x) ∧
        ∀ c, L c = ∑ x ∈ c.support, c x • f x

end Specs.P103.Ch01.FreeModules
