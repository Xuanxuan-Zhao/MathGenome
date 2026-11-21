import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.JacobsonRadical
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
Nakayama's assertions in paper.tex, Theorem 3.2, lines 619–622 and 642–648.
The scalar ring is unital and may be noncommutative or the zero ring.
`I • ⊤` is the submodule of finite sums of products `a • m` with `a ∈ I`,
so it represents `IM`. `Module.Finite R M` means finite generation.
`Subsingleton M` expresses that the module is zero.

A right R-module is a left `Rᵐᵒᵖ`-module, following the global convention
at paper.tex line 47. Its two-sided ideal is represented as an ideal of
`Rᵐᵒᵖ`, and `I • ⊤` then represents `MI`. The upstream equality of left
and right radicals identifies the radical condition with the same `J(R)`.
The lifting statements quantify over arbitrary index types, including empty
ones, and every choice of lifts, without assuming that the family is finite.
-/

universe u v w

namespace P103.Specs.Ch03.Nakayama

open P103.Specs.Ch03.JacobsonRadical (radical)

def eq_zeroType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [I.IsTwoSided],
    I ≤ radical R → I • (⊤ : Submodule R M) = ⊤ → Subsingleton M

def sup_iffType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [I.IsTwoSided],
    I ≤ radical R → ∀ N : Submodule R M,
      N ⊔ I • (⊤ : Submodule R M) = ⊤ ↔ N = ⊤

def generators_liftType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [I.IsTwoSided],
    I ≤ radical R → ∀ (ι : Type w)
      (g : ι → M ⧸ (I • (⊤ : Submodule R M))) (x : ι → M),
      (∀ i, (I • (⊤ : Submodule R M)).mkQ (x i) = g i) →
      Submodule.span R (Set.range g) = ⊤ → Submodule.span R (Set.range x) = ⊤

def right_eq_zeroType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] (I : Ideal Rᵐᵒᵖ) [I.IsTwoSided],
    I ≤ radical Rᵐᵒᵖ → I • (⊤ : Submodule Rᵐᵒᵖ M) = ⊤ → Subsingleton M

def right_sup_iffType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] (I : Ideal Rᵐᵒᵖ) [I.IsTwoSided],
    I ≤ radical Rᵐᵒᵖ → ∀ N : Submodule Rᵐᵒᵖ M,
      N ⊔ I • (⊤ : Submodule Rᵐᵒᵖ M) = ⊤ ↔ N = ⊤

def right_generators_liftType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] (I : Ideal Rᵐᵒᵖ) [I.IsTwoSided],
    I ≤ radical Rᵐᵒᵖ → ∀ (ι : Type w)
      (g : ι → M ⧸ (I • (⊤ : Submodule Rᵐᵒᵖ M))) (x : ι → M),
      (∀ i, (I • (⊤ : Submodule Rᵐᵒᵖ M)).mkQ (x i) = g i) →
      Submodule.span Rᵐᵒᵖ (Set.range g) = ⊤ →
      Submodule.span Rᵐᵒᵖ (Set.range x) = ⊤

end P103.Specs.Ch03.Nakayama
