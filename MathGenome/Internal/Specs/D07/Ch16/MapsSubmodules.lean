import MathGenome.Internal.Specs.D07.Ch16.Definition
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
Independent specification of K07.16.maps_submodules, paper.tex:2945–2957.

All scalars form an associative unital ring, possibly noncommutative or
the zero ring. All modules are unital left modules on abelian groups.
No freeness, basis, finite generation, or nonzero-module hypothesis is used.

The two submodule characterizations retain the exact underlying subset.
Kernels, images, and arbitrary intersections are identified with the
underlying sets of their canonical submodules. Intersections include an
empty family. Finite linear combinations use a finite subset of the
generating set and arbitrary scalar coefficients; the finite subset may
be empty. The span characterization is thus meaningful for every set,
including the empty set, without any chosen basis.
-/

universe u v w t

namespace Specs.D07.Ch16.MapsSubmodules

open scoped BigOperators

/-- Addition and scalar preservation are exactly the linear-map data. -/
def LinearMapCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] (f : M → N),
    ((∀ x y, f (x + y) = f x + f y) ∧
      (∀ (r : R) x, f (r • x) = r • f x)) ↔
      ∃ g : M →ₗ[R] N, (g : M → N) = f

/-- A submodule is precisely an additive subgroup closed under the action. -/
def SubmoduleCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (S : Set M),
    (∃ A : AddSubgroup M, (A : Set M) = S ∧
      ∀ (r : R) x, x ∈ A → r • x ∈ A) ↔
      ∃ P : Submodule R M, (P : Set M) = S

/-- Nonemptiness replaces the zero and inverse closure axioms. -/
def SubmoduleNonemptyTest : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (S : Set M),
    (S.Nonempty ∧ (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) ∧
      (∀ (r : R) x, x ∈ S → r • x ∈ S)) ↔
      ∃ P : Submodule R M, (P : Set M) = S

/-- The source's cancellation-free witnesses for zero and additive inverses. -/
def ZeroNegFromClosure : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (S : Set M),
    S.Nonempty → (∀ (r : R) x, x ∈ S → r • x ∈ S) →
      0 ∈ S ∧ ∀ x ∈ S, -x ∈ S

/-- The set-theoretic kernel is the carrier of the canonical submodule. -/
def KernelSubmodule : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
    (LinearMap.ker f : Set M) = {x | f x = 0}

/-- The ordinary image is the carrier of the canonical range submodule. -/
def ImageSubmodule : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
    (LinearMap.range f : Set N) = Set.range f

/-- An arbitrary intersection, including an empty intersection, is a submodule. -/
def IntersectionSubmodule : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type t) (P : ι → Submodule R M),
    ((⨅ i, P i : Submodule R M) : Set M) = ⋂ i, (P i : Set M)

/-- Span consists exactly of finite sums of scalar multiples of generators. -/
def SpanFiniteSums : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (S : Set M) (x : M),
    x ∈ Submodule.span R S ↔
      ∃ (F : Finset M) (c : M → R),
        (↑F : Set M) ⊆ S ∧ ∑ m ∈ F, c m • m = x

/-- Span is closed under zero, addition, and the left scalar action. -/
def SpanClosure : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (S : Set M),
    0 ∈ Submodule.span R S ∧
      (∀ x ∈ Submodule.span R S, ∀ y ∈ Submodule.span R S,
        x + y ∈ Submodule.span R S) ∧
      (∀ (r : R) x, x ∈ Submodule.span R S → r • x ∈ Submodule.span R S)

/-- Span contains the generators and is the least submodule doing so. -/
def SpanUniversalProperty : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (S : Set M),
    S ⊆ Submodule.span R S ∧
      ∀ P : Submodule R M, Submodule.span R S ≤ P ↔ S ⊆ P

end Specs.D07.Ch16.MapsSubmodules
