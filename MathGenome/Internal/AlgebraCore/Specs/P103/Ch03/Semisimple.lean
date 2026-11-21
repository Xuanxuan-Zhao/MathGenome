import Mathlib.RingTheory.SimpleModule.Basic

/-!
Independent statements for paper.tex, Theorem 3.1 (lines 573–605).
Rings are unital, possibly noncommutative and possibly zero. Modules are
unital left modules. Taking `R := Sᵐᵒᵖ` gives exactly the right-module
statements under the global convention at paper.tex line 47.

We reuse `IsSimpleModule` and `IsSemisimpleModule`. Their meaning is made
explicit below: simple means nonzero with only the zero and whole submodule;
semisimple means every submodule has an internal direct complement.
`Π₀` denotes the dependent finite-support direct sum, with no finiteness
restriction on its index type. The empty direct sum is allowed.
-/

universe u v w z

namespace P103.Specs.Ch03.Semisimple

def simple_iffType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    IsSimpleModule R M ↔
      Nontrivial M ∧ ∀ U : Submodule R M, U = ⊥ ∨ U = ⊤

def schurType : Prop :=
  ∀ (R : Type u) (M : Type v) (N : Type w)
    [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N),
    f ≠ 0 → ∃ e : M ≃ₗ[R] N, e.toLinearMap = f

def endomorphismDivisionRingType :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M], DivisionRing (Module.End R M)

noncomputable def endomorphismDivisionRingValue : endomorphismDivisionRingType := by
  classical
  intro R M _ _ _ _
  infer_instance

/-- The division ring uses the original addition and composition of endomorphisms. -/
def endomorphism_ring_compatibleType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M],
    (endomorphismDivisionRingValue R M).toRing = (inferInstance : Ring (Module.End R M))

def semisimple_iff_directSumType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    IsSemisimpleModule R M ↔
      ∃ (s : Set (Submodule R M)) (_ : M ≃ₗ[R] Π₀ U : s, U.1),
        ∀ U : s, IsSimpleModule R U.1

def semisimple_iff_sumType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    IsSemisimpleModule R M ↔
      sSup {U : Submodule R M | IsSimpleModule R U} = ⊤

def semisimple_iff_summandType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    IsSemisimpleModule R M ↔
      ∀ U : Submodule R M, ∃ V : Submodule R M, IsCompl U V

/-- An internal decomposition, not merely an abstract isomorphism. -/
def internal_decompositionType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M],
    ∃ s : Set (Submodule R M),
      sSupIndep s ∧ sSup s = ⊤ ∧ ∀ U ∈ s, IsSimpleModule R U

def submoduleType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] (U : Submodule R M), IsSemisimpleModule R U

def quotientType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] (U : Submodule R M), IsSemisimpleModule R (M ⧸ U)

/-- Any family of simple modules, on any index type, has semisimple direct sum. -/
def arbitrary_directSumType : Prop :=
  ∀ (R : Type u) (ι : Type w) (S : ι → Type z) [Ring R]
    [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)]
    [∀ i, IsSimpleModule R (S i)], IsSemisimpleModule R (Π₀ i, S i)

/-- The zero module is semisimple over every ring, including the zero ring. -/
def zeroType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [Subsingleton M], IsSemisimpleModule R M

end P103.Specs.Ch03.Semisimple
