import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Density.Action
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.LinearMap.FiniteRange
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-! The finite-rank operator algebra and scalar commutant in RM03-C03.03. -/

universe u v

namespace RM03.Specs.Density.FiniteRankModule

section Definitions

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

/-- Finite rank means the image is finite-dimensional over the original field. -/
def finiteRankIdealValue : TwoSidedIdeal (Module.End k V) :=
  TwoSidedIdeal.mk' {f | f.HasFiniteRange}
    LinearMap.HasFiniteRange.zero
    (fun hf hg ↦ hf.add hg)
    (fun hf ↦ hf.neg)
    (fun {_ _} hg ↦ hg.comp_left _)
    (fun {_ _} hf ↦ hf.comp_right _)

/-- The unital subalgebra of scalar maps plus finite-rank maps. -/
def scalarPlusFiniteRankValue : Subalgebra k (Module.End k V) where
  carrier := {T | ∃ c : k, ∃ f ∈ finiteRankIdealValue k V, T = algebraMap k _ c + f}
  algebraMap_mem' c := ⟨c, 0, (finiteRankIdealValue k V).zero_mem, (add_zero _).symm⟩
  zero_mem' := ⟨0, 0, (finiteRankIdealValue k V).zero_mem, by simp⟩
  one_mem' := ⟨1, 0, (finiteRankIdealValue k V).zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨c, f, hf, rfl⟩ ⟨d, g, hg, rfl⟩
    refine ⟨c + d, f + g, (finiteRankIdealValue k V).add_mem hf hg, ?_⟩
    rw [map_add, add_add_add_comm]
  mul_mem' := by
    rintro _ _ ⟨c, f, hf, rfl⟩ ⟨d, g, hg, rfl⟩
    let I := finiteRankIdealValue k V
    refine ⟨c * d, algebraMap k _ c * g + f * (algebraMap k _ d + g),
      I.add_mem (I.mul_mem_left _ _ hg) (I.mul_mem_right _ _ hf), ?_⟩
    rw [map_mul, add_mul, mul_add (algebraMap k _ c), add_assoc]

/-- Restrict the tautological endomorphism action to the given subalgebra. -/
abbrev evaluationModuleValue : Module (scalarPlusFiniteRankValue k V) V :=
  (scalarPlusFiniteRankValue k V).moduleLeft

instance evaluationScalarTower : IsScalarTower k (scalarPlusFiniteRankValue k V) V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

instance endomorphismScalarTower :
    IsScalarTower k (Module.End (scalarPlusFiniteRankValue k V) V) V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

end Definitions

-- Keep the field and vector space universes independent.
set_option linter.checkUnivs false

def finiteRankIdealType :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V],
    TwoSidedIdeal (Module.End k V)

def mem_finiteRankIdealType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (f : Module.End k V), f ∈ finiteRankIdealValue k V ↔ FiniteDimensional k f.range

def scalarPlusFiniteRankType :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V],
    Subalgebra k (Module.End k V)

def mem_scalarPlusFiniteRankType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V] (T : Module.End k V),
    T ∈ scalarPlusFiniteRankValue k V ↔
      ∃ c : k, ∃ f ∈ finiteRankIdealValue k V, T = algebraMap k (Module.End k V) c + f

def evaluationModuleType :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V],
    Module (scalarPlusFiniteRankValue k V) V

def evaluation_smulType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (r : scalarPlusFiniteRankValue k V) (x : V), r • x = (r : Module.End k V) x

def faithfulType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V],
    FaithfulSMul (scalarPlusFiniteRankValue k V) V

def simpleType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (_b : Module.Basis ℕ k V), IsSimpleModule (scalarPlusFiniteRankValue k V) V

def commutantType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (_b : Module.Basis ℕ k V) (T : Module.End k V),
    (∀ r : scalarPlusFiniteRankValue k V, Commute T (r : Module.End k V)) ↔
      ∃ c : k, T = algebraMap k (Module.End k V) c

def commutantEquiv_existsType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (_b : Module.Basis ℕ k V),
    ∃ e : k ≃ₐ[k] Module.End (scalarPlusFiniteRankValue k V) V,
      (∀ (c : k) (x : V), e c x = c • x) ∧
      (∀ (c : k) (x : V),
        rightSMulValue (scalarPlusFiniteRankValue k V) x (MulOpposite.op (e c)) = c • x)

def rightEndEquiv_existsType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (_b : Module.Basis ℕ k V),
    ∃ e : RightEndValue (scalarPlusFiniteRankValue k V) V ≃ₐ[k] Module.End k V,
      (∀ (T : RightEndValue (scalarPlusFiniteRankValue k V) V) (x : V), e T x = T x) ∧
      (∀ r : scalarPlusFiniteRankValue k V,
        e (actionValue (scalarPlusFiniteRankValue k V) V r) = (r : Module.End k V))

end RM03.Specs.Density.FiniteRankModule
