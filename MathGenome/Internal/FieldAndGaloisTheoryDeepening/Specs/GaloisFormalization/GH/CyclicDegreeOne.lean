import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-! The degree-one cohomology of a finite cyclic group, with its evaluation map. -/

noncomputable section

namespace GaloisFormalization.GH.CyclicDegreeOne

open scoped BigOperators

universe u v

section Model

variable {C : Type u} {A : Type v}
  [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- The cyclic norm, with the powers of the designated generator in increasing order. -/
def norm (s : C) : A →ₗ[ℤ] A where
  toFun a := ∑ i ∈ Finset.range (orderOf s), s ^ i • a
  map_add' a b := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' n a := by simp [smul_comm (_ : C) n a, Finset.smul_sum]

/-- The endomorphism `s - 1` of the coefficient group. -/
def generatorDifference (s : C) : A →ₗ[ℤ] A where
  toFun a := s • a - a
  map_add' a b := by rw [smul_add, add_sub_add_comm]
  map_smul' n a := by simp [smul_comm s n a, smul_sub]

/-- The image of `s - 1` inside the kernel of the norm. -/
def generatorDifferences (s : C) : Submodule ℤ (LinearMap.ker (norm (A := A) s)) :=
  (LinearMap.range (generatorDifference s)).comap (LinearMap.ker (norm s)).subtype

/-- The quotient of the norm kernel by the image of `s - 1`. -/
abbrev NormQuotient (s : C) :=
  LinearMap.ker (norm (A := A) s) ⧸ generatorDifferences s

end Model

namespace Specification

/-- The image of `s - 1` lies in the norm kernel. -/
def NormKillsDifferences : Prop :=
  ∀ (C : Type u) (A : Type v) [Group C] [Finite C] [AddCommGroup A] [DistribMulAction C A]
    (s : C), LinearMap.range (generatorDifference (A := A) s) ≤ LinearMap.ker (norm s)

/-- The cyclic norm uses exactly the group order when `s` generates the finite group. -/
def NormFormula : Prop :=
  ∀ (C : Type u) (A : Type v) [Group C] [Finite C] [AddCommGroup A] [DistribMulAction C A]
    (s : C), Subgroup.zpowers s = ⊤ → ∀ a : A,
      norm s a = ∑ i ∈ Finset.range (Nat.card C), s ^ i • a

/-- Evaluation at the generator induces the additive isomorphism on ordinary cohomology.
The universe lifts in the standard integral representation leave the action unchanged. -/
def EvaluationAtGenerator : Prop :=
  ∀ (C : Type u) (A : Type v) [Group C] [Finite C] [AddCommGroup A] [DistribMulAction C A]
    (s : C), Subgroup.zpowers s = ⊤ →
    let R := Model.integralRepresentation.{u,v,max u v} C A
    ∃ e : groupCohomology.H1 R ≃+ NormQuotient (A := A) s,
      ∀ c : groupCohomology.cocycles₁ R,
        ∃ a : LinearMap.ker (norm (A := A) s),
          a.val = (c (ULift.up s)).down ∧
          e (groupCohomology.H1π R c) = Submodule.Quotient.mk a

/-- For a cyclic group of order one, both groups in the evaluation formula are trivial. -/
def TrivialGroup : Prop :=
  ∀ (C : Type u) (A : Type v) [Group C] [Finite C] [AddCommGroup A] [DistribMulAction C A]
    (s : C), Subgroup.zpowers s = ⊤ → Nat.card C = 1 →
    let R := Model.integralRepresentation.{u,v,max u v} C A
    Subsingleton (groupCohomology.H1 R) ∧ Subsingleton (NormQuotient (A := A) s)

/-- The power-sum formula determines a cocycle uniquely and reconstructs it exactly for
elements in the kernel of the norm. -/
def CocyclePowerSums : Prop :=
  ∀ (C : Type u) (A : Type v) [Group C] [Finite C] [AddCommGroup A] [DistribMulAction C A]
    (s : C), Subgroup.zpowers s = ⊤ → ∀ a : A,
    norm s a = 0 ↔ ∃! f : C → A,
      f s = a ∧ (∀ g h, f (g * h) = f g + g • f h) ∧
        (∀ n : ℕ, f (s ^ n) = ∑ i ∈ Finset.range n, s ^ i • a)

end Specification
end GaloisFormalization.GH.CyclicDegreeOne
