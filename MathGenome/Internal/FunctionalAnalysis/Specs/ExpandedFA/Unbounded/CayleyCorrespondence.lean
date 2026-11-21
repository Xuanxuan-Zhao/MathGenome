import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SelfAdjointRangeCriterion
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! The Cayley correspondence, paper.tex:13656–13688. A unitary is represented
by a surjective complex linear isometry. The equations below specify the
fractions without applying an inverse outside its exact range. -/
noncomputable section
universe u
namespace ExpandedFA.Unbounded.CayleyCorrespondenceSpec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def plus (S : Operator ℂ H H) : S.domain →ₗ[ℂ] H :=
  S.toFun + Complex.I • S.domain.subtype

def minus (S : Operator ℂ H H) : S.domain →ₗ[ℂ] H :=
  S.toFun - Complex.I • S.domain.subtype

/-- Equivalent to ker(I−U)=0. -/
def NoFixedVectors (U : H ≃ₗᵢ[ℂ] H) : Prop := ∀ x, U x = x → x = 0

def Pair (S : Operator ℂ H H) (U : H ≃ₗᵢ[ℂ] H) : Prop :=
  ∀ x : S.domain, U (plus S x) = minus S x

def SelfAdjointOperators (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :=
  {S : Operator ℂ H H // SymmetryAndDeficienciesSpec.selfAdjointValue S}

def UnitariesWithoutFixedVectors (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] := {U : H ≃ₗᵢ[ℂ] H // NoFixedVectors U}

def NoFixedVectorsKernelExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H ≃ₗᵢ[ℂ] H), NoFixedVectors U ↔ (LinearMap.id - U.toLinearMap).ker = ⊥

def PartialExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → SymmetryAndDeficienciesSpec.symmetricValue S →
    _root_.IsClosed ((plus S).range : Set H) ∧
    _root_.IsClosed ((minus S).range : Set H) ∧
    (plus S).range = (SymmetryAndDeficienciesSpec.deficiencyPlusValue S).orthogonal ∧
    (minus S).range = (SymmetryAndDeficienciesSpec.deficiencyMinusValue S).orthogonal ∧
    ∃ V : (plus S).range ≃ₗᵢ[ℂ] (minus S).range,
      ∀ x : S.domain, V ⟨plus S x, ⟨x, rfl⟩⟩ = ⟨minus S x, ⟨x, rfl⟩⟩

def InverseExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H ≃ₗᵢ[ℂ] H), NoFixedVectors U →
    ∃ S : Operator ℂ H H, SymmetryAndDeficienciesSpec.selfAdjointValue S ∧ Pair S U

/-- Inverse formula with its exact domain, including all vectors in the range. -/
def InverseFormulaExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H) (U : H ≃ₗᵢ[ℂ] H),
    SymmetryAndDeficienciesSpec.selfAdjointValue S → Pair S U →
    S.domain = (LinearMap.id - U.toLinearMap).range ∧
    ∀ x : H, (x - U x, Complex.I • (x + U x)) ∈ S.graph

def CorrespondenceExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∃ e : SelfAdjointOperators H ≃ UnitariesWithoutFixedVectors H,
      (∀ S, Pair S.val (e S).val) ∧
      ∀ U, (e.symm U).val.domain = (LinearMap.id - U.val.toLinearMap).range ∧
        ∀ x : H, (x - U.val x, Complex.I • (x + U.val x)) ∈ (e.symm U).val.graph
end ExpandedFA.Unbounded.CayleyCorrespondenceSpec
