import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanQuotient
import Mathlib.Algebra.Lie.Abelian

/-! The center and the structural properties of the canonical contragredient quotient. -/

namespace Specs.LieNotes.Contragredient.Center

open CartanData CartanQuotient

universe u v

/-- The center is the image of the common kernel of the simple roots under the Cartan map. -/
def CenterEqMapCommonKernel : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    (LieAlgebra.center ℂ (Algebra R)).toSubmodule =
      (⨅ i, LinearMap.ker (R.α i)).map (cartan R)

/-- For a minimal realization the center has dimension equal to the corank of the matrix. -/
def MinimalRealizationCenterFinrank : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Fintype I]
    (R : Realization A H), R.IsMinimal →
    Module.finrank ℂ (LieAlgebra.center ℂ (Algebra R)) =
      Fintype.card I - (A.map fun a : ℤ => (a : ℂ)).rank

/-- The largest Cartan-disjoint ideal, the inherited decomposition and grading, the center,
and the absence of nonzero Cartan-disjoint ideals in its quotient. -/
def CartanDisjointIdealAndCenter : Prop :=
  CartanDisjointIdealIsGreatest.{u, v} ∧
    CartanInjective.{u, v} ∧ TriangularAddBijective.{u, v} ∧
    GradeEqMap.{u, v} ∧ GradeIsInternal.{u, v} ∧ LieMemGrade.{u, v} ∧ GradeZero.{u, v} ∧
    ISupNegativeGrade.{u, v} ∧ ISupPositiveGrade.{u, v} ∧
    CenterEqMapCommonKernel.{u, v} ∧ MinimalRealizationCenterFinrank.{u, v} ∧
    EqBotOfDisjointCartan.{u, v}

end Specs.LieNotes.Contragredient.Center
