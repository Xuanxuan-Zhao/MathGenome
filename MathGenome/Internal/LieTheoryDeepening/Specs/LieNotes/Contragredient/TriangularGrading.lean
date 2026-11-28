import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.Presentation
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.WeightExtraction
import Mathlib.Algebra.Lie.Graded
import Mathlib.Algebra.Lie.OfAssociative

/-! The triangular decomposition and the root-lattice grading of the presented algebra. -/

namespace Specs.LieNotes.Contragredient.TriangularGrading

open CartanData Presentation WeightExtraction
open scoped DirectSum

noncomputable section

universe u v

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The linear family of adjoints of elements of the Cartan space. -/
def cartanAdjoint (R : Realization A H) : H →ₗ[ℂ] Module.End ℂ (Algebra R) :=
  (LieModule.toEnd ℂ (Algebra R) (Algebra R)).toLinearMap.comp (cartan R)

/-- The degree-`q` component is the full common eigenspace of the lattice weight of `q`. -/
def grade (R : Realization A H) (q : Q I) : Submodule ℂ (Algebra R) :=
  weightSpace (cartanAdjoint R) (R.rootWeight q)

/-- The sum map on the negative side, Cartan space, and positive side. -/
def triangularAdd (R : Realization A H) :
    (negative R × H × positive R) →ₗ[ℂ] Algebra R :=
  (negative R).toSubmodule.subtype.coprod
    ((cartan R).coprod (positive R).toSubmodule.subtype)

set_option linter.checkUnivs false

def CartanAdjointType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      H →ₗ[ℂ] Module.End ℂ (Algebra R)

def GradeType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      Q I → Submodule ℂ (Algebra R)

def TriangularAddType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      (negative R × H × positive R) →ₗ[ℂ] Algebra R

def CartanAdjointApply : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∀ (h : H) (x : Algebra R), cartanAdjoint R h x = ⁅cartan R h, x⁆

def MemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∀ {q : Q I} {x : Algebra R},
        x ∈ grade R q ↔ ∀ h : H, ⁅cartan R h, x⁆ = R.rootWeight q h • x

def CartanMemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∀ h : H, cartan R h ∈ grade R 0

def EMemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∀ i : I, e R i ∈ grade R (simpleDegree i)

def FMemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∀ i : I, f R i ∈ grade R (-simpleDegree i)

def LieMemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∀ {q p : Q I} {x y : Algebra R},
        x ∈ grade R q → y ∈ grade R p → ⁅x, y⁆ ∈ grade R (q + p)

def GradeIsInternal : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    [DecidableEq (Q I)]
    (R : Realization A H),
      DirectSum.IsInternal (grade R)

def GradeAdditionEquiv : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    [DecidableEq (Q I)]
    (R : Realization A H),
      ∃ E : (⨁ q, grade R q) ≃ₗ[ℂ] Algebra R,
        E.toLinearMap = DirectSum.coeLinearMap (grade R)

def WeightSpaceEqBotOfNotMemRange : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∀ μ : Module.Dual ℂ H, μ ∉ Set.range R.rootWeight →
        weightSpace (cartanAdjoint R) μ = ⊥

def GradeZero : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      grade R 0 = (cartan R).range

def ISupPositiveGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      (⨆ q, ⨆ (_ : PositiveDegree q), grade R q) = (positive R).toSubmodule

def ISupNegativeGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      (⨆ q, ⨆ (_ : NegativeDegree q), grade R q) = (negative R).toSubmodule

def GradeEqBotOfNotPositiveOrNegative : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∀ q : Q I, q ≠ 0 → ¬ PositiveDegree q → ¬ NegativeDegree q → grade R q = ⊥

def TriangularAddApply : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∀ (x : negative R) (h : H) (y : positive R),
        triangularAdd R (x, h, y) = (x : Algebra R) + (cartan R h + (y : Algebra R))

def TriangularAddBijective : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      Function.Bijective (triangularAdd R)

def TriangularAdditionEquiv : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
      ∃ E : (negative R × H × positive R) ≃ₗ[ℂ] Algebra R,
        E.toLinearMap = triangularAdd R

end

end Specs.LieNotes.Contragredient.TriangularGrading
