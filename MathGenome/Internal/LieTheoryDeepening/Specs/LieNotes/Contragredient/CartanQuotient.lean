import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.TriangularGrading

/-! The Cartan-disjoint ideal and the inherited structure on the canonical quotient. -/

namespace Specs.LieNotes.Contragredient.CartanQuotient

open CartanData WeightExtraction
open scoped DirectSum

noncomputable section

set_option linter.checkUnivs false

universe u v

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]

/-- The sum of the ideals that meet the presented Cartan subspace trivially. -/
def cartanDisjointIdeal (R : Realization A H) : LieIdeal ℂ (Presentation.Algebra R) :=
  ⨆ (J : LieIdeal ℂ (Presentation.Algebra R))
    (_ : Disjoint J.toSubmodule (Presentation.cartan R).range), J

/-- The contragredient Lie algebra of the given realization. -/
abbrev Algebra (R : Realization A H) := Presentation.Algebra R ⧸ cartanDisjointIdeal R

def quotientMap (R : Realization A H) : Presentation.Algebra R →ₗ⁅ℂ⁆ Algebra R :=
  { (cartanDisjointIdeal R).toSubmodule.mkQ with
    map_lie' := fun {_ _} => rfl }

def cartan (R : Realization A H) : H →ₗ[ℂ] Algebra R :=
  (quotientMap R).toLinearMap.comp (Presentation.cartan R)

def e (R : Realization A H) (i : I) : Algebra R := quotientMap R (Presentation.e R i)

def f (R : Realization A H) (i : I) : Algebra R := quotientMap R (Presentation.f R i)

def negative (R : Realization A H) : LieSubalgebra ℂ (Algebra R) :=
  (Presentation.negative R).map (quotientMap R)

def positive (R : Realization A H) : LieSubalgebra ℂ (Algebra R) :=
  (Presentation.positive R).map (quotientMap R)

attribute [local instance 100] LieRing.ofAssociativeRing in
def cartanAdjoint (R : Realization A H) : H →ₗ[ℂ] Module.End ℂ (Algebra R) :=
  (LieModule.toEnd ℂ (Algebra R) (Algebra R)).toLinearMap.comp (cartan R)

/-- The full adjoint weight space for the degree `q` in the quotient. -/
def grade (R : Realization A H) (q : Q I) : Submodule ℂ (Algebra R) :=
  weightSpace (cartanAdjoint R) (R.rootWeight q)

/-- Addition of the three triangular components, using the original Cartan space. -/
def triangularAdd (R : Realization A H) :
    (negative R × H × positive R) →ₗ[ℂ] Algebra R :=
  (negative R).toSubmodule.subtype.coprod
    ((cartan R).coprod (positive R).toSubmodule.subtype)

def CartanDisjointIdealType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), LieIdeal ℂ (Presentation.Algebra R)

def AlgebraType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    Realization A H → Type (max u v)

def QuotientMapType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), Presentation.Algebra R →ₗ⁅ℂ⁆ Algebra R

def CartanType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), H →ₗ[ℂ] Algebra R

def SimpleGeneratorType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), I → Algebra R

def SideType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), LieSubalgebra ℂ (Algebra R)

def CartanAdjointType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), H →ₗ[ℂ] Module.End ℂ (Algebra R)

def GradeType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), Q I → Submodule ℂ (Algebra R)

def TriangularAddType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), (negative R × H × positive R) →ₗ[ℂ] Algebra R

def CartanDisjointIdealIsGreatest : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    IsGreatest {J : LieIdeal ℂ (Presentation.Algebra R) |
      Disjoint J.toSubmodule (Presentation.cartan R).range} (cartanDisjointIdeal R)

def QuotientMapSurjective : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), Function.Surjective (quotientMap R)

def QuotientMapKer : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), (quotientMap R).ker = cartanDisjointIdeal R

def CartanInjective : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), Function.Injective (cartan R)

def DefiningRelations : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), Presentation.Relations R (cartan R) (e R) (f R)

def ENeZero : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (i : I), e R i ≠ 0

def FNeZero : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (i : I), f R i ≠ 0

def Generated : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    LieSubalgebra.lieSpan ℂ (Algebra R) (Set.range (cartan R) ∪ Set.range (e R) ∪ Set.range (f R)) = ⊤

def GradeEqMap : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (q : Q I),
    grade R q = (TriangularGrading.grade R q).map (quotientMap R).toLinearMap

def MemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) {q : Q I} {x : Algebra R},
    x ∈ grade R q ↔ ∀ h : H, ⁅cartan R h, x⁆ = R.rootWeight q h • x

def CartanMemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (h : H), cartan R h ∈ grade R 0

def EMemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (i : I), e R i ∈ grade R (simpleDegree i)

def FMemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (i : I), f R i ∈ grade R (-simpleDegree i)

def LieMemGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) {q p : Q I} {x y : Algebra R},
    x ∈ grade R q → y ∈ grade R p → ⁅x, y⁆ ∈ grade R (q + p)

def GradeIsInternal : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    [DecidableEq (Q I)] (R : Realization A H), DirectSum.IsInternal (grade R)

def WeightSpaceEqBotOfNotMemRange : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (μ : Module.Dual ℂ H),
    μ ∉ Set.range R.rootWeight → weightSpace (cartanAdjoint R) μ = ⊥

def GradeZero : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), grade R 0 = (cartan R).range

def ISupNegativeGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    (⨆ q, ⨆ (_ : NegativeDegree q), grade R q) = (negative R).toSubmodule

def ISupPositiveGrade : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    (⨆ q, ⨆ (_ : PositiveDegree q), grade R q) = (positive R).toSubmodule

def GradeEqBotOfNotPositiveOrNegative : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (q : Q I),
    q ≠ 0 → ¬ PositiveDegree q → ¬ NegativeDegree q → grade R q = ⊥

def TriangularAddBijective : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), Function.Bijective (triangularAdd R)

def EqBotOfDisjointCartan : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (J : LieIdeal ℂ (Algebra R)),
    Disjoint J.toSubmodule (cartan R).range → J = ⊥

/-- Every presented interchange induces an involutive automorphism on the canonical
quotient, with commutation on the entire presented algebra. -/
def InterchangeDescends : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (σ : Presentation.Algebra R ≃ₗ⁅ℂ⁆ Presentation.Algebra R),
    Presentation.IsInterchange R σ →
    ∃ τ : Algebra R ≃ₗ⁅ℂ⁆ Algebra R,
      Function.Involutive τ ∧ ∀ x, τ (quotientMap R x) = quotientMap R (σ x)

/-- The descended interchange acts on the embedded Cartan and simple generators. -/
def HasInterchange : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    ∃ τ : Algebra R ≃ₗ⁅ℂ⁆ Algebra R,
      Function.Involutive τ ∧
      (∀ h, τ (cartan R h) = -cartan R h) ∧
      (∀ i, τ (e R i) = f R i) ∧
      (∀ i, τ (f R i) = e R i)

end

end Specs.LieNotes.Contragredient.CartanQuotient
