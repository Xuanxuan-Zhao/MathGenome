import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies

/-! Independent statements for the range criterion in paper.tex:13646–13673.
The shared shift is zI − S on D(S). Its range equals that of S − zI,
since multiplication by −1 does not change a linear subspace. In particular,
shift (−i) represents Ran(S+i), and shift i represents Ran(S−i).
Density is included in the shared symmetry and self-adjointness predicates.
-/
noncomputable section
universe u
namespace ExpandedFA.Unbounded.SelfAdjointRangeCriterionSpec
open OperatorDomainsSpec HilbertAdjointSpec SymmetryAndDeficienciesSpec

/-- Explicit bridge to the source's S−z notation, on exactly D(S). -/
def ShiftRangeBridgeExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H) (z : ℂ),
      rangeValue (shiftValue z S) = (S.toFun - z • S.domain.subtype).range

def NonrealLowerBoundExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : Operator ℂ H H}, symmetricValue S → ∀ (z : ℂ) (x : S.domain),
      |z.im| * ‖(x : H)‖ ≤ ‖S x - z • (x : H)‖

def ShiftRangeOrthogonalExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), Dense (S.domain : Set H) → ∀ z : ℂ,
      (rangeValue (shiftValue z S)).orthogonal = deficiencySpaceValue S (starRingEnd ℂ z)

def NonrealRangeClosedExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
      ∀ z : ℂ, z.im ≠ 0 → _root_.IsClosed (rangeValue (shiftValue z S) : Set H)

def NonrealRangeExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
      ∀ z : ℂ, z.im ≠ 0 →
        rangeValue (shiftValue z S) = (deficiencySpaceValue S (starRingEnd ℂ z)).orthogonal

def SignedRangesExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
      rangeValue (shiftValue (-Complex.I) S) = (deficiencyPlusValue S).orthogonal ∧
      rangeValue (shiftValue Complex.I S) = (deficiencyMinusValue S).orthogonal

def SelfAdjointRangesExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
      (selfAdjointValue S ↔
        rangeValue (shiftValue (-Complex.I) S) = ⊤ ∧ rangeValue (shiftValue Complex.I S) = ⊤)

def SelfAdjointDeficienciesExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
      (selfAdjointValue S ↔ deficiencyPlusValue S = ⊥ ∧ deficiencyMinusValue S = ⊥)

end ExpandedFA.Unbounded.SelfAdjointRangeCriterionSpec
