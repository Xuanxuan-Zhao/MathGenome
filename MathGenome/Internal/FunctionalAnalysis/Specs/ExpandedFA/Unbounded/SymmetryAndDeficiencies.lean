import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Independent specification for the definitions and norm identity in
paper.tex:13646–13664, the lower-bound convention at 13743–13747, and
normality with exact product domains at 13865–13866.

Predicates include density, since the paper defines these classes on densely
defined operators. Normality is the product equality; closedness remains a
separate hypothesis. Semibounded means bounded on at least one side; the
lower-bound and upper-bound predicates retain their real bound parameter.
Deficiency indices are cardinalities of Hilbert bases, never algebraic ranks
or natural-number finite dimensions. They are defined for every densely
defined operator, without requiring symmetry or finite-dimensionality.
-/

noncomputable section
universe u
namespace ExpandedFA.Unbounded.SymmetryAndDeficienciesSpec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Symmetry, with inclusion of the entire operator domain. -/
def symmetricValue (S : Operator ℂ H H) : Prop :=
  Dense (S.domain : Set H) ∧ S ≤ HilbertAdjointSpec.adjointValue S

/-- Equality here is equality of partial linear maps, including their domains. -/
def selfAdjointValue (S : Operator ℂ H H) : Prop :=
  Dense (S.domain : Set H) ∧ S = HilbertAdjointSpec.adjointValue S

/-- The closure is only asserted to be self-adjoint when it exists as an operator. -/
def essentiallySelfAdjointValue (S : Operator ℂ H H) : Prop :=
  Dense (S.domain : Set H) ∧ S.IsClosable ∧ selfAdjointValue S.closure

/-- Product equality includes both product domains. -/
def normalValue (N : Operator ℂ H H) : Prop :=
  Dense (N.domain : Set H) ∧
    OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue N) N =
      OperatorDomainsSpec.productValue N (HilbertAdjointSpec.adjointValue N)

def boundedBelowValue (S : Operator ℂ H H) (c : ℝ) : Prop :=
  symmetricValue S ∧ ∀ x : S.domain,
    c * ‖(x : H)‖ ^ 2 ≤ (inner ℂ (x : H) (S x)).re

def boundedAboveValue (S : Operator ℂ H H) (c : ℝ) : Prop :=
  symmetricValue S ∧ ∀ x : S.domain,
    (inner ℂ (x : H) (S x)).re ≤ c * ‖(x : H)‖ ^ 2

def semiboundedValue (S : Operator ℂ H H) : Prop :=
  (∃ c : ℝ, boundedBelowValue S c) ∨ (∃ c : ℝ, boundedAboveValue S c)

/-- ker(S* − z) = ker(z I − S*), on exactly D(S*). -/
def deficiencySpaceValue (S : Operator ℂ H H) (z : ℂ) : Submodule ℂ H :=
  (OperatorDomainsSpec.shiftValue z (HilbertAdjointSpec.adjointValue S)).ker

def deficiencyPlusValue (S : Operator ℂ H H) : Submodule ℂ H :=
  deficiencySpaceValue S Complex.I

def deficiencyMinusValue (S : Operator ℂ H H) : Submodule ℂ H :=
  deficiencySpaceValue S (-Complex.I)

/-- Infrastructure for the Hilbert-space dimension: eigenspaces of a closed
adjoint are closed in H, even when the original operator is not closed. -/
theorem deficiencySpace_closed (S : Operator ℂ H H)
    (hS : Dense (S.domain : Set H)) (z : ℂ) :
    _root_.IsClosed (deficiencySpaceValue S z : Set H) := by
  have heq : (deficiencySpaceValue S z : Set H) =
      (fun x : H => (x, z • x)) ⁻¹'
        ((HilbertAdjointSpec.adjointValue S).graph : Set (H × H)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hxy, hy⟩ := LinearPMap.mem_ker_iff.mp hx
      subst x
      refine ((HilbertAdjointSpec.adjointValue S).mem_graph_iff).mpr ⟨y, rfl, ?_⟩
      change z • (y : H) - HilbertAdjointSpec.adjointValue S y = 0 at hy
      exact (sub_eq_zero.mp hy).symm
    · intro hx
      obtain ⟨y, hxy, hy⟩ := ((HilbertAdjointSpec.adjointValue S).mem_graph_iff).mp hx
      apply LinearPMap.mem_ker_iff.mpr
      refine ⟨y, hxy.symm, ?_⟩
      change z • (y : H) - HilbertAdjointSpec.adjointValue S y = 0
      rw [hy, hxy]
      exact sub_self _
  rw [heq]
  exact (LinearPMap.adjoint_isClosed hS).preimage
    (continuous_id.prodMk (continuous_const.smul continuous_id))

/-- A Hilbert dimension is the cardinality of a chosen Hilbert basis.
The choice works in every universe and includes all infinite cardinalities. -/
def hilbertDimensionValue (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] : Cardinal.{u} :=
  Cardinal.mk (exists_hilbertBasis ℂ E).choose

def deficiencyIndexValue (S : Operator ℂ H H)
    (hS : Dense (S.domain : Set H)) (z : ℂ) : Cardinal.{u} := by
  letI : CompleteSpace (deficiencySpaceValue S z) :=
    (deficiencySpace_closed S hS z).isComplete.completeSpace_coe
  exact hilbertDimensionValue (deficiencySpaceValue S z)

def deficiencyIndexPlusValue (S : Operator ℂ H H)
    (hS : Dense (S.domain : Set H)) : Cardinal.{u} :=
  deficiencyIndexValue S hS Complex.I

def deficiencyIndexMinusValue (S : Operator ℂ H H)
    (hS : Dense (S.domain : Set H)) : Cardinal.{u} :=
  deficiencyIndexValue S hS (-Complex.I)

-- Expected declaration types.

def SymmetricTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → Prop

def SelfAdjointTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → Prop

def EssentiallySelfAdjointTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → Prop

def NormalTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → Prop

def BoundedBelowTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → ℝ → Prop

def BoundedAboveTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → ℝ → Prop

def SemiboundedTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → Prop

def DeficiencySpaceTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → ℂ → Submodule ℂ H

def DeficiencyPlusTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → Submodule ℂ H

def DeficiencyMinusTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  Operator ℂ H H → Submodule ℂ H

def HilbertDimensionTypeExpected :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
  Cardinal.{u}

def DeficiencyIndexTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  (S : Operator ℂ H H) → Dense (S.domain : Set H) → ℂ → Cardinal.{u}

def DeficiencyIndexPlusTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  (S : Operator ℂ H H) → Dense (S.domain : Set H) → Cardinal.{u}

def DeficiencyIndexMinusTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  (S : Operator ℂ H H) → Dense (S.domain : Set H) → Cardinal.{u}

def SymmetricLawExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ S : Operator ℂ H H, symmetricValue S ↔ Dense (S.domain : Set H) ∧ S ≤ HilbertAdjointSpec.adjointValue S

def SelfAdjointLawExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ S : Operator ℂ H H, selfAdjointValue S ↔ Dense (S.domain : Set H) ∧ S = HilbertAdjointSpec.adjointValue S

def EssentiallySelfAdjointLawExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ S : Operator ℂ H H, essentiallySelfAdjointValue S ↔ Dense (S.domain : Set H) ∧
    ∃ h : S.IsClosable, selfAdjointValue (OperatorDomainsSpec.closureValue S h)

def NormalLawExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ N : Operator ℂ H H, normalValue N ↔ Dense (N.domain : Set H) ∧
    OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue N) N = OperatorDomainsSpec.productValue N (HilbertAdjointSpec.adjointValue N)

def BoundedBelowLawExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (S : Operator ℂ H H) (c : ℝ), boundedBelowValue S c ↔ symmetricValue S ∧
    ∀ x : S.domain, c * ‖(x : H)‖ ^ 2 ≤ (inner ℂ (x : H) (S x)).re

def BoundedAboveLawExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (S : Operator ℂ H H) (c : ℝ), boundedAboveValue S c ↔ symmetricValue S ∧
    ∀ x : S.domain, (inner ℂ (x : H) (S x)).re ≤ c * ‖(x : H)‖ ^ 2

def SemiboundedLawExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ S : Operator ℂ H H, semiboundedValue S ↔
    (∃ c : ℝ, boundedBelowValue S c) ∨ (∃ c : ℝ, boundedAboveValue S c)

def SymmetricInnerExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ {S : Operator ℂ H H}, symmetricValue S → ∀ x y : S.domain,
    inner ℂ (S x) (y : H) = inner ℂ (x : H) (S y)

def SymmetricClosableExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ {S : Operator ℂ H H}, symmetricValue S → S.IsClosable

def SymmetricRealQuadraticExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ {S : Operator ℂ H H}, symmetricValue S → ∀ x : S.domain,
    (inner ℂ (S x) (x : H)).im = 0

def DeficiencySpaceMembershipExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (S : Operator ℂ H H) (z : ℂ) (y : H),
    y ∈ deficiencySpaceValue S z ↔ ∃ hy : y ∈ (HilbertAdjointSpec.adjointValue S).domain,
      HilbertAdjointSpec.adjointValue S ⟨y, hy⟩ = z • y

def DeficiencyPlusMembershipExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (S : Operator ℂ H H) (y : H),
    y ∈ deficiencyPlusValue S ↔ ∃ hy : y ∈ (HilbertAdjointSpec.adjointValue S).domain,
      HilbertAdjointSpec.adjointValue S ⟨y, hy⟩ = Complex.I • y

def DeficiencyMinusMembershipExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (S : Operator ℂ H H) (y : H),
    y ∈ deficiencyMinusValue S ↔ ∃ hy : y ∈ (HilbertAdjointSpec.adjointValue S).domain,
      HilbertAdjointSpec.adjointValue S ⟨y, hy⟩ = (-Complex.I) • y

def DeficiencySpaceClosedExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (S : Operator ℂ H H), Dense (S.domain : Set H) → ∀ z : ℂ,
    _root_.IsClosed (deficiencySpaceValue S z : Set H)

def HilbertDimensionBasisExpected : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
  ∃ (w : Set E) (_b : HilbertBasis w ℂ E),
    hilbertDimensionValue E = Cardinal.mk w

def DeficiencyIndexBasisExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (S : Operator ℂ H H) (hS : Dense (S.domain : Set H)) (z : ℂ),
    ∃ (w : Set (deficiencySpaceValue S z))
      (_b : HilbertBasis w ℂ (deficiencySpaceValue S z)),
      deficiencyIndexValue S hS z = Cardinal.mk w

def SymmetricNormIdentityExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ {S : Operator ℂ H H}, symmetricValue S → ∀ (z : ℂ) (x : S.domain),
    ‖S x - z • (x : H)‖ ^ 2 =
      ‖S x - (z.re : ℂ) • (x : H)‖ ^ 2 + |z.im| ^ 2 * ‖(x : H)‖ ^ 2

def NormIdentityExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (S : Operator ℂ H H), S.IsClosed → symmetricValue S → ∀ (z : ℂ) (x : S.domain),
    ‖S x - z • (x : H)‖ ^ 2 =
      ‖S x - (z.re : ℂ) • (x : H)‖ ^ 2 + |z.im| ^ 2 * ‖(x : H)‖ ^ 2

end ExpandedFA.Unbounded.SymmetryAndDeficienciesSpec
