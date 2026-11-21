import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.DeficiencyGraphDecomposition
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SelfAdjointRangeCriterion

/-!
Von Neumann's extension theorem, paper.tex:13687–13724. A parameter consists
of an actual closed subspace of N₊ and a complex linear isometry into N₋.
The operator is the restriction of S* to the prescribed domain, not a formal
expression. Hilbert dimensions are the upstream cardinal dimensions, with no
separability or finite-dimensionality assumption. The graph decomposition and
half-plane constancy are separately allocated results.
-/
noncomputable section
universe u
namespace ExpandedFA.Unbounded.ClosedSymmetricExtensionsSpec
open HilbertAdjointSpec SymmetryAndDeficienciesSpec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The data L₊ and W; no operator-extension conclusion is assumed. -/
structure ExtensionParameter (S : Operator ℂ H H) where
  initialSpace : Submodule ℂ (deficiencyPlusValue S)
  closed_initialSpace : _root_.IsClosed (initialSpace : Set (deficiencyPlusValue S))
  isometry : initialSpace →ₗᵢ[ℂ] deficiencyMinusValue S

/-- u ↦ u + Wu, as an ambient-H linear map. -/
def boundaryMap (S : Operator ℂ H H) (p : ExtensionParameter S) :
    p.initialSpace →ₗ[ℂ] H :=
  (deficiencyPlusValue S).subtype.comp p.initialSpace.subtype +
    (deficiencyMinusValue S).subtype.comp p.isometry.toLinearMap

/-- Exactly D(S) + {u+Wu}; directness is a theorem, not an input. -/
def extensionDomain (S : Operator ℂ H H) (p : ExtensionParameter S) : Submodule ℂ H :=
  S.domain ⊔ (boundaryMap S p).range

/-- Restriction also makes sense away from symmetric S; exact domain semantics
are asserted below under the source hypotheses. -/
def extensionValue (S : Operator ℂ H H) (p : ExtensionParameter S) : Operator ℂ H H :=
  (adjointValue S).domRestrict (extensionDomain S p)

def ExtensionTypeExpected :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), ExtensionParameter S → Operator ℂ H H

def DomainExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
    ∀ p : ExtensionParameter S,
      (extensionValue S p).domain = extensionDomain S p ∧
      Disjoint S.domain (boundaryMap S p).range ∧ Function.Injective (boundaryMap S p)

def ActionExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
    ∀ (p : ExtensionParameter S) (x : S.domain) (u : p.initialSpace),
      ((x : H) + ((u : deficiencyPlusValue S) : H) + (p.isometry u : H),
        S x + Complex.I • ((u : deficiencyPlusValue S) : H) -
          Complex.I • (p.isometry u : H)) ∈ (extensionValue S p).graph

def ConstructionExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
    ∀ p : ExtensionParameter S,
      (extensionValue S p).IsClosed ∧ symmetricValue (extensionValue S p) ∧
      S ≤ extensionValue S p ∧ extensionValue S p ≤ adjointValue S

/-- Existence and uniqueness of the full parameter, including L₊ and W. -/
def ClassificationExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
    ∀ T : Operator ℂ H H, T.IsClosed → symmetricValue T → S ≤ T →
      ∃! p : ExtensionParameter S, extensionValue S p = T

def SelfAdjointExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → symmetricValue S →
    ∀ p : ExtensionParameter S,
      selfAdjointValue (extensionValue S p) ↔
        p.initialSpace = ⊤ ∧ Function.Surjective p.isometry

def ExistenceExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H) (_hc : S.IsClosed) (hS : symmetricValue S),
      (∃ T : Operator ℂ H H, S ≤ T ∧ selfAdjointValue T) ↔
        deficiencyIndexPlusValue S hS.1 = deficiencyIndexMinusValue S hS.1

end ExpandedFA.Unbounded.ClosedSymmetricExtensionsSpec
