import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeylChambersLength
import Mathlib.Algebra.BigOperators.Finprod

/-! The Weyl-group and half-sum assertions of res:E08, source lines 2409–2446.
The assertions concerning weights of Lie-algebra modules belong to the separate
finite-weight-set obligation. A positive system is the one specified by a
regular vector, as in res:E02. -/
noncomputable section
namespace LieAlgebrasAndRepresentations
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Half the sum of the positive roots. For a root system the indexing set is finite. -/
def rootRho (R : Set E) (v : E) : E :=
  (1 / 2 : ℝ) • ∑ᶠ a ∈ positiveRoots R v, a

/-- Half the sum of the coroots of the positive roots. -/
def corootRho (R : Set E) (v : E) : E :=
  (1 / 2 : ℝ) • ∑ᶠ a ∈ positiveRoots R v, coroot a

/-- The source's characterization of the longest Weyl element. -/
def IsLongestWeylElement (R : Set E) (v : E) (w : rootWeylGroup R) : Prop :=
  w.val '' positiveRoots R v = Neg.neg '' positiveRoots R v

namespace LongestElementRhoSpecs
universe u

def rhoType : Type (u + 1) :=
  {E : Type u} → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] → Set E → E → E

def rhoValue : rhoType := @rootRho

def corootRhoValue : rhoType := @corootRho

def existenceType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
    ∃! w : rootWeylGroup R, IsLongestWeylElement R v w

def involutionType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ w : rootWeylGroup R, IsLongestWeylElement R v w → w * w = 1

def lengthType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ w : rootWeylGroup R, IsLongestWeylElement R v w →
    weylWordLength R v w = (positiveRoots R v).ncard

def rhoPairingType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ a ∈ simpleRoots R v, inner ℝ (rootRho R v) (coroot a) = 1

def corootRhoPairingType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ a ∈ simpleRoots R v, inner ℝ a (corootRho R v) = 1

/-- The empty system has identity longest element and both half-sums vanish. -/
def emptyType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ v : E, IsLongestWeylElement (∅ : Set E) v 1 ∧
    rootRho (∅ : Set E) v = 0 ∧ corootRho (∅ : Set E) v = 0

end LongestElementRhoSpecs
end LieAlgebrasAndRepresentations
