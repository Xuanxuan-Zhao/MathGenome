import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeylChambersLength

/-! LA-E03, res:E03, lines 2085–2142: the closed chamber and its fundamental
 domain property. All ambient vectors are real; no regularity is required of
 the orbit point. In particular the definitions include rank zero. -/
noncomputable section
namespace LieAlgebrasAndRepresentations
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed positive chamber for the specified simple system. -/
def closedSimpleChamber (R : Set E) (v : E) : Set E :=
  {x | ∀ a ∈ simpleRoots R v, 0 ≤ inner ℝ x a}

/-- Finite nonnegative real combinations of the specified simple roots. -/
def simpleRootCone (R : Set E) (v : E) : Set E :=
  {x | ∃ c : simpleRoots R v →₀ ℝ, (∀ i, 0 ≤ c i) ∧
    Finsupp.linearCombination ℝ (fun i : simpleRoots R v => (i : E)) c = x}

namespace DominantFundamentalDomainSpecs
universe u

def closureType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
    closure (simpleChamber R v) = closedSimpleChamber R v

def dominantDifferenceType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ x ∈ closedSimpleChamber R v, ∀ w : rootWeylGroup R,
    x - w.val x ∈ simpleRootCone R v

def fundamentalDomainType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → ∀ v, RootRegular R v → ∀ x : E,
    ∃! y : E, y ∈ closedSimpleChamber R v ∧ ∃ w : rootWeylGroup R, w.val x = y

end DominantFundamentalDomainSpecs
end LieAlgebrasAndRepresentations
