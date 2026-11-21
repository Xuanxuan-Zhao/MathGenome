import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.List.Pairwise

/-! Ordered-monomial PBW, over an arbitrary commutative coefficient ring.
The index type is unrestricted, and no nontriviality assumption is imposed on k.
The empty list is an index, so the unit is included. -/
namespace Shared.Lie.PBW
universe u v w

abbrev OrderedWord (ι : Type w) [LE ι] := {l : List ι // l.Pairwise (· ≤ ·)}

def emptyWord (ι : Type w) [LE ι] : OrderedWord ι := ⟨[], List.Pairwise.nil⟩
def singletonWord {ι : Type w} [LE ι] (i : ι) : OrderedWord ι :=
  ⟨[i], List.pairwise_singleton _ _⟩

variable {k : Type u} {g : Type v} {ι : Type w}
  [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Product in the actual enveloping quotient, with basis indices as letters. -/
noncomputable def monomial (b : Module.Basis ι k g) (l : List ι) : U k g :=
  word k g (l.map b)

noncomputable def orderedMonomial [LE ι] (b : Module.Basis ι k g) (l : OrderedWord ι) : U k g :=
  monomial b l.val

end Shared.Lie.PBW

namespace Specs.Shared.Lie.PBW
open _root_.Shared.Lie _root_.Shared.Lie.PBW
universe u v w

/-- Full PBW conclusion: a basis, with its values fixed to the ordered products. -/
def orderedBasisExpected : Prop :=
  ∀ (k : Type u) (g : Type v) (ι : Type w) [CommRing k] [LieRing g]
    [LieAlgebra k g] [LinearOrder ι] (b : Module.Basis ι k g),
    ∃ B : Module.Basis (OrderedWord ι) k (U k g), ∀ l, B l = orderedMonomial b l

def injectiveExpected : Prop :=
  ∀ (k : Type u) (g : Type v) (ι : Type w) [CommRing k] [LieRing g]
    [LieAlgebra k g] [LinearOrder ι] (_b : Module.Basis ι k g),
    Function.Injective (inclusion k g)

/-- Intermediate spanning statement; it does not assert linear independence. -/
def spanningExpected : Prop :=
  ∀ (k : Type u) (g : Type v) (ι : Type w) [CommRing k] [LieRing g]
    [LieAlgebra k g] [LinearOrder ι] (b : Module.Basis ι k g),
    Submodule.span k (Set.range (orderedMonomial b)) = ⊤
end Specs.Shared.Lie.PBW
