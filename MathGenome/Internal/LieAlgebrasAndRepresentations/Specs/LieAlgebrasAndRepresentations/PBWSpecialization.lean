import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Enveloping
import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.PBWGraded

/-! Independent statements for LA A05, ordered and graded PBW.
The objects are the same tensor quotient and canonical Lie map as in LA A04.
The basis index has arbitrary cardinality; the empty word includes the unit.
The characteristic-zero symmetrization assertion is allocated to LA-A05-Sym.
-/
namespace Specs.LieAlgebrasAndRepresentations.PBW
open _root_.Shared.Lie _root_.Shared.Lie.PBW _root_.Shared.Lie.PBW.Graded
universe u v w

/-- The ordered products, including the empty product, are an actual basis. -/
def orderedBasisExpected : Prop :=
  ∀ (k : Type u) (g : Type v) (ι : Type w) [Field k] [LieRing g]
    [LieAlgebra k g] [LinearOrder ι] (b : Module.Basis ι k g),
    ∃ B : Module.Basis (OrderedWord ι) k (U k g),
      (∀ l, B l = orderedMonomial b l) ∧
      B (emptyWord ι) = 1 ∧
      ∀ i, B (singletonWord i) = inclusion k g (b i)

/-- Injectivity of the canonical map, with no characteristic restriction. -/
def inclusionInjectiveExpected : Prop :=
  ∀ (k : Type u) (g : Type v) (ι : Type w) [Field k] [LieRing g]
    [LieAlgebra k g] [LinearOrder ι] (_b : Module.Basis ι k g),
    Function.Injective (inclusion k g)

/-- The word filtration is exactly the length filtration of the ordered basis. -/
def filteredBasisExpected : Prop :=
  ∀ (k : Type u) (g : Type v) (ι : Type w) [Field k] [LieRing g]
    [LieAlgebra k g] [LinearOrder ι] (b : Module.Basis ι k g) (m : ℤ),
    filtration k g m = boundedSpan b m

/-- The natural map is an algebra isomorphism preserving each homogeneous
component in both directions. Its generator values are principal symbols,
and its monomial values agree with the graded ordered basis. The filtration
certificate (including exhaustivity and vanishing in negative degrees) is
part of the conclusion, not an added assumption. -/
def gradedExpected : Prop :=
  ∀ (k : Type u) (g : Type v) (ι : Type w) [Field k] [LieRing g]
    [LieAlgebra k g] [LinearOrder ι] (b : Module.Basis ι k g),
    ∃ hf : _root_.Specs.Shared.Lie.filtrationType k g,
      letI : Fact (_root_.Specs.Shared.Lie.filtrationType k g) := ⟨hf⟩
      ∃ e : SymmetricAlgebra k g ≃ₐ[k] Associated k g,
        e.toAlgHom = canonicalMap (k := k) (g := g) ∧
        (∀ x : g, e (SymmetricAlgebra.ι k g x) = generator (k := k) (g := g) x) ∧
        (∀ n : ℕ, Submodule.map e.toLinearMap (symmetricDegree (k := k) (g := g) n) =
          LinearMap.range (DirectSum.lof k ℕ (Piece k g) n)) ∧
        ∃ B : Module.Basis (OrderedWord ι) k (Associated k g),
          ∀ l, B l = gradedWord b l ∧ e (symmetricWord (l.val.map b)) = B l

end Specs.LieAlgebrasAndRepresentations.PBW
