import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.GradedComparison
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.DegreeOneConverse

/-! RK-11, separated converse and the local equivalences.
Separation uses the ideal of the whole list on every proper prefix quotient. -/
universe u v
namespace AdvCommAlg.RegularSequence.QuasiRegularConverse
open GradedComparison.Core

/-- The successive modules in RK-11 are separated for the ideal of the entire list. -/
def PrefixSeparated {R : Type u} [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (x : List R) : Prop :=
  ∀ j : ℕ, j < x.length →
    (⨅ n : ℕ, sequenceIdeal x ^ n •
      (⊤ : Submodule R (M ⧸ (Ideal.ofList (x.take j) • ⊤ : Submodule R M)))) = ⊥

namespace Specs

def separated_converseType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R), QuasiRegular M x → PrefixSeparated M x →
    RingTheory.Sequence.IsRegular M x

def local_equivalencesType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : List R), (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) →
    (QuasiRegular M x ↔ RingTheory.Sequence.IsRegular M x) ∧
    (QuasiRegular M x ↔ ∀ q : ℕ, 0 < q → Subsingleton (_root_.AdvCommAlg.Koszul.homology M x q)) ∧
    (QuasiRegular M x ↔ Subsingleton (_root_.AdvCommAlg.Koszul.homology M x 1))

end Specs
end AdvCommAlg.RegularSequence.QuasiRegularConverse
