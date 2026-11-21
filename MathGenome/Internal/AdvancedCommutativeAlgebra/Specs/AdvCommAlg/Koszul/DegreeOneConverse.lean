import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions

/-! RK-08, paper.tex:2281–2298. Vanishing means that the actual Koszul
homology module is subsingleton. The general converse includes the zero
module and empty list; proper regularity additionally assumes a nonzero module. -/

universe u v
namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

def degreeOneConverse : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M]
    (x : List R), (∀ a ∈ x, a ∈ (⊥ : Ideal R).jacobson) →
    Subsingleton (homology M x 1) → RingTheory.Sequence.IsWeaklyRegular M x

def degreeOneConverseRegular : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [IsNoetherianRing R]
    [Module.Finite R M] [Nontrivial M]
    (x : List R), (∀ a ∈ x, a ∈ (⊥ : Ideal R).jacobson) →
    Subsingleton (homology M x 1) → RingTheory.Sequence.IsRegular M x

def localRegularityEquivalences : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] [Nontrivial M]
    (x : List R), (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) →
    (RingTheory.Sequence.IsRegular M x ↔
      ∀ q : ℕ, 0 < q → Subsingleton (homology M x q)) ∧
    ((∀ q : ℕ, 0 < q → Subsingleton (homology M x q)) ↔
      Subsingleton (homology M x 1))

end Specs.AdvCommAlg.Koszul
