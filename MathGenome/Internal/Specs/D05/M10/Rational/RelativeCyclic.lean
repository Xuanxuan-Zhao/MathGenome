import MathGenome.Internal.Specs.D05.M10.InvariantFactors
import MathGenome.Internal.Specs.D05.M10.Cyclic
import MathGenome.Internal.Specs.D05.M06.Invariant

noncomputable section
open Polynomial
open scoped BigOperators
namespace Specs.D05.M10.Rational.RelativeCyclic

/-- Solvability of every polynomial equation with right side in W already in W.
Invariance is a separate hypothesis of the relative decomposition theorems. -/
def admissible_type := ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V],
  Module.End K V → Submodule K V → Prop

def admissible_value : admissible_type := fun K V _ _ _ T W =>
  ∀ (p : K[X]) (v : V), aeval T p v ∈ W →
    ∃ w : W, aeval T p v = aeval T p (w : V)

def admissible_iff_complement : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (W : Submodule K V),
    Specs.D05.M06.Invariant.invariant_value K V W T →
    (admissible_value K V T W ↔ ∃ L : Submodule K V,
      Specs.D05.M06.Invariant.invariant_value K V L T ∧ IsCompl W L)

/-- Actual cyclic spaces, their exact monic annihilators, and the actual summation
isomorphism. The ordered list is the canonical invariant-factor list of V/W. -/
def relative_decomposition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (W : Submodule K V)
    (hW : Specs.D05.M06.Invariant.invariant_value K V W T),
    admissible_value K V T W →
    ∃ (r : ℕ) (d : Fin r → K[X]) (u : Fin r → V),
      (∀ i, (d i).Monic) ∧ (∀ i, 0 < (d i).natDegree) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧
      Specs.D05.M10.InvariantFactors.factors
        (Specs.D05.M06.Invariant.inducedMap_value K V W T hW) = List.ofFn d ∧
      (∀ i, Specs.D05.M10.Cyclic.vectorAnnihilator_value K V T (u i) = d i) ∧
      (∀ i, Specs.D05.M06.Invariant.invariant_value K V
        (Specs.D05.M10.Cyclic.cyclicSpace_value K V T (u i)) T) ∧
      ∃ E : (W × (∀ i, Specs.D05.M10.Cyclic.cyclicSpace_value K V T (u i))) ≃ₗ[K] V,
        ∀ z, E z = (z.1 : V) + ∑ i, (z.2 i : V)

/-- Two relative lists, when identified with the quotient factors, coincide.
No uniqueness of complements or of generators is asserted. -/
def factor_uniqueness : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (W : Submodule K V)
    (hW : Specs.D05.M06.Invariant.invariant_value K V W T)
    {r s : ℕ} (d : Fin r → K[X]) (e : Fin s → K[X]),
    Specs.D05.M10.InvariantFactors.RationalFactors
      (Specs.D05.M06.Invariant.inducedMap_value K V W T hW) d →
    Specs.D05.M10.InvariantFactors.RationalFactors
      (Specs.D05.M06.Invariant.inducedMap_value K V W T hW) e →
    List.ofFn d = List.ofFn e

/-- The boundary case W = V has complement zero and an empty quotient list. -/
def full_subspace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    admissible_value K V T ⊤ ∧ IsCompl (⊤ : Submodule K V) ⊥ ∧
    Specs.D05.M10.InvariantFactors.factors
      (Specs.D05.M06.Invariant.inducedMap_value K V ⊤ T (fun _ _ => trivial)) = []

end Specs.D05.M10.Rational.RelativeCyclic
