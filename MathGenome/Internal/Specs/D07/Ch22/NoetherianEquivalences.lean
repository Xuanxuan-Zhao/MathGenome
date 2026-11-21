import MathGenome.Internal.Specs.D07.Ch16.MapsSubmodules
import Mathlib.RingTheory.Noetherian.Defs

/-!
Independent specification for K07.22.noetherian_equivalences,
paper.tex:6944–6972. The chapter's scalars are commutative unital rings,
with the zero ring allowed, and modules are unital left modules.

`Submodule.FG` means existence of a finite set whose span is the given
submodule. In particular no basis, nonzero module, or finite generation
of the ambient module is assumed. Stabilization is eventual equality of
all terms of an arbitrary increasing natural-number-indexed chain.
Maximality is within the given nonempty collection, not in the entire
submodule lattice, and is not a claim of a greatest member.

The canonical predicates `IsNoetherian` and `IsNoetherianRing` are linked
to the displayed source conditions by the characterization statements.
For commutative rings `Ideal R` is exactly a submodule of the regular
module, so its finite generation is ideal finite generation.
-/

universe u v

namespace Specs.D07.Ch22.NoetherianEquivalences

/-- Every increasing sequence is eventually constant. -/
def AscendingChainCondition (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] : Prop :=
  ∀ U : ℕ → Submodule R M, Monotone U →
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → U m = U n

/-- Every nonempty collection has a member maximal under inclusion. -/
def MaximalMemberCondition (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] : Prop :=
  ∀ S : Set (Submodule R M), S.Nonempty →
    ∃ U ∈ S, ∀ V ∈ S, U ≤ V → V = U

def ChainConditionIffFiniteGeneration : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    AscendingChainCondition R M ↔ ∀ U : Submodule R M, U.FG

def FiniteGenerationIffMaximalMember : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    (∀ U : Submodule R M, U.FG) ↔ MaximalMemberCondition R M

/-- The name Noetherian applies precisely to modules satisfying the ACC. -/
def NoetherianCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    IsNoetherian R M ↔ AscendingChainCondition R M

def NoetherianRingRegularModule : Prop :=
  ∀ (R : Type u) [CommRing R], IsNoetherianRing R ↔ IsNoetherian R R

def NoetherianRingIffIdealsFG : Prop :=
  ∀ (R : Type u) [CommRing R],
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG

end Specs.D07.Ch22.NoetherianEquivalences
