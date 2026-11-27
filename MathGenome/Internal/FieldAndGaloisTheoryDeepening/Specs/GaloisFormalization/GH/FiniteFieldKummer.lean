import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KummerConnecting
import Mathlib.Algebra.CharP.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace Specs.GaloisFormalization.GH.FiniteFieldKummer

open KummerConnecting (RootCohomology)

universe u v

/-- Over a finite field, continuous degree-one Kummer cohomology with the
natural Galois action is cyclic of order `gcd(m, q - 1)`. -/
def CohomologyCyclicOrder : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Finite k] [Field S] [Algebra k S]
    [IsSepClosure k S] [TopologicalSpace Sˣ] [DiscreteTopology Sˣ]
    {p m : ℕ} [CharP k p], 1 ≤ m → ¬ p ∣ m →
      IsCyclic (RootCohomology k S m) ∧
        Nat.card (RootCohomology k S m) = Nat.gcd m (Nat.card k - 1)

/-- A coprime exponent gives trivial degree-one Kummer cohomology. -/
def CohomologySubsingletonOfGcdEqOne : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Finite k] [Field S] [Algebra k S]
    [IsSepClosure k S] [TopologicalSpace Sˣ] [DiscreteTopology Sˣ]
    {p m : ℕ} [CharP k p], 1 ≤ m → ¬ p ∣ m →
      Nat.gcd m (Nat.card k - 1) = 1 → Subsingleton (RootCohomology k S m)

/-- In particular the cohomology with coefficients in the first roots of unity is trivial. -/
def CohomologyOneSubsingleton : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Finite k] [Field S] [Algebra k S]
    [IsSepClosure k S] [TopologicalSpace Sˣ] [DiscreteTopology Sˣ],
      Subsingleton (RootCohomology k S 1)

end Specs.GaloisFormalization.GH.FiniteFieldKummer
