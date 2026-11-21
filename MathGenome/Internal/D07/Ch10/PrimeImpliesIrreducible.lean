import MathGenome.Internal.Specs.D07.Ch10.PrimeImpliesIrreducible

/-! Prime implies irreducible, K07.10.prime_implies_irreducible. -/

universe u

namespace D07.Ch10.PrimeImpliesIrreducible

/-- Primality and cancellation force one factor in every factorization to be a unit. -/
theorem primeImpliesIrreducible :
    Specs.D07.Ch10.PrimeImpliesIrreducible.PrimeIsIrreducible.{u} := by
  intro R _ _ p hp
  exact hp.irreducible

end D07.Ch10.PrimeImpliesIrreducible
