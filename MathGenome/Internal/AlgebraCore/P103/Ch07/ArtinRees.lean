import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.ArtinRees

namespace P103.Ch07.ArtinRees

/-- Artin–Rees for every submodule of a finite module over a commutative
Noetherian ring, including all zero and whole-object cases. The library
theorem uses the same ideal action and proves the full submodule equality
by stability of the intersection filtration. -/
theorem artin_rees : P103.Specs.Ch07.ArtinRees.artin_reesType := by
  intro R _ _ I M _ _ _ N
  exact I.exists_pow_inf_eq_pow_smul N

end P103.Ch07.ArtinRees
