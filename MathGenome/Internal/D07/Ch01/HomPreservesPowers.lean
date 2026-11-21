import MathGenome.Internal.D07.Ch01.HomomorphismDefinition
import MathGenome.Internal.D07.Ch01.IntegerPowerLaws
import MathGenome.Internal.Specs.D07.Ch01.HomPreservesPowers

/-!
Homomorphisms preserve division and every integer power, as asserted in
`K07.01.hom_preserves_powers` (paper.tex:303–310). Mathlib's `map_zpow`
proves the power identity by natural-power induction and inverse preservation,
including zero and negative exponents, exactly as in the source proof.
-/

namespace D07.Ch01.HomPreservesPowers

universe u v

theorem preserves_division (G : Type u) (H : Type v) [Group G] [Group H]
    (f : HomomorphismDefinition.GroupHom G H) (x y : G) :
    f (x / y) = f x / f y :=
  map_div f x y

theorem preserves_integer_powers (G : Type u) (H : Type v) [Group G] [Group H]
    (f : HomomorphismDefinition.GroupHom G H) (x : G) (n : ℤ) :
    f (x ^ n) = f x ^ n :=
  map_zpow f x n

end D07.Ch01.HomPreservesPowers
