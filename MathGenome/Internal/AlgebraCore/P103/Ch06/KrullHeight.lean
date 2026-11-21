import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.KrullHeight
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
Krull's height theorem (paper.tex:1041–1053).
Apply Mathlib's height theorem to the finite image of the given family.
Its cardinality is at most r even when generators repeat, and also when r=0.
The height is exactly the shared Chapter 6 height, which agrees with the
dimension of the prime localization by the upstream dimension conventions.
-/
namespace P103.Ch06.KrullHeight

universe u
open P103.Specs.Ch06.KrullHeight

theorem height_bound : height_boundType.{u} := by
  intro R _ _ r x I hI _ p hp
  classical
  let s : Finset R := Finset.univ.image x
  have hs : (s : Set R) = Set.range x := by
    ext a
    simp [s]
  have hp' : p.asIdeal ∈ (Ideal.span (s : Set R)).minimalPrimes := by
    simpa only [hs, ← hI] using hp
  change p.asIdeal.height ≤ (r : ℕ∞)
  refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hp').trans ?_
  exact_mod_cast (Finset.card_image_le (s := Finset.univ) (f := x)).trans
    (by simp : (Finset.univ : Finset (Fin r)).card ≤ r)

theorem principal_height_bound : principal_height_boundType.{u} := by
  intro R _ _ x _ p hp
  exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
    (Ideal.span ({x} : Set R)) p.asIdeal hp

theorem minimal_prime_height_zero : minimal_prime_height_zeroType.{u} := by
  intro R _ _ p hp
  exact Ideal.height_eq_zero_iff.mpr hp

end P103.Ch06.KrullHeight
