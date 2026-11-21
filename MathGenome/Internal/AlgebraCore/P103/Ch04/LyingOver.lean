import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.LyingOver
import Mathlib.RingTheory.Ideal.GoingUp

/-! Lying over for arbitrary integral ring maps (Theorem 4.6).
The library ideal theorem allows a nonzero kernel and arbitrary
commutative rings, so no reduction requiring a nontrivial ring is imposed.
-/

namespace P103.Ch04.LyingOver

theorem contraction_contains_kernel : Specs.contraction_contains_kernel := by
  intro R A _ _ g q
  exact Ideal.ker_le_comap g

theorem exists_prime_over : Specs.exists_prime_over := by
  intro R A _ _ g hg p hp hker
  let : Algebra R A := g.toAlgebra
  let : Algebra.IsIntegral R A := ⟨hg⟩
  let : p.IsPrime := hp
  obtain ⟨q, _, hq, heq⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal A) hker
  exact ⟨q, hq, heq⟩

theorem spectrum_image : Specs.spectrum_image := by
  intro R A _ _ g hg
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact contraction_contains_kernel R A g q
  · intro hp
    obtain ⟨q, hq, heq⟩ := exists_prime_over R A g hg p.asIdeal p.isPrime hp
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext heq⟩

end P103.Ch04.LyingOver
