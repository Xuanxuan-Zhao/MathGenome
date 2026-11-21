import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.GaussianArithmetic
import MathGenome.AbstractAlgebra.PolynomialApplications

/-! Arithmetic of the canonical Gaussian integers (Theorem 4.3, arithmetic part).
The checked MathGenome results concern the very same ring, conjugation, norm,
and quotient. Only the passage from irreducible to prime factors and the explicit
unit witness require adaptation of the factorization interface.
-/

namespace P203.Ch04.GaussianArithmetic

open P203Specs.Ch04.GaussianArithmetic

theorem canonical_model : CanonicalModel := by
  refine ⟨D07.Ch19.GaussianEuclidean.complex_embedding, ?_⟩
  intro z
  exact ⟨GaussianInt.toComplex_def z, rfl⟩

theorem norm_properties : NormProperties :=
  D07.Ch19.GaussianEuclidean.norm_properties

theorem norm_multiplicative : NormMultiplicative :=
  D07.Ch19.GaussianEuclidean.norm_multiplicative

theorem norm_euclidean_data : NormEuclideanData :=
  D07.Ch19.GaussianEuclidean.norm_euclidean_data

theorem division_estimate : DivisionEstimate :=
  D07.Ch19.GaussianEuclidean.division_estimate

theorem units : Units :=
  D07.Ch19.GaussianEuclidean.units

theorem unique_factorization : UniqueFactorization := by
  obtain ⟨hUFD, hex, huniq⟩ := D07.Ch19.GaussianEuclidean.unique_factorization
  let : UniqueFactorizationMonoid GaussianInt := hUFD
  refine ⟨hUFD, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨f, hf, u, hu⟩ := hex a ha
    refine ⟨f, fun p hp => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf p hp),
      u, ?_⟩
    simpa only [mul_comm] using hu.symm
  · intro f g hf hg hassoc
    exact huniq f g
      (fun p hp => UniqueFactorizationMonoid.irreducible_iff_prime.mpr (hf p hp))
      (fun q hq => UniqueFactorizationMonoid.irreducible_iff_prime.mpr (hg q hq)) hassoc
  · intro a
    simpa only [Multiset.prod_zero] using
      (associated_one_iff_isUnit (a := a)).symm.trans Associated.comm

end P203.Ch04.GaussianArithmetic
