import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InnerDerivations
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.JordanDerivations
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AbstractJordan

/-! LA-B07 (source lines 954–999): transfer the Jordan decomposition of ad x
from derivations to the original algebra using the bijective adjoint map.
Polynomiality of the linear parts then gives the centralizer assertion. -/

universe u v
namespace LieAlgebrasAndRepresentations

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] [CharZero k]
  {L : Type v} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

omit [CharZero k] [FiniteDimensional k L] in
/-- Forgetting the derivation structure of an inner derivation gives ad. -/
private theorem adjoint_toLinearMap (x : L) :
    (adjoint k L x).toLinearMap = LieAlgebra.ad k L x := by
  ext y
  exact adjoint_apply x y

/-- Faithfulness of the endomorphism-valued adjoint representation. -/
theorem adjoint_end_injective (h : IsSemisimple k L) :
    Function.Injective (LieAlgebra.ad k L) := by
  intro x y he
  apply (adjoint_bijective k L h).injective
  apply LieDerivation.toLinearMapLieHom_injective k L
  change (adjoint k L x).toLinearMap = (adjoint k L y).toLinearMap
  simpa only [adjoint_toLinearMap] using he

omit [CharZero k] [FiniteDimensional k L] in
/-- An abstract decomposition induces the ordinary linear decomposition. -/
theorem abstract_jordan_to_linear {x s n : L}
    (hdec : IsAbstractJordanDecomposition (k := k) x s n) :
    IsJordanDecomposition (LieAlgebra.ad k L x)
      (LieAlgebra.ad k L s) (LieAlgebra.ad k L n) := by
  rcases hdec with ⟨he, hc, hs, hn⟩
  refine ⟨by rw [he, map_add], ?_, hs, hn⟩
  have hh := (LieAlgebra.ad k L).map_lie s n
  rw [hc, map_zero] at hh
  exact sub_eq_zero.mp hh.symm

/-- LA-B07: existence and full uniqueness over the original field. -/
theorem abstract_jordan_decomposition :
    Specs.LieAlgebrasAndRepresentations.AbstractJordan.abstract_jordan_decomposition_type := by
  intro k L _ _ _ _ _ h x
  obtain ⟨S, N, hdec, _, _, huniq⟩ :=
    jordan_decomposition_derivations (adjoint k L x)
  obtain ⟨s, hs⟩ := (adjoint_bijective k L h).surjective S
  obtain ⟨n, hn⟩ := (adjoint_bijective k L h).surjective N
  have hs' : LieAlgebra.ad k L s = S.toLinearMap :=
    (adjoint_toLinearMap s).symm.trans (congrArg LieDerivation.toLinearMap hs)
  have hn' : LieAlgebra.ad k L n = N.toLinearMap :=
    (adjoint_toLinearMap n).symm.trans (congrArg LieDerivation.toLinearMap hn)
  rw [adjoint_toLinearMap] at hdec huniq
  have hinj := adjoint_end_injective h
  refine ⟨s, n, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · apply hinj
    rw [map_add, hs', hn']
    exact hdec.1
  · apply hinj
    rw [(LieAlgebra.ad k L).map_lie, map_zero, hs', hn']
    exact sub_eq_zero.mpr hdec.2.1.eq
  · rw [hs']
    exact hdec.2.2.1
  · rw [hn']
    exact hdec.2.2.2
  · intro s' n' h'
    have hh := huniq _ _ (abstract_jordan_to_linear h')
    exact ⟨hinj (hh.1.trans hs'.symm), hinj (hh.2.trans hn'.symm)⟩

/-- LA-B07: elements commuting with x commute with both Jordan parts. -/
theorem abstract_jordan_centralizer :
    Specs.LieAlgebrasAndRepresentations.AbstractJordan.abstract_jordan_centralizer_type := by
  intro k L _ _ _ _ _ h x s n hdec y hxy
  obtain ⟨S, N, hlin, ⟨p, q, hp, hq⟩, _, _⟩ :=
    linear_jordan_decomposition (LieAlgebra.ad k L x)
  obtain ⟨hs, hn⟩ := jordan_decomposition_unique (abstract_jordan_to_linear hdec) hlin
  have hcomm : Commute (LieAlgebra.ad k L y) (LieAlgebra.ad k L x) := by
    have hh := (LieAlgebra.ad k L).map_lie x y
    rw [hxy, map_zero] at hh
    exact (sub_eq_zero.mp hh.symm).symm
  have hzero (z : L)
      (hz : LieAlgebra.ad k L z ∈ Algebra.adjoin k {LieAlgebra.ad k L x}) :
      ⁅z, y⁆ = 0 := by
    have hc := Algebra.commute_of_mem_adjoin_singleton_of_commute hz hcomm
    apply adjoint_end_injective h
    rw [(LieAlgebra.ad k L).map_lie, map_zero]
    exact sub_eq_zero.mpr hc.symm.eq
  constructor
  · apply hzero
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, hp.trans hs.symm⟩
  · apply hzero
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, hq.trans hn.symm⟩

end LieAlgebrasAndRepresentations
