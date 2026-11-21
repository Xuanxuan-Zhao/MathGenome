import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.AffineJacobson
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
The prime-intersection assertion of Theorem 6.7 over an arbitrary field.
We use the finite-type Jacobson theorem for separation. We also verify
the nonzero and finite-type properties of the source's principal localization.
-/
namespace P103.Ch06.AffineJacobson

open P103.Specs.Ch06.AffineJacobson

universe u v

theorem localization_nontrivial_finiteType :
    localization_nontrivial_finiteTypeType.{u,v} := by
  intro k A _ _ _ _ P hP a ha
  let : P.IsPrime := hP
  have hbar : Ideal.Quotient.mk P a ≠ 0 := by
    simpa only [Ne, Ideal.Quotient.eq_zero_iff_mem] using ha
  let := Localization.Away.isDomain hbar
  exact ⟨inferInstance, inferInstance⟩

theorem prime_eq_intersection : prime_eq_intersectionType.{u,v} := by
  intro k A _ _ _ _ P hP
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  exact (isJacobsonRing_iff_prime_eq.mp ‹IsJacobsonRing A› P hP).symm

theorem maximal_separation : maximal_separationType.{u,v} := by
  intro k A _ _ _ _ P hP a ha
  classical
  by_contra h
  apply ha
  rw [prime_eq_intersection k A P hP]
  apply Ideal.mem_sInf.mpr
  intro m hm
  by_contra ham
  exact h ⟨m, hm.2, hm.1, ham⟩

end P103.Ch06.AffineJacobson
