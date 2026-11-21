import MathGenome.Internal.Specs.D07.Ch09.Contraction
import MathGenome.Internal.D07.Ch09.IdealCorrespondence
import MathGenome.Internal.D07.Ch09.PrimeIdeal
import Mathlib.Algebra.Ring.Int.Field
import Mathlib.RingTheory.Ideal.Basic

/-! Contraction of prime and maximal ideals, including the two boundary
cases of K07.09.contraction (paper.tex:1699–1707). -/

universe u v

namespace D07.Ch09.Contraction

open Specs.D07.Ch09.Contraction

theorem contraction_carrier : ContractionCarrier.{u, v} := by
  intro R S _ _ f I
  rfl

theorem prime_contraction_proper : PrimeContractionProper.{u, v} := by
  intro R S _ _ f P hP
  have h1 : (1 : R) ∉ P.comap f := by
    intro h
    have h' : f 1 ∈ P := h
    rw [map_one] at h'
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P h' isUnit_one)
  refine ⟨h1, ?_⟩
  intro htop
  apply h1
  rw [htop]
  trivial

theorem prime_contraction : PrimeContraction.{u, v} := by
  intro R S _ _ f P hP
  apply (PrimeIdeal.primeCharacterization R (P.comap f)).mpr
  refine ⟨(prime_contraction_proper R S f P hP).2, ?_⟩
  intro a b hab
  have hab' : f a * f b ∈ P := by
    rw [← map_mul]
    exact hab
  exact hP.mem_or_mem hab'

theorem maximal_contraction : MaximalContraction.{u, v} := by
  intro R S _ _ f hf M hM
  let : M.IsMaximal := hM
  exact Ideal.comap_isMaximal_of_surjective f hf

theorem integer_rational_counterexample : IntegerRationalCounterexample := by
  have hinj : Function.Injective (Int.castRingHom ℚ) :=
    IdealCorrespondence.integer_rational_image_not_ideal.1
  have hnotsurj : ¬ Function.Surjective (Int.castRingHom ℚ) := by
    intro hsurj
    apply IdealCorrespondence.integer_rational_image_not_ideal.2
    refine ⟨⊤, ?_⟩
    rw [Set.range_eq_univ.mpr hsurj]
    rfl
  have hcomap : (⊥ : Ideal ℚ).comap (Int.castRingHom ℚ) = (⊥ : Ideal ℤ) :=
    Ideal.comap_bot_of_injective (Int.castRingHom ℚ) hinj
  refine ⟨hinj, hnotsurj, Ideal.bot_isMaximal, hcomap, ?_⟩
  rw [hcomap]
  intro hmax
  exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr hmax)

theorem nonunital_counterexample : NonunitalCounterexample := by
  refine ⟨0, ?_, inferInstance, ?_⟩
  · change (0 : ℤ) ≠ 1
    decide
  · ext x
    simp

end D07.Ch09.Contraction
