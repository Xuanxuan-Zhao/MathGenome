import MathGenome.Internal.Specs.D07.Ch22.IntegralClosureTransitivity
import MathGenome.Internal.D07.Ch22.IntegralClosureTransitivityFiniteIntegralGeneration
import MathGenome.Internal.D07.Ch11.Eisenstein
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Finite integral algebras, transitivity, and the infinite-degree example
from paper.tex:7230–7267. The finite-generation and ring-operation results
are reused from the assigned prerequisite. The library transitivity proof
adjoins the finitely many coefficients of a monic equation, then uses
finite generation in a scalar tower, without a Noetherian hypothesis.

For the counterexample, Eisenstein at 2 gives the minimal polynomial
X^n-2 of a root in a closure, hence a degree-n finite simple subextension.
If the whole closure had finite dimension d, the root with n=d+1 would
contradict the bound on minimal-polynomial degree in a finite algebra.
-/

universe u v w
namespace D07.Ch22.IntegralClosureTransitivity
open Polynomial
open Specs.D07.Ch22.IntegralClosureTransitivity

theorem integralElementsSubalgebra : IntegralElementsSubalgebra.{u, v} :=
  IntegralClosureTransitivityFiniteIntegralGeneration.integralElementsSubalgebra

theorem finiteIntegralGeneration : FiniteIntegralGeneration.{u, v} := by
  intro R B _ _ _ t x hx
  let S := Algebra.adjoin R (Set.range x)
  have hS : S.toSubmodule.FG :=
    IntegralClosureTransitivityFiniteIntegralGeneration.finiteIntegralGeneration R B t x hx
  exact Module.Finite.of_fg hS

theorem finiteAlgebraIntegral : FiniteAlgebraIntegral.{u, v} :=
  IntegralClosureTransitivityFiniteIntegralGeneration.finiteAlgebraIntegral

theorem integralTransitivity : IntegralTransitivity.{u, v, w} := by
  intro R B C _ _ _ _ _ _ _ hB z hz
  let : Algebra.IsIntegral R B := ⟨hB⟩
  exact isIntegral_trans z hz

theorem integralAlgebraTransitivity : IntegralAlgebraTransitivity.{u, v, w} := by
  intro R B C _ _ _ _ _ _ _ hB hC
  exact ⟨fun z => integralTransitivity R B C hB.1 z (hC.1 z)⟩

theorem finiteGeneratedIffIntegralGenerators : FiniteGeneratedIffIntegralGenerators.{u, v} := by
  intro R B _ _ _ t x hgen
  constructor
  · intro hfin i
    let := hfin
    exact finiteAlgebraIntegral R B (x i)
  · intro hx
    have hfg :=
      IntegralClosureTransitivityFiniteIntegralGeneration.finiteIntegralGeneration R B t x hx
    rw [hgen, Algebra.top_toSubmodule] at hfg
    exact ⟨hfg⟩

theorem finiteIffIntegralAndFiniteType : FiniteIffIntegralAndFiniteType.{u, v} := by
  intro R B _ _ _
  exact Algebra.finite_iff_isIntegral_and_finiteType

theorem rationalPowerTwoEisenstein : RationalPowerTwoEisenstein := by
  intro n hn
  have hm : (X ^ n - C (2 : ℤ)).Monic := monic_X_pow_sub_C _ hn.ne'
  refine ⟨hm, natDegree_X_pow_sub_C, ⟨?_, ?_, ?_⟩,
    (D07.Ch11.Eisenstein.xPowSubPrime 2 n (by decide) hn).1⟩
  · rw [hm.leadingCoeff, Ideal.mem_span_singleton]
    norm_num
  · intro i hi
    rw [natDegree_X_pow_sub_C] at hi
    rw [Ideal.mem_span_singleton]
    by_cases hi0 : i = 0
    · subst i
      simp [coeff_X_pow, Ne.symm hn.ne']
    · simp only [coeff_sub, coeff_X_pow, ite_eq_right hi.ne, coeff_C,
        ite_eq_right hi0, sub_zero, dvd_zero]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [coeff_X_pow, Ne.symm hn.ne']

theorem rationalClosureRootDegrees : RationalClosureRootDegrees.{v} := by
  intro Ω _ _ _ n hn
  have hirr : Irreducible (X ^ n - C (2 : ℚ)) :=
    (D07.Ch11.Eisenstein.xPowSubPrime 2 n (by decide) hn).2
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (2 : Ω) hn
  have hmonic : (X ^ n - C (2 : ℚ)).Monic := monic_X_pow_sub_C _ hn.ne'
  have heval : aeval x (X ^ n - C (2 : ℚ)) = 0 := by
    simp [hx]
  have hint : IsIntegral ℚ x := ⟨_, hmonic, heval⟩
  have hmin : minpoly ℚ x = X ^ n - C (2 : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr heval hmonic).symm
  have hdeg : (minpoly ℚ x).natDegree = n := by
    rw [hmin, natDegree_X_pow_sub_C]
  exact ⟨hirr, x, hx, hint, hmin, hdeg,
    IntermediateField.adjoin.finiteDimensional hint,
    (IntermediateField.adjoin.finrank hint).trans hdeg⟩

theorem rationalClosureNotFinite : RationalClosureNotFinite.{v} := by
  intro Ω _ _ _ _
  have hint : Algebra.IsIntegral ℚ Ω := inferInstance
  have hnot : ¬ Module.Finite ℚ Ω := by
    intro hfin
    let := hfin
    obtain ⟨_, x, _, _, _, hdegree, _, _⟩ :=
      rationalClosureRootDegrees Ω (Module.finrank ℚ Ω + 1) (Nat.succ_pos _)
    have hle := minpoly.natDegree_le (A := ℚ) x
    rw [hdegree] at hle
    exact (Nat.not_succ_le_self _) hle
  refine ⟨hint, hnot, ?_⟩
  intro hft
  exact hnot ((finiteIffIntegralAndFiniteType ℚ Ω).mpr ⟨hint, hft⟩)

theorem integralNotFiniteExample : IntegralNotFiniteExample := by
  obtain ⟨hint, hnot, hft⟩ := rationalClosureNotFinite (AlgebraicClosure ℚ)
  exact ⟨AlgebraicClosure ℚ, inferInstance, inferInstance, hint, inferInstance, hnot, hft⟩

end D07.Ch22.IntegralClosureTransitivity
