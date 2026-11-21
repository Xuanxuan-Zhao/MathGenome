import MathGenome.Internal.Specs.D07.Ch22.DeterminantTrick
import MathGenome.Internal.D07.Ch22.DeterminantTrickStableFiniteSubmodule
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
Integral elements and the determinant trick, paper.tex:7185–7227.

A monic equation gives finite module generation of R[x] by reduction of
powers. For the converse, restrict multiplication by x to the given
finite subalgebra and apply the upstream determinant trick. Its identity
belongs to the underlying submodule, so the annihilator is an equation
for x. No basis, domain, nontriviality, or injective algebra map is used.
-/

universe u v

namespace D07.Ch22.DeterminantTrick

open Polynomial
open scoped BigOperators
open Specs.D07.Ch22.DeterminantTrick

/-- Finite module generation of a subalgebra containing x supplies the
stable submodule, and membership of 1 turns its annihilator into an equation. -/
theorem integral_of_mem_finite_subalgebra
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (C : Subalgebra R B) (hC : C.toSubmodule.FG) (x : B) (hx : x ∈ C) :
    IsIntegral R x := by
  obtain ⟨n, hn, a, hp, hann, hOne, hFaithful⟩ :=
    DeterminantTrickStableFiniteSubmodule.stableFiniteSubmodule R B x C.toSubmodule hC
      (fun m hm => C.mul_mem hx hm)
  exact (hOne C.one_mem).2

theorem integralFiniteEquivalences : IntegralFiniteEquivalences.{u, v} := by
  intro R B _ _ _ x
  have hmem : x ∈ Algebra.adjoin R ({x} : Set B) := Algebra.subset_adjoin rfl
  constructor
  · exact ⟨fun hx => hx.fg_adjoin_singleton,
      fun h => integral_of_mem_finite_subalgebra _ h x hmem⟩
  · constructor
    · intro hx
      exact ⟨Algebra.adjoin R ({x} : Set B), hmem, hx.fg_adjoin_singleton⟩
    · rintro ⟨C, hx, hC⟩
      exact integral_of_mem_finite_subalgebra C hC x hx

theorem integralEquation : IntegralEquation.{u, v} := by
  intro R B _ _ _ x
  constructor
  · intro hx
    let C := Algebra.adjoin R ({x} : Set B)
    have hxC : x ∈ C := Algebra.subset_adjoin rfl
    obtain ⟨n, hn, a, hp, hann, hOne, hFaithful⟩ :=
      DeterminantTrickStableFiniteSubmodule.stableFiniteSubmodule R B x C.toSubmodule
        hx.fg_adjoin_singleton (fun m hm => C.mul_mem hxC hm)
    refine ⟨n, hn, a, ?_⟩
    simpa only [map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C] using
      (hOne C.one_mem).1
  · rintro ⟨n, hn, a, heq⟩
    let p : R[X] := X ^ n + ∑ i ∈ Finset.range n, C (a i) * X ^ i
    have hp : p.Monic := by
      apply monic_X_pow_add
      rw [← Fin.sum_univ_eq_sum_range]
      exact degree_sum_fin_lt (fun i : Fin n => a i)
    refine ⟨p, hp, ?_⟩
    change aeval x p = 0
    simpa only [p, map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C] using heq

theorem stableFiniteSubmodule : StableFiniteSubmodule.{u, v} :=
  DeterminantTrickStableFiniteSubmodule.stableFiniteSubmodule

end D07.Ch22.DeterminantTrick
