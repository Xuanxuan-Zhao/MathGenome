import MathGenome.Internal.Specs.D07.Ch22.IntegralClosureTransitivityFiniteIntegralGeneration
import MathGenome.Internal.D07.Ch22.DeterminantTrick
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-! Bounded monomial generation and closure of integral elements.
The single-variable reduction is polynomial division by a monic equation.
Products of the resulting spans give the several-variable result. The
finite-subalgebra determinant trick supplies integrality of every element.
No finiteness claim about arbitrary submodules is used. -/

universe u v w
namespace D07.Ch22.IntegralClosureTransitivityFiniteIntegralGeneration
open Polynomial
open scoped BigOperators Pointwise
open Specs.D07.Ch22.IntegralClosureTransitivityFiniteIntegralGeneration

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- A displayed monic equation gives the prescribed spanning powers, even
when its displayed exponent is not its formal degree (the zero ring). -/
theorem span_powers_of_equation (x : B) (n : ℕ) (a : ℕ → R)
    (heq : x ^ n + ∑ k ∈ Finset.range n, algebraMap R B (a k) * x ^ k = 0) :
    (Algebra.adjoin R ({x} : Set B)).toSubmodule =
      Submodule.span R (Set.range fun e : Fin n => x ^ (e : ℕ)) := by
  classical
  let p : R[X] := X ^ n + ∑ k ∈ Finset.range n, C (a k) * X ^ k
  have hp : p.Monic := by
    apply monic_X_pow_add
    rw [← Fin.sum_univ_eq_sum_range]
    exact degree_sum_fin_lt (fun i : Fin n => a i)
  have heval : aeval x p = 0 := by
    simpa only [p, map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C] using heq
  have hdegree : p.natDegree ≤ n := by
    apply natDegree_add_le_of_degree_le
    · exact natDegree_X_pow_le n
    · apply natDegree_sum_le_of_forall_le
      intro i hi
      exact (natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_range.mp hi).le
  apply le_antisymm
  · rw [← Submodule.span_range_natDegree_eq_adjoin hp heval]
    apply Submodule.span_mono
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨⟨k, (Finset.mem_range.mp hk).trans_le hdegree⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact (Algebra.adjoin R ({x} : Set B)).pow_mem (Algebra.subset_adjoin rfl) _

/-- Adjoining a finite family is the product of its single-generator
underlying submodules. Commutativity is used in this product identity. -/
theorem adjoin_image_toSubmodule {ι : Type w} (s : Finset ι) (x : ι → B) :
    (Algebra.adjoin R (x '' (s : Set ι))).toSubmodule =
      ∏ i ∈ s, (Algebra.adjoin R ({x i} : Set B)).toSubmodule := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.toSubmodule_bot, Submodule.one_eq_span]
  | insert i s hi ih =>
    rw [Finset.coe_insert, Set.image_insert_eq, ← Set.singleton_union,
      Algebra.adjoin_union_coe_submodule, ih, Finset.prod_insert hi]

theorem boundedMonomialSpan : BoundedMonomialSpan.{u, v} := by
  intro R B _ _ _ t x n a hn heq
  classical
  have hsingle (i : Fin t) := span_powers_of_equation (x i) (n i) (a i) (heq i)
  have hsets : (∏ i, Set.range fun e : Fin (n i) => x i ^ (e : ℕ)) =
      Set.range (fun e : (i : Fin t) → Fin (n i) => ∏ i, x i ^ (e i : ℕ)) := by
    ext y
    rw [Set.mem_fintype_prod]
    constructor
    · rintro ⟨g, hg, rfl⟩
      choose e he using hg
      exact ⟨e, Finset.prod_congr rfl (fun i _ => he i)⟩
    · rintro ⟨e, rfl⟩
      exact ⟨fun i => x i ^ (e i : ℕ), fun i => ⟨e i, rfl⟩, rfl⟩
  calc
    (Algebra.adjoin R (Set.range x)).toSubmodule =
        ∏ i, (Algebra.adjoin R ({x i} : Set B)).toSubmodule := by
      simpa using adjoin_image_toSubmodule (R := R) Finset.univ x
    _ = ∏ i, Submodule.span R (Set.range fun e : Fin (n i) => x i ^ (e : ℕ)) := by
      simp_rw [hsingle]
    _ = _ := by rw [Submodule.prod_span, hsets]

theorem finiteIntegralGeneration : FiniteIntegralGeneration.{u, v} := by
  intro R B _ _ _ t x hx
  classical
  have h := fun i => (DeterminantTrick.integralEquation R B (x i)).mp (hx i)
  choose n hn a ha using h
  rw [boundedMonomialSpan R B t x n a hn ha]
  exact Submodule.fg_span (Set.finite_range _)

theorem finiteAlgebraIntegral : FiniteAlgebraIntegral.{u, v} := by
  intro R B _ _ _ _ x
  exact DeterminantTrick.integral_of_mem_finite_subalgebra ⊤
    (by simpa only [Algebra.top_toSubmodule] using (Module.Finite.fg_top (R := R) (M := B)))
    x trivial

/-- All combinations in the two-generator algebra are integral. -/
theorem integral_of_mem_adjoin_pair (x y z : B) (hx : IsIntegral R x)
    (hy : IsIntegral R y) (hz : z ∈ Algebra.adjoin R ({x, y} : Set B)) :
    IsIntegral R z := by
  have hfg := finiteIntegralGeneration R B 2 ![x, y] (by
    intro i
    fin_cases i <;> simpa using (by assumption : IsIntegral R _))
  have hrange : Set.range ![x, y] = ({x, y} : Set B) := by
    ext z
    simp [or_comm]
  rw [hrange] at hfg
  exact DeterminantTrick.integral_of_mem_finite_subalgebra _ hfg z hz

theorem integralOperations : IntegralOperations.{u, v} := by
  intro R B _ _ _
  have hscalar (r : R) : IsIntegral R (algebraMap R B r) := isIntegral_algebraMap
  refine ⟨hscalar, ?_, ?_⟩
  · intro x y hx hy
    let S := Algebra.adjoin R ({x, y} : Set B)
    have hxS : x ∈ S := Algebra.subset_adjoin (by simp)
    have hyS : y ∈ S := Algebra.subset_adjoin (by simp)
    exact ⟨integral_of_mem_adjoin_pair x y (x + y) hx hy (S.add_mem hxS hyS),
      integral_of_mem_adjoin_pair x y (x * y) hx hy (S.mul_mem hxS hyS),
      integral_of_mem_adjoin_pair x y (x - y) hx hy (S.sub_mem hxS hyS)⟩
  · intro x hx
    apply integral_of_mem_adjoin_pair x 0 (-x) hx
      (by simpa only [map_zero] using hscalar 0)
    exact (Algebra.adjoin R ({x, 0} : Set B)).neg_mem (Algebra.subset_adjoin (by simp))

theorem integralElementsSubalgebra : IntegralElementsSubalgebra.{u, v} := by
  intro R B _ _ _
  obtain ⟨hscalar, hops, hneg⟩ := integralOperations R B
  exact ⟨{
    carrier := {x | IsIntegral R x}
    zero_mem' := by
      change IsIntegral R (0 : B)
      simpa only [map_zero] using hscalar 0
    one_mem' := by
      change IsIntegral R (1 : B)
      simpa only [map_one] using hscalar 1
    add_mem' := fun hx hy => (hops _ _ hx hy).1
    mul_mem' := fun hx hy => (hops _ _ hx hy).2.1
    algebraMap_mem' := hscalar }, fun _ => Iff.rfl⟩

end D07.Ch22.IntegralClosureTransitivityFiniteIntegralGeneration
