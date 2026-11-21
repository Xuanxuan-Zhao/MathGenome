import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Recurrence.InitialValues
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.DistinctRoots
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Theorem p204:W15: distinct characteristic roots.
Vandermonde inversion determines the coefficients on the first r entries;
uniqueness for the recurrence extends equality to all natural indices. -/

open scoped BigOperators
universe u
namespace FiniteCombinatorics.Recurrence

/-- A characteristic root gives a geometric solution, without dividing by the root. -/
theorem geometric_isSolution {K : Type u} [Field K] {r : ℕ}
    (c : Fin r → K) (q : K) (hq : (characteristicPolynomial c).IsRoot q) :
    IsSolution c (fun n => q ^ n) :=
  ((recurrence c).geom_sol_iff_root_charPoly q).mpr hq

/-- Any initial values have unique coefficients in the power columns of Vandermonde. -/
theorem existsUnique_initial_coefficients {K : Type u} [Field K] {r : ℕ}
    (roots : Fin r → K) (hroots : Function.Injective roots) (init : Fin r → K) :
    ∃! b : Fin r → K, ∀ j : Fin r, init j = ∑ i, b i * roots i ^ (j : ℕ) := by
  have hunit : IsUnit (Matrix.vandermonde roots) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hroots))
  obtain ⟨b, hb⟩ := Matrix.vecMul_surjective_iff_isUnit.mpr hunit init
  refine ⟨b, (fun j => (congrFun hb j).symm), ?_⟩
  intro d hd
  apply Matrix.vecMul_injective_iff_isUnit.mpr hunit
  exact (funext fun j => (hd j).symm).trans hb.symm

/-- Every solution is a unique linear combination of the geometric sequences.
The statement uses natural powers, so also covers a zero characteristic root. -/
theorem existsUnique_geometric_expansion {K : Type u} [Field K] {r : ℕ}
    (c : Fin r → K) (_hr : 1 ≤ r) (roots : Fin r → K)
    (hroots : Function.Injective roots)
    (hroot : ∀ i, (characteristicPolynomial c).IsRoot (roots i))
    (a : ℕ → K) (ha : IsSolution c a) :
    ∃! b : Fin r → K, ∀ n : ℕ, a n = ∑ i, b i * roots i ^ n := by
  obtain ⟨b, hb, huniq⟩ := existsUnique_initial_coefficients roots hroots (fun j => a j)
  have hs : IsSolution c (fun n => ∑ i, b i * roots i ^ n) := by
    change (fun n => ∑ i, b i * roots i ^ n) ∈ solutionSpace c
    have h := (solutionSpace c).sum_mem (fun i (_ : i ∈ Finset.univ) =>
      (solutionSpace c).smul_mem (b i) (geometric_isSolution c (roots i) (hroot i)))
    convert h using 1
    ext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨b, ?_, ?_⟩
  · have heq : a = (fun n => ∑ i, b i * roots i ^ n) :=
      ((recurrence c).eq_iff_eqOn_range_order a _ ha hs).mpr (by
        intro n hn
        exact hb ⟨n, Finset.mem_range.mp hn⟩)
    exact congrFun heq
  · intro d hd
    exact huniq d (fun j => hd j)

end FiniteCombinatorics.Recurrence
