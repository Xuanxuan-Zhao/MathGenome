import MathGenome.Internal.Specs.D07.Ch19.SymmetricFunctions
import Mathlib.RingTheory.Polynomial.Vieta

/-! Elementary symmetric polynomials over an arbitrary commutative unital ring. -/

universe u
noncomputable section

namespace D07.Ch19.SymmetricFunctions

open MvPolynomial
open Specs.D07.Ch19.SymmetricFunctions

theorem elementary_definition : ElementaryDefinition.{u} := by
  intro R _ n j
  rfl

theorem elementary_zero : ElementaryZero.{u} := by
  intro R _ n
  exact esymm_zero (Fin n) R

theorem permutation_automorphisms : PermutationAutomorphisms.{u} := by
  intro R _ n π
  exact ⟨fun _ => rfl, fun _ => rename_C π _, fun _ => rename_X π _, fun _ => rfl⟩

theorem permutation_action : PermutationAction.{u} := by
  intro R _ n p
  constructor
  · exact rename_id_apply p
  · intro π τ
    exact (rename_rename τ π p).symm

theorem exponent_permutation : ExponentPermutation.{u} := by
  intro R _ n π d e a p
  refine ⟨Finsupp.mapDomain_add, rename_monomial π d a,
    coeff_rename_mapDomain π π.injective p d, ?_⟩
  rw [← Finsupp.mapDomain_comp, π.symm_comp_self, Finsupp.mapDomain_id]

theorem symmetry_definition : SymmetryDefinition.{u} := by
  intro R _ n p
  rfl

theorem fixed_subring : FixedSubring.{u} := by
  intro R _ n p
  rfl

theorem symmetric_closure : SymmetricClosure.{u} := by
  intro R _ n
  exact ⟨IsSymmetric.zero, IsSymmetric.one, fun p q hp hq =>
    ⟨hp.add hq, hp.sub hq, hp.mul hq, hp.neg⟩⟩

theorem elementary_symmetry : ElementarySymmetry.{u} := by
  intro R _ n j
  exact esymm_isSymmetric (Fin n) R j

/-- Apply the multiset expansion to the list of formal variables. Its elementary
symmetric functions are the canonical multivariate elementary polynomials. -/
theorem formal_vieta : FormalVieta.{u} := by
  intro R _ n
  classical
  let s : Multiset (MvPolynomial (Fin n) R) :=
    Finset.univ.val.map (fun i : Fin n => X i)
  have hs : s.card = n := by simp [s]
  have he (j : ℕ) : s.esymm j = esymm (Fin n) R j := by
    exact (congrFun (esymm_eq_multiset_esymm (Fin n) R) j).symm
  have h := Multiset.prod_X_sub_X_eq_sum_esymm s
  simp only [hs, he] at h
  convert h using 1
  rw [Finset.prod_eq_multiset_prod]
  simp only [s, Multiset.map_map, Function.comp_def]

theorem empty_vieta : EmptyVieta.{u} := by
  intro R _
  simp

end D07.Ch19.SymmetricFunctions
