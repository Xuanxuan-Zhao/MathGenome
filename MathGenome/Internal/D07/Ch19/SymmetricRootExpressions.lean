import MathGenome.Internal.Specs.D07.Ch19.SymmetricRootExpressions
import MathGenome.Internal.D07.Ch19.SymmetricPolynomialTheorem
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.Multiset.Fintype

/-! Symmetric polynomial expressions in all roots of a split monic polynomial.
The proofs use the root multiset, so repeated roots need no separate argument.
-/

universe u v

noncomputable section

namespace D07.Ch19.SymmetricRootExpressions

open MvPolynomial
open Specs.D07.Ch19.SymmetricRootExpressions

theorem root_enumeration_exists : RootEnumerationExists.{u, v} := by
  intro F K _ _ _ f hf hs
  classical
  let m := (f.map (algebraMap F K)).roots
  have hm : Fintype.card m = f.natDegree := by
    rw [Multiset.card_coe]
    exact hs.natDegree_eq_card_roots.symm.trans (hf.natDegree_map _)
  let e : Fin f.natDegree ≃ m := (Fintype.equivFinOfCardEq hm).symm
  refine ⟨fun i => (e i : K), ?_⟩
  change Finset.univ.val.map ((fun x : m => (x : K)) ∘ e) = m
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv, Multiset.map_univ_coe]

theorem elementary_root_values : ElementaryRootValues.{u, v} := by
  intro F K _ _ _ f hf hs α hα j hj
  rw [aeval_esymm_eq_multiset_esymm, hα]
  have h := Polynomial.coeff_eq_esymm_roots_of_splits hs
    (k := f.natDegree - j) (by rw [hf.natDegree_map]; exact Nat.sub_le _ _)
  simp only [hf.natDegree_map, (hf.map (algebraMap F K)).leadingCoeff,
    one_mul, Nat.sub_sub_self hj, Polynomial.coeff_map] at h
  have hsign : (-1 : K) ^ j * (-1) ^ j = 1 := by
    rw [← mul_pow]
    simp
  rw [map_mul, map_pow, map_neg, map_one, h, ← mul_assoc, hsign, one_mul]

theorem symmetric_value_from_coefficients : SymmetricValueFromCoefficients.{u, v} := by
  intro F K _ _ _ f hf hs α hα p hp
  obtain ⟨G, hG, _⟩ :=
    D07.Ch19.SymmetricPolynomialTheorem.unique_expression F f.natDegree p hp
  refine ⟨G, hG, ?_⟩
  let c : Fin f.natDegree → F := fun i =>
    (-1) ^ (i.val + 1) * f.coeff (f.natDegree - (i.val + 1))
  have he (i : Fin f.natDegree) :
      aeval α (esymm (Fin f.natDegree) F (i.val + 1)) = algebraMap F K (c i) :=
    elementary_root_values F K f hf hs α hα (i.val + 1) i.isLt
  rw [← hG, ← AlgHom.comp_apply, comp_aeval]
  change aeval (fun i => aeval α (esymm (Fin f.natDegree) F (i.val + 1))) G = _
  simp_rw [he]
  exact (eval₂_comp (algebraMap F K) c G).symm

theorem symmetric_root_value_in_base_field : SymmetricRootValueInBaseField.{u, v} := by
  intro F K _ _ _ f hf hs α hα p hp
  obtain ⟨G, _, hG⟩ := symmetric_value_from_coefficients F K f hf hs α hα p hp
  exact ⟨_, hG.symm⟩

end D07.Ch19.SymmetricRootExpressions
