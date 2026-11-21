import MathGenome.Internal.Specs.D05.M04.Equivalence
import MathGenome.Internal.D05.M02.BasisExtension
import MathGenome.Internal.D05.M03.RankNullity
import MathGenome.Internal.D05.M04.ChangeBasis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Lean.Elab.Tactic.Omega

namespace D05.M04.Equivalence

open Module Matrix
open Specs.D05.M04.Equivalence
open Specs.D05.M04.MatrixOfMap

/-- Split off the kernel and the image, with the same basis on the two
isomorphic rank summands. The sum indices put the rank summand first. -/
private theorem block_bases {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] W) :
    ∃ (k l : ℕ)
      (b : Basis (Fin (finrank K T.range) ⊕ Fin k) K V)
      (c : Basis (Fin (finrank K T.range) ⊕ Fin l) K W),
      ∀ i j, c.repr (T (b j)) i = (fromBlocks 1 0 0 0 :
        Matrix (Fin (finrank K T.range) ⊕ Fin l)
          (Fin (finrank K T.range) ⊕ Fin k) K) i j := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl T.ker
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl T.range
  let e := T.kerComplementEquivRange hC.symm
  let a := Module.finBasis K T.range
  let u := Module.finBasis K T.ker
  let d := Module.finBasis K D
  let b := ((a.map e.symm).prod u).map (C.prodEquivOfIsCompl T.ker hC.symm)
  let c := (a.prod d).map (T.range.prodEquivOfIsCompl D hD)
  refine ⟨finrank K T.ker, finrank K D, b, c, ?_⟩
  intro i j
  cases j with
  | inl j =>
    have ht : T (b (Sum.inl j)) = (a j : W) := by
      simp only [b, Basis.map_apply, Basis.prod_apply, Sum.elim_inl,
        Function.comp_apply, LinearMap.inl_apply, Submodule.coe_prodEquivOfIsCompl',
        Submodule.coe_zero, add_zero]
      change ((e (e.symm (a j)) : T.range) : W) = (a j : W)
      rw [e.apply_symm_apply]
    rw [ht]
    have hc : c.repr (a j : W) = (a.prod d).repr (a j, 0) := by
      change (a.prod d).repr ((T.range.prodEquivOfIsCompl D hD).symm (a j : W)) = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    rw [hc]
    cases i <;> simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
  | inr j =>
    have ht : T (b (Sum.inr j)) = 0 := by
      simp only [b, Basis.map_apply, Basis.prod_apply, Sum.elim_inr,
        Function.comp_apply, LinearMap.inr_apply, Submodule.coe_prodEquivOfIsCompl',
        Submodule.coe_zero, zero_add]
      exact (u j).property
    rw [ht]
    cases i <;> simp

/-- Convert the ordered sum indices to consecutive natural indices. -/
private def orderedIndex (r k n : ℕ) (h : r + k = n) :
    (Fin r ⊕ Fin k) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

private theorem orderedIndex_val_inl (r k n : ℕ) (h : r + k = n) (i : Fin r) :
    (orderedIndex r k n h (Sum.inl i)).val = i.val := by
  subst n
  rfl

private theorem orderedIndex_val_inr (r k n : ℕ) (h : r + k = n) (i : Fin k) :
    (orderedIndex r k n h (Sum.inr i)).val = r + i.val := by
  subst n
  rfl

theorem map_rank_normal_form : Specs.D05.M04.Equivalence.map_rank_normal_form := by
  intro K V W _ _ _ _ _ _ _ T
  classical
  obtain ⟨k, l, b, c, h⟩ := block_bases T
  let r := finrank K T.range
  have hn : r + k = finrank K V := by
    simpa [r] using (finrank_eq_card_basis b).symm
  have hm : r + l = finrank K W := by
    simpa [r] using (finrank_eq_card_basis c).symm
  let en := orderedIndex r k (finrank K V) hn
  let em := orderedIndex r l (finrank K W) hm
  refine ⟨b.reindex en, c.reindex em, ?_⟩
  apply Matrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := em.surjective i
  obtain ⟨j, rfl⟩ := en.surjective j
  dsimp only [matrixOfMap_value]
  rw [LinearMap.toMatrix_apply]
  change (c.reindex em).repr (T ((b.reindex en) (en j))) (em i) = _
  simp only [Basis.reindex_apply, Basis.repr_reindex_apply, Equiv.symm_apply_apply]
  rw [h]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [rankNormalMatrix, em, en, orderedIndex_val_inl, Matrix.one_apply,
        Fin.ext_iff, show i.val < finrank K T.range from i.isLt]
    | inr j =>
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, rankNormalMatrix]
      rw [show (em (Sum.inl i)).val = i.val from orderedIndex_val_inl ..,
        show (en (Sum.inr j)).val = r + j.val from orderedIndex_val_inr ..]
      have hij : i.val ≠ r + j.val := by omega
      simp [hij]
  | inr i =>
    cases j <;>
      simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, rankNormalMatrix] <;>
      rw [show (em (Sum.inr i)).val = r + i.val from orderedIndex_val_inr ..] <;>
      simp [show ¬ r + i.val < finrank K T.range by dsimp [r]; omega]

/-- Reversing invertible row and column changes. -/
theorem equivalent_symm {R : Type*} [CommRing R] {m n : ℕ}
    {A B : Matrix (Fin m) (Fin n) R} (h : Equivalent A B) : Equivalent B A := by
  obtain ⟨L, P, rfl⟩ := h
  refine ⟨L⁻¹, P⁻¹, ?_⟩
  simp [← Matrix.mul_assoc]

/-- Composition of independent changes. -/
theorem equivalent_trans {R : Type*} [CommRing R] {m n : ℕ}
    {A B C : Matrix (Fin m) (Fin n) R} (h : Equivalent A B)
    (h' : Equivalent B C) : Equivalent A C := by
  obtain ⟨L, P, rfl⟩ := h
  obtain ⟨L', P', rfl⟩ := h'
  refine ⟨L' * L, P * P', ?_⟩
  simp only [Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem matrix_rank_normal_form : Specs.D05.M04.Equivalence.matrix_rank_normal_form := by
  intro K _ m n A
  classical
  have h := map_rank_normal_form A.mulVecLin
  rw [show finrank K (Fin n → K) = n by simp,
    show finrank K (Fin m → K) = m by simp] at h
  obtain ⟨b, c, h⟩ := h
  let b₀ := Pi.basisFun K (Fin n)
  let c₀ := Pi.basisFun K (Fin m)
  have hA : matrixOfMap_value b₀ c₀ A.mulVecLin = A := by
    change LinearMap.toMatrix' (Matrix.toLin' A) = A
    exact LinearMap.toMatrix'_toLin' A
  have hchange := D05.M04.ChangeBasis.change_basis b₀ b c₀ c A.mulVecLin
  rw [hA, h] at hchange
  obtain ⟨L, hL⟩ := D05.M04.ChangeBasis.conversion_isUnit c c₀
  obtain ⟨P, hP⟩ := D05.M04.ChangeBasis.conversion_isUnit b₀ b
  refine ⟨L, P, ?_⟩
  rw [hL, hP]
  rw [D05.M04.ChangeBasis.conversion_nonsingular_inverse c₀ c] at hchange
  exact hchange

theorem equivalent_iff_rank : Specs.D05.M04.Equivalence.equivalent_iff_rank := by
  intro K _ m n A B
  classical
  constructor
  · rintro ⟨L, P, rfl⟩
    have hL : IsUnit (L : Matrix (Fin m) (Fin m) K).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp L.isUnit
    have hP : IsUnit (P : Matrix (Fin n) (Fin n) K).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hP,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hL]
  · intro h
    have hA := matrix_rank_normal_form A
    have hB := matrix_rank_normal_form B
    rw [← h] at hB
    exact equivalent_trans hA (equivalent_symm hB)

end D05.M04.Equivalence
