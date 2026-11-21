import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Index
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MatrixDivision
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SeparableSubfield
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SubfieldSplitting
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.MatrixAlgebra

/-! Index and degrees of splitting extensions of central simple algebras. -/

namespace RM03.CSA

open scoped TensorProduct Matrix.Module

universe u v w x

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {D : Type w} [DivisionRing D] [Algebra k D]
  {L : Type x} [Field L] [Algebra k L] {r : ℕ}

/-- The index of a central simple algebra is the degree of its division factor. -/
noncomputable def index (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] : ℕ :=
  Specs.RM03.CSA.index k A

/-- The index agrees with the degree of every division factor over the original field. -/
theorem index_eq_degree (hA : IsCentralSimple k A) (_hD : IsCentralDivision k D)
    (hr : 0 < r) (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) :
    index k A = degree k D := by
  unfold index Specs.RM03.CSA.index
  obtain ⟨s, E, _, _, hE, hs, ⟨f⟩⟩ := MatrixDivision.exists_presentation k A hA
  have hne : {d : ℕ | ∃ (n : ℕ) (F : Type v) (_ : DivisionRing F) (_ : Algebra k F),
      IsCentralDivision k F ∧ 0 < n ∧ Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) F) ∧
      degree k F = d}.Nonempty :=
    ⟨degree k E, s, E, ‹DivisionRing E›, ‹Algebra k E›, hE, hs, ⟨f⟩, rfl⟩
  obtain ⟨n, F, _, _, _, hn, ⟨g⟩, hdeg⟩ := Nat.sInf_mem hne
  obtain ⟨_, ⟨i⟩⟩ := MatrixDivision.presentation_unique k A hA F D n r hn hr g e
  exact hdeg.symm.trans (congrArg Nat.sqrt i.toLinearEquiv.finrank_eq)

private def baseChangeMatrix (L : Type x) [Field L] [Algebra k L]
    {B : Type w} [Ring B] [Algebra k B] (n : ℕ) :
    BaseChange k L (Matrix (Fin n) (Fin n) B) ≃ₐ[L]
      Matrix (Fin n) (Fin n) (BaseChange k L B) :=
  (Algebra.TensorProduct.congr (Matrix.uniqueAlgEquiv (m := Unit) (R := L) (A := L)).symm
    (AlgEquiv.refl : Matrix (Fin n) (Fin n) B ≃ₐ[k] _)).trans
    ((Matrix.kroneckerTMulAlgEquiv Unit (Fin n) k L L B).trans
      (Matrix.reindexAlgEquiv L (BaseChange k L B) (Equiv.uniqueProd (Fin n) Unit)))

private def baseChangePresentation
    (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) :
    BaseChange k L A ≃ₐ[L] Matrix (Fin r) (Fin r) (BaseChange k L D) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans (baseChangeMatrix L r)

private def flattenMatrix {L : Type x} [Field L]
    (B : Type w) [Ring B] [Algebra L B] {r s : ℕ} :
    Matrix (Fin r) (Fin r) (Matrix (Fin s) (Fin s) B) ≃ₐ[L]
      Matrix (Fin (r * s)) (Fin (r * s)) B :=
  (Matrix.compAlgEquiv (Fin r) (Fin s) B L).trans
    (Matrix.reindexAlgEquiv L B finProdFinEquiv)

private theorem splits_of_division_splits
    (hr : 0 < r) (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) (h : Splits k L D) :
    Splits k L A := by
  obtain ⟨s, hs, ⟨f⟩⟩ := h
  exact ⟨r * s, Nat.mul_pos hr hs, ⟨(baseChangePresentation e).trans
    (f.mapMatrix.trans (flattenMatrix L))⟩⟩

private theorem division_splits_of_splits (hA : IsCentralSimple k A)
    (hD : IsCentralDivision k D) (hr : 0 < r)
    (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) (h : Splits k L A) :
    Splits k L D := by
  have hDL := isCentralSimple_baseChange (L := L) (isCentralSimple_of_isCentralDivision k D hD)
  obtain ⟨s, F, _, _, _, hs, ⟨f⟩⟩ :=
    MatrixDivision.exists_presentation L (BaseChange k L D) hDL
  obtain ⟨n, hn, ⟨g⟩⟩ := h
  let p := (baseChangePresentation e).trans (f.mapMatrix.trans (flattenMatrix F))
  obtain ⟨_, ⟨i⟩⟩ := MatrixDivision.presentation_unique L (BaseChange k L A)
    (isCentralSimple_baseChange hA) F L (r * s) n (Nat.mul_pos hr hs) hn p g
  exact ⟨s, hs, ⟨f.trans i.mapMatrix⟩⟩

private theorem division_degree_dvd_of_splits [FiniteDimensional k L]
    (hD : IsCentralDivision k D) (h : Splits k L D) :
    degree k D ∣ Module.finrank k L := by
  obtain ⟨n, hn_pos, ⟨f⟩⟩ := h
  have hCentral := isCentralSimple_of_isCentralDivision k D hD
  have hn := degree_eq_matrix_size hCentral f
  let j : D →ₐ[k] BaseChange k L D := Algebra.TensorProduct.includeRight
  let g : D →ₐ[k] Matrix (Fin n) (Fin n) L := (f.restrictScalars k).toAlgHom.comp j
  let : Module D (Fin n → L) := Module.compHom _ g.toRingHom
  let : IsScalarTower k D (Fin n → L) := IsScalarTower.of_algebraMap_smul fun a z => by
    change g (algebraMap k D a) • z = a • z
    rw [g.commutes, algebraMap_smul]
  have ht := Module.finrank_mul_finrank k D (Fin n → L)
  rw [finrank_eq_degree_sq hCentral, hn, Module.finrank_pi_fintype] at ht
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    pow_two, mul_assoc] at ht
  rw [hn]
  exact ⟨Module.finrank D (Fin n → L), (Nat.eq_of_mul_eq_mul_left hn_pos ht).symm⟩

/-- The index divides the degree of every finite splitting extension. -/
theorem index_dvd_finrank_of_splits [FiniteDimensional k L]
    (hA : IsCentralSimple k A) (h : Splits k L A) :
    index k A ∣ Module.finrank k L := by
  obtain ⟨r, D, _, _, hD, hr, ⟨e⟩⟩ := MatrixDivision.exists_presentation k A hA
  rw [index_eq_degree hA hD hr e]
  exact division_degree_dvd_of_splits hD (division_splits_of_splits hA hD hr e h)

/-- A central simple algebra has a finite separable splitting field of degree its index. -/
theorem exists_separable_splitting_field_of_finrank_index (hA : IsCentralSimple k A) :
    ∃ (E : Type v) (_ : Field E) (_ : Algebra k E),
      FiniteDimensional k E ∧ Algebra.IsSeparable k E ∧ Splits k E A ∧
        Module.finrank k E = index k A := by
  obtain ⟨r, D, _, _, hD, hr, ⟨e⟩⟩ := MatrixDivision.exists_presentation k A hA
  obtain ⟨E, hField, hSep, hDim⟩ := exists_separable_subfield hD
  let : Field E := hField.toField
  let : FiniteDimensional k D := hD.2
  obtain ⟨f⟩ := subfield_splits E.val hD hDim
  refine ⟨E, ‹Field E›, inferInstance, inferInstance, hSep, ?_, ?_⟩
  · exact splits_of_division_splits hr e
      ⟨degree k D, degree_pos (isCentralSimple_of_isCentralDivision k D hD), ⟨f⟩⟩
  · exact hDim.trans (index_eq_degree hA hD hr e).symm

end RM03.CSA
