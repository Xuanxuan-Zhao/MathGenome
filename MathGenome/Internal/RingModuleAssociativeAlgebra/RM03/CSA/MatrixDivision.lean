import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.MatrixDivision
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Defs
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SimpleArtinianModules
import Mathlib.Algebra.Central.Basic

/-! Matrix and division presentations of central simple algebras. -/

universe u v

namespace RM03.CSA.MatrixDivision

open RM03.Specs.CSA.SimpleArtinianModules (columnModule columnScalarTower)

/-- The center consists of scalar matrices whose coefficient lies in the center. -/
theorem center_eq_scalar_map (k : Type u) [Field k] (D : Type v) [DivisionRing D] [Algebra k D]
    (r : ℕ) : Subalgebra.center k (Matrix (Fin r) (Fin r) D) =
      (Subalgebra.center k D).map (Matrix.scalarAlgHom (Fin r) k) :=
  Matrix.subalgebraCenter_eq_scalarAlgHom_map

/-- Every central simple algebra has a positive-size matrix presentation over
a central division algebra. -/
theorem exists_presentation (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
    (hA : IsCentralSimple k A) :
    ∃ (r : ℕ) (D : Type v) (_ : DivisionRing D) (_ : Algebra k D),
      IsCentralDivision k D ∧ 0 < r ∧ Nonempty (A ≃ₐ[k] Matrix (Fin r) (Fin r) D) := by
  let : IsSimpleRing A := hA.1
  let : Algebra.IsCentral k A := hA.2.1
  let : FiniteDimensional k A := hA.2.2
  obtain ⟨r, D, _, _, _, hr, ⟨e⟩⟩ := SimpleArtinianModules.matrixPresentation k A
  have hmatrix : Algebra.IsCentral k (Matrix (Fin r) (Fin r) D) :=
    Algebra.IsCentral.of_algEquiv k A _ e
  refine ⟨r, D, ‹DivisionRing D›, ‹Algebra k D›, ⟨⟨?_⟩, ‹Module.Finite k D›⟩, hr, ⟨e⟩⟩
  intro d hd
  have hscalar : Matrix.scalarAlgHom (Fin r) k d ∈
      Subalgebra.center k (Matrix (Fin r) (Fin r) D) := by
    rw [center_eq_scalar_map k D r]
    exact ⟨d, hd, rfl⟩
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (hmatrix.out hscalar)
  let i : Fin r := ⟨0, hr⟩
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) D => M i i) ha
  exact Algebra.mem_bot.mpr ⟨a, by
    simpa [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply] using h⟩

/-- In a positive-size presentation, scalar matrices embed the coefficients into the algebra. -/
private theorem finite_coefficient {k A D : Type*} [Field k] [Ring A] [DivisionRing D]
    [Algebra k A] [Algebra k D] [FiniteDimensional k A] {r : ℕ} (hr : 0 < r)
    (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) : FiniteDimensional k D := by
  let f := Matrix.scalarAlgHom (Fin r) k (α := D)
  have hf : Function.Injective f := by
    intro d d' h
    let i : Fin r := ⟨0, hr⟩
    simpa [f, Matrix.scalar_apply] using
      congrArg (fun M : Matrix (Fin r) (Fin r) D => M i i) h
  exact FiniteDimensional.of_injective
    (e.symm.toLinearEquiv.toLinearMap.comp f.toLinearMap) (e.symm.injective.comp hf)

/-- Comparing the endomorphism algebras of the two simple columns recovers
the division algebra over the original scalar field. The matrix size then
follows from the dimension of the algebra. -/
theorem presentation_unique (k : Type*) [Field k] (A : Type*) [Ring A] [Algebra k A]
    (hA : IsCentralSimple k A) (D : Type*) [DivisionRing D] [Algebra k D]
    (E : Type*) [DivisionRing E] [Algebra k E] (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) (f : A ≃ₐ[k] Matrix (Fin s) (Fin s) E) :
    r = s ∧ Nonempty (D ≃ₐ[k] E) := by
  let : IsSimpleRing A := hA.1
  let : FiniteDimensional k A := hA.2.2
  let : FiniteDimensional k D := finite_coefficient hr e
  let := columnModule e
  let := columnModule f
  let := columnScalarTower e
  let := columnScalarTower f
  let : IsSimpleModule A (Fin r → D) := SimpleArtinianModules.columnSimple k A D r e hr
  obtain ⟨g⟩ :=
    SimpleArtinianModules.simpleModuleEquivColumn k A E s f hs (Fin r → D)
  obtain ⟨d, _⟩ := SimpleArtinianModules.columnEnd k A D r e hr
  obtain ⟨d', _⟩ := SimpleArtinianModules.columnEnd k A E s f hs
  let b : D ≃ₐ[k] E := (d.trans ((g.conjAlgEquiv k).trans d'.symm)).unop
  refine ⟨?_, ⟨b⟩⟩
  have hdim := e.toLinearEquiv.finrank_eq.symm.trans f.toLinearEquiv.finrank_eq
  rw [Module.finrank_matrix, Module.finrank_matrix, ← b.toLinearEquiv.finrank_eq] at hdim
  have hsq : r ^ 2 * Module.finrank k D = s ^ 2 * Module.finrank k D := by
    simpa [pow_two] using hdim
  exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
    (Nat.mul_right_cancel (Module.finrank_pos (R := k) (M := D)) hsq)

end RM03.CSA.MatrixDivision
