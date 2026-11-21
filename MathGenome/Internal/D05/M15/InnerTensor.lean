import MathGenome.Internal.Specs.D05.M15.InnerTensor
import MathGenome.Internal.D05.M12.InnerProduct
import MathGenome.Internal.D05.M12.OnBasis
import MathGenome.Internal.D05.M15.TensorBasis

/-! K05.15.inner_tensor. Coordinate construction and its canonical characterization
on the same algebraic tensor product as the upstream tensor basis. -/

noncomputable section
open scoped TensorProduct

namespace D05.M15.InnerTensor

abbrev coordinateForm : Specs.D05.M15.InnerTensor.coordinateForm_type :=
  @_root_.D05.tensorCoordinateInner

/-- Transport of the coordinate axioms uses injectivity of the coordinate map,
so it also proves definiteness when one of the product index sets is empty. -/
theorem coordinate_axioms : Specs.D05.M15.InnerTensor.coordinate_axioms := by
  intro F V W I J _ _ _ _ _ _ _ e f
  let B := e.tensorProduct f
  have hh := D05.M12.InnerProduct.coordinateInner_axioms (F := F) (ι := I × J)
  change D05.IsFirstInnerProduct (fun z t => D05.coordinateInner (B.equivFun z) (B.equivFun t))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b u v w
    simpa only [map_add, map_smul] using hh.1 a b (B.equivFun u) (B.equivFun v) (B.equivFun w)
  · intro u v
    exact hh.2.1 _ _
  · intro v
    exact hh.2.2.1 _
  · intro v hv
    apply hh.2.2.2
    intro hz
    apply hv
    exact B.equivFun.injective (hz.trans (map_zero B.equivFun).symm)

theorem coordinate_expansion : Specs.D05.M15.InnerTensor.coordinate_expansion := by
  intro F V W I J _ _ _ _ _ _ _ e f c d
  have hc (a : I × J → F) :
      (e.tensorProduct f).equivFun (∑ p, a p • (e p.1 ⊗ₜ[F] f p.2)) = a := by
    simpa only [Module.Basis.equivFun_symm_apply, Module.Basis.tensorProduct_apply'] using
      (e.tensorProduct f).equivFun.apply_symm_apply a
  simp only [D05.tensorCoordinateInner, hc, D05.coordinateInner]

theorem canonical_axioms : Specs.D05.M15.InnerTensor.canonical_axioms := by
  intro F V W _ _ _ _ _
  exact D05.M12.InnerProduct.firstInner_axioms

theorem pure_tensor : Specs.D05.M15.InnerTensor.pure_tensor := by
  intro F V W _ _ _ _ _ v v' w w'
  exact TensorProduct.inner_tmul F v' v w' w

theorem coordinate_eq_canonical : Specs.D05.M15.InnerTensor.coordinate_eq_canonical := by
  intro F V W I J _ _ _ _ _ _ _ e f he hf z t
  have hB : Orthonormal F (e.tensorProduct f) :=
    ((D05.M12.Orthonormal.orthonormal_iff_mathlib e).mp he).basisTensorProduct
      ((D05.M12.Orthonormal.orthonormal_iff_mathlib f).mp hf)
  let b := (e.tensorProduct f).toOrthonormalBasis hB
  change inner F (b.repr t) (b.repr z) = inner F t z
  exact b.repr.inner_map_map t z

/-- Double tensor induction is the algebraic spanning argument in both slots.
No continuity, conjugate symmetry, definiteness or finite dimension is needed. -/
theorem sesquilinear_unique : Specs.D05.M15.InnerTensor.sesquilinear_unique := by
  intro F V W _ _ _ _ _ h hl hr hp
  have hadd_left (x y z : V ⊗[F] W) : h (x + y) z = h x z + h y z := by
    simpa using hl 1 1 x y z
  have hadd_right (x y z : V ⊗[F] W) : h x (y + z) = h x y + h x z := by
    simpa using hr 1 1 x y z
  funext z t
  induction z using TensorProduct.inductionOn with
  | tmul v w =>
      induction t using TensorProduct.inductionOn with
      | tmul v' w' => exact (hp v v' w w').trans (pure_tensor v v' w w').symm
      | add t₁ t₂ ih₁ ih₂ =>
          simp only [hadd_right, D05.firstInner, inner_add_left] at *
          rw [ih₁, ih₂]
  | add z₁ z₂ ih₁ ih₂ =>
      simp only [hadd_left, D05.firstInner, inner_add_right] at *
      rw [ih₁, ih₂]

theorem exists_unique : Specs.D05.M15.InnerTensor.exists_unique := by
  intro F V W _ _ _ _ _ _ _
  refine ⟨D05.firstInner (F := F), ⟨canonical_axioms, pure_tensor⟩, ?_⟩
  intro h hh
  exact sesquilinear_unique h hh.1.1
    (D05.M12.InnerProduct.second_slot_of_axioms h hh.1) hh.2

theorem basis_independence : Specs.D05.M15.InnerTensor.basis_independence := by
  intro F V W I J I' J' _ _ _ _ _ _ _ _ _ e f e' f' he hf he' hf'
  funext z t
  exact (coordinate_eq_canonical e f he hf z t).trans
    (coordinate_eq_canonical e' f' he' hf' z t).symm

theorem orthonormal_tensor_basis : Specs.D05.M15.InnerTensor.orthonormal_tensor_basis := by
  intro F V W I J _ _ _ _ _ e f he hf
  obtain ⟨B, hB⟩ := D05.M15.TensorBasis.tensor_basis e f
  refine ⟨B, hB, ?_⟩
  apply (D05.M12.Orthonormal.orthonormal_iff_mathlib B).mpr
  have ho := ((D05.M12.Orthonormal.orthonormal_iff_mathlib e).mp he).tmul
    ((D05.M12.Orthonormal.orthonormal_iff_mathlib f).mp hf)
  have hfamily : (B : I × J → V ⊗[F] W) = fun p => e p.1 ⊗ₜ[F] f p.2 := funext hB
  rw [hfamily]
  exact ho

end D05.M15.InnerTensor
