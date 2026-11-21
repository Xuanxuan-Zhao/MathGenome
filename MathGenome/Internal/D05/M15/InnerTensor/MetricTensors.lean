import MathGenome.Internal.Specs.D05.M15.InnerTensor.MetricTensors
import MathGenome.Internal.D05.M11.Nondegenerate
import MathGenome.Internal.D05.M15.TensorPairing
import MathGenome.Internal.D05.M15.TensorDualHom

/-! Metric tensors of finite-dimensional nondegenerate symmetric bilinear forms.
The contraction orientation is explicit, so transposes cannot be suppressed
without the symmetry hypothesis. All arguments include the zero space. -/
namespace D05.M15.InnerTensor.MetricTensors

open Module Matrix
open scoped TensorProduct
open Specs.D05.M11.FormMatrix

noncomputable abbrev covariant := @Specs.D05.M15.InnerTensor.MetricTensors.covariant
noncomputable abbrev contravariant := @Specs.D05.M15.InnerTensor.MetricTensors.contravariant
abbrev firstContraction := Specs.D05.M15.InnerTensor.MetricTensors.firstContraction
abbrev metricContraction := Specs.D05.M15.InnerTensor.MetricTensors.metricContraction

theorem contraction_tmul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v w : V) (φ : Dual K V) : firstContraction K V (v ⊗ₜ[K] w) φ = φ v • w := rfl

theorem covariant_evaluation : Specs.D05.M15.InnerTensor.MetricTensors.covariant_evaluation := by
  intro K V _ _ _ n e B v w
  have h : TensorProduct.dualDistrib K V V (covariant e B) = TensorProduct.lift B := by
    apply TensorProduct.ext
    apply e.ext
    intro i
    apply e.ext
    intro j
    simp [covariant, Specs.D05.M15.InnerTensor.MetricTensors.covariant,
      TensorProduct.dualDistrib_apply, Module.Basis.coord_apply,
      Finsupp.single_apply, formMatrix_value]
  exact LinearMap.congr_fun h (v ⊗ₜ[K] w)

theorem metric_contraction_tmul :
    Specs.D05.M15.InnerTensor.MetricTensors.metric_contraction_tmul := by
  intro K V _ _ _ α β v w
  exact (TensorProduct.smul_tmul' (α v) β w).symm

theorem covariant_to_flat : Specs.D05.M15.InnerTensor.MetricTensors.covariant_to_flat := by
  intro K V _ _ _ n e B
  apply e.ext
  intro i
  apply e.ext
  intro j
  simp [Specs.D05.M15.InnerTensor.MetricTensors.covariant,
    Module.Basis.coord_apply, Finsupp.single_apply, formMatrix_value]

theorem covariant_basis_independent :
    Specs.D05.M15.InnerTensor.MetricTensors.covariant_basis_independent := by
  intro K V _ _ _ n m e f B
  let _ := Module.Finite.of_basis e
  obtain ⟨E, hE⟩ := D05.M15.TensorPairing.perfect_pairing (K := K) (V := V) (W := V)
  apply E.injective
  change E.toLinearMap _ = E.toLinearMap _
  rw [hE]
  apply TensorProduct.ext
  ext v w
  exact (covariant_evaluation e B v w).trans (covariant_evaluation f B v w).symm

theorem flat_isomorphism : Specs.D05.M15.InnerTensor.MetricTensors.flat_isomorphism := by
  intro K V _ _ _ _ B hB
  have hi : Function.Injective B := LinearMap.ker_eq_bot.mp
    (LinearMap.separatingLeft_iff_ker_eq_bot.mp hB.1)
  have hs : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp hi
  exact ⟨LinearEquiv.ofBijective B ⟨hi, hs⟩, rfl⟩

theorem flat_matrix : Specs.D05.M15.InnerTensor.MetricTensors.flat_matrix := by
  intro K V _ _ _ n e B hB
  refine ⟨D05.M11.Nondegenerate.toDual_matrix e B, ?_⟩
  ext i j
  exact hB.eq (e j) (e i)

/-- Coordinates of a finite coefficient expansion in a tensor basis. -/
lemma tensor_coefficients {K U W I J : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : Basis I K U) (f : Basis J K W) (A : Matrix I J K) (i : I) (j : J) :
    (e.tensorProduct f).repr (∑ a, ∑ b, A a b • (e a ⊗ₜ[K] f b)) (i,j) = A i j := by
  simp [map_sum, map_smul,
    Module.Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]

theorem covariant_coefficients : Specs.D05.M15.InnerTensor.MetricTensors.covariant_coefficients := by
  intro K V _ _ _ n e B i j
  change (e.dualBasis.tensorProduct e.dualBasis).repr
    (∑ a, ∑ b, formMatrix_value e B a b • (e.coord a ⊗ₜ[K] e.coord b)) (i,j) = _
  simpa only [Module.Basis.coe_dualBasis] using
    tensor_coefficients e.dualBasis e.dualBasis (formMatrix_value e B) i j

theorem contravariant_coefficients :
    Specs.D05.M15.InnerTensor.MetricTensors.contravariant_coefficients := by
  intro K V _ _ _ n e B i j
  exact tensor_coefficients e e (formMatrix_value e B)⁻¹ i j

lemma inverse_gram_symmetric {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    ((formMatrix_value e B)⁻¹)ᵀ = (formMatrix_value e B)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, (flat_matrix e B hB).2]

theorem contravariant_coordinates :
    Specs.D05.M15.InnerTensor.MetricTensors.contravariant_coordinates := by
  intro K V _ _ _ n e B hB φ i
  have hs (j : Fin n) : (formMatrix_value e B)⁻¹ j i = (formMatrix_value e B)⁻¹ i j :=
    congrArg (fun A : Matrix (Fin n) (Fin n) K => A i j) (inverse_gram_symmetric e B hB)
  simp only [Specs.D05.M15.InnerTensor.MetricTensors.contravariant,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [contraction_tmul, map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply, hs]

/-- Nondegeneracy makes the Gram determinant a unit, including size zero. -/
lemma gram_det_isUnit {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) :
    IsUnit (formMatrix_value e B).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp ((D05.M11.Nondegenerate.nondegenerate_iff_matrix e B).mp hB)

/-- In coordinates the contraction is exactly multiplication by G⁻¹. -/
lemma contraction_matrix {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (e : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    LinearMap.toMatrix e.dualBasis e (firstContraction K V (contravariant e B)) =
      (formMatrix_value e B)⁻¹ := by
  ext i j
  rw [LinearMap.toMatrix_apply, contravariant_coordinates e B hB]
  simp [Finsupp.single_apply]

theorem contravariant_inverse : Specs.D05.M15.InnerTensor.MetricTensors.contravariant_inverse := by
  intro K V _ _ _ n e B hs hn
  have hG := gram_det_isUnit e B hn
  have hflat : LinearMap.toMatrix e e.dualBasis B = formMatrix_value e B :=
    (flat_matrix e B hs).1.trans (flat_matrix e B hs).2
  constructor
  · apply (LinearMap.toMatrix e.dualBasis e.dualBasis).injective
    rw [LinearMap.toMatrix_comp e.dualBasis e e.dualBasis, hflat,
      contraction_matrix e B hs, Matrix.mul_nonsing_inv _ hG, LinearMap.toMatrix_id]
  · apply (LinearMap.toMatrix e e).injective
    rw [LinearMap.toMatrix_comp e e.dualBasis e, hflat,
      contraction_matrix e B hs, Matrix.nonsing_inv_mul _ hG, LinearMap.toMatrix_id]

theorem contraction_equivalence : Specs.D05.M15.InnerTensor.MetricTensors.contraction_equivalence := by
  intro K V _ _ _ _
  refine ⟨(TensorProduct.congr (Module.evalEquiv K V) (LinearEquiv.refl K V)).trans
    (dualTensorHomEquiv K (Dual K V) V), ?_⟩
  rfl

theorem contravariant_basis_independent :
    Specs.D05.M15.InnerTensor.MetricTensors.contravariant_basis_independent := by
  intro K V _ _ _ n m e f B hs hn
  let _ := Module.Finite.of_basis e
  obtain ⟨E, hE⟩ := contraction_equivalence (K := K) (V := V)
  obtain ⟨F, hF⟩ := flat_isomorphism B hn
  apply E.injective
  change E.toLinearMap _ = E.toLinearMap _
  rw [hE]
  ext φ
  apply F.injective
  change F.toLinearMap _ = F.toLinearMap _
  rw [hF]
  exact (LinearMap.congr_fun (contravariant_inverse e B hs hn).1 φ).trans
    (LinearMap.congr_fun (contravariant_inverse f B hs hn).1 φ).symm

/-- Tensor–Hom intertwines applying b-flat to the first vector factor with
precomposing the first contraction by b-flat; symmetry fixes the slot order. -/
lemma mixed_contraction_hom {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hs : B.IsSymm) (t : V ⊗[K] V) :
    dualTensorHom K V V (TensorProduct.map B (LinearMap.id : V →ₗ[K] V) t) =
      (firstContraction K V t).comp B := by
  induction t using TensorProduct.inductionOn with
  | tmul v w =>
      ext x
      change B v x • w = B x v • w
      rw [hs.eq v x]
  | add x y hx hy =>
      simp only [map_add, hx, hy, LinearMap.add_comp]

theorem mixed_contraction_identity :
    Specs.D05.M15.InnerTensor.MetricTensors.mixed_contraction_identity := by
  intro K V _ _ _ n e B hs hn
  let _ := Module.Finite.of_basis e
  apply (dualTensorHomEquiv K V V).injective
  change dualTensorHom K V V _ = dualTensorHom K V V _
  rw [mixed_contraction_hom B hs, (contravariant_inverse e B hs hn).2]
  have hp := D05.M15.TensorDualHom.phi_psi e (LinearMap.id : V →ₗ[K] V)
  rw [D05.M15.TensorDualHom.psi_apply e (LinearMap.id : V →ₗ[K] V)] at hp
  exact hp.symm

theorem metric_contraction_identity :
    Specs.D05.M15.InnerTensor.MetricTensors.metric_contraction_identity := by
  intro K V _ _ _ n e B hs hn
  unfold Specs.D05.M15.InnerTensor.MetricTensors.metricContraction
  rw [covariant_to_flat e B]
  exact mixed_contraction_identity e B hs hn

theorem contraction_coefficients : Specs.D05.M15.InnerTensor.MetricTensors.contraction_coefficients := by
  intro K V _ _ _ n e B hn i k
  exact congrArg (fun A : Matrix (Fin n) (Fin n) K => A i k)
    (Matrix.mul_nonsing_inv _ (gram_det_isUnit e B hn))

theorem orthonormal_sums : Specs.D05.M15.InnerTensor.MetricTensors.orthonormal_sums := by
  intro K V _ _ _ n e B hG
  constructor
  · simp [Specs.D05.M15.InnerTensor.MetricTensors.covariant, hG, Matrix.one_apply]
  · simp [Specs.D05.M15.InnerTensor.MetricTensors.contravariant, hG, Matrix.one_apply]

theorem identity_coefficients_iff : Specs.D05.M15.InnerTensor.MetricTensors.identity_coefficients_iff := by
  intro K V _ _ _ n e B
  constructor
  · exact ⟨fun h i j => congrArg (fun A : Matrix (Fin n) (Fin n) K => A i j) h,
      fun h => Matrix.ext h⟩
  · constructor
    · intro h
      have hu : IsUnit (formMatrix_value e B)⁻¹ := h.symm ▸ isUnit_one
      have hG := Matrix.isUnit_nonsing_inv_iff.mp hu
      have hx := Matrix.mul_nonsing_inv (formMatrix_value e B)
        ((Matrix.isUnit_iff_isUnit_det _).mp hG)
      simpa only [h, Matrix.mul_one] using hx
    · intro h
      simp [h]

end D05.M15.InnerTensor.MetricTensors
