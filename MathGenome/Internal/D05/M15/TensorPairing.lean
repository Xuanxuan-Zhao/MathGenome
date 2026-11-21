import MathGenome.Internal.Specs.D05.M15.TensorPairing
import MathGenome.Internal.D05.M15.TensorBasis
import MathGenome.Internal.D05.M07.DualBasis
import MathGenome.Internal.D05.M07.Biddual
import Mathlib.LinearAlgebra.Contraction

/-! K05.15.tensor_pairing: canonical algebraic dual tensor evaluation and its
finite-dimensional representations. The canonical maps remain available
without finite dimension; only the perfect-pairing statements require it. -/
namespace D05.M15.TensorPairing

open scoped TensorProduct

/-- Canonical dual tensor evaluation, with no dimensional restriction. -/
abbrev evaluation (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :
    (Module.Dual K V ⊗[K] Module.Dual K W) →ₗ[K] Module.Dual K (V ⊗[K] W) :=
  TensorProduct.dualDistrib K V W

theorem evaluation_apply : Specs.D05.M15.TensorPairing.evaluation_apply := by
  intro K V W _ _ _ _ _ φ ψ v w
  rfl

theorem evaluation_unique : Specs.D05.M15.TensorPairing.evaluation_unique := by
  intro K V W _ _ _ _ _ F hF
  ext φ ψ v w
  exact hF φ ψ v w

/-- The coordinate identity is meaningful for arbitrary bases. In finite
dimension the coordinate families are the full dual bases, so this is the
basis-to-dual-basis description of the canonical isomorphism. -/
theorem coordinate_functionals : Specs.D05.M15.TensorPairing.coordinate_functionals := by
  intro K V W I J _ _ _ _ _ e f i j
  ext v w
  change e.repr v i * f.repr w j = (e.tensorProduct f).repr (v ⊗ₜ[K] w) (i, j)
  simp only [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]

theorem perfect_pairing : Specs.D05.M15.TensorPairing.perfect_pairing := by
  intro K V W _ _ _ _ _ _ _
  exact ⟨TensorProduct.dualDistribEquiv K V W,
    TensorProduct.toLinearMap_dualDistribEquiv⟩

/-- Compose the proved dual tensor equivalence with the inverse of the
binary universal-property equivalence. -/
theorem bilinear_forms : Specs.D05.M15.TensorPairing.bilinear_forms := by
  intro K V W _ _ _ _ _ _ _
  obtain ⟨E, hE⟩ := perfect_pairing (K := K) (V := V) (W := W)
  refine ⟨E.trans (TensorProduct.lift.equiv (RingHom.id K) V W K).symm, ?_⟩
  intro z v w
  change E z (v ⊗ₜ[K] w) = _
  exact congrArg (fun L : _ →ₗ[K] Module.Dual K (V ⊗[K] W) =>
    L z (v ⊗ₜ[K] w)) hE

theorem unique_bilinear_representation :
    Specs.D05.M15.TensorPairing.unique_bilinear_representation := by
  intro K V W _ _ _ _ _ _ _ b
  obtain ⟨E, hE⟩ := bilinear_forms (K := K) (V := V) (W := W)
  refine ⟨E.symm b, ?_, ?_⟩
  · intro v w
    rw [← hE, E.apply_symm_apply]
  · intro z hz
    apply E.injective
    rw [E.apply_symm_apply]
    ext v w
    rw [hE]
    exact hz v w

/-- Tensor finite bidual evaluation, then use the same perfect pairing and
universal property on the two dual spaces. -/
theorem primal_bilinear_forms : Specs.D05.M15.TensorPairing.primal_bilinear_forms := by
  intro K V W _ _ _ _ _ _ _
  obtain ⟨jV, hjV, _⟩ := D05.M07.Biddual.canonical_isomorphism (K := K) (V := V)
  obtain ⟨jW, hjW, _⟩ := D05.M07.Biddual.canonical_isomorphism (K := K) (V := W)
  obtain ⟨E, hE⟩ := bilinear_forms
    (K := K) (V := Module.Dual K V) (W := Module.Dual K W)
  refine ⟨(TensorProduct.congr jV jW).trans E, ?_⟩
  intro v w φ ψ
  change E ((TensorProduct.congr jV jW) (v ⊗ₜ[K] w)) φ ψ = _
  simp only [TensorProduct.congr_tmul]
  rw [hE, TensorProduct.dualDistrib_apply, hjV, hjW]

/-- Canonical finite-family evaluation, including the empty family. -/
noncomputable abbrev finite_evaluation (K I : Type*) (V : I → Type*)
    [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] :
    PiTensorProduct K (fun i => Module.Dual K (V i)) →ₗ[K]
      Module.Dual K (PiTensorProduct K V) :=
  PiTensorProduct.dualDistrib

theorem finite_evaluation_apply : Specs.D05.M15.TensorPairing.finite_evaluation_apply := by
  intro K I V _ _ _ _ φ v
  exact PiTensorProduct.dualDistrib_apply φ v

theorem finite_coordinate_functionals :
    Specs.D05.M15.TensorPairing.finite_coordinate_functionals := by
  intro K I V J _ _ _ _ e p
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change PiTensorProduct.dualDistrib (R := K) (M := V)
    (PiTensorProduct.tprod K (fun i => (e i).coord (p i)))
    (PiTensorProduct.tprod K v) =
    (Basis.piTensorProduct e).repr (PiTensorProduct.tprod K v) p
  simp only [PiTensorProduct.dualDistrib_apply, Module.Basis.coord_apply,
    _root_.Basis.piTensorProduct_repr_tprod_apply]

theorem finite_perfect_pairing : Specs.D05.M15.TensorPairing.finite_perfect_pairing := by
  intro K I V _ _ _ _ _
  exact ⟨PiTensorProduct.dualDistribEquiv, rfl⟩

theorem finite_multilinear_forms : Specs.D05.M15.TensorPairing.finite_multilinear_forms := by
  intro K I V _ _ _ _ _
  obtain ⟨E, hE⟩ := finite_perfect_pairing (K := K) (V := V)
  refine ⟨E.trans PiTensorProduct.lift.symm, ?_⟩
  intro φ v
  change E (PiTensorProduct.tprod K φ) (PiTensorProduct.tprod K v) = _
  change E.toLinearMap _ _ = _
  rw [hE]
  exact finite_evaluation_apply φ v

theorem nullary_pairing : Specs.D05.M15.TensorPairing.nullary_pairing := by
  intro K I V _ _ _ _ _ a b
  simp [PiTensorProduct.dualDistrib_apply, mul_comm]

end D05.M15.TensorPairing
