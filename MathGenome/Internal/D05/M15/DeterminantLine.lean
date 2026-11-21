import MathGenome.Internal.Specs.D05.M15.DeterminantLine
import MathGenome.Internal.D05.M15.ExteriorBasis
import MathGenome.Internal.D05.M15.WedgeSign
import MathGenome.Internal.D05.M05.OperatorDet
import MathGenome.Internal.D05.M04.MatrixOfMap

/-! The determinant scalar on the actual top exterior power. -/

noncomputable section
namespace D05.M15.DeterminantLine

open Specs.D05.M15.DeterminantLine

/-- The usual determinant expansion also holds for vector-valued alternating
maps. It follows by testing on tuples of distinct basis vectors. -/
theorem alternating_eq_det_smul {K V H : Type*}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup H] [Module K H]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (f : AlternatingMap K V H (Fin n)) :
    f = b.det.smulRight (f b) := by
  refine Module.Basis.ext_alternating b fun i hi => ?_
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
  change f (b ∘ σ) = b.det.smulRight (f b) (b ∘ σ)
  simp [AlternatingMap.map_perm, Module.Basis.det_self]

theorem wedge_expansion : Specs.D05.M15.DeterminantLine.wedge_expansion := by
  intro K V _ _ _ n b x
  have h := congrArg (fun f : AlternatingMap K V (⋀[K]^n V) (Fin n) => f x)
    (alternating_eq_det_smul b (exteriorPower.ιMulti K n))
  rw [D05.M05.DetDefinition.matrix_det_bridge]
  have hm : b.toMatrix x = Matrix.of (fun i j => b.repr (x j) i) := by
    ext i j
    rfl
  simpa [Module.Basis.det_apply, hm, volume] using h

/-- Evaluation by the descended basis determinant detects the volume vector. -/
theorem volume_ne_zero {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) : volume b ≠ 0 := by
  intro h
  have h' := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h
  simp [volume, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Module.Basis.det_self] at h'

theorem top_wedge_basis : Specs.D05.M15.DeterminantLine.top_wedge_basis := by
  intro K V _ _ _ n b
  have hd : Module.finrank K (⋀[K]^n V) = 1 := by
    simpa using D05.M15.ExteriorBasis.dimension_of_finite_basis n b n
  exact ⟨FiniteDimensional.basisSingleton (Fin 1) hd (volume b) (volume_ne_zero b),
    FiniteDimensional.basisSingleton_apply _ _ _ _ _⟩

theorem leibniz_action : Specs.D05.M15.DeterminantLine.leibniz_action := by
  intro K V _ _ _ n b T
  simpa [D05.M05.determinant, Specs.D05.M04.MatrixOfMap.matrixOfMap_value,
    LinearMap.toMatrix_apply, Function.comp_def] using wedge_expansion b (T ∘ b)

theorem matrix_action : Specs.D05.M15.DeterminantLine.matrix_action := by
  intro K V _ _ _ n b T A hA
  have hm := D05.M04.MatrixOfMap.unique_matrix_from_basis b b T A hA
  rw [hm, D05.M15.WedgeSign.power_map_elementary]
  have h := wedge_expansion b (T ∘ b)
  have hM : Matrix.of (fun i j => b.repr ((T ∘ b) j) i) =
      Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T := by
    ext i j
    exact (D05.M04.MatrixOfMap.matrix_entry b b T i j).symm
  rw [hM] at h
  exact h

theorem top_power_in_basis : Specs.D05.M15.DeterminantLine.top_power_in_basis := by
  intro K V _ _ _ n b T
  obtain ⟨B, hB⟩ := top_wedge_basis b
  apply B.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [hB, LinearMap.smul_apply, LinearMap.id_apply]
  exact matrix_action b T _ (D05.M04.MatrixOfMap.basis_image b b T)

theorem top_power_operator_det : Specs.D05.M15.DeterminantLine.top_power_operator_det := by
  intro K V _ _ _ _ T
  rw [D05.M05.OperatorDet.operatorDet_eq_detInBasis (Module.finBasis K V)]
  exact top_power_in_basis (Module.finBasis K V) T

theorem exterior_algebra_action : Specs.D05.M15.DeterminantLine.exterior_algebra_action := by
  intro K V _ _ _ n b T z
  rw [← D05.M15.WedgeSign.power_restriction T n z, top_power_in_basis b T]
  rfl

theorem rescaled_volume : Specs.D05.M15.DeterminantLine.rescaled_volume := by
  intro K V _ _ _ n b T c hc
  have h : Specs.D05.M15.WedgeSign.powerMap_value n T (c • volume b) =
      Specs.D05.M05.OperatorDet.detInBasis_value b T • (c • volume b) := by
    rw [top_power_in_basis b T]
    rfl
  refine ⟨h, ?_⟩
  intro a ha
  have hn : c • volume b ≠ 0 := smul_ne_zero hc (volume_ne_zero b)
  exact smul_left_injective K hn (ha.symm.trans h)

theorem degree_zero_identity : Specs.D05.M15.DeterminantLine.degree_zero_identity := by
  intro K V _ _ _ T
  have h : Specs.D05.M15.WedgeSign.powerMap_value 0 T = LinearMap.id := by
    apply LinearMap.ext
    intro z
    apply (exteriorPower.zeroEquiv K V).injective
    exact D05.M15.WedgeSign.power_map_zero T z
  refine ⟨h, ?_⟩
  intro a
  rw [h, LinearMap.id_apply, LinearEquiv.apply_symm_apply]

theorem zero_dim_scalar : Specs.D05.M15.DeterminantLine.zero_dim_scalar := by
  intro K V _ _ _ b T
  exact ⟨D05.M05.OperatorDet.detInBasis_empty b T,
    _root_.ExteriorAlgebra.ιMulti_zero_apply b⟩

end D05.M15.DeterminantLine
