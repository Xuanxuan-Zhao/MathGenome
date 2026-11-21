import MathGenome.Internal.Specs.D05.M15.TensorDualHom
import MathGenome.Internal.D05.M03.BasisExtension
import MathGenome.Internal.D05.M07.DualBasis
import MathGenome.Internal.D05.M15.TensorUniversal

/-! K05.15.tensor_dual_hom: the canonical tensor–Hom map and its finite-basis inverse. -/

namespace D05.M15.TensorDualHom

open scoped TensorProduct

/-- Canonical in arbitrary dimensions; also used by the later finite-rank goal. -/
abbrev phi (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :=
  Specs.D05.M15.TensorDualHom.phi K V W

/-- The inverse map expressed in any given finite basis. -/
noncomputable abbrev psi {K V W I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Fintype I] (b : Module.Basis I K V) :=
  Specs.D05.M15.TensorDualHom.psi (W := W) b

theorem phi_tmul : Specs.D05.M15.TensorDualHom.phi_tmul := by
  intro K V W _ _ _ _ _ f w v
  rfl

theorem bilinear_assignment : Specs.D05.M15.TensorDualHom.bilinear_assignment := by
  intro K V W _ _ _ _ _
  exact ⟨LinearMap.smulRightₗ, fun _ _ _ => rfl, rfl⟩

theorem phi_unique : Specs.D05.M15.TensorDualHom.phi_unique := by
  intro K V W _ _ _ _ _ L hL
  apply TensorProduct.ext
  ext f w v
  exact hL f w v

theorem psi_apply : Specs.D05.M15.TensorDualHom.psi_apply := by
  intro K V W I _ _ _ _ _ _ b T
  simp only [Specs.D05.M15.TensorDualHom.psi, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, TensorProduct.mk_apply]

/-- Applying T to the vector expansion proves Phi Psi = id. -/
theorem phi_psi : Specs.D05.M15.TensorDualHom.phi_psi := by
  intro K V W I _ _ _ _ _ _ b T
  rw [psi_apply b T]
  ext v
  change (dualTensorHom K V W (∑ i, b.coord i ⊗ₜ[K] T (b i))) v = T v
  calc
    _ = ∑ i, b.coord i v • T (b i) := by
      simp only [map_sum, LinearMap.sum_apply, dualTensorHom_apply]
    _ = T (∑ i, b.repr v i • b i) := by
      simp only [map_sum, T.map_smul, Module.Basis.coord_apply]
    _ = T v := congrArg T (b.sum_repr v)

/-- The other composite is checked on elementary tensors, using the upstream
functional expansion in the dual coordinate family. -/
theorem psi_phi : Specs.D05.M15.TensorDualHom.psi_phi := by
  intro K V W I _ _ _ _ _ _ b t
  have h : (psi (W := W) b).comp (phi K V W) = LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro w
    change psi b (phi K V W (f ⊗ₜ[K] w)) = f ⊗ₜ[K] w
    rw [psi_apply b]
    simp only [dualTensorHom_apply, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
    rw [← D05.M07.DualBasis.functional_expansion b f]
  exact LinearMap.congr_fun h t

theorem finite_dimensional_equivalence :
    Specs.D05.M15.TensorDualHom.finite_dimensional_equivalence := by
  intro K V W _ _ _ _ _ _
  exact ⟨dualTensorHomEquiv K V W, rfl⟩

theorem inverse_formula : Specs.D05.M15.TensorDualHom.inverse_formula := by
  intro K V W I _ _ _ _ _ _ b E hE T
  rw [← psi_apply b T]
  apply E.injective
  calc
    E (E.symm T) = T := E.apply_symm_apply T
    _ = phi K V W (psi b T) := (phi_psi b T).symm
    _ = E (psi b T) := (LinearMap.congr_fun hE _).symm

theorem basis_independent : Specs.D05.M15.TensorDualHom.basis_independent := by
  intro K V W I J _ _ _ _ _ _ _ b c
  ext T
  calc
    psi b T = psi b (phi K V W (psi c T)) := by rw [phi_psi c T]
    _ = psi c T := psi_phi b _

/-- A finite sum of tensors has image in the span of its finitely many
second factors, regardless of the dimensions of V and W. -/
theorem finite_rank : Specs.D05.M15.TensorDualHom.finite_rank := by
  intro K V W _ _ _ _ _ t
  classical
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  let S := Submodule.span K (↑(s.image Prod.snd) : Set W)
  have hle : (phi K V W (∑ p ∈ s, p.1 ⊗ₜ[K] p.2)).range ≤ S := by
    rintro w ⟨v, rfl⟩
    simp only [map_sum, LinearMap.sum_apply]
    change (∑ p ∈ s, p.1 v • p.2) ∈ S
    apply Submodule.sum_mem
    intro p hp
    apply S.smul_mem
    exact Submodule.subset_span (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  let : FiniteDimensional K S := FiniteDimensional.span_finset K _
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

theorem identity_not_in_range : Specs.D05.M15.TensorDualHom.identity_not_in_range := by
  intro K V _ _ _ hV ht
  exact hV (Module.Finite.of_one_mem_range_dualTensorHom ht)

end D05.M15.TensorDualHom
