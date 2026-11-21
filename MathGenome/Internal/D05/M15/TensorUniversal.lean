import MathGenome.Internal.D05.M15.Multilinear
import MathGenome.Internal.D05.M06.Quotient
import MathGenome.Internal.Specs.D05.M15.TensorUniversal

/-! K05.15.tensor_universal: universal properties and their spanning consequences. -/

namespace D05.M15.TensorUniversal

universe u
open scoped TensorProduct
open Specs.D05.M15.TensorUniversal (IsTensorProduct IsMultitensorProduct)

/-- The paper's binary tensor space is the canonical algebraic tensor product. -/
abbrev tensorProduct (K V W : Type u) [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] :=
  TensorProduct K V W

theorem binary_universal : Specs.D05.M15.TensorUniversal.binary_universal := by
  intro K V W _ _ _ _ _ H _ _ b
  exact ⟨TensorProduct.lift b, fun _ _ => rfl,
    fun f hf => TensorProduct.lift.unique hf⟩

theorem binary_linearization : Specs.D05.M15.TensorUniversal.binary_linearization := by
  intro K V W H _ _ _ _ _ _ _
  exact ⟨TensorProduct.lift.equiv (RingHom.id K) V W H,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- The quotient map and zero map factor the same zero bilinear map. Their
uniqueness forces every quotient class to be zero, hence every vector is in S. -/
theorem elementary_span_of_universal :
    Specs.D05.M15.TensorUniversal.elementary_span_of_universal := by
  intro K V W U _ _ _ _ _ _ _ τ hτ
  let S := Submodule.span K (Set.range (fun vw : V × W => τ vw.1 vw.2))
  obtain ⟨l, _, hl⟩ := hτ (U ⧸ S) (0 : V →ₗ[K] W →ₗ[K] U ⧸ S)
  have hq : S.mkQ = l := hl S.mkQ (by
    intro v w
    exact (Submodule.Quotient.mk_eq_zero S).mpr
      (Submodule.subset_span ⟨(v, w), rfl⟩))
  have hz : (0 : U →ₗ[K] U ⧸ S) = l := hl 0 (fun _ _ => rfl)
  have hzero : S.mkQ = 0 := hq.trans hz.symm
  apply top_unique
  intro u _
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQ u = 0
  rw [hzero]
  rfl

theorem linear_ext_of_universal :
    Specs.D05.M15.TensorUniversal.linear_ext_of_universal := by
  intro K V W U H _ _ _ _ _ _ _ _ _ τ hτ f g hfg
  obtain ⟨l, _, hl⟩ := hτ H (τ.compr₂ f)
  exact (hl f (fun _ _ => rfl)).trans (hl g (fun v w => (hfg v w).symm)).symm

theorem elementary_span : Specs.D05.M15.TensorUniversal.elementary_span := by
  intro K V W _ _ _ _ _
  exact elementary_span_of_universal (TensorProduct.mk K V W) binary_universal

theorem linear_ext : Specs.D05.M15.TensorUniversal.linear_ext := by
  intro K V W H _ _ _ _ _ _ _ f g hfg
  exact linear_ext_of_universal (TensorProduct.mk K V W) binary_universal f g hfg

theorem finite_universal : Specs.D05.M15.TensorUniversal.finite_universal := by
  intro K I V _ _ _ _ H _ _ b
  exact ⟨PiTensorProduct.lift b, fun _ => PiTensorProduct.lift.tprod _,
    fun f hf => PiTensorProduct.lift.unique hf⟩

theorem finite_linearization : Specs.D05.M15.TensorUniversal.finite_linearization := by
  intro K I H V _ _ _ _ _ _
  exact ⟨PiTensorProduct.lift, fun _ _ => PiTensorProduct.lift.tprod _,
    fun _ _ => rfl⟩

theorem finite_span_of_universal :
    Specs.D05.M15.TensorUniversal.finite_span_of_universal := by
  intro K I U V _ _ _ _ _ _ τ hτ
  let S := Submodule.span K (Set.range τ)
  obtain ⟨l, _, hl⟩ := hτ (U ⧸ S) (0 : MultilinearMap K V (U ⧸ S))
  have hq : S.mkQ = l := hl S.mkQ (by
    intro v
    exact (Submodule.Quotient.mk_eq_zero S).mpr
      (Submodule.subset_span ⟨v, rfl⟩))
  have hz : (0 : U →ₗ[K] U ⧸ S) = l := hl 0 (fun _ => rfl)
  have hzero : S.mkQ = 0 := hq.trans hz.symm
  apply top_unique
  intro u _
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQ u = 0
  rw [hzero]
  rfl

theorem finite_ext_of_universal :
    Specs.D05.M15.TensorUniversal.finite_ext_of_universal := by
  intro K I U H V _ _ _ _ _ _ _ _ τ hτ f g hfg
  obtain ⟨l, _, hl⟩ := hτ H (f.compMultilinearMap τ)
  exact (hl f (fun _ => rfl)).trans (hl g (fun v => (hfg v).symm)).symm

theorem nullary_equivalence : Specs.D05.M15.TensorUniversal.nullary_equivalence := by
  intro K I V _ _ _ _ _
  refine ⟨PiTensorProduct.isEmptyEquiv I, fun v => PiTensorProduct.isEmptyEquiv_apply_tprod I v,
    ?_⟩
  intro a
  change a • PiTensorProduct.tprod K _ = a • PiTensorProduct.tprod K 0
  congr 2
  exact Subsingleton.elim _ _

theorem nullary_universal : Specs.D05.M15.TensorUniversal.nullary_universal := by
  intro K I H V _ _ _ _ _ _ b
  refine ⟨(LinearMap.id : K →ₗ[K] K).smulRight (b 0), ?_, ?_⟩
  · intro v
    change (1 : K) • b 0 = b v
    rw [one_smul, Subsingleton.elim (0 : ∀ i, V i) v]
  · intro f hf
    apply LinearMap.ext
    intro a
    calc
      f a = f (a • (1 : K)) := by rw [smul_eq_mul, mul_one]
      _ = a • f 1 := f.map_smul a 1
      _ = a • b 0 := by rw [hf 0]
      _ = _ := rfl

end D05.M15.TensorUniversal
