import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Naturality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.BaseChange

/-! KD-17: arbitrary base change and coherence for the universal differential. -/
namespace AdvCommAlg.Differentials

open TensorProduct
open Specs.AdvCommAlg.Differentials (baseChangeEquivValue)
universe u v w z t q
noncomputable section

/-- The canonical scalar extension isomorphism for any pushout realization. -/
def baseChangeEquiv : Specs.AdvCommAlg.Differentials.baseChangeEquivType.{u,v,w,z} :=
  fun R S B C _ _ _ _ _ _ _ _ _ _ _ _ =>
    KaehlerDifferential.tensorKaehlerEquiv R S B C

theorem baseChange_formula : Specs.AdvCommAlg.Differentials.baseChangeFormula := by
  intro R S B C _ _ _ _ _ _ _ _ _ _ _ _ c b
  exact KaehlerDifferential.tensorKaehlerEquiv_tmul_D R S B C c b

section
variable (R : Type u) (S : Type v) (B : Type w) (C : Type z)
  [CommRing R] [CommRing S] [CommRing B] [CommRing C]
  [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
  [IsScalarTower R S C] [IsScalarTower R B C] [Algebra.IsPushout R S B C]

/-- The isomorphism is scalar extension of the natural map of differentials. -/
theorem baseChangeEquiv_tmul (c : C) (ω : KaehlerDifferential R B) :
    baseChangeEquivValue R S B C (c ⊗ₜ ω) = c • KaehlerDifferential.map R S B C ω := by
  have h :
      ((baseChangeEquivValue R S B C).toLinearMap.restrictScalars B).comp
        (TensorProduct.mk B C (KaehlerDifferential R B) c) =
      ((LinearMap.lsmul C (KaehlerDifferential S C) c).restrictScalars B).comp
        (KaehlerDifferential.map R S B C) := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    change baseChangeEquivValue R S B C (c ⊗ₜ KaehlerDifferential.D R B b) =
      c • KaehlerDifferential.map R S B C (KaehlerDifferential.D R B b)
    rw [KaehlerDifferential.map_D]
    exact baseChange_formula R S B C c b
  exact congrArg (fun L : KaehlerDifferential R B →ₗ[B] KaehlerDifferential S C => L ω) h
end

theorem baseChange_naturality : Specs.AdvCommAlg.Differentials.baseChangeNaturality := by
  intro R S B C _ _ _ _ _ _ _ _ _ _ _ _ c ω
  rw [baseChangeEquiv_tmul]
  congr 1
  let f : B →+* C := algebraMap B C
  have h : f.comp (algebraMap R B) = (algebraMap S C).comp (algebraMap R S) := by
    rw [← IsScalarTower.algebraMap_eq R B C, ← IsScalarTower.algebraMap_eq R S C]
  have hm : ∀ b, Specs.AdvCommAlg.Differentials.algebraDifferentialMapValue
      (algebraMap R S) f h (KaehlerDifferential.D R B b) =
        KaehlerDifferential.D S C (f b) := algebraDifferentialMap_apply _ _ h
  have hx : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact (KaehlerDifferential.map_D R S B C b).trans (hm b).symm
  | zero => simp
  | add x y hx hy ex ey => simp only [map_add, ex, ey]
  | smul b x hx ex =>
    change KaehlerDifferential.map R S B C (b • x) =
      algebraDifferentialMap (algebraMap R S) (algebraMap B C) h (b • x)
    have ex' : KaehlerDifferential.map R S B C x =
        algebraDifferentialMap (algebraMap R S) (algebraMap B C) h x := ex
    rw [map_smul, algebraDifferentialMap_smul, ← ex',
      IsScalarTower.algebraMap_smul]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem baseChange_tensor_formula :
    Specs.AdvCommAlg.Differentials.baseChangeTensorFormula := by
  intro R S B _ _ _ _ _ c b
  exact baseChange_formula R S B (S ⊗[R] B) c b

theorem baseChange_identity : Specs.AdvCommAlg.Differentials.baseChangeIdentity := by
  intro R B _ _ _
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply Derivation.liftKaehlerDifferential_unique
  ext b
  change baseChangeEquivValue R R B B (c ⊗ₜ KaehlerDifferential.D R B b) =
    c • KaehlerDifferential.D R B b
  exact baseChange_formula R R B B c b

theorem baseChange_composition : Specs.AdvCommAlg.Differentials.baseChangeComposition := by
  intro R S T B C F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have : Algebra.IsPushout R T B F :=
    (Algebra.IsPushout.comp_iff R S B C (T := T)).mpr inferInstance
  intro x
  have h :
      (baseChangeEquivValue R T B F).toLinearMap.comp
        (AlgebraTensorModule.cancelBaseChange B C F F (KaehlerDifferential R B)).toLinearMap =
      (baseChangeEquivValue S T C F).toLinearMap.comp
        ((baseChangeEquivValue R S B C).toLinearMap.baseChange F) := by
    apply LinearMap.restrictScalars_injective C
    apply TensorProduct.ext
    apply LinearMap.ext
    intro d
    apply LinearMap.restrictScalars_injective B
    apply TensorProduct.ext
    apply LinearMap.ext
    intro c
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    change baseChangeEquivValue R T B F
        ((c • d) ⊗ₜ KaehlerDifferential.D R B b) =
      baseChangeEquivValue S T C F
        (d ⊗ₜ baseChangeEquivValue R S B C (c ⊗ₜ KaehlerDifferential.D R B b))
    rw [baseChange_formula, baseChange_formula, ← TensorProduct.smul_tmul,
      baseChange_formula, ← IsScalarTower.algebraMap_apply B C F]
  exact congrArg (fun L => L x) h

/-- Identity compatibility in the displayed tensor model. -/
theorem baseChange_tensor_identity :
    Specs.AdvCommAlg.Differentials.baseChangeTensorIdentity := by
  intro R B _ _ _ c b
  change algebraDifferentialMap (RingHom.id R) (Algebra.TensorProduct.lid R B).toRingHom
      (by ext a; exact (Algebra.TensorProduct.lid R B).commutes a)
      (baseChangeEquivValue R R B (R ⊗[R] B) (c ⊗ₜ KaehlerDifferential.D R B b)) = _
  rw [baseChange_tensor_formula, algebraDifferentialMap_smul]
  congr 1
  simpa [algebraDifferentialMap,
    Specs.AdvCommAlg.Differentials.algebraDifferentialMapValue] using
    algebraDifferentialMap_apply (RingHom.id R)
    (Algebra.TensorProduct.lid R B).toRingHom
    (by ext a; exact (Algebra.TensorProduct.lid R B).commutes a) (1 ⊗ₜ b)

/-- Composition compatibility through the concrete algebra tensor associator. -/
theorem baseChange_tensor_composition :
    Specs.AdvCommAlg.Differentials.baseChangeTensorComposition := by
  intro R S T B _ _ _ _ _ _ _ _ _ c b
  change algebraDifferentialMap (RingHom.id T)
    (Algebra.TensorProduct.cancelBaseChange R S T T B).toRingHom
    (by ext a; exact (Algebra.TensorProduct.cancelBaseChange R S T T B).commutes a)
    (baseChangeEquivValue S T (S ⊗[R] B) (T ⊗[S] (S ⊗[R] B))
      (c ⊗ₜ baseChangeEquivValue R S B (S ⊗[R] B)
        (1 ⊗ₜ KaehlerDifferential.D R B b))) = _
  rw [baseChange_tensor_formula, one_smul, baseChange_tensor_formula,
    algebraDifferentialMap_smul, baseChange_tensor_formula]
  congr 1
  simpa [algebraDifferentialMap,
    Specs.AdvCommAlg.Differentials.algebraDifferentialMapValue] using
    algebraDifferentialMap_apply (RingHom.id T)
    (Algebra.TensorProduct.cancelBaseChange R S T T B).toRingHom
    (by ext a; exact (Algebra.TensorProduct.cancelBaseChange R S T T B).commutes a)
    (1 ⊗ₜ (1 ⊗ₜ b))

end
end AdvCommAlg.Differentials
