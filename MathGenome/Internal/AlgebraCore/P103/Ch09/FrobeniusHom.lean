import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.FrobeniusHom
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionModels

noncomputable section
universe u v w x y
namespace P103.Ch09
set_option linter.style.haveILetI false
open scoped MonoidAlgebra
attribute [local instance] rightSubgroupModule
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {W : Type x} [AddCommGroup W] [Module k W]
variable (ρ : Representation k H V) (σ : Representation k G W)
variable (D : InductionData H ρ)

/-- Restriction of the algebra action agrees with inclusion of subgroup algebras. -/
theorem restrict_algebra_apply (b : k[H]) (z : W) :
    σ.asAlgebraHom (subgroupAlgebra H b) z = (restrict H σ).asAlgebraHom b z := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single h c => simp [restrict]

/-- An H-intertwiner commutes with the entire subgroup algebra. -/
theorem frobenius_balance (f : ρ.IntertwiningMap (restrict H σ))
    (a : k[G]) (b : k[H]) (z : V) :
    σ.asAlgebraHom (a * subgroupAlgebra H b) (f z) =
      σ.asAlgebraHom a (f (ρ.asAlgebraHom b z)) := by
  have hf : f (ρ.asAlgebraHom b z) = (restrict H σ).asAlgebraHom b (f z) := by
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b c hb hc => simp [hb, hc]
    | single h c =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply]
      rw [map_smul]
      exact congrArg (c • ·) (Representation.IntertwiningMap.isIntertwining _ _ f h z)
  rw [map_mul, Module.End.mul_apply, restrict_algebra_apply, hf]

/-- The balanced biadditive extension of `(g,z) ↦ σ(g)(f(z))`. -/
def frobeniusPairing (f : ρ.IntertwiningMap (restrict H σ)) :
    BalancedTensor.Pairing k[H] (A := k[G]) (B := ρ.asModule) W :=
  BalancedTensor.Pairing.ofFun
    (fun a z => σ.asAlgebraHom a (f (ρ.asModuleEquiv z)))
    (by intros; simp)
    (by intros; simp)
    (by
      intro b a z
      change σ.asAlgebraHom (a * subgroupAlgebra H b) (f (ρ.asModuleEquiv z)) = _
      rw [frobenius_balance]
      rfl)

def frobeniusLiftAdd (f : ρ.IntertwiningMap (restrict H σ)) : Induced H ρ →+ W :=
  BalancedTensor.lift (frobeniusPairing H ρ σ f)

@[simp] theorem frobeniusLiftAdd_tensor (f : ρ.IntertwiningMap (restrict H σ))
    (a : k[G]) (z : V) :
    frobeniusLiftAdd H ρ σ f (tensor H ρ a z) = σ.asAlgebraHom a (f z) := rfl

/-- Scalar linearity holds for any induced scalar structure with the tensor formula. -/
def frobeniusLiftLinear (f : ρ.IntertwiningMap (restrict H σ)) :
    letI := D.module; Induced H ρ →ₗ[k] W := by
  letI := D.module
  exact {
    toAddHom := frobeniusLiftAdd H ρ σ f
    map_smul' := by
      intro c z
      induction z using BalancedTensor.induction_on with
      | h0 => simp
      | ht a b =>
        change frobeniusLiftAdd H ρ σ f (c • tensor H ρ a (ρ.asModuleEquiv b)) =
          c • frobeniusLiftAdd H ρ σ f (tensor H ρ a (ρ.asModuleEquiv b))
        rw [D.scalar_tensor, frobeniusLiftAdd_tensor]
        simp
      | ha z z' hz hz' => simp_all [smul_add] }

/-- The inverse reciprocity map, already bundled as a G-intertwiner. -/
def frobeniusLift (f : ρ.IntertwiningMap (restrict H σ)) :
    letI := D.module; D.representation.IntertwiningMap σ := by
  letI := D.module
  exact {
    toLinearMap := frobeniusLiftLinear H ρ σ D f
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro z
      change frobeniusLiftLinear H ρ σ D f (D.representation g z) =
        σ g (frobeniusLiftLinear H ρ σ D f z)
      induction z using BalancedTensor.induction_on with
      | h0 => simp
      | ht a b =>
        change frobeniusLiftAdd H ρ σ f
          (D.representation g (tensor H ρ a (ρ.asModuleEquiv b))) =
            σ g (frobeniusLiftAdd H ρ σ f (tensor H ρ a (ρ.asModuleEquiv b)))
        rw [D.action_tensor, frobeniusLiftAdd_tensor]
        simp [map_mul, Module.End.mul_apply]
      | ha z z' hz hz' => simp_all }

@[simp] theorem frobeniusLift_tensor (f : ρ.IntertwiningMap (restrict H σ))
    (a : k[G]) (z : V) :
    letI := D.module
    frobeniusLift H ρ σ D f (tensor H ρ a z) = σ.asAlgebraHom a (f z) := rfl

/-- Evaluation at `1 ⊗ z` is H-equivariant by the balance relation. -/
def frobeniusEvaluate : letI := D.module
    D.representation.IntertwiningMap σ →ₗ[k] ρ.IntertwiningMap (restrict H σ) := by
  letI := D.module
  exact {
    toFun := fun F => {
      toLinearMap := {
        toFun := fun z => F (tensor H ρ 1 z)
        map_add' := by intros; simp [tensor_add_right]
        map_smul' := by
          intro c z
          rw [tensor_smul_right, ← D.scalar_tensor, map_smul]
          rfl }
      isIntertwining' := by
        intro h
        ext z
        change F (tensor H ρ 1 (ρ h z)) = σ h (F (tensor H ρ 1 z))
        rw [← tensor_balance_group, one_mul]
        have hf := Representation.IntertwiningMap.isIntertwining _ _ F (h : G) (tensor H ρ 1 z)
        simpa only [D.action_tensor, mul_one] using hf }
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem frobeniusEvaluate_apply : letI := D.module
    ∀ (F : D.representation.IntertwiningMap σ) (z : V),
      frobeniusEvaluate H ρ σ D F z = F (tensor H ρ 1 z) := by intros; rfl

/-- Group-basis tensors determine a linear map for every permitted scalar action. -/
theorem inductionData_hom_ext
    {F F' : letI := D.module; Induced H ρ →ₗ[k] W}
    (h : ∀ (g : G) (z : V),
      F (tensor H ρ (MonoidAlgebra.single g 1) z) =
      F' (tensor H ρ (MonoidAlgebra.single g 1) z)) : F = F' := by
  letI := D.module
  apply LinearMap.toAddMonoidHom_injective
  apply BalancedTensor.hom_ext
  intro a z
  change F (tensor H ρ a (ρ.asModuleEquiv z)) = F' (tensor H ρ a (ρ.asModuleEquiv z))
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [tensor_add_left, map_add, ha, hb]
  | single g c =>
    have hs : MonoidAlgebra.single g c = c • MonoidAlgebra.single g 1 := by simp
    rw [hs, ← D.scalar_tensor]
    simp only [map_smul, h]

/-- The source's Frobenius Hom isomorphism, constructed without coset choices. -/
def frobeniusEquiv : letI := D.module
    D.representation.IntertwiningMap σ ≃ₗ[k] ρ.IntertwiningMap (restrict H σ) := by
  letI := D.module
  exact {
    __ := frobeniusEvaluate H ρ σ D
    invFun := frobeniusLift H ρ σ D
    left_inv := by
      intro F
      apply Representation.IntertwiningMap.ext
      apply inductionData_hom_ext H ρ D
      intro g z
      change frobeniusLift H ρ σ D (frobeniusEvaluate H ρ σ D F)
        (tensor H ρ (MonoidAlgebra.single g 1) z) = F _
      rw [frobeniusLift_tensor]
      simp only [Representation.asAlgebraHom_single, one_smul, frobeniusEvaluate_apply]
      have hf := Representation.IntertwiningMap.isIntertwining _ _ F g (tensor H ρ 1 z)
      simpa only [D.action_tensor, mul_one] using hf.symm
    right_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext z
      change σ.asAlgebraHom 1 (f z) = f z
      simp }

/-- Both formulas characterize the isomorphism in the independent specification. -/
def frobeniusData : FrobeniusData H ρ σ D where
  equivalence := frobeniusEquiv H ρ σ D
  forward_one := by intros; rfl
  inverse_tensor := by
    letI := D.module
    intro f g z
    change σ.asAlgebraHom (MonoidAlgebra.single g 1) (f z) = σ g (f z)
    simp

/-- Reciprocity over arbitrary fields, groups, subgroup indices and dimensions. -/
theorem frobenius_reciprocity : FrobeniusSpecs.reciprocityType.{u,v,w,x} := by
  intro k G _ _ H V _ _ W _ _ ρ σ D
  exact ⟨frobeniusData H ρ σ D⟩

/-- Naturality under precomposition by every H-intertwiner. -/
theorem frobenius_naturality_pre : FrobeniusSpecs.naturalityPreType.{u,v,w,x,y} := by
  intro k G _ _ H V _ _ W _ _ U _ _ ρ σ τ D D' E E'
  letI := D.module
  letI := D'.module
  intro f J hJ F z
  rw [E'.forward_one, E.forward_one]
  change F (J (tensor H τ 1 z)) = F (tensor H ρ 1 (f z))
  rw [hJ]

/-- Naturality under postcomposition by every G-intertwiner. -/
theorem frobenius_naturality_post : FrobeniusSpecs.naturalityPostType.{u,v,w,x,y} := by
  intro k G _ _ H V _ _ W _ _ U _ _ ρ σ τ D E E'
  letI := D.module
  intro f F z
  rw [E'.forward_one, E.forward_one]
  rfl

/-- The unit is a universal arrow to restriction: Ind is left adjoint to Res. -/
theorem induction_left_adjoint : FrobeniusSpecs.leftAdjointType.{u,v,w,x} := by
  intro k G _ _ H V _ _ W _ _ ρ σ D
  letI := D.module
  intro f
  let E := frobeniusData H ρ σ D
  refine ⟨E.equivalence.symm f, ?_, ?_⟩
  · intro z
    rw [← E.forward_one, LinearEquiv.apply_symm_apply]
  · intro F hF
    apply E.equivalence.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Representation.IntertwiningMap.ext
    ext z
    change E.equivalence F z = f z
    rw [E.forward_one]
    exact hF z

end P103.Ch09
