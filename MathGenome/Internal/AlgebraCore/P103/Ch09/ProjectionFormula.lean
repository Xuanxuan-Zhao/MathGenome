import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.ProjectionFormula
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionModels

noncomputable section
universe u v w x y z
namespace P103.Ch09.Projection
open scoped MonoidAlgebra TensorProduct
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
attribute [local instance] rightSubgroupModule inducedAlgebraModule inducedScalarModule
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k H V)

/-- Equality of linear maps out of induction can be tested on group-basis tensors,
for every scalar action satisfying the upstream induction interface. -/
theorem induced_ext (D : InductionData H ρ)
    {U : Type*} [AddCommGroup U] [Module k U]
    (F F' : letI := D.module; Induced H ρ →ₗ[k] U)
    (h : ∀ (g : G) (v : V), F (tensor H ρ (MonoidAlgebra.single g 1) v) =
      F' (tensor H ρ (MonoidAlgebra.single g 1) v)) : F = F' := by
  let := D.module
  apply LinearMap.toAddMonoidHom_injective
  apply BalancedTensor.hom_ext
  intro a v
  change F (tensor H ρ a (ρ.asModuleEquiv v)) = F' (tensor H ρ a (ρ.asModuleEquiv v))
  induction a using MonoidAlgebra.induction_on with
  | of g => exact h g _
  | add a b ha hb => simp only [tensor_add_left, map_add, ha, hb]
  | smul c a ha =>
    rw [← D.scalar_tensor, map_smul, map_smul, ha]

/-- The preceding extensionality principle for the canonical scalar action. -/
theorem induced_ext_standard {U : Type*} [AddCommGroup U] [Module k U]
    (F F' : Induced H ρ →ₗ[k] U)
    (h : ∀ (g : G) (v : V), F (tensor H ρ (MonoidAlgebra.single g 1) v) =
      F' (tensor H ρ (MonoidAlgebra.single g 1) v)) : F = F' :=
  induced_ext H ρ (inductionData H ρ) F F' h

/-- Descend a field-bilinear group-algebra pairing using its full algebra
balancing law, preserving field linearity. -/
def inductionLift {U : Type*} [AddCommGroup U] [Module k U]
    (B : k[G] →ₗ[k] V →ₗ[k] U)
    (hB : ∀ (a : k[G]) (b : k[H]) (v : V),
      B (a * subgroupAlgebra H b) v = B a (ρ.asAlgebraHom b v)) :
    Induced H ρ →ₗ[k] U := by
  let L : Induced H ρ →+ U := BalancedTensor.lift <| BalancedTensor.Pairing.ofFun
    (fun a v => B a (ρ.asModuleEquiv v))
    (by intros; simp) (by intros; simp)
    (by intro b a v; exact hB a b (ρ.asModuleEquiv v))
  exact
    { L with
      map_smul' := by
        intro c q
        induction q using BalancedTensor.induction_on with
        | h0 => simp
        | ht a v =>
          change L (c • tensor H ρ a (ρ.asModuleEquiv v)) =
            c • L (tensor H ρ a (ρ.asModuleEquiv v))
          rw [inducedScalar_smul_tensor]
          change B (c • a) (ρ.asModuleEquiv v) = c • B a (ρ.asModuleEquiv v)
          simp
        | ha a b ha hb => simp_all [smul_add] }

@[simp] theorem inductionLift_tensor {U : Type*} [AddCommGroup U] [Module k U]
    (B : k[G] →ₗ[k] V →ₗ[k] U) (hB) (a : k[G]) (v : V) :
    inductionLift H ρ B hB (tensor H ρ a v) = B a v := rfl

variable {W : Type x} [AddCommGroup W] [Module k W]
variable (σ : Representation k G W)

/-- The forward formula at one group-basis coordinate, extended to all field tensors. -/
def forwardGenerator (g : G) : V ⊗[k] W →ₗ[k] Induced H ρ ⊗[k] W :=
  TensorProduct.map (tensorLinear H ρ (MonoidAlgebra.single g 1)) (σ g)

@[simp] theorem forwardGenerator_tmul (g : G) (v : V) (w : W) :
    forwardGenerator H ρ σ g (v ⊗ₜ[k] w) =
      tensor H ρ (MonoidAlgebra.single g 1) v ⊗ₜ[k] σ g w := rfl

/-- Extension of the forward formula along the group-algebra basis. -/
def forwardBilinear : k[G] →ₗ[k] V ⊗[k] W →ₗ[k] Induced H ρ ⊗[k] W :=
  (Finsupp.lift _ k G (forwardGenerator H ρ σ)).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem forwardBilinear_single (g : G) (c : k) (q : V ⊗[k] W) :
    forwardBilinear H ρ σ (MonoidAlgebra.single g c) q =
      c • forwardGenerator H ρ σ g q := by
  simp [forwardBilinear]

theorem forwardGenerator_balance (g : G) (h : H) (q : V ⊗[k] W) :
    forwardGenerator H ρ σ (g * h) q =
      forwardGenerator H ρ σ g (diagonal H ρ σ h q) := by
  induction q using TensorProduct.inductionOn with
  | add q q' hq hq' => simp [hq, hq']
  | tmul v w =>
    simp only [forwardGenerator_tmul, diagonal, Representation.tprod_apply,
      TensorProduct.map_tmul, restrict, MonoidHom.comp_apply]
    rw [TensorBridge.tensor_basis_balance]
    simp [map_mul, Module.End.mul_apply]

theorem forwardBilinear_balance (a : k[G]) (b : k[H]) (q : V ⊗[k] W) :
    forwardBilinear H ρ σ (a * subgroupAlgebra H b) q =
      forwardBilinear H ρ σ a ((diagonal H ρ σ).asAlgebraHom b q) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b b' hb hb' => simp [mul_add, hb, hb']
  | single h c =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, LinearMap.add_apply, ha, ha']
    | single g d =>
      simp only [subgroupAlgebra_single, MonoidAlgebra.single_mul_single,
        forwardBilinear_single, Representation.asAlgebraHom_single,
        LinearMap.smul_apply, map_smul, smul_smul]
      rw [forwardGenerator_balance, mul_comm d c]

/-- The balanced forward map. -/
def forward : Induced H (diagonal H ρ σ) →ₗ[k] Induced H ρ ⊗[k] W :=
  inductionLift H (diagonal H ρ σ) (forwardBilinear H ρ σ)
    (forwardBilinear_balance H ρ σ)

@[simp] theorem forward_basis (g : G) (v : V) (w : W) :
    forward H ρ σ (tensor H (diagonal H ρ σ) (MonoidAlgebra.single g 1) (v ⊗ₜ[k] w)) =
      tensor H ρ (MonoidAlgebra.single g 1) v ⊗ₜ[k] σ g w := by
  simp [forward]

/-- The inverse formula, bilinear in the two vector coordinates. -/
def backwardGenerator (g : G) : V →ₗ[k] W →ₗ[k] Induced H (diagonal H ρ σ) :=
  ((TensorProduct.mk k V W).compl₂ (σ g⁻¹)).compr₂
    (tensorLinear H (diagonal H ρ σ) (MonoidAlgebra.single g 1))

@[simp] theorem backwardGenerator_apply (g : G) (v : V) (w : W) :
    backwardGenerator H ρ σ g v w =
      tensor H (diagonal H ρ σ) (MonoidAlgebra.single g 1) (v ⊗ₜ[k] σ g⁻¹ w) := rfl

def backwardBilinear : k[G] →ₗ[k] V →ₗ[k] W →ₗ[k] Induced H (diagonal H ρ σ) :=
  (Finsupp.lift _ k G (backwardGenerator H ρ σ)).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem backwardBilinear_single (g : G) (c : k) (v : V) :
    backwardBilinear H ρ σ (MonoidAlgebra.single g c) v =
      c • backwardGenerator H ρ σ g v := by
  simp [backwardBilinear]

/-- The inverse twist cancels the action introduced by subgroup balancing. -/
theorem backwardGenerator_balance (g : G) (h : H) (v : V) :
    backwardGenerator H ρ σ (g * h) v = backwardGenerator H ρ σ g (ρ h v) := by
  ext w
  simp only [backwardGenerator_apply]
  rw [TensorBridge.tensor_basis_balance]
  simp [diagonal, Representation.tprod_apply, restrict, mul_inv_rev,
    map_mul, Module.End.mul_apply]

theorem backwardBilinear_balance (a : k[G]) (b : k[H]) (v : V) :
    backwardBilinear H ρ σ (a * subgroupAlgebra H b) v =
      backwardBilinear H ρ σ a (ρ.asAlgebraHom b v) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b b' hb hb' => simp [mul_add, hb, hb']
  | single h c =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, LinearMap.add_apply, ha, ha']
    | single g d =>
      simp only [subgroupAlgebra_single, MonoidAlgebra.single_mul_single,
        backwardBilinear_single, Representation.asAlgebraHom_single,
        LinearMap.smul_apply, map_smul, smul_smul]
      rw [backwardGenerator_balance, mul_comm d c]

/-- Descent first over the subgroup algebra, with values in linear maps on W. -/
def backwardInner : Induced H ρ →ₗ[k] W →ₗ[k] Induced H (diagonal H ρ σ) :=
  inductionLift H ρ (backwardBilinear H ρ σ) (backwardBilinear_balance H ρ σ)

/-- Descent over the field tensor product. -/
def backward : Induced H ρ ⊗[k] W →ₗ[k] Induced H (diagonal H ρ σ) :=
  TensorProduct.lift (backwardInner H ρ σ)

@[simp] theorem backward_basis (g : G) (v : V) (w : W) :
    backward H ρ σ (tensor H ρ (MonoidAlgebra.single g 1) v ⊗ₜ[k] w) =
      tensor H (diagonal H ρ σ) (MonoidAlgebra.single g 1) (v ⊗ₜ[k] σ g⁻¹ w) := by
  simp [backward, backwardInner]

theorem backward_forward :
    (backward H ρ σ).comp (forward H ρ σ) = LinearMap.id := by
  apply induced_ext_standard H (diagonal H ρ σ)
  intro g q
  induction q using TensorProduct.inductionOn with
  | tmul v w => simp
  | add q q' hq hq' => simp_all [tensor_add_right]

theorem forward_backward :
    (forward H ρ σ).comp (backward H ρ σ) = LinearMap.id := by
  apply TensorProduct.ext
  apply induced_ext_standard H ρ (U := W →ₗ[k] (Induced H ρ ⊗[k] W))
  intro g v
  ext w
  simp

/-- The vector space isomorphism in the projection formula. -/
def linearEquiv : Induced H (diagonal H ρ σ) ≃ₗ[k] Induced H ρ ⊗[k] W :=
  { forward H ρ σ with
    invFun := backward H ρ σ
    left_inv := fun q => LinearMap.congr_fun (backward_forward H ρ σ) q
    right_inv := fun q => LinearMap.congr_fun (forward_backward H ρ σ) q }

@[simp] theorem linearEquiv_basis (g : G) (v : V) (w : W) :
    linearEquiv H ρ σ (tensor H (diagonal H ρ σ) (MonoidAlgebra.single g 1) (v ⊗ₜ[k] w)) =
      tensor H ρ (MonoidAlgebra.single g 1) v ⊗ₜ[k] σ g w :=
  forward_basis H ρ σ g v w

@[simp] theorem linearEquiv_symm_basis (g : G) (v : V) (w : W) :
    (linearEquiv H ρ σ).symm (tensor H ρ (MonoidAlgebra.single g 1) v ⊗ₜ[k] w) =
      tensor H (diagonal H ρ σ) (MonoidAlgebra.single g 1) (v ⊗ₜ[k] σ g⁻¹ w) :=
  backward_basis H ρ σ g v w

/-- Left multiplication on the first group coordinate matches the diagonal action. -/
theorem forward_equivariant (g : G) :
    (forward H ρ σ).comp (induction H (diagonal H ρ σ) g) =
      ((induction H ρ).tprod σ g).comp (forward H ρ σ) := by
  apply induced_ext_standard H (diagonal H ρ σ)
  intro t q
  induction q using TensorProduct.inductionOn with
  | tmul v w =>
    simp [Representation.tprod_apply, MonoidAlgebra.single_mul_single,
      map_mul, Module.End.mul_apply]
  | add q q' hq hq' => simp_all [tensor_add_right]

/-- The G-equivariant projection isomorphism. -/
def equiv : (induction H (diagonal H ρ σ)).Equiv ((induction H ρ).tprod σ) :=
  Representation.Equiv.mk (linearEquiv H ρ σ) (forward_equivariant H ρ σ)

/-- Projection formula without finiteness or irreducibility restrictions. -/
theorem projection_formula : Specs.projectionFormulaType.{u,v,w,x} := by
  intro k G _ _ H V _ _ W _ _ ρ σ
  exact ⟨inductionData H ρ, inductionData H (diagonal H ρ σ), equiv H ρ σ,
    linearEquiv_basis H ρ σ, linearEquiv_symm_basis H ρ σ⟩

/-- Every family with the specified generator formula is natural in V and W. -/
theorem naturality_of_formulas : Specs.naturalityOfFormulasType.{u,v,w,x,y,z} := by
  intro k G _ _ H V _ _ W _ _ V' _ _ W' _ _ ρ σ ρ' σ' D DP D' DP'
  let := D.module
  let := DP.module
  let := D'.module
  let := DP'.module
  intro e e' he he' f j F FP hF hFP q
  have hn : e'.toLinearMap.comp FP = (TensorProduct.map F j.toLinearMap).comp e.toLinearMap := by
    apply induced_ext H (diagonal H ρ σ) DP
    intro t r
    change e' (FP (tensor H (diagonal H ρ σ) (MonoidAlgebra.single t 1) r)) =
      TensorProduct.map F j.toLinearMap (e (tensor H (diagonal H ρ σ) (MonoidAlgebra.single t 1) r))
    induction r using TensorProduct.inductionOn with
    | tmul v w =>
      rw [hFP, TensorProduct.map_tmul, he', he, TensorProduct.map_tmul, hF]
      exact congrArg (fun w' => tensor H ρ' (MonoidAlgebra.single t 1) (f v) ⊗ₜ[k] w')
        (Representation.IntertwiningMap.isIntertwining σ σ' j t w).symm
    | add r r' hr hr' => simp_all [tensor_add_right]
  exact LinearMap.congr_fun hn q

/-- Both induced maps exist as intertwiners, and the projection square commutes. -/
theorem projection_naturality : Specs.projectionNaturalityType.{u,v,w,x,y,z} := by
  intro k G _ _ H V _ _ W _ _ V' _ _ W' _ _ ρ σ ρ' σ' D DP D' DP'
  let := D.module
  let := DP.module
  let := D'.module
  let := DP'.module
  intro e e' he he' f j
  obtain ⟨F, hF⟩ := tensor_functoriality H ρ ρ' D D' f
  obtain ⟨FP, hFP⟩ := tensor_functoriality H (diagonal H ρ σ) (diagonal H ρ' σ') DP DP'
    (f.tensor (restrictionMap H j))
  refine ⟨F, FP, hF, hFP, ?_⟩
  exact naturality_of_formulas H ρ σ ρ' σ' D DP D' DP' e e' he he' f j
    F.toLinearMap FP.toLinearMap hF hFP

end P103.Ch09.Projection
