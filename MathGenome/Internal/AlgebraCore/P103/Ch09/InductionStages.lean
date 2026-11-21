import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InductionStages
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionModels

noncomputable section
set_option maxHeartbeats 2000000
universe u v w x
namespace P103.Ch09

-- Keep construction helpers separate from other Chapter 9 implementations.
namespace InductionStages
open scoped MonoidAlgebra
attribute [local instance] rightSubgroupModule inducedAlgebraModule inducedScalarModule
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k H V)
variable {W : Type x} [AddCommGroup W] [Module k W]

/-- Linear extension of a family on the group basis. -/
def generatorExtension (L : G → V →ₗ[k] W) : k[G] →ₗ[k] V →ₗ[k] W :=
  (Finsupp.linearCombination k L).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem generatorExtension_single (L : G → V →ₗ[k] W) (g : G) (c : k) (z : V) :
    generatorExtension L (MonoidAlgebra.single g c) z = c • L g z := by
  simp [generatorExtension]

/-- A covariant family extends across the full subgroup-algebra balance,
not merely the relations for group elements. -/
theorem generatorExtension_balance (L : G → V →ₗ[k] W)
    (hL : ∀ (g : G) (h : H) z, L (g * h) z = L g (ρ h z))
    (r : k[H]) (a : k[G]) (z : ρ.asModule) :
    generatorExtension L (MulOpposite.op r • a) (ρ.asModuleEquiv z) =
      generatorExtension L a (ρ.asModuleEquiv (r • z)) := by
  rw [rightSubgroup_smul]
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs =>
    simp only [map_add, mul_add, LinearMap.add_apply, add_smul, hr, hs]
  | single h c =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_mul, map_add, LinearMap.add_apply, ha, hb]
    | single g d =>
      simp only [subgroupAlgebra_single, MonoidAlgebra.single_mul_single,
        generatorExtension_single, Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_single, LinearMap.smul_apply, hL]
      simp [smul_smul]

/-- Descend a covariant family to the shared balanced tensor. -/
def generatorLift (L : G → V →ₗ[k] W)
    (hL : ∀ (g : G) (h : H) z, L (g * h) z = L g (ρ h z)) :
    Induced H ρ →ₗ[k] W := by
  let P : BalancedTensor.Pairing k[H] (A := k[G]) (B := ρ.asModule) W :=
    BalancedTensor.Pairing.ofFun
      (fun a z => generatorExtension L a (ρ.asModuleEquiv z))
      (by intros; simp) (by intros; simp) (generatorExtension_balance H ρ L hL)
  let A := BalancedTensor.lift P
  exact { toAddHom := A
          map_smul' := by
            intro c z
            induction z using BalancedTensor.induction_on with
            | h0 => simp
            | ht a b =>
              change A (c • tensor H ρ a (ρ.asModuleEquiv b)) = c • A _
              rw [inducedScalar_smul_tensor]
              change generatorExtension L (c • a) _ = c • generatorExtension L a _
              simp
            | ha z z' hz hz' =>
              change A (c • z) = c • A z at hz
              change A (c • z') = c • A z' at hz'
              simp [smul_add, hz, hz'] }

@[simp] theorem generatorLift_tensor (L : G → V →ₗ[k] W)
    (hL : ∀ (g : G) (h : H) z, L (g * h) z = L g (ρ h z))
    (a : k[G]) (z : V) :
    generatorLift H ρ L hL (tensor H ρ a z) = generatorExtension L a z := rfl

/-- The universal extension of an intertwiner into a restricted representation. -/
def inductionLift (τ : Representation k G W)
    (f : ρ.IntertwiningMap (restrict H τ)) :
    (induction H ρ).IntertwiningMap τ where
  toLinearMap := generatorLift H ρ (fun g => (τ g).comp f.toLinearMap)
    (by intro g h z; simpa [map_mul, Module.End.mul_apply, restrict] using
      congrArg (τ g) (Representation.IntertwiningMap.isIntertwining ρ (restrict H τ) f h z).symm)
  isIntertwining' g := by
    apply induced_hom_ext H ρ
    intro s z
    simp only [LinearMap.comp_apply, induction_tensor,
      MonoidAlgebra.single_mul_single, mul_one, generatorLift_tensor,
      generatorExtension_single, one_smul]
    simp [map_mul, Module.End.mul_apply]

@[simp] theorem inductionLift_tensor (τ : Representation k G W)
    (f : ρ.IntertwiningMap (restrict H τ)) (g : G) (z : V) :
    inductionLift H ρ τ f (tensor H ρ (MonoidAlgebra.single g 1) z) = τ g (f z) := by
  simp [inductionLift]

/-- Tensoring a fixed algebra coordinate is linear for every admissible
construction of the induced scalar action. -/
def tensorLinearWith (D : InductionData H ρ) (a : k[G]) :
    letI := D.module; V →ₗ[k] Induced H ρ :=
  letI := D.module
  { toFun := tensor H ρ a
    map_add' := tensor_add_right H ρ a
    map_smul' c z := by rw [tensor_smul_right, D.scalar_tensor]; rfl }

/-- Group-basis tensors determine a linear map for any induction data. -/
theorem inductionData_hom_ext (D : InductionData H ρ) :
    letI := D.module
    ∀ {F F' : Induced H ρ →ₗ[k] W},
      (∀ (g : G) (z : V), F (tensor H ρ (MonoidAlgebra.single g 1) z) =
        F' (tensor H ρ (MonoidAlgebra.single g 1) z)) → F = F' := by
  letI := D.module
  intro F F' h
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

section Stages
variable {H} {K : Subgroup G} (hHK : H ≤ K)

/-- Insert a vector at the identity, as a map into the restricted G-induction. -/
def stageUnit : (stageRestriction hHK ρ).IntertwiningMap
    (restrict (H.subgroupOf K) (restrict K (induction H ρ))) where
  toLinearMap := tensorLinear H ρ 1
  isIntertwining' h := by
    ext z
    change tensor H ρ 1 (ρ ((Subgroup.subgroupOfEquivOfLe hHK) h) z) =
      tensor H ρ (MonoidAlgebra.single ((h : K) : G) 1 * 1) z
    simpa using (tensor_balance_group H ρ 1
      ((Subgroup.subgroupOfEquivOfLe hHK) h) z).symm

/-- Multiply the inner K-coordinate into the direct G-coordinate. -/
def stageInnerMap : (induction (H.subgroupOf K) (stageRestriction hHK ρ)).IntertwiningMap
    (restrict K (induction H ρ)) :=
  inductionLift (H.subgroupOf K) (stageRestriction hHK ρ)
    (restrict K (induction H ρ)) (stageUnit ρ hHK)

@[simp] theorem stageInnerMap_tensor (s : K) (z : V) :
    stageInnerMap ρ hHK
      (tensor (H.subgroupOf K) (stageRestriction hHK ρ) (MonoidAlgebra.single s 1) z) =
    tensor H ρ (MonoidAlgebra.single (s : G) 1) z := by
  rw [stageInnerMap, inductionLift_tensor]
  change tensor H ρ (MonoidAlgebra.single (s : G) 1 * 1) z = _
  simp

/-- The multiplication map on the double induction. -/
def stageForward :
    (induction K (induction (H.subgroupOf K) (stageRestriction hHK ρ))).IntertwiningMap
      (induction H ρ) :=
  inductionLift K (induction (H.subgroupOf K) (stageRestriction hHK ρ))
    (induction H ρ) (stageInnerMap ρ hHK)

@[simp] theorem stageForward_tensor (g : G) (s : K) (z : V) :
    stageForward ρ hHK (tensor K (induction (H.subgroupOf K) (stageRestriction hHK ρ))
      (MonoidAlgebra.single g 1)
      (tensor (H.subgroupOf K) (stageRestriction hHK ρ) (MonoidAlgebra.single s 1) z)) =
    tensor H ρ (MonoidAlgebra.single (g * (s : G)) 1) z := by
  simp [stageForward, induction_tensor, MonoidAlgebra.single_mul_single]

/-- Identity-coordinate insertion for the reverse map. Its intertwining law
is exactly the two successive balancing relations. -/
def stageBackUnit : ρ.IntertwiningMap
    (restrict H (induction K (induction (H.subgroupOf K) (stageRestriction hHK ρ)))) where
  toLinearMap := (tensorLinear K (induction (H.subgroupOf K) (stageRestriction hHK ρ)) 1).comp
    (tensorLinear (H.subgroupOf K) (stageRestriction hHK ρ) 1)
  isIntertwining' h := by
    ext z
    change tensor K (induction (H.subgroupOf K) (stageRestriction hHK ρ)) 1
        (tensor (H.subgroupOf K) (stageRestriction hHK ρ) 1 (ρ h z)) =
      tensor K (induction (H.subgroupOf K) (stageRestriction hHK ρ))
        (MonoidAlgebra.single (h : G) 1 * 1)
        (tensor (H.subgroupOf K) (stageRestriction hHK ρ) 1 z)
    let hK : K := Subgroup.inclusion hHK h
    let hJ : H.subgroupOf K := (Subgroup.subgroupOfEquivOfLe hHK).symm h
    have hi := tensor_balance_group (H.subgroupOf K) (stageRestriction hHK ρ) 1 hJ z
    have ho := tensor_balance_group K
      (induction (H.subgroupOf K) (stageRestriction hHK ρ)) 1 hK
      (tensor (H.subgroupOf K) (stageRestriction hHK ρ) 1 z)
    have hi' : tensor (H.subgroupOf K) (stageRestriction hHK ρ)
        (MonoidAlgebra.single hK 1) z =
        tensor (H.subgroupOf K) (stageRestriction hHK ρ) 1 (ρ h z) := by
      simpa [hJ, hK, stageRestriction, Subgroup.subgroupOfEquivOfLe, Subgroup.inclusion] using hi
    have ho' : tensor K (induction (H.subgroupOf K) (stageRestriction hHK ρ))
        (MonoidAlgebra.single (h : G) 1)
        (tensor (H.subgroupOf K) (stageRestriction hHK ρ) 1 z) =
        tensor K (induction (H.subgroupOf K) (stageRestriction hHK ρ)) 1
          (tensor (H.subgroupOf K) (stageRestriction hHK ρ)
            (MonoidAlgebra.single hK 1) z) := by
      simpa [induction_tensor, hK] using ho
    simpa using (congrArg
      (tensor K (induction (H.subgroupOf K) (stageRestriction hHK ρ)) 1) hi').symm.trans ho'.symm

/-- The inverse sends `g ⊗ v` to `g ⊗ (1 ⊗ v)`. -/
def stageBackward : (induction H ρ).IntertwiningMap
    (induction K (induction (H.subgroupOf K) (stageRestriction hHK ρ))) :=
  inductionLift H ρ (induction K (induction (H.subgroupOf K) (stageRestriction hHK ρ)))
    (stageBackUnit ρ hHK)

@[simp] theorem stageBackward_tensor (g : G) (z : V) :
    stageBackward ρ hHK (tensor H ρ (MonoidAlgebra.single g 1) z) =
    tensor K (induction (H.subgroupOf K) (stageRestriction hHK ρ)) (MonoidAlgebra.single g 1)
      (tensor (H.subgroupOf K) (stageRestriction hHK ρ) 1 z) := by
  simp [stageBackward, stageBackUnit, tensorLinear, induction_tensor]

/-- Both composites are identities; the double-tensor identity uses K-balancing. -/
theorem stageForward_backward :
    (stageForward ρ hHK).toLinearMap.comp (stageBackward ρ hHK).toLinearMap =
      LinearMap.id := by
  apply induced_hom_ext H ρ
  intro g z
  change stageForward ρ hHK (stageBackward ρ hHK
    (tensor H ρ (MonoidAlgebra.single g 1) z)) = _
  rw [stageBackward_tensor]
  have h := stageForward_tensor ρ hHK g (1 : K) z
  simpa only [Subgroup.coe_one, mul_one, LinearMap.id_apply, MonoidAlgebra.one_def] using h

theorem stageBackward_forward :
    (stageBackward ρ hHK).toLinearMap.comp (stageForward ρ hHK).toLinearMap =
      LinearMap.id := by
  apply induced_hom_ext K (induction (H.subgroupOf K) (stageRestriction hHK ρ))
  intro g z
  let A := tensorLinear K (induction (H.subgroupOf K) (stageRestriction hHK ρ))
    (MonoidAlgebra.single g 1)
  have hh : ((stageBackward ρ hHK).toLinearMap.comp
      ((stageForward ρ hHK).toLinearMap.comp A)) = A := by
    apply induced_hom_ext (H.subgroupOf K) (stageRestriction hHK ρ)
    intro s v
    change stageBackward ρ hHK (stageForward ρ hHK
      (tensor K (induction (H.subgroupOf K) (stageRestriction hHK ρ))
        (MonoidAlgebra.single g 1)
        (tensor (H.subgroupOf K) (stageRestriction hHK ρ) (MonoidAlgebra.single s 1) v))) = _
    rw [stageForward_tensor, stageBackward_tensor]
    have hb := tensor_balance_group K (induction (H.subgroupOf K) (stageRestriction hHK ρ))
      (MonoidAlgebra.single g 1) s
      (tensor (H.subgroupOf K) (stageRestriction hHK ρ) 1 v)
    simpa [MonoidAlgebra.single_mul_single, induction_tensor, A, tensorLinear] using hb
  exact LinearMap.congr_fun hh z

/-- The canonical G-equivariant linear equivalence for induction in stages. -/
def stageEquiv : Induced K (induction (H.subgroupOf K) (stageRestriction hHK ρ)) ≃ₗ[k]
    Induced H ρ :=
  LinearEquiv.ofLinearMap (stageForward ρ hHK).toLinearMap (stageBackward ρ hHK).toLinearMap
    (stageForward_backward ρ hHK) (stageBackward_forward ρ hHK)

theorem induction_stages : Specs.inductionStagesType.{u,v,w} := by
  intro k G _ _ H K hHK V _ _ ρ
  exact ⟨{
    inner := inductionData (H.subgroupOf K) (stageRestriction hHK ρ)
    outer := inductionData K (induction (H.subgroupOf K) (stageRestriction hHK ρ))
    direct := inductionData H ρ
    equivalence := stageEquiv ρ hHK
    forward_tensor := stageForward_tensor ρ hHK
    inverse_tensor := stageBackward_tensor ρ hHK
    equivariant := fun g z => Representation.IntertwiningMap.isIntertwining _ _
      (stageForward ρ hHK) g z }⟩

end Stages

/-- Naturality follows by evaluating both linear composites on double
basis tensors. It applies to all choices of the induction construction. -/
theorem stage_naturality_condition : Specs.stageNaturalityCondition.{u,v,w,x} := by
  intro k G _ _ H K hHK V _ _ W _ _ ρ σ D E
  letI := D.inner.module
  letI := D.outer.module
  letI := D.direct.module
  letI := E.inner.module
  letI := E.outer.module
  letI := E.direct.module
  intro f I O F hI hO hF z
  have heq : E.equivalence.toLinearMap.comp O = F.comp D.equivalence.toLinearMap := by
    apply inductionData_hom_ext K D.inner.representation D.outer
    intro g y
    let A := tensorLinearWith K D.inner.representation D.outer (MonoidAlgebra.single g 1)
    have hi : (E.equivalence.toLinearMap.comp O).comp A =
        (F.comp D.equivalence.toLinearMap).comp A := by
      apply inductionData_hom_ext (H.subgroupOf K) (stageRestriction hHK ρ) D.inner
      intro s v
      change E.equivalence (O (tensor K D.inner.representation (MonoidAlgebra.single g 1)
        (tensor (H.subgroupOf K) (stageRestriction hHK ρ) (MonoidAlgebra.single s 1) v))) =
        F (D.equivalence (tensor K D.inner.representation (MonoidAlgebra.single g 1)
          (tensor (H.subgroupOf K) (stageRestriction hHK ρ) (MonoidAlgebra.single s 1) v)))
      rw [hO, hI, E.forward_tensor, D.forward_tensor, hF]
    exact LinearMap.congr_fun hi y
  exact LinearMap.congr_fun heq z

/-- The three induced intertwiners and the naturality square, for every
H-intertwiner and every choice of construction data. -/
theorem induction_stages_naturality : Specs.inductionStagesNaturalityType.{u,v,w,x} := by
  intro k G _ _ H K hHK V _ _ W _ _ ρ σ D E
  letI := D.inner.module
  letI := D.outer.module
  letI := D.direct.module
  letI := E.inner.module
  letI := E.outer.module
  letI := E.direct.module
  intro f
  let fJ : (stageRestriction hHK ρ).IntertwiningMap (stageRestriction hHK σ) :=
    { toLinearMap := f.toLinearMap
      isIntertwining' h := f.isIntertwining' ((Subgroup.subgroupOfEquivOfLe hHK) h) }
  obtain ⟨I, hI⟩ := tensor_functoriality (H.subgroupOf K)
    (stageRestriction hHK ρ) (stageRestriction hHK σ) D.inner E.inner fJ
  obtain ⟨O, hO⟩ := tensor_functoriality K D.inner.representation E.inner.representation
    D.outer E.outer I
  obtain ⟨F, hF⟩ := tensor_functoriality H ρ σ D.direct E.direct f
  refine ⟨I, O, F, hI, hO, hF, ?_⟩
  exact stage_naturality_condition hHK ρ σ D E f I.toLinearMap O.toLinearMap F.toLinearMap
    hI hO hF

end InductionStages

/-- Induction through an intermediate subgroup agrees equivariantly with direct induction. -/
theorem induction_stages : Specs.inductionStagesType.{u,v,w} :=
  InductionStages.induction_stages

/-- The induction-in-stages equivalence commutes with every intertwiner. -/
theorem induction_stages_naturality : Specs.inductionStagesNaturalityType.{u,v,w,x} :=
  InductionStages.induction_stages_naturality

end P103.Ch09
