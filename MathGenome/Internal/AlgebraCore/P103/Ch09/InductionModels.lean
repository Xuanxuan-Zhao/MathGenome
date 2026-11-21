import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InductionModels
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.P103.Ch08.RepresentationModules
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.DirectSum.Finsupp

noncomputable section
universe u v w x
namespace P103.Ch09
open scoped MonoidAlgebra
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
attribute [local instance] rightSubgroupModule

@[simp] theorem subgroupAlgebra_single (h : H) (c : k) :
    subgroupAlgebra H (MonoidAlgebra.single h c) = MonoidAlgebra.single (h : G) c := by
  simp [subgroupAlgebra]

theorem rightSubgroup_smul (a : k[H]) (b : k[G]) :
    MulOpposite.op a • b = b * subgroupAlgebra H a := rfl

instance subgroup_left_commute : SMulCommClass k[G] k[H]ᵐᵒᵖ k[G] where
  smul_comm a b c := by
    change a * (c * subgroupAlgebra H b.unop) = (a * c) * subgroupAlgebra H b.unop
    exact (mul_assoc _ _ _).symm

variable {V : Type w} [AddCommGroup V] [Module k V]

/-- Restriction along the subgroup inclusion. -/
def restriction (ρ : Representation k G V) : Representation k H V := restrict H ρ

@[simp] theorem restriction_apply (ρ : Representation k G V) (h : H) (z : V) :
    restriction H ρ h z = ρ h z := rfl

variable (ρ : Representation k H V)

@[simp] theorem tensor_zero_left (z : V) : tensor H ρ 0 z = 0 :=
  BalancedTensor.zero_tmul _

@[simp] theorem tensor_zero_right (a : k[G]) : tensor H ρ a 0 = 0 := by
  simp [tensor]

theorem tensor_add_left (a b : k[G]) (z : V) :
    tensor H ρ (a + b) z = tensor H ρ a z + tensor H ρ b z :=
  BalancedTensor.add_tmul _ _ _

theorem tensor_add_right (a : k[G]) (z z' : V) :
    tensor H ρ a (z + z') = tensor H ρ a z + tensor H ρ a z' := by
  simp [tensor, BalancedTensor.tmul_add]

/-- The full group-algebra balancing relation, on the original vector space. -/
theorem tensor_balance (a : k[G]) (b : k[H]) (z : V) :
    tensor H ρ (a * subgroupAlgebra H b) z =
      tensor H ρ a (ρ.asAlgebraHom b z) := by
  change BalancedTensor.tmul k[H] (MulOpposite.op b • a) _ = _
  rw [BalancedTensor.balance]
  rfl

theorem tensor_balance_group (a : k[G]) (h : H) (z : V) :
    tensor H ρ (a * MonoidAlgebra.single (h : G) 1) z =
      tensor H ρ a (ρ h z) := by
  simpa using tensor_balance H ρ a (MonoidAlgebra.single h 1) z

/-- Coefficients can be moved between the two tensor factors. -/
theorem tensor_smul_right (c : k) (a : k[G]) (z : V) :
    tensor H ρ a (c • z) = tensor H ρ (c • a) z := by
  rw [tensor, ρ.asModuleEquiv_symm_map_smul, ← BalancedTensor.balance]
  change tensor H ρ (a * subgroupAlgebra H (algebraMap k k[H] c)) z = _
  rw [AlgHom.commutes, ← Algebra.commutes, ← Algebra.smul_def]

/-- The outer group-algebra action on the shared balanced tensor. -/
@[instance_reducible] def inducedAlgebraModule : Module k[G] (Induced H ρ) :=
  BalancedTensor.leftModule

attribute [local instance] inducedAlgebraModule

/-- Its restriction to the coefficient field. -/
@[instance_reducible] def inducedScalarModule : Module k (Induced H ρ) :=
  Module.compHom (Induced H ρ) (algebraMap k k[G])

attribute [local instance] inducedScalarModule

instance inducedScalarTower : IsScalarTower k k[G] (Induced H ρ) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

@[simp] theorem inducedAlgebra_smul_tensor (a b : k[G]) (z : V) :
    a • tensor H ρ b z = tensor H ρ (a * b) z := rfl

@[simp] theorem inducedScalar_smul_tensor (c : k) (a : k[G]) (z : V) :
    c • tensor H ρ a z = tensor H ρ (c • a) z := by
  change tensor H ρ ((algebraMap k k[G] c) * a) z = _
  rw [← Algebra.smul_def]

/-- Each first-factor coordinate is linear in the represented vector. -/
def tensorLinear (a : k[G]) : V →ₗ[k] Induced H ρ where
  toFun := tensor H ρ a
  map_add' := tensor_add_right H ρ a
  map_smul' c z := by
    rw [tensor_smul_right, inducedScalar_smul_tensor]
    rfl

/-- Left multiplication on the first tensor factor. -/
def induction : Representation k G (Induced H ρ) := Representation.ofModule' _

@[simp] theorem induction_tensor (g : G) (a : k[G]) (z : V) :
    induction H ρ g (tensor H ρ a z) =
      tensor H ρ (MonoidAlgebra.single g 1 * a) z := rfl

def inductionData : InductionData H ρ where
  module := inducedScalarModule H ρ
  representation := induction H ρ
  scalar_tensor := inducedScalar_smul_tensor H ρ
  action_tensor := induction_tensor H ρ

theorem tensor_construction : Specs.tensorConstructionType.{u,v,w} := by
  intro k G _ _ H V _ _ ρ
  exact ⟨inductionData H ρ⟩

section Maps
variable {W : Type x} [AddCommGroup W] [Module k W]
variable {ρ} {σ : Representation k H W}

/-- Induction sends an intertwiner to the map acting on the second tensor factor. -/
def inductionMap (f : ρ.IntertwiningMap σ) :
    (induction H ρ).IntertwiningMap (induction H σ) where
  __ : Induced H ρ →ₗ[k] Induced H σ :=
    { __ := BalancedTensor.map (LinearMap.id : k[G] →ₗ[k[H]ᵐᵒᵖ] k[G])
        (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f)
      map_smul' c z := by
        exact BalancedTensor.map_leftScale _ _ (fun _ _ => rfl)
          (algebraMap k k[G] c) z }
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    exact BalancedTensor.map_leftScale _ _ (fun _ _ => rfl)
      (MonoidAlgebra.single g 1) z

@[simp] theorem inductionMap_tensor (f : ρ.IntertwiningMap σ) (a : k[G]) (z : V) :
    inductionMap H f (tensor H ρ a z) = tensor H σ a (f z) := rfl

/-- The generator formula determines a map uniquely, without a transversal. -/
theorem inductionMap_unique (f : ρ.IntertwiningMap σ)
    (F : Induced H ρ →ₗ[k] Induced H σ)
    (hF : ∀ a z, F (tensor H ρ a z) = tensor H σ a (f z)) :
    F = (inductionMap H f).toLinearMap := by
  apply LinearMap.toAddMonoidHom_injective
  apply BalancedTensor.hom_ext
  intro a z
  exact hF a (ρ.asModuleEquiv z)

end Maps

@[simp] theorem inductionMap_id :
    inductionMap H (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (induction H ρ) := by
  apply Representation.IntertwiningMap.ext
  symm
  apply inductionMap_unique H
  intro a z
  rfl

theorem inductionMap_comp {W : Type x} [AddCommGroup W] [Module k W]
    {U : Type*} [AddCommGroup U] [Module k U]
    {σ : Representation k H W} {τ : Representation k H U}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    inductionMap H (g.comp f) = (inductionMap H g).comp (inductionMap H f) := by
  apply Representation.IntertwiningMap.ext
  symm
  apply inductionMap_unique H
  intro a z
  simp

/-- An intertwiner for G is still an intertwiner after restriction to H. -/
def restrictionMap {W : Type x} [AddCommGroup W] [Module k W]
    {α : Representation k G V} {β : Representation k G W}
    (f : α.IntertwiningMap β) :
    (restriction H α).IntertwiningMap (restriction H β) where
  __ := f.toLinearMap
  isIntertwining' h := f.isIntertwining' h

end P103.Ch09

namespace P103.Ch09.TensorCoordinates
open scoped MonoidAlgebra
open DirectSum
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
attribute [local instance] rightSubgroupModule
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k H V)
attribute [local instance] inducedAlgebraModule inducedScalarModule
variable {T : Set G} (hT : Subgroup.IsComplement T (H : Set G))

/-- The `T` coordinate of an elementary group element. -/
def coordinateGenerator (g : G) : V →ₗ[k] (T →₀ V) :=
  (Finsupp.lsingle (hT.equiv g).1).comp (ρ (hT.equiv g).2)

@[simp] theorem coordinateGenerator_apply (g : G) (z : V) :
  coordinateGenerator H ρ hT g z =
    Finsupp.single (hT.equiv g).1 (ρ (hT.equiv g).2 z) := rfl

/-- Extend the group basis coordinates linearly. -/
def coordinateLinear : k[G] →ₗ[k] V →ₗ[k] (T →₀ V) :=
  (Finsupp.linearCombination k (coordinateGenerator H ρ hT)).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem coordinateLinear_single (g : G) (c : k) (z : V) :
  coordinateLinear H ρ hT (MonoidAlgebra.single g c) z =
    c • Finsupp.single (hT.equiv g).1 (ρ (hT.equiv g).2 z) := by
  simp [coordinateLinear]

@[simp] theorem coordinateGenerator_mul (g : G) (h : H) (z : V) :
  coordinateGenerator H ρ hT (g * h) z =
    coordinateGenerator H ρ hT g (ρ h z) := by
  simp [coordinateGenerator, hT.equiv_mul_right, ← Module.End.mul_apply, ← map_mul]

theorem coordinateLinear_balance (r : k[H]) (a : k[G]) (z : ρ.asModule) :
    coordinateLinear H ρ hT (MulOpposite.op r • a) (ρ.asModuleEquiv z) =
      coordinateLinear H ρ hT a (ρ.asModuleEquiv (r • z)) := by
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
        coordinateLinear_single, hT.equiv_mul_right,
        Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
        LinearMap.smul_apply]
      simp [map_mul, Module.End.mul_apply, smul_smul]

/-- The balanced map from tensor factors to transversal coordinates. -/
def coordinatePairing : BalancedTensor.Pairing k[H] (A := k[G]) (B := ρ.asModule)
    (T →₀ V) :=
  BalancedTensor.Pairing.ofFun
    (fun a z => coordinateLinear H ρ hT a (ρ.asModuleEquiv z))
    (by intros; simp)
    (by intros; simp)
    (coordinateLinear_balance H ρ hT)

def coordinatesAdd : Induced H ρ →+ (T →₀ V) :=
  BalancedTensor.lift (coordinatePairing H ρ hT)

@[simp] theorem coordinatesAdd_tensor (a : k[G]) (z : V) :
    coordinatesAdd H ρ hT (tensor H ρ a z) = coordinateLinear H ρ hT a z := by
  simp [coordinatesAdd, tensor, coordinatePairing, BalancedTensor.Pairing.ofFun]

def coordinates : Induced H ρ →ₗ[k] (T →₀ V) where
  toAddHom := coordinatesAdd H ρ hT
  map_smul' c z := by
    induction z using BalancedTensor.induction_on with
    | h0 => simp
    | ht a b =>
      change coordinatesAdd H ρ hT (c • tensor H ρ a (ρ.asModuleEquiv b)) =
        c • coordinatesAdd H ρ hT (tensor H ρ a (ρ.asModuleEquiv b))
      simp
    | ha z z' hz hz' =>
      change coordinatesAdd H ρ hT (c • z) = c • coordinatesAdd H ρ hT z at hz
      change coordinatesAdd H ρ hT (c • z') = c • coordinatesAdd H ρ hT z' at hz'
      simp [smul_add, hz, hz']

@[simp] theorem coordinates_tensor (a : k[G]) (z : V) :
    coordinates H ρ hT (tensor H ρ a z) = coordinateLinear H ρ hT a z :=
  coordinatesAdd_tensor H ρ hT a z

def summand (t : T) : V →ₗ[k] Induced H ρ where
  toFun z := tensor H ρ (MonoidAlgebra.single (t : G) 1) z
  map_add' := tensor_add_right H ρ _
  map_smul' c z := by simp [tensor_smul_right]

def coordinateSum : (T →₀ V) →ₗ[k] Induced H ρ :=
  Finsupp.lsum k (summand H ρ)

@[simp] theorem coordinateSum_single (t : T) (z : V) :
    coordinateSum H ρ (Finsupp.single t z) =
      tensor H ρ (MonoidAlgebra.single (t : G) 1) z := by
  simp [coordinateSum, Finsupp.lsum_single, summand]

theorem equiv_transversal (t : T) : hT.equiv (t : G) = (t, (1 : H)) := by
  apply hT.equiv.symm.injective
  rw [Equiv.symm_apply_apply, Subgroup.IsComplement.equiv_symm_apply]
  simp

@[simp] theorem coordinates_summand (t : T) (z : V) :
    coordinates H ρ hT (tensor H ρ (MonoidAlgebra.single (t : G) 1) z) =
      Finsupp.single t z := by
  simp [equiv_transversal H hT]

theorem coordinates_coordinateSum (d : T →₀ V) :
    coordinates H ρ hT (coordinateSum H ρ d) = d := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d d' hd hd' => simp [hd, hd']
  | single t z => simp [equiv_transversal H hT]

theorem tensor_decompose (g : G) (c : k) (z : V) :
    tensor H ρ (MonoidAlgebra.single g c) z =
      tensor H ρ (MonoidAlgebra.single ((hT.equiv g).1 : G) c)
        (ρ (hT.equiv g).2 z) := by
  rw [← tensor_balance_group]
  simp [MonoidAlgebra.single_mul_single, hT.equiv_fst_mul_equiv_snd]

theorem coordinateSum_coordinates (z : Induced H ρ) :
    coordinateSum H ρ (coordinates H ρ hT z) = z := by
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ha z z' hz hz' => simp [hz, hz']
  | ht a b =>
    change coordinateSum H ρ (coordinates H ρ hT (tensor H ρ a (ρ.asModuleEquiv b))) =
      tensor H ρ a (ρ.asModuleEquiv b)
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a a' ha ha' => simp only [tensor_add_left, map_add, ha, ha']
    | single g c =>
      simp only [coordinates_tensor, coordinateLinear_single, map_smul,
        coordinateSum_single, inducedScalar_smul_tensor]
      simpa using (tensor_decompose H ρ hT g c (ρ.asModuleEquiv b)).symm

/-- Canonical coordinates relative to any left transversal. -/
def transversalEquiv : (T →₀ V) ≃ₗ[k] Induced H ρ :=
  { coordinateSum H ρ with
    invFun := coordinates H ρ hT
    left_inv := coordinates_coordinateSum H ρ hT
    right_inv := coordinateSum_coordinates H ρ hT }

@[simp] theorem transversalEquiv_single (t : T) (z : V) :
    transversalEquiv H ρ hT (Finsupp.single t z) =
      tensor H ρ (MonoidAlgebra.single (t : G) 1) z :=
  coordinateSum_single H ρ t z

/-- The source's direct sum decomposition on an arbitrary left transversal. -/
def transversalDirectSumEquiv : (⨁ _ : T, V) ≃ₗ[k] Induced H ρ := by
  classical
  exact (finsuppLEquivDirectSum k V T).symm.trans (transversalEquiv H ρ hT)

@[simp] theorem transversalDirectSumEquiv_lof (t : T) (z : V) :
    letI : DecidableEq T := Classical.decEq _
    transversalDirectSumEquiv H ρ hT (DirectSum.lof k T (fun _ => V) t z) =
      tensor H ρ (MonoidAlgebra.single (t : G) 1) z := by
  letI : DecidableEq T := Classical.decEq _
  dsimp only [transversalDirectSumEquiv, LinearEquiv.trans_apply]
  have hs := finsuppLEquivDirectSum_symm_lof k V T t z
  erw [hs]
  exact transversalEquiv_single H ρ hT t z

theorem induced_finiteDimensional [H.FiniteIndex] [FiniteDimensional k V] :
    FiniteDimensional k (Induced H ρ) := by
  obtain ⟨T, hT, _⟩ := H.exists_isComplement_left 1
  letI : Finite T := hT.finite_left_iff.mpr inferInstance
  exact Module.Finite.equiv (transversalEquiv H ρ hT)

theorem induced_finrank [H.FiniteIndex] [FiniteDimensional k V] :
    Module.finrank k (Induced H ρ) = H.index * Module.finrank k V := by
  obtain ⟨T, hT, _⟩ := H.exists_isComplement_left 1
  letI : Finite T := hT.finite_left_iff.mpr inferInstance
  letI : Fintype T := Fintype.ofFinite T
  rw [← (transversalDirectSumEquiv H ρ hT).finrank_eq, Module.finrank_directSum]
  simp [← Nat.card_eq_fintype_card, hT.card_left]

end P103.Ch09.TensorCoordinates

open scoped Classical
namespace P103.Ch09
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module k V]


def functionAction (ρ : Representation k H V) : Representation k G (functions H ρ) where
  toFun g :=
    { toFun := fun f => ⟨fun x => f.1 (g⁻¹ * x), by
        refine ⟨?_, ?_⟩
        · intro x h
          simpa [mul_assoc] using f.2.1 (g⁻¹ * x) h
        · apply (f.2.2.image (fun q : G ⧸ H => g • q)).subset
          rintro q ⟨x, hx, rfl⟩
          refine ⟨QuotientGroup.mk (g⁻¹ * x), ⟨g⁻¹ * x, hx, rfl⟩, ?_⟩
          change QuotientGroup.mk (g * (g⁻¹ * x)) = QuotientGroup.mk x
          simp⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f x; simp
  map_mul' := by intros; ext f x; simp [mul_inv_rev, mul_assoc]

@[simp] theorem functionAction_apply (ρ : Representation k H V) (g : G)
    (f : functions H ρ) (x : G) : (functionAction H ρ g f).1 x = f.1 (g⁻¹ * x) := rfl

variable {H}
variable (ρ : Representation k H V) {T : Set G}
variable (hT : Subgroup.IsComplement T (H : Set G))

def coordinatesToFunction (F : T →₀ V) : functions H ρ :=
  ⟨fun x => ρ ((hT.equiv x).2)⁻¹ (F ((hT.equiv x).1)), by
    refine ⟨?_, ?_⟩
    · intro x h
      change ρ ((hT.equiv (x * h)).2)⁻¹ (F ((hT.equiv (x * h)).1)) = _
      rw [hT.equiv_mul_right]
      simp [mul_inv_rev, map_mul, Module.End.mul_apply]
    · apply (F.support.finite_toSet.image (fun t : T => QuotientGroup.mk (t : G))).subset
      rintro q ⟨x, hx, rfl⟩
      refine ⟨(hT.equiv x).1, ?_, ?_⟩
      · rw [Finset.mem_coe, Finsupp.mem_support_iff]
        contrapose! hx
        simp [Function.mem_support, hx]
      · apply Quotient.sound
        change (QuotientGroup.leftRel H).r _ _
        rw [QuotientGroup.leftRel_apply]
        rw [← hT.equiv_snd_eq_inv_mul x]
        exact (hT.equiv x).2.2⟩

@[simp] theorem coordinatesToFunction_apply (F : T →₀ V) (x : G) :
    (coordinatesToFunction ρ hT F).1 x =
      ρ ((hT.equiv x).2)⁻¹ (F ((hT.equiv x).1)) := rfl

@[simp] theorem equiv_transversal (t : T) : hT.equiv (t : G) = (t, (1 : H)) := by
  rw [← Equiv.eq_symm_apply]
  change (t : G) = (t : G) * (1 : H)
  simp

@[simp] theorem coordinatesToFunction_transversal (F : T →₀ V) (t : T) :
    (coordinatesToFunction ρ hT F).1 t = F t := by
  rw [coordinatesToFunction_apply, equiv_transversal hT]
  simp

def functionCoordinates (f : functions H ρ) : T →₀ V :=
  Finsupp.ofSupportFinite (fun t : T => f.1 t) <| by
    apply (f.2.2.image hT.leftQuotientEquiv).subset
    intro t ht
    refine ⟨QuotientGroup.mk (t : G), ⟨t, ht, rfl⟩, ?_⟩
    exact hT.leftQuotientEquiv.apply_symm_apply t

@[simp] theorem functionCoordinates_apply (f : functions H ρ) (t : T) :
    functionCoordinates ρ hT f t = f.1 t := rfl

@[simp] theorem functionCoordinates_toFunction (F : T →₀ V) :
    functionCoordinates ρ hT (coordinatesToFunction ρ hT F) = F := by
  ext t
  exact coordinatesToFunction_transversal ρ hT F t

@[simp] theorem coordinatesToFunction_fromFunction (f : functions H ρ) :
    coordinatesToFunction ρ hT (functionCoordinates ρ hT f) = f := by
  apply Subtype.ext
  funext x
  change ρ ((hT.equiv x).2)⁻¹ (f.1 ((hT.equiv x).1)) = f.1 x
  simpa only [hT.equiv_fst_mul_equiv_snd x] using
    (f.2.1 ((hT.equiv x).1) ((hT.equiv x).2)).symm

def functionCoordinatesEquiv : (T →₀ V) ≃ₗ[k] functions H ρ where
  toFun := coordinatesToFunction ρ hT
  invFun := functionCoordinates ρ hT
  left_inv := functionCoordinates_toFunction ρ hT
  right_inv := coordinatesToFunction_fromFunction ρ hT
  map_add' := by intros; ext x; simp [coordinatesToFunction]
  map_smul' := by intros; ext x; simp [coordinatesToFunction]


@[simp] theorem functionCoordinatesEquiv_apply (F : T →₀ V) (x : G) :
    (functionCoordinatesEquiv ρ hT F).1 x =
      ρ ((hT.equiv x).2)⁻¹ (F ((hT.equiv x).1)) := rfl

@[simp] theorem functionCoordinatesEquiv_symm_apply (f : functions H ρ) (t : T) :
    (functionCoordinatesEquiv ρ hT).symm f t = f.1 t := rfl


@[simp] theorem coordinatesToFunction_single_mul (t : T) (h : H) (z : V) :
    (coordinatesToFunction ρ hT (Finsupp.single t z)).1 ((t : G) * h) = ρ h⁻¹ z := by
  rw [coordinatesToFunction_apply, hT.equiv_mul_right, equiv_transversal hT]
  simp


private def generatorLinear (t : G) : V →ₗ[k] (G → V) :=
  LinearMap.pi fun x => if hx : x⁻¹ * t ∈ H then ρ ⟨x⁻¹ * t, hx⟩ else 0

private theorem generatorLinear_covariant (t x : G) (h : H) (z : V) :
    generatorLinear ρ t z (x * h) = ρ h⁻¹ (generatorLinear ρ t z x) := by
  classical
  by_cases hx : x⁻¹ * t ∈ H
  · have hnew : (x * h)⁻¹ * t ∈ H := by
      simpa [mul_inv_rev, mul_assoc] using H.mul_mem (H.inv_mem h.2) hx
    have heq : (⟨(x * h)⁻¹ * t, hnew⟩ : H) = h⁻¹ * ⟨x⁻¹ * t, hx⟩ := by
      ext
      simp [mul_inv_rev, mul_assoc]
    simp only [generatorLinear, LinearMap.pi_apply, dite_eq_left hx, dite_eq_left hnew, heq, map_mul, Module.End.mul_apply]
  · have hnew : ¬ (x * h)⁻¹ * t ∈ H := by
      intro hh
      apply hx
      simpa [mul_inv_rev, mul_assoc] using H.mul_mem h.2 hh
    simp only [generatorLinear, LinearMap.pi_apply, dite_eq_right hx, dite_eq_right hnew, LinearMap.zero_apply, map_zero]

private theorem generatorLinear_finite (t : G) (z : V) :
    (QuotientGroup.mk '' Function.support (generatorLinear ρ t z) : Set (G ⧸ H)).Finite := by
  classical
  apply (Set.finite_singleton (QuotientGroup.mk t : G ⧸ H)).subset
  rintro q ⟨x, hx, rfl⟩
  have hmem : x⁻¹ * t ∈ H := by
    by_contra hn
    simp [generatorLinear, hn, Function.mem_support] at hx
  change (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk t
  exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hmem)

/-- The representative-free generator supported on `tH`. -/
def functionGenerator (t : G) : V →ₗ[k] functions H ρ :=
  (generatorLinear ρ t).codRestrict _ fun z =>
    ⟨fun x h => generatorLinear_covariant ρ t x h z, generatorLinear_finite ρ t z⟩

@[simp] theorem functionGenerator_apply (t x : G) (z : V) :
    (functionGenerator ρ t z).1 x =
      if hx : x⁻¹ * t ∈ H then ρ ⟨x⁻¹ * t, hx⟩ z else 0 := by
  by_cases hx : x⁻¹ * t ∈ H <;> simp [functionGenerator, generatorLinear, hx]

@[simp] theorem functionGenerator_mul (t : G) (h : H) (z : V) :
    (functionGenerator ρ t z).1 (t * h) = ρ h⁻¹ z := by
  have hh : (t * h)⁻¹ * t ∈ H := by simp
  have heq : (⟨(t * h)⁻¹ * t, hh⟩ : H) = h⁻¹ := by ext; simp
  simp only [functionGenerator_apply, dite_eq_left hh, heq]

@[simp] theorem functionGenerator_self (t : G) (z : V) :
    (functionGenerator ρ t z).1 t = z := by
  simpa using functionGenerator_mul ρ t (1 : H) z

theorem functionGenerator_zero_off_coset (t x : G) (z : V)
    (hx : (QuotientGroup.mk x : G ⧸ H) ≠ QuotientGroup.mk t) :
    (functionGenerator ρ t z).1 x = 0 := by
  have hh : ¬ x⁻¹ * t ∈ H := by
    intro hh
    exact hx (Quotient.sound (QuotientGroup.leftRel_apply.mpr hh))
  simp [functionGenerator_apply, hh]

@[simp] theorem functionGenerator_balance (t : G) (h : H) (z : V) :
    functionGenerator ρ (t * h) z = functionGenerator ρ t (ρ h z) := by
  classical
  apply Subtype.ext
  funext x
  by_cases hx : x⁻¹ * t ∈ H
  · have hnew : x⁻¹ * (t * h) ∈ H := by
      simpa [mul_assoc] using H.mul_mem hx h.2
    have heq : (⟨x⁻¹ * (t * h), hnew⟩ : H) = ⟨x⁻¹ * t, hx⟩ * h := by
      ext
      simp [mul_assoc]
    simp [functionGenerator_apply, hx, hnew, heq, map_mul, Module.End.mul_apply]
  · have hnew : ¬ x⁻¹ * (t * h) ∈ H := by
      intro hh
      apply hx
      simpa [mul_assoc] using H.mul_mem hh (H.inv_mem h.2)
    simp [functionGenerator_apply, hx, hnew]

@[simp] theorem functionAction_generator (g t : G) (z : V) :
    functionAction H ρ g (functionGenerator ρ t z) = functionGenerator ρ (g * t) z := by
  classical
  apply Subtype.ext
  funext x
  simp [functionGenerator_apply, mul_inv_rev, mul_assoc]


include hT in
theorem functions_ext_transversal (f f' : functions H ρ)
    (hh : ∀ t : T, f.1 t = f'.1 t) : f = f' := by
  apply (functionCoordinatesEquiv ρ hT).symm.injective
  ext t
  exact hh t

@[simp] theorem coordinatesToFunction_single (t : T) (z : V) :
    coordinatesToFunction ρ hT (Finsupp.single t z) = functionGenerator ρ t z := by
  apply functions_ext_transversal ρ hT
  intro s
  rw [coordinatesToFunction_transversal]
  by_cases hst : s = t
  · subst s
    rw [Finsupp.single_eq_same]
    exact (functionGenerator_self ρ t z).symm
  · rw [Finsupp.single_eq_of_ne hst, functionGenerator_zero_off_coset]
    intro hh
    exact hst ((Subgroup.isComplement_subgroup_right_iff_bijective.mp hT).1 hh)

@[simp] theorem coordinatesToFunction_single_decomposition (t : G) (z : V) :
    coordinatesToFunction ρ hT
      (Finsupp.single (hT.equiv t).1 (ρ (hT.equiv t).2 z)) = functionGenerator ρ t z := by
  rw [coordinatesToFunction_single, ← functionGenerator_balance]
  rw [hT.equiv_fst_mul_equiv_snd]

variable {W : Type*} [AddCommGroup W] [Module k W]
variable {σ : Representation k H W}

/-- Postcomposition by an intertwiner preserves the function model. -/
def functionMap (L : ρ.IntertwiningMap σ) : functions H ρ →ₗ[k] functions H σ where
  toFun f := ⟨fun x => L (f.1 x), by
    refine ⟨?_, f.2.2.subset ?_⟩
    · intro x h
      change L (f.1 (x * h)) = _
      rw [f.2.1, L.isIntertwining]
    · rintro q ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      change L (f.1 x) ≠ 0 at hx
      change f.1 x ≠ 0
      intro hz
      exact hx (by simp [hz])⟩
  map_add' := by intros; ext x; simp
  map_smul' := by intros; ext x; simp

@[simp] theorem functionMap_apply (L : ρ.IntertwiningMap σ) (f : functions H ρ) (x : G) :
    (functionMap ρ L f).1 x = L (f.1 x) := rfl

@[simp] theorem functionMap_generator (L : ρ.IntertwiningMap σ) (t : G) (z : V) :
    functionMap ρ L (functionGenerator ρ t z) = functionGenerator σ t (L z) := by
  apply Subtype.ext
  funext x
  by_cases hx : x⁻¹ * t ∈ H
  · simp [functionGenerator_apply, hx, L.isIntertwining]
  · simp [functionGenerator_apply, hx]

@[simp] theorem functionMap_action (L : ρ.IntertwiningMap σ) (g : G) (f : functions H ρ) :
    functionMap ρ L (functionAction H ρ g f) = functionAction H σ g (functionMap ρ L f) := rfl

theorem functionCoordinatesEquiv_natural (L : ρ.IntertwiningMap σ) (F : T →₀ V) :
    functionMap ρ L (functionCoordinatesEquiv ρ hT F) =
      functionCoordinatesEquiv σ hT (Finsupp.mapRange.linearMap L.toLinearMap F) := by
  apply Subtype.ext
  funext x
  change L (ρ ((hT.equiv x).2)⁻¹ (F ((hT.equiv x).1))) =
    σ ((hT.equiv x).2)⁻¹ (L (F ((hT.equiv x).1)))
  exact Representation.IntertwiningMap.isIntertwining ρ σ L _ _

end P103.Ch09

namespace P103.Ch09
open scoped MonoidAlgebra
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
attribute [local instance] rightSubgroupModule inducedAlgebraModule inducedScalarModule
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k H V)

/-- Linear maps out of the induction are determined by the group-basis tensors. -/
theorem induced_hom_ext {W : Type*} [AddCommGroup W] [Module k W]
    {F F' : Induced H ρ →ₗ[k] W}
    (h : ∀ (g : G) (z : V),
      F (tensor H ρ (MonoidAlgebra.single g 1) z) =
      F' (tensor H ρ (MonoidAlgebra.single g 1) z)) : F = F' := by
  apply LinearMap.toAddMonoidHom_injective
  apply BalancedTensor.hom_ext
  intro a z
  change F (tensor H ρ a (ρ.asModuleEquiv z)) = F' (tensor H ρ a (ρ.asModuleEquiv z))
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [tensor_add_left, map_add, ha, hb]
  | single g c =>
    have hs : MonoidAlgebra.single g c = c • MonoidAlgebra.single g 1 := by simp
    rw [hs, ← inducedScalar_smul_tensor]
    simp only [map_smul, h]

variable {T : Set G} (hT : Subgroup.IsComplement T (H : Set G))

/-- Comparison obtained through any transversal coordinates. Its generator
formula below proves that the resulting map is independent of that choice. -/
def functionEquivOfTransversal : Induced H ρ ≃ₗ[k] functions H ρ :=
  (TensorCoordinates.transversalEquiv H ρ hT).symm.trans (functionCoordinatesEquiv ρ hT)

@[simp] theorem functionEquivOfTransversal_basis (g : G) (z : V) :
    functionEquivOfTransversal H ρ hT (tensor H ρ (MonoidAlgebra.single g 1) z) =
      functionGenerator ρ g z := by
  change coordinatesToFunction ρ hT
    (TensorCoordinates.coordinates H ρ hT (tensor H ρ (MonoidAlgebra.single g 1) z)) = _
  rw [TensorCoordinates.coordinates_tensor, TensorCoordinates.coordinateLinear_single, one_smul]
  exact coordinatesToFunction_single_decomposition ρ hT g z

/-- The comparison itself, as well as its inverse, is representative-free. -/
theorem functionEquivOfTransversal_independent {U : Set G}
    (hU : Subgroup.IsComplement U (H : Set G)) :
    functionEquivOfTransversal H ρ hT = functionEquivOfTransversal H ρ hU := by
  apply LinearEquiv.toLinearMap_injective
  apply induced_hom_ext
  intro g z
  simp

/-- A single comparison with the intrinsic function model. -/
def functionEquiv : Induced H ρ ≃ₗ[k] functions H ρ :=
  functionEquivOfTransversal H ρ (default : H.LeftTransversal).property

@[simp] theorem functionEquiv_basis (g : G) (z : V) :
    functionEquiv H ρ (tensor H ρ (MonoidAlgebra.single g 1) z) =
      functionGenerator ρ g z :=
  functionEquivOfTransversal_basis H ρ _ g z

theorem functionEquiv_eq_ofTransversal :
    functionEquiv H ρ = functionEquivOfTransversal H ρ hT :=
  functionEquivOfTransversal_independent H ρ _ hT

/-- This is an equivariant equivalence for the tensor's original left action. -/
theorem functionEquiv_equivariant (g : G) (z : Induced H ρ) :
    functionEquiv H ρ (induction H ρ g z) = functionAction H ρ g (functionEquiv H ρ z) := by
  have heq : (functionEquiv H ρ).toLinearMap.comp (induction H ρ g) =
      (functionAction H ρ g).comp (functionEquiv H ρ).toLinearMap := by
    apply induced_hom_ext
    intro t v
    simp [MonoidAlgebra.single_mul_single]
  exact LinearMap.congr_fun heq z

/-- All parts of the comparison, including its value away from the support. -/
def functionModelData : FunctionModelData H ρ (inductionData H ρ) where
  equivalence := functionEquiv H ρ
  equivariant g z x := congrArg (fun f : functions H ρ => f.1 x)
    (functionEquiv_equivariant H ρ g z)
  generator_mul t h z :=
    (congrArg (fun f : functions H ρ => f.1 (t * h))
      (functionEquiv_basis H ρ t z)).trans (functionGenerator_mul ρ t h z)
  generator_zero t x z hx :=
    (congrArg (fun f : functions H ρ => f.1 x)
      (functionEquiv_basis H ρ t z)).trans (functionGenerator_zero_off_coset ρ t x z hx)

end P103.Ch09

namespace P103.Ch09
open scoped MonoidAlgebra
attribute [local instance] rightSubgroupModule

/-- Tensoring an intertwiner works for every scalar and action construction
satisfying the elementary-tensor formulas. -/
theorem tensor_functoriality : Specs.tensorFunctorialityType.{u,v,w,x} := by
  intro k G _ _ H V _ _ W _ _ ρ σ D D'
  letI := D.module
  letI := D'.module
  intro f
  let A : Induced H ρ →+ Induced H σ :=
    BalancedTensor.map (LinearMap.id : k[G] →ₗ[k[H]ᵐᵒᵖ] k[G])
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f)
  have hA : ∀ (a : k[G]) (z : V), A (tensor H ρ a z) = tensor H σ a (f z) := by
    intro a z
    rfl
  let L : Induced H ρ →ₗ[k] Induced H σ :=
    { __ := A
      map_smul' c z := by
        change A (c • z) = c • A z
        induction z using BalancedTensor.induction_on with
        | h0 => simp
        | ht a b =>
          change A (c • tensor H ρ a (ρ.asModuleEquiv b)) =
            c • A (tensor H ρ a (ρ.asModuleEquiv b))
          rw [D.scalar_tensor, hA, hA, D'.scalar_tensor]
        | ha x y hx hy => simp only [smul_add, map_add, hx, hy] }
  refine ⟨{ __ := L, isIntertwining' := ?_ }, ?_⟩
  · intro g
    apply LinearMap.ext
    intro z
    change A (D.representation g z) = D'.representation g (A z)
    induction z using BalancedTensor.induction_on with
    | h0 => simp
    | ht a b =>
      change A (D.representation g (tensor H ρ a (ρ.asModuleEquiv b))) =
        D'.representation g (A (tensor H ρ a (ρ.asModuleEquiv b)))
      rw [D.action_tensor, hA, hA, D'.action_tensor]
    | ha x y hx hy => simp only [map_add, hx, hy]
  · exact hA

end P103.Ch09

namespace P103.Ch09
open scoped MonoidAlgebra
attribute [local instance] rightSubgroupModule

private theorem functionModelData_generator
    {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (D : InductionData H ρ)
    (E : FunctionModelData H ρ D) (t : G) (z : V) :
    E.equivalence (tensor H ρ (MonoidAlgebra.single t 1) z) = functionGenerator ρ t z := by
  apply Subtype.ext
  funext y
  by_cases hy : (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk t
  · have hh : t⁻¹ * y ∈ H :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact hy.symm)
    let h : H := ⟨t⁻¹ * y, hh⟩
    have hty : t * h = y := by simp [h]
    rw [← hty]
    exact (E.generator_mul t h z).trans (functionGenerator_mul ρ t h z).symm
  · exact (E.generator_zero t y z hy).trans
      (functionGenerator_zero_off_coset ρ t y z hy).symm

theorem model_naturality : Specs.modelNaturalityType.{u,v,w,x} := by
  intro k G _ _ H V _ _ W _ _ ρ σ D D' E E'
  letI := D.module
  letI := D'.module
  intro f F hF z y
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ht a z =>
    change (E'.equivalence (F (tensor H ρ a (ρ.asModuleEquiv z)))).1 y =
      f ((E.equivalence (tensor H ρ a (ρ.asModuleEquiv z))).1 y)
    rw [hF]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      simp only [tensor_add_left, map_add, Submodule.coe_add, Pi.add_apply, ha, hb]
    | single t c =>
      have hc : MonoidAlgebra.single t c = c • (MonoidAlgebra.single t 1 : k[G]) := by simp
      rw [hc, ← D.scalar_tensor, ← D'.scalar_tensor]
      simp only [map_smul, Submodule.coe_smul, Pi.smul_apply]
      rw [functionModelData_generator H ρ D E, functionModelData_generator H σ D' E']
      have hgen := functionMap_generator ρ f t (ρ.asModuleEquiv z)
      exact congrArg (fun q : functions H σ => c • q.1 y) hgen.symm
  | ha a b ha hb =>
    simpa only [map_add, Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) ha hb

end P103.Ch09

namespace P103.Ch09
open scoped MonoidAlgebra
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
attribute [local instance] rightSubgroupModule inducedAlgebraModule inducedScalarModule
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k H V)
variable {T : Set G} (hT : Subgroup.IsComplement T (H : Set G))

include hT in
theorem functionEquiv_inverse_sum (f : functions H ρ) (s : Finset T)
    (hs : ∀ t : T, f.1 t ≠ 0 → t ∈ s) :
    (functionEquiv H ρ).symm f =
      ∑ t ∈ s, tensor H ρ (MonoidAlgebra.single (t : G) 1) (f.1 t) := by
  classical
  rw [functionEquiv_eq_ofTransversal H ρ hT]
  change TensorCoordinates.coordinateSum H ρ (functionCoordinates ρ hT f) = _
  change (functionCoordinates ρ hT f).sum
    (fun t z => tensor H ρ (MonoidAlgebra.single (t : G) 1) z) = _
  rw [Finsupp.sum_of_support_subset _ (s := s)]
  · rfl
  · intro t ht
    exact hs t (Finsupp.mem_support_iff.mp ht)
  · intro t _
    exact tensor_zero_right H ρ _

end P103.Ch09

namespace P103.Ch09
open scoped MonoidAlgebra
attribute [local instance] rightSubgroupModule inducedAlgebraModule inducedScalarModule

/-- The intrinsic function space has the specified left-translation action. -/
theorem function_construction : Specs.functionConstructionType.{u,v,w} := by
  intro k G _ _ H V _ _ ρ
  exact ⟨functionAction H ρ, fun _ _ _ => rfl⟩

/-- Tensor, transversal and finite-coset-support models, with a common
representative-free comparison and the source's finite-dimensional formula. -/
theorem induction_models : Specs.modelsType.{u,v,w} := by
  intro k G _ _ H V _ _ ρ
  refine ⟨inductionData H ρ, functionModelData H ρ, ?_, ?_⟩
  · intro T hT
    refine ⟨TensorCoordinates.transversalEquiv H ρ hT, ?_, ?_⟩
    · exact TensorCoordinates.transversalEquiv_single H ρ hT
    · intro f s hs
      exact functionEquiv_inverse_sum H ρ hT f s hs
  · intro _ _
    exact ⟨TensorCoordinates.induced_finiteDimensional H ρ,
      TensorCoordinates.induced_finrank H ρ⟩

/-- The direct sum in its usual dependent finite-support presentation. -/
theorem direct_sum_construction : Specs.directSumType.{u,v,w} := by
  classical
  intro k G _ _ H V _ _ ρ
  refine ⟨inductionData H ρ, ?_⟩
  intro T hT
  exact ⟨TensorCoordinates.transversalDirectSumEquiv H ρ hT,
    TensorCoordinates.transversalDirectSumEquiv_lof H ρ hT⟩

end P103.Ch09

namespace P103.Ch09.TensorBridge
open scoped MonoidAlgebra
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
attribute [local instance] rightSubgroupModule inducedAlgebraModule inducedScalarModule
variable {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V)

@[simp] theorem tensor_basis_balance (g : G) (h : H) (c : k) (v : V) :
    tensor H ρ (MonoidAlgebra.single (g * h) c) v =
      tensor H ρ (MonoidAlgebra.single g c) (ρ h v) := by
  have ht := tensor_balance H ρ (MonoidAlgebra.single g c) (MonoidAlgebra.single h 1) v
  simpa [subgroupAlgebra_single, MonoidAlgebra.single_mul_single] using ht

/-- Core convention check: the inverted group basis identifies the usual right
balance relation with Mathlib's diagonal left coinvariants. -/
 theorem mathlib_mk_balance (g : G) (h : H) (v : V) :
    Representation.IndV.mk H.subtype ρ ((g * h)⁻¹) v =
      Representation.IndV.mk H.subtype ρ g⁻¹ (ρ h v) := by
  let τ := (Representation.leftRegular k G).comp H.subtype
  have hcv := Representation.Coinvariants.mk_inv_tmul τ ρ
    (MonoidAlgebra.single g⁻¹ 1) v h
  simpa [Representation.IndV.mk, τ, Representation.ofMulAction_single,
    mul_inv_rev] using hcv

/-- The same inversion changes right multiplication in Mathlib into the source's
left multiplication convention. -/
 theorem mathlib_mk_action (g t : G) (v : V) :
    Representation.ind H.subtype ρ g (Representation.IndV.mk H.subtype ρ t⁻¹ v) =
      Representation.IndV.mk H.subtype ρ ((g*t)⁻¹) v := by
  simpa [mul_inv_rev] using Representation.ind_mk H.subtype ρ g t⁻¹ v


/-- Invert the group basis before entering the library coinvariant construction. -/
def mathlibBilinear : k[G] →ₗ[k] V →ₗ[k] Representation.IndV H.subtype ρ :=
  (Finsupp.lift (V →ₗ[k] Representation.IndV H.subtype ρ) k G
    (fun g => Representation.IndV.mk H.subtype ρ g⁻¹)).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem mathlibBilinear_single (g : G) (c : k) (v : V) :
    mathlibBilinear H ρ (MonoidAlgebra.single g c) v =
      c • Representation.IndV.mk H.subtype ρ g⁻¹ v := by
  simp [mathlibBilinear]

 theorem mathlibBilinear_balance (a : k[G]) (r : k[H]) (v : V) :
    mathlibBilinear H ρ (a * subgroupAlgebra H r) v =
      mathlibBilinear H ρ a (ρ.asAlgebraHom r v) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp [mul_add, hr, hs]
  | single h c =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_mul, map_add, LinearMap.add_apply, ha, hb]
    | single g d =>
      simp only [subgroupAlgebra_single, MonoidAlgebra.single_mul_single,
        mathlibBilinear_single, Representation.asAlgebraHom_single, LinearMap.smul_apply,
        map_smul, smul_smul]
      rw [mathlib_mk_balance]
      rw [mul_comm d c]

/-- The full map from the shared tensor, obtained from its actual universal property. -/
def toMathlib : Induced H ρ →+ Representation.IndV H.subtype ρ :=
  BalancedTensor.lift <| BalancedTensor.Pairing.ofFun
    (fun a b => mathlibBilinear H ρ a (ρ.asModuleEquiv b))
    (by intros; simp)
    (by intros; simp)
    (by
      intro r a b
      change mathlibBilinear H ρ (a * subgroupAlgebra H r) (ρ.asModuleEquiv b) = _
      rw [mathlibBilinear_balance]
      rfl)

@[simp] theorem toMathlib_tensor (a : k[G]) (v : V) :
    toMathlib H ρ (tensor H ρ a v) = mathlibBilinear H ρ a v := rfl

@[simp] theorem toMathlib_basis (g : G) (v : V) :
    toMathlib H ρ (tensor H ρ (MonoidAlgebra.single g 1) v) =
      Representation.IndV.mk H.subtype ρ g⁻¹ v := by
  simp


/-- Shared-tensor elementary tensors in the inverse convention, as linear maps. -/
def sourceMk (g : G) : V →ₗ[k] Induced H ρ where
  toFun := tensor H ρ (MonoidAlgebra.single g⁻¹ 1)
  map_add' := tensor_add_right H ρ _
  map_smul' c v := by
    rw [tensor_smul_right, inducedScalar_smul_tensor]
    rfl

/-- The inverse map before quotienting by the diagonal group action. -/
def sourceBilinear : k[G] →ₗ[k] V →ₗ[k] Induced H ρ :=
  (Finsupp.lift (V →ₗ[k] Induced H ρ) k G (sourceMk H ρ)).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem sourceBilinear_single (g : G) (c : k) (v : V) :
    sourceBilinear H ρ (MonoidAlgebra.single g c) v =
      c • tensor H ρ (MonoidAlgebra.single g⁻¹ 1) v := by
  simp [sourceBilinear, sourceMk]

 theorem sourceBilinear_invariant (h : H) :
    TensorProduct.lift (sourceBilinear H ρ) ∘ₗ
      (Representation.tprod ((Representation.leftRegular k G).comp H.subtype) ρ) h =
    TensorProduct.lift (sourceBilinear H ρ) := by
  ext g v
  simp only [LinearMap.coe_comp, Function.comp_apply, Representation.tprod_apply,
    MonoidHom.comp_apply, TensorProduct.map_tmul, Representation.ofMulAction_single,
    TensorProduct.lift.tmul, sourceBilinear_single, mul_inv_rev]
  have ht := tensor_basis_balance H ρ g⁻¹ h⁻¹ 1 (ρ h v)
  simpa using ht

/-- The map from Mathlib's diagonal coinvariants to the shared tensor. -/
def fromMathlib : Representation.IndV H.subtype ρ →ₗ[k] Induced H ρ :=
  Representation.Coinvariants.lift _ (TensorProduct.lift (sourceBilinear H ρ))
    (sourceBilinear_invariant H ρ)

@[simp] theorem fromMathlib_mk (g : G) (v : V) :
    fromMathlib H ρ (Representation.IndV.mk H.subtype ρ g v) =
      tensor H ρ (MonoidAlgebra.single g⁻¹ 1) v := by
  simp [fromMathlib]

/-- Coefficient-field linearity follows by generation of the shared tensor. -/
def toMathlibLinear : Induced H ρ →ₗ[k] Representation.IndV H.subtype ρ where
  __ := toMathlib H ρ
  map_smul' c z := by
    induction z using BalancedTensor.induction_on with
    | h0 => simp
    | ht a b =>
      change toMathlib H ρ (c • tensor H ρ a (ρ.asModuleEquiv b)) =
        c • toMathlib H ρ (tensor H ρ a (ρ.asModuleEquiv b))
      rw [inducedScalar_smul_tensor, toMathlib_tensor, toMathlib_tensor, map_smul]
      rfl
    | ha x y hx hy => simp_all [smul_add]

 theorem from_toMathlib (z : Induced H ρ) :
    fromMathlib H ρ (toMathlib H ρ z) = z := by
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ht a b =>
    change fromMathlib H ρ (toMathlib H ρ (tensor H ρ a (ρ.asModuleEquiv b))) =
      tensor H ρ a (ρ.asModuleEquiv b)
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      change fromMathlib H ρ (toMathlib H ρ
        (tensor H ρ (MonoidAlgebra.single g 1) (ρ.asModuleEquiv b))) = _
      rw [toMathlib_basis, fromMathlib_mk]
      simp
    | add a b ha hb => simp only [tensor_add_left, map_add, ha, hb]
    | smul c a ha =>
      change fromMathlib H ρ (toMathlibLinear H ρ
        (tensor H ρ (c • a) (ρ.asModuleEquiv b))) = _
      rw [← inducedScalar_smul_tensor, map_smul, map_smul]
      change c • fromMathlib H ρ (toMathlib H ρ
        (tensor H ρ a (ρ.asModuleEquiv b))) = _
      rw [ha]
  | ha x y hx hy => simp only [map_add, hx, hy]

 theorem to_fromMathlib (z : Representation.IndV H.subtype ρ) :
    toMathlib H ρ (fromMathlib H ρ z) = z := by
  change ((toMathlibLinear H ρ).comp (fromMathlib H ρ)) z = z
  have he : (toMathlibLinear H ρ).comp (fromMathlib H ρ) =
      (LinearMap.id : Representation.IndV H.subtype ρ →ₗ[k] _) := by
    apply Representation.IndV.hom_ext
    intro g
    ext v
    change toMathlib H ρ (fromMathlib H ρ (Representation.IndV.mk H.subtype ρ g v)) =
      Representation.IndV.mk H.subtype ρ g v
    rw [fromMathlib_mk, toMathlib_basis]
    simp
  rw [he]
  rfl

/-- A linear bridge respecting all source conventions. -/
def mathlibEquiv : Induced H ρ ≃ₗ[k] Representation.IndV H.subtype ρ where
  __ := toMathlibLinear H ρ
  invFun := fromMathlib H ρ
  left_inv := from_toMathlib H ρ
  right_inv := to_fromMathlib H ρ


 theorem mathlibEquiv_equivariant (g : G) (z : Induced H ρ) :
    mathlibEquiv H ρ (induction H ρ g z) =
      Representation.ind H.subtype ρ g (mathlibEquiv H ρ z) := by
  change toMathlibLinear H ρ (induction H ρ g z) =
      Representation.ind H.subtype ρ g (toMathlibLinear H ρ z)
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ht a b =>
    change toMathlibLinear H ρ (induction H ρ g (tensor H ρ a (ρ.asModuleEquiv b))) =
      Representation.ind H.subtype ρ g (toMathlibLinear H ρ (tensor H ρ a (ρ.asModuleEquiv b)))
    induction a using MonoidAlgebra.induction_on with
    | of t =>
      change toMathlib H ρ (induction H ρ g (tensor H ρ
        (MonoidAlgebra.single t 1) (ρ.asModuleEquiv b))) =
        Representation.ind H.subtype ρ g (toMathlib H ρ
          (tensor H ρ (MonoidAlgebra.single t 1) (ρ.asModuleEquiv b)))
      rw [induction_tensor, MonoidAlgebra.single_mul_single, one_mul,
        toMathlib_basis, toMathlib_basis, mathlib_mk_action]
    | add a b ha hb => simp only [tensor_add_left, map_add, ha, hb]
    | smul c a ha =>
      rw [← inducedScalar_smul_tensor]
      simp only [map_smul, RingHom.id_apply]
      rw [ha]
  | ha x y hx hy => simp only [map_add, hx, hy]

end P103.Ch09.TensorBridge

namespace P103.Ch09
open scoped MonoidAlgebra
attribute [local instance] rightSubgroupModule inducedAlgebraModule inducedScalarModule

/-- Mathlib's inverse-coordinate induction is the same left tensor induction. -/
theorem mathlib_bridge : Specs.mathlibBridgeType.{u,v,w} := by
  intro k G _ _ H V _ _ ρ
  refine ⟨inductionData H ρ, TensorBridge.mathlibEquiv H ρ, ?_, ?_, ?_, ?_⟩
  · exact TensorBridge.toMathlib_basis H ρ
  · exact TensorBridge.fromMathlib_mk H ρ
  · exact TensorBridge.mathlibEquiv_equivariant H ρ
  · intro a b z
    exact congrArg (TensorBridge.mathlibEquiv H ρ) (tensor_balance H ρ a b z)

end P103.Ch09
