import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.MackeyDecomposition
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionModels
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Tactic.Group

noncomputable section
universe u v w x
namespace P103.Ch09.Mackey
open scoped MonoidAlgebra DirectSum
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H K : Subgroup G)

@[simp] theorem mem_intersection (s : G) (a : K) :
    a ∈ intersection H K s ↔ s⁻¹ * (a : G) * s ∈ H := Iff.rfl

@[simp] theorem intoSubgroup_coe (s : G) (a : intersection H K s) :
    (intoSubgroup H K s a : G) = s⁻¹ * (a.1 : G) * s := rfl

variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k H V)

@[simp] theorem twist_apply (s : G) (a : intersection H K s) (z : V) :
    twist H K ρ s a z = ρ (intoSubgroup H K s a) z := rfl

/-- A section always exists, including for infinite double-coset sets. -/
def representatives : Representatives H K where
  representative := Quotient.out
  represents := DoubleCoset.out_eq'

/-- Membership in a double coset in subgroup-element coordinates. -/
theorem mem_doubleCoset_iff (s g : G) :
    g ∈ DoubleCoset.doubleCoset s K H ↔
      ∃ (a : K) (h : H), g = (a : G) * s * h := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, h, hh, e⟩
    exact ⟨⟨a, ha⟩, ⟨h, hh⟩, e⟩
  · rintro ⟨a, h, e⟩
    exact ⟨a, a.2, h, h.2, e⟩

theorem mul_mem_doubleCoset (s : G) (a : K) (h : H) :
    (a : G) * s * h ∈ DoubleCoset.doubleCoset s K H :=
  (mem_doubleCoset_iff H K s _).mpr ⟨a, h, rfl⟩

theorem left_mem_doubleCoset (s : G) (a : K) :
    (a : G) * s ∈ DoubleCoset.doubleCoset s K H := by
  simpa using mul_mem_doubleCoset H K s a 1

theorem doubleCoset_left_stable (s g : G)
    (hg : g ∈ DoubleCoset.doubleCoset s K H) (a : K) :
    (a : G) * g ∈ DoubleCoset.doubleCoset s K H := by
  obtain ⟨b, h, rfl⟩ := (mem_doubleCoset_iff H K s g).mp hg
  simpa [mul_assoc] using mul_mem_doubleCoset H K s (a * b) h

theorem doubleCoset_right_stable (s g : G)
    (hg : g ∈ DoubleCoset.doubleCoset s K H) (h : H) :
    g * h ∈ DoubleCoset.doubleCoset s K H := by
  obtain ⟨a, b, rfl⟩ := (mem_doubleCoset_iff H K s g).mp hg
  simpa [mul_assoc] using mul_mem_doubleCoset H K s a (b * h)

/-- Equality of expressions in a double coset gives exactly the balancing
subgroup element needed by the inverse tensor formula. -/
theorem expression_change (s : G) (a a' : K) (h h' : H)
    (he : (a : G) * s * h = (a' : G) * s * h') :
    ∃ ℓ : intersection H K s,
      a = a' * ℓ.1 ∧ intoSubgroup H K s ℓ * h = h' := by
  have hc : s⁻¹ * ((a' : G)⁻¹ * a) * s = (h' : G) * (h : G)⁻¹ := by
    calc
      _ = s⁻¹ * ((a' : G)⁻¹ * ((a : G) * s * h)) * (h : G)⁻¹ := by group
      _ = (h' : G) * (h : G)⁻¹ := by rw [he]; group
  have hm : a'⁻¹ * a ∈ intersection H K s := by
    change s⁻¹ * ((a' : G)⁻¹ * a) * s ∈ H
    rw [hc]
    exact H.mul_mem h'.2 (H.inv_mem h.2)
  refine ⟨⟨a'⁻¹ * a, hm⟩, by simp, ?_⟩
  apply Subtype.ext
  change (s⁻¹ * ((a' : G)⁻¹ * a) * s) * h = h'
  rw [hc]
  group

/-- Equality of stabilizer subgroups under a change s' = a₀ s h₀, written as
membership under the actual inner automorphism of K. -/
theorem intersection_change (s : G) (a₀ : K) (h₀ : H) (a : K) :
    a ∈ intersection H K ((a₀ : G) * s * h₀) ↔
      a₀⁻¹ * a * a₀ ∈ intersection H K s := by
  simp only [mem_intersection, Subgroup.coe_mul, Subgroup.coe_inv]
  have he : ((a₀ : G) * s * h₀)⁻¹ * a * ((a₀ : G) * s * h₀) =
      (h₀ : G)⁻¹ * (s⁻¹ * ((a₀ : G)⁻¹ * a * a₀) * s) * h₀ := by group
  rw [he]
  constructor
  · intro hm
    have := H.mul_mem (H.mul_mem h₀.2 hm) (H.inv_mem h₀.2)
    simpa [mul_assoc] using this
  · intro hm
    exact H.mul_mem (H.mul_mem (H.inv_mem h₀.2) hm) h₀.2

/-- Coordinates changed by a₀,h₀ have the same tensor in the common ambient
induction; this uses the source's right-balancing convention. -/
theorem representative_tensor (s : G) (a₀ a : K) (h₀ : H) (z : V) :
    tensor H ρ (MonoidAlgebra.single ((a : G) * ((a₀ : G) * s * h₀)) 1) z =
      tensor H ρ (MonoidAlgebra.single (((a * a₀ : K) : G) * s) 1) (ρ h₀ z) := by
  rw [← tensor_balance_group]
  simp [MonoidAlgebra.single_mul_single, mul_assoc]

attribute [local instance] rightSubgroupModule inducedAlgebraModule inducedScalarModule

/-- Basis vectors with arbitrary coefficients lie in the actual block. -/
theorem single_mem_block (s g : G) (hg : g ∈ DoubleCoset.doubleCoset s K H) (c : k) :
    MonoidAlgebra.single g c ∈ blockSpace (k := k) H K s := by
  have h1 : MonoidAlgebra.single g (1 : k) ∈ blockSpace (k := k) H K s :=
    Submodule.subset_span ⟨g, hg, rfl⟩
  have he : MulOpposite.op (algebraMap k k[H] c) • MonoidAlgebra.single g 1 =
      MonoidAlgebra.single g c := by
    rw [rightSubgroup_smul, AlgHom.commutes, ← Algebra.commutes, ← Algebra.smul_def]
    simp
  exact he ▸ (blockSpace H K s).smul_mem (MulOpposite.op (algebraMap k k[H] c)) h1

/-- Multiplication on the right by a subgroup-algebra element preserves support
inside KsH. This is the step where the side of the double coset matters. -/
theorem support_right_mul (s : G) (b : k[G])
    (hb : ∀ g ∈ b.coeff.support, g ∈ DoubleCoset.doubleCoset s K H) (r : k[H]) :
    ∀ g ∈ (b * subgroupAlgebra H r).coeff.support, g ∈ DoubleCoset.doubleCoset s K H := by
  classical
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r r' hr hr' =>
    intro g hg
    rw [map_add, mul_add] at hg
    have hg' := Finsupp.support_add hg
    exact (Finset.mem_union.mp hg').elim (hr g) (hr' g)
  | single h c =>
    rw [subgroupAlgebra_single]
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp
      (MonoidAlgebra.support_coeff_mul_single_subset b c (h : G) hg)
    exact doubleCoset_right_stable H K s x (hb x hx) h

/-- The right-module span defining the block is exactly the space of group
algebra elements with finite support in KsH. -/
theorem block_support (s : G) (a : k[G]) :
    a ∈ blockSpace H K s ↔ ∀ g ∈ a.coeff.support, g ∈ DoubleCoset.doubleCoset s K H := by
  classical
  let M : Submodule k[H]ᵐᵒᵖ k[G] :=
    { carrier := {b | ∀ g ∈ b.coeff.support, g ∈ DoubleCoset.doubleCoset s K H}
      zero_mem' := by simp
      add_mem' := by
        intro b c hb hc g hg
        exact (Finset.mem_union.mp (Finsupp.support_add hg)).elim (hb g) (hc g)
      smul_mem' := by
        intro r b hb
        exact support_right_mul H K s b hb r.unop }
  constructor
  · intro ha
    have hle : blockSpace H K s ≤ M := by
      apply Submodule.span_le.mpr
      rintro b ⟨g, hg, rfl⟩ x hx
      have hx' : x = g := by simpa using Finsupp.support_single_subset hx
      exact hx' ▸ hg
    exact hle ha
  · intro ha
    rw [← MonoidAlgebra.sum_coeff_single a]
    apply Submodule.sum_mem
    intro g hg
    exact single_mem_block H K s g (ha g hg) _

theorem block_support_satisfies : Specs.blockSupportType.{u,v} := by
  intro k G _ _ H K s a
  exact block_support H K s a


instance subgroupRightScalarTower : IsScalarTower k k[H]ᵐᵒᵖ k[G] :=
  IsScalarTower.of_algebraMap_smul fun c a => by
    change a * subgroupAlgebra H (algebraMap k k[H] c) = c • a
    rw [AlgHom.commutes, ← Algebra.commutes, ← Algebra.smul_def]

/-- The inherited field action descends to the block tensor. -/
@[instance_reducible] def blockScalarModule (s : G) : Module k (BlockTensor H K ρ s) :=
  BalancedTensor.leftModule
attribute [local instance] blockScalarModule

@[simp] theorem block_smul_tensor (s : G) (c : k)
    (a : blockSpace (k := k) H K s) (z : V) :
    c • blockTensor H K ρ s a z = blockTensor H K ρ s (c • a) z := rfl

theorem blockTensor_smul_right (s : G) (c : k)
    (a : blockSpace (k := k) H K s) (z : V) :
    blockTensor H K ρ s a (c • z) = blockTensor H K ρ s (c • a) z := by
  rw [blockTensor, ρ.asModuleEquiv_symm_map_smul, ← BalancedTensor.balance]
  change BalancedTensor.tmul k[H] ((algebraMap k k[H]ᵐᵒᵖ c) • a) _ = _
  rw [IsScalarTower.algebraMap_smul]
  rfl

/-- Inclusion of a block is induced by inclusion of its right-module factor. -/
def blockInclusion (s : G) : BlockTensor H K ρ s →ₗ[k] Induced H ρ where
  __ := BalancedTensor.map (blockSpace (k := k) H K s).subtype
    (LinearMap.id : ρ.asModule →ₗ[k[H]] ρ.asModule)
  map_smul' c z := by
    induction z using BalancedTensor.induction_on with
    | h0 => simp
    | ht a b =>
      change tensor H ρ ((c • a : blockSpace (k := k) H K s) : k[G])
        (ρ.asModuleEquiv b) = c • tensor H ρ a.1 (ρ.asModuleEquiv b)
      rw [inducedScalar_smul_tensor]
      rfl
    | ha z z' hz hz' =>
      change BalancedTensor.map _ _ (c • z) = c • BalancedTensor.map _ _ z at hz
      change BalancedTensor.map _ _ (c • z') = c • BalancedTensor.map _ _ z' at hz'
      change BalancedTensor.map _ _ (c • (z + z')) = c • BalancedTensor.map _ _ (z + z')
      simp only [smul_add, map_add, hz, hz']

@[simp] theorem blockInclusion_tensor (s : G) (a : blockSpace (k := k) H K s) (z : V) :
    blockInclusion H K ρ s (blockTensor H K ρ s a z) = tensor H ρ a.1 z := rfl

/-- The right-balancing identity on block basis vectors. -/
theorem block_basis_balance (s g : G) (hg : g ∈ DoubleCoset.doubleCoset s K H)
    (h : H) (z : V) :
    blockTensor H K ρ s
      (blockBasis H K s (g * h) (doubleCoset_right_stable H K s g hg h)) z =
      blockTensor H K ρ s (blockBasis H K s g hg) (ρ h z) := by
  have he : blockBasis (k := k) H K s (g * h) (doubleCoset_right_stable H K s g hg h) =
      MulOpposite.op (MonoidAlgebra.single h (1 : k)) • blockBasis (k := k) H K s g hg := by
    apply Subtype.ext
    simp [rightSubgroup_smul, blockBasis, MonoidAlgebra.single_mul_single]
  rw [he, blockTensor, BalancedTensor.balance]
  change BalancedTensor.tmul k[H] _ (ρ.asModuleEquiv.symm
    (ρ.asAlgebraHom (MonoidAlgebra.single h 1) z)) = _
  simp only [Representation.asAlgebraHom_single, one_smul]
  rfl

/-- The elementary block map a⊗v ↦ as⊗v, before taking the quotient. -/
def blockGenerator (s : G) (a : K) : V →ₗ[k] BlockTensor H K ρ s where
  toFun z := blockTensor H K ρ s (blockBasis H K s ((a : G) * s) (left_mem_doubleCoset H K s a)) z
  map_add' z z' := by simp [blockTensor, BalancedTensor.tmul_add]
  map_smul' c z := by rw [blockTensor_smul_right, block_smul_tensor]; rfl

@[simp] theorem blockGenerator_apply (s : G) (a : K) (z : V) :
    blockGenerator H K ρ s a z =
      blockTensor H K ρ s (blockBasis H K s ((a : G) * s) (left_mem_doubleCoset H K s a)) z := rfl

theorem blockGenerator_balance (s : G) (a : K) (ℓ : intersection H K s) (z : V) :
    blockGenerator H K ρ s (a * ℓ.1) z =
      blockGenerator H K ρ s a (twist H K ρ s ℓ z) := by
  have he : ((a * ℓ.1 : K) : G) * s = ((a : G) * s) * intoSubgroup H K s ℓ := by
    simp only [Subgroup.coe_mul, intoSubgroup_coe]
    group
  simpa only [blockGenerator_apply, he, twist_apply] using
    block_basis_balance H K ρ s ((a : G) * s) (left_mem_doubleCoset H K s a)
      (intoSubgroup H K s ℓ) z

/-- Linear extension in the first tensor factor. -/
def blockBilinear (s : G) : k[K] →ₗ[k] V →ₗ[k] BlockTensor H K ρ s :=
  (Finsupp.linearCombination k (blockGenerator H K ρ s)).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem blockBilinear_single (s : G) (a : K) (c : k) (z : V) :
    blockBilinear H K ρ s (MonoidAlgebra.single a c) z = c • blockGenerator H K ρ s a z := by
  simp [blockBilinear]

theorem blockBilinear_balance (s : G) (r : k[intersection H K s]) (a : k[K])
    (z : (twist H K ρ s).asModule) :
    blockBilinear H K ρ s (MulOpposite.op r • a) ((twist H K ρ s).asModuleEquiv z) =
      blockBilinear H K ρ s a ((twist H K ρ s).asModuleEquiv (r • z)) := by
  rw [rightSubgroup_smul]
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r r' hr hr' =>
    simp only [map_add, mul_add, LinearMap.add_apply, add_smul, hr, hr']
  | single ℓ c =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_mul, map_add, LinearMap.add_apply, ha, hb]
    | single a d =>
      simp only [subgroupAlgebra_single, MonoidAlgebra.single_mul_single,
        blockBilinear_single, Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_single, LinearMap.smul_apply]
      simp only [map_smul, blockGenerator_balance, smul_smul]

def blockPairing (s : G) : BalancedTensor.Pairing k[intersection H K s]
    (A := k[K]) (B := (twist H K ρ s).asModule) (BlockTensor H K ρ s) :=
  BalancedTensor.Pairing.ofFun
    (fun a z => blockBilinear H K ρ s a ((twist H K ρ s).asModuleEquiv z))
    (by intros; simp) (by intros; simp) (blockBilinear_balance H K ρ s)

/-- The balanced block map, on the common noncommutative tensor interface. -/
def toBlock (s : G) :
    Induced (intersection H K s) (twist H K ρ s) →ₗ[k] BlockTensor H K ρ s where
  __ := BalancedTensor.lift (blockPairing H K ρ s)
  map_smul' c z := by
    induction z using BalancedTensor.induction_on with
    | h0 => simp
    | ht a b =>
      change BalancedTensor.lift _ (c • tensor (intersection H K s) (twist H K ρ s) a
        ((twist H K ρ s).asModuleEquiv b)) = _
      rw [inducedScalar_smul_tensor]
      simp [blockPairing, blockBilinear, tensor, BalancedTensor.Pairing.ofFun]
    | ha z z' hz hz' =>
      change BalancedTensor.lift _ (c • z) = c • BalancedTensor.lift _ z at hz
      change BalancedTensor.lift _ (c • z') = c • BalancedTensor.lift _ z' at hz'
      change BalancedTensor.lift _ (c • (z + z')) = c • BalancedTensor.lift _ (z + z')
      simp only [smul_add, map_add, hz, hz']

@[simp] theorem toBlock_tensor (s : G) (a : k[K]) (z : V) :
    toBlock H K ρ s (tensor (intersection H K s) (twist H K ρ s) a z) =
      blockBilinear H K ρ s a z := rfl

/-- Canonical map of a Mackey summand into the restricted induction. -/
def toGlobal (s : G) : Induced (intersection H K s) (twist H K ρ s) →ₗ[k] Induced H ρ :=
  (blockInclusion H K ρ s).comp (toBlock H K ρ s)

@[simp] theorem toGlobal_basis (s : G) (a : K) (z : V) :
    toGlobal H K ρ s (tensor (intersection H K s) (twist H K ρ s)
      (MonoidAlgebra.single a 1) z) = tensor H ρ (MonoidAlgebra.single ((a : G) * s) 1) z := by
  simp [toGlobal, blockBasis]

/-- Pulling back the global function model along a ↦ as. Its values are used to
separate Mackey summands; no support restriction on K is assumed here. -/
def pullback (s : G) : Induced H ρ →ₗ[k] (K → V) where
  toFun z a := (functionEquiv H ρ z).1 ((a : G) * s)
  map_add' z z' := by ext a; simp
  map_smul' c z := by ext a; simp

theorem pullback_toGlobal (s : G)
    (z : Induced (intersection H K s) (twist H K ρ s)) (x : K) :
    pullback H K ρ s (toGlobal H K ρ s z) x =
      (functionEquiv (intersection H K s) (twist H K ρ s) z).1 x := by
  have he : (pullback H K ρ s).comp (toGlobal H K ρ s) =
      (functions (intersection H K s) (twist H K ρ s)).subtype.comp
        (functionEquiv (intersection H K s) (twist H K ρ s)).toLinearMap := by
    apply induced_hom_ext
    intro a z
    ext x
    simp only [LinearMap.comp_apply, toGlobal_basis, pullback, LinearMap.coe_mk,
      AddHom.coe_mk, functionEquiv_basis, Submodule.coe_subtype]
    change (functionGenerator ρ ((a : G) * s) z).1 ((x : G) * s) =
      (functionEquiv (intersection H K s) (twist H K ρ s)
        (tensor (intersection H K s) (twist H K ρ s) (MonoidAlgebra.single a 1) z)).1 x
    rw [functionEquiv_basis]
    by_cases hx : x⁻¹ * a ∈ intersection H K s
    · have hh : ((x : G) * s)⁻¹ * ((a : G) * s) ∈ H := by
        simpa [mem_intersection, mul_inv_rev, mul_assoc] using hx
      simp only [functionGenerator_apply, dite_eq_left hh, dite_eq_left hx, twist_apply]
      congr 2
      apply Subtype.ext
      simp [intoSubgroup, conjugation, mul_inv_rev, mul_assoc]
    · have hh : ¬ ((x : G) * s)⁻¹ * ((a : G) * s) ∈ H := by
        simpa [mem_intersection, mul_inv_rev, mul_assoc] using hx
      simp only [functionGenerator_apply, dite_eq_right hh, dite_eq_right hx]
  exact congrFun (LinearMap.congr_fun he z) x

/-- A summand embeds without any finiteness or nonzero hypothesis on V. -/
theorem toGlobal_injective (s : G) : Function.Injective (toGlobal H K ρ s) := by
  intro z z' he
  apply (functionEquiv (intersection H K s) (twist H K ρ s)).injective
  apply Subtype.ext
  funext x
  rw [← pullback_toGlobal, ← pullback_toGlobal, he]

/-- The forward block map respects the full K-action. -/
theorem toGlobal_equivariant (s : G) (a : K)
    (z : Induced (intersection H K s) (twist H K ρ s)) :
    toGlobal H K ρ s (induction (intersection H K s) (twist H K ρ s) a z) =
      induction H ρ (a : G) (toGlobal H K ρ s z) := by
  have he : (toGlobal H K ρ s).comp (induction (intersection H K s) (twist H K ρ s) a) =
      (induction H ρ (a : G)).comp (toGlobal H K ρ s) := by
    apply induced_hom_ext
    intro b z
    simp [MonoidAlgebra.single_mul_single, mul_assoc]
  exact LinearMap.congr_fun he z

/-- Distinct double cosets have zero cross-coordinates in the function model. -/
theorem pullback_other (s t : G)
    (hst : DoubleCoset.mk K H s ≠ DoubleCoset.mk K H t)
    (z : Induced (intersection H K t) (twist H K ρ t)) :
    pullback H K ρ s (toGlobal H K ρ t z) = 0 := by
  have he : (pullback H K ρ s).comp (toGlobal H K ρ t) = 0 := by
    apply induced_hom_ext
    intro a z
    ext x
    simp only [LinearMap.comp_apply, toGlobal_basis, pullback, LinearMap.coe_mk,
      AddHom.coe_mk, functionEquiv_basis, LinearMap.zero_apply, Pi.zero_apply]
    apply functionGenerator_zero_off_coset
    intro hx
    have hm : ((x : G) * s)⁻¹ * ((a : G) * t) ∈ H :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact hx)
    apply hst
    have hh : DoubleCoset.mk K H ((a : G) * t) = DoubleCoset.mk K H ((x : G) * s) := by
      apply (DoubleCoset.eq).mpr
      exact ⟨1, K.one_mem, _, H.inv_mem hm, by simp only [mul_inv_rev]; group⟩
    simpa using hh.symm
  exact LinearMap.congr_fun he z

set_option maxHeartbeats 2000000 in
/-- The block map is onto: every basis element has an expression ash, and
right-module span and tensor generation extend this to the whole block. -/
theorem toBlock_surjective (s : G) : Function.Surjective (toBlock H K ρ s) := by
  have ht : ∀ (a : blockSpace (k := k) H K s) (z : V),
      blockTensor H K ρ s a z ∈ LinearMap.range (toBlock H K ρ s) := by
    intro a
    obtain ⟨a, ha⟩ := a
    induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, hg, rfl⟩ := hb
      obtain ⟨a, h, rfl⟩ := (mem_doubleCoset_iff H K s g).mp hg
      intro z
      refine ⟨tensor (intersection H K s) (twist H K ρ s) (MonoidAlgebra.single a 1) (ρ h z), ?_⟩
      simpa only [toBlock_tensor, blockBilinear_single, one_smul, blockGenerator_apply, blockBasis]
        using (block_basis_balance H K ρ s ((a : G) * s)
          (left_mem_doubleCoset H K s a) h z).symm
    | zero =>
      intro z
      change BalancedTensor.tmul k[H] (0 : blockSpace (k := k) H K s) _ ∈ _
      simp
    | add a b ha hb ia ib =>
      intro z
      change BalancedTensor.tmul k[H] ((⟨a, ha⟩ : blockSpace (k := k) H K s) + ⟨b, hb⟩) _ ∈ _
      rw [BalancedTensor.add_tmul]
      exact (LinearMap.range (toBlock H K ρ s)).add_mem (ia z) (ib z)
    | smul r a ha ia =>
      intro z
      change BalancedTensor.tmul k[H] (r • (⟨a, ha⟩ : blockSpace (k := k) H K s))
        (ρ.asModuleEquiv.symm z) ∈ _
      rw [← MulOpposite.op_unop r, BalancedTensor.balance]
      exact ia (ρ.asModuleEquiv (r.unop • ρ.asModuleEquiv.symm z))
  intro z
  change z ∈ LinearMap.range (toBlock H K ρ s)
  induction z using BalancedTensor.induction_on with
  | h0 => exact Submodule.zero_mem _
  | ht a b => exact ht a (ρ.asModuleEquiv b)
  | ha z z' hz hz' => exact Submodule.add_mem _ hz hz'

/-- The ambient function coordinates prove that the block map is also one-to-one. -/
theorem toBlock_injective (s : G) : Function.Injective (toBlock H K ρ s) :=
  Function.Injective.of_comp (toGlobal_injective H K ρ s)

def blockEquiv (s : G) :
    Induced (intersection H K s) (twist H K ρ s) ≃ₗ[k] BlockTensor H K ρ s :=
  LinearEquiv.ofBijective (toBlock H K ρ s)
    ⟨toBlock_injective H K ρ s, toBlock_surjective H K ρ s⟩

@[simp] theorem blockEquiv_apply (s : G) (z) :
    blockEquiv H K ρ s z = toBlock H K ρ s z := rfl

theorem blockInclusion_injective (s : G) : Function.Injective (blockInclusion H K ρ s) := by
  intro z z' he
  obtain ⟨x, rfl⟩ := toBlock_surjective H K ρ s z
  obtain ⟨y, rfl⟩ := toBlock_surjective H K ρ s z'
  exact congrArg (toBlock H K ρ s) (toGlobal_injective H K ρ s he)

/-- Transport of the K-action along the proved block equivalence. -/
def blockRepresentation (s : G) : Representation k K (BlockTensor H K ρ s) :=
  (blockEquiv H K ρ s).conjRingEquiv.toMonoidHom.comp
    (induction (intersection H K s) (twist H K ρ s))

theorem blockInclusion_equivariant (s : G) (a : K) (z : BlockTensor H K ρ s) :
    blockInclusion H K ρ s (blockRepresentation H K ρ s a z) =
      induction H ρ (a : G) (blockInclusion H K ρ s z) := by
  obtain ⟨x, rfl⟩ := (blockEquiv H K ρ s).surjective z
  change blockInclusion H K ρ s ((blockEquiv H K ρ s)
    (induction (intersection H K s) (twist H K ρ s) a
      ((blockEquiv H K ρ s).symm ((blockEquiv H K ρ s) x)))) = _
  rw [(blockEquiv H K ρ s).symm_apply_apply]
  exact toGlobal_equivariant H K ρ s a x

/-- The transported representation has the source's actual action on basis tensors. -/
@[reducible] def blockAction (s : G) : BlockAction H K ρ s where
  module := blockScalarModule H K ρ s
  representation := blockRepresentation H K ρ s
  scalar_basis c g hg z := by rw [block_smul_tensor, blockTensor_smul_right]
  action_basis a g hg z := by
    refine ⟨doubleCoset_left_stable H K s g hg a, ?_⟩
    apply blockInclusion_injective H K ρ s
    simp [blockInclusion_equivariant, MonoidAlgebra.single_mul_single, blockBasis]

/-- The complete tensor identification, including the inverse on ash⊗v. -/
def blockEquivalence (s : G) : BlockEquivalence H K ρ s (inductionData H ρ)
    (inductionData (intersection H K s) (twist H K ρ s)) (blockAction H K ρ s) where
  equivalence := blockEquiv H K ρ s
  inclusion := blockInclusion H K ρ s
  inclusion_injective := blockInclusion_injective H K ρ s
  inclusion_tensor := blockInclusion_tensor H K ρ s
  forward a z := ⟨left_mem_doubleCoset H K s a, by
    change toBlock H K ρ s (tensor (intersection H K s) (twist H K ρ s)
      (MonoidAlgebra.single a 1) z) = _
    simp⟩
  inverse a h z := by
    refine ⟨mul_mem_doubleCoset H K s a h, ?_⟩
    change (blockEquiv H K ρ s).symm
      (blockTensor H K ρ s (blockBasis H K s ((a : G) * s * h) _) z) = _
    apply (blockEquiv H K ρ s).injective
    rw [(blockEquiv H K ρ s).apply_symm_apply]
    simpa only [blockEquiv_apply, toBlock_tensor, blockBilinear_single, one_smul,
      blockGenerator_apply] using (block_basis_balance H K ρ s ((a : G) * s)
      (left_mem_doubleCoset H K s a) h z)
  equivariant a z := by
    change (blockEquiv H K ρ s) (induction (intersection H K s) (twist H K ρ s) a z) =
      blockRepresentation H K ρ s a ((blockEquiv H K ρ s) z)
    change _ = (blockEquiv H K ρ s) (induction (intersection H K s) (twist H K ρ s) a
      ((blockEquiv H K ρ s).symm ((blockEquiv H K ρ s) z)))
    rw [(blockEquiv H K ρ s).symm_apply_apply]

variable (R : Representatives H K)
local instance : DecidableEq (DoubleCoset.Quotient (K : Set G) H) := Classical.decEq _

abbrev Summand (q : DoubleCoset.Quotient (K : Set G) H) :=
  Induced (intersection H K (R.representative q)) (twist H K ρ (R.representative q))

abbrev Summands := ⨁ q : DoubleCoset.Quotient (K : Set G) H, Summand H K ρ R q

/-- The sum of all canonical summand embeddings. -/
def sumToGlobal : Summands H K ρ R →ₗ[k] Induced H ρ :=
  DirectSum.toModule k _ _ (fun q => toGlobal H K ρ (R.representative q))

@[simp] theorem sumToGlobal_lof (q) (z) :
    sumToGlobal H K ρ R (DirectSum.lof k _ (Summand H K ρ R) q z) = toGlobal H K ρ (R.representative q) z := by
  classical
  exact DirectSum.toModule_lof k (φ := fun q => toGlobal H K ρ (R.representative q)) q z

/-- Each block coordinate of the global sum recovers precisely its corresponding
summand function, so infinite index sets cause no product/sum ambiguity. -/
theorem pullback_sum (d : Summands H K ρ R) (q) (x : K) :
    pullback H K ρ (R.representative q) (sumToGlobal H K ρ R d) x =
      (functionEquiv (intersection H K (R.representative q))
        (twist H K ρ (R.representative q)) (d q)).1 x := by
  classical
  induction d using DirectSum.induction_on with
  | zero => simp
  | of i z =>
    by_cases hi : i = q
    · subst i
      change pullback H K ρ (R.representative q)
        (sumToGlobal H K ρ R (DirectSum.lof k _ (Summand H K ρ R) q z)) x = _
      rw [sumToGlobal_lof]
      simpa using pullback_toGlobal H K ρ (R.representative q) z x
    · have hne : DoubleCoset.mk K H (R.representative q) ≠
          DoubleCoset.mk K H (R.representative i) := by
        rw [R.represents, R.represents]
        exact Ne.symm hi
      change pullback H K ρ (R.representative q)
        (sumToGlobal H K ρ R (DirectSum.lof k _ (Summand H K ρ R) i z)) x = _
      rw [sumToGlobal_lof, pullback_other H K ρ _ _ hne]
      simp [DirectSum.of_eq_of_ne i q z (Ne.symm hi)]
  | add d d' hd hd' => simp [hd, hd']

theorem sumToGlobal_injective : Function.Injective (sumToGlobal H K ρ R) := by
  intro d d' he
  ext q
  apply (functionEquiv (intersection H K (R.representative q))
    (twist H K ρ (R.representative q))).injective
  apply Subtype.ext
  funext x
  rw [← pullback_sum, ← pullback_sum, he]

/-- Every group-basis tensor lies in its unique double-coset summand. -/
theorem sumToGlobal_surjective : Function.Surjective (sumToGlobal H K ρ R) := by
  classical
  have hb : ∀ (g : G) (z : V),
      tensor H ρ (MonoidAlgebra.single g 1) z ∈ LinearMap.range (sumToGlobal H K ρ R) := by
    intro g z
    let q := DoubleCoset.mk K H g
    obtain ⟨a, ha, h, hh, he⟩ := DoubleCoset.eq.mp (R.represents q)
    refine ⟨DirectSum.lof k _ (Summand H K ρ R) q (tensor (intersection H K (R.representative q))
      (twist H K ρ (R.representative q)) (MonoidAlgebra.single (⟨a, ha⟩ : K) 1)
        (ρ ⟨h, hh⟩ z)), ?_⟩
    rw [sumToGlobal_lof, toGlobal_basis, ← tensor_balance_group]
    simp [MonoidAlgebra.single_mul_single, he]
  intro z
  change z ∈ LinearMap.range (sumToGlobal H K ρ R)
  induction z using BalancedTensor.induction_on with
  | h0 => exact Submodule.zero_mem _
  | ht a b =>
    change tensor H ρ a (ρ.asModuleEquiv b) ∈ _
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a a' ha ha' =>
      rw [tensor_add_left]
      exact Submodule.add_mem _ ha ha'
    | single g c =>
      have he : MonoidAlgebra.single g c = c • MonoidAlgebra.single g 1 := by simp
      rw [he, ← inducedScalar_smul_tensor]
      exact Submodule.smul_mem _ c (hb g _)
  | ha z z' hz hz' => exact Submodule.add_mem _ hz hz'

/-- The Mackey isomorphism in the direction stated in the source. -/
def decompositionEquiv : Induced H ρ ≃ₗ[k] Summands H K ρ R :=
  (LinearEquiv.ofBijective (sumToGlobal H K ρ R)
    ⟨sumToGlobal_injective H K ρ R, sumToGlobal_surjective H K ρ R⟩).symm

/-- Componentwise K-action commutes with summing the summand embeddings. -/
theorem sumToGlobal_equivariant (a : K) (d : Summands H K ρ R) :
    sumToGlobal H K ρ R
      (DirectSum.lmap (fun q => induction (intersection H K (R.representative q))
        (twist H K ρ (R.representative q)) a) d) =
      induction H ρ (a : G) (sumToGlobal H K ρ R d) := by
  classical
  induction d using DirectSum.induction_on with
  | zero => simp
  | of q z =>
    change sumToGlobal H K ρ R
      (DirectSum.lmap _ (DirectSum.lof k _ (Summand H K ρ R) q z)) =
        induction H ρ (a : G) (sumToGlobal H K ρ R (DirectSum.lof k _ (Summand H K ρ R) q z))
    rw [DirectSum.lmap_lof, sumToGlobal_lof, sumToGlobal_lof]
    exact toGlobal_equivariant H K ρ _ a z
  | add d d' hd hd' => simp [hd, hd']

/-- All pieces of the source's Mackey construction. -/
def decomposition : Decomposition H K ρ R where
  globalAction := inductionData H ρ
  summandAction s := inductionData (intersection H K s) (twist H K ρ s)
  blockAction := blockAction H K ρ
  blockEquivalence := blockEquivalence H K ρ
  equivalence := decompositionEquiv H K ρ R
  summand_formula q a z := by
    change sumToGlobal H K ρ R (DirectSum.lof k _ (Summand H K ρ R) q _) = _
    rw [sumToGlobal_lof]
    exact toGlobal_basis H K ρ _ a z
  equivariant a z := by
    change decompositionEquiv H K ρ R (induction H ρ (a : G) z) =
      DirectSum.lmap (fun q => induction (intersection H K (R.representative q))
        (twist H K ρ (R.representative q)) a) (decompositionEquiv H K ρ R z)
    apply (decompositionEquiv H K ρ R).symm.injective
    rw [(decompositionEquiv H K ρ R).symm_apply_apply]
    change _ = sumToGlobal H K ρ R _
    rw [sumToGlobal_equivariant]
    change _ = induction H ρ (a : G) ((decompositionEquiv H K ρ R).symm
      (decompositionEquiv H K ρ R z))
    rw [(decompositionEquiv H K ρ R).symm_apply_apply]

theorem mackey_decomposition : Specs.decompositionType.{u,v,w} := by
  intro k G _ _ H K V _ _ ρ R
  exact ⟨decomposition H K ρ R⟩

/-- The tensor formulas force the scalar structure, even when a construction
was supplied abstractly as `InductionData`. -/
theorem inductionData_module (D : InductionData H ρ) :
    D.module = inducedScalarModule H ρ := by
  apply Module.ext'
  intro c z
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ht a b =>
    exact (D.scalar_tensor c a (ρ.asModuleEquiv b)).trans
      (inducedScalar_smul_tensor H ρ c a (ρ.asModuleEquiv b)).symm
  | ha z z' hz hz' =>
    calc
      (letI := D.module; c • (z + z')) = (letI := D.module; c • z + c • z') := by
        letI := D.module
        exact smul_add c z z'
      _ = (letI := inducedScalarModule H ρ; c • z + c • z') := congrArg₂ (· + ·) hz hz'
      _ = (letI := inducedScalarModule H ρ; c • (z + z')) := by
        letI := inducedScalarModule H ρ
        exact (smul_add c z z').symm

/-- No freedom remains in either action once its elementary-tensor formulas
are fixed. This permits comparisons for every construction in the Specs. -/
theorem inductionData_unique (D : InductionData H ρ) : D = inductionData H ρ := by
  cases D with
  | mk m r hs ha =>
    have hm : m = inducedScalarModule H ρ := inductionData_module H ρ ⟨m, r, hs, ha⟩
    subst m
    have hr : r = induction H ρ := by
      apply MonoidHom.ext
      intro g
      apply LinearMap.toAddMonoidHom_injective
      apply BalancedTensor.hom_ext
      intro a b
      exact ha g a (ρ.asModuleEquiv b)
    subst r
    rfl

/-- The image of a summand is characterized intrinsically by its double coset. -/
theorem range_toGlobal (s : G) :
    LinearMap.range (toGlobal H K ρ s) = Submodule.span k
      {y | ∃ (g : G), g ∈ DoubleCoset.doubleCoset s K H ∧
        ∃ z : V, y = tensor H ρ (MonoidAlgebra.single g 1) z} := by
  let M := Submodule.span k
    {y | ∃ (g : G), g ∈ DoubleCoset.doubleCoset s K H ∧
      ∃ z : V, y = tensor H ρ (MonoidAlgebra.single g 1) z}
  apply le_antisymm
  · rintro y ⟨z, rfl⟩
    induction z using BalancedTensor.induction_on with
    | h0 => exact M.zero_mem
    | ht a b =>
      change toGlobal H K ρ s (tensor (intersection H K s) (twist H K ρ s) a
        ((twist H K ρ s).asModuleEquiv b)) ∈ M
      induction a using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a a' ha ha' =>
        rw [tensor_add_left, map_add]
        exact M.add_mem ha ha'
      | single a c =>
        have he : MonoidAlgebra.single a c = c • MonoidAlgebra.single a 1 := by simp
        rw [he, ← inducedScalar_smul_tensor, map_smul, toGlobal_basis]
        exact M.smul_mem c (Submodule.subset_span
          ⟨_, left_mem_doubleCoset H K s a, _, rfl⟩)
    | ha z z' hz hz' =>
      rw [map_add]
      exact M.add_mem hz hz'
  · apply Submodule.span_le.mpr
    rintro y ⟨g, hg, z, rfl⟩
    obtain ⟨a, h, rfl⟩ := (mem_doubleCoset_iff H K s g).mp hg
    refine ⟨tensor (intersection H K s) (twist H K ρ s) (MonoidAlgebra.single a 1) (ρ h z), ?_⟩
    rw [toGlobal_basis, ← tensor_balance_group]
    simp [MonoidAlgebra.single_mul_single]

theorem range_toGlobal_change (s : G) (a₀ : K) (h₀ : H) :
    LinearMap.range (toGlobal H K ρ ((a₀ : G) * s * h₀)) = LinearMap.range (toGlobal H K ρ s) := by
  rw [range_toGlobal, range_toGlobal,
    DoubleCoset.doubleCoset_eq_of_mem (mul_mem_doubleCoset H K s a₀ h₀)]

/-- Comparison through the common embedded block; its coordinate formula below
proves that the construction is independent of any auxiliary choices. -/
def representativeComparison (s : G) (a₀ : K) (h₀ : H) :
    Induced (intersection H K ((a₀ : G) * s * h₀)) (twist H K ρ ((a₀ : G) * s * h₀)) ≃ₗ[k]
      Induced (intersection H K s) (twist H K ρ s) :=
  (LinearEquiv.ofInjective (toGlobal H K ρ ((a₀ : G) * s * h₀))
    (toGlobal_injective H K ρ _)).trans
    ((LinearEquiv.ofEq _ _ (range_toGlobal_change H K ρ s a₀ h₀)).trans
      (LinearEquiv.ofInjective (toGlobal H K ρ s) (toGlobal_injective H K ρ s)).symm)

@[simp] theorem representativeComparison_global (s : G) (a₀ : K) (h₀ : H) (z) :
    toGlobal H K ρ s (representativeComparison H K ρ s a₀ h₀ z) =
      toGlobal H K ρ ((a₀ : G) * s * h₀) z := by
  simp [representativeComparison]

@[simp] theorem representativeComparison_basis (s : G) (a₀ a : K) (h₀ : H) (z : V) :
    representativeComparison H K ρ s a₀ h₀
      (tensor (intersection H K ((a₀ : G) * s * h₀))
        (twist H K ρ ((a₀ : G) * s * h₀)) (MonoidAlgebra.single a 1) z) =
      tensor (intersection H K s) (twist H K ρ s) (MonoidAlgebra.single (a * a₀) 1) (ρ h₀ z) := by
  apply toGlobal_injective H K ρ s
  rw [representativeComparison_global, toGlobal_basis, toGlobal_basis]
  exact representative_tensor H K ρ s a₀ a h₀ z

theorem representativeComparison_equivariant (s : G) (a₀ : K) (h₀ : H) (a : K) (z) :
    representativeComparison H K ρ s a₀ h₀
      (induction (intersection H K ((a₀ : G) * s * h₀)) (twist H K ρ ((a₀ : G) * s * h₀)) a z) =
      induction (intersection H K s) (twist H K ρ s) a (representativeComparison H K ρ s a₀ h₀ z) := by
  apply toGlobal_injective H K ρ s
  rw [representativeComparison_global, toGlobal_equivariant,
    toGlobal_equivariant, representativeComparison_global]

theorem representative_independence : Specs.representativeIndependenceType.{u,v,w} := by
  intro k G _ _ H K V _ _ ρ s a₀ h₀ Ds Ds'
  rw [inductionData_unique _ _ Ds, inductionData_unique _ _ Ds']
  refine ⟨intersection_change H K s a₀ h₀, representativeComparison H K ρ s a₀ h₀, ?_, ?_, ?_⟩
  · exact fun a z => representativeComparison_basis H K ρ s a₀ a h₀ z
  · exact fun a z => representativeComparison_equivariant H K ρ s a₀ h₀ a z
  · exact fun a z => representative_tensor H K ρ s a₀ a h₀ z

section Naturality
variable {W : Type x} [AddCommGroup W] [Module k W]
variable {σ : Representation k H W}

/-- Twisting preserves the actual underlying intertwiner. -/
def twistMap (f : ρ.IntertwiningMap σ) (s : G) :
    (twist H K ρ s).IntertwiningMap (twist H K σ s) where
  __ := f.toLinearMap
  isIntertwining' ℓ := f.isIntertwining' (intoSubgroup H K s ℓ)

theorem toGlobal_natural (f : ρ.IntertwiningMap σ) (s : G) (z) :
    toGlobal H K σ s (inductionMap (intersection H K s) (twistMap H K ρ f s) z) =
      inductionMap H f (toGlobal H K ρ s z) := by
  have he : (toGlobal H K σ s).comp
      (inductionMap (intersection H K s) (twistMap H K ρ f s)).toLinearMap =
      (inductionMap H f).toLinearMap.comp (toGlobal H K ρ s) := by
    apply induced_hom_ext
    intro a z
    simp [twistMap]
    rfl
  exact LinearMap.congr_fun he z

theorem sumToGlobal_natural (f : ρ.IntertwiningMap σ) (d : Summands H K ρ R) :
    sumToGlobal H K σ R
      (DirectSum.lmap (fun q =>
        (inductionMap (intersection H K (R.representative q))
          (twistMap H K ρ f (R.representative q))).toLinearMap) d) =
      inductionMap H f (sumToGlobal H K ρ R d) := by
  classical
  induction d using DirectSum.induction_on with
  | zero => simp
  | of q z =>
    change sumToGlobal H K σ R (DirectSum.lmap _
      (DirectSum.lof k _ (Summand H K ρ R) q z)) =
      inductionMap H f (sumToGlobal H K ρ R (DirectSum.lof k _ (Summand H K ρ R) q z))
    rw [DirectSum.lmap_lof, sumToGlobal_lof, sumToGlobal_lof]
    exact toGlobal_natural H K ρ f _ z
  | add d d' hd hd' => simp [hd, hd']

theorem decompositionEquiv_natural (f : ρ.IntertwiningMap σ) (z : Induced H ρ) :
    decompositionEquiv H K σ R (inductionMap H f z) =
      DirectSum.lmap (fun q =>
        (inductionMap (intersection H K (R.representative q))
          (twistMap H K ρ f (R.representative q))).toLinearMap)
        (decompositionEquiv H K ρ R z) := by
  apply (decompositionEquiv H K σ R).symm.injective
  rw [(decompositionEquiv H K σ R).symm_apply_apply]
  change _ = sumToGlobal H K σ R _
  rw [sumToGlobal_natural]
  change _ = inductionMap H f ((decompositionEquiv H K ρ R).symm
    (decompositionEquiv H K ρ R z))
  rw [(decompositionEquiv H K ρ R).symm_apply_apply]
end Naturality

/-- Any decomposition with the specified summand formulas has this inverse.
In particular, naturality is not dependent on our chosen action construction. -/
theorem decomposition_inverse_unique (A : Decomposition H K ρ R) (d : Summands H K ρ R) :
    A.equivalence.symm d = sumToGlobal H K ρ R d := by
  cases A with
  | mk D Ds B E e he ha =>
    have hD : D = inductionData H ρ := inductionData_unique H ρ D
    subst D
    have hDs : Ds = fun s => inductionData (intersection H K s) (twist H K ρ s) := by
      funext s
      exact inductionData_unique _ _ (Ds s)
    subst Ds
    dsimp only [inductionData] at e he ha
    have h : e.symm.toLinearMap = sumToGlobal H K ρ R := by
      apply LinearMap.toAddMonoidHom_injective
      apply DirectSum.addHom_ext
      intro q z
      have hq : e.symm.toLinearMap.comp (DirectSum.lof k _ (Summand H K ρ R) q) =
          toGlobal H K ρ (R.representative q) := by
        apply induced_hom_ext
        intro a z
        exact (he q a z).trans (toGlobal_basis H K ρ (R.representative q) a z).symm
      change e.symm (DirectSum.lof k _ (Summand H K ρ R) q z) =
        sumToGlobal H K ρ R (DirectSum.lof k _ (Summand H K ρ R) q z)
      rw [sumToGlobal_lof]
      exact LinearMap.congr_fun hq z
    exact LinearMap.congr_fun h d

theorem decomposition_equivalence_unique (A : Decomposition H K ρ R) (z : Induced H ρ) :
    A.equivalence z = decompositionEquiv H K ρ R z := by
  apply A.equivalence.symm.injective
  rw [A.equivalence.symm_apply_apply, decomposition_inverse_unique]
  exact ((decompositionEquiv H K ρ R).symm_apply_apply z).symm

/-- The full naturality statement, for all constructions with the prescribed
scalar and elementary-tensor actions and all H-intertwiners. -/
theorem mackey_naturality : Specs.naturalityType.{u,v,w,x} := by
  intro k G _ _ H K V _ _ W _ _ ρ σ R A B f
  classical
  letI := A.globalAction.module
  letI := B.globalAction.module
  letI := fun q => (A.summandAction (R.representative q)).module
  letI := fun q => (B.summandAction (R.representative q)).module
  obtain ⟨F, hF⟩ := tensor_functoriality H ρ σ A.globalAction B.globalAction f
  have exFs : ∀ q, ∃ Fs :
      (A.summandAction (R.representative q)).representation.IntertwiningMap
        (B.summandAction (R.representative q)).representation,
      ∀ (a : k[K]) z, Fs
        (tensor (intersection H K (R.representative q)) (twist H K ρ (R.representative q)) a z) =
        tensor (intersection H K (R.representative q)) (twist H K σ (R.representative q)) a (f z) := by
    intro q
    exact tensor_functoriality _ _ _ (A.summandAction (R.representative q))
      (B.summandAction (R.representative q)) (twistMap H K ρ f (R.representative q))
  choose Fs hFs using exFs
  refine ⟨F, Fs, hF, hFs, ?_⟩
  intro z
  have hF' : ∀ z, F z = inductionMap H f z := by
    intro z
    induction z using BalancedTensor.induction_on with
    | h0 => simp
    | ht a b => exact hF a (ρ.asModuleEquiv b)
    | ha z z' hz hz' => simp only [map_add, hz, hz']
  have hFs' : ∀ q z, Fs q z = inductionMap (intersection H K (R.representative q))
      (twistMap H K ρ f (R.representative q)) z := by
    intro q z
    induction z using BalancedTensor.induction_on with
    | h0 => simp
    | ht a b => exact hFs q a ((twist H K ρ (R.representative q)).asModuleEquiv b)
    | ha z z' hz hz' => simp only [map_add, hz, hz']
  ext q
  rw [decomposition_equivalence_unique, hF', DirectSum.lmap_apply,
    decomposition_equivalence_unique]
  change _ = Fs q ((decompositionEquiv H K ρ R z) q)
  rw [hFs']
  exact congrArg (fun d => d q) (decompositionEquiv_natural H K ρ R f z)

end P103.Ch09.Mackey
