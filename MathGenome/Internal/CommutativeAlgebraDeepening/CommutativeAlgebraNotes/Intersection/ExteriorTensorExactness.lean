import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorExactness
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Filtration

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.ExteriorTensorExactness

open ExteriorTensorProduct ExteriorTensorInverseLimit
open scoped ExteriorTensorInverseLimit
open LinearMap

noncomputable section

/-- Artin–Rees for the filtration induced by an injective linear map. -/
private theorem exists_comap_pow_le {R L M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (f : L →ₗ[R] M) (hf : Function.Injective f) (i : ℕ) :
    ∃ j, i ≤ j ∧ (I ^ j • (⊤ : Submodule R M)).comap f ≤ I ^ i • ⊤ := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul f.range
  refine ⟨i + c, Nat.le_add_right i c, ?_⟩
  have h : I ^ (i + c) • (⊤ : Submodule R M) ⊓ f.range =
      I ^ i • (I ^ c • ⊤ ⊓ f.range) := by
    simpa only [Nat.add_sub_cancel] using hc (i + c) (Nat.le_add_left c i)
  intro x hx
  have hx' : f x ∈ I ^ (i + c) • (⊤ : Submodule R M) ⊓ f.range :=
    ⟨hx, ⟨x, rfl⟩⟩
  rw [h] at hx'
  change x ∈ (I ^ i • (I ^ c • ⊤ ⊓ f.range)).comap f at hx'
  rw [Submodule.comap_smul'' hf inf_le_right] at hx'
  have hle : I ^ i • (I ^ c • (⊤ : Submodule R M) ⊓ f.range).comap f ≤
      I ^ i • (⊤ : Submodule R L) := smul_mono_right (I ^ i) le_top
  exact hle hx'

private theorem exists_factor_of_ker_le {k E F G : Type*} [Field k]
    [AddCommGroup E] [Module k E] [AddCommGroup F] [Module k F]
    [AddCommGroup G] [Module k G] (f : E →ₗ[k] F) (g : E →ₗ[k] G)
    (h : f.ker ≤ g.ker) : ∃ r : F →ₗ[k] G, r.comp f = g := by
  let q := (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨r, hr⟩ := q.exists_extend
  refine ⟨r, LinearMap.ext fun x => ?_⟩
  have hx : f x ∈ f.range := ⟨x, rfl⟩
  calc
    r (f x) = q ⟨f x, hx⟩ := LinearMap.congr_fun hr (⟨f x, hx⟩ : f.range)
    _ = g x := by
      change (f.ker.liftQ g h) (f.quotKerEquivRange.symm ⟨f x, hx⟩) = g x
      rw [f.quotKerEquivRange_symm_apply_image x hx]
      rfl

/-- A sufficiently deep quotient map induced by an injection factors the
transition to any prescribed shallower quotient of its source as a field-linear map. -/
private theorem quotient_power_factor {k R L M : Type*} [Field k]
    [CommRing R] [Algebra k R] [IsNoetherianRing R]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R)
    [∀ n : ℕ, Module k (L ⧸ (I ^ n • ⊤ : Submodule R L))]
    [∀ n : ℕ, IsScalarTower k R (L ⧸ (I ^ n • ⊤ : Submodule R L))]
    [∀ n : ℕ, Module k (M ⧸ (I ^ n • ⊤ : Submodule R M))]
    [∀ n : ℕ, IsScalarTower k R (M ⧸ (I ^ n • ⊤ : Submodule R M))]
    (f : L →ₗ[R] M) (hf : Function.Injective f) (i : ℕ) :
    ∃ (j : ℕ) (hij : i ≤ j)
      (r : (M ⧸ (I ^ j • ⊤ : Submodule R M)) →ₗ[k]
        (L ⧸ (I ^ i • ⊤ : Submodule R L))),
      r.comp ((quotientLinearMap (I ^ j) f).restrictScalars k) =
        (Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right hij))
          (M := L)).restrictScalars k := by
  obtain ⟨j, hij, h⟩ := exists_comap_pow_le I f hf i
  refine ⟨j, hij, exists_factor_of_ker_le _ _ ?_⟩
  intro z hz
  obtain ⟨x, rfl⟩ := (I ^ j • (⊤ : Submodule R L)).mkQ_surjective z
  have hx : f x ∈ I ^ j • (⊤ : Submodule R M) :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr (h hx)

section TensorReductions

variable (k : Type*) [Field k] (a b : ℕ)
variable {M N M' N' : Type*}
    [AddCommGroup M] [Module (X k a) M] [AddCommGroup N] [Module (Y k b) N]
    [AddCommGroup M'] [Module (X k a) M'] [AddCommGroup N'] [Module (Y k b) N']

local notation "A" => X k a
local notation "B" => Y k b
local notation "R" => S k a b

private def reduction (i j : ℕ) :
    Product k a b M N →ₗ[R] ModuleTensor k a b M N i j :=
  (moduleComparison k a b M N i j).toLinearMap.comp (levelSubmodule k a b _ i j).mkQ

private theorem reduction_natural (f : M →ₗ[A] M') (g : N →ₗ[B] N') (i j : ℕ)
    (t : Product k a b M N) :
    moduleTensorMap k a b M N f g i j (reduction k a b i j t) =
      reduction k a b i j (ExteriorTensorProduct.map f g t) :=
  moduleComparison_natural k a b M N f g i j (Submodule.Quotient.mk t)

private theorem reduction_transition {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j')
    (t : Product k a b M N) :
    tensorTransition k a b M N hi hj (reduction k a b i' j' t) =
      reduction k a b i j t := by
  rw [← tensorTransitionLinear_apply, reduction, LinearMap.comp_apply]
  exact moduleComparison_transition k a b M N hi hj (Submodule.Quotient.mk t)

private theorem eq_zero_of_reductions [Module.Finite A M] [Module.Finite B N]
    {t : Product k a b M N} (ht : ∀ i j, reduction k a b i j t = 0) : t = 0 := by
  apply (limitComparison k a b M N).injective
  rw [map_zero]
  exact Subtype.ext (funext fun i => funext fun j => ht i j)

set_option backward.isDefEq.respectTransparency false in
private theorem map_left_injective [Module.Finite A M] [Module.Finite A M']
    [Module.Finite B N] (f : M →ₗ[A] M') (hf : Function.Injective f) :
    Function.Injective (ExteriorTensorProduct.map f (LinearMap.id : N →ₗ[B] N)) := by
  let F := ExteriorTensorProduct.map f (LinearMap.id : N →ₗ[B] N)
  suffices h : ∀ t, F t = 0 → t = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply h
    have hxy' : F x = F y := hxy
    exact (map_sub F x y).trans (sub_eq_zero.mpr hxy')
  intro t ht
  change ExteriorTensorProduct.map f (LinearMap.id : N →ₗ[B] N) t = 0 at ht
  apply eq_zero_of_reductions k a b
  intro i j
  obtain ⟨i', hi, r, hr⟩ :=
    quotient_power_factor (k := k) (variableIdeal k (Fin a)) f hf i
  have hzero :
      moduleTensorMap k a b M N f (LinearMap.id : N →ₗ[B] N) i' j
        (reduction k a b i' j t) = 0 := by
    rw [reduction_natural, ht, map_zero]
  have hcomp :
      (TensorProduct.map r (LinearMap.id : YN k b N j →ₗ[k] YN k b N j)).comp
        (moduleTensorMap k a b M N f (LinearMap.id : N →ₗ[B] N) i' j) =
      tensorTransition k a b M N hi (le_refl j) := by
    rw [moduleTensorMap, ← TensorProduct.map_comp, hr]
    apply TensorProduct.ext'
    intro x y
    obtain ⟨y, rfl⟩ := (ySubmodule k b N j).mkQ_surjective y
    rfl
  rw [← reduction_transition k a b hi (le_refl j) t, ← hcomp, LinearMap.comp_apply,
    hzero, map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem map_right_injective [Module.Finite A M] [Module.Finite B N]
    [Module.Finite B N'] (f : N →ₗ[B] N') (hf : Function.Injective f) :
    Function.Injective (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) f) := by
  let F := ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) f
  suffices h : ∀ t, F t = 0 → t = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply h
    have hxy' : F x = F y := hxy
    exact (map_sub F x y).trans (sub_eq_zero.mpr hxy')
  intro t ht
  change ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) f t = 0 at ht
  apply eq_zero_of_reductions k a b
  intro i j
  obtain ⟨j', hj, r, hr⟩ :=
    quotient_power_factor (k := k) (variableIdeal k (YIndex b)) f hf j
  have hzero :
      moduleTensorMap k a b M N (LinearMap.id : M →ₗ[A] M) f i j'
        (reduction k a b i j' t) = 0 := by
    rw [reduction_natural, ht, map_zero]
  have hcomp :
      (TensorProduct.map (LinearMap.id : XM k a M i →ₗ[k] XM k a M i) r).comp
        (moduleTensorMap k a b M N (LinearMap.id : M →ₗ[A] M) f i j') =
      tensorTransition k a b M N (le_refl i) hj := by
    rw [moduleTensorMap, ← TensorProduct.map_comp, hr]
    apply TensorProduct.ext'
    intro x y
    obtain ⟨x, rfl⟩ := (xSubmodule k a M i).mkQ_surjective x
    rfl
  rw [← reduction_transition k a b (le_refl i) hj t, ← hcomp, LinearMap.comp_apply,
    hzero, map_zero]

private theorem coe_map_left (f : M →ₗ[A] M') :
    (ExteriorTensorProduct.map f (LinearMap.id : N →ₗ[B] N) :
      Product k a b M N → Product k a b M' N) =
      ((f.baseChange R).restrictScalars B).rTensor N :=
  TensorProduct.AlgebraTensorModule.coe_rTensor (f.baseChange R)

private theorem coe_map_right (f : N →ₗ[B] N') :
    (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) f :
      Product k a b M N → Product k a b M N') = f.lTensor (R ⊗[A] M) := by
  unfold ExteriorTensorProduct.map
  rw [LinearMap.baseChange_id]
  exact TensorProduct.AlgebraTensorModule.coe_lTensor f

end TensorReductions

/-- The exterior tensor product with a fixed right factor preserves short exact sequences. -/
theorem exactLeft : Spec.ExactLeft := by
  intro k _ a b L M P N _ _ _ _ _ _ _ _ _ _ _ _ f g ⟨hf, hfg, hg⟩
  let A := X k a
  let B := Y k b
  let R := S k a b
  change Spec.ShortExact (ExteriorTensorProduct.map f (LinearMap.id : N →ₗ[B] N))
    (ExteriorTensorProduct.map g (LinearMap.id : N →ₗ[B] N))
  let fB := (f.baseChange R).restrictScalars B
  let gB := (g.baseChange R).restrictScalars B
  have hfgB : Function.Exact fB gB := lTensor_exact R hfg hg
  have hgB : Function.Surjective gB := g.baseChange_surjective R hg
  refine ⟨map_left_injective k a b f hf, ?_, ?_⟩
  · rw [coe_map_left, coe_map_left]
    exact rTensor_exact N hfgB hgB
  · rw [coe_map_left]
    exact gB.rTensor_surjective N hgB

/-- The exterior tensor product with a fixed left factor preserves short exact sequences. -/
theorem exactRight : Spec.ExactRight := by
  intro k _ a b M L N P _ _ _ _ _ _ _ _ _ _ _ _ f g ⟨hf, hfg, hg⟩
  let A := X k a
  change Spec.ShortExact (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) f)
    (ExteriorTensorProduct.map (LinearMap.id : M →ₗ[A] M) g)
  refine ⟨map_right_injective k a b f hf, ?_, ?_⟩
  · rw [coe_map_right, coe_map_right]
    exact lTensor_exact _ hfg hg
  · rw [coe_map_right]
    exact g.lTensor_surjective _ hg

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem eq_moduleComparison (k : Type*) [Field k] (a b i j : ℕ)
    (M N : Type*) [AddCommGroup M] [Module (X k a) M]
    [AddCommGroup N] [Module (Y k b) N]
    (e : ModuleLevel k a b (Product k a b M N) i j ≃ₗ[S k a b] ModuleTensor k a b M N i j)
    (he : ∀ m n, e (Submodule.Quotient.mk (((1 : S k a b) ⊗ₜ[X k a] m) ⊗ₜ[Y k b] n)) =
      (xSubmodule k a M i).mkQ m ⊗ₜ[k] (ySubmodule k b N j).mkQ n) :
    e = moduleComparison k a b M N i j := by
  refine LinearEquiv.ext fun t => ?_
  induction t using Submodule.Quotient.induction_on with
  | _ z =>
    induction z using TensorProduct.inductionOn with
    | tmul z n =>
      induction z using TensorProduct.inductionOn with
      | tmul r m =>
        have hr : ((r ⊗ₜ[X k a] m) ⊗ₜ[Y k b] n : Product k a b M N) =
            r • (((1 : S k a b) ⊗ₜ[X k a] m) ⊗ₜ[Y k b] n) := by
          rw [ExteriorTensorProduct.smul_tmul, mul_one]
        rw [hr, Submodule.Quotient.mk_smul, map_smul, map_smul, he, moduleComparison_pair]
      | add z z' hz hz' =>
        simp only [TensorProduct.add_tmul, Submodule.Quotient.mk_add, map_add, hz, hz']
    | add z z' hz hz' =>
      simp only [Submodule.Quotient.mk_add, map_add, hz, hz']

/-- The two-index comparison intertwines the maps induced by either module. -/
theorem comparisonNaturality : Spec.ComparisonNaturality := by
  intro k _ a b i j h M N M' N' _ _ _ _ _ _ _ _
  dsimp only
  intro e e' he he' f g t
  rw [eq_moduleComparison k a b i j M N e he, eq_moduleComparison k a b i j M' N' e' he']
  exact moduleComparison_natural k a b M N f g i j t

/-- The completed exterior tensor product is a natural finite module, exact
in both variables and canonically identified with the inverse limit of truncations. -/
theorem constructionAndSeparateExactness : Spec.ConstructionAndSeparateExactness :=
  ⟨@ExteriorTensorProduct.finite, @ExteriorTensorProduct.map_id,
    @ExteriorTensorProduct.map_comp, @ExteriorTensorProduct.map_add_left,
    @ExteriorTensorProduct.map_add_right, ringComparison, exteriorComparison,
    comparisonNaturality, exactLeft, exactRight⟩

end

end CommutativeAlgebraNotes.Intersection.ExteriorTensorExactness
