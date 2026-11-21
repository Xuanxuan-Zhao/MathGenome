import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Tensors
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Covectors
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleOperations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

namespace SmoothManifolds.Tensors
open ModelData AtlasData MapData TangentData DifferentialData TensorData
open scoped TensorProduct
universe u v w z t q

section Algebra
variable {V : Type u} {W : Type v} {Z : Type w}
  [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
  [AddCommMonoid Z] [Module ℝ Z]

/-- The full tensor space is determined by evaluations on all argument tuples. -/
theorem evaluate_bijective [Module.Finite ℝ V] (r s : ℕ) :
    Function.Bijective (evaluate V r s) := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℝ
  letI : ∀ i : Fin r ⊕ Fin s, AddCommGroup (Argument V r s i) :=
    fun i => Module.addCommMonoidToAddCommGroup ℝ
  letI : ∀ i : Fin r ⊕ Fin s, Module.Finite ℝ (Argument V r s i) := fun i =>
    match i with
    | .inl _ => inferInstance
    | .inr _ => inferInstance
  letI : ∀ i : Fin r ⊕ Fin s, Module.Free ℝ (Argument V r s i) := fun i =>
    match i with
    | .inl _ => inferInstance
    | .inr _ => inferInstance
  let e : (i : Fin r ⊕ Fin s) → Factor V r s i ≃ₗ[ℝ]
      Module.Dual ℝ (Argument V r s i) :=
    fun i => by
      cases i with
      | inl _ => exact Module.evalEquiv ℝ V
      | inr _ => exact LinearEquiv.refl ℝ _
  let E := (PiTensorProduct.tmulEquivDep ℝ (Factor V r s)).trans
    ((PiTensorProduct.congr e).trans
      ((PiTensorProduct.dualDistribEquiv (R := ℝ) (M := Argument V r s)).trans PiTensorProduct.lift.symm))
  have hefac : (fun i => (e i).toLinearMap) = factorEvaluation V r s := by
    funext i
    cases i <;> rfl
  have he : E.toLinearMap = evaluate V r s := by
    unfold evaluate
    rw [← hefac]
    rfl
  exact he ▸ E.bijective

@[simp] theorem evaluate_pure (r s : ℕ) (v : Fin r → V)
    (lam : Fin s → Module.Dual ℝ V) (α : Fin r → Module.Dual ℝ V) (w : Fin s → V) :
    evaluate V r s (pure v lam) (Sum.rec α w) =
      (∏ i, α i (v i)) * ∏ j, lam j (w j) := by
  change PiTensorProduct.dualDistrib
    (PiTensorProduct.map (factorEvaluation V r s)
      (PiTensorProduct.tmulEquivDep ℝ (Factor V r s)
        ((PiTensorProduct.tprod ℝ v) ⊗ₜ[ℝ] (PiTensorProduct.tprod ℝ lam))))
    (PiTensorProduct.tprod ℝ (Sum.rec α w)) = _
  rw [PiTensorProduct.tmulEquivDep_apply, PiTensorProduct.map_tprod,
    PiTensorProduct.dualDistrib_apply, Fintype.prod_sum_type]
  rfl

@[simp] theorem covariantTransport_pure (s : ℕ) (L : V →ₗ[ℝ] W)
    (lam : Fin s → Module.Dual ℝ W) :
    covariantTransport s L (PiTensorProduct.tprod ℝ lam) =
      PiTensorProduct.tprod ℝ (fun i => (lam i).comp L) := by
  simp only [covariantTransport, PiTensorProduct.map_tprod]; rfl

@[simp] theorem covariantTransport_id (s : ℕ) :
    covariantTransport s (LinearMap.id : V →ₗ[ℝ] V) = LinearMap.id := by
  simp [covariantTransport]

theorem covariantTransport_comp (s : ℕ) (L : V →ₗ[ℝ] W) (K : W →ₗ[ℝ] Z) :
    covariantTransport s (K.comp L) =
      (covariantTransport s L).comp (covariantTransport s K) := by
  simp only [covariantTransport, LinearMap.dualMap_comp_dualMap, ← PiTensorProduct.map_comp]

@[simp] theorem mixedTransport_pure (r s : ℕ) (e : V ≃ₗ[ℝ] W)
    (v : Fin r → W) (lam : Fin s → Module.Dual ℝ W) :
    mixedTransport r s e (pure v lam) =
      pure (fun i => e.symm (v i)) (fun j => (lam j).comp e.toLinearMap) := by
  simp only [mixedTransport, TensorData.pure, TensorProduct.map_tmul, PiTensorProduct.map_tprod]; rfl

@[simp] theorem mixedTransport_id (r s : ℕ) :
    mixedTransport r s (LinearEquiv.refl ℝ V) = LinearMap.id := by
  simp [mixedTransport]

theorem mixedTransport_comp (r s : ℕ) (e : V ≃ₗ[ℝ] W) (d : W ≃ₗ[ℝ] Z) :
    mixedTransport r s (e.trans d) =
      (mixedTransport r s e).comp (mixedTransport r s d) := by
  simp only [mixedTransport, ← TensorProduct.map_comp, ← PiTensorProduct.map_comp]
  rfl

@[simp] theorem covariantEvaluate_pure (s : ℕ)
    (lam : Fin s → Module.Dual ℝ V) (v : Fin s → V) :
    covariantEvaluate V s (PiTensorProduct.tprod ℝ lam) v = ∏ i, lam i (v i) := by
  change PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℝ lam)
    (PiTensorProduct.tprod ℝ v) = _
  exact PiTensorProduct.dualDistrib_apply lam v

theorem covariantTransport_evaluate (s : ℕ) (L : V →ₗ[ℝ] W)
    (A : Power (Module.Dual ℝ W) s) (v : Fin s → V) :
    covariantEvaluate V s (covariantTransport s L A) v =
      covariantEvaluate W s A (fun i => L (v i)) := by
  induction A using PiTensorProduct.induction_on with
  | smul_tprod c lam =>
    simp only [map_smul, covariantTransport_pure,
      MultilinearMap.smul_apply, covariantEvaluate_pure, LinearMap.comp_apply]
  | add x y hx hy =>
    simp only [map_add, MultilinearMap.add_apply, hx, hy]

/-- The reindexing action is a representation, with the usual permutation
multiplication. This fixes the composition convention used in the averages. -/
noncomputable def permutationRepresentation (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) : Equiv.Perm (Fin k) →* Module.End ℝ (Power V k) where
  toFun := permute V k
  map_one' := by
    change (PiTensorProduct.reindex ℝ (fun _ : Fin k => V) (Equiv.refl _)).toLinearMap = LinearMap.id
    rw [PiTensorProduct.reindex_refl]
    rfl
  map_mul' σ τ := by
    ext v
    simp [permute, PiTensorProduct.reindex_tprod, Function.comp_def, Equiv.piCongrLeft']
    congr 1

theorem signScalar_self (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    signScalar k σ * signScalar k σ = 1 := by
  have hi : signScalar k σ⁻¹ = signScalar k σ := by
    simp only [signScalar, MonoidHom.comp_apply, Equiv.Perm.sign_inv]
  nth_rw 1 [← hi]
  rw [← map_mul, inv_mul_cancel, map_one]

noncomputable def signedPermutationRepresentation (V : Type u)
    [AddCommMonoid V] [Module ℝ V] (k : ℕ) :
    Equiv.Perm (Fin k) →* Module.End ℝ (Power V k) where
  toFun σ := signScalar k σ • permutationRepresentation V k σ
  map_one' := by simp
  map_mul' σ τ := by
    ext x
    simp [map_mul, smul_smul, Module.End.mul_apply, mul_comm]

private noncomputable def average {G : Type v} [Group G] [Fintype G]
    {X : Type u} [AddCommMonoid X] [Module ℝ X]
    (ρ : G →* Module.End ℝ X) : X →ₗ[ℝ] X :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g : G, ρ g

private theorem average_invariant {G : Type v} [Group G] [Fintype G]
    {X : Type u} [AddCommMonoid X] [Module ℝ X]
    (ρ : G →* Module.End ℝ X) (g : G) (x : X) :
    ρ g (average ρ x) = average ρ x := by
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  simp_rw [← Module.End.mul_apply, ← map_mul]
  exact Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun i => ρ i x)

private theorem average_fixed {G : Type v} [Group G] [Fintype G]
    {X : Type u} [AddCommMonoid X] [Module ℝ X]
    (ρ : G →* Module.End ℝ X) (x : X) (hx : ∀ g, ρ g x = x) :
    average ρ x = x := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply, hx, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

private theorem average_symmetrize (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) : average (permutationRepresentation V k) = symmetrize V k := by
  simp only [average, symmetrize, Fintype.card_perm, Fintype.card_fin]
  rfl

private theorem average_alternate (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) : average (signedPermutationRepresentation V k) = alternate V k := by
  simp only [average, alternate, Fintype.card_perm, Fintype.card_fin]
  rfl

private theorem symmetrize_invariant (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) (x : Power V k) (σ : Equiv.Perm (Fin k)) :
    permute V k σ (symmetrize V k x) = symmetrize V k x := by
  rw [← average_symmetrize]
  exact average_invariant (permutationRepresentation V k) σ x

private theorem alternate_invariant (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) (x : Power V k) (σ : Equiv.Perm (Fin k)) :
    permute V k σ (alternate V k x) = signScalar k σ • alternate V k x := by
  have h := average_invariant (signedPermutationRepresentation V k) σ x
  rw [average_alternate] at h
  have hh := congrArg (fun y => signScalar k σ • y) h
  change signScalar k σ • (signScalar k σ •
    permute V k σ (alternate V k x)) = signScalar k σ • alternate V k x at hh
  simpa only [smul_smul, signScalar_self, one_smul] using hh

private theorem symmetrize_fixed (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) (x : Power V k) (hx : ∀ σ, permute V k σ x = x) :
    symmetrize V k x = x := by
  rw [← average_symmetrize]
  exact average_fixed (permutationRepresentation V k) x hx

private theorem alternate_fixed (V : Type u) [AddCommMonoid V] [Module ℝ V]
    (k : ℕ) (x : Power V k) (hx : ∀ σ, permute V k σ x = signScalar k σ • x) :
    alternate V k x = x := by
  rw [← average_alternate]
  apply average_fixed
  intro σ
  change signScalar k σ • permute V k σ x = x
  rw [hx, smul_smul, signScalar_self, one_smul]

-- Implementation: inside SmoothManifolds.Tensors, with open TensorData.
@[simp] theorem slotIndex_symm_left {k : ℕ} (p : Fin (k+1)) (i : Fin 1) :
    (slotIndex p).symm (.inl i) = p := by
  simp [slotIndex, optionSlotIndex]

@[simp] theorem slotIndex_symm_right {k : ℕ} (p : Fin (k+1)) (i : Fin k) :
    (slotIndex p).symm (.inr i) = p.succAbove i := by
  simp [slotIndex, optionSlotIndex]

@[simp] theorem splitPowerAt_tprod {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {k : ℕ} (p : Fin (k+1)) (v : Fin (k+1) → V) :
    splitPowerAt V p (PiTensorProduct.tprod ℝ v) =
      (v p) ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ (fun i => v (p.succAbove i)) := by
  simp [splitPowerAt, PiTensorProduct.reindex_tprod]

/-- Contract the specified tangent and cotangent factors, retaining the original
order on the remaining factors. All maps are canonical tensor universal maps. -/

@[simp] theorem contract_pure {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {r s : ℕ} (i : Fin (r+1)) (j : Fin (s+1))
    (v : Fin (r+1) → V) (lam : Fin (s+1) → Module.Dual ℝ V) :
    contract V i j (TensorData.pure v lam) =
      lam j (v i) • TensorData.pure (fun k => v (i.succAbove k)) (fun l => lam (j.succAbove l)) := by
  simp [contract, TensorData.pure]

theorem contract_natural {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    {r s : ℕ} (i : Fin (r+1)) (j : Fin (s+1)) (e : V ≃ₗ[ℝ] W) :
    (contract V i j).comp (mixedTransport (r+1) (s+1) e) =
      (mixedTransport r s e).comp (contract W i j) := by
  ext v lam
  change contract V i j (mixedTransport (r+1) (s+1) e (TensorData.pure v lam)) =
    mixedTransport r s e (contract W i j (TensorData.pure v lam))
  simp only [mixedTransport_pure, contract_pure, map_smul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

@[simp] theorem joinPower_tmul {V : Type u} [AddCommMonoid V] [Module ℝ V]
    (r s : ℕ) (v : Fin r → V) (w : Fin s → V) :
    joinPower V r s ((PiTensorProduct.tprod ℝ v) ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ w) =
      PiTensorProduct.tprod ℝ (Fin.append v w) := by
  simp only [joinPower, LinearEquiv.trans_apply, PiTensorProduct.tmulEquiv_apply,
    PiTensorProduct.reindex_tprod]
  congr 1
  funext i
  refine Fin.addCases (fun l => ?_) (fun k => ?_) i <;> simp

@[simp] theorem tensorMultiply_pure {V : Type u} [AddCommMonoid V] [Module ℝ V]
    (r s r' s' : ℕ) (v : Fin r → V) (lam : Fin s → Module.Dual ℝ V)
    (w : Fin r' → V) (mu : Fin s' → Module.Dual ℝ V) :
    tensorMultiply V r s r' s' (TensorData.pure v lam) (TensorData.pure w mu) =
      TensorData.pure (Fin.append v w) (Fin.append lam mu) := by
  simp [tensorMultiply, tensorProductMap, TensorData.pure]

theorem tensorProductMap_natural {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    (r s r' s' : ℕ) (e : V ≃ₗ[ℝ] W) :
    (mixedTransport (r+r') (s+s') e).comp (tensorProductMap W r s r' s') =
      (tensorProductMap V r s r' s').comp
        (TensorProduct.map (mixedTransport r s e) (mixedTransport r' s' e)) := by
  ext v lam w mu
  change mixedTransport (r+r') (s+s') e
      (tensorMultiply W r s r' s' (TensorData.pure v lam) (TensorData.pure w mu)) =
    tensorMultiply V r s r' s' (mixedTransport r s e (TensorData.pure v lam))
      (mixedTransport r' s' e (TensorData.pure w mu))
  simp only [tensorMultiply_pure, mixedTransport_pure]
  congr 1 <;> funext i <;>
    refine Fin.addCases (fun k => ?_) (fun l => ?_) i <;> simp

theorem tensorMultiply_natural {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    (r s r' s' : ℕ) (e : V ≃ₗ[ℝ] W) (A : Fiber W r s) (B : Fiber W r' s') :
    mixedTransport (r+r') (s+s') e (tensorMultiply W r s r' s' A B) =
      tensorMultiply V r s r' s' (mixedTransport r s e A) (mixedTransport r' s' e B) := by
  exact congrArg (fun f => f (A ⊗ₜ[ℝ] B)) (tensorProductMap_natural r s r' s' e)

end Algebra

private theorem fiber_interpretation_proof :
    Specs.SmoothManifolds.Ch05.Tensors.fiber_interpretationType.{u} := by
  intro n a M _ S p r s
  letI := (tangent_dimension S p).1
  exact evaluate_bijective r s

private theorem pure_evaluation_proof :
    Specs.SmoothManifolds.Ch05.Tensors.pure_evaluationType.{u} := by
  intro n a M _ S p r s v lam α w
  exact evaluate_pure r s v lam α w

private theorem covariant_pullback_id_proof :
    Specs.SmoothManifolds.Ch05.Tensors.covariant_pullback_idType.{u} := by
  intro n a M _ S s L hL A
  funext p
  have h := (differential_exists S S id (by
    exact manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1) p).unique
      (hL p) (differential_id S p)
  simp [covariantPullback, h]

private theorem covariant_pullback_comp_proof :
    Specs.SmoothManifolds.Ch05.Tensors.covariant_pullback_compType.{u} := by
  intro n m k a b c M P Q _ _ _ S T U f g hf hg s L K H hL hK hH A
  funext q
  have hfg : IsSmoothMap U S (f ∘ g) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ T.smoothStructure.property.1.1 g f hg hf
  have heq := (differential_exists U S (f ∘ g) hfg q).unique
    (hH q) (differential_comp U T S g f hg hf q (K q) (L (g q)) (hK q) (hL (g q)))
  simp only [covariantPullback, heq, covariantTransport_comp, LinearMap.comp_apply]
  rfl

private theorem mixed_pullback_id_proof :
    Specs.SmoothManifolds.Ch05.Tensors.mixed_pullback_idType.{u} := by
  intro n a M _ S r s e he A
  funext p
  have h := (differential_exists S S id (by
    exact manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1) p).unique
      (he p) (differential_id S p)
  have heq : e p = LinearEquiv.refl ℝ _ := LinearEquiv.toLinearMap_injective h
  simp [mixedPullback, heq]

private theorem mixed_pullback_comp_proof :
    Specs.SmoothManifolds.Ch05.Tensors.mixed_pullback_compType.{u} := by
  intro n m k a b c M P Q _ _ _ S T U f g hf hg r s e d h he hd hh A
  funext q
  have hfg : IsSmoothMap U S (f ∘ g) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ T.smoothStructure.property.1.1 g f hg hf
  have hlinear := (differential_exists U S (f ∘ g) hfg q).unique
    (hh q) (differential_comp U T S g f hg hf q (d q).toLinearMap
      (e (g q)).toLinearMap (hd q) (he (g q)))
  have heq : h q = (d q).trans (e (g q)) := LinearEquiv.toLinearMap_injective hlinear
  simp only [mixedPullback, heq, mixedTransport_comp, LinearMap.comp_apply]
  rfl

private theorem covariant_pullback_apply_proof :
    Specs.SmoothManifolds.Ch05.Tensors.covariant_pullback_applyType.{u} := by
  intro n m a b M P _ _ S T f L s A p v
  exact covariantTransport_evaluate s (L p) (A (f p)) v

private theorem averaging_projections_proof :
    Specs.SmoothManifolds.Ch05.Tensors.averaging_projectionsType.{u} := by
  intro V _ _ k
  refine ⟨?_, symmetrize_fixed V k, alternate_fixed V k⟩
  intro x
  exact ⟨symmetrize_invariant V k x, alternate_invariant V k x,
    symmetrize_fixed V k _ (symmetrize_invariant V k x),
    alternate_fixed V k _ (alternate_invariant V k x)⟩



/-! Closed algebraic consequences, using the accepted differential proofs. -/

theorem fiber_interpretation :
    Specs.SmoothManifolds.Ch05.Tensors.fiber_interpretationType.{u} :=
  fiber_interpretation_proof

theorem pure_evaluation :
    Specs.SmoothManifolds.Ch05.Tensors.pure_evaluationType.{u} :=
  pure_evaluation_proof

theorem covariant_pullback_id :
    Specs.SmoothManifolds.Ch05.Tensors.covariant_pullback_idType.{u} :=
  covariant_pullback_id_proof

theorem covariant_pullback_comp :
    Specs.SmoothManifolds.Ch05.Tensors.covariant_pullback_compType.{u} :=
  covariant_pullback_comp_proof

theorem covariant_pullback_apply :
    Specs.SmoothManifolds.Ch05.Tensors.covariant_pullback_applyType.{u} :=
  covariant_pullback_apply_proof

theorem mixed_pullback_id :
    Specs.SmoothManifolds.Ch05.Tensors.mixed_pullback_idType.{u} :=
  mixed_pullback_id_proof

theorem mixed_pullback_comp :
    Specs.SmoothManifolds.Ch05.Tensors.mixed_pullback_compType.{u} :=
  mixed_pullback_comp_proof

theorem averaging_projections :
    Specs.SmoothManifolds.Ch05.Tensors.averaging_projectionsType.{u} :=
  averaging_projections_proof

section Bundles
open BundleData BundleOperationsData FrameData Set Filter
open scoped Topology

@[simp] theorem powerCoordinates_tprod {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (k : ℕ)
    (v : Fin k → V) (j : Fin k → Fin d) :
    powerCoordinates e k (PiTensorProduct.tprod ℝ v) (powerIndex d k j) =
      ∏ l, e (v l) (j l) := by
  simp [powerCoordinates, powerBasis, Module.Basis.equivFun_apply,
    Module.Basis.repr_reindex_apply]

@[simp] theorem powerCoordinates_symm_single {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (k : ℕ) (j : Fin (d ^ k)) :
    (powerCoordinates e k).symm (Pi.single j 1) =
      PiTensorProduct.tprod ℝ (fun l => e.symm (Pi.single ((powerIndex d k).symm j l) 1)) := by
  classical
  change (powerBasis e k).equivFun.symm (Pi.single j 1) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp [powerBasis, Module.Basis.reindex_apply, Basis.piTensorProduct_apply,
    Pi.single_apply, ite_smul]

/-- Finite products of scalar coefficient functions are smooth. -/
theorem vectorSmoothAt_prod {d : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    {A : Set (ModelChart d a X)} {κ : Type v} [Fintype κ]
    {f : X → κ → ℝ} {p : X} (hf : ∀ j, VectorSmoothAt A (fun x => f x j) p) :
    VectorSmoothAt A (fun x => ∏ j, f x j) p :=
  (FrameData.VectorSmoothAt.pi hf).postcomp
    (contDiff_prod (fun j _ =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).contDiff))

/-- The induced transition matrix has entries equal to products of the
original transition entries. This proves smoothness at faces by ambient extension. -/
noncomputable def powerPresentation {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (C : BundleOperations.CoordinatePresentation S d ι E) (k : ℕ) :
    BundleOperations.CoordinatePresentation S (d ^ k) ι (fun p => Power (E p) k) where
  domain := C.domain
  isOpen_domain := C.isOpen_domain
  covers := C.covers
  coord i p hp := powerCoordinates (C.coord i p hp) k
  transition i j p := QuotientBundles.columnOperator (fun l q => ∏ h : Fin k,
    C.transition i j p (Pi.single ((powerIndex d k).symm l h) 1)
      ((powerIndex d k).symm q h))
  transition_eq i j p hi hj v := by
    have heq : (QuotientBundles.columnOperator (fun l q => ∏ h : Fin k,
        C.transition i j p (Pi.single ((powerIndex d k).symm l h) 1)
          ((powerIndex d k).symm q h))).toLinearMap =
        ((powerCoordinates (C.coord i p hi) k).symm.trans
          (powerCoordinates (C.coord j p hj) k)).toLinearMap := by
      apply (Pi.basisFun ℝ (Fin (d ^ k))).ext
      intro l
      rw [Pi.basisFun_apply]
      change QuotientBundles.columnOperator _ (Pi.single l 1) = _
      rw [QuotientBundles.columnOperator_single]
      funext q
      change _ = powerCoordinates (C.coord j p hj) k
        ((powerCoordinates (C.coord i p hi) k).symm (Pi.single l 1)) q
      conv_rhs => rw [← (powerIndex d k).apply_symm_apply q]
      rw [powerCoordinates_symm_single, powerCoordinates_tprod]
      apply Finset.prod_congr rfl
      intro h _
      rw [C.transition_eq]
    exact LinearMap.congr_fun heq v
  smooth i j p hi hj := by
    apply BundleOperations.columnOperator_smooth
    intro l
    apply FrameData.VectorSmoothAt.pi
    intro q
    apply vectorSmoothAt_prod
    intro h
    exact ((C.smooth i j p hi hj).clm_apply
      (FrameData.VectorSmoothAt.const _ _ p)).postcomp (ContinuousLinearMap.proj _).contDiff

theorem exists_powerBundle : Specs.SmoothManifolds.Ch05.Tensors.exists_powerBundleType.{u} := by
  intro n d a M _ S ι E _ _ _ B k
  obtain ⟨V, hbase, hcoord⟩ := (powerPresentation (BundleOperations.bundlePresentation B) k).exists_bundle
  letI := V.topology
  refine ⟨{ space := V, baseSet := hbase, coordinates := ?_ }⟩
  intro i p hp v j
  rw [hcoord i p hp]
  exact powerCoordinates_tprod _ _ v j

theorem exists_tensorBundle : Specs.SmoothManifolds.Ch05.Tensors.exists_tensorBundleType.{u} := by
  intro n a M _ S r s
  obtain ⟨C⟩ := BundleOperations.exists_cotangent S
  letI := C.realization.space.topology
  letI := C.dual.space.topology
  obtain ⟨U⟩ := exists_powerBundle C.realization.space.bundle r
  obtain ⟨D⟩ := exists_powerBundle C.dual.space.bundle s
  letI := U.space.topology
  letI := D.space.topology
  obtain ⟨B⟩ := BundleOperations.exists_tensor U.space.bundle D.space.bundle
  exact ⟨{ cotangent := C, upper := U, lower := D, mixed := B }⟩

/-- The canonical tensor product sends any pair of smooth lifts with the same
base map to a smooth lift, also when the base has boundary. -/
theorem tensor_lift_smooth
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F)
    (P : BundleOperationsData.TensorBundle B D)
    {m : ℕ} {b : ModelKind} {X : Type q} [TopologicalSpace X]
    (U : SmoothManifold m b X) (f : X → M)
    (v : (x : X) → E (f x)) (w : (x : X) → F (f x))
    (hv : IsSmoothMap U B.totalManifold (fun x => ⟨f x, v x⟩))
    (hw : IsSmoothMap U D.totalManifold (fun x => ⟨f x, w x⟩)) :
    letI := P.space.topology
    IsSmoothMap U P.space.bundle.totalManifold
      (fun x => (⟨f x, (v x) ⊗ₜ[ℝ] (w x)⟩ :
        Bundle.TotalSpace (Euclidean (r*s)) (fun p => E p ⊗[ℝ] F p))) := by
  letI := P.space.topology
  intro x
  obtain ⟨i, hi⟩ := B.covers (f x)
  obtain ⟨j, hj⟩ := D.covers (f x)
  have hf : ManifoldSmoothAt U.smoothStructure.val S.smoothStructure.val f x :=
    manifoldContDiffAt_comp B.totalManifold.smoothStructure.property.1.1
      (hv x) (B.projection_smooth ⟨f x, v x⟩)
  have hvi := FrameData.VectorSmoothAt.comp (g := fun y => (⟨f y, v y⟩ : Bundle.TotalSpace (Euclidean r) E)) (x := x) B.totalManifold.smoothStructure.property.1.1
    (Frames.trivializationCoordinates_smoothAt B i ⟨f x, v x⟩ hi) (hv x)
  have hwj := FrameData.VectorSmoothAt.comp (g := fun y => (⟨f y, w y⟩ : Bundle.TotalSpace (Euclidean s) F)) (x := x) D.totalManifold.smoothStructure.property.1.1
    (Frames.trivializationCoordinates_smoothAt D j ⟨f x, w x⟩ hj) (hw x)
  have hp : f x ∈ P.space.bundle.baseSet (i,j) := by rw [P.baseSet]; exact ⟨hi, hj⟩
  refine Frames.smoothAt_from_trivialization P.space.bundle
    U.smoothStructure.property.1 (i,j) hp hf
    (v := fun x l => ((B.trivialization i) ⟨f x, v x⟩).2 (finProdFinEquiv.symm l).1 *
      ((D.trivialization j) ⟨f x, w x⟩).2 (finProdFinEquiv.symm l).2)
    ?_ (fun _ => rfl) ?_
  · apply FrameData.VectorSmoothAt.pi
    intro l
    exact ((hvi.postcomp (ContinuousLinearMap.proj _).contDiff).prod
      (hwj.postcomp (ContinuousLinearMap.proj _).contDiff)).postcomp
      (contDiff_fst.mul contDiff_snd)
  · filter_upwards [hf.1.preimage_mem_nhds
      (((B.trivialization_baseSet i).symm ▸ (B.trivialization i).open_baseSet).mem_nhds hi),
      hf.1.preimage_mem_nhds
      (((D.trivialization_baseSet j).symm ▸ (D.trivialization j).open_baseSet).mem_nhds hj)] with y hyB hyD
    ext l
    conv_lhs => rw [← finProdFinEquiv.apply_symm_apply l]
    exact P.coordinates (i,j) (f y) (by rw [P.baseSet]; exact ⟨hyB, hyD⟩)
      (v y) (w y) _ _


end Bundles

section PowerOperations
open BundleData BundleOperationsData FrameData Set Filter
open scoped Topology

noncomputable def permutationCoordinates (d k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Euclidean (d ^ k) →ₗ[ℝ] Euclidean (d ^ k) where
  toFun x j := x (powerIndex d k (fun l => (powerIndex d k).symm j (σ l)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem powerCoordinates_permute {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (x : Power V k) :
    powerCoordinates e k (permute V k σ x) =
      permutationCoordinates d k σ (powerCoordinates e k x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul]
    congr 1
    ext j
    obtain ⟨j, rfl⟩ := (powerIndex d k).surjective j
    simp only [permute, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod,
      powerCoordinates_tprod, permutationCoordinates, LinearMap.coe_mk, AddHom.coe_mk,
      Equiv.symm_apply_apply]
    exact (Equiv.prod_comp σ (fun l => e (v (σ.symm l)) (j l))).symm.trans
      (Finset.prod_congr rfl (fun l _ => by simp))
  | add x y hx hy => simp only [map_add, hx, hy]

theorem powerBundle_coordinates {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    (B : SmoothVectorBundle S d ι E) {k : ℕ} (P : PowerBundle B k)
    (i : ι) (p : M) (hp : p ∈ B.baseSet i) (x : Power (E p) k) :
    letI := P.space.topology
    ((P.space.bundle.trivialization i) ⟨p, x⟩).2 =
      powerCoordinates (B.fiberCoordinates i p hp) k x := by
  letI := P.space.topology
  have hpP : p ∈ P.space.bundle.baseSet i := by rw [P.baseSet]; exact hp
  change P.space.bundle.fiberCoordinates i p hpP x = _
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul]
    congr 1
    ext j
    obtain ⟨j, rfl⟩ := (powerIndex d k).surjective j
    rw [powerCoordinates_tprod]
    exact P.coordinates i p hp v j
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A constant linear coordinate formula defines a smooth bundle map. -/
theorem powerBundle_smooth_of_coordinates {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    (B : SmoothVectorBundle S d ι E) {k : ℕ} (P : PowerBundle B k)
    (A : (p : M) → Power (E p) k →ₗ[ℝ] Power (E p) k)
    (C : Euclidean (d ^ k) →L[ℝ] Euclidean (d ^ k))
    (hC : ∀ i p (hp : p ∈ B.baseSet i) x,
      powerCoordinates (B.fiberCoordinates i p hp) k (A p x) =
        C (powerCoordinates (B.fiberCoordinates i p hp) k x)) :
    letI := P.space.topology
    IsSmoothMap P.space.bundle.totalManifold P.space.bundle.totalManifold
      (fun q => (⟨q.proj, A q.proj q.snd⟩ :
        Bundle.TotalSpace (Euclidean (d ^ k)) (fun p => Power (E p) k))) := by
  letI := P.space.topology
  intro q
  obtain ⟨i, hi⟩ := B.covers q.proj
  have hiP : q.proj ∈ P.space.bundle.baseSet i := by rw [P.baseSet]; exact hi
  have hv := (Frames.trivializationCoordinates_smoothAt P.space.bundle i q hiP).postcomp C.contDiff
  apply Frames.smoothAt_from_trivialization P.space.bundle
    P.space.bundle.totalManifold.smoothStructure.property.1
    (f := fun y => ⟨y.proj, A y.proj y.snd⟩) i hiP
    (P.space.bundle.projection_smooth q) hv (fun _ => rfl)
  have hopen : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸
    (B.trivialization i).open_baseSet
  filter_upwards [(P.space.bundle.projection_smooth q).1.preimage_mem_nhds
    (hopen.mem_nhds hi)] with y hy
  rw [powerBundle_coordinates B P i y.proj hy, hC,
    powerBundle_coordinates B P i y.proj hy]

theorem power_permute_smooth {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    (B : SmoothVectorBundle S d ι E) {k : ℕ} (P : PowerBundle B k)
    (σ : Equiv.Perm (Fin k)) :
    letI := P.space.topology
    IsSmoothMap P.space.bundle.totalManifold P.space.bundle.totalManifold
      (fun q => (⟨q.proj, permute (E q.proj) k σ q.snd⟩ :
        Bundle.TotalSpace (Euclidean (d ^ k)) (fun p => Power (E p) k))) := by
  apply powerBundle_smooth_of_coordinates B P (fun p => permute (E p) k σ)
    (permutationCoordinates d k σ).toContinuousLinearMap
  intro i p hp x
  exact powerCoordinates_permute _ _ _ _

noncomputable def symmetrizeCoordinates (d k : ℕ) :
    Euclidean (d ^ k) →ₗ[ℝ] Euclidean (d ^ k) :=
  (k.factorial : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), permutationCoordinates d k σ

noncomputable def alternateCoordinates (d k : ℕ) :
    Euclidean (d ^ k) →ₗ[ℝ] Euclidean (d ^ k) :=
  (k.factorial : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), signScalar k σ • permutationCoordinates d k σ

theorem powerCoordinates_symmetrize {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (k : ℕ) (x : Power V k) :
    powerCoordinates e k (symmetrize V k x) =
      symmetrizeCoordinates d k (powerCoordinates e k x) := by
  simp only [symmetrize, symmetrizeCoordinates, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, powerCoordinates_permute]

theorem powerCoordinates_alternate {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (k : ℕ) (x : Power V k) :
    powerCoordinates e k (alternate V k x) =
      alternateCoordinates d k (powerCoordinates e k x) := by
  simp only [alternate, alternateCoordinates, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, powerCoordinates_permute]

theorem power_symmetrize_smooth {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    (B : SmoothVectorBundle S d ι E) {k : ℕ} (P : PowerBundle B k) :
    letI := P.space.topology
    IsSmoothMap P.space.bundle.totalManifold P.space.bundle.totalManifold
      (fun q => (⟨q.proj, symmetrize (E q.proj) k q.snd⟩ :
        Bundle.TotalSpace (Euclidean (d ^ k)) (fun p => Power (E p) k))) := by
  apply powerBundle_smooth_of_coordinates B P (fun p => symmetrize (E p) k)
    (symmetrizeCoordinates d k).toContinuousLinearMap
  intro i p hp x
  exact powerCoordinates_symmetrize _ _ _

theorem power_alternate_smooth {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    (B : SmoothVectorBundle S d ι E) {k : ℕ} (P : PowerBundle B k) :
    letI := P.space.topology
    IsSmoothMap P.space.bundle.totalManifold P.space.bundle.totalManifold
      (fun q => (⟨q.proj, alternate (E q.proj) k q.snd⟩ :
        Bundle.TotalSpace (Euclidean (d ^ k)) (fun p => Power (E p) k))) := by
  apply powerBundle_smooth_of_coordinates B P (fun p => alternate (E p) k)
    (alternateCoordinates d k).toContinuousLinearMap
  intro i p hp x
  exact powerCoordinates_alternate _ _ _

end PowerOperations

section LocalDiffeomorphisms
open FiniteRegularityData Set Filter
open scoped Topology

private theorem chartDerivative_congr {n m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (e : ModelChart n a M) (d : ModelChart m b N) {f g : M → N} {p : M}
    (hp : p ∈ e.source) (hf : ChartContDiffAt (⊤ : ℕ∞) e d f p)
    (hfg : f =ᶠ[𝓝 p] g) : chartDerivative e d f p = chartDerivative e d g p := by
  have h := FiniteRegularity.chartDerivative_exists (⊤ : ℕ∞) (by simp) e d f p hf
  rcases h with ⟨F, hF, heF⟩
  exact (FiniteRegularity.coordinateDerivative_eq e _ p hp _
    ⟨F, hF, heF.trans (hfg.fun_comp (fun x => (d x).val))⟩).symm

theorem differential_bijective_of_localDiffeomorphism
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (hf : IsLocalDiffeomorphism S T f) (p : M) :
    Function.Bijective (SmoothManifolds.differential S T f hf.1 p) := by
  obtain ⟨g, hg, hgp, hgf, hfg⟩ := hf.2 p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  have hfcd := (hf.1 p).2 e he d hd hp hfp
  have hgcd := hg.2 d hd e he hfp (by simpa only [hgp] using hp)
  have hleft := FiniteRegularity.chartDerivative_comp (⊤ : ℕ∞) (by simp)
    e d e f g p hp (hf.1 p).1 hfcd hgcd
  have hright := FiniteRegularity.chartDerivative_comp (⊤ : ℕ∞) (by simp)
    d e d g f (f p) hfp hg.1 hgcd
    (by simpa only [hgp] using hfcd)
  have hgfSmooth := SmoothManifolds.manifoldContDiffAt_comp
    T.smoothStructure.property.1.1 (hf.1 p) hg
  have hfgSmooth := SmoothManifolds.manifoldContDiffAt_comp
    S.smoothStructure.property.1.1 hg (hf.1 (g (f p)))
  have hgfcd : ChartContDiffAt (⊤ : ℕ∞) e e (g ∘ f) p :=
    hgfSmooth.2 e he e he hp (by simpa only [Function.comp_apply, hgp] using hp)
  have hfgcd : ChartContDiffAt (⊤ : ℕ∞) d d (f ∘ g) (f p) :=
    hfgSmooth.2 d hd d hd hfp (by simpa only [Function.comp_apply, hgp] using hfp)
  rw [chartDerivative_congr e e hp hgfcd hgf, FiniteRegularity.chartDerivative_id e p hp] at hleft
  rw [chartDerivative_congr d d hfp hfgcd hfg, FiniteRegularity.chartDerivative_id d (f p) hfp,
    hgp] at hright
  have hJ : Function.Bijective (chartDerivative e d f p) := by
    constructor
    · intro x y hxy
      have hx := congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L x) hleft
      have hy := congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L y) hleft
      change x = chartDerivative d e g (f p) (chartDerivative e d f p x) at hx
      change y = chartDerivative d e g (f p) (chartDerivative e d f p y) at hy
      exact hx.trans ((congrArg (chartDerivative d e g (f p)) hxy).trans hy.symm)
    · intro y
      refine ⟨chartDerivative d e g (f p) y, ?_⟩
      exact (congrArg (fun L : Euclidean m →L[ℝ] Euclidean m => L y) hright).symm
  have hinv := MapClasses.smooth_tangent_invariants S T f hf.1 p
    (SmoothManifolds.differential S T f hf.1 p)
    (SmoothManifolds.differential_spec S T f hf.1 p)
  have hf1 := SmoothManifolds.manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf.1
  have hc := MapClasses.chart_invariants S T f hf1 p e d he hd hp hfp
  exact ⟨hinv.2.1.mp (hc.2.1.mpr hJ.1), hinv.2.2.mp (hc.2.2.mpr hJ.2)⟩

noncomputable def localDiffeomorphismDifferential
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (hf : IsLocalDiffeomorphism S T f) (p : M) :
    TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p) :=
  LinearEquiv.ofBijective (SmoothManifolds.differential S T f hf.1 p)
    (differential_bijective_of_localDiffeomorphism S T f hf p)

theorem localDiffeomorphismDifferential_spec
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (hf : IsLocalDiffeomorphism S T f) (p : M) :
    IsDifferential S T f p (localDiffeomorphismDifferential S T f hf p).toLinearMap :=
  SmoothManifolds.differential_spec S T f hf.1 p
open FrameData

theorem chartCoordinate_smoothAt {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    VectorSmoothAt S.smoothStructure.val (fun x => (e x).val) p := by
  refine ⟨continuous_subtype_val.continuousAt.comp (e.continuousAt hp), ?_⟩
  intro c hc hcp
  exact SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 c hc e he) hcp hp

theorem chartDerivative_smoothAt
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (hf : IsSmoothMap S T f) (e : ModelChart n a M) (d : ModelChart m b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hfp : f p ∈ d.source) :
    VectorSmoothAt S.smoothStructure.val (fun x => chartDerivative e d f x) p := by
  obtain ⟨U, hU, hpU, F, hF, hFeq⟩ := (hf p).2 e he d hd hp hfp
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hFeq
  have hsmooth := (chartCoordinate_smoothAt S e he p hp).postcompOn hU hpU
    (hF.fderiv_of_isOpen hU (by simp))
  apply hsmooth.congr
  filter_upwards [e.open_source.mem_nhds hp, hV.mem_nhds hpV,
    (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).preimage_mem_nhds
      (hU.mem_nhds hpU)] with x hxe hxV hxU
  exact (FiniteRegularity.coordinateDerivative_eq e _ x hxe _
    ⟨F, ((hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).hasFDerivAt,
      Filter.mem_of_superset (hV.mem_nhds hxV) hVsub⟩).symm


theorem chartDerivative_isInvertible
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (hf : IsLocalDiffeomorphism S T f) (e : ModelChart n a M) (d : ModelChart m b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hfp : f p ∈ d.source) :
    (chartDerivative e d f p).IsInvertible := by
  have hdf := differential_bijective_of_localDiffeomorphism S T f hf p
  have hinv := MapClasses.smooth_tangent_invariants S T f hf.1 p
    (SmoothManifolds.differential S T f hf.1 p)
    (SmoothManifolds.differential_spec S T f hf.1 p)
  have hf1 := SmoothManifolds.manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf.1
  have hc := MapClasses.chart_invariants S T f hf1 p e d he hd hp hfp
  have hJ : Function.Bijective (chartDerivative e d f p) :=
    ⟨hc.2.1.mp (hinv.2.1.mpr hdf.1), hc.2.2.mp (hinv.2.2.mpr hdf.2)⟩
  exact ⟨(LinearEquiv.ofBijective (chartDerivative e d f p).toLinearMap hJ).toContinuousLinearEquiv, rfl⟩

theorem inverse_chartDerivative_smoothAt
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (hf : IsLocalDiffeomorphism S T f) (e : ModelChart n a M) (d : ModelChart m b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hfp : f p ∈ d.source) :
    VectorSmoothAt S.smoothStructure.val
      (fun x => ContinuousLinearMap.inverse (chartDerivative e d f x)) p :=
  (chartDerivative_smoothAt S T f hf.1 e d he hd p hp hfp).inverse
    (chartDerivative_isInvertible S T f hf e d he hd p hp hfp)


theorem isLocalDiffeomorphism_id {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) :
    IsLocalDiffeomorphism S S id := by
  have hid := manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1
  exact ⟨hid, fun p => ⟨id, hid p, rfl, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩⟩

theorem isLocalDiffeomorphism_comp
    {n m k : ℕ} {a b c : ModelKind} {M N Q : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (U : SmoothManifold k c Q)
    (f : M → N) (g : N → Q)
    (hf : IsLocalDiffeomorphism S T f) (hg : IsLocalDiffeomorphism T U g) :
    IsLocalDiffeomorphism S U (g ∘ f) := by
  refine ⟨manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ T.smoothStructure.property.1.1
    f g hf.1 hg.1, ?_⟩
  intro p
  obtain ⟨fi, hfi, hfip, hfiL, hfiR⟩ := hf.2 p
  obtain ⟨gi, hgi, hgip, hgiL, hgiR⟩ := hg.2 (f p)
  refine ⟨fi ∘ gi, ?_, ?_, ?_, ?_⟩
  · exact manifoldContDiffAt_comp T.smoothStructure.property.1.1 hgi
      (by simpa only [Function.comp_apply, hgip] using hfi)
  · simp only [Function.comp_apply, hgip, hfip]
  · filter_upwards [hgiL.comp_tendsto (hf.1 p).1, hfiL] with x hx hfx
    change fi (gi (g (f x))) = x
    change gi (g (f x)) = f x at hx
    rw [hx]
    exact hfx
  · have ht : Tendsto gi (𝓝 (g (f p))) (𝓝 (f p)) := by
      simpa only [ContinuousAt, hgip] using hgi.1
    filter_upwards [hfiR.comp_tendsto ht, hgiR] with y hy hgy
    change g (f (fi (gi y))) = y
    change f (fi (gi y)) = gi y at hy
    rw [hy]
    exact hgy


end LocalDiffeomorphisms


section TensorCoordinates
open BundleData BundleOperationsData FrameData CovectorData Set Filter
open scoped Topology

-- Tested in /tmp/ContractionSmoothness.lean.
-- Add within namespace SmoothManifolds.Tensors after powerCoordinates_tprod and powerBundle_coordinates.
theorem dualBundle_coordinates {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    (B : SmoothVectorBundle S d ι E) (D : DualBundle B)
    (i : ι) (p : M) (hp : p ∈ B.baseSet i) (lam : Module.Dual ℝ (E p)) :
    letI := D.space.topology
    ((D.space.bundle.trivialization i) ⟨p, lam⟩).2 =
      BundleOperations.dualCoordinates (B.fiberCoordinates i p hp) lam := by
  letI := D.space.topology
  ext j
  rw [D.coordinates i p hp, BundleOperations.dualCoordinates_apply]
  rfl

theorem tensorBundle_coordinates {n d e : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {κ : Type w}
    {E : M → Type u} {F : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean d) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean e) F)]
    (B : SmoothVectorBundle S d ι E) (D : SmoothVectorBundle S e κ F)
    (T : BundleOperationsData.TensorBundle B D) (i : ι × κ) (p : M)
    (hp : letI := T.space.topology; p ∈ T.space.bundle.baseSet i)
    (hB : p ∈ B.baseSet i.1) (hD : p ∈ D.baseSet i.2) (x : E p ⊗[ℝ] F p) :
    letI := T.space.topology
    ((T.space.bundle.trivialization i) ⟨p, x⟩).2 =
      BundleOperations.tensorCoordinates (B.fiberCoordinates i.1 p hB)
        (D.fiberCoordinates i.2 p hD) x := by
  letI := T.space.topology
  change T.space.bundle.fiberCoordinates i p hp x = _
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    ext j
    obtain ⟨⟨j,k⟩, rfl⟩ := finProdFinEquiv.surjective j
    simp only [SmoothVectorBundle.fiberCoordinates_apply,
      BundleOperations.tensorCoordinates_tmul]
    exact T.coordinates i p hp x y j k
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def mixedCoordinates {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (r s : ℕ) :
    Fiber V r s ≃ₗ[ℝ] Euclidean (d^r * d^s) :=
  by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℝ
  letI : AddCommGroup (Power V r) := Module.addCommMonoidToAddCommGroup ℝ
  letI : AddCommGroup (Power (Module.Dual ℝ V) s) := Module.addCommMonoidToAddCommGroup ℝ
  let f : Module.Dual ℝ V ≃ₗ[ℝ] Euclidean d := BundleOperations.dualCoordinates e
  exact BundleOperations.tensorCoordinates (powerCoordinates e r) (powerCoordinates f s)

theorem mixedCoordinates_transport {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (r s : ℕ) :
    (mixedCoordinates (LinearEquiv.refl ℝ (Euclidean d)) r s).toLinearMap.comp
      (mixedTransport r s e.symm) = (mixedCoordinates e r s).toLinearMap := by
  ext v lam j
  obtain ⟨⟨j,k⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨j,rfl⟩ := (powerIndex d r).surjective j
  obtain ⟨k,rfl⟩ := (powerIndex d s).surjective k
  change mixedCoordinates (LinearEquiv.refl ℝ (Euclidean d)) r s
      (mixedTransport r s e.symm (TensorData.pure v lam)) _ =
    mixedCoordinates e r s (TensorData.pure v lam) _
  rw [mixedTransport_pure]
  simp [mixedCoordinates, TensorData.pure,
    BundleOperations.tensorCoordinates_tmul, powerCoordinates_tprod,
    BundleOperations.dualCoordinates_apply]

noncomputable def contractionCoordinates (d : ℕ) {r s : ℕ}
    (i : Fin (r+1)) (j : Fin (s+1)) :
    Euclidean (d^(r+1) * d^(s+1)) →ₗ[ℝ] Euclidean (d^r * d^s) :=
  (mixedCoordinates (LinearEquiv.refl ℝ (Euclidean d)) r s).toLinearMap ∘ₗ
    contract (Euclidean d) i j ∘ₗ
      (mixedCoordinates (LinearEquiv.refl ℝ (Euclidean d)) (r+1) (s+1)).symm.toLinearMap

theorem mixedCoordinates_contract {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) {r s : ℕ}
    (i : Fin (r+1)) (j : Fin (s+1)) (x : Fiber V (r+1) (s+1)) :
    mixedCoordinates e r s (contract V i j x) =
      contractionCoordinates d i j (mixedCoordinates e (r+1) (s+1) x) := by
  have h₁ := congrArg (fun f => f x) (mixedCoordinates_transport e (r+1) (s+1))
  have h₂ := congrArg (fun f => f (contract V i j x)) (mixedCoordinates_transport e r s)
  have h₃ := congrArg (fun f => f x) (contract_natural i j e.symm)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h₁ h₂ h₃
  rw [← h₁, ← h₂]
  simp only [contractionCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, ← h₃]

theorem tensorBundle_diagonal_baseSet {n r s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)
    (c : TangentIndex S) :
    letI := B.cotangent.realization.space.topology
    letI := B.cotangent.dual.space.topology
    letI := B.upper.space.topology
    letI := B.lower.space.topology
    letI := B.mixed.space.topology
    B.mixed.space.bundle.baseSet (c,c) = c.val.source := by
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  letI := B.upper.space.topology
  letI := B.lower.space.topology
  letI := B.mixed.space.topology
  simp only [B.mixed.baseSet, B.upper.baseSet, B.lower.baseSet,
    B.cotangent.dual.baseSet, B.cotangent.realization.baseSet, Set.inter_self]

theorem tensorBundle_diagonal_coordinates {n r s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)
    (c : TangentIndex S) (p : M) (hp : p ∈ c.val.source) (x : Fiber (TangentSpace S p) r s) :
    letI := B.cotangent.realization.space.topology
    letI := B.cotangent.dual.space.topology
    letI := B.upper.space.topology
    letI := B.lower.space.topology
    letI := B.mixed.space.topology
    ((B.mixed.space.bundle.trivialization (c,c)) ⟨p,x⟩).2 =
      mixedCoordinates (B.cotangent.tangent.fiberCoordinates.equiv c.val c.property p hp) r s x := by
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  letI := B.upper.space.topology
  letI := B.lower.space.topology
  letI := B.mixed.space.topology
  let e := B.cotangent.tangent.fiberCoordinates.equiv c.val c.property p hp
  have hpR : p ∈ B.cotangent.realization.space.bundle.baseSet c := by
    rw [B.cotangent.realization.baseSet]; exact hp
  have hpD : p ∈ B.cotangent.dual.space.bundle.baseSet c := by
    rw [B.cotangent.dual.baseSet]; exact hpR
  have hpU : p ∈ B.upper.space.bundle.baseSet c := by rw [B.upper.baseSet]; exact hpR
  have hpL : p ∈ B.lower.space.bundle.baseSet c := by rw [B.lower.baseSet]; exact hpD
  have hpM : p ∈ B.mixed.space.bundle.baseSet (c,c) := by
    rw [tensorBundle_diagonal_baseSet]; exact hp
  have he : B.cotangent.realization.space.bundle.fiberCoordinates c p hpR = e := by
    apply LinearEquiv.ext
    intro v
    exact B.cotangent.realization.coordinates c p hp v
  have hdual : B.cotangent.dual.space.bundle.fiberCoordinates c p hpD =
      BundleOperations.dualCoordinates e := by
    ext lam j
    rw [SmoothVectorBundle.fiberCoordinates_apply,
      dualBundle_coordinates B.cotangent.realization.space.bundle B.cotangent.dual c p hpR,
      he]
  have hu : B.upper.space.bundle.fiberCoordinates c p hpU = powerCoordinates e r := by
    ext z j
    rw [SmoothVectorBundle.fiberCoordinates_apply,
      powerBundle_coordinates B.cotangent.realization.space.bundle B.upper c p hpR, he]
  have hl : B.lower.space.bundle.fiberCoordinates c p hpL =
      powerCoordinates (BundleOperations.dualCoordinates e) s := by
    ext z j
    rw [SmoothVectorBundle.fiberCoordinates_apply,
      powerBundle_coordinates B.cotangent.dual.space.bundle B.lower c p hpD, hdual]
  rw [tensorBundle_coordinates B.upper.space.bundle B.lower.space.bundle B.mixed
    (c,c) p hpM hpU hpL, hu, hl]
  rfl


/-- A smooth family of coordinate matrices defines a smooth map on total spaces.
No continuity of the total-space map is assumed. -/
theorem bundleMap_smooth_of_coordinates
    {n m r s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    {S : SmoothManifold n a M} {T : SmoothManifold m b P}
    {ι : Type v} {κ : Type t} {E : M → Type w} {F : P → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle T s κ F)
    (f : M → P) (A : (p : M) → E p →ₗ[ℝ] F (f p))
    (C : ι → κ → M → Euclidean r →L[ℝ] Euclidean s)
    (hf : IsSmoothMap S T f)
    (hC : ∀ i j p, p ∈ B.baseSet i → f p ∈ D.baseSet j →
      VectorSmoothAt S.smoothStructure.val (C i j) p)
    (hcoord : ∀ i j p, p ∈ B.baseSet i → f p ∈ D.baseSet j → ∀ x,
      ((D.trivialization j) ⟨f p, A p x⟩).2 =
        C i j p (((B.trivialization i) ⟨p, x⟩).2)) :
    IsSmoothMap B.totalManifold D.totalManifold
      (fun q => (⟨f q.proj, A q.proj q.snd⟩ : Bundle.TotalSpace (Euclidean s) F)) := by
  intro q
  obtain ⟨i, hi⟩ := B.covers q.proj
  obtain ⟨j, hj⟩ := D.covers (f q.proj)
  have hbase := manifoldContDiffAt_comp S.smoothStructure.property.1.1
    (B.projection_smooth q) (hf q.proj)
  have hm := (hC i j q.proj hi hj).comp (g := fun y : Bundle.TotalSpace (Euclidean r) E => y.proj) S.smoothStructure.property.1.1
    (B.projection_smooth q)
  have hv := hm.clm_apply (Frames.trivializationCoordinates_smoothAt B i q hi)
  apply Frames.smoothAt_from_trivialization D B.totalManifold.smoothStructure.property.1
    (f := fun y => ⟨f y.proj, A y.proj y.snd⟩) j hj hbase hv (fun _ => rfl)
  have hBi : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hDj : IsOpen (D.baseSet j) := D.trivialization_baseSet j ▸ (D.trivialization j).open_baseSet
  filter_upwards [(B.projection_smooth q).1.preimage_mem_nhds (hBi.mem_nhds hi),
    hbase.1.preimage_mem_nhds (hDj.mem_nhds hj)] with y hyi hyj
  exact hcoord i j y.proj hyi hyj y.snd

theorem power_map_coefficients {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {n m k : ℕ}
    (e : V ≃ₗ[ℝ] Euclidean n) (d : W ≃ₗ[ℝ] Euclidean m) (L : V →ₗ[ℝ] W)
    (x : Power V k) (q : Fin k → Fin m) :
    powerCoordinates d k (PiTensorProduct.map (fun _ : Fin k => L) x) (powerIndex m k q) =
      ∑ j : Fin (n^k), powerCoordinates e k x j *
        ∏ l : Fin k, d (L (e.symm (Pi.single ((powerIndex n k).symm j l) 1))) (q l) := by
  classical
  have hx : x = ∑ j : Fin (n^k), (powerCoordinates e k x j) •
      (powerCoordinates e k).symm (Pi.single j 1) := by
    apply (powerCoordinates e k).injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    ext z
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [powerCoordinates_symm_single, PiTensorProduct.map_tprod, powerCoordinates_tprod]


theorem cotangent_coordinates_symm_single
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (j : Fin n) :
    letI := (cotangentSpace C).topology
    ((cotangentSpace C).bundle.fiberCoordinates ⟨c,hc⟩ p
      (by rw [Covectors.cotangent_baseSet]; exact hp)).symm (Pi.single j 1) =
      coordinateCovector C.tangent.fiberCoordinates c hc p hp j := by
  letI := (cotangentSpace C).topology
  apply ((cotangentSpace C).bundle.fiberCoordinates ⟨c,hc⟩ p
    (by rw [Covectors.cotangent_baseSet]; exact hp)).injective
  ext l
  rw [LinearEquiv.apply_symm_apply, SmoothVectorBundle.fiberCoordinates_apply,
    Covectors.cotangent_coordinates C c hc p hp]
  simp [Covectors.coordinateCovector_apply, Pi.single_apply, eq_comm]

theorem covector_map_coefficient
    {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (C : CotangentBundle S) (D : CotangentBundle T) (f : P → M)
    (hf : IsSmoothMap T S f)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (hL : ∀ p, IsDifferential T S f p (L p))
    (c : ModelChart n a M) (e : ModelChart m b P)
    (hc : c ∈ S.smoothStructure.val) (he : e ∈ T.smoothStructure.val)
    (p : P) (hp : p ∈ e.source) (hfp : f p ∈ c.source) (j : Fin n) (l : Fin m) :
    letI := (cotangentSpace C).topology
    letI := (cotangentSpace D).topology
    (cotangentSpace D).bundle.fiberCoordinates ⟨e,he⟩ p
      (by rw [Covectors.cotangent_baseSet]; exact hp)
      ((L p).dualMap (((cotangentSpace C).bundle.fiberCoordinates ⟨c,hc⟩ (f p)
        (by rw [Covectors.cotangent_baseSet]; exact hfp)).symm (Pi.single j 1))) l =
      FiniteRegularityData.chartDerivative e c f p (Pi.single l 1) j := by
  letI := (cotangentSpace C).topology
  letI := (cotangentSpace D).topology
  rw [cotangent_coordinates_symm_single, SmoothVectorBundle.fiberCoordinates_apply,
    Covectors.cotangent_coordinates]
  change C.tangent.fiberCoordinates.equiv c hc (f p) hfp
    (L p (coordinateVector D.tangent.fiberCoordinates e he p hp l)) j = _
  have hJ := FiniteRegularity.smooth_jacobian_coordinateDerivative T S f hf p (L p) (hL p)
    e c he hc hp hfp (D.tangent.fiberCoordinates.equiv e he p hp)
    (C.tangent.fiberCoordinates.equiv c hc (f p) hfp)
    (D.tangent.fiberCoordinates.isCoordinates e he p hp)
    (C.tangent.fiberCoordinates.isCoordinates c hc (f p) hfp)
    (coordinateVector D.tangent.fiberCoordinates e he p hp l)
  simpa only [coordinateVector, LinearEquiv.apply_symm_apply] using congrFun hJ j


theorem covariant_pullback_smooth
    {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (C : CotangentBundle S) (D : CotangentBundle T) (s : ℕ)
    (U : letI := (cotangentSpace C).topology; PowerBundle (cotangentSpace C).bundle s)
    (V : letI := (cotangentSpace D).topology; PowerBundle (cotangentSpace D).bundle s)
    (f : P → M) (hf : IsSmoothMap T S f)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (hL : ∀ p, IsDifferential T S f p (L p)) :
    letI := (cotangentSpace C).topology
    letI := (cotangentSpace D).topology
    letI := U.space.topology
    letI := V.space.topology
    ∀ A : CovariantField S s,
      IsSmoothMap S U.space.bundle.totalManifold
        (fun p => (⟨p,A p⟩ : Bundle.TotalSpace (Euclidean (n^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace S p)) s))) →
      IsSmoothMap T V.space.bundle.totalManifold
        (fun p => (⟨p,covariantPullback S T f L A p⟩ : Bundle.TotalSpace (Euclidean (m^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace T p)) s))) := by
  letI := (cotangentSpace C).topology
  letI := (cotangentSpace D).topology
  letI := U.space.topology
  letI := V.space.topology
  intro A hA p
  obtain ⟨e, he, hp⟩ := T.smoothStructure.property.1.1 p
  obtain ⟨c, hc, hfp⟩ := S.smoothStructure.property.1.1 (f p)
  have hfpC : f p ∈ (cotangentSpace C).bundle.baseSet ⟨c,hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hfp
  have hpD : p ∈ (cotangentSpace D).bundle.baseSet ⟨e,he⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hp
  have hfpU : f p ∈ U.space.bundle.baseSet ⟨c,hc⟩ := by rw [U.baseSet]; exact hfpC
  have hpV : p ∈ V.space.bundle.baseSet ⟨e,he⟩ := by rw [V.baseSet]; exact hpD
  let ac (y : P) : Euclidean (n^s) :=
    ((U.space.bundle.trivialization ⟨c,hc⟩) ⟨f y,A (f y)⟩).2
  have hAf := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1
    f (fun q => (⟨q,A q⟩ : Bundle.TotalSpace (Euclidean (n^s))
      (fun q => Power (Module.Dual ℝ (TangentSpace S q)) s))) hf hA
  have hac : VectorSmoothAt T.smoothStructure.val ac p :=
    FrameData.VectorSmoothAt.comp
      (g := fun y => (⟨f y,A (f y)⟩ : Bundle.TotalSpace (Euclidean (n^s))
        (fun q => Power (Module.Dual ℝ (TangentSpace S q)) s)))
      U.space.bundle.totalManifold.smoothStructure.property.1.1
      (Frames.trivializationCoordinates_smoothAt U.space.bundle ⟨c,hc⟩
        ⟨f p,A (f p)⟩ hfpU) (hAf p)
  let vc (y : P) : Euclidean (m^s) := fun q => ∑ j : Fin (n^s), ac y j *
    ∏ l : Fin s, FiniteRegularityData.chartDerivative e c f y
      (Pi.single ((powerIndex m s).symm q l) 1) ((powerIndex n s).symm j l)
  have hJ := chartDerivative_smoothAt T S f hf e c he hc p hp hfp
  have hvc : VectorSmoothAt T.smoothStructure.val vc p := by
    apply FrameData.VectorSmoothAt.pi
    intro q
    apply FrameData.VectorSmoothAt.sum
    intro j
    apply FrameData.VectorSmoothAt.postcomp
      ((hac.postcomp (ContinuousLinearMap.proj j).contDiff).prod ?_)
      (contDiff_fst.mul contDiff_snd)
    exact vectorSmoothAt_prod (κ := Fin s)
      (f := fun y l => FiniteRegularityData.chartDerivative e c f y
        (Pi.single ((powerIndex m s).symm q l) 1) ((powerIndex n s).symm j l))
      (fun l => (hJ.clm_apply (FrameData.VectorSmoothAt.const _
        (Pi.single ((powerIndex m s).symm q l) 1) p)).postcomp
          (ContinuousLinearMap.proj ((powerIndex n s).symm j l)).contDiff)
  apply Frames.smoothAt_from_trivialization V.space.bundle T.smoothStructure.property.1
    ⟨e,he⟩ hpV ((manifoldContDiff_id (⊤ : ℕ∞) _ T.smoothStructure.property.1) p)
    hvc (fun _ => rfl)
  filter_upwards [e.open_source.mem_nhds hp,
    (hf p).1.preimage_mem_nhds (c.open_source.mem_nhds hfp)] with y hye hyc
  have hyeD : y ∈ (cotangentSpace D).bundle.baseSet ⟨e,he⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hye
  have hycC : f y ∈ (cotangentSpace C).bundle.baseSet ⟨c,hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hyc
  rw [powerBundle_coordinates (cotangentSpace D).bundle V ⟨e,he⟩ y hyeD]
  ext q
  change powerCoordinates ((cotangentSpace D).bundle.fiberCoordinates ⟨e,he⟩ y hyeD) s
    (PiTensorProduct.map (fun _ : Fin s => (L y).dualMap) (A (f y))) q = vc y q
  conv_lhs => rw [← (powerIndex m s).apply_symm_apply q]
  rw [power_map_coefficients ((cotangentSpace C).bundle.fiberCoordinates ⟨c,hc⟩ (f y) hycC)]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  · change _ = ((U.space.bundle.trivialization ⟨c,hc⟩) ⟨f y,A (f y)⟩).2 j
    rw [powerBundle_coordinates (cotangentSpace C).bundle U ⟨c,hc⟩ (f y) hycC]
  · apply Finset.prod_congr rfl
    intro l _
    exact covector_map_coefficient S T C D f hf L hL c e hc he y hye hyc _ _


end TensorCoordinates

section SmoothMixedOperations
open BundleData BundleOperationsData FrameData CovectorData Set Filter
open scoped Topology

-- Compiles against current SmoothManifolds.Ch05.Tensors.
theorem tensorSpace_diagonal_coordinates {n r s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)
    (c : TangentIndex S) (p : M) (hp : p ∈ c.val.source)
    (e : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (he : IsChartCoordinates S p c.val e)
    (x : Fiber (TangentSpace S p) r s) :
    letI := (tensorSpace B).topology
    (((tensorSpace B).bundle.trivialization (c,c)) ⟨p,x⟩).2 =
      mixedCoordinates e r s x := by
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  letI := B.upper.space.topology
  letI := B.lower.space.topology
  letI := B.mixed.space.topology
  have h := tensorBundle_diagonal_coordinates B c p hp x
  have heq := TangentBundle.chartCoordinates_unique
    (B.cotangent.tangent.fiberCoordinates.isCoordinates c.val c.property p hp) he
  rw [heq] at h
  exact h

theorem tensorSpace_diagonal_baseSet {n r s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)
    (c : TangentIndex S) : letI := (tensorSpace B).topology
    (tensorSpace B).bundle.baseSet (c,c) = c.val.source :=
  tensorBundle_diagonal_baseSet B c

theorem contraction_smooth {n r s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (B : TensorData.TensorBundle S (r+1) (s+1)) (D : TensorData.TensorBundle S r s)
    (i : Fin (r+1)) (j : Fin (s+1)) :
    letI := (tensorSpace B).topology
    letI := (tensorSpace D).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace D).bundle.totalManifold
      (fun q => (⟨q.proj, contract (TangentSpace S q.proj) i j q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r * n^s))
          (fun p => Fiber (TangentSpace S p) r s))) := by
  letI := (tensorSpace B).topology
  letI := (tensorSpace D).topology
  intro q
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 q.proj
  let c' : TangentIndex S := ⟨c, hc⟩
  have hi : q.proj ∈ (tensorSpace B).bundle.baseSet (c',c') := by
    rw [tensorSpace_diagonal_baseSet]; exact hp
  have hj : q.proj ∈ (tensorSpace D).bundle.baseSet (c',c') := by
    rw [tensorSpace_diagonal_baseSet]; exact hp
  have hv := (Frames.trivializationCoordinates_smoothAt (tensorSpace B).bundle
    (c',c') q hi).postcomp (contractionCoordinates n i j).toContinuousLinearMap.contDiff
  apply Frames.smoothAt_from_trivialization (tensorSpace D).bundle
    (tensorSpace B).bundle.totalManifold.smoothStructure.property.1
    (f := fun y => ⟨y.proj, contract (TangentSpace S y.proj) i j y.snd⟩)
    (c',c') hj ((tensorSpace B).bundle.projection_smooth q) hv (fun _ => rfl)
  filter_upwards [((tensorSpace B).bundle.projection_smooth q).1.preimage_mem_nhds
    (c.open_source.mem_nhds hp)] with y hy
  let e := B.cotangent.tangent.fiberCoordinates.equiv c hc y.proj hy
  have he : IsChartCoordinates S y.proj c e :=
    B.cotangent.tangent.fiberCoordinates.isCoordinates c hc y.proj hy
  rw [tensorSpace_diagonal_coordinates D c' y.proj hy e he,
    mixedCoordinates_contract, tensorSpace_diagonal_coordinates B c' y.proj hy e he]
  rfl



-- Tested in /tmp/TensorMultiplyFinal.lean with current main imported.
-- Add inside SmoothManifolds.Tensors after coordinate helpers.
noncomputable def tensorMultiplicationCoordinates (d r s r' s' : ℕ) :
    Euclidean (d^r * d^s) →ₗ[ℝ] Euclidean (d^r' * d^s') →ₗ[ℝ]
      Euclidean (d^(r+r') * d^(s+s')) :=
  TensorProduct.curry
    ((mixedCoordinates (LinearEquiv.refl ℝ (Euclidean d)) (r+r') (s+s')).toLinearMap ∘ₗ
      tensorProductMap (Euclidean d) r s r' s' ∘ₗ
        TensorProduct.map
          (mixedCoordinates (LinearEquiv.refl ℝ (Euclidean d)) r s).symm.toLinearMap
          (mixedCoordinates (LinearEquiv.refl ℝ (Euclidean d)) r' s').symm.toLinearMap)

theorem mixedCoordinates_tensorMultiply {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (r s r' s' : ℕ)
    (x : Fiber V r s) (y : Fiber V r' s') :
    mixedCoordinates e (r+r') (s+s') (tensorMultiply V r s r' s' x y) =
      tensorMultiplicationCoordinates d r s r' s' (mixedCoordinates e r s x)
        (mixedCoordinates e r' s' y) := by
  have h₁ := congrArg (fun f => f x) (mixedCoordinates_transport e r s)
  have h₂ := congrArg (fun f => f y) (mixedCoordinates_transport e r' s')
  have h₃ := congrArg (fun f => f (tensorMultiply V r s r' s' x y))
    (mixedCoordinates_transport e (r+r') (s+s'))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h₁ h₂ h₃
  rw [← h₁, ← h₂, ← h₃]
  simp only [tensorMultiplicationCoordinates, TensorProduct.curry_apply,
    LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact congrArg (mixedCoordinates (LinearEquiv.refl ℝ (Euclidean d)) (r+r') (s+s'))
    (tensorMultiply_natural r s r' s' e.symm x y)

theorem vectorSmoothAt_bilinear {m : ℕ} {b : ModelKind} {X : Type q}
    [TopologicalSpace X] {A : Set (ModelChart m b X)} {p : X}
    {d e f : ℕ} (L : Euclidean d →ₗ[ℝ] Euclidean e →ₗ[ℝ] Euclidean f)
    {v : X → Euclidean d} {w : X → Euclidean e}
    (hv : VectorSmoothAt A v p) (hw : VectorSmoothAt A w p) :
    VectorSmoothAt A (fun x => L (v x) (w x)) p := by
  let CL : Euclidean d →L[ℝ] Euclidean e →L[ℝ] Euclidean f :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Euclidean e →ₗ[ℝ] Euclidean f) ≃ₗ[ℝ]
          (Euclidean e →L[ℝ] Euclidean f)).toLinearMap.comp L)
  exact ((hv.postcomp CL.contDiff).clm_apply hw)

/-- The usual product of mixed tensors is a smooth bundle operation, with
arbitrary smooth parameters and without a boundary or positive-rank restriction. -/
theorem tensorMultiply_lift_smooth
    {n r s r' s' : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M}
    (A : TensorData.TensorBundle S r s) (B : TensorData.TensorBundle S r' s')
    (C : TensorData.TensorBundle S (r+r') (s+s'))
    {m : ℕ} {b : ModelKind} {X : Type v} [TopologicalSpace X]
    (U : SmoothManifold m b X) (f : X → M)
    (x : (t : X) → Fiber (TangentSpace S (f t)) r s)
    (y : (t : X) → Fiber (TangentSpace S (f t)) r' s')
    (hx : letI := (tensorSpace A).topology
      IsSmoothMap U (tensorSpace A).bundle.totalManifold (fun t => ⟨f t, x t⟩))
    (hy : letI := (tensorSpace B).topology
      IsSmoothMap U (tensorSpace B).bundle.totalManifold (fun t => ⟨f t, y t⟩)) :
    letI := (tensorSpace C).topology
    IsSmoothMap U (tensorSpace C).bundle.totalManifold
      (fun t => (⟨f t, tensorMultiply (TangentSpace S (f t)) r s r' s' (x t) (y t)⟩ :
        Bundle.TotalSpace (Euclidean (n^(r+r')*n^(s+s')))
          (fun p => Fiber (TangentSpace S p) (r+r') (s+s')))) := by
  letI := (tensorSpace A).topology
  letI := (tensorSpace B).topology
  letI := (tensorSpace C).topology
  intro t
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 (f t)
  let i : TangentIndex S := ⟨c, hc⟩
  have hA : f t ∈ (tensorSpace A).bundle.baseSet (i,i) := by
    rw [show (tensorSpace A).bundle.baseSet (i,i) = c.source from tensorBundle_diagonal_baseSet A i]
    exact hpc
  have hB : f t ∈ (tensorSpace B).bundle.baseSet (i,i) := by
    rw [show (tensorSpace B).bundle.baseSet (i,i) = c.source from tensorBundle_diagonal_baseSet B i]
    exact hpc
  have hC : f t ∈ (tensorSpace C).bundle.baseSet (i,i) := by
    rw [show (tensorSpace C).bundle.baseSet (i,i) = c.source from tensorBundle_diagonal_baseSet C i]
    exact hpc
  have hf : ManifoldSmoothAt U.smoothStructure.val S.smoothStructure.val f t :=
    manifoldContDiffAt_comp (tensorSpace A).bundle.totalManifold.smoothStructure.property.1.1
      (hx t) ((tensorSpace A).bundle.projection_smooth ⟨f t, x t⟩)
  have hAx := FrameData.VectorSmoothAt.comp
    (g := fun t => (⟨f t, x t⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
      (fun p => Fiber (TangentSpace S p) r s))) (x := t)
    (tensorSpace A).bundle.totalManifold.smoothStructure.property.1.1
    (Frames.trivializationCoordinates_smoothAt (tensorSpace A).bundle (i,i) ⟨f t, x t⟩ hA)
    (hx t)
  have hBy := FrameData.VectorSmoothAt.comp
    (g := fun t => (⟨f t, y t⟩ : Bundle.TotalSpace (Euclidean (n^r'*n^s'))
      (fun p => Fiber (TangentSpace S p) r' s'))) (x := t)
    (tensorSpace B).bundle.totalManifold.smoothStructure.property.1.1
    (Frames.trivializationCoordinates_smoothAt (tensorSpace B).bundle (i,i) ⟨f t, y t⟩ hB)
    (hy t)
  refine Frames.smoothAt_from_trivialization (tensorSpace C).bundle
    U.smoothStructure.property.1 (i,i) hC hf
    (vectorSmoothAt_bilinear (tensorMultiplicationCoordinates n r s r' s') hAx hBy)
    (fun _ => rfl) ?_
  filter_upwards [hf.1.preimage_mem_nhds (c.open_source.mem_nhds hpc)] with u hu
  change (((tensorSpace C).bundle.trivialization (i,i))
      ⟨f u, tensorMultiply (TangentSpace S (f u)) r s r' s' (x u) (y u)⟩).2 =
    tensorMultiplicationCoordinates n r s r' s'
      ((((tensorSpace A).bundle.trivialization (i,i)) ⟨f u, x u⟩).2)
      ((((tensorSpace B).bundle.trivialization (i,i)) ⟨f u, y u⟩).2)
  have hCeq : (((tensorSpace C).bundle.trivialization (i,i))
      ⟨f u, tensorMultiply (TangentSpace S (f u)) r s r' s' (x u) (y u)⟩).2 =
      mixedCoordinates (C.cotangent.tangent.fiberCoordinates.equiv i.val i.property (f u) hu)
        (r+r') (s+s') (tensorMultiply (TangentSpace S (f u)) r s r' s' (x u) (y u)) :=
    tensorBundle_diagonal_coordinates C i (f u) hu _
  have hAeq : (((tensorSpace A).bundle.trivialization (i,i)) ⟨f u, x u⟩).2 =
      mixedCoordinates (A.cotangent.tangent.fiberCoordinates.equiv i.val i.property (f u) hu)
        r s (x u) := tensorBundle_diagonal_coordinates A i (f u) hu _
  have hBeq : (((tensorSpace B).bundle.trivialization (i,i)) ⟨f u, y u⟩).2 =
      mixedCoordinates (B.cotangent.tangent.fiberCoordinates.equiv i.val i.property (f u) hu)
        r' s' (y u) := tensorBundle_diagonal_coordinates B i (f u) hu _
  rw [hCeq, hAeq, hBeq]
  have heA := TangentBundle.chartCoordinates_unique
    (A.cotangent.tangent.fiberCoordinates.isCoordinates i.val i.property (f u) hu)
    (C.cotangent.tangent.fiberCoordinates.isCoordinates i.val i.property (f u) hu)
  have heB := TangentBundle.chartCoordinates_unique
    (B.cotangent.tangent.fiberCoordinates.isCoordinates i.val i.property (f u) hu)
    (C.cotangent.tangent.fiberCoordinates.isCoordinates i.val i.property (f u) hu)
  rw [heA, heB]
  exact mixedCoordinates_tensorMultiply _ r s r' s' (x u) (y u)

@[simp] theorem mixedCoordinates_pure {V : Type u} [AddCommGroup V] [Module ℝ V]
    {n r s : ℕ} (e : V ≃ₗ[ℝ] Euclidean n)
    (v : Fin r → V) (lam : Fin s → Module.Dual ℝ V) (q : Fin (n^r*n^s)) :
    mixedCoordinates e r s (TensorData.pure v lam) q =
      (∏ l, e (v l) ((powerIndex n r).symm (finProdFinEquiv.symm q).1 l)) *
      ∏ l, lam l (e.symm (Pi.single ((powerIndex n s).symm (finProdFinEquiv.symm q).2 l) 1)) := by
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective q
  obtain ⟨i,rfl⟩ := (powerIndex n r).surjective i
  obtain ⟨j,rfl⟩ := (powerIndex n s).surjective j
  simp [mixedCoordinates, TensorData.pure, BundleOperations.tensorCoordinates_tmul,
    powerCoordinates_tprod, BundleOperations.dualCoordinates_apply]

@[simp] theorem mixedCoordinates_symm_single {V : Type u} [AddCommGroup V] [Module ℝ V]
    {n r s : ℕ} (e : V ≃ₗ[ℝ] Euclidean n) (j : Fin (n^r*n^s)) :
    (mixedCoordinates e r s).symm (Pi.single j 1) =
      TensorData.pure
        (fun l => e.symm (Pi.single ((powerIndex n r).symm (finProdFinEquiv.symm j).1 l) 1))
        (fun l => (BundleOperations.dualCoordinates e).symm
          (Pi.single ((powerIndex n s).symm (finProdFinEquiv.symm j).2 l) 1)) := by
  simp only [mixedCoordinates, BundleOperations.tensorCoordinates_symm_single,
    powerCoordinates_symm_single, TensorData.pure]
  rfl

theorem mixedTransport_coefficients {V W : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n m r s : ℕ} (e : V ≃ₗ[ℝ] Euclidean n) (d : W ≃ₗ[ℝ] Euclidean m)
    (F : W ≃ₗ[ℝ] V) (x : Fiber V r s) (q : Fin (m^r*m^s)) :
    mixedCoordinates d r s (mixedTransport r s F x) q =
      ∑ j : Fin (n^r*n^s), mixedCoordinates e r s x j *
        ((∏ l : Fin r, d (F.symm (e.symm
          (Pi.single ((powerIndex n r).symm (finProdFinEquiv.symm j).1 l) 1)))
          ((powerIndex m r).symm (finProdFinEquiv.symm q).1 l)) *
        ∏ l : Fin s, e (F (d.symm
          (Pi.single ((powerIndex m s).symm (finProdFinEquiv.symm q).2 l) 1)))
          ((powerIndex n s).symm (finProdFinEquiv.symm j).2 l)) := by
  classical
  have hx : x = ∑ j : Fin (n^r*n^s), mixedCoordinates e r s x j •
      (mixedCoordinates e r s).symm (Pi.single j 1) := by
    apply (mixedCoordinates e r s).injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    ext z
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mixedCoordinates_symm_single, mixedTransport_pure, mixedCoordinates_pure]
  congr 2
  apply Finset.prod_congr rfl
  intro l _
  change (BundleOperations.dualCoordinates e).symm (Pi.single _ 1) _ = _
  simp [BundleOperations.dualCoordinates_symm_apply, Pi.single_apply]


theorem inverse_differential_coordinates
    {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (hf : IsLocalDiffeomorphism T S f)
    (F : (p : P) → TangentSpace T p ≃ₗ[ℝ] TangentSpace S (f p))
    (hF : ∀ p, IsDifferential T S f p (F p).toLinearMap)
    (B : TangentBundleData.FiberCoordinates S) (C : TangentBundleData.FiberCoordinates T)
    (c : ModelChart n a M) (e : ModelChart m b P)
    (hc : c ∈ S.smoothStructure.val) (he : e ∈ T.smoothStructure.val)
    (p : P) (hp : p ∈ e.source) (hfp : f p ∈ c.source) (v : TangentSpace S (f p)) :
    ContinuousLinearMap.inverse (FiniteRegularityData.chartDerivative e c f p)
      (B.equiv c hc (f p) hfp v) = C.equiv e he p hp ((F p).symm v) := by
  apply (chartDerivative_isInvertible T S f hf e c he hc p hp hfp).inverse_apply_eq.mpr
  have hJ := FiniteRegularity.smooth_jacobian_coordinateDerivative T S f hf.1 p
    (F p).toLinearMap (hF p) e c he hc hp hfp (C.equiv e he p hp)
    (B.equiv c hc (f p) hfp) (C.isCoordinates e he p hp) (B.isCoordinates c hc (f p) hfp)
    ((F p).symm v)
  simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hJ

theorem mixed_pullback_smooth
    {n m r s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (B : TensorData.TensorBundle S r s) (C : TensorData.TensorBundle T r s)
    (f : P → M) (hf : IsLocalDiffeomorphism T S f)
    (F : (p : P) → TangentSpace T p ≃ₗ[ℝ] TangentSpace S (f p))
    (hF : ∀ p, IsDifferential T S f p (F p).toLinearMap)
    (A : Field S r s) (hA : IsSmoothField B A) :
    IsSmoothField C (mixedPullback S T f F A) := by
  classical
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  letI := B.upper.space.topology
  letI := B.lower.space.topology
  letI := C.cotangent.realization.space.topology
  letI := C.cotangent.dual.space.topology
  letI := C.upper.space.topology
  letI := C.lower.space.topology
  letI := (tensorSpace B).topology
  letI := (tensorSpace C).topology
  intro p
  obtain ⟨e, he, hp⟩ := T.smoothStructure.property.1.1 p
  obtain ⟨c, hc, hfp⟩ := S.smoothStructure.property.1.1 (f p)
  let ec : TangentIndex T := ⟨e,he⟩
  let cc : TangentIndex S := ⟨c,hc⟩
  have hfpB : f p ∈ (tensorSpace B).bundle.baseSet (cc,cc) := by
    change f p ∈ B.mixed.space.bundle.baseSet (cc,cc)
    rw [tensorBundle_diagonal_baseSet]; exact hfp
  have hpC : p ∈ (tensorSpace C).bundle.baseSet (ec,ec) := by
    change p ∈ C.mixed.space.bundle.baseSet (ec,ec)
    rw [tensorBundle_diagonal_baseSet]; exact hp
  let ac (y : P) : Euclidean (n^r*n^s) :=
    (((tensorSpace B).bundle.trivialization (cc,cc)) ⟨f y,A (f y)⟩).2
  have hAf := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1
    f (fun q => (⟨q,A q⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
      (fun q => Fiber (TangentSpace S q) r s))) hf.1 hA
  have hac : VectorSmoothAt T.smoothStructure.val ac p :=
    FrameData.VectorSmoothAt.comp
      (g := fun y => (⟨f y,A (f y)⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
        (fun q => Fiber (TangentSpace S q) r s)))
      (tensorSpace B).bundle.totalManifold.smoothStructure.property.1.1
      (Frames.trivializationCoordinates_smoothAt (tensorSpace B).bundle (cc,cc)
        ⟨f p,A (f p)⟩ hfpB) (hAf p)
  let J (y : P) := FiniteRegularityData.chartDerivative e c f y
  let vc (y : P) : Euclidean (m^r*m^s) := fun q => ∑ j : Fin (n^r*n^s), ac y j *
    ((∏ l : Fin r, ContinuousLinearMap.inverse (J y)
      (Pi.single ((powerIndex n r).symm (finProdFinEquiv.symm j).1 l) 1)
        ((powerIndex m r).symm (finProdFinEquiv.symm q).1 l)) *
    ∏ l : Fin s, J y
      (Pi.single ((powerIndex m s).symm (finProdFinEquiv.symm q).2 l) 1)
        ((powerIndex n s).symm (finProdFinEquiv.symm j).2 l))
  have hJ := chartDerivative_smoothAt T S f hf.1 e c he hc p hp hfp
  have hJinv := inverse_chartDerivative_smoothAt T S f hf e c he hc p hp hfp
  have hvc : VectorSmoothAt T.smoothStructure.val vc p := by
    apply FrameData.VectorSmoothAt.pi
    intro q
    apply FrameData.VectorSmoothAt.sum
    intro j
    apply FrameData.VectorSmoothAt.postcomp
      ((hac.postcomp (ContinuousLinearMap.proj j).contDiff).prod ?_)
      (contDiff_fst.mul contDiff_snd)
    have hu := vectorSmoothAt_prod (κ := Fin r)
        (f := fun y l => ContinuousLinearMap.inverse (J y)
          (Pi.single ((powerIndex n r).symm (finProdFinEquiv.symm j).1 l) 1)
            ((powerIndex m r).symm (finProdFinEquiv.symm q).1 l))
        (fun l => (hJinv.clm_apply (FrameData.VectorSmoothAt.const _
          (Pi.single ((powerIndex n r).symm (finProdFinEquiv.symm j).1 l) 1) p)).postcomp
            (ContinuousLinearMap.proj ((powerIndex m r).symm (finProdFinEquiv.symm q).1 l)).contDiff)
    have hl := vectorSmoothAt_prod (κ := Fin s)
        (f := fun y l => J y
          (Pi.single ((powerIndex m s).symm (finProdFinEquiv.symm q).2 l) 1)
            ((powerIndex n s).symm (finProdFinEquiv.symm j).2 l))
        (fun l => (hJ.clm_apply (FrameData.VectorSmoothAt.const _
          (Pi.single ((powerIndex m s).symm (finProdFinEquiv.symm q).2 l) 1) p)).postcomp
            (ContinuousLinearMap.proj ((powerIndex n s).symm (finProdFinEquiv.symm j).2 l)).contDiff)
    exact (hu.prod hl).postcomp (contDiff_fst.mul contDiff_snd)
  apply Frames.smoothAt_from_trivialization (tensorSpace C).bundle T.smoothStructure.property.1
    (ec,ec) hpC ((manifoldContDiff_id (⊤ : ℕ∞) _ T.smoothStructure.property.1) p)
    hvc (fun _ => rfl)
  filter_upwards [e.open_source.mem_nhds hp,
    (hf.1 p).1.preimage_mem_nhds (c.open_source.mem_nhds hfp)] with y hye hyc
  change ((C.mixed.space.bundle.trivialization (ec,ec))
    ⟨y,mixedPullback S T f F A y⟩).2 = vc y
  rw [tensorBundle_diagonal_coordinates C ec y hye]
  ext q
  change mixedCoordinates (C.cotangent.tangent.fiberCoordinates.equiv e he y hye) r s
    (mixedTransport r s (F y) (A (f y))) q = vc y q
  have hcoeff := mixedTransport_coefficients (V := TangentSpace S (f y))
    (W := TangentSpace T y) (n := n) (m := m) (r := r) (s := s)
    (B.cotangent.tangent.fiberCoordinates.equiv c hc (f y) hyc)
    (C.cotangent.tangent.fiberCoordinates.equiv e he y hye) (F y) (A (f y)) q
  apply hcoeff.trans
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  · change _ = (((tensorSpace B).bundle.trivialization (cc,cc)) ⟨f y,A (f y)⟩).2 j
    change _ = ((B.mixed.space.bundle.trivialization (cc,cc)) ⟨f y,A (f y)⟩).2 j
    rw [tensorBundle_diagonal_coordinates B cc (f y) hyc]
  · congr 1
    · apply Finset.prod_congr rfl
      intro l _
      have hi := inverse_differential_coordinates S T f hf F hF
        B.cotangent.tangent.fiberCoordinates C.cotangent.tangent.fiberCoordinates
        c e hc he y hye hyc
        ((B.cotangent.tangent.fiberCoordinates.equiv c hc (f y) hyc).symm
          (Pi.single ((powerIndex n r).symm (finProdFinEquiv.symm j).1 l) 1))
      simpa only [LinearEquiv.apply_symm_apply] using
        (congrFun hi ((powerIndex m r).symm (finProdFinEquiv.symm q).1 l)).symm
    · apply Finset.prod_congr rfl
      intro l _
      have hforward := FiniteRegularity.smooth_jacobian_coordinateDerivative T S f hf.1 y
        (F y).toLinearMap (hF y) e c he hc hye hyc
        (C.cotangent.tangent.fiberCoordinates.equiv e he y hye)
        (B.cotangent.tangent.fiberCoordinates.equiv c hc (f y) hyc)
        (C.cotangent.tangent.fiberCoordinates.isCoordinates e he y hye)
        (B.cotangent.tangent.fiberCoordinates.isCoordinates c hc (f y) hyc)
        ((C.cotangent.tangent.fiberCoordinates.equiv e he y hye).symm
          (Pi.single ((powerIndex m s).symm (finProdFinEquiv.symm q).2 l) 1))
      simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        congrFun hforward ((powerIndex n s).symm (finProdFinEquiv.symm j).2 l)


end SmoothMixedOperations

section MixedAverages
open BundleData BundleOperationsData FrameData Set Filter
open scoped Topology
set_option maxRecDepth 10000

theorem permute_map {V : Type u} {W : Type v} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid W] [Module ℝ W] (L : V →ₗ[ℝ] W) (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (x : Power V k) :
    permute W k σ (PiTensorProduct.map (fun _ : Fin k => L) x) =
      PiTensorProduct.map (fun _ : Fin k => L) (permute V k σ x) := by
  exact (PiTensorProduct.map_reindex (fun _ : Fin k => L) σ x).symm

theorem symmetrize_map {V : Type u} {W : Type v} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid W] [Module ℝ W] (L : V →ₗ[ℝ] W) (k : ℕ) (x : Power V k) :
    symmetrize W k (PiTensorProduct.map (fun _ : Fin k => L) x) =
      PiTensorProduct.map (fun _ : Fin k => L) (symmetrize V k x) := by
  simp only [symmetrize, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, permute_map]

theorem alternate_map {V : Type u} {W : Type v} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid W] [Module ℝ W] (L : V →ₗ[ℝ] W) (k : ℕ) (x : Power V k) :
    alternate W k (PiTensorProduct.map (fun _ : Fin k => L) x) =
      PiTensorProduct.map (fun _ : Fin k => L) (alternate V k x) := by
  simp only [alternate, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, permute_map]

theorem tensorSpace_diagonal_coordinates_standard {n r s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)
    (c : TangentIndex S) (p : M) (hp : p ∈ c.val.source) (x : Fiber (TangentSpace S p) r s) :
    letI := (tensorSpace B).topology
    (((tensorSpace B).bundle.trivialization (c,c)) ⟨p,x⟩).2 =
      mixedCoordinates (B.cotangent.tangent.fiberCoordinates.equiv c.val c.property p hp) r s x :=
  tensorBundle_diagonal_coordinates B c p hp x

/-- Smoothness follows from a fixed linear coordinate expression in every
intrinsic tangent frame, even for different realizations of the tensor bundles. -/
theorem tensorMap_smooth_of_coordinates
    {n r s r' s' : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)
    (D : TensorData.TensorBundle S r' s')
    (A : (p : M) → Fiber (TangentSpace S p) r s →ₗ[ℝ] Fiber (TangentSpace S p) r' s')
    (C : Euclidean (n^r * n^s) →L[ℝ] Euclidean (n^r' * n^s'))
    (hC : ∀ (c : TangentIndex S) p (hp : p ∈ c.val.source) x,
      mixedCoordinates (B.cotangent.tangent.fiberCoordinates.equiv c.val c.property p hp) r' s'
        (A p x) = C (mixedCoordinates
          (B.cotangent.tangent.fiberCoordinates.equiv c.val c.property p hp) r s x)) :
    letI := (tensorSpace B).topology
    letI := (tensorSpace D).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace D).bundle.totalManifold
      (fun q => (⟨q.proj, A q.proj q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r' * n^s')) (fun p => Fiber (TangentSpace S p) r' s'))) := by
  letI := (tensorSpace B).topology
  letI := (tensorSpace D).topology
  intro q
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 q.proj
  let i : TangentIndex S := ⟨c,hc⟩
  have hiB : q.proj ∈ (tensorSpace B).bundle.baseSet (i,i) := by
    rw [tensorSpace_diagonal_baseSet]; exact hp
  have hiD : q.proj ∈ (tensorSpace D).bundle.baseSet (i,i) := by
    rw [tensorSpace_diagonal_baseSet]; exact hp
  have hv := (Frames.trivializationCoordinates_smoothAt (tensorSpace B).bundle (i,i) q hiB).postcomp C.contDiff
  apply Frames.smoothAt_from_trivialization (tensorSpace D).bundle
    (tensorSpace B).bundle.totalManifold.smoothStructure.property.1
    (f := fun y => ⟨y.proj, A y.proj y.snd⟩) (i,i) hiD
    ((tensorSpace B).bundle.projection_smooth q) hv (fun _ => rfl)
  filter_upwards [((tensorSpace B).bundle.projection_smooth q).1.preimage_mem_nhds
    (c.open_source.mem_nhds hp)] with y hy
  rw [tensorSpace_diagonal_coordinates_standard D i y.proj hy (A y.proj y.snd),
    tensorSpace_diagonal_coordinates_standard B i y.proj hy y.snd]
  have heq := TangentBundle.chartCoordinates_unique
    (D.cotangent.tangent.fiberCoordinates.isCoordinates c hc y.proj hy)
    (B.cotangent.tangent.fiberCoordinates.isCoordinates c hc y.proj hy)
  rw [heq]
  exact hC i y.proj hy y.snd

/-- Tensoring commuting maps preserves naturality. -/
theorem mixedPermute_natural {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    (r s : ℕ) (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)) (e : V ≃ₗ[ℝ] W) :
    (mixedPermute V r s σ τ).comp (mixedTransport r s e) =
      (mixedTransport r s e).comp (mixedPermute W r s σ τ) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply, mixedPermute, mixedTransport, TensorProduct.map_tmul,
    permute_map]

theorem mixedSymmetrizeUpper_natural {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    (r s : ℕ) (e : V ≃ₗ[ℝ] W) :
    (mixedSymmetrizeUpper V r s).comp (mixedTransport r s e) =
      (mixedTransport r s e).comp (mixedSymmetrizeUpper W r s) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply, mixedSymmetrizeUpper, mixedTransport, TensorProduct.map_tmul,
    LinearMap.id_apply, symmetrize_map]

theorem mixedAlternateUpper_natural {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    (r s : ℕ) (e : V ≃ₗ[ℝ] W) :
    (mixedAlternateUpper V r s).comp (mixedTransport r s e) =
      (mixedTransport r s e).comp (mixedAlternateUpper W r s) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply, mixedAlternateUpper, mixedTransport, TensorProduct.map_tmul,
    LinearMap.id_apply, alternate_map]

theorem mixedSymmetrizeLower_natural {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    (r s : ℕ) (e : V ≃ₗ[ℝ] W) :
    (mixedSymmetrizeLower V r s).comp (mixedTransport r s e) =
      (mixedTransport r s e).comp (mixedSymmetrizeLower W r s) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply, mixedSymmetrizeLower, mixedTransport, TensorProduct.map_tmul,
    LinearMap.id_apply, symmetrize_map]

theorem mixedAlternateLower_natural {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    (r s : ℕ) (e : V ≃ₗ[ℝ] W) :
    (mixedAlternateLower V r s).comp (mixedTransport r s e) =
      (mixedTransport r s e).comp (mixedAlternateLower W r s) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply, mixedAlternateLower, mixedTransport, TensorProduct.map_tmul,
    LinearMap.id_apply, alternate_map]

noncomputable def linearTensorOperationCoordinates (n r s r' s' : ℕ)
    (C : Fiber (Euclidean n) r s →ₗ[ℝ] Fiber (Euclidean n) r' s') :
    Euclidean (n^r * n^s) →ₗ[ℝ] Euclidean (n^r' * n^s') :=
  (mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r' s').toLinearMap ∘ₗ C ∘ₗ
    (mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s).symm.toLinearMap

theorem mixedCoordinates_of_natural {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {n r s r' s' : ℕ} (e : V ≃ₗ[ℝ] Euclidean n)
    (A : Fiber V r s →ₗ[ℝ] Fiber V r' s')
    (C : Fiber (Euclidean n) r s →ₗ[ℝ] Fiber (Euclidean n) r' s')
    (h : C.comp (mixedTransport r s e.symm) = (mixedTransport r' s' e.symm).comp A)
    (x : Fiber V r s) :
    mixedCoordinates e r' s' (A x) =
      linearTensorOperationCoordinates n r s r' s' C (mixedCoordinates e r s x) := by
  have h₁ := LinearMap.congr_fun (mixedCoordinates_transport e r s) x
  have h₂ := LinearMap.congr_fun (mixedCoordinates_transport e r' s') (A x)
  have h₃ := LinearMap.congr_fun h x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h₁ h₂ h₃
  rw [← h₁, ← h₂]
  simp only [linearTensorOperationCoordinates, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, h₃]

theorem mixedPermute_smooth {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s) (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)) :
    letI := (tensorSpace B).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedPermute (TangentSpace S q.proj) r s σ τ q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r * n^s)) (fun p => Fiber (TangentSpace S p) r s))) := by
  apply tensorMap_smooth_of_coordinates B B
    (fun p => mixedPermute (TangentSpace S p) r s σ τ)
    (linearTensorOperationCoordinates n r s r s (mixedPermute (Euclidean n) r s σ τ)).toContinuousLinearMap
  intro c p hp x
  exact mixedCoordinates_of_natural _ _ _
    (mixedPermute_natural r s σ τ _) x

theorem mixedSymmetrizeUpper_smooth {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)  :
    letI := (tensorSpace B).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedSymmetrizeUpper (TangentSpace S q.proj) r s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r * n^s)) (fun p => Fiber (TangentSpace S p) r s))) := by
  apply tensorMap_smooth_of_coordinates B B
    (fun p => mixedSymmetrizeUpper (TangentSpace S p) r s)
    (linearTensorOperationCoordinates n r s r s (mixedSymmetrizeUpper (Euclidean n) r s)).toContinuousLinearMap
  intro c p hp x
  exact mixedCoordinates_of_natural _ _ _
    (mixedSymmetrizeUpper_natural r s _) x

theorem mixedAlternateUpper_smooth {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)  :
    letI := (tensorSpace B).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedAlternateUpper (TangentSpace S q.proj) r s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r * n^s)) (fun p => Fiber (TangentSpace S p) r s))) := by
  apply tensorMap_smooth_of_coordinates B B
    (fun p => mixedAlternateUpper (TangentSpace S p) r s)
    (linearTensorOperationCoordinates n r s r s (mixedAlternateUpper (Euclidean n) r s)).toContinuousLinearMap
  intro c p hp x
  exact mixedCoordinates_of_natural _ _ _
    (mixedAlternateUpper_natural r s _) x

theorem mixedSymmetrizeLower_smooth {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)  :
    letI := (tensorSpace B).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedSymmetrizeLower (TangentSpace S q.proj) r s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r * n^s)) (fun p => Fiber (TangentSpace S p) r s))) := by
  apply tensorMap_smooth_of_coordinates B B
    (fun p => mixedSymmetrizeLower (TangentSpace S p) r s)
    (linearTensorOperationCoordinates n r s r s (mixedSymmetrizeLower (Euclidean n) r s)).toContinuousLinearMap
  intro c p hp x
  exact mixedCoordinates_of_natural _ _ _
    (mixedSymmetrizeLower_natural r s _) x

theorem mixedAlternateLower_smooth {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TensorData.TensorBundle S r s)  :
    letI := (tensorSpace B).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, mixedAlternateLower (TangentSpace S q.proj) r s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^r * n^s)) (fun p => Fiber (TangentSpace S p) r s))) := by
  apply tensorMap_smooth_of_coordinates B B
    (fun p => mixedAlternateLower (TangentSpace S p) r s)
    (linearTensorOperationCoordinates n r s r s (mixedAlternateLower (Euclidean n) r s)).toContinuousLinearMap
  intro c p hp x
  exact mixedCoordinates_of_natural _ _ _
    (mixedAlternateLower_natural r s _) x


end MixedAverages

section CovariantUnitAlgebra
open Set Filter
@[simp] theorem covariantEquiv_pure {V : Type u} [AddCommMonoid V] [Module ℝ V] (s : ℕ) (v : Fin 0 → V)
    (lam : Fin s → Module.Dual ℝ V) :
    covariantEquiv V s (TensorData.pure v lam) = PiTensorProduct.tprod ℝ lam := by
  simp [covariantEquiv, TensorData.pure]

theorem evaluate_covariantEquiv {V : Type u} [AddCommMonoid V] [Module ℝ V] (s : ℕ) (A : Fiber V 0 s) (w : Fin s → V) :
    evaluate V 0 s A (Sum.rec Fin.elim0 w) =
      covariantEvaluate V s (covariantEquiv V s A) w := by
  induction A using TensorProduct.induction_on with
  | zero => simp only [map_zero, MultilinearMap.zero_apply]
  | add A B hA hB => simp only [map_add, MultilinearMap.add_apply, hA, hB]
  | tmul A B =>
    induction A using PiTensorProduct.induction_on with
    | add A C hA hC => simp only [TensorProduct.add_tmul, map_add, MultilinearMap.add_apply, hA, hC]
    | smul_tprod c v =>
      induction B using PiTensorProduct.induction_on with
      | add B C hB hC => simp only [TensorProduct.tmul_add, map_add, MultilinearMap.add_apply, hB, hC]
      | smul_tprod d lam =>
        simp only [TensorProduct.smul_tmul_smul, map_smul,
          MultilinearMap.smul_apply]
        change (c*d) • evaluate V 0 s (TensorData.pure v lam) (Sum.rec Fin.elim0 w) =
          (c*d) • covariantEvaluate V s (covariantEquiv V s (TensorData.pure v lam)) w
        simp only [evaluate_pure, covariantEquiv_pure, covariantEvaluate_pure,
          Finset.univ_eq_empty, Finset.prod_empty, one_mul]

theorem covariantEquiv_mixedTransport {V : Type u} {W : Type v}
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W] (s : ℕ) (e : V ≃ₗ[ℝ] W) :
    (covariantEquiv V s).toLinearMap.comp (mixedTransport 0 s e) =
      (covariantTransport s e.toLinearMap).comp (covariantEquiv W s).toLinearMap := by
  ext v lam
  change covariantEquiv V s (mixedTransport 0 s e (TensorData.pure v lam)) =
    covariantTransport s e.toLinearMap (covariantEquiv W s (TensorData.pure v lam))
  rw [mixedTransport_pure, covariantEquiv_pure, covariantEquiv_pure, covariantTransport_pure]


end CovariantUnitAlgebra

section CovariantUnitSmoothness
open BundleData BundleOperationsData FrameData CovectorData Set Filter
open scoped Topology

-- Tested in /tmp/CovariantBridge.lean. Requires definitions in research/covariant-bridge-definitions.txt.
set_option maxRecDepth 10000
noncomputable def covariantCoordinateProjection (d s : ℕ) :
    Euclidean (d^0*d^s) →ₗ[ℝ] Euclidean (d^s) where
  toFun x j := x (finProdFinEquiv (⟨0, by simp⟩,j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def covariantCoordinateInclusion (d s : ℕ) :
    Euclidean (d^s) →ₗ[ℝ] Euclidean (d^0*d^s) where
  toFun x j := x (finProdFinEquiv.symm j).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem covariantCoordinateProjection_inclusion (d s : ℕ) (x : Euclidean (d^s)) :
    covariantCoordinateProjection d s (covariantCoordinateInclusion d s x) = x := by
  ext j
  change x (finProdFinEquiv.symm (finProdFinEquiv (⟨0, by simp⟩,j))).2 = x j
  rw [Equiv.symm_apply_apply]

@[simp] theorem covariantCoordinateInclusion_projection (d s : ℕ) (x : Euclidean (d^0*d^s)) :
    covariantCoordinateInclusion d s (covariantCoordinateProjection d s x) = x := by
  letI : Subsingleton (Fin (d^0)) := by simpa using (inferInstance : Subsingleton (Fin 1))
  ext j
  change x (finProdFinEquiv (⟨0, by simp⟩,(finProdFinEquiv.symm j).2)) = x j
  have hpair : (⟨0, by simp⟩,(finProdFinEquiv.symm j).2) = finProdFinEquiv.symm j :=
    Prod.ext (Subsingleton.elim _ _) rfl
  rw [hpair, Equiv.apply_symm_apply]

@[simp] theorem covariantEquiv_tprod_tmul {V : Type u} [AddCommMonoid V] [Module ℝ V]
    (s : ℕ) (v : Fin 0 → V) (x : Power (Module.Dual ℝ V) s) :
    covariantEquiv V s ((PiTensorProduct.tprod ℝ v) ⊗ₜ[ℝ] x) = x := by
  simp [covariantEquiv]

theorem mixedCoordinates_covariantEquiv {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (s : ℕ) (x : Fiber V 0 s) :
    letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℝ
    powerCoordinates (BundleOperations.dualCoordinates e) s (covariantEquiv V s x) =
      covariantCoordinateProjection d s (mixedCoordinates e 0 s x) := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℝ
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      simp only [← TensorProduct.smul_tmul', map_smul]
      congr 1
      ext j
      change powerCoordinates (BundleOperations.dualCoordinates e) s
          (covariantEquiv V s ((PiTensorProduct.tprod ℝ v) ⊗ₜ[ℝ] y)) j =
        BundleOperations.tensorCoordinates (powerCoordinates e 0)
          (powerCoordinates (BundleOperations.dualCoordinates e) s)
            ((PiTensorProduct.tprod ℝ v) ⊗ₜ[ℝ] y) (finProdFinEquiv (⟨0, by simp⟩,j))
      rw [covariantEquiv_tprod_tmul, BundleOperations.tensorCoordinates_tmul]
      letI : Subsingleton (Fin (d^0)) := by simpa using (inferInstance : Subsingleton (Fin 1))
      rw [show (⟨0, by simp⟩ : Fin (d^0)) = powerIndex d 0 Fin.elim0 from Subsingleton.elim _ _,
        powerCoordinates_tprod]
      simp
    | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mixedCoordinates_covariantEquiv_symm {V : Type u} [AddCommMonoid V] [Module ℝ V]
    {d : ℕ} (e : V ≃ₗ[ℝ] Euclidean d) (s : ℕ) (x : Power (Module.Dual ℝ V) s) :
    letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℝ
    mixedCoordinates e 0 s ((covariantEquiv V s).symm x) =
      covariantCoordinateInclusion d s (powerCoordinates (BundleOperations.dualCoordinates e) s x) := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℝ
  have h := mixedCoordinates_covariantEquiv e s ((covariantEquiv V s).symm x)
  simp only [LinearEquiv.apply_symm_apply] at h
  rw [h, covariantCoordinateInclusion_projection]



theorem covariantSpace_baseSet {n s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S 0 s)
    (c : TangentIndex S) :
    letI := (covariantSpace B).topology
    (covariantSpace B).bundle.baseSet c = c.val.source := by
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  letI := B.lower.space.topology
  change B.lower.space.bundle.baseSet c = _
  rw [B.lower.baseSet, B.cotangent.dual.baseSet, B.cotangent.realization.baseSet]

theorem covariantSpace_coordinates {n s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S 0 s)
    (c : TangentIndex S) (p : M) (hp : p ∈ c.val.source)
    (x : Power (Module.Dual ℝ (TangentSpace S p)) s) :
    letI : AddCommGroup (TangentSpace S p) := Module.addCommMonoidToAddCommGroup ℝ
    letI := (covariantSpace B).topology
    (((covariantSpace B).bundle.trivialization c) ⟨p,x⟩).2 =
      powerCoordinates
        (BundleOperations.dualCoordinates
          (B.cotangent.tangent.fiberCoordinates.equiv c.val c.property p hp)) s x := by
  letI : AddCommGroup (TangentSpace S p) := Module.addCommMonoidToAddCommGroup ℝ
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  letI := B.lower.space.topology
  let e := B.cotangent.tangent.fiberCoordinates.equiv c.val c.property p hp
  have hpR : p ∈ B.cotangent.realization.space.bundle.baseSet c := by
    rw [B.cotangent.realization.baseSet]; exact hp
  have hpD : p ∈ B.cotangent.dual.space.bundle.baseSet c := by
    rw [B.cotangent.dual.baseSet]; exact hpR
  have he : B.cotangent.realization.space.bundle.fiberCoordinates c p hpR = e := by
    apply LinearEquiv.ext
    intro v
    exact B.cotangent.realization.coordinates c p hp v
  have hdual : B.cotangent.dual.space.bundle.fiberCoordinates c p hpD =
      BundleOperations.dualCoordinates e := by
    ext lam j
    rw [SmoothVectorBundle.fiberCoordinates_apply,
      dualBundle_coordinates B.cotangent.realization.space.bundle B.cotangent.dual c p hpR, he]
    rfl
  change ((B.lower.space.bundle.trivialization c) ⟨p,x⟩).2 = _
  rw [powerBundle_coordinates B.cotangent.dual.space.bundle B.lower c p hpD, hdual]


theorem covariantEquiv_bundle_smooth {n s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S 0 s) :
    letI := (tensorSpace B).topology
    letI := (covariantSpace B).topology
    IsSmoothMap (tensorSpace B).bundle.totalManifold (covariantSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, covariantEquiv (TangentSpace S q.proj) s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace S p)) s))) := by
  letI := (tensorSpace B).topology
  letI := (covariantSpace B).topology
  intro q
  obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 q.proj
  let i : TangentIndex S := ⟨c,hc⟩
  have hT : q.proj ∈ (tensorSpace B).bundle.baseSet (i,i) := by
    rw [tensorSpace_diagonal_baseSet]; exact hp
  have hL : q.proj ∈ (covariantSpace B).bundle.baseSet i := by
    rw [covariantSpace_baseSet]; exact hp
  have hcoord := Frames.trivializationCoordinates_smoothAt (tensorSpace B).bundle (i,i) q hT
  refine Frames.smoothAt_from_trivialization (covariantSpace B).bundle
    (tensorSpace B).bundle.totalManifold.smoothStructure.property.1 i hL
    ((tensorSpace B).bundle.projection_smooth q)
    (hcoord.postcomp (covariantCoordinateProjection n s).toContinuousLinearMap.contDiff)
    (fun _ => rfl) ?_
  filter_upwards [((tensorSpace B).bundle.projection_smooth q).1.preimage_mem_nhds
    (c.open_source.mem_nhds hp)] with y hy
  let e := B.cotangent.tangent.fiberCoordinates.equiv c hc y.proj hy
  have he : IsChartCoordinates S y.proj c e :=
    B.cotangent.tangent.fiberCoordinates.isCoordinates c hc y.proj hy
  have hTc := tensorSpace_diagonal_coordinates B i y.proj hy e he y.snd
  have hLc := covariantSpace_coordinates B i y.proj hy
    (covariantEquiv (TangentSpace S y.proj) s y.snd)
  change (((covariantSpace B).bundle.trivialization i)
    ⟨y.proj,covariantEquiv (TangentSpace S y.proj) s y.snd⟩).2 =
      covariantCoordinateProjection n s (((tensorSpace B).bundle.trivialization (i,i)) y).2
  rw [hTc, hLc]
  exact mixedCoordinates_covariantEquiv e s y.snd

theorem covariantEquiv_symm_bundle_smooth {n s : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TensorData.TensorBundle S 0 s) :
    letI := (tensorSpace B).topology
    letI := (covariantSpace B).topology
    IsSmoothMap (covariantSpace B).bundle.totalManifold (tensorSpace B).bundle.totalManifold
      (fun q => (⟨q.proj, (covariantEquiv (TangentSpace S q.proj) s).symm q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^0*n^s))
          (fun p => Fiber (TangentSpace S p) 0 s))) := by
  letI := (tensorSpace B).topology
  letI := (covariantSpace B).topology
  intro q
  obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 q.proj
  let i : TangentIndex S := ⟨c,hc⟩
  have hT : q.proj ∈ (tensorSpace B).bundle.baseSet (i,i) := by
    rw [tensorSpace_diagonal_baseSet]; exact hp
  have hL : q.proj ∈ (covariantSpace B).bundle.baseSet i := by
    rw [covariantSpace_baseSet]; exact hp
  have hcoord := Frames.trivializationCoordinates_smoothAt (covariantSpace B).bundle i q hL
  refine Frames.smoothAt_from_trivialization (tensorSpace B).bundle
    (covariantSpace B).bundle.totalManifold.smoothStructure.property.1 (i,i) hT
    ((covariantSpace B).bundle.projection_smooth q)
    (hcoord.postcomp (covariantCoordinateInclusion n s).toContinuousLinearMap.contDiff)
    (fun _ => rfl) ?_
  filter_upwards [((covariantSpace B).bundle.projection_smooth q).1.preimage_mem_nhds
    (c.open_source.mem_nhds hp)] with y hy
  let e := B.cotangent.tangent.fiberCoordinates.equiv c hc y.proj hy
  have he : IsChartCoordinates S y.proj c e :=
    B.cotangent.tangent.fiberCoordinates.isCoordinates c hc y.proj hy
  have hTc := tensorSpace_diagonal_coordinates B i y.proj hy e he
    ((covariantEquiv (TangentSpace S y.proj) s).symm y.snd)
  have hLc := covariantSpace_coordinates B i y.proj hy y.snd
  change (((tensorSpace B).bundle.trivialization (i,i))
    ⟨y.proj,(covariantEquiv (TangentSpace S y.proj) s).symm y.snd⟩).2 =
      covariantCoordinateInclusion n s (((covariantSpace B).bundle.trivialization i) y).2
  rw [hTc, hLc]
  exact mixedCoordinates_covariantEquiv_symm e s y.snd


theorem covariantTensorPullback_smooth
    {n m s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (B : TensorData.TensorBundle S 0 s) (C : TensorData.TensorBundle T 0 s)
    (f : P → M) (hf : IsSmoothMap T S f)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (hL : ∀ p, IsDifferential T S f p (L p))
    (A : Field S 0 s) (hA : IsSmoothField B A) :
    IsSmoothField C (covariantTensorPullback S T f L A) := by
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  letI := C.cotangent.realization.space.topology
  letI := C.cotangent.dual.space.topology
  letI := (tensorSpace B).topology
  letI := (covariantSpace B).topology
  letI := (tensorSpace C).topology
  letI := (covariantSpace C).topology
  have hAf : IsSmoothMap S (covariantSpace B).bundle.totalManifold
      (fun p => (⟨p,covariantEquiv (TangentSpace S p) s (A p)⟩ :
        Bundle.TotalSpace (Euclidean (n^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace S p)) s))) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
      (tensorSpace B).bundle.totalManifold.smoothStructure.property.1.1
      (fun p => (⟨p,A p⟩ : Bundle.TotalSpace (Euclidean (n^0*n^s))
        (fun p => Fiber (TangentSpace S p) 0 s)))
      (fun q => (⟨q.proj,covariantEquiv (TangentSpace S q.proj) s q.snd⟩ :
        Bundle.TotalSpace (Euclidean (n^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace S p)) s)))
      hA (covariantEquiv_bundle_smooth B)
  have hpb : IsSmoothMap T (covariantSpace C).bundle.totalManifold
      (fun p => (⟨p,covariantPullback S T f L
        (fun q => covariantEquiv (TangentSpace S q) s (A q)) p⟩ :
        Bundle.TotalSpace (Euclidean (m^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace T p)) s))) :=
    covariant_pullback_smooth S T B.cotangent C.cotangent s B.lower C.lower f hf L hL _ hAf
  exact manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    (covariantSpace C).bundle.totalManifold.smoothStructure.property.1.1
    (fun p => (⟨p,covariantPullback S T f L
      (fun q => covariantEquiv (TangentSpace S q) s (A q)) p⟩ :
        Bundle.TotalSpace (Euclidean (m^s))
          (fun p => Power (Module.Dual ℝ (TangentSpace T p)) s)))
    (fun q => (⟨q.proj,(covariantEquiv (TangentSpace T q.proj) s).symm q.snd⟩ :
      Bundle.TotalSpace (Euclidean (m^0*m^s)) (fun p => Fiber (TangentSpace T p) 0 s)))
    hpb (covariantEquiv_symm_bundle_smooth C)



theorem covariantTensorPullback_apply
    {n m s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (A : Field S 0 s) (p : P) (v : Fin s → TangentSpace T p) :
    evaluate (TangentSpace T p) 0 s (covariantTensorPullback S T f L A p)
      (Sum.rec Fin.elim0 v) =
    evaluate (TangentSpace S (f p)) 0 s (A (f p))
      (Sum.rec Fin.elim0 (fun i => L p (v i))) := by
  rw [evaluate_covariantEquiv, evaluate_covariantEquiv]
  simp only [covariantTensorPullback, LinearEquiv.apply_symm_apply]
  exact covariant_pullback_apply S T f L s
    (fun q => covariantEquiv (TangentSpace S q) s (A q)) p v

theorem covariantTensorPullback_id
    {n s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p)
    (hL : ∀ p, IsDifferential S S id p (L p)) (A : Field S 0 s) :
    covariantTensorPullback S S id L A = A := by
  have h := covariant_pullback_id S s L hL (fun p => covariantEquiv (TangentSpace S p) s (A p))
  funext p
  apply (covariantEquiv (TangentSpace S p) s).injective
  simpa only [covariantTensorPullback, LinearEquiv.apply_symm_apply] using congrFun h p

theorem covariantTensorPullback_comp
    {n m k s : ℕ} {a b c : ModelKind} {M P Q : Type u}
    [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (U : SmoothManifold k c Q)
    (f : P → M) (g : Q → P) (hf : IsSmoothMap T S f) (hg : IsSmoothMap U T g)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (K : (q : Q) → TangentSpace U q →ₗ[ℝ] TangentSpace T (g q))
    (H : (q : Q) → TangentSpace U q →ₗ[ℝ] TangentSpace S (f (g q)))
    (hL : ∀ p, IsDifferential T S f p (L p))
    (hK : ∀ q, IsDifferential U T g q (K q))
    (hH : ∀ q, IsDifferential U S (f ∘ g) q (H q)) (A : Field S 0 s) :
    covariantTensorPullback S U (f ∘ g) H A =
      covariantTensorPullback T U g K (covariantTensorPullback S T f L A) := by
  have h := covariant_pullback_comp S T U f g hf hg s L K H hL hK hH
    (fun p => covariantEquiv (TangentSpace S p) s (A p))
  funext q
  apply (covariantEquiv (TangentSpace U q) s).injective
  simpa only [covariantTensorPullback, covariantPullback, LinearEquiv.apply_symm_apply]
    using congrFun h q

theorem covariantTensorPullback_mixed
    {n m s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (e : (p : P) → TangentSpace T p ≃ₗ[ℝ] TangentSpace S (f p)) (A : Field S 0 s) :
    covariantTensorPullback S T f (fun p => (e p).toLinearMap) A = mixedPullback S T f e A := by
  funext p
  apply (covariantEquiv (TangentSpace T p) s).injective
  simp only [covariantTensorPullback, covariantPullback, LinearEquiv.apply_symm_apply, mixedPullback]
  exact (LinearMap.congr_fun (covariantEquiv_mixedTransport s (e p)) (A (f p))).symm

theorem covariantTensorPullback_exists
    {n m s : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (B : TensorData.TensorBundle S 0 s) (C : TensorData.TensorBundle T 0 s)
    (f : P → M) (hf : IsSmoothMap T S f) :
    ∃ L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p),
      (∀ p, IsDifferential T S f p (L p)) ∧
      ∀ A : Field S 0 s, IsSmoothField B A → IsSmoothField C (covariantTensorPullback S T f L A) := by
  exact ⟨SmoothManifolds.differential T S f hf,
    SmoothManifolds.differential_spec T S f hf,
    fun A hA => covariantTensorPullback_smooth S T B C f hf _
      (SmoothManifolds.differential_spec T S f hf) A hA⟩

end CovariantUnitSmoothness

section FurtherResults
open BundleData

theorem contraction_evaluation :
    Specs.SmoothManifolds.Ch05.Tensors.contraction_evaluationType.{u} := by
  intro V _ _ r s i j v lam
  exact contract_pure i j v lam

theorem tensor_product_evaluation :
    Specs.SmoothManifolds.Ch05.Tensors.tensor_product_evaluationType.{u} := by
  intro V _ _ r s r' s' v lam w mu
  exact tensorMultiply_pure r s r' s' v lam w mu

theorem mixed_transport_naturality :
    Specs.SmoothManifolds.Ch05.Tensors.mixed_transport_naturalityType.{u} := by
  intro V W _ _ _ _ e
  constructor
  · intro r s i j A
    exact LinearMap.congr_fun (contract_natural i j e) A
  · intro r s r' s' A B
    exact tensorMultiply_natural r s r' s' e A B

theorem local_diffeomorphism_differential :
    Specs.SmoothManifolds.Ch05.Tensors.local_diffeomorphism_differentialType.{u} := by
  intro n m a b M N _ _ S T f hf
  exact ⟨localDiffeomorphismDifferential S T f hf,
    localDiffeomorphismDifferential_spec S T f hf⟩

theorem power_operations_smooth :
    Specs.SmoothManifolds.Ch05.Tensors.power_operations_smoothType.{u} := by
  intro n d a M _ S ι E _ _ _ B k P
  exact ⟨power_permute_smooth B P, power_symmetrize_smooth B P, power_alternate_smooth B P⟩

theorem exists_tensorPullbackBundle :
    Specs.SmoothManifolds.Ch05.Tensors.exists_tensorPullbackBundleType.{u} := by
  intro n m a b M P _ _ S T f hf r s B
  letI := B.cotangent.realization.space.topology
  letI := B.cotangent.dual.space.topology
  letI := B.upper.space.topology
  letI := B.lower.space.topology
  letI := B.mixed.space.topology
  exact BundleOperations.exists_pullback B.mixed.space.bundle T f hf


theorem mixed_operations_smooth :
    Specs.SmoothManifolds.Ch05.Tensors.mixed_operations_smoothType.{u} := by
  intro n r s a M _ S B
  exact ⟨mixedPermute_smooth B, mixedSymmetrizeUpper_smooth B, mixedAlternateUpper_smooth B,
    mixedSymmetrizeLower_smooth B, mixedAlternateLower_smooth B⟩

theorem mixed_pullback_exists :
    Specs.SmoothManifolds.Ch05.Tensors.mixed_pullback_existsType.{u} := by
  intro n m r s a b M P _ _ S T B C f hf
  refine ⟨localDiffeomorphismDifferential T S f hf,
    localDiffeomorphismDifferential_spec T S f hf, ?_⟩
  intro A hA
  exact mixed_pullback_smooth S T B C f hf _
    (localDiffeomorphismDifferential_spec T S f hf) A hA

end FurtherResults

end SmoothManifolds.Tensors
