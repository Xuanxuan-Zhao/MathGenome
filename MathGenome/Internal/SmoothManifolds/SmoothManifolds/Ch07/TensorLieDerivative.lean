import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.TensorLieDerivative
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Tensors
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.BracketFromFlow
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Tensor Lie derivatives in all variances, including smooth boundary extension
for arbitrary fields and actual-flow identification for boundary-tangent fields.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace SmoothManifolds.TensorLieDerivative
open ModelData AtlasData MapData PartitionData TangentData TangentBundleData VectorFieldData
  LieBracketData BracketFlowData TensorLieData FiniteRegularityData
open Set Filter
open scoped Topology
universe u

/-- Chain rule along an actual integral curve. Only the defining curve equation
is used, so this also handles a curve through a boundary point without imposing
an unnecessary tangency hypothesis on an unrelated field. -/
theorem scalar_derivative_on_curve
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) (D : RealDerivation S) (hD : Represents X D)
    (I : Set ℝ) (γ : ℝ → M) (hI : IsOpen I)
    (hγ : BoundaryFlowData.IsIntegralCurveOn X I γ)
    (f : GlobalSmooth S) (t : ℝ) (ht : t ∈ I) :
    HasDerivAt (fun s => f.val (γ s)) ((D f).val (γ t)) t := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (γ t)
  obtain ⟨U, hU, hpU, F, hF, hEq⟩ :=
    ((scalarContDiffAt_iff _ _ _ _).mp
      ((mem_globalSmoothAlgebra_iff S _).mp f.property (γ t))).2 e he hp
  have hc : ContinuousAt γ t := hγ.1.continuousAt (hI.mem_nhds ht)
  have hFt : DifferentiableAt ℝ F (e (γ t)).val :=
    (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hd := hFt.hasFDerivAt.comp_hasDerivAt t (hγ.2 t ht e he hp).2
  have hv : (D f).val (γ t) = fderiv ℝ F (e (γ t)).val
      (B.fiberCoordinates.equiv e he (γ t) hp (X.val (γ t))) := by
    rw [hD (γ t) f (globalToGerm S (γ t) f) rfl]
    exact VectorFields.tangent_action_coordinates S B.fiberCoordinates (γ t)
      e he hp (X.val (γ t)) (globalToGerm S (γ t) f) F
      ⟨⟨U, hU, hpU, hF⟩, Germ.coe_eq.mpr hEq⟩
  rw [hv]
  exact hd.congr_of_eventuallyEq (hEq.symm.comp_tendsto hc)

/-- Differentiate evaluation of a moving covariant multilinear form on
moving arguments. This analytic helper is used with the intrinsic
tensor-to-coordinate bridge below. -/
theorem evaluation_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
    (A : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin s => V) ℝ)
    (A' : ContinuousMultilinearMap ℝ (fun _ : Fin s => V) ℝ)
    (Y : Fin s → ℝ → V) (Y' : Fin s → V) (t : ℝ)
    (hA : HasDerivAt A A' t) (hY : ∀ i, HasDerivAt (Y i) (Y' i) t) :
    HasDerivAt (fun z => A z (fun i => Y i z))
      (A' (fun i => Y i t) +
        ∑ i : Fin s, A t (Function.update (fun j => Y j t) i (Y' i))) t := by
  classical
  convert (hA.hasFDerivAt.continuousMultilinearMap_apply
    (fun i => (hY i).hasFDerivAt)).hasDerivAt using 1; simp

/-- Solving the differentiated evaluation identity for the tensor derivative
is exactly the minus-sum formula in M07.06. In a flow application the moving
arguments are the pulled-back fields, whose derivatives are their brackets. -/
theorem evaluation_derivative_formula
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
    (A : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin s => V) ℝ)
    (A' : ContinuousMultilinearMap ℝ (fun _ : Fin s => V) ℝ)
    (Y : Fin s → ℝ → V) (Y' : Fin s → V) (t : ℝ)
    (hA : HasDerivAt A A' t) (hY : ∀ i, HasDerivAt (Y i) (Y' i) t)
    (g : ℝ → ℝ) (g' : ℝ)
    (hg : HasDerivAt g g' t)
    (heq : g =ᶠ[𝓝 t] (fun z => A z (fun i => Y i z))) :
    A' (fun i => Y i t) = g' -
      ∑ i : Fin s, A t (Function.update (fun j => Y j t) i (Y' i)) := by
  have hd := (evaluation_hasDerivAt A A' Y Y' t hA hY).congr_of_eventuallyEq heq
  have h := hd.unique hg
  linarith

/-- The scalar evaluation rule for covariant tensors in a local vector-space
model, with the coordinate commutator DY·X - DX·Y. No antisymmetry, connection,
or positive-arity assumption is used. The remaining global bridge must identify
these multilinear coordinate maps with the actual tensor sections. -/
theorem covariant_coordinate_evaluation_formula
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
    (X : V → V)
    (A : V → ContinuousMultilinearMap ℝ (fun _ : Fin s => V) ℝ)
    (Y : Fin s → V → V) (z : V)
    (hA : DifferentiableAt ℝ A z) (hY : ∀ i, DifferentiableAt ℝ (Y i) z) :
    (fderiv ℝ A z (X z)) (fun i => Y i z) +
        (∑ i : Fin s, A z (Function.update (fun j => Y j z) i (fderiv ℝ X z (Y i z)))) =
      fderiv ℝ (fun w => A w (fun i => Y i w)) z (X z) -
        ∑ i : Fin s, A z (Function.update (fun j => Y j z) i
          (fderiv ℝ (Y i) z (X z) - fderiv ℝ X z (Y i z))) := by
  classical
  have hd := congrArg (fun L => L (X z))
    (hA.hasFDerivAt.continuousMultilinearMap_apply
      (fun i => (hY i).hasFDerivAt)).fderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    sum_apply] at hd
  have hv : fderiv ℝ (fun w => A w (fun i => Y i w)) z (X z) =
      (fderiv ℝ A z (X z)) (fun i => Y i z) +
        ∑ i : Fin s, A z (Function.update (fun j => Y j z) i (fderiv ℝ (Y i) z (X z))) := by
    simpa using hd
  rw [hv]
  simp only [ContinuousMultilinearMap.map_update_sub, Finset.sum_sub_distrib]
  ring

/-- Every ambient coefficient in the mixed Lie formula is smooth. In
particular there is no boundary tangency requirement in this computation. -/
theorem arrayLie_smooth (n r s : ℕ) (U : Set (Euclidean n)) (hU : IsOpen U)
    (X : Euclidean n → Euclidean n)
    (A : Euclidean n → (Fin r → Fin n) → (Fin s → Fin n) → ℝ)
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X U)
    (hA : ∀ I J, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => A z I J) U)
    (I : Fin r → Fin n) (J : Fin s → Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => arrayLie n r s X A z I J) U := by
  classical
  have hDX : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ X) U :=
    hX.fderiv_of_isOpen hU (by simp)
  have hDA : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun z => A z I J)) U :=
    (hA I J).fderiv_of_isOpen hU (by simp)
  unfold arrayLie
  apply ContDiffOn.add
  · apply ContDiffOn.sub
    · exact hDA.clm_apply hX
    · apply ContDiffOn.sum
      intro i _
      apply ContDiffOn.sum
      intro k _
      exact ((contDiff_apply ℝ (fun _ : Fin n => ℝ) (I i)).contDiffOn.comp
        (hDX.clm_apply contDiffOn_const) (mapsTo_univ _ _)).mul (hA _ _)
  · apply ContDiffOn.sum
    intro j _
    apply ContDiffOn.sum
    intro k _
    exact ((contDiff_apply ℝ (fun _ : Fin n => ℝ) k).contDiffOn.comp
      (hDX.clm_apply contDiffOn_const) (mapsTo_univ _ _)).mul (hA _ _)

/-- The basis test concerns the source's tensor fiber, rather than a replacement
array type. Its only pending mathematical input is the full frozen multilinear
interpretation theorem, not an assumed special-case isomorphism. -/
theorem component_ext_of_fiber_interpretation
    (hfi : Specs.SmoothManifolds.Ch05.Tensors.fiber_interpretationType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (r s : ℕ)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (A C : TensorData.Fiber (TangentSpace S p) r s)
    (h : ∀ I J, component B r s e he p I J A = component B r s e he p I J C) :
    A = C := by
  classical
  let c := B.fiberCoordinates.equiv e he p hp
  let b : Module.Basis (Fin n) ℝ (TangentSpace S p) := (Pi.basisFun ℝ (Fin n)).map c.symm
  have hdual (i : Fin n) : b.dualBasis i = (LinearMap.proj i).comp c.toLinearMap := by
    ext v
    simp [b, Module.Basis.map_repr, Pi.basisFun_repr]
  let ba : (i : Fin r ⊕ Fin s) → Module.Basis (Fin n) ℝ (TensorData.Argument (TangentSpace S p) r s i) :=
    Sum.rec (fun _ => b.dualBasis) (fun _ => b)
  apply (hfi S p r s).1
  apply Module.Basis.ext_multilinear ba
  intro v
  have hh := h (fun i => v (.inl i)) (fun j => v (.inr j))
  simp only [component, dite_eq_left hp, LinearMap.coe_mk, AddHom.coe_mk] at hh
  change TensorData.evaluate (TangentSpace S p) r s A
      (Sum.rec (fun i => (LinearMap.proj (v (.inl i))).comp c.toLinearMap)
        (fun j => c.symm (Pi.single (v (.inr j)) 1))) =
    TensorData.evaluate (TangentSpace S p) r s C
      (Sum.rec (fun i => (LinearMap.proj (v (.inl i))).comp c.toLinearMap)
        (fun j => c.symm (Pi.single (v (.inr j)) 1))) at hh
  have hargs : (fun i => ba i (v i)) =
      Sum.rec (fun i => (LinearMap.proj (v (.inl i))).comp c.toLinearMap)
        (fun j => c.symm (Pi.single (v (.inr j)) 1)) := by
    funext i
    cases i <;> simp [ba, hdual, b, Pi.basisFun_apply]
  simpa only [hargs] using hh

/-- The coordinate formula determines at most one tensor section. Smoothness
and flow existence are not assumptions in this uniqueness argument. -/
theorem coordinateLie_unique_of_fiber_interpretation
    (hfi : Specs.SmoothManifolds.Ch05.Tensors.fiber_interpretationType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (X : SmoothField B)
    {r s : ℕ} (A Z W : TensorData.Field S r s)
    (hZ : CoordinateLieDerivative B X A Z) (hW : CoordinateLieDerivative B X A W) :
    Z = W := by
  funext p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  apply component_ext_of_fiber_interpretation hfi S B r s e he p hp
  intro I J
  obtain ⟨L, hL⟩ := (hZ e he p hp).1
  obtain ⟨K, hK⟩ := ((hZ e he p hp).2 I J).1
  exact (((hZ e he p hp).2 I J).2 L K hL hK).trans
    (((hW e he p hp).2 I J).2 L K hL hK).symm

/-- The interior is dense in each permitted local model, also in dimension
zero. This supplies the uniqueness argument for arbitrary boundary fields. -/
theorem model_interior_dense (n : ℕ) (a : ModelKind) :
    Dense {z : ModelSpace n a | z.val ∈ interior (modelSet n a)} := by
  rw [Subtype.dense_iff]
  have himage : (Subtype.val '' {z : ModelSpace n a | z.val ∈ interior (modelSet n a)}) =
      interior (modelSet n a) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hz; exact ⟨⟨z, interior_subset hz⟩, hz, rfl⟩
  rw [himage]
  cases a with
  | euclidean => simp [modelSet, ModelData.modelSet]
  | halfSpace =>
    cases n with
    | zero => simp [modelSet, ModelData.modelSet, ModelData.halfSpaceSet]
    | succ n =>
      have hconv : Convex ℝ (modelSet (n + 1) .halfSpace) := by
        intro x hx y hy α β hα hβ _
        exact add_nonneg (mul_nonneg hα hx) (mul_nonneg hβ hy)
      have hopen : IsOpen {z : Euclidean (n + 1) | 0 < z (Fin.last n)} :=
        isOpen_lt continuous_const (continuous_apply (Fin.last n))
      have hnonempty : (interior (modelSet (n + 1) .halfSpace)).Nonempty := by
        have hsub : {z : Euclidean (n + 1) | 0 < z (Fin.last n)} ⊆
            modelSet (n + 1) .halfSpace := by
          intro z hz
          change 0 ≤ z (Fin.last n)
          exact le_of_lt hz
        refine ⟨fun _ => 1, (interior_maximal hsub hopen) ?_⟩
        change (0 : ℝ) < 1
        exact zero_lt_one
      rw [hconv.closure_interior_eq_closure_of_nonempty_interior hnonempty]
      exact subset_closure

/-- The intrinsic ordinary interior, not an ambient frontier complement, is
dense in the whole base. Only the shared chart definition of that interior is
used. -/
theorem manifold_interior_dense
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : Dense (BoundaryData.manifoldInterior S) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨p, hpU⟩ := hUne
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) :=
    e.symm.continuousOn.isOpen_inter_preimage e.open_target hU
  have hne : (e.target ∩ e.symm ⁻¹' U).Nonempty :=
    ⟨e p, e.map_source hp, by simpa only [mem_preimage, e.left_inv hp] using hpU⟩
  obtain ⟨z, hz, hzi⟩ := (model_interior_dense n a).inter_open_nonempty _ hopen hne
  refine ⟨e.symm z, hz.2, e, he, e.map_target hz.1, ?_⟩
  change z.val ∈ interior (modelSet n a) at hzi
  change (e (e.symm z)).val ∈ interior (modelSet n a)
  rwa [e.right_inv hz.1]

/-- Two smooth tensors that agree on the ordinary interior agree up to the
boundary. Thus a smooth extension of the interior Lie formula is unique even
when the original field has no boundary-preserving flow. -/
theorem tensor_eq_of_eqOn_interior
    (hfi : Specs.SmoothManifolds.Ch05.Tensors.fiber_interpretationType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (r s : ℕ)
    (A Z : SmoothTensor B r s)
    (hAZ : ∀ p ∈ BoundaryData.manifoldInterior S, A.val p = Z.val p) : A = Z := by
  have hval : A.val = Z.val := by
    funext p
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    apply component_ext_of_fiber_interpretation hfi S B r s e he p hp
    intro I J
    have hA : ContinuousOn (tensorCoefficients B A.val e he I J) e.source := by
      intro q hq
      exact ((scalarContDiffAt_iff _ _ _ _).mp (A.smooth e he q hq I J)).1.continuousWithinAt
    have hZ : ContinuousOn (tensorCoefficients B Z.val e he I J) e.source := by
      intro q hq
      exact ((scalarContDiffAt_iff _ _ _ _).mp (Z.smooth e he q hq I J)).1.continuousWithinAt
    have hdense : e.source ⊆ closure (BoundaryData.manifoldInterior S ∩ e.source) := by
      intro q hq
      rw [mem_closure_iff]
      intro V hV hqV
      obtain ⟨w, hw, hwi⟩ := (manifold_interior_dense S).inter_open_nonempty
        (V ∩ e.source) (hV.inter e.open_source) ⟨q, hqV, hq⟩
      exact ⟨w, hw.1, hwi, hw.2⟩
    have hEq : EqOn (tensorCoefficients B A.val e he I J)
        (tensorCoefficients B Z.val e he I J) (BoundaryData.manifoldInterior S ∩ e.source) := by
      intro q hq
      unfold tensorCoefficients
      rw [hAZ q hq.1]
    exact hEq.of_subset_closure hA hZ inter_subset_right hdense hp
  cases A
  cases Z
  cases hval
  rfl

/-- Evaluation components agree with the coordinates of the upstream mixed
tensor bundle, including the scalar tensor powers. -/
theorem component_eq_mixedCoordinates
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (r s : ℕ)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (I : Fin r → Fin n) (J : Fin s → Fin n)
    (A : TensorData.Fiber (TangentSpace S p) r s) :
    component B r s e he p I J A =
      Tensors.mixedCoordinates (B.fiberCoordinates.equiv e he p hp) r s A
        (finProdFinEquiv (TensorData.powerIndex n r I, TensorData.powerIndex n s J)) := by
  classical
  let c := B.fiberCoordinates.equiv e he p hp
  let q := finProdFinEquiv (TensorData.powerIndex n r I, TensorData.powerIndex n s J)
  have hm : component B r s e he p I J =
      (LinearMap.proj q).comp (Tensors.mixedCoordinates c r s).toLinearMap := by
    ext v lam
    change component B r s e he p I J (TensorData.pure v lam) =
      Tensors.mixedCoordinates c r s (TensorData.pure v lam) q
    simp only [component, dite_eq_left hp, LinearMap.coe_mk, AddHom.coe_mk,
      Tensors.evaluate_pure]
    simpa [c, q] using (Tensors.mixedCoordinates_pure c v lam q).symm
  exact congrArg (fun L => L A) hm

/-- Every linear test of a fixed-fiber tensor curve can be differentiated
from the derivatives of its components. -/
theorem linear_test_hasDerivAt
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (r s : ℕ)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source)
    (A : ℝ → TensorData.Fiber (TangentSpace S p) r s)
    (Z : TensorData.Fiber (TangentSpace S p) r s) (t : ℝ)
    (hA : ∀ I J, HasDerivAt (fun τ => component B r s e he p I J (A τ))
      (component B r s e he p I J Z) t)
    (L : TensorData.Fiber (TangentSpace S p) r s →ₗ[ℝ] ℝ) :
    HasDerivAt (fun τ => L (A τ)) (L Z) t := by
  classical
  let c := B.fiberCoordinates.equiv e he p hp
  let C := Tensors.mixedCoordinates c r s
  have hC (q : Fin (n^r*n^s)) :
      HasDerivAt (fun τ => C (A τ) q) (C Z q) t := by
    obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective q
    obtain ⟨I,rfl⟩ := (TensorData.powerIndex n r).surjective i
    obtain ⟨J,rfl⟩ := (TensorData.powerIndex n s).surjective j
    simpa only [component_eq_mixedCoordinates B r s e he p hp] using hA I J
  have hexp (x : TensorData.Fiber (TangentSpace S p) r s) :
      L x = ∑ q : Fin (n^r*n^s), C x q * L (C.symm (Pi.single q 1)) := by
    have hx : x = ∑ q : Fin (n^r*n^s), C x q • C.symm (Pi.single q 1) := by
      apply C.injective
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
      ext k
      simp [Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun q _ => (hC q).mul_const (L (C.symm (Pi.single q 1))))
  have hfun : (∑ q : Fin (n^r*n^s),
      fun τ => C (A τ) q * L (C.symm (Pi.single q 1))) = (fun τ => L (A τ)) := by
    funext τ
    simpa only [Finset.sum_apply] using (hexp (A τ)).symm
  rw [hfun, ← hexp] at hd
  exact hd


/-- The product rule for an arbitrary bilinear scalar test on actual tensor
fibers. No norm or topology is chosen on the algebraic tensor products. -/
theorem bilinear_test_hasDerivAt
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (r s r' s' : ℕ)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source)
    (A : ℝ → TensorData.Fiber (TangentSpace S p) r s)
    (C : ℝ → TensorData.Fiber (TangentSpace S p) r' s')
    (ZA : TensorData.Fiber (TangentSpace S p) r s)
    (ZC : TensorData.Fiber (TangentSpace S p) r' s') (t : ℝ)
    (hA : ∀ I J, HasDerivAt (fun τ => component B r s e he p I J (A τ))
      (component B r s e he p I J ZA) t)
    (hC : ∀ I J, HasDerivAt (fun τ => component B r' s' e he p I J (C τ))
      (component B r' s' e he p I J ZC) t)
    (L : TensorData.Fiber (TangentSpace S p) r s →ₗ[ℝ]
      TensorData.Fiber (TangentSpace S p) r' s' →ₗ[ℝ] ℝ) :
    HasDerivAt (fun τ => L (A τ) (C τ)) (L ZA (C t) + L (A t) ZC) t := by
  classical
  let c := B.fiberCoordinates.equiv e he p hp
  let D := Tensors.mixedCoordinates c r s
  have hD (q : Fin (n^r*n^s)) :
      HasDerivAt (fun τ => D (A τ) q) (D ZA q) t := by
    obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective q
    obtain ⟨I,rfl⟩ := (TensorData.powerIndex n r).surjective i
    obtain ⟨J,rfl⟩ := (TensorData.powerIndex n s).surjective j
    simpa only [component_eq_mixedCoordinates B r s e he p hp] using hA I J
  have hexp (x : TensorData.Fiber (TangentSpace S p) r s)
      (y : TensorData.Fiber (TangentSpace S p) r' s') :
      L x y = ∑ q : Fin (n^r*n^s), D x q * L (D.symm (Pi.single q 1)) y := by
    have hx : x = ∑ q : Fin (n^r*n^s), D x q • D.symm (Pi.single q 1) := by
      apply D.injective
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
      ext k
      simp [Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hd := HasDerivAt.sum (u := Finset.univ) (fun q _ =>
    (hD q).mul (linear_test_hasDerivAt B r' s' e he p hp C ZC t hC
      (L (D.symm (Pi.single q 1)))))
  have hfun : (∑ q : Fin (n^r*n^s),
      (fun τ => D (A τ) q) * (fun τ => L (D.symm (Pi.single q 1)) (C τ))) =
      (fun τ => L (A τ) (C τ)) := by
    funext τ
    simpa only [Finset.sum_apply, Pi.mul_apply] using (hexp (A τ) (C τ)).symm
  rw [hfun] at hd
  simpa only [Finset.sum_add_distrib, ← hexp] using hd

/-- The zero-time tensor transport is the identity because its equivalence
is the actual differential of the identity map. -/
theorem mixedTransport_eq_self_of_identity
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (f : M → M) (hf : f = id) (p : M)
    (d : TangentSpace S p ≃ₗ[ℝ] TangentSpace S (f p))
    (hd : DifferentialData.IsDifferential S S f p d.toLinearMap)
    (r s : ℕ) (A : TensorData.Field S r s) :
    TensorData.mixedTransport r s d (A (f p)) = A p := by
  subst f
  have h := (differential_exists S S id
    (manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val
      S.smoothStructure.property.1) p).unique hd (differential_id S p)
  have heq : d = LinearEquiv.refl ℝ _ := LinearEquiv.toLinearMap_injective h
  simp [heq]

/-- Differentiation of actual mixed pullback commutes with every natural
fiberwise linear operation. Naturality is checked for genuine linear
equivalences; no regularity certificate for the operation is assumed. -/
theorem flow_derivative_linear_operation
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : MaximalFlowData.CurveFamily M) {r s r' s' : ℕ}
    (Q : (p : M) → TensorData.Fiber (TangentSpace S p) r s →ₗ[ℝ]
      TensorData.Fiber (TangentSpace S p) r' s')
    (hQ : ∀ p q (d : TangentSpace S p ≃ₗ[ℝ] TangentSpace S q) x,
      Q p (TensorData.mixedTransport r s d x) =
        TensorData.mixedTransport r' s' d (Q q x))
    (A Z : TensorData.Field S r s) (p : M)
    (hA : HasTensorFlowDerivative B F A Z p) :
    HasTensorFlowDerivative B F (fun q => Q q (A q)) (fun q => Q q (Z q)) p := by
  refine ⟨hA.choose, hA.choose_spec.1, ?_⟩
  intro d hd e he hp I J
  have h := linear_test_hasDerivAt B r s e he p hp
    (fun t => TensorData.mixedTransport r s (d t) (A (F.curve p t))) (Z p) 0
    (hA.choose_spec.2 d hd e he hp)
    ((component B r' s' e he p I J).comp (Q p))
  simpa only [LinearMap.comp_apply, hQ, tensorCoefficients] using h

theorem tensor_flow_contraction :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_flow_contractionType.{u} := by
  intro n a M _ S B F r s i j A Z p hA
  apply flow_derivative_linear_operation B F
    (fun q => TensorData.contract (TangentSpace S q) i j) ?_ A Z p hA
  intro p q d x
  exact congrArg (fun L => L x) (Tensors.contract_natural i j d)

theorem tensor_flow_permutation :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_flow_permutationType.{u} := by
  intro n a M _ S B F r s σ τ A Z p hA
  apply flow_derivative_linear_operation B F
    (fun q => TensorData.mixedPermute (TangentSpace S q) r s σ τ) ?_ A Z p hA
  intro p q d x
  exact congrArg (fun L => L x) (Tensors.mixedPermute_natural r s σ τ d)

/-- Tensor-product Leibniz rule for actual flow derivatives. Only the
zero-time identity of the flow is needed beyond existence of the derivatives. -/
theorem tensor_flow_product :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_flow_productType.{u} := by
  intro n a M _ S B F hzero r s r' s' A C ZA ZC p hA hC
  refine ⟨hA.choose, hA.choose_spec.1, ?_⟩
  intro d hd e he hp I J
  have hd0 := (Filter.Eventually.self_of_nhds hd).2
  have h0A := mixedTransport_eq_self_of_identity S (fun q => F.curve q 0)
    (funext hzero) p (d 0) hd0 r s A
  have h0C := mixedTransport_eq_self_of_identity S (fun q => F.curve q 0)
    (funext hzero) p (d 0) hd0 r' s' C
  have h := bilinear_test_hasDerivAt B r s r' s' e he p hp
    (fun t => TensorData.mixedTransport r s (d t) (A (F.curve p t)))
    (fun t => TensorData.mixedTransport r' s' (d t) (C (F.curve p t)))
    (ZA p) (ZC p) 0 (hA.choose_spec.2 d hd e he hp) (hC.choose_spec.2 d hd e he hp)
    ((TensorData.tensorMultiply (TangentSpace S p) r s r' s').compr₂
      (component B (r+r') (s+s') e he p I J))
  simpa only [LinearMap.compr₂_apply, h0A, h0C, tensorCoefficients, map_add,
    ← Tensors.tensorMultiply_natural] using h

theorem scalar_flow :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.scalar_flowType.{u} := by
  intro n a M _ S B X D hD I γ hI hγ f t ht
  exact scalar_derivative_on_curve S B X D hD I γ hI hγ f t ht

theorem vector_flow :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.vector_flowType.{u} := by
  constructor
  · intro n M _ S B b hb X Y F hF
    exact ⟨(BracketFromFlow.pullback_boundaryless S B X F hF).1,
      (BracketFromFlow.pullback_boundaryless S B X F hF).2 Y,
      BracketFromFlow.pullback_smooth S B X F hF Y,
      BracketFromFlow.derivative_zero S B b hb X Y F hF,
      BracketFromFlow.derivative_at_time S B b hb X Y F hF⟩
  · intro n a M _ S B b hb X Y hX F hF
    exact ⟨(BracketFromFlow.pullback_boundary S B X hX F hF).1,
      (BracketFromFlow.pullback_boundary S B X hX F hF).2 Y,
      BracketFromFlow.boundary_pullback_smooth S B X hX F hF Y,
      BracketFromFlow.boundary_derivative_zero S B b hb X Y hX F hF,
      BracketFromFlow.boundary_derivative_at_time S B b hb X Y hX F hF⟩

theorem tensor_coefficients_ext :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_coefficients_extType.{u} := by
  intro n a M _ S B r s e he p hp A C h
  exact component_ext_of_fiber_interpretation Tensors.fiber_interpretation S B r s e he p hp A C h

theorem local_formula_smooth :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.local_formula_smoothType := by
  exact arrayLie_smooth

theorem tensor_coordinate_unique :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_coordinate_uniqueType.{u} := by
  intro n a M _ S B X r s A Z W hZ hW
  exact coordinateLie_unique_of_fiber_interpretation Tensors.fiber_interpretation S B X A Z W hZ hW

theorem boundary_extension_unique :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.boundary_extension_uniqueType.{u} := by
  intro n a M _ S B r s A Z hAZ
  exact tensor_eq_of_eqOn_interior Tensors.fiber_interpretation S B r s A Z hAZ

theorem component_eq_bundle_coordinate
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (T : TensorData.TensorBundle S r s)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (I : Fin r → Fin n) (J : Fin s → Fin n)
    (A : TensorData.Fiber (TangentSpace S p) r s) :
    letI := (TensorData.tensorSpace T).topology
    component B r s e he p I J A =
      (((TensorData.tensorSpace T).bundle.trivialization (⟨e,he⟩,⟨e,he⟩)) ⟨p,A⟩).2
        (finProdFinEquiv (TensorData.powerIndex n r I, TensorData.powerIndex n s J)) := by
  letI := (TensorData.tensorSpace T).topology
  rw [component_eq_mixedCoordinates B r s e he p hp,
    Tensors.tensorSpace_diagonal_coordinates T ⟨e,he⟩ p hp
      (B.fiberCoordinates.equiv e he p hp)
      (B.fiberCoordinates.isCoordinates e he p hp)]

theorem tensorSmooth_iff_isSmoothField
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (T : TensorData.TensorBundle S r s) (A : TensorData.Field S r s) :
    TensorSmooth B A ↔ TensorData.IsSmoothField T A := by
  classical
  letI := (TensorData.tensorSpace T).topology
  constructor
  · intro hA p
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
    let i : BundleOperationsData.TangentIndex S := ⟨e,he⟩
    let v : M → Euclidean (n^r*n^s) := fun q =>
      (((TensorData.tensorSpace T).bundle.trivialization (i,i)) ⟨q,A q⟩).2
    have hv : FrameData.VectorSmoothAt S.smoothStructure.val v p := by
      apply FrameData.VectorSmoothAt.pi
      intro k
      obtain ⟨⟨kr,ks⟩, rfl⟩ := finProdFinEquiv.surjective k
      obtain ⟨I,rfl⟩ := (TensorData.powerIndex n r).surjective kr
      obtain ⟨J,rfl⟩ := (TensorData.powerIndex n s).surjective ks
      apply FrameData.VectorSmoothAt.congr
        ((scalarContDiffAt_iff _ _ _ _).mp (hA e he p hp I J))
      filter_upwards [e.open_source.mem_nhds hp] with q hq
      exact component_eq_bundle_coordinate B T e he q hq I J (A q)
    exact Frames.smoothAt_from_trivialization (TensorData.tensorSpace T).bundle
      S.smoothStructure.property.1 (i,i)
      (by rw [Tensors.tensorSpace_diagonal_baseSet]; exact hp)
      (manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val
        S.smoothStructure.property.1 p) hv (fun _ => rfl) Filter.EventuallyEq.rfl
  · intro hA e he p hp I J
    let i : BundleOperationsData.TangentIndex S := ⟨e,he⟩
    have hv := FrameData.VectorSmoothAt.comp
      (g := fun q : M => (⟨q,A q⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
        (fun q => TensorData.Fiber (TangentSpace S q) r s)))
      (TensorData.tensorSpace T).bundle.totalManifold.smoothStructure.property.1.1
      (Frames.trivializationCoordinates_smoothAt
      (TensorData.tensorSpace T).bundle (i,i) ⟨p,A p⟩
      (by rw [Tensors.tensorSpace_diagonal_baseSet]; exact hp)) (hA p)
    have hproj := hv.postcomp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (n^r*n^s) => ℝ)
      (finProdFinEquiv (TensorData.powerIndex n r I, TensorData.powerIndex n s J))).contDiff
    apply (scalarContDiffAt_iff _ _ _ _).mpr
    apply FrameData.VectorSmoothAt.congr hproj
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact (component_eq_bundle_coordinate B T e he q hq I J (A q)).symm


theorem tensorSmooth_contract
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (i : Fin (r+1)) (j : Fin (s+1)) (A : TensorData.Field S (r+1) (s+1))
    (hA : TensorSmooth B A) :
    TensorSmooth B (fun p => TensorData.contract (TangentSpace S p) i j (A p)) := by
  obtain ⟨T⟩ := Tensors.exists_tensorBundle S (r+1) (s+1)
  obtain ⟨D⟩ := Tensors.exists_tensorBundle S r s
  letI := (TensorData.tensorSpace T).topology
  letI := (TensorData.tensorSpace D).topology
  apply (tensorSmooth_iff_isSmoothField B D _).mpr
  intro p
  exact manifoldContDiffAt_comp
    (TensorData.tensorSpace T).bundle.totalManifold.smoothStructure.property.1.1
    ((tensorSmooth_iff_isSmoothField B T A).mp hA p)
    (Tensors.contraction_smooth T D i j ⟨p,A p⟩)

theorem tensorSmooth_permute
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)) (A : TensorData.Field S r s)
    (hA : TensorSmooth B A) :
    TensorSmooth B (fun p => TensorData.mixedPermute (TangentSpace S p) r s σ τ (A p)) := by
  obtain ⟨T⟩ := Tensors.exists_tensorBundle S r s
  letI := (TensorData.tensorSpace T).topology
  apply (tensorSmooth_iff_isSmoothField B T _).mpr
  intro p
  exact manifoldContDiffAt_comp
    (TensorData.tensorSpace T).bundle.totalManifold.smoothStructure.property.1.1
    ((tensorSmooth_iff_isSmoothField B T A).mp hA p)
    (Tensors.mixedPermute_smooth T σ τ ⟨p,A p⟩)

theorem tensorSmooth_product
    {n r s r' s' : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (A : TensorData.Field S r s) (C : TensorData.Field S r' s')
    (hA : TensorSmooth B A) (hC : TensorSmooth B C) :
    TensorSmooth B (fun p => TensorData.tensorMultiply (TangentSpace S p) r s r' s' (A p) (C p)) := by
  obtain ⟨T⟩ := Tensors.exists_tensorBundle S r s
  obtain ⟨D⟩ := Tensors.exists_tensorBundle S r' s'
  obtain ⟨E⟩ := Tensors.exists_tensorBundle S (r+r') (s+s')
  apply (tensorSmooth_iff_isSmoothField B E _).mpr
  exact Tensors.tensorMultiply_lift_smooth T D E S id A C
    ((tensorSmooth_iff_isSmoothField B T A).mp hA)
    ((tensorSmooth_iff_isSmoothField B D C).mp hC)


theorem multilinear_coordinate_expansion {n s : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ)
    (v : Fin s → Euclidean n) :
    F v = ∑ J : Fin s → Fin n, (∏ i : Fin s, v i (J i)) *
      F (fun i => Pi.single (J i) 1) := by
  classical
  have hv (i : Fin s) : v i = ∑ k : Fin n, v i k • Pi.single k 1 := by
    ext j
    simp [Pi.single_apply]
  calc
    F v = F (fun i => ∑ k : Fin n, v i k • Pi.single k 1) := by
      congr 1
      exact funext hv
    _ = ∑ J : Fin s → Fin n, F (fun i => v i (J i) • Pi.single (J i) 1) :=
      F.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro J _
      rw [F.map_smul_univ]
      rfl

theorem covariantEvaluation_eq_sum
    {n s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (A : TensorData.Field S 0 s) (Y : Fin s → Section S) :
    covariantEvaluation A Y p =
      ∑ J : Fin s → Fin n, (∏ i : Fin s, coefficients B (Y i) e he p (J i)) *
        tensorCoefficients B A e he Fin.elim0 J p := by
  classical
  let c := B.fiberCoordinates.equiv e he p hp
  let F := (TensorData.covariantEvaluate (TangentSpace S p) s
    (TensorData.covariantEquiv (TangentSpace S p) s (A p))).compLinearMap
      (fun _ : Fin s => c.symm.toLinearMap)
  have hF : F (fun i => c (Y i p)) = covariantEvaluation A Y p := by
    simp [F, covariantEvaluation]
  rw [← hF, multilinear_coordinate_expansion]
  apply Finset.sum_congr rfl
  intro J _
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [coefficients, hp, c]
  · change TensorData.covariantEvaluate (TangentSpace S p) s
      (TensorData.covariantEquiv (TangentSpace S p) s (A p))
      (fun i => c.symm (Pi.single (J i) 1)) = _
    rw [← Tensors.evaluate_covariantEquiv]
    unfold tensorCoefficients component
    simp only [dite_eq_left hp, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    funext i
    cases i with
    | inl i => exact Fin.elim0 i
    | inr i => rfl

theorem scalarContDiffAt_finset_prod
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {r : ℕ∞} {A : Set (ModelChart n a M)} {x : M}
    {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ScalarContDiffAt r A (f i) x) :
    ScalarContDiffAt r A (fun y => ∏ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ScalarContDiffAt.const r A 1 x
  | @insert i s hi ih =>
    simpa [hi] using (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem field_coefficient_scalar_smooth
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    (X : SmoothField B) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (k : Fin n) :
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
      (fun q => coefficients B X.val e he q k) p := by
  obtain ⟨U, hU, hpU, F, hF, heq⟩ := LieBrackets.smooth_field_regular X e he p hp
  apply scalarContDiffAt_of_chart S.smoothStructure.property.1 he hp
  refine ⟨U, hU, hpU, (fun z => F z k), ?_, ?_⟩
  · exact (contDiffOn_pi.mp hF) k
  · exact heq.mono (fun q hq => congrFun hq k)

theorem covariantEvaluation_scalar_smooth
    {n s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (A : SmoothTensor B 0 s) (Y : Fin s → SmoothField B) (p : M) :
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
      (covariantEvaluation A.val (fun i => (Y i).val)) p := by
  classical
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  have hsum : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
      (fun q => ∑ J : Fin s → Fin n,
        (∏ i : Fin s, coefficients B (Y i).val e he q (J i)) *
          tensorCoefficients B A.val e he Fin.elim0 J q) p := by
    apply ScalarContDiffAt.sum Finset.univ
    intro J _
    apply ScalarContDiffAt.mul
    · apply scalarContDiffAt_finset_prod Finset.univ
      intro i _
      exact field_coefficient_scalar_smooth (Y i) e he p hp (J i)
    · exact A.smooth e he p hp Fin.elim0 J
  apply hsum.congr
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact (covariantEvaluation_eq_sum B e he q hq A.val (fun i => (Y i).val)).symm


/-- Any smooth scalar has a genuine ambient coordinate derivative at every chart point. -/
theorem scalar_coordinate_derivative_exists
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : M → ℝ) (p : M)
    (hg : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val g p)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    ∃ K, HasScalarCoordinateDerivative e g p K := by
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := ((scalarContDiffAt_iff _ _ _ _).mp hg).2 e he hp
  exact ⟨fderiv ℝ G (e p).val, G,
    ((hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt, heG⟩

/-- The local ambient scalar differential is independent of extensions, also on a face. -/
theorem scalar_coordinate_derivative_unique
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n a M) (g : M → ℝ) (p : M) (hp : p ∈ e.source)
    (K L : Euclidean n →L[ℝ] ℝ)
    (hK : HasScalarCoordinateDerivative e g p K)
    (hL : HasScalarCoordinateDerivative e g p L) : K = L := by
  obtain ⟨F, hF, heF⟩ := hK
  obtain ⟨G, hG, heG⟩ := hL
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp (heF.trans heG.symm)
  let s : Set (ModelSpace n a) := e.target ∩ e.symm ⁻¹' V
  have hs : IsOpen s := e.symm.isOpen_inter_preimage hV
  have heps : e p ∈ s := ⟨e.map_source hp, by
    change e.symm (e p) ∈ V
    rwa [e.left_inv hp]⟩
  have hFG : EqOn F G (Subtype.val '' s) := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := hVsub hx.2
    change F (e (e.symm x)).val = G (e (e.symm x)).val at hh
    simpa only [e.right_inv hx.1] using hh
  have hpoint : (e p).val ∈ Subtype.val '' s := ⟨e p, heps, rfl⟩
  exact (uniqueDiffOn_modelDomain hs).eq hpoint
    hF.hasFDerivWithinAt (hG.hasFDerivWithinAt.congr' hFG hpoint)

/-- Every smooth tensor coefficient has the ambient derivative required by the full formula. -/
theorem tensor_coordinate_derivative_exists
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (A : SmoothTensor B r s) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source)
    (I : Fin r → Fin n) (J : Fin s → Fin n) :
    ∃ K, HasScalarCoordinateDerivative e (tensorCoefficients B A.val e he I J) p K :=
  scalar_coordinate_derivative_exists _ p (A.smooth e he p hp I J) e he hp

/-- An arbitrary complete coordinate array reconstructs a unique tensor in the actual fiber. -/
theorem tensor_reconstruction
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source)
    (C : (Fin r → Fin n) → (Fin s → Fin n) → ℝ) :
    ∃! A : TensorData.Fiber (TangentSpace S p) r s,
      ∀ I J, component B r s e he p I J A = C I J := by
  classical
  let c := B.fiberCoordinates.equiv e he p hp
  let coords : Euclidean (n^r * n^s) := fun q =>
    C ((TensorData.powerIndex n r).symm (finProdFinEquiv.symm q).1)
      ((TensorData.powerIndex n s).symm (finProdFinEquiv.symm q).2)
  refine ⟨(Tensors.mixedCoordinates c r s).symm coords, ?_, ?_⟩
  · intro I J
    rw [component_eq_mixedCoordinates B r s e he p hp]
    simp only [c, LinearEquiv.apply_symm_apply, coords, Equiv.symm_apply_apply]
  · intro A hA
    apply (Tensors.mixedCoordinates c r s).injective
    rw [LinearEquiv.apply_symm_apply]
    funext q
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective q
    obtain ⟨I,rfl⟩ := (TensorData.powerIndex n r).surjective i
    obtain ⟨J,rfl⟩ := (TensorData.powerIndex n s).surjective j
    simpa only [component_eq_mixedCoordinates B r s e he p hp,
      coords, Equiv.symm_apply_apply] using hA I J

/-- The complete mixed formula determines an actual fiber element in any chosen chart.
Chart independence, needed for a global field, is a separate assertion. -/
theorem chart_coordinate_lie_exists
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (A : SmoothTensor B r s)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    ∃! v : TensorData.Fiber (TangentSpace S p) r s,
      ∀ (I : Fin r → Fin n) (J : Fin s → Fin n)
        (L : Euclidean n →L[ℝ] Euclidean n) (K : Euclidean n →L[ℝ] ℝ),
        HasCoordinateDerivative e (coefficients B X.val e he) p L →
        HasScalarCoordinateDerivative e (tensorCoefficients B A.val e he I J) p K →
        component B r s e he p I J v =
          K (coefficients B X.val e he p) -
            (∑ i : Fin r, ∑ k : Fin n, L (Pi.single k 1) (I i) *
              tensorCoefficients B A.val e he (Function.update I i k) J p) +
            (∑ j : Fin s, ∑ k : Fin n, L (Pi.single (J j) 1) k *
              tensorCoefficients B A.val e he I (Function.update J j k) p) := by
  classical
  obtain ⟨L, hL⟩ := LieBrackets.coordinate_derivative_exists X e he p hp
  choose K hK using tensor_coordinate_derivative_exists B A e he p hp
  let C (I : Fin r → Fin n) (J : Fin s → Fin n) : ℝ :=
    K I J (coefficients B X.val e he p) -
      (∑ i : Fin r, ∑ k : Fin n, L (Pi.single k 1) (I i) *
        tensorCoefficients B A.val e he (Function.update I i k) J p) +
      (∑ j : Fin s, ∑ k : Fin n, L (Pi.single (J j) 1) k *
        tensorCoefficients B A.val e he I (Function.update J j k) p)
  obtain ⟨v, hv, huniq⟩ := tensor_reconstruction B e he p hp C
  refine ⟨v, ?_, ?_⟩
  · intro I J L' K' hL' hK'
    have hLeq : L' = L := FiniteRegularity.extension_independence e _ p hp _ _ hL' hL
    have hKeq : K' = K I J := scalar_coordinate_derivative_unique e _ p hp _ _ hK' (hK I J)
    subst L'
    subst K'
    exact hv I J
  · intro w hw
    apply huniq w
    intro I J
    exact hw I J L (K I J) hL (hK I J)


lemma update_comp_equiv {r n : ℕ} (σ : Equiv.Perm (Fin r)) (I : Fin r → Fin n)
    (i : Fin r) (k : Fin n) :
    (Function.update I (σ i) k) ∘ σ = Function.update (I ∘ σ) i k := by
  classical
  funext j
  by_cases hj : j = i
  · subst j; simp
  · have hs : σ j ≠ σ i := fun h => hj (σ.injective h)
    simp [Function.update_of_ne, hj, hs, Function.comp_apply]

theorem arrayLie_permutation (n r s : ℕ) (X : Euclidean n → Euclidean n)
    (A : Euclidean n → (Fin r → Fin n) → (Fin s → Fin n) → ℝ)
    (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s))
    (z : Euclidean n) (I : Fin r → Fin n) (J : Fin s → Fin n) :
    arrayLie n r s X (fun z I J => A z (I ∘ σ) (J ∘ τ)) z I J =
      arrayLie n r s X A z (I ∘ σ) (J ∘ τ) := by
  classical
  unfold arrayLie
  have hu : (∑ i : Fin r, ∑ k : Fin n,
      fderiv ℝ X z (Pi.single k 1) (I i) *
      A z ((Function.update I i k) ∘ σ) (J ∘ τ)) =
    ∑ i : Fin r, ∑ k : Fin n,
      fderiv ℝ X z (Pi.single k 1) ((I ∘ σ) i) *
      A z (Function.update (I ∘ σ) i k) (J ∘ τ) := by
    rw [← Equiv.sum_comp σ]
    simp only [update_comp_equiv, Function.comp_apply]
  have hl : (∑ j : Fin s, ∑ k : Fin n,
      fderiv ℝ X z (Pi.single (J j) 1) k *
      A z (I ∘ σ) ((Function.update J j k) ∘ τ)) =
    ∑ j : Fin s, ∑ k : Fin n,
      fderiv ℝ X z (Pi.single ((J ∘ τ) j) 1) k *
      A z (I ∘ σ) (Function.update (J ∘ τ) j k) := by
    rw [← Equiv.sum_comp τ]
    simp only [update_comp_equiv, Function.comp_apply]
  rw [hu, hl]

theorem component_mixedPermute
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (r s : ℕ)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s))
    (I : Fin r → Fin n) (J : Fin s → Fin n)
    (A : TensorData.Fiber (TangentSpace S p) r s) :
    component B r s e he p I J (TensorData.mixedPermute (TangentSpace S p) r s σ τ A) =
      component B r s e he p (I ∘ σ) (J ∘ τ) A := by
  classical
  by_cases hp : p ∈ e.source
  · have hm : (component B r s e he p I J).comp
        (TensorData.mixedPermute (TangentSpace S p) r s σ τ) =
        component B r s e he p (I ∘ σ) (J ∘ τ) := by
      ext v lam
      change component B r s e he p I J
          (TensorData.mixedPermute (TangentSpace S p) r s σ τ (TensorData.pure v lam)) =
        component B r s e he p (I ∘ σ) (J ∘ τ) (TensorData.pure v lam)
      simp only [TensorData.mixedPermute, TensorData.pure, TensorProduct.map_tmul,
        TensorData.permute, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod]
      change component B r s e he p I J
          (TensorData.pure (fun i => v (σ.symm i)) (fun j => lam (τ.symm j))) =
        component B r s e he p (I ∘ σ) (J ∘ τ) (TensorData.pure v lam)
      simp only [component, dite_eq_left hp, LinearMap.coe_mk, AddHom.coe_mk, Tensors.evaluate_pure,
        LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply]
      rw [← Equiv.prod_comp σ, ← Equiv.prod_comp τ]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        rw [σ.symm_apply_apply]
      · apply Finset.prod_congr rfl
        intro j _
        rw [τ.symm_apply_apply]
    exact congrArg (fun L => L A) hm
  · simp [component, hp]


theorem tensor_coordinate_permutation
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (r s : ℕ) (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s))
    (A Z : TensorData.Field S r s) (hA : CoordinateLieDerivative B X A Z) :
    CoordinateLieDerivative B X
      (fun q => TensorData.mixedPermute (TangentSpace S q) r s σ τ (A q))
      (fun q => TensorData.mixedPermute (TangentSpace S q) r s σ τ (Z q)) := by
  classical
  intro e he p hp
  obtain ⟨hX, hA⟩ := hA e he p hp
  refine ⟨hX, ?_⟩
  intro I J
  have eqA (I J) :
      tensorCoefficients B
        (fun q => TensorData.mixedPermute (TangentSpace S q) r s σ τ (A q)) e he I J =
      tensorCoefficients B A e he (I ∘ σ) (J ∘ τ) := by
    funext q
    exact component_mixedPermute B r s e he q σ τ I J (A q)
  refine ⟨?_, ?_⟩
  · rw [eqA]
    exact (hA (I ∘ σ) (J ∘ τ)).1
  · intro L K hL hK
    rw [eqA] at hK
    have h := (hA (I ∘ σ) (J ∘ τ)).2 L K hL hK
    simp only [tensorCoefficients, component_mixedPermute] at h ⊢
    rw [h]
    have hu : (∑ i : Fin r, ∑ k : Fin n,
        L (Pi.single k 1) (I i) *
        component B r s e he p ((Function.update I i k) ∘ σ) (J ∘ τ) (A p)) =
      ∑ i : Fin r, ∑ k : Fin n,
        L (Pi.single k 1) ((I ∘ σ) i) *
        component B r s e he p (Function.update (I ∘ σ) i k) (J ∘ τ) (A p) := by
      rw [← Equiv.sum_comp σ]
      simp only [update_comp_equiv, Function.comp_apply]
    have hl : (∑ j : Fin s, ∑ k : Fin n,
        L (Pi.single (J j) 1) k *
        component B r s e he p (I ∘ σ) ((Function.update J j k) ∘ τ) (A p)) =
      ∑ j : Fin s, ∑ k : Fin n,
        L (Pi.single ((J ∘ τ) j) 1) k *
        component B r s e he p (I ∘ σ) (Function.update (J ∘ τ) j k) (A p) := by
      rw [← Equiv.sum_comp τ]
      simp only [update_comp_equiv, Function.comp_apply]
    rw [hu, hl]

/-- The coefficient representation and the actual tensor bundle have the same
smooth sections, independently of the chosen tangent and cotangent realizations. -/
theorem tensor_smooth_iff :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_smooth_iffType.{u} := by
  intro n r s a M _ S B T A
  exact tensorSmooth_iff_isSmoothField B T A

theorem covariant_evaluation_smooth :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.covariant_evaluation_smoothType.{u} := by
  intro n s a M _ S B A Y
  exact ⟨⟨_, (mem_globalSmoothAlgebra_iff S _).mpr
    (covariantEvaluation_scalar_smooth B A Y)⟩, rfl⟩

theorem tensor_operations_smooth :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_operations_smoothType.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro n r s a M _ S B i j A hA
    exact tensorSmooth_contract B i j A hA
  · intro n r s a M _ S B σ τ A hA
    exact tensorSmooth_permute B σ τ A hA
  · intro n r s r' s' a M _ S B A C hA hC
    exact tensorSmooth_product B A C hA hC

theorem tensor_permutation :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_permutationType.{u} := by
  intro n a M _ S B X r s σ τ A Z hA
  exact tensor_coordinate_permutation B X r s σ τ A Z hA

/-- The tensor coordinate entries respect addition in their original fibers. -/
theorem tensorSmooth_add
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (A C : TensorData.Field S r s) (hA : TensorSmooth B A) (hC : TensorSmooth B C) :
    TensorSmooth B (fun p => A p + C p) := by
  intro e he p hp I J
  apply ScalarContDiffAt.congr
    (ScalarContDiffAt.add (hA e he p hp I J) (hC e he p hp I J))
  exact Filter.Eventually.of_forall (fun q => (map_add (component B r s e he q I J) (A q) (C q)).symm)

@[simp] theorem component_scalarTensorField
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (f : M → ℝ) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (I J : Fin 0 → Fin n) :
    tensorCoefficients B (scalarTensorField f) e he I J p = f p := by
  simp [tensorCoefficients, scalarTensorField, component, hp, Tensors.evaluate_pure]

@[simp] theorem component_vectorTensorField
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (Y : Section S) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (I : Fin 1 → Fin n) (J : Fin 0 → Fin n) :
    tensorCoefficients B (vectorTensorField Y) e he I J p = coefficients B Y e he p (I 0) := by
  simp [tensorCoefficients, vectorTensorField, component, hp, Tensors.evaluate_pure,
    coefficients]

/-- Canonical scalar tensors have exactly the source's scalar smoothness. -/
theorem scalarTensorField_smooth
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (f : GlobalSmooth S) :
    TensorSmooth B (scalarTensorField f.val) := by
  intro e he p hp I J
  apply ScalarContDiffAt.congr ((mem_globalSmoothAlgebra_iff S _).mp f.property p)
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact (component_scalarTensorField B f.val e he q hq I J).symm

/-- Any coordinate component of a smooth vector field is a smooth scalar near its chart. -/
theorem vector_component_smoothAt
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (Y : SmoothField B) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (j : Fin n) :
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val (fun q => coefficients B Y.val e he q j) p := by
  have h := TangentBundle.chartFiber_smoothAt S B S (fun q => ⟨q, Y.val q⟩)
    p e he hp (Y.smooth p)
  have hs : FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q => TangentBundle.chartFiber B e he ⟨q, Y.val q⟩) p := h
  have hj := hs.postcomp (ContinuousLinearMap.proj j).contDiff
  apply ScalarContDiffAt.congr ((scalarContDiffAt_iff _ _ _ _).mpr hj)
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  rw [TangentBundle.chartFiber_eq S B e he ⟨q, Y.val q⟩ hq,
    LieBrackets.coefficients_eq Y.val e he q hq]
  rfl

/-- Canonical one-upper-slot tensors represent actual smooth vector fields. -/
theorem vectorTensorField_smooth
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (Y : SmoothField B) :
    TensorSmooth B (vectorTensorField Y.val) := by
  intro e he p hp I J
  apply ScalarContDiffAt.congr (vector_component_smoothAt B Y e he p hp (I 0))
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact (component_vectorTensorField B Y.val e he q hq I J).symm

/-- The mixed coordinate derivative on scalar tensors is exactly Xf. -/
theorem scalarTensorField_coordinate_lie
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (D : RealDerivation S) (hD : Represents X D)
    (f : GlobalSmooth S) :
    CoordinateLieDerivative B X (scalarTensorField f.val) (scalarTensorField (D f).val) := by
  intro e he p hp
  refine ⟨LieBrackets.coordinate_derivative_exists X e he p hp, ?_⟩
  intro I J
  obtain ⟨U, hU, hpU, F, hF, heF⟩ :=
    ((scalarContDiffAt_iff _ _ _ _).mp ((mem_globalSmoothAlgebra_iff S _).mp f.property p)).2 e he hp
  have hFd := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  have heC : f.val =ᶠ[𝓝 p] tensorCoefficients B (scalarTensorField f.val) e he I J := by
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact (component_scalarTensorField B f.val e he q hq I J).symm
  have hK : HasScalarCoordinateDerivative e
      (tensorCoefficients B (scalarTensorField f.val) e he I J) p (fderiv ℝ F (e p).val) :=
    ⟨F, hFd, heF.trans heC⟩
  refine ⟨⟨_, hK⟩, ?_⟩
  intro L K hL hK'
  have hKeq := scalar_coordinate_derivative_unique e _ p hp K _ hK' hK
  rw [hKeq, component_scalarTensorField B (D f).val e he p hp]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, add_zero]
  rw [hD p f (globalToGerm S p f) rfl]
  rw [LieBrackets.coefficients_eq X.val e he p hp]
  exact VectorFields.tangent_action_coordinates S B.fiberCoordinates p e he hp (X.val p)
    (globalToGerm S p f) F ⟨⟨U, hU, hpU, hF⟩, Germ.coe_eq.mpr heF⟩

/-- The mixed coordinate derivative on vector tensors is the intrinsic bracket. -/
theorem vectorTensorField_coordinate_lie
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B) :
    CoordinateLieDerivative B X (vectorTensorField Y.val) (vectorTensorField (b X Y).val) := by
  classical
  intro e he p hp
  refine ⟨LieBrackets.coordinate_derivative_exists X e he p hp, ?_⟩
  intro I J
  obtain ⟨H, hH⟩ := LieBrackets.coordinate_derivative_exists Y e he p hp
  obtain ⟨F, hF, heF⟩ := hH
  let P : Euclidean n →L[ℝ] ℝ := ContinuousLinearMap.proj (I 0)
  have heC : (fun q => coefficients B Y.val e he q (I 0)) =ᶠ[𝓝 p]
      tensorCoefficients B (vectorTensorField Y.val) e he I J := by
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact (component_vectorTensorField B Y.val e he q hq I J).symm
  have hK : HasScalarCoordinateDerivative e
      (tensorCoefficients B (vectorTensorField Y.val) e he I J) p (P.comp H) :=
    ⟨fun z => F z (I 0), P.hasFDerivAt.comp (e p).val hF,
      (heF.fun_comp P).trans heC⟩
  refine ⟨⟨_, hK⟩, ?_⟩
  intro L K hL hK'
  have hKeq := scalar_coordinate_derivative_unique e _ p hp K _ hK' hK
  have hH' : HasCoordinateDerivative e (coefficients B Y.val e he) p H := ⟨F, hF, heF⟩
  have hbcoord := (LieBrackets.bracket_coordinates S B b hb X Y).2 e he p hp L H hL hH' (I 0)
  have hval : coefficients B (b X Y).val e he p (I 0) =
      (H (coefficients B X.val e he p) - L (coefficients B Y.val e he p)) (I 0) :=
    hbcoord.trans (LieBrackets.coordinate_commutator_sum L H _ _ (I 0)).symm
  have hexp : coefficients B Y.val e he p = ∑ k : Fin n,
      coefficients B Y.val e he p k • Pi.single k (1 : ℝ) := by
    funext j
    simp [Pi.single_apply]
  have hsum : (∑ k : Fin n, L (Pi.single k 1) (I 0) *
      tensorCoefficients B (vectorTensorField Y.val) e he (Function.update I 0 k) J p) =
      L (coefficients B Y.val e he p) (I 0) := by
    simp only [component_vectorTensorField B Y.val e he p hp, Function.update_self]
    conv_rhs => rw [hexp, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [component_vectorTensorField B (b X Y).val e he p hp, hKeq]
  simpa only [Fin.sum_univ_one, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, hsum, ContinuousLinearMap.comp_apply, P, ContinuousLinearMap.proj_apply,
    Pi.sub_apply] using hval

theorem scalar_tensor : Specs.SmoothManifolds.Ch07.TensorLieDerivative.scalar_tensorType.{u} := by
  intro n a M _ S B X D hD f
  exact ⟨scalarTensorField_smooth B f, scalarTensorField_smooth B (D f),
    scalarTensorField_coordinate_lie B X D hD f⟩

theorem vector_tensor : Specs.SmoothManifolds.Ch07.TensorLieDerivative.vector_tensorType.{u} := by
  intro n a M _ S B b hb X Y
  exact ⟨vectorTensorField_smooth B Y, vectorTensorField_smooth B (b X Y),
    vectorTensorField_coordinate_lie B b hb X Y⟩


noncomputable def coordinateCovariantMonomial {n s : ℕ} (J : Fin s → Fin n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin s) ℝ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (J i))
noncomputable def arrayToCovariantMultilinearMap (n s : ℕ) :
    ((Fin s → Fin n) → ℝ) →ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ where
  toFun a := ∑ J, a J • coordinateCovariantMonomial J
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_smul, Finset.smul_sum]
@[simp] theorem coordinateCovariantMonomial_apply {n s : ℕ} (J : Fin s → Fin n) (v : Fin s → Euclidean n) :
    coordinateCovariantMonomial J v = ∏ i, v i (J i) := rfl
@[simp] theorem coordinateCovariantMonomial_basis {n s : ℕ} (J K : Fin s → Fin n) :
    coordinateCovariantMonomial J (fun i => Pi.single (K i) 1) = if J = K then 1 else 0 := by
  classical
  rw [coordinateCovariantMonomial_apply]
  split_ifs with h
  · subst K
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]
@[simp] theorem arrayToCovariantMultilinearMap_basis (n s : ℕ) (a : (Fin s → Fin n) → ℝ)
    (J : Fin s → Fin n) :
    arrayToCovariantMultilinearMap n s a (fun i => Pi.single (J i) 1) = a J := by
  classical
  change (∑ K, a K • coordinateCovariantMonomial K) _ = _
  simp only [sum_apply, smul_apply,
    coordinateCovariantMonomial_basis, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]


@[simp] theorem arrayToCovariantMultilinearMap_apply (n s : ℕ) (a : (Fin s → Fin n) → ℝ)
    (v : Fin s → Euclidean n) :
    arrayToCovariantMultilinearMap n s a v = ∑ J, a J * ∏ i, v i (J i) := by
  change (∑ K, a K • coordinateCovariantMonomial K) _ = _
  simp only [sum_apply, smul_apply, coordinateCovariantMonomial_apply, smul_eq_mul]

theorem covariantEvaluation_eq_array
    {n s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (A : TensorData.Field S 0 s) (Y : Fin s → Section S) :
    covariantEvaluation A Y p =
      arrayToCovariantMultilinearMap n s (fun J => tensorCoefficients B A e he Fin.elim0 J p)
        (fun i => coefficients B (Y i) e he p) := by
  rw [covariantEvaluation_eq_sum B e he p hp A Y, arrayToCovariantMultilinearMap_apply]
  apply Finset.sum_congr rfl
  intro J _
  exact mul_comm _ _

theorem multilinear_update_coordinates {n s : ℕ}
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ)
    (v : Fin s → Euclidean n) (i : Fin s) (w : Euclidean n) :
    F (Function.update v i w) =
      ∑ k : Fin n, w k * F (Function.update v i (Pi.single k 1)) := by
  classical
  have hw : w = ∑ k : Fin n, w k • Pi.single k 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  change F.toMultilinearMap _ = _
  rw [F.toMultilinearMap.map_update_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact F.toMultilinearMap.map_update_smul _ _ _ _

noncomputable def covariantSlotDerivative {n s : ℕ}
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ)
    (L : Euclidean n →L[ℝ] Euclidean n) :
      ContinuousMultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ :=
  ∑ i : Fin s, F.compContinuousLinearMap
    (Function.update (fun _ : Fin s => ContinuousLinearMap.id ℝ (Euclidean n)) i L)

theorem covariantSlotDerivative_apply {n s : ℕ}
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ)
    (L : Euclidean n →L[ℝ] Euclidean n) (v : Fin s → Euclidean n) :
    covariantSlotDerivative F L v =
      ∑ i : Fin s, F (Function.update v i (L (v i))) := by
  classical
  unfold covariantSlotDerivative
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change F (fun j => Function.update (fun _ : Fin s => ContinuousLinearMap.id ℝ (Euclidean n)) i L j (v j)) = _
  apply congrArg F
  funext j
  by_cases h : j = i <;> simp [h]


theorem covariant_coordinate_extension
    {n s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (A : SmoothTensor B 0 s) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    ∃ (U : Set (Euclidean n)), IsOpen U ∧ (e p).val ∈ U ∧
      ∃ F : Euclidean n → ContinuousMultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
          (fun q => F (e q).val) =ᶠ[𝓝 p]
            (fun q => arrayToCovariantMultilinearMap n s (fun J => tensorCoefficients B A.val e he Fin.elim0 J q)) := by
  classical
  have hex (J : Fin s → Fin n) :=
    ((scalarContDiffAt_iff _ _ _ _).mp (A.smooth e he p hp Fin.elim0 J)).2 e he hp
  choose U hU hpU G hG heq using hex
  let V := ⋂ J, U J
  let F := fun z => arrayToCovariantMultilinearMap n s (fun J => G J z)
  refine ⟨V, isOpen_iInter_of_finite hU, mem_iInter.mpr hpU, F, ?_, ?_⟩
  · exact (arrayToCovariantMultilinearMap n s).toContinuousLinearMap.contDiff.contDiffOn.comp
      (contDiffOn_pi.mpr (fun J => (hG J).mono (iInter_subset U J))) (mapsTo_univ _ _)
  · filter_upwards [Filter.eventually_all.mpr heq] with q hq
    exact congrArg (arrayToCovariantMultilinearMap n s) (funext hq)

theorem linear_apply_eq_sum {n : ℕ} {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (L : Euclidean n →ₗ[ℝ] W) (v : Euclidean n) :
    L v = ∑ k : Fin n, v k • L (Pi.single k 1) := by
  have hv : v = ∑ k : Fin n, v k • Pi.single k 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul]


theorem covariantSlotDerivative_array_basis {n s : ℕ}
    (a : (Fin s → Fin n) → ℝ) (L : Euclidean n →L[ℝ] Euclidean n)
    (J : Fin s → Fin n) :
    covariantSlotDerivative (arrayToCovariantMultilinearMap n s a) L (fun i => Pi.single (J i) 1) =
      ∑ i : Fin s, ∑ k : Fin n, L (Pi.single (J i) 1) k * a (Function.update J i k) := by
  classical
  rw [covariantSlotDerivative_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [multilinear_update_coordinates]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have hv : Function.update (fun j => (Pi.single (J j) 1 : Euclidean n)) i (Pi.single k 1) =
      fun j => (Pi.single (Function.update J i k j) 1 : Euclidean n) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [hv, arrayToCovariantMultilinearMap_basis]

theorem coordinateLie_covariant_equation
    {n s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (A Z : TensorData.Field S 0 s)
    (hZ : CoordinateLieDerivative B X A Z)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source)
    (F : Euclidean n → ContinuousMultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ)
    (hF : DifferentiableAt ℝ F (e p).val)
    (heq : (fun q => F (e q).val) =ᶠ[𝓝 p]
      (fun q => arrayToCovariantMultilinearMap n s (fun J => tensorCoefficients B A e he Fin.elim0 J q)))
    (L : Euclidean n →L[ℝ] Euclidean n)
    (hL : FiniteRegularityData.HasCoordinateDerivative e (coefficients B X.val e he) p L) :
    arrayToCovariantMultilinearMap n s (fun J => tensorCoefficients B Z e he Fin.elim0 J p) =
      fderiv ℝ F (e p).val (coefficients B X.val e he p) + covariantSlotDerivative (F (e p).val) L := by
  classical
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin s => Pi.basisFun ℝ (Fin n))
  intro J
  simp only [Pi.basisFun_apply]
  change arrayToCovariantMultilinearMap n s _ (fun i => Pi.single (J i) 1) =
    (fderiv ℝ F (e p).val (coefficients B X.val e he p) + covariantSlotDerivative (F (e p).val) L)
      (fun i => Pi.single (J i) 1)
  let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Euclidean n) ℝ
    (fun i => Pi.single (J i) 1)
  have hK : HasScalarCoordinateDerivative e (tensorCoefficients B A e he Fin.elim0 J) p
      (E.comp (fderiv ℝ F (e p).val)) := by
    refine ⟨(fun z => F z (fun i => Pi.single (J i) 1)), ?_, ?_⟩
    · exact E.hasFDerivAt.comp (e p).val hF.hasFDerivAt
    · filter_upwards [heq] with q hq
      rw [hq, arrayToCovariantMultilinearMap_basis]
  have h := ((hZ e he p hp).2 Fin.elim0 J).2 L _ hL hK
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at h
  rw [arrayToCovariantMultilinearMap_basis, h]
  change _ = _ + covariantSlotDerivative (F (e p).val) L _
  rw [heq.eq_of_nhds, covariantSlotDerivative_array_basis]
  rfl


theorem continuousMultilinearMap_contDiffOn_apply {n s : ℕ}
    (U : Set (Euclidean n))
    (F : Euclidean n → ContinuousMultilinearMap ℝ (fun _ : Fin s => Euclidean n) ℝ)
    (Y : Fin s → Euclidean n → Euclidean n)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => F z (fun i => Y i z)) U := by
  classical
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ∑ J : Fin s → Fin n,
        (∏ i : Fin s, Y i z (J i)) * F z (fun i => Pi.single (J i) 1)) U := by
    apply ContDiffOn.sum
    intro J _
    apply ContDiffOn.mul
    · apply contDiffOn_prod
      intro i _
      exact (contDiff_apply ℝ (fun _ : Fin n => ℝ) (J i)).contDiffOn.comp
        (hY i) (mapsTo_univ _ _)
    · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Euclidean n) ℝ
        (fun i => Pi.single (J i) 1)).contDiff.contDiffOn.comp hF (mapsTo_univ _ _)
  apply hsum.congr
  intro z _
  exact multilinear_coordinate_expansion (F z).toMultilinearMap (fun i => Y i z)

theorem bracket_coefficients_vector
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source)
    (L K : Euclidean n →L[ℝ] Euclidean n)
    (hL : FiniteRegularityData.HasCoordinateDerivative e (coefficients B X.val e he) p L)
    (hK : FiniteRegularityData.HasCoordinateDerivative e (coefficients B Y.val e he) p K) :
    coefficients B (b X Y).val e he p =
      K (coefficients B X.val e he p) - L (coefficients B Y.val e he p) := by
  have h := (LieBrackets.bracket_coordinates S B b hb X Y).2 e he p hp L K hL hK
  change _ = K.toLinearMap _ - L.toLinearMap _
  rw [linear_apply_eq_sum K.toLinearMap, linear_apply_eq_sum L.toLinearMap]
  ext j
  simpa only [ContinuousLinearMap.coe_coe, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib] using h j


theorem covariant_formula :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.covariant_formulaType.{u} := by
  classical
  intro n a M _ S B b hb X s A Y
  let f : GlobalSmooth S :=
    ⟨covariantEvaluation A.val (fun i => (Y i).val),
      (mem_globalSmoothAlgebra_iff S _).mpr (covariantEvaluation_scalar_smooth B A Y)⟩
  refine ⟨f, rfl, ?_⟩
  intro Z hZ D hD p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := covariant_coordinate_extension B A e he p hp
  choose V hV hpV W hW heW using (fun i => LieBrackets.smooth_field_regular (Y i) e he p hp)
  let z := (e p).val
  let x := coefficients B X.val e he p
  let y := fun i => coefficients B (Y i).val e he p
  let K := fun i => fderiv ℝ (W i) z
  obtain ⟨L, hL⟩ := LieBrackets.coordinate_derivative_exists X e he p hp
  have hFd : DifferentiableAt ℝ F z := (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hWd (i : Fin s) : DifferentiableAt ℝ (W i) z :=
    ((hW i).contDiffAt ((hV i).mem_nhds (hpV i))).differentiableAt (by simp)
  have hWval : (fun i => W i z) = y := by
    funext i
    exact (heW i).eq_of_nhds
  have hK (i : Fin s) : FiniteRegularityData.HasCoordinateDerivative e
      (coefficients B (Y i).val e he) p (K i) :=
    ⟨W i, (hWd i).hasFDerivAt, heW i⟩
  have hbr (i : Fin s) : coefficients B (b X (Y i)).val e he p =
      K i x - L (y i) :=
    bracket_coefficients_vector B b hb X (Y i) e he p hp L (K i) hL (hK i)
  let g := fun w => F w (fun i => W i w)
  have hgnear : (fun q => g (e q).val) =ᶠ[𝓝 p] f.val := by
    filter_upwards [heF, Filter.eventually_all.mpr heW, e.open_source.mem_nhds hp] with q hqF hqW hqe
    change F (e q).val (fun i => W i (e q).val) = covariantEvaluation A.val (fun i => (Y i).val) q
    rw [hqF, funext hqW]
    exact (covariantEvaluation_eq_array B e he q hqe A.val (fun i => (Y i).val)).symm
  have hgerm : GermChartExtension S p e (globalToGerm S p f) g := by
    refine ⟨⟨U ∩ ⋂ i, V i, hU.inter (isOpen_iInter_of_finite hV),
      ⟨hpU, mem_iInter.mpr hpV⟩, ?_⟩, Germ.coe_eq.mpr hgnear⟩
    apply continuousMultilinearMap_contDiffOn_apply _ F W (hF.mono inter_subset_left)
    intro i
    exact (hW i).mono (fun w hw => mem_iInter.mp hw.2 i)
  have hDval : (D f).val p = fderiv ℝ g z x := by
    rw [hD p f (globalToGerm S p f) rfl]
    have h := VectorFields.tangent_action_coordinates S B.fiberCoordinates p e he hp
      (X.val p) (globalToGerm S p f) g hgerm
    simpa [x, coefficients, hp] using h
  have hdiff := congrArg (fun T => T x)
    (hFd.hasFDerivAt.continuousMultilinearMap_apply (fun i => (hWd i).hasFDerivAt)).fderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply, sum_apply] at hdiff
  have hdg : fderiv ℝ g z x = (fderiv ℝ F z x) y +
      ∑ i : Fin s, F z (Function.update y i (K i x)) := by
    simpa [g, K, hWval] using hdiff
  have hZval := congrArg (fun T => T y)
    (coordinateLie_covariant_equation B X A.val Z.val hZ e he p hp F hFd heF L hL)
  have hzformula : covariantEvaluation Z.val (fun i => (Y i).val) p =
      (fderiv ℝ F z x) y + ∑ i : Fin s, F z (Function.update y i (L (y i))) := by
    rw [covariantEvaluation_eq_array B e he p hp Z.val (fun i => (Y i).val)]
    simpa only [add_apply, covariantSlotDerivative_apply] using hZval
  have hsum : (∑ i : Fin s, covariantEvaluation A.val
      (fun j => (Function.update Y i (b X (Y i)) j).val) p) =
      ∑ i : Fin s, F z (Function.update y i (K i x - L (y i))) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [covariantEvaluation_eq_array B e he p hp A.val
      (fun j => (Function.update Y i (b X (Y i)) j).val)]
    rw [← heF.eq_of_nhds]
    congr 1
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
      exact hbr i
    · simp [h, y]
  rw [hzformula, hDval, hdg, hsum]
  simp only [ContinuousMultilinearMap.map_update_sub, Finset.sum_sub_distrib]
  ring


/-- Differentiation of actual pullback has a unique value in the original
mixed tensor fiber. This uses a single genuine differential family for both
candidate values and does not assume a coordinate formula. -/
theorem tensor_flow_derivative_unique
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : MaximalFlowData.CurveFamily M) (A Z W : TensorData.Field S r s) (p : M)
    (hZ : HasTensorFlowDerivative B F A Z p) (hW : HasTensorFlowDerivative B F A W p) :
    Z p = W p := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  apply tensor_coefficients_ext S B r s e he p hp
  intro I J
  exact (hZ.choose_spec.2 hZ.choose hZ.choose_spec.1 e he hp I J).unique
    (hW.choose_spec.2 hZ.choose hZ.choose_spec.1 e he hp I J)

theorem scalar_coordinate_derivative_mul
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n a M) (f g : M → ℝ) (p : M)
    (L K : Euclidean n →L[ℝ] ℝ)
    (hL : HasScalarCoordinateDerivative e f p L)
    (hK : HasScalarCoordinateDerivative e g p K) :
    HasScalarCoordinateDerivative e (fun q => f q * g q) p (g p • L + f p • K) := by
  obtain ⟨F, hF, heF⟩ := hL
  obtain ⟨G, hG, heG⟩ := hK
  have hFp : F (e p).val = f p := heF.eq_of_nhds
  have hGp : G (e p).val = g p := heG.eq_of_nhds
  refine ⟨fun z => F z * G z, ?_, ?_⟩
  · simpa only [hFp, hGp, add_comm] using! hF.mul hG
  · filter_upwards [heF, heG] with q hqF hqG
    rw [hqF, hqG]


theorem component_tensorMultiply
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (r s r' s' : ℕ)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (I : Fin (r+r') → Fin n) (J : Fin (s+s') → Fin n)
    (A : TensorData.Fiber (TangentSpace S p) r s)
    (C : TensorData.Fiber (TangentSpace S p) r' s') :
    component B (r+r') (s+s') e he p I J
        (TensorData.tensorMultiply (TangentSpace S p) r s r' s' A C) =
      component B r s e he p (I ∘ Fin.castAdd r') (J ∘ Fin.castAdd s') A *
      component B r' s' e he p (I ∘ Fin.natAdd r) (J ∘ Fin.natAdd s) C := by
  classical
  by_cases hp : p ∈ e.source
  · have hm : (TensorData.tensorMultiply (TangentSpace S p) r s r' s').compr₂
        (component B (r+r') (s+s') e he p I J) =
        (LinearMap.mul ℝ ℝ).compl₁₂
          (component B r s e he p (I ∘ Fin.castAdd r') (J ∘ Fin.castAdd s'))
          (component B r' s' e he p (I ∘ Fin.natAdd r) (J ∘ Fin.natAdd s)) := by
      ext v lam w mu
      change component B (r+r') (s+s') e he p I J
          (TensorData.tensorMultiply (TangentSpace S p) r s r' s'
            (TensorData.pure v lam) (TensorData.pure w mu)) =
        component B r s e he p (I ∘ Fin.castAdd r') (J ∘ Fin.castAdd s')
          (TensorData.pure v lam) *
        component B r' s' e he p (I ∘ Fin.natAdd r) (J ∘ Fin.natAdd s)
          (TensorData.pure w mu)
      rw [Tensors.tensorMultiply_pure]
      simp only [component, dite_eq_left hp, LinearMap.coe_mk, AddHom.coe_mk,
        Tensors.evaluate_pure, LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply]
      rw [Fin.prod_univ_add, Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      ring
    exact congrArg (fun L => L A C) hm
  · simp [component, hp]


lemma update_comp_castAdd {r r' n : ℕ} (I : Fin (r+r') → Fin n)
    (i : Fin r) (k : Fin n) :
    (Function.update I (Fin.castAdd r' i) k) ∘ Fin.castAdd r' =
      Function.update (I ∘ Fin.castAdd r') i k := by
  classical
  funext j
  by_cases hj : j = i
  · subst j; simp
  · have hs : Fin.castAdd r' j ≠ Fin.castAdd r' i := by simpa
    simp [Function.update_of_ne, hj, hs, Function.comp_apply]

lemma update_castAdd_comp_natAdd {r r' n : ℕ} (I : Fin (r+r') → Fin n)
    (i : Fin r) (k : Fin n) :
    (Function.update I (Fin.castAdd r' i) k) ∘ Fin.natAdd r = I ∘ Fin.natAdd r := by
  classical
  funext j
  have hne : Fin.natAdd r j ≠ Fin.castAdd r' i := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [Function.update_of_ne, hne, Function.comp_apply]

lemma update_comp_natAdd {r r' n : ℕ} (I : Fin (r+r') → Fin n)
    (i : Fin r') (k : Fin n) :
    (Function.update I (Fin.natAdd r i) k) ∘ Fin.natAdd r =
      Function.update (I ∘ Fin.natAdd r) i k := by
  classical
  funext j
  by_cases hj : j = i
  · subst j; simp
  · have hs : Fin.natAdd r j ≠ Fin.natAdd r i := by simpa
    simp [Function.update_of_ne, hj, hs, Function.comp_apply]

lemma update_natAdd_comp_castAdd {r r' n : ℕ} (I : Fin (r+r') → Fin n)
    (i : Fin r') (k : Fin n) :
    (Function.update I (Fin.natAdd r i) k) ∘ Fin.castAdd r' = I ∘ Fin.castAdd r' := by
  classical
  funext j
  have hne : Fin.castAdd r' j ≠ Fin.natAdd r i := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [Function.update_of_ne, hne, Function.comp_apply]


theorem tensor_coordinate_product
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (r s r' s' : ℕ) (A ZA : TensorData.Field S r s) (C ZC : TensorData.Field S r' s')
    (hA : CoordinateLieDerivative B X A ZA) (hC : CoordinateLieDerivative B X C ZC) :
    CoordinateLieDerivative B X
      (fun q => TensorData.tensorMultiply (TangentSpace S q) r s r' s' (A q) (C q))
      (fun q => TensorData.tensorMultiply (TangentSpace S q) r s r' s' (ZA q) (C q) +
        TensorData.tensorMultiply (TangentSpace S q) r s r' s' (A q) (ZC q)) := by
  classical
  intro e he p hp
  obtain ⟨hX, hA⟩ := hA e he p hp
  obtain ⟨_, hC⟩ := hC e he p hp
  refine ⟨hX, ?_⟩
  intro I J
  have eqAC (I J) :
      tensorCoefficients B
        (fun q => TensorData.tensorMultiply (TangentSpace S q) r s r' s' (A q) (C q))
          e he I J =
        (fun q => tensorCoefficients B A e he (I ∘ Fin.castAdd r') (J ∘ Fin.castAdd s') q *
          tensorCoefficients B C e he (I ∘ Fin.natAdd r) (J ∘ Fin.natAdd s) q) := by
    funext q
    exact component_tensorMultiply B r s r' s' e he q I J (A q) (C q)
  obtain ⟨KA, hKA⟩ := (hA (I ∘ Fin.castAdd r') (J ∘ Fin.castAdd s')).1
  obtain ⟨KC, hKC⟩ := (hC (I ∘ Fin.natAdd r) (J ∘ Fin.natAdd s)).1
  let a0 := tensorCoefficients B A e he (I ∘ Fin.castAdd r') (J ∘ Fin.castAdd s') p
  let c0 := tensorCoefficients B C e he (I ∘ Fin.natAdd r) (J ∘ Fin.natAdd s) p
  have hKAC : HasScalarCoordinateDerivative e
      (tensorCoefficients B
        (fun q => TensorData.tensorMultiply (TangentSpace S q) r s r' s' (A q) (C q)) e he I J)
      p (c0 • KA + a0 • KC) := by
    rw [eqAC]
    exact scalar_coordinate_derivative_mul e _ _ p KA KC hKA hKC
  refine ⟨⟨_, hKAC⟩, ?_⟩
  intro L K hL hK
  have hKeq := scalar_coordinate_derivative_unique e _ p hp K (c0 • KA + a0 • KC) hK hKAC
  rw [hKeq]
  have hZA := (hA (I ∘ Fin.castAdd r') (J ∘ Fin.castAdd s')).2 L KA hL hKA
  have hZC := (hC (I ∘ Fin.natAdd r) (J ∘ Fin.natAdd s)).2 L KC hL hKC
  simp only [tensorCoefficients] at hZA hZC
  simp only [tensorCoefficients, map_add, component_tensorMultiply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hZA, hZC]
  simp only [Fin.sum_univ_add, update_comp_castAdd, update_comp_natAdd,
    update_castAdd_comp_natAdd, update_natAdd_comp_castAdd]
  dsimp only [a0, c0, tensorCoefficients]
  simp only [mul_add, add_mul, mul_sub, sub_mul, Finset.sum_mul, Finset.mul_sum]
  simp only [Function.comp_apply]
  ring_nf

theorem tensor_product :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_productType.{u} := by
  intro n r s r' s' a M _ S B X A ZA C ZC hA hC
  exact tensor_coordinate_product B X r s r' s' A.val ZA.val C.val ZC.val hA hC


theorem component_contract
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (r s : ℕ)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M)
    (i : Fin (r+1)) (j : Fin (s+1))
    (I : Fin r → Fin n) (J : Fin s → Fin n)
    (A : TensorData.Fiber (TangentSpace S p) (r+1) (s+1)) :
    component B r s e he p I J (TensorData.contract (TangentSpace S p) i j A) =
      ∑ k : Fin n, component B (r+1) (s+1) e he p
        (i.insertNth k I) (j.insertNth k J) A := by
  classical
  by_cases hp : p ∈ e.source
  · have hm : (component B r s e he p I J).comp (TensorData.contract (TangentSpace S p) i j) =
        ∑ k : Fin n, component B (r+1) (s+1) e he p (i.insertNth k I) (j.insertNth k J) := by
      ext v lam
      change component B r s e he p I J
          (TensorData.contract (TangentSpace S p) i j (TensorData.pure v lam)) =
        (∑ k : Fin n, component B (r+1) (s+1) e he p (i.insertNth k I) (j.insertNth k J))
          (TensorData.pure v lam)
      rw [Tensors.contract_pure]
      simp only [map_smul, smul_eq_mul, LinearMap.sum_apply, component, dite_eq_left hp,
        LinearMap.coe_mk, AddHom.coe_mk, Tensors.evaluate_pure,
        LinearMap.comp_apply, LinearMap.proj_apply]
      simp_rw [Fin.prod_univ_succAbove _ i, Fin.prod_univ_succAbove _ j]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      let c := B.fiberCoordinates.equiv e he p hp
      have hv : ∑ k : Fin n, c (v i) k • c.symm (Pi.single k 1) = v i := by
        apply c.injective
        simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
        ext k
        simp [Pi.single_apply]
      have hpair : (∑ k : Fin n, c (v i) k * lam j (c.symm (Pi.single k 1))) = lam j (v i) := by
        simpa only [map_sum, map_smul, smul_eq_mul] using congrArg (lam j) hv
      change lam j (v i) *
          ((∏ l, c (v (i.succAbove l)) (I l)) *
            ∏ l, lam (j.succAbove l) (c.symm (Pi.single (J l) 1))) =
        ∑ k : Fin n,
          (c (v i) k * ∏ l, c (v (i.succAbove l)) (I l)) *
          (lam j (c.symm (Pi.single k 1)) *
            ∏ l, lam (j.succAbove l) (c.symm (Pi.single (J l) 1)))
      rw [← hpair, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using congrArg (fun L => L A) hm
  · simp [component, hp]


theorem scalar_coordinate_derivative_sum
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {ι : Type*} [Fintype ι]
    (e : ModelChart n a M) (f : ι → M → ℝ) (p : M)
    (K : ι → Euclidean n →L[ℝ] ℝ)
    (hK : ∀ i, HasScalarCoordinateDerivative e (f i) p (K i)) :
    HasScalarCoordinateDerivative e (fun q => ∑ i, f i q) p (∑ i, K i) := by
  classical
  choose F hF hEq using hK
  refine ⟨fun z => ∑ i, F i z, ?_, ?_⟩
  · convert (HasFDerivAt.sum (u := Finset.univ) (fun i _ => hF i)) using 1 <;>
      ext <;> simp
  · filter_upwards [Filter.eventually_all.2 hEq] with q hq
    exact Finset.sum_congr rfl (fun i _ => hq i)

lemma sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

theorem tensor_coordinate_contraction
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (r s : ℕ) (i : Fin (r+1)) (j : Fin (s+1))
    (A Z : TensorData.Field S (r+1) (s+1)) (hA : CoordinateLieDerivative B X A Z) :
    CoordinateLieDerivative B X
      (fun q => TensorData.contract (TangentSpace S q) i j (A q))
      (fun q => TensorData.contract (TangentSpace S q) i j (Z q)) := by
  classical
  intro e he p hp
  obtain ⟨hX, hA⟩ := hA e he p hp
  refine ⟨hX, ?_⟩
  intro I J
  have eqA (I J) :
      tensorCoefficients B (fun q => TensorData.contract (TangentSpace S q) i j (A q)) e he I J =
      (fun q => ∑ k : Fin n, tensorCoefficients B A e he (i.insertNth k I) (j.insertNth k J) q) := by
    funext q
    exact component_contract B r s e he q i j I J (A q)
  choose K hK using fun k : Fin n => (hA (i.insertNth k I) (j.insertNth k J)).1
  have hKC : HasScalarCoordinateDerivative e
      (tensorCoefficients B (fun q => TensorData.contract (TangentSpace S q) i j (A q)) e he I J)
      p (∑ k, K k) := by
    rw [eqA]
    exact scalar_coordinate_derivative_sum e _ p K hK
  refine ⟨⟨_, hKC⟩, ?_⟩
  intro L KC hL hKCon
  have hKeq := scalar_coordinate_derivative_unique e _ p hp KC (∑ k, K k) hKCon hKC
  rw [hKeq]
  have hZ (k : Fin n) := (hA (i.insertNth k I) (j.insertNth k J)).2 L (K k) hL (hK k)
  simp only [tensorCoefficients] at hZ
  simp only [tensorCoefficients, component_contract, sum_apply]
  simp_rw [hZ]
  simp_rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    Fin.update_insertNth, ← Fin.insertNth_update,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hdiag :
      (∑ k : Fin n, ∑ l : Fin n, L (Pi.single l 1) k *
        component B (r+1) (s+1) e he p (i.insertNth l I) (j.insertNth k J) (A p)) =
      ∑ k : Fin n, ∑ l : Fin n, L (Pi.single k 1) l *
        component B (r+1) (s+1) e he p (i.insertNth k I) (j.insertNth l J) (A p) := by
    rw [Finset.sum_comm]
  have hu :
      (∑ k : Fin n, ∑ u : Fin r, ∑ l : Fin n, L (Pi.single l 1) (I u) *
        component B (r+1) (s+1) e he p (i.insertNth k (Function.update I u l))
          (j.insertNth k J) (A p)) =
      ∑ u : Fin r, ∑ l : Fin n, L (Pi.single l 1) (I u) *
        ∑ k : Fin n, component B (r+1) (s+1) e he p
          (i.insertNth k (Function.update I u l)) (j.insertNth k J) (A p) := by
    simp only [Finset.mul_sum]
    rw [sum_rotate]
  have hl :
      (∑ k : Fin n, ∑ u : Fin s, ∑ l : Fin n, L (Pi.single (J u) 1) l *
        component B (r+1) (s+1) e he p (i.insertNth k I)
          (j.insertNth k (Function.update J u l)) (A p)) =
      ∑ u : Fin s, ∑ l : Fin n, L (Pi.single (J u) 1) l *
        ∑ k : Fin n, component B (r+1) (s+1) e he p
          (i.insertNth k I) (j.insertNth k (Function.update J u l)) (A p) := by
    simp only [Finset.mul_sum]
    rw [sum_rotate]
  rw [hdiag, hu, hl]
  ring

theorem tensor_contraction :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_contractionType.{u} := by
  intro n r s a M _ S B X i j A Z hA
  exact tensor_coordinate_contraction B X r s i j A.val Z.val hA


section MixedPathCalculus
open TensorData
set_option maxHeartbeats 1000000

noncomputable def mixedCoordinateArguments {n r s : ℕ}
    (I : Fin r → Fin n) (J : Fin s → Fin n) : Fin r ⊕ Fin s → Euclidean n :=
  Sum.rec (fun i => Pi.single (I i) 1) (fun j => Pi.single (J j) 1)

noncomputable def mixedPathArguments {n r s : ℕ}
    (H K : ℝ → Euclidean n →L[ℝ] Euclidean n)
    (I : Fin r → Fin n) (J : Fin s → Fin n) (t : ℝ) : Fin r ⊕ Fin s → Euclidean n :=
  Sum.rec (fun i k => K t (Pi.single k 1) (I i))
    (fun j => H t (Pi.single (J j) 1))

/-- Replacing an upper argument by a matrix row expands into the upper-index sum. -/
theorem mixed_update_upper
    {n r s : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin r ⊕ Fin s => Euclidean n) ℝ)
    (I : Fin r → Fin n) (J : Fin s → Fin n) (i : Fin r)
    (L : Euclidean n →L[ℝ] Euclidean n) :
    A (Function.update (mixedCoordinateArguments I J) (.inl i)
      (fun k => L (Pi.single k 1) (I i))) =
      ∑ k : Fin n, L (Pi.single k 1) (I i) *
        A (mixedCoordinateArguments (Function.update I i k) J) := by
  classical
  have hexp : (fun k => L (Pi.single k 1) (I i)) = ∑ k : Fin n,
      L (Pi.single k 1) (I i) • Pi.single k (1 : ℝ) := by
    funext j
    simp [Pi.single_apply]
  conv_lhs => rw [hexp]
  change A.toMultilinearMap _ = _
  rw [A.toMultilinearMap.map_update_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [A.toMultilinearMap.map_update_smul]
  simp only [smul_eq_mul]
  change _ * A _ = _ * A _
  congr 2
  funext slot
  cases slot with
  | inl j => simp only [mixedCoordinateArguments, Function.update_apply, Sum.inl.injEq]; split_ifs <;> rfl
  | inr j => simp [mixedCoordinateArguments]

/-- Replacing a lower argument by a matrix column expands into the lower-index sum. -/
theorem mixed_update_lower
    {n r s : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin r ⊕ Fin s => Euclidean n) ℝ)
    (I : Fin r → Fin n) (J : Fin s → Fin n) (j : Fin s)
    (L : Euclidean n →L[ℝ] Euclidean n) :
    A (Function.update (mixedCoordinateArguments I J) (.inr j) (L (Pi.single (J j) 1))) =
      ∑ k : Fin n, L (Pi.single (J j) 1) k *
        A (mixedCoordinateArguments I (Function.update J j k)) := by
  classical
  have hexp : L (Pi.single (J j) 1) = ∑ k : Fin n,
      L (Pi.single (J j) 1) k • Pi.single k (1 : ℝ) := by
    funext l
    simp [Pi.single_apply]
  conv_lhs => rw [hexp]
  change A.toMultilinearMap _ = _
  rw [A.toMultilinearMap.map_update_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [A.toMultilinearMap.map_update_smul]
  simp only [smul_eq_mul]
  change _ * A _ = _ * A _
  congr 2
  funext slot
  cases slot with
  | inl i => simp [mixedCoordinateArguments]
  | inr i => simp only [mixedCoordinateArguments, Function.update_apply, Sum.inr.injEq]; split_ifs <;> rfl

/-- Differentiate genuine inverse-row/forward-column transport in a fixed coordinate
space. The identities at zero and the two explicit Jacobian derivatives determine
the upper minus signs and lower plus signs. -/
theorem mixed_multilinear_path_derivative
    {n r s : ℕ}
    (A : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin r ⊕ Fin s => Euclidean n) ℝ)
    (A' : ContinuousMultilinearMap ℝ (fun _ : Fin r ⊕ Fin s => Euclidean n) ℝ)
    (H K : ℝ → Euclidean n →L[ℝ] Euclidean n) (L : Euclidean n →L[ℝ] Euclidean n)
    (hA : HasDerivAt A A' 0) (hH : HasDerivAt H L 0) (hK : HasDerivAt K (-L) 0)
    (hH0 : H 0 = ContinuousLinearMap.id ℝ (Euclidean n))
    (hK0 : K 0 = ContinuousLinearMap.id ℝ (Euclidean n))
    (I : Fin r → Fin n) (J : Fin s → Fin n) :
    HasDerivAt (fun t => A t (mixedPathArguments H K I J t))
      (A' (mixedCoordinateArguments I J) -
        (∑ i : Fin r, ∑ k : Fin n, L (Pi.single k 1) (I i) *
          A 0 (mixedCoordinateArguments (Function.update I i k) J)) +
        (∑ j : Fin s, ∑ k : Fin n, L (Pi.single (J j) 1) k *
          A 0 (mixedCoordinateArguments I (Function.update J j k)))) 0 := by
  classical
  let V' : Fin r ⊕ Fin s → Euclidean n :=
    Sum.rec (fun i k => -L (Pi.single k 1) (I i))
      (fun j => L (Pi.single (J j) 1))
  have hV : ∀ slot, HasDerivAt (fun t => mixedPathArguments H K I J t slot) (V' slot) 0 := by
    intro slot
    cases slot with
    | inl i =>
      apply hasDerivAt_pi.mpr
      intro k
      have hk := hK.clm_apply (hasDerivAt_const (0 : ℝ) (Pi.single k (1 : ℝ)))
      have hi := (ContinuousLinearMap.proj (I i) : Euclidean n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hk
      simpa [mixedPathArguments, V', Function.comp_def] using hi
    | inr j =>
      have hj := hH.clm_apply (hasDerivAt_const (0 : ℝ) (Pi.single (J j) (1 : ℝ)))
      simpa [mixedPathArguments, V'] using hj
  have hz : mixedPathArguments H K I J 0 = mixedCoordinateArguments I J := by
    funext slot k
    cases slot <;> simp [mixedPathArguments, mixedCoordinateArguments, hH0, hK0, Pi.single_apply, eq_comm]
  have hd := (hA.hasFDerivAt.continuousMultilinearMap_apply
    (fun slot => (hV slot).hasFDerivAt)).hasDerivAt
  have hup (i : Fin r) : A 0 (Function.update (mixedCoordinateArguments I J) (.inl i) (V' (.inl i))) =
      -(∑ k : Fin n, L (Pi.single k 1) (I i) *
        A 0 (mixedCoordinateArguments (Function.update I i k) J)) := by
    simpa only [V', neg_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] using
      mixed_update_upper (A 0) I J i (-L)
  have hlo (j : Fin s) : A 0 (Function.update (mixedCoordinateArguments I J) (.inr j) (V' (.inr j))) =
      ∑ k : Fin n, L (Pi.single (J j) 1) k *
        A 0 (mixedCoordinateArguments I (Function.update J j k)) :=
    mixed_update_lower (A 0) I J j L
  have hd' : HasDerivAt (fun t => A t (mixedPathArguments H K I J t))
      (A' (mixedCoordinateArguments I J) + ∑ slot : Fin r ⊕ Fin s,
        A 0 (Function.update (mixedCoordinateArguments I J) slot (V' slot))) 0 := by
    convert hd using 1
    simp [hz]
  convert hd' using 1
  simp only [Fintype.sum_sum_type, hup, hlo, Finset.sum_neg_distrib]
  ring

/-- A coordinate monomial, continuous multilinear in the slot arguments. -/
noncomputable def arrayMonomial {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → Fin n) :
    ContinuousMultilinearMap ℝ (fun _ : ι => Euclidean n) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (q i))

@[simp] theorem arrayMonomial_apply {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → Fin n) (v : ι → Euclidean n) :
    arrayMonomial q v = ∏ i, v i (q i) := rfl

/-- A finite coordinate array as a continuous multilinear form. -/
noncomputable def arrayForm {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : (ι → Fin n) → ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : ι => Euclidean n) ℝ := by
  classical
  exact ∑ q : ι → Fin n, C q • arrayMonomial q

@[simp] theorem arrayForm_apply {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : (ι → Fin n) → ℝ) (v : ι → Euclidean n) :
    arrayForm C v = ∑ q : ι → Fin n, C q * ∏ i, v i (q i) := by
  classical
  simp [arrayForm]

@[simp] theorem arrayMonomial_basis {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q j : ι → Fin n) :
    arrayMonomial q (fun i => Pi.single (j i) (1 : ℝ)) = if q = j then 1 else 0 := by
  classical
  rw [arrayMonomial_apply]
  by_cases h : q = j
  · subst q
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi])

@[simp] theorem arrayForm_basis {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : (ι → Fin n) → ℝ) (j : ι → Fin n) :
    arrayForm C (fun i => Pi.single (j i) (1 : ℝ)) = C j := by
  classical
  simp only [arrayForm, sum_apply, smul_apply, smul_eq_mul, arrayMonomial_basis]
  simp

/-- Coordinatewise time differentiation gives differentiation in the multilinear-form space. -/
theorem arrayForm_hasDerivAt {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℝ → (ι → Fin n) → ℝ) (C' : (ι → Fin n) → ℝ)
    (hC : ∀ q, HasDerivAt (fun t => C t q) (C' q) 0) :
    HasDerivAt (fun t => arrayForm (C t)) (arrayForm C') 0 := by
  classical
  have hd := HasDerivAt.sum (u := Finset.univ) (fun q _ => (hC q).smul_const (arrayMonomial q))
  convert hd using 1
  · funext t
    simp only [arrayForm, Finset.sum_apply]
  · rfl

@[simp] theorem arrayForm_mixed_basis {n r s : ℕ}
    (C : (Fin r ⊕ Fin s → Fin n) → ℝ) (I : Fin r → Fin n) (J : Fin s → Fin n) :
    arrayForm C (mixedCoordinateArguments I J) = C (Sum.rec I J) := by
  convert arrayForm_basis C (Sum.rec I J) using 1
  congr 1
  funext slot
  cases slot <;> rfl

/-- The complete mixed transport coefficient expression has the usual signed derivative. -/
theorem mixed_array_path_derivative
    {n r s : ℕ} (C : ℝ → (Fin r ⊕ Fin s → Fin n) → ℝ)
    (C' : (Fin r ⊕ Fin s → Fin n) → ℝ)
    (H K : ℝ → Euclidean n →L[ℝ] Euclidean n) (L : Euclidean n →L[ℝ] Euclidean n)
    (hC : ∀ q, HasDerivAt (fun t => C t q) (C' q) 0)
    (hH : HasDerivAt H L 0) (hK : HasDerivAt K (-L) 0)
    (hH0 : H 0 = ContinuousLinearMap.id ℝ (Euclidean n))
    (hK0 : K 0 = ContinuousLinearMap.id ℝ (Euclidean n))
    (I : Fin r → Fin n) (J : Fin s → Fin n) :
    HasDerivAt
      (fun t => ∑ q : Fin r ⊕ Fin s → Fin n, C t q *
        ((∏ i : Fin r, K t (Pi.single (q (.inl i)) 1) (I i)) *
          ∏ j : Fin s, H t (Pi.single (J j) 1) (q (.inr j))))
      (C' (Sum.rec I J) -
        (∑ i : Fin r, ∑ k : Fin n, L (Pi.single k 1) (I i) *
          C 0 (Sum.rec (Function.update I i k) J)) +
        (∑ j : Fin s, ∑ k : Fin n, L (Pi.single (J j) 1) k *
          C 0 (Sum.rec I (Function.update J j k)))) 0 := by
  have hd := mixed_multilinear_path_derivative (fun t => arrayForm (C t)) (arrayForm C')
    H K L (arrayForm_hasDerivAt C C' hC) hH hK hH0 hK0 I J
  simp only [arrayForm_mixed_basis] at hd
  simpa only [arrayForm_apply, Fintype.prod_sum_type, mixedPathArguments] using hd

noncomputable def mixedTupleIndex (n r s : ℕ) :
    (Fin r ⊕ Fin s → Fin n) ≃ Fin (n^r * n^s) :=
  ((Equiv.sumArrowEquivProdArrow (Fin r) (Fin s) (Fin n)).trans
    (Equiv.prodCongr (powerIndex n r) (powerIndex n s))).trans finProdFinEquiv

@[simp] theorem mixedTupleIndex_apply {n r s : ℕ} (q : Fin r ⊕ Fin s → Fin n) :
    mixedTupleIndex n r s q = finProdFinEquiv
      (powerIndex n r (fun i => q (.inl i)), powerIndex n s (fun j => q (.inr j))) := rfl

@[simp] theorem mixedTupleIndex_sum {n r s : ℕ} (I : Fin r → Fin n) (J : Fin s → Fin n) :
    mixedTupleIndex n r s (Sum.rec I J) = finProdFinEquiv (powerIndex n r I, powerIndex n s J) := rfl

/-- The fixed Euclidean tensor pullback is exactly the inverse-row/forward-column
finite coordinate expression. This bridge uses the genuine algebraic tensor transport. -/
theorem mixedTransport_coordinate_array
    {n r s : ℕ} (F : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (H K : Euclidean n →L[ℝ] Euclidean n)
    (hH : ∀ v, H v = F v) (hK : ∀ v, K v = F.symm v)
    (A : Fiber (Euclidean n) r s) (I : Fin r → Fin n) (J : Fin s → Fin n) :
    Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s
        (mixedTransport r s F A) (finProdFinEquiv (powerIndex n r I, powerIndex n s J)) =
      ∑ q : Fin r ⊕ Fin s → Fin n,
        Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s A (mixedTupleIndex n r s q) *
          ((∏ i : Fin r, K (Pi.single (q (.inl i)) 1) (I i)) *
            ∏ j : Fin s, H (Pi.single (J j) 1) (q (.inr j))) := by
  classical
  rw [Tensors.mixedTransport_coefficients (LinearEquiv.refl ℝ (Euclidean n))
    (LinearEquiv.refl ℝ (Euclidean n)) F A]
  symm
  apply Fintype.sum_equiv (mixedTupleIndex n r s)
  intro q
  simp [mixedTupleIndex_apply, LinearEquiv.refl_apply, hH, hK]

/-- General mixed tensor pullback differentiation in a fixed Euclidean model.
The tensor path is differentiated only through its coordinate entries, so no norm
is introduced on the original algebraic tensor products. -/
theorem mixedTransport_path_derivative
    {n r s : ℕ} (A : ℝ → Fiber (Euclidean n) r s) (A' : Fiber (Euclidean n) r s)
    (F : ℝ → Euclidean n ≃ₗ[ℝ] Euclidean n)
    (H K : ℝ → Euclidean n →L[ℝ] Euclidean n) (L : Euclidean n →L[ℝ] Euclidean n)
    (hFH : ∀ t v, H t v = F t v) (hFK : ∀ t v, K t v = (F t).symm v)
    (hA : ∀ (I : Fin r → Fin n) (J : Fin s → Fin n),
      HasDerivAt (fun t => Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s
          (A t) (finProdFinEquiv (powerIndex n r I, powerIndex n s J)))
        (Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s A'
          (finProdFinEquiv (powerIndex n r I, powerIndex n s J))) 0)
    (hH : HasDerivAt H L 0) (hK : HasDerivAt K (-L) 0)
    (hH0 : H 0 = ContinuousLinearMap.id ℝ (Euclidean n))
    (hK0 : K 0 = ContinuousLinearMap.id ℝ (Euclidean n))
    (I : Fin r → Fin n) (J : Fin s → Fin n) :
    HasDerivAt (fun t =>
      Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s
        (mixedTransport r s (F t) (A t))
        (finProdFinEquiv (powerIndex n r I, powerIndex n s J)))
      (Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s A'
          (finProdFinEquiv (powerIndex n r I, powerIndex n s J)) -
        (∑ i : Fin r, ∑ k : Fin n, L (Pi.single k 1) (I i) *
          Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s (A 0)
            (finProdFinEquiv (powerIndex n r (Function.update I i k), powerIndex n s J))) +
        (∑ j : Fin s, ∑ k : Fin n, L (Pi.single (J j) 1) k *
          Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s (A 0)
            (finProdFinEquiv (powerIndex n r I, powerIndex n s (Function.update J j k))))) 0 := by
  let C (t : ℝ) (q : Fin r ⊕ Fin s → Fin n) :=
    Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s (A t) (mixedTupleIndex n r s q)
  let C' (q : Fin r ⊕ Fin s → Fin n) :=
    Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s A' (mixedTupleIndex n r s q)
  have hC : ∀ q, HasDerivAt (fun t => C t q) (C' q) 0 := by
    intro q
    exact hA (fun i => q (.inl i)) (fun j => q (.inr j))
  have hd := mixed_array_path_derivative C C' H K L hC hH hK hH0 hK0 I J
  have heq : (fun t => Tensors.mixedCoordinates (LinearEquiv.refl ℝ (Euclidean n)) r s
      (mixedTransport r s (F t) (A t)) (finProdFinEquiv (powerIndex n r I, powerIndex n s J))) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∑ q : Fin r ⊕ Fin s → Fin n, C t q *
        ((∏ i : Fin r, K t (Pi.single (q (.inl i)) 1) (I i)) *
          ∏ j : Fin s, H t (Pi.single (J j) 1) (q (.inr j)))) :=
    Eventually.of_forall (fun t => mixedTransport_coordinate_array (F t) (H t) (K t)
      (hFH t) (hFK t) (A t) I J)
  simpa only [C, C', mixedTupleIndex_sum] using hd.congr_of_eventuallyEq heq


end MixedPathCalculus

theorem fixed_chart_lie_local_representation
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (A : SmoothTensor B r s) (W : TensorData.Field S r s)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hW : ∀ (q : M), q ∈ e.source →
      ∀ (I : Fin r → Fin n) (J : Fin s → Fin n)
        (L : Euclidean n →L[ℝ] Euclidean n) (K : Euclidean n →L[ℝ] ℝ),
        HasCoordinateDerivative e (coefficients B X.val e he) q L →
        HasScalarCoordinateDerivative e (tensorCoefficients B A.val e he I J) q K →
        tensorCoefficients B W e he I J q =
          K (coefficients B X.val e he q) -
            (∑ i : Fin r, ∑ k : Fin n, L (Pi.single k 1) (I i) *
              tensorCoefficients B A.val e he (Function.update I i k) J q) +
            (∑ j : Fin s, ∑ k : Fin n, L (Pi.single (J j) 1) k *
              tensorCoefficients B A.val e he I (Function.update J j k) q))
    (p : M) (hp : p ∈ e.source) :
    ∃ (U : Set (Euclidean n)) (H : Euclidean n → Euclidean n)
      (G : Euclidean n → (Fin r → Fin n) → (Fin s → Fin n) → ℝ),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) H U ∧
      (∀ I J, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => G z I J) U) ∧
      ∀ᶠ q in 𝓝 p, ∀ I J,
        tensorCoefficients B W e he I J q = arrayLie n r s H G (e q).val I J := by
  classical
  have hAcoord : FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q I J => tensorCoefficients B A.val e he I J q) p := by
    apply FrameData.VectorSmoothAt.pi
    intro I
    apply FrameData.VectorSmoothAt.pi
    intro J
    exact (scalarContDiffAt_iff _ _ _ _).mp (A.smooth e he p hp I J)
  obtain ⟨U, hU, hpU, H, hH, heH⟩ := LieBrackets.smooth_field_regular X e he p hp
  obtain ⟨V, hV, hpV, G, hG, heG⟩ := hAcoord.2 e he hp
  have hHu := hH.mono (inter_subset_left : U ∩ V ⊆ U)
  have hGu (I) (J) := ((contDiffOn_pi.mp (contDiffOn_pi.mp hG I)) J).mono
    (inter_subset_right : U ∩ V ⊆ V)
  refine ⟨U ∩ V, H, G, hU.inter hV, ⟨hpU, hpV⟩, hHu, hGu, ?_⟩
  have hc : ContinuousAt (fun q => (e q).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  filter_upwards [e.open_source.mem_nhds hp,
    hc.preimage_mem_nhds ((hU.inter hV).mem_nhds ⟨hpU, hpV⟩),
    eventually_eventually_nhds.mpr heH, eventually_eventually_nhds.mpr heG]
    with q hqe hqU hqH hqG
  have hqH' : (fun y => H (e y).val) =ᶠ[𝓝 q] coefficients B X.val e he := hqH
  have hqG' : (fun y => G (e y).val) =ᶠ[𝓝 q]
      (fun y I J => tensorCoefficients B A.val e he I J y) := hqG
  intro I J
  have hHd := (hHu.contDiffAt ((hU.inter hV).mem_nhds hqU)).differentiableAt (by simp)
  have hGd (I) (J) := ((hGu I J).contDiffAt ((hU.inter hV).mem_nhds hqU)).differentiableAt (by simp)
  have hHq : H (e q).val = coefficients B X.val e he q := hqH'.eq_of_nhds
  have hGq (I) (J) : G (e q).val I J = tensorCoefficients B A.val e he I J q :=
    congrFun (congrFun hqG'.eq_of_nhds I) J
  have hL : HasCoordinateDerivative e (coefficients B X.val e he) q
      (fderiv ℝ H (e q).val) := ⟨H, hHd.hasFDerivAt, hqH⟩
  have hK : HasScalarCoordinateDerivative e (tensorCoefficients B A.val e he I J) q
      (fderiv ℝ (fun z => G z I J) (e q).val) :=
    ⟨(fun z => G z I J), (hGd I J).hasFDerivAt,
      hqG.mono (fun y hy => congrFun (congrFun hy I) J)⟩
  have h := hW q hqe I J _ _ hL hK
  simpa only [arrayLie, hHq, hGq] using h

theorem fixed_chart_lie_smoothAt
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (T : TensorData.TensorBundle S r s)
    (X : SmoothField B) (A : SmoothTensor B r s) (W : TensorData.Field S r s)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hW : ∀ (q : M), q ∈ e.source →
      ∀ (I : Fin r → Fin n) (J : Fin s → Fin n)
        (L : Euclidean n →L[ℝ] Euclidean n) (K : Euclidean n →L[ℝ] ℝ),
        HasCoordinateDerivative e (coefficients B X.val e he) q L →
        HasScalarCoordinateDerivative e (tensorCoefficients B A.val e he I J) q K →
        tensorCoefficients B W e he I J q =
          K (coefficients B X.val e he q) -
            (∑ i : Fin r, ∑ k : Fin n, L (Pi.single k 1) (I i) *
              tensorCoefficients B A.val e he (Function.update I i k) J q) +
            (∑ j : Fin s, ∑ k : Fin n, L (Pi.single (J j) 1) k *
              tensorCoefficients B A.val e he I (Function.update J j k) q))
    (p : M) (hp : p ∈ e.source) :
    let := (TensorData.tensorSpace T).topology
    ManifoldContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
      (TensorData.tensorSpace T).bundle.totalManifold.smoothStructure.val
      (fun q => (⟨q,W q⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
        (fun q => TensorData.Fiber (TangentSpace S q) r s))) p := by
  classical
  let := (TensorData.tensorSpace T).topology
  obtain ⟨U, H, G, hU, hpU, hH, hG, heW⟩ :=
    fixed_chart_lie_local_representation B X A W e he hW p hp
  have hscalar (I : Fin r → Fin n) (J : Fin s → Fin n) :
      ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
        (tensorCoefficients B W e he I J) p := by
    apply scalarContDiffAt_of_chart S.smoothStructure.property.1 he hp
    refine ⟨U, hU, hpU, (fun z => arrayLie n r s H G z I J),
      arrayLie_smooth n r s U hU H G hH hG I J, ?_⟩
    exact heW.mono (fun q hq => (hq I J).symm)
  let i : BundleOperationsData.TangentIndex S := ⟨e,he⟩
  let v : M → Euclidean (n^r*n^s) := fun q =>
    (((TensorData.tensorSpace T).bundle.trivialization (i,i)) ⟨q,W q⟩).2
  have hv : FrameData.VectorSmoothAt S.smoothStructure.val v p := by
    apply FrameData.VectorSmoothAt.pi
    intro k
    obtain ⟨⟨kr,ks⟩, rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨I,rfl⟩ := (TensorData.powerIndex n r).surjective kr
    obtain ⟨J,rfl⟩ := (TensorData.powerIndex n s).surjective ks
    apply FrameData.VectorSmoothAt.congr ((scalarContDiffAt_iff _ _ _ _).mp (hscalar I J))
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact component_eq_bundle_coordinate B T e he q hq I J (W q)
  exact Frames.smoothAt_from_trivialization (TensorData.tensorSpace T).bundle
    S.smoothStructure.property.1 (i,i)
    (by rw [Tensors.tensorSpace_diagonal_baseSet]; exact hp)
    (manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val
      S.smoothStructure.property.1 p) hv (fun _ => rfl) Filter.EventuallyEq.rfl


/-- A chart determines its local candidate without assuming overlap compatibility. -/
noncomputable def chartLieSection
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (A : SmoothTensor B r s)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) : TensorData.Field S r s := by
  classical
  exact fun p => if hp : p ∈ e.source then
    (chart_coordinate_lie_exists B X A e he p hp).choose else 0

theorem chartLieSection_component
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (A : SmoothTensor B r s)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (I : Fin r → Fin n) (J : Fin s → Fin n)
    (L : Euclidean n →L[ℝ] Euclidean n) (K : Euclidean n →L[ℝ] ℝ)
    (hL : HasCoordinateDerivative e (coefficients B X.val e he) p L)
    (hK : HasScalarCoordinateDerivative e (tensorCoefficients B A.val e he I J) p K) :
    tensorCoefficients B (chartLieSection B X A e he) e he I J p =
      K (coefficients B X.val e he p) -
        (∑ i : Fin r, ∑ k : Fin n, L (Pi.single k 1) (I i) *
          tensorCoefficients B A.val e he (Function.update I i k) J p) +
        (∑ j : Fin s, ∑ k : Fin n, L (Pi.single (J j) 1) k *
          tensorCoefficients B A.val e he I (Function.update J j k) p) := by
  simp only [tensorCoefficients, chartLieSection, dite_eq_left hp]
  exact (chart_coordinate_lie_exists B X A e he p hp).choose_spec.1 I J L K hL hK

theorem chartLieSection_smoothAt
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (T : TensorData.TensorBundle S r s)
    (X : SmoothField B) (A : SmoothTensor B r s)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    let := (TensorData.tensorSpace T).topology
    ManifoldSmoothAt S.smoothStructure.val
      (TensorData.tensorSpace T).bundle.totalManifold.smoothStructure.val
      (fun q => (⟨q,chartLieSection B X A e he q⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
        (fun q => TensorData.Fiber (TangentSpace S q) r s))) p :=
  fixed_chart_lie_smoothAt B T X A _ e he
    (fun q hq I J L K hL hK => chartLieSection_component B X A e he q hq I J L K hL hK) p hp

/-- Any smooth field can be replaced near an interior point by a globally
boundary-tangent field. No tangent condition is imposed on the original field. -/
theorem exists_tangent_field_eq_near_interior
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (p : M) (hp : p ∈ BoundaryData.manifoldInterior S) :
    ∃ Y : SmoothField B, BoundaryFlowData.IsTangentToBoundary Y ∧ ∀ᶠ q in 𝓝 p, Y.val q = X.val q := by
  obtain ⟨χ, hχ, _, heχ, hsχ, _⟩ := exists_local_bump S p
    (BoundaryData.manifoldInterior S) (isOpen_manifoldInterior S) hp
  let f : GlobalSmooth S := ⟨χ, (mem_globalSmoothAlgebra_iff S _).mpr hχ⟩
  obtain ⟨Y,hY⟩ := LieBrackets.smooth_field_mul f X
  refine ⟨Y, ?_, ?_⟩
  · intro q hq e he hqe
    have hzero : χ q = 0 := by
      by_contra hn
      have hi := hsχ (subset_closure hn)
      change q ∈ manifoldInterior S at hi
      rw [← compl_intrinsicBoundary S] at hi
      exact hi hq
    rw [hY q]
    change BoundaryFlowData.FaceTangent n a (B.fiberCoordinates.equiv e he q hqe (χ q • X.val q))
    rw [hzero, zero_smul, map_zero]
    cases n <;> cases a <;> simp [BoundaryFlowData.FaceTangent]
  · filter_upwards [heχ] with q hq
    rw [hY q]
    change χ q • X.val q = X.val q
    rw [hq, one_smul]


theorem chartLieSection_eq_of_field_eq_near
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X Y : SmoothField B) (A : SmoothTensor B r s)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hXY : ∀ᶠ q in 𝓝 p, X.val q = Y.val q) :
    chartLieSection B X A e he p = chartLieSection B Y A e he p := by
  have hc : coefficients B X.val e he =ᶠ[𝓝 p] coefficients B Y.val e he := by
    filter_upwards [hXY] with q hq
    unfold coefficients
    split_ifs <;> simp only [hq]
  obtain ⟨L,hLX⟩ := LieBrackets.coordinate_derivative_exists X e he p hp
  have hLY : HasCoordinateDerivative e (coefficients B Y.val e he) p L := by
    obtain ⟨G,hG,heG⟩ := hLX
    exact ⟨G,hG,heG.trans hc⟩
  apply tensor_coefficients_ext S B r s e he p hp
  intro I J
  obtain ⟨K,hK⟩ := tensor_coordinate_derivative_exists B A e he p hp I J
  change tensorCoefficients B (chartLieSection B X A e he) e he I J p =
    tensorCoefficients B (chartLieSection B Y A e he) e he I J p
  rw [chartLieSection_component B X A e he p hp I J L K hLX hK,
    chartLieSection_component B Y A e he p hp I J L K hLY hK, hc.eq_of_nhds]


theorem tensor_coefficient_smoothAt_of_section_smoothAt
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (T : TensorData.TensorBundle S r s) (A : TensorData.Field S r s)
    (p : M)
    (hA : letI := (TensorData.tensorSpace T).topology
      ManifoldContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
        (TensorData.tensorSpace T).bundle.totalManifold.smoothStructure.val
        (fun q => (⟨q,A q⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
          (fun q => TensorData.Fiber (TangentSpace S q) r s))) p)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (I : Fin r → Fin n) (J : Fin s → Fin n) :
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
      (tensorCoefficients B A e he I J) p := by
  let := (TensorData.tensorSpace T).topology
  let i : BundleOperationsData.TangentIndex S := ⟨e,he⟩
  have hv := FrameData.VectorSmoothAt.comp
    (g := fun q : M => (⟨q,A q⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
      (fun q => TensorData.Fiber (TangentSpace S q) r s)))
    (TensorData.tensorSpace T).bundle.totalManifold.smoothStructure.property.1.1
    (Frames.trivializationCoordinates_smoothAt
    (TensorData.tensorSpace T).bundle (i,i) ⟨p,A p⟩
    (by rw [Tensors.tensorSpace_diagonal_baseSet]; exact hp)) hA
  have hproj := hv.postcomp (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin (n^r*n^s) => ℝ)
    (finProdFinEquiv (TensorData.powerIndex n r I, TensorData.powerIndex n s J))).contDiff
  apply (scalarContDiffAt_iff _ _ _ _).mpr
  apply FrameData.VectorSmoothAt.congr hproj
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  exact (component_eq_bundle_coordinate B T e he q hq I J (A q)).symm

theorem tensor_eqOn_of_eqOn_interior
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (T : TensorData.TensorBundle S r s) (U : Set M) (hU : IsOpen U)
    (A C : TensorData.Field S r s)
    (hA : letI := (TensorData.tensorSpace T).topology
      ∀ p ∈ U, ManifoldContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
        (TensorData.tensorSpace T).bundle.totalManifold.smoothStructure.val
        (fun q => (⟨q,A q⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
          (fun q => TensorData.Fiber (TangentSpace S q) r s))) p)
    (hC : letI := (TensorData.tensorSpace T).topology
      ∀ p ∈ U, ManifoldContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
        (TensorData.tensorSpace T).bundle.totalManifold.smoothStructure.val
        (fun q => (⟨q,C q⟩ : Bundle.TotalSpace (Euclidean (n^r*n^s))
          (fun q => TensorData.Fiber (TangentSpace S q) r s))) p)
    (hEq : ∀ p ∈ U ∩ BoundaryData.manifoldInterior S, A p = C p) :
    ∀ p ∈ U, A p = C p := by
  intro p hpU
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  apply component_ext_of_fiber_interpretation Tensors.fiber_interpretation S B r s e he p hp
  intro I J
  have hAc : ContinuousOn (tensorCoefficients B A e he I J) (U ∩ e.source) := by
    intro q hq
    exact ((scalarContDiffAt_iff _ _ _ _).mp
      (tensor_coefficient_smoothAt_of_section_smoothAt B T A q (hA q hq.1)
        e he hq.2 I J)).1.continuousWithinAt
  have hCc : ContinuousOn (tensorCoefficients B C e he I J) (U ∩ e.source) := by
    intro q hq
    exact ((scalarContDiffAt_iff _ _ _ _).mp
      (tensor_coefficient_smoothAt_of_section_smoothAt B T C q (hC q hq.1)
        e he hq.2 I J)).1.continuousWithinAt
  have hdense : U ∩ e.source ⊆ closure (BoundaryData.manifoldInterior S ∩ (U ∩ e.source)) := by
    intro q hq
    rw [mem_closure_iff]
    intro V hV hqV
    obtain ⟨w, hw, hwi⟩ := (manifold_interior_dense S).inter_open_nonempty
      (V ∩ (U ∩ e.source)) (hV.inter (hU.inter e.open_source)) ⟨q, hqV, hq⟩
    exact ⟨w, hw.1, hwi, hw.2⟩
  have hEqc : EqOn (tensorCoefficients B A e he I J)
      (tensorCoefficients B C e he I J) (BoundaryData.manifoldInterior S ∩ (U ∩ e.source)) := by
    intro q hq
    unfold tensorCoefficients
    rw [hEq q ⟨hq.2.1, hq.1⟩]
  exact hEqc.of_subset_closure hAc hCc inter_subset_right hdense ⟨hpU,hp⟩


section TensorConstructionAssembly
open TensorData DifferentialData
set_option maxHeartbeats 1600000

theorem mixedTransport_coordinate_array_of_coordinates
    {V W : Type u} [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    {n r s : ℕ} (e : V ≃ₗ[ℝ] Euclidean n) (d : W ≃ₗ[ℝ] Euclidean n)
    (F : V ≃ₗ[ℝ] W) (H K : Euclidean n →L[ℝ] Euclidean n)
    (hH : ∀ v, d (F v) = H (e v)) (hK : ∀ w, e (F.symm w) = K (d w))
    (A : Fiber W r s) (I : Fin r → Fin n) (J : Fin s → Fin n) :
    Tensors.mixedCoordinates e r s (mixedTransport r s F A)
        (finProdFinEquiv (powerIndex n r I, powerIndex n s J)) =
      ∑ q : Fin r ⊕ Fin s → Fin n,
        Tensors.mixedCoordinates d r s A (mixedTupleIndex n r s q) *
          ((∏ i : Fin r, K (Pi.single (q (.inl i)) 1) (I i)) *
            ∏ j : Fin s, H (Pi.single (J j) 1) (q (.inr j))) := by
  classical
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℝ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℝ
  rw [Tensors.mixedTransport_coefficients d e F A]
  symm
  apply Fintype.sum_equiv (mixedTupleIndex n r s)
  intro q
  simp [mixedTupleIndex_apply, hH, hK]

theorem component_mixedTransport_coordinate_array
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleData.TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p q : M) (hp : p ∈ e.source) (hq : q ∈ e.source)
    (F : TangentData.TangentSpace S p ≃ₗ[ℝ] TangentData.TangentSpace S q)
    (H K : Euclidean n →L[ℝ] Euclidean n)
    (hH : ∀ v, B.fiberCoordinates.equiv e he q hq (F v) =
      H (B.fiberCoordinates.equiv e he p hp v))
    (hK : ∀ w, B.fiberCoordinates.equiv e he p hp (F.symm w) =
      K (B.fiberCoordinates.equiv e he q hq w))
    (A : Fiber (TangentData.TangentSpace S q) r s)
    (I : Fin r → Fin n) (J : Fin s → Fin n) :
    TensorLieData.component B r s e he p I J (mixedTransport r s F A) =
      ∑ v : Fin r ⊕ Fin s → Fin n,
        TensorLieData.component B r s e he q (fun i => v (.inl i)) (fun j => v (.inr j)) A *
          ((∏ i : Fin r, K (Pi.single (v (.inl i)) 1) (I i)) *
            ∏ j : Fin s, H (Pi.single (J j) 1) (v (.inr j))) := by
  rw [component_eq_mixedCoordinates B r s e he p hp]
  have hh := mixedTransport_coordinate_array_of_coordinates (r := r) (s := s)
    (B.fiberCoordinates.equiv e he p hp) (B.fiberCoordinates.equiv e he q hq)
    F H K hH hK A I J
  exact hh.trans (Finset.sum_congr rfl (fun v _ => by
    rw [component_eq_mixedCoordinates B r s e he q hq]
    rfl))


/-- Chart independence follows from a local actual-flow calculation for tangent fields. -/
theorem chartLieSection_overlap_of_tangent_flow
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (T : TensorData.TensorBundle S r s) (X : SmoothField B) (A : SmoothTensor B r s)
    (hFlow : ∀ (Y : SmoothField B), BoundaryFlowData.IsTangentToBoundary Y →
      ∀ (F : MaximalFlowData.CurveFamily M), BoundaryFlowData.IsMaximalFamily Y F →
      ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
        HasTensorFlowDerivative B F A.val (chartLieSection B Y A e he) p)
    (e d : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : M) (hpe : p ∈ e.source) (hpd : p ∈ d.source) :
    chartLieSection B X A e he p = chartLieSection B X A d hd p := by
  apply tensor_eqOn_of_eqOn_interior S B T (e.source ∩ d.source)
    (e.open_source.inter d.open_source)
    (chartLieSection B X A e he) (chartLieSection B X A d hd)
    (fun q hq => chartLieSection_smoothAt B T X A e he q hq.1)
    (fun q hq => chartLieSection_smoothAt B T X A d hd q hq.2) ?_ p ⟨hpe,hpd⟩
  intro q hq
  obtain ⟨Y,hY,hYX⟩ := exists_tangent_field_eq_near_interior B X q hq.2
  obtain ⟨F,hF⟩ := BoundaryTangentFlow.maximal_family_exists S B Y hY
  calc
    chartLieSection B X A e he q = chartLieSection B Y A e he q :=
      chartLieSection_eq_of_field_eq_near B X Y A e he q hq.1.1 (hYX.mono (fun _ h => h.symm))
    _ = chartLieSection B Y A d hd q := tensor_flow_derivative_unique B F A.val
      (chartLieSection B Y A e he) (chartLieSection B Y A d hd) q
      (hFlow Y hY F hF e he q hq.1.1) (hFlow Y hY F hF d hd q hq.1.2)
    _ = chartLieSection B X A d hd q :=
      chartLieSection_eq_of_field_eq_near B Y X A d hd q hq.1.2 hYX

/-- Compatible local candidates assemble into a smooth intrinsic tensor satisfying all charts. -/
theorem tensor_from_compatible_chart_sections
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (T : TensorData.TensorBundle S r s) (X : SmoothField B) (A : SmoothTensor B r s)
    (hOverlap : ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
      (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val) (p : M),
      p ∈ e.source → p ∈ d.source →
        chartLieSection B X A e he p = chartLieSection B X A d hd p) :
    ∃ Z : SmoothTensor B r s, CoordinateLieDerivative B X A.val Z.val ∧
      ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
        Z.val p = chartLieSection B X A e he p := by
  classical
  choose eOf heOf hpOf using S.smoothStructure.property.1.1
  let z : TensorData.Field S r s := fun p => chartLieSection B X A (eOf p) (heOf p) p
  have hlocal (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
      z p = chartLieSection B X A e he p :=
    hOverlap (eOf p) (heOf p) e he p (hpOf p) hp
  have hs : TensorSmooth B z := by
    intro e he p hp I J
    have hc := tensor_coefficient_smoothAt_of_section_smoothAt B T
      (chartLieSection B X A e he) p (chartLieSection_smoothAt B T X A e he p hp)
      e he hp I J
    apply hc.congr
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    unfold tensorCoefficients
    rw [hlocal e he q hq]
  refine ⟨⟨z, hs⟩, ?_, hlocal⟩
  intro e he p hp
  refine ⟨LieBrackets.coordinate_derivative_exists X e he p hp, ?_⟩
  intro I J
  refine ⟨tensor_coordinate_derivative_exists B A e he p hp I J, ?_⟩
  intro L K hL hK
  change component B r s e he p I J (z p) = _
  rw [hlocal e he p hp]
  exact chartLieSection_component B X A e he p hp I J L K hL hK

/-- Full construction assembly from the internal local actual-flow differentiation fact.
The premise is an ordinary local lemma to be proved analytically, not the construction target. -/
theorem tensor_construction_of_chart_flow
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) (A : SmoothTensor B r s)
    (hFlow : ∀ (Y : SmoothField B), BoundaryFlowData.IsTangentToBoundary Y →
      ∀ (F : MaximalFlowData.CurveFamily M), BoundaryFlowData.IsMaximalFamily Y F →
      ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
        HasTensorFlowDerivative B F A.val (chartLieSection B Y A e he) p) :
    ∃! Z : SmoothTensor B r s, CoordinateLieDerivative B X A.val Z.val ∧
      (BoundaryFlowData.IsTangentToBoundary X → ∀ F : MaximalFlowData.CurveFamily M,
        BoundaryFlowData.IsMaximalFamily X F → ∀ p,
          HasTensorFlowDerivative B F A.val Z.val p) := by
  classical
  obtain ⟨T⟩ := Tensors.exists_tensorBundle S r s
  obtain ⟨Z,hZ,hZE⟩ := tensor_from_compatible_chart_sections B T X A
    (fun e he d hd p hpe hpd =>
      chartLieSection_overlap_of_tangent_flow B T X A hFlow e d he hd p hpe hpd)
  refine ⟨Z, ⟨hZ, ?_⟩, ?_⟩
  · intro hX F hF p
    obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 p
    obtain ⟨d,hd,hcalc⟩ := hFlow X hX F hF e he p hp
    refine ⟨d,hd,?_⟩
    intro d' hd' c hc hpc I J
    have h := hcalc d' hd' c hc hpc I J
    simpa only [tensorCoefficients, hZE e he p hp] using h
  · intro W hW
    have hval : W.val = Z.val := tensor_coordinate_unique S B X r s A.val W.val Z.val hW.1 hZ
    cases W
    cases Z
    cases hval
    rfl

theorem coordinate_lie_eq_chart
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) (A : SmoothTensor B r s) (Z : TensorData.Field S r s)
    (hZ : CoordinateLieDerivative B X A.val Z)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    Z p = chartLieSection B X A e he p := by
  apply tensor_coefficients_ext S B r s e he p hp
  intro I J
  obtain ⟨L,hL⟩ := (hZ e he p hp).1
  obtain ⟨K,hK⟩ := ((hZ e he p hp).2 I J).1
  change tensorCoefficients B Z e he I J p =
    tensorCoefficients B (chartLieSection B X A e he) e he I J p
  rw [((hZ e he p hp).2 I J).2 L K hL hK,
    chartLieSection_component B X A e he p hp I J L K hL hK]

theorem tensor_flow_derivative_congr_value
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : MaximalFlowData.CurveFamily M) (A Z W : TensorData.Field S r s) (p : M)
    (hZW : Z p = W p) (hZ : HasTensorFlowDerivative B F A Z p) :
    HasTensorFlowDerivative B F A W p := by
  obtain ⟨d,hd,hcalc⟩ := hZ
  refine ⟨d,hd,?_⟩
  intro d' hd' e he hp I J
  simpa only [tensorCoefficients,hZW] using hcalc d' hd' e he hp I J

theorem tensor_boundaryless_flow_of_chart_flow
    {n r s : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (A Z : SmoothTensor B r s)
    (hZ : CoordinateLieDerivative B X A.val Z.val)
    (hFlow : ∀ (Y : SmoothField B), BoundaryFlowData.IsTangentToBoundary Y →
      ∀ (F : MaximalFlowData.CurveFamily M), BoundaryFlowData.IsMaximalFamily Y F →
      ∀ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
        HasTensorFlowDerivative B F A.val (chartLieSection B Y A e he) p)
    (F : MaximalFlowData.CurveFamily M) (hF : MaximalFlowData.IsMaximalFamily X F) (p : M) :
    HasTensorFlowDerivative B F A.val Z.val p := by
  have hX : BoundaryFlowData.IsTangentToBoundary X := by
    intro p hp e he hpe
    cases n <;> trivial
  obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 p
  exact tensor_flow_derivative_congr_value B F A.val (chartLieSection B X A e he) Z.val p
    (coordinate_lie_eq_chart S B X A Z.val hZ e he p hp).symm
    (hFlow X hX F hF e he p hp)

end TensorConstructionAssembly

section ActualTensorFlow
open DifferentialData MaximalFlowData TensorData
set_option maxHeartbeats 1600000

/-- The differential of an allowed time map is an actual linear equivalence.
Only the open flow domain and local smoothness of the time maps are used. -/
theorem forward_time_differential_equiv
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (F : CurveFamily M)
    (hzero : ∀ p, 0 ∈ (F.interval p).carrier) (hinit : ∀ p, F.curve p 0 = p)
    (hD : IsOpen (flowDomain F))
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (hlaw : ∀ p s, s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t, s + t ∈ (F.interval p).carrier → F.curve (F.curve p s) t = F.curve p (s + t))
    (p : M) (t : ℝ) (ht : t ∈ (F.interval p).carrier) :
    ∃ d : TangentSpace S p ≃ₗ[ℝ] TangentSpace S (F.curve p t),
      IsDifferential S S (fun q => F.curve q t) p d.toLinearMap := by
  classical
  have hc := BracketFromFlow.pullbackCorrect_of_flow S F hzero hinit hsm hlaw
  have hrev := hc p t ht
  obtain ⟨L, hL, _⟩ := BracketFromFlow.differentialAt_exists S S
    (fun q => F.curve q t) p (BracketFromFlow.timeMap_smoothAt S F t p (hsm (t,p) ht))
  have hgf : ((fun q => F.curve q (-t)) ∘ (fun q => F.curve q t)) =ᶠ[𝓝 p] id := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hD.mem_nhds ht)] with q hqt
    exact (BracketFromFlow.reverse_time F hzero hinit hlaw q t hqt).2
  have hKL := BracketFromFlow.tangent_left_inverse_of_local_inverse S
    (fun q => F.curve q t) (fun q => F.curve q (-t)) p
    (BracketFromFlow.timeMap_smoothAt S F (-t) (F.curve p t)
      (hsm (-t,F.curve p t) hrev.1)) hrev.2.1 hgf L hL
    (inverseTimeDifferential S F t p) hrev.2.2.1
  have hLinj : Function.Injective L := Function.LeftInverse.injective hKL
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨f, hf, hq⟩ := S.smoothStructure.property.1.1 (F.curve p t)
  let c := B.fiberCoordinates.equiv e he p hp
  let d := B.fiberCoordinates.equiv f hf (F.curve p t) hq
  let R : Euclidean n →ₗ[ℝ] Euclidean n := d.toLinearMap.comp (L.comp c.symm.toLinearMap)
  have hRinj : Function.Injective R := d.injective.comp (hLinj.comp c.symm.injective)
  have hRsurj : Function.Surjective R := LinearMap.injective_iff_surjective.mp hRinj
  have hLsurj : Function.Surjective L := by
    intro y
    obtain ⟨x, hx⟩ := hRsurj (d y)
    exact ⟨c.symm x, d.injective hx⟩
  exact ⟨LinearEquiv.ofBijective L ⟨hLinj,hLsurj⟩, hL⟩

/-- A total equivalence family with genuine forward differentials near zero.
Values off the allowed time interval are arbitrary linear identifications of
fibers of the same dimension; they impose no global smoothness condition. -/
theorem forward_time_differential_family
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (F : CurveFamily M)
    (hzero : ∀ p, 0 ∈ (F.interval p).carrier) (hinit : ∀ p, F.curve p 0 = p)
    (hD : IsOpen (flowDomain F))
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (hlaw : ∀ p s, s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t, s + t ∈ (F.interval p).carrier → F.curve (F.curve p s) t = F.curve p (s + t))
    (p : M) :
    ∃ d : (t : ℝ) → TangentSpace S p ≃ₗ[ℝ] TangentSpace S (F.curve p t),
      ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ (F.interval p).carrier ∧
        IsDifferential S S (fun q => F.curve q t) p (d t).toLinearMap := by
  classical
  have hex : ∀ t : ℝ, ∃ d : TangentSpace S p ≃ₗ[ℝ] TangentSpace S (F.curve p t),
      t ∈ (F.interval p).carrier → IsDifferential S S (fun q => F.curve q t) p d.toLinearMap := by
    intro t
    by_cases ht : t ∈ (F.interval p).carrier
    · obtain ⟨d, hd⟩ := forward_time_differential_equiv S B F hzero hinit hD hsm hlaw p t ht
      exact ⟨d, fun _ => hd⟩
    · obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
      obtain ⟨f, hf, hq⟩ := S.smoothStructure.property.1.1 (F.curve p t)
      exact ⟨(B.fiberCoordinates.equiv e he p hp).trans
        (B.fiberCoordinates.equiv f hf (F.curve p t) hq).symm, fun h => False.elim (ht h)⟩
  choose d hd using hex
  refine ⟨d, ?_⟩
  have hdom : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ (F.interval p).carrier :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hD.mem_nhds (hzero p))
  filter_upwards [hdom] with t ht
  exact ⟨ht, hd t ht⟩

/-- Actual flow differentials admit smooth forward/inverse coordinate paths through
identity, with the variational derivatives and no off-domain regularity assumption. -/
theorem flow_coordinate_jacobian_paths
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (F : CurveFamily M) (hF : BoundaryFlowData.IsMaximalFamily X F)
    (hD : IsOpen (flowDomain F))
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (hlaw : ∀ p s, s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t, s + t ∈ (F.interval p).carrier → F.curve (F.curve p s) t = F.curve p (s + t))
    (p : M) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (d : (t : ℝ) → TangentSpace S p ≃ₗ[ℝ] TangentSpace S (F.curve p t))
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ (F.interval p).carrier ∧
      IsDifferential S S (fun q => F.curve q t) p (d t).toLinearMap) :
    ∃ (H K : ℝ → Euclidean n →L[ℝ] Euclidean n) (L : Euclidean n →L[ℝ] Euclidean n),
      HasCoordinateDerivative e (coefficients B X.val e he) p L ∧
      HasDerivAt H L 0 ∧ HasDerivAt K (-L) 0 ∧
      H 0 = ContinuousLinearMap.id ℝ (Euclidean n) ∧
      K 0 = ContinuousLinearMap.id ℝ (Euclidean n) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), F.curve p t ∈ e.source ∧
        (∀ hq : F.curve p t ∈ e.source, ∀ v,
          B.fiberCoordinates.equiv e he (F.curve p t) hq (d t v) =
            H t (B.fiberCoordinates.equiv e he p hp v)) ∧
        (∀ hq : F.curve p t ∈ e.source, ∀ w,
          B.fiberCoordinates.equiv e he p hp ((d t).symm w) =
            K t (B.fiberCoordinates.equiv e he (F.curve p t) hq w)) := by
  classical
  have hzero := fun q => (hF q).1
  have hinit := fun q => (hF q).2.1
  have hq0 : F.curve p 0 ∈ e.source := by simpa only [hinit p] using hp
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := (hsm (0,p) (hzero p)).2 e he e he hp hq0
  obtain ⟨V, hV, hpV, CX, hCX, heCX⟩ := LieBrackets.smooth_field_regular X e he p hp
  let R : Euclidean n →L[ℝ] ℝ × Euclidean n := ContinuousLinearMap.inr ℝ ℝ (Euclidean n)
  let H (t : ℝ) := (fderiv ℝ G (t, (e p).val)).comp R
  let K (t : ℝ) := (fderiv ℝ G (-t, G (t, (e p).val))).comp R
  let L := fderiv ℝ CX (e p).val
  have hGdiff := (hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hCXdiff := (hCX.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  have hL : HasCoordinateDerivative e (coefficients B X.val e he) p L :=
    ⟨CX, hCXdiff.hasFDerivAt, heCX⟩
  have hG0 : G (0, (e p).val) = (e p).val := by
    simpa only [flow, hinit p] using heG.self_of_nhds
  have hGslice := hGdiff.hasFDerivAt.comp (e p).val
    ((hasFDerivAt_const (0 : ℝ) (e p).val).prodMk (hasFDerivAt_id (e p).val))
  have hGs : HasFDerivAt (fun z => G (0,z)) (H 0) (e p).val := by
    convert hGslice using 1 <;> rfl
  have heGslice : (fun q => G (0,(e q).val)) =ᶠ[𝓝 p] (fun q => (e q).val) := by
    simpa only [Function.comp_def, flow, hinit] using heG.comp_tendsto
      (continuousAt_const.prodMk continuousAt_id : ContinuousAt (fun q : M => ((0 : ℝ),q)) p)
  have hH0 : H 0 = ContinuousLinearMap.id ℝ (Euclidean n) :=
    FiniteRegularity.extension_independence e (fun q => (e q).val) p hp _ _
      ⟨fun z => G (0,z), hGs, heGslice⟩
      ⟨id, hasFDerivAt_id _, Eventually.of_forall (fun _ => rfl)⟩
  have hK0 : K 0 = ContinuousLinearMap.id ℝ (Euclidean n) := by
    simpa only [K, neg_zero, hG0] using hH0
  have hHraw := BracketFromFlow.flow_state_jacobian_variation B X F hF hD hsm
    0 p (hzero p) e he hp e he hq0 U G hU hpU hG heG V CX hV
    (by simpa only [hinit p] using hpV) hCX
    (by simpa only [hinit p] using heCX)
  have hHd : HasDerivAt H L 0 := by
    rw [hinit p] at hHraw
    change HasDerivAt H (L.comp (H 0)) 0 at hHraw
    simpa only [hH0, ContinuousLinearMap.comp_id] using hHraw
  have hstate : DifferentiableAt ℝ (fun t => G (t, (e p).val)) 0 :=
    hGdiff.comp 0 (differentiableAt_id.prodMk (differentiableAt_const (e p).val))
  have hDG : DifferentiableAt ℝ (fderiv ℝ G) (-0,G (0,(e p).val)) := by
    rw [neg_zero, hG0]
    exact ((hG.contDiffAt (hU.mem_nhds hpU)).fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  have hKd : DifferentiableAt ℝ K 0 :=
    (hDG.comp 0 (differentiableAt_id.neg.prodMk hstate)).clm_comp (differentiableAt_const R)
  have hi : ContinuousAt (fun t : ℝ => (t,p)) 0 := continuousAt_id.prodMk continuousAt_const
  have hcurve : ContinuousAt (F.curve p) 0 := (hsm (0,p) (hzero p)).1.comp (f := fun t : ℝ => (t,p)) hi
  have hmove : ContinuousAt (fun t => (-t,F.curve p t)) 0 := continuousAt_id.neg.prodMk hcurve
  have hcoords : ContinuousAt (fun t => (-t,(e (F.curve p t)).val)) 0 :=
    continuousAt_id.neg.prodMk (continuous_subtype_val.continuousAt.comp
      ((e.continuousAt hq0).comp hcurve))
  have heGnear := hi.eventually (eventually_eventually_nhds.mpr heG)
  have heGback : (fun w : ℝ × M => G (w.1,(e w.2).val)) =ᶠ[𝓝 (-0,F.curve p 0)]
      (fun w => (e (flow F w)).val) := by simpa only [neg_zero,hinit p] using heG
  have heHnear := hmove.eventually (eventually_eventually_nhds.mpr heGback)
  have hKA : (fun t => (K t).comp (H t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun _ => ContinuousLinearMap.id ℝ (Euclidean n)) := by
    filter_upwards [heGnear, heHnear, hi.preimage_mem_nhds (hD.mem_nhds (hzero p)),
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hU.mem_nhds hpU),
      hcoords.preimage_mem_nhds (hU.mem_nhds (by simpa only [neg_zero,hinit p] using hpU)),
      hcurve.preimage_mem_nhds (e.open_source.mem_nhds hq0)] with t htG htH htD htU htV hte
    exact BracketFromFlow.flow_jacobians_inverse F hzero hinit hlaw hD t p htD
      (hsm (t,p) htD) e hp e hte G G
      ((hG.contDiffAt (hU.mem_nhds htU)).differentiableAt (by simp))
      ((hG.contDiffAt (hU.mem_nhds htV)).differentiableAt (by simp)) htG htH
  have hKzero : deriv K 0 + L = 0 := by
    have hz := ((hKd.hasDerivAt.clm_comp hHd).congr_of_eventuallyEq hKA.symm).unique
      (hasDerivAt_const (0 : ℝ) (ContinuousLinearMap.id ℝ (Euclidean n)))
    simpa only [hH0,hK0,ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp] using hz
  have hKder : HasDerivAt K (-L) 0 := by
    exact hKd.hasDerivAt.congr_deriv (eq_neg_of_add_eq_zero_left hKzero)
  refine ⟨H,K,L,hL,hHd,hKder,hH0,hK0,?_⟩
  filter_upwards [hd, heGnear, hKA,
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hU.mem_nhds hpU),
    hcurve.preimage_mem_nhds (e.open_source.mem_nhds hq0)] with t htd htG htKA htU hte
  have hforward : ∀ hq : F.curve p t ∈ e.source, ∀ v,
      B.fiberCoordinates.equiv e he (F.curve p t) hq (d t v) =
        H t (B.fiberCoordinates.equiv e he p hp v) := by
    intro hq v
    have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => G (t,z)) ((fun z => (t,z)) ⁻¹' U) :=
      hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
    have htGeq : (fun w : ℝ × M => G (w.1,(e w.2).val)) =ᶠ[𝓝 (t,p)]
        (fun w => (e (flow F w)).val) := htG
    have heq := htGeq.comp_tendsto
      (continuousAt_const.prodMk continuousAt_id : ContinuousAt (fun q : M => (t,q)) p)
    have hJac := BracketFromFlow.rebased_jacobian B (fun q => F.curve q t) p (F.curve p t)
      (d t).toLinearMap htd.2 e he hq e he hp _ (fun z => G (t,z))
      (hU.preimage (continuous_const.prodMk continuous_id)) htU hslice heq v
    have hGs := ((hG.contDiffAt (hU.mem_nhds htU)).differentiableAt (by simp)).hasFDerivAt.comp
      (e p).val ((hasFDerivAt_const t (e p).val).prodMk (hasFDerivAt_id (e p).val))
    have hGs' : HasFDerivAt (fun z => G (t,z)) (H t) (e p).val := by
      convert hGs using 1 <;> rfl
    rw [hGs'.fderiv] at hJac
    exact hJac
  refine ⟨hte,hforward,?_⟩
  intro hq w
  have hh := hforward hq ((d t).symm w)
  rw [LinearEquiv.apply_symm_apply] at hh
  calc
    _ = K t (H t (B.fiberCoordinates.equiv e he p hp ((d t).symm w))) :=
      (congrArg (fun R : Euclidean n →L[ℝ] Euclidean n =>
        R (B.fiberCoordinates.equiv e he p hp ((d t).symm w))) htKA).symm
    _ = _ := congrArg (K t) hh.symm

/-- A scalar ambient differential gives the actual scalar time derivative along
an integral curve, including at an ordinary boundary point. -/
theorem scalar_coordinate_flow_derivative
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (F : CurveFamily M) (hF : BoundaryFlowData.IsMaximalFamily X F)
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (p : M) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (g : M → ℝ) (K : Euclidean n →L[ℝ] ℝ)
    (hK : HasScalarCoordinateDerivative e g p K) :
    HasDerivAt (fun t => g (F.curve p t)) (K (coefficients B X.val e he p)) 0 := by
  have hinit := (hF p).2.1
  have hq : F.curve p 0 ∈ e.source := by simpa only [hinit] using hp
  have hγ := ((hF p).2.2.1).2 0 (hF p).1 e he hq
  have hγd : HasDerivAt (fun t => (e (F.curve p t)).val) (coefficients B X.val e he p) 0 := by
    apply hγ.2.congr_deriv
    rw [← LieBrackets.coefficients_eq X.val e he (F.curve p 0) hq, hinit]
  obtain ⟨G,hG,heG⟩ := hK
  have hG' : HasFDerivAt G K (e (F.curve p 0)).val := by simpa only [hinit] using hG
  have hd := hG'.comp_hasDerivAt 0 hγd
  have hcurve : ContinuousAt (F.curve p) 0 := (hsm (0,p) (hF p).1).1.comp
    (f := fun t : ℝ => (t,p)) (continuousAt_id.prodMk continuousAt_const)
  have heG' : (fun q => G (e q).val) =ᶠ[𝓝 (F.curve p 0)] g := by simpa only [hinit] using heG
  exact hd.congr_of_eventuallyEq (heG'.symm.comp_tendsto hcurve)

/-- The local chart formula is the actual tensor pullback time derivative in
that chart, for every family of genuine forward differential equivalences. -/
theorem chartLieSection_component_flow_derivative
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (A : SmoothTensor B r s) (F : CurveFamily M) (hF : BoundaryFlowData.IsMaximalFamily X F)
    (hD : IsOpen (flowDomain F))
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (hlaw : ∀ p s, s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t, s + t ∈ (F.interval p).carrier → F.curve (F.curve p s) t = F.curve p (s + t))
    (p : M) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (d : (t : ℝ) → TangentSpace S p ≃ₗ[ℝ] TangentSpace S (F.curve p t))
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ (F.interval p).carrier ∧
      IsDifferential S S (fun q => F.curve q t) p (d t).toLinearMap)
    (I : Fin r → Fin n) (J : Fin s → Fin n) :
    HasDerivAt (fun t => component B r s e he p I J
      (mixedTransport r s (d t) (A.val (F.curve p t))))
      (tensorCoefficients B (chartLieSection B X A e he) e he I J p) 0 := by
  classical
  obtain ⟨H,K,L,hL,hH,hK,hH0,hK0,hcoord⟩ :=
    flow_coordinate_jacobian_paths B X F hF hD hsm hlaw p e he hp d hd
  choose Q hQ using tensor_coordinate_derivative_exists B A e he p hp
  let C (t : ℝ) (q : Fin r ⊕ Fin s → Fin n) :=
    tensorCoefficients B A.val e he (fun i => q (.inl i)) (fun j => q (.inr j)) (F.curve p t)
  let C' (q : Fin r ⊕ Fin s → Fin n) :=
    Q (fun i => q (.inl i)) (fun j => q (.inr j)) (coefficients B X.val e he p)
  have hC : ∀ q, HasDerivAt (fun t => C t q) (C' q) 0 := by
    intro q
    exact scalar_coordinate_flow_derivative B X F hF hsm p e he hp _ _
      (hQ (fun i => q (.inl i)) (fun j => q (.inr j)))
  have hcalc := mixed_array_path_derivative C C' H K L hC hH hK hH0 hK0 I J
  have heq : (fun t => component B r s e he p I J
      (mixedTransport r s (d t) (A.val (F.curve p t)))) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∑ q : Fin r ⊕ Fin s → Fin n, C t q *
        ((∏ i : Fin r, K t (Pi.single (q (.inl i)) 1) (I i)) *
          ∏ j : Fin s, H t (Pi.single (J j) 1) (q (.inr j)))) := by
    filter_upwards [hcoord] with t ht
    exact component_mixedTransport_coordinate_array B e he p (F.curve p t) hp ht.1
      (d t) (H t) (K t) (ht.2.1 ht.1) (ht.2.2 ht.1) (A.val (F.curve p t)) I J

  have hvalue := chartLieSection_component B X A e he p hp I J L (Q I J) hL (hQ I J)
  have hinit := (hF p).2.1
  rw [hvalue]
  simpa only [C,C',hinit] using hcalc.congr_of_eventuallyEq heq

/-- The chart candidate has the intrinsic tensor flow derivative. Its derivative
is tested in every chart after transferring fixed-fiber linear tests. -/
theorem chartLieSection_flow_derivative_of_flow
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (A : SmoothTensor B r s) (F : CurveFamily M) (hF : BoundaryFlowData.IsMaximalFamily X F)
    (hD : IsOpen (flowDomain F))
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (hlaw : ∀ p s, s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t, s + t ∈ (F.interval p).carrier → F.curve (F.curve p s) t = F.curve p (s + t))
    (p : M) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    HasTensorFlowDerivative B F A.val (chartLieSection B X A e he) p := by
  obtain ⟨d,hd⟩ := forward_time_differential_family S B F
    (fun q => (hF q).1) (fun q => (hF q).2.1) hD hsm hlaw p
  refine ⟨d,hd,?_⟩
  intro d hd f hf hpf I J
  exact linear_test_hasDerivAt B r s e he p hp
    (fun t => mixedTransport r s (d t) (A.val (F.curve p t)))
    (chartLieSection B X A e he p) 0
    (chartLieSection_component_flow_derivative B X A F hF hD hsm hlaw p e he hp d hd)
    (component B r s f hf p I J)

/-- The chart Lie candidate agrees with the actual boundary-tangent flow. -/
theorem chartLieSection_boundary_flow
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (hX : BoundaryFlowData.IsTangentToBoundary X) (A : SmoothTensor B r s)
    (F : CurveFamily M) (hF : BoundaryFlowData.IsMaximalFamily X F)
    (p : M) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    HasTensorFlowDerivative B F A.val (chartLieSection B X A e he) p :=
  chartLieSection_flow_derivative_of_flow B X A F hF
    (BoundaryTangentFlow.domain_open_smooth S B X hX F hF).1
    (BoundaryTangentFlow.domain_open_smooth S B X hX F hF).2
    (BoundaryTangentFlow.lifespan_flow_law S B X hX F hF) p e he hp


end ActualTensorFlow

/-- The intrinsic smooth tensor derivative exists uniquely for every variance
and every smooth field, including arbitrary fields at boundary points. -/
theorem tensor_construction :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_constructionType.{u} := by
  intro n a M _ S B X r s A
  exact tensor_construction_of_chart_flow S B X A
    (fun Y hY F hF e he p hp => chartLieSection_boundary_flow B Y hY A F hF p e he hp)

/-- On a boundaryless manifold the coordinate construction is differentiation
of the actual mixed tensor pullback, with no tangency premise. -/
theorem tensor_boundaryless_flow :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_boundaryless_flowType.{u} := by
  intro n M _ S B X r s A Z hZ F hF p
  exact tensor_boundaryless_flow_of_chart_flow S B X A Z hZ
    (fun Y hY F hF e he p hp => chartLieSection_boundary_flow B Y hY A F hF p e he hp) F hF p

theorem scalar_coordinate_derivative_add
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n a M) (f g : M → ℝ) (p : M) (K L : Euclidean n →L[ℝ] ℝ)
    (hK : HasScalarCoordinateDerivative e f p K) (hL : HasScalarCoordinateDerivative e g p L) :
    HasScalarCoordinateDerivative e (fun q => f q + g q) p (K + L) := by
  obtain ⟨F,hF,hEF⟩ := hK
  obtain ⟨G,hG,hEG⟩ := hL
  refine ⟨fun z => F z + G z, ?_, ?_⟩
  · simpa only [Pi.add_apply] using! hF.add hG
  · filter_upwards [hEF,hEG] with q hqF hqG
    rw [hqF,hqG]

theorem scalar_coordinate_derivative_const_mul
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n a M) (f : M → ℝ) (p : M) (K : Euclidean n →L[ℝ] ℝ) (c : ℝ)
    (hK : HasScalarCoordinateDerivative e f p K) :
    HasScalarCoordinateDerivative e (fun q => c * f q) p (c • K) := by
  obtain ⟨F,hF,hEF⟩ := hK
  refine ⟨fun z => c * F z, ?_, ?_⟩
  · simpa only [smul_eq_mul] using! hF.const_smul c
  · exact hEF.mono (fun q hq => congrArg (fun x => c * x) hq)

theorem tensorSmooth_const_smul
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (c : ℝ) (A : TensorData.Field S r s) (hA : TensorSmooth B A) :
    TensorSmooth B (fun p => c • A p) := by
  intro e he p hp I J
  apply ScalarContDiffAt.congr
    ((ScalarContDiffAt.const (⊤ : ℕ∞) S.smoothStructure.val c p).mul (hA e he p hp I J))
  exact Filter.Eventually.of_forall (fun q => by
    simp only [tensorCoefficients, map_smul, smul_eq_mul])

theorem tensor_coordinate_add
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (A ZA C ZC : TensorData.Field S r s)
    (hA : CoordinateLieDerivative B X A ZA) (hC : CoordinateLieDerivative B X C ZC) :
    CoordinateLieDerivative B X (fun p => A p + C p) (fun p => ZA p + ZC p) := by
  intro e he p hp
  obtain ⟨hX,hA⟩ := hA e he p hp
  obtain ⟨_,hC⟩ := hC e he p hp
  refine ⟨hX, ?_⟩
  intro I J
  obtain ⟨KA,hKA⟩ := (hA I J).1
  obtain ⟨KC,hKC⟩ := (hC I J).1
  have hKSum : HasScalarCoordinateDerivative e
      (tensorCoefficients B (fun p => A p + C p) e he I J) p (KA+KC) := by
    have heq : tensorCoefficients B (fun p => A p + C p) e he I J =
        (fun q => tensorCoefficients B A e he I J q + tensorCoefficients B C e he I J q) := by
      funext q
      exact map_add (component B r s e he q I J) (A q) (C q)
    rw [heq]
    exact scalar_coordinate_derivative_add e _ _ p KA KC hKA hKC
  refine ⟨⟨_,hKSum⟩, ?_⟩
  intro L K hL hK
  have hKeq := scalar_coordinate_derivative_unique e _ p hp K (KA+KC) hK hKSum
  rw [hKeq]
  have hZA := (hA I J).2 L KA hL hKA
  have hZC := (hC I J).2 L KC hL hKC
  simp only [tensorCoefficients] at hZA hZC
  simp only [tensorCoefficients,map_add,add_apply]
  rw [hZA,hZC]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem tensor_coordinate_const_smul
    {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (X : SmoothField B)
    (c : ℝ) (A Z : TensorData.Field S r s) (hA : CoordinateLieDerivative B X A Z) :
    CoordinateLieDerivative B X (fun p => c • A p) (fun p => c • Z p) := by
  intro e he p hp
  obtain ⟨hX,hA⟩ := hA e he p hp
  refine ⟨hX, ?_⟩
  intro I J
  obtain ⟨KA,hKA⟩ := (hA I J).1
  have hKMul : HasScalarCoordinateDerivative e
      (tensorCoefficients B (fun p => c • A p) e he I J) p (c • KA) := by
    have heq : tensorCoefficients B (fun p => c • A p) e he I J =
        (fun q => c * tensorCoefficients B A e he I J q) := by
      funext q
      exact map_smul (component B r s e he q I J) c (A q)
    rw [heq]
    exact scalar_coordinate_derivative_const_mul e _ p KA c hKA
  refine ⟨⟨_,hKMul⟩, ?_⟩
  intro L K hL hK
  have hKeq := scalar_coordinate_derivative_unique e _ p hp K (c • KA) hK hKMul
  rw [hKeq]
  have hZ := (hA I J).2 L KA hL hKA
  simp only [tensorCoefficients] at hZ
  simp only [tensorCoefficients,map_smul,smul_apply,smul_eq_mul]
  rw [hZ]
  simp only [mul_add,mul_sub,Finset.mul_sum]
  ring_nf

theorem tensor_linearity :
    Specs.SmoothManifolds.Ch07.TensorLieDerivative.tensor_linearityType.{u} := by
  constructor
  · intro n r s a M _ S B X A ZA C ZC hA hC
    exact tensor_coordinate_add B X A ZA C ZC hA hC
  · intro n r s a M _ S B X c A Z hA
    exact tensor_coordinate_const_smul B X c A Z hA


end SmoothManifolds.TensorLieDerivative
