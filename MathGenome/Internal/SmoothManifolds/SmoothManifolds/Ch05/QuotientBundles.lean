import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Frames
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.QuotientBundles

namespace SmoothManifolds.QuotientBundles
open ModelData AtlasData MapData ProductData BundleData FrameData QuotientData
  Bundle Module Set Filter
open scoped Topology
universe u v w z t

private theorem transported_twice {n : ℕ} {a : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (e : ModelChart n a X) :
    h.toOpenPartialHomeomorph.trans (h.symm.toOpenPartialHomeomorph.trans e) = e := by
  apply OpenPartialHomeomorph.ext
  · intro x
    change e (h.symm (h x)) = e x
    rw [h.symm_apply_apply]
  · intro x
    change h.symm (h (e.symm x)) = e.symm x
    rw [h.symm_apply_apply]
  · ext x
    change (x ∈ univ ∧ (h x ∈ univ ∧ h.symm (h x) ∈ e.source)) ↔ x ∈ e.source
    simp only [mem_univ, true_and, h.symm_apply_apply]

private theorem transportAtlas_isMaximal {n : ℕ} {a : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (A : Set (ModelChart n a X)) (hA : IsMaximalContDiffAtlas (⊤ : ℕ∞) A) :
    IsMaximalContDiffAtlas (⊤ : ℕ∞) (transportAtlas h A) := by
  refine ⟨transportAtlas_isContDiffAtlas _ A h hA.1, ?_⟩
  intro D hD hsub
  have hback := transportAtlas_isContDiffAtlas (⊤ : ℕ∞) D h.symm hD
  have hAsub : A ⊆ transportAtlas h.symm D := by
    intro e he
    exact ⟨h.symm.toOpenPartialHomeomorph.trans e, hsub ⟨e, he, rfl⟩,
      transported_twice h e⟩
  have heq := hA.2 _ hback hAsub
  apply Subset.antisymm
  · intro d hd
    have hmem : h.toOpenPartialHomeomorph.trans d ∈ A :=
      heq ▸ (show h.toOpenPartialHomeomorph.trans d ∈ transportAtlas h.symm D from ⟨d, hd, rfl⟩)
    exact ⟨h.toOpenPartialHomeomorph.trans d, hmem, transported_twice h.symm d⟩
  · exact hsub

private noncomputable def transportManifold {n : ℕ} {a : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold n a X) (h : X ≃ₜ Y) : SmoothManifold n a Y where
  topologicalManifold := {
    hausdorff := by letI := S.topologicalManifold.hausdorff; exact h.symm.isEmbedding.t2Space
    secondCountable := by letI := S.topologicalManifold.secondCountable; exact h.symm.secondCountableTopology
    atlas := transportAtlas h S.smoothStructure.val
    covers := (transportAtlas_isContDiffAtlas _ _ h S.smoothStructure.property.1).1 }
  smoothStructure := ⟨transportAtlas h S.smoothStructure.val,
    transportAtlas_isMaximal h _ S.smoothStructure.property⟩

private theorem smoothWithParameters_transport {n d : ℕ} {a b : ModelKind}
    {M : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Y]
    {S : SmoothManifold n a M} {T : SmoothManifold d b X}
    {V : Type z} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : M × V → X} {U : Set M} (h : X ≃ₜ Y)
    (hf : SmoothWithParameters S T f U) :
    SmoothWithParameters S (transportManifold T h) (fun q => h (f q)) U := by
  intro p hp
  obtain ⟨hcont, hcharts⟩ := hf p hp
  refine ⟨h.continuous.continuousAt.comp hcont, ?_⟩
  rintro c hc _ ⟨d, hd, rfl⟩ hpc hpd
  have hpd' : f p ∈ d.source := by
    simpa only [mem_transportedChart_source, h.symm_apply_apply] using hpd
  obtain ⟨W, hW, hpW, F, hF, heq⟩ := hcharts c hc d hd hpc hpd'
  refine ⟨W, hW, hpW, F, hF, ?_⟩
  simpa only [transportedChart_apply, h.symm_apply_apply] using heq

namespace Transport
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (e : (p : M) → F p ≃ₗ[ℝ] E p)

noncomputable def totalEquiv : TotalSpace (Euclidean r) F ≃ TotalSpace (Euclidean r) E where
  toFun q := ⟨q.proj, e q.proj q.snd⟩
  invFun q := ⟨q.proj, (e q.proj).symm q.snd⟩
  left_inv q := by cases q; simp
  right_inv q := by cases q; simp

noncomputable def topology : TopologicalSpace (TotalSpace (Euclidean r) F) :=
  TopologicalSpace.induced (totalEquiv (r := r) e) inferInstance

noncomputable def homeomorph : @Homeomorph (TotalSpace (Euclidean r) F)
    (TotalSpace (Euclidean r) E) (topology (r := r) e) inferInstance := by
  letI := topology (r := r) e
  exact (totalEquiv (r := r) e).toHomeomorphOfIsInducing ⟨rfl⟩

noncomputable def trivialization (i : ι) :
    @Trivialization M (Euclidean r) (TotalSpace (Euclidean r) F) _ _ (topology (r := r) e)
      TotalSpace.proj := by
  letI := topology (r := r) e
  exact (B.trivialization i).compHomeomorph (homeomorph (r := r) e)

section


@[simp] theorem trivialization_apply (i : ι) (q : TotalSpace (Euclidean r) F) :
    letI := topology (r := r) e
    trivialization B e i q = B.trivialization i ⟨q.proj, e q.proj q.snd⟩ := rfl

@[simp] theorem trivialization_baseSet (i : ι) :
    letI := topology (r := r) e
    (trivialization B e i).baseSet = B.baseSet i := B.trivialization_baseSet i

theorem trivialization_linear (i : ι) : letI := topology (r := r) e
    (trivialization B e i).IsLinear ℝ := by
  letI := topology (r := r) e
  constructor
  intro p hp
  have hpB : p ∈ B.baseSet i := trivialization_baseSet B e i ▸ hp
  exact ((B.fiberCoordinates i p hpB).toLinearMap.comp (e p).toLinearMap).isLinear

theorem trivialization_symm (i : ι) (p : M) (hp : p ∈ B.baseSet i) (v : Euclidean r) :
    letI := topology (r := r) e
    (trivialization B e i).symm p v = (e p).symm ((B.trivialization i).symm p v) := by
  letI := topology (r := r) e
  have hpB : p ∈ (B.trivialization i).baseSet := (B.trivialization_baseSet i).symm ▸ hp
  have hpF : p ∈ (trivialization B e i).baseSet := (trivialization_baseSet B e i).symm ▸ hp
  apply (e p).injective
  apply (B.fiberCoordinates i p hp).injective
  change ((B.trivialization i) ⟨p, e p ((trivialization B e i).symm p v)⟩).2 =
    ((B.trivialization i) ⟨p, e p ((e p).symm ((B.trivialization i).symm p v))⟩).2
  change ((trivialization B e i) ⟨p, (trivialization B e i).symm p v⟩).2 = _
  rw [Trivialization.apply_mk_symm _ hpF, LinearEquiv.apply_symm_apply,
    Trivialization.apply_mk_symm _ hpB]

noncomputable def manifold : letI := topology (r := r) e
    SmoothManifold (n + r) (productKind n a r .euclidean)
    (TotalSpace (Euclidean r) F) := by
  letI := topology (r := r) e
  exact transportManifold B.totalManifold (homeomorph (r := r) e).symm

theorem manifold_maps : letI := topology (r := r) e
    IsSmoothMap (manifold B e) B.totalManifold (homeomorph (r := r) e) ∧
    IsSmoothMap B.totalManifold (manifold B e) (homeomorph (r := r) e).symm := by
  letI := topology (r := r) e
  have hh := transportAtlas_maps (⊤ : ℕ∞) B.totalManifold.smoothStructure.val
    (homeomorph (r := r) e).symm B.totalManifold.smoothStructure.property.1
  exact ⟨hh.2, hh.1⟩


noncomputable def bundle : letI := topology (r := r) e
    SmoothVectorBundle S r ι F := by
  letI := topology (r := r) e
  let H := homeomorph (r := r) e
  have hmaps := manifold_maps B e
  refine {
    baseSet := B.baseSet
    covers := B.covers
    trivialization := trivialization B e
    trivialization_baseSet := trivialization_baseSet B e
    linear := trivialization_linear B e
    coordinates := B.coordinates
    totalManifold := manifold B e
    chart_mem := ?_
    projection_smooth := ?_
    zero_smooth := ?_
    add_smooth := ?_
    smul_smooth := ?_ }
  · intro i c hc
    change bundleChart B.coordinates (trivialization B e i) c ∈
      transportAtlas H.symm B.totalManifold.smoothStructure.val
    refine ⟨bundleChart B.coordinates (B.trivialization i) c, B.chart_mem i c hc, ?_⟩
    change H.toOpenPartialHomeomorph.trans
      ((B.trivialization i).toOpenPartialHomeomorph.trans
        (productChart B.coordinates c (fiberChart r))) =
      (H.transOpenPartialHomeomorph (B.trivialization i).toOpenPartialHomeomorph).trans
        (productChart B.coordinates c (fiberChart r))
    rw [Homeomorph.transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc]
  · exact manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
      B.totalManifold.smoothStructure.property.1.1 H TotalSpace.proj
      hmaps.1 B.projection_smooth
  · have hz := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
      B.totalManifold.smoothStructure.property.1.1
      (fun p : M => (⟨p, 0⟩ : TotalSpace (Euclidean r) E)) H.symm
      B.zero_smooth hmaps.2
    have heq : (H.symm ∘ (fun p : M => (⟨p, 0⟩ : TotalSpace (Euclidean r) E))) =
        (fun p : M => (⟨p, 0⟩ : TotalSpace (Euclidean r) F)) := by
      funext p
      change (⟨p, (e p).symm 0⟩ : TotalSpace (Euclidean r) F) = ⟨p, 0⟩
      rw [LinearEquiv.map_zero]
    rw [heq] at hz
    exact hz
  · intro i
    have hh := smoothWithParameters_transport H.symm (B.add_smooth i)
    have hU : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
    apply SmoothWithParameters.congr hU hh
    intro q hq
    change (⟨q.1, (e q.1).symm
      ((B.trivialization i).symm q.1 q.2.1 + (B.trivialization i).symm q.1 q.2.2)⟩ :
      TotalSpace (Euclidean r) F) = _
    congr 1
    rw [LinearEquiv.map_add, trivialization_symm B e i q.1 hq,
      trivialization_symm B e i q.1 hq]
  · intro i
    have hh := smoothWithParameters_transport H.symm (B.smul_smooth i)
    have hU : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
    apply SmoothWithParameters.congr hU hh
    intro q hq
    change (⟨q.1, (e q.1).symm (q.2.1 • (B.trivialization i).symm q.1 q.2.2)⟩ :
      TotalSpace (Euclidean r) F) = _
    congr 1
    rw [LinearEquiv.map_smul, trivialization_symm B e i q.1 hq]


@[simp] theorem bundle_baseSet (i : ι) : letI := topology (r := r) e
    (bundle B e).baseSet i = B.baseSet i := rfl

@[simp] theorem bundle_fiberCoordinates (i : ι) (p : M) (hp : p ∈ B.baseSet i) (v : F p) :
    letI := topology (r := r) e
    (bundle B e).fiberCoordinates i p hp v = B.fiberCoordinates i p hp (e p v) := rfl

end
end Transport

section LocalLinearAlgebra

/-- The synthesis operator of a finite family of Euclidean vectors. -/
noncomputable def columnOperator {r k : ℕ} (v : Fin k → Euclidean r) :
    Euclidean k →L[ℝ] Euclidean r :=
  ∑ j : Fin k, (ContinuousLinearMap.proj j).smulRight (v j)

@[simp] theorem columnOperator_apply {r k : ℕ} (v : Fin k → Euclidean r)
    (c : Euclidean k) : columnOperator v c = ∑ j, c j • v j := by
  simp [columnOperator]

@[simp] theorem columnOperator_single {r k : ℕ} (v : Fin k → Euclidean r)
    (j : Fin k) : columnOperator v (Pi.single j 1) = v j := by
  classical
  simp [columnOperator_apply, Pi.single_apply, ite_smul]

theorem columnOperator_injective {r k : ℕ} {v : Fin k → Euclidean r}
    (hv : LinearIndependent ℝ v) : Function.Injective (columnOperator v) := by
  intro c d h
  apply hv.fintypeLinearCombination_injective
  simpa only [Fintype.linearCombination_apply, columnOperator_apply] using h

/-- A smooth perturbation of the identity transporting a given independent
family to its nearby values. This avoids choosing minors or ordering a
complement, and works unchanged for empty families. -/
theorem exists_local_columnTransport {n r k : ℕ} {a : ModelKind}
    {X : Type u} [TopologicalSpace X] (A : Set (ModelChart n a X))
    (v : X → Fin k → Euclidean r) (V : Set X) (hVopen : IsOpen V)
    (hv : ∀ j y, y ∈ V → VectorSmoothAt A (fun x => v x j) y)
    (x : X) (hxV : x ∈ V) (hx : LinearIndependent ℝ (v x)) :
    ∃ T : X → (Euclidean r →L[ℝ] Euclidean r),
      (∀ y ∈ V, VectorSmoothAt A T y) ∧ T x = ContinuousLinearMap.id ℝ (Euclidean r) ∧
      (∀ y j, T y (v x j) = v y j) ∧
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ ∀ y ∈ U, (T y).IsInvertible := by
  classical
  let C := fun y => columnOperator (v y)
  have hC : ∀ y ∈ V, VectorSmoothAt A C y := by
    intro y hy
    apply FrameData.VectorSmoothAt.sum
    intro j
    exact (hv j y hy).postcomp (contDiff_const.smulRight contDiff_id)
  obtain ⟨L, hL⟩ := (C x).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (columnOperator_injective hx))
  let L' : Euclidean r →L[ℝ] Euclidean k := L.toContinuousLinearMap
  let T := fun y => ContinuousLinearMap.id ℝ (Euclidean r) +
    ((C y - C x).comp L')
  have hT : ∀ y ∈ V, VectorSmoothAt A T y := by
    intro y hy
    exact (hC y hy).postcomp
      (contDiff_const.add ((contDiff_id.sub contDiff_const).clm_comp contDiff_const))
  have hTx : T x = ContinuousLinearMap.id ℝ (Euclidean r) := by simp [T]
  have hTinv : (T x).IsInvertible := by
    rw [hTx]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hnhds : ∀ᶠ y in 𝓝 x, (T y).IsInvertible :=
    (hT x hxV).1.preimage_mem_nhds hTinv.eventually_nhds
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnhds
  refine ⟨T, hT, hTx, ?_, U ∩ V, hU.inter hVopen, ⟨hxU, hxV⟩,
    inter_subset_right, fun y hy => hUsub hy.1⟩
  intro y j
  have hLj : L' (v x j) = Pi.single j 1 := by
    change L (v x j) = _
    have hh := LinearMap.congr_fun hL (Pi.single j 1)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply,
      ContinuousLinearMap.coe_coe, columnOperator_single, C] using hh
  simp [T, hLj, C]

end LocalLinearAlgebra

section Algebra
variable {M : Type u} {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  (K : (p : M) → Submodule ℝ (E p))

theorem quotientProjection_surjective (p : M) :
    Function.Surjective (quotientProjection K p) := (K p).mkQ_surjective

theorem quotientProjection_kernel (p : M) :
    LinearMap.ker (quotientProjection K p) = K p := (K p).ker_mkQ

@[simp] theorem quotientLift_projection (A : (p : M) → E p →ₗ[ℝ] F p)
    (hA : VanishesOn K A) (p : M) (v : E p) :
    quotientLift K A hA p (quotientProjection K p v) = A p v := rfl

theorem quotientLift_comp (A : (p : M) → E p →ₗ[ℝ] F p)
    (hA : VanishesOn K A) (p : M) :
    (quotientLift K A hA p).comp (quotientProjection K p) = A p :=
  (K p).liftQ_mkQ _ _

/-- Algebraic uniqueness needs neither smoothness nor a rank assumption. -/
theorem quotientLift_unique (A : (p : M) → E p →ₗ[ℝ] F p) (hA : VanishesOn K A)
    (L : (p : M) → QuotientFiber K p →ₗ[ℝ] F p)
    (hL : ∀ p, (L p).comp (quotientProjection K p) = A p) :
    L = quotientLift K A hA := by
  funext p
  apply (K p).linearMap_qext
  exact (hL p).trans (quotientLift_comp K A hA p).symm

/-- The zero-submodule quotient has the canonical, rather than a chosen,
linear identification with the original fiber. -/
theorem quotient_zero :
    ∃ e : (p : M) → QuotientFiber (fun q => (⊥ : Submodule ℝ (E q))) p ≃ₗ[ℝ] E p,
      ∀ p v, e p (quotientProjection (fun q => (⊥ : Submodule ℝ (E q))) p v) = v := by
  exact ⟨fun p => (⊥ : Submodule ℝ (E p)).quotEquivOfEqBot rfl, fun _ _ => rfl⟩

/-- Quotienting by the full fiber really gives the zero vector space. -/
theorem quotient_full (p : M)
    (v : QuotientFiber (fun q => (⊤ : Submodule ℝ (E q))) p) : v = 0 :=
  Subsingleton.elim _ _

end Algebra

section Bundle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (K : (p : M) → Submodule ℝ (E p)) (k : ℕ)

include B in
/-- Finite dimensionality follows from the original bundle trivializations. -/
theorem fiber_finrank (p : M) : Module.finrank ℝ (E p) = r := by
  obtain ⟨i, hi⟩ := B.covers p
  calc
    Module.finrank ℝ (E p) = Module.finrank ℝ (Euclidean r) :=
      (B.fiberCoordinates i p hi).finrank_eq
    _ = r := Module.finrank_fin_fun ℝ

/-- A smooth local subbundle basis fixes its fiber dimension. -/
theorem subbundle_finrank (hK : SmoothSubbundle B K k) (p : M) :
    Module.finrank ℝ (K p) = k := by
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := hK p
  simpa using Module.finrank_eq_card_basis (b.basis ⟨p, hp⟩)

/-- In particular, the empty-base case does not force an artificial global
inequality k ≤ r: the bound is asserted at an actual base point. -/
theorem quotient_finrank (hK : SmoothSubbundle B K k) (p : M) :
    k ≤ r ∧ Module.finrank ℝ (QuotientFiber K p) = r - k := by
  obtain ⟨i, hi⟩ := B.covers p
  letI : FiniteDimensional ℝ (E p) :=
    Module.Finite.equiv (B.fiberCoordinates i p hi).symm
  have hr := fiber_finrank B p
  have hk := subbundle_finrank B K k hK p
  have hsum := (K p).finrank_quotient_add_finrank
  rw [hr, hk] at hsum
  constructor
  · omega
  · exact Nat.eq_sub_of_add_eq hsum

/-- The original trivializations give smooth local frames of E without any
additional regularity assumption on its algebraic fibers. -/
noncomputable def trivializationFrame (i : ι) :
    LocalFrame B (B.baseSet i)
      ((B.trivialization_baseSet i) ▸ (B.trivialization i).open_baseSet) where
  section_ j p := (B.fiberCoordinates i p.val p.property).symm (Pi.single j 1)
  basis p := Basis.ofEquivFun (B.fiberCoordinates i p.val p.property)
  basis_eq p j := congrFun (Basis.coe_ofEquivFun _) j
  smooth j p := by
    apply Frames.smoothAt_of_sectionCoordinates B (B.baseSet i)
      ((B.trivialization_baseSet i) ▸ (B.trivialization i).open_baseSet) i
      (fun p => (B.fiberCoordinates i p.val p.property).symm (Pi.single j 1)) p p.property
    apply (FrameData.VectorSmoothAt.const _ (Pi.single j 1) p).congr
    exact Filter.Eventually.of_forall (fun y =>
      (B.fiberCoordinates i y.val y.property).apply_symm_apply (Pi.single j 1) |>.symm)

/-- The zero subbundle meets the local-frame hypothesis, also at rank zero. -/
theorem smoothSubbundle_zero :
    SmoothSubbundle B (fun p => (⊥ : Submodule ℝ (E p))) 0 := by
  intro p
  refine ⟨univ, isOpen_univ, mem_univ p, ⟨?_⟩⟩
  exact { basis := fun _ => Basis.empty _
          smooth := fun j => Fin.elim0 j }

/-- The full subbundle meets the same hypothesis, with its original rank. -/
theorem smoothSubbundle_full :
    SmoothSubbundle B (fun p => (⊤ : Submodule ℝ (E p))) r := by
  intro p
  obtain ⟨i, hi⟩ := B.covers p
  let hU : IsOpen (B.baseSet i) :=
    (B.trivialization_baseSet i) ▸ (B.trivialization i).open_baseSet
  let b := trivializationFrame B i
  refine ⟨B.baseSet i, hU, hi, ⟨?_⟩⟩
  refine { basis := fun q => (b.basis q).map (Submodule.topEquiv.symm)
           smooth := ?_ }
  intro j
  simpa [Basis.map_apply, b.basis_eq, Submodule.topEquiv] using b.smooth j

/-- Local Euclidean coordinates in which the subbundle is transported from a
fixed subspace by a smooth family of invertible operators. The reference
subspace need not be a coordinate plane; any fixed linear identification of
its quotient with Euclidean space can subsequently be used. -/
structure LocalSubbundleCoordinates where
  domain : Set M
  isOpen_domain : IsOpen domain
  index : ι
  in_baseSet : domain ⊆ B.baseSet index
  reference : Submodule ℝ (Euclidean r)
  reference_finrank : Module.finrank ℝ reference = k
  change : M → (Euclidean r →L[ℝ] Euclidean r)
  smooth : ∀ p ∈ domain, VectorSmoothAt S.smoothStructure.val change p
  invertible : ∀ p ∈ domain, (change p).IsInvertible
  submodule_eq : ∀ p (hp : p ∈ domain),
    (K p).map (B.fiberCoordinates index p (in_baseSet hp)).toLinearMap =
      reference.map (change p).toLinearMap

/-- Straightening a smooth subbundle needs only its given local basis, not an
already adapted frame or a quotient bundle. -/
theorem exists_localSubbundleCoordinates (hK : SmoothSubbundle B K k) (p : M) :
    ∃ C : LocalSubbundleCoordinates B K k, p ∈ C.domain := by
  classical
  obtain ⟨U, hU, hpU, ⟨b⟩⟩ := hK p
  obtain ⟨i, hpi⟩ := B.covers p
  let V := U ∩ B.baseSet i
  have hV : IsOpen V := hU.inter
    ((B.trivialization_baseSet i) ▸ (B.trivialization i).open_baseSet)
  let v : M → Fin k → Euclidean r := fun q j =>
    FrameData.totalize (Frames.sectionCoordinates B U i
      (fun q : U => (b.basis q j).val)) q
  have hv_eq (q : M) (hq : q ∈ V) (j : Fin k) :
      v q j = B.fiberCoordinates i q hq.2 (b.basis ⟨q, hq.1⟩ j).val := by
    rw [show v q j = FrameData.totalize _ q from rfl,
      FrameData.totalize_of_mem _ q hq.1]
    rfl
  have hv : ∀ j q, q ∈ V → VectorSmoothAt S.smoothStructure.val (fun q => v q j) q := by
    intro j q hq
    exact (Frames.sectionCoordinates_smoothAt B U hU i
      (fun q : U => (b.basis q j).val) ⟨q, hq.1⟩ hq.2 (b.smooth j ⟨q, hq.1⟩)).totalize hU
  have hspan (q : M) (hq : q ∈ V) :
      Submodule.span ℝ (Set.range (v q)) =
        (K q).map (B.fiberCoordinates i q hq.2).toLinearMap := by
    have hh := congrArg
      (Submodule.map ((B.fiberCoordinates i q hq.2).toLinearMap.comp (K q).subtype))
      (b.basis ⟨q, hq.1⟩).span_eq
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_comp,
      Submodule.range_subtype] at hh
    rw [← hh, ← Set.range_comp]
    congr 2
    funext j
    exact hv_eq q hq j
  have hpV : p ∈ V := ⟨hpU, hpi⟩
  have hli : LinearIndependent ℝ (v p) := by
    have hh := (b.basis ⟨p, hpU⟩).linearIndependent.map'
      ((B.fiberCoordinates i p hpi).toLinearMap.comp (K p).subtype)
      (LinearMap.ker_eq_bot.mpr ((B.fiberCoordinates i p hpi).injective.comp Subtype.val_injective))
    convert hh using 1
    funext j
    exact hv_eq p hpV j
  obtain ⟨T, hT, hTp, hTv, W, hW, hpW, hWV, hWinv⟩ :=
    exists_local_columnTransport S.smoothStructure.val v V hV hv p hpV hli
  let P := (K p).map (B.fiberCoordinates i p hpi).toLinearMap
  have hrank : Module.finrank ℝ P = k := by
    rw [← subbundle_finrank B K k hK p]
    exact ((K p).equivMapOfInjective _ (B.fiberCoordinates i p hpi).injective).finrank_eq.symm
  refine ⟨{ domain := W
            isOpen_domain := hW
            index := i
            in_baseSet := fun q hq => (hWV hq).2
            reference := P
            reference_finrank := hrank
            change := T
            smooth := fun q hq => hT q (hWV hq)
            invertible := hWinv
            submodule_eq := ?_ }, hpW⟩
  intro q hq
  change (K q).map (B.fiberCoordinates i q (hWV hq).2).toLinearMap =
    P.map (T q).toLinearMap
  rw [← hspan q (hWV hq)]
  change Submodule.span ℝ (Set.range (v q)) =
    ((K p).map (B.fiberCoordinates i p hpi).toLinearMap).map (T q).toLinearMap
  rw [← hspan p hpV, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact (hTv q j).symm

namespace LocalSubbundleCoordinates
variable {B K k} (C : LocalSubbundleCoordinates B K k)

/-- The invertible coordinate change, only on its proved domain. -/
noncomputable def changeEquiv (p : M) (hp : p ∈ C.domain) :
    Euclidean r ≃L[ℝ] Euclidean r := Classical.choose (C.invertible p hp)

@[simp] theorem changeEquiv_coe (p : M) (hp : p ∈ C.domain) :
    (C.changeEquiv p hp).toContinuousLinearMap = C.change p :=
  Classical.choose_spec (C.invertible p hp)

noncomputable def ambientEquiv (p : M) (hp : p ∈ C.domain) :
    E p ≃ₗ[ℝ] Euclidean r :=
  (B.fiberCoordinates C.index p (C.in_baseSet hp)).trans
    (C.changeEquiv p hp).symm.toLinearEquiv

theorem ambientEquiv_submodule (p : M) (hp : p ∈ C.domain) :
    (K p).map (C.ambientEquiv p hp).toLinearMap = C.reference := by
  change (K p).map ((C.changeEquiv p hp).symm.toLinearEquiv.toLinearMap.comp
    (B.fiberCoordinates C.index p (C.in_baseSet hp)).toLinearMap) = _
  rw [Submodule.map_comp, C.submodule_eq p hp]
  apply Submodule.ext
  intro v
  constructor
  · rintro ⟨w, ⟨z, hz, hzw⟩, hwv⟩
    have hchange : C.change p z = C.changeEquiv p hp z :=
      congrArg (fun f : Euclidean r →L[ℝ] Euclidean r => f z)
        (C.changeEquiv_coe p hp).symm
    change (C.changeEquiv p hp).symm w = v at hwv
    change C.change p z = w at hzw
    rw [hchange] at hzw
    rw [← hzw, ContinuousLinearEquiv.symm_apply_apply] at hwv
    exact hwv ▸ hz
  · intro hv
    refine ⟨C.changeEquiv p hp v, ⟨v, hv, ?_⟩,
      (C.changeEquiv p hp).symm_apply_apply v⟩
    exact congrArg (fun f : Euclidean r →L[ℝ] Euclidean r => f v)
      (C.changeEquiv_coe p hp).symm

theorem quotient_finrank : Module.finrank ℝ (Euclidean r ⧸ C.reference) = r - k := by
  have h := C.reference.finrank_quotient_add_finrank
  rw [C.reference_finrank, Module.finrank_fin_fun] at h
  exact Nat.eq_sub_of_add_eq h

/-- A single constant choice is made for the reference quotient, rather than
unrelated choices of bases in the varying quotient fibers. -/
noncomputable def referenceEquiv :
    (Euclidean r ⧸ C.reference) ≃ₗ[ℝ] Euclidean (r - k) :=
  Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by
    rw [C.quotient_finrank, Module.finrank_fin_fun]))

/-- Coordinates on the actual quotient fibers, induced by the ambient change. -/
noncomputable def quotientEquiv (p : M) (hp : p ∈ C.domain) :
    QuotientFiber K p ≃ₗ[ℝ] Euclidean (r - k) :=
  (Submodule.Quotient.equiv (K p) C.reference (C.ambientEquiv p hp)
    (C.ambientEquiv_submodule p hp)).trans C.referenceEquiv

noncomputable def referenceProjection : Euclidean r →L[ℝ] Euclidean (r - k) :=
  (C.referenceEquiv.toLinearMap.comp C.reference.mkQ).toContinuousLinearMap

noncomputable def projectionMatrix (p : M) : Euclidean r →L[ℝ] Euclidean (r - k) :=
  C.referenceProjection.comp (ContinuousLinearMap.inverse (C.change p))

theorem projectionMatrix_smooth (p : M) (hp : p ∈ C.domain) :
    VectorSmoothAt S.smoothStructure.val C.projectionMatrix p :=
  ((C.smooth p hp).inverse (C.invertible p hp)).postcomp
    (contDiff_const.clm_comp contDiff_id)

theorem quotientEquiv_projection (p : M) (hp : p ∈ C.domain) (v : E p) :
    C.quotientEquiv p hp (quotientProjection K p v) =
      C.projectionMatrix p (B.fiberCoordinates C.index p (C.in_baseSet hp) v) := by
  change C.referenceEquiv (C.reference.mkQ ((C.changeEquiv p hp).symm
    (B.fiberCoordinates C.index p (C.in_baseSet hp) v))) = _
  rw [projectionMatrix, ← C.changeEquiv_coe p hp, ContinuousLinearMap.inverse_equiv]
  rfl

theorem referenceProjection_surjective : Function.Surjective C.referenceProjection :=
  C.referenceEquiv.surjective.comp C.reference.mkQ_surjective

/-- A fixed linear section of the reference projection. Its coefficients are
constant, so smoothness is automatic; no global complement of K is used. -/
noncomputable def referenceSection : Euclidean (r - k) →L[ℝ] Euclidean r :=
  Classical.choose (C.referenceProjection.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr C.referenceProjection_surjective))

theorem referenceProjection_section :
    C.referenceProjection.comp C.referenceSection = ContinuousLinearMap.id ℝ _ :=
  Classical.choose_spec (C.referenceProjection.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr C.referenceProjection_surjective))

noncomputable def sectionMatrix (p : M) : Euclidean (r - k) →L[ℝ] Euclidean r :=
  (C.change p).comp C.referenceSection

theorem sectionMatrix_smooth (p : M) (hp : p ∈ C.domain) :
    VectorSmoothAt S.smoothStructure.val C.sectionMatrix p :=
  (C.smooth p hp).postcomp (contDiff_id.clm_comp contDiff_const)

theorem projectionMatrix_sectionMatrix (p : M) (hp : p ∈ C.domain)
    (v : Euclidean (r - k)) : C.projectionMatrix p (C.sectionMatrix p v) = v := by
  have hh := congrArg (fun f : Euclidean (r - k) →L[ℝ] Euclidean (r - k) => f v)
    C.referenceProjection_section
  dsimp [projectionMatrix, sectionMatrix]
  rw [← C.changeEquiv_coe p hp, ContinuousLinearMap.inverse_equiv]
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hh

/-- Smooth local representatives for every quotient class. This identity is
also the local right inverse needed for smooth descent. -/
theorem quotientEquiv_symm (p : M) (hp : p ∈ C.domain) (v : Euclidean (r - k)) :
    (C.quotientEquiv p hp).symm v = quotientProjection K p
      ((B.fiberCoordinates C.index p (C.in_baseSet hp)).symm (C.sectionMatrix p v)) := by
  apply (C.quotientEquiv p hp).injective
  rw [LinearEquiv.apply_symm_apply, C.quotientEquiv_projection,
    LinearEquiv.apply_symm_apply, C.projectionMatrix_sectionMatrix p hp]

end LocalSubbundleCoordinates

namespace LocalSubbundleCoordinates
variable {B K k} (C : LocalSubbundleCoordinates B K k)

/-- Coordinates of the quotient projection are smooth on every local domain. -/
theorem projectionCoordinates_smoothAt (q : TotalSpace (Euclidean r) E)
    (hq : q.proj ∈ C.domain) :
    VectorSmoothAt B.totalManifold.smoothStructure.val
      (fun y : TotalSpace (Euclidean r) E =>
        C.projectionMatrix y.proj (((B.trivialization C.index) y).2)) q := by
  have hmat := FrameData.VectorSmoothAt.comp S.smoothStructure.property.1.1
    (C.projectionMatrix_smooth q.proj hq) (B.projection_smooth q)
  exact hmat.clm_apply (Frames.trivializationCoordinates_smoothAt B C.index q
    (C.in_baseSet hq))

/-- Actual smooth representatives for smoothly varying quotient coordinates. -/
theorem smoothAt_representative {d : ℕ} {b : ModelKind} {X : Type z}
    [TopologicalSpace X] {A : Set (ModelChart d b X)}
    (hA : IsContDiffAtlas (⊤ : ℕ∞) A) {h : X → M}
    {v : X → Euclidean (r-k)} {x : X} (hx : h x ∈ C.domain)
    (hh : ManifoldSmoothAt A S.smoothStructure.val h x)
    (hv : VectorSmoothAt A v x) :
    ManifoldSmoothAt A B.totalManifold.smoothStructure.val
      (fun y => (⟨h y, (B.trivialization C.index).symm (h y)
        (C.sectionMatrix (h y) (v y))⟩ : TotalSpace (Euclidean r) E)) x := by
  have hmat := FrameData.VectorSmoothAt.comp S.smoothStructure.property.1.1
    (C.sectionMatrix_smooth (h x) hx) hh
  apply Frames.smoothAt_from_trivialization B hA C.index (C.in_baseSet hx)
    hh (hmat.clm_apply hv) (fun _ => rfl)
  filter_upwards [hh.1.preimage_mem_nhds (C.isOpen_domain.mem_nhds hx)] with y hy
  change (B.fiberCoordinates C.index (h y) (C.in_baseSet hy))
    ((B.fiberCoordinates C.index (h y) (C.in_baseSet hy)).symm
      (C.sectionMatrix (h y) (v y))) = C.sectionMatrix (h y) (v y)
  exact LinearEquiv.apply_symm_apply _ _

end LocalSubbundleCoordinates

/-- The matrix of an original bundle transition, with harmless values away
from its overlap. -/
noncomputable def bundleTransitionOperator (i j : ι) (p : M) :
    Euclidean r →L[ℝ] Euclidean r :=
  columnOperator (fun l => ((B.trivialization j)
    (⟨p, (B.trivialization i).symm p (Pi.single l 1)⟩ : TotalSpace (Euclidean r) E)).2)

theorem bundleTransitionOperator_apply (i j : ι) (p : M)
    (hi : p ∈ B.baseSet i) (hj : p ∈ B.baseSet j) (v : Euclidean r) :
    bundleTransitionOperator B i j p v = B.fiberCoordinates j p hj
      ((B.fiberCoordinates i p hi).symm v) := by
  have hh : (bundleTransitionOperator B i j p).toLinearMap =
      ((B.fiberCoordinates i p hi).symm.trans (B.fiberCoordinates j p hj)).toLinearMap := by
    apply (Pi.basisFun ℝ (Fin r)).ext
    intro l
    rw [Pi.basisFun_apply]
    change columnOperator _ (Pi.single l 1) = _
    rw [columnOperator_single]
    rfl
  exact LinearMap.congr_fun hh v

theorem bundleTransitionOperator_smooth (i j : ι) (p : M)
    (hi : p ∈ B.baseSet i) (hj : p ∈ B.baseSet j) :
    VectorSmoothAt S.smoothStructure.val (bundleTransitionOperator B i j) p := by
  let U := B.baseSet i
  have hU : IsOpen U := by
    change IsOpen (B.baseSet i)
    exact (B.trivialization_baseSet i) ▸ (B.trivialization i).open_baseSet
  let b := trivializationFrame B i
  unfold bundleTransitionOperator columnOperator
  apply FrameData.VectorSmoothAt.sum
  intro l
  have hh := (Frames.sectionCoordinates_smoothAt B U hU j (b.section_ l)
    ⟨p, hi⟩ hj (b.smooth l ⟨p, hi⟩)).totalize hU
  apply (hh.postcomp (contDiff_const.smulRight contDiff_id)).congr
  filter_upwards [hU.mem_nhds hi] with q hq
  rw [FrameData.totalize_of_mem _ q hq]
  rfl

namespace LocalSubbundleCoordinates
variable {B K k} (C D : LocalSubbundleCoordinates B K k)

/-- Quotient transitions are ordinary smooth products of rectangular matrices. -/
noncomputable def transitionMatrix (p : M) :
    Euclidean (r - k) →L[ℝ] Euclidean (r - k) :=
  (D.projectionMatrix p).comp ((bundleTransitionOperator B C.index D.index p).comp
    (C.sectionMatrix p))

theorem transitionMatrix_smooth (p : M) (hpC : p ∈ C.domain) (hpD : p ∈ D.domain) :
    VectorSmoothAt S.smoothStructure.val (C.transitionMatrix D) p := by
  have hB := bundleTransitionOperator_smooth B C.index D.index p
    (C.in_baseSet hpC) (D.in_baseSet hpD)
  exact ((D.projectionMatrix_smooth p hpD).prod
    (hB.prod (C.sectionMatrix_smooth p hpC))).postcomp
      (contDiff_fst.clm_comp (contDiff_snd.fst.clm_comp contDiff_snd.snd))

theorem transitionMatrix_apply (p : M) (hpC : p ∈ C.domain) (hpD : p ∈ D.domain)
    (v : Euclidean (r - k)) : C.transitionMatrix D p v =
      D.quotientEquiv p hpD ((C.quotientEquiv p hpC).symm v) := by
  rw [C.quotientEquiv_symm p hpC, D.quotientEquiv_projection p hpD]
  dsimp [transitionMatrix]
  rw [bundleTransitionOperator_apply B C.index D.index p
    (C.in_baseSet hpC) (D.in_baseSet hpD)]
  rfl

end LocalSubbundleCoordinates

/-- One proved local quotient-coordinate neighborhood at every base point. -/
structure QuotientCoordinateCover where
  localCoordinates : M → LocalSubbundleCoordinates B K k
  center_mem : ∀ p, p ∈ (localCoordinates p).domain

noncomputable def quotientCoordinateCover (hK : SmoothSubbundle B K k) :
    QuotientCoordinateCover B K k where
  localCoordinates p := Classical.choose (exists_localSubbundleCoordinates B K k hK p)
  center_mem p := Classical.choose_spec (exists_localSubbundleCoordinates B K k hK p)

namespace QuotientCoordinateCover
variable {B K k} (C : QuotientCoordinateCover B K k)

/-- The actual changes between quotient-fiber coordinates form a smooth
overlap cocycle; the cocycle identities follow from those linear equivalences. -/
noncomputable def overlapCocycle : OverlapCocycle S (r - k) M where
  baseSet i := (C.localCoordinates i).domain
  isOpen_baseSet i := (C.localCoordinates i).isOpen_domain
  covers p := ⟨p, C.center_mem p⟩
  g i j p := (((C.localCoordinates i).quotientEquiv p.val p.property.1).symm.trans
    ((C.localCoordinates j).quotientEquiv p.val p.property.2)).toContinuousLinearEquiv
  self i p hp := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact ((C.localCoordinates i).quotientEquiv p hp).apply_symm_apply v
  comp i j l p hi hj hl := by
    apply ContinuousLinearMap.ext
    intro v
    change (C.localCoordinates l).quotientEquiv p hl
      (((C.localCoordinates j).quotientEquiv p hj).symm
        ((C.localCoordinates j).quotientEquiv p hj
          (((C.localCoordinates i).quotientEquiv p hi).symm v))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  smooth i j p := by
    let T := (C.localCoordinates i).transitionMatrix (C.localCoordinates j)
    have heq : (fun q : ↥((C.localCoordinates i).domain ∩ (C.localCoordinates j).domain) =>
        ((((C.localCoordinates i).quotientEquiv q.val q.property.1).symm.trans
          ((C.localCoordinates j).quotientEquiv q.val q.property.2)).toContinuousLinearEquiv :
            Euclidean (r - k) →L[ℝ] Euclidean (r - k))) = fun q => T q.val := by
      funext q
      apply ContinuousLinearMap.ext
      intro v
      exact ((C.localCoordinates i).transitionMatrix_apply (C.localCoordinates j)
        q.val q.property.1 q.property.2 v).symm
    rw [heq]
    have hT := (C.localCoordinates i).transitionMatrix_smooth (C.localCoordinates j)
      p.val p.property.1 p.property.2
    refine ⟨hT.1.comp continuousAt_subtype_val, ?_⟩
    intro c hc hp
    obtain ⟨W, hW, hpW, F, hF, heF⟩ := hT.2 c hc hp
    exact ⟨W, hW, hpW, F, hF, heF.comp_tendsto continuousAt_subtype_val⟩

/-- Gluing has now been performed with exactly the transitions of the
algebraic quotient fibers. Transport to those fibers is a separate step. -/
noncomputable def glued : GluedBundle C.overlapCocycle.totalize :=
  Classical.choice (exists_gluedBundle C.overlapCocycle.totalize)

variable (G : GluedBundle C.overlapCocycle.totalize)

local instance gluedFiberAddCommGroup (p : M) : AddCommGroup (G.Fiber p) := G.addCommGroup p
local instance gluedFiberModule (p : M) : Module ℝ (G.Fiber p) := G.module p
local instance gluedTotalTopology : TopologicalSpace (TotalSpace (Euclidean (r-k)) G.Fiber) := G.topology
noncomputable def realizationEquiv (p : M) : QuotientFiber K p ≃ₗ[ℝ] G.Fiber p :=
  ((C.localCoordinates p).quotientEquiv p (C.center_mem p)).trans
    (G.bundle.fiberCoordinates p p ((G.realizes.1 p).symm ▸ C.center_mem p)).symm

theorem realizationEquiv_coordinates (i : M) (p : M)
    (hp : p ∈ (C.localCoordinates i).domain) (v : QuotientFiber K p) :
    ((G.bundle.trivialization i) ⟨p, C.realizationEquiv G p v⟩).2 =
      (C.localCoordinates i).quotientEquiv p hp v := by
  have hh := G.bundle.coordinates_transition G.realizes p i p (C.center_mem p) hp
    (C.realizationEquiv G p v)
  rw [hh]
  change C.overlapCocycle.totalTransition p i p _ = _
  rw [C.overlapCocycle.totalTransition_eq p i p (C.center_mem p) hp]
  change (C.localCoordinates i).quotientEquiv p hp
    (((C.localCoordinates p).quotientEquiv p (C.center_mem p)).symm
      (G.bundle.fiberCoordinates p p ((G.realizes.1 p).symm ▸ C.center_mem p)
        (C.realizationEquiv G p v))) = _
  simp only [realizationEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply]

end QuotientCoordinateCover

namespace QuotientCoordinateCover
variable {B K k} (C : QuotientCoordinateCover B K k)
  [TopologicalSpace (TotalSpace (Euclidean (r-k)) (QuotientFiber K))]
  (Q : SmoothVectorBundle S (r-k) M (QuotientFiber K))
  (hbase : ∀ i, Q.baseSet i = (C.localCoordinates i).domain)
  (hcoord : ∀ i p (hp : p ∈ Q.baseSet i), Q.fiberCoordinates i p hp =
    (C.localCoordinates i).quotientEquiv p ((hbase i) ▸ hp))

include C hbase hcoord in
/-- The coordinate construction makes the canonical quotient projection smooth. -/
theorem projection_smooth_of_coordinates :
    IsSmoothMap B.totalManifold Q.totalManifold
      (fun q => (⟨q.proj, quotientProjection K q.proj q.snd⟩ :
        TotalSpace (Euclidean (r-k)) (QuotientFiber K))) := by
  intro q
  let i := q.proj
  let D := C.localCoordinates i
  have hqD : q.proj ∈ D.domain := C.center_mem q.proj
  have hqi : q.proj ∈ Q.baseSet i := (hbase i) ▸ hqD
  apply Frames.smoothAt_from_trivialization Q
    B.totalManifold.smoothStructure.property.1 i hqi (B.projection_smooth q)
    (D.projectionCoordinates_smoothAt q hqD) (fun _ => rfl)
  have hopen := D.isOpen_domain
  filter_upwards [(B.projection_smooth q).1.preimage_mem_nhds (hopen.mem_nhds hqD)] with y hy
  have hyi : y.proj ∈ Q.baseSet i := (hbase i) ▸ hy
  change Q.fiberCoordinates i y.proj hyi (quotientProjection K y.proj y.snd) = _
  rw [hcoord i y.proj hyi]
  exact D.quotientEquiv_projection y.proj hy y.snd

include C hbase hcoord in
/-- Smoothness descends because quotient coordinates have smooth local representatives. -/
theorem descent_smooth_of_coordinates {s : ℕ} {κ : Type t} {F : M → Type z}
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean s) F)]
    (T : SmoothVectorBundle S s κ F)
    (L : (p : M) → QuotientFiber K p →ₗ[ℝ] F p)
    (hL : IsSmoothMap B.totalManifold T.totalManifold
      (fun q => (⟨q.proj, L q.proj (quotientProjection K q.proj q.snd)⟩ :
        TotalSpace (Euclidean s) F))) :
    IsSmoothMap Q.totalManifold T.totalManifold
      (fun q => (⟨q.proj, L q.proj q.snd⟩ : TotalSpace (Euclidean s) F)) := by
  intro q
  let i := q.proj
  let D := C.localCoordinates i
  have hqD : q.proj ∈ D.domain := C.center_mem q.proj
  have hqi : q.proj ∈ Q.baseSet i := (hbase i) ▸ hqD
  let f : TotalSpace (Euclidean (r-k)) (QuotientFiber K) → TotalSpace (Euclidean r) E :=
    fun y => ⟨y.proj, (B.trivialization D.index).symm y.proj
      (D.sectionMatrix y.proj (((Q.trivialization i) y).2))⟩
  have hf : ManifoldSmoothAt Q.totalManifold.smoothStructure.val
      B.totalManifold.smoothStructure.val f q := by
    exact D.smoothAt_representative Q.totalManifold.smoothStructure.property.1 hqD
      (Q.projection_smooth q) (Frames.trivializationCoordinates_smoothAt Q i q hqi)
  have hcomp := manifoldContDiffAt_comp B.totalManifold.smoothStructure.property.1.1
    hf (hL (f q))
  apply manifoldContDiffAt_congr hcomp
  filter_upwards [(Q.projection_smooth q).1.preimage_mem_nhds
    (D.isOpen_domain.mem_nhds hqD)] with y hy
  have hyi : y.proj ∈ Q.baseSet i := (hbase i) ▸ hy
  have hreps : quotientProjection K y.proj
      ((B.trivialization D.index).symm y.proj
        (D.sectionMatrix y.proj (((Q.trivialization i) y).2))) = y.snd := by
    change quotientProjection K y.proj
      ((B.fiberCoordinates D.index y.proj (D.in_baseSet hy)).symm
        (D.sectionMatrix y.proj (Q.fiberCoordinates i y.proj hyi y.snd))) = y.snd
    rw [hcoord i y.proj hyi, ← D.quotientEquiv_symm y.proj hy,
      LinearEquiv.symm_apply_apply]
  change (⟨y.proj, L y.proj _⟩ : TotalSpace (Euclidean s) F) = ⟨y.proj, L y.proj y.snd⟩
  rw [hreps]

end QuotientCoordinateCover

/-- Gluing the induced cocycle and transporting along its coordinate-preserving
fiber equivalences constructs the smooth bundle on the actual quotients. -/
theorem exists_smoothQuotient (hK : SmoothSubbundle B K k) :
    Nonempty (SmoothQuotient.{u,v,w,z,t} B K k) := by
  classical
  let C := quotientCoordinateCover B K k hK
  let G := C.glued
  letI : ∀ p, AddCommGroup (G.Fiber p) := G.addCommGroup
  letI : ∀ p, Module ℝ (G.Fiber p) := G.module
  letI : TopologicalSpace (TotalSpace (Euclidean (r-k)) G.Fiber) := G.topology
  let e := C.realizationEquiv G
  letI := Transport.topology (r := r-k) e
  let Q := Transport.bundle G.bundle e
  have hbase : ∀ i, Q.baseSet i = (C.localCoordinates i).domain :=
    fun i => G.realizes.1 i
  have hcoord : ∀ i p (hp : p ∈ Q.baseSet i), Q.fiberCoordinates i p hp =
      (C.localCoordinates i).quotientEquiv p ((hbase i) ▸ hp) := by
    intro i p hp
    apply LinearEquiv.ext
    intro v
    change ((G.bundle.trivialization i) ⟨p, e p v⟩).2 = _
    exact C.realizationEquiv_coordinates G i p ((hbase i) ▸ hp) v
  refine ⟨{ topology := Transport.topology (r := r-k) e
            bundle := Q
            projection_smooth := C.projection_smooth_of_coordinates Q hbase hcoord
            descent_smooth := ?_ }⟩
  intro s κ F _ _ _ D L hL
  exact C.descent_smooth_of_coordinates Q hbase hcoord D L hL

/-- Once the quotient smooth structure is constructed, the full smooth
factorization follows from its descent test and algebraic uniqueness. -/
theorem factorization_of_smoothQuotient {s : ℕ} {κ : Type t} {F : M → Type z}
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean s) F)]
    (D : SmoothVectorBundle S s κ F) (Q : SmoothQuotient.{u,v,w,z,t} B K k)
    (A : (p : M) → E p →ₗ[ℝ] F p)
    (hA : IsSmoothMap B.totalManifold D.totalManifold (fun q => ⟨q.proj, A q.proj q.snd⟩))
    (hAK : VanishesOn K A) :
    letI := Q.topology
    ∃! L : (p : M) → QuotientFiber K p →ₗ[ℝ] F p,
      IsSmoothMap Q.bundle.totalManifold D.totalManifold
        (fun q => ⟨q.proj, L q.proj q.snd⟩) ∧
      ∀ p, (L p).comp (quotientProjection K p) = A p := by
  letI := Q.topology
  refine ⟨quotientLift K A hAK, ⟨?_, quotientLift_comp K A hAK⟩, ?_⟩
  · apply Q.descent_smooth D
    simpa only [quotientLift_projection] using hA
  · intro L hL
    exact quotientLift_unique K A hAK L hL.2

end Bundle

/-- Full universal property with quantifiers ordered as in the independent Spec. -/
theorem smoothQuotient_factorization :
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    [TopologicalSpace (TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F)
    (K : (p : M) → Submodule ℝ (E p)) (k : ℕ)
    (Q : SmoothQuotient.{u,v,w,z,t} B K k) (A : (p : M) → E p →ₗ[ℝ] F p),
    IsSmoothMap B.totalManifold D.totalManifold (fun q => ⟨q.proj, A q.proj q.snd⟩) →
    VanishesOn K A →
    letI := Q.topology
    ∃! L : (p : M) → QuotientFiber K p →ₗ[ℝ] F p,
      @IsSmoothMap (n + (r - k)) (n + s)
        (productKind n a (r - k) .euclidean) (productKind n a s .euclidean)
        (TotalSpace (Euclidean (r - k)) (QuotientFiber K)) (TotalSpace (Euclidean s) F)
        Q.topology _ Q.bundle.totalManifold D.totalManifold
        (fun q => ⟨q.proj, L q.proj q.snd⟩) ∧
      ∀ p, (L p).comp (quotientProjection K p) = A p := by
  intro n r s a M _ S ι κ E F _ _ _ _ _ _ B D K k Q A hA hAK
  exact factorization_of_smoothQuotient B K k D Q A hA hAK

/-- Components of this base are open by the accepted manifold topology
result; openness in ComponentwiseBundle is therefore no extra restriction. -/
theorem isOpen_componentSet {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (c : ConnectedComponents M) :
    IsOpen (componentSet c) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  change IsOpen ((ConnectedComponents.mk : M → ConnectedComponents M) ⁻¹' {ConnectedComponents.mk p})
  rw [connectedComponents_preimage_singleton]
  exact TopologicalManifold.isOpen_connectedComponent S.topologicalManifold p

/-- The component base structures used above are supplied by restriction of S. -/
theorem exists_componentBase {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (c : ConnectedComponents M) :
    ∃ R : SmoothManifold n a (componentSet c),
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val (componentSet c) (isOpen_componentSet S c)) ∧
      IsSmoothMap R S Subtype.val := by
  obtain ⟨R, _, hR, hi⟩ := exists_openSubset_smoothManifold S
    (componentSet c) (isOpen_componentSet S c)
  exact ⟨R, hR, hi⟩

/-- Separate application on open connected components allows arbitrary ranks
on different components, retaining the original fibers at every point. -/
theorem exists_componentwise_smoothQuotient :
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (B : ComponentwiseBundle.{u,v,w} S E)
    (K : (p : M) → Submodule ℝ (E p)) (k : ConnectedComponents M → ℕ),
    (∀ c, @SmoothSubbundle n (B.rank c) a (componentSet c) _ (B.base c) (B.index c)
      (fun p : componentSet c => E p.val) (fun _ => inferInstance)
      (fun _ => inferInstance) (B.topology c) (B.bundle c) (fun p => K p.val) (k c)) →
    Nonempty (∀ c, @SmoothQuotient.{u,v,w,z,t} n (B.rank c) a (componentSet c) _ (B.base c)
      (B.index c) (fun p : componentSet c => E p.val) (fun _ => inferInstance)
      (fun _ => inferInstance) (B.topology c) (B.bundle c) (fun p => K p.val) (k c)) := by
  intro n a M _ S E _ _ B K k hK
  classical
  refine ⟨fun c => ?_⟩
  letI := B.topology c
  exact Classical.choice (exists_smoothQuotient (B.bundle c)
    (fun p => K p.val) (k c) (hK c))

end SmoothManifolds.QuotientBundles
