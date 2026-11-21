import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Covectors
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Frames
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Bundle
import Batteries.Tactic.OpenPrivate

/-! Differentials and pullbacks of smooth one-forms (paper.tex M05.06).

The coordinate calculations use the shared intrinsic tangent fibers and the dual
bundle trivializations. All statements allow ordinary boundary and dimension zero.
-/
set_option autoImplicit false
set_option linter.unusedVariables false

namespace SmoothManifolds.Covectors
open ModelData AtlasData MapData PartitionData TangentData TangentBundleData
  DifferentialData BundleData BundleOperationsData FrameData CovectorData Set Filter
open scoped Topology
universe u

open private scalar_comp_at differential_unique from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

section Base
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem coordinateCovector_apply (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (j k : Fin n) :
    coordinateCovector K c hc p hp j (coordinateVector K c hc p hp k) =
      if k = j then 1 else 0 := by
  classical
  simp [coordinateCovector, coordinateVector, Pi.single_apply, eq_comm]

theorem coordinateCovector_germ (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (j : Fin n) (g : SmoothGerm S p)
    (hg : g.val = Germ.ofFun (fun y => (c y).val j)) :
    germDifferential S p g = coordinateCovector K c hc p hp j := by
  obtain ⟨xs, hxs, hx⟩ := K.isCoordinates c hc p hp
  apply LinearMap.ext
  intro v
  change v.val g = K.equiv c hc p hp v j
  rw [hx]
  exact congrArg v.val (Subtype.ext (hg.trans (hxs j).symm))

/-- Expansion in the coordinate frame and its algebraic dual. -/
theorem covector_expansion (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (α : CotangentFiber S p) :
    α = ∑ j : Fin n, α (coordinateVector K c hc p hp j) •
      coordinateCovector K c hc p hp j := by
  classical
  apply LinearMap.ext
  intro v
  have hvec : v = ∑ j : Fin n, (K.equiv c hc p hp v j) • coordinateVector K c hc p hp j := by
    apply (K.equiv c hc p hp).injective
    simp only [map_sum, map_smul, coordinateVector, LinearEquiv.apply_symm_apply]
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hvec, map_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    coordinateCovector, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The prescribed dual trivialization evaluates on the intrinsic coordinate
vectors. This bridges the two upstream representations of tangent bundles. -/
theorem cotangent_coordinates (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (α : CotangentFiber S p) (j : Fin n) :
    letI := (cotangentSpace C).topology
    (((cotangentSpace C).bundle.trivialization ⟨c, hc⟩) ⟨p, α⟩).2 j =
      α (coordinateVector C.tangent.fiberCoordinates c hc p hp j) := by
  letI := C.realization.space.topology
  letI := (cotangentSpace C).topology
  have hb : p ∈ C.realization.space.bundle.baseSet ⟨c, hc⟩ := by
    rw [C.realization.baseSet]
    exact hp
  have hE : C.realization.space.bundle.fiberCoordinates ⟨c, hc⟩ p hb =
      C.tangent.fiberCoordinates.equiv c hc p hp := by
    apply LinearEquiv.ext
    intro v
    exact C.realization.coordinates ⟨c, hc⟩ p hp v
  change ((C.dual.space.bundle.trivialization ⟨c, hc⟩) ⟨p, α⟩).2 j = _
  rw [C.dual.coordinates ⟨c, hc⟩ p (by rw [C.realization.baseSet]; exact hp)]
  apply congrArg α
  change (C.realization.space.bundle.fiberCoordinates ⟨c, hc⟩ p hb).symm
    (Pi.single j 1) = _
  rw [hE]
  rfl

theorem cotangent_baseSet (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    letI := (cotangentSpace C).topology
    (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ = c.source := by
  letI := C.realization.space.topology
  exact (C.dual.baseSet ⟨c, hc⟩).trans (C.realization.baseSet ⟨c, hc⟩)

theorem coordinate_dual_frame :
    Specs.SmoothManifolds.Ch05.Covectors.coordinate_dual_frameType.{u} := by
  intro n a M _ S C c hc
  classical
  letI := (cotangentSpace C).topology
  let B := (cotangentSpace C).bundle
  let s (j : Fin n) (p : c.source) :=
    coordinateCovector C.tangent.fiberCoordinates c hc p.val p.property j
  have hb (p : c.source) : p.val ∈ B.baseSet ⟨c, hc⟩ := by
    rw [cotangent_baseSet]
    exact p.property
  have hcoord (p : c.source) (j : Fin n) :
      B.fiberCoordinates ⟨c, hc⟩ p.val (hb p) (s j p) = Pi.single j 1 := by
    ext k
    rw [BundleData.SmoothVectorBundle.fiberCoordinates_apply,
      cotangent_coordinates C c hc p.val p.property (s j p) k]
    change coordinateCovector _ _ _ _ _ j (coordinateVector _ _ _ _ _ k) = _
    simp [coordinateCovector_apply, Pi.single_apply]
  let b (p : c.source) : Module.Basis (Fin n) ℝ (CotangentFiber S p.val) :=
    (Pi.basisFun ℝ (Fin n)).map (B.fiberCoordinates ⟨c, hc⟩ p.val (hb p)).symm
  have hbs (p : c.source) (j : Fin n) : b p j = s j p := by
    apply (B.fiberCoordinates ⟨c, hc⟩ p.val (hb p)).injective
    simp only [b, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
      Pi.basisFun_apply, hcoord]
  refine ⟨{ section_ := s, basis := b, basis_eq := hbs, smooth := ?_ },
    fun _ _ => rfl, ?_, ?_⟩
  · intro j p
    apply Frames.smoothAt_of_sectionCoordinates B c.source c.open_source ⟨c, hc⟩
      (s j) p (hb p)
    have heq : Frames.sectionCoordinates B c.source ⟨c, hc⟩ (s j) =
        fun _ => Pi.single j (1 : ℝ) := by
      funext y
      exact hcoord y j
    rw [heq]
    exact VectorSmoothAt.const _ _ _
  · exact fun p hp j k => coordinateCovector_apply _ c hc p hp j k
  · exact fun p hp j g hg => coordinateCovector_germ _ c hc p hp j g hg

theorem differential_coordinates :
    Specs.SmoothManifolds.Ch05.Covectors.differential_coordinatesType.{u} := by
  intro n a M _ S C u hu c hc p hp F hF
  let K := C.tangent.fiberCoordinates
  obtain ⟨xs, hxs, hx⟩ := K.isCoordinates c hc p hp
  have hcoords (v : TangentSpace S p) (i : Fin n) :
      v.val (coordinateGerm S p c hc hp i) = K.equiv c hc p hp v i := by
    rw [hx]
    exact congrArg v.val (Subtype.ext (hxs i).symm)
  have hval (j : Fin n) : dFunction S u hu p (coordinateVector K c hc p hp j) =
      fderiv ℝ F (c p).val (Pi.single j 1) := by
    change (coordinateVector K c hc p hp j).val (functionGerm S u hu p) = _
    rw [derivation_coordinate_formula S p c hc hp _ _ F hF]
    simp only [hcoords, coordinateVector, LinearEquiv.apply_symm_apply]
    simp [Pi.single_apply]
  refine ⟨hval, ?_⟩
  rw [covector_expansion K c hc p hp (dFunction S u hu p)]
  simp only [hval]
  rfl

theorem differential_smooth :
    Specs.SmoothManifolds.Ch05.Covectors.differential_smoothType.{u} := by
  intro n a M _ S C u hu
  classical
  letI := (cotangentSpace C).topology
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨W, hW, hpW, F, hF, heF⟩ :=
    ((scalarContDiffAt_iff _ _ _ _).mp (hu p)).2 c hc hp
  let G : Euclidean n → Euclidean n := fun z j => fderiv ℝ F z (Pi.single j 1)
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G W := by
    apply contDiffOn_pi.mpr
    intro j
    exact (hF.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have hcoeff : VectorSmoothAt S.smoothStructure.val (fun y => G (c y).val) p :=
    TangentBundle.euclidean_smoothAt_of_chart S _ p c hc hp
      ⟨W, hW, hpW, G, hG, Filter.EventuallyEq.rfl⟩
  apply Frames.smoothAt_from_trivialization (cotangentSpace C).bundle
    S.smoothStructure.property.1 ⟨c, hc⟩
    (by rw [cotangent_baseSet]; exact hp)
    ((manifoldContDiff_id _ _ S.smoothStructure.property.1) p) hcoeff (fun _ => rfl)
  have hcont : ContinuousAt (fun y => (c y).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  filter_upwards [c.open_source.mem_nhds hp,
    hcont.preimage_mem_nhds (hW.mem_nhds hpW), heF.eventuallyEq_nhds] with y hyc hyW heFy
  ext j
  rw [cotangent_coordinates C c hc y hyc]
  exact (differential_coordinates S C u hu c hc y hyc F
    ⟨⟨W, hW, hyW, hF⟩, Germ.coe_eq.mpr heFy⟩).1 j

/-- Smoothness of the natural pairing, checked in a single dual coordinate
frame. Only smoothness at the point in question is needed. -/
theorem evaluation_smoothAt {k : ℕ} {b : ModelKind} {Q : Type u}
    [TopologicalSpace Q] (R : SmoothManifold k b Q) (C : CotangentBundle S)
    (h : Q → M) (α : (x : Q) → CotangentFiber S (h x))
    (v : (x : Q) → TangentSpace S (h x)) (x : Q)
    (hh : IsSmoothMap R S h) :
    letI := (cotangentSpace C).topology
    letI := C.tangent.topology
    ManifoldSmoothAt R.smoothStructure.val (cotangentSpace C).bundle.totalManifold.smoothStructure.val
      (fun y => (⟨h y, α y⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S))) x →
    ManifoldSmoothAt R.smoothStructure.val C.tangent.manifold.smoothStructure.val
      (fun y => (⟨h y, v y⟩ : TangentBundleData.TotalSpace S)) x →
    VectorSmoothAt R.smoothStructure.val (fun y => α y (v y)) x := by
  letI := (cotangentSpace C).topology
  letI := C.tangent.topology
  intro hα hv
  classical
  obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 (h x)
  let ac : Q → Euclidean n := fun y =>
    (((cotangentSpace C).bundle.trivialization ⟨c, hc⟩) ⟨h y, α y⟩).2
  let vc : Q → Euclidean n := fun y =>
    TangentBundle.chartFiber C.tangent c hc ⟨h y, v y⟩
  have ha : VectorSmoothAt R.smoothStructure.val ac x :=
    (Frames.trivializationCoordinates_smoothAt (cotangentSpace C).bundle ⟨c, hc⟩
      ⟨h x, α x⟩ (by rw [cotangent_baseSet]; exact hxc)).comp
      (g := fun y : Q => (⟨h y, α y⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S)))
      (cotangentSpace C).bundle.totalManifold.smoothStructure.property.1.1 hα
  have hv' : VectorSmoothAt R.smoothStructure.val vc x :=
    TangentBundle.chartFiber_smoothAt S C.tangent R _ x c hc hxc hv
  have hsum : VectorSmoothAt R.smoothStructure.val (fun y => ∑ j, ac y j * vc y j) x := by
    apply VectorSmoothAt.sum
    intro j
    exact ((ha.postcomp (contDiff_apply ℝ (fun _ : Fin n => ℝ) j)).prod
      (hv'.postcomp (contDiff_apply ℝ (fun _ : Fin n => ℝ) j))).postcomp
      (contDiff_fst.mul contDiff_snd)
  apply hsum.congr
  filter_upwards [(hh x).1.preimage_mem_nhds (c.open_source.mem_nhds hxc)] with y hy
  have hαexpand := congrArg (fun lam : CotangentFiber S (h y) => lam (v y))
    (covector_expansion C.tangent.fiberCoordinates c hc (h y) hy (α y))
  rw [hαexpand]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show ac y j = α y (coordinateVector C.tangent.fiberCoordinates c hc (h y) hy j)
    from cotangent_coordinates C c hc (h y) hy (α y) j]
  rw [show vc y = C.tangent.fiberCoordinates.equiv c hc (h y) hy (v y)
    from TangentBundle.chartFiber_eq S C.tangent c hc ⟨h y, v y⟩ hy]
  rfl

theorem pullback_smooth :
    Specs.SmoothManifolds.Ch05.Covectors.pullback_smoothType.{u} := by
  intro n m a b M P _ _ S T C D f hf L hL α hα
  classical
  letI := (cotangentSpace C).topology
  letI := (cotangentSpace D).topology
  letI := C.tangent.topology
  letI := D.tangent.topology
  have hαf : IsSmoothMap T (cotangentSpace C).bundle.totalManifold
      (fun y => (⟨f y, α (f y)⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S))) :=
    manifoldContDiff_comp _ _ _ _ S.smoothStructure.property.1.1 f _ hf hα
  have hdf := TangentBundle.map_smooth T S D.tangent C.tangent f hf L hL
  intro p
  obtain ⟨e, he, hp⟩ := T.smoothStructure.property.1.1 p
  let v (j : Fin m) (y : P) : TangentSpace T y :=
    if hy : y ∈ e.source then coordinateVector D.tangent.fiberCoordinates e he y hy j else 0
  have hv (j : Fin m) : ManifoldSmoothAt T.smoothStructure.val D.tangent.manifold.smoothStructure.val
      (fun y => (⟨y, v j y⟩ : TangentBundleData.TotalSpace T)) p := by
    apply TangentBundle.lift_smoothAt_of_coeff T D.tangent T _ p e he hp
      (fun _ => Pi.single j 1)
      ((manifoldContDiff_id _ _ T.smoothStructure.property.1) p)
      (VectorSmoothAt.const _ _ _)
    filter_upwards [e.open_source.mem_nhds hp] with y hy
    refine ⟨hy, ?_⟩
    simp [v, hy, coordinateVector]
  have hvalues (j : Fin m) : VectorSmoothAt T.smoothStructure.val
      (fun y => α (f y) (L y (v j y))) p := by
    apply evaluation_smoothAt T C f (fun y => α (f y)) (fun y => L y (v j y)) p hf (hαf p)
    exact manifoldContDiffAt_comp D.tangent.manifold.smoothStructure.property.1.1
      (hv j) (hdf ⟨p, v j p⟩)
  have hcoeff := VectorSmoothAt.pi hvalues
  apply Frames.smoothAt_from_trivialization (cotangentSpace D).bundle
    T.smoothStructure.property.1 ⟨e, he⟩ (by rw [cotangent_baseSet]; exact hp)
    ((manifoldContDiff_id _ _ T.smoothStructure.property.1) p) hcoeff (fun _ => rfl)
  filter_upwards [e.open_source.mem_nhds hp] with y hy
  ext j
  rw [cotangent_coordinates D e he y hy]
  simp [pullbackField, v, hy]

theorem pullback_exists :
    Specs.SmoothManifolds.Ch05.Covectors.pullback_existsType.{u} := by
  intro n m a b M P _ _ S T C D f hf α
  classical
  choose L hL hunique using differential_exists T S f hf
  exact ⟨L, hL, pullback_smooth S T C D f hf L hL α.field α.smooth⟩

theorem pullback_apply :
    Specs.SmoothManifolds.Ch05.Covectors.pullback_applyType.{u} := by
  intro n m a b M P _ _ S T f L α p v
  rfl

theorem pullback_differential :
    Specs.SmoothManifolds.Ch05.Covectors.pullback_differentialType.{u} := by
  intro n m a b M P _ _ S T f hf L hL u hu
  have huf : ScalarSmooth T.smoothStructure.val (u ∘ f) :=
    fun p => scalar_comp_at (hf p) (hu (f p))
  refine ⟨huf, ?_⟩
  funext p
  apply LinearMap.ext
  intro v
  exact (hL p v (functionGerm S u hu (f p)) (functionGerm T (u ∘ f) huf p)
    u rfl rfl).symm

theorem pullback_id :
    Specs.SmoothManifolds.Ch05.Covectors.pullback_idType.{u} := by
  intro n a M _ S L hL α
  have hid : IsSmoothMap S S id := manifoldContDiff_id _ _ S.smoothStructure.property.1
  funext p
  have h := differential_unique (@mem_smoothGermAlgebra_iff.{u}) S S id hid p
    (L p) LinearMap.id (hL p) (differential_id S p)
  change (α p).comp (L p) = α p
  rw [h]
  rfl

theorem pullback_comp :
    Specs.SmoothManifolds.Ch05.Covectors.pullback_compType.{u} := by
  intro n m k a b c M P Q _ _ _ S T U f g hf hg L K H hL hK hH α
  have hfg : IsSmoothMap U S (f ∘ g) :=
    manifoldContDiff_comp _ _ _ _ T.smoothStructure.property.1.1 g f hg hf
  funext q
  have h := differential_unique (@mem_smoothGermAlgebra_iff.{u}) U S (f ∘ g) hfg q
    (H q) ((L (g q)).comp (K q)) (hH q)
    (differential_comp U T S g f hg hf q (K q) (L (g q)) (hK q) (hL (g q)))
  change (α (f (g q))).comp (H q) = ((α (f (g q))).comp (L (g q))).comp (K q)
  rw [h]
  rfl

theorem restriction :
    Specs.SmoothManifolds.Ch05.Covectors.restrictionType.{u} := by
  intro n m a b M P _ _ S T C D i hi L hL α hα
  exact ⟨pullback_smooth S T C D i hi.1 L hL α hα, fun _ => rfl⟩

theorem zero_dimension :
    Specs.SmoothManifolds.Ch05.Covectors.zero_dimensionType.{u} := by
  intro a M _ S α p
  letI := tangent_zero S p
  apply LinearMap.ext
  intro v
  have hv : v = 0 := Subsingleton.elim _ _
  simp [hv]

end Base

end SmoothManifolds.Covectors
