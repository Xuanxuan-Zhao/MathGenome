import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Covectors
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleOperations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorAlgebra

/-! Pullback of differential forms and the canonical tautological one-form.
All statements use the original intrinsic tangent and cotangent fibers. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
noncomputable section

namespace SmoothManifolds.FormPullbackResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  BundleData BundleOperationsData FrameData CovectorData ExteriorData FormPullbackData
  Set Filter Module
open scoped Topology
universe u

/-- Naturality of the determinant-normalized exterior pairing. -/
theorem pairing_natural {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (L : V →ₗ[ℝ] W) :
    (exteriorPower.pairingDual ℝ V k).comp (fiberPullback k L) =
      (exteriorPower.map k L).dualMap.comp (exteriorPower.pairingDual ℝ W k) := by
  apply exteriorPower.linearMap_ext (R := ℝ) (M := Module.Dual ℝ W) (n := k)
  apply AlternatingMap.ext
  intro α
  apply exteriorPower.linearMap_ext (R := ℝ) (M := V) (n := k)
  apply AlternatingMap.ext
  intro v
  change exteriorPower.pairingDual ℝ V k
      (exteriorPower.map k L.dualMap (exteriorPower.ιMulti ℝ k α)) (exteriorPower.ιMulti ℝ k v) =
    exteriorPower.pairingDual ℝ W k (exteriorPower.ιMulti ℝ k α)
      (exteriorPower.map k L (exteriorPower.ιMulti ℝ k v))
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  rfl

/-- Evaluation is the homogeneous exterior pairing on the wedge of arguments. -/
theorem evaluate_eq_pairing {V : Type u} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (ω : Fiber V k) (v : Fin k → V) :
    evaluate V k ω v = exteriorPower.pairingDual ℝ V k ω (exteriorPower.ιMulti ℝ k v) := by
  change exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPower.pairingDual ℝ V k ω) v = _
  exact exteriorPower.alternatingMapLinearEquiv_symm_apply _ _

/-- Evaluation of pullback holds without finite dimensionality or smoothness. -/
theorem evaluate_fiberPullback {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (L : V →ₗ[ℝ] W)
    (ω : Fiber W k) (v : Fin k → V) :
    evaluate V k (fiberPullback k L ω) v = evaluate W k ω (fun i => L (v i)) := by
  rw [evaluate_eq_pairing, evaluate_eq_pairing]
  change ((exteriorPower.pairingDual ℝ V k).comp (fiberPullback k L)) ω
    (exteriorPower.ιMulti ℝ k v) = _
  rw [pairing_natural]
  change exteriorPower.pairingDual ℝ W k ω
    (exteriorPower.map k L (exteriorPower.ιMulti ℝ k v)) = _
  rw [exteriorPower.map_apply_ιMulti]
  rfl

/-- In degree zero, every linear map induces the identity on scalars. -/
theorem fiberPullback_zero {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (r : ℝ) :
    fiberPullback 0 L ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ W)).symm r) =
      (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)).symm r := by
  apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)).injective
  have h := congrArg (fun F : Fiber W 0 →ₗ[ℝ] ℝ =>
      F ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ W)).symm r))
    (exteriorPower.zeroEquiv_naturality L.dualMap)
  simpa only [fiberPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using h

/-- Exterior-power functoriality in degree zero is composition of functions. -/
theorem pullback_zero_proof : Specs.SmoothManifolds.Ch07.FormPullback.pullback_zeroType.{u} := by
  intro n m a b M N _ _ S T f L g
  funext p
  apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
  change ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).toLinearMap.comp
    (exteriorPower.map 0 (L p).dualMap)) (scalarField T g (f p)) =
      (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))) (scalarField S (g ∘ f) p)
  rw [exteriorPower.zeroEquiv_naturality]
  change (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace T (f p))))
      ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace T (f p)))).symm (g (f p))) =
    (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p)))
      ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm (g (f p)))
  exact ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace T (f p)))).apply_symm_apply _).trans
    ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).apply_symm_apply _).symm

/-- Pullback of the identity, for every genuine representative of its differential. -/
theorem pullback_id_proof : Specs.SmoothManifolds.Ch07.FormPullback.pullback_idType.{u} := by
  intro n a M _ S L hL k ω
  have hid : IsSmoothMap S S id := manifoldContDiff_id _ _ S.smoothStructure.property.1
  funext p
  have he : L p = LinearMap.id :=
    (differential_exists S S id hid p).unique (hL p) (differential_id S p)
  simp only [FormPullbackData.pullbackField, fiberPullback, id_eq, he,
    LinearMap.dualMap_id, exteriorPower.map_id, LinearMap.id_apply]

/-- The chain rule and exterior-power functoriality give contravariance. -/
theorem pullback_comp_proof : Specs.SmoothManifolds.Ch07.FormPullback.pullback_compType.{u} := by
  intro n m r a b c M N P _ _ _ S T U f g hf hg L K H hL hK hH k ω
  have hgf : IsSmoothMap S U (g ∘ f) :=
    manifoldContDiff_comp _ _ _ _ T.smoothStructure.property.1.1 f g hf hg
  funext p
  have he : H p = (K (f p)).comp (L p) :=
    (differential_exists S U (g ∘ f) hgf p).unique (hH p)
    (differential_comp S T U f g hf hg p (L p) (K (f p)) (hL p) (hK (f p)))
  simp only [FormPullbackData.pullbackField, fiberPullback, Function.comp_apply, he,
    ← LinearMap.dualMap_comp_dualMap, exteriorPower.map_comp, LinearMap.comp_apply]

/-- Exterior algebra maps preserve multiplication in every pair of degrees. -/
theorem fiberPullback_wedge {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (k l : ℕ)
    (α : Fiber W k) (β : Fiber W l) :
    fiberPullback (k+l) L (wedge α β) = wedge (fiberPullback k L α) (fiberPullback l L β) := by
  apply Subtype.ext
  simp only [fiberPullback, exteriorPower.coe_map, wedge,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, map_mul]

/-- The induced p_i are the coefficients of the original covector. -/
theorem tautological_coordinates_proof :
    Specs.SmoothManifolds.Ch07.FormPullback.tautological_coordinatesType.{u} := by
  intro n a M _ S C
  letI := (cotangentSpace C).topology
  dsimp only
  intro L hL c hc ξ hξ
  change ξ.snd.comp (L ξ) = _
  rw [Covectors.covector_expansion C.tangent.fiberCoordinates c hc ξ.proj hξ ξ.snd]
  ext v
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Covectors.cotangent_coordinates C c hc ξ.proj hξ ξ.snd]

/-- Smoothness of θ is the smooth pairing of the universal covector with dπ. -/
theorem tautological_smooth_proof :
    Specs.SmoothManifolds.Ch07.FormPullback.tautological_smoothType.{u} := by
  classical
  intro n a M _ S C
  letI := (cotangentSpace C).topology
  let Q := (cotangentSpace C).bundle.totalManifold
  dsimp only
  intro L hL A
  letI := (cotangentSpace A).topology
  letI := C.tangent.topology
  letI := A.tangent.topology
  have hπ : IsSmoothMap Q S Bundle.TotalSpace.proj :=
    (cotangentSpace C).bundle.projection_smooth
  have hdf := TangentBundle.map_smooth Q S A.tangent C.tangent
    Bundle.TotalSpace.proj hπ L hL
  intro ξ
  obtain ⟨e, he, hξ⟩ := Q.smoothStructure.property.1.1 ξ
  let v (j : Fin (n+n)) (η : CotangentTotal S) : TangentSpace Q η :=
    if hη : η ∈ e.source then coordinateVector A.tangent.fiberCoordinates e he η hη j else 0
  have hv (j : Fin (n+n)) :
      ManifoldSmoothAt Q.smoothStructure.val A.tangent.manifold.smoothStructure.val
        (fun η => (⟨η, v j η⟩ : TangentBundleData.TotalSpace Q)) ξ := by
    apply TangentBundle.lift_smoothAt_of_coeff Q A.tangent Q _ ξ e he hξ
      (fun _ => Pi.single j 1)
      ((manifoldContDiff_id _ _ Q.smoothStructure.property.1) ξ)
      (VectorSmoothAt.const _ _ _)
    filter_upwards [e.open_source.mem_nhds hξ] with η hη
    refine ⟨hη, ?_⟩
    simp [v, hη, coordinateVector]
  have hvalues (j : Fin (n+n)) : VectorSmoothAt Q.smoothStructure.val
      (fun η => η.snd (L η (v j η))) ξ := by
    apply Covectors.evaluation_smoothAt Q C Bundle.TotalSpace.proj
      (fun η => η.snd) (fun η => L η (v j η)) ξ hπ
      ((manifoldContDiff_id _ _ Q.smoothStructure.property.1) ξ)
    exact manifoldContDiffAt_comp A.tangent.manifold.smoothStructure.property.1.1
      (hv j) (hdf ⟨ξ, v j ξ⟩)
  have hcoeff := VectorSmoothAt.pi hvalues
  apply Frames.smoothAt_from_trivialization (cotangentSpace A).bundle
    Q.smoothStructure.property.1 ⟨e, he⟩ (by rw [Covectors.cotangent_baseSet]; exact hξ)
    ((manifoldContDiff_id _ _ Q.smoothStructure.property.1) ξ) hcoeff (fun _ => rfl)
  filter_upwards [e.open_source.mem_nhds hξ] with η hη
  ext j
  rw [Covectors.cotangent_coordinates A e he η hη]
  simp [tautologicalField, v, hη]

/-- The projection is smooth, so its intrinsic differential exists everywhere. -/
theorem tautological_exists_proof :
    Specs.SmoothManifolds.Ch07.FormPullback.tautological_existsType.{u} := by
  intro n a M _ S C
  letI := (cotangentSpace C).topology
  let Q := (cotangentSpace C).bundle.totalManifold
  have hπ : IsSmoothMap Q S Bundle.TotalSpace.proj :=
    (cotangentSpace C).bundle.projection_smooth
  let L := differential Q S Bundle.TotalSpace.proj hπ
  have hL := differential_spec Q S Bundle.TotalSpace.proj hπ
  dsimp only
  exact ⟨L, hL, tautological_smooth_proof C L hL⟩

/-- The signed determinant formula for any top alternating map, including n = 0. -/
theorem signed_jacobian_proof : Specs.SmoothManifolds.Ch07.FormPullback.signed_jacobianType.{u} := by
  intro n a b M N _ _ S T C D f hf L hL c hc d hd p hp hq W H hW hpW hH heH ω
  let E := C.tangent.fiberCoordinates.equiv c hc p hp
  let F := D.tangent.fiberCoordinates.equiv d hd (f p) hq
  let basis : Basis (Fin n) ℝ (TangentSpace T (f p)) := (Pi.basisFun ℝ (Fin n)).map F.symm
  have hb (j : Fin n) : basis j = coordinateVector D.tangent.fiberCoordinates d hd (f p) hq j := by
    simp [basis, coordinateVector, F, Pi.basisFun_apply]
  have hj (j : Fin n) : F (L p (coordinateVector C.tangent.fiberCoordinates c hc p hp j)) =
      fderiv ℝ H (c p).val (Pi.single j 1) := by
    rw [differential_jacobian S T f hf p (L p) (hL p) c d hc hd hp hq E F
      (C.tangent.fiberCoordinates.isCoordinates c hc p hp)
      (D.tangent.fiberCoordinates.isCoordinates d hd (f p) hq)
      W H hW hpW hH heH]
    simp [E, coordinateVector]
  have hdet : basis.det (fun j => L p (coordinateVector C.tangent.fiberCoordinates c hc p hp j)) =
      (Matrix.of (fun i j => fderiv ℝ H (c p).val (Pi.single j 1) i)).det := by
    rw [Basis.det_apply]
    congr 1
    ext i j
    change (basis.repr (L p (coordinateVector C.tangent.fiberCoordinates c hc p hp j))) i = _
    simpa [basis, Basis.map_repr, F] using congrFun (hj j) i
  change evaluate (TangentSpace S p) n
    (fiberPullback (V := TangentSpace S p) (W := TangentSpace T (f p)) n (L p) (ω (f p)))
    (coordinateVector C.tangent.fiberCoordinates c hc p hp) = _
  rw [evaluate_fiberPullback]
  have hexp := AlternatingMap.eq_smul_basis_det (R := ℝ) (M := TangentSpace T (f p))
    basis (evaluate (TangentSpace T (f p)) n (ω (f p)))
  have h := congrArg
    (fun A : AlternatingMap ℝ (TangentSpace T (f p)) ℝ (Fin n) =>
      A (fun j => L p (coordinateVector C.tangent.fiberCoordinates c hc p hp j)))
    hexp
  simpa only [smul_apply, smul_eq_mul, hdet, topCoefficient, ← funext hb] using h

/-- Coordinates of the induced exterior trivialization on every element. -/
theorem form_coordinates {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (A : FormBundle C k)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (ω : Fiber (TangentSpace S p) k) :
    letI := (cotangentSpace C).topology
    letI := A.space.topology
    ((A.space.bundle.trivialization ⟨c, hc⟩) ⟨p, ω⟩).2 =
      A.modelEquiv (exteriorPower.map k
        ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ p
          (by rw [Covectors.cotangent_baseSet]; exact hp)).toLinearMap ω) := by
  letI := (cotangentSpace C).topology
  letI := A.space.topology
  have hpC : p ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hp
  have hpA : p ∈ A.space.bundle.baseSet ⟨c, hc⟩ := by rw [A.baseSet]; exact hpC
  have h : (A.space.bundle.fiberCoordinates ⟨c, hc⟩ p hpA).toLinearMap =
      A.modelEquiv.toLinearMap.comp (exteriorPower.map k
        ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ p hpC).toLinearMap) := by
    apply exteriorPower.linearMap_ext (R := ℝ) (M := CotangentFiber S p) (n := k)
    apply AlternatingMap.ext
    intro v
    simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, exteriorPower.map_apply_ιMulti,
      BundleData.SmoothVectorBundle.fiberCoordinates_apply, Function.comp_def] using
      A.coordinates ⟨c, hc⟩ p hpC v
  exact congrArg (fun F => F ω) h

/-- Exterior powers of rectangular matrices have polynomial entries (minors).
This formulation includes empty matrices and all exterior degrees. -/
theorem exterior_image_smooth {d r s k : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] {A : Set (ModelChart d a X)}
    (I : (⋀[ℝ]^k (Euclidean r)) ≃ₗ[ℝ] Euclidean (r.choose k))
    (O : (⋀[ℝ]^k (Euclidean s)) ≃ₗ[ℝ] Euclidean (s.choose k))
    {J : X → Euclidean r →L[ℝ] Euclidean s} {z : X → Euclidean (r.choose k)} {p : X}
    (hJ : VectorSmoothAt A J p) (hz : VectorSmoothAt A z p) :
    VectorSmoothAt A
      (fun x => O (exteriorPower.map k (J x).toLinearMap (I.symm (z x)))) p := by
  classical
  let b := (Pi.basisFun ℝ (Fin r)).exteriorPower k
  have hexp (x : X) : O (exteriorPower.map k (J x).toLinearMap (I.symm (z x))) =
      ∑ t : Index r k, b.repr (I.symm (z x)) t •
        O (exteriorPower.map k (J x).toLinearMap (b t)) := by
    conv_lhs => rw [← b.sum_repr (I.symm (z x))]
    simp only [map_sum, map_smul]
  simp_rw [hexp]
  apply VectorSmoothAt.sum
  intro t
  let lam : Euclidean (r.choose k) →ₗ[ℝ] ℝ := (b.coord t).comp I.symm.toLinearMap
  have hlam : VectorSmoothAt A (fun x => b.repr (I.symm (z x)) t) p :=
    hz.postcomp lam.toContinuousLinearMap.contDiff
  have hβ : VectorSmoothAt A
      (fun x => O (exteriorPower.map k (J x).toLinearMap (b t))) p := by
    simp only [b, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.map_apply_ιMulti]
    apply BundleOperations.wedgeCoordinates_smooth O.toLinearMap
    intro j
    exact hJ.clm_apply (VectorSmoothAt.const _ _ _)
  exact (hlam.prod hβ).postcomp (contDiff_fst.smul contDiff_snd)

/-- The coordinate matrix of dF's transpose is smooth, and its exterior powers
act by minors on the smooth coefficients of ω. -/
theorem pullback_smooth_proof : Specs.SmoothManifolds.Ch07.FormPullback.pullback_smoothType.{u} := by
  intro n m a b M N _ _ S T C D f hf L hL k A B ω hω
  classical
  letI := (cotangentSpace C).topology
  letI := (cotangentSpace D).topology
  letI := A.space.topology
  letI := B.space.topology
  letI := C.tangent.topology
  letI := D.tangent.topology
  have hdf := TangentBundle.map_smooth S T C.tangent D.tangent f hf L hL
  have hωf : IsSmoothMap S B.space.bundle.totalManifold
      (fun y => (⟨f y, ω (f y)⟩ : Bundle.TotalSpace (Euclidean (m.choose k)) (fun q => Fiber (TangentSpace T q) k))) :=
    manifoldContDiff_comp _ _ _ _ T.smoothStructure.property.1.1 f _ hf hω
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  let v (i : Fin n) (y : M) : TangentSpace S y :=
    if hy : y ∈ c.source then coordinateVector C.tangent.fiberCoordinates c hc y hy i else 0
  let α (j : Fin m) (y : M) : CotangentFiber T (f y) :=
    if hy : f y ∈ d.source then coordinateCovector D.tangent.fiberCoordinates d hd (f y) hy j else 0
  have hv (i : Fin n) : ManifoldSmoothAt S.smoothStructure.val C.tangent.manifold.smoothStructure.val
      (fun y => (⟨y, v i y⟩ : TangentBundleData.TotalSpace S)) p := by
    apply TangentBundle.lift_smoothAt_of_coeff S C.tangent S _ p c hc hp
      (fun _ => Pi.single i 1)
      ((manifoldContDiff_id _ _ S.smoothStructure.property.1) p)
      (VectorSmoothAt.const _ _ _)
    filter_upwards [c.open_source.mem_nhds hp] with y hy
    refine ⟨hy, ?_⟩
    simp [v, hy, coordinateVector]
  have hα (j : Fin m) : ManifoldSmoothAt S.smoothStructure.val
      (cotangentSpace D).bundle.totalManifold.smoothStructure.val
      (fun y => (⟨f y, α j y⟩ : CotangentTotal T)) p := by
    apply Frames.smoothAt_from_trivialization (cotangentSpace D).bundle
      S.smoothStructure.property.1 ⟨d, hd⟩
      (by rw [Covectors.cotangent_baseSet]; exact hfp)
      (hf p) (VectorSmoothAt.const _ (Pi.single j 1) _) (fun _ => rfl)
    filter_upwards [(hf p).1.preimage_mem_nhds (d.open_source.mem_nhds hfp)] with y hy
    change f y ∈ d.source at hy
    ext i
    rw [Covectors.cotangent_coordinates D d hd (f y) hy]
    simp only [α, dif_pos hy, Covectors.coordinateCovector_apply, Pi.single_apply, eq_comm]
  let J : M → Euclidean m →L[ℝ] Euclidean n := fun y =>
    QuotientBundles.columnOperator (fun j i => α j y (L y (v i y)))
  have hJ : VectorSmoothAt S.smoothStructure.val J p := by
    apply BundleOperations.columnOperator_smooth
    intro j
    apply VectorSmoothAt.pi
    intro i
    apply Covectors.evaluation_smoothAt S D f (α j) (fun y => L y (v i y)) p hf (hα j)
    exact manifoldContDiffAt_comp C.tangent.manifold.smoothStructure.property.1.1
      (hv i) (hdf ⟨p, v i p⟩)
  let z : M → Euclidean (m.choose k) := fun y =>
    ((B.space.bundle.trivialization ⟨d, hd⟩) ⟨f y, ω (f y)⟩).2
  have hz : VectorSmoothAt S.smoothStructure.val z p := by
    apply (Frames.trivializationCoordinates_smoothAt B.space.bundle ⟨d, hd⟩
      ⟨f p, ω (f p)⟩ (by rw [B.baseSet, Covectors.cotangent_baseSet]; exact hfp)).comp
      (g := fun y => (⟨f y, ω (f y)⟩ : Bundle.TotalSpace (Euclidean (m.choose k))
        (fun q => Fiber (TangentSpace T q) k)))
      B.space.bundle.totalManifold.smoothStructure.property.1.1 (hωf p)
  have hout := exterior_image_smooth B.modelEquiv A.modelEquiv hJ hz
  apply Frames.smoothAt_from_trivialization A.space.bundle S.smoothStructure.property.1
    ⟨c, hc⟩ (by rw [A.baseSet, Covectors.cotangent_baseSet]; exact hp)
    ((manifoldContDiff_id _ _ S.smoothStructure.property.1) p) hout (fun _ => rfl)
  filter_upwards [c.open_source.mem_nhds hp,
    (hf p).1.preimage_mem_nhds (d.open_source.mem_nhds hfp)] with y hy hfy
  change f y ∈ d.source at hfy
  have hyC : y ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hy
  have hyD : f y ∈ (cotangentSpace D).bundle.baseSet ⟨d, hd⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hfy
  let eC := (cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ y hyC
  let eD := (cotangentSpace D).bundle.fiberCoordinates ⟨d, hd⟩ (f y) hyD
  have heJ (lam : CotangentFiber T (f y)) : J y (eD lam) = eC (lam.comp (L y)) := by
    ext i
    have heval := congrArg (fun β : CotangentFiber T (f y) => β (L y (v i y)))
      (Covectors.covector_expansion D.tangent.fiberCoordinates d hd (f y) hfy lam)
    simpa [J, QuotientBundles.columnOperator_apply, eC, eD,
      BundleData.SmoothVectorBundle.fiberCoordinates_apply, Covectors.cotangent_coordinates,
      α, v, hy, hfy, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using heval.symm
  have heLin : eC.toLinearMap.comp (L y).dualMap = (J y).toLinearMap.comp eD.toLinearMap := by
    ext lam i
    exact congrFun (heJ lam).symm i
  have heMap := congrArg (fun F => exteriorPower.map k F (ω (f y))) heLin
  simp only [exteriorPower.map_comp, LinearMap.comp_apply] at heMap
  change ((A.space.bundle.trivialization ⟨c, hc⟩)
      ⟨y, fiberPullback (V := TangentSpace S y) (W := TangentSpace T (f y)) k (L y) (ω (f y))⟩).2 =
    A.modelEquiv (exteriorPower.map k (J y).toLinearMap (B.modelEquiv.symm (z y)))
  rw [form_coordinates C k A c hc y hy]
  have hzval : z y = B.modelEquiv (exteriorPower.map k eD.toLinearMap (ω (f y))) :=
    form_coordinates D k B d hd (f y) hfy (ω (f y))
  rw [hzval, LinearEquiv.symm_apply_apply]
  exact congrArg A.modelEquiv heMap

/-- The intrinsic differential is constructed upstream from smooth germs. -/
theorem pullback_exists_proof : Specs.SmoothManifolds.Ch07.FormPullback.pullback_existsType.{u} := by
  intro n m a b M N _ _ S T C D f hf k A B ω
  let L := differential S T f hf
  have hL := differential_spec S T f hf
  exact ⟨L, hL, @pullback_smooth_proof.{u} n m a b M N _ _ S T C D f hf L hL k A B ω.field ω.smooth⟩


/-- Submanifold restriction is the same pullback construction with the inclusion. -/
theorem restriction_proof : Specs.SmoothManifolds.Ch07.FormPullback.restrictionType.{u} := by
  intro n m a b M N _ _ S T C D i hi L hL k A B ω hω
  constructor
  · exact @pullback_smooth_proof.{u} n m a b M N _ _ S T C D i hi.1 L hL k A B ω hω
  · intro p v
    dsimp only [FormPullbackData.pullbackField]
    with_reducible exact @evaluate_fiberPullback.{u} (TangentSpace S p) (TangentSpace T (i p)) _ _ _ _ k (L p) (ω (i p)) v


theorem pullback_apply :
    Specs.SmoothManifolds.Ch07.FormPullback.pullback_applyType.{u} := by
  intro n m a b M N _ _ S T f L k ω p v
  dsimp only [FormPullbackData.pullbackField]
  with_reducible
    exact @evaluate_fiberPullback.{u} (TangentSpace S p)
      (TangentSpace T (f p)) _ _ _ _ k (L p) (ω (f p)) v

theorem pullback_zero :
    Specs.SmoothManifolds.Ch07.FormPullback.pullback_zeroType.{u} := by
  exact pullback_zero_proof

theorem pullback_id :
    Specs.SmoothManifolds.Ch07.FormPullback.pullback_idType.{u} := by
  exact pullback_id_proof

theorem pullback_comp :
    Specs.SmoothManifolds.Ch07.FormPullback.pullback_compType.{u} := by
  exact pullback_comp_proof

theorem pullback_wedge :
    Specs.SmoothManifolds.Ch07.FormPullback.pullback_wedgeType.{u} := by
  intro n m a b M N _ _ S T f L k l α β
  funext p
  dsimp only [FormPullbackData.pullbackField, fieldWedge]
  with_reducible
    exact @fiberPullback_wedge.{u} (TangentSpace S p)
      (TangentSpace T (f p)) _ _ _ _ (L p) k l (α (f p)) (β (f p))

theorem pullback_high_degree :
    Specs.SmoothManifolds.Ch07.FormPullback.pullback_high_degreeType.{u} := by
  intro n m a b M N _ _ S T C D f L k ω h p
  rcases h with h | h
  · exact @ExteriorAlgebraResults.fields_above_dimension n a M _ S C k h (FormPullbackData.pullbackField S T f L ω) p
  · change fiberPullback (V := TangentSpace S p) (W := TangentSpace T (f p)) k (L p) (ω (f p)) = 0
    rw [@ExteriorAlgebraResults.fields_above_dimension m b N _ T D k h ω (f p), map_zero]

theorem tautological_apply :
    Specs.SmoothManifolds.Ch07.FormPullback.tautological_applyType.{u} := by
  intro n a M _ S C
  letI := (cotangentSpace C).topology
  dsimp only
  intro L ξ V
  rfl

theorem tautological_coordinates :
    Specs.SmoothManifolds.Ch07.FormPullback.tautological_coordinatesType.{u} := by
  exact tautological_coordinates_proof

theorem tautological_smooth :
    Specs.SmoothManifolds.Ch07.FormPullback.tautological_smoothType.{u} :=
  tautological_smooth_proof

theorem tautological_exists :
    Specs.SmoothManifolds.Ch07.FormPullback.tautological_existsType.{u} :=
  tautological_exists_proof

theorem signed_jacobian :
    Specs.SmoothManifolds.Ch07.FormPullback.signed_jacobianType.{u} :=
  signed_jacobian_proof

theorem pullback_smooth :
    Specs.SmoothManifolds.Ch07.FormPullback.pullback_smoothType.{u} :=
  pullback_smooth_proof

theorem pullback_exists :
    Specs.SmoothManifolds.Ch07.FormPullback.pullback_existsType.{u} :=
  pullback_exists_proof

theorem restriction :
    Specs.SmoothManifolds.Ch07.FormPullback.restrictionType.{u} :=
  restriction_proof

end SmoothManifolds.FormPullbackResults
