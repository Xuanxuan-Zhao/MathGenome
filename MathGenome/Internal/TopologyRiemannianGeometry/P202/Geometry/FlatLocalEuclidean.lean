import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.FlatLocalEuclidean
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionCalculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.CkDependence
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.Frobenius
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.LocalPrimitiveHomotopy

/-! Theorem 7.3: flatness iff local Euclidean geometry.
The chart formulation in the independent Specs uses genuine smooth atlas
charts and their intrinsic coordinate differentials on the whole source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

namespace P202.Geometry.FlatLocalEuclidean
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
  P202.TorsionMetricData P202.CurvatureData P202.FlatData
open Filter Set
open scoped Topology Matrix Matrix.Norms.Elementwise
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

open scoped RealInnerProductSpace

theorem exists_metric_orthonormal_basis {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) (p : M) :
    ∃ b : Module.Basis (Fin n) ℝ (TangentSpace S p), ∀ i j,
      pairing g p (b i) (b j) = if i = j then 1 else 0 := by
  classical
  letI : InnerProductSpace.Core ℝ (TangentSpace S p) := {
    inner := fun v w => pairing g p v w
    conj_inner_symm := by intro v w; exact g.symmetric p w v
    re_inner_nonneg := by
      intro v
      by_cases hv : v = 0
      · subst v; simp [pairing]
      · exact (g.positive p v hv).le
    add_left := by intro v w z; exact (pairing g p).map_add₂ v w z
    smul_left := by intro v w r; simp [pairing]
    definite := by
      intro v hv
      by_contra h
      exact (ne_of_gt (g.positive p v h)) hv }
  letI : NormedAddCommGroup (TangentSpace S p) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ (TangentSpace S p) :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (TangentSpace S p))
  obtain ⟨i, hi⟩ := (tangentRealization S).space.bundle.covers p
  let E := (tangentRealization S).space.bundle.fiberCoordinates i p hi
  letI : FiniteDimensional ℝ (TangentSpace S p) :=
    FiniteDimensional.of_injective E.toLinearMap E.injective
  have hdim : Module.finrank ℝ (TangentSpace S p) = n := by
    rw [E.finrank_eq]
    simp [Euclidean]
  let b := (stdOrthonormalBasis ℝ (TangentSpace S p)).reindex
    (finCongr hdim)
  refine ⟨b.toBasis, ?_⟩
  intro i j
  exact b.inner_eq_ite i j


theorem exists_parallel_orthonormal_of_basis {n : ℕ} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n .euclidean M}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (U : Set M) (p : M) (e : Fin n → Field S)
    (hpar : ∀ i q, q ∈ U → ∀ v : TangentSpace S q,
      pointDerivative C (e i).val q v = 0)
    (b : Module.Basis (Fin n) ℝ (TangentSpace S p))
    (hb : ∀ i, (e i).val p = b i) :
    ∃ E : Fin n → Field S,
      (∀ i q, q ∈ U → ∀ v : TangentSpace S q,
        pointDerivative C (E i).val q v = 0) ∧
      (∀ i j, pairing g p ((E i).val p) ((E j).val p) = if i = j then 1 else 0) := by
  classical
  obtain ⟨o, ho⟩ := exists_metric_orthonormal_basis g p
  let E : Fin n → Field S := fun j => ∑ i : Fin n, b.equivFun (o j) i • e i
  let eval (q : M) : Field S →ₗ[ℝ] TangentSpace S q := {
    toFun := fun X => X.val q
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hE (j : Fin n) : (E j).val p = o j := by
    change eval p (∑ i : Fin n, b.equivFun (o j) i • e i) = o j
    rw [map_sum]
    simp only [map_smul]
    change (∑ i : Fin n, b.equivFun (o j) i • (e i).val p) = o j
    simpa only [hb] using b.sum_equivFun (o j)
  refine ⟨E, ?_, ?_⟩
  · intro j q hq v
    obtain ⟨X, hX⟩ := P202.Geometry.ConnectionForms.section_evaluation_surjective
      (tangentBundle S) q v
    rw [← hX, P202.Geometry.ConnectionForms.pointDerivative_global]
    change eval q (C.cov X (∑ i : Fin n, b.equivFun (o j) i • e i)) = 0
    rw [map_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul, map_smul]
    have h := hpar i q hq (X.val q)
    rw [P202.Geometry.ConnectionForms.pointDerivative_global] at h
    change (C.cov X (e i)).val q = 0 at h
    change b.equivFun (o j) i • (C.cov X (e i)).val q = 0
    rw [h, smul_zero]
  · intro i j
    rw [hE i, hE j]
    exact ho i j


/-- Constancy near a point forces the intrinsic scalar derivative to vanish. -/
theorem scalarDerivative_eq_zero_of_eventually_const (f : M → ℝ) (r : ℝ)
    (p : M) (h : f =ᶠ[𝓝 p] fun _ => r) (v : TangentSpace S p) :
    scalarDerivative S f p v = 0 := by
  let F : GlobalSmooth S := algebraMap ℝ (GlobalSmooth S) r
  have hF : F.val =ᶠ[𝓝 p] f := by
    filter_upwards [h] with q hq
    exact hq.symm
  rw [ConnectionForms.scalarDerivative_representative f F p hF]
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
  rw [← hX, ← ConnectionForms.act_apply]
  exact congrArg (fun a : GlobalSmooth S => a.val p) ((act S X).map_algebraMap r)

/-- Smooth Euclidean coordinate data have global smooth field
representatives near the chosen point in the fixed intrinsic tangent model. -/
theorem exists_field_with_coordinate_germ
    (d : TangentIndex S) (p : M) (hp : p ∈ d.val.source)
    (O : Set (Euclidean n)) (hO : IsOpen O) (hpO : (d.val p).val ∈ O)
    (f : Euclidean n → Euclidean n) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) :
    ∃ X : Field S, ∀ᶠ q in 𝓝 p,
      SmoothManifolds.LieBracketData.coefficients (tangentStructure S)
        X.val d.val d.property q = f (d.val q).val := by
  obtain ⟨X, hX⟩ := SmoothManifolds.Frobenius.exists_field_with_coordinate_germ
    S (tangentStructure S) d.val d.property p hp O hO hpO f hf
  have hs : SmoothManifolds.SectionExtensionData.SmoothSection (tangentBundle S) X.val := by
    letI := (tangentStructure S).topology
    intro q
    exact SmoothManifolds.manifoldContDiffAt_comp
      (tangentStructure S).manifold.smoothStructure.property.1.1
      (X.smooth q) ((tangentRealization S).smooth_from_original _)
  exact ⟨⟨X.val, hs⟩, hX⟩

/-- An isometric chart has the identity Gram matrix at every point. -/
theorem metricMatrix_eq_identity (g : RiemannianMetric S)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hg : IsEuclideanChart g c) (p : M) (hp : p ∈ c.source) (i j : Fin n) :
    metricMatrix g ⟨c, hc⟩ p i j = if i = j then 1 else 0 := by
  classical
  obtain ⟨hc', hmetric⟩ := hg
  let d : TangentIndex S := ⟨c, hc⟩
  have hp' : p ∈ (tangentBundle S).baseSet d := by
    rwa [(tangentRealization S).baseSet d]
  have hcoords (k : Fin n) :
      (tangentStructure S).fiberCoordinates.equiv c hc' p hp (coordinateVector d k p) =
        Pi.single k 1 := by
    rw [← (tangentRealization S).coordinates d p hp]
    exact ((tangentBundle S).fiberCoordinates d p hp').apply_symm_apply _
  change pairing g p (coordinateVector d i p) (coordinateVector d j p) = _
  rw [hmetric p hp, hcoords i, hcoords j]
  simp [Pi.single_apply, eq_comm]

/-- In an isometric chart all Christoffel symbols vanish on the entire source. -/
theorem christoffel_eq_zero (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hg : IsEuclideanChart g c)
    (p : (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S)) (k i j : Fin n) :
    christoffel C ⟨c, hc⟩ p k i j = 0 := by
  classical
  let d : TangentIndex S := ⟨c, hc⟩
  have hp : p.val ∈ c.source := (tangentRealization S).baseSet d ▸ p.property
  have hd (r s t : Fin n) :
      scalarDerivative S (fun q => metricMatrix g d q r s) p.val
        (coordinateVector d t p.val) = 0 := by
    apply scalarDerivative_eq_zero_of_eventually_const _ (if r = s then 1 else 0)
    filter_upwards [c.open_source.mem_nhds hp] with q hq
    exact metricMatrix_eq_identity g c hc hg q hq r s
  rw [LeviCivita.christoffel_formula g C hC d p k i j]
  simp only [hd, add_zero, sub_zero, mul_zero, Finset.sum_const_zero]

/-- Smooth global representatives of the coordinate fields have zero covariant
pair derivatives wherever they agree locally with those fields. -/
theorem coordinate_cov_eq_zero (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hg : IsEuclideanChart g c) (p : M) (hp : p ∈ c.source)
    (e : Fin n → Field S)
    (he : ∀ j, ∀ᶠ q in 𝓝 p, (e j).val q = coordinateVector ⟨c, hc⟩ j q)
    (i j : Fin n) : (C.cov (e i) (e j)).val p = 0 := by
  let d : TangentIndex S := ⟨c, hc⟩
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B d
  have hp' : p ∈ B.baseSet d := by rwa [(tangentRealization S).baseSet d]
  have hsec : ∀ᶠ q in 𝓝 p, (e j).val q =
      SmoothManifolds.SectionExtension.totalSection (b.section_ j) q := by
    filter_upwards [he j, c.open_source.mem_nhds hp] with q heq hq
    have hq' : q ∈ B.baseSet d := by rwa [(tangentRealization S).baseSet d]
    rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq', heq]
    exact (LeviCivita.trivializationFrame_section d j ⟨q, hq'⟩).symm
  have hder : pointDerivative C
      (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p =
      pointDerivative C (e j).val p :=
    (ConnectionForms.pointDerivative_congr B C (e j).val _ p
      ⟨e j, Eventually.of_forall (fun _ => rfl)⟩ hsec).symm
  apply (b.basis ⟨p, hp'⟩).equivFun.injective
  rw [map_zero]
  funext k
  have h := christoffel_eq_zero g C hC c hc hg ⟨p, hp'⟩ k i j
  change ((b.basis ⟨p, hp'⟩).equivFun
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p
      (coordinateVector d i p))) k = 0 at h
  rw [hder, ← (he i).self_of_nhds] at h
  have hglob : pointDerivative C (e j).val p ((e i).val p) =
      (C.cov (e i) (e j)).val p := ConnectionForms.pointDerivative_global B C (e j) p (e i)
  rw [hglob] at h
  exact h

/-- Trilinearity reduces vanishing on a fiber to the coordinate basis. -/
theorem curvature_vanishes_of_coordinates (R : CurvatureTensor S)
    (d : TangentIndex S) (p : M) (hp : p ∈ (tangentBundle S).baseSet d)
    (h : ∀ i j k : Fin n,
      R.val p (coordinateVector d i p) (coordinateVector d j p) (coordinateVector d k p) = 0)
    (v w z : TangentSpace S p) : R.val p v w z = 0 := by
  classical
  let E := (tangentBundle S).fiberCoordinates d p hp
  calc
    R.val p v w z = R.val p
        (∑ i : Fin n, E v i • coordinateVector d i p)
        (∑ j : Fin n, E w j • coordinateVector d j p)
        (∑ k : Fin n, E z k • coordinateVector d k p) := by
      rw [LeviCivita.coordinate_expansion d p hp v,
        LeviCivita.coordinate_expansion d p hp w, LeviCivita.coordinate_expansion d p hp z]
    _ = 0 := by simp only [map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, h, smul_zero, Finset.sum_const_zero]

/-- A Euclidean chart has zero curvature on its entire source. -/
theorem flatOn_chart (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (c : ModelChart n .euclidean M) (hg : IsEuclideanChart g c) :
    FlatOn R c.source := by
  classical
  obtain ⟨hc, hmetric⟩ := hg
  have hg : IsEuclideanChart g c := ⟨hc, hmetric⟩
  let d : TangentIndex S := ⟨c, hc⟩
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B d
  intro p hp v w z
  have hp' : p ∈ B.baseSet d := by rwa [(tangentRealization S).baseSet d]
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨p, hp'⟩
  have hec (j : Fin n) : ∀ᶠ q in 𝓝 p, (e j).val q = coordinateVector d j q := by
    filter_upwards [he j, c.open_source.mem_nhds hp] with q heq hq
    have hq' : q ∈ B.baseSet d := by rwa [(tangentRealization S).baseSet d]
    rw [heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq']
    exact LeviCivita.trivializationFrame_section d j ⟨q, hq'⟩
  have hcov (i j : Fin n) : ∀ᶠ q in 𝓝 p, (C.cov (e i) (e j)).val q = 0 := by
    have hnear : ∀ᶠ q in 𝓝 p,
        ∀ k : Fin n, (e k).val q = coordinateVector d k q :=
      Filter.eventually_all.mpr hec
    obtain ⟨V, hV, hVo, hpV⟩ := eventually_nhds_iff.mp hnear
    filter_upwards [hVo.mem_nhds hpV, c.open_source.mem_nhds hp] with q hq hqc
    apply coordinate_cov_eq_zero g C hC c hc hg q hqc e
    intro k
    filter_upwards [hVo.mem_nhds hq] with r hr
    exact hV r hr k
  apply curvature_vanishes_of_coordinates R d p hp' _ v w z
  intro i j k
  have heval (l : Fin n) : (e l).val p = coordinateVector d l p := (hec l).self_of_nhds
  rw [← heval i, ← heval j, ← heval k, hR]
  have hfirst : (C.cov (e i) (C.cov (e j) (e k))).val p = 0 := by
    have h := ConnectionForms.locality_section B C (e i) (C.cov (e j) (e k)) 0 p (hcov j k)
    simpa only [map_zero, ConnectionForms.section_zero_apply] using h
  have hsecond : (C.cov (e j) (C.cov (e i) (e k))).val p = 0 := by
    have h := ConnectionForms.locality_section B C (e j) (C.cov (e i) (e k)) 0 p (hcov i k)
    simpa only [map_zero, ConnectionForms.section_zero_apply] using h
  have hbr : (bracket (e i) (e j)).val p = 0 :=
    LeviCivita.coordinate_bracket_zero d p hp' i j (e i) (e j) (hec i) (hec j)
  have hthird := ConnectionForms.cov_field_eq_zero B C (bracket (e i) (e j)) (e k) p hbr
  rw [CurvatureAlgebra.curvature_apply, hfirst, hsecond, hthird]
  simp only [LeviCivita.tangent_sub_as_add, smul_zero, add_zero]

theorem flat_of_locallyEuclidean :
    P202Specs.Geometry.FlatLocalEuclidean.flat_of_locallyEuclideanType.{u} := by
  intro n M _ S g C hC R hR U hU p hp
  obtain ⟨c, hpc, _, hcg⟩ := hU p hp
  exact flatOn_chart g C hC R hR c hcg p hpc

theorem local_covariant_coefficients
    (C : Connection (tangentBundle S)) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU) (X s : Field S) (p : U) (i : Fin n) :
    (b.basis p).equivFun ((C.cov X s).val p.val) i =
      scalarDerivative S (SmoothManifolds.FrameData.totalize
        (fun q : U => SmoothManifolds.FrameData.coefficients b
          (restrictGlobalSection s U hU).val q i)) p.val (X.val p.val) +
      ∑ j, connectionForm C b p i j (X.val p.val) *
        SmoothManifolds.FrameData.coefficients b (restrictGlobalSection s U hU).val p j := by
  have h := ConnectionForms.local_frame_formula (tangentBundle S) C b
    (restrictGlobalSection s U hU) p (X.val p.val) i
  have hcov := ConnectionForms.covOn_global (tangentBundle S) C U hU X s p
  rw [ConnectionForms.covOn_pointDerivative] at hcov
  exact (congrArg (fun v => (b.basis p).equivFun v i) hcov).symm.trans h

theorem connectionForm_global_representative
    (C : Connection (tangentBundle S)) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU) (p : U) (X e : Field S) (i j : Fin n)
    (he : ∀ᶠ q in 𝓝 p.val, e.val q =
      SmoothManifolds.SectionExtension.totalSection (b.section_ j) q) :
    connectionForm C b p i j (X.val p.val) =
      (b.basis p).equivFun ((C.cov X e).val p.val) i := by
  have hder : pointDerivative C e.val p.val = pointDerivative C
      (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val :=
    ConnectionForms.pointDerivative_congr (tangentBundle S) C _ _ p.val
      ⟨e, Eventually.of_forall (fun _ => rfl)⟩ he
  change (b.basis p).equivFun (pointDerivative C
    (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val
    (X.val p.val)) i = _
  rw [← hder, ConnectionForms.pointDerivative_global]


noncomputable def fieldConnectionEntry
    (C : Connection (tangentBundle S)) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU) (X : Field S) (i j : Fin n) : M → ℝ :=
  SmoothManifolds.FrameData.totalize
    (fun q : U => connectionForm C b q i j (X.val q.val))

theorem coefficient_connectionEntry_germ
    (C : Connection (tangentBundle S)) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU) (p : U) (X e : Field S) (i j : Fin n)
    (he : ∀ᶠ q in 𝓝 p.val, e.val q =
      SmoothManifolds.SectionExtension.totalSection (b.section_ j) q) :
    SmoothManifolds.FrameData.totalize
      (fun q : U => SmoothManifolds.FrameData.coefficients b
        (restrictGlobalSection (C.cov X e) U hU).val q i) =ᶠ[𝓝 p.val]
      fieldConnectionEntry C b X i j := by
  obtain ⟨V, hVe, hVo, hpV⟩ := eventually_nhds_iff.mp he
  filter_upwards [hVo.mem_nhds hpV, hU.mem_nhds p.property] with q hqV hqU
  simp only [fieldConnectionEntry, SmoothManifolds.FrameData.totalize_of_mem _ q hqU]
  change (b.basis ⟨q, hqU⟩).equivFun ((C.cov X e).val q) i = _
  apply (connectionForm_global_representative C b ⟨q, hqU⟩ X e i j ?_).symm
  filter_upwards [hVo.mem_nhds hqV] with r hr
  exact hVe r hr

theorem scalarDerivative_congr_of_representative (f g : M → ℝ) (p : M)
    (hf : ∃ F : GlobalSmooth S, F.val =ᶠ[𝓝 p] f) (hfg : f =ᶠ[𝓝 p] g) :
    scalarDerivative S f p = scalarDerivative S g p := by
  obtain ⟨F, hF⟩ := hf
  ext v
  rw [ConnectionForms.scalarDerivative_representative f F p hF,
    ConnectionForms.scalarDerivative_representative g F p (hF.trans hfg)]

theorem local_curvature_coefficient
    (C : Connection (tangentBundle S)) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU)
    (X Y e : Field S) (p : U) (i j : Fin n)
    (he : ∀ᶠ q in 𝓝 p.val, e.val q =
      SmoothManifolds.SectionExtension.totalSection (b.section_ j) q) :
    (b.basis p).equivFun ((curvature C X Y e).val p.val) i =
      scalarDerivative S (fieldConnectionEntry C b Y i j) p.val (X.val p.val) -
      scalarDerivative S (fieldConnectionEntry C b X i j) p.val (Y.val p.val) +
      ∑ k, connectionForm C b p i k (X.val p.val) * connectionForm C b p k j (Y.val p.val) -
      ∑ k, connectionForm C b p i k (Y.val p.val) * connectionForm C b p k j (X.val p.val) -
      connectionForm C b p i j ((bracket X Y).val p.val) := by
  have hXY := local_covariant_coefficients C b X (C.cov Y e) p i
  have hYX := local_covariant_coefficients C b Y (C.cov X e) p i
  have hA (Z : Field S) (k : Fin n) :
      SmoothManifolds.FrameData.coefficients b
        (restrictGlobalSection (C.cov Z e) U hU).val p k =
      connectionForm C b p k j (Z.val p.val) :=
    (connectionForm_global_representative C b p Z e k j he).symm
  have hD (Z : Field S) : scalarDerivative S
      (SmoothManifolds.FrameData.totalize (fun q : U =>
        SmoothManifolds.FrameData.coefficients b
          (restrictGlobalSection (C.cov Z e) U hU).val q i)) p.val =
      scalarDerivative S (fieldConnectionEntry C b Z i j) p.val := by
    obtain ⟨F, hF⟩ := ConnectionForms.local_coefficients_representative
      (tangentBundle S) b (restrictGlobalSection (C.cov Z e) U hU).val
      (restrictGlobalSection (C.cov Z e) U hU).property p
    exact scalarDerivative_congr_of_representative _ _ p.val ⟨F i, hF i⟩
      (coefficient_connectionEntry_germ C b p Z e i j he)
  simp only [P202.CurvatureData.curvature, ConnectionForms.section_add_apply,
    ConnectionForms.section_smul_apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [hXY, hYX, hD Y, hD X]
  simp_rw [hA]
  have hbr := connectionForm_global_representative C b p (bracket X Y) e i j he
  rw [← hbr]
  ring


theorem curvature_matrix_coefficients
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (hR : RepresentsCurvature C R) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU)
    (X Y : Field S) (p : U) (i j : Fin n) :
    (b.basis p).equivFun (R.val p.val (X.val p.val) (Y.val p.val) (b.section_ j p)) i =
      scalarDerivative S (fieldConnectionEntry C b Y i j) p.val (X.val p.val) -
      scalarDerivative S (fieldConnectionEntry C b X i j) p.val (Y.val p.val) +
      ∑ k, connectionForm C b p i k (X.val p.val) * connectionForm C b p k j (Y.val p.val) -
      ∑ k, connectionForm C b p i k (Y.val p.val) * connectionForm C b p k j (X.val p.val) -
      connectionForm C b p i j ((bracket X Y).val p.val) := by
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative (tangentBundle S) b p
  have hej : (e j).val p.val = b.section_ j p := by
    simpa only [SmoothManifolds.SectionExtension.totalSection_of_mem _ p.val p.property]
      using (he j).self_of_nhds
  rw [← hej, hR]
  exact local_curvature_coefficient C b X Y (e j) p i j (he j)

theorem local_maurer_cartan
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (hR : RepresentsCurvature C R) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU)
    (X Y : Field S) (p : U) (i j : Fin n)
    (hflat : R.val p.val (X.val p.val) (Y.val p.val) (b.section_ j p) = 0)
    (hcomm : (bracket X Y).val p.val = 0) :
    scalarDerivative S (fieldConnectionEntry C b Y i j) p.val (X.val p.val) -
      scalarDerivative S (fieldConnectionEntry C b X i j) p.val (Y.val p.val) +
      ∑ k, connectionForm C b p i k (X.val p.val) * connectionForm C b p k j (Y.val p.val) -
      ∑ k, connectionForm C b p i k (Y.val p.val) * connectionForm C b p k j (X.val p.val) = 0 := by
  have h := curvature_matrix_coefficients C R hR b X Y p i j
  rw [hflat, map_zero, Pi.zero_apply, hcomm, map_zero, sub_zero] at h
  exact h.symm

theorem fieldConnectionEntry_representative
    (C : Connection (tangentBundle S)) {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU) (p : U) (X : Field S) (i j : Fin n) :
    ∃ F : GlobalSmooth S, F.val =ᶠ[𝓝 p.val] fieldConnectionEntry C b X i j := by
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative (tangentBundle S) b p
  obtain ⟨F, hF⟩ := ConnectionForms.local_coefficients_representative (tangentBundle S) b
    (restrictGlobalSection (C.cov X (e j)) U hU).val
    (restrictGlobalSection (C.cov X (e j)) U hU).property p
  exact ⟨F i, (hF i).trans (coefficient_connectionEntry_germ C b p X (e j) i j (he j))⟩


/-- The source's zero-curvature compatibility equation, in the actual intrinsic
coordinate derivatives and Christoffel matrices, at any point of a chart. -/
theorem christoffel_maurer_cartan
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (hR : RepresentsCurvature C R) (d : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet d)
    (hflat : ∀ v w z : TangentSpace S p.val, R.val p.val v w z = 0)
    (i j row col : Fin n) :
    scalarDerivative S (SmoothManifolds.FrameData.totalize
        (fun q : (tangentBundle S).baseSet d => christoffel C d q row j col)) p.val
        (coordinateVector d i p.val) -
      scalarDerivative S (SmoothManifolds.FrameData.totalize
        (fun q : (tangentBundle S).baseSet d => christoffel C d q row i col)) p.val
        (coordinateVector d j p.val) +
      ∑ k, christoffel C d p row i k * christoffel C d p k j col -
      ∑ k, christoffel C d p row j k * christoffel C d p k i col = 0 := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B d
  have hO : IsOpen (B.baseSet d) :=
    B.trivialization_baseSet d ▸ (B.trivialization d).open_baseSet
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b p
  have hec (k : Fin n) : ∀ᶠ q in 𝓝 p.val,
      (e k).val q = coordinateVector d k q := by
    filter_upwards [he k, hO.mem_nhds p.property] with q heq hq
    rw [heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    exact LeviCivita.trivializationFrame_section d k ⟨q, hq⟩
  have hΓ (k r s : Fin n) : fieldConnectionEntry C b (e k) r s =ᶠ[𝓝 p.val]
      SmoothManifolds.FrameData.totalize
        (fun q : B.baseSet d => christoffel C d q r k s) := by
    filter_upwards [hec k, hO.mem_nhds p.property] with q heq hq
    simp only [fieldConnectionEntry, SmoothManifolds.FrameData.totalize_of_mem _ q hq]
    rw [heq]
    rfl
  have hD (k r s : Fin n) : scalarDerivative S (fieldConnectionEntry C b (e k) r s) p.val =
      scalarDerivative S (SmoothManifolds.FrameData.totalize
        (fun q : B.baseSet d => christoffel C d q r k s)) p.val :=
    scalarDerivative_congr_of_representative _ _ p.val
      (fieldConnectionEntry_representative C b p (e k) r s) (hΓ k r s)
  have h := local_maurer_cartan C R hR b (e i) (e j) p row col
    (hflat _ _ _) (LeviCivita.coordinate_bracket_zero d p.val p.property i j (e i) (e j)
      (hec i) (hec j))
  rw [hD j row col, hD i row col, (hec i).self_of_nhds, (hec j).self_of_nhds] at h
  exact h


theorem christoffel_representative
    (C : Connection (tangentBundle S)) (d : TangentIndex S)
    (p : (tangentBundle S).baseSet d) (row i col : Fin n) :
    ∃ F : GlobalSmooth S, F.val =ᶠ[𝓝 p.val] SmoothManifolds.FrameData.totalize
      (fun q : (tangentBundle S).baseSet d => christoffel C d q row i col) := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B d
  have hO : IsOpen (B.baseSet d) :=
    B.trivialization_baseSet d ▸ (B.trivialization d).open_baseSet
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b p
  have hec : ∀ᶠ q in 𝓝 p.val, (e i).val q = coordinateVector d i q := by
    filter_upwards [he i, hO.mem_nhds p.property] with q heq hq
    rw [heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    exact LeviCivita.trivializationFrame_section d i ⟨q, hq⟩
  have hΓ : fieldConnectionEntry C b (e i) row col =ᶠ[𝓝 p.val]
      SmoothManifolds.FrameData.totalize
        (fun q : B.baseSet d => christoffel C d q row i col) := by
    filter_upwards [hec, hO.mem_nhds p.property] with q heq hq
    simp only [fieldConnectionEntry, SmoothManifolds.FrameData.totalize_of_mem _ q hq]
    rw [heq]
    rfl
  obtain ⟨F, hF⟩ := fieldConnectionEntry_representative C b p (e i) row col
  exact ⟨F, hF.trans hΓ⟩

theorem christoffel_scalarContDiffAt
    (C : Connection (tangentBundle S)) (d : TangentIndex S)
    (p : (tangentBundle S).baseSet d) (row i col : Fin n) :
    SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
      (SmoothManifolds.FrameData.totalize
        (fun q : (tangentBundle S).baseSet d => christoffel C d q row i col)) p.val := by
  obtain ⟨F, hF⟩ := christoffel_representative C d p row i col
  exact SmoothManifolds.ScalarContDiffAt.congr
    ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp F.property p.val) hF

theorem christoffel_vectorSmoothAt
    (C : Connection (tangentBundle S)) (d : TangentIndex S)
    (p : (tangentBundle S).baseSet d) (row i col : Fin n) :
    SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
      (SmoothManifolds.FrameData.totalize
        (fun q : (tangentBundle S).baseSet d => christoffel C d q row i col)) p.val :=
  (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
    (christoffel_scalarContDiffAt C d p row i col)


/-- Evaluate the intrinsic differential using any actual smooth ambient extension
in a genuine chart. Smoothness of the manifold function is deduced from the extension. -/
theorem scalarDerivative_eq_fderiv
    (d : TangentIndex S) (p : M) (hp : p ∈ (tangentBundle S).baseSet d)
    (f : M → ℝ) (F : Euclidean n → ℝ) (W : Set (Euclidean n))
    (hW : IsOpen W) (hpW : (d.val p).val ∈ W) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W)
    (heq : (fun q => F (d.val q).val) =ᶠ[𝓝 p] f) (v : TangentSpace S p) :
    scalarDerivative S f p v =
      fderiv ℝ F (d.val p).val ((tangentBundle S).fiberCoordinates d p hp v) := by
  have hpc : p ∈ d.val.source := (tangentRealization S).baseSet d ▸ hp
  have hf := SmoothManifolds.scalarContDiffAt_of_chart
    S.smoothStructure.property.1 d.property hpc ⟨W, hW, hpW, F, hF, heq⟩
  have hG : GermChartExtension S p d.val (scalarGerm S f p) F := by
    refine ⟨⟨W, hW, hpW, hF⟩, ?_⟩
    simp only [scalarGerm, dite_eq_left hf]
    exact Germ.coe_eq.mpr heq
  change v.val (scalarGerm S f p) = _
  rw [SmoothManifolds.VectorFields.tangent_action_coordinates S
    (tangentStructure S).fiberCoordinates p d.val d.property hpc v (scalarGerm S f p) F hG]
  congr 1
  exact ((tangentRealization S).coordinates d p hpc v).symm


def euclideanModelPoint (x : Euclidean n) : ModelSpace n .euclidean := ⟨x, mem_univ x⟩

theorem continuous_euclideanModelPoint : Continuous (@euclideanModelPoint n) :=
  continuous_id.subtype_mk (fun x => mem_univ x)

def euclideanChartDomain (d : TangentIndex S) : Set (Euclidean n) :=
  euclideanModelPoint ⁻¹' d.val.target

theorem euclideanChartDomain_open (d : TangentIndex S) : IsOpen (euclideanChartDomain d) :=
  d.val.open_target.preimage continuous_euclideanModelPoint

noncomputable def coordinateFunction (d : TangentIndex S) (f : M → ℝ) (x : Euclidean n) : ℝ :=
  f (d.val.symm (euclideanModelPoint x))

theorem coordinateFunction_germ (d : TangentIndex S) (f : M → ℝ)
    (p : M) (hp : p ∈ d.val.source) :
    (fun q => coordinateFunction d f (d.val q).val) =ᶠ[𝓝 p] f := by
  filter_upwards [d.val.open_source.mem_nhds hp] with q hq
  change f (d.val.symm (d.val q)) = f q
  rw [d.val.left_inv hq]

theorem coordinateFunction_contDiffOn (d : TangentIndex S) (f : M → ℝ)
    (hf : ∀ p ∈ (tangentBundle S).baseSet d,
      SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val f p) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateFunction d f) (euclideanChartDomain d) := by
  intro x hx
  let p := d.val.symm (euclideanModelPoint x)
  have hp : p ∈ d.val.source := d.val.map_target hx
  have hpb : p ∈ (tangentBundle S).baseSet d := by
    rwa [(tangentRealization S).baseSet d]
  have hpx : (d.val p).val = x := congrArg Subtype.val (d.val.right_inv hx)
  obtain ⟨W, hW, hpW, F, hF, heq⟩ := (hf p hpb).2 d.val d.property hp
  have hcont : ContinuousAt (fun z => d.val.symm (euclideanModelPoint z)) x :=
    (d.val.continuousAt_symm hx).comp continuous_euclideanModelPoint.continuousAt
  have heqF : coordinateFunction d f =ᶠ[𝓝 x] F := by
    filter_upwards [heq.comp_tendsto hcont,
      (euclideanChartDomain_open d).mem_nhds hx] with z hz hzD
    change F (d.val (d.val.symm (euclideanModelPoint z))).val =
      f (d.val.symm (euclideanModelPoint z)) at hz
    rw [d.val.right_inv hzD] at hz
    exact hz.symm
  have hFat : ContDiffAt ℝ (⊤ : ℕ∞) F x := by
    simpa only [hpx] using hF.contDiffAt (hW.mem_nhds hpW)
  exact (hFat.congr_of_eventuallyEq heqF).contDiffWithinAt

noncomputable def euclideanChristoffel (C : Connection (tangentBundle S))
    (d : TangentIndex S) (i : Fin n) (x : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  fun row col => coordinateFunction d
    (SmoothManifolds.FrameData.totalize
      (fun p : (tangentBundle S).baseSet d => christoffel C d p row i col)) x

theorem euclideanChristoffel_entry_contDiffOn (C : Connection (tangentBundle S))
    (d : TangentIndex S) (i row col : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => euclideanChristoffel C d i x row col)
      (euclideanChartDomain d) :=
  coordinateFunction_contDiffOn d _
    (fun p hp => christoffel_vectorSmoothAt C d ⟨p, hp⟩ row i col)

theorem euclideanChristoffel_contDiffOn (C : Connection (tangentBundle S))
    (d : TangentIndex S) (i : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (euclideanChristoffel C d i) (euclideanChartDomain d) :=
  contDiffOn_pi.mpr (fun row => contDiffOn_pi.mpr
    (fun col => euclideanChristoffel_entry_contDiffOn C d i row col))


theorem euclideanChristoffel_entry_fderiv (C : Connection (tangentBundle S))
    (d : TangentIndex S) (p : (tangentBundle S).baseSet d) (i k row col : Fin n) :
    scalarDerivative S (SmoothManifolds.FrameData.totalize
        (fun q : (tangentBundle S).baseSet d => christoffel C d q row i col)) p.val
        (coordinateVector d k p.val) =
      fderiv ℝ (fun x => euclideanChristoffel C d i x row col) (d.val p.val).val
        (Pi.single k 1) := by
  have hp : p.val ∈ d.val.source := (tangentRealization S).baseSet d ▸ p.property
  have hpD : (d.val p.val).val ∈ euclideanChartDomain d := d.val.map_source hp
  have hcoord : (tangentBundle S).fiberCoordinates d p.val p.property
      (coordinateVector d k p.val) = Pi.single k 1 := by
    change (tangentBundle S).fiberCoordinates d p.val p.property
      (((tangentBundle S).fiberCoordinates d p.val p.property).symm (Pi.single k 1)) = _
    exact ((tangentBundle S).fiberCoordinates d p.val p.property).apply_symm_apply _
  have h := scalarDerivative_eq_fderiv d p.val p.property _
    (fun x => euclideanChristoffel C d i x row col) (euclideanChartDomain d)
    (euclideanChartDomain_open d) hpD (euclideanChristoffel_entry_contDiffOn C d i row col)
    (coordinateFunction_germ d _ p.val hp) (coordinateVector d k p.val)
  rw [hcoord] at h
  exact h

theorem euclideanChristoffel_entry_at (C : Connection (tangentBundle S))
    (d : TangentIndex S) (p : (tangentBundle S).baseSet d) (i row col : Fin n) :
    euclideanChristoffel C d i (d.val p.val).val row col = christoffel C d p row i col := by
  have hp : p.val ∈ d.val.source := (tangentRealization S).baseSet d ▸ p.property
  change SmoothManifolds.FrameData.totalize
    (fun q : (tangentBundle S).baseSet d => christoffel C d q row i col)
    (d.val.symm (d.val p.val)) = _
  rw [d.val.left_inv hp, SmoothManifolds.FrameData.totalize_of_mem _ p.val p.property]

theorem euclideanChristoffel_entry_maurer_cartan
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (hR : RepresentsCurvature C R) (d : TangentIndex S)
    (hflat : FlatOn R d.val.source)
    (x : Euclidean n) (hx : x ∈ euclideanChartDomain d) (i j row col : Fin n) :
    fderiv ℝ (fun y => euclideanChristoffel C d j y row col) x (Pi.single i 1) -
      fderiv ℝ (fun y => euclideanChristoffel C d i y row col) x (Pi.single j 1) +
      ∑ k, euclideanChristoffel C d i x row k * euclideanChristoffel C d j x k col -
      ∑ k, euclideanChristoffel C d j x row k * euclideanChristoffel C d i x k col = 0 := by
  let p := d.val.symm (euclideanModelPoint x)
  have hp : p ∈ d.val.source := d.val.map_target hx
  have hpb : p ∈ (tangentBundle S).baseSet d := by
    rwa [(tangentRealization S).baseSet d]
  have hpx : (d.val p).val = x := congrArg Subtype.val (d.val.right_inv hx)
  have h := christoffel_maurer_cartan C R hR d ⟨p, hpb⟩ (hflat p hp) i j row col
  rw [euclideanChristoffel_entry_fderiv C d ⟨p, hpb⟩ j i row col,
    euclideanChristoffel_entry_fderiv C d ⟨p, hpb⟩ i j row col] at h
  simp_rw [← euclideanChristoffel_entry_at C d ⟨p, hpb⟩] at h
  simpa only [hpx] using h



theorem euclideanChristoffel_fderiv_entry
    (C : Connection (tangentBundle S)) (d : TangentIndex S)
    (x : Euclidean n) (hx : x ∈ euclideanChartDomain d) (i row col : Fin n)
    (v : Euclidean n) :
    (fderiv ℝ (euclideanChristoffel C d i) x v) row col =
      fderiv ℝ (fun y => euclideanChristoffel C d i y row col) x v := by
  have hdiff : DifferentiableAt ℝ (euclideanChristoffel C d i) x :=
    ((euclideanChristoffel_contDiffOn C d i).contDiffAt
      ((euclideanChartDomain_open d).mem_nhds hx)).differentiableAt (by simp)
  have hrow : DifferentiableAt ℝ (fun y => euclideanChristoffel C d i y row) x :=
    (differentiableAt_pi.mp hdiff) row
  rw [fderiv_apply hrow col, fderiv_apply hdiff row]
  rfl

/-- The actual smooth Christoffel matrices on the genuine chart target satisfy
Euclidean Maurer–Cartan whenever the intrinsic curvature vanishes on its source. -/
theorem euclideanChristoffel_maurer_cartan
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (hR : RepresentsCurvature C R) (d : TangentIndex S)
    (hflat : FlatOn R d.val.source)
    (x : Euclidean n) (hx : x ∈ euclideanChartDomain d) (i j : Fin n) :
    fderiv ℝ (euclideanChristoffel C d j) x (Pi.single i 1) -
      fderiv ℝ (euclideanChristoffel C d i) x (Pi.single j 1) +
      euclideanChristoffel C d i x * euclideanChristoffel C d j x -
      euclideanChristoffel C d j x * euclideanChristoffel C d i x = 0 := by
  ext row col
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
    euclideanChristoffel_fderiv_entry C d x hx]
  exact euclideanChristoffel_entry_maurer_cartan C R hR d hflat x hx i j row col



/-- Simultaneous coordinates integrate the commuting fields, and their
orthonormality identifies the whole metric with the standard Euclidean metric.
This uses no closed-form or local-primitive certificate. -/
theorem exists_euclidean_chart_of_commuting_orthonormal
    (g : RiemannianMetric S) (U : Set M) (hU : IsOpen U) (p : M) (hp : p ∈ U)
    (e : Fin n → Field S)
    (horth : ∀ q ∈ U, ∀ i j : Fin n,
      pairing g q ((e i).val q) ((e j).val q) = if i = j then 1 else 0)
    (hcomm : ∀ i j q, q ∈ U → (bracket (e i) (e j)).val q = 0) :
    ∃ c : ModelChart n .euclidean M,
      p ∈ c.source ∧ c.source ⊆ U ∧ IsEuclideanChart g c := by
  classical
  have hlin : LinearIndependent ℝ (fun i => (e i).val p) := by
    apply Fintype.linearIndependent_iffₛ.mpr
    intro a b ha j
    have h := congrArg (fun v => pairing g p v ((e j).val p)) ha
    simp only [pairing, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul] at h
    change (∑ i, a i * pairing g p ((e i).val p) ((e j).val p)) =
      (∑ i, b i * pairing g p ((e i).val p) ((e j).val p)) at h
    simpa [horth p hp] using h
  have hb : SmoothManifolds.LieBracketData.BracketOperation (originalBracket (S := S)) :=
    (Classical.choose_spec (SmoothManifolds.LieBrackets.bracket_exists S
      (tangentStructure S))).1
  obtain ⟨c, hc, hpc, hec⟩ := SmoothManifolds.CommutingFields.simultaneous_coordinates
    S (tangentStructure S) originalBracket hb (fun i => originalField S (e i)) p
    (le_refl n) hlin ⟨U, hU, hp, hcomm⟩
  let d := c.restr U
  have hd : d ∈ S.smoothStructure.val := SmoothManifolds.Frobenius.chart_restr_mem S c hc U
  have hdsource : d.source = c.source ∩ U := c.restr_source' U hU
  refine ⟨d, hdsource ▸ ⟨hpc, hp⟩, ?_, hd, ?_⟩
  · rw [hdsource]
    exact inter_subset_right
  · intro q hq v w
    have hqU : q ∈ U := (hdsource ▸ hq).2
    let E := (tangentStructure S).fiberCoordinates.equiv d hd q hq
    have hEi (i : Fin n) : E ((e i).val q) = Pi.single i 1 := by
      change (tangentStructure S).fiberCoordinates.equiv (c.restr U) hd q hq _ = _
      rw [SmoothManifolds.Frobenius.fiberCoordinates_restr (tangentStructure S) c hc U q hq]
      exact hec q (hdsource ▸ hq).1 i
    have hexp (v : TangentSpace S q) :
        (∑ i : Fin n, E v i • (e i).val q) = v := by
      apply E.injective
      simp only [map_sum, map_smul, hEi]
      ext i
      simp [Pi.single_apply]
    calc
      pairing g q v w = pairing g q (∑ i : Fin n, E v i • (e i).val q)
          (∑ j : Fin n, E w j • (e j).val q) := by rw [hexp v, hexp w]
      _ = ∑ i : Fin n, E v i * E w i := by
        simp only [pairing, map_sum, map_smul, LinearMap.sum_apply,
          LinearMap.smul_apply, smul_eq_mul]
        change (∑ j, E w j * ∑ i, E v i * pairing g q ((e i).val q) ((e j).val q)) = _
        simp [horth q hqU, mul_comm]


/-- Independently specified version of the local integration theorem. -/
theorem chart_of_commuting_orthonormal :
    P202Specs.Geometry.FlatLocalEuclidean.chart_of_commuting_orthonormalType.{u} := by
  intro n M _ S g U hU p hp e horth hcomm
  exact exists_euclidean_chart_of_commuting_orthonormal g U hU p hp e horth hcomm

/-- Torsion freeness makes two locally parallel fields commute pointwise. -/
theorem bracket_eq_zero_of_parallel (C : Connection (tangentBundle S))
    (hC : IsTorsionFree C) (X Y : Field S) (p : M)
    (hX : ∀ v : TangentSpace S p, pointDerivative C X.val p v = 0)
    (hY : ∀ v : TangentSpace S p, pointDerivative C Y.val p v = 0) :
    (bracket X Y).val p = 0 := by
  have hXY := hY (X.val p)
  have hYX := hX (Y.val p)
  rw [ConnectionForms.pointDerivative_global] at hXY hYX
  rw [CurvatureAlgebra.bracket_cov C hC X Y]
  change (C.cov X Y).val p + (-1 : ℝ) • (C.cov Y X).val p = 0
  rw [hXY, hYX, smul_zero, add_zero]

/-- The zero-curvature compatibility equation for commuting directions.
This is the intrinsic residual identity used when extending a parallel field
from one coordinate slice to the next. -/
theorem cov_cov_commute_of_flat (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (U : Set M) (hflat : FlatOn R U) (X Y Z : Field S)
    (p : M) (hp : p ∈ U) (hbr : (bracket X Y).val p = 0) :
    (C.cov X (C.cov Y Z)).val p = (C.cov Y (C.cov X Z)).val p := by
  have h : (curvature C X Y Z).val p = 0 :=
    (hR X Y Z p).symm.trans (hflat p hp _ _ _)
  have hz := ConnectionForms.cov_field_eq_zero (tangentBundle S) C
    (bracket X Y) Z p hbr
  rw [CurvatureAlgebra.curvature_apply, hz,
    LeviCivita.tangent_sub_as_add, LeviCivita.tangent_sub_as_add,
    smul_zero, add_zero] at h
  obtain ⟨d, hd⟩ := (tangentBundle S).covers p
  let E := (tangentBundle S).fiberCoordinates d p hd
  apply E.injective
  have he := congrArg E h
  funext i
  have hi := congrFun he i
  simp only [map_add, map_smul, map_zero, Pi.add_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul] at hi
  linarith

/-- If a field is parallel in Y on a neighborhood, then its X-residual has
zero Y-derivative whenever X and Y commute and the curvature vanishes.
ODE uniqueness is still needed to propagate zero initial residuals. -/
theorem residual_cov_eq_zero_of_flat (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (U : Set M) (hflat : FlatOn R U) (X Y Z : Field S)
    (p : M) (hp : p ∈ U) (hbr : (bracket X Y).val p = 0)
    (hpar : ∀ᶠ q in 𝓝 p, (C.cov Y Z).val q = 0) :
    (C.cov Y (C.cov X Z)).val p = 0 := by
  rw [← cov_cov_commute_of_flat C R hR U hflat X Y Z p hp hbr]
  have h := ConnectionForms.locality_section (tangentBundle S) C X (C.cov Y Z) 0 p hpar
  simpa only [map_zero, ConnectionForms.section_zero_apply] using h

/-- The metric pairing of parallel fields has zero intrinsic differential on
the open set where they are parallel, and hence is locally constant there. -/
theorem pairing_locallyConstant_of_parallel (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsMetricCompatible g C)
    (U : Set M) (hU : IsOpen U) (X Y : Field S)
    (hX : ∀ p ∈ U, ∀ v : TangentSpace S p, pointDerivative C X.val p v = 0)
    (hY : ∀ p ∈ U, ∀ v : TangentSpace S p, pointDerivative C Y.val p v = 0) :
    IsLocallyConstant (fun p : U => pairing g p.val (X.val p.val) (Y.val p.val)) := by
  let f := LeviCivita.fieldPairing g X Y
  have hf := (SmoothManifolds.mem_globalSmoothAlgebra_iff S f.val).mp f.property
  apply SmoothManifolds.LocalPrimitiveHomotopy.locallyConstantOn_of_dFunction_zero
    S f.val hf U hU
  intro p hp
  apply LinearMap.ext
  intro v
  have hd : scalarDerivative S f.val p v = 0 := by
    obtain ⟨Z, hZ⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
    rw [← hZ]
    change scalarDerivative S (fun q => pairing g q (X.val q) (Y.val q)) p (Z.val p) = 0
    rw [hC Z X Y p]
    have hXZ := hX p hp (Z.val p)
    have hYZ := hY p hp (Z.val p)
    rw [ConnectionForms.pointDerivative_global] at hXZ hYZ
    simp only [hXZ, hYZ, pairing, map_zero, LinearMap.zero_apply, add_zero]
  rw [ConnectionForms.scalarDerivative_representative f.val f p EventuallyEq.rfl] at hd
  exact hd

/-- A parallel frame need only be orthonormal at the chosen point. Metric
compatibility preserves its Gram matrix locally; torsion freeness and the
simultaneous-coordinate theorem then give an actual isometric chart. -/
theorem exists_euclidean_chart_of_parallel
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (U : Set M) (hU : IsOpen U) (p : M) (hp : p ∈ U)
    (e : Fin n → Field S)
    (horth : ∀ i j : Fin n,
      pairing g p ((e i).val p) ((e j).val p) = if i = j then 1 else 0)
    (hpar : ∀ q ∈ U, ∀ i : Fin n, ∀ v : TangentSpace S q,
      pointDerivative C (e i).val q v = 0) :
    ∃ c : ModelChart n .euclidean M,
      p ∈ c.source ∧ c.source ⊆ U ∧ IsEuclideanChart g c := by
  classical
  have hloc (i j : Fin n) : ∀ᶠ q in 𝓝 (⟨p, hp⟩ : U),
      pairing g q.val ((e i).val q.val) ((e j).val q.val) =
        pairing g p ((e i).val p) ((e j).val p) :=
    (pairing_locallyConstant_of_parallel g C hC.2 U hU (e i) (e j)
      (fun q hq => hpar q hq i) (fun q hq => hpar q hq j)).eventually_eq ⟨p, hp⟩
  have hnear : ∀ᶠ q in 𝓝 (⟨p, hp⟩ : U), ∀ i j : Fin n,
      pairing g q.val ((e i).val q.val) ((e j).val q.val) = if i = j then 1 else 0 := by
    have hall := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hloc i))
    filter_upwards [hall] with q hq i j
    exact (hq i j).trans (horth i j)
  obtain ⟨V, hV, hVo, hpV⟩ := eventually_nhds_iff.mp hnear
  let W : Set M := Subtype.val '' V
  have hWo : IsOpen W := hU.isOpenEmbedding_subtypeVal.isOpenMap V hVo
  have hpW : p ∈ W := ⟨⟨p, hp⟩, hpV, rfl⟩
  have hWU : W ⊆ U := by
    rintro q ⟨r, _, rfl⟩
    exact r.property
  obtain ⟨c, hpc, hcW, hcg⟩ := exists_euclidean_chart_of_commuting_orthonormal
    g W hWo p hpW e (by
      rintro q ⟨r, hr, rfl⟩ i j
      exact hV r hr i j) (by
      intro i j q hq
      exact bracket_eq_zero_of_parallel C hC.1 (e i) (e j) q
        (hpar q (hWU hq) i) (hpar q (hWU hq) j))
  exact ⟨c, hpc, hcW.trans hWU, hcg⟩

/-- Any parallel frame gives an isometric chart. Constant changes of frame
make its initial values orthonormal, and metric compatibility preserves them. -/
theorem exists_euclidean_chart_of_parallel_basis
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (U : Set M) (hU : IsOpen U) (p : M) (hp : p ∈ U)
    (e : Fin n → Field S)
    (hpar : ∀ q ∈ U, ∀ i : Fin n, ∀ v : TangentSpace S q,
      pointDerivative C (e i).val q v = 0)
    (b : Module.Basis (Fin n) ℝ (TangentSpace S p))
    (hb : ∀ i, (e i).val p = b i) :
    ∃ c : ModelChart n .euclidean M,
      p ∈ c.source ∧ c.source ⊆ U ∧ IsEuclideanChart g c := by
  obtain ⟨E, hE, horth⟩ := exists_parallel_orthonormal_of_basis g C U p e
    (fun i q hq => hpar q hq i) b hb
  exact exists_euclidean_chart_of_parallel g C hC U hU p hp E horth
    (fun q hq i => hE i q hq)

/-- It suffices to extend each prescribed initial vector to a local parallel
field. A finite intersection gives a common neighborhood for an orthonormal
initial basis, including the empty basis in dimension zero. -/
theorem exists_euclidean_chart_of_parallel_extensions
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (U : Set M) (hU : IsOpen U) (p : M) (hp : p ∈ U)
    (hext : ∀ v : TangentSpace S p,
      ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
        ∃ e : Field S, e.val p = v ∧
          ∀ q ∈ V, ∀ w : TangentSpace S q, pointDerivative C e.val q w = 0) :
    ∃ c : ModelChart n .euclidean M,
      p ∈ c.source ∧ c.source ⊆ U ∧ IsEuclideanChart g c := by
  classical
  obtain ⟨b, hb⟩ := exists_metric_orthonormal_basis g p
  choose V hVo hpV hVU e he hpar using fun i => hext (b i)
  let W : Set M := U ∩ ⋂ i : Fin n, V i
  have hWo : IsOpen W := hU.inter (isOpen_iInter_of_finite hVo)
  have hpW : p ∈ W := ⟨hp, mem_iInter.mpr hpV⟩
  obtain ⟨c, hpc, hcW, hcg⟩ := exists_euclidean_chart_of_parallel
    g C hC W hWo p hpW e (by
      intro i j
      rw [he i, he j]
      exact hb i j) (by
      intro q hq i w
      exact hpar i q (mem_iInter.mp hq.2 i) w)
  exact ⟨c, hpc, fun q hq => (hcW hq).1, hcg⟩

/-- Vanishing in the coordinate directions is vanishing in all directions;
the intrinsic covariant derivative is linear in its tangent argument. -/
theorem pointDerivative_eq_zero_of_coordinates
    (C : Connection (tangentBundle S)) (s : Field S)
    (d : TangentIndex S) (p : M) (hp : p ∈ (tangentBundle S).baseSet d)
    (h : ∀ i : Fin n, pointDerivative C s.val p (coordinateVector d i p) = 0)
    (v : TangentSpace S p) : pointDerivative C s.val p v = 0 := by
  let E := (tangentBundle S).fiberCoordinates d p hp
  calc
    pointDerivative C s.val p v = pointDerivative C s.val p
        (∑ i : Fin n, E v i • coordinateVector d i p) :=
      congrArg (pointDerivative C s.val p) (LeviCivita.coordinate_expansion d p hp v).symm
    _ = 0 := by simp only [map_sum, map_smul, h, smul_zero, Finset.sum_const_zero]

/-- A smooth parallel family on an open domain can be replaced near any
point by global smooth representatives. Thus local sections suffice for the
parallel-frame construction; no global topology assumption is needed. -/
theorem exists_euclidean_chart_of_local_parallel
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (U : Set M) (hU : IsOpen U) (p : M) (hp : p ∈ U)
    (s : Fin n → LocalSection (tangentBundle S) U hU)
    (horth : ∀ i j : Fin n,
      pairing g p ((s i).val ⟨p, hp⟩) ((s j).val ⟨p, hp⟩) =
        if i = j then 1 else 0)
    (hpar : ∀ q ∈ U, ∀ i : Fin n, ∀ v : TangentSpace S q,
      pointDerivative C (SmoothManifolds.SectionExtension.totalSection (s i).val) q v = 0) :
    ∃ c : ModelChart n .euclidean M,
      p ∈ c.source ∧ c.source ⊆ U ∧ IsEuclideanChart g c := by
  classical
  have hex (i : Fin n) : ∃ e : Field S, ∀ᶠ q in 𝓝 p,
      e.val q = SmoothManifolds.SectionExtension.totalSection (s i).val q :=
    ConnectionForms.exists_section_representative (tangentBundle S) U hU _
      (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S)
        hU _ (s i).property) p hp
  choose e he using hex
  have hnear := Filter.eventually_all.mpr he
  obtain ⟨V, hV, hVo, hpV⟩ := eventually_nhds_iff.mp hnear
  have hpW : p ∈ V ∩ U := ⟨hpV, hp⟩
  obtain ⟨c, hpc, hcW, hcg⟩ := exists_euclidean_chart_of_parallel
    g C hC (V ∩ U) (hVo.inter hU) p hpW e (by
      intro i j
      have hei := (he i).self_of_nhds
      have hej := (he j).self_of_nhds
      rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ p hp] at hei hej
      rw [hei, hej]
      exact horth i j) (by
      intro q hq i v
      have heq : ∀ᶠ r in 𝓝 q,
          (e i).val r = SmoothManifolds.SectionExtension.totalSection (s i).val r := by
        filter_upwards [hVo.mem_nhds hq.1] with r hr
        exact hV r hr i
      have hd : pointDerivative C (e i).val q =
          pointDerivative C (SmoothManifolds.SectionExtension.totalSection (s i).val) q :=
        ConnectionForms.pointDerivative_congr (tangentBundle S) C _ _ q
          ⟨e i, Eventually.of_forall (fun _ => rfl)⟩ heq
      rw [hd]
      exact hpar q hq.2 i v)
  exact ⟨c, hpc, fun q hq => (hcW hq).2, hcg⟩

section CoordinateODE
open scoped ContDiff Matrix.Norms.Elementwise

open D13Unified D13Unified.Ch06.C1Dependence
open Specs.D13Unified.Ch04.MaximalSolutionMap

/-- A smooth family of initial conditions determines a jointly smooth local
solution on an actual open neighborhood, including its initial hyperplane. -/
theorem smooth_solution_with_initial_data
    {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (hF : ContDiffOn ℝ ∞ (field F) F.domain)
    (s : ℝ) (V : Set P) (hV : IsOpen V) (η : P → E)
    (hη : ContDiffOn ℝ ∞ η V) (p₀ : P) (hp₀ : p₀ ∈ V)
    (hstart : ((s, η p₀), p₀) ∈ F.domain) :
    ∃ (W : Set (ℝ × P)) (Y : ℝ × P → E),
      IsOpen W ∧ (s, p₀) ∈ W ∧
      ContDiffOn ℝ ∞ Y W ∧
      (∀ p, (s, p) ∈ W → Y (s, p) = η p) ∧
      (∀ q ∈ W, ((q.1, Y q), q.2) ∈ F.domain) ∧
      (∀ q ∈ W, HasDerivAt (fun t => Y (t, q.2))
        (field F ((q.1, Y q), q.2)) q.1) := by
  classical
  let c : ℝ × P → ℝ × ((ℝ × E) × P) :=
    fun q => (q.1, ((s, η q.2), q.2))
  let A : Set (ℝ × P) := Prod.snd ⁻¹' V
  have hA : IsOpen A := hV.preimage continuous_snd
  have hc : ContDiffOn ℝ ∞ c A :=
    contDiffOn_fst.prodMk ((contDiffOn_const.prodMk
      (hη.comp contDiffOn_snd (fun _ hq => hq))).prodMk contDiffOn_snd)
  obtain ⟨hD, hsol⟩ := D13Unified.Ch06.CkDependence.joint_smooth F hF
  let W : Set (ℝ × P) := A ∩ c ⁻¹' parameterSolutionDomainValue F
  have hW : IsOpen W := hc.continuousOn.isOpen_inter_preimage hA hD
  have hF1 : ContDiffOn ℝ 1 (field F) F.domain := hF.of_le (by simp)
  have hFip := F.locallyLipschitzInState_of_contDiffOn hF1
  have hinit := ParameterODE.solutionValue_ivp F hFip s (η p₀) p₀ hstart
  have hpW : (s, p₀) ∈ W := ⟨hp₀, hstart, hinit.2.1⟩
  let Y : ℝ × P → E := solution F ∘ c
  refine ⟨W, Y, hW, hpW, hsol.comp (hc.mono inter_subset_left) (fun _ hq => hq.2),
    ?_, ?_, ?_⟩
  · intro p hp
    exact (ParameterODE.solutionValue_ivp F hFip s (η p) p hp.2.1).2.2
  · intro q hq
    exact (ParameterODE.solutionValue_on_domain F hFip q.1 s (η q.2) q.2 hq.2).2
  · intro q hq
    exact D13Unified.Ch06.C1Dependence.terminal_derivative F hF1 q.1 s (η q.2) q.2 hq.2

/-- The neighborhood can be taken to be one common open time interval times
an open neighborhood of the initial parameter. -/
theorem smooth_solution_on_product
    {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (hF : ContDiffOn ℝ ∞ (field F) F.domain)
    (s : ℝ) (V : Set P) (hV : IsOpen V) (η : P → E)
    (hη : ContDiffOn ℝ ∞ η V) (p₀ : P) (hp₀ : p₀ ∈ V)
    (hstart : ((s, η p₀), p₀) ∈ F.domain) :
    ∃ (a b : ℝ) (U : Set P) (Y : ℝ × P → E),
      a < s ∧ s < b ∧ IsOpen U ∧ p₀ ∈ U ∧ U ⊆ V ∧
      ContDiffOn ℝ ∞ Y (Ioo a b ×ˢ U) ∧
      (∀ p ∈ U, Y (s, p) = η p) ∧
      (∀ t ∈ Ioo a b, ∀ p ∈ U, ((t, Y (t,p)), p) ∈ F.domain) ∧
      (∀ t ∈ Ioo a b, ∀ p ∈ U, HasDerivAt (fun r => Y (r,p))
        (field F ((t,Y (t,p)),p)) t) := by
  obtain ⟨W,Y,hW,hsW,hY,hY0,hYmem,hYd⟩ :=
    smooth_solution_with_initial_data F hF s V hV η hη p₀ hp₀ hstart
  obtain ⟨T,U,hT,hsT,hU,hpU,hTU⟩ := mem_nhds_prod_iff'.mp (hW.mem_nhds hsW)
  obtain ⟨a,b,⟨has,hsb⟩,hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hT.mem_nhds hsT)
  let U' : Set P := U ∩ V
  have hsub : Ioo a b ×ˢ U' ⊆ W := by
    rintro ⟨t,p⟩ ⟨ht,hp⟩
    exact hTU ⟨hab ht,hp.1⟩
  refine ⟨a,b,U',Y,has,hsb,hU.inter hV,⟨hpU,hp₀⟩,inter_subset_right,
    hY.mono hsub, ?_, ?_, ?_⟩
  · intro p hp
    exact hY0 p (hsub ⟨⟨has,hsb⟩,hp⟩)
  · intro t ht p hp
    exact hYmem (t,p) (hsub ⟨ht,hp⟩)
  · intro t ht p hp
    exact hYd (t,p) (hsub ⟨ht,hp⟩)

/-- The actual one-coordinate matrix equation with smooth initial data,
with no prior solution, inverse matrix, or derivative certificate as input. -/
theorem local_matrix_solution
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (n : ℕ) (O : Set (ℝ × P)) (hO : IsOpen O)
    (Γ : ℝ × P → Matrix (Fin n) (Fin n) ℝ) (hΓ : ContDiffOn ℝ ∞ Γ O)
    (s : ℝ) (V : Set P) (hV : IsOpen V)
    (η : P → Matrix (Fin n) (Fin n) ℝ) (hη : ContDiffOn ℝ ∞ η V)
    (p₀ : P) (hp₀ : p₀ ∈ V) (hstart : (s,p₀) ∈ O) :
    ∃ (a b : ℝ) (U : Set P) (Y : ℝ × P → Matrix (Fin n) (Fin n) ℝ),
      a < s ∧ s < b ∧ IsOpen U ∧ p₀ ∈ U ∧ U ⊆ V ∧
      (Ioo a b ×ˢ U) ⊆ O ∧ ContDiffOn ℝ ∞ Y (Ioo a b ×ˢ U) ∧
      (∀ p ∈ U, Y (s,p) = η p) ∧
      (∀ t ∈ Ioo a b, ∀ p ∈ U,
        HasDerivAt (fun r => Y (r,p)) (-(Γ (t,p)) * Y (t,p)) t) := by
  classical
  let D : Set ((ℝ × Matrix (Fin n) (Fin n) ℝ) × P) :=
    (fun q => (q.1.1,q.2)) ⁻¹' O
  have hD : IsOpen D := hO.preimage (continuous_fst.fst.prodMk continuous_snd)
  let G : ((ℝ × Matrix (Fin n) (Fin n) ℝ) × P) → Matrix (Fin n) (Fin n) ℝ :=
    fun q => -(Γ (q.1.1,q.2)) * q.1.2
  have hG : ContDiffOn ℝ ∞ G D := by
    have hΓ' : ContDiffOn ℝ ∞ (fun q : (ℝ × Matrix (Fin n) (Fin n) ℝ) × P =>
        Γ (q.1.1,q.2)) D :=
      hΓ.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd) (fun _ hq => hq)
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    change ContDiffOn ℝ ∞ (fun q => ∑ k, -(Γ (q.1.1,q.2) i k) * q.1.2 k j) D
    exact ContDiffOn.sum (fun k _ =>
      ((contDiffOn_pi.mp (contDiffOn_pi.mp hΓ' i) k).neg).mul
        (contDiffOn_pi.mp (contDiffOn_pi.mp contDiffOn_fst.snd k) j))
  let F : ParameterODE (Matrix (Fin n) (Fin n) ℝ) P :=
    ⟨D,hD,(fun q => G q.val),continuousOn_iff_continuous_domRestrict.mp hG.continuousOn⟩
  have hfield : ContDiffOn ℝ ∞ (field F) F.domain := by
    apply hG.congr
    intro q hq
    simp only [field, Specs.D13Unified.Ch01.AutonomousParameters.parameterEvalValue,
      F, hq, dite_true]
  obtain ⟨a,b,U,Y,has,hsb,hU,hpU,hUV,hY,hY0,hYmem,hYd⟩ :=
    smooth_solution_on_product F hfield s V hV η hη p₀ hp₀ hstart
  refine ⟨a,b,U,Y,has,hsb,hU,hpU,hUV,?_,hY,hY0,?_⟩
  · rintro ⟨t,p⟩ ⟨ht,hp⟩
    exact hYmem t ht p hp
  · intro t ht p hp
    have hm := hYmem t ht p hp
    have he : field F ((t,Y (t,p)),p) = -(Γ (t,p)) * Y (t,p) := by
      simp only [field, Specs.D13Unified.Ch01.AutonomousParameters.parameterEvalValue,
        F, hm, dite_true]
      rfl
    rw [← he]
    exact hYd t ht p hp

end CoordinateODE

theorem trivializationFrame_coefficients (d : TangentIndex S)
    (X : Field S) (q : (tangentBundle S).baseSet d) :
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) d).basis q).equivFun (X.val q.val) =
      (tangentBundle S).fiberCoordinates d q.val q.property (X.val q.val) := by
  simp only [SmoothManifolds.ConstantRankBundles.trivializationFrame,
    Module.Basis.map_equivFun, Pi.basisFun_equivFun, LinearEquiv.trans_refl,
    LinearEquiv.symm_symm]

/-- A genuine smooth coordinate solution of the parallel equations represents
an intrinsically parallel field, independently of its extension away from q. -/
theorem pointDerivative_eq_zero_of_coordinate_pde
    (C : Connection (tangentBundle S)) (d : TangentIndex S) (X : Field S)
    (q : M) (hq : q ∈ (tangentBundle S).baseSet d)
    (O : Set (Euclidean n)) (hO : IsOpen O) (hqO : (d.val q).val ∈ O)
    (f : Euclidean n → Euclidean n) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (hcoords : ∀ᶠ r in 𝓝 q,
      SmoothManifolds.LieBracketData.coefficients (tangentStructure S)
        X.val d.val d.property r = f (d.val r).val)
    (hPDE : ∀ i row : Fin n,
      fderiv ℝ f (d.val q).val (Pi.single i 1) row +
        ∑ k, christoffel C d ⟨q,hq⟩ row i k * f (d.val q).val k = 0)
    (v : TangentSpace S q) : pointDerivative C X.val q v = 0 := by
  classical
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B d
  let a (row : Fin n) := SmoothManifolds.FrameData.totalize
    (fun p : B.baseSet d => SmoothManifolds.FrameData.coefficients b
      (restrictGlobalSection X (B.baseSet d)
        (B.trivialization_baseSet d ▸ (B.trivialization d).open_baseSet)).val p row)
  have hbase : IsOpen (B.baseSet d) :=
    B.trivialization_baseSet d ▸ (B.trivialization d).open_baseSet
  have ha (row : Fin n) : (fun r => f (d.val r).val row) =ᶠ[𝓝 q] a row := by
    filter_upwards [hcoords, hbase.mem_nhds hq] with r hr hrbase
    simp only [a, SmoothManifolds.FrameData.totalize_of_mem _ r hrbase]
    change f (d.val r).val row =
      (b.basis ⟨r,hrbase⟩).equivFun (X.val r) row
    rw [trivializationFrame_coefficients]
    exact (congrFun ((LeviCivita.original_coordinates_eq d X r hrbase).symm.trans hr) row).symm
  apply pointDerivative_eq_zero_of_coordinates C X d q hq _ v
  intro i
  apply (b.basis ⟨q,hq⟩).equivFun.injective
  rw [map_zero]
  funext row
  obtain ⟨Y,hY⟩ := ConnectionForms.section_evaluation_surjective B q (coordinateVector d i q)
  have hl := local_covariant_coefficients C b Y X ⟨q,hq⟩ row
  rw [hY] at hl
  have hd : scalarDerivative S (a row) q (coordinateVector d i q) =
      fderiv ℝ (fun x => f x row) (d.val q).val (Pi.single i 1) := by
    rw [scalarDerivative_eq_fderiv d q hq (a row) (fun x => f x row)
      O hO hqO (contDiffOn_pi.mp hf row) (ha row)]
    congr 1
    exact (B.fiberCoordinates d q hq).apply_symm_apply _
  change (b.basis ⟨q,hq⟩).equivFun ((C.cov Y X).val q) row =
    scalarDerivative S (a row) q (coordinateVector d i q) +
      ∑ j, connectionForm C b ⟨q,hq⟩ row j (coordinateVector d i q) *
        (b.basis ⟨q,hq⟩).equivFun (X.val q) j at hl
  rw [hd] at hl
  have hcoef : (b.basis ⟨q,hq⟩).equivFun (X.val q) =
      B.fiberCoordinates d q hq (X.val q) :=
    trivializationFrame_coefficients d X ⟨q,hq⟩
  rw [hcoef] at hl
  have hvf : B.fiberCoordinates d q hq (X.val q) = f (d.val q).val :=
    (LeviCivita.original_coordinates_eq d X q hq).symm.trans hcoords.self_of_nhds
  rw [hvf] at hl
  have hdiff : DifferentiableAt ℝ f (d.val q).val :=
    (hf.contDiffAt (hO.mem_nhds hqO)).differentiableAt (by simp)
  have hrow : fderiv ℝ (fun x => f x row) (d.val q).val (Pi.single i 1) =
      fderiv ℝ f (d.val q).val (Pi.single i 1) row := by
    exact congrArg (fun L : Euclidean n →L[ℝ] ℝ => L (Pi.single i 1))
      (((hasFDerivAt_apply row (f (d.val q).val)).comp _ hdiff.hasFDerivAt).fderiv)
  rw [hrow] at hl
  have hz := hPDE i row
  change fderiv ℝ f (d.val q).val (Pi.single i 1) row +
    ∑ k, connectionForm C b ⟨q,hq⟩ row k (coordinateVector d i q) * f (d.val q).val k = 0 at hz
  rw [hz] at hl
  rw [← hY, ConnectionForms.pointDerivative_global]
  exact hl

/-- A smooth coordinate solution with prescribed initial value gives an
actual local parallel field, represented by a global smooth field near p. -/
theorem parallel_extension_of_coordinate_solution
    (C : Connection (tangentBundle S)) (d : TangentIndex S)
    (U : Set M) (hU : IsOpen U) (p : M) (hpU : p ∈ U)
    (hp : p ∈ (tangentBundle S).baseSet d) (v : TangentSpace S p)
    (O : Set (Euclidean n)) (hO : IsOpen O) (hpO : (d.val p).val ∈ O)
    (f : Euclidean n → Euclidean n) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (hinit : f (d.val p).val = (tangentBundle S).fiberCoordinates d p hp v)
    (hPDE : ∀ q (hq : q ∈ (tangentBundle S).baseSet d), (d.val q).val ∈ O →
      ∀ i row : Fin n,
        fderiv ℝ f (d.val q).val (Pi.single i 1) row +
          ∑ k, christoffel C d ⟨q,hq⟩ row i k * f (d.val q).val k = 0) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∃ X : Field S, X.val p = v ∧
        ∀ q ∈ V, ∀ w : TangentSpace S q, pointDerivative C X.val q w = 0 := by
  have hpc : p ∈ d.val.source := (tangentRealization S).baseSet d ▸ hp
  obtain ⟨X, hX⟩ := exists_field_with_coordinate_germ d p hpc O hO hpO f hf
  obtain ⟨W,hWX,hWo,hpW⟩ := eventually_nhds_iff.mp hX
  let T : Set M := d.val.source ∩ (fun q => (d.val q).val) ⁻¹' O
  have hTo : IsOpen T :=
    (continuous_subtype_val.comp_continuousOn d.val.continuousOn_toFun).isOpen_inter_preimage
      d.val.open_source hO
  let V : Set M := (U ∩ W) ∩ T
  have hVo : IsOpen V := (hU.inter hWo).inter hTo
  have hpV : p ∈ V := ⟨⟨hpU,hpW⟩,hpc,hpO⟩
  refine ⟨V,hVo,hpV,fun q hq => hq.1.1,X,?_,?_⟩
  · apply ((tangentBundle S).fiberCoordinates d p hp).injective
    exact ((LeviCivita.original_coordinates_eq d X p hp).symm.trans
      hX.self_of_nhds).trans hinit
  · intro q hq w
    have hqb : q ∈ (tangentBundle S).baseSet d := by
      rw [(tangentRealization S).baseSet d]
      exact hq.2.1
    apply pointDerivative_eq_zero_of_coordinate_pde C d X q hqb O hO hq.2.2 f hf
    · filter_upwards [hWo.mem_nhds hq.1.2] with r hr
      exact hWX r hr
    · exact hPDE q hqb hq.2.2


noncomputable section HorizontalIntegration
open Set Filter
open scoped Topology ContDiff
namespace Horizontal
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.TangentBundleData SmoothManifolds.VectorFieldData
  SmoothManifolds.FiniteRegularityData SmoothManifolds.LieBracketData

/-- The global identity chart with the source's actual Euclidean model subtype. -/
def identityChart (d : ℕ) : ModelChart d .euclidean (Euclidean d) where
  toFun := fun x => ⟨x, mem_univ x⟩
  invFun := Subtype.val
  source := univ
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun _ _ => rfl
  right_inv' := fun _ _ => rfl
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := (continuous_id.subtype_mk _).continuousOn
  continuousOn_invFun := continuous_subtype_val.continuousOn

@[simp] theorem identityChart_apply (d : ℕ) (x : Euclidean d) :
    ((identityChart d) x).val = x := rfl

/-- Smooth Euclidean vector fields commuting on an open set have actual
intrinsic global smooth realizations commuting near each specified point. -/
theorem cutoff_commuting_fields
    {d k : ℕ} (S : SmoothManifold d .euclidean (Euclidean d))
    (he : identityChart d ∈ S.smoothStructure.val) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (O : Set (Euclidean d)) (hO : IsOpen O)
    (p : Euclidean d) (hp : p ∈ O)
    (v : Fin k → Euclidean d → Euclidean d)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) O)
    (hc : ∀ i j q, q ∈ O →
      fderiv ℝ (v j) q (v i q) = fderiv ℝ (v i) q (v j q)) :
    ∃ (X : Fin k → SmoothField B) (W : Set (Euclidean d)),
      IsOpen W ∧ p ∈ W ∧ W ⊆ O ∧
      (∀ i q, q ∈ W → coefficients B (X i).val (identityChart d) he q = v i q) ∧
      (∀ i j q, q ∈ W → (b (X i) (X j)).val q = 0) := by
  classical
  have hX (i : Fin k) : ∃ X : SmoothField B,
      ∀ᶠ q in 𝓝 p, coefficients B X.val (identityChart d) he q = v i q := by
    exact SmoothManifolds.Frobenius.exists_field_with_coordinate_germ S B
      (identityChart d) he p (mem_univ _) O hO hp (v i) (hv i)
  choose X hX using hX
  have hall : ∀ᶠ q in 𝓝 p, ∀ i,
      coefficients B (X i).val (identityChart d) he q = v i q :=
    Filter.eventually_all.mpr hX
  obtain ⟨W,hWsub,hW,hpW⟩ := eventually_nhds_iff.mp (hall.and (hO.mem_nhds hp))
  refine ⟨X,W,hW,hpW,(fun q hq => (hWsub q hq).2), ?_, ?_⟩
  · intro i q hq
    exact (hWsub q hq).1 i
  · intro i j q hq
    have hqi := (hWsub q hq).1 i
    have hqj := (hWsub q hq).1 j
    have hqO := (hWsub q hq).2
    have hi : HasCoordinateDerivative (identityChart d)
        (coefficients B (X i).val (identityChart d) he) q (fderiv ℝ (v i) q) := by
      refine ⟨v i, ((hv i).contDiffAt (hO.mem_nhds hqO)).differentiableAt (by simp) |>.hasFDerivAt, ?_⟩
      filter_upwards [hW.mem_nhds hq] with r hr
      exact ((hWsub r hr).1 i).symm
    have hj : HasCoordinateDerivative (identityChart d)
        (coefficients B (X j).val (identityChart d) he) q (fderiv ℝ (v j) q) := by
      refine ⟨v j, ((hv j).contDiffAt (hO.mem_nhds hqO)).differentiableAt (by simp) |>.hasFDerivAt, ?_⟩
      filter_upwards [hW.mem_nhds hq] with r hr
      exact ((hWsub r hr).1 j).symm
    have hbr := (SmoothManifolds.LieBrackets.bracket_coordinates S B b hb (X i) (X j)).2
    have hz : coefficients B (b (X i) (X j)).val (identityChart d) he q = 0 := by
      ext l
      rw [hbr (identityChart d) he q (mem_univ _) _ _ hi hj l, hqi, hqj]
      rw [Finset.sum_sub_distrib, ← SmoothManifolds.Frobenius.linearMap_apply_component,
        ← SmoothManifolds.Frobenius.linearMap_apply_component]
      rw [hc i j q hqO, sub_self, Pi.zero_apply]
    apply (B.fiberCoordinates.equiv (identityChart d) he q (mem_univ _)).injective
    unfold coefficients at hz
    rw [dite_eq_left (show q ∈ (identityChart d).source from mem_univ _)] at hz
    simpa only [map_zero] using hz

/-- Straightening actual intrinsic fields yields an ordinary smooth local
parametrization whose partial derivatives are the prescribed Euclidean fields. -/
theorem inverse_chart_parametrization
    {d k : ℕ} (hk : k ≤ d)
    (S : SmoothManifold d .euclidean (Euclidean d))
    (he : identityChart d ∈ S.smoothStructure.val) (B : TangentBundleStructure S)
    (X : Fin k → SmoothField B) (v : Fin k → Euclidean d → Euclidean d)
    (O : Set (Euclidean d)) (hO : IsOpen O) (p : Euclidean d) (hpO : p ∈ O)
    (hX : ∀ i q, q ∈ O → coefficients B (X i).val (identityChart d) he q = v i q)
    (c : ModelChart d .euclidean (Euclidean d)) (hc : c ∈ S.smoothStructure.val)
    (hp : p ∈ c.source)
    (hstraight : ∀ q (hq : q ∈ c.source) (i : Fin k),
      B.fiberCoordinates.equiv c hc q hq ((X i).val q) = Pi.single (Fin.castLE hk i) 1) :
    ∃ (U : Set (Euclidean d)) (F : Euclidean d → Euclidean d),
      IsOpen U ∧ (c p).val ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ F (c p).val = p ∧
      MapsTo F U O ∧ ∀ y ∈ U, ∀ i : Fin k,
        fderiv ℝ F y (Pi.single (Fin.castLE hk i) 1) = v i (F y) := by
  obtain ⟨V,hV,hpV,F,hF,hrep⟩ := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 c hc (identityChart d) he) hp (mem_univ _)
  have hrep' : ∀ᶠ q in 𝓝 p, F (c q).val = q := hrep
  obtain ⟨R,hRsub,hR,hpR⟩ := eventually_nhds_iff.mp
    (hrep'.and (Filter.Eventually.and (c.open_source.mem_nhds hp) (hO.mem_nhds hpO)))
  let j := SmoothManifolds.InteriorInverse.ambientChart c
  have hjs : j.source = c.source := by
    simp [j, SmoothManifolds.InteriorInverse.ambientChart_source,
      SmoothManifolds.ModelData.modelSet]
  have hpj : p ∈ j.source := by rwa [hjs]
  let T : Set (Euclidean d) := j.target ∩ j.symm ⁻¹' R
  have hT : IsOpen T :=
    j.continuousOn_invFun.isOpen_inter_preimage j.open_target hR
  have hpT : (c p).val ∈ T := by
    refine ⟨j.map_source hpj, ?_⟩
    change j.symm (j p) ∈ R
    rw [j.left_inv hpj]
    exact hpR
  have hFinv (y : Euclidean d) (hy : y ∈ T) : F y = j.symm y := by
    have hh := (hRsub _ hy.2).1
    change F (j (j.symm y)) = j.symm y at hh
    rwa [j.right_inv hy.1] at hh
  let U := V ∩ T
  have hU : IsOpen U := hV.inter hT
  refine ⟨U,F,hU,⟨hpV,hpT⟩,hF.mono inter_subset_left,(hRsub p hpR).1,?_,?_⟩
  · intro y hy
    rw [hFinv y hy.2]
    exact (hRsub _ hy.2.2).2.2
  · intro y hy i
    let q := F y
    have hqR : q ∈ R := by
      change F y ∈ R
      rw [hFinv y hy.2]
      exact hy.2.2
    have hqc : q ∈ c.source := (hRsub q hqR).2.1
    have hqO : q ∈ O := (hRsub q hqR).2.2
    have hcy : (c q).val = y := by
      change j (F y) = y
      rw [hFinv y hy.2]
      exact j.right_inv hy.2.1
    have hrepq : (fun r => F (c r).val) =ᶠ[𝓝 q] (fun r => ((identityChart d) r).val) := by
      filter_upwards [hR.mem_nhds hqR] with r hr
      exact (hRsub r hr).1
    have hd := SmoothManifolds.TangentBundle.transition_jacobian S B.fiberCoordinates
      c (identityChart d) hc he q hqc (mem_univ _) V F hV
      (by rw [hcy]; exact hy.1) hF hrepq ((X i).val q)
    have hvq : B.fiberCoordinates.equiv (identityChart d) he q (mem_univ _)
        ((X i).val q) = v i q := by
      have hh := hX i q hqO
      unfold coefficients at hh
      rwa [dite_eq_left (show q ∈ (identityChart d).source from mem_univ _)] at hh
    rw [hvq, hstraight q hqc i, hcy] at hd
    exact hd.symm

/-- A local Euclidean parametrization tangent to any finite independent
commuting family, constructed without an input integral-manifold certificate. -/
theorem commuting_parametrization
    {d k : ℕ} (hk : k ≤ d)
    (O : Set (Euclidean d)) (hO : IsOpen O) (p : Euclidean d) (hp : p ∈ O)
    (v : Fin k → Euclidean d → Euclidean d)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) O)
    (hc : ∀ i j q, q ∈ O →
      fderiv ℝ (v j) q (v i q) = fderiv ℝ (v i) q (v j q))
    (hind : LinearIndependent ℝ (fun i => v i p)) :
    ∃ (U : Set (Euclidean d)) (F : Euclidean d → Euclidean d),
      IsOpen U ∧ (0 : Euclidean d) ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ F 0 = p ∧
      MapsTo F U O ∧ ∀ y ∈ U, ∀ i : Fin k,
        fderiv ℝ F y (Pi.single (Fin.castLE hk i) 1) = v i (F y) := by
  classical
  obtain ⟨S,he⟩ := SmoothManifolds.Frobenius.smoothManifold_of_fullChart
    (identityChart d) rfl
  let B : TangentBundleStructure S := Classical.choice (SmoothManifolds.TangentBundle.exists_bundle S)
  obtain ⟨b,hb,_⟩ := SmoothManifolds.LieBrackets.bracket_exists S B
  obtain ⟨X,W,hW,hpW,hWO,hX,hbr⟩ := cutoff_commuting_fields S he B b hb O hO p hp v hv hc
  let A := B.fiberCoordinates.equiv (identityChart d) he p (mem_univ _)
  have hlin : LinearIndependent ℝ (fun i => (X i).val p) := by
    apply LinearIndependent.of_comp A.toLinearMap
    have heq : (A.toLinearMap ∘ (fun i => (X i).val p)) = fun i => v i p := by
      funext i
      have hh := hX i p hpW
      unfold coefficients at hh
      rwa [dite_eq_left (show p ∈ (identityChart d).source from mem_univ _)] at hh
    rw [heq]
    exact hind
  obtain ⟨c,hc,hpc,hstraight⟩ := SmoothManifolds.CommutingFields.simultaneous_coordinates
    S B b hb X p hk hlin ⟨W,hW,hpW,hbr⟩
  obtain ⟨V,G,hV,hpV,hG,hGp,hGW,hGd⟩ :=
    inverse_chart_parametrization hk S he B X v W hW p hpW hX c hc hpc hstraight
  let a := (c p).val
  let shift : Euclidean d → Euclidean d := fun y => y + a
  let U := shift ⁻¹' V
  have hsmooth : ContDiff ℝ ∞ shift := contDiff_id.add contDiff_const
  have hU : IsOpen U := hV.preimage hsmooth.continuous
  have h0 : (0 : Euclidean d) ∈ U := by simpa [U,shift] using hpV
  let F := G ∘ shift
  have hF : ContDiffOn ℝ ∞ F U := hG.comp hsmooth.contDiffOn (fun _ hy => hy)
  refine ⟨U,F,hU,h0,hF,by simpa [F,shift] using hGp,?_,?_⟩
  · intro y hy
    exact hWO (hGW hy)
  · intro y hy i
    have hGs := ((hG.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have hshift : HasFDerivAt shift (ContinuousLinearMap.id ℝ (Euclidean d)) y :=
      (hasFDerivAt_id y).add_const a
    have hdf := (hGs.comp y hshift).fderiv
    rw [hdf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    exact hGd (shift y) hy i

theorem longitudinalInclusion_single {d k : ℕ} (hk : k ≤ d) (i : Fin k) :
    SmoothManifolds.Frobenius.longitudinalInclusion hk (Pi.single i 1) =
      Pi.single (Fin.castLE hk i) 1 := by
  ext j
  by_cases hj : j.val < k
  · simp [SmoothManifolds.Frobenius.longitudinalInclusion, hj, Pi.single_apply,
      Fin.ext_iff]
  · have hij : (Fin.castLE hk i) ≠ j := by
      intro heq
      have heq' := congrArg Fin.val heq
      exact hj (heq' ▸ i.isLt)
    simp [SmoothManifolds.Frobenius.longitudinalInclusion, hj,
      Pi.single_eq_of_ne hij.symm]

/-- Commuting fields whose first k components are the coordinate unit fields
integrate to a smooth local graph over those k coordinates. -/
theorem commuting_graph
    {d k : ℕ} (hk : k ≤ d)
    (O : Set (Euclidean d)) (hO : IsOpen O) (p : Euclidean d) (hp : p ∈ O)
    (v : Fin k → Euclidean d → Euclidean d)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) O)
    (hc : ∀ i j q, q ∈ O →
      fderiv ℝ (v j) q (v i q) = fderiv ℝ (v i) q (v j q))
    (hproj : ∀ i q, q ∈ O →
      SmoothManifolds.Frobenius.longitudinalProjection hk (v i q) = Pi.single i 1) :
    ∃ (V : Set (Euclidean k)) (G : Euclidean k → Euclidean d),
      IsOpen V ∧ SmoothManifolds.Frobenius.longitudinalProjection hk p ∈ V ∧
      ContDiffOn ℝ ∞ G V ∧
      G (SmoothManifolds.Frobenius.longitudinalProjection hk p) = p ∧
      MapsTo G V O ∧
      (∀ x ∈ V, SmoothManifolds.Frobenius.longitudinalProjection hk (G x) = x) ∧
      (∀ x ∈ V, ∀ i : Fin k, fderiv ℝ G x (Pi.single i 1) = v i (G x)) := by
  classical
  let P := SmoothManifolds.Frobenius.longitudinalProjection hk
  let I := SmoothManifolds.Frobenius.longitudinalInclusion hk
  have hind : LinearIndependent ℝ (fun i => v i p) := by
    apply LinearIndependent.of_comp P.toLinearMap
    have heq : P.toLinearMap ∘ (fun i => v i p) = fun i => Pi.single i 1 := by
      funext i
      exact hproj i p hp
    rw [heq]
    exact Pi.linearIndependent_single_one (Fin k) ℝ
  obtain ⟨U,F,hU,h0U,hF,hF0,hFO,hFd⟩ := commuting_parametrization hk O hO p hp v hv hc hind
  let A : Set (Euclidean k) := I ⁻¹' U
  have hA : IsOpen A := hU.preimage I.continuous
  have h0A : (0 : Euclidean k) ∈ A := by simpa [A] using h0U
  let H : Euclidean k → Euclidean d := F ∘ I
  have hH : ContDiffOn ℝ ∞ H A := hF.comp I.contDiff.contDiffOn (fun _ hx => hx)
  have hH0 : H 0 = p := by simpa [H] using hF0
  have hHO : MapsTo H A O := fun _ hx => hFO hx
  have hHd (x : Euclidean k) (hx : x ∈ A) (i : Fin k) :
      fderiv ℝ H x (Pi.single i 1) = v i (H x) := by
    have hdF := ((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hd := (hdF.comp x I.hasFDerivAt).fderiv
    rw [hd, ContinuousLinearMap.comp_apply, longitudinalInclusion_single hk i]
    exact hFd (I x) hx i
  obtain ⟨ε,hε,hεA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds h0A)
  let B : Set (Euclidean k) := Metric.ball 0 ε
  have hB : IsOpen B := Metric.isOpen_ball
  have h0B : (0 : Euclidean k) ∈ B := Metric.mem_ball_self hε
  have hBA : B ⊆ A := hεA
  let K : Euclidean k → Euclidean k := P ∘ H
  have hK : ContDiffOn ℝ ∞ K A := P.contDiff.contDiffOn.comp hH (fun _ _ => mem_univ _)
  have hKd (x : Euclidean k) (hx : x ∈ B) :
      fderiv ℝ K x = ContinuousLinearMap.id ℝ (Euclidean k) := by
    have hdH := ((hH.contDiffAt (hA.mem_nhds (hBA hx))).differentiableAt (by simp)).hasFDerivAt
    have hdK := (P.hasFDerivAt.comp x hdH).fderiv
    have hcols (i : Fin k) : fderiv ℝ K x (Pi.single i 1) = Pi.single i 1 := by
      rw [hdK,ContinuousLinearMap.comp_apply,hHd x (hBA hx) i]
      exact hproj i (H x) (hHO (hBA hx))
    ext u j
    rw [SmoothManifolds.Frobenius.linearMap_apply_component]
    simp only [hcols, ContinuousLinearMap.id_apply]
    simp [Pi.single_apply]
  have hKval (x : Euclidean k) (hx : x ∈ B) : K x = x + P p := by
    have heq := hB.eqOn_of_fderiv_eq (convex_ball (0 : Euclidean k) ε).isPreconnected
      (hK.differentiableOn (by simp) |>.mono hBA)
      ((differentiable_id.add_const (P p) : Differentiable ℝ (fun y : Euclidean k => y + P p)).differentiableOn)
      (fun y hy => (hKd y hy).trans ((hasFDerivAt_id y).add_const (P p)).fderiv.symm)
      h0B (by simp [K,hH0])
    exact heq hx
  let V : Set (Euclidean k) := (fun x => x - P p) ⁻¹' B
  have hV : IsOpen V := hB.preimage (continuous_id.sub continuous_const)
  have hpV : P p ∈ V := by simpa [V] using h0B
  let G : Euclidean k → Euclidean d := fun x => H (x - P p)
  have hG : ContDiffOn ℝ ∞ G V :=
    (hH.mono hBA).comp (contDiffOn_id.sub contDiffOn_const) (fun _ hx => hx)
  refine ⟨V,G,hV,hpV,hG,by simpa [G,P] using hH0,?_,?_,?_⟩
  · intro x hx
    exact hHO (hBA hx)
  · intro x hx
    have hh := hKval (x - P p) hx
    change P (H (x - P p)) = _ at hh
    simpa only [sub_add_cancel] using hh
  · intro x hx i
    have hdH := ((hH.contDiffAt (hA.mem_nhds (hBA hx))).differentiableAt (by simp)).hasFDerivAt
    have hshift : HasFDerivAt (fun y : Euclidean k => y - P p)
        (ContinuousLinearMap.id ℝ (Euclidean k)) x := (hasFDerivAt_id x).sub_const (P p)
    change (fderiv ℝ (H ∘ fun y : Euclidean k => y - P p) x) (Pi.single i 1) = v i (G x)
    rw [(hdH.comp x hshift).fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply]
    exact hHd (x-P p) (hBA hx) i

end Horizontal

end HorizontalIntegration

noncomputable section HorizontalLiftCalculus
open Set Filter
open scoped Topology Matrix ContDiff Matrix.Norms.Elementwise
open SmoothManifolds.ModelData
namespace HorizontalLift


def baseProjection (n r : ℕ) : Euclidean (n+r) →L[ℝ] Euclidean n :=
  SmoothManifolds.Frobenius.longitudinalProjection (Nat.le_add_right n r)

def fiberProjection (n r : ℕ) : Euclidean (n+r) →L[ℝ] Euclidean r :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (Fin.natAdd n a)

def appendLinear (n r : ℕ) : (Euclidean n × Euclidean r) →L[ℝ] Euclidean (n+r) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => Fin.append x.1 x.2
    map_add' := by intros; ext k; refine Fin.addCases ?_ ?_ k <;> intro i <;> simp
    map_smul' := by intros; ext k; refine Fin.addCases ?_ ?_ k <;> intro i <;> simp }

@[simp] theorem appendLinear_apply {n r : ℕ} (x : Euclidean n) (z : Euclidean r) :
    appendLinear n r (x,z) = Fin.append x z := rfl

@[simp] theorem baseProjection_append {n r : ℕ} (x : Euclidean n) (z : Euclidean r) :
    baseProjection n r (Fin.append x z) = x := by
  ext i
  change Fin.append x z (Fin.castAdd r i) = x i
  exact Fin.append_left x z i

@[simp] theorem fiberProjection_append {n r : ℕ} (x : Euclidean n) (z : Euclidean r) :
    fiberProjection n r (Fin.append x z) = z := by
  ext i
  exact Fin.append_right x z i

def mulVecBilin (r : ℕ) : Matrix (Fin r) (Fin r) ℝ →L[ℝ] Euclidean r →L[ℝ] Euclidean r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Euclidean r →ₗ[ℝ] Euclidean r) ≃ₗ[ℝ] (Euclidean r →L[ℝ] Euclidean r)).toLinearMap.comp
      (Matrix.mulVecBilin ℝ ℝ))

@[simp] theorem mulVecBilin_apply {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (z : Euclidean r) :
    mulVecBilin r A z = A *ᵥ z := rfl

def horizontalLift {n r : ℕ} (Γ : Fin n → Euclidean n → Matrix (Fin r) (Fin r) ℝ)
    (i : Fin n) (q : Euclidean (n+r)) : Euclidean (n+r) :=
  Fin.append (Pi.single i 1) (-(Γ i (baseProjection n r q) *ᵥ fiberProjection n r q))

@[simp] theorem baseProjection_horizontalLift {n r : ℕ}
    (Γ : Fin n → Euclidean n → Matrix (Fin r) (Fin r) ℝ) (i : Fin n) (q : Euclidean (n+r)) :
    baseProjection n r (horizontalLift Γ i q) = Pi.single i 1 :=
  baseProjection_append _ _

@[simp] theorem fiberProjection_horizontalLift {n r : ℕ}
    (Γ : Fin n → Euclidean n → Matrix (Fin r) (Fin r) ℝ) (i : Fin n) (q : Euclidean (n+r)) :
    fiberProjection n r (horizontalLift Γ i q) = -(Γ i (baseProjection n r q) *ᵥ fiberProjection n r q) :=
  fiberProjection_append _ _

theorem horizontalLift_smooth {n r : ℕ}
    (Γ : Fin n → Euclidean n → Matrix (Fin r) (Fin r) ℝ)
    (O : Set (Euclidean n)) (hΓ : ∀ i, ContDiffOn ℝ ∞ (Γ i) O) (i : Fin n) :
    ContDiffOn ℝ ∞ (horizontalLift Γ i) ((baseProjection n r) ⁻¹' O) := by
  have hA := (hΓ i).comp (baseProjection n r).contDiff.contDiffOn (fun _ h => h)
  have hM := ((mulVecBilin r).contDiff.comp_contDiffOn hA).clm_apply
    (fiberProjection n r).contDiff.contDiffOn
  have he : ContDiffOn ℝ ∞ (fun _ : Euclidean (n+r) => (Pi.single i 1 : Euclidean n))
      ((baseProjection n r) ⁻¹' O) := contDiffOn_const
  exact (appendLinear n r).contDiff.comp_contDiffOn (he.prodMk hM.neg)


theorem horizontalLift_fderiv_apply {n r : ℕ}
    (Γ : Fin n → Euclidean n → Matrix (Fin r) (Fin r) ℝ)
    (i : Fin n) (q v : Euclidean (n+r))
    (hΓ : DifferentiableAt ℝ (Γ i) (baseProjection n r q)) :
    fderiv ℝ (horizontalLift Γ i) q v =
      Fin.append 0 (-(fderiv ℝ (Γ i) (baseProjection n r q) (baseProjection n r v) *ᵥ
        fiberProjection n r q + Γ i (baseProjection n r q) *ᵥ fiberProjection n r v)) := by
  have hA := hΓ.hasFDerivAt.comp q (baseProjection n r).hasFDerivAt
  have hM := (mulVecBilin r).hasFDerivAt_of_bilinear hA (fiberProjection n r).hasFDerivAt
  have he : HasFDerivAt (fun _ : Euclidean (n+r) => (Pi.single i 1 : Euclidean n)) (0 : Euclidean (n+r) →L[ℝ] Euclidean n) q :=
    hasFDerivAt_const _ _
  have hL := (appendLinear n r).hasFDerivAt.comp q (he.prodMk hM.neg)
  rw [show fderiv ℝ (horizontalLift Γ i) q = _ from hL.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply, appendLinear_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, mulVecBilin_apply]
  congr 2
  exact add_comm _ _


theorem horizontalLift_commute {n r : ℕ}
    (Γ : Fin n → Euclidean n → Matrix (Fin r) (Fin r) ℝ)
    (O : Set (Euclidean n)) (hO : IsOpen O)
    (hΓ : ∀ i, ContDiffOn ℝ ∞ (Γ i) O)
    (hMC : ∀ i j x, x ∈ O →
      fderiv ℝ (Γ j) x (Pi.single i 1) - fderiv ℝ (Γ i) x (Pi.single j 1) +
        Γ i x * Γ j x - Γ j x * Γ i x = 0)
    (i j : Fin n) (q : Euclidean (n+r)) (hq : baseProjection n r q ∈ O) :
    fderiv ℝ (horizontalLift Γ j) q (horizontalLift Γ i q) =
      fderiv ℝ (horizontalLift Γ i) q (horizontalLift Γ j q) := by
  have hd (a : Fin n) : DifferentiableAt ℝ (Γ a) (baseProjection n r q) :=
    ((hΓ a).contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  rw [horizontalLift_fderiv_apply Γ j q _ (hd j),
    horizontalLift_fderiv_apply Γ i q _ (hd i)]
  simp only [baseProjection_horizontalLift, fiberProjection_horizontalLift]
  congr 2
  have h := congrArg (fun A => A *ᵥ fiberProjection n r q)
    (hMC i j (baseProjection n r q) hq)
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.zero_mulVec] at h
  simp only [Matrix.mulVec_neg, Matrix.mulVec_mulVec]
  ext a
  have ha := congrFun h a
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at ha ⊢
  linarith

end HorizontalLift

end HorizontalLiftCalculus

noncomputable section ParallelEquation
open Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
open SmoothManifolds.ModelData
namespace LocalParallel

/-- Horizontal Frobenius graphs yield actual prescribed vector solutions.
This bridge separates geometric integration from the explicit lift computation. -/
theorem local_parallel_solution_of_commuting_lifts
    {n r : ℕ} (Γ : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℝ)
    (O : Set (Euclidean n)) (hO : IsOpen O)
    (hΓ : ∀ i, ContDiffOn ℝ ∞ (fun x => Γ x i) O)
    (hcomm : ∀ i j q, q ∈ (P202.Geometry.FlatLocalEuclidean.HorizontalLift.baseProjection n r) ⁻¹' O →
      fderiv ℝ (P202.Geometry.FlatLocalEuclidean.HorizontalLift.horizontalLift (fun i x => Γ x i) j) q
          (P202.Geometry.FlatLocalEuclidean.HorizontalLift.horizontalLift (fun i x => Γ x i) i q) =
        fderiv ℝ (P202.Geometry.FlatLocalEuclidean.HorizontalLift.horizontalLift (fun i x => Γ x i) i) q
          (P202.Geometry.FlatLocalEuclidean.HorizontalLift.horizontalLift (fun i x => Γ x i) j q))
    (x₀ : Euclidean n) (hx₀ : x₀ ∈ O) (z₀ : Euclidean r) :
    ∃ (W : Set (Euclidean n)) (f : Euclidean n → Euclidean r),
      IsOpen W ∧ x₀ ∈ W ∧ W ⊆ O ∧ ContDiffOn ℝ ∞ f W ∧ f x₀ = z₀ ∧
      ∀ x ∈ W, ∀ i : Fin n,
        fderiv ℝ f x (Pi.single i 1) = -(Γ x i) *ᵥ f x := by
  let P := P202.Geometry.FlatLocalEuclidean.HorizontalLift.baseProjection n r
  let Z := P202.Geometry.FlatLocalEuclidean.HorizontalLift.fiberProjection n r
  let v := P202.Geometry.FlatLocalEuclidean.HorizontalLift.horizontalLift (fun i x => Γ x i)
  let A := P ⁻¹' O
  have hA : IsOpen A := hO.preimage P.continuous
  let p := Fin.append x₀ z₀
  have hPp : P p = x₀ := P202.Geometry.FlatLocalEuclidean.HorizontalLift.baseProjection_append _ _
  have hp : p ∈ A := by change P p ∈ O; rwa [hPp]
  obtain ⟨W,G,hW,hpW,hG,hGp,hGA,hPG,hGd⟩ :=
    P202.Geometry.FlatLocalEuclidean.Horizontal.commuting_graph (Nat.le_add_right n r) A hA p hp v
      (P202.Geometry.FlatLocalEuclidean.HorizontalLift.horizontalLift_smooth (fun i x => Γ x i) O hΓ)
      hcomm (fun i q _ => P202.Geometry.FlatLocalEuclidean.HorizontalLift.baseProjection_horizontalLift _ i q)
  change P p ∈ W at hpW
  rw [hPp] at hpW
  have hG0 : G x₀ = p := by
    change G (P p) = p at hGp
    rwa [hPp] at hGp
  have hWO : W ⊆ O := by
    intro x hx
    have hm : P (G x) ∈ O := hGA hx
    have heq : P (G x) = x := hPG x hx
    rwa [heq] at hm
  let f : Euclidean n → Euclidean r := Z ∘ G
  have hf : ContDiffOn ℝ ∞ f W :=
    Z.contDiff.contDiffOn.comp hG (fun _ _ => mem_univ _)
  have hf0 : f x₀ = z₀ := by
    change Z (G x₀) = z₀
    rw [hG0]
    exact P202.Geometry.FlatLocalEuclidean.HorizontalLift.fiberProjection_append _ _
  refine ⟨W,f,hW,hpW,hWO,hf,hf0,?_⟩
  intro x hx i
  have hdG := ((hG.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hdf := (Z.hasFDerivAt.comp x hdG).fderiv
  rw [hdf,ContinuousLinearMap.comp_apply,hGd x hx i]
  change P202.Geometry.FlatLocalEuclidean.HorizontalLift.fiberProjection n r
    (P202.Geometry.FlatLocalEuclidean.HorizontalLift.horizontalLift (fun i x => Γ x i) i (G x)) = _
  rw [P202.Geometry.FlatLocalEuclidean.HorizontalLift.fiberProjection_horizontalLift]
  have heq : P (G x) = x := hPG x hx
  change -(Γ (P (G x)) i *ᵥ f x) = _
  rw [heq,Matrix.neg_mulVec]

/-- Local integrability of a smooth flat matrix connection, for any prescribed
fiber vector, in arbitrary base and fiber dimensions including zero. -/
theorem local_parallel_solution
    {n r : ℕ} (Γ : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℝ)
    (O : Set (Euclidean n)) (hO : IsOpen O)
    (hΓ : ∀ i, ContDiffOn ℝ ∞ (fun x => Γ x i) O)
    (hMC : ∀ i j x, x ∈ O →
      fderiv ℝ (fun y => Γ y j) x (Pi.single i 1) -
        fderiv ℝ (fun y => Γ y i) x (Pi.single j 1) +
        Γ x i * Γ x j - Γ x j * Γ x i = 0)
    (x₀ : Euclidean n) (hx₀ : x₀ ∈ O) (z₀ : Euclidean r) :
    ∃ (W : Set (Euclidean n)) (f : Euclidean n → Euclidean r),
      IsOpen W ∧ x₀ ∈ W ∧ W ⊆ O ∧ ContDiffOn ℝ ∞ f W ∧ f x₀ = z₀ ∧
      ∀ x ∈ W, ∀ i : Fin n,
        fderiv ℝ f x (Pi.single i 1) = -(Γ x i) *ᵥ f x := by
  apply local_parallel_solution_of_commuting_lifts Γ O hO hΓ
    (fun i j q hq => P202.Geometry.FlatLocalEuclidean.HorizontalLift.horizontalLift_commute
      (fun i x => Γ x i) O hO hΓ hMC i j q hq) x₀ hx₀ z₀

end LocalParallel

end ParallelEquation

/-- The zero-dimensional tangent fiber contains only zero, as follows from
its actual chart-coordinate equivalence. -/
theorem tangent_eq_zero_dim_zero {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 .euclidean M) (p : M) (v : TangentSpace S p) : v = 0 := by
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  exact ((tangentStructure S).fiberCoordinates.equiv c hc p hp).injective
    (Subsingleton.elim _ _)

/-- Every chart in dimension zero is an isometric chart. -/
theorem isEuclideanChart_dim_zero {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 .euclidean M} (g : RiemannianMetric S)
    (c : ModelChart 0 .euclidean M) (hc : c ∈ S.smoothStructure.val) :
    IsEuclideanChart g c := by
  refine ⟨hc, ?_⟩
  intro p hp v w
  rw [tangent_eq_zero_dim_zero S p v]
  simp only [pairing, map_zero, LinearMap.zero_apply, Finset.univ_eq_empty,
    Finset.sum_empty]

theorem zero_dimensional : P202Specs.Geometry.FlatLocalEuclidean.zero_dimensionalType.{u} := by
  intro M _ S g R U _hU
  constructor
  · intro p hp v w z
    rw [tangent_eq_zero_dim_zero S p v]
    simp only [map_zero, LinearMap.zero_apply]
  · intro p hp
    obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
    refine ⟨c, hpc, ?_, isEuclideanChart_dim_zero g c hc⟩
    intro q hq
    have hqp : q = p := c.injOn hq hpc (Subsingleton.elim _ _)
    exact hqp ▸ hp

/-- Vanishing curvature supplies a local parallel extension of every
initial tangent vector, hence an actual Euclidean isometric chart. -/
theorem locallyEuclidean_of_flat
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (U : Set M) (hU : IsOpen U) (hflat : FlatOn R U) : LocallyEuclideanOn g U := by
  intro p hpU
  obtain ⟨c,hc,hpc⟩ := S.smoothStructure.property.1.1 p
  let c' := c.restr U
  have hc' : c' ∈ S.smoothStructure.val :=
    SmoothManifolds.Frobenius.chart_restr_mem S c hc U
  have hsource : c'.source = c.source ∩ U := c.restr_source' U hU
  let d : TangentIndex S := ⟨c',hc'⟩
  have hpd : p ∈ d.val.source := hsource ▸ ⟨hpc,hpU⟩
  have hpB : p ∈ (tangentBundle S).baseSet d := by
    rwa [(tangentRealization S).baseSet d]
  have hflatd : FlatOn R d.val.source := by
    intro q hq
    exact hflat q ((hsource ▸ hq).2)
  let O := euclideanChartDomain d
  have hO : IsOpen O := euclideanChartDomain_open d
  have hpO : (d.val p).val ∈ O := d.val.map_source hpd
  let Γ : Euclidean n → Fin n → Matrix (Fin n) (Fin n) ℝ :=
    fun x i => euclideanChristoffel C d i x
  apply exists_euclidean_chart_of_parallel_extensions g C hC U hU p hpU
  intro v
  obtain ⟨W,f,hW,hpW,hWO,hf,hinit,hPDE⟩ := LocalParallel.local_parallel_solution
    Γ O hO (fun i => euclideanChristoffel_contDiffOn C d i)
    (fun i j x hx => euclideanChristoffel_maurer_cartan C R hR d hflatd x hx i j)
    (d.val p).val hpO ((tangentBundle S).fiberCoordinates d p hpB v)
  apply parallel_extension_of_coordinate_solution C d U hU p hpU hpB v W hW hpW f hf hinit
  intro q hq hqW i row
  have h := congrFun (hPDE (d.val q).val hqW i) row
  change fderiv ℝ f (d.val q).val (Pi.single i 1) row =
    (-(euclideanChristoffel C d i (d.val q).val) *ᵥ f (d.val q).val) row at h
  rw [Matrix.neg_mulVec] at h
  change fderiv ℝ f (d.val q).val (Pi.single i 1) row =
    -(∑ k, euclideanChristoffel C d i (d.val q).val row k * f (d.val q).val k) at h
  simp_rw [euclideanChristoffel_entry_at C d ⟨q,hq⟩] at h
  linarith

/-- Theorem 7.3, with the complete original scope, including dimension zero. -/
theorem flat_iff_locallyEuclidean :
    P202Specs.Geometry.FlatLocalEuclidean.flat_iff_locallyEuclideanType.{u} := by
  intro n M _ S g C hC R hR U hU
  exact ⟨locallyEuclidean_of_flat g C hC R hR U hU,
    flat_of_locallyEuclidean g C hC R hR U⟩

end P202.Geometry.FlatLocalEuclidean
