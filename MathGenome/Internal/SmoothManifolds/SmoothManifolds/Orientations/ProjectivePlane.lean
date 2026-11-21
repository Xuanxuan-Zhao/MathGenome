import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.ProjectivePlane
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.ProductsAndSigns
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.StandardCoverings
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.FinCases

/-! The projective plane example following M09.02, paper.tex 1738.

The projective argument uses the literal ratio atlas: its two connected charts
have overlap transition determinants of opposite signs. The sphere argument
constructs the actual radial determinant functional on intrinsic derivations,
checks smoothness by the hemisphere coordinate frames, and uses the actual
antipodal differential. The radial curve crosses the unit ball outwards.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Topology

namespace SmoothManifolds.ProjectiveOrientations
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  OrientationData OrientationProductData SphereTorusData ProjectiveData
  ProjectiveOrientationData BoundaryOrientationData Set Filter

theorem projectiveChart_mem
    (P : SmoothManifold 2 .euclidean (RealProjectiveSpace 2))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas 2))
    (i : Fin 3) : Projective.projectiveChart i ∈ P.smoothStructure.val := by
  rw [hP]
  exact subset_maximalExtension (Projective.projectiveAtlas_isContDiffAtlas 2)
    ⟨i, Projective.projectiveChart_spec i⟩

theorem projective_chart_sign_constant
    (P : SmoothManifold 2 .euclidean (RealProjectiveSpace 2))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas 2))
    (s : SignedCharts P) (i : Fin 3)
    (p q : (Projective.projectiveChart i).source) :
    s.sign (Projective.projectiveChart i) (projectiveChart_mem P hP i) p =
    s.sign (Projective.projectiveChart i) (projectiveChart_mem P hP i) q := by
  let c := Projective.projectiveChart i
  letI : ConnectedSpace c.target := by
    change ConnectedSpace (↥(Set.univ : Set (ModelSpace 2 .euclidean)))
    letI : ConnectedSpace (ModelSpace 2 .euclidean) :=
      (Homeomorph.Set.univ (Euclidean 2)).connectedSpace_iff.mpr inferInstance
    exact (Homeomorph.Set.univ (ModelSpace 2 .euclidean)).connectedSpace_iff.mpr inferInstance
  letI : ConnectedSpace c.source :=
    c.toHomeomorphSourceTarget.connectedSpace_iff.mpr inferInstance
  exact congrFun ((s.locallyConstant c _).eq_const q) p

def swapRatio (x : Euclidean 2) : Euclidean 2 := ![(x 0)⁻¹, x 1 * (x 0)⁻¹]
def ratioDerivative (x : Euclidean 2) : Euclidean 2 →L[ℝ] Euclidean 2 :=
  ContinuousLinearMap.pi ![-((x 0)^2)⁻¹ • ContinuousLinearMap.proj 0,
    x 1 • (-((x 0)^2)⁻¹ • ContinuousLinearMap.proj 0) +
      (x 0)⁻¹ • ContinuousLinearMap.proj 1]

theorem swapRatio_hasFDerivAt (x : Euclidean 2) (hx : x 0 ≠ 0) :
    HasFDerivAt swapRatio (ratioDerivative x) x := by
  have hi := (hasDerivAt_inv (𝕜 := ℝ) hx).comp_hasFDerivAt x
    (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hi
  · exact (hasFDerivAt_apply (𝕜 := ℝ) 1 x).mul hi

theorem ratioDerivative_det (a : ℝ) :
    (ratioDerivative ![a, 0]).toLinearMap.det = -(a^2)⁻¹ * a⁻¹ := by
  rw [← LinearMap.det_toMatrix']
  simp [LinearMap.toMatrix', Matrix.det_fin_two, ratioDerivative]

theorem projectiveTransition_zero_one :
    projectiveTransition (0 : Fin 3) 1 = swapRatio := by
  funext x i
  fin_cases i
  · change 1 / x 0 = (x 0)⁻¹
    exact one_div _
  · change x 1 / x 0 = x 1 * (x 0)⁻¹
    exact div_eq_mul_inv _ _

theorem inverse_zero_mem_one (a : ℝ) (ha : a ≠ 0) :
    projectiveInverse (0 : Fin 3) ![a, 0] ∈ projectiveLocus 1 := by
  apply (Projective.projection_mem_locus _ _).mpr
  simp [normalizedRepresentative, insertOne, Fin.insertNth,
    ha, (Projective.sqrt_normalizer_pos (![a, 0] : Euclidean 2)).ne']

theorem projective_transition_det
    (P : SmoothManifold 2 .euclidean (RealProjectiveSpace 2))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas 2))
    (K : FiberCoordinates P) (a : ℝ) (ha : a ≠ 0) :
    transitionDeterminant K (Projective.projectiveChart 0) (Projective.projectiveChart 1)
      (projectiveChart_mem P hP 0) (projectiveChart_mem P hP 1)
      ⟨projectiveInverse 0 ![a, 0], Projective.inverse_mem_locus 0 _, inverse_zero_mem_one a ha⟩ =
      -(a^2)⁻¹ * a⁻¹ := by
  rw [OrientationResults.transition_jacobian P K _ _ _ _ _
    (projectiveOverlap 0 1) (projectiveTransition 0 1)
    (Projective.isOpen_overlap 0 1) ?_ (Projective.contDiffOn_transition 0 1) ?_]
  · change (fderiv ℝ (projectiveTransition (0 : Fin 3) 1)
      (projectiveRatios 0 (projectiveInverse 0 ![a, 0]))).toLinearMap.det = _
    rw [Projective.ratios_inverse, projectiveTransition_zero_one,
      (swapRatio_hasFDerivAt ![a, 0] ha).fderiv, ratioDerivative_det]
  · change projectiveRatios 0 (projectiveInverse 0 ![a, 0]) ∈ projectiveOverlap 0 1
    exact Projective.overlap_ratios 0 1 _ (Projective.inverse_mem_locus 0 _)
      (inverse_zero_mem_one a ha)
  · filter_upwards [(Projective.isOpen_locus (0 : Fin 3)).mem_nhds
      (Projective.inverse_mem_locus 0 (![a, 0] : Euclidean 2))] with q hq
    exact (Projective.transition_ratios 0 1 q hq).symm

theorem projective_no_orientation
    (P : SmoothManifold 2 .euclidean (RealProjectiveSpace 2))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas 2)) :
    ¬ Nonempty (Orientation P) := by
  rintro ⟨o⟩
  obtain ⟨s, hs, _⟩ := (OrientationResults.signed_charts P o.val).mp o.property
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists P
  let p := projectiveInverse (0 : Fin 3) ![1, 0]
  let q := projectiveInverse (0 : Fin 3) ![-1, 0]
  have hp0 : p ∈ (Projective.projectiveChart 0).source := Projective.inverse_mem_locus 0 _
  have hq0 : q ∈ (Projective.projectiveChart 0).source := Projective.inverse_mem_locus 0 _
  have hp1 : p ∈ (Projective.projectiveChart 1).source := inverse_zero_mem_one 1 (by norm_num)
  have hq1 : q ∈ (Projective.projectiveChart 1).source := inverse_zero_mem_one (-1) (by norm_num)
  have hp := s.compatible K _ _ (projectiveChart_mem P hP 0) (projectiveChart_mem P hP 1)
    ⟨p, hp0, hp1⟩
  have hq := s.compatible K _ _ (projectiveChart_mem P hP 0) (projectiveChart_mem P hP 1)
    ⟨q, hq0, hq1⟩
  rw [projective_transition_det P hP K 1 (by norm_num)] at hp
  rw [projective_transition_det P hP K (-1) (by norm_num)] at hq
  have h0 := projective_chart_sign_constant P hP s 0 ⟨p, hp0⟩ ⟨q, hq0⟩
  have h1 := projective_chart_sign_constant P hP s 1 ⟨p, hp1⟩ ⟨q, hq1⟩
  rw [h0, h1] at hp
  norm_num at hp hq
  have hn := OrientationResults.signValue_ne_zero
    (s.sign (Projective.projectiveChart 0) (projectiveChart_mem P hP 0) ⟨q, hq0⟩)
  apply hn
  linarith

def sphereEuclideanHomeomorph (n : ℕ) :
    Sphere n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 where
  toFun p := ⟨(EuclideanSpace.equiv (Fin (n+1)) ℝ).symm p.val, by
    rw [Metric.mem_sphere, dist_zero_right]
    have h : ‖(EuclideanSpace.equiv (Fin (n+1)) ℝ).symm p.val‖ ^ 2 = 1 := by
      simpa [EuclideanSpace.real_norm_sq_eq, squareSum] using p.property
    nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin (n+1)) ℝ).symm p.val)]⟩
  invFun p := ⟨EuclideanSpace.equiv (Fin (n+1)) ℝ p.val, by
    have h : ‖p.val‖ = 1 := by simpa using p.property
    change ∑ i, p.val.ofLp i ^ 2 = 1
    rw [← EuclideanSpace.real_norm_sq_eq, h]
    norm_num⟩
  left_inv p := by apply Subtype.ext; exact (EuclideanSpace.equiv _ ℝ).apply_symm_apply p.val
  right_inv p := by apply Subtype.ext; exact (EuclideanSpace.equiv _ ℝ).symm_apply_apply p.val
  continuous_toFun := ((EuclideanSpace.equiv _ ℝ).symm.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((EuclideanSpace.equiv _ ℝ).continuous.comp continuous_subtype_val).subtype_mk _

instance sphereTwoConnected : ConnectedSpace (Sphere 2) := by
  have hr : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp [← Module.finrank_eq_rank]
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere hr 0 (by norm_num : (0:ℝ) ≤ 1))
  exact (sphereEuclideanHomeomorph 2).connectedSpace_iff.mpr inferInstance

theorem hemisphereChart_mem
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (i : Fin 3) (s : Bool) : SphereTorus.hemisphereChart i s ∈ S.smoothStructure.val := by
  rw [hS]
  exact subset_maximalExtension (SphereTorus.hemisphereAtlas_isContDiffAtlas 2)
    ⟨i, s, SphereTorus.hemisphereChart_spec i s⟩

theorem ambient_germ_exists
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (p : Sphere 2) (j : Fin 3) :
    ∃ g : SmoothGerm S p, g.val = Germ.ofFun (fun q : Sphere 2 => q.val j) := by
  obtain ⟨i, s, hp⟩ := SphereTorus.hemisphere_cover 2 p
  let c := SphereTorus.hemisphereChart i s
  have hc := hemisphereChart_mem S hS i s
  let g := germOfChart S p c hc hp (fun y => insertRoot i s y j)
    ⟨{y | squareSum y < 1},
      isOpen_lt (SphereTorus.continuous_squareSum 2) continuous_const,
      SphereTorus.hemisphere_omit_mem i s p hp,
      contDiffOn_pi.mp (SphereTorus.contDiffOn_insertRoot i s) j⟩
  refine ⟨g, ?_⟩
  apply Germ.coe_eq.mpr
  filter_upwards [c.open_source.mem_nhds hp] with q hq
  exact congrFun (SphereTorus.insertRoot_omit i s q hq) j

def ambientGerm
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (p : Sphere 2) (j : Fin 3) : SmoothGerm S p :=
  (ambient_germ_exists S hS p j).choose

theorem ambientGerm_value
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (p : Sphere 2) (j : Fin 3) :
    (ambientGerm S hS p j).val = Germ.ofFun (fun q : Sphere 2 => q.val j) :=
  (ambient_germ_exists S hS p j).choose_spec

def ambientDerivative
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (p : Sphere 2) : TangentSpace S p →ₗ[ℝ] Euclidean 3 where
  toFun v j := v.val (ambientGerm S hS p j)
  map_add' v w := by funext j; rfl
  map_smul' r v := by funext j; rfl

theorem ambientDerivative_spec
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (p : Sphere 2) : IsAmbientDifferential S p (ambientDerivative S hS p) := by
  intro j
  exact ⟨ambientGerm S hS p j, ambientGerm_value S hS p j, fun _ => rfl⟩

theorem ambient_differential_unique
    (S : SmoothManifold 2 .euclidean (Sphere 2)) (p : Sphere 2)
    (L K : TangentSpace S p →ₗ[ℝ] Euclidean 3)
    (hL : IsAmbientDifferential S p L) (hK : IsAmbientDifferential S p K) : L = K := by
  ext v j
  obtain ⟨g, hg, hv⟩ := hL j
  obtain ⟨k, hk, hw⟩ := hK j
  have h : g = k := Subtype.ext (hg.trans hk.symm)
  rw [hv, hw, h]

theorem ambient_differential_normal
    (S : SmoothManifold 2 .euclidean (Sphere 2)) (p : Sphere 2)
    (L : TangentSpace S p →ₗ[ℝ] Euclidean 3) (hL : IsAmbientDifferential S p L)
    (v : TangentSpace S p) : ∑ j, p.val j * L v j = 0 := by
  choose g hg hv using hL
  have hsum : ∑ j, g j * g j = (1 : SmoothGerm S p) := by
    apply Subtype.ext
    simp only [Fin.sum_univ_three, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_one, hg]
    change Germ.ofFun (fun q : Sphere 2 =>
      q.val 0 * q.val 0 + q.val 1 * q.val 1 + q.val 2 * q.val 2) =
        Germ.ofFun (fun _ => (1 : ℝ))
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun q => by
      have h := q.property
      change (∑ j : Fin 3, q.val j ^ 2) = 1 at h
      rw [Fin.sum_univ_three] at h
      simpa only [pow_two] using h)

  have hz := congrArg (fun f : SmoothGerm S p => v.val f) hsum
  rw [map_sum] at hz
  have h1 : v.val (1 : SmoothGerm S p) = 0 := by
    have h := derivation_kills_constants (germEvaluation S p) v 1
    simpa using h
  have hd (j : Fin 3) := v.property (g j) (g j)
  simp_rw [hd, h1] at hz
  have he (j : Fin 3) : germEvaluation S p (g j) = p.val j := by
    change (g j).val.value = p.val j
    rw [hg]
    rfl
  simp_rw [he, ← hv] at hz
  have htwice : (∑ j, (p.val j * L v j + p.val j * L v j)) =
      2 * (∑ j, p.val j * L v j) := by
    rw [Finset.sum_add_distrib]
    ring
  rw [htwice] at hz
  linarith

theorem ambient_differential_coordinates
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (K : FiberCoordinates S) (i : Fin 3) (s : Bool)
    (hc : SphereTorus.hemisphereChart i s ∈ S.smoothStructure.val)
    (p : (SphereTorus.hemisphereChart i s).source)
    (L : TangentSpace S p.val →ₗ[ℝ] Euclidean 3)
    (hL : IsAmbientDifferential S p.val L) (v : TangentSpace S p.val) (j : Fin 2) :
    L v (i.succAbove j) = K.equiv _ hc p.val p.property v j := by
  obtain ⟨g, hg, hv⟩ := hL (i.succAbove j)
  obtain ⟨k, hk, he⟩ := K.isCoordinates _ hc p.val p.property
  have h : g = k j := by
    apply Subtype.ext
    exact hg.trans (hk j).symm
  rw [hv, h, he]

theorem normalWedge_decomposable {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] Euclidean 3) (p : Euclidean 3) (v : Fin 2 → V) :
    normalWedge L p (exteriorPower.ιMulti ℝ 2 v) =
      exteriorPower.ιMulti ℝ 3 (Fin.append (fun _ : Fin 1 => p) (fun j => L (v j))) := by
  simp only [normalWedge, exteriorPower.map_apply_ιMulti]
  apply Subtype.ext
  exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _

theorem ambientDeterminant_decomposable (v : Fin 3 → Euclidean 3) :
    ambientDeterminant (exteriorPower.ιMulti ℝ 3 v) =
      (Matrix.of fun i j => v i j).det := by
  rw [ambientDeterminant, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact Pi.basisFun_det_apply v


theorem radial_frame_coefficient
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (K : FiberCoordinates S) (i : Fin 3) (s : Bool)
    (hc : SphereTorus.hemisphereChart i s ∈ S.smoothStructure.val)
    (p : (SphereTorus.hemisphereChart i s).source)
    (L : TangentSpace S p.val →ₗ[ℝ] Euclidean 3)
    (hL : IsAmbientDifferential S p.val L) :
    ambientDeterminant (normalWedge L p.val.val
      (coordinateVector K (SphereTorus.hemisphereChart i s) hc p)) * p.val.val i =
      (-1 : ℝ)^i.val := by
  let E := K.equiv (SphereTorus.hemisphereChart i s) hc p.val p.property
  let u := E.symm ((Pi.basisFun ℝ (Fin 2)) 0)
  let w := E.symm ((Pi.basisFun ℝ (Fin 2)) 1)
  have hu (j : Fin 2) : L u (i.succAbove j) = (Pi.basisFun ℝ (Fin 2)) 0 j := by
    rw [ambient_differential_coordinates S K i s hc p L hL]
    exact congrFun (E.apply_symm_apply _) j
  have hw (j : Fin 2) : L w (i.succAbove j) = (Pi.basisFun ℝ (Fin 2)) 1 j := by
    rw [ambient_differential_coordinates S K i s hc p L hL]
    exact congrFun (E.apply_symm_apply _) j
  have hnu := ambient_differential_normal S p.val L hL u
  have hnw := ambient_differential_normal S p.val L hL w
  have hp := p.val.property
  change (∑ j : Fin 3, p.val.val j ^ 2) = 1 at hp
  rw [Fin.sum_univ_three] at hp hnu hnw
  rw [coordinateVector, normalWedge_decomposable, ambientDeterminant_decomposable]
  change (Matrix.of ![p.val.val, L u, L w]).det * p.val.val i = _
  rw [Matrix.det_fin_three]
  have hu0 := hu 0
  have hu1 := hu 1
  have hw0 := hw 0
  have hw1 := hw 1
  fin_cases i <;> norm_num [Fin.succAbove, Pi.basisFun_apply] at hu0 hu1 hw0 hw1
  all_goals simp [hu0, hu1, hw0, hw1] at hnu hnw ⊢
  · nlinarith [congrArg (fun r : ℝ => p.val.val 1 * r) hnu,
      congrArg (fun r : ℝ => p.val.val 2 * r) hnw]
  · nlinarith [congrArg (fun r : ℝ => p.val.val 0 * r) hnu,
      congrArg (fun r : ℝ => p.val.val 2 * r) hnw]
  · nlinarith [congrArg (fun r : ℝ => p.val.val 0 * r) hnu,
      congrArg (fun r : ℝ => p.val.val 1 * r) hnw]


def radialFunctional {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] Euclidean 3) (p : Euclidean 3) : (⋀[ℝ]^2 V) →ₗ[ℝ] ℝ :=
  ambientDeterminant.comp
    ((exteriorPower.wedge ℝ (Euclidean 3) 1 2 (exteriorPower.ιMulti ℝ 1 (fun _ => p))).comp
      (exteriorPower.map 2 L))

theorem radialFunctional_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] Euclidean 3) (p : Euclidean 3) (η : ⋀[ℝ]^2 V) :
    radialFunctional L p η = ambientDeterminant (normalWedge L p η) := rfl

theorem radialFunctional_ne_zero
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (p : Sphere 2) (L : TangentSpace S p →ₗ[ℝ] Euclidean 3)
    (hL : IsAmbientDifferential S p L) : radialFunctional (V := TangentSpace S p) L p.val ≠ 0 := by
  obtain ⟨i, s, hp⟩ := SphereTorus.hemisphere_cover 2 p
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  have h := radial_frame_coefficient S K i s (hemisphereChart_mem S hS i s) ⟨p, hp⟩ L hL
  intro hz
  rw [← radialFunctional_apply] at h
  rw [hz, LinearMap.zero_apply, zero_mul] at h
  exact pow_ne_zero i.val (by norm_num : (-1 : ℝ) ≠ 0) h.symm

theorem radial_positive_ray_exists
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (p : Sphere 2) : ∃! r : DeterminantRay S p, ∀ η,
      IsPositive r η ↔ 0 < radialFunctional (ambientDerivative S hS p) p.val η := by
  letI := (tangent_dimension S p).1
  exact OrientationResults.exists_unique_positive_ray (OrientationResults.determinant_finrank S p)
    _ (radialFunctional_ne_zero S hS p _ (ambientDerivative_spec S hS p))

def radialRayField
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2)) : RayField S :=
  fun p => (radial_positive_ray_exists S hS p).choose

theorem radialRayField_positive
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (p : Sphere 2) (η : DeterminantLine S p) :
    IsPositive (radialRayField S hS p) η ↔
      0 < radialFunctional (ambientDerivative S hS p) p.val η :=
  (radial_positive_ray_exists S hS p).choose_spec.1 η

def hemisphereOrientationSign (i : Fin 3) (s : Bool) : Bool :=
  if i = 1 then !s else s

theorem positive_hemisphere_sign (i : Fin 3) (s : Bool) (a x : ℝ)
    (h : a * x = (-1 : ℝ)^i.val) (hx : if s then 0 < x else x < 0) :
    0 < signValue (hemisphereOrientationSign i s) * a := by
  fin_cases i <;> cases s <;>
    norm_num [hemisphereOrientationSign, signValue] at h hx ⊢ <;> nlinarith

theorem radial_signed_frame_positive
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (K : FiberCoordinates S) (i : Fin 3) (s : Bool)
    (p : (SphereTorus.hemisphereChart i s).source) :
    IsPositive (radialRayField S hS p.val)
      (signValue (hemisphereOrientationSign i s) •
        coordinateVector K (SphereTorus.hemisphereChart i s) (hemisphereChart_mem S hS i s) p) := by
  rw [radialRayField_positive, map_smul, smul_eq_mul]
  have h := radial_frame_coefficient S K i s (hemisphereChart_mem S hS i s) p
    _ (ambientDerivative_spec S hS p.val)
  rw [← radialFunctional_apply] at h
  exact positive_hemisphere_sign i s _ _ h p.property

theorem radialRayField_continuous
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2)) :
    IsContinuousRayField (radialRayField S hS) := by
  apply OrientationProducts.isContinuousRayField_of_cover
    {c | ∃ i s, c = SphereTorus.hemisphereChart i s}
    (by rintro c ⟨i, s, rfl⟩; exact hemisphereChart_mem S hS i s)
    (by
      intro p
      obtain ⟨i, s, hp⟩ := SphereTorus.hemisphere_cover 2 p
      exact ⟨SphereTorus.hemisphereChart i s, ⟨i, s, rfl⟩, hp⟩)
  rintro K c ⟨i, s, rfl⟩
  have hr (p : (SphereTorus.hemisphereChart i s).source) :
      radialRayField S hS p.val = OrientationResults.coordinateRayEquiv K _
        (hemisphereChart_mem S hS i s) p (hemisphereOrientationSign i s) := by
    rw [OrientationResults.coordinateRayEquiv_apply]
    exact (radial_signed_frame_positive S hS K i s p).choose_spec.symm
  have hm (p : (SphereTorus.hemisphereChart i s).source) :
      Module.Ray.map (determinantCoordinates K _ (hemisphereChart_mem S hS i s) p)
        (radialRayField S hS p.val) = OrientationResults.standardRayEquiv 2 (hemisphereOrientationSign i s) := by
    rw [hr, OrientationResults.map_coordinateRayEquiv]
  convert (IsLocallyConstant.const
    (X := (SphereTorus.hemisphereChart i s).source)
    (OrientationResults.standardRayEquiv 2 (hemisphereOrientationSign i s))) using 1
  funext p
  exact hm p


theorem exists_positive_vector {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r : Module.Ray ℝ V) : ∃ v, IsPositive r v := by
  induction r using Module.Ray.ind with
  | h v hv => exact ⟨v, hv, rfl⟩

def sphereOutwardOrientation
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2)) : Orientation S :=
  ⟨radialRayField S hS, radialRayField_continuous S hS⟩

theorem sphereOutwardOrientation_spec
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2)) :
    IsOutwardSphereOrientation S (sphereOutwardOrientation S hS) := by
  refine ⟨fun p => ⟨ambientDerivative S hS p, ambientDerivative_spec S hS p⟩, ?_⟩
  intro p L hL η
  rw [ambient_differential_unique S p L _ hL (ambientDerivative_spec S hS p)]
  exact radialRayField_positive S hS p η

theorem sphere_outward_orientation_exists :
    Specs.SmoothManifolds.Orientations.ProjectivePlane.sphere_boundary_orientationType := by
  intro S hS
  refine ⟨sphereOutwardOrientation S hS, sphereOutwardOrientation_spec S hS, ?_⟩
  intro q hq
  apply Subtype.ext
  funext p
  obtain ⟨η, hη⟩ := exists_positive_vector ((sphereOutwardOrientation S hS).val p)
  apply OrientationProducts.positive_ray_eq (v := η) ?_ hη
  exact (hq.2 p _ (ambientDerivative_spec S hS p) η).mpr
    ((sphereOutwardOrientation_spec S hS).2 p _ (ambientDerivative_spec S hS p) η |>.mp hη)


/-- Along the radial curve the unit sphere is crossed from the literal closed
unit ball to its complement. This identifies the radial sign used above as
outward for the unit-ball convention. -/
theorem radial_square_sum (p : Sphere 2) (r : ℝ) : squareSum (r • p.val) = r ^ 2 := by
  unfold squareSum
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum]
  change r ^ 2 * squareSum p.val = r ^ 2
  rw [p.property, mul_one]

theorem radial_exits_unit_ball (p : Sphere 2) (t : ℝ) (ht : 0 < t) :
    1 < squareSum ((1 + t) • p.val) := by
  rw [radial_square_sum]
  nlinarith

theorem radial_enters_unit_ball (p : Sphere 2) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    squareSum ((1 - t) • p.val) < 1 := by
  rw [radial_square_sum]
  nlinarith

theorem radial_curve_velocity (p : Sphere 2) :
    HasDerivAt (fun t : ℝ => (1 + t) • p.val) p.val 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const p.val

theorem projection_antipode (p : Sphere 2) :
    projectiveProjection (antipode p) = projectiveProjection p :=
  Quotient.sound (Or.inr rfl)

def antipodalHomeomorph : Sphere 2 ≃ₜ Sphere 2 where
  toFun := antipode
  invFun := antipode
  left_inv := antipode_antipode
  right_inv := antipode_antipode
  continuous_toFun := Projective.continuous_antipode 2
  continuous_invFun := Projective.continuous_antipode 2

theorem antipodal_local_diffeomorphism
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2)) :
    IsLocalDiffeomorphism S S antipode := by
  have hc := (StandardCoverings.antipodalSmoothCovering 2 S (Projective.projectiveManifold 2)
    hS rfl).1
  have hs : IsSmoothMap S S antipode := CoveringStructure.smooth_lift S
    (Projective.projectiveManifold 2) S projectiveProjection hc projectiveProjection antipode
    hc.2.1 (Projective.continuous_antipode 2) (funext projection_antipode)
  intro p
  refine ⟨antipodalHomeomorph.toOpenPartialHomeomorph, mem_univ _, fun _ _ => rfl, ?_, ?_⟩
  · exact fun x _ => hs x
  · exact fun x _ => hs x

theorem ambient_antipodal_differential
    (S : SmoothManifold 2 .euclidean (Sphere 2)) (p : Sphere 2)
    (E : TangentSpace S p ≃ₗ[ℝ] TangentSpace S (antipode p))
    (hE : IsDifferential S S antipode p E.toLinearMap)
    (L : TangentSpace S p →ₗ[ℝ] Euclidean 3)
    (K : TangentSpace S (antipode p) →ₗ[ℝ] Euclidean 3)
    (hL : IsAmbientDifferential S p L) (hK : IsAmbientDifferential S (antipode p) K) :
    K.comp E.toLinearMap = -L := by
  ext v j
  obtain ⟨g, hg, hgv⟩ := hL j
  obtain ⟨k, hk, hkv⟩ := hK j
  have heq : Germ.ofFun ((fun q : Sphere 2 => q.val j) ∘ antipode) = (-g).val := by
    rw [Subalgebra.coe_neg, hg]
    rfl
  have h := hE v k (-g) (fun q : Sphere 2 => q.val j) hk.symm heq
  change K (E v) j = -(L v j)
  rw [hkv, hgv]
  simpa only [LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap, map_neg] using h

theorem exterior_square_map_neg {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] Euclidean 3) : exteriorPower.map 2 (-L) = exteriorPower.map 2 L := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.map 2 (-L) (exteriorPower.ιMulti ℝ 2 v) =
    exteriorPower.map 2 L (exteriorPower.ιMulti ℝ 2 v)
  simp only [exteriorPower.map_apply_ιMulti]
  change exteriorPower.ιMulti ℝ 2 (fun i => -L (v i)) =
    exteriorPower.ιMulti ℝ 2 (fun i => L (v i))
  simpa using (exteriorPower.ιMulti ℝ 2 (M := Euclidean 3)).map_smul_univ
    (fun _ => (-1 : ℝ)) (fun i => L (v i))

theorem exterior_single_neg (p : Euclidean 3) :
    exteriorPower.ιMulti ℝ 1 (fun _ : Fin 1 => -p) =
      -exteriorPower.ιMulti ℝ 1 (fun _ : Fin 1 => p) := by
  simpa using (exteriorPower.ιMulti ℝ 1 (M := Euclidean 3)).map_smul_univ
    (fun _ => (-1 : ℝ)) (fun _ => p)

theorem radialFunctional_transport {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (E : V ≃ₗ[ℝ] W) (L : V →ₗ[ℝ] Euclidean 3) (K : W →ₗ[ℝ] Euclidean 3)
    (h : K.comp E.toLinearMap = -L) (p : Euclidean 3) (η : ⋀[ℝ]^2 V) :
    radialFunctional K (-p) (determinantMap 2 E η) = -radialFunctional L p η := by
  have hmap : exteriorPower.map 2 K (determinantMap 2 E η) = exteriorPower.map 2 L η := by
    change exteriorPower.map 2 K (exteriorPower.map 2 E.toLinearMap η) = _
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, h, exterior_square_map_neg]
  change ambientDeterminant
    (exteriorPower.wedge ℝ (Euclidean 3) 1 2
      (exteriorPower.ιMulti ℝ 1 (fun _ : Fin 1 => -p))
      (exteriorPower.map 2 K (determinantMap 2 E η))) = _
  rw [hmap, exterior_single_neg, map_neg, LinearMap.neg_apply, map_neg]
  rfl

theorem radialFunctional_antipodal
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (p : Sphere 2) (E : TangentSpace S p ≃ₗ[ℝ] TangentSpace S (antipode p))
    (hE : IsDifferential S S antipode p E.toLinearMap) (η : DeterminantLine S p) :
    radialFunctional (ambientDerivative S hS (antipode p)) (antipode p).val
        (determinantMap (V := TangentSpace S p) (W := TangentSpace S (antipode p)) 2 E η) =
      -radialFunctional (ambientDerivative S hS p) p.val η := by
  have he := ambient_antipodal_differential S p E hE
    (ambientDerivative S hS p) (ambientDerivative S hS (antipode p))
    (ambientDerivative_spec S hS p) (ambientDerivative_spec S hS (antipode p))
  have h := @radialFunctional_transport (TangentSpace S p) (TangentSpace S (antipode p))
    inferInstance inferInstance inferInstance inferInstance
    E (ambientDerivative S hS p) (ambientDerivative S hS (antipode p)) he p.val η
  exact h

theorem positive_neg {V : Type*} [AddCommGroup V] [Module ℝ V]
    {r : Module.Ray ℝ V} {v : V} (h : IsPositive r v) : IsPositive (-r) (-v) := by
  obtain ⟨hv, hr⟩ := h
  exact ⟨neg_ne_zero.mpr hv, by rw [← hr, neg_rayOfNeZero]⟩

theorem antipodal_reverses_radial
    (S : SmoothManifold 2 .euclidean (Sphere 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2))
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace S (antipode p))
    (hE : ∀ p, IsDifferential S S antipode p (E p).toLinearMap) (p : Sphere 2) :
    Module.Ray.map (determinantMap 2 (E p)) (radialRayField S hS p) =
      -radialRayField S hS (antipode p) := by
  obtain ⟨η, hη⟩ := exists_positive_vector (radialRayField S hS p)
  have hηpos := (radialRayField_positive S hS p η).mp hη
  have hneg : IsPositive (radialRayField S hS (antipode p))
      (-determinantMap 2 (E p) η) := by
    rw [radialRayField_positive, map_neg, radialFunctional_antipodal S hS p (E p) (hE p), neg_neg]
    exact hηpos
  apply OrientationProducts.positive_ray_eq (OrientationProducts.positive_map hη _) ?_
  simpa only [neg_neg] using positive_neg hneg

theorem reverses_every_orientation {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] [PreconnectedSpace M]
    (S : SmoothManifold n a M) (f : M → M)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace S (f p))
    (o : Orientation S)
    (h : ∀ p, Module.Ray.map (determinantMap n (E p)) (o.val p) = -o.val (f p))
    (q : Orientation S) (p : M) :
    Module.Ray.map (determinantMap n (E p)) (q.val p) = -q.val (f p) := by
  have hc := (OrientationResults.comparison_locallyConstant o q).apply_eq_of_preconnectedSpace p (f p)
  rw [OrientationResults.comparison_reconstruct o q p,
    OrientationResults.comparison_reconstruct o q (f p), ← hc]
  cases hb : comparison o q p
  · simp only [Bool.false_eq_true, ite_false, Module.Ray.map_neg]
    exact congrArg Neg.neg (h p)
  · simp only [ite_true]
    exact h p

theorem sphere_antipodal_reverses :
    Specs.SmoothManifolds.Orientations.ProjectivePlane.antipodal_reversesType := by
  intro S hS
  refine ⟨antipodal_local_diffeomorphism S hS, ?_⟩
  intro o E hE p
  apply reverses_every_orientation S antipode E (sphereOutwardOrientation S hS) ?_ o p
  intro q
  exact antipodal_reverses_radial S hS E hE q

/-- The standard sphere has its unique outward-first boundary orientation. -/
theorem sphere_boundary_orientation :
    Specs.SmoothManifolds.Orientations.ProjectivePlane.sphere_boundary_orientationType :=
  sphere_outward_orientation_exists

/-- The antipodal differential reverses every orientation of the standard sphere. -/
theorem antipodal_reverses :
    Specs.SmoothManifolds.Orientations.ProjectivePlane.antipodal_reversesType :=
  sphere_antipodal_reverses

/-- The standard real projective plane is nonorientable. -/
theorem projective_nonorientable :
    Specs.SmoothManifolds.Orientations.ProjectivePlane.projective_nonorientableType :=
  projective_no_orientation

end SmoothManifolds.ProjectiveOrientations
