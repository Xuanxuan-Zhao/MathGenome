import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.TerminalConjugacyExample
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConstantCurvaturePolar
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CompleteExponentialMinimizers

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ModelPolarDomains
/-! Conditional derivation of the round-sphere endpoint example.
Only the ten explicitly listed model-domain statements remain parameters.
The unproved model-domain implementation is not imported. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.TerminalConjugacyExample
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.SpaceFormData P202.MetricData
  P202.ConnectionData P202.CurveConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.CurveData P202.CurvatureData P202.JacobiData
  P202.ExponentialData P202.ExponentialJacobiData P202.ConstantCurvaturePolarData
  P202.ModelPolarData P202.TerminalConjugacyData
open Set
universe u

/-- In dimension at least two every tangent vector has a nonzero normal. -/
lemma exists_nonzero_normal {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (hn : 2 ≤ n) (p : M) (v : TangentSpace S p) :
    ∃ w : TangentSpace S p, w ≠ 0 ∧ pairing g p w v = 0 := by
  classical
  let f : TangentSpace S p →ₗ[ℝ] ℝ := (pairing g p).flip v
  by_contra h
  have hf : Function.Injective f := by
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hh : pairing g p (x - y) v = 0 := by
      rw [LinearMap.BilinForm.sub_left (B₁ := pairing g p) x y v]
      change f x - f y = 0
      rw [hxy, sub_self]
    exact h ⟨x - y, hne, hh⟩
  let _ := (SmoothManifolds.tangent_dimension S p).1
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  rw [(SmoothManifolds.tangent_dimension S p).2] at hd
  norm_num at hd
  omega

lemma spherical_scalar (a : ℝ) (ha : 0 < a) (t : ℝ) :
    s ((a ^ 2)⁻¹) t = a * Real.sin (t / a) := by
  have hk : 0 < (a ^ 2)⁻¹ := inv_pos.mpr (pow_pos ha 2)
  simp only [s, ite_eq_left hk, Real.sqrt_inv, Real.sqrt_sq ha.le]
  rw [inv_mul_eq_div, div_inv_eq_mul, mul_comm]

/-- Every global unit spherical geodesic has the stated formula and speed. -/
lemma semicircle_formula {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) (hB : B.Conclusion)
    (p : Sphere n a) (v : TangentSpace B.manifold p)
    (hv : tangentNorm B.metric p v = 1)
    (q : ℝ → Phase B.manifold)
    (hq : IsMaximalThrough B.manifold B.connection ⟨p,v⟩
      D13Unified.OpenTimeInterval.whole q) :
    ∀ t, (q t).1.val = greatCircle a p.val (B.ambientVector p v) t ∧
      tangentNorm B.metric (q t).1 (q t).2 = 1 := by
  obtain ⟨r, hr, hformula⟩ := hB.2.2.2.2.2 p v hv
  have heq := (hq.2.2.2 D13Unified.OpenTimeInterval.whole r
    hr.1 hr.2.1 hr.2.2.1).2
  intro t
  rw [heq (mem_univ t)]
  exact ⟨(hformula t).1, (hformula t).2.2⟩

lemma semicircle_jacobi {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a)
    {A : EuclideanModel (n + 1)} (B : SphericalModel n a A) (hB : B.Conclusion)
    (q : ℝ → Phase B.manifold)
    (hq : IsGeodesicOn B.manifold B.connection Set.univ q)
    (hunit : ∀ t, tangentNorm B.metric (q t).1 (q t).2 = 1) :
    ∃ R : CurvatureTensor B.manifold, RepresentsCurvature B.connection R ∧
    ∃ w : TangentSpace B.manifold (q 0).1,
      w ≠ 0 ∧ pairing B.metric (q 0).1 w (q 0).2 = 0 ∧
      let J := fun t => (a * Real.sin (t / a)) •
        parallel B.connection D13Unified.OpenTimeInterval.whole q w t
      IsJacobiField B.connection R Set.univ q J ∧ J 0 = 0 ∧ J (Real.pi * a) = 0 ∧
      HasCovariantDerivativeAt B.connection (fun t => (q t).1) J 0 w ∧
      (∀ t, pairing B.metric (q t).1 (J t) (q t).2 = 0) ∧
      J (Real.pi * a / 2) ≠ 0 ∧
      ConjugateAlong B.manifold B.connection R D13Unified.OpenTimeInterval.whole q
        ⟨0, Set.mem_univ _⟩ ⟨Real.pi * a, Set.mem_univ _⟩ := by
  obtain ⟨R, hR, hcurv⟩ := hB.2.2.2.1
  obtain ⟨w, hw, horth⟩ := exists_nonzero_normal B.manifold B.metric hn (q 0).1 (q 0).2
  have hpair : ∀ t ∈ (D13Unified.OpenTimeInterval.whole).carrier,
      pairing B.metric (q t).1 (q t).2 (q t).2 = 1 := by
    intro t _
    have hh := SmoothMetrics.tangentNorm_sq B.metric (q t).1 (q t).2
    rw [hunit t] at hh
    simpa using hh.symm
  have hJ := ConstantCurvaturePolar.normal_jacobi B.manifold B.metric B.connection
    B.leviCivita R hR ((a ^ 2)⁻¹) hcurv D13Unified.OpenTimeInterval.whole q hq
    (mem_univ 0) hpair w horth
  simp only [spherical_scalar a ha] at hJ
  let J := fun t => (a * Real.sin (t / a)) •
    parallel B.connection D13Unified.OpenTimeInterval.whole q w t
  change IsJacobiField B.connection R Set.univ q J ∧ _ at hJ
  have hend : J (Real.pi * a) = 0 := by
    simp [J, mul_div_cancel_right₀ _ ha.ne']
  have hP := ConstantCurvaturePolar.parallel_properties B.connection
    D13Unified.OpenTimeInterval.whole q hq (mem_univ 0) w
  have hPne : parallel B.connection D13Unified.OpenTimeInterval.whole q w
      (Real.pi * a / 2) ≠ 0 := by
    intro hz
    have hh := ConstantCurvaturePolar.pairing_constant B.metric B.connection
      B.leviCivita D13Unified.OpenTimeInterval.whole q
      (parallel B.connection D13Unified.OpenTimeInterval.whole q w)
      (parallel B.connection D13Unified.OpenTimeInterval.whole q w)
      hP.2 hP.2 (mem_univ 0) (Real.pi * a / 2) (mem_univ _)
    rw [hz, hP.1] at hh
    have hp := B.metric.positive (q 0).1 w hw
    change 0 < pairing B.metric (q 0).1 w w at hp
    simp only [pairing, map_zero] at hh
    change 0 = pairing B.metric (q 0).1 w w at hh
    exact (ne_of_gt hp) hh.symm
  have hmid : J (Real.pi * a / 2) ≠ 0 := by
    have ht : (Real.pi * a / 2) / a = Real.pi / 2 := by field_simp
    simpa [J, ht, Real.sin_pi_div_two] using smul_ne_zero ha.ne' hPne
  refine ⟨R, hR, w, hw, horth, hJ.1, hJ.2.1, hend, hJ.2.2.1,
    (fun t => hJ.2.2.2.1 t (mem_univ t)), hmid, ?_⟩
  refine ⟨fun t => J t.val, ?_, ?_⟩
  · exact ⟨⟨J, hJ.1, fun _ => rfl⟩, hJ.2.1, hend⟩
  · intro hz
    apply hmid
    exact congrFun hz ⟨Real.pi * a / 2, mem_univ _⟩

/-- The premise order is frozen by the conditional-proof contract. -/
theorem terminal_conjugacy_conditional :
    P202Specs.Geometry.ModelPolarDomains.euclideanDistanceType →
    P202Specs.Geometry.ModelPolarDomains.euclideanFormulaType →
    P202Specs.Geometry.ModelPolarDomains.euclideanType →
    P202Specs.Geometry.ModelPolarDomains.halfSpaceHomogeneityType →
    P202Specs.Geometry.ModelPolarDomains.hyperbolicType →
    P202Specs.Geometry.ModelPolarDomains.modelPolarDomainsType →
    P202Specs.Geometry.ModelPolarDomains.modelsExistType →
    P202Specs.Geometry.ModelPolarDomains.sphericalCutTimeType →
    P202Specs.Geometry.ModelPolarDomains.sphericalFormulaType →
    P202Specs.Geometry.ModelPolarDomains.sphericalType →
    P202Specs.Geometry.TerminalConjugacyExample.terminal_conjugacyType := by
  intro _hED _hEF _hEG _hHH _hHG _hAll _hExist _hCut _hSF hSphere
  intro n hn a ha A B hB p v hv q hq
  have hformula := semicircle_formula B hB p v hv q hq
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists B.manifold B.connection
  have hfull : (F.interval ⟨p,v⟩).carrier = univ := by
    exact Set.Subset.antisymm (subset_univ _)
      ((hF ⟨p,v⟩).2.2.2 D13Unified.OpenTimeInterval.whole q
        hq.1 hq.2.1 hq.2.2.1).1
  have htrace : ∀ t, F.curve ⟨p,v⟩ t = q t :=
    fun t => ((hF ⟨p,v⟩).2.2.2 D13Unified.OpenTimeInterval.whole q
      hq.1 hq.2.1 hq.2.2.1).2 (mem_univ t)
  have hrad (t : ℝ) : fiberExponential F p (t • v) = (q t).1 := by
    rw [← htrace t]
    exact (ExponentialNormalCoordinates.radial_identity_at B.connection F hF p v t
      (by rw [hfull]; trivial)).2
  obtain ⟨E,c,hE,hchart,hsource,hall,hdist,hantip,hacos,hantiDist,hpolar,hradii⟩ :=
    (hSphere n hn a ha A B hB).1 F hF p
  have hend : (q (Real.pi * a)).1.val = -p.val := by
    rw [← hrad]
    exact hantip v hv
  have hD : modelDistance B.metric p (q (Real.pi * a)).1 = Real.pi * a :=
    hantiDist _ hend
  have hpos : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  let γ := CompleteExponentialMinimizers.geodesicRepresentative B.connection
    D13Unified.OpenTimeInterval.whole q hq.2.2.1 hpos.le (subset_univ _)
  have hγ : ∀ t, γ t = (q t).1 := fun _ => rfl
  have hL : length B.metric γ = Real.pi * a := by
    have hh := GeodesicCriticalityCorners.geodesic_piece_length_of_eqOn B.metric
      B.connection B.leviCivita D13Unified.OpenTimeInterval.whole q hq.2.2.1
      hpos (subset_univ _) γ (fun _ _ => rfl)
    change (∫ t in (0 : ℝ)..Real.pi * a, speed B.metric γ t) = _
    rw [hh, (hformula 0).2]
    ring
  refine ⟨hformula, hend, ⟨γ, hγ, ?_, hL, hD, ?_⟩,
    semicircle_jacobi hn ha B hB q hq.2.2.1 (fun t => (hformula t).2)⟩
  · change (q 0).1 = p
    rw [hq.2.1]
  · intro l r η hη0 hη1
    have hh := CompleteExponentialMinimizers.lengthDistance_le_length B.metric η
    rw [hη0, hη1] at hh
    rw [hL]
    exact hD ▸ hh

end P202.Geometry.TerminalConjugacyExample

theorem _root_.«P202».«Geometry».«TerminalConjugacyExample».«terminal_conjugacy» : _root_.«P202Specs».«Geometry».«TerminalConjugacyExample».«terminal_conjugacyType» :=
  @_root_.«P202».«Geometry».«TerminalConjugacyExample».«terminal_conjugacy_conditional» (@_root_.«P202».«Geometry».«ModelPolarDomains».«euclidean_distance») (@_root_.«P202».«Geometry».«ModelPolarDomains».«euclidean_formula») (@_root_.«P202».«Geometry».«ModelPolarDomains».«euclidean_geometry») (@_root_.«P202».«Geometry».«ModelPolarDomains».«halfSpace_homogeneity») (@_root_.«P202».«Geometry».«ModelPolarDomains».«hyperbolic_geometry») (@_root_.«P202».«Geometry».«ModelPolarDomains».«model_polar_domains») (@_root_.«P202».«Geometry».«ModelPolarDomains».«models_exist») (@_root_.«P202».«Geometry».«ModelPolarDomains».«spherical_cut_time») (@_root_.«P202».«Geometry».«ModelPolarDomains».«spherical_formula») (@_root_.«P202».«Geometry».«ModelPolarDomains».«spherical_geometry»)
