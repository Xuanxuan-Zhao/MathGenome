import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialNormalCoordinates
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GeodesicIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse

/-! Proposition 6.6: exponential maps on the actual maximal domain.
No global existence assumption is imposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.Geometry.ExponentialNormalCoordinates
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.CurveConnectionData
  P202.GeodesicData P202.LeviCivitaData P202.ExponentialData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- A family is chosen from actual maximal integral curves of the proved spray. -/
theorem family_exists : P202Specs.Geometry.ExponentialNormalCoordinates.family_existsType.{u} := by
  intro n M _ S C
  obtain ⟨G, _, hbridge⟩ := GeodesicIVP.spray_exists S C
  obtain ⟨F, hF⟩ := SmoothManifolds.MaximalFlow.maximal_family_exists
    (phaseManifold S) (tangentStructure (phaseManifold S)) G
  exact ⟨F, fun w => (GeodesicIVP.maximal_iff_integral C G hbridge
    w (F.interval w) (F.curve w)).mpr (hF w)⟩

variable (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
  (hF : P202.GeodesicData.IsMaximalFamily S C F)
include C F hF

/-- The initial zero velocity has the constant solution on the entire real line.
Universal maximality forces every choice of maximal family to agree with it. -/
theorem zero_family (p : M) :
    (F.interval ⟨p, 0⟩).carrier = univ ∧ ∀ t : ℝ, F.curve ⟨p, 0⟩ t = ⟨p, 0⟩ := by
  have h := (hF ⟨p, 0⟩).2.2.2 D13Unified.OpenTimeInterval.whole
    (constantCurve S p) (mem_univ _) rfl (GeodesicIVP.constant_is_geodesic C p)
  exact ⟨Subset.antisymm (subset_univ _) h.1, fun t => h.2 (mem_univ t)⟩

theorem zero_section_at (p : M) :
    (⟨p, 0⟩ : Phase S) ∈ exponentialDomain F ∧ fiberExponential F p 0 = p := by
  obtain ⟨hI, hq⟩ := zero_family C F hF p
  exact ⟨by change 1 ∈ (F.interval ⟨p, 0⟩).carrier; rw [hI]; trivial,
    congrArg Sigma.fst (hq 1)⟩

/-- Exact radial identity, with no sign restriction on the time parameter. -/
theorem radial_identity_at (p : M) (v : TangentSpace S p) (s : ℝ)
    (hs : s ∈ (F.interval ⟨p, v⟩).carrier) :
    (⟨p, s • v⟩ : Phase S) ∈ exponentialDomain F ∧
      fiberExponential F p (s • v) = (F.curve ⟨p, v⟩ s).1 := by
  by_cases hs0 : s = 0
  · subst s
    simpa only [zero_smul, (hF ⟨p, v⟩).2.1] using zero_section_at C F hF p
  · obtain ⟨J, hJ, hmax⟩ := GeodesicIVP.maximal_affine S C ⟨p, v⟩
      (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩) (hF ⟨p, v⟩) s 0 hs0 (hF ⟨p, v⟩).1
    have hi : affineCurve S (F.curve ⟨p, v⟩) s 0 0 = (⟨p, s • v⟩ : Phase S) := by
      change (⟨(F.curve ⟨p, v⟩ (s * 0 + 0)).1, s • (F.curve ⟨p, v⟩ (s * 0 + 0)).2⟩ : Phase S) = _
      rw [mul_zero, add_zero, (hF ⟨p, v⟩).2.1]
    rw [hi] at hmax
    obtain ⟨hI, hq⟩ := GeodesicIVP.maximal_unique S C ⟨p, s • v⟩
      (F.interval ⟨p, s • v⟩) J (F.curve ⟨p, s • v⟩)
      (affineCurve S (F.curve ⟨p, v⟩) s 0) (hF ⟨p, s • v⟩) hmax
    have h1 : 1 ∈ (F.interval ⟨p, s • v⟩).carrier := by
      rw [hI, hJ]
      simpa only [affineDomain, mem_ofPred_eq, mul_one, add_zero] using hs
    refine ⟨h1, ?_⟩
    have heq := congrArg Sigma.fst (hq h1)
    simpa only [fiberExponential, exponential, affineCurve, mul_one, add_zero] using heq

/-- Openness is inherited from the open joint existence domain by time slicing. -/
theorem domain_isOpen : IsOpen (exponentialDomain F) := by
  have h := (GeodesicIVP.domain_open_smooth S C F hF).1
  exact h.preimage (continuous_const.prodMk continuous_id)

/-- Restrict the smooth position flow to the constant time-one slice.
The witness is a smooth local extension in every pair of actual charts. -/
theorem exponential_smooth :
    ManifoldSmoothOn (phaseManifold S).smoothStructure.val S.smoothStructure.val
      (exponential F) (exponentialDomain F) := by
  intro w hw
  have h := (GeodesicIVP.domain_open_smooth S C F hF).2 (1, w) hw
  have hj : ContinuousAt (fun z : Phase S => ((1 : ℝ), z)) w :=
    continuous_const.continuousAt.prodMk continuousAt_id
  refine ⟨h.2.1.comp hj, ?_⟩
  intro e he d hd hw' hwd
  obtain ⟨U, hU, hzU, H, hH, heq⟩ := h.2.2 e he d hd hw' hwd
  let j : Euclidean (n + n) → ℝ × Euclidean (n + n) := fun x => (1, x)
  refine ⟨j ⁻¹' U, hU.preimage (continuous_const.prodMk continuous_id), hzU,
    H ∘ j, hH.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx), ?_⟩
  exact heq.comp_tendsto hj

/- A fiber in its own canonical coordinates has the expected tangent-chart
expression. This also fixes the source identification used for the derivative. -/
omit C F hF in
theorem fiberInclusion_chart (p : M) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) (x : Euclidean n) :
    let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
    (((tangentStructure S).chart e he) ⟨p, E.symm x⟩).val =
      (tangentStructure S).productCoordinates.linearEquiv ((e p).val, x) := by
  dsimp only
  rw [(tangentStructure S).chart_apply e he _ hp]
  simp only [LinearEquiv.apply_symm_apply]

omit C F hF in
theorem fiberInclusion_continuousAt (p : M) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) (x : Euclidean n) :
    let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
    ContinuousAt (fun y : Euclidean n => (⟨p, E.symm y⟩ : Phase S)) x := by
  dsimp only
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let b := (tangentStructure S).chart e he
  have hsource (y : Euclidean n) : (⟨p, E.symm y⟩ : Phase S) ∈ b.source := by
    simpa only [b, (tangentStructure S).chart_source, mem_preimage, projection] using hp
  have hcoord : ContinuousAt (fun y : Euclidean n => (b ⟨p, E.symm y⟩).val) x := by
    change ContinuousAt (fun y : Euclidean n =>
      (((tangentStructure S).chart e he) ⟨p, E.symm y⟩).val) x
    have hfun : (fun y : Euclidean n =>
        (((tangentStructure S).chart e he) ⟨p, E.symm y⟩).val) =
        (fun y => (tangentStructure S).productCoordinates.linearEquiv ((e p).val, y)) :=
      funext (fun y => fiberInclusion_chart p e he hp y)
    rw [hfun]
    exact (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv.continuous.continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt
  have hmodel : ContinuousAt (fun y : Euclidean n => b ⟨p, E.symm y⟩) x :=
    tendsto_subtype_rng.mpr hcoord
  have hback := (b.continuousAt_symm (b.map_source (hsource x))).comp (f := fun y : Euclidean n => b ⟨p, E.symm y⟩) hmodel
  exact hback.congr (Eventually.of_forall (fun y => b.left_inv (hsource y)))

/-- Smoothness of the exponential restricted to any tangent fiber, expressed
in the canonical fiber coordinates and an arbitrary target chart. -/
theorem fiberExponential_contDiffAt (p : M) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (x : Euclidean n)
    (hx : (⟨p, ((tangentStructure S).fiberCoordinates.equiv e he p hp).symm x⟩ : Phase S)
      ∈ exponentialDomain F)
    (hxd : fiberExponential F p
      (((tangentStructure S).fiberCoordinates.equiv e he p hp).symm x) ∈ d.source) :
    let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Euclidean n =>
      (d (fiberExponential F p (E.symm y))).val) x := by
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let b := (tangentStructure S).chart e he
  have hb := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
  have hpx : (⟨p, E.symm x⟩ : Phase S) ∈ b.source := by
    simpa only [b, (tangentStructure S).chart_source, mem_preimage, projection] using hp
  obtain ⟨U, hU, hxU, H, hH, heq⟩ :=
    (exponential_smooth C F hF _ hx).2 b hb d hd hpx hxd
  let j : Euclidean n → Euclidean (n + n) :=
    fun y => (tangentStructure S).productCoordinates.linearEquiv ((e p).val, y)
  have hj : ContDiff ℝ (⊤ : ℕ∞) j :=
    (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv.contDiff.comp
      (contDiff_const.prodMk contDiff_id)
  have hxj : j x ∈ U := by
    simpa only [b, fiberInclusion_chart p e he hp, j] using hxU
  have hcomp := (hH.contDiffAt (hU.mem_nhds hxj)).comp x hj.contDiffAt
  apply hcomp.congr_of_eventuallyEq
  have heq' := heq.comp_tendsto (fiberInclusion_continuousAt p e he hp x)
  simpa only [Function.comp_def, b, fiberInclusion_chart p e he hp, j,
    fiberExponential] using heq'.symm

/-- Every ray through the origin has precisely its prescribed initial velocity.
The local equality is obtained on the open maximal interval, not by assuming
that the original velocity survives to time one. -/
theorem radial_derivative (p : M) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) (v : TangentSpace S p) :
    HasDerivAt (fun s : ℝ => (e (fiberExponential F p (s • v))).val)
      ((tangentStructure S).fiberCoordinates.equiv e he p hp v) 0 := by
  let q := F.curve ⟨p, v⟩
  have h0 := (hF ⟨p, v⟩).1
  have hinit : q 0 = (⟨p, v⟩ : Phase S) := (hF ⟨p, v⟩).2.1
  have hv := ((hF ⟨p, v⟩).2.2.1 0 h0).1
  have hp' : (q 0).1 ∈ e.source := by rw [hinit]; exact hp
  have hd := CurveCovariantDerivative.velocity_coordinates hv (mem_univ 0) e he hp'
  have hd' : HasDerivAt (fun s : ℝ => (e (q s).1).val)
      ((tangentStructure S).fiberCoordinates.equiv e he p hp v) 0 := by
    have hcoords (z : Phase S) (hz : z.1 ∈ e.source) (h : z = ⟨p, v⟩) :
        (tangentStructure S).fiberCoordinates.equiv e he z.1 hz z.2 =
          (tangentStructure S).fiberCoordinates.equiv e he p hp v := by
      subst z
      rfl
    rw [hcoords _ hp' hinit] at hd
    exact hasDerivWithinAt_univ.mp hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [(F.interval ⟨p, v⟩).isOpen.mem_nhds h0] with s hs
  exact congrArg (fun z : M => (e z).val) (radial_identity_at C F hF p v s hs).2

/-- Smoothness makes the differential linear; its values on all radial
velocities determine it, including on a zero-dimensional tangent space. -/
theorem derivative_zero_at (p : M) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
    HasFDerivAt (fun x : Euclidean n => (e (fiberExponential F p (E.symm x))).val)
      (ContinuousLinearMap.id ℝ (Euclidean n)) 0 := by
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let f : Euclidean n → Euclidean n := fun x => (e (fiberExponential F p (E.symm x))).val
  have hzero := zero_section_at C F hF p
  have hx : (⟨p, E.symm 0⟩ : Phase S) ∈ exponentialDomain F := by
    simpa only [map_zero] using hzero.1
  have hxp : fiberExponential F p (E.symm 0) ∈ e.source := by
    simpa only [map_zero, hzero.2] using hp
  have hcd := fiberExponential_contDiffAt C F hF p e he hp e he 0 hx hxp
  have hf : DifferentiableAt ℝ f 0 := hcd.differentiableAt (by simp)
  have hL : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ (Euclidean n) := by
    apply ContinuousLinearMap.ext
    intro x
    have hray := radial_derivative C F hF p e he hp (E.symm x)
    have hline : HasDerivAt (fun s : ℝ => s • x) x 0 := by
      simpa only [one_smul, id_eq] using! (hasDerivAt_id (0 : ℝ)).smul_const x
    have hchain := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have heq : (fun s : ℝ => f (s • x)) =
        (fun s : ℝ => (e (fiberExponential F p (s • E.symm x))).val) := by
      funext s
      simp only [f, map_smul]
    change HasDerivAt (fun s => f (s • x)) _ _ at hchain
    rw [heq] at hchain
    simpa only [E, LinearEquiv.apply_symm_apply, ContinuousLinearMap.id_apply] using hchain.unique hray
  rw [← hL]
  exact hf.hasFDerivAt

omit C F hF in
/-- Normalize an orthogonal basis for the positive-definite tangent metric.
This algebraic construction works equally in rank zero. -/
theorem orthonormal_coordinates_exist (g : RiemannianMetric S) (p : M) :
    ∃ E : TangentSpace S p ≃ₗ[ℝ] Euclidean n, IsOrthonormalCoordinates g p E := by
  classical
  let : FiniteDimensional ℝ (TangentSpace S p) := (SmoothManifolds.tangent_dimension S p).1
  have hdim : Module.finrank ℝ (TangentSpace S p) = n :=
    (SmoothManifolds.tangent_dimension S p).2
  have hex : ∃ b : Module.Basis (Fin n) ℝ (TangentSpace S p), (g.form p).IsOrthoᵢ b := by
    obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := g.form p) ⟨g.symmetric p⟩
    refine ⟨b.reindex (finCongr hdim), ?_⟩
    intro i j hij
    simpa only [Function.onFun, Module.Basis.reindex_apply] using
      hb (fun h => hij ((finCongr hdim).symm.injective h))
  obtain ⟨b, hb⟩ := hex
  let w : Fin n → ℝ := fun i => (Real.sqrt (g.form p (b i) (b i)))⁻¹
  have hpos (i : Fin n) : 0 < g.form p (b i) (b i) := g.positive p _ (b.ne_zero i)
  have hw (i : Fin n) : IsUnit (w i) :=
    isUnit_iff_ne_zero.mpr (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (hpos i))))
  let b' := b.isUnitSMul hw
  refine ⟨b'.equivFun, ?_⟩
  have hsingle (i : Fin n) : b'.equivFun.symm (Pi.single i 1) = b' i := by
    simp only [Module.Basis.equivFun_symm_apply, Pi.single_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  intro i j
  rw [hsingle i, hsingle j]
  change g.form p (b' i) (b' j) = _
  simp only [b', Module.Basis.isUnitSMul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    change (Real.sqrt (g.form p (b i) (b i)))⁻¹ *
      ((Real.sqrt (g.form p (b i) (b i)))⁻¹ * g.form p (b i) (b i)) = 1
    rw [← mul_assoc, ← mul_inv, ← pow_two, Real.sq_sqrt (hpos i).le,
      inv_mul_cancel₀ (ne_of_gt (hpos i))]
  · rw [ite_eq_right hij, hb hij, mul_zero, mul_zero]

omit C hF in
/-- The inverse law in a normal chart identifies the germ of every radial
exponential curve with a straight line in the chosen basis coordinates. -/
theorem normal_chart_ray_germ (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r : ℝ)
    (c : ModelChart n .euclidean M) (hc : IsNormalChart g F p E r c)
    (v : TangentSpace S p) :
    (fun s : ℝ => (c (fiberExponential F p (s • v))).val) =ᶠ[𝓝 0]
      (fun s : ℝ => s • E v) := by
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0, |s| * tangentNorm g p v < r :=
    (continuous_abs.mul_const (tangentNorm g p v)).continuousAt
      (Iio_mem_nhds (by simpa only [abs_zero, zero_mul] using hc.1))
  filter_upwards [hsmall] with s hs
  let x : ModelSpace n .euclidean := ⟨E (s • v), mem_univ _⟩
  have hxnorm : tangentNorm g p (E.symm x.val) < r := by
    simpa only [x, LinearEquiv.symm_apply_apply, SmoothMetrics.tangentNorm_smul] using hs
  have hx : x ∈ c.target := by rw [hc.2.2.2.2.1]; exact hxnorm
  have heq : fiberExponential F p (s • v) = c.symm x := by
    simpa only [x, LinearEquiv.symm_apply_apply] using (hc.2.2.2.2.2 x hxnorm).2
  calc
    (c (fiberExponential F p (s • v))).val = (c (c.symm x)).val := congrArg (fun z => (c z).val) heq
    _ = x.val := congrArg Subtype.val (c.right_inv hx)
    _ = s • E v := E.map_smul s v

/-- The canonical coordinate tangent map at the center equals the basis
identification used to construct the normal chart. -/
theorem normal_chart_coordinates (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r : ℝ)
    (c : ModelChart n .euclidean M) (hc : IsNormalChart g F p E r c)
    (v : TangentSpace S p) :
    (tangentStructure S).fiberCoordinates.equiv c hc.2.1 p hc.2.2.1 v = E v := by
  have hray := radial_derivative C F hF p c hc.2.1 hc.2.2.1 v
  have hline : HasDerivAt (fun s : ℝ => s • E v) (E v) 0 := by
    simpa only [one_smul, id_eq] using! (hasDerivAt_id (0 : ℝ)).smul_const (E v)
  exact hray.unique (hline.congr_of_eventuallyEq (normal_chart_ray_germ F g p E r c hc v))

/-- The metric is Euclidean at the center of any orthonormal normal chart. -/
theorem normal_chart_metric (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E)
    (r : ℝ) (c : ModelChart n .euclidean M) (hc : IsNormalChart g F p E r c) :
    let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc.2.1⟩
    ∀ i j : Fin n, metricMatrix g d p i j = if i = j then 1 else 0 := by
  dsimp only
  let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc.2.1⟩
  have hp : p ∈ (tangentBundle S).baseSet d := by
    simpa only [(tangentRealization S).baseSet d] using hc.2.2.1
  have hvec (i : Fin n) : coordinateVector d i p = E.symm (Pi.single i 1) := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    rw [← normal_chart_coordinates C F hF g p E r c hc (coordinateVector d i p)]
    rw [← (tangentRealization S).coordinates d p hc.2.2.1]
    change ((tangentBundle S).trivialization d ⟨p, coordinateVector d i p⟩).2 = _
    change ((tangentBundle S).fiberCoordinates d p hp (coordinateVector d i p)) = _
    change ((tangentBundle S).fiberCoordinates d p hp
      (((tangentBundle S).fiberCoordinates d p hp).symm (Pi.single i 1))) = _
    exact LinearEquiv.apply_symm_apply _ _
  intro i j
  change pairing g p (coordinateVector d i p) (coordinateVector d j p) = _
  rw [hvec i, hvec j]
  exact hE i j

/-- In a normal chart every radial geodesic is a straight line as a germ,
so its coordinate acceleration at the center vanishes. -/
theorem normal_chart_acceleration (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r : ℝ)
    (c : ModelChart n .euclidean M) (hc : IsNormalChart g F p E r c)
    (v : TangentSpace S p) :
    let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc.2.1⟩
    let hp : p ∈ (tangentBundle S).baseSet d := by
      simpa only [(tangentRealization S).baseSet d] using hc.2.2.1
    coordinateAcceleration S C d ⟨p, hp⟩ (E v) = 0 := by
  dsimp only
  let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc.2.1⟩
  let q := F.curve ⟨p, v⟩
  let I := F.interval ⟨p, v⟩
  have h0 : 0 ∈ I.carrier := (hF ⟨p, v⟩).1
  have hinit : q 0 = (⟨p, v⟩ : Phase S) := (hF ⟨p, v⟩).2.1
  have hgeo : IsGeodesicOn S C I.carrier q := (hF ⟨p, v⟩).2.2.1
  have hp0 : (q 0).1 ∈ c.source := by rw [hinit]; exact hc.2.2.1
  have hcont : ContinuousAt (fun t => (q t).1) 0 :=
    (hgeo 0 h0).1.1.continuousAt (by simp)
  have hsource : ∀ᶠ t in 𝓝 0, (q t).1 ∈ c.source :=
    hcont.preimage_mem_nhds (c.open_source.mem_nhds hp0)
  have hcoord : (fun t : ℝ => (c (q t).1).val) =ᶠ[𝓝 0] (fun t => t • E v) := by
    filter_upwards [I.isOpen.mem_nhds h0, normal_chart_ray_germ F g p E r c hc v] with t ht heq
    rw [← (radial_identity_at C F hF p v t ht).2]
    exact heq
  have hvel : chartVelocity S d q =ᶠ[𝓝 0] (fun _ => E v) := by
    filter_upwards [I.isOpen.mem_nhds h0, hsource, hcoord.eventually_nhds] with t ht htc heq
    have hbase : (q t).1 ∈ (tangentBundle S).baseSet d := by
      simpa only [(tangentRealization S).baseSet d] using htc
    have hderiv := (GeodesicIVP.geodesic_coordinate_equation C hgeo ht d hbase).1
    have hline : HasDerivAt (fun s : ℝ => s • E v) (E v) t := by
      simpa only [one_smul, id_eq] using! (hasDerivAt_id t).smul_const (E v)
    exact hderiv.unique (hline.congr_of_eventuallyEq heq)
  have hbase0 : (q 0).1 ∈ (tangentBundle S).baseSet d := by
    simpa only [(tangentRealization S).baseSet d] using hp0
  have hderiv := (GeodesicIVP.geodesic_coordinate_equation C hgeo h0 d hbase0).2
  have hz : HasDerivAt (chartVelocity S d q) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (E v)).congr_of_eventuallyEq hvel
  have hacc := hderiv.unique hz
  rw [hvel.eq_of_nhds] at hacc
  have hpoint : (⟨(q 0).1, hbase0⟩ : (tangentBundle S).baseSet d) =
      ⟨p, by simpa only [(tangentRealization S).baseSet d] using hc.2.2.1⟩ :=
    Subtype.ext (congrArg Sigma.fst hinit)
  rw [hpoint] at hacc
  exact hacc

omit F hF in
/-- Symmetry of the lower Christoffel indices follows from the actual
Levi–Civita formula and symmetry of the metric coefficient functions. -/
theorem christoffel_symmetric (g : RiemannianMetric S) (hC : IsLeviCivita g C)
    (d : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet d) (k i j : Fin n) :
    christoffel C d p k i j = christoffel C d p k j i := by
  rw [LeviCivita.christoffel_formula g C hC d p k i j,
    LeviCivita.christoffel_formula g C hC d p k j i]
  have hs : (fun q => metricMatrix g d q i j) = (fun q => metricMatrix g d q j i) :=
    funext (fun q => g.symmetric q _ _)
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Polarization of the radial geodesic equation kills every Christoffel
coefficient at the center. No global radial geodesic is assumed. -/
theorem normal_chart_christoffel (g : RiemannianMetric S) (hC : IsLeviCivita g C)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r : ℝ)
    (c : ModelChart n .euclidean M) (hc : IsNormalChart g F p E r c) :
    let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc.2.1⟩
    let q : (tangentBundle S).baseSet d := ⟨p, by
      simpa only [(tangentRealization S).baseSet d] using hc.2.2.1⟩
    ∀ k i j : Fin n, christoffel C d q k i j = 0 := by
  classical
  dsimp only
  let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc.2.1⟩
  let q : (tangentBundle S).baseSet d := ⟨p, by
    simpa only [(tangentRealization S).baseSet d] using hc.2.2.1⟩
  intro k i j
  have hquad (x : Euclidean n) :
      ∑ a : Fin n, ∑ b : Fin n, christoffel C d q k a b * x a * x b = 0 := by
    have h := normal_chart_acceleration C F hF g p E r c hc (E.symm x)
    dsimp only at h
    rw [LinearEquiv.apply_symm_apply] at h
    have hv := congrFun h k
    simpa only [coordinateAcceleration, Pi.zero_apply, neg_eq_zero] using hv
  have hdiag (a : Fin n) : christoffel C d q k a a = 0 := by
    have h := hquad (Pi.single a 1)
    simpa only [Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero] using h
  have hcross := hquad (Pi.single i 1 + Pi.single j 1)
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hcross
  have hsym := christoffel_symmetric C g hC d q k i j
  have hi := hdiag i
  have hj := hdiag j
  linarith

/-- At an orthonormal center, the Levi–Civita formula with vanishing
Christoffel symbols implies vanishing of every first metric derivative. -/
theorem normal_chart_metric_derivatives (g : RiemannianMetric S) (hC : IsLeviCivita g C)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E)
    (r : ℝ) (c : ModelChart n .euclidean M) (hc : IsNormalChart g F p E r c) :
    let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc.2.1⟩
    ∀ i j k : Fin n, scalarDerivative S (fun z => metricMatrix g d z j k) p
      (coordinateVector d i p) = 0 := by
  classical
  dsimp only
  let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc.2.1⟩
  let q : (tangentBundle S).baseSet d := ⟨p, by
    simpa only [(tangentRealization S).baseSet d] using hc.2.2.1⟩
  have hm : metricMatrix g d p = 1 := by
    ext i j
    simpa only [Matrix.one_apply] using normal_chart_metric C F hF g p E hE r c hc i j
  have hinv : (metricMatrix g d p)⁻¹ = 1 := by rw [hm, inv_one]
  let D : Fin n → Fin n → Fin n → ℝ := fun i j k =>
    scalarDerivative S (fun z => metricMatrix g d z j k) p (coordinateVector d i p)
  have hsym (i j k : Fin n) : D i j k = D i k j := by
    apply congrArg (fun f : M → ℝ => scalarDerivative S f p (coordinateVector d i p))
    exact funext (fun z => g.symmetric z _ _)
  have hrel (k i j : Fin n) : (1 / 2 : ℝ) * (D i j k + D j i k - D k i j) = 0 := by
    have h := LeviCivita.christoffel_formula g C hC d q k i j
    rw [normal_chart_christoffel C F hF g hC p E r c hc k i j] at h
    change 0 = (1 / 2 : ℝ) * ∑ l : Fin n, (metricMatrix g d p)⁻¹ k l *
      (D i j l + D j i l - D l i j) at h
    rw [hinv] at h
    simpa only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true] using h.symm
  intro i j k
  have h1 := hrel k i j
  have h2 := hrel j i k
  rw [hsym i k j] at h2
  change D i j k = 0
  linarith

omit C F hF in
/-- Norm comparison needed to select a metric ball inside an inverse-function
neighborhood. The finite sum is empty in dimension zero. -/
theorem orthonormal_norm_formula (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E)
    (x : Euclidean n) : tangentNorm g p (E.symm x) = Real.sqrt (∑ i : Fin n, x i ^ 2) := by
  unfold tangentNorm
  have h := SmoothMetrics.bilinear_coordinates E (g.form p) (E.symm x) (E.symm x)
  simp only [LinearEquiv.apply_symm_apply] at h
  simp_rw [show ∀ i j, g.form p (E.symm (Pi.single i 1)) (E.symm (Pi.single j 1)) =
    if i = j then 1 else 0 from hE] at h
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  simpa only [pairing, pow_two] using congrArg Real.sqrt h

omit C F hF in
theorem orthonormal_norm_continuous (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E) :
    Continuous (fun x : Euclidean n => tangentNorm g p (E.symm x)) := by
  simp_rw [orthonormal_norm_formula g p E hE]
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2))

omit C F hF in
theorem coordinate_norm_le_metric_norm (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E)
    (x : Euclidean n) : ‖x‖ ≤ tangentNorm g p (E.symm x) := by
  rw [orthonormal_norm_formula g p E hE]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  have hsum : 0 ≤ ∑ j : Fin n, x j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hi : x i ^ 2 ≤ ∑ j : Fin n, x j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  have habs := abs_nonneg (x i)
  have hs := Real.sqrt_nonneg (∑ j : Fin n, x j ^ 2)
  have heq := Real.sq_sqrt hsum
  nlinarith [sq_abs (x i)]

omit C F hF in
noncomputable def parametrizationChart (h : OpenPartialHomeomorph (Euclidean n) M) :
    ModelChart n .euclidean M :=
  h.symm.trans (Homeomorph.Set.univ (Euclidean n)).symm.toOpenPartialHomeomorph

omit C F hF in
@[simp] theorem parametrizationChart_apply (h : OpenPartialHomeomorph (Euclidean n) M) (p : M) :
    (parametrizationChart h p).val = h.symm p := rfl

omit C F hF in
@[simp] theorem parametrizationChart_symm (h : OpenPartialHomeomorph (Euclidean n) M)
    (x : ModelSpace n .euclidean) : (parametrizationChart h).symm x = h x.val := rfl

omit C F hF in
@[simp] theorem parametrizationChart_source (h : OpenPartialHomeomorph (Euclidean n) M) :
    (parametrizationChart h).source = h.target := by
  ext x
  simp only [parametrizationChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  rfl

omit C F hF in
@[simp] theorem parametrizationChart_target (h : OpenPartialHomeomorph (Euclidean n) M) :
    (parametrizationChart h).target = {x | x.val ∈ h.source} := by
  ext x
  simp only [parametrizationChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, mem_inter_iff, mem_univ, true_and,
    mem_preimage, mem_ofPred_eq]
  rfl

omit C F hF in
/-- A smooth Euclidean parametrization with smooth inverse defines a chart
in the original maximal smooth atlas, rather than an unrelated atlas. -/
theorem parametrizationChart_mem (h : OpenPartialHomeomorph (Euclidean n) M)
    (hf : ∀ x ∈ h.source, ∀ d ∈ S.smoothStructure.val, h x ∈ d.source →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (d (h y)).val) x)
    (hg : ∀ x ∈ h.target, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
      S.smoothStructure.val h.symm x) :
    parametrizationChart h ∈ S.smoothStructure.val := by
  let c := parametrizationChart h
  have hm : c ∈ maximalExtension (⊤ : ℕ∞) S.smoothStructure.val := by
    intro d hd
    apply SmoothManifolds.contDiffCompatible_of_germs
    · intro x hxc hxd
      have hxt : x ∈ h.target := by simpa only [c, parametrizationChart_source] using hxc
      let U := h.source ∩ h ⁻¹' d.source
      have hU : IsOpen U := h.continuousOn.isOpen_inter_preimage h.open_source d.open_source
      have hxU : (c x).val ∈ U := by
        change h.symm x ∈ U
        refine ⟨h.map_target hxt, ?_⟩
        change h (h.symm x) ∈ d.source
        rwa [h.right_inv hxt]
      refine ⟨U, hU, hxU, fun y => (d (h y)).val, fun y hy =>
        (hf y hy.1 d hd hy.2).contDiffWithinAt, ?_⟩
      filter_upwards [h.open_target.mem_nhds hxt] with y hy
      exact congrArg (fun z => (d z).val) (h.right_inv hy)
    · intro x hxd hxc
      have hxt : x ∈ h.target := by simpa only [c, parametrizationChart_source] using hxc
      exact (hg x hxt).2 d hd hxd
  have heq := S.smoothStructure.property.2
    (maximalExtension (⊤ : ℕ∞) S.smoothStructure.val)
    (SmoothManifolds.maximalExtension_isContDiffAtlas S.smoothStructure.property.1)
    (SmoothManifolds.subset_maximalExtension S.smoothStructure.property.1)
  rwa [heq] at hm

omit C F hF in
theorem fiberInclusion_continuous_basis (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Continuous (fun x : Euclidean n => (⟨p, E.symm x⟩ : Phase S)) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let K := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let A := (E.symm.trans K).toContinuousLinearEquiv
  have hcan : Continuous (fun x : Euclidean n => (⟨p, K.symm x⟩ : Phase S)) :=
    continuous_iff_continuousAt.mpr (fun x => fiberInclusion_continuousAt p e he hp x)
  have hh := hcan.comp A.continuous
  have heq : (fun x : Euclidean n => (⟨p, K.symm (A x)⟩ : Phase S)) =
      (fun x : Euclidean n => (⟨p, E.symm x⟩ : Phase S)) := by
    funext x
    change (⟨p, K.symm (K (E.symm x))⟩ : Phase S) = _
    rw [LinearEquiv.symm_apply_apply]
  exact heq ▸ hh

theorem fiberExponential_contDiffAt_basis (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (x : Euclidean n) (hx : (⟨p, E.symm x⟩ : Phase S) ∈ exponentialDomain F)
    (hxd : fiberExponential F p (E.symm x) ∈ d.source) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (d (fiberExponential F p (E.symm y))).val) x := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let K := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let A := (E.symm.trans K).toContinuousLinearEquiv
  have hA (y : Euclidean n) : K.symm (A y) = E.symm y := K.symm_apply_apply _
  have hx' : (⟨p, K.symm (A x)⟩ : Phase S) ∈ exponentialDomain F := by rwa [hA]
  have hxd' : fiberExponential F p (K.symm (A x)) ∈ d.source := by rwa [hA]
  have h := (fiberExponential_contDiffAt C F hF p e he hp d hd (A x) hx' hxd').comp x A.contDiff.contDiffAt
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun y => (d (fiberExponential F p (K.symm (A y)))).val) x at h
  simpa only [hA] using h

theorem fiberExponential_derivative_basis (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    let K := (tangentStructure S).fiberCoordinates.equiv e he p hp
    let A := (E.symm.trans K).toContinuousLinearEquiv
    HasFDerivAt (fun x => (e (fiberExponential F p (E.symm x))).val) A.toContinuousLinearMap 0 := by
  dsimp only
  let K := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let A := (E.symm.trans K).toContinuousLinearEquiv
  have hA (y : Euclidean n) : K.symm (A y) = E.symm y := K.symm_apply_apply _
  have hd : HasFDerivAt (fun x => (e (fiberExponential F p (K.symm x))).val)
      (ContinuousLinearMap.id ℝ (Euclidean n)) (A 0) := by
    simpa only [map_zero] using derivative_zero_at C F hF p e he hp
  have hh := hd.comp 0 A.hasFDerivAt
  simpa only [Function.comp_def, hA, ContinuousLinearMap.id_comp] using hh

/-- The ordinary inverse function theorem applied in a base chart gives a
smooth local parametrization by the actual exponential map. -/
theorem fiberExponential_parametrization (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    ∃ h : OpenPartialHomeomorph (Euclidean n) M,
      0 ∈ h.source ∧ h 0 = p ∧
      (∀ x ∈ h.source, (⟨p, E.symm x⟩ : Phase S) ∈ exponentialDomain F) ∧
      EqOn h (fun x => fiberExponential F p (E.symm x)) h.source ∧
      (∀ x ∈ h.source, ∀ d ∈ S.smoothStructure.val, h x ∈ d.source →
        ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (d (h y)).val) x) ∧
      (∀ x ∈ h.target, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
        S.smoothStructure.val h.symm x) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let f : Euclidean n → M := fun x => fiberExponential F p (E.symm x)
  let D : Set (Euclidean n) := {x | (⟨p, E.symm x⟩ : Phase S) ∈ exponentialDomain F}
  have hD : IsOpen D := (domain_isOpen C F hF).preimage (fiberInclusion_continuous_basis p E)
  have hfc (x : Euclidean n) (hx : x ∈ D) : ContinuousAt f x :=
    (exponential_smooth C F hF _ hx).1.comp
      (f := fun y : Euclidean n => (⟨p, E.symm y⟩ : Phase S))
      (fiberInclusion_continuous_basis p E).continuousAt
  have hfcOn : ContinuousOn f D := fun x hx => (hfc x hx).continuousWithinAt
  let U := D ∩ f ⁻¹' e.source
  have hU : IsOpen U := hfcOn.isOpen_inter_preimage hD e.open_source
  have hf0 : f 0 = p := by simpa only [f, map_zero] using (zero_section_at C F hF p).2
  have h0U : (0 : Euclidean n) ∈ U := by
    refine ⟨?_, ?_⟩
    · simpa only [D, mem_ofPred_eq, map_zero] using (zero_section_at C F hF p).1
    · change f 0 ∈ e.source
      rwa [hf0]
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (e (f x)).val) U := by
    intro x hx
    exact (fiberExponential_contDiffAt_basis C F hF p E e he x hx.1 hx.2).contDiffWithinAt
  let K := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let A := (E.symm.trans K).toContinuousLinearEquiv
  have hd : HasFDerivAt (fun x => (e (f x)).val) A.toContinuousLinearMap 0 :=
    fiberExponential_derivative_basis C F hF p E e he hp
  obtain ⟨j, hj0, hjf, hji⟩ := SmoothManifolds.InteriorInverse.euclidean_inverse
    (⊤ : ℕ∞) (by simp) (fun x => (e (f x)).val) U hU hf 0 h0U A hd A.bijective
  let b := SmoothManifolds.InteriorInverse.ambientChart e
  have hpb : p ∈ b.source := by
    refine ⟨hp, ?_⟩
    change (e p).val ∈ interior (modelSet n .euclidean)
    simp [modelSet]
  have hjp : j 0 = b p := by
    rw [hjf]
    change (e (f 0)).val = (e p).val
    rw [hf0]
  let h := (j.restrOpen U hU).trans b.symm
  have h0 : (0 : Euclidean n) ∈ h.source := by
    refine ⟨⟨hj0, h0U⟩, ?_⟩
    change j 0 ∈ b.target
    rw [hjp]
    exact b.map_source hpb
  have hfun0 : h 0 = p := by
    change b.symm (j 0) = p
    rw [hjp, b.left_inv hpb]
  have hsource (x : Euclidean n) (hx : x ∈ h.source) : x ∈ U := hx.1.2
  have heq : EqOn h f h.source := by
    intro x hx
    change b.symm (j x) = f x
    rw [hjf]
    apply b.left_inv
    refine ⟨(hsource x hx).2, ?_⟩
    change (e (f x)).val ∈ interior (modelSet n .euclidean)
    simp [modelSet]
  refine ⟨h, h0, hfun0, fun x hx => (hsource x hx).1, heq, ?_, ?_⟩
  · intro x hx d hd hxd
    have hfxd : f x ∈ d.source := by rwa [← heq hx]
    have hcd := fiberExponential_contDiffAt_basis C F hF p E d hd x (hsource x hx).1 hfxd
    apply hcd.congr_of_eventuallyEq
    filter_upwards [h.open_source.mem_nhds hx] with y hy
    exact congrArg (fun z => (d z).val) (heq hy)
  · intro y hy
    have hye : y ∈ e.source := hy.1.1
    have hyj : (e y).val ∈ j.target := hy.2.1
    refine ⟨h.symm.continuousAt hy, ?_⟩
    intro d hd hyd
    have ht := SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 d hd e he) hyd hye
    have hi : LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (e z).val) h.symm y :=
      ⟨j.target, j.open_target, hyj, j.symm, hji, Eventually.of_forall (fun _ => rfl)⟩
    exact SmoothManifolds.LocalCoordinateExtension.comp hi ht

/-- Restrict the inverse-function neighborhood to a metric ball. The chart is
proved to belong to the original maximal smooth atlas. -/
theorem normal_chart_exists_at (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsOrthonormalCoordinates g p E) :
    ∃ (r : ℝ) (c : ModelChart n .euclidean M), IsNormalChart g F p E r c := by
  obtain ⟨h, h0, hf0, hdom, heq, hf, hg⟩ := fiberExponential_parametrization C F hF p E
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (h.open_source.mem_nhds h0)
  let B : Set (Euclidean n) := {x | tangentNorm g p (E.symm x) < r}
  have hB : IsOpen B := (orthonormal_norm_continuous g p E hE).isOpen_preimage _ isOpen_Iio
  have hBs : B ⊆ h.source := by
    intro x hx
    apply hball
    have hlt := lt_of_le_of_lt (coordinate_norm_le_metric_norm g p E hE x) hx
    simpa only [Metric.mem_ball, dist_zero_right] using hlt
  let h' := h.restrOpen B hB
  have hs : h'.source = B := by
    change h.source ∩ B = B
    exact inter_eq_right.mpr hBs
  have hzB : (0 : Euclidean n) ∈ B := by
    simpa only [B, mem_ofPred_eq, map_zero, SmoothMetrics.tangentNorm_zero] using hr
  have hz : (0 : Euclidean n) ∈ h'.source := by rwa [hs]
  let c := parametrizationChart h'
  have hc : c ∈ S.smoothStructure.val := parametrizationChart_mem h'
    (fun x hx d hd hxd => hf x hx.1 d hd hxd) (fun y hy => hg y hy.1)
  have hp : p ∈ c.source := by
    rw [show c.source = h'.target from parametrizationChart_source h']
    have hh := h'.map_source hz
    change h 0 ∈ h'.target at hh
    rwa [hf0] at hh
  have hcp : (c p).val = 0 := by
    change h'.symm p = 0
    rw [← hf0]
    exact h'.left_inv hz
  refine ⟨r, c, hr, hc, hp, hcp, ?_, ?_⟩
  · change (parametrizationChart h').target = _
    rw [parametrizationChart_target, hs]
    rfl
  · intro x hx
    have hxB : x.val ∈ B := hx
    have hxs : x.val ∈ h.source := hBs hxB
    exact ⟨hdom x.val hxs, (heq hxs).symm⟩

omit C F hF
section Targets

theorem domain_open : P202Specs.Geometry.ExponentialNormalCoordinates.domain_openType.{u} := by
  intro n M _ S C F hF
  exact domain_isOpen C F hF

theorem zero_section : P202Specs.Geometry.ExponentialNormalCoordinates.zero_sectionType.{u} := by
  intro n M _ S C F hF p
  exact zero_section_at C F hF p

theorem radial_identity : P202Specs.Geometry.ExponentialNormalCoordinates.radial_identityType.{u} := by
  intro n M _ S C F hF p v s hs
  exact radial_identity_at C F hF p v s hs

theorem fiber_star_shaped :
    P202Specs.Geometry.ExponentialNormalCoordinates.fiber_star_shapedType.{u} := by
  intro n M _ S C F hF p v hv s hs0 hs1
  have hs : s ∈ (F.interval ⟨p, v⟩).carrier :=
    (F.interval ⟨p, v⟩).ordConnected.out (hF ⟨p, v⟩).1 hv ⟨hs0, hs1⟩
  exact (radial_identity_at C F hF p v s hs).1

theorem smooth : P202Specs.Geometry.ExponentialNormalCoordinates.smoothType.{u} := by
  intro n M _ S C F hF
  exact exponential_smooth C F hF

theorem derivative_zero :
    P202Specs.Geometry.ExponentialNormalCoordinates.derivative_zeroType.{u} := by
  intro n M _ S C F hF p e he hp
  exact derivative_zero_at C F hF p e he hp

theorem orthonormal_exists :
    P202Specs.Geometry.ExponentialNormalCoordinates.orthonormal_existsType.{u} := by
  intro n M _ S g p
  exact orthonormal_coordinates_exist g p

theorem normal_chart_identities :
    P202Specs.Geometry.ExponentialNormalCoordinates.normal_chart_identitiesType.{u} := by
  intro n M _ S g C hC F hF p E hE r c hc
  exact ⟨normal_chart_metric C F hF g p E hE r c hc,
    normal_chart_christoffel C F hF g hC p E r c hc,
    normal_chart_metric_derivatives C F hF g hC p E hE r c hc⟩

theorem normal_chart_exists :
    P202Specs.Geometry.ExponentialNormalCoordinates.normal_chart_existsType.{u} := by
  intro n M _ S g C _hC F hF p E hE
  exact normal_chart_exists_at C F hF g p E hE

end Targets

abbrev exponentialDomain : P202Specs.Geometry.ExponentialNormalCoordinates.exponentialDomainType.{u} :=
  @P202.ExponentialData.exponentialDomain

abbrev exponential : P202Specs.Geometry.ExponentialNormalCoordinates.exponentialType.{u} :=
  @P202.ExponentialData.exponential

abbrev fiberExponential : P202Specs.Geometry.ExponentialNormalCoordinates.fiberExponentialType.{u} :=
  @P202.ExponentialData.fiberExponential

abbrev IsOrthonormalCoordinates : P202Specs.Geometry.ExponentialNormalCoordinates.IsOrthonormalCoordinatesType.{u} :=
  @P202.ExponentialData.IsOrthonormalCoordinates

abbrev IsNormalChart : P202Specs.Geometry.ExponentialNormalCoordinates.IsNormalChartType.{u} :=
  @P202.ExponentialData.IsNormalChart

end P202.Geometry.ExponentialNormalCoordinates
