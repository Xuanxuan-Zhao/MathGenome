import MathGenome.Internal.LinearPDE.P201Specs.Potential.AnalyticContinuation
import MathGenome.Internal.LinearPDE.P201.Potential.BallPoisson
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.ContinuousMap.Units

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace P201.AnalyticContinuation

/-- Analytic regularity can be recovered through a local analytic diffeomorphism. -/
lemma analyticAt_of_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {g : E → F} {x : E} (i : F ≃L[ℝ] G)
    (hf : AnalyticAt ℝ f (g x)) (hd : HasFDerivAt f (i : F →L[ℝ] G) (g x))
    (hg : ContinuousAt g x) (hfg : AnalyticAt ℝ (f ∘ g) x) : AnalyticAt ℝ g x := by
  have hs : HasStrictFDerivAt f (i : F →L[ℝ] G) (g x) := by
    rw [← hd.fderiv]
    exact hf.hasStrictFDerivAt
  let R := hs.toOpenPartialHomeomorph f
  have hx : g x ∈ R.source := hs.mem_toOpenPartialHomeomorph_source
  obtain ⟨p, hp⟩ := hf
  have hc : p 1 = (continuousMultilinearCurryFin1 ℝ F G).symm (i : F →L[ℝ] G) := by
    apply (continuousMultilinearCurryFin1 ℝ F G).injective
    simpa using hp.hasFDerivAt.unique hd
  have hi : AnalyticAt ℝ R.symm (f (g x)) :=
    (R.hasFPowerSeriesAt_symm hx hp hc).analyticAt
  apply (hi.comp (f := f ∘ g) (x := x) hfg).congr
  filter_upwards [hg.preimage_mem_nhds (R.open_source.mem_nhds hx)] with y hy
  exact R.left_inv hy

/-- Distances to a compact sphere, bundled with the supremum norm. -/
def sphereDistance {n : ℕ} (a : Space n) (r : ℝ) (x : Space n) : C(sphere a r, ℝ) :=
  ⟨fun ζ => ‖x - (ζ : Space n)‖, by fun_prop⟩

lemma sphereDistance_continuous {n : ℕ} (a : Space n) (r : ℝ) :
    Continuous (sphereDistance a r) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Space n × sphere a r => ‖p.1 - (p.2 : Space n)‖)
  fun_prop

lemma sphereDistance_center {n : ℕ} (a : Space n) (r : ℝ) :
    sphereDistance a r a = ContinuousMap.const _ r := by
  ext ζ
  exact (by simpa [sphereDistance, dist_eq_norm, norm_sub_rev] using ζ.property)

/-- Squared distances form a polynomial with values in the continuous functions. -/
lemma sphereDistance_sq_analytic {n : ℕ} (a : Space n) (r : ℝ) (x : Space n) :
    AnalyticAt ℝ (fun y => sphereDistance a r y * sphereDistance a r y) x := by
  let c : Fin n → C(sphere a r, ℝ) := fun i =>
    ⟨fun ζ => (ζ : Space n) i, by fun_prop⟩
  let L : Fin n → Space n →L[ℝ] C(sphere a r, ℝ) := fun i =>
    (ContinuousLinearMap.const ℝ (sphere a r)).comp
      ((PiLp.proj 2 (fun _ : Fin n => ℝ) i) : Space n →L[ℝ] ℝ)
  have h : AnalyticAt ℝ (fun y => ∑ i : Fin n, (L i y - c i) ^ 2) x :=
    Finset.analyticAt_fun_sum Finset.univ (fun i _ => ((L i).analyticAt x |>.sub analyticAt_const).pow 2)
  convert h using 1
  funext y
  ext ζ
  simp only [sphereDistance, ContinuousMap.mul_apply, ContinuousMap.coe_mk,
    ContinuousMap.sum_apply, ContinuousMap.pow_apply, ContinuousMap.sub_apply]
  rw [← pow_two, EuclideanSpace.real_norm_sq_eq]
  rfl

lemma sphereDistance_analytic {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r) :
    AnalyticAt ℝ (sphereDistance a r) a := by
  let F := C(sphere a r, ℝ)
  let i : F ≃L[ℝ] F := Units.mk0 (2 * r) (by positivity) •
    ContinuousLinearEquiv.refl ℝ F
  have hf : AnalyticAt ℝ (fun v : F => v * v) (sphereDistance a r a) :=
    analyticAt_id.mul analyticAt_id
  have hd : HasFDerivAt (fun v : F => v * v) (i : F →L[ℝ] F)
      (sphereDistance a r a) := by
    convert! (hasFDerivAt_id (𝕜 := ℝ) (sphereDistance a r a)).mul
      (hasFDerivAt_id (𝕜 := ℝ) (sphereDistance a r a)) using 1
    ext v ζ
    change (2 * r) * v ζ = sphereDistance a r a ζ * v ζ + sphereDistance a r a ζ * v ζ
    rw [sphereDistance_center]
    change (2 * r) * v ζ = r * v ζ + r * v ζ
    ring
  exact analyticAt_of_comp i hf hd (sphereDistance_continuous a r).continuousAt
    (sphereDistance_sq_analytic a r a)

/-- The kernel as an element of the Banach algebra of continuous boundary functions.
`Ring.inverse` agrees with pointwise reciprocals whenever the denominator is a unit. -/
def kernelMap {n : ℕ} (a : Space n) (r : ℝ) (x : Space n) : C(sphere a r, ℝ) :=
  ContinuousMap.const _ (r ^ 2 - ‖x - a‖ ^ 2) *
    Ring.inverse (ContinuousMap.const _ (r * omega n) * sphereDistance a r x ^ n)

lemma kernelMap_analytic {n : ℕ} (hn : 1 ≤ n) (a : Space n) {r : ℝ} (hr : 0 < r) :
    AnalyticAt ℝ (kernelMap a r) a := by
  have hden : IsUnit (ContinuousMap.const (sphere a r) (r * omega n) *
      sphereDistance a r a ^ n) := by
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    intro ζ
    simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, ContinuousMap.pow_apply,
      sphereDistance_center]
    exact mul_ne_zero (mul_ne_zero hr.ne' (MeanValues.omega_pos hn).ne') (pow_ne_zero _ hr.ne')
  have hnum : AnalyticAt ℝ (fun x : Space n => r ^ 2 - ‖x - a‖ ^ 2) a :=
    (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ) :
      ContDiff ℝ ω _).contDiffAt.analyticAt
  have hi : AnalyticAt ℝ Ring.inverse
      (ContinuousMap.const (sphere a r) (r * omega n) * sphereDistance a r a ^ n) := by
    simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℝ) hden.unit)
  exact ((ContinuousLinearMap.const ℝ (sphere a r)).analyticAt _ |>.comp hnum).mul
    (hi.comp (f := fun x => ContinuousMap.const (sphere a r) (r * omega n) *
      sphereDistance a r x ^ n)
      (analyticAt_const.mul ((sphereDistance_analytic a hr).pow n)))

lemma kernelMap_apply {n : ℕ} (hn : 1 ≤ n) {a x : Space n} {r : ℝ}
    (hx : x ∈ ball a r) (ζ : sphere a r) :
    kernelMap a r x ζ = BallPoisson.kernel a r x ζ := by
  let d := ContinuousMap.const (sphere a r) (r * omega n) * sphereDistance a r x ^ n
  have hd : IsUnit d := by
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    intro η
    exact mul_ne_zero (mul_ne_zero
      (ne_of_gt (lt_of_le_of_lt dist_nonneg (mem_ball.mp hx)))
      (MeanValues.omega_pos hn).ne')
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr
        (BallPoisson.interior_ne_boundary hx η.property))))
  have he := hd.map_ringInverse (ContinuousMap.evalAlgHom ℝ ℝ ζ)
  change Ring.inverse d ζ = Ring.inverse (d ζ) at he
  change (r ^ 2 - ‖x - a‖ ^ 2) * Ring.inverse d ζ = _
  rw [he, Ring.inverse_eq_inv]
  rfl

/-- Integration of continuous sphere data as a bounded real-linear map. -/
def surfaceIntegralCLM {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) {r : ℝ} (hr : 0 < r) : C(sphere a r, 𝕜) →L[ℝ] 𝕜 := by
  let I : C(sphere a r, 𝕜) →ₗ[ℝ] 𝕜 :=
    { toFun := fun g => ∫ ζ, BallPoisson.boundaryValue a r g ζ ∂sphereSurface a r
      map_add' := by
        intro f g
        rw [← integral_add
          (BallPoisson.sphereSurface_integrable_of_continuousOn hr
            (BallPoisson.boundaryValue_continuousOn a r f))
          (BallPoisson.sphereSurface_integrable_of_continuousOn hr
            (BallPoisson.boundaryValue_continuousOn a r g))]
        apply integral_congr_ae
        filter_upwards [BallPoisson.sphereSurface_ae_mem a hr] with ζ hζ
        simp only [BallPoisson.boundaryValue_coe a r _ ⟨ζ, hζ⟩,
          ContinuousMap.add_apply]
      map_smul' := by
        intro c f
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [BallPoisson.sphereSurface_ae_mem a hr] with ζ hζ
        simp only [BallPoisson.boundaryValue_coe a r _ ⟨ζ, hζ⟩,
          ContinuousMap.smul_apply, RingHom.id_apply] }
  refine I.mkContinuous ((sphereSurface a r).real univ) (fun g => ?_)
  rw [mul_comm]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [BallPoisson.sphereSurface_ae_mem a hr] with ζ hζ
  rw [show BallPoisson.boundaryValue a r g ζ = g ⟨ζ, hζ⟩ from
    BallPoisson.boundaryValue_coe a r g ⟨ζ, hζ⟩]
  exact g.norm_coe_le_norm _

/-- Multiplication by fixed boundary data is bounded in the supremum norm. -/
def boundaryMultiplyCLM {S : Type*} [TopologicalSpace S] [CompactSpace S]
    {𝕜 : Type} [RCLike 𝕜] (g : C(S, 𝕜)) : C(S, ℝ) →L[ℝ] C(S, 𝕜) := by
  let L : C(S, ℝ) →ₗ[ℝ] C(S, 𝕜) :=
    { toFun := fun f => f • g
      map_add' := fun f h => add_smul f h g
      map_smul' := fun c f => by ext ζ; simp [smul_smul] }
  refine L.mkContinuous ‖g‖ (fun f => ?_)
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro ζ
  change ‖f ζ • g ζ‖ ≤ ‖g‖ * ‖f‖
  rw [norm_smul, mul_comm]
  exact mul_le_mul (g.norm_coe_le_norm ζ) (f.norm_coe_le_norm ζ)
    (norm_nonneg _) (norm_nonneg _)

lemma poissonIntegral_analytic {n : ℕ} (hn : 2 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) {r : ℝ} (hr : 0 < r) (g : C(sphere a r, 𝕜)) :
    AnalyticAt ℝ (BallPoisson.poissonIntegral a r g) a := by
  have h := (surfaceIntegralCLM (𝕜 := 𝕜) a hr).analyticAt _ |>.comp
    ((boundaryMultiplyCLM g).analyticAt _ |>.comp
      (kernelMap_analytic (by omega) a hr))
  apply h.congr
  filter_upwards [ball_mem_nhds a hr] with x hx
  apply integral_congr_ae
  filter_upwards [BallPoisson.sphereSurface_ae_mem a hr] with ζ hζ
  change BallPoisson.boundaryValue a r (kernelMap a r x • g) ζ =
    BallPoisson.kernel a r x ζ • BallPoisson.boundaryValue a r g ζ
  rw [show BallPoisson.boundaryValue a r (kernelMap a r x • g) ζ =
      (kernelMap a r x • g) ⟨ζ, hζ⟩ from
      BallPoisson.boundaryValue_coe a r _ ⟨ζ, hζ⟩]
  simp only [ContinuousMap.smul_apply']
  rw [kernelMap_apply (by omega) hx ⟨ζ, hζ⟩,
    BallPoisson.boundaryValue_coe a r g ⟨ζ, hζ⟩]

/-- In dimension one the zero Laplacian forces the entire second derivative to vanish. -/
lemma harmonic_one_second_derivative {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain 1) (u : Space 1 → 𝕜) (hu : MeanValues.IsHarmonic Ω u)
    {x : Space 1} (hx : x ∈ Ω) : fderiv ℝ (fderiv ℝ u) x = 0 := by
  let e : Space 1 := coordinate 1 0
  have he : fderiv ℝ (fderiv ℝ u) x e e = 0 := by
    have hl := hu.2 x hx
    rw [MeanValues.laplacian_bridge u x (hu.1.contDiffAt (Ω.isOpen.mem_nhds hx)),
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
        (EuclideanSpace.basisFun (Fin 1) ℝ)] at hl
    simpa [Fin.sum_univ_succ, iteratedFDeriv_two_apply, e, coordinate,
      P201Specs.coordinate, P102.U4.coordinateVector] using hl
  have hv (v : Space 1) : v = v 0 • e := by
    ext i
    fin_cases i
    simp [e, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  ext v w
  rw [hv v, hv w]
  simp only [map_smul, smul_apply, he, smul_zero,
    zero_apply]

/-- A one-dimensional harmonic function agrees locally with its affine tangent. -/
lemma harmonic_one_analytic {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain 1) (u : Space 1 → 𝕜) (hu : MeanValues.IsHarmonic Ω u) :
    AnalyticOnNhd ℝ u (Ω : Set (Space 1)) := by
  intro a ha
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp Ω.isOpen a ha
  have hfd : DifferentiableOn ℝ (fderiv ℝ u) (ball a r) := by
    intro x hx
    exact ((hu.1.contDiffAt (Ω.isOpen.mem_nhds (hsub hx))).fderiv_right
      (m := 1) (by norm_num)).differentiableAt one_ne_zero |>.differentiableWithinAt
  have hconst : ∀ x ∈ ball a r, fderiv ℝ u x = fderiv ℝ u a := by
    intro x hx
    exact isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball a r).isPreconnected hfd
      (fun y hy => harmonic_one_second_derivative Ω u hu (hsub hy)) hx (mem_ball_self hr)
  let v : Space 1 → 𝕜 := fun x => u a + fderiv ℝ u a (x - a)
  have hv : AnalyticAt ℝ v a :=
    analyticAt_const.add ((fderiv ℝ u a).analyticAt _ |>.comp
      (analyticAt_id.sub analyticAt_const))
  have hderiv : ∀ x, HasFDerivAt v (fderiv ℝ u a) x := by
    intro x
    simpa [v] using ((fderiv ℝ u a).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const a)).const_add (u a)
  have heq : EqOn u v (ball a r) :=
    isOpen_ball.eqOn_of_fderiv_eq (convex_ball a r).isPreconnected
      (hu.1.differentiableOn (by norm_num) |>.mono hsub)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt)
      (fun x hx => (hconst x hx).trans (hderiv x).fderiv.symm)
      (mem_ball_self hr) (by simp [v])
  apply hv.congr
  filter_upwards [ball_mem_nhds a hr] with x hx
  exact (heq hx).symm

/-- Harmonic functions in dimensions at least two inherit analyticity from Poisson representation. -/
lemma harmonic_analytic_of_two_le {n : ℕ} (hn : 2 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hu : MeanValues.IsHarmonic Ω u) :
    AnalyticOnNhd ℝ u (Ω : Set (Space n)) := by
  intro a ha
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds ha)
  obtain ⟨g, _, heq, _⟩ := BallPoisson.representation hn a (r / 2) (by positivity) Ω u
    ((closedBall_subset_ball (by linarith)).trans hsub) hu
  apply (poissonIntegral_analytic hn a (by positivity : 0 < r / 2) g).congr
  filter_upwards [ball_mem_nhds a (by positivity : 0 < r / 2)] with x hx
  exact (heq hx).symm

/-- paper.tex, cor:pde-harmonic-analytic: real analyticity in every n ≥ 1. -/
theorem analyticity : P201Specs.AnalyticContinuation.AnalyticityStatement := by
  intro n hn 𝕜 _ Ω u hu
  by_cases h : n = 1
  · subst n
    exact harmonic_one_analytic Ω u hu
  · exact harmonic_analytic_of_two_le (by omega) Ω u hu

/-- paper.tex, cor:pde-harmonic-analytic: continuation on connected open sets. -/
theorem continuation : P201Specs.AnalyticContinuation.ContinuationStatement := by
  intro n hn 𝕜 _ Ω u v hΩ hu hv V hV hne hsub heq
  obtain ⟨a, ha⟩ := hne
  apply (analyticity hn Ω u hu).eqOn_of_preconnected_of_eventuallyEq
    (analyticity hn Ω v hv) hΩ.isPreconnected (hsub ha)
  filter_upwards [hV.mem_nhds ha] with x hx
  exact heq hx

end P201.AnalyticContinuation
