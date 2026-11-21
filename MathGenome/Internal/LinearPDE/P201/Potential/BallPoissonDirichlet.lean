import MathGenome.Internal.LinearPDE.P201Specs.Potential.BallPoissonDirichlet
import MathGenome.Internal.LinearPDE.P201.Potential.BallGreen
import MathGenome.Internal.LinearPDE.P201.Potential.NewtonPotential

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology
namespace P201.BallPoissonDirichlet

abbrev volumePotential : P201Specs.BallPoissonDirichlet.VolumePotentialType :=
  @P201Specs.BallPoissonDirichlet.volumePotential

/-- The smooth correction, in the symmetric formula valid at the center. -/
def correction {n : ℕ} (a : Space n) (r : ℝ) (x y : Space n) : ℝ :=
  P201Specs.fundamentalProfile n
    (Real.sqrt (BallGreen.symmetricPolynomial r (x-a) (y-a)) / r)

theorem correction_comm {n : ℕ} (a : Space n) (r : ℝ) (x y : Space n) :
    correction a r x y = correction a r y x := by
  simp only [correction, BallGreen.symmetricPolynomial_comm r (x-a) (y-a)]

theorem correction_joint_continuousOn {n : ℕ} {a : Space n} {r : ℝ}
    (hr : 0 < r) (K : Set (Space n)) (hK : K ⊆ ball a r) :
    ContinuousOn (fun p : Space n × Space n => correction a r p.1 p.2)
      (closedBall a r ×ˢ K) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hq : 0 < BallGreen.symmetricPolynomial r (p.1-a) (p.2-a) := by
    rw [BallGreen.symmetricPolynomial_comm]
    exact BallGreen.symmetricPolynomial_pos hr (hK hp.2) hp.1
  have hrad : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Space n × Space n =>
      Real.sqrt (BallGreen.symmetricPolynomial r (p.1-a) (p.2-a)) / r) p :=
    ((BallGreen.symmetricPolynomial_contDiff a r).contDiffAt.sqrt hq.ne').div_const r
  exact ((BallGreen.profile_contDiffAt n
    (div_pos (Real.sqrt_pos.mpr hq) hr).ne').comp p hrad).continuousAt

/-- A continuous integrand on a compact product has a continuous parameter integral,
including at the boundary of the parameter set. -/
theorem compact_integral_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {S K : Set (Space n)} (hS : IsCompact S) (hK : IsCompact K)
    (F : Space n → Space n → 𝕜)
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ K)) :
    ContinuousOn (fun x => ∫ y in K, F x y) S := by
  obtain ⟨C, hC⟩ := (hS.prod hK).bddAbove_image hF.norm
  apply continuousOn_of_dominated (bound := fun _ => C)
  · intro x hx
    exact ((hF.comp (continuousOn_const.prodMk continuousOn_id)
      (fun y hy => ⟨hx, hy⟩)).integrableOn_compact hK).aestronglyMeasurable
  · intro x hx
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact hC (mem_image_of_mem _ (show (x, y) ∈ S ×ˢ K from ⟨hx, hy⟩))
  · exact integrableOn_const hK.measure_ne_top
  · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact hF.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨hx, hy⟩)

/-- Integrating harmonic functions over a compact set preserves their ball mean values. -/
theorem compact_integral_harmonic {n : ℕ} (hn : 1 ≤ n)
    {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) {K : Set (Space n)} (hK : IsCompact K)
    (F : Space n → Space n → 𝕜)
    (hF : ContinuousOn (Function.uncurry F) ((Ω : Set _) ×ˢ K))
    (hh : ∀ y ∈ K, MeanValues.IsHarmonic Ω (fun x => F x y)) :
    MeanValues.IsHarmonic Ω (fun x => ∫ y in K, F x y) := by
  have hc : ContinuousOn (fun x => ∫ y in K, F x y) Ω := by
    intro x hx
    obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hx)
    have hsub : closedBall x (ε/2) ⊆ (Ω : Set _) :=
      (closedBall_subset_ball (by linarith)).trans hεΩ
    have hlocal := compact_integral_continuousOn (isCompact_closedBall x (ε/2)) hK F
      (hF.mono (Set.prod_mono hsub Subset.rfl))
    exact (hlocal.continuousAt (closedBall_mem_nhds x (half_pos hε))).continuousWithinAt
  apply (MeanValues.ball_converse hn Ω _ hc ?_).2
  intro b s hs hball
  have hi := (hF.mono (Set.prod_mono hball Subset.rfl)).integrableOn_compact
    (μ := (volume.restrict (ball b s)).prod (volume.restrict K))
    ((isCompact_closedBall b s).prod hK)
  have hsupport : ∀ᵐ p ∂(volume.restrict (ball b s)).prod (volume.restrict K),
      p ∈ closedBall b s ×ˢ K := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (isClosed_closedBall.measurableSet.prod hK.measurableSet)).mpr
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact ⟨ball_subset_closedBall hx, hy⟩
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hsupport] at hi
  change (∫ y in K, F b y) =
    (volume.real (ball b s))⁻¹ • ∫ x in ball b s, ∫ y in K, F x y
  rw [integral_integral_swap hi, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
  exact (MeanValues.mean_values hn Ω _ (hh y hy) b s hs hball).2

/-- Forgetting the support domain does not change the test function. -/
def globalTest {n : ℕ} {a : Space n} {r : ℝ}
    (f : Test ℝ ⟨ball a r, isOpen_ball⟩) : Test ℝ (⊤ : Domain n) :=
  ⟨f, f.contDiff, f.hasCompactSupport, subset_univ _⟩

def correctionIntegral {n : ℕ} (a : Space n) (r : ℝ)
    (f : Test ℝ ⟨ball a r, isOpen_ball⟩) (x : Space n) : ℝ :=
  ∫ y in tsupport f, correction a r x y * f y

theorem correction_weight_continuousOn {n : ℕ} {a : Space n} {r : ℝ}
    (hr : 0 < r) (f : Test ℝ ⟨ball a r, isOpen_ball⟩) :
    ContinuousOn (fun p : Space n × Space n => correction a r p.1 p.2 * f p.2)
      (closedBall a r ×ˢ tsupport f) :=
  (correction_joint_continuousOn hr _ f.tsupport_subset).mul
    (f.continuous.comp continuous_snd).continuousOn

theorem correctionIntegral_continuousOn {n : ℕ} {a : Space n} {r : ℝ}
    (hr : 0 < r) (f : Test ℝ ⟨ball a r, isOpen_ball⟩) :
    ContinuousOn (correctionIntegral a r f) (closedBall a r) :=
  compact_integral_continuousOn (isCompact_closedBall a r) f.hasCompactSupport _
    (correction_weight_continuousOn hr f)

theorem correctionIntegral_harmonic {n : ℕ} (hn : 2 ≤ n) {a : Space n} {r : ℝ}
    (hr : 0 < r) (f : Test ℝ ⟨ball a r, isOpen_ball⟩) :
    MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ (correctionIntegral a r f) := by
  apply compact_integral_harmonic (by omega) _ f.hasCompactSupport
    (fun x y => correction a r x y * f y)
    ((correction_weight_continuousOn hr f).mono
      (Set.prod_mono ball_subset_closedBall Subset.rfl))
  intro y hy
  have hh := BallGreen.correction_harmonic hn a r hr y (f.tsupport_subset hy)
  have he : (fun x => correction a r x y * f y) =
      (fun x => correction a r y x • f y) := by
    funext x
    rw [correction_comm]
    rfl
  rw [he]
  exact (MeanValues.harmonic_bridge _ _).mpr
    (((MeanValues.harmonic_bridge _ _).mp hh).comp_CLM
      (ContinuousLinearMap.toSpanSingleton ℝ (f y)))

theorem fundamental_weight_integrable {n : ℕ} (hn : 1 ≤ n) {a : Space n} {r : ℝ}
    (f : Test ℝ ⟨ball a r, isOpen_ball⟩) (x : Space n) :
    Integrable (fun y => P201Specs.fundamentalKernel n (y-x) * f y) volume :=
  (BallGreen.fundamental_translate_locallyIntegrable hn x).integrable_smul_right_of_hasCompactSupport
    f.continuous f.hasCompactSupport

/-- Reflection and translation turn the ordinary Newton convolution into its source-variable form. -/
theorem newton_integral {n : ℕ} {a : Space n} {r : ℝ}
    (f : Test ℝ ⟨ball a r, isOpen_ball⟩) (x : Space n) :
    newtonPotential (globalTest f) x =
      ∫ y, P201Specs.fundamentalKernel n (y-x) * f y := by
  calc
    _ = ∫ y, P201Specs.fundamentalKernel n ((x-y)-x) * f (x-y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        simp [globalTest,
          P201Specs.fundamentalKernel, show x-y-x = -y by abel])
    _ = _ := integral_sub_left_eq_self
      (fun y => P201Specs.fundamentalKernel n (y-x) * f y) volume x

theorem correction_weight_integrable {n : ℕ} {a x : Space n} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ closedBall a r) (f : Test ℝ ⟨ball a r, isOpen_ball⟩) :
    Integrable (fun y => correction a r x y * f y) volume := by
  apply (integrableOn_iff_integrable_of_support_subset
    (s := tsupport f) (Function.support_subset_iff'.mpr ?_)).mp
  · exact ((correction_weight_continuousOn hr f).comp
      (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨hx, hy⟩)).integrableOn_compact
        f.hasCompactSupport
  · intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

theorem volume_decomposition {n : ℕ} (hn : 1 ≤ n) {a x : Space n} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ closedBall a r) (f : Test ℝ ⟨ball a r, isOpen_ball⟩) :
    volumePotential a r f x = newtonPotential (globalTest f) x - correctionIntegral a r f x := by
  have hi := fundamental_weight_integrable hn f x
  have hc := correction_weight_integrable hr hx f
  have hzero (y : Space n) (hy : y ∉ ball a r) : f y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (f.tsupport_subset h))
  unfold volumePotential P201Specs.BallPoissonDirichlet.volumePotential
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => by rw [hzero y hy, mul_zero])]
  simp_rw [P201Specs.BallGreen.kernel, sub_mul]
  change (∫ y, P201Specs.fundamentalKernel n (y-x) * f y - correction a r x y * f y) = _
  rw [integral_sub hi hc, newton_integral]
  congr 1
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => by rw [image_eq_zero_of_notMem_tsupport hy, mul_zero])).symm

/-- Additivity and locality for the canonical coordinate Laplacian. -/
theorem laplacian_sub {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u v : Space n → 𝕜) (x : Space n)
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    P201Specs.laplacian (u-v) x = P201Specs.laplacian u x - P201Specs.laplacian v x := by
  have e1 : P201Specs.laplacian (u-v) x = Laplacian.laplacian (u-v) x :=
    MeanValues.laplacian_bridge _ _ (hu.sub hv)
  have e2 : P201Specs.laplacian u x = Laplacian.laplacian u x :=
    MeanValues.laplacian_bridge _ _ hu
  have e3 : P201Specs.laplacian v x = Laplacian.laplacian v x :=
    MeanValues.laplacian_bridge _ _ hv
  rw [e1, hu.laplacian_sub hv, e2, e3]

theorem laplacian_add {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u v : Space n → 𝕜) (x : Space n)
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    P201Specs.laplacian (u+v) x = P201Specs.laplacian u x + P201Specs.laplacian v x := by
  have e1 : P201Specs.laplacian (u+v) x = Laplacian.laplacian (u+v) x :=
    MeanValues.laplacian_bridge _ _ (hu.add hv)
  have e2 : P201Specs.laplacian u x = Laplacian.laplacian u x :=
    MeanValues.laplacian_bridge _ _ hu
  have e3 : P201Specs.laplacian v x = Laplacian.laplacian v x :=
    MeanValues.laplacian_bridge _ _ hv
  rw [e1, hu.laplacian_add hv, e2, e3]

theorem laplacian_congr {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u v : Space n → 𝕜} {x : Space n} (hu : ContDiffAt ℝ 2 u x)
    (hv : ContDiffAt ℝ 2 v x) (he : u =ᶠ[𝓝 x] v) :
    P201Specs.laplacian u x = P201Specs.laplacian v x := by
  have e1 : P201Specs.laplacian u x = Laplacian.laplacian u x :=
    MeanValues.laplacian_bridge _ _ hu
  have e2 : P201Specs.laplacian v x = Laplacian.laplacian v x :=
    MeanValues.laplacian_bridge _ _ hv
  rw [e1, e2]
  exact (InnerProductSpace.laplacian_congr_nhds he).eq_of_nhds

/-- The compact source gives a correction continuous on the entire closed ball. -/
theorem volume_potential : P201Specs.BallPoissonDirichlet.VolumePotentialStatement := by
  intro n hn a r hr f
  have hN : ContDiff ℝ (⊤ : ℕ∞) (newtonPotential (globalTest f)) :=
    newtonSmooth n (by omega) _
  have hC := correctionIntegral_harmonic hn hr f
  have hV : ContDiffOn ℝ 2 (volumePotential a r f) (ball a r) :=
    (((hN.of_le (by simp)).contDiffOn).sub hC.1).congr
      (fun x hx => volume_decomposition (by omega) hr (ball_subset_closedBall hx) f)
  refine ⟨?_, hV, ?_, ?_, ?_⟩
  · intro x hx
    have hi := (fundamental_weight_integrable (by omega) f x).sub
      (correction_weight_integrable hr hx f)
    apply (hi.integrableOn).congr_fun _ measurableSet_ball
    intro y _
    simp only [P201Specs.BallGreen.kernel, correction, sub_mul, Pi.sub_apply]
  · exact (hN.continuous.continuousOn.sub (correctionIntegral_continuousOn hr f)).congr
      (fun x hx => volume_decomposition (by omega) hr hx f)
  · intro x hx
    have hxN : ContDiffAt ℝ 2 (newtonPotential (globalTest f)) x :=
      hN.contDiffAt.of_le (by simp)
    have hxC := hC.1.contDiffAt (isOpen_ball.mem_nhds hx)
    have he : volumePotential a r f =ᶠ[𝓝 x]
        (newtonPotential (globalTest f) - correctionIntegral a r f) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact volume_decomposition (by omega) hr (ball_subset_closedBall hy) f
    erw [laplacian_congr (hV.contDiffAt (isOpen_ball.mem_nhds hx)) (hxN.sub hxC) he,
      laplacian_sub _ _ x hxN hxC, hC.2 x hx, sub_zero]
    exact newtonEquation n (by omega) (globalTest f) x
  · intro ζ hζ
    change (∫ y in ball a r, P201Specs.BallGreen.kernel a r ζ y * f y) = 0
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    rw [BallGreen.symmetry hn a r hr ζ y, BallGreen.boundary_zero hn a r hr y hy ζ hζ,
      zero_mul]

/-- Existence uses the Green volume potential and the continuous Poisson extension.
Uniqueness uses harmonicity of the difference and the maximum principle. -/
theorem poisson_dirichlet : P201Specs.BallPoissonDirichlet.PoissonDirichletStatement := by
  intro n hn a r hr f g
  let V := volumePotential a r f
  let H := BallPoisson.poissonExtension a r g
  have hV := volume_potential hn a r hr f
  have hH := BallPoisson.poissonExtension_harmonic hn a hr g
  have hcH := BallPoisson.continuous_extension hn a r hr g
  have hU : P201Specs.BallPoissonDirichlet.IsSolution a r f g (V+H) := by
    refine ⟨hV.2.1.add hH.1, hV.2.2.1.add hcH.1, ?_, ?_⟩
    · intro x hx
      erw [laplacian_add V H x
        (hV.2.1.contDiffAt (isOpen_ball.mem_nhds hx))
        (hH.1.contDiffAt (isOpen_ball.mem_nhds hx)), hH.2 x hx, add_zero]
      exact hV.2.2.2.1 x hx
    · intro ζ
      change volumePotential a r f ζ + BallPoisson.poissonExtension a r g ζ = g ζ
      exact (congrArg₂ (· + ·) (hV.2.2.2.2 ζ ζ.property) (hcH.2 ζ)).trans (zero_add _)
  refine ⟨V+H, hU, ?_, ?_⟩
  · intro x hx
    change V x + BallPoisson.poissonExtension a r g x = V x + BallPoisson.poissonIntegral a r g x
    erw [BallPoisson.poissonExtension_interior a r g hx]
  · intro v hv
    let w := v - (V+H)
    have hw : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ w := by
      refine ⟨hv.1.sub hU.1, ?_⟩
      intro x hx
      change P201Specs.laplacian (v - (V+H)) x = 0
      erw [laplacian_sub v (V+H) x (hv.1.contDiffAt (isOpen_ball.mem_nhds hx))
        (hU.1.contDiffAt (isOpen_ball.mem_nhds hx))]
      have hvE := hv.2.2.1 x hx
      have huE := hU.2.2.1 x hx
      linarith
    have hz := BallPoisson.harmonic_zero_closedBall_real (by omega) a r hr w hw
      (hv.2.1.sub hU.2.1) (fun ζ hζ => by
        change v ζ - (V+H) ζ = 0
        rw [hv.2.2.2 ⟨ζ, hζ⟩, hU.2.2.2 ⟨ζ, hζ⟩, sub_self])
    intro x hx
    exact sub_eq_zero.mp (hz hx)

abbrev scalarVolumePotential : P201Specs.BallPoissonDirichlet.ScalarVolumePotentialType :=
  @P201Specs.BallPoissonDirichlet.scalarVolumePotential

/-- Postcomposition preserves the actual compact smooth source class. -/
def realPartTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Domain n}
    (f : Test 𝕜 Ω) : Test ℝ Ω := TestFunction.postcompCLM RCLike.reCLM f

def imagPartTest {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Domain n}
    (f : Test 𝕜 Ω) : Test ℝ Ω := TestFunction.postcompCLM RCLike.imCLM f

theorem scalar_decomposition {𝕜 : Type} [RCLike 𝕜] (z : 𝕜) :
    z = RCLike.re z • (1 : 𝕜) + RCLike.im z • RCLike.I := by
  simpa only [RCLike.real_smul_eq_coe_mul, mul_one] using (RCLike.re_add_im z).symm

theorem laplacian_smul_const {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : Space n → ℝ) (c : 𝕜) (x : Space n) (hu : ContDiffAt ℝ 2 u x) :
    P201Specs.laplacian (fun z => u z • c) x = P201Specs.laplacian u x • c := by
  let l := ContinuousLinearMap.toSpanSingleton ℝ c
  have he : ContDiffAt ℝ 2 (l ∘ u) x := l.contDiff.contDiffAt.comp x hu
  have h1 : P201Specs.laplacian (l ∘ u) x = Laplacian.laplacian (l ∘ u) x :=
    MeanValues.laplacian_bridge _ _ he
  have h2 : P201Specs.laplacian u x = Laplacian.laplacian u x :=
    MeanValues.laplacian_bridge _ _ hu
  change P201Specs.laplacian (l ∘ u) x = l (P201Specs.laplacian u x)
  rw [h1, hu.laplacian_CLM_comp_left, h2]
  rfl

theorem scalar_integrand_decomposition {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : Space n} {r : ℝ} (f : Test 𝕜 ⟨ball a r, isOpen_ball⟩) (x y : Space n) :
    P201Specs.BallGreen.kernel a r x y • f y =
      (P201Specs.BallGreen.kernel a r x y * realPartTest f y) • (1 : 𝕜) +
      (P201Specs.BallGreen.kernel a r x y * imagPartTest f y) • RCLike.I := by
  change P201Specs.BallGreen.kernel a r x y • f y =
    (P201Specs.BallGreen.kernel a r x y * RCLike.re (f y)) • (1 : 𝕜) +
    (P201Specs.BallGreen.kernel a r x y * RCLike.im (f y)) • RCLike.I
  conv_lhs => rw [scalar_decomposition (f y)]
  rw [smul_add, smul_smul, smul_smul]

theorem scalar_volume_decomposition {n : ℕ} (hn : 2 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    {a x : Space n} {r : ℝ} (hr : 0 < r) (hx : x ∈ closedBall a r)
    (f : Test 𝕜 ⟨ball a r, isOpen_ball⟩) :
    scalarVolumePotential a r f x = volumePotential a r (realPartTest f) x • (1 : 𝕜) +
      volumePotential a r (imagPartTest f) x • RCLike.I := by
  have hiR := ((volume_potential hn a r hr (realPartTest f)).1 x hx).smul_const (1 : 𝕜)
  have hiI := ((volume_potential hn a r hr (imagPartTest f)).1 x hx).smul_const
    (RCLike.I : 𝕜)
  change (∫ y in ball a r, P201Specs.BallGreen.kernel a r x y • f y) = _
  simp_rw [scalar_integrand_decomposition f x]
  rw [integral_add hiR hiI, integral_smul_const, integral_smul_const]
  rfl

/-- Complexification is performed on the source and the integral, not on an
assumed solution certificate. -/
theorem scalar_volume_potential :
    P201Specs.BallPoissonDirichlet.ScalarVolumePotentialStatement := by
  intro n hn 𝕜 _ a r hr f
  let R := volumePotential a r (realPartTest f)
  let I := volumePotential a r (imagPartTest f)
  let V : Space n → 𝕜 := fun x => R x • (1 : 𝕜) + I x • RCLike.I
  have hR := volume_potential hn a r hr (realPartTest f)
  have hI := volume_potential hn a r hr (imagPartTest f)
  have hreg : ContDiffOn ℝ 2 V (ball a r) :=
    (hR.2.1.smul contDiffOn_const).add (hI.2.1.smul contDiffOn_const)
  have hcont : ContinuousOn V (closedBall a r) :=
    (hR.2.2.1.smul continuousOn_const).add (hI.2.2.1.smul continuousOn_const)
  have hEq : EqOn (scalarVolumePotential a r f) V (closedBall a r) :=
    fun x hx => scalar_volume_decomposition hn hr hx f
  have hregS : ContDiffOn ℝ 2 (scalarVolumePotential a r f) (ball a r) :=
    hreg.congr (fun x hx => hEq (ball_subset_closedBall hx))
  refine ⟨?_, hregS, hcont.congr hEq, ?_, ?_⟩
  · intro x hx
    have hiR := (hR.1 x hx).smul_const (1 : 𝕜)
    have hiI := (hI.1 x hx).smul_const (RCLike.I : 𝕜)
    exact IntegrableOn.congr_fun (hiR.add hiI)
      (fun y _ => (scalar_integrand_decomposition f x y).symm) measurableSet_ball
  · intro x hx
    have hxR := hR.2.1.contDiffAt (isOpen_ball.mem_nhds hx)
    have hxI := hI.2.1.contDiffAt (isOpen_ball.mem_nhds hx)
    have he : scalarVolumePotential a r f =ᶠ[𝓝 x] V := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hEq (ball_subset_closedBall hy)
    have hl := laplacian_congr (hregS.contDiffAt (isOpen_ball.mem_nhds hx))
      (hreg.contDiffAt (isOpen_ball.mem_nhds hx)) he
    rw [hl]
    change -P201Specs.laplacian ((fun x => R x • (1 : 𝕜)) +
      (fun x => I x • (RCLike.I : 𝕜))) x = f x
    rw [laplacian_add (fun z => R z • (1 : 𝕜)) (fun z => I z • (RCLike.I : 𝕜)) x
      (hxR.smul contDiffAt_const) (hxI.smul contDiffAt_const),
      laplacian_smul_const R (1 : 𝕜) x hxR,
      laplacian_smul_const I (RCLike.I : 𝕜) x hxI, neg_add,
      ← neg_smul, ← neg_smul]
    change (-P201Specs.laplacian (volumePotential a r (realPartTest f)) x) • (1 : 𝕜) +
      (-P201Specs.laplacian (volumePotential a r (imagPartTest f)) x) • RCLike.I = f x
    rw [hR.2.2.2.1 x hx, hI.2.2.2.1 x hx]
    exact (scalar_decomposition (f x)).symm
  · intro ζ hζ
    apply (hEq (sphere_subset_closedBall hζ)).trans
    change R ζ • (1 : 𝕜) + I ζ • RCLike.I = 0
    have hζR : R ζ = 0 := hR.2.2.2.2 ζ hζ
    have hζI : I ζ = 0 := hI.2.2.2.2 ζ hζ
    rw [hζR, hζI, zero_smul, zero_smul, add_zero]

/-- The full theorem for both real and complex data, with derivatives over ℝ. -/
theorem scalar_poisson_dirichlet :
    P201Specs.BallPoissonDirichlet.ScalarPoissonDirichletStatement := by
  intro n hn 𝕜 _ a r hr f g
  let V := scalarVolumePotential a r f
  let H := BallPoisson.poissonExtension a r g
  have hV := scalar_volume_potential hn a r hr f
  have hH := BallPoisson.poissonExtension_harmonic hn a hr g
  have hcH := BallPoisson.continuous_extension hn a r hr g
  have hU : P201Specs.BallPoissonDirichlet.ScalarIsSolution a r f g (V+H) := by
    refine ⟨hV.2.1.add hH.1, hV.2.2.1.add hcH.1, ?_, ?_⟩
    · intro x hx
      rw [laplacian_add V H x
        (hV.2.1.contDiffAt (isOpen_ball.mem_nhds hx))
        (hH.1.contDiffAt (isOpen_ball.mem_nhds hx)), hH.2 x hx, add_zero]
      exact hV.2.2.2.1 x hx
    · intro ζ
      exact (congrArg₂ (· + ·) (hV.2.2.2.2 ζ ζ.property) (hcH.2 ζ)).trans (zero_add _)
  refine ⟨V+H, hU, ?_, ?_⟩
  · intro x hx
    exact congrArg (fun z => V x + z) (BallPoisson.poissonExtension_interior a r g hx)
  · intro v hv
    let w := v - (V+H)
    have hw : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ w := by
      refine ⟨hv.1.sub hU.1, ?_⟩
      intro x hx
      change P201Specs.laplacian (v - (V+H)) x = 0
      rw [laplacian_sub v (V+H) x (hv.1.contDiffAt (isOpen_ball.mem_nhds hx))
        (hU.1.contDiffAt (isOpen_ball.mem_nhds hx))]
      exact sub_eq_zero.mpr (neg_injective ((hv.2.2.1 x hx).trans (hU.2.2.1 x hx).symm))
    have hzero : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩
        (fun _ : Space n => (0 : 𝕜)) :=
      (MeanValues.harmonic_bridge _ _).mpr (InnerProductSpace.harmonicOnNhd_const _)
    have hz := BallPoisson.harmonic_eqOn_closedBall (by omega) a r hr w (fun _ => 0)
      hw hzero (hv.2.1.sub hU.2.1) continuousOn_const (fun ζ hζ => by
        change v ζ - (V+H) ζ = 0
        rw [hv.2.2.2 ⟨ζ, hζ⟩, hU.2.2.2 ⟨ζ, hζ⟩, sub_self])
    intro x hx
    exact sub_eq_zero.mp (hz hx)

theorem normal_derivative : P201Specs.BallPoissonDirichlet.NormalDerivativeStatement :=
  BallGreen.normal_derivative

end P201.BallPoissonDirichlet
