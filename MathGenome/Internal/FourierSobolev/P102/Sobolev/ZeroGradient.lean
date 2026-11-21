import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.ZeroGradient
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionMollification
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section
open Set TopologicalSpace MeasureTheory Filter Metric
open scoped ContDiff Distributions Topology
namespace P102.Sobolev
open P102.U4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Moving one derivative from the kernel to the distribution. -/
theorem convolution_coordinate_eq_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω)
    (hT : ∀ i : Fin d, distributionPartial {i} T = 0)
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (x : Space d)
    (hx : x ∈ convolutionDomain Ω ρ) (i : Fin d) :
    fderiv ℝ (localConvolution T ρ) x (coordinateVector d i) = 0 := by
  rw [localConvolution_coordinate_derivative T ρ i x hx]
  have hx' : x ∈ convolutionDomain Ω (testPartialWord ⊤ [i] ρ) := by
    intro z hz
    exact hx z (testPartialWord_tsupport_subset ⊤ [i] ρ hz)
  rw [localConvolution_pairing d 𝕜 Ω T _ x hx']
  have htest : testPartialWord Ω [i] (convolutionTest ρ x hx) =
      -(convolutionTest (testPartialWord ⊤ [i] ρ) x hx') := by
    ext y
    rw [testPartialWord_coe]
    change partialWord (fun y => ρ (x - y)) [i] y = _
    rw [partialWord_const_sub ρ.contDiff]
    change (-1 : 𝕜) ^ [i].length * partialWord ρ [i] (x - y) =
      -(testPartialWord ⊤ [i] ρ (x - y))
    rw [testPartialWord_coe]
    simp
  have h := congrArg (fun S : DistributionSpace 𝕜 Ω => S (convolutionTest ρ x hx)) (hT i)
  simpa [distributionPartial, htest] using h

/-- All coordinate vectors span the Euclidean domain. -/
theorem convolution_fderiv_eq_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω)
    (hT : ∀ i : Fin d, distributionPartial {i} T = 0)
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (x : Space d)
    (hx : x ∈ convolutionDomain Ω ρ) :
    fderiv ℝ (localConvolution T ρ) x = 0 := by
  have hi (i : Fin d) : fderiv ℝ (localConvolution T ρ) x
      (EuclideanSpace.single i 1) = 0 := by
    simpa [coordinateVector] using convolution_coordinate_eq_zero T hT ρ x hx i
  ext v
  rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp [hi]

/-- A unit-mass test inside every nonempty open ball. -/
theorem exists_unit_test {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (a : Space d)
    {r : ℝ} (hr : 0 < r) :
    ∃ φ : TestSpace 𝕜 (⟨ball a r, isOpen_ball⟩ : Opens (Space d)),
      (∫ x, φ x) = 1 := by
  let b : ContDiffBump a :=
    { rIn := r / 4, rOut := r / 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let ψ : TestSpace ℝ (⟨ball a r, isOpen_ball⟩ : Opens (Space d)) :=
    ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed,
      by rw [b.tsupport_normed_eq]; exact closedBall_subset_ball (by dsimp [b]; linarith)⟩
  refine ⟨TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) ψ, ?_⟩
  change (∫ x, (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) (b.normed volume x)) = 1
  rw [ContinuousLinearMap.integral_comp_comm _ b.integrable_normed, b.integral_normed]
  simp

/-- Pairing with ambient zero-extended tests. -/
theorem regular_apply_integral {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (u : Space d → 𝕜)
    (hu : LocallyIntegrableOn u Ω volume) (φ : TestSpace 𝕜 Ω) :
    regularDistribution Ω u φ = ∫ x, u x * φ x := by
  rw [regularDistribution, TestFunction.integralAgainstBilinCLM_eq_integral hu]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- Pairing a function constant on the test support. -/
theorem integral_mul_test_of_eqOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {V : Opens (Space d)} (φ : TestSpace 𝕜 V) (g : Space d → 𝕜) (c : 𝕜)
    (hg : ∀ x ∈ V, g x = c) :
    (∫ x, g x * φ x) = c * ∫ x, φ x := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ V
  · rw [hg x hx]
  · rw [φ.zero_on_compl hx]
    simp

/-- On a relatively compact ball the distribution is a constant distribution. -/
theorem constant_pairing_on_ball {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω)
    (hT : ∀ i : Fin d, distributionPartial {i} T = 0)
    (a : Space d) {r : ℝ} (hr : 0 < r) (hB : closedBall a r ⊆ Ω) :
    ∃ c : 𝕜, ∀ φ : TestSpace 𝕜 (⟨ball a r, isOpen_ball⟩ : Opens (Space d)),
      T (TestFunction.monoCLM 𝕜 φ) = c * ∫ x, φ x := by
  let B : Opens (Space d) := ⟨ball a r, isOpen_ball⟩
  have hBO : B ≤ Ω := ball_subset_closedBall.trans hB
  obtain ⟨η, hη⟩ := exists_unit_test 𝕜 a hr
  obtain ⟨ρ₀, hρ₀⟩ := exists_unit_test 𝕜 (0 : Space d) (by norm_num : (0 : ℝ) < 1)
  let ρ : TestSpace 𝕜 (⊤ : Opens (Space d)) := TestFunction.monoCLM 𝕜 ρ₀
  have hρcoe : (ρ : Space d → 𝕜) = ρ₀ := by
    simp [ρ, TestFunction.monoCLM_apply]
  have hρ : (∫ x, ρ x) = 1 := by rw [hρcoe]; exact hρ₀
  let ext : TestSpace 𝕜 B →L[𝕜] TestSpace 𝕜 Ω := TestFunction.monoCLM 𝕜
  have hext (φ : TestSpace 𝕜 B) : (ext φ : Space d → 𝕜) = φ := by
    simp [ext, TestFunction.monoCLM_apply, hBO]
  let g := fun ε => localConvolution T (Mollification.scaledKernel ρ ε)
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ c : 𝕜, ∀ x ∈ B, g ε x = c := by
    have hcomp : IsCompact (closure (B : Set (Space d))) := by
      change IsCompact (closure (ball a r))
      rw [closure_ball a hr.ne']
      exact isCompact_closedBall _ _
    have hcl : closure (B : Set (Space d)) ⊆ Ω := by
      change closure (ball a r) ⊆ Ω
      rwa [closure_ball a hr.ne']
    filter_upwards [Mollification.relativelyCompactDomain d 𝕜 Ω B ρ hcomp hcl] with ε hε
    apply B.isOpen.exists_is_const_of_fderiv_eq_zero (𝕜 := ℝ) (convex_ball a r).isPreconnected
    · exact (localConvolution_smooth d 𝕜 Ω T _).differentiableOn (by simp) |>.mono hε
    · intro x hx
      exact convolution_fderiv_eq_zero T hT _ x (hε hx)
  refine ⟨T (ext η), fun φ => ?_⟩
  have hlimη := Mollification.distributionLimit d 𝕜 Ω T ρ hρ (ext η)
  have hlimφ := Mollification.distributionLimit d 𝕜 Ω T ρ hρ (ext φ)
  simp only [hext] at hlimη hlimφ
  have heq : (fun ε => ∫ x, g ε x * φ x) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => (∫ x, g ε x * η x) * ∫ x, φ x) := by
    filter_upwards [hevent] with ε hε
    obtain ⟨c, hc⟩ := hε
    rw [integral_mul_test_of_eqOn φ (g ε) c hc,
      integral_mul_test_of_eqOn η (g ε) c hc, hη, mul_one]
  exact tendsto_nhds_unique hlimφ ((hlimη.mul_const (∫ x, φ x)).congr' heq.symm)

/-- Local a.e. constancy, before any use of connectedness. -/
theorem ae_constant_on_ball {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (u : Space d → 𝕜)
    (hu : LocallyIntegrableOn u Ω volume)
    (hT : ∀ i : Fin d, distributionPartial {i} (regularDistribution Ω u) = 0)
    (a : Space d) {r : ℝ} (hr : 0 < r) (hB : closedBall a r ⊆ Ω) :
    ∃ c : 𝕜, u =ᵐ[volume.restrict (ball a r)] fun _ => c := by
  let B : Opens (Space d) := ⟨ball a r, isOpen_ball⟩
  have hBO : B ≤ Ω := ball_subset_closedBall.trans hB
  obtain ⟨c, hc⟩ := constant_pairing_on_ball (regularDistribution Ω u) hT a hr hB
  refine ⟨c, (regular_injectivity d 𝕜 B u (fun _ => c) (hu.mono_set hBO)
    (locallyIntegrableOn_const _)).mp ?_⟩
  ext φ
  rw [regular_apply_integral B u (hu.mono_set hBO),
    regular_apply_integral B (fun _ => c) (locallyIntegrableOn_const _), integral_const_mul]
  have h := hc φ
  rw [regular_apply_integral Ω u hu] at h
  have hmono : ((TestFunction.monoCLM 𝕜 φ : TestSpace 𝕜 Ω) : Space d → 𝕜) = φ := by
    rw [TestFunction.monoCLM_apply, ite_eq_left (And.intro le_rfl hBO)]
  have hmonox (x : Space d) : (TestFunction.monoCLM 𝕜 φ : TestSpace 𝕜 Ω) x = φ x :=
    congrFun hmono x
  calc
    (∫ x, u x * φ x) = ∫ x, u x * (TestFunction.monoCLM 𝕜 φ : TestSpace 𝕜 Ω) x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hmonox x]
    _ = _ := h

/-- Constants on overlapping open sets agree, since a nonempty open overlap
has positive Lebesgue measure. -/
theorem constants_eq_on_overlap {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u : Space d → 𝕜} {V W : Opens (Space d)} {c c' : 𝕜}
    (hV : u =ᵐ[volume.restrict V] fun _ => c)
    (hW : u =ᵐ[volume.restrict W] fun _ => c')
    {x : Space d} (hxV : x ∈ V) (hxW : x ∈ W) : c = c' := by
  have h1 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left :
    (V : Set (Space d)) ∩ W ⊆ V) hV
  have h2 := ae_restrict_of_ae_restrict_of_subset (inter_subset_right :
    (V : Set (Space d)) ∩ W ⊆ W) hW
  have heq : (fun _ : Space d => c) =ᵐ[volume.restrict ((V : Set (Space d)) ∩ W)]
      (fun _ => c') := by
    filter_upwards [h1, h2] with y hy1 hy2
    exact hy1.symm.trans hy2
  exact Measure.eqOn_open_of_ae_eq heq (V.isOpen.inter W.isOpen)
    continuousOn_const continuousOn_const ⟨hxV, hxW⟩

/-- Gluing local a.e. constants on a preconnected open set. The final a.e.
statement uses a countable subcover, rather than an uncountable union of null sets. -/
theorem ae_constant_of_locally_ae_constant {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (u : Space d → 𝕜)
    (hconn : IsPreconnected (Ω : Set (Space d)))
    (hlocal : ∀ x ∈ Ω, ∃ (V : Opens (Space d)) (c : 𝕜),
      x ∈ V ∧ V ≤ Ω ∧ u =ᵐ[volume.restrict V] fun _ => c) :
    ∃ c : 𝕜, u =ᵐ[volume.restrict Ω] fun _ => c := by
  classical
  choose V c hxV hVO hc using (fun x : Ω => hlocal x x.property)
  let : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp hconn
  have hclocal : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_eventually_eq c).mpr
    intro x
    have hnhds : (Subtype.val ⁻¹' (V x : Set (Space d))) ∈ 𝓝 x :=
      (V x).isOpen.preimage continuous_subtype_val |>.mem_nhds (hxV x)
    filter_upwards [hnhds] with y hy
    exact constants_eq_on_overlap (hc y) (hc x) (hxV y) hy
  obtain ⟨c₀, hc₀⟩ := hclocal.exists_eq_const
  have hcover : (Ω : Set (Space d)) ⊆ ⋃ x : Ω, (V x : Set (Space d)) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨S, hS, hScov⟩ := (HereditarilyLindelofSpace.isLindelof (Ω : Set (Space d))).elim_countable_subcover
    (fun x : Ω => (V x : Set (Space d))) (fun x => (V x).isOpen) hcover
  refine ⟨c₀, ae_restrict_of_ae_restrict_of_subset hScov ?_⟩
  apply (ae_restrict_biUnion_iff _ hS _).mpr
  intro x hxS
  have heq : c x = c₀ := congrFun hc₀ x
  filter_upwards [hc x] with y hy
  exact hy.trans heq

/-- Zero weak coordinate gradient forces one a.e. constant on a connected open set. -/
theorem zero_gradient_constant : ZeroGradientExpected.Constant := by
  intro d 𝕜 _ Ω u hconn hu hT
  apply ae_constant_of_locally_ae_constant Ω u hconn
  intro a ha
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen a ha
  have hr' : 0 < r / 2 := half_pos hr
  have hclosed : closedBall a (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨c, hc⟩ := ae_constant_on_ball u hu hT a hr' hclosed
  exact ⟨⟨ball a (r / 2), isOpen_ball⟩, c, mem_ball_self hr',
    ball_subset_closedBall.trans hclosed, hc⟩

/-- On a nonempty connected open set the constant is unique. -/
theorem zero_gradient_unique_constant : ZeroGradientExpected.UniqueConstant := by
  intro d 𝕜 _ Ω u hconn hu hT
  obtain ⟨c, hc⟩ := zero_gradient_constant d 𝕜 Ω u hconn.isPreconnected hu hT
  refine ⟨c, hc, fun c' hc' => ?_⟩
  obtain ⟨x, hx⟩ := hconn.nonempty
  exact constants_eq_on_overlap hc' hc hx hx

/-- A locally integrable whole-space function in any finite positive Lp
class with zero gradient vanishes. -/
theorem zero_gradient_whole_space_of_locally_integrable :
    ZeroGradientExpected.WholeSpaceZeroOfLocallyIntegrable := by
  intro d 𝕜 _ hd p u hp hptop huloc hu hT
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hu' : LocallyIntegrableOn u (⊤ : Opens (Space d)) volume :=
    huloc.locallyIntegrableOn _
  obtain ⟨c, hc⟩ := zero_gradient_constant d 𝕜 ⊤ u isPreconnected_univ hu' hT
  have hc' : u =ᵐ[volume] fun _ => c := by simpa using hc
  have hmem : MemLp (fun _ : Space d => c) p volume := hu.ae_eq hc'
  have hc0 : c = 0 := by
    have h := (memLp_const_iff hp hptop).mp hmem
    simpa only [MeasureTheory.measure_univ_of_isAddLeftInvariant, lt_self_iff_false, or_false] using h
  filter_upwards [hc'] with x hx
  simpa only [hc0, Pi.zero_apply] using hx

/-- For exponents at least one, Lp membership already supplies local integrability. -/
theorem zero_gradient_whole_space : ZeroGradientExpected.WholeSpaceZero := by
  intro d 𝕜 _ hd p u hp hptop hu hT
  exact zero_gradient_whole_space_of_locally_integrable d 𝕜 hd p u
    (ne_of_gt (lt_of_lt_of_le (by norm_num) hp)) hptop (hu.locallyIntegrable hp) hu hT

end P102.Sobolev
