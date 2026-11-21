import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.Transcritical
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.SimplePersistence
import MathGenome.Internal.MultivariableAnalysis.D04.C05.MorseCoefficients
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Transcritical exchange on the actual open parameter/state domain.
The Hadamard factor retains the trivial branch, and the scalar flow tests
are supplied by SimplePersistence. -/
noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch16.Transcritical
open Specs.D13Unified.Ch16.SimplePersistence

/-- Hadamard's factor, defined by its actual integral rather than by a
certificate of factorization. -/
def hadamardFactor (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  D04.riemannValue (fun t => stateDerivative f (z.1,t*z.2))

/-- State segments stay in the same product box. -/
theorem scaled_state_mem {r s μ x t : ℝ}
    (hs : 0 < s) (hμ : μ ∈ Metric.ball 0 r) (hx : x ∈ Metric.ball 0 s)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (μ,t*x) ∈ Metric.ball 0 r ×ˢ Metric.ball 0 s := by
  refine ⟨hμ, ?_⟩
  exact (convex_ball (0 : ℝ) s).smul_mem_of_zero_mem
    (Metric.mem_ball_self hs) hx ht

/-- On an open set the state partial loses one derivative. -/
theorem stateDerivative_contDiffOn {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) :
    ContDiffOn ℝ 2 (stateDerivative f) U := by
  have hd : ContDiffOn ℝ 2 (fderiv ℝ f) U := by
    intro z hz
    exact ((hf.contDiffAt (hU.mem_nhds hz)).fderiv_right (by norm_num)).contDiffWithinAt
  exact hd.clm_apply contDiffOn_const

/-- The factor has the regularity needed for implicit persistence. The
integrand is jointly C² on the open preimage of the original domain. -/
theorem hadamardFactor_contDiffOn {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    {r s : ℝ} (hs : 0 < s)
    (hbox : Metric.ball 0 r ×ˢ Metric.ball 0 s ⊆ U) :
    ContDiffOn ℝ 2 (hadamardFactor f) (Metric.ball 0 r ×ˢ Metric.ball 0 s) := by
  let S : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun p => (p.1.1,p.2*p.1.2)
  have hS : ContDiff ℝ 2 S := by dsimp [S]; fun_prop
  exact D04.MorseParameter.riemann_contDiffOn 2 (S ⁻¹' U)
    (hU.preimage hS.continuous) _
    ((stateDerivative_contDiffOn hU hf).comp hS.contDiffOn (fun _ hp => hp))
    _ (Metric.isOpen_ball.prod Metric.isOpen_ball)
    (fun z hz t ht => hbox (scaled_state_mem hs hz.1 hz.2 ht))

open SingleVariableAnalysis.Riemann

/-- The integral on the unit interval of an affine function. -/
theorem riemannValue_affine (c d : ℝ) :
    D04.riemannValue (fun t => c + d*t) = c + d/2 := by
  have hi := D04.continuous_real_riemann_integrable (fun t : ℝ => c+d*t)
    (by fun_prop)
  rw [D04.riemannValue_eq hi]
  have he := real_ftc_second (fun t : ℝ => c*t+d*t^2/2) (fun t => c+d*t)
    0 1 (by norm_num) (by fun_prop) (fun t _ => by
      convert ((hasDerivAt_id t).const_mul c).add
        (((hasDerivAt_id t).pow 2).const_mul d |>.div_const 2) using 1
      · rfl
      · dsimp
        ring) hi
  calc
    _ = c*1+d*1^2/2-(c*0+d*0^2/2) := he
    _ = _ := by ring

@[simp] theorem hadamardFactor_zero (f : ℝ × ℝ → ℝ) :
    hadamardFactor f (0,0) = stateDerivative f (0,0) := by
  simpa [hadamardFactor] using riemannValue_affine (stateDerivative f (0,0)) 0

/-- Integration along the state segment gives the factorization, including
at x=0. No division by the state is used. -/
theorem state_mul_hadamardFactor {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    {r s μ x : ℝ} (hs : 0 < s)
    (hbox : Metric.ball 0 r ×ˢ Metric.ball 0 s ⊆ U)
    (hμ : μ ∈ Metric.ball 0 r) (hx : x ∈ Metric.ball 0 s) :
    x * hadamardFactor f (μ,x) = f (μ,x) - f (μ,0) := by
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (μ,t*x) ∈ U :=
    hbox (scaled_state_mem hs hμ hx ht)
  have hi := D04.continuous_real_riemann_integrable
    (fun t => stateDerivative f (μ,t*x))
    ((stateDerivative_contDiffOn hU hf).continuousOn.comp (by fun_prop) hseg)
  obtain ⟨hi', he'⟩ := real_mul_value hi x
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t => f (μ,t*x)) (x * stateDerivative f (μ,t*x)) t := by
    have hd := ((hf.contDiffAt (hU.mem_nhds (hseg t ⟨ht.1.le, ht.2.le⟩))).differentiableAt
      (by norm_num)).hasFDerivAt
    have heq : ((0,x) : ℝ × ℝ) = x • ((0,1) : ℝ × ℝ) := by ext <;> simp
    convert hd.comp_hasDerivAt t
      ((hasDerivAt_const t μ).prodMk ((hasDerivAt_id t).mul_const x)) using 1
    · rfl
    · rw [one_mul, heq, map_smul]
      rfl
  have he := real_ftc_second (fun t => f (μ,t*x))
    (fun t => x*stateDerivative f (μ,t*x)) 0 1 (by norm_num)
    (hf.continuousOn.comp (by fun_prop) hseg) hd hi'
  simpa [hadamardFactor, D04.riemannValue_eq hi, he'] using he

/-- Exact preservation of the zero branch and the factor's zero set. -/
theorem equilibrium_iff_factor {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    {r s μ x : ℝ} (hs : 0 < s)
    (hbox : Metric.ball 0 r ×ˢ Metric.ball 0 s ⊆ U)
    (hμ : μ ∈ Metric.ball 0 r) (hx : x ∈ Metric.ball 0 s)
    (hzero : f (μ,0) = 0) :
    f (μ,x) = 0 ↔ x = 0 ∨ hadamardFactor f (μ,x) = 0 := by
  have he := state_mul_hadamardFactor hU hf hs hbox hμ hx
  rw [hzero, sub_zero] at he
  rw [← he, mul_eq_zero]

/-- Derivatives of the integral factor at the singular point. -/
theorem hadamardFactor_hasFDerivAt_zero {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hbox : Metric.ball 0 r ×ˢ Metric.ball 0 s ⊆ U) :
    ∃ L : (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (hadamardFactor f) L (0,0) ∧
      ∀ h, L h = mixedCoefficient f * h.1 + quadraticCoefficient f * h.2 := by
  let V := Metric.ball (0 : ℝ) r ×ˢ Metric.ball (0 : ℝ) s
  have hV : IsOpen V := Metric.isOpen_ball.prod Metric.isOpen_ball
  have h0 : ((0,0) : ℝ × ℝ) ∈ V := ⟨Metric.mem_ball_self hr,Metric.mem_ball_self hs⟩
  let R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := fun t =>
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (t • ContinuousLinearMap.snd ℝ ℝ ℝ)
  let S : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun p => (p.1.1,p.2*p.1.2)
  let D : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun z t =>
    (fderiv ℝ (stateDerivative f) (S (z,t))).comp (R t)
  have hH := stateDerivative_contDiffOn hU hf
  have hH' : ContinuousOn (fderiv ℝ (stateDerivative f)) U := by
    intro z hz
    exact ((hH.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hSU : MapsTo S (V ×ˢ Icc (0 : ℝ) 1) U := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    exact hbox (scaled_state_mem hs hz.1 hz.2 ht)
  have hR : Continuous R :=
    (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
      (continuous_const.prodMk (continuous_id.smul continuous_const))
  have hD : ContinuousOn (Function.uncurry D) (V ×ˢ Icc (0 : ℝ) 1) :=
    (hH'.comp (by dsimp [S]; fun_prop) hSU).clm_comp
      (hR.comp continuous_snd).continuousOn
  have hder (z : ℝ × ℝ) (hz : z ∈ V) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasFDerivAt (fun y => stateDerivative f (y.1,t*y.2)) (D z t) z := by
    have hmem : S (z,t) ∈ U := hSU ⟨hz,ht⟩
    have hbase : HasFDerivAt (stateDerivative f)
        (fderiv ℝ (stateDerivative f) (S (z,t))) ((R t) z) := by
      simpa [R, S] using ((hH.contDiffAt (hU.mem_nhds hmem)).differentiableAt
        (by norm_num)).hasFDerivAt
    exact hbase.comp z (R t).hasFDerivAt
  obtain ⟨L,hL,hval⟩ := D04.MorseParameter.riemann_hasFDerivAt V hV
    (fun z t => stateDerivative f (S (z,t))) D
    (hH.continuousOn.comp (by dsimp [S]; fun_prop) hSU) hD hder (0,0) h0
  refine ⟨L,hL,fun h => ?_⟩
  rw [hval]
  have hlin (t : ℝ) : D (0,0) t h =
      mixedCoefficient f * h.1 +
        (stateDerivative (stateDerivative f) (0,0) * h.2) * t := by
    have hp : (h.1,t*h.2) = h.1 • ((1,0) : ℝ × ℝ) + (t*h.2) • ((0,1) : ℝ × ℝ) := by
      ext <;> simp
    simp only [D, S, ContinuousLinearMap.comp_apply, R, ContinuousLinearMap.prod_apply,
      smul_apply, smul_eq_mul, mul_zero]
    change (fderiv ℝ (stateDerivative f) (0,0)) (h.1,t*h.2) = _
    rw [hp, map_add, map_smul, map_smul]
    dsimp [mixedCoefficient, stateDerivative]
    ring
  change D04.riemannValue (fun t => D (0,0) t h) = _
  simp_rw [hlin]
  rw [riemannValue_affine]
  dsimp [quadraticCoefficient]
  ring

/-- A derivative with a nonzero linear coefficient has that sign on the
punctured neighborhood, uniformly on both sides of zero. -/
theorem eventually_same_linear_sign {g : ℝ → ℝ} {c : ℝ}
    (hg : HasDerivAt g c 0) (h0 : g 0 = 0) (hc : c ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 → 0 < g t * (c*t) := by
  have hcont := (continuousAt_dslope_same.mpr hg.differentiableAt).mul_const c
  have hpos : 0 < dslope g 0 0 * c := by
    simpa [hg.deriv] using mul_self_pos.mpr hc
  have hev := hcont (isOpen_Ioi.mem_nhds hpos)
  filter_upwards [hev] with t ht hne
  have he : t * dslope g 0 t = g t := by
    simpa [h0, smul_eq_mul] using sub_smul_dslope g 0 t
  have hp := mul_pos (mul_self_pos.mpr hne) ht
  rw [← he]
  nlinarith [hp]

/-- The usual derivative formula for the factorization on the open box. -/
theorem stateDerivative_factor
    (hSlice : Specs.D13Unified.Ch16.SimplePersistence.stateDerivativeSlice)
    {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    {r s μ x : ℝ} (hs : 0 < s)
    (hbox : Metric.ball 0 r ×ˢ Metric.ball 0 s ⊆ U)
    (hμ : μ ∈ Metric.ball 0 r) (hx : x ∈ Metric.ball 0 s)
    (hzero : f (μ,0) = 0) :
    stateDerivative f (μ,x) = hadamardFactor f (μ,x) +
      x * stateDerivative (hadamardFactor f) (μ,x) := by
  have hG := hadamardFactor_contDiffOn hU hf hs hbox
  have hfd := hSlice f (μ,x) ((hf.contDiffAt (hU.mem_nhds (hbox ⟨hμ,hx⟩))).differentiableAt
    (by norm_num))
  have hgd := hSlice (hadamardFactor f) (μ,x)
    ((hG.contDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds ⟨hμ,hx⟩)).differentiableAt
      (by norm_num))
  have heq : (fun y => y*hadamardFactor f (μ,y)) =ᶠ[𝓝 x] fun y => f (μ,y) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    simpa [hzero] using state_mul_hadamardFactor hU hf hs hbox hμ hy
  have hd := ((hasDerivAt_id x).mul hgd).congr_of_eventuallyEq heq.symm
  simpa using hfd.unique hd

/-- A product neighborhood on which the trivial equilibrium branch is valid. -/
theorem exists_equilibrium_box {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h0 : ((0,0) : ℝ × ℝ) ∈ U)
    (hz : ∀ᶠ μ in 𝓝 (0 : ℝ), f (μ,0) = 0) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      Metric.ball 0 r ×ˢ Metric.ball 0 s ⊆ U ∧
      ∀ μ ∈ Metric.ball 0 r, f (μ,0) = 0 := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨δ,hδ,hδz⟩ := Metric.mem_nhds_iff.mp hz
  refine ⟨min ε δ,ε,lt_min hε hδ,hε,?_,?_⟩
  · exact (Set.prod_mono (Metric.ball_subset_ball (min_le_left _ _)) Subset.rfl).trans
      (by simpa only [ball_prod_same] using hεU)
  · intro μ hμ
    exact hδz (Metric.ball_subset_ball (min_le_right _ _) hμ)

/-- Differentiating the factor's implicit zero graph determines its slope. -/
theorem implicit_graph_derivative {G : ℝ × ℝ → ℝ} {χ : ℝ → ℝ}
    {U : Set (ℝ × ℝ)} {r s a b : ℝ}
    (hgraph : IsLocalZeroGraph G U χ r s)
    (hL : ∃ L : (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt G L (0,0) ∧
      ∀ h, L h = a*h.1+b*h.2)
    (hb : b ≠ 0) : HasDerivAt χ (-a/b) 0 := by
  obtain ⟨hr,hs,hχ0,hbox,hχ,hzeros⟩ := hgraph
  have hχd := ((hχ.contDiffAt (Metric.ball_mem_nhds 0 hr)).differentiableAt
    (by norm_num)).hasDerivAt
  obtain ⟨L,hL,hval⟩ := hL
  have hL' : HasFDerivAt G L ((0 : ℝ),χ 0) := by simpa [hχ0] using hL
  have hd := hL'.comp_hasDerivAt 0 ((hasDerivAt_id 0).prodMk hχd)
  have heq : (fun μ => G (μ,χ μ)) =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with μ hμ
    exact ((hzeros μ hμ).2 (χ μ) (hzeros μ hμ).1).mpr rfl
  have hz := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq
  have he := hd.unique hz
  rw [hval] at he
  dsimp at he
  have hc : deriv χ 0 = -a/b := by apply (eq_div_iff hb).mpr; nlinarith
  simpa [hc] using hχd

/-- Implicit persistence applied to the actual Hadamard factor. -/
theorem exists_factor_graph
    (hPersistence : Specs.D13Unified.Ch16.SimplePersistence.flowPersistence)
    {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hbox : Metric.ball 0 r ×ˢ Metric.ball 0 s ⊆ U)
    (hfx : stateDerivative f (0,0) = 0)
    (hb : quadraticCoefficient f ≠ 0) :
    ∃ χ : ℝ → ℝ, ∃ r' s' : ℝ,
      IsLocalZeroGraph (hadamardFactor f) (Metric.ball 0 r ×ˢ Metric.ball 0 s) χ r' s' ∧
      HasDerivAt χ (-mixedCoefficient f / quadraticCoefficient f) 0 := by
  have hG := hadamardFactor_contDiffOn hU hf hs hbox
  obtain ⟨L,hL,hval⟩ := hadamardFactor_hasFDerivAt_zero hU hf hr hs hbox
  have hGx : stateDerivative (hadamardFactor f) (0,0) = quadraticCoefficient f := by
    rw [stateDerivative, hL.fderiv, hval]
    simp
  obtain ⟨χ,r',s',hgraph,_⟩ := hPersistence (hadamardFactor f)
    (Metric.ball 0 r ×ˢ Metric.ball 0 s) (Metric.isOpen_ball.prod Metric.isOpen_ball)
    ⟨Metric.mem_ball_self hr,Metric.mem_ball_self hs⟩ (hG.of_le (by norm_num))
    (by simpa using hfx) (by simpa [hGx] using hb)
  exact ⟨χ,r',s',hgraph,implicit_graph_derivative hgraph ⟨L,hL,hval⟩ hb⟩

/-- First-order expansions of the actual state derivatives on both branches. -/
theorem factor_graph_derivatives
    (hSlice : Specs.D13Unified.Ch16.SimplePersistence.stateDerivativeSlice)
    {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hbox : Metric.ball 0 r ×ˢ Metric.ball 0 s ⊆ U)
    (hzero : ∀ μ ∈ Metric.ball 0 r, f (μ,0) = 0)
    (hb : quadraticCoefficient f ≠ 0)
    {χ : ℝ → ℝ} {r' s' : ℝ}
    (hgraph : IsLocalZeroGraph (hadamardFactor f)
      (Metric.ball 0 r ×ˢ Metric.ball 0 s) χ r' s')
    (hχ : HasDerivAt χ (-mixedCoefficient f / quadraticCoefficient f) 0) :
    HasDerivAt (fun μ => stateDerivative f (μ,0)) (mixedCoefficient f) 0 ∧
    HasDerivAt (fun μ => stateDerivative f (μ,χ μ)) (-mixedCoefficient f) 0 := by
  obtain ⟨L,hL,hval⟩ := hadamardFactor_hasFDerivAt_zero hU hf hr hs hbox
  have hGx0 : stateDerivative (hadamardFactor f) (0,0) = quadraticCoefficient f := by
    rw [stateDerivative,hL.fderiv,hval]
    simp
  obtain ⟨hr',hs',hχ0,hsmall,hχC,hroots⟩ := hgraph
  have hsource (μ : ℝ) (hμ : μ ∈ Metric.ball 0 r') :
      (μ,χ μ) ∈ Metric.ball 0 r ×ˢ Metric.ball 0 s :=
    hsmall ⟨hμ,(hroots μ hμ).1⟩
  have hGμ : HasDerivAt (fun μ => hadamardFactor f (μ,0)) (mixedCoefficient f) 0 := by
    simpa [Function.comp_def,hval] using hL.comp_hasDerivAt (f := fun μ : ℝ => (μ,0)) 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 (0 : ℝ)))
  have hG := hadamardFactor_contDiffOn hU hf hs hbox
  have hGx : ContDiffOn ℝ 1 (stateDerivative (hadamardFactor f))
      (Metric.ball 0 r ×ˢ Metric.ball 0 s) := by
    have hd : ContDiffOn ℝ 1 (fderiv ℝ (hadamardFactor f))
        (Metric.ball 0 r ×ˢ Metric.ball 0 s) := by
      intro z hz
      exact ((hG.contDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hz)).fderiv_right
        (by norm_num)).contDiffWithinAt
    exact hd.clm_apply contDiffOn_const
  have hkbase : DifferentiableAt ℝ (stateDerivative (hadamardFactor f)) ((0 : ℝ),χ 0) := by
    rw [hχ0]
    exact (hGx.contDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
      ⟨Metric.mem_ball_self hr,Metric.mem_ball_self hs⟩)).differentiableAt (by norm_num)
  have hk := hkbase.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_id 0).prodMk hχ)
  have hprod : HasDerivAt
      (fun μ => χ μ * stateDerivative (hadamardFactor f) (μ,χ μ)) (-mixedCoefficient f) 0 := by
    simpa [Function.comp_def,hχ0,hGx0,hb] using hχ.fun_mul hk
  constructor
  · apply hGμ.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr'] with μ hμ
    simpa using stateDerivative_factor hSlice hU hf hs hbox (hsource μ hμ).1
      (Metric.mem_ball_self hs) (hzero μ (hsource μ hμ).1)
  · apply hprod.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr'] with μ hμ
    have he := stateDerivative_factor hSlice hU hf hs hbox (hsource μ hμ).1
      (hsource μ hμ).2 (hzero μ (hsource μ hμ).1)
    have hz : hadamardFactor f (μ,χ μ) = 0 :=
      ((hroots μ hμ).2 (χ μ) (hroots μ hμ).1).mpr rfl
    simpa [hz] using he

/-- The scalar conditional stability test applies on the actual translated
state slice at any equilibrium, with its original domain retained. -/
theorem scalar_stability_of_same_sign
    (hStability : Specs.D13Unified.Ch16.SimplePersistence.scalarFlowStability)
    (hSlice : Specs.D13Unified.Ch16.SimplePersistence.stateDerivativeSlice)
    {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {μ p l : ℝ} (hp : (μ,p) ∈ U) (heq : f (μ,p) = 0)
    (hsign : 0 < stateDerivative f (μ,p) * l) :
    HasScalarStability f U μ p l := by
  let V := {y : ℝ | (μ,p+y) ∈ U}
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have hsf : ContDiffOn ℝ 1 (fun y : ℝ => f (μ,p+y)) V :=
    hf.comp (by fun_prop) (fun _ hy => hy)
  let F : D13Unified.AutonomousODE ℝ :=
    ⟨V,hV,fun y => f (μ,p+y), hsf.continuousOn.domRestrict⟩
  have hev : EqOn (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F)
      (fun y => f (μ,p+y)) V := by
    intro y hy
    simp only [Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue, F, dite_eq_left hy]
  have hF : ContDiffOn ℝ 1
      (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) F.domain :=
    hsf.congr hev
  have h0 : (0 : ℝ) ∈ F.domain := by simpa [F,V] using hp
  have hEq0 : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F 0 = 0 := by
    rw [hev h0]; simpa using heq
  have hfd := hSlice f (μ,p) ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num))
  have hfd' : HasDerivAt (fun y : ℝ => f (μ,p+y)) (stateDerivative f (μ,p)) 0 := by
    simpa [Function.comp_def] using hfd.comp_of_eq 0
      ((hasDerivAt_id (0 : ℝ)).const_add p) (by simp)
  have hdf : deriv (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) 0 =
      stateDerivative f (μ,p) :=
    (hfd'.congr_of_eventuallyEq (hev.eventuallyEq_of_mem (hV.mem_nhds h0))).deriv
  obtain ⟨hst,hunst⟩ := hStability F hF h0 hEq0
  refine ⟨F,rfl,hev, hF,h0,hEq0,?_,?_⟩
  · intro hl
    apply hst
    rw [hdf]
    rcases mul_pos_iff.mp hsign with h | h
    · linarith [h.2]
    · exact h.1
  · intro hl
    apply hunst
    rw [hdf]
    rcases mul_pos_iff.mp hsign with h | h
    · exact h.1
    · linarith [h.2]

/-- All nearby equilibria consist of the trivial and transcritical branches,
with their derivative signs and nonlinear scalar stability exchanged. -/
theorem transcritical_exchange :
    Specs.D13Unified.Ch16.Transcritical.transcriticalExchange := by
  have hPersistence := D13Unified.Ch16.SimplePersistence.flow_persistence
  have hStability := D13Unified.Ch16.SimplePersistence.scalar_flow_stability
  have hSlice := D13Unified.Ch16.SimplePersistence.state_derivative_slice
  intro f U hU h0 hf hzero hfx ha hb
  obtain ⟨r,s,hr,hs,hbox,hzero⟩ := exists_equilibrium_box hU h0 hzero
  obtain ⟨χ,r',s',hgraph,hχ⟩ := exists_factor_graph hPersistence hU hf hr hs hbox hfx hb
  have hχ0 := hgraph.2.2.1
  have hχsign := eventually_same_linear_sign hχ hχ0 (div_ne_zero (neg_ne_zero.mpr ha) hb)
  obtain ⟨hd0,hdχ⟩ := factor_graph_derivatives hSlice hU hf hr hs hbox hzero hb hgraph hχ
  have hsign0 := eventually_same_linear_sign hd0 hfx ha
  have hsignχ := eventually_same_linear_sign hdχ (by simpa [hχ0] using hfx) (neg_ne_zero.mpr ha)
  obtain ⟨δ,hδ,hδsign⟩ := Metric.mem_nhds_iff.mp (hχsign.and (hsign0.and hsignχ))
  obtain ⟨hr',hs',hχ0',hsmall,hχC,hroots⟩ := hgraph
  have hsub : Metric.ball (0 : ℝ) (min r' δ) ⊆ Metric.ball 0 r' :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsigns (μ : ℝ) (hμ : μ ∈ Metric.ball 0 (min r' δ)) :=
    hδsign (Metric.ball_subset_ball (min_le_right _ _) hμ)
  have hsource (μ : ℝ) (hμ : μ ∈ Metric.ball 0 (min r' δ)) :
      (μ,χ μ) ∈ Metric.ball 0 r ×ˢ Metric.ball 0 s :=
    hsmall ⟨hsub hμ,(hroots μ (hsub hμ)).1⟩
  refine ⟨χ,min r' δ,s',?_,hχ,?_,?_⟩
  · refine ⟨lt_min hr' hδ,hs',hχ0',
      ((Set.prod_mono hsub Subset.rfl).trans hsmall).trans hbox,
      hχC.mono hsub,fun μ hμ => ?_⟩
    refine ⟨(hroots μ (hsub hμ)).1,?_,fun x hx => ?_⟩
    · constructor
      · intro he
        by_contra hne
        have hpos := (hsigns μ hμ).1 hne
        simp [he] at hpos
      · rintro rfl
        exact hχ0'
    · have hpt : (μ,x) ∈ Metric.ball 0 r ×ˢ Metric.ball 0 s := hsmall ⟨hsub hμ,hx⟩
      rw [equilibrium_iff_factor hU hf hs hbox hpt.1 hpt.2 (hzero μ hpt.1),
        (hroots μ (hsub hμ)).2 x hx]
  · simpa [hχ0',smul_eq_mul,mul_comm] using hχ.isLittleO
  · intro μ hμ hne
    have hpos := (hsigns μ hμ).2.1 hne
    have hneg : stateDerivative f (μ,χ μ) * (mixedCoefficient f * μ) < 0 := by
      have hp := (hsigns μ hμ).2.2 hne
      nlinarith
    refine ⟨hpos,hneg,?_,?_⟩
    · exact scalar_stability_of_same_sign hStability hSlice hU (hf.of_le (by norm_num))
        (hbox ⟨(hsource μ hμ).1,Metric.mem_ball_self hs⟩)
        (hzero μ (hsource μ hμ).1) hpos
    · have hroot : f (μ,χ μ) = 0 := by
        apply (equilibrium_iff_factor hU hf hs hbox (hsource μ hμ).1
          (hsource μ hμ).2 (hzero μ (hsource μ hμ).1)).mpr
        exact Or.inr (((hroots μ (hsub hμ)).2 (χ μ) (hroots μ (hsub hμ)).1).mpr rfl)
      exact scalar_stability_of_same_sign hStability hSlice hU (hf.of_le (by norm_num))
        (hbox (hsource μ hμ)) hroot (by nlinarith)

end D13Unified.Ch16.Transcritical
