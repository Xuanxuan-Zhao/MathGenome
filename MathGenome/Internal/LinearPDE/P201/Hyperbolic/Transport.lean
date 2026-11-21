import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.Transport
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.Flow
import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.ScalarLinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Ring

noncomputable section
open Set
open scoped ContDiff Topology
namespace P201.Hyperbolic
open P201Specs P201Specs.Hyperbolic

/-- Restricting a classical PDE solution to any characteristic gives the
endpoint-aware scalar differential equation. -/
theorem derivative_along_characteristic {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {D : Set (ℝ × P201Specs.Space n)} {b : ℝ × P201Specs.Space n → P201Specs.Space n}
    {q f u : ℝ × P201Specs.Space n → 𝕜}
    (hu : IsTransportSolutionOn D b q f u) {J : Set ℝ}
    {x : ℝ → P201Specs.Space n} (hx : ∀ r ∈ J, (r, x r) ∈ D)
    (hd : ∀ r ∈ J, HasDerivWithinAt x (b (r, x r)) J r) :
    ∀ r ∈ J, HasDerivWithinAt (fun t => u (t, x t))
      (-q (r, x r) * u (r, x r) + f (r, x r)) J r := by
  intro r hr
  obtain ⟨du, hdu, heq⟩ := hu.2 (r, x r) (hx r hr)
  have hcurve := (hasDerivWithinAt_id r J).prodMk (hd r hr)
  have hc := hdu.comp_hasDerivWithinAt r hcurve hx
  change HasDerivWithinAt (fun t => u (t, x t)) (du (1, b (r, x r))) J r at hc
  have he : du (1, b (r, x r)) = -q (r, x r) * u (r, x r) + f (r, x r) := by
    rw [eq_sub_of_add_eq heq]
    ring
  rwa [he] at hc

/-- The homogeneous expression is C¹ on the original closed slab. -/
theorem homogeneous_regular {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → P201Specs.Space n → P201Specs.Space n}
    (hX : SlabFlowProperties b X) {𝕜 : Type*} [RCLike 𝕜]
    {g : P201Specs.Space n → 𝕜} (hg : ContDiff ℝ 1 g) :
    ContDiffOn ℝ 1 (homogeneousFormula X g) (Icc 0 T ×ˢ univ) := by
  exact hg.comp_contDiffOn (hX.regular.comp
    (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => ⟨⟨le_rfl, hT⟩, hp⟩))

/-- Initial values follow directly from the flow identity. -/
theorem homogeneous_initial {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → P201Specs.Space n → P201Specs.Space n}
    (hX : SlabFlowProperties b X) {𝕜 : Type*} [RCLike 𝕜]
    (g : P201Specs.Space n → 𝕜) (y : P201Specs.Space n) :
    homogeneousFormula X g (0, y) = g y := by
  simp only [homogeneousFormula, hX.initial 0 ⟨le_rfl, hT⟩]

/-- The scalar integrating-factor formula in the manuscript's two-term form.
Only continuity on the original closed interval is used. -/
theorem variation_eq_two_term_on {𝕜 : Type*} [RCLike 𝕜]
    (I : D13Unified.TimeInterval) (hzero : (0 : ℝ) ∈ I.carrier)
    {t : ℝ} (ht : t ∈ I.carrier) (Q F : ℝ → 𝕜)
    (hQ : ContinuousOn Q I.carrier) (ξ : 𝕜) :
    D13Unified.ScalarLinear.variation (fun r => -Q r) F 0 ξ t =
      NormedSpace.exp (-(∫ r in (0 : ℝ)..t, Q r)) * ξ +
      ∫ s in (0 : ℝ)..t, NormedSpace.exp (-(∫ r in s..t, Q r)) * F s := by
  have hInt {a c : ℝ} (ha : a ∈ I.carrier) (hc : c ∈ I.carrier) :
      IntervalIntegrable Q MeasureTheory.volume a c :=
    (hQ.mono (I.ordConnected.uIcc_subset ha hc)).intervalIntegrable
  simp only [D13Unified.ScalarLinear.variation, D13Unified.ScalarLinear.primitive,
    intervalIntegral.integral_neg, neg_neg]
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsI : s ∈ I.carrier := I.ordConnected.uIcc_subset hzero ht hs
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hInt hzero hsI) (hInt hsI ht)
  dsimp only
  rw [← mul_assoc, ← NormedSpace.exp_add]
  congr 2
  rw [← hadd]
  ring

theorem variation_eq_two_term {𝕜 : Type*} [RCLike 𝕜] {T t : ℝ}
    (ht : t ∈ Icc 0 T) (Q F : ℝ → 𝕜) (hQ : ContinuousOn Q (Icc 0 T)) (ξ : 𝕜) :
    D13Unified.ScalarLinear.variation (fun r => -Q r) F 0 ξ t =
      NormedSpace.exp (-(∫ r in (0 : ℝ)..t, Q r)) * ξ +
      ∫ s in (0 : ℝ)..t, NormedSpace.exp (-(∫ r in s..t, Q r)) * F s :=
  variation_eq_two_term_on ⟨Icc 0 T, ⟨t, ht⟩, ordConnected_Icc⟩
    ⟨le_rfl, ht.1.trans ht.2⟩ ht Q F hQ ξ

/-- Every classical solution has exactly the displayed characteristic formula.
This includes one-sided endpoints and a zero-length slab. -/
theorem slabRepresentation : slabRepresentationStatement := by
  intro n hn T hT b X hX 𝕜 _ q f g hq hf u hu p hp
  let x : ℝ → P201Specs.Space n := fun r => X r p.1 p.2
  have hx := hX.solution p.1 hp.1 p.2
  let Q : ℝ → 𝕜 := fun r => q (r, x r)
  let F : ℝ → 𝕜 := fun r => f (r, x r)
  have hgraph : MapsTo (fun r => (r, x r)) (Icc 0 T) (Icc 0 T ×ˢ univ) :=
    fun r hr => ⟨hr, mem_univ _⟩
  have hcurve : ContinuousOn (fun r => (r, x r)) (Icc 0 T) :=
    continuousOn_id.prodMk hx.1
  have hQ : ContinuousOn Q (Icc 0 T) := hq.comp hcurve hgraph
  have hF : ContinuousOn F (Icc 0 T) := hf.comp hcurve hgraph
  let I : D13Unified.TimeInterval := ⟨Icc 0 T, nonempty_Icc.mpr hT, ordConnected_Icc⟩
  have hI : D13Unified.ScalarLinear.IsIVP I (fun r => -Q r) F 0 (g (x 0))
      (fun r => u (r, x r)) := by
    refine ⟨hu.1.1.continuousOn.comp hcurve hgraph, ⟨le_rfl, hT⟩,
      hu.2 (x 0) (mem_univ _), ?_⟩
    exact derivative_along_characteristic hu.1 hgraph hx.2
  have he := D13Unified.ScalarLinear.eq_variation_of_isIVP I
    (fun r => -Q r) F 0 (g (x 0)) hQ.neg hF hI hp.1
  rw [variation_eq_two_term hp.1 Q F hQ] at he
  simpa only [x, Q, F, hX.initial p.1 hp.1, transportFormula] using he

/-- In particular, two classical solutions with the same data agree. -/
theorem slab_transport_unique {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T)
    (b : SlabField n T) (X : ℝ → ℝ → P201Specs.Space n → P201Specs.Space n)
    (hX : SlabFlowProperties b X) {𝕜 : Type} [RCLike 𝕜]
    (q f : ℝ × P201Specs.Space n → 𝕜) (g : P201Specs.Space n → 𝕜)
    (hq : ContinuousOn q (Icc 0 T ×ˢ univ)) (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    {u v : ℝ × P201Specs.Space n → 𝕜}
    (hu : IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity q f g u)
    (hv : IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity q f g v) :
    EqOn u v (Icc 0 T ×ˢ univ) := by
  have hU := slabRepresentation n hn T hT b X hX 𝕜 q f g hq hf u hu
  have hV := slabRepresentation n hn T hT b X hX 𝕜 q f g hq hf v hv
  exact fun p hp => (hU hp).trans (hV hp).symm

/-- The homogeneous formula solves the PDE, including the degenerate slab.
For positive length, differentiate its constancy along the characteristic.
At zero length, the unused normal differential can be chosen freely. -/
theorem homogeneous_solution {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → P201Specs.Space n → P201Specs.Space n}
    (hX : SlabFlowProperties b X) {𝕜 : Type*} [RCLike 𝕜]
    {g : P201Specs.Space n → 𝕜} (hg : ContDiff ℝ 1 g) :
    IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity
      (fun _ => 0) (fun _ => 0) g (homogeneousFormula X g) := by
  have hreg := homogeneous_regular hT hX hg
  refine ⟨⟨hreg, ?_⟩, fun y _ => homogeneous_initial hT hX g y⟩
  intro p hp
  obtain ⟨du, hdu⟩ := hreg.differentiableOn one_ne_zero p hp
  by_cases hpos : 0 < T
  · let x : ℝ → P201Specs.Space n := fun r => X r p.1 p.2
    have hx := hX.solution p.1 hp.1 p.2
    have hgraph : MapsTo (fun r => (r, x r)) (Icc 0 T) (Icc 0 T ×ˢ univ) :=
      fun r hr => ⟨hr, mem_univ _⟩
    have hpt : (p.1, x p.1) = p := by simp [x, hX.initial p.1 hp.1]
    have hdup : HasFDerivWithinAt (homogeneousFormula X g) du (Icc 0 T ×ˢ univ)
        (p.1, x p.1) := by rw [hpt]; exact hdu
    have hdiff := hdup.comp_hasDerivWithinAt p.1
      ((hasDerivWithinAt_id p.1 (Icc 0 T)).prodMk (hx.2 p.1 hp.1)) hgraph
    rw [hpt] at hdiff
    have hconst : EqOn (fun r => homogeneousFormula X g (r, x r))
        (fun _ => homogeneousFormula X g p) (Icc 0 T) := by
      intro r hr
      dsimp only [homogeneousFormula, x]
      rw [hX.composition 0 ⟨le_rfl, hT⟩ r hr p.1 hp.1 p.2]
    have hz : HasDerivWithinAt (fun r => homogeneousFormula X g (r, x r)) 0
        (Icc 0 T) p.1 :=
      (hasDerivWithinAt_const p.1 (Icc 0 T) (homogeneousFormula X g p)).congr
        hconst (hconst hp.1)
    have he := UniqueDiffWithinAt.eq_deriv (Icc 0 T)
      (uniqueDiffOn_Icc hpos p.1 hp.1) hdiff hz
    exact ⟨du, hdu, by simpa only [zero_mul, add_zero] using he⟩
  · have hT0 : T = 0 := le_antisymm (not_lt.mp hpos) hT
    subst T
    have hp0 : p.1 = 0 := le_antisymm hp.1.2 hp.1.1
    let C : 𝕜 := du (1, b.velocity p)
    let normal : (ℝ × P201Specs.Space n) →L[ℝ] 𝕜 :=
      (ContinuousLinearMap.fst ℝ ℝ (P201Specs.Space n)).smulRight C
    have hn : HasFDerivWithinAt (fun _ : ℝ × P201Specs.Space n => (0 : 𝕜))
        normal (Icc 0 0 ×ˢ univ) p := by
      apply ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).smul_const C).hasFDerivWithinAt.congr
      · intro z hz
        have hz0 : z.1 = 0 := le_antisymm hz.1.2 hz.1.1
        simp [hz0]
      · simp [hp0]
    refine ⟨du - normal, ?_, ?_⟩
    · have hh := hdu.sub hn
      change HasFDerivWithinAt (fun z => homogeneousFormula X g z - 0)
        (du - normal) (Icc 0 0 ×ˢ univ) p at hh
      simpa only [sub_zero] using hh
    · simp [normal, C]

/-- With no lower-order terms the two-term formula reduces to pullback. -/
theorem transportFormula_zero {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (X : ℝ → ℝ → P201Specs.Space n → P201Specs.Space n)
    (g : P201Specs.Space n → 𝕜) :
    transportFormula X (fun _ => 0) (fun _ => 0) g = homogeneousFormula X g := by
  funext p
  simp [transportFormula, homogeneousFormula, NormedSpace.exp_zero]

/-- Necessity of the characteristic formula on the actual local domain.
The maximal interval is used only as the interval of integration/uniqueness;
no field or data are extended beyond their original domains. -/
theorem local_representation {n : ℕ} {b : LocalField n} (hX : LocalFlowProperties b)
    {𝕜 : Type*} [RCLike 𝕜] (A : Set (P201Specs.Space n))
    (q f : ℝ × P201Specs.Space n → 𝕜) (g : P201Specs.Space n → 𝕜)
    (hq : ContinuousOn q b.domain) (hf : ContinuousOn f b.domain)
    {u : ℝ × P201Specs.Space n → 𝕜}
    (hu : IsTransportIVPOn (transportDomain b A) A b.velocity q f g u) :
    EqOn u (transportFormula (P201Specs.Hyperbolic.localFlow b) q f g)
      (transportDomain b A) := by
  intro p hp
  let J := Specs.D13Unified.Ch04.MaximalSolutionMap.parameterMaximalIntervalValue
    b.equation p.1 p.2 0
  let x : ℝ → P201Specs.Space n := fun r => P201Specs.Hyperbolic.localFlow b r p.1 p.2
  have hdom : ∀ r ∈ J.carrier, (r, p.1, p.2) ∈ localFlowDomain b :=
    fun r hr => ⟨hp.1.1, hr⟩
  have hzero : (0 : ℝ) ∈ J.carrier := hp.1.2
  have htime : p.1 ∈ J.carrier := (hX.initial p.1 p.2 hp.1.1).1.2
  have hxd : ∀ r ∈ J.carrier, HasDerivAt x (b.velocity (r, x r)) r :=
    fun r hr => (hX.equation r p.1 p.2 (hdom r hr)).2
  have hxc : ContinuousOn x J.carrier := fun r hr =>
    (hxd r hr).continuousAt.continuousWithinAt
  have hcurve : ContinuousOn (fun r => (r, x r)) J.carrier :=
    continuousOn_id.prodMk hxc
  have hgraph : MapsTo (fun r => (r, x r)) J.carrier b.domain :=
    fun r hr => (hX.equation r p.1 p.2 (hdom r hr)).1
  have hreach : MapsTo (fun r => (r, x r)) J.carrier (transportDomain b A) := by
    intro r hr
    have hc := hX.composition r p.1 p.2 (hdom r hr) 0
    exact ⟨hc.1.mpr hp.1, by simpa only [x, hc.2 hp.1] using hp.2⟩
  let Q : ℝ → 𝕜 := fun r => q (r, x r)
  let F : ℝ → 𝕜 := fun r => f (r, x r)
  have hQ : ContinuousOn Q J.carrier := hq.comp hcurve hgraph
  have hF : ContinuousOn F J.carrier := hf.comp hcurve hgraph
  have hI : D13Unified.ScalarLinear.IsIVP J.toTimeInterval
      (fun r => -Q r) F 0 (g (x 0)) (fun r => u (r, x r)) := by
    refine ⟨hu.1.1.continuousOn.comp hcurve hreach, hzero, hu.2 (x 0) hp.2, ?_⟩
    exact derivative_along_characteristic hu.1 hreach
      (fun r hr => (hxd r hr).hasDerivWithinAt)
  have he := D13Unified.ScalarLinear.eq_variation_of_isIVP J.toTimeInterval
    (fun r => -Q r) F 0 (g (x 0)) hQ.neg hF hI htime
  rw [variation_eq_two_term_on J.toTimeInterval hzero htime Q F hQ] at he
  simpa only [x, Q, F, (hX.initial p.1 p.2 hp.1.1).2, transportFormula] using he

/-- The region in the local assertion is open, as a relative preimage on the
actual inverse-flow domain. -/
theorem isOpen_transportDomain {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) {A : Set (P201Specs.Space n)} (hA : IsOpen A) :
    IsOpen (transportDomain b A) := by
  have hback : ContDiffOn ℝ 1 (fun p : ℝ × P201Specs.Space n =>
      P201Specs.Hyperbolic.localFlow b 0 p.1 p.2)
      {p | (0, p.1, p.2) ∈ localFlowDomain b} :=
    hX.regular.comp (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => hp)
  exact hback.continuousOn.isOpen_inter_preimage
    (hX.open_domain.preimage (continuous_const.prodMk continuous_id)) hA

/-- Local homogeneous existence on the source's characteristic domain. -/
theorem local_homogeneous_solution {n : ℕ} {b : LocalField n} (hX : LocalFlowProperties b)
    {A : Set (P201Specs.Space n)} (_hA : IsOpen A)
    (hA0 : ∀ y ∈ A, (0, y) ∈ b.domain) {𝕜 : Type*} [RCLike 𝕜]
    {g : P201Specs.Space n → 𝕜} (hg : ContDiffOn ℝ 1 g A) :
    IsTransportIVPOn (transportDomain b A) A b.velocity
      (fun _ => 0) (fun _ => 0) g
      (homogeneousFormula (P201Specs.Hyperbolic.localFlow b) g) := by
  have hreg : ContDiffOn ℝ 1 (homogeneousFormula (P201Specs.Hyperbolic.localFlow b) g)
      (transportDomain b A) := by
    exact hg.comp (hX.regular.comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => hp.1)) (fun p hp => hp.2)
  refine ⟨⟨hreg, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨du, hdu⟩ := hreg.differentiableOn one_ne_zero p hp
    let x : ℝ → P201Specs.Space n := fun r => P201Specs.Hyperbolic.localFlow b r p.1 p.2
    let J : Set ℝ := {r | (r, p.1, p.2) ∈ localFlowDomain b}
    have hJo : IsOpen J := hX.open_domain.preimage (continuous_id.prodMk continuous_const)
    have htime : p.1 ∈ J := (hX.initial p.1 p.2 hp.1.1).1
    have hgraph : MapsTo (fun r => (r, x r)) J (transportDomain b A) := by
      intro r hr
      have hc := hX.composition r p.1 p.2 hr 0
      exact ⟨hc.1.mpr hp.1, by simpa only [x, hc.2 hp.1] using hp.2⟩
    have hpt : (p.1, x p.1) = p := by
      simp [x, (hX.initial p.1 p.2 hp.1.1).2]
    have hdup : HasFDerivWithinAt
        (homogeneousFormula (P201Specs.Hyperbolic.localFlow b) g) du (transportDomain b A)
        (p.1, x p.1) := by rw [hpt]; exact hdu
    have hdx := (hX.equation p.1 p.1 p.2 htime).2.hasDerivWithinAt (s := J)
    have hdiff := hdup.comp_hasDerivWithinAt p.1
      ((hasDerivWithinAt_id p.1 J).prodMk hdx) hgraph
    rw [hpt] at hdiff
    have hconst : EqOn (fun r => homogeneousFormula (P201Specs.Hyperbolic.localFlow b) g (r, x r))
        (fun _ => homogeneousFormula (P201Specs.Hyperbolic.localFlow b) g p) J := by
      intro r hr
      exact congrArg g ((hX.composition r p.1 p.2 hr 0).2 hp.1)
    have hz := (hasDerivWithinAt_const p.1 J
      (homogeneousFormula (P201Specs.Hyperbolic.localFlow b) g p)).congr hconst (hconst htime)
    have he := UniqueDiffWithinAt.eq_deriv J (hJo.uniqueDiffOn p.1 htime) hdiff hz
    exact ⟨du, hdu, by simpa only [zero_mul, add_zero] using he⟩
  · intro y hy
    exact congrArg g (hX.initial 0 y (hA0 y hy)).2

/-- Homogeneous uniqueness is a direct specialization of local representation. -/
theorem local_homogeneous_unique {n : ℕ} {b : LocalField n} (hX : LocalFlowProperties b)
    {𝕜 : Type*} [RCLike 𝕜] (A : Set (P201Specs.Space n)) (g : P201Specs.Space n → 𝕜)
    {u : ℝ × P201Specs.Space n → 𝕜}
    (hu : IsTransportIVPOn (transportDomain b A) A b.velocity
      (fun _ => 0) (fun _ => 0) g u) :
    EqOn u (homogeneousFormula (P201Specs.Hyperbolic.localFlow b) g) (transportDomain b A) := by
  simpa only [transportFormula_zero] using
    local_representation hX A (fun _ => 0) (fun _ => 0) g continuousOn_const continuousOn_const hu

/-- Rebase the two-term expression along a characteristic. All integrals stay
in `J`; the composition law is needed only there. -/
theorem transportFormula_rebase {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (X : ℝ → ℝ → P201Specs.Space n → P201Specs.Space n)
    (q f : ℝ × P201Specs.Space n → 𝕜) (g : P201Specs.Space n → 𝕜)
    (J : D13Unified.TimeInterval) (hzero : (0 : ℝ) ∈ J.carrier)
    {r t : ℝ} (hr : r ∈ J.carrier) (y : P201Specs.Space n)
    (hcomp : ∀ v ∈ J.carrier, X v r (X r t y) = X v t y) :
    transportFormula X q f g (r, X r t y) =
      NormedSpace.exp (-(∫ v in (0 : ℝ)..r, q (v, X v t y))) * g (X 0 t y) +
      ∫ s in (0 : ℝ)..r,
        NormedSpace.exp (-(∫ v in s..r, q (v, X v t y))) * f (s, X s t y) := by
  have hqi {a c : ℝ} (ha : a ∈ J.carrier) (hc : c ∈ J.carrier) :
      (∫ v in a..c, q (v, X v r (X r t y))) = ∫ v in a..c, q (v, X v t y) := by
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [hcomp v (J.ordConnected.uIcc_subset ha hc hv)]
  dsimp only [transportFormula]
  rw [hqi hzero hr, hcomp 0 hzero]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsJ := J.ordConnected.uIcc_subset hzero hr hs
  dsimp only
  rw [hqi hsJ hr, hcomp s hsJ]

/-- The formula satisfies the scalar ODE along every slab characteristic,
without yet asserting differentiability in the spatial parameter. -/
theorem slab_formula_isIVP {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → P201Specs.Space n → P201Specs.Space n}
    (hX : SlabFlowProperties b X) {𝕜 : Type} [RCLike 𝕜]
    (q f : ℝ × P201Specs.Space n → 𝕜) (g : P201Specs.Space n → 𝕜)
    (hq : ContinuousOn q (Icc 0 T ×ˢ univ)) (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc 0 T) (y : P201Specs.Space n) :
    D13Unified.ScalarLinear.IsIVP
      ⟨Icc 0 T, nonempty_Icc.mpr hT, ordConnected_Icc⟩
      (fun r => -q (r, X r t y)) (fun r => f (r, X r t y)) 0 (g (X 0 t y))
      (fun r => transportFormula X q f g (r, X r t y)) := by
  let J : D13Unified.TimeInterval := ⟨Icc 0 T, nonempty_Icc.mpr hT, ordConnected_Icc⟩
  have hgraph : MapsTo (fun r => (r, X r t y)) J.carrier (Icc 0 T ×ˢ univ) :=
    fun r hr => ⟨hr, mem_univ _⟩
  have hcurve : ContinuousOn (fun r => (r, X r t y)) J.carrier :=
    continuousOn_id.prodMk (hX.solution t ht y).1
  have hQ := hq.comp hcurve hgraph
  have hF := hf.comp hcurve hgraph
  apply (D13Unified.ScalarLinear.variation_of_constants J
    (fun r => -q (r, X r t y)) (fun r => f (r, X r t y))
    0 (g (X 0 t y)) hQ.neg hF ⟨le_rfl, hT⟩).2 _ |>.mpr
  intro r hr
  rw [variation_eq_two_term hr (fun v => q (v, X v t y))
    (fun v => f (v, X v t y)) hQ]
  exact transportFormula_rebase X q f g J ⟨le_rfl, hT⟩ hr y
    (fun v hv => hX.composition v hv r hr t ht y)

/-- C¹ regularity of the displayed formula suffices to finish slab existence.
This is an assembly lemma, not an extra assumption in `transportFlowStatement`.
The remaining analytic obligation is to prove this regularity from `SpatialC1`. -/
theorem slab_formula_solution_of_regular {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {b : SlabField n T} {X : ℝ → ℝ → P201Specs.Space n → P201Specs.Space n}
    (hX : SlabFlowProperties b X) {𝕜 : Type} [RCLike 𝕜]
    (q f : ℝ × P201Specs.Space n → 𝕜) (g : P201Specs.Space n → 𝕜)
    (hq : ContinuousOn q (Icc 0 T ×ˢ univ)) (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hreg : ContDiffOn ℝ 1 (transportFormula X q f g) (Icc 0 T ×ˢ univ)) :
    IsTransportIVPOn (Icc 0 T ×ˢ univ) univ b.velocity q f g (transportFormula X q f g) := by
  refine ⟨⟨hreg, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨du, hdu⟩ := hreg.differentiableOn one_ne_zero p hp
    by_cases hpos : 0 < T
    · let x : ℝ → P201Specs.Space n := fun r => X r p.1 p.2
      have hx := hX.solution p.1 hp.1 p.2
      have hgraph : MapsTo (fun r => (r, x r)) (Icc 0 T) (Icc 0 T ×ˢ univ) :=
        fun r hr => ⟨hr, mem_univ _⟩
      have hpt : (p.1, x p.1) = p := by simp [x, hX.initial p.1 hp.1]
      have hdup : HasFDerivWithinAt (transportFormula X q f g) du (Icc 0 T ×ˢ univ)
          (p.1, x p.1) := by rw [hpt]; exact hdu
      have hdiff := hdup.comp_hasDerivWithinAt p.1
        ((hasDerivWithinAt_id p.1 (Icc 0 T)).prodMk (hx.2 p.1 hp.1)) hgraph
      have hscalar := (slab_formula_isIVP hT hX q f g hq hf hp.1 p.2).2.2.2 p.1 hp.1
      change HasDerivWithinAt (fun r => transportFormula X q f g (r, x r))
        (-q (p.1, x p.1) * transportFormula X q f g (p.1, x p.1) + f (p.1, x p.1))
        (Icc 0 T) p.1 at hscalar
      rw [hpt] at hdiff hscalar
      have he := UniqueDiffWithinAt.eq_deriv (Icc 0 T)
        (uniqueDiffOn_Icc hpos p.1 hp.1) hdiff hscalar
      refine ⟨du, hdu, ?_⟩
      rw [he]
      ring
    · have hT0 : T = 0 := le_antisymm (not_lt.mp hpos) hT
      subst T
      have hp0 : p.1 = 0 := le_antisymm hp.1.2 hp.1.1
      let C : 𝕜 := du (1, b.velocity p) + q p * transportFormula X q f g p - f p
      let normal : (ℝ × P201Specs.Space n) →L[ℝ] 𝕜 :=
        (ContinuousLinearMap.fst ℝ ℝ (P201Specs.Space n)).smulRight C
      have hn : HasFDerivWithinAt (fun _ : ℝ × P201Specs.Space n => (0 : 𝕜))
          normal (Icc 0 0 ×ˢ univ) p := by
        apply ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).smul_const C).hasFDerivWithinAt.congr
        · intro z hz
          have hz0 : z.1 = 0 := le_antisymm hz.1.2 hz.1.1
          simp [hz0]
        · simp [hp0]
      refine ⟨du - normal, ?_, ?_⟩
      · have hh := hdu.sub hn
        change HasFDerivWithinAt (fun z => transportFormula X q f g z - 0)
          (du - normal) (Icc 0 0 ×ˢ univ) p at hh
        simpa only [sub_zero] using hh
      · simp [normal, C]
        ring
  · intro y _
    simp [transportFormula, hX.initial 0 ⟨le_rfl, hT⟩, NormedSpace.exp_zero]

/-- Scalar ODE for the inhomogeneous formula on an actual maximal local
characteristic; no spatial regularity of the formula is used here. -/
theorem local_formula_isIVP {n : ℕ} {b : LocalField n} (hX : LocalFlowProperties b)
    {𝕜 : Type} [RCLike 𝕜] (q f : ℝ × P201Specs.Space n → 𝕜)
    (g : P201Specs.Space n → 𝕜) (hq : ContinuousOn q b.domain) (hf : ContinuousOn f b.domain)
    {p : ℝ × P201Specs.Space n} (hp : (0, p.1, p.2) ∈ localFlowDomain b) :
    let J := Specs.D13Unified.Ch04.MaximalSolutionMap.parameterMaximalIntervalValue
      b.equation p.1 p.2 0
    D13Unified.ScalarLinear.IsIVP J.toTimeInterval
      (fun r => -q (r, P201Specs.Hyperbolic.localFlow b r p.1 p.2))
      (fun r => f (r, P201Specs.Hyperbolic.localFlow b r p.1 p.2))
      0 (g (P201Specs.Hyperbolic.localFlow b 0 p.1 p.2))
      (fun r => transportFormula (P201Specs.Hyperbolic.localFlow b) q f g
        (r, P201Specs.Hyperbolic.localFlow b r p.1 p.2)) := by
  let J := Specs.D13Unified.Ch04.MaximalSolutionMap.parameterMaximalIntervalValue
    b.equation p.1 p.2 0
  let x : ℝ → P201Specs.Space n := fun r => P201Specs.Hyperbolic.localFlow b r p.1 p.2
  have hdom : ∀ r ∈ J.carrier, (r, p.1, p.2) ∈ localFlowDomain b :=
    fun r hr => ⟨hp.1, hr⟩
  have hzero : (0 : ℝ) ∈ J.carrier := hp.2
  have hcurve : ContinuousOn (fun r => (r, x r)) J.carrier :=
    continuousOn_id.prodMk (fun r hr =>
      (hX.equation r p.1 p.2 (hdom r hr)).2.continuousAt.continuousWithinAt)
  have hgraph : MapsTo (fun r => (r, x r)) J.carrier b.domain :=
    fun r hr => (hX.equation r p.1 p.2 (hdom r hr)).1
  have hQ : ContinuousOn (fun r => q (r, x r)) J.carrier := hq.comp hcurve hgraph
  have hF : ContinuousOn (fun r => f (r, x r)) J.carrier := hf.comp hcurve hgraph
  apply (D13Unified.ScalarLinear.variation_of_constants J.toTimeInterval
    (fun r => -q (r, x r)) (fun r => f (r, x r))
    0 (g (x 0)) hQ.neg hF hzero).2 _ |>.mpr
  intro r hr
  rw [variation_eq_two_term_on J.toTimeInterval hzero hr
    (fun v => q (v, x v)) (fun v => f (v, x v)) hQ]
  exact transportFormula_rebase (P201Specs.Hyperbolic.localFlow b) q f g J.toTimeInterval
    hzero hr p.2 (fun v hv => (hX.composition r p.1 p.2 (hdom r hr) v).2 (hdom v hv))

/-- Local assembly from the sole remaining regularity obligation. -/
theorem local_formula_solution_of_regular {n : ℕ} {b : LocalField n} (hX : LocalFlowProperties b)
    {𝕜 : Type} [RCLike 𝕜] (A : Set (P201Specs.Space n))
    (hA0 : ∀ y ∈ A, (0, y) ∈ b.domain)
    (q f : ℝ × P201Specs.Space n → 𝕜) (g : P201Specs.Space n → 𝕜)
    (hq : ContinuousOn q b.domain) (hf : ContinuousOn f b.domain)
    (hreg : ContDiffOn ℝ 1 (transportFormula (P201Specs.Hyperbolic.localFlow b) q f g)
      (transportDomain b A)) :
    IsTransportIVPOn (transportDomain b A) A b.velocity q f g
      (transportFormula (P201Specs.Hyperbolic.localFlow b) q f g) := by
  refine ⟨⟨hreg, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨du, hdu⟩ := hreg.differentiableOn one_ne_zero p hp
    let J := Specs.D13Unified.Ch04.MaximalSolutionMap.parameterMaximalIntervalValue
      b.equation p.1 p.2 0
    let x : ℝ → P201Specs.Space n := fun r => P201Specs.Hyperbolic.localFlow b r p.1 p.2
    have hdom : ∀ r ∈ J.carrier, (r, p.1, p.2) ∈ localFlowDomain b :=
      fun r hr => ⟨hp.1.1, hr⟩
    have htime : p.1 ∈ J.carrier := (hX.initial p.1 p.2 hp.1.1).1.2
    have hreach : MapsTo (fun r => (r, x r)) J.carrier (transportDomain b A) := by
      intro r hr
      have hc := hX.composition r p.1 p.2 (hdom r hr) 0
      exact ⟨hc.1.mpr hp.1, by simpa only [x, hc.2 hp.1] using hp.2⟩
    have hpt : (p.1, x p.1) = p := by simp [x, (hX.initial p.1 p.2 hp.1.1).2]
    have hdup : HasFDerivWithinAt (transportFormula (P201Specs.Hyperbolic.localFlow b) q f g)
        du (transportDomain b A) (p.1, x p.1) := by rw [hpt]; exact hdu
    have hdx := (hX.equation p.1 p.1 p.2 (hdom p.1 htime)).2.hasDerivWithinAt
      (s := J.carrier)
    have hdiff := hdup.comp_hasDerivWithinAt p.1
      ((hasDerivWithinAt_id p.1 J.carrier).prodMk hdx) hreach
    have hscalar := (local_formula_isIVP hX q f g hq hf hp.1).2.2.2 p.1 htime
    change HasDerivWithinAt
      (fun r => transportFormula (P201Specs.Hyperbolic.localFlow b) q f g (r, x r))
      (-q (p.1, x p.1) * transportFormula (P201Specs.Hyperbolic.localFlow b) q f g
        (p.1, x p.1) + f (p.1, x p.1)) J.carrier p.1 at hscalar
    rw [hpt] at hdiff hscalar
    have he := UniqueDiffWithinAt.eq_deriv J.carrier (J.isOpen.uniqueDiffOn p.1 htime)
      hdiff hscalar
    refine ⟨du, hdu, ?_⟩
    rw [he]
    ring
  · intro y hy
    simp [transportFormula, (hX.initial 0 y (hA0 y hy)).2, NormedSpace.exp_zero]

theorem localRepresentation : localRepresentationStatement := by
  intro n hn b hX 𝕜 _ A q f g hq hf u hu
  exact local_representation hX A q f g hq hf hu

/-- Complete homogeneous transport theorem, without any regularity certificate. -/
theorem homogeneousTransport : homogeneousTransportStatement := by
  constructor
  · intro n hn T hT b
    obtain ⟨X, hX⟩ := slabFlow n hn T hT b
    refine ⟨X, hX, ?_⟩
    intro 𝕜 _ g hg
    refine ⟨homogeneous_solution hT hX hg, ?_⟩
    intro u hu
    simpa only [transportFormula_zero] using
      slabRepresentation n hn T hT b X hX 𝕜 (fun _ => 0) (fun _ => 0) g
        continuousOn_const continuousOn_const u hu
  · intro n hn b
    have hX := P201.Hyperbolic.localFlow n hn b
    refine ⟨hX, ?_⟩
    intro A hA hA0 𝕜 _ g hg
    exact ⟨local_homogeneous_solution hX hA hA0 hg,
      fun u hu => local_homogeneous_unique hX A g hu⟩

/-- Assembly of the full theorem from the two explicitly outstanding analytic
regularity obligations. No such obligation is assumed by the final Spec. -/
theorem transportFlow_of_regular : regularityAssemblyStatement := by
  intro hs hl
  constructor
  · intro n hn T hT b
    obtain ⟨X, hX⟩ := slabFlow n hn T hT b
    refine ⟨X, hX, ?_⟩
    intro 𝕜 _ g hg
    refine ⟨⟨homogeneous_solution hT hX hg, ?_⟩, ?_⟩
    · intro u hu
      simpa only [transportFormula_zero] using
        slabRepresentation n hn T hT b X hX 𝕜 (fun _ => 0) (fun _ => 0) g
          continuousOn_const continuousOn_const u hu
    · intro q f hq hf
      exact ⟨slab_formula_solution_of_regular hT hX q f g hq.continuous hf.continuous
          (hs n hn T hT b X hX 𝕜 g hg q f hq hf),
        fun u hu => slabRepresentation n hn T hT b X hX 𝕜 q f g hq.continuous hf.continuous u hu⟩
  · intro n hn b
    have hX := P201.Hyperbolic.localFlow n hn b
    refine ⟨hX, ?_⟩
    intro A hA hA0 𝕜 _ g hg
    refine ⟨⟨local_homogeneous_solution hX hA hA0 hg,
      fun u hu => local_homogeneous_unique hX A g hu⟩, ?_⟩
    intro q f hq hf
    exact ⟨local_formula_solution_of_regular hX A hA0 q f g hq.continuous hf.continuous
        (hl n hn b hX A hA hA0 𝕜 g hg q f hq hf),
      fun u hu => local_representation hX A q f g hq.continuous hf.continuous hu⟩

/-- Differentiation in a spatial parameter on a compact time interval needs
only joint continuity of the integrand and its spatial differential. The
bound is obtained locally from compactness, not assumed globally. -/
theorem hasFDerivAt_spatial_integral {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℝ × E → F) (dh : ℝ × E → E →L[ℝ] F)
    (hc : Continuous h) (hdc : Continuous dh)
    (hd : ∀ t y, HasFDerivAt (fun z => h (t, z)) (dh (t, y)) y)
    (a b : ℝ) (y : E) :
    HasFDerivAt (fun z => ∫ t in a..b, h (t, z))
      (∫ t in a..b, dh (t, y)) y := by
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod (isCompact_closedBall y 1)).exists_bound_of_continuousOn
    hdc.continuousOn
  have hslice (z : E) : Continuous (fun t => h (t, z)) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hdslice (z : E) : Continuous (fun t => dh (t, z)) :=
    hdc.comp (continuous_id.prodMk continuous_const)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball y 1) (F' := fun z t => dh (t, z))
    (bound := fun _ => C) (Metric.ball_mem_nhds y zero_lt_one)
  · exact Filter.Eventually.of_forall fun z => (hslice z).aestronglyMeasurable
  · exact (hslice y).intervalIntegrable a b
  · exact (hdslice y).aestronglyMeasurable
  · exact MeasureTheory.ae_of_all _ fun t ht z hz =>
      hC (t, z) ⟨uIoc_subset_uIcc ht, Metric.ball_subset_closedBall hz⟩
  · exact intervalIntegrable_const
  · exact MeasureTheory.ae_of_all _ fun t _ z _ => hd t z

/-- A time primitive of continuous, spatially C¹ data is jointly C¹.
No time differentiability of the integrand is required. -/
theorem contDiff_spatial_primitive {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (h : ℝ × E → F) (dh : ℝ × E → E →L[ℝ] F)
    (hc : Continuous h) (hdc : Continuous dh)
    (hd : ∀ t y, HasFDerivAt (fun z => h (t, z)) (dh (t, y)) y) (a : ℝ) :
    ContDiff ℝ 1 (fun p : ℝ × E => ∫ t in a..p.1, h (t, p.2)) := by
  let dspace : ℝ × E → E →L[ℝ] F := fun p => ∫ t in a..p.1, dh (t, p.2)
  let dtime : ℝ × E → ℝ →L[ℝ] F := fun p => (1 : ℝ →L[ℝ] ℝ).smulRight (h p)
  have hcs : Continuous dspace := by
    exact (intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := fun y t => dh (t, y)) (hdc.comp continuous_swap)).comp continuous_swap
  have hct : Continuous dtime := by
    exact (ContinuousLinearMap.smulRightL ℝ ℝ F (1 : ℝ →L[ℝ] ℝ)).continuous.comp hc
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun p => (dtime p).coprod (dspace p), hct.continuousLinearMapCoprod hcs, ?_⟩
  intro p
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun t y => ∫ r in a..t, h (r, y))
    (f₁ := fun t y => dtime (t, y)) (f₂ := fun t y => dspace (t, y))
  · exact Filter.Eventually.of_forall fun v =>
      ((hc.comp (continuous_id.prodMk continuous_const)).integral_hasStrictDerivAt a v.1).hasStrictFDerivAt.hasFDerivAt
  · exact Filter.Eventually.of_forall fun v =>
      hasFDerivAt_spatial_integral h dh hc hdc hd a v.1 v.2
  · exact hct.continuousAt
  · exact hcs.continuousAt

/-- Closed-slab version of the primitive lemma. Clamping only the time
variable extends the continuous spatial differential, including when `T = 0`. -/
theorem contDiffOn_spatial_primitive_slab {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    {𝕜 : Type*} [RCLike 𝕜] {h : ℝ × P201Specs.Space n → 𝕜}
    (hh : SpatialC1 (Icc 0 T ×ˢ univ) h) :
    ContDiffOn ℝ 1 (fun p : ℝ × P201Specs.Space n => ∫ t in (0 : ℝ)..p.1, h (t, p.2))
      (Icc 0 T ×ˢ univ) := by
  obtain ⟨dh, hdc, hd⟩ := hh.spatial
  let c : ℝ → ℝ := fun t => (projIcc 0 T hT t : ℝ)
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hc_mem (t : ℝ) : c t ∈ Icc 0 T := (projIcc 0 T hT t).property
  have hc_eq (t : ℝ) (ht : t ∈ Icc 0 T) : c t = t := by
    exact congrArg Subtype.val (projIcc_of_mem hT ht)
  have hext : ContDiff ℝ 1 (fun p : ℝ × P201Specs.Space n =>
      ∫ t in (0 : ℝ)..p.1, h (c t, p.2)) := by
    refine contDiff_spatial_primitive (fun p => h (c p.1, p.2))
      (fun p => dh (c p.1, p.2)) ?_ ?_ ?_ 0
    · exact hh.continuous.comp_continuous ((hc.comp continuous_fst).prodMk continuous_snd)
        (fun p => ⟨hc_mem p.1, mem_univ _⟩)
    · exact hdc.comp_continuous ((hc.comp continuous_fst).prodMk continuous_snd)
        (fun p => ⟨hc_mem p.1, mem_univ _⟩)
    · intro t y
      have H := hd (c t, y) ⟨hc_mem t, mem_univ _⟩
      have hs : {z : P201Specs.Space n | (c t, z) ∈ Icc 0 T ×ˢ univ} = univ := by
        ext z
        simp [hc_mem]
      rw [hs] at H
      exact H.hasFDerivAt (by simp)
  apply hext.contDiffOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hc_eq t (uIcc_subset_Icc ⟨le_rfl, hT⟩ hp.1 ht)]

/-- Products preserve the original continuous-time spatial regularity. -/
theorem spatialC1_mul {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {D : Set (ℝ × P201Specs.Space n)} {u v : ℝ × P201Specs.Space n → 𝕜}
    (hu : SpatialC1 D u) (hv : SpatialC1 D v) : SpatialC1 D (fun p => u p * v p) := by
  obtain ⟨du, hduc, hdu⟩ := hu.spatial
  obtain ⟨dv, hdvc, hdv⟩ := hv.spatial
  refine ⟨hu.continuous.mul hv.continuous,
    fun p => u p • dv p + v p • du p,
    (hu.continuous.smul hdvc).add (hv.continuous.smul hduc), ?_⟩
  intro p hp
  exact (hdu p hp).mul (hdv p hp)

/-- The continuous total differential restricts to a jointly continuous
spatial differential, also at the two time endpoints. -/
theorem spatialC1_of_contDiffOn_slab {n : ℕ} {T : ℝ} (hT : 0 < T)
    {𝕜 : Type*} [RCLike 𝕜] {u : ℝ × P201Specs.Space n → 𝕜}
    (hu : ContDiffOn ℝ 1 u (Icc 0 T ×ˢ univ)) : SpatialC1 (Icc 0 T ×ˢ univ) u := by
  let D : Set (ℝ × P201Specs.Space n) := Icc 0 T ×ˢ univ
  let du := fderivWithin ℝ u D
  have hD : UniqueDiffOn ℝ D := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hduc : ContinuousOn du D := hu.continuousOn_fderivWithin hD le_rfl
  refine ⟨hu.continuousOn, fun p => (du p).comp (ContinuousLinearMap.inr ℝ ℝ _),
    hduc.clm_comp continuousOn_const, ?_⟩
  intro p hp
  have h := (hu.differentiableOn one_ne_zero p hp).hasFDerivWithinAt.comp (f := fun z : P201Specs.Space n => (p.1, z)) p.2
    ((hasFDerivWithinAt_const p.1 p.2 univ).prodMk (hasFDerivWithinAt_id p.2 univ))
    (fun z _ => ⟨hp.1, mem_univ z⟩)
  have hs : {z : P201Specs.Space n | (p.1, z) ∈ Icc 0 T ×ˢ univ} = univ := by
    ext z
    simp [hp.1]
  rw [hs]
  exact h

/-- Pulling back coefficients to Lagrangian coordinates preserves precisely
the spatial regularity assumed in the manuscript. -/
theorem spatialC1_flow_coordinates {n : ℕ} {T : ℝ} (hT : 0 < T)
    {b : SlabField n T} {X : ℝ → ℝ → P201Specs.Space n → P201Specs.Space n}
    (hX : SlabFlowProperties b X) {𝕜 : Type*} [RCLike 𝕜]
    {h : ℝ × P201Specs.Space n → 𝕜} (hh : SpatialC1 (Icc 0 T ×ˢ univ) h) :
    SpatialC1 (Icc 0 T ×ˢ univ) (fun p => h (p.1, X p.1 0 p.2)) := by
  let D : Set (ℝ × P201Specs.Space n) := Icc 0 T ×ˢ univ
  let Y : ℝ × P201Specs.Space n → P201Specs.Space n := fun p => X p.1 0 p.2
  have hY : ContDiffOn ℝ 1 Y D := hX.regular.comp
    (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
    (fun p hp => ⟨hp.1, ⟨le_rfl, hT.le⟩, hp.2⟩)
  let dY := fderivWithin ℝ Y D
  have hD : UniqueDiffOn ℝ D := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hdY : ContinuousOn dY D := hY.continuousOn_fderivWithin hD le_rfl
  obtain ⟨dh, hdc, hd⟩ := hh.spatial
  have hmap : MapsTo (fun p => (p.1, Y p)) D D := fun p hp => ⟨hp.1, mem_univ _⟩
  refine ⟨hh.continuous.comp (continuousOn_fst.prodMk hY.continuousOn) hmap,
    fun p => (dh (p.1, Y p)).comp ((dY p).comp (ContinuousLinearMap.inr ℝ ℝ _)),
    (hdc.comp (continuousOn_fst.prodMk hY.continuousOn) hmap).clm_comp
      (hdY.clm_comp continuousOn_const), ?_⟩
  intro p hp
  have hslice : {z : P201Specs.Space n | (p.1, z) ∈ D} = univ := by
    ext z
    simp [D, hp.1]
  have hy := (hY.differentiableOn one_ne_zero p hp).hasFDerivWithinAt.comp (f := fun z : P201Specs.Space n => (p.1, z)) p.2
    ((hasFDerivWithinAt_const p.1 p.2 univ).prodMk (hasFDerivWithinAt_id p.2 univ))
    (fun z _ => ⟨hp.1, mem_univ z⟩)
  have hdh := hd (p.1, Y p) (hmap hp)
  change HasFDerivWithinAt (fun z => h (p.1, z)) _ {z | (p.1, z) ∈ D} _ at hdh
  rw [hslice] at hdh
  rw [hslice]
  exact hdh.comp p.2 hy (fun z _ => mem_univ _)

/-- C¹ dependence of the integrating-factor solution in Lagrangian
coordinates, with no time derivative of the coefficients. -/
theorem slab_lagrangian_regular {n : ℕ} {T : ℝ} (hT : 0 < T)
    {𝕜 : Type*} [RCLike 𝕜]
    {Q F : ℝ × P201Specs.Space n → 𝕜}
    (hQ : SpatialC1 (Icc 0 T ×ˢ univ) Q) (hF : SpatialC1 (Icc 0 T ×ˢ univ) F)
    {g : P201Specs.Space n → 𝕜} (hg : ContDiff ℝ 1 g) :
    ContDiffOn ℝ 1 (fun p : ℝ × P201Specs.Space n =>
      NormedSpace.exp (-(∫ r in (0 : ℝ)..p.1, Q (r, p.2))) *
        (g p.2 + ∫ s in (0 : ℝ)..p.1,
          NormedSpace.exp (∫ r in (0 : ℝ)..s, Q (r, p.2)) * F (s, p.2)))
      (Icc 0 T ×ˢ univ) := by
  have he : ContDiff ℝ 1 (NormedSpace.exp : 𝕜 → 𝕜) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : 𝕜 → 𝕜) univ from
      fun x _ => NormedSpace.exp_analytic x).contDiff
  have hP := contDiffOn_spatial_primitive_slab hT.le hQ
  have hB := spatialC1_mul (spatialC1_of_contDiffOn_slab hT (he.comp_contDiffOn hP)) hF
  exact (he.comp_contDiffOn hP.neg).mul
    ((hg.comp_contDiffOn contDiffOn_snd).add (contDiffOn_spatial_primitive_slab hT.le hB))

/-- Full inhomogeneous C¹ regularity on the slab from the original coefficient
hypotheses. Lagrangian coordinates avoid differentiating `q` or `f` in time. -/
theorem slabFormulaRegularity : slabFormulaRegularityStatement := by
  intro n hn T hT b X hX 𝕜 _ g hg q f hq hf
  by_cases hpos : 0 < T
  · let Q : ℝ × P201Specs.Space n → 𝕜 := fun p => q (p.1, X p.1 0 p.2)
    let F : ℝ × P201Specs.Space n → 𝕜 := fun p => f (p.1, X p.1 0 p.2)
    have hQ : SpatialC1 (Icc 0 T ×ˢ univ) Q := spatialC1_flow_coordinates hpos hX hq
    have hF : SpatialC1 (Icc 0 T ×ˢ univ) F := spatialC1_flow_coordinates hpos hX hf
    have hV := slab_lagrangian_regular hpos hQ hF hg
    have hback : ContDiffOn ℝ 1 (fun p : ℝ × P201Specs.Space n =>
        (p.1, X 0 p.1 p.2)) (Icc 0 T ×ˢ univ) :=
      contDiffOn_fst.prodMk (hX.regular.comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => ⟨⟨le_rfl, hT⟩, hp⟩))
    apply (hV.comp hback (fun p hp => ⟨hp.1, mem_univ _⟩)).congr
    intro p hp
    let J : D13Unified.TimeInterval := ⟨Icc 0 T, nonempty_Icc.mpr hT, ordConnected_Icc⟩
    have hz : (0 : ℝ) ∈ J.carrier := ⟨le_rfl, hT⟩
    have hc := transportFormula_rebase X q f g J hz hp.1 (X 0 p.1 p.2)
      (t := 0) (fun v hv => hX.composition v hv p.1 hp.1 0 hz _)
    rw [hX.composition p.1 hp.1 0 hz p.1 hp.1 p.2, hX.initial p.1 hp.1,
      hX.initial 0 hz] at hc
    have hqc : ContinuousOn (fun r => Q (r, X 0 p.1 p.2)) (Icc 0 T) :=
      hQ.continuous.comp (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr, mem_univ _⟩)
    have hv := variation_eq_two_term hp.1 (fun r => Q (r, X 0 p.1 p.2))
      (fun r => F (r, X 0 p.1 p.2)) hqc (g (X 0 p.1 p.2))
    simp only [D13Unified.ScalarLinear.variation, D13Unified.ScalarLinear.primitive,
      intervalIntegral.integral_neg, neg_neg] at hv
    dsimp only [Q, F] at hv ⊢
    exact (hv.trans hc.symm).symm
  · have hT0 : T = 0 := le_antisymm (not_lt.mp hpos) hT
    subst T
    apply (homogeneous_regular hT hX hg).congr
    intro p hp
    have hp0 : p.1 = 0 := le_antisymm hp.1.2 hp.1.1
    simp [transportFormula, homogeneousFormula, hp0, NormedSpace.exp_zero]

theorem spatial_tube_rectangle {E : Type*} [PseudoMetricSpace E]
    {D : Set (ℝ × E)} (hD : IsOpen D) {t : ℝ} {y : E}
    (hseg : ∀ r ∈ uIcc 0 t, (r, y) ∈ D) :
    ∃ a b ε : ℝ, 0 < ε ∧ a < min 0 t ∧ max 0 t < b ∧
      (Icc a b ×ˢ Metric.ball y ε) ⊆ D := by
  obtain ⟨δ, hδ, hsub⟩ :=
    (isCompact_uIcc.prod (isCompact_singleton (x := y))).exists_thickening_subset_open hD
      (by rintro ⟨r, z⟩ ⟨hr, hz⟩; have hz' : z = y := hz; subst z; exact hseg r hr)
  refine ⟨min 0 t - δ / 2, max 0 t + δ / 2, δ / 2,
    by linarith, by linarith, by linarith, ?_⟩
  rintro ⟨r, z⟩ ⟨hr, hz⟩
  apply hsub
  rw [Metric.mem_thickening_iff]
  have hzδ : dist z y < δ := lt_trans hz (by linarith)
  by_cases hlo : r ≤ min 0 t
  · refine ⟨(min 0 t, y), ⟨⟨le_rfl, min_le_max⟩, mem_singleton y⟩, ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨?_, hzδ⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith [hr.1]
  · by_cases hhi : max 0 t ≤ r
    · refine ⟨(max 0 t, y), ⟨⟨min_le_max, le_rfl⟩, mem_singleton y⟩, ?_⟩
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨?_, hzδ⟩
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hhi)]
      linarith [hr.2]
    · refine ⟨(r, y), ⟨⟨(not_le.mp hlo).le, (not_le.mp hhi).le⟩, mem_singleton y⟩, ?_⟩
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hzδ


private theorem smooth_ball_compression {n : ℕ} (y : P201Specs.Space n) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : P201Specs.Space n → P201Specs.Space n,
      ContDiff ℝ 1 R ∧ (∀ z, R z ∈ Metric.ball y ε) ∧ R =ᶠ[𝓝 y] id := by
  let φ : ContDiffBump y := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let R : P201Specs.Space n → P201Specs.Space n := fun z => y + φ z • (z - y)
  refine ⟨R, contDiff_const.add (φ.contDiff.smul (contDiff_id.sub contDiff_const)), ?_, ?_⟩
  · intro z
    change dist (y + φ z • (z - y)) y < ε
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg φ.nonneg]
    by_cases hz : z ∈ Metric.ball y ε
    · exact (mul_le_of_le_one_left (norm_nonneg _) φ.le_one).trans_lt
        (mem_ball_iff_norm.mp hz)
    · have hφ : φ z = 0 := φ.zero_of_le_dist (le_of_not_gt hz)
      rw [hφ, zero_mul]
      exact hε
  · filter_upwards [φ.eventuallyEq_one] with z hz
    change y + φ z • (z-y) = z
    rw [hz, Pi.one_apply, one_smul]
    abel

-- This rectangular version is used only after a compact tube has been chosen.
theorem contDiffAt_spatial_primitive_rectangle {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {D : Set (ℝ × P201Specs.Space n)} {h : ℝ × P201Specs.Space n → 𝕜}
    (hDo : IsOpen D) (hh : SpatialC1 D h) {p : ℝ × P201Specs.Space n}
    {a b ε : ℝ} (hε : 0 < ε) (ha : a < min 0 p.1) (hb : max 0 p.1 < b)
    (hrect : Icc a b ×ˢ Metric.ball p.2 ε ⊆ D) :
    ContDiffAt ℝ 1 (fun z : ℝ × P201Specs.Space n => ∫ r in (0 : ℝ)..z.1, h (r,z.2)) p := by
  obtain ⟨R, hR, hRmem, hReq⟩ := smooth_ball_compression p.2 hε
  have hab : a ≤ b := (ha.trans_le (min_le_left _ _)).le.trans ((le_max_left _ _).trans hb.le)
  let c : ℝ → ℝ := fun t => (projIcc a b hab t : ℝ)
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hc_mem (t : ℝ) : c t ∈ Icc a b := (projIcc a b hab t).property
  have hc_eq (t : ℝ) (ht : t ∈ Icc a b) : c t = t := by
    exact congrArg Subtype.val (projIcc_of_mem hab ht)
  obtain ⟨dh, hdc, hd⟩ := hh.spatial
  let Ψ : ℝ × P201Specs.Space n → ℝ × P201Specs.Space n := fun z => (c z.1, R z.2)
  have hΨ : Continuous Ψ := (hc.comp continuous_fst).prodMk (hR.continuous.comp continuous_snd)
  have hΨmem (z : ℝ × P201Specs.Space n) : Ψ z ∈ D := hrect ⟨hc_mem z.1, hRmem z.2⟩
  have hExt : ContDiff ℝ 1 (fun z : ℝ × P201Specs.Space n =>
      ∫ r in (0 : ℝ)..z.1, h (c r,R z.2)) := by
    refine contDiff_spatial_primitive (fun z => h (Ψ z))
      (fun z => (dh (Ψ z)).comp (fderiv ℝ R z.2))
      (hh.continuous.comp_continuous hΨ hΨmem)
      ((hdc.comp_continuous hΨ hΨmem).clm_comp
        ((hR.continuous_fderiv one_ne_zero).comp continuous_snd)) ?_ 0
    intro t y
    have H := hd (Ψ (t,y)) (hΨmem (t,y))
    have hslice : IsOpen {z : P201Specs.Space n | (c t,z) ∈ D} :=
      hDo.preimage (continuous_const.prodMk continuous_id)
    have H' := H.hasFDerivAt (hslice.mem_nhds (hΨmem (t,y)))
    exact H'.comp y ((hR.differentiable one_ne_zero y).hasFDerivAt)
  apply hExt.contDiffAt.congr_of_eventuallyEq
  have hpt : p.1 ∈ Ioo a b := ⟨ha.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb⟩
  have htime : ∀ᶠ z : ℝ × P201Specs.Space n in 𝓝 p, z.1 ∈ Ioo a b :=
    continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hpt)
  have hspace : ∀ᶠ z : ℝ × P201Specs.Space n in 𝓝 p, R z.2 = z.2 :=
    continuous_snd.continuousAt.eventually hReq
  filter_upwards [htime, hspace] with z hzt hzy
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [hzy, hc_eq]
  exact uIcc_subset_Icc
    ⟨(ha.trans_le (min_le_left _ _)).le, (le_max_left _ _).trans hb.le⟩
    ⟨hzt.1.le,hzt.2.le⟩ hr

/-- On an open domain, a continuous spatial differential gives a C¹ time
primitive wherever the full oriented characteristic time segment stays in the domain. -/
theorem contDiffAt_spatial_primitive_open {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {D : Set (ℝ × P201Specs.Space n)} {h : ℝ × P201Specs.Space n → 𝕜}
    (hDo : IsOpen D) (hh : SpatialC1 D h) {p : ℝ × P201Specs.Space n}
    (hseg : ∀ r ∈ uIcc 0 p.1, (r,p.2) ∈ D) :
    ContDiffAt ℝ 1 (fun z : ℝ × P201Specs.Space n =>
      ∫ r in (0 : ℝ)..z.1, h (r,z.2)) p := by
  obtain ⟨a,b,ε,hε,ha,hb,hrect⟩ := spatial_tube_rectangle hDo hseg
  exact contDiffAt_spatial_primitive_rectangle hDo hh hε ha hb hrect

/-- On an open domain, a continuous total differential restricts to a
continuous spatial differential. -/
theorem spatialC1_of_contDiffOn_open {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {D : Set (ℝ × P201Specs.Space n)} (hD : IsOpen D)
    {u : ℝ × P201Specs.Space n → 𝕜} (hu : ContDiffOn ℝ 1 u D) : SpatialC1 D u := by
  have hduc : ContinuousOn (fderiv ℝ u) D :=
    hu.continuousOn_fderiv_of_isOpen hD le_rfl
  refine ⟨hu.continuousOn,
    fun p => (fderiv ℝ u p).comp (ContinuousLinearMap.inr ℝ ℝ _),
    hduc.clm_comp continuousOn_const, ?_⟩
  intro p hp
  have huat := (hu.contDiffAt (hD.mem_nhds hp)).differentiableAt one_ne_zero
  exact (huat.hasFDerivAt.comp p.2
    ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).hasFDerivWithinAt

/-- The forward local flow coordinates exist precisely at these points. -/
def localLagrangianDomain {n : ℕ} (b : LocalField n) (A : Set (P201Specs.Space n)) :
    Set (ℝ × P201Specs.Space n) :=
  {p | (p.1, 0, p.2) ∈ localFlowDomain b ∧ p.2 ∈ A}

theorem isOpen_localLagrangianDomain {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) {A : Set (P201Specs.Space n)} (hA : IsOpen A) :
    IsOpen (localLagrangianDomain b A) := by
  exact (hX.open_domain.preimage
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).inter
    (hA.preimage continuous_snd)

/-- Every integration segment stays in the actual forward-flow domain. -/
theorem localLagrangianDomain_segment {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) {A : Set (P201Specs.Space n)}
    {p : ℝ × P201Specs.Space n} (hp : p ∈ localLagrangianDomain b A)
    {r : ℝ} (hr : r ∈ uIcc 0 p.1) : (r, p.2) ∈ localLagrangianDomain b A := by
  let J := Specs.D13Unified.Ch04.MaximalSolutionMap.parameterMaximalIntervalValue
    b.equation 0 p.2 0
  have hzero : (0 : ℝ) ∈ J.carrier :=
    (hX.initial 0 p.2 hp.1.1).1.2
  have htime : p.1 ∈ J.carrier := hp.1.2
  exact ⟨⟨hp.1.1, J.ordConnected.uIcc_subset hzero htime hr⟩, hp.2⟩

/-- Pulling back local coefficients preserves the stated continuous-time,
spatially C¹ regularity on their actual coordinate domain. -/
theorem spatialC1_local_flow_coordinates {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) {A : Set (P201Specs.Space n)} (hA : IsOpen A)
    {𝕜 : Type*} [RCLike 𝕜] {h : ℝ × P201Specs.Space n → 𝕜}
    (hh : SpatialC1 b.domain h) :
    SpatialC1 (localLagrangianDomain b A)
      (fun p => h (p.1, P201Specs.Hyperbolic.localFlow b p.1 0 p.2)) := by
  let D := localLagrangianDomain b A
  have hD : IsOpen D := isOpen_localLagrangianDomain hX hA
  let Y : ℝ × P201Specs.Space n → P201Specs.Space n :=
    fun p => P201Specs.Hyperbolic.localFlow b p.1 0 p.2
  have hY : ContDiffOn ℝ 1 Y D := hX.regular.comp
    (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
    (fun p hp => hp.1)
  have hdY : ContinuousOn (fderiv ℝ Y) D :=
    hY.continuousOn_fderiv_of_isOpen hD le_rfl
  obtain ⟨dh, hdc, hd⟩ := hh.spatial
  have hmap : MapsTo (fun p => (p.1, Y p)) D b.domain :=
    fun p hp => (hX.equation p.1 0 p.2 hp.1).1
  refine ⟨hh.continuous.comp (continuousOn_fst.prodMk hY.continuousOn) hmap,
    fun p => (dh (p.1, Y p)).comp
      ((fderiv ℝ Y p).comp (ContinuousLinearMap.inr ℝ ℝ _)),
    (hdc.comp (continuousOn_fst.prodMk hY.continuousOn) hmap).clm_comp
      (hdY.clm_comp continuousOn_const), ?_⟩
  intro p hp
  have hy := ((hY.contDiffAt (hD.mem_nhds hp)).differentiableAt one_ne_zero).hasFDerivAt.comp (f := fun z : P201Specs.Space n => (p.1, z)) p.2
    ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))
  have hslice : IsOpen {z : P201Specs.Space n | (p.1, z) ∈ b.domain} :=
    b.isOpen_domain.preimage (continuous_const.prodMk continuous_id)
  have hdh := (hd (p.1, Y p) (hmap hp)).hasFDerivAt
    (hslice.mem_nhds (hmap hp))
  exact (hdh.comp p.2 hy).hasFDerivWithinAt


/-- Integration on the actual local forward-flow domain is jointly C¹. -/
theorem contDiffOn_spatial_primitive_local {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) {A : Set (P201Specs.Space n)} (hA : IsOpen A)
    {𝕜 : Type} [RCLike 𝕜] {h : ℝ × P201Specs.Space n → 𝕜}
    (hh : SpatialC1 (localLagrangianDomain b A) h) :
    ContDiffOn ℝ 1 (fun p : ℝ × P201Specs.Space n =>
      ∫ r in (0 : ℝ)..p.1, h (r, p.2)) (localLagrangianDomain b A) := by
  intro p hp
  exact (contDiffAt_spatial_primitive_open (isOpen_localLagrangianDomain hX hA) hh
    (fun r hr => localLagrangianDomain_segment hX hp hr)).contDiffWithinAt

/-- The integrating-factor solution is C¹ in the actual local flow coordinates. -/
theorem local_lagrangian_regular {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) {A : Set (P201Specs.Space n)} (hA : IsOpen A)
    {𝕜 : Type} [RCLike 𝕜] {Q F : ℝ × P201Specs.Space n → 𝕜}
    (hQ : SpatialC1 (localLagrangianDomain b A) Q)
    (hF : SpatialC1 (localLagrangianDomain b A) F)
    {g : P201Specs.Space n → 𝕜} (hg : ContDiffOn ℝ 1 g A) :
    ContDiffOn ℝ 1 (fun p : ℝ × P201Specs.Space n =>
      NormedSpace.exp (-(∫ r in (0 : ℝ)..p.1, Q (r, p.2))) *
        (g p.2 + ∫ s in (0 : ℝ)..p.1,
          NormedSpace.exp (∫ r in (0 : ℝ)..s, Q (r, p.2)) * F (s, p.2)))
      (localLagrangianDomain b A) := by
  have he : ContDiff ℝ 1 (NormedSpace.exp : 𝕜 → 𝕜) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : 𝕜 → 𝕜) univ from
      fun x _ => NormedSpace.exp_analytic x).contDiff
  have hP := contDiffOn_spatial_primitive_local hX hA hQ
  have hB := spatialC1_mul (spatialC1_of_contDiffOn_open
    (isOpen_localLagrangianDomain hX hA) (he.comp_contDiffOn hP)) hF
  exact (he.comp_contDiffOn hP.neg).mul
    ((hg.comp contDiffOn_snd (fun p hp => hp.2)).add
      (contDiffOn_spatial_primitive_local hX hA hB))

/-- Joint C¹ regularity of the complete local characteristic formula. -/
theorem localFormulaRegularity : localFormulaRegularityStatement := by
  intro n hn b hX A hA hA0 𝕜 _ g hg q f hq hf
  let Q : ℝ × P201Specs.Space n → 𝕜 :=
    fun p => q (p.1, P201Specs.Hyperbolic.localFlow b p.1 0 p.2)
  let F : ℝ × P201Specs.Space n → 𝕜 :=
    fun p => f (p.1, P201Specs.Hyperbolic.localFlow b p.1 0 p.2)
  have hQ : SpatialC1 (localLagrangianDomain b A) Q :=
    spatialC1_local_flow_coordinates hX hA hq
  have hF : SpatialC1 (localLagrangianDomain b A) F :=
    spatialC1_local_flow_coordinates hX hA hf
  have hV := local_lagrangian_regular hX hA hQ hF hg
  have hback : ContDiffOn ℝ 1 (fun p : ℝ × P201Specs.Space n =>
      (p.1, P201Specs.Hyperbolic.localFlow b 0 p.1 p.2)) (transportDomain b A) :=
    contDiffOn_fst.prodMk (hX.regular.comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => hp.1))
  have hbackmap : MapsTo (fun p : ℝ × P201Specs.Space n =>
      (p.1, P201Specs.Hyperbolic.localFlow b 0 p.1 p.2))
      (transportDomain b A) (localLagrangianDomain b A) := by
    intro p hp
    exact ⟨(hX.composition 0 p.1 p.2 hp.1 p.1).1.mpr
      (hX.initial p.1 p.2 hp.1.1).1, hp.2⟩
  apply (hV.comp hback hbackmap).congr
  intro p hp
  let y := P201Specs.Hyperbolic.localFlow b 0 p.1 p.2
  let J := Specs.D13Unified.Ch04.MaximalSolutionMap.parameterMaximalIntervalValue
    b.equation 0 y 0
  have htimeDom : (p.1, 0, y) ∈ localFlowDomain b := (hbackmap hp).1
  have htime : p.1 ∈ J.carrier := htimeDom.2
  have hzero : (0 : ℝ) ∈ J.carrier :=
    (hX.initial 0 y htimeDom.1).1.2
  have hdom : ∀ r ∈ J.carrier, (r, 0, y) ∈ localFlowDomain b :=
    fun r hr => ⟨htimeDom.1, hr⟩
  have hc := transportFormula_rebase (P201Specs.Hyperbolic.localFlow b) q f g
    J.toTimeInterval hzero htime y (t := 0)
    (fun v hv => (hX.composition p.1 0 y htimeDom v).2 (hdom v hv))
  have hidentity : P201Specs.Hyperbolic.localFlow b p.1 0 y = p.2 := by
    exact ((hX.composition 0 p.1 p.2 hp.1 p.1).2
      (hX.initial p.1 p.2 hp.1.1).1).trans
      (hX.initial p.1 p.2 hp.1.1).2
  rw [hidentity, (hX.initial 0 y htimeDom.1).2] at hc
  have hqc : ContinuousOn (fun r => Q (r, y)) J.carrier :=
    hQ.continuous.comp (continuousOn_id.prodMk continuousOn_const)
      (fun r hr => ⟨hdom r hr, hp.2⟩)
  have hv := variation_eq_two_term_on J.toTimeInterval hzero htime
    (fun r => Q (r, y)) (fun r => F (r, y)) hqc (g y)
  simp only [D13Unified.ScalarLinear.variation, D13Unified.ScalarLinear.primitive,
    intervalIntegral.integral_neg, neg_neg] at hv
  dsimp only [Q, F, y] at hv ⊢
  exact (hv.trans hc.symm).symm


/-- The complete transport-by-flow theorem, including inhomogeneous existence,
uniqueness, the source representation, and the global/local flow assertions. -/
theorem transportFlow : transportFlowStatement :=
  transportFlow_of_regular slabFormulaRegularity localFormulaRegularity

end P201.Hyperbolic
