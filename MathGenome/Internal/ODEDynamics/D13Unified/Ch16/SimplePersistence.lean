import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.SimplePersistence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.LinearizedStability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.LinearizedStability
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch16.SimplePersistence

/-- The state partial derivative, with the parameter held fixed. -/
abbrev stateDerivative := Specs.D13Unified.Ch16.SimplePersistence.stateDerivative

/-- All zeros on a fixed parameter/state neighborhood, using the canonical
predicate from the independent specification. -/
abbrev IsLocalZeroGraph := Specs.D13Unified.Ch16.SimplePersistence.IsLocalZeroGraph

lemma scalar_partial_invertible {L : ℝ × ℝ →L[ℝ] ℝ}
    (h : L (0,1) ≠ 0) : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  let T := L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hT (x : ℝ) : T x = L (0,1) * x := by
    change L (0,x) = _
    have hx : (0,x) = x • ((0,1) : ℝ × ℝ) := by simp
    rw [hx, map_smul]
    simp [mul_comm]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L (0,1))⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · apply ContinuousLinearMap.ext_ring
    change T ((L (0,1))⁻¹ * 1) = 1
    rw [hT]
    simp [h]
  · apply ContinuousLinearMap.ext_ring
    change (L (0,1))⁻¹ * T 1 = 1
    rw [hT]
    simp [h]

/-- A scalar specialization of the C¹ implicit function theorem, keeping
both the actual open domain and a fixed product neighborhood. -/
lemma local_zero_graph (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (h0 : (0,0) ∈ U) (hf : ContDiffOn ℝ 1 f U)
    (hzero : f (0,0) = 0) (hd : stateDerivative f (0,0) ≠ 0) :
    ∃ ψ : ℝ → ℝ, ∃ a b : ℝ, IsLocalZeroGraph f U ψ a b := by
  have hc : ContDiffAt ℝ 1 f (0,0) := (hf _ h0).contDiffAt (hU.mem_nhds h0)
  have hi := scalar_partial_invertible hd
  let ψ := hc.implicitFunction (by norm_num) hi
  have hψ0 : ψ 0 = 0 := hc.implicitFunction_apply_self (by norm_num) hi
  have hψc : ContDiffAt ℝ 1 ψ 0 := hc.contDiffAt_implicitFunction (by norm_num) hi
  have heq : ∀ᶠ z in 𝓝 ((0,0) : ℝ × ℝ), f z = 0 ↔ ψ z.1 = z.2 := by
    simpa only [hzero] using hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi
  obtain ⟨W, hW, hψW⟩ := hψc.contDiffOn le_rfl (by norm_num)
  have hrect : ∃ A ∈ 𝓝 (0 : ℝ), ∃ B ∈ 𝓝 (0 : ℝ),
      A ×ˢ B ⊆ {z | z ∈ U ∧ (f z = 0 ↔ ψ z.1 = z.2)} := by
    apply mem_nhds_prod_iff.mp
    exact inter_mem (hU.mem_nhds h0) heq
  obtain ⟨A, hA, B, hB, hAB⟩ := hrect
  obtain ⟨b, hb, hbB⟩ := Metric.mem_nhds_iff.mp hB
  have hψB : ∀ᶠ μ in 𝓝 (0 : ℝ), ψ μ ∈ Metric.ball 0 b := by
    apply hψc.continuousAt.preimage_mem_nhds
    simpa [hψ0] using Metric.ball_mem_nhds (0 : ℝ) hb
  obtain ⟨a, ha, haA⟩ := Metric.mem_nhds_iff.mp (inter_mem hA (inter_mem hW hψB))
  refine ⟨ψ,a,b,ha,hb,hψ0,?_,hψW.mono (fun μ hμ => (haA hμ).2.1),?_⟩
  · intro z hz
    exact (hAB ⟨(haA hz.1).1, hbB hz.2⟩).1
  · intro μ hμ
    refine ⟨(haA hμ).2.2, fun x hx => ?_⟩
    exact (hAB ⟨(haA hμ).1, hbB hx⟩).2.trans eq_comm

lemma stateDerivative_continuousAt {f : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f z) : ContinuousAt (stateDerivative f) z := by
  exact (hf.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const

/-- Shrinking only the parameter interval preserves the zero graph. -/
lemma IsLocalZeroGraph.shrink {f U ψ a b c} (h : IsLocalZeroGraph f U ψ a b)
    (hc : 0 < c) (hca : c ≤ a) : IsLocalZeroGraph f U ψ c b := by
  rcases h with ⟨ha,hb,h0,hU,hC,hgraph⟩
  have hsub : Metric.ball (0 : ℝ) c ⊆ Metric.ball 0 a := Metric.ball_subset_ball hca
  exact ⟨hc,hb,h0,fun z hz => hU ⟨hsub hz.1,hz.2⟩,hC.mono hsub,
    fun μ hμ => hgraph μ (hsub hμ)⟩

lemma IsLocalZeroGraph.restrict_eventually {f U ψ a b} (h : IsLocalZeroGraph f U ψ a b)
    {P : ℝ → Prop} (hP : ∀ᶠ μ in 𝓝 (0 : ℝ), P μ) :
    ∃ c : ℝ, IsLocalZeroGraph f U ψ c b ∧ ∀ μ ∈ Metric.ball 0 c, P μ := by
  obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff.mp hP
  refine ⟨min a r, h.shrink (lt_min h.1 hr) (min_le_left _ _), ?_⟩
  intro μ hμ
  apply hrP
  exact (Metric.mem_ball.mp hμ).trans_le (min_le_right _ _)

lemma IsLocalZeroGraph.continuousAt {f U ψ a b} (h : IsLocalZeroGraph f U ψ a b) :
    ContinuousAt ψ 0 :=
  (h.2.2.2.2.1 0 (Metric.mem_ball_self h.1)).continuousWithinAt.continuousAt
    (Metric.ball_mem_nhds _ h.1)

lemma stateDerivative_along_graph {f U ψ a b} (h : IsLocalZeroGraph f U ψ a b)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffAt ℝ 1 F (0,0)) :
    ContinuousAt (fun μ => stateDerivative F (μ,ψ μ)) 0 := by
  have hc := stateDerivative_continuousAt hF
  have hp : ContinuousAt (fun μ => (μ,ψ μ)) 0 := continuousAt_id.prodMk h.continuousAt
  exact hc.comp_of_eq hp (by simp only [h.2.2.1])

theorem flow_persistence : Specs.D13Unified.Ch16.SimplePersistence.flowPersistence := by
  intro f U hU h0 hf heq hd
  obtain ⟨ψ,a,b,hgraph⟩ := local_zero_graph f U hU h0 hf heq hd
  have hc := stateDerivative_along_graph hgraph ((hf _ h0).contDiffAt (hU.mem_nhds h0))
  have he : ∀ᶠ μ in 𝓝 (0 : ℝ), 0 < stateDerivative f (μ,ψ μ) * stateDerivative f (0,0) := by
    have hprod := hc.mul_const (stateDerivative f (0,0))
    apply hprod.eventually (lt_mem_nhds _)
    simpa only [hgraph.2.2.1] using mul_self_pos.mpr hd
  obtain ⟨c,hcgraph,hcP⟩ := hgraph.restrict_eventually he
  exact ⟨ψ,c,b,hcgraph,hcP⟩

theorem state_derivative_slice : Specs.D13Unified.Ch16.SimplePersistence.stateDerivativeSlice := by
  intro f z hf
  have hh := hf.hasFDerivAt.comp z.2
    ((hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) z.2))
  simpa [stateDerivative, Specs.D13Unified.Ch16.SimplePersistence.stateDerivative,
    Function.comp_def] using hh.hasDerivAt

lemma stateDerivative_sub_snd {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F z) :
    stateDerivative (fun q => F q - q.2) z = stateDerivative F z - 1 := by
  unfold stateDerivative
  change (fderiv ℝ (F - Prod.snd) z) (0,1) = _
  rw [(hF.hasFDerivAt.sub hasFDerivAt_snd).fderiv]
  simp [Specs.D13Unified.Ch16.SimplePersistence.stateDerivative]

theorem map_persistence : Specs.D13Unified.Ch16.SimplePersistence.mapPersistence := by
  intro F U hU h0 hF heq hd
  have hc : ContDiffAt ℝ 1 F (0,0) := (hF _ h0).contDiffAt (hU.mem_nhds h0)
  let g : ℝ × ℝ → ℝ := fun z => F z - z.2
  have hgc : ContDiffOn ℝ 1 g U := hF.sub contDiff_snd.contDiffOn
  have hgd : stateDerivative g (0,0) ≠ 0 := by
    rw [stateDerivative_sub_snd hc.differentiableAt_one]
    exact sub_ne_zero.mpr hd
  obtain ⟨ψ,a,b,hgraph⟩ := local_zero_graph g U hU h0 hgc (by simpa [g] using heq) hgd
  have hDc := stateDerivative_along_graph hgraph hc
  have hDc0 : stateDerivative F (0,ψ 0) = stateDerivative F (0,0) := by rw [hgraph.2.2.1]
  have hne : ∀ᶠ μ in 𝓝 (0 : ℝ), stateDerivative F (μ,ψ μ) ≠ 1 := by
    exact hDc.eventually_ne (by simpa only [hDc0] using hd)
  have hlt : ∀ᶠ μ in 𝓝 (0 : ℝ),
      |stateDerivative F (0,0)| < 1 → |stateDerivative F (μ,ψ μ)| < 1 := by
    by_cases h : |stateDerivative F (0,0)| < 1
    · have hh := hDc.abs.eventually (gt_mem_nhds (by simpa only [hDc0] using h))
      exact hh.mono fun μ hμ _ => hμ
    · exact Filter.Eventually.of_forall fun μ hh => (h hh).elim
  have hgt : ∀ᶠ μ in 𝓝 (0 : ℝ),
      1 < |stateDerivative F (0,0)| → 1 < |stateDerivative F (μ,ψ μ)| := by
    by_cases h : 1 < |stateDerivative F (0,0)|
    · have hh := hDc.abs.eventually (lt_mem_nhds (by simpa only [hDc0] using h))
      exact hh.mono fun μ hμ _ => hμ
    · exact Filter.Eventually.of_forall fun μ hh => (h hh).elim
  obtain ⟨c,hcg,hcP⟩ := hgraph.restrict_eventually (hne.and (hlt.and hgt))
  exact ⟨ψ,c,b,hcg,hcP⟩

lemma scalar_remainder_bound {g : ℝ → ℝ} {p l : ℝ} (hg : HasDerivAt g l p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, |x-p| < r →
      |g x - g p - l * (x-p)| ≤ ε * |x-p| := by
  obtain ⟨r,hr,hrem⟩ := Metric.eventually_nhds_iff.mp (hg.isLittleO.def hε)
  refine ⟨r,hr,fun x hx => ?_⟩
  simpa [Real.norm_eq_abs, smul_eq_mul, mul_comm] using
    hrem (by simpa [Real.dist_eq] using hx)

theorem flow_directions : Specs.D13Unified.Ch16.SimplePersistence.flowDirections := by
  intro g p l heq hg hl
  obtain ⟨r,hr,hrem⟩ := scalar_remainder_bound hg (half_pos (abs_pos.mpr hl))
  refine ⟨r,hr,fun x hx hxp => ?_⟩
  have he := hrem x hx
  rw [heq, sub_zero] at he
  have heprod := mul_le_mul_of_nonneg_right he (abs_nonneg (x-p))
  rw [← abs_mul] at heprod
  have hs : 0 < (x-p)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxp)
  have hsq : |x-p| * |x-p| = (x-p)^2 := by rw [← abs_mul, ← pow_two, abs_of_nonneg (sq_nonneg _)]
  have hbound : |g x * (x-p) - l * (x-p)^2| ≤ |l| / 2 * (x-p)^2 := by
    calc
      _ = |(g x - l * (x-p)) * (x-p)| := by congr 1; ring
      _ ≤ |l| / 2 * |x-p| * |x-p| := heprod
      _ = _ := by rw [mul_assoc, hsq]
  obtain ⟨hlo,hhi⟩ := abs_le.mp hbound
  constructor
  · intro hneg
    rw [abs_of_neg hneg] at hhi
    nlinarith [mul_neg_of_neg_of_pos hneg hs]
  · intro hpos
    rw [abs_of_pos hpos] at hlo
    nlinarith [mul_pos hpos hs]

lemma scalar_radial_bounds {G : ℝ → ℝ} {p l : ℝ} (hfix : G p = p)
    (hg : HasDerivAt G l p) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, |x-p| < r →
      |G x-p| ≤ (|l|+ε) * |x-p| ∧ (|l|-ε) * |x-p| ≤ |G x-p| := by
  obtain ⟨r,hr,hrem⟩ := scalar_remainder_bound hg hε
  refine ⟨r,hr,fun x hx => ?_⟩
  have h := hrem x hx
  rw [hfix] at h
  have hup : |G x-p| ≤ |G x-p-l*(x-p)| + |l*(x-p)| := by
    simpa using abs_add_le (G x-p-l*(x-p)) (l*(x-p))
  have hlow : |l*(x-p)| ≤ |G x-p-l*(x-p)| + |G x-p| := by
    have hh := abs_add_le (G x-p) (-(G x-p-l*(x-p)))
    have heq : G x-p + -(G x-p-l*(x-p)) = l*(x-p) := by ring
    rw [heq, abs_neg] at hh
    linarith
  rw [abs_mul] at hup hlow
  constructor <;> nlinarith

theorem map_stability : Specs.D13Unified.Ch16.SimplePersistence.mapStability := by
  intro G V p l hV hp hfix hg
  constructor
  · intro hl
    let q := (1+|l|)/2
    have hq : 0 < q := by dsimp [q]; positivity
    have hq1 : q < 1 := by dsimp [q]; linarith
    have hε : 0 < q - |l| := by dsimp [q]; linarith
    obtain ⟨r,hr,hstep⟩ := scalar_radial_bounds hfix hg hε
    let N : Seminorm ℝ ℝ := normSeminorm ℝ ℝ
    have hN : D13Unified.Ch15.AdaptedNorm.Equivalent N := by
      refine ⟨1,by norm_num,1,by norm_num,fun x => ?_⟩
      simp [N]
    obtain ⟨C,hC,δ,hδ,hbound⟩ :=
      Ch15.LinearizedStability.iterate_bound_of_local_contraction G p V
        (hV.mem_nhds hp) N hN hq hq1 hr (by
          intro x hx
          simpa [N, Real.norm_eq_abs] using (hstep x (by simpa [Real.norm_eq_abs] using hx)).1)
    have hexp : Specs.D13Unified.Ch15.DiscreteDefinitions.LocallyExponentiallyStable G p :=
      ⟨C,hC,q,hq,hq1,δ,hδ,fun x hx n => (hbound x hx n).2⟩
    exact ⟨⟨δ,hδ,fun x hx n => (hbound x (by simpa [Real.norm_eq_abs] using hx) n).1⟩,
      hexp,(Ch15.LinearizedStability.stability_of_exponential_estimate hexp).2⟩
  · intro hl
    let q := (1+|l|)/2
    have hq : 1 < q := by dsimp [q]; linarith
    have hε : 0 < |l|-q := by dsimp [q]; linarith
    obtain ⟨r,hr,hstep⟩ := scalar_radial_bounds hfix hg hε
    obtain ⟨s,hs,hsV⟩ := Metric.isOpen_iff.mp hV p hp
    refine ⟨q,min r s,hq,lt_min hr hs,?_,?_⟩
    · exact (Metric.ball_subset_ball (min_le_right _ _)).trans hsV
    · intro x hx
      have hh := (hstep x (hx.trans_le (min_le_left _ _))).2
      linarith

/-- The scalar positive quadratic form supplies both flow tests without any
matrix or choice-of-basis conversion. -/
theorem scalar_flow_stability : Specs.D13Unified.Ch16.SimplePersistence.scalarFlowStability := by
  intro F hF h0 heq
  let A := fderiv ℝ F.eval 0
  let l := deriv F.eval 0
  have hA (x : ℝ) : A x = l * x := by
    change A x = A 1 * x
    calc
      A x = A (x • (1 : ℝ)) := by simp only [smul_eq_mul,mul_one]
      _ = x * A 1 := by rw [map_smul]; rfl
      _ = _ := mul_comm _ _
  let B := ContinuousLinearMap.mul ℝ ℝ
  have hB (x y : ℝ) : B x y = x*y := rfl
  constructor
  · intro hl
    change l < 0 at hl
    apply Ch12.LinearizedStability.stability_of_bilinear_decay F hF h0 heq B
      (fun x hx => by simpa only [hB] using mul_self_pos.mpr hx) (-2*l) (by linarith)
    intro x
    change B x (A x) + B (A x) x ≤ _
    rw [hB,hB,hA,Real.norm_eq_abs,sq_abs]
    nlinarith
  · intro hl
    change 0 < l at hl
    apply Ch12.LinearizedInstability.certificate_implies_escape F hF h0 heq
    apply Ch12.LinearizedInstability.bilinear_growth_certificate A B (2*l) (by linarith)
    · intro x _
      rw [hB,hB,hA,Real.norm_eq_abs,sq_abs]
      nlinarith
    · exact ⟨1,by norm_num [hB]⟩

/-- Realize a fixed parameter as an ODE on precisely its shifted open domain. -/
lemma realize_flow_slice (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (μ p : ℝ) (hp : (μ,p) ∈ U)
    (heq : f (μ,p) = 0) :
    ∃ F : AutonomousODE ℝ, F.domain = {y | (μ,p+y) ∈ U} ∧
      (∀ y ∈ F.domain, F.eval y = f (μ,p+y)) ∧
      ∃ (_hF : ContDiffOn ℝ 1 F.eval F.domain) (_h0 : (0 : ℝ) ∈ F.domain)
        (_hzero : F.eval 0 = 0), deriv F.eval 0 = stateDerivative f (μ,p) := by
  let V : Set ℝ := {y | (μ,p+y) ∈ U}
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have hg : ContDiffOn ℝ 1 (fun y => f (μ,p+y)) V :=
    hf.comp (by fun_prop) (fun y hy => hy)
  let F : AutonomousODE ℝ := {
    domain := V
    isOpen_domain := hV
    field := fun y => f (μ,p+y.val)
    continuous_field := hg.continuousOn.domRestrict }
  have hEval (y : ℝ) (hy : y ∈ V) : F.eval y = f (μ,p+y) := by
    simp [AutonomousODE.eval, Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue,F,hy]
  have hFc : ContDiffOn ℝ 1 F.eval F.domain := hg.congr (fun y hy => hEval y hy)
  have h0 : (0 : ℝ) ∈ V := by simpa [V] using hp
  have hzero : F.eval 0 = 0 := by rw [hEval 0 h0]; simpa using heq
  refine ⟨F,rfl,hEval,hFc,h0,hzero,?_⟩
  have hevent : F.eval =ᶠ[𝓝 (0 : ℝ)] (fun y => f (μ,p+y)) :=
    Filter.mem_of_superset (hV.mem_nhds h0) hEval
  have hc := (hf _ hp).contDiffAt (hU.mem_nhds hp)
  have hd' : HasDerivAt (fun x => f (μ,x)) (stateDerivative f (μ,p)) (p + 0) := by
    simpa only [add_zero] using state_derivative_slice f (μ,p) hc.differentiableAt_one
  have hd := hd'.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add p)
  have hh : HasDerivAt F.eval (stateDerivative f (μ,p)) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq (f := fun y => f (μ,p+y)) _ hevent
    simpa only [add_zero,mul_one,Function.comp_def] using hd
  exact hh.deriv

theorem flow_branch_stability : Specs.D13Unified.Ch16.SimplePersistence.flowBranchStability := by
  intro f U hU h0 hf heq hd
  obtain ⟨ψ,a,b,hgraph,hsign⟩ := flow_persistence f U hU h0 hf heq hd
  refine ⟨ψ,a,b,hgraph,fun μ hμ => ?_⟩
  have hp : (μ,ψ μ) ∈ U := hgraph.2.2.2.1 ⟨hμ,(hgraph.2.2.2.2.2 μ hμ).1⟩
  have hzero : f (μ,ψ μ) = 0 :=
    ((hgraph.2.2.2.2.2 μ hμ).2 _ (hgraph.2.2.2.2.2 μ hμ).1).mpr rfl
  obtain ⟨F,hdom,hEval,hF,hF0,hFeq,hderiv⟩ := realize_flow_slice f U hU hf μ (ψ μ) hp hzero
  refine ⟨F,hdom,hEval,hF,hF0,hFeq,?_,?_⟩
  · intro hneg
    apply (scalar_flow_stability F hF hF0 hFeq).1
    change deriv F.eval 0 < 0
    rw [hderiv]
    exact (mul_pos_iff.mp (hsign μ hμ)).resolve_left (fun h => not_lt_of_ge hneg.le h.2) |>.1
  · intro hpos
    apply (scalar_flow_stability F hF hF0 hFeq).2
    change 0 < deriv F.eval 0
    rw [hderiv]
    exact (mul_pos_iff.mp (hsign μ hμ)).resolve_right (fun h => not_lt_of_ge hpos.le h.2) |>.1

/-- Uniform local radial expansion forces a first exit, regardless of how the
ambient representative is defined outside the actual domain. -/
lemma radial_expansion_unstable (G : ℝ → ℝ) (V : Set ℝ) (p q r : ℝ)
    (hq : 1 < q) (hr : 0 < r) (hball : Metric.ball p r ⊆ V)
    (hstep : ∀ x, |x-p| < r → q * |x-p| ≤ |G x-p|) :
    Ch15.LinearizedInstability.LocallyUnstable G V p := by
  classical
  refine ⟨r,hr,hball,fun δ hδ => ?_⟩
  let d := min δ r / 2
  have hd : 0 < d := half_pos (lt_min hδ hr)
  have hdδ : d < δ := by dsimp [d]; have := min_le_left δ r; linarith
  have hdr : d < r := by dsimp [d]; have := min_le_right δ r; linarith
  let x := p+d
  have hxp : |x-p| = d := by simp [x,abs_of_pos hd]
  have hmem : x ∈ V := hball (by simpa [Real.dist_eq,hxp] using hdr)
  have hexit : ∃ N : ℕ, r ≤ |G^[N] x-p| := by
    by_contra hn
    push Not at hn
    have hbound : ∀ n : ℕ, q^n * d ≤ |G^[n] x-p| := by
      intro n
      induction n with
      | zero => simp [hxp]
      | succ n ih =>
        calc
          _ = q * (q^n * d) := by rw [pow_succ]; ring
          _ ≤ q * |G^[n] x-p| := mul_le_mul_of_nonneg_left ih (by linarith)
          _ ≤ |G (G^[n] x)-p| := hstep _ (hn n)
          _ = _ := by rw [Function.iterate_succ_apply']
    have ht := (tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const hd
    obtain ⟨n,hn'⟩ := Filter.Eventually.exists (ht.eventually (eventually_gt_atTop r))
    have := hbound n
    have := hn n
    linarith
  let N := Nat.find hexit
  have hN : r ≤ |G^[N] x-p| := Nat.find_spec hexit
  have hNpos : 0 < N := by
    by_contra hn
    have : N = 0 := Nat.eq_zero_of_not_pos hn
    simp only [this,Function.iterate_zero, id_eq,hxp] at hN
    linarith
  refine ⟨x,hmem,by simpa [Real.norm_eq_abs,hxp] using hdδ,N,hNpos,?_,?_⟩
  · simpa only [Real.norm_eq_abs] using hN
  · intro n hn
    have hnsmall : |G^[n] x-p| < r := lt_of_not_ge (Nat.find_min hexit hn)
    exact ⟨by simpa only [Real.norm_eq_abs] using hnsmall,
      hball (by simpa [Real.dist_eq] using hnsmall)⟩

theorem map_branch_stability : Specs.D13Unified.Ch16.SimplePersistence.mapBranchStability := by
  intro F U hU h0 hF heq hd
  obtain ⟨ψ,a,b,hgraph,hmulti⟩ := map_persistence F U hU h0 hF heq hd
  refine ⟨ψ,a,b,hgraph,fun μ hμ => ?_⟩
  have hp : (μ,ψ μ) ∈ U := hgraph.2.2.2.1 ⟨hμ,(hgraph.2.2.2.2.2 μ hμ).1⟩
  have hfix : F (μ,ψ μ) = ψ μ := by
    have hz := ((hgraph.2.2.2.2.2 μ hμ).2 _ (hgraph.2.2.2.2.2 μ hμ).1).mpr rfl
    exact sub_eq_zero.mp hz
  have hc := (hF _ hp).contDiffAt (hU.mem_nhds hp)
  have hderiv := state_derivative_slice F (μ,ψ μ) hc.differentiableAt_one
  let V : Set ℝ := {x | (μ,x) ∈ U}
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have hpV : ψ μ ∈ V := hp
  have htests := map_stability (fun x => F (μ,x)) V (ψ μ)
    (stateDerivative F (μ,ψ μ)) hV hpV hfix hderiv
  constructor
  · intro hlt
    exact htests.1 ((hmulti μ hμ).2.1 hlt)
  · intro hgt
    obtain ⟨q,r,hq,hr,hball,hstep⟩ := htests.2 ((hmulti μ hμ).2.2 hgt)
    exact radial_expansion_unstable _ V (ψ μ) q r hq hr hball hstep

end D13Unified.Ch16.SimplePersistence
