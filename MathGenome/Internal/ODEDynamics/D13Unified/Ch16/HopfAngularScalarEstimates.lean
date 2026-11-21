import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfAngularScalarEstimates
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.CkDependence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.ScalarLinear
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace D13Unified.Ch16.HopfAngularScalarEstimates
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Ch06.C1Dependence

lemma normalizedODE_eval (d : AngularData) (h : Hypotheses d)
    {θ y r μ : ℝ} (hq : ((θ,r*y),μ) ∈ d.domain) :
    parameterEvalValue (normalizedODE d h) θ y (r,μ) =
      y * d.G ((θ,r*y),μ) := by
  simp [parameterEvalValue, normalizedODE, normalizedDomain, normalizedField, hq]

lemma normalizedField_c2 (d : AngularData) (h : Hypotheses d) :
    ContDiffOn ℝ 2 (normalizedField d) (normalizedDomain d) :=
  contDiffOn_fst.snd.mul (h.smooth_G.comp
    ((contDiffOn_fst.fst.prodMk (contDiffOn_snd.fst.mul contDiffOn_fst.snd)).prodMk
      contDiffOn_snd.snd) (fun _ hq => hq))

lemma normalizedODE_c2 (d : AngularData) (h : Hypotheses d) :
    ContDiffOn ℝ 2 (field (normalizedODE d h)) (normalizedODE d h).domain := by
  exact (normalizedField_c2 d h).congr
    (fun q hq => normalizedODE_eval d h hq)

/-- C² dependence holds on the actual domain; no common time interval is
inferred until the reference trajectory and compactness argument are used. -/
theorem amplitude_c2 (d : AngularData) (h : Hypotheses d) :
    IsOpen (amplitudeDomain d h) ∧
      ContDiffOn ℝ 2 (fun q : ℝ × (ℝ × ℝ) => amplitude d h q.1 q.2.1 q.2.2)
        (amplitudeDomain d h) := by
  have hc := Ch06.CkDependence.joint_ck 2 (by decide) (normalizedODE d h)
    (normalizedODE_c2 d h)
  refine ⟨hc.1.preimage (continuous_fst.prodMk
    ((continuous_const.prodMk continuous_const).prodMk continuous_snd)), ?_⟩
  exact hc.2.comp (contDiffOn_fst.prodMk
    ((contDiffOn_const.prodMk contDiffOn_const).prodMk contDiffOn_snd)) (fun _ hq => hq)

lemma amplitude_derivative (d : AngularData) (h : Hypotheses d)
    {θ r μ : ℝ} (hq : (θ,(r,μ)) ∈ amplitudeDomain d h) :
    ((θ,radialSolution d h θ r μ),μ) ∈ d.domain ∧
    HasDerivAt (fun s => amplitude d h s r μ)
      (amplitude d h θ r μ * d.G ((θ,radialSolution d h θ r μ),μ)) θ := by
  have hF1 := (normalizedODE_c2 d h).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hLip := (normalizedODE d h).locallyLipschitzInState_of_contDiffOn hF1
  have hg := (ParameterODE.solutionValue_on_domain (normalizedODE d h) hLip
    θ 0 1 (r,μ) hq).2
  have hd := Ch06.C1Dependence.terminal_derivative (normalizedODE d h) hF1
    θ 0 1 (r,μ) hq
  refine ⟨hg, ?_⟩
  change HasDerivAt (fun s => amplitude d h s r μ)
    (parameterEvalValue (normalizedODE d h) θ (amplitude d h θ r μ) (r,μ)) θ at hd
  change ((θ,r * amplitude d h θ r μ),μ) ∈ d.domain at hg
  rw [normalizedODE_eval d h (θ := θ) (y := amplitude d h θ r μ)
    (r := r) (μ := μ) hg] at hd
  exact hd

lemma radialSolution_derivative (d : AngularData) (h : Hypotheses d)
    {θ r μ : ℝ} (hq : (θ,(r,μ)) ∈ amplitudeDomain d h) :
    HasDerivAt (fun s => radialSolution d h s r μ)
      (angularField d θ (radialSolution d h θ r μ) μ) θ := by
  simpa only [radialSolution, angularField, mul_assoc] using
    ((amplitude_derivative d h hq).2.const_mul r)

lemma amplitude_initial (d : AngularData) (h : Hypotheses d)
    {r μ : ℝ} (hq : ((0,r),μ) ∈ d.domain) : amplitude d h 0 r μ = 1 := by
  have hF1 := (normalizedODE_c2 d h).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hLip := (normalizedODE d h).locallyLipschitzInState_of_contDiffOn hF1
  have hq' : ((0,1),(r,μ)) ∈ (normalizedODE d h).domain := by
    simpa only [normalizedODE, normalizedDomain, mem_ofPred_eq, mul_one] using hq
  exact (ParameterODE.solutionValue_ivp (normalizedODE d h) hLip 0 1 (r,μ) hq').2.2

lemma radialSolution_initial (d : AngularData) (h : Hypotheses d)
    {r μ : ℝ} (hq : ((0,r),μ) ∈ d.domain) : radialSolution d h 0 r μ = r := by
  simp only [radialSolution, amplitude_initial d h hq, mul_one]

/-- Algebraic expansion with the actual error, independent of its estimates. -/
lemma endpoint_expansion_identity (d : AngularData) (h : Hypotheses d) (r μ : ℝ) :
    endpoint d h r μ = Real.exp (d.T * d.A μ) * r +
      cubicCoefficient d μ * r ^ 3 + endpointError d h r μ := by
  dsimp [endpointError]
  ring

/-- Division at zero is not used in the identity. -/
lemma endpoint_factorization (d : AngularData) (h : Hypotheses d) (r μ : ℝ) :
    endpoint d h r μ = r * (1 + dividedDisplacement d h r μ) := by
  simp [endpoint, radialSolution, dividedDisplacement]

lemma cubicCoefficient_at_zero (d : AngularData) {μ : ℝ} (hA : d.A μ = 0) :
    cubicCoefficient d μ = d.T * d.B μ := by
  simp [cubicCoefficient, hA, mul_comm]

/-- Compact-interval scalar integrating factors give strict positivity without
assuming a positive initial radius stays away from zero a priori. -/
lemma positive_of_scalar_equation (T : ℝ) (hT : 0 ≤ T) (a y : ℝ → ℝ)
    (ha : ContinuousOn a (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hy0 : y 0 = 1)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (a t * y t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, 0 < y t := by
  let I : TimeInterval := ⟨Icc 0 T, ⟨0,⟨le_rfl,hT⟩⟩, ordConnected_Icc⟩
  have he := ScalarLinear.eq_variation_of_isIVP I a (fun _ => 0) 0 1
    ha continuousOn_const (x := y)
    ⟨hy, ⟨le_rfl,hT⟩, hy0, fun t ht => by simpa using hd t ht⟩
  intro t ht
  rw [he ht]
  simpa [ScalarLinear.variation, ← Real.exp_eq_exp_ℝ] using
    Real.exp_pos (ScalarLinear.primitive a 0 t)

/-- An open neighborhood of a whole compact time interval contains a slightly
larger open interval. No regularity outside that neighborhood is assumed. -/
lemma enclosing_interval {S : Set ℝ} (hS : IsOpen S) {T : ℝ} (hT : 0 ≤ T)
    (hI : Icc 0 T ⊆ S) :
    ∃ a b : ℝ, a < 0 ∧ T < b ∧ Ioo a b ⊆ S := by
  have hn₀ : ∀ᶠ θ in 𝓝 (0 : ℝ), θ ∈ S := hS.mem_nhds (hI ⟨le_rfl,hT⟩)
  obtain ⟨a₀,b₀,h₀,hsub₀⟩ := hn₀.exists_Ioo_subset
  have hnT : ∀ᶠ θ in 𝓝 T, θ ∈ S := hS.mem_nhds (hI ⟨hT,le_rfl⟩)
  obtain ⟨aT,bT,hT',hsubT⟩ := hnT.exists_Ioo_subset
  refine ⟨a₀,bT,h₀.1,hT'.2,?_⟩
  intro θ hθ
  by_cases hθ₀ : θ < 0
  · exact hsub₀ ⟨hθ.1,hθ₀.trans h₀.2⟩
  by_cases hθT : θ ≤ T
  · exact hI ⟨le_of_not_gt hθ₀,hθT⟩
  · exact hsubT ⟨hT'.1.trans (lt_of_not_ge hθT),hθ.2⟩

/-- The entire zero-radius reference trajectory is inside the ACTUAL maximal
solution domain. This is proved using a scalar linear IVP on an open interval,
including a small extension past both endpoints. -/
theorem amplitude_zero (d : AngularData) (h : Hypotheses d)
    {μ : ℝ} (hμ : |μ| < d.ε) :
    ∀ θ ∈ Icc 0 d.T, (θ,(0,μ)) ∈ amplitudeDomain d h ∧
      amplitude d h θ 0 μ = Real.exp (d.A μ * θ) := by
  let S : Set ℝ := {θ | ((θ,0),μ) ∈ d.domain}
  have ho : IsOpen S := h.open_domain.preimage
    ((continuous_id.prodMk continuous_const).prodMk continuous_const)
  have hI : Icc 0 d.T ⊆ S := fun θ hθ =>
    h.contains_cylinder ⟨hθ,by simpa using h.radius_pos,hμ⟩
  obtain ⟨a,b,ha,hb,hsub⟩ := enclosing_interval ho h.T_pos.le hI
  let J : OpenTimeInterval := ⟨⟨Ioo a b,⟨0,⟨ha,h.T_pos.le.trans_lt hb⟩⟩,
    ordConnected_Ioo⟩,isOpen_Ioo⟩
  have h0 : 0 ∈ J.carrier := ⟨ha,h.T_pos.le.trans_lt hb⟩
  let c : ℝ → ℝ := fun θ => d.G ((θ,0),μ)
  have hc : ContinuousOn c J.carrier := h.smooth_G.continuousOn.comp
    ((continuousOn_id.prodMk continuousOn_const).prodMk continuousOn_const) hsub
  let y : ℝ → ℝ := ScalarLinear.variation c (fun _ => 0) 0 1
  have hy := (ScalarLinear.classical_variation_of_constants J c (fun _ => 0)
    0 1 hc continuousOn_const h0 y).mpr (fun _ _ => rfl)
  have hF1 := (normalizedODE_c2 d h).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hLip := (normalizedODE d h).locallyLipschitzInState_of_contDiffOn hF1
  have hinit : ((0,1),(0,μ)) ∈ (normalizedODE d h).domain := by
    change ((0,0*1),μ) ∈ d.domain
    simpa [S] using hI ⟨le_rfl,h.T_pos.le⟩
  have hyP : classicalParameterIVPOnValue (normalizedODE d h) (0,μ) J y 0 1 := by
    refine ⟨⟨hy.1,?_,?_⟩,h0,hy.2.1⟩
    · intro θ hθ
      change ((θ,0*y θ),μ) ∈ d.domain
      simpa [S] using hsub hθ
    · intro θ hθ
      have hm : ((θ,0*y θ),μ) ∈ d.domain := by simpa [S] using hsub hθ
      rw [normalizedODE_eval d h hm]
      convert hy.2.2 θ hθ using 1
      simp only [zero_mul,add_zero,c]
      ring
  obtain ⟨_,_,_,_,_,hres,_⟩ := ParameterODE.canonical_solution
    (normalizedODE d h) hLip 0 1 (0,μ) hinit
  have hr := hres J y
    ((classicalParameterIVPOn_iff (normalizedODE d h) (0,μ) J y 0 1).mp hyP)
  intro θ hθ
  have hθJ : θ ∈ J.carrier := ⟨ha.trans_le hθ.1,hθ.2.trans_lt hb⟩
  have hdom : (θ,(0,μ)) ∈ amplitudeDomain d h := ⟨hinit,hr.1 hθJ⟩
  refine ⟨hdom,?_⟩
  have he := (ParameterODE.solutionValue_on_domain (normalizedODE d h) hLip
    θ 0 1 (0,μ) hdom).1.trans (hr.2 hθJ)
  change amplitude d h θ 0 μ = y θ at he
  rw [he]
  have hi : ScalarLinear.primitive c 0 θ = θ * d.A μ := by
    unfold ScalarLinear.primitive
    calc
      (∫ s in 0..θ, c s) = ∫ _ in 0..θ, d.A μ :=
        intervalIntegral.integral_congr (fun s hs => h.value_at_zero s
          ⟨(uIcc_of_le hθ.1 ▸ hs).1, (uIcc_of_le hθ.1 ▸ hs).2.trans hθ.2⟩ μ hμ)
      _ = θ * d.A μ := by simp
  simp [y,ScalarLinear.variation,hi,← Real.exp_eq_exp_ℝ,mul_comm]

lemma amplitude_positive (d : AngularData) (h : Hypotheses d)
    {r μ : ℝ} (hdom : ∀ θ ∈ Icc 0 d.T, (θ,(r,μ)) ∈ amplitudeDomain d h) :
    ∀ θ ∈ Icc 0 d.T, 0 < amplitude d h θ r μ := by
  let Y : ℝ → ℝ := fun θ => amplitude d h θ r μ
  let c : ℝ → ℝ := fun θ => d.G ((θ,r * Y θ),μ)
  have hY : ContinuousOn Y (Icc 0 d.T) := by
    intro θ hθ
    have hy : ContinuousAt (fun q : ℝ × (ℝ × ℝ) =>
        amplitude d h q.1 q.2.1 q.2.2) (θ,(r,μ)) :=
      (amplitude_c2 d h).2.continuousOn.continuousAt
        ((amplitude_c2 d h).1.mem_nhds (hdom θ hθ))
    have ht : ContinuousAt (fun s : ℝ => amplitude d h s r μ) θ :=
      hy.comp (f := fun s : ℝ => (s,(r,μ)))
        (show ContinuousAt (fun s : ℝ => (s,(r,μ))) θ by fun_prop)
    exact ht.continuousWithinAt
  have hcmap : ContinuousOn (fun θ => ((θ,r * Y θ),μ)) (Icc 0 d.T) :=
    (continuousOn_id.prodMk ((continuousOn_const (c := r)).mul hY)).prodMk
      (continuousOn_const (c := μ))
  have hcmem : MapsTo (fun θ => ((θ,r * Y θ),μ)) (Icc 0 d.T) d.domain :=
    fun θ hθ => (amplitude_derivative d h (hdom θ hθ)).1
  have hc : ContinuousOn c (Icc 0 d.T) := h.smooth_G.continuousOn.comp hcmap hcmem
  have hinit := (hdom 0 ⟨le_rfl,h.T_pos.le⟩).1
  have hinit' : ((0,r),μ) ∈ d.domain := by
    simpa only [normalizedODE, normalizedDomain, mem_ofPred_eq, mul_one] using hinit
  have hY0 : Y 0 = 1 := amplitude_initial d h hinit'
  have hd : ∀ θ ∈ Icc 0 d.T, HasDerivWithinAt Y (c θ * Y θ) (Icc 0 d.T) θ := by
    intro θ hθ
    have hd := (amplitude_derivative d h (hdom θ hθ)).2.hasDerivWithinAt (s := Icc 0 d.T)
    change HasDerivWithinAt Y (Y θ * c θ) (Icc 0 d.T) θ at hd
    rw [mul_comm (Y θ) (c θ)] at hd
    exact hd
  exact positive_of_scalar_equation d.T h.T_pos.le c Y hc hY hY0 hd

/-- Common full-turn existence and a uniform linear radius bound, obtained
from the normalized IVP and compactness rather than from a global flow. -/
theorem common_amplitude_domain (d : AngularData) (h : Hypotheses d) :
    ∃ δ η L a b : ℝ, 0 < δ ∧ δ < d.ρ ∧ 0 < η ∧ η < d.ε ∧
      0 < L ∧ a < 0 ∧ d.T < b ∧ L * δ < d.ρ ∧
      (Ioo a b ×ˢ parameterBox δ η) ⊆ amplitudeDomain d h ∧
      (∀ r μ, (r,μ) ∈ parameterBox δ η → ∀ θ ∈ Icc 0 d.T,
        |radialSolution d h θ r μ| ≤ L * |r| ∧
        |radialSolution d h θ r μ| < d.ρ ∧
        (0 < r → 0 < radialSolution d h θ r μ)) := by
  have hzero := amplitude_zero d h (μ := 0) (by simpa using h.parameter_pos)
  obtain ⟨U,V,hU,hV,hIU,h0V,hUV⟩ := generalized_tube_lemma
    isCompact_Icc (isCompact_singleton (x := ((0,0) : ℝ × ℝ)))
    (amplitude_c2 d h).1 (by
      rintro ⟨θ,p⟩ ⟨hθ,hp⟩
      rcases Set.mem_singleton_iff.mp hp with rfl
      exact (hzero θ hθ).1)
  obtain ⟨a,b,ha,hb,hJ⟩ := enclosing_interval hU h.T_pos.le hIU
  obtain ⟨c,hc,hcV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (show ((0,0) : ℝ × ℝ) ∈ {(0,0)} from rfl)))
  let R := c / 2
  have hR : 0 < R := half_pos hc
  have hRV : Metric.closedBall (0 : ℝ × ℝ) R ⊆ V :=
    (Metric.closedBall_subset_ball (half_lt_self hc)).trans hcV
  let K := Icc 0 d.T ×ˢ Metric.closedBall (0 : ℝ × ℝ) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKD : K ⊆ amplitudeDomain d h := fun q hq => hUV ⟨hIU hq.1,hRV hq.2⟩
  obtain ⟨L₀,hL₀⟩ := hK.exists_bound_of_continuousOn
    ((amplitude_c2 d h).2.continuousOn.mono hKD)
  let L := max L₀ 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let δ := min (min R (d.ρ / 2)) (d.ρ / (2 * L))
  let η := min R (d.ε / 2)
  have hδ : 0 < δ := lt_min (lt_min hR (half_pos h.radius_pos))
    (div_pos h.radius_pos (mul_pos (by norm_num) hL))
  have hη : 0 < η := lt_min hR (half_pos h.parameter_pos)
  have hδR : δ ≤ R := (min_le_left _ _).trans (min_le_left _ _)
  have hηR : η ≤ R := min_le_left _ _
  have hδρ : δ < d.ρ :=
    ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self h.radius_pos)
  have hηε : η < d.ε := (min_le_right _ _).trans_lt (half_lt_self h.parameter_pos)
  have hLδ : L * δ < d.ρ := by
    have hn := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hL)).mp
      (show δ ≤ d.ρ / (2*L) from min_le_right _ _)
    nlinarith [h.radius_pos]
  have hbox : parameterBox δ η ⊆ Metric.closedBall (0 : ℝ × ℝ) R := by
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    exact ⟨(le_of_lt (abs_lt.mpr hp.1)).trans hδR,
      (le_of_lt (abs_lt.mpr hp.2)).trans hηR⟩
  have hdom : (Ioo a b ×ˢ parameterBox δ η) ⊆ amplitudeDomain d h :=
    fun q hq => hUV ⟨hJ hq.1,hRV (hbox hq.2)⟩
  refine ⟨δ,η,L,a,b,hδ,hδρ,hη,hηε,hL,ha,hb,hLδ,hdom,?_⟩
  intro r μ hp θ hθ
  have hYbound : |amplitude d h θ r μ| ≤ L :=
    (hL₀ (θ,(r,μ)) ⟨hθ,hbox hp⟩).trans (le_max_left _ _)
  have hbnd : |radialSolution d h θ r μ| ≤ L * |r| := by
    dsimp [radialSolution]
    rw [abs_mul, mul_comm L]
    exact mul_le_mul_of_nonneg_left hYbound (abs_nonneg r)
  refine ⟨hbnd,?_,?_⟩
  · exact hbnd.trans_lt ((mul_lt_mul_of_pos_left (abs_lt.mpr hp.1) hL).trans hLδ)
  · intro hr
    exact mul_pos hr (amplitude_positive d h
      (fun s hs => hdom ⟨⟨ha.trans_le hs.1,hs.2.trans_lt hb⟩,hp⟩) θ hθ)

/-- Full common-domain evolution and smooth divided displacement, including
r₀=0. Quantitative cubic error estimates are proved separately below. -/
theorem normalizedEvolution :
    Specs.D13Unified.Ch16.HopfAngularScalarEstimates.NormalizedEvolution := by
  intro d h
  obtain ⟨δ,η,L,a,b,hδ,hδρ,hη,hηε,hL,ha,hb,hLδ,hdom,hbound⟩ :=
    common_amplitude_domain d h
  have hT : d.T ∈ Ioo a b := ⟨ha.trans h.T_pos,hb⟩
  refine ⟨δ,η,L,a,b,hδ,hδρ,hη,hηε,hL,ha,hb,hLδ,hdom,
    (amplitude_c2 d h).2.mono hdom,?_,?_,?_,endpoint_factorization d h⟩
  · intro r μ hp
    have hr : |r| < d.ρ := (abs_lt.mpr hp.1).trans hδρ
    have hμ : |μ| < d.ε := (abs_lt.mpr hp.2).trans hηε
    have hinit : ((0,r),μ) ∈ d.domain := h.contains_cylinder
      ⟨⟨le_rfl,h.T_pos.le⟩,hr,hμ⟩
    refine ⟨amplitude_initial d h hinit,?_,radialSolution_initial d h hinit,
      hbound r μ hp⟩
    intro θ hθ
    have hq : (θ,(r,μ)) ∈ amplitudeDomain d h := hdom ⟨hθ,hp⟩
    exact ⟨(amplitude_derivative d h hq).1,(amplitude_derivative d h hq).2,
      radialSolution_derivative d h hq⟩
  · intro μ hμ θ hθ
    exact (amplitude_zero d h (hμ.trans hηε) θ hθ).2
  · have hc : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => amplitude d h d.T p.1 p.2)
        (parameterBox δ η) :=
      (amplitude_c2 d h).2.comp (f := fun p : ℝ × ℝ => (d.T,p))
        (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => hdom ⟨hT,hp⟩)
    exact hc.sub contDiffOn_const

lemma amplitude_c2_on (d : AngularData) (h : Hypotheses d) {J : Set ℝ}
    {r μ : ℝ} (hdom : ∀ θ ∈ J, (θ,(r,μ)) ∈ amplitudeDomain d h) :
    ContDiffOn ℝ 2 (fun θ => amplitude d h θ r μ) J :=
  (amplitude_c2 d h).2.comp (f := fun θ : ℝ => (θ,(r,μ)))
    (contDiffOn_id.prodMk (contDiffOn_const (c := (r,μ)))) hdom

lemma radialSolution_c2_on (d : AngularData) (h : Hypotheses d) {J : Set ℝ}
    {r μ : ℝ} (hdom : ∀ θ ∈ J, (θ,(r,μ)) ∈ amplitudeDomain d h) :
    ContDiffOn ℝ 2 (fun θ => radialSolution d h θ r μ) J :=
  (contDiffOn_const (c := r)).mul (amplitude_c2_on d h hdom)

/-- Exact variation of constants for the nonlinear scalar solution. It does
not postulate any asymptotic estimate and retains the actual compact domain. -/
lemma radialSolution_integral (d : AngularData) (h : Hypotheses d)
    {r μ : ℝ} (hdom : ∀ θ ∈ Icc 0 d.T, (θ,(r,μ)) ∈ amplitudeDomain d h) :
    ∀ θ ∈ Icc 0 d.T,
      radialSolution d h θ r μ = Real.exp (d.A μ * θ) *
        (r + ∫ s in 0..θ, Real.exp (-d.A μ * s) *
          (d.B μ * radialSolution d h s r μ ^ 3 +
            remainder d s (radialSolution d h s r μ) μ)) := by
  let u : ℝ → ℝ := fun θ => radialSolution d h θ r μ
  let c : ℝ → ℝ := fun θ => d.B μ * u θ ^ 3 + remainder d θ (u θ) μ
  have hu : ContinuousOn u (Icc 0 d.T) := (radialSolution_c2_on d h hdom).continuousOn
  have hg : ContinuousOn (fun θ => d.G ((θ,u θ),μ)) (Icc 0 d.T) :=
    h.smooth_G.continuousOn.comp
      ((continuousOn_id.prodMk hu).prodMk (continuousOn_const (c := μ)))
      (fun θ hθ => (amplitude_derivative d h (hdom θ hθ)).1)
  have hc : ContinuousOn c (Icc 0 d.T) := by
    have hf := (hu.mul hg).sub ((continuousOn_const (c := d.A μ)).mul hu)
    apply hf.congr
    intro θ _
    dsimp [c,remainder,angularField]
    ring
  let I : TimeInterval := ⟨Icc 0 d.T,⟨0,⟨le_rfl,h.T_pos.le⟩⟩,ordConnected_Icc⟩
  have hinit : ((0,r),μ) ∈ d.domain := by
    simpa only [normalizedODE,normalizedDomain,mem_ofPred_eq,mul_one] using
      (hdom 0 ⟨le_rfl,h.T_pos.le⟩).1
  have hde : ∀ θ ∈ I.carrier,
      HasDerivWithinAt u (d.A μ * u θ + c θ) I.carrier θ := by
    intro θ hθ
    have heq : d.A μ * u θ + c θ = angularField d θ (u θ) μ := by
      dsimp [c,remainder]
      ring
    rw [heq]
    exact (radialSolution_derivative d h (hdom θ hθ)).hasDerivWithinAt
  have he := ScalarLinear.eq_variation_of_isIVP I (fun _ => d.A μ) c 0 r
    continuousOn_const hc
    ⟨hu,⟨le_rfl,h.T_pos.le⟩,radialSolution_initial d h hinit,hde⟩
  intro θ hθ
  simpa [ScalarLinear.variation,ScalarLinear.primitive,← Real.exp_eq_exp_ℝ,
    mul_comm,neg_mul,u,c] using he hθ

/-- An everywhere-defined auxiliary equation constructs the exponential
integral smoothly in its exponent, including exponent zero. -/
private def exponentialIntegralODE : ParameterODE ℝ ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun q => Real.exp (q.val.2 * q.val.1.1)
  continuous_field := by fun_prop

private lemma exponentialIntegralODE_eval (t y p : ℝ) :
    parameterEvalValue exponentialIntegralODE t y p = Real.exp (p*t) := by
  simp [parameterEvalValue, exponentialIntegralODE]

private lemma exponentialIntegralODE_c2 :
    ContDiffOn ℝ 2 (field exponentialIntegralODE) univ := by
  have he : field exponentialIntegralODE =
      (fun q : (ℝ × ℝ) × ℝ => Real.exp (q.2 * q.1.1)) := by
    funext q
    exact exponentialIntegralODE_eval _ _ _
  rw [he]
  exact (contDiff_snd.mul contDiff_fst.fst).exp.contDiffOn

private lemma exponentialIntegralODE_value (t p : ℝ) :
    (t,((0,0),p)) ∈ parameterSolutionDomainValue exponentialIntegralODE ∧
    parameterSolutionValueValue exponentialIntegralODE t 0 0 p =
      ∫ s in 0..t, Real.exp (p*s) := by
  let J : OpenTimeInterval := ⟨⟨univ, ⟨0,mem_univ _⟩, ordConnected_univ⟩,isOpen_univ⟩
  let z : ℝ → ℝ := ScalarLinear.variation (fun _ => 0) (fun s => Real.exp (p*s)) 0 0
  have hz := (ScalarLinear.classical_variation_of_constants J (fun _ => 0)
    (fun s => Real.exp (p*s)) 0 0 continuousOn_const (by fun_prop) (mem_univ _) z).mpr
      (fun _ _ => rfl)
  have hIVP : classicalParameterIVPOnValue exponentialIntegralODE p J z 0 0 := by
    refine ⟨⟨hz.1,fun _ _ => mem_univ _,?_⟩,mem_univ _,hz.2.1⟩
    intro s hs
    rw [exponentialIntegralODE_eval]
    simpa using hz.2.2 s hs
  have hLip := exponentialIntegralODE.locallyLipschitzInState_of_contDiffOn
    (exponentialIntegralODE_c2.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num))
  obtain ⟨_,_,_,_,_,hres,_⟩ := ParameterODE.canonical_solution
    exponentialIntegralODE hLip 0 0 p (mem_univ _)
  have hr := hres J z
    ((classicalParameterIVPOn_iff exponentialIntegralODE p J z 0 0).mp hIVP)
  have hdom : (t,((0,0),p)) ∈ parameterSolutionDomainValue exponentialIntegralODE :=
    ⟨mem_univ _,hr.1 (mem_univ _)⟩
  refine ⟨hdom,?_⟩
  have he := (ParameterODE.solutionValue_on_domain exponentialIntegralODE hLip
    t 0 0 p hdom).1.trans (hr.2 (mem_univ _))
  simpa [z,ScalarLinear.variation,ScalarLinear.primitive] using he

/-- Smoothness of the integral coefficient does not require division by A. -/
lemma exponentialIntegral_c2 (T : ℝ) :
    ContDiff ℝ 2 (fun p : ℝ => ∫ s in 0..T, Real.exp (p*s)) := by
  have hc := Ch06.CkDependence.joint_ck 2 (by decide) exponentialIntegralODE
    exponentialIntegralODE_c2
  have hcomp : ContDiffOn ℝ 2
      (fun p : ℝ => parameterSolutionValueValue exponentialIntegralODE T 0 0 p) univ :=
    hc.2.comp (f := fun p : ℝ => (T,((0,0),p)))
      (contDiffOn_const.prodMk
        ((contDiffOn_const.prodMk contDiffOn_const).prodMk contDiffOn_id))
      (fun p _ => (exponentialIntegralODE_value T p).1)
  have heq : (fun p : ℝ => parameterSolutionValueValue exponentialIntegralODE T 0 0 p) =
      (fun p : ℝ => ∫ s in 0..T, Real.exp (p*s)) :=
    funext (fun p => (exponentialIntegralODE_value T p).2)
  rw [heq] at hcomp
  exact contDiffOn_univ.mp hcomp

lemma cubicCoefficient_c2 (d : AngularData) (h : Hypotheses d) :
    ContDiffOn ℝ 2 (cubicCoefficient d) (Ioo (-d.ε) d.ε) := by
  exact (h.smooth_B.mul ((contDiffOn_const.mul h.smooth_A).exp)).mul
    ((exponentialIntegral_c2 d.T).comp_contDiffOn (contDiffOn_const.mul h.smooth_A))

lemma endpointError_c2 (d : AngularData) (h : Hypotheses d) {δ η : ℝ}
    (hη : η ≤ d.ε)
    (hdom : ∀ p ∈ parameterBox δ η, (d.T,p) ∈ amplitudeDomain d h) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => endpointError d h p.1 p.2)
      (parameterBox δ η) := by
  have hA : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => d.A p.2) (parameterBox δ η) :=
    h.smooth_A.comp contDiffOn_snd (fun p hp =>
      ⟨(neg_le_neg hη).trans_lt hp.2.1,hp.2.2.trans_le hη⟩)
  have hK : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => cubicCoefficient d p.2)
      (parameterBox δ η) :=
    (cubicCoefficient_c2 d h).comp contDiffOn_snd (fun p hp =>
      ⟨(neg_le_neg hη).trans_lt hp.2.1,hp.2.2.trans_le hη⟩)
  have hY : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => amplitude d h d.T p.1 p.2)
      (parameterBox δ η) :=
    (amplitude_c2 d h).2.comp (f := fun p : ℝ × ℝ => (d.T,p))
      (contDiffOn_const.prodMk contDiffOn_id) hdom
  exact ((contDiffOn_fst.mul hY).sub
    ((contDiffOn_const.mul hA).exp.mul contDiffOn_fst)).sub
      (hK.mul (contDiffOn_fst.pow 3))

/-- Uniform estimates for both signs of the integrating-factor exponent. -/
lemma exponential_bounds {a N T s : ℝ} (ha : |a| ≤ N) (hs : s ∈ Icc 0 T) :
    |Real.exp (a*s)| ≤ Real.exp (N*T) ∧
    |Real.exp (-a*s)| ≤ Real.exp (N*T) := by
  have hN : 0 ≤ N := (abs_nonneg a).trans ha
  have hab : |a*s| ≤ N*T := by
    rw [abs_mul, abs_of_nonneg hs.1]
    exact mul_le_mul ha hs.2 hs.1 hN
  constructor
  · rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hab)
  · rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith [neg_le_abs (a*s)])

/-- A compact integrating-factor estimate; it applies equally at zero radius. -/
lemma weighted_integral_bound {a N T D : ℝ} {f : ℝ → ℝ}
    (ha : |a| ≤ N) (hD : 0 ≤ D)
    (hf : ∀ s ∈ Icc 0 T, |f s| ≤ D) {t : ℝ} (ht : t ∈ Icc 0 T) :
    |Real.exp (a*t) * ∫ s in 0..t, Real.exp (-a*s) * f s| ≤
      Real.exp (N*T) ^ 2 * D * T := by
  let H := Real.exp (N*T)
  have hH : 0 ≤ H := (Real.exp_pos _).le
  have hi : |∫ s in 0..t, Real.exp (-a*s) * f s| ≤ H * D * t := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t) (C := H*D) (f := fun s => Real.exp (-a*s) * f s) (by
        intro s hs
        rw [uIoc_of_le ht.1] at hs
        have hsT : s ∈ Icc 0 T := ⟨hs.1.le,hs.2.trans ht.2⟩
        simp only [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul (exponential_bounds ha hsT).2 (hf s hsT)
          (abs_nonneg _) hH)
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] using hi
  rw [abs_mul]
  calc
    |Real.exp (a*t)| * |∫ s in 0..t, Real.exp (-a*s) * f s| ≤
        H * (H * D * t) :=
      mul_le_mul (exponential_bounds ha ht).1 hi (abs_nonneg _) hH
    _ ≤ H^2 * D * T := by
      nlinarith [mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (sq_nonneg H) hD)]

lemma abs_cube_sub_le {x y R S D : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hx : |x| ≤ R) (hy : |y| ≤ S) (hxy : |x-y| ≤ D) :
    |x^3-y^3| ≤ D * (R^2+R*S+S^2) := by
  have hid : x^3-y^3 = (x-y)*(x^2+x*y+y^2) := by ring
  rw [hid,abs_mul]
  have hsum : |x^2+x*y+y^2| ≤ R^2+R*S+S^2 := by
    calc
      |x^2+x*y+y^2| ≤ |x^2|+|x*y|+|y^2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ R^2+R*S+S^2 := by
        simp only [abs_pow,abs_mul]
        exact add_le_add (add_le_add (pow_le_pow_left₀ (abs_nonneg _) hx 2)
          (mul_le_mul hx hy (abs_nonneg _) hR))
          (pow_le_pow_left₀ (abs_nonneg _) hy 2)
  exact mul_le_mul hxy hsum (abs_nonneg _) ((abs_nonneg (x-y)).trans hxy)

/-- The first substitution in variation of constants is uniformly cubic. -/
lemma radialSolution_linear_error_bound (d : AngularData) (h : Hypotheses d)
    {r μ L N : ℝ} (hL : 0 ≤ L) (hN : 0 ≤ N) (hr : |r| ≤ 1)
    (hμ : |μ| < d.ε) (hA : |d.A μ| ≤ N) (hB : |d.B μ| ≤ N)
    (hdom : ∀ θ ∈ Icc 0 d.T, (θ,(r,μ)) ∈ amplitudeDomain d h)
    (hu : ∀ θ ∈ Icc 0 d.T,
      |radialSolution d h θ r μ| ≤ L*|r| ∧ |radialSolution d h θ r μ| < d.ρ) :
    ∀ θ ∈ Icc 0 d.T,
      |radialSolution d h θ r μ - Real.exp (d.A μ*θ)*r| ≤
        (Real.exp (N*d.T)^2 * (N*L^3 + d.M*L^4) * d.T) * |r|^3 := by
  have hM := h.bound_nonneg
  have hf : ∀ s ∈ Icc 0 d.T,
      |d.B μ * radialSolution d h s r μ ^ 3 +
        remainder d s (radialSolution d h s r μ) μ| ≤
        (N*L^3+d.M*L^4)*|r|^3 := by
    intro s hs
    have hb := (h.remainder_bounds ((s,radialSolution d h s r μ),μ)
      ⟨hs,(hu s hs).2,hμ⟩).1
    have hpow : |r|^4 ≤ |r|^3 := by
      nlinarith [mul_le_mul_of_nonneg_left hr (pow_nonneg (abs_nonneg r) 3)]
    calc
      _ ≤ |d.B μ| * |radialSolution d h s r μ|^3 +
          d.M * |radialSolution d h s r μ|^4 := by
        calc
          _ ≤ |d.B μ * radialSolution d h s r μ ^ 3| +
              |remainder d s (radialSolution d h s r μ) μ| := abs_add_le _ _
          _ = |d.B μ| * |radialSolution d h s r μ|^3 +
              |remainder d s (radialSolution d h s r μ) μ| := by
            rw [abs_mul,abs_pow]
          _ ≤ _ := add_le_add le_rfl hb
      _ ≤ N*(L*|r|)^3+d.M*(L*|r|)^4 :=
        add_le_add
          (mul_le_mul hB (pow_le_pow_left₀ (abs_nonneg _) (hu s hs).1 3)
            (pow_nonneg (abs_nonneg _) _) hN)
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hu s hs).1 4) h.bound_nonneg)
      _ ≤ (N*L^3+d.M*L^4)*|r|^3 := by
        nlinarith [mul_le_mul_of_nonneg_left hpow
          (mul_nonneg h.bound_nonneg (pow_nonneg hL 4))]
  intro θ hθ
  have he : radialSolution d h θ r μ - Real.exp (d.A μ*θ)*r =
      Real.exp (d.A μ*θ) * ∫ s in 0..θ, Real.exp (-d.A μ*s) *
        (d.B μ * radialSolution d h s r μ^3 +
          remainder d s (radialSolution d h s r μ) μ) := by
    rw [radialSolution_integral d h hdom θ hθ]
    ring
  rw [he]
  convert weighted_integral_bound hA
    (show 0 ≤ (N*L^3+d.M*L^4)*|r|^3 by positivity) hf hθ using 1 <;> ring


/-- The exact cubic residual is an integral of the cubic substitution error
and the original fourth-order vector-field remainder. -/
lemma endpointError_integral (d : AngularData) (h : Hypotheses d)
    {r μ : ℝ}
    (hdom : ∀ θ ∈ Icc 0 d.T, (θ,(r,μ)) ∈ amplitudeDomain d h) :
    endpointError d h r μ = Real.exp (d.A μ*d.T) *
      ∫ s in 0..d.T, Real.exp (-d.A μ*s) *
        (d.B μ * (radialSolution d h s r μ^3 - (Real.exp (d.A μ*s)*r)^3) +
          remainder d s (radialSolution d h s r μ) μ) := by
  let u : ℝ → ℝ := fun s => radialSolution d h s r μ
  let f : ℝ → ℝ := fun s => Real.exp (-d.A μ*s) *
    (d.B μ * u s^3 + remainder d s (u s) μ)
  let j : ℝ → ℝ := fun s => d.B μ * r^3 * Real.exp (2*d.A μ*s)
  have hu : ContinuousOn u (Icc 0 d.T) := (radialSolution_c2_on d h hdom).continuousOn
  have hg : ContinuousOn (fun s => d.G ((s,u s),μ)) (Icc 0 d.T) :=
    h.smooth_G.continuousOn.comp
      ((continuousOn_id.prodMk hu).prodMk continuousOn_const)
      (fun s hs => (amplitude_derivative d h (hdom s hs)).1)
  have hf : ContinuousOn f (Icc 0 d.T) := by
    have hc : ContinuousOn (fun s => u s * d.G ((s,u s),μ) - d.A μ*u s)
        (Icc 0 d.T) := (hu.mul hg).sub (continuousOn_const.mul hu)
    have he : ContinuousOn (fun s : ℝ => Real.exp (-d.A μ*s)) (Icc 0 d.T) := by fun_prop
    apply (he.mul hc).congr
    intro s _
    dsimp [f,remainder,angularField]
    ring
  have hj : ContinuousOn j (Icc 0 d.T) := by dsimp [j]; fun_prop
  have hi : (∫ s in 0..d.T, f s) - ∫ s in 0..d.T, j s =
      ∫ s in 0..d.T, Real.exp (-d.A μ*s) *
        (d.B μ * (u s^3 - (Real.exp (d.A μ*s)*r)^3) + remainder d s (u s) μ) := by
    rw [← intervalIntegral.integral_sub (hf.intervalIntegrable_of_Icc h.T_pos.le)
      (hj.intervalIntegrable_of_Icc h.T_pos.le)]
    apply intervalIntegral.integral_congr
    intro s _
    have he : Real.exp (-d.A μ*s) * Real.exp (d.A μ*s)^3 =
        Real.exp (2*d.A μ*s) := by
      rw [show (3 : ℕ) = 1+1+1 from rfl, pow_succ, pow_succ, pow_one]
      rw [← mul_assoc,← mul_assoc,← Real.exp_add]
      simp only [neg_mul,neg_add_cancel,Real.exp_zero,one_mul]
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [f,j]
    rw [mul_pow]
    rw [← he]
    ring
  have hjI : (∫ s in 0..d.T, j s) =
      d.B μ*r^3 * ∫ s in 0..d.T, Real.exp (2*d.A μ*s) :=
    intervalIntegral.integral_const_mul _ _
  have hsol := radialSolution_integral d h hdom d.T ⟨h.T_pos.le,le_rfl⟩
  change endpoint d h r μ = Real.exp (d.A μ*d.T) * (r + ∫ s in 0..d.T, f s) at hsol
  rw [← hi,hjI]
  dsimp [endpointError,cubicCoefficient]
  rw [hsol,mul_comm d.T (d.A μ)]
  ring

/-- An explicit fourth-order bound after the cubic substitution. Constants
are uniform as soon as L and N are uniform, and no radius is divided out. -/
lemma endpointError_bound (d : AngularData) (h : Hypotheses d)
    {r μ L N : ℝ} (hL : 0 ≤ L) (hN : 0 ≤ N) (hr : |r| ≤ 1)
    (hμ : |μ| < d.ε) (hA : |d.A μ| ≤ N) (hB : |d.B μ| ≤ N)
    (hdom : ∀ θ ∈ Icc 0 d.T, (θ,(r,μ)) ∈ amplitudeDomain d h)
    (hu : ∀ θ ∈ Icc 0 d.T,
      |radialSolution d h θ r μ| ≤ L*|r| ∧ |radialSolution d h θ r μ| < d.ρ) :
    let H := Real.exp (N*d.T)
    let D := H^2 * (N*L^3+d.M*L^4) * d.T
    |endpointError d h r μ| ≤
      (H^2 * (N*D*(L^2+L*H+H^2)+d.M*L^4) * d.T) * |r|^4 := by
  let H := Real.exp (N*d.T)
  let D := H^2 * (N*L^3+d.M*L^4) * d.T
  have hH : 0 ≤ H := (Real.exp_pos _).le
  have hM := h.bound_nonneg
  have hT := h.T_pos.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlin := radialSolution_linear_error_bound d h hL hN hr hμ hA hB hdom hu
  have hcubic : ∀ s ∈ Icc 0 d.T,
      |radialSolution d h s r μ^3-(Real.exp (d.A μ*s)*r)^3| ≤
        D*(L^2+L*H+H^2)*|r|^4 := by
    intro s hs
    have hep : |Real.exp (d.A μ*s)*r| ≤ H*|r| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (exponential_bounds hA hs).1 (abs_nonneg _)
    have hc := abs_cube_sub_le
      (mul_nonneg hL (abs_nonneg r)) (mul_nonneg hH (abs_nonneg r))
      (hu s hs).1 hep (hlin s hs)
    have hpow : |r|^5 ≤ |r|^4 := by
      nlinarith [mul_le_mul_of_nonneg_left hr (pow_nonneg (abs_nonneg r) 4)]
    calc
      _ ≤ D*|r|^3 * ((L*|r|)^2+(L*|r|)*(H*|r|)+(H*|r|)^2) := hc
      _ = D*(L^2+L*H+H^2)*|r|^5 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hf : ∀ s ∈ Icc 0 d.T,
      |d.B μ * (radialSolution d h s r μ^3-(Real.exp (d.A μ*s)*r)^3) +
          remainder d s (radialSolution d h s r μ) μ| ≤
        (N*D*(L^2+L*H+H^2)+d.M*L^4)*|r|^4 := by
    intro s hs
    have hb := (h.remainder_bounds ((s,radialSolution d h s r μ),μ)
      ⟨hs,(hu s hs).2,hμ⟩).1
    calc
      _ ≤ |d.B μ| * |radialSolution d h s r μ^3-(Real.exp (d.A μ*s)*r)^3| +
          |remainder d s (radialSolution d h s r μ) μ| := by
        calc
          _ ≤ |d.B μ * (radialSolution d h s r μ^3-(Real.exp (d.A μ*s)*r)^3)| +
              |remainder d s (radialSolution d h s r μ) μ| := abs_add_le _ _
          _ = _ := by rw [abs_mul]
      _ ≤ N*(D*(L^2+L*H+H^2)*|r|^4)+d.M*(L*|r|)^4 :=
        add_le_add (mul_le_mul hB (hcubic s hs) (abs_nonneg _) hN)
          (hb.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hu s hs).1 4) hM))
      _ = _ := by ring
  rw [endpointError_integral d h hdom]
  convert weighted_integral_bound hA
    (show 0 ≤ (N*D*(L^2+L*H+H^2)+d.M*L^4)*|r|^4 by positivity)
    hf ⟨hT,le_rfl⟩ using 1 <;> ring


lemma parameterBox_mono {δ η δ' η' : ℝ} (hδ : δ' ≤ δ) (hη : η' ≤ η) :
    parameterBox δ' η' ⊆ parameterBox δ η := by
  intro p hp
  exact ⟨⟨(neg_le_neg hδ).trans_lt hp.1.1,hp.1.2.trans_le hδ⟩,
    ⟨(neg_le_neg hη).trans_lt hp.2.1,hp.2.2.trans_le hη⟩⟩

lemma evolutionOnBox_shrink (d : AngularData) (h : Hypotheses d)
    {δ η L a b δ' η' : ℝ}
    (he : Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ η L a b)
    (hδ' : 0 < δ') (hη' : 0 < η') (hδ : δ' ≤ δ) (hη : η' ≤ η) :
    Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ' η' L a b := by
  rcases he with ⟨_,hδρ,_,hηε,hL,ha,hb,hLδ,hdom,hY,hevo,hzero,hQ,hfact⟩
  have hbox := parameterBox_mono hδ hη
  have hprod : (Ioo a b ×ˢ parameterBox δ' η') ⊆
      (Ioo a b ×ˢ parameterBox δ η) := fun _ hp => ⟨hp.1,hbox hp.2⟩
  exact ⟨hδ',hδ.trans_lt hδρ,hη',hη.trans_lt hηε,hL,ha,hb,
    (mul_le_mul_of_nonneg_left hδ hL.le).trans_lt hLδ,hprod.trans hdom,
    hY.mono hprod,fun r μ hp => hevo r μ (hbox hp),
    fun μ hμ => hzero μ (hμ.trans_le hη),hQ.mono hbox,hfact⟩

/-- Common evolution, smooth error, and the undifferentiated uniform quartic
estimate. The two differentiated estimates are proved separately below. -/
theorem quarticEndpointEstimate (d : AngularData) (h : Hypotheses d) :
    ∃ δ η L C a b : ℝ,
      0 ≤ C ∧
      Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ η L a b ∧
      ContDiffOn ℝ 2 (fun p : ℝ × ℝ => endpointError d h p.1 p.2)
        (parameterBox δ η) ∧
      (∀ r μ, (r,μ) ∈ parameterBox δ η →
        |endpointError d h r μ| ≤ C*|r|^4) := by
  obtain ⟨δ,η,L,a,b,he⟩ := normalizedEvolution d h
  have hη := he.2.2.1
  have hηε := he.2.2.2.1
  have hδ := he.1
  let δ' := min δ 1
  let η' := η/2
  have hδ' : 0 < δ' := lt_min hδ zero_lt_one
  have hη' : 0 < η' := half_pos hη
  have hη'η : η' ≤ η := (half_lt_self hη).le
  have he' := evolutionOnBox_shrink d h he hδ' hη' (min_le_left _ _) hη'η
  have hparam : Icc (-η') η' ⊆ Ioo (-d.ε) d.ε := by
    intro μ hμ
    have hη'ε : η' < d.ε := hη'η.trans_lt hηε
    exact ⟨(neg_lt_neg hη'ε).trans_le hμ.1,hμ.2.trans_lt hη'ε⟩
  obtain ⟨NA,hNA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.smooth_A.continuousOn.mono hparam)
  obtain ⟨NB,hNB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.smooth_B.continuousOn.mono hparam)
  let N := max (max NA NB) 0
  have hN : 0 ≤ N := le_max_right _ _
  have hL : 0 < L := he'.2.2.2.2.1
  let H := Real.exp (N*d.T)
  let D := H^2*(N*L^3+d.M*L^4)*d.T
  let C := H^2*(N*D*(L^2+L*H+H^2)+d.M*L^4)*d.T
  have hH : 0 ≤ H := (Real.exp_pos _).le
  have hM := h.bound_nonneg
  have hT := h.T_pos.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rcases he' with ⟨hd,hdρ,hηp,hηpε,hLp,ha,hb,hLδ,hdom,hY,hev,hzero,hQ,hfact⟩
  refine ⟨δ',η',L,C,a,b,hC,?_,?_,?_⟩
  · exact ⟨hd,hdρ,hηp,hηpε,hLp,ha,hb,hLδ,hdom,hY,hev,hzero,hQ,hfact⟩
  · exact endpointError_c2 d h hηpε.le (fun p hp => hdom ⟨⟨ha.trans h.T_pos,hb⟩,hp⟩)
  · intro r μ hp
    have hμclosed : μ ∈ Icc (-η') η' := ⟨hp.2.1.le,hp.2.2.le⟩
    have hA : |d.A μ| ≤ N := (hNA μ hμclosed).trans
      ((le_max_left NA NB).trans (le_max_left _ _))
    have hB : |d.B μ| ≤ N := (hNB μ hμclosed).trans
      ((le_max_right NA NB).trans (le_max_left _ _))
    have hr : |r| ≤ 1 := (abs_lt.mpr hp.1).le.trans (min_le_right _ _)
    have hμ : |μ| < d.ε := (abs_lt.mpr hp.2).trans hηpε
    have hdom' : ∀ θ ∈ Icc 0 d.T, (θ,(r,μ)) ∈ amplitudeDomain d h :=
      fun θ hθ => hdom ⟨⟨ha.trans_le hθ.1,hθ.2.trans_lt hb⟩,hp⟩
    have hu := (hev r μ hp).2.2.2
    exact endpointError_bound d h hLp.le hN hr hμ hA hB hdom'
      (fun θ hθ => ⟨(hu θ hθ).1,(hu θ hθ).2.1⟩)


/-- The original scalar equation, used to apply the actual state and parameter
variation theorems. The normalized equation remains the construction of u. -/
def radialODE (d : AngularData) (h : Hypotheses d) : ParameterODE ℝ ℝ where
  domain := d.domain
  isOpen_domain := h.open_domain
  field := fun q => angularField d q.val.1.1 q.val.1.2 q.val.2
  continuous_field := by
    have hc : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => angularField d q.1.1 q.1.2 q.2)
        d.domain := continuousOn_fst.snd.mul h.smooth_G.continuousOn
    exact continuousOn_iff_continuous_domRestrict.mp hc

lemma radialODE_eval (d : AngularData) (h : Hypotheses d) {θ r μ : ℝ}
    (hq : ((θ,r),μ) ∈ d.domain) :
    parameterEvalValue (radialODE d h) θ r μ = angularField d θ r μ := by
  simp [parameterEvalValue,radialODE,hq]

lemma radialODE_c2 (d : AngularData) (h : Hypotheses d) :
    ContDiffOn ℝ 2 (field (radialODE d h)) (radialODE d h).domain := by
  exact (contDiffOn_fst.snd.mul h.smooth_G).congr
    (fun q hq => radialODE_eval d h hq)

/-- The normalized construction agrees with the original canonical scalar
IVP on every actual open common solution interval. -/
lemma radialSolution_eq_canonical (d : AngularData) (h : Hypotheses d)
    (J : OpenTimeInterval) (h0 : 0 ∈ J.carrier) {r μ : ℝ}
    (hdom : ∀ θ ∈ J.carrier, (θ,(r,μ)) ∈ amplitudeDomain d h) :
    ∀ θ ∈ J.carrier,
      (θ,((0,r),μ)) ∈ parameterSolutionDomainValue (radialODE d h) ∧
      radialSolution d h θ r μ = parameterSolutionValueValue (radialODE d h) θ 0 r μ := by
  have hinit : ((0,r),μ) ∈ d.domain := by
    simpa only [normalizedODE,normalizedDomain,mem_ofPred_eq,mul_one] using (hdom 0 h0).1
  have hIVP : classicalParameterIVPOnValue (radialODE d h) μ J
      (fun θ => radialSolution d h θ r μ) 0 r := by
    refine ⟨⟨(radialSolution_c2_on d h hdom).of_le (by norm_num),
      fun θ hθ => (amplitude_derivative d h (hdom θ hθ)).1,?_⟩,
      h0,radialSolution_initial d h hinit⟩
    intro θ hθ
    rw [radialODE_eval d h (amplitude_derivative d h (hdom θ hθ)).1]
    exact radialSolution_derivative d h (hdom θ hθ)
  have hLip := (radialODE d h).locallyLipschitzInState_of_contDiffOn
    ((radialODE_c2 d h).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num))
  obtain ⟨_,_,_,_,_,hres,_⟩ := ParameterODE.canonical_solution (radialODE d h)
    hLip 0 r μ hinit
  have hr := hres J (fun θ => radialSolution d h θ r μ)
    ((classicalParameterIVPOn_iff (radialODE d h) μ J _ 0 r).mp hIVP)
  intro θ hθ
  have hq : (θ,((0,r),μ)) ∈ parameterSolutionDomainValue (radialODE d h) :=
    ⟨hinit,hr.1 hθ⟩
  exact ⟨hq,((ParameterODE.solutionValue_on_domain (radialODE d h)
    hLip θ 0 r μ hq).1.trans (hr.2 hθ)).symm⟩

/-- Actual radius and parameter derivatives of the constructed curve, as
canonical first variations; their existence is not assumed. -/
lemma radialSolution_first_derivatives (d : AngularData) (h : Hypotheses d)
    {a b δ η θ r μ : ℝ} (ha : a < 0) (hb : 0 < b)
    (hdom : (Ioo a b ×ˢ parameterBox δ η) ⊆ amplitudeDomain d h)
    (hθ : θ ∈ Ioo a b) (hp : (r,μ) ∈ parameterBox δ η) :
    HasDerivAt (fun x => radialSolution d h θ x μ)
      (stateVariation (radialODE d h) 0 r μ θ 1) r ∧
    HasDerivAt (fun ν => radialSolution d h θ r ν)
      (parameterVariation (radialODE d h) 0 r μ θ 1) μ := by
  let J : OpenTimeInterval := ⟨⟨Ioo a b,⟨0,ha,hb⟩,ordConnected_Ioo⟩,isOpen_Ioo⟩
  have h0 : 0 ∈ J.carrier := ⟨ha,hb⟩
  have hcan := radialSolution_eq_canonical d h J h0
    (fun t ht => hdom ⟨ht,hp⟩) θ hθ
  have hF1 := (radialODE_c2 d h).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hv := (Ch06.C1Dependence.state_variation (radialODE d h) hF1
    0 r μ hcan.1.1).2.1 θ hcan.1.2
  have hw := (Ch06.C1Dependence.parameter_variation (radialODE d h) hF1
    0 r μ hcan.1.1).2.1 θ hcan.1.2
  have hrEq : (fun x => radialSolution d h θ x μ) =ᶠ[𝓝 r]
      (fun x => parameterSolutionValueValue (radialODE d h) θ 0 x μ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with x hx
    exact (radialSolution_eq_canonical d h J h0 (r := x) (μ := μ)
      (fun t ht => hdom ⟨ht,hx,hp.2⟩) θ hθ).2
  have hμEq : (fun ν => radialSolution d h θ r ν) =ᶠ[𝓝 μ]
      (fun ν => parameterSolutionValueValue (radialODE d h) θ 0 r ν) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.2] with ν hν
    exact (radialSolution_eq_canonical d h J h0 (r := r) (μ := ν)
      (fun t ht => hdom ⟨ht,hp.1,hν⟩) θ hθ).2
  exact ⟨hv.1.hasDerivAt.congr_of_eventuallyEq hrEq,
    hw.1.hasDerivAt.congr_of_eventuallyEq hμEq⟩


lemma angularField_state_derivative (d : AngularData) (h : Hypotheses d)
    {θ x μ : ℝ} (hq : ((θ,x),μ) ∈ cylinder d) :
    HasDerivAt (fun z => angularField d θ z μ)
      (d.A μ + 3*d.B μ*x^2 + deriv (fun z => remainder d θ z μ) x) x := by
  have hd := (((h.remainder_differentiable ((θ,x),μ) hq).1.hasDerivAt.add
    ((hasDerivAt_id x).const_mul (d.A μ))).add
    (((hasDerivAt_id x).pow 3).const_mul (d.B μ)))
  convert hd using 1 <;> (try funext z) <;> dsimp [remainder] <;> ring

lemma angularField_parameter_derivative (d : AngularData) (h : Hypotheses d)
    {θ x μ : ℝ} (hq : ((θ,x),μ) ∈ cylinder d) :
    HasDerivAt (fun ν => angularField d θ x ν)
      (deriv d.A μ*x + deriv d.B μ*x^3 + deriv (fun ν => remainder d θ x ν) μ) μ := by
  have hμ : μ ∈ Ioo (-d.ε) d.ε := abs_lt.mp hq.2.2
  have hA : DifferentiableAt ℝ d.A μ :=
    (h.smooth_A.differentiableOn (by norm_num) μ hμ).differentiableAt
      (isOpen_Ioo.mem_nhds hμ)
  have hB : DifferentiableAt ℝ d.B μ :=
    (h.smooth_B.differentiableOn (by norm_num) μ hμ).differentiableAt
      (isOpen_Ioo.mem_nhds hμ)
  have hd := (((h.remainder_differentiable ((θ,x),μ) hq).2.hasDerivAt.add
    (hA.hasDerivAt.mul_const x)).add (hB.hasDerivAt.mul_const (x^3)))
  convert hd using 1 <;> (try funext z) <;> dsimp [remainder] <;> ring

lemma radialODE_state_derivative (d : AngularData) (h : Hypotheses d)
    {θ x μ : ℝ} (hq : ((θ,x),μ) ∈ cylinder d) :
    HasDerivAt (fun z => parameterEvalValue (radialODE d h) θ z μ)
      (d.A μ + 3*d.B μ*x^2 + deriv (fun z => remainder d θ z μ) x) x := by
  apply (angularField_state_derivative d h hq).congr_of_eventuallyEq
  have hn : {z : ℝ | ((θ,z),μ) ∈ d.domain} ∈ 𝓝 x :=
    (h.open_domain.preimage ((continuous_const.prodMk continuous_id).prodMk continuous_const)).mem_nhds
      (h.contains_cylinder hq)
  filter_upwards [hn] with z hz
  exact radialODE_eval d h hz

lemma radialODE_parameter_derivative (d : AngularData) (h : Hypotheses d)
    {θ x μ : ℝ} (hq : ((θ,x),μ) ∈ cylinder d) :
    HasDerivAt (fun ν => parameterEvalValue (radialODE d h) θ x ν)
      (deriv d.A μ*x + deriv d.B μ*x^3 + deriv (fun ν => remainder d θ x ν) μ) μ := by
  apply (angularField_parameter_derivative d h hq).congr_of_eventuallyEq
  have hn : {ν : ℝ | ((θ,x),ν) ∈ d.domain} ∈ 𝓝 μ :=
    (h.open_domain.preimage (continuous_const.prodMk continuous_id)).mem_nhds
      (h.contains_cylinder hq)
  filter_upwards [hn] with ν hν
  exact radialODE_eval d h hν

lemma radialSolution_variation_initial (d : AngularData) (h : Hypotheses d)
    {a b δ η r μ : ℝ} (ha : a < 0) (hb : 0 < b)
    (hdom : (Ioo a b ×ˢ parameterBox δ η) ⊆ amplitudeDomain d h)
    (hp : (r,μ) ∈ parameterBox δ η) :
    deriv (fun x => radialSolution d h 0 x μ) r = 1 ∧
    deriv (fun ν => radialSolution d h 0 r ν) μ = 0 := by
  have hd := radialSolution_first_derivatives d h ha hb hdom ⟨ha,hb⟩ hp
  have hcan : ((0,r),μ) ∈ (radialODE d h).domain := by
    simpa only [radialODE,normalizedODE,normalizedDomain,mem_ofPred_eq,mul_one] using
      (hdom (show (0,(r,μ)) ∈ _ from ⟨⟨ha,hb⟩,hp⟩)).1
  have hF1 := (radialODE_c2 d h).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  rw [hd.1.deriv,hd.2.deriv,
    (Ch06.C1Dependence.state_variation (radialODE d h) hF1 0 r μ hcan).1,
    (Ch06.C1Dependence.parameter_variation (radialODE d h) hF1 0 r μ hcan).1]
  simp

lemma radialSolution_variation_equations (d : AngularData) (h : Hypotheses d)
    {a b δ η θ r μ : ℝ} (ha : a < 0) (hb : 0 < b)
    (hdom : (Ioo a b ×ˢ parameterBox δ η) ⊆ amplitudeDomain d h)
    (hθ : θ ∈ Ioo a b) (hp : (r,μ) ∈ parameterBox δ η)
    (hcyl : ((θ,radialSolution d h θ r μ),μ) ∈ cylinder d) :
    let u := radialSolution d h θ r μ
    let v := deriv (fun x => radialSolution d h θ x μ) r
    let w := deriv (fun ν => radialSolution d h θ r ν) μ
    let α := d.A μ + 3*d.B μ*u^2 + deriv (fun x => remainder d θ x μ) u
    let β := deriv d.A μ*u + deriv d.B μ*u^3 + deriv (fun ν => remainder d θ u ν) μ
    HasDerivAt (fun t => deriv (fun x => radialSolution d h t x μ) r) (α*v) θ ∧
    HasDerivAt (fun t => deriv (fun ν => radialSolution d h t r ν) μ) (α*w+β) θ := by
  dsimp only
  let J : OpenTimeInterval := ⟨⟨Ioo a b,⟨0,ha,hb⟩,ordConnected_Ioo⟩,isOpen_Ioo⟩
  have hcan := radialSolution_eq_canonical d h J ⟨ha,hb⟩
    (fun t ht => hdom ⟨ht,hp⟩) θ hθ
  have hF1 := (radialODE_c2 d h).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hv := (Ch06.C1Dependence.state_variation (radialODE d h) hF1
    0 r μ hcan.1.1).2.1 θ hcan.1.2
  have hw := (Ch06.C1Dependence.parameter_variation (radialODE d h) hF1
    0 r μ hcan.1.1).2.1 θ hcan.1.2
  have hd := radialSolution_first_derivatives d h ha hb hdom hθ hp
  have hvEq : (fun t => deriv (fun x => radialSolution d h t x μ) r) =ᶠ[𝓝 θ]
      (fun t => stateVariation (radialODE d h) 0 r μ t 1) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact (radialSolution_first_derivatives d h ha hb hdom ht hp).1.deriv
  have hwEq : (fun t => deriv (fun ν => radialSolution d h t r ν) μ) =ᶠ[𝓝 θ]
      (fun t => parameterVariation (radialODE d h) 0 r μ t 1) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact (radialSolution_first_derivatives d h ha hb hdom ht hp).2.deriv
  have hcoef : stateCoefficient (radialODE d h) 0 r μ θ =
      fderiv ℝ (fun z => parameterEvalValue (radialODE d h) θ z μ)
        (radialSolution d h θ r μ) := by
    simp only [stateCoefficient,solution,hcan.2]
  have hpar : parameterCoefficient (radialODE d h) 0 r μ θ 1 =
      deriv d.A μ*radialSolution d h θ r μ + deriv d.B μ*(radialSolution d h θ r μ)^3 +
        deriv (fun ν => remainder d θ (radialSolution d h θ r μ) ν) μ := by
    simp only [parameterCoefficient,solution,← hcan.2,fderiv_apply_one_eq_deriv]
    exact (radialODE_parameter_derivative d h hcyl).deriv
  constructor
  · have hvd := hv.2.clm_apply (hasDerivAt_const θ (1 : ℝ))
    simp only [ContinuousLinearMap.comp_apply,zero_add,map_zero,add_zero,hcoef,
      fderiv_eq_deriv_mul,(radialODE_state_derivative d h hcyl).deriv] at hvd
    rw [← hd.1.deriv] at hvd
    exact hvd.congr_of_eventuallyEq hvEq
  · have hwd := hw.2.clm_apply (hasDerivAt_const θ (1 : ℝ))
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      zero_add,map_zero,add_zero,hcoef,hpar,
      fderiv_eq_deriv_mul,(radialODE_state_derivative d h hcyl).deriv] at hwd
    rw [← hd.2.deriv] at hwd
    exact hwd.congr_of_eventuallyEq hwEq


lemma amplitude_parameter_derivatives (d : AngularData) (h : Hypotheses d)
    {θ r μ : ℝ} (hq : (θ,(r,μ)) ∈ amplitudeDomain d h) :
    HasDerivAt (fun x => amplitude d h θ x μ)
      (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => amplitude d h q.1 q.2.1 q.2.2)
        (θ,(r,μ)) (0,(1,0))) r ∧
    HasDerivAt (fun ν => amplitude d h θ r ν)
      (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => amplitude d h q.1 q.2.1 q.2.2)
        (θ,(r,μ)) (0,(0,1))) μ := by
  have hf := ((amplitude_c2 d h).2.contDiffAt
    ((amplitude_c2 d h).1.mem_nhds hq)).differentiableAt (by norm_num)
  constructor
  · exact hf.hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r θ).prodMk ((hasDerivAt_id r).prodMk (hasDerivAt_const r μ)))
  · exact hf.hasFDerivAt.comp_hasDerivAt μ
      ((hasDerivAt_const μ θ).prodMk ((hasDerivAt_const μ r).prodMk (hasDerivAt_id μ)))

/-- Compact C² dependence bounds both first variations uniformly. The parameter
variation has a factor of the signed initial radius, including at zero. -/
lemma uniform_first_derivative_bounds (d : AngularData) (h : Hypotheses d)
    {δ η L a b : ℝ}
    (he : Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ η L a b) :
    ∃ δ' η' V W : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ 1 ∧
      0 < η' ∧ η' ≤ η ∧ 0 ≤ V ∧ 0 ≤ W ∧
      (∀ r μ, (r,μ) ∈ parameterBox δ' η' → ∀ θ ∈ Icc 0 d.T,
        |deriv (fun x => radialSolution d h θ x μ) r| ≤ V ∧
        |deriv (fun ν => radialSolution d h θ r ν) μ| ≤ W*|r|) := by
  rcases he with ⟨hδ,hδρ,hη,hηε,hL,ha,hb,hLδ,hdom,hY,hev,hzero,hQ,hfact⟩
  let δ' := min (δ/2) 1
  let η' := η/2
  have hδ' : 0 < δ' := lt_min (half_pos hδ) zero_lt_one
  have hη' : 0 < η' := half_pos hη
  have hδ'δ : δ' < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hη'η : η' < η := half_lt_self hη
  let K : Set (ℝ × (ℝ × ℝ)) := Icc 0 d.T ×ˢ (Icc (-δ') δ' ×ˢ Icc (-η') η')
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKD : K ⊆ amplitudeDomain d h := by
    intro q hq
    exact hdom ⟨⟨ha.trans_le hq.1.1,hq.1.2.trans_lt hb⟩,
      ⟨(neg_lt_neg hδ'δ).trans_le hq.2.1.1,hq.2.1.2.trans_lt hδ'δ⟩,
      ⟨(neg_lt_neg hη'η).trans_le hq.2.2.1,hq.2.2.2.trans_lt hη'η⟩⟩
  let Y := fun q : ℝ × (ℝ × ℝ) => amplitude d h q.1 q.2.1 q.2.2
  obtain ⟨NY,hNY⟩ := hK.exists_bound_of_continuousOn
    ((amplitude_c2 d h).2.continuousOn.mono hKD)
  obtain ⟨ND,hND⟩ := hK.exists_bound_of_continuousOn
    (((amplitude_c2 d h).2.continuousOn_fderiv_of_isOpen (amplitude_c2 d h).1
      (by norm_num)).mono hKD)
  let N := max (max NY ND) 0
  have hN : 0 ≤ N := le_max_right _ _
  refine ⟨δ',η',2*N,N,hδ',hδ'δ.le,min_le_right _ _,hη',hη'η.le,
    mul_nonneg (by norm_num) hN,hN,?_⟩
  intro r μ hp θ hθ
  have hr : |r| ≤ 1 := (abs_lt.mpr hp.1).le.trans (min_le_right _ _)
  have hqK : (θ,(r,μ)) ∈ K :=
    ⟨hθ,⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩
  have hYN : |amplitude d h θ r μ| ≤ N :=
    (hNY (θ,(r,μ)) hqK).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hDN : ‖fderiv ℝ Y (θ,(r,μ))‖ ≤ N :=
    (hND (θ,(r,μ)) hqK).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hdr : |fderiv ℝ Y (θ,(r,μ)) (0,(1,0))| ≤ N := by
    calc
      _ ≤ ‖fderiv ℝ Y (θ,(r,μ))‖ * ‖((0,(1,0)) : ℝ × (ℝ × ℝ))‖ :=
        (fderiv ℝ Y (θ,(r,μ))).le_opNorm _
      _ = ‖fderiv ℝ Y (θ,(r,μ))‖ := by norm_num [Prod.norm_def]
      _ ≤ N := hDN
  have hdμ : |fderiv ℝ Y (θ,(r,μ)) (0,(0,1))| ≤ N := by
    calc
      _ ≤ ‖fderiv ℝ Y (θ,(r,μ))‖ * ‖((0,(0,1)) : ℝ × (ℝ × ℝ))‖ :=
        (fderiv ℝ Y (θ,(r,μ))).le_opNorm _
      _ = ‖fderiv ℝ Y (θ,(r,μ))‖ := by norm_num [Prod.norm_def]
      _ ≤ N := hDN
  have hd := amplitude_parameter_derivatives d h (hKD hqK)
  have hvr := ((hasDerivAt_id r).mul hd.1).deriv
  have hwμ := (hd.2.const_mul r).deriv
  change deriv (fun x => radialSolution d h θ x μ) r = _ at hvr
  change deriv (fun ν => radialSolution d h θ r ν) μ = _ at hwμ
  constructor
  · rw [hvr]
    simp only [one_mul,id_eq]
    calc
      _ ≤ |amplitude d h θ r μ| + |r| * |fderiv ℝ Y (θ,(r,μ)) (0,(1,0))| := by
        simpa only [abs_mul] using abs_add_le (amplitude d h θ r μ)
          (r*fderiv ℝ Y (θ,(r,μ)) (0,(1,0)))
      _ ≤ N+1*N := add_le_add hYN (mul_le_mul hr hdr (abs_nonneg _) (by norm_num))
      _ = 2*N := by ring
  · rw [hwμ,abs_mul,mul_comm N]
    exact mul_le_mul_of_nonneg_left hdμ (abs_nonneg r)


lemma remainder_c2_on_strip (d : AngularData) (h : Hypotheses d) :
    ContDiffOn ℝ 2 (fun q : (ℝ × ℝ) × ℝ => remainder d q.1.1 q.1.2 q.2)
      (d.domain ∩ {q | q.2 ∈ Ioo (-d.ε) d.ε}) := by
  have hA : ContDiffOn ℝ 2 (fun q : (ℝ × ℝ) × ℝ => d.A q.2)
      (d.domain ∩ {q | q.2 ∈ Ioo (-d.ε) d.ε}) :=
    h.smooth_A.comp contDiffOn_snd (fun q hq => hq.2)
  have hB : ContDiffOn ℝ 2 (fun q : (ℝ × ℝ) × ℝ => d.B q.2)
      (d.domain ∩ {q | q.2 ∈ Ioo (-d.ε) d.ε}) :=
    h.smooth_B.comp contDiffOn_snd (fun q hq => hq.2)
  exact ((contDiffOn_fst.snd.mul (h.smooth_G.mono inter_subset_left)).sub
    (hA.mul contDiffOn_fst.snd)).sub (hB.mul (contDiffOn_fst.snd.pow 3))

lemma remainder_partials_continuousOn (d : AngularData) (h : Hypotheses d) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ => deriv (fun x => remainder d q.1.1 x q.2) q.1.2)
      (d.domain ∩ {q | q.2 ∈ Ioo (-d.ε) d.ε}) ∧
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ => deriv (fun μ => remainder d q.1.1 q.1.2 μ) q.2)
      (d.domain ∩ {q | q.2 ∈ Ioo (-d.ε) d.ε}) := by
  let R := fun q : (ℝ × ℝ) × ℝ => remainder d q.1.1 q.1.2 q.2
  let S : Set ((ℝ × ℝ) × ℝ) := d.domain ∩ {q | q.2 ∈ Ioo (-d.ε) d.ε}
  have hS : IsOpen S := h.open_domain.inter (isOpen_Ioo.preimage continuous_snd)
  have hR : ContDiffOn ℝ 2 R S := remainder_c2_on_strip d h
  have hd : ContinuousOn (fderiv ℝ R) S :=
    hR.continuousOn_fderiv_of_isOpen hS (by norm_num)
  constructor
  · refine (hd.clm_apply (continuousOn_const (c := ((0,1),0)))).congr ?_
    intro q hq
    have hRq : HasFDerivAt R (fderiv ℝ R q) q :=
      ((hR.differentiableOn (by norm_num) q hq).differentiableAt (hS.mem_nhds hq)).hasFDerivAt
    exact (hRq.comp_hasDerivAt q.1.2
      (((hasDerivAt_const q.1.2 q.1.1).prodMk (hasDerivAt_id q.1.2)).prodMk
        (hasDerivAt_const q.1.2 q.2))).deriv
  · refine (hd.clm_apply (continuousOn_const (c := ((0,0),1)))).congr ?_
    intro q hq
    have hRq : HasFDerivAt R (fderiv ℝ R q) q :=
      ((hR.differentiableOn (by norm_num) q hq).differentiableAt (hS.mem_nhds hq)).hasFDerivAt
    exact (hRq.comp_hasDerivAt q.2
      ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))).deriv

lemma radialSolution_remainder_partials_continuous (d : AngularData) (h : Hypotheses d)
    {r μ : ℝ}
    (hdom : ∀ θ ∈ Icc 0 d.T, (θ,(r,μ)) ∈ amplitudeDomain d h)
    (hcyl : ∀ θ ∈ Icc 0 d.T, ((θ,radialSolution d h θ r μ),μ) ∈ cylinder d) :
    ContinuousOn (fun θ => deriv (fun x => remainder d θ x μ)
        (radialSolution d h θ r μ)) (Icc 0 d.T) ∧
    ContinuousOn (fun θ => deriv (fun ν => remainder d θ (radialSolution d h θ r μ) ν) μ)
      (Icc 0 d.T) := by
  have hcurve : ContinuousOn (fun θ => ((θ,radialSolution d h θ r μ),μ)) (Icc 0 d.T) :=
    (continuousOn_id.prodMk (radialSolution_c2_on d h hdom).continuousOn).prodMk continuousOn_const
  have hmem : MapsTo (fun θ => ((θ,radialSolution d h θ r μ),μ)) (Icc 0 d.T)
      (d.domain ∩ {q | q.2 ∈ Ioo (-d.ε) d.ε}) := by
    intro θ hθ
    exact ⟨h.contains_cylinder (hcyl θ hθ),abs_lt.mp (hcyl θ hθ).2.2⟩
  exact ⟨(remainder_partials_continuousOn d h).1.comp hcurve hmem,
    (remainder_partials_continuousOn d h).2.comp hcurve hmem⟩


lemma exponentialIntegral_hasDerivAt {T : ℝ} (hT : 0 ≤ T) (p : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ s in 0..T, Real.exp (x*s))
      (∫ s in 0..T, s * Real.exp (p*s)) p := by
  let C : ℝ := T * Real.exp ((|p|+1)*T)
  have hF (x : ℝ) : Continuous (fun s : ℝ => Real.exp (x*s)) := by fun_prop
  have hF' (x : ℝ) : Continuous (fun s : ℝ => s * Real.exp (x*s)) := by fun_prop
  have hbd : ∀ᵐ s ∂(volume.restrict (Ioc 0 T)),
      ∀ x ∈ Metric.ball p 1, ‖s * Real.exp (x*s)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro x hx
    have hx' : |x-p| < 1 := by simpa [Real.dist_eq] using hx
    have hxp : |x| ≤ |p| + 1 := by
      calc
        |x| = |(x-p)+p| := by congr 1; ring
        _ ≤ |x-p|+|p| := abs_add_le _ _
        _ ≤ |p|+1 := by linarith
    have hexp : Real.exp (x*s) ≤ Real.exp ((|p|+1)*T) := by
      apply Real.exp_le_exp.mpr
      calc
        x*s ≤ (|p|+1)*s := mul_le_mul_of_nonneg_right ((le_abs_self x).trans hxp) hs.1.le
        _ ≤ (|p|+1)*T := mul_le_mul_of_nonneg_left hs.2 (by positivity)
    dsimp [C]
    rw [abs_mul, abs_of_nonneg hs.1.le, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hs.2 hexp (Real.exp_pos _).le hT
  have hder : ∀ᵐ s ∂(volume.restrict (Ioc 0 T)),
      ∀ x ∈ Metric.ball p 1, HasDerivAt (fun x : ℝ => Real.exp (x*s))
        (s * Real.exp (x*s)) x := by
    exact Filter.Eventually.of_forall (fun s x _ => by
      convert ((hasDerivAt_id x).mul_const s).exp using 1 <;> simp [mul_comm])
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 T)) (F := fun x s : ℝ => Real.exp (x*s))
    (F' := fun x s : ℝ => s * Real.exp (x*s)) (bound := fun _ => C)
    (Metric.ball_mem_nhds p (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun x => (hF x).aestronglyMeasurable))
    (((hF p).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    ((hF' p).aestronglyMeasurable) hbd ((continuous_const.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self) hder
  simpa only [intervalIntegral.integral_of_le hT] using h.2

lemma cubicCoefficient_hasDerivAt (d : AngularData) (h : Hypotheses d)
    {μ : ℝ} (hμ : |μ| < d.ε) :
    HasDerivAt (cubicCoefficient d)
      ((deriv d.B μ * Real.exp (d.T * d.A μ) +
        d.B μ * (d.T * deriv d.A μ * Real.exp (d.T * d.A μ))) *
          (∫ s in 0..d.T, Real.exp (2*d.A μ*s)) +
        d.B μ * Real.exp (d.T*d.A μ) *
          ((2*deriv d.A μ) * ∫ s in 0..d.T, s * Real.exp (2*d.A μ*s))) μ := by
  have hμ' : μ ∈ Ioo (-d.ε) d.ε := abs_lt.mp hμ
  have hA := ((h.smooth_A.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).contDiffAt
    (isOpen_Ioo.mem_nhds hμ')).differentiableAt_one.hasDerivAt
  have hB := ((h.smooth_B.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).contDiffAt
    (isOpen_Ioo.mem_nhds hμ')).differentiableAt_one.hasDerivAt
  have hI := (exponentialIntegral_hasDerivAt h.T_pos.le (2*d.A μ)).comp μ (hA.const_mul 2)
  have hE := (hA.const_mul d.T).exp
  convert (hB.mul hE).mul hI using 1
  · rfl
  · simp only [Pi.mul_apply,Function.comp_apply]
    ring


/-- Differentiation of a finite-interval integral from local joint continuity
of the integrand and its actual parameter derivative. No global bound is assumed. -/
lemma intervalIntegral_hasDerivAt_of_continuousOn
    {T x : ℝ} {U : Set ℝ} {F F' : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T) (hU : IsOpen U) (hx : x ∈ U)
    (hF : ContinuousOn (fun q : ℝ × ℝ => F q.2 q.1) (Icc 0 T ×ˢ U))
    (hF' : ContinuousOn (fun q : ℝ × ℝ => F' q.2 q.1) (Icc 0 T ×ˢ U))
    (hd : ∀ t ∈ Icc 0 T, ∀ y ∈ U, HasDerivAt (fun y => F y t) (F' y t) y) :
    HasDerivAt (fun y => ∫ t in 0..T, F y t) (∫ t in 0..T, F' x t) x := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let R := ε/2
  have hR : 0 < R := half_pos hε
  have hRU : Metric.closedBall x R ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hBRU : Metric.ball x R ⊆ U := Metric.ball_subset_closedBall.trans hRU
  have hKF' : ContinuousOn (fun q : ℝ × ℝ => F' q.2 q.1)
      (Icc 0 T ×ˢ Metric.closedBall x R) :=
    hF'.mono (Set.prod_mono Subset.rfl hRU)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x R)).exists_bound_of_continuousOn hKF'
  have hc (y : ℝ) (hy : y ∈ U) : ContinuousOn (F y) (Icc 0 T) :=
    hF.comp (f := fun t : ℝ => (t,y))
      (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,hy⟩)
  have hc' : ContinuousOn (F' x) (Icc 0 T) :=
    hF'.comp (f := fun t : ℝ => (t,x))
      (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,hx⟩)
  have hm : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (volume.restrict (Ioc 0 T)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact AEStronglyMeasurable.mono_set Ioc_subset_Icc_self
      ((hc y hy).aestronglyMeasurable measurableSet_Icc)
  have hb : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      ∀ y ∈ Metric.ball x R, ‖F' y t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro y hy
    exact hC (t,y) ⟨Ioc_subset_Icc_self ht,Metric.ball_subset_closedBall hy⟩
  have hd' : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      ∀ y ∈ Metric.ball x R, HasDerivAt (fun y => F y t) (F' y t) y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro y hy
    exact hd t (Ioc_subset_Icc_self ht) y (hBRU hy)
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 T)) (F := F) (F' := F') (bound := fun _ => C)
    (Metric.ball_mem_nhds x hR) hm
    ((hc x hx).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (AEStronglyMeasurable.mono_set Ioc_subset_Icc_self
      (hc'.aestronglyMeasurable measurableSet_Icc)) hb
    ((continuous_const.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self) hd'
  simpa only [intervalIntegral.integral_of_le hT] using hh.2



/-- A uniform signed-radius order estimate on an explicitly specified set. -/
def RadialOrderBound (S : Set (ℝ × (ℝ × ℝ))) (n : ℕ)
    (f : ℝ × (ℝ × ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ S, |f q| ≤ C * |q.2.1|^n

namespace RadialOrderBound
variable {S : Set (ℝ × (ℝ × ℝ))} {m n : ℕ} {f g : ℝ × (ℝ × ℝ) → ℝ}
lemma congr (hf : RadialOrderBound S n f) (he : EqOn g f S) :
    RadialOrderBound S n g := by
  rcases hf with ⟨C,hC,hf⟩
  exact ⟨C,hC,fun q hq => he hq ▸ hf q hq⟩
lemma add (hf : RadialOrderBound S n f) (hg : RadialOrderBound S n g) :
    RadialOrderBound S n (fun q => f q+g q) := by
  rcases hf with ⟨C,hC,hf⟩
  rcases hg with ⟨D,hD,hg⟩
  refine ⟨C+D,add_nonneg hC hD,fun q hq => ?_⟩
  exact (abs_add_le _ _).trans (by nlinarith [hf q hq,hg q hq])
lemma neg (hf : RadialOrderBound S n f) : RadialOrderBound S n (fun q => -f q) := by
  simpa only [RadialOrderBound,abs_neg] using hf
lemma sub (hf : RadialOrderBound S n f) (hg : RadialOrderBound S n g) :
    RadialOrderBound S n (fun q => f q-g q) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma mul (hf : RadialOrderBound S m f) (hg : RadialOrderBound S n g) :
    RadialOrderBound S (m+n) (fun q => f q*g q) := by
  rcases hf with ⟨C,hC,hf⟩
  rcases hg with ⟨D,hD,hg⟩
  refine ⟨C*D,mul_nonneg hC hD,fun q hq => ?_⟩
  rw [abs_mul]
  calc
    _ ≤ (C*|q.2.1|^m)*(D*|q.2.1|^n) :=
      mul_le_mul (hf q hq) (hg q hq) (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring
lemma pow (hf : RadialOrderBound S n f) (k : ℕ) :
    RadialOrderBound S (n*k) (fun q => f q^k) := by
  rcases hf with ⟨C,hC,hf⟩
  refine ⟨C^k,pow_nonneg hC _,fun q hq => ?_⟩
  rw [abs_pow]
  calc
    _ ≤ (C*|q.2.1|^n)^k := pow_le_pow_left₀ (abs_nonneg _) (hf q hq) k
    _ = _ := by rw [mul_pow,pow_mul]
lemma const_mul (hf : RadialOrderBound S n f) (c : ℝ) :
    RadialOrderBound S n (fun q => c*f q) := by
  rcases hf with ⟨C,hC,hf⟩
  refine ⟨|c| * C,mul_nonneg (abs_nonneg _) hC,fun q hq => ?_⟩
  rw [abs_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf q hq) (abs_nonneg _)
lemma weaken (hf : RadialOrderBound S n f) (hmn : m ≤ n)
    (hr : ∀ q ∈ S, |q.2.1| ≤ 1) : RadialOrderBound S m f := by
  rcases hf with ⟨C,hC,hf⟩
  refine ⟨C,hC,fun q hq => (hf q hq).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (abs_nonneg _) (hr q hq) hmn) hC
lemma mono (hf : RadialOrderBound S n f) {S' : Set (ℝ × (ℝ × ℝ))} (hS : S' ⊆ S) :
    RadialOrderBound S' n f := by
  rcases hf with ⟨C,hC,hf⟩
  exact ⟨C,hC,fun q hq => hf q (hS hq)⟩
lemma zero (S : Set (ℝ × (ℝ × ℝ))) (n : ℕ) : RadialOrderBound S n (fun _ => 0) :=
  ⟨0,le_rfl,by simp⟩
lemma radius (S : Set (ℝ × (ℝ × ℝ))) : RadialOrderBound S 1 (fun q => q.2.1) :=
  ⟨1,by norm_num,by simp⟩
lemma of_uniform {C : ℝ} (hC : 0 ≤ C) (hf : ∀ q ∈ S, |f q| ≤ C) :
    RadialOrderBound S 0 f := ⟨C,hC,by simpa using hf⟩

lemma weighted_integral {T δ η N : ℝ} {a : ℝ → ℝ}
    (ha : ∀ μ ∈ Ioo (-η) η, |a μ| ≤ N)
    (hf : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) n f) :
    RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) n
      (fun q => Real.exp (a q.2.2*q.1) *
        ∫ s in 0..q.1, Real.exp (-a q.2.2*s)*f (s,q.2)) := by
  rcases hf with ⟨C,hC,hf⟩
  by_cases hT : 0 ≤ T
  · refine ⟨Real.exp (N*T)^2*C*T,by positivity,?_⟩
    rintro ⟨t,r,μ⟩ ⟨ht,hp⟩
    convert weighted_integral_bound (ha μ hp.2)
      (mul_nonneg hC (pow_nonneg (abs_nonneg r) n))
      (fun s hs => hf (s,(r,μ)) ⟨hs,hp⟩) ht using 1 <;> ring
  · exact ⟨0,le_rfl,by simp [Icc_eq_empty_of_lt (lt_of_not_ge hT)]⟩
end RadialOrderBound


lemma scalar_forcing_bound {a N T D : ℝ} {y f : ℝ → ℝ}
    (hT : 0 ≤ T) (ha : |a| ≤ N) (hD : 0 ≤ D)
    (hy : ContinuousOn y (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hy0 : y 0 = 0)
    (hyd : ∀ s ∈ Icc 0 T, HasDerivWithinAt y (a*y s+f s) (Icc 0 T) s)
    (hfb : ∀ s ∈ Icc 0 T, |f s| ≤ D) :
    ∀ t ∈ Icc 0 T, |y t| ≤ Real.exp (N*T)^2 * D * T := by
  let I : D13Unified.TimeInterval := ⟨Icc 0 T,⟨0,le_rfl,hT⟩,ordConnected_Icc⟩
  have he := D13Unified.ScalarLinear.eq_variation_of_isIVP I (fun _ => a) f 0 0
    continuousOn_const hf ⟨hy,⟨le_rfl,hT⟩,hy0,hyd⟩
  intro t ht
  have hid := he ht
  have hp (s : ℝ) : D13Unified.ScalarLinear.primitive (fun _ => a) 0 s = a*s := by
    simp [D13Unified.ScalarLinear.primitive,mul_comm]
  simp only [D13Unified.ScalarLinear.variation,hp,zero_add,← Real.exp_eq_exp_ℝ] at hid
  rw [hid]
  simpa only [neg_mul] using weighted_integral_bound ha hD hfb ht





lemma radial_variation_linear_error_bound {a B M L V N T r : ℝ}
    {u v q : ℝ → ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L) (hV : 0 ≤ V) (hN : 0 ≤ N)
    (ha : |a| ≤ N) (hB : |B| ≤ N) (hr : |r| ≤ 1)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hq : ContinuousOn q (Icc 0 T)) (hv0 : v 0 = 1)
    (hvd : ∀ s ∈ Icc 0 T,
      HasDerivWithinAt v ((a+3*B*u s^2+q s)*v s) (Icc 0 T) s)
    (hub : ∀ s ∈ Icc 0 T, |u s| ≤ L*|r|)
    (hvb : ∀ s ∈ Icc 0 T, |v s| ≤ V)
    (hqb : ∀ s ∈ Icc 0 T, |q s| ≤ M*|u s|^3) :
    ∀ t ∈ Icc 0 T,
      |v t-Real.exp (a*t)| ≤
        (Real.exp (N*T)^2 * ((3*N*L^2+M*L^3)*V) * T)*|r|^2 := by
  let f : ℝ → ℝ := fun s => (3*B*u s^2+q s)*v s
  have hf : ContinuousOn f (Icc 0 T) :=
    ((continuousOn_const.mul (hu.pow 2)).add hq).mul hv
  have he : ContinuousOn (fun s : ℝ => Real.exp (a*s)) (Icc 0 T) := by fun_prop
  have hder : ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun t => v t-Real.exp (a*t))
      (a*(v s-Real.exp (a*s))+f s) (Icc 0 T) s := by
    intro s hs
    have hp := ((Real.hasDerivAt_exp (a*s)).comp s
      ((hasDerivAt_id s).const_mul a)).hasDerivWithinAt (s := Icc 0 T)
    convert! (hvd s hs).sub hp using 1 <;> dsimp [f] <;> ring
  have hpow : |r|^3 ≤ |r|^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg |r|)]
  have hfb : ∀ s ∈ Icc 0 T, |f s| ≤ ((3*N*L^2+M*L^3)*V)*|r|^2 := by
    intro s hs
    have hqu : |q s| ≤ M*L^3*|r|^3 := by
      calc
        _ ≤ M*|u s|^3 := hqb s hs
        _ ≤ M*(L*|r|)^3 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (hub s hs) 3) hM
        _ = _ := by ring
    have hq' : |q s| ≤ M*L^3*|r|^2 := hqu.trans
      (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hu2 := pow_le_pow_left₀ (abs_nonneg _) (hub s hs) 2
    have hab : |3*B*u s^2+q s| ≤ (3*N*L^2+M*L^3)*|r|^2 := by
      calc
        _ ≤ |3*B*u s^2|+|q s| := abs_add_le _ _
        _ = 3*|B| *|u s|^2+|q s| := by rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),abs_pow]
        _ ≤ 3*N*(L*|r|)^2+(M*L^3)*|r|^2 :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num)) hu2
            (sq_nonneg _) (by positivity)) hq'
        _ = _ := by ring
    calc
      |f s| = |3*B*u s^2+q s| *|v s| := abs_mul _ _
      _ ≤ ((3*N*L^2+M*L^3)*|r|^2)*V :=
        mul_le_mul hab (hvb s hs) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hb := scalar_forcing_bound hT ha
    (show 0 ≤ ((3*N*L^2+M*L^3)*V)*|r|^2 by positivity)
    (hv.sub he) hf (by simpa only [Pi.sub_apply,mul_zero,Real.exp_zero] using sub_eq_zero.mpr hv0) hder hfb
  intro t ht
  convert hb t ht using 1 <;> ring





lemma cubic_linear_coefficient_bound {B M L N r u q : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (hB : |B| ≤ N) (hr : |r| ≤ 1)
    (hu : |u| ≤ L*|r|) (hq : |q| ≤ M*|u|^3) :
    |3*B*u^2+q| ≤ (3*N*L^2+M*L^3)*|r|^2 := by
  have hpow : |r|^3 ≤ |r|^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg |r|)]
  have hqu : |q| ≤ M*L^3*|r|^3 := by
    calc
      _ ≤ M*|u|^3 := hq
      _ ≤ M*(L*|r|)^3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) hu 3) hM
      _ = _ := by ring
  have hq' : |q| ≤ M*L^3*|r|^2 := hqu.trans
    (mul_le_mul_of_nonneg_left hpow (by positivity))
  calc
    _ ≤ |3*B*u^2|+|q| := abs_add_le _ _
    _ = 3*|B| * |u|^2+|q| := by
      rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),abs_pow]
    _ ≤ 3*N*(L*|r|)^2+(M*L^3)*|r|^2 :=
      add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num))
        (pow_le_pow_left₀ (abs_nonneg _) hu 2) (sq_nonneg _) (by positivity)) hq'
    _ = _ := by ring

lemma parameter_variation_linear_error_bound {a a₁ B B₁ M L W N T r D : ℝ}
    {u w q z : ℝ → ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hN : 0 ≤ N) (hD : 0 ≤ D)
    (ha : |a| ≤ N) (ha₁ : |a₁| ≤ N) (hB : |B| ≤ N) (hB₁ : |B₁| ≤ N)
    (hr : |r| ≤ 1)
    (hu : ContinuousOn u (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hq : ContinuousOn q (Icc 0 T)) (hz : ContinuousOn z (Icc 0 T))
    (hw0 : w 0 = 0)
    (hwd : ∀ s ∈ Icc 0 T,
      HasDerivWithinAt w ((a+3*B*u s^2+q s)*w s+a₁*u s+B₁*u s^3+z s)
        (Icc 0 T) s)
    (hub : ∀ s ∈ Icc 0 T, |u s| ≤ L*|r|)
    (hwb : ∀ s ∈ Icc 0 T, |w s| ≤ W*|r|)
    (hqb : ∀ s ∈ Icc 0 T, |q s| ≤ M*|u s|^3)
    (hzb : ∀ s ∈ Icc 0 T, |z s| ≤ M*|u s|^4)
    (hlin : ∀ s ∈ Icc 0 T, |u s-Real.exp (a*s)*r| ≤ D*|r|^3) :
    ∀ t ∈ Icc 0 T,
      |w t-a₁*t*Real.exp (a*t)*r| ≤
        (Real.exp (N*T)^2 * (N*D+(3*N*L^2+M*L^3)*W+N*L^3+M*L^4) * T)*|r|^3 := by
  let p : ℝ → ℝ := fun s => a₁*s*Real.exp (a*s)*r
  let f : ℝ → ℝ := fun s => a₁*(u s-Real.exp (a*s)*r) +
    (3*B*u s^2+q s)*w s + B₁*u s^3+z s
  have he : ContinuousOn (fun s : ℝ => Real.exp (a*s)*r) (Icc 0 T) := by fun_prop
  have hp : ContinuousOn p (Icc 0 T) := by dsimp [p]; fun_prop
  have hf : ContinuousOn f (Icc 0 T) :=
    (((continuousOn_const.mul (hu.sub he)).add
      (((continuousOn_const.mul (hu.pow 2)).add hq).mul hw)).add
      (continuousOn_const.mul (hu.pow 3))).add hz
  have hder : ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun t => w t-p t)
      (a*(w s-p s)+f s) (Icc 0 T) s := by
    intro s hs
    have hp' : HasDerivWithinAt p (a*p s+a₁*(Real.exp (a*s)*r)) (Icc 0 T) s := by
      have hex := (Real.hasDerivAt_exp (a*s)).comp s ((hasDerivAt_id s).const_mul a)
      convert! ((((hasDerivAt_id s).const_mul a₁).mul hex).mul_const r).hasDerivWithinAt
        (s := Icc 0 T) using 1 <;> dsimp [p] <;> ring
    convert! (hwd s hs).sub hp' using 1 <;> dsimp [f] <;> ring
  have hpow : |r|^4 ≤ |r|^3 := by
    nlinarith [mul_le_mul_of_nonneg_left hr (pow_nonneg (abs_nonneg r) 3)]
  have hfb : ∀ s ∈ Icc 0 T,
      |f s| ≤ (N*D+(3*N*L^2+M*L^3)*W+N*L^3+M*L^4)*|r|^3 := by
    intro s hs
    have h₁ : |a₁*(u s-Real.exp (a*s)*r)| ≤ N*D*|r|^3 := by
      rw [abs_mul]
      convert mul_le_mul ha₁ (hlin s hs) (abs_nonneg _) hN using 1 <;> ring
    have h₂ : |(3*B*u s^2+q s)*w s| ≤ (3*N*L^2+M*L^3)*W*|r|^3 := by
      rw [abs_mul]
      convert mul_le_mul (cubic_linear_coefficient_bound hM hL hN hB hr
        (hub s hs) (hqb s hs)) (hwb s hs) (abs_nonneg _) (by positivity) using 1 <;> ring
    have h₃ : |B₁*u s^3| ≤ N*L^3*|r|^3 := by
      rw [abs_mul,abs_pow]
      convert mul_le_mul hB₁ (pow_le_pow_left₀ (abs_nonneg _) (hub s hs) 3)
        (pow_nonneg (abs_nonneg _) _) hN using 1 <;> ring
    have h₄ : |z s| ≤ M*L^4*|r|^3 := by
      calc
        _ ≤ M*|u s|^4 := hzb s hs
        _ ≤ M*(L*|r|)^4 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (hub s hs) 4) hM
        _ = M*L^4*|r|^4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
    dsimp [f]
    calc
      _ ≤ |a₁*(u s-Real.exp (a*s)*r)+(3*B*u s^2+q s)*w s+B₁*u s^3|+|z s| :=
        abs_add_le _ _
      _ ≤ |a₁*(u s-Real.exp (a*s)*r)|+|(3*B*u s^2+q s)*w s|+|B₁*u s^3|+|z s| :=
        add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl
      _ ≤ N*D*|r|^3+(3*N*L^2+M*L^3)*W*|r|^3+N*L^3*|r|^3+M*L^4*|r|^3 :=
        add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
      _ = _ := by ring
  have hb := scalar_forcing_bound hT ha
    (show 0 ≤ (N*D+(3*N*L^2+M*L^3)*W+N*L^3+M*L^4)*|r|^3 by positivity)
    (hw.sub hp) hf (by simpa [p] using hw0) hder hfb
  intro t ht
  convert hb t ht using 1 <;> ring





set_option maxHeartbeats 800000 in
lemma radialSolution_remainder_partials_joint_continuous (d : AngularData) (h : Hypotheses d)
    {S : Set (ℝ × (ℝ × ℝ))} (hdom : S ⊆ amplitudeDomain d h)
    (hcyl : ∀ q ∈ S,
      ((q.1,radialSolution d h q.1 q.2.1 q.2.2),q.2.2) ∈ cylinder d) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => deriv (fun x => remainder d q.1 x q.2.2)
        (radialSolution d h q.1 q.2.1 q.2.2)) S ∧
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      deriv (fun ν => remainder d q.1 (radialSolution d h q.1 q.2.1 q.2.2) ν) q.2.2) S := by
  have hu : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => radialSolution d h q.1 q.2.1 q.2.2) S :=
    continuousOn_snd.fst.mul ((amplitude_c2 d h).2.continuousOn.mono hdom)
  have hcurve : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      ((q.1,radialSolution d h q.1 q.2.1 q.2.2),q.2.2)) S :=
    (continuousOn_fst.prodMk hu).prodMk continuousOn_snd.snd
  have hmem : MapsTo (fun q : ℝ × (ℝ × ℝ) =>
      ((q.1,radialSolution d h q.1 q.2.1 q.2.2),q.2.2)) S
      (d.domain ∩ {q | q.2 ∈ Ioo (-d.ε) d.ε}) := by
    intro q hq
    exact ⟨h.contains_cylinder (hcyl q hq),abs_lt.mp (hcyl q hq).2.2⟩
  exact ⟨(remainder_partials_continuousOn d h).1.comp hcurve hmem,
    (remainder_partials_continuousOn d h).2.comp hcurve hmem⟩


lemma cubic_response_hasDerivAt (a B t : ℝ) :
    HasDerivAt (fun t : ℝ => B*Real.exp (a*t)*∫ s in 0..t, Real.exp (2*a*s))
      (a*(B*Real.exp (a*t)*∫ s in 0..t, Real.exp (2*a*s))+
        B*Real.exp (a*t)^3) t := by
  have hc : Continuous (fun s : ℝ => Real.exp (2*a*s)) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he := (Real.hasDerivAt_exp (a*t)).comp t ((hasDerivAt_id t).const_mul a)
  have hpow : Real.exp (a*t)*Real.exp (2*a*t) = Real.exp (a*t)^3 := by
    rw [← Real.exp_add,← Real.exp_nat_mul]
    congr 1
    ring
  convert! (he.const_mul B).mul hi using 1
  simp only [Function.comp_apply,mul_one]
  rw [← hpow]
  ring

lemma abs_square_sub_le {x y R S D : ℝ} (hR : 0 ≤ R)
    (hx : |x| ≤ R) (hy : |y| ≤ S) (hxy : |x-y| ≤ D) :
    |x^2-y^2| ≤ D*(R+S) := by
  rw [show x^2-y^2=(x-y)*(x+y) by ring,abs_mul]
  exact mul_le_mul hxy ((abs_add_le _ _).trans (add_le_add hx hy))
    (abs_nonneg _) ((abs_nonneg _).trans hxy)

lemma radial_variation_cubic_error_bound {a B M L V N T r D J : ℝ}
    {u v q k : ℝ → ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hN : 0 ≤ N) (hD : 0 ≤ D) (hJ : 0 ≤ J)
    (ha : |a| ≤ N) (hB : |B| ≤ N) (hr : |r| ≤ 1)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hq : ContinuousOn q (Icc 0 T)) (hk : ContinuousOn k (Icc 0 T))
    (hv0 : v 0 = 1) (hk0 : k 0 = 0)
    (hvd : ∀ s ∈ Icc 0 T,
      HasDerivWithinAt v ((a+3*B*u s^2+q s)*v s) (Icc 0 T) s)
    (hkd : ∀ s ∈ Icc 0 T,
      HasDerivWithinAt k (a*k s+B*Real.exp (a*s)^3) (Icc 0 T) s)
    (hub : ∀ s ∈ Icc 0 T, |u s| ≤ L*|r|)
    (hvb : ∀ s ∈ Icc 0 T, |v s| ≤ V)
    (hqb : ∀ s ∈ Icc 0 T, |q s| ≤ M*|u s|^3)
    (hlin : ∀ s ∈ Icc 0 T, |u s-Real.exp (a*s)*r| ≤ D*|r|^3)
    (hvlin : ∀ s ∈ Icc 0 T, |v s-Real.exp (a*s)| ≤ J*|r|^2) :
    let H := Real.exp (N*T)
    ∀ t ∈ Icc 0 T,
      |v t-Real.exp (a*t)-3*k t*r^2| ≤
        (H^2 * (3*N*(L^2*J+D*(L+H)*H)+M*L^3*V) * T)*|r|^3 := by
  let H := Real.exp (N*T)
  have hH : 0 ≤ H := (Real.exp_pos _).le
  let e : ℝ → ℝ := fun s => v s-Real.exp (a*s)-3*k s*r^2
  let f : ℝ → ℝ := fun s => 3*B*(u s^2*v s-Real.exp (a*s)^3*r^2)+q s*v s
  have hp : ContinuousOn (fun s : ℝ => Real.exp (a*s)) (Icc 0 T) := by fun_prop
  have he : ContinuousOn e (Icc 0 T) := (hv.sub hp).sub
    ((continuousOn_const.mul hk).mul continuousOn_const)
  have hf : ContinuousOn f (Icc 0 T) :=
    (continuousOn_const.mul ((hu.pow 2).mul hv |>.sub
      ((hp.pow 3).mul continuousOn_const))).add (hq.mul hv)
  have he0 : e 0 = 0 := by simp [e,hv0,hk0]
  have hed : ∀ s ∈ Icc 0 T, HasDerivWithinAt e (a*e s+f s) (Icc 0 T) s := by
    intro s hs
    have hpd := ((Real.hasDerivAt_exp (a*s)).comp s
      ((hasDerivAt_id s).const_mul a)).hasDerivWithinAt (s := Icc 0 T)
    convert! ((hvd s hs).sub hpd).sub (((hkd s hs).const_mul 3).mul_const (r^2)) using 1 <;>
      dsimp [e,f] <;> ring
  have hpow : |r|^4 ≤ |r|^3 := by
    nlinarith [mul_le_mul_of_nonneg_left hr (pow_nonneg (abs_nonneg r) 3)]
  have hfb : ∀ s ∈ Icc 0 T,
      |f s| ≤ (3*N*(L^2*J+D*(L+H)*H)+M*L^3*V)*|r|^3 := by
    intro s hs
    have hpabs : |Real.exp (a*s)| ≤ H := (exponential_bounds ha hs).1
    have hu0 : |Real.exp (a*s)*r| ≤ H*|r| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hpabs (abs_nonneg _)
    have hsquare : |u s^2-(Real.exp (a*s)*r)^2| ≤ D*(L+H)*|r|^4 := by
      convert abs_square_sub_le (mul_nonneg hL (abs_nonneg r))
        (hub s hs) hu0 (hlin s hs) using 1 <;> ring
    have hx : |u s^2*(v s-Real.exp (a*s))| ≤ L^2*J*|r|^4 := by
      rw [abs_mul,abs_pow]
      convert mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hub s hs) 2)
        (hvlin s hs) (abs_nonneg _) (by positivity) using 1 <;> ring
    have hy : |(u s^2-(Real.exp (a*s)*r)^2)*Real.exp (a*s)| ≤ D*(L+H)*H*|r|^4 := by
      rw [abs_mul]
      convert mul_le_mul hsquare hpabs (abs_nonneg _) (by positivity) using 1 <;> ring
    have hcv : |u s^2*v s-Real.exp (a*s)^3*r^2| ≤
        (L^2*J+D*(L+H)*H)*|r|^4 := by
      calc
        _ = |u s^2*(v s-Real.exp (a*s))+
            (u s^2-(Real.exp (a*s)*r)^2)*Real.exp (a*s)| := by congr 1; ring
        _ ≤ |u s^2*(v s-Real.exp (a*s))|+
            |(u s^2-(Real.exp (a*s)*r)^2)*Real.exp (a*s)| := abs_add_le _ _
        _ ≤ L^2*J*|r|^4+D*(L+H)*H*|r|^4 := add_le_add hx hy
        _ = _ := by ring
    have hmain : |3*B*(u s^2*v s-Real.exp (a*s)^3*r^2)| ≤
        3*N*(L^2*J+D*(L+H)*H)*|r|^3 := by
      calc
        _ = 3*|B| * |u s^2*v s-Real.exp (a*s)^3*r^2| := by
          rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)]
        _ ≤ 3*N*((L^2*J+D*(L+H)*H)*|r|^4) := mul_le_mul
          (mul_le_mul_of_nonneg_left hB (by norm_num)) hcv (abs_nonneg _) (by positivity)
        _ = (3*N*(L^2*J+D*(L+H)*H))*|r|^4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
    have hrem : |q s*v s| ≤ M*L^3*V*|r|^3 := by
      rw [abs_mul]
      have hqu : |q s| ≤ M*(L*|r|)^3 := (hqb s hs).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hub s hs) 3) hM)
      convert mul_le_mul hqu (hvb s hs) (abs_nonneg _) (by positivity) using 1 <;> ring
    exact (abs_add_le _ _).trans ((add_le_add hmain hrem).trans_eq (by ring))
  have hb := scalar_forcing_bound hT ha
    (show 0 ≤ (3*N*(L^2*J+D*(L+H)*H)+M*L^3*V)*|r|^3 by positivity)
    he hf he0 hed hfb
  dsimp only
  intro t ht
  convert hb t ht using 1 <;> ring




lemma radialSolution_parameter_derivatives_continuous (d : AngularData) (h : Hypotheses d) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      deriv (fun r => radialSolution d h q.1 r q.2.2) q.2.1) (amplitudeDomain d h) ∧
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      deriv (fun μ => radialSolution d h q.1 q.2.1 μ) q.2.2) (amplitudeDomain d h) := by
  let U := fun q : ℝ × (ℝ × ℝ) => radialSolution d h q.1 q.2.1 q.2.2
  have hS : IsOpen (amplitudeDomain d h) := (amplitude_c2 d h).1
  have hU : ContDiffOn ℝ 2 U (amplitudeDomain d h) :=
    contDiffOn_snd.fst.mul (amplitude_c2 d h).2
  have hd : ContinuousOn (fderiv ℝ U) (amplitudeDomain d h) :=
    hU.continuousOn_fderiv_of_isOpen hS (by norm_num)
  constructor
  · refine (hd.clm_apply (continuousOn_const (c := (0,(1,0))))).congr ?_
    intro q hq
    have hUq : HasFDerivAt U (fderiv ℝ U q) q :=
      ((hU.differentiableOn (by norm_num) q hq).differentiableAt (hS.mem_nhds hq)).hasFDerivAt
    exact (hUq.comp_hasDerivAt q.2.1
      ((hasDerivAt_const q.2.1 q.1).prodMk
        ((hasDerivAt_id q.2.1).prodMk (hasDerivAt_const q.2.1 q.2.2)))).deriv
  · refine (hd.clm_apply (continuousOn_const (c := (0,(0,1))))).congr ?_
    intro q hq
    have hUq : HasFDerivAt U (fderiv ℝ U q) q :=
      ((hU.differentiableOn (by norm_num) q hq).differentiableAt (hS.mem_nhds hq)).hasFDerivAt
    exact (hUq.comp_hasDerivAt q.2.2
      ((hasDerivAt_const q.2.2 q.1).prodMk
        ((hasDerivAt_const q.2.2 q.2.1).prodMk (hasDerivAt_id q.2.2)))).deriv


lemma remainder_hasDerivAt_curve (d : AngularData) (h : Hypotheses d)
    {s ν w : ℝ} {u : ℝ → ℝ}
    (hq : ((s,u ν),ν) ∈ d.domain) (hν : |ν| < d.ε) (hu : HasDerivAt u w ν) :
    HasDerivAt (fun μ => remainder d s (u μ) μ)
      (deriv (fun x => remainder d s x ν) (u ν) * w +
        deriv (fun μ => remainder d s (u ν) μ) ν) ν := by
  let R := fun q : (ℝ × ℝ) × ℝ => remainder d q.1.1 q.1.2 q.2
  let S : Set ((ℝ × ℝ) × ℝ) := d.domain ∩ {q | q.2 ∈ Ioo (-d.ε) d.ε}
  have hS : IsOpen S := h.open_domain.inter (isOpen_Ioo.preimage continuous_snd)
  have hR : ContDiffOn ℝ 2 R S := remainder_c2_on_strip d h
  have hqS : ((s,u ν),ν) ∈ S := ⟨hq,abs_lt.mp hν⟩
  have hRq : HasFDerivAt R (fderiv ℝ R ((s,u ν),ν)) ((s,u ν),ν) :=
    ((hR.differentiableOn (by norm_num) _ hqS).differentiableAt (hS.mem_nhds hqS)).hasFDerivAt
  have hdx : deriv (fun x => remainder d s x ν) (u ν) =
      fderiv ℝ R ((s,u ν),ν) ((0,1),0) :=
    (hRq.comp_hasDerivAt (f := fun x : ℝ => ((s,x),ν)) (u ν)
      (((hasDerivAt_const (u ν) s).prodMk (hasDerivAt_id (u ν))).prodMk
        (hasDerivAt_const (u ν) ν))).deriv
  have hdμ : deriv (fun μ => remainder d s (u ν) μ) ν =
      fderiv ℝ R ((s,u ν),ν) ((0,0),1) :=
    (hRq.comp_hasDerivAt (f := fun μ : ℝ => ((s,u ν),μ)) ν
      ((hasDerivAt_const ν (s,u ν)).prodMk (hasDerivAt_id ν))).deriv
  have hd := hRq.comp_hasDerivAt (f := fun μ : ℝ => ((s,u μ),μ)) ν
    (((hasDerivAt_const ν s).prodMk hu).prodMk (hasDerivAt_id ν))
  have hdir : ((0,w),1) = w • (((0,1),0) : (ℝ × ℝ) × ℝ) + ((0,0),1) := by
    ext <;> simp
  change HasDerivAt (fun μ => remainder d s (u μ) μ)
    (fderiv ℝ R ((s,u ν),ν) ((0,w),1)) ν at hd
  rw [hdir,map_add,map_smul,← hdx,← hdμ] at hd
  simpa only [smul_eq_mul,mul_comm w] using hd


set_option maxHeartbeats 1000000 in
lemma common_uniform_data (d : AngularData) (h : Hypotheses d)
    {δ η L C a b : ℝ}
    (he : Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ η L a b)
    (hE : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => endpointError d h p.1 p.2) (parameterBox δ η))
    (hEb : ∀ r μ, (r,μ) ∈ parameterBox δ η → |endpointError d h r μ| ≤ C*|r|^4) :
    ∃ δ' η' N V W : ℝ,
      0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ 1 ∧ 0 < η' ∧ η' ≤ η ∧
      0 ≤ N ∧ 0 ≤ V ∧ 0 ≤ W ∧
      Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ' η' L a b ∧
      ContDiffOn ℝ 2 (fun p : ℝ × ℝ => endpointError d h p.1 p.2) (parameterBox δ' η') ∧
      (∀ r μ, (r,μ) ∈ parameterBox δ' η' → |endpointError d h r μ| ≤ C*|r|^4) ∧
      (∀ μ, |μ| < η' →
        |d.A μ| ≤ N ∧ |d.B μ| ≤ N ∧ |deriv d.A μ| ≤ N ∧ |deriv d.B μ| ≤ N) ∧
      (∀ r μ, (r,μ) ∈ parameterBox δ' η' → ∀ θ ∈ Icc 0 d.T,
        |deriv (fun x => radialSolution d h θ x μ) r| ≤ V ∧
        |deriv (fun ν => radialSolution d h θ r ν) μ| ≤ W*|r|) := by
  obtain ⟨δ₁,η₁,V,W,hδ₁,hδ₁δ,hδ₁one,hη₁,hη₁η,hV,hW,hvw⟩ :=
    uniform_first_derivative_bounds d h he
  let η' := η₁/2
  have hη' : 0 < η' := half_pos hη₁
  have hη'η₁ : η' ≤ η₁ := (half_lt_self hη₁).le
  have hη'η : η' ≤ η := hη'η₁.trans hη₁η
  have hbox : parameterBox δ₁ η' ⊆ parameterBox δ η := parameterBox_mono hδ₁δ hη'η
  have hbox₁ : parameterBox δ₁ η' ⊆ parameterBox δ₁ η₁ :=
    parameterBox_mono le_rfl hη'η₁
  have hηε : η < d.ε := he.2.2.2.1
  have hη'ε : η' < d.ε := hη'η.trans_lt hηε
  have hstrip : Icc (-η') η' ⊆ Ioo (-d.ε) d.ε := by
    intro μ hμ
    exact ⟨(neg_lt_neg hη'ε).trans_le hμ.1,hμ.2.trans_lt hη'ε⟩
  have hdA : ContinuousOn (deriv d.A) (Ioo (-d.ε) d.ε) := by
    simpa only [fderiv_apply_one_eq_deriv] using
      (h.smooth_A.continuousOn_fderiv_of_isOpen isOpen_Ioo (by norm_num)).clm_apply
        (continuousOn_const (c := (1 : ℝ)))
  have hdB : ContinuousOn (deriv d.B) (Ioo (-d.ε) d.ε) := by
    simpa only [fderiv_apply_one_eq_deriv] using
      (h.smooth_B.continuousOn_fderiv_of_isOpen isOpen_Ioo (by norm_num)).clm_apply
        (continuousOn_const (c := (1 : ℝ)))
  obtain ⟨NA,hNA⟩ := isCompact_Icc.exists_bound_of_continuousOn (h.smooth_A.continuousOn.mono hstrip)
  obtain ⟨NB,hNB⟩ := isCompact_Icc.exists_bound_of_continuousOn (h.smooth_B.continuousOn.mono hstrip)
  obtain ⟨NDA,hNDA⟩ := isCompact_Icc.exists_bound_of_continuousOn (hdA.mono hstrip)
  obtain ⟨NDB,hNDB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hdB.mono hstrip)
  let N := max (max (max NA NB) (max NDA NDB)) 0
  have hN : 0 ≤ N := le_max_right _ _
  have hN₁ : NA ≤ N := (le_max_left NA NB).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hN₂ : NB ≤ N := (le_max_right NA NB).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hN₃ : NDA ≤ N := (le_max_left NDA NDB).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hN₄ : NDB ≤ N := (le_max_right NDA NDB).trans ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨δ₁,η',N,V,W,hδ₁,hδ₁δ,hδ₁one,hη',hη'η,hN,hV,hW,
    evolutionOnBox_shrink d h he hδ₁ hη' hδ₁δ hη'η,hE.mono hbox,
    fun r μ hp => hEb r μ (hbox hp),?_,?_⟩
  · intro μ hμ
    have hμclosed : μ ∈ Icc (-η') η' := ⟨(abs_lt.mp hμ).1.le,(abs_lt.mp hμ).2.le⟩
    exact ⟨(hNA μ hμclosed).trans hN₁,(hNB μ hμclosed).trans hN₂,
      (hNDA μ hμclosed).trans hN₃,(hNDB μ hμclosed).trans hN₄⟩
  · intro r μ hp
    exact hvw r μ (hbox₁ hp)


namespace RadialOrderBound
variable {S : Set (ℝ × (ℝ × ℝ))} {u p w z : ℝ × (ℝ × ℝ) → ℝ}

lemma square_difference (hu : RadialOrderBound S 1 u) (hp : RadialOrderBound S 1 p)
    (hd : RadialOrderBound S 3 (fun q => u q-p q)) :
    RadialOrderBound S 4 (fun q => u q^2-p q^2) := by
  apply (hd.mul (hu.add hp)).congr
  intro q _
  dsimp
  ring

lemma cubic_difference (hu : RadialOrderBound S 1 u) (hp : RadialOrderBound S 1 p)
    (hd : RadialOrderBound S 3 (fun q => u q-p q)) :
    RadialOrderBound S 5 (fun q => u q^3-p q^3) := by
  have h₂ : RadialOrderBound S 2 (fun q => u q^2+u q*p q+p q^2) :=
    ((hu.pow 2).add (hu.mul hp)).add (hp.pow 2)
  apply (hd.mul h₂).congr
  intro q _
  dsimp
  ring

lemma cubic_variation_difference (hu : RadialOrderBound S 1 u)
    (hp : RadialOrderBound S 1 p) (hz : RadialOrderBound S 1 z)
    (hud : RadialOrderBound S 3 (fun q => u q-p q))
    (hwd : RadialOrderBound S 3 (fun q => w q-z q)) :
    RadialOrderBound S 5 (fun q => u q^2*w q-p q^2*z q) := by
  have h₁ := (hu.pow 2).mul hwd
  have h₂ := (square_difference hu hp hud).mul hz
  apply (h₁.add h₂).congr
  intro q _
  dsimp
  ring

/-- Algebra and a compact integrating factor preserve the parameter error's
fourth order once the actual differentiated identity has been established. -/
lemma parameter_residual
    {T δ η N : ℝ} {a : ℝ → ℝ}
    {ap b bp e hm hr hμ eμ : ℝ × (ℝ × ℝ) → ℝ}
    (hT : 0 ≤ T)
    (hsmall : ∀ q ∈ Icc 0 T ×ˢ parameterBox δ η, |q.2.1| ≤ 1)
    (ha : ∀ μ ∈ Ioo (-η) η, |a μ| ≤ N)
    (hap : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 0 ap)
    (hb : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 0 b)
    (hbp : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 0 bp)
    (hu : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 1 u)
    (hp : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 1 p)
    (hw : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 1 w)
    (hz : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 1 z)
    (hud : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 3 (fun q => u q-p q))
    (hwd : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 3 (fun q => w q-z q))
    (he : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 4 e)
    (hhm : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 4 hm)
    (hhr : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 3 hr)
    (hhμ : RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 4 hμ)
    (hid : ∀ q ∈ Icc 0 T ×ˢ parameterBox δ η,
      eμ q = ap q*T*e q + Real.exp (a q.2.2*T) *
        ∫ s in 0..T, Real.exp (-a q.2.2*s) *
          (-(ap (s,q.2)*s) *
              (b (s,q.2)*(u (s,q.2)^3-p (s,q.2)^3)+hm (s,q.2)) +
            bp (s,q.2)*(u (s,q.2)^3-p (s,q.2)^3) +
            3*b (s,q.2)*(u (s,q.2)^2*w (s,q.2)-p (s,q.2)^2*z (s,q.2)) +
            hr (s,q.2)*w (s,q.2)+hμ (s,q.2))) :
    RadialOrderBound (Icc 0 T ×ˢ parameterBox δ η) 4 eμ := by
  let S := Icc 0 T ×ˢ parameterBox δ η
  have ht : RadialOrderBound S 0 (fun q => q.1) :=
    of_uniform hT (fun q hq => by simpa only [abs_of_nonneg hq.1.1] using hq.1.2)
  have hcube := (cubic_difference hu hp hud).weaken (show 4 ≤ 5 by decide) hsmall
  have hcvar := (cubic_variation_difference hu hp hz hud hwd).weaken
    (show 4 ≤ 5 by decide) hsmall
  have hf : RadialOrderBound S 4 (fun q =>
      -(ap q*q.1)*(b q*(u q^3-p q^3)+hm q) +
        bp q*(u q^3-p q^3)+3*b q*(u q^2*w q-p q^2*z q)+hr q*w q+hμ q) := by
    exact ((((hap.mul ht).neg.mul ((hb.mul hcube).add hhm)).add
      (hbp.mul hcube) |>.add ((hb.const_mul 3).mul hcvar) |>.add
      (hhr.mul hw)).add hhμ)
  have hi := hf.weighted_integral ha
  rcases hi with ⟨C,hC,hi⟩
  have hiT : RadialOrderBound S 4 (fun q => Real.exp (a q.2.2*T) *
      ∫ s in 0..T, Real.exp (-a q.2.2*s) *
        (-(ap (s,q.2)*s)*(b (s,q.2)*(u (s,q.2)^3-p (s,q.2)^3)+hm (s,q.2)) +
          bp (s,q.2)*(u (s,q.2)^3-p (s,q.2)^3)+
          3*b (s,q.2)*(u (s,q.2)^2*w (s,q.2)-p (s,q.2)^2*z (s,q.2)) +
          hr (s,q.2)*w (s,q.2)+hμ (s,q.2))) :=
    ⟨C,hC,fun q hq => hi (T,q.2) ⟨⟨hT,le_rfl⟩,hq.2⟩⟩
  apply (((hap.mul he).const_mul T).add hiT).congr
  intro q hq
  rw [hid q hq]
  dsimp
  ring
end RadialOrderBound


lemma endpointError_radius_bound (d : AngularData) (h : Hypotheses d)
    {δ η L a b r μ N V : ℝ}
    (he : Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ η L a b)
    (hδ : δ ≤ 1) (hp : (r,μ) ∈ parameterBox δ η)
    (hN : 0 ≤ N) (hV : 0 ≤ V) (hA : |d.A μ| ≤ N) (hB : |d.B μ| ≤ N)
    (hvb : ∀ θ ∈ Icc 0 d.T,
      |deriv (fun x => radialSolution d h θ x μ) r| ≤ V) :
    let H := Real.exp (N*d.T)
    let D := H^2*(N*L^3+d.M*L^4)*d.T
    let J := H^2*((3*N*L^2+d.M*L^3)*V)*d.T
    |deriv (fun x => endpointError d h x μ) r| ≤
      (H^2*(3*N*(L^2*J+D*(L+H)*H)+d.M*L^3*V)*d.T)*|r|^3 := by
  rcases he with ⟨hd,hdρ,hη,hηε,hL,ha,hb,hLδ,hdom,hY,hev,hzero,hQ,hfact⟩
  let H := Real.exp (N*d.T)
  let D := H^2*(N*L^3+d.M*L^4)*d.T
  let J := H^2*((3*N*L^2+d.M*L^3)*V)*d.T
  let u : ℝ → ℝ := fun θ => radialSolution d h θ r μ
  let v : ℝ → ℝ := fun θ => deriv (fun x => radialSolution d h θ x μ) r
  let q : ℝ → ℝ := fun θ => deriv (fun x => remainder d θ x μ) (u θ)
  let k : ℝ → ℝ := fun θ => d.B μ*Real.exp (d.A μ*θ)*
    ∫ s in 0..θ, Real.exp (2*d.A μ*s)
  have hI : ∀ θ ∈ Icc 0 d.T, θ ∈ Ioo a b :=
    fun θ hθ => ⟨ha.trans_le hθ.1,hθ.2.trans_lt hb⟩
  have hb0 : 0 < b := h.T_pos.trans hb
  have hdom' : ∀ θ ∈ Icc 0 d.T, (θ,(r,μ)) ∈ amplitudeDomain d h :=
    fun θ hθ => hdom ⟨hI θ hθ,hp⟩
  have hμ : |μ| < d.ε := (abs_lt.mpr hp.2).trans hηε
  have hub := (hev r μ hp).2.2.2
  have hcyl : ∀ θ ∈ Icc 0 d.T, ((θ,u θ),μ) ∈ cylinder d :=
    fun θ hθ => ⟨hθ,(hub θ hθ).2.1,hμ⟩
  have hvd : ∀ θ ∈ Icc 0 d.T,
      HasDerivAt v ((d.A μ+3*d.B μ*u θ^2+q θ)*v θ) θ := by
    intro θ hθ
    exact (radialSolution_variation_equations d h ha hb0 hdom
      (hI θ hθ) hp (hcyl θ hθ)).1
  have hu : ContinuousOn u (Icc 0 d.T) := (radialSolution_c2_on d h hdom').continuousOn
  have hv : ContinuousOn v (Icc 0 d.T) := fun θ hθ =>
    (hvd θ hθ).continuousAt.continuousWithinAt
  have hq : ContinuousOn q (Icc 0 d.T) :=
    (radialSolution_remainder_partials_continuous d h hdom' hcyl).1
  have hk : ContinuousOn k (Icc 0 d.T) := fun θ _ =>
    (cubic_response_hasDerivAt (d.A μ) (d.B μ) θ).continuousAt.continuousWithinAt
  have hv0 : v 0 = 1 := (radialSolution_variation_initial d h ha hb0 hdom hp).1
  have hk0 : k 0 = 0 := by simp [k]
  have hqb : ∀ θ ∈ Icc 0 d.T, |q θ| ≤ d.M*|u θ|^3 :=
    fun θ hθ => (h.remainder_bounds ((θ,u θ),μ) (hcyl θ hθ)).2.1
  have hr : |r| ≤ 1 := (abs_lt.mpr hp.1).le.trans hδ
  have hlin : ∀ θ ∈ Icc 0 d.T, |u θ-Real.exp (d.A μ*θ)*r| ≤ D*|r|^3 :=
    radialSolution_linear_error_bound d h hL.le hN hr hμ hA hB hdom'
      (fun θ hθ => ⟨(hub θ hθ).1,(hub θ hθ).2.1⟩)
  have hvlin : ∀ θ ∈ Icc 0 d.T, |v θ-Real.exp (d.A μ*θ)| ≤ J*|r|^2 :=
    radial_variation_linear_error_bound h.T_pos.le h.bound_nonneg hL.le hV hN
      hA hB hr hu hv hq hv0 (fun θ hθ => (hvd θ hθ).hasDerivWithinAt)
      (fun θ hθ => (hub θ hθ).1) hvb hqb
  have hH : 0 ≤ H := (Real.exp_pos _).le
  have hM := h.bound_nonneg
  have hT := h.T_pos.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hres := radial_variation_cubic_error_bound hT hM hL.le hV hN hD hJ
    hA hB hr hu hv hq hk hv0 hk0
    (fun θ hθ => (hvd θ hθ).hasDerivWithinAt)
    (fun θ _ => (cubic_response_hasDerivAt (d.A μ) (d.B μ) θ).hasDerivWithinAt)
    (fun θ hθ => (hub θ hθ).1) hvb hqb hlin hvlin d.T ⟨hT,le_rfl⟩
  have hfirst := radialSolution_first_derivatives d h ha hb0 hdom
    (hI d.T ⟨hT,le_rfl⟩) hp
  have hE : HasDerivAt (fun x => endpointError d h x μ)
      (v d.T-Real.exp (d.T*d.A μ)-3*cubicCoefficient d μ*r^2) r := by
    have hh := (hfirst.1.differentiableAt.hasDerivAt.sub
      ((hasDerivAt_id r).const_mul (Real.exp (d.T*d.A μ)))).sub
      (((hasDerivAt_id r).pow 3).const_mul (cubicCoefficient d μ))
    convert! hh using 1 <;> dsimp [endpointError,endpoint,v] <;> ring
  rw [hE.deriv]
  dsimp only
  convert hres using 1 <;> dsimp [k,cubicCoefficient,H,D,J] <;>
    simp only [mul_comm d.T (d.A μ)] <;> ring



lemma radialSolution_parameter_linear_error_bound (d : AngularData) (h : Hypotheses d)
    {δ η L a b N W r μ : ℝ}
    (he : Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ η L a b)
    (hN : 0 ≤ N) (hW : 0 ≤ W) (hp : (r,μ) ∈ parameterBox δ η) (hr : |r| ≤ 1)
    (hA : |d.A μ| ≤ N) (hB : |d.B μ| ≤ N)
    (hA' : |deriv d.A μ| ≤ N) (hB' : |deriv d.B μ| ≤ N)
    (hwb : ∀ θ ∈ Icc 0 d.T,
      |deriv (fun ν => radialSolution d h θ r ν) μ| ≤ W*|r|) :
    let H := Real.exp (N*d.T)
    let D := H^2*(N*L^3+d.M*L^4)*d.T
    let J := H^2*(N*D+(3*N*L^2+d.M*L^3)*W+N*L^3+d.M*L^4)*d.T
    ∀ θ ∈ Icc 0 d.T,
      |deriv (fun ν => radialSolution d h θ r ν) μ -
        deriv d.A μ*θ*Real.exp (d.A μ*θ)*r| ≤ J*|r|^3 := by
  rcases he with ⟨hδ,hδρ,hη,hηε,hL,ha,hb,hLδ,hdom,hY,hev,hzero,hQ,hfact⟩
  let H := Real.exp (N*d.T)
  let D := H^2*(N*L^3+d.M*L^4)*d.T
  have hM := h.bound_nonneg
  have hT := h.T_pos.le
  have hD : 0 ≤ D := by dsimp [D,H]; positivity
  have hθJ : ∀ θ ∈ Icc 0 d.T, θ ∈ Ioo a b :=
    fun θ hθ => ⟨ha.trans_le hθ.1,hθ.2.trans_lt hb⟩
  have hdomI : ∀ θ ∈ Icc 0 d.T, (θ,(r,μ)) ∈ amplitudeDomain d h :=
    fun θ hθ => hdom ⟨hθJ θ hθ,hp⟩
  have hu := (hev r μ hp).2.2.2
  have hμ : |μ| < d.ε := (abs_lt.mpr hp.2).trans hηε
  have hcyl : ∀ θ ∈ Icc 0 d.T,
      ((θ,radialSolution d h θ r μ),μ) ∈ cylinder d :=
    fun θ hθ => ⟨hθ,(hu θ hθ).2.1,hμ⟩
  have huc : ContinuousOn (fun θ => radialSolution d h θ r μ) (Icc 0 d.T) :=
    (radialSolution_c2_on d h hdomI).continuousOn
  have hwc : ContinuousOn (fun θ => deriv (fun ν => radialSolution d h θ r ν) μ)
      (Icc 0 d.T) :=
    (radialSolution_parameter_derivatives_continuous d h).2.comp
      (continuousOn_id.prodMk continuousOn_const) (fun θ hθ => hdomI θ hθ)
  have hpartials := radialSolution_remainder_partials_continuous d h hdomI hcyl
  have hw0 := (radialSolution_variation_initial d h ha (h.T_pos.trans hb) hdom hp).2
  have hwd : ∀ θ ∈ Icc 0 d.T,
      HasDerivWithinAt (fun θ => deriv (fun ν => radialSolution d h θ r ν) μ)
        ((d.A μ+3*d.B μ*(radialSolution d h θ r μ)^2+
            deriv (fun x => remainder d θ x μ) (radialSolution d h θ r μ))*
          deriv (fun ν => radialSolution d h θ r ν) μ+
          deriv d.A μ*radialSolution d h θ r μ+
          deriv d.B μ*(radialSolution d h θ r μ)^3+
          deriv (fun ν => remainder d θ (radialSolution d h θ r μ) ν) μ)
        (Icc 0 d.T) θ := by
    intro θ hθ
    convert (radialSolution_variation_equations d h ha (h.T_pos.trans hb) hdom
      (hθJ θ hθ) hp (hcyl θ hθ)).2.hasDerivWithinAt using 1 <;> ring
  have hqb : ∀ θ ∈ Icc 0 d.T,
      |deriv (fun x => remainder d θ x μ) (radialSolution d h θ r μ)| ≤
        d.M*|radialSolution d h θ r μ|^3 :=
    fun θ hθ => (h.remainder_bounds _ (hcyl θ hθ)).2.1
  have hzb : ∀ θ ∈ Icc 0 d.T,
      |deriv (fun ν => remainder d θ (radialSolution d h θ r μ) ν) μ| ≤
        d.M*|radialSolution d h θ r μ|^4 :=
    fun θ hθ => (h.remainder_bounds _ (hcyl θ hθ)).2.2
  have hlin := radialSolution_linear_error_bound d h hL.le hN hr hμ hA hB hdomI
    (fun θ hθ => ⟨(hu θ hθ).1,(hu θ hθ).2.1⟩)
  exact parameter_variation_linear_error_bound h.T_pos.le h.bound_nonneg hL.le hW hN hD
    hA hA' hB hB' hr huc hwc hpartials.1 hpartials.2 hw0 hwd
    (fun θ hθ => (hu θ hθ).1) hwb hqb hzb hlin


lemma endpointError_parameter_derivative_integral
    (d : AngularData) (h : Hypotheses d) {U : Set ℝ} {r μ : ℝ}
    {w : ℝ → ℝ → ℝ}
    (hU : IsOpen U) (hμ : μ ∈ U) (hUε : U ⊆ Ioo (-d.ε) d.ε)
    (hdom : ∀ ν ∈ U, ∀ s ∈ Icc 0 d.T, (s,(r,ν)) ∈ amplitudeDomain d h)
    (hw : ContinuousOn (fun q : ℝ × ℝ => w q.1 q.2) (Icc 0 d.T ×ˢ U))
    (hwd : ∀ s ∈ Icc 0 d.T, ∀ ν ∈ U,
      HasDerivAt (fun ν => radialSolution d h s r ν) (w s ν) ν)
    (hhr : ContinuousOn (fun q : ℝ × ℝ =>
      deriv (fun x => remainder d q.1 x q.2) (radialSolution d h q.1 r q.2)) (Icc 0 d.T ×ˢ U))
    (hhμ : ContinuousOn (fun q : ℝ × ℝ =>
      deriv (fun ν => remainder d q.1 (radialSolution d h q.1 r q.2) ν) q.2) (Icc 0 d.T ×ˢ U))
 :
    HasDerivAt (fun ν => endpointError d h r ν)
      (deriv d.A μ * d.T * endpointError d h r μ +
        Real.exp (d.A μ*d.T) * ∫ s in 0..d.T, Real.exp (-d.A μ*s) *
          (-deriv d.A μ * s *
            (d.B μ * (radialSolution d h s r μ^3 - (Real.exp (d.A μ*s)*r)^3) +
              remainder d s (radialSolution d h s r μ) μ) +
            deriv d.B μ * (radialSolution d h s r μ^3 - (Real.exp (d.A μ*s)*r)^3) +
            3*d.B μ * (radialSolution d h s r μ^2*w s μ -
              Real.exp (d.A μ*s)^3*deriv d.A μ*s*r^3) +
            deriv (fun x => remainder d s x μ) (radialSolution d h s r μ)*w s μ +
            deriv (fun ν => remainder d s (radialSolution d h s r μ) ν) μ)) μ := by
  let u := fun s ν => radialSolution d h s r ν
  let p := fun s ν => Real.exp (d.A ν*s)
  let R := fun s ν => remainder d s (u s ν) ν
  let H := fun s ν => deriv (fun x => remainder d s x ν) (u s ν)
  let J := fun s ν => deriv (fun z => remainder d s (u s ν) z) ν
  let C := fun s ν => d.B ν * (u s ν^3 - (p s ν*r)^3) + R s ν
  let F := fun ν s => Real.exp (-d.A ν*s) * C s ν
  let F' := fun ν s => Real.exp (-d.A ν*s) *
    (-deriv d.A ν*s*C s ν + deriv d.B ν*(u s ν^3 - (p s ν*r)^3) +
      3*d.B ν*(u s ν^2*w s ν - p s ν^3*deriv d.A ν*s*r^3) + H s ν*w s ν + J s ν)
  have huc : ContinuousOn (fun q : ℝ × ℝ => u q.1 q.2) (Icc 0 d.T ×ˢ U) := by
    exact continuousOn_const.mul ((amplitude_c2 d h).2.continuousOn.comp
      (f := fun q : ℝ × ℝ => (q.1,(r,q.2)))
      (continuousOn_fst.prodMk (continuousOn_const.prodMk continuousOn_snd))
      (fun q hq => hdom q.2 hq.2 q.1 hq.1))
  have hAc : ContinuousOn (fun q : ℝ × ℝ => d.A q.2) (Icc 0 d.T ×ˢ U) :=
    h.smooth_A.continuousOn.comp continuousOn_snd (fun q hq => hUε hq.2)
  have hBc : ContinuousOn (fun q : ℝ × ℝ => d.B q.2) (Icc 0 d.T ×ˢ U) :=
    h.smooth_B.continuousOn.comp continuousOn_snd (fun q hq => hUε hq.2)
  have hAdc : ContinuousOn (fun q : ℝ × ℝ => deriv d.A q.2) (Icc 0 d.T ×ˢ U) :=
    (h.smooth_A.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).comp
      continuousOn_snd (fun q hq => hUε hq.2)
  have hBdc : ContinuousOn (fun q : ℝ × ℝ => deriv d.B q.2) (Icc 0 d.T ×ˢ U) :=
    (h.smooth_B.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).comp
      continuousOn_snd (fun q hq => hUε hq.2)
  have hpc : ContinuousOn (fun q : ℝ × ℝ => p q.1 q.2) (Icc 0 d.T ×ˢ U) :=
    Real.continuous_exp.comp_continuousOn (hAc.mul continuousOn_fst)
  have hGc : ContinuousOn (fun q : ℝ × ℝ => d.G ((q.1,u q.1 q.2),q.2))
      (Icc 0 d.T ×ˢ U) := h.smooth_G.continuousOn.comp
    ((continuousOn_fst.prodMk huc).prodMk continuousOn_snd)
    (fun q hq => (amplitude_derivative d h (hdom q.2 hq.2 q.1 hq.1)).1)
  have hRc : ContinuousOn (fun q : ℝ × ℝ => R q.1 q.2) (Icc 0 d.T ×ˢ U) :=
    ((huc.mul hGc).sub (hAc.mul huc)).sub (hBc.mul (huc.pow 3))
  have hCc : ContinuousOn (fun q : ℝ × ℝ => C q.1 q.2) (Icc 0 d.T ×ˢ U) :=
    (hBc.mul ((huc.pow 3).sub ((hpc.mul continuousOn_const).pow 3))).add hRc
  have hFc : ContinuousOn (fun q : ℝ × ℝ => F q.2 q.1) (Icc 0 d.T ×ˢ U) :=
    (Real.continuous_exp.comp_continuousOn (hAc.neg.mul continuousOn_fst)).mul hCc
  have hF'c : ContinuousOn (fun q : ℝ × ℝ => F' q.2 q.1) (Icc 0 d.T ×ˢ U) := by
    have hc1 := (hAdc.neg.mul continuousOn_fst).mul hCc
    have hc2 := hBdc.mul ((huc.pow 3).sub ((hpc.mul (continuousOn_const (c := r))).pow 3))
    have hc3 := ((continuousOn_const (c := (3 : ℝ))).mul hBc).mul (((huc.pow 2).mul hw).sub
      ((((hpc.pow 3).mul hAdc).mul continuousOn_fst).mul (continuousOn_const (c := r^3))))
    exact (Real.continuous_exp.comp_continuousOn (hAc.neg.mul continuousOn_fst)).mul
      ((((hc1.add hc2).add hc3).add (hhr.mul hw)).add hhμ)
  have hFd : ∀ s ∈ Icc 0 d.T, ∀ ν ∈ U,
      HasDerivAt (fun ν => F ν s) (F' ν s) ν := by
    intro s hs ν hν
    have hA := ((h.smooth_A.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).contDiffAt
      (isOpen_Ioo.mem_nhds (hUε hν))).differentiableAt_one.hasDerivAt
    have hB := ((h.smooth_B.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).contDiffAt
      (isOpen_Ioo.mem_nhds (hUε hν))).differentiableAt_one.hasDerivAt
    have hu := hwd s hs ν hν
    have hp := (hA.mul_const s).exp
    have hR := remainder_hasDerivAt_curve d h
      (amplitude_derivative d h (hdom ν hν s hs)).1 (abs_lt.mpr (hUε hν)) hu
    have hd := ((hA.neg.mul_const s).exp).mul
      ((hB.mul ((hu.pow 3).sub ((hp.mul_const r).pow 3))).add hR)
    convert hd using 1
    dsimp [F',C,u,p,R,H,J]
    ring
  have hI := intervalIntegral_hasDerivAt_of_continuousOn h.T_pos.le hU hμ hFc hF'c hFd
  have hA := ((h.smooth_A.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).contDiffAt
    (isOpen_Ioo.mem_nhds (hUε hμ))).differentiableAt_one.hasDerivAt
  have hE := ((hA.mul_const d.T).exp).mul hI
  have heq : (fun ν => endpointError d h r ν) =ᶠ[𝓝 μ]
      (fun ν => Real.exp (d.A ν*d.T) * ∫ s in 0..d.T, F ν s) := by
    filter_upwards [hU.mem_nhds hμ] with ν hν
    exact endpointError_integral d h (hdom ν hν)
  convert hE.congr_of_eventuallyEq heq using 1
  rw [endpointError_integral d h (hdom μ hμ)]
  dsimp [F,F',C,u,p,R,H,J]
  ring


set_option maxHeartbeats 1000000 in
lemma endpointError_parameter_derivative_integral_on_box
    (d : AngularData) (h : Hypotheses d) {δ η L a b r μ : ℝ}
    (he : Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ η L a b)
    (hp : (r,μ) ∈ parameterBox δ η) :
    let w := fun s ν => deriv (fun z => radialSolution d h s r z) ν
    HasDerivAt (fun ν => endpointError d h r ν)
      (deriv d.A μ * d.T * endpointError d h r μ +
        Real.exp (d.A μ*d.T) * ∫ s in 0..d.T, Real.exp (-d.A μ*s) *
          (-deriv d.A μ * s *
            (d.B μ * (radialSolution d h s r μ^3 - (Real.exp (d.A μ*s)*r)^3) +
              remainder d s (radialSolution d h s r μ) μ) +
            deriv d.B μ * (radialSolution d h s r μ^3 - (Real.exp (d.A μ*s)*r)^3) +
            3*d.B μ * (radialSolution d h s r μ^2*w s μ -
              Real.exp (d.A μ*s)^3*deriv d.A μ*s*r^3) +
            deriv (fun x => remainder d s x μ) (radialSolution d h s r μ)*w s μ +
            deriv (fun ν => remainder d s (radialSolution d h s r μ) ν) μ)) μ := by
  let w := fun s ν => deriv (fun z => radialSolution d h s r z) ν
  change HasDerivAt _ _ μ
  rcases he with ⟨hδ,hδρ,hη,hηε,hL,ha,hb,hLδ,hdom,hY,hev,hzero,hQ,hfact⟩
  let S := Icc 0 d.T ×ˢ parameterBox δ η
  have hSJ : S ⊆ amplitudeDomain d h := by
    intro q hq
    exact hdom ⟨⟨ha.trans_le hq.1.1,hq.1.2.trans_lt hb⟩,hq.2⟩
  have hScyl : ∀ q ∈ S,
      ((q.1,radialSolution d h q.1 q.2.1 q.2.2),q.2.2) ∈ cylinder d := by
    intro q hq
    refine ⟨hq.1,((hev q.2.1 q.2.2 hq.2).2.2.2 q.1 hq.1).2.1,?_⟩
    exact (abs_lt.mpr hq.2.2).trans hηε
  have hpartial := radialSolution_remainder_partials_joint_continuous d h hSJ hScyl
  have hmap : MapsTo (fun q : ℝ × ℝ => (q.1,(r,q.2)))
      (Icc 0 d.T ×ˢ Ioo (-η) η) S := fun q hq => ⟨hq.1,hp.1,hq.2⟩
  have hmc : ContinuousOn (fun q : ℝ × ℝ => (q.1,(r,q.2)))
      (Icc 0 d.T ×ˢ Ioo (-η) η) :=
    continuousOn_fst.prodMk (continuousOn_const.prodMk continuousOn_snd)
  apply endpointError_parameter_derivative_integral d h isOpen_Ioo hp.2
    (fun ν hν => ⟨(neg_lt_neg hηε).trans hν.1,hν.2.trans hηε⟩)
    (fun ν hν s hs => hSJ ⟨hs,hp.1,hν⟩)
    ((radialSolution_parameter_derivatives_continuous d h).2.comp hmc
      (fun q hq => hSJ (hmap hq)))
    ?_ (hpartial.1.comp hmc hmap) (hpartial.2.comp hmc hmap)
  intro s hs ν hν
  have hd := (radialSolution_first_derivatives d h (r := r) (μ := ν) ha (h.T_pos.trans hb) hdom
    ⟨ha.trans_le hs.1,hs.2.trans_lt hb⟩ ⟨hp.1,hν⟩).2
  simpa only [w,hd.deriv] using hd



set_option maxHeartbeats 1200000 in
lemma endpointError_parameter_bound (d : AngularData) (h : Hypotheses d)
    {δ η L a b N W C : ℝ}
    (he : Specs.D13Unified.Ch16.HopfAngularScalarEstimates.EvolutionOnBox d h δ η L a b)
    (hδ : δ ≤ 1) (hN : 0 ≤ N) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hEb : ∀ r μ, (r,μ) ∈ parameterBox δ η → |endpointError d h r μ| ≤ C*|r|^4)
    (hcoeff : ∀ μ, |μ| < η →
      |d.A μ| ≤ N ∧ |d.B μ| ≤ N ∧ |deriv d.A μ| ≤ N ∧ |deriv d.B μ| ≤ N)
    (hwb : ∀ r μ, (r,μ) ∈ parameterBox δ η → ∀ θ ∈ Icc 0 d.T,
      |deriv (fun ν => radialSolution d h θ r ν) μ| ≤ W*|r|) :
    ∃ Cμ : ℝ, 0 ≤ Cμ ∧ ∀ r μ, (r,μ) ∈ parameterBox δ η →
      |deriv (fun ν => endpointError d h r ν) μ| ≤ Cμ*|r|^4 := by
  have he0 := he
  rcases he with ⟨hd,hdρ,hη,hηε,hL,ha,hb,hLδ,hdom,hY,hev,hzero,hQ,hfact⟩
  let S := Icc 0 d.T ×ˢ parameterBox δ η
  let u : ℝ × (ℝ × ℝ) → ℝ := fun q => radialSolution d h q.1 q.2.1 q.2.2
  let p : ℝ × (ℝ × ℝ) → ℝ := fun q => Real.exp (d.A q.2.2*q.1)*q.2.1
  let w : ℝ × (ℝ × ℝ) → ℝ := fun q =>
    deriv (fun ν => radialSolution d h q.1 q.2.1 ν) q.2.2
  let z : ℝ × (ℝ × ℝ) → ℝ := fun q =>
    deriv d.A q.2.2*q.1*Real.exp (d.A q.2.2*q.1)*q.2.1
  let ap : ℝ × (ℝ × ℝ) → ℝ := fun q => deriv d.A q.2.2
  let B : ℝ × (ℝ × ℝ) → ℝ := fun q => d.B q.2.2
  let bp : ℝ × (ℝ × ℝ) → ℝ := fun q => deriv d.B q.2.2
  let e : ℝ × (ℝ × ℝ) → ℝ := fun q => endpointError d h q.2.1 q.2.2
  let hm : ℝ × (ℝ × ℝ) → ℝ := fun q => remainder d q.1 (u q) q.2.2
  let hr : ℝ × (ℝ × ℝ) → ℝ := fun q =>
    deriv (fun x => remainder d q.1 x q.2.2) (u q)
  let hmμ : ℝ × (ℝ × ℝ) → ℝ := fun q =>
    deriv (fun ν => remainder d q.1 (u q) ν) q.2.2
  let eμ : ℝ × (ℝ × ℝ) → ℝ := fun q =>
    deriv (fun ν => endpointError d h q.2.1 ν) q.2.2
  let H := Real.exp (N*d.T)
  let D := H^2*(N*L^3+d.M*L^4)*d.T
  let J := H^2*(N*D+(3*N*L^2+d.M*L^3)*W+N*L^3+d.M*L^4)*d.T
  have hH : 0 ≤ H := (Real.exp_pos _).le
  have hM := h.bound_nonneg
  have hT := h.T_pos.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hcoeffq : ∀ q ∈ S,
      |d.A q.2.2| ≤ N ∧ |d.B q.2.2| ≤ N ∧
      |deriv d.A q.2.2| ≤ N ∧ |deriv d.B q.2.2| ≤ N :=
    fun q hq => hcoeff q.2.2 (abs_lt.mpr hq.2.2)
  have hsmall : ∀ q ∈ S, |q.2.1| ≤ 1 :=
    fun q hq => (abs_lt.mpr hq.2.1).le.trans hδ
  have hub : ∀ q ∈ S, |u q| ≤ L*|q.2.1| :=
    fun q hq => ((hev q.2.1 q.2.2 hq.2).2.2.2 q.1 hq.1).1
  have hcyl : ∀ q ∈ S, ((q.1,u q),q.2.2) ∈ cylinder d := by
    intro q hq
    exact ⟨hq.1,((hev q.2.1 q.2.2 hq.2).2.2.2 q.1 hq.1).2.1,
      (abs_lt.mpr hq.2.2).trans hηε⟩
  have hu : RadialOrderBound S 1 u := ⟨L,hL.le,by simpa only [pow_one] using hub⟩
  have hap : RadialOrderBound S 0 ap := RadialOrderBound.of_uniform hN
    (fun q hq => (hcoeffq q hq).2.2.1)
  have hB : RadialOrderBound S 0 B := RadialOrderBound.of_uniform hN
    (fun q hq => (hcoeffq q hq).2.1)
  have hbp : RadialOrderBound S 0 bp := RadialOrderBound.of_uniform hN
    (fun q hq => (hcoeffq q hq).2.2.2)
  have ht : RadialOrderBound S 0 (fun q => q.1) := RadialOrderBound.of_uniform hT
    (fun q hq => by simpa only [abs_of_nonneg hq.1.1] using hq.1.2)
  have hexp : RadialOrderBound S 0 (fun q => Real.exp (d.A q.2.2*q.1)) :=
    RadialOrderBound.of_uniform hH (fun q hq => (exponential_bounds (hcoeffq q hq).1 hq.1).1)
  have hp : RadialOrderBound S 1 p := hexp.mul (RadialOrderBound.radius S)
  have hz : RadialOrderBound S 1 z := ((hap.mul ht).mul hexp).mul (RadialOrderBound.radius S)
  have hw : RadialOrderBound S 1 w := ⟨W,hW,fun q hq => by
    simpa only [pow_one] using hwb q.2.1 q.2.2 hq.2 q.1 hq.1⟩
  have hE : RadialOrderBound S 4 e := ⟨C,hC,fun q hq => hEb q.2.1 q.2.2 hq.2⟩
  have hhm : RadialOrderBound S 4 hm := by
    refine ⟨d.M*L^4,by positivity,fun q hq => ?_⟩
    calc
      _ ≤ d.M*|u q|^4 := (h.remainder_bounds _ (hcyl q hq)).1
      _ ≤ d.M*(L*|q.2.1|)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hub q hq) 4) hM
      _ = _ := by ring
  have hhr : RadialOrderBound S 3 hr := by
    refine ⟨d.M*L^3,by positivity,fun q hq => ?_⟩
    calc
      _ ≤ d.M*|u q|^3 := (h.remainder_bounds _ (hcyl q hq)).2.1
      _ ≤ d.M*(L*|q.2.1|)^3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hub q hq) 3) hM
      _ = _ := by ring
  have hhmμ : RadialOrderBound S 4 hmμ := by
    refine ⟨d.M*L^4,by positivity,fun q hq => ?_⟩
    calc
      _ ≤ d.M*|u q|^4 := (h.remainder_bounds _ (hcyl q hq)).2.2
      _ ≤ d.M*(L*|q.2.1|)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hub q hq) 4) hM
      _ = _ := by ring
  have hud : RadialOrderBound S 3 (fun q => u q-p q) := by
    refine ⟨D,hD,fun q hq => ?_⟩
    have hdom' : ∀ θ ∈ Icc 0 d.T, (θ,q.2) ∈ amplitudeDomain d h :=
      fun θ hθ => hdom ⟨⟨ha.trans_le hθ.1,hθ.2.trans_lt hb⟩,hq.2⟩
    exact radialSolution_linear_error_bound d h hL.le hN (hsmall q hq)
      ((abs_lt.mpr hq.2.2).trans hηε) (hcoeffq q hq).1 (hcoeffq q hq).2.1 hdom'
      (fun θ hθ => ⟨((hev q.2.1 q.2.2 hq.2).2.2.2 θ hθ).1,
        ((hev q.2.1 q.2.2 hq.2).2.2.2 θ hθ).2.1⟩) q.1 hq.1
  have hwd : RadialOrderBound S 3 (fun q => w q-z q) := by
    refine ⟨J,hJ,fun q hq => ?_⟩
    exact radialSolution_parameter_linear_error_bound d h he0 hN hW hq.2 (hsmall q hq)
      (hcoeffq q hq).1 (hcoeffq q hq).2.1 (hcoeffq q hq).2.2.1 (hcoeffq q hq).2.2.2
      (hwb q.2.1 q.2.2 hq.2) q.1 hq.1
  have hid : ∀ q ∈ S,
      eμ q = ap q*d.T*e q + Real.exp (d.A q.2.2*d.T) *
        ∫ s in 0..d.T, Real.exp (-d.A q.2.2*s) *
          (-(ap (s,q.2)*s)*(B (s,q.2)*(u (s,q.2)^3-p (s,q.2)^3)+hm (s,q.2)) +
            bp (s,q.2)*(u (s,q.2)^3-p (s,q.2)^3) +
            3*B (s,q.2)*(u (s,q.2)^2*w (s,q.2)-p (s,q.2)^2*z (s,q.2)) +
            hr (s,q.2)*w (s,q.2)+hmμ (s,q.2)) := by
    intro q hq
    have hh := (endpointError_parameter_derivative_integral_on_box d h he0 hq.2).deriv
    dsimp only [eμ,ap,e,B,u,p,w,z,bp,hm,hr,hmμ]
    rw [hh]
    congr 1
    apply congrArg (fun x : ℝ => Real.exp (d.A q.2.2*d.T)*x)
    apply intervalIntegral.integral_congr
    intro s _
    ring
  obtain ⟨Cμ,hCμ,hCμb⟩ := RadialOrderBound.parameter_residual hT hsmall
    (fun μ hμ => (hcoeff μ (abs_lt.mpr hμ)).1) hap hB hbp hu hp hw hz hud hwd hE hhm hhr hhmμ hid
  refine ⟨Cμ,hCμ,fun r μ hp => ?_⟩
  exact hCμb (0,(r,μ)) ⟨⟨le_rfl,hT⟩,hp⟩



/-- Full signed scalar endpoint expansion with uniform first derivative
remainders, obtained from the vector-field assumptions alone. -/
theorem angularEstimates :
    Specs.D13Unified.Ch16.HopfAngularScalarEstimates.AngularEstimates := by
  intro d h
  obtain ⟨δ₀,η₀,L,C₀,a,b,hC₀,he₀,hE₀,hEb₀⟩ := quarticEndpointEstimate d h
  obtain ⟨δ,η,N,V,W,hδ,hδδ₀,hδone,hη,hηη₀,hN,hV,hW,he,hE,hEb,hcoeff,hvw⟩ :=
    common_uniform_data d h he₀ hE₀ hEb₀
  have hL : 0 ≤ L := he.2.2.2.2.1.le
  let H := Real.exp (N*d.T)
  let D := H^2*(N*L^3+d.M*L^4)*d.T
  let J := H^2*((3*N*L^2+d.M*L^3)*V)*d.T
  let Cr := H^2*(3*N*(L^2*J+D*(L+H)*H)+d.M*L^3*V)*d.T
  have hH : 0 ≤ H := (Real.exp_pos _).le
  have hM := h.bound_nonneg
  have hT := h.T_pos.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hrb : ∀ r μ, (r,μ) ∈ parameterBox δ η →
      |deriv (fun x => endpointError d h x μ) r| ≤ Cr*|r|^3 := by
    intro r μ hp
    have hc := hcoeff μ (abs_lt.mpr hp.2)
    exact endpointError_radius_bound d h he hδone hp hN hV hc.1 hc.2.1
      (fun θ hθ => (hvw r μ hp θ hθ).1)
  obtain ⟨Cμ,hCμ,hμb⟩ := endpointError_parameter_bound d h he hδone hN hW hC₀ hEb
    hcoeff (fun r μ hp θ hθ => (hvw r μ hp θ hθ).2)
  let C := max (max C₀ Cr) Cμ
  have hC₀C : C₀ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCrC : Cr ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCμC : Cμ ≤ C := le_max_right _ _
  refine ⟨δ,η,L,C,a,b,hC₀.trans hC₀C,he,hE.of_le (by norm_num),?_⟩
  intro r μ hp
  refine ⟨endpoint_expansion_identity d h r μ,
    (hEb r μ hp).trans ?_,(hrb r μ hp).trans ?_,(hμb r μ hp).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hC₀C (pow_nonneg (abs_nonneg _) _)
  · exact mul_le_mul_of_nonneg_right hCrC (pow_nonneg (abs_nonneg _) _)
  · exact mul_le_mul_of_nonneg_right hCμC (pow_nonneg (abs_nonneg _) _)

end D13Unified.Ch16.HopfAngularScalarEstimates
