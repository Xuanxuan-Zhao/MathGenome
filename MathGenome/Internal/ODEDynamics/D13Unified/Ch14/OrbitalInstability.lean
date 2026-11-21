import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.OrbitalInstability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.ReturnMap
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.Multipliers
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.OrbitalStability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.LinearizedInstability
import Mathlib.Topology.Order.Compact

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch14.OrbitalInstability
open Ch06.StateDerivative Ch11.Orbits Ch08.MatrixPowerCriteria
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch14.ReturnMap Specs.D13Unified.Ch14.OrbitalDefinitions
open Specs.D13Unified.Ch14.OrbitalInstability

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- No point of the chosen local section except its origin belongs to Γ.
The first-return property at zero excludes the entire open period arc. -/
lemma section_isolation {k : ℕ} {F : AutonomousODE E}
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic (fun t => flow F t p) T)
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ)
    {v : ℓ.ker} (hv : v ∈ d.sectionSet) (horb : p + (v : E) ∈ orbit F p) :
    v = 0 := by
  obtain ⟨t,ht,he⟩ := horb
  obtain ⟨s,hs,hes⟩ := hper.exists_mem_Ico₀ hT t
  have heq : flow F s p = p + (v : E) := hes.symm.trans he
  by_cases hs0 : s = 0
  · rw [hs0, (Ch11.Flow.flow_zero F hF p hp).2] at heq
    apply Subtype.ext
    simpa using (add_left_cancel (heq.symm.trans (add_zero p).symm))
  · have hno := d.first_return 0 d.source_zero s (lt_of_le_of_ne hs.1 (Ne.symm hs0))
      (by simpa only [d.time_zero] using hs.2)
    apply False.elim
    apply hno
    simp only [ZeroMemClass.coe_zero, add_zero]
    exact ⟨v,hv,heq.symm⟩

/-- Finite concatenation requires only the inputs preceding the exit to
belong to the actual return-map source; the final output can have exited. -/
lemma finite_return_nodes {k : ℕ} {F : AutonomousODE E}
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ)
    (v : ℓ.ker) (N : ℕ) (hv : v ∈ d.P.source)
    (hprior : ∀ n < N, (d.P : ℓ.ker → ℓ.ker)^[n] v ∈ d.P.source) :
    ∃ t : ℝ, (0 < N → 0 < t) ∧ (t,p + (v : E)) ∈ flowDomain F ∧
      flow F t (p + (v : E)) = p + ((d.P : ℓ.ker → ℓ.ker)^[N] v : E) := by
  have hpv := d.section_domain v (d.source_section hv)
  have hnodes : ∀ n, n ≤ N → ∃ t : ℝ, 0 ≤ t ∧ (0 < n → 0 < t) ∧
      (t,p + (v : E)) ∈ flowDomain F ∧
      flow F t (p + (v : E)) = p + ((d.P : ℓ.ker → ℓ.ker)^[n] v : E) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨0,le_rfl,by omega,by simpa using Ch11.Flow.flow_zero F hF _ hpv⟩
    | succ n ih =>
      intro hn
      obtain ⟨t,ht,_,hdom,he⟩ := ih (by omega)
      have hz := hprior n (by omega)
      have hτ := d.time_positive _ hz
      have hseg := d.flow_domain _ hz (d.τ _) ⟨hτ.le,(d.time_near _ hz).2.le⟩
      have htrans := Ch11.Flow.flow_translation F hF _ hpv _ hdom.2
      rw [he] at htrans
      have hsum : d.τ ((d.P : ℓ.ker → ℓ.ker)^[n] v) + t ∈
          (flowInterval F (p + (v : E))).carrier := by
        have hh := hseg.2
        rw [htrans.1] at hh
        exact hh
      refine ⟨d.τ ((d.P : ℓ.ker → ℓ.ker)^[n] v) + t, by linarith,
        fun _ => by linarith, ⟨hpv,hsum⟩, ?_⟩
      rw [← htrans.2 _ hsum, d.map_formula _ hz]
      simp only [Function.iterate_succ_apply']
  obtain ⟨t,_,hpos,hdom,he⟩ := hnodes N le_rfl
  exact ⟨t,hpos,hdom,he⟩

/-- A compact section annulus is uniformly separated from the whole orbit.
This also covers an empty annulus, without an artificial nonemptiness premise. -/
lemma annulus_separation {k : ℕ} {F : AutonomousODE E}
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    {T : ℝ} (hT : 0 < T) (hc : IsComplete F p)
    (hper : Function.Periodic (fun t => flow F t p) T)
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ)
    {R ε : ℝ} (hε : 0 < ε)
    (hR : Metric.closedBall (0 : ℓ.ker) R ⊆ d.sectionSet) :
    ∃ a : ℝ, 0 < a ∧ ∀ v : ℓ.ker, ε ≤ ‖v‖ → ‖v‖ ≤ R →
      a ≤ Metric.infDist (p + (v : E)) (orbit F p) := by
  let A : Set ℓ.ker := Metric.closedBall 0 R ∩ {v | ε ≤ ‖v‖}
  have hAc : IsCompact A := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hΓ : IsCompact (orbit F p) :=
    NearbySectionEntry.periodic_orbit_compact F hF hp hT hc hper
  have hpΓ : p ∈ orbit F p := by
    exact ⟨0,(Ch11.Flow.flow_zero F hF p hp).1.2,(Ch11.Flow.flow_zero F hF p hp).2⟩
  have hf : Continuous (fun v : ℓ.ker => Metric.infDist (p + (v : E)) (orbit F p)) :=
    (Metric.continuous_infDist_pt _).comp (continuous_const.add ℓ.ker.subtypeL.continuous)
  have hpos : ∀ v ∈ A, 0 < Metric.infDist (p + (v : E)) (orbit F p) := by
    intro v hv
    apply (hΓ.isClosed.notMem_iff_infDist_pos ⟨p,hpΓ⟩).mp
    intro horb
    have hz := section_isolation hF hp hT hper d (hR hv.1) horb
    have hnorm : ε ≤ ‖v‖ := hv.2
    exact hε.not_ge (by simpa only [hz, norm_zero] using hnorm)
  by_cases hA : A.Nonempty
  · obtain ⟨v,hv,hmin⟩ := hAc.exists_isMinOn hA hf.continuousOn
    exact ⟨_,hpos v hv,fun w hw hwR => hmin ⟨by simpa using hwR,hw⟩⟩
  · exact ⟨1,zero_lt_one,fun v hv hvR => False.elim
      (hA ⟨v,⟨by simpa using hvR,hv⟩⟩)⟩

/-- A witnessed distance escape contradicts orbital stability. -/
lemma unstable_of_distanceEscape {F : AutonomousODE E}
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    (h : distanceEscapeValue F p) : orbitalUnstableValue F (orbit F p) := by
  obtain ⟨ε,hε,hw⟩ := h
  intro hstable
  obtain ⟨δ,hδ,hstay⟩ := hstable ε hε
  obtain ⟨x,hx,hxp,t,ht,_,hexit⟩ := hw δ hδ
  have hpΓ : p ∈ orbit F p :=
    ⟨0,(Ch11.Flow.flow_zero F hF p hp).1.2,(Ch11.Flow.flow_zero F hF p hp).2⟩
  have hnear : Metric.infDist x (orbit F p) < δ :=
    (Metric.infDist_le_dist_of_mem hpΓ).trans_lt (by simpa [dist_eq_norm] using hxp)
  exact (not_lt_of_ge hexit) ((hstay x hx hnear).2 t ht.le)

/-- Discrete first exits are realized at finite sums of positive return times.
Continuity bounds the final output, so the entire exit annulus is compact and
has positive distance from Γ, uniformly in the arbitrarily small perturbation. -/
theorem orbital_instability : OrbitalInstabilityExpected := by
  intro E _ _ _ k hk F hF p hp T hT hc hper _hmin _hnc ℓ d hspec
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  obtain ⟨R₀,hR₀,hRball⟩ := Metric.mem_nhds_iff.mp
    (d.section_open.mem_nhds d.section_zero)
  let R := R₀ / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRc : Metric.closedBall (0 : ℓ.ker) R ⊆ d.sectionSet := by
    apply Subset.trans _ hRball
    exact Metric.closedBall_subset_ball (by dsimp [R]; linarith)
  have hPc : ContinuousAt (d.P : ℓ.ker → ℓ.ker) 0 :=
    d.P.continuousOn.continuousAt (d.P.open_source.mem_nhds d.source_zero)
  have he : (d.P : ℓ.ker → ℓ.ker) ⁻¹' Metric.ball 0 R ∈ 𝓝 0 :=
    hPc.preimage_mem_nhds (by rw [d.map_zero]; exact Metric.ball_mem_nhds _ hR)
  obtain ⟨V,hVsub,hVo,h0V⟩ := mem_nhds_iff.mp
    (inter_mem (d.P.open_source.mem_nhds d.source_zero) he)
  have hsrc : V ⊆ d.P.source := fun _ hv => (hVsub hv).1
  have houtput : ∀ v ∈ V, ‖d.P v‖ < R := by
    intro v hv
    simpa only [mem_preimage, Metric.mem_ball, dist_zero_right] using (hVsub hv).2
  have hcd : ContDiffAt ℝ 1 (d.P : ℓ.ker → ℓ.ker) 0 :=
    (d.map_regular.of_le (by exact_mod_cast hk)).contDiffAt
      (d.P.open_source.mem_nhds d.source_zero)
  obtain ⟨ε,hε,_hball,hperturb⟩ :=
    Ch15.LinearizedInstability.linearizedInstability (Module.finBasis ℝ ℓ.ker)
      d.P V 0 (fderiv ℝ (d.P : ℓ.ker → ℓ.ker) 0) hVo h0V d.map_zero hcd
      (hcd.differentiableAt one_ne_zero).hasFDerivAt hspec
  obtain ⟨a,ha,hsep⟩ := annulus_separation hF1 hp hT hc hper d hε hRc
  have hescape : distanceEscapeValue F p := by
    refine ⟨a,ha,fun δ hδ => ?_⟩
    obtain ⟨v,hv,hvδ,N,hN,hexit,hprior⟩ := hperturb δ hδ
    have hprior' : ∀ n < N, (d.P : ℓ.ker → ℓ.ker)^[n] v ∈ d.P.source :=
      fun n hn => hsrc (hprior n hn).2
    obtain ⟨t,ht,hdom,heq⟩ := finite_return_nodes hF1 d v N (hsrc hv) hprior'
    have hupper : ‖(d.P : ℓ.ker → ℓ.ker)^[N] v‖ ≤ R := by
      obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
      simpa only [Function.iterate_succ_apply'] using (houtput _ (hprior n (by omega)).2).le
    refine ⟨p + (v : E),d.section_domain v (d.source_section (hsrc hv)),
      by simpa using hvδ,t,ht hN,hdom,?_⟩
    rw [heq]
    exact hsep _ (by simpa using hexit) hupper
  exact ⟨hescape,unstable_of_distanceEscape hF1 hp hescape⟩

/-- Complexification preserves a scalar section derivative, in the canonical
finite basis used by the common spectral interfaces. -/
lemma complexify_scalar {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [FiniteDimensional ℝ K] (B : K →L[ℝ] K) {μ : ℝ}
    (hB : B.toLinearMap = μ • LinearMap.id) :
    complexify (LinearMap.toMatrix (Module.finBasis ℝ K) (Module.finBasis ℝ K)
      B.toLinearMap) = algebraMap ℂ (CMatrix (Module.finrank ℝ K)) (μ : ℂ) := by
  classical
  rw [hB]
  simp [complexify, Algebra.algebraMap_eq_smul_one, Matrix.map_smul, Matrix.map_one]

/-- The only planar transverse multiplier is exp of the divergence integral.
The two strict signs give exponential orbital attraction and actual-time
orbital escape respectively. No conclusion is asserted at equality. -/
theorem planar_criteria : PlanarCriteriaExpected := by
  intro E _ _ _ hplane k hk F hF p hp T hT hc hper hmin hnc ℓ d
  have ha : ℓ (autonomousEvalValue F p) ≠ 0 := by
    simpa using d.section_transverse 0 d.section_zero
  obtain ⟨_,hdim,_,hdet,hplanar⟩ :=
    (Multipliers.multipliers k hk F hF p hp T hT hc hper hmin hnc ℓ ha d).2
  have hline : Module.finrank ℝ ℓ.ker = 1 := by omega
  obtain ⟨μ,hμ,hB,_⟩ := hplanar hplane
  let B := fderiv ℝ (d.P : ℓ.ker → ℓ.ker) 0
  change B.toLinearMap = μ • LinearMap.id at hB
  have hμexp : μ = Real.exp (∫ t in (0 : ℝ)..T,
      Specs.D13Unified.Ch14.Multipliers.divergence F (flow F t p)) := by
    rw [hB, LinearMap.det_smul, hline] at hdet
    simpa using hdet
  let M := complexify (LinearMap.toMatrix (Module.finBasis ℝ ℓ.ker)
    (Module.finBasis ℝ ℓ.ker) B.toLinearMap)
  haveI : NeZero (Module.finrank ℝ ℓ.ker) := ⟨by omega⟩
  have hM : M = algebraMap ℂ (CMatrix (Module.finrank ℝ ℓ.ker)) (μ : ℂ) :=
    complexify_scalar B hB
  have hσ : spectrum ℂ M = {(μ : ℂ)} := by rw [hM]; exact spectrum.scalar_eq _
  constructor
  · intro hneg
    have hμ1 : μ < 1 := by rw [hμexp]; exact Real.exp_lt_one_iff.mpr hneg
    apply OrbitalStability.orbital_stability k hk F hF p hp T hT hc hper hmin hnc ℓ d
    change StrictSpectrum M
    intro z hz
    have hzμ : z = (μ : ℂ) := by simpa only [hσ, mem_singleton_iff] using hz
    rw [hzμ]
    simpa only [Complex.norm_real, Real.norm_of_nonneg hμ.le] using hμ1
  · intro hpos
    have hμ1 : 1 < μ := by rw [hμexp]; exact Real.one_lt_exp_iff.mpr hpos
    apply orbital_instability k hk F hF p hp T hT hc hper hmin hnc ℓ d
    refine ⟨(μ : ℂ),?_,?_⟩
    · exact (Ch08.MatrixPowerCriteria.eigenvalueBridge M _).mpr (by simp [hσ])
    · simpa only [Complex.norm_real, Real.norm_of_nonneg hμ.le] using hμ1

end D13Unified.Ch14.OrbitalInstability
