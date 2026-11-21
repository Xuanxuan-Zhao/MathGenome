import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.IntervalDerivativeExtensions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.IntervalDerivativeAdjoint

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Topology
namespace ExpandedFA.Unbounded.IntervalDerivative
open ExpandedFA.Sobolev ExpandedFA.Sobolev.OneDimensional
open HilbertAdjointSpec SymmetryAndDeficienciesSpec

abbrev traceMap : H1 →L[ℂ] (Fin 2 → ℂ) := Trace.intervalTrace (by norm_num : (0 : ℝ) < 1)

lemma trace_rep (u : H1) (f : ℝ → ℂ) (hf : PrimitiveRepresentative u f) :
    traceMap u 0 = f 0 ∧ traceMap u 1 = f 1 := by
  constructor
  · simpa [Trace.endpoint] using Trace.intervalTrace_apply (by norm_num : (0 : ℝ) < 1) u f hf 0
  · simpa [Trace.endpoint] using Trace.intervalTrace_apply (by norm_num : (0 : ℝ) < 1) u f hf 1

lemma boundaryCondition_iff (z : ℂ) (u : H1) :
    boundaryCondition z u ↔ traceMap u 1 = z * traceMap u 0 := by
  constructor
  · rintro ⟨f, hf, he⟩
    rw [(trace_rep u f hf).1, (trace_rep u f hf).2]
    exact he
  · intro he
    obtain ⟨f, hf⟩ := representative_existence ℂ interval ordConnected_Ioo 2 u
    exact ⟨f, hf, by simpa only [(trace_rep u f hf).1, (trace_rep u f hf).2] using he⟩

def boundarySpace (z : ℂ) : Submodule ℂ H1 :=
  ( (LinearMap.proj (1 : Fin 2)).comp traceMap.toLinearMap -
    z • (LinearMap.proj (0 : Fin 2)).comp traceMap.toLinearMap).ker

lemma mem_boundarySpace (z : ℂ) (u : H1) :
    u ∈ boundarySpace z ↔ traceMap u 1 = z * traceMap u 0 := by
  change traceMap u 1 - z • traceMap u 0 = 0 ↔ _
  simp only [smul_eq_mul, sub_eq_zero]

lemma phaseDomain_eq (z : ℂ) : phaseDomain z = (boundarySpace z).map baseMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨u, hu, rfl⟩
    exact ⟨u, (mem_boundarySpace z u).mpr ((boundaryCondition_iff z u).mp hu), rfl⟩
  · rintro v ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨u, (boundaryCondition_iff z u).mpr
      ((mem_boundarySpace z u).mp hu), rfl⟩

lemma phaseDomain_le (z : ℂ) : phaseDomain z ≤ maximal.domain := by
  rw [phaseDomain_eq, domains.2]
  rintro v ⟨u, _, rfl⟩
  exact ⟨u, rfl⟩

lemma phase_domain_eq (z : ℂ) : (phaseOperator z).domain = phaseDomain z :=
  inf_eq_left.mpr (phaseDomain_le z)

theorem phase_domain : Specs.ExpandedFA.Unbounded.IntervalDerivativeExtensions.Domain := by
  intro z v
  rw [phase_domain_eq, phaseDomain_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, rfl, (boundaryCondition_iff z u).mpr ((mem_boundarySpace z u).mp hu)⟩
  · rintro ⟨u, rfl, hu⟩
    exact ⟨u, (mem_boundarySpace z u).mpr ((boundaryCondition_iff z u).mp hu), rfl⟩

lemma maximal_apply (u : H1) (h : baseLp u ∈ maximal.domain) :
    maximal ⟨baseLp u, h⟩ = (-Complex.I) • derivativeLp u :=
  ((mem_graph_iff maximal _).mp (maximal_graph_mem u)).2

theorem phase_action : Specs.ExpandedFA.Unbounded.IntervalDerivativeExtensions.Action := by
  intro z u h
  exact (LinearPMap.domRestrict_apply (y := ⟨baseLp u, h.2⟩) rfl).trans (maximal_apply u h.2)

lemma phase_graph_mem (z : ℂ) (u : H1)
    (hu : traceMap u 1 = z * traceMap u 0) :
    (baseLp u, (-Complex.I) • derivativeLp u) ∈ (phaseOperator z).graph := by
  have h : baseLp u ∈ (phaseOperator z).domain :=
    (phase_domain z _).mpr ⟨u, rfl, (boundaryCondition_iff z u).mpr hu⟩
  exact (mem_graph_iff _ _).mpr ⟨h, phase_action z u h⟩

theorem phase_extension : Specs.ExpandedFA.Unbounded.IntervalDerivativeExtensions.Extension := by
  intro z
  apply LinearPMap.le_of_le_graph
  rintro ⟨v, w⟩ hm
  rw [graphs.1] at hm
  obtain ⟨u, hu⟩ := hm
  change (baseLp u.val, (-Complex.I) • derivativeLp u.val) = (v, w) at hu
  rw [← hu]
  apply phase_graph_mem
  obtain ⟨f, hf⟩ := representative_existence ℂ interval ordConnected_Ioo 2 u.val
  have he := Trace.interval_zeroSpace_endpoints ℂ 0 1 (by norm_num) 2 (by norm_num)
    u.val u.property f hf
  rw [(trace_rep _ _ hf).1, (trace_rep _ _ hf).2, he.1, he.2, mul_zero]

lemma phase_dense (z : ℂ) : Dense ((phaseOperator z).domain : Set L2) :=
  dense_domain.mono (phase_extension z).1

lemma boundary_form_trace (u v : H1) :
    inner ℂ ((-Complex.I) • derivativeLp u) (baseLp v) -
      inner ℂ (baseLp u) ((-Complex.I) • derivativeLp v) =
        Complex.I * (star (traceMap u 1) * traceMap v 1 -
          star (traceMap u 0) * traceMap v 0) := by
  obtain ⟨f, hf⟩ := representative_existence ℂ interval ordConnected_Ioo 2 u
  obtain ⟨g, hg⟩ := representative_existence ℂ interval ordConnected_Ioo 2 v
  rw [(trace_rep _ _ hf).1, (trace_rep _ _ hf).2,
    (trace_rep _ _ hg).1, (trace_rep _ _ hg).2]
  exact boundary_form u v f g hf hg

/-- Adjoint reversal, stated only on dense domains, avoiding any use of the
library's totalization on non-dense operators. -/
lemma adjoint_le_of_le {A B : Operator ℂ L2 L2}
    (hA : Dense (A.domain : Set L2)) (hB : Dense (B.domain : Set L2)) (h : A ≤ B) :
    adjointValue B ≤ adjointValue A := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨v, w⟩ hv
  apply (mem_hilbertAdjoint_graph_iff A hA v w).mpr
  have hf := (mem_hilbertAdjoint_graph_iff B hB v w).mp hv
  intro x
  have hx : (x : L2) ∈ B.domain := h.1 x.property
  rw [h.2 (x := x) (y := ⟨x, hx⟩) rfl]
  exact hf ⟨x, hx⟩

/-- Arbitrary endpoint data are realized by an affine function, multiplied
by a compactly supported cutoff which is one near [0,1]. -/
lemma trace_surjective (a b : ℂ) : ∃ u : H1, traceMap u 0 = a ∧ traceMap u 1 = b := by
  let β : ContDiffBump (0 : ExpandedFA.Distributions.Domain 1) :=
    ⟨2, 3, by norm_num, by norm_num⟩
  let η : ExpandedFA.Distributions.Tests ℝ (⊤ : Opens (ExpandedFA.Distributions.Domain 1)) :=
    ⟨β, β.contDiff, β.hasCompactSupport, subset_univ _⟩
  let f : ExpandedFA.Distributions.Domain 1 → ℂ := fun x => a + (x 0 : ℂ) * (b - a)
  have hfd : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_const.add (((Complex.ofRealCLM.contDiff).comp (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0)).mul contDiff_const)
  let φ := Smoothing.smoothMulTest (Smoothing.liftRealTest (𝕜 := ℂ) η) f hfd
  let u : H1 := C1Extension.restrictSobolev le_top (testToSobolev (p := 2) 1 φ)
  have htest : (testToSobolev (p := 2) 1 φ).val (zeroIndex 1 1) =ᵐ[volume] φ := by
    rw [testToSobolev_underlying]
    simpa only [Opens.coe_top, Measure.restrict_univ] using testToDomainLp_coe (p := 2) φ
  have hu : Represents (baseLp u) (fun t => a + (t : ℂ) * (b - a)) := by
    filter_upwards [C1Extension.restrictSobolev_coe le_top
      (testToSobolev (p := 2) 1 φ) (zeroIndex 1 1),
      ae_restrict_of_ae htest,
      ae_restrict_mem (lineDomain interval).isOpen.measurableSet] with x hx hφ hxI
    change baseLp u x = _ at hx ⊢
    rw [hx, hφ]
    have hβ : β x = 1 := by
      apply β.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖x‖ ≤ 2
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change |x 0| ≤ 2
      rw [abs_of_pos hxI.1]
      exact le_trans hxI.2.le (by norm_num)
    change (β x : ℂ) * f x = _
    rw [hβ]
    simp only [Complex.ofReal_one, one_mul, f]
  have htrace := Trace.intervalTrace_of_continuous (by norm_num : (0 : ℝ) < 1) u
    (fun t => a + (t : ℂ) * (b - a))
    (by fun_prop) hu
  refine ⟨u, ?_, ?_⟩
  · simpa [traceMap, Trace.endpoint] using htrace 0
  · simpa [traceMap, Trace.endpoint] using htrace 1

lemma unit_mul_star {z : ℂ} (hz : ‖z‖ = 1) : z * star z = 1 := by
  rw [RCLike.star_def, RCLike.mul_conj, hz]
  norm_num

lemma phase_pairing {z : ℂ} (hz : ‖z‖ = 1) (u v : H1)
    (hu : traceMap u 1 = z * traceMap u 0)
    (hv : traceMap v 1 = z * traceMap v 0) :
    inner ℂ ((-Complex.I) • derivativeLp u) (baseLp v) =
      inner ℂ (baseLp u) ((-Complex.I) • derivativeLp v) := by
  apply sub_eq_zero.mp
  rw [boundary_form_trace, hu, hv, star_mul]
  have hs : star z * z = 1 := (mul_comm _ _).trans (unit_mul_star hz)
  have he : star (traceMap u 0) * star z * (z * traceMap v 0) =
      (star z * z) * (star (traceMap u 0) * traceMap v 0) := by ring
  rw [he, hs, one_mul, sub_self, mul_zero]

lemma pair_of_graph {T : Operator ℂ L2 L2} (h : T ≤ maximal)
    {v w : L2} (hm : (v, w) ∈ T.graph) :
    ∃ u : H1, baseLp u = v ∧ (-Complex.I) • derivativeLp u = w := by
  have hm' := LinearPMap.le_graph_of_le h hm
  rw [graphs.2] at hm'
  obtain ⟨u, hu⟩ := hm'
  exact ⟨u, congrArg Prod.fst hu, congrArg Prod.snd hu⟩

theorem phase_adjoint_equality :
    Specs.ExpandedFA.Unbounded.IntervalDerivativeExtensions.AdjointEquality := by
  intro z hz
  apply LinearPMap.eq_of_eq_graph
  ext ⟨v, w⟩
  constructor
  · intro hj
    have hle : adjointValue (phaseOperator z) ≤ maximal := by
      rw [← adjoint_equality]
      exact adjoint_le_of_le dense_domain (phase_dense z) (phase_extension z)
    obtain ⟨u, rfl, rfl⟩ := pair_of_graph hle hj
    obtain ⟨q, hq0, hq1⟩ := trace_surjective 1 z
    have hq : baseLp q ∈ (phaseOperator z).domain :=
      (phase_domain z _).mpr ⟨q, rfl, (boundaryCondition_iff z q).mpr (by rw [hq0, hq1, mul_one])⟩
    have he := (mem_hilbertAdjoint_graph_iff (phaseOperator z) (phase_dense z) _ _).mp hj ⟨baseLp q, hq⟩
    rw [phase_action] at he
    have hb := boundary_form_trace q u
    rw [he, sub_self, hq0, hq1, star_one, one_mul] at hb
    have hs : star z * traceMap u 1 = traceMap u 0 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hb.symm).resolve_left Complex.I_ne_zero)
    apply phase_graph_mem
    calc
      traceMap u 1 = (z * star z) * traceMap u 1 := by rw [unit_mul_star hz, one_mul]
      _ = z * (star z * traceMap u 1) := mul_assoc _ _ _
      _ = z * traceMap u 0 := by rw [hs]
  · intro hj
    obtain ⟨u, rfl, rfl⟩ := pair_of_graph LinearPMap.domRestrict_le hj
    obtain ⟨hdom, _⟩ := (mem_graph_iff (phaseOperator z) _).mp hj
    obtain ⟨u', heq, hbc⟩ := (phase_domain z _).mp hdom
    have heu : u' = u := baseMap_injective heq
    subst u'
    have hu := (boundaryCondition_iff z u).mp hbc
    apply (mem_hilbertAdjoint_graph_iff (phaseOperator z) (phase_dense z) _ _).mpr
    intro x
    obtain ⟨q, hqbase, hqact⟩ := pair_of_graph LinearPMap.domRestrict_le ((phaseOperator z).mem_graph x)
    obtain ⟨q', hq', hbcq⟩ := (phase_domain z _).mp x.property
    have heq : q' = q := baseMap_injective (hq'.trans hqbase.symm)
    subst q'
    rw [← hqbase, ← hqact]
    exact phase_pairing hz q u ((boundaryCondition_iff z q).mp hbcq) hu

theorem theta_selfAdjoint : Specs.ExpandedFA.Unbounded.IntervalDerivativeExtensions.SelfAdjoint := by
  intro θ
  exact ⟨phase_dense _, (phase_adjoint_equality _ (Complex.norm_exp_ofReal_mul_I θ)).symm⟩

lemma extension_le_maximal {T : Operator ℂ L2 L2}
    (he : minimal ≤ T) (hT : selfAdjointValue T) : T ≤ maximal := by
  rw [hT.2, ← adjoint_equality]
  exact adjoint_le_of_le dense_domain hT.1 he

lemma selfAdjoint_boundary_zero {T : Operator ℂ L2 L2} (hT : selfAdjointValue T)
    (u v : H1) (hu : (baseLp u, (-Complex.I) • derivativeLp u) ∈ T.graph)
    (hv : (baseLp v, (-Complex.I) • derivativeLp v) ∈ T.graph) :
    star (traceMap u 1) * traceMap v 1 - star (traceMap u 0) * traceMap v 0 = 0 := by
  have hu' := (mem_graph_iff T _).mp hu
  have hv' : (baseLp v, (-Complex.I) • derivativeLp v) ∈ (hilbertAdjoint T).graph := by
    change _ ∈ (adjointValue T).graph
    rw [← hT.2]
    exact hv
  have he := (mem_hilbertAdjoint_graph_iff T hT.1 _ _).mp hv' ⟨baseLp u, hu'.1⟩
  rw [hu'.2] at he
  have hb := boundary_form_trace u v
  rw [he, sub_self] at hb
  exact (mul_eq_zero.mp hb.symm).resolve_left Complex.I_ne_zero

lemma selfAdjoint_mem_of_boundary {T : Operator ℂ L2 L2} (hT : selfAdjointValue T)
    (hmax : T ≤ maximal) (u : H1)
    (hu : ∀ v : H1, (baseLp v, (-Complex.I) • derivativeLp v) ∈ T.graph →
      star (traceMap v 1) * traceMap u 1 - star (traceMap v 0) * traceMap u 0 = 0) :
    (baseLp u, (-Complex.I) • derivativeLp u) ∈ T.graph := by
  rw [hT.2]
  apply (mem_hilbertAdjoint_graph_iff T hT.1 _ _).mpr
  intro x
  obtain ⟨v, hb, ha⟩ := pair_of_graph hmax (T.mem_graph x)
  have hv : (baseLp v, (-Complex.I) • derivativeLp v) ∈ T.graph := by rw [hb, ha]; exact T.mem_graph x
  rw [← hb, ← ha]
  apply sub_eq_zero.mp
  rw [boundary_form_trace, hu v hv, mul_zero]

lemma selfAdjoint_trace_norm {T : Operator ℂ L2 L2} (hT : selfAdjointValue T)
    (u : H1) (hu : (baseLp u, (-Complex.I) • derivativeLp u) ∈ T.graph) :
    ‖traceMap u 1‖ = ‖traceMap u 0‖ := by
  have hb := selfAdjoint_boundary_zero hT u u hu hu
  have hn := congrArg norm (sub_eq_zero.mp hb)
  simp only [norm_mul, norm_star] at hn
  nlinarith [norm_nonneg (traceMap u 1), norm_nonneg (traceMap u 0)]

lemma selfAdjoint_nonzero_trace {T : Operator ℂ L2 L2}
    (he : minimal ≤ T) (hT : selfAdjointValue T) :
    ∃ u : H1, (baseLp u, (-Complex.I) • derivativeLp u) ∈ T.graph ∧ traceMap u 0 ≠ 0 := by
  classical
  by_contra hn
  have hzero : ∀ u : H1, (baseLp u, (-Complex.I) • derivativeLp u) ∈ T.graph →
      traceMap u 0 = 0 := by
    intro u hu
    by_contra h
    exact hn ⟨u, hu, h⟩
  have hzero' : ∀ u : H1, (baseLp u, (-Complex.I) • derivativeLp u) ∈ T.graph →
      traceMap u 1 = 0 := by
    intro u hu
    apply norm_eq_zero.mp
    rw [selfAdjoint_trace_norm hT u hu, hzero u hu, norm_zero]
  obtain ⟨q, hq0, hq1⟩ := trace_surjective 1 1
  have hq := selfAdjoint_mem_of_boundary hT (extension_le_maximal he hT) q (by
    intro v hv
    rw [hzero v hv, hzero' v hv, star_zero, zero_mul, zero_mul, sub_self])
  exact one_ne_zero (hq0.symm.trans (hzero q hq))

lemma selfAdjoint_is_phase {T : Operator ℂ L2 L2}
    (he : minimal ≤ T) (hT : selfAdjointValue T) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ T = phaseOperator z := by
  obtain ⟨q, hq, hq0⟩ := selfAdjoint_nonzero_trace he hT
  let z := traceMap q 1 / traceMap q 0
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    rw [norm_div, selfAdjoint_trace_norm hT q hq, div_self (norm_ne_zero_iff.mpr hq0)]
  have hqz : traceMap q 1 = z * traceMap q 0 := by
    dsimp [z]
    rw [div_mul_cancel₀ _ hq0]
  have hline : ∀ u : H1, (baseLp u, (-Complex.I) • derivativeLp u) ∈ T.graph →
      traceMap u 1 = z * traceMap u 0 := by
    intro u hu
    have hb := selfAdjoint_boundary_zero hT q u hq hu
    rw [hqz, star_mul] at hb
    have hf : star (traceMap q 0) * (star z * traceMap u 1 - traceMap u 0) = 0 := by
      linear_combination hb
    have hs : star z * traceMap u 1 = traceMap u 0 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (by simpa using hq0))
    calc
      traceMap u 1 = (z * star z) * traceMap u 1 := by rw [unit_mul_star hz, one_mul]
      _ = z * (star z * traceMap u 1) := mul_assoc _ _ _
      _ = z * traceMap u 0 := by rw [hs]
  refine ⟨z, hz, le_antisymm ?_ ?_⟩
  · apply LinearPMap.le_of_le_graph
    rintro ⟨v, w⟩ hv
    obtain ⟨u, rfl, rfl⟩ := pair_of_graph (extension_le_maximal he hT) hv
    exact phase_graph_mem z u (hline u hv)
  · apply LinearPMap.le_of_le_graph
    rintro ⟨v, w⟩ hv
    obtain ⟨u, rfl, rfl⟩ := pair_of_graph LinearPMap.domRestrict_le hv
    obtain ⟨hu, _⟩ := (mem_graph_iff _ _).mp hv
    obtain ⟨u', hu', hbc⟩ := (phase_domain z _).mp hu
    have heu : u' = u := baseMap_injective hu'
    subst u'
    have hu := (boundaryCondition_iff z u).mp hbc
    apply selfAdjoint_mem_of_boundary hT (extension_le_maximal he hT) u
    intro v hv
    have hb := boundary_form_trace v u
    rw [phase_pairing hz v u (hline v hv) hu, sub_self] at hb
    exact (mul_eq_zero.mp hb.symm).resolve_left Complex.I_ne_zero

/-- Choosing a half-open angular interval retains θ=0 and excludes 2π. -/
lemma unit_phase_angle {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ θ ∈ Ico (0 : ℝ) (2 * Real.pi), Complex.exp ((θ : ℂ) * Complex.I) = z := by
  obtain ⟨α, hα⟩ := Complex.norm_eq_one_iff'.mp hz
  by_cases hα0 : 0 ≤ α
  · refine ⟨α, ⟨hα0, ?_⟩, hα.2⟩
    linarith [hα.1.2, Real.pi_pos]
  · refine ⟨α + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · linarith [hα.1.1, Real.pi_pos]
    · linarith
    · rw [Complex.ofReal_add, add_mul, Complex.exp_add]
      have hper : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
        simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using Complex.exp_two_pi_mul_I
      rw [hper, mul_one, hα.2]

theorem classification : Specs.ExpandedFA.Unbounded.IntervalDerivativeExtensions.Classification := by
  intro T
  constructor
  · rintro ⟨he, hT⟩
    obtain ⟨z, hz, h⟩ := selfAdjoint_is_phase he hT
    obtain ⟨θ, hθ, hθz⟩ := unit_phase_angle hz
    exact ⟨θ, hθ, by rw [h, thetaOperator, hθz]⟩
  · rintro ⟨θ, _, rfl⟩
    exact ⟨phase_extension _, theta_selfAdjoint θ⟩

end ExpandedFA.Unbounded.IntervalDerivative
