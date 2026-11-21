import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.MaximalFlow
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.MaximalIntegralCurves
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.DerivativeCriterion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.CkDependence
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.IntermediateValue

/-! The flow clauses of M06.03, using the actual maximal integral curves. -/
noncomputable section
namespace SmoothManifolds.MaximalFlow
open ModelData AtlasData MapData TangentBundleData VectorFieldData IntegralCurveData
  MaximalFlowData Set Filter
open scoped Topology ContDiff
universe u

/-- Choice is made only after the actual full existence proposition is supplied. -/
theorem maximal_family_exists_conditional
    (hExists : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_existsType.{u})
    (_hUnique : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_uniqueType.{u})
    (_hOverlap : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.overlap_uniqueType.{u}) :
    Specs.SmoothManifolds.Ch06.MaximalFlow.maximal_family_existsType.{u} := by
  classical
  intro n M _ S B X
  choose I γ hγ using hExists S B X
  exact ⟨⟨I, γ⟩, hγ⟩

/-- Translation preserves the actual open interval, including unbounded endpoints. -/
def translatedInterval (I : D13Unified.OpenTimeInterval) (s : ℝ) :
    D13Unified.OpenTimeInterval where
  carrier := {t | s + t ∈ I.carrier}
  nonempty := by
    obtain ⟨t, ht⟩ := I.nonempty
    exact ⟨t - s, by simpa using ht⟩
  ordConnected := I.ordConnected.preimage_mono (fun _ _ h => by simpa [add_comm] using add_le_add_left h s)
  isOpen := I.isOpen.preimage (continuous_const.add continuous_id)

/-- The derivative and smoothness equations are invariant under translation. -/
theorem integralCurve_translate {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} {I : D13Unified.OpenTimeInterval} {γ : ℝ → M}
    (hγ : IsIntegralCurveOn X I.carrier γ) (s : ℝ) :
    IsIntegralCurveOn X (translatedInterval I s).carrier (fun t => γ (s + t)) := by
  constructor
  · exact hγ.1.comp (continuous_const.add continuous_id).continuousOn (fun _ h => h)
  · intro t ht e he hp
    obtain ⟨hc, hd⟩ := hγ.2 (s + t) ht e he hp
    exact ⟨hc.comp t (contDiffAt_const.add contDiffAt_id), hd.comp_const_add s t⟩

/-- Locality of the integral-curve predicate on open time neighborhoods. -/
theorem integralCurve_of_local {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} {K : Set ℝ} {δ : ℝ → M}
    (h : ∀ t ∈ K, ∃ (U : Set ℝ) (γ : ℝ → M), IsOpen U ∧ t ∈ U ∧
      IsIntegralCurveOn X U γ ∧ δ =ᶠ[𝓝 t] γ) : IsIntegralCurveOn X K δ := by
  constructor
  · intro t ht
    obtain ⟨U, γ, hU, htU, hγ, heq⟩ := h t ht
    exact ((hγ.1.continuousAt (hU.mem_nhds htU)).congr heq.symm).continuousWithinAt
  · intro t ht e he hp
    obtain ⟨U, γ, hU, htU, hγ, heq⟩ := h t ht
    have hv : δ t = γ t := heq.eq_of_nhds
    have hcoord : (fun s => (e (δ s)).val) =ᶠ[𝓝 t] (fun s => (e (γ s)).val) :=
      heq.fun_comp (fun p => (e p).val)
    obtain ⟨hc, hd⟩ := hγ.2 t htU e he (hv ▸ hp)
    refine ⟨hc.congr_of_eventuallyEq hcoord, ?_⟩
    apply (hd.congr_of_eventuallyEq hcoord).congr_deriv
    exact congrArg (fun q : e.source =>
      B.fiberCoordinates.equiv e he q.val q.property (X.val q.val)) (show (⟨γ t, hv ▸ hp⟩ : e.source) = ⟨δ t, hp⟩ from Subtype.ext hv.symm)

/-- A total representative for gluing, without off-domain assertions. -/
def gluedCurve {M : Type u} (I : D13Unified.OpenTimeInterval) (γ η : ℝ → M) : ℝ → M := by
  classical
  exact I.carrier.piecewise γ η

/-- Gluing solutions that agree on the overlap preserves the actual equation. -/
theorem integralCurve_glue {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} {I J : D13Unified.OpenTimeInterval} {γ η : ℝ → M}
    (hγ : IsIntegralCurveOn X I.carrier γ) (hη : IsIntegralCurveOn X J.carrier η)
    (heq : EqOn γ η (I.carrier ∩ J.carrier)) :
    IsIntegralCurveOn X (I.carrier ∪ J.carrier) (gluedCurve I γ η) := by
  classical
  change IsIntegralCurveOn X (I.carrier ∪ J.carrier) (I.carrier.piecewise γ η)
  apply integralCurve_of_local
  intro t ht
  rcases ht with ht | ht
  · refine ⟨I.carrier, γ, I.isOpen, ht, hγ, ?_⟩
    filter_upwards [I.isOpen.mem_nhds ht] with s hs
    exact piecewise_eq_of_mem I.carrier γ η hs
  · refine ⟨J.carrier, η, J.isOpen, ht, hη, ?_⟩
    filter_upwards [J.isOpen.mem_nhds ht] with s hs
    by_cases hi : s ∈ I.carrier
    · simpa only [piecewise_eq_of_mem I.carrier γ η hi] using heq ⟨hi, hs⟩
    · exact piecewise_eq_of_notMem I.carrier γ η hi

/-- The union of two overlapping open intervals is again an open interval. -/
def unionInterval (I J : D13Unified.OpenTimeInterval)
    (hne : (I.carrier ∩ J.carrier).Nonempty) : D13Unified.OpenTimeInterval where
  carrier := I.carrier ∪ J.carrier
  nonempty := I.nonempty.mono subset_union_left
  ordConnected := (IsPreconnected.union' hne I.ordConnected.isPreconnected J.ordConnected.isPreconnected).ordConnected
  isOpen := I.isOpen.union J.isOpen

/-- A maximal curve absorbs every solution meeting it at any common time.
The comparison interval need not contain zero; the union does. -/
theorem maximalThrough_contains
    (hOverlap : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.overlap_uniqueType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} {p : M} {I J : D13Unified.OpenTimeInterval} {γ η : ℝ → M}
    (hγ : IsMaximalThrough X p I γ) (hη : IsIntegralCurveOn X J.carrier η)
    {s : ℝ} (hs : s ∈ I.carrier ∩ J.carrier) (heq : γ s = η s) :
    J.carrier ⊆ I.carrier ∧ EqOn γ η J.carrier := by
  classical
  have hAgree := hOverlap S B X I J γ η hγ.2.2.1 hη s hs heq
  let K := unionInterval I J ⟨s, hs⟩
  have hδ := integralCurve_glue hγ.2.2.1 hη hAgree
  have h0 : 0 ∈ K.carrier := Or.inl hγ.1
  have hδ0 : gluedCurve I γ η 0 = p := by
    simpa [gluedCurve, hγ.1] using hγ.2.1
  have hSub := (hγ.2.2.2 K (gluedCurve I γ η) h0 hδ0 hδ).1
  refine ⟨fun t ht => hSub (Or.inr ht), ?_⟩
  intro t ht
  exact hAgree ⟨hSub (Or.inr ht), ht⟩

/-- Time translation preserves maximality. The back-translated competitor is
absorbed using its meeting time `s`, rather than assuming it contains zero. -/
theorem maximalThrough_translate
    (hOverlap : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.overlap_uniqueType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} {p : M} {I : D13Unified.OpenTimeInterval} {γ : ℝ → M}
    (hγ : IsMaximalThrough X p I γ) {s : ℝ} (hs : s ∈ I.carrier) :
    IsMaximalThrough X (γ s) (translatedInterval I s) (fun t => γ (s + t)) := by
  refine ⟨by simpa [translatedInterval] using hs, by simp,
    integralCurve_translate hγ.2.2.1 s, ?_⟩
  intro J η hJ0 hη0 hη
  have hsJ : s ∈ (translatedInterval J (-s)).carrier := by
    simpa [translatedInterval] using hJ0
  have hsEq : γ s = η (-s + s) := by simpa using hη0.symm
  obtain ⟨hSub, hEq⟩ := maximalThrough_contains hOverlap hγ
    (integralCurve_translate hη (-s)) ⟨hs, hsJ⟩ hsEq
  constructor
  · intro t ht
    have ht' : s + t ∈ (translatedInterval J (-s)).carrier := by
      simpa [translatedInterval] using ht
    exact hSub ht'
  · intro t ht
    have ht' : s + t ∈ (translatedInterval J (-s)).carrier := by
      simpa [translatedInterval] using ht
    simpa using hEq ht'

/-- The full lifespan and composition laws, with precisely the contract's three
ordered prerequisite propositions and no assumed regularity of the flow. -/
theorem lifespan_flow_law_conditional
    (_hExists : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_existsType.{u})
    (hUnique : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_uniqueType.{u})
    (hOverlap : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.overlap_uniqueType.{u}) :
    Specs.SmoothManifolds.Ch06.MaximalFlow.lifespan_flow_lawType.{u} := by
  intro n M _ S B X F hF p s hs
  have hShift := maximalThrough_translate hOverlap (hF p) hs
  have hEq := hUnique S B X (F.curve p s) (F.interval (F.curve p s))
    (translatedInterval (F.interval p) s) (F.curve (F.curve p s))
    (fun t => F.curve p (s + t)) (hF (F.curve p s)) hShift
  refine ⟨hEq.1, ?_⟩
  intro t ht
  apply hEq.2
  rw [hEq.1]
  exact ht

theorem maximal_family_exists :
    Specs.SmoothManifolds.Ch06.MaximalFlow.maximal_family_existsType.{u} :=
  maximal_family_exists_conditional IntegralCurves.maximal_exists
    IntegralCurves.maximal_unique IntegralCurves.overlap_unique

theorem lifespan_flow_law :
    Specs.SmoothManifolds.Ch06.MaximalFlow.lifespan_flow_lawType.{u} :=
  lifespan_flow_law_conditional IntegralCurves.maximal_exists
    IntegralCurves.maximal_unique IntegralCurves.overlap_unique

/-- The time domains are open sections of the actual joint domain. -/
theorem timeDomain_isOpen {M : Type u} [TopologicalSpace M] (F : CurveFamily M)
    (hD : IsOpen (flowDomain F)) (s : ℝ) : IsOpen (timeDomain F s) :=
  hD.preimage (continuous_const.prodMk continuous_id)

/-- Restricting joint product-coordinate smoothness to a fixed time gives a
smooth map between any open source and target restrictions. -/
theorem timeMap_smooth {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (F : CurveFamily M) (s : ℝ)
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (g : U → V)
    (hg : ∀ p, (g p).val = F.curve p.val s)
    (hSmooth : ∀ p ∈ U, FlowSmoothAt S F (s, p)) :
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (openSubsetAtlas S.smoothStructure.val V hV) g := by
  intro p
  have hi : ContinuousAt (fun q : U => (s, q.val)) p :=
    continuousAt_const.prodMk continuousAt_subtype_val
  have hc : ContinuousAt (fun q : U => F.curve q.val s) p := by
    simpa only [Function.comp_def, flow] using ContinuousAt.comp (f := fun q : U => (s, q.val)) (hSmooth p.val p.property).1 hi
  have hcg : ContinuousAt (fun q : U => (g q).val) p :=
    hc.congr (Eventually.of_forall (fun q => (hg q).symm))
  refine ⟨tendsto_subtype_rng.mpr hcg, ?_⟩
  rintro _ ⟨hne, e, he, rfl⟩ _ ⟨hne', d, hd, rfl⟩ hp hgp
  have hpe : p.val ∈ e.source := by simpa using hp
  have hpd : flow F (s, p.val) ∈ d.source := by simpa [flow, ← hg p] using hgp
  obtain ⟨W, hW, hpW, G, hG, hEq⟩ := (hSmooth p.val p.property).2 e he d hd hpe hpd
  refine ⟨(fun x : Euclidean n => (s, x)) ⁻¹' W,
    hW.preimage (continuous_const.prodMk continuous_id), hpW,
    (fun x => G (s, x)), ?_, ?_⟩
  · exact hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  · have hEq' := hEq.comp_tendsto
      (continuousAt_const.prodMk continuousAt_subtype_val :
        ContinuousAt (fun q : U => (s, q.val)) p)
    filter_upwards [hEq'] with q hq
    change G (s, (e q.val).val) = (d (g q).val).val
    rw [hg q]
    exact hq

/-- Algebraic inverse time maps. This uses only the exact lifespan and flow laws,
and does not assert continuity or openness. -/
def timeEquiv {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (hLaw : ∀ (p : M) (s : ℝ), s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t : ℝ, s + t ∈ (F.interval p).carrier →
        F.curve (F.curve p s) t = F.curve p (s + t)) (s : ℝ) :
    timeDomain F s ≃ timeDomain F (-s) where
  toFun p := ⟨F.curve p.val s, by
    change -s ∈ (F.interval (F.curve p.val s)).carrier
    rw [(hLaw p.val s p.property).1]
    simpa using (hF p.val).1⟩
  invFun q := ⟨F.curve q.val (-s), by
    change s ∈ (F.interval (F.curve q.val (-s))).carrier
    rw [(hLaw q.val (-s) q.property).1]
    simpa using (hF q.val).1⟩
  left_inv p := by
    apply Subtype.ext
    change F.curve (F.curve p.val s) (-s) = p.val
    rw [(hLaw p.val s p.property).2 (-s) (by simpa using (hF p.val).1)]
    simpa using (hF p.val).2.1
  right_inv q := by
    apply Subtype.ext
    change F.curve (F.curve q.val (-s)) s = q.val
    rw [(hLaw q.val (-s) q.property).2 s (by simpa using (hF q.val).1)]
    simpa using (hF q.val).2.1

/-- Once joint openness and smoothness have been proved, the diffeomorphism
clause follows with exactly the two specified time maps. This helper isolates
that implication without treating its hypothesis as a proved upstream fact. -/
theorem time_diffeomorph_of_open_smooth
    (hExists : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_existsType.{u})
    (hUnique : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_uniqueType.{u})
    (hOverlap : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.overlap_uniqueType.{u})
    (hJoint : Specs.SmoothManifolds.Ch06.MaximalFlow.domain_open_smoothType.{u}) :
    Specs.SmoothManifolds.Ch06.MaximalFlow.time_diffeomorphType.{u} := by
  intro n M _ S B X F hF s
  obtain ⟨hD, hSmooth⟩ := hJoint S B X F hF
  have hLaw := lifespan_flow_law_conditional hExists hUnique hOverlap S B X F hF
  let E := timeEquiv F hF hLaw s
  have hU := timeDomain_isOpen F hD s
  have hV := timeDomain_isOpen F hD (-s)
  refine ⟨hU, hV, ⟨E, ?_, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · exact timeMap_smooth S F s hU hV E (fun _ => rfl) (fun p hp => hSmooth (s, p) hp)
  · exact timeMap_smooth S F (-s) hV hU E.symm (fun _ => rfl)
      (fun p hp => hSmooth (-s, p) hp)

/-- Euclidean coordinates as points of the shared unconstrained model. -/
def euclideanModelPoint {n : ℕ} (y : Euclidean n) : ModelSpace n .euclidean :=
  ⟨y, mem_univ _⟩

theorem continuous_euclideanModelPoint (n : ℕ) :
    Continuous (@euclideanModelPoint n) := continuous_id.subtype_mk _

/-- Actual open state domain of a boundaryless chart, with no extension to all
states and no implicit assumption that a trajectory stays in this chart. -/
def chartStateDomain {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) : Set (Euclidean n) :=
  euclideanModelPoint ⁻¹' e.target

theorem chartStateDomain_isOpen {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) : IsOpen (chartStateDomain e) :=
  e.open_target.preimage (continuous_euclideanModelPoint n)

/-- Actual intrinsic coefficients in a chart. Zero outside its domain is only
an evaluation convention; all regularity assertions retain `chartStateDomain`. -/
def chartCoefficient {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (y : Euclidean n) : Euclidean n := by
  classical
  exact if h : e.symm (euclideanModelPoint y) ∈ e.source then
    B.fiberCoordinates.equiv e he _ h (X.val _) else 0

/-- Smoothness of the section gives genuine C-infinity state coefficients on
the actual open chart domain. -/
theorem chartCoefficient_contDiffOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chartCoefficient B X e he) (chartStateDomain e) := by
  intro y hy
  have hp : e.symm (euclideanModelPoint y) ∈ e.source := e.map_target hy
  obtain ⟨U, hU, hpU, W, hW, hEq⟩ :=
    VectorFields.field_local_coordinates S B X (e.symm (euclideanModelPoint y)) e he hp
  have hv : (e (e.symm (euclideanModelPoint y))).val = y := congrArg Subtype.val (e.right_inv hy)
  have hyU : y ∈ U := hv ▸ hpU
  have hi : ContinuousAt (fun z => e.symm (euclideanModelPoint z)) y :=
    e.continuousAt_symm hy |>.comp (continuous_euclideanModelPoint n).continuousAt
  have hEq' := hi.eventually hEq
  have hCW : chartCoefficient B X e he =ᶠ[𝓝 y] W := by
    filter_upwards [(chartStateDomain_isOpen e).mem_nhds hy, hEq'] with z hz hzEq
    obtain ⟨hq, hqW⟩ := hzEq
    have hzVal : (e (e.symm (euclideanModelPoint z))).val = z :=
      congrArg Subtype.val (e.right_inv hz)
    unfold chartCoefficient
    rw [dite_eq_left hq]
    exact hqW.symm.trans (congrArg W hzVal)
  exact ((hW.contDiffAt (hU.mem_nhds hyU)).congr_of_eventuallyEq hCW).contDiffWithinAt

/-- The chart ODE is continuous on its recorded open domain. -/
def chartODE {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    D13Unified.AutonomousODE (Euclidean n) where
  domain := chartStateDomain e
  isOpen_domain := chartStateDomain_isOpen e
  field := fun y => chartCoefficient B X e he y.val
  continuous_field := (chartCoefficient_contDiffOn B X e he).continuousOn.domRestrict

/-- Evaluating the chart ODE on its domain recovers precisely its intrinsic coefficients. -/
theorem chartODE_eval {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    {y : Euclidean n} (hy : y ∈ chartStateDomain e) :
    (chartODE B X e he).eval y = chartCoefficient B X e he y := by
  simp [D13Unified.AutonomousODE.eval,
    Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue, chartODE, hy]

/-- Evaluation at an actual chart point is the original vector field's
intrinsic coordinate vector, rather than a chosen unrelated Euclidean field. -/
theorem chartCoefficient_apply {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    {p : M} (hp : p ∈ e.source) :
    chartCoefficient B X e he (e p).val = B.fiberCoordinates.equiv e he p hp (X.val p) := by
  have hv : e.symm (euclideanModelPoint (e p).val) = p := e.left_inv hp
  have hp' : e.symm (euclideanModelPoint (e p).val) ∈ e.source := e.map_target (e.map_source hp)
  unfold chartCoefficient
  rw [dite_eq_left hp']
  exact congrArg (fun q : e.source =>
    B.fiberCoordinates.equiv e he q.val q.property (X.val q.val))
    (show (⟨e.symm (euclideanModelPoint (e p).val), hp'⟩ : e.source) = ⟨p, hp⟩
      from Subtype.ext hv)

/-- The zero-extension evaluation convention does not affect smoothness on
the actual open domain of the chart ODE. -/
theorem chartODE_contDiffOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chartODE B X e he).eval (chartODE B X e he).domain :=
  (chartCoefficient_contDiffOn B X e he).congr (fun _ hy => chartODE_eval B X e he hy)

/-- The local Lipschitz hypothesis is derived on the true open time-state domain;
it is not an additional assumed certificate. -/
theorem chartODE_locallyLipschitz {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    (chartODE B X e he).toODE.LocallyLipschitzInState := by
  apply D13Unified.AutonomousODE.locallyLipschitzInState_of_contDiffOn
  exact (chartODE_contDiffOn B X e he).of_le (by simp)

/-- Smooth dependence for the canonical Euclidean chart solution, on its actual
maximal solution domain. This statement does not yet identify that solution
with the manifold family outside the chart. -/
theorem chartODE_flow_regular {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    IsOpen (D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he)) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × Euclidean n => D13Unified.Ch06.StateDerivative.flow (chartODE B X e he) q.1 q.2)
      (D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he)) := by
  have hC := chartODE_contDiffOn B X e he
  have hC1 : ContDiffOn ℝ 1 (chartODE B X e he).eval (chartODE B X e he).domain :=
    hC.of_le (by simp)
  refine ⟨D13Unified.Ch06.C1Dependence.isOpen_flowDomain _ hC1, ?_⟩
  rw [contDiffOn_infty]
  intro k
  by_cases hk : k = 0
  · subst k
    exact (D13Unified.Ch06.CkDependence.autonomous_joint_ck 1 le_rfl _ hC1).of_le (by simp)
  · exact D13Unified.Ch06.CkDependence.autonomous_joint_ck k
      (Nat.one_le_iff_ne_zero.mpr hk) _ (hC.of_le (by simp))

/-- On an open time interval, the intrinsic equation in one chart implies the
same equation in every chart. The transition Jacobian acts on the original
intrinsic field, so no coordinate compatibility is assumed. -/
theorem integralCurve_of_oneChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} {I : D13Unified.OpenTimeInterval} {γ : ℝ → M}
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hCont : ContinuousOn γ I.carrier)
    (hLocal : ∀ t ∈ I.carrier, ∃ hp : γ t ∈ e.source,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (γ s)).val) t ∧
      HasDerivAt (fun s => (e (γ s)).val)
        (B.fiberCoordinates.equiv e he (γ t) hp (X.val (γ t))) t) :
    IsIntegralCurveOn X I.carrier γ := by
  refine ⟨hCont, ?_⟩
  intro t ht d hd hpd
  obtain ⟨hp, hc, hDer⟩ := hLocal t ht
  obtain ⟨U, hU, hpU, G, hG, hRep⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d hd) hp hpd
  have hGAt := hG.contDiffAt (hU.mem_nhds hpU)
  have hEq := hRep.comp_tendsto (hCont.continuousAt (I.isOpen.mem_nhds ht))
  have hJac := TangentBundle.transition_jacobian S B.fiberCoordinates e d he hd
    (γ t) hp hpd U G hU hpU hG hRep (X.val (γ t))
  refine ⟨(hGAt.comp t hc).congr_of_eventuallyEq hEq.symm, ?_⟩
  rw [hJac]
  exact ((hGAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hDer)
    |>.congr_of_eventuallyEq hEq.symm

/-- Lifting a smooth Euclidean chart solution produces an actual integral
curve on the manifold, with the frozen all-charts definition. -/
theorem integralCurve_chartLift {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (I : D13Unified.OpenTimeInterval) (x : ℝ → Euclidean n)
    (hStay : ∀ t ∈ I.carrier, x t ∈ chartStateDomain e)
    (hSmooth : ∀ t ∈ I.carrier, ContDiffAt ℝ (⊤ : ℕ∞) x t)
    (hDer : ∀ t ∈ I.carrier, HasDerivAt x (chartCoefficient B X e he (x t)) t) :
    IsIntegralCurveOn X I.carrier (fun t => e.symm (euclideanModelPoint (x t))) := by
  have hCont : ContinuousOn (fun t => e.symm (euclideanModelPoint (x t))) I.carrier := by
    intro t ht
    have hi : ContinuousAt (fun s => euclideanModelPoint (x s)) t :=
      (continuous_euclideanModelPoint n).continuousAt.comp (hSmooth t ht).continuousAt
    exact (ContinuousAt.comp (f := fun s => euclideanModelPoint (x s))
      (e.continuousAt_symm (hStay t ht)) hi).continuousWithinAt
  apply integralCurve_of_oneChart e he hCont
  intro t ht
  have hp := e.map_target (hStay t ht)
  have hEq : (fun s => (e (e.symm (euclideanModelPoint (x s)))).val) =ᶠ[𝓝 t] x := by
    have hNear := I.isOpen.mem_nhds ht
    filter_upwards [hNear] with s hs
    exact congrArg Subtype.val (e.right_inv (hStay s hs))
  refine ⟨hp, (hSmooth t ht).congr_of_eventuallyEq hEq, ?_⟩
  have hVel : chartCoefficient B X e he (x t) =
      B.fiberCoordinates.equiv e he _ hp (X.val _) := by
    unfold chartCoefficient
    rw [dite_eq_left hp]
  exact ((hDer t ht).congr_of_eventuallyEq hEq).congr_deriv hVel

/-- Lift the actual canonical Euclidean chart solution, retaining its entire
recorded interval. No manifold-wide smoothness claim enters this proof. -/
theorem integralCurve_canonicalChartLift {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : SmoothField B) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (y : Euclidean n) (hy : y ∈ chartStateDomain e) :
    IsIntegralCurveOn X
      (D13Unified.Ch06.StateDerivative.flowInterval (chartODE B X e he) y).carrier
      (fun t => e.symm (euclideanModelPoint
        (D13Unified.Ch06.StateDerivative.flow (chartODE B X e he) t y))) := by
  have hC1 : ContDiffOn ℝ 1 (chartODE B X e he).eval (chartODE B X e he).domain :=
    (chartODE_contDiffOn B X e he).of_le (by simp)
  have hIVP := D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 hy
  have hReg := chartODE_flow_regular B X e he
  have hStay : ∀ t ∈ (D13Unified.Ch06.StateDerivative.flowInterval (chartODE B X e he) y).carrier,
      D13Unified.Ch06.StateDerivative.flow (chartODE B X e he) t y ∈ chartStateDomain e :=
    hIVP.1.2.1
  apply integralCurve_chartLift B X e he _ _ hStay
  · intro t ht
    have hMem : (t, y) ∈ D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he) := ⟨hy, ht⟩
    have hAt := hReg.2.contDiffAt (hReg.1.mem_nhds hMem)
    exact ContDiffAt.comp (f := fun s : ℝ => (s, y)) t hAt
      (contDiffAt_id.prodMk contDiffAt_const)
  · intro t ht
    have hDer := hIVP.1.2.2 t ht
    simpa only [D13Unified.AutonomousODE.toODE_eval, chartODE_eval B X e he (hStay t ht)]
      using hDer

/-- The canonical chart solution is the restriction of the supplied maximal
manifold curve. This is the actual bridge from Euclidean ODEs to that family. -/
theorem canonicalChartLift_restricts {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) :
    (D13Unified.Ch06.StateDerivative.flowInterval (chartODE B X e he) (e p).val).carrier ⊆
        (F.interval p).carrier ∧
      EqOn (F.curve p)
        (fun t => e.symm (euclideanModelPoint
          (D13Unified.Ch06.StateDerivative.flow (chartODE B X e he) t (e p).val)))
        (D13Unified.Ch06.StateDerivative.flowInterval (chartODE B X e he) (e p).val).carrier := by
  have hy : (e p).val ∈ chartStateDomain e := e.map_source hp
  have hC1 : ContDiffOn ℝ 1 (chartODE B X e he).eval (chartODE B X e he).domain :=
    (chartODE_contDiffOn B X e he).of_le (by simp)
  have hIVP := D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 hy
  apply (hF p).2.2.2 _ _ hIVP.2.1
  · have hZero : D13Unified.Ch06.StateDerivative.flow (chartODE B X e he) 0 (e p).val = (e p).val :=
      hIVP.2.2
    rw [hZero]
    exact e.left_inv hp
  · exact integralCurve_canonicalChartLift B X e he (e p).val hy

/-- Every pair in a chart solution domain, with initial point in that chart,
is in the maximal manifold domain and has the expected value there. -/
theorem chartFlow_agrees {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (z : ℝ × M) (hp : z.2 ∈ e.source)
    (hz : (z.1, (e z.2).val) ∈ D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he)) :
    z ∈ flowDomain F ∧
      flow F z = e.symm (euclideanModelPoint
        (D13Unified.Ch06.StateDerivative.flow (chartODE B X e he) z.1 (e z.2).val)) := by
  have h := canonicalChartLift_restricts F hF e he z.2 hp
  exact ⟨h.1 hz.2, h.2 hz.2⟩

/-- Each chart solution domain pulls back to an open neighborhood contained in
the manifold flow domain. In particular the domain is a neighborhood of every
zero-time pair, before any continuation argument along nonzero times. -/
theorem flowDomain_mem_nhds_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} (F : CurveFamily M) (hF : IsMaximalFamily X F) (p : M) :
    flowDomain F ∈ 𝓝 ((0 : ℝ), p) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  have hC1 : ContDiffOn ℝ 1 (chartODE B X e he).eval (chartODE B X e he).domain :=
    (chartODE_contDiffOn B X e he).of_le (by simp)
  have hIVP := D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 (e.map_source hp)
  have hReg := chartODE_flow_regular B X e he
  have hCoord : ContinuousAt (fun z : ℝ × M => (z.1, (e z.2).val)) (0, p) :=
    continuousAt_fst.prodMk
      (continuous_subtype_val.continuousAt.comp ((e.continuousAt hp).comp continuousAt_snd))
  have hNear := hCoord.preimage_mem_nhds (hReg.1.mem_nhds ⟨e.map_source hp, hIVP.2.1⟩)
  filter_upwards [hNear, (e.open_source.preimage continuous_snd).mem_nhds hp] with z hz hzp
  exact (chartFlow_agrees F hF e he z hzp hz).1

/-- In a chart solution neighborhood the manifold flow is genuinely continuous
in both variables, by equality with the lifted canonical Euclidean solution. -/
theorem flow_continuousAt_of_chartFlow {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (z : ℝ × M) (hp : z.2 ∈ e.source)
    (hz : (z.1, (e z.2).val) ∈ D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he)) :
    ContinuousAt (flow F) z := by
  let A : ℝ × M → ℝ × Euclidean n := fun w => (w.1, (e w.2).val)
  let Ψ : ℝ × Euclidean n → Euclidean n :=
    fun w => D13Unified.Ch06.StateDerivative.flow (chartODE B X e he) w.1 w.2
  have hA : ContinuousAt A z := continuousAt_fst.prodMk
    (continuous_subtype_val.continuousAt.comp ((e.continuousAt hp).comp continuousAt_snd))
  have hReg := chartODE_flow_regular B X e he
  have hΨ : ContinuousAt Ψ (A z) := hReg.2.continuousOn.continuousAt (hReg.1.mem_nhds hz)
  have hC1 : ContDiffOn ℝ 1 (chartODE B X e he).eval (chartODE B X e he).domain :=
    (chartODE_contDiffOn B X e he).of_le (by simp)
  have hIVP := D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 hz.1
  have hState : Ψ (A z) ∈ chartStateDomain e := hIVP.1.2.1 z.1 hz.2
  have hModel : ContinuousAt (fun w => euclideanModelPoint (Ψ (A w))) z :=
    (continuous_euclideanModelPoint n).continuousAt.comp (hΨ.comp hA)
  have hLift : ContinuousAt (fun w => e.symm (euclideanModelPoint (Ψ (A w)))) z :=
    ContinuousAt.comp (f := fun w => euclideanModelPoint (Ψ (A w)))
      (e.continuousAt_symm hState) hModel
  have hEq : flow F =ᶠ[𝓝 z] (fun w => e.symm (euclideanModelPoint (Ψ (A w)))) := by
    filter_upwards [hA.preimage_mem_nhds (hReg.1.mem_nhds hz),
      (e.open_source.preimage continuous_snd).mem_nhds hp] with w hw hwp
    exact (chartFlow_agrees F hF e he w hwp hw).2
  exact hLift.congr hEq.symm

/-- Joint continuity at every zero-time point, including arbitrary empty and
zero-dimensional bases under the same quantified interface. -/
theorem flow_continuousAt_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} (F : CurveFamily M) (hF : IsMaximalFamily X F) (p : M) :
    ContinuousAt (flow F) ((0 : ℝ), p) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  have hC1 : ContDiffOn ℝ 1 (chartODE B X e he).eval (chartODE B X e he).domain :=
    (chartODE_contDiffOn B X e he).of_le (by simp)
  have hIVP := D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 (e.map_source hp)
  exact flow_continuousAt_of_chartFlow F hF e he (0, p) hp ⟨e.map_source hp, hIVP.2.1⟩

/-- The all-charts joint smoothness test at time zero. This is the local starting
point for continuation along a trajectory; no global patching is claimed here. -/
theorem flow_smoothAt_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} (F : CurveFamily M) (hF : IsMaximalFamily X F) (p : M) :
    FlowSmoothAt S F ((0 : ℝ), p) := by
  have hc := flow_continuousAt_zero F hF p
  refine ⟨hc, ?_⟩
  intro e he d hd hp hpd
  have hZero : flow F (0, p) = p := (hF p).2.1
  rw [hZero] at hpd
  obtain ⟨V, hV, hpV, G, hG, hRep⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d hd) hp hpd
  let A : ℝ × M → ℝ × Euclidean n := fun w => (w.1, (e w.2).val)
  let Ψ : ℝ × Euclidean n → Euclidean n :=
    fun w => D13Unified.Ch06.StateDerivative.flow (chartODE B X e he) w.1 w.2
  let D := D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he)
  have hReg := chartODE_flow_regular B X e he
  have hC1 : ContDiffOn ℝ 1 (chartODE B X e he).eval (chartODE B X e he).domain :=
    (chartODE_contDiffOn B X e he).of_le (by simp)
  have hIVP := D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 (e.map_source hp)
  have hMem : (0, (e p).val) ∈ D := ⟨e.map_source hp, hIVP.2.1⟩
  have hΦZero : Ψ (0, (e p).val) = (e p).val := hIVP.2.2
  have hDom : IsOpen (D ∩ Ψ ⁻¹' V) := hReg.2.continuousOn.isOpen_inter_preimage hReg.1 hV
  refine ⟨D ∩ Ψ ⁻¹' V, hDom, ⟨hMem, by change Ψ (0, (e p).val) ∈ V; rw [hΦZero]; exact hpV⟩,
    G ∘ Ψ, hG.comp (hReg.2.mono inter_subset_left) (fun _ h => h.2), ?_⟩
  have hA : ContinuousAt A (0, p) := continuousAt_fst.prodMk
    (continuous_subtype_val.continuousAt.comp ((e.continuousAt hp).comp continuousAt_snd))
  have hRep' := hRep.comp_tendsto (show Filter.Tendsto (flow F) (𝓝 (0, p)) (𝓝 p) by
    simpa only [ContinuousAt, hZero] using hc)
  filter_upwards [hA.preimage_mem_nhds (hReg.1.mem_nhds hMem),
    (e.open_source.preimage continuous_snd).mem_nhds hp, hRep'] with w hw hwp hwRep
  have hAgree := (chartFlow_agrees F hF e he w hwp hw).2
  have hIVPw := D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 hw.1
  have hState : Ψ (A w) ∈ chartStateDomain e := hIVPw.1.2.1 w.1 hw.2
  have hCoord : (e (flow F w)).val = Ψ (A w) := by
    rw [hAgree]
    exact congrArg Subtype.val (e.right_inv hState)
  change G (Ψ (A w)) = (d (flow F w)).val
  rw [← hCoord]
  exact hwRep


/-- A regular point has both a genuine domain neighborhood and joint smoothness. -/
def FlowRegularAt {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (F : CurveFamily M) (z : ℝ × M) : Prop :=
  flowDomain F ∈ 𝓝 z ∧ FlowSmoothAt S F z

/-- Restarting at a regular time and following a chart solution preserves
regularity. The actual lifespan identity supplies every domain restriction. -/
theorem flowRegularAt_restart {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (s t : ℝ) (hs : FlowRegularAt S F (s, p))
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : F.curve p s ∈ e.source)
    (ht : (t - s, (e (F.curve p s)).val) ∈
      D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he)) :
    FlowRegularAt S F (t, p) := by
  let Q : ℝ × M → M := fun w => F.curve w.2 s
  let A : ℝ × M → ℝ × Euclidean n := fun w => (w.1 - s, (e (Q w)).val)
  let Ψ : ℝ × Euclidean n → Euclidean n := fun v =>
    D13Unified.Ch06.StateDerivative.flow (chartODE B X e he) v.1 v.2
  let D := D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he)
  have hReg := chartODE_flow_regular B X e he
  have hC1 : ContDiffOn ℝ 1 (chartODE B X e he).eval (chartODE B X e he).domain :=
    (chartODE_contDiffOn B X e he).of_le (by simp)
  have hi : ContinuousAt (fun w : ℝ × M => (s, w.2)) (t, p) :=
    continuousAt_const.prodMk continuousAt_snd
  have hQ : ContinuousAt Q (t, p) :=
    ContinuousAt.comp (f := fun w : ℝ × M => (s, w.2)) (x := (t, p)) hs.2.1 hi
  have hA : ContinuousAt A (t, p) :=
    (continuousAt_fst.sub continuousAt_const).prodMk
      (continuous_subtype_val.continuousAt.comp ((e.continuousAt hp).comp (f := Q) hQ))
  have hNear : ∀ᶠ w in 𝓝 (t, p), w ∈ flowDomain F ∧
      flow F w = e.symm (euclideanModelPoint (Ψ (A w))) := by
    have hFixed := (continuousAt_const.prodMk continuousAt_snd :
      ContinuousAt (fun w : ℝ × M => (s, w.2)) (t, p)).preimage_mem_nhds hs.1
    filter_upwards [hFixed, hA.preimage_mem_nhds (hReg.1.mem_nhds ht),
      hQ.preimage_mem_nhds (e.open_source.mem_nhds hp)] with w hw hwA hwQ
    have hLaw := lifespan_flow_law S B X F hF w.2 s hw
    have hChart := chartFlow_agrees F hF e he (w.1 - s, Q w) hwQ hwA
    have hsum : s + (w.1 - s) = w.1 := by ring
    have hDom : w ∈ flowDomain F := by
      have hh := hChart.1
      change w.1 - s ∈ (F.interval (F.curve w.2 s)).carrier at hh
      rw [hLaw.1] at hh
      simpa only [mem_ofPred_eq, flowDomain, hsum] using hh
    refine ⟨hDom, ?_⟩
    have hVal := hLaw.2 (w.1 - s) (by simpa only [flowDomain, mem_ofPred_eq, hsum] using hDom)
    exact (show flow F w = flow F (w.1 - s, Q w) by
      simpa only [flow, Q, hsum] using hVal.symm).trans hChart.2
  have hState : Ψ (A (t, p)) ∈ chartStateDomain e :=
    (D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 ht.1).1.2.1 _ ht.2
  have hΨ : ContinuousAt Ψ (A (t, p)) :=
    hReg.2.continuousOn.continuousAt (hReg.1.mem_nhds ht)
  have hLift : ContinuousAt (fun w => e.symm (euclideanModelPoint (Ψ (A w)))) (t, p) :=
    (e.continuousAt_symm hState).comp (f := fun w => euclideanModelPoint (Ψ (A w)))
      ((continuous_euclideanModelPoint n).continuousAt.comp (f := Ψ ∘ A) (hΨ.comp hA))
  have hEq : flow F =ᶠ[𝓝 (t, p)] (fun w => e.symm (euclideanModelPoint (Ψ (A w)))) :=
    hNear.mono (fun _ h => h.2)
  have hc : ContinuousAt (flow F) (t, p) := hLift.congr hEq.symm
  have hCoord : (fun w => (e (flow F w)).val) =ᶠ[𝓝 (t, p)] (Ψ ∘ A) := by
    filter_upwards [hNear, hA.preimage_mem_nhds (hReg.1.mem_nhds ht)] with w hw hwA
    rw [hw.2]
    exact congrArg Subtype.val (e.right_inv
      ((D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 hwA.1).1.2.1 _ hwA.2))
  have hpOut : flow F (t, p) ∈ e.source := by
    rw [hEq.eq_of_nhds]
    exact e.map_target hState
  refine ⟨hNear.mono (fun _ h => h.1), hc, ?_⟩
  intro a ha d hd hpa hpd
  obtain ⟨V, hV, hpV, K, hK, hKrep⟩ := hs.2.2 a ha e he hpa hp
  obtain ⟨T, hT, hpT, L, hL, hLrep⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d hd) hpOut hpd
  let J : ℝ × Euclidean n → ℝ × Euclidean n := fun v => (s, v.2)
  let H : ℝ × Euclidean n → ℝ × Euclidean n := fun v => (v.1 - s, K (J v))
  let W₀ := J ⁻¹' V
  have hW₀ : IsOpen W₀ := hV.preimage (continuous_const.prodMk continuous_snd)
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H W₀ :=
    (contDiff_fst.sub contDiff_const).contDiffOn.prodMk
      (hK.comp (contDiff_const.prodMk contDiff_snd).contDiffOn (fun _ h => h))
  let W₁ := W₀ ∩ H ⁻¹' D
  have hW₁ : IsOpen W₁ := hH.continuousOn.isOpen_inter_preimage hW₀ hReg.1
  have hΨH : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ H) W₁ :=
    hReg.2.comp (hH.mono inter_subset_left) (fun _ h => h.2)
  let W := W₁ ∩ (Ψ ∘ H) ⁻¹' T
  have hW : IsOpen W := hΨH.continuousOn.isOpen_inter_preimage hW₁ hT
  have hHval : H (t, (a p).val) = A (t, p) := by
    apply Prod.ext
    · rfl
    · exact hKrep.eq_of_nhds
  have hCenter : (t, (a p).val) ∈ W := by
    refine ⟨⟨hpV, ?_⟩, ?_⟩
    · change H (t, (a p).val) ∈ D
      rw [hHval]
      exact ht
    · change Ψ (H (t, (a p).val)) ∈ T
      rw [hHval]
      have hval : (e (flow F (t, p))).val = Ψ (A (t, p)) := hCoord.eq_of_nhds
      rwa [← hval]
  refine ⟨W, hW, hCenter, L ∘ (Ψ ∘ H),
    hL.comp (hΨH.mono inter_subset_left) (fun _ h => h.2), ?_⟩
  have hKrep' := hKrep.comp_tendsto
    (continuousAt_const.prodMk continuousAt_snd :
      ContinuousAt (fun w : ℝ × M => (s, w.2)) (t, p))
  have hLrep' := hLrep.comp_tendsto hc
  filter_upwards [hKrep', hCoord, hLrep'] with w hwK hwCoord hwL
  change L (Ψ (H (w.1, (a w.2).val))) = (d (flow F w)).val
  have hHw : H (w.1, (a w.2).val) = A w := by
    apply Prod.ext
    · rfl
    · exact hwK
  change (e (flow F w)).val = Ψ (A w) at hwCoord
  rw [hHw, ← hwCoord]
  exact hwL


/-- Regular times exhaust each connected lifespan. Local chart continuation
makes this set open; continuity of the original curve makes it closed. -/
theorem flowRegularAt_of_mem {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (t : ℝ) (ht : t ∈ (F.interval p).carrier) :
    FlowRegularAt S F (t, p) := by
  let I := (F.interval p).carrier
  let T : Set I := {a | FlowRegularAt S F (a.val, p)}
  letI : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp
    (F.interval p).ordConnected.isPreconnected
  have hZero : FlowRegularAt S F (0, p) :=
    ⟨flowDomain_mem_nhds_zero F hF p, flow_smoothAt_zero F hF p⟩
  have hStart (a : I) (e : ModelChart n .euclidean M)
      (he : e ∈ S.smoothStructure.val) (hp : F.curve p a.val ∈ e.source) :
      (0, (e (F.curve p a.val)).val) ∈
        D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he) := by
    have hC1 : ContDiffOn ℝ 1 (chartODE B X e he).eval (chartODE B X e he).domain :=
      (chartODE_contDiffOn B X e he).of_le (by simp)
    exact ⟨e.map_source hp,
      (D13Unified.Ch06.StateDerivative.flow_ivp (chartODE B X e he) hC1 (e.map_source hp)).2.1⟩
  have hOpen : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (F.curve p a.val)
    have hReg := chartODE_flow_regular B X e he
    have hA : ContinuousAt (fun b : I => (b.val - a.val, (e (F.curve p a.val)).val)) a :=
      (continuousAt_subtype_val.sub continuousAt_const).prodMk continuousAt_const
    have hNear : ∀ᶠ b : I in 𝓝 a,
        (b.val - a.val, (e (F.curve p a.val)).val) ∈
          D13Unified.Ch06.StateDerivative.flowDomain (chartODE B X e he) :=
      hA.preimage_mem_nhds (hReg.1.mem_nhds (by simpa using hStart a e he hp))
    filter_upwards [hNear] with b hb
    exact flowRegularAt_restart F hF p a.val b.val ha e he hp hb
  have hClosed : IsClosed T := by
    apply isClosed_of_closure_subset
    intro a ha
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (F.curve p a.val)
    have hReg := chartODE_flow_regular B X e he
    have hγ : Continuous (fun b : I => F.curve p b.val) :=
      (hF p).2.2.1.1.domRestrict
    have hE : ContinuousAt (fun b : I => (e (F.curve p b.val)).val) a :=
      continuous_subtype_val.continuousAt.comp
        ((e.continuousAt hp).comp (f := fun b : I => F.curve p b.val)
          (x := a) hγ.continuousAt)
    have hA : ContinuousAt (fun b : I => (a.val - b.val, (e (F.curve p b.val)).val)) a :=
      (continuousAt_const.sub continuousAt_subtype_val).prodMk hE
    have hNear := hA.preimage_mem_nhds
      (hReg.1.mem_nhds (by simpa using hStart a e he hp))
    have hSource := hγ.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hp)
    obtain ⟨b, ⟨hb, hbp⟩, hbT⟩ := mem_closure_iff_nhds.mp ha _ (inter_mem hNear hSource)
    exact flowRegularAt_restart F hF p b.val a.val hbT e he hbp hb
  have hAll : T = univ :=
    (show IsClopen T from ⟨hClosed, hOpen⟩).eq_univ ⟨⟨0, (hF p).1⟩, hZero⟩
  exact (show (⟨t, ht⟩ : I) ∈ T from hAll ▸ mem_univ _)

/-- The maximal manifold flow has its actual open domain and is jointly smooth
there, with no global completeness assumption. -/
theorem domain_open_smooth :
    Specs.SmoothManifolds.Ch06.MaximalFlow.domain_open_smoothType.{u} := by
  intro n M _ S B X F hF
  have hReg : ∀ z ∈ flowDomain F, FlowRegularAt S F z := by
    rintro ⟨t, p⟩ ht
    exact flowRegularAt_of_mem F hF p t ht
  exact ⟨isOpen_iff_mem_nhds.mpr (fun z hz => (hReg z hz).1),
    fun z hz => (hReg z hz).2⟩

theorem time_diffeomorph :
    Specs.SmoothManifolds.Ch06.MaximalFlow.time_diffeomorphType.{u} :=
  time_diffeomorph_of_open_smooth IntegralCurves.maximal_exists
    IntegralCurves.maximal_unique IntegralCurves.overlap_unique domain_open_smooth

end SmoothManifolds.MaximalFlow
