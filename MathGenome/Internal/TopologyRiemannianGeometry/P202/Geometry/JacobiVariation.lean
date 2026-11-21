import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.JacobiVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.JacobiIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GeodesicIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.TorsionAndMetric
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
open Set Filter
open scoped Topology
universe u v w
section Generic
variable {n r : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  {B : SmoothManifolds.BundleData.SmoothVectorBundle S r ι E}

theorem covariantDerivative_of_frame_coefficients (C : Connection B)
    (c : ℝ → M) (f : (s : ℝ) → E (c s)) (t : ℝ)
    (u : TangentSpace S (c t)) (hu : HasVelocityWithinAt S c univ t u)
    (U : Set M) (hU : IsOpen U) (b : LocalFrame B U hU) (hp : c t ∈ U)
    (w : E (c t))
    (hd : HasDerivAt (coefficientsAlong b c f)
      ((b.basis ⟨c t,hp⟩).equivFun w -
        (connectionMatrix C b ⟨c t,hp⟩ u).mulVec (coefficientsAlong b c f t)) t) :
    HasCovariantDerivativeAt C c f t w := by
  refine ⟨u,hu,U,hU,b,hp,_,hd.hasDerivWithinAt,?_⟩
  simp only [frameDerivative,sub_add_cancel,LinearEquiv.symm_apply_apply]
end Generic

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem exists_unique : P202Specs.Geometry.JacobiVariation.exists_uniqueType.{u} :=
  JacobiIVP.exists_unique

theorem decomposition : P202Specs.Geometry.JacobiVariation.decompositionType.{u} :=
  JacobiIVP.decomposition

/-- Construct a family from the proved spray, without assuming completeness. -/
theorem family_exists : P202Specs.Geometry.JacobiVariation.family_existsType.{u} := by
  intro n M _ S C
  classical
  obtain ⟨G, _, hbridge⟩ := GeodesicIVP.spray_exists S C
  have hex (w : Phase S) := GeodesicIVP.maximal_exists_from_spray C G hbridge w
  choose I q hq using hex
  exact ⟨⟨I, q⟩, hq⟩

/-- Translate the given geodesic through its phase at any interior time.
The universal maximality property puts the entire translated interval inside
the survival domain and identifies the flow there. -/
theorem flow_along_geodesic (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : P202.GeodesicData.IsMaximalFamily S C F)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (t₀ : ℝ) (ht₀ : t₀ ∈ I.carrier) :
    ∀ t ∈ I.carrier,
      (t - t₀, q t₀) ∈ flowDomain F ∧ F.curve (q t₀) (t - t₀) = q t := by
  let A := GeodesicIVP.affineInterval I 1 t₀ one_ne_zero
  let r := affineCurve S q 1 t₀
  have h0 : 0 ∈ A.carrier := by
    change 1 * 0 + t₀ ∈ I.carrier
    simpa using ht₀
  have hi : r 0 = q t₀ := by simp [r, affineCurve]
  have hr : IsGeodesicOn S C A.carrier r :=
    GeodesicIVP.geodesic_affine C 1 t₀ hq
  obtain ⟨hsub, heq⟩ := (hF (q t₀)).2.2.2 A r h0 hi hr
  intro t ht
  have htA : t - t₀ ∈ A.carrier := by
    change 1 * (t - t₀) + t₀ ∈ I.carrier
    simpa using ht
  refine ⟨hsub htA, ?_⟩
  simpa [r, affineCurve] using heq htA

/-- Every curve with an actual velocity admits a vector field with arbitrary
prescribed covariant first jet. Smooth section extensions provide the field;
its formula is A(c(s)) + s B(c(s)). This also works in dimension zero. -/
theorem prescribed_velocity_jet (C : Connection (tangentBundle S))
    (c : ℝ → M) (u : TangentSpace S (c 0))
    (hc : HasVelocityWithinAt S c univ 0 u)
    (v w : TangentSpace S (c 0)) :
    ∃ A B : Field S,
      A.val (c 0) = v ∧
      HasCovariantDerivativeAt C c
        (fun s => A.val (c s) + s • B.val (c s)) 0 w := by
  obtain ⟨A, hA⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c 0) v
  let d := pointDerivative C A.val (c 0) u
  obtain ⟨B, hB⟩ := ConnectionForms.section_evaluation_surjective
    (tangentBundle S) (c 0) (w - d)
  refine ⟨A, B, hA, ?_⟩
  have hDA := CurveCovariantDerivative.derivative_section C A (mem_univ 0) hc
  have hDB := CurveCovariantDerivative.derivative_section C B (mem_univ 0) hc
  have hDs := CurveCovariantDerivative.derivative_smul C hDB
    (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt
  have hd := CurveCovariantDerivative.derivative_add C (mem_univ 0)
    uniqueDiffWithinAt_univ hDA hDs
  have heq : pointDerivative C A.val (c 0) u + (w - d) = w := by
    dsimp [d]
    abel
  simpa only [id_eq, one_smul, zero_smul, add_zero, hB, heq] using hd

/-- A compact set of times has a single neighborhood of initial phases that
survives at every time. This is a tube inside the actual domain, not an
extension of the flow. -/
theorem compact_survival_neighborhood (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : P202.GeodesicData.IsMaximalFamily S C F)
    {K : Set ℝ} (hK : IsCompact K) (t₀ : ℝ) (w : Phase S)
    (hw : ∀ t ∈ K, (t - t₀, w) ∈ flowDomain F) :
    ∃ A : Set (Phase S), IsOpen A ∧ w ∈ A ∧
      ∀ v ∈ A, ∀ t ∈ K, (t - t₀, v) ∈ flowDomain F := by
  let D : Set (ℝ × Phase S) := {z | (z.1 - t₀, z.2) ∈ flowDomain F}
  have hD : IsOpen D := (GeodesicIVP.domain_open_smooth S C F hF).1.preimage
    ((continuous_fst.sub continuous_const).prodMk continuous_snd)
  have hsub : K ×ˢ ({w} : Set (Phase S)) ⊆ D := by
    rintro ⟨t, v⟩ ⟨ht, hv⟩
    have hv' : v = w := mem_singleton_iff.mp hv
    subst v
    exact hw t ht
  obtain ⟨B, A, _, hA, hKB, hwA, hBA⟩ :=
    generalized_tube_lemma hK isCompact_singleton hD hsub
  refine ⟨A, hA, hwA (mem_singleton w), ?_⟩
  intro v hv t ht
  exact hBA (show (t, v) ∈ B ×ˢ A from ⟨hKB ht, hv⟩)

/-- Pulling the survival neighborhood back by a continuous curve produces a
common positive width even when the original geodesic is incomplete. -/
theorem compact_survival : P202Specs.Geometry.JacobiVariation.compact_survivalType.{u} := by
  intro n M _ S C F hF K hK t₀ v hv hKv
  obtain ⟨A, hA, h0A, hAv⟩ := compact_survival_neighborhood C F hF hK t₀ (v 0) hKv
  have hn : v ⁻¹' A ∈ 𝓝 (0 : ℝ) := hv (hA.mem_nhds h0A)
  obtain ⟨ε, hε, hεA⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε, hε, ?_⟩
  intro s hs t ht
  apply hAv (v s) _ t ht
  apply hεA
  change dist s 0 < ε
  rw [Real.dist_eq, sub_zero, abs_lt]
  exact hs

/-- Smoothness supplies the actual variation field, without assuming its equation. -/
theorem variation_field_exists (C : Connection (tangentBundle S))
    {q : ℝ → Phase S} {U : Set ℝ} (V : GeodesicVariation C q U) :
    ∃ J : (t : ℝ) → TangentSpace S (q t).1, IsVariationField V J := by
  classical
  have hex (t : ℝ) : ∃ j : TangentSpace S (q t).1,
      t ∈ U → HasVelocityWithinAt S (fun s => (V.phase (s, t)).1) univ 0
        (Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) (V.central t)).symm j) := by
    by_cases ht : t ∈ U
    · have hs := V.smooth 0 ⟨neg_lt_zero.mpr V.width_pos, V.width_pos⟩ t ht
      obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (V.phase (0, t)).1
      have hline : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => (s, t)) 0 :=
        contDiffAt_id.prodMk contDiffAt_const
      have hd := ((hs.2 e he hp).comp 0 hline).differentiableAt (by simp)
      let E := (tangentStructure S).fiberCoordinates.equiv e he (V.phase (0, t)).1 hp
      let v := E.symm (deriv (fun s : ℝ => (e (V.phase (s, t)).1).val) 0)
      have hv : HasVelocityWithinAt S (fun s => (V.phase (s, t)).1) univ 0 v := by
        refine ⟨(hs.1.comp (f := fun s : ℝ => (s, t)) hline.continuousAt).continuousWithinAt, e, he, hp, ?_⟩
        simpa only [v, E, LinearEquiv.apply_symm_apply, Function.comp_def] using hd.hasDerivAt.hasDerivWithinAt
      let h := congrArg (fun z : Phase S => TangentSpace S z.1) (V.central t)
      refine ⟨Eq.mp h v, ?_⟩
      intro _
      change HasVelocityWithinAt S (fun s => (V.phase (s, t)).1) univ 0
        (Eq.mp h.symm (Eq.mp h v))
      simpa only [eq_mp_eq_cast, cast_cast, cast_eq] using hv
    · exact ⟨0, fun h => (ht h).elim⟩
  choose J hJ using hex
  exact ⟨J, hJ⟩

theorem variation_field_unique (C : Connection (tangentBundle S))
    {q : ℝ → Phase S} {U : Set ℝ} (V : GeodesicVariation C q U)
    {J K : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsVariationField V J) (hK : IsVariationField V K) :
    ∀ t ∈ U, J t = K t := by
  intro t ht
  have heq := CurveCovariantDerivative.velocity_unique (mem_univ 0)
    uniqueDiffWithinAt_univ (hJ t ht) (hK t ht)
  let h := congrArg (fun z : Phase S => TangentSpace S z.1) (V.central t)
  have heq' := congrArg (Eq.mp h) heq
  simpa only [eq_mp_eq_cast, cast_cast, cast_eq] using heq'

/-- Compose the actual smooth geodesic flow with an ordinary smooth curve
of initial phases. A single actual phase chart at the point suffices. -/
theorem positionSmoothAt_flow_comp (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : P202.GeodesicData.IsMaximalFamily S C F)
    (v : ℝ → Phase S) (t₀ s t : ℝ)
    (hv : ContinuousAt v s)
    (e : ModelChart (n + n) .euclidean (Phase S))
    (he : e ∈ (phaseManifold S).smoothStructure.val) (hve : v s ∈ e.source)
    (hvs : ContDiffAt ℝ (⊤ : ℕ∞) (fun r => (e (v r)).val) s)
    (ht : (t - t₀, v s) ∈ flowDomain F) :
    P202.JacobiVariationData.PositionSmoothAt
      (fun z : ℝ × ℝ => F.curve (v z.1) (z.2 - t₀)) (s, t) := by
  let L : ℝ × ℝ → ℝ × Phase S := fun z => (z.2 - t₀, v z.1)
  have hL : ContinuousAt L (s, t) :=
    (continuousAt_snd.sub continuousAt_const).prodMk (hv.comp continuousAt_fst)
  have hsmooth : P202.GeodesicData.PositionSmoothAt S F (t - t₀, v s) :=
    ((GeodesicIVP.domain_open_smooth S C F hF).2 _ ht).2
  have hvs' : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun r => ((e (v r)).val : Euclidean (n + n))) s := hvs
  refine ⟨?_, ?_⟩
  · have hh : ContinuousAt (fun w : ℝ × Phase S => (F.curve w.2 w.1).1) (t - t₀, v s) := hsmooth.1
    exact hh.comp (f := L) hL
  ·
    intro d hd hdp
    obtain ⟨A, hA, hzA, H, hH, hrep⟩ := hsmooth.2 e he d hd hve hdp
    have hcoord : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℝ × ℝ => ((z.2 - t₀, (e (v z.1)).val) : ℝ × Euclidean (n + n))) (s, t) :=
      (contDiffAt_snd.sub contDiffAt_const).prodMk (ContDiffAt.comp (F := ℝ) (G := Euclidean (n + n)) (s, t) hvs' contDiffAt_fst)
    have hcomp := (hH.contDiffAt (hA.mem_nhds hzA)).comp (s, t) hcoord
    exact hcomp.congr_of_eventuallyEq (hrep.comp_tendsto hL).symm

/-- Smooth chart lines are available on one open neighborhood of zero.
No claim is made about their arbitrary total representatives away from it. -/
theorem chartLine_local_smooth {m : ℕ} {N : Type u} [TopologicalSpace N]
    (e : ModelChart m .euclidean N) (p : N) (hp : p ∈ e.source)
    (w : Euclidean m) :
    ∃ A : Set ℝ, IsOpen A ∧ 0 ∈ A ∧ ∀ s ∈ A,
      GeodesicIVP.chartLine e p w s ∈ e.source ∧
      ContinuousAt (GeodesicIVP.chartLine e p w) s ∧
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun r => (e (GeodesicIVP.chartLine e p w r)).val) s := by
  let a : ℝ → modelSet m .euclidean :=
    fun s => ⟨(e p).val + s • w, mem_univ _⟩
  have ha : Continuous a :=
    (continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _
  let A := a ⁻¹' e.target
  have hA : IsOpen A := e.open_target.preimage ha
  have h0 : 0 ∈ A := by simpa [A, a] using e.map_source hp
  refine ⟨A, hA, h0, ?_⟩
  intro s hs
  have hsource : GeodesicIVP.chartLine e p w s ∈ e.source := e.map_target hs
  have hcont : ContinuousAt (GeodesicIVP.chartLine e p w) s :=
    (e.symm.continuousAt hs).comp ha.continuousAt
  refine ⟨hsource, hcont, ?_⟩
  have heq : (fun r => (e (GeodesicIVP.chartLine e p w r)).val) =ᶠ[𝓝 s]
      (fun r => (e p).val + r • w) := by
    filter_upwards [hA.mem_nhds hs] with r hr
    exact congrArg Subtype.val (e.right_inv hr)
  exact (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)).congr_of_eventuallyEq heq

/-- Convert an actual phase-chart derivative into the two intrinsic jets. -/
theorem phase_jet_of_chart_derivative (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (q : ℝ → Phase S) (t : ℝ) (hp : (q t).1 ∈ c.val.source)
    (hc : ContinuousAt q t) (u w : TangentSpace S (q t).1)
    (hd : HasDerivAt
      (fun s => (((tangentStructure S).chart c.val c.property) (q s)).val)
      ((tangentStructure S).productCoordinates.linearEquiv
        ((tangentStructure S).fiberCoordinates.equiv c.val c.property (q t).1 hp u,
          (tangentStructure S).fiberCoordinates.equiv c.val c.property (q t).1 hp w -
            (connectionMatrix C
              (SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c)
              ⟨(q t).1, by rw [(tangentRealization S).baseSet c]; exact hp⟩ u).mulVec
              (chartVelocity S c q t))) t) :
    HasVelocityWithinAt S (fun s => (q s).1) univ t u ∧
      HasCovariantDerivativeAt C (fun s => (q s).1) (fun s => (q s).2) t w := by
  have hbase : ContinuousAt (fun s => (q s).1) t :=
    (SmoothManifolds.TangentBundle.projection_smooth S (tangentStructure S) (q t)).1.comp hc
  obtain ⟨hx,hv⟩ := (P202.Geometry.GeodesicIVP.phase_chart_hasDerivAt_iff c q t hp hbase).mp hd
  have hu : HasVelocityWithinAt S (fun s => (q s).1) univ t u :=
    ⟨hbase.continuousWithinAt,c.val,c.property,hp,hx.hasDerivWithinAt⟩
  refine ⟨hu,?_⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hpb : (q t).1 ∈ (tangentBundle S).baseSet c := by
    rw [(tangentRealization S).baseSet c]
    exact hp
  have hw : (b.basis ⟨(q t).1,hpb⟩).equivFun w =
      (tangentStructure S).fiberCoordinates.equiv c.val c.property (q t).1 hp w := by
    rw [P202.Geometry.GeodesicIVP.trivializationFrame_equivFun c]
    exact (tangentRealization S).coordinates c (q t).1 hp w
  apply covariantDerivative_of_frame_coefficients C (fun s => (q s).1)
    (fun s => (q s).2) t u hu ((tangentBundle S).baseSet c)
    (P202.Geometry.GeodesicIVP.tangent_baseSet_isOpen c) b hpb w
  rw [hw]
  exact hv

/-- The phase-chart derivative corresponding to a prescribed position velocity
and a prescribed covariant derivative of the fiber component. -/
noncomputable def phaseJetCoordinates (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (z : Phase S) (hp : z.1 ∈ c.val.source) (u w : TangentSpace S z.1) :
    Euclidean (n + n) :=
  (tangentStructure S).productCoordinates.linearEquiv
    ((tangentStructure S).fiberCoordinates.equiv c.val c.property z.1 hp u,
      (tangentStructure S).fiberCoordinates.equiv c.val c.property z.1 hp w -
        (connectionMatrix C
          (SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c)
          ⟨z.1, by rw [(tangentRealization S).baseSet c]; exact hp⟩ u).mulVec
          ((tangentStructure S).fiberCoordinates.equiv c.val c.property z.1 hp z.2))

theorem phaseJetCoordinates_transport (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    {z z' : Phase S} (h : z = z') (hp : z.1 ∈ c.val.source) (hp' : z'.1 ∈ c.val.source)
    (u w : TangentSpace S z'.1) :
    phaseJetCoordinates C c z hp
      (Eq.mp (congrArg (fun y : Phase S => TangentSpace S y.1) h).symm u)
      (Eq.mp (congrArg (fun y : Phase S => TangentSpace S y.1) h).symm w) =
      phaseJetCoordinates C c z' hp' u w := by
  cases h
  rfl

/-- Arbitrary position and covariant velocity jets are realized by an actual
smooth curve in phase space near zero. The correction by the connection
matrix is necessary when both the base point and the velocity vary. -/
theorem initial_phase_curve (C : Connection (tangentBundle S))
    (z : Phase S) (u w : TangentSpace S z.1) :
    ∃ (v : ℝ → Phase S) (h0 : v 0 = z) (A : Set ℝ), IsOpen A ∧ 0 ∈ A ∧
      (∀ s ∈ A, ContinuousAt v s ∧
        ∃ e ∈ (phaseManifold S).smoothStructure.val, v s ∈ e.source ∧
          ContDiffAt ℝ (⊤ : ℕ∞) (fun r => (e (v r)).val) s) ∧
      HasVelocityWithinAt S (fun s => (v s).1) univ 0
        (Eq.mp (congrArg (fun y : Phase S => TangentSpace S y.1) h0).symm u) ∧
      HasCovariantDerivativeAt C (fun s => (v s).1) (fun s => (v s).2) 0
        (Eq.mp (congrArg (fun y : Phase S => TangentSpace S y.1) h0).symm w) := by
  obtain ⟨d, hd, hp⟩ := S.smoothStructure.property.1.1 z.1
  let c : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨d, hd⟩
  let e := (tangentStructure S).chart d hd
  have he : e ∈ (phaseManifold S).smoothStructure.val :=
    SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) d hd
  have hz : z ∈ e.source := by
    rw [(tangentStructure S).chart_source]
    exact hp
  let W := phaseJetCoordinates C c z hp u w
  let v := GeodesicIVP.chartLine e z W
  have h0 : v 0 = z := GeodesicIVP.chartLine_zero e z hz W
  obtain ⟨A, hA, h0A, hreg⟩ := chartLine_local_smooth e z hz W
  refine ⟨v, h0, A, hA, h0A, ?_, ?_⟩
  · intro s hs
    exact ⟨(hreg s hs).2.1, e, he, (hreg s hs).1, (hreg s hs).2.2⟩
  · have hp0 : (v 0).1 ∈ c.val.source := by simpa only [h0] using hp
    let u0 := Eq.mp (congrArg (fun y : Phase S => TangentSpace S y.1) h0).symm u
    let w0 := Eq.mp (congrArg (fun y : Phase S => TangentSpace S y.1) h0).symm w
    have hW : phaseJetCoordinates C c (v 0) hp0 u0 w0 = W :=
      phaseJetCoordinates_transport C c h0 hp0 hp u w
    apply phase_jet_of_chart_derivative C c v 0 hp0
      (GeodesicIVP.chartLine_continuousAt e z hz W) u0 w0
    rw [GeodesicIVP.chartVelocity_eq c v 0 hp0]
    change HasDerivAt (fun s => (e (v s)).val)
      (phaseJetCoordinates C c (v 0) hp0 u0 w0) 0
    rw [hW]
    exact GeodesicIVP.chartLine_deriv e z hz W

end P202.Geometry.JacobiVariation

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace P202.Geometry.JacobiVariation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def coordinateCovariantDerivative (A : E → F →L[ℝ] F)
    (v : E) (Z : E → F) (x : E) : F := fderiv ℝ Z x v + A x (Z x)

theorem coordinate_covariant_commutator
    (A B : E → F →L[ℝ] F) (Z : E → F) (x u v : E)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hZ : ContDiffAt ℝ 2 Z x) :
    coordinateCovariantDerivative A u (coordinateCovariantDerivative B v Z) x -
      coordinateCovariantDerivative B v (coordinateCovariantDerivative A u Z) x =
      (fderiv ℝ B x u) (Z x) - (fderiv ℝ A x v) (Z x) +
        A x (B x (Z x)) - B x (A x (Z x)) := by
  have hZ' : DifferentiableAt ℝ Z x := hZ.differentiableAt (by norm_num)
  have hDZ : DifferentiableAt ℝ (fderiv ℝ Z) x :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDZu : DifferentiableAt ℝ (fun y => fderiv ℝ Z y u) x :=
    hDZ.clm_apply (differentiableAt_const _)
  have hDZv : DifferentiableAt ℝ (fun y => fderiv ℝ Z y v) x :=
    hDZ.clm_apply (differentiableAt_const _)
  have hs := hZ.isSymmSndFDerivAt (by norm_num)
  unfold coordinateCovariantDerivative
  rw [fderiv_fun_add hDZv (hB.clm_apply hZ'),
    fderiv_fun_add hDZu (hA.clm_apply hZ')]
  rw [fderiv_clm_apply hDZ (differentiableAt_const _),
    fderiv_clm_apply hDZ (differentiableAt_const _),
    fderiv_clm_apply hB hZ', fderiv_clm_apply hA hZ']
  simp only [fderiv_const_apply, zero_apply, map_zero, zero_add,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, map_add]
  rw [hs u v]
  abel

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def pullbackConnectionMatrix (A : E → E →L[ℝ] F →L[ℝ] F)
    (f : H → E) (v : H) (x : H) : F →L[ℝ] F :=
  A (f x) (fderiv ℝ f x v)

theorem pullbackConnectionMatrix_derivative
    (A : E → E →L[ℝ] F →L[ℝ] F) (f : H → E) (x u v : H)
    (hA : DifferentiableAt ℝ A (f x)) (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (pullbackConnectionMatrix A f v) x u =
      (fderiv ℝ A (f x) (fderiv ℝ f x u)) (fderiv ℝ f x v) +
        A (f x) (fderiv ℝ (fderiv ℝ f) x u v) := by
  have hf' : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold pullbackConnectionMatrix
  rw [fderiv_clm_apply (hA.comp x hf') (hDf.clm_apply (differentiableAt_const _))]
  rw [fderiv_fun_comp x hA hf', fderiv_clm_apply hDf (differentiableAt_const _)]
  simp only [fderiv_const_apply, zero_apply, map_zero, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, zero_add]
  exact add_comm _ _

/-- Curvature of an ordinary matrix-valued connection one-form. -/
noncomputable def coordinateCurvature
    (A : E → E →L[ℝ] F →L[ℝ] F) (x u v : E) (z : F) : F :=
  ((fderiv ℝ A x u) v) z - ((fderiv ℝ A x v) u) z +
    A x u (A x v z) - A x v (A x u z)

/-- Curvature of a matrix connection pulls back along every smooth map.
Only derivatives of the ordinary map enter, so rank restrictions are absent. -/
theorem pullback_coordinate_commutator
    (A : E → E →L[ℝ] F →L[ℝ] F) (f : H → E) (Z : H → F)
    (x u v : H) (hA : DifferentiableAt ℝ A (f x))
    (hf : ContDiffAt ℝ 2 f x) (hZ : ContDiffAt ℝ 2 Z x) :
    coordinateCovariantDerivative (pullbackConnectionMatrix A f u) u
        (coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v Z) x -
      coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
        (coordinateCovariantDerivative (pullbackConnectionMatrix A f u) u Z) x =
      ((fderiv ℝ A (f x) (fderiv ℝ f x u)) (fderiv ℝ f x v)) (Z x) -
      ((fderiv ℝ A (f x) (fderiv ℝ f x v)) (fderiv ℝ f x u)) (Z x) +
      A (f x) (fderiv ℝ f x u) (A (f x) (fderiv ℝ f x v) (Z x)) -
      A (f x) (fderiv ℝ f x v) (A (f x) (fderiv ℝ f x u) (Z x)) := by
  have hf' : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hP (w : H) : DifferentiableAt ℝ (pullbackConnectionMatrix A f w) x :=
    (hA.comp x hf').clm_apply (hDf.clm_apply (differentiableAt_const _))
  rw [coordinate_covariant_commutator _ _ Z x u v (hP u) (hP v) hZ,
    pullbackConnectionMatrix_derivative A f x u v hA hf,
    pullbackConnectionMatrix_derivative A f x v u hA hf]
  simp only [add_apply, pullbackConnectionMatrix]
  rw [hf.isSymmSndFDerivAt (by norm_num) u v]
  abel


/-- For a symmetric connection matrix the covariant mixed derivatives of
an ordinary map agree. -/
theorem coordinate_mixed_symmetry
    (A : E → E →L[ℝ] E →L[ℝ] E) (f : H → E) (x u v : H)
    (hf : ContDiffAt ℝ 2 f x)
    (hsym : A (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) =
      A (f x) (fderiv ℝ f x v) (fderiv ℝ f x u)) :
    coordinateCovariantDerivative (pullbackConnectionMatrix A f u) u
        (fun y => fderiv ℝ f y v) x =
      coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
        (fun y => fderiv ℝ f y u) x := by
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold coordinateCovariantDerivative pullbackConnectionMatrix
  rw [fderiv_clm_apply hDf (differentiableAt_const _),
    fderiv_clm_apply hDf (differentiableAt_const _)]
  simp only [fderiv_const_apply, zero_apply, map_zero, zero_add,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rw [hf.isSymmSndFDerivAt (by norm_num) u v, hsym]

/-- Differentiating the affine geodesic equation produces the Jacobi
operator, for an arbitrary smooth map into a coordinate domain. -/
theorem coordinate_geodesic_linearization
    (A : E → E →L[ℝ] E →L[ℝ] E) (f : H → E) (x u v : H)
    (hA : DifferentiableAt ℝ A (f x)) (hf : ContDiffAt ℝ 3 f x)
    (hsym : ∀ᶠ y in 𝓝 x, ∀ a b, A (f y) a b = A (f y) b a)
    (hgeo : ∀ᶠ y in 𝓝 x,
      coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
        (fun z => fderiv ℝ f z v) y = 0) :
    coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
      (coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
        (fun y => fderiv ℝ f y u)) x =
      -(((fderiv ℝ A (f x) (fderiv ℝ f x u)) (fderiv ℝ f x v)) (fderiv ℝ f x v) -
      ((fderiv ℝ A (f x) (fderiv ℝ f x v)) (fderiv ℝ f x u)) (fderiv ℝ f x v) +
      A (f x) (fderiv ℝ f x u) (A (f x) (fderiv ℝ f x v) (fderiv ℝ f x v)) -
      A (f x) (fderiv ℝ f x v) (A (f x) (fderiv ℝ f x u) (fderiv ℝ f x v))) := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hT : ContDiffAt ℝ 2 (fun y => fderiv ℝ f y v) x :=
    (hf.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hswap : (coordinateCovariantDerivative (pullbackConnectionMatrix A f u) u
        (fun y => fderiv ℝ f y v)) =ᶠ[𝓝 x]
      (coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
        (fun y => fderiv ℝ f y u)) := by
    filter_upwards [hf2.eventually (by norm_num), hsym] with y hy hsy
    exact coordinate_mixed_symmetry A f y u v hy (hsy _ _)
  have hz : coordinateCovariantDerivative (pullbackConnectionMatrix A f u) u
      (coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
        (fun y => fderiv ℝ f y v)) x = 0 := by
    have hg : (coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
      (fun y => fderiv ℝ f y v)) =ᶠ[𝓝 x] (fun _ => 0) := hgeo
    change (fderiv ℝ (coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
      (fun y => fderiv ℝ f y v)) x) u +
      pullbackConnectionMatrix A f u x
        (coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
          (fun y => fderiv ℝ f y v) x) = 0
    rw [hg.fderiv_eq, hg.eq_of_nhds]
    simp only [fderiv_const_apply, zero_apply, map_zero, add_zero]
  have heq : coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
      (coordinateCovariantDerivative (pullbackConnectionMatrix A f u) u
        (fun y => fderiv ℝ f y v)) x =
      coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
      (coordinateCovariantDerivative (pullbackConnectionMatrix A f v) v
        (fun y => fderiv ℝ f y u)) x := by
    change (fderiv ℝ (coordinateCovariantDerivative (pullbackConnectionMatrix A f u) u
      (fun y => fderiv ℝ f y v)) x) v +
      pullbackConnectionMatrix A f v x
        (coordinateCovariantDerivative (pullbackConnectionMatrix A f u) u
          (fun y => fderiv ℝ f y v) x) = _
    rw [hswap.fderiv_eq, hswap.eq_of_nhds]
    rfl
  have hc := pullback_coordinate_commutator A f (fun y => fderiv ℝ f y v)
    x u v hA hf2 hT
  rw [hz, heq, zero_sub] at hc
  exact neg_eq_iff_eq_neg.mp hc


/-- The linearized equation gives actual ordinary derivatives of the field
and its first covariant derivative along a parameter row. -/
theorem coordinate_geodesic_first_order_system
    (A : E → E →L[ℝ] E →L[ℝ] E) (f : ℝ × ℝ → E) (s t : ℝ)
    (hA : DifferentiableAt ℝ A (f (s,t))) (hf : ContDiffAt ℝ 3 f (s,t))
    (hsym : ∀ᶠ y in 𝓝 (s,t), ∀ a b, A (f y) a b = A (f y) b a)
    (hgeo : ∀ᶠ y in 𝓝 (s,t),
      coordinateCovariantDerivative (pullbackConnectionMatrix A f (0,1)) (0,1)
        (fun z => fderiv ℝ f z (0,1)) y = 0) :
    let j : ℝ → E := fun r => fderiv ℝ f (s,r) (1,0)
    let K : ℝ × ℝ → E := coordinateCovariantDerivative
      (pullbackConnectionMatrix A f (0,1)) (0,1) (fun y => fderiv ℝ f y (1,0))
    HasDerivAt j (K (s,t) - A (f (s,t)) (fderiv ℝ f (s,t) (0,1)) (j t)) t ∧
      HasDerivAt (fun r => K (s,r))
        (-coordinateCurvature A (f (s,t)) (j t) (fderiv ℝ f (s,t) (0,1))
          (fderiv ℝ f (s,t) (0,1)) -
          A (f (s,t)) (fderiv ℝ f (s,t) (0,1)) (K (s,t))) t := by
  dsimp only
  let S : ℝ × ℝ → E := fun y => fderiv ℝ f y (1,0)
  let K := coordinateCovariantDerivative
      (pullbackConnectionMatrix A f (0,1)) (0,1) S
  have hdf : ContDiffAt ℝ 2 (fderiv ℝ f) (s,t) := hf.fderiv_right (by norm_num)
  have hS : ContDiffAt ℝ 2 S (s,t) := hdf.clm_apply contDiffAt_const
  have hds : DifferentiableAt ℝ (fderiv ℝ S) (s,t) :=
    (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf' : DifferentiableAt ℝ f (s,t) := hf.differentiableAt (by norm_num)
  have hP : DifferentiableAt ℝ (pullbackConnectionMatrix A f (0,1)) (s,t) :=
    (hA.comp (s,t) hf').clm_apply
      (hdf.differentiableAt (by norm_num) |>.clm_apply (differentiableAt_const _))
  have hK : DifferentiableAt ℝ K (s,t) :=
    (hds.clm_apply (differentiableAt_const _)).add
      (hP.clm_apply (hS.differentiableAt (by norm_num)))
  have hj := (hS.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  have hk := hK.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  constructor
  · simpa only [S, K, Function.comp_def, coordinateCovariantDerivative, pullbackConnectionMatrix,
      add_sub_cancel_right] using hj
  · have heq := coordinate_geodesic_linearization A f (s,t) (1,0) (0,1) hA hf hsym hgeo
    change (fderiv ℝ K (s,t)) (0,1) +
      A (f (s,t)) (fderiv ℝ f (s,t) (0,1)) (K (s,t)) =
      -coordinateCurvature A (f (s,t)) (S (s,t))
        (fderiv ℝ f (s,t) (0,1)) (fderiv ℝ f (s,t) (0,1)) at heq
    have heq' := eq_sub_iff_add_eq.mpr heq
    simpa only [S, K, Function.comp_def, heq'] using hk

end P202.Geometry.JacobiVariation

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace P202.Geometry.JacobiVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_line_fst {f : ℝ × ℝ → E} {s t : ℝ}
    (hf : DifferentiableAt ℝ f (s,t)) :
    HasDerivAt (fun r => f (r,t)) (fderiv ℝ f (s,t) (1,0)) s := by
  exact hf.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))

theorem hasDerivAt_line_snd {f : ℝ × ℝ → E} {s t : ℝ}
    (hf : DifferentiableAt ℝ f (s,t)) :
    HasDerivAt (fun r => f (s,r)) (fderiv ℝ f (s,t) (0,1)) t := by
  exact hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))

theorem partial_s_t {f : ℝ × ℝ → E} {s t : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (s,t)) :
    HasDerivAt (fun r => fderiv ℝ f (s,r) (1,0))
      (fderiv ℝ (fderiv ℝ f) (s,t) (0,1) (1,0)) t := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) (s,t) :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  have hh := (hasDerivAt_line_snd hd).clm_apply (hasDerivAt_const t ((1,0) : ℝ × ℝ))
  simpa only [map_zero, add_zero] using hh

theorem partial_t_s {f : ℝ × ℝ → E} {s t : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (s,t)) :
    HasDerivAt (fun r => fderiv ℝ f (r,t) (0,1))
      (fderiv ℝ (fderiv ℝ f) (s,t) (0,1) (1,0)) s := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) (s,t) :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  have hh := (hasDerivAt_line_fst hd).clm_apply (hasDerivAt_const s ((0,1) : ℝ × ℝ))
  rw [(hf.isSymmSndFDerivAt (by simp)).eq (1,0) (0,1)] at hh
  simpa only [map_zero, add_zero] using hh
theorem mixed_derivative_of_row_derivatives {f : ℝ × ℝ → E} {s t : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (s,t)) (J T : ℝ → E)
    (hJ : ∀ᶠ r in 𝓝 t, HasDerivAt (fun a => f (a,r)) (J r) s)
    (hT : ∀ᶠ a in 𝓝 s, HasDerivAt (fun r => f (a,r)) (T a) t) :
    ∃ w : E, HasDerivAt J w t ∧ HasDerivAt T w s := by
  have hreg : ∀ᶠ z in 𝓝 (s,t), DifferentiableAt ℝ f z := by
    have h1 : ContDiffAt ℝ 1 f (s,t) := hf.of_le (by simp)
    filter_upwards [h1.eventually (by simp)] with z hz
    exact hz.differentiableAt one_ne_zero
  have hJ' : J =ᶠ[𝓝 t] (fun r => fderiv ℝ f (s,r) (1,0)) := by
    filter_upwards [hJ, (continuousAt_const.prodMk continuousAt_id) hreg] with r hr hd
    exact hr.unique (hasDerivAt_line_fst hd)
  have hT' : T =ᶠ[𝓝 s] (fun a => fderiv ℝ f (a,t) (0,1)) := by
    filter_upwards [hT, (continuousAt_id.prodMk continuousAt_const) hreg] with a ha hd
    exact ha.unique (hasDerivAt_line_snd hd)
  exact ⟨_, (partial_s_t hf).congr_of_eventuallyEq hJ',
    (partial_t_s hf).congr_of_eventuallyEq hT'⟩
end P202.Geometry.JacobiVariation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem christoffel_symmetric (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (k i j : Fin n) :
    christoffel C c p k i j = christoffel C c p k j i := by
  have hmetric : (fun q => metricMatrix g c q i j) = (fun q => metricMatrix g c q j i) := by
    funext q
    exact g.symmetric q _ _
  rw [LeviCivita.christoffel_formula g C hC c p k i j,
    LeviCivita.christoffel_formula g C hC c p k j i]
  rw [hmetric]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem connectionMatrix_swap (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (u v : TangentSpace S p.val) :
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
    (connectionMatrix C b p u).mulVec ((b.basis p).equivFun v) =
      (connectionMatrix C b p v).mulVec ((b.basis p).equivFun u) := by
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hexpand (z : TangentSpace S p.val) (k j : Fin n) :
      connectionForm C b p k j z = ∑ i : Fin n,
        (b.basis p).equivFun z i * christoffel C c p k i j := by
    conv_lhs => rw [← (b.basis p).sum_equivFun z]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change _ = (b.basis p).equivFun z i *
      connectionForm C b p k j (P202.LeviCivitaData.coordinateVector c i p.val)
    rw [GeodesicIVP.coordinateVector_eq_frame]
    rfl
  dsimp only
  ext k
  change (∑ j : Fin n, connectionForm C b p k j u * (b.basis p).equivFun v j) =
    ∑ j : Fin n, connectionForm C b p k j v * (b.basis p).equivFun u j
  simp_rw [hexpand, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [christoffel_symmetric g C hC c p k j i]
  ring

theorem velocity_coordinates_frame
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    {d : ℝ → M} {t : ℝ} {v : TangentSpace S (d t)}
    (hv : HasVelocityWithinAt S d univ t v)
    (hp : d t ∈ (tangentBundle S).baseSet c) :
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
    HasDerivAt (fun r => (c.val (d r)).val) ((b.basis ⟨d t,hp⟩).equivFun v) t := by
  dsimp only
  have hp' : d t ∈ c.val.source := (tangentRealization S).baseSet c ▸ hp
  have hd := CurveCovariantDerivative.velocity_coordinates hv (mem_univ t) c.val c.property hp'
  rw [hasDerivWithinAt_univ] at hd
  rw [GeodesicIVP.trivializationFrame_equivFun]
  change HasDerivAt (fun r => (c.val (d r)).val)
    (((tangentBundle S).trivialization c) ⟨d t,v⟩).2 t
  rw [(tangentRealization S).coordinates c (d t) hp' v]
  exact hd

theorem mixed_covariant_derivative
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (Q : ℝ × ℝ → M) (t : ℝ)
    (hQ : ContinuousAt Q (0,t))
    (hsm : ∀ e ∈ S.smoothStructure.val, Q (0,t) ∈ e.source →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z => (e (Q z)).val) (0,t))
    (J : (r : ℝ) → TangentSpace S (Q (0,r)))
    (T : (s : ℝ) → TangentSpace S (Q (s,t)))
    (hJ : ∀ᶠ r in 𝓝 t, HasVelocityWithinAt S (fun s => Q (s,r)) univ 0 (J r))
    (hT : ∀ᶠ s in 𝓝 0, HasVelocityWithinAt S (fun r => Q (s,r)) univ t (T s))
    (w : TangentSpace S (Q (0,t)))
    (hw : HasCovariantDerivativeAt C (fun s => Q (s,t)) T 0 w) :
    HasCovariantDerivativeAt C (fun r => Q (0,r)) J t w := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (Q (0,t))
  let c : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e,he⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hpB : Q (0,t) ∈ (tangentBundle S).baseSet c := by
    rw [(tangentRealization S).baseSet c]
    exact hp
  have hO : IsOpen ((tangentBundle S).baseSet c) := GeodesicIVP.tangent_baseSet_isOpen c
  have hcJ : ContinuousAt (fun r => Q (0,r)) t :=
    hQ.comp (f := fun r : ℝ => (0,r)) (continuousAt_const.prodMk continuousAt_id)
  have hcT : ContinuousAt (fun s => Q (s,t)) 0 :=
    hQ.comp (f := fun s : ℝ => (s,t)) (continuousAt_id.prodMk continuousAt_const)
  let j := coefficientsAlong b (fun r => Q (0,r)) J
  let v := coefficientsAlong b (fun s => Q (s,t)) T
  have hj : ∀ᶠ r in 𝓝 t, HasDerivAt (fun s => (e (Q (s,r))).val) (j r) 0 := by
    filter_upwards [hJ, hcJ (hO.mem_nhds hpB)] with r hr hpr
    have hd := velocity_coordinates_frame c hr hpr
    dsimp only at hd
    dsimp only [j]
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b (fun r => Q (0,r)) J r hpr]
    exact hd
  have hv : ∀ᶠ s in 𝓝 0, HasDerivAt (fun r => (e (Q (s,r))).val) (v s) t := by
    filter_upwards [hT, hcT (hO.mem_nhds hpB)] with s hs hps
    have hd := velocity_coordinates_frame c hs hps
    dsimp only at hd
    dsimp only [v]
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b (fun s => Q (s,t)) T s hps]
    exact hd
  obtain ⟨D, hD, hD'⟩ := mixed_derivative_of_row_derivatives (hsm e he hp) j v hj hv
  have hw' := CurveCovariantDerivative.local_formula C (mem_univ 0)
    uniqueDiffWithinAt_univ hw b hpB hJ.self_of_nhds hD'.hasDerivWithinAt
  refine ⟨T 0, hT.self_of_nhds, _, hO, b, hpB, D, hD.hasDerivWithinAt, ?_⟩
  rw [hw']
  unfold frameDerivative
  congr 1
  congr 1
  rw [CurveCovariantDerivative.coefficientsAlong_of_mem b (fun s => Q (s,t)) T 0 hpB,
    CurveCovariantDerivative.coefficientsAlong_of_mem b (fun r => Q (0,r)) J t hpB]
  exact connectionMatrix_swap g C hC c ⟨Q (0,t),hpB⟩ (J t) (T 0)
end P202.Geometry.JacobiVariation

namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem covariantDerivative_transport (C : Connection (tangentBundle S))
    {c d : ℝ → M} (h : c = d)
    (J : (r : ℝ) → TangentSpace S (d r)) (t : ℝ) (w : TangentSpace S (d t)) :
    HasCovariantDerivativeAt C c
      (fun r => Eq.mp (congrArg (fun p => TangentSpace S p) (congrFun h r)).symm (J r)) t
      (Eq.mp (congrArg (fun p => TangentSpace S p) (congrFun h t)).symm w) ↔
        HasCovariantDerivativeAt C d J t w := by
  cases h
  rfl

theorem variation_initial_derivative (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {q : ℝ → Phase S} {U : Set ℝ} (hU : IsOpen U)
    (V : GeodesicVariation C q U)
    (J : (r : ℝ) → TangentSpace S (q r).1) (hJ : IsVariationField V J)
    (t : ℝ) (ht : t ∈ U) (w : TangentSpace S (q t).1)
    (hw : HasInitialVelocityJet V t w) :
    HasCovariantDerivativeAt C (fun r => (q r).1) J t w := by
  let J0 : (r : ℝ) → TangentSpace S (V.phase (0,r)).1 := fun r =>
    Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) (V.central r)).symm (J r)
  let w0 : TangentSpace S (V.phase (0,t)).1 :=
    Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) (V.central t)).symm w
  have hs0 : (0 : ℝ) ∈ Ioo (-V.width) V.width :=
    ⟨neg_lt_zero.mpr V.width_pos, V.width_pos⟩
  have hJ0 : ∀ᶠ r in 𝓝 t,
      HasVelocityWithinAt S (fun s => (V.phase (s,r)).1) univ 0 (J0 r) := by
    filter_upwards [hU.mem_nhds ht] with r hr
    exact hJ r hr
  have hT0 : ∀ᶠ s in 𝓝 0,
      HasVelocityWithinAt S (fun r => (V.phase (s,r)).1) univ t (V.phase (s,t)).2 := by
    filter_upwards [isOpen_Ioo.mem_nhds hs0] with s hs
    exact (V.geodesic s hs t ht).1
  have hD := mixed_covariant_derivative g C hC
    (fun z => (V.phase z).1) t (V.smooth 0 hs0 t ht).1
    (V.smooth 0 hs0 t ht).2 J0 (fun s => (V.phase (s,t)).2) hJ0 hT0 w0 hw
  let h : (fun r => (V.phase (0,r)).1) = (fun r => (q r).1) :=
    funext (fun r => congrArg (fun z : Phase S => z.1) (V.central r))
  exact (covariantDerivative_transport C h J t w).mp hD
end P202.Geometry.JacobiVariation

namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem covariantDerivative_congr_field (C : Connection (tangentBundle S))
    {c : ℝ → M} {J K : (r : ℝ) → TangentSpace S (c r)} {t : ℝ}
    {w : TangentSpace S (c t)} (hJ : HasCovariantDerivativeAt C c J t w)
    (hJK : ∀ᶠ r in 𝓝 t, J r = K r) :
    HasCovariantDerivativeAt C c K t w := by
  exact ParallelTransport.derivative_field_congr C (mem_univ t)
    (by simpa only [nhdsWithin_univ] using hJK) hJ

theorem jacobi_of_local_derivatives (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (U : Set ℝ) (q : ℝ → Phase S)
    (J : (r : ℝ) → TangentSpace S (q r).1)
    (hJ : ∀ t ∈ U, ∃ K : (r : ℝ) → TangentSpace S (q r).1,
      (∀ᶠ r in 𝓝 t, HasCovariantDerivativeAt C (fun a => (q a).1) J r (K r)) ∧
      HasCovariantDerivativeAt C (fun a => (q a).1) K t
        (-(R.val (q t).1 (J t) (q t).2 (q t).2))) :
    IsJacobiField C R U q J := by
  refine ⟨fun r => covariantDerivative C (fun a => (q a).1) J r, ?_⟩
  intro t ht
  obtain ⟨K, hK, hK'⟩ := hJ t ht
  have hsame : ∀ᶠ r in 𝓝 t,
      K r = covariantDerivative C (fun a => (q a).1) J r := by
    filter_upwards [hK] with r hr
    exact (CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ r)
      uniqueDiffWithinAt_univ hr).symm
  constructor
  · simpa only [← hsame.self_of_nhds] using hK.self_of_nhds
  · exact covariantDerivative_congr_field C hK' hsame
end P202.Geometry.JacobiVariation

namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem jacobi_of_local_frame_equations
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (U : Set ℝ) (hU : IsOpen U) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C U q)
    (J : (r : ℝ) → TangentSpace S (q r).1)
    (hlocal : ∀ t ∈ U,
      ∃ (A : Set M) (hA : IsOpen A) (b : LocalFrame (tangentBundle S) A hA)
        (hp : (q t).1 ∈ A) (f k : ℝ → Euclidean n),
      coefficientsAlong b (fun r => (q r).1) J =ᶠ[𝓝 t] f ∧
      (∀ᶠ r in 𝓝 t, ∃ hpr : (q r).1 ∈ A,
        HasDerivAt f
          (k r - (connectionMatrix C b ⟨(q r).1,hpr⟩ (q r).2).mulVec (f r)) r) ∧
      HasDerivAt k
        ((b.basis ⟨(q t).1,hp⟩).equivFun
          (-(R.val (q t).1 (J t) (q t).2 (q t).2)) -
            (connectionMatrix C b ⟨(q t).1,hp⟩ (q t).2).mulVec (k t)) t) :
    IsJacobiField C R U q J := by
  apply jacobi_of_local_derivatives C R U q J
  intro t ht
  obtain ⟨A, hA, b, hp, f, k, hcoeff, hfirst, hsecond⟩ := hlocal t ht
  let K := frameFieldAlong b (fun r => (q r).1) k
  have hfield : ∀ᶠ r in 𝓝 t,
      frameFieldAlong b (fun a => (q a).1) f r = J r := by
    have hc : ContinuousAt (fun r => (q r).1) t := by
      simpa only [continuousWithinAt_univ] using (hq t ht).1.1
    filter_upwards [hcoeff, hc (hA.mem_nhds hp)] with r hr hpr
    have hh := congrArg (b.basis ⟨(q r).1,hpr⟩).equivFun.symm hr.symm
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b (fun r => (q r).1) J r hpr,
      LinearEquiv.symm_apply_apply] at hh
    unfold frameFieldAlong
    split_ifs with h
    · exact hh
    · exact (h hpr).elim
  refine ⟨K, ?_, ?_⟩
  · filter_upwards [hfirst, eventually_eventually_nhds.mpr hfield, hU.mem_nhds ht] with r hder hfj hrU
    obtain ⟨hpr, hder⟩ := hder
    have hD := CurveCovariantDerivative.derivative_frame_expansion C b (mem_univ r)
      hpr (hq r hrU).1 hder.hasDerivWithinAt
    have hval : (b.basis ⟨(q r).1,hpr⟩).equivFun.symm (k r) = K r := by
      simp only [K, frameFieldAlong, dite_eq_left hpr]
    rw [sub_add_cancel, hval] at hD
    exact covariantDerivative_congr_field C hD hfj
  · have hD := CurveCovariantDerivative.derivative_frame_expansion C b (mem_univ t)
      hp (hq t ht).1 hsecond.hasDerivWithinAt
    rw [sub_add_cancel, LinearEquiv.symm_apply_apply] at hD
    exact hD
end P202.Geometry.JacobiVariation

namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem phase_frameCoordinates_transport
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    {z z' : Phase S} (h : z = z')
    (hp : z.1 ∈ (tangentBundle S).baseSet c)
    (hp' : z'.1 ∈ (tangentBundle S).baseSet c) (v : TangentSpace S z'.1) :
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
    (b.basis ⟨z.1,hp⟩).equivFun
      (Eq.mp (congrArg (fun a : Phase S => TangentSpace S a.1) h).symm v) =
        (b.basis ⟨z'.1,hp'⟩).equivFun v := by
  cases h
  rfl

theorem variation_field_coefficients (C : Connection (tangentBundle S))
    {q : ℝ → Phase S} {U : Set ℝ} (hU : IsOpen U)
    (V : GeodesicVariation C q U)
    (J : (r : ℝ) → TangentSpace S (q r).1) (hJ : IsVariationField V J)
    (t : ℝ) (ht : t ∈ U)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (hp : (q t).1 ∈ (tangentBundle S).baseSet c) :
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
    let f := fun z : ℝ × ℝ => (c.val (V.phase z).1).val
    coefficientsAlong b (fun r => (q r).1) J =ᶠ[𝓝 t]
      (fun r => fderiv ℝ f (0,r) (1,0)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun r => fderiv ℝ f (0,r) (1,0)) t := by
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let f := fun z : ℝ × ℝ => (c.val (V.phase z).1).val
  have hs0 : (0 : ℝ) ∈ Ioo (-V.width) V.width :=
    ⟨neg_lt_zero.mpr V.width_pos, V.width_pos⟩
  have hc : ContinuousAt (fun r => (q r).1) t := by
    simpa only [continuousWithinAt_univ, V.central] using (V.geodesic 0 hs0 t ht).1.1
  have hO : IsOpen ((tangentBundle S).baseSet c) := GeodesicIVP.tangent_baseSet_isOpen c
  constructor
  · filter_upwards [hU.mem_nhds ht, hc (hO.mem_nhds hp)] with r hr hpr
    have hprQ : (V.phase (0,r)).1 ∈ (tangentBundle S).baseSet c := by
      rw [V.central r]
      exact hpr
    have hpr' : (V.phase (0,r)).1 ∈ c.val.source := (tangentRealization S).baseSet c ▸ hprQ
    have hder := velocity_coordinates_frame c (hJ r hr) hprQ
    have hder' := hasDerivAt_line_fst
      (((V.smooth 0 hs0 r hr).2 c.val c.property hpr').differentiableAt (by simp))
    have heq := hder.unique hder'
    rw [phase_frameCoordinates_transport c (V.central r) hprQ hpr] at heq
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b (fun r => (q r).1) J r hpr]
    exact heq
  · have hpQ : (V.phase (0,t)).1 ∈ c.val.source := by
      rw [V.central t]
      exact (tangentRealization S).baseSet c ▸ hp
    have hf : ContDiffAt ℝ (⊤ : ℕ∞) f (0,t) :=
      (V.smooth 0 hs0 t ht).2 c.val c.property hpQ
    have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ f) (0,t) :=
      hf.fderiv_right (by simp)
    have hh := hg.clm_apply (g := fun _ : ℝ × ℝ => ((1,0) : ℝ × ℝ)) contDiffAt_const
    exact hh.comp t (contDiffAt_const.prodMk contDiffAt_id)
end P202.Geometry.JacobiVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P202.Geometry.JacobiVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.SectionExtensionData
  P202.ConnectionData P202.MetricData P202.CurvatureData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

noncomputable def frameCoefficients {U : Set M} {hU : IsOpen U}
    (b : LocalFrame (tangentBundle S) U hU) (Z : Field S) (k : Fin n) : M → ℝ :=
  totalize (fun q : U => (b.basis q).equivFun (Z.val q.val) k)

noncomputable def frameConnectionEntry (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (Y : Field S) (k j : Fin n) : M → ℝ :=
  totalize (fun q : U => connectionForm C b q k j (Y.val q.val))

theorem covariant_frame_coefficients (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (X Z : Field S) (p : U) (k : Fin n) :
    (b.basis p).equivFun ((C.cov X Z).val p.val) k =
      scalarDerivative S (frameCoefficients b Z k) p.val (X.val p.val) +
        ∑ j, connectionForm C b p k j (X.val p.val) * (b.basis p).equivFun (Z.val p.val) j := by
  have he : ∀ᶠ q in 𝓝 p.val, Z.val q =
      SmoothManifolds.SectionExtension.totalSection (restrictGlobalSection Z U hU).val q := by
    filter_upwards [hU.mem_nhds p.property] with q hq
    rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    rfl
  have hd := ConnectionForms.pointDerivative_congr (tangentBundle S) C
    Z.val _ p.val ⟨Z, Eventually.of_forall (fun _ => rfl)⟩ he
  have hh := ConnectionForms.local_frame_formula (tangentBundle S) C b
    (restrictGlobalSection Z U hU) p (X.val p.val) k
  rw [← hd, ConnectionForms.pointDerivative_global] at hh
  exact hh

theorem covariant_frame_entry_germ (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (Y Z : Field S) (p : U) (j k : Fin n)
    (hZ : ∀ᶠ q in 𝓝 p.val, Z.val q = SmoothManifolds.SectionExtension.totalSection (b.section_ j) q) :
    frameCoefficients b (C.cov Y Z) k =ᶠ[𝓝 p.val] frameConnectionEntry C b Y k j := by
  filter_upwards [hU.mem_nhds p.property, hZ.eventually_nhds] with q hq hZq
  simp only [frameCoefficients, frameConnectionEntry, totalize_of_mem _ q hq]
  change (b.basis ⟨q, hq⟩).equivFun ((C.cov Y Z).val q) k =
    (b.basis ⟨q, hq⟩).equivFun
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) q (Y.val q)) k
  rw [← ConnectionForms.pointDerivative_global (tangentBundle S) C Z q Y,
    ConnectionForms.pointDerivative_congr (tangentBundle S) C Z.val _ q
      ⟨Z, Eventually.of_forall (fun _ => rfl)⟩ hZq]

theorem scalarDerivative_frameCoefficients_congr
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (Z : Field S) (p : U) (k : Fin n) (f : M → ℝ)
    (hf : frameCoefficients b Z k =ᶠ[𝓝 p.val] f) :
    scalarDerivative S (frameCoefficients b Z k) p.val = scalarDerivative S f p.val := by
  obtain ⟨g, hg⟩ := ConnectionForms.local_coefficients_representative (tangentBundle S) b
    (restrictGlobalSection Z U hU).val (restrictGlobalSection Z U hU).property p
  apply PullbackConnections.scalarDerivative_congr
    (frameCoefficients b Z k) f p.val ⟨g k, ?_⟩ hf
  exact hg k

theorem curvature_frame_basis (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (X Y : Field S) (p : U) (j k : Fin n) :
    (b.basis p).equivFun (R.val p.val (X.val p.val) (Y.val p.val) (b.basis p j)) k =
      scalarDerivative S (frameConnectionEntry C b Y k j) p.val (X.val p.val) -
      scalarDerivative S (frameConnectionEntry C b X k j) p.val (Y.val p.val) +
      (∑ m, connectionForm C b p k m (X.val p.val) * connectionForm C b p m j (Y.val p.val)) -
      (∑ m, connectionForm C b p k m (Y.val p.val) * connectionForm C b p m j (X.val p.val)) -
      connectionForm C b p k j ((P202.TorsionMetricData.bracket X Y).val p.val) := by
  obtain ⟨Z, hZ⟩ := ConnectionForms.local_frame_representative (tangentBundle S) b p
  have hZj := hZ j
  have hz : (Z j).val p.val = b.basis p j := by
    rw [hZj.self_of_nhds, SmoothManifolds.SectionExtension.totalSection_of_mem _ p.val p.property]
    exact (b.basis_eq p j).symm
  have hYg (m : Fin n) := covariant_frame_entry_germ C b Y (Z j) p j m hZj
  have hXg (m : Fin n) := covariant_frame_entry_germ C b X (Z j) p j m hZj
  have hbg := covariant_frame_entry_germ C b (P202.TorsionMetricData.bracket X Y) (Z j) p j k hZj
  have hYval (m : Fin n) : (b.basis p).equivFun ((C.cov Y (Z j)).val p.val) m =
      connectionForm C b p m j (Y.val p.val) := by
    simpa only [frameCoefficients, frameConnectionEntry, totalize_of_mem _ p.val p.property]
      using (hYg m).eq_of_nhds
  have hXval (m : Fin n) : (b.basis p).equivFun ((C.cov X (Z j)).val p.val) m =
      connectionForm C b p m j (X.val p.val) := by
    simpa only [frameCoefficients, frameConnectionEntry, totalize_of_mem _ p.val p.property]
      using (hXg m).eq_of_nhds
  have hbval : (b.basis p).equivFun ((C.cov (P202.TorsionMetricData.bracket X Y) (Z j)).val p.val) k =
      connectionForm C b p k j ((P202.TorsionMetricData.bracket X Y).val p.val) := by
    simpa only [frameCoefficients, frameConnectionEntry, totalize_of_mem _ p.val p.property]
      using hbg.eq_of_nhds
  have hXY := covariant_frame_coefficients C b X (C.cov Y (Z j)) p k
  have hYX := covariant_frame_coefficients C b Y (C.cov X (Z j)) p k
  rw [scalarDerivative_frameCoefficients_congr b (C.cov Y (Z j)) p k _ (hYg k)] at hXY
  rw [scalarDerivative_frameCoefficients_congr b (C.cov X (Z j)) p k _ (hXg k)] at hYX
  simp_rw [hYval] at hXY
  simp_rw [hXval] at hYX
  rw [← hz, hR]
  simp only [curvature, ConnectionForms.section_add_apply, ConnectionForms.section_smul_apply,
    neg_one_smul, map_add, map_neg, Pi.add_apply, Pi.neg_apply]
  rw [hXY, hYX, hbval]
  ring

theorem scalarDerivative_frameConnectionEntry_congr (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (Y : Field S) (p : U) (k j : Fin n) (f : M → ℝ)
    (hf : frameConnectionEntry C b Y k j =ᶠ[𝓝 p.val] f) :
    scalarDerivative S (frameConnectionEntry C b Y k j) p.val = scalarDerivative S f p.val := by
  obtain ⟨Z, hZ⟩ := ConnectionForms.local_frame_representative (tangentBundle S) b p
  have h := covariant_frame_entry_germ C b Y (Z j) p j k (hZ j)
  exact (scalarDerivative_frameCoefficients_congr b (C.cov Y (Z j)) p k _ h).symm.trans
    (scalarDerivative_frameCoefficients_congr b (C.cov Y (Z j)) p k _ (h.trans hf))

noncomputable def coordinateChristoffel (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (k i j : Fin n) : M → ℝ :=
  totalize (fun p : (tangentBundle S).baseSet c => P202.LeviCivitaData.christoffel C c p k i j)

set_option maxHeartbeats 6000000 in
theorem curvature_christoffel (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (i j l k : Fin n) :
    (tangentBundle S).fiberCoordinates c p.val p.property
      (R.val p.val (P202.LeviCivitaData.coordinateVector c i p.val)
        (P202.LeviCivitaData.coordinateVector c j p.val)
        (P202.LeviCivitaData.coordinateVector c l p.val)) k =
      scalarDerivative S (coordinateChristoffel C c k j l) p.val
        (P202.LeviCivitaData.coordinateVector c i p.val) -
      scalarDerivative S (coordinateChristoffel C c k i l) p.val
        (P202.LeviCivitaData.coordinateVector c j p.val) +
      (∑ m, P202.LeviCivitaData.christoffel C c p k i m * P202.LeviCivitaData.christoffel C c p m j l) -
      (∑ m, P202.LeviCivitaData.christoffel C c p k j m * P202.LeviCivitaData.christoffel C c p m i l) := by
  classical
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hU : IsOpen (B.baseSet c) :=
    B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  obtain ⟨E, hE⟩ := ConnectionForms.local_frame_representative B b p
  have hec (r : Fin n) : ∀ᶠ q in 𝓝 p.val,
      (E r).val q = P202.LeviCivitaData.coordinateVector c r q := by
    filter_upwards [hE r, hU.mem_nhds p.property] with q hq hq'
    rw [hq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq']
    exact LeviCivita.trivializationFrame_section c r ⟨q, hq'⟩
  have heval (r : Fin n) := (hec r).self_of_nhds
  have hgamma (r d e : Fin n) : frameConnectionEntry C b (E r) d e =ᶠ[𝓝 p.val]
      coordinateChristoffel C c d r e := by
    filter_upwards [hec r, hU.mem_nhds p.property] with q hq hq'
    simp only [frameConnectionEntry, coordinateChristoffel, totalize_of_mem _ q hq']
    rw [hq]
    rfl
  have hdi := scalarDerivative_frameConnectionEntry_congr C b (E i) p k l _ (hgamma i k l)
  have hdj := scalarDerivative_frameConnectionEntry_congr C b (E j) p k l _ (hgamma j k l)
  have hh := curvature_frame_basis C R hR b (E i) (E j) p l k
  have hb : (P202.TorsionMetricData.bracket (E i) (E j)).val p.val = 0 :=
    LeviCivita.coordinate_bracket_zero c p.val p.property i j (E i) (E j) (hec i) (hec j)
  rw [hdi, hdj, hb, map_zero, sub_zero] at hh
  simp_rw [heval] at hh
  rw [b.basis_eq p l, LeviCivita.trivializationFrame_section c l p] at hh
  rw [LeviCivita.trivializationFrame_coordinates c p] at hh
  exact hh

end P202.Geometry.JacobiVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem positionSmoothAt_congr {Q P : ℝ × ℝ → Phase S} {z : ℝ × ℝ}
    (heq : Q =ᶠ[𝓝 z] P) (hP : P202.JacobiVariationData.PositionSmoothAt P z) :
    P202.JacobiVariationData.PositionSmoothAt Q z := by
  have h0 := heq.eq_of_nhds
  refine ⟨hP.1.congr_of_eventuallyEq (heq.mono (fun w hw => congrArg (fun x : Phase S => x.1) hw)), ?_⟩
  intro d hd hdz
  have hdp : (P z).1 ∈ d.source := by simpa only [h0] using hdz
  exact (hP.2 d hd hdp).congr_of_eventuallyEq
    (heq.mono (fun w hw => congrArg (fun x : Phase S => (d x.1).val) hw))

private theorem phase_initial_jets_congr (C : Connection (tangentBundle S))
    (v r : ℝ → Phase S) (z : Phase S) (hr : r = v)
    (hv0 : v 0 = z) (hr0 : r 0 = z) (u w : TangentSpace S z.1)
    (hpos : HasVelocityWithinAt S (fun s => (v s).1) univ 0
      (Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) hv0).symm u))
    (hjet : HasCovariantDerivativeAt C (fun s => (v s).1) (fun s => (v s).2) 0
      (Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) hv0).symm w)) :
    HasVelocityWithinAt S (fun s => (r s).1) univ 0
      (Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) hr0).symm u) ∧
    HasCovariantDerivativeAt C (fun s => (r s).1) (fun s => (r s).2) 0
      (Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) hr0).symm w) := by
  cases hr
  exact ⟨hpos,hjet⟩

theorem variation_from_initial_jets (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (t₀ : ℝ) (ht₀ : t₀ ∈ I.carrier)
    (u w : TangentSpace S (q t₀).1) (a b : ℝ) (hab : a ≤ b)
    (habI : Icc a b ⊆ I.carrier) (F : CurveFamily (Phase S))
    (hF : P202.GeodesicData.IsMaximalFamily S C F) :
    ∃ U : Set ℝ, IsOpen U ∧ OrdConnected U ∧ Icc a b ⊆ U ∧ t₀ ∈ U ∧ U ⊆ I.carrier ∧
      ∃ V : GeodesicVariation C q U,
        HasVelocityWithinAt S (fun s => (V.phase (s,t₀)).1) univ 0
          (Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) (V.central t₀)).symm u) ∧
        HasInitialVelocityJet V t₀ w ∧ ContinuousAt (fun s => V.phase (s,t₀)) 0 ∧
        ∀ s ∈ Ioo (-V.width) V.width, ∀ t ∈ U,
          (t-t₀, V.phase (s,t₀)) ∈ flowDomain F ∧
            V.phase (s,t) = F.curve (V.phase (s,t₀)) (t-t₀) := by
  classical
  have haI : a ∈ I.carrier := habI ⟨le_rfl, hab⟩
  have hbI : b ∈ I.carrier := habI ⟨hab, le_rfl⟩
  have hmI : min a t₀ ∈ I.carrier := by
    rcases le_total a t₀ with h | h
    · simpa only [min_eq_left h] using haI
    · simpa only [min_eq_right h] using ht₀
  have hMI : max b t₀ ∈ I.carrier := by
    rcases le_total b t₀ with h | h
    · simpa only [max_eq_right h] using ht₀
    · simpa only [max_eq_left h] using hbI
  have hmM : min a t₀ ≤ max b t₀ :=
    (min_le_left a t₀).trans (hab.trans (le_max_left b t₀))
  obtain ⟨l,r,hl,hr,hK⟩ := JacobiIVP.exists_compact_interval I hmI hMI
  rw [min_eq_left hmM] at hl
  rw [max_eq_right hmM] at hr
  let U : Set ℝ := Ioo l r
  have hUK : U ⊆ Icc l r := Ioo_subset_Icc_self
  have hUI : U ⊆ I.carrier := hUK.trans hK
  have htU : t₀ ∈ U :=
    ⟨hl.trans_le (min_le_right a t₀), (le_max_right b t₀).trans_lt hr⟩
  have habU : Icc a b ⊆ U := by
    intro t ht
    exact ⟨(hl.trans_le (min_le_left a t₀)).trans_le ht.1,
      ht.2.trans_lt ((le_max_left b t₀).trans_lt hr)⟩
  obtain ⟨v,h0,A,hA,h0A,hreg,hpos,hjet⟩ := initial_phase_curve C (q t₀) u w
  have hv0 : ContinuousAt v 0 := (hreg 0 h0A).1
  have hcenter := flow_along_geodesic C F hF I q hq t₀ ht₀
  have hsurv0 : ∀ t ∈ Icc l r, (t-t₀,v 0) ∈ flowDomain F := by
    intro t ht
    rw [h0]
    exact (hcenter t (hK ht)).1
  obtain ⟨δ,hδ,hδsurv⟩ := compact_survival S C F hF (Icc l r) isCompact_Icc t₀ v hv0 hsurv0
  obtain ⟨η,hη,hηA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds h0A)
  let ε := min δ η
  have hε : 0 < ε := lt_min hδ hη
  have hεA : ∀ s ∈ Ioo (-ε) ε, s ∈ A := by
    intro s hs
    apply hηA
    change dist s 0 < η
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right δ η)) hs.1,
      lt_of_lt_of_le hs.2 (min_le_right δ η)⟩
  have hsurv : ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ U, (t-t₀,v s) ∈ flowDomain F := by
    intro s hs t ht
    apply hδsurv s _ t (hUK ht)
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left δ η)) hs.1,
      lt_of_lt_of_le hs.2 (min_le_left δ η)⟩
  let Q : ℝ × ℝ → Phase S := fun z => if z.1 = 0 then q z.2 else F.curve (v z.1) (z.2-t₀)
  have hQ (s t : ℝ) (ht : t ∈ I.carrier) : Q (s,t) = F.curve (v s) (t-t₀) := by
    dsimp only [Q]
    split_ifs with hs
    · subst s
      rw [h0, (hcenter t ht).2]
    · rfl
  have hrow : (fun s => Q (s,t₀)) = v := by
    funext s
    rw [hQ s t₀ ht₀, sub_self, (hF (v s)).2.1]
  let V : GeodesicVariation C q U := {
    width := ε
    width_pos := hε
    phase := Q
    central := fun t => by dsimp only [Q]; rw [if_pos rfl]
    smooth := by
      intro s hs t ht
      obtain ⟨hv,e,he,hve,hev⟩ := hreg s (hεA s hs)
      have hflow := positionSmoothAt_flow_comp C F hF v t₀ s t hv e he hve hev (hsurv s hs t ht)
      apply positionSmoothAt_congr _ hflow
      filter_upwards [continuousAt_snd.preimage_mem_nhds (I.isOpen.mem_nhds (hUI ht))] with z hz
      exact hQ z.1 z.2 hz
    geodesic := by
      intro s hs
      by_cases hs0 : s = 0
      · subst s
        have hzero : (fun t => Q (0,t)) = q := by
          funext t
          exact if_pos rfl
        rw [hzero]
        exact fun t ht => hq t (hUI ht)
      · have hnonzero : (fun t => Q (s,t)) = (fun t => F.curve (v s) (t-t₀)) := by
          funext t
          exact if_neg hs0
        rw [hnonzero]
        have haf : affineCurve S (F.curve (v s)) 1 (-t₀) =
            (fun t => F.curve (v s) (t-t₀)) := by
          funext t
          dsimp only [affineCurve]
          simp only [one_smul]
          change F.curve (v s) (1 * t + -t₀) = F.curve (v s) (t-t₀)
          congr 1
          ring
        have hg := GeodesicIVP.geodesic_affine C 1 (-t₀) (hF (v s)).2.2.1
        rw [haf] at hg
        intro t ht
        apply hg t
        simpa only [affineDomain, flowDomain, mem_setOf_eq, one_mul, sub_eq_add_neg]
          using hsurv s hs t ht
  }
  have hjets := phase_initial_jets_congr C v (fun s => V.phase (s,t₀)) (q t₀)
    hrow h0 (V.central t₀) u w hpos hjet
  refine ⟨U,isOpen_Ioo,ordConnected_Ioo,habU,htU,hUI,V,hjets.1,hjets.2,?_,?_⟩
  · change ContinuousAt (fun s => Q (s,t₀)) 0
    rw [hrow]
    exact hv0
  · intro s hs t ht
    have hinitial : V.phase (s,t₀) = v s := congrFun hrow s
    rw [hinitial]
    exact ⟨hsurv s hs t ht,hQ s t (hUI ht)⟩
end P202.Geometry.JacobiVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.JacobiVariation
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Two Jacobi fields with the same actual two initial jets agree on the
entire original open interval. Representatives outside the interval are free. -/
theorem jacobi_unique (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (t₀ : ℝ) (ht₀ : t₀ ∈ I.carrier)
    {J K : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I.carrier q J) (hK : IsJacobiField C R I.carrier q K)
    (h0 : J t₀ = K t₀) (w : TangentSpace S (q t₀).1)
    (hdJ : HasCovariantDerivativeAt C (fun t => (q t).1) J t₀ w)
    (hdK : HasCovariantDerivativeAt C (fun t => (q t).1) K t₀ w) :
    ∀ t ∈ I.carrier, J t = K t := by
  obtain ⟨L, _, _, _, huniq⟩ := JacobiIVP.exists_unique S g C hC R hR I q hq t₀ ht₀ (J t₀) w
  intro t ht
  exact (huniq J hJ rfl hdJ t ht).trans (huniq K hK h0.symm hdK t ht).symm

/-- The central row inherits the intrinsic affine geodesic equation. -/
theorem central_geodesic (C : Connection (tangentBundle S))
    {q : ℝ → Phase S} {U : Set ℝ} (V : GeodesicVariation C q U) :
    IsGeodesicOn S C U q := by
  have heq : (fun t => V.phase (0,t)) = q := funext V.central
  rw [← heq]
  exact V.geodesic 0 ⟨neg_lt_zero.mpr V.width_pos,V.width_pos⟩
end P202.Geometry.JacobiVariation

namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem variation_velocity_coordinates (C : Connection (tangentBundle S))
    {q : ℝ → Phase S} {U : Set ℝ} (hU : IsOpen U)
    (V : GeodesicVariation C q U) (t : ℝ) (ht : t ∈ U)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (hp : (q t).1 ∈ (tangentBundle S).baseSet c) :
    let f := fun z : ℝ × ℝ => (c.val (V.phase z).1).val
    (fun z : ℝ × ℝ => chartVelocity S c (fun r => V.phase (z.1,r)) z.2) =ᶠ[𝓝 (0,t)]
      (fun z => fderiv ℝ f z (0,1)) := by
  have hs0 : (0 : ℝ) ∈ Ioo (-V.width) V.width :=
    ⟨neg_lt_zero.mpr V.width_pos, V.width_pos⟩
  have hpQ : (V.phase (0,t)).1 ∈ (tangentBundle S).baseSet c := by
    rw [V.central t]
    exact hp
  have hO : IsOpen ((tangentBundle S).baseSet c) := GeodesicIVP.tangent_baseSet_isOpen c
  have hQ := (V.smooth 0 hs0 t ht).1
  filter_upwards [(isOpen_Ioo.prod hU).mem_nhds ⟨hs0,ht⟩,
    hQ (hO.mem_nhds hpQ)] with z hz hpz
  have hpz' : (V.phase z).1 ∈ c.val.source := (tangentRealization S).baseSet c ▸ hpz
  have hder := (GeodesicIVP.geodesic_coordinate_equation C
    (V.geodesic z.1 hz.1) hz.2 c hpz).1
  have hf := (V.smooth z.1 hz.1 z.2 hz.2).2 c.val c.property hpz'
  exact hder.unique (hasDerivAt_line_snd (hf.differentiableAt (by simp)))

theorem variation_coordinate_geodesic (C : Connection (tangentBundle S))
    {q : ℝ → Phase S} {U : Set ℝ} (hU : IsOpen U)
    (V : GeodesicVariation C q U) (t : ℝ) (ht : t ∈ U)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (hp : (q t).1 ∈ (tangentBundle S).baseSet c)
    (A : Euclidean n → Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n)
    (hA : ∀ᶠ z : ℝ × ℝ in 𝓝 (0,t),
      ∀ (hpz : (V.phase z).1 ∈ (tangentBundle S).baseSet c)
        (u v : TangentSpace S (V.phase z).1),
      let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
      A (c.val (V.phase z).1).val
        ((b.basis ⟨(V.phase z).1,hpz⟩).equivFun u)
        ((b.basis ⟨(V.phase z).1,hpz⟩).equivFun v) =
        (connectionMatrix C b ⟨(V.phase z).1,hpz⟩ u).mulVec
          ((b.basis ⟨(V.phase z).1,hpz⟩).equivFun v)) :
    let f := fun z : ℝ × ℝ => (c.val (V.phase z).1).val
    ∀ᶠ z in 𝓝 (0,t),
      coordinateCovariantDerivative (pullbackConnectionMatrix A f (0,1)) (0,1)
        (fun z => fderiv ℝ f z (0,1)) z = 0 := by
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let f := fun z : ℝ × ℝ => (c.val (V.phase z).1).val
  let T := fun z : ℝ × ℝ => fderiv ℝ f z (0,1)
  have hs0 : (0 : ℝ) ∈ Ioo (-V.width) V.width :=
    ⟨neg_lt_zero.mpr V.width_pos, V.width_pos⟩
  have hpQ : (V.phase (0,t)).1 ∈ (tangentBundle S).baseSet c := by
    rw [V.central t]
    exact hp
  have hO : IsOpen ((tangentBundle S).baseSet c) := GeodesicIVP.tangent_baseSet_isOpen c
  have hQ := (V.smooth 0 hs0 t ht).1
  have hvel := variation_velocity_coordinates C hU V t ht c hp
  filter_upwards [(isOpen_Ioo.prod hU).mem_nhds ⟨hs0,ht⟩,
    hQ (hO.mem_nhds hpQ), hA, hvel, hvel.eventually_nhds] with z hz hpz hAz hvelz hvelnear
  have hpz' : (V.phase z).1 ∈ c.val.source := (tangentRealization S).baseSet c ▸ hpz
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) f z :=
    (V.smooth z.1 hz.1 z.2 hz.2).2 c.val c.property hpz'
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  have hT : DifferentiableAt ℝ T z := hDf.clm_apply (differentiableAt_const _)
  have hrow : chartVelocity S c (fun r => V.phase (z.1,r)) =ᶠ[𝓝 z.2]
      (fun r => T (z.1,r)) := by
    exact (continuousAt_const.prodMk continuousAt_id) hvelnear
  have hder := GeodesicIVP.geodesic_frame_equation C (V.geodesic z.1 hz.1) hz.2 b hpz
  have hder' : HasDerivAt (fun r => T (z.1,r))
      (-(connectionMatrix C b ⟨(V.phase z).1,hpz⟩ (V.phase z).2).mulVec
        (chartVelocity S c (fun r => V.phase (z.1,r)) z.2)) z.2 := by
    exact hder.congr_of_eventuallyEq hrow.symm
  have hderval := hder'.unique (hasDerivAt_line_snd hT)
  change chartVelocity S c (fun r => V.phase (z.1,r)) z.2 = T z at hvelz
  have hcoord : (b.basis ⟨(V.phase z).1,hpz⟩).equivFun (V.phase z).2 = T z := by
    rw [← hvelz]
    exact (CurveCovariantDerivative.coefficientsAlong_of_mem b
      (fun r => (V.phase (z.1,r)).1) (fun r => (V.phase (z.1,r)).2) z.2 hpz).symm
  have hmat := hAz hpz (V.phase z).2 (V.phase z).2
  change A (f z) ((b.basis ⟨(V.phase z).1,hpz⟩).equivFun (V.phase z).2)
    ((b.basis ⟨(V.phase z).1,hpz⟩).equivFun (V.phase z).2) =
    (connectionMatrix C b ⟨(V.phase z).1,hpz⟩ (V.phase z).2).mulVec
      ((b.basis ⟨(V.phase z).1,hpz⟩).equivFun (V.phase z).2) at hmat
  rw [hcoord] at hmat
  change fderiv ℝ T z (0,1) + A (f z) (T z) (T z) = 0
  rw [← hderval, hmat, hvelz]
  exact neg_add_cancel _
end P202.Geometry.JacobiVariation

set_option autoImplicit false
namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def coordinateCurvatureThird
    (A : E → E →L[ℝ] F →L[ℝ] F) (x u v : E) : F →ₗ[ℝ] F where
  toFun := coordinateCurvature A x u v
  map_add' z w := by simp only [coordinateCurvature, map_add, add_apply]; abel
  map_smul' a z := by simp only [coordinateCurvature, map_smul, smul_apply, RingHom.id_apply, id_eq]; module

noncomputable def coordinateCurvatureSecond
    (A : E → E →L[ℝ] F →L[ℝ] F) (x u : E) : E →ₗ[ℝ] F →ₗ[ℝ] F where
  toFun := coordinateCurvatureThird A x u
  map_add' v w := by
    ext z
    simp only [coordinateCurvatureThird, coordinateCurvature, map_add, LinearMap.coe_mk,
      AddHom.coe_mk, add_apply, LinearMap.add_apply]
    abel
  map_smul' a v := by
    ext z
    simp only [coordinateCurvatureThird, coordinateCurvature, map_smul, LinearMap.coe_mk,
      AddHom.coe_mk, smul_apply, LinearMap.smul_apply, RingHom.id_apply, id_eq]
    module

noncomputable def coordinateCurvatureLinearMap
    (A : E → E →L[ℝ] F →L[ℝ] F) (x : E) : E →ₗ[ℝ] E →ₗ[ℝ] F →ₗ[ℝ] F where
  toFun := coordinateCurvatureSecond A x
  map_add' u v := by
    ext w z
    simp only [coordinateCurvatureSecond, coordinateCurvatureThird, coordinateCurvature,
      map_add, LinearMap.coe_mk, AddHom.coe_mk, add_apply, LinearMap.add_apply]
    abel
  map_smul' a u := by
    ext v z
    simp only [coordinateCurvatureSecond, coordinateCurvatureThird, coordinateCurvature,
      map_smul, LinearMap.coe_mk, AddHom.coe_mk, smul_apply, LinearMap.smul_apply, RingHom.id_apply, id_eq]
    module

@[simp] theorem coordinateCurvatureLinearMap_apply
    (A : E → E →L[ℝ] F →L[ℝ] F) (x u v : E) (z : F) :
    coordinateCurvatureLinearMap A x u v z = coordinateCurvature A x u v z := rfl

/-- Checking curvature in a coordinate basis suffices for all tangent vectors. -/
theorem coordinateCurvature_eq_of_basis {n : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : V ≃ₗ[ℝ] Euclidean n) (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V)
    (A : Euclidean n → Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n)
    (x : Euclidean n)
    (hb : ∀ i j k : Fin n,
      e (T (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1)) (e.symm (Pi.single k 1))) =
        coordinateCurvature A x (Pi.single i 1) (Pi.single j 1) (Pi.single k 1))
    (u v w : V) :
    e (T u v w) = coordinateCurvature A x (e u) (e v) (e w) := by
  classical
  change e (T u v w) = coordinateCurvatureLinearMap A x (e u) (e v) (e w)
  rw [JacobiIVP.trilinear_coordinates e T u v w,
    JacobiIVP.trilinear_coordinates (LinearEquiv.refl ℝ (Euclidean n))
      (coordinateCurvatureLinearMap A x) (e u) (e v) (e w)]
  simp only [map_sum, map_smul, LinearEquiv.refl_apply,
    LinearEquiv.refl_symm, coordinateCurvatureLinearMap_apply, hb]
end P202.Geometry.JacobiVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem variation_jacobi_of_local_connection
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (U : Set ℝ) (hU : IsOpen U) (q : ℝ → Phase S)
    (V : GeodesicVariation C q U)
    (J : (r : ℝ) → TangentSpace S (q r).1) (hJ : IsVariationField V J)
    (hlocal : ∀ t ∈ U,
      ∃ (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
        (hp : (q t).1 ∈ (tangentBundle S).baseSet c)
        (A : Euclidean n → Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n),
      ContDiffAt ℝ 1 A (c.val (q t).1).val ∧
      (∀ᶠ z : ℝ × ℝ in 𝓝 (0,t),
        ∀ (hpz : (V.phase z).1 ∈ (tangentBundle S).baseSet c)
          (u v : TangentSpace S (V.phase z).1),
        let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
        A (c.val (V.phase z).1).val
          ((b.basis ⟨(V.phase z).1,hpz⟩).equivFun u)
          ((b.basis ⟨(V.phase z).1,hpz⟩).equivFun v) =
          (connectionMatrix C b ⟨(V.phase z).1,hpz⟩ u).mulVec
            ((b.basis ⟨(V.phase z).1,hpz⟩).equivFun v)) ∧
      (∀ u v w : TangentSpace S (q t).1,
        let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
        coordinateCurvature A (c.val (q t).1).val
          ((b.basis ⟨(q t).1,hp⟩).equivFun u)
          ((b.basis ⟨(q t).1,hp⟩).equivFun v)
          ((b.basis ⟨(q t).1,hp⟩).equivFun w) =
            (b.basis ⟨(q t).1,hp⟩).equivFun (R.val (q t).1 u v w))) :
    IsJacobiField C R U q J := by
  have hs0 : (0 : ℝ) ∈ Ioo (-V.width) V.width :=
    ⟨neg_lt_zero.mpr V.width_pos, V.width_pos⟩
  have hq : IsGeodesicOn S C U q := by
    simpa only [V.central] using V.geodesic 0 hs0
  apply jacobi_of_local_frame_equations C R U hU q hq J
  intro t ht
  obtain ⟨c, hp, A, hA, hrep, hR⟩ := hlocal t ht
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let f := fun z : ℝ × ℝ => (c.val (V.phase z).1).val
  let j := fun r : ℝ => fderiv ℝ f (0,r) (1,0)
  let T := fun z : ℝ × ℝ => fderiv ℝ f z (0,1)
  let K := coordinateCovariantDerivative (pullbackConnectionMatrix A f (0,1)) (0,1)
    (fun z => fderiv ℝ f z (1,0))
  let k := fun r : ℝ => K (0,r)
  have hO : IsOpen ((tangentBundle S).baseSet c) := GeodesicIVP.tangent_baseSet_isOpen c
  have hc : ContinuousAt (fun r => (q r).1) t := by
    simpa only [continuousWithinAt_univ] using (hq t ht).1.1
  have hpQ : (V.phase (0,t)).1 ∈ c.val.source := by
    rw [V.central t]
    exact (tangentRealization S).baseSet c ▸ hp
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) f (0,t) :=
    (V.smooth 0 hs0 t ht).2 c.val c.property hpQ
  have hf0 : f (0,t) = (c.val (q t).1).val := by simp only [f, V.central]
  have hDA : ∀ᶠ z in 𝓝 (0,t), DifferentiableAt ℝ A (f z) := by
    have hh : ∀ᶠ x in 𝓝 (f (0,t)), DifferentiableAt ℝ A x := by
      rw [hf0]
      filter_upwards [hA.eventually (by simp)] with x hx
      exact hx.differentiableAt one_ne_zero
    exact hf.continuousAt hh
  have hsym : ∀ᶠ z in 𝓝 (0,t), ∀ a d, A (f z) a d = A (f z) d a := by
    have hpQB : (V.phase (0,t)).1 ∈ (tangentBundle S).baseSet c := by
      rw [V.central t]
      exact hp
    filter_upwards [hrep, (V.smooth 0 hs0 t ht).1 (hO.mem_nhds hpQB)] with z hz hpz
    intro a d
    let E := (b.basis ⟨(V.phase z).1,hpz⟩).equivFun
    have h1 := hz hpz (E.symm a) (E.symm d)
    have h2 := hz hpz (E.symm d) (E.symm a)
    have hswap := connectionMatrix_swap g C hC c ⟨(V.phase z).1,hpz⟩ (E.symm a) (E.symm d)
    change A (f z) (E (E.symm a)) (E (E.symm d)) = _ at h1
    change A (f z) (E (E.symm d)) (E (E.symm a)) = _ at h2
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1 h2
    change (connectionMatrix C b ⟨(V.phase z).1,hpz⟩ (E.symm a)).mulVec (E (E.symm d)) =
      (connectionMatrix C b ⟨(V.phase z).1,hpz⟩ (E.symm d)).mulVec (E (E.symm a)) at hswap
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hswap
    exact h1.trans (hswap.trans h2.symm)
  have hgeo := variation_coordinate_geodesic C hU V t ht c hp A hrep
  have hcoeff := (variation_field_coefficients C hU V J hJ t ht c hp).1
  have hvel := variation_velocity_coordinates C hU V t ht c hp
  have hrepLine : ∀ᶠ r in 𝓝 t,
      ∀ (hpr : (q r).1 ∈ (tangentBundle S).baseSet c) (u v : TangentSpace S (q r).1),
      A (f (0,r)) ((b.basis ⟨(q r).1,hpr⟩).equivFun u)
        ((b.basis ⟨(q r).1,hpr⟩).equivFun v) =
        (connectionMatrix C b ⟨(q r).1,hpr⟩ u).mulVec
          ((b.basis ⟨(q r).1,hpr⟩).equivFun v) := by
    let P : Phase S → Prop := fun z =>
      ∀ (hpz : z.1 ∈ (tangentBundle S).baseSet c) (u v : TangentSpace S z.1),
      A (c.val z.1).val ((b.basis ⟨z.1,hpz⟩).equivFun u)
        ((b.basis ⟨z.1,hpz⟩).equivFun v) =
        (connectionMatrix C b ⟨z.1,hpz⟩ u).mulVec ((b.basis ⟨z.1,hpz⟩).equivFun v)
    have hh : ∀ᶠ r in 𝓝 t, P (V.phase (0,r)) :=
      (continuousAt_const.prodMk continuousAt_id) hrep
    filter_upwards [hh] with r hr
    have hr' : P (q r) := Eq.mp (congrArg P (V.central r)) hr
    simpa only [P, f, V.central] using hr'
  have hTLine : ∀ᶠ r in 𝓝 t, ∀ hpr : (q r).1 ∈ (tangentBundle S).baseSet c,
      (b.basis ⟨(q r).1,hpr⟩).equivFun (q r).2 = T (0,r) := by
    have hh := (continuousAt_const.prodMk continuousAt_id) hvel
    filter_upwards [hh] with r hr
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, id_eq] at hr
    intro hpr
    have hr' : chartVelocity S c q r = T (0,r) := by
      change chartVelocity S c (fun a => V.phase (0,a)) r = T (0,r) at hr
      rw [show (fun a => V.phase (0,a)) = q from funext V.central] at hr
      exact hr
    rw [← hr']
    exact (CurveCovariantDerivative.coefficientsAlong_of_mem b
      (fun r => (q r).1) (fun r => (q r).2) r hpr).symm
  have hconnLine : ∀ᶠ r in 𝓝 t, ∀ hpr : (q r).1 ∈ (tangentBundle S).baseSet c,
      ∀ a : Euclidean n,
      A (f (0,r)) (T (0,r)) a =
        (connectionMatrix C b ⟨(q r).1,hpr⟩ (q r).2).mulVec a := by
    filter_upwards [hrepLine, hTLine] with r hr hTr
    intro hpr a
    have hh := hr hpr (q r).2 ((b.basis ⟨(q r).1,hpr⟩).equivFun.symm a)
    rwa [LinearEquiv.apply_symm_apply, hTr hpr] at hh
  refine ⟨_, hO, b, hp, j, k, hcoeff, ?_, ?_⟩
  · have hDAline := (continuousAt_const.prodMk continuousAt_id) hDA
    have hsyline := (continuousAt_const.prodMk continuousAt_id) (eventually_eventually_nhds.mpr hsym)
    have hgeoline := (continuousAt_const.prodMk continuousAt_id) (eventually_eventually_nhds.mpr hgeo)
    filter_upwards [hU.mem_nhds ht, hc (hO.mem_nhds hp), hDAline, hsyline, hgeoline, hconnLine]
      with r hr hpr hDAr hsyr hgeor hconnr
    have hprQ : (V.phase (0,r)).1 ∈ c.val.source := by
      rw [V.central r]
      exact (tangentRealization S).baseSet c ▸ hpr
    have hfr : ContDiffAt ℝ 3 f (0,r) :=
      ((V.smooth 0 hs0 r hr).2 c.val c.property hprQ).of_le (by simp)
    have hd := (coordinate_geodesic_first_order_system A f 0 r hDAr hfr hsyr hgeor).1
    refine ⟨hpr, ?_⟩
    change HasDerivAt j (k r - A (f (0,r)) (T (0,r)) (j r)) r at hd
    rw [hconnr hpr] at hd
    exact hd
  · have hd := (coordinate_geodesic_first_order_system A f 0 t hDA.self_of_nhds
      (hf.of_le (by simp)) hsym hgeo).2
    change HasDerivAt k
      (-coordinateCurvature A (f (0,t)) (j t) (T (0,t)) (T (0,t)) -
        A (f (0,t)) (T (0,t)) (k t)) t at hd
    have hJt : (b.basis ⟨(q t).1,hp⟩).equivFun (J t) = j t := by
      have hh := hcoeff.self_of_nhds
      rw [CurveCovariantDerivative.coefficientsAlong_of_mem b (fun r => (q r).1) J t hp] at hh
      exact hh
    have hRt := hR (J t) (q t).2 (q t).2
    change coordinateCurvature A (c.val (q t).1).val
      ((b.basis ⟨(q t).1,hp⟩).equivFun (J t))
      ((b.basis ⟨(q t).1,hp⟩).equivFun (q t).2)
      ((b.basis ⟨(q t).1,hp⟩).equivFun (q t).2) = _ at hRt
    rw [← hf0, hJt, hTLine.self_of_nhds hp] at hRt
    rw [hRt, hconnLine.self_of_nhds hp] at hd
    have hneg := (b.basis ⟨(q t).1,hp⟩).equivFun.map_neg
      (R.val (q t).1 (J t) (q t).2 (q t).2)
    have hparam := congrArg
      (fun a : Euclidean n => a - (connectionMatrix C b ⟨(q t).1,hp⟩ (q t).2).mulVec (k t)) hneg
    exact hparam.symm ▸ hd
end P202.Geometry.JacobiVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace P202.Geometry.JacobiVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData
  P202.ConnectionData P202.MetricData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem scalarDerivative_of_chart_extension
    (f : M → ℝ) (p : M) (hf : VectorSmoothAt S.smoothStructure.val f p)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source)
    (F : Euclidean n → ℝ)
    (hF : ∃ A : Set (Euclidean n), IsOpen A ∧ (c p).val ∈ A ∧
      ContDiffOn ℝ (⊤ : ℕ∞) F A)
    (hrep : (fun q => F (c q).val) =ᶠ[𝓝 p] f) (v : TangentSpace S p) :
    scalarDerivative S f p v = fderiv ℝ F (c p).val
      ((tangentStructure S).fiberCoordinates.equiv c hc p hp v) := by
  have hs := (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hf
  have hg : (scalarGerm S f p).val = Germ.ofFun f := by
    simp only [scalarGerm, dite_eq_left hs]
  have hext : GermChartExtension S p c (scalarGerm S f p) F :=
    ⟨hF, (Germ.coe_eq.mpr hrep).trans hg.symm⟩
  exact SmoothManifolds.VectorFields.tangent_action_coordinates S
    (tangentStructure S).fiberCoordinates p c hc hp v (scalarGerm S f p) F hext

theorem scalarDerivative_of_bilinear_chart_extension
    (f : M → ℝ) (p : M) (hf : VectorSmoothAt S.smoothStructure.val f p)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source)
    (A : Euclidean n → Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n)
    (W : Set (Euclidean n)) (hW : IsOpen W) (hpW : (c p).val ∈ W)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A W) (u w : Euclidean n) (k : Fin n)
    (hrep : (fun q => A (c q).val u w k) =ᶠ[𝓝 p] f) (v : TangentSpace S p) :
    scalarDerivative S f p v = (fderiv ℝ A (c p).val
      ((tangentStructure S).fiberCoordinates.equiv c hc p hp v)) u w k := by
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A x u w) W :=
    (hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hscalar := scalarDerivative_of_chart_extension f p hf c hc hp
    (fun x => A x u w k) ⟨W, hW, hpW, contDiffOn_pi.mp hv k⟩ hrep v
  have hdA : DifferentiableAt ℝ A (c p).val :=
    (hA.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by simp)
  have hd := (hdA.hasFDerivAt.clm_apply (hasFDerivAt_const u (c p).val)).clm_apply
    (hasFDerivAt_const w (c p).val)
  have hdk := (ContinuousLinearMap.proj k).hasFDerivAt.comp (c p).val hd
  change HasFDerivAt (fun x => A x u w k) _ _ at hdk
  rw [hscalar, hdk.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add, add_zero]
  rfl

noncomputable def christoffelBilinear {n : ℕ} (G : Fin n → Fin n → Fin n → ℝ) :
    Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n :=
  ∑ k, ∑ i, ∑ j, G k i j •
    (ContinuousLinearMap.proj i).smulRight
      ((ContinuousLinearMap.proj j).smulRight (Pi.single k 1))

theorem christoffelBilinear_apply {n : ℕ} (G : Fin n → Fin n → Fin n → ℝ)
    (u v : Euclidean n) (k : Fin n) :
    christoffelBilinear G u v k = ∑ i, ∑ j, G k i j * u i * v j := by
  classical
  simp only [christoffelBilinear, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  congr 1
  funext i
  rw [Finset.sum_comm]
  congr 1
  funext j
  simp [Pi.single_apply, Finset.sum_ite_eq]
  ring

theorem connection_chart_model_exists {S : SmoothManifold n .euclidean M}
    (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) :
    ∃ W : Set (Euclidean n), IsOpen W ∧ (c.val p.val).val ∈ W ∧
      ∃ A : Euclidean n → Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n,
        ContDiffOn ℝ (⊤ : ℕ∞) A W ∧
        ∀ᶠ q in 𝓝 p.val, ∀ k i j : Fin n,
          A (c.val q).val (Pi.single i 1) (Pi.single j 1) k =
            totalize (fun r : (tangentBundle S).baseSet c =>
              P202.LeviCivitaData.christoffel C c r k i j) q := by
  classical
  have hp : p.val ∈ c.val.source := (tangentRealization S).baseSet c ▸ p.property
  have hex (k i j : Fin n) : ∃ W : Set (Euclidean n), IsOpen W ∧ (c.val p.val).val ∈ W ∧
      ∃ G : Euclidean n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) G W ∧
        (fun q => G (c.val q).val) =ᶠ[𝓝 p.val]
          totalize (fun r : (tangentBundle S).baseSet c =>
            P202.LeviCivitaData.christoffel C c r k i j) := by
    have hs := VectorSmoothAt.totalize (GeodesicIVP.tangent_baseSet_isOpen c)
      (GeodesicIVP.christoffel_smooth C c k i j p)
    exact hs.2 c.val c.property hp
  choose W hW hpW G hG hrep using hex
  let D : Set (Euclidean n) := ⋂ k, ⋂ i, ⋂ j, W k i j
  have hD : IsOpen D := isOpen_iInter_of_finite (fun k =>
    isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (hW k i)))
  have hpD : (c.val p.val).val ∈ D := mem_iInter.mpr (fun k =>
    mem_iInter.mpr (fun i => mem_iInter.mpr (hpW k i)))
  let A : Euclidean n → Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n :=
    fun x => christoffelBilinear (fun k i j => G k i j x)
  refine ⟨D, hD, hpD, A, ?_, ?_⟩
  · apply contDiffOn_clm_apply.mpr
    intro u
    apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_pi.mpr
    intro k
    simp only [A, christoffelBilinear_apply]
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    have hh : ContDiffOn ℝ (⊤ : ℕ∞) (G k i j) D := (hG k i j).mono (by
      intro x hx
      exact mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hx k) i) j)
    exact (hh.mul contDiffOn_const).mul contDiffOn_const
  · filter_upwards [Filter.eventually_all.mpr (fun k =>
      Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hrep k i)))] with q hq
    intro k i j
    simp only [A, christoffelBilinear_apply, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hq k i j

theorem connection_matrix_of_bilinear_entries {S : SmoothManifold n .euclidean M}
    (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c)
    (A : Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n)
    (hA : ∀ k i j : Fin n, A (Pi.single i 1) (Pi.single j 1) k =
      P202.LeviCivitaData.christoffel C c p k i j)
    (u v : TangentSpace S p.val) :
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
    A ((b.basis p).equivFun u) ((b.basis p).equivFun v) =
      (connectionMatrix C b p u).mulVec ((b.basis p).equivFun v) := by
  classical
  dsimp only
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let x := (b.basis p).equivFun u
  let y := (b.basis p).equivFun v
  have hlinear (k j : Fin n) : connectionForm C b p k j u =
      ∑ i : Fin n, x i * P202.LeviCivitaData.christoffel C c p k i j := by
    conv_lhs => rw [← (b.basis p).sum_equivFun u]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change _ = x i * connectionForm C b p k j (P202.LeviCivitaData.coordinateVector c i p.val)
    rw [GeodesicIVP.coordinateVector_eq_frame]
    rfl
  ext k
  change A x y k = ∑ j, connectionForm C b p k j u * y j
  have hx : (∑ i, x i • Pi.single i 1) = x := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply] using (Pi.basisFun ℝ (Fin n)).sum_equivFun x
  have hy : (∑ i, y i • Pi.single i 1) = y := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply] using (Pi.basisFun ℝ (Fin n)).sum_equivFun y
  conv_lhs => rw [← hx, ← hy]
  simp only [map_sum, map_smul, sum_apply, smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, hA]
  simp_rw [hlinear]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem connection_chart_model_full_exists {S : SmoothManifold n .euclidean M}
    (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) :
    ∃ W : Set (Euclidean n), IsOpen W ∧ (c.val p.val).val ∈ W ∧
      ∃ A : Euclidean n → Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n,
        ContDiffOn ℝ (⊤ : ℕ∞) A W ∧
        (∀ᶠ q in 𝓝 p.val, ∀ k i j : Fin n,
          A (c.val q).val (Pi.single i 1) (Pi.single j 1) k = coordinateChristoffel C c k i j q) ∧
        ∀ᶠ q in 𝓝 p.val, ∃ hq : q ∈ (tangentBundle S).baseSet c,
          ∀ u v : TangentSpace S q,
            let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
            A (c.val q).val ((b.basis ⟨q,hq⟩).equivFun u) ((b.basis ⟨q,hq⟩).equivFun v) =
              (connectionMatrix C b ⟨q,hq⟩ u).mulVec ((b.basis ⟨q,hq⟩).equivFun v) := by
  obtain ⟨W,hW,hpW,A,hA,hcoeff⟩ := connection_chart_model_exists C c p
  refine ⟨W,hW,hpW,A,hA,hcoeff,?_⟩
  filter_upwards [hcoeff, (GeodesicIVP.tangent_baseSet_isOpen c).mem_nhds p.property] with q hc hq
  refine ⟨hq,?_⟩
  apply connection_matrix_of_bilinear_entries C c ⟨q,hq⟩ (A (c.val q).val)
  intro k i j
  simpa only [totalize_of_mem _ q hq] using hc k i j

set_option maxHeartbeats 4000000 in
theorem curvature_chart_model_basis {S : SmoothManifold n .euclidean M}
    (C : Connection (tangentBundle S)) (R : P202.CurvatureData.CurvatureTensor S)
    (hR : P202.CurvatureData.RepresentsCurvature C R)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c)
    (A : Euclidean n → Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n)
    (W : Set (Euclidean n)) (hW : IsOpen W) (hpW : (c.val p.val).val ∈ W)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A W)
    (hcoeff : ∀ᶠ q in 𝓝 p.val, ∀ k i j : Fin n,
      A (c.val q).val (Pi.single i 1) (Pi.single j 1) k = coordinateChristoffel C c k i j q)
    (i j l : Fin n) :
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
    coordinateCurvature A (c.val p.val).val (Pi.single i 1) (Pi.single j 1) (Pi.single l 1) =
      (b.basis p).equivFun (R.val p.val (b.basis p i) (b.basis p j) (b.basis p l)) := by
  classical
  dsimp only
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let x := (c.val p.val).val
  have hp : p.val ∈ c.val.source := (tangentRealization S).baseSet c ▸ p.property
  have hco (r : Fin n) :
      (tangentStructure S).fiberCoordinates.equiv c.val c.property p.val hp
        (P202.LeviCivitaData.coordinateVector c r p.val) = Pi.single r 1 := by
    rw [← (tangentRealization S).coordinates c p.val hp]
    change ((tangentBundle S).fiberCoordinates c p.val p.property)
      (((tangentBundle S).fiberCoordinates c p.val p.property).symm (Pi.single r 1)) = _
    exact LinearEquiv.apply_symm_apply _ _
  have hd (d e f k : Fin n) :
      scalarDerivative S (coordinateChristoffel C c k e f) p.val
        (P202.LeviCivitaData.coordinateVector c d p.val) =
      (fderiv ℝ A x (Pi.single d 1)) (Pi.single e 1) (Pi.single f 1) k := by
    have hs : VectorSmoothAt S.smoothStructure.val (coordinateChristoffel C c k e f) p.val :=
      VectorSmoothAt.totalize (GeodesicIVP.tangent_baseSet_isOpen c)
        (GeodesicIVP.christoffel_smooth C c k e f p)
    have heq := scalarDerivative_of_bilinear_chart_extension
      (coordinateChristoffel C c k e f) p.val hs c.val c.property hp A W hW hpW hA
      (Pi.single e 1) (Pi.single f 1) k
      (hcoeff.mono (fun q hq => hq k e f)) (P202.LeviCivitaData.coordinateVector c d p.val)
    rw [hco] at heq
    exact heq
  have ha0 (k d e : Fin n) : A x (Pi.single d 1) (Pi.single e 1) k =
      P202.LeviCivitaData.christoffel C c p k d e := by
    simpa only [coordinateChristoffel, totalize_of_mem _ p.val p.property] using
      hcoeff.self_of_nhds k d e
  have hprod (d e f k : Fin n) : A x (Pi.single d 1) (A x (Pi.single e 1) (Pi.single f 1)) k =
      ∑ m, A x (Pi.single d 1) (Pi.single m 1) k * A x (Pi.single e 1) (Pi.single f 1) m := by
    have hh := JacobiIVP.vector_coordinates (LinearEquiv.refl ℝ (Euclidean n))
      (A x (Pi.single d 1)).toLinearMap (A x (Pi.single e 1) (Pi.single f 1))
    have hv := congrFun hh k
    simp only [LinearEquiv.refl_apply, LinearEquiv.refl_symm, sum_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hv
    change A x (Pi.single d 1) (A x (Pi.single e 1) (Pi.single f 1)) k =
      ∑ m, A x (Pi.single e 1) (Pi.single f 1) m * A x (Pi.single d 1) (Pi.single m 1) k at hv
    rw [hv]
    apply Finset.sum_congr rfl
    intro m _
    exact mul_comm _ _
  ext k
  have hh := curvature_christoffel C R hR c p i j l k
  rw [hd, hd] at hh
  simp_rw [← ha0] at hh
  have hb (r : Fin n) : b.basis p r = P202.LeviCivitaData.coordinateVector c r p.val := by
    rw [b.basis_eq]
    exact LeviCivita.trivializationFrame_section c r p
  change coordinateCurvature A x (Pi.single i 1) (Pi.single j 1) (Pi.single l 1) k = _
  simp only [coordinateCurvature, Pi.add_apply, Pi.sub_apply, hprod]
  rw [hb i, hb j, hb l, LeviCivita.trivializationFrame_coordinates c p]
  exact hh.symm

theorem connection_curvature_chart_model_exists {S : SmoothManifold n .euclidean M}
    (C : Connection (tangentBundle S)) (R : P202.CurvatureData.CurvatureTensor S)
    (hR : P202.CurvatureData.RepresentsCurvature C R)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) :
    ∃ W : Set (Euclidean n), IsOpen W ∧ (c.val p.val).val ∈ W ∧
      ∃ A : Euclidean n → Euclidean n →L[ℝ] Euclidean n →L[ℝ] Euclidean n,
        ContDiffOn ℝ (⊤ : ℕ∞) A W ∧
        (∀ᶠ q in 𝓝 p.val, ∃ hq : q ∈ (tangentBundle S).baseSet c,
          ∀ u v : TangentSpace S q,
            let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
            A (c.val q).val ((b.basis ⟨q,hq⟩).equivFun u) ((b.basis ⟨q,hq⟩).equivFun v) =
              (connectionMatrix C b ⟨q,hq⟩ u).mulVec ((b.basis ⟨q,hq⟩).equivFun v)) ∧
        ∀ u v w : TangentSpace S p.val,
          let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
          coordinateCurvature A (c.val p.val).val ((b.basis p).equivFun u)
            ((b.basis p).equivFun v) ((b.basis p).equivFun w) =
              (b.basis p).equivFun (R.val p.val u v w) := by
  obtain ⟨W,hW,hpW,A,hA,hcoeff,hmat⟩ := connection_chart_model_full_exists C c p
  refine ⟨W,hW,hpW,A,hA,hmat,?_⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  intro u v w
  dsimp only
  apply Eq.symm
  apply coordinateCurvature_eq_of_basis (b.basis p).equivFun (R.val p.val) A (c.val p.val).val
  intro i j l
  have hh := curvature_chart_model_basis C R hR c p A W hW hpW hA hcoeff i j l
  have he (r : Fin n) : (b.basis p).equivFun.symm (Pi.single r 1) = b.basis p r := by
    apply (b.basis p).equivFun.injective
    funext s
    simp only [LinearEquiv.apply_symm_apply, Pi.single_apply, Module.Basis.equivFun_self, eq_comm]
  rw [he i, he j, he l]
  exact hh.symm

end P202.Geometry.JacobiVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
open Set Filter
open scoped Topology
universe u

theorem variation_jacobi : P202Specs.Geometry.JacobiVariation.variation_jacobiType.{u} := by
  intro n M _ S g C hC R hR U hU q V J hJ
  apply variation_jacobi_of_local_connection g C hC R U hU q V J hJ
  intro t ht
  obtain ⟨d, hd, hp⟩ := S.smoothStructure.property.1.1 (q t).1
  let c : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨d,hd⟩
  have hpB : (q t).1 ∈ (tangentBundle S).baseSet c := by
    rw [(tangentRealization S).baseSet c]
    exact hp
  obtain ⟨W,hW,hpW,A,hA,hrep,hRcoord⟩ :=
    connection_curvature_chart_model_exists C R hR c ⟨(q t).1,hpB⟩
  refine ⟨c,hpB,A,?_,?_,?_⟩
  · exact (hA.contDiffAt (hW.mem_nhds hpW)).of_le (by simp)
  · have hs0 : (0 : ℝ) ∈ Ioo (-V.width) V.width :=
      ⟨neg_lt_zero.mpr V.width_pos, V.width_pos⟩
    have hQ : Tendsto (fun z => (V.phase z).1) (𝓝 (0,t)) (𝓝 (q t).1) := by
      have hh := (V.smooth 0 hs0 t ht).1
      change Tendsto (fun z => (V.phase z).1) (𝓝 (0,t)) (𝓝 (V.phase (0,t)).1) at hh
      rw [V.central t] at hh
      exact hh
    filter_upwards [hQ hrep] with z hz
    intro hpz u v
    obtain ⟨hq,hrepr⟩ := hz
    exact hrepr u v
  · exact hRcoord
end P202.Geometry.JacobiVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P202.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
open Set Filter
open scoped Topology
universe u

theorem realization : P202Specs.Geometry.JacobiVariation.realizationType.{u} := by
  intro n M _ S g C hC R hR I q hq J hJ t₀ ht₀ w hw a b hab habI F hF
  obtain ⟨U,hU,hconn,habU,htU,hUI,V,hpos,hjet,hcont,hflow⟩ :=
    variation_from_initial_jets C I q hq t₀ ht₀ (J t₀) w a b hab habI F hF
  obtain ⟨K,hK⟩ := variation_field_exists C V
  have hK0 : K t₀ = J t₀ := by
    have heq := CurveCovariantDerivative.velocity_unique (mem_univ 0)
      uniqueDiffWithinAt_univ (hK t₀ htU) hpos
    let h := congrArg (fun z : Phase S => TangentSpace S z.1) (V.central t₀)
    have heq' := congrArg (Eq.mp h) heq
    simpa only [eq_mp_eq_cast,cast_cast,cast_eq] using heq'
  have hDK := variation_initial_derivative g C hC hU V K hK t₀ htU w hjet
  have hJacK : IsJacobiField C R U q K := variation_jacobi S g C hC R hR U hU q V K hK
  have hJacJ : IsJacobiField C R U q J := by
    obtain ⟨D,hD⟩ := hJ
    exact ⟨D,fun t ht => hD t (hUI ht)⟩
  let IU : D13Unified.OpenTimeInterval := {
    carrier := U
    nonempty := ⟨t₀,htU⟩
    ordConnected := hconn
    isOpen := hU
  }
  have hqU : IsGeodesicOn S C IU.carrier q := fun t ht => hq t (hUI ht)
  obtain ⟨L,hL,hL0,hDL,huniq⟩ :=
    JacobiIVP.exists_unique S g C hC R hR IU q hqU t₀ htU (J t₀) w
  have hKJ : ∀ t ∈ U, K t = J t := by
    intro t ht
    exact (huniq K hJacK hK0 hDK t ht).trans (huniq J hJacJ rfl hw t ht).symm
  have hVJ : IsVariationField V J := by
    intro t ht
    rw [← hKJ t ht]
    exact hK t ht
  exact ⟨U,hU,habU,htU,hUI,V,hVJ,hjet,hcont,hflow⟩
end P202.Geometry.JacobiVariation
