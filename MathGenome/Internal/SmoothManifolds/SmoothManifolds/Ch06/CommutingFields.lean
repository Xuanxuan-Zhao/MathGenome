import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.CommutingFields
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.BracketFromFlow
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Logic.Equiv.Fintype

/-! Commuting-field clauses of M06.07. All time-map statements below
are restricted to their actual maximal flow domains. -/
noncomputable section
namespace SmoothManifolds.CommutingFields
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData VectorFieldData LieBracketData
  IntegralCurveData MaximalFlowData BracketFlowData CommutingFieldsData Set Filter
open scoped Topology
universe u

/-- The zero section remains zero under the actual inverse-time linear map,
including at off-domain representative values. -/
theorem pullback_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (F : CurveFamily M) (s : ℝ) (p : M) :
    pullback F (fun _ => (0 : TangentSpace S _)) s p = 0 := by
  exact map_zero _

/-- A vanishing bracket makes the time derivative of every fixed-fiber
coordinate of the pullback zero, throughout its actual maximal interval. -/
theorem pullback_hasDerivAt_zero
    (hDerivative : Specs.SmoothManifolds.Ch06.BracketFromFlow.derivative_at_timeType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B) (hbracket : ∀ q, (b X Y).val q = 0)
    (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (s : ℝ) (hs : s ∈ (F.interval p).carrier)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source) :
    HasDerivAt (fun t => pullbackCoefficients B F Y.val e he (t, p)) 0 s := by
  classical
  have h := hDerivative S B b hb X Y F hF p s hs e he hp
  have hz : pullback F (b X Y).val s p = 0 := by
    change inverseTimeDifferential S F s p ((b X Y).val (F.curve p s)) = 0
    rw [hbracket, map_zero]
  have hc : coefficients B (pullback F (b X Y).val s) e he p = 0 := by
    simp [coefficients, hp, hz]
  rwa [hc] at h

/-- Integrate in the fixed tangent fiber, rather than comparing coordinates
in the moving fiber. Openness and connectedness of the actual maximal time
interval are sufficient, with no completeness assumption. -/
theorem pullback_invariant
    (hDerivative : Specs.SmoothManifolds.Ch06.BracketFromFlow.derivative_at_timeType.{u})
    (hPullback : Specs.SmoothManifolds.Ch06.BracketFromFlow.pullback_boundarylessType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B) (hbracket : ∀ q, (b X Y).val q = 0)
    (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (s : ℝ) (hs : s ∈ (F.interval p).carrier) :
    pullback F Y.val s p = Y.val p := by
  classical
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let c : ℝ → Euclidean n := fun t => pullbackCoefficients B F Y.val e he (t, p)
  have hd : ∀ t ∈ (F.interval p).carrier, HasDerivAt c 0 t := by
    intro t ht
    exact pullback_hasDerivAt_zero hDerivative S B b hb X Y hbracket F hF p t ht e he hp
  have hc : c s = c 0 := (F.interval p).isOpen.is_const_of_deriv_eq_zero
    (F.interval p).ordConnected.isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hs (hF p).1
  apply (B.fiberCoordinates.equiv e he p hp).injective
  have hzero := (hPullback S B X F hF).2 Y p
  simpa only [c, pullbackCoefficients, coefficients, dite_eq_left hp, hzero] using hc

/-- Localized invariance: the bracket need only vanish along the indicated
trajectory segment. This is the version needed for simultaneous coordinates
when pairwise brackets vanish only near the point of independence. -/
theorem pullback_invariant_on_interval
    (hDerivative : Specs.SmoothManifolds.Ch06.BracketFromFlow.derivative_at_timeType.{u})
    (hPullback : Specs.SmoothManifolds.Ch06.BracketFromFlow.pullback_boundarylessType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (J : D13Unified.OpenTimeInterval) (hJ0 : 0 ∈ J.carrier)
    (hJF : J.carrier ⊆ (F.interval p).carrier)
    (hbracket : ∀ r ∈ J.carrier, (b X Y).val (F.curve p r) = 0)
    (s : ℝ) (hs : s ∈ J.carrier) : pullback F Y.val s p = Y.val p := by
  classical
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let c : ℝ → Euclidean n := fun t => pullbackCoefficients B F Y.val e he (t, p)
  have hd : ∀ t ∈ J.carrier, HasDerivAt c 0 t := by
    intro t ht
    have h := hDerivative S B b hb X Y F hF p t (hJF ht) e he hp
    have hz : pullback F (b X Y).val t p = 0 := by
      change inverseTimeDifferential S F t p ((b X Y).val (F.curve p t)) = 0
      rw [hbracket t ht, map_zero]
    have hc : coefficients B (pullback F (b X Y).val t) e he p = 0 := by
      simp [coefficients, hp, hz]
    rwa [hc] at h
  have hc := J.isOpen.is_const_of_deriv_eq_zero J.ordConnected.isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hs hJ0
  apply (B.fiberCoordinates.equiv e he p hp).injective
  have hzero := (hPullback S B X F hF).2 Y p
  simpa only [c, pullbackCoefficients, coefficients, dite_eq_left hp, hzero] using hc

/-- The number of independent fields cannot exceed the manifold dimension;
thus the explicit k ≤ n parameter in the independent Spec is automatic. -/
theorem independent_card_le_dimension {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : Fin k → SmoothField B) (p : M)
    (hX : LinearIndependent ℝ (fun i => (X i).val p)) : k ≤ n := by
  obtain ⟨hFinite, hRank⟩ := tangent_dimension S p
  letI := hFinite
  have h := hX.fintype_card_le_finrank
  simpa only [Fintype.card_fin, hRank] using h

/-- Completeness by itself supplies every domain condition, independently
of any bracket or commutation conclusion. -/
theorem complete_compositions_defined {M : Type u} (F G : CurveFamily M)
    (hF : CompleteFamily F) (hG : CompleteFamily G) (p : M) (s t : ℝ) :
    CompositionsDefined F G p s t := by
  change ∀ q, (F.interval q).carrier = univ at hF
  change ∀ q, (G.interval q).carrier = univ at hG
  simp [CompositionsDefined, hF, hG]

/-- The empty family has simultaneous coordinates in every chart through p.
This includes the source's zero-dimensional case. -/
theorem simultaneous_coordinates_empty {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : Fin 0 → SmoothField B) (p : M) (hk : 0 ≤ n) :
    SimultaneousCoordinates B X p hk := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  exact ⟨e, he, hp, fun _ _ i => Fin.elim0 i⟩

/-- The germ formulation of `df_p(Y_p)=Y_(f p)`. It is meaningful for a
total representative of a map smooth only near p. -/
def PreservesFieldAt {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (Y : SmoothField B) (f : M → M) (p : M) : Prop :=
  ∀ (h : SmoothGerm S (f p)) (k : SmoothGerm S p) (r : M → ℝ),
    Germ.ofFun r = h.val → Germ.ofFun (r ∘ f) = k.val →
      (Y.val (f p)).val h = (Y.val p).val k

/-- Rebasing a differential's source fiber uses an actual equality of points.
The auxiliary point q is arbitrary, so equality elimination introduces no
equation between a point and a flow expression containing that point. -/
theorem preservesFieldAt_of_rebased {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (Y : SmoothField B) (f : M → M) (p q : M) (hqp : q = p)
    (L : TangentSpace S q →ₗ[ℝ] TangentSpace S (f p))
    (hL : ∀ (v : TangentSpace S q) (h : SmoothGerm S (f p))
      (k : SmoothGerm S q) (r : M → ℝ),
      Germ.ofFun r = h.val → Germ.ofFun (r ∘ f) = k.val →
        (L v).val h = v.val k)
    (hY : L (Y.val q) = Y.val (f p)) : PreservesFieldAt Y f p := by
  subst q
  intro h k r hr hk
  have h := hL (Y.val p) h k r hr hk
  rwa [hY] at h

/-- Invariance of the pullback at the inverse-flow base point gives the
forward time map's field relation. No global time map is assumed smooth. -/
theorem timeMap_preservesFieldAt
    (hDerivative : Specs.SmoothManifolds.Ch06.BracketFromFlow.derivative_at_timeType.{u})
    (hPullback : Specs.SmoothManifolds.Ch06.BracketFromFlow.pullback_boundarylessType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B) (hbracket : ∀ q, (b X Y).val q = 0)
    (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (s : ℝ) (hs : s ∈ (F.interval p).carrier) :
    PreservesFieldAt Y (fun q => F.curve q s) p := by
  have hcorrect := (hPullback S B X F hF).1
  have hi := hcorrect p s hs
  have hj := hcorrect (F.curve p s) (-s) hi.1
  apply preservesFieldAt_of_rebased Y (fun q => F.curve q s) p
    (F.curve (F.curve p s) (-s)) hi.2.1
    (inverseTimeDifferential S F (-s) (F.curve p s))
  · simpa only [IsInverseTimeDifferential, neg_neg] using hj.2.2.1
  · exact pullback_invariant hDerivative hPullback S B b hb X Y hbracket F hF
      (F.curve p s) (-s) hi.1

/-- Localized forward field preservation. The bracket is assumed zero only
along the inverse trajectory segment used to integrate the pullback, with
all its time-domain conditions stated explicitly. -/
theorem timeMap_preservesFieldAt_on_interval
    (hDerivative : Specs.SmoothManifolds.Ch06.BracketFromFlow.derivative_at_timeType.{u})
    (hPullback : Specs.SmoothManifolds.Ch06.BracketFromFlow.pullback_boundarylessType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (s : ℝ) (hs : s ∈ (F.interval p).carrier)
    (J : D13Unified.OpenTimeInterval) (hJ0 : 0 ∈ J.carrier) (hJs : -s ∈ J.carrier)
    (hJF : J.carrier ⊆ (F.interval (F.curve p s)).carrier)
    (hbracket : ∀ r ∈ J.carrier, (b X Y).val (F.curve (F.curve p s) r) = 0) :
    PreservesFieldAt Y (fun q => F.curve q s) p := by
  have hcorrect := (hPullback S B X F hF).1
  have hi := hcorrect p s hs
  have hj := hcorrect (F.curve p s) (-s) hi.1
  apply preservesFieldAt_of_rebased Y (fun q => F.curve q s) p
    (F.curve (F.curve p s) (-s)) hi.2.1
    (inverseTimeDifferential S F (-s) (F.curve p s))
  · simpa only [IsInverseTimeDifferential, neg_neg] using hj.2.2.1
  · exact pullback_invariant_on_interval hDerivative hPullback S B b hb X Y F hF
      (F.curve p s) J hJ0 hJF hbracket (-s) hJs

/-- Integral curves differentiate every locally smooth scalar representative
by the original germ derivation. -/
theorem integralCurve_scalar_hasDerivAt {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (Y : SmoothField B) {I : Set ℝ} (hI : IsOpen I) (γ : ℝ → M)
    (hγ : IsIntegralCurveOn Y I γ) (t : ℝ) (ht : t ∈ I)
    (g : SmoothGerm S (γ t)) (r : M → ℝ) (hr : Germ.ofFun r = g.val) :
    HasDerivAt (r ∘ γ) ((Y.val (γ t)).val g) t := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (γ t)
  obtain ⟨P, ⟨⟨U, hU, hpU, hP⟩, hPg⟩⟩ := exists_germChartExtension S (γ t) e he hp g
  have hEq : r =ᶠ[𝓝 (γ t)] (fun q => P (e q).val) :=
    Germ.coe_eq.mp (hr.trans hPg.symm)
  have hd := ((hP.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (hγ.2 t ht e he hp).2
  have hval := VectorFields.tangent_action_coordinates S B.fiberCoordinates
    (γ t) e he hp (Y.val (γ t)) g P ⟨⟨U, hU, hpU, hP⟩, hPg⟩
  rw [← hval] at hd
  exact hd.congr_of_eventuallyEq (hEq.comp_tendsto (hγ.1.continuousAt (hI.mem_nhds ht)))

/-- A map smooth and field-preserving along a curve carries that curve to
an integral curve. Both assumptions are pointwise along the actual interval. -/
theorem integralCurve_map {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (Y : SmoothField B) {I : Set ℝ} (hI : IsOpen I) (γ : ℝ → M)
    (hγ : IsIntegralCurveOn Y I γ) (f : M → M)
    (hf : ∀ t ∈ I, ManifoldSmoothAt S.smoothStructure.val S.smoothStructure.val f (γ t))
    (hY : ∀ t ∈ I, PreservesFieldAt Y f (γ t)) :
    IsIntegralCurveOn Y I (f ∘ γ) := by
  constructor
  · intro t ht
    exact ((hf t ht).1.comp (hγ.1.continuousAt (hI.mem_nhds ht))).continuousWithinAt
  intro t ht e he hp
  obtain ⟨d, hd, hdp⟩ := S.smoothStructure.property.1.1 (γ t)
  obtain ⟨U, hU, hpU, H, hH, hEq⟩ := (hf t ht).2 d hd e he hdp hp
  have hct := hγ.1.continuousAt (hI.mem_nhds ht)
  have hEqγ := hEq.comp_tendsto hct
  have hSmooth := (hH.contDiffAt (hU.mem_nhds hpU)).comp t (hγ.2 t ht d hd hdp).1
  refine ⟨hSmooth.congr_of_eventuallyEq hEqγ.symm, ?_⟩
  apply hasDerivAt_pi.mpr
  intro i
  obtain ⟨coords, hcoords, hvalues⟩ := B.fiberCoordinates.isCoordinates e he (f (γ t)) hp
  let k : SmoothGerm S (γ t) := germOfChart S (γ t) d hd hdp (fun z => H z i)
    ⟨U, hU, hpU, (contDiffOn_pi.mp hH) i⟩
  have hk : Germ.ofFun ((fun q => (e q).val i) ∘ f) = k.val := by
    exact (Germ.coe_eq.mpr (hEq.mono (fun q hq => congrFun hq i))).symm
  have hpres := hY t ht (coords i) k (fun q => (e q).val i) (hcoords i).symm hk
  have hder := integralCurve_scalar_hasDerivAt S B Y hI γ hγ t ht k
    ((fun q => (e q).val i) ∘ f) hk
  rw [← hpres, ← hvalues] at hder
  exact hder

/-- Joint smoothness of the flow supplies smoothness of each time map at
every point of its actual open time domain. -/
theorem timeMap_smoothAt {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (F : CurveFamily M) (s : ℝ) (p : M)
    (hF : FlowSmoothAt S F (s, p)) :
    ManifoldSmoothAt S.smoothStructure.val S.smoothStructure.val (fun q => F.curve q s) p := by
  have hi : ContinuousAt (fun q : M => (s, q)) p := continuousAt_const.prodMk continuousAt_id
  refine ⟨hF.1.comp hi, ?_⟩
  intro e he d hd hp hfp
  obtain ⟨U, hU, hpU, H, hH, hEq⟩ := hF.2 e he d hd hp hfp
  exact ⟨(fun z : Euclidean n => (s, z)) ⁻¹' U,
    hU.preimage (continuous_const.prodMk continuous_id), hpU,
    (fun z => H (s, z)),
    hH.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => hz),
    hEq.comp_tendsto hi⟩

/-- Global commutation from the two flow-pullback facts actually used.
The public theorem below supplies both facts from the upstream proofs. -/
theorem complete_commutation_of_pullback
    (hDerivative : Specs.SmoothManifolds.Ch06.BracketFromFlow.derivative_at_timeType.{u})
    (hPullback : Specs.SmoothManifolds.Ch06.BracketFromFlow.pullback_boundarylessType.{u}) :
    Specs.SmoothManifolds.Ch06.CommutingFields.complete_commutationType.{u} := by
  intro n M _ S B b hb X Y hbracket F G hF hG hCF hCG p s t
  refine ⟨complete_compositions_defined F G hCF hCG p s t, ?_⟩
  have hFtime (q : M) : s ∈ (F.interval q).carrier := by rw [hCF q]; trivial
  have hGtime (q : M) : t ∈ (G.interval q).carrier := by rw [hCG q]; trivial
  let f : M → M := fun q => F.curve q s
  have hreg := (MaximalFlow.domain_open_smooth S B X F hF).2
  have hsm : ∀ q, ManifoldSmoothAt S.smoothStructure.val S.smoothStructure.val f q :=
    fun q => timeMap_smoothAt S F s q (hreg (s, q) (hFtime q))
  have hpres : ∀ q, PreservesFieldAt Y f q := fun q =>
    timeMap_preservesFieldAt hDerivative hPullback S B b hb X Y hbracket F hF q s (hFtime q)
  have hcurve := integralCurve_map S B Y (G.interval p).isOpen (G.curve p)
    (hG p).2.2.1 f (fun r _ => hsm (G.curve p r)) (fun r _ => hpres (G.curve p r))
  have hEq := IntegralCurves.overlap_unique S B Y (G.interval p) (G.interval (f p))
    (f ∘ G.curve p) (G.curve (f p)) hcurve (hG (f p)).2.2.1 0
    ⟨(hG p).1, (hG (f p)).1⟩
    (by simp only [Function.comp_apply, (hG p).2.1, (hG (f p)).2.1])
  exact (hEq ⟨hGtime p, hGtime (f p)⟩).symm

/-- Around zero times there is one common box on which both orders of the
partial flow composition are defined. The fields need not commute. -/
theorem common_composition_neighborhood {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X Y : SmoothField B) (F G : CurveFamily M)
    (hF : IsMaximalFamily X F) (hG : IsMaximalFamily Y G) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
        CompositionsDefined F G q s t := by
  have hRF := MaximalFlow.domain_open_smooth S B X F hF
  have hRG := MaximalFlow.domain_open_smooth S B Y G hG
  let z₀ : ℝ × (ℝ × M) := (0, 0, p)
  have hA : ContinuousAt (fun z : ℝ × (ℝ × M) => (z.1, z.2.2)) z₀ :=
    continuousAt_fst.prodMk continuousAt_snd.snd
  have hB : ContinuousAt (fun z : ℝ × (ℝ × M) => (z.2.1, z.2.2)) z₀ :=
    continuousAt_snd.fst.prodMk continuousAt_snd.snd
  have hFc := ContinuousAt.comp (f := fun z : ℝ × (ℝ × M) => (z.1, z.2.2))
    (hRF.2 (0, p) (hF p).1).1 hA
  have hGc := ContinuousAt.comp (f := fun z : ℝ × (ℝ × M) => (z.2.1, z.2.2))
    (hRG.2 (0, p) (hG p).1).1 hB
  have hC : ContinuousAt (fun z : ℝ × (ℝ × M) => (z.2.1, F.curve z.2.2 z.1)) z₀ :=
    continuousAt_snd.fst.prodMk hFc
  have hD : ContinuousAt (fun z : ℝ × (ℝ × M) => (z.1, G.curve z.2.2 z.2.1)) z₀ :=
    continuousAt_fst.prodMk hGc
  have hGbase : (0, F.curve p 0) ∈ flowDomain G := by
    change 0 ∈ (G.interval (F.curve p 0)).carrier
    rw [(hF p).2.1]
    exact (hG p).1
  have hFbase : (0, G.curve p 0) ∈ flowDomain F := by
    change 0 ∈ (F.interval (G.curve p 0)).carrier
    rw [(hG p).2.1]
    exact (hF p).1
  have hAll : ∀ᶠ z : ℝ × (ℝ × M) in 𝓝 z₀,
      CompositionsDefined F G z.2.2 z.1 z.2.1 := by
    filter_upwards [hA.preimage_mem_nhds (hRF.1.mem_nhds (hF p).1),
      hB.preimage_mem_nhds (hRG.1.mem_nhds (hG p).1),
      hC.preimage_mem_nhds (hRG.1.mem_nhds hGbase),
      hD.preimage_mem_nhds (hRF.1.mem_nhds hFbase)] with z h₁ h₂ h₃ h₄
    exact ⟨h₁, h₂, h₃, h₄⟩
  obtain ⟨A, hA₀, V, hV₀, hAV⟩ := mem_nhds_prod_iff.mp hAll
  obtain ⟨C, hC₀, U₀, hU₀, hCU⟩ := mem_nhds_prod_iff.mp hV₀
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hA₀
  obtain ⟨c, d, ⟨hc, hd⟩, hcd⟩ := mem_nhds_iff_exists_Ioo_subset.mp hC₀
  obtain ⟨U, hUU, hU, hpU⟩ := mem_nhds_iff.mp hU₀
  let ε : ℝ := min (min (-a) b) (min (-c) d)
  have hε : 0 < ε := lt_min (lt_min (neg_pos.mpr ha) hb) (lt_min (neg_pos.mpr hc) hd)
  have hεa : ε ≤ -a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεb : ε ≤ b := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεc : ε ≤ -c := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεd : ε ≤ d := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ε, hε, U, hU, hpU, ?_⟩
  intro q hq s hs t ht
  apply hAV (a := (s, t, q))
  exact ⟨hab ⟨by linarith [hs.1], lt_of_lt_of_le hs.2 hεb⟩,
    hCU ⟨hcd ⟨by linarith [ht.1], lt_of_lt_of_le ht.2 hεd⟩, hUU hq⟩⟩

/-- Local uniqueness is applied on a common interval contained in both
domains. Existence of one partial composition at an isolated time is never
used as a substitute for existence along its trajectory segment. -/
theorem local_commutation_of_pullback
    (hDerivative : Specs.SmoothManifolds.Ch06.BracketFromFlow.derivative_at_timeType.{u})
    (hPullback : Specs.SmoothManifolds.Ch06.BracketFromFlow.pullback_boundarylessType.{u}) :
    Specs.SmoothManifolds.Ch06.CommutingFields.local_commutationType.{u} := by
  intro n M _ S B b hb X Y hbracket F G hF hG p
  obtain ⟨ε, hε, U, hU, hpU, hD⟩ := common_composition_neighborhood S B X Y F G hF hG p
  refine ⟨ε, hε, U, hU, hpU, ?_⟩
  intro q hq s hs t ht
  refine ⟨hD q hq s hs t ht, ?_⟩
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  let I : D13Unified.OpenTimeInterval :=
    { carrier := Ioo (-ε) ε
      nonempty := ⟨0, h0⟩
      ordConnected := ordConnected_Ioo
      isOpen := isOpen_Ioo }
  have hGI : I.carrier ⊆ (G.interval q).carrier := fun r hr => (hD q hq s hs r hr).2.1
  have hGI' : I.carrier ⊆ (G.interval (F.curve q s)).carrier :=
    fun r hr => (hD q hq s hs r hr).2.2.1
  have hFtime (r : ℝ) (hr : r ∈ I.carrier) :
      s ∈ (F.interval (G.curve q r)).carrier := (hD q hq s hs r hr).2.2.2
  let f : M → M := fun x => F.curve x s
  have hreg := (MaximalFlow.domain_open_smooth S B X F hF).2
  have hcurve := integralCurve_map S B Y I.isOpen (G.curve q)
    (IntegralCurves.integral_mono (hG q).2.2.1 hGI) f
    (fun r hr => timeMap_smoothAt S F s (G.curve q r)
      (hreg (s, G.curve q r) (hFtime r hr)))
    (fun r hr => timeMap_preservesFieldAt hDerivative hPullback S B b hb X Y hbracket
      F hF (G.curve q r) s (hFtime r hr))
  have hEq := IntegralCurves.overlap_unique S B Y I I
    (f ∘ G.curve q) (G.curve (f q)) hcurve
    (IntegralCurves.integral_mono (hG (f q)).2.2.1 hGI') 0 ⟨h0, h0⟩
    (by simp only [Function.comp_apply, (hG q).2.1, (hG (f q)).2.1])
  exact (hEq ⟨ht, ht⟩).symm


/-- Uniform small times and nearby initial states remain in any prescribed
open neighborhood. The domain condition is included in the same box. -/
theorem flow_neighborhood {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (U : Set M) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ q ∈ V, ∀ t ∈ Ioo (-ε) ε,
        t ∈ (F.interval q).carrier ∧ F.curve q t ∈ U := by
  have hreg := MaximalFlow.domain_open_smooth S B X F hF
  have hzero : flow F (0, p) ∈ U := by
    change F.curve p 0 ∈ U
    rwa [(hF p).2.1]
  have hAll : ∀ᶠ z in 𝓝 (0, p), z ∈ flowDomain F ∧ flow F z ∈ U :=
    inter_mem (hreg.1.mem_nhds (show (0, p) ∈ flowDomain F from (hF p).1))
      ((hreg.2 (0, p) (hF p).1).1.preimage_mem_nhds (hU.mem_nhds hzero))
  obtain ⟨A, hA, V₀, hV₀, hAV⟩ := mem_nhds_prod_iff.mp hAll
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hA
  obtain ⟨V, hVV, hV, hpV⟩ := mem_nhds_iff.mp hV₀
  let ε : ℝ := min (-a) b
  have hε : 0 < ε := lt_min (neg_pos.mpr ha) hb
  refine ⟨ε, hε, V, hV, hpV, ?_⟩
  intro q hq t ht
  apply hAV (a := (t, q))
  exact ⟨hab ⟨by linarith [ht.1, min_le_left (-a) b],
    lt_of_lt_of_le ht.2 (min_le_right (-a) b)⟩, hVV hq⟩

/-- If the bracket vanishes on an open neighborhood, small time maps
preserve Y at every nearby initial state. The inverse trajectory used for
pullback invariance is kept inside that neighborhood. -/
theorem timeMap_preservesFieldAt_near {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (U : Set M) (hU : IsOpen U) (hpU : p ∈ U)
    (hbracket : ∀ q ∈ U, (b X Y).val q = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ q ∈ V, ∀ s ∈ Ioo (-ε) ε,
        s ∈ (F.interval q).carrier ∧
          PreservesFieldAt Y (fun x => F.curve x s) q := by
  obtain ⟨δ, hδ, W, hW, hpW, hFW⟩ := flow_neighborhood S B X F hF p U hU hpU
  obtain ⟨η, hη, V, hV, hpV, hFV⟩ := flow_neighborhood S B X F hF p W hW hpW
  let ε : ℝ := min δ η
  have hε : 0 < ε := lt_min hδ hη
  refine ⟨ε, hε, V, hV, hpV, ?_⟩
  intro q hq s hs
  have hsδ : s ∈ Ioo (-δ) δ :=
    ⟨by linarith [hs.1, min_le_left δ η], lt_of_lt_of_le hs.2 (min_le_left δ η)⟩
  have hsη : s ∈ Ioo (-η) η :=
    ⟨by linarith [hs.1, min_le_right δ η], lt_of_lt_of_le hs.2 (min_le_right δ η)⟩
  have hqs := hFV q hq s hsη
  let J : D13Unified.OpenTimeInterval :=
    { carrier := Ioo (-δ) δ
      nonempty := ⟨0, by exact ⟨neg_neg_of_pos hδ, hδ⟩⟩
      ordConnected := ordConnected_Ioo
      isOpen := isOpen_Ioo }
  refine ⟨hqs.1, timeMap_preservesFieldAt_on_interval
    BracketFromFlow.derivative_at_time BracketFromFlow.pullback_boundaryless
    S B b hb X Y F hF q s hqs.1 J
    ⟨neg_neg_of_pos hδ, hδ⟩ ⟨by linarith [hsδ.2], by linarith [hsδ.1]⟩ ?_ ?_⟩
  · intro r hr
    exact (hFW (F.curve q s) hqs.2 r hr).1
  · intro r hr
    exact hbracket _ (hFW (F.curve q s) hqs.2 r hr).2

/-- Local commutation needs bracket vanishing only near the initial point.
Both composition domains and every intervening trajectory segment are
controlled on the same time/state box. -/
theorem local_commutation_on_neighborhood {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B) (F G : CurveFamily M)
    (hF : IsMaximalFamily X F) (hG : IsMaximalFamily Y G)
    (p : M) (W : Set M) (hW : IsOpen W) (hpW : p ∈ W)
    (hbracket : ∀ q ∈ W, (b X Y).val q = 0) : CommuteNear F G p := by
  obtain ⟨a, ha, A, hA, hpA, hpres⟩ :=
    timeMap_preservesFieldAt_near S B b hb X Y F hF p W hW hpW hbracket
  obtain ⟨c, hc, C, hC, hpC, hGC⟩ := flow_neighborhood S B Y G hG p A hA hpA
  obtain ⟨d, hd, D, hD, hpD, hdom⟩ := common_composition_neighborhood S B X Y F G hF hG p
  let ε : ℝ := min a (min c d)
  have hε : 0 < ε := lt_min ha (lt_min hc hd)
  have hεa : ε ≤ a := min_le_left _ _
  have hεc : ε ≤ c := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεd : ε ≤ d := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsmall (r : ℝ) (hr : r ∈ Ioo (-ε) ε) (z : ℝ) (hz : ε ≤ z) :
      r ∈ Ioo (-z) z := ⟨by linarith [hr.1], lt_of_lt_of_le hr.2 hz⟩
  refine ⟨ε, hε, C ∩ D, hC.inter hD, ⟨hpC, hpD⟩, ?_⟩
  intro q hq s hs t ht
  have hbox (r : ℝ) (hr : r ∈ Ioo (-ε) ε) :=
    hdom q hq.2 s (hsmall s hs d hεd) r (hsmall r hr d hεd)
  refine ⟨hbox t ht, ?_⟩
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  let I : D13Unified.OpenTimeInterval :=
    { carrier := Ioo (-ε) ε
      nonempty := ⟨0, h0⟩
      ordConnected := ordConnected_Ioo
      isOpen := isOpen_Ioo }
  have hGI : I.carrier ⊆ (G.interval q).carrier := fun r hr => (hbox r hr).2.1
  have hGI' : I.carrier ⊆ (G.interval (F.curve q s)).carrier :=
    fun r hr => (hbox r hr).2.2.1
  let f : M → M := fun x => F.curve x s
  have hreg := (MaximalFlow.domain_open_smooth S B X F hF).2
  have hcurve := integralCurve_map S B Y I.isOpen (G.curve q)
    (IntegralCurves.integral_mono (hG q).2.2.1 hGI) f
    (fun r hr => timeMap_smoothAt S F s (G.curve q r)
      (hreg (s, G.curve q r) (hbox r hr).2.2.2))
    (fun r hr => (hpres (G.curve q r)
      (hGC q hq.1 r (hsmall r hr c hεc)).2 s (hsmall s hs a hεa)).2)
  have hEq := IntegralCurves.overlap_unique S B Y I I
    (f ∘ G.curve q) (G.curve (f q)) hcurve
    (IntegralCurves.integral_mono (hG (f q)).2.2.1 hGI') 0 ⟨h0, h0⟩
    (by simp only [Function.comp_apply, (hG q).2.1, (hG (f q)).2.1])
  exact (hEq ⟨ht, ht⟩).symm

/-- Change a Euclidean chart by a partial coordinate diffeomorphism.
The target containment is asserted only on the actual parameter domain. -/
noncomputable def parameterChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M)
    (j : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hje : ∀ x ∈ j.source, MaximalFlow.euclideanModelPoint (j x) ∈ e.target) :
    ModelChart n .euclidean M where
  toFun q := MaximalFlow.euclideanModelPoint (j.symm (e q).val)
  invFun x := e.symm (MaximalFlow.euclideanModelPoint (j x.val))
  source := e.source ∩ (fun q => (e q).val) ⁻¹' j.target
  target := Subtype.val ⁻¹' j.source
  map_source' q hq := j.map_target hq.2
  map_target' x hx := by
    have he := hje x.val hx
    refine ⟨e.map_target he, ?_⟩
    change (e (e.symm (MaximalFlow.euclideanModelPoint (j x.val)))).val ∈ j.target
    rw [e.right_inv he]
    exact j.map_source hx
  left_inv' q hq := by
    change e.symm (MaximalFlow.euclideanModelPoint (j (j.symm (e q).val))) = q
    rw [j.right_inv hq.2]
    exact e.left_inv hq.1
  right_inv' x hx := by
    apply Subtype.ext
    change j.symm (e (e.symm (MaximalFlow.euclideanModelPoint (j x.val)))).val = x.val
    rw [e.right_inv (hje x.val hx)]
    exact j.left_inv hx
  open_source := (continuous_subtype_val.comp_continuousOn e.continuousOn_toFun).isOpen_inter_preimage
    e.open_source j.open_target
  open_target := j.open_source.preimage continuous_subtype_val
  continuousOn_toFun := (MaximalFlow.continuous_euclideanModelPoint n).comp_continuousOn
    (j.symm.continuousOn.comp
      ((continuous_subtype_val.comp_continuousOn e.continuousOn_toFun).mono inter_subset_left)
      (fun _ hx => hx.2))
  continuousOn_invFun := e.symm.continuousOn.comp
    ((MaximalFlow.continuous_euclideanModelPoint n).comp_continuousOn
      (j.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)))
    (fun x hx => hje x.val hx)

/-- A smooth partial change of Euclidean coordinates belongs to the original
maximal atlas. This proves atlas membership rather than adding it as data. -/
theorem parameterChart_mem {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val)
    (j : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hje : ∀ x ∈ j.source, MaximalFlow.euclideanModelPoint (j x) ∈ e.target)
    (hj : ContDiffOn ℝ (⊤ : ℕ∞) j j.source)
    (hji : ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target) :
    parameterChart e j hje ∈ S.smoothStructure.val := by
  let c := parameterChart e j hje
  have hec (q : M) (hq : q ∈ c.source) :
      ChartContDiffAt (⊤ : ℕ∞) e c id q :=
    ⟨j.target, j.open_target, hq.2, j.symm, hji, Eventually.of_forall (fun _ => rfl)⟩
  have hce (q : M) (hq : q ∈ c.source) :
      ChartContDiffAt (⊤ : ℕ∞) c e id q := by
    refine ⟨j.source, j.open_source, j.map_target hq.2, j, hj, ?_⟩
    filter_upwards [c.open_source.mem_nhds hq] with x hx
    exact j.right_inv hx.2
  let A := S.smoothStructure.val
  have hmax : maximalExtension (⊤ : ℕ∞) A = A :=
    S.smoothStructure.property.2 _ (maximalExtension_isContDiffAtlas S.smoothStructure.property.1)
      (subset_maximalExtension S.smoothStructure.property.1)
  change c ∈ A
  rw [← hmax]
  intro d hd
  apply contDiffCompatible_of_germs
  · intro q hqc hqd
    exact LocalCoordinateExtension.comp
      (chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 e he d hd) hqc.1 hqd)
      (hce q hqc)
  · intro q hqd hqc
    exact LocalCoordinateExtension.comp (hec q hqc)
      (chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 d hd e he) hqd hqc.1)

/-- Differentiating the actual partial-inverse equation gives a left inverse
on tangent coordinates at every point of the parameter chart. -/
theorem parameterChart_inverse_derivative {n : ℕ}
    (j : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hj : ContDiffOn ℝ (⊤ : ℕ∞) j j.source)
    (hji : ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target)
    (x : Euclidean n) (hx : x ∈ j.source) (v : Euclidean n) :
    fderiv ℝ j.symm (j x) (fderiv ℝ j x v) = v := by
  have hdj := ((hj.contDiffAt (j.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hdji := ((hji.contDiffAt (j.open_target.mem_nhds (j.map_source hx))).differentiableAt (by simp)).hasFDerivAt
  have hcomp := hdji.comp x hdj
  have heq : (j.symm ∘ j) =ᶠ[𝓝 x] id := by
    filter_upwards [j.open_source.mem_nhds hx] with y hy
    exact j.left_inv hy
  have h := hcomp.unique ((hasFDerivAt_id x).congr_of_eventuallyEq heq)
  exact congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L v) h

/-- A parameter chart whose coordinate derivative columns are the prescribed
fields gives simultaneous coordinates in the actual maximal smooth atlas. -/
theorem simultaneous_coordinates_of_parameter_chart
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : Fin k → SmoothField B) (p : M) (hk : k ≤ n)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (j : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hje : ∀ x ∈ j.source, MaximalFlow.euclideanModelPoint (j x) ∈ e.target)
    (hj : ContDiffOn ℝ (⊤ : ℕ∞) j j.source)
    (hji : ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target)
    (h0 : (0 : Euclidean n) ∈ j.source) (hj0 : j 0 = (e p).val)
    (hfield : ∀ x (hx : x ∈ j.source) (i : Fin k),
      B.fiberCoordinates.equiv e he
        (e.symm (MaximalFlow.euclideanModelPoint (j x))) (e.map_target (hje x hx))
        ((X i).val (e.symm (MaximalFlow.euclideanModelPoint (j x)))) =
          fderiv ℝ j x (Pi.single (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin n) 1)) :
    SimultaneousCoordinates B X p hk := by
  let c := parameterChart e j hje
  have hc : c ∈ S.smoothStructure.val := parameterChart_mem S e he j hje hj hji
  refine ⟨c, hc, ⟨hp, ?_⟩, ?_⟩
  · change (e p).val ∈ j.target
    rw [← hj0]
    exact j.map_source h0
  intro q hq i
  have htrans := TangentBundle.transition_jacobian S B.fiberCoordinates e c he hc q hq.1 hq
    j.target j.symm j.open_target hq.2 hji (Eventually.of_forall (fun _ => rfl))
      ((X i).val q)
  rw [htrans]
  let x := j.symm (e q).val
  have hx : x ∈ j.source := j.map_target hq.2
  have hjx : j x = (e q).val := j.right_inv hq.2
  have hqx : e.symm (MaximalFlow.euclideanModelPoint (j x)) = q := by
    rw [hjx]
    exact e.left_inv hq.1
  have hvec := hfield x hx i
  have hvec' : B.fiberCoordinates.equiv e he q hq.1 ((X i).val q) =
      fderiv ℝ j x (Pi.single (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin n) 1) := by
    have hvec'' : coefficients B (X i).val e he
        (e.symm (MaximalFlow.euclideanModelPoint (j x))) =
          fderiv ℝ j x (Pi.single (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin n) 1) := by
      simpa only [coefficients, dite_eq_left (e.map_target (hje x hx))] using hvec
    rw [hqx] at hvec''
    simpa only [coefficients, dite_eq_left hq.1] using hvec''
  rw [hvec', ← hjx]
  exact parameterChart_inverse_derivative j hj hji x hx _

/-- A smooth parametrization with invertible derivative and the prescribed
field columns yields simultaneous coordinates. Only its open parameter domain
is used; all chart membership and inverse regularity follow from the inverse
function theorem and the maximality of the given atlas. -/
theorem simultaneous_coordinates_of_parametrization
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : Fin k → SmoothField B) (p : M) (hk : k ≤ n)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (V : Set (Euclidean n)) (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ V)
    (f : Euclidean n → Euclidean n) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V)
    (hf0 : f 0 = (e p).val)
    (hfe : ∀ x ∈ V, MaximalFlow.euclideanModelPoint (f x) ∈ e.target)
    (hbij : Function.Bijective (fderiv ℝ f 0))
    (hfield : ∀ x ∈ V, ∀ i : Fin k,
      coefficients B (X i).val e he (e.symm (MaximalFlow.euclideanModelPoint (f x))) =
        fderiv ℝ f x (Pi.single (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin n) 1)) :
    SimultaneousCoordinates B X p hk := by
  have hdf := ((hf.contDiffAt (hV.mem_nhds h0)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨j, hj0, hjf, hji⟩ := InteriorInverse.euclidean_inverse
    (⊤ : ℕ∞) (by simp) f V hV hf 0 h0 (fderiv ℝ f 0) hdf hbij
  let l := j.restrOpen V hV
  have hl0 : (0 : Euclidean n) ∈ l.source := ⟨hj0, h0⟩
  have hlf : (l : Euclidean n → Euclidean n) = f := hjf
  have hle : ∀ x ∈ l.source, MaximalFlow.euclideanModelPoint (l x) ∈ e.target := by
    intro x hx
    rw [hlf]
    exact hfe x hx.2
  have hl : ContDiffOn ℝ (⊤ : ℕ∞) l l.source := by
    rw [hlf]
    exact hf.mono inter_subset_right
  have hli : ContDiffOn ℝ (⊤ : ℕ∞) l.symm l.target :=
    hji.mono (fun _ hx => hx.1)
  apply simultaneous_coordinates_of_parameter_chart S B X p hk e he hp l hle hl hli hl0
    (by rw [hlf]; exact hf0)
  intro x hx i
  have hv := hfield x hx.2 i
  have hv' : coefficients B (X i).val e he
      (e.symm (MaximalFlow.euclideanModelPoint (l x))) =
        fderiv ℝ l x (Pi.single (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin n) 1) := by
    simpa only [hlf] using hv
  simpa only [coefficients, dite_eq_left (e.map_target (hle x hx))] using hv' 

/-- Vanishing bracket implies local commutation on a common time/state box. -/
theorem local_commutation :
    Specs.SmoothManifolds.Ch06.CommutingFields.local_commutationType.{u} :=
  local_commutation_of_pullback BracketFromFlow.derivative_at_time
    BracketFromFlow.pullback_boundaryless

/-- Complete commuting fields have commuting flows for every pair of real times. -/
theorem complete_commutation :
    Specs.SmoothManifolds.Ch06.CommutingFields.complete_commutationType.{u} :=
  complete_commutation_of_pullback BracketFromFlow.derivative_at_time
    BracketFromFlow.pullback_boundaryless

end SmoothManifolds.CommutingFields



noncomputable section
namespace SmoothManifolds.CommutingFields
open ModelData AtlasData TangentBundleData VectorFieldData LieBracketData
  IntegralCurveData MaximalFlowData Set Filter
open scoped Topology
universe u

/-- The actual coordinate expression of a maximal flow, with its total
representative used only at admissible coordinate pairs. -/
def coordinateFlow {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (F : CurveFamily M)
    (w : ℝ × Euclidean n) : Euclidean n :=
  (e (F.curve (e.symm (MaximalFlow.euclideanModelPoint w.2)) w.1)).val

/-- At any admissible pair whose initial and moving points lie in the chart,
the actual coordinate representative is smooth. -/
theorem coordinateFlow_contDiffAt {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (w : ℝ × Euclidean n)
    (hw : MaximalFlow.euclideanModelPoint w.2 ∈ e.target)
    (ht : w.1 ∈ (F.interval (e.symm (MaximalFlow.euclideanModelPoint w.2))).carrier)
    (hq : F.curve (e.symm (MaximalFlow.euclideanModelPoint w.2)) w.1 ∈ e.source) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coordinateFlow e F) w := by
  let q := e.symm (MaximalFlow.euclideanModelPoint w.2)
  have hqsrc : q ∈ e.source := e.map_target hw
  have hqcoord : (e q).val = w.2 := congrArg Subtype.val (e.right_inv hw)
  obtain ⟨U, hU, hwU, G, hG, hEq⟩ :=
    ((MaximalFlow.domain_open_smooth S B X F hF).2 (w.1, q) ht).2
      e he e he hqsrc hq
  have hmodel : ContinuousAt (fun z : ℝ × Euclidean n =>
      MaximalFlow.euclideanModelPoint z.2) w :=
    (MaximalFlow.continuous_euclideanModelPoint n).continuousAt.comp continuousAt_snd
  have hi : ContinuousAt (fun z : ℝ × Euclidean n =>
      (z.1, e.symm (MaximalFlow.euclideanModelPoint z.2))) w :=
    continuousAt_fst.prodMk ((e.continuousAt_symm hw).comp
      (f := fun z : ℝ × Euclidean n => MaximalFlow.euclideanModelPoint z.2) hmodel)
  have hEq' := hEq.comp_tendsto hi
  have htarget : ∀ᶠ z : ℝ × Euclidean n in 𝓝 w,
      MaximalFlow.euclideanModelPoint z.2 ∈ e.target :=
    hmodel.preimage_mem_nhds (e.open_target.mem_nhds hw)
  have hCG : coordinateFlow e F =ᶠ[𝓝 w] G := by
    filter_upwards [hEq', htarget] with z hz hzsrc
    change (e (F.curve (e.symm (MaximalFlow.euclideanModelPoint z.2)) z.1)).val = G z
    have hzc : (e (e.symm (MaximalFlow.euclideanModelPoint z.2))).val = z.2 :=
      congrArg Subtype.val (e.right_inv hzsrc)
    change G (z.1, (e (e.symm (MaximalFlow.euclideanModelPoint z.2))).val) = _ at hz
    rw [hzc] at hz
    exact hz.symm
  have hwU' : w ∈ U := by simpa only [hqcoord] using hwU
  exact (hG.contDiffAt (hU.mem_nhds hwU')).congr_of_eventuallyEq hCG

/-- The time column of the actual coordinate flow is the actual field at the
moving point, at every admissible pair inside the chart. -/
theorem coordinateFlow_time_derivative {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (w : ℝ × Euclidean n)
    (hw : MaximalFlow.euclideanModelPoint w.2 ∈ e.target)
    (ht : w.1 ∈ (F.interval (e.symm (MaximalFlow.euclideanModelPoint w.2))).carrier)
    (hq : F.curve (e.symm (MaximalFlow.euclideanModelPoint w.2)) w.1 ∈ e.source) :
    fderiv ℝ (coordinateFlow e F) w (1, 0) =
      coefficients B X.val e he (F.curve (e.symm (MaximalFlow.euclideanModelPoint w.2)) w.1) := by
  have hC := coordinateFlow_contDiffAt S B X F hF e he w hw ht hq
  have hvel := (hC.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.1
    ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))
  have hode := (hF (e.symm (MaximalFlow.euclideanModelPoint w.2))).2.2.1.2 w.1 ht e he hq
  simpa only [coefficients, dite_eq_left hq] using hvel.unique hode.2

/-- The actual open coordinate domain, retaining both chart conditions and
actual maximal-time membership. -/
def coordinateFlowDomain {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (F : CurveFamily M) : Set (ℝ × Euclidean n) :=
  {w | MaximalFlow.euclideanModelPoint w.2 ∈ e.target ∧
    w.1 ∈ (F.interval (e.symm (MaximalFlow.euclideanModelPoint w.2))).carrier ∧
    F.curve (e.symm (MaximalFlow.euclideanModelPoint w.2)) w.1 ∈ e.source}

theorem coordinateFlowDomain_isOpen {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) : IsOpen (coordinateFlowDomain e F) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  have hmodel : ContinuousAt (fun z : ℝ × Euclidean n =>
      MaximalFlow.euclideanModelPoint z.2) w :=
    (MaximalFlow.continuous_euclideanModelPoint n).continuousAt.comp continuousAt_snd
  have hi : ContinuousAt (fun z : ℝ × Euclidean n =>
      (z.1, e.symm (MaximalFlow.euclideanModelPoint z.2))) w :=
    continuousAt_fst.prodMk ((e.continuousAt_symm hw.1).comp
      (f := fun z : ℝ × Euclidean n => MaximalFlow.euclideanModelPoint z.2) hmodel)
  have hreg := MaximalFlow.domain_open_smooth S B X F hF
  have hstate : ContinuousAt (fun z : ℝ × Euclidean n =>
      F.curve (e.symm (MaximalFlow.euclideanModelPoint z.2)) z.1) w :=
    (hreg.2 _ hw.2.1).1.comp hi
  filter_upwards [hmodel.preimage_mem_nhds (e.open_target.mem_nhds hw.1),
    hi.preimage_mem_nhds (hreg.1.mem_nhds hw.2.1),
    hstate.preimage_mem_nhds (e.open_source.mem_nhds hw.2.2)] with z hz₁ hz₂ hz₃
  exact ⟨hz₁, hz₂, hz₃⟩

theorem coordinateFlow_contDiffOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateFlow e F) (coordinateFlowDomain e F) := by
  intro w hw
  exact (coordinateFlow_contDiffAt S B X F hF e he w hw.1 hw.2.1 hw.2.2).contDiffWithinAt

theorem coordinateFlow_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (z : Euclidean n)
    (hz : MaximalFlow.euclideanModelPoint z ∈ e.target) :
    coordinateFlow e F (0, z) = z := by
  change (e (F.curve _ 0)).val = z
  rw [(hF _).2.1]
  exact congrArg Subtype.val (e.right_inv hz)

theorem coordinateFlow_zero_mem {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (p : M) (hp : p ∈ e.source) :
    (0, (e p).val) ∈ coordinateFlowDomain e F := by
  refine ⟨e.map_source hp, (hF _).1, ?_⟩
  rw [(hF _).2.1]
  exact e.map_target (e.map_source hp)

theorem coordinateFlow_state_derivative_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (z : Euclidean n) (hz : MaximalFlow.euclideanModelPoint z ∈ e.target)
    (v : Euclidean n) : fderiv ℝ (coordinateFlow e F) (0, z) (0, v) = v := by
  have hzero : F.curve (e.symm (MaximalFlow.euclideanModelPoint z)) 0 ∈ e.source := by
    rw [(hF _).2.1]
    exact e.map_target hz
  have hC := coordinateFlow_contDiffAt S B X F hF e he (0,z) hz (hF _).1 hzero
  have hd := (hC.differentiableAt (by simp)).hasFDerivAt.comp z
    ((hasFDerivAt_const (0 : ℝ) z).prodMk (hasFDerivAt_id z))
  have hEq : (coordinateFlow e F ∘ fun y : Euclidean n => (0,y)) =ᶠ[𝓝 z] id := by
    filter_upwards [((MaximalFlow.continuous_euclideanModelPoint n).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds hz))] with y hy
    exact coordinateFlow_zero S B X F hF e y hy
  have h := (hd.congr_of_eventuallyEq hEq.symm).unique (hasFDerivAt_id z)
  exact congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L v) h

end SmoothManifolds.CommutingFields


namespace SmoothManifolds.CommutingFields
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  VectorFieldData LieBracketData MaximalFlowData BracketFlowData Set Filter
open scoped Topology
universe u

/-- The germ field-preservation equation computes the ordinary Jacobian of
any smooth Euclidean representative, in arbitrary source and target charts. -/
theorem preservesFieldAt_jacobian
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (Y : SmoothField B) (f : M → M) (q : M)
    (hf : ManifoldSmoothAt S.smoothStructure.val S.smoothStructure.val f q)
    (hY : PreservesFieldAt Y f q)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hq : q ∈ e.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hfq : f q ∈ d.source)
    (U : Set (Euclidean n)) (H : Euclidean n → Euclidean n)
    (hU : IsOpen U) (hqU : (e q).val ∈ U)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U)
    (heH : (fun r => H (e r).val) =ᶠ[𝓝 q]
      (fun r => (d (f r)).val)) :
    fderiv ℝ H (e q).val (coefficients B Y.val e he q) =
      coefficients B Y.val d hd (f q) := by
  obtain ⟨L, hL, _⟩ := BracketFromFlow.differentialAt_exists S S f q hf
  have hLY : L (Y.val q) = Y.val (f q) := by
    apply Subtype.ext
    apply LinearMap.ext
    intro h
    obtain ⟨r, _, hr⟩ := (mem_smoothGermAlgebra_iff S (f q) h.val).mp h.property
    let k := BracketFromFlow.localGermPullback S S f q hf h
    have hk : Germ.ofFun (r ∘ f) = k.val :=
      (BracketFromFlow.localGermPullback_rep S S f q hf h r hr.symm).symm
    exact (hL (Y.val q) h k r hr.symm hk).trans (hY h k r hr.symm hk).symm
  have hj := BracketFromFlow.rebased_jacobian B f q (f q) L hL
    d hd hfq e he hq U H hU hqU hH heH (Y.val q)
  rw [hLY] at hj
  simpa only [coefficients, dite_eq_left hq, dite_eq_left hfq] using hj.symm

end SmoothManifolds.CommutingFields

namespace SmoothManifolds.CommutingFields
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  VectorFieldData LieBracketData IntegralCurveData MaximalFlowData BracketFlowData
  Set Filter
open scoped Topology
universe u

/-- Field preservation gives the state columns of the actual coordinate flow
on every open set where that representative is smooth. -/
theorem coordinateFlow_state_derivative
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X Y : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (W : Set (ℝ × Euclidean n)) (hW : IsOpen W)
    (hC : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateFlow e F) W)
    (w : ℝ × Euclidean n) (hwW : w ∈ W)
    (hw : MaximalFlow.euclideanModelPoint w.2 ∈ e.target)
    (ht : w.1 ∈ (F.interval (e.symm (MaximalFlow.euclideanModelPoint w.2))).carrier)
    (hq : F.curve (e.symm (MaximalFlow.euclideanModelPoint w.2)) w.1 ∈ e.source)
    (hY : PreservesFieldAt Y (fun r => F.curve r w.1)
      (e.symm (MaximalFlow.euclideanModelPoint w.2))) :
    fderiv ℝ (coordinateFlow e F) w
        (0, coefficients B Y.val e he (e.symm (MaximalFlow.euclideanModelPoint w.2))) =
      coefficients B Y.val e he
        (F.curve (e.symm (MaximalFlow.euclideanModelPoint w.2)) w.1) := by
  let q := e.symm (MaximalFlow.euclideanModelPoint w.2)
  have hqsrc : q ∈ e.source := e.map_target hw
  have hqcoord : (e q).val = w.2 := congrArg Subtype.val (e.right_inv hw)
  let H : Euclidean n → Euclidean n := fun z => coordinateFlow e F (w.1, z)
  let V : Set (Euclidean n) := (fun z => (w.1, z)) ⁻¹' W
  have hV : IsOpen V := hW.preimage (continuous_const.prodMk continuous_id)
  have hqV : (e q).val ∈ V := by
    change (w.1, (e q).val) ∈ W
    rw [hqcoord]
    exact hwW
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H V :=
    hC.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => hz)
  have heH : (fun r => H (e r).val) =ᶠ[𝓝 q]
      (fun r => (e (F.curve r w.1)).val) := by
    filter_upwards [e.open_source.mem_nhds hqsrc] with r hr
    change (e (F.curve (e.symm (MaximalFlow.euclideanModelPoint (e r).val)) w.1)).val = _
    rw [show e.symm (MaximalFlow.euclideanModelPoint (e r).val) = r from e.left_inv hr]
  have hj := preservesFieldAt_jacobian B Y (fun r => F.curve r w.1) q
    (timeMap_smoothAt S F w.1 q ((MaximalFlow.domain_open_smooth S B X F hF).2 (w.1, q) ht))
    hY e he hqsrc e he hq V H hV hqV hH heH
  have hder := ((hC.contDiffAt (hW.mem_nhds hwW)).differentiableAt (by simp)).hasFDerivAt.comp w.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) w.1 w.2)
  change HasFDerivAt H _ w.2 at hder
  rw [hqcoord, hder.fderiv] at hj
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using hj

/-- Coordinate coefficient maps of the prescribed fields on one fixed chart. -/
def coordinateField {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : Fin k → SmoothField B)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (i : Fin k) (z : Euclidean n) : Euclidean n :=
  coefficients B (X i).val e he (e.symm (MaximalFlow.euclideanModelPoint z))

end SmoothManifolds.CommutingFields

namespace SmoothManifolds.CommutingFields
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  VectorFieldData LieBracketData IntegralCurveData MaximalFlowData BracketFlowData
  Set Filter
open scoped Topology
universe u

/-- One actual maximal flow admits a smooth coordinate neighborhood on which
its state differential preserves every field in a finite commuting family. -/
theorem coordinate_flow_package_one
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X : Fin k → SmoothField B) (p : M)
    (U : Set M) (hU : IsOpen U) (hpU : p ∈ U)
    (hbr : ∀ (i j : Fin k) (q : M), q ∈ U → (b (X i) (X j)).val q = 0)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (i : Fin k) (F : CurveFamily M) (hF : IsMaximalFamily (X i) F) :
    ∃ W : Set (ℝ × Euclidean n), IsOpen W ∧ (0, (e p).val) ∈ W ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (coordinateFlow e F) W ∧
      (coordinateFlow e F (0, (e p).val) = (e p).val) ∧
      (∀ v, fderiv ℝ (coordinateFlow e F) (0, (e p).val) (0, v) = v) ∧
      (∀ w ∈ W, fderiv ℝ (coordinateFlow e F) w (1, 0) =
        coordinateField B X e he i (coordinateFlow e F w)) ∧
      (∀ (j : Fin k) (w : ℝ × Euclidean n), w ∈ W →
        fderiv ℝ (coordinateFlow e F) w (0, coordinateField B X e he j w.2) =
          coordinateField B X e he j (coordinateFlow e F w)) := by
  classical
  have hpres (j : Fin k) : ∀ᶠ z : ℝ × M in 𝓝 (0, p),
      PreservesFieldAt (X j) (fun q => F.curve q z.1) z.2 := by
    obtain ⟨ε, hε, V, hV, hpV, hP⟩ := timeMap_preservesFieldAt_near
      S B b hb (X i) (X j) F hF p U hU hpU (hbr i j)
    have hbox : Ioo (-ε) ε ×ˢ V ∈ 𝓝 ((0 : ℝ), p) :=
      prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨neg_neg_of_pos hε, hε⟩) (hV.mem_nhds hpV)
    filter_upwards [hbox] with z hz
    exact (hP z.2 hz.2 z.1 hz.1).2
  have hpresAll : ∀ᶠ z : ℝ × M in 𝓝 (0, p),
      ∀ j : Fin k, PreservesFieldAt (X j) (fun q => F.curve q z.1) z.2 :=
    Filter.eventually_all.mpr hpres
  have hdecode : e.symm (MaximalFlow.euclideanModelPoint (e p).val) = p := e.left_inv hp
  have hmodel : ContinuousAt (fun w : ℝ × Euclidean n =>
      MaximalFlow.euclideanModelPoint w.2) (0, (e p).val) :=
    (MaximalFlow.continuous_euclideanModelPoint n).continuousAt.comp continuousAt_snd
  have hi : ContinuousAt (fun w : ℝ × Euclidean n =>
      (w.1, e.symm (MaximalFlow.euclideanModelPoint w.2))) (0, (e p).val) :=
    continuousAt_fst.prodMk ((e.continuousAt_symm (e.map_source hp)).comp
      (f := fun w : ℝ × Euclidean n => MaximalFlow.euclideanModelPoint w.2) hmodel)
  have hi' : Tendsto (fun w : ℝ × Euclidean n =>
      (w.1, e.symm (MaximalFlow.euclideanModelPoint w.2)))
      (𝓝 (0, (e p).val)) (𝓝 (0, p)) := by
    change Tendsto _ (𝓝 (0, (e p).val))
      (𝓝 (0, e.symm (MaximalFlow.euclideanModelPoint (e p).val))) at hi
    rwa [hdecode] at hi
  have hDom : ∀ᶠ w in 𝓝 ((0 : ℝ), (e p).val), w ∈ coordinateFlowDomain e F :=
    (coordinateFlowDomain_isOpen S B (X i) F hF e).mem_nhds
      (coordinateFlow_zero_mem S B (X i) F hF e p hp)
  have hAll := hDom.and (hi'.eventually hpresAll)
  obtain ⟨W, hWA, hW, hw0⟩ := mem_nhds_iff.mp hAll
  have hCW : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateFlow e F) W :=
    (coordinateFlow_contDiffOn S B (X i) F hF e he).mono (fun _ hw => (hWA hw).1)
  have hmove (w : ℝ × Euclidean n) (hw : w ∈ W) :
      e.symm (MaximalFlow.euclideanModelPoint (coordinateFlow e F w)) =
        F.curve (e.symm (MaximalFlow.euclideanModelPoint w.2)) w.1 :=
    e.left_inv (hWA hw).1.2.2
  refine ⟨W, hW, hw0, hCW, coordinateFlow_zero S B (X i) F hF e _ (e.map_source hp),
    coordinateFlow_state_derivative_zero S B (X i) F hF e he _ (e.map_source hp), ?_, ?_⟩
  · intro w hw
    have hD := (hWA hw).1
    have hv := coordinateFlow_time_derivative S B (X i) F hF e he w hD.1 hD.2.1 hD.2.2
    simpa only [coordinateField, hmove w hw] using hv
  · intro j w hw
    have hD := (hWA hw).1
    have hs := coordinateFlow_state_derivative S B (X i) (X j) F hF e he
      W hW hCW w hw hD.1 hD.2.1 hD.2.2 ((hWA hw).2 j)
    simpa only [coordinateField, hmove w hw] using hs

/-- The finite commuting family gives precisely the coordinate evolution data
needed by finite composition, on genuine open time/state neighborhoods. -/
theorem coordinate_flow_package
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X : Fin k → SmoothField B) (p : M)
    (U : Set M) (hU : IsOpen U) (hpU : p ∈ U)
    (hbr : ∀ (i j : Fin k) (q : M), q ∈ U → (b (X i) (X j)).val q = 0)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    ∃ (H : Fin k → ℝ × Euclidean n → Euclidean n)
      (W : Fin k → Set (ℝ × Euclidean n)),
      (∀ i, IsOpen (W i)) ∧ (∀ i, (0, (e p).val) ∈ W i) ∧
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (H i) (W i)) ∧
      (∀ i, H i (0, (e p).val) = (e p).val) ∧
      (∀ i v, fderiv ℝ (H i) (0, (e p).val) (0, v) = v) ∧
      (∀ i w, w ∈ W i → fderiv ℝ (H i) w (1, 0) =
        coordinateField B X e he i (H i w)) ∧
      (∀ (i j : Fin k), j.val < i.val → ∀ w, w ∈ W i →
        fderiv ℝ (H i) w (0, coordinateField B X e he j w.2) =
          coordinateField B X e he j (H i w)) := by
  classical
  choose F hF using fun i => MaximalFlow.maximal_family_exists S B (X i)
  choose W hW hW0 hC hC0 hS0 hV hP using fun i =>
    coordinate_flow_package_one S B b hb X p U hU hpU hbr e he hp i (F i) (hF i)
  exact ⟨(fun i => coordinateFlow e (F i)), W, hW, hW0, hC, hC0, hS0,
    hV, fun i j _ w hw => hP i j w hw⟩

end SmoothManifolds.CommutingFields

namespace SmoothManifolds.CommutingFields
open Module ModelData

/-- Complete a linearly independent list to an invertible linear coordinate map. -/
theorem linear_completion {k n : ℕ} (hk : k ≤ n)
    (v : Fin k → Euclidean n) (hv : LinearIndependent ℝ v) :
    ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
      ∀ i : Fin k, A (Pi.single (Fin.castLE hk i) 1) = v i := by
  classical
  let s : Set (Euclidean n) := hv.linearIndepOn_id.extend (Set.subset_univ _)
  let b : Basis s ℝ (Euclidean n) := Basis.extend hv.linearIndepOn_id
  let : Fintype s := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card s = n := by
    rw [← Module.finrank_eq_card_basis b]
    simp [Euclidean, ModelData.Euclidean, Module.finrank_fintype_fun_eq_card]
  let e : s ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let g : Fin k → s := fun i => ⟨v i, hv.linearIndepOn_id.subset_extend _ ⟨i, rfl⟩⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hv.injective
    exact congrArg Subtype.val hij
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hk) (fun i => e (g i))
    (Fin.castLE_injective hk) (e.injective.comp hg)
  let c : Basis (Fin n) ℝ (Euclidean n) := b.reindex (e.trans σ.symm)
  refine ⟨c.equivFun.symm.toContinuousLinearEquiv, ?_⟩
  intro i
  change c.equivFun.symm (Pi.single (Fin.castLE hk i) 1) = v i
  rw [Basis.equivFun_symm_single]
  change (b.reindex (e.trans σ.symm)) (Fin.castLE hk i) = v i
  rw [Basis.reindex_apply]
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm, hσ, Equiv.symm_apply_apply]
  exact Basis.extend_apply_self hv.linearIndepOn_id (g i)

end SmoothManifolds.CommutingFields



namespace SmoothManifolds.CommutingFields
open ModelData Set

/-- Finite composition of local smooth evolution maps with their velocity
and field-preservation equations. -/
theorem finite_flow_parametrization {n k : ℕ} (hk : k ≤ n)
    (z₀ : Euclidean n) (A : Euclidean n ≃L[ℝ] Euclidean n)
    (v : Fin k → Euclidean n → Euclidean n)
    (hAv : ∀ i : Fin k, A (Pi.single (Fin.castLE hk i) 1) = v i z₀)
    (H : Fin k → ℝ × Euclidean n → Euclidean n)
    (W : Fin k → Set (ℝ × Euclidean n))
    (hW : ∀ i, IsOpen (W i)) (hW₀ : ∀ i, (0, z₀) ∈ W i)
    (hH : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (H i) (W i))
    (hH₀ : ∀ i, H i (0, z₀) = z₀)
    (hstate₀ : ∀ i w, fderiv ℝ (H i) (0, z₀) (0, w) = w)
    (hvelocity : ∀ i z, z ∈ W i →
      fderiv ℝ (H i) z (1, 0) = v i (H i z))
    (hpreserve : ∀ (i j : Fin k), j.val < i.val → ∀ z, z ∈ W i →
      fderiv ℝ (H i) z (0, v j z.2) = v j (H i z)) :
    ∃ V : Set (Euclidean n), IsOpen V ∧ (0 : Euclidean n) ∈ V ∧
      ∃ f : Euclidean n → Euclidean n,
        ContDiffOn ℝ (⊤ : ℕ∞) f V ∧ f 0 = z₀ ∧
        fderiv ℝ f 0 = A.toContinuousLinearMap ∧
        ∀ x ∈ V, ∀ i : Fin k,
          fderiv ℝ f x (Pi.single (Fin.castLE hk i) 1) = v i (f x) := by
  classical
  let P : Euclidean n →L[ℝ] Euclidean n :=
    ContinuousLinearMap.pi (fun l : Fin n => if k ≤ l.val then ContinuousLinearMap.proj l else 0)
  have hP (l : Fin n) : P (Pi.single l 1) = if k ≤ l.val then Pi.single l 1 else 0 := by
    ext j
    simp only [P, ContinuousLinearMap.pi_apply]
    by_cases hl : k ≤ l.val
    · by_cases hj : k ≤ j.val
      · simp [hl, hj]
      · have hne : l ≠ j := by intro h; subst j; contradiction
        simp [hl, hj, Pi.single_eq_of_ne hne.symm]
    · by_cases hj : k ≤ j.val
      · have hne : l ≠ j := by intro h; subst j; contradiction
        simp [hl, hj, Pi.single_eq_of_ne hne.symm]
      · simp [hl, hj]
  have hstage : ∀ m, m ≤ k → ∃ V : Set (Euclidean n), IsOpen V ∧ (0 : Euclidean n) ∈ V ∧
      ∃ f : Euclidean n → Euclidean n,
        ContDiffOn ℝ (⊤ : ℕ∞) f V ∧ f 0 = z₀ ∧
        (∀ x ∈ V, ∀ i : Fin k,
          fderiv ℝ f x (Pi.single (Fin.castLE hk i) 1) =
            if i.val < m then v i (f x) else 0) ∧
        ∀ l : Fin n, k ≤ l.val →
          fderiv ℝ f 0 (Pi.single l 1) = A (Pi.single l 1) := by
    intro m
    induction m with
    | zero =>
      intro _
      let f : Euclidean n → Euclidean n := fun x => z₀ + A (P x)
      have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_const.add (A.contDiff.comp P.contDiff)
      refine ⟨univ, isOpen_univ, mem_univ _, f, hf.contDiffOn, by simp [f], ?_, ?_⟩
      · intro x _ i
        have hd : fderiv ℝ f x = A.toContinuousLinearMap.comp P := by
          exact ((A.hasFDerivAt.comp x P.hasFDerivAt).const_add z₀).fderiv
        rw [hd]
        simp [ContinuousLinearMap.comp_apply, hP, i.isLt]
      · intro l hl
        have hd : fderiv ℝ f 0 = A.toContinuousLinearMap.comp P := by
          exact ((A.hasFDerivAt.comp (0 : Euclidean n) P.hasFDerivAt).const_add z₀).fderiv
        rw [hd]
        simp [ContinuousLinearMap.comp_apply, hP, hl]
    | succ m ih =>
      intro hmk
      have hm : m < k := Nat.lt_of_succ_le hmk
      let a : Fin k := ⟨m, hm⟩
      let l : Fin n := Fin.castLE hk a
      obtain ⟨V, hV, h0, f, hf, hf0, hcols, htail⟩ := ih (Nat.le_of_succ_le hmk)
      let C : Euclidean n → ℝ × Euclidean n := fun x => (x l, f x)
      have hC : ContDiffOn ℝ (⊤ : ℕ∞) C V :=
        (contDiff_apply ℝ (fun _ : Fin n => ℝ) l).contDiffOn.prodMk hf
      let V' := V ∩ C ⁻¹' W a
      have hV' : IsOpen V' := hC.continuousOn.isOpen_inter_preimage hV (hW a)
      have h0' : (0 : Euclidean n) ∈ V' := ⟨h0, by simpa [C, hf0] using hW₀ a⟩
      let g : Euclidean n → Euclidean n := H a ∘ C
      have hg : ContDiffOn ℝ (⊤ : ℕ∞) g V' :=
        (hH a).comp (hC.mono inter_subset_left) (fun _ hx => hx.2)
      have hg0 : g 0 = z₀ := by simpa [g, C, hf0] using hH₀ a
      have hd (x : Euclidean n) (hx : x ∈ V') :
          fderiv ℝ g x = (fderiv ℝ (H a) (C x)).comp
            ((ContinuousLinearMap.proj l).prod (fderiv ℝ f x)) := by
        have hdf := ((hf.contDiffAt (hV.mem_nhds hx.1)).differentiableAt (by simp)).hasFDerivAt
        have hdH := ((hH a).contDiffAt ((hW a).mem_nhds hx.2)).differentiableAt (by simp)
        exact (hdH.hasFDerivAt.comp x ((hasFDerivAt_apply l x).prodMk hdf)).fderiv
      refine ⟨V', hV', h0', g, hg, hg0, ?_, ?_⟩
      · intro x hx i
        rw [hd x hx, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
        change fderiv ℝ (H a) (C x)
          ((Pi.single (Fin.castLE hk i) 1 : Euclidean n) l,
            fderiv ℝ f x (Pi.single (Fin.castLE hk i) 1)) = _
        rw [hcols x hx.1 i]
        by_cases hi : i.val < m
        · have hil : Fin.castLE hk i ≠ l := by
            intro heq
            have := congrArg Fin.val heq
            change i.val = m at this
            omega
          have him : i.val < m + 1 := Nat.lt_succ_of_lt hi
          simp only [hi, ite_true, Pi.single_eq_of_ne hil.symm, him]
          exact hpreserve a i hi (C x) hx.2
        · by_cases hie : i.val = m
          · have hie' : i = a := Fin.ext hie
            subst i
            have ham : a.val < m + 1 := Nat.lt_succ_self m
            have han : ¬ a.val < m := Nat.lt_irrefl m
            simpa only [han, ite_false, l, Pi.single_eq_same, ham, ite_true, g, Function.comp_def] using hvelocity a (C x) hx.2
          · have hil : Fin.castLE hk i ≠ l := by
              intro heq
              exact hie (congrArg Fin.val heq)
            have him : ¬i.val < m + 1 := by omega
            simp only [hi, ite_false, Pi.single_eq_of_ne hil.symm, him, Prod.mk_zero_zero, map_zero]
      · intro j hj
        rw [hd 0 h0', ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
        have hjl : j ≠ l := by
          intro heq
          have heq' : j.val = m := congrArg Fin.val heq
          omega
        simp only [ContinuousLinearMap.proj_apply, Pi.single_eq_of_ne hjl.symm, htail j hj]
        simpa only [C, Pi.zero_apply, hf0] using hstate₀ a (A (Pi.single j 1))
  obtain ⟨V, hV, h0, f, hf, hf0, hcols, htail⟩ := hstage k le_rfl
  refine ⟨V, hV, h0, f, hf, hf0, ?_, ?_⟩
  · have heq (l : Fin n) : fderiv ℝ f 0 (Pi.single l 1) = A (Pi.single l 1) := by
      by_cases hl : l.val < k
      · let i : Fin k := ⟨l.val, hl⟩
        have hil : Fin.castLE hk i = l := Fin.ext rfl
        have h := hcols 0 h0 i
        simp only [i.isLt, ite_true, hf0] at h
        rw [hil] at h
        exact h.trans (by simpa only [hil] using (hAv i).symm)
      · exact htail l (Nat.le_of_not_lt hl)
    apply ContinuousLinearMap.ext
    intro x
    have hx : x = ∑ l : Fin n, x l • Pi.single l (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hx, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun l _ => by rw [map_smul, map_smul, heq]; rfl)
  · intro x hx i
    simpa only [i.isLt, ite_true] using hcols x hx i

end SmoothManifolds.CommutingFields



noncomputable section
namespace SmoothManifolds.CommutingFields
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  VectorFieldData LieBracketData IntegralCurveData MaximalFlowData BracketFlowData CommutingFieldsData Set Filter
open scoped Topology
universe u

/-- The original tangent independence persists in any actual chart coordinates. -/
theorem coordinateField_independent_at_base
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (X : Fin k → SmoothField B) (p : M)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (hlin : LinearIndependent ℝ (fun i => (X i).val p)) :
    LinearIndependent ℝ (fun i => coordinateField B X e he i (e p).val) := by
  have hi : e.symm (MaximalFlow.euclideanModelPoint (e p).val) = p := e.left_inv hp
  let L : TangentSpace S p →ₗ[ℝ] Euclidean n :=
    (B.fiberCoordinates.equiv e he p hp).toLinearMap
  have hv : LinearIndependent ℝ (L ∘ (fun i : Fin k => (X i).val p)) :=
    (L.linearIndependent_iff_of_injOn
      (B.fiberCoordinates.equiv e he p hp).injective.injOn).mpr hlin
  convert hv using 1
  funext i
  change coefficients B (X i).val e he
    (e.symm (MaximalFlow.euclideanModelPoint (e p).val)) = L ((X i).val p)
  rw [hi]
  simp only [coefficients, dite_eq_left hp]
  rfl

/-- The smooth finite coordinate evolution, restricted to the actual chart
range, yields the simultaneous chart by the inverse function theorem. -/
theorem simultaneous_coordinates_of_coordinate_evolutions
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : Fin k → SmoothField B) (p : M) (hk : k ≤ n)
    (hlin : LinearIndependent ℝ (fun i => (X i).val p))
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (H : Fin k → ℝ × Euclidean n → Euclidean n)
    (W : Fin k → Set (ℝ × Euclidean n))
    (hW : ∀ i, IsOpen (W i)) (hW₀ : ∀ i, (0, (e p).val) ∈ W i)
    (hH : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (H i) (W i))
    (hH₀ : ∀ i, H i (0, (e p).val) = (e p).val)
    (hstate₀ : ∀ i w, fderiv ℝ (H i) (0, (e p).val) (0, w) = w)
    (hvelocity : ∀ i z, z ∈ W i →
      fderiv ℝ (H i) z (1, 0) = coordinateField B X e he i (H i z))
    (hpreserve : ∀ (i j : Fin k), j.val < i.val → ∀ z, z ∈ W i →
      fderiv ℝ (H i) z (0, coordinateField B X e he j z.2) =
        coordinateField B X e he j (H i z)) :
    SimultaneousCoordinates B X p hk := by
  obtain ⟨A, hA⟩ := linear_completion hk
    (fun i => coordinateField B X e he i (e p).val)
    (coordinateField_independent_at_base B X p e he hp hlin)
  obtain ⟨V, hV, h0, f, hf, hf0, hdf0, hcols⟩ :=
    finite_flow_parametrization hk (e p).val A (coordinateField B X e he) hA
      H W hW hW₀ hH hH₀ hstate₀ hvelocity hpreserve
  let V' : Set (Euclidean n) := V ∩ f ⁻¹' MaximalFlow.chartStateDomain e
  have hV' : IsOpen V' :=
    hf.continuousOn.isOpen_inter_preimage hV (MaximalFlow.chartStateDomain_isOpen e)
  have h0' : (0 : Euclidean n) ∈ V' := by
    refine ⟨h0, ?_⟩
    change MaximalFlow.euclideanModelPoint (f 0) ∈ e.target
    rw [hf0]
    exact e.map_source hp
  apply simultaneous_coordinates_of_parametrization S B X p hk e he hp
    V' hV' h0' f (hf.mono inter_subset_left) hf0 (fun _ hx => hx.2)
  · rw [hdf0]
    exact A.bijective
  · intro x hx i
    exact (hcols x hx.1 i).symm

/-- Pairwise local commutation and independence produce simultaneous coordinates. -/
theorem simultaneous_coordinates :
    Specs.SmoothManifolds.Ch06.CommutingFields.simultaneous_coordinatesType.{u} := by
  classical
  intro n k M _ S B b hb X p hk hlin hlocal
  obtain ⟨U, hU, hpU, hbr⟩ := hlocal
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨H, W, hW, hW0, hH, hH0, hstate0, hvelocity, hpreserve⟩ :=
    coordinate_flow_package S B b hb X p U hU hpU hbr e he hp
  exact simultaneous_coordinates_of_coordinate_evolutions S B X p hk hlin e he hp
    H W hW hW0 hH hH0 hstate0 hvelocity hpreserve

end SmoothManifolds.CommutingFields
