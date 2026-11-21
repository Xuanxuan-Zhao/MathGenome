import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.LeftInvariantCompleteness
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.LieBracket
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.MaximalFlow
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

noncomputable section
namespace SmoothManifolds.LeftInvariantCompleteness
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  VectorFieldData LieBracketData IntegralCurveData MaximalFlowData Set Filter
open scoped Topology ContDiff
universe u

/-- A smooth map carrying one field to another carries their integral curves. -/
theorem integralCurve_map {n m : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n .euclidean M} {T : SmoothManifold m .euclidean N}
    {B : TangentBundleStructure S} {C : TangentBundleStructure T}
    {X : SmoothField B} {Y : SmoothField C} (f : M → N)
    (hf : IsSmoothMap S T f)
    (hrel : ∀ p (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
      IsDifferential S T f p L → L (X.val p) = Y.val (f p))
    {I : Set ℝ} (hI : IsOpen I) {γ : ℝ → M}
    (hγ : IsIntegralCurveOn X I γ) : IsIntegralCurveOn Y I (f ∘ γ) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hf p).1)
  refine ⟨hfc.continuousOn.comp hγ.1 (mapsTo_univ _ _), ?_⟩
  intro t ht d hd hdt
  obtain ⟨e, he, het⟩ := S.smoothStructure.property.1.1 (γ t)
  obtain ⟨U, hU, hu, H, hH, hrep⟩ := (hf (γ t)).2 e he d hd het hdt
  have hct := hγ.1.continuousAt (hI.mem_nhds ht)
  have heq := hrep.comp_tendsto hct
  obtain ⟨hc, hv⟩ := hγ.2 t ht e he het
  have hHat := hH.contDiffAt (hU.mem_nhds hu)
  have hs := hHat.comp t hc
  have hdH := (hHat.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hv
  obtain ⟨L, hL, _⟩ := differential_exists S T f hf (γ t)
  have hvel := differential_jacobian S T f hf (γ t) L hL
    e d he hd het hdt (B.fiberCoordinates.equiv e he (γ t) het)
    (C.fiberCoordinates.equiv d hd (f (γ t)) hdt)
    (B.fiberCoordinates.isCoordinates e he (γ t) het)
    (C.fiberCoordinates.isCoordinates d hd (f (γ t)) hdt)
    U H hU hu hH hrep (X.val (γ t))
  rw [hrel (γ t) L hL] at hvel
  exact ⟨hs.congr_of_eventuallyEq heq.symm,
    hvel ▸ hdH.congr_of_eventuallyEq heq.symm⟩

section Group
variable {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
  {S : SmoothManifold n .euclidean G} {B : TangentBundleStructure S}
  {X : SmoothField B}

theorem integralCurve_left (A : LieGroupStructure S) (hX : IsLeftInvariant X) {I : Set ℝ} (hI : IsOpen I) {γ : ℝ → G}
    (hγ : IsIntegralCurveOn X I γ) (g : G) :
    IsIntegralCurveOn X I (fun t => g * γ t) :=
  integralCurve_map (fun p => g * p) (LieBrackets.left_translation_smooth A g)
    (hX g) hI hγ

/-- Every left translation preserves the full maximal lifespan, and transports
its curve values on that lifespan. -/
theorem maximalFamily_left (A : LieGroupStructure S) (hX : IsLeftInvariant X)
    (F : CurveFamily G) (hF : IsMaximalFamily X F)
    (g p : G) :
    (F.interval (g * p)).carrier = (F.interval p).carrier ∧
    EqOn (F.curve (g * p)) (fun t => g * F.curve p t) (F.interval p).carrier := by
  have htrans (a q : G) :=
    (hF (a * q)).2.2.2 (F.interval q) (fun t => a * F.curve q t)
      (hF q).1 (by rw [(hF q).2.1])
      (integralCurve_left A hX (F.interval q).isOpen (hF q).2.2.1 a)
  refine ⟨Subset.antisymm ?_ (htrans g p).1, (htrans g p).2⟩
  simpa only [inv_mul_cancel_left] using (htrans g⁻¹ (g * p)).1

/-- The common lifespan is an open additive subgroup of the connected line. -/
theorem complete : Specs.SmoothManifolds.Ch06.LeftInvariantCompleteness.completeType.{u} := by
  intro n G _ _ S B A X hX F hF g
  have hcommon (p : G) : (F.interval p).carrier = (F.interval 1).carrier := by
    simpa only [mul_one] using (maximalFamily_left A hX F hF p 1).1
  have hshift (s : ℝ) (hs : s ∈ (F.interval 1).carrier) :
      (F.interval 1).carrier = {t | s + t ∈ (F.interval 1).carrier} := by
    have h := (MaximalFlow.lifespan_flow_law S B X F hF 1 s hs).1
    rwa [hcommon (F.curve 1 s)] at h
  let H : OpenAddSubgroup ℝ :=
    { carrier := (F.interval 1).carrier
      zero_mem' := (hF 1).1
      add_mem' := by
        intro s t hs ht
        exact (show t ∈ {t | s + t ∈ (F.interval 1).carrier} from
          (hshift s hs) ▸ ht)
      neg_mem' := by
        intro s hs
        have hneg : -s ∈ {t | s + t ∈ (F.interval 1).carrier} := by
          simpa only [mem_ofPred_eq, add_neg_cancel] using (hF 1).1
        rwa [← hshift s hs] at hneg
      isOpen' := (F.interval 1).isOpen }
  have htop : (H : Set ℝ) = univ := H.isClopen.eq_univ ⟨0, H.zero_mem⟩
  exact (hcommon g).trans htop

/-- Completeness removes every time restriction from the maximal flow law. -/
theorem oneParameter : Specs.SmoothManifolds.Ch06.LeftInvariantCompleteness.oneParameterType.{u} := by
  intro n G _ _ S B A X hX F hF
  have hall (g : G) (t : ℝ) : t ∈ (F.interval g).carrier := by
    rw [complete S B A X hX F hF g]
    trivial
  have hleft (g : G) (t : ℝ) : F.curve g t = g * F.curve 1 t := by
    simpa only [mul_one] using (maximalFamily_left A hX F hF g 1).2 (hall 1 t)
  refine ⟨?_, ?_, (hF 1).2.1, ?_, hleft⟩
  · exact continuous_iff_continuousAt.mpr (fun t =>
      (hF 1).2.2.1.1.continuousAt ((F.interval 1).isOpen.mem_nhds (hall 1 t)))
  · intro t e he ht
    exact ((hF 1).2.2.1.2 t (hall 1 t) e he ht).1
  · intro s t
    exact ((MaximalFlow.lifespan_flow_law S B X F hF 1 s (hall 1 s)).2 t
      (hall 1 (s + t))).symm.trans (hleft (F.curve 1 s) t)

end Group

end SmoothManifolds.LeftInvariantCompleteness
