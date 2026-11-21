import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.Flowout
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.MaximalFlow
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.InjectiveShrinking
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flowbox

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SmoothManifolds.Flowout
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  VectorFieldData IntegralCurveData MaximalFlowData FlowoutData Set Filter
open scoped Topology ContDiff
universe u

/-- The actual parameter domain for a hypersurface flow; all zero times lie in it. -/
def parameterDomain {H M : Type u} (i : H → M) (F : CurveFamily M) : Set (ℝ × H) :=
  (fun z : ℝ × H => (z.1, i z.2)) ⁻¹' flowDomain F

def parameterMap {H M : Type u} (i : H → M) (F : CurveFamily M) : ℝ × H → M :=
  fun z => F.curve (i z.2) z.1

section Pullback
variable {k n : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
  (T : SmoothManifold k .euclidean H) (S : SmoothManifold n .euclidean M)
  (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M)
  (hF : IsMaximalFamily X F) (i : H → M)
include hF

theorem parameterDomain_isOpen (hi : IsSmoothMap T S i) :
    IsOpen (parameterDomain i F) := by
  have hc : Continuous i := continuous_iff_continuousAt.mpr (fun q => (hi q).1)
  exact (MaximalFlow.domain_open_smooth S B X F hF).1.preimage
    (continuous_fst.prodMk (hc.comp continuous_snd))

theorem zero_mem_parameterDomain (q : H) : (0,q) ∈ parameterDomain i F :=
  (hF (i q)).1

@[simp] theorem parameterMap_zero (q : H) : parameterMap i F (0,q) = i q :=
  (hF (i q)).2.1

/-- Joint smoothness survives restriction of the initial point to any smooth
map, with the full product-coordinate extension, rather than separate regularity. -/
theorem parameterMap_smoothAt (hi : IsSmoothMap T S i) (z : ℝ × H)
    (hz : z ∈ parameterDomain i F) : ProductSmoothAt T S (parameterMap i F) z := by
  have hs := (MaximalFlow.domain_open_smooth S B X F hF).2 (z.1, i z.2) hz
  have hι : ContinuousAt (fun w : ℝ × H => (w.1, i w.2)) z :=
    continuousAt_fst.prodMk ((hi z.2).1.comp continuousAt_snd)
  refine ⟨?_, ?_⟩
  · exact hs.1.comp (f := fun w : ℝ × H => (w.1, i w.2)) hι
  · intro e he d hd hze hzd
    obtain ⟨c, hc, hic⟩ := S.smoothStructure.property.1.1 (i z.2)
    obtain ⟨V, hV, hzV, I, hI, heI⟩ := (hi z.2).2 e he c hc hze hic
    obtain ⟨W, hW, hzW, G, hG, heG⟩ := hs.2 c hc d hd hic hzd
    let J : ℝ × Euclidean k → ℝ × Euclidean n := fun w => (w.1, I w.2)
    let U : Set (ℝ × Euclidean k) := Prod.snd ⁻¹' V ∩ J ⁻¹' W
    have hIo : ContDiffOn ℝ (⊤ : ℕ∞) J (Prod.snd ⁻¹' V) :=
      contDiffOn_fst.prodMk (hI.comp contDiffOn_snd (fun _ h => h))
    have hU : IsOpen U :=
      hIo.continuousOn.isOpen_inter_preimage (hV.preimage continuous_snd) hW
    have hIv : I (e z.2).val = (c (i z.2)).val := heI.eq_of_nhds
    refine ⟨U, hU, ⟨hzV, ?_⟩, (fun w => G (J w)), ?_, ?_⟩
    · change (z.1, I (e z.2).val) ∈ W
      rwa [hIv]
    · exact hG.comp (hIo.mono inter_subset_left) (fun _ h => h.2)
    · have heI' := heI.comp_tendsto continuousAt_snd
      have heG' := heG.comp_tendsto hι
      filter_upwards [heI', heG'] with w hwI hwG
      change G (w.1, I (e w.2).val) = (d (parameterMap i F w)).val
      change I (e w.2).val = (c (i w.2)).val at hwI
      rw [hwI]
      exact hwG

/-- The time derivative is exactly the original intrinsic field in every chart. -/
theorem parameterMap_hasDerivAt (z : ℝ × H) (hz : z ∈ parameterDomain i F)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hp : parameterMap i F z ∈ d.source) :
    HasDerivAt (fun t => (d (parameterMap i F (t,z.2))).val)
      (B.fiberCoordinates.equiv d hd (parameterMap i F z) hp
        (X.val (parameterMap i F z))) z.1 :=
  (hF (i z.2)).2.2.1.2 z.1 hz d hd hp |>.2

/-- Every open restriction of the true parameter map carries the time vector
to X; the hypersurface need not be closed and the time width need not be uniform. -/
theorem carriesTimeField_of_eqOn
    (h : OpenPartialHomeomorph (ℝ × H) M)
    (hdom : h.source ⊆ parameterDomain i F)
    (heq : EqOn h (parameterMap i F) h.source) : CarriesTimeField X h := by
  intro z hz d hd hp
  have hv : h z = parameterMap i F z := heq hz
  have hder := parameterMap_hasDerivAt S B X F hF i z (hdom hz) d hd (hv ▸ hp)
  have hevent : (fun t => (d (h (t,z.2))).val) =ᶠ[𝓝 z.1]
      (fun t => (d (parameterMap i F (t,z.2))).val) := by
    have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      (h.open_source.mem_nhds hz)
    filter_upwards [hn] with t ht
    exact congrArg (fun p => (d p).val) (heq (show (t,z.2) ∈ h.source from ht))
  have hv' : (⟨parameterMap i F z, hv ▸ hp⟩ : d.source) = ⟨h z, hp⟩ :=
    Subtype.ext hv.symm
  convert hder.congr_of_eventuallyEq hevent using 1
  exact congrArg (fun q : d.source =>
    B.fiberCoordinates.equiv d hd q.val q.property (X.val q.val)) hv'.symm

end Pullback

/-- An embedded locally compact space has locally closed image in a Hausdorff
space. This supplies the precise shrinking hypothesis without assuming that
the hypersurface is closed. -/
theorem embedding_range_isLocallyClosed {H M : Type u}
    [TopologicalSpace H] [TopologicalSpace M] [LocallyCompactSpace H] [T2Space M]
    {i : H → M} (hi : Topology.IsEmbedding i) : IsLocallyClosed (Set.range i) := by
  apply isLocallyClosed_iff_isLocallyClosedAt.mpr
  rintro _ ⟨q, rfl⟩
  obtain ⟨K, hKnhds, _, hK⟩ := local_compact_nhds (Filter.univ_mem : Set.univ ∈ 𝓝 q)
  obtain ⟨O, hO, hpre⟩ := hi.isInducing.isOpen_iff.mp (isOpen_interior (s := K))
  have hqO : i q ∈ O := by
    change q ∈ i ⁻¹' O
    rw [hpre]
    exact mem_interior_iff_mem_nhds.mpr hKnhds
  apply isLocallyClosedAt_iff_exists_isClosed_eventuallyEqSet.mpr
  refine ⟨i '' K, (hK.image hi.continuous).isClosed, ?_⟩
  filter_upwards [hO.mem_nhds hqO] with y hy
  apply propext
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, interior_subset ?_, rfl⟩
    change x ∈ interior K
    rw [← hpre]
    exact hy
  · rintro ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩

/-- A smooth forward map and a C¹ inverse have a smooth inverse. This lets us
use the fixed C¹ flow-box construction with the same chart at every order. -/
theorem inverse_smooth_of_c1 {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : OpenPartialHomeomorph E G)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) b b.source)
    (hg : ContDiffOn ℝ 1 b.symm b.target) :
    ContDiffOn ℝ (⊤ : ℕ∞) b.symm b.target := by
  intro y hy
  have hx := b.map_target hy
  have hd := (hf.contDiffAt (b.open_source.mem_nhds hx)).differentiableAt (by simp)
  have he := (hg.contDiffAt (b.open_target.mem_nhds hy)).differentiableAt_one
  let L := fderiv ℝ b (b.symm y)
  let K := fderiv ℝ b.symm y
  have hK : HasFDerivAt b.symm K (b (b.symm y)) := by
    simpa only [b.right_inv hy] using he.hasFDerivAt
  have hleft : Function.LeftInverse K L := by
    have hdId := (hK.comp (b.symm y) hd.hasFDerivAt).congr_of_eventuallyEq
      (show id =ᶠ[𝓝 (b.symm y)] (b.symm ∘ b) from by
        filter_upwards [b.open_source.mem_nhds hx] with x hx
        exact (b.left_inv hx).symm)
    have hL := hdId.unique (hasFDerivAt_id (b.symm y) (𝕜 := ℝ))
    intro v
    exact congrArg (fun D : E →L[ℝ] E => D v) hL
  have hright : Function.RightInverse K L := by
    have hd' : HasFDerivAt b L (b.symm y) := hd.hasFDerivAt
    have hdId := (hd'.comp y he.hasFDerivAt).congr_of_eventuallyEq
      (show id =ᶠ[𝓝 y] (b ∘ b.symm) from by
        filter_upwards [b.open_target.mem_nhds hy] with z hz
        exact (b.right_inv hz).symm)
    have hL := hdId.unique (hasFDerivAt_id y (𝕜 := ℝ))
    intro v
    exact congrArg (fun D : G →L[ℝ] G => D v) hL
  let A : E ≃L[ℝ] G := ContinuousLinearEquiv.equivOfInverse L K hleft hright
  exact (b.contDiffAt_symm (f₀' := A) hy hd.hasFDerivAt
    (hf.contDiffAt (b.open_source.mem_nhds hx))).contDiffWithinAt

/-- The fixed D13 C¹ flow chart is C-infinity in both directions for a smooth
chart ODE. In particular we do not choose different coordinate charts as the
requested differentiability order increases. -/
theorem smooth_euclidean_flowbox {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (O : D13Unified.AutonomousODE E)
    (hO : ContDiffOn ℝ (⊤ : ℕ∞) O.eval O.domain)
    (hflow : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × E => D13Unified.Ch06.StateDerivative.flow O z.1 z.2)
      (D13Unified.Ch06.StateDerivative.flowDomain O))
    (p : E) (hp : p ∈ O.domain) (hv : O.eval p ≠ 0) :
    ∃ c : Specs.D13Unified.Ch11.Flowbox.Chart O p 1,
      ContDiffOn ℝ (⊤ : ℕ∞) c.coord c.coord.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c.coord.symm c.coord.target := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨c⟩ := D13Unified.Ch11.Flowbox.flowbox 1 le_rfl O (hO.of_le (by simp)) p hp hv
  let j : ℝ × (Fin (Module.finrank ℝ E - 1) → ℝ) → ℝ × E :=
    fun z => (z.1, p + c.frame (0,z.2))
  have hj : ContDiff ℝ (⊤ : ℕ∞) j :=
    contDiff_fst.prodMk (contDiff_const.add
      (c.frame.contDiff.comp (contDiff_const.prodMk contDiff_snd)))
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) c.coord c.coord.source :=
    (hflow.comp hj.contDiffOn c.flow_domain).congr (fun z hz => c.formula z hz)
  exact ⟨c, hf, inverse_smooth_of_c1 c.coord hf c.inverse_regular⟩

@[simp] theorem ambient_euclidean_source {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) : (InteriorInverse.ambientChart e).source = e.source := by
  simp [InteriorInverse.ambientChart_source, ModelData.modelSet]

@[simp] theorem ambient_euclidean_target {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) :
    (InteriorInverse.ambientChart e).target = MaximalFlow.chartStateDomain e := by
  ext x
  simp [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.coe_trans_symm, InteriorInverse.ambientChart, InteriorInverse.modelInteriorChart,
    ModelData.modelSet, MaximalFlow.chartStateDomain, MaximalFlow.euclideanModelPoint]

@[simp] theorem ambient_euclidean_symm {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (x : Euclidean n) :
    (InteriorInverse.ambientChart e).symm x = e.symm (MaximalFlow.euclideanModelPoint x) := by
  simp [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.coe_trans_symm, InteriorInverse.ambientChart, InteriorInverse.modelInteriorChart,
    ModelData.modelSet, MaximalFlow.euclideanModelPoint]

/-- Smooth transitions in genuine Euclidean charts are smooth on their actual
open domains, with the same ambient-extension convention as the maximal atlas. -/
theorem ambient_transition_contDiff {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M)
    (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val) :
    let j := (InteriorInverse.ambientChart e).symm.trans (InteriorInverse.ambientChart d)
    ContDiffOn ℝ (⊤ : ℕ∞) j j.source := by
  dsimp only
  let E := InteriorInverse.ambientChart e
  let D := InteriorInverse.ambientChart d
  intro y hy
  have hye : MaximalFlow.euclideanModelPoint y ∈ e.target := by simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target, ambient_euclidean_target, MaximalFlow.chartStateDomain, Set.mem_preimage] using hy.1
  have hpd : e.symm (MaximalFlow.euclideanModelPoint y) ∈ d.source := by simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target, ambient_euclidean_symm] using hy.2.1
  have hmod : MaximalFlow.euclideanModelPoint y ∈ (e.symm.trans d).source :=
    ⟨hye, hpd⟩
  obtain ⟨U, hU, hyU, G, hG, heG⟩ := (S.smoothStructure.property.1.2 e he d hd).1
    (MaximalFlow.euclideanModelPoint y) hmod
  have hevent : G =ᶠ[𝓝 y] (E.symm.trans D) := by
    filter_upwards [(E.symm.trans D).open_source.mem_nhds hy, hU.mem_nhds hyU] with z hz hzU
    have hz1 : MaximalFlow.euclideanModelPoint z ∈ e.target := by
      simpa only [E, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target, ambient_euclidean_target, MaximalFlow.chartStateDomain, Set.mem_preimage] using hz.1
    have hz2 : e.symm (MaximalFlow.euclideanModelPoint z) ∈ d.source := by
      simpa only [E, D, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target, ambient_euclidean_symm] using hz.2.1
    simpa only [E, D, OpenPartialHomeomorph.trans_apply, InteriorInverse.ambientChart_apply,
      ambient_euclidean_symm, MaximalFlow.euclideanModelPoint] using heG (MaximalFlow.euclideanModelPoint z) ⟨hz1, hz2⟩ hzU
  exact ((hG.contDiffAt (hU.mem_nhds hyU)).congr_of_eventuallyEq hevent.symm).contDiffWithinAt

/-- Composition of smooth partial coordinate maps retains smoothness on exactly
the open source where both component coordinate maps are defined. -/
theorem partial_comp_contDiff {E G K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (b : OpenPartialHomeomorph E G) (c : OpenPartialHomeomorph G K)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b b.source)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c c.source) :
    ContDiffOn ℝ (⊤ : ℕ∞) (b.trans c) (b.trans c).source :=
  hc.comp (hb.mono inter_subset_left) (fun _ h => h.2)

/-- Flow coordinates at every nonzero point. The same chart is smooth in both
 directions, and the maximal flow translates its first coordinate. -/
theorem flow_box : Specs.SmoothManifolds.Ch06.Flowout.flow_boxType.{u} := by
  intro n M _ S B X F hF p hXp
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let A := InteriorInverse.ambientChart e
  have hpA : p ∈ A.source := by simpa only [A, ambient_euclidean_source] using hp
  have hdim : Module.finrank ℝ (Euclidean n) = n := by simp [ModelData.Euclidean]
  have hn : 0 < n := by
    by_contra h
    have hn : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    apply hXp
    apply (B.fiberCoordinates.equiv e he p hp).injective
    exact Subsingleton.elim _ _
  refine ⟨hn, ?_⟩
  suffices hh : ∃ h : OpenPartialHomeomorph M
      (ℝ × (Fin (Module.finrank ℝ (Euclidean n)-1) → ℝ)), IsFlowBox S F p h by
    change ∃ h : OpenPartialHomeomorph M
      (ℝ × Euclidean (Module.finrank ℝ (Euclidean n)-1)), IsFlowBox S F p h at hh
    rwa [hdim] at hh
  let O := MaximalFlow.chartODE B X e he
  have hO := MaximalFlow.chartODE_contDiffOn B X e he
  have hflow := MaximalFlow.chartODE_flow_regular B X e he
  have hep : (e p).val ∈ O.domain := e.map_source hp
  have hOv : O.eval (e p).val ≠ 0 := by
    rw [MaximalFlow.chartODE_eval B X e he hep, MaximalFlow.chartCoefficient_apply B X e he hp]
    exact fun h => hXp ((B.fiberCoordinates.equiv e he p hp).injective (by simpa using h))
  obtain ⟨c, hc, hci⟩ := smooth_euclidean_flowbox O hO hflow.2 (e p).val hep hOv
  let h := A.trans c.coord.symm
  have hc0 : (0,0) ∈ c.coord.source := by
    rw [c.source_eq]
    exact ⟨⟨neg_neg_of_pos c.ε_pos, c.ε_pos⟩, c.transverse_zero⟩
  have hpH : p ∈ h.source := ⟨hpA, c.target_point⟩
  have horigin : h p = (0,0) := by
    change c.coord.symm (e p).val = (0,0)
    exact (congrArg c.coord.symm c.origin).symm.trans (c.coord.left_inv hc0)
  refine ⟨h, hpH, horigin, ?_, ?_, ?_⟩
  · intro q hq
    refine ⟨h.continuousAt hq, ?_⟩
    change q ∈ A.source ∧ A q ∈ c.coord.target at hq
    intro d hd hqd
    let D := InteriorInverse.ambientChart d
    let j := D.symm.trans A
    let l := j.trans c.coord.symm
    have hj := ambient_transition_contDiff S d e hd he
    have hl := partial_comp_contDiff j c.coord.symm hj hci
    have hqD : q ∈ D.source := by simpa only [D, ambient_euclidean_source] using hqd
    have hql : D q ∈ l.source := by
      refine ⟨⟨D.map_source hqD, ?_⟩, ?_⟩
      · change D.symm (D q) ∈ A.source
        simpa only [D.left_inv hqD] using hq.1
      · change A (D.symm (D q)) ∈ c.coord.target
        simpa only [D.left_inv hqD] using hq.2
    refine ⟨l.source, l.open_source, hql, l, hl, ?_⟩
    filter_upwards [D.open_source.mem_nhds hqD] with y hy
    change c.coord.symm (A (D.symm (D y))) = c.coord.symm (A y)
    rw [D.left_inv hy]
  · intro z hz
    refine ⟨h.symm.continuousAt hz, ?_⟩
    change z ∈ c.coord.source ∧ c.coord z ∈ A.target at hz
    intro d hd hzd
    let D := InteriorInverse.ambientChart d
    let j := A.symm.trans D
    let l := c.coord.trans j
    have hj := ambient_transition_contDiff S e d he hd
    have hl := partial_comp_contDiff c.coord j hc hj
    have hzl : z ∈ l.source := by
      refine ⟨hz.1, hz.2, ?_⟩
      change A.symm (c.coord z) ∈ D.source
      change A.symm (c.coord z) ∈ d.source at hzd
      simpa only [D, ambient_euclidean_source] using hzd
    refine ⟨l.source, l.open_source, hzl, l, hl, ?_⟩
    exact Eventually.of_forall (fun _ => rfl)
  · intro q hq
    change q ∈ A.source ∧ A q ∈ c.coord.target at hq
    let z := h q
    have hz : z ∈ c.coord.source := (h.map_source hq).1
    have hqe : q ∈ e.source := by
      simpa only [A, ambient_euclidean_source] using hq.1
    have hAz : c.coord z = A q := c.coord.right_inv hq.2
    have hevent : (fun t => h (F.curve q t)) =ᶠ[𝓝 (0 : ℝ)]
        (fun t => (z.1+t,z.2)) := by
      have hshift : ContinuousAt (fun t : ℝ => (z.1+t,z.2)) 0 :=
        (continuousAt_const.add continuousAt_id).prodMk continuousAt_const
      have hnear := hshift.preimage_mem_nhds
        (c.coord.open_source.mem_nhds (by simpa using hz))
      filter_upwards [hnear] with t ht
      obtain ⟨hdom, htrans⟩ := c.translation z hz t ht
      have hdom' : (t,(e q).val) ∈ D13Unified.Ch06.StateDerivative.flowDomain O := by
        simpa only [hAz, A, InteriorInverse.ambientChart_apply] using hdom
      have hagree := MaximalFlow.chartFlow_agrees F hF e he (t,q) hqe hdom'
      have hvalue : F.curve q t = A.symm (c.coord (z.1+t,z.2)) := by
        rw [show A.symm (c.coord (z.1+t,z.2)) =
          e.symm (MaximalFlow.euclideanModelPoint (c.coord (z.1+t,z.2))) by
            exact ambient_euclidean_symm e _]
        have hagree' : F.curve q t = e.symm (MaximalFlow.euclideanModelPoint
          (D13Unified.Ch06.StateDerivative.flow O t (e q).val)) := hagree.2
        rw [hagree']
        have heq : D13Unified.Ch06.StateDerivative.flow O t (e q).val = c.coord (z.1+t,z.2) := by
          simpa only [hAz, A, InteriorInverse.ambientChart_apply] using htrans
        rw [heq]
      have htarget : c.coord (z.1+t,z.2) ∈ A.target := by
        simpa only [A, ambient_euclidean_target, O, MaximalFlow.chartODE] using
          c.target_domain (c.coord.map_source ht)
      change c.coord.symm (A (F.curve q t)) = (z.1+t,z.2)
      rw [hvalue, A.right_inv htarget, c.coord.left_inv ht]
    have hder : HasDerivAt (fun t : ℝ => (z.1+t,z.2)) (1,0) 0 := by
      simpa using ((hasDerivAt_const (0 : ℝ) z.1).add (hasDerivAt_id (0 : ℝ))).prodMk
        (hasDerivAt_const (0 : ℝ) z.2)
    exact hder.congr_of_eventuallyEq hevent

/-- Shrinking may be done inside an open domain where a total representative is
continuous. No assertion about the representative outside that domain is needed. -/
theorem injective_shrinking_within_open {U M : Type u}
    [TopologicalSpace U] [TopologicalSpace M]
    {n : ℕ} {a : ModelKind} (A : TopologicalManifold n a M)
    (f : U → M) (D Z : Set U) (hD : IsOpen D) (hZD : Z ⊆ D)
    (hf : ContinuousOn f D) (hE : Topology.IsEmbedding (fun z : Z => f z))
    (hC : IsLocallyClosed (f '' Z))
    (hlocal : ∀ z ∈ Z, ∃ W : Set U, IsOpen W ∧ z ∈ W ∧ InjOn f W) :
    ∃ V : Set U, IsOpen V ∧ Z ⊆ V ∧ V ⊆ D ∧ InjOn f V := by
  let Z' : Set D := Subtype.val ⁻¹' Z
  let f' : D → M := fun x => f x.val
  have hf' : Continuous f' := hf.domRestrict
  have hj : Topology.IsEmbedding (fun z : Z' => (⟨z.val.val, z.property⟩ : Z)) := by
    have hval : Topology.IsEmbedding (fun z : Z' => (z.val.val : U)) :=
      (show Topology.IsEmbedding (Subtype.val : D → U) from .subtypeVal).comp
        (show Topology.IsEmbedding (Subtype.val : Z' → D) from .subtypeVal)
    exact (show Topology.IsEmbedding (Subtype.val : Z → U) from .subtypeVal).of_comp_iff.mp hval
  have he : Topology.IsEmbedding (fun z : Z' => f' z) := hE.comp hj
  have him : f' '' Z' = f '' Z := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hZD hx⟩, hx, rfl⟩
  have hl : ∀ z ∈ Z', ∃ W : Set D, IsOpen W ∧ z ∈ W ∧ InjOn f' W := by
    intro z hz
    obtain ⟨W, hW, hzW, hi⟩ := hlocal z.val hz
    refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hzW, ?_⟩
    intro x hx y hy hxy
    exact Subtype.ext (hi hx hy hxy)
  obtain ⟨V, hV, hZV, hi⟩ := injective_shrinking A f' Z' hf' he (him ▸ hC) hl
  refine ⟨Subtype.val '' V, hD.isOpenMap_subtype_val V hV, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨⟨z, hZD hz⟩, hZV hz, rfl⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.property
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    exact congrArg Subtype.val (hi hx hy hxy)

/-- The zero-time section has exactly the original hypersurface topology. -/
def zeroTimeHomeomorph (H : Type u) [TopologicalSpace H] :
    H ≃ₜ {z : ℝ × H | z.1 = 0} where
  toFun q := ⟨(0,q), rfl⟩
  invFun z := z.val.2
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext z.property.symm rfl
  continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _
  continuous_invFun := continuous_snd.comp continuous_subtype_val

/-- Once local injectivity on the zero section is established, the *whole*
section has an injective open flow neighborhood. Closedness of its image is
proved locally from the embedding and local compactness, not assumed. -/
theorem parameterMap_injective_neighborhood
    {k n : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold n .euclidean M)
    (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M)
    (hF : IsMaximalFamily X F) (i : H → M) (hi : IsSmoothMap T S i)
    (hE : Topology.IsEmbedding i)
    (hlocal : ∀ q : H, ∃ W : Set (ℝ × H), IsOpen W ∧ (0,q) ∈ W ∧
      InjOn (parameterMap i F) W) :
    ∃ V : Set (ℝ × H), IsOpen V ∧ (∀ q, (0,q) ∈ V) ∧
      V ⊆ parameterDomain i F ∧ InjOn (parameterMap i F) V := by
  letI : LocallyCompactSpace H := _root_.SmoothManifolds.TopologicalManifold.locallyCompactSpace T.topologicalManifold
  letI : T2Space M := S.topologicalManifold.hausdorff
  let Z : Set (ℝ × H) := {z | z.1 = 0}
  have hz : ∀ z : Z, parameterMap i F z.val = i z.val.2 := by
    intro z
    change F.curve (i z.val.2) z.val.1 = i z.val.2
    rw [z.property]
    exact (hF (i z.val.2)).2.1
  have he : Topology.IsEmbedding (fun z : Z => parameterMap i F z.val) := by
    have hh := hE.comp (zeroTimeHomeomorph H).symm.isEmbedding
    convert hh using 1
    exact funext hz
  have him : parameterMap i F '' Z = Set.range i := by
    ext y
    constructor
    · rintro ⟨z, hzZ, rfl⟩
      exact ⟨z.2, (hz ⟨z, hzZ⟩).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(0,q), rfl, parameterMap_zero S B X F hF i q⟩
  have hcont : ContinuousOn (parameterMap i F) (parameterDomain i F) :=
    fun z hz => (parameterMap_smoothAt T S B X F hF i hi z hz).1.continuousWithinAt
  have hloc : ∀ z ∈ Z, ∃ W : Set (ℝ × H), IsOpen W ∧ z ∈ W ∧
      InjOn (parameterMap i F) W := by
    rintro ⟨t,q⟩ hz
    change t = 0 at hz
    subst t
    exact hlocal q
  have hZD : Z ⊆ parameterDomain i F := by
    rintro ⟨t,q⟩ hz
    change t = 0 at hz
    subst t
    exact zero_mem_parameterDomain S B X F hF i q
  obtain ⟨V, hV, hZV, hVD, hVi⟩ := injective_shrinking_within_open
    S.topologicalManifold (parameterMap i F) (parameterDomain i F) Z
    (parameterDomain_isOpen T S B X F hF i hi) hZD hcont he
    (him ▸ embedding_range_isLocallyClosed hE) hloc
  exact ⟨V, hV, (fun q => hZV rfl), hVD, hVi⟩

/-- The linear algebra of a transverse hypersurface: adding a non-tangent
velocity to an injective codimension-one map gives an isomorphism. -/
theorem transverse_linear_bijective {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (L : V →ₗ[ℝ] W) (hL : Function.Injective L) (x : W)
    (hx : x ∉ LinearMap.range L)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 1) :
    Function.Bijective
      ((((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight x).coprod L) : ℝ × V → W) := by
  let J := ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight x).coprod L
  have hzero : ∀ z : ℝ × V, J z = 0 → z = 0 := by
    rintro ⟨a,v⟩ hz
    change a • x + L v = 0 at hz
    have ha : a = 0 := by
      by_contra ha
      have hax : a • x = L (-v) := by
        rw [map_neg]
        exact eq_neg_of_add_eq_zero_left hz
      apply hx
      refine ⟨a⁻¹ • (-v), ?_⟩
      rw [map_smul, ← hax, smul_smul, inv_mul_cancel₀ ha, one_smul]
    have hv : v = 0 := by
      apply hL
      simpa [ha] using hz
    simp [ha, hv]
  have hj : Function.Injective J := by
    intro z w hzw
    have := hzero (z-w) (by simp [map_sub, hzw])
    exact sub_eq_zero.mp this
  refine ⟨hj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := J) ?_).mp hj
  simp only [Module.finrank_prod, Module.finrank_self]
  omega

/-- The actual joint derivative at zero time is (a,v) ↦ aX + di(v).
This is proved for every local smooth coordinate representative of the parameter
map; it is not an extra assumption on the flow or on the hypersurface. -/
theorem parameterMap_derivative_zero
    {k n : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold n .euclidean M)
    (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M)
    (hF : IsMaximalFamily X F) (i : H → M) (hi : IsSmoothMap T S i)
    (q : H) (L : TangentSpace T q →ₗ[ℝ] TangentSpace S (i q))
    (hL : IsDifferential T S i q L)
    (e : ModelChart k .euclidean H) (d : ModelChart n .euclidean M)
    (he : e ∈ T.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (hqe : q ∈ e.source) (hqd : i q ∈ d.source)
    (E : TangentSpace T q ≃ₗ[ℝ] Euclidean k) (hE : IsChartCoordinates T q e E)
    (U : Set (ℝ × Euclidean k)) (G : ℝ × Euclidean k → Euclidean n)
    (hU : IsOpen U) (hyU : (0,(e q).val) ∈ U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (heG : (fun z : ℝ × H => G (z.1,(e z.2).val)) =ᶠ[𝓝 (0,q)]
      (fun z => (d (parameterMap i F z)).val)) :
    ∀ z : ℝ × Euclidean k,
      fderiv ℝ G (0,(e q).val) z =
        z.1 • B.fiberCoordinates.equiv d hd (i q) hqd (X.val (i q)) +
          B.fiberCoordinates.equiv d hd (i q) hqd (L (E.symm z.2)) := by
  let D := fderiv ℝ G (0,(e q).val)
  have hdG : HasFDerivAt G D (0,(e q).val) :=
    ((hG.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).hasFDerivAt
  have ht0 := heG.comp_tendsto
    (continuousAt_id.prodMk continuousAt_const :
      ContinuousAt (fun t : ℝ => (t,q)) 0)
  have htcurve := parameterMap_hasDerivAt S B X F hF i (0,q)
    (zero_mem_parameterDomain S B X F hF i q) d hd
    (by simpa only [parameterMap_zero S B X F hF i q] using hqd)
  have ht : HasDerivAt (fun t => G (t,(e q).val))
      (B.fiberCoordinates.equiv d hd (i q) hqd (X.val (i q))) 0 := by
    have ht' := htcurve.congr_of_eventuallyEq ht0
    apply ht'.congr_deriv
    exact congrArg (fun r : d.source =>
      B.fiberCoordinates.equiv d hd r.val r.property (X.val r.val))
      (show (⟨parameterMap i F (0,q), (parameterMap_zero S B X F hF i q).symm ▸ hqd⟩ : d.source) = ⟨i q, hqd⟩ from
        Subtype.ext (parameterMap_zero S B X F hF i q))
  have htD := hdG.comp (0 : ℝ)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) (e q).val)
  have htime (a : ℝ) : D (a,0) =
      a • B.fiberCoordinates.equiv d hd (i q) hqd (X.val (i q)) := by
    exact congrArg (fun J : ℝ →L[ℝ] Euclidean n => J a) (htD.unique ht.hasFDerivAt)
  let C : Euclidean k → Euclidean n := fun v => G (0,v)
  let V : Set (Euclidean k) := (fun v : Euclidean k => ((0 : ℝ),v)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hC : ContDiffOn ℝ (⊤ : ℕ∞) C V :=
    hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  have heC : (fun r => C (e r).val) =ᶠ[𝓝 q] (fun r => (d (i r)).val) := by
    have heC' := heG.comp_tendsto
      (continuousAt_const.prodMk continuousAt_id :
        ContinuousAt (fun r : H => ((0 : ℝ),r)) q)
    filter_upwards [heC'] with r hr
    change G (0,(e r).val) = (d (parameterMap i F (0,r))).val at hr
    exact hr.trans (congrArg (fun x => (d x).val) (parameterMap_zero S B X F hF i r))
  have hspace' := differential_jacobian T S i hi q L hL e d he hd hqe hqd E
    (B.fiberCoordinates.equiv d hd (i q) hqd) hE
    (B.fiberCoordinates.isCoordinates d hd (i q) hqd) V C hV hyU hC heC
  have hCd := hdG.comp (e q).val
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : ℝ) (e q).val)
  change HasFDerivAt C (D.comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean k))) (e q).val at hCd
  have hspace (v : Euclidean k) : D (0,v) =
      B.fiberCoordinates.equiv d hd (i q) hqd (L (E.symm v)) := by
    have h := hspace' (E.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [hCd.fderiv] at h
    exact h.symm
  intro z
  change D z = _
  calc
    D z = D (z.1,0) + D (0,z.2) := by
      rw [← map_add]
      congr 1 <;> ext <;> simp
    _ = _ := by rw [htime, hspace]

/-- Transversality makes every smooth coordinate representative of the actual
flowout map invertible at zero time. All tangent comparisons are through the
canonical intrinsic differential, including injectivity from the embedding. -/
theorem parameterMap_derivative_bijective
    {k : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M)
    (hF : IsMaximalFamily X F) (i : H → M)
    (hi : MapClassData.IsSmoothEmbedding T S i) (htrans : IsTransverse T S X i)
    (q : H) (e : ModelChart k .euclidean H) (d : ModelChart (k+1) .euclidean M)
    (he : e ∈ T.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (hqe : q ∈ e.source) (hqd : i q ∈ d.source)
    (U : Set (ℝ × Euclidean k)) (G : ℝ × Euclidean k → Euclidean (k+1))
    (hU : IsOpen U) (hyU : (0,(e q).val) ∈ U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (heG : (fun z : ℝ × H => G (z.1,(e z.2).val)) =ᶠ[𝓝 (0,q)]
      (fun z => (d (parameterMap i F z)).val)) :
    Function.Bijective (fderiv ℝ G (0,(e q).val)) := by
  obtain ⟨L, hL, hXL⟩ := htrans q
  obtain ⟨E, hE⟩ := FiniteRegularity.exists_smooth_chart_coordinates T q e he hqe
  let D := B.fiberCoordinates.equiv d hd (i q) hqd
  let J : Euclidean k →ₗ[ℝ] Euclidean (k+1) :=
    D.toLinearMap.comp (L.comp E.symm.toLinearMap)
  have hLin : Function.Injective L :=
    (MapClasses.smooth_tangent_invariants T S i hi.1 q L hL).2.1.mp (hi.2.2.1 q)
  have hJ : Function.Injective J := D.injective.comp (hLin.comp E.symm.injective)
  have hXJ : D (X.val (i q)) ∉ LinearMap.range J := by
    rintro ⟨v, hv⟩
    exact hXL ⟨E.symm v, D.injective hv⟩
  have hbij := transverse_linear_bijective J hJ (D (X.val (i q))) hXJ (by simp)
  have hform := parameterMap_derivative_zero T S B X F hF i hi.1 q L hL
    e d he hd hqe hqd E hE U G hU hyU hG heG
  have heq : (fderiv ℝ G (0,(e q).val) : ℝ × Euclidean k → Euclidean (k+1)) =
      (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (D (X.val (i q)))).coprod J) := by
    funext z
    exact hform z
  rw [heq]
  exact hbij

/-- A smooth coordinate representative with invertible derivative has an open
local inverse smooth on its entire target. The product source is a genuine
finite-dimensional space, rather than an assumed manifold inverse theorem. -/
theorem smooth_local_inverse {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (x : E) (hx : x ∈ U) (hbij : Function.Bijective (fderiv ℝ f x)) :
    ∃ j : OpenPartialHomeomorph E G, x ∈ j.source ∧ j.source ⊆ U ∧
      (j : E → G) = f ∧ ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target := by
  let A := (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hbij).toContinuousLinearEquiv
  have hA : (A : E →L[ℝ] G) = fderiv ℝ f x := by ext; rfl
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  have hdf : HasFDerivAt f (A : E →L[ℝ] G) x := by
    rw [hA]
    exact (hfx.differentiableAt (by simp)).hasFDerivAt
  let j₀ := hfx.toOpenPartialHomeomorph f hdf (by simp)
  let W := U ∩ (fderiv ℝ f) ⁻¹' Set.range (fun e : E ≃L[ℝ] G => (e : E →L[ℝ] G))
  have hW : IsOpen W :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage
      hU ContinuousLinearEquiv.isOpen
  have hxW : x ∈ W := ⟨hx, A, hA⟩
  let j := j₀.restrOpen W hW
  refine ⟨j, ⟨hfx.mem_toOpenPartialHomeomorph_source hdf (by simp), hxW⟩,
    (fun _ h => h.2.1), rfl, ?_⟩
  intro y hy
  have hsy := j.map_target hy
  obtain ⟨D, hD⟩ := hsy.2.2
  have hd : HasFDerivAt f (D : E →L[ℝ] G) (j.symm y) := by
    change (D : E →L[ℝ] G) = _ at hD
    rw [hD]
    exact ((hf.contDiffAt (hU.mem_nhds hsy.2.1)).differentiableAt (by simp)).hasFDerivAt
  exact (j.contDiffAt_symm hy hd (hf.contDiffAt (hU.mem_nhds hsy.2.1))).contDiffWithinAt

/-- Passing from a total partial-homeomorphism representative to the actual open
subspaces preserves every flowout assertion and both smooth coordinate tests. -/
theorem flowoutOn_of_partial
    {k : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M)
    (hF : IsMaximalFamily X F) (i : H → M)
    (h : OpenPartialHomeomorph (ℝ × H) M) (hh : IsFlowout T S X i F h) :
    IsFlowoutOn T S X i F h.source h.target h.toHomeomorphSourceTarget := by
  obtain ⟨hzero, hdom, heq, _, him, hf, hg, _⟩ := hh
  refine ⟨hzero, hdom, (fun z => heq z.property), him, ?_, ?_, ?_⟩
  · intro z e he d hd hze hzd
    obtain ⟨U, hU, hzU, G, hG, hEq⟩ := (hf z.val z.property).2 e he d hd hze hzd
    exact ⟨U, hU, hzU, G, hG, hEq.comp_tendsto continuousAt_subtype_val⟩
  · intro p d hd e he hpd hpe
    obtain ⟨U, hU, hpU, G, hG, hEq⟩ := (hg p.val p.property).2 d hd e he hpd hpe
    exact ⟨U, hU, hpU, G, hG, hEq.comp_tendsto continuousAt_subtype_val⟩
  · intro z hz d hd hp
    exact parameterMap_hasDerivAt S B X F hF i z (hdom hz) d hd hp

/-- The empty hypersurface has the empty flowout, even in a nonempty manifold.
Smoothness and the time-vector equation have no points to test in this case. -/
theorem empty_hypersurface_flowout
    {k : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M] [IsEmpty H]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M) (i : H → M) :
    ∃ (V : Set (ℝ × H)) (W : Set M), IsOpen V ∧ IsOpen W ∧
      ∃ h : V ≃ₜ W, IsFlowoutOn T S X i F V W h := by
  let V : Set (ℝ × H) := ∅
  let W : Set M := ∅
  let h : V ≃ₜ W := Homeomorph.empty
  refine ⟨V, W, isOpen_empty, isOpen_empty, h, ?_⟩
  refine ⟨(fun q => isEmptyElim q), empty_subset _, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact z.property.elim
  · rintro _ ⟨q, rfl⟩
    exact isEmptyElim q
  · intro z
    exact z.property.elim
  · intro p
    exact p.property.elim
  · intro z hz
    exact hz.elim

/-- The inverse function theorem gives local injectivity at each zero-time
point under exactly the embedding and transversality hypotheses. -/
theorem parameterMap_locally_injective
    {k : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M)
    (hF : IsMaximalFamily X F) (i : H → M)
    (hi : MapClassData.IsSmoothEmbedding T S i) (htrans : IsTransverse T S X i)
    (q : H) :
    ∃ W : Set (ℝ × H), IsOpen W ∧ (0,q) ∈ W ∧ InjOn (parameterMap i F) W := by
  obtain ⟨e, he, hqe⟩ := T.smoothStructure.property.1.1 q
  obtain ⟨d, hd, hqd⟩ := S.smoothStructure.property.1.1 (i q)
  have hs := parameterMap_smoothAt T S B X F hF i hi.1 (0,q)
    (zero_mem_parameterDomain S B X F hF i q)
  obtain ⟨U, hU, hyU, G, hG, heG⟩ := hs.2 e he d hd hqe
    ((parameterMap_zero S B X F hF i q).symm ▸ hqd)
  have hbij := parameterMap_derivative_bijective T S B X F hF i hi htrans q
    e d he hd hqe hqd U G hU hyU hG heG
  obtain ⟨j, hyj, _, hj, _⟩ := smooth_local_inverse G U hU hG (0,(e q).val) hyU hbij
  let c : ℝ × H → ℝ × Euclidean k := fun z => (z.1,(e z.2).val)
  have hc : ContinuousAt c (0,q) := continuousAt_fst.prodMk
    (continuous_subtype_val.continuousAt.comp ((e.continuousAt hqe).comp continuousAt_snd))
  have hnear : {z : ℝ × H | z.2 ∈ e.source ∧ c z ∈ j.source ∧
      G (c z) = (d (parameterMap i F z)).val} ∈ 𝓝 (0,q) := by
    exact inter_mem ((e.open_source.preimage continuous_snd).mem_nhds hqe)
      (inter_mem (hc.preimage_mem_nhds (j.open_source.mem_nhds hyj)) heG)
  obtain ⟨W, hWsub, hW, hqW⟩ := mem_nhds_iff.mp hnear
  refine ⟨W, hW, hqW, ?_⟩
  intro x hx y hy hxy
  have hx' := hWsub hx
  have hy' := hWsub hy
  have hcoord : c x = c y := by
    apply j.injOn hx'.2.1 hy'.2.1
    rw [hj]
    exact hx'.2.2.trans ((congrArg (fun p => (d p).val) hxy).trans hy'.2.2.symm)
  have htime : x.1 = y.1 := congrArg (fun z : ℝ × Euclidean k => z.1) hcoord
  have hspace : x.2 = y.2 := e.injOn hx'.1 hy'.1
    (Subtype.ext (congrArg (fun z : ℝ × Euclidean k => z.2) hcoord))
  exact Prod.ext htime hspace

/-- Global injectivity near the entire zero section, with no common time width.
This combines the proved local inverse criterion with locally closed embedding
shrinking, and keeps the resulting neighborhood inside the true flow domain. -/
theorem transverse_injective_neighborhood
    {k : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M)
    (hF : IsMaximalFamily X F) (i : H → M)
    (hi : MapClassData.IsSmoothEmbedding T S i) (htrans : IsTransverse T S X i) :
    ∃ V : Set (ℝ × H), IsOpen V ∧ (∀ q, (0,q) ∈ V) ∧
      V ⊆ parameterDomain i F ∧ InjOn (parameterMap i F) V := by
  obtain ⟨h, hh⟩ := hi.2.2.2
  have he : Topology.IsEmbedding i := by
    have hcomp := (Topology.IsEmbedding.subtypeVal (p := fun y => y ∈ Set.range i)).comp h.isEmbedding
    convert hcomp using 1
    exact (funext hh).symm
  exact parameterMap_injective_neighborhood T S B X F hF i hi.1 he
    (parameterMap_locally_injective T S B X F hF i hi htrans)


/-- The smooth product-coordinate test depends only on the germ of the map. -/
theorem productSmoothAt_congr
    {k n : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold n .euclidean M)
    {f g : ℝ × H → M} {z : ℝ × H}
    (hf : ProductSmoothAt T S f z) (h : g =ᶠ[𝓝 z] f) :
    ProductSmoothAt T S g z := by
  have hz : g z = f z := h.eq_of_nhds
  refine ⟨hf.1.congr_of_eventuallyEq h, ?_⟩
  intro e he d hd hze hzd
  obtain ⟨U, hU, hzU, G, hG, heG⟩ := hf.2 e he d hd hze (by simpa only [hz] using hzd)
  refine ⟨U, hU, hzU, G, hG, ?_⟩
  filter_upwards [heG, h] with w hw heq
  rw [heq]
  exact hw

/-- The inverse product-coordinate test also depends only on a germ. -/
theorem smoothToProductAt_congr
    {k n : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (T : SmoothManifold k .euclidean H)
    {f g : M → ℝ × H} {p : M}
    (hf : SmoothToProductAt S T f p) (h : g =ᶠ[𝓝 p] f) :
    SmoothToProductAt S T g p := by
  have hp : g p = f p := h.eq_of_nhds
  refine ⟨hf.1.congr_of_eventuallyEq h, ?_⟩
  intro d hd e he hpd hpe
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := hf.2 d hd e he hpd (by simpa only [hp] using hpe)
  refine ⟨U, hU, hpU, G, hG, ?_⟩
  filter_upwards [heG, h] with q hq heq
  rw [heq]
  exact hq


section LocalHomeomorphismGluing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]

/-- The inverse of an injective global map agrees with any local inverse on its target. -/
theorem inverse_eqOn_local (f : X → Y) (D : Set X) (hinj : InjOn f D)
    (c : OpenPartialHomeomorph X Y) (hcD : c.source ⊆ D)
    (hcf : EqOn c f c.source) :
    EqOn (hinj.toPartialEquiv f D).symm c.symm c.target := by
  intro y hy
  have hcx : c.symm y ∈ c.source := c.map_target hy
  have heq : f (c.symm y) = y := (hcf hcx).symm.trans (c.right_inv hy)
  change (hinj.toPartialEquiv f D).symm y = c.symm y
  calc
    (hinj.toPartialEquiv f D).symm y =
        (hinj.toPartialEquiv f D).symm (f (c.symm y)) := congrArg _ heq.symm
    _ = c.symm y := (hinj.toPartialEquiv f D).left_inv (hcD hcx)

theorem exists_openPartialHomeomorph_of_locally_eq
    (f : X → Y) (D : Set X) (hD : IsOpen D) (hinj : InjOn f D)
    (hcont : ContinuousOn f D)
    (hloc : ∀ x ∈ D, ∃ c : OpenPartialHomeomorph X Y,
      x ∈ c.source ∧ c.source ⊆ D ∧ EqOn c f c.source) :
    ∃ h : OpenPartialHomeomorph X Y,
      h.source = D ∧ (h : X → Y) = f ∧ h.target = f '' D := by
  let e := hinj.toPartialEquiv f D
  have hopen : IsOpen (f '' D) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨c, hxc, hcD, hcf⟩ := hloc x hx
    have hfc : f x ∈ c.target := hcf hxc ▸ c.map_source hxc
    refine mem_of_superset (c.open_target.mem_nhds hfc) ?_
    intro y hy
    exact ⟨c.symm y, hcD (c.map_target hy),
      (hcf (c.map_target hy)).symm.trans (c.right_inv hy)⟩
  have hcinv : ContinuousOn e.symm (f '' D) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨c, hxc, hcD, hcf⟩ := hloc x hx
    have hfc : f x ∈ c.target := hcf hxc ▸ c.map_source hxc
    have hevent : e.symm =ᶠ[𝓝 (f x)] c.symm :=
      Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hfc)
        (inverse_eqOn_local f D hinj c hcD hcf)
    exact ((c.continuousAt_symm hfc).congr_of_eventuallyEq hevent).continuousWithinAt
  let h : OpenPartialHomeomorph X Y :=
    { toPartialEquiv := e
      open_source := hD
      open_target := hopen
      continuousOn_toFun := hcont
      continuousOn_invFun := hcinv }
  exact ⟨h, rfl, rfl, rfl⟩


/-- The local charts may have sources larger than the final domain, and any additional
property of the charts is retained in the inverse's local representation. -/
theorem exists_openPartialHomeomorph_of_locally_eq_with_property
    (f : X → Y) (D : Set X) (hD : IsOpen D) (hinj : InjOn f D)
    (hcont : ContinuousOn f D) (P : OpenPartialHomeomorph X Y → Prop)
    (hloc : ∀ x ∈ D, ∃ c : OpenPartialHomeomorph X Y,
      x ∈ c.source ∧ EqOn c f c.source ∧ P c) :
    ∃ h : OpenPartialHomeomorph X Y,
      h.source = D ∧ (h : X → Y) = f ∧ h.target = f '' D ∧
      ∀ y ∈ h.target, ∃ c : OpenPartialHomeomorph X Y,
        P c ∧ y ∈ c.target ∧ h.symm =ᶠ[𝓝 y] c.symm := by
  have hloc' : ∀ x ∈ D, ∃ c : OpenPartialHomeomorph X Y,
      x ∈ c.source ∧ c.source ⊆ D ∧ EqOn c f c.source := by
    intro x hx
    obtain ⟨c, hxc, hcf, _⟩ := hloc x hx
    exact ⟨c.restrOpen D hD, ⟨hxc, hx⟩, inter_subset_right,
      fun z hz => hcf hz.1⟩
  obtain ⟨h, hs, hf, ht⟩ :=
    exists_openPartialHomeomorph_of_locally_eq f D hD hinj hcont hloc'
  refine ⟨h, hs, hf, ht, ?_⟩
  intro y hy
  rw [ht] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨c, hxc, hcf, hPc⟩ := hloc x hx
  have hfc : f x ∈ c.target := hcf hxc ▸ c.map_source hxc
  refine ⟨c, hPc, hfc, ?_⟩
  let d := c.restrOpen D hD
  have hxd : x ∈ d.source := ⟨hxc, hx⟩
  have hdf : EqOn d f d.source := fun z hz => hcf hz.1
  have hfd : f x ∈ d.target := hdf hxd ▸ d.map_source hxd
  filter_upwards [d.open_target.mem_nhds hfd] with z hz
  have hdz : d.symm z ∈ d.source := d.map_target hz
  have hhz : h.symm (h (d.symm z)) = d.symm z :=
    h.left_inv (hs.symm ▸ hdz.2)
  have hmap : h (d.symm z) = z := by
    rw [hf]
    exact (hdf hdz).symm.trans (d.right_inv hz)
  rw [hmap] at hhz
  exact hhz


end LocalHomeomorphismGluing

/-- At each zero-time point the actual parameter map has a jointly smooth
local inverse on an open target, in every pair of original atlas charts. -/
theorem parameterMap_local_inverse
    {k : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M)
    (hF : IsMaximalFamily X F) (i : H → M)
    (hi : MapClassData.IsSmoothEmbedding T S i) (htrans : IsTransverse T S X i)
    (q : H) :
    ∃ h : OpenPartialHomeomorph (ℝ × H) M,
      (0,q) ∈ h.source ∧ h.source ⊆ parameterDomain i F ∧
      EqOn h (parameterMap i F) h.source ∧
      ∀ p ∈ h.target, SmoothToProductAt S T h.symm p := by
  obtain ⟨e, he, hqe⟩ := T.smoothStructure.property.1.1 q
  obtain ⟨d, hd, hqd⟩ := S.smoothStructure.property.1.1 (i q)
  have hs := parameterMap_smoothAt T S B X F hF i hi.1 (0,q)
    (zero_mem_parameterDomain S B X F hF i q)
  obtain ⟨U, hU, hyU, G, hG, heG⟩ := hs.2 e he d hd hqe
    ((parameterMap_zero S B X F hF i q).symm ▸ hqd)
  have hbij := parameterMap_derivative_bijective T S B X F hF i hi htrans q
    e d he hd hqe hqd U G hU hyU hG heG
  obtain ⟨j, hyj, _, hj, hji⟩ := smooth_local_inverse G U hU hG (0,(e q).val) hyU hbij
  let A := InteriorInverse.ambientChart e
  let D := InteriorInverse.ambientChart d
  let C := (OpenPartialHomeomorph.refl ℝ).prod A
  let h₀ := C.trans (j.trans D.symm)
  have hqA : q ∈ A.source := by simpa only [A, ambient_euclidean_source] using hqe
  have hiqD : i q ∈ D.source := by simpa only [D, ambient_euclidean_source] using hqd
  have hC : ∀ z : ℝ × H, C z = (z.1,(e z.2).val) := by
    intro z
    simp only [C, OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply,
      A, InteriorInverse.ambientChart_apply, id_eq]
  have hG0 : G (0,(e q).val) = D (i q) := by
    simpa only [D, InteriorInverse.ambientChart_apply, parameterMap_zero S B X F hF i q]
      using heG.eq_of_nhds
  have hq₀ : (0,q) ∈ h₀.source := by
    refine ⟨⟨Set.mem_univ _, hqA⟩, ?_, ?_⟩
    · change C (0,q) ∈ j.source
      rw [hC]
      exact hyj
    · change j (C (0,q)) ∈ D.target
      rw [hC, hj, hG0]
      exact D.map_source hiqD
  have hEqNear : (h₀ : ℝ × H → M) =ᶠ[𝓝 (0,q)] parameterMap i F := by
    have hpD : parameterMap i F (0,q) ∈ d.source := by
      simpa only [parameterMap_zero S B X F hF i q] using hqd
    filter_upwards [heG, hs.1.preimage_mem_nhds (d.open_source.mem_nhds hpD)] with z hz hzD
    change D.symm (j (C z)) = parameterMap i F z
    rw [hC, hj, hz]
    exact D.left_inv (by
      simpa only [D, ambient_euclidean_source] using
        (show parameterMap i F z ∈ d.source from hzD))
  have hnear : {z : ℝ × H | z ∈ h₀.source ∧ z ∈ parameterDomain i F ∧
      h₀ z = parameterMap i F z} ∈ 𝓝 (0,q) :=
    inter_mem (h₀.open_source.mem_nhds hq₀)
      (inter_mem ((parameterDomain_isOpen T S B X F hF i hi.1).mem_nhds
        (zero_mem_parameterDomain S B X F hF i q)) hEqNear)
  obtain ⟨W, hWsub, hW, hqW⟩ := mem_nhds_iff.mp hnear
  let h := h₀.restrOpen W hW
  refine ⟨h, ⟨hq₀, hqW⟩, (fun z hz => (hWsub hz.2).2.1),
    (fun z hz => (hWsub hz.2).2.2), ?_⟩
  intro p hp
  refine ⟨h.symm.continuousAt hp, ?_⟩
  intro d' hd' e' he' hpd' hpe'
  let D' := InteriorInverse.ambientChart d'
  let E' := InteriorInverse.ambientChart e'
  let K := D'.symm.trans D
  let J := A.symm.trans E'
  let P := (OpenPartialHomeomorph.refl ℝ).prod J
  let l := K.trans (j.symm.trans P)
  have hp₀ : p ∈ h₀.target := hp.1
  change (p ∈ D.source ∧ D p ∈ j.target) ∧ j.symm (D p) ∈ C.target at hp₀
  have hpD' : p ∈ D'.source := by simpa only [D', ambient_euclidean_source] using hpd'
  have hpK : D' p ∈ K.source := by
    refine ⟨D'.map_source hpD', ?_⟩
    change D'.symm (D' p) ∈ D.source
    rw [D'.left_inv hpD']
    exact hp₀.1.1
  have hJ : (j.symm (D p)).2 ∈ J.source := by
    refine ⟨hp₀.2.2, ?_⟩
    change A.symm (j.symm (D p)).2 ∈ E'.source
    change A.symm (j.symm (D p)).2 ∈ e'.source at hpe'
    simpa only [E', ambient_euclidean_source] using hpe'
  have hpl : D' p ∈ l.source := by
    refine ⟨hpK, ?_, ?_⟩
    · change D (D'.symm (D' p)) ∈ j.target
      rw [D'.left_inv hpD']
      exact hp₀.1.2
    · change j.symm (D (D'.symm (D' p))) ∈ P.source
      rw [D'.left_inv hpD']
      exact ⟨Set.mem_univ _, hJ⟩
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) P P.source := by
    exact contDiffOn_fst.prodMk ((ambient_transition_contDiff T e e' he he').comp
      contDiffOn_snd (fun _ hz => hz.2))
  have hl := partial_comp_contDiff K (j.symm.trans P)
    (ambient_transition_contDiff S d' d hd' hd)
    (partial_comp_contDiff j.symm P hji hP)
  refine ⟨l.source, l.open_source, hpl, l, hl, ?_⟩
  filter_upwards [D'.open_source.mem_nhds hpD'] with y hy
  change P (j.symm (D (D'.symm (D' y)))) =
    ((h.symm y).1, (e' (h.symm y).2).val)
  rw [D'.left_inv hy]
  rfl

/-- The local inverse charts cover an open neighborhood of the whole zero-time
section. Shrinking inside this locus gives one diffeomorphism, even when the
hypersurface is noncompact or not closed in the ambient manifold. -/
theorem hypersurface_flowout :
    Specs.SmoothManifolds.Ch06.Flowout.hypersurface_flowoutType.{u} := by
  classical
  intro k H M _ _ T S B X F hF i hi htrans
  cases isEmpty_or_nonempty H with
  | inl hH =>
      letI : IsEmpty H := hH
      exact empty_hypersurface_flowout T S B X F i
  | inr hH =>
      letI : Nonempty H := hH
      have hcharts := parameterMap_local_inverse T S B X F hF i hi htrans
      choose c hc0 hcdom hceq hcinv using hcharts
      obtain ⟨V₀, hV₀, hzero, hdom, hinj⟩ :=
        transverse_injective_neighborhood T S B X F hF i hi htrans
      let V : Set (ℝ × H) := V₀ ∩ ⋃ q, (c q).source
      have hV : IsOpen V := hV₀.inter (isOpen_iUnion fun q => (c q).open_source)
      have hVdom : V ⊆ parameterDomain i F := fun _ hx => hdom hx.1
      have hcont : ContinuousOn (parameterMap i F) V := fun z hz =>
        (parameterMap_smoothAt T S B X F hF i hi.1 z (hVdom hz)).1.continuousWithinAt
      let P : OpenPartialHomeomorph (ℝ × H) M → Prop := fun b =>
        ∀ y ∈ b.target, SmoothToProductAt S T b.symm y
      have hlocal : ∀ z ∈ V, ∃ b : OpenPartialHomeomorph (ℝ × H) M,
          z ∈ b.source ∧ EqOn b (parameterMap i F) b.source ∧ P b := by
        intro z hz
        obtain ⟨q, hq⟩ := mem_iUnion.mp hz.2
        exact ⟨c q, hq, hceq q, hcinv q⟩
      obtain ⟨h, hs, hf, _, hginv⟩ :=
        exists_openPartialHomeomorph_of_locally_eq_with_property
          (parameterMap i F) V hV (hinj.mono inter_subset_left) hcont P hlocal
      have hzsource : ∀ q, (0,q) ∈ h.source := by
        intro q
        rw [hs]
        exact ⟨hzero q, mem_iUnion.mpr ⟨q, hc0 q⟩⟩
      have hhdom : h.source ⊆ parameterDomain i F := hs ▸ hVdom
      have hheq : EqOn h (parameterMap i F) h.source := fun _ _ => congrFun hf _
      have hh : IsFlowout T S X i F h := by
        refine ⟨hzsource, hhdom, hheq, ?_, ?_, ?_, ?_, ?_⟩
        · intro q
          rw [hf]
          exact parameterMap_zero S B X F hF i q
        · rintro y ⟨q, rfl⟩
          have hy := h.map_source (hzsource q)
          simpa only [hf, parameterMap_zero S B X F hF i q] using hy
        · intro z hz
          rw [hf]
          exact parameterMap_smoothAt T S B X F hF i hi.1 z (hhdom hz)
        · intro y hy
          obtain ⟨b, hb, hyb, heq⟩ := hginv y hy
          exact smoothToProductAt_congr S T (hb y hyb) heq
        · exact carriesTimeField_of_eqOn S B X F hF i h hhdom hheq
      exact ⟨h.source, h.target, h.open_source, h.open_target,
        h.toHomeomorphSourceTarget, flowoutOn_of_partial T S B X F hF i h hh⟩

end SmoothManifolds.Flowout
