import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringLifting

namespace P202.Topology
open P202Specs.Topology
open scoped unitInterval
open Function Set _root_.Topology
universe u v w
noncomputable section
variable {E : Type u} {B : Type v} {Z : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]

/-- The sheet's homeomorphism with the subspace U, retaining the projection. -/
def sheetHomeomorph {p : E → B} {U : Set B} (s : CoveringSheet p U) :
    s.chart.source ≃ₜ U :=
  s.chart.toHomeomorphSourceTarget.trans (Homeomorph.setCongr s.target_eq)

theorem sheetHomeomorph_over {p : E → B} {U : Set B} (s : CoveringSheet p U)
    (e : s.chart.source) : (sheetHomeomorph s e : B) = p e := by
  change s.chart e = p e
  rw [s.projection]

/-- A trivialization with discrete fiber gives one open sheet for each fiber value. -/
def trivializationSheet {p : E → B} {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    (t : Bundle.Trivialization F p) (i : F) : CoveringSheet p t.baseSet where
  chart := {
    toFun := p
    invFun := fun b => t.invFun (b, i)
    source := t.source ∩ (fun e => (t e).2) ⁻¹' {i}
    target := t.baseSet
    map_source' := fun e he => t.mem_source.mp he.1
    map_target' := by
      intro b hb
      exact ⟨t.map_target (t.mem_target.mpr hb), by simp [t.apply_symm_apply' hb]⟩
    left_inv' := by
      intro e he
      have hi : (t e).2 = i := he.2
      rw [← hi]
      exact t.symm_apply_mk_proj he.1
    right_inv' := fun b hb => t.proj_symm_apply' hb
    open_source := t.continuousOn_toFun.snd.isOpen_inter_preimage t.open_source
      (isOpen_discrete {i})
    open_target := t.open_baseSet
    continuousOn_toFun := t.continuousOn_proj.mono Set.inter_subset_left
    continuousOn_invFun := t.continuousOn_invFun.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun b hb => t.mem_target.mpr hb) }
  projection := rfl
  target_eq := rfl

theorem trivialization_evenlyCovered {p : E → B} {F : Type*}
    [TopologicalSpace F] [DiscreteTopology F] (t : Bundle.Trivialization F p) :
    EvenlyCovered p t.baseSet := by
  refine ⟨t.open_baseSet, Set.range (trivializationSheet t), ?_, ?_⟩
  · rintro s ⟨i, rfl⟩ s' ⟨j, rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro e he he'
    have hij : i = j := he.2.symm.trans he'.2
    exact hne (hij ▸ rfl)
  · ext e
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨s, ⟨i, rfl⟩, he⟩
      exact t.mem_source.mp he.1
    · intro he
      exact ⟨trivializationSheet t (t e).2, ⟨_, rfl⟩, t.mem_source.mpr he, rfl⟩

/-- An open sheet decomposition yields the library's local product chart. -/
theorem covering_to_library {p : E → B} (hp : Covering p) : IsCoveringMap p := by
  intro b
  obtain ⟨U, hb, hU, S, hdis, hcover⟩ := hp.2 b
  have : Nonempty (B → E) := ⟨fun b => (hp.1 b).choose⟩
  obtain ⟨e, he⟩ := hp.1 b
  have hemem : e ∈ ⋃ s ∈ S, s.chart.source := by
    rw [hcover, Set.mem_preimage, he]
    exact hb
  simp only [Set.mem_iUnion] at hemem
  obtain ⟨s, hs, _⟩ := hemem
  have : Nonempty S := ⟨⟨s, hs⟩⟩
  let : TopologicalSpace S := ⊥
  have : DiscreteTopology S := ⟨rfl⟩
  let V (s : S) : Set E := s.1.chart.source
  have ho (s : S) {W : Set B} (hW : W ⊆ U) :
      IsOpen W ↔ IsOpen (p ⁻¹' W ∩ V s) := by
    have htarget : W ⊆ s.1.chart.target := by rwa [s.1.target_eq]
    rw [← s.1.chart.isOpen_symm_image_iff_of_subset_target htarget,
      s.1.chart.symm_image_eq_source_inter_preimage htarget,
      s.1.projection, Set.inter_comm]
  have hinj (s : S) : (V s).InjOn p := by
    rw [← s.1.projection]
    exact s.1.chart.injOn
  have hsurj (s : S) : (V s).SurjOn p U := by
    simpa only [s.1.projection, s.1.target_eq] using s.1.chart.surjOn
  have hdis' : Pairwise (Disjoint on V) := by
    intro s t hne
    exact hdis s.2 t.2 (fun h => hne (Subtype.ext h))
  have hex : p ⁻¹' U ⊆ ⋃ s : S, V s := by
    intro e he
    rw [← hcover] at he
    simp only [Set.mem_iUnion] at he ⊢
    obtain ⟨s, hs, he⟩ := he
    exact ⟨⟨s, hs⟩, he⟩
  exact (IsEvenlyCovered.of_trivialization
    (t := hU.trivializationDiscrete V U ho hinj hsurj hdis' hex) hb).to_isEvenlyCovered_preimage

theorem coveringBridge : CoveringExpected.coveringBridge.{u,v} := by
  intro E B _ _ p
  constructor
  · intro hp
    exact ⟨covering_to_library hp, hp.1⟩
  · rintro ⟨hp, hsurj⟩
    refine ⟨hsurj, fun b => ?_⟩
    have : Nonempty (p ⁻¹' {b}) := ⟨⟨(hsurj b).choose, (hsurj b).choose_spec⟩⟩
    have := (hp b).discreteTopology_fiber
    exact ⟨(hp b).toTrivialization.baseSet, (hp b).mem_toTrivialization_baseSet,
      trivialization_evenlyCovered (hp b).toTrivialization⟩

theorem coveringContinuous : CoveringExpected.coveringContinuous.{u,v} := by
  intro E B _ _ p hp
  exact (covering_to_library hp).continuous


theorem pathLifting : CoveringExpected.pathLifting.{u,v} := by
  intro E B _ _ p hp a e he
  let cov := covering_to_library hp
  refine ⟨cov.liftPath a e he.symm, ⟨?_, cov.liftPath_zero a e he.symm⟩, ?_⟩
  · intro t
    exact congr_fun (cov.liftPath_lifts a e he.symm) t
  · intro M hM
    exact (cov.eq_liftPath_iff' he.symm).mpr ⟨funext hM.1, hM.2⟩

/-- Transpose both the base homotopy and its lift through product swap. -/
theorem homotopyLifting : CoveringExpected.homotopyLifting.{u,v,w} := by
  intro E B Z _ _ _ p hp F h hh
  let cov := covering_to_library hp
  let G : C(unitInterval × Z, B) := F.comp ContinuousMap.prodSwap
  have hG : ∀ z, G (0, z) = p (h z) := fun z => (hh z).symm
  let K := cov.liftHomotopy G h hG
  let L : C(Z × unitInterval, E) := K.comp ContinuousMap.prodSwap
  refine ⟨L, ⟨?_, ?_⟩, ?_⟩
  · intro ⟨z, t⟩
    exact congr_fun (cov.liftHomotopy_lifts G h hG) (t, z)
  · intro z
    exact cov.liftHomotopy_zero G h hG z
  · intro M hM
    have hswap : M.comp ContinuousMap.prodSwap = K :=
      (cov.eq_liftHomotopy_iff' hG (M.comp ContinuousMap.prodSwap)).mpr
        ⟨funext (fun q => hM.1 (q.2, q.1)), hM.2⟩
    ext ⟨z, t⟩
    exact DFunLike.congr_fun hswap (t, z)

theorem constantLift : CoveringExpected.constantLift.{u,v} := by
  intro E B _ _ p hp b L hL t
  exact (covering_to_library hp).const_of_comp L.continuous
    (fun s t => (hL s).trans (hL t).symm) t 0

theorem homotopyEndpoints : CoveringExpected.homotopyEndpoints.{u,v} := by
  intro E B _ _ p hp x y a b H L e hL h0
  refine ⟨h0, fun s => ?_⟩
  apply (covering_to_library hp).const_of_comp
    (L.continuous.comp (continuous_id.prodMk continuous_const)) (a := s) (a' := 0)
  intro s t
  exact ((hL (s, 1)).trans (H.target s)).trans
    ((hL (t, 1)).trans (H.target t)).symm

theorem pathHomotopyLifts : CoveringExpected.pathHomotopyLifts.{u,v} := by
  intro E B _ _ p hp x y a b H L e hL h0
  let cov := covering_to_library hp
  exact cov.isLocalHomeomorph.monodromy_theorem cov.isSeparatedMap H L hL
    (fun s => (h0 s).trans (h0 0).symm)

theorem homotopicLiftEndpoints : CoveringExpected.homotopicLiftEndpoints.{u,v} := by
  intro E B _ _ p hp x y a b hH L M hL hM h0
  let cov := covering_to_library hp
  have ha : a.toContinuousMap 0 = p (L 0) := (hL 0).symm
  have hb : b.toContinuousMap 0 = p (L 0) := by rw [h0]; exact (hM 0).symm
  have hLeq := (cov.eq_liftPath_iff' ha).mpr ⟨funext hL, rfl⟩
  have hMeq := (cov.eq_liftPath_iff' hb).mpr ⟨funext hM, h0.symm⟩
  rw [hLeq, hMeq]
  exact cov.liftPath_apply_one_eq_of_homotopicRel hH (L 0) ha hb

end
end P202.Topology
