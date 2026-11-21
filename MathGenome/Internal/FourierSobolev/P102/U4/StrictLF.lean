import MathGenome.Internal.FourierSobolev.Specs.P102.U4.StrictLF
import MathGenome.Internal.FourierSobolev.P102.U4.TestSpace
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Metrizable.Uniformity

noncomputable section
open Set TopologicalSpace Topology Filter
open scoped ContDiff Distributions Topology BoundedContinuousFunction
namespace P102.U4

-- Pin the normed structure before Lean infers the topology on bounded derivative maps.
local instance jetNormedGroup {d k : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    NormedAddCommGroup (Space d [×k]→L[ℝ] 𝕜) := inferInstance

/-- The global derivative of exactly order k, with its bounded sup norm. -/
def testDerivativeCLM {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (k : ℕ) :
    TestSpace 𝕜 Ω →L[𝕜] (Space d →ᵇ (Space d [×k]→L[ℝ] 𝕜)) :=
  TestFunction.limitCLM 𝕜 (Ω := Ω) (n := ⊤)
    (fun f => ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k
      (ContDiffMapSupportedIn.of_support_subset f.contDiff subset_closure :
        FixedSupport d 𝕜 ⟨tsupport f, f.hasCompactSupport⟩))
    (fun _ _ => ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k)
    (fun _ _ _ => by
      ext x
      simp only [ContDiffMapSupportedIn.structureMapCLM_top_apply]
      rfl)

@[simp] theorem testDerivativeCLM_apply {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (k : ℕ) (f : TestSpace 𝕜 Ω) (x : Space d) :
    testDerivativeCLM 𝕜 Ω k f x = iteratedFDeriv ℝ k f x := by
  simp only [testDerivativeCLM, TestFunction.limitCLM_apply,
    ContDiffMapSupportedIn.structureMapCLM_top_apply]
  rfl

/-- Each stage has exactly the topology induced by all global derivative maps. -/
theorem isEmbedding_stageInclusion {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    {Ω : Opens (Space d)} {K : Compacts (Space d)} (hK : (K : Set (Space d)) ⊆ Ω) :
    IsEmbedding (stageInclusion 𝕜 hK) := by
  let J := ContinuousLinearMap.pi (testDerivativeCLM 𝕜 Ω)
  have heq : J ∘ stageInclusion 𝕜 hK =
      ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤) := by
    funext f k
    ext x
    simp [J, stageInclusion]
  apply Topology.IsEmbedding.of_comp (stageInclusion 𝕜 hK).continuous J.continuous
  rw [heq]
  exact (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM 𝕜).isEmbedding

theorem range_stageInclusion {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    {Ω : Opens (Space d)} {K : Compacts (Space d)} (hK : (K : Set (Space d)) ⊆ Ω) :
    Set.range (stageInclusion 𝕜 hK) = {f | ∀ x ∉ K, f x = 0} := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩ x hx
    exact g.zero_on_compl hx
  · intro hf
    let g : FixedSupport d 𝕜 K := ContDiffMapSupportedIn.of_support_subset f.contDiff
      (fun x hx => by by_contra hn; exact hx (hf x hn))
    exact ⟨g, by ext x; rfl⟩

theorem stageClosedEmbedding : Expected.StageClosedEmbedding := by
  intro d 𝕜 _ Ω K hK
  refine ⟨isEmbedding_stageInclusion 𝕜 hK, ?_⟩
  rw [range_stageInclusion]
  have heq : {f : TestSpace 𝕜 Ω | ∀ x ∉ K, f x = 0} =
      ⋂ (x : Space d) (_ : x ∉ K), {f : TestSpace 𝕜 Ω | f x = 0} := by ext; simp
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (continuous_eval_const x) continuous_const

theorem fixedStageClosedEmbedding : Expected.FixedStageClosedEmbedding := by
  intro d 𝕜 _ K L hKL
  let i : FixedSupport d 𝕜 K →L[𝕜] FixedSupport d 𝕜 L :=
    ContDiffMapSupportedIn.monoCLM 𝕜
  have hi (f : FixedSupport d 𝕜 K) : (i f : Space d → 𝕜) = f := by
    simp [i, ContDiffMapSupportedIn.monoCLM_apply, hKL]
  have hJ : (ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤) :
      FixedSupport d 𝕜 L →L[𝕜] _) ∘ i =
      ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤) := by
    funext f k
    ext x
    simp [hi]
  have he : IsEmbedding i := Topology.IsEmbedding.of_comp i.continuous
    (ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤)).continuous
    (hJ ▸ (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM 𝕜).isEmbedding)
  refine ⟨he, ?_⟩
  have hr : Set.range i = {f : FixedSupport d 𝕜 L | ∀ x ∉ K, f x = 0} := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩ x hx
      rw [congrFun (hi g)]
      exact g.zero_on_compl hx
    · intro hf
      let g : FixedSupport d 𝕜 K := ContDiffMapSupportedIn.of_support_subset f.contDiff
        (fun x hx => by by_contra hn; exact hx (hf x hn))
      exact ⟨g, by ext x; rw [congrFun (hi g)]; rfl⟩
  rw [hr]
  have heq : {f : FixedSupport d 𝕜 L | ∀ x ∉ K, f x = 0} =
      ⋂ (x : Space d) (_ : x ∉ K), {f : FixedSupport d 𝕜 L | f x = 0} := by ext; simp
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (continuous_eval_const x) continuous_const

/-- The full derivative map has closed range: uniform limits preserve the derivative
relations and the vanishing condition off K. -/
theorem isClosed_range_derivativeMap {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) :
    IsClosed (Set.range (ContinuousLinearMap.pi
      (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤) :
      FixedSupport d 𝕜 K →L[𝕜] Π k, Space d →ᵇ (Space d [×k]→L[ℝ] 𝕜))) := by
  apply IsSeqClosed.isClosed
  intro u g hu hug
  choose f hf using hu
  have hlim (k : ℕ) : Tendsto
      (fun n => ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k (f n)) atTop (𝓝 (g k)) := by
    have h := (tendsto_pi_nhds.mp hug) k
    convert h using 1
    funext n
    exact congrFun (hf n) k
  have hunif (k : ℕ) : TendstoUniformly
      (fun n => iteratedFDeriv ℝ k (f n)) (g k) atTop := by
    simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hlim k))
  have hderiv (k : ℕ) (x : Space d) : HasFDerivAt (g k)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space d) 𝕜)
        (g (k + 1) x)) x := by
    let c := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space d) 𝕜
    refine hasFDerivAt_of_tendstoUniformly
      (f := fun n => iteratedFDeriv ℝ k (f n))
      (g := g k) (g' := fun x => c (g (k + 1) x))
      (f' := fun n x => c (iteratedFDeriv ℝ (k + 1) (f n) x))
      (c.isometry.uniformContinuous.comp_tendstoUniformly (hunif (k + 1))) ?_ ?_ x
    · intro n y
      have hd := ((f n).contDiff.iteratedFDeriv_right (m := 1) (i := k) (by simp)).differentiable
        one_ne_zero y
      simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using hd.hasFDerivAt
    · exact fun y => (hunif k).tendsto_at y
  let φ : Space d → 𝕜 := fun x => (g 0 x).curry0
  have hjet : ∀ k, iteratedFDeriv ℝ k φ = g k := by
    intro k
    induction k with
    | zero =>
      funext x
      exact ContinuousMultilinearMap.uncurry0_curry0 (g 0 x)
    | succ k ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, ih]
      funext x
      change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space d) 𝕜).symm
        (fderiv ℝ (g k) x) = g (k + 1) x
      rw [(hderiv k x).fderiv]
      exact LinearIsometryEquiv.symm_apply_apply _ _
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    apply contDiff_iff_continuous_differentiable.mpr
    constructor
    · intro k _
      rw [hjet k]
      exact (g k).continuous
    · intro k _
      rw [hjet k]
      exact fun x => (hderiv k x).differentiableAt
  have hsupport : Function.support φ ⊆ K := by
    intro x hx
    by_contra hxK
    have hz : ∀ n, iteratedFDeriv ℝ 0 (f n) x = 0 := fun n =>
      (f n).iteratedFDeriv_zero_on_compl hxK
    have hzero : g 0 x = 0 := tendsto_nhds_unique ((hunif 0).tendsto_at x)
      (by simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (0 : Space d [×0]→L[ℝ] 𝕜)) atTop (𝓝 0)))
    apply hx
    simp [φ, hzero]
  let ψ : FixedSupport d 𝕜 K := ContDiffMapSupportedIn.of_support_subset hsmooth hsupport
  refine ⟨ψ, ?_⟩
  funext k
  apply BoundedContinuousFunction.ext
  intro x
  change iteratedFDeriv ℝ k φ x = g k x
  exact congrFun (hjet k) x

theorem fixedSupportComplete {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) : CompleteSpace (FixedSupport d 𝕜 K) :=
  (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM 𝕜).isUniformInducing.completeSpace
    (isClosed_range_derivativeMap 𝕜 K).isComplete

theorem fixedSupportMetrizable {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) : MetrizableSpace (FixedSupport d 𝕜 K) :=
  (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM 𝕜).isEmbedding.metrizableSpace

theorem fixedSupportFrechet : Expected.FixedSupportFrechet := by
  intro d 𝕜 _ K
  exact ⟨inferInstance, fixedSupportMetrizable 𝕜 K, inferInstance,
    fixedSupportComplete 𝕜 K, coordinateStageTopology d 𝕜 K⟩

theorem TestExhaustion.monotone {d : ℕ} {Ω : Opens (Space d)} (e : TestExhaustion Ω) :
    Monotone e.compact :=
  monotone_nat_of_le_succ fun n => (e.subset_interior_succ n).trans interior_subset

theorem exhaustionCofinality : Expected.ExhaustionCofinality := by
  intro d Ω e K hK
  obtain ⟨n, hn⟩ := K.isCompact.elim_directed_cover
    (fun n => interior (e.compact n : Set (Space d))) (fun _ => isOpen_interior)
    (fun x hx => by rw [e.interiors_cover]; exact hK hx)
    (Monotone.directed_le fun _ _ h => interior_mono (e.monotone h))
  exact ⟨n, hn.trans interior_subset⟩

theorem existsTestExhaustion : Expected.ExistsTestExhaustion := by
  intro d Ω
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let c := CompactExhaustion.choice Ω
  let K : ℕ → Compacts (Space d) := fun n =>
    ⟨Subtype.val '' c n, (c.isCompact n).image continuous_subtype_val⟩
  have hsub : ∀ n, (K n : Set (Space d)) ⊆ Ω := by
    rintro n x ⟨y, _, rfl⟩
    exact y.property
  have hinter : ∀ n, (K n : Set (Space d)) ⊆ interior (K (n + 1)) := by
    rintro n x ⟨y, hy, rfl⟩
    exact (Ω.isOpen.isOpenMap_subtype_val.image_interior_subset (c (n + 1)))
      ⟨y, c.subset_interior_succ n hy, rfl⟩
  refine ⟨⟨K, hsub, hinter, subset_antisymm ?_ ?_⟩⟩
  · exact iUnion_subset fun n => interior_subset.trans (hsub n)
  · intro x hx
    obtain ⟨n, hn⟩ := c.exists_mem ⟨x, hx⟩
    exact mem_iUnion.mpr ⟨n + 1, hinter n ⟨⟨x, hx⟩, hn, rfl⟩⟩

/-- Cofinality works for restrictions of arbitrary maps and arbitrary target topologies. -/
theorem continuous_comp_stages_iff {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    {Ω : Opens (Space d)} (e : TestExhaustion Ω) {F : Type*} [TopologicalSpace F]
    (T : TestSpace 𝕜 Ω → F) :
    (∀ (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ Ω),
      Continuous (T ∘ stageInclusion 𝕜 hK)) ↔
      ∀ n, Continuous (T ∘ stageInclusion 𝕜 (e.subset_open n)) := by
  constructor
  · intro h n
    exact h _ _
  · intro h K hK
    obtain ⟨n, hKn⟩ := exhaustionCofinality d Ω e K hK
    let i : FixedSupport d 𝕜 K →L[𝕜] FixedSupport d 𝕜 (e.compact n) :=
      ContDiffMapSupportedIn.monoCLM 𝕜
    have hi (f : FixedSupport d 𝕜 K) : (i f : Space d → 𝕜) = f := by
      simp [i, ContDiffMapSupportedIn.monoCLM_apply, hKn]
    have heq : T ∘ stageInclusion 𝕜 hK =
        (T ∘ stageInclusion 𝕜 (e.subset_open n)) ∘ i := by
      funext f
      apply congrArg T
      ext x
      exact (congrFun (hi f) x).symm
    rw [heq]
    exact (h n).comp i.continuous

theorem exhaustionStageCoverage : Expected.ExhaustionStageCoverage := by
  intro d 𝕜 _ Ω e f
  obtain ⟨K, hK, g, rfl⟩ := stageCoverage d 𝕜 Ω f
  obtain ⟨n, hKn⟩ := exhaustionCofinality d Ω e K hK
  let i : FixedSupport d 𝕜 K →L[𝕜] FixedSupport d 𝕜 (e.compact n) :=
    ContDiffMapSupportedIn.monoCLM 𝕜
  refine ⟨n, i g, ?_⟩
  ext x
  change (i g) x = g x
  exact congrFun (by simp [i, ContDiffMapSupportedIn.monoCLM_apply, hKn]) x

theorem exhaustionTopology_eq : Expected.ExhaustionTopology := by
  intro d 𝕜 _ Ω e
  apply le_antisymm
  · change TestFunction.topologicalSpace Ω 𝕜 ⊤ ≤ sInf _
    apply le_sInf
    intro t ht
    let : TopologicalSpace (TestSpace 𝕜 Ω) := t
    let : IsTopologicalAddGroup (TestSpace 𝕜 Ω) := ht.1
    let : ContinuousSMul ℝ (TestSpace 𝕜 Ω) := ht.2.1
    let : LocallyConvexSpace ℝ (TestSpace 𝕜 Ω) := ht.2.2.1
    apply (finestTopology d 𝕜 Ω t).mpr
    exact (continuous_comp_stages_iff 𝕜 e id).mpr ht.2.2.2
  · apply sInf_le
    exact ⟨inferInstance, inferInstance, inferInstance,
      fun n => (stageInclusion 𝕜 (e.subset_open n)).continuous⟩

theorem exhaustionSeminormContinuity : Expected.ExhaustionSeminormContinuity := by
  intro d 𝕜 _ Ω e p
  constructor
  · intro hp n
    exact hp.comp (stageInclusion 𝕜 (e.subset_open n)).continuous
  · intro hp
    let q : SeminormFamily ℝ (TestSpace 𝕜 Ω) Unit := fun _ => p.restrictScalars ℝ
    let t : TopologicalSpace (TestSpace 𝕜 Ω) := q.moduleFilterBasis.topology
    let : TopologicalSpace (TestSpace 𝕜 Ω) := TestFunction.topologicalSpace Ω 𝕜 ⊤
    have hq : @WithSeminorms ℝ (TestSpace 𝕜 Ω) Unit _ _ _ q t :=
      @WithSeminorms.mk ℝ (TestSpace 𝕜 Ω) Unit _ _ _ q t rfl
    have hpt : @Continuous (TestSpace 𝕜 Ω) ℝ t _ p :=
      WithSeminorms.continuous_seminorm (t := t) hq ()
    let i (n : ℕ) : FixedSupport d 𝕜 (e.compact n) →ₗ[ℝ] TestSpace 𝕜 Ω :=
      (stageInclusion 𝕜 (e.subset_open n)).toLinearMap.restrictScalars ℝ
    have ht : TestFunction.topologicalSpace Ω 𝕜 ⊤ ≤ t := by
      let : TopologicalSpace (TestSpace 𝕜 Ω) := t
      let : IsTopologicalAddGroup (TestSpace 𝕜 Ω) := hq.isTopologicalAddGroup
      let : ContinuousSMul ℝ (TestSpace 𝕜 Ω) := hq.continuousSMul
      let : LocallyConvexSpace ℝ (TestSpace 𝕜 Ω) := hq.toLocallyConvexSpace
      apply (finestTopology d 𝕜 Ω t).mpr
      apply (continuous_comp_stages_iff 𝕜 e id).mpr
      intro n
      exact hq.continuous_of_continuous_comp (i n) (fun _ => hp n)
    have hi : @Continuous (TestSpace 𝕜 Ω) (TestSpace 𝕜 Ω)
        (TestFunction.topologicalSpace Ω 𝕜 ⊤) t id := continuous_id_iff_le.mpr ht
    exact @Continuous.comp _ _ _ (TestFunction.topologicalSpace Ω 𝕜 ⊤) t _ id p hpt hi

theorem emptyTestSpace : Expected.EmptyTestSpace := by
  intro d 𝕜 _
  exact ⟨fun f g => (emptyTests d 𝕜 f).trans (emptyTests d 𝕜 g).symm⟩

end P102.U4
