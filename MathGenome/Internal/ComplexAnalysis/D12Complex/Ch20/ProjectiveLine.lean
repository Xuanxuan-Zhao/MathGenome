import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.ProjectiveLine
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FunProp

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.ProjectiveLine

private def vectorToSphere (v : HomogeneousVector) : RiemannSphere :=
  if v.val.1 = 0 then sphereInfty else sphereFinite (v.val.2 / v.val.1)

private def toSphere : ComplexProjectiveLine → RiemannSphere :=
  Projectivization.lift vectorToSphere (by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ t ht
    have ht0 : t ≠ 0 := by
      intro h
      apply hv
      simpa [h] using ht
    change v = t • w at ht
    subst v
    dsimp [vectorToSphere]
    simp only [mul_eq_zero,
      ht0, false_or, mul_div_mul_left _ _ ht0])

@[simp] private theorem toSphere_projection (v : HomogeneousVector) :
    toSphere (projection v) = vectorToSphere v := rfl

@[simp] private theorem toSphere_finiteParam (z : ℂ) :
    toSphere (finiteParam z) = sphereFinite z := by
  simp [finiteParam, vectorToSphere]

@[simp] private theorem toSphere_reciprocalParam (w : ℂ) :
    toSphere (reciprocalParam w) = infinityParametrization w := by
  simp [reciprocalParam, vectorToSphere, infinityParametrization, one_div]

private def fromSphere : RiemannSphere → ComplexProjectiveLine :=
  fun p => OnePoint.elim p (reciprocalParam 0) finiteParam

private theorem fromSphere_toSphere (p : ComplexProjectiveLine) :
    fromSphere (toSphere p) = p := by
  induction p using Projectivization.ind with | h v hv =>
  change fromSphere (vectorToSphere ⟨v, hv⟩) = _
  by_cases h : v.1 = 0
  · have h2 : v.2 ≠ 0 := by
      intro hh
      exact hv (Prod.ext h hh)
    simp only [vectorToSphere, h, ite_eq_left, fromSphere, sphereInfty, OnePoint.elim_infty]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨v.2⁻¹, ?_⟩
    ext <;> simp [h, h2]
  · simp only [vectorToSphere, h, ite_false, fromSphere, sphereFinite, OnePoint.elim_some]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨v.1⁻¹, ?_⟩
    ext <;> simp [h, div_eq_mul_inv, mul_comm]

private theorem toSphere_fromSphere (p : RiemannSphere) :
    toSphere (fromSphere p) = p := by
  induction p using OnePoint.rec with
  | infty => simp [fromSphere, toSphere_reciprocalParam, infinityParametrization, sphereInfty]
  | coe z => exact toSphere_finiteParam z

private def sphereEquiv : ComplexProjectiveLine ≃ RiemannSphere where
  toFun := toSphere
  invFun := fromSphere
  left_inv := fromSphere_toSphere
  right_inv := toSphere_fromSphere

theorem projection_quotient : Topology.IsQuotientMap projection :=
  isQuotientMap_quotient_mk'

private theorem continuous_projection : Continuous projection :=
  projection_quotient.continuous

private theorem continuous_finiteParam : Continuous finiteParam := by
  exact continuous_projection.comp (by fun_prop)

private theorem continuous_reciprocalParam : Continuous reciprocalParam := by
  exact continuous_projection.comp (by fun_prop)

private theorem vectorToSphere_reciprocal (v : HomogeneousVector) (h : v.val.2 ≠ 0) :
    vectorToSphere v = infinityParametrization (v.val.1 / v.val.2) := by
  by_cases h1 : v.val.1 = 0
  · simp [vectorToSphere, infinityParametrization, h1, sphereInfty]
  · simp [vectorToSphere, infinityParametrization, h1, div_ne_zero h1 h, inv_div]

private theorem continuous_vectorToSphere : Continuous vectorToSphere := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hc1 : Continuous (fun u : HomogeneousVector => u.val.1) := by fun_prop
  have hc2 : Continuous (fun u : HomogeneousVector => u.val.2) := by fun_prop
  by_cases h1 : v.val.1 = 0
  · have h2 : v.val.2 ≠ 0 := fun h2 => v.property (Prod.ext h1 h2)
    have hc := continuous_infinityParametrization.continuousAt.comp
      (hc1.continuousAt.div hc2.continuousAt h2)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hc2.continuousAt.eventually_ne h2] with u hu
    exact vectorToSphere_reciprocal u hu
  · have hc := continuous_sphereFinite.continuousAt.comp
      (hc2.continuousAt.div hc1.continuousAt h1)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hc1.continuousAt.eventually_ne h1] with u hu
    simp [vectorToSphere, hu]

private theorem continuous_toSphere : Continuous toSphere :=
  projection_quotient.continuous_iff.mpr continuous_vectorToSphere

private theorem fromSphere_infinityParametrization (w : ℂ) :
    fromSphere (infinityParametrization w) = reciprocalParam w := by
  apply sphereEquiv.injective
  exact (toSphere_fromSphere _).trans (toSphere_reciprocalParam w).symm

private theorem continuous_fromSphere : Continuous fromSphere := by
  apply continuous_iff_continuousAt.mpr
  intro p
  induction p using OnePoint.rec with
  | coe z => exact OnePoint.continuousAt_coe.mpr continuous_finiteParam.continuousAt
  | infty =>
    have hc := continuous_reciprocalParam.continuousAt.comp
      continuousAt_infinityCoordinate_infty
    apply hc.congr_of_eventuallyEq
    filter_upwards [infinityChart_homeomorph.1.mem_nhds
      (show sphereInfty ∈ infinityChart.source from OnePoint.infty_ne_coe 0)] with p hp
    calc
      fromSphere p = fromSphere (infinityParametrization (infinityCoordinate p)) :=
        congrArg fromSphere (infinityChart.left_inv hp).symm
      _ = _ := fromSphere_infinityParametrization _

/-- The homeomorphism is proved for the scalar-orbit quotient topology. -/
private def sphereHomeomorph : ComplexProjectiveLine ≃ₜ RiemannSphere where
  toEquiv := sphereEquiv
  continuous_toFun := continuous_toSphere
  continuous_invFun := continuous_fromSphere

open Surfaces

private def sphereOpenChart (c : SphereCoordinate) : OpenPartialHomeomorph RiemannSphere ℂ :=
  match c with
  | .finite =>
    { toPartialEquiv := finiteChart
      continuousOn_toFun := continuousOn_finiteCoordinate
      continuousOn_invFun := continuous_sphereFinite.continuousOn
      open_source := finiteChart_homeomorph.1
      open_target := isOpen_univ }
  | .reciprocal =>
    { toPartialEquiv := infinityChart
      continuousOn_toFun := continuousOn_infinityCoordinate
      continuousOn_invFun := continuous_infinityParametrization.continuousOn
      open_source := infinityChart_homeomorph.1
      open_target := isOpen_univ }

private theorem sphereOpenChart_partialEquiv (c : SphereCoordinate) :
    (sphereOpenChart c).toPartialEquiv = sphereCoordinate c := by cases c <;> rfl

private def projectiveChart (c : SphereCoordinate) : ComplexChart ComplexProjectiveLine := by
  refine ⟨sphereHomeomorph.toOpenPartialHomeomorph.trans (sphereOpenChart c), ?_⟩
  have ht : (sphereHomeomorph.toOpenPartialHomeomorph.trans (sphereOpenChart c)).target = univ := by
    cases c <;> simp [sphereOpenChart, finiteChart,
      infinityChart, Homeomorph.toOpenPartialHomeomorph, Homeomorph.toOpenPartialHomeomorphOfImageEq]
  rw [ht]
  exact ⟨Set.univ_nonempty, isOpen_univ, isPreconnected_univ⟩

private theorem projectiveChart_partialEquiv (c : SphereCoordinate) :
    (projectiveChart c).val.toPartialEquiv =
      sphereHomeomorph.toEquiv.toPartialEquiv.trans (sphereCoordinate c) := by
  simp only [projectiveChart, OpenPartialHomeomorph.trans_toPartialEquiv,
    sphereOpenChart_partialEquiv]
  rfl

private theorem projectiveChart_apply (c : SphereCoordinate) (p : ComplexProjectiveLine) :
    (projectiveChart c).val p = sphereCoordinate c (sphereHomeomorph p) := by
  cases c <;> rfl

private theorem projectiveChart_symm_apply (c : SphereCoordinate) (z : ℂ) :
    (projectiveChart c).val.symm z = sphereHomeomorph.symm ((sphereCoordinate c).symm z) := by
  cases c <;> rfl

private theorem projectiveChart_source (c : SphereCoordinate) :
    (projectiveChart c).val.source = sphereHomeomorph ⁻¹' (sphereCoordinate c).source := by
  rw [show (projectiveChart c).val.source =
    ((projectiveChart c).val.toPartialEquiv).source from rfl,
    projectiveChart_partialEquiv, PartialEquiv.trans_source]
  simp

private theorem projectiveChart_target (c : SphereCoordinate) :
    (projectiveChart c).val.target = univ := by
  rw [show (projectiveChart c).val.target =
    ((projectiveChart c).val.toPartialEquiv).target from rfl,
    projectiveChart_partialEquiv, PartialEquiv.trans_target]
  cases c <;> simp [sphereCoordinate, finiteChart, infinityChart]

private theorem projectiveChart_transition (c d : SphereCoordinate) (z : ℂ) :
    (projectiveChart d).val ((projectiveChart c).val.symm z) =
      sphereCoordinate d ((sphereCoordinate c).symm z) := by
  rw [projectiveChart_apply, projectiveChart_symm_apply, sphereHomeomorph.apply_symm_apply]

private theorem projectiveChart_compatible (c d : SphereCoordinate) :
    CompatibleCharts (projectiveChart c) (projectiveChart d) := by
  let t := (projectiveChart c).val.symm.trans (projectiveChart d).val
  change BiholomorphicPair t.source t.target t t.symm
  refine ⟨⟨t.open_source, ?_⟩, ⟨t.open_target, ?_⟩,
    t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩
  · intro z hz
    have hzc : z ∈ (sphereCoordinate c).target := by
      cases c <;> trivial
    have hzd : (sphereCoordinate c).symm z ∈ (sphereCoordinate d).source := by
      have hz' : (projectiveChart c).val.symm z ∈ (projectiveChart d).val.source := hz.2
      rw [projectiveChart_source, mem_preimage, projectiveChart_symm_apply,
        sphereHomeomorph.apply_symm_apply] at hz'
      exact hz'
    have h := sphereCoordinate_transition c d ((sphereCoordinate c).symm z)
      ((sphereCoordinate c).map_target hzc) hzd
    rw [(sphereCoordinate c).right_inv hzc] at h
    have he : (t : ℂ → ℂ) = (fun z => sphereCoordinate d ((sphereCoordinate c).symm z)) :=
      funext (projectiveChart_transition c d)
    rw [he]
    exact h.differentiableAt
  · intro z hz
    have hzd : z ∈ (sphereCoordinate d).target := by cases d <;> trivial
    have hzc : (sphereCoordinate d).symm z ∈ (sphereCoordinate c).source := by
      have hz' : (projectiveChart d).val.symm z ∈ (projectiveChart c).val.source := hz.2
      rw [projectiveChart_source, mem_preimage, projectiveChart_symm_apply,
        sphereHomeomorph.apply_symm_apply] at hz'
      exact hz'
    have h := sphereCoordinate_transition d c ((sphereCoordinate d).symm z)
      ((sphereCoordinate d).map_target hzd) hzc
    rw [(sphereCoordinate d).right_inv hzd] at h
    have he : (t.symm : ℂ → ℂ) =
        (fun z => sphereCoordinate c ((sphereCoordinate d).symm z)) :=
      funext (projectiveChart_transition d c)
    rw [he]
    exact h.differentiableAt

private theorem projectiveChart_cover (p : ComplexProjectiveLine) :
    ∃ c : SphereCoordinate, p ∈ (projectiveChart c).val.source := by
  by_cases hp : sphereHomeomorph p = sphereInfty
  · refine ⟨.reciprocal, ?_⟩
    rw [projectiveChart_source]
    change sphereHomeomorph p ∈ infinityChart.source
    rw [hp]
    exact OnePoint.infty_ne_coe 0
  · exact ⟨.finite, by rw [projectiveChart_source]; exact hp⟩

private theorem projective_secondCountable : SecondCountableTopology ComplexProjectiveLine := by
  let c : Bool → SphereCoordinate := fun b => if b then .finite else .reciprocal
  let U : Bool → Set ComplexProjectiveLine := fun b => (projectiveChart (c b)).val.source
  let : ∀ b, SecondCountableTopology (U b) := fun b =>
    (projectiveChart (c b)).val.secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
    (fun b => (projectiveChart (c b)).val.open_source)
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨d, hd⟩ := projectiveChart_cover p
  cases d
  · exact ⟨true, hd⟩
  · exact ⟨false, hd⟩

private theorem projective_isAtlas :
    IsAtlas {projectiveChart .finite, projectiveChart .reciprocal} := by
  constructor
  · intro p
    obtain ⟨c, hc⟩ := projectiveChart_cover p
    refine ⟨projectiveChart c, ?_, hc⟩
    cases c <;> simp
  · intro e he f hf
    simp only [mem_insert_iff, mem_singleton_iff] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
      exact projectiveChart_compatible _ _

private def projectiveSurface : RiemannSurface ComplexProjectiveLine where
  connected := sphereHomeomorph.symm.surjective.connectedSpace sphereHomeomorph.symm.continuous
  hausdorff := sphereHomeomorph.symm.t2Space
  secondCountable := projective_secondCountable
  atlas := {projectiveChart .finite, projectiveChart .reciprocal}
  isAtlas := projective_isAtlas

/-- The projective line, with its literal quotient topology, is a compact
Riemann surface, and [1:z] ↔ z and [w:1] ↔ 1/w give its biholomorphic
homeomorphism to the previously constructed sphere. -/
theorem projective_line : Specs.D12Complex.Ch20.ProjectiveLine.projective_line_type := by
  refine ⟨projection_quotient, sphereHomeomorph.symm.compactSpace,
    sphereHomeomorph, projectiveSurface,
    projectiveChart .finite, projectiveChart .reciprocal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl,
    projectiveChart_partialEquiv .finite, projectiveChart_partialEquiv .reciprocal,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact toSphere_projection v
  · exact toSphere_finiteParam
  · exact toSphere_reciprocalParam
  · intro z
    constructor
    · rw [projectiveChart_apply]
      change finiteCoordinate (toSphere (finiteParam z)) = z
      rw [toSphere_finiteParam]
      rfl
    · rw [projectiveChart_symm_apply]
      rfl
  · intro w
    constructor
    · rw [projectiveChart_apply]
      change infinityCoordinate (toSphere (reciprocalParam w)) = w
      rw [toSphere_reciprocalParam]
      exact infinityChart.right_inv (mem_univ w)
    · rw [projectiveChart_symm_apply]
      exact fromSphere_infinityParametrization w
  · ext v
    rw [projectiveChart_source]
    change (vectorToSphere v ≠ sphereInfty) ↔ v.val.1 ≠ 0
    by_cases h : v.val.1 = 0 <;> simp [vectorToSphere, h, sphereInfty, sphereFinite]
  · ext v
    rw [projectiveChart_source]
    change (vectorToSphere v ≠ sphereFinite 0) ↔ v.val.2 ≠ 0
    by_cases h : v.val.1 = 0
    · have h2 : v.val.2 ≠ 0 := fun h2 => v.property (Prod.ext h h2)
      simp [vectorToSphere, h, h2, sphereInfty, sphereFinite]
    · simp [vectorToSphere, h, sphereFinite, div_eq_zero_iff]
  · simpa only [projectiveChart_transition, sphereCoordinate] using sphere_chart_transition_biholomorphic
  · intro z hz
    rw [projectiveChart_transition]
    exact (sphere_chart_transition_formulas z hz).1
  · have he : (fun z => finiteCoordinate (sphereHomeomorph ((projectiveChart .finite).val.symm z))) =
        (fun z : ℂ => z) := by
      funext z
      rw [projectiveChart_symm_apply, sphereHomeomorph.apply_symm_apply]
      rfl
    rw [he]
    exact ⟨isOpen_univ, fun _ _ => differentiableAt_id⟩
  · have he : (fun w => infinityCoordinate (sphereHomeomorph ((projectiveChart .reciprocal).val.symm w))) =
        (fun w : ℂ => w) := by
      funext w
      rw [projectiveChart_symm_apply, sphereHomeomorph.apply_symm_apply]
      exact infinityChart.right_inv (mem_univ w)
    rw [he]
    exact ⟨isOpen_univ, fun _ _ => differentiableAt_id⟩
  · have he : (fun z => (projectiveChart .finite).val (sphereHomeomorph.symm (sphereFinite z))) =
        (fun z : ℂ => z) := by
      funext z
      rw [projectiveChart_apply, sphereHomeomorph.apply_symm_apply]
      rfl
    rw [he]
    exact ⟨isOpen_univ, fun _ _ => differentiableAt_id⟩
  · have he : (fun w => (projectiveChart .reciprocal).val
        (sphereHomeomorph.symm (infinityParametrization w))) = (fun w : ℂ => w) := by
      funext w
      rw [projectiveChart_apply, sphereHomeomorph.apply_symm_apply]
      exact infinityChart.right_inv (mem_univ w)
    rw [he]
    exact ⟨isOpen_univ, fun _ _ => differentiableAt_id⟩

end D12Complex.ProjectiveLine

/- Definition exports of the canonical quotient and its homogeneous sections. -/
namespace D12Complex.ProjectiveLine.Definitions
abbrev HomogeneousVector : Specs.D12Complex.Ch20.ProjectiveLine.HomogeneousVector_type :=
  D12Complex.ProjectiveLine.HomogeneousVector
abbrev ComplexProjectiveLine : Specs.D12Complex.Ch20.ProjectiveLine.ComplexProjectiveLine_type :=
  D12Complex.ProjectiveLine.ComplexProjectiveLine
abbrev projection : Specs.D12Complex.Ch20.ProjectiveLine.projection_type :=
  D12Complex.ProjectiveLine.projection
abbrev finiteParam : Specs.D12Complex.Ch20.ProjectiveLine.finiteParam_type :=
  D12Complex.ProjectiveLine.finiteParam
abbrev reciprocalParam : Specs.D12Complex.Ch20.ProjectiveLine.reciprocalParam_type :=
  D12Complex.ProjectiveLine.reciprocalParam
end D12Complex.ProjectiveLine.Definitions
