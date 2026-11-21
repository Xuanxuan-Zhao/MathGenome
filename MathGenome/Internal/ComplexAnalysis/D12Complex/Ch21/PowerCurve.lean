import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.PowerCurve
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.ProjectiveLine
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.MapsMultiplicity
import Mathlib.Tactic.FunProp
import Batteries.Tactic.OpenPrivate

open private projectiveSurface projectiveChart sphereHomeomorph
  projectiveChart_apply projectiveChart_symm_apply projectiveChart_source
  projectiveChart_target projectiveChart_cover projectiveChart_partialEquiv
  toSphere toSphere_finiteParam
  toSphere_reciprocalParam from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.ProjectiveLine

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.PowerCurve
open Surfaces ProjectiveLine

/-- The graph parametrization is a homeomorphism for the subspace topology. -/
def parameterHomeomorph (n : ℕ) : ℂ ≃ₜ AffineCurve n where
  toFun := parameter n
  invFun := coordinate n
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext p.property rfl
  continuous_toFun := by unfold parameter; fun_prop
  continuous_invFun := by unfold coordinate; fun_prop

/-- The global `w` chart, with inverse the polynomial graph. -/
def affineChart (n : ℕ) : ComplexChart (AffineCurve n) :=
  ⟨(parameterHomeomorph n).symm.toOpenPartialHomeomorph,
    by exact ⟨Set.univ_nonempty, isOpen_univ, isPreconnected_univ⟩⟩

@[simp] theorem affineChart_apply (n : ℕ) (p : AffineCurve n) :
    (affineChart n).val p = coordinate n p := rfl

@[simp] theorem affineChart_symm (n : ℕ) (t : ℂ) :
    (affineChart n).val.symm t = parameter n t := rfl

@[simp] theorem affineChart_source (n : ℕ) : (affineChart n).val.source = univ := rfl
@[simp] theorem affineChart_target (n : ℕ) : (affineChart n).val.target = univ := rfl

/-- The induced genuine Riemann surface on the literal affine subset. -/
def affineSurface (n : ℕ) : RiemannSurface (AffineCurve n) where
  connected := (parameterHomeomorph n).surjective.connectedSpace
    (parameterHomeomorph n).continuous
  hausdorff := inferInstance
  secondCountable := inferInstance
  atlas := {affineChart n}
  isAtlas := by
    constructor
    · intro p
      exact ⟨affineChart n, rfl, mem_univ p⟩
    · intro e he f hf
      have he' : e = affineChart n := he
      have hf' : f = affineChart n := hf
      subst e; subst f
      exact compatibleCharts_refl _

theorem affine_parameter : Specs.D12Complex.Ch21.PowerCurve.affine_parameter_type := by
  intro n
  refine ⟨parameterHomeomorph n, affineSurface n, affineChart n,
    fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact continuous_fst.comp continuous_subtype_val
    · intro e he
      have he' : e = affineChart n := he
      subst e
      exact ⟨isOpen_univ, fun t _ => differentiableAt_id.pow n⟩
  · constructor
    · exact (parameterHomeomorph n).symm.continuous
    · intro e he
      have he' : e = affineChart n := he
      subst e
      exact ⟨isOpen_univ, fun _ _ => differentiableAt_id⟩
  · intro t
    exact (hasDerivAt_pow n t).prodMk (hasDerivAt_id t)
  · intro t h
    have := congrArg Prod.snd h
    exact one_ne_zero this

/-- The affine graph is precisely the finite chart of its completion. -/
theorem inclusion_topology (n : ℕ) (e : ComplexProjectiveLine ≃ₜ RiemannSphere)
    (he : ∀ t : ℂ, e (finiteParam t) = sphereFinite t)
    (hinfty : e (reciprocalParam 0) = sphereInfty) :
    Topology.IsOpenEmbedding (inclusion n) ∧ DenseRange (inclusion n) ∧
      Set.range (inclusion n) = {reciprocalParam 0}ᶜ := by
  have hj : inclusion n = e.symm ∘ sphereFinite ∘ (parameterHomeomorph n).symm := by
    funext p
    apply e.injective
    change e (finiteParam p.val.2) = e (e.symm (sphereFinite p.val.2))
    rw [e.apply_symm_apply]
    exact he p.val.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hj]
    exact e.symm.isOpenEmbedding.comp
      (OnePoint.isOpenEmbedding_coe.comp (parameterHomeomorph n).symm.isOpenEmbedding)
  · rw [hj]
    exact e.symm.surjective.denseRange.comp
      (OnePoint.denseRange_coe.comp (parameterHomeomorph n).symm.surjective.denseRange
        OnePoint.continuous_coe) e.symm.continuous
  · ext p
    constructor
    · rintro ⟨q, rfl⟩ h
      have hh := congrArg e h
      rw [inclusion, he, hinfty] at hh
      exact OnePoint.coe_ne_infty _ hh
    · intro hp
      have hep : e p ≠ sphereInfty := by
        intro h
        exact hp (e.injective (h.trans hinfty.symm))
      obtain ⟨t, ht⟩ := OnePoint.ne_infty_iff_exists.mp hep
      refine ⟨parameter n t, ?_⟩
      apply e.injective
      exact (he t).trans ht



def spherePower (n : ℕ) : RiemannSphere → RiemannSphere := OnePoint.map (fun z : ℂ => z ^ n)

@[simp] theorem spherePower_finite (n : ℕ) (z : ℂ) :
    spherePower n (sphereFinite z) = sphereFinite (z ^ n) := rfl

@[simp] theorem spherePower_infty (n : ℕ) : spherePower n sphereInfty = sphereInfty := rfl

theorem spherePower_reciprocal (n : ℕ) (hn : 0 < n) (s : ℂ) :
    spherePower n (infinityParametrization s) = infinityParametrization (s ^ n) := by
  by_cases hs : s = 0
  · simp [hs, infinityParametrization, zero_pow (Nat.ne_of_gt hn)]
  · simp [infinityParametrization, hs, pow_ne_zero n hs, inv_pow]

theorem continuous_spherePower (n : ℕ) (hn : 0 < n) : Continuous (spherePower n) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  induction p using OnePoint.rec with
  | coe z =>
      exact OnePoint.continuousAt_coe.mpr
        (continuous_sphereFinite.comp (continuous_id.pow n)).continuousAt
  | infty =>
      have h := continuous_infinityParametrization.continuousAt.comp
        (continuousAt_infinityCoordinate_infty.pow n)
      apply h.congr_of_eventuallyEq
      filter_upwards [infinityChart_homeomorph.1.mem_nhds
        (show sphereInfty ∈ infinityChart.source from OnePoint.infty_ne_coe 0)] with p hp
      change spherePower n p = infinityParametrization (infinityCoordinate p ^ n)
      rw [← spherePower_reciprocal n hn]
      exact congrArg (spherePower n) (infinityChart.left_inv hp).symm

def projectivePower (n : ℕ) : ComplexProjectiveLine → ComplexProjectiveLine :=
  fun p => sphereHomeomorph.symm (spherePower n (sphereHomeomorph p))

@[simp] theorem projectivePower_finite (n : ℕ) (z : ℂ) :
    projectivePower n (finiteParam z) = finiteParam (z ^ n) := by
  apply sphereHomeomorph.injective
  simp only [projectivePower, Homeomorph.apply_symm_apply]
  change spherePower n (toSphere (finiteParam z)) = toSphere (finiteParam (z ^ n))
  rw [toSphere_finiteParam, toSphere_finiteParam]
  rfl

@[simp] theorem projectivePower_reciprocal (n : ℕ) (hn : 0 < n) (z : ℂ) :
    projectivePower n (reciprocalParam z) = reciprocalParam (z ^ n) := by
  apply sphereHomeomorph.injective
  simp only [projectivePower, Homeomorph.apply_symm_apply]
  change spherePower n (toSphere (reciprocalParam z)) = toSphere (reciprocalParam (z ^ n))
  rw [toSphere_reciprocalParam, toSphere_reciprocalParam]
  exact spherePower_reciprocal n hn z

theorem continuous_projectivePower (n : ℕ) (hn : 0 < n) : Continuous (projectivePower n) :=
  sphereHomeomorph.symm.continuous.comp ((continuous_spherePower n hn).comp sphereHomeomorph.continuous)

theorem projectivePower_coordinate (n : ℕ) (hn : 0 < n) (c : SphereCoordinate) (z : ℂ) :
    coordinateMap (projectiveChart c) (projectiveChart c) (projectivePower n) z = z ^ n := by
  rw [coordinateMap, projectiveChart_symm_apply, projectivePower,
    Homeomorph.apply_symm_apply, projectiveChart_apply, Homeomorph.apply_symm_apply]
  cases c
  · rfl
  · change infinityCoordinate (spherePower n (infinityParametrization z)) = z ^ n
    rw [spherePower_reciprocal n hn]
    exact infinityChart.right_inv (mem_univ _)

theorem projectivePower_preserves_chart (n : ℕ) (_hn : 0 < n) (c : SphereCoordinate)
    (p : ComplexProjectiveLine) (hc : p ∈ (projectiveChart c).val.source) :
    projectivePower n p ∈ (projectiveChart c).val.source := by
  rw [projectiveChart_source] at hc ⊢
  simp only [mem_preimage, projectivePower, Homeomorph.apply_symm_apply] at *
  cases c
  · change sphereHomeomorph p ≠ sphereInfty at hc
    change spherePower n (sphereHomeomorph p) ≠ sphereInfty
    generalize sphereHomeomorph p = q at hc ⊢
    induction q using OnePoint.rec with
    | infty => exact False.elim (hc rfl)
    | coe z => exact OnePoint.coe_ne_infty _
  · change sphereHomeomorph p ≠ sphereFinite 0 at hc
    change spherePower n (sphereHomeomorph p) ≠ sphereFinite 0
    generalize sphereHomeomorph p = q at hc ⊢
    induction q using OnePoint.rec with
    | infty => exact OnePoint.infty_ne_coe _
    | coe z =>
        have hz : z ≠ 0 := fun h => hc (congrArg sphereFinite h)
        exact fun h => pow_ne_zero n hz (OnePoint.coe_injective h)

theorem holomorphic_projectivePower (n : ℕ) (hn : 0 < n) :
    HolomorphicMap projectiveSurface projectiveSurface (projectivePower n) := by
  intro p
  refine ⟨(continuous_projectivePower n hn).continuousAt, ?_⟩
  obtain ⟨c, hc⟩ := projectiveChart_cover p
  refine ⟨projectiveChart c, ?_, projectiveChart c, ?_, hc, ?_, ?_⟩
  · cases c <;> simp [projectiveSurface]
  · cases c <;> simp [projectiveSurface]
  · exact projectivePower_preserves_chart n hn c p hc
  · have he : coordinateMap (projectiveChart c) (projectiveChart c) (projectivePower n) =
        (fun z : ℂ => z ^ n) := funext (projectivePower_coordinate n hn c)
    rw [he]
    exact ⟨univ, mem_univ _, isOpen_univ, fun _ _ => differentiableAt_id.pow n⟩

theorem projectivePower_chart_multiplicity (n : ℕ) (hn : 0 < n) (c : SphereCoordinate) :
    HasMultiplicity projectiveSurface projectiveSurface (projectivePower n)
      ((projectiveChart c).val.symm 0) n := by
  let a := (projectiveChart c).val.symm 0
  have hc : projectiveChart c ∈ projectiveSurface.atlas := by cases c <;> simp [projectiveSurface]
  have hcm := subset_maximalAtlas projectiveSurface.isAtlas hc
  have h0t : (0 : ℂ) ∈ (projectiveChart c).val.target := by rw [projectiveChart_target]; trivial
  have ha : a ∈ (projectiveChart c).val.source := (projectiveChart c).val.map_target h0t
  have hfa := projectivePower_preserves_chart n hn c a ha
  have hca : (projectiveChart c).val a = 0 := (projectiveChart c).val.right_inv h0t
  have hcfa : (projectiveChart c).val (projectivePower n a) = 0 := by
    change coordinateMap (projectiveChart c) (projectiveChart c) (projectivePower n) 0 = 0
    rw [projectivePower_coordinate n hn, zero_pow (Nat.ne_of_gt hn)]
  have horder : coordinateOrder (projectiveChart c) (projectiveChart c) (projectivePower n) a =
      (n : ℕ∞) := by
    unfold coordinateOrder
    rw [hca, hcfa]
    simp_rw [projectivePower_coordinate n hn, sub_zero]
    change analyticOrderAt ((id : ℂ → ℂ) ^ n) 0 = (n : ℕ∞)
    rw [analyticOrderAt_pow analyticAt_id]
    simp
  refine ⟨hn, ?_⟩
  intro e he d hd hea hdfa
  rw [coordinate_order_chart_independent projectiveSurface projectiveSurface (projectivePower n)
    a (holomorphic_projectivePower n hn a) e he d hd
    (projectiveChart c) hcm (projectiveChart c) hcm hea hdfa ha hfa]
  exact horder

theorem projectivePower_zero_multiplicity (n : ℕ) (hn : 0 < n) :
    HasMultiplicity projectiveSurface projectiveSurface (projectivePower n) (finiteParam 0) n := by
  convert projectivePower_chart_multiplicity n hn .finite using 1
  apply sphereHomeomorph.injective
  rw [projectiveChart_symm_apply, Homeomorph.apply_symm_apply]
  exact toSphere_finiteParam 0

theorem projectivePower_infty_multiplicity (n : ℕ) (hn : 0 < n) :
    HasMultiplicity projectiveSurface projectiveSurface (projectivePower n) (reciprocalParam 0) n := by
  convert projectivePower_chart_multiplicity n hn .reciprocal using 1
  apply sphereHomeomorph.injective
  rw [projectiveChart_symm_apply, Homeomorph.apply_symm_apply]
  exact toSphere_reciprocalParam 0

theorem projectivePower_nonconstant (n : ℕ) (hn : 0 < n) :
    ¬ ∃ b, ∀ p, projectivePower n p = b := by
  rintro ⟨b, hb⟩
  have h := (hb (finiteParam 0)).trans (hb (reciprocalParam 0)).symm
  rw [projectivePower_finite, projectivePower_reciprocal n hn,
    zero_pow (Nat.ne_of_gt hn)] at h
  have h' := congrArg sphereHomeomorph h
  change toSphere (finiteParam 0) = toSphere (reciprocalParam 0) at h'
  rw [toSphere_finiteParam, toSphere_reciprocalParam] at h'
  simp [infinityParametrization, sphereFinite, sphereInfty] at h'

theorem projectivePower_one_unramified :
    LocallyBiholomorphicAt projectiveSurface projectiveSurface (projectivePower 1) (finiteParam 0) ∧
    LocallyBiholomorphicAt projectiveSurface projectiveSurface (projectivePower 1) (reciprocalParam 0) := by
  constructor
  · exact (locally_biholomorphic_iff_multiplicity_one projectiveSurface projectiveSurface
      (projectivePower 1) (holomorphic_projectivePower 1 (by decide))
      (projectivePower_nonconstant 1 (by decide)) (finiteParam 0) 1
      (projectivePower_zero_multiplicity 1 (by decide))).mpr rfl
  · exact (locally_biholomorphic_iff_multiplicity_one projectiveSurface projectiveSurface
      (projectivePower 1) (holomorphic_projectivePower 1 (by decide))
      (projectivePower_nonconstant 1 (by decide)) (reciprocalParam 0) 1
      (projectivePower_infty_multiplicity 1 (by decide))).mpr rfl


theorem finite_chart_formulas (t : ℂ) :
    (projectiveChart .finite).val (finiteParam t) = t ∧
      (projectiveChart .finite).val.symm t = finiteParam t := by
  constructor
  · rw [projectiveChart_apply]
    change finiteCoordinate (toSphere (finiteParam t)) = t
    rw [toSphere_finiteParam]
    rfl
  · rw [projectiveChart_symm_apply]
    rfl

theorem reciprocal_chart_formulas (s : ℂ) :
    (projectiveChart .reciprocal).val (reciprocalParam s) = s ∧
      (projectiveChart .reciprocal).val.symm s = reciprocalParam s := by
  constructor
  · rw [projectiveChart_apply]
    change infinityCoordinate (toSphere (reciprocalParam s)) = s
    rw [toSphere_reciprocalParam]
    exact infinityChart.right_inv (mem_univ s)
  · apply sphereHomeomorph.injective
    rw [projectiveChart_symm_apply, Homeomorph.apply_symm_apply]
    exact (toSphere_reciprocalParam s).symm

theorem inclusion_in_chart (n : ℕ) (p : AffineCurve n) :
    inclusion n p ∈ (projectiveChart .finite).val.source := by
  rw [projectiveChart_source]
  change toSphere (finiteParam p.val.2) ≠ sphereInfty
  rw [toSphere_finiteParam]
  exact OnePoint.coe_ne_infty _

theorem inclusion_coordinate (n : ℕ) :
    coordinateMap (affineChart n) (projectiveChart .finite) (inclusion n) = id := by
  funext t
  exact (finite_chart_formulas t).1

theorem holomorphic_inclusion (n : ℕ) :
    HolomorphicMap (affineSurface n) projectiveSurface (inclusion n) := by
  intro p
  have hj := (inclusion_topology n sphereHomeomorph toSphere_finiteParam
    (by
      change toSphere (reciprocalParam 0) = sphereInfty
      rw [toSphere_reciprocalParam]
      simp [infinityParametrization])).1
  refine ⟨hj.continuous.continuousAt, affineChart n, rfl,
    projectiveChart .finite, by simp [projectiveSurface], mem_univ p,
    inclusion_in_chart n p, ?_⟩
  rw [inclusion_coordinate]
  exact ⟨univ, mem_univ _, isOpen_univ, fun _ _ => differentiableAt_id⟩

theorem locally_biholomorphic_inclusion (n : ℕ) (p : AffineCurve n) :
    LocallyBiholomorphicAt (affineSurface n) projectiveSurface (inclusion n) p := by
  refine ⟨affineChart n, rfl, projectiveChart .finite, by simp [projectiveSurface],
    mem_univ p, inclusion_in_chart n p, univ, univ, id, mem_univ _, ?_, ?_, ?_⟩
  · intro t _
    exact ⟨mem_univ t, inclusion_in_chart n ((affineChart n).val.symm t)⟩
  · rw [projectiveChart_target]
  · rw [inclusion_coordinate]
    exact ⟨⟨isOpen_univ, fun _ _ => differentiableAt_id⟩,
      ⟨isOpen_univ, fun _ _ => differentiableAt_id⟩,
      fun _ _ => mem_univ _, fun _ _ => mem_univ _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem compact_completion : Specs.D12Complex.Ch21.PowerCurve.compact_completion_type := by
  intro n hn
  refine ⟨affineSurface n, affineChart n, projectiveSurface,
    projectiveChart .finite, projectiveChart .reciprocal, sphereHomeomorph,
    projectivePower n, sphereHomeomorph.symm.compactSpace, rfl, rfl, rfl,
    fun _ => rfl, fun _ => rfl, rfl, projectiveChart_partialEquiv .finite,
    projectiveChart_partialEquiv .reciprocal, toSphere_finiteParam,
    toSphere_reciprocalParam, finite_chart_formulas, reciprocal_chart_formulas, ?_⟩
  obtain ⟨hj, hd, hr⟩ := inclusion_topology n sphereHomeomorph toSphere_finiteParam
    (by
      change toSphere (reciprocalParam 0) = sphereInfty
      rw [toSphere_reciprocalParam]
      simp [infinityParametrization])
  refine ⟨hj, hd, hr, holomorphic_inclusion n, locally_biholomorphic_inclusion n,
    holomorphic_projectivePower n hn, ?_, projectivePower_finite n,
    projectivePower_reciprocal n hn, projectivePower_zero_multiplicity n hn,
    projectivePower_infty_multiplicity n hn, ?_⟩
  · intro p
    change projectivePower n (finiteParam p.val.2) = finiteParam p.val.1
    rw [projectivePower_finite, p.property]
  · intro h
    subst n
    exact projectivePower_one_unramified

end D12Complex.PowerCurve

/- Candidate exports of the canonical objects shared with the independent Spec. -/
namespace D12Complex.PowerCurve.Definitions

abbrev AffineCurve : Specs.D12Complex.Ch21.PowerCurve.AffineCurve_type :=
  D12Complex.PowerCurve.AffineCurve

abbrev parameter : Specs.D12Complex.Ch21.PowerCurve.parameter_type :=
  D12Complex.PowerCurve.parameter

abbrev coordinate : Specs.D12Complex.Ch21.PowerCurve.coordinate_type :=
  D12Complex.PowerCurve.coordinate

abbrev inclusion : Specs.D12Complex.Ch21.PowerCurve.inclusion_type :=
  D12Complex.PowerCurve.inclusion

end D12Complex.PowerCurve.Definitions
