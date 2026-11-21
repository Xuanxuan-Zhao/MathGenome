import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.MintyBrowder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Monotone.FiniteDimensionalGalerkin
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14BallCharacterization

noncomputable section
open Set Filter Topology
namespace ExpandedFA.Monotone.MintyBrowder
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Weak compactness turns simultaneous finite-dimensional Galerkin solutions
into a point satisfying every Minty half-space. The finite intersection argument
works without a countability or separability assumption. -/
theorem exists_solution_of_uniformGalerkin
    (hr : ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X)
    (A : X → X →L[ℝ] ℝ) (hh : Hemicontinuous X A) (hm : MonotoneMap X A)
    (f : X →L[ℝ] ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hgal : ∀ (E : Submodule ℝ X) [FiniteDimensional ℝ E],
      ∃ x : E, ‖x‖ ≤ R ∧ ∀ v : E, (A (x : X) - f) (v : X) = 0) :
    ∃ x : X, A x = f := by
  let K : Set X := {x | ‖x‖ ≤ R}
  let S : X → Set X := fun y => {x | (f - A y) y ≤ (f - A y) x}
  have hfinite (s : Finset X) : (K ∩ ⋂ y ∈ s, S y).Nonempty := by
    let E := Submodule.span ℝ (s : Set X)
    obtain ⟨x, hx, he⟩ := hgal E
    refine ⟨(x : X), hx, ?_⟩
    simp only [mem_iInter]
    intro y hy
    have hyE : y ∈ E := Submodule.subset_span hy
    have hz := he (x - ⟨y, hyE⟩)
    have hp := hm (x : X) y
    change (f - A y) y ≤ (f - A y) x
    simp only [Submodule.coe_sub, sub_apply, map_sub] at hz hp ⊢
    linarith
  have hc := ExpandedFA.P1.C14BallCharacterization.reflexive_weakCompact_norm_ball
    ℝ X hr R hR
  let B := topDualPairing ℝ X
  let : TopologicalSpace X := ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue
    ℝ X (X →L[ℝ] ℝ) (topDualPairing ℝ X)
  have hclosed (y : X) : IsClosed (S y) := by
    have he : Continuous (fun x : X => (f - A y) x) := by
      change @Continuous (WeakBilin B.flip) ℝ
        (TopologicalSpace.induced id (WeakBilin.instTopologicalSpace B.flip)) _ _
      rw [induced_id]
      exact WeakBilin.eval_continuous B.flip (f - A y)
    exact isClosed_le continuous_const he
  obtain ⟨x, _, hx⟩ := hc.inter_iInter_nonempty S hclosed hfinite
  refine ⟨x, ?_⟩
  apply (Galerkin.eq_of_monotonically_related A hh x f ?_).symm
  intro y
  have hp := mem_iInter.mp hx y
  change (f - A y) y ≤ (f - A y) x at hp
  simpa only [map_sub, sub_nonneg] using hp

/-- Strict monotonicity alone gives injectivity. -/
theorem injective_of_strictMonotone (A : X → X →L[ℝ] ℝ)
    (hs : StrictMonotoneMap X A) : Function.Injective A := by
  intro x y hxy
  by_contra hn
  have hp := hs x y hn
  rw [hxy, sub_self, zero_apply] at hp
  exact lt_irrefl 0 hp

theorem surjectivity : Spec.Surjectivity.{u} := by
  intro X _ _ _ hr A hb hh hm hc f
  obtain ⟨R, hR, hgal⟩ := Galerkin.uniformGalerkin X A hb hh hm hc f
  exact exists_solution_of_uniformGalerkin hr A hh hm f R hR.le hgal

theorem uniqueSolvability : Spec.UniqueSolvability.{u} := by
  intro X _ _ _ hr A hb hh hs hc f
  have hm := strictMonotoneMap_monotone X A hs
  obtain ⟨x, hx⟩ := surjectivity X hr A hb hh hm hc f
  exact ⟨x, hx, fun y hy => injective_of_strictMonotone A hs (hy.trans hx.symm)⟩

/-- For a norm-continuous operator, all finite-dimensional residual maps are
continuous directly. Thus this specialization needs no extra global boundedness
assumption on images of bounded sets. -/
theorem continuousUniqueSolvability : Spec.ContinuousUniqueSolvability.{u} := by
  intro X _ _ _ hr A hcont hs hc f
  have hh : Hemicontinuous X A := by
    intro x y z
    exact (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hm := strictMonotoneMap_monotone X A hs
  obtain ⟨R, hR, hout⟩ := Galerkin.coercive_outward_radius X A hc f
  have hgal (E : Submodule ℝ X) [FiniteDimensional ℝ E] :
      ∃ x : E, ‖x‖ ≤ R ∧ ∀ v : E, (A (x : X) - f) (v : X) = 0 := by
    let B : E → E →L[ℝ] ℝ := fun x => (A (x : X) - f).comp E.subtypeL
    have hB : Continuous B :=
      ((hcont.comp E.subtypeL.continuous).sub continuous_const).clm_comp continuous_const
    have houtE (x : E) (hx : ‖x‖ = R) : 0 < B x x :=
      hout x (show R ≤ ‖(x : X)‖ from hx.ge)
    obtain ⟨x, hx, hz⟩ := Galerkin.exists_zero_of_outward B hB R hR houtE
    refine ⟨x, hx, ?_⟩
    intro v
    exact congrArg (fun g : E →L[ℝ] ℝ => g v) hz
  obtain ⟨x, hx⟩ := exists_solution_of_uniformGalerkin hr A hh hm f R hR.le hgal
  exact ⟨x, hx, fun y hy => injective_of_strictMonotone A hs (hy.trans hx.symm)⟩

end ExpandedFA.Monotone.MintyBrowder
