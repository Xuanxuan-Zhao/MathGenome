import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.FiniteDimensionalGalerkin
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Monotone.Definitions
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Maps.Proper.Basic
import MathGenome.PointSetTopology.Topics.D10Topology.Ch17
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
namespace ExpandedFA.Monotone.Galerkin
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The hemicontinuous Minty argument: a pair related to every graph point
already belongs to the graph. Only scalar limits along lines are used. -/
theorem eq_of_monotonically_related (A : X → X →L[ℝ] ℝ)
    (hA : Hemicontinuous X A) (x : X) (g : X →L[ℝ] ℝ)
    (h : ∀ y, 0 ≤ (g - A y) (x - y)) : g = A x := by
  have hle (z : X) : g z ≤ A x z := by
    have ht : Tendsto (fun t : ℝ => A (x + t • z) z) (𝓝[>] 0) (𝓝 (A x z)) := by
      simpa using ((hA x z z).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t htpos
    have hp := h (x + t • z)
    have he : x - (x + t • z) = (-t) • z := by simp
    rw [he, map_smul] at hp
    change 0 ≤ -t * (g z - A (x + t • z) z) at hp
    have : 0 < t := htpos
    nlinarith
  ext z
  have hneg := hle (-z)
  simp only [map_neg] at hneg
  exact le_antisymm (hle z) (by linarith)

/-- The graph is an intersection of closed monotonicity half-spaces. -/
theorem isClosed_graph (A : X → X →L[ℝ] ℝ)
    (hA : Hemicontinuous X A) (hm : MonotoneMap X A) : IsClosed (Function.graph A) := by
  have heq : Function.graph A =
      ⋂ y : X, {p : X × (X →L[ℝ] ℝ) | 0 ≤ (p.2 - A y) (p.1 - y)} := by
    ext ⟨x, g⟩
    simp only [Function.mem_graph, mem_iInter, mem_ofPred_eq]
    constructor
    · intro hg
      subst g
      exact hm x
    · intro h
      exact (eq_of_monotonically_related A hA x g h).symm
  rw [heq]
  apply isClosed_iInter
  intro y
  exact isClosed_le continuous_const
    ((continuous_snd.sub continuous_const).clm_apply (continuous_fst.sub continuous_const))

/-- Local boundedness plus the closed graph gives continuity in finite dimension.
The compact-codomain closed graph theorem is applied on each closed norm ball. -/
theorem continuous_of_finiteDimensional [FiniteDimensional ℝ X]
    (A : X → X →L[ℝ] ℝ) (hb : BoundedOnBoundedSets X A)
    (hh : Hemicontinuous X A) (hm : MonotoneMap X A) : Continuous A := by
  have hg := isClosed_graph A hh hm
  rw [continuous_iff_continuousAt]
  intro x
  let D : Set X := Metric.closedBall 0 (‖x‖ + 1)
  obtain ⟨C, hC⟩ := (hb D Metric.isBounded_closedBall).exists_norm_le
  let K : Set (X →L[ℝ] ℝ) := Metric.closedBall 0 C
  have him (y : D) : A y ∈ K := by
    simpa only [K, Metric.mem_closedBall, dist_zero_right] using hC (A y) ⟨y, y.2, rfl⟩
  let B : D → K := fun y => ⟨A y, him y⟩
  have hK : IsCompact K := isCompact_closedBall 0 C
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hB : Continuous B := by
    apply continuous_of_isClosed_graph
    have hc : Continuous (fun p : D × K => ((p.1 : X), (p.2 : X →L[ℝ] ℝ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    convert hg.preimage hc using 1
    ext p
    simp only [Function.mem_graph, mem_preimage, B]
    exact Subtype.ext_iff
  have hres : ContinuousOn A D := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_subtype_val.comp hB
  apply (hres x ?_).continuousAt
  · apply Metric.closedBall_mem_nhds_of_mem
    simp
  · simp [D]

/-- Restriction of a dual functional does not increase its operator norm. -/
theorem norm_restriction_le (E : Submodule ℝ X) (A : X → X →L[ℝ] ℝ) (x : E) :
    ‖restriction E A x‖ ≤ ‖A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (A x).le_opNorm (v : X)

theorem restriction_bounded (E : Submodule ℝ X) (A : X → X →L[ℝ] ℝ)
    (hb : BoundedOnBoundedSets X A) : BoundedOnBoundedSets E (restriction E A) := by
  intro D hD
  have hi := E.subtypeL.lipschitzWith.isBounded_image hD
  obtain ⟨C, hC⟩ := (hb _ hi).exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (norm_restriction_le E A x).trans (hC _ ⟨x, ⟨x, hx, rfl⟩, rfl⟩)

theorem restriction_hemicontinuous (E : Submodule ℝ X) (A : X → X →L[ℝ] ℝ)
    (hh : Hemicontinuous X A) : Hemicontinuous E (restriction E A) := by
  intro x y z
  simpa only [restriction, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.coe_add, Submodule.coe_smul] using hh (x : X) (y : X) (z : X)

theorem restriction_monotone (E : Submodule ℝ X) (A : X → X →L[ℝ] ℝ)
    (hm : MonotoneMap X A) : MonotoneMap E (restriction E A) := by
  intro x y
  exact hm x y

theorem finiteRestriction_continuous : Spec.FiniteRestrictionContinuous.{u} := by
  intro X _ _ A hb hh hm E _
  exact continuous_of_finiteDimensional (restriction E A) (restriction_bounded E A hb)
    (restriction_hemicontinuous E A hh) (restriction_monotone E A hm)

theorem coercive_outward_radius : Spec.CoerciveOutwardRadius.{u} := by
  intro X _ _ A hc f
  obtain ⟨r, hr⟩ := (coercive_iff X A).mp hc (‖f‖ + 1)
  refine ⟨max r 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  have hp : 0 < ‖x‖ := lt_of_lt_of_le
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hx
  have hg := hr x ((le_max_left _ _).trans hx)
  have hg' := (le_div_iff₀ hp).mp hg
  have hf : f x ≤ ‖f‖ * ‖x‖ := (le_abs_self _).trans (f.le_opNorm x)
  change 0 < A x x - f x
  nlinarith

/-- Coordinates of a functional, interpreted as a vector in an arbitrary basis.
This supplies the Euclidean dual identification without altering the given norm. -/
def dualVector [FiniteDimensional ℝ X] (g : X →L[ℝ] ℝ) : X :=
  ∑ i, g (Module.finBasis ℝ X i) • Module.finBasis ℝ X i

theorem continuous_dualVector [FiniteDimensional ℝ X] :
    Continuous (dualVector : (X →L[ℝ] ℝ) → X) := by
  unfold dualVector
  apply continuous_finsetSum
  intro i _
  exact (continuous_id.clm_apply continuous_const).smul continuous_const

theorem dualVector_eq_zero_iff [FiniteDimensional ℝ X] (g : X →L[ℝ] ℝ) :
    dualVector g = 0 ↔ g = 0 := by
  constructor
  · intro h
    have he (i : Fin (Module.finrank ℝ X)) : g (Module.finBasis ℝ X i) = 0 := by
      have hp := congrArg (fun v => (Module.finBasis ℝ X).repr v i) h
      simpa only [dualVector, Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] using hp
    have hlin : g.toLinearMap = 0 := (Module.finBasis ℝ X).ext he
    ext v
    exact congrArg (fun l : X →ₗ[ℝ] ℝ => l v) hlin
  · rintro rfl
    simp [dualVector]

theorem dualVector_pairing_nonneg [FiniteDimensional ℝ X] (g : X →L[ℝ] ℝ) :
    0 ≤ g (dualVector g) := by
  simp only [dualVector, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

/-- Brouwer's outward-pointing zero lemma, with the original norm and with
no positive-dimension hypothesis. The fixed point theorem is used on the
nonempty compact convex closed ball itself. -/
theorem exists_zero_of_outward [FiniteDimensional ℝ X]
    (B : X → X →L[ℝ] ℝ) (hB : Continuous B) (R : ℝ) (hR : 0 < R)
    (hout : ∀ x : X, ‖x‖ = R → 0 < B x x) :
    ∃ x : X, ‖x‖ ≤ R ∧ B x = 0 := by
  by_contra! hn
  let K : Set X := Metric.closedBall 0 R
  have hne (x : K) : dualVector (B x) ≠ 0 := by
    apply mt (dualVector_eq_zero_iff (B x)).mp
    exact hn x (by simpa only [K, Metric.mem_closedBall, dist_zero_right] using x.2)
  let T₀ : K → X := fun x => (-R / ‖dualVector (B x)‖) • dualVector (B x)
  have hnorm (x : K) : ‖T₀ x‖ = R := by
    have hp : 0 < ‖dualVector (B x)‖ := norm_pos_iff.mpr (hne x)
    dsimp only [T₀]
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hR, abs_of_pos hp]
    exact div_mul_cancel₀ R (ne_of_gt hp)
  have hmem (x : K) : T₀ x ∈ K := by
    simpa only [K, Metric.mem_closedBall, dist_zero_right, hnorm] using (le_refl R)
  let T : K → K := fun x => ⟨T₀ x, hmem x⟩
  have hT : Continuous T := by
    have hc : Continuous (fun x : K => dualVector (B x)) :=
      continuous_dualVector.comp (hB.comp continuous_subtype_val)
    exact ((continuous_const.div hc.norm (fun x => norm_ne_zero_iff.mpr (hne x))).smul hc).subtype_mk hmem
  obtain ⟨x, hx⟩ := D10Topology.Ch17.brouwer_finiteDimensional X K
    (Metric.nonempty_closedBall.mpr hR.le) (isCompact_closedBall 0 R)
    (convex_closedBall 0 R) T hT
  have hfix : T₀ x = (x : X) := congrArg Subtype.val hx
  have hxR : ‖(x : X)‖ = R := by rw [← hfix]; exact hnorm x
  have hp := hout x hxR
  have hnp : B x (T₀ x) ≤ 0 := by
    dsimp only [T₀]
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hR.le) (norm_nonneg _))
      (dualVector_pairing_nonneg (B x))
  rw [hfix] at hnp
  exact (not_lt_of_ge hnp) hp

/-- One radius works simultaneously for every finite-dimensional subspace,
including the zero subspace. -/
theorem uniformGalerkin : Spec.UniformGalerkin.{u} := by
  intro X _ _ A hb hh hm hc f
  obtain ⟨R, hR, hout⟩ := coercive_outward_radius X A hc f
  refine ⟨R, hR, ?_⟩
  intro E _
  let B : E → E →L[ℝ] ℝ := fun x => restriction E A x - f.comp E.subtypeL
  have hB : Continuous B :=
    (finiteRestriction_continuous X A hb hh hm E).sub continuous_const
  have hBE : ∀ x : E, ‖x‖ = R → 0 < B x x := by
    intro x hx
    exact hout x (by change R ≤ ‖x‖; exact hx.ge)
  obtain ⟨x, hx, hz⟩ := exists_zero_of_outward B hB R hR hBE
  refine ⟨x, hx, ?_⟩
  intro v
  have he := congrArg (fun g : E →L[ℝ] ℝ => g v) hz
  exact he

end ExpandedFA.Monotone.Galerkin
