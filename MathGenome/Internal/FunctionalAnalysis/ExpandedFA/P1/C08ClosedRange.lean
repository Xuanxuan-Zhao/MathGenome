import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08ClosedRange
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08BoundedInverse
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
The quotient by the full closed kernel is Banach, and the induced operator
is injective with the original range. A closed range in a Banach target
allows the bounded inverse theorem on this quotient. Conversely the distance
bound makes the induced operator anti-Lipschitz, so its image is closed.
For a lower bound on the original space, the same argument requires no
completeness of the target and constructs the bounded inverse on the range.
-/

namespace ExpandedFA.P1.C08ClosedRange

open scoped NNReal

theorem kernel_distance : Spec.KernelDistance := by
  intro 𝕜 E F _ _ _ _ _ T
  exact ⟨T.isClosed_ker, fun x => (C02QuotientNorm.distanceSeminorm_mk 𝕜 E T.ker x).2.1⟩

theorem closed_range_distance : Spec.ClosedRangeDistance := by
  intro 𝕜 E F _ _ _ _ _ _ _ T
  let : IsClosed (T.ker : Set E) := T.isClosed_ker
  obtain ⟨U, hU, _, _⟩ := C02QuotientMap.quotient_bounded_factorization 𝕜 E F T.ker
    T.isClosed_ker T (fun _ hx => hx)
  have hnorm (x : E) : ‖T.ker.mkQ x‖ = Metric.infDist x (T.ker : Set E) :=
    (kernel_distance 𝕜 E F T).2 x
  have hUinj : Function.Injective U := by
    intro z w hzw
    obtain ⟨x, rfl⟩ := T.ker.mkQ_surjective z
    obtain ⟨y, rfl⟩ := T.ker.mkQ_surjective w
    apply sub_eq_zero.mp
    rw [← T.ker.mkQ.map_sub]
    apply (Submodule.Quotient.mk_eq_zero T.ker).mpr
    change T (x - y) = 0
    rw [T.map_sub, ← hU x, ← hU y, hzw, sub_self]
  have hrange : Set.range U = Set.range T := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := T.ker.mkQ_surjective z
      exact ⟨x, (hU x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨T.ker.mkQ x, hU x⟩
  constructor
  · intro hclosed
    have hUclosed : IsClosed (Set.range U) := hrange ▸ hclosed
    let : CompleteSpace U.range := hUclosed.completeSpace_coe
    have hbij : Function.Bijective U.rangeRestrict := by
      constructor
      · intro z w h
        exact hUinj (congrArg Subtype.val h)
      · rintro ⟨y, hy⟩
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, Subtype.ext hz⟩
    obtain ⟨S, hSU, _, _⟩ := C08BoundedInverse.bounded_inverse 𝕜 (E ⧸ T.ker) U.range
      U.rangeRestrict hbij
    refine ⟨‖S‖ + 1, by positivity, ?_⟩
    intro x
    calc
      Metric.infDist x (T.ker : Set E) = ‖T.ker.mkQ x‖ := (hnorm x).symm
      _ = ‖S (U.rangeRestrict (T.ker.mkQ x))‖ := congrArg norm (hSU _).symm
      _ ≤ ‖S‖ * ‖U.rangeRestrict (T.ker.mkQ x)‖ := S.le_opNorm _
      _ = ‖S‖ * ‖T x‖ := by
        change ‖S‖ * ‖U (T.ker.mkQ x)‖ = _
        rw [hU]
      _ ≤ (‖S‖ + 1) * ‖T x‖ := by nlinarith [norm_nonneg (T x)]
  · rintro ⟨C, hC, hbound⟩
    have hquot (z : E ⧸ T.ker) : ‖z‖ ≤ C * ‖U z‖ := by
      obtain ⟨x, rfl⟩ := T.ker.mkQ_surjective z
      rw [hnorm, hU]
      exact hbound x
    have hanti : AntilipschitzWith ⟨C, hC.le⟩ U := by
      apply AntilipschitzWith.of_le_mul_dist
      intro z w
      change dist z w ≤ C * dist (U z) (U w)
      simpa only [dist_eq_norm, ← U.map_sub] using hquot (z - w)
    rw [← hrange]
    exact hanti.isClosed_range U.uniformContinuous


/-- The lower bound gives a uniform embedding; completeness of the domain
therefore makes its range closed. The algebraic inverse on that range is
continuous by the same bound, with precisely the given constant. -/
theorem bounded_below_closed_range :
    Spec.BoundedBelowClosedRange := by
  intro 𝕜 E F _ _ _ _ _ _ T C hC hbound
  let K : ℝ≥0 := ⟨C, hC.le⟩
  have ha : AntilipschitzWith K T := T.antilipschitz_of_bound hbound
  have hinj : Function.Injective T := ha.injective
  have hclosed : IsClosed (T.range : Set F) := ha.isClosed_range T.uniformContinuous
  let e : E ≃ₗ[𝕜] T.range := LinearEquiv.ofInjective T.toLinearMap hinj
  have he (y : T.range) : T (e.symm y) = (y : F) :=
    LinearEquiv.ofInjective_symm_apply T.toLinearMap (h := hinj) y
  have hb (y : T.range) : ‖e.symm y‖ ≤ C * ‖y‖ := by
    simpa only [he y, Submodule.norm_coe] using hbound (e.symm y)
  let S : T.range →L[𝕜] E := e.symm.toLinearMap.mkContinuous C hb
  refine ⟨hinj, hclosed, S, S.opNorm_le_bound hC.le hb, ?_, ?_⟩
  · intro x
    exact e.symm_apply_apply x
  · intro y
    exact he y

/-- Injectivity turns the kernel into the singleton zero, so its distance
is the original norm, including on the zero space. -/
theorem injective_kernel_distance :
    Spec.InjectiveKernelDistance := by
  intro 𝕜 E F _ _ _ _ _ T hinj x
  have hker : (T.ker : Set E) = {0} := by
    ext z
    change T z = 0 ↔ z = 0
    constructor
    · intro hz
      exact hinj (hz.trans T.map_zero.symm)
    · rintro rfl
      exact T.map_zero
  rw [hker, Metric.infDist_singleton, dist_zero_right]

/-- The distance-to-kernel estimate and the norm lower bound have exactly
the same constant in the injective Banach-space specialization. -/
theorem injective_distance_estimate_specialization :
    Spec.InjectiveDistanceEstimateSpecialization := by
  intro 𝕜 E F _ _ _ _ _ T hinj C
  simp only [injective_kernel_distance 𝕜 E F T hinj]


/-- Closed range and boundedness below for injective Banach-space maps. -/
theorem injective_closed_range_iff : Spec.InjectiveClosedRange := by
  intro 𝕜 E F _ _ _ _ _ _ _ T hinj
  rw [closed_range_distance 𝕜 E F T]
  simp only [injective_kernel_distance 𝕜 E F T hinj]

end ExpandedFA.P1.C08ClosedRange
