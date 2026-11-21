import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Polars
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Dual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import Mathlib.Analysis.Convex.Combination

/-! Canonical polar sets, pairing topologies, and the zero-inclusive absolutely
convex hull of Definition `fa2:p1:c06:polars`. The topology maps are linear
identity equivalences, rather than identifications with a different dual. -/

namespace ExpandedFA.P1.C06Polars

universe u v
open scoped BigOperators

/-- The polar in the continuous scalar-linear dual. -/
noncomputable abbrev polar : Spec.PolarType :=
  Spec.PolarValue

/-- The prepolar for the same evaluation pairing. -/
noncomputable abbrev prepolar : Spec.PrepolarType :=
  Spec.PrepolarValue

/-- The identity on vectors, with the native weak topology on the target. -/
noncomputable def weakEquiv : Spec.WeakEquivType :=
  fun 𝕜 E _ _ _ => toWeakSpace 𝕜 E

/-- The identity on continuous linear functionals, with the native weak-star target. -/
noncomputable def weakStarEquiv : Spec.WeakStarEquivType :=
  fun _ _ _ _ _ => StrongDual.toWeakDual

/-- The native weak topology transported to the original vector carrier. -/
noncomputable def weakTopology : Spec.WeakTopologyType :=
  fun 𝕜 E _ _ _ => dualPairTopology 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)

/-- The native weak-star topology transported to the original dual carrier. -/
noncomputable abbrev weakStarTopology : Spec.WeakStarTopologyType :=
  C12WeakStar.weakStarTopology

/-- Real convexity together with balance over the original scalar field. -/
noncomputable abbrev IsAbsolutelyConvex : Spec.IsAbsolutelyConvexType :=
  Spec.IsAbsolutelyConvexValue

/-- Finite sums with total coefficient modulus at most one, allowing the empty sum. -/
noncomputable abbrev absolutelyConvexHull : Spec.AbsolutelyConvexHullType :=
  Spec.AbsolutelyConvexHullValue

/-- The closure is taken in the original norm topology. -/
noncomputable abbrev closedAbsolutelyConvexHull : Spec.ClosedAbsolutelyConvexHullType :=
  Spec.ClosedAbsolutelyConvexHullValue

@[simp]
theorem polar_mem : Spec.PolarMembership := by
  intro 𝕜 E _ _ _ A f
  rfl

@[simp]
theorem prepolar_mem : Spec.PrepolarMembership := by
  intro 𝕜 E _ _ _ A f
  rfl

@[simp]
theorem weakEquiv_apply : Spec.WeakEquivIdentity := by
  intro 𝕜 E _ _ _ x
  rfl

@[simp]
theorem weakStarEquiv_apply : Spec.WeakStarEquivIdentity := by
  intro 𝕜 E _ _ _ f x
  rfl

theorem weakTopology_initial : Spec.WeakTopologyInitial := by
  intro 𝕜 E _ _ _
  exact dualPairTopology_evaluation 𝕜 E

theorem weakStarTopology_initial : Spec.WeakStarTopologyInitial := by
  intro 𝕜 E _ _ _
  exact C12WeakStar.weakStarTopology_evaluations 𝕜 E

theorem weakTopology_coarsest : Spec.WeakTopologyCoarsest := by
  intro 𝕜 E _ _ _
  -- Fix the norm-continuous dual before introducing the competing topology.
  have h := dualPairTopology_coarsest 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  dsimp only
  intro t
  exact h t

theorem weakStarTopology_coarsest : Spec.WeakStarTopologyCoarsest := by
  intro 𝕜 E _ _ _
  dsimp only
  intro t
  exact C12WeakStar.weakStarTopology_evaluation_coarsest 𝕜 E t

theorem isAbsolutelyConvex_iff : Spec.AbsolutelyConvexCharacterization := by
  intro 𝕜 E _ _ _ A
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  exact and_congr_right fun _ => balanced_iff_smul_mem

theorem zero_mem_absolutelyConvexHull : Spec.HullZero := by
  intro 𝕜 E _ _ _ A
  exact ⟨0, Fin.elim0, Fin.elim0, (fun i => i.elim0), by simp, by simp⟩

@[simp]
theorem absolutelyConvexHull_empty : Spec.HullEmpty := by
  intro 𝕜 E _ _ _
  apply Set.Subset.antisymm
  · rintro y ⟨n, c, x, hx, _, hsum⟩
    cases n with
    | zero => simpa using hsum.symm
    | succ n => exact (hx 0).elim
  · rintro y (rfl : y = 0)
    exact zero_mem_absolutelyConvexHull 𝕜 E ∅

theorem subset_absolutelyConvexHull : Spec.SubsetHull := by
  intro 𝕜 E _ _ _ A y hy
  exact ⟨1, (fun _ => 1), (fun _ => y), (fun _ => hy), by simp, by simp⟩

theorem absolutelyConvexHull_isAbsolutelyConvex :
    Spec.HullAbsolutelyConvex := by
  intro 𝕜 E _ _ _ A
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  change Convex ℝ (absolutelyConvexHull 𝕜 E A) ∧ Balanced 𝕜 (absolutelyConvexHull 𝕜 E A)
  constructor
  · rintro u ⟨n, c, x, hx, hc, rfl⟩ v ⟨m, d, y, hy, hd, rfl⟩ a b ha hb hab
    refine ⟨n + m, Fin.append (fun i => (a : 𝕜) * c i) (fun i => (b : 𝕜) * d i),
      Fin.append x y, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using hx j
      · simpa using hy j
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
        norm_mul, RCLike.norm_ofReal, abs_of_nonneg ha, abs_of_nonneg hb,
        ← Finset.mul_sum]
      calc
        a * (∑ i, ‖c i‖) + b * (∑ i, ‖d i‖) ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hc ha) (mul_le_mul_of_nonneg_left hd hb)
        _ = 1 := by simpa using hab
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
        mul_smul, ← Finset.smul_sum, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  · apply balanced_iff_smul_mem.mpr
    rintro a ha u ⟨n, c, x, hx, hc, rfl⟩
    refine ⟨n, (fun i => a * c i), x, hx, ?_, ?_⟩
    · simp only [norm_mul, ← Finset.mul_sum]
      calc
        ‖a‖ * (∑ i, ‖c i‖) ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
        _ ≤ 1 := by simpa using ha
    · simp only [mul_smul, Finset.smul_sum]

/-- Normalize each coefficient to the closed scalar unit ball, and use its
modulus as a nonnegative real weight. A slack weight at zero makes the total
weight one. This also handles a zero coefficient and an empty family. -/
theorem absolutelyConvexHull_minimal : Spec.HullMinimal := by
  intro 𝕜 E _ _ _ A C hAC hzero hC u hu
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  change Convex ℝ C ∧ Balanced 𝕜 C at hC
  rcases hu with ⟨n, c, x, hx, hc, rfl⟩
  let w : Fin (n + 1) → ℝ := Fin.cons (1 - ∑ i, ‖c i‖) (fun i => ‖c i‖)
  let z : Fin (n + 1) → E := Fin.cons 0
    (fun i => ((‖c i‖ : 𝕜)⁻¹ * c i) • x i)
  have hw (i) : 0 ≤ w i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact sub_nonneg.mpr hc
    · exact norm_nonneg _
  have hw_sum : ∑ i, w i = 1 := by
    simp [w, Fin.sum_univ_succ]
  have hz (i) : z i ∈ C := by
    refine Fin.cases hzero (fun j => ?_) i
    apply hC.2.smul_mem _ (hAC (hx j))
    by_cases hj : c j = 0
    · simp [hj]
    · simp [norm_mul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hj)]
  have hmem := hC.1.sum_mem (t := Finset.univ) (fun i _ => hw i) hw_sum (fun i _ => hz i)
  have heq (i : Fin n) : ‖c i‖ • (((‖c i‖ : 𝕜)⁻¹ * c i) • x i) = c i • x i := by
    by_cases hi : c i = 0
    · simp [hi]
    · rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul, ← mul_assoc,
        mul_inv_cancel₀, one_mul]
      exact_mod_cast (norm_ne_zero_iff.mpr hi)
  simpa only [w, z, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_zero,
    zero_add, heq] using hmem

end ExpandedFA.P1.C06Polars
