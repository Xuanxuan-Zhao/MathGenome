import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Unconditional
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Banach
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-! Definitions and bridges for unconditional series and bases.
The scalar counterexample proves that ordered convergence is strictly weaker.
The basis predicates quantify over actual expansions and assume no continuity
of coordinates. All proofs cover the Banach spaces in the source; those not
using completeness are stated for arbitrary normed additive groups/spaces.
-/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C15Unconditional

def finiteSubsum : Spec.finiteSubsumType := @Spec.finiteSubsumValue

def HasUnconditionalSum : Spec.HasUnconditionalSumType := @Spec.HasUnconditionalSumValue

def UnconditionallyConvergent : Spec.UnconditionallyConvergentType :=
  @Spec.UnconditionallyConvergentValue

def IsUnconditionalSchauderBasis : Spec.IsUnconditionalSchauderBasisType :=
  Spec.IsUnconditionalSchauderBasisValue

def IsUnconditionalFiniteBasis : Spec.IsUnconditionalFiniteBasisType :=
  Spec.IsUnconditionalFiniteBasisValue

/-- Mathlib's explicit unconditional summation filter is the finite-subset net. -/
theorem hasUnconditionalSum_iff_hasSum : Spec.HasUnconditionalSumIdentification := by
  intro ι E _ v x
  rfl

theorem unconditionallyConvergent_iff_summable :
    Spec.UnconditionalConvergenceIdentification := by
  intro ι E _ v
  rfl

/-- In the displayed norm topology, net convergence has the required epsilon
condition over every finite superset of a fixed finite set. -/
theorem hasUnconditionalSum_iff_norm : Spec.NormNetIdentification := by
  intro ι E _ v x
  classical
  simpa only [Spec.HasUnconditionalSumValue, dist_eq_norm] using
    (Metric.tendsto_atTop (u := Spec.finiteSubsumValue v) (a := x))

/-- Initial intervals form a cofinal sequence in the finite-subset ordering. -/
theorem hasUnconditionalSum_hasSequentialSum : Spec.UnconditionalSumIsOrderedSum := by
  intro E _ v x h
  apply (C01Banach.hasSequentialSum_iff E v x).mpr
  exact ((hasUnconditionalSum_iff_hasSum v x).mp h).tendsto_sum_nat

theorem unconditionallyConvergent_sequentiallySummable :
    Spec.UnconditionalConvergenceIsOrderedConvergence := by
  rintro E _ v ⟨x, hx⟩
  exact ⟨x, hasUnconditionalSum_hasSequentialSum v x hx⟩

/-- Alternating harmonic series: natural-order convergence does not imply
convergence of the net of all finite subsums, even in a scalar Banach space. -/
theorem orderedConvergence_isStrictlyWeaker : Spec.OrderedConvergenceIsStrictlyWeaker := by
  let v : ℕ → ℝ := fun n => (-1) ^ n * (1 / ((n : ℝ) + 1))
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hmn 1
  obtain ⟨x, hx⟩ := hanti.tendsto_alternating_series_of_tendsto_zero
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨v, ⟨x, (C01Banach.hasSequentialSum_iff ℝ v x).mpr hx⟩, ?_⟩
  intro hu
  have hs := ((unconditionallyConvergent_iff_summable v).mp hu).abs
  have habs : (fun n => |v n|) = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    funext n
    simp only [v, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : 0 ≤ 1 / ((n : ℝ) + 1))]
  rw [habs] at hs
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hs

theorem hasUnconditionalSum_unique : Spec.UnconditionalSumUnique := by
  intro ι E _ v x y hx hy
  exact tendsto_nhds_unique hx hy

/-- The sum of an unconditional expansion is its original vector: both limits
agree along the cofinal sequence of natural-order initial intervals. -/
theorem isUnconditionalSchauderBasis_iff : Spec.UnconditionalSchauderBasisIdentification := by
  intro 𝕜 E _ _ _ e
  constructor
  · rintro ⟨hb, hu⟩
    refine ⟨hb, ?_⟩
    intro x a ha
    obtain ⟨y, hy⟩ := hu x a ha
    have hyx : y = x := tendsto_nhds_unique
      ((C01Banach.hasSequentialSum_iff E _ y).mp
        (hasUnconditionalSum_hasSequentialSum _ y hy))
      ((C01Banach.hasSequentialSum_iff E _ x).mp ha)
    simpa only [hyx] using hy
  · rintro ⟨hb, hu⟩
    exact ⟨hb, fun x a ha => ⟨x, hu x a ha⟩⟩

theorem isUnconditionalSchauderBasis_iff_coordinates :
    Spec.UnconditionalBasisCoordinateIdentification := by
  intro 𝕜 E _ _ _ e h a ha
  constructor
  · intro hu x
    exact hu.2 x (a x) (ha x)
  · intro hu
    refine ⟨h, ?_⟩
    intro x b hb
    have hba : b = a x := (h.2 x).unique hb (ha x)
    simpa only [hba] using hu x

theorem hasUnconditionalSum_fintype : Spec.FiniteFamilySum := by
  intro ι E _ _ v
  exact (hasUnconditionalSum_iff_hasSum v _).mpr (hasSum_fintype v)

theorem finiteExpansion_hasUnconditionalSum : Spec.FiniteExpansionSum := by
  intro 𝕜 E _ _ _ d e x a ha
  simpa only [ha] using hasUnconditionalSum_fintype (fun n => a n • e n)

theorem finiteBasis_isUnconditional : Spec.FiniteBasisIsUnconditional := by
  intro 𝕜 E _ _ _ d e he
  exact ⟨he, fun x a ha => ⟨x, finiteExpansion_hasUnconditionalSum 𝕜 E e x a ha⟩⟩

/-- Length zero uses an empty index type, never a padded sequence of zero
basis vectors. Its finite-subset net and every expansion are zero. -/
theorem emptyBasis_isUnconditional : Spec.EmptyBasisIsUnconditional := by
  intro 𝕜 E _ _ _ _
  apply finiteBasis_isUnconditional
  constructor
  · exact fun n => Fin.elim0 n
  · intro x
    refine ⟨(fun n => Fin.elim0 n), Subsingleton.elim _ _, ?_⟩
    intro a _
    exact Subsingleton.elim _ _

theorem empty_finiteSubsum_eq_zero : Spec.EmptySubsum := by
  intro E _ v F
  exact Finset.sum_eq_zero (fun n _ => Fin.elim0 n)

end ExpandedFA.P1.C15Unconditional
