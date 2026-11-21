import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! The two counterexamples of paper.tex, d10:13:ascoli-boundaries.
The first uses all constants on the fixed nonempty compact domain Unit and
an arbitrary infinite underlying set, with distance exactly 0 or 1.
The second indexes the positive integer frequencies by n + 1. All closures
below use the canonical uniform topology of the bounded supremum metric. -/
noncomputable section
open Set Filter
open scoped Topology
universe u
namespace Specs.D10Topology.Ch13.AscoliBoundaries
open FunctionTopologies

/-- The specified bounded discrete metric on any underlying set. -/
@[instance_reducible]
def discreteMetric (Y : Type u) : MetricSpace Y := by
  classical
  exact {
    dist := fun y z => if y = z then 0 else 1
    dist_self := by intro y; simp
    dist_comm := by intro y z; simp [eq_comm]
    dist_triangle := by
      intro x y z
      by_cases hxy : x = y
      · subst y; simp
      by_cases hyz : y = z
      · subst z; simp
      simp [hxy, hyz]; split_ifs <;> norm_num
    eq_of_dist_eq_zero := by intro x y h; by_contra hn; simp [hn] at h }

def constantFamily (Y : Type u) [TopologicalSpace Y] : Set (ContinuousMaps Unit Y) :=
  range (ContinuousMap.const Unit)

def discrete_constants : Prop :=
  ∀ (Y : Type u) [Infinite Y],
    letI : MetricSpace Y := discreteMetric Y
    Equicontinuous (constantFamily Y) ∧
    (∀ x : Unit, Bornology.IsBounded ((fun f : ContinuousMaps Unit Y => f x) '' constantFamily Y)) ∧
    ¬ PointwiseRelativelyCompact (constantFamily Y) ∧
    ¬ @IsCompact _ uniformContinuousTopology
      (@closure _ uniformContinuousTopology (constantFamily Y))

abbrev SineDomain := Icc (0 : ℝ) (2 * Real.pi)

def sineZero : SineDomain := ⟨0, le_rfl, by positivity⟩

def sineMap (n : ℕ) : ContinuousMaps SineDomain ℝ :=
  ⟨fun x => Real.sin (((n : ℝ) + 1) * x.val),
    Real.continuous_sin.comp (continuous_const.mul continuous_subtype_val)⟩

def sineFamily : Set (ContinuousMaps SineDomain ℝ) := range sineMap

def sineSample (n : ℕ) : SineDomain :=
  ⟨Real.pi / (2 * ((n : ℝ) + 1)), by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 2 * ((n : ℝ) + 1))).mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [Real.pi_pos]⟩

def sine_bound : Prop :=
  ∀ f ∈ sineFamily, ∀ x : SineDomain, |f x| ≤ 1

def sine_pointwise_bounded : Prop :=
  ∀ x : SineDomain, Bornology.IsBounded
    ((fun f : ContinuousMaps SineDomain ℝ => f x) '' sineFamily)

def sine_witness : Prop :=
  Tendsto sineSample atTop (𝓝 sineZero) ∧
    ∀ n, sineMap n (sineSample n) = 1 ∧ sineMap n sineZero = 0

def sine_not_equicontinuous : Prop := ¬ EquicontinuousAt sineFamily sineZero

def sine_not_compact_uniform_closure : Prop :=
  ¬ @IsCompact _ uniformContinuousTopology
    (@closure _ uniformContinuousTopology sineFamily)

end Specs.D10Topology.Ch13.AscoliBoundaries
