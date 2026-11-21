import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.Banach
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Ring

/-! Banach's contraction theorem, including every estimate in d10:14:banach.
The nonnegative real library constant is explicitly constructed from the given
real q. Chapter 9's proved bridges transfer completeness and convergence.
No Baire category result is used. -/
open scoped NNReal
universe u
namespace D10Topology.Ch14

theorem banach_contraction : Specs.D10Topology.Ch14.Banach.banach_contraction.{u} := by
  intro X d hnonempty hcomplete T q hq₀ hq₁ hcontract
  let := d
  let := hnonempty
  let := (Ch09.sequentiallyComplete_iff_mathlib d.toPseudoMetricSpace).mp hcomplete
  let K : ℝ≥0 := ⟨q, hq₀⟩
  have hK : (K : ℝ) = q := rfl
  have hT : ContractingWith K T :=
    ⟨hq₁, lipschitzWith_iff_dist_le_mul.mpr hcontract⟩
  refine ⟨hT.fixedPoint T, hT.fixedPoint_isFixedPt,
    fun p' hp' => hT.fixedPoint_unique hp', ?_, ?_⟩
  · intro x₀
    refine ⟨(Ch09.sequenceConverges_iff_mathlib _ _ _).mpr
      (hT.tendsto_iterate_fixedPoint x₀), ?_, ?_, ?_⟩
    · intro n
      change dist (T^[n] x₀) (hT.fixedPoint T) ≤
        q ^ n / (1 - q) * dist (T^[1] x₀) x₀
      calc
        _ ≤ dist x₀ (T x₀) * q ^ n / (1 - q) :=
          hT.apriori_dist_iterate_fixedPoint_le x₀ n
        _ = _ := by rw [Function.iterate_one, dist_comm x₀ (T x₀)]; ring
    · intro n
      change dist (T^[n] x₀) (hT.fixedPoint T) ≤
        1 / (1 - q) * dist (T^[n + 1] x₀) (T^[n] x₀)
      calc
        _ ≤ dist (T^[n] x₀) (T^[n + 1] x₀) / (1 - q) :=
          hT.aposteriori_dist_iterate_fixedPoint_le x₀ n
        _ = _ := by rw [dist_comm (T^[n] x₀) (T^[n + 1] x₀)]; ring
    · intro n hn
      change dist (T^[n] x₀) (hT.fixedPoint T) ≤
        q / (1 - q) * dist (T^[n] x₀) (T^[n - 1] x₀)
      have hnext : T^[n] x₀ = T (T^[n - 1] x₀) := by
        have hn' : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
        conv_lhs => rw [hn', Function.iterate_succ_apply']
      have hstep : dist (T^[n] x₀) (T^[n + 1] x₀) ≤
          q * dist (T^[n] x₀) (T^[n - 1] x₀) := by
        rw [Function.iterate_succ_apply', hnext]
        simpa only [hK, dist_comm] using
          hT.dist_le_mul (T^[n - 1] x₀) (T (T^[n - 1] x₀))
      calc
        _ ≤ dist (T^[n] x₀) (T^[n + 1] x₀) / (1 - q) :=
          hT.aposteriori_dist_iterate_fixedPoint_le x₀ n
        _ ≤ (q * dist (T^[n] x₀) (T^[n - 1] x₀)) / (1 - q) :=
          div_le_div_of_nonneg_right hstep (le_of_lt (sub_pos.mpr hq₁))
        _ = _ := by ring
  · intro z
    exact hT.dist_fixedPoint_le z

end D10Topology.Ch14
