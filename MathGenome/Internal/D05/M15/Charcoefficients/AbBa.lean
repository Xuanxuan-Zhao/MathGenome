import MathGenome.Internal.Specs.D05.M15.Charcoefficients.AbBa
import MathGenome.Internal.D05.M15.Charcoefficients

/-! Products in opposite orders have the same exterior traces and characteristic
polynomial (paper.tex:3187). All dimensions, degrees, and characteristics are included. -/

noncomputable section
namespace D05.M15.Charcoefficients.AbBa

theorem exterior_trace_comp_comm :
    Specs.D05.M15.Charcoefficients.AbBa.exterior_trace_comp_comm := by
  intro K V _ _ _ _ A B p
  rw [D05.M15.WedgeSign.power_map_comp, D05.M15.WedgeSign.power_map_comp,
    LinearMap.trace_comp_comm']

/-- Reuse the upstream exterior-trace expansion and cyclic-trace consequence. -/
theorem charpoly_comp_comm :
    Specs.D05.M15.Charcoefficients.AbBa.charpoly_comp_comm := by
  exact D05.M15.Charcoefficients.charpoly_comp_comm

theorem charpoly_coeff_comp_comm :
    Specs.D05.M15.Charcoefficients.AbBa.charpoly_coeff_comp_comm := by
  intro K V _ _ _ _ A B k
  exact congrArg (fun f => f.coeff k) (charpoly_comp_comm A B)

end D05.M15.Charcoefficients.AbBa
