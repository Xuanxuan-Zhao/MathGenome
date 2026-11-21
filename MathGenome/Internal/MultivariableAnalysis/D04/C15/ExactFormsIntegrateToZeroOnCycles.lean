import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.ExactFormsIntegrateToZeroOnCycles
import MathGenome.Internal.MultivariableAnalysis.D04.C15.CellStokesC1
import MathGenome.Internal.MultivariableAnalysis.D04.C15.GeneralizedStokes

/-! Exact forms integrate to zero on finite cell cycles and compact
boundaryless manifolds (paper.tex, d04:15:exact-cycles). -/
noncomputable section

namespace D04.ExactCycles
open Specs.D04.C15.ExactFormsIntegrateToZeroOnCycles

/-- Stokes sends the derivative integral to the integral over the zero
formal boundary. The shared chain integral is an additive homomorphism. -/
theorem exact_chain_integral_zero : exact_chain_integral_zeroType := by
  intro d n O C V eta heta hCV hcycle
  rw [D04.Cells.chain_stokes_c1 C V eta heta hCV, hcycle, map_zero]

/-- Compactness makes the primitive's relative closed support compact;
boundaryless intrinsic Stokes then gives zero. -/
theorem exact_intrinsic_integral_zero : exact_intrinsic_integral_zeroType := by
  intro d n M o hcompact hboundary eta heta
  exact D04Stokes.intrinsic_stokes_boundaryless o eta heta
    (D04Stokes.formSupport_compact_of_compact hcompact eta) hboundary

/-- The relevant ambient support along a compact manifold is compact.
The C¹ ambient Stokes theorem applies without a C² primitive or C² charts. -/
theorem exact_ambient_integral_zero : exact_ambient_integral_zeroType := by
  intro d n M o hcompact hboundary V eta hMV heta
  exact D04Stokes.ambient_stokes_boundaryless o V eta hMV heta
    (hcompact.inter_right (isClosed_tsupport eta)) hboundary

end D04.ExactCycles
