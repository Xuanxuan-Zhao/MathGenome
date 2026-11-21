import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SchrodingerPotentialBounds

/-! Independent interface for `fa2:p3:schrodinger-potential`, paper.tex:13642–13673.
The canonical objects and full conclusion `Spec.Schrodinger` are shared with the
upstream potential-bounds and free-Laplacian obligations. In particular L² has
native real-line domain, the real clause uses real-valued classes, H² requires
both weak derivatives in L², and admissibility is an a.e. L² + L∞ decomposition.
No analytic bounds or free-operator facts are assumptions of the final theorem. -/

namespace ExpandedFA.Unbounded.SchrodingerPotential.Spec

/-- Both quantitative estimates required in addition to the operator conclusion:
arbitrarily small relative operator bound on H², and infinitesimal quadratic-form
bound (with integrability) on the whole H¹ form domain. -/
def PotentialEstimates : Prop := RelativeBound ∧ FormBound

end ExpandedFA.Unbounded.SchrodingerPotential.Spec
