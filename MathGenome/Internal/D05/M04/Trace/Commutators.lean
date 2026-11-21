import MathGenome.Internal.Specs.D05.M04.Trace.Commutators
import MathGenome.Internal.D05.M04.Trace

/-!
K05.04.trace: trace functionals and commutators (paper.tex:687–703).

The declared prerequisite `D05.M04.Trace` already proves these results using
matrix units and finite matrix expansions. Reuse those proofs against the
independent statements for this obligation.
-/

namespace D05.M04.Trace.Commutators

theorem commutator_span_eq_ker :
    Specs.D05.M04.Trace.Commutators.commutator_span_eq_ker :=
  D05.M04.Trace.commutator_span_eq_ker

theorem cyclic_functional_iff :
    Specs.D05.M04.Trace.Commutators.cyclic_functional_iff :=
  D05.M04.Trace.cyclic_functional_iff

theorem normalized_cyclic_functional :
    Specs.D05.M04.Trace.Commutators.normalized_cyclic_functional :=
  D05.M04.Trace.normalized_cyclic_functional

theorem empty_functional :
    Specs.D05.M04.Trace.Commutators.empty_functional :=
  D05.M04.Trace.empty_functional

theorem normalization_counterexample :
    Specs.D05.M04.Trace.Commutators.normalization_counterexample :=
  D05.M04.Trace.normalization_counterexample

end D05.M04.Trace.Commutators
