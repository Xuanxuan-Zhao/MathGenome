import MathGenome.Internal.Specs.D07.Ch10.EuclideanDefinition
import MathGenome.Internal.Specs.D07.Ch10.PidDefinition

/-!
Independent specification for K07.10.euclidean_pid, paper.tex:1919–1930.
The Euclidean hypothesis is the source's existential well-founded relation
predicate. The conclusion includes the domain condition and every ideal,
including the zero ideal and the whole ring.
-/

universe u

namespace Specs.D07.Ch10.EuclideanPid

/-- Every Euclidean domain, in the precise source sense, is a PID. -/
def EuclideanImpliesPID : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    EuclideanDefinition.IsEuclidean R → PidDefinition.pidPredicateValue R

end Specs.D07.Ch10.EuclideanPid
