import MathGenome.Internal.Specs.D07.Ch10.PidDefinition
import MathGenome.Internal.Specs.D07.Ch10.EuclideanDefinition
import MathGenome.Internal.Specs.D07.Ch10.PidNotEuclideanQuadraticIntegerNorm

/-!
The final assertion of K07.10.pid_not_euclidean, paper.tex:2068–2140.
The ring is the shared, concretely embedded complex subring ℤ[omega],
where omega = (1 + sqrt(-19))/2. The norm and denominator constructions
are specified by the prerequisite goals for this entry.
-/

namespace Specs.D07.Ch10.PidNotEuclidean

/-- Every ideal of the domain ℤ[(1 + sqrt(-19))/2] is principal, but its
given ring operations admit no well-founded Euclidean remainder relation.
The Euclidean predicate requires only well-foundedness and division with
strictly smaller nonzero remainder, with no multiplicative size axiom. -/
def PrincipalButNotEuclidean : Prop :=
  PidDefinition.pidPredicateValue
      _root_.D07.Ch10.PidNotEuclideanQuadraticIntegerNorm.R ∧
    ¬ EuclideanDefinition.IsEuclidean
      _root_.D07.Ch10.PidNotEuclideanQuadraticIntegerNorm.R

end Specs.D07.Ch10.PidNotEuclidean
