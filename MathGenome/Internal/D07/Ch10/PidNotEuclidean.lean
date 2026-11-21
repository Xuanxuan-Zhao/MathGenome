import MathGenome.Internal.Specs.D07.Ch10.PidNotEuclidean
import MathGenome.Internal.D07.Ch10.PidNotEuclideanDedekindHasseVerification
import MathGenome.Internal.D07.Ch10.PidNotEuclideanNoEuclideanStructure

/-!
The ring of discriminant -19 is a PID but is not Euclidean
(K07.10.pid_not_euclidean, paper.tex:2068–2140).

The first prerequisite proves principality using the positive integer norm
and the Dedekind–Hasse construction, including denominators 2, 3, 4 and ≥5.
The second excludes every well-founded Euclidean remainder relation by the
universal side-divisor obstruction. Both refer to the same complex subring
and its inherited ring operations.
-/

namespace D07.Ch10.PidNotEuclidean

theorem pid_not_euclidean :
    _root_.Specs.D07.Ch10.PidNotEuclidean.PrincipalButNotEuclidean := by
  exact ⟨PidNotEuclideanDedekindHasseVerification.principalIdealDomain,
    PidNotEuclideanNoEuclideanStructure.notEuclidean⟩

end D07.Ch10.PidNotEuclidean
