import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.MaximalToriExist
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.WeylScheme

universe u

namespace LinearAlgebraicGroups.Specs.MaximalToriAndWeyl

/-- C02. A smooth connected affine algebraic group has a geometrically maximal
torus, and maximal tori over an algebraically closed field are conjugate.
In a reductive group a geometrically maximal torus is its scheme centralizer,
and its right fppf normalizer quotient is finite étale. For split maximal
tori the Weyl group scheme is constant and its rational points lift to the
normalizer. Split maximal tori in a split reductive group are rationally
conjugate. -/
def Statement : Prop :=
  MaximalToriExist.GeometricallyMaximalTorusExists.{u} ∧
    MaximalToriConjugate.ToriConjugate.{u} ∧
    TorusCentralizer.MaximalTorusCentralizer.{u} ∧
    WeylScheme.Statement.{u} ∧
    SplitToriConjugacy.Statement.{u}

end LinearAlgebraicGroups.Specs.MaximalToriAndWeyl
