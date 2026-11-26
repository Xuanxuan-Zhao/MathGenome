import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.MaximalToriAndWeyl
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
universe u

namespace LinearAlgebraicGroups.Reductive.MaximalToriAndWeyl

theorem maximalToriAndWeyl_conditional
    (existence : Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u})
    (splitConjugacy : Specs.SplitToriConjugacy.Statement.{u})
    (centralizer : Specs.TorusCentralizer.MaximalTorusCentralizer.{u})
    (weyl : Specs.WeylScheme.Statement.{u}) :
    Specs.MaximalToriAndWeyl.Statement.{u} :=
  ⟨existence, LinearAlgebraicGroups.MaximalToriConjugate.maximalToriConjugate.{u},
    centralizer, weyl, splitConjugacy⟩

end LinearAlgebraicGroups.Reductive.MaximalToriAndWeyl

universe v8_closure_ee3ca6f310e4bf1a_u0
theorem _root_.«LinearAlgebraicGroups».«Reductive».«MaximalToriAndWeyl».«maximalToriAndWeyl» : _root_.«LinearAlgebraicGroups».«Specs».«MaximalToriAndWeyl».«Statement».{v8_closure_ee3ca6f310e4bf1a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«MaximalToriAndWeyl».«maximalToriAndWeyl_conditional».{v8_closure_ee3ca6f310e4bf1a_u0} (@_root_.«LinearAlgebraicGroups».«MaximalToriExist».«geometricallyMaximalTorusExists».{v8_closure_ee3ca6f310e4bf1a_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«SplitToriConjugacy».«splitToriConjugacy».{v8_closure_ee3ca6f310e4bf1a_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«TorusCentralizer».«maximalTorusCentralizer».{v8_closure_ee3ca6f310e4bf1a_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«WeylScheme».«weylScheme».{v8_closure_ee3ca6f310e4bf1a_u0})
