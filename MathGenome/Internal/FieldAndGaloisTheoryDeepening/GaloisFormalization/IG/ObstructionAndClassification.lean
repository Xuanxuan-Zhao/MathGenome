import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.WeakLiftTorsor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.ObstructionAndClassification

namespace GaloisFormalization.IG.FiniteEmbeddingProblem

open Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.Specification

universe u v w

/-- Weak lifts exist exactly when the pulled-back extension class vanishes.
When they exist, their conjugacy classes form a torsor by cocycle twisting. -/
theorem weakLift_obstruction_and_classification :
    WeakLiftObstructionAndClassification.{u,v,w} :=
  fun P => ⟨nonempty_weakSolution_iff_obstruction_eq_zero P, weakSolutionClasses_torsor P⟩

/-- In the central case the coefficient action through the prescribed quotient is trivial. -/
theorem centralWeakLift_coefficient_action :
    CentralWeakLiftCoefficientAction.{u,v,w} :=
  fun P => pullbackKernelAction_eq_self_of_isCentral P

end GaloisFormalization.IG.FiniteEmbeddingProblem
