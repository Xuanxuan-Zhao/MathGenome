import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BoundedWeakstarDual

/-!
The complete statement of `fa2:p1:bounded-weak-star`, paper.tex:3311–3321.
The shared independent definitions fix the original norm-continuous scalar-linear
dual, the seminorms indexed by all norm-null sequences, and their generated
topology. No new carrier, norm, or topology is introduced here.
-/

namespace ExpandedFA.P1.BoundedWeakStar.Spec

universe u v

/-- The null-sequence seminorms are finite and have the stated supremum formula;
they generate a Hausdorff locally convex topology, agree with weak star on
every norm-bounded subset, give the finest such topology among all topologies,
and characterize closed sets by ambient weak-star closed ball slices.
All these clauses hold for arbitrary real or complex normed spaces. Only the
last clause, identifying the continuous linear dual with evaluations, assumes
completeness of the predual. Its evaluating vector is additionally unique. -/
def CompleteStatement : Prop :=
  BoundedWeakstarTopology.Spec.FiniteSupremum.{u, v} ∧
  BoundedWeakstarTopology.Spec.Construction.{u, v} ∧
  BoundedWeakstarTopology.Spec.BoundedAgreement.{u, v} ∧
  BoundedWeakstarTopology.Spec.Finest.{u, v} ∧
  BoundedWeakstarTopology.Spec.ClosedCriterion.{u, v} ∧
  BoundedWeakstarDual.Spec.ContinuousDualIdentification.{u, v}

end ExpandedFA.P1.BoundedWeakStar.Spec
