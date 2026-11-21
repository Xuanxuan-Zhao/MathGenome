import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.FixedColorings
import Mathlib.Algebra.MvPolynomial.Eval

/-! Independent statement of unweighted Pólya enumeration, paper.tex W32.
The quotient uses inverse precomposition on colorings. The cycle index has
all complete cycles, including fixed points, and is evaluated over ℚ.
The finite types may be empty; no faithful action is required. -/
namespace FiniteCombinatorics.PolyaSpec

universe u v w

def Enumeration : Prop :=
  ∀ (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype G] [Fintype X] [Fintype C],
    letI := FixedColoringsSpec.coloringAction G X C
    (Nat.card (Quotient (MulAction.orbitRel G (X → C))) : ℚ) =
      MvPolynomial.eval (fun _ => (Fintype.card C : ℚ)) (CycleIndexSpec.cycleIndex G X)

end FiniteCombinatorics.PolyaSpec
