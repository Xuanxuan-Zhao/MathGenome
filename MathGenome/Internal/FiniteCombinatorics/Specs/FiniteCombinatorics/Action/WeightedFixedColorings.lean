import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.FixedColorings
import Mathlib.GroupTheory.GroupAction.Defs

/-! Independent specification of the integral fixed-coloring part of W33.
The full orbit enumeration and rational cycle-index substitution are allocated
separately. All weights here lie in the natural polynomial ring. -/
namespace FiniteCombinatorics.WeightedFixedColoringsSpec
open scoped BigOperators
universe u v w
attribute [local instance] Classical.propDecidable FixedColoringsSpec.coloringAction

noncomputable def coloringWeight (X : Type v) (C : Type w) [Fintype X]
    (f : X → C) : MvPolynomial C ℕ := ∏ x, MvPolynomial.X (f x)

/-- An orbit's weight is computed at a representative; the representative
independence is part of `OrbitWeightMk`, not an assumed certificate. -/
noncomputable def orbitWeight (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X]
    (O : MulAction.orbitRel.Quotient G (X → C)) : MvPolynomial C ℕ :=
  coloringWeight X C O.out

noncomputable def fixedWeightSum (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype X] [Fintype C] (g : G) : MvPolynomial C ℕ :=
  ∑ f ∈ Finset.univ.filter (fun f : X → C => g • f = f), coloringWeight X C f

def coloringWeightType := ∀ (X : Type v) (C : Type w) [Fintype X],
  (X → C) → MvPolynomial C ℕ

def orbitWeightType := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X],
  MulAction.orbitRel.Quotient G (X → C) → MvPolynomial C ℕ

def fixedWeightSumType := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] [Fintype C], G → MvPolynomial C ℕ

def WeightInvariant : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] (g : G) (f : X → C),
  coloringWeight X C (g • f) = coloringWeight X C f

def OrbitWeightMk : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] (f : X → C),
  orbitWeight G X C (Quotient.mk (MulAction.orbitRel G (X → C)) f) =
    coloringWeight X C f

def FixedFactorization : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] [Fintype C] (g : G),
  fixedWeightSum G X C g =
    ∏ k ∈ Finset.Icc 1 (Fintype.card X),
      (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℕ) ^ k) ^
        CycleIndexSpec.countCycles G X g k

def EmptyWeight : Prop := ∀ (X : Type v) (C : Type w) [Fintype X]
  [IsEmpty X] (f : X → C), coloringWeight X C f = 1

def EmptyPositions : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] [Fintype C] [IsEmpty X] (g : G),
  fixedWeightSum G X C g = 1

def EmptyColors : Prop := ∀ (G : Type u) (X : Type v) (C : Type w)
  [Group G] [MulAction G X] [Fintype X] [Fintype C]
  [Nonempty X] [IsEmpty C] (g : G), fixedWeightSum G X C g = 0

end FiniteCombinatorics.WeightedFixedColoringsSpec
