import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.Triangularization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.EquivariantUnipotentSeries

noncomputable section

open Unipotent

variable {k : Type u} [Field k]

abbrev GroupPoints (G : GroupScheme k) (R : TestAlgebra k) :=
  ((groupPointsFunctor k).obj G).obj R

abbrev onPoints {G H : GroupScheme k} (f : G ⟶ H) (R : TestAlgebra k) :
    GroupPoints G R →* GroupPoints H R :=
  (((groupPointsFunctor k).map f).app R).hom

/-- A split torus is a finite product of multiplicative group schemes. -/
def IsSplitTorus (T : GroupScheme k) : Prop :=
  ∃ r : ℕ, Nonempty (T ≅ (StandardGroups.multiplicativePowerGroup k (Index r)).val)

/-- An algebraic action by group automorphisms, with its identities on all test algebras. -/
structure AutomorphismAction (T U : GroupScheme k) where
  action : T.X ⊗ U.X ⟶ U.X
  one_act (R : TestAlgebra k) (x : GroupPoints U R) :
    lift (1 : GroupPoints T R) x ≫ action = x
  mul_act (R : TestAlgebra k) (s t : GroupPoints T R) (x : GroupPoints U R) :
    lift (s * t) x ≫ action = lift s (lift t x ≫ action) ≫ action
  act_one (R : TestAlgebra k) (t : GroupPoints T R) :
    (show GroupPoints U R from lift t (1 : GroupPoints U R) ≫ action) = 1
  act_mul (R : TestAlgebra k) (t : GroupPoints T R) (x y : GroupPoints U R) :
    lift t (x * y) ≫ action =
      (show GroupPoints U R from lift t x ≫ action) *
        (show GroupPoints U R from lift t y ≫ action)

/-- The central series is smooth and connected at every term, with trivial
steps omitted. -/
def IsSmoothAdditiveCentralSeries {U : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries U n) : Prop :=
  S.IsCentral ∧
  (∀ i ≤ n, Smooth (S.term i).val.X.hom ∧ ConnectedSpace (S.term i).val.X.left) ∧
  ∀ i < n, ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
    IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
    Nonempty ((groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k)

/-- The action preserves the subgroup, as witnessed on all test algebras. -/
def IsStable {T U V : GroupScheme k} (a : AutomorphismAction T U) (j : V ⟶ U) : Prop :=
  ∀ (R : TestAlgebra k) (t : GroupPoints T R) (y : GroupPoints V R),
    ∃ z : GroupPoints V R, onPoints j R z = lift t (onPoints j R y) ≫ a.action

/-- The stable central series for an arbitrary algebraic action of a split torus. -/
def StableSeriesForTorusAction : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (U T : AffineAlgebraicGroup k),
    Smooth U.val.X.hom → ConnectedSpace U.val.X.left → IsUnipotent U →
    IsSplitTorus T.val → ∀ a : AutomorphismAction T.val U.val,
      ∃ (n : ℕ) (S : ClosedSeries U n), IsSmoothAdditiveCentralSeries S ∧
        ∀ i ≤ n, IsStable a (S.inclusion i)

/-- In an exact extension, conjugation stabilizes every term of the same series.
On each factor it is scalar multiplication via a character of the quotient torus. -/
def StableSeriesForTorusExtension : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G T : AffineAlgebraicGroup k)
    (U : ClosedSubgroup G.val) (p : G.val ⟶ T.val),
    IsFppfGroupQuotient U p → IsSplitTorus T.val →
    Smooth U.group.X.hom → ConnectedSpace U.group.X.left →
    IsUnipotent (closedSubgroupAlgebraicGroup U) →
    ∃ (n : ℕ) (S : ClosedSeries (closedSubgroupAlgebraicGroup U) n),
      S.IsCentral ∧
      (∀ i ≤ n, Smooth (S.term i).val.X.hom ∧ ConnectedSpace (S.term i).val.X.left) ∧
      (∀ i ≤ n, IsNormalSubgroup (S.inclusion i ≫ U.inclusion)) ∧
      ∀ i < n,
        ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val)
          (e : (groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k)
          (M : AffineAlgebraicGroup k)
          (m : (groupPointsFunctor k).obj M.val ≅ StandardGroups.multiplicativePoints k)
          (χ : T.val ⟶ M.val),
          IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
          ∀ (R : TestAlgebra k) (g : GroupPoints G.val R)
            (y z : GroupPoints (S.term i).val R),
            let j := onPoints (S.inclusion i ≫ U.inclusion) R
            j z = g * j y * g⁻¹ →
            Multiplicative.toAdd (show Multiplicative R from e.hom.app R (onPoints q R z)) =
              (show Rˣ from m.hom.app R (onPoints χ R (onPoints p R g))).val *
                Multiplicative.toAdd (show Multiplicative R from e.hom.app R (onPoints q R y))

end

end LinearAlgebraicGroups.Specs.EquivariantUnipotentSeries
