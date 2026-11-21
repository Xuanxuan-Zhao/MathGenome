import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SubcomplexNeighborhoods
import Mathlib.Algebra.DirectSum.Module

/-!
Independent specifications for the finite wedge assertion in paper.tex,
Proposition `prop:p202-homology-computations`, lines 1588–1595 and 1617–1624.
The coefficient object is an arbitrary module, as stipulated at 1430–1434.
There is no connectedness assumption. The point in the presentation below
also gives the stipulated point as the empty wedge.
-/
noncomputable section
open CategoryTheory DirectSum

universe u v w
namespace P202Specs.WedgeHomology
open P202Specs.SingularChains P202.Cellular

/-- A space with a specified point; no separation axiom is implicit. -/
structure BasedSpace where
  space : TopCat.{w}
  base : space

/-- The source's good basepoint condition, including closedness. -/
def Good (X : BasedSpace.{w}) : Prop :=
  IsClosed ({X.base} : Set X.space) ∧
    ∃ W : Set X.space, IsOpen W ∧ StrongDeformationRetracts {X.base} W

/-- A vertex means a point of an actual zero-dimensional open cell. -/
def IsVertex (X : BasedSpace.{w}) [CWStructure X.space] : Prop :=
  ∃ c : Cell X.space 0, X.base ∈ openCell X.space 0 c

section Wedge
variable {ι : Type w} (X : ι → BasedSpace.{w})

/-- The disjoint union with a distinguished point. For nonempty families the
extra point is identified with the original basepoints. -/
abbrev Presentation := PUnit.{w+1} ⊕ (Σ i, (X i).space)

def IsBase : Presentation X → Prop
  | .inl _ => True
  | .inr ⟨i, x⟩ => x = (X i).base

def wedgeSetoid : Setoid (Presentation X) where
  r a b := a = b ∨ (IsBase X a ∧ IsBase X b)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => h.elim (fun e => Or.inl e.symm) (fun h => Or.inr h.symm)
    trans := by
      intro a b c hab hbc
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      exact Or.inr ⟨hab.1, hbc.2⟩ }

/-- The usual quotient topology on the wedge, with no weak or metric topology
substituted. No finiteness condition is needed to define the space. -/
def Wedge := Quotient (wedgeSetoid X)

instance : TopologicalSpace (Wedge X) :=
  inferInstanceAs (TopologicalSpace (Quotient (wedgeSetoid X)))

def point : Wedge X := Quotient.mk _ (.inl PUnit.unit)

def inclusion (i : ι) : (X i).space ⟶ TopCat.of (Wedge X) :=
  TopCat.ofHom ⟨fun x => Quotient.mk _ (.inr ⟨i, x⟩),
    continuous_quotient_mk'.comp (continuous_inr.comp continuous_sigmaMk)⟩

/-- The map in the conclusion is precisely the sum of the maps induced by
the summand inclusions, for arbitrary module coefficients. -/
def inclusionSum (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    (⨁ i : ι, reducedHomology R M (X i).space (n : ℤ)) →ₗ[R]
      reducedHomology R M (TopCat.of (Wedge X)) (n : ℤ) := by
  classical
  exact DirectSum.toModule R ι _
    (fun i => ((reducedHomologyFunctor R M (n : ℤ)).map (inclusion X i)).hom)

end Wedge

/-- Full finite good-pointed-pair conclusion, including degrees zero and the
empty and one-member families. -/
def goodWedgeHomology_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type w) [Finite ι] (X : ι → BasedSpace.{w}),
    (∀ i, Good (X i)) → ∀ n : ℕ, Function.Bijective (inclusionSum X R M n)

/-- The original CW statement uses the actual CW structures and their vertices.
It is not stated with an additional good-basepoint assumption. -/
def cwWedgeHomology_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type w) [Finite ι] (X : ι → BasedSpace.{w})
    [∀ i, CWStructure (X i).space],
    (∀ i, IsVertex (X i)) → ∀ n : ℕ, Function.Bijective (inclusionSum X R M n)

end P202Specs.WedgeHomology
