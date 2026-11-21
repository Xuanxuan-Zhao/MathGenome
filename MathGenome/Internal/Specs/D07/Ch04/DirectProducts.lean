import MathGenome.Internal.Specs.D07.Ch01.GroupDefinition
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

/-!
Independent specification for `K07.04.direct_products`, paper.tex:746–754.
Products are dependent function types, so arbitrary index sets and unequal
factor types are allowed. The finite-support clauses distinguish the full
product from the direct sum. Infinitude alone does not imply strictness:
the strictness assertion explicitly requires nontrivial factors.
-/

namespace Specs.D07.Ch04.DirectProducts

universe u v w

def ProductType : Type (max u v + 1) :=
  (I : Type u) → (I → Type v) → Type (max u v)

def productValue : ProductType.{u, v} := fun I G => ∀ i : I, G i

def GroupStructureType : Type (max u v + 1) :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)], Group (∀ i, G i)

def groupStructureValue : GroupStructureType.{u, v} := fun _ _ _ => inferInstance

def PointwiseOperations : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)],
    (∀ (x y : ∀ i, G i) (i : I), (x * y) i = x i * y i) ∧
    (∀ i : I, (1 : ∀ i, G i) i = 1) ∧
    (∀ (x : ∀ i, G i) (i : I), x⁻¹ i = (x i)⁻¹)

def ProductGroupLaws : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)],
    Specs.D07.Ch01.GroupDefinition.groupAxiomsValue (∀ i, G i) (· * ·) 1 Inv.inv

def EmptyProductTrivial : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] [IsEmpty I],
    ∀ x : ∀ i, G i, x = 1

def ProjectionType : Type (max u v + 1) :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] (i : I),
    (∀ j, G j) →* G i

def projectionValue : ProjectionType.{u, v} := fun _ G _ i => Pi.evalMonoidHom G i

def ProjectionLaws : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] (i : I),
    (∀ x : ∀ j, G j, projectionValue I G i x = x i) ∧
    projectionValue I G i 1 = 1 ∧
    (∀ x y : ∀ j, G j,
      projectionValue I G i (x * y) = projectionValue I G i x * projectionValue I G i y)

def InclusionType : Type (max u v + 1) :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] (i : I),
    G i →* (∀ j, G j)

noncomputable def inclusionValue : InclusionType.{u, v} := by
  classical
  exact fun _ G _ i => MonoidHom.mulSingle G i

def InclusionLaws : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] (i : I),
    (∀ g : G i, inclusionValue I G i g i = g) ∧
    (∀ (g : G i) (j : I), j ≠ i → inclusionValue I G i g j = 1) ∧
    inclusionValue I G i 1 = 1 ∧
    (∀ g h : G i,
      inclusionValue I G i (g * h) = inclusionValue I G i g * inclusionValue I G i h)

def CoordinateMapsSplit : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] (i : I),
    (∀ g : G i, projectionValue I G i (inclusionValue I G i g) = g) ∧
    Function.Injective (inclusionValue I G i) ∧
    Function.Surjective (projectionValue I G i)

def FiniteProductCardinality : Prop := by
  classical
  exact ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)]
    [Fintype I] [∀ i, Fintype (G i)],
    Fintype.card (∀ i, G i) = ∏ i : I, Fintype.card (G i)

def PairCardinality : Prop :=
  ∀ (A : Type v) (B : Type w) [Group A] [Group B] [Fintype A] [Fintype B],
    Fintype.card (A × B) = Fintype.card A * Fintype.card B

/-- The finite-support set is a subgroup, with exactly the displayed carrier. -/
def FiniteSupportSubgroupExists : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)],
    ∃ H : Subgroup (∀ i, G i), ∀ x : ∀ i, G i,
      x ∈ H ↔ Set.Finite {i : I | x i ≠ 1}

def FiniteIndexSupport : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] [Finite I],
    ∀ x : ∀ i, G i, Set.Finite {i : I | x i ≠ 1}

/-- A precise sufficient condition for the source's "usually smaller". -/
def InfiniteProductHasInfiniteSupport : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)]
    [Infinite I] [∀ i, Nontrivial (G i)],
    ∃ x : ∀ i, G i, ¬ Set.Finite {i : I | x i ≠ 1}

def DirectSumInclusionType : Type (max u v + 1) :=
  ∀ (I : Type u) (A : I → Type v) [∀ i, AddCommGroup (A i)],
    DirectSum I A →+ (∀ i, A i)

def directSumInclusionValue : DirectSumInclusionType.{u, v} :=
  fun _ A _ => DirectSum.coeFnAddMonoidHom A

/-- The additive direct sum embeds as precisely the finite-support tuples.
Together injectivity and the range formula identify it with that subgroup. -/
def DirectSumIdentification : Prop :=
  ∀ (I : Type u) (A : I → Type v) [∀ i, AddCommGroup (A i)],
    Function.Injective (directSumInclusionValue I A) ∧
    (∀ x : ∀ i, A i,
      (∃ s : DirectSum I A, directSumInclusionValue I A s = x) ↔
        Set.Finite {i : I | x i ≠ 0})

def FiniteDirectSumIsProduct : Prop :=
  ∀ (I : Type u) (A : I → Type v) [∀ i, AddCommGroup (A i)] [Finite I],
    Function.Bijective (directSumInclusionValue I A)

def InfiniteDirectSumIsProper : Prop :=
  ∀ (I : Type u) (A : I → Type v) [∀ i, AddCommGroup (A i)]
    [Infinite I] [∀ i, Nontrivial (A i)],
    ¬ Function.Surjective (directSumInclusionValue I A)

end Specs.D07.Ch04.DirectProducts
