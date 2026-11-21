import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExceptionalCoordinateGF
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalCoordinateRoots
import Mathlib.Topology.Instances.Int

/-! res:E06, expanded source lines 2317–2371. Coordinate indices here start
at zero. All E-series objects are the displayed coordinate sets, not objects
chosen by their cardinality or by an assumed root-system certificate. -/
noncomputable section
namespace LieAlgebrasAndRepresentations.ExceptionalE
open Set Module
open ExceptionalGF (QVec Space unit sign realize)

/-- The source's two cosets of the even-sum integer lattice. -/
def lattice : Set (Space 8) :=
  {x | (∃ z : Fin 8 → ℤ, Even (∑ i, z i) ∧ ∀ i, x i = (z i : ℝ)) ∨
    (∃ z : Fin 8 → ℤ, Even (∑ i, z i) ∧ ∀ i, x i = (z i : ℝ) + 1 / 2)}

def integralList : Finset (QVec 8) :=
  ((Finset.univ : Finset ((Fin 8 × Fin 8) × (Bool × Bool))).filter
    (fun p => p.1.1 < p.1.2)).image
    (fun p => sign p.2.1 • unit p.1.1 + sign p.2.2 • unit p.1.2)

def halfList : Finset (QVec 8) :=
  ((Finset.univ : Finset (Fin 8 → Bool)).filter
    (fun b => (∑ i, if b i then (1 : ℕ) else 0) % 2 = 0)).image
      (fun b i => sign (b i) / 2)

def e8List : Finset (QVec 8) := integralList ∪ halfList
def e7List : Finset (QVec 8) := e8List.filter (fun x => x 6 + x 7 = 0)
def e6List : Finset (QVec 8) := e7List.filter (fun x => x 5 = x 6)

def e8Roots : Set (Space 8) := realize '' (e8List : Set (QVec 8))
def e7AmbientRoots : Set (Space 8) := realize '' (e7List : Set (QVec 8))
def e6AmbientRoots : Set (Space 8) := realize '' (e6List : Set (QVec 8))

def e7Space : Submodule ℝ (Space 8) where
  carrier := {x | x 6 + x 7 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x 6 + x 7 = 0 at hx
    change y 6 + y 7 = 0 at hy
    change (x 6 + y 6) + (x 7 + y 7) = 0
    linarith
  smul_mem' := by
    intro t x hx
    change t * x 6 + t * x 7 = 0
    rw [← mul_add, hx, mul_zero]

def e6Space : Submodule ℝ (Space 8) where
  carrier := {x | x 6 + x 7 = 0 ∧ x 5 = x 6}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · change (x 6 + y 6) + (x 7 + y 7) = 0
      linarith [hx.1, hy.1]
    · change x 5 + y 5 = x 6 + y 6
      rw [hx.2, hy.2]
  smul_mem' := by
    intro t x hx
    constructor
    · change t * x 6 + t * x 7 = 0
      rw [← mul_add, hx.1, mul_zero]
    · change t * x 5 = t * x 6
      rw [hx.2]

def e7Roots : Set e7Space := {x | (x : Space 8) ∈ e8Roots}
def e6Roots : Set e6Space := {x | (x : Space 8) ∈ e8Roots}

def simpleQ : Fin 8 → QVec 8 :=
  ![![1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,1/2],
    ![1,1,0,0,0,0,0,0], ![-1,1,0,0,0,0,0,0],
    ![0,-1,1,0,0,0,0,0], ![0,0,-1,1,0,0,0,0],
    ![0,0,0,-1,1,0,0,0], ![0,0,0,0,-1,1,0,0],
    ![0,0,0,0,0,-1,1,0]]

def e8Simple (i : Fin 8) : Space 8 := realize (simpleQ i)
def e7Simple (i : Fin 7) : e7Space :=
  ⟨e8Simple i.castSucc, by
    fin_cases i <;> norm_num [e8Simple, simpleQ, realize, e7Space]⟩
def e6Simple (i : Fin 6) : e6Space :=
  ⟨e8Simple (i.castLE (by decide)), by
    fin_cases i <;> norm_num [e8Simple, simpleQ, realize, e6Space]⟩

def e8Regular : Space 8 := realize ![0,1,2,3,4,5,6,23]
def e7Regular : e7Space :=
  ⟨realize ![0,1,2,3,4,5,-17/2,17/2], by norm_num [e7Space, realize]⟩
def e6Regular : e6Space :=
  ⟨realize ![0,1,2,3,4,-4,-4,4], by norm_num [e6Space, realize]⟩

/-- The E₈ tree in the order of the source's simple roots; restricting to
the first seven or six vertices gives E₇ or E₆. The branch is vertex 3. -/
def adjacent (i j : Fin 8) : Prop :=
  (i = 0 ∧ j = 2) ∨ (j = 0 ∧ i = 2) ∨
  (i = 1 ∧ j = 3) ∨ (j = 1 ∧ i = 3) ∨
  (2 ≤ i.val ∧ i.val + 1 = j.val) ∨ (2 ≤ j.val ∧ j.val + 1 = i.val)

instance (i j : Fin 8) : Decidable (adjacent i j) := by
  unfold adjacent
  infer_instance

namespace Specs

/-- Additive full-rank discrete lattice, with integral pairing and even norm. -/
def latticeType : Prop :=
  (0 : Space 8) ∈ lattice ∧
  (∀ x ∈ lattice, ∀ y ∈ lattice, x + y ∈ lattice) ∧
  (∀ x ∈ lattice, -x ∈ lattice) ∧
  DiscreteTopology lattice ∧ Submodule.span ℝ lattice = ⊤ ∧
  (∀ x ∈ lattice, ∀ y ∈ lattice, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) ∧
  (∀ x ∈ lattice, ∃ z : ℤ, inner ℝ x x = 2 * (z : ℝ))

def normTwoType : Prop :=
  {x ∈ lattice | inner ℝ x x = 2} = e8Roots

def e8Axioms : Prop := IsRootSystem e8Roots
def e7Axioms : Prop := IsRootSystem e7Roots
def e6Axioms : Prop := IsRootSystem e6Roots

def e8Count : Prop := e8Roots.ncard = 240 ∧
  (realize '' (integralList : Set (QVec 8))).ncard = 112 ∧
  (realize '' (halfList : Set (QVec 8))).ncard = 128 ∧ Disjoint integralList halfList

def e7Count : Prop := e7Roots.ncard = 126 ∧
  (e7List ∩ integralList).card = 62 ∧
  ((e7List ∩ integralList).filter (fun x => x 6 = 0 ∧ x 7 = 0)).card = 60 ∧
  ((e7List ∩ integralList).filter (fun x => x 6 ≠ 0 ∨ x 7 ≠ 0)).card = 2 ∧
  (e7List ∩ halfList).card = 64

def e6Count : Prop := e6Roots.ncard = 72 ∧
  (e6List ∩ integralList).card = 40 ∧ (e6List ∩ halfList).card = 32

def e8Basis : Prop := RootRegular e8Roots e8Regular ∧
  ∃ b : Basis (Fin 8) ℝ (Space 8), (∀ i, b i = e8Simple i) ∧
    IsSimpleBasis e8Roots e8Regular b
def e7Basis : Prop := RootRegular e7Roots e7Regular ∧
  ∃ b : Basis (Fin 7) ℝ e7Space, (∀ i, b i = e7Simple i) ∧
    IsSimpleBasis e7Roots e7Regular b
def e6Basis : Prop := RootRegular e6Roots e6Regular ∧
  ∃ b : Basis (Fin 6) ℝ e6Space, (∀ i, b i = e6Simple i) ∧
    IsSimpleBasis e6Roots e6Regular b

def e8Diagram : Prop :=
  (∀ i j, cartanMatrix e8Simple i j = if i = j then 2 else if adjacent i j then -1 else 0) ∧
  (∀ i j, (dynkinDiagram e8Simple).edges i j = if adjacent i j then 1 else 0) ∧
  (∀ i j, ¬ (dynkinDiagram e8Simple).arrow i j)
def e7Diagram : Prop :=
  (∀ i j, cartanMatrix e7Simple i j =
    if i = j then 2 else if adjacent i.castSucc j.castSucc then -1 else 0) ∧
  (∀ i j, (dynkinDiagram e7Simple).edges i j = if adjacent i.castSucc j.castSucc then 1 else 0) ∧
  (∀ i j, ¬ (dynkinDiagram e7Simple).arrow i j)
def e6Diagram : Prop :=
  (∀ i j, cartanMatrix e6Simple i j = if i = j then 2 else
    if adjacent (i.castLE (by decide)) (j.castLE (by decide)) then -1 else 0) ∧
  (∀ i j, (dynkinDiagram e6Simple).edges i j =
    if adjacent (i.castLE (by decide)) (j.castLE (by decide)) then 1 else 0) ∧
  (∀ i j, ¬ (dynkinDiagram e6Simple).arrow i j)

/-- The complete finite list in res:E05 is realized by the source's explicit
coordinate systems, with its rank ranges, counts, and simple diagrams. -/
def realizationsType : Prop :=
  (ClassicalCoordinates.Specs.rootSystemAType ∧ ClassicalCoordinates.Specs.countAType ∧
    ClassicalCoordinates.Specs.simpleDiagramAType) ∧
  (ClassicalCoordinates.Specs.rootSystemBType ∧ ClassicalCoordinates.Specs.countBType ∧
    ClassicalCoordinates.Specs.simpleDiagramBType) ∧
  (ClassicalCoordinates.Specs.rootSystemCType ∧ ClassicalCoordinates.Specs.countCType ∧
    ClassicalCoordinates.Specs.simpleDiagramCType) ∧
  (ClassicalCoordinates.Specs.rootSystemDType ∧ ClassicalCoordinates.Specs.countDType ∧
    ClassicalCoordinates.Specs.simpleDiagramDType) ∧
  (ExceptionalGF.Specs.g2Axioms ∧ ExceptionalGF.Specs.g2Count ∧
    ExceptionalGF.Specs.g2Basis ∧ ExceptionalGF.Specs.g2Diagram) ∧
  (ExceptionalGF.Specs.f4Axioms ∧ ExceptionalGF.Specs.f4Count ∧
    ExceptionalGF.Specs.f4Basis ∧ ExceptionalGF.Specs.f4Diagram) ∧
  (e8Axioms ∧ e8Count ∧ e8Basis ∧ e8Diagram) ∧
  (e7Axioms ∧ e7Count ∧ e7Basis ∧ e7Diagram) ∧
  (e6Axioms ∧ e6Count ∧ e6Basis ∧ e6Diagram)

end Specs
end LieAlgebrasAndRepresentations.ExceptionalE
