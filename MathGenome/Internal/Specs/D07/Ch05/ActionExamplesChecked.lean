import MathGenome.Internal.Specs.D07.Ch05.Burnside
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Data.Fintype.Pi

/-! Independent specification of paper.tex:923–930.
`DihedralGroup 4` has eight elements. Its `sr j` is s r^j,
so the source's r^j s is `sr (-j)`. Colors are labelled by `Fin q`;
no positivity assumption is imposed on q. Cycles include singleton cycles.
-/
namespace Specs.D07.Ch05.ActionExamplesChecked

abbrev Vertex := ZMod 4
abbrev SquareGroup := DihedralGroup 4
abbrev Rotations := Multiplicative (ZMod 4)

/-- The vertex action, with the library's s r^j convention. -/
def vertexMap : SquareGroup → Vertex → Vertex
  | .r j, i => j + i
  | .sr j, i => -(j + i)

instance vertexAction : MulAction SquareGroup Vertex where
  smul := vertexMap
  one_smul i := by change (0 : Vertex) + i = i; exact zero_add i
  mul_smul g h i := by
    change vertexMap (g*h) i = vertexMap g (vertexMap h i)
    cases g <;> cases h <;>
      simp [vertexMap, add_assoc, sub_eq_add_neg, add_comm, add_left_comm]

/-- Identification of the cyclic rotation group with the rotation subgroup. -/
def rotationInclusion : Rotations →* SquareGroup where
  toFun j := .r j.toAdd
  map_one' := rfl
  map_mul' _ _ := rfl

instance rotationVertexAction : MulAction Rotations Vertex :=
  MulAction.compHom Vertex rotationInclusion

/-- Pullback of colors along the inverse vertex motion. -/
def Coloring (q : ℕ) := Vertex → Fin q

instance (q : ℕ) : Fintype (Coloring q) := inferInstanceAs (Fintype (Vertex → Fin q))
instance (q : ℕ) : DecidableEq (Coloring q) := inferInstanceAs (DecidableEq (Vertex → Fin q))

instance coloringAction (G : Type*) [Group G] [MulAction G Vertex] (q : ℕ) :
    MulAction G (Coloring q) where
  smul g c := fun i => c (g⁻¹ • i)
  one_smul c := by change (fun i => c ((1 : G)⁻¹ • i)) = c; simp
  mul_smul g h c := by
    change (fun i => c ((g*h)⁻¹ • i)) = (fun i => c (h⁻¹ • (g⁻¹ • i)))
    simp [mul_smul]

/-- Actual permutation of vertices, not a permutation of colors. -/
def vertexPermutation (g : SquareGroup) : Equiv.Perm Vertex :=
  MulAction.toPermHom SquareGroup Vertex g

abbrev Cycles (g : SquareGroup) :=
  Quotient (Equiv.Perm.SameCycle.setoid (vertexPermutation g))

/-- Singleton orbits count as one cycle. -/
noncomputable def cycleCount (g : SquareGroup) : ℕ := Nat.card (Cycles g)

def rotationOrbits (q : ℕ) := MulAction.orbitRel.Quotient Rotations (Coloring q)
def squareOrbits (q : ℕ) := MulAction.orbitRel.Quotient SquareGroup (Coloring q)

def oneRed {q : ℕ} (red blue : Fin q) : Coloring q := fun i => if i = 0 then red else blue

def VertexFormulas : Prop :=
  (∀ i : Vertex, (DihedralGroup.r 1 : SquareGroup) • i = i + 1) ∧
  (∀ i : Vertex, (DihedralGroup.sr 0 : SquareGroup) • i = -i) ∧
  (DihedralGroup.r 1 : SquareGroup)^4 = 1 ∧
  (DihedralGroup.sr 0 : SquareGroup)^2 = 1 ∧
  (DihedralGroup.sr 0 : SquareGroup) * .r 1 * .sr 0 = (.r 1 : SquareGroup)⁻¹

def RotationIdentification : Prop :=
  Function.Injective rotationInclusion ∧
  (∀ g : SquareGroup, g ∈ rotationInclusion.range ↔ ∃ j : Vertex, g = .r j) ∧
  Nat.card Rotations = 4 ∧ Nat.card SquareGroup = 8 ∧
  (∀ (j : Rotations) (i : Vertex), j • i = j.toAdd + i)

def VertexStabilizers : Prop :=
  (∀ g : SquareGroup, g ∈ MulAction.stabilizer SquareGroup (0 : Vertex) ↔
    g = 1 ∨ g = .sr 0) ∧
  (∀ j : Vertex,
    ((DihedralGroup.r j : SquareGroup) • (0 : Vertex) = 0 ↔ j = 0) ∧
    (((DihedralGroup.r j : SquareGroup) * .sr 0) • (0 : Vertex) = 0 ↔ j = 0)) ∧
  MulAction.stabilizer Rotations (0 : Vertex) = ⊥

/-- These are the action laws and the exact color-preserving stabilizer. -/
def ColoringLaws : Prop :=
  ∀ q : ℕ,
    (∀ (g : SquareGroup) (c : Coloring q) (i : Vertex), (g • c) i = c (g⁻¹ • i)) ∧
    (∀ c : Coloring q, (1 : SquareGroup) • c = c) ∧
    (∀ (g h : SquareGroup) (c : Coloring q), (g*h) • c = g • (h • c)) ∧
    (∀ (g : SquareGroup) (c : Coloring q),
      g ∈ MulAction.stabilizer SquareGroup c ↔ ∀ i : Vertex, c (g • i) = c i) ∧
    (∀ (g : Rotations) (c : Coloring q) (i : Vertex), (g • c) i = c (g⁻¹ • i))

def SpecialColoringStabilizers : Prop :=
  (∀ (q : ℕ) (a : Fin q),
    MulAction.stabilizer SquareGroup (show Coloring q from fun _ : Vertex => a) = ⊤ ∧
    MulAction.stabilizer Rotations (show Coloring q from fun _ : Vertex => a) = ⊤) ∧
  (∀ (q : ℕ) (red blue : Fin q), red ≠ blue →
    MulAction.stabilizer SquareGroup (oneRed red blue) =
      MulAction.stabilizer SquareGroup (0 : Vertex)) ∧
  (∀ (q : ℕ) (red blue : Fin q), red ≠ blue →
    MulAction.stabilizer Rotations (oneRed red blue) = ⊥)

def FixedIffCycleConstant : Prop :=
  ∀ (q : ℕ) (g : SquareGroup) (c : Coloring q),
    g • c = c ↔ ∀ i j : Vertex, (vertexPermutation g).SameCycle i j → c i = c j

def FixedColoringCount : Prop :=
  ∀ (q : ℕ) (g : SquareGroup),
    Nat.card {c : Coloring q // g • c = c} = q ^ cycleCount g

def CycleCounts : Prop :=
  cycleCount (.r 0) = 4 ∧ cycleCount (.r 1) = 1 ∧
  cycleCount (.r 2) = 2 ∧ cycleCount (.r 3) = 1 ∧
  cycleCount (.sr 0) = 3 ∧ cycleCount (.sr 1) = 2 ∧
  cycleCount (.sr 2) = 3 ∧ cycleCount (.sr 3) = 2

def OrbitFormulas : Prop :=
  ∀ q : ℕ,
    Nat.card (rotationOrbits q) = (q^4 + q^2 + 2*q) / 4 ∧
    Nat.card (squareOrbits q) = (q^4 + 2*q^3 + 3*q^2 + 2*q) / 8

/-- Both averages are exact, including the empty color set. -/
def ExactAverages : Prop :=
  ∀ q : ℕ,
    4 * Nat.card (rotationOrbits q) = q^4 + q^2 + 2*q ∧
    8 * Nat.card (squareOrbits q) = q^4 + 2*q^3 + 3*q^2 + 2*q

def ThreeColors : Prop :=
  Nat.card (rotationOrbits 3) = 24 ∧ Nat.card (squareOrbits 3) = 21 ∧
    Nat.card (rotationOrbits 3) ≠ Nat.card (squareOrbits 3)

/-- Reflection equivalence identifies some colorings that rotation equivalence does not. -/
def DifferentEquivalenceRelations : Prop :=
  (∀ c d : Coloring 3, MulAction.orbitRel Rotations (Coloring 3) c d →
    MulAction.orbitRel SquareGroup (Coloring 3) c d) ∧
  ∃ c d : Coloring 3, MulAction.orbitRel SquareGroup (Coloring 3) c d ∧
    ¬ MulAction.orbitRel Rotations (Coloring 3) c d

end Specs.D07.Ch05.ActionExamplesChecked
