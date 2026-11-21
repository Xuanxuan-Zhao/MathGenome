import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanMatrix
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Independent statement of LA-E05 (res:E05, source lines 2170–2241).
The diagram is classified with its arrows, by an equivalence of vertices.
Coordinate realization of all labels is allocated to LA-E06 and its children.
No classification assertion is assumed in the definitions below. -/
noncomputable section
namespace LieAlgebrasAndRepresentations

/-- Precisely the rank ranges in the finite Dynkin list. -/
inductive FiniteDynkinType where
  | A (n : ℕ) (hn : 1 ≤ n)
  | B (n : ℕ) (hn : 2 ≤ n)
  | C (n : ℕ) (hn : 2 ≤ n)
  | D (n : ℕ) (hn : 4 ≤ n)
  | E6 | E7 | E8 | F4 | G2

namespace FiniteDynkinType

def rank : FiniteDynkinType → ℕ
  | .A n _ | .B n _ | .C n _ | .D n _ => n
  | .E6 => 6 | .E7 => 7 | .E8 => 8 | .F4 => 4 | .G2 => 2

/-- Rows index coroots. With this convention the coordinate B and C models
have respectively Mathlib's `C` and `B` matrices. The actual matrix entries,
not the library's names, fix this convention. -/
def cartan : (t : FiniteDynkinType) → Matrix (Fin t.rank) (Fin t.rank) ℤ
  | .A n _ => CartanMatrix.A n
  | .B n _ => CartanMatrix.C n
  | .C n _ => CartanMatrix.B n
  | .D n _ => CartanMatrix.D n
  | .E6 => CartanMatrix.E 6
  | .E7 => CartanMatrix.E 7
  | .E8 => CartanMatrix.E 8
  | .F4 => CartanMatrix.F₄
  | .G2 => CartanMatrix.G₂

/-- Multiplicities and arrows recovered from the standard Cartan matrix.
For a nonzero edge the row with the more negative entry is the shorter root. -/
def diagram (t : FiniteDynkinType) : DynkinDiagram (Fin t.rank) :=
  ⟨fun i j => if i = j then 0 else (t.cartan i j * t.cartan j i).toNat,
   fun i j => i ≠ j ∧ t.cartan j i < t.cartan i j⟩

end FiniteDynkinType

/-- Isomorphism of diagrams including multiplicities and the directions of arrows. -/
def DynkinDiagram.Isomorphic {ι κ : Type*} (d : DynkinDiagram ι)
    (e : DynkinDiagram κ) : Prop :=
  ∃ f : ι ≃ κ, (∀ i j, d.edges i j = e.edges (f i) (f j)) ∧
    (∀ i j, d.arrow i j ↔ e.arrow (f i) (f j))

/-- Connected diagrams are nonempty. In particular, rank zero is not
incorrectly classified as a connected A-type diagram. -/
def DynkinDiagram.IsConnected {ι : Type*} (d : DynkinDiagram ι) : Prop :=
  Nonempty ι ∧ ∀ i j, Relation.EqvGen (fun x y => d.edges x y ≠ 0) i j

/-- Symmetric Gram matrix after scaling the basis vectors to norm one,
then multiplying the Gram matrix by two. Equivalently the scaled vectors
have squared length two. -/
def normalizedSimpleGram {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : ι → E) : Matrix ι ι ℝ :=
  (2 : ℝ) • Matrix.gram ℝ (fun i => ‖b i‖⁻¹ • b i)

/-- The underlying simple graph, forgetting edge weights and arrows. -/
def simpleRootGraph {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : ι → E) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ inner ℝ (b i) (b j) ≠ 0
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa [real_inner_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

namespace DynkinExhaustionSpecs
universe u w z

/-- The complete exhaustion assertion, without any additional Cartan or
classification certificate in the hypotheses. Finiteness of the index is
already forced by the finite spanning root system and the basis. -/
def exhaustionType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R v b →
  (dynkinDiagram b).IsConnected →
  ∃ t : FiniteDynkinType, (dynkinDiagram b).Isomorphic t.diagram

/-- Distinct entries of the list have distinct oriented diagrams except
for B₂ and C₂, where the vertices exchange. -/
def uniquenessType : Prop :=
  ∀ t s : FiniteDynkinType, t.diagram.Isomorphic s.diagram →
    t = s ∨
    (t = .B 2 (by decide) ∧ s = .C 2 (by decide)) ∨
    (t = .C 2 (by decide) ∧ s = .B 2 (by decide))

/-- The rank-two B/C coincidence preserves the full arrow data under
interchanging the two vertices. -/
def bcTwoType : Prop :=
  (FiniteDynkinType.B 2 (by decide)).diagram.Isomorphic
    (FiniteDynkinType.C 2 (by decide)).diagram

/-- Positivity and the exact entry formula needed by the graph exclusions. -/
def normalizedGramType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} [Finite ι] (R : Set E), IsRootSystem R →
  ∀ v, RootRegular R v → ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R v b →
    (normalizedSimpleGram b).PosDef ∧
    (∀ i, normalizedSimpleGram b i i = 2) ∧
    (∀ i j, i ≠ j → normalizedSimpleGram b i j =
      -Real.sqrt ((dynkinDiagram b).edges i j : ℝ))

/-- Every nonempty finite induced subdiagram has a vertex with at most
one neighbor in that subdiagram. This is a forest criterion. -/
def thinVertexType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R v b →
  ∀ s : Finset ι, s.Nonempty → ∃ i ∈ s, ∀ j ∈ s, ∀ k ∈ s,
    (dynkinDiagram b).edges i j ≠ 0 → (dynkinDiagram b).edges i k ≠ 0 → j = k

/-- A vertex cannot have four distinct neighbors, even with further edges
between the retained vertices. -/
def noFourNeighborsType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R v b →
  ∀ e : Fin 5 ↪ ι, ¬ ∀ j : Fin 5, j ≠ 0 →
    (dynkinDiagram b).edges (e 0) (e j) ≠ 0

/-- No edge may be attached to either endpoint of a triple edge.
The universal embedding includes both choices of endpoint and any extra edge. -/
def tripleEdgeType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R v b →
  ∀ e : Fin 3 ↪ ι, (dynkinDiagram b).edges (e 0) (e 1) = 3 →
    (dynkinDiagram b).edges (e 1) (e 2) = 0

/-- The graph-theoretic conclusion used when extracting chains and arms. -/
def treeType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R v b →
    (simpleRootGraph b).IsAcyclic ∧
    ((dynkinDiagram b).IsConnected → (simpleRootGraph b).IsTree)

/-- A connected diagram with a triple edge is the full oriented G₂ diagram. -/
def tripleClassificationType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R v b →
    (dynkinDiagram b).IsConnected →
    (∃ i j, (dynkinDiagram b).edges i j = 3) →
    (dynkinDiagram b).Isomorphic FiniteDynkinType.G2.diagram

/-- Sorted positive arm lengths permitted by the branch Schur complement. -/
def armLengthsType : Prop :=
  ∀ a b c : ℕ, 1 ≤ a → a ≤ b → b ≤ c →
    (1 < (1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) + 1 / ((c : ℝ) + 1)) ↔
      a = 1 ∧ (b = 1 ∨ (b = 2 ∧ (c = 2 ∨ c = 3 ∨ c = 4))))

/-- The remaining numerical restriction for a chain with one double edge. -/
def doubleChainType : Prop :=
  ∀ p q : ℕ, 1 ≤ p → 1 ≤ q →
    (0 < (((p : ℝ) + 1) * ((q : ℝ) + 1) - 2 * p * q) ↔
      p = 1 ∨ q = 1 ∨ (p = 2 ∧ q = 2))

/-- The total multiplicity of edges from a retained path to distinct
external vertices is less than four. Each external vertex is counted once,
at any chosen vertex of attachment. This includes paths consisting of one vertex. -/
def pathAttachmentBoundType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R v b →
  ∀ (n : ℕ) {κ : Type z} [Fintype κ] (e : Fin (n + 1) ⊕ κ ↪ ι),
    (∀ i j : Fin (n + 1), i.val + 1 = j.val →
      (dynkinDiagram b).edges (e (.inl i)) (e (.inl j)) ≠ 0) →
  ∀ a : κ → Fin (n + 1),
    (∑ k, ((dynkinDiagram b).edges (e (.inl (a k))) (e (.inr k)) : ℝ)) < 4

end DynkinExhaustionSpecs
end LieAlgebrasAndRepresentations
