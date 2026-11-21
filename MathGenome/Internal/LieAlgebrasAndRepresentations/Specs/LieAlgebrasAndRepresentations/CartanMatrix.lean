import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RankTwoRootSystems
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Algebra.Order.Floor.Ring

/-! LA-E04, res:E04, expanded source lines 2146–2168.
The basis may have any finite index type, hence includes the empty diagram.
Cartan rows index coroots, as in the source. Diagram arrows point from longer
to shorter roots. The diagonal carries no graph edges. -/
noncomputable section
namespace LieAlgebrasAndRepresentations
open Set Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An indexed basis is the specified simple system, without extra choices or hypotheses. -/
def IsSimpleBasis {ι : Type*} (R : Set E) (v : E) (b : Basis ι ℝ E) : Prop :=
  Set.range b = simpleRoots R v

/-- The real Cartan matrix; integrality of its entries is a theorem. -/
def cartanMatrix {ι : Type*} (b : ι → E) : Matrix ι ι ℝ :=
  fun i j => rootCartan (b j) (b i)

/-- A Dynkin diagram is specified by its edge multiplicities and oriented arrows. -/
structure DynkinDiagram (ι : Type*) where
  edges : ι → ι → ℕ
  arrow : ι → ι → Prop

/-- Edge multiplicity is the Cartan product off the diagonal. Taking its floor
is only a total definition; the exact equality with that product is proved. -/
def dynkinDiagram {ι : Type*} (b : ι → E) : DynkinDiagram ι := by
  classical
  exact ⟨fun i j => if i = j then 0 else
    (⌊cartanMatrix b i j * cartanMatrix b j i⌋ : ℤ).toNat,
    fun i j => i ≠ j ∧ inner ℝ (b i) (b j) ≠ 0 ∧
      inner ℝ (b j) (b j) < inner ℝ (b i) (b i)⟩

/-- Connectedness in the graph with the stated edge multiplicities. -/
def DynkinConnected {ι : Type*} (b : ι → E) : ι → ι → Prop :=
  Relation.EqvGen (fun i j => (dynkinDiagram b).edges i j ≠ 0)

def dynkinComponent {ι : Type*} (b : ι → E) (i : ι) : Set ι :=
  {j | DynkinConnected b i j}

/-- The ambient span of one graph component. -/
def dynkinComponentSpan {ι : Type*} (b : ι → E) (i : ι) : Submodule ℝ E :=
  Submodule.span ℝ (b '' dynkinComponent b i)

/-- A graph block regarded as a Euclidean subspace. -/
def dynkinFactorSpace {ι : Type*} (b : ι → E) (A : Set ι) : Submodule ℝ E :=
  Submodule.span ℝ (b '' A)

def dynkinFactorRoots {ι : Type*} (R : Set E) (b : ι → E) (A : Set ι) :
    Set (dynkinFactorSpace b A) := {x | (x : E) ∈ R}

namespace CartanMatrixSpecs
universe u w

def cartanMatrixType : Type (max (u + 1) (w + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    {ι : Type w} → (ι → E) → Matrix ι ι ℝ

def cartanMatrixValue : cartanMatrixType := @cartanMatrix

def dynkinDiagramType : Type (max (u + 1) (w + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    {ι : Type w} → (ι → E) → DynkinDiagram ι

def dynkinDiagramValue : dynkinDiagramType := @dynkinDiagram

def diagonalType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Basis ι ℝ E, IsSimpleBasis R v b → ∀ i, cartanMatrix b i i = 2

def offDiagonalType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Basis ι ℝ E, IsSimpleBasis R v b →
    (∀ i j, ∃ z : ℤ, cartanMatrix b i j = (z : ℝ)) ∧
    (∀ i j, i ≠ j → cartanMatrix b i j ≤ 0)

def productType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Basis ι ℝ E, IsSimpleBasis R v b → ∀ i j, i ≠ j →
    cartanMatrix b i j * cartanMatrix b j i ∈ ({0,1,2,3} : Set ℝ)

def symmetrizationType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} [Fintype ι] [DecidableEq ι] (R : Set E),
  IsRootSystem R → ∀ v, RootRegular R v → ∀ b : Basis ι ℝ E,
  IsSimpleBasis R v b →
    let M := Matrix.diagonal (fun i => inner ℝ (b i) (b i)) * cartanMatrix b
    M = (2 : ℝ) • Matrix.gram ℝ b ∧ M.IsSymm ∧ M.PosDef

def diagramType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Basis ι ℝ E, IsSimpleBasis R v b →
    (∀ i, (dynkinDiagram b).edges i i = 0) ∧
    (∀ i j, i ≠ j → ((dynkinDiagram b).edges i j : ℝ) =
      cartanMatrix b i j * cartanMatrix b j i) ∧
    (∀ i j, (dynkinDiagram b).edges i j = (dynkinDiagram b).edges j i) ∧
    (∀ i j, (dynkinDiagram b).edges i j ≠ 0 ↔
      i ≠ j ∧ inner ℝ (b i) (b j) ≠ 0) ∧
    (∀ i j, (dynkinDiagram b).arrow i j ↔
      (dynkinDiagram b).edges i j ≠ 0 ∧
        inner ℝ (b j) (b j) < inner ℝ (b i) (b i))

/-- Identically indexed diagrams represent any graph isomorphism after
reindexing the second simple basis. The scale is constant on each component,
and the metric identity holds on the entire component subspace. -/
def reconstructionType.{t} : Prop :=
  ∀ {E : Type u} {F : Type t} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F],
  ∀ {ι : Type w} (R : Set E) (S : Set F), IsRootSystem R → IsRootSystem S →
  ∀ v z, RootRegular R v → RootRegular S z →
  ∀ (b : Basis ι ℝ E) (c : Basis ι ℝ F), IsSimpleBasis R v b → IsSimpleBasis S z c →
  (∀ i j, (dynkinDiagram b).edges i j = (dynkinDiagram c).edges i j) →
  (∀ i j, (dynkinDiagram b).arrow i j ↔ (dynkinDiagram c).arrow i j) →
  ∃ (f : E ≃ₗ[ℝ] F) (s : ι → ℝ),
    (∀ i, f (b i) = c i) ∧ f '' R = S ∧
    (∀ i, 0 < s i) ∧
    (∀ i j, DynkinConnected b i j → s i = s j) ∧
    ∀ i, ∀ x ∈ dynkinComponentSpan b i, ∀ y ∈ dynkinComponentSpan b i,
      inner ℝ (f x) (f y) = s i * inner ℝ x y

/-- Reconstruction under an arbitrary isomorphism of the vertex sets. -/
def reconstructionIsoType.{t,r} : Prop :=
  ∀ {E : Type u} {F : Type t} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F],
  ∀ {ι : Type w} {κ : Type r} (R : Set E) (S : Set F), IsRootSystem R → IsRootSystem S →
  ∀ v z, RootRegular R v → RootRegular S z →
  ∀ (b : Basis ι ℝ E) (c : Basis κ ℝ F), IsSimpleBasis R v b → IsSimpleBasis S z c →
  ∀ e : ι ≃ κ,
  (∀ i j, (dynkinDiagram b).edges i j = (dynkinDiagram c).edges (e i) (e j)) →
  (∀ i j, (dynkinDiagram b).arrow i j ↔ (dynkinDiagram c).arrow (e i) (e j)) →
  ∃ (f : E ≃ₗ[ℝ] F) (s : ι → ℝ),
    (∀ i, f (b i) = c (e i)) ∧ f '' R = S ∧
    (∀ i, 0 < s i) ∧
    (∀ i j, DynkinConnected b i j → s i = s j) ∧
    ∀ i, ∀ x ∈ dynkinComponentSpan b i, ∀ y ∈ dynkinComponentSpan b i,
      inner ℝ (f x) (f y) = s i * inner ℝ x y

/-- Graph components are precisely the irreducible orthogonal root factors,
including identification of every root with its component subspace. -/
def componentsType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Basis ι ℝ E, IsSimpleBasis R v b →
    (∀ i j, DynkinConnected b i j ↔ RootConnected R (b i) (b j)) ∧
    (∀ i x, x ∈ R → (x ∈ dynkinComponentSpan b i ↔ RootConnected R (b i) x)) ∧
    IsOrthogonalDecomposition R
      (Set.range (fun i => {x | x ∈ R ∧ x ∈ dynkinComponentSpan b i}))

/-- The Weyl group is the product of the Weyl groups of the components,
with the isomorphism given by restricting its actual action to each span. -/
def weylProductType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type w} (R : Set E), IsRootSystem R → ∀ v, RootRegular R v →
  ∀ b : Basis ι ℝ E, IsSimpleBasis R v b →
  ∃ φ : rootWeylGroup R ≃*
      (∀ A : Set.range (dynkinComponent b),
        rootWeylGroup (dynkinFactorRoots R b A.val)),
    ∀ (w : rootWeylGroup R) (A : Set.range (dynkinComponent b))
      (x : dynkinFactorSpace b A.val),
      (((φ w A).val x : dynkinFactorSpace b A.val) : E) = w.val (x : E)

end CartanMatrixSpecs
end LieAlgebrasAndRepresentations
