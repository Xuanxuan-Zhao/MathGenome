import MathGenome.Internal.Specs.D07.Ch17.IntertwinersEquivalence
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Matrix.Block

/-! Independent specification for K07.17.direct_sums, paper.tex:4707–4726.
The group and field are arbitrary. Only the matrix and finite basis assertions
use finite index types, including empty ones. Infinite sums use `DirectSum`.
-/
namespace Specs.D07.Ch17.DirectSums

universe u v w x t z y

open DirectSum

/-- Stability of an ordinary subspace under every group element. -/
def Invariant {K G E : Type*} [Field K] [Group G] [AddCommGroup E] [Module K E]
    (ρ : Representation K G E) (U : Submodule K E) : Prop :=
  ∀ g x, x ∈ U → ρ g x ∈ U

/-- The spans of the two blocks of a single chosen basis. -/
def leftSpan {K E ι κ : Type*} [Field K] [AddCommGroup E] [Module K E]
    (b : Module.Basis (ι ⊕ κ) K E) : Submodule K E :=
  Submodule.span K (b '' Set.range Sum.inl)

def rightSpan {K E ι κ : Type*} [Field K] [AddCommGroup E] [Module K E]
    (b : Module.Basis (ι ⊕ κ) K E) : Submodule K E :=
  Submodule.span K (b '' Set.range Sum.inr)

def ProductLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W),
    (∀ g p, (ρ.prod σ) g p = (ρ g p.1, σ g p.2)) ∧
    (ρ.prod σ) 1 = LinearMap.id ∧
    (∀ g h, (ρ.prod σ) (g * h) = ((ρ.prod σ) g).comp ((ρ.prod σ) h))

def ProductIntertwiners : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W),
    ρ.IsIntertwiningMap (ρ.prod σ) (LinearMap.inl K V W) ∧
    σ.IsIntertwiningMap (ρ.prod σ) (LinearMap.inr K V W) ∧
    (ρ.prod σ).IsIntertwiningMap ρ (LinearMap.fst K V W) ∧
    (ρ.prod σ).IsIntertwiningMap σ (LinearMap.snd K V W)

/-- The forward map of the equivariant equivalence is precisely addition. -/
def InternalEquivalence : Prop :=
  ∀ (K : Type u) (G : Type v) (E : Type w)
    [Field K] [Group G] [AddCommGroup E] [Module K E]
    (ρ : Representation K G E) (U W : Subrepresentation ρ),
    IsCompl U.toSubmodule W.toSubmodule →
    ∃ e : (U.toRepresentation.prod W.toRepresentation).Equiv ρ,
      ∀ p, e p = (p.1 : E) + (p.2 : E)

/-- Concatenating the given bases of invariant complements gives one basis
for all group elements, with the specified restriction matrices on its diagonal. -/
def ConcatenatedBlockBasis : Prop :=
  ∀ (K : Type u) (G : Type v) (E : Type w) (ι : Type t) (κ : Type z)
    [Field K] [Group G] [AddCommGroup E] [Module K E]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ρ : Representation K G E) (U W : Subrepresentation ρ)
    (_h : IsCompl U.toSubmodule W.toSubmodule)
    (bU : Module.Basis ι K U.toSubmodule) (bW : Module.Basis κ K W.toSubmodule),
    ∃ b : Module.Basis (ι ⊕ κ) K E,
      (∀ i, b (Sum.inl i) = (bU i : E)) ∧
      (∀ j, b (Sum.inr j) = (bW j : E)) ∧
      ∀ g, LinearMap.toMatrix b b (ρ g) = Matrix.fromBlocks
        (LinearMap.toMatrix bU bU (U.toRepresentation g)) 0 0
        (LinearMap.toMatrix bW bW (W.toRepresentation g))

/-- Both spans are complements, and common off-diagonal zero blocks are
exactly invariance of both spans, in the same basis and partition for every g. -/
def CommonBlockCriterion : Prop :=
  ∀ (K : Type u) (G : Type v) (E : Type w) (ι : Type t) (κ : Type z)
    [Field K] [Group G] [AddCommGroup E] [Module K E]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ρ : Representation K G E) (b : Module.Basis (ι ⊕ κ) K E),
    IsCompl (leftSpan b) (rightSpan b) ∧
    ((Invariant ρ (leftSpan b) ∧ Invariant ρ (rightSpan b)) ↔
      ∀ g, (∀ i j, LinearMap.toMatrix b b (ρ g) (Sum.inl i) (Sum.inr j) = 0) ∧
        (∀ j i, LinearMap.toMatrix b b (ρ g) (Sum.inr j) (Sum.inl i) = 0))

/-- One invariant block is equivalent to just the lower-left zero block. -/
def TriangularCriterion : Prop :=
  ∀ (K : Type u) (G : Type v) (E : Type w) (ι : Type t) (κ : Type z)
    [Field K] [Group G] [AddCommGroup E] [Module K E]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ρ : Representation K G E) (b : Module.Basis (ι ⊕ κ) K E),
    Invariant ρ (leftSpan b) ↔
      ∀ g j i, LinearMap.toMatrix b b (ρ g) (Sum.inr j) (Sum.inl i) = 0

/-- Any chosen finite basis of an invariant subspace extends to an adapted
finite basis of E; the complement is not assumed invariant. -/
def ExtendedTriangularBasis : Prop :=
  ∀ (K : Type u) (G : Type v) (E : Type w) (ι : Type t)
    [Field K] [Group G] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [Fintype ι] [DecidableEq ι]
    (ρ : Representation K G E) (U : Subrepresentation ρ)
    (bU : Module.Basis ι K U.toSubmodule),
    ∃ (n : ℕ) (b : Module.Basis (ι ⊕ Fin n) K E),
      (∀ i, b (Sum.inl i) = (bU i : E)) ∧
      leftSpan b = U.toSubmodule ∧
      ∀ g j i, LinearMap.toMatrix b b (ρ g) (Sum.inr j) (Sum.inl i) = 0

/-- In an arbitrary family the sum has the component action, equivariant
inclusions and projections, and exactly the finitely supported functions. -/
def ArbitraryDirectSum.{a,b,c,d} : Prop := by
  classical
  exact
  ∀ (K : Type a) (G : Type b) (ι : Type c) (V : ι → Type d)
    [Field K] [Group G] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (ρ : ∀ i, Representation K G (V i)),
    (∀ g (x : ⨁ i, V i) i, Representation.directSum ρ g x i = ρ i g (x i)) ∧
    (∀ i, (ρ i).IsIntertwiningMap (Representation.directSum ρ) (DirectSum.lof K ι V i)) ∧
    (∀ i, (Representation.directSum ρ).IsIntertwiningMap (ρ i)
      (DirectSum.component K ι V i)) ∧
    (∀ (f : ∀ i, V i), (∃ x : ⨁ i, V i, ∀ i, x i = f i) ↔ Set.Finite {i | f i ≠ 0})

/-- The full infinite product can be strictly larger, even for scalar copies. -/
def InfiniteProductBoundary : Prop :=
  ¬ ∃ x : ⨁ _ : ℕ, ℚ, ∀ i, x i = 1

/-- Invariance of the first summand does not force invariance of its
chosen vector-space complement. The example uses a genuine group action. -/
def NonInvariantComplement : Prop :=
  ∃ (G : Type) (_ : Group G) (ρ : Representation ℚ G (ℚ × ℚ))
    (U W : Submodule ℚ (ℚ × ℚ)),
    IsCompl U W ∧ Invariant ρ U ∧ ¬ Invariant ρ W

end Specs.D07.Ch17.DirectSums
