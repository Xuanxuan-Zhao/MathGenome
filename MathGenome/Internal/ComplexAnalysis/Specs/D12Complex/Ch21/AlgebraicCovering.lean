import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.FiniteExceptionalSet
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.SimpleRootBranches
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.CoveringHomotopies
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermsContinuation
import Mathlib.Topology.Homotopy.Path

/-! Independent statements for paper.tex:3606–3623, D12.21.03.
The curve has the induced topology from the literal subset of ℂ × ℂ.
An atlas is supplied without assuming that the curve is connected.
Root germs are actual neighborhood-equivalence classes, with local
holomorphic representatives satisfying the original polynomial equation. -/

noncomputable section
open Set
open scoped Topology

namespace D12Complex.AlgebraicCovering

abbrev fiber := Specs.D12Complex.Ch21.FiniteExceptionalSet.fiber_value
abbrev exceptionalSet := Specs.D12Complex.Ch21.FiniteExceptionalSet.exceptionalSet_value

def baseSet (P : Polynomial (Polynomial ℂ)) : Set ℂ := (exceptionalSet P)ᶜ
abbrev Base (P : Polynomial (Polynomial ℂ)) : Type := baseSet P
abbrev Curve (P : Polynomial (Polynomial ℂ)) :=
  {x : ℂ × ℂ // x.1 ∈ baseSet P ∧ (fiber P x.1).eval x.2 = 0}
def projection (P : Polynomial (Polynomial ℂ)) (x : Curve P) : Base P :=
  ⟨x.val.1, x.property.1⟩

/-- All roots on one base disk, with disjoint isolating neighborhoods. -/
structure LocalBranches (P : Polynomial (Polynomial ℂ)) (d : ℕ) (a : ℂ) where
  radius : ℝ
  radius_pos : 0 < radius
  base_subset : Metric.ball a radius ⊆ baseSet P
  branch : Fin d → ℂ → ℂ
  V : Fin d → Set ℂ
  open_V : ∀ i, IsOpen (V i)
  center_mem : ∀ i, branch i a ∈ V i
  disjoint : Pairwise (fun i j => Disjoint (V i) (V j))
  holomorphic : ∀ i, HolomorphicOn (Metric.ball a radius) (branch i)
  mapsTo : ∀ i, MapsTo (branch i) (Metric.ball a radius) (V i)
  unique : ∀ z ∈ Metric.ball a radius, ∀ i, ∀ w ∈ V i,
    (fiber P z).eval w = 0 ↔ w = branch i z
  exhaustive : ∀ z ∈ Metric.ball a radius, ∀ w : ℂ,
    (fiber P z).eval w = 0 ↔ ∃ i, w = branch i z
  injective : ∀ z ∈ Metric.ball a radius, Function.Injective (fun i => branch i z)

def IsRootGerm (P : Polynomial (Polynomial ℂ)) (a : ℂ)
    (g : HolomorphicGerm a) : Prop :=
  ∃ (U : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn U f) (ha : a ∈ U),
    HolomorphicGerm.ofFunction f hf ha = g ∧
      ∀ z ∈ U, (fiber P z).eval (f z) = 0

def RootGerm (P : Polynomial (Polynomial ℂ)) (a : ℂ) :=
  {g : HolomorphicGerm a // IsRootGerm P a g}

end D12Complex.AlgebraicCovering

namespace Specs.D12Complex.Ch21.AlgebraicCovering
open _root_.D12Complex _root_.D12Complex.AlgebraicCovering

-- Canonical objects, shared by subsequent algebraic-surface goals.
def baseSet_type := Polynomial (Polynomial ℂ) → Set ℂ
def baseSet_value : baseSet_type := fun P =>
  (Specs.D12Complex.Ch21.FiniteExceptionalSet.exceptionalSet_value P)ᶜ
def Base_type := Polynomial (Polynomial ℂ) → Type
def Base_value : Base_type := fun P => baseSet_value P
def Curve_type := Polynomial (Polynomial ℂ) → Type
def Curve_value : Curve_type := fun P =>
  {x : ℂ × ℂ // x.1 ∈ baseSet_value P ∧
    (Specs.D12Complex.Ch21.FiniteExceptionalSet.fiber_value P x.1).eval x.2 = 0}
def projection_type := (P : Polynomial (Polynomial ℂ)) → Curve P → Base P
def projection_value : projection_type := fun _ x => ⟨x.val.1, x.property.1⟩
def IsRootGerm_type := Polynomial (Polynomial ℂ) → (a : ℂ) → HolomorphicGerm a → Prop
def IsRootGerm_value : IsRootGerm_type := fun P a g =>
  ∃ (U : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn U f) (ha : a ∈ U),
    HolomorphicGerm.ofFunction f hf ha = g ∧ ∀ z ∈ U,
      (Specs.D12Complex.Ch21.FiniteExceptionalSet.fiber_value P z).eval (f z) = 0
def RootGerm_type := Polynomial (Polynomial ℂ) → ℂ → Type
def RootGerm_value : RootGerm_type := fun P a =>
  {g : HolomorphicGerm a // IsRootGerm_value P a g}

def base_domain_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d → IsDomain (baseSet P)

def local_branches_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    ∀ a ∈ baseSet P, Nonempty (LocalBranches P d a)

/-- Exactly d sheets; empty fibers are excluded by the fiber equivalence. -/
def covering_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    Ch20.IsCovering (projection P) ∧
      ∀ a : Base P, Nonempty ((projection P ⁻¹' {a}) ≃ Fin d)

/-- The subspace separation/countability, projection charts, and holomorphic
second coordinate state the holomorphic-covering conclusion explicitly. -/
def complex_atlas_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    T2Space (Curve P) ∧ SecondCountableTopology (Curve P) ∧
      ∃ A : Set (Surfaces.ComplexChart (Curve P)), Surfaces.IsAtlas A ∧
        ∀ e ∈ A,
          (∀ x ∈ e.val.source, e.val x = x.val.1) ∧
          HolomorphicOn e.val.target (fun z => (e.val.symm z).val.2)

/-- Values identify the actual root germs with the covering fiber. -/
def root_germs_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d → ∀ a : Base P,
    ∃ e : RootGerm P (a : ℂ) ≃ (projection P ⁻¹' {a}),
      ∀ g, (e g).val.val.2 = g.val.value

/-- Continuation is a locally represented family of actual holomorphic germs,
not merely a continuous selection of root values. -/
def branch_continuation_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    ∀ (a b : Base P) (γ : Path a b) (g : RootGerm P (a : ℂ)),
      ∃ Φ : GermFamily (fun t => (γ t : ℂ)),
        IsContinuation (baseSet P) (fun t => (γ t : ℂ))
          ((congrArg Subtype.val γ.source).symm ▸ g.val) Φ ∧ ∀ t, IsRootGerm P (γ t : ℂ) (Φ t)

/-- The terminal germ describes the action, and all laws use actual based
loops and based homotopies. Multiplication of permutations composes functions. -/
def monodromy_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d → ∀ a : Base P,
    ∃ M : Path a a → Equiv.Perm (RootGerm P (a : ℂ)),
      (∀ γ η, γ.Homotopic η → M γ = M η) ∧
      (∀ γ, M γ.symm = (M γ)⁻¹) ∧
      (∀ γ η, M (γ.trans η) = M η * M γ) ∧
      ∀ γ g, ∃ Φ : GermFamily (fun t => (γ t : ℂ)),
        IsContinuation (baseSet P) (fun t => (γ t : ℂ))
          ((congrArg Subtype.val γ.source).symm ▸ g.val) Φ ∧
        (∀ t, IsRootGerm P (γ t : ℂ) (Φ t)) ∧
        (congrArg Subtype.val γ.target ▸ Φ 1) = (M γ g).val

end Specs.D12Complex.Ch21.AlgebraicCovering
