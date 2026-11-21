import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.SupNormAlgebras
import Mathlib.Topology.ContinuousMap.Lattice

/-! Independent statements for paper.tex, `d10:16:closed-lattice`.
The algebra and uniform closure are the canonical chapter 16 objects.
Compactness imposes no separation condition. The continuous-map lattice
operations are pointwise: `|f| x = |f x|`, `(f ⊓ g) x = min (f x) (g x)`,
and `(f ⊔ g) x = max (f x) (g x)`.
-/

noncomputable section
open Set Filter
open scoped Topology
universe u

namespace Specs.D10Topology.Ch16.ClosedLattice
open SupNormAlgebras

def product_error_bound : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] (a b f g : C(X, ℝ)),
    ‖a * b - f * g‖ ≤ ‖a‖ * ‖b - g‖ + ‖g‖ * ‖a - f‖

def uniformClosure_subalgebra : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (A : RealFunctionAlgebra X), SupNormAlgebras.IsUnital A →
    ∃ B : RealFunctionAlgebra X,
      (B : Set C(X, ℝ)) = uniformClosure (A : Set C(X, ℝ)) ∧ SupNormAlgebras.IsUnital B

def uniformClosure_lattice : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (A : RealFunctionAlgebra X), SupNormAlgebras.IsUnital A →
    ∀ f g : C(X, ℝ), f ∈ uniformClosure (A : Set C(X, ℝ)) →
      g ∈ uniformClosure (A : Set C(X, ℝ)) →
      |f| ∈ uniformClosure (A : Set C(X, ℝ)) ∧
      f ⊓ g ∈ uniformClosure (A : Set C(X, ℝ)) ∧
      f ⊔ g ∈ uniformClosure (A : Set C(X, ℝ))

/-- The boundedness and product convergence used for uniform limits. -/
def uniform_limits_mul : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (F G : ℕ → C(X, ℝ)) (f g : C(X, ℝ)),
    TendstoUniformly (fun n => (F n : X → ℝ)) f atTop →
    TendstoUniformly (fun n => (G n : X → ℝ)) g atTop →
    (∃ M : ℝ, ∀ n, ‖F n‖ ≤ M) ∧
    TendstoUniformly (fun n x => F n x * G n x) (fun x => f x * g x) atTop

end Specs.D10Topology.Ch16.ClosedLattice
