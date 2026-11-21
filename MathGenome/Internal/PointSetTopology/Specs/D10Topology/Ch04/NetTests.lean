import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetsAndSubnets
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.ContinuityTests

/-!
Independent statements for paper.tex, d10:04:closure-net and
 d10:04:continuity-net. Nets use the upstream neighborhood definition of
convergence. Every quantified index has a preorder, is nonempty, and is
upper directed. No countability or separation condition is imposed.

An existential witness can be taken in the universe of X or in any larger
universe. Tests quantify over all indices in any such larger universe;
`mem_closure_of_net` and `continuousAt_preserves_net_limits` additionally
state preservation for an arbitrary index universe, independent of X and Y.
-/

open Set
universe u v w
namespace Specs.D10Topology.Ch04.NetTests
open Specs.D10Topology.Ch04.NetsAndSubnets

def mem_closure_of_net : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] {D : Type v}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (A : Set X) (a : Net D X) (x : X),
    (∀ d, a d ∈ A) → Converges t a x → x ∈ closure A

def closure_iff_exists_net : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X) (x : X),
    x ∈ closure A ↔
      ∃ (D : Type (max u v)) (p : Preorder D),
        Nonempty D ∧ @IsDirectedOrder D p.toLE ∧
        ∃ a : Net D X, (∀ d, a d ∈ A) ∧ @Converges D X p t a x

def closed_iff_net_limits : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    IsClosed A ↔
      ∀ {D : Type (max u v)} [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : Net D X) (x : X), (∀ d, a d ∈ A) → Converges t a x → x ∈ A

def continuousAt_preserves_net_limits : Prop :=
  ∀ {X : Type u} [tX : TopologicalSpace X] {Y : Type v} [tY : TopologicalSpace Y]
    (f : X → Y) (x : X), ContinuousAt f x →
      ∀ {D : Type w} [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : Net D X), Converges tX a x → Converges tY (f ∘ a) (f x)

def continuousAt_iff_net_limits : Prop :=
  ∀ {X : Type u} [tX : TopologicalSpace X] {Y : Type v} [tY : TopologicalSpace Y]
    (f : X → Y) (x : X),
    ContinuousAt f x ↔
      ∀ {D : Type (max u w)} [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : Net D X), Converges tX a x → Converges tY (f ∘ a) (f x)

def continuous_iff_net_limits : Prop :=
  ∀ {X : Type u} [tX : TopologicalSpace X] {Y : Type v} [tY : TopologicalSpace Y]
    (f : X → Y),
    Continuous f ↔
      ∀ {D : Type (max u w)} [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : Net D X) (x : X), Converges tX a x → Converges tY (f ∘ a) (f x)

end Specs.D10Topology.Ch04.NetTests
