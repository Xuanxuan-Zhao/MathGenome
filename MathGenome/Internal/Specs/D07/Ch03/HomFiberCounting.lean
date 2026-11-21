import MathGenome.Internal.Specs.D07.Ch01.KernelImage
import MathGenome.Internal.Specs.D07.Ch03.CosetBijections
import Mathlib.SetTheory.Cardinal.NatCard

/-!
Independent specification of K07.03.hom_fiber_counting (paper.tex:619–626).

Fibres are subsets of the domain, the kernel and image are the canonical
subgroups `f.ker` and `f.range`, and cosets use the shared set definitions.
The fibre assertions apply to arbitrary groups in independent universes.
The natural cardinality formulas retain the source's finite-domain premise;
the codomain need not be finite unless this follows from surjectivity.
-/

namespace Specs.D07.Ch03.HomFiberCounting

open Specs.D07.Ch03.CosetsPartition

universe u v

/-- Any point of a fibre can serve as representative of its left and right
kernel cosets. No finiteness or surjectivity is assumed. -/
def FiberEqCosets : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H)
    (h : H) (a : G), f a = h →
    {x : G | f x = h} = leftCoset f.ker a ∧
    {x : G | f x = h} = rightCoset f.ker a

/-- The source's nonempty-fibre formulation, including a representative in
the fibre itself. -/
def NonemptyFiberIsCoset : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H)
    (h : H), ({x : G | f x = h} : Set G).Nonempty →
    ∃ a : G, f a = h ∧
      {x : G | f x = h} = leftCoset f.ker a ∧
      {x : G | f x = h} = rightCoset f.ker a

/-- Multiplication by a representative identifies the kernel with its fibre,
with exactly the forward and inverse formulas used in the source. -/
def FiberBijection : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H)
    (h : H) (a : G), f a = h →
    ∃ e : f.ker ≃ ↥({x : G | f x = h} : Set G),
      (∀ k : f.ker, (e k : G) = a * (k : G)) ∧
      (∀ x : ↥({x : G | f x = h} : Set G),
        (e.symm x : G) = a⁻¹ * (x : G))

/-- Finite domain, arbitrary codomain: `|G| = |ker f| |im f|`. -/
def CardDomain : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] [Finite G]
    (f : G →* H), Nat.card G = Nat.card f.ker * Nat.card f.range

/-- Surjectivity replaces the image factor by the cardinality of the target.
There is no extra finiteness hypothesis on the target. -/
def CardDomainOfSurjective : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] [Finite G]
    (f : G →* H), Function.Surjective f →
    Nat.card G = Nat.card f.ker * Nat.card H

end Specs.D07.Ch03.HomFiberCounting
