import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Independent statements for paper.tex, d10:07:tietze-real.
Normality means separation of disjoint closed sets, without T1. The
real-valued functions have no boundedness restriction. Subspaces have the
canonical induced topology; empty subspaces and empty ambient spaces are
included by the unrestricted quantifiers.
-/

open Set
universe u

namespace Specs.D10Topology.Ch07.RealTietze

/-- Every continuous real-valued map on a closed subspace of a normal
space extends, including unbounded maps. -/
def tietze_real : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], NormalSpace X →
    ∀ (A : Set X), IsClosed A → ∀ (f : A → ℝ), Continuous f →
      ∃ F : X → ℝ, Continuous F ∧ ∀ x : A, F x = f x

/-- The full real-valued extension property characterizes normality. -/
def normal_iff_real_tietze : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], NormalSpace X ↔
    ∀ (A : Set X), IsClosed A → ∀ (f : A → ℝ), Continuous f →
      ∃ F : X → ℝ, Continuous F ∧ ∀ x : A, F x = f x

end Specs.D10Topology.Ch07.RealTietze
