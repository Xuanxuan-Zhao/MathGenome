import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions

/-! Independent statements of paper.tex, Lemma `d10:12:cauchy-cluster`.
The uniform space supplies its induced topology. Properness is explicit in
the convergence implication and is part of `CauchyFilter` in the other two.
No nonemptiness, completeness, or separation assumption is imposed.
-/

open Filter
universe u v

namespace Specs.D10Topology.Ch12.UniformCauchyBasics

open UniformConventions
open Specs.D10Topology.Ch04.ProperFilters

/-- A proper convergent filter satisfies the entourage-square Cauchy condition. -/
def convergent_cauchy : Prop :=
  ∀ {X : Type u} [UniformSpace X] (F : Filter X) (x : X),
    F.NeBot → FilterConverges F x → CauchyFilter F

/-- Every cluster point of a Cauchy filter is a limit, also in nonseparated spaces. -/
def cauchy_cluster_converges : Prop :=
  ∀ {X : Type u} [UniformSpace X] (F : Filter X) (x : X),
    CauchyFilter F → FilterClusters F x → FilterConverges F x

/-- The image filter under an entourage-continuous map remains proper and Cauchy. -/
def uniformContinuous_image_cauchy : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y]
    (f : X → Y) (F : Filter X),
    EntourageContinuous f → CauchyFilter F → CauchyFilter (ImageFilter f F)

end Specs.D10Topology.Ch12.UniformCauchyBasics
