import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.Dini
import Mathlib.Topology.UniformSpace.Dini

/-!
Dini's theorem for increasing and decreasing sequences of continuous real
functions on any compact topological space (paper.tex, d10:16:dini).

Mathlib's normed lattice theorem specializes to the usual ordered real
field. Its compact-domain version assumes only TopologicalSpace and
CompactSpace on the domain. Pointwise monotonicity below is converted to
the pointwise order on the function space; no domain separation or metric
is used. In particular an empty domain is allowed throughout.
-/

open Filter
open scoped Topology
universe u

namespace D10Topology.Ch16

theorem dini_increasing : Specs.D10Topology.Ch16.Dini.dini_increasing.{u} := by
  intro X _ _ F f hF hf hmono hlim
  exact Monotone.tendstoUniformly_of_forall_tendsto hF
    (fun _ _ hmn x => hmono x hmn) hf hlim

theorem dini_decreasing : Specs.D10Topology.Ch16.Dini.dini_decreasing.{u} := by
  intro X _ _ F f hF hf hanti hlim
  exact Antitone.tendstoUniformly_of_forall_tendsto hF
    (fun _ _ hmn x => hanti x hmn) hf hlim

theorem dini_increasing_epsilon :
    Specs.D10Topology.Ch16.Dini.dini_increasing_epsilon.{u} := by
  intro X _ _ F f hF hf hmono hlim ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (dini_increasing F f hF hf hmono hlim)) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  exact ⟨N, fun n hn x => by simpa only [Real.dist_eq, abs_sub_comm] using hN n hn x⟩

theorem dini_decreasing_epsilon :
    Specs.D10Topology.Ch16.Dini.dini_decreasing_epsilon.{u} := by
  intro X _ _ F f hF hf hanti hlim ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (dini_decreasing F f hF hf hanti hlim)) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  exact ⟨N, fun n hn x => by simpa only [Real.dist_eq, abs_sub_comm] using hN n hn x⟩

end D10Topology.Ch16
