import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.EvaluationParameter
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.CompactShrinking

/-! Joint evaluation and the parameter criterion (paper.tex, 13.6).

The upstream bridge identifies the source compact-open topology with Mathlib's
compact-open topology on ContinuousMap. The LCH bridge upgrades a single compact
neighborhood to arbitrarily small compact neighborhoods, with Hausdorffness used
only on X. Mathlib's evaluation and currying theorems then have precisely the
required hypotheses. All spaces and spaces of maps may be empty.
-/

universe u v w

namespace D10Topology.Ch13

abbrev parameterMap := @Specs.D10Topology.Ch13.EvaluationParameter.parameterMap

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem joint_evaluation_continuous (hX : Ch11.LCH X) :
    letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
    Continuous (fun p : ContinuousMaps X Y × X => p.1 p.2) := by
  let : T2Space X := hX.2
  let : LocallyCompactSpace X :=
    (Ch11.locallyCompact_iff_locallyCompactSpace X).mp hX.1
  rw [compactOpenContinuousTopology_eq_mathlib]
  exact continuous_eval

theorem continuous_slices (h : Z × X → Y) (hh : Continuous h) :
    ∀ z : Z, Continuous (fun x : X => h (z, x)) := by
  intro z
  exact hh.comp (continuous_const.prodMk continuous_id)

theorem parameter_map_continuous (h : Z × X → Y)
    (hs : ∀ z : Z, Continuous (fun x : X => h (z, x)))
    (hh : Continuous h) :
    letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
    Continuous (parameterMap h hs) := by
  rw [compactOpenContinuousTopology_eq_mathlib]
  exact ContinuousMap.continuous_of_continuous_uncurry (parameterMap h hs) hh

theorem associated_map_continuous (hX : Ch11.LCH X) (F : Z → ContinuousMaps X Y)
    (hF : letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
          Continuous F) :
    Continuous (fun p : Z × X => F p.1 p.2) := by
  rw [compactOpenContinuousTopology_eq_mathlib] at hF
  let : T2Space X := hX.2
  let : LocallyCompactSpace X :=
    (Ch11.locallyCompact_iff_locallyCompactSpace X).mp hX.1
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩

theorem parameter_criterion (hX : Ch11.LCH X) (h : Z × X → Y)
    (hs : ∀ z : Z, Continuous (fun x : X => h (z, x))) :
    Continuous h ↔
    (letI : TopologicalSpace (ContinuousMaps X Y) := compactOpenContinuousTopology
     Continuous (parameterMap h hs)) := by
  constructor
  · exact parameter_map_continuous h hs
  · intro hF
    exact associated_map_continuous hX (parameterMap h hs) hF

end D10Topology.Ch13
