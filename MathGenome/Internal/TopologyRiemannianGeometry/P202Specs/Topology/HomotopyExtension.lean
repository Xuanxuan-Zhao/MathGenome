import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures
import Mathlib.Topology.Homotopy.Basic

/-! Independent shared interface for paper.tex, Theorem `thm:p202-cw-hep`.
Time is the first coordinate, as in `ContinuousMap.Homotopy`; transposing
coordinates gives the paper's `X × I` formulation. No finiteness hypothesis
is imposed on the CW complex or subcomplex. -/
namespace P202Specs.Topology.HomotopyExtension

open P202.Cellular
open scoped unitInterval
universe u v

/-- The actual subspace inclusion of a subcomplex. -/
def subcomplexInclusion {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) : C(A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Homotopy extension for every CW pair and every topological target.
The terminal map on the subcomplex is explicit so the prescribed homotopy
has its usual `ContinuousMap.Homotopy` type. Its full values are preserved. -/
def cwHomotopyExtension : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWStructure X] (A : Subcomplex X) (f : C(X, Y)) (g : C(A, Y))
    (h : ContinuousMap.Homotopy (f.comp (subcomplexInclusion A)) g),
    ∃ F : C(X, Y), ∃ H : ContinuousMap.Homotopy f F,
      ∀ (t : unitInterval) (a : A), H (t, a.1) = h (t, a)

/-- The same HEP statement with source and target in the same universe.
This is an additional dependency interface, not a restriction of the
full, independently required heterogeneous-universe theorem above. -/
def cwHomotopyExtensionSelf : Prop := cwHomotopyExtension.{u,u}

end P202Specs.Topology.HomotopyExtension
