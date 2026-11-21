import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Convex.Hull

/-! Independent statements for the averaging portion of `fa2:p5:haar`.
All closures and compactness below use the supremum norm on C(G, 𝕜).
Convexity is over ℝ for both scalar fields. No measurable structure on G
or continuity of an action on a space of measures is an input. -/

noncomputable section
universe u v
namespace ExpandedFA.PartV.HaarAveraging

inductive Side | left | right

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {𝕜 : Type v} [RCLike 𝕜]

/-- The source conventions Lₛf(x)=f(sx), Rₛf(x)=f(xs). -/
def translate (side : Side) (s : G) (f : C(G, 𝕜)) : C(G, 𝕜) :=
  f.comp ⟨(match side with | .left => fun x => s * x | .right => fun x => x * s),
    by cases side <;> fun_prop⟩

def orbit (side : Side) (f : C(G, 𝕜)) : Set C(G, 𝕜) :=
  Set.range (fun s => translate side s f)

def translateHull (side : Side) (f : C(G, 𝕜)) : Set C(G, 𝕜) :=
  closure (convexHull ℝ (orbit side f))

def translateOperator (side : Side) (s : G) : C(G, 𝕜) →L[𝕜] C(G, 𝕜) :=
  ContinuousMap.compCLM 𝕜 𝕜
    ⟨(match side with | .left => fun x => s * x | .right => fun x => x * s),
      by cases side <;> fun_prop⟩

/-- Membership means a finite real convex combination of translation operators. -/
def IsFiniteAverage (side : Side) (P : C(G, 𝕜) →L[𝕜] C(G, 𝕜)) : Prop :=
  P ∈ convexHull ℝ (Set.range (translateOperator (𝕜 := 𝕜) side))

variable [CompactSpace G] [T2Space G]

namespace Spec

def CompactTranslateHulls : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] (𝕜 : Type v) [RCLike 𝕜]
    (side : Side) (f : C(G, 𝕜)),
    Continuous (fun s => translate side s f) ∧ IsCompact (orbit side f) ∧
      IsCompact (translateHull side f)

/-- Positivity is the usual one, including for complex-valued functions:
pointwise nonnegative real functions have nonnegative real means. -/
def MeanProperties (M : C(G, 𝕜) →L[𝕜] 𝕜) : Prop :=
  (∀ c, M (ContinuousMap.const G c) = c) ∧
  (∀ f : C(G, 𝕜), (∀ x, ∃ r : ℝ, 0 ≤ r ∧ f x = (r : 𝕜)) →
    ∃ r : ℝ, 0 ≤ r ∧ M f = (r : 𝕜)) ∧
  (∀ side s f, M (translate side s f) = M f) ∧
  (∀ side f c, ContinuousMap.const G c ∈ translateHull side f ↔ c = M f) ∧
  (∀ side f h, h ∈ translateHull side f → M h = M f) ∧
  ‖M‖ = 1

def ExistsAveragingMean : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] (𝕜 : Type v) [RCLike 𝕜],
    ∃ M : C(G, 𝕜) →L[𝕜] 𝕜, MeanProperties M

/-- The successive averaging construction controls two functions with the same
composite average. In particular, the last inequality gives the approximants
used in the source's additivity argument. -/
def SuccessiveAveraging : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] (𝕜 : Type v) [RCLike 𝕜]
    (M : C(G, 𝕜) →L[𝕜] 𝕜), MeanProperties M →
    ∀ (f g : C(G, 𝕜)) (ε : ℝ), 0 < ε →
    ∃ P Q : C(G, 𝕜) →L[𝕜] C(G, 𝕜),
      IsFiniteAverage .left P ∧ IsFiniteAverage .left Q ∧
      ‖P f - ContinuousMap.const G (M f)‖ < ε ∧
      ‖Q (P f) - ContinuousMap.const G (M f)‖ < ε ∧
      ‖Q (P g) - ContinuousMap.const G (M g)‖ < ε ∧
      ‖Q (P (f + g)) - ContinuousMap.const G (M f + M g)‖ < 2 * ε

/-- Additivity from successive averages for an ordinary function m. Neither
linearity nor continuity of m is assumed in this supporting argument. The two
hypotheses are the hull properties established for the constructed mean. -/
def AdditivityOfHullAveraging : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] (𝕜 : Type v) [RCLike 𝕜]
    (m : C(G, 𝕜) → 𝕜),
    (∀ f c, ContinuousMap.const G c ∈ translateHull .left f ↔ c = m f) →
    (∀ f h, h ∈ translateHull .left f → m h = m f) →
    ∀ f g, m (f + g) = m f + m g

end Spec
end ExpandedFA.PartV.HaarAveraging
