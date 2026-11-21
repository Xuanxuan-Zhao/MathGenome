import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.StableManifold
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.CountableImmersedAtlas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Bases
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! Independent statements for paper.tex, Remark d13:20:local-global.
The global stable set is defined using the original canonical maximal flow.
The atlas is allowed its own topology; no ambient subspace topology is asserted.
A compatible atlas on open subsets of the actual stable spectral space, with
smooth full-rank parametrizations, expresses the immersed manifold conclusion. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace D13Unified.Ch20.GlobalStableManifold
open D13Unified.Ch06.StateDerivative
open Specs.D13Unified.Ch11.Flow Specs.D13Unified.Ch20.StableGraphs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forward completeness and convergence are both required, in the original domain. -/
def stableSet (F : AutonomousODE E) (p : E) : Set E :=
  {x | x ∈ F.domain ∧ (∀ t : ℝ, 0 ≤ t → (t, x) ∈ flowDomain F) ∧
    Tendsto (fun t : ℝ => flow F t x) atTop (𝓝 p)}

def graphPoint (p : E) {S T : Submodule ℝ E} (h : S → T) (ξ : S) : E :=
  p + graphMap h ξ

def stageDomain (F : AutonomousODE E) (p : E) {S T : Submodule ℝ E}
    (h : S → T) (V : Set S) (m : ℕ) : Set S :=
  V ∩ (graphPoint p h) ⁻¹' timeDomainValue F (-(m : ℝ))

def stageMap (F : AutonomousODE E) (p : E) {S T : Submodule ℝ E}
    (h : S → T) (m : ℕ) (ξ : S) : E :=
  flow F (-(m : ℝ)) (graphPoint p h ξ)

def backwardStage (F : AutonomousODE E) (p : E) {S T : Submodule ℝ E}
    (h : S → T) (V : Set S) (m : ℕ) : Set E :=
  stageMap F p h m '' stageDomain F p h V m

/-- An open local stable portion, containing the equilibrium, is positively
invariant and has complete forward solutions converging to the equilibrium. -/
def LocalPortion (k : ℕ∞) (F : AutonomousODE E) (p : E)
    (S T : Submodule ℝ E) (h : S → T) (V : Set S) (ρ : ℝ) : Prop :=
  GraphGeometry k S T h ∧ 0 < ρ ∧ IsOpen V ∧ (0 : S) ∈ V ∧
  (∀ ξ ∈ V, graphPoint p h ξ ∈ F.domain ∧ ‖graphPoint p h ξ - p‖ < ρ) ∧
  (∀ ξ ∈ V, graphPoint p h ξ ∈ stableSet F p) ∧
  (∀ ξ ∈ V, ∀ t : ℝ, 0 ≤ t →
    flow F t (graphPoint p h ξ) ∈ graphPoint p h '' V)

/-- Every globally convergent original trajectory eventually enters the
chosen portion at an integer time, not merely an unspecified real time. -/
def CapturesStableSet (F : AutonomousODE E) (p : E) {S T : Submodule ℝ E}
    (h : S → T) (V : Set S) : Prop :=
  ∀ x ∈ stableSet F p, ∃ m : ℕ, flow F (m : ℝ) x ∈ graphPoint p h '' V

/-- The explicit countable compatible atlas. Its model is S itself, so its
dimension is finrank ℝ S, including S=0. Full rank is stated in coordinates
as injectivity of the differential of the inclusion parametrization. -/
structure StableAtlas (k : ℕ∞) (F : AutonomousODE E) (p : E)
    {S T : Submodule ℝ E} (h : S → T) (V : Set S) where
  topology : TopologicalSpace (stableSet F p)
  hausdorff : @T2Space (stableSet F p) topology
  secondCountable : @SecondCountableTopology (stableSet F p) topology
  chart : ℕ → @OpenPartialHomeomorph (stableSet F p) S topology inferInstance
  source_eq : ∀ m, (chart m).source = {x : stableSet F p | (x : E) ∈ backwardStage F p h V m}
  target_eq : ∀ m, (chart m).target = stageDomain F p h V m
  cover : (⋃ m, (chart m).source) = univ
  inverse_eq : ∀ m ξ, ξ ∈ (chart m).target →
    ((chart m).symm ξ : E) = stageMap F p h m ξ
  transitions : ∀ m n, ContDiffOn ℝ k ((chart m).symm.trans (chart n))
    ((chart m).symm.trans (chart n)).source
  parametrization : ∀ m, ContDiffOn ℝ k (stageMap F p h m) (stageDomain F p h V m)
  injective_differential : ∀ m ξ, ξ ∈ stageDomain F p h V m →
    Function.Injective (fderiv ℝ (stageMap F p h m) ξ)
  inclusion_continuous : @Continuous (stableSet F p) E topology inferInstance Subtype.val
  inclusion_injective : Function.Injective (Subtype.val : stableSet F p → E)
  inclusion_regular : ∀ m, ContDiffOn ℝ k
    (fun ξ => ((chart m).symm ξ : E)) (chart m).target
  inclusion_differential : ∀ m ξ, ξ ∈ (chart m).target →
    Function.Injective (fderiv ℝ (fun η => ((chart m).symm η : E)) ξ)
  chartedSpace : @ChartedSpace S inferInstance (stableSet F p) topology
  atlas_eq : @atlas S inferInstance (stableSet F p) topology chartedSpace = range chart
  manifold : @IsManifold ℝ inferInstance S inferInstance inferInstance S inferInstance
    (modelWithCornersSelf ℝ S) (k : ℕ∞ω) (stableSet F p) topology chartedSpace
  dimension : ∀ x : stableSet F p,
    Module.finrank ℝ (TangentSpace (modelWithCornersSelf ℝ S) x) = Module.finrank ℝ S

end D13Unified.Ch20.GlobalStableManifold

namespace Specs.D13Unified.Ch20.GlobalStableManifold
open _root_.D13Unified _root_.D13Unified.Ch20 _root_.D13Unified.Ch07
open _root_.D13Unified.Ch06.StateDerivative
open _root_.D13Unified.Ch20.GlobalStableManifold
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.PerronRegularity Specs.D13Unified.Ch20.StableGraphs
open Specs.D13Unified.Ch01.AutonomousParameters
universe u v

/-- Full original obligation: no cutoff completeness is substituted for original
forward existence, and no closed-embedding or subspace-topology conclusion occurs. -/
def globalStableManifoldExpected : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (F : AutonomousODE E) (p : E)
    (A : Matrix n n ℝ) (k : ℕ∞),
    p ∈ F.domain → 1 ≤ k → ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    autonomousEvalValue F p = 0 →
    HasFDerivAt (autonomousEvalValue F) (matrixOperatorEquiv b A) p → hyperbolicValue A →
    ∃ (h : stableParameters b A → unstableParameters b A)
      (V : Set (stableParameters b A)) (ρ : ℝ),
      LocalPortion k F p (stableParameters b A) (unstableParameters b A) h V ρ ∧
      CapturesStableSet F p h V ∧
      (stableSet F p = ⋃ m : ℕ, backwardStage F p h V m) ∧
      Monotone (backwardStage F p h V) ∧ Nonempty (StableAtlas k F p h V)

/-- The local-portion construction and eventual entry stage of the proof. -/
def stablePortionExpected : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (F : AutonomousODE E) (p : E)
    (A : Matrix n n ℝ) (k : ℕ∞),
    p ∈ F.domain → 1 ≤ k → ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    autonomousEvalValue F p = 0 →
    HasFDerivAt (autonomousEvalValue F) (matrixOperatorEquiv b A) p → hyperbolicValue A →
    ∃ (h : stableParameters b A → unstableParameters b A)
      (V : Set (stableParameters b A)) (ρ : ℝ),
      LocalPortion k F p (stableParameters b A) (unstableParameters b A) h V ρ ∧
      CapturesStableSet F p h V

/-- The constructed nested stages, with their original survival domains and
full-rank Cᵏ parametrizations. The compatible-atlas construction is separate. -/
def globalStagesExpected : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (F : AutonomousODE E) (p : E)
    (A : Matrix n n ℝ) (k : ℕ∞),
    p ∈ F.domain → 1 ≤ k → ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    autonomousEvalValue F p = 0 →
    HasFDerivAt (autonomousEvalValue F) (matrixOperatorEquiv b A) p → hyperbolicValue A →
    ∃ (h : stableParameters b A → unstableParameters b A)
      (V : Set (stableParameters b A)) (ρ : ℝ),
      LocalPortion k F p (stableParameters b A) (unstableParameters b A) h V ρ ∧
      CapturesStableSet F p h V ∧
      (stableSet F p = ⋃ m : ℕ, backwardStage F p h V m) ∧
      Monotone (backwardStage F p h V) ∧
      ∀ m : ℕ, IsOpen (stageDomain F p h V m) ∧
        ContDiffOn ℝ k (stageMap F p h m) (stageDomain F p h V m) ∧
        InjOn (stageMap F p h m) (stageDomain F p h V m) ∧
        ∀ ξ ∈ stageDomain F p h V m, Function.Injective (fderiv ℝ (stageMap F p h m) ξ)

end Specs.D13Unified.Ch20.GlobalStableManifold
