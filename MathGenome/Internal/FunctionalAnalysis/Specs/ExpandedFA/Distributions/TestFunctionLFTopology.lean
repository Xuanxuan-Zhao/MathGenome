import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

/-! Independent objects and full propositions for paper.tex, definition
`fa2:p4:test-lf`. Scalar-valued tests and scalar-linear duals are used in
both the real and complex cases. No topology is specified by sequences. -/

open Set TopologicalSpace
open scoped Distributions BoundedContinuousFunction

namespace ExpandedFA.Distributions

abbrev Domain (d : ℕ) := Fin d → ℝ
abbrev Step (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (K : Compacts (Domain d)) :=
  ContDiffMapSupportedIn (Domain d) 𝕜 ⊤ K
abbrev Tests (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :=
  TestFunction Ω 𝕜 ⊤

/-- The paper's continuous scalar-linear dual, including complex-linear
functionals on complex-valued tests. -/
abbrev ScalarDistribution (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :=
  Tests 𝕜 Ω →L[𝕜] 𝕜

/-- A compact exhaustion in the ambient Euclidean space. -/
structure Exhaustion {d : ℕ} (Ω : Opens (Domain d)) where
  compact : ℕ → Compacts (Domain d)
  inside : ∀ j, (compact j : Set (Domain d)) ⊆ Ω
  nested : ∀ j, (compact j : Set (Domain d)) ⊆ interior (compact (j + 1) : Set (Domain d))
  covers : ⋃ j, (compact j : Set (Domain d)) = Ω

/-- Final topology in topological spaces for the chosen countable steps,
before taking its locally convex modification. -/
@[instance_reducible]
noncomputable def exhaustionOriginal {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (e : Exhaustion Ω) : TopologicalSpace (Tests 𝕜 Ω) :=
  ⨆ j, TopologicalSpace.coinduced
    (TestFunction.ofSupportedIn (F := 𝕜) (n := ⊤) (e.inside j)) inferInstance

/-- The finest locally convex vector topology for the exhaustion steps.
Lean orders topologies in reverse order of fineness. -/
@[instance_reducible]
noncomputable def exhaustionTopology {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (e : Exhaustion Ω) : TopologicalSpace (Tests 𝕜 Ω) :=
  sInf {t : TopologicalSpace (Tests 𝕜 Ω) | exhaustionOriginal (𝕜 := 𝕜) e ≤ t ∧
    @IsTopologicalAddGroup (Tests 𝕜 Ω) t _ ∧
    @ContinuousSMul ℝ (Tests 𝕜 Ω) _ _ t ∧
    @LocallyConvexSpace ℝ (Tests 𝕜 Ω) _ _ _ _ t}

/-- The standard coordinate directions on ℝ^d. -/
def coordinateVector {d : ℕ} (i : Fin d) : Domain d := Pi.single i 1

/-- Evaluation of a real multilinear derivative in coordinate directions,
linear over the scalar field of the function values. -/
noncomputable def coordinateEvaluation (𝕜 : Type) [RCLike 𝕜] {d k : ℕ}
    (a : Fin k → Fin d) : ((Domain d) [×k]→L[ℝ] 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun A => A (fun j => coordinateVector (a j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (∏ j, ‖coordinateVector (a j)‖)
    (fun A => by simpa [mul_comm] using A.le_opNorm (fun j => coordinateVector (a j)))

/-- An ordered coordinate partial derivative, as a bounded continuous function.
Indexing by coordinate words lists mixed partials with harmless repetitions. -/
noncomputable def coordinateDerivative (𝕜 : Type) [RCLike 𝕜] {d k : ℕ}
    (K : Compacts (Domain d)) (a : Fin k → Fin d) :
    Step 𝕜 K →L[𝕜] (Domain d →ᵇ 𝕜) :=
  ((coordinateEvaluation 𝕜 a).compLeftContinuousBounded (Domain d)).comp
    (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k)

noncomputable def coordinateSeminorm (𝕜 : Type) [RCLike 𝕜] {d k : ℕ}
    (K : Compacts (Domain d)) (a : Fin k → Fin d) : Seminorm 𝕜 (Step 𝕜 K) :=
  (normSeminorm 𝕜 (Domain d →ᵇ 𝕜)).comp (coordinateDerivative 𝕜 K a).toLinearMap

/-- `p_m`: maximum sup norm of all coordinate partial derivatives of orders ≤ m.
The finite maximum includes order zero even when d = 0. -/
noncomputable def stepSeminorm (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (K : Compacts (Domain d)) (m : ℕ) : Seminorm 𝕜 (Step 𝕜 K) :=
  (Finset.range (m + 1)).sup fun k =>
    Finset.univ.sup (coordinateSeminorm (k := k) 𝕜 K)

end ExpandedFA.Distributions

namespace Specs.ExpandedFA.Distributions.TestFunctionLFTopology
open _root_.ExpandedFA.Distributions

def lfTopologyType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), TopologicalSpace (Tests 𝕜 Ω)

noncomputable def lfTopologyValue : lfTopologyType :=
  fun 𝕜 _ _ Ω => TestFunction.topologicalSpace Ω 𝕜 ⊤

def distributionSpaceType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (_Ω : Opens (Domain d)), Type

def distributionSpaceValue : distributionSpaceType :=
  fun 𝕜 _ _ Ω => Tests 𝕜 Ω →L[𝕜] 𝕜

/-- The chosen steps cover the entire test space, including zero-dimensional
and empty open sets. -/
def unionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (e : Exhaustion Ω) (φ : Tests 𝕜 Ω),
  ∃ j, ∃ ψ : Step 𝕜 (e.compact j), TestFunction.ofSupportedIn (e.inside j) ψ = φ

/-- Exhaustions exist for every open subset. -/
def existsExhaustionType : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d)),
  Nonempty (Exhaustion Ω)

/-- This is equality of topologies, not just agreement of converging sequences. -/
def exhaustionEqualityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (e : Exhaustion Ω),
  exhaustionTopology (𝕜 := 𝕜) e = TestFunction.topologicalSpace Ω 𝕜 ⊤

def exhaustionIndependenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (e f : Exhaustion Ω),
  exhaustionTopology (𝕜 := 𝕜) e = exhaustionTopology (𝕜 := 𝕜) f

/-- Locally convex vector topology and continuity of each compact inclusion. -/
def topologyType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)),
  T2Space (Tests 𝕜 Ω) ∧ IsTopologicalAddGroup (Tests 𝕜 Ω) ∧ ContinuousSMul ℝ (Tests 𝕜 Ω) ∧
  LocallyConvexSpace ℝ (Tests 𝕜 Ω) ∧
  ∀ (K : Compacts (Domain d)) (hK : (K : Set (Domain d)) ⊆ Ω),
    Continuous (TestFunction.ofSupportedIn (F := 𝕜) (n := ⊤) hK)

/-- Universal maximality among all locally convex vector topologies with
continuous inclusions from the given exhaustion. -/
def finestType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (e : Exhaustion Ω)
    (t : TopologicalSpace (Tests 𝕜 Ω)),
  @IsTopologicalAddGroup (Tests 𝕜 Ω) t _ →
  @ContinuousSMul ℝ (Tests 𝕜 Ω) _ _ t →
  @LocallyConvexSpace ℝ (Tests 𝕜 Ω) _ _ _ _ t →
  (∀ j, @Continuous _ _ inferInstance t
    (TestFunction.ofSupportedIn (F := 𝕜) (n := ⊤) (e.inside j))) →
  TestFunction.topologicalSpace Ω 𝕜 ⊤ ≤ t

/-- The continuous-seminorm characterization for the countable exhaustion. -/
def seminormCriterionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (e : Exhaustion Ω) (p : Seminorm ℝ (Tests 𝕜 Ω)),
  Continuous p ↔ ∀ j, Continuous (p ∘ TestFunction.ofSupportedIn (e.inside j))

/-- A distribution is precisely a scalar-linear functional continuous on each step. -/
def dualCriterionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (e : Exhaustion Ω) (u : Tests 𝕜 Ω →ₗ[𝕜] 𝕜),
  Continuous u ↔ ∀ j, Continuous (u ∘ TestFunction.ofSupportedIn (e.inside j))

/-- The native compact-step topology is generated by the displayed partial
seminorms, rather than merely by equivalent norms left without a bridge. -/
def stepSeminormTopologyType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (K : Compacts (Domain d)), WithSeminorms (stepSeminorm 𝕜 K)

/-- A precise max/sup characterization of the defining seminorm values. -/
def stepSeminormFormulaType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (K : Compacts (Domain d)) (m : ℕ) (φ : Step 𝕜 K) (C : ℝ), 0 ≤ C →
  (stepSeminorm 𝕜 K m φ ≤ C ↔ ∀ k ≤ m, ∀ a : Fin k → Fin d, ∀ x,
    ‖iteratedFDeriv ℝ k φ x (fun j => coordinateVector (a j))‖ ≤ C)

/-- Scalar seminorms as well as underlying real seminorms satisfy the criterion. -/
def scalarSeminormCriterionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (e : Exhaustion Ω) (p : Seminorm 𝕜 (Tests 𝕜 Ω)),
  Continuous p ↔ ∀ j, Continuous (p ∘ TestFunction.ofSupportedIn (e.inside j))

def scalarTopologyType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), ContinuousSMul 𝕜 (Tests 𝕜 Ω)

/-- An explicit generating family of seminorms for the LF topology. -/
def generatingSeminormsType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (e : Exhaustion Ω),
  WithSeminorms (fun p : {p : Seminorm ℝ (Tests 𝕜 Ω) //
    ∀ j, Continuous (p ∘ TestFunction.ofSupportedIn (e.inside j))} => p.val)

end Specs.ExpandedFA.Distributions.TestFunctionLFTopology
