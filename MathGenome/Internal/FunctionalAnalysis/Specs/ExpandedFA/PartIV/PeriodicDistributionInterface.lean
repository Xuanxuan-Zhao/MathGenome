import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.TestFunctionLFTopology
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.LocallyConvex
import Mathlib.Analysis.Normed.Group.Uniform

/-!
Independent specification for the interface part of
`paper.tex`, `fa2:p4:periodic-distributions` (20538--20577).

A smooth function on the quotient torus is represented as an actual function on
`(ℝ/ℤ)^d` whose pullback along the quotient projection is smooth. The topology
is induced by all derivatives, in the uniform norm on the closed unit cube.
No distribution is defined by a sequential continuity condition.
-/

open Set TopologicalSpace
open scoped Distributions BoundedContinuousFunction

namespace ExpandedFA.PartIV.Periodic

open ExpandedFA.Distributions

abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)
abbrev Lattice (d : ℕ) := Fin d → ℤ

def integerVector {d : ℕ} (k : Lattice d) : Domain d := fun i => (k i : ℝ)

def quotient {d : ℕ} (x : Domain d) : Torus d := fun i => (x i : UnitAddCircle)

/-- Smoothness on the quotient is tested by the Euclidean covering projection. -/
def smoothSubmodule (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :
    Submodule 𝕜 (Torus d → 𝕜) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) (fun x : Domain d => f (quotient x))}
  zero_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : Domain d => (0 : 𝕜))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ (⊤ : ℕ∞) (fun x : Domain d => f (quotient x)) from hf).add hg
  smul_mem' := by
    intro c f hf
    exact (show ContDiff ℝ (⊤ : ℕ∞) (fun x : Domain d => f (quotient x)) from hf).const_smul c

abbrev Smooth (𝕜 : Type) [RCLike 𝕜] (d : ℕ) := smoothSubmodule 𝕜 d

def lift {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (φ : Smooth 𝕜 d) : Domain d → 𝕜 :=
  fun x => φ.val (quotient x)

theorem contDiff_lift {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (φ : Smooth 𝕜 d) :
    ContDiff ℝ (⊤ : ℕ∞) (lift φ) := φ.property

/-- The compact fundamental cube; closed faces overlap harmlessly. -/
def cube (d : ℕ) : Set (Domain d) := Icc 0 1

instance cubeCompactSpace (d : ℕ) : CompactSpace (cube d) :=
  isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Icc (0 : Domain d) 1))

/-- The derivative restriction maps whose uniform norms define the smooth topology. -/
noncomputable def jetLM (𝕜 : Type) [RCLike 𝕜] (d m : ℕ) :
    Smooth 𝕜 d →ₗ[𝕜] C(cube d, (Domain d) [×m]→L[ℝ] 𝕜) where
  toFun φ :=
    ⟨fun x => iteratedFDeriv ℝ m (lift φ) x,
      ((contDiff_lift φ).continuous_iteratedFDeriv (mod_cast le_top)).comp continuous_subtype_val⟩
  map_add' φ ψ := by
    apply ContinuousMap.ext
    intro x
    change iteratedFDeriv ℝ m (lift φ + lift ψ) x = _
    exact iteratedFDeriv_add_apply
      ((contDiff_lift φ).of_le (mod_cast le_top)).contDiffAt
      ((contDiff_lift ψ).of_le (mod_cast le_top)).contDiffAt
  map_smul' c φ := by
    apply ContinuousMap.ext
    intro x
    change iteratedFDeriv ℝ m (c • lift φ) x = _
    exact iteratedFDeriv_const_smul_apply
      ((contDiff_lift φ).of_le (mod_cast le_top)).contDiffAt

/-- Initial topology for the derivative restriction maps, not a topology defined
only by convergence of sequences. -/
noncomputable instance smoothTopology {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    TopologicalSpace (Smooth 𝕜 d) :=
  ⨅ m : ℕ, induced (jetLM 𝕜 d m) inferInstance

noncomputable instance smoothUniformSpace {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    UniformSpace (Smooth 𝕜 d) := .replaceTopology
  (⨅ m : ℕ, UniformSpace.comap (jetLM 𝕜 d m) inferInstance)
  UniformSpace.toTopologicalSpace_iInf.symm

instance smoothIsTopologicalAddGroup {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    IsTopologicalAddGroup (Smooth 𝕜 d) :=
  isTopologicalAddGroup_iInf fun _ => isTopologicalAddGroup_induced _

/-- The derivative uniformity is the additive group uniformity, so its
completeness is the completeness used in the definition of a Fréchet space. -/
instance smoothIsUniformAddGroup {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    IsUniformAddGroup (Smooth 𝕜 d) := by
  rw [smoothUniformSpace, UniformSpace.replaceTopology_eq]
  apply isUniformAddGroup_iInf
  intro m
  letI : IsUniformAddGroup C(cube d, (Domain d) [×m]→L[ℝ] 𝕜) :=
    @SeminormedAddCommGroup.to_isUniformAddGroup
      C(cube d, (Domain d) [×m]→L[ℝ] 𝕜) inferInstance
  exact IsUniformAddGroup.comap (jetLM 𝕜 d m)

instance smoothContinuousSMul {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    ContinuousSMul 𝕜 (Smooth 𝕜 d) :=
  continuousSMul_iInf fun m => continuousSMul_induced (jetLM 𝕜 d m)

instance smoothRealContinuousSMul {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    ContinuousSMul ℝ (Smooth 𝕜 d) :=
  continuousSMul_iInf fun m => continuousSMul_induced ((jetLM 𝕜 d m).restrictScalars ℝ)

instance smoothLocallyConvexSpace {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    LocallyConvexSpace ℝ (Smooth 𝕜 d) :=
  LocallyConvexSpace.iInf fun m =>
    LocallyConvexSpace.induced ((jetLM 𝕜 d m).restrictScalars ℝ)

/-- Supremum norm of the m-th derivative on a fundamental cube. -/
noncomputable def derivativeSeminorm (𝕜 : Type) [RCLike 𝕜] (d m : ℕ) :
    Seminorm 𝕜 (Smooth 𝕜 d) :=
  (normSeminorm 𝕜 C(cube d, (Domain d) [×m]→L[ℝ] 𝕜)).comp (jetLM 𝕜 d m)

/-- A coordinate partial derivative on the fundamental cube. -/
noncomputable def coordinateJetLM (𝕜 : Type) [RCLike 𝕜] (d : ℕ) {k : ℕ}
    (a : Fin k → Fin d) : Smooth 𝕜 d →ₗ[𝕜] C(cube d, 𝕜) :=
  (((coordinateEvaluation 𝕜 a).compLeftContinuous 𝕜 (cube d)).toLinearMap).comp (jetLM 𝕜 d k)

noncomputable def coordinateJetSeminorm (𝕜 : Type) [RCLike 𝕜] (d : ℕ) {k : ℕ}
    (a : Fin k → Fin d) : Seminorm 𝕜 (Smooth 𝕜 d) :=
  (normSeminorm 𝕜 C(cube d, 𝕜)).comp (coordinateJetLM 𝕜 d a)

/-- The usual increasing C∞ seminorms: all coordinate partials of order at most m. -/
noncomputable def smoothPartialSeminorm (𝕜 : Type) [RCLike 𝕜] (d m : ℕ) :
    Seminorm 𝕜 (Smooth 𝕜 d) :=
  (Finset.range (m + 1)).sup fun k => Finset.univ.sup (coordinateJetSeminorm 𝕜 d (k := k))

abbrev EuclideanTests (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  Tests 𝕜 (⊤ : Opens (Domain d))

abbrev EuclideanDistribution (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  ScalarDistribution 𝕜 (⊤ : Opens (Domain d))

/-- Translation acts on a test by `ψ(x+a)`; invariance uses every integer vector. -/
noncomputable def translateTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Domain d) (ψ : EuclideanTests 𝕜 d) : EuclideanTests 𝕜 d where
  toFun x := ψ (x + a)
  contDiff' := ψ.contDiff.comp (contDiff_id.add contDiff_const)
  hasCompactSupport' := ψ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight a)
  tsupport_subset' := subset_univ _

/-- Continuous scalar-linear dual of the smooth Fréchet topology. -/
abbrev TorusDistribution (𝕜 : Type) [RCLike 𝕜] (d : ℕ) := Smooth 𝕜 d →L[𝕜] 𝕜

/-- Integer-translation-invariant distributions on all of Euclidean space. -/
def invariantSubmodule (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :
    Submodule 𝕜 (EuclideanDistribution 𝕜 d) where
  carrier := {u | ∀ (k : Lattice d) (ψ : EuclideanTests 𝕜 d),
    u (translateTest (integerVector k) ψ) = u ψ}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv k ψ; simp [hu k ψ, hv k ψ]
  smul_mem' := by intro c u hu k ψ; simp [hu k ψ]

abbrev InvariantDistribution (𝕜 : Type) [RCLike 𝕜] (d : ℕ) := invariantSubmodule 𝕜 d

/-- Finitely supported sum at each point; the finiteness and smoothness are
part of the periodization obligation below. -/
noncomputable def periodizeRaw {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ψ : EuclideanTests 𝕜 d) (x : Domain d) : 𝕜 :=
  ∑ᶠ k : Lattice d, ψ (x + integerVector k)

/-- Multiplication by a compact smooth cutoff after periodic lifting. -/
noncomputable def cutoffTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (χ : EuclideanTests 𝕜 d) (φ : Smooth 𝕜 d) : EuclideanTests 𝕜 d where
  toFun x := χ x * lift φ x
  contDiff' := χ.contDiff.mul (contDiff_lift φ)
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := subset_univ _

/-- A cutoff with periodization identically one, without a chosen support radius. -/
def IsCutoff {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (χ : EuclideanTests 𝕜 d) : Prop :=
  ∀ x, periodizeRaw χ x = 1

end ExpandedFA.PartIV.Periodic

namespace Specs.ExpandedFA.PartIV.PeriodicDistributionInterface
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.PartIV.Periodic

/-- Canonical definitions of the two distribution spaces. -/
def torusDistributionType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), Type

def torusDistributionValue : torusDistributionType := fun 𝕜 _ d => TorusDistribution 𝕜 d

def invariantDistributionType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), Type

def invariantDistributionValue : invariantDistributionType := fun 𝕜 _ d => InvariantDistribution 𝕜 d

/-- The quotient projection identifies exactly integer translates. -/
def quotientType : Prop := ∀ d : ℕ,
  Function.Surjective (@quotient d) ∧ ∀ x y : Domain d,
    quotient x = quotient y ↔ ∃ k : Lattice d, y = x + integerVector k

/-- The smooth topology is Fréchet: Hausdorff, metrizable, complete, and locally
convex, with continuous vector space operations. -/
def smoothTopologyPropertiesType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  T2Space (Smooth 𝕜 d) ∧ MetrizableSpace (Smooth 𝕜 d) ∧ CompleteSpace (Smooth 𝕜 d) ∧
    IsTopologicalAddGroup (Smooth 𝕜 d) ∧ ContinuousSMul 𝕜 (Smooth 𝕜 d) ∧
    LocallyConvexSpace ℝ (Smooth 𝕜 d)

def seminormTopologyType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  WithSeminorms (derivativeSeminorm 𝕜 d)

/-- Equality with the standard topology given by all coordinate partial sup norms. -/
def partialTopologyType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  WithSeminorms (smoothPartialSeminorm 𝕜 d)

def partialFormulaType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (φ : Smooth 𝕜 d) (C : ℝ), 0 ≤ C →
  (smoothPartialSeminorm 𝕜 d m φ ≤ C ↔ ∀ k ≤ m, ∀ a : Fin k → Fin d,
    ∀ x ∈ cube d, ‖iteratedFDeriv ℝ k (lift φ) x
      (fun j => coordinateVector (a j))‖ ≤ C)

/-- The actual finite lattice sum defines a continuous map for the LF topology;
in particular its restriction to every compact step is continuous. -/
def periodizationType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  ∃ P : EuclideanTests 𝕜 d →L[𝕜] Smooth 𝕜 d,
    ∀ ψ x, lift (P ψ) x = periodizeRaw ψ x

/-- No finiteness of an arbitrary infinite series is silently assumed. -/
def localFinitenessType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (ψ : EuclideanTests 𝕜 d),
  LocallyFinite (fun k : Lattice d =>
    tsupport (fun x : Domain d => ψ (x + integerVector k)))

def cutoffExistenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  ∃ χ : EuclideanTests 𝕜 d, IsCutoff χ

/-- The map lands continuously in the single fixed compact step determined by χ. -/
def cutoffContinuityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (χ : EuclideanTests 𝕜 d),
  ∃ M : Smooth 𝕜 d →L[𝕜]
      Step 𝕜 (⟨tsupport χ, χ.hasCompactSupport⟩ : Compacts (Domain d)),
    ∀ φ x, M φ x = χ x * lift φ x

/-- Both inverse formulas, quantified over every normalized cutoff. The linear
equivalence supplies injectivity, surjectivity, and the two inverse identities. -/
def correspondenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  ∃ P : EuclideanTests 𝕜 d →L[𝕜] Smooth 𝕜 d,
  ∃ e : TorusDistribution 𝕜 d ≃ₗ[𝕜] InvariantDistribution 𝕜 d,
    (∀ ψ x, lift (P ψ) x = periodizeRaw ψ x) ∧
    (∀ U ψ, (e U).val ψ = U (P ψ)) ∧
    (∀ (χ : EuclideanTests 𝕜 d), IsCutoff χ →
      ∀ u φ, e.symm u φ = u.val (cutoffTest χ φ))

def cutoffIndependenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (χ ξ : EuclideanTests 𝕜 d), IsCutoff χ → IsCutoff ξ →
    ∀ (u : InvariantDistribution 𝕜 d) (φ : Smooth 𝕜 d),
      u.val (cutoffTest χ φ) = u.val (cutoffTest ξ φ)

end Specs.ExpandedFA.PartIV.PeriodicDistributionInterface
