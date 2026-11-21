import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.List.OfFn
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Canonical objects for paper.tex, Definition 4.1 (1276–1289).

Tests are represented by their ambient zero extensions. `FixedSupport` is independent
of the open set; it is used as a stage in `TestSpace Ω` only with a proof `K ⊆ Ω`.
The scalar-linear dual is intentional: complex pairings have no conjugation.
The Fréchet seminorms below are an auxiliary family. The expected statements include
their equivalence with the paper's coordinate multi-index seminorms. Multi-indices
are multisets of coordinate directions, with an explicit equivalence to ℕ^d.
-/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Distributions BoundedContinuousFunction

namespace P102.U4

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev TestSpace {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) :=
  TestFunction Ω 𝕜 ⊤

abbrev FixedSupport (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)) :=
  ContDiffMapSupportedIn (Space d) 𝕜 ⊤ K

abbrev DistributionSpace {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) :=
  TestSpace 𝕜 Ω →L[𝕜] 𝕜

/-- The Lebesgue measure attached to the Euclidean inner product. -/
def euclideanVolume (d : ℕ) : MeasureTheory.Measure (Space d) := MeasureTheory.volume

/-- Operator-norm seminorm of the derivative of exactly order `k`. -/
def frechetSeminorm {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)) (k : ℕ) :
    Seminorm 𝕜 (FixedSupport d 𝕜 K) :=
  ContDiffMapSupportedIn.seminorm 𝕜 (Space d) 𝕜 ⊤ K k

/-- Increasing auxiliary seminorm, including order zero. -/
def frechetSupSeminorm {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) : Seminorm 𝕜 (FixedSupport d 𝕜 K) :=
  ContDiffMapSupportedIn.supSeminorm 𝕜 (Space d) 𝕜 ⊤ K m

/-- The natural inclusion of a stage, preserving the ambient function. -/
def stageInclusion {d : ℕ} (𝕜 : Type) [RCLike 𝕜] {Ω : Opens (Space d)}
    {K : Compacts (Space d)} (hK : (K : Set (Space d)) ⊆ Ω) :
    FixedSupport d 𝕜 K →L[𝕜] TestSpace 𝕜 Ω :=
  TestFunction.ofSupportedInCLM 𝕜 hK

/-- Zero extension between open sets, represented by the same ambient function. -/
def zeroExtension {d : ℕ} (𝕜 : Type) [RCLike 𝕜] {V Ω : Opens (Space d)}
    (_h : V ≤ Ω) : TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 Ω := TestFunction.monoCLM 𝕜

/-- The standard orthonormal coordinate vector; Euclidean, not the supremum norm. -/
def coordinateVector (d : ℕ) (i : Fin d) : Space d := EuclideanSpace.basisFun (Fin d) ℝ i

def realPart {d : ℕ} (Ω : Opens (Space d)) : TestSpace ℂ Ω →L[ℝ] TestSpace ℝ Ω :=
  TestFunction.postcompCLM Complex.reCLM

def imagPart {d : ℕ} (Ω : Opens (Space d)) : TestSpace ℂ Ω →L[ℝ] TestSpace ℝ Ω :=
  TestFunction.postcompCLM Complex.imCLM

def complexifyTest {d : ℕ} (Ω : Opens (Space d)) : TestSpace ℝ Ω →L[ℝ] TestSpace ℂ Ω :=
  TestFunction.postcompCLM Complex.ofRealCLM

/-- Evaluation of a multilinear derivative on a coordinate word. -/
def coordinateEvaluation {d k : ℕ} (𝕜 : Type) [RCLike 𝕜] (a : Fin k → Fin d) :
    (Space d [×k]→L[ℝ] 𝕜) →L[𝕜] 𝕜 where
  toFun A := A (fun j => coordinateVector d (a j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_id.eval_const _

/-- Supremum norm of one coordinate word derivative. -/
def coordinateWordSeminorm {d k : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (a : Fin k → Fin d) : Seminorm 𝕜 (FixedSupport d 𝕜 K) :=
  (normSeminorm 𝕜 (Space d →ᵇ 𝕜)).comp
    (((coordinateEvaluation 𝕜 a).compLeftContinuousBounded (Space d)).comp
      (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k)).toLinearMap

/-- Maximum over the coordinate words of one given length. -/
def coordinateOrderSeminorm {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (k : ℕ) : Seminorm 𝕜 (FixedSupport d 𝕜 K) :=
  Finset.univ.sup (coordinateWordSeminorm 𝕜 K (k := k))

/-- The paper's q_m, expressed as a finite maximum over coordinate words. Its exact
multi-index formula is `Expected.MultiIndexSeminormFormula`. -/
def coordinateSupSeminorm {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) : Seminorm 𝕜 (FixedSupport d 𝕜 K) :=
  (Finset.range (m + 1)).sup (coordinateOrderSeminorm 𝕜 K)

/-- A multi-index is a multiset of coordinate directions; its multiplicity at i is αᵢ. -/
abbrev MultiIndex (d : ℕ) := Multiset (Fin d)

/-- The multiset model is bijective with the usual nonnegative integer coordinate vector. -/
def multiIndexCountsEquiv (d : ℕ) : MultiIndex d ≃ (Fin d → ℕ) :=
  Multiset.toFinsupp.toEquiv.trans Finsupp.equivFunOnFinite

/-- Successive ordinary coordinate derivatives, written from outermost to innermost. -/
def partialWord {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Space d → 𝕜) :
    List (Fin d) → Space d → 𝕜
  | [] => f
  | i :: l => fun x => fderiv ℝ (partialWord f l) x (coordinateVector d i)

/-- The usual multi-index derivative, using coordinates in increasing order. -/
def multiPartial {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Space d → 𝕜)
    (α : MultiIndex d) : Space d → 𝕜 := partialWord f (α.sort (· ≤ ·))

namespace Expected

def testSpaceType := (d : ℕ) → (𝕜 : Type) → [RCLike 𝕜] → Opens (Space d) → Type

def testSpaceValue : testSpaceType := fun _ 𝕜 _ Ω => TestSpace 𝕜 Ω

def fixedSupportType := (d : ℕ) → (𝕜 : Type) → [RCLike 𝕜] → Compacts (Space d) → Type

def fixedSupportValue : fixedSupportType := fun d 𝕜 _ K => FixedSupport d 𝕜 K

def distributionSpaceType := (d : ℕ) → (𝕜 : Type) → [RCLike 𝕜] → Opens (Space d) → Type

def distributionSpaceValue : distributionSpaceType := fun _ 𝕜 _ Ω => DistributionSpace 𝕜 Ω

def coordinateSeminormType := (d : ℕ) → (𝕜 : Type) → [RCLike 𝕜] →
  (K : Compacts (Space d)) → ℕ → Seminorm 𝕜 (FixedSupport d 𝕜 K)

def coordinateSeminormValue : coordinateSeminormType := fun _ 𝕜 _ K m => coordinateSupSeminorm 𝕜 K m

/-- Actual continuity of each fixed-support inclusion. -/
def StageContinuity : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ Ω),
    Continuous (stageInclusion 𝕜 hK)

/-- Universal property of the actual inductive-limit topology, including the complex-linear case.
The target is a locally convex real topological vector space with compatible scalar action. -/
def FinalTopology : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (F : Type*) [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F] (T : TestSpace 𝕜 Ω →ₗ[𝕜] F),
    Continuous T ↔ ∀ (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ Ω),
      Continuous (T ∘ stageInclusion 𝕜 hK)

/-- This also asserts pointwise equality of every ambient derivative after extension. -/
def ZeroExtensionProperties : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (V Ω : Opens (Space d)) (h : V ≤ Ω)
    (f : TestSpace 𝕜 V),
    (∀ x, zeroExtension 𝕜 h f x = f x) ∧
    (∀ x ∉ V, zeroExtension 𝕜 h f x = 0) ∧
    (∀ k x, iteratedFDeriv ℝ k (zeroExtension 𝕜 h f) x = iteratedFDeriv ℝ k f x)

/-- A support-free local-to-global smoothness lemma: a globally represented function
smooth on an open set and with topological support inside it is globally smooth. -/
def SmoothZeroExtension : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (V : Opens (Space d)) (f : Space d → 𝕜),
    ContDiffOn ℝ (⊤ : ℕ∞) f V → tsupport f ⊆ V → ContDiff ℝ (⊤ : ℕ∞) f

/-- Smooth cutoff with ambient compact support in V, equal to one on an open neighborhood. -/
def Cutoff : Prop :=
  ∀ (d : ℕ) (V : Opens (Space d)) (K : Compacts (Space d)),
    (K : Set (Space d)) ⊆ V → ∃ χ : TestSpace ℝ V,
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∃ U : Opens (Space d), (K : Set (Space d)) ⊆ U ∧ U ≤ V ∧ ∀ x ∈ U, χ x = 1

/-- Empty open sets have precisely the zero test. -/
def EmptyTests : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (f : TestSpace 𝕜 (⊥ : Opens (Space d))), f = 0

/-- The Fréchet derivative topology on a stage; the coordinate bridge is separate. -/
def FrechetStageTopology : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)),
    WithSeminorms (frechetSupSeminorm 𝕜 K)

/-- No conjugation in the scalar-linear continuous dual. -/
def PairingBilinear : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (T S : DistributionSpace 𝕜 Ω) (f g : TestSpace 𝕜 Ω) (a : 𝕜),
      T (f + g) = T f + T g ∧ T (a • f) = a * T f ∧
      (T + S) f = T f + S f ∧ (a • T) f = a * T f

def CoordinateEvaluationBound : Prop :=
  ∀ (d k : ℕ) (𝕜 : Type) [RCLike 𝕜] (A : Space d [×k]→L[ℝ] 𝕜) (a : Fin k → Fin d),
    ‖A (fun j => coordinateVector d (a j))‖ ≤ ‖A‖

/-- The full quantitative upper bound; it also covers zero variables and zero dimension. -/
def OperatorNormBound : Prop :=
  ∀ (d k : ℕ) (𝕜 : Type) [RCLike 𝕜] (A : Space d [×k]→L[ℝ] 𝕜) (M : ℝ),
    0 ≤ M → (∀ a : Fin k → Fin d, ‖A (fun j => coordinateVector d (a j))‖ ≤ M) →
      ‖A‖ ≤ (d : ℝ) ^ k * M

/-- Euclidean coordinates with their product Lebesgue measure. No norm isometry is asserted. -/
def CoordinateVolume : Prop :=
  ∀ d : ℕ, MeasureTheory.MeasurePreserving
    (@WithLp.ofLp 2 (Fin d → ℝ)) (euclideanVolume d) MeasureTheory.volume

/-- An individual coordinate is bounded by Euclidean length. -/
def CoordinateNorm : Prop :=
  ∀ (d : ℕ) (x : Space d) (i : Fin d), ‖x i‖ ≤ ‖x‖

def EmptyStage : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (f : FixedSupport d 𝕜 (⊥ : Compacts (Space d))),
    f = 0 ∧ ∀ k, frechetSeminorm 𝕜 ⊥ k f = 0

def FixedSupportExtension : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (V Ω : Opens (Space d)) (h : V ≤ Ω)
    (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ V)
    (f : FixedSupport d 𝕜 K),
    zeroExtension 𝕜 h (stageInclusion 𝕜 hK f) = stageInclusion 𝕜 (hK.trans h) f

/-- Restriction to real tests has a unique continuous complex-linear extension.
Its value on every complex test is prescribed, as is its value on φ+iψ. -/
def ComplexExtension : Prop :=
  ∀ (d : ℕ) (Ω : Opens (Space d)) (T : TestSpace ℝ Ω →L[ℝ] ℂ),
    ∃ S : DistributionSpace ℂ Ω,
      (∀ f, S f = T (realPart Ω f) + Complex.I * T (imagPart Ω f)) ∧
      (∀ φ ψ, S (complexifyTest Ω φ + Complex.I • complexifyTest Ω ψ) =
        T φ + Complex.I * T ψ) ∧
      (∀ φ, S (complexifyTest Ω φ) = T φ) ∧
      (∀ S' : DistributionSpace ℂ Ω,
        (∀ φ, S' (complexifyTest Ω φ) = T φ) → S' = S)

def CoordinateSeminormFormula : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)) (m : ℕ)
    (f : FixedSupport d 𝕜 K) (C : ℝ), 0 ≤ C →
    (coordinateSupSeminorm 𝕜 K m f ≤ C ↔
      ∀ k ≤ m, ∀ a : Fin k → Fin d, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ k f x (fun j => coordinateVector d (a j))‖ ≤ C)

def CoordinateStageTopology : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)),
    WithSeminorms (coordinateSupSeminorm 𝕜 K)

def LocalTestZeroExtension : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (V : Opens (Space d))
    (K : Compacts (Space d)) (_hK : (K : Set (Space d)) ⊆ V) (f : Space d → 𝕜),
    ContDiffOn ℝ (⊤ : ℕ∞) f V → Function.support f ∩ V ⊆ K →
    ∃ φ : TestSpace 𝕜 V, tsupport φ ⊆ K ∧ EqOn φ f V ∧ EqOn φ 0 Vᶜ

/-- The exact multi-index formula for the defining seminorm; the empty K case follows too. -/
def MultiIndexSeminormFormula : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)) (m : ℕ)
    (f : FixedSupport d 𝕜 K) (C : ℝ), 0 ≤ C →
    (coordinateSupSeminorm 𝕜 K m f ≤ C ↔
      ∀ α : MultiIndex d, α.card ≤ m → ∀ x ∈ K, ‖multiPartial f α x‖ ≤ C)

def ComplexScalarContinuity : Prop :=
  ∀ (d : ℕ) (Ω : Opens (Space d)),
    Continuous (fun p : ℂ × TestSpace ℂ Ω => p.1 • p.2)

def EmptyCoordinateSeminorm : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (f : FixedSupport d 𝕜 (⊥ : Compacts (Space d))) (m : ℕ),
    coordinateSupSeminorm 𝕜 ⊥ m f = 0

def MultiIndexCoordinates : Prop :=
  ∀ (d : ℕ) (α : MultiIndex d),
    (∀ i, multiIndexCountsEquiv d α i = α.count i) ∧
      α.card = ∑ i, multiIndexCountsEquiv d α i

/-- The same fixed-support function realizes extension, preserving all defining seminorms. -/
def ExtensionSeminorms : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (V Ω : Opens (Space d)) (h : V ≤ Ω)
    (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ V) (f : FixedSupport d 𝕜 K),
    ∃ g : FixedSupport d 𝕜 K,
      stageInclusion 𝕜 (hK.trans h) g = zeroExtension 𝕜 h (stageInclusion 𝕜 hK f) ∧
      (∀ m, coordinateSupSeminorm 𝕜 K m g = coordinateSupSeminorm 𝕜 K m f) ∧
      (∀ k, frechetSeminorm 𝕜 K k g = frechetSeminorm 𝕜 K k f)

def OrderSeminormComparison : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)) (k : ℕ)
    (f : FixedSupport d 𝕜 K),
      coordinateOrderSeminorm 𝕜 K k f ≤ frechetSeminorm 𝕜 K k f ∧
      frechetSeminorm 𝕜 K k f ≤ (d : ℝ) ^ k * coordinateOrderSeminorm 𝕜 K k f

/-- The defining finest-property, stated directly for arbitrary locally convex vector topologies. -/
def FinestTopology : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (t : TopologicalSpace (TestSpace 𝕜 Ω)),
    letI : TopologicalSpace (TestSpace 𝕜 Ω) := t
    ∀ [IsTopologicalAddGroup (TestSpace 𝕜 Ω)] [ContinuousSMul ℝ (TestSpace 𝕜 Ω)]
      [LocallyConvexSpace ℝ (TestSpace 𝕜 Ω)],
      TestFunction.topologicalSpace Ω 𝕜 ⊤ ≤ t ↔
        ∀ (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ Ω),
          Continuous (stageInclusion 𝕜 hK)

def StageCoverage : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (f : TestSpace 𝕜 Ω),
    ∃ (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ Ω)
      (g : FixedSupport d 𝕜 K), stageInclusion 𝕜 hK g = f

end Expected
end P102.U4
