import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.SpheresAndTori
import Mathlib.NumberTheory.Real.Irrational

namespace SmoothManifolds.IrrationalLineData
open ModelData AtlasData MapData SphereTorusData Set

/-- The usual global coordinate on the real line. -/
def realCoordinates : ℝ ≃ₜ ModelSpace 1 .euclidean where
  toFun t := ⟨fun _ => t, mem_univ _⟩
  invFun x := x.val 0
  left_inv _ := rfl
  right_inv x := by ext i; exact congrArg x.val (Subsingleton.elim 0 i)
  continuous_toFun := by fun_prop
  continuous_invFun := (continuous_apply 0).comp continuous_subtype_val

def realChart : ModelChart 1 .euclidean ℝ := realCoordinates.toOpenPartialHomeomorph

def realAtlas : Set (ModelChart 1 .euclidean ℝ) := {realChart}

/-- The lift fixes the ordering of the two quotient coordinates. -/
def lineLift (α t : ℝ) : Euclidean 2 := ![t, α * t]

def irrationalLine (α t : ℝ) : FlatTorus 2 := quotientProjection 2 (lineLift α t)

/-- The derivative in quotient coordinates, including its scale. -/
noncomputable def lineLinear (α : ℝ) : Euclidean 1 →L[ℝ] Euclidean 2 :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, α • ContinuousLinearMap.proj 0]

def lineRange (α : ℝ) : Set (FlatTorus 2) := range (irrationalLine α)

def rangeParam (α : ℝ) (t : ℝ) : lineRange α := ⟨irrationalLine α t, ⟨t, rfl⟩⟩

/-- The final topology transported from R; this definition does not assume
injectivity or any of the conclusions of the example. -/
def immersedTopology (α : ℝ) : TopologicalSpace (lineRange α) :=
  TopologicalSpace.coinduced (rangeParam α) inferInstance

end SmoothManifolds.IrrationalLineData

namespace Specs.SmoothManifolds.Ch03.IrrationalLine
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.FiniteRegularityData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.IrrationalLineData Set

def irrationalLineType := ℝ → ℝ → FlatTorus 2
def irrationalLineValue : irrationalLineType := irrationalLine

def lineLiftType := ℝ → ℝ → Euclidean 2
def lineLiftValue : lineLiftType := lineLift

def lineLinearType := ℝ → Euclidean 1 →L[ℝ] Euclidean 2
noncomputable def lineLinearValue : lineLinearType := lineLinear

def realAtlasType := Set (ModelChart 1 .euclidean ℝ)
def realAtlasValue : realAtlasType := realAtlas

def lineRangeType := ℝ → Set (FlatTorus 2)
def lineRangeValue : lineRangeType := lineRange

def rangeParamType := (α : ℝ) → ℝ → lineRange α
def rangeParamValue : rangeParamType := rangeParam

def immersedTopologyType := (α : ℝ) → TopologicalSpace (lineRange α)
def immersedTopologyValue : immersedTopologyType := immersedTopology

/-- The structures in the later statements exist, with the standard atlases. -/
def standardManifoldsType : Prop :=
  (∃ S : SmoothManifold 1 .euclidean ℝ,
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) realAtlas) ∧
  (∃ Q : SmoothManifold 2 .euclidean (FlatTorus 2),
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))

def injectiveType : Prop := ∀ α : ℝ, Irrational α → Function.Injective (irrationalLine α)

/-- Every actual small-box quotient chart has the stated derivative, using the
ordinary real coordinate. In particular the derivative sends 1 to (1,α). -/
def quotientDerivativeType : Prop :=
  ∀ (α t : ℝ) (a : Euclidean 2) (ε : ℝ)
    (d : ModelChart 2 .euclidean (FlatTorus 2)),
    IsAngleChart a ε d → irrationalLine α t ∈ d.source →
      chartDerivative realChart d (irrationalLine α) t = lineLinear α ∧
      lineLinear α (fun _ => 1) = ![1, α] ∧
      lineLinear α (fun _ => 1) ≠ 0

def smoothImmersionType : Prop :=
  ∀ (α : ℝ) (S : SmoothManifold 1 .euclidean ℝ)
    (Q : SmoothManifold 2 .euclidean (FlatTorus 2)),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) realAtlas →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2) →
    IsSmoothMap S Q (irrationalLine α) ∧ IsImmersion S Q (irrationalLine α)

/-- The topology on the range here is exactly the ambient subspace topology. -/
def notHomeomorphType : Prop :=
  ∀ α : ℝ, ¬ ∃ h : ℝ ≃ₜ lineRange α, ∀ t, (h t).val = irrationalLine α t

def notEmbeddingType : Prop :=
  ∀ (α : ℝ) (S : SmoothManifold 1 .euclidean ℝ)
    (Q : SmoothManifold 2 .euclidean (FlatTorus 2)),
    ¬ IsSmoothEmbedding S Q (irrationalLine α)

/-- For irrational slope the canonical final topology is strictly finer than
the subspace topology. Its standard structure is transported along the SAME
parametrization, and its inclusion into the SAME quotient torus is smooth and
an immersion. Topology order is reversed: t ≤ s means t is finer than s. -/
def immersedRangeType : Prop :=
  ∀ (α : ℝ), Irrational α →
  ∀ (S : SmoothManifold 1 .euclidean ℝ)
    (Q : SmoothManifold 2 .euclidean (FlatTorus 2)),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) realAtlas →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2) →
    immersedTopology α < (inferInstance : TopologicalSpace (lineRange α)) ∧
    (letI : TopologicalSpace (lineRange α) := immersedTopology α
     ∃ h : ℝ ≃ₜ lineRange α,
      (∀ t, h t = rangeParam α t) ∧
      ∃ R : SmoothManifold 1 .euclidean (lineRange α),
        R.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (transportAtlas h realAtlas) ∧
        IsSmoothMap R Q Subtype.val ∧ IsImmersion R Q Subtype.val)

end Specs.SmoothManifolds.Ch03.IrrationalLine
