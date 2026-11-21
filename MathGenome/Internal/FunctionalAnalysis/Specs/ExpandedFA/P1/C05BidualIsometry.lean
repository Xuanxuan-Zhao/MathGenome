import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-!
Independent statements for `fa2:p1:c05:bidual-isometry`, paper.tex:961–972.
The scalar norm is absolute value over ℝ and modulus over ℂ. Both suprema
range over the entire closed unit ball of the continuous scalar-linear dual.
The canonical map, bidual, transpose, Banach property and reflexivity use
exactly the shared definitions. No completeness or nontriviality assumption
is made on either original space.
-/

namespace ExpandedFA.P1.C05BidualIsometry.Spec

universe u v w

/-- The absolute-value and real-part dual norm formulas, also at zero. -/
def DualNormFormula : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E),
    ‖x‖ = sSup ((fun f : E →L[𝕜] 𝕜 => ‖f x‖) '' {f | ‖f‖ ≤ 1}) ∧
    ‖x‖ = sSup ((fun f : E →L[𝕜] 𝕜 => RCLike.re (f x)) '' {f | ‖f‖ ≤ 1})

/-- Norm preservation for the canonical evaluation map. -/
def CanonicalEvaluationNorm : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E),
    ‖C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x‖ = ‖x‖

/-- The canonical map is scalar-linear and preserves all distances. -/
def CanonicalEvaluationLinearIsometry : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (∀ x y : E,
      C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E (x + y) =
        C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x +
          C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E y) ∧
    (∀ (a : 𝕜) (x : E),
      C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E (a • x) =
        a • C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x) ∧
    Isometry (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)

def CanonicalEvaluationInjective : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Function.Injective (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)

/-- The continuous scalar-linear dual distinguishes every pair of distinct vectors. -/
def DualSeparatesPoints : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x y : E),
    x ≠ y → ∃ f : E →L[𝕜] 𝕜, f x ≠ f y

/-- The continuous linear bidual is Banach in its operator norm. -/
def BidualBanach : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C01Banach.Spec.IsBanachSpaceValue ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)

/-- The canonical image is norm closed exactly when the domain is Banach. -/
def CanonicalEvaluationClosedRangeIffBanach : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    IsClosed (Set.range (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)) ↔
      C01Banach.Spec.IsBanachSpaceValue E

/-- Surjectivity of the canonical map forces completeness. -/
def ReflexiveBanach : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
      C01Banach.Spec.IsBanachSpaceValue E

/-- The Banach transpose has the same operator norm as the original map. -/
def BanachTransposeNormEquality : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    ‖C04Annihilators.Spec.BanachTransposeValue 𝕜 E F T‖ = ‖T‖

/-- All clauses of the source theorem, for the original norm and canonical maps. -/
def CompleteBidualTheorem : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (∀ x : E,
      ‖x‖ = sSup ((fun f : E →L[𝕜] 𝕜 => ‖f x‖) '' {f | ‖f‖ ≤ 1}) ∧
      ‖x‖ = sSup ((fun f : E →L[𝕜] 𝕜 => RCLike.re (f x)) '' {f | ‖f‖ ≤ 1})) ∧
    ((∀ x y : E,
      C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E (x + y) =
        C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x +
          C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E y) ∧
      (∀ (a : 𝕜) (x : E),
        C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E (a • x) =
          a • C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x) ∧
      Isometry (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)) ∧
    (∀ x y : E, x ≠ y → ∃ f : E →L[𝕜] 𝕜, f x ≠ f y) ∧
    C01Banach.Spec.IsBanachSpaceValue ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) ∧
    (IsClosed (Set.range (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)) ↔
      C01Banach.Spec.IsBanachSpaceValue E) ∧
    (C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
      C01Banach.Spec.IsBanachSpaceValue E) ∧
    (∀ (F : Type w) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
      ‖C04Annihilators.Spec.BanachTransposeValue 𝕜 E F T‖ = ‖T‖)

end ExpandedFA.P1.C05BidualIsometry.Spec
