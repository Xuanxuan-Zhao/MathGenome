import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.DualRegularizerFiniteness

/-! Independent statements for `fa2:p2:dual-regularization`, paper.tex
10386–10433. All normed spaces may be incomplete. Pairings are algebraic,
nondegenerate bilinear maps over either manuscript scalar field. The solution
criteria are stated for arbitrary bounded T and R, hence in particular for
left and right compact-defect regularizers. -/
namespace ExpandedFA.Fredholm.RegularizedEquationEquivalenceSpec
universe u₁ v₁ u₂ v₂ w

/-- Equality of the left-regularized and original solution sets for every
right-hand side, with no restriction to solvable right-hand sides. -/
def LeftCriterionAll : Prop :=
  ∀ {𝕂 : Type w} [RCLike 𝕂]
    {X₁ : Type u₁} {X₂ : Type u₂}
    [NormedAddCommGroup X₁] [NormedSpace 𝕂 X₁]
    [NormedAddCommGroup X₂] [NormedSpace 𝕂 X₂]
    (T : X₁ →L[𝕂] X₂) (R : X₂ →L[𝕂] X₁),
    (∀ (f : X₂) (x : X₁), R (T x) = R f ↔ T x = f) ↔
      Function.Injective R

/-- The image under R of the right-regularized solution set is the entire
original solution set, for every right-hand side. The existential includes
the right-regularized equation itself as well as the image identity. -/
def RightCriterionAll : Prop :=
  ∀ {𝕂 : Type w} [RCLike 𝕂]
    {X₁ : Type u₁} {X₂ : Type u₂}
    [NormedAddCommGroup X₁] [NormedSpace 𝕂 X₁]
    [NormedAddCommGroup X₂] [NormedSpace 𝕂 X₂]
    (T : X₁ →L[𝕂] X₂) (R : X₂ →L[𝕂] X₁),
    (∀ (f : X₂) (x : X₁),
      (∃ z : X₂, T (R z) = f ∧ R z = x) ↔ T x = f) ↔
      Function.Surjective R

/-- Full regularization theorem, including all finite kernel/cokernel,
closed range, annihilator and dimension conclusions in both systems and
both exact solution criteria. There is no bound on either pairing. -/
def BilinearRegularizationAll : Prop :=
  ∀ {𝕂 : Type w} [RCLike 𝕂]
    {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
    [NormedAddCommGroup X₁] [NormedSpace 𝕂 X₁]
    [NormedAddCommGroup Y₁] [NormedSpace 𝕂 Y₁]
    [NormedAddCommGroup X₂] [NormedSpace 𝕂 X₂]
    [NormedAddCommGroup Y₂] [NormedSpace 𝕂 Y₂]
    (C₁ : Y₁ →ₗ[𝕂] X₁ →ₗ[𝕂] 𝕂)
    (C₂ : Y₂ →ₗ[𝕂] X₂ →ₗ[𝕂] 𝕂)
    (T : X₁ →L[𝕂] X₂) (U : Y₂ →L[𝕂] Y₁)
    (R : X₂ →L[𝕂] X₁) (V : Y₁ →L[𝕂] Y₂),
    (∀ x, (∀ y, C₁ y x = 0) → x = 0) →
    (∀ y, (∀ x, C₁ y x = 0) → y = 0) →
    (∀ x, (∀ y, C₂ y x = 0) → x = 0) →
    (∀ y, (∀ x, C₂ y x = 0) → y = 0) →
    (∀ x y, C₂ y (T x) = C₁ (U y) x) →
    (∀ f g, C₁ g (R f) = C₂ (V g) f) →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id 𝕂 X₁ - R.comp T).toLinearMap →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id 𝕂 X₂ - T.comp R).toLinearMap →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id 𝕂 Y₁ - U.comp V).toLinearMap →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (ContinuousLinearMap.id 𝕂 Y₂ - V.comp U).toLinearMap →
    DualRegularizerFinitenessSpec.BilinearConclusion C₁ C₂ T U ∧
    ((∀ (f : X₂) (x : X₁), R (T x) = R f ↔ T x = f) ↔
      Function.Injective R) ∧
    ((∀ (f : X₂) (x : X₁),
      (∃ z : X₂, T (R z) = f ∧ R z = x) ↔ T x = f) ↔
      Function.Surjective R)

end ExpandedFA.Fredholm.RegularizedEquationEquivalenceSpec
