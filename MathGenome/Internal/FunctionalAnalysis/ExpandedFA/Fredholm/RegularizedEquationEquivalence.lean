import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RegularizedEquationEquivalence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.DualRegularizerFiniteness

namespace ExpandedFA.Fredholm
universe u₁ v₁ u₂ v₂ w

/-- Left multiplication preserves exactly every solution set precisely when
the regularizer is injective. No compactness is needed for this criterion. -/
theorem left_regularized_equation_iff_injective :
  ∀ {𝕂 : Type w} [RCLike 𝕂]
    {X₁ : Type u₁} {X₂ : Type u₂}
    [NormedAddCommGroup X₁] [NormedSpace 𝕂 X₁]
    [NormedAddCommGroup X₂] [NormedSpace 𝕂 X₂]
    (T : X₁ →L[𝕂] X₂) (R : X₂ →L[𝕂] X₁),
    (∀ (f : X₂) (x : X₁), R (T x) = R f ↔ T x = f) ↔
      Function.Injective R := by
  intro 𝕂 _ X₁ X₂ _ _ _ _ T R
  constructor
  · intro h a b hab
    have hzero : (0 : X₂) = a - b := by
      simpa only [map_zero] using
        (h (a - b) 0).mp (by simp only [map_zero, map_sub, hab, sub_self])
    exact sub_eq_zero.mp hzero.symm
  · intro hR f x
    exact ⟨fun h => hR h, fun h => congrArg R h⟩

/-- Right-regularized solutions map onto every original solution set
precisely when the regularizer is surjective. -/
theorem right_regularized_equation_iff_surjective :
  ∀ {𝕂 : Type w} [RCLike 𝕂]
    {X₁ : Type u₁} {X₂ : Type u₂}
    [NormedAddCommGroup X₁] [NormedSpace 𝕂 X₁]
    [NormedAddCommGroup X₂] [NormedSpace 𝕂 X₂]
    (T : X₁ →L[𝕂] X₂) (R : X₂ →L[𝕂] X₁),
    (∀ (f : X₂) (x : X₁),
      (∃ z : X₂, T (R z) = f ∧ R z = x) ↔ T x = f) ↔
      Function.Surjective R := by
  intro 𝕂 _ X₁ X₂ _ _ _ _ T R
  constructor
  · intro h x
    obtain ⟨z, _, hz⟩ := (h (T x) x).mpr rfl
    exact ⟨z, hz⟩
  · intro hR f x
    constructor
    · rintro ⟨z, hf, hz⟩
      simpa only [hz] using hf
    · intro hx
      obtain ⟨z, hz⟩ := hR x
      exact ⟨z, by simpa only [hz] using hx, hz⟩

/-- Regularization in nondegenerate bilinear normed dual systems, over
R or C, including the two exact equivalence tests. -/
theorem bilinear_regularization :
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
      Function.Surjective R) := by
  intro 𝕂 _ X₁ Y₁ X₂ Y₂ _ _ _ _ _ _ _ _ C₁ C₂ T U R V
    h₁X h₁Y h₂X h₂Y hT hR hX₁ hX₂ hY₁ hY₂
  exact ⟨bilinear_regularizer_finiteness C₁ C₂ T U R V
      h₁X h₁Y h₂X h₂Y hT hR hX₁ hX₂ hY₁ hY₂,
    left_regularized_equation_iff_injective T R,
    right_regularized_equation_iff_surjective T R⟩

end ExpandedFA.Fredholm
