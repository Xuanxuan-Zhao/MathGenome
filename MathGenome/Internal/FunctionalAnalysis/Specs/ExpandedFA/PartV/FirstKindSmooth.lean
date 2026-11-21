import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.VolterraSmoothness

/-! First-kind clause of paper.tex, `fa2:p5:first-kind-smooth` (21951–21956).
We state the result on `[a,b]`; `a=0,b=T` is the source interval. The equation
uses the actual scalar kernel and ordinary scalar multiplication. The clamped
extension of `u` agrees with `u` throughout the integration interval. -/
noncomputable section
open Set MeasureTheory
namespace ExpandedFA.PartV

/-- The original first-kind integral equation, including its initial point. -/
def firstKindVolterraEquation {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    (hab : a ≤ b) (k : ℝ × ℝ → 𝕜)
    (g u : C(VolterraInterval a b, 𝕜)) : Prop :=
  ∀ t : VolterraInterval a b,
    (∫ s in a..(t : ℝ), k ((t : ℝ), s) * volterraIntervalExtension hab u s) = g t

namespace FirstKindSmoothSpec

/-- Every scalar `C¹` kernel on an open neighborhood of the closed triangle,
with nonvanishing diagonal, and every native closed-interval `C¹` datum are
covered. Existence is equivalent to endpoint compatibility for all `a≤b`;
uniqueness is asserted on positive intervals only. -/
def C1Solvability : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
  (a b : ℝ) (hab : a ≤ b) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
  (hsub : volterraTriangle a b ⊆ U) (k : ℝ × ℝ → 𝕜)
  (hk : ContDiffOn ℝ 1 k U)
  (hne : ∀ t : VolterraInterval a b, k (t, t) ≠ 0)
  (g : C(VolterraInterval a b, 𝕜)),
  ContDiffOn ℝ 1 (volterraIntervalExtension hab g) (Icc a b) →
  ((∃ u, firstKindVolterraEquation hab k g u) ↔ g ⟨a, le_rfl, hab⟩ = 0) ∧
  (a < b → ∀ u v, firstKindVolterraEquation hab k g u →
    firstKindVolterraEquation hab k g v → u = v)

/-- On the zero interval every scalar-valued function is continuous. Every
such function solves the equation exactly when the datum vanishes. In that
case the solution is not unique (the constants zero and one already differ).
No kernel regularity or diagonal hypothesis is needed for this endpoint. -/
def SingletonClassification : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
  (a : ℝ) (k : ℝ × ℝ → 𝕜) (g : C(VolterraInterval a a, 𝕜)),
  (∀ u, firstKindVolterraEquation (le_refl a) k g u ↔ g ⟨a, le_rfl, le_rfl⟩ = 0) ∧
  (g ⟨a, le_rfl, le_rfl⟩ = 0 →
    ¬ ∃! u, firstKindVolterraEquation (le_refl a) k g u)

end FirstKindSmoothSpec
end ExpandedFA.PartV
