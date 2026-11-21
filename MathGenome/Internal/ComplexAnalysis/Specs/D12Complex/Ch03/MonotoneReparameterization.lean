import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.RectifiableStieltjes

/-! All monotone parameter changes, paper.tex:729–747. Parameter maps are
continuous on their actual compact interval and may have constant plateaus.
Image equality expresses both the range condition and surjectivity. The
variation remains extended-real valued, including on degenerate intervals.
The last two statements specialize the general Stieltjes laws to the canonical
continuous path and its contour integral. -/
noncomputable section
open Set
open scoped ENNReal

namespace D12Complex.ComplexPath

/-- Composition on a specified compact parameter interval. The range and
continuity hypotheses refer only to that interval, including its endpoints. -/
def reparameterize (γ : ComplexPath) {c d : ℝ} (hcd : c ≤ d) (φ : ℝ → ℝ)
    (hc : ContinuousOn φ (Icc c d)) (hi : φ '' Icc c d = Icc γ.a γ.b) : ComplexPath :=
  ⟨c, d, hcd, γ ∘ φ,
    γ.continuousOn.comp hc (fun _x hx => hi ▸ mem_image_of_mem φ hx)⟩

end D12Complex.ComplexPath

namespace Specs.D12Complex.Ch03.MonotoneReparameterization
open _root_.D12Complex _root_.D12Complex.Stieltjes

def reparameterize_type := (γ : ComplexPath) → {c d : ℝ} → (hcd : c ≤ d) →
  (φ : ℝ → ℝ) → ContinuousOn φ (Icc c d) →
  φ '' Icc c d = Icc γ.a γ.b → ComplexPath

def reparameterize_value : reparameterize_type := @_root_.D12Complex.ComplexPath.reparameterize

def variation_monotone_type : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c ≤ d → ∀ (γ : ℝ → ℂ) (φ : ℝ → ℝ),
    MonotoneOn φ (Icc c d) → φ '' Icc c d = Icc a b →
    totalVariation (γ ∘ φ) c d = totalVariation γ a b

def variation_antitone_type : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c ≤ d → ∀ (γ : ℝ → ℂ) (φ : ℝ → ℝ),
    AntitoneOn φ (Icc c d) → φ '' Icc c d = Icc a b →
    totalVariation (γ ∘ φ) c d = totalVariation γ a b

def integral_monotone_type : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c ≤ d → ∀ (u γ : ℝ → ℂ) (φ : ℝ → ℝ),
    ContinuousOn u (Icc a b) → totalVariation γ a b < ⊤ →
    ContinuousOn φ (Icc c d) → MonotoneOn φ (Icc c d) →
    φ '' Icc c d = Icc a b →
    integral c d (u ∘ φ) (γ ∘ φ) = integral a b u γ

def integral_antitone_type : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c ≤ d → ∀ (u γ : ℝ → ℂ) (φ : ℝ → ℝ),
    ContinuousOn u (Icc a b) → totalVariation γ a b < ⊤ →
    ContinuousOn φ (Icc c d) → AntitoneOn φ (Icc c d) →
    φ '' Icc c d = Icc a b →
    integral c d (u ∘ φ) (γ ∘ φ) = -integral a b u γ

def contour_monotone_type : Prop :=
  ∀ (γ : ComplexPath), Rectifiable γ → ∀ (f : ℂ → ℂ),
    ContinuousOn f γ.trace → ∀ {c d : ℝ} (hcd : c ≤ d) (φ : ℝ → ℝ),
    MonotoneOn φ (Icc c d) →
    ∀ (hc : ContinuousOn φ (Icc c d)) (hi : φ '' Icc c d = Icc γ.a γ.b),
    let η := γ.reparameterize hcd φ hc hi
    polygonalLength η = polygonalLength γ ∧ Rectifiable η ∧
      contourIntegral η f = contourIntegral γ f

def contour_antitone_type : Prop :=
  ∀ (γ : ComplexPath), Rectifiable γ → ∀ (f : ℂ → ℂ),
    ContinuousOn f γ.trace → ∀ {c d : ℝ} (hcd : c ≤ d) (φ : ℝ → ℝ),
    AntitoneOn φ (Icc c d) →
    ∀ (hc : ContinuousOn φ (Icc c d)) (hi : φ '' Icc c d = Icc γ.a γ.b),
    let η := γ.reparameterize hcd φ hc hi
    polygonalLength η = polygonalLength γ ∧ Rectifiable η ∧
      contourIntegral η f = -contourIntegral γ f

end Specs.D12Complex.Ch03.MonotoneReparameterization
