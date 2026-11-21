import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ClosedForm
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Matrix.Normed

/-! Independent statements for the shifted-realization part of E11.
Forms use the manuscript's linear-first convention. The abstract statement
keeps the full form-space norm separate from the ambient L² norm.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexConjugate
universe u v w
namespace P201.Elliptic.NonsymmetricExpected

section Objects
variable {𝕜 : Type u} {H : Type v} {V : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- Transport only the algebraic form to its actual ambient domain. This is
the same `DenseForm.associatedOperator` as E10, without its symmetry hypotheses. -/
def embeddedForm (j : V →L[𝕜] H) (hi : Function.Injective j)
    (hd : DenseRange j) (B : V →L[𝕜] V →L⋆[𝕜] 𝕜) : DenseForm 𝕜 H where
  domain := j.range
  dense := hd
  form := LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd 𝕜)
    (fun u v => B ((LinearEquiv.ofInjective j.toLinearMap hi).symm u)
      ((LinearEquiv.ofInjective j.toLinearMap hi).symm v))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)

def ResolventAt (a : DenseForm 𝕜 H) (j : V →L[𝕜] H)
    (B : V →L[𝕜] V →L⋆[𝕜] 𝕜) (μ : ℝ) : Prop :=
    ∃ S : H →L[𝕜] V,
      (∀ f v, B (S f) v + (μ : 𝕜) * paperInner (𝕜 := 𝕜) (j (S f)) (j v) =
        paperInner (𝕜 := 𝕜) f (j v)) ∧
      (∀ f u, (∀ v, B u v + (μ : 𝕜) * paperInner (𝕜 := 𝕜) (j u) (j v) =
          paperInner (𝕜 := 𝕜) f (j v)) → u = S f) ∧
      Function.Injective (j.comp S) ∧ DenseRange (j.comp S) ∧
      Dense (a.associatedOperator.domain : Set H) ∧
      a.associatedOperator.IsClosed ∧
      (∀ u, u ∈ a.associatedOperator.domain ↔ u ∈ Set.range (j.comp S)) ∧
      (∀ u f, (u, f - (μ : 𝕜) • u) ∈ a.associatedOperator.graph ↔ j (S f) = u) ∧
      (∀ u f, (u, f - (μ : 𝕜) • u) ∈ a.associatedOperator.adjoint.graph ↔
        (j.comp S).adjoint f = u) ∧
      (IsCompactOperator j → IsCompactOperator (j.comp S))

end Objects

def AbstractResolvent : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} {V : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    (a : DenseForm 𝕜 H) (e : V ≃ₗ[𝕜] a.domain) (j : V →L[𝕜] H),
    (∀ v, (e v : H) = j v) →
    ∀ (B : V →L[𝕜] V →L⋆[𝕜] 𝕜),
    (∀ u v, B u v = a.form (e u) (e v)) →
    ∀ (μ α : ℝ), 0 < α →
    (∀ v, α * ‖v‖ ^ 2 ≤
      RCLike.re (B v v + (μ : 𝕜) * paperInner (𝕜 := 𝕜) (j v) (j v))) →
    ResolventAt a j B μ

end P201.Elliptic.NonsymmetricExpected

namespace P201Specs.Nonsymmetric
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

abbrev Coefficients (n : ℕ) (𝕜 : Type) :=
  (Space n → Matrix (Fin n) (Fin n) 𝕜) ×
    (Space n → Fin n → 𝕜) × (Space n → Fin n → 𝕜) × (Space n → 𝕜)

def Bounded {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (q : Coefficients n 𝕜) : Prop :=
  MemLp q.1 ∞ (domainMeasure Ω) ∧ MemLp q.2.1 ∞ (domainMeasure Ω) ∧
    MemLp q.2.2.1 ∞ (domainMeasure Ω) ∧ MemLp q.2.2.2 ∞ (domainMeasure Ω)

def Elliptic {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (q : Coefficients n 𝕜) (lam : ℝ) : Prop :=
  ∀ᵐ x ∂domainMeasure Ω, ∀ ξ : EuclideanSpace 𝕜 (Fin n),
    lam * ‖ξ‖ ^ 2 ≤ RCLike.re (∑ i, ∑ j, q.1 x i j * ξ j * conj (ξ i))

/-- Scalar extension casts all four real coefficient fields. -/
def complexify {n : ℕ} (q : Coefficients n ℝ) : Coefficients n ℂ :=
  ⟨(fun x i j => (q.1 x i j : ℂ)),
    (fun x i => (q.2.1 x i : ℂ)), (fun x i => (q.2.2.1 x i : ℂ)),
    (fun x => (q.2.2.2 x : ℂ))⟩

/-- Real principal ellipticity suffices for the complexified coefficients,
without symmetry of the real matrix. Boundedness of all four fields is preserved. -/
def Complexification : Prop :=
  ∀ {n : ℕ} {Ω : Domain n} {q : Coefficients n ℝ} {lam : ℝ},
    Bounded Ω q → Elliptic Ω q lam →
      Bounded Ω (complexify q) ∧ Elliptic Ω (complexify q) lam

/-- The exact four terms of the source, including the divergence lower term. -/
def form {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (q : Coefficients n 𝕜) (u v : H10 𝕜 Ω) : 𝕜 :=
  ∫ x, ((∑ i, ∑ j, q.1 x i j * hFirstDerivative u.val j x *
      conj (hFirstDerivative v.val i x)) +
    (∑ j, q.2.1 x j * hFirstDerivative u.val j x) * conj (hZeroUnderlying Ω v x) +
    hZeroUnderlying Ω u x * (∑ i, q.2.2.1 x i * conj (hFirstDerivative v.val i x)) +
    q.2.2.2 x * hZeroUnderlying Ω u x * conj (hZeroUnderlying Ω v x)) ∂domainMeasure Ω

/-- This bridge is required on the actual Sobolev closure, over either field. -/
def SobolevBridge : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∀ (𝕜 : Type) [RCLike 𝕜],
    Function.Injective (hZeroUnderlying (𝕜 := 𝕜) Ω) ∧
    DenseRange (hZeroUnderlying (𝕜 := 𝕜) Ω) ∧
    IsCompactOperator (hZeroUnderlying (𝕜 := 𝕜) Ω) ∧
    ∀ u : H10 𝕜 Ω,
      ‖u‖ ^ 2 = ‖hZeroUnderlying Ω u‖ ^ 2 + ‖hGradient u.val‖ ^ 2

/-- The bounded original form and Gårding estimate, with no symmetry or sign
restriction on the lower coefficients. The coercive shifts follow in assembly. -/
def Garding : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∀ (𝕜 : Type) [RCLike 𝕜] (q : Coefficients (m + 1) 𝕜), Bounded Ω q →
    ∀ lam : ℝ, 0 < lam → Elliptic Ω q lam →
    ∃ (B : H10 𝕜 Ω →L[𝕜] H10 𝕜 Ω →L⋆[𝕜] 𝕜) (C : ℝ),
      0 ≤ C ∧ (∀ u v, B u v = form Ω q u v) ∧
      (∀ u, (lam / 2) * ‖hGradient u.val‖ ^ 2 - C * ‖hZeroUnderlying Ω u‖ ^ 2 ≤
        RCLike.re (B u u))

/-- Full concrete shifted-realization conclusion allocated to E11. The later
Fredholm alternative is a separately allocated result. Real coefficients and
their complexification are included by the RCLike scalar parameter. -/
def PDE : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∀ (𝕜 : Type) [RCLike 𝕜] (q : Coefficients (m + 1) 𝕜), Bounded Ω q →
    ∀ lam : ℝ, 0 < lam → Elliptic Ω q lam →
    ∃ (B : H10 𝕜 Ω →L[𝕜] H10 𝕜 Ω →L⋆[𝕜] 𝕜) (C : ℝ)
      (hi : Function.Injective (hZeroUnderlying (𝕜 := 𝕜) Ω))
      (hd : DenseRange (hZeroUnderlying (𝕜 := 𝕜) Ω)),
      let a := P201.Elliptic.NonsymmetricExpected.embeddedForm (𝕜 := 𝕜) (H := Lp 𝕜 Ω 2)
        (V := H10 𝕜 Ω) (hZeroUnderlying (𝕜 := 𝕜) Ω) hi hd B
      0 ≤ C ∧ (∀ u v, B u v = form Ω q u v) ∧
      (∀ u, (lam / 2) * ‖hGradient u.val‖ ^ 2 - C * ‖hZeroUnderlying Ω u‖ ^ 2 ≤
        RCLike.re (B u u)) ∧
      IsCompactOperator (hZeroUnderlying (𝕜 := 𝕜) Ω) ∧
      ∀ μ : ℝ, C < μ →
        (∃ α : ℝ, 0 < α ∧ ∀ u,
          α * ‖u‖ ^ 2 ≤ RCLike.re (B u u +
            (μ : 𝕜) * P201.Elliptic.paperInner (𝕜 := 𝕜)
              (hZeroUnderlying Ω u) (hZeroUnderlying Ω u))) ∧
        P201.Elliptic.NonsymmetricExpected.ResolventAt (𝕜 := 𝕜) (H := Lp 𝕜 Ω 2) (V := H10 𝕜 Ω) a (hZeroUnderlying (𝕜 := 𝕜) Ω) B μ

def Assembly : Prop := SobolevBridge → Garding → PDE

end P201Specs.Nonsymmetric
