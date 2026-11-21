import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.RectifiableStieltjes

/-! Independent statements for paper.tex:632–669 (D12.03.04).
The primitive is weakly holomorphic. Continuity is imposed on f, not on a
certificate of analyticity. Both contour integrals use the canonical paths and
integrals from the preceding goals, including arbitrary compact intervals. -/
noncomputable section
namespace Specs.D12Complex.Ch03.PrimitivePeriodCriterion
open _root_.D12Complex

def IsPrimitive_type := Set ℂ → (ℂ → ℂ) → (ℂ → ℂ) → Prop
def IsPrimitive_value : IsPrimitive_type :=
  fun Ω f F => HolomorphicOn Ω F ∧ ∀ z ∈ Ω, deriv F z = f z

def EndpointIndependent_type := Set ℂ → (ℂ → ℂ) → Prop
def EndpointIndependent_value : EndpointIndependent_type :=
  fun Ω f => ∀ γ η : PiecewiseC1Path, γ.trace ⊆ Ω → η.trace ⊆ Ω →
    γ.path.source = η.path.source → γ.path.target = η.path.target →
    γ.integral f = η.integral f

def ZeroPeriods_type := Set ℂ → (ℂ → ℂ) → Prop
def ZeroPeriods_value : ZeroPeriods_type :=
  fun Ω f => ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed → γ.integral f = 0

def piecewise_endpoint_type : Prop :=
  ∀ (Ω : Set ℂ) (f F : ℂ → ℂ), ContinuousOn f Ω → IsPrimitive_value Ω f F →
    ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω →
      γ.integral f = F γ.path.target - F γ.path.source

def primitive_endpointIndependent_type : Prop :=
  ∀ (Ω : Set ℂ) (f F : ℂ → ℂ), ContinuousOn f Ω → IsPrimitive_value Ω f F →
    EndpointIndependent_value Ω f

def endpointIndependent_iff_zeroPeriods_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), ContinuousOn f Ω →
    (EndpointIndependent_value Ω f ↔ ZeroPeriods_value Ω f)

def exists_primitive_of_endpointIndependent_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → ContinuousOn f Ω →
    EndpointIndependent_value Ω f → ∃ F, IsPrimitive_value Ω f F

def primitive_criterion_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → ContinuousOn f Ω →
    ((∃ F, IsPrimitive_value Ω f F) ↔ EndpointIndependent_value Ω f) ∧
    (EndpointIndependent_value Ω f ↔ ZeroPeriods_value Ω f)

def rectifiable_endpoint_type : Prop :=
  ∀ (Ω : Set ℂ) (f F : ℂ → ℂ), ContinuousOn f Ω → IsPrimitive_value Ω f F →
    ∀ γ : ComplexPath, Stieltjes.Rectifiable γ → γ.trace ⊆ Ω →
      Stieltjes.contourIntegral γ f = F γ.target - F γ.source

def zero_derivative_constant_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω F →
    (∀ z ∈ Ω, deriv F z = 0) → ∃ c : ℂ, ∀ z ∈ Ω, F z = c

def primitive_unique_type : Prop :=
  ∀ (Ω : Set ℂ) (f F G : ℂ → ℂ), IsDomain Ω →
    IsPrimitive_value Ω f F → IsPrimitive_value Ω f G →
      ∃ c : ℂ, ∀ z ∈ Ω, F z = G z + c

end Specs.D12Complex.Ch03.PrimitivePeriodCriterion
