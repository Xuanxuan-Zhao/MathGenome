import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.Existence
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Projection

/-! Independent statements for `fa2:p2:hilbert-prox`, paper.tex:8461–8477.
The variational inequality is written with real finite values, so subtraction
never subtracts infinities. Its domain guard is part of the characterization. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Proximal.VariationalSpec
open P1.ExtendedConvexFunctions
universe u

def VariationalInequalityType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → ℝ → H → H → Prop

def VariationalInequalityValue : VariationalInequalityType.{u} :=
  fun H _ _ φ μ f u => P1.ExtendedConvexFunctions.Spec.finiteDomainValue H φ u ∧
    ∀ (v : H) (r s : ℝ), φ u = (r : WithTop ℝ) → φ v = (s : WithTop ℝ) →
      ⟪f - u, v - u⟫_ℝ ≤ μ * (s - r)

def MinimizerIffVariational : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H), P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f u : H,
      Spec.IsProximalMinimizerValue H φ μ f u ↔ VariationalInequalityValue H φ μ f u

def VariationalIffSubgradient : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : ExtendedFunction H) (μ : ℝ), 0 < μ → ∀ f u : H,
      VariationalInequalityValue H φ μ f u ↔
        μ⁻¹ • (f - u) ∈ Spec.HilbertSubdifferentialValue H φ u

/-- The chosen proximal map has both equivalent characterizations, for every
candidate u, under exactly the standing source hypotheses. -/
def ProximalCharacterization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f u : H,
      (u = Spec.ProximalMapValue H φ μ f ↔ VariationalInequalityValue H φ μ f u) ∧
      (u = Spec.ProximalMapValue H φ μ f ↔
        μ⁻¹ • (f - u) ∈ Spec.HilbertSubdifferentialValue H φ u)

def FirmBound : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f g : H,
      let u := Spec.ProximalMapValue H φ μ f
      let z := Spec.ProximalMapValue H φ μ g
      ‖u - z‖ ^ 2 ≤ ⟪f - g, u - z⟫_ℝ

def Nonexpansive : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f g : H,
      ‖Spec.ProximalMapValue H φ μ f - Spec.ProximalMapValue H φ μ g‖ ≤ ‖f - g‖

/-- The indicator is zero on K and +∞ elsewhere; equality is equality of maps. -/
def IndicatorProjection : Prop := by
  classical
  exact ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : Set H) (hne : K.Nonempty) (hclosed : IsClosed K) (hc : Convex ℝ K)
    (μ : ℝ), 0 < μ →
    Spec.ProximalMapValue H (fun v => if v ∈ K then 0 else ⊤) μ =
      Hilbert.Projection.Spec.ConvexProjectionValue ℝ H K hne hclosed hc

end ExpandedFA.Proximal.VariationalSpec
