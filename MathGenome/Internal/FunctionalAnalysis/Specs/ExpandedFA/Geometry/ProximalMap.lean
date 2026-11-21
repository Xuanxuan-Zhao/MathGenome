import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.Definitions

/-! Independent statements for `fa2:p3:subgradient` and the proximal assertions
in `fa2:p2:potential-vi`. Values lie in ℝ ∪ {+∞}; subgradients are the canonical
Hilbert vectors, transported to the continuous dual by the real Riesz map.
No nontriviality, dimension, domain-interior, or bounded-below assumption occurs. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Geometry.ProximalMap.Spec
open P1.ExtendedConvexFunctions
universe u

def IdentityPlusSubgradientType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → ℝ → Set (H × H)

/-- The graph of I + μ∂φ, with input u and output f. -/
def IdentityPlusSubgradientValue : IdentityPlusSubgradientType.{u} :=
  fun H _ _ φ μ => {p | ∃ a ∈ Proximal.Spec.HilbertSubdifferentialValue H φ p.1,
    p.2 = p.1 + μ • a}

def ResolventType := Proximal.Spec.ProximalMapType.{u}

/-- Choice from the inverse graph; the theorems below establish totality,
uniqueness and agreement with the independently defined proximal map. -/
def ResolventValue : ResolventType.{u} :=
  fun H _ _ φ μ f => Classical.epsilon
    (fun u => (u, f) ∈ IdentityPlusSubgradientValue H φ μ)

def RieszIdentification : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H) (x a : H),
    a ∈ Proximal.Spec.HilbertSubdifferentialValue H φ x ↔
      InnerProductSpace.toDual ℝ H a ∈ BanachConvex.Spec.SubdifferentialValue H φ x

/-- In fact monotonicity holds for every extended function. -/
def SubgradientMonotone : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H) (x y a b : H),
    a ∈ Proximal.Spec.HilbertSubdifferentialValue H φ x →
    b ∈ Proximal.Spec.HilbertSubdifferentialValue H φ y →
    0 ≤ ⟪a - b, x - y⟫_ℝ

def GraphCharacterization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f x : H,
    (x, f) ∈ IdentityPlusSubgradientValue H φ μ ↔
      x = Proximal.Spec.ProximalMapValue H φ μ f

def Onto : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      ∃ x, (x, f) ∈ IdentityPlusSubgradientValue H φ μ

def UniquePreimage : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      ∃! x, (x, f) ∈ IdentityPlusSubgradientValue H φ μ

def ResolventEqProximal : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ →
      ResolventValue H φ μ = Proximal.Spec.ProximalMapValue H φ μ

def ResolventInverse : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f x : H,
      (x, f) ∈ IdentityPlusSubgradientValue H φ μ ↔ x = ResolventValue H φ μ f

/-- Global minimization includes infinite-valued competitors; every minimizer
is precisely Jμ f. The finite-domain condition is retained. -/
def ResolventMinimization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      Proximal.Spec.IsProximalMinimizerValue H φ μ f (ResolventValue H φ μ f) ∧
      ∀ x, Proximal.Spec.IsProximalMinimizerValue H φ μ f x ↔
        x = ResolventValue H φ μ f

def ResidualSubgradient : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      μ⁻¹ • (f - ResolventValue H φ μ f) ∈
        Proximal.Spec.HilbertSubdifferentialValue H φ (ResolventValue H φ μ f)

def FirmBound : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f g : H,
      ‖ResolventValue H φ μ f - ResolventValue H φ μ g‖ ^ 2 ≤
        ⟪f - g, ResolventValue H φ μ f - ResolventValue H φ μ g⟫_ℝ

end ExpandedFA.Geometry.ProximalMap.Spec
