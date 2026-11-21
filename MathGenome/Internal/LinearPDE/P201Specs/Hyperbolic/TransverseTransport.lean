import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.Transport
import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.ContinuityEquation

/-! Independent statements for the complete proposition
`prop:pde-transport-jacobian`, paper.tex:3687–3736.
The local clause is independent of the bounded slab hypotheses. Tangent
independence is expressed invariantly: no nonzero linear combination of the
elapsed-time vector and the chart differential vanishes. Since both spaces
have dimension n+1, this is precisely the usual transverse frame condition.
The chart need only be an immersion locally; the proved coordinate map
will in particular give an embedded restriction. No flow-box or PDE solution
is included in the input data. -/
noncomputable section
open Set
open scoped ContDiff
namespace P201Specs.Hyperbolic

/-- A C¹ local parametrization of a hypersurface in the original field domain.
Regularity and transversality at the base point ensure it is a chart after
restriction; no global injectivity assumption is needed. -/
structure HypersurfaceChart {n : ℕ} (b : LocalField n) where
  parameterDomain : Set (Space n)
  open_parameterDomain : IsOpen parameterDomain
  parametrization : Space n → ℝ × Space n
  regular : ContDiffOn ℝ 1 parametrization parameterDomain
  in_domain : MapsTo parametrization parameterDomain b.domain

/-- Columns: (1,b) and the tangent differential of the prescribed chart. -/
def transverseFrame {n : ℕ} (b : LocalField n) (σ : Space n → ℝ × Space n)
    (y : Space n) : (ℝ × Space n) →L[ℝ] (ℝ × Space n) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (1, b.velocity (σ y))).coprod
    (fderiv ℝ σ y)

/-- Linear independence of the transverse vector and all chart tangent
vectors. This coordinate-free version quantifies over every coefficient. -/
def IsTransverseAt {n : ℕ} (b : LocalField n) (σ : Space n → ℝ × Space n)
    (y : Space n) : Prop := Function.Injective (transverseFrame b σ y)

/-- Actual elapsed-time flow from the prescribed hypersurface. -/
def transverseFlowMap {n : ℕ} (b : LocalField n)
    (σ : Space n → ℝ × Space n) (p : ℝ × Space n) : ℝ × Space n :=
  ((σ p.2).1 + p.1,
    localFlow b ((σ p.2).1 + p.1) (σ p.2).1 (σ p.2).2)

/-- Its domain is pulled back from the actual maximal local flow domain. -/
def transverseFlowDomain {n : ℕ} (b : LocalField n)
    (σ : Space n → ℝ × Space n) : Set (ℝ × Space n) :=
  {p | ((σ p.2).1 + p.1, (σ p.2).1, (σ p.2).2) ∈ localFlowDomain b}

/-- Product flow coordinates constructed from the given hypersurface, with
both coordinate directions C¹ and every characteristic inside its actual
local domain. This is a conclusion, never an input certificate. -/
structure TransverseCoordinates {n : ℕ} (b : LocalField n)
    (S : HypersurfaceChart b) (y₀ : Space n) where
  radius : ℝ
  radius_pos : 0 < radius
  parameters : Set (Space n)
  open_parameters : IsOpen parameters
  base_parameter : y₀ ∈ parameters
  parameters_subset : parameters ⊆ S.parameterDomain
  coord : OpenPartialHomeomorph (ℝ × Space n) (ℝ × Space n)
  source_eq : coord.source = Ioo (-radius) radius ×ˢ parameters
  formula : (coord : (ℝ × Space n) → ℝ × Space n) =
    transverseFlowMap b S.parametrization
  actual_domain : coord.source ⊆ transverseFlowDomain b S.parametrization
  target_domain : coord.target ⊆ b.domain
  base_point : S.parametrization y₀ ∈ coord.target
  regular : ContDiffOn ℝ 1 coord coord.source
  inverse_regular : ContDiffOn ℝ 1 coord.symm coord.target
  initial : ∀ y ∈ parameters, coord (0, y) = S.parametrization y
  velocity : ∀ p ∈ coord.source,
    fderiv ℝ coord p (1, 0) = (1, b.velocity (coord p))

/-- Local invertibility of the elapsed-time map must follow from the field,
chart regularity, and tangent independence alone. -/
def transverseCoordinatesStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ (b : LocalField n) (S : HypersurfaceChart b)
    (y₀ : Space n), y₀ ∈ S.parameterDomain →
    IsTransverseAt b S.parametrization y₀ →
    Nonempty (TransverseCoordinates b S y₀)

/-- Existence and uniqueness on a flow-coordinate neighborhood, together with
uniqueness of the germ against solutions on arbitrary open neighborhoods. -/
def TransverseTransportProperties {n : ℕ} (b : LocalField n)
    (S : HypersurfaceChart b) (y₀ : Space n) : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (g : Space n → 𝕜),
    ContDiffOn ℝ 1 g S.parameterDomain →
    ∀ q f : ℝ × Space n → 𝕜, SpatialC1 b.domain q → SpatialC1 b.domain f →
    ∃ C : TransverseCoordinates b S y₀, ∃ u : ℝ × Space n → 𝕜,
      IsTransportSolutionOn C.coord.target b.velocity q f u ∧
      (∀ y ∈ C.parameters, u (S.parametrization y) = g y) ∧
      (∀ v : ℝ × Space n → 𝕜,
        IsTransportSolutionOn C.coord.target b.velocity q f v →
        (∀ y ∈ C.parameters, v (S.parametrization y) = g y) →
        EqOn v u C.coord.target) ∧
      (∀ (W : Set (ℝ × Space n)) (v : ℝ × Space n → 𝕜), IsOpen W →
        S.parametrization y₀ ∈ W → IsTransportSolutionOn W b.velocity q f v →
        (∀ y ∈ S.parameterDomain, S.parametrization y ∈ W →
          v (S.parametrization y) = g y) →
        ∃ N : Set (ℝ × Space n), IsOpen N ∧ S.parametrization y₀ ∈ N ∧
          N ⊆ C.coord.target ∩ W ∧ EqOn v u N)

def transverseTransportStatement : Prop :=
  ∀ n, 1 ≤ n → ∀ (b : LocalField n) (S : HypersurfaceChart b)
    (y₀ : Space n), y₀ ∈ S.parameterDomain →
    IsTransverseAt b S.parametrization y₀ → TransverseTransportProperties b S y₀

/-- Full proposition: global Jacobian, transported density and weak initial
value continuity equation, plus the independently local transverse Cauchy
problem. The global hypotheses are confined to the first conjunct. -/
def continuityAndTransverseDataStatement : Prop :=
  continuityEquationStatement ∧ transverseCoordinatesStatement ∧ transverseTransportStatement

end P201Specs.Hyperbolic
