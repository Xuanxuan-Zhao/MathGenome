import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.ChosenPowers
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Sphere
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.Reflection
import Mathlib.Topology.Homeomorph.Defs

/-! Local corner assertions of paper.tex:2509–2520. `Corner` is a geometric
interior-angle condition, stated by equality with an actual wedge. It contains
no holomorphic straightening or assumed regularity of the conformal map.
The analytic assertions below apply to any domain with this local geometry,
and in particular to each vertex and each open side of a simple polygon.
The source power is always the principal branch restricted to Im z > 0.
-/
noncomputable section
open Set Metric Complex
open scoped Topology

namespace D12Complex.PolygonVertex

def halfPlane : Set ℂ := {z | 0 < z.im}
def closedHalfPlane : Set ℂ := {z | 0 ≤ z.im}
def compactifiedClosedHalfPlane : Set RiemannSphere :=
  {sphereInfty} ∪ sphereFinite '' closedHalfPlane

/-- The total representative retains the values of the given boundary
extension at finite real points. No behavior of F below the real axis is imposed. -/
def HasBoundaryExtension (P : Set ℂ) (F : ℂ → ℂ) : Prop :=
  ∃ e : compactifiedClosedHalfPlane ≃ₜ closure P,
    ∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
      (e ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z

/-- A wedge has the literal opening πα, including reentrant angles. The
rotation c has modulus one; the edges and the vertex are excluded. -/
def wedge (v c : ℂ) (α : ℝ) : Set ℂ :=
  {w | ∃ (ρ θ : ℝ), 0 < ρ ∧ 0 < θ ∧ θ < Real.pi * α ∧
    w = v + c * ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))}

/-- The meaning of a polygon's interior angle πα at v. At an interior point
of a side the same condition holds with α = 1. -/
def Corner (P : Set ℂ) (v : ℂ) (α : ℝ) : Prop :=
  ∃ (c : ℂ) (R : ℝ), ‖c‖ = 1 ∧ 0 < R ∧
    P ∩ ball v R = wedge v c α ∩ ball v R

def upperPower (α : ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  principalPower α (z - (a : ℂ))

/-- The factor is holomorphic and nonvanishing on a full disk, although the
power-factor identity is asserted only on its intersection with H. -/
def HasCornerFactor (F : ℂ → ℂ) (a : ℝ) (v : ℂ) (α : ℂ) : Prop :=
  ∃ (r : ℝ) (u : ℂ → ℂ), 0 < r ∧ HolomorphicOn (ball (a : ℂ) r) u ∧
    (∀ z ∈ ball (a : ℂ) r, u z ≠ 0) ∧
    ∀ z ∈ ball (a : ℂ) r ∩ halfPlane,
      F z - v = upperPower α a z * u z

/-- The extension agrees with the upper-side logarithmic derivative; no
value is assigned to the singular rational expression at the prevertex. -/
def HasLogDerivExtension (F : ℂ → ℂ) (a : ℝ) (α : ℂ) : Prop :=
  ∃ (r : ℝ) (h : ℂ → ℂ), 0 < r ∧ HolomorphicOn (ball (a : ℂ) r) h ∧
    ∀ z ∈ ball (a : ℂ) r ∩ halfPlane,
      deriv (deriv F) z / deriv F z - (α - 1) / (z - (a : ℂ)) = h z

end D12Complex.PolygonVertex

namespace Specs.D12Complex.Ch12.PolygonVertex
open _root_.D12Complex _root_.D12Complex.PolygonVertex

-- Expected values of the canonical geometric and branch definitions.
def halfPlane_type := Set ℂ
def halfPlane_value : halfPlane_type := {z | 0 < z.im}
def closedHalfPlane_type := Set ℂ
def closedHalfPlane_value : closedHalfPlane_type := {z | 0 ≤ z.im}
def compactifiedClosedHalfPlane_type := Set RiemannSphere
def compactifiedClosedHalfPlane_value : compactifiedClosedHalfPlane_type :=
  show Set RiemannSphere from {sphereInfty} ∪ sphereFinite '' closedHalfPlane

def HasBoundaryExtension_type := Set ℂ → (ℂ → ℂ) → Prop
def HasBoundaryExtension_value : HasBoundaryExtension_type := fun P F =>
  ∃ e : compactifiedClosedHalfPlane ≃ₜ closure P,
    ∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
      (e ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z

def wedge_type := ℂ → ℂ → ℝ → Set ℂ
def wedge_value : wedge_type := fun v c α =>
  {w | ∃ (ρ θ : ℝ), 0 < ρ ∧ 0 < θ ∧ θ < Real.pi * α ∧
    w = v + c * ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))}

def Corner_type := Set ℂ → ℂ → ℝ → Prop
def Corner_value : Corner_type := fun P v α =>
  ∃ (c : ℂ) (R : ℝ), ‖c‖ = 1 ∧ 0 < R ∧
    P ∩ ball v R = wedge v c α ∩ ball v R

def upperPower_type := ℂ → ℝ → ℂ → ℂ
def upperPower_value : upperPower_type := fun α a z =>
  principalPower α (z - (a : ℂ))

def HasCornerFactor_type := (ℂ → ℂ) → ℝ → ℂ → ℂ → Prop
def HasCornerFactor_value : HasCornerFactor_type := fun F a v α =>
  ∃ (r : ℝ) (u : ℂ → ℂ), 0 < r ∧ HolomorphicOn (ball (a : ℂ) r) u ∧
    (∀ z ∈ ball (a : ℂ) r, u z ≠ 0) ∧
    ∀ z ∈ ball (a : ℂ) r ∩ halfPlane,
      F z - v = upperPower α a z * u z

def HasLogDerivExtension_type := (ℂ → ℂ) → ℝ → ℂ → Prop
def HasLogDerivExtension_value : HasLogDerivExtension_type := fun F a α =>
  ∃ (r : ℝ) (h : ℂ → ℂ), 0 < r ∧ HolomorphicOn (ball (a : ℂ) r) h ∧
    ∀ z ∈ ball (a : ℂ) r ∩ halfPlane,
      deriv (deriv F) z / deriv F z - (α - 1) / (z - (a : ℂ)) = h z

/-- Full finite-vertex assertion. No restriction is placed on where infinity
maps, nor on other vertices. The local geometric hypothesis is exactly the
interior-angle property of the specified polygon vertex. -/
def polygon_vertex_type : Prop :=
  ∀ (P : Set ℂ) (F G : ℂ → ℂ), IsDomain P → Bornology.IsBounded P →
    BiholomorphicPair halfPlane P F G → HasBoundaryExtension P F →
    ∀ (a : ℝ) (α : ℝ), 0 < α → α < 2 → Corner P (F a) α →
      HasCornerFactor F a (F a) (α : ℂ) ∧ HasLogDerivExtension F a (α : ℂ)

/-- Every finite real preimage of an open side admits a full holomorphic
extension with nonzero derivative at that point. -/
def polygon_side_type : Prop :=
  ∀ (P : Set ℂ) (F G : ℂ → ℂ), IsDomain P → Bornology.IsBounded P →
    BiholomorphicPair halfPlane P F G → HasBoundaryExtension P F →
    ∀ a : ℝ, Corner P (F a) 1 → ∃ (r : ℝ) (f : ℂ → ℂ),
      0 < r ∧ HolomorphicOn (ball (a : ℂ) r) f ∧ deriv f (a : ℂ) ≠ 0 ∧
      EqOn f F (ball (a : ℂ) r ∩ closedHalfPlane)

/-- Analytic consequence, independent of the geometry producing the factor.
This auxiliary assertion is not a substitute for polygon_vertex_type. -/
def logDeriv_of_cornerFactor_type : Prop :=
  ∀ (F : ℂ → ℂ) (a : ℝ) (v α : ℂ), α ≠ 0 →
    HasCornerFactor F a v α → HasLogDerivExtension F a α

/-- A reflected straightening with a simple zero has an actual holomorphic
unit, not just a pointwise quotient on a punctured neighborhood. -/
def simple_zero_factor_type : Prop :=
  ∀ (q : ℂ → ℂ) (a : ℂ), AnalyticAt ℂ q a → q a = 0 → deriv q a ≠ 0 →
    ∃ (r : ℝ) (b : ℂ → ℂ), 0 < r ∧ HolomorphicOn (ball a r) b ∧
      (∀ z ∈ ball a r, b z ≠ 0) ∧ b a = deriv q a ∧
      ∀ z ∈ ball a r, q z = (z - a) * b z

/-- The line-reflection step used after the wedge has been straightened.
All the input conditions concern the given open side and diameter. -/
def straightening_reflection_type : Prop :=
  ∀ (a : ℝ) (r : ℝ) (q : ℂ → ℂ), 0 < r →
    HolomorphicOn (Reflection.upper (a : ℂ) r) q →
    ContinuousOn q (Reflection.upperClosure (a : ℂ) r) →
    (∀ z ∈ Reflection.diameter (a : ℂ) r, (q z).im = 0) →
    InjOn q (Reflection.upperClosure (a : ℂ) r) →
    (∀ z ∈ Reflection.upper (a : ℂ) r, deriv q z ≠ 0) →
    (∀ z ∈ Reflection.upper (a : ℂ) r, 0 < (q z).im) → q a = 0 →
    ∃ (s : ℝ) (b : ℂ → ℂ), 0 < s ∧ s ≤ r ∧
      HolomorphicOn (ball (a : ℂ) s) b ∧
      (∀ z ∈ ball (a : ℂ) s, b z ≠ 0) ∧
      ∀ z ∈ Reflection.upperClosure (a : ℂ) s, q z = (z - (a : ℂ)) * b z

/-- Reconstruction of the unit after reflection. All powers use one chosen
logarithm. The analytic simple zero and upper-side image are hypotheses of
this helper only, and are to be established geometrically in polygon_vertex. -/
def power_simple_zero_factor_type : Prop :=
  ∀ (q : ℂ → ℂ) (a : ℝ) (R : ℝ) (α : ℂ), 0 < R →
    HolomorphicOn (ball (a : ℂ) R) q → q a = 0 → deriv q (a : ℂ) ≠ 0 →
    (∀ z ∈ ball (a : ℂ) R ∩ halfPlane, 0 < (q z).im) →
    ∃ (r : ℝ) (u : ℂ → ℂ), 0 < r ∧ r ≤ R ∧
      HolomorphicOn (ball (a : ℂ) r) u ∧
      (∀ z ∈ ball (a : ℂ) r, u z ≠ 0) ∧
      ∀ z ∈ ball (a : ℂ) r ∩ halfPlane,
        principalPower α (q z) = upperPower α a z * u z

/-- Assembly after a geometric wedge-straightening map has been constructed.
The map q is only given on the upper side and diameter, not assumed analytic
through the prevertex. Reflection and the simple zero are conclusions. -/
def corner_factor_of_straightening_type : Prop :=
  ∀ (F q : ℂ → ℂ) (a : ℝ) (v c α : ℂ) (r : ℝ), 0 < r → c ≠ 0 →
    HolomorphicOn (Reflection.upper (a : ℂ) r) q →
    ContinuousOn q (Reflection.upperClosure (a : ℂ) r) →
    (∀ z ∈ Reflection.diameter (a : ℂ) r, (q z).im = 0) →
    InjOn q (Reflection.upperClosure (a : ℂ) r) →
    (∀ z ∈ Reflection.upper (a : ℂ) r, deriv q z ≠ 0) →
    (∀ z ∈ Reflection.upper (a : ℂ) r, 0 < (q z).im) → q a = 0 →
    (∀ z ∈ Reflection.upper (a : ℂ) r,
      F z - v = c * principalPower α (q z)) → HasCornerFactor F a v α

def boundary_extension_data_type : Prop :=
  ∀ (P : Set ℂ) (F : ℂ → ℂ), HasBoundaryExtension P F →
    ContinuousOn F closedHalfPlane ∧ InjOn F closedHalfPlane ∧
      MapsTo F closedHalfPlane (closure P)

def boundary_real_frontier_type : Prop :=
  ∀ (P : Set ℂ) (F G : ℂ → ℂ), BiholomorphicPair halfPlane P F G →
    HasBoundaryExtension P F → ∀ z : ℂ, z.im = 0 → F z ∈ frontier P

def polygon_vertex_angle_one_type : Prop :=
  ∀ (P : Set ℂ) (F G : ℂ → ℂ), IsDomain P → Bornology.IsBounded P →
    BiholomorphicPair halfPlane P F G → HasBoundaryExtension P F →
    ∀ a : ℝ, Corner P (F a) 1 →
      HasCornerFactor F a (F a) 1 ∧ HasLogDerivExtension F a 1

end Specs.D12Complex.Ch12.PolygonVertex
