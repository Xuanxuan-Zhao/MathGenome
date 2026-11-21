import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.PolygonVertex
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PrimitivePeriodCriterion
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Convex.Segment
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Independent interface for paper.tex:2509–2524 (D12.12.06).

The boundary geometry is expressed locally, using the upstream literal wedges.
For a polygon these are its prescribed interior angles at the vertices, and
angle one at every interior point of a side. All finite prevertices are listed;
`side` covers the remaining finite boundary points. The image of infinity is
specified by the actual compactified homeomorphism, and has angle `β`.
Thus `β = 1` is the all-finite-prevertices case, while arbitrary `0 < β < 2`
also includes a vertex at infinity. No analytic continuation, angle-sum
identity, or Schwarz–Christoffel certificate is an input.

This local-geometric version is more general than the polygon statement:
no global polygon combinatorics is needed by the conclusion. The finite
vertices are `F (a j)`; in the infinity-vertex case the last vertex is the
value of the extension at infinity. Only the finite vertices enter the product.
-/
noncomputable section
open Set Complex Filter Metric
open scoped Topology BigOperators

namespace D12Complex.SchwarzChristoffel
open PolygonVertex

/-- The selected logarithm has argument in (0,π) on H. -/
def integrand {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∏ j, upperPower ((α j : ℂ) - 1) (a j) z

def poleSum {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑ j, ((α j : ℂ) - 1) / (z - (a j : ℂ))

def correctedLogDeriv {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ)
    (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (deriv F) z / deriv F z - poleSum a α z

/-- An explicit bounded simple polygonal domain, with cyclic vertices and
interior angles. The local wedge and side fields describe the target's
geometry only. They impose no boundary differentiability on the given map.
The edge condition excludes crossings and vertices on other open edges. -/
structure PolygonGeometry {n : ℕ} (P : Set ℂ) (v : Fin n → ℂ)
    (α : Fin n → ℝ) where
  domain : IsDomain P
  bounded : Bornology.IsBounded P
  three_le : 3 ≤ n
  vertices_injective : Function.Injective v
  vertices_frontier : ∀ j, v j ∈ frontier P
  frontier_edges : frontier P = ⋃ j, segment ℝ (v j) (v (finRotate n j))
  simple_edges : ∀ i j, i ≠ j →
    Disjoint (openSegment ℝ (v i) (v (finRotate n i)))
      (segment ℝ (v j) (v (finRotate n j)))
  angle_pos : ∀ j, 0 < α j
  angle_lt_two : ∀ j, α j < 2
  vertex : ∀ j, Corner P (v j) (α j)
  side : ∀ w ∈ frontier P, w ∉ range v → Corner P w 1

/-- Geometric boundary data of the given map. The angle at infinity is
independent of the list of finite angles. `side` asserts literal local
half-plane geometry of the target, not a regularity condition on F. -/
structure BoundaryData {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ)
    (β : ℝ) (P : Set ℂ) (F G : ℂ → ℂ) where
  domain : IsDomain P
  bounded : Bornology.IsBounded P
  biholomorphic : BiholomorphicPair halfPlane P F G
  extension : compactifiedClosedHalfPlane ≃ₜ closure P
  agrees : ∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
    (extension ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z
  ordered : StrictMono a
  angle_pos : ∀ j, 0 < α j
  angle_lt_two : ∀ j, α j < 2
  vertex : ∀ j, Corner P (F (a j)) (α j)
  side : ∀ x : ℝ, x ∉ range a → Corner P (F x) 1
  infinity_angle_pos : 0 < β
  infinity_angle_lt_two : β < 2
  infinity_corner : Corner P
    (extension ⟨sphereInfty, Or.inl rfl⟩ : ℂ) β

/-- A normalized primitive and its actual contour formula, for every
basepoint and every canonical piecewise C1 path in H. The additive constant
is exactly F(z*). Path independence is stated separately. -/
def PrimitiveFormula {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ)
    (F : ℂ → ℂ) (C : ℂ) : Prop :=
  Specs.D12Complex.Ch03.PrimitivePeriodCriterion.EndpointIndependent_value
    halfPlane (integrand a α) ∧
  ∀ z₀ ∈ halfPlane, ∃ B : ℂ → ℂ,
    Specs.D12Complex.Ch03.PrimitivePeriodCriterion.IsPrimitive_value
      halfPlane (integrand a α) B ∧ B z₀ = 0 ∧
    (∀ z ∈ halfPlane, F z = F z₀ + C * B z) ∧
    ∀ γ : PiecewiseC1Path, γ.trace ⊆ halfPlane → γ.path.source = z₀ →
      F γ.path.target = F z₀ + C * γ.integral (integrand a α)

def Formula {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ C : ℂ, C ≠ 0 ∧
    (∀ z ∈ halfPlane, deriv F z = C * integrand a α z) ∧
    PrimitiveFormula a α F C

end D12Complex.SchwarzChristoffel

namespace Specs.D12Complex.Ch12.SchwarzChristoffel
open _root_.D12Complex _root_.D12Complex.PolygonVertex
open _root_.D12Complex.SchwarzChristoffel

def integrand_type := {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ) → ℂ → ℂ
def integrand_value : integrand_type := fun a α z =>
  ∏ j, upperPower ((α j : ℂ) - 1) (a j) z

def poleSum_type := {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ) → ℂ → ℂ
def poleSum_value : poleSum_type := fun a α z =>
  ∑ j, ((α j : ℂ) - 1) / (z - (a j : ℂ))

def correctedLogDeriv_type :=
  {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ) → (ℂ → ℂ) → ℂ → ℂ
def correctedLogDeriv_value : correctedLogDeriv_type := fun a α F z =>
  deriv (deriv F) z / deriv F z - poleSum a α z

/-- Full obligation, including both locations of infinity and the retained
finite-vertex local factorization. This is a Prop definition, not an axiom. -/
def schwarz_christoffel_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ) (β : ℝ)
    (P : Set ℂ) (F G : ℂ → ℂ), BoundaryData a α β P F G →
      Formula a α F ∧ ∀ j,
        HasCornerFactor F (a j) (F (a j)) (α j : ℂ) ∧
        HasLogDerivExtension F (a j) (α j : ℂ)

/-- The original all-finite-prevertices statement, with an actual polygon
and its given boundary homeomorphism. Its applicability does not require
any analytic continuation or an assumed angle-sum identity. -/
def finite_prevertices_type : Prop :=
  ∀ (n : ℕ) (P : Set ℂ) (v : Fin n → ℂ) (α : Fin n → ℝ)
    (F G : ℂ → ℂ) (a : Fin n → ℝ), PolygonGeometry P v α →
    BiholomorphicPair halfPlane P F G →
    ∀ e : compactifiedClosedHalfPlane ≃ₜ closure P,
      (∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
        (e ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z) →
      StrictMono a → (∀ j, F (a j) = v j) →
      (e ⟨sphereInfty, Or.inl rfl⟩ : ℂ) ∉ range v →
      Formula a α F ∧ ∀ j,
        HasCornerFactor F (a j) (v j) (α j : ℂ) ∧
        HasLogDerivExtension F (a j) (α j : ℂ)

/-- There are n finite prevertices and n+1 polygon vertices; the last
vertex is the image of infinity. The product has exactly n factors. -/
def infinity_vertex_type : Prop :=
  ∀ (n : ℕ) (P : Set ℂ) (v : Fin (n+1) → ℂ) (α : Fin (n+1) → ℝ)
    (F G : ℂ → ℂ) (a : Fin n → ℝ), PolygonGeometry P v α →
    BiholomorphicPair halfPlane P F G →
    ∀ e : compactifiedClosedHalfPlane ≃ₜ closure P,
      (∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
        (e ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z) →
      StrictMono a → (∀ j, F (a j) = v j.castSucc) →
      (e ⟨sphereInfty, Or.inl rfl⟩ : ℂ) = v (Fin.last n) →
      Formula a (fun j => α j.castSucc) F ∧ ∀ j,
        HasCornerFactor F (a j) (v j.castSucc) (α j.castSucc : ℂ) ∧
        HasLogDerivExtension F (a j) (α j.castSucc : ℂ)

def integrand_ne_zero_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ) (z : ℂ),
    integrand a α z ≠ 0

def hasDerivAt_integrand_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ),
    ∀ z ∈ halfPlane,
      HasDerivAt (integrand a α) (integrand a α z * poleSum a α z) z

def holomorphic_integrand_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ),
    HolomorphicOn halfPlane (integrand a α)

def formula_of_logDeriv_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ) (F : ℂ → ℂ),
    HolomorphicOn halfPlane F → (∀ z ∈ halfPlane, deriv F z ≠ 0) →
    (∀ z ∈ halfPlane, deriv (deriv F) z / deriv F z = poleSum a α z) →
      Formula a α F

def primitive_formula_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ) (F : ℂ → ℂ) (C : ℂ),
    C ≠ 0 → HolomorphicOn halfPlane F →
    (∀ z ∈ halfPlane, deriv F z = C * integrand a α z) →
      PrimitiveFormula a α F C

def finite_vertex_factors_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ) (β : ℝ)
    (P : Set ℂ) (F G : ℂ → ℂ), BoundaryData a α β P F G → ∀ j,
      HasCornerFactor F (a j) (F (a j)) (α j : ℂ) ∧
      HasLogDerivExtension F (a j) (α j : ℂ)

/-- Finite-plane continuation of the corrected logarithmic derivative. -/
def entire_correction_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ) (β : ℝ)
    (P : Set ℂ) (F G : ℂ → ℂ), BoundaryData a α β P F G →
      ∃ h : ℂ → ℂ, HolomorphicOn univ h ∧
        EqOn h (correctedLogDeriv a α F) halfPlane ∧
        ∀ z : ℂ, h (star z) = star (h z)

def correction_decay_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ) (β : ℝ)
    (P : Set ℂ) (F G : ℂ → ℂ), BoundaryData a α β P F G →
      ∀ h : ℂ → ℂ, HolomorphicOn univ h →
        EqOn h (correctedLogDeriv a α F) halfPlane →
        (∀ z : ℂ, h (star z) = star (h z)) →
        Tendsto h (cocompact ℂ) (𝓝 0)

def formula_of_entire_correction_type : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (α : Fin n → ℝ) (F : ℂ → ℂ),
    HolomorphicOn halfPlane F → (∀ z ∈ halfPlane, deriv F z ≠ 0) →
    ∀ h : ℂ → ℂ, HolomorphicOn univ h →
      EqOn h (correctedLogDeriv a α F) halfPlane →
      Tendsto h (cocompact ℂ) (𝓝 0) → Formula a α F

def finite_boundary_data_type : Prop :=
  ∀ (n : ℕ) (P : Set ℂ) (v : Fin n → ℂ) (α : Fin n → ℝ)
    (F G : ℂ → ℂ) (a : Fin n → ℝ), PolygonGeometry P v α →
    BiholomorphicPair halfPlane P F G →
    ∀ e : compactifiedClosedHalfPlane ≃ₜ closure P,
      (∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
        (e ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z) →
      StrictMono a → (∀ j, F (a j) = v j) →
      (e ⟨sphereInfty, Or.inl rfl⟩ : ℂ) ∉ range v →
      Nonempty (BoundaryData a α 1 P F G)

def infinity_boundary_data_type : Prop :=
  ∀ (n : ℕ) (P : Set ℂ) (v : Fin (n+1) → ℂ) (α : Fin (n+1) → ℝ)
    (F G : ℂ → ℂ) (a : Fin n → ℝ), PolygonGeometry P v α →
    BiholomorphicPair halfPlane P F G →
    ∀ e : compactifiedClosedHalfPlane ≃ₜ closure P,
      (∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
        (e ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z) →
      StrictMono a → (∀ j, F (a j) = v j.castSucc) →
      (e ⟨sphereInfty, Or.inl rfl⟩ : ℂ) = v (Fin.last n) →
      Nonempty (BoundaryData a (fun j => α j.castSucc) (α (Fin.last n)) P F G)

/-- Assembly helper; the continuation claims are proved independently and
are never assumptions of either original polygon statement. -/
def assemble_type : Prop :=
  entire_correction_type → correction_decay_type → schwarz_christoffel_type

def specialize_type : Prop :=
  schwarz_christoffel_type → finite_prevertices_type ∧ infinity_vertex_type

end Specs.D12Complex.Ch12.SchwarzChristoffel
