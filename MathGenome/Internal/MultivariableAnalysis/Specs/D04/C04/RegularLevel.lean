import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.EmbeddedManifoldCharts
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.ImplicitFunction
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Independent objects and full propositions for d04:04:regular-level.
Coordinate changes below only reorder coordinates: arbitrary linear changes
are not substituted for the coordinate-permutation assertion. -/
noncomputable section
open Set Topology
open scoped ContDiff
namespace Specs.D04.C04.RegularLevel
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
namespace Model

def level {n q : ℕ} (U : Set (E n)) (g : E n → E q) (c : E q) : Set (E n) :=
  {x | x ∈ U ∧ g x = c}

/-- An ordering of the free and solved coordinates, with no rotation or shear. -/
def coordinateEquiv {p q n : ℕ} (s : Fin p ⊕ Fin q ≃ Fin n) :
    (E p × E q) ≃L[ℝ] E n :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => WithLp.toLp 2 (fun j => Sum.elim (fun i => z.1 i) (fun i => z.2 i) (s.symm j))
      invFun := fun x => (WithLp.toLp 2 (fun i => x (s (.inl i))),
        WithLp.toLp 2 (fun i => x (s (.inr i))))
      left_inv := by intro z; ext i <;> simp
      right_inv := by
        intro x
        ext j
        change Sum.elim _ _ (s.symm j) = x j
        have hj : j = s (s.symm j) := (s.apply_symm_apply j).symm
        rw [hj]
        simp only [Equiv.symm_apply_apply]
        cases s.symm j <;> rfl
      map_add' := by
        intro z w
        ext j
        change Sum.elim (fun i => z.1 i + w.1 i) (fun i => z.2 i + w.2 i) (s.symm j) =
          Sum.elim (fun i => z.1 i) (fun i => z.2 i) (s.symm j) +
          Sum.elim (fun i => w.1 i) (fun i => w.2 i) (s.symm j)
        cases s.symm j <;> rfl
      map_smul' := by
        intro t z
        ext j
        change Sum.elim (fun i => t * z.1 i) (fun i => t * z.2 i) (s.symm j) =
          t * Sum.elim (fun i => z.1 i) (fun i => z.2 i) (s.symm j)
        cases s.symm j <;> rfl }

/-- The velocities are those of C¹ curves on an open TWO-SIDED interval.
Ambient representatives off that interval have no prescribed values. -/
def CurveVelocity {n : ℕ} (M : Set (E n)) (x v : E n) : Prop :=
  ∃ (ε : ℝ) (γ : ℝ → E n), 0 < ε ∧ γ 0 = x ∧
    MapsTo γ (Ioo (-ε) ε) M ∧ ContDiffOn ℝ 1 γ (Ioo (-ε) ε) ∧
    HasDerivAt γ v 0

/-- Product neighborhoods and an actual C^r solution graph. The invertible
solved block is required throughout the graph, as supplied by the IFT. -/
structure LevelGraph (r : ℕ∞ω) {n q : ℕ}
    (U : Set (E n)) (g : E n → E q) (c : E q) where
  coordinates : Fin (n-q) ⊕ Fin q ≃ Fin n
  A : Set (E (n-q))
  B : Set (E q)
  open_A : IsOpen A
  open_B : IsOpen B
  φ : E (n-q) → E q
  regular_φ : ContDiffOn ℝ r φ A
  map_φ : MapsTo φ A B
  product_subset : coordinateEquiv coordinates '' (A ×ˢ B) ⊆ U
  equation : ∀ u ∈ A, ∀ y ∈ B,
    g (coordinateEquiv coordinates (u,y)) = c ↔ y = φ u
  solved_invertible : ∀ u ∈ A,
    ((fderiv ℝ (g ∘ coordinateEquiv coordinates) (u,φ u)).comp
      (ContinuousLinearMap.inr ℝ (E (n-q)) (E q))).IsInvertible

namespace LevelGraph
variable {r : ℕ∞ω} {n q : ℕ} {U : Set (E n)} {g : E n → E q} {c : E q}
def θ (d : LevelGraph r U g c) (u : E (n-q)) : E n :=
  coordinateEquiv d.coordinates (u,d.φ u)
def projection (d : LevelGraph r U g c) : E n →L[ℝ] E (n-q) :=
  (ContinuousLinearMap.fst ℝ (E (n-q)) (E q)).comp
    (coordinateEquiv d.coordinates).symm.toContinuousLinearMap
def ambient (d : LevelGraph r U g c) : Set (E n) :=
  coordinateEquiv d.coordinates '' (d.A ×ˢ d.B)
def overlap (d e : LevelGraph r U g c) : Set (E (n-q)) :=
  d.A ∩ d.θ ⁻¹' e.ambient

def Geometry (d : LevelGraph r U g c) : Prop :=
  IsOpen d.ambient ∧ d.ambient ⊆ U ∧
  d.θ '' d.A = level U g c ∩ d.ambient ∧
  Function.Injective d.θ ∧ ContDiffOn ℝ r d.θ d.A ∧
  (∃ h : d.A ≃ₜ ↥(level U g c ∩ d.ambient), ∀ u, (h u).val = d.θ u) ∧
  ∀ u ∈ d.A, Function.Injective (fderiv ℝ d.θ u) ∧
    LinearMap.range (fderiv ℝ d.θ u).toLinearMap =
      LinearMap.ker (fderiv ℝ g (d.θ u)).toLinearMap ∧
    ∀ v, CurveVelocity (level U g c) (d.θ u) v ↔ fderiv ℝ g (d.θ u) v = 0
end LevelGraph
end Model
open Model

/-- Pointwise theorem, including the whole relative-neighborhood, differential,
and curve-velocity conclusion. ℕ∞ω is bounded to exclude analytic order ω. -/
def regular_level_localType : Prop :=
  ∀ {n q : ℕ} (r : ℕ∞ω) (U : Set (E n)) (g : E n → E q) (c : E q) (a : E n),
    ManifoldRegularity r → IsOpen U → ContDiffOn ℝ r g U → a ∈ level U g c →
    Function.Surjective (fderiv ℝ g a) → q ≤ n ∧
      ∃ d : LevelGraph r U g c, a ∈ d.ambient ∧ d.Geometry

def graph_geometryType : Prop :=
  ∀ {r : ℕ∞ω} {n q : ℕ} {U : Set (E n)} {g : E n → E q} {c : E q},
    1 ≤ r → IsOpen U → ContDiffOn ℝ r g U →
    ∀ d : LevelGraph r U g c, d.Geometry

/-- Both transition directions and inverse identities on the complete overlap. -/
def graph_transitionsType : Prop :=
  ∀ {r : ℕ∞ω} {n q : ℕ} {U : Set (E n)} {g : E n → E q} {c : E q}
    (d e : LevelGraph r U g c),
    IsOpen (d.overlap e) ∧
    ContDiffOn ℝ r (e.projection ∘ d.θ) (d.overlap e) ∧
    MapsTo (e.projection ∘ d.θ) (d.overlap e) (e.overlap d) ∧
    IsOpen (e.overlap d) ∧
    ContDiffOn ℝ r (d.projection ∘ e.θ) (e.overlap d) ∧
    MapsTo (d.projection ∘ e.θ) (e.overlap d) (d.overlap e) ∧
    (∀ u ∈ d.overlap e, d.projection (e.θ (e.projection (d.θ u))) = u) ∧
    (∀ v ∈ e.overlap d, e.projection (d.θ (d.projection (e.θ v))) = v)

/-- The graph construction supplies witnesses of the canonical predicate.
No manifold theorem or chart-transition theorem is an assumption. -/
def regular_level_manifoldType : Prop :=
  ∀ {n q : ℕ} (r : ℕ∞ω) (U : Set (E n)) (g : E n → E q) (c : E q),
    ManifoldRegularity r → IsOpen U → ContDiffOn ℝ r g U →
    (∀ a ∈ level U g c, Function.Surjective (fderiv ℝ g a)) →
    IsEmbeddedManifold r (n-q) (level U g c) ∧
    ∀ a ∈ level U g c, ∃ (d : LevelGraph r U g c)
      (h : EmbeddedChart r (n-q) n (level U g c)) (u : E (n-q)),
      h.half = false ∧ h.source = d.A ∧ h.ambient = d.ambient ∧
      h.toFun = d.θ ∧ h.invFun = d.projection ∧ CenteredAt h u ∧ h.toFun u = a

/-- Zero constraints impose no condition, even in ambient dimension zero. -/
def zero_constraintsType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (g : E n → E 0) (c : E 0), level U g c = U

/-- Full codimension: each regular point is relatively isolated and has zero kernel. -/
def full_codimensionType : Prop :=
  ∀ {n : ℕ} (r : ℕ∞ω) (U : Set (E n)) (g : E n → E n) (c a : E n),
    ManifoldRegularity r → IsOpen U → ContDiffOn ℝ r g U → a ∈ level U g c →
    Function.Surjective (fderiv ℝ g a) →
    (∃ O, IsOpen O ∧ a ∈ O ∧ level U g c ∩ O = {a}) ∧
      LinearMap.ker (fderiv ℝ g a).toLinearMap = ⊥

def empty_levelType : Prop :=
  ∀ {n q : ℕ} (r : ℕ∞ω) (U : Set (E n)) (g : E n → E q) (c : E q),
    ManifoldRegularity r → level U g c = ∅ →
    IsEmbeddedManifold r (n-q) (level U g c)
end Specs.D04.C04.RegularLevel
