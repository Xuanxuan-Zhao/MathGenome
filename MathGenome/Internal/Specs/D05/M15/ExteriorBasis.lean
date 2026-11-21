import MathGenome.Internal.Specs.D05.M15.Exterior
import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.Foundations.SubsetCount
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Hom.PowersetCard

/-!
Independent statements for K05.15.exterior_basis (paper.tex:2914–2920).
The powers are the accepted homogeneous submodules of the square-relation
quotient, not alternating tensors obtained by averaging. The family below is
literally the product of the basis vectors in increasing order. The basis result
also holds for an arbitrary ordered basis; only the dimension assertions use
finite dimension. There is no characteristic or positive-degree restriction.
-/

noncomputable section
namespace Specs.D05.M15.ExteriorBasis

universe u v w

/-- The wedge on a finite subset, enumerated in its induced increasing order. -/
def increasingWedge {K : Type u} {V : Type v} {I : Type w}
    [Field K] [AddCommGroup V] [Module K V] [LinearOrder I]
    (b : Module.Basis I K V) (p : ℕ) (s : Set.powersetCard I p) :
    Exterior.homogeneousPart_value K V p :=
  exteriorPower.ιMulti K p (fun j => b (s.val.orderEmbOfFin s.prop j))

/-- The specified increasing wedges themselves, not just some family of the
same cardinality, are the vectors of a basis. -/
def increasing_wedges_basis : Prop :=
  ∀ {K : Type u} {V : Type v} {I : Type w}
    [Field K] [AddCommGroup V] [Module K V] [LinearOrder I],
    ∀ (b : Module.Basis I K V) (p : ℕ),
    ∃ B : Module.Basis (Set.powersetCard I p) K (Exterior.homogeneousPart_value K V p),
      ∀ s, B s = increasingWedge b p s

def increasing_wedges_independent : Prop :=
  ∀ {K : Type u} {V : Type v} {I : Type w}
    [Field K] [AddCommGroup V] [Module K V] [LinearOrder I],
    ∀ (b : Module.Basis I K V) (p : ℕ), LinearIndependent K (increasingWedge b p)

def increasing_wedges_span : Prop :=
  ∀ {K : Type u} {V : Type v} {I : Type w}
    [Field K] [AddCommGroup V] [Module K V] [LinearOrder I],
    ∀ (b : Module.Basis I K V) (p : ℕ),
      Submodule.span K (Set.range (increasingWedge b p)) = ⊤

/-- Determinants of the selected coordinate rows descend to the exterior power
and extract the coefficients of its increasing wedges, also in characteristic two. -/
def determinant_coordinates : Prop :=
  ∀ {K : Type u} {V : Type v} {I : Type w}
    [Field K] [AddCommGroup V] [Module K V] [LinearOrder I],
    ∀ (b : Module.Basis I K V) (p : ℕ) (s : Set.powersetCard I p),
    ∃ L : (Exterior.homogeneousPart_value K V p) →ₗ[K] K,
      (∀ x : Fin p → V, L (exteriorPower.ιMulti K p x) =
        Matrix.det (fun a j => b.coord (s.val.orderEmbOfFin s.prop a) (x j))) ∧
      (∀ t : Set.powersetCard I p,
        L (increasingWedge b p t) = if s = t then 1 else 0)

/-- The count is an integer binomial coefficient; no division takes place in K. -/
def dimension_of_finite_basis : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    ∀ (n : ℕ) (b : Module.Basis (Fin n) K V) (p : ℕ),
      Module.finrank K (Exterior.homogeneousPart_value K V p) = n.choose p

def dimension : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], ∀ p : ℕ,
      Module.finrank K (Exterior.homogeneousPart_value K V p) =
        (Module.finrank K V).choose p

/-- The degree-zero basis vector is the scalar unit of the exterior algebra. -/
def degree_zero_unit_basis : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    ∃ B : Module.Basis (Fin 1) K (Exterior.homogeneousPart_value K V 0),
      ((B 0 : Exterior.homogeneousPart_value K V 0) : _root_.ExteriorAlgebra K V) = 1

/-- Above the dimension the actual homogeneous submodule is zero. -/
def above_dimension : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V],
    ∀ (n : ℕ) (b : Module.Basis (Fin n) K V) (p : ℕ), n < p →
      Exterior.homogeneousPart_value K V p = ⊥

end Specs.D05.M15.ExteriorBasis
