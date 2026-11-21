import MathGenome.Internal.Specs.D05.M02.VectorSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Independent statements for K05.12.inner_product, paper.tex:1873–1884.
`RCLike` treats the real and complex fields uniformly. The axioms below are on
an arbitrary module, with no norm, topology, dimension, or completeness premise.
The core bridge swaps the arguments and retains the given module operations.
-/

noncomputable section

namespace D05

/-- The manuscript's shared first-slot-linear convention. -/
def firstInner {F V : Type*} [Inner F V] (u v : V) : F := inner F v u

/-- Exactly the displayed inner-product axioms, with real diagonal values explicit. -/
def IsFirstInnerProduct {F V : Type*} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F) : Prop :=
  (∀ (a b : F) (u v w : V), h (a • u + b • v) w = a * h u w + b * h v w) ∧
  (∀ u v : V, h v u = starRingEnd F (h u v)) ∧
  (∀ v : V, RCLike.im (h v v) = 0) ∧
  (∀ v : V, v ≠ 0 → 0 < RCLike.re (h v v))

/-- The coordinate formula on a finite set of coordinates, including the empty set. -/
def coordinateInner {F ι : Type*} [RCLike F] [Fintype ι] (x y : ι → F) : F :=
  ∑ j, x j * starRingEnd F (y j)

end D05

namespace Specs.D05.M12.InnerProduct

universe u v w

def firstInner_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [Inner F V] → V → V → F

def firstInner_value : firstInner_type.{u, v} := fun u v => inner _ v u

def IsFirstInnerProduct_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [AddCommGroup V] → [Module F V] →
    (V → V → F) → Prop

def IsFirstInnerProduct_value : IsFirstInnerProduct_type.{u, v} := fun {F} {V} _ _ _ h =>
  (∀ (a b : F) (u v w : V), h (a • u + b • v) w = a * h u w + b * h v w) ∧
  (∀ u v : V, h v u = starRingEnd F (h u v)) ∧
  (∀ v : V, RCLike.im (h v v) = 0) ∧
  (∀ v : V, v ≠ 0 → 0 < RCLike.re (h v v))

def coordinateInner_type : Type (max (u + 1) (w + 1)) :=
  {F : Type u} → {ι : Type w} → [RCLike F] → [Fintype ι] → (ι → F) → (ι → F) → F

def coordinateInner_value : coordinateInner_type.{u, w} :=
  fun {F} _ _ _ x y => ∑ j, x j * starRingEnd F (y j)

/-- The four paper axioms hold for the canonical convention. -/
def firstInner_axioms : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V], _root_.D05.IsFirstInnerProduct (_root_.D05.firstInner (F := F) (V := V))

def firstInner_linear : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (a b : F) (u v w : V),
    _root_.D05.firstInner (a • u + b • v) w =
      a * _root_.D05.firstInner u w + b * _root_.D05.firstInner v w

def firstInner_conjugate : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (u v : V),
    _root_.D05.firstInner (F := F) v u = starRingEnd F (_root_.D05.firstInner u v)

def firstInner_diagonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (v : V),
    RCLike.im (_root_.D05.firstInner (F := F) v v) = 0 ∧
      (0 < RCLike.re (_root_.D05.firstInner (F := F) v v) ↔ v ≠ 0)

/-- These consequences are derived from the displayed axioms alone. -/
def second_slot_of_axioms : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h →
    ∀ (a b : F) (u v w : V),
      h u (a • v + b • w) = starRingEnd F a * h u v + starRingEnd F b * h u w

def zero_of_axioms : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h →
    ∀ v : V, h 0 v = 0 ∧ h v 0 = 0

def firstInner_second_slot : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (a b : F) (u v w : V),
    _root_.D05.firstInner u (a • v + b • w) =
      starRingEnd F a * _root_.D05.firstInner u v +
      starRingEnd F b * _root_.D05.firstInner u w

def firstInner_zero : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (v : V),
    _root_.D05.firstInner (F := F) 0 v = 0 ∧ _root_.D05.firstInner (F := F) v 0 = 0

/-- Equivalence with Mathlib's algebraic definition, on the very same module. -/
def axioms_iff_core : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F),
    _root_.D05.IsFirstInnerProduct h ↔
      ∃ c : InnerProductSpace.Core F V, ∀ u v, c.inner u v = h v u

/-- Over ℝ, the axioms give a positive definite symmetric bilinear form. -/
def real_symmetric_bilinear : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module ℝ V] (h : V → V → ℝ),
    _root_.D05.IsFirstInnerProduct h →
    (∀ u v, h u v = h v u) ∧
    (∀ (a b : ℝ) (u v w : V), h (a • u + b • v) w = a * h u w + b * h v w) ∧
    (∀ (a b : ℝ) (u v w : V), h u (a • v + b • w) = a * h u v + b * h u w) ∧
    (∀ v : V, v ≠ 0 → 0 < h v v)

/-- The raw coordinate expression agrees with the canonical Euclidean inner product. -/
def coordinateInner_eq_firstInner : Prop :=
  ∀ {F : Type u} {ι : Type w} [RCLike F] [Fintype ι] (x y : ι → F),
    _root_.D05.coordinateInner x y =
      _root_.D05.firstInner (F := F) (WithLp.toLp 2 x) (WithLp.toLp 2 y)

def coordinateInner_axioms : Prop :=
  ∀ {F : Type u} {ι : Type w} [RCLike F] [Fintype ι],
    _root_.D05.IsFirstInnerProduct (_root_.D05.coordinateInner (F := F) (ι := ι))

/-- The diagonal is the real sum of squared absolute values, with its exact zero case. -/
def coordinateInner_diagonal : Prop :=
  ∀ {F : Type u} {ι : Type w} [RCLike F] [Fintype ι] (x : ι → F),
    _root_.D05.coordinateInner x x = ((∑ j, ‖x j‖ ^ 2 : ℝ) : F) ∧
    (0 < (∑ j, ‖x j‖ ^ 2 : ℝ) ↔ x ≠ 0) ∧
    (_root_.D05.coordinateInner x x = 0 ↔ ∀ j, x j = 0)

/-- On any zero vector space the zero form obeys the definition vacuously. -/
def zero_space : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V] [Subsingleton V],
    _root_.D05.IsFirstInnerProduct (fun (_ _ : V) => (0 : F))

end Specs.D05.M12.InnerProduct
