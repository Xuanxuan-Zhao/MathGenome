import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Products
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.Linarith

/-! The sphere is defined by its Euclidean sum of squares, rather than the norm
of the shared coordinate space `Fin n → ℝ` (which has the sup norm).
All spaces below have their usual subspace, product, or quotient topology.
The statements include n = 0 and k = 0. No smoothness is assumed as data. -/
namespace SmoothManifolds.SphereTorusData
open ModelData AtlasData MapData Set
open scoped BigOperators

/-- Squared Euclidean length, independent of the sup norm on coordinate tuples. -/
def squareSum {n : ℕ} (x : Euclidean n) : ℝ := ∑ i, (x i) ^ 2

/-- The actual unit sphere in R^(n+1), with its subspace topology. -/
abbrev Sphere (n : ℕ) := {x : Euclidean (n + 1) // squareSum x = 1}

/-- Delete coordinate i, retaining the order of all the other coordinates. -/
def omitCoordinate {n : ℕ} (i : Fin (n + 1)) (x : Euclidean (n + 1)) :
    Euclidean n := fun j => x (i.succAbove j)

/-- The two square-root branches. True denotes the positive hemisphere. -/
noncomputable def signedRoot (positive : Bool) (r : ℝ) : ℝ :=
  if positive then Real.sqrt r else -Real.sqrt r

/-- The manuscript's inverse hemisphere parametrization, including dimension zero. -/
noncomputable def insertRoot {n : ℕ} (i : Fin (n + 1)) (positive : Bool)
    (y : Euclidean n) : Euclidean (n + 1) :=
  i.insertNth (signedRoot positive (1 - squareSum y)) y

def hemisphere {n : ℕ} (i : Fin (n + 1)) (positive : Bool) : Set (Sphere n) :=
  {x | if positive then 0 < x.val i else x.val i < 0}

def unitBall (n : ℕ) : Set (ModelSpace n .euclidean) :=
  {y | squareSum y.val < 1}

/-- This predicate specifies the maps on their entire source and target.
Values outside those sets are irrelevant for an open partial homeomorphism. -/
def IsHemisphereChart {n : ℕ} (i : Fin (n + 1)) (positive : Bool)
    (c : ModelChart n .euclidean (Sphere n)) : Prop :=
  c.source = hemisphere i positive ∧ c.target = unitBall n ∧
    (∀ x ∈ c.source, (c x).val = omitCoordinate i x.val) ∧
    (∀ y ∈ c.target, (c.symm y).val = insertRoot i positive y.val)

def hemisphereAtlas (n : ℕ) : Set (ModelChart n .euclidean (Sphere n)) :=
  {c | ∃ i positive, IsHemisphereChart i positive c}

/-- The k-fold product of the same S^1, with the product topology. -/
abbrev Torus (k : ℕ) := Fin k → Sphere 1

/-- Coordinatewise R/Z is a quotient representation of R^k/Z^k. The theorem
`angleQuotientType` additionally verifies the quotient topology and exact fibers. -/
abbrev FlatTorus (k : ℕ) := Fin k → AddCircle (1 : ℝ)

def quotientProjection (k : ℕ) (x : Euclidean k) : FlatTorus k := fun j => (x j : AddCircle (1 : ℝ))

/-- The integer translation relation defining the literal quotient R^k/Z^k. -/
def integerTranslationSetoid (k : ℕ) : Setoid (Euclidean k) where
  r x y := ∃ z : Fin k → ℤ, ∀ j, x j = y j + (z j : ℝ)
  iseqv := {
    refl := fun x => ⟨0, by simp⟩
    symm := by
      rintro x y ⟨z, hz⟩
      refine ⟨-z, fun j => ?_⟩
      simp only [Pi.neg_apply, Int.cast_neg]
      linarith [hz j]
    trans := by
      rintro x y w ⟨z, hz⟩ ⟨v, hv⟩
      refine ⟨z + v, fun j => ?_⟩
      simp only [Pi.add_apply, Int.cast_add]
      linarith [hz j, hv j] }

abbrev LatticeQuotient (k : ℕ) := Quotient (integerTranslationSetoid k)

def latticeProjection (k : ℕ) (x : Euclidean k) : LatticeQuotient k :=
  Quotient.mk (integerTranslationSetoid k) x

noncomputable def anglePoint (t : ℝ) : Sphere 1 :=
  ⟨![Real.cos (2 * Real.pi * t), Real.sin (2 * Real.pi * t)], by
    simpa [squareSum, Fin.sum_univ_two] using Real.cos_sq_add_sin_sq (2 * Real.pi * t)⟩

noncomputable def angleMap (k : ℕ) (x : Euclidean k) : Torus k := fun j => anglePoint (x j)

/-- The generating finite-product hemisphere charts, in the standard ordering
of the k one-dimensional coordinate blocks. This includes the empty product. -/
def IsProductHemisphereChart (k : ℕ) (i : Fin k → Fin 2) (positive : Fin k → Bool)
    (c : ModelChart k .euclidean (Torus k)) : Prop :=
  c.source = {p | ∀ j, p j ∈ hemisphere (i j) (positive j)} ∧
  c.target = {y | ∀ j, (y.val j) ^ 2 < 1} ∧
  (∀ p ∈ c.source, ∀ j, (c p).val j = (p j).val ((i j).succAbove 0)) ∧
  (∀ y ∈ c.target, ∀ j, (c.symm y j).val =
    insertRoot (i j) (positive j) (fun _ : Fin 1 => y.val j))

def productHemisphereAtlas (k : ℕ) : Set (ModelChart k .euclidean (Torus k)) :=
  {c | ∃ i positive, IsProductHemisphereChart k i positive c}

/-- Boxes of radius less than 1/4 have width less than one period. -/
def angleBox {k : ℕ} (a : Euclidean k) (ε : ℝ) : Set (Euclidean k) :=
  {x | ∀ j, |x j - a j| < ε}

/-- Quotient coordinates on a small box are the actual inverse of the quotient
projection on that box, not an assumed smooth local inverse. -/
def IsAngleChart {k : ℕ} (a : Euclidean k) (ε : ℝ)
    (c : ModelChart k .euclidean (FlatTorus k)) : Prop :=
  c.source = quotientProjection k '' angleBox a ε ∧
  c.target = {y | y.val ∈ angleBox a ε} ∧
  (∀ x ∈ angleBox a ε, (c (quotientProjection k x)).val = x) ∧
  (∀ y ∈ c.target, c.symm y = quotientProjection k y.val)

def angleAtlas (k : ℕ) : Set (ModelChart k .euclidean (FlatTorus k)) :=
  {c | ∃ a ε, 0 < ε ∧ ε < 1 / 4 ∧ IsAngleChart a ε c}

end SmoothManifolds.SphereTorusData

namespace Specs.SmoothManifolds.Examples.SpheresAndTori
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.SphereTorusData Set

/-- Every specified hemisphere exists as a chart; these exact charts form a
smooth atlas and generate the returned maximal smooth structure. -/
def sphereManifoldType : Prop :=
  ∀ n : ℕ,
    (∀ (i : Fin (n + 1)) (positive : Bool), ∃ c, IsHemisphereChart i positive c) ∧
    IsContDiffAtlas (⊤ : ℕ∞) (hemisphereAtlas n) ∧
    ∃ S : SmoothManifold n .euclidean (Sphere n),
      S.topologicalManifold.atlas = hemisphereAtlas n ∧
      S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas n)

/-- The torus uses exactly the finite-product hemisphere atlas, including k=0. -/
def torusManifoldType : Prop :=
  ∀ k : ℕ,
    (∀ (i : Fin k → Fin 2) (positive : Fin k → Bool),
      ∃ c, IsProductHemisphereChart k i positive c) ∧
    IsContDiffAtlas (⊤ : ℕ∞) (productHemisphereAtlas k) ∧
    ∃ T : SmoothManifold k .euclidean (Torus k),
      T.topologicalManifold.atlas = productHemisphereAtlas k ∧
      T.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (productHemisphereAtlas k)

/-- The coordinatewise quotient really has the topology and equivalence relation
of R^k/Z^k, and the homeomorphism is induced by the specified periodic angles. -/
def angleQuotientType : Prop :=
  ∀ k : ℕ, IsOpenQuotientMap (quotientProjection k) ∧
    (∀ x y : Euclidean k, quotientProjection k x = quotientProjection k y ↔
      ∃ z : Fin k → ℤ, ∀ j, x j = y j + (z j : ℝ)) ∧
    ∃ h : FlatTorus k ≃ₜ Torus k, ∀ x, h (quotientProjection k x) = angleMap k x

/-- All sufficiently small boxes give smooth quotient charts on the quotient
topology; they generate the asserted quotient smooth structure. -/
def angleManifoldType : Prop :=
  ∀ k : ℕ,
    (∀ (a : Euclidean k) (ε : ℝ), 0 < ε → ε < 1 / 4 →
      ∃ c, IsAngleChart a ε c) ∧
    IsContDiffAtlas (⊤ : ℕ∞) (angleAtlas k) ∧
    ∃ Q : SmoothManifold k .euclidean (FlatTorus k),
      Q.topologicalManifold.atlas = angleAtlas k ∧
      Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas k)

/-- Agreement means equality of maximal atlases after transport, as well as
smoothness of the angle-induced homeomorphism and its inverse. The hypotheses
only identify the two already specified generating constructions. -/
def angleProductCompatibilityType : Prop :=
  ∀ (k : ℕ) (T : SmoothManifold k .euclidean (Torus k))
    (Q : SmoothManifold k .euclidean (FlatTorus k)),
    T.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (productHemisphereAtlas k) →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas k) →
    ∃ h : FlatTorus k ≃ₜ Torus k,
      (∀ x, h (quotientProjection k x) = angleMap k x) ∧
      IsSmoothMap Q T h ∧ IsSmoothMap T Q h.symm ∧
      T.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (transportAtlas h (angleAtlas k))

/-- An explicit bridge from the literal quotient by integer translations to
the coordinatewise quotient representation and then the product of circles.
Both triangles commute on every real coordinate vector. -/
def latticeAngleHomeomorphType : Prop :=
  ∀ k : ℕ, ∃ e : LatticeQuotient k ≃ₜ FlatTorus k,
    (∀ x, e (latticeProjection k x) = quotientProjection k x) ∧
    ∃ h : LatticeQuotient k ≃ₜ Torus k,
      ∀ x, h (latticeProjection k x) = angleMap k x

-- Full types and values for the exported canonical objects.
def SphereType := ℕ → Type
def SphereValue : SphereType := SphereTorusData.Sphere

def TorusType := ℕ → Type
def TorusValue : TorusType := SphereTorusData.Torus

def FlatTorusType := ℕ → Type
def FlatTorusValue : FlatTorusType := SphereTorusData.FlatTorus

def LatticeQuotientType := ℕ → Type
def LatticeQuotientValue : LatticeQuotientType := SphereTorusData.LatticeQuotient

def hemisphereAtlasType := (n : ℕ) → Set (ModelChart n .euclidean (Sphere n))
def hemisphereAtlasValue : hemisphereAtlasType := SphereTorusData.hemisphereAtlas

def productHemisphereAtlasType := (k : ℕ) → Set (ModelChart k .euclidean (Torus k))
def productHemisphereAtlasValue : productHemisphereAtlasType := SphereTorusData.productHemisphereAtlas

def angleAtlasType := (k : ℕ) → Set (ModelChart k .euclidean (FlatTorus k))
def angleAtlasValue : angleAtlasType := SphereTorusData.angleAtlas

def quotientProjectionType := (k : ℕ) → Euclidean k → FlatTorus k
def quotientProjectionValue : quotientProjectionType := SphereTorusData.quotientProjection

def angleMapType := (k : ℕ) → Euclidean k → Torus k
noncomputable def angleMapValue : angleMapType := SphereTorusData.angleMap

end Specs.SmoothManifolds.Examples.SpheresAndTori
