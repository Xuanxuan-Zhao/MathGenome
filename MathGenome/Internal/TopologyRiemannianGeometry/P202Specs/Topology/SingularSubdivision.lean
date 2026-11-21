import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Concrete barycentric subdivision, using augmented affine vertex chains.
An affine chain indexed by `n` has `n` vertices, hence dimension `n-1`.
The unique empty vertex list represents augmented degree -1. The recursion
cones the subdivided boundary to the barycenter; its signs are the induced
boundary signs. We use barycenter-first vertex lists (decreasing face
dimension in a flag), a standard parametrization convention for the signed
barycentric subdivision. No theorem about the operators is assumed here. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite

namespace P202Specs.SingularSubdivision
open P202Specs.SingularChains
open Convexity
universe u v w

abbrev AffineChains (R : Type u) [CommRing R] (Y : Type v) (n : ℕ) :=
  (Fin n → Y) →₀ R

def affineBoundary (R : Type u) [CommRing R] (Y : Type v) (n : ℕ) :
    AffineChains R Y (n+1) →ₗ[R] AffineChains R Y n :=
  ∑ i : Fin (n+1), (-1 : R) ^ i.val •
    Finsupp.lmapDomain R R (fun t => t ∘ i.succAbove)

def cone (R : Type u) [CommRing R] {Y : Type v} (b : Y) (n : ℕ) :
    AffineChains R Y n →ₗ[R] AffineChains R Y (n+1) :=
  Finsupp.lmapDomain R R (fun t => Fin.cons b t)

def affinePush (R : Type u) [CommRing R] {Y : Type v} {Z : Type w}
    (f : Y → Z) (n : ℕ) : AffineChains R Y n →ₗ[R] AffineChains R Z n :=
  Finsupp.lmapDomain R R (fun t => f ∘ t)

/-- Recursive signed barycentric subdivision, including the empty simplex. -/
def affineSubdivision (R : Type u) [CommRing R] (Y : Type v)
    [ConvexSpace ℝ Y] : ∀ n, AffineChains R Y n →ₗ[R] AffineChains R Y n := fun
  | 0 => LinearMap.id
  | n+1 => Finsupp.linearCombination R (fun t =>
      cone R ((StdSimplex.barycenter : StdSimplex ℝ (Fin (n+1))).iConvexComb t) n
        (affineSubdivision R Y n (affineBoundary R Y n (Finsupp.single t 1))))

/-- The cone filling of `S - id - K∂`, with zero in augmented degree -1. -/
def affineHomotopy (R : Type u) [CommRing R] (Y : Type v)
    [ConvexSpace ℝ Y] : ∀ n, AffineChains R Y n →ₗ[R] AffineChains R Y (n+1) := fun
  | 0 => 0
  | n+1 => Finsupp.linearCombination R (fun t =>
      cone R ((StdSimplex.barycenter : StdSimplex ℝ (Fin (n+1))).iConvexComb t) (n+1)
        (affineSubdivision R Y (n+1) (Finsupp.single t 1) - Finsupp.single t 1 -
          affineHomotopy R Y n (affineBoundary R Y n (Finsupp.single t 1))))

abbrev Delta (n : ℕ) := StdSimplex ℝ (Fin (n+1))

/-- Affine maps between finite real simplices have their actual simplex topology. -/
def affineSimplexMap {m n : ℕ} (t : Fin (n+1) → Delta m) : C(Delta n, Delta m) :=
  ⟨StdSimplex.affineMapMk t, by
    apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (m+1))).continuous_iff.mpr
    apply continuous_pi_iff.mpr
    intro i
    exact StdSimplex.continuous_of_affineMap
      ⟨fun x => (StdSimplex.affineMapMk t x).weights i, by
        have h := (StdSimplex.isAffineMap_weights ℝ (Fin (m+1))).comp
          (StdSimplex.affineMapMk t).isAffineMap
        exact (Convexity.IsAffineMap.linearMap
          (Finsupp.lapply i : (Fin (m+1) →₀ ℝ) →ₗ[ℝ] ℝ)).comp h⟩⟩

def evaluate (R : Type u) [CommRing R] {X : TopCat.{v}} {m : ℕ}
    (s : Simplex X m) (n : ℕ) :
    AffineChains R (Delta m) (n+1) →ₗ[R] Chains R X n :=
  Finsupp.lmapDomain R R (fun t =>
    (simplexEquiv X n).symm ((simplexEquiv X m s).comp (affineSimplexMap t)))

def subdivision (R : Type u) [CommRing R] (X : TopCat.{v}) (n : ℕ) :
    Chains R X n →ₗ[R] Chains R X n :=
  Finsupp.linearCombination R (fun s => evaluate R s n
    (affineSubdivision R (Delta n) (n+1) (Finsupp.single StdSimplex.single 1)))

def homotopy (R : Type u) [CommRing R] (X : TopCat.{v}) (n : ℕ) :
    Chains R X n →ₗ[R] Chains R X (n+1) :=
  Finsupp.linearCombination R (fun s => evaluate R s (n+1)
    (affineHomotopy R (Delta n) (n+1) (Finsupp.single StdSimplex.single 1)))

/-- Index zero is augmented degree -1, on which subdivision is identity. -/
def augmentedSubdivision (R : Type u) [CommRing R] (X : TopCat.{v}) (n : ℕ) :
    (augmentedShifted R R X).X n ⟶ (augmentedShifted R R X).X n :=
  match n with
  | 0 => 𝟙 _
  | n+1 => ModuleCat.ofHom (subdivision R X n)

/-- The homotopy is zero on the coefficient module in degree -1. -/
def augmentedHomotopy (R : Type u) [CommRing R] (X : TopCat.{v}) (n : ℕ) :
    (augmentedShifted R R X).X n ⟶ (augmentedShifted R R X).X (n+1) :=
  match n with
  | 0 => 0
  | n+1 => ModuleCat.ofHom (homotopy R X n)

/-- Finite union of images of the simplices whose coefficients are nonzero. -/
def support {R : Type u} [CommRing R] {X : TopCat.{v}} {n : ℕ}
    (c : Chains R X n) : Set X :=
  ⋃ s ∈ c.support, Set.range (simplexEquiv X n s)

def SupportedIn {R : Type u} [CommRing R] {X : TopCat.{v}} {n : ℕ}
    (A : Set X) (c : Chains R X n) : Prop := support c ⊆ A

/-- Smallness is simplexwise, not the stronger assertion that the entire
chain support belongs to a single cover member. -/
def IsSmall {R : Type u} [CommRing R] {X : TopCat.{v}} {n : ℕ}
    {ι : Type w} (U : ι → Set X) (c : Chains R X n) : Prop :=
  ∀ s ∈ c.support, ∃ i, Set.range (simplexEquiv X n s) ⊆ U i

/-- All conclusions for the concrete barycentric operators, over every
commutative ring and every topological space, including empty spaces and
the zero ring. The two homotopy equations cover degrees zero and positive.
The augmented extension is `S₋₁ = id`, `K₋₁ = 0`; the augmentation identities
below verify the additional chain and homotopy equations at that degree. -/
def supportControlledSubdivision : Prop :=
  ∀ (R : Type u) [CommRing R],
    (∀ (X : TopCat.{v}) (n : ℕ) (c : Chains R X (n+1)),
      boundary R R X n (subdivision R X (n+1) c) =
        subdivision R X n (boundary R R X n c)) ∧
    (∀ {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ) (c : Chains R X n),
      subdivision R Y n (((chainMap R R f).f n).hom c) =
        ((chainMap R R f).f n).hom (subdivision R X n c)) ∧
    (∀ {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ) (c : Chains R X n),
      homotopy R Y n (((chainMap R R f).f n).hom c) =
        ((chainMap R R f).f (n+1)).hom (homotopy R X n c)) ∧
    (∀ (X : TopCat.{v}) (c : Chains R X 0),
      boundary R R X 0 (homotopy R X 0 c) = subdivision R X 0 c - c) ∧
    (∀ (X : TopCat.{v}) (n : ℕ) (c : Chains R X (n+1)),
      HAdd.hAdd (α := Chains R X (n+1)) (β := Chains R X (n+1))
        (γ := Chains R X (n+1))
        (boundary R R X (n+1) (homotopy R X (n+1) c))
        (homotopy R X n (boundary R R X n c)) = subdivision R X (n+1) c - c) ∧
    (∀ (X : TopCat.{v}) (n : ℕ) (c : Chains R X n),
      support (subdivision R X n c) ⊆ support c ∧
      support (homotopy R X n c) ⊆ support c) ∧
    (∀ (X : TopCat.{v}) (c : Chains R X 0),
      subdivision R X 0 c = c ∧ homotopy R X 0 c = 0 ∧
      augmentationLinear R R X (subdivision R X 0 c) = augmentationLinear R R X c) ∧
    (∀ (X : TopCat.{v}) (A : Set X) (n : ℕ) (c : Chains R X n),
      SupportedIn A c → SupportedIn A (subdivision R X n c) ∧
        SupportedIn A (homotopy R X n c)) ∧
    (∀ (X : TopCat.{v}) (ι : Type v) (U : ι → Set X) (n : ℕ) (c : Chains R X n),
      IsSmall U c → IsSmall U (subdivision R X n c) ∧ IsSmall U (homotopy R X n c)) ∧
    (∀ (X : TopCat.{v}) (n : ℕ),
      augmentedSubdivision R X (n+1) ≫ (augmentedShifted R R X).d (n+1) n =
        (augmentedShifted R R X).d (n+1) n ≫ augmentedSubdivision R X n) ∧
    (∀ (X : TopCat.{v}) (n : ℕ),
      augmentedHomotopy R X (n+1) ≫ (augmentedShifted R R X).d (n+2) (n+1) +
        (augmentedShifted R R X).d (n+1) n ≫ augmentedHomotopy R X n =
          augmentedSubdivision R X (n+1) - 𝟙 _) ∧
    (∀ (X : TopCat.{v}),
      augmentedHomotopy R X 0 ≫ (augmentedShifted R R X).d 1 0 =
        augmentedSubdivision R X 0 - 𝟙 _) ∧
    (∀ {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ),
      (augmentedShiftedMap R R f).f n ≫ augmentedSubdivision R Y n =
        augmentedSubdivision R X n ≫ (augmentedShiftedMap R R f).f n) ∧
    (∀ {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ),
      (augmentedShiftedMap R R f).f n ≫ augmentedHomotopy R Y n =
        augmentedHomotopy R X n ≫ (augmentedShiftedMap R R f).f (n+1))

end P202Specs.SingularSubdivision
