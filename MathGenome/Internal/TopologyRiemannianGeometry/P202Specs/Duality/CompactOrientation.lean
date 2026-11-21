import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.LocalOrientation

/-!
Fundamental classes near compact sets, paper.tex 2080--2154.
All modules and maps are the original ordinary relative singular homology.
The vanishing and injectivity assertions are stated in their stronger,
orientation-independent form. No nonemptiness, connectedness, positive dimension,
or nonzero coefficient-ring hypothesis is imposed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace P202Specs.CompactOrientation
open P202Specs.LocalOrientation P202Specs.SingularChains P202Specs.RelativeSingularChains

/-- Restriction to the product of the actual local groups at points of K. -/
def localRestrictions (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (K : Set M) (j : ℕ) :
    SupportedGroup R M K j →ₗ[R] ((x : K) → LocalGroup R M x.val j) :=
  LinearMap.pi (fun x : K => restrictPoint R x.property j)

/-- Having the prescribed local orientation at every point of a support. -/
def HasLocalValues (R : Type u) [CommRing R] {n : ℕ} {M : Type v}
    [TopologicalSpace M] (o : LocalChoice R n M) (K : Set M)
    (g : SupportedGroup R M K n) : Prop :=
  ∀ (x : M) (hx : x ∈ K), restrictPoint R hx n g = o x

/-- The canonical projection from ordinary homology to the supported pair.
For K = univ the second space is empty; that this map is an isomorphism is
part of the implementation, not an assumed certificate. -/
def absoluteToSupported (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (j : ℕ) :
    homology R R (TopCat.of M) (j : ℤ) →ₗ[R] SupportedGroup R M Set.univ j :=
  (HomologicalComplex.homologyMap
    (projection (ordinaryFunctor R R) (supportedPair M Set.univ)) (j : ℤ)).hom

namespace Expected

/-- Existence and uniqueness for every compact support and every orientation. -/
def compactClass : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A) (K : Set M), IsCompact K →
      ∃! g : SupportedGroup R M K n, HasLocalValues R o.val K g

/-- Compatibility means the actual support restriction takes one unique class
to the other, for every inclusion of compact supports. -/
def compatibility : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A) (K L : Set M),
    IsCompact K → IsCompact L → ∀ hKL : K ⊆ L,
    ∀ (gK : SupportedGroup R M K n) (gL : SupportedGroup R M L n),
      HasLocalValues R o.val K gK → HasLocalValues R o.val L gL →
      ((relativeHomologyFunctor R R (n : ℤ)).map (supportMap hKL)) gL = gK

/-- All degrees above the manifold dimension vanish. -/
def aboveDimension : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (_A : Manifold n M) (K : Set M), IsCompact K →
      ∀ j : ℕ, n < j → IsZero (SupportedGroup R M K j)

/-- Degree-n classes are detected by their restrictions at all points of K. -/
def localDetection : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (_A : Manifold n M) (K : Set M), IsCompact K →
      Function.Injective (localRestrictions R K n)

/-- The supported class for a compact whole manifold is precisely a unique
ordinary singular homology class, via the canonical quotient projection. -/
def ordinaryFundamentalClass : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A), IsCompact (Set.univ : Set M) →
      Function.Bijective (absoluteToSupported R M n) ∧
      ∃! g : homology R R (TopCat.of M) (n : ℤ),
        HasLocalValues R o.val Set.univ (absoluteToSupported R M n g)

end Expected
end P202Specs.CompactOrientation
