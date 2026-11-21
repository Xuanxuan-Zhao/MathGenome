import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleChains

/-! The product-side natural Eilenberg–Zilber homotopy on finite singular
chains. All objects, maps, signs, and smooth-chain submodules are the upstream
ones. The degree-zero equation is ordinary, without an augmentation term. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory
namespace P202Specs.EZProductHomotopy
open P202Specs.SingularChains P202Specs.AlexanderWhitney P202Specs.ShuffleModel
universe u w
variable (R : Type u) [CommRing R]

/-- The shared singular boundary with its finite-chain module type exposed. -/
def differential (X : TopCat.{w}) (n : ℕ) :
    Chains R X (n+1) →ₗ[R] Chains R X n := boundary R R X n

/-- A single family, natural in both spaces, of homotopies sh AW - id = dH+Hd.
The degree-zero identity has no boundary to degree -1. -/
structure ProductHomotopy where
  hom : ∀ (X Y : TopCat.{w}) (n : ℕ),
    Chains R (productSpace X Y) n →ₗ[R] Chains R (productSpace X Y) (n+1)
  zero : ∀ X Y,
    (shuffle R X Y 0).comp (aw R X Y 0) - LinearMap.id =
      (differential R (productSpace X Y) 0).comp (hom X Y 0)
  succ : ∀ X Y n,
    (shuffle R X Y (n+1)).comp (aw R X Y (n+1)) - LinearMap.id =
      (differential R (productSpace X Y) (n+1)).comp (hom X Y (n+1)) +
        (hom X Y n).comp (differential R (productSpace X Y) n)
  naturality : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
    (((chainMap R R (productMap f g)).f (n+1)).hom).comp (hom X Y n) =
      (hom X' Y' n).comp (((chainMap R R (productMap f g)).f n).hom)

/-- Preservation of smooth singular chains uses the upstream chart-local
criterion with local extensions at every corner. -/
def ProductHomotopy.Smooth (h : ProductHomotopy R) : Prop :=
  ∀ {E F H K : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F) (X Y : TopCat.{w})
    [ChartedSpace H X] [ChartedSpace K Y] (n : ℕ)
    (c : Chains R (productSpace X Y) n),
    c ∈ smoothChains R (H := ModelProd H K) (fun z => (I z.1, J z.2))
      (productSpace X Y) n →
    h.hom X Y n c ∈ smoothChains R (H := ModelProd H K)
      (fun z => (I z.1, J z.2)) (productSpace X Y) (n+1)

/-- One chosen family satisfies both the chain identities and smoothness,
simultaneously for all spaces and all continuous maps in both factors. -/
def naturalHomotopy_type : Prop := ∀ (R : Type u) [CommRing R],
  ∃ h : ProductHomotopy.{u,w} R, h.Smooth R

end P202Specs.EZProductHomotopy
