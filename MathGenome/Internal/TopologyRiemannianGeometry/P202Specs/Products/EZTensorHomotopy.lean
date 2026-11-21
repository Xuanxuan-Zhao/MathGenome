import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleModel

/-! Independent tensor-side Eilenberg--Zilber obligation, paper.tex 1814--1893.
The ordinary differential, AW, shuffle and smooth submodules below are exactly
the canonical upstream objects. No contraction or filling is assumed. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace P202Specs.EZTensorHomotopy
open P202Specs.SingularChains P202Specs.AlexanderWhitney P202Specs.ShuffleModel
universe u w vE vF vH vK
variable (R : Type u) [CommRing R]

/-- One simultaneous choice on all spaces, including all continuous maps. -/
structure TensorHomotopy where
  hom : ∀ (X Y : TopCat.{w}) (n : ℕ), Total R X Y n →ₗ[R] Total R X Y (n+1)
  zero : ∀ X Y,
    (aw R X Y 0).comp (shuffle R X Y 0) - LinearMap.id =
      (totalBoundary R X Y 0).comp (hom X Y 0)
  succ : ∀ X Y n,
    (aw R X Y (n+1)).comp (shuffle R X Y (n+1)) - LinearMap.id =
      (totalBoundary R X Y (n+1)).comp (hom X Y (n+1)) +
        (hom X Y n).comp (totalBoundary R X Y n)
  naturality : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
    (totalMap R f g (n+1)).comp (hom X Y n) =
      (hom X' Y' n).comp (totalMap R f g n)

/-- A genuine R-linear lift for the *same* homotopy on the upstream tensor
of supported smooth-chain submodules. No flatness hypothesis is imposed. -/
def TensorHomotopy.Smooth (h : TensorHomotopy R) : Prop :=
  ∀ {E : Type vE} {F : Type vF} {H : Type vH} {K : Type vK}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F) (X Y : TopCat.{w})
    [ChartedSpace H X] [ChartedSpace K Y] (n : ℕ),
    ∃ L : SmoothTotal R I J X Y n →ₗ[R] SmoothTotal R I J X Y (n+1),
      (smoothTotalInclusion R I J X Y (n+1)).comp L =
        (h.hom X Y n).comp (smoothTotalInclusion R I J X Y n)

/-- The full unconditional existence claim, for arbitrary commutative unital
rings, arbitrary spaces, arbitrary rank and every nonnegative degree. -/
def naturalHomotopy_type : Prop := ∀ (R : Type u) [CommRing R],
  ∃ h : TensorHomotopy.{u,w} R, TensorHomotopy.Smooth.{u,w,vE,vF,vH,vK} R h

end P202Specs.EZTensorHomotopy
