import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.FundamentalGroupoid
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! The degree-one Hurewicz map, paper.tex 1708–1738.
All simplices and homology groups below are the shared singular-chain objects.
The interval coordinate of a one-simplex is its weight at vertex 1. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory
namespace P202Specs.HurewiczOne
open P202Specs.SingularChains P202Specs.Topology
universe u
variable {X : TopCat.{u}}

def pointSimplex (x : X) : Simplex X 0 :=
  (simplexEquiv X 0).symm (ContinuousMap.const _ x)

def pathSimplex {x y : X} (a : Path x y) : Simplex X 1 :=
  (simplexEquiv X 1).symm
    (a.toContinuousMap.comp ⟨Convexity.StdSimplex.homeomorphI, Convexity.StdSimplex.homeomorphI.continuous⟩)

def pathChain {x y : X} (a : Path x y) : Chains ℤ X 1 :=
  Finsupp.single (pathSimplex a) 1

/-- Recover the parametrized edge, without any reversal of the ordered vertices. -/
def simplexPath (s : Simplex X 1) :
    Path (simplexEquiv X 1 s (.single 0)) (simplexEquiv X 1 s (.single 1)) where
  toContinuousMap := (simplexEquiv X 1 s).comp
    ⟨Convexity.StdSimplex.homeomorphI.symm, Convexity.StdSimplex.homeomorphI.symm.continuous⟩
  source' := by simp
  target' := by simp

abbrev OneCycles (X : TopCat.{u}) := LinearMap.ker (boundary ℤ ℤ X 0)

/-- The inclusion of two-boundaries into one-cycles. -/
def boundaryToCycles (X : TopCat.{u}) : Chains ℤ X 2 →ₗ[ℤ] OneCycles X :=
  (boundary ℤ ℤ X 1).codRestrict _ (fun c => by
    have h := congrArg (fun f : Chains ℤ X 2 →ₗ[ℤ] Chains ℤ X 0 => f c)
      (show (boundary ℤ ℤ X 0).comp (boundary ℤ ℤ X 1) = 0 from
        ModuleCat.hom_ext_iff.mp ((complex ℤ ℤ X).d_comp_d 2 1 0))
    exact h)

/-- A concrete cycles/boundaries quotient, using the actual differentials. -/
abbrev FirstHomologyQuotient (X : TopCat.{u}) :=
  OneCycles X ⧸ LinearMap.range (boundaryToCycles X)

/-- The canonical bridge from the actual ordinary homology to cycles modulo boundaries. -/
def homologyQuotientEquiv (X : TopCat.{u}) :
    homology ℤ ℤ X 1 ≃ₗ[ℤ] FirstHomologyQuotient X :=
  ((complex ℤ ℤ X).extendHomologyIso (degreeEmbedding 0) (j := 1) (by rfl) ≪≫
    ShortComplex.homologyMapIso ((complex ℤ ℤ X).isoSc' 2 1 0 (by simp) (by simp)) ≪≫
    ((complex ℤ ℤ X).sc' 2 1 0).moduleCatHomologyIso).toLinearEquiv

/-- The class in ordinary H₁ of an explicit singular cycle. -/
def cycleClass (X : TopCat.{u}) (c : Chains ℤ X 1)
    (hc : boundary ℤ ℤ X 0 c = 0) : homology ℤ ℤ X 1 :=
  (homologyQuotientEquiv X).symm
    ((LinearMap.range (boundaryToCycles X)).mkQ ⟨c, hc⟩)

namespace Expected

def pathBoundary : Prop :=
  ∀ (X : TopCat.{u}) (x y : X) (a : Path x y),
    boundary ℤ ℤ X 0 (pathChain a) =
      Finsupp.single (pointSimplex y) 1 - Finsupp.single (pointSimplex x) 1

def concatenationBoundary : Prop :=
  ∀ (X : TopCat.{u}) (x y z : X) (a : Path x y) (b : Path y z),
    ∃ s : Simplex X 2, boundary ℤ ℤ X 1 (Finsupp.single s 1) =
      pathChain a + pathChain b - pathChain (a.trans b)

/-- The triangle identity is an equality of endpoint-fixed path classes. -/
def nullTriangle : Prop :=
  ∀ (X : TopCat.{u}) (s : Simplex X 2),
    let v (i : Fin 3) := simplexEquiv X 2 s (.single i)
    ∃ (a : Path (v 0) (v 1)) (b : Path (v 1) (v 2)) (c : Path (v 0) (v 2)),
      pathSimplex a = face 2 s ∧ pathSimplex b = face 0 s ∧
      pathSimplex c = face 1 s ∧ (a.trans b).Homotopic c

/-- No connectedness is needed to construct the loop-to-cycle homomorphism. -/
def hurewiczMap : Prop :=
  ∀ (X : TopCat.{u}) (x : X),
    ∃ h : Pi1 X x →* Multiplicative (homology ℤ ℤ X 1),
      ∀ a : Path x x, ∃ ha : boundary ℤ ℤ X 0 (pathChain a) = 0,
        h (loopClass a) = Multiplicative.ofAdd (cycleClass X (pathChain a) ha)

/-- The isomorphism is required to be induced by the specified loop map. -/
def hurewiczOne : Prop :=
  ∀ (X : TopCat.{u}) [PathConnectedSpace X] (x : X),
    ∃ e : Additive (Abelianization (Pi1 X x)) ≃+ homology ℤ ℤ X 1,
      ∀ a : Path x x, ∃ ha : boundary ℤ ℤ X 0 (pathChain a) = 0,
        e (Additive.ofMul (Abelianization.of (loopClass a))) =
          cycleClass X (pathChain a) ha

end Expected
end P202Specs.HurewiczOne
