import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CompactSupportMayerVietoris

/-!
Independent targets for paper.tex 2207–2303 (T30).  The groups and cap maps
are the actual finite singular theories from the shared interfaces.  Degrees
range over all integers; the manifold may be empty, disconnected or noncompact.
No Mayer–Vietoris or local-duality assumption is added to these target types.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v

namespace P202Specs.PoincareDuality
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation P202Specs.CompactSupport

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]

/-- Forgetting compact support, induced by the inclusions of relative cochains
into the original ordinary cochain complex. -/
def forgetSupport (p : ℤ) :
    CompactCohomology R M p →ₗ[R] ordinaryCohomology R R (TopCat.of M) p :=
  descend R M p (fun K => (homologyMap (cochainInclusion R M K) p).hom) (by
    intro K L h a
    change homologyMap (cochainInclusion R M L) p
      (homologyMap (cochainTransition R M h) p a) = _
    rw [← ModuleCat.comp_apply, ← homologyMap_comp, cochainInclusion_transition])

/-- All-degree duality for this precise cap map and orientation. -/
def Holds (d : DualityData.{u,v} R) {n : ℕ} (A : Manifold n M)
    (o : Orientation R A) : Prop :=
  ∀ p : ℤ, Function.Bijective (d.D n M A o p)

namespace Expected

/-- The complete compact-support Poincaré duality theorem, including dimension
zero and all negative and above-dimension degrees. -/
def duality : Prop :=
  ∀ (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A), Holds R M d A o

/-- On a compact manifold forgetting support is an isomorphism. Under its
inverse the same D is cap by the ordinary fundamental class, with the exact
front/back convention, specified on every ordinary cocycle and cycle.
The fundamental class is fixed by its prescribed local orientation values.
-/
def compactIdentification : Prop :=
  ∀ (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A),
    IsCompact (Set.univ : Set M) →
    ∃ (h : ∀ p : ℤ, Function.Bijective (forgetSupport R M p))
      (μ : homology R R (TopCat.of M) (n : ℤ)),
      P202Specs.CompactOrientation.HasLocalValues R o.val Set.univ
        (P202Specs.CompactOrientation.absoluteToSupported R M n μ) ∧
      ∀ (p : ℕ) (a : (ordinaryCochains R R (TopCat.of M)).cycles (p : ℤ))
        (z : (ordinaryComplex R R (TopCat.of M)).cycles (n : ℤ)),
        (ordinaryComplex R R (TopCat.of M)).homologyπ (n : ℤ) z = μ →
        ∃ w : (ordinaryComplex R R (TopCat.of M)).cycles ((n : ℤ)-p),
          (ordinaryComplex R R (TopCat.of M)).iCycles ((n : ℤ)-p) w =
            P202Specs.CapProducts.cap R (TopCat.of M) p (n : ℤ)
              (P202Specs.CupProduct.cocycleValue R (TopCat.of M) p a)
              ((ordinaryComplex R R (TopCat.of M)).iCycles (n : ℤ) z) ∧
          d.D n M A o (p : ℤ)
            ((LinearEquiv.ofBijective (forgetSupport R M (p : ℤ)) (h (p : ℤ))).symm
              ((ordinaryCochains R R (TopCat.of M)).homologyπ (p : ℤ) a)) =
            (ordinaryComplex R R (TopCat.of M)).homologyπ ((n : ℤ)-p) w

/-- The dimension-vanishing consequence used subsequently in the Euler
argument. The ordinary theory here always has finite chains. -/
def aboveDimension : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (_A : Manifold n M) (o : Orientation R _A) (i : ℤ), (n : ℤ) < i →
      IsZero (homology R R (TopCat.of M) i)

end Expected
end P202Specs.PoincareDuality
