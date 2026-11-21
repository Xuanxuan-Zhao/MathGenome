import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.RelativeFundamentalClass
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.PoincareDuality

/-!
The first cap isomorphism of T31, paper.tex 2307–2319 and 2362–2370.
All groups are the existing integer-graded ordinary singular theories over R.
The collar contains only geometric data. In particular none of the statements
below takes a cohomological equivalence or cap isomorphism as a hypothesis.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped TensorProduct
universe u v
namespace P202Specs.LefschetzRelativeCohomology
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass P202Specs.CompactSupport

/-- The actual inclusion of the interior, with the inherited subspace topology. -/
def interiorInclusion {M : Type v} [TopologicalSpace M] (B : Set M) :
    TopCat.of (Interior B) ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Cap with the shared relative fundamental class in a natural cohomological
 degree. PairProducts fixes the front/back formula on every representative. -/
def capNat (R : Type u) [CommRing R] (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    {M : Type v} [TopologicalSpace M] (B : Set M) (n : ℕ)
    (o : LocalChoice R n (Interior B)) (p : ℕ) :
    relativeCohomology R R (boundaryPair M B) (p : ℤ) →ₗ[R]
      homology R R (TopCat.of M) ((n : ℤ)-p) :=
  (c.relative (boundaryPair M B) p (n : ℤ)).comp
    ((TensorProduct.mk R _ _).flip (fundamentalClass R B n o))

/-- The same cap map in every integer degree. Negative cohomology is zero;
for p≥0 the casts only identify p.toNat with p. -/
def cap (R : Type u) [CommRing R] (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    {M : Type v} [TopologicalSpace M] (B : Set M) (n : ℕ)
    (o : LocalChoice R n (Interior B)) (p : ℤ) :
    relativeCohomology R R (boundaryPair M B) p →ₗ[R]
      homology R R (TopCat.of M) ((n : ℤ)-p) := by
  by_cases hp : 0 ≤ p
  · have he : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp
    exact he ▸ capNat R c B n o p.toNat
  · exact 0

namespace Expected

/-- The two actual cohomology arrows at a collar core are isomorphisms, and
the induced identification with compact supports has its canonical formula
on *every* compact interior support, not only on a chosen sequence of cores.
The statement uses no manifold or orientation assumption. -/
def coreComparison : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]
    (B : Set M), IsClosed B → ∀ (c : Collar B), IsCompact (Set.univ : Set M) →
    (∀ (t : ℝ), 0 < t → t < 1 → ∀ p : ℤ,
      IsIso ((relativeCohomologyFunctor R R p).map
        (relativeToCompact B (c.interiorCore t)).op)) ∧
    (∀ (K : Set (Interior B)), IsCompact K → ∀ p : ℤ,
      IsIso ((relativeCohomologyFunctor R R p).map (compactSupportInclusion B K).op)) ∧
    ∀ p : ℤ, ∃ e : CompactCohomology R (Interior B) p ≃ₗ[R]
        relativeCohomology R R (boundaryPair M B) p,
      ∀ (K : Support (Interior B))
        (a : relativeCohomology R R (supportedPair M (Subtype.val '' (K : Set (Interior B)))) p),
        e (ofSupport R (Interior B) p K
            (((relativeCohomologyFunctor R R p).map
              (compactSupportInclusion B (K : Set (Interior B))).op) a)) =
          ((relativeCohomologyFunctor R R p).map
            (relativeToCompact B (K : Set (Interior B))).op) a

/-- The inclusion really is a homotopy equivalence, and therefore induces
isomorphisms on the actual ordinary homology in every integer degree. -/
def interiorEquivalence : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [T2Space M] (B : Set M),
    IsClosed B → ∀ (_c : Collar B), IsCompact (Set.univ : Set M) →
    (∃ r : TopCat.of M ⟶ TopCat.of (Interior B),
      Nonempty (TopCat.Homotopy (interiorInclusion B ≫ r) (𝟙 _)) ∧
      Nonempty (TopCat.Homotopy (r ≫ interiorInclusion B) (𝟙 _))) ∧
    ∀ (R : Type u) [CommRing R] (i : ℤ),
      IsIso ((homologyFunctor R R i).map (interiorInclusion B))

/-- The first Poincaré–Lefschetz isomorphism and its comparison with the
actual interior duality map. Both c and d satisfy already-established
representative formulas; neither includes any bijectivity certificate.
The half-space atlas supplies the intrinsic boundary and the chapter's
Hausdorff and second-countability conventions. -/
def duality : Prop :=
  ∀ (R : Type u) [CommRing R]
    (c : P202Specs.CapProducts.PairProducts.{u,v} R) (d : DualityData.{u,v} R)
    (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold n .halfSpace M),
    let B := manifoldBoundary A
    ∀ (_collar : Collar B) (AI : Manifold n (Interior B)) (o : Orientation R AI),
      IsCompact (Set.univ : Set M) →
      (∀ p : ℤ, Function.Bijective (cap R c B n o.val p)) ∧
      ∀ p : ℤ, ∃ e : CompactCohomology R (Interior B) p ≃ₗ[R]
          relativeCohomology R R (boundaryPair M B) p,
        (∀ (K : Support (Interior B))
          (a : relativeCohomology R R (supportedPair M (Subtype.val '' (K : Set (Interior B)))) p),
          e (ofSupport R (Interior B) p K
              (((relativeCohomologyFunctor R R p).map
                (compactSupportInclusion B (K : Set (Interior B))).op) a)) =
            ((relativeCohomologyFunctor R R p).map
              (relativeToCompact B (K : Set (Interior B))).op) a) ∧
        ∀ a : CompactCohomology R (Interior B) p,
          cap R c B n o.val p (e a) =
            ((homologyFunctor R R ((n : ℤ)-p)).map (interiorInclusion B))
              (d.D n (Interior B) AI o p a)

/-- Both absolute and relative ordinary homology vanish above the manifold
 dimension. This includes empty and disconnected manifolds and n=0. -/
def aboveDimension : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold n .halfSpace M),
    let B := manifoldBoundary A
    ∀ (_collar : Collar B) (AI : Manifold n (Interior B)) (_o : Orientation R AI),
      IsCompact (Set.univ : Set M) → ∀ i : ℤ, (n : ℤ) < i →
      IsZero (homology R R (TopCat.of M) i) ∧
      IsZero (relativeHomology R R (boundaryPair M B) i)

end Expected
end P202Specs.LefschetzRelativeCohomology
