import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CompactSupportDualityMap
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.RelativeCupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.MayerVietoris
import Mathlib.Algebra.Ring.NegOnePow

/-!
Independent gluing interface for paper.tex 2231–2277.  This statement constructs
the compact-support sequence and its comparison with ordinary finite-chain
Mayer–Vietoris.  Exactness of a pre-supplied sequence is not a premise.

The connecting map is normalized by the actual supported cochain splitting,
the dual of C(M)/(C(P)+C(Q)), and excision into U∩V.  In particular its value is
specified in H_c(U∩V), not merely after extension to M.  The ordinary connecting
map is normalized by the existing positive boundary-of-a-lift formula.
No duality map is assumed bijective.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
universe u v

namespace P202Specs.CompactSupportMayerVietoris
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]

/-- An ordered two-set open cover, including empty members and intersection. -/
structure Cover where
  left : Set M
  right : Set M
  left_open : IsOpen left
  right_open : IsOpen right
  covers : left ∪ right = Set.univ

abbrev Cover.intersection (C : Cover M) := C.left ∩ C.right

/-- The same cover in the already fixed ordinary Mayer–Vietoris interface. -/
def Cover.ordinary (C : Cover M) : P202Specs.MayerVietoris.CoverPair.{v,0} :=
  P202Specs.MayerVietoris.CoverPair.ofSets ⟨TopCat.of M, ∅⟩
    C.left C.right C.left_open C.right_open C.covers

variable {M}

/-- Inclusion between the actual subspaces, rather than an identification of
the intersection with a nested subtype. -/
def subsetInclusion {B E : Set M} (h : B ⊆ E) : C(B, E) :=
  ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩

def supportInSubset {B E : Set M} (h : B ⊆ E) (K : Support B) : Support E :=
  K.map (subsetInclusion h) (subsetInclusion h).continuous

def subsetPairInclusion {B E : Set M} (h : B ⊆ E) (K : Support B) :
    supportedPair B K ⟶ supportedPair E (supportInSubset h K) where
  map := TopCat.ofHom (subsetInclusion h)
  mapsTo := by
    rintro x hx ⟨y, hy, he⟩
    have hval : y.val = x.val := congrArg (fun z : E => z.val) he
    have he' : y = x := Subtype.ext hval
    exact hx (he' ▸ hy)

/-- Excision restriction along a named inclusion of open subspaces. -/
def subsetPullback {B E : Set M} (h : B ⊆ E) (K : Support B) (p : ℤ) :
    supportedCohomology R E p (supportInSubset h K) ⟶
      supportedCohomology R B p K :=
  (relativeCohomologyFunctor R R p).map (subsetPairInclusion h K).op

variable (M) [T2Space M]

def UnionCofinal (C : Cover M) : Prop :=
  ∀ N : Support M, ∃ (K : Support C.left) (L : Support C.right),
    N ≤ ambientSupport M C.left K ⊔ ambientSupport M C.right L

/-- Both the existence of the actual intersection support and its cofinality. -/
def IntersectionCofinal (C : Cover M) : Prop :=
  (∀ (K : Support C.left) (L : Support C.right),
    ∃ J : Support C.intersection,
      ambientSupport M C.intersection J =
        ambientSupport M C.left K ⊓ ambientSupport M C.right L) ∧
  ∀ N : Support C.intersection,
    ∃ (K : Support C.left) (L : Support C.right),
      ambientSupport M C.intersection N ≤
        ambientSupport M C.left K ⊓ ambientSupport M C.right L

abbrev CompactMiddle (C : Cover M) (p : ℤ) :=
  ModuleCat.of R (CompactCohomology R C.left p) ⊞
    ModuleCat.of R (CompactCohomology R C.right p)

abbrev IntersectionExtension (C : Cover M) (E : Set M) :=
  ∀ p : ℤ, CompactCohomology R C.intersection p →ₗ[R] CompactCohomology R E p

/-- Extension is fixed by inverse excision at each compact support. -/
def ExtensionRepresents (C : Cover M) {E : Set M} (h : C.intersection ⊆ E)
    (e : IntersectionExtension R M C E) : Prop :=
  ∀ (p : ℤ) (K : Support C.intersection)
    (b : supportedCohomology R E p (supportInSubset h K)),
    e p (ofSupport R C.intersection p K (subsetPullback R h K p b)) =
      ofSupport R E p (supportInSubset h K) b

def first (C : Cover M)
    (eL : IntersectionExtension R M C C.left)
    (eR : IntersectionExtension R M C C.right) (p : ℤ) :
    ModuleCat.of R (CompactCohomology R C.intersection p) ⟶ CompactMiddle R M C p :=
  biprod.lift (ModuleCat.ofHom (eL p)) (-ModuleCat.ofHom (eR p))

def sum (d : DualityData.{u,v} R) (C : Cover M) (p : ℤ) :
    CompactMiddle R M C p ⟶ ModuleCat.of R (CompactCohomology R M p) :=
  biprod.desc (ModuleCat.ofHom (d.extend M C.left C.left_open p))
    (ModuleCat.ofHom (d.extend M C.right C.right_open p))

abbrev Connecting (C : Cover M) :=
  ∀ p : ℤ, CompactCohomology R M p →ₗ[R] CompactCohomology R C.intersection (p+1)

/-- Every degree of the resulting compact-support long exact sequence. -/
def Exact (d : DualityData.{u,v} R) (C : Cover M)
    (eL : IntersectionExtension R M C C.left)
    (eR : IntersectionExtension R M C C.right) (δ : Connecting R M C) : Prop :=
  (∀ p : ℤ, (ComposableArrows.mk₅ (first R M C eL eR p) (sum R M d C p)
    (ModuleCat.ofHom (δ p)) (first R M C eL eR (p+1)) (sum R M d C (p+1))).Exact) ∧
  ∀ p : ℤ, (ComposableArrows.mk₂ (first R M C eL eR p) (sum R M d C p)).Exact

/-- P=M\K and Q=M\L, as actual subspaces used by the small-chain comparison. -/
def complementPair (C : Cover M) (K : Support C.left) (L : Support C.right) :
    P202Specs.RelativeCupProduct.TwoSubspaces.{v} :=
  ⟨TopCat.of M, (ambientSupport M C.left K : Set M)ᶜ,
    (ambientSupport M C.right L : Set M)ᶜ⟩

/-- Identity of ambient spaces with the De Morgan identification of subspaces. -/
def intersectionPairMap (C : Cover M) (K : Support C.left) (L : Support C.right)
    (J : Support C.intersection)
    (hJ : ambientSupport M C.intersection J =
      ambientSupport M C.left K ⊓ ambientSupport M C.right L) :
    (complementPair M C K L).unionPair ⟶
      supportedPair M (ambientSupport M C.intersection J) where
  map := 𝟙 _
  mapsTo := by
    intro x hx hxJ
    change x ∈ (ambientSupport M C.intersection J : Set M) at hxJ
    rw [hJ] at hxJ
    rcases hx with hx | hx
    · exact hx hxJ.1
    · exact hx hxJ.2

/-- Positive coboundary-of-the-left-lift convention. All lifts and comparisons
are conclusions, and the final equality takes place in the intersection. -/
def ConnectingFormula (C : Cover M) (δ : Connecting R M C) : Prop :=
  ∀ (K : Support C.left) (L : Support C.right) (p : ℤ)
    (a : (supportedCochains R M
      (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).cycles p),
    ∃ (J : Support C.intersection)
      (hJ : ambientSupport M C.intersection J =
        ambientSupport M C.left K ⊓ ambientSupport M C.right L)
      (aP : (supportedCochains R M (ambientSupport M C.left K)).X p)
      (aQ : (supportedCochains R M (ambientSupport M C.right L)).X p)
      (z : (P202Specs.RelativeCupProduct.sumCochains R (complementPair M C K L)).cycles (p+1))
      (b : supportedCohomology R M (p+1) (ambientSupport M C.intersection J)),
      (cochainInclusion R M (ambientSupport M C.left K)).f p aP +
        (cochainInclusion R M (ambientSupport M C.right L)).f p aQ =
        (cochainInclusion R M
          (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).f p
          ((supportedCochains R M
            (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).iCycles p a) ∧
      (P202Specs.RelativeCupProduct.sumToAbsolute R (complementPair M C K L)).f (p+1)
        ((P202Specs.RelativeCupProduct.sumCochains R (complementPair M C K L)).iCycles (p+1) z) =
        (ordinaryCochains R R (TopCat.of M)).d p (p+1)
          ((cochainInclusion R M (ambientSupport M C.left K)).f p aP) ∧
      homologyMap (P202Specs.RelativeCupProduct.unionComparison R (complementPair M C K L)) (p+1)
        (((relativeCohomologyFunctor R R (p+1)).map
          (intersectionPairMap M C K L J hJ).op) b) =
        (P202Specs.RelativeCupProduct.sumCochains R (complementPair M C K L)).homologyπ (p+1) z ∧
      δ p (ofSupport R M p (ambientSupport M C.left K ⊔ ambientSupport M C.right L)
        ((supportedCochains R M
          (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).homologyπ p a)) =
        ofSupport R C.intersection (p+1) J (openPullback R M C.intersection J (p+1) b)

/-- Transport only changes the integer degree, not the singular homology model. -/
def degreeTransport (X : TopCat.{v}) (i j : ℤ) (h : i = j) :
    homology R R X i →ₗ[R] homology R R X j := by
  subst j
  exact LinearMap.id

abbrev ordinaryChains := P202Specs.MayerVietoris.theoryFunctor.{u,v} R .ordinary

/-- Full cover and cap gluing data. Existence of these data is the upstream
obligation; no field is available as an assumption before it has been proved. -/
structure GluingData (d : DualityData.{u,v} R) (n : ℕ)
    (A : Manifold n M) (o : Orientation R A) (C : Cover M) where
  union_cofinal : UnionCofinal M C
  intersection_cofinal : IntersectionCofinal M C
  extendLeft : IntersectionExtension R M C C.left
  extendRight : IntersectionExtension R M C C.right
  left_represents : ExtensionRepresents R M C Set.inter_subset_left extendLeft
  right_represents : ExtensionRepresents R M C Set.inter_subset_right extendRight
  connecting : Connecting R M C
  exact : Exact R M d C extendLeft extendRight connecting
  connecting_formula : ConnectingFormula R M C connecting
  homologyConnecting : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R)
  homology_exact : P202Specs.MayerVietoris.Exact (ordinaryChains R) homologyConnecting
  homology_natural : P202Specs.MayerVietoris.Natural (ordinaryChains R) homologyConnecting
  homology_boundary : P202Specs.MayerVietoris.BoundaryFormula (ordinaryChains R) homologyConnecting
  leftManifold : Manifold n C.left
  rightManifold : Manifold n C.right
  intersectionManifold : Manifold n C.intersection
  leftOrientation : Orientation R leftManifold
  rightOrientation : Orientation R rightManifold
  intersectionOrientation : Orientation R intersectionManifold
  left_compatible : OpenOrientationCompatible R M o.val leftOrientation.val
  right_compatible : OpenOrientationCompatible R M o.val rightOrientation.val
  intersection_compatible : OpenOrientationCompatible R M o.val intersectionOrientation.val
  cap_first : ∀ p : ℤ,
    first R M C extendLeft extendRight p ≫
      biprod.map (ModuleCat.ofHom (d.D n C.left leftManifold leftOrientation p))
        (ModuleCat.ofHom (d.D n C.right rightManifold rightOrientation p)) =
      ModuleCat.ofHom (d.D n C.intersection intersectionManifold intersectionOrientation p) ≫
        P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary ((n : ℤ)-p)
  cap_sum : ∀ p : ℤ,
    sum R M d C p ≫ ModuleCat.ofHom (d.D n M A o p) =
      biprod.map (ModuleCat.ofHom (d.D n C.left leftManifold leftOrientation p))
        (ModuleCat.ofHom (d.D n C.right rightManifold rightOrientation p)) ≫
        P202Specs.MayerVietoris.sum (ordinaryChains R) C.ordinary ((n : ℤ)-p)
  cap_connecting : ∀ (p : ℤ) (a : CompactCohomology R M p),
    homologyConnecting C.ordinary ((n : ℤ)-p-1)
      (degreeTransport R (TopCat.of M) ((n : ℤ)-p) (((n : ℤ)-p-1)+1)
        (by omega) (d.D n M A o p a)) =
      ((p+1).negOnePow : ℤ) •
        degreeTransport R (TopCat.of C.intersection) ((n : ℤ)-(p+1)) ((n : ℤ)-p-1)
          (by omega)
          (d.D n C.intersection intersectionManifold intersectionOrientation (p+1) (connecting p a))

namespace Expected

/-- Full actual sequence and signed cap comparison for every oriented manifold
and every open two-set cover, including dimension zero and empty spaces. -/
def gluing : Prop :=
  ∀ (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    (n : ℕ) (M : Type v) [TopologicalSpace M] (A : Manifold n M)
    (o : Orientation R A),
    letI : T2Space M := A.hausdorff
    ∀ C : Cover M, Nonempty (GluingData R M d n A o C)

end Expected
end P202Specs.CompactSupportMayerVietoris
