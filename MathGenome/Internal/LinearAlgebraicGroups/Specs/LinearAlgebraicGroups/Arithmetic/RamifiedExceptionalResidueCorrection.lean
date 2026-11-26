import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.Lang
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalResidueCorrection

noncomputable section

variable {k : Type u} [Field k]

abbrev GeometricPoints (X : SchemeOver k) :=
  Points X (CommAlgCat.of k (AlgebraicClosure k))

abbrev geometricScheme (X : SchemeOver k) := (baseChange k (AlgebraicClosure k)).obj X

/-- The point on the geometric base change underlying a geometric point. -/
def geometricCarrier {X : SchemeOver k} (p : GeometricPoints X) :
    (geometricScheme X).left :=
  pullback.lift p.left (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) (by
    change p.left ≫ X.hom = 𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))) ≫ fieldSpecMap k (AlgebraicClosure k)
    rw [Category.id_comp]
    exact Over.w p)
    (IsLocalRing.closedPoint (AlgebraicClosure k))

/-- Geometric points carry the Zariski topology induced from the scheme after
extension to the algebraic closure. -/
abbrev geometricTopology (X : SchemeOver k) : TopologicalSpace (GeometricPoints X) :=
  TopologicalSpace.induced geometricCarrier inferInstance

/-- A finite family of finite-type parameter maps describes the image. -/
structure Parameterization (G : AffineAlgebraicGroup k)
    (S : Subgroup (GeometricPoints G.val.X)) where
  Index : Type u
  finite : Finite Index
  source : Index → SchemeOver k
  finiteType : ∀ i, LocallyOfFiniteType (source i).hom
  quasiCompact : ∀ i, QuasiCompact (source i).hom
  map : ∀ i, source i ⟶ G.val.X
  image_eq : ⋃ i, Set.range (fun p : GeometricPoints (source i) ↦ p ≫ map i) = S

/-- The generators are images of algebraic group homomorphisms, and these
images are connected in the geometric point topology. -/
structure ConnectedGenerators (G : AffineAlgebraicGroup k)
    (S : Subgroup (GeometricPoints G.val.X)) where
  Index : Type u
  source : Index → AffineAlgebraicGroup k
  connected : ∀ i, ConnectedSpace (source i).val.X.left
  map : ∀ i, (source i).val ⟶ G.val
  imageConnected : ∀ i, @_root_.IsConnected _ (geometricTopology G.val.X)
    (Set.range (fun p : GeometricPoints (source i).val.X ↦ p ≫ (map i).hom.hom))
  generates : Subgroup.closure
    (⋃ i, Set.range (fun p : GeometricPoints (source i).val.X ↦ p ≫ (map i).hom.hom)) = S

/-- A closed, reduced, smooth and geometrically connected subgroup scheme
with the prescribed geometric image. -/
def Realizes (G : AffineAlgebraicGroup k) (S : Subgroup (GeometricPoints G.val.X))
    (H : AffineAlgebraicGroup k) (i : H.val ⟶ G.val) : Prop :=
  IsClosedImmersion i.hom.hom.left ∧ IsReduced H.val.X.left ∧ Smooth H.val.X.hom ∧
    ConnectedSpace (geometricScheme H.val.X).left ∧
    Set.range (fun p : GeometricPoints H.val.X ↦ p ≫ i.hom.hom) = S

def ClosedResidueImage : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G : AffineAlgebraicGroup k)
    (S : Subgroup (GeometricPoints G.val.X)),
    Parameterization G S → ConnectedGenerators G S →
    ∃ (H : AffineAlgebraicGroup k) (i : H.val ⟶ G.val), Realizes G S H i

/-- The coefficient stages and their homomorphic reductions. The group upstairs
may be infinite. Only each coefficient Galois group has to be finite cyclic. -/
structure CoefficientStages [Fintype k]
    (G : AffineAlgebraicGroup k) (S : Subgroup (GeometricPoints G.val.X))
    (I : Type u) [Preorder I] where
  Coeff : I → GrpCat.{u}
  Gal : I → GrpCat.{u}
  galFinite : ∀ i, Finite (Gal i)
  generator : ∀ i, Gal i
  cyclic : ∀ i, Subgroup.zpowers (generator i) = ⊤
  act : ∀ i, Gal i →* MulAut (Coeff i)
  extend : ∀ {i j}, i ≤ j → Coeff i →* Coeff j
  restrict : ∀ {i j}, i ≤ j → Gal j →* Gal i
  restrict_generator : ∀ {i j} (h : i ≤ j), restrict h (generator j) = generator i
  reduction : ∀ i, Coeff i →* GeometricPoints G.val.X
  reduction_extend : ∀ {i j} (h : i ≤ j) (x : Coeff i),
    reduction j (extend h x) = reduction i x
  reduction_generator : ∀ i (x : Coeff i),
    reduction i (act i (generator i) x) = frobeniusOnPoints _ (reduction i x)
  extend_action : ∀ {i j} (h : i ≤ j) (σ : Gal j) (x : Coeff i),
    extend h (act i (restrict h σ) x) = act j σ (extend h x)
  image_eq : ⋃ i, Set.range (reduction i) = S

/-- After inflation and a single change of trivialization, all values reduce
to the identity at the enlarged stage. -/
def CorrectsAtLargerStage [Fintype k] {G : AffineAlgebraicGroup k}
    {S : Subgroup (GeometricPoints G.val.X)} {I : Type u} [Preorder I]
    (D : CoefficientStages G S I) (i : I) (c : D.Gal i → D.Coeff i) : Prop :=
  ∃ (j : I) (h : i ≤ j) (b : D.Coeff j), ∀ σ : D.Gal j,
    D.reduction j (b⁻¹ * D.extend h (c (D.restrict h σ)) * D.act j σ b) = 1

def ResidueLangCorrection : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G : AffineAlgebraicGroup k)
    (S : Subgroup (GeometricPoints G.val.X)),
    Parameterization G S → ConnectedGenerators G S →
    ∀ (I : Type u) [Preorder I] [IsDirectedOrder I]
      (D : CoefficientStages G S I) (i : I) (c : D.Gal i → D.Coeff i),
      (∀ σ τ, c (σ * τ) = c σ * D.act i σ (c τ)) →
      CorrectsAtLargerStage D i c

end

end LinearAlgebraicGroups.Specs.RamifiedExceptionalResidueCorrection
