import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SmallChainHomology
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
Independent interface for paper.tex 1374–1414, `thm:p202-mv`.

The four theories below use the actual upstream ordinary, augmented/reduced,
and relative complexes. Covers have two members, with a harmless universe lift
of their Boolean indices. No nonemptiness assumptions are imposed, including on
the intersection. In particular reduced homology of the empty intersection
retains the augmentation in degree -1.

The boundary formula uses an arbitrary chain in the direct sum, whose image
in the ambient complex is a cycle. Thus its two components need not be cycles.
The equation with `chainFirst` says exactly `i x = ∂a`, `j x = -∂b`.
`smallRepresentatives` asserts that every class has such a representative.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v w
namespace P202Specs.MayerVietoris
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.SmallChainHomology

/-- Forget the specified subspace, retaining its ambient space and map. -/
def spaceFunctor : Pair.{v} ⥤ TopCat.{v} where
  obj P := P.space
  map f := f.map

/-- The original ordinary and reduced theories, both absolute and relative. -/
inductive Theory
  | ordinary | relative | reduced | reducedRelative
  deriving DecidableEq

def theoryFunctor (R : Type u) [CommRing R] (t : Theory) :
    Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ :=
  match t with
  | .ordinary => spaceFunctor ⋙ ordinaryFunctor R R
  | .relative => relativeFunctor (ordinaryFunctor R R)
  | .reduced => spaceFunctor ⋙ reducedFunctor R R
  | .reducedRelative => relativeFunctor (reducedFunctor R R)

/-- Arbitrary subspace of an arbitrary space, with a two-member open cover. -/
structure CoverPair where
  pair : Pair.{v}
  cover : OpenCover pair.space (ULift.{w} Bool)

abbrev CoverPair.left (C : CoverPair.{v,w}) : Set C.pair.space := C.cover.sets ⟨false⟩
abbrev CoverPair.right (C : CoverPair.{v,w}) : Set C.pair.space := C.cover.sets ⟨true⟩

/-- A piece of the pair has second term `A ∩ B`, expressed in the subtype `B`. -/
def piece (P : Pair.{v}) (B : Set P.space) : Pair.{v} :=
  ⟨TopCat.of B, {x | x.val ∈ P.subspace}⟩

/-- Every open cover by the original sets U and V gives this interface,
with no change to the ambient space or specified subspace. -/
def CoverPair.ofSets (P : Pair.{v}) (U V : Set P.space)
    (hU : IsOpen U) (hV : IsOpen V) (h : U ∪ V = Set.univ) : CoverPair.{v,w} where
  pair := P
  cover := {
    sets := fun i => if i.down then V else U
    isOpen := by intro ⟨b⟩; cases b <;> assumption
    covers := by
      intro x
      have hx : x ∈ U ∪ V := by rw [h]; trivial
      rcases hx with hx | hx
      · exact ⟨⟨false⟩, hx⟩
      · exact ⟨⟨true⟩, hx⟩ }

@[simp] lemma CoverPair.ofSets_left (P : Pair.{v}) (U V : Set P.space)
    (hU : IsOpen U) (hV : IsOpen V) (h : U ∪ V = Set.univ) :
    (CoverPair.ofSets.{v,w} P U V hU hV h).left = U := rfl

@[simp] lemma CoverPair.ofSets_right (P : Pair.{v}) (U V : Set P.space)
    (hU : IsOpen U) (hV : IsOpen V) (h : U ∪ V = Set.univ) :
    (CoverPair.ofSets.{v,w} P U V hU hV h).right = V := rfl

abbrev CoverPair.leftPair (C : CoverPair.{v,w}) := piece C.pair C.left
abbrev CoverPair.rightPair (C : CoverPair.{v,w}) := piece C.pair C.right
abbrev CoverPair.intersectionPair (C : CoverPair.{v,w}) := piece C.pair (C.left ∩ C.right)

def pieceInclusion (P : Pair.{v}) (B : Set P.space) : piece P B ⟶ P where
  map := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  mapsTo := fun _ hx => hx

def pieceMono (P : Pair.{v}) {B D : Set P.space} (h : B ⊆ D) :
    piece P B ⟶ piece P D where
  map := TopCat.ofHom ⟨fun x => ⟨x.val, h x.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  mapsTo := fun _ hx => hx

abbrev CoverPair.toLeft (C : CoverPair.{v,w}) : C.intersectionPair ⟶ C.leftPair :=
  pieceMono C.pair Set.inter_subset_left
abbrev CoverPair.toRight (C : CoverPair.{v,w}) : C.intersectionPair ⟶ C.rightPair :=
  pieceMono C.pair Set.inter_subset_right
abbrev CoverPair.leftInclusion (C : CoverPair.{v,w}) := pieceInclusion C.pair C.left
abbrev CoverPair.rightInclusion (C : CoverPair.{v,w}) := pieceInclusion C.pair C.right

/-- Maps preserve both named cover members and the specified subspace. -/
structure CoverMap (C D : CoverPair.{v,w}) where
  map : C.pair ⟶ D.pair
  left : Set.MapsTo map.map C.left D.left
  right : Set.MapsTo map.map C.right D.right

def pieceMap {P Q : Pair.{v}} (f : P ⟶ Q) {B : Set P.space} {D : Set Q.space}
    (h : Set.MapsTo f.map B D) : piece P B ⟶ piece Q D where
  map := TopCat.ofHom ⟨fun x => ⟨f.map x.val, h x.property⟩,
    (f.map.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  mapsTo := fun _ hx => f.mapsTo hx

def CoverMap.onLeft {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    C.leftPair ⟶ D.leftPair := pieceMap f.map f.left

def CoverMap.onRight {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    C.rightPair ⟶ D.rightPair := pieceMap f.map f.right

def CoverMap.onIntersection {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    C.intersectionPair ⟶ D.intersectionPair :=
  pieceMap f.map (fun _ hx => ⟨f.left hx.1, f.right hx.2⟩)

section Functor
variable {R : Type u} [CommRing R]
  (F : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ)

def middle (C : CoverPair.{v,w}) := F.obj C.leftPair ⊞ F.obj C.rightPair

def chainFirst (C : CoverPair.{v,w}) : F.obj C.intersectionPair ⟶ middle F C :=
  biprod.lift (F.map C.toLeft) (-F.map C.toRight)

def chainSum (C : CoverPair.{v,w}) : middle F C ⟶ F.obj C.pair :=
  biprod.desc (F.map C.leftInclusion) (F.map C.rightInclusion)

def middleMap {C D : CoverPair.{v,w}} (f : CoverMap C D) : middle F C ⟶ middle F D :=
  biprod.map (F.map f.onLeft) (F.map f.onRight)

/-- The direct sum in the displayed homology sequence is the binary biproduct. -/
def homologyMiddle (C : CoverPair.{v,w}) (n : ℤ) :=
  (F.obj C.leftPair).homology n ⊞ (F.obj C.rightPair).homology n

def first (C : CoverPair.{v,w}) (n : ℤ) :
    (F.obj C.intersectionPair).homology n ⟶ homologyMiddle F C n :=
  biprod.lift (homologyMap (F.map C.toLeft) n) (-homologyMap (F.map C.toRight) n)

def sum (C : CoverPair.{v,w}) (n : ℤ) :
    homologyMiddle F C n ⟶ (F.obj C.pair).homology n :=
  biprod.desc (homologyMap (F.map C.leftInclusion) n)
    (homologyMap (F.map C.rightInclusion) n)

def homologyMiddleMap {C D : CoverPair.{v,w}} (f : CoverMap C D) (n : ℤ) :
    homologyMiddle F C n ⟶ homologyMiddle F D n :=
  biprod.map (homologyMap (F.map f.onLeft) n) (homologyMap (F.map f.onRight) n)

/-- A cycle's actual class, with no quotient model substituted for homology. -/
def classOf (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (z : K.X n) (hz : K.d n (n-1) z = 0) : K.homology n :=
  P202Specs.ChainLES.cycleClass K (n-1)
    ((ComplexShape.down ℤ).next_eq' (by simp)) z hz

/-- The connecting arrows are chosen simultaneously for all pairs and covers. -/
abbrev Connecting := ∀ (C : CoverPair.{v,w}) (n : ℤ),
  (F.obj C.pair).homology (n+1) ⟶ (F.obj C.intersectionPair).homology n

/-- Every finite six-term portion, and exactness at the direct sum in every degree. -/
def Exact (δ : Connecting.{u,v,w} F) : Prop :=
  (∀ (C : CoverPair.{v,w}) (n : ℤ),
    (ComposableArrows.mk₅ (first F C (n+1)) (sum F C (n+1)) (δ C n)
      (first F C n) (sum F C n)).Exact) ∧
  ∀ (C : CoverPair.{v,w}) (n : ℤ),
    (ComposableArrows.mk₂ (first F C n) (sum F C n)).Exact

/-- Naturality of every kind of arrow. -/
def Natural (δ : Connecting.{u,v,w} F) : Prop :=
  ∀ (C D : CoverPair.{v,w}) (f : CoverMap C D),
    (∀ n, first F C n ≫ homologyMiddleMap F f n =
      homologyMap (F.map f.onIntersection) n ≫ first F D n) ∧
    (∀ n, sum F C n ≫ homologyMap (F.map f.map) n =
      homologyMiddleMap F f n ≫ sum F D n) ∧
    ∀ n, δ C n ≫ homologyMap (F.map f.onIntersection) n =
      homologyMap (F.map f.map) (n+1) ≫ δ D n

/-- Every ambient homology class admits a representative of the form `a+b`
with `a` supported in U and `b` in V, also in the relative quotient. -/
def SmallRepresentatives : Prop :=
  ∀ (C : CoverPair.{v,w}) (n : ℤ) (z : (F.obj C.pair).X n)
    (hz : (F.obj C.pair).d n (n-1) z = 0),
    ∃ c : (middle F C).X n,
      ∃ hc : (F.obj C.pair).d n (n-1) ((chainSum F C).f n c) = 0,
        classOf.{u,v} (R := R) (F.obj C.pair) n ((chainSum F C).f n c) hc =
          classOf.{u,v} (R := R) (F.obj C.pair) n z hz

/-- The boundary of a split cycle has a unique preimage in the intersection;
that preimage is a cycle. This supplies the cycle condition used by the formula. -/
def BoundaryLifts : Prop :=
  ∀ (C : CoverPair.{v,w}) (n : ℤ) (c : (middle F C).X (n+1)),
    (F.obj C.pair).d (n+1) n ((chainSum F C).f (n+1) c) = 0 →
    ∃! x : (F.obj C.intersectionPair).X n,
      (chainFirst F C).f n x = (middle F C).d (n+1) n c ∧
        (F.obj C.intersectionPair).d n (n-1) x = 0

/-- Positive boundary-of-a-lift convention, for every split representative
and every preimage of its boundary, rather than for a specially chosen lift. -/
def BoundaryFormula (δ : Connecting.{u,v,w} F) : Prop :=
  ∀ (C : CoverPair.{v,w}) (n : ℤ) (c : (middle F C).X (n+1))
    (hc : (F.obj C.pair).d (n+1) n ((chainSum F C).f (n+1) c) = 0)
    (x : (F.obj C.intersectionPair).X n)
    (hx : (chainFirst F C).f n x = (middle F C).d (n+1) n c)
    (hxc : (F.obj C.intersectionPair).d n (n-1) x = 0),
    δ C n (classOf.{u,v} (R := R) (F.obj C.pair) (n+1) ((chainSum F C).f (n+1) c)
      (by rw [add_sub_cancel_right]; exact hc)) = classOf.{u,v} (R := R) (F.obj C.intersectionPair) n x hxc

end Functor

/-- Full original theorem: arbitrary commutative rings, spaces and subspaces,
ordinary and reduced variants, all degrees, the signs, and cover-map naturality.
In the two ordinary theories the long exact sequence has the usual surjective
H₀ endpoint. No conditional upstream premises occur in this target. -/
def mayerVietoris_type : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Theory),
    let F := theoryFunctor.{u,v} R t
    (∃ δ : Connecting.{u,v,w} F,
      Exact F δ ∧ Natural F δ ∧ BoundaryFormula F δ) ∧
    SmallRepresentatives.{u,v,w} F ∧ BoundaryLifts.{u,v,w} F ∧
    ((t = .ordinary ∨ t = .relative) →
      ∀ C : CoverPair.{v,w}, Epi (sum F C 0))

end P202Specs.MayerVietoris
