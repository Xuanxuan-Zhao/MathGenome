import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalSteinbergSection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalTwistedTraceComparison

open AdjointRepresentation (GroupPoints)
open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints restrictIso
  RelativeAut groupSections automorphisms innerAut)
open ExceptionalSteinbergSection (IsGeometricImage)
open GeometricRadicals (IsReductive)
open Pinning (PinnedGroup AttachedDatum SimpleRoot)
open QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction)
open RelativeFormComparison (fieldTest transportedAut IsInduced)
open RootGroups (AdditiveLine)
open RootWeightAction (Representation)
open SteinbergPinnedDescent (coefficientAction comparisonOnPoints pinnedAction diagramPermutation
  permuteParameters traceValue)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle pointAction)

noncomputable section

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

/-- Continuous cocycles of the actual point group over the chosen separable closure. -/
abbrev PointCocycle (G : GroupScheme k) :=
  @Cocycle (Gal(S/k)) (GroupPoints G (CommAlgCat.of k S)) _
    (krullTopology k S) _ ⊥ (pointAction k S G.X)

abbrev InnerMap {G : AffineAlgebraicGroup k} (Q : AdjointQuotient G) :=
  groupSections Q.quotient.val ⟶ automorphisms G.val

/-- The action is induced by conjugation before passage to the full central quotient. -/
def ActsByConjugation {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G}
    (inn : InnerMap Q) : Prop :=
  ∀ (U : SchemeOver k) (g : U ⟶ G.val.X),
    inn.app (op U) ⟨g ≫ Q.projection.hom.hom⟩ = innerAut g

/-- Evaluate an automorphism of the relative point functor on the extension field itself. -/
abbrev evalAut {G : GroupScheme k} (a : RelativeAut G (fieldTest k S)) :
    MulAut (GroupPoints G (CommAlgCat.of k S)) :=
  comparisonOnPoints a.asIso

def adjointAction {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G}
    (inn : InnerMap Q) (q : GroupPoints Q.quotient.val (CommAlgCat.of k S)) :
    MulAut (GroupPoints G.val (CommAlgCat.of k S)) :=
  evalAut (inn.app (op (fieldTest k S)) ⟨q⟩)

abbrev extendPoint {G : GroupScheme k} (x : GroupPoints G (CommAlgCat.of k k)) :
    GroupPoints G (CommAlgCat.of k S) :=
  mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x

def projectionOnPoints {G : AffineAlgebraicGroup k} (Q : AdjointQuotient G) :
    GroupPoints G.val (CommAlgCat.of k S) →*
      GroupPoints Q.quotient.val (CommAlgCat.of k S) :=
  ((yonedaGrp.map Q.projection).app (op (fieldTest k S))).hom

/-- A reductive form with the specified inner cocycle, using relative
trivializations oriented from the reference group to the descended group. -/
structure Twist {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G}
    (a : PointCocycle (S := S) Q.quotient.val) where
  group : AffineAlgebraicGroup k
  reductive : IsReductive group
  trivialization : relativePoints G.val (fieldTest k S) ≅ relativePoints group.val (fieldTest k S)
  inner : InnerMap Q
  onLift : ActsByConjugation inner
  innerInjective : ∀ U, Function.Injective (inner.app U)
  cocycle_eq : ∀ σ, transportedAut k S trivialization σ =
    inner.app (op (fieldTest k S)) ⟨a.val σ⟩
  fixed : ∀ (x : GroupPoints group.val (CommAlgCat.of k k)) (σ : Gal(S/k)),
    let y := (comparisonOnPoints trivialization).symm (extendPoint x)
    adjointAction inner (a.val σ) (coefficientAction S G.val σ y) = y

def AdjointTwisting : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (Q : AdjointQuotient G) (a : PointCocycle (S := S) Q.quotient.val),
      Nonempty (Twist a)

/-- Cocycle pushforward along the actual adjoint projection, with the
conjugation formula on points for its induced twist. -/
def SimplyConnectedTwisting : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (Q : AdjointQuotient G) (b : PointCocycle (S := S) G.val),
      ∃ (a : PointCocycle (S := S) Q.quotient.val) (T : Twist a),
        (∀ σ, a.val σ = projectionOnPoints Q (b.val σ)) ∧
        ∀ (x : GroupPoints T.group.val (CommAlgCat.of k k)) (σ : Gal(S/k)),
          let y := (comparisonOnPoints T.trivialization).symm (extendPoint x)
          b.val σ * coefficientAction S G.val σ y * (b.val σ)⁻¹ = y

/-- Changing the reference coordinates by the pinned comparison gives the
pinned diagram action composed with the ordinary coefficient action. -/
def PinnedActionComparison : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q₀ : AdjointQuotient P.pair.G}
    {E : SplitSequence P D l Q₀}
    {ω : @Cocycle (Gal(S/k)) (Aut D.toBased) _ (krullTopology k S) _ ⊥
      (trivialOuterAction (k := k) (S := S) D.toBased)}
    (V : PinnedRepresentative (S := S) E ω) (σ : Gal(S/k))
    (y : GroupPoints P.pair.G.val (CommAlgCat.of k S)),
    comparisonOnPoints V.trivialization (pinnedAction S (l (ω σ)).asIso.hom σ y) =
      coefficientAction S V.model.val.val σ (comparisonOnPoints V.trivialization y)

/-- The adjoint action, expressed in split coordinates, preserves the trace
of every rational representation of the split group. -/
def AdjointTraceInvariant : Prop :=
  ∀ {k S I : Type u} [Field k] [Field S] [Algebra k S] [Algebra.IsAlgebraic k S]
    [Fintype I] [DecidableEq I] {A : AdditiveLine k} {P : PinnedGroup A}
    {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G}
    (e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (inn : InnerMap Q), ActsByConjugation inn →
    ∀ (ρ : Representation P.pair.G.val I)
      (q : GroupPoints Q.quotient.val (CommAlgCat.of k S))
      (y : GroupPoints P.pair.G.val (CommAlgCat.of k S)),
      traceValue ρ _ ((comparisonOnPoints e).symm
        (adjointAction inn q (comparisonOnPoints e y))) = traceValue ρ _ y

/-- Each tuple of rational representation traces with the indicated
permutation and field action is fixed on a rational point of the twist. -/
def FixedTraceTuple : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q₀ : AdjointQuotient P.pair.G}
    {E : SplitSequence P D l Q₀}
    {ω : @Cocycle (Gal(S/k)) (Aut D.toBased) _ (krullTopology k S) _ ⊥
      (trivialOuterAction (k := k) (S := S) D.toBased)}
    (V : PinnedRepresentative (S := S) E ω)
    {Q : AdjointQuotient V.model.val} {a : PointCocycle (S := S) Q.quotient.val}
    (T : Twist a) (x : GroupPoints T.group.val (CommAlgCat.of k k))
    (I : SimpleRoot P.pair → Type u) [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    (ρ : ∀ i, Representation P.pair.G.val (I i)),
    let tr : GroupPoints P.pair.G.val (CommAlgCat.of k S) → SimpleRoot P.pair → S :=
      fun g i ↦ traceValue (ρ i) _ g
    let permute := fun σ : Gal(S/k) ↦ permuteParameters (diagramPermutation D (ω σ)) σ
    let y := (comparisonOnPoints V.trivialization).symm
      ((comparisonOnPoints T.trivialization).symm (extendPoint x))
    (∀ σ g, tr (pinnedAction S (l (ω σ)).asIso.hom σ g) = permute σ (tr g)) →
    ∀ σ, permute σ (tr y) = tr y

/-- The projection from the direct scalar extension over the algebraic
closure to the scalar extension over the splitting field. -/
def extensionProjection (f : S →ₐ[k] AlgebraicClosure k) (X : SchemeOver k) :
    ((baseChange k (AlgebraicClosure k)).obj X).left ⟶ ((baseChange k S).obj X).left :=
  let a := Spec.map (CommRingCat.ofHom f.toRingHom)
  pullback.lift (pullback.fst X.hom (fieldSpecMap k (AlgebraicClosure k)))
    (pullback.snd X.hom (fieldSpecMap k (AlgebraicClosure k)) ≫ a) (by
      have ha : a ≫ fieldSpecMap k S = fieldSpecMap k (AlgebraicClosure k) := by
        change Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp]
        congr 1
        ext x
        exact f.commutes x
      rw [Category.assoc, ha]
      exact pullback.condition)

/-- The scheme comparison and its restriction along the embedding of the
splitting field induce compatible isomorphisms on actual field-valued points. -/
def GeometricComparison : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {G H : GroupScheme k} (f : S →ₐ[k] AlgebraicClosure k)
    (e : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S)),
    let K := AlgebraicClosure k
    let fieldArrow := (testSpec k).map (CommAlgCat.ofHom f).op
    ∃ (i : (groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H)
      (j : (groupBaseChange k K).obj G ≅ (groupBaseChange k K).obj H),
      IsInduced k S i e ∧ IsInduced k K j (restrictIso fieldArrow e) ∧
      j.hom.hom.hom.left ≫ extensionProjection f H.X =
        extensionProjection f G.X ≫ i.hom.hom.hom.left ∧
      ∀ (x : GroupPoints G (CommAlgCat.of k S))
        (x' : GroupPoints ((groupBaseChange k K).obj G) (CommAlgCat.of K K)),
        IsGeometricImage f x x' →
        IsGeometricImage f (comparisonOnPoints e x)
          ((((groupPointsFunctor K).map j.hom).app (CommAlgCat.of K K)).hom x')

end

end LinearAlgebraicGroups.Specs.ExceptionalTwistedTraceComparison
