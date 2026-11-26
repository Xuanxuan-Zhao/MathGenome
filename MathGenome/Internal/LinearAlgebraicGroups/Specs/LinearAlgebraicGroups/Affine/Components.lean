import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups
namespace Specs

variable {k : Type u} [Field k]

/-- The quotient map and the identity component, with its induced scheme structure. -/
structure ComponentQuotient {G : GroupScheme k} (Q H : GroupScheme k)
    (q : G ⟶ Q) (i : H ⟶ G) : Prop where
  finite : IsFinite Q.X.hom
  etale : Etale Q.X.hom
  flat : Flat q.hom.hom.left
  surjective : Surjective q.hom.hom.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation q.hom.hom.left
  connectedFibers : GeometricallyConnected q.hom.hom.left
  openImmersion : IsOpenImmersion i.hom.hom.left
  closedImmersion : IsClosedImmersion i.hom.hom.left
  normal : IsNormalSubgroup i
  geometricallyConnected : GeometricallyConnected H.X.hom
  identityComponent :
    Set.range i.hom.hom.left = connectedComponent (η[G.X].left
      (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))))
  kernel : IsPullback i.hom.hom.left H.X.hom q.hom.hom.left η[Q.X].left
  universal : ∀ (E : GroupScheme k), Etale E.X.hom →
    ∀ f : G ⟶ E, ∃! g : Q ⟶ E, q ≫ g = f

/-- The scalar action on the underlying base-changed scheme is induced by
the inverse field automorphism on the scalar factor. -/
noncomputable def galoisBaseChangeMap (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOver k) (σ : Gal(K/k)) :
    ((baseChange k K).obj X).left ⟶ ((baseChange k K).obj X).left := by
  let r := (testSpec k).map (CommAlgCat.ofHom σ.symm.toAlgHom).op
  let a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) := r.left
  have ha : a ≫ fieldSpecMap k K = fieldSpecMap k K := Over.w r
  exact pullback.lift (pullback.fst X.hom (fieldSpecMap k K))
    (pullback.snd X.hom (fieldSpecMap k K) ≫ a) (by
      rw [Category.assoc, ha, pullback.condition])

/-- Over a separably closed extension the points of the finite étale quotient index
the geometric connected components. An algebraic closure is included in this statement. -/
def ComponentPoints {G Q : GroupScheme k} (q : G ⟶ Q) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [IsSepClosed K],
    let E := (groupBaseChange k K).obj Q
    let X := (groupBaseChange k K).obj G
    let p := (groupBaseChange k K).map q
    let y := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of K)))
    ∃ e : ConnectedComponents X.X.left ≃ Points E.X (.of K K),
      (∀ x : X.X.left, (e (ConnectedComponents.mk x)).left y = p.hom.hom.left x) ∧
      (∀ c, let i := pullback.fst p.hom.hom.left (e c).left
        IsOpenImmersion i ∧ IsClosedImmersion i ∧
          Set.range i = ConnectedComponents.mk ⁻¹' {c}) ∧
      (∀ z : (X.X ⊗ X.X).left,
        e (ConnectedComponents.mk (μ[X.X].left z)) =
          e (ConnectedComponents.mk ((fst X.X X.X).left z)) *
          e (ConnectedComponents.mk ((snd X.X X.X).left z))) ∧
      ∃ a : ConnectedComponents X.X.left ≃ Points Q.X (.of k K),
        (∀ c, a c = baseChangePoint k K Q.X (.of K K) (e c)) ∧
        ∀ (σ : Gal(K/k)) (x : X.X.left),
          a (ConnectedComponents.mk (galoisBaseChangeMap K G.X σ x)) =
            mapPoints (CommAlgCat.ofHom σ.toAlgHom) (a (ConnectedComponents.mk x))

/-- The absolute Galois action is the canonical scalar action on the points of the
component group. This point set carries the discrete topology. -/
def ComponentGalois (Q : GroupScheme k) : Prop :=
  let K := SeparableClosure k
  let P := Points Q.X (.of k K)
  letI : TopologicalSpace P := ⊥
  let act (σ : Gal(K/k)) (p : P) := mapPoints (CommAlgCat.ofHom σ.toAlgHom) p
  Finite P ∧ Continuous (fun s : Gal(K/k) × P ↦ act s.1 s.2) ∧
    (∀ p, act 1 p = p) ∧
    (∀ σ τ p, act (σ * τ) p = act σ (act τ p)) ∧
    ∀ σ p q, act σ (p * q) = act σ p * act σ q

/-- The scheme construction used to obtain the component group from an affine
scheme of finite type. Its geometrically connected fibers retain their scheme
structure. -/
def AffineComponentQuotientsExist : Prop :=
  ∀ (k : Type u) [Field k] (X : SchemeOver k), IsAffine X.left →
    LocallyOfFiniteType X.hom →
    ∃ (Y : SchemeOver k) (q : X ⟶ Y), IsFinite Y.hom ∧ Etale Y.hom ∧
      Flat q.left ∧ QuasiCompact q.left ∧ UniversallyOpen q.left ∧
      GeometricallyConnected q.left

def IdentityComponentAndQuotient : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k),
    ∃ (Q H : GroupScheme k) (q : G.val ⟶ Q) (i : H ⟶ G.val),
      ComponentQuotient Q H q i ∧ ComponentPoints q ∧ ComponentGalois Q ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        ComponentQuotient ((groupBaseChange k K).obj Q) ((groupBaseChange k K).obj H)
          ((groupBaseChange k K).map q) ((groupBaseChange k K).map i)

end Specs
end LinearAlgebraicGroups
