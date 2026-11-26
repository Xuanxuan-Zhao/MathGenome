import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AffineTorsorDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Algebra.Pi

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SmoothTorsors

open Fppf LinearAlgebraicGroups.Descent.NonabelianCohomology

local notation "GroupPoints" => _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points

noncomputable section

variable {k : Type u} [Field k]
section

variable (k) (S : Type u) [CommRing S] [Algebra k S]

/-- The field-valued test object in the slice used by the fppf torsor interface. -/
abbrev fieldExtensionTest : Over (fieldBase k) :=
  Over.mk (Over.homMk
    (((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k S))).hom) (Category.comp_id _))

variable {k S}

/-- Restriction of test objects along a homomorphism of commutative
algebras, with the contravariance of Spec. -/
def fieldExtensionMap {R : Type u} [CommRing R] [Algebra k R] (f : R →ₐ[k] S) :
    fieldExtensionTest k S ⟶ fieldExtensionTest k R :=
  Over.homMk ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op)
    (Over.mkIdTerminal.hom_ext _ _)

end

section

variable (k) (S : Type u) [Field S] [Algebra k S]

/-- The map of test objects associated to a field automorphism. -/
abbrev fieldExtensionAut (σ : S ≃ₐ[k] S) :
    fieldExtensionTest k S ⟶ fieldExtensionTest k S :=
  fieldExtensionMap σ.toAlgHom

variable {k S}

/-- Galois cocycles in the shared discrete group of points. -/
abbrev GaloisCocycle (H : GroupScheme k) :=
  @Cocycle (S ≃ₐ[k] S) (GroupPoints k S H.X) _ (krullTopology k S) _ ⊥
    (pointAction k S H.X)

/-- The defining equation for the cocycle of a section of a right torsor. -/
def IsCocycleOf {H : GroupScheme k} (P : FppfTorsor (fieldBase k) H)
    (p : P.val.Section (fieldExtensionTest k S)) (a : GaloisCocycle (S := S) H) : Prop :=
  ∀ σ, P.val.res (fieldExtensionAut k S σ) p = P.val.act p ⟨a σ⟩

end

/-- Effective twisting over a finite Galois splitting field. -/
def FiniteRealization : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (H : AffineAlgebraicGroup k) (a : GaloisCocycle (S := K) H.val),
    ∃ (P : FppfTorsor (fieldBase k) H.val) (p : P.val.Section (fieldExtensionTest k K)),
      IsCocycleOf P p a

/-- Two pointed torsors with equal finite descent data are isomorphic over
the base field. -/
def FiniteIsomorphism : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (H : AffineAlgebraicGroup k) (P Q : FppfTorsor (fieldBase k) H.val)
    (p : P.val.Section (fieldExtensionTest k K)) (q : Q.val.Section (fieldExtensionTest k K))
    (a : GaloisCocycle (S := K) H.val),
    IsCocycleOf P p a → IsCocycleOf Q q a → Nonempty (RightActionIso P.val Q.val)

/-- The classifying bijection sends the class of each right fppf torsor to
the cocycle of any of its separable-closure points. The neutral class consists
of torsors with a rational point. -/
def Classification : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (H : AffineAlgebraicGroup k), Smooth H.val.X.hom →
    ∃ e : H1fppf k H.val ≃ groupH1 k H.val.X S,
      (∀ hG, e (neutralClass hG) = groupBasepoint k H.val.X S) ∧
      ∀ (P : FppfTorsor (fieldBase k) H.val),
        (e (Quotient.mk _ P) = groupBasepoint k H.val.X S ↔
          Nonempty (P.val.Section (fieldTest k))) ∧
        (∃ p : P.val.Section (fieldExtensionTest k S),
          ∃ a : GaloisCocycle (S := S) H.val, IsCocycleOf P p a) ∧
        ∀ (p : P.val.Section (fieldExtensionTest k S))
          (a : GaloisCocycle (S := S) H.val), IsCocycleOf P p a →
          e (Quotient.mk _ P) =
            @classOf (S ≃ₐ[k] S) (GroupPoints k S H.val.X) _ (krullTopology k S) _ ⊥
              (pointAction k S H.val.X) a

/-- The forward map on torsor classes, specified by the point formula. -/
def ClassificationMap : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (H : AffineAlgebraicGroup k) (hG : Presieve.IsSheaf (torsorTopology (fieldBase k))
      (groupSections (fieldBase k) H.val ⋙ forget GrpCat)),
    Smooth H.val.X.hom →
    ∃ f : H1fppf k H.val → groupH1 k H.val.X S,
      f (neutralClass hG) = groupBasepoint k H.val.X S ∧
      (∀ P : FppfTorsor (fieldBase k) H.val,
        f (Quotient.mk _ P) = groupBasepoint k H.val.X S ↔
          Nonempty (P.val.Section (fieldTest k))) ∧
      ∀ (P : FppfTorsor (fieldBase k) H.val)
        (p : P.val.Section (fieldExtensionTest k S))
        (a : GaloisCocycle (S := S) H.val), IsCocycleOf P p a →
        f (Quotient.mk _ P) =
          @classOf (S ≃ₐ[k] S) (GroupPoints k S H.val.X) _ (krullTopology k S) _ ⊥
            (pointAction k S H.val.X) a

/-- Smooth right torsors have a separable-closure point. -/
def GeometricPoint : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (H : AffineAlgebraicGroup k) (P : FppfTorsor (fieldBase k) H.val),
    Smooth H.val.X.hom → Nonempty (P.val.Section (fieldExtensionTest k S))

/-- Torsor sections over an algebraic Galois extension are defined at
finite Galois levels. This also applies to nonsmooth torsors. -/
def FinitePoint : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    (H : AffineAlgebraicGroup k) (P : FppfTorsor (fieldBase k) H.val)
    (p : P.val.Section (fieldExtensionTest k S)),
    ∃ (L : FiniteGaloisIntermediateField k S) (q : P.val.Section (fieldExtensionTest k L)),
      P.val.res (fieldExtensionMap L.toIntermediateField.val) q = p

/-- Restriction to a larger field is injective on sections of an affine-group
torsor. -/
def PointRestrictionInjective : Prop :=
  ∀ {k R S : Type u} [Field k] [Field R] [Field S] [Algebra k R] [Algebra k S]
    (H : AffineAlgebraicGroup k) (P : FppfTorsor (fieldBase k) H.val)
    (f : R →ₐ[k] S), Function.Injective (P.val.res (fieldExtensionMap f))

/-- Fixed points over a possibly infinite Galois extension descend to
rational points. -/
def FixedPoint : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    (H : AffineAlgebraicGroup k) (P : FppfTorsor (fieldBase k) H.val)
    (p : P.val.Section (fieldExtensionTest k S)),
    (∀ σ, P.val.res (fieldExtensionAut k S σ) p = p) →
    ∃ q : P.val.Section (fieldExtensionTest k k),
      P.val.res (fieldExtensionMap (Algebra.ofId k S)) q = p

/-- All sections of a right fppf torsor over the separable closure give a
continuous cocycle by taking their unique displacements under Galois. -/
def PointCocycle : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (H : AffineAlgebraicGroup k) (P : FppfTorsor (fieldBase k) H.val)
    (p : P.val.Section (fieldExtensionTest k S)),
    ∃ a : GaloisCocycle (S := S) H.val, IsCocycleOf P p a

/-- A change of point produces the cohomology relation from the source. -/
def ChangeOfPoint : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {H : GroupScheme k} (P : FppfTorsor (fieldBase k) H)
    {p q : P.val.Section (fieldExtensionTest k S)} {a b : GaloisCocycle (S := S) H},
    IsCocycleOf P p a → IsCocycleOf P q b →
    ∃ t : GroupPoints k S H.X,
      ∀ σ, b σ = t⁻¹ * a σ * pointAction k S H.X σ t

section DoubleOverlap

open scoped TensorProduct

/-- Coordinate map for the automorphism graphs in the self-product of a
finite Galois cover, sending x ⊗ y to the family x * σ y. -/
def galoisTensorMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (K ⊗[k] K) →ₐ[K] (Gal(K/k) → K) :=
  AlgHom.pi (fun σ ↦ AlgHom.liftEquiv k K K K σ.toAlgHom)

/-- The graphs of the automorphisms give the finite decomposition of the
double overlap. -/
def GaloisTensorComparison : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K],
    Function.Bijective (galoisTensorMap k K)

end DoubleOverlap

/-- The affine k-scheme x^n = a, as an object of the common fppf site. -/
abbrev powerFiber (n : ℕ) (a : kˣ) : Over (fieldBase k) :=
  fieldExtensionTest k (AdjoinRoot (Polynomial.X ^ n - Polynomial.C (a : k)))

/-- Global functions on a test scheme, with the algebra structure from its
map to the field spectrum. -/
abbrev testFunctions (T : SchemeOver k) := ((algΓ (CommRingCat.of k)).obj T).unop

/-- Evaluate the universal root at a point of the power fiber. -/
def rootCoordinate {n : ℕ} {a : kˣ} {T : SchemeOver k} (x : T ⟶ (powerFiber n a).left) :
    testFunctions T :=
  (((algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv T
    (op (CommAlgCat.of k (AdjoinRoot (Polynomial.X ^ n - Polynomial.C (a : k)))))).symm
      x).unop.hom (AdjoinRoot.root _)

/-- The scheme of pth roots of a non-power is an fppf torsor under the
group scheme of pth roots of unity, with the multiplication action. -/
def PowerFiberTorsor : Prop :=
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (a : kˣ) (_ : ∀ x : k, x ^ p ≠ (a : k)),
    ∃ (H : GroupScheme k) (i : H.X ≅ (powerFiber p (1 : kˣ)).left)
      (A : SchemeRightAction (powerFiber p a) H),
      IsTorsor (representedAction A) ∧
      (∀ (T : SchemeOver k) (g h : T ⟶ H.X),
        rootCoordinate ((1 : T ⟶ H.X) ≫ i.hom) = 1 ∧
        rootCoordinate (a := (1 : kˣ)) ((g * h) ≫ i.hom) =
          rootCoordinate (g ≫ i.hom) * rootCoordinate (h ≫ i.hom)) ∧
      ∀ (T : Over (fieldBase k)) (x : T ⟶ powerFiber p a)
        (g : (groupSections (fieldBase k) H).obj (op T)),
        rootCoordinate ((actionPair x g.down ≫ A.action).left) =
          rootCoordinate x.left * rootCoordinate (T := T.left) (g.down ≫ i.hom)

/-- The characteristic-p power fiber of a non-power has no
separable-closure point. -/
def PowerFiberNoPoint : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (p : ℕ) [Fact p.Prime] [CharP k p] (a : kˣ) (_ : ∀ x : k, x ^ p ≠ (a : k)),
    IsEmpty (fieldExtensionTest k S ⟶ powerFiber p a)

end

end LinearAlgebraicGroups.Specs.SmoothTorsors
