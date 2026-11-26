import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.LieBracket
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.CategoryTheory.FinCategory.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs

noncomputable section

/-- Compatible tangent vectors on a diagram lift uniquely on its scheme-theoretic limit.
The brackets on the limit and on the members of the diagram are the intrinsic brackets. -/
def LieLimitComparison : Prop :=
  ∀ (k : Type u) [Field k] (J : Type u) [SmallCategory J] [FinCategory J]
    (F : J ⥤ GroupScheme k) (c : Cone F),
    IsLimit c → [IsAffine c.pt.X.left] → [∀ j, IsAffine (F.obj j).X.left] →
    (∀ (p : Lie k c.pt) ⦃i j⦄ (f : i ⟶ j),
      mapPointKernel (F.map f) (mapPointKernel (c.π.app i) p) =
        mapPointKernel (c.π.app j) p) ∧
    (∀ (x : ∀ j, Lie k (F.obj j)),
      (∀ ⦃i j⦄ (f : i ⟶ j), mapPointKernel (F.map f) (x i) = x j) →
      ∃! p : Lie k c.pt, ∀ j, mapPointKernel (c.π.app j) p = x j) ∧
    (∀ j (p q : Lie k c.pt),
      mapPointKernel (c.π.app j) (p + q) =
        mapPointKernel (c.π.app j) p + mapPointKernel (c.π.app j) q) ∧
    (∀ j (s : k) p,
      mapPointKernel (c.π.app j) (scalePointKernel c.pt s p) =
        scalePointKernel (F.obj j) s (mapPointKernel (c.π.app j) p)) ∧
    ∀ j p q,
      mapPointKernel (c.π.app j) (intrinsicLieBracket k c.pt p q) =
        intrinsicLieBracket k (F.obj j) (mapPointKernel (c.π.app j) p)
          (mapPointKernel (c.π.app j) q)

/-- The comparison for an actual pullback square, including intersections of closed subgroups. -/
def LiePullbackComparison : Prop :=
  ∀ (k : Type u) [Field k] {P G H L : GroupScheme k}
    {p : P ⟶ G} {q : P ⟶ L} {f : G ⟶ H} {g : L ⟶ H},
    IsPullback p q f g → ∀ (x : Lie k G) (y : Lie k L),
      mapPointKernel f x = mapPointKernel g y →
      ∃! z : Lie k P, mapPointKernel p z = x ∧ mapPointKernel q z = y

/-- In the scheme-theoretic kernel square the differential of the inclusion
identifies the identity tangent space with the kernel of the differential. -/
def LieKernelComparison : Prop :=
  ∀ (k : Type u) [Field k] {N G H T : GroupScheme k}
    {i : N ⟶ G} {t : N ⟶ T} {f : G ⟶ H} {e : T ⟶ H},
    IsTerminal T → IsPullback i t f e →
      Function.Injective (mapPointKernel i) ∧
      Set.range (mapPointKernel i) = {x | mapPointKernel f x = 0}

/-- Pullbacks of affine algebraic groups remain affine and of finite type. -/
def AffineAlgebraicPullback : Prop :=
  ∀ (k : Type u) [Field k] (G H L : AffineAlgebraicGroup k)
    (f : G.val ⟶ H.val) (g : L.val ⟶ H.val),
    let P := pullback f g
    IsAffine P.X.left ∧ LocallyOfFiniteType P.X.hom ∧ QuasiCompact P.X.hom

/-- The differential of the inclusion of a scheme-theoretic intersection
identifies its Lie algebra with the intersection inside the ambient Lie algebra. -/
def LieClosedIntersection : Prop :=
  ∀ (k : Type u) [Field k] {P G H L : GroupScheme k}
    {p : P ⟶ G} {q : P ⟶ L} {f : G ⟶ H} {g : L ⟶ H},
    IsClosedImmersion f.hom.hom.left → IsClosedImmersion g.hom.hom.left →
    IsPullback p q f g →
      Function.Injective (mapPointKernel (p ≫ f)) ∧
      Set.range (mapPointKernel (p ≫ f)) =
        Set.range (mapPointKernel f) ∩ Set.range (mapPointKernel g)

/-- The same kernel comparison for the Hopf quotient defining the scheme kernel in A04. -/
def LieHopfKernel : Prop :=
  ∀ (k : Type u) [Field k] {A B : HopfAlgebraCategory k} (a : B ⟶ A)
    [(kernelIdeal a).IsHopfIdeal k],
    let i := specGroupMap (hopfQuotientMap A (kernelIdeal a))
    Function.Injective (mapPointKernel i) ∧
      Set.range (mapPointKernel i) = {x | mapPointKernel (specGroupMap a) x = 0}

section Matrix

open StandardGroups

/-- The tangent coordinate of an invertible matrix is its entrywise coefficient of ε. -/
def glTangentCoefficient {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    {G : GroupScheme k} (a : (groupPointsFunctor k).obj G ≅ generalLinearPoints k ι)
    (p : Lie k G) : Matrix ι ι k :=
  fun i j => (((a.hom.app (CommAlgCat.of k (DualNumber k))).hom p.toMul.val).val i j).snd

/-- The same tangent coordinate on the determinant-one matrix functor. -/
def slTangentCoefficient {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    {G : GroupScheme k} (a : (groupPointsFunctor k).obj G ≅ specialLinearPoints k ι)
    (p : Lie k G) : Matrix ι ι k :=
  fun i j => (((a.hom.app (CommAlgCat.of k (DualNumber k))).hom p.toMul.val).val i j).snd

def LieGeneralLinearAt (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι]
    (G : AffineAlgebraicGroup k)
    (a : (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k ι)
    (b : IdentityLieStructure G.val) : Prop :=
  letI := b.lieRing
  letI := b.lieAlgebra
  ∃ d : Lie k G.val ≃ₗ[k] Matrix ι ι k,
    (∀ p, d p = glTangentCoefficient a p) ∧
    ∀ p q, d ⁅p, q⁆ = d p * d q - d q * d p

def LieGeneralLinear : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι]
    (G : AffineAlgebraicGroup k)
    (a : (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k ι)
    (b : IdentityLieStructure G.val), LieGeneralLinearAt k ι G a b

def LieSpecialLinearAt (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι]
    (G : AffineAlgebraicGroup k)
    (a : (groupPointsFunctor k).obj G.val ≅ specialLinearPoints k ι)
    (b : IdentityLieStructure G.val) : Prop :=
  letI := b.lieRing
  letI := b.lieAlgebra
  ∃ d : Lie k G.val ≃ₗ[k] LinearMap.ker (Matrix.traceLinearMap ι k k),
    (∀ p, (d p).val = slTangentCoefficient a p) ∧
    ∀ p q, (d ⁅p, q⁆).val = (d p).val * (d q).val - (d q).val * (d p).val

def LieSpecialLinear : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι]
    (G : AffineAlgebraicGroup k)
    (a : (groupPointsFunctor k).obj G.val ≅ specialLinearPoints k ι)
    (b : IdentityLieStructure G.val), LieSpecialLinearAt k ι G a b

end Matrix

section OneDimensional

open StandardGroups

def LieAdditiveGroupAt (k : Type u) [Field k]
    (G : AffineAlgebraicGroup k)
    (a : (groupPointsFunctor k).obj G.val ≅ additivePoints k)
    (b : IdentityLieStructure G.val) : Prop :=
  letI := b.lieRing
  letI := b.lieAlgebra
  ∃ d : Lie k G.val ≃ₗ[k] k,
    (∀ p, d p =
      (Multiplicative.toAdd ((a.hom.app (CommAlgCat.of k (DualNumber k))).hom p.toMul.val)).snd) ∧
    ∀ p q : Lie k G.val, ⁅p, q⁆ = 0

def LieAdditiveGroup : Prop :=
  ∀ (k : Type u) [Field k]
    (G : AffineAlgebraicGroup k)
    (a : (groupPointsFunctor k).obj G.val ≅ additivePoints k)
    (b : IdentityLieStructure G.val), LieAdditiveGroupAt k G a b

def LieMultiplicativeGroupAt (k : Type u) [Field k]
    (G : AffineAlgebraicGroup k)
    (a : (groupPointsFunctor k).obj G.val ≅ multiplicativePoints k)
    (b : IdentityLieStructure G.val) : Prop :=
  letI := b.lieRing
  letI := b.lieAlgebra
  ∃ d : Lie k G.val ≃ₗ[k] k,
    (∀ p, d p = (((a.hom.app (CommAlgCat.of k (DualNumber k))).hom p.toMul.val).val).snd) ∧
    ∀ p q : Lie k G.val, ⁅p, q⁆ = 0

def LieMultiplicativeGroup : Prop :=
  ∀ (k : Type u) [Field k]
    (G : AffineAlgebraicGroup k)
    (a : (groupPointsFunctor k).obj G.val ≅ multiplicativePoints k)
    (b : IdentityLieStructure G.val), LieMultiplicativeGroupAt k G a b

end OneDimensional

end
end LinearAlgebraicGroups.Specs
