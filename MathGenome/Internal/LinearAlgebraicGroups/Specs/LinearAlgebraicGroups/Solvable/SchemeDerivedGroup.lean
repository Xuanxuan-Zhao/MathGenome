import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Commutator.Basic

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SchemeDerivedGroup

noncomputable section

variable {k : Type u} [Field k]

/-- The commutator morphism on a pair of homomorphisms to the ambient group. -/
def commutatorMap {G A B : GroupScheme k} (a : A ⟶ G) (b : B ⟶ G) :
    A.X ⊗ B.X ⟶ G.X :=
  let x := fst A.X B.X ≫ a.hom.hom
  let y := snd A.X B.X ≫ b.hom.hom
  x * y * x⁻¹ * y⁻¹

/-- A morphism factors through a closed subgroup as a morphism of schemes over the field. -/
def FactorsThrough {G : GroupScheme k} (H : ClosedSubgroup G) {X : SchemeOver k}
    (f : X ⟶ G.X) : Prop :=
  f ∈ SubgroupSections H X

/-- Inclusion of closed subgroups is factorization in the category of group schemes. -/
def IsSubgroupOf {G : GroupScheme k} (H N : ClosedSubgroup G) : Prop :=
  ∃ j : H.group ⟶ N.group, j ≫ N.inclusion = H.inclusion

/-- The least closed normal subgroup containing a morphism of schemes over the field. -/
def IsNormalClosure {G : GroupScheme k} {X : SchemeOver k} (f : X ⟶ G.X)
    (D : ClosedSubgroup G) : Prop :=
  IsNormalSubgroup D.inclusion ∧ FactorsThrough D f ∧
    ∀ (N : ClosedSubgroup G), IsNormalSubgroup N.inclusion → FactorsThrough N f →
      IsSubgroupOf D N

def IsDerivedSubgroup {G : GroupScheme k} (D : ClosedSubgroup G) : Prop :=
  IsNormalClosure (commutatorMap (𝟙 G) (𝟙 G)) D

/-- Commutativity is required on sections over every scheme over the base field. -/
def IsCommutative (G : GroupScheme k) : Prop :=
  ∀ (T : SchemeOver k) (x y : T ⟶ G.X), x * y = y * x

/-- The quotient by a closed normal subgroup, with the original right-coset projection. -/
def RepresentsQuotient {G Q : GroupScheme k} (D : ClosedSubgroup G) (q : G ⟶ Q) : Prop :=
  ∃ e : rightQuotientSheaf D ≅ schemeFppfSheaf Q.X,
    rightQuotientProjection D ≫ e.hom = (fppfOver k).uliftYoneda.map q.hom.hom

/-- Terms of the derived series, characterized up to isomorphism by successive derived
subgroups of the preceding term. -/
inductive DerivedSeries (G : GroupScheme k) : ℕ → GroupScheme k → Prop
  | zero : DerivedSeries G 0 G
  | succ {n H} (prev : DerivedSeries G n H) (D : ClosedSubgroup H)
      (derived : IsDerivedSubgroup D) : DerivedSeries G (n + 1) D.group

/-- The derived series reaches the trivial group scheme. -/
def IsSolvable (G : GroupScheme k) : Prop :=
  ∃ (n : ℕ) (H : GroupScheme k), DerivedSeries G n H ∧
    Nonempty (H ≅ Grp.trivial (SchemeOver k))

/-- A finite subnormal series with successive fppf quotients the additive or
multiplicative group over the displayed field. -/
inductive IsSplitSolvable : GroupScheme k → Prop
  | trivial {G} (e : Nonempty (G ≅ Grp.trivial (SchemeOver k))) : IsSplitSolvable G
  | step {G} (D : ClosedSubgroup G) (normal : IsNormalSubgroup D.inclusion)
      (prev : IsSplitSolvable D.group) (Q : AffineAlgebraicGroup k) (q : G ⟶ Q.val)
      (quotient : RepresentsQuotient D q)
      (factor : Nonempty ((groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k) ∨
        Nonempty ((groupPointsFunctor k).obj Q.val ≅ StandardGroups.multiplicativePoints k)) :
      IsSplitSolvable G

/-- The lower central series takes successive normal closures of the commutators
of the ambient group with the current term. -/
inductive LowerCentralSeries (G : GroupScheme k) : ℕ → ClosedSubgroup G → Prop
  | zero (D : ClosedSubgroup G) (iso : IsIso D.inclusion) : LowerCentralSeries G 0 D
  | succ {n H} (prev : LowerCentralSeries G n H) (D : ClosedSubgroup G)
      (generated : IsNormalClosure (commutatorMap (𝟙 G) H.inclusion) D) :
      LowerCentralSeries G (n + 1) D

def CommutatorMapType :=
  ∀ {k : Type u} [Field k] {G A B : GroupScheme k}, (A ⟶ G) → (B ⟶ G) →
    (A.X ⊗ B.X ⟶ G.X)

def IsDerivedSubgroupType :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k}, ClosedSubgroup G → Prop

def GroupPredicateType := ∀ {k : Type u} [Field k], GroupScheme k → Prop

def DerivedSeriesType :=
  ∀ {k : Type u} [Field k] (_G : GroupScheme k), ℕ → GroupScheme k → Prop

def LowerCentralSeriesType :=
  ∀ {k : Type u} [Field k] (G : GroupScheme k), ℕ → ClosedSubgroup G → Prop

def IsSplitSolvableValue : GroupPredicateType.{u} := @IsSplitSolvable

def DerivedSeriesValue : DerivedSeriesType.{u} := @DerivedSeries

def LowerCentralSeriesValue : LowerCentralSeriesType.{u} := @LowerCentralSeries

def NormalClosureExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) {X : SchemeOver k}
    (f : X ⟶ G.val.X), ∃ D : ClosedSubgroup G.val, IsNormalClosure f D

def DerivedSubgroupExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    ∃ D : ClosedSubgroup G.val, IsDerivedSubgroup D

def Abelianization : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (D : ClosedSubgroup G.val),
    IsDerivedSubgroup D →
    ∃ (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsSchemeKernel q D ∧ RepresentsQuotient D q ∧ IsCommutative Q.val ∧
      ∀ (L : AffineAlgebraicGroup k), IsCommutative L.val → ∀ f : G.val ⟶ L.val,
        ∃! g : Q.val ⟶ L.val, q ≫ g = f

def CommutatorSubgroupLe : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (D : ClosedSubgroup G),
    IsDerivedSubgroup D →
    ∀ T : SchemeOver k, commutator (T ⟶ G.X) ≤ SubgroupSections D T

def DerivedSeriesExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (n : ℕ),
    ∃ H : AffineAlgebraicGroup k, DerivedSeries G.val n H.val

def DerivedSubgroupConnected : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [ConnectedSpace G.val.X.left]
    (D : ClosedSubgroup G.val), IsDerivedSubgroup D → ConnectedSpace D.group.X.left

def LowerCentralSeriesConnected : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [ConnectedSpace G.val.X.left]
    {n : ℕ} {D : ClosedSubgroup G.val}, LowerCentralSeries G.val n D →
    ConnectedSpace D.group.X.left

def LowerCentralSeriesExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (n : ℕ),
    ∃ D : ClosedSubgroup G.val, LowerCentralSeries G.val n D

def DerivedSubgroupOverAlgClosed : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (D : ClosedSubgroup G.val), IsDerivedSubgroup D →
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    Smooth D.group.X.hom ∧ ConnectedSpace D.group.X.left ∧
      SubgroupSections D (𝟙_ (SchemeOver k)) = commutator ((𝟙_ (SchemeOver k)) ⟶ G.val.X)

def LowerCentralSeriesSmoothConnected : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G : AffineAlgebraicGroup k)
    (n : ℕ) (D : ClosedSubgroup G.val), LowerCentralSeries G.val n D →
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    Smooth D.group.X.hom ∧ ConnectedSpace D.group.X.left

end

end LinearAlgebraicGroups.Specs.SchemeDerivedGroup
