import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Maps.OpenQuotient

open Set Filter Topology
open scoped Classical RestrictedProduct

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Arithmetic.CompactProductIsolation

section TopologicalGroups

variable {J U : Type*} [Group J] [Group U] [TopologicalSpace J] [TopologicalSpace U]

/-- Elements contracted to the identity by positive powers of a fixed conjugating element. -/
def Contracted (x : J) : Prop :=
  ∃ a : J, Tendsto (fun n : ℕ => a ^ n * x * (a ^ n)⁻¹) atTop (𝓝 1)

/-- The closure of the second projection of the closed subgroup. -/
def secondClosure [IsTopologicalGroup U] (P : Subgroup (J × U)) : Subgroup U :=
  (P.map (MonoidHom.snd J U)).topologicalClosure

/-- The fiber over the identity of the first factor, regarded as a subgroup of the
closure of the second projection. -/
def identityFiber [IsTopologicalGroup U] (P : Subgroup (J × U)) :
    Subgroup (secondClosure P) :=
  P.comap ((MonoidHom.inr J U).comp (secondClosure P).subtype)

/-- The second coordinate of an element of the closed subgroup, in its projected closure. -/
def secondCoordinate [IsTopologicalGroup U] (P : Subgroup (J × U)) : P →* secondClosure P :=
  ((MonoidHom.snd J U).comp P.subtype).codRestrict (secondClosure P) fun p =>
    (P.map (MonoidHom.snd J U)).le_topologicalClosure ⟨p, p.property, rfl⟩

end TopologicalGroups

open AdelicGroups ArithmeticLatticeProjection
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization RationalPoints)

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
variable (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)

/-- The rational diagonal as a set in the actual restricted product outside S. -/
def diagonalSet (S : Finset D.Place) : Set (Adeles D i S) :=
  {x | ∃ g : RationalPoints G, ∀ w : Outside D S, x w = localPoint D i w.1 g}

/-- The adelic diagonal closure outside S. -/
def diagonalClosure (S : Finset D.Place) : Set (Adeles D i S) :=
  closure (diagonalSet D i S)

/-- Include the remaining places in the old set of outside places. -/
def outsideIndex {S T : Finset D.Place} (h : S ⊆ T) (w : Outside D T) : Outside D S :=
  ⟨w.1, fun hw => w.2 (h hw)⟩

theorem outsideIndex_injective {S T : Finset D.Place} (h : S ⊆ T) :
    Function.Injective (outsideIndex D h) :=
  fun _ _ e => Subtype.ext (congrArg (fun w : Outside D S => w.val) e)

/-- Projection of adeles after enlarging the set of omitted places. -/
def forgetOutside {S T : Finset D.Place} (h : S ⊆ T) :
    Adeles D i S →* Adeles D i T :=
  RestrictedProduct.mapAlongMonoidHom _ _ (outsideIndex D h)
    (outsideIndex_injective D h).tendsto_cofinite
    (fun _ => MonoidHom.id _) (Eventually.of_forall fun _ _ hw => hw)

/-- The part of an outside adele at the finite set J. -/
def projectFinite {S J : Finset D.Place} (h : Disjoint J S) :
    Adeles D i S →* FinitePoints D i J where
  toFun x w := x ⟨w.1, (Finset.disjoint_left.mp h w.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Insert the finite product into the restricted product with identity at every other place. -/
def insertFinite (S J : Finset D.Place) (x : FinitePoints D i J) : Adeles D i S := by
  classical
  refine ⟨fun w => if hw : w.1 ∈ J then x ⟨w.1, hw⟩ else 1, ?_⟩
  have h : ∀ᶠ w : Outside D S in cofinite, w.1 ∉ J := by
    rw [Filter.eventually_cofinite]
    convert J.finite_toSet.preimage (f := fun w : Outside D S => w.val)
      Subtype.val_injective.injOn using 1
    ext w
    simp
  exact h.mono fun w hw => by simp [hw]

/-- The arithmetic projection to J, using integrality in U away from S ∪ J. -/
def projectedArithmetic (S J : Finset D.Place) (U : Subgroup (Adeles D i (S ∪ J))) :
    Subgroup (FinitePoints D i J) :=
  (lattice D i (S ∪ J) U).map (forgetPlaces D i Finset.subset_union_right)

/-- The diagonal closure in the region where the complementary adele lies in U. -/
def compatibleAdeles (S J : Finset D.Place) (U : Subgroup (Adeles D i (S ∪ J))) :
    Set (Adeles D i S) :=
  diagonalClosure D i S ∩
    forgetOutside D i (S := S) (T := S ∪ J) Finset.subset_union_left ⁻¹' (U : Set _)

/-- The places where an outside adele differs from the identity. -/
def support {S : Finset D.Place} (x : Adeles D i S) : Set (Outside D S) :=
  {w | x w ≠ 1}

end LinearAlgebraicGroups.Arithmetic.CompactProductIsolation

namespace LinearAlgebraicGroups.Specs.CompactProductIsolation

open Arithmetic Arithmetic.AdelicGroups Arithmetic.ArithmeticLatticeProjection
open Arithmetic.CompactProductIsolation
open Specs.IntegralModels (MatrixRealization)

/-- The quotient map of the compact-product argument, its contraction property and
its kernel. -/
def compactProductIsolation : Prop :=
  ∀ {J : Type u} {U : Type v} [Group J] [Group U] [TopologicalSpace J] [TopologicalSpace U]
    [IsTopologicalGroup J] [IsTopologicalGroup U] [CompactSpace U]
    (P : Subgroup (J × U)), IsClosed (P : Set (J × U)) →
    Function.Surjective ((MonoidHom.fst J U).comp P.subtype) →
    IsClosed (identityFiber P : Set (secondClosure P)) ∧
    ∃ hN : (identityFiber P).Normal,
      letI := hN
      ∃! φ : J →ₜ* (secondClosure P ⧸ identityFiber P),
        (∀ p : P, φ p.val.1 = QuotientGroup.mk' (identityFiber P) (secondCoordinate P p)) ∧
        (∀ x : J, Contracted x → φ x = 1) ∧
        (∀ x : J, φ x = 1 ↔ (x, 1) ∈ P) ∧
        (Dense (Subgroup.closure {x : J | Contracted x} : Set J) →
          ∀ x : J, (x, 1) ∈ P)

/-- For a compact open complementary subgroup, the projection of the compatible diagonal
closure is exactly the closure of the projected arithmetic subgroup. If this projection is
full and the contracted elements generate densely, the whole finite product embeds in the
adelic diagonal closure with identity elsewhere. -/
def isolateAdelicFactors : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (h : Disjoint J S) (U : Subgroup (Adeles D i (S ∪ J))),
    IsCompact (U : Set (Adeles D i (S ∪ J))) →
    IsOpen (U : Set (Adeles D i (S ∪ J))) →
    (projectFinite D i h) '' compatibleAdeles D i S J U =
      closure (projectedArithmetic D i S J U : Set (FinitePoints D i J)) ∧
    (Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) →
      Dense (Subgroup.closure {x : FinitePoints D i J | Contracted x} :
        Set (FinitePoints D i J)) →
      ∀ x : FinitePoints D i J, insertFinite D i S J x ∈ diagonalClosure D i S)

/-- The restricted product supported on E is the closure of its finite-support elements. -/
def finiteSupportDensity : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S : Finset D.Place) (E : Set (Outside D S)),
    closure {x : Adeles D i S | (support D i x).Finite ∧ support D i x ⊆ E} =
      {x : Adeles D i S | support D i x ⊆ E}

/-- Isolating every single factor over E isolates the entire restricted product over E. -/
def isolatedFactorsSpan : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S : Finset D.Place) (E : Set (Outside D S)) (Z : Subgroup (Adeles D i S)),
    IsClosed (Z : Set (Adeles D i S)) →
    (∀ w ∈ E, ∀ a : LocalPoints D i w.1,
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w a ∈ Z) →
    {x : Adeles D i S | support D i x ⊆ E} ⊆ Z

/-- Once the kernel is isolated, projection to the enlarged omitted set preserves the
diagonal closure and membership in that closure is equivalent upstairs and downstairs.
In particular, strong approximation after enlargement lifts to the original set. -/
def enlargeOmittedSet : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S T : Finset D.Place) (h : S ⊆ T),
    IsOpenQuotientMap (forgetOutside D i h) ∧
    (((forgetOutside D i h).ker : Set (Adeles D i S)) ⊆ diagonalClosure D i S →
      (forgetOutside D i h) '' diagonalClosure D i S = diagonalClosure D i T ∧
      (forgetOutside D i h) ⁻¹' diagonalClosure D i T = diagonalClosure D i S ∧
      (StrongApproximation D i T ↔ StrongApproximation D i S))

/-- If all outside factors except a finite remainder have been isolated, density of the
rational projection on that remainder lifts to strong approximation. -/
def projectToRemainingPlaces : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (h : Disjoint J S),
    IsOpenQuotientMap (projectFinite D i h) ∧
    ((∀ w : Outside D S, w.1 ∉ J → ∀ a : LocalPoints D i w.1,
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w a ∈
        diagonalClosure D i S) →
      (projectFinite D i h) '' diagonalClosure D i S = closure (range (rationalProjection D i J)) ∧
      (projectFinite D i h) ⁻¹' closure (range (rationalProjection D i J)) =
        diagonalClosure D i S ∧
      (DenseRange (rationalProjection D i J) ↔ StrongApproximation D i S))

end LinearAlgebraicGroups.Specs.CompactProductIsolation
