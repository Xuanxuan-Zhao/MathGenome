import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IdempotentCharts
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals

namespace LinearAlgebraicGroups.Albert.ReductiveFiberSpecification

open AlgebraicGeometry CategoryTheory Matrix
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open IdempotentSpecification (IsSplitAutomorphism ZornIndex)
open TrialitySpecification (Model mapModel)
open CubicSpecification (cubicUnit)
open _root_.LinearAlgebraicGroups.Composition (Zorn)
open scoped Matrix CategoryTheory.MonObj

universe u

noncomputable section

/-- An identification of a group scheme with the split quadratic Albert
automorphism functor on all test algebras. -/
structure SplitAction {k : Type u} [Field k] (G : GroupScheme k) where
  action : ∀ R : TestAlgebra k, Points G.X R →* (Model R ≃ₗ[R] Model R)
  injective : ∀ R, Function.Injective (action R)
  image : ∀ R, Set.range (action R) = {g | IsSplitAutomorphism g}
  natural : ∀ {R S : TestAlgebra k} (f : R ⟶ S) (g : Points G.X R) (x : Model R),
    mapModel f.hom.toRingHom (action R g x) =
      action S (mapPoints f g) (mapModel f.hom.toRingHom x)

abbrev traceMap (R : Type u) [CommRing R] : Model R →ₗ[R] R :=
  CubicSpecification.linearTrace (Composition.ZornSpecification.norm R) (fun _ => 1)

abbrev traceZero (R : Type u) [CommRing R] : Submodule R (Model R) :=
  LinearMap.ker (traceMap R)

/-- The line spanned by the unit in the ambient Albert module. -/
def scalarLine (R : Type u) [CommRing R] : Submodule R (Model R) :=
  Submodule.span R {cubicUnit}

def IsInvariant {K : Type u} [Field K] (W : Submodule K (Model K)) : Prop :=
  ∀ (g : Model K ≃ₗ[K] Model K), IsSplitAutomorphism g → ∀ x ∈ W, g x ∈ W

/-- Invariant subspaces of the representation, expressed as their inverse images
in the ambient split Albert module. -/
def PointIrreducibility (K : Type u) [Field K] : Prop :=
  scalarLine K ⊓ traceZero K < traceZero K ∧
  ∀ W : Submodule K (Model K), scalarLine K ⊓ traceZero K ≤ W →
    W ≤ traceZero K → IsInvariant W →
    W = scalarLine K ⊓ traceZero K ∨ W = traceZero K

/-- A split automorphism acting trivially modulo the scalar line on trace-zero
vectors is the identity. -/
def PointFaithfulness (K : Type u) [Field K] : Prop :=
  ∀ (g : Model K ≃ₗ[K] Model K), IsSplitAutomorphism g →
    (∀ x ∈ traceZero K, g x - x ∈ scalarLine K ⊓ traceZero K) → g = 1

def characteristicThree (k : Type u) [Field k] : Bool :=
  @ite Bool ((3 : k) = 0) (Classical.propDecidable _) true false

abbrev DiagonalIndex (b : Bool) := Fin (if b then 1 else 2)

abbrev TraceIndex (b : Bool) := ULift.{u} (DiagonalIndex b ⊕ (Fin 3 × ZornIndex))

/-- Two independent diagonal coordinates off characteristic three. In
characteristic three the single coordinate is the second diagonal entry
after subtracting the first diagonal entry times the unit. -/
def diagonalProjection (R : Type u) [CommRing R] :
    (b : Bool) → (Fin 3 → R) →ₗ[R] (DiagonalIndex b → R)
  | false => {
      toFun := fun x i => x (Fin.castLE (by decide) i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  | true => {
      toFun := fun x _ => x 1 - x 0
      map_add' := by intro x y; ext i; change (x 1 + y 1) - (x 0 + y 0) = (x 1 - x 0) + (y 1 - y 0); abel
      map_smul' := by intro c x; ext i; exact mul_sub c (x 1) (x 0) |>.symm }

def traceProjection (b : Bool) (R : Type u) [CommRing R] :
    Model R →ₗ[R] (TraceIndex.{u} b → R) where
  toFun x i := match i.down with
    | .inl j => diagonalProjection R b x.1 j
    | .inr (j, l) => Zorn.pairedFunctions R (x.2 j) l
  map_add' x y := by
    funext i
    rcases i with ⟨j | ⟨j,l⟩⟩
    · exact congrFun ((diagonalProjection R b).map_add x.1 y.1) j
    · exact congrFun ((Zorn.pairedFunctions R).map_add (x.2 j) (y.2 j)) l
  map_smul' c x := by
    funext i
    rcases i with ⟨j | ⟨j,l⟩⟩
    · exact congrFun ((diagonalProjection R b).map_smul c x.1) j
    · exact congrFun ((Zorn.pairedFunctions R).map_smul c (x.2 j)) l

/-- The quotient coordinates of the trace-zero space commute with scalar maps.
On a test algebra the kernel on trace-zero vectors is exactly its intersection
with the scalar line. -/
def TraceCoordinatesType : Prop :=
  ∀ (k : Type u) [Field k], let b := characteristicThree k
    (∀ R : TestAlgebra k,
      Function.Surjective (fun x : traceZero R => traceProjection b R x) ∧
      ∀ x ∈ traceZero R, traceProjection b R x = 0 ↔ x ∈ scalarLine R ⊓ traceZero R) ∧
    ∀ {R S : TestAlgebra k} (f : R ⟶ S) (x : Model R),
      traceProjection b S (mapModel f.hom.toRingHom x) = f.hom ∘ traceProjection b R x

/-- The actual trace-kernel or scalar-quotient action, represented by a group
scheme homomorphism and evaluated on every commutative test algebra. -/
def TraceRepresentation : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (a : SplitAction G.val),
    let b := characteristicThree k
    ∃ (L : GroupScheme k)
      (e : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k (TraceIndex.{u} b))
      (ρ : G.val ⟶ L),
      ∀ (R : TestAlgebra k) (g : Points G.val.X R) (x : Model R), x ∈ traceZero R →
        (e.hom.app R (((groupPointsFunctor k).map ρ).app R g)).val *ᵥ traceProjection b R x =
          traceProjection b R (a.action R g x)

/-- Geometric irreducibility and geometric faithfulness of the specified
trace representation kill the smooth connected unipotent radical. -/
def Reductivity : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (_ : SplitAction G.val),
    Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
    (∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K], PointIrreducibility K) →
    (∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K], PointFaithfulness K) →
    Specs.GeometricRadicals.IsReductive G

end
end LinearAlgebraicGroups.Albert.ReductiveFiberSpecification
