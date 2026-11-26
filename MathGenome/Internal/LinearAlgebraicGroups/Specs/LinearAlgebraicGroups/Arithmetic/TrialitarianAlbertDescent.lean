import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.Triality
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import Mathlib.NumberTheory.LocalField.Basic

/-! The local trialitarian realization as a pointwise cubic-field stabilizer. -/

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Specs
open AutomorphismSequence Pinning QuasiSplitInnerForms
open RootGroups (AdditiveLine)
open RelativeFormComparison (fieldTest transportedAut)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open GeometricRadicals (IsSemisimple)
open LinearAlgebraicGroups.Albert
open SplitSpecification
open TrialitySpecification (Model)
open LinearAlgebraicGroups.Descent.NonabelianCohomology (pointAction IsCocycle)

universe u

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S]

/-- The three outer vertices are numbered 0, 1 and 2, with the central
vertex numbered 3. -/
def cartanD4 (i j : Fin 4) : ℤ :=
  if i = j then 2 else if i = 3 ∨ j = 3 then -1 else 0

/-- A pinned presentation of the diagram action of the given form, with the
three embeddings of its cubic orbit field identified with the outer vertices. -/
structure DiagramPresentation (G : AffineAlgebraicGroup F) (E S : Type u)
    [Field E] [Field S] [Algebra F E] [Algebra F S] where
  additive : AdditiveLine F
  pinned : PinnedGroup additive
  datum : AttachedDatum pinned.pair
  lifts : Aut datum.toBased ≃* Aut pinned
  adjoint : AdjointQuotient pinned.pair.G
  autSequence : SplitSequence pinned datum lifts adjoint
  semisimple : IsSemisimple pinned.pair.G
  simplyConnected : GeometricallySimplyConnected pinned.pair.G
  roots : Fin 4 ≃ datum.toBased.base.support
  cartan : ∀ i j, datum.toBased.datum.pairing (roots i).val (roots j).val = cartanD4 i j
  form : relativePoints pinned.pair.G.val (fieldTest F S) ≅ relativePoints G.val (fieldTest F S)
  numbering : (E →ₐ[F] S) ≃ Fin 3
  diagramAction : ∀ (σ : Gal(S/F)) (e : E →ₐ[F] S),
    (outerHom autSequence (transportedAut F S form σ)).asIso.hom.val.indexEquiv
        (roots (numbering e).castSucc).val =
      (roots (numbering (σ.toAlgHom.comp e)).castSucc).val

/-- The automorphism scheme of the unit and the entire quadratic Jordan law.
The comparison is natural on all test algebras. -/
structure AlbertModel (F : Type u) [Field F] where
  V : Type u
  [addV : AddCommGroup V]
  [moduleV : Module F V]
  law : ParaQuadratic F V
  albert : IsAlbert law
  automorphisms : AffineAlgebraicGroup F
  action : ∀ R : TestAlgebra F, Points automorphisms.val.X R →* (R ⊗[F] V ≃ₗ[R] R ⊗[F] V)
  faithful : ∀ R, Function.Injective (action R)
  image : ∀ R, Set.range (action R) =
    {g | g (1 ⊗ₜ[F] law.unit) = 1 ⊗ₜ[F] law.unit ∧
      ∀ x y, g (law.op R x y) = law.op R (g x) (g y)}
  natural : ∀ {R T : TestAlgebra F} (f : R ⟶ T) (g : Points automorphisms.val.X R) (x : R ⊗[F] V),
    let m := TensorProduct.map f.hom.toLinearMap (LinearMap.id : V →ₗ[F] V)
    m (action R g x) = action T (mapPoints f g) (m x)

attribute [instance] AlbertModel.addV AlbertModel.moduleV

/-- A cubic field inside the Albert algebra, with its pointwise stabilizer
identified by the functor of points on every commutative test algebra. -/
structure CubicStabilizer (J : AlbertModel F) (E : Type u) [Field E] [Algebra F E] where
  diagonal : E →ₗ[F] J.V
  injective : Function.Injective diagonal
  unit : diagonal 1 = J.law.unit
  respectsOperator : ∀ (R : TestAlgebra F) (x y : R ⊗[F] E),
    diagonal.baseChange R (x ^ 2 * y) =
      J.law.op R (diagonal.baseChange R x) (diagonal.baseChange R y)
  stabilizer : ClosedSubgroup J.automorphisms.val
  fixesExactly : ∀ (R : TestAlgebra F) (g : Points J.automorphisms.val.X R),
    (∀ x, J.action R g (diagonal.baseChange R x) = diagonal.baseChange R x) ↔
      ∃ h : Points stabilizer.group.X R, h ≫ stabilizer.inclusion.hom.hom = g

/-- The comparison with the split model over the separable closure carries the
cubic field to the diagonal with the specified indexing by its embeddings. -/
def IsDiagonalOver (J : AlbertModel F) (B : CubicStabilizer J E)
    (numbering : (E →ₐ[F] S) ≃ Fin 3) : Prop :=
  ∃ t : S ⊗[F] J.V ≃ₗ[S] Model S,
    t (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit ∧
    (∀ x y, t (J.law.op S x y) = TrialitySpecification.modelOp (t x) (t y)) ∧
    ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0)

/-- Split coordinates on the reference algebra furnished by the permutation
descent. Reversing a cyclic ordering conjugates the octonion blocks. -/
def IsPermutationDescent (J : AlbertModel F) (B : CubicStabilizer J E)
    (numbering : (E →ₐ[F] S) ≃ Fin 3) : Prop :=
  ∃ t : S ⊗[F] J.V ≃ₗ[S] Model S,
    t (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit ∧
    (∀ x y, t (J.law.op S x y) = TrialitySpecification.modelOp (t x) (t y)) ∧
    (∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0)) ∧
    ∀ (σ : Gal(S/F)), ∃ π : Equiv.Perm (Fin 3),
      (∀ e : E →ₐ[F] S, π (numbering e) = numbering (σ.toAlgHom.comp e)) ∧
      ∀ x : S ⊗[F] J.V,
        let y := TrialitySpecification.mapModel σ.toRingHom (t x)
        let z := t (TensorProduct.map σ.toAlgHom.toLinearMap LinearMap.id x)
        (∀ i, z.1 (π i) = y.1 i) ∧
        ∀ i, z.2 (π i) = if Equiv.Perm.sign π = 1 then y.2 i else
          Composition.AdjointSpecification.conjugate (Composition.ZornSpecification.norm S) (y.2 i)

/-- The inner displacement of the given group is represented by a continuous
cocycle of the simply connected reference stabilizer itself. -/
def HasInnerLift (M G : GroupScheme F) (S : Type u) [Field S] [Algebra F S] : Prop :=
  letI : TopologicalSpace (Gal(S/F)) := krullTopology F S
  letI : TopologicalSpace (Points M.X (CommAlgCat.of F S)) := ⊥
  ∃ (a : Gal(S/F) → Points M.X (CommAlgCat.of F S))
    (i : relativePoints M (fieldTest F S) ≅ relativePoints G (fieldTest F S)),
    IsCocycle (pointAction F S M.X) a ∧
      ∀ σ, transportedAut F S i σ = innerAut (a σ)

/-- The trialitarian reference comes from permutation descent of the split
frame. The original group is itself a pointwise cubic-field stabilizer in
an Albert algebra split over the given local field. -/
def TrialitarianRealization : Prop :=
  ∀ (F E S : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field E] [Field S] [Algebra F E] [Algebra F S]
    [Module.Finite F E] [Algebra.IsSeparable F E] [IsSepClosure F S],
    Module.finrank F E = 3 → ∀ (G : AffineAlgebraicGroup F) (D : DiagramPresentation G E S),
    ∃ (J₀ : AlbertModel F) (B₀ : CubicStabilizer J₀ E),
      IsPermutationDescent J₀ B₀ D.numbering ∧ HasInnerLift B₀.stabilizer.group G.val S ∧
      ∃ (J : AlbertModel F) (B : CubicStabilizer J E),
        Nonempty (G.val ≅ B.stabilizer.group) ∧ IsSplitModel J.law .octonion ∧
          IsDiagonalOver J B D.numbering

end LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
