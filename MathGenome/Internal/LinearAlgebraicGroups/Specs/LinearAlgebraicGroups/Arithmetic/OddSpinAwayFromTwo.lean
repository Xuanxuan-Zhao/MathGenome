import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinFunctor
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Order.Sum.Order
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.OddSpinAwayFromTwo

open Albert.SpinSpecification
  (ExtendedForm IsSpinPointRepresentation IsVectorAction SchemePoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots pairing characterValue)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open AbstractPairing (Datum IsAttachedCoroot)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLatticeOf)
open SchemeDerivedGroup (RepresentsQuotient)

noncomputable section

abbrev Indices (n : ℕ) := Fin n ⊕ Fin n
abbrev OddIndices (n : ℕ) := Indices n ⊕ Unit
abbrev Space (n : ℕ) (R : Type u) := (Indices n → R) × R
 
instance oddIndicesOrder (n : ℕ) : LinearOrder (OddIndices n) :=
  (inferInstance : LinearOrder ((Fin n ⊕ₗ Fin n) ⊕ₗ Unit))

variable (n : ℕ) (R : Type u) [CommRing R]

/-- Hyperbolic coordinates followed by the norm-one coordinate. -/
def basis : Basis (OddIndices n) R (Space n R) :=
  (Pi.basisFun R (Indices n)).prod (Basis.singleton Unit R)

/-- The sum of the hyperbolic planes and the norm-one line. -/
def form : QuadraticForm R (Space n R) :=
  (∑ i : Fin n, QuadraticMap.linMulLin (LinearMap.proj (Sum.inl i))
    (LinearMap.proj (Sum.inr i))).prod (QuadraticMap.sq (R := R) (A := R))

def FormCoordinates : Prop :=
  ∀ (n : ℕ) (R : Type u) [CommRing R] (x : Space n R),
    form n R x = (∑ i : Fin n, x.1 (.inl i) * x.1 (.inr i)) + x.2 ^ 2

def PolarCoordinates : Prop :=
  ∀ (n : ℕ) (R : Type u) [CommRing R] (x y : Space n R),
    (form n R).polarBilin x y =
      (∑ i : Fin n, (x.1 (.inl i) * y.1 (.inr i) + x.1 (.inr i) * y.1 (.inl i))) +
        2 * x.2 * y.2

def PerfectPolar : Prop :=
  ∀ (n : ℕ) (k : Type u) [Field k], (2 : k) ≠ 0 →
    Function.Bijective (form n k).polarBilin

def coordinate (n : ℕ) (i : Fin n) : Fin n → ℤ := Pi.single i 1

/-- Both the short and the long roots of the adjoint type B pair. -/
def roots (n : ℕ) : Set (Fin n → ℤ) :=
  {v | (∃ i, v = coordinate n i ∨ v = -coordinate n i) ∨
    ∃ i j, i ≠ j ∧ (v = coordinate n i - coordinate n j ∨
      v = coordinate n i + coordinate n j ∨ v = -(coordinate n i + coordinate n j))}

/-- Short roots have doubled coroots, and long roots have the same coordinates. -/
def corootPairs (n : ℕ) : Set ((Fin n → ℤ) × (Fin n → ℤ)) :=
  {p | (∃ i, (p.1 = coordinate n i ∧ p.2 = 2 • coordinate n i) ∨
      (p.1 = -coordinate n i ∧ p.2 = -(2 • coordinate n i))) ∨
    ∃ i j, i ≠ j ∧ p.1 = p.2 ∧
      (p.1 = coordinate n i - coordinate n j ∨ p.1 = coordinate n i + coordinate n j ∨
        p.1 = -(coordinate n i + coordinate n j))}

def evenSum (n : ℕ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {v | Even (∑ i, v i)}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change Even (∑ i, (x i + y i))
    rw [Finset.sum_add_distrib]
    exact hx.add hy
  smul_mem' a x hx := by
    change Even (∑ i, a * x i)
    rw [← Finset.mul_sum]
    exact hx.mul_left a

def CorootLattice : Prop :=
  ∀ n : ℕ, 0 < n →
    Submodule.span ℤ (Prod.snd '' corootPairs n) = evenSum n ∧
    ∀ v : Fin n → ℤ, (∃ a : ℤ, 2 * a + ∑ i, v i = 0) ↔ v ∈ evenSum n

/-- Every determinant-one geometric isometry has an even, norm-one Clifford implementer. -/
def GeometricLifting : Prop :=
  ∀ {F V : Type u} [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (q : QuadraticForm F V), (2 : F) ≠ 0 →
    LinearMap.ker q.polarBilin = ⊥ →
    ∀ g : V ≃ₗ[F] V, (∀ x, q (g x) = q x) → LinearEquiv.det g = 1 →
    ∃ a : (CliffordAlgebra q)ˣ,
      a.val ∈ CliffordAlgebra.evenOdd q 0 ∧ CliffordAlgebra.reverse a.val * a.val = 1 ∧
      ∀ x, CliffordAlgebra.ι q (g x) = a.val * CliffordAlgebra.ι q x * (a⁻¹).val

/-- The intrinsic Clifford scheme has the full scalar kernel on the split odd space. -/
def ScalarKernel : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 →
    Albert.SpinSpecification.HasScalarSchemeKernel (form n k)

/-- The determinant-one isometries of the extended quadratic form. -/
def specialOrthogonal {k : Type u} [Field k] (n : ℕ) (S : CommAlgCat.{u} k) :
    Subgroup ((S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)) :=
  Albert.SpinSpecification.orthogonalGroup (form n k) S (basis n k) ⊓
    (LinearEquiv.det : ((S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)) →* Sˣ).ker

/-- Clifford conjugation has determinant one on every test algebra. -/
def DeterminantOneAction : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 →
    ∀ (S : Type u) [CommRing S] [Algebra k S]
      (a : (Albert.SpinSpecification.ScalarClifford (form n k) S)ˣ),
      a ∈ Albert.SpinSpecification.spinUnits (form n k) S →
      ∀ g, IsVectorAction (form n k) S a g → LinearEquiv.det g = 1

/-- The vector map from the intrinsic scalar-extended spin functor is surjective
on the determinant-one orthogonal points over any algebraically closed extension. -/
def GeometricVectorLifting : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 →
    ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
      ∀ g : specialOrthogonal n (CommAlgCat.of k K),
        ∃ a ∈ Albert.SpinSpecification.spinUnits (form n k) K,
          IsVectorAction (form n k) K a g.val

/-- The determinant-one isometry functor with its linear action and scalar maps. -/
def RepresentsSpecialOrthogonal {k : Type u} [Field k] {n : ℕ} (O : GroupScheme k)
    (o : ∀ S : CommAlgCat.{u} k, SchemePoints O S ≃* specialOrthogonal n S) : Prop :=
  ∀ {S T : CommAlgCat.{u} k} (f : S ⟶ T) (p : SchemePoints O S) (x : S ⊗[k] Space n k),
    let fV := TensorProduct.map f.hom.toLinearMap (LinearMap.id : Space n k →ₗ[k] Space n k)
    fV ((o S p).val x) = (o T ((algSpec (CommRingCat.of k)).map f.op ≫ p)).val (fV x)

/-- The diagonal action on the hyperbolic basis, fixing the last vector. -/
def IsDiagonalAction {k : Type u} [Field k] {n : ℕ} {S : CommAlgCat.{u} k}
    (t : Fin n → Sˣ) (g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)) : Prop :=
  (∀ i, g (1 ⊗ₜ[k] basis n k (.inl (.inl i))) = (t i : S) • (1 ⊗ₜ[k] basis n k (.inl (.inl i)))) ∧
  (∀ i, g (1 ⊗ₜ[k] basis n k (.inl (.inr i))) = (↑(t i)⁻¹ : S) • (1 ⊗ₜ[k] basis n k (.inl (.inr i)))) ∧
  g (1 ⊗ₜ[k] basis n k (.inr ())) = 1 ⊗ₜ[k] basis n k (.inr ())

def liftTorus {R : Type u} [CommRing R] (n : ℕ) : Subgroup ((Fin n → Rˣ) × Rˣ) :=
  (show ((Fin n → Rˣ) × Rˣ) →* Rˣ from
    { toFun := fun x => x.2 ^ 2 * ∏ i, x.1 i
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, Finset.prod_mul_distrib, mul_pow]
        ac_rfl }).ker

/-- The specified Clifford implementer of a lifted diagonal point. -/
def diagonalImplementer {k : Type u} [Field k] {n : ℕ} {S : CommAlgCat.{u} k}
    (t : liftTorus (R := S) n) : Albert.SpinSpecification.ScalarClifford (form n k) S :=
  let v := Albert.SpinSpecification.vectors (form n k) S
  algebraMap S _ (t.val.2 : S) *
    (List.ofFn fun i : Fin n =>
      let e := v (1 ⊗ₜ[k] basis n k (.inl (.inl i)))
      let f := v (1 ⊗ₜ[k] basis n k (.inl (.inr i)))
      (t.val.1 i : S) • (e * f) + f * e).prod

/-- The actual spin lifts of a diagonal isometry are precisely the indicated Clifford
implementers satisfying the torus norm equation, over every test algebra. -/
def DiagonalSpinPoints : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 →
    ∀ (S : CommAlgCat.{u} k) (t : Fin n → Sˣ)
      (g : (S ⊗[k] Space n k) ≃ₗ[S] (S ⊗[k] Space n k)), IsDiagonalAction t g →
      (∀ a : (Albert.SpinSpecification.ScalarClifford (form n k) S)ˣ,
        (a ∈ Albert.SpinSpecification.spinUnits (form n k) S ∧
          IsVectorAction (form n k) S a g) ↔
        ∃! z : liftTorus (R := S) n, z.val.1 = t ∧ a.val = diagonalImplementer (S := S) z) ∧
      (∀ z : liftTorus (R := S) n, z.val.1 = t →
        ∃ a : (Albert.SpinSpecification.ScalarClifford (form n k) S)ˣ,
          a ∈ Albert.SpinSpecification.spinUnits (form n k) S ∧
          IsVectorAction (form n k) S a g ∧ a.val = diagonalImplementer (S := S) z)

/-- The norm equation is solved by the scalar and all but the first hyperbolic scale. -/
def LiftTorusCoordinates : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    ∃ e : liftTorus (R := R) (n + 1) ≃* (Fin (n + 1) → Rˣ),
      ∀ z, e z = Fin.cons z.val.2 (z.val.1 ∘ Fin.succ)

/-- An orthogonal action on vectors induces the Clifford action on the spin functor.
When the isometry is the vector image of a spin point, this action is conjugation. -/
def CliffordEquivariance : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (S : CommAlgCat.{u} k) (h : specialOrthogonal n S),
    let Q := form n k
    let A := Albert.SpinSpecification.ScalarClifford Q S
    let v := Albert.SpinSpecification.vectors Q S
    ∃! φ : A ≃ₐ[S] A,
      (∀ x, φ (v x) = v (h.val x)) ∧
      (∀ a, a ∈ Albert.SpinSpecification.spinUnits Q S →
        Units.map φ.toMonoidHom a ∈ Albert.SpinSpecification.spinUnits Q S) ∧
      (∀ a, IsVectorAction Q S a h.val → ∀ x, φ x = Albert.SpinSpecification.conjugate Q S a x)

open Albert.SpinSpecification (ScalarClifford vectors coefficientMap spinUnits conjugate) in
/-- The adjoint action on the split quadratic space extends to a natural action
on its Clifford algebra and intrinsic spin functor. -/
def RepresentsCliffordAction {k : Type u} [Field k] {n : ℕ} (O : GroupScheme k)
    (o : ∀ S : CommAlgCat.{u} k, SchemePoints O S ≃* specialOrthogonal n S) : Prop :=
  let Q := form n k
  ∃ A : ∀ S : CommAlgCat.{u} k, SchemePoints O S →*
      (ScalarClifford Q S ≃ₐ[S] ScalarClifford Q S),
    (∀ S (h : SchemePoints O S),
      (∀ x, A S h (vectors Q S x) = vectors Q S ((o S h).val x)) ∧
      (∀ a, a ∈ spinUnits Q S → Units.map (A S h).toMonoidHom a ∈ spinUnits Q S) ∧
      (∀ a, IsVectorAction Q S a (o S h).val → ∀ x, A S h x = conjugate Q S a x)) ∧
    ∀ {S T : CommAlgCat.{u} k} (f : S ⟶ T) (h : SchemePoints O S) (x : ScalarClifford Q S),
      coefficientMap Q S f.hom (A S h x) = A T (mapPoints f h) (coefficientMap Q S f.hom x)

/-- The actual character and cocharacter coordinates of the marked adjoint torus. -/
def IsTypeBDatum {k : Type u} [Field k] {O : AffineAlgebraicGroup k}
    (n : ℕ) (T : ClosedSubgroup O.val) [IsCommMonObj T.group.X] (D : Datum T)
    (X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
    (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ)) : Prop :=
  (∀ χ c, pairing T.group χ c = ∑ i, X (Additive.ofMul χ) i * Y (Additive.ofMul c) i) ∧
  (fun χ => X (Additive.ofMul χ)) '' absoluteRoots T = roots n ∧
  (fun r => (X (Additive.ofMul r.val), Y (D.rootDatum.coroot r))) '' Set.univ = corootPairs n

/-- The split odd orthogonal group is represented on every test algebra. -/
def SpecialOrthogonalRepresentation : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 →
    ∃ (O : AffineAlgebraicGroup k)
      (o : ∀ S : CommAlgCat.{u} k, SchemePoints O.val S ≃* specialOrthogonal n S),
      RepresentsSpecialOrthogonal O.val o

/-- The split diagonal torus is a closed subgroup of the determinant-one isometry
scheme and acts by the specified hyperbolic scales on all test algebras. -/
def SplitOrthogonalTorus : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 →
    ∃ (O : AffineAlgebraicGroup k)
      (o : ∀ S : CommAlgCat.{u} k, SchemePoints O.val S ≃* specialOrthogonal n S)
      (T : ClosedSubgroup O.val)
      (t : ∀ S : CommAlgCat.{u} k, SchemePoints T.group S ≃* (Fin n → Sˣ)),
      RepresentsSpecialOrthogonal O.val o ∧ IsSplitTorus T.group ∧
      ∀ S a, IsDiagonalAction (t S a) (o S (a ≫ T.inclusion.hom.hom)).val

/-- The vector morphism to the represented orthogonal group, with its action
on all test algebras and surjectivity on algebraically closed test fields. -/
def VectorMorphism : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 →
    ∃ (G O : AffineAlgebraicGroup k) (p : G.val ⟶ O.val)
      (e : ∀ S : CommAlgCat.{u} k, SchemePoints G.val S →* (Albert.SpinSpecification.ScalarClifford (form n k) S)ˣ)
      (o : ∀ S : CommAlgCat.{u} k, SchemePoints O.val S ≃* specialOrthogonal n S),
      IsSpinPointRepresentation (form n k) G.val e ∧ RepresentsSpecialOrthogonal O.val o ∧
      (∀ S (g : SchemePoints G.val S), IsVectorAction (form n k) S (e S g)
        (o S (g ≫ p.hom.hom)).val) ∧
      Surjective p.hom.hom.left ∧
      (∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
        Function.Surjective (fun g : SchemePoints G.val (CommAlgCat.of k K) => g ≫ p.hom.hom)) ∧
      ∃ (Z : ClosedSubgroup G.val),
        IsSchemeKernel p Z ∧ Z.group.X = Albert.SpinSpecification.muTwoUnderlying k ∧
        (∀ S (z : SchemePoints Z.group S), ∃ ζ : rootsOfUnity 2 S,
          (e S (z ≫ Z.inclusion.hom.hom)).val = algebraMap S _ (ζ.val : S))

/-- The intrinsic vector map is a finite étale central cover of the represented
determinant-one isometry group, with the scalar order-two scheme as kernel. -/
def VectorCover : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 →
    ∃ (G O : AffineAlgebraicGroup k) (p : G.val ⟶ O.val)
      (e : ∀ S : CommAlgCat.{u} k, SchemePoints G.val S →*
        (Albert.SpinSpecification.ScalarClifford (form n k) S)ˣ)
      (o : ∀ S : CommAlgCat.{u} k, SchemePoints O.val S ≃* specialOrthogonal n S),
      IsSpinPointRepresentation (form n k) G.val e ∧ RepresentsSpecialOrthogonal O.val o ∧
      (∀ S (g : SchemePoints G.val S), IsVectorAction (form n k) S (e S g)
        (o S (g ≫ p.hom.hom)).val) ∧
      Smooth G.val.X.hom ∧ Smooth O.val.X.hom ∧ IsCentralIsogeny p ∧ Etale p.hom.hom.left ∧
      ∃ (Z : ClosedSubgroup G.val),
        IsSchemeKernel p Z ∧ Z.group.X = Albert.SpinSpecification.muTwoUnderlying k ∧
        Etale Z.group.X.hom ∧ RepresentsQuotient Z p ∧
        (∀ S (z : SchemePoints Z.group S), ∃ ζ : rootsOfUnity 2 S,
          (e S (z ≫ Z.inclusion.hom.hom)).val = algebraMap S _ (ζ.val : S))

/-- The full inverse image of the diagonal orthogonal torus under the intrinsic
spin vector map is the split torus given by the scalar norm equation. -/
def SplitSpinTorus : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 → 0 < n →
    ∃ (G O : AffineAlgebraicGroup k) (p : G.val ⟶ O.val)
      (e : ∀ S : CommAlgCat.{u} k, SchemePoints G.val S →*
        (Albert.SpinSpecification.ScalarClifford (form n k) S)ˣ)
      (o : ∀ S : CommAlgCat.{u} k, SchemePoints O.val S ≃* specialOrthogonal n S),
      IsSpinPointRepresentation (form n k) G.val e ∧ RepresentsSpecialOrthogonal O.val o ∧
      (∀ S (g : SchemePoints G.val S), IsVectorAction (form n k) S (e S g)
        (o S (g ≫ p.hom.hom)).val) ∧
      ∃ (T : ClosedSubgroup O.val) (U : ClosedSubgroup G.val) (pT : U.group ⟶ T.group),
        IsSplitTorus T.group ∧ IsSplitTorus U.group ∧
        GeometricallyConnected T.group.X.hom ∧ GeometricallyConnected U.group.X.hom ∧
        IsTorusRestriction p pT ∧
        IsPullback pT.hom.hom U.inclusion.hom.hom T.inclusion.hom.hom p.hom.hom ∧
        (∃ (Z : ClosedSubgroup G.val), IsSchemeKernel p Z ∧
          Z.group.X = Albert.SpinSpecification.muTwoUnderlying k ∧
          ∃ j : Z.group ⟶ U.group, j ≫ U.inclusion = Z.inclusion) ∧
        ∃ (t : ∀ S : CommAlgCat.{u} k, SchemePoints T.group S ≃* (Fin n → Sˣ))
          (s : ∀ S : CommAlgCat.{u} k, SchemePoints U.group S ≃* liftTorus (R := S) n),
          (∀ S a, IsDiagonalAction (t S a) (o S (a ≫ T.inclusion.hom.hom)).val) ∧
          (∀ S a, t S (a ≫ pT.hom.hom) = (s S a).val.1) ∧
          (∀ S a, (e S (a ≫ U.inclusion.hom.hom)).val = diagonalImplementer (s S a)) ∧
          ∃ comm : IsCommMonObj T.group.X,
            letI := comm
            ∃ (X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
              (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ)),
              (∀ χ c, pairing T.group χ c = ∑ i, X (Additive.ofMul χ) i * Y (Additive.ofMul c) i) ∧
              (∀ S (a : SchemePoints T.group S) (χ : Character T.group),
                characterValue χ S a = ((∏ i, (t S a i) ^ (X (Additive.ofMul χ) i) : Sˣ) : S)) ∧
              (∀ (S : CommAlgCat.{u} k) (z : Sˣ) (c : Cocharacter T.group) i,
                t S (cocharacterPoint c S z) i = z ^ (Y (Additive.ofMul c) i)) ∧
              Function.Injective (fun c : Cocharacter U.group => c ≫ pT) ∧
              Set.range (fun c : Cocharacter U.group => Y (Additive.ofMul (c ≫ pT))) = evenSum n

/-- Both ambient groups in the intrinsic vector cover are geometrically connected. -/
def SplitOddConnectedness : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 → 0 < n →
    ∃ (G O : AffineAlgebraicGroup k) (p : G.val ⟶ O.val)
      (e : ∀ S : CommAlgCat.{u} k, SchemePoints G.val S →*
        (Albert.SpinSpecification.ScalarClifford (form n k) S)ˣ)
      (o : ∀ S : CommAlgCat.{u} k, SchemePoints O.val S ≃* specialOrthogonal n S),
      IsSpinPointRepresentation (form n k) G.val e ∧ RepresentsSpecialOrthogonal O.val o ∧
      (∀ S (g : SchemePoints G.val S), IsVectorAction (form n k) S (e S g)
        (o S (g ≫ p.hom.hom)).val) ∧
      GeometricallyConnected G.val.X.hom ∧ GeometricallyConnected O.val.X.hom

/-- The split odd spin model in characteristic different from two. -/
def SplitOddSpin : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 → 0 < n →
    ∃ (G O : AffineAlgebraicGroup k) (p : G.val ⟶ O.val)
      (e : ∀ S : CommAlgCat.{u} k, SchemePoints G.val S →* (Albert.SpinSpecification.ScalarClifford (form n k) S)ˣ)
      (o : ∀ S : CommAlgCat.{u} k, SchemePoints O.val S ≃* specialOrthogonal n S),
      CliffordEquivariance.{u} ∧ RepresentsCliffordAction O.val o ∧
      IsSpinPointRepresentation (form n k) G.val e ∧ RepresentsSpecialOrthogonal O.val o ∧
      (∀ S (g : SchemePoints G.val S), IsVectorAction (form n k) S (e S g)
        (o S (g ≫ p.hom.hom)).val) ∧
      IsSemisimple G ∧ GeometricallySimplyConnected G ∧ IsSemisimple O ∧
      IsCentralIsogeny p ∧ Etale p.hom.hom.left ∧
      (∀ (S : SchemeOver k) (a : S ⟶ O.val.X), Centralizes (𝟙 O.val) a → a = 1) ∧
      ∃ (Z : ClosedSubgroup G.val),
        IsSchemeKernel p Z ∧ Z.group.X = Albert.SpinSpecification.muTwoUnderlying k ∧
        RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 G.val) z) ∧
        (∀ S (g : SchemePoints Z.group S),
          ∃ ζ : rootsOfUnity 2 S, (e S (g ≫ Z.inclusion.hom.hom)).val =
            algebraMap S _ (ζ.val : S)) ∧
        RepresentsQuotient Z p ∧
      ∃ (T : ClosedSubgroup O.val) (U : ClosedSubgroup G.val) (pT : U.group ⟶ T.group),
        IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧
        IsSplitTorus U.group ∧ IsGeometricallyMaximal U ∧ IsTorusRestriction p pT ∧
        IsPullback pT.hom.hom U.inclusion.hom.hom T.inclusion.hom.hom p.hom.hom ∧
        (∀ S (a : SchemePoints T.group S) (b : SchemePoints G.val S),
          a ≫ T.inclusion.hom.hom = b ≫ p.hom.hom →
          ∃! c : SchemePoints U.group S, c ≫ pT.hom.hom = a ∧ c ≫ U.inclusion.hom.hom = b) ∧
      ∃ (t : ∀ S : CommAlgCat.{u} k, SchemePoints T.group S ≃* (Fin n → Sˣ))
        (s : ∀ S : CommAlgCat.{u} k, SchemePoints U.group S ≃* @liftTorus S _ n),
        (∀ S a, IsDiagonalAction (t S a) (o S (a ≫ T.inclusion.hom.hom)).val) ∧
        (∀ S a, t S (a ≫ pT.hom.hom) = (s S a).val.1) ∧
        (∀ S a, (e S (a ≫ U.inclusion.hom.hom)).val = diagonalImplementer (s S a)) ∧
      ∃ (comm : IsCommMonObj T.group.X),
        letI := comm
        ∃ (D : Datum T) (X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
          (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ)),
          IsTypeBDatum n T D X Y ∧
          (corootLatticeOf D).map Y.toLinearMap = evenSum n ∧
          (∀ S (a : SchemePoints T.group S) (χ : Character T.group),
            characterValue χ S a = ((∏ i, (t S a i) ^ (X (Additive.ofMul χ) i) : Sˣ) : S)) ∧
          (∀ (S : CommAlgCat.{u} k) (z : Sˣ) (c : Cocharacter T.group) i,
            t S (cocharacterPoint c S z) i = z ^ (Y (Additive.ofMul c) i)) ∧
          Function.Injective (fun c : Cocharacter U.group => c ≫ pT) ∧
          Set.range (fun c : Cocharacter U.group => Y (Additive.ofMul (c ≫ pT))) = evenSum n

end

end LinearAlgebraicGroups.Specs.Arithmetic.OddSpinAwayFromTwo
