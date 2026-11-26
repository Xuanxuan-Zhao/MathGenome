import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.CliffordModel
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

namespace LinearAlgebraicGroups.Albert.SpinSpecification

open CliffordAlgebra Module
open scoped TensorProduct

universe u v w w' z z'

noncomputable section

set_option linter.checkUnivs false

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable (q : QuadraticForm R V) (S : Type z) [CommRing S] [Algebra R S]

abbrev ScalarClifford := S ⊗[R] CliffordAlgebra q

abbrev vectors : S ⊗[R] V →ₗ[S] ScalarClifford q S := (ι q).baseChange S

abbrev reversion : ScalarClifford q S →ₗ[S] ScalarClifford q S :=
  (reverse (Q := q)).baseChange S

abbrev evenPart : Submodule S (ScalarClifford q S) := (evenOdd q 0).baseChange S

/-- Conjugation in the scalar-extended Clifford algebra. -/
def conjugate (a : (ScalarClifford q S)ˣ) (x : ScalarClifford q S) :
    ScalarClifford q S := (a : ScalarClifford q S) * x * ↑a⁻¹

/-- Even units of reversion norm one preserving the vector module in both directions. -/
def spinUnits : Set (ScalarClifford q S)ˣ :=
  {a | (a : ScalarClifford q S) ∈ evenPart q S ∧
    reversion q S a * a = 1 ∧
    Set.MapsTo (conjugate q S a) (LinearMap.range (vectors q S))
      (LinearMap.range (vectors q S)) ∧
    Set.MapsTo (conjugate q S a⁻¹) (LinearMap.range (vectors q S))
      (LinearMap.range (vectors q S))}

def spinUnitsType := ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  (q : QuadraticForm R V) (S : Type z) [CommRing S] [Algebra R S],
  Set (ScalarClifford q S)ˣ

variable {I : Type w} [LinearOrder I] (b : Basis I R V)

/-- The intrinsic version of the criterion, in the actual Clifford algebra of the extended form. -/
def intrinsicCriterionType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm R V) (b : Basis I R V)
    (S : Type z) [CommRing S] [Algebra R S],
    let Q := CliffordSpecification.coefficientForm S q b
    ∃ e : ScalarClifford q S ≃ₐ[S] CliffordAlgebra Q,
      (∀ x, e (vectors q S x) = ι Q x) ∧
      ∀ (a : (ScalarClifford q S)ˣ),
        a ∈ spinUnits q S ↔
          e a ∈ evenOdd Q 0 ∧ reverse (e a) * e a = 1 ∧
          (fun x : CliffordAlgebra Q => e a * x * e ↑a⁻¹) ''
            (LinearMap.range (ι Q) : Set (CliffordAlgebra Q)) = LinearMap.range (ι Q)

abbrev ExtendedForm := CliffordSpecification.coefficientForm S q b

/-- Linear automorphisms preserving the scalar-extended quadratic form. -/
def orthogonalGroup : Subgroup ((S ⊗[R] V) ≃ₗ[S] (S ⊗[R] V)) where
  carrier := {g | ∀ x, ExtendedForm q S b (g x) = ExtendedForm q S b x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro g h hg hh x
    exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have h := hg (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- Restriction of Clifford conjugation to the vector module, expressed by its graph. -/
def IsVectorAction
    (a : (ScalarClifford q S)ˣ) (g : (S ⊗[R] V) ≃ₗ[S] (S ⊗[R] V)) : Prop :=
  ∀ x, vectors q S (g x) = conjugate q S a (vectors q S x)

def VectorActionType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm R V) (b : Basis I R V)
    (S : Type z) [CommRing S] [Algebra R S]
    (G : Subgroup (ScalarClifford q S)ˣ), (↑G : Set _) = spinUnits q S →
    ∃ ρ : G →* orthogonalGroup q S b,
      ∀ a : G, IsVectorAction q S a.val (ρ a).val

/-- The test-algebra map on Clifford elements. -/
def coefficientMap {T : Type z'} [CommRing T] [Algebra R T] (f : S →ₐ[R] T) :
    ScalarClifford q S →ₐ[R] ScalarClifford q T :=
  Algebra.TensorProduct.map f (AlgHom.id R (CliffordAlgebra q))

/-- Functoriality on the prescribed subgroup and naturality of its vector action. -/
def FunctorialityType : Prop :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (q : QuadraticForm R V) {I : Type w} [LinearOrder I] (_b : Basis I R V)
    {S : Type z} [CommRing S] [Algebra R S] {T : Type z'} [CommRing T] [Algebra R T]
    (G : Subgroup (ScalarClifford q S)ˣ) (H : Subgroup (ScalarClifford q T)ˣ)
    (_hG : (↑G : Set _) = spinUnits q S) (_hH : (↑H : Set _) = spinUnits q T)
    (f : S →ₐ[R] T),
    ∃ m : G →* H,
      (∀ a : G, (m a).val = Units.map (coefficientMap q S f).toMonoidHom a.val) ∧
      ∀ (a : G) (g : (S ⊗[R] V) ≃ₗ[S] (S ⊗[R] V))
        (h : (T ⊗[R] V) ≃ₗ[T] (T ⊗[R] V)),
        IsVectorAction q S a.val g → IsVectorAction q T (m a).val h →
        ∀ x, let fV := TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[R] V)
             fV (g x) = h (fV x)

/-- The kernel identification uses the scalar map, including over nonreduced algebras. -/
def ScalarKernel
    {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (q : QuadraticForm R V) (S : Type z) [CommRing S] [Algebra R S]
    (G : Subgroup (ScalarClifford q S)ˣ)
    (ρ : G →* (S ⊗[R] V) ≃ₗ[S] (S ⊗[R] V)) : Prop :=
  ∃ e : rootsOfUnity 2 S ≃* ρ.ker,
    ∀ ζ, (e ζ).val.val.val = algebraMap S _ (ζ.val : S)

def RegularKernelType : Prop :=
  ∀ {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    {I : Type w} [LinearOrder I] [Fintype I] (q : QuadraticForm K V) (_b : Basis I K V)
    (_h : LinearMap.ker q.polarBilin = ⊥ ∨
      ∃ r : V, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = K ∙ r)
    (S : Type z) [CommRing S] [Algebra K S]
    (G : Subgroup (ScalarClifford q S)ˣ) (ρ : G →* (S ⊗[K] V) ≃ₗ[S] (S ⊗[K] V)),
    (↑G : Set _) = spinUnits q S → (∀ a : G, IsVectorAction q S a.val (ρ a)) →
    ScalarKernel q S G ρ

/-- The full vector centralizer in characteristic two, before taking its even part. -/
def CharTwoCentralizersType : Prop :=
  ∀ {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    {I : Type w} [LinearOrder I] [Fintype I] (q : QuadraticForm K V) (_b : Basis I K V)
    (S : Type z) [CommRing S] [Algebra K S], (2 : K) = 0 →
    ∀ a : ScalarClifford q S,
      (LinearMap.ker q.polarBilin = ⊥ →
        ((∀ x, Commute a (vectors q S x)) ↔ ∃ t : S, a = algebraMap S _ t)) ∧
      (∀ r : V, q r ≠ 0 → LinearMap.ker q.polarBilin = K ∙ r →
        ((∀ x, Commute a (vectors q S x)) ↔
          ∃ t s : S, a = algebraMap S _ t + s • vectors q S (1 ⊗ₜ[K] r)))

/-- Clifford conjugation fixes the polar radical pointwise in characteristic two. -/
def CharTwoRadicalActionType : Prop :=
  ∀ {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm K V) (_b : Basis I K V)
    (S : Type z) [CommRing S] [Algebra K S], (2 : K) = 0 →
    ∀ (a : (ScalarClifford q S)ˣ) (g : (S ⊗[K] V) ≃ₗ[S] (S ⊗[K] V)),
      IsVectorAction q S a g →
      ∀ r ∈ LinearMap.ker q.polarBilin, g (1 ⊗ₜ[K] r) = 1 ⊗ₜ[K] r

def HyperbolicKernelType : Prop :=
  ∀ {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    {I : Type w} [LinearOrder I] [Fintype I] (_d : Basis I R E)
    {J : Type w'} [LinearOrder J] [Fintype J] (_b : Basis J R (Module.Dual R E × E))
    (S : Type z) [CommRing S] [Algebra R S],
    let q := QuadraticForm.dualProd R E
    ∀ (G : Subgroup (ScalarClifford q S)ˣ)
      (ρ : G →* (S ⊗[R] (Module.Dual R E × E)) ≃ₗ[S] (S ⊗[R] (Module.Dual R E × E))),
      (↑G : Set _) = spinUnits q S → (∀ a : G, IsVectorAction q S a.val (ρ a)) →
      ScalarKernel q S G ρ

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

abbrev GroupScheme (R : Type u) [CommRing R] := Grp (Over (Spec (CommRingCat.of R)))

abbrev SchemePoints {R : Type u} [CommRing R] (G : GroupScheme R) (S : CommAlgCat.{u} R) :=
  (algSpec (CommRingCat.of R)).obj (op S) ⟶ G.X

/-- A group-valued identification with the prescribed Clifford points on all test algebras. -/
def IsSpinPointRepresentation {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
    (q : QuadraticForm R V) (G : GroupScheme R)
    (e : ∀ S : CommAlgCat.{u} R, SchemePoints G S →* (ScalarClifford q S)ˣ) : Prop :=
  (∀ S, Function.Injective (e S) ∧ Set.range (e S) = spinUnits q S) ∧
  ∀ {S T : CommAlgCat.{u} R} (f : S ⟶ T) (a : SchemePoints G S),
    e T ((algSpec (CommRingCat.of R)).map f.op ≫ a) =
      Units.map (coefficientMap q S f.hom).toMonoidHom (e S a)

/-- Representability on all commutative test algebras, with the specified point group law. -/
def AffineRepresentationType : Prop :=
  ∀ {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
    {I : Type u} [LinearOrder I] [Fintype I] (q : QuadraticForm R V) (_b : Basis I R V),
    ∃ (A : CommAlgCat.{u} R), Algebra.FinitePresentation R A ∧
    ∃ (G : GroupScheme R),
      G.X = (algSpec (CommRingCat.of R)).obj (op A) ∧
      IsAffineHom G.X.hom ∧ LocallyOfFinitePresentation G.X.hom ∧
      ∃ e, IsSpinPointRepresentation q G e

abbrev muTwoPolynomial (R : Type u) [CommRing R] : Polynomial R := Polynomial.X ^ 2 - 1

abbrev muTwoCoordinateRing (R : Type u) [CommRing R] := AdjoinRoot (muTwoPolynomial R)

abbrev muTwoUnderlying (R : Type u) [CommRing R] :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (muTwoCoordinateRing R)))

def MuTwoRepresentationType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ e : ∀ (S : Type z) [CommRing S] [Algebra R S],
          (AdjoinRoot (muTwoPolynomial R) →ₐ[R] S) ≃ rootsOfUnity 2 S,
      (∀ (S : Type z) [CommRing S] [Algebra R S] (a : AdjoinRoot (muTwoPolynomial R) →ₐ[R] S),
        (e S a).val.val = a (AdjoinRoot.root (muTwoPolynomial R))) ∧
      ∀ (S T : Type z) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
        (f : S →ₐ[R] T) (a : AdjoinRoot (muTwoPolynomial R) →ₐ[R] S),
        (e T (f.comp a)).val.val = f (e S a).val.val

/-- The scalar subgroup represents the kernel of the vector action on all affine test schemes. -/
def HasScalarSchemeKernel {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
    (q : QuadraticForm R V) : Prop :=
  ∃ (G H : GroupScheme R) (i : H ⟶ G) (e : ∀ S, SchemePoints G S →* (ScalarClifford q S)ˣ)
    (e₂ : ∀ S, SchemePoints H S ≃* rootsOfUnity 2 S),
    IsSpinPointRepresentation q G e ∧ IsClosedImmersion i.hom.hom.left ∧
    (∃ h : H.X = muTwoUnderlying R,
      ∀ (S : CommAlgCat.{u} R) (a : muTwoCoordinateRing R →ₐ[R] S),
        (e₂ S ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom a).op ≫ eqToHom h.symm)).val.val =
          a (AdjoinRoot.root (muTwoPolynomial R))) ∧
    (∀ S (t : SchemePoints H S),
      (e S (t ≫ i.hom.hom)).val = algebraMap S _ (e₂ S t).val.val) ∧
    (∀ S (t : SchemePoints H S) (p : SchemePoints G S), Commute (t ≫ i.hom.hom) p) ∧
    ∀ S (p : SchemePoints G S),
      (∀ x, Commute (e S p).val (vectors q S x)) ↔
        ∃! t : SchemePoints H S, t ≫ i.hom.hom = p

def RegularSchemeKernelType : Prop :=
  ∀ {K : Type u} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
    {I : Type u} [LinearOrder I] [Fintype I] (q : QuadraticForm K V) (_b : Basis I K V),
    (LinearMap.ker q.polarBilin = ⊥ ∨
      ∃ r : V, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = K ∙ r) →
    HasScalarSchemeKernel q

def HyperbolicSchemeKernelType : Prop :=
  ∀ {R : Type u} [CommRing R] {E : Type u} [AddCommGroup E] [Module R E]
    {I J : Type u} [LinearOrder I] [Fintype I] [LinearOrder J] [Fintype J]
    (_d : Basis I R E) (_b : Basis J R (Module.Dual R E × E)),
    HasScalarSchemeKernel (QuadraticForm.dualProd R E)

end

end LinearAlgebraicGroups.Albert.SpinSpecification
