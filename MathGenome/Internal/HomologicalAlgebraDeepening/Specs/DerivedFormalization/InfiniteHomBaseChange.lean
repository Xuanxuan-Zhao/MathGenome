import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomComparisonMaps
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! The degree-zero counterexample for scalar extension of internal Hom. -/

namespace Specs.DerivedFormalization.InfiniteHomBaseChange

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings
open Cochains (compValue stalkValue qValue derivedCohomologyValue cohomologyFactorsValue)
open CochainTensor (tensor isKFlat)
open CochainTensorTransport (AdequateModel)
open CochainModels (internalHomValue)
open DerivedHomAdjunction (Closed Presentation homComparison)
open DerivedHomModels (Models rHomValue)
open DerivedScalarExtension (Extension MonoidalExtension)
open ScalarExtensionTransport (extension extendPure MonoidalChange)

attribute [local instance] HasDerivedCategory.standard

universe u

noncomputable section

variable (k : Type u) [Field k]

abbrev P : compValue.{u} k := (stalkValue k).obj (ModuleCat.of k (ℕ →₀ k))
abbrev Y : compValue.{u} k := (stalkValue k).obj (ModuleCat.of k k)

abbrev scalarMap : k →+* Polynomial k := Polynomial.C

/-- The coefficientwise scalar extension of sequences. -/
def coefficientMap : Polynomial k ⊗[k] (ℕ → k) →ₗ[Polynomial k] (ℕ → Polynomial k) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun p => LinearMap.pi fun n =>
        (LinearMap.mulLeft k p).comp ((Algebra.linearMap k (Polynomial k)).comp (LinearMap.proj n))
      map_add' := fun p q => by
        apply LinearMap.ext
        intro a
        funext n
        change (p + q) * Polynomial.C (a n) = p * Polynomial.C (a n) + q * Polynomial.C (a n)
        exact add_mul ..
      map_smul' := fun p q => by
        apply LinearMap.ext
        intro a
        funext n
        change (p * q) * Polynomial.C (a n) = p * (q * Polynomial.C (a n))
        exact mul_assoc .. }


def CoefficientBound : Prop :=
  ∀ (k : Type u) [Field k] (x : Polynomial k ⊗[k] (ℕ → k)),
    ∃ N : ℕ, ∀ n : ℕ, ((coefficientMap k) x n).natDegree ≤ N

def MissingSequence : Prop :=
  ∀ (k : Type u) [Field k],
    (fun n : ℕ => (Polynomial.X : Polynomial k) ^ n) ∉ Set.range (coefficientMap k)

section ChainComparison

variable {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
  {MR : AdequateModel (RingEquiv.refl R)} {MS : AdequateModel (RingEquiv.refl S)}
  (F : MonoidalChange (RingEquiv.refl R) (RingEquiv.refl S) f MR MS)

local notation "E" => extension (RingEquiv.refl S) f
local notation "Hom" => internalHomValue

/-- The ordinary map is adjoint to extended evaluation under the signed tensor–Hom
adjunction. -/
def chainComparison (P Y : compValue.{u} R) :
    (E).obj (Hom P Y) ⟶ Hom ((E).obj P) ((E).obj Y) :=
  letI := MR.chainMonoidal
  letI := MS.chainMonoidal
  letI := MR.chainSymmetric
  letI := MS.chainSymmetric
  letI := F.extensionBraided
  let H := Hom P Y
  let b := MS.tensorModel ((E).obj H) ((E).obj P) ≪≫ Functor.Monoidal.μIso E H P ≪≫
    (E).mapIso (MR.tensorModel H P).symm
  (MS.rawClosed ((E).obj P)).adj.homEquiv _ _
    (b.hom ≫ (E).map ((MR.rawClosed P).adj.counit.app Y))

end ChainComparison

section Counterexample

open CategoryTheory.Limits HomologicalComplex

/-- A complex supported in degree zero. -/
abbrev DegreeZero {R : Type u} [CommRing R] (C : compValue.{u} R) :=
  ∀ i : ℤ, i ≠ 0 → IsZero (C.X i)

def termCohomologyIso {R : Type u} [CommRing R] (C : compValue.{u} R)
    (h : DegreeZero C) : C.X 0 ≅ C.homology 0 :=
  (C.iCyclesIso 0 1 ((ComplexShape.up ℤ).next_eq' (by decide)) ((h 1 (by decide)).eq_of_tgt _ _)).symm ≪≫
    C.isoHomologyπ (-1) 0 ((ComplexShape.up ℤ).prev_eq' (by decide)) ((h (-1) (by decide)).eq_of_src _ _)

def termToDerived {R : Type u} [CommRing R] (C : compValue.{u} R) (h : DegreeZero C) :
    C.X 0 ≅ (derivedCohomologyValue R 0).obj ((qValue R).obj C) :=
  termCohomologyIso C h ≪≫ (cohomologyFactorsValue R 0).symm.app C

abbrev stalkPresentation {R : Type u} [CommRing R] (X : compValue.{u} R) :
    Presentation ((qValue R).obj X) := ⟨X, Iso.refl _⟩

abbrev extendedPresentation {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (L : Extension (RingEquiv.refl S) f)
    (X : compValue.{u} R) (hX : isKFlat X) :
    Presentation (L.derived.obj ((qValue R).obj X)) :=
  ⟨(extension (RingEquiv.refl S) f).obj X, (L.toLift.model X hX).symm⟩

variable (k : Type u) [Field k]

local notation "S" => Polynomial k
local notation "E" => extension (RingEquiv.refl (Polynomial k)) (scalarMap k)
abbrev extendedSource : compValue.{u} S := (E).obj (internalHomValue (P k) (Y k))
abbrev extendedTarget : compValue.{u} S := internalHomValue ((E).obj (P k)) ((E).obj (Y k))

abbrev yZero : (Y k).X 0 ≅ ModuleCat.of k k := singleObjXSelf (.up ℤ) 0 _

def basisVector (n : ℕ) : (P k).X 0 :=
  (singleObjXSelf (.up ℤ) 0 (ModuleCat.of k (ℕ →₀ k))).inv (Finsupp.single n 1)

/-- The actual represented extension term expressed using the polynomial algebra action. -/
def polynomialTensorTerm (C : compValue.{u} k) (i : ℤ) :
    ((E).obj C).X i ≃ₗ[S] S ⊗[k] (C.X i) := by
  let M := (ModuleCat.restrictScalars ((RingEquiv.refl S).toRingHom.comp (scalarMap k))).obj
    (ModuleCat.of S S)
  letI : Module S M := inferInstanceAs (Module S S)
  letI : IsScalarTower k S M := ⟨fun r s p => by
    change (r • s) * (show S from p) = Polynomial.C r * (s * (show S from p))
    rw [Polynomial.smul_eq_C_mul, mul_assoc]⟩
  let b : M ≃ₗ[S] S := LinearEquiv.refl S S
  exact TensorProduct.AlgebraTensorModule.congr b (LinearEquiv.refl k (C.X i))

def extendedYTerm : ((E).obj (Y k)).X 0 ≃ₗ[S] S :=
  (polynomialTensorTerm k (Y k) 0).trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (yZero k).toLinearEquiv).trans (TensorProduct.AlgebraTensorModule.rid k S S))

variable {L : Extension (RingEquiv.refl (Polynomial k)) (scalarMap k)}

def sourceCohomologyMap (HR : Models.{u,u} k)
    (hH : isKFlat (internalHomValue (P k) (Y k))) (h : DegreeZero (extendedSource k)) :
    (extendedSource k).X 0 ⟶ (derivedCohomologyValue S 0).obj
      (L.derived.obj ((rHomValue HR).obj (op ((qValue k).obj (P k)), (qValue k).obj (Y k)))) :=
  (termToDerived (extendedSource k) h).hom ≫ (derivedCohomologyValue S 0).map
    ((L.toLift.model _ hH).inv ≫
      L.derived.map (homComparison HR (stalkPresentation (P k)) (stalkPresentation (Y k))))

def targetCohomologyMap (HS : Models.{u,u} S)
    (hP : isKFlat (P k)) (hY : isKFlat (Y k)) (h : DegreeZero (extendedTarget k)) :
    (extendedTarget k).X 0 ⟶ (derivedCohomologyValue S 0).obj
      ((rHomValue HS).obj (op (L.derived.obj ((qValue k).obj (P k))),
        L.derived.obj ((qValue k).obj (Y k)))) :=
  (termToDerived (extendedTarget k) h).hom ≫ (derivedCohomologyValue S 0).map
    (homComparison HS (extendedPresentation L (P k) hP) (extendedPresentation L (Y k) hY))

/-- In the indicated cohomology identifications the canonical derived map
is the coefficientwise map, and the powers of the indeterminate are missed. -/
def Counterexample : Prop :=
  ∀ (k : Type u) [Field k]
    {MR : AdequateModel (RingEquiv.refl k)} {MS : AdequateModel (RingEquiv.refl (Polynomial k))}
    {TR : DerivedTensor.Model MR} {TS : DerivedTensor.Model MS}
    {HR : Models.{u,u} k} {HS : Models.{u,u} (Polynomial k)}
    {F : MonoidalChange (RingEquiv.refl k) (RingEquiv.refl (Polynomial k)) (scalarMap k) MR MS}
    {L : Extension (RingEquiv.refl (Polynomial k)) (scalarMap k)}
    (cR : Closed TR HR) (cS : Closed TS HS)
    (m : MonoidalExtension TR.toDescent TS.toDescent F L),
    let β := (derivedCohomologyValue (Polynomial k) 0).map
      (DerivedHomComparisonMaps.baseChangeValue cR cS m ((qValue k).obj (P k)) ((qValue k).obj (Y k)))
    ∃ (hp : (P k).IsKProjective) (hY : isKFlat (Y k))
      (hH : isKFlat (internalHomValue (P k) (Y k)))
      (hsrc : DegreeZero (extendedSource k)) (hdst : DegreeZero (extendedTarget k))
      (src : (extendedSource k).X 0 ≃ₗ[(Polynomial k)] (Polynomial k) ⊗[k] (ℕ → k)) (dst : (extendedTarget k).X 0 ≃ₗ[(Polynomial k)] (ℕ → (Polynomial k))),
      let a := sourceCohomologyMap k (L := L) HR hH hsrc
      let b := targetCohomologyMap k (L := L) HS (L.projectiveFlat _ hp) hY hdst
      (∀ (s : Polynomial k) (v : (internalHomValue (P k) (Y k)).X 0), src (extendPure (RingEquiv.refl (Polynomial k)) (scalarMap k) (internalHomValue (P k) (Y k)) 0 s v) =
        s ⊗ₜ[k] (fun n => (yZero k).hom (v.v 0 0 rfl (basisVector k n)))) ∧
      (∀ (v : (extendedTarget k).X 0) (n : ℕ), dst v n = extendedYTerm k
        (v.v 0 0 rfl (extendPure (RingEquiv.refl (Polynomial k)) (scalarMap k) (P k) 0 1 (basisVector k n)))) ∧
      IsIso a ∧ IsIso b ∧
      (∀ x, β (a x) = b (dst.symm (coefficientMap k (src x)))) ∧
      b (dst.symm (fun n => Polynomial.X ^ n)) ∉ Set.range β

/-- For each field the compatible models exist and the canonical map on degree-zero
cohomology fails to be surjective. -/
def ExistsCounterexample : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (MR : AdequateModel (RingEquiv.refl k))
      (MS : AdequateModel (RingEquiv.refl (Polynomial k)))
      (TR : DerivedTensor.Model MR) (TS : DerivedTensor.Model MS)
      (HR : Models.{u,u} k) (HS : Models.{u,u} (Polynomial k))
      (F : MonoidalChange (RingEquiv.refl k) (RingEquiv.refl (Polynomial k)) (scalarMap k) MR MS)
      (L : Extension (RingEquiv.refl (Polynomial k)) (scalarMap k))
      (cR : Closed TR HR) (cS : Closed TS HS)
      (m : MonoidalExtension TR.toDescent TS.toDescent F L),
      ¬ Function.Surjective ((derivedCohomologyValue (Polynomial k) 0).map
        (DerivedHomComparisonMaps.baseChangeValue cR cS m ((qValue k).obj (P k)) ((qValue k).obj (Y k))))

end Counterexample

end

end Specs.DerivedFormalization.InfiniteHomBaseChange
