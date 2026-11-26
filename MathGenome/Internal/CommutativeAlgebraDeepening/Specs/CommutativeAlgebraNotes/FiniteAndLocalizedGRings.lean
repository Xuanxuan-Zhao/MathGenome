import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion
import Mathlib.RingTheory.Localization.Submodule

open scoped TensorProduct
open Ideal
open Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion

universe u v

namespace CommutativeAlgebraNotes.Excellence.Specs

/-- After extending the base formal fibre to the residue field of a prime of
the upper local ring, the product coordinates are the fibres of the completed
stalks. The chosen stalk's coordinate is its formal fibre. -/
def FiniteFormalFiberDecomposition : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [IsNoetherianRing A] [IsNoetherianRing B]
    (p : Ideal A) [p.IsPrime] (i : PrimesOver p B)
    (Q : Ideal (Localization.AtPrime i.1.asIdeal)) [Q.IsPrime],
    let q := Q.under (Localization.AtPrime p)
    letI : Q.LiesOver q := ⟨rfl⟩
    letI := Localization.AtPrime.algebraOfLiesOver q Q
    Module.Finite q.ResidueField Q.ResidueField ∧
      (∃ e : (Q.ResidueField ⊗[q.ResidueField] q.Fiber
          (LocalCompletion (Localization.AtPrime p))) ≃ₐ[Q.ResidueField]
            ((j : PrimesOver p B) → Q.ResidueField ⊗[B] Factor p j),
        ∀ (a : Q.ResidueField) (b : q.ResidueField)
          (x : LocalCompletion (Localization.AtPrime p)) (j : PrimesOver p B),
          e (a ⊗ₜ[q.ResidueField] (b ⊗ₜ[Localization.AtPrime p] x)) j =
            (algebraMap q.ResidueField Q.ResidueField b * a) ⊗ₜ[B] fromBaseCompletion p j x) ∧
      (∃ e : (Q.ResidueField ⊗[B] Factor p i) ≃ₐ[Q.ResidueField] Q.Fiber (Factor p i),
        ∀ (a : Q.ResidueField) (x : Factor p i),
          e (a ⊗ₜ[B] x) = a ⊗ₜ[Localization.AtPrime i.1.asIdeal] x)

/-- Geometric regularity transfers at a pair of corresponding formal fibres,
under the single hypothesis of geometric regularity of the lower fibre. -/
def FiniteFormalFiberRegularity : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [IsNoetherianRing A] [IsNoetherianRing B]
    (p : Ideal A) [p.IsPrime] (i : PrimesOver p B)
    (Q : Ideal (Localization.AtPrime i.1.asIdeal)) [Q.IsPrime],
    let q := Q.under (Localization.AtPrime p)
    GeometricallyRegularValue q.ResidueField (q.Fiber (LocalCompletion (Localization.AtPrime p))) →
      GeometricallyRegularValue Q.ResidueField (Q.Fiber (Factor p i))

def FiniteAlgebraGRing : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B],
    IsGRingValue A →
      letI := IsNoetherianRing.of_finite A B
      IsGRingValue B

def LocalizedGRing : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] (M : Submonoid A) [IsLocalization M B],
    IsGRingValue A →
      letI := IsLocalization.isNoetherianRing M B inferInstance
      IsGRingValue B

def SurjectiveGRing : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) (hf : Function.Surjective f),
    IsGRingValue A →
      letI := isNoetherianRing_of_surjective A B f hf
      IsGRingValue B

end CommutativeAlgebraNotes.Excellence.Specs
