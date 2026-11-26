import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.FieldDiagonalTor
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity

noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity (degreeMultiplicity)

namespace CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection.Specs

open ExteriorTensorProduct (S includeX)
open PowerSeriesDiagonal (R diagonalIdeal identify)
open FieldDiagonalTor (diagonalList)
open IntersectionEulerCompletion.Specs (CompletedRing completedModuleCat)
open IsolatedTorSupport.Specs (Tor)
open IsolatedIntersectionEuler.Specs (intersectionEuler)

universe u v w

/-- The completed exterior tensor product using the right-variable copy of N. -/
abbrev diagonalTensor {k : Type u} [Field k] {d : ℕ}
    (M : ModuleCat.{v} (R k d)) (N : ModuleCat.{w} (R k d)) :=
  ExteriorTensorProduct.Spec.diagonalValue k d M N

/-- Homology of the Koszul complex on the diagonal with exterior tensor coefficients. -/
abbrev diagonalHomology {k : Type u} [Field k] {d : ℕ}
    (M : ModuleCat.{v} (R k d)) (N : ModuleCat.{w} (R k d)) (i : ℕ) :=
  AdvCommAlg.Koszul.homology (diagonalTensor M N) (diagonalList k d) i

/-- The restriction along the left copy supplies the diagonal ring action when the
joint ring acts through the map identifying the two copies. -/
abbrev diagonalModule {k : Type u} [Field k] {d : ℕ}
    (M : ModuleCat.{v} (R k d)) (N : ModuleCat.{w} (R k d)) (i : ℕ) :=
  (ModuleCat.restrictScalars (includeX k d d).toRingHom).obj (diagonalHomology M N i)

/-- The joint ring acts on Koszul homology through the diagonal quotient. -/
def diagonalAction {k : Type u} [Field k] {d : ℕ}
    (M : ModuleCat.{v} (R k d)) (N : ModuleCat.{w} (R k d)) : Prop :=
  ∀ (i : ℕ) (s : S k d d) (x : diagonalHomology M N i),
    s • x = includeX k d d (identify k d s) • x

/-- Transport the completed module to the chosen power-series ring. -/
abbrev presentedModule {A : Type u} [CommRing A] [IsLocalRing A] {d : ℕ}
    (e : R (ResidueField A) d ≃+* CompletedRing A) (M : ModuleCat.{v} A) :
    ModuleCat.{max u v} (R (ResidueField A) d) :=
  (ModuleCat.extendScalars e.symm.toRingHom).obj (completedModuleCat M)

/-- The original ring acts through completion and the chosen presentation. -/
abbrev restrictPresentation {A : Type u} [CommRing A] [IsLocalRing A] {d : ℕ}
    (e : R (ResidueField A) d ≃+* CompletedRing A) :
    ModuleCat.{v} (R (ResidueField A) d) ⥤ ModuleCat.{v} A :=
  ModuleCat.restrictScalars (e.symm.toRingHom.comp (algebraMap A (CompletedRing A)))

/-- The diagonal formulas and the dimension and sign conclusions over a
formal power-series ring over a field. -/
def powerSeriesDiagonalType : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ) (M : ModuleCat.{v} (R k d))
    (N : ModuleCat.{w} (R k d))
    [Module.Finite (R k d) M] [Module.Finite (R k d) N] [Nontrivial M] [Nontrivial N],
    IsFiniteLength (R k d) (M ⊗[R k d] N) →
      ∃ hreg : IsRegularLocalRing (R k d),
        letI := hreg
        ringKrullDim (R k d) = (d : WithBot ℕ∞) ∧
        diagonalAction M N ∧
        (∀ i : ℕ, Nonempty (Tor M N i ≃ₗ[R k d] ↥(diagonalModule M N i))) ∧
        (intersectionEuler M N : ℚ) = degreeMultiplicity (diagonalIdeal k d) (diagonalTensor M N) d ∧
        let s := moduleDimensionValue (R k d) M + moduleDimensionValue (R k d) N
        s ≤ (d : WithBot ℕ∞) ∧
          (s < (d : WithBot ℕ∞) → intersectionEuler M N = 0) ∧
          (s = (d : WithBot ℕ∞) → 0 < intersectionEuler M N)

/-- The diagonal formulas after completion, with the Koszul homology viewed
as a module over the original ring through the diagonal and the completion map. -/
def equalCharacteristicType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] (d : ℕ),
    ringKrullDim A = (d : WithBot ℕ∞) →
    ringChar (ResidueField A) = ringChar A →
    ∀ (M : ModuleCat.{v} A) (N : ModuleCat.{w} A) [Module.Finite A M] [Module.Finite A N]
      [Nontrivial M] [Nontrivial N],
      IsFiniteLength A (M ⊗[A] N) →
        ∃ σ : ResidueField A →+* CompletedRing A,
          (residue (CompletedRing A)).comp σ = ResidueField.map (algebraMap A (CompletedRing A)) ∧
          ∃ e : R (ResidueField A) d ≃+* CompletedRing A,
            (∀ a, e (MvPowerSeries.C a) = σ a) ∧
            let k := ResidueField A
            let M' := presentedModule e M
            let N' := presentedModule e N
            diagonalAction M' N' ∧
            (∀ i : ℕ, Nonempty (Tor M N i ≃ₗ[A] ↥((restrictPresentation e).obj
              (diagonalModule M' N' i)))) ∧
            (intersectionEuler M N : ℚ) =
              degreeMultiplicity (diagonalIdeal k d) (diagonalTensor M' N') d ∧
            let s := moduleDimensionValue A M + moduleDimensionValue A N
            s ≤ (d : WithBot ℕ∞) ∧
              (s < (d : WithBot ℕ∞) → intersectionEuler M N = 0) ∧
              (s = (d : WithBot ℕ∞) → 0 < intersectionEuler M N)

end CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection.Specs
