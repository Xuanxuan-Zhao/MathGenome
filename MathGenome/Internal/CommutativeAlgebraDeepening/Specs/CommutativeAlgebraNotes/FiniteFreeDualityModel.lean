import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.AugmentedCechComplex
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CochainLinearTensorHomAdjunction
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.LinearAlgebra.FreeModule.Basic

open CategoryTheory HomologicalComplex IsLocalRing
open CochainComplex (linearHomComplex)
open CommutativeAlgebraNotes.CochainTensorHom (Complex)
open CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)

namespace Specs.CommutativeAlgebraNotes.FiniteFreeDualityModel

open CompletionOfTorsionModules (Completion IsPowerTorsion scalar)

universe u

noncomputable section

/-- The indicated module placed in a single cohomological degree. In particular,
the stalk in degree `d` is the module in degree zero shifted by `-d`. -/
abbrev stalk {R : Type u} [CommRing R] (d : ℤ) (M : ModuleCat.{u} R) : Complex R :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) d).obj M

/-- The augmentation gives the first comparison. The second comparison is a
roof obtained by tensoring two quasi-isomorphisms with the given resolution. -/
def TensorComparisons : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (_ : AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue R) (d : ℕ)
    (_ : ringKrullDim R = (d : WithBot ℕ∞)) (E : residueFieldEnvelopeValue R)
    (rs : List R), Ideal.span {r | r ∈ rs} = maximalIdeal R →
    ∀ (X : ModuleCat.{u} R) [Module.Finite R X] (P : Complex R)
      (π : P ⟶ stalk 0 X), QuasiIso π →
      (∀ i, Module.Free R (P.X i)) → (∀ i, Module.Finite R (P.X i)) →
      (∃ N : ℤ, P.IsStrictlyLE N) →
      let C := AugmentedCechComplex.complex R rs
      QuasiIso (tensorHom π (𝟙 C)) ∧
        ∃ (W : Complex R) (s : W ⟶ C)
          (t : W ⟶ stalk (d : ℤ) (ModuleCat.of R E.carrier)),
          QuasiIso (tensorHom (𝟙 P) s) ∧ QuasiIso (tensorHom (𝟙 P) t)

/-- In the last model, currying followed by the scalar identification of the
inner Hom gives the completed-ring-valued Hom complex. This holds for every
complex `P`; the finite-free and boundedness conditions are needed for the
quasi-isomorphism comparisons. The formula specifies the comparison on pure
tensors in the only degree of the hull stalk. -/
def DualComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (E : residueFieldEnvelopeValue R) (P : Complex R),
    let A := ModuleCat.of R E.carrier
    let B := ModuleCat.of R (Completion R)
    let Q := stalk (d : ℤ) A
    let J := stalk 0 A
    let L := stalk (-(d : ℤ)) B
    ∃ (h : IsPowerTorsion R E.carrier)
      (e : linearHomComplex R (tensorObj P Q) J ≅ linearHomComplex R P L),
      ∀ {n i : ℤ} (hi : i + n = -(d : ℤ)) (f : CochainComplex.HomComplex.Cochain
          (tensorObj P Q) J n) (x : P.X i) (y : Q.X (d : ℤ)),
        scalar h
          ((singleObjXSelf (.up ℤ) (-(d : ℤ)) B).hom ((e.hom.f n f).v i _ hi x))
          ((singleObjXSelf (.up ℤ) (d : ℤ) A).hom y) =
        (singleObjXSelf (.up ℤ) 0 A).hom
          (f.v (i + (d : ℤ)) 0 (by omega)
            (ιTensorObj P Q i (d : ℤ) (i + (d : ℤ)) rfl
              (TensorProduct.tmul R x y)))

end

end Specs.CommutativeAlgebraNotes.FiniteFreeDualityModel
