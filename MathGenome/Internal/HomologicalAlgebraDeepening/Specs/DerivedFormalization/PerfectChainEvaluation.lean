import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs

/-! Chain-level duality for a bounded complex of finite projective modules. -/

namespace Specs.DerivedFormalization.PerfectChainEvaluation

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CochainComplex.HomComplex
open HomologicalComplex (ιTensorObj)
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels
  (tensorComplexValue tensorMapValue internalHomValue internalHomMapValue)
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]

/-- The chain-level hypothesis of a bounded complex with finite projective terms. -/
def boundedFiniteProjectiveValue (P : compValue.{u} R) : Prop :=
  (∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) ∧
    (∀ i : ℤ, Module.Finite R (P.X i)) ∧ (∀ i : ℤ, Module.Projective R (P.X i))

def ringStalkType := ∀ (R : Type u) [CommRing R], compValue.{u} R

noncomputable abbrev ringStalkValue (R : Type u) [CommRing R] : compValue.{u} R :=
  (Specs.DerivedFormalization.Cochains.stalkValue R).obj (ModuleCat.of R R)

def chainDualType := ∀ {R : Type u} [CommRing R], compValue.{u} R → compValue.{u} R

noncomputable abbrev chainDualValue (P : compValue.{u} R) : compValue.{u} R :=
  internalHomValue P (ringStalkValue R)

noncomputable abbrev ringAtZero : (ringStalkValue R).X 0 ≅ ModuleCat.of R R :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)

def chainDualBoundedFiniteProjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] {P : compValue.{u} R},
    boundedFiniteProjectiveValue P → boundedFiniteProjectiveValue (chainDualValue P)

/-- All formulas use the signed tensor and internal Hom of the ordinary cochain models. -/
def chainDualityType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ (ev : ∀ P : compValue.{u} R, tensorComplexValue (chainDualValue P) P ⟶ ringStalkValue R)
      (cmp : ∀ P Y : compValue.{u} R, tensorComplexValue Y (chainDualValue P) ⟶ internalHomValue P Y)
      (coev : ∀ P : compValue.{u} R, boundedFiniteProjectiveValue P →
        (ringStalkValue R ⟶ tensorComplexValue P (chainDualValue P)))
      (bid : ∀ P : compValue.{u} R, P ⟶ chainDualValue (chainDualValue P)),
      (∀ (P : compValue.{u} R) (j i t : ℤ) (ht : j + i = t) (f : (chainDualValue P).X j)
          (x : P.X i),
        (ev P).f t (ιTensorObj (chainDualValue P) P j i t ht (f ⊗ₜ[R] x)) =
          f.v i t (by omega) x) ∧
      (∀ (P Y : compValue.{u} R) {i j k t : ℤ} (ht : j + k = t) (hk : i + k = 0)
          (y : Y.X j) (f : (chainDualValue P).X k) (x : P.X i),
        ((cmp P Y).f t
          (ιTensorObj Y (chainDualValue P) j k t ht (y ⊗ₜ[R] f))).v i j (by omega) x =
          (ringAtZero (R := R)).hom (f.v i 0 hk x) • y) ∧
      (∀ (P Y : compValue.{u} R) {i j k t l : ℤ} (ht : j + k = t) (hl : i + t = l)
          (hk : i + k ≠ 0) (y : Y.X j) (f : (chainDualValue P).X k) (x : P.X i),
        ((cmp P Y).f t
          (ιTensorObj Y (chainDualValue P) j k t ht (y ⊗ₜ[R] f))).v i l hl x = 0) ∧
      (∀ {P P' Y Y' : compValue.{u} R} (a : P' ⟶ P) (b : Y ⟶ Y'),
        tensorMapValue b (internalHomMapValue a (𝟙 (ringStalkValue R))) ≫ cmp P' Y' =
          cmp P Y ≫ internalHomMapValue a b) ∧
      (∀ (P : compValue.{u} R) (_ : boundedFiniteProjectiveValue P)
          (Y : compValue.{u} R), IsIso (cmp P Y)) ∧
      (∀ (P : compValue.{u} R) (hP : boundedFiniteProjectiveValue P),
        (cmp P P).f 0 ((coev P hP).f 0 ((ringAtZero (R := R)).inv 1)) =
          Cochain.ofHom (𝟙 P)) ∧
      (∀ (P : compValue.{u} R) (hP : boundedFiniteProjectiveValue P),
        coev P hP ▷ P ≫ (α_ P (chainDualValue P) P).hom ≫ P ◁ ev P ≫ (ρ_ P).hom =
          (λ_ P).hom) ∧
      (∀ (P : compValue.{u} R) (hP : boundedFiniteProjectiveValue P),
        chainDualValue P ◁ coev P hP ≫ (α_ (chainDualValue P) P (chainDualValue P)).inv ≫
          ev P ▷ chainDualValue P = (ρ_ (chainDualValue P)).hom ≫ (λ_ (chainDualValue P)).inv) ∧
      (∀ (P : compValue.{u} R) {i j t : ℤ} (ht : j + i = t)
          (x : P.X i) (f : (chainDualValue P).X j),
        ((bid P).f i x).v j t ht f = (i * j).negOnePow • f.v i t (by omega) x) ∧
      (∀ (P : compValue.{u} R), boundedFiniteProjectiveValue P → IsIso (bid P))

end Specs.DerivedFormalization.PerfectChainEvaluation
