import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs.FlagCohomology

universe u

namespace LinearAlgebraicGroups.Specs.ArithmeticProjectiveFiniteness

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The base ring obtained by inverting the integer (m). -/
abbrev BaseRing (m : ℕ) : Type u := Localization.Away (m : ULift.{u} ℤ)

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The usual total-degree grading on the homogeneous coordinate ring. -/
abbrev homogeneousGrading := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- The map from the base ring to the degree-zero part of the grading. -/
def homogeneousConstants : A →+* homogeneousGrading A n 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C _ a⟩
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)

/-- Projective (n)-space over the original coefficient ring. -/
abbrev projectiveSpace : SchemeOverRing A :=
  Over.mk (Proj.toSpecZero (homogeneousGrading A n) ≫
    Spec.map (CommRingCat.ofHom (homogeneousConstants A n)))

/-- The coefficient sheaf is quasi-coherent and trivial of rank one on an open neighborhood
of every point. -/
def IsLineBundleOn (Y : SchemeOverRing A) (F : Y.left.Modules) : Prop :=
  (F : SheafOfModules Y.left.ringCatSheaf).IsQuasicoherent ∧
    ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
      Nonempty (F.restrict U.ι ≅ structureModule U.toScheme)

/-- Finiteness of all derived global cohomology modules of the coefficient line over the
localized integer base. -/
def Statement : Prop :=
  ∀ (m : ℕ), m ≠ 0 →
    ∀ (Y : SchemeOverRing (BaseRing.{u} m)) (n : ℕ)
      (j : Y ⟶ projectiveSpace (BaseRing.{u} m) n), IsClosedImmersion j.left →
    ∀ (F : Y.left.Modules), IsLineBundleOn _ Y F →
      ∀ i : ℕ, Module.Finite (BaseRing.{u} m) ((cohomology Y i).obj F)

end

end LinearAlgebraicGroups.Specs.ArithmeticProjectiveFiniteness
