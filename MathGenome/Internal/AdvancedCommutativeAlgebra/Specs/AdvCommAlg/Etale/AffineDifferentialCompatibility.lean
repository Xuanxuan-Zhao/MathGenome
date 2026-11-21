import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.BaseChange
import Mathlib.RingTheory.Etale.Kaehler

/-! Algebraic compatibility on affine principal charts (paper.tex:2079–2087).
All rings may be zero. Scalar extension is the tensor model of localized
modules, as in KD-16. All localization models and compatible structural maps
are arbitrary; in particular no regularity condition on g or h is imposed. -/
namespace Specs.AdvCommAlg.Etale.AffineDifferentialCompatibility

open TensorProduct
open Specs.AdvCommAlg.Differentials (baseChangeEquivValue)
universe u v w z t q
noncomputable section

/-- The KD-16 comparison, in its tensor model. Its defining map is the natural
map on differentials; thus its choice is independent of a presentation. -/
def localizationComparison (A : Type u) (B : Type v) (T : Type w)
    [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    (S : Submonoid B) [IsLocalization S T] :
    T ⊗[B] KaehlerDifferential A B ≃ₗ[T] KaehlerDifferential A T :=
  (IsLocalizedModule.isBaseChange S T (KaehlerDifferential.map A A B T)).equiv

/-- An arbitrary model F of (B_g)_(h/1) is also a model of B_(gh).
The outer comparison below is consequently the *direct* KD-16 comparison at
gh, with the canonical ring identification supplied by the localization
universal property. The equality holds on the entire iterated module. -/
def principalIteration : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w) (F : Type z)
    [CommRing A] [CommRing B] [CommRing C] [CommRing F]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra A F] [Algebra B F] [Algebra C F]
    [IsScalarTower A B F] [IsScalarTower A C F] [IsScalarTower B C F]
    (g h : B) [IsLocalization.Away g C]
    [IsLocalization.Away (algebraMap B C h) F],
    letI : IsLocalization.Away (g * h) F := IsLocalization.Away.mul' C F g h
    ∀ x : F ⊗[C] (C ⊗[B] KaehlerDifferential A B),
      localizationComparison A B F (Submonoid.powers (g * h))
        (AlgebraTensorModule.cancelBaseChange B C F F (KaehlerDifferential A B) x) =
      localizationComparison A C F (Submonoid.powers (algebraMap B C h))
        ((localizationComparison A B C (Submonoid.powers g)).toLinearMap.baseChange F x)

/-- The two comparison paths both carry db/1/1 to d(b/1).
This also fixes the orientation of the comparison in principalIteration. -/
def principalIterationGenerators : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w) (F : Type z)
    [CommRing A] [CommRing B] [CommRing C] [CommRing F]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra A F] [Algebra B F] [Algebra C F]
    [IsScalarTower A B F] [IsScalarTower A C F] [IsScalarTower B C F]
    (g h : B) [IsLocalization.Away g C]
    [IsLocalization.Away (algebraMap B C h) F],
    letI : IsLocalization.Away (g * h) F := IsLocalization.Away.mul' C F g h
    ∀ b : B,
      localizationComparison A B F (Submonoid.powers (g * h))
          (1 ⊗ₜ KaehlerDifferential.D A B b) =
        KaehlerDifferential.D A F (algebraMap B F b) ∧
      localizationComparison A C F (Submonoid.powers (algebraMap B C h))
          (1 ⊗ₜ localizationComparison A B C (Submonoid.powers g)
            (1 ⊗ₜ KaehlerDifferential.D A B b)) =
        KaehlerDifferential.D A F (algebraMap B F b)

section BaseChange
variable (A : Type u) (A' : Type v) (B : Type w) (C : Type z)
    (T : Type t) (U : Type q)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing C] [CommRing T] [CommRing U]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' C] [Algebra B C]
    [IsScalarTower A A' C] [IsScalarTower A B C]
    [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    [Algebra A U] [Algebra A' U] [Algebra B U] [Algebra C U] [Algebra T U]
    [IsScalarTower A A' U] [IsScalarTower A B U] [IsScalarTower A C U]
    [IsScalarTower A T U] [IsScalarTower A' C U]
    [IsScalarTower B C U] [IsScalarTower B T U]
    [Algebra.IsPushout A A' B C]
    (g : B) [IsLocalization.Away g T]
    [IsLocalization.Away (algebraMap B C g) U]

include B C g in
/-- Localization commutes with ring base change. This is proved from the
localization universal property and pasting of pushouts, not an extra
hypothesis on the base map A → A'. -/
theorem localizedPushout : Algebra.IsPushout A A' T U := by
  have : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers g)) U := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization.Away (algebraMap B C g) U)
  have : Algebra.IsPushout B C T U :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers g) T C U
  have : Algebra.IsPushout A B A' C := Algebra.IsPushout.symm inferInstance
  have : Algebra.IsPushout B T C U := Algebra.IsPushout.symm inferInstance
  exact Algebra.IsPushout.symm
    ((Algebra.IsPushout.comp_iff A B A' C (T := T)).mpr inferInstance)

/-- The square of KD-17 isomorphisms and principal restriction maps commutes.
Both paths start at U ⊗_B Ω(B/A); the inverses of cancelBaseChange are precisely
the canonical identifications of the two iterated scalar extensions.
C is any model of A' ⊗_A B and U is its principal localization, so this
includes every base change and every principal open. -/
def baseChangeRestrictionAt : Prop :=
  letI : Algebra.IsPushout A A' T U := localizedPushout A A' B C T U g
  ∀ x : U ⊗[B] KaehlerDifferential A B,
    localizationComparison A' C U (Submonoid.powers (algebraMap B C g))
      ((baseChangeEquivValue A A' B C).toLinearMap.baseChange U
        ((AlgebraTensorModule.cancelBaseChange B C U U (KaehlerDifferential A B)).symm x)) =
    baseChangeEquivValue A A' T U
      ((localizationComparison A B T (Submonoid.powers g)).toLinearMap.baseChange U
        ((AlgebraTensorModule.cancelBaseChange B T U U (KaehlerDifferential A B)).symm x))

end BaseChange

/-- Principal restriction is natural under every change of the base ring. -/
def baseChangeRestriction : Prop :=
  ∀ (A : Type u) (A' : Type v) (B : Type w) (C : Type z)
    (T : Type t) (U : Type q)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing C] [CommRing T] [CommRing U]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' C] [Algebra B C]
    [IsScalarTower A A' C] [IsScalarTower A B C]
    [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    [Algebra A U] [Algebra A' U] [Algebra B U] [Algebra C U] [Algebra T U]
    [IsScalarTower A A' U] [IsScalarTower A B U] [IsScalarTower A C U]
    [IsScalarTower A T U] [IsScalarTower A' C U]
    [IsScalarTower B C U] [IsScalarTower B T U]
    [Algebra.IsPushout A A' B C]
    (g : B) [IsLocalization.Away g T]
    [IsLocalization.Away (algebraMap B C g) U],
    baseChangeRestrictionAt A A' B C T U g

end
end Specs.AdvCommAlg.Etale.AffineDifferentialCompatibility
