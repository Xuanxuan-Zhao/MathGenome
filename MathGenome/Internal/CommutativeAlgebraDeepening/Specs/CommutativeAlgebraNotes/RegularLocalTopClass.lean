import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.KoszulTower
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RegularLocalRing.Defs

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped TensorProduct

namespace Specs.CommutativeAlgebraNotes.RegularLocalTopClass

universe u

open AugmentedCechComplex (Selection coefficients factor complex headDegree product)
open KoszulTower (denominator fraction localizationTensorIso)

noncomputable section

variable {R : Type u} [CommRing R]

/-- Select every position of the ordered list. -/
def fullSelection : (n : ℕ) → (q : ℤ) → q = n → Selection n q
  | 0, q, h => ⟨by simpa using h⟩
  | n + 1, q, h => ⟨true, fullSelection n (q - 1) (by omega)⟩

private def localizationTensorEquiv (r p : R) :
    (Localization.Away r ⊗[R] Localization.Away p) ≃ₐ[R] Localization.Away (r * p) := by
  let A := Localization.Away r
  let B := Localization.Away p
  have : IsLocalization.Away (r * p) (A ⊗[R] B) :=
    IsLocalization.Away.mul' A (A ⊗[R] B) r p
  exact IsLocalization.algEquiv (Submonoid.powers (r * p)) _ _

/-- The all-selected summand, using the canonical tensor isomorphism of principal
localizations at each step. -/
def topLocalizationInclusion : (rs : List R) → (q : ℤ) → (h : q = rs.length) →
    ModuleCat.of R (Localization.Away (product R rs (fullSelection rs.length q h))) ⟶
      (complex R rs).X q
  | [], q, h =>
      (IsLocalization.atOne R (Localization.Away (1 : R))).symm.toLinearEquiv.toModuleIso.hom ≫
        (singleObjXIsoOfEq (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R)) q (by simpa using h)).inv
  | r :: rs, q, h => by
      have h' : q - 1 = (rs.length : ℤ) := by simp at h; omega
      let p := product R rs (fullSelection rs.length (q - 1) h')
      exact (localizationTensorEquiv r p).toLinearEquiv.toModuleIso.inv ≫
        ((factor R r).X 1 ◁ topLocalizationInclusion rs (q - 1) h') ≫
        ιTensorObj (factor R r) (complex R rs) 1 (q - 1) q (by omega)

/-- The Čech class represented by the fraction with numerator one and the product
of all parameters in the denominator. -/
def cechFractionClass (rs : List R)
    (h : (coefficients R rs (ModuleCat.of R R)).d (rs.length : ℤ) ((rs.length : ℤ) + 1) = 0) :
    (coefficients R rs (ModuleCat.of R R)).homology (rs.length : ℤ) :=
  let M := ModuleCat.of R R
  let q : ℤ := rs.length
  let K := coefficients R rs M
  let p := product R rs (fullSelection rs.length q rfl)
  (fraction M p 0 ≫ (localizationTensorIso M p).hom ≫
    (topLocalizationInclusion rs q rfl ▷ M) ≫
    ιTensorObj (complex R rs) ((single (ModuleCat R) (.up ℤ) 0).obj M) q 0 q (add_zero q) ≫
    K.pOpcycles q ≫ (K.isoHomologyι q (q + 1) ((ComplexShape.up ℤ).next_eq' (show q + 1 = q + 1 from rfl)) h).inv) (1 : R)

/-- Nonvanishing of the specific top class in local cohomology. The list generates
the maximal ideal and has length equal to the dimension, so it is minimal. -/
def TopClassNonzero : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] (rs : List R),
    ringKrullDim R = (rs.length : WithBot ℕ∞) →
    Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R →
    ∃ (e : IdealTorsion.localCohomology (IsLocalRing.maximalIdeal R) (rs.length : ℤ) ≅
        (single (ModuleCat.{u} R) (.up ℤ) 0 ⋙ AugmentedCechComplex.tensorFunctor R rs) ⋙
          homologyFunctor (ModuleCat.{u} R) (.up ℤ) (rs.length : ℤ))
      (h : (coefficients R rs (ModuleCat.of R R)).d (rs.length : ℤ) ((rs.length : ℤ) + 1) = 0),
      e.inv.app (ModuleCat.of R R) (cechFractionClass rs h) ≠ 0

end

end Specs.CommutativeAlgebraNotes.RegularLocalTopClass
