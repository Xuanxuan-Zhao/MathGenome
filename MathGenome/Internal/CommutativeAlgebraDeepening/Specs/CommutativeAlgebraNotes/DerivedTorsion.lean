import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DerivedTorsionExtComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalCohomologyExactSequence

/-! Theorem 1.2, including the compatibility of the Ext comparison with the
cochain connecting homomorphism. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ZeroObject

namespace Specs.CommutativeAlgebraNotes.DerivedTorsion

open IdealTorsion DerivedTorsionExtComparison LocalCohomologyExactSequence

universe v u

set_option linter.checkUnivs false

noncomputable section

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The stagewise covariant boundary given by the Yoneda class of the row. -/
def extStageBoundary (I : Ideal R) {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (q n : ℕ) :
    extStage I q S.X₃ n ⟶ extStage I (q + 1) S.X₁ n :=
  ModuleCat.ofHom (hS.extClass.postcompOfLinear R (powerQuotient I n) rfl)

private lemma extStageBoundary_transition (I : Ideal R) {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (q : ℕ) {m n : ℕ} (f : m ⟶ n) :
    ((extPowerDiagram I q).map f).app S.X₃ ≫ extStageBoundary I hS q n =
      extStageBoundary I hS q m ≫ ((extPowerDiagram I (q + 1)).map f).app S.X₁ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Ext.comp_assoc (Ext.mk₀ (powerQuotientMap I (leOfHom f))) x hS.extClass
    (zero_add q) rfl (by simp)

/-- The boundary induced by the compatible Ext boundaries over the positive powers. -/
def extPowerBoundary (I : Ideal R) {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (q : ℕ) :
    (extPowerColimit I q).obj S.X₃ ⟶ (extPowerColimit I (q + 1)).obj S.X₁ :=
  (isColimitOfPreserves ((evaluation _ _).obj S.X₃)
    (colimit.isColimit (extPowerDiagram I q))).desc
    { pt := (extPowerColimit I (q + 1)).obj S.X₁
      ι :=
        { app := fun n => extStageBoundary I hS q n ≫ (extPowerι I (q + 1) n).app S.X₁
          naturality := fun m n f => by
            change ((extPowerDiagram I q).map f).app S.X₃ ≫
              extStageBoundary I hS q n ≫ (extPowerι I (q + 1) n).app S.X₁ =
                (extStageBoundary I hS q m ≫ (extPowerι I (q + 1) m).app S.X₁) ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, extStageBoundary_transition, Category.assoc]
            congr 1
            exact NatTrans.congr_app (colimit.w (extPowerDiagram I (q + 1)) f) S.X₁ } }

/-- The tower of Ext functors, with zero stages in negative degrees. -/
def extPowerGradedDiagram (I : Ideal R) (q : ℤ) : ℕ ⥤ ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  match q with
  | .ofNat n => extPowerDiagram I n
  | .negSucc _ => (CategoryTheory.Functor.const ℕ).obj 0

/-- The integer-graded Ext limit, taken over the positive ideal powers. -/
def extPowerGraded (I : Ideal R) (q : ℤ) : ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  colimit (extPowerGradedDiagram I q)

def extPowerGradedType :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R], Ideal R → ℤ →
    (ModuleCat.{v} R ⥤ ModuleCat.{v} R)

def extStageBoundaryType :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    {S : ShortComplex (ModuleCat.{v} R)}, S.ShortExact → ∀ q n : ℕ,
      extStage I q S.X₃ n ⟶ extStage I (q + 1) S.X₁ n

def extPowerBoundaryType :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    {S : ShortComplex (ModuleCat.{v} R)}, S.ShortExact → ∀ q : ℕ,
      (extPowerColimit I q).obj S.X₃ ⟶ (extPowerColimit I (q + 1)).obj S.X₁

-- The exported names denote the canonical constructions above.
abbrev extStageBoundaryValue : extStageBoundaryType.{v,u} := @extStageBoundary.{v,u}
abbrev extPowerBoundaryValue : extPowerBoundaryType.{v,u} := @extPowerBoundary.{v,u}
abbrev extPowerGradedValue : extPowerGradedType.{v,u} := @extPowerGraded.{v,u}

def extPowerBoundaryOnStagesType : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact) (q n : ℕ),
      (extPowerι I q n).app S.X₃ ≫ extPowerBoundary I hS q =
        extStageBoundary I hS q n ≫ (extPowerι I (q + 1) n).app S.X₁

def localCohomologyDegreeType : Prop :=
  localCohomologyNonnegType.{v,u} ∧ localCohomologyNegType.{v,u}

/-- The Ext colimit comparison and its compatibility with the long exact sequence. -/
def extPowerBoundaryComparisonType : Prop :=
  ∃ α : extPowerComparisonType.{v,u},
    extPowerComparisonOnCocycles α ∧ extPowerZeroEdge α ∧
      ∀ {R : Type u} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
        {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact) (q : ℕ),
        boundary I hS (q : ℤ) ≫ (α I (q + 1)).hom.app S.X₁ =
          (α I q).hom.app S.X₃ ≫ extPowerBoundary I hS q

def gradedExtComparisonType : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (q : ℤ),
    Nonempty (localCohomology.{v} I q ≅ extPowerGraded I q)

def powerTorsionType : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (q : ℤ)
    (M : ModuleCat.{v} R) (x : (localCohomology I q).obj M),
    ∃ n : ℕ, 1 ≤ n ∧ ∀ a ∈ I ^ n, a • x = 0

end

end Specs.CommutativeAlgebraNotes.DerivedTorsion
