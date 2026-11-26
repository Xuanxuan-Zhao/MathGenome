import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.QuasiIso

/-! The linear Hom complex into the residue-field injective hull in degree zero. -/

noncomputable section

open CategoryTheory Opposite
open CochainComplex.HomComplex

namespace CommutativeAlgebraNotes.ExactDualCochainCohomologySpecs

open MatlisDualFunctorSpecs

universe u v

section LinearHom

variable {R : Type u} [CommRing R]
variable {C : Type*} [Category.{v} C] [Preadditive C] [Linear R C]
variable {U V J K : CochainComplex C ℤ}

/-- Precomposition on every degree of the linear Hom complex. -/
def precomp (f : U ⟶ V) (J : CochainComplex C ℤ) :
    CochainComplex.linearHomComplex R V J ⟶ CochainComplex.linearHomComplex R U J where
  f i := ModuleCat.ofHom
    { toFun := fun z => (Cochain.ofHom f).comp z (zero_add i)
      map_add' := fun _ _ => Cochain.comp_add _ _ _ _
      map_smul' := fun _ _ => Cochain.comp_smul _ _ _ _ }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_ofHom_comp f z j

/-- Postcomposition on every degree of the linear Hom complex. -/
def postcomp (U : CochainComplex C ℤ) (g : J ⟶ K) :
    CochainComplex.linearHomComplex R U J ⟶ CochainComplex.linearHomComplex R U K where
  f i := ModuleCat.ofHom
    { toFun := fun z => z.comp (Cochain.ofHom g) (add_zero i)
      map_add' := fun _ _ => Cochain.add_comp _ _ _ _
      map_smul' := fun _ _ => Cochain.smul_comp _ _ _ _ }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_comp_ofHom z g j

end LinearHom

variable {R : Type u} [CommRing R] [IsLocalRing R]

abbrev hull (E : residueFieldEnvelopeValue R) : ModuleCat.{u} R :=
  ModuleCat.of R E.carrier

abbrev hullInDegreeZero (E : residueFieldEnvelopeValue R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (hull E)

def dualComplexType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R], residueFieldEnvelopeValue R →
    (CochainComplex (ModuleCat.{u} R) ℤ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ

/-- The genuine linear Hom complex with the Matlis hull as its single-term target. -/
def dualComplexValue (E : residueFieldEnvelopeValue R) :
    (CochainComplex (ModuleCat.{u} R) ℤ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj U := CochainComplex.linearHomComplex R U.unop (hullInDegreeZero E)
  map f := precomp f.unop (hullInDegreeZero E)
  map_id _ := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Cochain.id_comp z
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    simp [precomp, Cochain.zero_cochain_comp_v _ _ p q hpq]

/-- The complex map induced by an endomorphism of the target hull. -/
def hullPostcomp (E : residueFieldEnvelopeValue R)
    (U : CochainComplex (ModuleCat.{u} R) ℤ) (a : hull E ⟶ hull E) :
    (dualComplexValue E).obj (op U) ⟶ (dualComplexValue E).obj (op U) :=
  postcomp U ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map a)

/-- The map on the Matlis dual induced by an endomorphism of the target hull. -/
def dualPostcomp (E : residueFieldEnvelopeValue R) (X : ModuleCat.{u} R)
    (a : hull E ⟶ hull E) :
    (matlisDualValue E).obj (op X) ⟶ (matlisDualValue E).obj (op X) :=
  ModuleCat.ofHom (LinearMap.llcomp R X E.carrier E.carrier a.hom)

abbrev dualCohomology (E : residueFieldEnvelopeValue R) (j : ℤ) :=
  dualComplexValue E ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) j

abbrev cohomologyDual (E : residueFieldEnvelopeValue R) (j : ℤ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-j)).op ⋙ matlisDualValue E

/-- The natural comparison commutes with postcomposition by every hull endomorphism,
in particular the scalar operators when the hull has its completed scalar action. -/
def comparison (E : residueFieldEnvelopeValue R) (j : ℤ)
    (e : dualCohomology E j ≅ cohomologyDual E j) : Prop :=
  ∀ (U : CochainComplex (ModuleCat.{u} R) ℤ) (a : hull E ⟶ hull E),
    HomologicalComplex.homologyMap (hullPostcomp E U a) j ≫ e.hom.app (op U) =
      e.hom.app (op U) ≫ dualPostcomp E (U.homology (-j)) a

def exactDualCohomology : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R) (j : ℤ),
    ∃ e : dualCohomology E j ≅ cohomologyDual E j, comparison E j e

def dualPreservesQuasiIso : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    {U V : CochainComplex (ModuleCat.{u} R) ℤ} (f : U ⟶ V),
    QuasiIso f → QuasiIso ((dualComplexValue E).map f.op)

end CommutativeAlgebraNotes.ExactDualCochainCohomologySpecs
