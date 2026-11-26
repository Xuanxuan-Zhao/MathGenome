import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.InjectiveEnvelope

noncomputable section

open CategoryTheory Opposite

namespace CommutativeAlgebraNotes

universe u v w

/-- A residue-field hull retains the actual inclusion and its envelope properties. -/
abbrev ResidueFieldEnvelope (R : Type u) [CommRing R] [IsLocalRing R] :=
  MatlisDualFunctorSpecs.residueFieldEnvelopeValue R

theorem residueFieldEnvelope_exists (R : Type u) [CommRing R] [IsLocalRing R] :
    Nonempty (ResidueFieldEnvelope R) :=
  AdvCommAlg.Gorenstein.exists_injectiveEnvelope R (IsLocalRing.ResidueField R)

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem residueFieldEnvelope_essential (E : ResidueFieldEnvelope R)
    (N : Submodule R E.carrier) (hN : N ≠ ⊥) :
    N ⊓ LinearMap.range E.inclusion ≠ ⊥ :=
  E.isEnvelope.essential N hN

/-- Two choices of hull admit an isomorphism extending the identity on the residue field. -/
theorem residueFieldEnvelope_equiv (E F : ResidueFieldEnvelope R) :
    ∃ e : E.carrier ≃ₗ[R] F.carrier, e.toLinearMap.comp E.inclusion = F.inclusion :=
  AdvCommAlg.Gorenstein.injectiveEnvelope_equiv _ _ E.isEnvelope F.isEnvelope

/-- The linear functionals on X with values in the displayed residue-field hull. -/
abbrev MatlisDualModule (E : ResidueFieldEnvelope R) (X : Type v)
    [AddCommGroup X] [Module R X] :=
  MatlisDualFunctorSpecs.matlisDualModuleValue E X

/-- The dual map is precomposition. -/
def matlisDualMap (E : ResidueFieldEnvelope R) {X : Type v} {Y : Type w}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) : MatlisDualModule E Y →ₗ[R] MatlisDualModule E X :=
  MatlisDualFunctorSpecs.matlisDualMapValue E f

@[simp]
theorem matlisDualMap_apply (E : ResidueFieldEnvelope R) {X : Type v} {Y : Type w}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (g : MatlisDualModule E Y) (x : X) :
    matlisDualMap E f g x = g (f x) :=
  rfl

/-- The contravariant Matlis dual functor for a fixed residue-field hull. -/
def MatlisDual (E : ResidueFieldEnvelope R) : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
  MatlisDualFunctorSpecs.matlisDualValue E

@[simp]
theorem matlisDual_obj (E : ResidueFieldEnvelope R) (X : (ModuleCat.{u} R)ᵒᵖ) :
    (MatlisDual E).obj X = ModuleCat.of R (MatlisDualModule E X.unop) :=
  rfl

@[simp]
theorem matlisDual_map_hom (E : ResidueFieldEnvelope R)
    {X Y : (ModuleCat.{u} R)ᵒᵖ} (f : X ⟶ Y) :
    ((MatlisDual E).map f).hom = matlisDualMap E f.unop.hom :=
  rfl

instance matlisDual_additive (E : ResidueFieldEnvelope R) : (MatlisDual E).Additive where
  map_add := by
    intro X Y f g
    exact ModuleCat.hom_ext (LinearMap.ext fun h => LinearMap.ext fun _ => h.map_add _ _)

instance matlisDual_linear (E : ResidueFieldEnvelope R) : (MatlisDual E).Linear R where
  map_smul := by
    intro X Y f r
    exact ModuleCat.hom_ext (LinearMap.ext fun h => LinearMap.ext fun _ => h.map_smul r _)

/-- Multiplication in the target agrees with precomposition by multiplication in the source. -/
theorem matlisDual_scalar (E : ResidueFieldEnvelope R) {X : Type v}
    [AddCommGroup X] [Module R X] (r : R) (f : MatlisDualModule E X) :
    r • f = matlisDualMap E (LinearMap.lsmul R X r) f :=
  LinearMap.ext fun x => (f.map_smul r x).symm

/-- Evaluation sending x to the functional f ↦ f x. -/
def matlisEvaluation (E : ResidueFieldEnvelope R) (X : Type v) [AddCommGroup X] [Module R X] :
    X →ₗ[R] MatlisDualModule E (MatlisDualModule E X) :=
  MatlisDualFunctorSpecs.matlisEvaluationValue E X

@[simp]
theorem matlisEvaluation_apply (E : ResidueFieldEnvelope R) {X : Type v}
    [AddCommGroup X] [Module R X] (x : X) (f : MatlisDualModule E X) :
    matlisEvaluation E X x f = f x :=
  rfl

/-- The natural transformation from the identity to the double Matlis dual. -/
def matlisBidualEvaluation (E : ResidueFieldEnvelope R) :
    𝟭 (ModuleCat.{u} R) ⟶ (MatlisDual E).rightOp ⋙ MatlisDual E :=
  MatlisDualFunctorSpecs.matlisBidualEvaluationValue E

@[simp]
theorem matlisBidualEvaluation_app (E : ResidueFieldEnvelope R) (X : ModuleCat.{u} R) :
    ((matlisBidualEvaluation E).app X).hom = matlisEvaluation E X :=
  rfl

/-- Postcomposition with an isomorphism of hulls identifies their Matlis dual functors. -/
def matlisDualIso {E F : ResidueFieldEnvelope R} (e : E.carrier ≃ₗ[R] F.carrier) :
    MatlisDual E ≅ MatlisDual F :=
  MatlisDualFunctorSpecs.matlisDualIsoValue e

@[simp]
theorem matlisDualIso_hom_app {E F : ResidueFieldEnvelope R}
    (e : E.carrier ≃ₗ[R] F.carrier) (X : (ModuleCat.{u} R)ᵒᵖ) :
    ((matlisDualIso (E := E) (F := F) e).hom.app X).hom =
      (e.congrRight : MatlisDualModule E X.unop ≃ₗ[R] MatlisDualModule F X.unop).toLinearMap :=
  rfl

theorem mem_socle_iff {X : Type u} [AddCommGroup X] [Module R X] (x : X) :
    x ∈ AdvCommAlg.Depth.Socle R X ↔ ∀ r ∈ IsLocalRing.maximalIdeal R, r • x = 0 := by
  simp only [Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]

theorem residue_smul_socle {X : Type u} [AddCommGroup X] [Module R X] (r : R)
    (x : AdvCommAlg.Depth.Socle R X) : IsLocalRing.residue R r • x = r • x :=
  Submodule.torsionBySet.mk_smul (IsLocalRing.maximalIdeal R) r x

end CommutativeAlgebraNotes
