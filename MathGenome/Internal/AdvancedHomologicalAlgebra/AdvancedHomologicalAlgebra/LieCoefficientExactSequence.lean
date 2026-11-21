import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LieCoefficientExactSequence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtExactSequences
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
import MathGenome.Internal.AlgebraCore.P103.Ch11.VanishingAndFlatness
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! The all-degree coefficient sequence of the explicit CE complex. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence P103.Specs.Ch11.ExtTorDefinitions
namespace AdvancedHomologicalAlgebra.CE.Coefficients
open scoped TensorProduct
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)

/-- The models exist with the differential already constructed in HA-A06. -/
theorem models : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.modelsExpected.{u,v,w} k g d hc := by
  intro hd M
  let C := cochainData k g M ⟨d, hd, hc⟩
  exact ⟨{
    δ := C.differential
    square := C.squared
    evaluation := Ext.evaluationIso k g M d hc C
    eval := C.evaluate_tmul
    formula := C.formula }⟩

theorem construction : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.constructionExpected.{u,v,w} k g := by
  intro hg
  letI := hg
  exact ⟨boundary k g, boundary_augmented k g, boundary_formula k g,
    Ext.boundary_exact k g, models k g (boundary k g) (boundary_augmented k g)
      (boundary_formula k g)⟩

namespace Model
variable {k g d hc}
variable {M N P : ModuleCat.{w} (U k g)}

@[simp] theorem map_apply (C : Model k g d hc M) (D : Model k g d hc N)
    (h : M ⟶ N) (n : ℕ) (f : W k g n →ₗ[k] M) :
    ((C.map D h).f n).hom f = (h.hom.restrictScalars k).comp f := by
  apply LinearMap.ext
  intro z
  change (D.evaluation.hom.f n).hom
    (h.hom.comp ((C.evaluation.inv.f n).hom f)) z = h.hom (f z)
  rw [D.eval]
  have hi := congrArg (fun a => (a.f n).hom) C.evaluation.inv_hom_id
  have hf := LinearMap.congr_fun hi f
  have hz := LinearMap.congr_fun hf z
  change (C.evaluation.hom.f n).hom ((C.evaluation.inv.f n).hom f) z = f z at hz
  rw [C.eval] at hz
  exact congrArg h.hom hz

@[simp] theorem map_id (C : Model k g d hc M) : C.map C (𝟙 M) = 𝟙 C.complex := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  simpa using map_apply C C (𝟙 M) n f

@[simp] theorem map_comp (C : Model k g d hc M) (D : Model k g d hc N)
    (E : Model k g d hc P) (h : M ⟶ N) (j : N ⟶ P) :
    C.map E (h ≫ j) = C.map D h ≫ D.map E j := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change W k g n →ₗ[k] M at f
  change ((C.map E (h ≫ j)).f n).hom f =
    ((D.map E j).f n).hom (((C.map D h).f n).hom f)
  rw [map_apply C E (h ≫ j) n f, map_apply C D h n f, map_apply D E j]
  rfl

/-- Evaluation intertwines coefficient maps as actual complex maps. -/
theorem map_evaluation (C : Model k g d hc M) (D : Model k g d hc N) (h : M ⟶ N) :
    C.map D h ≫ D.evaluation.inv =
      C.evaluation.inv ≫ homPostMap (Ext.chain k g d hc) h.hom := by
  simp [map]
end Model

theorem map_formula : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.mapExpected.{u,v,w} k g d hc := by
  intro M N C D h n f
  exact Model.map_apply C D h n f

/-- Each exterior power is free, so lifting linear cochains requires neither
finite rank nor a splitting of the coefficient sequence as U-modules. -/
theorem degreewise : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.degreewiseExpected.{u,v,w} k g d hc := by
  intro hg M N P C D E i p hi he hp n
  letI := hg
  have hfree : Module.Free k (W k g n) := inferInstance
  letI := hfree
  obtain ⟨hinj, hex⟩ := P103.HomTensorExactness.homCovariant k M N P
    (W k g n) (i.hom.restrictScalars k) (p.hom.restrictScalars k) hi he
  refine ⟨?_, ?_, ?_⟩
  · intro f f' h
    apply hinj
    rw [Model.map_apply C D i n f, Model.map_apply C D i n f'] at h
    exact h
  · intro f
    change ((D.map E p).f n).hom f = 0 ↔ ∃ a, ((C.map D i).f n).hom a = f
    rw [Model.map_apply D E p n f]
    constructor
    · intro hf
      obtain ⟨a, ha⟩ := (hex f).mp hf
      exact ⟨a, (Model.map_apply C D i n a).trans ha⟩
    · rintro ⟨a, ha⟩
      apply (hex f).mpr
      exact ⟨a, (Model.map_apply C D i n a).symm.trans ha⟩
  · intro f
    obtain ⟨l, hl⟩ := Module.projective_lifting_property
      (p.hom.restrictScalars k) f hp
    exact ⟨l, (Model.map_apply D E p n l).trans hl⟩

theorem sequence : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.sequenceExpected.{u,v,w} k g d hc := by
  intro hg M N P C D E i p hi he hp
  have hs := degreewise k g d hc hg M N P C D E i p hi he hp
  have hd := fun n => P103.Ch10.HomologySequence.sequence
    (C.map D i) (D.map E p) hs n (n+1) (by rfl)
  choose δ hδ huniq using hd
  exact ⟨δ, (P103.Ch10.HorseshoeNaturality.cochain_zero_exact _ _ hs).1, hδ⟩

theorem lifted_boundary : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.liftedExpected.{u,v,w} k g d hc := by
  intro hg M N P C D E i p hi hex hp n δ hδ z b hb
  have hs := degreewise k g d hc hg M N P C D E i p hi hex hp
  have hb' : ((D.map E p).f n).hom b = z.val :=
    (Model.map_apply D E p n b).trans hb
  have hz : ((D.map E p).f (n+1)).hom ((D.complex.d n (n+1)).hom b) = 0 := by
    rw [← P103.Ch10.HomologySequence.comm_apply, hb']
    exact (P103.Ch10.HomologySequence.cycle_iff E.complex (show (ComplexShape.up ℕ).Rel n (n+1) from rfl) z.val).mp z.property
  obtain ⟨a, ha⟩ := ((hs (n+1)).2.1 _).mp hz
  have haz : a ∈ cycles C.complex (n+1) := by
    change (C.complex.d (n+1) ((ComplexShape.up ℕ).next (n+1))).hom a = 0
    apply (hs ((ComplexShape.up ℕ).next (n+1))).1
    rw [map_zero, ← P103.Ch10.HomologySequence.comm_apply, ha,
      P103.Ch10.HomologySequence.square_zero]
  refine ⟨⟨a, haz⟩, ?_, hδ z b ⟨a, haz⟩ hb' ha⟩
  intro x
  have hx := LinearMap.congr_fun ha (wedge k g (n+1) x)
  rw [Model.map_apply C D i (n+1) a] at hx
  have hx' : i.hom (a (wedge k g (n+1) x)) =
      D.δ n b (wedge k g (n+1) x) := by
    simpa only [Model.complex, Ext.cochain, CochainComplex.of_d,
      ModuleCat.hom_ofHom, AddMonoidHom.coe_toIntLinearMap,
      LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, LinearMap.restrictScalars_apply] using hx
  exact hx'.trans (D.formula n b x)

theorem naturality : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.naturalityExpected.{u,v,w} k g d hc := by
  intro hg M N P M' N' P' C D E C' D' E' i p i' p' a b c
    hi he hp hi' he' hp' hab hbc n δ ε hδ hε
  apply P103.Ch10.HomologySequence.naturality
    (C.map D i) (D.map E p) (C'.map D' i') (D'.map E' p')
    (C.map C' a) (D.map D' b) (E.map E' c) ?_ ?_
    (degreewise k g d hc hg M N P C D E i p hi he hp)
    (degreewise k g d hc hg M' N' P' C' D' E' i' p' hi' he' hp')
    n (n+1) (by rfl) δ ε hδ hε
  · rw [← Model.map_comp, ← Model.map_comp, hab]
  · rw [← Model.map_comp, ← Model.map_comp, hbc]

attribute [local instance] Ext.trivialModule

/-- The genuine CE resolution is projective in every degree. -/
theorem resolution_projective [Module.Free k g] (he : Ext.AugmentedExact k g d) :
    (Ext.resolution k g d hc he).IsProjective := by
  intro n
  change Module.Projective (U k g) (V k g n)
  haveI := term_free k g n
  infer_instance

/-- All three comparison squares follow from naturality of the positive
lift/differentiate connector applied to inverse evaluation. -/
theorem ext_compatibility : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.extExpected.{u,v,w} k g d hc := by
  intro hg he M N P C D E i p hi hex hp n δ ε hδ hε
  letI := hg
  have hs := degreewise k g d hc hg M N P C D E i p hi hex hp
  have ht := P103.Ch11.ExtExactSequences.second_degreewise_exact
    (A := @ModuleCat.of (U k g) _ k _ (Ext.trivialModule k g))
    (Ext.resolution k g d hc he) (resolution_projective k g d hc he) i p hi hex hp
  have h := P103.Ch10.HomologySequence.naturality
    (C.map D i) (D.map E p)
    (homPostMap (Ext.chain k g d hc) i.hom) (homPostMap (Ext.chain k g d hc) p.hom)
    C.evaluation.inv D.evaluation.inv E.evaluation.inv
    (Model.map_evaluation C D i) (Model.map_evaluation D E p)
    hs ht n (n+1) (by rfl) δ ε hδ hε
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Injective resolution balance preserves this same boundary, including its
sign, rather than merely identifying the cohomology group objects. -/
theorem derived_compatibility : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.derivedExpected.{u,v,w} k g d hc := by
  intro hg he M N P C D E i p hi hex hp
  letI := Ext.trivialModule k g
  intro L T H n δ ε hδ hε eT eL heT heL
  letI := hg
  let R := Ext.resolution k g d hc he
  have hR := resolution_projective k g d hc he
  have ht := P103.Ch11.ExtExactSequences.second_degreewise_exact
    (A := ModuleCat.of (U k g) k) R hR i p hi hex hp
  obtain ⟨τ, hτ, _⟩ := P103.Ch10.HomologySequence.sequence
    (homPostMap R.complex i.hom) (homPostMap R.complex p.hom) ht n (n+1) (by rfl)
  have hcomp := (ext_compatibility k g d hc hg he M N P C D E i p hi hex hp
    n δ τ hδ hτ.1).2.2
  have hbal := P103.Ch11.ExtExactSequences.balance_connecting
    (U k g) (ModuleCat.of (U k g) k) R hR M N P i p hi hex hp L T H n τ ε
    hτ.1 hε eT eL heT heL
  apply LinearMap.ext
  intro x
  apply (C.comparison (n+1)).injective
  have hc' := LinearMap.congr_fun hcomp ((E.comparison n).symm (eT x))
  have hb' := LinearMap.congr_fun hbal x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at hc' hb' ⊢
  exact hb'.trans hc'.symm

end AdvancedHomologicalAlgebra.CE.Coefficients

open CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch11.ExtExactSequences P103.Specs.Ch11.ExtBalance
namespace AdvancedHomologicalAlgebra.CE.Coefficients.Derived
universe r a s h h'
variable (R : Type r) [Ring R] (X : ModuleCat.{a} R)
  (P : LeftResolution R X) (hP : P.IsProjective)

include hP in
theorem data_exists : Nonempty (OrdinaryData.{r,a,s} R X P) := by
  let E := fun n => (P103.Ch11.ExtTorDefinitions.ext_bifunctorial.{r,a,max r a s} R n).some
  have ex : ∀ (S : ShortComplex (ModuleCat.{max r a s} R)) (hS : S.ShortExact) n,
      ∃ δ : ExtWith P S.X₃ n →ₗ[ℤ] ExtWith P S.X₁ (n+1),
        SecondConnecting (A := X) P S.f S.g n δ ∧ SecondExact (A := X) P S.f S.g n δ := by
    intro S hS n
    obtain ⟨δ, hδ, _⟩ := P103.Ch10.HomologySequence.sequence
      (homPostMap P.complex S.f.hom) (homPostMap P.complex S.g.hom)
      (P103.Ch11.ExtExactSequences.second_degreewise_exact P hP S.f S.g
        hS.moduleCat_injective_f ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
        hS.moduleCat_surjective_g) n (n+1) (by rfl)
    exact ⟨δ, hδ⟩
  choose δ hδ using ex
  exact ⟨⟨E, fun hS n => δ _ hS n, fun hS n => (hδ _ hS n).1,
    fun hS n => (hδ _ hS n).2⟩⟩

variable {R X P hP}

lemma ordinary_arrow (D : OrdinaryData.{r,a,s} R X P) {M N : (ModuleCat.{max r a s} R)} (f : M ⟶ N) (n : ℕ) :
    ((D.system hP).value n).map f = ModuleCat.ofHom (homologyMap (homPostMap P.complex f.hom) n) := by
  apply ModuleCat.hom_ext
  exact ((P103.Ch11.ExtExactSequences.coefficient_arrows R n (D.maps n)).2 X P hP M N f).symm

lemma exactPair_of_function {V W Z : (ModuleCat.{max r a s} ℤ)} (f : V ⟶ W) (g : W ⟶ Z)
    (he : Function.Exact f.hom g.hom) : ExactPair f g := by
  have hz : f ≫ g = 0 := by
    apply ModuleCat.hom_ext
    ext x
    exact he.apply_apply_eq_zero x
  exact ⟨hz, (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr (LinearMap.exact_iff.mp he).symm⟩

lemma ordinary_cohomological (D : OrdinaryData.{r,a,s} R X P) : IsCohomological (D.system hP) where
  additive n := by
    change ((D.maps n).coefficients ⟨P, hP⟩).Additive
    infer_instance
  naturality hS hT f n := by
    apply ModuleCat.hom_ext
    exact (P103.Ch11.ExtExactSequences.second_natural R n (D.maps n) (D.maps (n+1))
      X X P P hP hP (𝟙 X) _ _ _ _ _ _ _ _ _ _ f.τ₁ f.τ₂ f.τ₃
      hS.moduleCat_injective_f (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _ |>.mp hS.exact)
      hS.moduleCat_surjective_g hT.moduleCat_injective_f
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _ |>.mp hT.exact)
      hT.moduleCat_surjective_g f.comm₁₂.symm f.comm₂₃.symm
      (D.boundary hS n) (D.boundary hT n) (D.connecting hS n) (D.connecting hT n)).symm
  exact₁ hS n := by
    rw [ordinary_arrow]
    exact exactPair_of_function.{r,a,s} _ _ (D.exactness hS n).2.2
  exact₂ hS n := by
    rw [ordinary_arrow, ordinary_arrow]
    exact exactPair_of_function.{r,a,s} _ _ (D.exactness hS n).1
  exact₃ hS n := by
    rw [ordinary_arrow]
    exact exactPair_of_function.{r,a,s} _ _ (D.exactness hS n).2.1
  mono_zero hS := by
    rw [ordinary_arrow]
    apply (ModuleCat.mono_iff_injective _).mpr
    apply (P103.Ch10.HorseshoeNaturality.cochain_zero_exact _ _
      (P103.Ch11.ExtExactSequences.second_degreewise_exact P hP _ _
        hS.moduleCat_injective_f (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _ |>.mp hS.exact)
        hS.moduleCat_surjective_g)).1

lemma ordinary_universal (D : OrdinaryData.{r,a,s} R X P) :
    IsUniversalCohomological (D.system hP) := by
  apply AdvancedHomologicalAlgebra.UniversalDeltaFunctors.universal_of_injective_vanishing
    (D.system hP) (ordinary_cohomological.{r,a,s} D)
  intro I hI n
  letI := Module.injective_module_of_injective_object R I
  haveI := P103.Ch11.VanishingAndFlatness.ext_injective.{r,a,max a s} R X I inferInstance P hP n
  change IsZero (ModuleCat.of ℤ (ExtWith P I (n+1)))
  exact (ModuleCat.isZero_iff_subsingleton).mpr inferInstance


lemma hom_preservesFiniteLimits : PreservesFiniteLimits (covariantHom (R := R) X : (ModuleCat.{max r a s} R) ⥤ (ModuleCat.{max r a s} ℤ)) := by
  let e : (covariantHom (R := R) X : (ModuleCat.{max r a s} R) ⥤ (ModuleCat.{max r a s} ℤ)) ⋙ forget (ModuleCat.{max r a s} ℤ) ≅
      coyoneda.obj (Opposite.op (ModuleCat.of R (ULift.{max r a s} X))) :=
    NatIso.ofComponents (fun M => Equiv.toIso ({
      toFun f := ModuleCat.ofHom {
        toFun x := f x.down
        map_add' x y := f.map_add x.down y.down
        map_smul' r x := f.map_smul r x.down }
      invFun f := {
        toFun x := f.hom (ULift.up x)
        map_add' x y := f.hom.map_add (ULift.up x) (ULift.up y)
        map_smul' r x := f.hom.map_smul r (ULift.up x) }
      left_inv f := by ext x; rfl
      right_inv f := by apply ModuleCat.hom_ext; ext x; rfl } :
      (X →ₗ[R] M) ≃ (ModuleCat.of R (ULift.{max r a s} X) ⟶ M)))
      (fun f => by ext x; rfl)
  haveI : PreservesLimits ((covariantHom (R := R) X : (ModuleCat.{max r a s} R) ⥤ (ModuleCat.{max r a s} ℤ)) ⋙ forget (ModuleCat.{max r a s} ℤ)) :=
    preservesLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget (ModuleCat.{max r a s} ℤ))

noncomputable def ordinaryZeroIso (D : OrdinaryData.{r,a,s} R X P) :
    (covariantHom (R := R) X : (ModuleCat.{max r a s} R) ⥤ (ModuleCat.{max r a s} ℤ)) ≅ (D.system hP).value 0 :=
  NatIso.ofComponents
    (fun M => (LinearEquiv.ofBijective (homClass P M)
      (P103.Ch11.ExtExactSequences.homClass_bijective P M)).toModuleIso)
    (by
      intro M N f
      rw [ordinary_arrow]
      apply ModuleCat.hom_ext
      ext x
      rfl)

def identityMorphism (T : CohomologicalSystem (ModuleCat.{max r a s} R) (ModuleCat.{max r a s} ℤ)) : CohomologicalMorphism T T where
  component n := 𝟙 _
  comm hS n := by simp

def composeMorphism {T U V : CohomologicalSystem (ModuleCat.{max r a s} R) (ModuleCat.{max r a s} ℤ)}
    (f : CohomologicalMorphism T U) (g : CohomologicalMorphism U V) :
    CohomologicalMorphism T V where
  component n := f.component n ≫ g.component n
  comm hS n := by
    simp only [NatTrans.comp_app]
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc]

lemma universal_comparison {T U : CohomologicalSystem (ModuleCat.{max r a s} R) (ModuleCat.{max r a s} ℤ)}
    (hT : IsCohomological T) (hU : IsCohomological U)
    (huT : IsUniversalCohomological T) (huU : IsUniversalCohomological U)
    (e : T.value 0 ≅ U.value 0) :
    ∃ φ : CohomologicalMorphism T U, φ.component 0 = e.hom ∧
      ∀ n, IsIso (φ.component n) := by
  obtain ⟨φ, hφ, _⟩ := huT U hU e.hom
  obtain ⟨ψ, hψ, _⟩ := huU T hT e.inv
  obtain ⟨idT, hidT, uniqT⟩ := huT T hT (𝟙 _)
  obtain ⟨idU, hidU, uniqU⟩ := huU U hU (𝟙 _)
  have hcompT : composeMorphism.{r,a,s} φ ψ = identityMorphism.{r,a,s} T := by
    apply (uniqT _ ?_).trans (uniqT _ rfl).symm
    change φ.component 0 ≫ ψ.component 0 = 𝟙 _
    rw [hφ, hψ, e.hom_inv_id]
  have hcompU : composeMorphism.{r,a,s} ψ φ = identityMorphism.{r,a,s} U := by
    apply (uniqU _ ?_).trans (uniqU _ rfl).symm
    change ψ.component 0 ≫ φ.component 0 = 𝟙 _
    rw [hψ, hφ, e.inv_hom_id]
  refine ⟨φ, hφ, fun n => ?_⟩
  let en : T.value n ≅ U.value n :=
    { hom := φ.component n
      inv := ψ.component n
      hom_inv_id := congrArg (fun f => f.component n) hcompT
      inv_hom_id := congrArg (fun f => f.component n) hcompU }
  exact en.isIso_hom

/-- For a left exact functor, taking degree-zero homology of the actual
cochain derived unit at a stalk is invertible. -/
private theorem degreeZeroUnit_isIso {A : Type*} {B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{h} A] [HasDerivedCategory.{h'} B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] :
    IsIso (degreeZeroUnit F) := by
  have app_isIso (M : A) : IsIso ((degreeZeroUnit F).app M) := by
    let stalk : A ⥤ CochainComplex.Plus A :=
      (CochainComplex.plus A).lift (CochainComplex.singleFunctor A 0)
        (fun _ => ⟨0, inferInstance⟩)
    have : (stalk.obj M).obj.IsStrictlyGE 0 := by
      change ((CochainComplex.singleFunctor A 0).obj M).IsStrictlyGE 0
      infer_instance
    have : IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map
        (F.rightDerivedFunctorPlusUnit.app (stalk.obj M))) :=
      AcyclicTermComparison.rightComparison_lowest_degree F (stalk.obj M) 0
    simp only [degreeZeroUnit, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

section
variable [HasDerivedCategory.{h} (ModuleCat.{max r a s} R)] [HasDerivedCategory.{h'} (ModuleCat.{max r a s} ℤ)]

theorem ordinary_rightDerived (D : OrdinaryData.{r,a,s} R X P) :
    let F := (covariantHom (R := R) X : ModuleCat.{max r a s} R ⥤ ModuleCat.{max r a s} ℤ)
    ∃ φ : CohomologicalMorphism (D.system hP) (rightSystem F),
      (∀ n, IsIso (φ.component n)) ∧
      ∀ (M : ModuleCat.{max r a s} R) (f : X →ₗ[R] M),
        ((φ.component 0).app M).hom (homClass P M f) = ((degreeZeroUnit F).app M).hom f := by
  let F := (covariantHom (R := R) X : ModuleCat.{max r a s} R ⥤ ModuleCat.{max r a s} ℤ)
  let := hom_preservesFiniteLimits.{r,a,s} (R := R) (X := X)
  let := degreeZeroUnit_isIso F
  let U := rightSystem F
  have hU : IsCohomological U :=
    AdvancedHomologicalAlgebra.UniversalDeltaFunctors.rightDelta _ _ F
  have huU : IsUniversalCohomological U :=
    AdvancedHomologicalAlgebra.UniversalDeltaFunctors.universal_of_injective_vanishing U hU
      (fun I _ n => AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightInjectiveVanishing _ _ F I n)
  let e : (D.system hP).value 0 ≅ U.value 0 :=
    (ordinaryZeroIso.{r,a,s} D).symm ≪≫ asIso (degreeZeroUnit F)
  obtain ⟨φ, hφ, hiso⟩ := universal_comparison.{r,a,s} (ordinary_cohomological.{r,a,s} D) hU
    (ordinary_universal.{r,a,s} D) huU e
  refine ⟨φ, hiso, fun M f => ?_⟩
  have hn : (ordinaryZeroIso.{r,a,s} (hP := hP) D).hom ≫ φ.component 0 = degreeZeroUnit F := by
    rw [hφ]
    simp [e]
  exact congrArg (fun t => (t.app M).hom f) hn

end

/-- A closed target for the independent ordinary-system existence Spec. -/
theorem ordinary_data_exists : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.Derived.dataExistsType.{r,a,s} := by
  intro R _ X P hP
  exact data_exists R X P hP

/-- The comparison extends the actual degree-zero augmentation class. -/
theorem rightDerived_comparison : Specs.AdvancedHomologicalAlgebra.CE.Coefficients.Derived.rightDerivedType.{r,a,s,h,h'} := by
  intro R _ X P hP _ _ D
  exact ordinary_rightDerived.{r,a,s,h,h'} (hP := hP) D

end AdvancedHomologicalAlgebra.CE.Coefficients.Derived

namespace AdvancedHomologicalAlgebra.CE.Coefficients
universe u v w h h'

theorem rightDerived_sequence :
    Specs.AdvancedHomologicalAlgebra.CE.Coefficients.rightDerivedSequenceType.{u,v,w,h,h'} := by
  intro k g _ _ _ _ d hc he
  letI := Ext.trivialModule k g
  intro _ _
  let hP := resolution_projective k g d hc he
  let O := (Derived.data_exists.{max u v,u,w} (U k g) (ModuleCat.of (U k g) k)
    (Ext.resolution k g d hc he) hP).some
  obtain ⟨φ, hiso, hzero⟩ := Derived.ordinary_rightDerived.{max u v,u,w,h,h'} (hP := hP) O
  refine ⟨hP, O, φ, hiso, hzero, ?_⟩
  intro S hS C D E n δ hδ
  have hcomp := (ext_compatibility k g d hc inferInstance he _ _ _ C D E S.f S.g
    hS.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
    hS.moduleCat_surjective_g n δ (O.boundary hS n) hδ (O.connecting hS n)).2.2
  have hc' := congrArg ModuleCat.Hom.hom (φ.comm hS n)
  change ((φ.component (n+1)).app S.X₁).hom.comp (O.boundary hS n) =
    (rightBoundary (covariantHom (R := U k g) k :
      ModuleCat.{max u v w} (U k g) ⥤ ModuleCat.{max u v w} ℤ) hS n).hom.comp ((φ.component n).app S.X₃).hom at hc'
  apply LinearMap.ext
  intro x
  have hx := congrArg (((φ.component (n+1)).app S.X₁).hom) (LinearMap.congr_fun hcomp x)
  exact hx.trans (LinearMap.congr_fun hc' ((E.comparison n) x))

end AdvancedHomologicalAlgebra.CE.Coefficients

namespace AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

open _root_.AdvancedHomologicalAlgebra.CE
open P103.Ch10.HomologySequence (cycle_iff square_zero)
open private Ext.pointwiseHomologyMap
  Ext.pointwiseHomologyMap_induces Ext.component_comm Ext.inverse_component_apply
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt

universe u v a b c a' b' c' s t q s' t' q'

theorem homology_class_surjective {R : Type*} [Ring R]
    (A : CochainComplex (ModuleCat.{s} R) ℕ) (n : ℕ) :
    Function.Surjective (homologyClass A n) :=
  (cycleBoundaries A n).mkQ_surjective

section QuotientMaps

variable {A : CochainComplex (ModuleCat.{s} ℤ) ℕ}
  {B : CochainComplex (ModuleCat.{t} ℤ) ℕ}
  {C : CochainComplex (ModuleCat.{q} ℤ) ℕ}
  {f : ∀ n, A.X n →ₗ[ℤ] B.X n}
  {g : ∀ n, B.X n →ₗ[ℤ] C.X n}

/-- A family of linear maps commuting with the differentials acts on the
original cycle quotients, even when the two complexes have different universes. -/
def quotientMap (f : ∀ n, A.X n →ₗ[ℤ] B.X n)
    (comm : ∀ i j, (B.d i j).hom.comp (f i) = (f j).comp (A.d i j).hom) :
    QuotientMap A B f :=
  ⟨fun n => (Ext.pointwiseHomologyMap f comm n).toAddMonoidHom.toIntLinearMap,
    Ext.pointwiseHomologyMap_induces f comm⟩

theorem QuotientMap.class_apply (F : QuotientMap A B f) (n : ℕ) (z : cycles A n)
    (w : cycles B n) (hw : w.val = f n z.val) :
    F.hom n (homologyClass A n z) = homologyClass B n w := by
  obtain ⟨w', hw', h⟩ := F.induced.2 n z
  rwa [show w' = w from Subtype.ext (hw'.trans hw.symm)] at h

theorem QuotientMap.differential_apply (F : QuotientMap A B f) (i j : ℕ) (z : A.X i) :
    (B.d i j).hom (f i z) = f j ((A.d i j).hom z) :=
  LinearMap.congr_fun (F.induced.1 i j) z

/-- A commuting square on cochains gives a commuting square on their quotients. -/
theorem quotient_square {D : CochainComplex (ModuleCat.{s'} ℤ) ℕ}
    {f' : ∀ n, C.X n →ₗ[ℤ] D.X n} {g' : ∀ n, A.X n →ₗ[ℤ] C.X n}
    {j : ∀ n, B.X n →ₗ[ℤ] D.X n}
    (F : QuotientMap A B f) (G : QuotientMap B D j)
    (F' : QuotientMap A C g') (G' : QuotientMap C D f')
    (hs : ∀ n, (j n).comp (f n) = (f' n).comp (g' n)) (n : ℕ) :
    (G.hom n).comp (F.hom n) = (G'.hom n).comp (F'.hom n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := homology_class_surjective A n x
  obtain ⟨w, hw, hFw⟩ := F.induced.2 n z
  obtain ⟨w', hw', hFw'⟩ := F'.induced.2 n z
  obtain ⟨y, hy, hGy⟩ := G.induced.2 n w
  have hy' : y.val = f' n w'.val := by
    rw [hy, hw, hw']
    exact LinearMap.congr_fun (hs n) z.val
  change G.hom n (F.hom n (homologyClass A n z)) =
    G'.hom n (F'.hom n (homologyClass A n z))
  rw [hFw, hFw', hGy, G'.class_apply n w' y hy']

/-- A categorical cochain map yields the quotient map defined in P103. -/
def quotientMapOfHom {B : CochainComplex (ModuleCat.{s} ℤ) ℕ} (F : A ⟶ B) :
    QuotientMap A B (fun n => (F.f n).hom) :=
  ⟨fun n => (homologyMap F n).toAddMonoidHom.toIntLinearMap, fun i j => congrArg ModuleCat.Hom.hom (F.comm i j),
    fun n z => ⟨cyclesMap F n z, rfl, rfl⟩⟩

theorem sequence_commutes
    {A' : CochainComplex (ModuleCat.{s'} ℤ) ℕ}
    {B' : CochainComplex (ModuleCat.{t'} ℤ) ℕ}
    {C' : CochainComplex (ModuleCat.{q'} ℤ) ℕ}
    {i : ∀ n, A.X n →ₗ[ℤ] B.X n} {p : ∀ n, B.X n →ₗ[ℤ] C.X n}
    {i' : ∀ n, A'.X n →ₗ[ℤ] B'.X n} {p' : ∀ n, B'.X n →ₗ[ℤ] C'.X n}
    {a : ∀ n, A.X n →ₗ[ℤ] A'.X n} {b : ∀ n, B.X n →ₗ[ℤ] B'.X n}
    {c : ∀ n, C.X n →ₗ[ℤ] C'.X n}
    (S : Sequence i p) (T : Sequence i' p')
    (α : QuotientMap A A' a) (β : QuotientMap B B' b) (γ : QuotientMap C C' c)
    (h₁ : ∀ n, (b n).comp (i n) = (i' n).comp (a n))
    (h₂ : ∀ n, (c n).comp (p n) = (p' n).comp (b n)) :
    S.Commutes T α.hom β.hom γ.hom := by
  intro n
  refine ⟨quotient_square S.inclusion β α T.inclusion h₁ n,
    quotient_square S.projection γ β T.projection h₂ n, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := homology_class_surjective C n x
  obtain ⟨y, hy⟩ := (S.degreewise n).2.2 z.val
  obtain ⟨x, hx, hxclass⟩ := S.lift_boundary n z y hy
  obtain ⟨z', hz', hzclass⟩ := γ.induced.2 n z
  obtain ⟨x', hx', hx'class⟩ := α.induced.2 (n+1) x
  have hy' : p' n (b n y) = z'.val := by
    rw [hz', ← hy]
    exact (LinearMap.congr_fun (h₂ n) y).symm
  have hi' : i' (n+1) x'.val = (B'.d n (n+1)).hom (b n y) := by
    rw [hx', β.differential_apply, ← hx]
    exact (LinearMap.congr_fun (h₁ (n+1)) x.val).symm
  obtain ⟨x'', hx'', h⟩ := T.lift_boundary n z' (b n y) hy'
  have hxx : x'' = x' :=
    Subtype.ext ((T.degreewise (n+1)).1 (hx''.trans hi'.symm))
  change α.hom (n+1) (S.boundary n (homologyClass C n z)) =
    T.boundary n (γ.hom n (homologyClass C n z))
  rw [hxclass, hzclass, hx'class, h, hxx]

end QuotientMaps

section CoefficientMaps

open scoped TensorProduct
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  {d : BoundaryFamily k g} {hc : IsAugmentedComplex k g d}
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}

theorem extPost_comm (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (h : M →ₗ[U k g] N) (i j : ℕ) :
    ((homComplex (Ext.chain k g d hc) N).d i j).hom.comp (extPost d hc h i) =
      (extPost d hc h j).comp ((homComplex (Ext.chain k g d hc) M).d i j).hom := by
  by_cases hij : (ComplexShape.up ℕ).Rel i j
  · change i + 1 = j at hij
    subst j
    apply LinearMap.ext
    intro f
    rfl
  · rw [(homComplex (Ext.chain k g d hc) N).shape i j hij,
      (homComplex (Ext.chain k g d hc) M).shape i j hij]
    simp

theorem evaluation_post (CM : Model k g d hc M) (CN : Model k g d hc N)
    (h : M →ₗ[U k g] N) (n : ℕ) (f : CM.complex.X n) :
    (CN.evaluation.hom.f n).hom (extPost d hc h n ((CM.evaluation.inv.f n).hom f)) =
      cePost CM CN h n f := by
  apply LinearMap.ext
  intro x
  change (CN.evaluation.hom.f n).hom (h.comp ((CM.evaluation.inv.f n).hom f)) x = h (f x)
  rw [CN.eval]
  have hx := LinearMap.congr_fun (Ext.inverse_component_apply CM.evaluation.symm n f) x
  change ((CM.evaluation.hom.f n).hom ((CM.evaluation.inv.f n).hom f)) x = f x at hx
  rw [CM.eval] at hx
  exact congrArg h hx

theorem evaluation_natural (CM : Model k g d hc M) (CN : Model k g d hc N)
    (h : M →ₗ[U k g] N) (n : ℕ) :
    (extPost d hc h n).comp (CM.evaluation.inv.f n).hom =
      (CN.evaluation.inv.f n).hom.comp (cePost CM CN h n) := by
  apply LinearMap.ext
  intro f
  change extPost d hc h n ((CM.evaluation.inv.f n).hom f) =
    (CN.evaluation.inv.f n).hom (cePost CM CN h n f)
  rw [← evaluation_post CM CN h n f, Ext.inverse_component_apply]

theorem cePost_comm (CM : Model k g d hc M) (CN : Model k g d hc N)
    (h : M →ₗ[U k g] N) (i j : ℕ) :
    (CN.complex.d i j).hom.comp (cePost CM CN h i) =
      (cePost CM CN h j).comp (CM.complex.d i j).hom := by
  apply LinearMap.ext
  intro f
  change (CN.complex.d i j).hom (cePost CM CN h i f) =
    cePost CM CN h j ((CM.complex.d i j).hom f)
  rw [← evaluation_post CM CN h i f, ← evaluation_post CM CN h j _,
    Ext.component_comm CN.evaluation.hom, ← Ext.component_comm CM.evaluation.inv]
  exact congrArg (CN.evaluation.hom.f j).hom
    (LinearMap.congr_fun (extPost_comm d hc h i j) _)

end CoefficientMaps

end AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

namespace AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

open P103.Ch10.HomologySequence (cycle_iff square_zero)
universe s t q l

section QuotientEquivalence

variable {A : CochainComplex (ModuleCat.{s} ℤ) ℕ} {B : CochainComplex (ModuleCat.{t} ℤ) ℕ}

/-- A degreewise linear equivalence commuting with differentials gives an
equivalence on the original cycle quotients. -/
def quotientEquiv (e : ∀ n, A.X n ≃ₗ[ℤ] B.X n)
    (comm : ∀ i j, (B.d i j).hom.comp (e i).toLinearMap =
      (e j).toLinearMap.comp (A.d i j).hom) (n : ℕ) : Homology A n ≃ₗ[ℤ] Homology B n := by
  let f := quotientMap (fun n => (e n).toLinearMap) comm
  have inv_comm (i j : ℕ) : (A.d i j).hom.comp (e i).symm.toLinearMap =
      (e j).symm.toLinearMap.comp (B.d i j).hom := by
    apply LinearMap.ext
    intro x
    apply (e j).injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact (LinearMap.congr_fun (comm i j) ((e i).symm x)).symm.trans
      (congrArg (B.d i j).hom ((e i).apply_symm_apply x))
  let g := quotientMap (fun n => (e n).symm.toLinearMap) inv_comm
  have hcomp :
      ∀ {A : CochainComplex (ModuleCat.{s} ℤ) ℕ} {B : CochainComplex (ModuleCat.{t} ℤ) ℕ}
        (e : A.X n ≃ₗ[ℤ] B.X n) (f : Homology A n →ₗ[ℤ] Homology B n)
        (g : Homology B n →ₗ[ℤ] Homology A n),
        (∀ z : cycles A n, ∃ w : cycles B n, w.val = e z.val ∧
          f (homologyClass A n z) = homologyClass B n w) →
        (∀ w : cycles B n, ∃ z : cycles A n, z.val = e.symm w.val ∧
          g (homologyClass B n w) = homologyClass A n z) →
        Function.LeftInverse g f := by
    intro A B e f g hf hg x
    obtain ⟨z, rfl⟩ := homology_class_surjective A n x
    obtain ⟨w, hw, hfz⟩ := hf z
    obtain ⟨z', hz', hgw⟩ := hg w
    have hz : z' = z := Subtype.ext (hz'.trans (by rw [hw, LinearEquiv.symm_apply_apply]))
    change g (f (homologyClass A n z)) = homologyClass A n z
    rw [hfz, hgw, hz]
  refine LinearEquiv.ofLinearMap (f.hom n) (g.hom n) ?_ ?_
  · apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := homology_class_surjective B n x
    obtain ⟨z, hz, hg⟩ := g.induced.2 n w
    have hw : w.val = (e n).toLinearMap z.val := by rw [hz]; exact ((e n).apply_symm_apply _).symm
    change f.hom n (g.hom n (homologyClass B n w)) = homologyClass B n w
    rw [hg, f.class_apply n z w hw]
  · apply LinearMap.ext
    exact hcomp (e n) (f.hom n) (g.hom n) (f.induced.2 n) (g.induced.2 n)

theorem quotientEquiv_induced (e : ∀ n, A.X n ≃ₗ[ℤ] B.X n)
    (comm : ∀ i j, (B.d i j).hom.comp (e i).toLinearMap =
      (e j).toLinearMap.comp (A.d i j).hom) :
    Ext.InducesCohomologyMap (fun n => (e n).toLinearMap)
      (fun n => (quotientEquiv e comm n).toLinearMap) :=
  (quotientMap (fun n => (e n).toLinearMap) comm).induced

end QuotientEquivalence

section LiftedComplexes

private abbrev liftComplex (A : CochainComplex (ModuleCat.{s} ℤ) ℕ) :
    CochainComplex (ModuleCat.{max s l} ℤ) ℕ :=
  ((ModuleCat.uliftFunctor.{l} ℤ).mapHomologicalComplex (ComplexShape.up ℕ)).obj A

private abbrev liftTerm (A : CochainComplex (ModuleCat.{s} ℤ) ℕ) (n : ℕ) :
    A.X n ≃ₗ[ℤ] (liftComplex.{s,l} A).X n :=
  ULift.moduleEquiv.symm

private theorem liftTerm_comm (A : CochainComplex (ModuleCat.{s} ℤ) ℕ) (i j : ℕ) :
    ((liftComplex.{s,l} A).d i j).hom.comp (liftTerm.{s,l} A i).toLinearMap =
      (liftTerm.{s,l} A j).toLinearMap.comp (A.d i j).hom := rfl

private def liftComplexMap
    {A : CochainComplex (ModuleCat.{s} ℤ) ℕ} {B : CochainComplex (ModuleCat.{t} ℤ) ℕ}
    (f : ∀ n, A.X n →ₗ[ℤ] B.X n)
    (comm : ∀ i j, (B.d i j).hom.comp (f i) = (f j).comp (A.d i j).hom) :
    liftComplex.{s,max s t l} A ⟶ liftComplex.{t,max s t l} B where
  f n := ConcreteCategory.ofHom (X := (liftComplex.{s,max s t l} A).X n)
    (Y := (liftComplex.{t,max s t l} B).X n) ((liftTerm.{t,max s t l} B n).toLinearMap.comp
    ((f n).comp (liftTerm.{s,max s t l} A n).symm.toLinearMap))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg ULift.up (LinearMap.congr_fun (comm i j) x.down)

private theorem liftComplexMap_square
    {A : CochainComplex (ModuleCat.{s} ℤ) ℕ} {B : CochainComplex (ModuleCat.{t} ℤ) ℕ}
    (f : ∀ n, A.X n →ₗ[ℤ] B.X n)
    (comm : ∀ i j, (B.d i j).hom.comp (f i) = (f j).comp (A.d i j).hom) (n : ℕ) :
    (((liftComplexMap.{s,t,l} f comm).f n).hom).comp (liftTerm.{s,max s t l} A n).toLinearMap =
      (liftTerm.{t,max s t l} B n).toLinearMap.comp (f n) := by
  apply LinearMap.ext
  intro x
  rfl

end LiftedComplexes

section SequenceOfDegreewise

variable {A : CochainComplex (ModuleCat.{s} ℤ) ℕ}
  {B : CochainComplex (ModuleCat.{t} ℤ) ℕ}
  {C : CochainComplex (ModuleCat.{q} ℤ) ℕ}
  {i : ∀ n, A.X n →ₗ[ℤ] B.X n} {p : ∀ n, B.X n →ₗ[ℤ] C.X n}

theorem cycle_lift (I : QuotientMap A B i) (P : QuotientMap B C p)
    (hs : ∀ n, Function.Injective (i n) ∧ Function.Exact (i n) (p n) ∧ Function.Surjective (p n))
    (n : ℕ) (z : cycles C n) (y : B.X n) (hy : p n y = z.val) :
    ∃ x : cycles A (n+1), i (n+1) x.val = (B.d n (n+1)).hom y := by
  have hz : p (n+1) ((B.d n (n+1)).hom y) = 0 := by
    rw [← P.differential_apply, hy]
    exact (cycle_iff C (show (ComplexShape.up ℕ).Rel n (n+1) from rfl) _).mp z.property
  obtain ⟨x, hx⟩ := ((hs (n+1)).2.1 _).mp hz
  refine ⟨⟨x, ?_⟩, hx⟩
  change (A.d (n+1) ((ComplexShape.up ℕ).next (n+1))).hom x = 0
  apply (hs ((ComplexShape.up ℕ).next (n+1))).1
  rw [map_zero, ← I.differential_apply, hx, square_zero]

/-- Build the heterogeneous sequence by computing the connecting map after
a common termwise universe lift and transporting along the quotient equivalences. -/
def sequenceOfDegreewise (I : QuotientMap A B i) (P : QuotientMap B C p)
    (hs : ∀ n, Function.Injective (i n) ∧ Function.Exact (i n) (p n) ∧ Function.Surjective (p n)) :
    Sequence i p := by
  let I' := liftComplexMap.{s,t,q} i I.induced.1
  let P' := liftComplexMap.{t,q,s} p P.induced.1
  let a := liftTerm.{s,max s t q} A
  let b := liftTerm.{t,max s t q} B
  let c := liftTerm.{q,max s t q} C
  have hI := liftComplexMap_square.{s,t,q} i I.induced.1
  have hP := liftComplexMap_square.{t,q,s} p P.induced.1
  have hs' : DegreewiseExact I' P' := by
    intro n
    refine ⟨?_, Function.Exact.of_ladder_linearEquiv_of_exact (hI n) (hP n) (hs n).2.1, ?_⟩
    · intro x y hxy
      apply ULift.ext
      exact (hs n).1 (congrArg ULift.down hxy)
    · intro z
      obtain ⟨y, hy⟩ := (hs n).2.2 z.down
      exact ⟨⟨y⟩, ULift.ext hy⟩
  have exists_δ (n : ℕ) := P103.Ch10.HomologySequence.sequence I' P' hs' n (n+1) (by rfl)
  choose δ hδ _ using exists_δ
  let δLift := fun n => (δ n).toAddMonoidHom.toIntLinearMap
  let EA := quotientEquiv a (liftTerm_comm.{s,max s t q} A)
  let EB := quotientEquiv b (liftTerm_comm.{t,max s t q} B)
  let EC := quotientEquiv c (liftTerm_comm.{q,max s t q} C)
  let QA : QuotientMap _ _ (fun n => (a n).toLinearMap) :=
    ⟨fun n => (EA n).toLinearMap, quotientEquiv_induced _ _⟩
  let QB : QuotientMap _ _ (fun n => (b n).toLinearMap) :=
    ⟨fun n => (EB n).toLinearMap, quotientEquiv_induced _ _⟩
  let QC : QuotientMap _ _ (fun n => (c n).toLinearMap) :=
    ⟨fun n => (EC n).toLinearMap, quotientEquiv_induced _ _⟩
  let δOriginal := fun n => (EA (n+1)).symm.toLinearMap.comp ((δLift n).comp (EC n).toLinearMap)
  have hIQ (n : ℕ) : ((quotientMapOfHom I').hom n).comp (EA n).toLinearMap =
      (EB n).toLinearMap.comp (I.hom n) :=
    (quotient_square I QB QA (quotientMapOfHom I') (fun n => (hI n).symm) n).symm
  have hPQ (n : ℕ) : ((quotientMapOfHom P').hom n).comp (EB n).toLinearMap =
      (EC n).toLinearMap.comp (P.hom n) :=
    (quotient_square P QC QB (quotientMapOfHom P') (fun n => (hP n).symm) n).symm
  have hδQ (n : ℕ) : (δLift n).comp (EC n).toLinearMap = (EA (n+1)).toLinearMap.comp (δOriginal n) := by
    ext x
    change δ n (EC n x) = EA (n+1) ((EA (n+1)).symm (δ n (EC n x)))
    exact ((EA (n+1)).apply_symm_apply _).symm
  refine ⟨I, P, hs, δOriginal, ?_, ?_, ?_⟩
  · intro x y h
    apply (EA 0).injective
    apply (P103.Ch10.HorseshoeNaturality.cochain_zero_exact I' P' hs').1
    exact (LinearMap.congr_fun (hIQ 0) x).trans
      ((congrArg (EB 0) h).trans (LinearMap.congr_fun (hIQ 0) y).symm)
  · intro n
    exact ⟨(Function.Exact.iff_of_ladder_linearEquiv (hIQ n) (hPQ n)).mp (hδ n).2.1,
      (Function.Exact.iff_of_ladder_linearEquiv (hPQ n) (hδQ n)).mp (hδ n).2.2.1,
      (Function.Exact.iff_of_ladder_linearEquiv (hδQ n) (hIQ (n+1))).mp (hδ n).2.2.2⟩
  · intro n z y hy
    obtain ⟨x, hx⟩ := cycle_lift I P hs n z y hy
    refine ⟨x, hx, ?_⟩
    obtain ⟨zl, hzl, hzclass⟩ := QC.induced.2 n z
    obtain ⟨xl, hxl, hxclass⟩ := QA.induced.2 (n+1) x
    have hyl : (P'.f n).hom (b n y) = zl.val := by
      rw [hzl, ← hy]
      exact LinearMap.congr_fun (hP n) y
    have hxl' : (I'.f (n+1)).hom xl.val = ((liftComplex.{t,max s t q} B).d n (n+1)).hom (b n y) := by
      rw [hxl]
      change (I'.f (n+1)).hom (a (n+1) x.val) = _
      rw [show (I'.f (n+1)).hom (a (n+1) x.val) = b (n+1) (i (n+1) x.val)
        from LinearMap.congr_fun (hI (n+1)) x.val, hx]
      rfl
    have hδ' := (hδ n).1 zl (b n y) xl hyl hxl'
    apply (EA (n+1)).injective
    change EA (n+1) (δOriginal n (homologyClass C n z)) = QA.hom (n+1) (homologyClass A (n+1) x)
    refine (LinearMap.congr_fun (hδQ n) (homologyClass C n z)).symm.trans ?_
    change δ n (QC.hom n (homologyClass C n z)) = QA.hom (n+1) (homologyClass A (n+1) x)
    rwa [hzclass, hxclass]

end SequenceOfDegreewise

end AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

namespace AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

open _root_.AdvancedHomologicalAlgebra.CE
universe u v a b c a' b' c'

section

variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  {d : BoundaryFamily k g} {hc : IsAugmentedComplex k g d}
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)} {P : ModuleCat.{c} (U k g)}
  {M' : ModuleCat.{a'} (U k g)} {N' : ModuleCat.{b'} (U k g)} {P' : ModuleCat.{c'} (U k g)}

/-- Inverse evaluation on the original cochain quotients. -/
def comparisonQuotientMap (CM : Model k g d hc M) :
    QuotientMap CM.complex (homComplex (Ext.chain k g d hc) M)
      (fun n => (CM.evaluation.inv.f n).hom) :=
  quotientMapOfHom CM.evaluation.inv

theorem comparisonQuotientMap_apply (CM : Model k g d hc M) :
    (comparisonQuotientMap CM).hom = fun n => (CM.comparison n).toLinearMap := by
  funext n
  apply LinearMap.ext
  intro x
  rfl

private theorem post_degreewise {R X L M N : Type*} [Ring R]
    [AddCommGroup X] [Module R X] [Module.Projective R X]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i : L →ₗ[R] M) (p : M →ₗ[R] N)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p) :
    Function.Injective (P103.HomTensorExactness.post (P := X) i) ∧
      Function.Exact (P103.HomTensorExactness.post (P := X) i) (P103.HomTensorExactness.post (P := X) p) ∧
      Function.Surjective (P103.HomTensorExactness.post (P := X) p) := by
  obtain ⟨hinj, hex⟩ := P103.HomTensorExactness.homCovariant R L M N X i p hi he
  exact ⟨hinj, hex, fun f => Module.projective_lifting_property p f hp⟩

theorem cePost_square
    {CM : Model k g d hc M} {CN : Model k g d hc N}
    {CM' : Model k g d hc M'} {CN' : Model k g d hc N'}
    {i : M →ₗ[U k g] N} {i' : M' →ₗ[U k g] N'}
    {α : M →ₗ[U k g] M'} {β : N →ₗ[U k g] N'} (h : β.comp i = i'.comp α) (n : ℕ) :
    (cePost CN CN' β n).comp (cePost CM CN i n) =
      (cePost CM' CN' i' n).comp (cePost CM CM' α n) := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun h (f x)

theorem extPost_square
    {i : M →ₗ[U k g] N} {i' : M' →ₗ[U k g] N'}
    {α : M →ₗ[U k g] M'} {β : N →ₗ[U k g] N'} (h : β.comp i = i'.comp α) (n : ℕ) :
    (extPost d hc β n).comp (extPost d hc i n) =
      (extPost d hc i' n).comp (extPost d hc α n) := by
  apply LinearMap.ext
  intro f
  change V k g n →ₗ[U k g] M at f
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun h (f x)

end

/-- The two coefficient long exact sequences on the given original quotients,
with inverse evaluation preserving the positive connecting map. -/
theorem sequence :
    Specs.AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous.sequenceType.{u,v,a,b,c} := by
  intro k g _ _ _ hg d hc M N P CM CN CP i p hi he hp
  let := hg
  have hCE n : Function.Injective (cePost CM CN i n) ∧
      Function.Exact (cePost CM CN i n) (cePost CN CP p n) ∧
      Function.Surjective (cePost CN CP p n) := by
    have : Module.Free k (W k g n) := inferInstance
    exact post_degreewise (X := W k g n) (i.restrictScalars k) (p.restrictScalars k) hi he hp
  have hExt n : Function.Injective (extPost d hc i n) ∧
      Function.Exact (extPost d hc i n) (extPost d hc p n) ∧
      Function.Surjective (extPost d hc p n) := by
    have := term_free k g n
    exact post_degreewise (X := V k g n) i p hi he hp
  let ce := sequenceOfDegreewise (quotientMap _ (cePost_comm CM CN i))
    (quotientMap _ (cePost_comm CN CP p)) hCE
  let ex := sequenceOfDegreewise (quotientMap _ (extPost_comm d hc i))
    (quotientMap _ (extPost_comm d hc p)) hExt
  refine ⟨⟨ce, ex, ?_⟩⟩
  rw [← comparisonQuotientMap_apply CM, ← comparisonQuotientMap_apply CN,
    ← comparisonQuotientMap_apply CP]
  exact sequence_commutes ce ex (comparisonQuotientMap CM) (comparisonQuotientMap CN)
    (comparisonQuotientMap CP) (fun n => (evaluation_natural CM CN i n).symm)
    (fun n => (evaluation_natural CN CP p n).symm)

/-- All original coefficient maps act naturally on both long exact
sequences, allowing six independently sized coefficient modules. -/
theorem naturality :
    Specs.AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous.naturalityType.{u,v,a,b,c,a',b',c'} := by
  intro k g _ _ _ d hc M N P M' N' P' CM CN CP CM' CN' CP'
    i p i' p' α β γ h₁ h₂ S T
  refine ⟨quotientMap _ (cePost_comm CM CM' α), quotientMap _ (cePost_comm CN CN' β),
    quotientMap _ (cePost_comm CP CP' γ), quotientMap _ (extPost_comm d hc α),
    quotientMap _ (extPost_comm d hc β), quotientMap _ (extPost_comm d hc γ), ?_, ?_⟩
  · exact sequence_commutes S.ce T.ce _ _ _ (cePost_square h₁) (cePost_square h₂)
  · exact sequence_commutes S.ext T.ext _ _ _
      (extPost_square (d := d) (hc := hc) h₁) (extPost_square (d := d) (hc := hc) h₂)

end AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

namespace AdvancedHomologicalAlgebra.CE.Coefficients.Derived

universe r a s h h'
variable {R : Type r} [Ring R] {X : ModuleCat.{a} R} {P : LeftResolution R X}
variable [HasDerivedCategory.{h} (ModuleCat.{max r a s} R)]
  [HasDerivedCategory.{h'} (ModuleCat.{max r a s} ℤ)]

/-- The comparison of cohomological systems preserves the actual boundary. -/
lemma derived_boundary (O : OrdinaryData.{r,a,s} R X P) (hP : P.IsProjective)
    (φ : CohomologicalMorphism (O.system hP)
      (rightSystem (covariantHom (R := R) X : ModuleCat.{max r a s} R ⥤ ModuleCat.{max r a s} ℤ)))
    {S : ShortComplex (ModuleCat.{max r a s} R)} (hS : S.ShortExact) (n : ℕ) :
    ((φ.component (n+1)).app S.X₁).hom.comp (O.boundary hS n) =
      (rightBoundary (covariantHom (R := R) X : ModuleCat.{max r a s} R ⥤
        ModuleCat.{max r a s} ℤ) hS n).hom.comp ((φ.component n).app S.X₃).hom :=
  congrArg ModuleCat.Hom.hom (φ.comm hS n)

end AdvancedHomologicalAlgebra.CE.Coefficients.Derived

namespace AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

universe z
variable {A B C : CochainComplex (ModuleCat.{z} ℤ) ℕ}

/-- Both boundary constructions use the same class of the lifted differential. -/
lemma boundary_apply_eq_connecting (i : A ⟶ B) (p : B ⟶ C)
    (T : Sequence (fun n => (i.f n).hom) (fun n => (p.f n).hom))
    (n : ℕ) {δ} (hδ : Connecting i p n (n+1) δ) (z : Homology C n) :
    T.boundary n z = δ z := by
  obtain ⟨z, rfl⟩ := Quotient.exists_rep z
  obtain ⟨y, hy⟩ := (T.degreewise n).2.2 z.val
  obtain ⟨x, hx, hb⟩ := T.lift_boundary n z y hy
  exact hb.trans (hδ z y x hy hx).symm

end AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

namespace AdvancedHomologicalAlgebra.CE.Coefficients.Model

open scoped TensorProduct
universe u v a b
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
variable {d : BoundaryFamily k g} {hc : IsAugmentedComplex k g d}
variable {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)}

private lemma evaluation_apply (C : Model k g d hc M) (n : ℕ)
    (F : V k g n →ₗ[U k g] M) :
    (C.evaluation.hom.f n).hom F = homEquiv k g M n F := by
  apply LinearMap.ext
  intro z
  exact C.eval n F z

/-- The prescribed evaluation determines the differential of any model. -/
private lemma differential_eq (C : Model k g d hc M) (n : ℕ)
    (f : W k g n →ₗ[k] M) : C.δ n f = coboundary k g M d n f := by
  obtain ⟨F, rfl⟩ := (homEquiv k g M n).surjective f
  have h := P103.Ch10.HomologySequence.comm_apply C.evaluation.hom n (n+1) F
  simp only [Ext.cochain, CochainComplex.of_d, ModuleCat.hom_ofHom,
    AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe] at h
  change C.δ n ((C.evaluation.hom.f n).hom F) =
    (C.evaluation.hom.f (n+1)).hom (((homComplex (Ext.chain k g d hc) M).d n (n+1)).hom F) at h
  rw [evaluation_apply, evaluation_apply, P103.Ch11.ExtTorDefinitions.hom_differential] at h
  rw [h, coboundary_comparison]
  simp only [Ext.chain, ChainComplex.of_d, ModuleCat.hom_ofHom, homCoboundary]

/-- Changing the carrier of a coefficient module preserves the explicit model. -/
def transport (C : Model k g d hc M) (e : M ≃ₗ[U k g] N) : Model k g d hc N := by
  have hformula (n : ℕ) (f : W k g n →ₗ[k] N) (x : Fin (n+1) → g) :
      coboundary k g N d n f (wedge k g (n+1) x) =
        cochainActionSum k g N n f x + cochainBracketSum k g N n f x := by
    apply e.symm.injective
    let h := e.symm.toLinearMap
    have hnat := LinearMap.congr_fun (coboundary_natural k g N M h d n f) (wedge k g (n+1) x)
    change coboundary k g M d n ((h.restrictScalars k).comp f) (wedge k g (n+1) x) =
      e.symm (coboundary k g N d n f (wedge k g (n+1) x)) at hnat
    rw [← hnat, ← differential_eq C, C.formula, map_add]
    congr 1
    · simp only [cochainActionSum, map_sum, map_zsmul, map_smul,
        LinearMap.comp_apply, LinearMap.restrictScalars_apply, h, LinearEquiv.coe_toLinearMap]
    · cases n <;> simp only [cochainBracketSum, map_zero, map_sum, map_zsmul,
        LinearMap.comp_apply, LinearMap.restrictScalars_apply, h, LinearEquiv.coe_toLinearMap]
  let A : CochainData k g N d := {
    evaluation := homEquiv k g N
    differential := coboundary k g N d
    evaluate_tmul := fun _ _ _ => rfl
    inverse_tmul := homEquiv_symm_tmul k g N
    compatible := coboundary_comparison k g N d
    squared := coboundary_squared k g N d hc.1
    formula := hformula }
  exact {
    δ := A.differential
    square := A.squared
    evaluation := Ext.evaluationIso k g N d hc A
    eval := fun _ _ _ => rfl
    formula := A.formula }

end AdvancedHomologicalAlgebra.CE.Coefficients.Model

namespace AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

open scoped TensorProduct
universe u v a b c s t q l

variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)} {P : ModuleCat.{c} (U k g)}
  (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)

/-- Conjugating both coefficient maps by the specified carrier lifts preserves short exactness. -/
theorem liftSequence_shortExact (i : M →ₗ[U k g] N) (p : N →ₗ[U k g] P)
    (hi : Function.Injective i) (hp : Function.Exact i p) (hs : Function.Surjective p) :
    (liftSequence i p hp).ShortExact := by
  exact ModuleCat.shortComplexOfConj_shortExact
    (liftEquiv.{u,v,a,max u v a b c} M).symm
    (liftEquiv.{u,v,b,max u v a b c} N).symm
    (liftEquiv.{u,v,c,max u v a b c} P).symm i p hp hi hs

private def extCarrierCochain (e : M ≃ₗ[U k g] N) (n : ℕ) :
    (homComplex (Ext.chain k g d hc) M).X n ≃ₗ[ℤ]
      (homComplex (Ext.chain k g d hc) N).X n :=
  LinearEquiv.ofLinearMap (extPost d hc e.toLinearMap n) (extPost d hc e.symm.toLinearMap n)
    (by
      apply LinearMap.ext
      intro F
      change V k g n →ₗ[U k g] N at F
      change (e.toLinearMap.comp (e.symm.toLinearMap.comp F)) = F
      apply LinearMap.ext
      intro x
      exact e.apply_symm_apply (F x))
    (by
      apply LinearMap.ext
      intro F
      change V k g n →ₗ[U k g] M at F
      change (e.symm.toLinearMap.comp (e.toLinearMap.comp F)) = F
      apply LinearMap.ext
      intro x
      exact e.symm_apply_apply (F x))

/-- Postcomposition with a coefficient equivalence induces an isomorphism on the original Ext quotients. -/
def extCarrierEquiv (e : M ≃ₗ[U k g] N) (n : ℕ) :
    Homology (homComplex (Ext.chain k g d hc) M) n ≃ₗ[ℤ]
      Homology (homComplex (Ext.chain k g d hc) N) n :=
  quotientEquiv (extCarrierCochain d hc e) (extPost_comm d hc e.toLinearMap) n

theorem extCarrier_induced (e : M ≃ₗ[U k g] N) :
    Ext.InducesCohomologyMap (extPost d hc e.toLinearMap)
      (fun n => (extCarrierEquiv d hc e n).toLinearMap) :=
  quotientEquiv_induced (extCarrierCochain d hc e) (extPost_comm d hc e.toLinearMap)

variable {d hc}

/-- Postcomposition with the same carrier equivalence on the alternating cochains
induces the comparison transported through the prescribed evaluations. -/
theorem ceCarrier_induced (CM : Model k g d hc M) (CN : Model k g d hc N)
    (e : M ≃ₗ[U k g] N) :
    Ext.InducesCohomologyMap (cePost CM CN e.toLinearMap)
      (fun n => ((CM.comparison n).trans
        ((extCarrierEquiv d hc e n).trans (CN.comparison n).symm)).toLinearMap) := by
  let C := quotientMap (cePost CM CN e.toLinearMap) (cePost_comm CM CN e.toLinearMap)
  let E : QuotientMap _ _ (extPost d hc e.toLinearMap) :=
    ⟨fun n => (extCarrierEquiv d hc e n).toLinearMap, extCarrier_induced d hc e⟩
  refine ⟨C.induced.1, fun n z => ?_⟩
  obtain ⟨y, hy, hY⟩ := C.induced.2 n z
  have h := quotient_square (comparisonQuotientMap CM) E C (comparisonQuotientMap CN)
    (evaluation_natural CM CN e.toLinearMap) n
  rw [comparisonQuotientMap_apply, comparisonQuotientMap_apply] at h
  have hy' := LinearMap.congr_fun h (homologyClass _ n z)
  refine ⟨y, hy, ?_⟩
  apply (CN.comparison n).injective
  rw [← hY]
  simpa only [E, LinearMap.comp_apply, LinearEquiv.trans_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hy'

universe a' b' c'

/-- The comparisons on the original quotients preserve the coefficient maps and the positive connector. -/
theorem carrier_commutes
    {M' : ModuleCat.{a'} (U k g)} {N' : ModuleCat.{b'} (U k g)} {P' : ModuleCat.{c'} (U k g)}
    {CM : Model k g d hc M} {CN : Model k g d hc N} {CP : Model k g d hc P}
    {CM' : Model k g d hc M'} {CN' : Model k g d hc N'} {CP' : Model k g d hc P'}
    {i : M →ₗ[U k g] N} {p : N →ₗ[U k g] P} {i' : M' →ₗ[U k g] N'} {p' : N' →ₗ[U k g] P'}
    (T : CoefficientSequence CM CN CP i p) (L : CoefficientSequence CM' CN' CP' i' p')
    (eM : M ≃ₗ[U k g] M') (eN : N ≃ₗ[U k g] N') (eP : P ≃ₗ[U k g] P')
    (hi : eN.toLinearMap.comp i = i'.comp eM.toLinearMap)
    (hp : eP.toLinearMap.comp p = p'.comp eN.toLinearMap) :
    T.ext.Commutes L.ext
      (fun n => (extCarrierEquiv d hc eM n).toLinearMap)
      (fun n => (extCarrierEquiv d hc eN n).toLinearMap)
      (fun n => (extCarrierEquiv d hc eP n).toLinearMap) ∧
    T.ce.Commutes L.ce
      (fun n => ((CM.comparison n).trans ((extCarrierEquiv d hc eM n).trans (CM'.comparison n).symm)).toLinearMap)
      (fun n => ((CN.comparison n).trans ((extCarrierEquiv d hc eN n).trans (CN'.comparison n).symm)).toLinearMap)
      (fun n => ((CP.comparison n).trans ((extCarrierEquiv d hc eP n).trans (CP'.comparison n).symm)).toLinearMap) := by
  refine ⟨sequence_commutes T.ext L.ext
    ⟨_, extCarrier_induced d hc eM⟩ ⟨_, extCarrier_induced d hc eN⟩ ⟨_, extCarrier_induced d hc eP⟩
    (extPost_square (d := d) (hc := hc) hi) (extPost_square (d := d) (hc := hc) hp),
    sequence_commutes T.ce L.ce
      ⟨_, ceCarrier_induced CM CM' eM⟩ ⟨_, ceCarrier_induced CN CN' eN⟩ ⟨_, ceCarrier_induced CP CP' eP⟩
      (cePost_square hi) (cePost_square hp)⟩

end AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

namespace AdvancedHomologicalAlgebra.CE.Coefficients

open Heterogeneous
universe u v w r x y
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)

/-- The quotient maps for homogeneous sequences are given by the same
termwise canonical carrier equivalences. -/
def liftedCohomology : LiftedCohomology.{u,v,w} k g d hc where
  ext M := extCarrierEquiv d hc (liftEquiv.{u,v,w,max u v} M)
  ext_induced M := extCarrier_induced d hc (liftEquiv.{u,v,w,max u v} M)
  ext_natural {M N} f n := by
    let eM := liftEquiv.{u,v,w,max u v} M
    let eN := liftEquiv.{u,v,w,max u v} N
    let f' := (liftCoefficients.{u,v,w} k g).map f
    have hf : eN.toLinearMap.comp f.hom = f'.hom.comp eM.toLinearMap := by
      apply LinearMap.ext
      intro x
      rfl
    exact quotient_square (quotientMapOfHom (homPostMap (Ext.chain k g d hc) f.hom))
      ⟨_, extCarrier_induced d hc eN⟩ ⟨_, extCarrier_induced d hc eM⟩
      (quotientMapOfHom (homPostMap (Ext.chain k g d hc) f'.hom))
      (extPost_square (d := d) (hc := hc) hf) n
  ce_induced M C D := ceCarrier_induced C D (liftEquiv.{u,v,w,max u v} M)

private def extSequenceOfShortExact {R : Type r} [Ring R] {A : ModuleCat.{x} R}
    {Q : LeftResolution R A} (hQ : Q.IsProjective) (S : ShortComplex (ModuleCat.{y} R))
    (hS : S.ShortExact) :
    Sequence (fun n => ((homPostMap Q.complex S.f.hom).f n).hom)
      (fun n => ((homPostMap Q.complex S.g.hom).f n).hom) :=
  sequenceOfDegreewise
    (quotientMapOfHom (homPostMap Q.complex S.f.hom))
    (quotientMapOfHom (homPostMap Q.complex S.g.hom))
    (P103.Ch11.ExtExactSequences.second_degreewise_exact Q hQ S.f S.g
      hS.moduleCat_injective_f
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
      hS.moduleCat_surjective_g)

attribute [local instance] Ext.trivialModule

set_option maxHeartbeats 800000 in
/-- The positive Ext connector commutes with the termwise lift. Both
connector formulas are applied to the same lifts, mapped by postcomposition. -/
theorem liftedExt_boundary [Module.Free k g] (he : Ext.AugmentedExact k g d)
    (S : ShortComplex (ModuleCat.{w} (U k g))) (hS : S.ShortExact)
    (O : Derived.OrdinaryData.{max u v,u,w} (U k g) (ModuleCat.of (U k g) k)
      (Ext.resolution k g d hc he))
    (n : ℕ) (ε : ExtWith (Ext.resolution k g d hc he) S.X₃ n →ₗ[ℤ]
      ExtWith (Ext.resolution k g d hc he) S.X₁ (n+1))
    (hε : SecondConnecting (A := ModuleCat.of (U k g) k) (Ext.resolution k g d hc he) S.f S.g n ε) :
    (let hS' := hS.map_of_exact (liftCoefficients.{u,v,w} k g)
      let L := liftedCohomology.{u,v,w} k g d hc
      (L.ext S.X₁ (n+1)).toLinearMap.comp ε =
        (O.boundary hS' n).comp (L.ext S.X₃ n).toLinearMap) := by
  let Q := Ext.resolution k g d hc he
  let S' := S.map (liftCoefficients.{u,v,w} k g)
  let hS' := hS.map_of_exact (liftCoefficients.{u,v,w} k g)
  let L := liftedCohomology.{u,v,w} k g d hc
  let eA := liftEquiv.{u,v,w,max u v} S.X₁
  let eB := liftEquiv.{u,v,w,max u v} S.X₂
  let eC := liftEquiv.{u,v,w,max u v} S.X₃
  have hQ : Q.IsProjective := resolution_projective k g d hc he
  let T := extSequenceOfShortExact (A := ModuleCat.of (U k g) k) (Q := Q) hQ S hS
  let T' := extSequenceOfShortExact (A := ModuleCat.of (U k g) k) (Q := Q) hQ S' hS'
  have hi : eB.toLinearMap.comp S.f.hom = S'.f.hom.comp eA.toLinearMap := rfl
  have hp : eC.toLinearMap.comp S.g.hom = S'.g.hom.comp eB.toLinearMap := rfl
  have hn := (sequence_commutes T T'
    ⟨_, L.ext_induced S.X₁⟩ ⟨_, L.ext_induced S.X₂⟩ ⟨_, L.ext_induced S.X₃⟩
    (extPost_square (d := d) (hc := hc) hi) (extPost_square (d := d) (hc := hc) hp) n).2.2
  apply LinearMap.ext
  intro x
  have hT := boundary_apply_eq_connecting (homPostMap Q.complex S.f.hom)
    (homPostMap Q.complex S.g.hom) T n hε x
  have hT' := boundary_apply_eq_connecting (homPostMap Q.complex S'.f.hom)
    (homPostMap Q.complex S'.g.hom) T' n (O.connecting hS' n) (L.ext S.X₃ n x)
  exact (congrArg (L.ext S.X₁ (n+1)) hT.symm).trans
    ((LinearMap.congr_fun hn x).trans hT')

end AdvancedHomologicalAlgebra.CE.Coefficients

namespace AdvancedHomologicalAlgebra.CE.Coefficients

universe u v w h h'

set_option maxHeartbeats 1000000 in
theorem liftedRightDerived_sequence :
    Specs.AdvancedHomologicalAlgebra.CE.Coefficients.liftedRightDerivedSequenceType.{u,v,w,h,h'} := by
  intro k g _ _ _ _ d hc he
  letI := Ext.trivialModule k g
  dsimp only
  intro _ _
  let Q := Ext.resolution k g d hc he
  let hQ := resolution_projective k g d hc he
  let O := (Derived.data_exists.{max u v,u,w} (U k g) (ModuleCat.of (U k g) k) Q hQ).some
  obtain ⟨φ, hiso, hzero⟩ := Derived.ordinary_rightDerived.{max u v,u,w,h,h'} (hP := hQ) O
  let L := liftedCohomology.{u,v,w} k g d hc
  refine ⟨L, hQ, O, φ, hiso, hzero, ?_⟩
  intro S hS C D E n δ ε hδ hε
  let hS' := hS.map_of_exact (liftCoefficients.{u,v,w} k g)
  have hExt := liftedExt_boundary k g d hc he S hS O n ε hε
  have hCE := (ext_compatibility k g d hc inferInstance he _ _ _ C D E S.f S.g
    hS.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
    hS.moduleCat_surjective_g n δ ε hδ hε).2.2
  have hDer := Derived.derived_boundary O hQ φ hS' n
  refine ⟨hExt, ?_⟩
  apply LinearMap.ext
  intro x
  have hCE' := LinearMap.congr_fun hCE x
  have hExt' := LinearMap.congr_fun hExt ((E.comparison n) x)
  have hDer' := LinearMap.congr_fun hDer ((L.ext S.X₃ n) ((E.comparison n) x))
  let compare := ((φ.component (n+1)).app ((liftCoefficients.{u,v,w} k g).obj S.X₁)).hom
  exact (congrArg (fun y => compare (L.ext S.X₁ (n+1) y)) hCE').trans
    ((congrArg compare hExt').trans hDer')

end AdvancedHomologicalAlgebra.CE.Coefficients

namespace AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

universe u v a b c h h'

set_option maxHeartbeats 1800000 in
theorem rightDerived_sequence :
    Specs.AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous.rightDerivedType.{u,v,a,b,c,h,h'} := by
  intro k g _ _ _ _ d hc he
  letI := Ext.trivialModule k g
  dsimp only
  intro _ _
  let Q := Ext.resolution k g d hc he
  let hQ := resolution_projective k g d hc he
  let O := (Derived.data_exists.{max u v,u,max a b c} (U k g) (ModuleCat.of (U k g) k) Q hQ).some
  obtain ⟨φ, hiso, hzero⟩ :=
    Derived.ordinary_rightDerived.{max u v,u,max a b c,h,h'} (hP := hQ) O
  refine ⟨hQ, O, φ, hiso, hzero, ?_⟩
  intro M N P CM CN CP i p hi hp hs T
  let S := liftSequence i p hp
  have hS : S.ShortExact := liftSequence_shortExact i p hi hp hs
  let eM : M ≃ₗ[U k g] S.X₁ := liftEquiv.{u,v,a,max u v a b c} M
  let eN : N ≃ₗ[U k g] S.X₂ := liftEquiv.{u,v,b,max u v a b c} N
  let eP : P ≃ₗ[U k g] S.X₃ := liftEquiv.{u,v,c,max u v a b c} P
  let LM := CM.transport eM
  let LN := CN.transport eN
  let LP := CP.transport eP
  obtain ⟨L⟩ := sequence k g d hc S.X₁ S.X₂ S.X₃ LM LN LP S.f.hom S.g.hom
    hS.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
    hS.moduleCat_surjective_g
  have hi' : eN.toLinearMap.comp i = S.f.hom.comp eM.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  have hp' : eP.toLinearMap.comp p = S.g.hom.comp eN.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  obtain ⟨hExt, hCE⟩ := carrier_commutes T L eM eN eP hi' hp'
  refine ⟨hS, LM, LN, LP, L, extCarrierEquiv d hc eM, extCarrierEquiv d hc eN,
    extCarrierEquiv d hc eP, extCarrier_induced d hc eM, extCarrier_induced d hc eN,
    extCarrier_induced d hc eP, ceCarrier_induced CM LM eM, ceCarrier_induced CN LN eN,
    ceCarrier_induced CP LP eP, hExt, hCE, ?_⟩
  intro n
  have hb : L.ext.boundary n = O.boundary hS n := by
    apply LinearMap.ext
    intro x
    exact boundary_apply_eq_connecting (homPostMap Q.complex S.f.hom)
      (homPostMap Q.complex S.g.hom) L.ext n (O.connecting hS n) x
  refine ⟨hb, ?_⟩
  apply LinearMap.ext
  intro x
  have hCE' := LinearMap.congr_fun (T.comparison n).2.2 x
  have hExt' := LinearMap.congr_fun (hExt n).2.2 ((CP.comparison n) x)
  have hDer := Derived.derived_boundary O hQ φ hS n
  have hDer' := LinearMap.congr_fun hDer
    ((extCarrierEquiv d hc eP n) ((CP.comparison n) x))
  have hb' := LinearMap.congr_fun hb ((extCarrierEquiv d hc eP n) ((CP.comparison n) x))
  let compare := ((φ.component (n+1)).app S.X₁).hom
  exact (congrArg (fun y => compare (extCarrierEquiv d hc eM (n+1) y)) hCE').trans
    ((congrArg compare (hExt'.trans hb')).trans hDer')

end AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous
