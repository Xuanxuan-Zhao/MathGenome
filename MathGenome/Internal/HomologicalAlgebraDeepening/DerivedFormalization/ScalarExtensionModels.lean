import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Preservation of K-flat and K-projective complexes by scalar extension. -/

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ModuleCat
open scoped TensorProduct ChangeOfRings

universe u w v

/-- Extend scalars degree by degree along a ring homomorphism. -/
noncomputable abbrev extendScalarsComplex {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) : Comp.{max w v} R ⥤ Comp.{max w v} S :=
  (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)

/-- The degreewise Mathlib restriction functor used in the acyclicity tests. -/
private noncomputable abbrev restrictScalarsComplex {R : Type u} {S : Type w} [Ring R] [Ring S]
    (f : R →+* S) : Comp.{v} S ⥤ Comp.{v} R :=
  (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)

/-- Exactness in each degree is the same after restriction of scalars. -/
theorem ScalarExtensionModels.restrict_acyclic_iff {R : Type u} {S : Type w} [Ring R] [Ring S]
    (f : R →+* S) (A : Comp.{v} S) :
    ((restrictScalarsComplex f).obj A).Acyclic ↔ A.Acyclic := by
  simp only [HomologicalComplex.acyclic_iff, HomologicalComplex.exactAt_iff]
  apply forall_congr'
  intro i
  change ((A.sc i).map (ModuleCat.restrictScalars f)).Exact ↔ (A.sc i).Exact
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

/-- Extending scalars carries K-projective complexes to K-projective complexes. -/
theorem isKProjective_extendScalars {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Comp.{max w v} R) (hP : IsKProjective P) :
    IsKProjective ((extendScalarsComplex f).obj P) := by
  constructor
  intro A g hA
  let E : Comp.{max w v} R ⥤ Comp.{max w v} S := extendScalarsComplex f
  let U : Comp.{max w v} S ⥤ Comp.{max w v} R := restrictScalarsComplex f
  let adj := ModuleCat.extendRestrictScalarsAdj.{v} f
  let η : 𝟭 (Comp.{max w v} R) ⟶ E ⋙ U := adj.unit.mapHomologicalComplex (.up ℤ)
  let ε : U ⋙ E ⟶ 𝟭 (Comp.{max w v} S) := adj.counit.mapHomologicalComplex (.up ℤ)
  let g' : P ⟶ U.obj A := η.app P ≫ U.map g
  obtain ⟨h⟩ := hP.nonempty_homotopy_zero g' ((ScalarExtensionModels.restrict_acyclic_iff f A).2 hA)
  have hg : E.map g' ≫ ε.app A = g := by
    apply HomologicalComplex.hom_ext
    intro i
    change (ModuleCat.extendScalars f).map
      (adj.unit.app (P.X i) ≫ (ModuleCat.restrictScalars f).map (g.f i)) ≫
        adj.counit.app (A.X i) = g.f i
    simpa only [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] using
      (adj.homEquiv (P.X i) (A.X i)).symm_apply_apply (g.f i)
  let : (ModuleCat.extendScalars.{u,w,max w v} f).Additive := by
    let := adj.isLeftAdjoint
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (ModuleCat.extendScalars f)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have hz : E.map (0 : P ⟶ U.obj A) ≫ ε.app A = 0 := by rw [E.map_zero, zero_comp]
  exact ⟨((Homotopy.ofEq hg.symm).trans
    (((ModuleCat.extendScalars f).mapHomotopy h).compRight (ε.app A))).trans
      (Homotopy.ofEq hz)⟩

section Tensor

open HomologicalComplex (ιTensorObj)

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Inverse of the module-level cancellation of the added scalars on the right. -/
private noncomputable def tensorExtendScalarsModuleIso (M : ModuleCat.{u} S) (N : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars f).obj M ⊗ N ≅
    (ModuleCat.restrictScalars f).obj (M ⊗ (ModuleCat.extendScalars f).obj N) := by
  letI : Algebra R S := f.toAlgebra
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  let T := M ⊗[S] (S ⊗[R] N)
  letI : Module R T := Module.compHom T f
  let e : T ≃ₗ[S] M ⊗[R] N := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M N
  let eR : (M ⊗[R] N) ≃ₗ[R] T :=
    { e.symm.toAddEquiv with
      map_smul' := fun r z => by
        change e.symm (r • z) = f r • e.symm z
        calc
          e.symm (r • z) = e.symm (f r • z) :=
            congrArg e.symm (IsScalarTower.algebraMap_smul S r z).symm
          _ = f r • e.symm z := e.symm.map_smul (f r) z }
  exact eR.toModuleIso

private theorem tensorExtendScalarsModuleIso_hom_tmul
    (M : ModuleCat.{u} S) (N : ModuleCat.{u} R) (x : (ModuleCat.restrictScalars f).obj M) (y : N) :
    (tensorExtendScalarsModuleIso f M N).hom (x ⊗ₜ[R] y) =
      (show M from x) ⊗ₜ[S] (show (ModuleCat.extendScalars f).obj N from (1 : S) ⊗ₜ[R,f] y) :=
  rfl

variable (A : Comp.{u} S) (P : Comp.{u} R)

private noncomputable def tensorExtendScalarsSummandIso (n : ℤ) :
    Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      ((restrictScalarsComplex f).obj A).X p.1.1 ⊗ P.X p.1.2) ≅
    Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      A.X p.1.1 ⊗ ((extendScalarsComplex f).obj P).X p.1.2) ⋙ ModuleCat.restrictScalars f :=
  Discrete.natIso (fun p => tensorExtendScalarsModuleIso f (A.X p.as.1.1) (P.X p.as.1.2))

private noncomputable def tensorExtendScalarsCofanIsColimit (n : ℤ) :
    IsColimit ((Cocone.precompose (tensorExtendScalarsSummandIso f A P n).hom).obj
      ((ModuleCat.restrictScalars f).mapCocone (tensorCofan A ((extendScalarsComplex f).obj P) n))) :=
  (IsColimit.precomposeHomEquiv _ _).symm
    (isColimitOfPreserves (ModuleCat.restrictScalars f)
      (tensorCofan_isColimit A ((extendScalarsComplex f).obj P) n).some)

private noncomputable def tensorExtendScalarsDegreeIso (n : ℤ) :
    (tensorComplex ((restrictScalarsComplex f).obj A) P).X n ≅
      ((restrictScalarsComplex f).obj (tensorComplex A ((extendScalarsComplex f).obj P))).X n :=
  (tensorCofan_isColimit ((restrictScalarsComplex f).obj A) P n).some.coconePointUniqueUpToIso
    (tensorExtendScalarsCofanIsColimit f A P n)

private theorem tensorExtendScalarsDegreeIso_hom_tmul (i j n : ℤ) (h : i + j = n)
    (x : ((restrictScalarsComplex f).obj A).X i) (y : P.X j) :
    (tensorExtendScalarsDegreeIso f A P n).hom
        (ιTensorObj ((restrictScalarsComplex f).obj A) P i j n h (x ⊗ₜ[R] y)) =
      ιTensorObj A ((extendScalarsComplex f).obj P) i j n h
        ((show A.X i from x) ⊗ₜ[S]
          (show ((extendScalarsComplex f).obj P).X j from (1 : S) ⊗ₜ[R,f] y)) := by
  have he := IsColimit.comp_coconePointUniqueUpToIso_hom
    (tensorCofan_isColimit ((restrictScalarsComplex f).obj A) P n).some
    (tensorExtendScalarsCofanIsColimit f A P n) (Discrete.mk ⟨(i, j), h⟩)
  change ιTensorObj ((restrictScalarsComplex f).obj A) P i j n h ≫
      (tensorExtendScalarsDegreeIso f A P n).hom =
    (tensorExtendScalarsModuleIso f (A.X i) (P.X j)).hom ≫
      (ModuleCat.restrictScalars f).map (ιTensorObj A ((extendScalarsComplex f).obj P) i j n h) at he
  have ht := ConcreteCategory.congr_hom he (x ⊗ₜ[R] y)
  change (tensorExtendScalarsDegreeIso f A P n).hom
      (ιTensorObj ((restrictScalarsComplex f).obj A) P i j n h (x ⊗ₜ[R] y)) =
    ιTensorObj A ((extendScalarsComplex f).obj P) i j n h
      ((tensorExtendScalarsModuleIso f (A.X i) (P.X j)).hom (x ⊗ₜ[R] y)) at ht
  rw [tensorExtendScalarsModuleIso_hom_tmul f (A.X i) (P.X j) x y] at ht
  exact ht

/-- Cancellation of extension of scalars inside the direct-sum total tensor.
The comparison is over the source ring, after restricting the target. -/
private noncomputable def tensorExtendScalarsIso :
    tensorComplex ((restrictScalarsComplex f).obj A) P ≅
      (restrictScalarsComplex f).obj (tensorComplex A ((extendScalarsComplex f).obj P)) := by
  refine HomologicalComplex.Hom.isoOfComponents (tensorExtendScalarsDegreeIso f A P) ?_
  intro n m hnm
  have hstep : n + 1 = m := hnm
  apply (tensorCofan_isColimit ((restrictScalarsComplex f).obj A) P n).some.hom_ext
  rintro ⟨⟨⟨i, j⟩, hij⟩⟩
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change
    (tensorComplex A ((extendScalarsComplex f).obj P)).d n m
      ((tensorExtendScalarsDegreeIso f A P n).hom
        (ιTensorObj ((restrictScalarsComplex f).obj A) P i j n hij (x ⊗ₜ[R] y))) =
    (tensorExtendScalarsDegreeIso f A P m).hom
      ((tensorComplex ((restrictScalarsComplex f).obj A) P).d n m
        (ιTensorObj ((restrictScalarsComplex f).obj A) P i j n hij (x ⊗ₜ[R] y)))
  rw [tensorExtendScalarsDegreeIso_hom_tmul f A P i j n hij x y,
    tensor_d_apply i j n m hij hstep, tensor_d_apply i j n m hij hstep]
  simp only [map_add, Units.smul_def, map_zsmul, tensorExtendScalarsDegreeIso_hom_tmul]
  rfl

/-- Extending scalars carries K-flat complexes to K-flat complexes. -/
theorem isKFlat_extendScalars (hP : IsKFlat P) :
    IsKFlat ((extendScalarsComplex f).obj P) := by
  intro A hA
  have h := hP ((restrictScalarsComplex f).obj A)
    ((ScalarExtensionModels.restrict_acyclic_iff f A).2 hA)
  apply (ScalarExtensionModels.restrict_acyclic_iff f _).1
  intro n
  exact (h n).of_iso (tensorExtendScalarsIso f A P)

end Tensor

end DerivedFormalization
