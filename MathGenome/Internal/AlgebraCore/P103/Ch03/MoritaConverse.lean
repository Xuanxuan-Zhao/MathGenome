import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.MoritaConverse

noncomputable section

universe u v w x y

namespace P103.Ch03.MoritaConverse

open CategoryTheory Limits
open scoped DirectSum
open P103.Specs.Ch03.MoritaConverse

private theorem equivalence_additive {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryProducts C] [HasZeroObject C]
    [HasZeroObject D] (E : C ≌ D) : E.functor.Additive :=
  E.functor.additive_of_preserves_binary_products

theorem preservation : preservationType.{u,v,w} := by
  intro R S _ _ E
  let := equivalence_additive E
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro X Y f
  rw [← ModuleCat.epi_iff_surjective, ← ModuleCat.epi_iff_surjective]
  exact ⟨fun _ => inferInstance, fun h => E.functor.epi_of_epi_map h⟩

/-- Lifting along surjections is preserved in both directions. -/
theorem projectivity : projectivityType.{u,v,w} := by
  intro R S _ _ E A
  rw [IsProjective.iff_projective, IsProjective.iff_projective]
  exact (E.map_projective_iff A).symm

/-- Extensionality for maps out of a lifted regular module. -/
private theorem regular_hom_ext {S : Type u} [Ring S]
    {M : ModuleCat.{max u v} Sᵐᵒᵖ} (f g : regular.{u,v} S ⟶ M)
    (h : f ⟨1⟩ = g ⟨1⟩) : f = g := by
  ext x
  have hx : x = x.down • (⟨1⟩ : regular.{u,v} S) := by
    apply ULift.ext
    simp
  rw [hx, map_smul, map_smul, h]

/-- A categorical equivalence preserves projectivity without an additive assumption. -/
theorem image_projective (R : Type u) (S : Type v) [Ring R] [Ring S]
    (E : ModuleCat.{max u v w} Sᵐᵒᵖ ≌ ModuleCat.{max u v w} Rᵐᵒᵖ) :
    Module.Projective Rᵐᵒᵖ (E.functor.obj (regular.{v,max u w} S)) := by
  have : Module.Projective Sᵐᵒᵖ (regular.{v,max u w} S) :=
    Module.Projective.of_equiv (ULift.moduleEquiv (R := Sᵐᵒᵖ)).symm
  have : CategoryTheory.Projective (regular.{v,max u w} S) := inferInstance
  have := (E.map_projective_iff (regular.{v,max u w} S)).mpr inferInstance
  infer_instance

/-- The regular module separates linear maps, also over the zero ring. -/
theorem regular_separator (S : Type u) [Ring S] :
    IsSeparator (regular.{u,v} S) := by
  rw [isSeparator_def]
  intro X Y f g h
  ext x
  let a : regular.{u,v} S ⟶ X := ModuleCat.ofHom
    ((LinearMap.toSpanSingleton Sᵐᵒᵖ X x).comp ULift.moduleEquiv.toLinearMap)
  have hx := congrArg (fun k : regular.{u,v} S ⟶ Y => k ⟨1⟩) (h a)
  simpa [a] using hx

/-- A separator in a module category gives an actual surjection from a sum. -/
theorem generator_of_separator {R : Type u} [Ring R]
    (P : ModuleCat.{v} Rᵐᵒᵖ) (hP : IsSeparator P) : Generator P := by
  classical
  intro M
  let X : (P ⟶ M) → ModuleCat.{v} Rᵐᵒᵖ := fun _ => P
  have : Epi (Sigma.desc (fun f : P ⟶ M => f)) :=
    (isSeparator_iff_epi P).mp hP M
  let e := ModuleCat.coprodIsoDirectSum X
  refine ⟨P ⟶ M, (Sigma.desc (fun f : P ⟶ M => f)).hom.comp e.inv.hom, ?_⟩
  exact ((ModuleCat.epi_iff_surjective _).mp inferInstance).comp
    ((ModuleCat.epi_iff_surjective e.inv).mp inferInstance)

/-- The regular module is small with respect to arbitrary direct sums. -/
theorem regular_finiteSum (S : Type u) [Ring S] :
    FiniteSumFactorization.{max u v + 1, max u v, max u v} (regular.{u,v} S) := by
  classical
  intro I X c hc f
  let hd := ModuleCat.coproductCoconeIsColimit X
  let e : ModuleCat.of Sᵐᵒᵖ (⨁ j, X j) ≅ c.pt := hd.coconePointUniqueUpToIso hc
  let y : ⨁ j, X j := e.inv (f ⟨1⟩)
  let g : ∀ j, regular.{u,v} S ⟶ X j := fun j => ModuleCat.ofHom
    ((LinearMap.toSpanSingleton Sᵐᵒᵖ (X j) (y j)).comp ULift.moduleEquiv.toLinearMap)
  refine ⟨y.support, g, regular_hom_ext _ _ ?_⟩
  have hy : (∑ j ∈ y.support, c.inj j (y j)) = f ⟨1⟩ := by
    have he (j : I) : e.hom (DirectSum.lof Sᵐᵒᵖ I (fun j => X j) j (y j)) =
        c.inj j (y j) := by
      exact congrArg (fun k : X j ⟶ c.pt => k (y j))
        (hd.comp_coconePointUniqueUpToIso_hom hc ⟨j⟩)
    calc
      (∑ j ∈ y.support, c.inj j (y j)) =
          e.hom (∑ j ∈ y.support, DirectSum.of (fun j => X j) j (y j)) := by
        simp only [map_sum]
        exact Finset.sum_congr rfl fun j _ => (he j).symm
      _ = e.hom y := congrArg e.hom (DirectSum.sum_support_of y)
      _ = f ⟨1⟩ := by simp [y]
  simpa [g] using hy.symm

/-- Smallness is categorical once addition has been recovered. -/
theorem finiteSum_of_equivalence {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{x} D] [Preadditive C] [Preadditive D]
    [HasBinaryProducts C] [HasZeroObject C] [HasZeroObject D]
    (E : C ≌ D) (P : C) (hP : FiniteSumFactorization.{u,w,y} P) :
    FiniteSumFactorization.{v,x,y} (E.functor.obj P) := by
  classical
  let := equivalence_additive E
  intro I X c hc f
  let c' : Cofan (fun j => E.inverse.obj (X j)) :=
    Cofan.mk (E.inverse.obj c.pt) (fun j => E.inverse.map (c.inj j))
  have hc' : IsColimit c' :=
    (Cofan.isColimitMapCoconeEquiv E.inverse X c) (isColimitOfPreserves E.inverse hc)
  obtain ⟨s, g, hg⟩ := hP I _ c' hc' ((E.unitIso.app P).hom ≫ E.inverse.map f)
  refine ⟨s, fun j => E.functor.map (g j) ≫ (E.counitIso.app (X j)).hom, ?_⟩
  calc
    f = E.functor.map ((E.unitIso.app P).hom ≫ E.inverse.map f) ≫
        (E.counitIso.app c.pt).hom := by simp
    _ = (∑ j ∈ s, E.functor.map (g j ≫ c'.inj j)) ≫
        (E.counitIso.app c.pt).hom := by rw [hg, E.functor.map_sum]
    _ = ∑ j ∈ s, (E.functor.map (g j) ≫ (E.counitIso.app (X j)).hom) ≫ c.inj j := by
      simp only [Preadditive.sum_comp, Functor.map_comp, Category.assoc]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [c']
      rw [E.counit_naturality]

/-- Smallness is invariant under isomorphism of the source object. -/
theorem finiteSum_of_iso {C : Type u} [Category.{v} C] [Preadditive C]
    {A B : C} (i : A ≅ B) (hA : FiniteSumFactorization.{u,v,w} A) :
    FiniteSumFactorization.{u,v,w} B := by
  intro I X c hc f
  obtain ⟨s, g, hg⟩ := hA I X c hc (i.hom ≫ f)
  refine ⟨s, fun j => i.inv ≫ g j, ?_⟩
  calc
    f = i.inv ≫ (i.hom ≫ f) := by simp
    _ = ∑ j ∈ s, (i.inv ≫ g j) ≫ c.inj j := by
      rw [hg, Preadditive.comp_sum]
      simp only [Category.assoc]

/-- A small projective module is finitely generated: split a free cover and
use the finitely many summands needed by its section. -/
theorem finite_of_projective_finiteSum {T : Type u} [Ring T]
    (P : ModuleCat.{max u v} T) [Module.Projective T P]
    (hP : FiniteSumFactorization.{max u v + 1, max u v, max u v} P) :
    Module.Finite T P := by
  classical
  let X : P → ModuleCat.{max u v} T := fun _ => ModuleCat.of T (ULift.{v} T)
  let d := ModuleCat.coproductCocone X
  let q : (⨁ j : P, X j) →ₗ[T] P := DirectSum.toModule T P P
    (fun j => (LinearMap.toSpanSingleton T P j).comp ULift.moduleEquiv.toLinearMap)
  have hq : Function.Surjective q := by
    intro p
    refine ⟨DirectSum.lof T P (fun j => X j) p ⟨1⟩, ?_⟩
    simp only [q, DirectSum.toModule_lof, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
    change (1 : T) • p = p
    exact one_smul T p
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q (LinearMap.id : P →ₗ[T] P) hq
  obtain ⟨t, g, hg⟩ := hP P X d (ModuleCat.coproductCoconeIsColimit X)
    (ModuleCat.ofHom s)
  apply Module.Finite.of_fg_top
  refine ⟨t, ?_⟩
  apply top_unique
  intro p _
  have hp : p = ∑ j ∈ t, (g j p).down • j := by
    calc
      p = q (s p) := (LinearMap.congr_fun hs p).symm
      _ = q ((∑ j ∈ t, g j ≫ d.inj j) p) := by rw [← hg]; rfl
      _ = ∑ j ∈ t, (g j p).down • j := by
        change q ((∑ j ∈ t, g j ≫ d.inj j).hom p) = _
        simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
        change q (∑ j ∈ t, DirectSum.lof T P (fun j => X j) j (g j p)) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        change q (DirectSum.lof T P (fun j => X j) j (g j p)) = _
        simp only [q, DirectSum.toModule_lof, LinearMap.comp_apply,
          LinearMap.toSpanSingleton_apply]
        rfl
  rw [hp]
  exact Submodule.sum_mem _ fun j hj =>
    Submodule.smul_mem _ _ (Submodule.subset_span hj)

/-- Full faithfulness and the recovered additive structure identify endomorphism
rings, with composition (rather than reverse composition) as multiplication. -/
theorem equivalence_endomorphisms (R : Type u) (S : Type v) [Ring R] [Ring S]
    (E : ModuleCat.{max u v w} Sᵐᵒᵖ ≌ ModuleCat.{max u v w} Rᵐᵒᵖ)
    (A : ModuleCat.{max u v w} Sᵐᵒᵖ) :
    ∃ e : Module.End Sᵐᵒᵖ A ≃+* Module.End Rᵐᵒᵖ (E.functor.obj A),
      ∀ f, e f = (E.functor.map (ModuleCat.ofHom f)).hom := by
  let := equivalence_additive E
  let φ : Module.End Sᵐᵒᵖ A →+* Module.End Rᵐᵒᵖ (E.functor.obj A) :=
    { toFun := fun f => (E.functor.map (ModuleCat.ofHom f)).hom
      map_one' := by
        exact congrArg ModuleCat.Hom.hom (E.functor.map_id A)
      map_mul' := fun f g => by
        exact congrArg ModuleCat.Hom.hom
          (E.functor.map_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))
      map_zero' := by
        exact congrArg ModuleCat.Hom.hom (E.functor.map_zero (X := A) (Y := A))
      map_add' := fun f g => by
        exact congrArg ModuleCat.Hom.hom (E.functor.map_add (f := ModuleCat.ofHom f)
          (g := ModuleCat.ofHom g)) }
  have hφ : Function.Bijective φ := by
    constructor
    · intro f g h
      exact congrArg ModuleCat.Hom.hom (E.functor.map_injective (ModuleCat.hom_ext h))
    · intro f
      obtain ⟨g, hg⟩ := E.functor.map_surjective (ModuleCat.ofHom f)
      exact ⟨g.hom, congrArg ModuleCat.Hom.hom hg⟩
  exact ⟨RingEquiv.ofBijective φ hφ, fun _ => rfl⟩

/-- The complete converse of the progenerator theorem. -/
theorem converse : converseType.{u,v,w} := by
  intro R S _ _ E P i
  have hsmallA := finiteSum_of_equivalence E (regular.{v,max u w} S)
    (regular_finiteSum S)
  have hsmallP := finiteSum_of_iso i hsmallA
  have : Module.Projective Rᵐᵒᵖ (E.functor.obj (regular.{v,max u w} S)) :=
    image_projective R S E
  have : Module.Projective Rᵐᵒᵖ P := Module.Projective.of_equiv i.toLinearEquiv
  have hsepA := (regular_separator.{v,max u w} S).of_equivalence E
  have hsepP : IsSeparator P := by
    rw [isSeparator_def]
    intro X Y f g h
    apply hsepA.def f g
    intro a
    have ha := h (i.inv ≫ a)
    simpa using congrArg (fun k => i.hom ≫ k) ha
  refine ⟨finite_of_projective_finiteSum.{u,max v w} P hsmallP, inferInstance,
    generator_of_separator P hsepP, hsmallP, ?_⟩
  obtain ⟨e₀, he₀⟩ := equivalence_endomorphisms R S E (regular.{v,max u w} S)
  let e₁ : Module.End Rᵐᵒᵖ (E.functor.obj (regular.{v,max u w} S)) ≃+*
      Module.End Rᵐᵒᵖ P := i.toLinearEquiv.conjRingEquiv
  let e₂ : Module.End Sᵐᵒᵖ (regular.{v,max u w} S) ≃+* S :=
    (ULift.moduleEquiv (R := Sᵐᵒᵖ)).conjRingEquiv.trans
      ((RingEquiv.moduleEndSelf Sᵐᵒᵖ).symm.trans (RingEquiv.opOp S).symm)
  refine ⟨e₁.symm.trans (e₀.symm.trans e₂), ?_⟩
  intro f
  change (e₁.symm.trans (e₀.symm.trans e₂))
    (e₁ ((E.functor.map (ModuleCat.ofHom f)).hom)) = _
  rw [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, ← he₀,
    RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  rfl

end P103.Ch03.MoritaConverse
