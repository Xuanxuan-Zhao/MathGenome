import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ProjectiveCovers
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ComponentBounds
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.TruncatedProjectives
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Noetherian.Orzech
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open scoped Classical ModuleCat.Algebra

namespace RepTheorySurvey.CategoryO.ProjectiveCovers

open Specs.RepTheorySurvey.CategoryO.ProjectiveCovers
open Specs.RepTheorySurvey.CategoryO.ComponentBounds
  (inComponent_value simpleLabels_value)
open Specs.RepTheorySurvey.CategoryO.ComponentProjectors
  (Index component component_map_mem componentMap projection)
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient (quotientHighestVector)

open private submodule_mem_O from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects

universe u v

abbrev IsProjectiveCover : ProjectiveCoverType.{u, v} := @projectiveCover_value

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable {D : Setup g}

private theorem projectiveLift {P X Y : O.{u, v} D} (hP : Projective P)
    (p : P.obj →ₗ[U g] Y.obj) (q : X.obj →ₗ[U g] Y.obj) (hq : Function.Surjective q) :
    ∃ f : P.obj →ₗ[U g] X.obj, q.comp f = p := by
  let := hP
  let e : X ⟶ Y := ObjectProperty.homMk (ModuleCat.ofHom q)
  have he : Epi ((objects D).ι.map e) := (ModuleCat.epi_iff_surjective _).mpr hq
  let : Epi e := (objects D).ι.epi_of_epi_map he
  obtain ⟨f, hf⟩ := Projective.factors
    (ObjectProperty.homMk (ModuleCat.ofHom p) : P ⟶ Y) e
  exact ⟨f.hom.hom, congrArg (fun a : P ⟶ Y => a.hom.hom) hf⟩

omit [FiniteDimensional ℂ g] in
private theorem restrict_surjective_iff_sup_ker {X Y : ModuleCat.{v} (U g)}
    (p : X →ₗ[U g] Y) (hp : Function.Surjective p) (J : Submodule (U g) X) :
    Function.Surjective (p.domRestrict J) ↔ J ⊔ p.ker = ⊤ := by
  constructor
  · intro hj
    apply top_unique
    intro x _
    obtain ⟨j, he⟩ := hj (p x)
    have he' : p (j : X) = p x := he
    exact Submodule.mem_sup.mpr
      ⟨j, j.property, x - j, by simp [LinearMap.mem_ker, map_sub, he'], by abel⟩
  · intro hj y
    obtain ⟨x, rfl⟩ := hp y
    obtain ⟨j, hj', k, hk, rfl⟩ :=
      Submodule.mem_sup.mp (show x ∈ J ⊔ p.ker by rw [hj]; exact Submodule.mem_top)
    exact ⟨⟨j, hj'⟩, by
      change p j = p (j + k)
      simp [LinearMap.mem_ker.mp hk]⟩

theorem projectiveCover_of_indecomposable : CoverOfIndecomposableType.{u, v} := by
  intro g _ _ _ D X Y p hP hInd hY hp
  let : IsSimpleModule (U g) Y.obj := (simple_iff_isSimpleModule D Y).mp hY
  let : Nontrivial Y.obj := IsSimpleModule.nontrivial (U g) Y.obj
  have hLength := isFiniteLength_iff_isNoetherian_isArtinian.mp (categoryO_finiteLength D X)
  let : IsNoetherian (U g) X.obj := hLength.1
  let : IsArtinian (U g) X.obj := hLength.2
  refine ⟨hP, hp, fun J hJ => ?_⟩
  let J' : O.{u, v} D :=
    ⟨ModuleCat.of (U g) J, submodule_mem_O D X.obj X.property J (IsNoetherian.noetherian J)⟩
  obtain ⟨f, hf⟩ := projectiveLift (X := J') hP p (p.domRestrict J)
    ((restrict_surjective_iff_sup_ker p hp J).mpr hJ)
  let a : Module.End (U g) X.obj := J.subtype.comp f
  have ha (x : X.obj) : p (a x) = p x := DFunLike.congr_fun hf x
  have hpow (n : ℕ) (x : X.obj) : p ((a ^ n) x) = p x := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ha, ih]
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp a.eventually_isCompl_ker_pow_range_pow
  have hc := hn (n + 1) (Nat.le_succ n)
  have hr : LinearMap.range (a ^ (n + 1)) ≠ ⊥ := by
    intro he
    obtain ⟨y, hy⟩ := exists_ne (0 : Y.obj)
    obtain ⟨x, rfl⟩ := hp y
    have hz : (a ^ (n + 1)) x = 0 :=
      DFunLike.congr_fun (LinearMap.range_eq_bot.mp he) x
    exact hy (by rw [← hpow (n + 1) x, hz, map_zero])
  have hk := (hInd.2 _ _ hc).resolve_right hr
  have htop : LinearMap.range (a ^ (n + 1)) = ⊤ :=
    eq_top_of_bot_isCompl (hk ▸ hc)
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := LinearMap.range_eq_top.mp htop x
  rw [pow_succ', Module.End.mul_apply]
  exact (f ((a ^ n) y)).property

theorem unique_maximal_submodule : UniqueMaximalSubmoduleType.{u, v} := by
  intro g _ _ _ D X Y p hY hp
  let : IsSimpleModule (U g) Y.obj := (simple_iff_isSimpleModule D Y).mp hY
  refine ⟨LinearMap.isCoatom_ker_of_surjective hp.2.1, fun J hJ => ?_⟩
  have hle : p.ker ≤ J := by
    by_contra hn
    have hh : J < J ⊔ p.ker := left_lt_sup.mpr hn
    exact hJ.ne_top (hp.2.2 J (hJ.2 _ hh))
  exact ((LinearMap.isCoatom_ker_of_surjective hp.2.1).le_iff_eq hJ.ne_top).mp hle

private theorem lift_surjective {X X' Y : O.{u, v} D}
    {p : X.obj →ₗ[U g] Y.obj} {p' : X'.obj →ₗ[U g] Y.obj}
    (hp : Function.Surjective p) (hp' : IsProjectiveCover X' p')
    {f : X.obj →ₗ[U g] X'.obj} (hf : p'.comp f = p) :
    Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  apply hp'.2.2
  apply (restrict_surjective_iff_sup_ker p' hp'.2.1 _).mp
  intro y
  obtain ⟨x, hx⟩ := hp y
  exact ⟨⟨f x, LinearMap.mem_range_self f x⟩,
    (DFunLike.congr_fun hf x).trans hx⟩

theorem unique_over_target : UniquenessType.{u, v} := by
  intro g _ _ _ D X X' Y p p' hp hp'
  obtain ⟨f, hf⟩ := projectiveLift hp.1 p p' hp'.2.1
  obtain ⟨q, hq⟩ := projectiveLift hp'.1 p' p hp.2.1
  have hfs := lift_surjective hp.2.1 hp' hf
  have hqs := lift_surjective hp'.2.1 hp hq
  let : IsNoetherian (U g) X.obj :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (categoryO_finiteLength D X)).1
  have hi := IsNoetherian.injective_of_surjective_endomorphism (q.comp f) (hqs.comp hfs)
  exact ⟨LinearEquiv.ofBijective f ⟨fun x y h => hi (congrArg q h), hfs⟩, hf⟩

private theorem surjective_of_epi_O {X Y : O.{u, v} D} (f : X ⟶ Y) [Epi f] :
    Function.Surjective f.hom.hom := by
  let I : O.{u, v} D ⥤ ModuleCat.{v} (U g) := (objects D).ι
  let : ∀ {X Y : O.{u, v} D} (f : X ⟶ Y),
      Limits.PreservesColimit (Limits.parallelPair f 0) I :=
    fun f => (objects D).preservesCokernels_ι f
  let : I.PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels I
  exact (ModuleCat.epi_iff_surjective (I.map f)).mp inferInstance

private theorem inComponent_of_surjection (k : Index D) {X Y : ModuleCat.{v} (U g)}
    (f : X →ₗ[U g] Y) (hf : Function.Surjective f) (hX : inComponent_value D X k) :
    inComponent_value D Y k := by
  change component D X k = ⊤ at hX
  change component D Y k = ⊤
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  exact component_map_mem f k (by rw [hX]; exact Submodule.mem_top)

private theorem projection_apply_summand (k : Index D) (X : O.{u, v} D)
    (h : DirectSum.IsInternal (component D X.obj)) (x : component D X.obj k) :
    projection D h k (x : X.obj) = x :=
  DFunLike.congr_fun (ComponentProjectors.projection_on_summands D X h k).1 x

private theorem component_in_own_index (k : Index D) (X : O.{u, v} D) :
    inComponent_value D ((ComponentProjectors.projectorFunctor D k).obj X).obj k := by
  let h := (ComponentProjectors.component_decomposition D X).1
  change component D ((ComponentProjectors.projectorFunctor D k).obj X).obj k = ⊤
  apply top_unique
  intro x _
  have hx : projection D h k (Subtype.val x) ∈
      component D ((ComponentProjectors.projectorFunctor D k).obj X).obj k :=
    component_map_mem (X := X.obj) (Y := ((ComponentProjectors.projectorFunctor D k).obj X).obj)
      (projection D h k) k x.property
  rwa [projection_apply_summand k X h x] at hx

private theorem surjective_of_epi_component (k : Index D)
    {X Y : (componentObjects D k).FullSubcategory} (e : X ⟶ Y) [Epi e] :
    Function.Surjective e.hom.hom.hom := by
  let S := LinearMap.range e.hom.hom.hom
  let Z := ModuleCat.of (U g) (Y.obj.obj ⧸ S)
  let q : Y.obj.obj →ₗ[U g] Z := S.mkQ
  have hq : Function.Surjective q := S.mkQ_surjective
  let : Epi (ModuleCat.ofHom q) := (ModuleCat.epi_iff_surjective _).mpr hq
  have hO : objects D Z := ObjectProperty.prop_of_epi (P := objects D)
    (ModuleCat.ofHom q) Y.obj.property
  let Q : (componentObjects D k).FullSubcategory :=
    ⟨⟨Z, hO⟩, inComponent_of_surjection k q hq Y.property⟩
  let q' : Y ⟶ Q := ObjectProperty.homMk (ObjectProperty.homMk (ModuleCat.ofHom q))
  have hzero : q' = ObjectProperty.homMk (ObjectProperty.homMk (ModuleCat.ofHom 0)) := by
    apply (cancel_epi e).mp
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext x
    change q (e.hom.hom.hom x) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr ⟨x, rfl⟩
  intro y
  exact (Submodule.Quotient.mk_eq_zero S).mp
    (congrArg (fun f : Y ⟶ Q => f.hom.hom.hom y) hzero)

/-- Exact projection and the common cutoff give projectivity in all of O. -/
theorem projectedTruncation_projective : ProjectedProjectiveType.{u} := by
  intro g _ _ _ D k μ Λ hμ hΛ
  obtain ⟨hP, hproj⟩ := TruncatedProjectives.projective D μ Λ hμ
  let X : O.{u, u} D := ⟨TruncatedProjectives.P D μ Λ, hP.1⟩
  let F := ComponentProjectors.projectorFunctor.{u, u} D k
  let X₀ := F.obj X
  let hX := (ComponentProjectors.component_decomposition D X).1
  have hX₀ := component_in_own_index k X
  let truncation (Y : O.{u, u} D) : TruncatedProjectives.Cutoff D Λ :=
    ⟨(F.obj Y).obj, (F.obj Y).property, hΛ.2.2 (F.obj Y) (component_in_own_index k Y)⟩
  have hp₀ : Projective X₀ := by
    constructor
    intro B C f e he
    let : F.PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_preserves_shortExact_right F
        (fun S hS => by
          have hs := ComponentProjectors.projector_shortExact D k S hS
          exact ⟨hs.exact, hs.epi_g⟩)
    have hsurj := surjective_of_epi_O (F.map e)
    let q : truncation B ⟶ truncation C := ObjectProperty.homMk (F.map e).hom
    let : Epi q := (TruncatedProjectives.cutoffObjects D Λ).ι.epi_of_epi_map
      ((ModuleCat.epi_iff_surjective _).mpr hsurj)
    let a : (⟨TruncatedProjectives.P D μ Λ, hP⟩ : TruncatedProjectives.Cutoff D Λ) ⟶
        truncation C := ObjectProperty.homMk (ModuleCat.ofHom
      ((f.hom.hom.codRestrict _ (fun x =>
        component_map_mem f.hom.hom k (by
          change component D X₀.obj k = ⊤ at hX₀
          rw [hX₀]
          exact Submodule.mem_top))).comp (projection D hX k)))
    let := hproj
    obtain ⟨b, hb⟩ := Projective.factors a q
    let b₀ : X₀.obj →ₗ[U g] B.obj :=
      (component D B.obj k).subtype.comp (b.hom.hom.domRestrict (component D X.obj k))
    refine ⟨ObjectProperty.homMk (ModuleCat.ofHom b₀), ?_⟩
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext x
    have hx := congrArg (fun z : _ ⟶ truncation C => z.hom.hom (Subtype.val x)) hb
    have hv := congrArg Subtype.val hx
    change e.hom.hom (b₀ x) = f.hom.hom (projection D hX k (Subtype.val x)) at hv
    rw [projection_apply_summand k X hX x] at hv
    exact hv
  refine ⟨X₀.property, hX₀, hp₀, ⟨fun {B C} f e he => ?_⟩⟩
  obtain ⟨b, hb⟩ := projectiveLift hp₀ f.hom.hom.hom e.hom.hom.hom
    (surjective_of_epi_component k e)
  refine ⟨ObjectProperty.homMk (ObjectProperty.homMk (ModuleCat.ofHom b)), ?_⟩
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact ModuleCat.hom_ext hb

/-- A minimal direct summand on which a map is nonzero is indecomposable. -/
private theorem exists_indecomposable_summand
    {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsArtinian R M]
    (p : M →ₗ[R] N) (hp : p ≠ 0) :
    ∃ S T : Submodule R M, IsCompl S T ∧ p.domRestrict S ≠ 0 ∧
      (⊥ : Submodule R S) ≠ ⊤ ∧
      ∀ A B : Submodule R S, IsCompl A B → A = ⊥ ∨ B = ⊥ := by
  let Good (S : Submodule R M) : Prop :=
    ∃ r : M →ₗ[R] S, (∀ x : S, r x = x) ∧ p.domRestrict S ≠ 0
  have htop : Good ⊤ := by
    refine ⟨LinearMap.id.codRestrict ⊤ (fun _ => Submodule.mem_top), fun _ => rfl, ?_⟩
    intro hz
    apply hp
    ext x
    exact DFunLike.congr_fun hz (⟨x, Submodule.mem_top⟩ : (⊤ : Submodule R M))
  obtain ⟨S, hS⟩ := exists_minimal_of_wellFoundedLT Good ⟨⊤, htop⟩
  obtain ⟨r, hr, hne⟩ := hS.1
  refine ⟨S, r.ker, LinearMap.isCompl_of_proj hr, hne, ?_, ?_⟩
  · intro hbot
    apply hne
    ext x
    have hx : x = 0 := (Submodule.mem_bot R).mp (hbot.symm ▸ Submodule.mem_top)
    simp [hx]
  have eq_top_of_nonzero (A B : Submodule R S) (h : IsCompl A B)
      (hpA : (p.domRestrict S).domRestrict A ≠ 0) : A = ⊤ := by
    let A' := A.map S.subtype
    let e := Submodule.equivMapOfInjective S.subtype S.subtype_injective A
    have hA' : Good A' := by
      refine ⟨e.toLinearMap.comp ((A.projectionOnto B h).comp r), ?_, ?_⟩
      · intro x
        obtain ⟨a, rfl⟩ := e.surjective x
        have hval : ((e a : A') : M) = ((a : S) : M) :=
          Submodule.coe_equivMapOfInjective_apply S.subtype S.subtype_injective A a
        change e (A.projectionOnto B h (r (e a : A'))) = e a
        rw [hval, hr, Submodule.projectionOnto_apply_left]
      · intro hzero
        apply hpA
        ext a
        exact DFunLike.congr_fun hzero (e a)
    have heq := hS.eq_of_le hA' (Submodule.map_subtype_le S A)
    apply Submodule.map_injective_of_injective S.subtype_injective
    rwa [Submodule.map_subtype_top]
  intro A B hab
  by_cases hA : (p.domRestrict S).domRestrict A = 0
  · have hB : (p.domRestrict S).domRestrict B ≠ 0 := by
      intro hB
      apply hne
      apply LinearMap.ker_eq_top.mp
      apply top_unique
      rw [← hab.sup_eq_top]
      exact sup_le
        (fun a ha => DFunLike.congr_fun hA (⟨a, ha⟩ : A))
        (fun b hb => DFunLike.congr_fun hB (⟨b, hb⟩ : B))
    exact Or.inl (by
      rw [eq_top_of_nonzero B A hab.symm hB] at hab
      simpa using hab.inf_eq_bot)
  · exact Or.inr (by
      rw [eq_top_of_nonzero A B hab hA] at hab
      simpa using hab.inf_eq_bot)

/-- The map representing the simple's highest vector gives its cover on an
indecomposable summand of the projected truncation. -/
theorem exists_projectiveCover : ExistenceType.{u} := by
  intro g _ _ _ D μ
  let k := simpleIndex D μ
  have hlabel : μ ∈ simpleLabels_value D k := ⟨rfl, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, IsComponentBound D k Λ :=
    ComponentBounds.exists_common_upper_bound.{u, u} D k
  have hμ := hΛ.2.1 μ hlabel
  obtain ⟨hP₀, _, hproj, _⟩ := projectedTruncation_projective D k μ Λ hμ hΛ
  let P₀ : O.{u, u} D := ⟨projectedModule D k μ Λ, hP₀⟩
  let X : O.{u, u} D := ⟨TruncatedProjectives.P D μ Λ,
    (TruncatedProjectives.inCutoff D μ Λ hμ).1.1⟩
  let hX := (ComponentProjectors.component_decomposition D X).1
  obtain ⟨hL, hs, hv⟩ := simpleQuotient_in_O D μ
  let Y : O.{u, u} D := ⟨L D μ, hL⟩
  have hYk := (ComponentBounds.simpleQuotient_mem_component_iff D k μ).mpr hlabel
  let hY := (ComponentProjectors.component_decomposition D Y).1
  let Y' : TruncatedProjectives.Cutoff D Λ := ⟨Y.obj, hL, hΛ.2.2 Y hYk⟩
  obtain ⟨F, hF⟩ := TruncatedProjectives.represents D μ Λ hμ Y'
  let x : weightSpace D.cartan Y.obj μ :=
    ⟨quotientHighestVector D.cartan D.direction (character D μ), hv.2.1⟩
  let q : X.obj →ₗ[U g] Y.obj := F.symm x
  have hq : q (TruncatedProjectives.generatorP D μ Λ) = (x : Y.obj) := by
    rw [← hF q]
    exact congrArg Subtype.val (F.apply_symm_apply x)
  let p₀ : P₀.obj →ₗ[U g] Y.obj := q.domRestrict (component D X.obj k)
  have heval : p₀ (projection D hX k (TruncatedProjectives.generatorP D μ Λ)) =
      (x : Y.obj) := by
    let j : X ⟶ Y := ObjectProperty.homMk
      (ConcreteCategory.ofHom (C := ModuleCat (U g)) (X := X.obj) (Y := Y.obj) q)
    have hn := DFunLike.congr_fun (ComponentProjectors.projection_naturality D hX hY j k)
      (TruncatedProjectives.generatorP D μ Λ)
    have hn' := congrArg Subtype.val hn
    change (projection D hY k (q (TruncatedProjectives.generatorP D μ Λ)) : Y.obj) =
      p₀ (projection D hX k (TruncatedProjectives.generatorP D μ Λ)) at hn'
    rw [hq] at hn'
    have hxk : (x : Y.obj) ∈ component D Y.obj k := by
      change component D Y.obj k = ⊤ at hYk
      rw [hYk]
      exact Submodule.mem_top
    have he := congrArg Subtype.val (projection_apply_summand k Y hY ⟨x, hxk⟩)
    exact hn'.symm.trans he
  have hp₀ : p₀ ≠ 0 := by
    intro he
    apply hv.1
    change (x : Y.obj) = 0
    exact heval.symm.trans (by rw [he, LinearMap.zero_apply])
  let : IsSimpleModule (U g) Y.obj := (simple_iff_isSimpleModule D Y).mp hs
  have hf := isFiniteLength_iff_isNoetherian_isArtinian.mp (categoryO_finiteLength D P₀)
  let : IsNoetherian (U g) P₀.obj := hf.1
  let : IsArtinian (U g) P₀.obj := hf.2
  obtain ⟨S, T, hST, hpS, hInd⟩ := exists_indecomposable_summand p₀ hp₀
  have hS := submodule_mem_O D P₀.obj P₀.property S (IsNoetherian.noetherian S)
  let Z : O.{u, u} D := ⟨ModuleCat.of (U g) S, hS⟩
  let : Projective P₀ := hproj
  have hR : Retract Z P₀ := by
    refine ⟨ObjectProperty.homMk (ModuleCat.ofHom S.subtype),
      ObjectProperty.homMk (ModuleCat.ofHom (S.projectionOnto T hST)), ?_⟩
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext (Submodule.projectionOnto_apply_left hST)
  exact ⟨Λ, hΛ, hμ, hX, p₀, S, T, hS, heval, LinearMap.surjective_of_ne_zero hp₀,
    hST, hInd, projectiveCover_of_indecomposable D Z Y (p₀.domRestrict S)
      hR.projective hInd hs (LinearMap.surjective_of_ne_zero hpS)⟩

end RepTheorySurvey.CategoryO.ProjectiveCovers
