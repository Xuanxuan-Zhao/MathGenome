import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.BGGReciprocity
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ProjectiveCovers
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.FiniteLength
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.DualVermaExtensions
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Batteries.Tactic.OpenPrivate

/-! BGG reciprocity in finite category O. -/

noncomputable section

open CategoryTheory Function
open scoped Classical ModuleCat.Algebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)

namespace RepTheorySurvey.CategoryO.BGGReciprocity

open Specs.RepTheorySurvey.CategoryO (Setup objects_value restrictedLieRingModule restrictedLieModule)
open Specs.RepTheorySurvey.CategoryO.BGGReciprocity
open Specs.RepTheorySurvey.CategoryO.ProjectiveCovers (projectiveCover_value)
open ProjectiveFiltrations (Layer VermaFlag)
open RestrictedDual (dualModule dualMap dual_mem_O dual_simple costandard)
open private projectiveLift from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ProjectiveCovers
open private submodule_mem_O surjective_mem_O from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects
open private objects_closedUnderFiniteProducts from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.FiniteLength
open private cartanMap onWeight subsingleton_dual dual_shortExact from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.RestrictedDual

universe u

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g)

theorem composition_multiplicity_invariant : CompositionMultiplicityInvariantType.{u} := by
  intro g _ _ _ D mu lam s t hs₀ hs₁ ht₀ ht₁
  obtain ⟨e, he⟩ := s.jordan_holder t (hs₀.trans ht₀.symm) (hs₁.trans ht₁.symm)
  unfold compositionMultiplicity
  apply Finset.card_equiv e
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  let iso := (he i).linearEquiv
  exact ⟨fun ⟨f⟩ => ⟨iso.symm.trans f⟩, fun ⟨f⟩ => ⟨iso.trans f⟩⟩

private theorem finite_finrank_of_exact {A B C : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℂ A] [Module ℂ B] [Module ℂ C]
    [FiniteDimensional ℂ A] [FiniteDimensional ℂ C]
    (i : A →ₗ[ℂ] B) (q : B →ₗ[ℂ] C)
    (hi : Injective i) (he : Exact i q) (hq : Surjective q) :
    FiniteDimensional ℂ B ∧ Module.finrank ℂ B = Module.finrank ℂ A + Module.finrank ℂ C := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  let e := (he.splitSurjectiveEquiv hi ⟨s, hs⟩).val
  exact ⟨FiniteDimensional.of_injective e.toLinearMap e.injective,
    e.finrank_eq.trans Module.finrank_prod⟩

section Hom

omit [FiniteDimensional ℂ g]

variable {A B C T : ModuleCat.{u} (U g)}

private abbrev homEquiv (A B : ModuleCat.{u} (U g)) :
    (A ⟶ B) ≃ₗ[ℂ] (A →ₗ[U g] B) := ModuleCat.homLinearEquiv

private def postcompose (T : ModuleCat.{u} (U g)) (q : B →ₗ[U g] C) :
    (T ⟶ B) →ₗ[ℂ] (T ⟶ C) where
  toFun f := ModuleCat.ofHom (q.comp f.hom)
  map_add' f k := ModuleCat.hom_ext (by ext x; simp)
  map_smul' c f := ModuleCat.hom_ext (by
    ext x
    exact (q.restrictScalars ℂ).map_smul c (f.hom x))

private def precompose (T : ModuleCat.{u} (U g)) (i : A →ₗ[U g] B) :
    (B ⟶ T) →ₗ[ℂ] (A ⟶ T) :=
  (homEquiv A T).symm.toLinearMap.comp
    ((LinearMap.lcomp ℂ T i).comp (homEquiv B T).toLinearMap)

private theorem postcompose_exact (i : A →ₗ[U g] B) (q : B →ₗ[U g] C)
    (hi : Injective i) (he : Exact i q) :
    Exact (postcompose T i) (postcompose T q) := by
  intro f
  change postcompose T q f = 0 ↔ ∃ k, postcompose T i k = f
  constructor
  · intro hf
    let e := LinearEquiv.ofInjective i hi
    let r : T →ₗ[U g] i.range := f.hom.codRestrict i.range (fun x =>
      (he (f.hom x)).mp (congrArg (fun h : T ⟶ C => h.hom x) hf))
    refine ⟨ModuleCat.ofHom (e.symm.toLinearMap.comp r), ModuleCat.hom_ext ?_⟩
    exact LinearMap.ext fun x => congrArg Subtype.val (e.apply_symm_apply (r x))
  · rintro ⟨k, rfl⟩
    exact ModuleCat.hom_ext (LinearMap.ext fun x => he.apply_apply_eq_zero _)

private theorem precompose_exact (i : A →ₗ[U g] B) (q : B →ₗ[U g] C)
    (he : Exact i q) (hq : Surjective q) :
    Exact (precompose T q) (precompose T i) := by
  intro f
  change precompose T i f = 0 ↔ ∃ k, precompose T q k = f
  constructor
  · intro hf
    have hker : q.ker ≤ f.hom.ker := by
      intro x hx
      obtain ⟨y, rfl⟩ := (he x).mp hx
      exact congrArg (fun h : A ⟶ T => h.hom y) hf
    let k := (q.ker.liftQ f.hom hker).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap
    refine ⟨ModuleCat.ofHom k, ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
    change k (q x) = f.hom x
    simp [k]
  · rintro ⟨k, rfl⟩
    exact ModuleCat.hom_ext (LinearMap.ext fun x => by
      change k.hom (q (i x)) = 0
      rw [he.apply_apply_eq_zero, map_zero])

private theorem postcompose_finrank
    [FiniteDimensional ℂ (T ⟶ A)] [FiniteDimensional ℂ (T ⟶ C)]
    (i : A →ₗ[U g] B) (q : B →ₗ[U g] C) (hi : Injective i) (he : Exact i q)
    (hq : Surjective (postcompose T q)) :
    FiniteDimensional ℂ (T ⟶ B) ∧
      Module.finrank ℂ (T ⟶ B) = Module.finrank ℂ (T ⟶ A) + Module.finrank ℂ (T ⟶ C) :=
  finite_finrank_of_exact _ _
    (fun _ _ h => ModuleCat.hom_ext (LinearMap.ext fun x =>
      hi (congrArg (fun k : T ⟶ B => k.hom x) h)))
    (postcompose_exact i q hi he) hq

private theorem precompose_finrank
    [FiniteDimensional ℂ (C ⟶ T)] [FiniteDimensional ℂ (A ⟶ T)]
    (i : A →ₗ[U g] B) (q : B →ₗ[U g] C) (he : Exact i q) (hq : Surjective q)
    (hi : Surjective (precompose T i)) :
    FiniteDimensional ℂ (B ⟶ T) ∧
      Module.finrank ℂ (B ⟶ T) = Module.finrank ℂ (C ⟶ T) + Module.finrank ℂ (A ⟶ T) :=
  finite_finrank_of_exact _ _
    (fun f k h => ModuleCat.hom_ext (hq.injective_linearMapComp_right
      (congrArg ModuleCat.Hom.hom h : f.hom.comp q = k.hom.comp q)))
    (precompose_exact i q he hq) hi

private theorem precompose_bijective (e : A ≃ₗ[U g] B) :
    Bijective (precompose T e.toLinearMap) := by
  refine ⟨?_, ?_⟩
  · intro f k h
    exact ModuleCat.hom_ext (e.surjective.injective_linearMapComp_right
      (congrArg ModuleCat.Hom.hom h : f.hom.comp e.toLinearMap = k.hom.comp e.toLinearMap))
  · intro f
    refine ⟨ModuleCat.ofHom (f.hom.comp e.symm.toLinearMap), ModuleCat.hom_ext ?_⟩
    exact LinearMap.ext fun x => congrArg f.hom (e.symm_apply_apply x)

private theorem postcompose_bijective (e : A ≃ₗ[U g] B) :
    Bijective (postcompose T e.toLinearMap) := by
  refine ⟨?_, ?_⟩
  · intro f k h
    exact ModuleCat.hom_ext (LinearMap.ext fun x =>
      e.injective (congrArg (fun k : T ⟶ B => k.hom x) h))
  · intro f
    refine ⟨ModuleCat.ofHom (e.symm.toLinearMap.comp f.hom), ModuleCat.hom_ext ?_⟩
    exact LinearMap.ext fun x => e.apply_symm_apply (f.hom x)

end Hom

open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient (quotientHighestVector)

private theorem simple_end_finrank (mu : D.Weight) :
    FiniteDimensional ℂ (L D mu ⟶ L D mu) ∧ Module.finrank ℂ (L D mu ⟶ L D mu) = 1 := by
  obtain ⟨_, _, hv⟩ := simpleQuotient_in_O D mu
  let v : L D mu := quotientHighestVector D.cartan D.direction (character D mu)
  let q := (homEquiv (M D mu) (L D mu)).symm
    (show M D mu →ₗ[U g] L D mu from quotientMap D mu)
  let := restrictedLieRingModule (M D mu) (g := g)
  let := restrictedLieModule (M D mu) (g := g)
  let := restrictedLieRingModule (L D mu) (g := g)
  let := restrictedLieModule (L D mu) (g := g)
  let qmu := onWeight D q mu
  have hq : Surjective qmu :=
    WeightExactness.weightMap_surjective (cartanMap D q) (verma_mem_O D mu).1.2.1
      (show Surjective q from quotientMap_surjective D mu) mu
  let : FiniteDimensional ℂ (weightSpace D.cartan (M D mu) mu) :=
    (verma_mem_O D mu).2.2.2.1 mu
  let : FiniteDimensional ℂ (weightSpace D.cartan (L D mu) mu) :=
    FiniteDimensional.of_surjective qmu hq
  have hdim : Module.finrank ℂ (weightSpace D.cartan (L D mu) mu) ≤ 1 := by
    refine (LinearMap.finrank_le_finrank_of_surjective hq).trans_eq ?_
    change Module.finrank ℂ (weightSpace D.cartan (M D mu) mu) = 1
    let vM : M D mu := Specs.LieAlgebrasAndRepresentations.VermaModules.highestVector_value
      D.cartan D.direction (character D mu)
    have hline : weightSpace D.cartan (M D mu) mu = ℂ ∙ vM :=
      (verma_mem_O D mu).2.2.2.2.2
    rw [hline]
    exact finrank_span_singleton (verma_mem_O D mu).2.1
  let ev : (L D mu ⟶ L D mu) →ₗ[ℂ] weightSpace D.cartan (L D mu) mu :=
    { toFun := fun f => onWeight D f mu ⟨v, hv.2.1⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  have hi : Injective ev := by
    intro f k h
    apply ModuleCat.hom_ext
    exact LinearMap.ext_on hv.2.2.2 (Set.eqOn_singleton.mpr (congrArg Subtype.val h))
  let := FiniteDimensional.of_injective ev hi
  have hupper := (LinearMap.finrank_le_finrank_of_injective hi).trans hdim
  have hn : (𝟙 (L D mu) : L D mu ⟶ L D mu) ≠ 0 :=
    fun h => hv.1 (congrArg (fun f : L D mu ⟶ L D mu => f.hom v) h)
  let := nontrivial_of_ne _ _ hn
  have hpos := Module.finrank_pos (R := ℂ) (M := L D mu ⟶ L D mu)
  exact ⟨inferInstance, by omega⟩

private theorem hom_cover_simple (mu : D.Weight) (P : O.{u,u} D)
    (p : P.obj →ₗ[U g] L D mu) (hp : projectiveCover_value P p)
    (S : ModuleCat.{u} (U g)) [IsSimpleModule (U g) S] :
    FiniteDimensional ℂ (P.obj ⟶ S) ∧ Module.finrank ℂ (P.obj ⟶ S) =
      (if Nonempty (S ≃ₗ[U g] L D mu) then 1 else 0) := by
  obtain ⟨hL, hsimple, _⟩ := simpleQuotient_in_O D mu
  have hmax := (ProjectiveCovers.unique_maximal_submodule D P ⟨L D mu, hL⟩ p hsimple hp).2
  have factor (f : P.obj →ₗ[U g] S) (hf : f ≠ 0) : f.ker = p.ker :=
    hmax _ (LinearMap.isCoatom_ker_of_surjective (LinearMap.surjective_of_ne_zero hf))
  by_cases hIso : Nonempty (S ≃ₗ[U g] L D mu)
  · let iso := hIso.some
    let pull := precompose S p
    have hpull : Bijective pull := by
      refine ⟨?_, ?_⟩
      · intro f k h
        exact ModuleCat.hom_ext (hp.2.1.injective_linearMapComp_right
          (congrArg ModuleCat.Hom.hom h : f.hom.comp p = k.hom.comp p))
      · intro f
        have hker : p.ker ≤ f.hom.ker := by
          by_cases hz : f.hom = 0
          · simp [hz]
          · exact (factor f.hom hz).ge
        let k := (p.ker.liftQ f.hom hker).comp (p.quotKerEquivOfSurjective hp.2.1).symm.toLinearMap
        refine ⟨(homEquiv (L D mu) S).symm k, ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
        change k (p x) = f.hom x
        simp [k]
    let e := (LinearEquiv.ofBijective pull hpull).symm.trans
      (LinearEquiv.ofBijective (postcompose (L D mu) iso.toLinearMap) (postcompose_bijective iso))
    obtain ⟨hfin, hdim⟩ := simple_end_finrank D mu
    let := hfin
    exact ⟨FiniteDimensional.of_injective e.toLinearMap e.injective,
      by rw [e.finrank_eq, hdim, ite_eq_left hIso]⟩
  · have hz (f : P.obj ⟶ S) : f = 0 := by
      apply ModuleCat.hom_ext
      by_contra hf
      have hker := factor f.hom hf
      let e := Submodule.quotEquivOfEq f.hom.ker p.ker hker
      exact hIso ⟨((f.hom.quotKerEquivOfSurjective
        (LinearMap.surjective_of_ne_zero hf)).symm.trans e).trans
          (p.quotKerEquivOfSurjective hp.2.1)⟩
    let : Subsingleton (P.obj ⟶ S) := ⟨fun f k => (hz f).trans (hz k).symm⟩
    exact ⟨inferInstance, by rw [Module.finrank_zero_of_subsingleton, ite_eq_right hIso]⟩

private abbrev subobject (X : ModuleCat.{u} (U g)) (S : Submodule (U g) X) :
    ModuleCat.{u} (U g) := ModuleCat.of (U g) S

private theorem subobject_mem_O (X : O.{u,u} D) (S : Submodule (U g) X.obj) :
    objects_value D (subobject X.obj S) := by
  let : IsNoetherian (U g) X.obj :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (categoryO_finiteLength D X)).1
  exact submodule_mem_O D X.obj X.property S (IsNoetherian.noetherian S)

private abbrev layerObject {X : ModuleCat.{u} (U g)} (A B : Submodule (U g) X) :
    ModuleCat.{u} (U g) := ModuleCat.of (U g) (Layer A B)

private abbrev layerMap {X : ModuleCat.{u} (U g)} (A B : Submodule (U g) X) :
    subobject X B →ₗ[U g] layerObject A B := (A.comap B.subtype).mkQ

omit [FiniteDimensional ℂ g] in
private theorem layer_exact {X : ModuleCat.{u} (U g)} {A B : Submodule (U g) X} (h : A ≤ B) :
    Exact (Submodule.inclusion h) (layerMap A B) := by
  rw [LinearMap.exact_iff, Submodule.range_inclusion, Submodule.ker_mkQ]

private theorem layer_mem_O (X : O.{u,u} D) (A B : Submodule (U g) X.obj) :
    objects_value D (layerObject A B) :=
  surjective_mem_O D (subobject_mem_O D X B) (layerMap A B) (Submodule.mkQ_surjective _)

private def dualEquiv {A B : ModuleCat.{u} (U g)} (e : A ≃ₗ[U g] B) :
    dualModule D B ≃ₗ[U g] dualModule D A :=
  ((Specs.RepTheorySurvey.CategoryO.RestrictedDual.ambientDualFunctor D).mapIso
    e.toModuleIso.op).toLinearEquiv

private theorem simple_dual_equiv (S : O.{u,u} D) [IsSimpleModule (U g) S.obj] :
    Nonempty (dualModule D S.obj ≃ₗ[U g] S.obj) := by
  have hs := (simple_iff_isSimpleModule D S).mpr inferInstance
  obtain ⟨eta, ⟨e⟩, _⟩ := (simpleClassification D S).mp hs
  obtain ⟨l⟩ := dual_simple D eta
  exact ⟨((dualEquiv D e.symm).trans l).trans e.symm⟩

private theorem sum_successive_increments {n : ℕ} (f : Fin (n + 1) → ℕ) (a : Fin n → ℕ)
    (h : ∀ i, f i.succ = f i.castSucc + a i) :
    f (Fin.last n) = f 0 + ∑ i, a i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, ← Nat.add_assoc]
    have h' := ih (fun j => f j.castSucc) (fun j => a j.castSucc) (fun j => h j.castSucc)
    exact (h (Fin.last n)).trans (congrArg (· + a (Fin.last n)) h')

private theorem hom_to_dual_series (mu : D.Weight) (P : O.{u,u} D)
    (p : P.obj →ₗ[U g] L D mu) (hp : projectiveCover_value P p)
    (X : O.{u,u} D) (s : CompositionSeries (Submodule (U g) X.obj))
    (hs₀ : s.head = ⊥) (hs₁ : s.last = ⊤) :
    FiniteDimensional ℂ (P.obj ⟶ dualModule D X.obj) ∧
    Module.finrank ℂ (P.obj ⟶ dualModule D X.obj) = compositionMultiplicity D mu s := by
  let A (j : Fin (s.length + 1)) : ModuleCat.{u} (U g) := subobject X.obj (s j)
  let Q (j : Fin s.length) : ModuleCat.{u} (U g) := layerObject (s j.castSucc) (s j.succ)
  let a (j : Fin s.length) : ℕ := if Nonempty (Q j ≃ₗ[U g] L D mu) then 1 else 0
  have hA (j) : objects_value D (A j) := subobject_mem_O D X (s j)
  have hQ (j) : objects_value D (Q j) := layer_mem_O D X (s j.castSucc) (s j.succ)
  have hzero : FiniteDimensional ℂ (P.obj ⟶ dualModule D (A 0)) ∧
      Module.finrank ℂ (P.obj ⟶ dualModule D (A 0)) = 0 := by
    have h : Subsingleton (A 0) := by
      change Subsingleton s.head
      rw [hs₀]
      infer_instance
    let := h
    let := subsingleton_dual D (A 0)
    let : Subsingleton (P.obj ⟶ dualModule D (A 0)) :=
      ⟨(ModuleCat.isZero_of_subsingleton (dualModule D (A 0))).eq_of_tgt⟩
    exact ⟨inferInstance, Module.finrank_zero_of_subsingleton⟩
  have hstep (j : Fin s.length) (hfin : FiniteDimensional ℂ (P.obj ⟶ dualModule D (A j.castSucc))) :
      FiniteDimensional ℂ (P.obj ⟶ dualModule D (A j.succ)) ∧
      Module.finrank ℂ (P.obj ⟶ dualModule D (A j.succ)) =
        Module.finrank ℂ (P.obj ⟶ dualModule D (A j.castSucc)) + a j := by
    let := hfin
    let h : s j.castSucc ⋖ s j.succ := s.step j
    let : IsSimpleModule (U g) (Q j) := (covBy_iff_quot_is_simple h.le).mp h
    let e := (simple_dual_equiv D ⟨Q j, hQ j⟩).some
    let : IsSimpleModule (U g) (dualModule D (Q j)) := IsSimpleModule.congr e
    have heq : Nonempty (dualModule D (Q j) ≃ₗ[U g] L D mu) ↔
        Nonempty (Q j ≃ₗ[U g] L D mu) :=
      ⟨fun ⟨k⟩ => ⟨e.symm.trans k⟩, fun ⟨k⟩ => ⟨e.trans k⟩⟩
    obtain ⟨hfinQ, hdim⟩ := hom_cover_simple D mu P p hp (dualModule D (Q j))
    let := hfinQ
    let i : A j.castSucc ⟶ A j.succ := ModuleCat.ofHom (Submodule.inclusion h.le)
    let q : A j.succ ⟶ Q j := ModuleCat.ofHom (layerMap _ _)
    have hd := dual_shortExact D i q (hA _).2.1 (hA _).2.1 (hQ _).2.1
      (Submodule.inclusion_injective h.le) (layer_exact h.le) (Submodule.mkQ_surjective _)
    let i' := (dualMap D q).hom
    let q' := (dualMap D i).hom
    have hsurj : Surjective (postcompose P.obj q') := by
      intro f
      let X' : O.{u,u} D := ⟨dualModule D (A j.succ), dual_mem_O D ⟨_, hA _⟩⟩
      let Y' : O.{u,u} D := ⟨dualModule D (A j.castSucc), dual_mem_O D ⟨_, hA _⟩⟩
      obtain ⟨k, hk⟩ := projectiveLift (X := X') (Y := Y') hp.1 f.hom q' hd.2.2
      exact ⟨ModuleCat.ofHom k, ModuleCat.hom_ext hk⟩
    obtain ⟨hfinB, hdimB⟩ := postcompose_finrank i' q' hd.1 hd.2.1 hsurj
    refine ⟨hfinB, ?_⟩
    rw [hdimB, hdim, add_comm]
    simp only [a, heq]
  have hfin (j : Fin (s.length + 1)) : FiniteDimensional ℂ (P.obj ⟶ dualModule D (A j)) := by
    induction j using Fin.induction with
    | zero => exact hzero.1
    | succ j ih => exact (hstep j ih).1
  have hsum : Module.finrank ℂ (P.obj ⟶ dualModule D (A (Fin.last s.length))) =
      compositionMultiplicity D mu s := by
    rw [sum_successive_increments (fun j => Module.finrank ℂ (P.obj ⟶ dualModule D (A j))) a
      (fun j => (hstep j (hfin _)).2)]
    rw [hzero.2, zero_add]
    simp only [compositionMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
    rfl
  let e : A (Fin.last s.length) ≃ₗ[U g] X.obj := by
    change s.last ≃ₗ[U g] X.obj
    rw [hs₁]
    exact Submodule.topEquiv
  let d := dualEquiv D e
  let E := LinearEquiv.ofBijective (postcompose P.obj d.toLinearMap) (postcompose_bijective d)
  let := hfin (Fin.last s.length)
  exact ⟨FiniteDimensional.of_injective E.toLinearMap E.injective, E.finrank_eq.trans hsum⟩

private theorem binary_product_mem_O (A B : O.{u,u} D) :
    objects_value D (ModuleCat.of (U g) (A.obj × B.obj)) := by
  let : (objects_value.{u,u} D).IsClosedUnderFiniteProducts := objects_closedUnderFiniteProducts D
  exact (objects_value D).prop_of_isLimit_binaryFan
    (ModuleCat.binaryProductLimitCone A.obj B.obj).isLimit A.property B.property

/-- A map from a submodule extends across a Verma quotient by splitting its pushout. -/
private theorem extends_across_verma (nu lam : D.Weight) (B : O.{u,u} D)
    {A : ModuleCat.{u} (U g)} (i : A →ₗ[U g] B.obj) (q : B.obj →ₗ[U g] M D nu)
    (hi : Injective i) (he : Exact i q) (hq : Surjective q) :
    Surjective (precompose (costandard D lam) i) := by
  intro fCat
  let N := costandard D lam
  let f := fCat.hom
  let graph : A →ₗ[U g] B.obj × N := i.prod (-f)
  let S := graph.range
  let W : ModuleCat.{u} (U g) := ModuleCat.of (U g) ((B.obj × N) ⧸ S)
  let hW : objects_value D W := surjective_mem_O D
    (binary_product_mem_O D B ⟨N, RestrictedDual.costandard_mem_O D lam⟩)
    S.mkQ S.mkQ_surjective
  let j : N →ₗ[U g] W := S.mkQ.comp (LinearMap.inr (U g) B.obj N)
  let b : B.obj →ₗ[U g] W := S.mkQ.comp (LinearMap.inl (U g) B.obj N)
  let k₀ : B.obj × N →ₗ[U g] M D nu := q.comp (LinearMap.fst (U g) B.obj N)
  let k : W →ₗ[U g] M D nu := S.liftQ k₀ (by
    rintro z ⟨a, rfl⟩
    exact he.apply_apply_eq_zero a)
  have hj : Injective j := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    change S.mkQ (0, x) = 0 at hx
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero S).mp hx
    have ha₀ : i a = 0 := congrArg Prod.fst ha
    have ha₁ : -f a = x := congrArg Prod.snd ha
    have : a = 0 := hi (ha₀.trans i.map_zero.symm)
    change x = 0
    simpa [this] using ha₁.symm
  have hex : Exact j k := by
    intro z
    obtain ⟨⟨y, n⟩, rfl⟩ := S.mkQ_surjective z
    change q y = 0 ↔ ∃ x, S.mkQ (0, x) = S.mkQ (y, n)
    constructor
    · intro h
      obtain ⟨a, rfl⟩ := (he y).mp h
      refine ⟨n + f a, (Submodule.Quotient.eq S).mpr ⟨-a, ?_⟩⟩
      change (i (-a), -f (-a)) = (0, n + f a) - (i a, n)
      simp
    · rintro ⟨x, hx⟩
      have h := congrArg k hx
      change q 0 = q y at h
      simpa using h.symm
  have hk : Surjective k := by
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨S.mkQ (x, 0), rfl⟩
  have hcomm (a : A) : b (i a) = j (f a) := by
    change S.mkQ (i a, 0) = S.mkQ (0, f a)
    refine (Submodule.Quotient.eq S).mpr ⟨a, ?_⟩
    change (i a, -f a) = (i a, (0 : N)) - (0, f a)
    simp
  obtain ⟨s, hs⟩ := DualVermaExtensions.extension_splits D nu lam ⟨W, hW⟩ j k hj hex hk
  let e := hex.splitSurjectiveEquiv hj ⟨s, hs⟩
  let r : W →ₗ[U g] N := (LinearMap.fst (U g) N (M D nu)).comp e.val.toLinearMap
  have hr (x : N) : r (j x) = x := by
    change (e.val (j x)).1 = x
    have h : j x = e.val.symm (x, 0) := LinearMap.congr_fun e.property.1 x
    exact (congrArg (fun w => (e.val w).1) h).trans
      (congrArg Prod.fst (e.val.apply_symm_apply (x, 0)))
  refine ⟨ModuleCat.ofHom (r.comp b), ModuleCat.hom_ext (LinearMap.ext fun a => ?_)⟩
  change r (b (i a)) = f a
  rw [hcomm, hr]

private theorem verma_equiv_iff (nu lam : D.Weight) :
    Nonempty (M D nu ≃ₗ[U g] M D lam) ↔ nu = lam := by
  constructor
  · rintro ⟨iso⟩
    let e := LinearEquiv.ofBijective (precompose (costandard D lam) iso.toLinearMap)
      (precompose_bijective iso)
    have h := e.finrank_eq
    rw [(DualVermaExtensions.hom_dimension D lam lam).2,
      (DualVermaExtensions.hom_dimension D nu lam).2, ite_eq_left rfl] at h
    by_contra hn
    rw [ite_eq_right hn] at h
    exact Nat.one_ne_zero h
  · rintro rfl
    exact ⟨LinearEquiv.refl _ _⟩

private theorem hom_from_verma_flag (lam : D.Weight) (X : O.{u,u} D)
    {weights : List D.Weight} {A B : Submodule (U g) X.obj}
    (F : VermaFlag D weights A B)
    (hA : FiniteDimensional ℂ (subobject X.obj A ⟶ costandard D lam)) :
    FiniteDimensional ℂ (subobject X.obj B ⟶ costandard D lam) ∧
    Module.finrank ℂ (subobject X.obj B ⟶ costandard D lam) =
      Module.finrank ℂ (subobject X.obj A ⟶ costandard D lam) +
        vermaMultiplicity D lam weights := by
  induction F with
  | nil A => exact ⟨hA, by simp [vermaMultiplicity]⟩
  | @cons nu rest A B C hAB hIso F ih =>
    let := hA
    let i : subobject X.obj A →ₗ[U g] subobject X.obj B := Submodule.inclusion hAB
    let e := hIso.some
    let q : subobject X.obj B →ₗ[U g] M D nu := e.toLinearMap.comp (layerMap A B)
    have hq : Surjective q := e.surjective.comp (Submodule.mkQ_surjective _)
    have he : Exact i q := by
      intro x
      change e (layerMap A B x) = 0 ↔ _
      rw [← e.map_zero, e.injective.eq_iff]
      exact layer_exact hAB x
    have hsurj := extends_across_verma D nu lam ⟨subobject X.obj B, subobject_mem_O D X B⟩ i q
      (Submodule.inclusion_injective _) he hq
    obtain ⟨hfinVerma, hdimVerma⟩ := DualVermaExtensions.hom_dimension D nu lam
    let := hfinVerma
    obtain ⟨hfinB, hdimB⟩ := precompose_finrank i q he hq hsurj
    obtain ⟨hfinC, hdimC⟩ := ih hfinB
    refine ⟨hfinC, ?_⟩
    rw [hdimC, hdimB, hdimVerma]
    have hcount : vermaMultiplicity D lam (nu :: rest) =
        vermaMultiplicity D lam rest + (if nu = lam then 1 else 0) := by
      simp [vermaMultiplicity, List.countP_cons, verma_equiv_iff D nu lam]
    rw [hcount]
    ac_rfl

theorem bgg_reciprocity : ReciprocityType.{u} := by
  intro g _ _ _ D mu lam P p hp
  let X : O.{u,u} D := ⟨M D lam, (verma_mem_O D lam).1⟩
  obtain ⟨s, hs₀, hs₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp (categoryO_finiteLength D X)
  refine ⟨(hom_to_dual_series D mu P p hp X s hs₀ hs₁).1, ?_, ?_⟩
  · intro weights F
    let A : ModuleCat.{u} (U g) := subobject P.obj ⊥
    let : Subsingleton (A ⟶ costandard D lam) := ⟨(ModuleCat.isZero_of_subsingleton A).eq_of_src⟩
    obtain ⟨_, hf⟩ := hom_from_verma_flag D lam P F (inferInstanceAs (FiniteDimensional ℂ
      (A ⟶ costandard D lam)))
    let e : subobject P.obj ⊤ ≃ₗ[U g] P.obj := Submodule.topEquiv
    let E := LinearEquiv.ofBijective (precompose (costandard D lam) e.toLinearMap)
      (precompose_bijective e)
    rw [E.finrank_eq, hf, Module.finrank_zero_of_subsingleton, zero_add]
  · intro t ht₀ ht₁
    exact (hom_to_dual_series D mu P p hp X t ht₀ ht₁).2.symm

end RepTheorySurvey.CategoryO.BGGReciprocity
