import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSums
import Mathlib.Algebra.Module.Shrink

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum

universe u v w j t

namespace DerivedFormalization.DG.IndexedSums

open Specs.DerivedFormalization.DG.IndexedSemiFree (StrictSum SumTerm summand)
open Specs.DerivedFormalization.DG.IndexedSums
open CoefficientLift (liftCategory liftModule liftMap)

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {I : Type j} {F : I → RightDGModuleModel A}
variable {S T N : RightDGModuleModel A}

private def rawStep (F : I → RightDGModuleModel A) (a : A.Obj) (n : ℤ) :
    SumTerm F a n →ₗ[k] SumTerm F a (n+1) :=
  DirectSum.lmap fun i => ((F i).complex a).d n (n+1) |>.hom

private def rawAct (F : I → RightDGModuleModel A) {a b : A.Obj} (m n q : ℤ)
    (h : m+n = q) :
    SumTerm F b m →ₗ[k] (A.hom a b).X n →ₗ[k] SumTerm F a q :=
  LinearMap.flip
    { toFun := fun f => DirectSum.lmap fun i => ((F i).act m n q h).flip f
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro x
        apply DFinsupp.ext
        intro i
        exact map_add ((F i).act m n q h (x i)) f g
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro x
        apply DFinsupp.ext
        intro i
        exact map_smul ((F i).act m n q h (x i)) c f }

section Construction

variable (F) (hF : TermsSmall F)

private def term (a : A.Obj) (n : ℤ) : ModuleCat.{v} k :=
  letI := hF a n
  ModuleCat.of k (Shrink.{v} (SumTerm F a n))

private def coordinates (a : A.Obj) (n : ℤ) : term F hF a n ≃ₗ[k] SumTerm F a n :=
  letI := hF a n
  Shrink.linearEquiv k _

private def step (a : A.Obj) (n : ℤ) : term F hF a n ⟶ term F hF a (n+1) :=
  ModuleCat.ofHom <| (coordinates F hF a (n+1)).symm.toLinearMap.comp
    ((rawStep F a n).comp (coordinates F hF a n).toLinearMap)

@[simp] private theorem coordinates_step (a : A.Obj) (n : ℤ) (x : term F hF a n) :
    coordinates F hF a (n+1) (step F hF a n x) = rawStep F a n (coordinates F hF a n x) :=
  (coordinates F hF a (n+1)).apply_symm_apply _

@[reducible] private def complex (a : A.Obj) : ModuleCochain.{u,v} k :=
  CochainComplex.of (term F hF a) (step F hF a) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (coordinates F hF a (n+1+1)).injective
    change coordinates F hF a (n+1+1) (step F hF a (n+1) (step F hF a n x)) =
      coordinates F hF a (n+1+1) 0
    rw [coordinates_step, coordinates_step, map_zero]
    apply DFinsupp.ext
    intro i
    change ((F i).complex a).d (n+1) (n+1+1)
      (((F i).complex a).d n (n+1) (coordinates F hF a n x i)) = 0
    rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
    rfl)

@[simp] private theorem coordinates_d_eq (a : A.Obj) (n : ℤ) (x : term F hF a n) :
    coordinates F hF a (n+1) ((complex F hF a).d n (n+1) x) =
      rawStep F a n (coordinates F hF a n x) := by
  change coordinates F hF a (n+1) (CochainComplex.of.d _ (step F hF a) n (n+1) x) = _
  rw [CochainComplex.of_d, coordinates_step]

private def action {a b : A.Obj} (m n q : ℤ) (h : m+n = q) :
    term F hF b m →ₗ[k] (A.hom a b).X n →ₗ[k] term F hF a q :=
  ((rawAct F m n q h).comp (coordinates F hF b m).toLinearMap).compr₂
    (coordinates F hF a q).symm.toLinearMap

@[simp] private theorem coordinates_action {a b : A.Obj} (m n q : ℤ) (h : m+n = q)
    (x : term F hF b m) (f : (A.hom a b).X n) :
    coordinates F hF a q (action F hF m n q h x f) = rawAct F m n q h (coordinates F hF b m x) f :=
  (coordinates F hF a q).apply_symm_apply _

/-- The degreewise sum transported to small coefficient carriers. -/
def sum : RightDGModuleModel A where
  complex := complex F hF
  act := action F hF
  act_id a n x := by
    apply (coordinates F hF a n).injective
    rw [coordinates_action]
    exact DFinsupp.ext fun i => (F i).act_id a n (coordinates F hF a n x i)
  act_assoc {a b c} m n q x f g := by
    apply (coordinates F hF a (m+n+q)).injective
    simp only [coordinates_action]
    exact DFinsupp.ext fun i => (F i).act_assoc m n q (coordinates F hF c m x i) f g
  leibniz {a b} m n q h x f := by
    apply (coordinates F hF a (q+1)).injective
    simp only [CochainComplex.of_d, coordinates_step, map_add, Units.smul_def, map_zsmul,
      coordinates_action]
    exact DFinsupp.ext fun i => (F i).leibniz m n q h (coordinates F hF b m x i) f

private def inclusion (i : I) : F i ⟶ sum F hF where
  app a := CochainComplex.ofHom
    (fun n => ModuleCat.ofHom ((coordinates F hF a n).symm.toLinearMap.comp (summand F a n i)))
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (coordinates F hF a (n+1)).injective
      change coordinates F hF a (n+1) ((complex F hF a).d n (n+1)
        ((coordinates F hF a n).symm (summand F a n i x))) =
        coordinates F hF a (n+1) ((coordinates F hF a (n+1)).symm
          (summand F a (n+1) i (((F i).complex a).d n (n+1) x)))
      rw [coordinates_d_eq, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      classical
      exact DirectSum.lmap_lof (fun s => ((F s).complex a).d n (n+1) |>.hom) i x)
  comm_act {a b} m n q h x f := by
    apply (coordinates F hF a q).injective
    change coordinates F hF a q ((coordinates F hF a q).symm
        (summand F a q i ((F i).act m n q h x f))) =
      coordinates F hF a q (action F hF m n q h
        ((coordinates F hF b m).symm (summand F b m i x)) f)
    rw [coordinates_action, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    classical
    exact (DirectSum.lmap_lof (fun s => ((F s).act m n q h).flip f) i x).symm

/-- Coordinates of the constructed sum, together with the strict summand maps. -/
def sumRealization : StrictSum F (sum F hF) where
  inclusion := inclusion F hF
  coordinates := coordinates F hF
  coordinate_inclusion _ a n _ := (coordinates F hF a n).apply_symm_apply _
  coordinate_d a n x i := congrArg (fun y : SumTerm F a (n+1) => y i) (coordinates_d_eq F hF a n x)
  coordinate_act {a _b} m n q h x f i :=
    congrArg (fun y : SumTerm F a q => y i) (coordinates_action F hF m n q h x f)

end Construction

theorem realization : Realization.{u,v,w,j} :=
  fun F hF => ⟨sum F hF, ⟨sumRealization F hF⟩⟩

private def rawDesc (g : ∀ i, F i ⟶ N) (a : A.Obj) (n : ℤ) :
    SumTerm F a n →ₗ[k] (N.complex a).X n := by
  classical
  exact DirectSum.toModule k I _ (fun i => ((g i).app a |>.f n).hom)

@[simp] private theorem rawDesc_summand (g : ∀ i, F i ⟶ N)
    (a : A.Obj) (n : ℤ) (i : I) (x : ((F i).complex a).X n) :
    rawDesc g a n (summand F a n i x) = ((g i).app a).f n x := by
  classical
  exact DirectSum.toModule_lof (R := k) (φ := fun i => ((g i).app a |>.f n).hom) i x

variable (s : StrictSum F S)

private theorem term_hom_ext {L : Type*} [AddCommMonoid L] [Module k L]
    (a : A.Obj) (n : ℤ) {f g : (S.complex a).X n →ₗ[k] L}
    (h : ∀ i x, f (((s.inclusion i).app a).f n x) = g (((s.inclusion i).app a).f n x)) :
    f = g := by
  classical
  let e := s.coordinates a n
  have hcomp : f.comp e.symm.toLinearMap = g.comp e.symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change f (e.symm (summand F a n i x)) = g (e.symm (summand F a n i x))
    rw [← s.coordinate_inclusion i a n x]
    simpa only [e, LinearEquiv.symm_apply_apply] using h i x
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    using LinearMap.congr_fun hcomp (e x)

private def descTerm (g : ∀ i, F i ⟶ N) (a : A.Obj) (n : ℤ) :
    (S.complex a).X n →ₗ[k] (N.complex a).X n :=
  (rawDesc g a n).comp (s.coordinates a n).toLinearMap

@[simp] private theorem descTerm_inclusion (g : ∀ i, F i ⟶ N)
    (a : A.Obj) (n : ℤ) (i : I) (x : ((F i).complex a).X n) :
    descTerm s g a n (((s.inclusion i).app a).f n x) = ((g i).app a).f n x := by
  change rawDesc g a n (s.coordinates a n (((s.inclusion i).app a).f n x)) = _
  rw [s.coordinate_inclusion, rawDesc_summand]

/-- A strict map from a realized sum is determined by its summand maps. -/
theorem hom_ext {f g : S ⟶ N}
    (h : ∀ i, s.inclusion i ≫ f = s.inclusion i ≫ g) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply term_hom_ext s a n
  intro i x
  exact congrArg (fun p : F i ⟶ N => (p.app a).f n x) (h i)

/-- Extend a family of strict maps by summing their values on the finite support. -/
def desc (g : ∀ i, F i ⟶ N) : S ⟶ N where
  app a := CochainComplex.ofHom (fun n => ModuleCat.ofHom (descTerm s g a n)) (by
    intro n
    apply ModuleCat.hom_ext
    apply term_hom_ext s a n
    intro i x
    change (N.complex a).d n (n+1) (descTerm s g a n (((s.inclusion i).app a).f n x)) =
      descTerm s g a (n+1) ((S.complex a).d n (n+1) (((s.inclusion i).app a).f n x))
    have h := CategoryTheory.congr_fun ((s.inclusion i).app a |>.comm n (n+1)) x
    change (S.complex a).d n (n+1) (((s.inclusion i).app a).f n x) =
      ((s.inclusion i).app a).f (n+1) (((F i).complex a).d n (n+1) x) at h
    rw [descTerm_inclusion, h, descTerm_inclusion]
    exact CategoryTheory.congr_fun ((g i).app a |>.comm n (n+1)) x)
  comm_act {a b} m n q h x f := by
    have hlin :
        (descTerm s g a q).comp ((S.act m n q h).flip f) =
          ((N.act m n q h).flip f).comp (descTerm s g b m) := by
      apply term_hom_ext s b m
      intro i y
      change descTerm s g a q (S.act m n q h (((s.inclusion i).app b).f m y) f) =
        N.act m n q h (descTerm s g b m (((s.inclusion i).app b).f m y)) f
      rw [← (s.inclusion i).comm_act, descTerm_inclusion, descTerm_inclusion]
      exact (g i).comm_act m n q h y f
    exact LinearMap.congr_fun hlin x

@[reassoc (attr := simp)]
theorem inclusion_desc (g : ∀ i, F i ⟶ N) (i : I) :
    s.inclusion i ≫ desc s g = g i := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact descTerm_inclusion s g a n i x

/-- The realized sum and its inclusions form a strict coproduct cofan. -/
def isColimit : IsColimit (Cofan.mk S s.inclusion) :=
  Cofan.IsColimit.mk _ (fun c => desc s c.inj)
    (fun c i => inclusion_desc s c.inj i)
    (fun c _ h => hom_ext s fun i => (h i).trans (inclusion_desc s c.inj i).symm)

theorem universalProperty : UniversalProperty.{u,v,w,j} := fun s => ⟨isColimit s⟩

private def select (i t : I) : F t ⟶ F i := by
  classical
  exact if h : t = i then eqToHom (congrArg F h) else 0

/-- The coordinate projections provided by any strict coproduct distinguish the
elements of the raw direct sum. -/
theorem termsSmallOfIsColimit {c : Cofan F} (hc : IsColimit c) : TermsSmall F := by
  intro a n
  classical
  let d := rawDesc c.inj a n
  apply small_of_injective (f := d)
  intro x y h
  apply DFinsupp.ext
  intro i
  let p : c.pt ⟶ F i := hc.desc (Cofan.mk (F i) (select i))
  have hp (t : I) : c.inj t ≫ p = select i t := hc.fac _ ⟨t⟩
  have hproj : ((p.app a).f n).hom.comp d =
      DirectSum.component k I (fun t => ((F t).complex a).X n) i := by
    apply DirectSum.linearMap_ext
    intro t
    apply LinearMap.ext
    intro z
    change (p.app a).f n (d (summand F a n t z)) =
      DirectSum.component k I (fun t => ((F t).complex a).X n) i (summand F a n t z)
    change (p.app a).f n (rawDesc c.inj a n (summand F a n t z)) = _
    rw [rawDesc_summand]
    change ((c.inj t ≫ p).app a).f n z = _
    rw [hp]
    by_cases ht : t = i
    · subst t
      simp only [select, dite_eq_left rfl, eqToHom_refl, RightDGModuleModel.id_app,
        HomologicalComplex.id_f, ModuleCat.id_apply, summand, DirectSum.component.lof_self]
    · rw [select, dite_eq_right ht, RightDGModuleModel.zero_app, HomologicalComplex.zero_f]
      change 0 = _
      rw [summand, DirectSum.component.of, dite_eq_right ht]
  exact (LinearMap.congr_fun hproj x).symm.trans
    ((congrArg ((p.app a).f n) h).trans (LinearMap.congr_fun hproj y))

/-- Transport sum coordinates back to the vertex of an arbitrary colimit cofan. -/
def strictSumOfIsColimit {c : Cofan F} (hc : IsColimit c) : StrictSum F c.pt := by
  let hF := termsSmallOfIsColimit hc
  let s := sumRealization F hF
  let e := hc.coconePointUniqueUpToIso (isColimit s)
  have he (i : I) : c.inj i ≫ e.hom = s.inclusion i :=
    hc.fac _ ⟨i⟩
  let coords (a : A.Obj) (n : ℤ) : (c.pt.complex a).X n ≃ₗ[k] SumTerm F a n :=
    (CategoryTheory.Iso.toLinearEquiv ((RightDGModuleModel.degree a n).mapIso e)).trans
      (s.coordinates a n)
  refine ⟨c.inj, coords, ?_, ?_, ?_⟩
  · intro i a n x
    change s.coordinates a n (((c.inj i ≫ e.hom).app a).f n x) = _
    rw [he, s.coordinate_inclusion]
  · intro a n x i
    change s.coordinates a (n+1) ((e.hom.app a).f (n+1) ((c.pt.complex a).d n (n+1) x)) i = _
    have h := CategoryTheory.congr_fun ((e.hom.app a).comm n (n+1)) x
    change ((sum F hF).complex a).d n (n+1) ((e.hom.app a).f n x) =
      (e.hom.app a).f (n+1) ((c.pt.complex a).d n (n+1) x) at h
    rw [← h, s.coordinate_d]
    rfl
  · intro a b m n q h x f i
    change s.coordinates a q ((e.hom.app a).f q (c.pt.act m n q h x f)) i = _
    rw [e.hom.comm_act]
    exact s.coordinate_act m n q h ((e.hom.app b).f m x) f i

theorem existingCoproduct : ExistingCoproduct.{u,v,w,j} := fun _ hc =>
  ⟨termsSmallOfIsColimit hc, strictSumOfIsColimit hc, fun _ => rfl⟩

theorem hasCoproduct_iff_termsSmall : ExistenceCriterion.{u,v,w,j} := by
  intro k _ A I F
  constructor
  · intro h
    let c := getColimitCocone (Discrete.functor F)
    exact termsSmallOfIsColimit c.isColimit
  · intro h
    let s := sumRealization F h
    exact HasColimit.mk ⟨Cofan.mk _ s.inclusion, isColimit s⟩

variable (r : StrictSum F T)

/-- Compare two realizations by the unique strict isomorphism of coproducts. -/
def comparisonIso : S ≅ T :=
  (isColimit s).coconePointUniqueUpToIso (isColimit r)

@[reassoc (attr := simp)]
theorem inclusion_comparisonIso (i : I) :
    s.inclusion i ≫ (comparisonIso s r).hom = r.inclusion i :=
  (isColimit s).fac _ ⟨i⟩

theorem comparisonIso_coordinates (a : A.Obj) (n : ℤ) (x : (S.complex a).X n) :
    r.coordinates a n (((comparisonIso s r).hom.app a).f n x) = s.coordinates a n x := by
  have h : (r.coordinates a n).toLinearMap.comp (((comparisonIso s r).hom.app a).f n).hom =
      (s.coordinates a n).toLinearMap := by
    apply term_hom_ext s a n
    intro i y
    change r.coordinates a n (((s.inclusion i ≫ (comparisonIso s r).hom).app a).f n y) =
      s.coordinates a n (((s.inclusion i).app a).f n y)
    rw [inclusion_comparisonIso, r.coordinate_inclusion, s.coordinate_inclusion]
  exact LinearMap.congr_fun h x

theorem strictComparison : StrictComparison.{u,v,w,j} :=
  fun s r => ⟨comparisonIso s r, inclusion_comparisonIso s r, comparisonIso_coordinates s r⟩

theorem termsSmallOfIsEmpty [IsEmpty I] (F : I → RightDGModuleModel A) : TermsSmall F := by
  intro a n
  apply small_of_injective (f := fun _ : SumTerm F a n => PUnit.unit.{v+1})
  intro x y _
  exact DFinsupp.ext fun i => isEmptyElim i

theorem emptyFamily : EmptyFamily.{u,v,w,j} := by
  intro k _ A I _ F
  let hF := termsSmallOfIsEmpty F
  let s := sumRealization F hF
  refine ⟨sum F hF, s, ⟨isColimit s⟩, fun a n x => ?_⟩
  exact (s.coordinates a n).injective (DFinsupp.ext fun i => isEmptyElim i)

/-- The existing sum already has the required coordinates for a small index. -/
def nativeSum {J : Type v} (F : J → RightDGModuleModel A) :
    StrictSum F (RightDGModule.directSum F) where
  inclusion := RightDGModule.sumInclusion F
  coordinates _ _ := LinearEquiv.refl k _
  coordinate_inclusion _ _ _ _ := rfl
  coordinate_d a n x i := Specs.DerivedFormalization.DG.SemiFree.directSum_d F a n x i
  coordinate_act _ _ _ _ _ _ _ := rfl

theorem smallIndex : SmallIndex.{u,v,w} := fun F =>
  ⟨nativeSum F, fun _ => rfl, fun _ _ _ => rfl, ⟨RightDGModule.directSumIsColimit F⟩⟩

/-- The base-ring-linear coefficient lift on each term gives a linear
equivalence of the raw sums with the same finite support index. -/
def liftTerm (F : I → RightDGModuleModel A) (a : A.Obj) (n : ℤ) :
    SumTerm F a n ≃ₗ[k] SumTerm (liftedFamily.{u,v,w,j,t} F) a n :=
  DFinsupp.mapRange.linearEquiv fun i =>
    (ULift.moduleEquiv : ((liftModule.{u,v,w,t} (F i)).complex a).X n ≃ₗ[k]
      ((F i).complex a).X n).symm

@[simp]
theorem liftTerm_apply (x : SumTerm F a n) (i : I) :
    (liftTerm.{u,v,w,j,t} F a n x i).down = x i := rfl

private theorem liftTerm_summand (i : I) (a : A.Obj) (n : ℤ) (x : ((F i).complex a).X n) :
    liftTerm.{u,v,w,j,t} F a n (summand F a n i x) =
      summand (liftedFamily.{u,v,w,j,t} F) a n i (ULift.up x) := by
  classical
  exact DirectSum.lmap_lof (fun i => (ULift.moduleEquiv.symm :
    ((F i).complex a).X n ≃ₗ[k] ((liftModule.{u,v,w,t} (F i)).complex a).X n).toLinearMap) i x

/-- Upgrade any realized sum to the indicated coefficient universe without
altering the underlying finitely supported family of entries. -/
def liftStrictSum : StrictSum (liftedFamily.{u,v,w,j,t} F) (liftModule.{u,v,w,t} S) where
  inclusion i := liftMap.{u,v,w,t} (s.inclusion i)
  coordinates a n :=
    ULift.moduleEquiv.trans ((s.coordinates a n).trans (liftTerm.{u,v,w,j,t} F a n))
  coordinate_inclusion i a n x := by
    change liftTerm.{u,v,w,j,t} F a n (s.coordinates a n (((s.inclusion i).app a).f n x.down)) = _
    rw [s.coordinate_inclusion, liftTerm_summand]
    rfl
  coordinate_d a n x i := by
    apply ULift.ext
    exact s.coordinate_d a n x.down i
  coordinate_act m n q h x f i := by
    apply ULift.ext
    exact s.coordinate_act m n q h x.down f.down i

@[simp]
theorem liftStrictSum_coordinates (a : A.Obj) (n : ℤ)
    (x : ((liftModule.{u,v,w,t} S).complex a).X n) (i : I) :
    ((liftStrictSum.{u,v,w,j,t} s).coordinates a n x i).down = s.coordinates a n x.down i :=
  rfl

/-- At the coefficient universe containing the index, all lifted terms fit. -/
theorem liftedTermsSmall (F : I → RightDGModuleModel A) :
    TermsSmall (liftedFamily.{u,v,w,j,j} F) :=
  fun _ _ => small_self _

/-- The canonical sum at the coefficient universe containing the index. -/
def liftedSum (F : I → RightDGModuleModel A) :
    RightDGModuleModel (liftCategory.{u,v,w,j} A) :=
  sum (liftedFamily.{u,v,w,j,j} F) (liftedTermsSmall F)

def liftedSumRealization (F : I → RightDGModuleModel A) :
    StrictSum (liftedFamily.{u,v,w,j,j} F) (liftedSum F) :=
  sumRealization _ (liftedTermsSmall F)

theorem adequateIndex : AdequateIndex.{u,v,w,j} :=
  fun F => ⟨liftedTermsSmall F, liftedSum F, liftedSumRealization F,
    ⟨isColimit (liftedSumRealization F)⟩⟩

theorem liftComparison : LiftComparison.{u,v,w,j,t} := by
  intro k _ A I F S s
  let r := liftStrictSum.{u,v,w,j,t} s
  refine ⟨r, fun _ => rfl, fun _ _ _ _ => rfl, ⟨isColimit r⟩, ?_⟩
  intro T q
  refine ⟨comparisonIso r q, inclusion_comparisonIso r q, fun a n x i => ?_⟩
  exact congrArg (fun y : SumTerm (liftedFamily.{u,v,w,j,t} F) a n => (y i).down)
    (comparisonIso_coordinates r q a n x)

end

end DerivedFormalization.DG.IndexedSums
