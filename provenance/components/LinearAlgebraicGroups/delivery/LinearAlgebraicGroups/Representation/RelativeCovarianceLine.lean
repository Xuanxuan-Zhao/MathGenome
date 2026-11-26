import Specs.LinearAlgebraicGroups.Representation.RelativeCovarianceLine
import LinearAlgebraicGroups.Representation.FlagCohomology
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.RelativeCovarianceLine

open LinearAlgebraicGroups.Specs
open Specs.FlagCohomology Specs.RelativeCovarianceLine
open LinearAlgebraicGroups.Representation.FlagCohomology
open private covariance_app_eq_zero pullbackOnOpen firstLeft_w secondLeft_w
  regularSection_mem_covariance equivKernelOnOpen equivKernelOnOpen_apply
  sectionGenerator sectionGeneratorOver restrictSection
  quasicoherent_of_unit_on_cover isIso_adjoint_of_local_generators covariancePullback_app
  from LinearAlgebraicGroups.Representation.FlagCohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A B : Type u} [CommRing A] [CommRing B]
variable {X : SchemeOverRing A} {Y : SchemeOverRing B}

/-- The condition on a unit multiplier on a kernel pair, evaluated on three
composable pairs of points with an arbitrary test scheme. -/
private structure Cocycle (D : CovarianceData X) : Prop where
  unit : IsUnit D.multiplier
  mul : ∀ {S : Scheme.{u}} (a b c : S ⟶ D.overlap.left),
    a ≫ D.second.left = b ≫ D.first.left →
    a ≫ D.first.left = c ≫ D.first.left →
    b ≫ D.second.left = c ≫ D.second.left →
    c.appTop D.multiplier = a.appTop D.multiplier * b.appTop D.multiplier

private theorem appTop_comp_apply {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (r : Γ(U, ⊤)) : (f ≫ g).appTop r = f.appTop (g.appTop r) := rfl

private theorem topIso_appLE {P Q : Scheme.{u}} (f : P ⟶ Q)
    {U : Q.Opens} {V : P.Opens} (h : V ≤ f ⁻¹ᵁ U) (x : Γ(Q, U)) :
    V.topIso.inv (f.appLE U V h x) = (f.resLE U V h).appTop (U.topIso.inv x) := by
  change _ = (f.resLE U V h).app ⊤ (U.topIso.inv x)
  rw [Scheme.Hom.resLE_app_top]
  change V.topIso.inv (f.appLE U V h x) =
    V.topIso.inv (f.appLE U V h ((U.topIso.inv ≫ U.topIso.hom) x))
  rw [U.topIso.inv_hom_id]
  rfl

private theorem topIso_restrict {P : Scheme.{u}} (V : P.Opens) (x : Γ(P, ⊤)) :
    V.topIso.inv (P.presheaf.map V.leTop.op x) = V.ι.appTop x := by
  change (P.presheaf.map V.leTop.op ≫ V.topIso.inv) x = _
  rw [V.ι_appTop]
  congr 1
  simp only [Scheme.Opens.topIso_inv, ← P.presheaf.map_comp, ← op_comp]
  rfl

private abbrev ambient (D : CovarianceData X) (U : X.left.Opens)
    (z : Γ(D.sheaf, U)) : ↑Γ(D.torsor.left, D.projection.left ⁻¹ᵁ U) :=
  D.inclusion.app U z

private theorem inclusion_injective (D : CovarianceData X) (U : X.left.Opens) :
    Function.Injective (D.inclusion.app U) := by
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso (equivKernelOnOpen D.covariance U).hom).1
  apply Subtype.ext
  rwa [equivKernelOnOpen_apply, equivKernelOnOpen_apply]

private theorem lift_covariant (D : CovarianceData X) (U : X.left.Opens)
    (z : Γ(D.torsor.left, D.projection.left ⁻¹ᵁ U)) (hz : D.covariance.app U z = 0) :
    ∃ s : Γ(D.sheaf, U), D.inclusion.app U s = z := by
  let e := equivKernelOnOpen D.covariance U
  let a : (D.covariance.val.app (op U)).hom.ker := ⟨z, hz⟩
  refine ⟨e.inv a, ?_⟩
  rw [← equivKernelOnOpen_apply]
  change ((e.inv ≫ e.hom) a).val = z
  rw [e.inv_hom_id]
  rfl

section Charts

variable {D : CovarianceData X} (U : X.left.Opens)

private abbrev TorsorOpen := D.projection.left ⁻¹ᵁ U
private abbrev OverlapOpen := D.overlapProjection.left ⁻¹ᵁ U

private abbrev chartProj : (TorsorOpen (D := D) U).toScheme ⟶ U.toScheme :=
  D.projection.left.resLE U _ le_rfl

private abbrev chartFirst : (OverlapOpen (D := D) U).toScheme ⟶
    (TorsorOpen (D := D) U).toScheme :=
  D.first.left.resLE _ _ (by rw [← Scheme.Hom.comp_preimage, firstLeft_w])

private abbrev chartSecond : (OverlapOpen (D := D) U).toScheme ⟶
    (TorsorOpen (D := D) U).toScheme :=
  D.second.left.resLE _ _ (by rw [← Scheme.Hom.comp_preimage, secondLeft_w])

private theorem chartProj_eq :
    chartFirst (D := D) U ≫ chartProj U = chartSecond U ≫ chartProj U := by
  apply (cancel_mono U.ι).mp
  simp [firstLeft_w, secondLeft_w]

private abbrev chartCoeff : Γ((OverlapOpen (D := D) U).toScheme, ⊤) :=
  (OverlapOpen (D := D) U).ι.appTop D.multiplier

private theorem covariance_chart (z : Γ(D.torsor.left, TorsorOpen (D := D) U)) :
    D.covariance.app U z = 0 ↔
      (chartSecond U).appTop ((TorsorOpen (D := D) U).topIso.inv z) =
        (chartFirst U).appTop ((TorsorOpen (D := D) U).topIso.inv z) * chartCoeff U := by
  rw [covariance_app_eq_zero]
  let e := (OverlapOpen (D := D) U).topIso.inv
  have hinj := (ConcreteCategory.bijective_of_isIso e).1
  rw [← hinj.eq_iff, map_mul e.hom]
  change (OverlapOpen (D := D) U).topIso.inv
      (D.second.left.appLE _ _ _ z) =
    (OverlapOpen (D := D) U).topIso.inv (D.first.left.appLE _ _ _ z) *
      (OverlapOpen (D := D) U).topIso.inv (D.overlap.left.presheaf.map _ D.multiplier) ↔ _
  rw [topIso_appLE, topIso_appLE, topIso_restrict]

variable (s : U.toScheme ⟶ D.torsor.left) (hs : s ≫ D.projection.left = U.ι)

private def chartSection : U.toScheme ⟶ (TorsorOpen (D := D) U).toScheme :=
  IsOpenImmersion.lift (TorsorOpen (D := D) U).ι s (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (s ≫ D.projection.left) x ∈ U
    rw [hs]
    exact x.2)

@[simp, reassoc]
private theorem chartSection_ι :
    chartSection U s hs ≫ (TorsorOpen (D := D) U).ι = s :=
  IsOpenImmersion.lift_fac _ _ _

@[simp, reassoc]
private theorem chartSection_proj :
    chartSection U s hs ≫ chartProj U = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, chartSection_ι, hs,
    Category.id_comp]

variable (pb : IsPullback D.first.left D.second.left D.projection.left D.projection.left)

private def division : (TorsorOpen (D := D) U).toScheme ⟶ D.overlap.left :=
  pb.lift (chartProj U ≫ s) (TorsorOpen (D := D) U).ι (by simp [hs])

@[simp, reassoc]
private theorem division_first :
    division U s hs pb ≫ D.first.left = chartProj U ≫ s :=
  pb.lift_fst _ _ _

@[simp, reassoc]
private theorem division_second :
    division U s hs pb ≫ D.second.left = (TorsorOpen (D := D) U).ι :=
  pb.lift_snd _ _ _

include s hs pb in
private theorem frame_covariant (c : Cocycle D) :
    ∃ z : Γ(D.sheaf, U), IsUnit (ambient D U z) := by
  let k := division U s hs pb
  let V := TorsorOpen (D := D) U
  let W := OverlapOpen (D := D) U
  let z := V.topIso.hom (k.appTop D.multiplier)
  have hz : V.topIso.inv z = k.appTop D.multiplier := by
    change (V.topIso.hom ≫ V.topIso.inv) _ = _
    rw [V.topIso.hom_inv_id]
    rfl
  have hcov : D.covariance.app U z = 0 := by
    apply (covariance_chart U z).mpr
    rw [hz, ← appTop_comp_apply, ← appTop_comp_apply]
    apply c.mul (chartFirst U ≫ k) (W.ι) (chartSecond U ≫ k)
    · rw [Category.assoc, division_second, Scheme.Hom.resLE_comp_ι]
    · rw [Category.assoc, Category.assoc, division_first,
        ← Category.assoc (chartFirst U), ← Category.assoc (chartSecond U), chartProj_eq]
    · rw [Category.assoc, division_second, Scheme.Hom.resLE_comp_ι]
  obtain ⟨x, hx⟩ := lift_covariant D U z hcov
  refine ⟨x, ?_⟩
  change ambient D U x = z at hx
  rw [hx]
  exact (c.unit.map k.appTop.hom).map V.topIso.hom.hom

private theorem chart_covariance_formula (x : Γ(D.sheaf, U)) :
    let y := (TorsorOpen (D := D) U).topIso.inv (D.inclusion.app U x)
    y = (chartProj U).appTop ((chartSection U s hs).appTop y) *
      (division U s hs pb).appTop D.multiplier := by
  let k := division U s hs pb
  let W := OverlapOpen (D := D) U
  let V := TorsorOpen (D := D) U
  let y := V.topIso.inv (D.inclusion.app U x)
  have hk : Set.range k ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    change (k ≫ D.overlapProjection.left) v ∈ U
    have h : k ≫ D.overlapProjection.left = V.ι ≫ D.projection.left := by
      rw [← secondLeft_w D, ← Category.assoc, division_second]
    rw [h]
    exact v.2
  let j := IsOpenImmersion.lift W.ι k hk
  have hj : j ≫ W.ι = k := IsOpenImmersion.lift_fac _ _ _
  have hj₀ : j ≫ chartFirst (D := D) U = chartProj U ≫ chartSection U s hs := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hj, division_first,
      Category.assoc, chartSection_ι]
  have hj₁ : j ≫ chartSecond (D := D) U = 𝟙 V.toScheme := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hj, division_second,
      Category.id_comp]
  have eq := (covariance_chart U _).mp (regularSection_mem_covariance D U x)
  change (chartSecond U).appTop y = (chartFirst U).appTop y * chartCoeff U at eq
  have hh := congrArg (j.appTop ·) eq
  rw [map_mul j.appTop.hom] at hh
  change (j ≫ chartSecond U).appTop y =
    (j ≫ chartFirst U).appTop y * (j ≫ W.ι).appTop D.multiplier at hh
  rw [hj₁, hj₀, hj, appTop_comp_apply] at hh
  exact hh

private theorem chart_smul (x : Γ(D.sheaf, U)) (r : Γ(X.left, U)) :
    (TorsorOpen (D := D) U).topIso.inv (D.inclusion.app U (r • x)) =
    (chartProj U).appTop (U.topIso.inv r) *
      (TorsorOpen (D := D) U).topIso.inv (D.inclusion.app U x) := by
  let i := D.inclusion.val.app (op U)
  change (TorsorOpen (D := D) U).topIso.inv (i (r • x)) = _
  rw [i.hom.map_smul]
  change (TorsorOpen (D := D) U).topIso.inv
    (D.projection.left.app U r * ambient D U x) = _
  rw [map_mul (TorsorOpen (D := D) U).topIso.inv.hom]
  rw [← Scheme.Hom.appLE_eq_app, topIso_appLE]

include s hs pb in
private theorem chart_generator_bijective (z : Γ(D.sheaf, U))
    (hz : IsUnit (ambient D U z)) :
    Function.Bijective (sectionGenerator D.sheaf U z) := by
  let V := TorsorOpen (D := D) U
  let i := fun x : Γ(D.sheaf, U) => V.topIso.inv (D.inclusion.app U x)
  let q := (chartProj (D := D) U).appTop
  let a := (chartSection U s hs).appTop
  have haq (r : Γ(U.toScheme, ⊤)) : a (q r) = r := by
    rw [← appTop_comp_apply, chartSection_proj]
    rfl
  have hi : Function.Injective i :=
    (ConcreteCategory.bijective_of_isIso V.topIso.inv).1.comp (inclusion_injective D U)
  have hU := ConcreteCategory.bijective_of_isIso U.topIso.inv
  have hunit : IsUnit (i z) := hz.map V.topIso.inv.hom
  have smul_eq (x : Γ(D.sheaf, U)) (r : Γ(X.left, U)) :
      i (r • x) = q (U.topIso.inv r) * i x := chart_smul U x r
  constructor
  · intro r r' h
    apply hU.1
    apply_fun i at h
    change i (r • z) = i (r' • z) at h
    rw [smul_eq, smul_eq] at h
    exact (haq _).symm.trans ((congrArg a (hunit.mul_right_cancel h)).trans (haq _))
  · intro x
    let d := (division U s hs pb).appTop D.multiplier
    have hx : i x = q (a (i x)) * d := chart_covariance_formula U s hs pb x
    have hz' : i z = q (a (i z)) * d := chart_covariance_formula U s hs pb z
    obtain ⟨w, hw⟩ := (hunit.map a.hom).exists_right_inv
    have hw' : w * a (i z) = 1 := (mul_comm _ _).trans hw
    obtain ⟨r, hr⟩ := hU.2 (a (i x) * w)
    refine ⟨r, hi ?_⟩
    change i (r • z) = i x
    rw [smul_eq]
    change q (U.topIso.inv r) * i z = i x
    rw [hr, hz', ← mul_assoc, ← map_mul q.hom, mul_assoc, hw', mul_one, ← hx]

end Charts

private theorem restrict_ambient_unit {D : CovarianceData X} {U V : X.left.Opens} (h : V ≤ U)
    (z : Γ(D.sheaf, U)) (hz : IsUnit (ambient D U z)) :
    IsUnit (ambient D V (restrictSection D.sheaf h z)) := by
  let j := (homOfLE h).op
  have he := PresheafOfModules.naturality_apply D.inclusion.val j z
  change ambient D V (restrictSection D.sheaf h z) =
    D.torsor.left.presheaf.map ((Opens.map D.projection.left.base).map j.unop).op
      (ambient D U z) at he
  rw [he]
  exact hz.map _

private theorem generator_iso {D : CovarianceData X}
    (pb : IsPullback D.first.left D.second.left D.projection.left D.projection.left)
    (U : X.left.Opens) (s : U.toScheme ⟶ D.torsor.left) (hs : s ≫ D.projection.left = U.ι)
    (z : Γ(D.sheaf, U)) (hz : IsUnit (ambient D U z)) :
    IsIso (sectionGeneratorOver D.sheaf U z) := by
  let F := SheafOfModules.toSheaf (X.left.ringCatSheaf.over U)
  let m := sectionGeneratorOver D.sheaf U z
  let G := sheafToPresheaf ((Opens.grothendieckTopology X.left).over U) AddCommGrpCat.{u}
  have hi : IsIso (G.map (F.map m)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro W
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    let V : X.left.Opens := W.unop.left
    let h : V ≤ U := W.unop.hom.le
    let t := X.left.homOfLE h ≫ s
    have ht : t ≫ D.projection.left = V.ι := by simp [t, hs]
    change Function.Bijective (sectionGenerator D.sheaf V (restrictSection D.sheaf h z))
    exact chart_generator_bijective V t ht pb _ (restrict_ambient_unit h z hz)
  let : IsIso (F.map m) := isIso_of_reflects_iso (F.map m) G
  exact isIso_of_reflects_iso m F

private theorem line_of_local_ambient_units (D : CovarianceData X)
    (pb : IsPullback D.first.left D.second.left D.projection.left D.projection.left)
    (h : ∀ x : X.left, ∃ U : X.left.Opens, x ∈ U ∧
      ∃ s : U.toScheme ⟶ D.torsor.left, s ≫ D.projection.left = U.ι ∧
      ∃ z : Γ(D.sheaf, U), IsUnit (ambient D U z)) :
    ArithmeticProjectiveFiniteness.IsLineBundleOn A X D.sheaf := by
  choose U hx s hs z hz using h
  let e (x : X.left) := @asIso _ _ _ _ (sectionGeneratorOver D.sheaf (U x) (z x))
    (generator_iso pb (U x) (s x) (hs x) (z x) (hz x))
  have cov : (⨆ x, U x) = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  refine ⟨quasicoherent_of_unit_on_cover D.sheaf U cov e, ?_⟩
  intro x
  let F := (Scheme.Modules.overEquiv (U x)).functor
  refine ⟨U x, hx x, ⟨((Scheme.Modules.overFunctorEquiv (U x)).app D.sheaf).symm ≪≫
    F.mapIso (e x).symm ≪≫ (U x).sheafOfModulesEquivOverUnit X.left.ringCatSheaf⟩⟩

section Change

variable {D : CovarianceData X} {E : CovarianceData Y} {f : Y.left ⟶ X.left}
variable (C : CartesianChange D E f)
variable (pb : IsPullback D.first.left D.second.left D.projection.left D.projection.left)

include C pb in
private theorem change_kernelPair :
    IsPullback E.first.left E.second.left E.projection.left E.projection.left := by
  have he : E.first.left ≫ E.projection.left = E.second.left ≫ E.projection.left :=
    (firstLeft_w E).trans (secondLeft_w E).symm
  refine IsPullback.mk' he ?_ ?_
  · intro S x y h₀ h₁
    apply C.overlapSquare.hom_ext
    · apply pb.hom_ext
      · rw [Category.assoc, Category.assoc, C.first_eq,
          ← Category.assoc x E.first.left, ← Category.assoc y E.first.left, h₀]
      · rw [Category.assoc, Category.assoc, C.second_eq,
          ← Category.assoc x E.second.left, ← Category.assoc y E.second.left, h₁]
    · simpa only [← firstLeft_w E, ← Category.assoc] using congrArg (· ≫ E.projection.left) h₀
  · intro S a b hab
    have hk : (a ≫ C.torsorMap) ≫ D.projection.left =
        (b ≫ C.torsorMap) ≫ D.projection.left := by
      rw [Category.assoc, Category.assoc, C.torsorSquare.w, ← Category.assoc a E.projection.left,
        ← Category.assoc b E.projection.left, hab]
    let k := pb.lift (a ≫ C.torsorMap) (b ≫ C.torsorMap) hk
    have hj : k ≫ D.overlapProjection.left = (a ≫ E.projection.left) ≫ f := by
      rw [← firstLeft_w D, ← Category.assoc, pb.lift_fst, Category.assoc, C.torsorSquare.w,
        Category.assoc]
    let j := C.overlapSquare.lift k (a ≫ E.projection.left) hj
    have j₀ : j ≫ C.overlapMap = k := C.overlapSquare.lift_fst _ _ _
    have j₁ : j ≫ E.overlapProjection.left = a ≫ E.projection.left :=
      C.overlapSquare.lift_snd _ _ _
    refine ⟨j, C.torsorSquare.hom_ext ?_ ?_, C.torsorSquare.hom_ext ?_ ?_⟩
    · rw [Category.assoc, ← C.first_eq, ← Category.assoc, j₀, pb.lift_fst]
    · rw [Category.assoc, firstLeft_w E, j₁]
    · rw [Category.assoc, ← C.second_eq, ← Category.assoc, j₀, pb.lift_snd]
    · rw [Category.assoc, secondLeft_w E, j₁, hab]

include C in
private theorem change_local_section (U : X.left.Opens)
    (s : U.toScheme ⟶ D.torsor.left) (hs : s ≫ D.projection.left = U.ι) :
    ∃ t : (f ⁻¹ᵁ U).toScheme ⟶ E.torsor.left, t ≫ E.projection.left = (f ⁻¹ᵁ U).ι := by
  have h : (f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ s) ≫ D.projection.left = (f ⁻¹ᵁ U).ι ≫ f := by
    rw [Category.assoc, hs, Scheme.Hom.resLE_comp_ι]
  exact ⟨_, C.torsorSquare.lift_snd _ _ h⟩

private theorem change_ambient_unit
    {α : D.sheaf ⟶ (Scheme.Modules.pushforward f).obj E.sheaf}
    (hα : D.IsPullbackMap E f C.torsorMap C.torsorSquare.w α)
    (U : X.left.Opens) (z : Γ(D.sheaf, U)) (hz : IsUnit (ambient D U z)) :
    IsUnit (ambient E (f ⁻¹ᵁ U) (α.app U z)) := by
  have e := covariancePullback_app hα U z
  change ambient E (f ⁻¹ᵁ U) (α.app U z) =
      pullbackOnOpen _ _ _ C.torsorSquare.w U (ambient D U z) at e
  rw [e]
  exact hz.map _

include pb in
private theorem comparison_of_charts (c : Cocycle D)
    (hlocal : ∀ x : X.left, ∃ U : X.left.Opens, x ∈ U ∧
      ∃ s : U.toScheme ⟶ D.torsor.left, s ≫ D.projection.left = U.ι) :
    C.HasComparison ∧ ArithmeticProjectiveFiniteness.IsLineBundleOn B Y E.sheaf := by
  obtain ⟨α, hα⟩ := covariancePullback_exists D E f _ C.torsorSquare.w _
    C.first_eq C.second_eq C.multiplier_eq
  have pb' := change_kernelPair C pb
  have h (y : Y.left) : ∃ U : X.left.Opens, f y ∈ U ∧
      ∃ (s : U.toScheme ⟶ D.torsor.left) (t : (f ⁻¹ᵁ U).toScheme ⟶ E.torsor.left),
        s ≫ D.projection.left = U.ι ∧ t ≫ E.projection.left = (f ⁻¹ᵁ U).ι ∧
        ∃ z : Γ(D.sheaf, U),
          IsUnit (ambient D U z) ∧ IsUnit (ambient E (f ⁻¹ᵁ U) (α.app U z)) := by
    obtain ⟨U, hy, s, hs⟩ := hlocal (f y)
    obtain ⟨t, ht⟩ := change_local_section C U s hs
    obtain ⟨z, hz⟩ := frame_covariant U s hs pb c
    exact ⟨U, hy, s, t, hs, ht, z, hz, change_ambient_unit C hα U z hz⟩
  have hi := isIso_adjoint_of_local_generators f α (fun y => by
    obtain ⟨U, hy, s, t, hs, ht, z, hz, hz'⟩ := h y
    exact ⟨U, hy, z, generator_iso pb U s hs z hz, generator_iso pb' _ t ht _ hz'⟩)
  let e := @asIso _ _ _ _ (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm α) hi
  refine ⟨⟨e, ?_⟩, line_of_local_ambient_units E pb' ?_⟩
  · change D.IsPullbackMap E f _ _ ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm α))
    rw [Equiv.apply_symm_apply]
    exact hα
  · intro y
    obtain ⟨U, hy, _, t, _, ht, z, _, hz'⟩ := h y
    exact ⟨f ⁻¹ᵁ U, hy, t, ht, α.app U z, hz'⟩

end Change

section RightTorsor

variable (T : Torsor A)

private theorem rightMultiply_comp {G H : Grp (SchemeOverRing A)} (i : H ⟶ G)
    {S : SchemeOverRing A} (p : S ⟶ G.X ⨯ H.X) :
    p ≫ rightMultiply i = (p ≫ prod.fst) * ((p ≫ prod.snd) ≫ i.hom.hom) := by
  simp [rightMultiply, MonObj.comp_mul, Category.assoc]

private def inverseCharacter {S : SchemeOverRing A} (b : S ⟶ T.subgroup.X) :
    Γ(S.left, ⊤)ˣ :=
  Units.map b.left.appTop.hom.toMonoidHom T.character⁻¹

private theorem inverseCharacter_mul {S : SchemeOverRing A} (b c : S ⟶ T.subgroup.X) :
    inverseCharacter T (b * c) = inverseCharacter T b * inverseCharacter T c := by
  have hu : Units.map (b * c).left.appTop.hom.toMonoidHom T.character =
      Units.map b.left.appTop.hom.toMonoidHom T.character *
        Units.map c.left.appTop.hom.toMonoidHom T.character := by
    apply Units.ext
    change (b * c).left.appTop (T.character : Γ(T.subgroup.X.left, ⊤)) =
      b.left.appTop (T.character : Γ(T.subgroup.X.left, ⊤)) *
        c.left.appTop (T.character : Γ(T.subgroup.X.left, ⊤))
    change (lift b c ≫ μ[T.subgroup.X]).left.appTop _ = _
    rw [Over.comp_left, appTop_comp_apply, T.character_mul, map_mul (lift b c).left.appTop.hom]
    rw [← appTop_comp_apply, ← appTop_comp_apply, ← Over.comp_left, ← Over.comp_left,
      lift_fst, lift_snd]
  simp only [inverseCharacter, map_inv, hu, mul_inv_rev]
  exact mul_comm _ _

private theorem right_cocycle_over {S : SchemeOverRing A} (a b c : S ⟶ T.lineData.overlap)
    (hab : a ≫ T.lineData.second = b ≫ T.lineData.first)
    (hac : a ≫ T.lineData.first = c ≫ T.lineData.first)
    (hbc : b ≫ T.lineData.second = c ≫ T.lineData.second) :
    c.left.appTop T.lineData.multiplier =
      a.left.appTop T.lineData.multiplier * b.left.appTop T.lineData.multiplier := by
  let j : T.lineData.overlap ⟶ T.subgroup.X := prod.snd
  let i : T.subgroup.X ⟶ T.group.X := T.inclusion.hom.hom
  have hi : Mono i := by
    have hI := T.closedSubgroup
    let : IsClosedImmersion i.left := hI
    exact Over.mono_of_mono_left _
  let p : T.lineData.overlap ⟶ T.group.X := T.lineData.first
  have eq₁ : (a ≫ p) * ((a ≫ j) ≫ i) = b ≫ p :=
    (rightMultiply_comp T.inclusion a).symm.trans hab
  have eq₂ : (b ≫ p) * ((b ≫ j) ≫ i) =
      (c ≫ p) * ((c ≫ j) ≫ i) :=
    (rightMultiply_comp T.inclusion b).symm.trans (hbc.trans (rightMultiply_comp T.inclusion c))
  have eq : c ≫ j = (a ≫ j) * (b ≫ j) := by
    apply (cancel_mono i).mp
    have h : ((a ≫ j) * (b ≫ j)) ≫ i = ((a ≫ j) ≫ i) * ((b ≫ j) ≫ i) :=
      (IsMonHom.monoidHom T.inclusion.hom.hom S).map_mul _ _
    rw [h]
    apply mul_left_cancel (a := a ≫ p)
    change a ≫ p = c ≫ p at hac
    rw [← hac] at eq₂
    rw [← mul_assoc, eq₁]
    exact eq₂.symm
  have e := congrArg (inverseCharacter T) eq
  rw [inverseCharacter_mul] at e
  have val := congrArg Units.val e
  change (c ≫ j).left.appTop _ = (a ≫ j).left.appTop _ * (b ≫ j).left.appTop _ at val
  simp only [Over.comp_left, appTop_comp_apply] at val
  exact val

private theorem right_cocycle : Cocycle T.lineData := by
  refine ⟨?_, ?_⟩
  · exact T.character⁻¹.isUnit.map (prod.snd :
      T.group.X ⨯ T.subgroup.X ⟶ T.subgroup.X).left.appTop.hom
  · intro S a b c hab hac hbc
    let W := T.lineData.overlap
    let S' := Over.mk (a ≫ W.hom)
    have hb : b ≫ W.hom = a ≫ W.hom := by
      change b ≫ T.lineData.overlap.hom = a ≫ T.lineData.overlap.hom
      rw [← Over.w T.lineData.first, ← Category.assoc, ← hab,
        Category.assoc]
      exact congrArg (a ≫ ·) ((Over.w T.lineData.second).trans (Over.w T.lineData.first).symm)
    have hc : c ≫ W.hom = a ≫ W.hom := by
      change c ≫ T.lineData.overlap.hom = a ≫ T.lineData.overlap.hom
      rw [← Over.w T.lineData.first, ← Category.assoc, ← hac, Category.assoc]
    let α : S' ⟶ W := Over.homMk a rfl
    let β : S' ⟶ W := Over.homMk b hb
    let third : S' ⟶ W := Over.homMk c hc
    exact right_cocycle_over T α β third (Over.OverMorphism.ext hab)
      (Over.OverMorphism.ext hac) (Over.OverMorphism.ext hbc)

private theorem right_kernelPair :
    IsPullback T.lineData.first.left T.lineData.second.left
      T.lineData.projection.left T.lineData.projection.left :=
  (Over.forget _).map_isPullback T.kernelPair

/-- The relative inverse-character covariance kernel is a line bundle. -/
theorem isLineBundle : IsLineBundle.{u} := by
  intro A _ T
  apply line_of_local_ambient_units T.lineData (right_kernelPair T)
  intro x
  obtain ⟨U, hx, s, hs⟩ := T.localSections x
  exact ⟨U, hx, s, hs, frame_covariant U s hs (right_kernelPair T) (right_cocycle T)⟩

/-- The comparison for Cartesian torsors and overlaps is the adjoint of
pulling back covariant functions along the torsor map. -/
theorem cartesianComparison : CartesianComparison.{u} := by
  intro A B _ _ T Y E f C
  exact comparison_of_charts C (right_kernelPair T) (right_cocycle T) T.localSections

/-- A compatible isomorphism of quotient data is a Cartesian comparison. -/
theorem isoComparison : IsoComparison.{u} := by
  intro A B _ _ T Y E f g j hg hj h₀ h₁ hc
  let C : CartesianChange T.lineData E f.hom :=
    { torsorMap := g.hom
      overlapMap := j.hom
      torsorSquare := IsPullback.of_horiz_isIso ⟨hg⟩
      overlapSquare := IsPullback.of_horiz_isIso ⟨hj⟩
      first_eq := h₀
      second_eq := h₁
      multiplier_eq := hc }
  exact (cartesianComparison A B T E f.hom C).1

end RightTorsor

section BaseChange

open ArithmeticCohomologyBaseChange (fibreProjection changeBase)

private theorem changeBaseMap_isPullback (φ : A →+* B) {X Y : SchemeOverRing A} (q : X ⟶ Y) :
    IsPullback ((changeBase φ).map q).left (fibreProjection φ X)
      (fibreProjection φ Y) q.left := by
  let b := Spec.map (CommRingCat.ofHom φ)
  have h : IsPullback (fibreProjection φ X) (pullback.snd X.hom b) (q.left ≫ Y.hom) b := by
    rw [Over.w q]
    exact IsPullback.of_hasPullback _ _
  have hf : ((changeBase φ).map q).left ≫ fibreProjection φ Y =
      fibreProjection φ X ≫ q.left := pullback.lift_fst _ _ _
  have hs : ((changeBase φ).map q).left ≫ pullback.snd Y.hom b =
      pullback.snd X.hom b := pullback.lift_snd _ _ _
  exact (IsPullback.of_bot (hs.symm ▸ h) hf.symm (IsPullback.of_hasPullback Y.hom b)).flip

/-- Change of the coefficient ring gives the adjoint comparison along the
actual fibre projections. -/
theorem ringComparison : RingComparison.{u} := by
  intro A B _ _ T φ
  let D := T.lineData
  let C : CartesianChange D (ringChange D φ) (fibreProjection φ T.quotient) :=
    { torsorMap := fibreProjection φ D.torsor
      overlapMap := fibreProjection φ D.overlap
      torsorSquare := (changeBaseMap_isPullback φ D.projection).flip
      overlapSquare := (changeBaseMap_isPullback φ D.overlapProjection).flip
      first_eq := (changeBaseMap_isPullback φ D.first).w.symm
      second_eq := (changeBaseMap_isPullback φ D.second).w.symm
      multiplier_eq := rfl }
  exact ⟨C, rfl, rfl, (cartesianComparison A B T _ _ C).1⟩

end BaseChange

section Action

private theorem whiskerLeft_isPullback (W : SchemeOverRing A) {X Y : SchemeOverRing A}
    (q : X ⟶ Y) : IsPullback (snd W X) (W ◁ q) q (snd W Y) := by
  refine IsPullback.mk' (whiskerLeft_snd _ _).symm ?_ ?_
  · intro T a b hab he
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, whiskerLeft_fst] using congrArg (· ≫ fst W Y) he
    · exact hab
  · intro T a b hab
    refine ⟨lift (b ≫ fst W Y) a, lift_snd _ _, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [hab]


/-- Multiplication on the torsor is cartesian over the left action on
the quotient. Its inverse over an acting element uses that element's inverse. -/
private theorem actionTorsor_isPullback (T : Torsor A)
    (act : ModObj T.group.X T.quotient)
    (ha : μ[T.group.X] ≫ T.projection = (𝟙 T.group.X ⊗ₘ T.projection) ≫ T.leftAction act) :
    IsPullback μ[T.group.X] (T.group.X ◁ T.projection) T.projection (T.leftAction act) := by
  let G := T.group.X
  let Y := T.quotient
  let q : G ⟶ Y := T.projection
  let : ModObj G Y := act
  let : ModObj G G := ModObj.regular G
  let : IsModHom G q := ⟨ha⟩
  have multiply {S : SchemeOverRing A} (f : S ⟶ G ⊗ G) :
      f ≫ μ[G] = (f ≫ fst G G) * (f ≫ snd G G) := by
    change f ≫ μ[G] = lift (f ≫ fst G G) (f ≫ snd G G) ≫ μ[G]
    rw [lift_comp_fst_snd]
  refine IsPullback.mk' ha ?_ ?_
  · intro S a b hab hq
    change a ≫ (G ◁ q) = b ≫ (G ◁ q) at hq
    have hfst : a ≫ fst G G = b ≫ fst G G := by
      have hr : (G ◁ q) ≫ fst G Y = fst G G := whiskerLeft_fst G q
      calc
        _ = (a ≫ (G ◁ q)) ≫ fst G Y := by rw [Category.assoc, hr]
        _ = (b ≫ (G ◁ q)) ≫ fst G Y := congrArg (· ≫ fst G Y) hq
        _ = _ := by rw [Category.assoc, hr]
    refine CartesianMonoidalCategory.hom_ext a b hfst ?_
    rw [multiply, multiply, hfst] at hab
    exact mul_left_cancel hab
  · intro S a b hw
    let g := b ≫ fst G Y
    let y := b ≫ snd G Y
    let i : S ⟶ G := g⁻¹ * a
    refine ⟨lift g i, ?_, ?_⟩
    · change g * (g⁻¹ * a) = a
      exact mul_inv_cancel_left _ _
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_whiskerLeft, lift_fst, g]
        rfl
      · simp only [lift_whiskerLeft, lift_snd]
        change ((g⁻¹ : S ⟶ G) • a) ≫ q = y
        rw [IsModHom.map_smul q]
        have hw' : a ≫ q = g • y := by
          change a ≫ q = lift (b ≫ fst G Y) (b ≫ snd G Y) ≫ T.leftAction act
          rw [lift_comp_fst_snd]
          exact hw
        rw [hw', ← mul_smul, inv_mul_cancel, one_smul]

/-- Left translation of the group coordinate in the right torsor overlap. -/
private def translateOverlap (T : Torsor A) :
    T.actionLineData.overlap ⟶ T.lineData.overlap :=
  prod.lift (fst _ _ * (snd _ _ ≫ prod.fst)) (snd _ _ ≫ prod.snd)

private theorem translateOverlap_first (T : Torsor A) :
    translateOverlap T ≫ T.lineData.first = T.actionLineData.first ≫ μ[T.group.X] := by
  let f : T.group.X ⨯ T.subgroup.X ⟶ T.group.X := prod.fst
  change translateOverlap T ≫ f = (T.group.X ◁ f) ≫ μ[T.group.X]
  rw [← lift_comp_fst_snd (T.group.X ◁ f)]
  change translateOverlap T ≫ f =
    (T.group.X ◁ f ≫ fst T.group.X T.group.X) * (T.group.X ◁ f ≫ snd T.group.X T.group.X)
  rw [whiskerLeft_snd, whiskerLeft_fst]
  exact prod.lift_fst _ _

private theorem translateOverlap_second (T : Torsor A) :
    translateOverlap T ≫ T.lineData.second = T.actionLineData.second ≫ μ[T.group.X] := by
  let f : T.group.X ⨯ T.subgroup.X ⟶ T.group.X := rightMultiply T.inclusion
  change translateOverlap T ≫ f = (T.group.X ◁ f) ≫ μ[T.group.X]
  rw [← lift_comp_fst_snd (T.group.X ◁ f)]
  change translateOverlap T ≫ f =
    (T.group.X ◁ f ≫ fst T.group.X T.group.X) * (T.group.X ◁ f ≫ snd T.group.X T.group.X)
  rw [whiskerLeft_snd, whiskerLeft_fst]
  let g := fst T.group.X (T.group.X ⨯ T.subgroup.X)
  let s := snd T.group.X (T.group.X ⨯ T.subgroup.X)
  change prod.lift (g * (s ≫ prod.fst)) (s ≫ prod.snd) ≫ rightMultiply T.inclusion =
    g * (s ≫ rightMultiply T.inclusion)
  rw [rightMultiply_comp, prod.lift_fst, prod.lift_snd, rightMultiply_comp]
  exact mul_assoc _ _ _

/-- Acting on the left preserves the inverse-character transition function
of the line on the right torsor. -/
private theorem translateOverlap_multiplier (T : Torsor A) :
    (translateOverlap T).left.appTop T.lineData.multiplier = T.actionLineData.multiplier := by
  let d : T.lineData.overlap ⟶ T.subgroup.X := prod.snd
  let s := snd T.group.X T.lineData.overlap
  have hd : translateOverlap T ≫ d = s ≫ d := prod.lift_snd _ _
  let t : Γ(T.subgroup.X.left, ⊤) := (T.character⁻¹ : Γ(T.subgroup.X.left, ⊤)ˣ)
  change (d.left.appTop ≫ (translateOverlap T).left.appTop) t = (d.left.appTop ≫ s.left.appTop) t
  have hh : (translateOverlap T).left ≫ d.left = s.left ≫ d.left :=
    congrArg Over.Hom.left hd
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hh]
  rfl

private theorem translateOverlap_isPullback (T : Torsor A) :
    IsPullback (translateOverlap T) (T.group.X ◁ T.lineData.first) T.lineData.first μ[T.group.X] := by
  let G := T.group.X
  let H := T.subgroup.X
  let W := T.lineData.overlap
  let p : W ⟶ G := prod.fst
  let d : W ⟶ H := prod.snd
  have hw : translateOverlap T ≫ p = (G ◁ p) ≫ μ[G] := translateOverlap_first T
  have hd : translateOverlap T ≫ d = snd G W ≫ d := prod.lift_snd _ _
  change IsPullback (translateOverlap T) (G ◁ p) p μ[G]
  refine IsPullback.mk' hw ?_ ?_
  · intro S x y h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, whiskerLeft_fst] using congrArg (· ≫ fst G G) h₂
    · apply prod.hom_ext
      · change (x ≫ snd G W) ≫ p = (y ≫ snd G W) ≫ p
        simpa only [Category.assoc, whiskerLeft_snd] using congrArg (· ≫ snd G G) h₂
      · change (x ≫ snd G W) ≫ d = (y ≫ snd G W) ≫ d
        simpa only [Category.assoc, hd] using congrArg (· ≫ d) h₁
  · intro S x y hxy
    let z : S ⟶ W := prod.lift (y ≫ snd G G) (x ≫ d)
    let k := lift (y ≫ fst G G) z
    have h : k ≫ (G ◁ p) = y := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, whiskerLeft_fst]
        exact lift_fst _ _
      · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc]
        rw [show k ≫ snd G W = z from lift_snd _ _]
        exact prod.lift_fst _ _
    refine ⟨k, ?_, h⟩
    apply prod.hom_ext
    · change (k ≫ translateOverlap T) ≫ p = x ≫ p
      rw [Category.assoc, hw, ← Category.assoc, h]
      exact hxy.symm
    · change (k ≫ translateOverlap T) ≫ d = x ≫ d
      rw [Category.assoc, hd, ← Category.assoc, show k ≫ snd G W = z from lift_snd _ _]
      exact prod.lift_snd _ _

private def projectionChange (T : Torsor A) :
    CartesianChange T.lineData T.actionLineData (snd T.group.X T.quotient).left where
  torsorMap := (snd T.group.X T.group.X).left
  overlapMap := (snd T.group.X T.lineData.overlap).left
  torsorSquare := (Over.forget _).map_isPullback (whiskerLeft_isPullback _ T.projection)
  overlapSquare := (Over.forget _).map_isPullback (whiskerLeft_isPullback _ T.lineData.overlapProjection)
  first_eq := congrArg Over.Hom.left (whiskerLeft_snd _ _).symm
  second_eq := congrArg Over.Hom.left (whiskerLeft_snd _ _).symm
  multiplier_eq := rfl

private def actionChange (T : Torsor A) (a : ModObj T.group.X T.quotient)
    (ha : μ[T.group.X] ≫ T.projection = (𝟙 T.group.X ⊗ₘ T.projection) ≫ T.leftAction a) :
    CartesianChange T.lineData T.actionLineData (T.leftAction a).left where
  torsorMap := μ[T.group.X].left
  overlapMap := (translateOverlap T).left
  torsorSquare := (Over.forget _).map_isPullback (actionTorsor_isPullback T a ha)
  overlapSquare := by
    have h := (translateOverlap_isPullback T).paste_vert (actionTorsor_isPullback T a ha)
    rw [← whiskerLeft_comp] at h
    exact (Over.forget _).map_isPullback h
  first_eq := congrArg Over.Hom.left (translateOverlap_first T)
  second_eq := congrArg Over.Hom.left (translateOverlap_second T)
  multiplier_eq := translateOverlap_multiplier T

end Action

section AdjointComposition

open Scheme.Modules

variable {P Q R : Scheme.{u}} (j : R ⟶ Q) (f g : Q ⟶ P)

private abbrev adj (f : Q ⟶ P) := Scheme.Modules.pullbackPushforwardAdjunction f

private def composePull {F : P.Modules} {G : Q.Modules} {H : R.Modules}
    (e : (Scheme.Modules.pullback f).obj F ⟶ G) (k : (Scheme.Modules.pullback j).obj G ⟶ H) :
    (Scheme.Modules.pullback (j ≫ f)).obj F ⟶ H :=
  (pullbackComp j f).inv.app F ≫ (Scheme.Modules.pullback j).map e ≫ k

private theorem adjoint_composePull {F : P.Modules} {G : Q.Modules} {H : R.Modules}
    (e : (Scheme.Modules.pullback f).obj F ⟶ G) (k : (Scheme.Modules.pullback j).obj G ⟶ H) :
    (adj (j ≫ f)).homEquiv _ _ (composePull j f e k) =
      (adj f).homEquiv _ _ e ≫ (pushforward f).map ((adj j).homEquiv _ _ k) ≫
        (pushforwardComp j f).hom.app H := by
  let b := (adj f).comp (adj j)
  let σ := (pullbackComp j f).inv
  let τ := (pushforwardComp j f).hom
  have hu : b.unit.app F ≫ τ.app ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback f).obj F)) =
      (adj (j ≫ f)).unit.app F ≫ (pushforward (j ≫ f)).map (σ.app F) := by
    have hu := unit_conjugateEquiv b (adj (j ≫ f)) σ F
    rw [conjugateEquiv_pullbackComp_inv] at hu
    exact hu
  let d := (Scheme.Modules.pullback j).map e ≫ k
  change (adj (j ≫ f)).homEquiv _ _ (σ.app F ≫ d) = _
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
    Category.assoc, ← τ.naturality, ← Category.assoc, ← Adjunction.homEquiv_unit]
  change b.homEquiv _ _ ((Scheme.Modules.pullback j).map e ≫ k) ≫ τ.app H = _
  rw [Adjunction.comp_homEquiv]
  change (adj f).homEquiv _ _ ((adj j).homEquiv _ _ ((Scheme.Modules.pullback j).map e ≫ k)) ≫ τ.app H = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Category.assoc]

private theorem reindex_composePull {F : P.Modules} {G : Q.Modules} {H : R.Modules}
    (a : (Scheme.Modules.pullback f).obj F ⟶ G) (p : (Scheme.Modules.pullback g).obj F ≅ G)
    (k : (Scheme.Modules.pullback j).obj G ⟶ H) :
    Specs.RelativeCovarianceLine.pullbackComparison F j f g (a ≫ p.inv) ≫ composePull j g p.hom k = composePull j f a k := by
  unfold Specs.RelativeCovarianceLine.pullbackComparison
  have hm : (Scheme.Modules.pullback j).map (a ≫ p.inv) ≫
      (Scheme.Modules.pullback j).map p.hom = (Scheme.Modules.pullback j).map a := by
    rw [← Functor.map_comp, Category.assoc, p.inv_hom_id, Category.comp_id]
  simp only [composePull, Category.assoc, Iso.hom_inv_id_app_assoc, reassoc_of% hm]

end AdjointComposition

section CovarianceAdjoints

open Scheme.Modules

variable {C : Type u} [CommRing C] {Z : SchemeOverRing C}
variable {D : CovarianceData X} {E : CovarianceData Y} {F : CovarianceData Z}

private def IsAdjointPull {f : Y.left ⟶ X.left}
    {t : E.torsor.left ⟶ D.torsor.left}
    (w : t ≫ D.projection.left = E.projection.left ≫ f)
    (e : (Scheme.Modules.pullback f).obj D.sheaf ⟶ E.sheaf) :=
  D.IsPullbackMap E f t w ((adj f).homEquiv _ _ e)

private theorem adjointPull_comp {f : Y.left ⟶ X.left} {g : Z.left ⟶ Y.left}
    {t : E.torsor.left ⟶ D.torsor.left} {s : F.torsor.left ⟶ E.torsor.left}
    {w : t ≫ D.projection.left = E.projection.left ≫ f}
    {w' : s ≫ E.projection.left = F.projection.left ≫ g}
    {e : (Scheme.Modules.pullback f).obj D.sheaf ⟶ E.sheaf} {k : (Scheme.Modules.pullback g).obj E.sheaf ⟶ F.sheaf}
    (he : IsAdjointPull w e) (hk : IsAdjointPull w' k) :
    IsAdjointPull (show (s ≫ t) ≫ D.projection.left = F.projection.left ≫ (g ≫ f) by
      rw [Category.assoc, w, ← Category.assoc, w', Category.assoc]) (composePull g f e k) := by
  unfold IsAdjointPull at he hk ⊢
  rw [adjoint_composePull]
  exact covariancePullback_comp he hk

private theorem adjointPull_eq {f f' : Y.left ⟶ X.left} (hf : f = f')
    {t t' : E.torsor.left ⟶ D.torsor.left} (ht : t = t')
    {w : t ≫ D.projection.left = E.projection.left ≫ f}
    {w' : t' ≫ D.projection.left = E.projection.left ≫ f'}
    {e : (Scheme.Modules.pullback f).obj D.sheaf ⟶ E.sheaf}
    {e' : (Scheme.Modules.pullback f').obj D.sheaf ⟶ E.sheaf}
    (he : IsAdjointPull w e) (he' : IsAdjointPull w' e') :
    e = (pullbackCongr hf).hom.app D.sheaf ≫ e' := by
  subst f'
  subst t'
  rw [show (pullbackCongr (rfl : f = f)).hom.app D.sheaf = 𝟙 _ by rfl, Category.id_comp]
  unfold IsAdjointPull at he he'
  exact ((adj f).homEquiv _ _).injective (covariancePullback_unique _ _ _ _ _ he he')

end CovarianceAdjoints

section ActionCoherence

open Scheme.Modules

private theorem pull_of_maps {X Y : SchemeOverRing A} {D : CovarianceData X} {E : CovarianceData Y}
    (f : Y ⟶ X) (t : E.torsor ⟶ D.torsor) (o : E.overlap ⟶ D.overlap)
    (w : t ≫ D.projection = E.projection ≫ f)
    (h₀ : o ≫ D.first = E.first ≫ t) (h₁ : o ≫ D.second = E.second ≫ t)
    (hc : o.left.appTop D.multiplier = E.multiplier) :
    ∃ e : (Scheme.Modules.pullback f.left).obj D.sheaf ⟶ E.sheaf,
      IsAdjointPull (congrArg Over.Hom.left w) e := by
  obtain ⟨α, hα⟩ := covariancePullback_exists D E f.left t.left (congrArg Over.Hom.left w)
    o.left (congrArg Over.Hom.left h₀) (congrArg Over.Hom.left h₁) hc
  refine ⟨((adj f.left).homEquiv _ _).symm α, ?_⟩
  unfold IsAdjointPull
  rwa [Equiv.apply_symm_apply]

private theorem insertUnit_natural (G : Grp (SchemeOverRing A))
    {K L : SchemeOverRing A} (f : K ⟶ L) :
    insertUnit G K ≫ (G.X ◁ f) = f ≫ insertUnit G L := by
  unfold insertUnit
  rw [lift_whiskerLeft, comp_lift, Category.id_comp, Category.comp_id, ← Category.assoc]
  rw [Subsingleton.elim (f ≫ toUnit L) (toUnit K)]

private theorem insertUnit_isPullback (G : Grp (SchemeOverRing A))
    {K L : SchemeOverRing A} (q : K ⟶ L) :
    IsPullback (insertUnit G K) q (G.X ◁ q) (insertUnit G L) := by
  apply IsPullback.of_right _ (insertUnit_natural G q) (whiskerLeft_isPullback G.X q)
  have h (Z : SchemeOverRing A) : insertUnit G Z ≫ snd G.X Z = 𝟙 Z := lift_snd _ _
  rw [h, h]
  exact IsPullback.of_id_fst

private def unitChange (G : Grp (SchemeOverRing A)) (D : CovarianceData X) :
    CartesianChange (productData G.X D) D (insertUnit G X).left where
  torsorMap := (insertUnit G D.torsor).left
  overlapMap := (insertUnit G D.overlap).left
  torsorSquare := (Over.forget _).map_isPullback (insertUnit_isPullback G D.projection)
  overlapSquare := (Over.forget _).map_isPullback (insertUnit_isPullback G D.overlapProjection)
  first_eq := congrArg Over.Hom.left (insertUnit_natural G D.first)
  second_eq := congrArg Over.Hom.left (insertUnit_natural G D.second)
  multiplier_eq := by
    change (insertUnit G D.overlap).left.appTop ((snd G.X D.overlap).left.appTop D.multiplier) = _
    rw [← appTop_comp_apply, ← Over.comp_left, show insertUnit G D.overlap ≫ snd G.X D.overlap =
      𝟙 D.overlap from lift_snd _ _]
    rfl

private theorem combineGroup_natural (G : Grp (SchemeOverRing A))
    {K L : SchemeOverRing A} (f : K ⟶ L) :
    combineGroup G K ≫ (G.X ◁ f) = (G.X ◁ (G.X ◁ f)) ≫ combineGroup G L := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, whiskerLeft_fst, combineGroup, lift_fst,
      MonObj.comp_mul, whiskerLeft_snd_assoc]
  · simp only [Category.assoc, whiskerLeft_snd, combineGroup, lift_snd, lift_snd_assoc,
      whiskerLeft_snd_assoc]

private theorem combine_pull (G : Grp (SchemeOverRing A)) (D : CovarianceData X) :
    ∃ e : (Scheme.Modules.pullback (combineGroup G X).left).obj (productData G.X D).sheaf ⟶
      (productData G.X (productData G.X D)).sheaf,
      IsAdjointPull (congrArg Over.Hom.left (combineGroup_natural G D.projection)) e := by
  apply pull_of_maps (D := productData G.X D) (E := productData G.X (productData G.X D))
    (combineGroup G X) (combineGroup G D.torsor) (combineGroup G D.overlap)
    (combineGroup_natural G D.projection) (combineGroup_natural G D.first)
    (combineGroup_natural G D.second)
  change (combineGroup G D.overlap).left.appTop ((snd G.X D.overlap).left.appTop D.multiplier) =
    (snd G.X (G.X ⊗ D.overlap)).left.appTop ((snd G.X D.overlap).left.appTop D.multiplier)
  rw [← appTop_comp_apply, ← appTop_comp_apply, ← Over.comp_left, ← Over.comp_left,
    show combineGroup G D.overlap ≫ snd G.X D.overlap =
      snd G.X (G.X ⊗ D.overlap) ≫ snd G.X D.overlap from lift_snd _ _]

private theorem successive_pull (T : Torsor A) (a : ModObj T.group.X T.quotient)
    (ha : μ[T.group.X] ≫ T.projection = (𝟙 T.group.X ⊗ₘ T.projection) ≫ T.leftAction a) :
    ∃ e : (Scheme.Modules.pullback (T.group.X ◁ T.leftAction a).left).obj T.actionLineData.sheaf ⟶
      (productData T.group.X T.actionLineData).sheaf,
      IsAdjointPull (congrArg Over.Hom.left (show
        (T.group.X ◁ μ[T.group.X]) ≫ T.actionLineData.projection =
          (productData T.group.X T.actionLineData).projection ≫ (T.group.X ◁ T.leftAction a) by
            change (T.group.X ◁ μ[T.group.X]) ≫ (T.group.X ◁ T.projection) =
              (T.group.X ◁ (T.group.X ◁ T.projection)) ≫ (T.group.X ◁ T.leftAction a)
            rw [← whiskerLeft_comp, ← whiskerLeft_comp]
            exact congrArg (T.group.X ◁ ·) ha)) e := by
  let G := T.group.X
  apply pull_of_maps (D := T.actionLineData) (E := productData G T.actionLineData)
    (G ◁ T.leftAction a) (G ◁ μ[G]) (G ◁ translateOverlap T)
  · change (G ◁ μ[G]) ≫ (G ◁ T.projection) =
      (G ◁ (G ◁ T.projection)) ≫ (G ◁ T.leftAction a)
    rw [← whiskerLeft_comp, ← whiskerLeft_comp]
    exact congrArg (G ◁ ·) ha
  · change (G ◁ translateOverlap T) ≫ (G ◁ T.lineData.first) =
      (G ◁ T.actionLineData.first) ≫ (G ◁ μ[G])
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, translateOverlap_first]
  · change (G ◁ translateOverlap T) ≫ (G ◁ T.lineData.second) =
      (G ◁ T.actionLineData.second) ≫ (G ◁ μ[G])
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, translateOverlap_second]
  · change (G ◁ translateOverlap T).left.appTop
        ((snd G T.lineData.overlap).left.appTop T.lineData.multiplier) =
      (snd G T.actionLineData.overlap).left.appTop T.actionLineData.multiplier
    rw [← appTop_comp_apply, ← Over.comp_left, whiskerLeft_snd, Over.comp_left,
      appTop_comp_apply, translateOverlap_multiplier]

private def parameterProjection (W : SchemeOverRing A) (D : CovarianceData X) :
    CartesianChange D (productData W D) (snd W X).left where
  torsorMap := (snd W D.torsor).left
  overlapMap := (snd W D.overlap).left
  torsorSquare := (Over.forget _).map_isPullback (whiskerLeft_isPullback W D.projection)
  overlapSquare := (Over.forget _).map_isPullback (whiskerLeft_isPullback W D.overlapProjection)
  first_eq := congrArg Over.Hom.left (whiskerLeft_snd _ _).symm
  second_eq := congrArg Over.Hom.left (whiskerLeft_snd _ _).symm
  multiplier_eq := rfl

private theorem change_cocycle {D : CovarianceData X} {E : CovarianceData Y}
    {f : Y.left ⟶ X.left} (C : CartesianChange D E f) (h : Cocycle D) : Cocycle E := by
  refine ⟨C.multiplier_eq ▸ h.unit.map C.overlapMap.appTop.hom, ?_⟩
  intro S a b c hab hac hbc
  rw [← C.multiplier_eq, ← appTop_comp_apply, ← appTop_comp_apply, ← appTop_comp_apply]
  exact h.mul (a ≫ C.overlapMap) (b ≫ C.overlapMap) (c ≫ C.overlapMap)
    (by rw [Category.assoc, Category.assoc, C.first_eq, C.second_eq, ← Category.assoc,
      ← Category.assoc, hab])
    (by rw [Category.assoc, Category.assoc, C.first_eq, ← Category.assoc,
      ← Category.assoc, hac])
    (by rw [Category.assoc, Category.assoc, C.second_eq, ← Category.assoc,
      ← Category.assoc, hbc])

private theorem parameterComparison (T : Torsor A) {Y : SchemeOverRing B}
    {E : CovarianceData Y} {f : Y.left ⟶ (T.group.X ⊗ T.quotient).left}
    (K : CartesianChange T.actionLineData E f) : K.HasComparison := by
  let C := projectionChange T
  apply (comparison_of_charts K (change_kernelPair C (right_kernelPair T))
    (change_cocycle C (right_cocycle T)) ?_).1
  intro y
  let p := (snd T.group.X T.quotient).left
  obtain ⟨U, hU, s, hs⟩ := T.localSections (p y)
  exact ⟨p ⁻¹ᵁ U, hU, change_local_section C U s hs⟩

private theorem insertUnit_action (G : Grp (SchemeOverRing A)) {K : SchemeOverRing A}
    (a : ModObj G.X K) : insertUnit G K ≫ a.smul = 𝟙 K := by
  let : ModObj G.X K := a
  exact one_smul (K ⟶ G.X) (𝟙 K : K ⟶ K)

private theorem combine_action (G : Grp (SchemeOverRing A)) {K : SchemeOverRing A}
    (a : ModObj G.X K) : combineGroup G K ≫ a.smul = (G.X ◁ a.smul) ≫ a.smul := by
  let : ModObj G.X K := a
  let x := fst G.X (G.X ⊗ K)
  let y := snd G.X (G.X ⊗ K) ≫ fst G.X K
  let z := snd G.X (G.X ⊗ K) ≫ snd G.X K
  have hy : lift y z = snd G.X (G.X ⊗ K) := lift_comp_fst_snd _
  have he : G.X ◁ a.smul = lift x (y • z) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [whiskerLeft_fst, lift_fst]
      rfl
    · rw [whiskerLeft_snd, lift_snd]
      change _ = lift y z ≫ a.smul
      rw [hy]
      rfl
  rw [he]
  exact mul_smul x y z

private theorem compare_composites {C : Type u} [Category C]
    {Va Vp Ua Up Ta Tp W : C}
    (v : Va ⟶ Vp) (u : Ua ⟶ Up) (t : Ta ⟶ Tp)
    (c₁ : Va ⟶ Ua) (c₂ : Up ⟶ Ta) (c₃ : Tp ⟶ Vp)
    (pv : Vp ⟶ W) (pu : Up ⟶ W) (pt : Tp ⟶ W)
    (mono : Mono pv)
    (h₁ : v ≫ pv = c₁ ≫ u ≫ pu)
    (h₂ : pu = c₂ ≫ t ≫ pt) (h₃ : pt = c₃ ≫ pv) :
    v = c₁ ≫ u ≫ c₂ ≫ t ≫ c₃ := by
  apply (cancel_mono pv).mp
  rw [h₁, h₂, h₃]
  simp only [Category.assoc]

/-- An equality of the two composites into a common line gives the identity
of the comparison after reindexing along the unit. -/
private theorem reindexed_unit {P Q R : Scheme.{u}}
    {L : P.Modules} {M : Q.Modules} {N : R.Modules}
    {a p : Q ⟶ P} {j : R ⟶ Q} (h : j ≫ a = j ≫ p)
    (ea : (Scheme.Modules.pullback a).obj L ≅ M) (ep : (Scheme.Modules.pullback p).obj L ≅ M)
    (k : (Scheme.Modules.pullback j).obj M ≅ N)
    (w : composePull j a ea.hom k.hom =
      (pullbackCongr h).hom.app L ≫ composePull j p ep.hom k.hom) :
    pullbackComparison L j a p (ea.hom ≫ ep.inv) = (pullbackCongr h).hom.app L := by
  have : IsIso (composePull j p ep.hom k.hom) := by
    dsimp only [composePull]
    infer_instance
  apply (cancel_mono (composePull j p ep.hom k.hom)).mp
  exact (reindex_composePull j a p ea.hom ep k.hom).trans w

/-- Compare the reindexed identifications by mapping into the common line. -/
private theorem reindexed_cocycle {P Q R : Scheme.{u}}
    {L : P.Modules} {M : Q.Modules} {N : R.Modules}
    {a p : Q ⟶ P} {v u t : R ⟶ Q}
    (ha : v ≫ a = u ≫ a) (hm : u ≫ p = t ≫ a) (hp : t ≫ p = v ≫ p)
    (ea : (Scheme.Modules.pullback a).obj L ≅ M) (ep : (Scheme.Modules.pullback p).obj L ≅ M)
    (kv : (Scheme.Modules.pullback v).obj M ⟶ N) (ku : (Scheme.Modules.pullback u).obj M ⟶ N)
    (kt : (Scheme.Modules.pullback t).obj M ≅ N)
    (wv : composePull v a ea.hom kv =
      (pullbackCongr ha).hom.app L ≫ composePull u a ea.hom ku)
    (wu : composePull u p ep.hom ku =
      (pullbackCongr hm).hom.app L ≫ composePull t a ea.hom kt.hom)
    (wt : composePull t p ep.hom kt.hom =
      (pullbackCongr hp).hom.app L ≫ composePull v p ep.hom kv) :
    SuccessiveComparison L a p v u t (ea.hom ≫ ep.inv) ha hm hp := by
  unfold SuccessiveComparison
  have : IsIso (composePull t p ep.hom kt.hom) := by
    dsimp only [composePull]
    infer_instance
  have : IsIso (composePull v p ep.hom kv) :=
    IsIso.of_isIso_fac_left wt.symm
  have hv := reindex_composePull v a p ea.hom ep kv
  have hu := reindex_composePull u a p ea.hom ep ku
  have ht := reindex_composePull t a p ea.hom ep kt.hom
  exact compare_composites _ _ _ _ _ _ _ _ _ inferInstance
    (hv.trans (wv.trans (congrArg ((pullbackCongr ha).hom.app L ≫ ·) hu.symm)))
    (wu.trans (congrArg ((pullbackCongr hm).hom.app L ≫ ·) ht.symm)) wt

private theorem adjoint_composites_eq
    {Z : SchemeOverRing A}
    (D : CovarianceData X) (E : CovarianceData Y) (F : CovarianceData Z)
    (f f' : Y.left ⟶ X.left) (j j' : Z.left ⟶ Y.left)
    (t t' : E.torsor.left ⟶ D.torsor.left) (s s' : F.torsor.left ⟶ E.torsor.left)
    (hf : j ≫ f = j' ≫ f') (ht : s ≫ t = s' ≫ t')
    {wf : t ≫ D.projection.left = E.projection.left ≫ f}
    {wf' : t' ≫ D.projection.left = E.projection.left ≫ f'}
    {wj : s ≫ E.projection.left = F.projection.left ≫ j}
    {wj' : s' ≫ E.projection.left = F.projection.left ≫ j'}
    {e : (Scheme.Modules.pullback f).obj D.sheaf ⟶ E.sheaf}
    {e' : (Scheme.Modules.pullback f').obj D.sheaf ⟶ E.sheaf}
    {k : (Scheme.Modules.pullback j).obj E.sheaf ⟶ F.sheaf}
    {k' : (Scheme.Modules.pullback j').obj E.sheaf ⟶ F.sheaf}
    (he : IsAdjointPull wf e) (he' : IsAdjointPull wf' e')
    (hk : IsAdjointPull wj k) (hk' : IsAdjointPull wj' k') :
    composePull j f e k = (pullbackCongr hf).hom.app D.sheaf ≫ composePull j' f' e' k' :=
  adjointPull_eq (D := D) (E := F) hf ht
    (adjointPull_comp (D := D) (E := E) (F := F) he hk)
    (adjointPull_comp (D := D) (E := E) (F := F) he' hk')

/-- The comparisons compose when the corresponding maps on both schemes
compose. The three equalities on the torsor lift those on the base. -/
private theorem covariance_comparison_cocycle
    {Z : SchemeOverRing A}
    (D : CovarianceData X) (E : CovarianceData Y) (F : CovarianceData Z)
    (a p : Y.left ⟶ X.left) (v u t : Z.left ⟶ Y.left)
    (m s : E.torsor.left ⟶ D.torsor.left)
    (v' u' t' : F.torsor.left ⟶ E.torsor.left)
    (hva : v ≫ a = u ≫ a) (hup : u ≫ p = t ≫ a) (htp : t ≫ p = v ≫ p)
    (hvm : v' ≫ m = u' ≫ m) (hus : u' ≫ s = t' ≫ m) (hts : t' ≫ s = v' ≫ s)
    (ea : (Scheme.Modules.pullback a).obj D.sheaf ≅ E.sheaf)
    (ep : (Scheme.Modules.pullback p).obj D.sheaf ≅ E.sheaf)
    (kv : (Scheme.Modules.pullback v).obj E.sheaf ⟶ F.sheaf)
    (ku : (Scheme.Modules.pullback u).obj E.sheaf ⟶ F.sheaf)
    (kt : (Scheme.Modules.pullback t).obj E.sheaf ≅ F.sheaf)
    {wa : m ≫ D.projection.left = E.projection.left ≫ a}
    {wp : s ≫ D.projection.left = E.projection.left ≫ p}
    {wv : v' ≫ E.projection.left = F.projection.left ≫ v}
    {wu : u' ≫ E.projection.left = F.projection.left ≫ u}
    {wt : t' ≫ E.projection.left = F.projection.left ≫ t}
    (eaAdj : IsAdjointPull wa ea.hom) (epAdj : IsAdjointPull wp ep.hom)
    (kvAdj : IsAdjointPull wv kv) (kuAdj : IsAdjointPull wu ku) (ktAdj : IsAdjointPull wt kt.hom) :
    SuccessiveComparison D.sheaf a p v u t (ea.hom ≫ ep.inv) hva hup htp := by
  refine reindexed_cocycle (P := X.left) (Q := Y.left) (R := Z.left) hva hup htp ea ep kv ku kt ?_ ?_ ?_
  · exact adjoint_composites_eq D E F a a v u m m v' u' hva hvm eaAdj eaAdj kvAdj kuAdj
  · exact adjoint_composites_eq D E F p a u t s m u' t' hup hus epAdj eaAdj kuAdj ktAdj
  · exact adjoint_composites_eq D E F p p t v s s t' v' htp hts epAdj epAdj ktAdj kvAdj

private theorem translation_unit (T : Torsor A) (a : ModObj T.group.X T.quotient)
    (ha : μ[T.group.X] ≫ T.projection = (𝟙 T.group.X ⊗ₘ T.projection) ≫ T.leftAction a)
    (ea : (Scheme.Modules.pullback (T.leftAction a).left).obj T.line ≅ T.actionLineData.sheaf)
    (ep : (Scheme.Modules.pullback (snd T.group.X T.quotient).left).obj T.line ≅
      T.actionLineData.sheaf)
    (hea : IsAdjointPull (actionChange T a ha).torsorSquare.w ea.hom)
    (hep : IsAdjointPull (projectionChange T).torsorSquare.w ep.hom) :
    let j := (insertUnit T.group T.quotient).left
    let p := (snd T.group.X T.quotient).left
    ∀ hj : j ≫ (T.leftAction a).left = j ≫ p,
      pullbackComparison T.line j (T.leftAction a).left p (ea.hom ≫ ep.inv) =
        (pullbackCongr hj).hom.app T.line := by
  intro j p hj
  let G := T.group.X
  let D := T.lineData
  let E := T.actionLineData
  let j' := (insertUnit T.group G).left
  let m := μ[G].left
  let s := (snd G G).left
  have hjm : j' ≫ m = 𝟙 G.left :=
    congrArg Over.Hom.left (insertUnit_action T.group (ModObj.regular G))
  have hjs : j' ≫ s = 𝟙 G.left := congrArg Over.Hom.left (lift_snd _ _)
  obtain ⟨k, hk⟩ := parameterComparison T (unitChange T.group D)
  change IsAdjointPull (D := E) (E := D) (f := j) (t := j') _ k.hom at hk
  have h := adjoint_composites_eq D E D (T.leftAction a).left p j j m s j' j'
    hj (hjm.trans hjs.symm) hea hep hk hk
  exact reindexed_unit hj ea ep k h

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.implicitBump false in
private theorem translation_product (T : Torsor A) (a : ModObj T.group.X T.quotient)
    (ha : μ[T.group.X] ≫ T.projection = (𝟙 T.group.X ⊗ₘ T.projection) ≫ T.leftAction a)
    (ea : (Scheme.Modules.pullback (T.leftAction a).left).obj T.line ≅ T.actionLineData.sheaf)
    (ep : (Scheme.Modules.pullback (snd T.group.X T.quotient).left).obj T.line ≅
      T.actionLineData.sheaf)
    (hea : IsAdjointPull (actionChange T a ha).torsorSquare.w ea.hom)
    (hep : IsAdjointPull (projectionChange T).torsorSquare.w ep.hom) :
    let G := T.group.X
    let Q := T.quotient
    let p := (snd G Q).left
    let u := (G ◁ T.leftAction a).left
    let t := (snd G (G ⊗ Q)).left
    let v := (combineGroup T.group Q).left
    ∀ (hva : v ≫ (T.leftAction a).left = u ≫ (T.leftAction a).left)
      (hup : u ≫ p = t ≫ (T.leftAction a).left) (htp : t ≫ p = v ≫ p),
      SuccessiveComparison T.line (T.leftAction a).left p v u t
        (ea.hom ≫ ep.inv) hva hup htp := by
  intro G Q p u t v hva hup htp
  let D := T.lineData
  let E := T.actionLineData
  let F := productData G E
  let a₀ := (T.leftAction a).left
  let m := μ[G].left
  let s := (snd G G).left
  let u' := (G ◁ μ[G]).left
  let t' := (snd G (G ⊗ G)).left
  let v' := (combineGroup T.group G).left
  have hvm : v' ≫ m = u' ≫ m :=
    congrArg Over.Hom.left (combine_action T.group (ModObj.regular G))
  have hus : u' ≫ s = t' ≫ m := congrArg Over.Hom.left (whiskerLeft_snd _ _)
  have hts : t' ≫ s = v' ≫ s := (congrArg Over.Hom.left
    (show combineGroup T.group G ≫ snd G G = snd G (G ⊗ G) ≫ snd G G from lift_snd _ _)).symm
  obtain ⟨ku, hku⟩ := successive_pull T a ha
  obtain ⟨kv, hkv⟩ := combine_pull T.group D
  obtain ⟨kt, hkt⟩ := parameterComparison T (parameterProjection G E)
  change IsAdjointPull (D := E) (E := F) (f := u) (t := u') _ ku at hku
  change IsAdjointPull (D := E) (E := F) (f := v) (t := v') _ kv at hkv
  change IsAdjointPull (D := E) (E := F) (f := t) (t := t') _ kt.hom at hkt
  exact covariance_comparison_cocycle (X := Q) (Y := G ⊗ Q) (Z := G ⊗ (G ⊗ Q))
    D E F a₀ p v u t m s v' u' t' hva hup htp hvm hus hts ea ep kv ku kt hea hep hkv hku hkt

private theorem translation_cocycle (T : Torsor A) (a : ModObj T.group.X T.quotient)
    (ha : μ[T.group.X] ≫ T.projection = (𝟙 T.group.X ⊗ₘ T.projection) ≫ T.leftAction a)
    (ea : (Scheme.Modules.pullback (T.leftAction a).left).obj T.line ≅ T.actionLineData.sheaf)
    (ep : (Scheme.Modules.pullback (snd T.group.X T.quotient).left).obj T.line ≅
      T.actionLineData.sheaf)
    (hea : IsAdjointPull (actionChange T a ha).torsorSquare.w ea.hom)
    (hep : IsAdjointPull (projectionChange T).torsorSquare.w ep.hom) :
    T.HasLineCocycle a (ea.hom ≫ ep.inv) := by
  let G := T.group.X
  let Q := T.quotient
  let a₀ := (T.leftAction a).left
  let p := (snd G Q).left
  let j := (insertUnit T.group Q).left
  let u := (G ◁ T.leftAction a).left
  let t := (snd G (G ⊗ Q)).left
  let v := (combineGroup T.group Q).left
  have hja : j ≫ a₀ = 𝟙 Q.left := congrArg Over.Hom.left (insertUnit_action T.group a)
  have hjp : j ≫ p = 𝟙 Q.left := congrArg Over.Hom.left (lift_snd _ _)
  have hj : j ≫ a₀ = j ≫ p := hja.trans hjp.symm
  have hva : v ≫ a₀ = u ≫ a₀ := congrArg Over.Hom.left (combine_action T.group a)
  have hup : u ≫ p = t ≫ a₀ := congrArg Over.Hom.left (whiskerLeft_snd _ _)
  have htp : t ≫ p = v ≫ p := (congrArg Over.Hom.left
    (show combineGroup T.group Q ≫ snd G Q = snd G (G ⊗ Q) ≫ snd G Q from lift_snd _ _)).symm
  exact ⟨hj, hva, hup, htp, translation_unit T a ha ea ep hea hep hj,
    translation_product T a ha ea ep hea hep hva hup htp⟩

/-- Left multiplication gives a linearization of the same kernel line,
with the identity and the two-translation cocycle. -/
theorem equivariantLine : EquivariantLine.{u} := by
  intro A _ T a ha
  let ca := actionChange T a ha
  let cp := projectionChange T
  obtain ⟨ea, hea⟩ := (cartesianComparison A A T _ _ ca).1
  obtain ⟨ep, hep⟩ := (cartesianComparison A A T _ _ cp).1
  exact ⟨ca.torsorSquare.w, cp.torsorSquare.w, ea, ep, hea, hep,
    translation_cocycle T a ha ea ep hea hep⟩

end ActionCoherence

end
end LinearAlgebraicGroups.Representation.RelativeCovarianceLine
