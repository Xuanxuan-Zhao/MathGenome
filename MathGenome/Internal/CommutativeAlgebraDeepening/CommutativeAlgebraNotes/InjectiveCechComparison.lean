import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.InjectiveCechComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.AugmentedCechComplex
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.BoundedAboveFlatTensor
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalizationOfInjectives
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.TorsionOfInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.InjectiveCechComparison
  (singleZero factorProjection dropFactor projection)
open Cech (Complex)

universe u
variable {R : Type u} [CommRing R]

private abbrev principal (r : R) : Ideal R := Ideal.span {r}
private abbrev generators (rs : List R) : Ideal R := Ideal.span {r | r ∈ rs}
private abbrev T (I : Ideal R) (M : ModuleCat.{u} R) :=
  ModuleCat.of R (idealTorsion I M)
private abbrev incl (I : Ideal R) (M : ModuleCat.{u} R) : T I M ⟶ M :=
  ModuleCat.ofHom (idealTorsion I M).subtype

-- A common power of the sum can be computed from separate annihilating powers.
private theorem mem_torsion_sup (I J : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
    (x : M) :
    x ∈ idealTorsion (I ⊔ J) M ↔ x ∈ idealTorsion I M ∧ x ∈ idealTorsion J M := by
  simp only [mem_idealTorsion]
  constructor
  · rintro ⟨n, hn, hx⟩
    exact ⟨⟨n, hn, fun a ha => hx a ((show I ^ n ≤ (I ⊔ J) ^ n from pow_le_pow_left' le_sup_left n) ha)⟩,
      ⟨n, hn, fun a ha => hx a ((show J ^ n ≤ (I ⊔ J) ^ n from pow_le_pow_left' le_sup_right n) ha)⟩⟩
  · rintro ⟨⟨n, hn, hx⟩, ⟨m, hm, hy⟩⟩
    refine ⟨n + m, by omega, fun a ha => ?_⟩
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp
      (Ideal.sup_pow_add_le_pow_sup_pow ha)
    rw [add_smul, hx b hb, hy c hc, add_zero]

private theorem generators_cons (r : R) (rs : List R) :
    generators (r :: rs) = principal r ⊔ generators rs := by
  change Ideal.span {a | a ∈ r :: rs} = _
  simp only [List.mem_cons]
  exact Ideal.span_insert r _

private theorem mem_torsion_submodule (I : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
    (S : Submodule R M) (x : S) :
    x ∈ idealTorsion I S ↔ (x : M) ∈ idealTorsion I M := by
  simp only [mem_idealTorsion]
  constructor
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, fun a ha => (Submodule.coe_eq_zero (p := S)).mpr (hx a ha)⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, fun a ha => (Submodule.coe_eq_zero (p := S)).mp (hx a ha)⟩

private def torsionRestrict (I J : Ideal R) {M : Type u} [AddCommGroup M] [Module R M] :
    idealTorsion (I ⊔ J) M →ₗ[R] idealTorsion J M :=
  (idealTorsion (I ⊔ J) M).subtype.codRestrict (idealTorsion J M)
    (fun x => ((mem_torsion_sup I J x.val).mp x.property).2)

private theorem torsionRestrict_val (I J : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
    (x : idealTorsion (I ⊔ J) M) : (torsionRestrict I J x).val = x.val :=
  (LinearMap.codRestrict_apply (idealTorsion J M) (idealTorsion (I ⊔ J) M).subtype x).trans rfl

private theorem torsionRestrict_mem (I J : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
    (x : idealTorsion (I ⊔ J) M) :
    torsionRestrict I J x ∈ idealTorsion I (idealTorsion J M) := by
  rw [mem_torsion_submodule, torsionRestrict_val]
  exact ((mem_torsion_sup I J x.val).mp x.property).1

private def torsionSupMap (I J : Ideal R) {M : Type u} [AddCommGroup M] [Module R M] :
    idealTorsion (I ⊔ J) M →ₗ[R] idealTorsion I (idealTorsion J M) :=
  (torsionRestrict I J).codRestrict _ (torsionRestrict_mem I J)

private theorem torsionSupMap_val (I J : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]
    (x : idealTorsion (I ⊔ J) M) : (torsionSupMap I J x).val.val = x.val := by
  unfold torsionSupMap
  rw [LinearMap.codRestrict_apply, torsionRestrict_val]

private theorem torsionSupMap_bijective (I J : Ideal R)
    {M : Type u} [AddCommGroup M] [Module R M] :
    Function.Bijective (torsionSupMap I J (M := M)) := by
  constructor
  · intro x y h
    apply Subtype.val_injective
    simpa only [torsionSupMap_val] using
      congrArg (fun z : idealTorsion I (idealTorsion J M) => z.val.val) h
  · intro y
    refine ⟨⟨y.val.val, (mem_torsion_sup I J y.val.val).mpr
      ⟨(mem_torsion_submodule I _ y.val).mp y.property, y.val.property⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

private def torsionSupHom (I J : Ideal R) (M : ModuleCat.{u} R) :
    T (I ⊔ J) M ⟶ T I (T J M) :=
  ModuleCat.ofHom (torsionSupMap I J)

private theorem torsionSupHom_isIso (I J : Ideal R) (M : ModuleCat.{u} R) :
    IsIso (torsionSupHom I J M) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (torsionSupMap_bijective (M := M) I J)

private noncomputable def torsionSupIso (I J : Ideal R) (M : ModuleCat.{u} R) :
    T (I ⊔ J) M ≅ T I (T J M) := by
  letI := torsionSupHom_isIso I J M
  exact asIso (torsionSupHom I J M)

private theorem torsionSupHom_apply (I J : Ideal R) (M : ModuleCat.{u} R)
    (x : T (I ⊔ J) M) :
    torsionSupHom I J M x = torsionSupMap I J x :=
  ModuleCat.ofHom_apply (torsionSupMap I J) x

private theorem incl_apply (I : Ideal R) (M : ModuleCat.{u} R) (x : T I M) :
    incl I M x = x.val :=
  ModuleCat.ofHom_apply (idealTorsion I M).subtype x

private theorem torsionSupIso_incl (I J : Ideal R) (M : ModuleCat.{u} R) :
    (torsionSupIso I J M).hom ≫ incl I (T J M) ≫ incl J M = incl (I ⊔ J) M := by
  change torsionSupHom I J M ≫ incl I (T J M) ≫ incl J M = incl (I ⊔ J) M
  apply ConcreteCategory.hom_ext
  intro x
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, torsionSupHom_apply,
    incl_apply I, incl_apply J, incl_apply (I ⊔ J)]
  exact torsionSupMap_val I J x

private noncomputable def torsionConsIso (r : R) (rs : List R) (M : ModuleCat.{u} R) :
    T (generators (r :: rs)) M ≅ T (principal r) (T (generators rs) M) :=
  eqToIso (congrArg (fun I => T I M) (generators_cons r rs)) ≪≫
    torsionSupIso (principal r) (generators rs) M

private theorem torsion_eqToHom_incl {I J : Ideal R} (h : I = J) (M : ModuleCat.{u} R) :
    eqToHom (congrArg (fun K => T K M) h) ≫ incl J M = incl I M := by
  cases h
  exact Category.id_comp _

private theorem torsionConsIso_incl (r : R) (rs : List R) (M : ModuleCat.{u} R) :
    (torsionConsIso r rs M).hom ≫ incl (principal r) (T (generators rs) M) ≫
        incl (generators rs) M = incl (generators (r :: rs)) M := by
  change (eqToHom (congrArg (fun I => T I M) (generators_cons r rs)) ≫
    (torsionSupIso (principal r) (generators rs) M).hom) ≫ _ ≫ _ = _
  rw [Category.assoc, torsionSupIso_incl]
  exact torsion_eqToHom_incl (generators_cons r rs) M

private theorem torsion_nil_isIso (M : ModuleCat.{u} R) : IsIso (incl (generators []) M) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨Subtype.val_injective, fun x => ⟨⟨x, ?_⟩, rfl⟩⟩
  apply (mem_idealTorsion _ _).mpr
  refine ⟨1, le_rfl, fun a ha => ?_⟩
  have : a = 0 := by simpa [generators] using ha
  simp [this]

open private tensorCofanIsColimit restrictCofanIsColimit
  tensor_isZero_left tensor_isZero_right factor_flat factor_d_zero_one
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.AugmentedCechComplex

-- A tensor diagonal with all other summands zero is identified by its inclusion.
private theorem tensorInclusion_isIso (A B : Complex R) (i j k : ℤ) (h : i + j = k)
    (hz : ∀ p q : ℤ, p + q = k → (p ≠ i ∨ q ≠ j) → IsZero (A.X p ⊗ B.X q)) :
    IsIso (ιTensorObj A B i j k h) := by
  let e : Unit ↪ { pq : ℤ × ℤ // pq.1 + pq.2 = k } :=
    ⟨fun _ => ⟨(i, j), h⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  have he (pq : { pq : ℤ × ℤ // pq.1 + pq.2 = k })
      (hne : ∀ b, e b ≠ pq) : IsZero (A.X pq.val.1 ⊗ B.X pq.val.2) := by
    apply hz _ _ pq.property
    rcases pq with ⟨⟨p, q⟩, hpq⟩
    by_cases hp : p = i
    · subst p
      exact Or.inr (fun hq => by change q = j at hq; subst q; exact hne () rfl)
    · exact Or.inl hp
  let hc := restrictCofanIsColimit _ (tensorCofanIsColimit A B k) e he
  let P := A.X i ⊗ B.X j
  let c := Cofan.mk P (fun _ : Unit => 𝟙 P)
  have hc' : IsColimit c := by
    refine Cofan.IsColimit.mk _ (fun t => t.inj ()) ?_ ?_
    · rintro t ⟨⟩
      exact Category.id_comp _
    · intro t f hf
      exact (Category.id_comp f).symm.trans (hf ())
  let iso : A.X i ⊗ B.X j ≅ (A ⊗ B).X k := hc'.coconePointUniqueUpToIso hc
  have hι : ιTensorObj A B i j k h = iso.hom := by
    have hh := hc'.comp_coconePointUniqueUpToIso_hom hc (Discrete.mk ())
    change 𝟙 P ≫ iso.hom = ιTensorObj A B i j k h at hh
    rw [Category.id_comp] at hh
    exact hh.symm
  rw [hι]
  exact iso.isIso_hom

private theorem tensorZeroInclusion_isIso (A B : Complex R)
    (hA : ∀ i < 0, IsZero (A.X i)) (hB : ∀ i < 0, IsZero (B.X i)) :
    IsIso (ιTensorObj A B 0 0 0 rfl) := by
  refine tensorInclusion_isIso A B 0 0 0 rfl fun p q h hpq => ?_
  by_cases hp : p < 0
  · exact tensor_isZero_left (hA p hp)
  · exact tensor_isZero_right (hB q (by omega))

private instance singleTensorInclusion_isIso (A : Complex R) (M : ModuleCat.{u} R)
    (i : ℤ) : IsIso (ιTensorObj A ((singleZero R).obj M) i 0 i (add_zero i)) := by
  refine tensorInclusion_isIso A _ i 0 i (add_zero i) fun p q h hpq => ?_
  exact tensor_isZero_right (isZero_single_obj_X (.up ℤ) 0 M q (by omega))

private noncomputable def singleTensorTerm (A : Complex R) (M : ModuleCat.{u} R) (i : ℤ) :
    A.X i ⊗ M ≅ (A ⊗ (singleZero R).obj M).X i :=
  asIso (ιTensorObj A ((singleZero R).obj M) i 0 i (add_zero i))

private theorem factor_isZero_neg (r : R) (i : ℤ) (hi : i < 0) : IsZero ((Cech.factor r).X i) :=
  Cech.factor_isZero r i (by omega) (by omega)

private theorem single_isZero_neg (M : ModuleCat.{u} R) (i : ℤ) (hi : i < 0) :
    IsZero (((singleZero R).obj M).X i) :=
  isZero_single_obj_X _ _ _ _ (by omega)

private theorem coefficients_isZero_neg (rs : List R) (M : ModuleCat.{u} R) (i : ℤ) (hi : i < 0) :
    IsZero ((cechCoefficients rs M).X i) :=
  IsZero.of_iso (tensor_isZero_left (Cech.isZero_X rs i (.inl hi)))
    (singleTensorTerm (CechComplex rs) M i).symm

private theorem factorProjection_f_zero (r : R) :
    (factorProjection r).f 0 = (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv := by
  simp [factorProjection]

private theorem dropFactor_zero_isIso (r : R) (K : Complex R)
    (hK : ∀ i < 0, IsZero (K.X i)) : IsIso ((dropFactor r K).f 0) := by
  let U := tensorUnit (ModuleCat.{u} R) (.up ℤ)
  have := tensorZeroInclusion_isIso (Cech.factor r) K (factor_isZero_neg r) hK
  have := tensorZeroInclusion_isIso U K (single_isZero_neg _) hK
  have h :
      ιTensorObj (Cech.factor r) K 0 0 0 rfl ≫ ((factorProjection r ⊗ₘ 𝟙 K).f 0) =
        ((factorProjection r).f 0 ▷ K.X 0) ≫ ιTensorObj U K 0 0 0 rfl := by
    change _ ≫ (HomologicalComplex.tensorHom (factorProjection r) (𝟙 K)).f 0 = _
    rw [ι_mapBifunctorMap]
    change ((factorProjection r).f 0 ▷ K.X 0) ≫
      (U.X 0 ◁ 𝟙 (K.X 0)) ≫ ιTensorObj U K 0 0 0 rfl = _
    rw [whiskerLeft_id, Category.id_comp]
  have : IsIso ((factorProjection r).f 0) := by
    rw [factorProjection_f_zero]
    infer_instance
  have : IsIso (((factorProjection r ⊗ₘ 𝟙 K).f 0)) := by
    have : IsIso (((factorProjection r).f 0 ▷ K.X 0) ≫ ιTensorObj U K 0 0 0 rfl) := by
      infer_instance
    rw [← h] at this
    exact IsIso.of_isIso_comp_left (ιTensorObj (Cech.factor r) K 0 0 0 rfl) _
  change IsIso ((factorProjection r ⊗ₘ 𝟙 K).f 0 ≫ (λ_ K).hom.f 0)
  infer_instance

theorem cechProjection_degreeZero :
    Specs.CommutativeAlgebraNotes.InjectiveCechComparison.ProjectionDegreeZero.{u} := by
  intro R _ rs M
  induction rs with
  | nil =>
    change IsIso (((λ_ ((singleZero R).obj M)).hom).f 0)
    infer_instance
  | cons r rs ih =>
    have hdrop : IsIso ((dropFactor r (cechCoefficients rs M)).f 0) :=
      dropFactor_zero_isIso r (cechCoefficients rs M) (coefficients_isZero_neg rs M)
    have htail : IsIso ((projection rs ((singleZero R).obj M)).f 0) := ih
    have hassoc : IsIso
        ((α_ (Cech.factor r) (CechComplex rs) ((singleZero R).obj M)).hom.f 0) := inferInstance
    change IsIso
      ((α_ (Cech.factor r) (CechComplex rs) ((singleZero R).obj M)).hom.f 0 ≫
        (dropFactor r (cechCoefficients rs M)).f 0 ≫
          (projection rs ((singleZero R).obj M)).f 0)
    exact IsIso.comp_isIso' hassoc (IsIso.comp_isIso' hdrop htail)

open scoped TensorProduct

private noncomputable abbrev factorCoefficients (r : R) (M : ModuleCat.{u} R) :=
  Cech.factor r ⊗ (singleZero R).obj M

private noncomputable def principalZeroIso (r : R) (M : ModuleCat.{u} R) :
    M ≅ (factorCoefficients r M).X 0 :=
  (λ_ M).symm ≪≫ singleTensorTerm (Cech.factor r) M 0

private noncomputable def principalOneIso (r : R) (M : ModuleCat.{u} R) :
    ModuleCat.of R (Localization.Away r ⊗[R] M) ≅ (factorCoefficients r M).X 1 :=
  singleTensorTerm (Cech.factor r) M 1

private noncomputable def principalLoc (r : R) (M : ModuleCat.{u} R) :
    M ⟶ ModuleCat.of R (Localization.Away r ⊗[R] M) :=
  ModuleCat.ofHom (TensorProduct.mk R (Localization.Away r) M 1)

@[reassoc] private theorem principal_d (r : R) (M : ModuleCat.{u} R) :
    (principalZeroIso r M).hom ≫ (factorCoefficients r M).d 0 1 =
      principalLoc r M ≫ (principalOneIso r M).hom := by
  let F := Cech.factor r
  let S := (singleZero R).obj M
  have hl : (λ_ M).inv ≫ (F.d 0 1 ▷ M) = principalLoc r M := by
    change (λ_ M).inv ≫ ((Cech.factor r).d 0 1 ▷ M) = _
    rw [factor_d_zero_one]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (algebraMap R (Localization.Away r) 1) ⊗ₜ[R] x = 1 ⊗ₜ[R] x
    rw [map_one]
  have hd := Cech.tensor_d F S 0 0
  change ιTensorObj F S 0 0 0 rfl ≫ (F ⊗ S).d 0 1 =
    ((F.d 0 1 ▷ S.X 0) ≫ ιTensorObj F S 1 0 1 rfl) +
      (0 : ℤ).negOnePow • ((F.X 0 ◁ S.d 0 1) ≫ ιTensorObj F S 0 1 1 rfl) at hd
  have hz : S.d 0 1 = 0 := rfl
  simp only [hz, MonoidalPreadditive.whiskerLeft_zero, zero_comp, smul_zero, add_zero] at hd
  change ιTensorObj F S 0 0 0 rfl ≫ (F ⊗ S).d 0 1 =
    (F.d 0 1 ▷ M) ≫ ιTensorObj F S 1 0 1 rfl at hd
  change (((λ_ M).inv ≫ ιTensorObj F S 0 0 0 rfl) ≫ (F ⊗ S).d 0 1) =
    principalLoc r M ≫ ιTensorObj F S 1 0 1 rfl
  rw [Category.assoc, hd, ← Category.assoc, hl]

@[reassoc] private theorem principalZeroIso_drop (r : R) (M : ModuleCat.{u} R) :
    (principalZeroIso r M).hom ≫ (dropFactor r ((singleZero R).obj M)).f 0 =
      (singleObjXSelf (.up ℤ) 0 M).inv := by
  let S := (singleZero R).obj M
  let U := tensorUnit (ModuleCat.{u} R) (.up ℤ)
  have hU : (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv = 𝟙 (𝟙_ (ModuleCat R)) := rfl
  have hM : (singleObjXSelf (.up ℤ) 0 M).inv = 𝟙 M := rfl
  have hι : ιTensorObj (Cech.factor r) S 0 0 0 rfl ≫
      (HomologicalComplex.tensorHom (factorProjection r) (𝟙 S)).f 0 =
      ιTensorObj U S 0 0 0 rfl := by
    rw [ι_mapBifunctorMap]
    change ((factorProjection r).f 0 ▷ M) ≫
      ((𝟙_ (ModuleCat R)) ◁ 𝟙 M) ≫ ιTensorObj U S 0 0 0 rfl = _
    have hp : (factorProjection r).f 0 = 𝟙 (𝟙_ (ModuleCat R)) :=
      (factorProjection_f_zero r).trans hU
    rw [hp, whiskerLeft_id]
    change (𝟙 (𝟙_ (ModuleCat R)) ▷ M) ≫ 𝟙 (𝟙_ (ModuleCat R) ⊗ M) ≫
      ιTensorObj U S 0 0 0 rfl = _
    rw [id_whiskerRight, Category.id_comp, Category.id_comp]
  change ((λ_ M).inv ≫ ιTensorObj (Cech.factor r) S 0 0 0 rfl) ≫
    (HomologicalComplex.tensorHom (factorProjection r) (𝟙 S)).f 0 ≫
      (HomologicalComplex.leftUnitor S).hom.f 0 = _
  rw [Category.assoc, reassoc_of% hι, hM]
  have hh := congrArg (fun f : S ⟶ S => f.f 0)
    (Iso.inv_hom_id (HomologicalComplex.leftUnitor S))
  change (HomologicalComplex.leftUnitor' S).inv 0 ≫
    (HomologicalComplex.leftUnitor S).hom.f 0 = 𝟙 M at hh
  rw [HomologicalComplex.leftUnitor'_inv] at hh
  change ((λ_ M).inv ≫
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv ▷ M) ≫
    ιTensorObj U S 0 0 0 rfl) ≫ (HomologicalComplex.leftUnitor S).hom.f 0 = 𝟙 M at hh
  simpa only [hU, id_whiskerRight, Category.id_comp, Category.assoc] using hh

private theorem principalLoc_ker (r : R) (M : ModuleCat.{u} R) :
    LinearMap.ker (principalLoc r M).hom = idealTorsion (principal r) M := by
  let f := (principalLoc r M).hom
  have : IsLocalizedModule.Away r f :=
    IsLocalization.tensorProduct_isLocalizedModule _ _
  ext x
  change x ∈ LinearMap.ker f ↔ _
  rw [LinearMap.mem_ker, IsLocalizedModule.eq_zero_iff (Submonoid.powers r) f,
    mem_idealTorsion]
  constructor
  · rintro ⟨⟨_, n, rfl⟩, h⟩
    change r ^ n • x = 0 at h
    refine ⟨n + 1, Nat.succ_pos n, fun a ha => ?_⟩
    have ha' := Ideal.pow_le_pow_right (I := principal r) (Nat.le_succ n) ha
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha'
    obtain ⟨b, rfl⟩ := ha'
    rw [mul_comm, mul_smul, h, smul_zero]
  · rintro ⟨n, _, h⟩
    refine ⟨⟨r ^ n, n, rfl⟩, h _ ?_⟩
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _

private theorem principalLoc_cancel (r : R) (M : ModuleCat.{u} R) :
    incl (principal r) M ≫ principalLoc r M = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (principalLoc r M).hom x.val = 0
  exact LinearMap.mem_ker.mp (by rw [principalLoc_ker]; exact x.property)

private noncomputable def principalComparison (r : R) (M : ModuleCat.{u} R) :
    (singleZero R).obj (T (principal r) M) ⟶ factorCoefficients r M :=
  mkHomFromSingle (incl (principal r) M ≫ (principalZeroIso r M).hom) (fun k hk => by
    have hk' : k = 1 := by
      change (0 : ℤ) + 1 = k at hk
      omega
    subst k
    change incl (principal r) M ≫ (principalZeroIso r M).hom ≫
      (factorCoefficients r M).d 0 1 = 0
    rw [principal_d, ← Category.assoc, principalLoc_cancel, zero_comp])

@[reassoc] private theorem principalComparison_proj (r : R) (M : ModuleCat.{u} R) :
    principalComparison r M ≫ dropFactor r ((singleZero R).obj M) =
      (singleZero R).map (incl (principal r) M) := by
  apply from_single_hom_ext
  change (principalComparison r M).f 0 ≫ _ = _
  simp only [principalComparison, mkHomFromSingle_f, Category.assoc, principalZeroIso_drop,
    single_map_f_self]

private theorem principalComparison_quasiIso [IsNoetherianRing R] (r : R)
    (Q : ModuleCat.{u} R) (hQ : Module.Injective R Q) :
    QuasiIso (principalComparison r Q) := by
  have := hQ
  let S := (singleZero R).obj (T (principal r) Q)
  let K := factorCoefficients r Q
  let φ := principalComparison r Q
  have : IsLocalizedModule.Away r (principalLoc r Q).hom :=
    IsLocalization.tensorProduct_isLocalizedModule _ _
  have hl := (localizationAway_surjective_ker r (principalLoc r Q).hom).1
  rw [quasiIso_iff]
  intro n
  by_cases hn : n = 0
  · subst n
    rw [quasiIsoAt_iff' φ (-1) 0 1
      (ComplexShape.prev_eq' _ (by rfl)) (ComplexShape.next_eq' _ (by rfl))]
    let ψ := (shortComplexFunctor' (ModuleCat R) (.up ℤ) (-1) 0 1).map φ
    change ShortComplex.QuasiIso ψ
    have hK : K.d (-1) 0 = 0 := by
      exact (IsZero.of_iso (tensor_isZero_left (factor_isZero_neg r (-1) (by decide)))
        (singleTensorTerm (Cech.factor r) Q (-1)).symm).eq_of_src _ _
    rw [ShortComplex.quasiIso_iff_of_zeros ψ (by rfl) (by rfl) hK]
    have hψ : ψ.τ₂ = (singleObjXSelf (.up ℤ) 0 (T (principal r) Q)).hom ≫
        incl (principal r) Q ≫ (principalZeroIso r Q).hom := by
      change (principalComparison r Q).f 0 = _
      rw [principalComparison, mkHomFromSingle_f]
    constructor
    · apply (ShortComplex.moduleCat_exact_iff _).mpr
      intro x hx
      obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso (principalZeroIso r Q).hom).2 x
      have h : y ∈ idealTorsion (principal r) Q := by
        rw [← principalLoc_ker]
        apply LinearMap.mem_ker.mpr
        apply (ConcreteCategory.bijective_of_isIso (principalOneIso r Q).hom).1
        change (principalOneIso r Q).hom ((principalLoc r Q).hom y) =
          (principalOneIso r Q).hom 0
        rw [map_zero]
        have he := congrArg (fun f : Q ⟶ K.X 1 => f y) (principal_d r Q)
        exact he.symm.trans hx
      refine ⟨(singleObjXSelf (.up ℤ) 0 (T (principal r) Q)).inv ⟨y, h⟩, ?_⟩
      change ψ.τ₂ _ = _
      rw [hψ]
      simp only [ModuleCat.comp_apply]
      rfl
    · rw [hψ]
      have : Mono (incl (principal r) Q) := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
      infer_instance
  · rw [quasiIsoAt_iff_exactAt φ n
      (ExactAt.of_isZero (isZero_single_obj_X (.up ℤ) 0 _ n hn))]
    by_cases h1 : n = 1
    · subst n
      apply (K.exactAt_iff' (i := 0) (j := 1) (k := 2)
        (ComplexShape.prev_eq' _ (by rfl)) (ComplexShape.next_eq' _ (by rfl))).mpr
      apply (ShortComplex.moduleCat_exact_iff _).mpr
      intro x _
      obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso (principalOneIso r Q).hom).2 x
      obtain ⟨a, rfl⟩ := hl y
      exact ⟨(principalZeroIso r Q).hom a,
        congrArg (fun f : Q ⟶ K.X 1 => f a) (principal_d r Q)⟩
    · exact ExactAt.of_isZero (IsZero.of_iso (tensor_isZero_left (Cech.factor_isZero r n hn h1))
        (singleTensorTerm (Cech.factor r) Q n).symm)

@[reassoc] private theorem dropFactor_natural (r : R) {K L : Complex R} (f : K ⟶ L) :
    (𝟙 (Cech.factor r) ⊗ₘ f) ≫ dropFactor r L = dropFactor r K ≫ f := by
  let p : Cech.factor r ⟶ 𝟙_ (Complex R) := factorProjection r
  change (𝟙 (Cech.factor r) ⊗ₘ f) ≫ ((p ⊗ₘ 𝟙 L) ≫ (λ_ L).hom) =
    ((p ⊗ₘ 𝟙 K) ≫ (λ_ K).hom) ≫ f
  rw [Category.assoc, ← leftUnitor_naturality, ← id_tensorHom]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

@[reassoc] private theorem projection_natural (rs : List R) {K L : Complex R} (f : K ⟶ L) :
    (𝟙 (CechComplex rs) ⊗ₘ f) ≫ projection rs L = projection rs K ≫ f := by
  induction rs with
  | nil =>
    change (𝟙_ (Complex R) ◁ f) ≫ (λ_ L).hom = (λ_ K).hom ≫ f
    exact leftUnitor_naturality f
  | cons r rs ih =>
    let F := Cech.factor r
    let B := CechComplex rs
    change ((F ⊗ B) ◁ f) ≫ ((α_ F B L).hom ≫ dropFactor r (B ⊗ L) ≫ projection rs L) =
      ((α_ F B K).hom ≫ dropFactor r (B ⊗ K) ≫ projection rs K) ≫ f
    rw [Category.assoc, associator_naturality_right_assoc]
    rw [← id_tensorHom F, dropFactor_natural_assoc]
    rw [← id_tensorHom B, ih]
    simp only [Category.assoc]

private noncomputable abbrev coefficientsComplex (rs : List R) (M : ModuleCat.{u} R) :
    Complex R :=
  CechComplex rs ⊗ (singleZero R).obj M

private noncomputable def comparison : (rs : List R) → (M : ModuleCat.{u} R) →
    (singleZero R).obj (T (generators rs) M) ⟶ coefficientsComplex rs M
  | [], M => (singleZero R).map (incl (generators []) M) ≫ (λ_ ((singleZero R).obj M)).inv
  | r :: rs, M =>
    (singleZero R).map (torsionConsIso r rs M).hom ≫
      principalComparison r (T (generators rs) M) ≫
      (𝟙 (Cech.factor r) ⊗ₘ comparison rs M) ≫
      (α_ (Cech.factor r) (CechComplex rs) ((singleZero R).obj M)).inv

@[reassoc] private theorem comparison_proj (rs : List R) (M : ModuleCat.{u} R) :
    comparison rs M ≫ projection rs ((singleZero R).obj M) =
      (singleZero R).map (incl (generators rs) M) := by
  induction rs with
  | nil => simp only [comparison, projection, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  | cons r rs ih =>
    rw [comparison, projection]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hdrop := dropFactor_natural_assoc r (comparison rs M)
      (projection rs ((singleZero R).obj M))
    erw [hdrop]
    rw [ih]
    have hprincipal := principalComparison_proj_assoc r (T (generators rs) M)
      ((singleZero R).map (incl (generators rs) M))
    erw [hprincipal]
    rw [← Functor.map_comp, ← Functor.map_comp, torsionConsIso_incl]

private theorem comparison_quasiIso [IsNoetherianRing R] (rs : List R) (Q : ModuleCat.{u} R)
    (hQ : Module.Injective R Q) : QuasiIso (comparison rs Q) := by
  induction rs with
  | nil =>
    have := torsion_nil_isIso Q
    have h₁ := Functor.map_isIso (singleZero R) (incl (generators []) Q)
    have h₂ := Iso.isIso_inv (λ_ ((singleZero R).obj Q))
    rw [comparison]
    exact quasiIso_of_isIso _
  | cons r rs ih =>
    rw [comparison]
    have hprincipal := principalComparison_quasiIso r (T (generators rs) Q)
      (idealTorsion_injective (generators rs) hQ)
    have hBound : ∃ N : ℤ, (Cech.factor r).IsStrictlyLE N :=
      ⟨1, (CochainComplex.isStrictlyLE_iff ..).mpr
        (fun i hi => Cech.factor_isZero r i (by omega) (by omega))⟩
    have htensor : QuasiIso (𝟙 (Cech.factor r) ⊗ₘ comparison rs Q) :=
      boundedAboveFlatTensorQuasiIso R (Cech.factor r) (factor_flat r) hBound _ ih
    have h₁ := Functor.map_isIso (singleZero R) (torsionConsIso r rs Q).hom
    have h₂ := Iso.isIso_inv (α_ (Cech.factor r) (CechComplex rs) ((singleZero R).obj Q))
    exact quasiIso_comp _ _

private theorem comparison_natural (rs : List R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((idealTorsionFunctor (generators rs) ⋙ singleZero R).map f) ≫ comparison rs N =
      comparison rs M ≫ ((singleZero R ⋙ cechTensorFunctor rs).map f) := by
  have hN := cechProjection_degreeZero rs N
  apply from_single_hom_ext
  apply (cancel_mono ((projection rs ((singleZero R).obj N)).f 0)).mp
  change ((_ ≫ comparison rs N) ≫ projection rs ((singleZero R).obj N)).f 0 =
    ((comparison rs M ≫ _) ≫ projection rs ((singleZero R).obj N)).f 0
  have h : ((idealTorsionFunctor (generators rs) ⋙ singleZero R).map f) ≫ comparison rs N ≫
      projection rs ((singleZero R).obj N) =
      comparison rs M ≫ (𝟙 (CechComplex rs) ⊗ₘ (singleZero R).map f) ≫
        projection rs ((singleZero R).obj N) := by
    rw [comparison_proj, projection_natural, comparison_proj_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp]
    rfl
  exact congrArg (fun g => g.f 0) ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm))

/-- For every list generating the ideal, the degree-zero torsion inclusion is
natural in the coefficient module and is a quasi-isomorphism on injectives. -/
theorem idealTorsionCechComparison :
    Specs.CommutativeAlgebraNotes.InjectiveCechComparison.Comparison.{u} := by
  intro R _ _ I rs hI
  subst I
  refine ⟨{ app := comparison rs, naturality := fun _ _ f => comparison_natural rs f }, comparison_proj rs, ?_⟩
  intro Q hQ
  exact comparison_quasiIso rs Q ((Module.injective_iff_injective_object R Q).mpr hQ)

end CommutativeAlgebraNotes
