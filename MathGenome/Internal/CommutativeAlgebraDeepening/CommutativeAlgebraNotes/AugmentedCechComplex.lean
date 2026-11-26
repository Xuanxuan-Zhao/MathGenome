import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.AugmentedCechComplex
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.RingTheory.Localization.BaseChange

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open HomologicalComplex
open scoped TensorProduct DirectSum

namespace CommutativeAlgebraNotes

universe u

variable {R : Type u} [CommRing R]

namespace Cech

abbrev Complex (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{u} R) ℤ

noncomputable abbrev factor (r : R) : Complex R :=
  Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor R r

end Cech

/-- The augmented Čech complex of an ordered list of ring elements. -/
noncomputable abbrev CechComplex (rs : List R) : Cech.Complex R :=
  Specs.CommutativeAlgebraNotes.AugmentedCechComplex.complex R rs

/-- Tensoring on the left by the augmented Čech complex. -/
noncomputable abbrev cechTensorFunctor (rs : List R) : Cech.Complex R ⥤ Cech.Complex R :=
  Specs.CommutativeAlgebraNotes.AugmentedCechComplex.tensorFunctor R rs

/-- The augmented Čech complex with module coefficients. -/
noncomputable abbrev cechCoefficients (rs : List R) (M : ModuleCat.{u} R) : Cech.Complex R :=
  Specs.CommutativeAlgebraNotes.AugmentedCechComplex.coefficients R rs M

namespace Cech

@[simp] theorem nil_complex : CechComplex ([] : List R) = tensorUnit (ModuleCat.{u} R) (ComplexShape.up ℤ) := rfl

@[simp] theorem cons_complex (r : R) (rs : List R) :
    CechComplex (r :: rs) = HomologicalComplex.tensorObj (factor r) (CechComplex rs) := rfl

theorem factor_isZero (r : R) (i : ℤ) (hi : i ≠ 0) (hi' : i ≠ 1) :
    IsZero ((factor r).X i) := by
  simpa [factor, Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor, hi, hi'] using
    ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)

private theorem tensor_isZero_left {M N : ModuleCat.{u} R} (h : IsZero M) :
    IsZero (M ⊗ N) :=
  Functor.map_isZero ((curriedTensor (ModuleCat R)).flip.obj N) h

private theorem tensor_isZero_right {M N : ModuleCat.{u} R} (h : IsZero N) :
    IsZero (M ⊗ N) :=
  Functor.map_isZero ((curriedTensor (ModuleCat R)).obj M) h

private abbrev Diagonal (k : ℤ) := { ij : ℤ × ℤ // ij.1 + ij.2 = k }

private noncomputable def tensorCofan (A B : Complex R) (k : ℤ) :
    Cofan (fun ij : Diagonal k => A.X ij.val.1 ⊗ B.X ij.val.2) :=
  Cofan.mk (HomologicalComplex.tensorObj A B |>.X k)
    (fun ij => ιTensorObj A B ij.val.1 ij.val.2 k ij.property)

private noncomputable def tensorCofanIsColimit (A B : Complex R) (k : ℤ) :
    IsColimit (tensorCofan A B k) := by
  refine Cofan.IsColimit.mk _ (fun s => mapBifunctorDesc
    (fun i j h => s.inj ⟨(i, j), h⟩)) ?_ ?_
  · rintro s ⟨⟨i, j⟩, h⟩
    exact ι_mapBifunctorDesc _ _ _ _
  · intro s f h
    apply mapBifunctor.hom_ext
    intro i j hij
    refine (h ⟨(i, j), hij⟩).trans ?_
    symm
    exact ι_mapBifunctorDesc _ _ _ _

private theorem flat_of_isZero {M : ModuleCat.{u} R} (h : IsZero M) :
    Module.Flat R M := by
  let := ModuleCat.subsingleton_of_isZero h
  infer_instance

private theorem factor_flat (r : R) (i : ℤ) : Module.Flat R ((factor r).X i) := by
  by_cases h : i = 0
  · subst i
    change Module.Flat R R
    infer_instance
  by_cases h' : i = 1
  · subst i
    change Module.Flat R (Localization.Away r)
    infer_instance
  exact flat_of_isZero (factor_isZero r i h h')

private theorem tensor_flat (A B : Complex R) (k : ℤ)
    (hA : ∀ i, Module.Flat R (A.X i)) (hB : ∀ i, Module.Flat R (B.X i)) :
    Module.Flat R ((HomologicalComplex.tensorObj A B).X k) := by
  let F (ij : Diagonal k) : ModuleCat.{u} R := A.X ij.val.1 ⊗ B.X ij.val.2
  have (ij : Diagonal k) : Module.Flat R (F ij) := by
    let := hA ij.val.1
    let := hB ij.val.2
    change Module.Flat R (A.X ij.val.1 ⊗[R] B.X ij.val.2)
    infer_instance
  let e := (tensorCofanIsColimit A B k).coconePointUniqueUpToIso
    (ModuleCat.coproductCoconeIsColimit F)
  have : Module.Flat R (↑(ModuleCat.coproductCocone F).pt : Type u) :=
    inferInstanceAs (Module.Flat R (⨁ ij : Diagonal k, F ij))
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

theorem flat (rs : List R) (i : ℤ) : Module.Flat R ((CechComplex rs).X i) := by
  induction rs generalizing i with
  | nil =>
    by_cases hi : i = 0
    · subst i
      exact Module.Flat.of_linearEquiv (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).toLinearEquiv
    · exact flat_of_isZero (isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R)) i hi)
  | cons r rs ih =>
    exact tensor_flat _ _ _ (factor_flat r) ih

/-- The complex is supported between zero and the length of the list. -/
theorem isZero_X (rs : List R) (k : ℤ) (h : k < 0 ∨ (rs.length : ℤ) < k) :
    IsZero ((CechComplex rs).X k) := by
  induction rs generalizing k with
  | nil =>
    exact isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R)) k (by simp at h; omega)
  | cons r rs ih =>
    change IsZero ((HomologicalComplex.tensorObj (factor r) (CechComplex rs)).X k)
    apply (IsZero.iff_id_eq_zero _).mpr
    apply mapBifunctor.hom_ext
    intro i j hij
    change i + j = k at hij
    by_cases hi : i = 0 ∨ i = 1
    · have hj : j < 0 ∨ (rs.length : ℤ) < j := by
        simp only [List.length_cons, Nat.cast_succ] at h
        omega
      exact (tensor_isZero_right (ih j hj)).eq_of_src _ _
    · exact (tensor_isZero_left (factor_isZero r i (fun h => hi (Or.inl h))
        (fun h => hi (Or.inr h)))).eq_of_src _ _

/-- The action of the total differential on a bidegree summand. Its second
component has the sign of the degree in the left factor. -/
@[reassoc] theorem tensor_d (A B : Complex R) (i j : ℤ) :
    ιTensorObj A B i j (i + j) rfl ≫ (HomologicalComplex.tensorObj A B).d (i + j) (i + j + 1) =
      (A.d i (i + 1) ▷ B.X j) ≫
        ιTensorObj A B (i + 1) j (i + j + 1) (by omega) +
      i.negOnePow • ((A.X i ◁ B.d j (j + 1)) ≫
        ιTensorObj A B i (j + 1) (i + j + 1) (by omega)) := by
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl) _ _ (by
      change (i + 1) + j = i + j + 1; omega),
    mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl) _ (by
      change i + (j + 1) = i + j + 1; omega)]
  change (1 : ℤˣ) • _ + i.negOnePow • _ = _ + i.negOnePow • _
  rw [one_smul]
  rfl

/-- Restricting a coproduct to a subfamily discards only zero objects. -/
private noncomputable def restrictCofanIsColimit {α β : Type} {F : α → ModuleCat.{u} R}
    (c : Cofan F) (hc : IsColimit c) (e : β ↪ α)
    (hz : ∀ a, (∀ b, e b ≠ a) → IsZero (F a)) :
    IsColimit (Cofan.mk c.pt (fun b => c.inj (e b))) := by
  classical
  let G := fun b => F (e b)
  let extend (t : Cofan G) (a : α) : F a ⟶ t.pt :=
    if h : ∃ b, e b = a then eqToHom (congrArg F h.choose_spec.symm) ≫ t.inj h.choose
    else 0
  have hExtend (t : Cofan G) (b : β) : extend t (e b) = t.inj b := by
    have hh : ∃ b', e b' = e b := ⟨b, rfl⟩
    change (if h : ∃ b', e b' = e b then _ else _) = _
    rw [dite_eq_left hh]
    have aux (b' : β) (h : e b' = e b) :
        eqToHom (congrArg F h.symm) ≫ t.inj b' = t.inj b := by
      obtain rfl := e.injective h
      simp
    exact aux hh.choose hh.choose_spec
  refine Cofan.IsColimit.mk _ (fun t => Cofan.IsColimit.desc hc (extend t)) ?_ ?_
  · intro t b
    exact (Cofan.IsColimit.fac hc (extend t) (e b)).trans (hExtend t b)
  · intro t f hf
    apply Cofan.IsColimit.hom_ext hc
    intro a
    by_cases h : ∃ b, e b = a
    · obtain ⟨b, rfl⟩ := h
      rw [Cofan.IsColimit.fac, hExtend]
      exact hf b
    · exact (hz a (fun b hb => h ⟨b, hb⟩)).eq_of_src _ _

private noncomputable def precomposeCofanIsColimit {α : Type}
    {F G : α → ModuleCat.{u} R} (c : Cofan G) (hc : IsColimit c)
    (e : ∀ a, F a ≅ G a) :
    IsColimit (Cofan.mk c.pt (fun a => (e a).hom ≫ c.inj a)) := by
  refine Cofan.IsColimit.mk _ (fun t => Cofan.IsColimit.desc hc (fun a => (e a).inv ≫ t.inj a))
    ?_ ?_
  · intro t a
    simp only [cofan_mk_inj, Category.assoc, Cofan.IsColimit.fac, Iso.hom_inv_id_assoc]
  · intro t f hf
    apply Cofan.IsColimit.hom_ext hc
    intro a
    rw [Cofan.IsColimit.fac, Iso.eq_inv_comp]
    simpa only [cofan_mk_inj, Category.assoc] using hf a

/-- Tensoring with a module in degree zero has only the summand of bidegree (q, 0). -/
noncomputable def tensorSingleTerm (A : Complex R) (M : ModuleCat.{u} R) (q : ℤ) :
    A.X q ⊗ M ≅
      (HomologicalComplex.tensorObj A ((single (ModuleCat R) (.up ℤ) 0).obj M)).X q := by
  let B : Complex R := (single (ModuleCat R) (.up ℤ) 0).obj M
  let e : Unit ↪ Diagonal q := ⟨fun _ => ⟨(q, 0), add_zero q⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  have hz (ij : Diagonal q) (h : ∀ b, e b ≠ ij) :
      IsZero (A.X ij.val.1 ⊗ B.X ij.val.2 : ModuleCat.{u} R) := by
    rcases ij with ⟨⟨i, j⟩, hq⟩
    refine tensor_isZero_right (isZero_single_obj_X (.up ℤ) 0 M j ?_)
    rintro rfl
    have hi : i = q := by simpa using hq
    subst i
    exact h () rfl
  let P : ModuleCat.{u} R := A.X q ⊗ B.X 0
  let c := Cofan.mk P (fun _ : Unit => 𝟙 P)
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk _ (fun t => t.inj ()) ?_ ?_
    · rintro t ⟨⟩
      exact Category.id_comp _
    · intro t m hm
      exact (Category.id_comp _).symm.trans (hm ())
  exact (tensorLeft (A.X q)).mapIso (singleObjXSelf (.up ℤ) 0 M).symm ≪≫
    hc.coconePointUniqueUpToIso (restrictCofanIsColimit _ (tensorCofanIsColimit A B q) e hz)


open Specs.CommutativeAlgebraNotes.AugmentedCechComplex (Selection headDegree product term moduleTerm)

private def headDiagonal (k : ℤ) : Bool ↪ Diagonal k where
  toFun b := ⟨(headDegree b, k - headDegree b), by omega⟩
  inj' := by
    intro b b' h
    have he := congrArg (fun ij : Diagonal k => ij.val.1) h
    cases b <;> cases b' <;> simp_all [headDegree]

private noncomputable abbrev headCofan (r : R) (B : Complex R) (k : ℤ) :
    Cofan (fun b => (factor r).X (headDegree b) ⊗ B.X (k - headDegree b)) :=
  Cofan.mk ((HomologicalComplex.tensorObj (factor r) B).X k)
    (fun b => ιTensorObj (factor r) B (headDegree b) (k - headDegree b) k (by omega))

private noncomputable def headCofanIsColimit (r : R) (B : Complex R) (k : ℤ) :
    IsColimit (headCofan r B k) := by
  apply restrictCofanIsColimit _ (tensorCofanIsColimit (factor r) B k) (headDiagonal k)
  rintro ⟨⟨i, j⟩, hij⟩ h
  refine tensor_isZero_left (factor_isZero r i ?_ ?_)
  · intro hi
    apply h false
    apply Subtype.ext
    change (headDegree false, k - headDegree false) = (i, j)
    simp [headDegree] at hij ⊢
    simp [hi, ← hij]
  · intro hi
    apply h true
    apply Subtype.ext
    change (headDegree true, k - headDegree true) = (i, j)
    simp [headDegree]
    exact ⟨hi.symm, by omega⟩

/-- The tensor of two principal localizations inverts the product. -/
private noncomputable def localizationTensorIso (r t : R) :
    (Localization.Away r ⊗[R] Localization.Away t) ≃ₐ[R] Localization.Away (r * t) := by
  let A := Localization.Away r
  let B := Localization.Away t
  have : IsLocalization.Away (r * t) (A ⊗[R] B) :=
    IsLocalization.Away.mul' A (A ⊗[R] B) r t
  exact IsLocalization.algEquiv (Submonoid.powers (r * t)) _ _

private noncomputable def termTensorIso (r : R) (rs : List R) (k : ℤ)
    (s : Selection (r :: rs).length k) :
    (factor r).X (headDegree s.1) ⊗ term R rs s.2 ≅ term R (r :: rs) s := by
  rcases s with ⟨b, s⟩
  cases b
  · exact λ_ (term R rs s)
  · exact (localizationTensorIso r (product R rs s)).toLinearEquiv.toModuleIso

/-- Inclusion of a localization summand in the tensor Čech complex. -/
noncomputable def summandι : (rs : List R) → (k : ℤ) → (s : Selection rs.length k) →
    term R rs s ⟶ (CechComplex rs).X k
  | [], k, s =>
      (IsLocalization.atOne R (Localization.Away (1 : R))).symm.toLinearEquiv.toModuleIso.hom ≫
        (singleObjXIsoOfEq (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R)) k s.down).inv
  | r :: rs, k, s =>
      (termTensorIso r rs k s).inv ≫
        ((factor r).X (headDegree s.1) ◁ summandι rs (k - headDegree s.1) s.2) ≫
        (headCofan r (CechComplex rs) k).inj s.1

/-- The degree-q term is the coproduct of the localizations indexed by the q-element subsets. -/
noncomputable def summandCofanIsColimit (rs : List R) (k : ℤ) :
    IsColimit (Cofan.mk ((CechComplex rs).X k) (summandι rs k)) := by
  induction rs generalizing k with
  | nil =>
    by_cases hk : k = 0
    · subst k
      let s : Selection ([] : List R).length (0 : ℤ) := ⟨rfl⟩
      let e : term R [] s ≅ (CechComplex ([] : List R)).X 0 :=
        (IsLocalization.atOne R (Localization.Away (1 : R))).symm.toLinearEquiv.toModuleIso ≪≫
          (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).symm
      refine Cofan.IsColimit.mk _ (fun t => e.inv ≫ t.inj s) ?_ ?_
      · intro t s'
        have : s' = s := @Subsingleton.elim (PLift ((0 : ℤ) = 0)) inferInstance s' s
        subst s'
        change e.hom ≫ (e.inv ≫ t.inj s) = _
        simp only [Iso.hom_inv_id_assoc]
      · intro t m hm
        apply (cancel_epi e.hom).mp
        rw [Iso.hom_inv_id_assoc]
        exact hm s
    · have hz := isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R)) k hk
      exact Cofan.IsColimit.mk _ (fun _ => 0) (fun _ s => (hk s.down).elim)
        (fun _ _ _ => hz.eq_of_src _ _)
  | cons r rs ih =>
    let c := headCofan r (CechComplex rs) k
    have hc := headCofanIsColimit r (CechComplex rs) k
    let inner (b : Bool) := summandι rs (k - headDegree b)
    let F (b : Bool) := tensorLeft ((factor r).X (headDegree b))
    have hs (b : Bool) : IsColimit (Cofan.mk _ (fun s => (F b).map (inner b s))) :=
      isColimitCofanMkObjOfIsColimit (F b) _ _ (ih (k - headDegree b))
    let c' := Cofan.mk c.pt (fun s : Selection (r :: rs).length k =>
      (F s.1).map (inner s.1 s.2) ≫ c.inj s.1)
    have hc' : IsColimit c' := Cofan.isColimitTrans c hc _ hs
    exact precomposeCofanIsColimit c' hc' (fun s => (termTensorIso r rs k s).symm)

/-- The degreewise isomorphism with the direct sum of principal ring localizations. -/
noncomputable def ringTerms (rs : List R) (k : ℤ) :
    (CechComplex rs).X k ≅ ∐ (fun s : Selection rs.length k => term R rs s) :=
  (summandCofanIsColimit rs k).coconePointUniqueUpToIso (colimit.isColimit _)

private noncomputable def moduleTermIso (rs : List R) (M : ModuleCat.{u} R)
    {k : ℤ} (s : Selection rs.length k) :
    moduleTerm R rs M s ≅ term R rs s ⊗ M :=
  ((LocalizedModule.equivTensorProduct (Submonoid.powers (product R rs s)) M).restrictScalars
    R).toModuleIso

/-- The degreewise isomorphism with the direct sum of principal module localizations. -/
noncomputable def moduleTerms (rs : List R) (M : ModuleCat.{u} R) (k : ℤ) :
    (cechCoefficients rs M).X k ≅ ∐ (fun s : Selection rs.length k => moduleTerm R rs M s) := by
  let t := tensorRight M
  let c := Cofan.mk (t.obj ((CechComplex rs).X k))
    (fun s : Selection rs.length k => t.map (summandι rs k s))
  have hc : IsColimit c :=
    isColimitCofanMkObjOfIsColimit t _ _ (summandCofanIsColimit rs k)
  let hc' := precomposeCofanIsColimit c hc (moduleTermIso rs M)
  exact (tensorSingleTerm (CechComplex rs) M k).symm ≪≫
    hc'.coconePointUniqueUpToIso (colimit.isColimit _)

/-- The differential in the first factor is possible only when its degree is zero. -/
private noncomputable def headInsertion (r : R) (B : Complex R) (k : ℤ) (b : Bool) :
    (factor r).X (headDegree b) ⊗ B.X (k - headDegree b) ⟶
      (HomologicalComplex.tensorObj (factor r) B).X (k + 1) :=
  match b with
  | false =>
      ((factor r).d 0 1 ▷ B.X (k - headDegree false)) ≫
        ιTensorObj (factor r) B 1 (k - headDegree false) (k + 1) (by simp [headDegree]; omega)
  | true => 0

private noncomputable def tailMap (r : R) (B : Complex R) (k : ℤ) (b : Bool)
    (g : B.X (k - headDegree b) ⟶ B.X (k - headDegree b + 1)) :
    (factor r).X (headDegree b) ⊗ B.X (k - headDegree b) ⟶
      (HomologicalComplex.tensorObj (factor r) B).X (k + 1) :=
  ((factor r).X (headDegree b) ◁ g) ≫
    ιTensorObj (factor r) B (headDegree b) (k - headDegree b + 1) (k + 1) (by omega)

private theorem headDifferential (r : R) (B : Complex R) (k : ℤ) (b : Bool) :
    (headCofan r B k).inj b ≫ (HomologicalComplex.tensorObj (factor r) B).d k (k + 1) =
      headInsertion r B k b + (headDegree b).negOnePow •
        tailMap r B k b (B.d (k - headDegree b) (k - headDegree b + 1)) := by
  change ιTensorObj (factor r) B (headDegree b) (k - headDegree b) k _ ≫ _ = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.up ℤ).Rel (headDegree b) (headDegree b + 1) from rfl) _ _ (by
        change (headDegree b + 1) + (k - headDegree b) = k + 1
        omega),
    mapBifunctor.d₂_eq _ _ _ _ _
      (show (ComplexShape.up ℤ).Rel (k - headDegree b) (k - headDegree b + 1) from rfl)
      _ (by change headDegree b + (k - headDegree b + 1) = k + 1; omega)]
  change (1 : ℤˣ) • _ + (headDegree b).negOnePow • _ = _
  rw [one_smul]
  simp only [curriedTensor_map_app, curriedTensor_obj_map]
  congr 1
  cases b
  · rfl
  · simp [headInsertion, headDegree, factor, Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor]

/-- The map inserting one specified position. The sign at each step comes from
the degree of the earlier factor skipped by that step. -/
noncomputable def insertionMap (signed : Bool) :
    (rs : List R) → (a : Fin rs.length) → (k : ℤ) →
      (CechComplex rs).X k ⟶ (CechComplex rs).X (k + 1)
  | [], a, _ => Fin.elim0 a
  | r :: rs, a, k =>
      Fin.cases
        (Cofan.IsColimit.desc (headCofanIsColimit r (CechComplex rs) k)
          (headInsertion r (CechComplex rs) k))
        (fun a' => Cofan.IsColimit.desc (headCofanIsColimit r (CechComplex rs) k)
          (fun b => (if signed then (headDegree b).negOnePow else (1 : ℤˣ)) •
            tailMap r (CechComplex rs) k b
              (insertionMap signed rs a' (k - headDegree b)))) a

private theorem headι_insertionMap_zero (signed : Bool) (r : R) (rs : List R) (k : ℤ) (b : Bool) :
    (headCofan r (CechComplex rs) k).inj b ≫ insertionMap signed (r :: rs) 0 k =
      headInsertion r (CechComplex rs) k b := by
  exact Cofan.IsColimit.fac (headCofanIsColimit r (CechComplex rs) k) _ b

private theorem headι_insertionMap_succ (signed : Bool) (r : R) (rs : List R)
    (a : Fin rs.length) (k : ℤ) (b : Bool) :
    (headCofan r (CechComplex rs) k).inj b ≫ insertionMap signed (r :: rs) a.succ k =
      (if signed then (headDegree b).negOnePow else (1 : ℤˣ)) •
        tailMap r (CechComplex rs) k b (insertionMap signed rs a (k - headDegree b)) := by
  exact Cofan.IsColimit.fac (headCofanIsColimit r (CechComplex rs) k) _ b

private theorem tailMap_sum {α : Type*} (r : R) (B : Complex R) (k : ℤ) (b : Bool)
    (s : Finset α) (g : α → (B.X (k - headDegree b) ⟶ B.X (k - headDegree b + 1))) :
    tailMap r B k b (∑ a ∈ s, g a) = ∑ a ∈ s, tailMap r B k b (g a) := by
  simp only [tailMap, whiskerLeft_sum, Preadditive.sum_comp]

/-- The differential is the sum of the signed insertion maps on the ordered positions. -/
theorem differential_eq_sum (rs : List R) (k : ℤ) :
    (CechComplex rs).d k (k + 1) = ∑ a : Fin rs.length, insertionMap true rs a k := by
  induction rs generalizing k with
  | nil => simp
  | cons r rs ih =>
    apply Cofan.IsColimit.hom_ext (headCofanIsColimit r (CechComplex rs) k)
    intro b
    change (headCofan r (CechComplex rs) k).inj b ≫
      (HomologicalComplex.tensorObj (factor r) (CechComplex rs)).d k (k + 1) = _
    rw [headDifferential]
    have hs := Fin.sum_univ_succ
      (fun a : Fin (rs.length + 1) => insertionMap true (r :: rs) a k)
    erw [hs, Preadditive.comp_add, Preadditive.comp_sum, headι_insertionMap_zero]
    simp only [headι_insertionMap_succ, ite_true]
    rw [ih (k - headDegree b), tailMap_sum, Finset.smul_sum]

open Specs.CommutativeAlgebraNotes.AugmentedCechComplex (selected preceding)

/-- The integer degree of a selection is the size of the selected subset. -/
theorem selection_card {n : ℕ} {k : ℤ} (s : Selection n k) :
    (((Finset.univ.filter fun i => selected s i = true).card : ℕ) : ℤ) = k := by
  have hdegree (b : Bool) : headDegree b = if b = true then 1 else 0 := by cases b <;> rfl
  rw [← Finset.sum_boole]
  change ∑ i : Fin n, (if selected s i = true then (1 : ℤ) else 0) = k
  simp only [← hdegree]
  induction n generalizing k with
  | zero =>
    change PLift (k = 0) at s
    simp [s.down]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    change headDegree s.1 + (∑ i : Fin n, headDegree (selected s.2 i)) = k
    rw [ih]
    omega

/-- The sign exponent counts exactly the selected positions strictly before the insertion. -/
theorem preceding_card {n : ℕ} {k : ℤ} (s : Selection n k) (a : Fin n) :
    preceding s a =
      (((Finset.univ.filter fun j => selected s j = true ∧ j < a).card : ℕ) : ℤ) := by
  rw [← Finset.sum_boole]
  induction n generalizing k with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) a
    · simp [preceding]
    · rw [Fin.sum_univ_succ]
      have ha (b : Bool) : (if b = true then (1 : ℤ) else 0) = headDegree b := by
        cases b <;> rfl
      change headDegree s.1 + preceding s.2 i =
        (if selected s 0 = true ∧ (0 : Fin (n + 1)) < i.succ then 1 else 0) +
          ∑ j : Fin n, if selected s j.succ = true ∧ j.succ < i.succ then 1 else 0
      have hpos : (0 : Fin (n + 1)) < i.succ := Fin.succ_pos i
      simp only [hpos, and_true, Fin.succ_lt_succ_iff]
      change headDegree s.1 + preceding s.2 i =
        (if s.1 = true then 1 else 0) +
          ∑ j : Fin n, if selected s.2 j = true ∧ j < i then 1 else 0
      rw [ha, ih]

private theorem selection_ext {n : ℕ} {k : ℤ} (s t : Selection n k)
    (h : ∀ i, selected s i = selected t i) : s = t := by
  induction n generalizing k with
  | zero => exact @Subsingleton.elim (PLift (k = 0)) inferInstance s t
  | succ n ih =>
    rcases s with ⟨b, s⟩
    rcases t with ⟨b', t⟩
    have hb : b = b' := h 0
    subst b'
    have ht := ih s t (fun i => h i.succ)
    cases ht
    rfl

private def selectionOfSubset : (n : ℕ) → (S : Finset (Fin n)) →
    Selection n (S.card : ℤ)
  | 0, S => ⟨by simp [show S = ∅ from Finset.eq_empty_of_forall_notMem (fun a => Fin.elim0 a)]⟩
  | n + 1, S => by
    let b := decide ((0 : Fin (n + 1)) ∈ S)
    let T := Finset.univ.filter fun i : Fin n => i.succ ∈ S
    have he : (T.card : ℤ) = (S.card : ℤ) - headDegree b := by
      have hb : (if (0 : Fin (n + 1)) ∈ S then (1 : ℤ) else 0) = headDegree b := by
        by_cases h : (0 : Fin (n + 1)) ∈ S <;> simp [b, h, headDegree]
      have h := Fin.sum_univ_succ (fun i : Fin (n + 1) => if i ∈ S then (1 : ℤ) else 0)
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hb,
        Finset.sum_boole] at h
      change (S.card : ℤ) = headDegree b + (T.card : ℤ) at h
      omega
    exact ⟨b, he ▸ selectionOfSubset n T⟩

private theorem selected_selectionOfSubset (n : ℕ) (S : Finset (Fin n)) (a : Fin n) :
    selected (selectionOfSubset n S) a = decide (a ∈ S) := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) a
    · rfl
    · let T := Finset.univ.filter fun i : Fin n => i.succ ∈ S
      have aux (j : ℤ) (e : (T.card : ℤ) = j) :
          selected (e ▸ selectionOfSubset n T : Selection n j) i = decide (i.succ ∈ S) := by
        subst j
        rw [ih]
        simp [T]
      exact aux _ _

/-- The membership encoding is in bijection with the q-element subsets of the positions. -/
noncomputable def selectionEquiv (n : ℕ) (k : ℤ) :
    Selection n k ≃ { S : Finset (Fin n) // (S.card : ℤ) = k } := by
  refine Equiv.ofBijective (fun s => ⟨Finset.univ.filter fun a => selected s a = true,
    selection_card s⟩) ⟨?_, ?_⟩
  · intro s t h
    apply selection_ext s t
    intro i
    have he : (selected s i = true) = (selected t i = true) := by
      have hm := congrArg (fun U : { S : Finset (Fin n) // (S.card : ℤ) = k } => i ∈ U.val) h
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hm
    cases hs : selected s i <;> cases ht : selected t i <;> simp_all
  · rintro ⟨S, rfl⟩
    refine ⟨selectionOfSubset n S, Subtype.ext ?_⟩
    ext a
    simp [selected_selectionOfSubset]


/-- The summand denominator is the product of the selected list entries. -/
theorem product_eq {k : ℤ} (rs : List R) (s : Selection rs.length k) :
    product R rs s = ∏ a ∈ Finset.univ.filter (fun a => selected s a = true), rs.get a := by
  rw [Finset.prod_filter]
  induction rs generalizing k with
  | nil => simp [product]
  | cons r rs ih =>
    have hprod := Fin.prod_univ_succ
      (fun a : Fin (rs.length + 1) => if selected s a = true then (r :: rs).get a else 1)
    erw [hprod]
    rcases s with ⟨b, s⟩
    have ih' := ih s
    cases b
    · change product R rs s = (if false = true then r else 1) *
        (∏ a : Fin rs.length, if selected s a = true then rs.get a else 1)
      simpa only [Bool.false_eq_true, ite_false, one_mul] using ih'
    · change r * product R rs s = (if true = true then r else 1) *
        (∏ a : Fin rs.length, if selected s a = true then rs.get a else 1)
      simpa only [ite_true] using congrArg (r * ·) ih'

private theorem summandι_insert_zero (signed : Bool) (r : R) (rs : List R)
    (k : ℤ) (s : Selection (r :: rs).length k) :
    summandι (r :: rs) k s ≫ insertionMap signed (r :: rs) 0 k =
      (termTensorIso r rs k s).inv ≫
        ((factor r).X (headDegree s.1) ◁ summandι rs (k - headDegree s.1) s.2) ≫
        headInsertion r (CechComplex rs) k s.1 := by
  rw [summandι]
  simp only [Category.assoc]
  erw [headι_insertionMap_zero]

private theorem summandι_insert_succ (signed : Bool) (r : R) (rs : List R)
    (a : Fin rs.length) (k : ℤ) (s : Selection (r :: rs).length k) :
    summandι (r :: rs) k s ≫ insertionMap signed (r :: rs) a.succ k =
      (if signed then (headDegree s.1).negOnePow else (1 : ℤˣ)) •
        ((termTensorIso r rs k s).inv ≫
          ((factor r).X (headDegree s.1) ◁
            (summandι rs (k - headDegree s.1) s.2 ≫
              insertionMap signed rs a (k - headDegree s.1))) ≫
          ιTensorObj (factor r) (CechComplex rs) (headDegree s.1)
            (k - headDegree s.1 + 1) (k + 1) (by omega)) := by
  rw [summandι]
  simp only [Category.assoc]
  erw [headι_insertionMap_succ]
  simp only [tailMap, Units.smul_def, Preadditive.comp_zsmul, ← whiskerLeft_comp_assoc]

/-- A selected position contributes zero to the differential. -/
theorem summandι_insert_eq_zero (signed : Bool) (rs : List R) (k : ℤ)
    (s : Selection rs.length k) (a : Fin rs.length) (h : selected s a = true) :
    summandι rs k s ≫ insertionMap signed rs a k = 0 := by
  induction rs generalizing k with
  | nil => exact Fin.elim0 a
  | cons r rs ih =>
    induction a using Fin.cases with
    | zero =>
      rw [summandι_insert_zero]
      rcases s with ⟨b, s⟩
      change b = true at h
      subst b
      simp [headInsertion]
    | succ a =>
      rw [summandι_insert_succ]
      change selected s.2 a = true at h
      rw [ih _ s.2 a h]
      simp

/-- An insertion is multiplied by (-1) to the number of selected positions
strictly preceding it. -/
theorem summandι_insert_sign (rs : List R) (k : ℤ)
    (s : Selection rs.length k) (a : Fin rs.length) :
    summandι rs k s ≫ insertionMap true rs a k =
      (preceding s a).negOnePow • (summandι rs k s ≫ insertionMap false rs a k) := by
  induction rs generalizing k with
  | nil => exact Fin.elim0 a
  | cons r rs ih =>
    induction a using Fin.cases with
    | zero =>
      simp only [summandι_insert_zero]
      change _ = (0 : ℤ).negOnePow • _
      rw [Int.negOnePow_zero, one_smul]
    | succ a =>
      simp only [summandι_insert_succ, ite_true, Bool.false_eq_true, ite_false, one_smul]
      rw [ih _ s.2 a]
      have hmap (A : ModuleCat.{u} R) {X Y : ModuleCat.{u} R} (e : ℤˣ) (f : X ⟶ Y) :
          A ◁ (e • f) = e • (A ◁ f) :=
        (tensorLeft A).map_zsmul
      rw [hmap]
      have hcomp (A B C : ModuleCat.{u} R) (e : ℤˣ) (f : A ⟶ B) (g : B ⟶ C) :
          f ≫ (e • g) = e • (f ≫ g) := Preadditive.comp_zsmul f g (e : ℤ)
      have hcomp' (A B C : ModuleCat.{u} R) (e : ℤˣ) (f : A ⟶ B) (g : B ⟶ C) :
          (e • f) ≫ g = e • (f ≫ g) := Preadditive.zsmul_comp f g (e : ℤ)
      simp only [hcomp, hcomp', smul_smul, ← Int.negOnePow_add]
      rfl

/-- The differential on an individual localization summand, with the source signs. -/
theorem summandι_differential (rs : List R) (k : ℤ) (s : Selection rs.length k) :
    summandι rs k s ≫ (CechComplex rs).d k (k + 1) =
      ∑ a : Fin rs.length, (preceding s a).negOnePow •
        (summandι rs k s ≫ insertionMap false rs a k) := by
  simp only [differential_eq_sum, Preadditive.comp_sum, summandι_insert_sign]

private abbrev loc (r : R) := Localization.Away r

private abbrev algMap {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : ModuleCat.of R A ⟶ ModuleCat.of R B :=
  ModuleCat.ofHom f.toLinearMap

private noncomputable def castLocalization (rs : List R) {i j : ℤ} (h : i = j)
    (s : Selection rs.length i) : loc (product R rs s) →ₐ[R] loc (product R rs (h ▸ s)) := by
  subst j
  exact AlgHom.id _ _

private theorem selected_cast {n : ℕ} {i j : ℤ} (h : i = j) (s : Selection n i) (a : Fin n) :
    selected (h ▸ s) a = selected s a := by
  subst j
  rfl

private theorem castLocalization_ι (rs : List R) {i j : ℤ} (h : i = j)
    (s : Selection rs.length i) :
    algMap (castLocalization rs h s) ≫ summandι rs j (h ▸ s) =
      summandι rs i s ≫ eqToHom (congrArg (CechComplex rs).X h) := by
  subst j
  change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  simp

private theorem ιTensorObj_whisker_cast (A B : Complex R) (p : ℤ) {i j : ℤ} (k : ℤ)
    (h : i = j) (hk : p + j = k) {M : ModuleCat.{u} R} (f : M ⟶ B.X i) :
    (A.X p ◁ (f ≫ eqToHom (congrArg B.X h))) ≫ ιTensorObj A B p j k hk =
      (A.X p ◁ f) ≫ ιTensorObj A B p i k (h.symm ▸ hk) := by
  subst j
  simp

private theorem factor_d_zero_one (r : R) :
    (factor r).d 0 1 =
      algMap (Algebra.ofId R (loc r)) := by
  rfl

private theorem module_tensor_algMap {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    (algMap f ⊗ₘ algMap g) = algMap (Algebra.TensorProduct.map f g) := by
  ext : 1
  apply TensorProduct.ext'
  intro x y
  rfl

private theorem leftUnitor_as_algEquiv (A : Type u) [CommRing A] [Algebra R A] :
    (λ_ (ModuleCat.of R A)) = (Algebra.TensorProduct.lid R A).toLinearEquiv.toModuleIso := by
  apply Iso.ext
  ext : 1
  apply TensorProduct.ext'
  intro x y
  rfl

/-- Extending the denominator set in a principal localization. -/
private noncomputable def localizationMap (p q : R) (h : p ∣ q) : loc p →ₐ[R] loc q :=
  Specs.CommutativeAlgebraNotes.AugmentedCechComplex.localizationMap R p q h

private theorem localizationMap_unique (p q : R) (f g : loc p →ₐ[R] loc q) :
    f = g := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers p)
  ext x
  exact (f.commutes x).trans (g.commutes x).symm


private theorem algMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (g : B →ₐ[R] C) (f : A →ₐ[R] B) : algMap (g.comp f) = algMap f ≫ algMap g := rfl

private theorem termTensorIso_tail (r : R) (rs : List R) (b : Bool) (k l : ℤ)
    (s : Selection rs.length (k - headDegree b)) (t : Selection rs.length (l - headDegree b))
    (g : loc (product R rs s) →ₐ[R] loc (product R rs t)) :
    ∃ f : loc (product R (r :: rs) (⟨b, s⟩ : Selection (r :: rs).length k)) →ₐ[R]
        loc (product R (r :: rs) (⟨b, t⟩ : Selection (r :: rs).length l)),
      algMap f = (termTensorIso r rs k ⟨b, s⟩).inv ≫
        ((factor r).X (headDegree b) ◁ algMap g) ≫ (termTensorIso r rs l ⟨b, t⟩).hom := by
  cases b
  · refine ⟨g, ?_⟩
    change _ = (λ_ _).inv ≫ ((𝟙_ (ModuleCat.{u} R)) ◁ algMap g) ≫ (λ_ _).hom
    rw [leftUnitor_naturality, Iso.inv_hom_id_assoc]
  · let e := localizationTensorIso r (product R rs s)
    let e' := localizationTensorIso r (product R rs t)
    refine ⟨e'.toAlgHom.comp ((Algebra.TensorProduct.map (AlgHom.id R (loc r)) g).comp
      e.symm.toAlgHom), ?_⟩
    erw [algMap_comp, algMap_comp, ← module_tensor_algMap, id_tensorHom]
    rfl

private theorem termTensorIso_head (r : R) (rs : List R) (k l : ℤ)
    (s : Selection rs.length (k - headDegree false))
    (t : Selection rs.length (l - headDegree true))
    (g : loc (product R rs s) →ₐ[R] loc (product R rs t)) :
    ∃ f : loc (product R (r :: rs) (⟨false, s⟩ : Selection (r :: rs).length k)) →ₐ[R]
        loc (product R (r :: rs) (⟨true, t⟩ : Selection (r :: rs).length l)),
      algMap f = (termTensorIso r rs k ⟨false, s⟩).inv ≫
        ((factor r).d 0 1 ⊗ₘ algMap g) ≫ (termTensorIso r rs l ⟨true, t⟩).hom := by
  let e := Algebra.TensorProduct.lid R (loc (product R rs s))
  let e' := localizationTensorIso r (product R rs t)
  refine ⟨e'.toAlgHom.comp ((Algebra.TensorProduct.map (Algebra.ofId R (loc r)) g).comp
    e.symm.toAlgHom), ?_⟩
  erw [algMap_comp, algMap_comp, ← module_tensor_algMap, factor_d_zero_one]
  simp only [Category.assoc]
  change e.toLinearEquiv.toModuleIso.inv ≫ _ = (λ_ (term R rs s)).inv ≫ _
  rw [leftUnitor_as_algEquiv]
  rfl

set_option maxHeartbeats 450000 in
private theorem unsigned_insertion (rs : List R) (k : ℤ) (s : Selection rs.length k)
    (a : Fin rs.length) (ha : selected s a = false) :
    ∃ (t : Selection rs.length (k + 1))
      (g : loc (product R rs s) →ₐ[R] loc (product R rs t)),
      (∀ j, selected t j = (decide (j = a) || selected s j)) ∧
      summandι rs k s ≫ insertionMap false rs a k = algMap g ≫ summandι rs (k + 1) t := by
  induction rs generalizing k with
  | nil => exact Fin.elim0 a
  | cons r rs ih =>
    induction a using Fin.cases with
    | zero =>
      rcases s with ⟨b, s⟩
      have hb : b = false := ha
      subst b
      have h : k - headDegree false = k + 1 - headDegree true := by
        simp [headDegree]
      let t : Selection rs.length (k + 1 - headDegree true) := h ▸ s
      let g := castLocalization rs h s
      obtain ⟨f, hf⟩ := termTensorIso_head r rs k (k + 1) s t g
      refine ⟨⟨true, t⟩, f, ?_, ?_⟩
      · intro j
        induction j using Fin.cases with
        | zero => rfl
        | succ j =>
          change selected t j = (decide (j.succ = 0) || selected s j)
          simp [t, selected_cast]
      · have hc :
            ((factor r).X 1 ◁ (algMap g ≫ summandι rs (k + 1 - headDegree true) t)) ≫
                (headCofan r (CechComplex rs) (k + 1)).inj true =
              ((factor r).X 1 ◁ summandι rs (k - headDegree false) s) ≫
                ιTensorObj (factor r) (CechComplex rs) 1 (k - headDegree false) (k + 1)
                  (by simp [headDegree]; omega) := by
          dsimp only [g, t]
          rw [castLocalization_ι]
          exact ιTensorObj_whisker_cast (factor r) (CechComplex rs) 1 (k + 1) h
            (by simp [headDegree]; omega)
            (summandι rs (k - headDegree false) s)
        have hw := whisker_exchange_assoc ((factor r).d 0 1)
          (summandι rs (k - headDegree false) s)
          (ιTensorObj (factor r) (CechComplex rs) 1 (k - headDegree false) (k + 1)
            (by simp [headDegree]; omega))
        rw [summandι_insert_zero, hf, summandι]
        simp only [headInsertion, tensorHom_def, Category.assoc, Iso.hom_inv_id_assoc,
          ← whiskerLeft_comp_assoc]
        erw [hw, hc]
        rfl
    | succ a =>
      rcases s with ⟨b, s⟩
      have ha' : selected s a = false := ha
      obtain ⟨t₀, g₀, ht₀, hg₀⟩ := ih (k - headDegree b) s a ha'
      have h : k - headDegree b + 1 = k + 1 - headDegree b := by omega
      let t : Selection rs.length (k + 1 - headDegree b) := h ▸ t₀
      let g := (castLocalization rs h t₀).comp g₀
      obtain ⟨f, hf⟩ := termTensorIso_tail r rs b k (k + 1) s t g
      refine ⟨⟨b, t⟩, f, ?_, ?_⟩
      · intro j
        induction j using Fin.cases with
        | zero => simp [selected, Ne.symm (Fin.succ_ne_zero a)]
        | succ j =>
          change selected t j = (decide (j.succ = a.succ) || selected s j)
          simp [t, selected_cast, ht₀]
      · have hg : algMap g ≫ summandι rs (k + 1 - headDegree b) t =
            (summandι rs (k - headDegree b) s ≫ insertionMap false rs a (k - headDegree b)) ≫
              eqToHom (congrArg (CechComplex rs).X h) := by
          let e := eqToHom (congrArg (CechComplex rs).X h)
          calc
            algMap g ≫ summandι rs (k + 1 - headDegree b) t =
                algMap g₀ ≫ (algMap (castLocalization rs h t₀) ≫
                  summandι rs (k + 1 - headDegree b) t) :=
              (congrArg (· ≫ summandι rs (k + 1 - headDegree b) t)
                (algMap_comp (castLocalization rs h t₀) g₀)).trans
                  (Category.assoc (algMap g₀) (algMap (castLocalization rs h t₀))
                    (summandι rs (k + 1 - headDegree b) t))
            _ = algMap g₀ ≫ (summandι rs (k - headDegree b + 1) t₀ ≫ e) :=
              congrArg (algMap g₀ ≫ ·) (castLocalization_ι rs h t₀)
            _ = (summandι rs (k - headDegree b) s ≫
                insertionMap false rs a (k - headDegree b)) ≫ e :=
              (Category.assoc _ _ _).symm.trans (congrArg (· ≫ e) hg₀.symm)
        rw [summandι_insert_succ, summandι, hf]
        simp only [Bool.false_eq_true, ite_false, one_smul, Category.assoc, Iso.hom_inv_id_assoc,
          ← whiskerLeft_comp_assoc, hg]
        apply congrArg ((termTensorIso r rs k ⟨b, s⟩).inv ≫ ·)
        exact (ιTensorObj_whisker_cast (factor r) (CechComplex rs) (headDegree b) (k + 1) h
          (by omega) (summandι rs (k - headDegree b) s ≫
            insertionMap false rs a (k - headDegree b))).symm

/-- Inserting an absent position extends the denominator set by that generator. -/
theorem summandι_insert_localization (rs : List R) (k : ℤ) (s : Selection rs.length k)
    (a : Fin rs.length) (ha : selected s a = false) :
    ∃ (t : Selection rs.length (k + 1)) (h : product R rs s ∣ product R rs t),
      (∀ j, selected t j = (decide (j = a) || selected s j)) ∧
      product R rs t = rs.get a * product R rs s ∧
      summandι rs k s ≫ insertionMap false rs a k =
        algMap (localizationMap (product R rs s) (product R rs t) h) ≫ summandι rs (k + 1) t := by
  obtain ⟨t, g, ht, hcomp⟩ := unsigned_insertion rs k s a ha
  have hset : (Finset.univ.filter fun j => selected t j = true) =
      insert a (Finset.univ.filter fun j => selected s j = true) := by
    ext j
    simp [ht]
  have hproduct : product R rs t = rs.get a * product R rs s := by
    rw [product_eq rs t, hset, Finset.prod_insert (by simp [ha]), product_eq rs s]
  have hdvd : product R rs s ∣ product R rs t := hproduct ▸ dvd_mul_left _ _
  refine ⟨t, hdvd, ht, hproduct, ?_⟩
  rw [hcomp, localizationMap_unique _ _ g (localizationMap _ _ hdvd)]


/-- The unique degree-zero summand is the base ring. -/
noncomputable def degreeZeroIso (rs : List R) :
    (CechComplex rs).X 0 ≅ ModuleCat.of R R := by
  let s₀ : Selection rs.length (0 : ℤ) := selectionOfSubset rs.length ∅
  have hempty (s : Selection rs.length (0 : ℤ)) :
      (Finset.univ.filter fun j => selected s j = true) = ∅ :=
    Finset.card_eq_zero.mp (Int.ofNat_eq_zero.mp (selection_card s))
  have h (s : Selection rs.length (0 : ℤ)) : s = s₀ := by
    apply (selectionEquiv rs.length 0).injective
    apply Subtype.ext
    exact (hempty s).trans (hempty s₀).symm
  let c := Cofan.mk (term R rs s₀)
    (fun s => eqToHom (congrArg (fun t => term R rs t) (h s)))
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk _ (fun t => t.inj s₀) ?_ ?_
    · intro t s
      obtain rfl := h s
      exact Category.id_comp _
    · intro t f hf
      exact (Category.id_comp f).symm.trans (hf s₀)
  have hprod : product R rs s₀ = 1 := by
    rw [product_eq, hempty, Finset.prod_empty]
  let e : term R rs s₀ ≅ ModuleCat.of R (Localization.Away (1 : R)) :=
    eqToIso (congrArg (fun r => ModuleCat.of R (Localization.Away r)) hprod)
  exact (summandCofanIsColimit rs 0).coconePointUniqueUpToIso hc ≪≫ e ≪≫
    (IsLocalization.atOne R (Localization.Away (1 : R))).symm.toLinearEquiv.toModuleIso

theorem degreeZeroTerm : Specs.CommutativeAlgebraNotes.AugmentedCechComplex.DegreeZeroTerm.{u} :=
  fun rs => ⟨degreeZeroIso rs⟩

/-- The source's direct-sum presentation, including the canonical insertion maps. -/
theorem ringTermFormula : Specs.CommutativeAlgebraNotes.AugmentedCechComplex.RingTermFormula.{u} := by
  intro R _ rs
  refine ⟨summandι rs, (fun k => ⟨summandCofanIsColimit rs k⟩),
    (fun k => ⟨selectionEquiv rs.length k, fun _ => rfl⟩),
    (fun _ s => product_eq rs s), ?_⟩
  intro k s
  refine ⟨(fun a => summandι rs k s ≫ insertionMap false rs a k), ?_,
    summandι_insert_eq_zero false rs k s, summandι_insert_localization rs k s⟩
  simpa only [← preceding_card] using summandι_differential rs k s

theorem moduleTermFormula :
    Specs.CommutativeAlgebraNotes.AugmentedCechComplex.ModuleTermFormula.{u} :=
  fun rs M k => ⟨moduleTerms rs M k⟩

end Cech
end CommutativeAlgebraNotes
