import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Linear.LinearFunctor

open CategoryTheory
open TensorProduct
open MvPowerSeries
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal

open ExteriorTensorProduct (Y S includeX includeY xToY)
open scoped ExteriorTensorProduct PowerSeriesDiagonal

universe u v w

variable (D : Type u) [CommRing D] (d : ℕ)

@[simp] theorem translate_left (add : Bool) (i : Fin d) :
    translate D d add (leftVar D d i) = translateFamily D d add (Sum.inl i) :=
  substAlgHom_X _ _

@[simp] theorem translate_right (add : Bool) (j : ExteriorTensorProduct.YIndex d) :
    translate D d add (MvPowerSeries.X (Sum.inr j)) = MvPowerSeries.X (Sum.inr j) :=
  substAlgHom_X _ _

theorem coordinateChange : Spec.CoordinateChange := by
  intro D _ d
  have comp_eq (a b : Bool) (h : a ≠ b) (f : S D d d) :
      translate D d a (translate D d b f) = f := by
    have he : (fun i ↦ translate D d a (translateFamily D d b i)) =
        (MvPowerSeries.X : Index d → S D d d) := by
      funext i
      cases i with
      | inl i =>
        cases a <;> cases b <;> try contradiction
        · change translate D d false (leftVar D d i + rightVar D d i) = _
          rw [map_add, translate_left, show translate D d false (rightVar D d i) = _ from
            translate_right D d false (ULift.up i)]
          exact sub_add_cancel _ _
        · change translate D d true (leftVar D d i - rightVar D d i) = _
          rw [map_sub, translate_left, show translate D d true (rightVar D d i) = _ from
            translate_right D d true (ULift.up i)]
          exact add_sub_cancel_right _ _
      | inr j => exact translate_right D d a j
    simp only [translate, substAlgHom_apply]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero
      (translateFamily_constantCoeff D d b)) (hasSubst_of_constantCoeff_zero
      (translateFamily_constantCoeff D d a))]
    simp only [translate, substAlgHom_apply] at he
    rw [he, subst_self]
    rfl
  exact ⟨comp_eq false true (by decide), comp_eq true false (by decide)⟩

/-- The change from the old coordinates to the coordinates z,y. -/
noncomputable def changeCoordinates : S D d d ≃ₐ[D] S D d d :=
  AlgEquiv.ofAlgHom (translate D d true) (translate D d false)
    (AlgHom.ext (coordinateChange D d).2) (AlgHom.ext (coordinateChange D d).1)

theorem identifyCopies : Spec.IdentifyCopies := by
  intro D _ d
  constructor
  · rw [identify, includeX, rename_comp_rename]
    exact rename_id
  · rw [identify, includeY, rename_comp_rename]
    rfl

private theorem mem_span_vars_of_coeff {σ : Type*} (s : Finset σ)
    (f : MvPowerSeries σ D)
    (hf : ∀ m : σ →₀ ℕ, (∀ i ∈ s, m i = 0) → coeff m f = 0) :
    f ∈ Ideal.span ((MvPowerSeries.X (R := D)) '' (s : Set σ)) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    have h : f = 0 := by
      ext m
      exact hf m (by simp)
    simp [h]
  | @insert i s hi ih =>
    let g : MvPowerSeries σ D := fun m => if m i = 0 then coeff m f else 0
    let q : MvPowerSeries σ D := fun m => coeff (m + Finsupp.single i 1) f
    have hg : g ∈ Ideal.span ((MvPowerSeries.X (R := D)) '' (s : Set σ)) := by
      apply ih
      intro m hm
      change (if m i = 0 then coeff m f else 0) = 0
      split
      · exact hf m (by simpa [Finset.mem_insert, or_imp, forall_and] using And.intro ‹m i = 0› hm)
      · rfl
    have hsplit : f = g + MvPowerSeries.X i * q := by
      ext m
      rw [map_add, MvPowerSeries.X_def, coeff_monomial_mul]
      change coeff m f =
        (if m i = 0 then coeff m f else 0) +
        (if Finsupp.single i 1 ≤ m then 1 * coeff (m - Finsupp.single i 1 + Finsupp.single i 1) f
          else 0)
      have hle : Finsupp.single i 1 ≤ m ↔ m i ≠ 0 := by
        rw [Finsupp.single_le_iff]
        omega
      by_cases hz : m i = 0
      · simp [hz, hle]
      · have h := hle.mpr hz
        simp [hz, h, tsub_add_cancel_of_le h]
    rw [hsplit]
    refine Ideal.add_mem _ (Ideal.span_mono (Set.image_mono ?_) hg) ?_
    · exact_mod_cast Finset.subset_insert i s
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, Finset.mem_insert_self _ _, rfl⟩)

private theorem ker_killCompl {σ τ : Type*} [Finite τ] (e : σ ↪ τ) :
    RingHom.ker (killCompl (R := D) e).toRingHom =
      Ideal.span ((MvPowerSeries.X (R := D)) '' (Set.range e)ᶜ) := by
  classical
  let := Fintype.ofFinite τ
  apply le_antisymm
  · intro f hf
    let s := Finset.univ.filter fun i => i ∉ Set.range e
    have hs : (s : Set τ) = (Set.range e)ᶜ := by ext; simp [s]
    rw [← hs]
    apply mem_span_vars_of_coeff D s f
    intro m hm
    have hr : m ∈ Set.range (Finsupp.embDomain e) := by
      rw [Finsupp.mem_range_embDomain_iff]
      intro i hi
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hi) (hm i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
    obtain ⟨n, rfl⟩ := hr
    have hf' : killCompl (R := D) e f = 0 := hf
    simpa only [coeff_killCompl, map_zero] using congrArg (coeff n) hf'
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact killCompl_X_eq_zero hi


private theorem translate_includeY (b : Bool) (p : Y D d) :
    translate D d b (includeY D d d p) = includeY D d d p := by
  have h := hasSubst_of_constantCoeff_zero (translateFamily_constantCoeff D d b)
  let j : ExteriorTensorProduct.YIndex d → Index d := Sum.inr
  change substAlgHom h (rename j p) = rename j p
  simp only [substAlgHom_apply, rename_eq_subst,
    subst_comp_subst_apply (HasSubst.X_comp j) h]
  congr 1
  funext i
  exact (substAlgHom_apply h _).symm.trans (translate_right D d b i)

private noncomputable abbrev leftIdeal : Ideal (S D d d) := Ideal.span (Set.range (leftVar D d))

private theorem map_leftIdeal :
    (leftIdeal D d).map (translate D d false).toRingHom = diagonalIdeal D d := by
  rw [leftIdeal, Ideal.map_span]
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (translate_left D d false i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, translate_left D d false i⟩

theorem identifyKernel : Spec.IdentifyKernel := by
  intro D _ d
  let e : ExteriorTensorProduct.YIndex d ↪ Index d := ⟨Sum.inr, Sum.inr_injective⟩
  have hker : RingHom.ker (killCompl (R := D) e).toRingHom = leftIdeal D d := by
    rw [ker_killCompl]
    congr 1
    ext t
    constructor
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | inl i => exact ⟨i, rfl⟩
      | inr j => exact False.elim (hi ⟨j, rfl⟩)
    · rintro ⟨i, rfl⟩
      refine ⟨Sum.inl i, ?_, rfl⟩
      rintro ⟨j, hj⟩
      cases hj
  have hincl : diagonalIdeal D d ≤ RingHom.ker (identify D d).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change identify D d (leftVar D d i - rightVar D d i) = 0
    simp [identify, leftVar, rightVar]
  refine le_antisymm (fun f hf => ?_) hincl
  let g := translate D d true f
  let p := killCompl (R := D) e g
  have hg : g - includeY D d d p ∈ leftIdeal D d := by
    rw [← hker]
    change killCompl e (g - rename e p) = 0
    rw [map_sub, killCompl_rename_app, sub_self]
  have hmem : f - includeY D d d p ∈ diagonalIdeal D d := by
    have hm := Ideal.mem_map_of_mem (translate D d false).toRingHom hg
    rwa [map_leftIdeal, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub,
      (coordinateChange D d).1 f, translate_includeY] at hm
  have hp : identify D d (includeY D d d p) = 0 := by
    have hh : identify D d (f - includeY D d d p) = 0 := hincl hmem
    rw [map_sub, show identify D d f = 0 from hf, zero_sub, neg_eq_zero] at hh
    exact hh
  have hp0 : p = 0 := by
    have he := AlgHom.congr_fun (identifyCopies D d).2 p
    exact (xToY D d).symm.injective (he.symm.trans (hp.trans (map_zero _).symm))
  simpa [hp0] using hmem

theorem identify_surjective : Function.Surjective (identify D d) := fun r =>
  ⟨includeX D d d r, AlgHom.congr_fun (identifyCopies D d).1 r⟩

/-- The ring of the diagonal, with the quotient map identifying x and y. -/
noncomputable def diagonalQuotientEquiv :
    (S D d d ⧸ diagonalIdeal D d) ≃ₐ[D] ExteriorTensorProduct.X D d :=
  (Ideal.quotientEquivAlgOfEq D (identifyKernel D d).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (identify_surjective D d))

@[simp] theorem diagonalQuotientEquiv_mk (s : S D d d) :
    diagonalQuotientEquiv D d (Ideal.Quotient.mk _ s) = identify D d s := rfl

theorem ofList_difference :
    Ideal.ofList (List.ofFn (difference D d)) = diagonalIdeal D d := by
  exact congrArg Ideal.span (Set.ext fun s => List.mem_ofFn' _ s)

private theorem variables_regular {σ : Type*} [Finite σ] [Nontrivial D]
    (l : List σ) (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPowerSeries σ D) (l.map (MvPowerSeries.X (R := D))) := by
  classical
  constructor
  · constructor
    intro i hi
    have hil : i < l.length := by simpa using hi
    let e : {s : σ // s ∉ l.take i} ↪ σ := Function.Embedding.subtype _
    have hker : RingHom.ker (killCompl (R := D) e).toRingHom =
        Ideal.ofList ((l.map (MvPowerSeries.X (R := D))).take i) := by
      rw [ker_killCompl, ← List.map_take]
      congr 1
      ext x
      simp [e, Set.mem_image]
      simp only [← List.map_take, List.mem_map]
    have hkeep : l[i] ∉ l.take i := by
      rw [List.mem_take_iff_getElem]
      rintro ⟨j, hj, he⟩
      have := hl.getElem_inj_iff.mp he
      omega
    let k := killCompl (R := D) e
    have hk : Function.Surjective k := fun p => ⟨rename e p, killCompl_rename_app (e := e) p⟩
    have hsmul (I : Ideal (MvPowerSeries σ D)) :
        I • (⊤ : Submodule (MvPowerSeries σ D) (MvPowerSeries σ D)) = I := I.mul_top
    rw [hsmul, ← hker]
    let eqv := Ideal.quotientKerAlgEquivOfSurjective hk
    intro p q hpq
    apply eqv.injective
    change Ideal.Quotient.mk _ ((l.map (MvPowerSeries.X (R := D)))[i]) * p =
      Ideal.Quotient.mk _ ((l.map (MvPowerSeries.X (R := D)))[i]) * q at hpq
    -- Transport multiplication to the power series in the surviving variables.
    rw [List.getElem_map] at hpq
    have heq := (eqv.map_mul _ p).symm.trans
      ((congrArg eqv hpq).trans (eqv.map_mul _ q))
    have hvar : eqv (Ideal.Quotient.mk _ (MvPowerSeries.X l[i])) =
        MvPowerSeries.X (⟨l[i], hkeep⟩ : {s : σ // s ∉ l.take i}) :=
      killCompl_X (e := e) ⟨l[i], hkeep⟩
    change eqv (Ideal.Quotient.mk _ (MvPowerSeries.X l[i])) * eqv p =
      eqv (Ideal.Quotient.mk _ (MvPowerSeries.X l[i])) * eqv q at heq
    rw [hvar] at heq
    ext m
    have hc := congrArg (coeff (Finsupp.single (⟨l[i], hkeep⟩ :
      {s : σ // s ∉ l.take i}) 1 + m)) heq
    simpa only [MvPowerSeries.X_def, coeff_add_monomial_mul, one_mul] using hc
  · change (⊤ : Ideal (MvPowerSeries σ D)) ≠ Ideal.ofList
        (l.map (MvPowerSeries.X (R := D))) * ⊤
    rw [Ideal.mul_top]
    intro h
    have hone : (1 : MvPowerSeries σ D) ∈ Ideal.ofList (l.map (MvPowerSeries.X (R := D))) :=
      h ▸ Submodule.mem_top
    have hin : Ideal.ofList (l.map (MvPowerSeries.X (R := D))) ≤ RingHom.ker constantCoeff := by
      apply Ideal.span_le.mpr
      intro x hx
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
      exact constantCoeff_X s
    exact one_ne_zero ((constantCoeff_one (σ := σ) (R := D)).symm.trans (hin hone))

theorem diagonalRegular : Spec.DiagonalRegular := by
  intro D _ _ d
  let l : List (Index d) := List.ofFn Sum.inl
  have hl : l.Nodup := by
    apply List.nodup_iff_injective_get.mpr
    intro i j h
    apply Fin.ext
    simpa [l, List.get_eq_getElem] using h
  have h := variables_regular D l hl
  have tr : (l.map (MvPowerSeries.X (R := D))).map (changeCoordinates D d).symm =
      List.ofFn (difference D d) := by
    simp only [l, List.map_ofFn, Function.comp_def]
    exact congrArg List.ofFn (funext fun i => translate_left D d false i)
  rw [← tr]
  refine (AddEquiv.isRegular_congr (e := (changeCoordinates D d).symm.toAddEquiv) ?_).mp h
  exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x =>
    (changeCoordinates D d).symm.map_mul r x)


theorem quotientPresentation : Spec.QuotientPresentation :=
  fun D _ d => ⟨diagonalQuotientEquiv D d, diagonalQuotientEquiv_mk D d⟩

section Tensor

noncomputable local instance : Algebra (Y D d) (R D d) :=
  (xToY D d).symm.toRingHom.toAlgebra

@[simp] theorem identify_includeX (r : R D d) :
    identify D d (includeX D d d r) = r :=
  AlgHom.congr_fun (identifyCopies D d).1 r

@[simp] theorem identify_includeY (r : Y D d) :
    identify D d (includeY D d d r) = (xToY D d).symm r :=
  AlgHom.congr_fun (identifyCopies D d).2 r

local instance : IsScalarTower (R D d) (S D d d) (R D d) :=
  IsScalarTower.of_algebraMap_eq fun r => (identify_includeX D d r).symm

local instance : IsScalarTower (Y D d) (S D d d) (R D d) :=
  IsScalarTower.of_algebraMap_eq fun r => (identify_includeY D d r).symm

variable (M : Type v) (N : Type w)
  [AddCommGroup M] [Module (R D d) M] [AddCommGroup N] [Module (R D d) N]

open ExteriorTensorProduct (OnY diagonal)

/-- Extend scalars to the diagonal and combine the two balancing relations. -/
noncomputable def tensorBaseChangeEquiv :
    (R D d ⊗[S D d d] diagonal D d M N) ≃ₗ[R D d] (M ⊗[R D d] N) := by
  letI : Module (Y D d) M := Module.compHom M (xToY D d).symm.toRingHom
  letI : Module (R D d) (OnY N) := inferInstanceAs (Module (R D d) N)
  letI : IsScalarTower (Y D d) (R D d) M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower (Y D d) (R D d) (OnY N) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : CompatibleSMul (Y D d) (R D d) M (OnY N) := ⟨fun r m n => by
    obtain ⟨a, rfl⟩ := (xToY D d).symm.surjective r
    change (a • m) ⊗ₜ[Y D d] n = m ⊗ₜ[Y D d] (a • n)
    exact smul_tmul _ _ _⟩
  let assoc := (AlgebraTensorModule.assoc (Y D d) (S D d d) (R D d)
    (R D d) (S D d d ⊗[R D d] M) (OnY N)).symm
  let cancel := AlgebraTensorModule.cancelBaseChange (R D d) (S D d d) (R D d) (R D d) M
  let reduce := TensorProduct.equivOfCompatibleSMul (R D d) (Y D d) (R D d) M (OnY N)
  exact assoc ≪≫ₗ
    AlgebraTensorModule.congr (cancel ≪≫ₗ TensorProduct.lid (R D d) M)
      (LinearEquiv.refl (Y D d) (OnY N)) ≪≫ₗ reduce

@[simp] theorem tensorBaseChangeEquiv_tmul (r : R D d) (s : S D d d) (m : M) (n : N) :
    tensorBaseChangeEquiv D d M N
      (r ⊗ₜ[S D d d] ((s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] ExteriorTensorProduct.toY n)) =
      (r * identify D d s) • (m ⊗ₜ[R D d] n) := by
  change (identify D d s * r) • (m ⊗ₜ[R D d] n) = _
  rw [mul_comm]

theorem tensorBaseChange : Spec.TensorBaseChange :=
  fun D _ d M N _ _ _ _ =>
    ⟨tensorBaseChangeEquiv D d M N, tensorBaseChangeEquiv_tmul D d M N⟩

private noncomputable def quotientRingLinearEquiv :
    (S D d d ⧸ diagonalIdeal D d) ≃ₗ[S D d d] R D d where
  __ := (diagonalQuotientEquiv D d).toAddEquiv
  map_smul' s q := by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
    change diagonalQuotientEquiv D d (Ideal.Quotient.mk _ (s * t)) =
      identify D d s * diagonalQuotientEquiv D d (Ideal.Quotient.mk _ t)
    rw [diagonalQuotientEquiv_mk, map_mul, diagonalQuotientEquiv_mk]

/-- Quotienting a module by the diagonal ideal agrees with extending scalars to R. -/
noncomputable def diagonalReductionBaseChangeEquiv (T : Type v)
    [AddCommGroup T] [Module (S D d d) T] :
    diagonalReduction D d T ≃ₗ[S D d d] (R D d ⊗[S D d d] T) :=
  (quotTensorEquivQuotSMul T (diagonalIdeal D d)).symm ≪≫ₗ
    TensorProduct.congr (quotientRingLinearEquiv D d) (LinearEquiv.refl _ _)

@[simp] theorem diagonalReductionBaseChangeEquiv_mk {T : Type v}
    [AddCommGroup T] [Module (S D d d) T] (t : T) :
    diagonalReductionBaseChangeEquiv D d T (Submodule.Quotient.mk t) = 1 ⊗ₜ[S D d d] t := by
  change quotientRingLinearEquiv D d 1 ⊗ₜ[S D d d] t = _
  rw [show quotientRingLinearEquiv D d 1 = 1 from (diagonalQuotientEquiv D d).map_one]

theorem diagonalReductionBaseChangeEquiv_map {T U : Type*}
    [AddCommGroup T] [AddCommGroup U] [Module (S D d d) T] [Module (S D d d) U]
    (f : T →ₗ[S D d d] U) (t : T) :
    f.baseChange (R D d) (diagonalReductionBaseChangeEquiv D d T (Submodule.Quotient.mk t)) =
      diagonalReductionBaseChangeEquiv D d U (Submodule.Quotient.mk (f t)) := by
  rw [diagonalReductionBaseChangeEquiv_mk, diagonalReductionBaseChangeEquiv_mk,
    LinearMap.baseChange_tmul]

theorem reductionBaseChange : Spec.ReductionBaseChange :=
  fun D _ d T _ _ =>
    ⟨diagonalReductionBaseChangeEquiv D d T, diagonalReductionBaseChangeEquiv_mk D d⟩

/-- The quotient of the exterior product by the diagonal ideal is the ordinary tensor product. -/
noncomputable def tensorQuotientEquiv :
    diagonalReduction D d (diagonal D d M N)
      ≃ₗ[S D d d] ↥((restrictDiagonal D d).obj (ModuleCat.of _ (M ⊗[R D d] N))) := by
  letI : Module (S D d d) (M ⊗[R D d] N) :=
    ((restrictDiagonal D d).obj (ModuleCat.of _ (M ⊗[R D d] N))).isModule
  letI : IsScalarTower (S D d d) (R D d) (M ⊗[R D d] N) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact diagonalReductionBaseChangeEquiv D d (diagonal D d M N) ≪≫ₗ
    (tensorBaseChangeEquiv D d M N).restrictScalars (S D d d)

@[simp] theorem tensorQuotientEquiv_mk (s : S D d d) (m : M) (n : N) :
    tensorQuotientEquiv D d M N
        (Submodule.Quotient.mk ((s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] ExteriorTensorProduct.toY n)) =
      (identify D d s • (m ⊗ₜ[R D d] n) : M ⊗[R D d] N) := by
  let t : diagonal D d M N :=
    (s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] ExteriorTensorProduct.toY n
  exact (congrArg (tensorBaseChangeEquiv D d M N) (diagonalReductionBaseChangeEquiv_mk D d t)).trans
    ((tensorBaseChangeEquiv_tmul D d M N 1 s m n).trans (by rw [one_mul]))

theorem tensorQuotient : Spec.TensorQuotient :=
  fun D _ d M N _ _ _ _ =>
    ⟨tensorQuotientEquiv D d M N, tensorQuotientEquiv_mk D d M N⟩

end Tensor

section TotalComparison

open CategoryTheory.Limits
open HomologicalComplex₂

variable {C E : Type*} [Category* C] [Category* E] [Preadditive C] [Preadditive E]
variable {ι : Type} [DecidableEq ι] (c : ComplexShape ι) [TotalComplexShape c c c]
variable (F : C ⥤ E) [F.Additive] [PreservesColimitsOfSize.{0, 0} F]
variable (K : HomologicalComplex₂ C c c) (L : HomologicalComplex₂ E c c)
variable [K.HasTotal c] [L.HasTotal c]
variable (e : ∀ i j, F.obj ((K.X i).X j) ≅ (L.X i).X j)

private abbrev TotalIndex (n : ι) :=
  {p : ι × ι // ComplexShape.π c c c p = n}

private noncomputable def mappedTotalCofanIsColimit (n : ι) :
    IsColimit (Cofan.mk (F.obj ((K.total c).X n)) (fun p : TotalIndex c n =>
      F.map (K.ιTotal c p.1.1 p.1.2 n p.2)) :
      Cofan (fun p : TotalIndex c n => F.obj ((K.X p.1.1).X p.1.2))) :=
  isColimitCofanMkObjOfIsColimit F _ _ (K.toGradedObject.isColimitCofanMapObj _ n)

private noncomputable def comparisonCofanIsColimit (n : ι) :
    IsColimit (Cofan.mk ((L.total c).X n) (fun p : TotalIndex c n =>
      (e p.1.1 p.1.2).hom ≫ L.ιTotal c p.1.1 p.1.2 n p.2) :
      Cofan (fun p : TotalIndex c n => F.obj ((K.X p.1.1).X p.1.2))) := by
  refine Cofan.IsColimit.mk _ (fun s => L.totalDesc
    (fun i j h => (e i j).inv ≫ s.inj ⟨(i, j), h⟩)) ?_ ?_
  · rintro s ⟨⟨i, j⟩, h⟩
    simp
  · intro s f hf
    apply HomologicalComplex₂.total.hom_ext
    intro i j h
    have h' := hf ⟨(i, j), h⟩
    simpa [Category.assoc, ← cancel_epi (e i j).hom] using h'

private noncomputable def totalComponentIso (n : ι) :
    F.obj ((K.total c).X n) ≅ (L.total c).X n :=
  (mappedTotalCofanIsColimit c F K n).coconePointUniqueUpToIso
    (comparisonCofanIsColimit c F K L e n)

omit [F.Additive] in
@[reassoc] private theorem ι_totalComponentIso (i j n : ι)
    (h : ComplexShape.π c c c (i, j) = n) :
    F.map (K.ιTotal c i j n h) ≫ (totalComponentIso c F K L e n).hom =
      (e i j).hom ≫ L.ιTotal c i j n h :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (mappedTotalCofanIsColimit c F K n) (comparisonCofanIsColimit c F K L e n)
    ⟨⟨(i, j), h⟩⟩

private theorem ιOrZero_totalComponentIso (i j n : ι) :
    F.map (K.ιTotalOrZero c i j n) ≫ (totalComponentIso c F K L e n).hom =
      (e i j).hom ≫ L.ιTotalOrZero c i j n := by
  by_cases h : ComplexShape.π c c c (i, j) = n
  · simpa only [ιTotalOrZero_eq _ _ _ _ _ h] using ι_totalComponentIso c F K L e i j n h
  · simp only [ιTotalOrZero_eq_zero _ _ _ _ _ h, F.map_zero, zero_comp, comp_zero]

variable
  (h₁ : ∀ i i' j, F.map ((K.d i i').f j) ≫ (e i' j).hom =
    (e i j).hom ≫ (L.d i i').f j)
  (h₂ : ∀ i j j', F.map ((K.X i).d j j') ≫ (e i j').hom =
    (e i j).hom ≫ (L.X i).d j j')

include h₁ in
private theorem d₁_totalComponentIso (i j n : ι) :
    F.map (K.d₁ c i j n) ≫ (totalComponentIso c F K L e n).hom =
      (e i j).hom ≫ L.d₁ c i j n := by
  change F.map (ComplexShape.ε₁ c c c (i, j) •
      ((K.d i (c.next i)).f j ≫ K.ιTotalOrZero c (c.next i) j n)) ≫ _ =
    _ ≫ (ComplexShape.ε₁ c c c (i, j) •
      ((L.d i (c.next i)).f j ≫ L.ιTotalOrZero c (c.next i) j n))
  rw [F.map_units_smul, Linear.units_smul_comp, F.map_comp, Category.assoc,
    ιOrZero_totalComponentIso, ← Category.assoc, h₁, Category.assoc, Linear.comp_units_smul]

include h₂ in
private theorem d₂_totalComponentIso (i j n : ι) :
    F.map (K.d₂ c i j n) ≫ (totalComponentIso c F K L e n).hom =
      (e i j).hom ≫ L.d₂ c i j n := by
  change F.map (ComplexShape.ε₂ c c c (i, j) •
      ((K.X i).d j (c.next j) ≫ K.ιTotalOrZero c i (c.next j) n)) ≫ _ =
    _ ≫ (ComplexShape.ε₂ c c c (i, j) •
      ((L.X i).d j (c.next j) ≫ L.ιTotalOrZero c i (c.next j) n))
  rw [F.map_units_smul, Linear.units_smul_comp, F.map_comp, Category.assoc,
    ιOrZero_totalComponentIso, ← Category.assoc, h₂, Category.assoc, Linear.comp_units_smul]

/-- A coproduct-preserving additive functor takes the signed total to the signed total
of any compatible bicomplex of its images. -/
private noncomputable def mapTotalIso :
    (F.mapHomologicalComplex c).obj (K.total c) ≅ L.total c :=
  HomologicalComplex.Hom.isoOfComponents (totalComponentIso c F K L e) <| by
    intro n n' _
    apply Cofan.IsColimit.hom_ext (mappedTotalCofanIsColimit c F K n)
    rintro ⟨⟨i, j⟩, h⟩
    change
      F.map (K.ιTotal c i j n h) ≫ (totalComponentIso c F K L e n).hom ≫ (L.total c).d n n' =
      F.map (K.ιTotal c i j n h) ≫ F.map ((K.total c).d n n') ≫
        (totalComponentIso c F K L e n').hom
    rw [ι_totalComponentIso_assoc, ← CategoryTheory.Functor.map_comp_assoc,
      HomologicalComplex₂.total_d, HomologicalComplex₂.total_d]
    simp only [Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      F.map_add,
      Preadditive.add_comp, d₁_totalComponentIso c F K L e h₁,
      d₂_totalComponentIso c F K L e h₂]

end TotalComparison

section Complexes

open scoped MonoidalCategory
open ExteriorTensorProduct (toY)

local instance : (extendDiagonal D d).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change extendDiagonalTmul D d _ 1 ((f + g) x) =
      extendDiagonalTmul D d _ 1 (f x) + extendDiagonalTmul D d _ 1 (g x)
    exact TensorProduct.tmul_add _ _ _

/-- The module comparison as an isomorphism in the category of diagonal-ring modules. -/
noncomputable def exteriorPairBaseChangeIso (M N : ModuleCat.{u} (R D d)) :
    (extendDiagonal D d).obj (exteriorPair M N) ≅ M ⊗ N :=
  (tensorBaseChangeEquiv D d M N).toModuleIso

@[simp] theorem exteriorPairBaseChangeIso_tmul (M N : ModuleCat.{u} (R D d))
    (r : R D d) (s : S D d d) (m : M) (n : N) :
    (exteriorPairBaseChangeIso D d M N).hom
      (extendDiagonalTmul D d (exteriorPair M N) r ((s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] toY n)) =
      (show (M ⊗ N : ModuleCat.{u} (R D d)) from
        (r * identify D d s) • (m ⊗ₜ[R D d] n)) :=
  tensorBaseChangeEquiv_tmul D d M N r s m n

theorem exteriorPairBaseChangeIso_natural {M M' N N' : ModuleCat.{u} (R D d)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (extendDiagonal D d).map (exteriorPairMap f g) ≫ (exteriorPairBaseChangeIso D d M' N').hom =
      (exteriorPairBaseChangeIso D d M N).hom ≫ (f ⊗ₘ g) := by
  let adj := ModuleCat.extendRestrictScalarsAdj (identify D d).toRingHom
  apply (adj.homEquiv _ _).injective
  apply exteriorPair_hom_ext
  intro s m n
  change tensorBaseChangeEquiv D d M' N'
    (1 ⊗ₜ[S D d d] ((s ⊗ₜ[R D d] f m) ⊗ₜ[Y D d] toY (g n))) =
    TensorProduct.map f.hom g.hom (tensorBaseChangeEquiv D d M N
      (1 ⊗ₜ[S D d d] ((s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] toY n)))
  rw [tensorBaseChangeEquiv_tmul, tensorBaseChangeEquiv_tmul, map_smul, TensorProduct.map_tmul]

variable {ι : Type} [AddMonoid ι] [DecidableEq ι] (c : ComplexShape ι) [c.TensorSigns]
variable (P Q : HomologicalComplex (ModuleCat.{u} (R D d)) c)

/-- Degreewise diagonal reduction identifies the exterior and ordinary signed tensor totals. -/
noncomputable def totalBaseChangeIso :
    ((extendDiagonal D d).mapHomologicalComplex c).obj ((exteriorBicomplex D d P Q).total c)
      ≅ (ordinaryBicomplex D d P Q).total c :=
  mapTotalIso c (extendDiagonal D d) (exteriorBicomplex D d P Q) (ordinaryBicomplex D d P Q)
    (fun i j => exteriorPairBaseChangeIso D d (P.X i) (Q.X j))
    (fun i i' j => exteriorPairBaseChangeIso_natural D d (P.d i i') (𝟙 (Q.X j)))
    (fun i j j' => exteriorPairBaseChangeIso_natural D d (𝟙 (P.X i)) (Q.d j j'))

theorem totalBaseChange : Spec.TotalBaseChange := by
  intro D _ d ι _ _ c _ P Q
  refine ⟨totalBaseChangeIso D d c P Q, ?_⟩
  intro i j k h r s m n
  have hι := ι_totalComponentIso c (extendDiagonal D d) (exteriorBicomplex D d P Q)
    (ordinaryBicomplex D d P Q)
    (fun i j => exteriorPairBaseChangeIso D d (P.X i) (Q.X j)) i j k h
  exact (ConcreteCategory.congr_hom hι _).trans
    (congrArg (fun x => (ordinaryBicomplex D d P Q).ιTotal c i j k h x)
      (exteriorPairBaseChangeIso_tmul D d (P.X i) (Q.X j) r s m n))

end Complexes

end CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal
