import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CompleteIntersectionConormal
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.KoszulZeroLocus
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeDifferentials

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex

universe u

namespace DerivedFormalization.Affine.CompleteIntersectionConormal

open Specs.DerivedFormalization.Affine.CompleteIntersectionConormal
open Specs.DerivedFormalization.Affine.KoszulZeroLocus (quotientAlg)

noncomputable section

variable {k : Type u} [Field k] [CharZero k] {s r : ℕ}
variable (f : Fin r → Polynomial k s)

omit [CharZero k] in
private theorem stalkTerm_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((quotientStalk f).X i) :=
  isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of (Quotient f) (Quotient f)) i hi

omit [CharZero k] in
private theorem cochain_ext_stalk {n p : ℤ} (hp : p + n = 0)
    {a b : Cochain (conormal f) (quotientStalk f) n}
    (h : a.v p 0 hp = b.v p 0 hp) : a = b := by
  apply Cochain.ext
  intro i j hij
  by_cases hj : j = 0
  · cases hj
    obtain rfl : i = p := by omega
    exact h
  · exact (stalkTerm_isZero f j hj).eq_of_tgt _ _

omit [CharZero k] in
private theorem pi_eq_sum {d : ℕ} (a : Fin d → Quotient f) :
    ∑ i, a i • (Pi.single i 1 : Fin d → Quotient f) = a := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne (Ne.symm hj)]
  · simp

private def homCoordinates {n p : ℤ} (hp : p + n = 0) {d : ℕ}
    (e : (conormal f).X p ≅ ModuleCat.of (Quotient f) (Fin d → Quotient f)) :
    Cochain (conormal f) (quotientStalk f) n ≃ₗ[Quotient f] (Fin d → Quotient f) :=
  LinearEquiv.ofBijective
    { toFun := fun a i => a.v p 0 hp (e.inv (Pi.single i 1))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } (by
    constructor
    · intro a b hab
      apply cochain_ext_stalk f hp
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := (e.toLinearEquiv.symm.surjective :
        Function.Surjective (fun y => e.inv y)) x
      rw [← pi_eq_sum f y]
      simp only [map_sum, map_smul]
      exact Finset.sum_congr rfl fun i _ => congrArg (y i • ·) (congrFun hab i)
    · intro a
      let g : (Fin d → Quotient f) →ₗ[Quotient f] Quotient f :=
        LinearMap.lsum (Quotient f) (fun _ : Fin d => Quotient f) (Quotient f)
          (fun i => (LinearMap.id : Quotient f →ₗ[Quotient f] Quotient f).smulRight (a i))
      let m : (conormal f).X p ⟶ (quotientStalk f).X 0 := e.hom ≫ ModuleCat.ofHom g
      refine ⟨Cochain.single m n, funext fun i => ?_⟩
      change (Cochain.single m n).v p 0 hp (e.inv (Pi.single i 1)) = a i
      rw [Cochain.single_v]
      change g (e.hom (e.inv (Pi.single i 1))) = _
      rw [show e.hom (e.inv (Pi.single i 1)) = Pi.single i 1 from
        e.toLinearEquiv.apply_symm_apply _]
      simp only [g, LinearMap.lsum_piSingle, LinearMap.smulRight_apply, LinearMap.id_apply,
        one_smul])

private abbrev homCoordinates₀ :=
  homCoordinates f (n := 0) (p := 0) rfl (polynomialCoordinates f)

private abbrev homCoordinates₁ :=
  homCoordinates f (n := 1) (p := -1) rfl (equationCoordinates f)

omit [CharZero k] in
private theorem jacobian_single (i : Fin r) :
    jacobian f (Pi.single i 1) = fun j => jacobianEntry f j i := by
  ext j
  change ∑ l, jacobianEntry f j l * (Pi.single i 1 : Fin r → Quotient f) l = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp

set_option backward.isDefEq.respectTransparency false in
omit [CharZero k] in
private theorem homDifferential_coordinates (a : (conormalHom f).X 0) :
    homCoordinates₁ f ((conormalHom f).d 0 1 a) =
      -(transposeJacobian f (homCoordinates₀ f a)) := by
  ext i
  change (δ 0 1 a).v (-1) 0 rfl ((equationCoordinates f).inv (Pi.single i 1)) =
    -(transposeJacobian f (homCoordinates₀ f a) i)
  rw [δ_v 0 1 rfl a (-1) 0 rfl (-1) 0 rfl rfl]
  have hz : (quotientStalk f).d (-1) 0 = 0 := rfl
  rw [hz, comp_zero, zero_add]
  rw [Int.negOnePow_one, Units.smul_def]
  change ((-1 : ℤ) • ((conormal f).d (-1) 0 ≫ a.v 0 0 rfl))
    ((equationCoordinates f).inv (Pi.single i 1)) = _
  rw [neg_zsmul, one_zsmul]
  change -(((conormal f).d (-1) 0 ≫ a.v 0 0 rfl).hom
    ((equationCoordinates f).inv (Pi.single i 1))) = _
  change -(a.v 0 0 rfl ((conormal f).d (-1) 0
    ((equationCoordinates f).inv (Pi.single i 1)))) = _
  congr 1
  rw [show (conormal f).d (-1) 0 =
      (equationCoordinates f).hom ≫ ModuleCat.ofHom (jacobian f) ≫
        (polynomialCoordinates f).inv from double_d _ _ (by decide)]
  change a.v 0 0 rfl ((polynomialCoordinates f).inv
    (jacobian f ((equationCoordinates f).hom ((equationCoordinates f).inv (Pi.single i 1))))) = _
  rw [show (equationCoordinates f).hom ((equationCoordinates f).inv (Pi.single i 1)) =
    Pi.single i 1 from (equationCoordinates f).toLinearEquiv.apply_symm_apply _, jacobian_single]
  let b : Fin s → Quotient f := fun j => jacobianEntry f j i
  change a.v 0 0 rfl ((polynomialCoordinates f).inv b) =
    ∑ j, b j * homCoordinates₀ f a j
  calc
    _ = a.v 0 0 rfl ((polynomialCoordinates f).inv
          (∑ j, b j • (Pi.single j 1 : Fin s → Quotient f))) :=
      congrArg (fun x => a.v 0 0 rfl ((polynomialCoordinates f).inv x)) (pi_eq_sum f b).symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]; rfl

omit [CharZero k] in
private theorem conormalHom_d_one : (conormalHom f).d 1 2 = 0 := by
  ext a
  apply cochain_ext_stalk f (n := 2) (p := -2) rfl
  exact (isZero_double_X _ _ (-2) (by decide) (by decide)
    : IsZero ((conormal f).X (-2))).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private def cokernelComparison : CokernelComparison f := by
  let K := conormalHom f
  let q : K.X 1 ⟶ ModuleCat.of (Quotient f) (JacobianCokernel f) :=
    ModuleCat.ofHom ((transposeJacobian f).range.mkQ.comp (homCoordinates₁ f).toLinearMap)
  have hExact : Function.Exact (K.d 0 1).hom q.hom := by
    intro a
    change (transposeJacobian f).range.mkQ (homCoordinates₁ f a) = 0 ↔
      a ∈ Set.range (K.d 0 1).hom
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨-(homCoordinates₀ f).symm b, (homCoordinates₁ f).injective ?_⟩
      change homCoordinates₁ f ((conormalHom f).d 0 1 (-(homCoordinates₀ f).symm b)) = _
      rw [homDifferential_coordinates, map_neg, LinearEquiv.apply_symm_apply, map_neg, neg_neg, hb]
    · rintro ⟨b, rfl⟩
      refine ⟨-(homCoordinates₀ f b), ?_⟩
      rw [map_neg, homDifferential_coordinates]
  have hSurj : Function.Surjective q.hom :=
    (Submodule.mkQ_surjective _).comp (homCoordinates₁ f).surjective
  have hq : K.d 0 1 ≫ q = 0 := by
    ext a
    exact (hExact _).2 ⟨a, rfl⟩
  let D' : (K.sc' 0 1 2).LeftHomologyData :=
    ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork _ (conormalHom_d_one f)
      (CokernelCofork.ofπ q hq) (ModuleCat.isColimitCokernelCofork _ _ hExact hSurj)
  let c := ComplexShape.up ℤ
  let e := K.isoSc' 0 1 2 (c.prev_eq' (by decide : c.Rel 0 1)) (c.next_eq' (by decide : c.Rel 1 2))
  let D := D'.ofIso e.symm
  refine ⟨D.homologyIso.toLinearEquiv, fun z => ?_⟩
  have hπ := D.homologyπ_comp_homologyIso_hom
  have hi := D.cyclesIso_hom_comp_i
  change (K.homologyπ 1 ≫ D.homologyIso.hom) z = q (K.iCycles 1 z)
  change (K.sc 1).homologyπ ≫ D.homologyIso.hom = D.cyclesIso.hom ≫ q at hπ
  have hι : D.i = 𝟙 (K.X 1) := by
    change 𝟙 (K.X 1) ≫ 𝟙 (K.X 1) = _
    simp
  have hi₀ : D.cyclesIso.hom z = K.iCycles 1 z := by
    have h₁ : D.i (D.cyclesIso.hom z) = K.iCycles 1 z := CategoryTheory.congr_fun hi z
    have h₂ : D.i (D.cyclesIso.hom z) = D.cyclesIso.hom z :=
      CategoryTheory.congr_fun hι (D.cyclesIso.hom z)
    exact h₂.symm.trans h₁
  exact (CategoryTheory.congr_fun hπ z).trans (congrArg (fun w : K.X 1 => q w) hi₀)

section Presentation

open NonpositiveCDGA (ordinary ordinaryComplex)
open Semifree
open Specs.DerivedFormalization.Affine.KoszulZeroLocus (KoszulAlgebra exteriorVariables)

private theorem ordinaryTerm_isZero (S : CommAlgCat.{u} k) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((ordinary S).complex.X i) := by
  change IsZero ((ordinaryComplex S).X i)
  exact isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of k S) i hi

private def fromOrdinary {S : CommAlgCat.{u} k} {Q : CommDGAlgebra.{u,u} k}
    (a : S →ₐ[k] Q.DegreeZero) (i : ℤ) :
    (ordinary S).complex.X i →ₗ[k] Q.complex.X i := by
  by_cases hi : i = 0
  · subst i
    exact a.toLinearMap
  · exact 0

private theorem fromOrdinary_zero {S : CommAlgCat.{u} k} {Q : CommDGAlgebra.{u,u} k}
    (a : S →ₐ[k] Q.DegreeZero) (x : S) : fromOrdinary a 0 x = a x := by
  unfold fromOrdinary
  rw [dite_eq_left rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem fromOrdinary_mul {S : CommAlgCat.{u} k} {Q : CommDGAlgebra.{u,u} k}
    (a : S →ₐ[k] Q.DegreeZero) (i j n : ℤ) (h : i+j=n)
    (x : (ordinary S).complex.X i) (y : (ordinary S).complex.X j) :
    fromOrdinary a n ((ordinary S).mul i j n h x y) =
      Q.mul i j n h (fromOrdinary a i x) (fromOrdinary a j y) := by
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · subst i j
      have hn : n = 0 := h.symm
      cases hn
      rw [fromOrdinary_zero, fromOrdinary_zero, fromOrdinary_zero]
      exact a.map_mul x y
    · have := ModuleCat.subsingleton_of_isZero (ordinaryTerm_isZero S j hj)
      rw [show y = 0 from Subsingleton.elim _ _]
      simp only [map_zero]
  · have := ModuleCat.subsingleton_of_isZero (ordinaryTerm_isZero S i hi)
    rw [show x = 0 from Subsingleton.elim _ _]
    simp only [map_zero, LinearMap.zero_apply]

private abbrev fieldCDGA (k : Type u) [Field k] [CharZero k] :=
  ordinary (CommAlgCat.of k k)

private abbrev monomialCDGA (k : Type u) [Field k] [CharZero k] (s r : ℕ) :=
  (polynomialGradedAlgebra (fieldCDGA k) (resolutionVariables.{u} s r)).toCommDGAlgebra

private def polynomialCoefficients (k : Type u) [Field k] [CharZero k] (s r : ℕ) :
    PolynomialAlgebra k s →ₐ[k] (monomialCDGA k s r).DegreeZero :=
  MvPolynomial.aeval fun j : Fin s => variableTerm (fieldCDGA k) (resolutionVariables s r)
    (polynomialIndex j)

set_option backward.isDefEq.respectTransparency false in
private theorem polynomialCoefficients_C (c : k) :
    polynomialCoefficients k s r (MvPolynomial.C c) =
      coefficient (fieldCDGA k) (resolutionVariables s r) 0 c := by
  rw [MvPolynomial.C_eq_algebraMap, (polynomialCoefficients k s r).commutes,
    Algebra.algebraMap_eq_smul_one]
  change c • coefficient (fieldCDGA k) (resolutionVariables s r) 0 (1 : k) =
    coefficient (fieldCDGA k) (resolutionVariables s r) 0 c
  have h : c • (fieldCDGA k).one = (show (fieldCDGA k).complex.X 0 from c) := mul_one c
  exact (map_smul (coefficient (fieldCDGA k) (resolutionVariables s r) 0) c
    (fieldCDGA k).one).symm.trans (congrArg _ h)

private theorem polynomialCoefficients_support (p : Polynomial k s) :
    UsesOnly (fieldCDGA k) (resolutionVariables s r)
      (Set.range (polynomialIndex (s := s) (r := r))) (polynomialCoefficients k s r p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [polynomialCoefficients_C]
      exact coefficient_usesOnly (A := fieldCDGA k) (V := resolutionVariables s r) 0 c
  | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
  | mul_X p j hp =>
      rw [map_mul]
      change UsesOnly _ _ _ (polynomialMul _ _ 0 0 0 rfl
        (polynomialCoefficients k s r p) (polynomialCoefficients k s r (MvPolynomial.X j)))
      rw [show polynomialCoefficients k s r (MvPolynomial.X j) =
        variableTerm (fieldCDGA k) (resolutionVariables s r) (polynomialIndex j) from
          MvPolynomial.aeval_X _ _]
      exact hp.mul rfl (variable_usesOnly _ ⟨j, rfl⟩)

private def presentationStages (s r : ℕ) : Stages (resolutionVariables.{u} s r) where
  Stage := ULift.{u} ℕ
  order := LinearOrder.lift' ULift.down ULift.down_injective
  wellFounded := InvImage.wf ULift.down Nat.lt_wfRel.wf
  stage x := ⟨x.down.elim (fun _ => 0) (fun _ => 1)⟩

private theorem polynomial_before_equation (j : Fin s) (i : Fin r) :
    (presentationStages.{u} s r).stage (polynomialIndex j) <
      (presentationStages.{u} s r).stage (equationIndex i) :=
  Nat.zero_lt_succ 0

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
private theorem koszul_over_field (K : KoszulAlgebra (PolynomialAlgebra k s) f) :
    ∃ E : StagedPresentation (fieldCDGA k) (resolutionVariables s r)
      (coefficientMap k s ≫ K.base),
      (∀ j : Fin s, E.component 0 (variableTerm _ _ (polynomialIndex j)) =
        K.base.chainMap.f 0 (MvPolynomial.X j)) ∧
      (∀ i : Fin r, E.component (-1) (variableTerm _ _ (equationIndex i)) = K.generator i) ∧
      ∀ (j : Fin s) (i : Fin r), E.stages.stage (polynomialIndex j) <
        E.stages.stage (equationIndex i) := by
  let A := fieldCDGA k
  let V := resolutionVariables.{u} s r
  let W := exteriorVariables.{u} r
  let S := ordinary (PolynomialAlgebra k s)
  let b : A ⟶ K.obj := coefficientMap k s ≫ K.base
  let C := monomialCDGA k s r
  let a := polynomialCoefficients k s r
  let x : ∀ t : V.Index, K.obj.complex.X (V.degree t)
    | ⟨Sum.inl j⟩ => K.base.chainMap.f 0 (MvPolynomial.X j)
    | ⟨Sum.inr i⟩ => K.generator i
  let e : ∀ t : W.Index, C.complex.X (W.degree t) :=
    fun i => variableTerm A V (equationIndex i.down)
  obtain ⟨G⟩ := gradedUniversalProperty A V K.obj.toCommDGAlgebra
    (fun i => (b.chainMap.f i).hom) b.map_one b.map_mul x
  obtain ⟨J⟩ := gradedUniversalProperty S W C (fromOrdinary a)
    ((fromOrdinary_zero a 1).trans a.map_one) (fromOrdinary_mul a) e
  let L := G.default
  let R := J.default
  let back (i : ℤ) := (R.component i).comp (K.exterior.component i).symm.toLinearMap
  have back_base (i : ℤ) (p : S.complex.X i) :
      back i (K.base.chainMap.f i p) = fromOrdinary a i p := by
    change R.component i ((K.exterior.component i).symm (K.base.chainMap.f i p)) = _
    rw [← K.exterior.map_base, LinearEquiv.symm_apply_apply, R.map_base]
  have back_equation (i : Fin r) :
      back (-1) (K.generator i) = variableTerm A V (equationIndex i) := by
    change R.component (-1) ((K.exterior.component (-1)).symm
      (K.exterior.component (-1) (variableTerm S W (ULift.up i)))) = _
    rw [LinearEquiv.symm_apply_apply]
    exact R.map_var (ULift.up i)
  have back_mul (i j n : ℤ) (h : i+j=n) (p : K.obj.complex.X i) (q : K.obj.complex.X j) :
      back n (K.obj.mul i j n h p q) =
        polynomialMul A V i j n h (back i p) (back j q) := by
    obtain ⟨p, rfl⟩ := (K.exterior.component i).surjective p
    obtain ⟨q, rfl⟩ := (K.exterior.component j).surjective q
    change R.component n ((K.exterior.component n).symm (K.obj.mul i j n h
      (K.exterior.component i p) (K.exterior.component j q))) = _
    rw [← K.exterior.map_mul, LinearEquiv.symm_apply_apply, R.map_mul]
    change C.mul i j n h _ _ = C.mul i j n h
      (R.component i ((K.exterior.component i).symm (K.exterior.component i p)))
      (R.component j ((K.exterior.component j).symm (K.exterior.component j q)))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  let L₀ : C.DegreeZero →ₐ[k] K.obj.toCommDGAlgebra.DegreeZero :=
    { L.component 0 with
      map_zero' := map_zero (L.component 0)
      map_one' := (L.map_base 0 A.one).trans b.map_one
      map_mul' := L.map_mul 0 0 0 rfl
      commutes' := fun c => by
        change L.component 0 (c • C.one) = c • K.obj.one
        rw [map_smul, show L.component 0 C.one = K.obj.one from
          (L.map_base 0 A.one).trans b.map_one] }
  let K₀ : Polynomial k s →ₐ[k] K.obj.toCommDGAlgebra.DegreeZero :=
    { toFun := fun p => K.base.chainMap.f 0 p
      map_zero' := map_zero (K.base.chainMap.f 0).hom
      map_add' := map_add (K.base.chainMap.f 0).hom
      map_one' := K.base.map_one
      map_mul' := K.base.map_mul 0 0 0 rfl
      commutes' := fun c => by
        change K.base.chainMap.f 0 (algebraMap k (Polynomial k s) c) = c • K.obj.one
        rw [Algebra.algebraMap_eq_smul_one]
        exact (map_smul (K.base.chainMap.f 0).hom c S.one).trans
          (congrArg (c • ·) K.base.map_one) }
  have L_coeff : L₀.comp a = K₀ := by
    apply MvPolynomial.algHom_ext
    intro j
    change L₀ (a (MvPolynomial.X j)) = K.base.chainMap.f 0 (MvPolynomial.X j)
    rw [show a (MvPolynomial.X j) = variableTerm A V (polynomialIndex j) from
      MvPolynomial.aeval_X _ _]
    exact L.map_var (polynomialIndex j)
  have forward_base (i : ℤ) (p : S.complex.X i) :
      L.component i (fromOrdinary a i p) = K.base.chainMap.f i p := by
    by_cases hi : i = 0
    · subst i
      rw [fromOrdinary_zero]
      exact AlgHom.congr_fun L_coeff p
    · have := ModuleCat.subsingleton_of_isZero (ordinaryTerm_isZero (PolynomialAlgebra k s) i hi)
      rw [show p = 0 from Subsingleton.elim _ _]
      simp only [map_zero]
  have backward_base (i : ℤ) (p : A.complex.X i) :
      back i (b.chainMap.f i p) = coefficient A V i p := by
    change back i (K.base.chainMap.f i ((coefficientMap k s).chainMap.f i p)) = _
    rw [back_base]
    by_cases hi : i = 0
    · subst i
      rw [fromOrdinary_zero]
      exact polynomialCoefficients_C (k := k) (s := s) (r := r) p
    · have := ModuleCat.subsingleton_of_isZero
        (ordinaryTerm_isZero (CommAlgCat.of k k) i hi)
      rw [show p = 0 from Subsingleton.elim _ _]
      simp only [map_zero]
  have left_inv (i : ℤ) (p : Semifree.Polynomial A V i) :
      back i (L.component i p) = p := by
    refine polynomial_generated A V (fun i p => back i (L.component i p) = p)
      ?_ ?_ ?_ ?_ ?_ ?_ i p
    · intro i
      simp
    · intro i a b ha hb
      simp only [map_add, ha, hb]
    · intro i z a ha
      simp only [Units.smul_def, map_zsmul, ha]
    · intro i a
      rw [L.map_base]
      exact backward_base i a
    · rintro ⟨j | j⟩
      · rw [L.map_var]
        change back 0 (K.base.chainMap.f 0 (MvPolynomial.X j)) = _
        rw [back_base, fromOrdinary_zero]
        exact MvPolynomial.aeval_X _ _
      · rw [L.map_var]
        exact back_equation j
    · intro i j n h a b ha hb
      rw [L.map_mul, back_mul, ha, hb]
  have right_inv (i : ℤ) (p : K.obj.complex.X i) :
      L.component i (back i p) = p := by
    obtain ⟨p, rfl⟩ := (K.exterior.component i).surjective p
    refine polynomial_generated S W
      (fun i p => L.component i (back i (K.exterior.component i p)) =
        K.exterior.component i p) ?_ ?_ ?_ ?_ ?_ ?_ i p
    · intro i
      simp
    · intro i a b ha hb
      simp only [map_add, ha, hb]
    · intro i z a ha
      simp only [Units.smul_def, map_zsmul, ha]
    · intro i a
      rw [K.exterior.map_base, back_base, forward_base]
    · rintro ⟨i⟩
      change L.component (-1) (back (-1) (K.generator i)) = K.generator i
      rw [back_equation]
      exact L.map_var (equationIndex i)
    · intro i j n h a b ha hb
      rw [K.exterior.map_mul, back_mul, L.map_mul, ha, hb]
  let E₀ (i : ℤ) : Semifree.Polynomial A V i ≃ₗ[k] K.obj.complex.X i :=
    LinearEquiv.ofLinearMap (L.component i) (back i)
      (LinearMap.ext fun p => right_inv i p) (LinearMap.ext fun p => left_inv i p)
  let St : Stages V := presentationStages s r
  let E : StagedPresentation A V b :=
    { component := E₀
      map_one := (L.map_base 0 A.one).trans b.map_one
      map_mul := L.map_mul
      map_base := L.map_base
      stages := St
      earlier := by
        rintro ⟨j | i⟩
        · change UsesOnly A V _ (back 1 (K.obj.complex.d 0 1 _))
          have := K.obj.nonpositive 1 (by decide)
          rw [show K.obj.complex.d 0 1 _ = 0 from Subsingleton.elim _ _, map_zero]
          exact UsesOnly.zero _
        · change UsesOnly A V (St.before (St.stage (equationIndex i)))
            (back 0 (K.obj.complex.d (-1) 0 (L.component (-1)
              (variableTerm A V (equationIndex i)))))
          have he : L.component (-1) (variableTerm A V (equationIndex i)) =
              K.generator i := L.map_var (equationIndex i)
          rw [he]
          rw [K.d_generator, back_base, fromOrdinary_zero]
          apply (polynomialCoefficients_support (r := r) (f i)).mono
          rintro _ ⟨j, rfl⟩
          exact polynomial_before_equation.{u} j i }
  exact ⟨E, fun j => L.map_var (polynomialIndex j), fun i => L.map_var (equationIndex i),
    polynomial_before_equation.{u}⟩

private theorem existsKoszulPresentation
    (hK : Specs.DerivedFormalization.Affine.KoszulZeroLocus.ZeroLocus.{u,u})
    (hf : RingTheory.Sequence.IsRegular (Polynomial k s) (List.ofFn f)) :
    Nonempty (KoszulPresentation f) := by
  obtain ⟨_, _, h, _⟩ := hK (k := k)
  obtain ⟨K, _⟩ := h.1 (PolynomialAlgebra k s) r f
  obtain ⟨hs, hq, _⟩ := h.2.2 (PolynomialAlgebra k s) r f K hf
  obtain ⟨E, hx, he, ho⟩ := koszul_over_field f K
  exact ⟨⟨K, E, hx, he, ho, hs, hq⟩⟩

end Presentation

section Cotangent

open Kahler (value)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor act term regular act_assoc_at)
open SemifreeDifferentials (differential_symbol generator Coefficients multiples IsGradedBasis
  semifreeAfterBaseChange)

variable {f}
variable (P : KoszulPresentation f) (O : P.relativeDifferentials) (T : ModuleTensor.{u,u} k)

set_option backward.isDefEq.respectTransparency false in
private theorem symbolDifferentials : SymbolDifferentials P O := by
  constructor
  · intro j
    have h := differential_symbol O 0 (P.koszul.base.chainMap.f 0 (MvPolynomial.X j))
    refine h.trans ?_
    have := P.koszul.obj.nonpositive 1 (by decide)
    exact (congrArg (value O.symbol 1 1 rfl) (Subsingleton.elim _ 0)).trans
      (map_zero (value O.symbol 1 1 rfl).hom)
  · intro i
    exact (differential_symbol O (-1) (P.koszul.generator i)).trans
      (congrArg (value O.symbol 0 0 rfl) (P.koszul.d_generator i))

private abbrev variablesOver (_k : Type u) (s r : ℕ) : Semifree.Variables.{u} :=
  resolutionVariables s r

set_option quotPrecheck false

local notation "B₀" => (quotientCDGA f).toCommDGAlgebra
local notation "M₀" => (P.model O).module T
local notation "V₀" => variablesOver k s r

private abbrev extendedGenerator (x : (V₀).Index) : term M₀ ((V₀).degree x) :=
  T.tmul P.koszul.augmentation (N := regular B₀) _ 0 _ (add_zero _)
    (generator P.overField O x) (B₀).one

private theorem extendedGenerator_poly (j : Fin s) :
    extendedGenerator P O T (polynomialIndex j) =
      extendedSymbol P O T 0 (P.koszul.base.chainMap.f 0 (MvPolynomial.X j)) :=
  congrArg (extendedSymbol P O T 0) (P.polynomial_generator j)

private theorem extendedGenerator_equation (i : Fin r) :
    extendedGenerator P O T (equationIndex i) =
      extendedSymbol P O T (-1) (P.koszul.generator i) :=
  congrArg (extendedSymbol P O T (-1)) (P.equation_generator i)

private theorem extendedBasis
    (hT : T.Formulas (P.koszul.augmentation :
      P.koszul.obj.toCommDGAlgebra ⟶ B₀) (regular B₀)) :
    IsGradedBasis (extendedGenerator P O T) := by
  obtain ⟨_, h, _⟩ := semifreeAfterBaseChange T P.overField O P.koszul.augmentation hT
  exact h

private abbrev tensorWithUnit (n : ℤ) : term O.module n →ₗ[k] term M₀ n :=
  ((Tensor.pair (N := regular B₀)
    P.koszul.augmentation n 0 n (add_zero n)).compr₂
      (T.degree P.koszul.augmentation O.module (regular B₀) n).toLinearMap).flip (B₀).one

set_option backward.isDefEq.respectTransparency false in
private theorem d_extendedSymbol
    (hT : T.Formulas (P.koszul.augmentation :
      P.koszul.obj.toCommDGAlgebra ⟶ B₀) (regular B₀)) (i : ℤ)
    (x : P.koszul.obj.complex.X i) :
    ((M₀).complex ()).d i (i+1) (extendedSymbol P O T i x) =
      extendedSymbol P O T (i+1) (P.koszul.obj.complex.d i (i+1) x) := by
  let g : P.koszul.obj.toCommDGAlgebra ⟶ B₀ := P.koszul.augmentation
  let z := value O.symbol i i (add_zero i) x
  have hd := hT.differential O.module i 0 i (add_zero i) z (B₀).one
  refine hd.trans ?_
  let l : (B₀).complex.X 1 →ₗ[k] term M₀ (i+1) :=
    ((Tensor.pair (N := regular B₀) g i 1 (i+1) rfl).compr₂
      (T.degree g O.module (regular B₀) (i+1)).toLinearMap) z
  change tensorWithUnit P O T (i+1) ((O.module.complex ()).d i (i+1) z) +
    i.negOnePow • l ((B₀).complex.d 0 1 (B₀).one) = _
  have hz : (B₀).complex.d 0 1 (B₀).one = 0 := rfl
  rw [hz, map_zero, smul_zero, add_zero]
  exact congrArg (tensorWithUnit P O T (i+1)) (differential_symbol O i x)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorWithUnit_act (n : ℤ)
    (hT : T.Formulas (P.koszul.augmentation :
      P.koszul.obj.toCommDGAlgebra ⟶ B₀) (regular B₀))
    (x : term O.module n) (a : P.koszul.obj.complex.X 0) :
    tensorWithUnit P O T n (act O.module n 0 n (add_zero n) x a) =
      act M₀ n 0 n (add_zero n) (tensorWithUnit P O T n x)
        (P.koszul.augmentation.chainMap.f 0 a) := by
  let g : P.koszul.obj.toCommDGAlgebra ⟶ B₀ := P.koszul.augmentation
  have ha := hT.action O.module n 0 n 0 n (add_zero n) (add_zero n) x
    (B₀).one (g.chainMap.f 0 a)
  have hb := congrArg (T.degree g O.module (regular B₀) n)
    (Tensor.pure_balance (N := regular B₀) g n 0 0 n 0 n (add_zero n) rfl (add_zero n) x a (B₀).one)
  have hr := congrArg (fun b => T.tmul g (N := regular B₀) n 0 n (add_zero n) x b)
    ((B₀).toDGAlgebra.id_comp 0 (g.chainMap.f 0 a))
  have hleft : Specs.DerivedFormalization.Affine.Tensor.signedLeft (regular B₀) 0 0 0 rfl
      (g.chainMap.f 0 a) (B₀).one = g.chainMap.f 0 a := by
    rw [Specs.DerivedFormalization.Affine.Tensor.signedLeft_apply, Int.mul_zero,
      Int.negOnePow_zero, one_smul]
    exact (B₀).toDGAlgebra.id_comp 0 _
  exact hb.trans ((congrArg (fun b => T.tmul g (N := regular B₀) n 0 n (add_zero n) x b)
    hleft).trans (hr.symm.trans ha.symm))

open scoped DirectSum

private def entryScalar (n : ℤ) (x : (V₀).Index) (hx : (V₀).degree x = n) :
    (B₀).complex.X (n + -(V₀).degree x) ≃ₗ[k] Quotient f := by
  exact ((B₀).complex.XIsoOfEq (by omega : n + -(V₀).degree x = 0)).toLinearEquiv

private def coefficientInclusion {n : ℤ} {d : ℕ} (idx : Fin d ↪ (V₀).Index)
    (degree : ∀ j, (V₀).degree (idx j) = n) (j : Fin d) :
    Quotient f →ₗ[k] Coefficients B₀ V₀ n := by
  classical
  exact (DirectSum.lof k _ _ (idx j)).comp (entryScalar n (idx j) (degree j)).symm.toLinearMap

private def coefficientRead {n : ℤ} {d : ℕ} (idx : Fin d ↪ (V₀).Index)
    (degree : ∀ j, (V₀).degree (idx j) = n) :
    Coefficients B₀ V₀ n →ₗ[k] (Fin d → Quotient f) where
  toFun a j := entryScalar n (idx j) (degree j) (a (idx j))
  map_add' a b := by ext j; exact map_add (entryScalar n (idx j) (degree j)) _ _
  map_smul' c a := by ext j; exact map_smul (entryScalar n (idx j) (degree j)) _ _

private theorem coefficientRead_inclusion {n : ℤ} {d : ℕ} (idx : Fin d ↪ (V₀).Index)
    (degree : ∀ j, (V₀).degree (idx j) = n) (j : Fin d) (a : Quotient f) :
    coefficientRead idx degree (coefficientInclusion idx degree j a) = Pi.single j a := by
  classical
  ext i
  change entryScalar n (idx i) (degree i)
    ((DirectSum.lof k (V₀).Index (fun x => (B₀).complex.X (n + -(V₀).degree x))
      (idx j) ((entryScalar n (idx j) (degree j)).symm a) : Coefficients B₀ V₀ n) (idx i)) = _
  by_cases h : i = j
  · subst i
    rw [DirectSum.lof_apply, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
  · have he : idx j ≠ idx i := fun hh => h (idx.injective hh.symm)
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (fun hh => he hh.symm), map_zero, Pi.single_eq_of_ne h]

private def coefficientEquiv {n : ℤ} {d : ℕ} (idx : Fin d ↪ (V₀).Index)
    (degree : ∀ j, (V₀).degree (idx j) = n)
    (cover : ∀ x : (V₀).Index, (V₀).degree x = n → x ∈ Set.range idx) :
    Coefficients B₀ V₀ n ≃ₗ[k] (Fin d → Quotient f) :=
  LinearEquiv.ofBijective (coefficientRead idx degree) (by
    constructor
    · intro a b hab
      apply DFinsupp.ext
      intro x
      by_cases h : (V₀).degree x = n
      · obtain ⟨i, rfl⟩ := cover x h
        exact (entryScalar n (idx i) (degree i)).injective (congrFun hab i)
      · have := ModuleCat.subsingleton_of_isZero
          (ordinaryTerm_isZero (quotientAlg (PolynomialAlgebra k s) f) _
            (by omega : n + -(V₀).degree x ≠ 0))
        exact Subsingleton.elim (a x) (b x)
    · intro a
      refine ⟨∑ j, coefficientInclusion idx degree j (a j), ?_⟩
      rw [map_sum]
      simp only [coefficientRead_inclusion, Finset.univ_sum_single])

private theorem coefficientEquiv_inv {n : ℤ} {d : ℕ} (idx : Fin d ↪ (V₀).Index)
    (degree : ∀ j, (V₀).degree (idx j) = n)
    (cover : ∀ x : (V₀).Index, (V₀).degree x = n → x ∈ Set.range idx)
    (a : Fin d → Quotient f) :
    (coefficientEquiv idx degree cover).symm a = ∑ j, coefficientInclusion idx degree j (a j) := by
  apply (coefficientEquiv idx degree cover).injective
  rw [LinearEquiv.apply_symm_apply, map_sum]
  change a = ∑ j, coefficientRead idx degree (coefficientInclusion idx degree j (a j))
  simp only [coefficientRead_inclusion, Finset.univ_sum_single]

private def polynomialIndices (s r : ℕ) : Fin s ↪ (resolutionVariables.{u} s r).Index :=
  ⟨polynomialIndex, fun _ _ h => Sum.inl.inj (congrArg ULift.down h)⟩

private def equationIndices (s r : ℕ) : Fin r ↪ (resolutionVariables.{u} s r).Index :=
  ⟨equationIndex, fun _ _ h => Sum.inr.inj (congrArg ULift.down h)⟩

omit [Field k] [CharZero k] in
private theorem polynomialIndices_cover (x : (V₀).Index)
    (h : (V₀).degree x = 0) : x ∈ Set.range (polynomialIndices s r) := by
  rcases x with ⟨j | i⟩
  · exact ⟨j, rfl⟩
  · exact False.elim ((by decide : (-1 : ℤ) ≠ 0) h)

omit [Field k] [CharZero k] in
private theorem equationIndices_cover (x : (V₀).Index)
    (h : (V₀).degree x = -1) : x ∈ Set.range (equationIndices s r) := by
  rcases x with ⟨j | i⟩
  · exact False.elim ((by decide : (0 : ℤ) ≠ -1) h)
  · exact ⟨i, rfl⟩


private abbrev qact (M : (B₀).Module) (n : ℤ) (x : term M n) (a : Quotient f) : term M n :=
  act M n 0 n (add_zero n) x a

set_option backward.isDefEq.respectTransparency false in
private theorem qact_assoc (M : (B₀).Module) (n : ℤ) (x : term M n) (a b : Quotient f) :
    qact M n (qact M n x a) b = qact M n x (a * b) :=
  act_assoc_at M n 0 0 n 0 n (add_zero n) rfl (add_zero n) x a b

set_option backward.isDefEq.respectTransparency false in
private theorem qact_d (M : (B₀).Module) (n : ℤ) (x : term M n) (a : Quotient f) :
    (M.complex ()).d n (n+1) (qact M n x a) = qact M (n+1) ((M.complex ()).d n (n+1) x) a := by
  have h := M.leibniz (a := ()) (b := ()) n 0 n (add_zero n) x a
  have hz : (B₀).complex.d 0 1 a = 0 := rfl
  change _ = _ + n.negOnePow • act M n 1 (n+1) rfl x ((B₀).complex.d 0 1 a) at h
  rw [hz, map_zero, smul_zero, add_zero] at h
  exact h

private theorem extended_coeff (p : Polynomial k s) :
    P.koszul.augmentation.chainMap.f 0 (P.koszul.base.chainMap.f 0 p) =
      (show (B₀).complex.X 0 from quotientClass f p) :=
  congrArg (fun b : NonpositiveCDGA.ordinary (PolynomialAlgebra k s) ⟶ quotientCDGA f =>
    b.chainMap.f 0 p) P.koszul.augmentation_base

set_option backward.isDefEq.respectTransparency false in
private theorem extendedLeibniz
    (hT : T.Formulas (P.koszul.augmentation :
      P.koszul.obj.toCommDGAlgebra ⟶ B₀) (regular B₀))
    (a b : Polynomial k s) :
    extendedSymbol P O T 0 (P.koszul.base.chainMap.f 0 (a*b)) =
      qact M₀ 0 (extendedSymbol P O T 0 (P.koszul.base.chainMap.f 0 a)) (quotientClass f b) +
      qact M₀ 0 (extendedSymbol P O T 0 (P.koszul.base.chainMap.f 0 b)) (quotientClass f a) := by
  let a' := P.koszul.base.chainMap.f 0 a
  let b' := P.koszul.base.chainMap.f 0 b
  let D := value O.symbol 0 0 rfl
  let L := tensorWithUnit P O T 0
  have hbase : P.koszul.base.chainMap.f 0 (a*b) = P.koszul.obj.mul 0 0 0 rfl a' b' :=
    P.koszul.base.map_mul 0 0 0 rfl a b
  have hD : D (P.koszul.obj.mul 0 0 0 rfl a' b') =
      act O.module 0 0 0 rfl (D a') b' + act O.module 0 0 0 rfl (D b') a' := by
    have h := O.symbol.property.leibniz 0 0 0 0 0 0 rfl rfl rfl rfl a' b'
    simpa only [Int.zero_mul, Int.negOnePow_zero, one_smul] using h
  calc
    _ = L (D (P.koszul.obj.mul 0 0 0 rfl a' b')) := congrArg (fun z => L (D z)) hbase
    _ = L (act O.module 0 0 0 rfl (D a') b') + L (act O.module 0 0 0 rfl (D b') a') :=
      (congrArg L hD).trans (map_add L _ _)
    _ = _ := by
      have ha := tensorWithUnit_act P O T 0 hT (D a') b'
      have hb := tensorWithUnit_act P O T 0 hT (D b') a'
      exact congrArg₂ (· + ·)
        (ha.trans (congrArg (act M₀ 0 0 0 rfl (L (D a'))) (extended_coeff P b)))
        (hb.trans (congrArg (act M₀ 0 0 0 rfl (L (D b'))) (extended_coeff P a)))

set_option backward.isDefEq.respectTransparency false in
private theorem gradient
    (hT : T.Formulas (P.koszul.augmentation :
      P.koszul.obj.toCommDGAlgebra ⟶ B₀) (regular B₀))
    (p : Polynomial k s) :
    extendedSymbol P O T 0 (P.koszul.base.chainMap.f 0 p) =
      ∑ j, qact M₀ 0 (extendedGenerator P O T (polynomialIndex j))
        (quotientClass f (MvPolynomial.pderiv j p)) := by
  classical
  let F : Polynomial k s →ₗ[k] term M₀ 0 :=
    (tensorWithUnit P O T 0).comp
      ((value O.symbol 0 0 rfl).hom.comp (P.koszul.base.chainMap.f 0).hom)
  let G (p : Polynomial k s) (j : Fin s) : term M₀ 0 :=
    qact M₀ 0 (extendedGenerator P O T (polynomialIndex j))
      (quotientClass f (MvPolynomial.pderiv j p))
  have hX (j : Fin s) : F (MvPolynomial.X j) = ∑ i, G (MvPolynomial.X j) i := by
    rw [Finset.sum_eq_single j]
    · change extendedSymbol P O T 0 (P.koszul.base.chainMap.f 0 (MvPolynomial.X j)) = _
      rw [← extendedGenerator_poly]
      change _ = qact M₀ 0 _ (quotientClass f (MvPolynomial.pderiv j (MvPolynomial.X j)))
      rw [MvPolynomial.pderiv_X_self, map_one]
      exact ((M₀).act_id () 0 _).symm
    · intro i _ hi
      change qact M₀ 0 _ (quotientClass f (MvPolynomial.pderiv i (MvPolynomial.X j))) = 0
      rw [MvPolynomial.pderiv_X_of_ne hi.symm, map_zero]
      exact map_zero _
    · simp
  have hG (a b : Polynomial k s) (j : Fin s) :
      G (a*b) j = qact M₀ 0 (G a j) (quotientClass f b) + qact M₀ 0 (G b j) (quotientClass f a) := by
    unfold G qact
    rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, map_add]
    have h₁ := (qact_assoc M₀ 0 (extendedGenerator P O T (polynomialIndex j))
      (quotientClass f (MvPolynomial.pderiv j a)) (quotientClass f b)).symm
    have h₂ := (qact_assoc M₀ 0 (extendedGenerator P O T (polynomialIndex j))
      (quotientClass f (MvPolynomial.pderiv j b)) (quotientClass f a)).symm
    have hm := congrArg (qact M₀ 0 (extendedGenerator P O T (polynomialIndex j)))
      (mul_comm (quotientClass f a) (quotientClass f (MvPolynomial.pderiv j b)))
    exact congrArg₂ (· + ·) h₁ (hm.trans h₂)
  change F p = ∑ j, G p j
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hrel := O.symbol.property.relative 0 0 rfl (show (fieldCDGA k).complex.X 0 from c)
    have hF : F (MvPolynomial.C c) = 0 :=
      (congrArg (tensorWithUnit P O T 0) hrel).trans (map_zero (tensorWithUnit P O T 0))
    rw [hF]
    symm
    apply Finset.sum_eq_zero
    intro j _
    change qact M₀ 0 _ (quotientClass f (MvPolynomial.pderiv j (MvPolynomial.C c))) = 0
    rw [MvPolynomial.pderiv_C, map_zero]
    exact map_zero _
  | add a b ha hb =>
    rw [map_add, ha, hb, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold G qact
    simp only [map_add]
  | mul_X a j ha =>
    have hL : F (a * MvPolynomial.X j) =
        qact M₀ 0 (F a) (quotientClass f (MvPolynomial.X j)) +
        qact M₀ 0 (F (MvPolynomial.X j)) (quotientClass f a) := extendedLeibniz P O T hT _ _
    rw [hL, ha, hX]
    let L (a : Quotient f) : term M₀ 0 →ₗ[k] term M₀ 0 := (act M₀ 0 0 0 rfl).flip a
    change L (quotientClass f (MvPolynomial.X j)) (∑ i, G a i) +
      L (quotientClass f a) (∑ i, G (MvPolynomial.X j) i) = _
    rw [map_sum, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (hG a (MvPolynomial.X j) i).symm)


private def basisVectors (h : IsGradedBasis (extendedGenerator P O T))
    {n : ℤ} {d : ℕ} (idx : Fin d ↪ (V₀).Index) (degree : ∀ j, (V₀).degree (idx j) = n)
    (cover : ∀ x : (V₀).Index, (V₀).degree x = n → x ∈ Set.range idx) :
    (Fin d → Quotient f) ≃ₗ[k] term M₀ n :=
  (coefficientEquiv idx degree cover).symm.trans
    (LinearEquiv.ofBijective _ (h n))

private abbrev polynomialBasis (h : IsGradedBasis (extendedGenerator P O T)) :=
  basisVectors P O T h (polynomialIndices s r) (fun _ => rfl) polynomialIndices_cover

private abbrev equationBasis (h : IsGradedBasis (extendedGenerator P O T)) :=
  basisVectors P O T h (equationIndices s r) (fun _ => rfl) equationIndices_cover

set_option backward.isDefEq.respectTransparency false in
private theorem inclusion_multiples {n : ℤ} {d : ℕ} (idx : Fin d ↪ (V₀).Index)
    (degree : ∀ j, (V₀).degree (idx j) = n) (j : Fin d) (a : Quotient f) :
    multiples (extendedGenerator P O T) n (coefficientInclusion idx degree j a) =
      act M₀ ((V₀).degree (idx j)) (n + -(V₀).degree (idx j)) n (by omega)
        (extendedGenerator P O T (idx j)) ((entryScalar n (idx j) (degree j)).symm a) := by
  classical
  apply DirectSum.toModule_lof (R := k)

set_option backward.isDefEq.respectTransparency false in
private theorem polynomialBasis_apply (h : IsGradedBasis (extendedGenerator P O T))
    (v : Fin s → Quotient f) :
    polynomialBasis P O T h v =
      ∑ j, qact M₀ 0 (extendedGenerator P O T (polynomialIndex j)) (v j) := by
  classical
  change multiples (extendedGenerator P O T) 0
    ((coefficientEquiv (polynomialIndices s r) (fun _ => rfl) polynomialIndices_cover).symm v) = _
  rw [coefficientEquiv_inv, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact inclusion_multiples P O T (polynomialIndices s r) (fun _ => rfl) j (v j)

set_option backward.isDefEq.respectTransparency false in
private theorem equationBasis_apply (h : IsGradedBasis (extendedGenerator P O T))
    (v : Fin r → Quotient f) :
    equationBasis P O T h v =
      ∑ i, qact M₀ (-1) (extendedGenerator P O T (equationIndex i)) (v i) := by
  classical
  change multiples (extendedGenerator P O T) (-1)
    ((coefficientEquiv (equationIndices s r) (fun _ => rfl) equationIndices_cover).symm v) = _
  rw [coefficientEquiv_inv, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact inclusion_multiples P O T (equationIndices s r) (fun _ => rfl) i (v i)

private theorem cotangentTerm_subsingleton (h : IsGradedBasis (extendedGenerator P O T))
    (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ -1) : Subsingleton (term M₀ n) := by
  have hz : Subsingleton (Coefficients B₀ V₀ n) := by
    constructor
    intro a b
    apply DFinsupp.ext
    rintro ⟨j | i⟩
    · have h : n + -(V₀).degree (polynomialIndex j) ≠ 0 := by
        change n + -(0 : ℤ) ≠ 0
        simpa using h₀
      exact (ModuleCat.subsingleton_of_isZero
        (ordinaryTerm_isZero (quotientAlg (PolynomialAlgebra k s) f) _ h)).elim _ _
    · have h : n + -(V₀).degree (equationIndex i) ≠ 0 := by
        change n + -(-1 : ℤ) ≠ 0
        omega
      exact (ModuleCat.subsingleton_of_isZero
        (ordinaryTerm_isZero (quotientAlg (PolynomialAlgebra k s) f) _ h)).elim _ _
  exact (h n).2.subsingleton

private abbrev restrictToField :=
  ModuleCat.restrictScalars (algebraMap k (Quotient f))

set_option backward.isDefEq.respectTransparency false in
private def restrictProduct (d : ℕ) :
    (restrictToField (f := f)).obj (ModuleCat.of (Quotient f) (Fin d → Quotient f))
      ≃ₗ[k] (Fin d → Quotient f) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' c a := funext (fun j =>
    show (algebraMap k (Quotient f) c) • (show Fin d → Quotient f from a) j =
      c • (show Fin d → Quotient f from a) j from
      IsScalarTower.algebraMap_smul (Quotient f) c _)

private abbrev restrictCoordinates {n : ℤ} {d : ℕ}
    (e : (conormal f).X n ≅ ModuleCat.of (Quotient f) (Fin d → Quotient f)) :
    ((restriction f).obj (conormal f)).X n ≃ₗ[k] (Fin d → Quotient f) :=
  ((restrictToField (f := f)).mapIso e).toLinearEquiv.trans (restrictProduct d)

private def conormalTermIso (h : IsGradedBasis (extendedGenerator P O T)) (n : ℤ) :
    ((restriction f).obj (conormal f)).X n ≅ ((M₀).complex ()).X n := by
  by_cases h₀ : n = 0
  · subst n
    exact ((restrictCoordinates (polynomialCoordinates f)).trans
      (polynomialBasis P O T h)).toModuleIso
  · by_cases h₁ : n = -1
    · subst n
      exact ((restrictCoordinates (equationCoordinates f)).trans
        (equationBasis P O T h)).toModuleIso
    · have := cotangentTerm_subsingleton P O T h n h₀ h₁
      have : Subsingleton (((restriction f).obj (conormal f)).X n) :=
        ModuleCat.subsingleton_of_isZero (Functor.map_isZero (restrictToField (f := f))
          (show IsZero ((conormal f).X n) from isZero_double_X _ _ n h₁ h₀))
      exact (LinearEquiv.ofSubsingleton (R := k)
        (((restriction f).obj (conormal f)).X n) (term M₀ n)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
private theorem d_equationBasis (h : IsGradedBasis (extendedGenerator P O T))
    (hT : T.Formulas (P.koszul.augmentation :
      P.koszul.obj.toCommDGAlgebra ⟶ B₀) (regular B₀))
    (a : Fin r → Quotient f) :
    ((M₀).complex ()).d (-1) 0 (equationBasis P O T h a) =
      polynomialBasis P O T h (jacobian f a) := by
  classical
  rw [equationBasis_apply, polynomialBasis_apply, map_sum]
  have he (i : Fin r) :
      ((M₀).complex ()).d (-1) 0 (extendedGenerator P O T (equationIndex i)) =
        ∑ j, qact M₀ 0 (extendedGenerator P O T (polynomialIndex j)) (jacobianEntry f j i) := by
    calc
      _ = ((M₀).complex ()).d (-1) 0 (extendedSymbol P O T (-1) (P.koszul.generator i)) :=
        congrArg (((M₀).complex ()).d (-1) 0) (extendedGenerator_equation P O T i)
      _ = extendedSymbol P O T 0 ((P.koszul.obj.complex.d (-1) 0) (P.koszul.generator i)) :=
        d_extendedSymbol P O T hT (-1) (P.koszul.generator i)
      _ = _ := (congrArg (extendedSymbol P O T 0) (P.koszul.d_generator i)).trans
        (gradient P O T hT (f i))
  calc
    _ = ∑ i, ∑ j, qact M₀ 0 (extendedGenerator P O T (polynomialIndex j))
        (jacobianEntry f j i * a i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := qact_d M₀ (-1) (extendedGenerator P O T (equationIndex i)) (a i)
      refine hi.trans ?_
      have h₁ : ((M₀).complex ()).d (-1) ((-1 : ℤ) + 1)
        (extendedGenerator P O T (equationIndex i)) =
          ∑ j, qact M₀ 0 (extendedGenerator P O T (polynomialIndex j)) (jacobianEntry f j i) := he i
      rw [h₁]
      let l : term M₀ 0 →ₗ[k] term M₀ 0 := (act M₀ 0 0 0 rfl).flip (a i)
      change l _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => qact_assoc M₀ 0 _ _ _
    _ = ∑ j, ∑ i, qact M₀ 0 (extendedGenerator P O T (polynomialIndex j))
        (jacobianEntry f j i * a i) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      let l := act M₀ 0 0 0 rfl (extendedGenerator P O T (polynomialIndex j))
      change ∑ i, l (jacobianEntry f j i * a i) = l (∑ i, jacobianEntry f j i * a i)
      exact (map_sum l _ _).symm

set_option backward.isDefEq.respectTransparency false in
private def conormalIso (h : IsGradedBasis (extendedGenerator P O T))
    (hT : T.Formulas (P.koszul.augmentation :
      P.koszul.obj.toCommDGAlgebra ⟶ B₀) (regular B₀)) :
    (restriction f).obj (conormal f) ≅ ((M₀).complex ()) := by
  refine Hom.isoOfComponents (conormalTermIso P O T h) ?_
  intro i j hij
  change i + 1 = j at hij
  cases hij
  by_cases hi : i = -1
  · subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hd : (conormal f).d (-1) 0 =
      (equationCoordinates f).hom ≫ ModuleCat.ofHom (jacobian f) ≫
        (polynomialCoordinates f).inv := double_d _ _ (by decide)
    have hx : (polynomialCoordinates f).hom ((conormal f).d (-1) 0 x) =
        jacobian f ((equationCoordinates f).hom x) := by
      have hy := CategoryTheory.congr_fun hd x
      change (conormal f).d (-1) 0 x =
        (polynomialCoordinates f).inv (jacobian f ((equationCoordinates f).hom x)) at hy
      rw [hy]
      exact (polynomialCoordinates f).toLinearEquiv.apply_symm_apply _
    change ((M₀).complex ()).d (-1) 0
      ((conormalTermIso P O T h (-1)).hom x) =
        (conormalTermIso P O T h 0).hom ((conormal f).d (-1) 0 x)
    have hl : (conormalTermIso P O T h (-1)).hom x =
        equationBasis P O T h ((equationCoordinates f).hom x) := by
      simp only [conormalTermIso, dite_eq_right (by decide : (-1 : ℤ) ≠ 0)]
      rfl
    have hr (y : (conormal f).X 0) : (conormalTermIso P O T h 0).hom y =
        polynomialBasis P O T h ((polynomialCoordinates f).hom y) := by
      simp only [conormalTermIso]
      rfl
    rw [hl, hr, hx]
    exact d_equationBasis P O T h hT _
  · by_cases h₀ : i = 0
    · subst i
      have : Subsingleton (term M₀ ((0 : ℤ) + 1)) :=
        cotangentTerm_subsingleton P O T h 1 (by decide) (by decide)
      ext x
      exact Subsingleton.elim _ _
    · have : Subsingleton (((restriction f).obj (conormal f)).X i) :=
        ModuleCat.subsingleton_of_isZero (Functor.map_isZero (restrictToField (f := f))
          (show IsZero ((conormal f).X i) from isZero_double_X _ _ i hi h₀))
      ext x
      rw [show x = 0 from Subsingleton.elim _ _]
      simp


set_option backward.isDefEq.respectTransparency false in
private theorem conormalTermIso₀ (h : IsGradedBasis (extendedGenerator P O T))
    (x : (conormal f).X 0) :
    (conormalTermIso P O T h 0).hom x =
      polynomialBasis P O T h ((polynomialCoordinates f).hom x) := by
  simp only [conormalTermIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem conormalTermIso₁ (h : IsGradedBasis (extendedGenerator P O T))
    (x : (conormal f).X (-1)) :
    (conormalTermIso P O T h (-1)).hom x =
      equationBasis P O T h ((equationCoordinates f).hom x) := by
  simp only [conormalTermIso, dite_eq_right (by decide : (-1 : ℤ) ≠ 0)]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sum_qact_smul {d : ℕ} (M : (B₀).Module) (n : ℤ)
    (e : Fin d → term M n) (v : Fin d → Quotient f) (a : Quotient f) :
    (∑ j, qact M n (e j) ((a • v) j)) = qact M n (∑ j, qact M n (e j) (v j)) a := by
  let L : term M n →ₗ[k] term M n := (act M n 0 n (add_zero n)).flip a
  change _ = L _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change qact M n (e j) (a * v j) = qact M n (qact M n (e j) (v j)) a
  rw [qact_assoc, mul_comm]

set_option backward.isDefEq.respectTransparency false in
private theorem conormalTermIso_smul (h : IsGradedBasis (extendedGenerator P O T)) (n : ℤ)
    (x : (conormal f).X n) (a : Quotient f) :
    (conormalTermIso P O T h n).hom (a • x) =
      qact M₀ n ((conormalTermIso P O T h n).hom x) a := by
  by_cases h₀ : n = 0
  · subst n
    rw [conormalTermIso₀, conormalTermIso₀, map_smul, polynomialBasis_apply, polynomialBasis_apply]
    exact sum_qact_smul M₀ 0 _ _ _
  · by_cases h₁ : n = -1
    · subst n
      rw [conormalTermIso₁, conormalTermIso₁, map_smul, equationBasis_apply, equationBasis_apply]
      exact sum_qact_smul M₀ (-1) _ _ _
    · have := cotangentTerm_subsingleton P O T h n h₀ h₁
      exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
private theorem sum_qact_single {d : ℕ} (M : (B₀).Module) (n : ℤ)
    (e : Fin d → term M n) (i : Fin d) :
    (∑ j, qact M n (e j) ((Pi.single i 1 : Fin d → Quotient f) j)) = e i := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
    exact M.act_id () n _
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    exact map_zero _
  · simp

set_option backward.isDefEq.respectTransparency false in
private def conormalComparison
    (hT : T.Formulas (P.koszul.augmentation :
      P.koszul.obj.toCommDGAlgebra ⟶ B₀) (regular B₀)) :
    ConormalComparison P O T := by
  let h := extendedBasis P O T hT
  let e := conormalIso P O T h hT
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · intro n a x
    apply (Hom.isoApp e n).toLinearEquiv.injective
    change (conormalTermIso P O T h n).hom
      ((e.inv.f n) (qact M₀ n x a)) =
      (conormalTermIso P O T h n).hom (a • (show (conormal f).X n from e.inv.f n x))
    rw [conormalTermIso_smul]
    have he (y : term M₀ n) : (conormalTermIso P O T h n).hom (e.inv.f n y) = y :=
      (Hom.isoApp e n).toLinearEquiv.apply_symm_apply y
    rw [he, he]
  · intro j
    let x := (polynomialCoordinates f).inv (Pi.single j 1)
    have hx : e.hom.f 0 x = extendedSymbol P O T 0
          (P.koszul.base.chainMap.f 0 (MvPolynomial.X j)) := by
      change (conormalTermIso P O T h 0).hom x = _
      rw [conormalTermIso₀]
      have hx : (polynomialCoordinates f).hom x = Pi.single j 1 :=
        (polynomialCoordinates f).toLinearEquiv.apply_symm_apply _
      rw [hx, polynomialBasis_apply, sum_qact_single]
      exact extendedGenerator_poly P O T j
    change (polynomialCoordinates f).hom (e.inv.f 0 _) = _
    rw [← hx]
    have hh : e.inv.f 0 (e.hom.f 0 x) = x :=
      (Hom.isoApp e 0).toLinearEquiv.symm_apply_apply x
    rw [hh]
    exact (polynomialCoordinates f).toLinearEquiv.apply_symm_apply _
  · intro i
    let x := (equationCoordinates f).inv (Pi.single i 1)
    have hx : e.hom.f (-1) x = extendedSymbol P O T (-1) (P.koszul.generator i) := by
      change (conormalTermIso P O T h (-1)).hom x = _
      rw [conormalTermIso₁]
      have hx : (equationCoordinates f).hom x = Pi.single i 1 :=
        (equationCoordinates f).toLinearEquiv.apply_symm_apply _
      rw [hx, equationBasis_apply, sum_qact_single]
      exact extendedGenerator_equation P O T i
    change (equationCoordinates f).hom (e.inv.f (-1) _) = _
    rw [← hx]
    have hh : e.inv.f (-1) (e.hom.f (-1) x) = x :=
      (Hom.isoApp e (-1)).toLinearEquiv.symm_apply_apply x
    rw [hh]
    exact (equationCoordinates f).toLinearEquiv.apply_symm_apply _


section Hom

open Specs.DerivedFormalization.DG.HomComplex (Family RightLinear gradedHom component homComplex)

variable (E : ConormalComparison P O T)

local notation "N₀" => regular B₀

set_option backward.isDefEq.respectTransparency false in
private def quotientStalkTermIso (j : ℤ) :
    ((restriction f).obj (quotientStalk f)).X j ≅ (B₀).complex.X j := by
  by_cases h : j = 0
  · subst j
    exact
      ({ toFun := id
         invFun := id
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl
         map_add' := fun _ _ => rfl
         map_smul' := fun a x =>
           IsScalarTower.algebraMap_smul (Quotient f) a (show Quotient f from x) } :
        (restrictToField (f := f)).obj (ModuleCat.of (Quotient f) (Quotient f)) ≃ₗ[k]
          Quotient f).toModuleIso
  · have : Subsingleton (((restriction f).obj (quotientStalk f)).X j) :=
        ModuleCat.subsingleton_of_isZero ((restrictToField (f := f)).map_isZero (stalkTerm_isZero f j h))
    have : Subsingleton ((B₀).complex.X j) := ModuleCat.subsingleton_of_isZero
      (ordinaryTerm_isZero (quotientAlg (PolynomialAlgebra k s) f) j h)
    exact (LinearEquiv.ofSubsingleton (R := k)
      (((restriction f).obj (quotientStalk f)).X j) ((B₀).complex.X j)).toModuleIso

private def quotientStalkIso : (restriction f).obj (quotientStalk f) ≅ (B₀).complex :=
  Hom.isoOfComponents quotientStalkTermIso (by
    intro i j _
    have hl : (B₀).complex.d i j = 0 := rfl
    have hr : ((restriction f).obj (quotientStalk f)).d i j = 0 :=
      (restrictToField (f := f)).map_zero _ _
    rw [hl, hr, comp_zero, zero_comp])

private theorem quotientStalkIso_zero (x : (quotientStalk f).X 0) :
    (quotientStalkIso (f := f)).hom.f 0 x = (show (B₀).complex.X 0 from x) := rfl

private theorem quotientStalkIso_smul (j : ℤ) (x : (quotientStalk f).X j) (a : Quotient f) :
    (quotientStalkIso (f := f)).hom.f j (a • x) =
      qact N₀ j ((quotientStalkIso (f := f)).hom.f j x) a := by
  by_cases hj : j = 0
  · subst j
    have h₁ := quotientStalkIso_zero (f := f) (a • x)
    have h₂ := quotientStalkIso_zero (f := f) x
    exact h₁.trans ((mul_comm a (show Quotient f from x)).trans
      (congrArg (fun y => qact N₀ 0 y a) h₂.symm))
  · have := ModuleCat.subsingleton_of_isZero
      (ordinaryTerm_isZero (quotientAlg (PolynomialAlgebra k s) f) j hj)
    exact Subsingleton.elim _ _

private def conjugateCochain {n : ℤ} (a : Cochain (conormal f) (quotientStalk f) n) :
    Cochain ((M₀).complex ()) ((B₀).complex) n :=
  ((Cochain.ofHom E.iso.hom).comp (a.map (restrictToField (f := f))) (zero_add n)).comp
    (Cochain.ofHom (quotientStalkIso (f := f)).hom) (add_zero n)

set_option backward.isDefEq.respectTransparency false in
private theorem conjugateCochain_apply {n : ℤ} (a : Cochain (conormal f) (quotientStalk f) n)
    (i j : ℤ) (h : i+n=j) (x : term M₀ i) :
    (conjugateCochain P O T E a).v i j h x =
      (quotientStalkIso (f := f)).hom.f j (a.v i j h (E.iso.hom.f i x)) := by
  unfold conjugateCochain
  rw [Cochain.comp_v _ _ _ i j j h (add_zero j),
    Cochain.comp_v _ _ _ i i j (add_zero i) h]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def toGraded {n : ℤ} (a : Cochain (conormal f) (quotientStalk f) n) :
    gradedHom M₀ N₀ n :=
  ⟨fun _ => conjugateCochain P O T E a, by
    rintro ⟨⟩ ⟨⟩ i j l ir lr h hi hl x z
    by_cases hj : j = 0
    · subst j
      have hil : l = i := h.symm.trans (add_zero i)
      cases hil
      have hir : lr = ir := hl.symm.trans hi
      cases hir
      change (conjugateCochain P O T E a).v i ir hi (qact M₀ i x z) =
        qact N₀ ir ((conjugateCochain P O T E a).v i ir hi x) z
      rw [conjugateCochain_apply, conjugateCochain_apply]
      have e₁ := E.scalar i z x
      have e₂ := (a.v i ir hi).hom.map_smul (show Quotient f from z) (E.iso.hom.f i x)
      have e₃ := quotientStalkIso_smul (f := f) ir (a.v i ir hi (E.iso.hom.f i x)) z
      exact (congrArg (fun y => (quotientStalkIso (f := f)).hom.f ir (a.v i ir hi y)) e₁).trans
        ((congrArg ((quotientStalkIso (f := f)).hom.f ir) e₂).trans e₃)
    · have hz := ModuleCat.subsingleton_of_isZero
        (ordinaryTerm_isZero (quotientAlg (PolynomialAlgebra k s) f) j hj)
      have hz' : z = 0 := hz.elim _ _
      subst z
      simp only [map_zero]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_inv_smul (i : ℤ) (a : Quotient f) (x : (conormal f).X i) :
    E.iso.inv.f i (a • x) = qact M₀ i (E.iso.inv.f i x) a := by
  let e := (Hom.isoApp E.iso i).toLinearEquiv
  apply e.injective
  have hx : (show (conormal f).X i from e (e.symm x)) = x := e.apply_symm_apply x
  have ha := e.apply_symm_apply (a • x)
  exact ha.trans ((congrArg (fun y : (conormal f).X i => a • y) hx.symm).trans
    (E.scalar i a (E.iso.inv.f i x)).symm)

set_option backward.isDefEq.respectTransparency false in
private def fromGraded {n : ℤ} (a : gradedHom M₀ N₀ n) :
    Cochain (conormal f) (quotientStalk f) n :=
  Cochain.mk fun i j h => ModuleCat.ofHom (X := (conormal f).X i) (Y := (quotientStalk f).X j)
    { toFun := fun x => (quotientStalkIso (f := f)).inv.f j
        (component a () i j h (E.iso.inv.f i x))
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro b x
        let e := (Hom.isoApp (quotientStalkIso (f := f)) j).toLinearEquiv
        apply e.injective
        change e (e.symm (component a () i j h (E.iso.inv.f i (b • x)))) =
          e (b • (show (quotientStalk f).X j from e.symm (component a () i j h (E.iso.inv.f i x))))
        rw [LinearEquiv.apply_symm_apply, comparison_inv_smul P O T E i]
        have h₁ : component a () i j h (qact M₀ i (E.iso.inv.f i x) b) =
            qact N₀ j (component a () i j h (E.iso.inv.f i x)) b :=
          a.property (a := ()) (b := ()) i 0 i j j (add_zero i) h h (E.iso.inv.f i x) b
        rw [h₁]
        have h₂ := quotientStalkIso_smul (f := f) j
          (e.symm (component a () i j h (E.iso.inv.f i x))) b
        change e (b • (show (quotientStalk f).X j from e.symm _)) = qact N₀ j (e (e.symm _)) b at h₂
        rw [LinearEquiv.apply_symm_apply] at h₂
        exact h₂.symm }

private theorem graded_ext {n : ℤ} {a b : gradedHom M₀ N₀ n}
    (e : ∀ i j (h : i+n=j) (x : term M₀ i), component a () i j h x = component b () i j h x) :
    a = b := by
  apply Subtype.ext
  funext v
  cases v
  apply Cochain.ext
  intro i j h
  apply ModuleCat.hom_ext
  exact LinearMap.ext (e i j h)

set_option backward.isDefEq.respectTransparency false in
private def homTermEquiv (n : ℤ) :
    ((restriction f).obj (conormalHom f)).X n ≃ₗ[k] (homComplex M₀ N₀).X n where
  toFun := toGraded P O T E
  invFun := fromGraded P O T E
  left_inv a := by
    apply Cochain.ext
    intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (quotientStalkIso (f := f)).inv.f j
      ((conjugateCochain P O T E a).v i j h (E.iso.inv.f i x)) = a.v i j h x
    rw [conjugateCochain_apply]
    have hx : E.iso.hom.f i (E.iso.inv.f i x) = x :=
      (Hom.isoApp E.iso i).toLinearEquiv.apply_symm_apply x
    rw [hx]
    exact (Hom.isoApp (quotientStalkIso (f := f)) j).toLinearEquiv.symm_apply_apply _
  right_inv a := by
    apply graded_ext P O T
    intro i j h x
    change (conjugateCochain P O T E (fromGraded P O T E a)).v i j h x = _
    rw [conjugateCochain_apply]
    change (quotientStalkIso (f := f)).hom.f j ((quotientStalkIso (f := f)).inv.f j
      (component a () i j h (E.iso.inv.f i (E.iso.hom.f i x)))) = _
    have hx : E.iso.inv.f i (E.iso.hom.f i x) = x :=
      (Hom.isoApp E.iso i).toLinearEquiv.symm_apply_apply x
    rw [hx]
    exact (Hom.isoApp (quotientStalkIso (f := f)) j).toLinearEquiv.apply_symm_apply _
  map_add' a b := by
    apply graded_ext P O T
    intro i j h x
    let a' : Cochain (conormal f) (quotientStalk f) n := a
    let b' : Cochain (conormal f) (quotientStalk f) n := b
    change (conjugateCochain P O T E (a' + b')).v i j h x =
      (conjugateCochain P O T E a').v i j h x + (conjugateCochain P O T E b').v i j h x
    simp only [conjugateCochain_apply, Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply,
      map_add]
  map_smul' c a := by
    apply graded_ext P O T
    intro i j h x
    let a' : Cochain (conormal f) (quotientStalk f) n := a
    change (conjugateCochain P O T E ((algebraMap k (Quotient f) c) • a')).v i j h x =
      c • (conjugateCochain P O T E a').v i j h x
    rw [conjugateCochain_apply, conjugateCochain_apply, Cochain.smul_v]
    have e : (((algebraMap k (Quotient f) c) • a.v i j h) (E.iso.hom.f i x) :
        (quotientStalk f).X j) = (algebraMap k (Quotient f) c) • a.v i j h (E.iso.hom.f i x) := rfl
    rw [e]
    let L := ((quotientStalkIso (f := f)).hom.f j).hom
    let y := a.v i j h (E.iso.hom.f i x)
    change L (c • (show (restrictToField (f := f)).obj ((quotientStalk f).X j) from y)) = c • L y
    exact map_smul L c (show (restrictToField (f := f)).obj ((quotientStalk f).X j) from y)

private def homIso :
    (restriction f).obj (conormalHom f) ≅ homComplex M₀ N₀ :=
  Hom.isoOfComponents (fun n => (homTermEquiv P O T E n).toModuleIso) (by
    intro i j _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext b
    cases b
    let a' : Cochain (conormal f) (quotientStalk f) i := a
    change δ i j (conjugateCochain P O T E a') = conjugateCochain P O T E (δ i j a')
    simp only [conjugateCochain, δ_comp_ofHom, δ_ofHom_comp, δ_map])

private theorem homIso_apply (m n : ℤ) (hmn : m+n=0)
    (a : Cochain (conormal f) (quotientStalk f) n) (x : term M₀ m) :
    component ((homIso P O T E).hom.f n a) () m 0 hmn x =
      (show (B₀).complex.X 0 from a.v m 0 hmn (E.iso.hom.f m x)) :=
  (conjugateCochain_apply P O T E a m 0 hmn x).trans (quotientStalkIso_zero _)

end Hom

end Cotangent

/-- The conormal complex and the degree-one internal Hom of the regular quotient. -/
theorem conormalModel : ConormalModel.{u} := by
  intro k _ _ s r f hreg
  obtain ⟨P⟩ := existsKoszulPresentation f KoszulZeroLocus.koszulZeroLocus.{u,u} hreg
  let O : P.relativeDifferentials := Kahler.model (coefficientMap k s ≫ P.koszul.base)
  obtain ⟨T, h, hT, ⟨C⟩⟩ :=
    DerivedFormalization.Affine.CotangentComplex.cotangentExists (groundMap f)
  let E := conormalComparison P O T (hT P.koszul.augmentation _)
  exact ⟨P, O, T, h, C, E, symbolDifferentials P O,
    ⟨homIso P O T E, homIso_apply P O T E⟩, ⟨cokernelComparison f⟩⟩

end

end DerivedFormalization.Affine.CompleteIntersectionConormal
