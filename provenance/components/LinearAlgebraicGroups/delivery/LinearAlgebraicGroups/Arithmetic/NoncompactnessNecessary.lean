import Specs.LinearAlgebraicGroups.Arithmetic.NoncompactnessNecessary
import LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Set Topology MvPolynomial
open IsDedekindDomain ValuativeRel
open scoped RestrictedProduct Polynomial NumberField

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

universe u v

namespace LinearAlgebraicGroups.Arithmetic.NoncompactnessNecessary

open AdelicGroups
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.NoncompactnessNecessary (InsidePoints outsideDiagonalImage)

section Projection

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
variable (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place)

private def joinedCoordinates (p : InsidePoints D i S × Adeles D i S) (w : Outside D ∅) :
    LocalPoints D i w.1 := by
  classical
  exact if hw : w.1 ∈ S then p.1 ⟨w.1, hw⟩ else p.2 ⟨w.1, hw⟩

private def outsideIndex (w : Outside D S) : Outside D ∅ :=
  ⟨w.1, by simp⟩

private theorem cofinite_joined (T : Set (Outside D S)) (hT : cofinite ≤ 𝓟 T) :
    cofinite ≤ 𝓟 (outsideIndex D S '' T) := by
  classical
  rw [le_principal_iff, mem_cofinite] at hT ⊢
  have hInside : {w : Outside D ∅ | w.1 ∈ S}.Finite :=
    S.finite_toSet.preimage Subtype.val_injective.injOn
  refine (hInside.union (hT.image (outsideIndex D S))).subset ?_
  intro w hw
  by_cases h : w.1 ∈ S
  · exact Or.inl h
  · refine Or.inr ⟨⟨w.1, h⟩, ?_, Subtype.ext rfl⟩
    exact fun hmem => hw ⟨⟨w.1, h⟩, hmem, Subtype.ext rfl⟩

private def joinPoints (p : InsidePoints D i S × Adeles D i S) : Adeles D i ∅ :=
  RestrictedProduct.mk (joinedCoordinates D i S p) <| by
    classical
    have h : outsideIndex D S '' {w | p.2 w ∈ localSubgroup D i w.1} ∈
        (cofinite : Filter (Outside D ∅)) :=
      le_principal_iff.mp (cofinite_joined D S _ (le_principal_iff.mpr p.2.eventually))
    filter_upwards [h] with _ hw
    obtain ⟨⟨w, hw⟩, hmem, rfl⟩ := hw
    change joinedCoordinates D i S p (outsideIndex D S ⟨w, hw⟩) ∈ localSubgroup D i w
    simpa [joinedCoordinates, outsideIndex, hw] using hmem

private theorem continuous_joinPoints : Continuous (joinPoints D i S) := by
  classical
  let R (w : Outside D S) := LocalPoints D i w.1
  let A (w : Outside D S) : Set (R w) := localSubgroup D i w.1
  have hA (w : Outside D S) : IsOpen (A w) := localSubgroup_open D i w.1
  refine (RestrictedProduct.continuous_dom_prod_left hA).mpr ?_
  intro T hT
  let W := outsideIndex D S '' T
  let join : InsidePoints D i S × (Πʳ w, [R w, A w]_[𝓟 T]) →
      Πʳ w : Outside D ∅, [LocalPoints D i w.1, localSubgroup D i w.1]_[𝓟 W] :=
    fun p => RestrictedProduct.mk
      (joinedCoordinates D i S
        (p.1, RestrictedProduct.inclusion R A hT p.2))
      (mem_principal.mpr <| by
        rintro _ ⟨⟨w, hS⟩, hw, rfl⟩
        change joinedCoordinates D i S (p.1, RestrictedProduct.inclusion R A hT p.2)
          (outsideIndex D S ⟨w, hS⟩) ∈ localSubgroup D i w
        unfold joinedCoordinates
        split
        · contradiction
        · exact (mem_principal.mp p.2.eventually) hw)
  have hc : Continuous join := by
    refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun w => ?_
    by_cases hw : w.1 ∈ S
    · have he : (fun p => join p w) = fun p => p.1 ⟨w.1, hw⟩ := by
        funext p
        change joinedCoordinates D i S _ w = _
        unfold joinedCoordinates
        split
        · rfl
        · contradiction
      change Continuous (fun p => join p w)
      rw [he]
      exact (continuous_apply (A := fun w : (↑S : Set D.Place) => LocalPoints D i w.1)
        ⟨w.1, hw⟩).comp continuous_fst
    · have he : (fun p => join p w) = fun p => p.2 ⟨w.1, hw⟩ := by
        funext p
        change joinedCoordinates D i S _ w = _
        unfold joinedCoordinates
        split
        · contradiction
        · rfl
      change Continuous (fun p => join p w)
      rw [he]
      exact (RestrictedProduct.continuous_eval (R := R) (A := A) (𝓕 := 𝓟 T) ⟨w.1, hw⟩).comp
        continuous_snd
  exact (RestrictedProduct.continuous_inclusion (cofinite_joined D S T hT)).comp hc

private theorem joinPoints_inside (p : InsidePoints D i S × Adeles D i S)
    (w : D.Place) (hw : w ∈ S) :
    joinPoints D i S p ⟨w, by simp⟩ = p.1 ⟨w, hw⟩ := by
  change joinedCoordinates D i S p _ = _
  unfold joinedCoordinates
  split
  · rfl
  · contradiction

private theorem joinPoints_outside (p : InsidePoints D i S × Adeles D i S)
    (w : Outside D S) : joinPoints D i S p (outsideIndex D S w) = p.2 w := by
  change joinedCoordinates D i S p (outsideIndex D S w) = _
  unfold joinedCoordinates
  split
  · exact (w.2 (by assumption)).elim
  · cases w
    rfl

private theorem outsideDiagonal_eq_image :
    outsideDiagonalImage D i S =
      Prod.snd '' (joinPoints D i S ⁻¹' Specs.DiscreteDiagonals.groupDiagonalImage D i) := by
  classical
  ext x
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨⟨fun w => localPoint D i w.1 g, x⟩, ⟨g, fun w => ?_⟩, rfl⟩
    obtain ⟨w, _⟩ := w
    by_cases hw : w ∈ S
    · exact joinPoints_inside D i S _ w hw
    · exact (joinPoints_outside D i S _ ⟨w, hw⟩).trans (hg ⟨w, hw⟩)
  · rintro ⟨⟨p, x⟩, ⟨g, hg⟩, rfl⟩
    exact ⟨g, fun w => (joinPoints_outside D i S (p, x) w).symm.trans
      (hg (outsideIndex D S w))⟩

theorem compactInsideClosedDiscrete :
    Specs.NoncompactnessNecessary.CompactInsideClosedDiscrete.{u, v} := by
  intro K _ G D i S hcompact
  let := hcompact
  obtain ⟨hclosed, hdiscrete⟩ := DiscreteDiagonals.groupClosedDiscrete D i
  let C := joinPoints D i S ⁻¹' Specs.DiscreteDiagonals.groupDiagonalImage D i
  rw [outsideDiagonal_eq_image]
  have hc : IsClosed C := hclosed.preimage (continuous_joinPoints D i S)
  refine ⟨isClosedMap_snd_of_compactSpace _ hc, ?_⟩
  refine isDiscrete_iff_forall_mem_exists_isClosed.mpr fun B hB => ⟨B, ?_, inter_eq_left.mpr hB⟩
  have hclosedPreimage : IsClosed (joinPoints D i S '' (C ∩ Prod.snd ⁻¹' B)) :=
    isClosed_of_subset_discrete_closed
      (by rintro _ ⟨p, hp, rfl⟩; exact hp.1) hdiscrete hclosed
  have heq : joinPoints D i S ⁻¹' (joinPoints D i S '' (C ∩ Prod.snd ⁻¹' B)) =
      C ∩ Prod.snd ⁻¹' B := by
    apply Set.preimage_image_eq _ ?_
    intro p q hpq
    apply Prod.ext
    · funext w
      obtain ⟨w, hw⟩ := w
      exact (joinPoints_inside D i S p w hw).symm.trans
        ((congrArg (fun a : Adeles D i ∅ => a ⟨w, by simp⟩) hpq).trans
          (joinPoints_inside D i S q w hw))
    · apply RestrictedProduct.ext
      intro w
      exact (joinPoints_outside D i S p w).symm.trans
        ((congrArg (fun a : Adeles D i ∅ => a (outsideIndex D S w)) hpq).trans
          (joinPoints_outside D i S q w))
  have hp := hclosedPreimage.preimage (continuous_joinPoints D i S)
  rw [heq] at hp
  convert isClosedMap_snd_of_compactSpace _ hp using 1
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := hB hx
    exact ⟨p, ⟨hp.1, show p.2 ∈ B from hp.2.symm ▸ hx⟩, hp.2⟩
  · rintro ⟨p, hp, rfl⟩
    exact hp.2

end Projection

section FinitePlaces

private theorem intJacobson : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hp : P = ⊥
  · subst P
    refine le_antisymm (fun x hx => ?_) bot_le
    change x = 0
    by_contra hn
    obtain ⟨p, hpx, hp⟩ := Nat.exists_infinite_primes (x.natAbs + 1)
    let Q := Ideal.span {(p : ℤ)}
    have hprime : Q.IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.mp hp)
    have hne : Q ≠ ⊥ := by
      intro h
      have hm : (p : ℤ) ∈ Q := Ideal.subset_span (Set.mem_singleton _)
      rw [h] at hm
      exact hp.ne_zero (by exact_mod_cast (show (p : ℤ) = 0 from hm))
    have hxm : x ∈ Q :=
      (show (⊥ : Ideal ℤ).jacobson ≤ Q from sInf_le ⟨bot_le, hprime.isMaximal hne⟩) hx
    have hdvd := (Ideal.mem_span_singleton.mp hxm)
    have h := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natAbs_dvd_natAbs.mpr hdvd)
    simp only [Int.natAbs_natCast] at h
    omega
  · let := hP.isMaximal hp
    exact Ideal.jacobson_eq_self_of_isMaximal

private theorem infiniteHeightOne (R : Type*) [CommRing R] [IsDedekindDomain R]
    [IsJacobsonRing R] (hf : ¬ IsField R) : Infinite (HeightOneSpectrum R) := by
  classical
  let eqv := HeightOneSpectrum.equivMaximalSpectrum hf
  suffices Infinite (MaximalSpectrum R) from Infinite.of_injective eqv.symm eqv.symm.injective
  by_contra! h
  letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  have hne (p : MaximalSpectrum R) : p.asIdeal ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField p.isMaximal hf
  choose a ha ha0 using fun p : MaximalSpectrum R =>
    (Submodule.ne_bot_iff p.asIdeal).mp (hne p)
  let b := ∏ p : MaximalSpectrum R, a p
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => ha0 p
  have hb' : b ∈ Ring.jacobson R := by
    rw [Ring.jacobson_eq_sInf_isMaximal, Ideal.mem_sInf]
    intro I hI
    let p : MaximalSpectrum R := ⟨I, hI⟩
    unfold b
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ p)]
    exact I.mul_mem_left _ (ha p)
  have he : Ring.jacobson R = ⊥ := by
    rw [← Ideal.jacobson_bot, ← Ideal.radical_eq_jacobson]
    exact nilradical_eq_zero R
  rw [he] at hb'
  exact hb (show b = 0 from hb')

private theorem exists_finiteOutside {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (S : Finset D.Place) :
    ∃ w : D.FinitePlace, Sum.inl w ∉ S := by
  classical
  have h : Infinite D.FinitePlace := by
    cases D with
    | number hK =>
      letI := hK
      letI := intJacobson
      letI := isJacobsonRing_of_isIntegral (R := ℤ) (S := 𝓞 K)
      exact infiniteHeightOne (𝓞 K) (NumberField.RingOfIntegers.not_isField K)
    | function F t =>
      letI := t.polynomialAlgebra
      change Infinite (FunctionPlace K)
      have hinj : Function.Injective (algebraMap F[X] t.integerRing) := by
        intro a b h
        exact (transcendental_iff_injective.mp t.transcendental)
          (congrArg (fun z : t.integerRing => (z : K)) h)
      let : Algebra.IsIntegral F[X] t.integerRing :=
        inferInstanceAs (Algebra.IsIntegral F[X] (integralClosure F[X] K))
      let := isJacobsonRing_of_isIntegral (R := F[X]) (S := t.integerRing)
      let := infiniteHeightOne t.integerRing fun hh =>
        Polynomial.not_isField F ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hh)
      exact Infinite.of_injective t.placeOfPrime t.placeOfPrime_injective
  obtain ⟨w, hw⟩ := (S.preimage Sum.inl Sum.inl_injective.injOn).exists_notMem
  exact ⟨w, fun hw' => hw (Finset.mem_preimage.mpr hw')⟩

end FinitePlaces

section PolynomialDerivative

variable {k F I : Type*} [Field k] [NontriviallyNormedField F] [Algebra k F]
  [Fintype I] [DecidableEq I]

private def polynomialDerivative (x : I → F) (p : MvPolynomial I k) :
    (I → F) →L[F] F :=
  ∑ j : I, aeval x (pderiv j p) • ContinuousLinearMap.proj (R := F) j

private theorem hasStrictFDerivAt_aeval (p : MvPolynomial I k) (x : I → F) :
    HasStrictFDerivAt (fun y : I → F => aeval y p) (polynomialDerivative x p) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have he : polynomialDerivative x (C a) = 0 := by
        ext y
        simp [polynomialDerivative, smul_eq_mul]
      rw [he]
      simpa using (hasStrictFDerivAt_const (𝕜 := F) (algebraMap k F a) x)
  | add p q hp hq =>
      convert hp.add hq using 1
      · ext y
        exact map_add (aeval y) p q
      · ext y
        simp [polynomialDerivative, Finset.sum_add_distrib, add_mul]
  | mul_X p i hp =>
      have h := hp.mul (ContinuousLinearMap.proj (R := F) (φ := fun _ : I => F) i
        |>.hasStrictFDerivAt (x := x))
      convert h using 1
      · ext y
        simp
      · ext y
        simp only [polynomialDerivative, _root_.sum_apply,
          _root_.add_apply, _root_.smul_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul, Derivation.leibniz,
          aeval_X, map_add, map_mul, pderiv_X]
        simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [Ne.symm hji]
        · simp

end PolynomialDerivative

section Presentation

open Algebra Module

variable {k F A I J : Type*} [Field k] [NontriviallyNormedField F] [CompleteSpace F]
  [Algebra k F] [CommRing A] [Algebra k A] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

private def relationDerivatives (P : SubmersivePresentation k A I J) (x : I → F) :
    (I → F) →L[F] (J → F) :=
  ContinuousLinearMap.pi fun j => polynomialDerivative x (P.relation j)

private def relationVariables (P : SubmersivePresentation k A I J) :
    (J → F) →ₗ[F] (I → F) :=
  (Pi.basisFun F J).constr F fun j => Pi.single (P.map j) 1

omit [CompleteSpace F] [Algebra k F] [Fintype I] [DecidableEq J] in
private theorem relationVariables_on (P : SubmersivePresentation k A I J) (u : J → F) (j : J) :
    relationVariables P u (P.map j) = u j := by
  classical
  simp only [relationVariables, Basis.constr_apply_fintype, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    have h : P.map j ≠ P.map l := fun h => hl (P.map_inj h).symm
    simp [h]
  · simp

omit [CompleteSpace F] [Algebra k F] [Fintype I] [DecidableEq J] in
private theorem relationVariables_off (P : SubmersivePresentation k A I J) (u : J → F) (i : I)
    (hi : i ∉ range P.map) : relationVariables P u i = 0 := by
  classical
  have h (j : J) : P.map j ≠ i := fun h => hi ⟨j, h⟩
  simp [relationVariables, fun j => (h j).symm]

omit [CompleteSpace F] in
private theorem relationJacobian_bijective (P : SubmersivePresentation k A I J)
    (e : A →ₐ[k] F) :
    Function.Bijective ((relationDerivatives P (e ∘ P.val)).toLinearMap ∘ₗ relationVariables P) := by
  let T := (relationDerivatives P (e ∘ P.val)).toLinearMap ∘ₗ relationVariables P
  have hT : T.toMatrix' = ((aeval (e ∘ P.val)).mapMatrix P.jacobiMatrix).transpose := by
    ext i j : 1
    rw [LinearMap.toMatrix'_apply]
    change (relationDerivatives P (e ∘ P.val)) (relationVariables P (Pi.single j 1)) i = _
    have hvar : relationVariables P (Pi.single j (1 : F)) = Pi.single (P.map j) 1 := by
      simp [relationVariables]
    rw [hvar]
    simp [relationDerivatives, polynomialDerivative, Pi.single_apply, P.jacobiMatrix_apply]
  have hdet : IsUnit T.det := by
    rw [← LinearMap.det_toMatrix', hT, Matrix.det_transpose]
    change IsUnit (((aeval (e ∘ P.val)).toRingHom.mapMatrix P.jacobiMatrix).det)
    rw [← RingHom.map_det]
    have h := P.jacobian_isUnit.map e
    rw [P.jacobian_eq_jacobiMatrix_det] at h
    have he : (aeval (e ∘ P.val) : MvPolynomial I k →ₐ[k] F) = e.comp (aeval P.val) := by
      ext i
      simp
    rw [he]
    change IsUnit (e (aeval P.val P.jacobiMatrix.det))
    simpa only [P.algebraMap_apply] using h
  exact (Module.End.isUnit_iff _).mp ((LinearMap.isUnit_iff_isUnit_det T).mpr hdet)

private theorem nearby_points_of_submersivePresentation (P : SubmersivePresentation k A I J)
    (e : A →ₐ[k] F) (i₀ : I) (hi₀ : i₀ ∉ range P.map)
    {U : Set (I → F)} (hU : U ∈ 𝓝 (e ∘ P.val)) :
    ∃ e' : A →ₐ[k] F, e' ∘ P.val ∈ U ∧ e' ≠ e := by
  classical
  let Free := {i : I // i ∉ range P.map}
  let x : I → F := e ∘ P.val
  -- Use the relations and the free coordinates as the components of the local map.
  let f : (I → F) → (J → F) × (Free → F) :=
    fun y => (fun j => aeval y (P.relation j), fun i => y i.1)
  let Q : (I → F) →L[F] (Free → F) := ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := F) i.1
  let R := relationDerivatives P x
  let T := R.prod Q
  have hJ := relationJacobian_bijective P e
  have hzero : ∀ {y : I → F}, Q y = 0 →
      y = relationVariables P (y ∘ P.map) := by
    intro y hy
    funext i
    by_cases hi : i ∈ range P.map
    · obtain ⟨j, rfl⟩ := hi
      rw [relationVariables_on]
      rfl
    · rw [relationVariables_off P _ _ hi]
      exact congrFun hy ⟨i, hi⟩
  have hT : Function.Bijective T := by
    constructor
    · intro y z hyz
      have ht : T (y - z) = 0 := by rw [map_sub, hyz, sub_self]
      have hq : Q (y - z) = 0 :=
        congrArg Prod.snd ht
      have hr : R (y - z) = 0 :=
        congrArg Prod.fst ht
      have he := hzero hq
      rw [he] at hr
      have hn : (y - z) ∘ P.map = 0 := hJ.1 (by
        change R (relationVariables P ((y - z) ∘ P.map)) =
          R (relationVariables P 0)
        rw [hr, map_zero, map_zero])
      rw [hn, map_zero] at he
      exact sub_eq_zero.mp he
    · rintro ⟨z, b⟩
      let y : I → F := fun i => if hi : i ∉ range P.map then b ⟨i, hi⟩ else 0
      obtain ⟨u, hu⟩ := hJ.2 (z - R y)
      refine ⟨y + relationVariables P u, Prod.ext ?_ ?_⟩
      · change R (y + relationVariables P u) = z
        rw [map_add]
        change R (relationVariables P u) = z - R y at hu
        rw [hu, add_sub_cancel]
      · funext i
        change y i.1 + relationVariables P u i.1 = b i
        rw [relationVariables_off P u i.1 i.2, add_zero]
        exact dite_eq_left i.2
  let c := (LinearEquiv.ofBijective T.toLinearMap hT).toContinuousLinearEquiv
  have hf : HasStrictFDerivAt f (c : (I → F) →L[F] (J → F) × (Free → F)) x := by
    have he : (c : (I → F) →L[F] (J → F) × (Free → F)) = T := by
      ext1 y
      rfl
    rw [he]
    exact (hasStrictFDerivAt_pi.mpr fun j => hasStrictFDerivAt_aeval (P.relation j) x).prodMk
      Q.hasStrictFDerivAt
  have hfx : (f x).1 = 0 := by
    funext j
    have he : (aeval (e ∘ P.val) : MvPolynomial I k →ₐ[k] F) = e.comp (aeval P.val) := by
      ext i
      simp
    change aeval (e ∘ P.val) (P.relation j) = 0
    rw [he, AlgHom.comp_apply, P.aeval_val_relation, map_zero]
  have hIm : f '' U ∈ 𝓝 (f x) := by
    rw [← hf.map_nhds_eq_of_equiv]
    exact image_mem_map hU
  let u₀ : Free := ⟨i₀, hi₀⟩
  let line : F → (J → F) × (Free → F) :=
    fun t => (0, fun i => if i = u₀ then t else x i.1)
  have hl : Continuous line := continuous_const.prodMk (continuous_pi fun i => by
    by_cases hi : i = u₀
    · simp only [hi]
      exact continuous_id
    · simp only [ite_eq_right hi]
      exact continuous_const)
  have hline : line (x i₀) = f x := by
    refine Prod.ext hfx.symm ?_
    funext i
    change (if i = u₀ then x i₀ else x i.1) = x i.1
    split
    · rename_i h
      rw [h]
    · rfl
  have hv : line ⁻¹' (f '' U) ∈ 𝓝 (x i₀) :=
    hl.continuousAt.preimage_mem_nhds (hline ▸ hIm)
  have hnb : (𝓝[≠] x i₀).NeBot := inferInstance
  obtain ⟨t, ht, hnt⟩ := Filter.nonempty_of_mem
    (inter_mem (mem_nhdsWithin_of_mem_nhds hv)
      (self_mem_nhdsWithin : {x i₀}ᶜ ∈ 𝓝[≠] x i₀))
  obtain ⟨y, hy, hyl⟩ := ht
  have hrel (j : J) : aeval y (P.relation j) = 0 :=
    congrArg (fun a : (J → F) × (Free → F) => a.1 j) hyl
  have hval : y i₀ = t := by
    simpa [f, line, u₀] using congrArg (fun a : (J → F) × (Free → F) => a.2 u₀) hyl
  let a := aeval (R := k) y
  let b := aeval (R := k) P.val
  have hker : RingHom.ker b ≤ RingHom.ker a := by
    rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hrel j)
  -- Evaluation at the new root descends along the presentation.
  let eB := Ideal.quotientKerAlgEquivOfSurjective (f := b) P.aeval_val_surjective
  let l := Ideal.Quotient.liftₐ (RingHom.ker b) a (fun _ h => hker h)
  let e' := l.comp eB.symm.toAlgHom
  have he' (i : I) : e' (P.val i) = y i := by
    have hb : b (X i) = P.val i := aeval_X _ _
    rw [← hb]
    change l (eB.symm (b (X i))) = _
    have heq : eB (Ideal.Quotient.mk (RingHom.ker b) (X i)) = b (X i) :=
      Ideal.quotientKerAlgEquivOfSurjective_mk P.aeval_val_surjective _
    rw [← heq, AlgEquiv.symm_apply_apply]
    exact aeval_X y i
  refine ⟨e', (funext he' : e' ∘ P.val = y) ▸ hy, ?_⟩
  intro heq
  apply hnt
  exact hval.symm.trans ((he' i₀).symm.trans (congrArg (fun h : A →ₐ[k] F => h (P.val i₀)) heq))

end Presentation

open LinearAlgebraicGroups.Specs.Unipotent (Index)
open LinearAlgebraicGroups.StandardGroups (universalMatrix)
open private matrixPresentation coordinateMap_of_map
  from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation glEvaluation_entry from LinearAlgebraicGroups.Affine.StandardGroups
open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels

@[instance_reducible]
private def finiteCompletionNormedField {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) :
    NontriviallyNormedField (D.Completion (.inl w)) := by
  let F := D.FiniteCompletion w
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  letI : (Valued.v (R := F)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := F) |>.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  exact Valued.toNontriviallyNormedField F (ValueGroupWithZero F)

private theorem finiteCompletion_complete {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) :
    @CompleteSpace (D.Completion (.inl w)) (finiteCompletionNormedField D w).toUniformSpace := by
  let F := D.FiniteCompletion w
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  exact inferInstanceAs (CompleteSpace F)

private theorem localizationPresentation_has_freeVariable
    {K A I J : Type*} [Field K] [CommRing A] [Algebra K A] [Finite I] [Finite J]
    [ConnectedSpace (PrimeSpectrum A)] [Nontrivial (PrimeSpectrum A)]
    (ε : A →ₐ[K] K) (s : A) (hs : ε s ≠ 0)
    (P : Algebra.SubmersivePresentation K (Localization.Away s) I J) :
    ∃ i : I, i ∉ range P.map := by
  classical
  by_contra! h
  have hd : P.dimension = 0 :=
    Nat.sub_eq_zero_of_le (Nat.card_le_card_of_surjective P.map (fun i => h i))
  -- With no free variables the localization is étale over the field.
  letI := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero).mpr
    (P.isStandardSmoothOfRelativeDimension hd)
  let B := Localization.Away s
  letI : Module.Finite K B := Algebra.FormallyUnramified.finite_of_free K B
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  let unit := isUnit_iff_ne_zero.mpr hs
  let εs : B →ₐ[K] K := IsLocalization.Away.liftAlgHom s (f := ε) unit
  have hl (x : A) : εs (algebraMap A B x) = ε x := IsLocalization.Away.lift_eq s unit x
  let x : PrimeSpectrum B := ⟨RingHom.ker εs, RingHom.ker_isPrime εs⟩
  let y := PrimeSpectrum.comap (algebraMap A B) x
  have he : (εs.toRingHom.comp (algebraMap A B)) = ε.toRingHom := RingHom.ext hl
  have hmax : y.asIdeal.IsMaximal := by
    change (RingHom.ker (εs.toRingHom.comp (algebraMap A B))).IsMaximal
    rw [he]
    exact RingHom.ker_isMaximal_of_surjective ε fun t => ⟨algebraMap K A t, by simp⟩
  have ho : IsOpen ({y} : Set (PrimeSpectrum A)) := by
    simpa only [image_singleton] using
      (PrimeSpectrum.localization_away_isOpenEmbedding B s).isOpenMap _ (isOpen_discrete {x})
  have hcl : IsClopen ({y} : Set (PrimeSpectrum A)) :=
    ⟨(PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hmax, ho⟩
  have hy := hcl.eq_univ (singleton_nonempty y)
  obtain ⟨a, ha⟩ := exists_ne y
  exact ha (show a ∈ ({y} : Set (PrimeSpectrum A)) from hy.symm ▸ mem_univ a)

section
variable {K : Type u} [Field K] {G : Specs.AffineAlgebraicGroup K} (i : MatrixRealization G)

private theorem smoothAlgebraOfPresentation (h : Smooth G.val.X.hom)
    (A : TestAlgebra K) (e : (testSpec K).obj (Opposite.op A) ≅ G.val.X) :
    Algebra.Smooth K A := by
  let a : CommRingCat.of K ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap K A)
  suffices Smooth (Spec.map a) from
    RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp this)
  letI : Smooth G.val.X.hom := h
  letI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have he : ((testSpec K).obj (Opposite.op A)).hom = Spec.map a := rfl
  rw [← he, ← Over.w e.hom]
  infer_instance

private def pointOfAlgebraHom {F : Type u} [Field F] [Algebra K F]
    {A : TestAlgebra K} (e : (testSpec K).obj (Opposite.op A) ≅ G.val.X)
    (q : A →ₐ[K] F) : PointsIn i F :=
  (testSpec K).map (CommAlgCat.ofHom q).op ≫ e.hom

private theorem pointOfAlgebraHom_injective {F : Type u} [Field F] [Algebra K F]
    {A : TestAlgebra K} (e : (testSpec K).obj (Opposite.op A) ≅ G.val.X) :
    Function.Injective (pointOfAlgebraHom i (F := F) e) := by
  intro q r hqr
  change (testSpec K).map (CommAlgCat.ofHom q).op ≫ e.hom =
    (testSpec K).map (CommAlgCat.ofHom r).op ≫ e.hom at hqr
  rw [cancel_mono] at hqr
  have hh := Quiver.Hom.op_inj ((algSpec.fullyFaithful (R := CommRingCat.of K)).map_injective hqr)
  exact congrArg CommAlgCat.Hom.hom hh

private theorem chartMatrix {F : Type u} [Field F] [Algebra K F]
    {A : TestAlgebra K} (e : (testSpec K).obj (Opposite.op A) ≅ G.val.X) :
    ∃ a : Matrix (Index.{u} i.size) (Index.{u} i.size) A,
      ∀ (q : A →ₐ[K] F) l m,
        (asMatrix i F (pointOfAlgebraHom i e q)).val l m = q (a l m) := by
  obtain ⟨a, _, ha⟩ := matrixPresentation A e i
  refine ⟨fun l m => a.hom (universalMatrix K _ l m), fun q l m => ?_⟩
  rw [← glEvaluation_entry (k := K)]
  rw [ha F]
  have hp : coordinateMap (k := K) (pointOfAlgebraHom i e q ≫ e.inv) = CommAlgCat.ofHom q := by
    change coordinateMap (((testSpec K).map (CommAlgCat.ofHom q).op ≫ e.hom) ≫ e.inv) = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, coordinateMap_of_map]
  rw [hp]
  rfl

end

section LocalPoints

variable {K : Type u} [Field K] {G : Specs.AffineAlgebraicGroup K}

/-- The group of points over a complete normed field is nondiscrete when
the smooth connected group has a nontrivial underlying scheme. -/
private theorem not_discrete_normedPoints
    (i : MatrixRealization G) (F : Type u) [NontriviallyNormedField F]
    [CompleteSpace F] [Algebra K F]
    (hSmooth : Smooth G.val.X.hom) (hConnected : ConnectedSpace G.val.X.left)
    (hNontrivial : Nontrivial G.val.X.left)
    (hEmb : IsEmbedding (fun g : PointsIn i F => (asMatrix i F g).val)) :
    ¬ DiscreteTopology (PointsIn i F) := by
  classical
  intro hDiscrete
  let := hNontrivial
  obtain ⟨A₀, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  let A : TestAlgebra K := A₀.unop
  let eX : Spec (CommRingCat.of A) ≅ G.val.X.left := (Over.forget _).mapIso e
  let hX := Scheme.homeoOfIso eX
  letI : ConnectedSpace (PrimeSpectrum A) := hX.connectedSpace_iff.mpr hConnected
  letI : Nontrivial (PrimeSpectrum A) := hX.symm.injective.nontrivial
  letI : Algebra.Smooth K A := smoothAlgebraOfPresentation hSmooth A e
  let ε : A →ₐ[K] K := (coordinateMap (k := K) ((1 : PointsIn i K) ≫ e.inv)).hom
  let m : Ideal A := RingHom.ker ε
  letI : m.IsPrime := RingHom.ker_isPrime ε
  obtain ⟨s, hs, hStd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K m
  let B := Localization.Away s
  let l : A →ₐ[K] B := IsScalarTower.toAlgHom K A B
  have hε : ε s ≠ 0 := fun h => hs (RingHom.mem_ker.mpr h)
  let εF : A →ₐ[K] F := (Algebra.ofId K F).comp ε
  have hunit : IsUnit (εF s) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero (algebraMap K F)).mpr hε)
  let εB : B →ₐ[K] F := IsLocalization.Away.liftAlgHom s (f := εF) hunit
  obtain ⟨I, J, _, _, ⟨P⟩⟩ := hStd.out
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype J := Fintype.ofFinite J
  obtain ⟨i₀, hi₀⟩ := localizationPresentation_has_freeVariable ε s hε P
  let r (q : B →ₐ[K] F) := pointOfAlgebraHom i e (q.comp l)
  let M (g : PointsIn i F) := (asMatrix i F g).val
  have hOpen : IsOpen ({r εB} : Set (PointsIn i F)) :=
    @isOpen_discrete _ _ hDiscrete _
  obtain ⟨W, hW, hWpre⟩ := hEmb.isInducing.isOpen_iff.mp hOpen
  obtain ⟨a, ha⟩ := chartMatrix i (F := F) e
  choose p hp using fun j k => P.aeval_val_surjective (l (a j k))
  let φ (x : I → F) : Matrix (Index.{u} i.size) (Index.{u} i.size) F :=
    fun j k => aeval x (p j k)
  have hφ : Continuous φ := by
    refine continuous_matrix fun j k => ?_
    change Continuous (fun x : I → F => aeval x (p j k))
    simp only [MvPolynomial.aeval_def, ← MvPolynomial.eval_map]
    exact MvPolynomial.continuous_eval _
  have hEval (q : B →ₐ[K] F) : φ (q ∘ P.val) = M (r q) := by
    ext j k
    change aeval (q ∘ P.val) (p j k) = (asMatrix i F (pointOfAlgebraHom i e (q.comp l))).val j k
    rw [ha (q.comp l), AlgHom.comp_apply, ← hp j k]
    have he : aeval (q ∘ P.val) = q.comp (aeval P.val) := by
      ext t
      simp
    rw [he]
    rfl
  have hx : φ (εB ∘ P.val) ∈ W := by
    rw [hEval]
    change r εB ∈ M ⁻¹' W
    rw [hWpre]
    exact mem_singleton _
  obtain ⟨q, hq, hqne⟩ := nearby_points_of_submersivePresentation P εB i₀ hi₀
    ((hW.preimage hφ).mem_nhds hx)
  have hqr : r q = r εB := by
    change φ (q ∘ P.val) ∈ W at hq
    rw [hEval] at hq
    change r q ∈ M ⁻¹' W at hq
    rwa [hWpre] at hq
  apply hqne
  exact IsLocalization.algHom_ext (Submonoid.powers s)
    (pointOfAlgebraHom_injective i e hqr)

private theorem not_discrete_finite_localPoints
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.FinitePlace)
    (hSmooth : Smooth G.val.X.hom) (hConnected : ConnectedSpace G.val.X.left)
    (hNontrivial : Nontrivial G.val.X.left) :
    ¬ DiscreteTopology (LocalPoints D i (.inl w)) := by
  let F := D.Completion (.inl w)
  letI : NontriviallyNormedField F := finiteCompletionNormedField D w
  letI : CompleteSpace F := finiteCompletion_complete D w
  letI : Algebra K F := completionAlgebra D (.inl w)
  exact not_discrete_normedPoints i F hSmooth hConnected hNontrivial
    (AdelicGroups.usualLocalTopology D i (.inl w))

end LocalPoints

section Nondensity

variable {K : Type u} [Field K] {G : Specs.AffineAlgebraicGroup K}
variable (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place)

private theorem continuous_singlePlace {J : Type*} {H : J → Type*}
    [∀ j, Group (H j)] [∀ j, TopologicalSpace (H j)]
    [DecidableEq J] (A : ∀ j, Subgroup (H j)) (w : J) :
    Continuous (RestrictedProduct.mulSingle A w) := by
  let T : Set J := {w}ᶜ
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr (by simp [T])
  let f (x : H w) : Πʳ j, [H j, A j]_[𝓟 T] :=
    RestrictedProduct.mk (Pi.mulSingle w x) (mem_principal.mpr (by
      intro j hj
      have hne : j ≠ w := hj
      change Pi.mulSingle w x j ∈ A j
      rw [Pi.mulSingle_eq_of_ne hne]
      exact Subgroup.one_mem _))
  have hc : Continuous f := by
    refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun j => ?_
    change Continuous (fun (x : H w) => Pi.mulSingle w x j)
    by_cases hj : j = w
    · subst j
      simp only [Pi.mulSingle_eq_same]
      exact continuous_id
    · simp only [Pi.mulSingle_eq_of_ne hj]
      exact continuous_const
  exact (RestrictedProduct.continuous_inclusion hT).comp hc

private theorem discreteLocal_of_discreteAdeles {J : Type*} {H : J → Type*}
    [∀ j, Group (H j)] [∀ j, TopologicalSpace (H j)]
    [DecidableEq J] (A : ∀ j, Subgroup (H j)) (w : J)
    (h : DiscreteTopology (Πʳ j, [H j, A j])) : DiscreteTopology (H w) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  let f := RestrictedProduct.mulSingle A w
  have ho : IsOpen ({f x} : Set (Πʳ j, [H j, A j])) := @isOpen_discrete _ _ h _
  have he : f ⁻¹' {f x} = {x} := by
    ext y
    exact (RestrictedProduct.mulSingle_injective A w).eq_iff
  exact he ▸ ho.preimage (continuous_singlePlace A w)

theorem compactInsidePrecludesStrongApproximation :
    Specs.NoncompactnessNecessary.CompactInsidePrecludesStrongApproximation.{u, v} := by
  classical
  intro K _ G D i S _ hSmooth hConnected hPosDim hCompact
  have hNontrivial : Nontrivial G.val.X.left := by
    rw [← not_subsingleton_iff_nontrivial]
    intro h
    exact (not_lt_of_ge (topologicalKrullDim_zero_of_discreteTopology _)) hPosDim
  obtain ⟨hClosed, hDiscrete⟩ := compactInsideClosedDiscrete D i S hCompact
  refine ⟨hClosed, hDiscrete, ?_⟩
  intro hDense
  have hAll : outsideDiagonalImage D i S = univ := by
    have hd : Dense (outsideDiagonalImage D i S) := hDense
    simpa only [hClosed.closure_eq] using hd.closure_eq
  have hAdeles : DiscreteTopology (Adeles D i S) := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun a => ?_
    obtain ⟨U, hU, he⟩ := (isDiscrete_iff_forall_mem_exists_isOpen.mp hDiscrete a)
      (hAll.symm ▸ mem_univ a)
    rw [hAll, inter_univ] at he
    exact he ▸ hU
  obtain ⟨w, hw⟩ := exists_finiteOutside D S
  exact not_discrete_finite_localPoints D i w hSmooth hConnected hNontrivial
    (discreteLocal_of_discreteAdeles (H := fun j : Outside D S => LocalPoints D i j.1)
      (fun j => localSubgroup D i j.1) ⟨.inl w, hw⟩ hAdeles)

end Nondensity

end LinearAlgebraicGroups.Arithmetic.NoncompactnessNecessary
