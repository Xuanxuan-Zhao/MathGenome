import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.LocalStructure

open TensorProduct KaehlerDifferential
open Specs.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion

namespace LinearAlgebraicGroups.Albert.SmoothIdentityCriterion

section Fibers

variable {R A B C K : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Field K]
variable [Algebra R A] [Algebra R B] [Algebra R C]
variable [Algebra A B] [Algebra A C] [Algebra B C]
variable [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B C]
variable [Algebra A K] [Algebra B K] [Algebra C K]
variable [IsScalarTower A B K] [IsScalarTower A C K] [IsScalarTower B C K]

omit [Algebra R A] [Algebra A B] [Algebra A C] [IsScalarTower R A B]
  [IsScalarTower R A C] [Algebra A K] [IsScalarTower A B K] [IsScalarTower A C K] in
@[simp] theorem cotangentFiberMap_tmul (a : K) (v : Ω[B⁄R]) :
    cotangentFiberMap R B C K (a ⊗ₜ v) = a ⊗ₜ map R R B C v := by
  simp [cotangentFiberMap]

variable [IsScalarTower A B C]

theorem cotangentFiberMap_comp :
    cotangentFiberMap R A C K =
      cotangentFiberMap R B C K ∘ₗ cotangentFiberMap R A B K := by
  apply AlgebraTensorModule.ext
  intro a v
  simp only [LinearMap.comp_apply, cotangentFiberMap_tmul]
  have he : map R R A C = (map R R B C).restrictScalars A ∘ₗ map R R A B := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [IsScalarTower.algebraMap_apply A B C]
  rw [he]
  rfl

end Fibers

private theorem bijective_of_field_fiber {S K M N : Type*}
    [CommRing S] [IsLocalRing S] [Field K] [Algebra S K]
    [AddCommGroup M] [Module S M] [Module.Finite S M]
    [AddCommGroup N] [Module S N] [Module.Finite S N] [Module.Free S N]
    (hker : IsLocalRing.maximalIdeal S ≤ RingHom.ker (algebraMap S K))
    (f : M →ₗ[S] N) (hf : Function.Bijective (f.baseChange K)) :
    Function.Bijective f := by
  let k := IsLocalRing.ResidueField S
  let g : k →ₐ[S] K := Ideal.Quotient.liftₐ _ (Algebra.ofId S K) hker
  let : Algebra k K := g.toAlgebra
  let : IsScalarTower S k K := .of_algebraMap_eq' g.comp_algebraMap.symm
  have he : (AlgebraTensorModule.cancelBaseChange S k K K N).toLinearMap ∘ₗ
      (f.baseChange k).baseChange K =
      f.baseChange K ∘ₗ (AlgebraTensorModule.cancelBaseChange S k K K M).toLinearMap := by
    apply AlgebraTensorModule.ext
    intro a v
    induction v using TensorProduct.inductionOn with
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | tmul b x => simp [LinearMap.baseChange_tmul]
  have hf' : Function.Bijective (f.baseChange k) := by
    apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective k K _).mp
    apply ((AlgebraTensorModule.cancelBaseChange S k K K N).comp_bijective _).mp
    change Function.Bijective (⇑((AlgebraTensorModule.cancelBaseChange S k K K N).toLinearMap ∘ₗ
      (f.baseChange k).baseChange K))
    rw [he, LinearMap.coe_comp]
    exact hf.comp (AlgebraTensorModule.cancelBaseChange S k K K M).bijective
  obtain ⟨l, hl⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hf'.1
  refine ⟨Function.HasLeftInverse.injective ⟨l, DFunLike.congr_fun hl⟩, ?_⟩
  rw [← LinearMap.range_eq_top, ← IsLocalRing.map_tensorProduct_mk_eq_top]
  rw [← LinearMap.range_comp]
  apply LinearMap.range_eq_top.mpr
  have ht : (TensorProduct.mk S k N 1) ∘ₗ f =
      ((f.baseChange k).restrictScalars S) ∘ₗ (TensorProduct.mk S k M 1) := by
    ext x
    simp
  rw [ht]
  exact hf'.2.comp (TensorProduct.mk_surjective S M k IsLocalRing.residue_surjective)

private theorem formallyEtale_of_fiber_bijective
    {R B S K : Type*} [CommRing R] [CommRing B] [CommRing S] [Field K]
    [IsLocalRing S] [Algebra R B] [Algebra R S] [Algebra B S] [IsScalarTower R B S]
    [Algebra B K] [Algebra S K] [IsScalarTower B S K]
    [Algebra.FinitePresentation R B] [Algebra.EssFiniteType R S] [Algebra.FormallySmooth R S]
    (hker : IsLocalRing.maximalIdeal S ≤ RingHom.ker (algebraMap S K))
    (hf : Function.Bijective (cotangentFiberMap R B S K)) :
    Algebra.FormallyEtale B S := by
  have : Module.Free S Ω[S⁄R] := Module.free_of_flat_of_isLocalRing
  have hm : Function.Bijective (mapBaseChange R B S) :=
    bijective_of_field_fiber hker _ <|
      ((AlgebraTensorModule.cancelBaseChange B S K K Ω[B⁄R]).symm.bijective_comp _).mp hf
  rw [Algebra.formallyEtale_iff]
  constructor
  · refine ⟨fun a b => ?_⟩
    have hz (x : Ω[S⁄B]) : x = 0 := by
      obtain ⟨v, rfl⟩ := map_surjective R B S x
      obtain ⟨w, rfl⟩ := hm.2 v
      exact (exact_mapBaseChange_map R B S _).mpr ⟨w, rfl⟩
    exact (hz a).trans (hz b).symm
  · refine ⟨fun a b => ?_⟩
    have hz (x : Algebra.H1Cotangent B S) : x = 0 := by
      have hx := (Algebra.H1Cotangent.exact_δ_mapBaseChange R B S).apply_apply_eq_zero x
      have hx' := hm.1 (hx.trans (map_zero _).symm)
      obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ R B S x).mp hx'
      rw [Subsingleton.elim w 0, map_zero] at hw
      exact hw.symm
    exact (hz a).trans (hz b).symm

section EtaleDescent

open Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Flat base change identifies the relations in the two quotient presentations. -/
private theorem tensorKernelOfFlat {P B Q : Type*} [CommRing P] [CommRing B] [CommRing Q]
    [Algebra P B] [Algebra P Q] [Module.Flat P Q] :
    ∃ e : Q ⊗[P] (RingHom.ker (algebraMap P B)) ≃ₗ[Q]
        RingHom.ker (algebraMap Q (Q ⊗[P] B)),
      ∀ (q : Q) (i : RingHom.ker (algebraMap P B)),
        (e (q ⊗ₜ[P] i)).1 = q * algebraMap P Q i := by
  let T := Q ⊗[P] B
  let J := RingHom.ker (algebraMap Q T)
  let ell := Algebra.linearMap P B
  let e : Q ⊗[P] LinearMap.ker ell ≃ₗ[Q]
      LinearMap.ker (AlgebraTensorModule.lTensor Q Q ell) :=
    LinearMap.tensorKerEquiv Q Q ell
  let u := AlgebraTensorModule.rid P Q Q
  have hmap : AlgebraTensorModule.lTensor Q Q ell =
      (Algebra.linearMap Q T) ∘ₗ u.toLinearMap := by
    apply AlgebraTensorModule.ext
    intro q p
    simp only [AlgebraTensorModule.lTensor_tmul]
    change q ⊗ₜ[P] algebraMap P B p = (p • q) ⊗ₜ[P] (1 : B)
    rw [smul_tmul, Algebra.smul_def, mul_one]
  have eqker : LinearMap.ker (AlgebraTensorModule.lTensor Q Q ell) =
      Submodule.comap u.toLinearMap (J : Submodule Q Q) := by
    rw [hmap]
    rfl
  let eu : (Submodule.comap u.toLinearMap (J : Submodule Q Q)) ≃ₗ[Q] J :=
    LinearEquiv.ofBijective (u.toLinearMap.submoduleComap _) <| by
      refine ⟨fun x y h => Subtype.ext (u.injective (congrArg Subtype.val h)), ?_⟩
      intro x
      refine ⟨⟨u.symm x, ?_⟩, Subtype.ext (u.apply_symm_apply x)⟩
      change u (u.symm x) ∈ J
      simpa only [LinearEquiv.apply_symm_apply] using x.2
  refine ⟨e ≪≫ₗ LinearEquiv.ofEq _ _ eqker ≪≫ₗ eu, ?_⟩
  intro q i
  change LinearMap.ker ell at i
  change u ((LinearMap.tensorKer Q Q ell (q ⊗ₜ[P] i)).1) = q * algebraMap P Q (i : P)
  rw [LinearMap.tensorKer_tmul]
  dsimp only [u]
  rw [AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm]

/-- Compare the first cotangent homology using two formally smooth presentations. -/
private theorem compareFirstCotangentHomology
    {R B T : Type*} [CommRing R] [CommRing B] [CommRing T]
    [Algebra R B] [Algebra R T] [Algebra B T] [IsScalarTower R B T] [Module.Flat B T]
    (E : Extension.{u} R B) (F : Extension.{u} R T)
    [FormallySmooth R E.Ring] [FormallySmooth R F.Ring] [Algebra E.Ring F.Ring]
    (f : E.Hom F) (halg : algebraMap E.Ring F.Ring = f.toRingHom)
    (het : f.toRingHom.FormallyEtale)
    (hker : Function.Bijective ((f.mapKer halg).liftBaseChange F.Ring)) :
    Nonempty (T ⊗[B] H1Cotangent R B ≃ₗ[T] H1Cotangent R T) := by
  let e : T ⊗[B] E.H1Cotangent ≃ₗ[T] F.H1Cotangent :=
    Extension.tensorH1CotangentOfFormallyEtale f halg het hker
  let eB : H1Cotangent R B ≃ₗ[B] E.H1Cotangent :=
    (Extension.equivH1CotangentOfFormallySmooth E).symm
  let eT : F.H1Cotangent ≃ₗ[T] H1Cotangent R T :=
    Extension.equivH1CotangentOfFormallySmooth F
  exact ⟨(eB.baseChange (A := T)).trans (e.trans eT)⟩

set_option backward.isDefEq.respectTransparency false in
/-- A formally étale, flat change of the presentation ring commutes with
the first cotangent homology of the presented algebra. -/
private theorem tensorH1OfEtalePresentation
    {R B : Type*} {P Q : Type u} [CommRing R] [CommRing P] [CommRing B] [CommRing Q]
    [Algebra R P] [Algebra R B] [Algebra R Q] [Algebra P B] [Algebra P Q]
    [IsScalarTower R P B] [IsScalarTower R P Q]
    [FormallySmooth R P] [FormallyEtale P Q] [Module.Flat P Q]
    (hp : Function.Surjective (algebraMap P B)) :
    Nonempty ((Q ⊗[P] B) ⊗[B] Algebra.H1Cotangent R B ≃ₗ[Q ⊗[P] B]
      Algebra.H1Cotangent R (Q ⊗[P] B)) := by
  let T := Q ⊗[P] B
  have hsurj : Function.Surjective (algebraMap Q T) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul q b =>
      obtain ⟨p, rfl⟩ := hp b
      refine ⟨q * algebraMap P Q p, ?_⟩
      change (q * algebraMap P Q p) ⊗ₜ[P] (1 : B) = q ⊗ₜ algebraMap P B p
      rw [mul_comm, ← Algebra.smul_def, smul_tmul, Algebra.smul_def, mul_one]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨q₁, rfl⟩ := h₁
      obtain ⟨q₂, rfl⟩ := h₂
      exact ⟨q₁ + q₂, map_add _ _ _⟩
  let E : Extension.{u} R B :=
    { Ring := P, σ := Function.surjInv hp, algebraMap_σ := Function.surjInv_eq hp }
  let F : Extension.{u} R T :=
    { Ring := Q, σ := Function.surjInv hsurj, algebraMap_σ := Function.surjInv_eq hsurj }
  let : IsScalarTower R B T := .of_algebraMap_eq fun r => by
    change algebraMap R Q r ⊗ₜ[P] (1 : B) = 1 ⊗ₜ[P] algebraMap R B r
    simp only [IsScalarTower.algebraMap_apply R P Q, IsScalarTower.algebraMap_apply R P B]
    rw [Algebra.algebraMap_eq_smul_one (R := P) (A := Q), smul_tmul, Algebra.smul_def, mul_one]
  let f : E.Hom F := .ofAlgHom (IsScalarTower.toAlgHom R P Q) (by
    ext p
    change algebraMap P Q p ⊗ₜ[P] (1 : B) = 1 ⊗ₜ[P] algebraMap P B p
    rw [Algebra.algebraMap_eq_smul_one (R := P) (A := Q), smul_tmul, Algebra.smul_def, mul_one])
  have : Module.Flat B T := by
    let e : T ≃ₐ[B] B ⊗[P] Q :=
      { __ := Algebra.TensorProduct.comm P Q B, commutes' := fun _ => rfl }
    exact .of_linearEquiv e.toLinearEquiv
  have : FormallySmooth R E.Ring := ‹FormallySmooth R P›
  have : FormallySmooth R F.Ring := FormallySmooth.comp R P Q
  let : Algebra E.Ring F.Ring := ‹Algebra P Q›
  have hk : Function.Bijective ((f.mapKer rfl).liftBaseChange F.Ring) := by
    obtain ⟨ek, hek⟩ := tensorKernelOfFlat (P := P) (B := B) (Q := Q)
    let e : F.Ring ⊗[E.Ring] E.ker ≃ₗ[F.Ring] F.ker := ek
    have he : e.toLinearMap = (f.mapKer rfl).liftBaseChange F.Ring := by
      apply AlgebraTensorModule.ext
      intro q p
      apply Subtype.ext
      rw [LinearMap.liftBaseChange_tmul]
      exact hek q p
    exact he ▸ e.bijective
  have hFE : f.toRingHom.FormallyEtale :=
    RingHom.formallyEtale_algebraMap.mpr (show FormallyEtale P Q from inferInstance)
  exact compareFirstCotangentHomology E F f rfl hFE hk

open Polynomial in
/-- A standard étale algebra over a quotient comes from an étale algebra over
the presentation ring. Inverting the lifted derivative ensures étaleness
even before imposing the quotient. -/
private theorem standardEtale_lift
    {P : Type u} {B : Type v} {T : Type w} [CommRing P] [CommRing B] [CommRing T]
    [Algebra P B] [Algebra B T] [IsStandardEtale B T]
    (hp : Function.Surjective (algebraMap P B)) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra P Q),
      Etale P Q ∧ Nonempty (B ⊗[P] Q ≃ₐ[B] T) := by
  classical
  let E := (IsStandardEtale.nonempty_standardEtalePresentation (R := B) (S := T)).some
  have liftable (a : B[X]) : a ∈ Polynomial.lifts (algebraMap P B) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun _ => hp _
  obtain ⟨f, hf, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic (liftable E.f) E.monic_f
  obtain ⟨g, hg, -⟩ := Polynomial.exists_support_eq_of_mem_lifts (liftable E.g)
  let Q : StandardEtalePair P :=
    ⟨f, hm, g * f.derivative, ⟨g, 0, 1, by simp [mul_comm]⟩⟩
  let Q' := Q.map (algebraMap P B)
  have hf' : Q'.f = E.f := hf
  have hg' : Q'.g = E.g * E.f.derivative := by
    change (g * f.derivative).map (algebraMap P B) = _
    rw [Polynomial.map_mul, ← Polynomial.derivative_map, hg, hf]
  have hmap {S : Type v} [CommRing S] [Algebra B S] (x : S) :
      Q'.HasMap x ↔ E.HasMap x := by
    constructor
    · intro h
      change Polynomial.aeval x Q'.f = 0 ∧ IsUnit (Polynomial.aeval x Q'.g) at h
      rw [hf', hg', map_mul] at h
      exact ⟨h.1, isUnit_of_mul_isUnit_left h.2⟩
    · intro h
      change Polynomial.aeval x Q'.f = 0 ∧ IsUnit (Polynomial.aeval x Q'.g)
      rw [hf', hg', map_mul]
      exact ⟨h.1, h.2.mul h.isUnit_derivative_f⟩
  let i : Q'.Ring →ₐ[B] E.Ring := Q'.lift E.X ((hmap _).mpr E.hasMap_X)
  let j : E.Ring →ₐ[B] Q'.Ring := E.lift Q'.X ((hmap _).mp Q'.hasMap_X)
  have hi : i Q'.X = E.X := StandardEtalePair.lift_X _ _ _
  have hj : j E.X = Q'.X := StandardEtalePair.lift_X _ _ _
  let e : Q'.Ring ≃ₐ[B] E.Ring := AlgEquiv.ofAlgHom i j
    (StandardEtalePair.hom_ext (P := E.P) (by
      change i (j E.X) = E.X
      rw [hj, hi]))
    (StandardEtalePair.hom_ext (P := Q') (by
      change j (i Q'.X) = Q'.X
      rw [hi, hj]))
  let U : StandardEtalePresentation P Q.Ring :=
    ⟨Q, Q.X, Q.hasMap_X, by simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩
  exact ⟨Q.Ring, inferInstance, inferInstance, inferInstance,
    ⟨(U.baseChange (T := B)).equivRing.trans (e.trans E.equivRing.symm)⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness at a prime descends through a standard étale neighborhood. -/
private theorem smoothAt_of_standardEtale
    {R B T : Type*} [CommRing R] [CommRing B] [CommRing T]
    [Algebra R B] [Algebra R T] [Algebra B T] [IsScalarTower R B T]
    [Algebra.FinitePresentation R B] [IsStandardEtale B T]
    (q : Ideal T) [q.IsPrime] (hs : Algebra.IsSmoothAt R q) :
    Algebra.IsSmoothAt R (q.comap (algebraMap B T)) := by
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := B)).mp
    (inferInstance : Algebra.FiniteType R B)
  let P := MvPolynomial (Fin n) R
  let : Algebra P B := π.toAlgebra
  let : IsScalarTower R P B := .of_algebraMap_eq' π.comp_algebraMap.symm
  obtain ⟨Q, _, _, hQ, ⟨e⟩⟩ := standardEtale_lift (P := P) (B := B) (T := T) hπ
  let : Algebra R Q := ((algebraMap P Q).comp (algebraMap R P)).toAlgebra
  let : IsScalarTower R P Q := .of_algebraMap_eq' rfl
  let D := Q ⊗[P] B
  let : IsScalarTower R B D := .of_algebraMap_eq fun r => by
    change algebraMap R Q r ⊗ₜ[P] (1 : B) = 1 ⊗ₜ[P] algebraMap R B r
    simp only [IsScalarTower.algebraMap_apply R P Q, IsScalarTower.algebraMap_apply R P B]
    rw [Algebra.algebraMap_eq_smul_one (R := P) (A := Q), smul_tmul, Algebra.smul_def, mul_one]
  let e' : D ≃ₐ[B] T :=
    ({ __ := Algebra.TensorProduct.comm P Q B, commutes' := fun _ => rfl } :
      D ≃ₐ[B] B ⊗[P] Q).trans e
  let q' : Ideal D := q.comap e'.toRingHom
  let p : Ideal B := q.comap (algebraMap B T)
  let : q'.IsPrime := inferInstanceAs (q.comap e'.toRingHom).IsPrime
  let : p.IsPrime := inferInstanceAs (q.comap (algebraMap B T)).IsPrime
  have hpq : p = q'.comap (algebraMap B D) := by
    ext b
    change algebraMap B T b ∈ q ↔ e' (algebraMap B D b) ∈ q
    rw [AlgEquiv.commutes]
  let : q'.LiesOver p := ⟨hpq⟩
  let L := Localization.AtPrime q'
  let A := Localization.AtPrime p
  let : Algebra A L := Localization.AtPrime.algebraOfLiesOver p q'
  have : IsLocalHom (algebraMap A L) :=
    Localization.isLocalHom_localRingHom p q' (algebraMap B D) hpq
  have : FormallySmooth R L :=
    FormallySmooth.of_equiv
      ((Localization.localAlgEquiv q' q e' rfl).restrictScalars R).symm
  have : Etale B D := Etale.of_equiv e'.symm
  have : Module.Flat B L := Module.Flat.trans B D L
  have : Module.Flat A L := (Module.flat_iff_of_isLocalization A p.primeCompl L).mpr ‹_›
  have : Module.FaithfullyFlat A L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : FormallyEtale B L := FormallyEtale.comp B D L
  have : FormallyEtale B A := FormallyEtale.of_isLocalization p.primeCompl
  obtain ⟨h₁⟩ := tensorH1OfEtalePresentation (R := R) (Q := Q) hπ
  let h₂ := tensorH1CotangentOfIsLocalization R (S := D) L q'.primeCompl
  let h₃ := tensorH1CotangentOfIsLocalization R (S := B) A p.primeCompl
  let hL : L ⊗[A] H1Cotangent R A ≃ₗ[L] H1Cotangent R L :=
    (h₃.baseChange (A := L)).symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange B A L L (H1Cotangent R B) ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange B D L L (H1Cotangent R B)).symm ≪≫ₗ
      h₁.baseChange (A := L) ≪≫ₗ h₂
  have : Subsingleton (L ⊗[A] H1Cotangent R A) := hL.subsingleton
  have hvanish := Module.FaithfullyFlat.lTensor_reflects_triviality A L (H1Cotangent R A)
  let kd : L ⊗[A] Ω[A⁄R] ≃ₗ[L] Ω[L⁄R] :=
    ((tensorKaehlerEquivOfFormallyEtale R B A).baseChange (A := L)).symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange B A L L Ω[B⁄R] ≪≫ₗ
      tensorKaehlerEquivOfFormallyEtale R B L
  have : Module.Flat L (L ⊗[A] Ω[A⁄R]) := Module.Flat.of_linearEquiv kd
  have : Module.Flat A Ω[A⁄R] := Module.Flat.of_flat_tensorProduct A Ω[A⁄R] L
  have : Algebra.EssFiniteType R A := Algebra.EssFiniteType.comp _ B _
  have : Module.Free A Ω[A⁄R] := Module.free_of_flat_of_isLocalRing
  exact (Algebra.formallySmooth_iff R A).mpr ⟨inferInstance, hvanish⟩

end EtaleDescent

section SmoothPoint

open Algebra

variable {R B C K : Type*} [CommRing R] [CommRing B] [CommRing C] [Field K]
variable [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
variable [Algebra B K] [Algebra C K] [IsScalarTower B C K]
variable [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R C]

local instance (A : Type*) [CommRing A] [Algebra A K] :
    (RingHom.ker (algebraMap A K)).IsPrime :=
  RingHom.ker_isPrime _

omit [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R C] in
theorem cotangentFiberMap_bijective_of_formallyEtale [FormallyEtale B C] :
    Function.Bijective (cotangentFiberMap R B C K) :=
  ((tensorKaehlerEquivOfFormallyEtale R B C).baseChange (A := K)).bijective.comp
    (AlgebraTensorModule.cancelBaseChange B C K K Ω[B⁄R]).symm.bijective

set_option backward.isDefEq.respectTransparency false in
private theorem smoothAt_of_tangent_bijective
    (hs : IsSmoothAt R (RingHom.ker (algebraMap C K)))
    (hf : Function.Bijective (cotangentFiberMap R B C K)) :
    IsSmoothAt R (RingHom.ker (algebraMap B K)) := by
  let q := RingHom.ker (algebraMap C K)
  let : q.IsPrime := RingHom.ker_isPrime _
  let L := Localization.AtPrime q
  let yL : L →+* K := IsLocalization.lift (M := q.primeCompl)
    (fun a => isUnit_iff_ne_zero.mpr a.2)
  let : Algebra L K := yL.toAlgebra
  have : IsScalarTower C L K := .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsScalarTower B L K := .to₁₃₄ _ C _ _
  have hker : IsLocalRing.maximalIdeal L ≤ RingHom.ker (algebraMap L K) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change algebraMap L K (algebraMap C L a) = 0
    rw [← IsScalarTower.algebraMap_apply C L K]
    exact ha
  have : FormallyEtale C L := FormallyEtale.of_isLocalization q.primeCompl
  have : FormallySmooth R L := hs
  have : EssFiniteType R L := .comp _ C _
  have hfl : Function.Bijective (cotangentFiberMap R B L K) := by
    rw [cotangentFiberMap_comp (B := C)]
    exact cotangentFiberMap_bijective_of_formallyEtale.comp hf
  have : IsEtaleAt B q := formallyEtale_of_fiber_bijective hker hfl
  have : Algebra.FinitePresentation B C := .of_restrict_scalars_finitePresentation R B C
  obtain ⟨s, hsq, he⟩ := IsEtaleAt.exists_isStandardEtale (R := B) q
  let T := Localization.Away s
  let yT : T →+* K := IsLocalization.Away.lift (g := algebraMap C K) s
    (isUnit_iff_ne_zero.mpr hsq)
  let qT := RingHom.ker yT
  let : qT.IsPrime := RingHom.ker_isPrime _
  have hqT : qT.comap (algebraMap C T) = q := by
    ext a
    change yT (algebraMap C T a) = 0 ↔ algebraMap C K a = 0
    rw [IsLocalization.Away.lift_eq]
  have hqB : qT.comap (algebraMap B T) = RingHom.ker (algebraMap B K) := by
    rw [IsScalarTower.algebraMap_eq B C T, ← Ideal.comap_comap, hqT]
    ext b
    change algebraMap C K (algebraMap B C b) = 0 ↔ algebraMap B K b = 0
    rw [← IsScalarTower.algebraMap_apply B C K]
  let LT := Localization.AtPrime qT
  have : IsLocalization.AtPrime LT q := by
    have hi := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers s) LT qT
    have heq : q.primeCompl = (qT.comap (algebraMap C T)).primeCompl := by
      ext a
      simp only [Ideal.mem_primeCompl_iff, hqT]
    change IsLocalization q.primeCompl LT
    rw [heq]
    exact hi
  have hsT : IsSmoothAt R qT :=
    FormallySmooth.of_equiv ((IsLocalization.algEquiv q.primeCompl L LT).restrictScalars R)
  let p' := qT.comap (algebraMap B T)
  let p := RingHom.ker (algebraMap B K)
  have heq : p'.primeCompl = p.primeCompl := by
    ext b
    simp only [Ideal.mem_primeCompl_iff, p', hqB, p]
  have : IsLocalization p.primeCompl (Localization.AtPrime p') :=
    heq ▸ (inferInstance : IsLocalization p'.primeCompl (Localization.AtPrime p'))
  have : FormallySmooth R (Localization.AtPrime p') := smoothAt_of_standardEtale qT hsT
  let e := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime p') (Localization.AtPrime p)
  exact FormallySmooth.of_equiv (e.restrictScalars R)

omit [Algebra R B] [Algebra B C] [IsScalarTower R B C] [Algebra B K] [IsScalarTower B C K]
  [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R C] in
/-- A standard smooth presentation of relative dimension `d` gives a
cotangent fiber of dimension `d` at every field-valued point. -/
theorem cotangentFiber_finrank_of_standardSmooth (d : ℕ)
    [IsStandardSmoothOfRelativeDimension d R C] :
    Module.finrank K (CotangentFiber R C K) = d := by
  have : Nontrivial C := (algebraMap C K).domain_nontrivial
  have : IsStandardSmooth R C := IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  rw [Module.finrank_baseChange, Module.finrank,
    IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d]
  simp

end SmoothPoint

theorem smooth_identity_criterion : SmoothIdentityCriterionType := by
  intro R B C K _ _ _ _ _ _ _ _ _ _ _ _ _ d hs hd hdual
  let p := RingHom.ker (algebraMap B K)
  let : p.IsPrime := RingHom.ker_isPrime _
  have hf := LinearMap.dualMap_bijective_iff.mp hdual
  have : Algebra.IsSmoothAt R p := smoothAt_of_tangent_bijective hs hf
  obtain ⟨b, hb, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p
  refine ⟨b, hb, ?_⟩
  let U := Localization.Away b
  let xU : U →+* K := IsLocalization.Away.lift (g := algebraMap B K) b
    (isUnit_iff_ne_zero.mpr hb)
  let : Algebra U K := xU.toAlgebra
  have : IsScalarTower B U K := .of_algebraMap_eq' (IsLocalization.Away.lift_comp _ _).symm
  have : Nontrivial U := xU.domain_nontrivial
  have : Algebra.FormallyEtale B U := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers b)
  let e := LinearEquiv.ofBijective (cotangentFiberMap R B U K)
    cotangentFiberMap_bijective_of_formallyEtale
  let eBC := LinearEquiv.ofBijective (cotangentFiberMap R B C K) hf
  have hfin : Module.finrank U Ω[U⁄R] = d :=
    (Module.finrank_baseChange (R := K)).symm.trans
      (e.finrank_eq.symm.trans (eBC.finrank_eq.trans hd))
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  exact (Module.finrank_eq_rank U Ω[U⁄R]).symm.trans (congrArg Nat.cast hfin)

/-- Dualizing the cotangent fiber identifies it with the relative derivations
whose coefficients have the module structure specified by the point. -/
noncomputable def tangentEquivDerivation (R A K : Type*)
    [CommRing R] [CommRing A] [Field K] [Algebra R A] [Algebra A K] [Algebra R K]
    [IsScalarTower R A K] :
    Module.Dual K (CotangentFiber R A K) ≃ Derivation R A K :=
  (LinearMap.liftBaseChangeEquiv (A := K) (R := A) (M := Ω[A⁄R]) (N := K)).symm.toEquiv.trans
    (KaehlerDifferential.linearMapEquivDerivation R A (M := K)).toEquiv

@[simp] theorem tangentEquivDerivation_apply
    {R A K : Type*} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
    (l : Module.Dual K (CotangentFiber R A K)) (a : A) :
    tangentEquivDerivation R A K l a = l (1 ⊗ₜ D R A a) := rfl

theorem smooth_identity_criterion_of_derivations : DerivationSmoothIdentityCriterionType := by
  intro R B C K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d hs hd hder
  apply smooth_identity_criterion R B C K d hs hd
  have hn : (tangentEquivDerivation R B K : _ → _) ∘ (cotangentFiberMap R B C K).dualMap =
      (fun D : Derivation R C K => D.compAlgebraMap B) ∘ tangentEquivDerivation R C K := by
    funext l
    ext b
    simp
  exact ((tangentEquivDerivation R B K).comp_bijective _).mp
    (hn.symm ▸ hder.comp (tangentEquivDerivation R C K).bijective)

end LinearAlgebraicGroups.Albert.SmoothIdentityCriterion
