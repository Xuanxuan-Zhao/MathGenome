import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.BasicGRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularBaseGenericFormalFibers
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.IntegerGenericFormalFibers
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.TensorProduct.Pi
import Batteries.Tactic.OpenPrivate

/-! Geometric regularity of formal fibres for the basic G-rings. -/

universe u v

open scoped TensorProduct
open Algebra IsLocalRing

namespace CommutativeAlgebraNotes.Excellence

set_option linter.style.haveILetI false

open _root_.CommutativeAlgebraNotes.Excellence.Specs (GenericFormalFiber)
open _root_.Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion
open _root_.Specs.CommutativeAlgebraNotes.FrobeniusCoefficientDefinitions
open _root_.CommutativeAlgebraNotes.FiniteAlgebraCompletion
open Algebra.TensorProduct (cancelBaseChange)

open private regularRing_localization from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularBaseGenericFormalFibers
open private completionTensorEquiv from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FormalFiberQuotient

private theorem regularity_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : IsNoetherianRing A ∧ RegularRing A) :
    IsNoetherianRing B ∧ RegularRing B := by
  letI := h.1
  letI := isNoetherianRing_of_ringEquiv A e
  letI := (regularRing_iff A).mp h.2
  exact ⟨inferInstance, (regularRing_iff B).mpr (IsRegularRing.of_ringEquiv e)⟩

private theorem geometricallyRegular_of_scalarEquiv {K F T U : Type*}
    [Field K] [Field F] [CommRing T] [CommRing U] [Algebra K T] [Algebra F U]
    (e : K ≃+* F) (f : T ≃+* U)
    (hf : ∀ k, f (algebraMap K T k) = algebraMap F U (e k))
    (h : GeometricallyRegular K T) : GeometricallyRegular F U := by
  intro L _ _ _
  letI : Algebra K F := e.toRingHom.toAlgebra
  letI : Algebra K L := ((algebraMap F L).comp e.toRingHom).toAlgebra
  letI : Algebra K U := ((algebraMap F U).comp e.toRingHom).toAlgebra
  haveI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K F U := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite K F := (RingHom.Finite.of_surjective e.toRingHom e.surjective)
  haveI : Module.Finite K L := Module.Finite.trans F L
  have hL (x : K) : algebraMap K L x = algebraMap F L (e x) :=
    IsScalarTower.algebraMap_apply K F L x
  have hU (x : K) : algebraMap K U x = algebraMap F U (e x) :=
    IsScalarTower.algebraMap_apply K F U x
  let fK : T ≃ₐ[K] U := { __ := f, commutes' := hf }
  haveI : _root_.TensorProduct.CompatibleSMul K F L U := ⟨fun y l z => by
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [Algebra.smul_def, hL, hU] using
      (_root_.TensorProduct.smul_tmul x l z : (x • l) ⊗ₜ[K] z = l ⊗ₜ[K] (x • z))⟩
  haveI : _root_.TensorProduct.CompatibleSMul F K L U := ⟨fun x l z => by
    simpa only [Algebra.smul_def, hL, hU] using
      (_root_.TensorProduct.smul_tmul (e x) l z : (e x • l) ⊗ₜ[F] z = l ⊗ₜ[F] (e x • z))⟩
  exact regularity_of_ringEquiv
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) fK).toRingEquiv.trans
      (Algebra.TensorProduct.equivOfCompatibleSMul K F L L U).symm.toRingEquiv)
    (h.regular_tensorProduct L)

private theorem regularity_of_pi {ι : Type*} (A : ι → Type*) [∀ i, CommRing (A i)]
    (h : IsNoetherianRing (∀ i, A i) ∧ RegularRing (∀ i, A i)) (i : ι) :
    IsNoetherianRing (A i) ∧ RegularRing (A i) := by
  classical
  letI : Algebra (∀ j, A j) (A i) := (Pi.evalRingHom A i).toAlgebra
  let e : ∀ j, A j := Pi.single i 1
  haveI : IsLocalization.Away e (A i) := by
    apply IsLocalization.away_of_isIdempotentElem_of_mul
    · change e * e = e
      funext j
      by_cases hij : j = i
      · subst j; simp [e]
      · simp [e, Pi.single_eq_of_ne hij]
    · intro x y
      change x i = y i ↔ e * x = e * y
      constructor
      · intro hxy
        funext j
        by_cases hij : j = i
        · subst j; simpa [e] using hxy
        · simp [e, Pi.single_eq_of_ne hij]
      · intro hxy
        simpa [e] using congrFun hxy i
    · change Function.Surjective (fun f : ∀ j, A j => f i)
      exact fun x => ⟨Pi.single i x, Pi.single_eq_same i x⟩
  exact ⟨IsLocalization.isNoetherianRing (Submonoid.powers e) _ h.1,
    regularRing_localization (Submonoid.powers e) h.2⟩

open nonZeroDivisors in
private theorem fractionRing_finite (S B : Type*) [CommRing S] [CommRing B]
    [IsDomain S] [IsDomain B] [Algebra S B] [Module.Finite S B]
    [Algebra (FractionRing S) (FractionRing B)] [IsScalarTower S (FractionRing S) (FractionRing B)]
    (hinj : Function.Injective (algebraMap S B)) :
    Module.Finite (FractionRing S) (FractionRing B) := by
  let M := Algebra.algebraMapSubmonoid B S⁰
  haveI : IsLocalization M (FractionRing B) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨_, s, hs, rfl⟩
      apply isUnit_iff_ne_zero.mpr
      exact (map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).mpr
        ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.coe_ne_zero ⟨s, hs⟩))
    · intro x
      obtain ⟨⟨a, b, hb⟩, h⟩ := IsLocalization.surj B⁰ x
      haveI : Algebra.IsAlgebraic S B := Algebra.IsIntegral.isAlgebraic
      obtain ⟨c, s, hs, hc⟩ :=
        Algebra.IsAlgebraic.exists_smul_eq_mul S a (nonZeroDivisors.coe_ne_zero ⟨b, hb⟩)
      refine ⟨⟨c, algebraMap S B s, ⟨s, mem_nonZeroDivisors_of_ne_zero hs, rfl⟩⟩, ?_⟩
      apply (mul_left_inj' ((IsFractionRing.to_map_eq_zero_iff (K := FractionRing B)).not.mpr
          (nonZeroDivisors.coe_ne_zero ⟨b, hb⟩))).mp
      change (x * algebraMap B (FractionRing B) (algebraMap S B s)) * algebraMap B (FractionRing B) b =
        algebraMap B (FractionRing B) c * algebraMap B (FractionRing B) b
      change x * algebraMap B (FractionRing B) b = algebraMap B (FractionRing B) a at h
      rw [mul_right_comm, h, ← map_mul, ← map_mul, mul_comm a, mul_comm c, ← hc, Algebra.smul_def]
    · intro x y h
      exact ⟨1, by simpa using IsFractionRing.injective B (FractionRing B) h⟩
  exact Module.Finite.of_isLocalization S B (Rₚ := FractionRing S) (Sₚ := FractionRing B) S⁰

/-- After extending scalars to a finite extension of the fraction field of B,
the fibre at q is a coordinate in the base-changed finite completion product. -/
private theorem genericFormalFiber_of_finite (S B : Type*) [CommRing S] [CommRing B]
    [IsDomain S] [IsDomain B] [IsNoetherianRing S] [IsNoetherianRing B] [Algebra S B]
    [Module.Finite S B] (hinj : Function.Injective (algebraMap S B))
    (hS : ∀ (p : Ideal S) [p.IsPrime],
      GeometricallyRegular (FractionRing S) (GenericFormalFiber S (FractionRing S) p))
    (q : Ideal B) [q.IsPrime] :
    GeometricallyRegular (FractionRing B) (GenericFormalFiber B (FractionRing B) q) := by
  classical
  let K := FractionRing S
  let F := FractionRing B
  haveI : FaithfulSMul S F := (faithfulSMul_iff_algebraMap_injective S F).mpr
    ((IsFractionRing.injective B F).comp hinj)
  letI : Algebra K F := FractionRing.liftAlgebra S F
  haveI : IsScalarTower S K F := FractionRing.isScalarTower_liftAlgebra S F
  haveI : Module.Finite K F := fractionRing_finite S B hinj
  let p := q.comap (algebraMap S B)
  let q' : PrimesOver p B := ⟨⟨q, inferInstance⟩, rfl⟩
  let C := LocalCompletion (Localization.AtPrime p)
  let P := (j : PrimesOver p B) → Factor p j
  haveI : Finite (PrimesOver p B) := finitePrimes S B p
  letI := Fintype.ofFinite (PrimesOver p B)
  let e : B ⊗[S] C ≃ₐ[B] P := by
    let e₀ : B ⊗[S] C ≃+* P :=
      (Algebra.TensorProduct.comm S B C).toRingEquiv.trans (decomposition p).toRingEquiv
    refine { __ := e₀, commutes' := ?_ }
    intro b
    funext j
    exact decomposition_one_tmul p b j
  intro L _ _ _
  letI : Algebra B L := ((algebraMap F L).comp (algebraMap B F)).toAlgebra
  letI : Algebra S L := ((algebraMap F L).comp (algebraMap S F)).toAlgebra
  letI : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  haveI : IsScalarTower B F L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S F L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S B L := IsScalarTower.of_algebraMap_eq' (by
    change (algebraMap F L).comp (algebraMap S F) =
      ((algebraMap F L).comp (algebraMap B F)).comp (algebraMap S B)
    rw [IsScalarTower.algebraMap_eq S B F, RingHom.comp_assoc])
  haveI : IsScalarTower S K L := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq S F L, IsScalarTower.algebraMap_eq S K F, IsScalarTower.algebraMap_eq K F L, RingHom.comp_assoc])
  haveI : Module.Finite K L := Module.Finite.trans F L
  have hl := (hS p).regular_tensorProduct L
  let eB : L ⊗[S] C ≃ₐ[L] L ⊗[B] P :=
    (cancelBaseChange S B L L C).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e)
  have hP := regularity_of_ringEquiv
    (((cancelBaseChange S K L L C).trans eB).trans
      (Algebra.TensorProduct.piRight B L L (Factor p))).toRingEquiv hl
  exact regularity_of_ringEquiv (cancelBaseChange B F L L (Factor p q')).symm.toRingEquiv
    (regularity_of_pi _ hP q')

private noncomputable def localCompletionEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) : LocalCompletion A ≃+* LocalCompletion B := by
  let f := completionMap (maximalIdeal A) (maximalIdeal B) e.toRingHom
    (map_ringEquiv_maximalIdeal e).le
  let g := completionMap (maximalIdeal B) (maximalIdeal A) e.symm.toRingHom
    (map_ringEquiv_maximalIdeal e.symm).le
  refine { __ := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro x
    change g (f x) = x
    apply AdicCompletion.ext_evalₐ
    intro n
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal A) n x)
    simp only [f, g, eval_completionMap, ← ha, quotientPowMap_mk, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  · intro x
    change f (g x) = x
    apply AdicCompletion.ext_evalₐ
    intro n
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal B) n x)
    simp only [f, g, eval_completionMap, ← ha, quotientPowMap_mk, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

private theorem localCompletionEquiv_algebraMap {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (a : A) :
    localCompletionEquiv e (algebraMap A (LocalCompletion A) a) =
      algebraMap B (LocalCompletion B) (e a) :=
  completionMap_of _ _ e.toRingHom _ a

private noncomputable def completionIdealEquiv (Q : Type*) [CommRing Q]
    (I J : Ideal Q) (h : I = J) : AdicCompletion I Q ≃ₐ[Q] AdicCompletion J Q := by
  subst J
  exact AlgEquiv.refl

/-- Quotient by the contraction of the fibre prime, then compare the completions
of the two presentations of the resulting local domain. -/
private theorem formalFiber_of_quotient_generic {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (q : Ideal (Localization.AtPrime p)) [q.IsPrime]
    (h : let D := R ⧸ q.comap (algebraMap R (Localization.AtPrime p))
         ∀ (P : Ideal D) [P.IsPrime],
           GeometricallyRegular (FractionRing D) (GenericFormalFiber D (FractionRing D) P)) :
    GeometricallyRegular q.ResidueField (FormalFiber (Localization.AtPrime p) q) := by
  let A := Localization.AtPrime p
  let r := q.comap (algebraMap R A)
  let D := R ⧸ r
  let Q := A ⧸ q
  letI : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let P : Ideal D := p.map (Ideal.Quotient.mk r)
  have hr : r ≤ p := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal A p]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal (inferInstance : q.IsPrime).ne_top)
  haveI : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hr)
  have hP : P.comap (Ideal.Quotient.mk r) = p := Ideal.comap_map_mk hr
  have hq : r.map (algebraMap R A) = q := IsLocalization.map_under p.primeCompl A q
  letI : Algebra D Q := (Ideal.quotientMap q (algebraMap R A) le_rfl).toAlgebra
  let eQ : Q ≃ₐ[D] A ⧸ r.map (algebraMap R A) := by
    refine { __ := (Ideal.quotientEquivAlgOfEq R hq.symm).toRingEquiv, commutes' := ?_ }
    intro d
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
    exact Ideal.quotientEquivAlgOfEq_mk R hq.symm (algebraMap R A x)
  let e₀ : Q ≃ₐ[D] D ⊗[R] A := eQ.trans (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A r)
  haveI : IsLocalization P.primeCompl Q := by
    have he : Algebra.algebraMapSubmonoid D p.primeCompl = P.primeCompl := by
      have hc : (P.comap (Ideal.Quotient.mk r)).primeCompl = p.primeCompl := by
        ext x
        change (x ∉ P.comap (Ideal.Quotient.mk r)) ↔ x ∉ p
        rw [hP]
      change p.primeCompl.map (Ideal.Quotient.mk r) = P.primeCompl
      simpa only [hc] using
        P.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk r) Ideal.Quotient.mk_surjective
    rw [← he]
    exact IsLocalization.isLocalization_of_algEquiv _
      e₀.symm
  let B := Localization.AtPrime P
  let e : B ≃ₐ[D] Q := IsLocalization.algEquiv P.primeCompl B Q
  let C := LocalCompletion B
  let T := AdicCompletion (Specs.quotientMaximalIdeal q) Q
  have hm : maximalIdeal Q = Specs.quotientMaximalIdeal q :=
    (map_maximalIdeal_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective).symm
  let eC₀ : C ≃ₐ[D] LocalCompletion Q :=
    { __ := localCompletionEquiv e.toRingEquiv
      commutes' := fun d => by
        change localCompletionEquiv e.toRingEquiv (algebraMap D C d) =
          algebraMap D (LocalCompletion Q) d
        rw [IsScalarTower.algebraMap_apply D B C, IsScalarTower.algebraMap_apply D Q (LocalCompletion Q),
          localCompletionEquiv_algebraMap]
        exact congrArg (algebraMap Q (LocalCompletion Q)) (e.commutes d) }
  let eC : C ≃ₐ[D] T := eC₀.trans ((completionIdealEquiv Q _ _ hm).restrictScalars D)
  let K := FractionRing D
  let F := FractionRing Q
  letI : Algebra Q K := ((algebraMap B K).comp e.symm.toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower D Q K := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap D K x = algebraMap B K (e.symm (algebraMap D Q x))
    rw [e.symm.commutes, IsScalarTower.algebraMap_apply D B K]
  haveI : IsFractionRing Q K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Q K
  let f := IsLocalization.algEquiv (nonZeroDivisors Q) K F
  -- Use the same canonical quotient instances throughout both tensor products.
  letI : CommRing Q := inferInstanceAs (CommRing (A ⧸ q))
  letI : CommRing T :=
    inferInstanceAs (CommRing (AdicCompletion (Specs.quotientMaximalIdeal q) (A ⧸ q)))
  letI : CommRing F := inferInstanceAs (CommRing (FractionRing (A ⧸ q)))
  letI : Algebra Q T := inferInstanceAs
    (Algebra (A ⧸ q) (AdicCompletion (Specs.quotientMaximalIdeal q) (A ⧸ q)))
  letI : Algebra Q F := inferInstanceAs (Algebra (A ⧸ q) (FractionRing (A ⧸ q)))
  let e₁ : K ⊗[D] C ≃ₐ[D] F ⊗[D] T :=
    Algebra.TensorProduct.congr (f.restrictScalars D) eC
  let e₂ : F ⊗[Q] T ≃ₐ[Q] F ⊗[D] T :=
    IsLocalization.algebraTensorEquiv P.primeCompl Q F T
  let eT : (K ⊗[D] C) ≃+* T ⊗[Q] F :=
    e₁.toRingEquiv.trans (e₂.symm.trans (Algebra.TensorProduct.comm Q F T)).toRingEquiv
  letI := Specs.formalFiberQuotientAlgebra q
  obtain ⟨_, e₃, _, _⟩ := formalFiberQuotient A q
  let eK : K ≃+* q.ResidueField :=
    f.toRingEquiv.trans (Specs.residueFieldToFractionRing q).symm.toRingEquiv
  refine geometricallyRegular_of_scalarEquiv eK (eT.trans e₃.symm.toRingEquiv) ?_ (h P)
  intro k
  apply e₃.injective
  change e₃ (e₃.symm (eT (k ⊗ₜ[D] (1 : C)))) =
    e₃ (algebraMap q.ResidueField (FormalFiber A q) (eK k))
  rw [e₃.apply_symm_apply, e₃.commutes]
  have hleft : eT (k ⊗ₜ[D] (1 : C)) = (1 : T) ⊗ₜ[Q] f k := by
    change (Algebra.TensorProduct.comm Q F T) (e₂.symm (e₁ (k ⊗ₜ[D] (1 : C)))) = _
    simp only [e₁, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [hleft]
  change (1 : T) ⊗ₜ[Q] f k =
    (1 : T) ⊗ₜ[Q] (Specs.residueFieldToFractionRing q) (eK k)
  simp [eK]

private theorem isGRing_of_quotient_generic (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (r : Ideal R) [r.IsPrime] (P : Ideal (R ⧸ r)) [P.IsPrime],
      GeometricallyRegular (FractionRing (R ⧸ r))
        (GenericFormalFiber (R ⧸ r) (FractionRing (R ⧸ r)) P)) : IsGRing R := by
  intro p hp
  let A := Localization.AtPrime p
  let C := LocalCompletion A
  letI := P103.Ch07.CompletedNoetherian.completed_noetherian A (maximalIdeal A)
  apply (regularMap_algebraMap_iff A C).mpr
  refine ⟨inferInstance, fun q hq => ?_⟩
  exact formalFiber_of_quotient_generic p q (fun P _ => h _ P)

private theorem quotient_isAdicComplete (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (r : Ideal R) [r.IsPrime] :
    IsAdicComplete ((maximalIdeal R).map (Ideal.Quotient.mk r)) (R ⧸ r) := by
  let D := R ⧸ r
  let e : D ≃ₐ[D] AdicCompletion ((maximalIdeal R).map (algebraMap R D)) D :=
    ((Algebra.TensorProduct.rid R D D).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[D] D)
        (AdicCompletion.ofAlgEquiv (maximalIdeal R)))).trans
      (completionTensorEquiv (maximalIdeal R) D)
  apply AdicCompletion.of_bijective_iff.mp
  have he : (e : D → _) = AdicCompletion.of ((maximalIdeal R).map (algebraMap R D)) D :=
    funext e.commutes
  change Function.Bijective (AdicCompletion.of ((maximalIdeal R).map (algebraMap R D)) D)
  rw [← he]
  exact e.bijective

private theorem coefficientTower_generic (k : Type*) [Field k] (r s : ℕ)
    (p : Ideal (CoefficientTowerBase k r s)) [p.IsPrime] :
    GeometricallyRegular (FractionRing (CoefficientTowerBase k r s))
      (GenericFormalFiber (CoefficientTowerBase k r s) (FractionRing (CoefficientTowerBase k r s)) p) := by
  let S := CoefficientTowerBase k r s
  by_cases h : ringChar k = 0
  · haveI : CharP k 0 := h ▸ ringChar.charP k
    haveI : CharZero k := CharP.charP_to_charZero k
    haveI : CharZero S := charZero_of_injective_ringHom (f := towerCoefficient k r s)
      ((MvPolynomial.C_injective (Fin s) (MvPowerSeries (Fin r) k)).comp
        MvPowerSeries.C_injective)
    haveI : CharZero (FractionRing S) := IsFractionRing.charZero_of_isFractionRing S
    haveI : IsRegularLocalRing (MvPowerSeries (Fin r) k) :=
      (CompleteRegularPowerSeries.overField k r).2.1
    exact regularBaseGenericFormalFiberCharZero S (FractionRing S)
      (regularRing_mvPolynomial _ _ (AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime _)) p
  · haveI : Fact (ringChar k).Prime := ⟨CharP.char_prime_of_ne_zero k h⟩
    exact regularBaseGenericFormalFiberCharP k (ringChar k) r s p

set_option maxHeartbeats 600000 in
private theorem fieldDomain_generic (k : Type*) (B : Type*) [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime] :
    GeometricallyRegular (FractionRing B) (GenericFormalFiber B (FractionRing B) q) := by
  obtain ⟨d, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  let S := CoefficientTowerBase k 0 d
  let e : S ≃+* MvPolynomial (Fin d) k :=
    MvPolynomial.mapEquiv (Fin d) (MvPowerSeries.isEmptyEquiv (Fin 0) k).toRingEquiv
  let g := f.toRingHom.comp e.toRingHom
  letI : Algebra S B := g.toAlgebra
  haveI : Module.Finite S B := (show g.Finite from (show f.toRingHom.Finite from hfin).comp
    (RingHom.Finite.of_surjective e.toRingHom e.surjective))
  haveI := Algebra.FiniteType.isNoetherianRing k B
  exact genericFormalFiber_of_finite S B (hf.comp e.injective) (coefficientTower_generic k 0 d) q

private theorem intDomain_generic (B : Type*) [CommRing B] [IsDomain B]
    [Algebra.FiniteType ℤ B] (q : Ideal B) [q.IsPrime] :
    GeometricallyRegular (FractionRing B) (GenericFormalFiber B (FractionRing B) q) := by
  by_cases h : Function.Injective (algebraMap ℤ B)
  · exact integerGenericFormalFiber B h q
  · let r := RingHom.ker (algebraMap ℤ B)
    haveI : r.IsPrime := Ideal.comap_isPrime _ _
    have hr : r ≠ ⊥ := fun he => h ((RingHom.injective_iff_ker_eq_bot _).mpr he)
    haveI : r.IsMaximal := IsPrime.to_maximal_ideal hr
    let k := ℤ ⧸ r
    letI : Field k := (Ideal.Quotient.maximal_ideal_iff_isField_quotient r).mp inferInstance |>.toField
    letI : Algebra k B := (RingHom.kerLift (algebraMap ℤ B)).toAlgebra
    haveI : IsScalarTower ℤ k B := IsScalarTower.of_algebraMap_eq' rfl
    haveI := Algebra.FiniteType.of_restrictScalars_finiteType ℤ k B
    exact fieldDomain_generic k B q

private theorem completeDomain_generic (B : Type u) [CommRing B] [IsDomain B] [IsLocalRing B]
    [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] (q : Ideal B) [q.IsPrime] :
    GeometricallyRegular (FractionRing B) (GenericFormalFiber B (FractionRing B) q) := by
  obtain ⟨d, _, h⟩ := CoefficientRings.finitePowerSeriesNormalization B
  rcases h with ⟨_, h⟩ | ⟨p, _, _, _, h⟩
  · obtain ⟨_, _, f, _, _, _, _, _, _, hfin⟩ := h
    obtain ⟨_, _, _, _, _, hf, _, hfin, _⟩ := hfin
    let k := ResidueField B
    let S := CoefficientTowerBase k d 0
    let e : S ≃+* MvPowerSeries (Fin d) k :=
      (MvPolynomial.isEmptyAlgEquiv _ _).toRingEquiv
    let g := f.comp e.toRingHom
    letI : Algebra S B := g.toAlgebra
    haveI : Module.Finite S B := (show g.Finite from
      (show f.Finite from hfin).comp (RingHom.Finite.of_surjective e.toRingHom e.surjective))
    exact genericFormalFiber_of_finite S B (hf.comp e.injective) (coefficientTower_generic k d 0) q
  · obtain ⟨_, _, _, _, Λ, _, _, _, _, _, _, _, _, _, f, _, _, _, _, _, _, _, hfin⟩ := h
    obtain ⟨_, _, hreg, _, _, hf, _, hfin, _⟩ := hfin
    let S := MvPowerSeries (Fin (d - 1)) Λ
    letI : Algebra S B := f.toAlgebra
    haveI : Module.Finite S B := hfin
    haveI : CharZero S := charZero_of_injective_ringHom
      (f := MvPowerSeries.C) MvPowerSeries.C_injective
    haveI : CharZero (FractionRing S) := IsFractionRing.charZero_of_isFractionRing S
    exact genericFormalFiber_of_finite S B hf
      (regularBaseGenericFormalFiberCharZero S (FractionRing S)
        (AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime S)) q

/-- Every Noetherian complete local ring is a G-ring. -/
theorem completeLocal_isGRing : Specs.completeLocal_isGRingType.{u} := by
  intro R _ _ _ _
  apply isGRing_of_quotient_generic R
  intro r _ P _
  letI : IsLocalRing (R ⧸ r) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk r) Ideal.Quotient.mk_surjective
  haveI : IsAdicComplete (maximalIdeal (R ⧸ r)) (R ⧸ r) := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk r) Ideal.Quotient.mk_surjective]
    exact quotient_isAdicComplete R r
  exact completeDomain_generic (R ⧸ r) P

/-- Every finite-type algebra over a field is a G-ring. -/
theorem finiteTypeField_isGRing : Specs.finiteTypeField_isGRingType.{u,v} := by
  intro k R _ _ _ _
  letI := Algebra.FiniteType.isNoetherianRing k R
  apply isGRing_of_quotient_generic R
  intro r _ P _
  exact fieldDomain_generic k (R ⧸ r) P

/-- Every finite-type algebra over the integers is a G-ring. -/
theorem finiteTypeInt_isGRing : Specs.finiteTypeInt_isGRingType.{u} := by
  intro R _ _
  letI := Algebra.FiniteType.isNoetherianRing ℤ R
  apply isGRing_of_quotient_generic R
  intro r _ P _
  have hfin := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ r) Ideal.Quotient.mk_surjective
  have hAlg : Ideal.Quotient.algebra (I := r) ℤ = Ring.toIntAlgebra (R := R ⧸ r) :=
    Subsingleton.elim _ _
  rw [hAlg] at hfin
  exact intDomain_generic (R ⧸ r) P

end CommutativeAlgebraNotes.Excellence
