import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.PolynomialExtension
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.PolynomialAlgebra

/-! Polynomial scalar extension, CM-15. -/
universe u
open scoped TensorProduct Pointwise
noncomputable section
set_option linter.style.haveILetI false
namespace AdvCommAlg.CohenMacaulay

/-- Hilbert's basis theorem for the actual polynomial ring in the statement. -/
theorem polynomial_noetherian : Specs.polynomial_noetherianType.{u} := by
  intro R _ _ n
  infer_instance

/-- Local principal ideal domains, including fields, are Cohen–Macaulay. -/
lemma localCohenMacaulay_of_localPID (A : Type u) [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] [IsLocalRing A] : LocalCohenMacaulay A A := by
  apply (localCohenMacaulay_iff_sourceDepth A A).mpr
  unfold dimension
  rw [Module.supportDim_self_eq_ringKrullDim]
  have hupper := Depth.depth_le_supportDim (R := A) A
  rw [Module.supportDim_self_eq_ringKrullDim] at hupper
  by_cases hf : IsField A
  · rw [ringKrullDim_eq_zero_of_isField hf] at hupper ⊢
    exact le_antisymm hupper (WithBot.coe_le_coe.mpr zero_le)
  · rw [IsPrincipalIdealRing.ringKrullDim_eq_one A hf] at hupper ⊢
    apply le_antisymm hupper
    let m := IsLocalRing.maximalIdeal A
    have hm : m ≠ ⊥ := fun h => hf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    let a := Submodule.IsPrincipal.generator m
    have ha : a ≠ 0 := fun h => hm ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero m).mpr h)
    have ham : a ∈ m := Submodule.IsPrincipal.generator_mem m
    have hmem : ∀ x ∈ [a], x ∈ m := by simpa using ham
    have hreg : RegularSequence.Regular A [a] := by
      apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
      apply (RingTheory.Sequence.isWeaklyRegular_singleton_iff A a).mpr
      intro x y h
      exact mul_left_cancel₀ ha h
    have hproper : m • (⊤ : Submodule A A) ≠ ⊤ :=
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A A))).symm
    change (1 : WithBot ℕ∞) ≤ (Depth.grade m A : WithBot ℕ∞)
    apply WithBot.coe_le_coe.mpr
    rw [Depth.grade_of_smul_ne_top m A hproper]
    exact le_sSup ⟨[a], hreg, hmem, by simp⟩

/-- The convention for a zero module remains valid after polynomial extension. -/
lemma mvPolynomial_cohenMacaulay_iff_of_subsingleton
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Subsingleton M] (n : ℕ) :
    let P := MvPolynomial (Fin n) R
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := P) M P
    letI := Specs.rightTensorFinite R P M P
    IsCohenMacaulay P (M ⊗[R] P) ↔ IsCohenMacaulay R M := by
  let P := MvPolynomial (Fin n) R
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := P) M P
  letI := Specs.rightTensorFinite R P M P
  exact iff_of_true (cohenMacaulay_of_subsingleton P (M ⊗[R] P))
    (cohenMacaulay_of_subsingleton R M)

/-- The prime obtained by setting every polynomial variable equal to zero. -/
def polynomialZeroPrime (R : Type u) [CommRing R] (n : ℕ)
    (p : PrimeSpectrum R) : PrimeSpectrum (MvPolynomial (Fin n) R) :=
  PrimeSpectrum.comap (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)) p

/-- Descent through the zero section reaches every base prime. -/
lemma polynomialZeroPrime_comap (R : Type u) [CommRing R] (n : ℕ)
    (p : PrimeSpectrum R) :
    PrimeSpectrum.comap (algebraMap R (MvPolynomial (Fin n) R))
      (polynomialZeroPrime R n p) = p := by
  ext x
  simp [polynomialZeroPrime, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap, MvPolynomial.algebraMap_eq]

/-- Every ideal of a localization is extended from an ideal of the base ring. -/
lemma principalIdealRing_of_isLocalization (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [IsPrincipalIdealRing A] (T : Submonoid A) [IsLocalization T B] :
    IsPrincipalIdealRing B := by
  constructor
  intro I
  rw [← IsLocalization.map_under T B I]
  exact (IsPrincipalIdealRing.principal (I.comap (algebraMap A B))).map_ringHom _

set_option backward.isDefEq.respectTransparency false in
/-- The actual one-variable local fiber is a domain and a principal ideal ring:
it is a localization of a polynomial ring over the residue field. -/
lemma polynomial_local_fiber_isPID (R : Type u) [CommRing R]
    (p : PrimeSpectrum R) (q : PrimeSpectrum (Polynomial R))
    (h : PrimeSpectrum.comap (algebraMap R (Polynomial R)) q = p) :
    let B := Localization.AtPrime q.asIdeal
    let J := p.asIdeal.map (algebraMap R B)
    IsDomain (B ⧸ J) ∧ IsPrincipalIdealRing (B ⧸ J) := by
  let E := PrimeSpectrum.preimageEquivFiber R (Polynomial R) p
  let q' := E ⟨q, h⟩
  let F := p.asIdeal.Fiber (Polynomial R)
  let e : Polynomial p.asIdeal.ResidueField ≃+* F :=
    (polyEquivTensor R p.asIdeal.ResidueField).toRingEquiv
  letI : IsDomain F := e.symm.toMulEquiv.isDomain
  letI : IsPrincipalIdealRing F := IsPrincipalIdealRing.of_surjective e e.surjective
  let L := Localization.AtPrime q'.asIdeal
  letI : IsPrincipalIdealRing L := principalIdealRing_of_isLocalization F L q'.asIdeal.primeCompl
  let P : PrimeSpectrum (Polynomial R) → Prop := fun r =>
    IsDomain (Localization.AtPrime r.asIdeal ⧸ p.asIdeal.map
      (algebraMap R (Localization.AtPrime r.asIdeal))) ∧
    IsPrincipalIdealRing (Localization.AtPrime r.asIdeal ⧸ p.asIdeal.map
      (algebraMap R (Localization.AtPrime r.asIdeal)))
  have hr : PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q' = q :=
    congrArg Subtype.val (E.symm_apply_apply ⟨q, h⟩)
  have hh : P (PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q') := by
    let e' := (Ideal.Fiber.algEquivAux₂ p.asIdeal q'.asIdeal).toRingEquiv
    let r := PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q'
    have hJ : (p.asIdeal.map (algebraMap R (Polynomial R))).map
        (algebraMap (Polynomial R) (Localization.AtPrime r.asIdeal)) =
        p.asIdeal.map (algebraMap R (Localization.AtPrime r.asIdeal)) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    let e'' := e'.trans (Ideal.quotEquivOfEq hJ)
    exact ⟨e''.symm.toMulEquiv.isDomain,
      IsPrincipalIdealRing.of_surjective e'' e''.surjective⟩
  exact Eq.mp (congrArg P hr) hh

/-- The map on stalks over a contracted prime is a local homomorphism. -/
lemma stalk_algebraMap_isLocalHom (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)] :
    IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
  rw [Localization.AtPrime.algebraMap_eq p q]
  infer_instance

/-- Flatness of an algebra induces flatness of the local map on stalks. -/
lemma stalk_flat (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)] :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
  apply (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
    (Localization.AtPrime q)).mpr
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- CM-10 uses the quotient by the *localized* base maximal ideal. Its
identification with the residue-field polynomial localization includes the
canonical scalar tower. -/
lemma polynomial_closedFiber_cohenMacaulay (R : Type u) [CommRing R]
    [IsNoetherianRing R] (p : PrimeSpectrum R) (q : PrimeSpectrum (Polynomial R))
    (h : PrimeSpectrum.comap (algebraMap R (Polynomial R)) q = p)
    [Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)]
    [IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)]
    [IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal))] :
    let A := Localization.AtPrime p.asIdeal
    let B := Localization.AtPrime q.asIdeal
    let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    letI := Specs.closedFiberLocalRing A B
    LocalCohenMacaulay (B ⧸ J) (B ⧸ J) := by
  let A := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime q.asIdeal
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  letI := Specs.closedFiberLocalRing A B
  have hp := polynomial_local_fiber_isPID R p q h
  letI : IsDomain (B ⧸ p.asIdeal.map (algebraMap R B)) := hp.1
  letI : IsPrincipalIdealRing (B ⧸ p.asIdeal.map (algebraMap R B)) := hp.2
  have hJ : p.asIdeal.map (algebraMap R B) = J := by
    dsimp only [J]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  let e := Ideal.quotEquivOfEq hJ
  letI : IsDomain (B ⧸ J) := e.symm.toMulEquiv.isDomain
  letI : IsPrincipalIdealRing (B ⧸ J) := IsPrincipalIdealRing.of_surjective e e.surjective
  exact localCohenMacaulay_of_localPID (B ⧸ J)

/-- Localization of scalar extension equals scalar extension of the localized
module, with the right-factor action on both tensor products. -/
def localizedTensorEquiv (R S M : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)] :
    let A := Localization.AtPrime p
    let B := Localization.AtPrime q
    let Q := LocalizedModule.AtPrime p M
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M S
    letI := RegularSequence.Specs.rightTensorModule (R := A) (S := B) Q B
    LocalizedModule.AtPrime q (M ⊗[R] S) ≃ₗ[B] (Q ⊗[A] B) := by
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q
  let Q := LocalizedModule.AtPrime p M
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M S
  letI := RegularSequence.Specs.rightTensorModule (R := A) (S := B) Q B
  let eLeft := LocalizedModule.equivTensorProduct q.primeCompl (M ⊗[R] S) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (RegularSequence.rightTensorComm (S := S) M S) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S B B M
  let eRight := RegularSequence.rightTensorComm (S := B) Q B ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (LocalizedModule.equivTensorProduct p.primeCompl M) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M
  exact eLeft ≪≫ₗ eRight.symm

/-- Applying CM-10 at an arbitrary polynomial prime, including vanishing stalks. -/
lemma polynomial_atPrime_cohenMacaulay_iff (R M : Type u) [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : PrimeSpectrum (Polynomial R)) :
    let p := PrimeSpectrum.comap (algebraMap R (Polynomial R)) q
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := Polynomial R) M (Polynomial R)
    letI := Specs.rightTensorFinite R (Polynomial R) M (Polynomial R)
    LocalCohenMacaulay (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal (M ⊗[R] Polynomial R)) ↔
    LocalCohenMacaulay (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) := by
  let p := PrimeSpectrum.comap (algebraMap R (Polynomial R)) q
  let A := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime q.asIdeal
  let Q := LocalizedModule.AtPrime p.asIdeal M
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : IsLocalHom (algebraMap A B) := stalk_algebraMap_isLocalHom R (Polynomial R) _ _
  letI : Module.Flat A B := stalk_flat R (Polynomial R) p.asIdeal q.asIdeal
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := Polynomial R) M (Polynomial R)
  letI := Specs.rightTensorFinite R (Polynomial R) M (Polynomial R)
  letI := RegularSequence.Specs.rightTensorModule (R := A) (S := B) Q B
  letI := Specs.rightTensorFinite A B Q B
  let e := localizedTensorEquiv R (Polynomial R) M p.asIdeal q.asIdeal
  rw [localCohenMacaulay_iff_of_linearEquiv e]
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · letI := hQ
    exact iff_of_true (localCohenMacaulay_of_subsingleton B (Q ⊗[A] B))
      (localCohenMacaulay_of_subsingleton A Q)
  · letI := hQ
    let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    letI := Specs.closedFiberLocalRing A B
    have hF := polynomial_closedFiber_cohenMacaulay R p q rfl
    have hF' : LocalCohenMacaulay (B ⧸ J) (B ⧸ (J • (⊤ : Submodule B B))) :=
      (localCohenMacaulay_iff_of_linearEquiv (quotientSelfEquiv B J)).mpr hF
    exact (tensor_cohenMacaulay_iff A B Q B).trans (and_iff_left hF')

/-- The global condition can equivalently include primes with zero stalks. -/
lemma isCohenMacaulay_iff_all_primes (R M : Type u) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsCohenMacaulay R M ↔ ∀ p : PrimeSpectrum R,
      LocalCohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
  constructor
  · intro h p
    rcases subsingleton_or_nontrivial (LocalizedModule.AtPrime p.asIdeal M) with hp | hp
    · exact Or.inl hp
    · exact h p hp
  · intro h p _
    exact h p

/-- The one-variable equivalence from the source, with its zero-module convention. -/
lemma polynomial_cohenMacaulay_iff (R M : Type u) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := Polynomial R) M (Polynomial R)
    letI := Specs.rightTensorFinite R (Polynomial R) M (Polynomial R)
    IsCohenMacaulay (Polynomial R) (M ⊗[R] Polynomial R) ↔ IsCohenMacaulay R M := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := Polynomial R) M (Polynomial R)
  letI := Specs.rightTensorFinite R (Polynomial R) M (Polynomial R)
  rw [isCohenMacaulay_iff_all_primes, isCohenMacaulay_iff_all_primes]
  constructor
  · intro h p
    let q := PrimeSpectrum.comap (Polynomial.constantCoeff : Polynomial R →+* R) p
    have hq : PrimeSpectrum.comap (algebraMap R (Polynomial R)) q = p := by
      ext x
      simp [q, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Polynomial.algebraMap_eq]
    have hlocal := (polynomial_atPrime_cohenMacaulay_iff R M q).mp (h q)
    exact Eq.mp (congrArg (fun p : PrimeSpectrum R => LocalCohenMacaulay
      (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M)) hq) hlocal
  · intro h q
    exact (polynomial_atPrime_cohenMacaulay_iff R M q).mpr (h _)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

set_option backward.isDefEq.respectTransparency false in
/-- Global CM is invariant under a simultaneous isomorphism of rings and modules. -/
lemma isCohenMacaulay_of_semilinearEquiv {R S M N : Type u}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module S N] [Module.Finite S N]
    (σ : R ≃+* S) (e : M ≃ₛₗ[RingHomClass.toRingHom σ] N)
    (hCM : IsCohenMacaulay R M) : IsCohenMacaulay S N := by
  letI : Algebra R S := σ.toRingHom.toAlgebra
  letI : Module R N := Module.compHom N σ.toRingHom
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eR : M ≃ₗ[R] N :=
    { e.toAddEquiv with map_smul' := fun a x => e.map_smulₛₗ a x }
  let T := IsUnit.submonoid R
  letI : IsLocalization T S := IsLocalization.of_le_isUnit_of_bijective
    Algebra.algebraMapSubmonoid_isUnit_le σ.bijective
  letI : IsLocalizedModule T (LinearMap.id : M →ₗ[R] M) :=
    isLocalizedModule_id T M R
  letI : IsLocalizedModule T eR.toLinearMap :=
    IsLocalizedModule.of_linearEquiv T (LinearMap.id : M →ₗ[R] M) eR
  intro q hq
  let p := PrimeSpectrum.comap σ.toRingHom q
  let f := (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N).restrictScalars R
  let g := f.comp eR.toLinearMap
  letI : IsLocalizedModule p.asIdeal.primeCompl g :=
    isLocalizedModule_atPrime_comp M T eR.toLinearMap q.asIdeal
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N)
  letI : IsLocalization p.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T
      (Localization.AtPrime q.asIdeal) q.asIdeal
  let eloc := localizedModule_semilinearEquiv M
    (A := Localization.AtPrime p.asIdeal) (B := Localization.AtPrime q.asIdeal)
    p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) g
  have hp : p ∈ Module.support R M := eloc.toEquiv.nontrivial_congr.mpr hq
  exact (localCohenMacaulay_iff_of_semilinearEquiv _ _ eloc).mp (hCM p hp)

/-- The two directions, including the zero module. -/
lemma isCohenMacaulay_iff_of_semilinearEquiv {R S M N : Type u}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module S N] [Module.Finite S N]
    (σ : R ≃+* S) (e : M ≃ₛₗ[RingHomClass.toRingHom σ] N) :
    IsCohenMacaulay R M ↔ IsCohenMacaulay S N :=
  ⟨isCohenMacaulay_of_semilinearEquiv σ e,
    isCohenMacaulay_of_semilinearEquiv σ.symm e.symm⟩

/-- The same-ring specialization of simultaneous transport. -/
lemma isCohenMacaulay_iff_of_linearEquiv {R M N : Type u}
    [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (e : M ≃ₗ[R] N) :
    IsCohenMacaulay R M ↔ IsCohenMacaulay R N :=
  isCohenMacaulay_iff_of_semilinearEquiv (RingEquiv.refl R) e

/-- Changing the coefficient algebra acts semilinearly on scalar extension. -/
def rightTensorSemilinearEquiv (R A B M : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M]
    (σ : A ≃ₐ[R] B) :
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := A) M A
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := B) M B
    (M ⊗[R] A) ≃ₛₗ[RingHomClass.toRingHom σ.toRingEquiv] (M ⊗[R] B) := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := A) M A
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := B) M B
  let e := TensorProduct.congr (LinearEquiv.refl R M) σ.toLinearEquiv
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a x
  change e (a • x) = σ a • e x
  induction x using TensorProduct.inductionOn with
  | tmul m b =>
    simp [RegularSequence.rightTensor_smul_tmul, e, smul_eq_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- The associativity comparison used when adjoining variables successively. -/
def rightTensorTowerEquiv (R A B M : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommGroup M] [Module R M] :
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := A) M A
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := B) M B
    letI := RegularSequence.Specs.rightTensorModule (R := A) (S := B) (M ⊗[R] A) B
    ((M ⊗[R] A) ⊗[A] B) ≃ₗ[B] (M ⊗[R] B) := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := A) M A
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := B) M B
  letI := RegularSequence.Specs.rightTensorModule (R := A) (S := B) (M ⊗[R] A) B
  exact RegularSequence.rightTensorComm (S := B) (M ⊗[R] A) B ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (RegularSequence.rightTensorComm (S := A) M A) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M ≪≫ₗ
    (RegularSequence.rightTensorComm (S := B) M B).symm

/-- CM-15 for finitely many polynomial variables. -/
theorem mvPolynomial_cohenMacaulay_iff : Specs.mvPolynomial_cohenMacaulay_iffType.{u} := by
  intro R _ _ M _ _ _ n
  induction n with
  | zero =>
    let P := MvPolynomial (Fin 0) R
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := P) M P
    letI := Specs.rightTensorFinite R P M P
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := R) M R
    letI := Specs.rightTensorFinite R R M R
    let σ := MvPolynomial.isEmptyAlgEquiv R (Fin 0)
    let e := rightTensorSemilinearEquiv R P R M σ
    let e' := RegularSequence.rightTensorComm (S := R) M R ≪≫ₗ TensorProduct.lid R M
    exact (isCohenMacaulay_iff_of_semilinearEquiv σ.toRingEquiv e).trans
      (isCohenMacaulay_iff_of_linearEquiv e')
  | succ n ih =>
    let A := MvPolynomial (Fin n) R
    let B := Polynomial A
    let P := MvPolynomial (Fin (n + 1)) R
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := A) M A
    letI := Specs.rightTensorFinite R A M A
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := B) M B
    letI := Specs.rightTensorFinite R B M B
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := P) M P
    letI := Specs.rightTensorFinite R P M P
    letI := RegularSequence.Specs.rightTensorModule (R := A) (S := B) (M ⊗[R] A) B
    letI := Specs.rightTensorFinite A B (M ⊗[R] A) B
    let σ := MvPolynomial.finSuccEquiv R n
    let e := rightTensorSemilinearEquiv R P B M σ
    let e' := rightTensorTowerEquiv R A B M
    exact (isCohenMacaulay_iff_of_semilinearEquiv σ.toRingEquiv e).trans
      ((isCohenMacaulay_iff_of_linearEquiv e').symm.trans
        ((polynomial_cohenMacaulay_iff A (M ⊗[R] A)).trans ih))

end AdvCommAlg.CohenMacaulay
