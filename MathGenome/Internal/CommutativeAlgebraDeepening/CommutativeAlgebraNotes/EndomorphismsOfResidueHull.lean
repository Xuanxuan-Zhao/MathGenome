import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.EndomorphismsOfResidueHull
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompletionOfTorsionModules
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteLengthMatlisDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveHullTruncations

/-! Endomorphisms of the residue-field injective hull (M03). -/

noncomputable section

namespace CommutativeAlgebraNotes

open IsLocalRing
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
  (Completion IsPowerTorsion mk_representative scalar)
open CompletionOfTorsionModules (completionModule completionScalarTower completionModule_smul)

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "𝔪" => maximalIdeal R

private theorem annihilates_hullTruncation (E : ResidueFieldEnvelope R) (n : ℕ)
    (x : hullTruncation E n) (a : R) (ha : a ∈ 𝔪 ^ n) : a • x.val = 0 :=
  (Submodule.mem_torsionBySet_iff _ _).mp x.property ⟨a, ha⟩

/-- Restriction of an endomorphism of the hull to the submodule killed by `𝔪 ^ n`. -/
def restrictHullEnd (E : ResidueFieldEnvelope R) (n : ℕ) :
    Module.End R E.carrier →ₐ[R] Module.End R (hullTruncation E n) where
  toFun f := f.restrict fun x hx =>
    (Submodule.mem_torsionBySet_iff _ _).mpr fun a => by
      change (a : R) • f x = 0
      rw [← map_smul, annihilates_hullTruncation E n ⟨x, hx⟩ a a.property, map_zero]
  map_one' := LinearMap.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl
  map_zero' := LinearMap.ext fun _ => Subtype.ext rfl
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext rfl
  commutes' _ := LinearMap.ext fun _ => Subtype.ext rfl

@[simp]
theorem restrictHullEnd_apply (E : ResidueFieldEnvelope R) (n : ℕ)
    (f : Module.End R E.carrier) (x : hullTruncation E n) :
    (restrictHullEnd E n f x).val = f x.val := rfl

/-- Scalar multiplication by the maximal-ideal quotient on the corresponding truncation. -/
abbrev truncationScalar (E : ResidueFieldEnvelope R) (n : ℕ) :
    TruncationRing R n →ₐ[R] Module.End R (hullTruncation E n) :=
  Algebra.lsmul R R (hullTruncation E n)

private theorem truncationEval_mul (E : ResidueFieldEnvelope R) (n : ℕ)
    (a : TruncationRing R n) (g : MatlisDualModule E (TruncationRing R n)) :
    g a = (a • truncationEval E n g : hullTruncation E n).val := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [hullTruncation_mk_smul]
  change g (Ideal.Quotient.mk (𝔪 ^ n) r) = r • g 1
  simpa only [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq] using
    g.map_smul r (1 : TruncationRing R n)

variable [IsNoetherianRing R]

private theorem truncationRing_finiteLength (E : ResidueFieldEnvelope R) (n : ℕ) :
    IsFiniteLength R (TruncationRing R n) := by
  cases n with
  | zero =>
    let : Subsingleton (TruncationRing R 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact .of_subsingleton
  | succ n => exact (hullTruncation_finiteLength E _ (Nat.succ_pos n)).2.2.1

private theorem truncationScalar_bijective (E : ResidueFieldEnvelope R) (n : ℕ) :
    Function.Bijective (truncationScalar E n) := by
  let A := TruncationRing R n
  let D := MatlisDualModule E A
  let ev := truncationEval E n
  obtain ⟨e, he⟩ := matlisEvaluation_equiv E A (truncationRing_finiteLength E n)
  have he' (a : A) (g : D) : e a g = g a :=
    congrArg (fun f : A →ₗ[R] MatlisDualModule E D => f a g) he
  constructor
  · intro a b hab
    apply e.injective
    apply LinearMap.ext
    intro g
    rw [he', he', truncationEval_mul E, truncationEval_mul E]
    exact congrArg (fun f : Module.End R (hullTruncation E n) => (f (ev g)).val) hab
  · intro f
    let g : MatlisDualModule E D := (hullTruncation E n).subtype.comp (f.comp ev.toLinearMap)
    obtain ⟨a, ha⟩ := e.surjective g
    refine ⟨a, LinearMap.ext fun x => Subtype.ext ?_⟩
    obtain ⟨b, rfl⟩ := ev.surjective x
    change (a • ev b : hullTruncation E n).val = g b
    rw [← truncationEval_mul E n, ← he', ha]

/-- The endomorphism algebra at a finite stage consists of the scalars in `R ⧸ 𝔪 ^ n`. -/
def truncationScalarEquiv (E : ResidueFieldEnvelope R) (n : ℕ) :
    TruncationRing R n ≃ₐ[R] Module.End R (hullTruncation E n) :=
  AlgEquiv.ofBijective (truncationScalar E n) (truncationScalar_bijective E n)

@[simp]
theorem truncationScalarEquiv_apply (E : ResidueFieldEnvelope R) (n : ℕ)
    (a : TruncationRing R n) (x : hullTruncation E n) :
    truncationScalarEquiv E n a x = a • x := rfl

/-- The hull carries the completion action on a maximal-ideal power-torsion module. -/
theorem residueHull_powerTorsion (E : ResidueFieldEnvelope R) : IsPowerTorsion R E.carrier := by
  intro x
  obtain ⟨n, hn, hx⟩ := exists_mem_hullTruncation E x
  exact (mem_idealTorsion 𝔪 x).mpr ⟨n, hn, annihilates_hullTruncation E n ⟨x, hx⟩⟩

private def completionScalar (E : ResidueFieldEnvelope R) :
    Completion R →ₐ[R] Module.End R E.carrier := by
  letI := completionModule (residueHull_powerTorsion E)
  letI := completionScalarTower (residueHull_powerTorsion E)
  exact Algebra.lsmul R R E.carrier

private theorem completionScalar_restrict (E : ResidueFieldEnvelope R) (n : ℕ)
    (s : Completion R) :
    restrictHullEnd E n (completionScalar E s) =
      truncationScalarEquiv E n (AdicCompletion.evalₐ 𝔪 n s) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [restrictHullEnd_apply, truncationScalarEquiv_apply, ← mk_representative s n,
    hullTruncation_mk_smul]
  exact completionModule_smul (residueHull_powerTorsion E)
    (annihilates_hullTruncation E n x) (mk_representative s n)

private def endomorphismScalarAt (E : ResidueFieldEnvelope R) (n : ℕ) :
    Module.End R E.carrier →ₐ[R] TruncationRing R n :=
  (truncationScalarEquiv E n).symm.toAlgHom.comp (restrictHullEnd E n)

private theorem endomorphismScalarAt_apply (E : ResidueFieldEnvelope R) (n : ℕ)
    (f : Module.End R E.carrier) (x : hullTruncation E n) :
    (endomorphismScalarAt E n f • x : hullTruncation E n).val = f x.val := by
  have h : truncationScalarEquiv E n (endomorphismScalarAt E n f) = restrictHullEnd E n f :=
    (truncationScalarEquiv E n).apply_symm_apply _
  exact congrArg (fun g : Module.End R (hullTruncation E n) => (g x).val) h

private theorem endomorphismScalarAt_compatible (E : ResidueFieldEnvelope R) {m n : ℕ}
    (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow 𝔪 hmn).comp (endomorphismScalarAt E n).toRingHom =
      (endomorphismScalarAt E m).toRingHom := by
  apply RingHom.ext
  intro f
  change Ideal.Quotient.factorPow 𝔪 hmn (endomorphismScalarAt E n f) =
    endomorphismScalarAt E m f
  apply (truncationScalarEquiv E m).injective
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  let y : hullTruncation E n :=
    Submodule.inclusion (Submodule.torsionBySet_le_torsionBySet_pow m n hmn 𝔪) x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (endomorphismScalarAt E n f)
  have hy := endomorphismScalarAt_apply E n f y
  rw [← hr, hullTruncation_mk_smul] at hy
  rw [truncationScalarEquiv_apply, truncationScalarEquiv_apply, ← hr]
  change (Ideal.Quotient.mk (𝔪 ^ m) r • x : hullTruncation E m).val =
    (endomorphismScalarAt E m f • x : hullTruncation E m).val
  rw [hullTruncation_mk_smul, endomorphismScalarAt_apply]
  exact hy

private theorem completionScalar_bijective (E : ResidueFieldEnvelope R) :
    Function.Bijective (completionScalar E) := by
  constructor
  · intro s t h
    apply AdicCompletion.ext_evalₐ
    intro n
    apply (truncationScalarEquiv E n).injective
    rw [← completionScalar_restrict, ← completionScalar_restrict, h]
  · intro f
    let s := AdicCompletion.liftRingHom 𝔪 (fun n => (endomorphismScalarAt E n).toRingHom)
      (fun h => endomorphismScalarAt_compatible E h) f
    refine ⟨s, LinearMap.ext fun x => ?_⟩
    obtain ⟨n, _, hx⟩ := exists_mem_hullTruncation E x
    have h := congrArg (fun g : Module.End R (hullTruncation E n) => (g ⟨x, hx⟩).val)
      (completionScalar_restrict E n s)
    change completionScalar E s x =
      (truncationScalarEquiv E n (AdicCompletion.evalₐ 𝔪 n s) ⟨x, hx⟩).val at h
    rw [show AdicCompletion.evalₐ 𝔪 n s = endomorphismScalarAt E n f from
      AdicCompletion.evalₐ_liftRingHom _ _ _ _ _, truncationScalarEquiv_apply,
      endomorphismScalarAt_apply] at h
    exact h

/-- Scalar multiplication identifies the completed ring with the endomorphisms of the hull. -/
def residueHullEndomorphismEquiv (E : ResidueFieldEnvelope R) :
    Completion R ≃ₐ[R] Module.End R E.carrier :=
  AlgEquiv.ofBijective (completionScalar E) (completionScalar_bijective E)

theorem residueHullEndomorphismEquiv_apply (E : ResidueFieldEnvelope R)
    (s : Completion R) (x : E.carrier) :
    residueHullEndomorphismEquiv E s x = scalar (residueHull_powerTorsion E) s x := rfl

/-- Restricting an endomorphism given by a completed scalar reduces that scalar modulo `𝔪 ^ n`. -/
theorem residueHullEndomorphismEquiv_restrict (E : ResidueFieldEnvelope R) (n : ℕ) :
    (restrictHullEnd E n).comp (residueHullEndomorphismEquiv E).toAlgHom =
      (truncationScalarEquiv E n).toAlgHom.comp (AdicCompletion.evalₐ 𝔪 n) :=
  AlgHom.ext (completionScalar_restrict E n)

/-- The scalar isomorphisms for the hull and its truncations, with their compatibility. -/
theorem residueHullEndomorphisms (E : ResidueFieldEnvelope R) :
    ∃ (h : IsPowerTorsion R E.carrier)
      (e : Completion R ≃ₐ[R] Module.End R E.carrier)
      (eₙ : ∀ n : ℕ, 1 ≤ n → TruncationRing R n ≃ₐ[R] Module.End R (hullTruncation E n)),
      (∀ s x, e s x = scalar h s x) ∧
      (∀ n hn a x, eₙ n hn a x = a • x) ∧
      (∀ n hn s (x : hullTruncation E n),
        e s x.val = (eₙ n hn (AdicCompletion.evalₐ 𝔪 n s) x).val) := by
  refine ⟨residueHull_powerTorsion E, residueHullEndomorphismEquiv E,
    fun n _ => truncationScalarEquiv E n, residueHullEndomorphismEquiv_apply E,
    fun n _ => truncationScalarEquiv_apply E n, ?_⟩
  intro n _ s x
  exact congrArg (fun g : Completion R →ₐ[R] Module.End R (hullTruncation E n) =>
    (g s x).val) (residueHullEndomorphismEquiv_restrict E n)

end CommutativeAlgebraNotes
