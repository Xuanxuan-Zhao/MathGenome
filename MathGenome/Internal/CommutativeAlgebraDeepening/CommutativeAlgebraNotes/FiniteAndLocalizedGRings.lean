import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FiniteAndLocalizedGRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteAlgebraCompletion
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.TensorProduct.Pi

open scoped TensorProduct
open Ideal IsLocalRing TensorProduct
open Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion
open CommutativeAlgebraNotes.FiniteAlgebraCompletion (decomposition decomposition_tmul_one
  decomposition_one_tmul)

universe u v

set_option linter.style.haveILetI false

namespace CommutativeAlgebraNotes.Excellence

private theorem noetherianRegular_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : IsNoetherianRing R ∧ RegularRing R) :
    IsNoetherianRing S ∧ RegularRing S := by
  letI := h.1
  letI : IsRegularRing R := (regularRing_iff R).mp h.2
  letI : IsRegularRing S := IsRegularRing.of_ringEquiv e
  exact ⟨inferInstance, (regularRing_iff S).mpr inferInstance⟩

theorem GeometricallyRegular.of_algEquiv {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (h : GeometricallyRegular k R) (e : R ≃ₐ[k] S) :
    GeometricallyRegular k S := by
  intro L _ _ _
  exact noetherianRegular_of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L) e).toRingEquiv
      (h.regular_tensorProduct L)

theorem GeometricallyRegular.baseChange_finite {k L T : Type*} [Field k] [Field L] [CommRing T]
    [Algebra k L] [Module.Finite k L] [Algebra k T] (h : GeometricallyRegular k T) :
    GeometricallyRegular L (L ⊗[k] T) := by
  intro M _ _ _
  letI : Algebra k M := ((algebraMap L M).comp (algebraMap k L)).toAlgebra
  letI : IsScalarTower k L M := .of_algebraMap_eq' rfl
  letI : Module.Finite k M := Module.Finite.trans L M
  exact noetherianRegular_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange k L M M T).symm.toRingEquiv
    (h.regular_tensorProduct M)

private noncomputable def localizationStalkEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (P : Ideal S) [P.IsPrime] :
    Localization.AtPrime (P.under R) ≃+* Localization.AtPrime P := by
  letI : IsLocalization.AtPrime (Localization.AtPrime P) (P.under R) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ P
  exact (IsLocalization.algEquiv (P.under R).primeCompl _ _).toRingEquiv

theorem RegularRing.of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (h : RegularRing R) :
    RegularRing S := by
  intro P _
  letI := h (P.under R)
  exact IsRegularLocalRing.of_ringEquiv (localizationStalkEquiv M P)

private theorem regularRing_piFactor {ι : Type*} {R : ι → Type*} [∀ j, CommRing (R j)]
    (h : RegularRing (∀ j, R j)) (i : ι) : RegularRing (R i) := by
  classical
  letI : Algebra (∀ j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  let e : ∀ j, R j := Pi.single i 1
  have hidem : IsIdempotentElem e := by
    show e * e = e
    funext j
    by_cases hj : j = i
    · subst j
      simp [e]
    · simp [e, Pi.single_eq_of_ne hj]
  letI : IsLocalization.Away e (R i) :=
    IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y ↦ by
      change x i = y i ↔ e * x = e * y
      constructor
      · intro hxy
        funext j
        by_cases hj : j = i
        · subst j
          simpa [e] using hxy
        · simp [e, Pi.single_eq_of_ne hj]
      · intro hxy
        simpa [e] using congrFun hxy i) (fun x ↦ ⟨Pi.single i x, Pi.single_eq_same i x⟩)
  exact h.of_isLocalization (Submonoid.powers e)

theorem GeometricallyRegular.piFactor {k ι : Type*} [Field k] [Finite ι]
    {R : ι → Type*} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
    (h : GeometricallyRegular k (∀ j, R j)) (i : ι) : GeometricallyRegular k (R i) := by
  classical
  letI := Fintype.ofFinite ι
  intro L _ _ _
  have H := noetherianRegular_of_ringEquiv
    (Algebra.TensorProduct.piRight k L L R).toRingEquiv (h.regular_tensorProduct L)
  letI := H.1
  let S (j : ι) := L ⊗[k] R j
  have hsurj : Function.Surjective (Pi.evalRingHom S i) := by
    intro x
    refine ⟨Pi.single (M := S) i x, ?_⟩
    change Pi.single (M := S) i x i = x
    exact Pi.single_eq_same (M := S) i x
  exact ⟨isNoetherianRing_of_surjective _ _ (Pi.evalRingHom S i) hsurj,
    regularRing_piFactor H.2 i⟩

private noncomputable def tensorLocalizationEquiv {R S L C : Type*} [CommRing R] [CommRing S]
    [CommRing L] [CommRing C] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra R C] [Algebra S C] [IsScalarTower R S C] :
    (L ⊗[S] C) ≃ₐ[L] L ⊗[R] C :=
  letI := IsLocalization.tensorProduct_compatibleSMul M S L C
  Algebra.TensorProduct.equivOfCompatibleSMul R S L L C

private theorem tensorLocalizationEquiv_tmul {R S L C : Type*} [CommRing R] [CommRing S]
    [CommRing L] [CommRing C] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra R C] [Algebra S C] [IsScalarTower R S C] (a : L) (x : C) :
    tensorLocalizationEquiv M (a ⊗ₜ[S] x) = a ⊗ₜ[R] x :=
  rfl

theorem finiteCompletionDecomposition : CanonicalDecomposition.{u,v} :=
  CommutativeAlgebraNotes.FiniteAlgebraCompletion.comparison_bijective

section FiniteFibers

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem finiteFormalFiberDecomposition : Specs.FiniteFormalFiberDecomposition.{u,v} := by
  classical
  intro A B _ _ _ _ _ _ p _ i Q _
  dsimp only
  let R := Localization.AtPrime p
  let C := Localization.AtPrime i.1.asIdeal
  let H := LocalCompletion R
  let q := Q.under R
  letI : Q.LiesOver q := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver q Q
  let k := q.ResidueField
  let L := Q.ResidueField
  letI : IsScalarTower A R L := .to₁₂₄ A R C L
  letI : Algebra.QuasiFinite A C := Algebra.QuasiFinite.of_isLocalization i.1.asIdeal.primeCompl
  letI : Algebra.QuasiFinite R C := Algebra.QuasiFinite.of_restrictScalars A R C
  refine ⟨(inferInstance : Module.Finite k L), ?_, ?_⟩
  · letI : Finite (PrimesOver p B) :=
      CommutativeAlgebraNotes.FiniteAlgebraCompletion.finitePrimes A B p
    letI := Fintype.ofFinite (PrimesOver p B)
    let d : (B ⊗[A] H) ≃ₐ[B] ((j : PrimesOver p B) → Factor p j) :=
      { toRingEquiv := (Algebra.TensorProduct.comm A B H).toRingEquiv.trans
          (decomposition p).toRingEquiv
        commutes' := fun b ↦ funext fun j ↦ decomposition_one_tmul p b j }
    let e₁ := Algebra.TensorProduct.cancelBaseChange R k L L H
    let e₂ : (L ⊗[R] H) ≃ₐ[L] L ⊗[A] H := tensorLocalizationEquiv p.primeCompl
    let e₃ := (Algebra.TensorProduct.cancelBaseChange A B L L H).symm
    let e₄ := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) d
    let e₅ := Algebra.TensorProduct.piRight B L L (Factor p (B := B))
    refine ⟨e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅))), ?_⟩
    intro a b x j
    change e₅ (e₄ (e₃ (e₂ (e₁ ((a : L) ⊗ₜ[k] ((b : k) ⊗ₜ[R] (x : H))))))) j =
      (algebraMap k L b * a) ⊗ₜ[B] fromBaseCompletion p j x
    have hd : d ((1 : B) ⊗ₜ[A] x) j = fromBaseCompletion p j x :=
      decomposition_tmul_one p x j
    simp only [e₁, Algebra.TensorProduct.cancelBaseChange_tmul,
      e₂, tensorLocalizationEquiv_tmul, e₃, Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      e₄, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.refl_toAlgHom, AlgHom.id_apply,
      e₅, Algebra.TensorProduct.piRight_tmul, Algebra.smul_def]
    change (algebraMap k L b * a) ⊗ₜ[B] d ((1 : B) ⊗ₜ[A] x) j = _
    rw [hd]
  · let e : (L ⊗[C] Factor p i) ≃ₐ[L] L ⊗[B] Factor p i :=
      tensorLocalizationEquiv i.1.asIdeal.primeCompl
    exact ⟨e.symm, fun a x ↦ e.symm_apply_eq.mpr (tensorLocalizationEquiv_tmul _ _ _).symm⟩

end FiniteFibers

theorem geometricallyRegular_finiteFormalFiber : Specs.FiniteFormalFiberRegularity.{u,v} := by
  intro A B _ _ _ _ _ _ p _ i Q _
  dsimp only
  intro h
  change GeometricallyRegular _ _ at h
  let q := Q.under (Localization.AtPrime p)
  letI : Q.LiesOver q := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver q Q
  letI : Finite (PrimesOver p B) :=
    CommutativeAlgebraNotes.FiniteAlgebraCompletion.finitePrimes A B p
  obtain ⟨hfinite, ⟨e, _⟩, ⟨e', _⟩⟩ := finiteFormalFiberDecomposition (B := B) p i Q
  letI := hfinite
  exact ((h.baseChange_finite.of_algEquiv e).piFactor i).of_algEquiv e'

theorem isGRing_finite : Specs.FiniteAlgebraGRing.{u,v} := by
  intro A B _ _ _ _ _ h
  letI : IsNoetherianRing B := .of_finite A B
  intro P _
  let C := Localization.AtPrime P
  let T := LocalCompletion C
  letI : IsNoetherianRing T := P103.Ch07.CompletedNoetherian.completed_noetherian C _
  apply (regularMap_algebraMap_iff C T).mpr
  refine ⟨inferInstance, ?_⟩
  intro Q _
  let p := P.under A
  let i : PrimesOver p B := ⟨⟨P, inferInstance⟩, rfl⟩
  let R := Localization.AtPrime p
  let H := LocalCompletion R
  letI : IsNoetherianRing H := P103.Ch07.CompletedNoetherian.completed_noetherian R _
  exact geometricallyRegular_finiteFormalFiber p i Q
    (((regularMap_algebraMap_iff R H).mp (h p)).2 _)

section Localization

private theorem map_maximalIdeal_le {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    (maximalIdeal R).map e.toRingHom ≤ maximalIdeal S :=
  (map_ringEquiv_maximalIdeal e).le

private theorem completionMap_symm_apply {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (x : LocalCompletion R) :
    completionMap _ _ e.symm.toRingHom (map_maximalIdeal_le e.symm)
      (completionMap _ _ e.toRingHom (map_maximalIdeal_le e) x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal R) n x)
  rw [eval_completionMap, eval_completionMap, ← ha, quotientPowMap_mk, quotientPowMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (e.symm_apply_apply a)

private noncomputable def completionLocalRingEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) : LocalCompletion R ≃+* LocalCompletion S :=
  RingEquiv.ofRingHom
    (completionMap _ _ e.toRingHom (map_maximalIdeal_le e))
    (completionMap _ _ e.symm.toRingHom (map_maximalIdeal_le e.symm))
    (RingHom.ext (completionMap_symm_apply e.symm))
    (RingHom.ext (completionMap_symm_apply e))

@[simp]
private theorem completionLocalRingEquiv_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (a : R) :
    completionLocalRingEquiv e (algebraMap R (LocalCompletion R) a) =
      algebraMap S (LocalCompletion S) (e a) :=
  completionMap_of _ _ _ _ a

private noncomputable def tensorChangeBase {R S L H H' : Type*}
    [CommRing R] [CommRing S] [CommRing L] [CommRing H] [CommRing H']
    [Algebra R L] [Algebra S L] [Algebra R H] [Algebra S H']
    (e : R ≃+* S) (f : H ≃+* H')
    (he : ∀ a : R, algebraMap R L a = algebraMap S L (e a))
    (hf : ∀ a : R, f (algebraMap R H a) = algebraMap S H' (e a)) :
    (L ⊗[R] H) ≃ₐ[L] L ⊗[S] H' := by
  let F := Algebra.TensorProduct.mapRingHom e.toRingHom (RingHom.id L) f.toRingHom
    (RingHom.ext he) (RingHom.ext hf)
  have he' (a : S) : algebraMap S L a = algebraMap R L (e.symm a) := by
    rw [he, e.apply_symm_apply]
  have hf' (a : S) : f.symm (algebraMap S H' a) = algebraMap R H (e.symm a) := by
    apply f.injective
    rw [f.apply_symm_apply, hf, e.apply_symm_apply]
  let G := Algebra.TensorProduct.mapRingHom e.symm.toRingHom (RingHom.id L) f.symm.toRingHom
    (RingHom.ext he') (RingHom.ext hf')
  refine { toRingEquiv := RingEquiv.ofRingHom F G ?_ ?_, commutes' := ?_ }
  · apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [F, G]
  · apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [F, G]
  · intro x
    change F (x ⊗ₜ[R] (1 : H)) = x ⊗ₜ[S] (1 : H')
    simp [F]

private theorem geometricallyRegular_fiber_of_localRingEquiv {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (P : Ideal S) [P.IsPrime]
    (h : GeometricallyRegular (P.comap e.toRingHom).ResidueField
      ((P.comap e.toRingHom).Fiber (LocalCompletion R))) :
    GeometricallyRegular P.ResidueField (P.Fiber (LocalCompletion S)) := by
  let q := P.comap e.toRingHom
  let k := q.ResidueField
  let L := P.ResidueField
  let ek : k ≃+* L := Ideal.residueFieldRingEquiv q P e rfl
  letI : Algebra k L := ek.toRingHom.toAlgebra
  letI : Algebra R L := ((algebraMap S L).comp e.toRingHom).toAlgebra
  letI : IsScalarTower R k L := .of_algebraMap_eq fun a ↦
    (Ideal.ResidueField.map_algebraMap q P e.toRingHom rfl a).symm
  letI : Module.Finite k L := Module.Finite.of_surjective (Algebra.linearMap k L) ek.surjective
  let e' := Algebra.TensorProduct.cancelBaseChange R k L L (LocalCompletion R)
  let e'' := tensorChangeBase (L := L) e (completionLocalRingEquiv e)
    (fun _ ↦ rfl) (completionLocalRingEquiv_algebraMap e)
  exact h.baseChange_finite.of_algEquiv (e'.trans e'')

theorem isGRing_localization : Specs.LocalizedGRing.{u,v} := by
  intro A B _ _ _ _ M _ h
  letI : IsNoetherianRing B := IsLocalization.isNoetherianRing M B inferInstance
  intro P _
  let R := Localization.AtPrime (P.under A)
  let S := Localization.AtPrime P
  let H := LocalCompletion R
  let T := LocalCompletion S
  letI : IsNoetherianRing H := P103.Ch07.CompletedNoetherian.completed_noetherian R _
  letI : IsNoetherianRing T := P103.Ch07.CompletedNoetherian.completed_noetherian S _
  let e : R ≃+* S := localizationStalkEquiv M P
  apply (regularMap_algebraMap_iff S T).mpr
  refine ⟨inferInstance, fun Q _ ↦ ?_⟩
  apply geometricallyRegular_fiber_of_localRingEquiv e Q
  exact ((regularMap_algebraMap_iff R H).mp (h (P.under A))).2 _

end Localization

theorem isGRing_surjective : Specs.SurjectiveGRing.{u,v} := by
  intro A B _ _ _ f hf h
  letI : Algebra A B := f.toAlgebra
  letI : Module.Finite A B := Module.Finite.of_surjective (Algebra.linearMap A B) hf
  exact isGRing_finite h

end CommutativeAlgebraNotes.Excellence
