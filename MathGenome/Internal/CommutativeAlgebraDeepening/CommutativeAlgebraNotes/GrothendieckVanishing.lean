import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FinitePrimeFiltration
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyBaseChange
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.GrothendieckVanishing
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.Category

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.GrothendieckVanishing

universe u

/-- The zero module has zero local cohomology in every degree. -/
theorem localCohomologyIsZeroOfSubsingleton : zeroModuleType.{u} := by
  intro R _ _ I M hM q
  have hs : Module.support R M = ∅ := Module.support_eq_empty_iff.mpr hM
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply (Module.support_eq_empty_iff (R := R)).mp
  exact Set.eq_empty_iff_forall_notMem.mpr fun p hp => by
    have h := (localCohomologySupportSubset I q M hp).2
    simp [hs] at h

private theorem localCohomology_map_smul_id {R : Type u} [CommRing R] (I : Ideal R)
    (n : ℕ) (M : ModuleCat.{u} R) (a : R) :
    (localCohomology I (n : ℤ)).map (a • 𝟙 M) =
      a • 𝟙 ((localCohomology I (n : ℤ)).obj M) := by
  let F := idealTorsionFunctor I
  let Q := injectiveResolution M
  let e := Q.isoRightDerivedObj F n
  change (F.rightDerived n).map (a • 𝟙 M) = a • 𝟙 _
  let G := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  have hG : G.map (a • 𝟙 Q.cocomplex) = a • 𝟙 (G.obj Q.cocomplex) := by
    ext k x
    rfl
  have hH (K : CochainComplex (ModuleCat.{u} R) ℕ) :
      H.map (a • 𝟙 K) = a • 𝟙 (H.obj K) := by
    change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (a • 𝟙 K)) = _
    rw [show (HomologicalComplex.shortComplexFunctor _ _ n).map (a • 𝟙 K) =
      a • 𝟙 (K.sc n) by ext <;> rfl, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  have hcomm : Q.ι.f 0 ≫ (a • 𝟙 Q.cocomplex).f 0 = (a • 𝟙 M) ≫ Q.ι.f 0 := by
    rw [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
    apply ModuleCat.hom_ext
    ext x
    exact ((Q.ι.f 0).hom.map_smul a x).symm
  rw [← cancel_mono e.hom, InjectiveResolution.isoRightDerivedObj_hom_naturality (a • 𝟙 M) Q Q
    (a • 𝟙 Q.cocomplex) hcomm F n]
  change e.hom ≫ H.map (G.map (a • 𝟙 Q.cocomplex)) =
    (a • 𝟙 ((F.rightDerived n).obj M)) ≫ e.hom
  rw [hG, hH, Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

private theorem localCohomology_isZero_of_shortExact {R : Type u}
    [CommRing R] [IsNoetherianRing R] (I : Ideal R) (q : ℤ)
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (h₁ : IsZero ((localCohomology I q).obj S.X₁))
    (h₃ : IsZero ((localCohomology I q).obj S.X₃)) :
    IsZero ((localCohomology I q).obj S.X₂) := by
  have he := (ShortComplex.moduleCat_exact_iff _).mp (localCohomology_exact I hS q).1.exact
  let h₁' := ModuleCat.isZero_iff_subsingleton.mp h₁
  let h₃' := ModuleCat.isZero_iff_subsingleton.mp h₃
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ := he x (Subsingleton.elim _ 0)
  simpa [Subsingleton.elim y 0] using hy.symm

-- The multiplication sequence reduces domain vanishing to the preceding cohomological degree.
private theorem domainVanishing {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (I : Ideal R) (n : ℕ) (hdim : ringKrullDim R < ((n + 1 : ℕ) : WithBot ℕ∞))
    (ih : ∀ (M : ModuleCat.{u} R) [Module.Finite R M],
      Module.supportDim R M < (n : WithBot ℕ∞) →
      IsZero ((localCohomology I (n : ℤ)).obj M)) :
    IsZero ((localCohomology I ((n + 1 : ℕ) : ℤ)).obj (ModuleCat.of R R)) := by
  by_cases hI : I = ⊥
  · subst I
    exact (Functor.isZero_iff _).mp
      (localCohomologyBotIsZero _ (by omega)) _
  by_cases htop : I = ⊤
  · subst I
    exact (Functor.isZero_iff _).mp (localCohomologyTopIsZero (R := R) _) _
  obtain ⟨x, hxI, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let M := ModuleCat.of R R
  have hreg : IsSMulRegular R x := IsSMulRegular.of_ne_zero hx
  let S := M.smulShortComplex x
  have hS : S.ShortExact := hreg.smulShortComplex_shortExact
  have hdrop : Module.supportDim R (QuotSMulTop x R) + 1 ≤ ringKrullDim R := by
    rw [← Module.supportDim_self_eq_ringKrullDim]
    exact Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
      (fun p hp => hreg.notMem_of_mem_minimalPrimes hp)
  have hdimQ : Module.supportDim R (QuotSMulTop x R) < (n : WithBot ℕ∞) := by
    apply lt_of_not_ge
    intro h
    have h' : (n : WithBot ℕ∞) + 1 ≤ Module.supportDim R (QuotSMulTop x R) + 1 :=
      add_le_add h le_rfl
    exact (not_le_of_gt hdim) (by simpa [Nat.cast_add] using h'.trans hdrop)
  have hz : IsZero ((localCohomology I (n : ℤ)).obj S.X₃) :=
    ih (ModuleCat.of R (QuotSMulTop x R)) hdimQ
  have he := (localCohomology_exact I hS (n : ℤ)).2.2
  have hm := (ShortComplex.exact_iff_mono _ (hz.eq_of_src _ _)).mp he.exact
  have hinj : Function.Injective (fun y : (localCohomology I ((n + 1 : ℕ) : ℤ)).obj M =>
      x • y) := by
    have hi := (ModuleCat.mono_iff_injective _).mp hm
    have hn : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := (Int.natCast_succ n).symm
    change Function.Injective ((localCohomology I ((n : ℤ) + 1)).map (x • 𝟙 M)) at hi
    rw [hn, localCohomology_map_smul_id] at hi
    exact hi
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨k, _, hk⟩ := localCohomology_isPowerTorsion I ((n + 1 : ℕ) : ℤ) M y
  apply hinj.iterate k
  rw [smul_iterate_apply, smul_iterate_apply, hk _ (Ideal.pow_mem_pow hxI k), smul_zero]

-- The finite filtration transfers vanishing on the prime cyclic quotients to the module.
private theorem of_primeQuotients {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (q : ℤ) (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : ∀ p : PrimeSpectrum R, ringKrullDim (R ⧸ p.asIdeal) ≤ Module.supportDim R M →
      IsZero ((localCohomology I q).obj (ModuleCat.of R (R ⧸ p.asIdeal)))) :
    IsZero ((localCohomology I q).obj M) := by
  obtain ⟨F⟩ := PrimeFiltration.exists_filtration R M
  have stages : ∀ k, IsZero ((localCohomology I q).obj (ModuleCat.of R (F.stage k))) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      apply localCohomologyIsZeroOfSubsingleton I _ _ q
      rw [show (F.stage 0 : Submodule R M) = ⊥ from F.first_eq_bot]
      infer_instance
    | succ i hi =>
      obtain ⟨hinj, hexact, hsurj⟩ := F.step_shortExact i
      let S := ModuleCat.shortComplexOfCompEqZero _ _ hexact.linearMap_comp_eq_zero
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hexact hinj hsurj
      apply localCohomology_isZero_of_shortExact I q hS hi
      apply h (F.prime i)
      rw [F.supportDim_eq]
      exact le_iSup (fun j => ringKrullDim (R ⧸ (F.prime j).asIdeal)) i
  let e : F.stage (Fin.last F.length) ≃ₗ[R] M :=
    (LinearEquiv.ofEq _ _ F.last_eq_top).trans Submodule.topEquiv
  exact (stages _).of_iso ((localCohomology I q).mapIso e.toModuleIso).symm

private theorem vanishing_nat (n : ℕ) :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
      (M : ModuleCat.{u} R) [Module.Finite R M],
      Module.supportDim R M < (n : WithBot ℕ∞) →
      IsZero ((localCohomology I (n : ℤ)).obj M) := by
  induction n with
  | zero =>
    intro R _ _ I M _ h
    have hb : Module.supportDim R M = ⊥ := by
      by_contra hne
      obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
      rw [← hd] at h
      exact (not_lt_of_ge (zero_le (a := d))) (WithBot.coe_lt_coe.mp h)
    exact localCohomologyIsZeroOfSubsingleton I M
      ((Module.supportDim_eq_bot_iff_subsingleton R M).mp hb) 0
  | succ n ih =>
    intro R _ _ I M _ h
    apply of_primeQuotients I _ M
    intro p hp
    let B := R ⧸ p.asIdeal
    let f : R →+* B := Ideal.Quotient.mk p.asIdeal
    let : p.asIdeal.IsPrime := p.isPrime
    have hz := domainVanishing (I.map f) n (hp.trans_lt h) (ih (I.map f))
    obtain ⟨e⟩ := localCohomologyChangeOfRings f I ((n + 1 : ℕ) : ℤ)
    have hrestr : IsZero ((ModuleCat.restrictScalars f).obj
        ((localCohomology (I.map f) ((n + 1 : ℕ) : ℤ)).obj (ModuleCat.of B B))) :=
      ModuleCat.isZero_iff_subsingleton.mpr (by
        have hs := ModuleCat.isZero_iff_subsingleton.mp hz
        exact hs)
    exact hrestr.of_iso (e.app (ModuleCat.of B B))

/-- Grothendieck's vanishing theorem for finite modules over a Noetherian ring. -/
theorem grothendieckVanishing : vanishingType.{u} := by
  intro R _ _ I M _ q h
  rcases h with hb | ⟨d, hd, hq⟩
  · exact localCohomologyIsZeroOfSubsingleton I M
      ((Module.supportDim_eq_bot_iff_subsingleton R M).mp hb) q
  cases q with
  | negSucc n => omega
  | ofNat n =>
    apply vanishing_nat n I M
    exact hd.trans_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Int.ofNat_lt.mp hq)))

end CommutativeAlgebraNotes
