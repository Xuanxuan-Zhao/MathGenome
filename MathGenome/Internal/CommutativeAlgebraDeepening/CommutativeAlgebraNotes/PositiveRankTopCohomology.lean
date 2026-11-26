import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CechGeneratorIndependence
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FiniteRegularNormalization
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyBaseChange
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularLocalTopCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PositiveRankTopCohomology
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import Batteries.Tactic.OpenPrivate

open CategoryTheory IsLocalRing
open scoped TensorProduct nonZeroDivisors

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.IdealTorsion (localCohomology)
open Specs.CommutativeAlgebraNotes.PositiveRankTopCohomology (PositiveRankNonvanishing)
open private localCohomology_map_smul_id from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GrothendieckVanishing

universe u

/-- A functional on the generic fibre that detects `x` can be scaled to take
values in the domain on a finite module. -/
private theorem exists_linearMap_ne_zero_at {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] {x : M}
    (hx : (1 : FractionRing R) ⊗ₜ[R] x ≠ 0) :
    ∃ f : M →ₗ[R] R, f x ≠ 0 := by
  let K := FractionRing R
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K hx
  let g : M →ₗ[R] K := (φ.restrictScalars R).comp (TensorProduct.mk R K M 1)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples R⁰ s g
  let i : R →ₗ[R] K := Algebra.linearMap R K
  let bg : M →ₗ[R] K := (b : R) • g
  have hbg : ∀ y, bg y ∈ LinearMap.range i := by
    intro y
    have hspan : Submodule.span R (s : Set M) ≤ (LinearMap.range i).comap bg :=
      Submodule.span_le.mpr fun z hz => hb z hz
    exact hspan (by rw [hs]; trivial)
  let f := bg.codRestrictOfInjective i (IsFractionRing.injective R K) hbg
  refine ⟨f, fun h => ?_⟩
  have he : i (f x) = bg x := LinearMap.codRestrictOfInjective_comp_apply ..
  rw [h, map_zero] at he
  have hb0 : algebraMap R K (b : R) ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr (nonZeroDivisors.coe_ne_zero b)
  apply mul_ne_zero hb0 hφ
  simpa only [bg, g, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, TensorProduct.mk_apply, Algebra.smul_def] using he.symm

/-- A positive-dimensional generic fibre has a nonzero element coming from
the module, since those elements span the fibre over the fraction field. -/
private theorem exists_tmul_one_ne_zero {B M : Type*} [CommRing B] [IsDomain B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hrank : 0 < Module.finrank (FractionRing B) (FractionRing B ⊗[B] M)) :
    ∃ x : M, (1 : FractionRing B) ⊗ₜ[B] x ≠ 0 := by
  obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hrank
  by_contra! h
  apply hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    calc
      a ⊗ₜ[B] x = a • ((1 : FractionRing B) ⊗ₜ[B] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = 0 := by rw [h x, smul_zero]
  | add z w hz hw => rw [hz, hw, add_zero]

/-- Degree-`d` local cohomology of the ring is nonzero when `d` is the
dimension of a regular local ring. -/
private theorem regular_top_nonzero {S : Type u} [CommRing S] [IsRegularLocalRing S]
    (d : ℕ) (hd : ringKrullDim S = (d : WithBot ℕ∞)) :
    ∃ z : (localCohomology (maximalIdeal S) (d : ℤ)).obj (ModuleCat.of S S), z ≠ 0 := by
  classical
  have hfg : (maximalIdeal S).FG := IsNoetherian.noetherian _
  obtain ⟨s, hc, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hcard : s.card = d := by
    have hr := IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)
    rw [hd, ← hc] at hr
    exact_mod_cast hr
  have hlen : s.toList.length = d := by simpa using hcard
  have hgen : Ideal.span {r | r ∈ s.toList} = maximalIdeal S := by
    rw [show {r | r ∈ s.toList} = (s : Set S) by ext r; simp]
    exact hspan
  obtain ⟨e, h, hz⟩ := (regularLocalTopCohomology d hd).1 s.toList hlen hgen
  rw [← hlen]
  exact ⟨_, hz⟩

/-- Top local cohomology at the maximal ideal is nonzero for a finite module
of positive rank over a complete Noetherian local domain. -/
theorem positiveRankTopCohomology : PositiveRankNonvanishing.{u} := by
  intro B _ _ _ _ _ d hd N _ hrank
  obtain ⟨e, he, S, hS, hnorm⟩ := CoefficientRings.finiteRegularNormalization B
  have hed : e = d := by exact_mod_cast he.symm.trans hd
  subst e
  let : IsLocalRing S := hS
  obtain ⟨_, hdom, hreg, _, hdim, hinj, _, hfin, hrad⟩ := hnorm
  let : IsDomain S := hdom
  let : IsRegularLocalRing S := hreg
  let ι : S →+* B := S.subtype
  let : Algebra S B := ι.toAlgebra
  let : Module.Finite S B := hfin
  let M := (ModuleCat.restrictScalars ι).obj N
  let : Module.Finite B M := ‹Module.Finite B N›
  let : IsScalarTower S B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module.Finite S M := Module.Finite.trans B M
  obtain ⟨x, hx⟩ := exists_tmul_one_ne_zero hrank
  have hxS : (1 : FractionRing S) ⊗ₜ[S] (show M from x) ≠ 0 := by
    intro hzero
    obtain ⟨b, hb⟩ := (IsLocalizedModule.eq_zero_iff S⁰
      (TensorProduct.mk S (FractionRing S) M 1)).mp hzero
    have hbi : ι (b : S) ≠ 0 := hinj.ne (nonZeroDivisors.coe_ne_zero b)
    apply hx
    exact (IsLocalizedModule.eq_zero_iff B⁰
      (TensorProduct.mk B (FractionRing B) N 1)).mpr
      ⟨⟨ι (b : S), mem_nonZeroDivisors_of_ne_zero hbi⟩, hb⟩
  obtain ⟨g, hg⟩ := exists_linearMap_ne_zero_at hxS
  let X := ModuleCat.of S S
  let H := localCohomology (maximalIdeal S) (d : ℤ)
  let f : X ⟶ M := ModuleCat.ofHom (LinearMap.toSpanSingleton S M x)
  let p : M ⟶ X := ModuleCat.ofHom g
  have hcomp : f ≫ p = g x • 𝟙 X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change g (r • (show M from x)) = g x * r
    rw [map_smul, smul_eq_mul, mul_comm]
  obtain ⟨z, hz⟩ := regular_top_nonzero d hdim
  obtain ⟨y, hy⟩ := (regularLocalTopCohomology d hdim).2 (g x) hg z
  have hy' : H.map p (H.map f y) = z := by
    change (H.map f ≫ H.map p) y = z
    rw [← Functor.map_comp, hcomp, localCohomology_map_smul_id]
    exact hy
  have hmid : H.map f y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy'
    exact hz hy'.symm
  obtain ⟨changeRings⟩ := localCohomologyChangeOfRings ι (maximalIdeal S) (d : ℤ)
  have hmax : (maximalIdeal B).radical = maximalIdeal B :=
    (inferInstance : (maximalIdeal B).IsPrime).radical
  obtain ⟨changeIdeal⟩ := localCohomologyIsoOfRadicalEq (hrad.trans hmax.symm) (d : ℤ)
  let eR := (changeRings.app N).toLinearEquiv
  let eI := (changeIdeal.app N).toLinearEquiv
  exact nontrivial_of_ne (eI (eR (H.map f y))) 0
    (eI.map_ne_zero_iff.mpr (eR.map_ne_zero_iff.mpr hmid))

end CommutativeAlgebraNotes
