import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveCechClassComputation
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.LaurentCechCohomology
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits
open DerivedFormalization.ProjectiveTwists (Index Polynomials)
open DerivedFormalization.LaurentCechCohomology

namespace DerivedFormalization.ProjectiveCechClassComputation

universe u v

open private chartToLaurent_injective polynomial_coeff_allowed
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.LaurentCechCohomology

section Representatives

variable (k : Type u) [Field k] (n : ℕ) {m : ℤ} {J : Finset (Index n)}

private theorem chartCoeff_eq_zero (s : chartPiece k n m J)
    (a : ExponentVector n) (ha : ∑ i, a i ≠ m) :
    (chartToLaurent k n J s.val).coeff a = 0 :=
  AddMonoidAlgebra.mem_supported'.mp s.property a (fun h ↦ ha h.1)

private theorem chart_eq_polynomial (s : chartPiece k n m J) (f : polynomialDegree k n m)
    (h : ∀ a : Exponents n m,
      (chartToLaurent k n J s.val).coeff a.val = (polynomialToLaurent k n f.val).coeff a.val) :
    s.val = algebraMap (Polynomials k n) _ f.val := by
  apply chartToLaurent_injective k J
  have hmap : chartToLaurent k n J (algebraMap (Polynomials k n) _ f.val) =
      polynomialToLaurent k n f.val :=
    IsLocalization.lift_eq (chartProduct_maps_to_unit k n J) f.val
  rw [hmap]
  apply AddMonoidAlgebra.ext
  ext a
  by_cases ha : ∑ i, a i = m
  · exact h ⟨a, ha⟩
  · rw [chartCoeff_eq_zero k n s a ha]
    by_contra hne
    exact ha (polynomial_coeff_allowed k f (Ne.symm hne)).1

open scoped Classical in
private theorem chart_eq_topLaurent (s : chartPiece k n m J) (f : TopExponents n m →₀ k)
    (h : ∀ a : Exponents n m, (chartToLaurent k n J s.val).coeff a.val =
      if hneg : ∀ i, a.val i < 0 then f ⟨a, hneg⟩ else 0) :
    chartToLaurent k n J s.val =
      AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain (fun a : TopExponents n m ↦ a.val.val) f) := by
  classical
  apply AddMonoidAlgebra.ext
  ext a
  rw [AddMonoidAlgebra.coeff_ofCoeff]
  let emb : TopExponents n m → ExponentVector n := fun b ↦ b.val.val
  change _ = Finsupp.mapDomain emb f a
  by_cases ha : ∑ i, a i = m
  · rw [h ⟨a, ha⟩]
    split_ifs with hneg
    · exact (Finsupp.mapDomain_apply_of_injective (f := emb)
        (Subtype.val_injective.comp Subtype.val_injective) f ⟨⟨a, ha⟩, hneg⟩).symm
    · rw [Finsupp.mapDomain_of_notMem_range]
      rintro ⟨b, hb⟩
      apply hneg
      simpa only [← hb] using b.property
  · rw [chartCoeff_eq_zero k n s a ha, Finsupp.mapDomain_of_notMem_range]
    rintro ⟨b, hb⟩
    apply ha
    rw [← hb]
    exact b.val.property

end Representatives

private theorem isZero_of_linearEquiv {k : Type u} [Field k]
    {A : Type u} [AddCommGroup A] [Module k A] {M : ModuleCat.{u} k}
    (hA : Subsingleton A) (e : A ≃ₗ[k] M) : IsZero M :=
  ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun x y ↦ e.symm.injective (hA.elim (e.symm x) (e.symm y))⟩

theorem transportedCechClasses :
    Specs.DerivedFormalization.ProjectiveCechClassComputation.transportedCechClassesType.{u, v} := by
  classical
  intro k _ n hn m sq K e hcoeff C H δ β g hπ I V hV hcard face ρ hρ
  obtain ⟨sq', h₀, hₙ, hexact⟩ := cohomologyComputation k n hn m
  have hsq : sq' = sq := Subsingleton.elim _ _
  subst sq'
  obtain ⟨e₀, he₀⟩ := h₀
  obtain ⟨eₙ, heₙ⟩ := hₙ
  let α (q : ℕ) : K.homology (q : ℤ) ≅ H q := β q ≪≫ δ q
  have hclass (q : ℕ) (z : K.cycles (q : ℤ)) :
      (δ q).hom (C.homologyπ q (g q z)) = (α q).hom (K.homologyπ (q : ℤ) z) := by
    rw [← hπ q z]
    rfl
  let E₀ : polynomialDegree k n m ≃ₗ[k] H 0 := e₀.trans (α 0).toLinearEquiv
  let Eₙ : (TopExponents n m →₀ k) ≃ₗ[k] H n := eₙ.trans (α n).toLinearEquiv
  refine ⟨⟨E₀, ?_⟩, ⟨Eₙ, ?_⟩, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨z, hz, hzcoeff⟩ := he₀ f
    refine ⟨g 0 z, ?_, ?_⟩
    · exact (hclass 0 z).trans (congrArg (fun y : K.homology 0 ↦ (α 0).hom y) hz)
    · intro t
      let x : Term k n m 0 := K.iCycles 0 z
      let s : chartPiece k n m (V 0 t) := e 0 x (face 0 t)
      have hs : ρ 0 (g 0 z) t = s.val :=
        chartToLaurent_injective k (V 0 t) (hρ 0 z t)
      rw [hs]
      apply chart_eq_polynomial k n s f
      intro a
      exact (hcoeff 0 x (face 0 t) a).trans (hzcoeff (V 0 t) a (hcard 0 t))
  · intro f
    obtain ⟨z, hz, hzcoeff⟩ := heₙ f
    refine ⟨g n z, ?_, ?_⟩
    · exact (hclass n z).trans (congrArg (fun y : K.homology (n : ℤ) ↦ (α n).hom y) hz)
    · intro t
      rw [hρ n z t]
      let x : Term k n m (n : ℤ) := K.iCycles (n : ℤ) z
      let s : chartPiece k n m (V n t) := e (n : ℤ) x (face n t)
      apply chart_eq_topLaurent k n s f
      have hfull : V n t = Finset.univ :=
        ((V n t).card_eq_iff_eq_univ).mp (by simpa using hcard n t)
      intro a
      calc
        _ = (x a).val (V n t) := hcoeff (n : ℤ) x (face n t) a
        _ = (x a).val Finset.univ := congrArg (x a).val hfull
        _ = _ := hzcoeff a
  · intro q hq hqn
    exact (α q).isZero_iff.mp
      ((hexact (q : ℤ) (by exact_mod_cast hq) (by exact_mod_cast hqn)).isZero_homology)
  · intro hm
    have hbot := (polynomialGrading k n).2 m hm
    exact ⟨hbot, isZero_of_linearEquiv (Submodule.subsingleton_iff_eq_bot.mpr hbot) E₀⟩
  · intro hEmpty
    let _ := hEmpty
    exact isZero_of_linearEquiv (inferInstance : Subsingleton (TopExponents n m →₀ k)) Eₙ

end DerivedFormalization.ProjectiveCechClassComputation
