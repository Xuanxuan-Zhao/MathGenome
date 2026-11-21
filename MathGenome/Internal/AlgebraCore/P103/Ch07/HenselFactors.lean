import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.HenselFactors
import Mathlib.Algebra.Polynomial.Lifts
import MathGenome.Internal.AlgebraCore.P103.Ch07.HenselFactorStep
import MathGenome.Internal.AlgebraCore.P103.Ch07.HenselFactorLimit

universe u
namespace P103.Ch07.HenselFactors
open Polynomial

/-- Unit resultant gives bijectivity of the bounded correction map.
The adjugate identities apply even when either degree is zero. -/
theorem sylvesterMap_bijective {R : Type u} [CommRing R] (g h : R[X])
    (hu : IsUnit (Polynomial.resultant g h)) :
    Function.Bijective (sylvesterMap g h le_rfl le_rfl) := by
  exact P103.Ch07.HenselFactorStep.sylvesterMap_bijective g h hu

/-- The correction isomorphism over an arbitrary commutative coefficient ring. -/
theorem correction_isomorphism :
    P103.Specs.Ch07.HenselFactors.correction_isomorphismType.{u} := by
  intro R _ g h hg _ hcop
  let e := LinearEquiv.ofBijective (sylvesterMap g h le_rfl le_rfl)
    (sylvesterMap_bijective g h ((isUnit_resultant_iff_isCoprime hg).mpr hcop))
  refine ⟨e, ?_⟩
  intro a b
  change g * b.val + h * a.val = a.val * h + b.val * g
  ring

/-- Coprimality of monic polynomials lifts across an ideal in the Jacobson radical. -/
theorem coprime_of_coprime_reduction {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) (g h : R[X]) (hg : g.Monic) (hh : h.Monic)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I))) :
    IsCoprime g h := by
  exact P103.Ch07.HenselFactorStep.coprime_of_coprime_reduction I hI g h hg hh hcop

/-- Uniqueness uses only the Jacobson condition; no completeness is needed here. -/
theorem factors_unique {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) (g h g' h' : R[X])
    (hg : g.Monic) (_hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I)))
    (hprod : g * h = g' * h')
    (_hgr : g.map (Ideal.Quotient.mk I) = g'.map (Ideal.Quotient.mk I))
    (hhr : h.map (Ideal.Quotient.mk I) = h'.map (Ideal.Quotient.mk I))
    (hd : g.natDegree = g'.natDegree) : g = g' ∧ h = h' := by
  have hc : IsCoprime g h' := coprime_of_coprime_reduction I hI g h' hg hh'
    (hhr ▸ hcop)
  have hdvd : g ∣ g' := hc.dvd_of_dvd_mul_right (hprod ▸ dvd_mul_right g h)
  have he : g' = g := eq_of_monic_of_dvd_of_natDegree_le hg hg' hdvd hd.ge
  subst g'
  exact ⟨rfl, hg.isRegular.left hprod⟩

/-- Arbitrary monic residue polynomials have monic lifts of the prescribed degree. -/
theorem monic_lift {R : Type u} [CommRing R] (I : Ideal R)
    (g₀ : (R ⧸ I)[X]) (hg₀ : g₀.Monic) :
    ∃ g : R[X], g.map (Ideal.Quotient.mk I) = g₀ ∧
      g.natDegree = g₀.natDegree ∧ g.Monic := by
  exact lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective (Ideal.Quotient.mk_surjective) g₀) hg₀

/-- The first approximations have an error with coefficients in `I`. -/
theorem initial_lifts {R : Type u} [CommRing R] (I : Ideal R)
    (f : R[X]) (g₀ h₀ : (R ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hf : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ ∧
      g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree ∧
      ∀ k, (f - g * h).coeff k ∈ I := by
  obtain ⟨g, hgr, hgd, hgm⟩ := monic_lift I g₀ hg₀
  obtain ⟨h, hhr, hhd, hhm⟩ := monic_lift I h₀ hh₀
  refine ⟨g, h, hgm, hhm, hgr, hhr, hgd, hhd, ?_⟩
  intro k
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hz : (f - g * h).map (Ideal.Quotient.mk I) = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, hf, hgr, hhr, sub_self]
  simpa only [coeff_map, coeff_zero] using congrArg (fun p => p.coeff k) hz

/-- In a separated complete ring the residual degrees sum to the original degree. -/
theorem degree_sum {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (g₀ h₀ : (R ⧸ I)[X])
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hred : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    f.natDegree = g₀.natDegree + h₀.natDegree := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [Subsingleton.elim f 0, Subsingleton.elim g₀ 0,
      Subsingleton.elim h₀ 0, natDegree_zero, zero_add]
  have hItop : I ≠ ⊤ := by
    intro he
    have hj : Ideal.jacobson (⊥ : Ideal R) = ⊤ :=
      top_le_iff.mp (he ▸ IsAdicComplete.le_jacobson_bot I)
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp hj)
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  rw [← hf.natDegree_map (Ideal.Quotient.mk I), hred, hg₀.natDegree_mul hh₀]

/-- Ordered monic factor lifting over every separated complete adic ring. -/
theorem factor_lifting :
    P103.Specs.Ch07.HenselFactors.factor_liftingType.{u} := by
  classical
  intro R _ I _ f g₀ h₀ hf hg₀ hh₀ hcop hred
  have hI := IsAdicComplete.le_jacobson_bot I
  have hdeg := degree_sum I f g₀ h₀ hf hg₀ hh₀ hred
  obtain ⟨g, h, hgm, hhm, hgr, hhr, hgd, hhd, herr⟩ :=
    initial_lifts I f g₀ h₀ hg₀ hh₀ hred
  let Q (n : ℕ) (p : R[X] × R[X]) : Prop :=
    p.1.Monic ∧ p.2.Monic ∧
    p.1.map (Ideal.Quotient.mk I) = g₀ ∧
    p.2.map (Ideal.Quotient.mk I) = h₀ ∧
    p.1.natDegree = g₀.natDegree ∧ p.2.natDegree = h₀.natDegree ∧
    ∀ k, (f - p.1 * p.2).coeff k ∈ I ^ (n+1)
  let S (n : ℕ) := {p : R[X] × R[X] // Q n p}
  have start : Q 0 (g, h) := by
    exact ⟨hgm, hhm, hgr, hhr, hgd, hhd, by simpa using herr⟩
  have step (n : ℕ) (p : S n) :
      ∃ q : S (n+1),
        (∀ k, (q.val.1 - p.val.1).coeff k ∈ I ^ (n+1)) ∧
        (∀ k, (q.val.2 - p.val.2).coeff k ∈ I ^ (n+1)) := by
    obtain ⟨hpm, hqm, hpr, hqr, hpd, hqd, hpe⟩ := p.property
    have hpc : IsCoprime (p.val.1.map (Ideal.Quotient.mk I))
        (p.val.2.map (Ideal.Quotient.mk I)) := by rw [hpr, hqr]; exact hcop
    have hpf : f.natDegree = p.val.1.natDegree + p.val.2.natDegree := by
      rw [hpd, hqd]; exact hdeg
    obtain ⟨g', h', hgm', hhm', hgd', hhd', hgc, hhc, he⟩ :=
      P103.Ch07.HenselFactorStep.factor_step I hI n f p.val.1 p.val.2
        hf hpm hqm hpf hpc hpe
    have hgcI : ∀ k, (g' - p.val.1).coeff k ∈ I := by
      intro k
      exact (Ideal.pow_le_self (by omega)) (hgc k)
    have hhcI : ∀ k, (h' - p.val.2).coeff k ∈ I := by
      intro k
      exact (Ideal.pow_le_self (by omega)) (hhc k)
    have hgr' : g'.map (Ideal.Quotient.mk I) = g₀ :=
      (P103.Ch07.HenselFactorLimit.map_eq_of_coeff_sub_mem I hgcI).trans hpr
    have hhr' : h'.map (Ideal.Quotient.mk I) = h₀ :=
      (P103.Ch07.HenselFactorLimit.map_eq_of_coeff_sub_mem I hhcI).trans hqr
    refine ⟨⟨(g', h'), hgm', hhm', hgr', hhr', hgd'.trans hpd,
      hhd'.trans hqd, ?_⟩, hgc, hhc⟩
    simpa only [Nat.add_assoc] using he
  let next (n : ℕ) (p : S n) : S (n+1) := (step n p).choose
  let a : (n : ℕ) → S n := Nat.rec ⟨(g, h), start⟩ next
  have ha (n : ℕ) :
      (∀ k, ((a (n+1)).val.1 - (a n).val.1).coeff k ∈ I ^ (n+1)) ∧
      (∀ k, ((a (n+1)).val.2 - (a n).val.2).coeff k ∈ I ^ (n+1)) :=
    (step n (a n)).choose_spec
  obtain ⟨G, H, hGm, hHm, hGd, hHd, hprod, hGc, hHc⟩ :=
    P103.Ch07.HenselFactorLimit.factor_limit R I g₀.natDegree h₀.natDegree f
      (fun n => (a n).val.1) (fun n => (a n).val.2)
      (fun n => (a n).property.1) (fun n => (a n).property.2.1)
      (fun n => (a n).property.2.2.2.2.1)
      (fun n => (a n).property.2.2.2.2.2.1)
      (fun n => (ha n).1) (fun n => (ha n).2)
      (fun n => (a n).property.2.2.2.2.2.2)
  have hGr : G.map (Ideal.Quotient.mk I) = g₀ := by
    have hc : ∀ k, (G - (a 0).val.1).coeff k ∈ I := by simpa using hGc 0
    exact (P103.Ch07.HenselFactorLimit.map_eq_of_coeff_sub_mem I hc).trans
      (a 0).property.2.2.1
  have hHr : H.map (Ideal.Quotient.mk I) = h₀ := by
    have hc : ∀ k, (H - (a 0).val.2).coeff k ∈ I := by simpa using hHc 0
    exact (P103.Ch07.HenselFactorLimit.map_eq_of_coeff_sub_mem I hc).trans
      (a 0).property.2.2.2.1
  refine ⟨(G, H), ⟨hGm, hHm, hprod, hGr, hHr, hGd, hHd⟩, ?_⟩
  rintro ⟨G', H'⟩ ⟨hGm', hHm', hprod', hGr', hHr', hGd', _⟩
  have hc : IsCoprime (G.map (Ideal.Quotient.mk I))
      (H.map (Ideal.Quotient.mk I)) := by rw [hGr, hHr]; exact hcop
  obtain ⟨heG, heH⟩ := factors_unique I hI G H G' H' hGm hHm hGm' hHm'
    hc (hprod.symm.trans hprod') (hGr.trans hGr'.symm) (hHr.trans hHr'.symm)
    (hGd.trans hGd'.symm)
  exact Prod.ext heG.symm heH.symm

end P103.Ch07.HenselFactors
