import MathGenome.Internal.Specs.D05.Foundations.Crt
import MathGenome.Internal.D05.Foundations.Factorization
import Mathlib.RingTheory.Coprime.Lemmas

/-! The polynomial Chinese remainder construction of paper.tex:380–382.
The proof constructs Bézout representatives, interpolates residue tuples,
and identifies the kernel before passing to the quotient. -/

noncomputable section

namespace D05.Foundations.Crt

open D05.Foundations

variable {K ι : Type*} [Field K] [Fintype ι]

theorem cofactor_mul (q : ι → Polynomial K) (i : ι) :
    q i * crtCofactor q i = crtProduct q := by
  classical
  exact Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)

theorem cofactorIdentity : D05.Specs.Crt.cofactorIdentity := by
  intro K ι _ _ q hq i
  classical
  refine ⟨cofactor_mul q i, ?_⟩
  rw [← cofactor_mul q i]
  exact (mul_div_cancel_left₀ _ (hq i).ne_zero).symm

theorem cofactor_coprime (q : ι → Polynomial K)
    (h : Pairwise fun i j => IsCoprime (q i) (q j)) (i : ι) :
    IsCoprime (crtCofactor q i) (q i) := by
  classical
  exact IsCoprime.prod_left fun j hj => h (Finset.mem_erase.mp hj).1

theorem residue_zero_iff (p f : Polynomial K) :
    Ideal.Quotient.mk (polynomialIdeal p) f = 0 ↔ p ∣ f :=
  Ideal.Quotient.eq_zero_iff_dvd _ _

theorem bezoutResidues : D05.Specs.Crt.bezoutResidues := by
  intro K ι _ _ q _ hq
  classical
  choose u v huv using cofactor_coprime q hq
  refine ⟨u, v, fun i => ⟨huv i, ?_⟩⟩
  intro j
  by_cases hji : j = i
  · subst j
    have hz : Ideal.Quotient.mk (polynomialIdeal (q i)) (q i) = 0 :=
      (residue_zero_iff _ _).mpr dvd_rfl
    have heq := congrArg (Ideal.Quotient.mk (polynomialIdeal (q i))) (huv i)
    simpa [map_add, map_mul, hz] using heq
  · rw [ite_eq_right hji]
    apply (residue_zero_iff _ _).mpr
    apply dvd_mul_of_dvd_right
    exact Finset.dvd_prod_of_mem q (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)

theorem residueInterpolation : D05.Specs.Crt.residueInterpolation := by
  intro K ι _ _ q e f he
  classical
  funext j
  change Ideal.Quotient.mk (polynomialIdeal (q j)) (∑ i, f i * e i) = _
  rw [map_sum, Fintype.sum_eq_single j]
  · simp [map_mul, he]
  · intro i hij
    simp [map_mul, he, Ne.symm hij]

theorem surjectiveResidues : D05.Specs.Crt.surjectiveResidues := by
  intro K ι _ _ q hm hq y
  classical
  obtain ⟨u, v, hu⟩ := bezoutResidues K ι q hm hq
  choose f hf using fun i => Ideal.Quotient.mk_surjective (y i)
  refine ⟨∑ i, f i * (u i * crtCofactor q i), ?_⟩
  rw [residueInterpolation K ι q (fun i => u i * crtCofactor q i) f
    (fun i => (hu i).2)]
  exact funext hf

theorem product_dvd_iff (q : ι → Polynomial K)
    (hq : Pairwise fun i j => IsCoprime (q i) (q j)) (f : Polynomial K) :
    crtProduct q ∣ f ↔ ∀ i, q i ∣ f := by
  classical
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem q (Finset.mem_univ i)).trans h
  · exact Fintype.prod_dvd_of_coprime hq

theorem kernelResidues : D05.Specs.Crt.kernelResidues := by
  intro K ι _ _ q _ hq
  refine ⟨?_, product_dvd_iff q hq⟩
  ext f
  change polynomialResidues q f = 0 ↔ _
  rw [Ideal.mem_span_singleton, product_dvd_iff q hq]
  constructor
  · intro h i
    exact (residue_zero_iff _ _).mp (congrFun h i)
  · intro h
    funext i
    exact (residue_zero_iff _ _).mpr (h i)

/-- Two classes modulo the product agree precisely when all their residue
classes agree. This also applies when some q_i are units. -/
theorem residue_eq_iff (q : ι → Polynomial K)
    (hq : Pairwise fun i j => IsCoprime (q i) (q j)) (f g : Polynomial K) :
    Ideal.Quotient.mk (polynomialIdeal (crtProduct q)) f =
        Ideal.Quotient.mk (polynomialIdeal (crtProduct q)) g ↔
      ∀ i, Ideal.Quotient.mk (polynomialIdeal (q i)) f =
        Ideal.Quotient.mk (polynomialIdeal (q i)) g := by
  simp only [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact product_dvd_iff q hq (f - g)

theorem residueIdempotents : D05.Specs.Crt.residueIdempotents := by
  intro K ι _ _ q e _ hq he
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply (residue_eq_iff q hq _ _).mpr
    intro j
    simp only [map_mul, he]
    split_ifs <;> simp
  · intro i j hij
    rw [← map_zero (Ideal.Quotient.mk (polynomialIdeal (crtProduct q)))]
    apply (residue_eq_iff q hq _ _).mpr
    intro k
    simp only [map_mul, map_zero, he]
    by_cases hki : k = i
    · subst k
      simp [hij]
    · simp [hki]
  · rw [← map_one (Ideal.Quotient.mk (polynomialIdeal (crtProduct q)))]
    apply (residue_eq_iff q hq _ _).mpr
    intro j
    simp only [map_sum, map_one, he]
    simp

theorem chineseRemainder : D05.Specs.Crt.chineseRemainder := by
  intro K ι _ _ q hm hq
  have hker := (kernelResidues K ι q hm hq).1
  have hz : ∀ f : Polynomial K, f ∈ polynomialIdeal (crtProduct q) →
      polynomialResidues q f = 0 := by
    intro f hf
    change f ∈ RingHom.ker (polynomialResidues q).toRingHom
    rwa [hker]
  let F := Ideal.Quotient.liftₐ (polynomialIdeal (crtProduct q)) (polynomialResidues q) hz
  have hF : Function.Bijective F := by
    constructor
    · exact (Ideal.injective_lift_iff hz).mpr hker
    · exact Ideal.Quotient.lift_surjective_of_surjective (polynomialIdeal (crtProduct q)) hz
        (surjectiveResidues K ι q hm hq)
  exact ⟨AlgEquiv.ofBijective F hF, fun _ _ => rfl⟩

theorem unitResidue : D05.Specs.Crt.unitResidue := by
  intro K _ p hp
  apply Ideal.Quotient.subsingleton_iff.mpr
  exact Ideal.span_singleton_eq_top.mpr hp

theorem emptyFamily : D05.Specs.Crt.emptyFamily := by
  intro K ι _ _ _ q
  have hQ : crtProduct q = 1 := by simp [crtProduct]
  refine ⟨hQ, ?_, inferInstance⟩
  apply unitResidue K
  rw [hQ]
  exact isUnit_one

end D05.Foundations.Crt
