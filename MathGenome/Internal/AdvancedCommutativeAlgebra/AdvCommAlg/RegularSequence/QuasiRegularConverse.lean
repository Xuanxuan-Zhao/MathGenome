import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.QuasiRegularConverse
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.AssociatedGraded
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.DegreeOneConverse
import Mathlib.RingTheory.Filtration

/-! The separated converse in RK-11. -/
noncomputable section
open scoped TensorProduct Pointwise
namespace AdvCommAlg.RegularSequence.QuasiRegularConverse
open P103.Rees GradedComparison.Core AssociatedGraded.Core AssociatedGraded
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (x : List R)

/-- Multiplication by an indeterminate, in the finite coefficient model. -/
def shiftRelation (i : Fin x.length) :
    ((Fin x.length →₀ ℕ) →₀ M) →ₗ[R] ((Fin x.length →₀ ℕ) →₀ M) :=
  Finsupp.lmapDomain M R (fun d => d + Finsupp.single i 1)

@[simp] lemma shiftRelation_apply (i : Fin x.length)
    (p : (Fin x.length →₀ ℕ) →₀ M) (d : Fin x.length →₀ ℕ) :
    shiftRelation M x i p (d + Finsupp.single i 1) = p d := by
  exact Finsupp.mapDomain_apply_of_injective (add_left_injective _) p d

lemma shiftRelation_homogeneous (i : Fin x.length) (n : ℕ)
    {p : (Fin x.length →₀ ℕ) →₀ M}
    (hp : p ∈ homogeneousRelations M x ⊤ n) :
    shiftRelation M x i p ∈ homogeneousRelations M x ⊤ (n + 1) := by
  classical
  refine ⟨fun _ => Submodule.mem_top, ?_⟩
  intro e he
  have hmem := (Finsupp.mem_support_iff.mpr he)
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (Finsupp.mapDomain_support hmem)
  rw [map_add, Finsupp.degree_single, hp.2 d (Finsupp.mem_support_iff.mp hd)]

lemma shiftRelation_evaluation (i : Fin x.length)
    (p : (Fin x.length →₀ ℕ) →₀ M) :
    relationEvaluation M x (shiftRelation M x i p) = x[i] • relationEvaluation M x p := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]
  | single d m =>
    simp only [shiftRelation, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      relationEvaluation, Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply]
    rw [monomialValue_add, smul_smul, mul_comm]
    simp [monomialValue]

/-- Injectivity of the graded comparison cancels a generator at every finite
filtration level. No separation or properness is needed here. -/
lemma generator_power_cancellation
    (hi : Function.Injective (comparison M x)) (i : Fin x.length)
    (n : ℕ) {m : M}
    (hm : x[i] • m ∈ sequenceIdeal x ^ (n + 1) • (⊤ : Submodule R M)) :
    m ∈ sequenceIdeal x ^ n • (⊤ : Submodule R M) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : sequenceIdeal x ^ (n + 1 + 1) ≤ sequenceIdeal x ^ (n + 1) :=
      Ideal.pow_le_pow_right (by omega)
    have hmn := ih (Submodule.smul_mono_left hle hm)
    obtain ⟨p, hp, he⟩ := homogeneous_generation M x ⊤ n hmn
    have hcoeff := relation_coefficients M x (coefficients_of_comparison_injective M x hi)
      (n + 1) (shiftRelation_homogeneous M x i n hp)
      (by simpa only [shiftRelation_evaluation, he] using hm)
    have hp' : p ∈ homogeneousRelations M x (sequenceIdeal x • ⊤) n :=
      ⟨fun d => by
        rw [← shiftRelation_apply M x i p d]
        exact hcoeff (d + Finsupp.single i 1), hp.2⟩
    rw [← he]
    have hg := relationEvaluation_mem M x (sequenceIdeal x • ⊤) n hp'
    simpa only [pow_succ, mul_smul] using hg

/-- Separation turns finite-level cancellation into a nonzerodivisor statement. -/
lemma generator_regular_of_separated
    (hi : Function.Injective (comparison M x)) (i : Fin x.length)
    (hsep : (⨅ n : ℕ, sequenceIdeal x ^ n • (⊤ : Submodule R M)) = ⊥) :
    IsSMulRegular M x[i] := by
  apply (injective_iff_map_eq_zero (DistribSMul.toLinearMap R M x[i])).mpr
  intro m hm
  change x[i] • m = 0 at hm
  have hmem : m ∈ (⨅ n : ℕ, sequenceIdeal x ^ n • (⊤ : Submodule R M)) := by
    simp only [Submodule.mem_iInf]
    intro n
    exact generator_power_cancellation M x hi i n (by rw [hm]; exact Submodule.zero_mem _)
  rwa [hsep, Submodule.mem_bot] at hmem

/-- The variables of the tail retain their positions after the first variable. -/
def tailExponent (a : R) (d : Fin x.length →₀ ℕ) : Fin (a :: x).length →₀ ℕ :=
  d.embDomain (Fin.succEmb x.length)

lemma tailExponent_injective (a : R) : Function.Injective (tailExponent x a) :=
  Finsupp.embDomain_injective _

@[simp] lemma tailExponent_degree (a : R) (d : Fin x.length →₀ ℕ) :
    (tailExponent x a d).degree = d.degree := by
  rw [tailExponent, Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]

@[simp] lemma tailExponent_zero (a : R) (d : Fin x.length →₀ ℕ) :
    tailExponent x a d 0 = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact Fin.succ_ne_zero i hi

@[simp] lemma tailExponent_value (a : R) (d : Fin x.length →₀ ℕ) :
    monomialValue (a :: x) (tailExponent x a d) = monomialValue x d := by
  classical
  simp only [monomialValue, tailExponent, Finsupp.prod_embDomain]
  apply Finsupp.prod_congr
  intro i hi
  simp [Fin.succEmb]

def embedRelation (a : R) :
    ((Fin x.length →₀ ℕ) →₀ M) →ₗ[R] ((Fin (a :: x).length →₀ ℕ) →₀ M) :=
  Finsupp.lmapDomain M R (tailExponent x a)

@[simp] lemma embedRelation_apply (a : R) (p : (Fin x.length →₀ ℕ) →₀ M)
    (d : Fin x.length →₀ ℕ) :
    embedRelation M x a p (tailExponent x a d) = p d :=
  Finsupp.mapDomain_apply_of_injective (tailExponent_injective x a) p d

lemma embedRelation_homogeneous (a : R) (n : ℕ)
    {p : (Fin x.length →₀ ℕ) →₀ M}
    (hp : p ∈ homogeneousRelations M x ⊤ n) :
    embedRelation M x a p ∈ homogeneousRelations M (a :: x) ⊤ n := by
  classical
  refine ⟨fun _ => Submodule.mem_top, ?_⟩
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr he))
  rw [tailExponent_degree]
  exact hp.2 d (Finsupp.mem_support_iff.mp hd)

@[simp] lemma embedRelation_evaluation (a : R) (p : (Fin x.length →₀ ℕ) →₀ M) :
    relationEvaluation M (a :: x) (embedRelation M x a p) = relationEvaluation M x p := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | single d m =>
    simp [embedRelation, relationEvaluation, tailExponent_value]

lemma shiftRelation_zero_of_exponent_zero (y : List R) (i : Fin y.length)
    (p : (Fin y.length →₀ ℕ) →₀ M) (d : Fin y.length →₀ ℕ) (hd : d i = 0) :
    shiftRelation M y i p d = 0 := by
  classical
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨e, he⟩
  have hh := congrArg (fun f : Fin y.length →₀ ℕ => f i) he
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, hd] at hh
  omega

lemma tailIdeal_le_cons (a : R) : sequenceIdeal x ≤ sequenceIdeal (a :: x) := by
  exact Ideal.span_mono (fun _ h => List.mem_cons_of_mem a h)

/-- On M/aM, the ideals of the full list and its tail act identically. -/
lemma quotient_cons_smul (a : R) :
    sequenceIdeal (a :: x) • (⊤ : Submodule R (QuotSMulTop a M)) =
      sequenceIdeal x • (⊤ : Submodule R (QuotSMulTop a M)) := by
  have ha : a • (⊤ : Submodule R (QuotSMulTop a M)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro q hq
    obtain ⟨q', _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hq
    exact (Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M a)) q'
  rw [Ideal.ofList_cons_smul, ha, bot_sup_eq]

/-- Removing the first generator preserves the homogeneous coefficient
criterion, by cancellation of that generator at finite filtration levels. -/
lemma quotient_coefficients (a : R)
    (hi : Function.Injective (comparison M (a :: x))) :
    HomogeneousCoefficients (QuotSMulTop a M) x := by
  classical
  let Q := QuotSMulTop a M
  let f : M →ₗ[R] Q := (a • (⊤ : Submodule R M)).mkQ
  intro n s hd c hc d hds
  choose m hm using fun e => (a • (⊤ : Submodule R M)).mkQ_surjective (c e)
  let p : (Fin x.length →₀ ℕ) →₀ M := ∑ e ∈ s, Finsupp.single e (m e)
  have hp : p ∈ homogeneousRelations M x ⊤ n := by
    refine ⟨fun _ => Submodule.mem_top, ?_⟩
    intro e he
    by_cases hs : e ∈ s
    · exact hd e hs
    · exact False.elim (he (by simp [p, Finsupp.single_apply, hs]))
  have heval : f (relationEvaluation M x p) = ∑ e ∈ s, monomialValue x e • c e := by
    simp only [p, map_sum, relationEvaluation, Finsupp.lsum_single,
      LinearMap.smul_apply, LinearMap.id_apply, map_smul]
    apply Finset.sum_congr rfl
    intro e he
    rw [show f (m e) = c e from hm e]
  have hmap : f (relationEvaluation M x p) ∈
      sequenceIdeal (a :: x) ^ (n + 1) • (⊤ : Submodule R Q) := by
    rw [heval]
    exact Submodule.smul_mono_left (pow_le_pow_left' (tailIdeal_le_cons x a) (n + 1)) hc
  have hpre : relationEvaluation M x p ∈
      sequenceIdeal (a :: x) ^ (n + 1) • (⊤ : Submodule R M) ⊔ a • ⊤ := by
    have hh := (Submodule.comap_smul_top_of_surjective
      (sequenceIdeal (a :: x) ^ (n + 1)) f (Submodule.mkQ_surjective _))
    rw [Submodule.ker_mkQ] at hh
    rw [← hh]
    exact hmap
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hpre
  obtain ⟨b, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv
  have hpb : relationEvaluation M (a :: x) (embedRelation M x a p) - a • b = u := by
    rw [embedRelation_evaluation, ← huv]
    abel
  have hpn : relationEvaluation M (a :: x) (embedRelation M x a p) ∈
      sequenceIdeal (a :: x) ^ n • (⊤ : Submodule R M) :=
    relationEvaluation_mem M (a :: x) ⊤ n (embedRelation_homogeneous M x a n hp)
  have hbn : a • b ∈ sequenceIdeal (a :: x) ^ n • (⊤ : Submodule R M) := by
    have hule := Submodule.smul_mono_left
      (show sequenceIdeal (a :: x) ^ (n + 1) ≤ sequenceIdeal (a :: x) ^ n from
        Ideal.pow_le_pow_right (by omega)) hu
    have heq : a • b = relationEvaluation M (a :: x) (embedRelation M x a p) - u := by
      rw [embedRelation_evaluation, ← huv]; abel
    rw [heq]
    exact Submodule.sub_mem _ hpn hule
  have hfull : p d ∈ sequenceIdeal (a :: x) • (⊤ : Submodule R M) := by
    cases n with
    | zero =>
      have hule : a • b ∈ sequenceIdeal (a :: x) ^ (0 + 1) • (⊤ : Submodule R M) := by
        simpa only [Nat.zero_add, pow_one] using Submodule.smul_mem_smul
          (show a ∈ sequenceIdeal (a :: x) from Ideal.subset_span (List.mem_cons_self))
          (Submodule.mem_top : b ∈ (⊤ : Submodule R M))
      have hzero := relation_coefficients M (a :: x)
        (coefficients_of_comparison_injective M (a :: x) hi) 0
        (embedRelation_homogeneous M x a 0 hp)
        (by rw [embedRelation_evaluation, ← huv]; exact Submodule.add_mem _ hu hule)
      rw [← embedRelation_apply M x a p d]
      exact hzero _
    | succ k =>
      have hb : b ∈ sequenceIdeal (a :: x) ^ k • (⊤ : Submodule R M) :=
        generator_power_cancellation M (a :: x) hi 0 k hbn
      obtain ⟨q, hq, heq⟩ := homogeneous_generation M (a :: x) ⊤ k hb
      let t := embedRelation M x a p - shiftRelation M (a :: x) 0 q
      have ht : t ∈ homogeneousRelations M (a :: x) ⊤ (k + 1) :=
        (homogeneousRelations M (a :: x) ⊤ (k + 1)).sub_mem
          (embedRelation_homogeneous M x a (k + 1) hp)
          (shiftRelation_homogeneous M (a :: x) 0 k hq)
      have hte : relationEvaluation M (a :: x) t = u := by
        simp only [t, map_sub, shiftRelation_evaluation, heq]
        exact hpb
      have htcoeff := relation_coefficients M (a :: x)
        (coefficients_of_comparison_injective M (a :: x) hi) (k + 1) ht (hte ▸ hu)
      have htd : t (tailExponent x a d) = p d := by
        dsimp [t]
        exact (congrArg₂ (fun z w : M => z - w)
          (embedRelation_apply M x a p d)
          (shiftRelation_zero_of_exponent_zero M (a :: x) 0 q _ (tailExponent_zero x a d))).trans
          (sub_zero _)
      rw [← htd]
      exact htcoeff _
  have himage : f (p d) ∈ sequenceIdeal (a :: x) • (⊤ : Submodule R Q) :=
    (Submodule.smul_top_le_comap_smul_top (sequenceIdeal (a :: x)) f) hfull
  rw [quotient_cons_smul M x a] at himage
  have hpd : p d = m d := by simp [p, Finsupp.single_apply, hds]
  rwa [hpd, show f (m d) = c d from hm d] at himage

/-- Separation transfers along an equivalence and to a smaller ideal. -/
lemma separated_of_equiv {N : Type*} [AddCommGroup N] [Module R N]
    (I J : Ideal R) (hIJ : I ≤ J) (e : M ≃ₗ[R] N)
    (hs : (⨅ n : ℕ, J ^ n • (⊤ : Submodule R M)) = ⊥) :
    (⨅ n : ℕ, I ^ n • (⊤ : Submodule R N)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro q hq
  have hqn : ∀ n : ℕ, q ∈ I ^ n • (⊤ : Submodule R N) := by
    simpa only [Submodule.mem_iInf] using hq
  have hm : e.symm q ∈ (⨅ n : ℕ, J ^ n • (⊤ : Submodule R M)) := by
    rw [Submodule.mem_iInf]
    intro n
    apply Submodule.smul_top_le_comap_smul_top (J ^ n) e.symm.toLinearMap
    exact Submodule.smul_mono_left (pow_le_pow_left' hIJ n)
      (hqn n)
  rw [hs, Submodule.mem_bot] at hm
  change q = 0
  exact e.symm.injective (hm.trans (map_zero e.symm).symm)

lemma prefixSeparated_quotient (a : R) (hs : PrefixSeparated M (a :: x)) :
    PrefixSeparated (QuotSMulTop a M) x := by
  intro j hj
  let e : (M ⧸ (Ideal.ofList ((a :: x).take (j + 1)) • ⊤ : Submodule R M)) ≃ₗ[R]
      (QuotSMulTop a M ⧸ (Ideal.ofList (x.take j) • ⊤ : Submodule R (QuotSMulTop a M))) :=
    (Submodule.quotEquivOfEq _ _ (by rw [List.take_succ_cons])) ≪≫ₗ
      Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a (x.take j)
  exact separated_of_equiv _ (sequenceIdeal x) (sequenceIdeal (a :: x))
    (tailIdeal_le_cons x a) e (hs (j + 1) (by simpa using hj))

lemma prefixSeparated_initial (a : R) (hs : PrefixSeparated M (a :: x)) :
    (⨅ n : ℕ, sequenceIdeal (a :: x) ^ n • (⊤ : Submodule R M)) = ⊥ := by
  let e : (M ⧸ (Ideal.ofList ((a :: x).take 0) • ⊤ : Submodule R M)) ≃ₗ[R] M :=
    Submodule.quotEquivOfEqBot _ (by simp)
  exact separated_of_equiv _ (sequenceIdeal (a :: x)) (sequenceIdeal (a :: x))
    le_rfl e (hs 0 (by simp))

/-- The tail is quasi-regular over the same base ring on M/aM. -/
lemma quasiRegular_quotient (a : R) (hq : GradedComparison.Core.QuasiRegular M (a :: x)) :
    GradedComparison.Core.QuasiRegular (QuotSMulTop a M) x := by
  refine ⟨⟨comparison_injective_of_coefficients _ x (quotient_coefficients M x a hq.1.1),
    GradedComparison.comparison_surjective _ x⟩, ?_⟩
  exact (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a x).toEquiv.nontrivial_congr.mp hq.2

/-- Quasi-regularity plus separation of the successive prefix quotients
implies proper regularity, with no finiteness or Noetherian assumptions. -/
theorem separated_converse (hq : GradedComparison.Core.QuasiRegular M x)
    (hs : PrefixSeparated M x) : RingTheory.Sequence.IsRegular M x := by
  induction x generalizing M with
  | nil =>
    have hn : Nontrivial M := (GradedComparison.quasiRegular_nil_iff M).mp hq
    exact RingTheory.Sequence.IsRegular.nil R M
  | cons a x ih =>
    apply (RingTheory.Sequence.isRegular_cons_iff M a x).mpr
    refine ⟨?_, ih (QuotSMulTop a M) (quasiRegular_quotient M x a hq)
      (prefixSeparated_quotient M x a hs)⟩
    exact generator_regular_of_separated M (a :: x) hq.1.1 0
      (prefixSeparated_initial M x a hs)

/-- Krull intersection provides exactly the successive separatedness needed
by RK-11 for a finite module over a Noetherian local ring. -/
lemma prefixSeparated_local [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] (hx : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) :
    PrefixSeparated M x := by
  intro j hj
  have hI : sequenceIdeal x ≤ (⊥ : Ideal R).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact Ideal.span_le.mpr hx
  exact Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (sequenceIdeal x) hI

/-- Over a Noetherian local ring, the four conditions of RK-11 and RK-08
are equivalent for a nonzero finite coefficient module. -/
theorem local_equivalences : Specs.local_equivalencesType := by
  intro R _ _ _ M _ _ _ _ x hx
  have hqr : GradedComparison.Core.QuasiRegular M x ↔ RingTheory.Sequence.IsRegular M x := by
    constructor
    · intro hq
      exact separated_converse M x hq (prefixSeparated_local M x hx)
    · intro hr
      refine ⟨AssociatedGraded.comparison_bijective M x hr.toIsWeaklyRegular, ?_⟩
      exact Submodule.Quotient.nontrivial_iff.mpr hr.top_ne_smul.symm
  obtain ⟨hra, haone⟩ := Koszul.local_regularity_equivalences M x hx
  exact ⟨hqr, hqr.trans hra, hqr.trans (hra.trans haone)⟩

end AdvCommAlg.RegularSequence.QuasiRegularConverse
