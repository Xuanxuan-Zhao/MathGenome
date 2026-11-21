import MathGenome.Internal.Specs.D07.Ch04.SemidirectRecognition
import MathGenome.Internal.D07.Ch04.SemidirectProduct
import MathGenome.Internal.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
import MathGenome.Internal.D07.Ch03.Lagrange
import MathGenome.Internal.D07.Ch03.SubgroupProductCounting
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Internal semidirect product recognition and the two boundary examples from
paper.tex:802–811. Conjugation is left conjugation. The finite obstruction
uses the unique quaternion involution; the matrix result transports it to
the original eight matrices. For S₃ we identify both cyclic factors with
ZMod and transport the conjugation action through these identifications.
-/

noncomputable section
namespace D07.Ch04.SemidirectRecognition
open Specs.D07.Ch04.SemidirectRecognition
open scoped Pointwise
universe u

def conjugationAction {G : Type u} [Group G] (N H : Subgroup G) [N.Normal] :
    H →* MulAut N :=
  N.normalizerMonoidHom.comp
    (Subgroup.inclusion (show H ≤ Subgroup.normalizer (N : Set G) from N.normalizer_eq_top ▸ le_top))

@[simp] theorem conjugationAction_apply {G : Type u} [Group G]
    (N H : Subgroup G) [N.Normal] (h : H) (n : N) :
    (conjugationAction N H h n : G) = (h : G) * n * (h : G)⁻¹ := rfl

theorem recognition : Recognition.{u} := by
  intro G _ N H _ hi hp
  have hc : N.IsComplement' H :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hi) hp
  exact ⟨conjugationAction N H, fun _ _ => rfl,
    _root_.SemidirectProduct.mulEquivSubgroup hc, fun _ => rfl⟩

lemma quaternion_card : Nat.card Q8 = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

lemma quaternionN_card : Nat.card quaternionN = 4 := by
  rw [quaternionN, Nat.card_zpowers]
  exact QuaternionGroup.orderOf_a_one

lemma quaternion_index : quaternionN.index = 2 := by
  have h := quaternionN.card_mul_index
  rw [quaternionN_card, quaternion_card] at h
  omega

lemma quaternion_normal : quaternionN.Normal :=
  Subgroup.normal_of_index_eq_two quaternion_index

lemma quaternion_minusOne_mem : minusOne ∈ quaternionN := by
  have h := Subgroup.pow_mem quaternionN (Subgroup.mem_zpowers qi) 2
  convert h using 1
  decide

lemma quaternion_squares (q : Q8) (h1 : q ≠ 1) (hm : q ≠ minusOne) :
    q ^ 2 = minusOne := by
  rcases q with t | t <;> fin_cases t <;> first | rfl | contradiction

lemma quaternion_involution (q : Q8) : (q ≠ 1 ∧ q ^ 2 = 1) ↔ q = minusOne := by
  rcases q with t | t <;> fin_cases t <;> decide

theorem quaternion_facts : QuaternionFacts :=
  ⟨quaternion_card, quaternionN_card, quaternion_index, quaternion_normal,
    quaternion_squares, quaternion_involution, quaternion_minusOne_mem⟩

theorem quaternion_complement_order : QuaternionComplementOrder := by
  intro H hc
  have h := hc.card_mul_card
  rw [quaternionN_card, quaternion_card] at h
  omega

/-- A complement of index two would supply a nontrivial involution outside N. -/
lemma no_complement_of_involutions {G : Type*} [Group G]
    (N : Subgroup G) (hi : N.index = 2)
    (hinv : ∀ g : G, g ^ 2 = 1 → g ∈ N) :
    ¬ ∃ H : Subgroup G, N.IsComplement' H := by
  rintro ⟨H, hc⟩
  have hcard : Nat.card H = 2 := hc.card_right.trans hi
  obtain ⟨x, hx, _⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hcard
  have hx2 : x ^ 2 = 1 := by
    simpa only [hcard] using (pow_card_eq_one' (x := x))
  have hmem : (x : G) ∈ N := hinv x (congrArg Subtype.val hx2)
  have heq : (x : G) = 1 := (Subgroup.disjoint_def.mp hc.disjoint) hmem x.property
  exact hx (Subtype.ext heq)

lemma quaternion_sq_one_mem (q : Q8) (hq : q ^ 2 = 1) : q ∈ quaternionN := by
  by_cases h1 : q = 1
  · exact h1 ▸ quaternionN.one_mem
  · rw [(quaternion_involution q).mp ⟨h1, hq⟩]
    exact quaternion_minusOne_mem

theorem quaternion_no_complement : QuaternionNoComplement :=
  no_complement_of_involutions quaternionN quaternion_index quaternion_sq_one_mem

theorem quaternion_nonsplit : QuaternionNonsplit := by
  intro hN
  let := hN
  have hcard : Nat.card (Q8 ⧸ quaternionN) = 2 := quaternion_index
  refine ⟨hcard, ?_⟩
  rintro ⟨s, hs⟩
  obtain ⟨q, hq, _⟩ := (Nat.card_eq_two_iff' (1 : Q8 ⧸ quaternionN)).mp hcard
  have hq2 : q ^ 2 = 1 := by simpa only [hcard] using (pow_card_eq_one' (x := q))
  have hs2 : (s q) ^ 2 = 1 := by rw [← map_pow, hq2, map_one]
  have hmem := quaternion_sq_one_mem (s q) hs2
  have he : (QuotientGroup.mk' quaternionN) (s q) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  have hsec := DFunLike.congr_fun hs q
  exact hq (hsec.symm.trans he)

/-- Transport the computed involution obstruction through any faithful model. -/
lemma quaternion_obstruction_transport {G : Type*} [Group G] (e : Q8 ≃* G) :
    (Subgroup.zpowers (e qi)).index = 2 ∧
    (Subgroup.zpowers (e qi)).Normal ∧
    ¬ ∃ H : Subgroup G, (Subgroup.zpowers (e qi)).IsComplement' H := by
  have hN : Subgroup.zpowers (e qi) = quaternionN.map e.toMonoidHom :=
    (MonoidHom.map_zpowers e.toMonoidHom qi).symm
  have hi : (Subgroup.zpowers (e qi)).index = 2 := by
    rw [hN]
    exact (Subgroup.index_map_of_bijective e.bijective quaternionN).trans quaternion_index
  refine ⟨hi, Subgroup.normal_of_index_eq_two hi, ?_⟩
  apply no_complement_of_involutions _ hi
  intro q hq
  have hpow : (e.symm q) ^ 2 = 1 := by rw [← map_pow, hq, map_one]
  rw [hN]
  exact ⟨e.symm q, quaternion_sq_one_mem _ hpow, e.apply_symm_apply q⟩

theorem quaternion_matrix_obstruction : QuaternionMatrixObstruction := by
  obtain ⟨M, hM, _, _, e, he⟩ :=
    D07.Ch01.DihedralQuaternionModelsQuaternionMatrices.quaternion_matrix_model
  exact ⟨M, hM, e, he, quaternion_obstruction_transport e⟩

lemma threeCycle_order : orderOf threeCycle = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide) (by decide)
lemma transposition_order : orderOf transposition = 2 := by
  exact orderOf_eq_prime (by decide) (by decide)

lemma s3N_card : Nat.card s3N = 3 := by
  rw [s3N, Nat.card_zpowers, threeCycle_order]

lemma s3H_card : Nat.card s3H = 2 := by
  rw [s3H, Nat.card_zpowers, transposition_order]

lemma s3_card : Nat.card S3 = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

lemma s3_index : s3N.index = 2 := by
  have h := s3N.card_mul_index
  rw [s3N_card, s3_card] at h
  omega

lemma s3_normal : s3N.Normal := Subgroup.normal_of_index_eq_two s3_index

lemma s3_complement : s3N.IsComplement' s3H := by
  apply Subgroup.isComplement'_of_coprime
  · rw [s3N_card, s3H_card, s3_card]
  · rw [s3N_card, s3H_card]; decide

lemma mem_s3N (q : S3) : q ∈ s3N ↔ q = 1 ∨ q = threeCycle ∨ q = threeCycle ^ 2 := by
  rw [s3N, mem_zpowers_iff_mem_range_orderOf, threeCycle_order]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩
    · exact ⟨2, by decide, rfl⟩

lemma s3_inversion (n : s3N) :
    transposition * (n : S3) * transposition⁻¹ = ((n : S3)⁻¹) := by
  rcases (mem_s3N n).mp n.property with h | h | h <;> rw [h] <;> decide

theorem symmetric_subgroups : SymmetricSubgroups :=
  ⟨threeCycle_order, transposition_order, s3_normal, s3_complement.disjoint.eq_bot,
    s3_complement.mul_eq, s3_inversion, by decide⟩

/-- The cyclic factor, with the specified generator corresponding to 1 mod n. -/
def cyclicFactorEquiv {G : Type*} [Group G] (g : G) (n : ℕ)
    (hn : Nat.card (Subgroup.zpowers g) = n) :
    Multiplicative (ZMod n) ≃* Subgroup.zpowers g :=
  zmodMulEquivOfGenerator (g := ⟨g, Subgroup.mem_zpowers g⟩)
    (by
      intro x
      obtain ⟨k, hk⟩ := x.property
      exact ⟨k, Subtype.ext hk⟩) hn

@[simp] lemma cyclicFactorEquiv_generator {G : Type*} [Group G] (g : G) (n : ℕ)
    (hn : Nat.card (Subgroup.zpowers g) = n) :
    cyclicFactorEquiv g n hn (Multiplicative.ofAdd 1) = ⟨g, Subgroup.mem_zpowers g⟩ :=
  zmodMulEquivOfGenerator_apply_ofAdd_one _ _

theorem symmetric_split : SymmetricSplit := by
  let : s3N.Normal := s3_normal
  let a := conjugationAction s3N s3H
  let eN : C3 ≃* s3N := cyclicFactorEquiv threeCycle 3 s3N_card
  let eH : C2 ≃* s3H := cyclicFactorEquiv transposition 2 s3H_card
  have heN : eN (Multiplicative.ofAdd 1) =
      ⟨threeCycle, Subgroup.mem_zpowers threeCycle⟩ := cyclicFactorEquiv_generator _ _ _
  have heH : eH (Multiplicative.ofAdd 1) =
      ⟨transposition, Subgroup.mem_zpowers transposition⟩ := cyclicFactorEquiv_generator _ _ _
  let φ : C2 →* MulAut C3 :=
    (MulAut.congr eN.symm).toMonoidHom.comp (a.comp eH.toMonoidHom)
  have hinv (n : C3) : φ (Multiplicative.ofAdd 1) n = n⁻¹ := by
    apply eN.injective
    change eN (eN.symm (a (eH (Multiplicative.ofAdd 1)) (eN n))) = eN n⁻¹
    rw [eN.apply_symm_apply, map_inv, heH]
    apply Subtype.ext
    exact s3_inversion (eN n)
  have hnontriv : φ (Multiplicative.ofAdd 1) ≠ 1 := by
    intro h
    have hh := hinv (Multiplicative.ofAdd 1)
    rw [h] at hh
    have hbad : (Multiplicative.ofAdd (1 : ZMod 3) : C3) ≠
        (Multiplicative.ofAdd (1 : ZMod 3) : C3)⁻¹ := by decide
    exact hbad hh
  let F : _root_.SemidirectProduct C3 C2 φ ≃*
      _root_.SemidirectProduct s3N s3H a :=
    (_root_.SemidirectProduct.congr' eN.symm eH.symm).symm
  let E : _root_.SemidirectProduct s3N s3H a ≃* S3 :=
    _root_.SemidirectProduct.mulEquivSubgroup s3_complement
  refine ⟨φ, hinv, hnontriv, F.trans E, ?_, ?_⟩
  · change ((eN (Multiplicative.ofAdd 1)) : S3) * ((eH 1) : S3) = threeCycle
    rw [heN, map_one]
    exact mul_one _
  · change ((eN 1) : S3) * ((eH (Multiplicative.ofAdd 1)) : S3) = transposition
    rw [heH, map_one]
    exact one_mul _

theorem symmetric_not_direct : SymmetricNotDirect := by
  rintro ⟨e⟩
  have h : e threeCycle * e transposition = e transposition * e threeCycle := mul_comm _ _
  have hne := symmetric_subgroups.2.2.2.2.2.2
  exact hne (e.injective (by simpa only [map_mul] using h))

end D07.Ch04.SemidirectRecognition
