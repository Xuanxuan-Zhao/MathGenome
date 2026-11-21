import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.PositiveMinMax
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.CompactNormalClassification
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Positive compact spectral ordering, attained Courant--Fischer formulas,
and injective reciprocal formulas on arbitrary real or complex Hilbert spaces.
The exact finite-rank tails and all admissible ambient dimensions are included. -/
noncomputable section
universe u v w
namespace ExpandedFA.CompactSpectral.PositiveMinMax
open Module
open scoped InnerProductSpace
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

lemma eigenvalue_positive (T : H →L[𝕜] H)
    (hp : T.IsPositive)
    (x : H) (hx : ‖x‖ = 1) (a : ℝ) (ha : a ≠ 0)
    (heig : T x = (a : 𝕜) • x) : 0 < a := by
  have h := hp.re_inner_nonneg_right x
  rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K, hx] at h
  simp only [one_pow, RCLike.ofReal_one, mul_one, RCLike.ofReal_re] at h
  exact lt_of_le_of_ne h (Ne.symm ha)

/-- Positivity removes the negative eigenvalues from the entire upstream family. -/
lemma positive_spectral_data (T : H →L[𝕜] H)
    (hp : T.IsPositive)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap) :
    ∃ (J : Type u) (_ : Countable J) (e : J → H) (a : J → ℝ),
      Orthonormal 𝕜 e ∧ (∀ j, 0 < a j) ∧
      (∀ j, T (e j) = (a j : 𝕜) • e j) ∧
      (∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • e j) (T x)) ∧
      (Submodule.span 𝕜 (Set.range e)).topologicalClosure = T.ker.orthogonal ∧
      (∀ ε : ℝ, 0 < ε → {j : J | ε ≤ a j}.Finite) := by
  obtain ⟨J, hJ, e, a, he, heig, hM, _, hs, _, hfin⟩ :=
    CompactNormalClassification.selfAdjoint_expansion 𝕜 H T hp.isSelfAdjoint hc
  have hpos : ∀ j, 0 < a j := fun j =>
    eigenvalue_positive T hp (e j) (he.norm_eq_one j) (a j) (heig j).1 (heig j).2
  refine ⟨J, hJ, e, a, he, hpos, fun j => (heig j).2,
    fun x => (hs x).2, hM, ?_⟩
  intro ε hε
  simpa only [abs_of_pos (hpos _)] using hfin ε hε


namespace Enumeration
variable {J : Type w} [LinearOrder J]
def predecessorCount (hf : ∀ j : J, (Set.Iio j).Finite) (j : J) : ℕ := (hf j).toFinset.card
lemma predecessorCount_strictMono (hf : ∀ j : J, (Set.Iio j).Finite) : StrictMono (predecessorCount hf) := by
  classical
  intro i j hij
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro k hk
    simp only [Set.Finite.mem_toFinset, Set.mem_Iio] at hk ⊢
    exact hk.trans hij
  · intro heq
    have hi : i ∈ (hf j).toFinset := by simpa using hij
    rw [← heq] at hi
    simp at hi
lemma predecessorCount_range_lower (hf : ∀ j : J, (Set.Iio j).Finite) :
    IsLowerSet (Set.range (predecessorCount hf)) := by
  classical
  rintro n m hmn ⟨j, rfl⟩
  rcases lt_or_eq_of_le hmn with hmn | rfl
  · let s := (hf j).toFinset
    let f := s.orderIsoOfFin rfl
    let k : Fin s.card := ⟨m, hmn⟩
    refine ⟨(f k : J), ?_⟩
    change ((hf (f k)).toFinset).card = m
    have hb : (hf (f k)).toFinset.card = (Finset.univ : Finset (Fin m)).card := by
      symm
      apply Finset.card_bij (fun i _ => (f ⟨i.val, i.isLt.trans k.isLt⟩ : J))
      · intro i _
        simp only [Set.Finite.mem_toFinset, Set.mem_Iio]
        exact f.strictMono (show (⟨i.val, i.isLt.trans k.isLt⟩ : Fin s.card) < k from i.isLt)
      · intro i _ l _ hil
        exact Fin.ext (congrArg (fun z : Fin s.card => z.val) (f.injective (Subtype.ext hil)))
      · intro y hy
        have hyk : y < (f k : J) := by simpa using hy
        have hyj : y < j := hyk.trans ((hf j).mem_toFinset.mp (f k).property)
        let z : s := ⟨y, by simpa [s] using hyj⟩
        have hz : f.symm z < k := by
          apply f.lt_iff_lt.mp
          rw [f.apply_symm_apply]
          exact hyk
        refine ⟨⟨(f.symm z).val, hz⟩, Finset.mem_univ _, ?_⟩
        change (f (f.symm z) : J) = y
        simp [z]
    simpa using hb
  · exact ⟨j, rfl⟩
end Enumeration

open Enumeration

/-- Finite positive threshold sets permit an exhaustive ordering, retaining ties. -/
lemma sorted_enumeration {J : Type w} [Countable J] (a : J → ℝ)
    (hp : ∀ j, 0 < a j) (hf : ∀ ε, 0 < ε → {j : J | ε ≤ a j}.Finite) :
    ∃ (I : Set ℕ) (b : I ≃ J), IsLowerSet I ∧ Antitone (a ∘ b) := by
  classical
  obtain ⟨code, hcode⟩ := Countable.exists_injective_nat J
  let f : J → ℝ ×ₗ ℕ := fun j => toLex (-a j, code j)
  have hfi : Function.Injective f := by
    intro i j hij
    apply hcode
    exact congrArg (fun z => (ofLex z).2) hij
  letI : LinearOrder J := LinearOrder.lift' f hfi
  have hpred : ∀ j : J, (Set.Iio j).Finite := by
    intro j
    apply (hf (a j) (hp j)).subset
    intro i hi
    change f i < f j at hi
    have hh := (Prod.Lex.toLex_lt_toLex.mp hi)
    rcases hh with hh | ⟨hh, _⟩
    · change -a i < -a j at hh
      change a j ≤ a i
      linarith
    · change -a i = -a j at hh
      change a j ≤ a i
      linarith
  let b := Equiv.ofInjective (predecessorCount hpred) (predecessorCount_strictMono hpred).injective
  refine ⟨Set.range (predecessorCount hpred), b.symm, predecessorCount_range_lower hpred, ?_⟩
  intro i j hij
  have hb : b.symm i ≤ b.symm j := (predecessorCount_strictMono hpred).le_iff_le.mp (by
    change predecessorCount hpred (b.symm i) ≤ predecessorCount hpred (b.symm j)
    change (b (b.symm i)).val ≤ (b (b.symm j)).val
    simpa only [Equiv.apply_symm_apply, Subtype.coe_le_coe] using hij)
  change f (b.symm i) ≤ f (b.symm j) at hb
  have hh := Prod.Lex.monotone_fst _ _ hb
  change -a (b.symm i) ≤ -a (b.symm j) at hh
  exact neg_le_neg_iff.mp hh


variable {J : Type w}

lemma eigenvectors_mem_range (T : H →L[𝕜] H) (e : J → H) (a : J → ℝ)
    (ha : ∀ i, a i ≠ 0) (heig : ∀ i, T (e i) = (a i : 𝕜) • e i) (i : J) :
    e i ∈ T.range := by
  refine ⟨(a i : 𝕜)⁻¹ • e i, ?_⟩
  change T ((a i : 𝕜)⁻¹ • e i) = e i
  rw [map_smul, heig i, smul_smul, inv_mul_cancel₀ (by simpa using ha i), one_smul]

lemma range_eq_span_of_finite [Finite J] (T : H →L[𝕜] H) (e : J → H) (a : J → ℝ)
    (ha : ∀ i, a i ≠ 0) (heig : ∀ i, T (e i) = (a i : 𝕜) • e i)
    (hs : ∀ x, HasSum (fun i => ((a i : 𝕜) * inner 𝕜 (e i) x) • e i) (T x)) :
    T.range = Submodule.span 𝕜 (Set.range e) := by
  let M := Submodule.span 𝕜 (Set.range e)
  have : FiniteDimensional 𝕜 M := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range e)
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    apply M.closed_of_finiteDimensional.mem_of_tendsto (hs x)
    exact Filter.Eventually.of_forall (fun F => Submodule.sum_mem M (fun i _ =>
      M.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)))
  · apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact eigenvectors_mem_range T e a ha heig i

lemma finite_index_of_finite_range (T : H →L[𝕜] H) (e : J → H) (a : J → ℝ)
    (he : Orthonormal 𝕜 e) (ha : ∀ i, a i ≠ 0)
    (heig : ∀ i, T (e i) = (a i : 𝕜) • e i) [FiniteDimensional 𝕜 T.range] :
    Finite J := by
  let er : J → T.range := fun i => ⟨e i, eigenvectors_mem_range T e a ha heig i⟩
  have her : Orthonormal 𝕜 er := (T.range.subtypeₗᵢ.orthonormal_comp_iff).mp he
  exact her.linearIndependent.finite

lemma finite_rank_iff_length {I : Set ℕ} (hI : IsLowerSet I)
    (T : H →L[𝕜] H) (e : I → H) (a : I → ℝ)
    (he : Orthonormal 𝕜 e) (ha : ∀ i, a i ≠ 0)
    (heig : ∀ i, T (e i) = (a i : 𝕜) • e i)
    (hs : ∀ x, HasSum (fun i => ((a i : 𝕜) * inner 𝕜 (e i) x) • e i) (T x)) :
    ∀ r : ℕ, (FiniteDimensional 𝕜 T.range ∧ finrank 𝕜 T.range = r) ↔ I = Set.Iio r := by
  have hlength (n : ℕ) (hIn : I = Set.Iio n) :
      FiniteDimensional 𝕜 T.range ∧ finrank 𝕜 T.range = n := by
    have hIfin : I.Finite := hIn ▸ Set.finite_Iio n
    letI : Finite I := hIfin.to_subtype
    letI : Fintype I := Fintype.ofFinite I
    have hR := range_eq_span_of_finite T e a ha heig hs
    have hfd : FiniteDimensional 𝕜 T.range := by
      rw [hR]
      exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range e)
    refine ⟨hfd, ?_⟩
    rw [hR, finrank_span_eq_card he.linearIndependent]
    have ec : I ≃ Fin n :=
      { toFun := fun i => ⟨i.val, by simpa [hIn] using i.property⟩
        invFun := fun i => ⟨i.val, by simpa [hIn] using i.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa using Fintype.card_congr ec
  intro r
  constructor
  · rintro ⟨hfd, hr⟩
    letI := hfd
    letI : Finite I := finite_index_of_finite_range T e a he ha heig
    rcases hI.eq_univ_or_Iio with hU | ⟨n, hIn⟩
    · have hIfin : I.Finite := Set.toFinite I
      rw [hU] at hIfin
      exact (Set.infinite_univ hIfin).elim
    · have hn := (hlength n hIn).2
      have : n = r := hn.symm.trans hr
      simpa [this] using hIn
  · exact hlength r

end ExpandedFA.CompactSpectral.PositiveMinMax

namespace ExpandedFA.CompactSpectral.PositiveMinMax
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A complete positive expansion covers each eigenspace with precisely the
vectors carrying that eigenvalue. This verifies the multiplicity interpretation
without choosing a basis for the kernel. -/
lemma positive_eigenspace_eq_span {J : Type w} (T : H →L[𝕜] H) (hp : T.IsPositive)
    (e : J → H) (a : J → ℝ)
    (heig : ∀ j, T (e j) = (a j : 𝕜) • e j)
    (hs : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • e j) (T x))
    (hfin : ∀ ε : ℝ, 0 < ε → {j : J | ε ≤ a j}.Finite)
    (μ : ℝ) (hμ : 0 < μ) :
    Module.End.eigenspace T.toLinearMap (μ : 𝕜) =
      Submodule.span 𝕜 (e '' {j | a j = μ}) := by
  classical
  have hfiber : {j : J | a j = μ}.Finite :=
    (hfin μ hμ).subset (fun j hj => hj.ge)
  let F := hfiber.toFinset
  apply le_antisymm
  · intro x hx
    have hTx : T x = (μ : 𝕜) • x := Module.End.mem_eigenspace_iff.mp hx
    have hcoef (j : J) (hj : a j ≠ μ) : inner 𝕜 (e j) x = 0 := by
      have hc := hp.isSymmetric (e j) x
      change inner 𝕜 (T (e j)) x = inner 𝕜 (e j) (T x) at hc
      rw [heig j, hTx, inner_smul_left, inner_smul_right] at hc
      simp only [RCLike.conj_ofReal] at hc
      by_contra hz
      have heq : (a j : 𝕜) = (μ : 𝕜) := mul_right_cancel₀ hz hc
      exact hj (RCLike.ofReal_injective heq)
    have hsum : HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • e j)
        (∑ j ∈ F, ((a j : 𝕜) * inner 𝕜 (e j) x) • e j) := by
      apply hasSum_sum_of_ne_finset_zero
      intro j hj
      have hj' : a j ≠ μ := by simpa [F] using hj
      simp [hcoef j hj']
    have hmem : T x ∈ Submodule.span 𝕜 (e '' {j | a j = μ}) := by
      rw [(hs x).unique hsum]
      apply Submodule.sum_mem
      intro j hj
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨j, hfiber.mem_toFinset.mp hj, rfl⟩
    have hμK : (μ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (ne_of_gt hμ)
    have hid : (μ : 𝕜)⁻¹ • T x = x := by rw [hTx, smul_smul, inv_mul_cancel₀ hμK, one_smul]
    rw [← hid]
    exact Submodule.smul_mem _ _ hmem
  · apply Submodule.span_le.mpr
    rintro y ⟨j, hj, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change T (e j) = (μ : 𝕜) • e j
    rw [heig j, show a j = μ from hj]

/-- The ordered positive compact spectral system, including exact finite rank,
empty systems and an arbitrary ambient kernel. -/
theorem ordered_positive_spectrum :
    Spec.OrderedPositiveSpectrum.{u, v} := by
  intro 𝕜 H _ _ _ _ T hp hc
  obtain ⟨J, hJ, e, a, he, ha, heig, hs, hM, hf⟩ := positive_spectral_data T hp hc
  letI : Countable J := hJ
  obtain ⟨I, b, hI, hb⟩ := sorted_enumeration a ha hf
  have he' := he.comp b b.injective
  have heig' : ∀ i : I, T ((e ∘ b) i) = ((a ∘ b) i : 𝕜) • (e ∘ b) i :=
    fun i => heig (b i)
  have hs' : ∀ x, HasSum (fun i : I => (((a ∘ b) i : 𝕜) * inner 𝕜 ((e ∘ b) i) x) •
      (e ∘ b) i) (T x) := by
    intro x
    exact b.hasSum_iff.mpr (hs x)
  refine ⟨I, e ∘ b, a ∘ b, hI, he', fun i => ha (b i), hb, heig', hs', ?_, ?_, ?_, ?_⟩
  · have hr : Set.range (e ∘ b) = Set.range e := by
      rw [Set.range_comp, b.surjective.range_eq, Set.image_univ]
    simpa only [hr] using hM
  · intro ε hε
    exact Set.Finite.preimage (f := b) b.injective.injOn (hf ε hε)
  · exact finite_rank_iff_length hI T (e ∘ b) (a ∘ b) he'
      (fun i => (ha (b i)).ne') heig' hs'
  · intro μ hμ
    exact positive_eigenspace_eq_span T hp (e ∘ b) (a ∘ b) heig' hs'
      (fun ε hε => Set.Finite.preimage (f := b) b.injective.injOn (hf ε hε)) μ hμ


open Spec Module Filter
open scoped Topology ComplexConjugate
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Rank--nullity for the projection M → L, followed by normalization.
Only L and M, rather than the ambient space, are finite dimensional. -/
lemma unit_mem_inter_orthogonal (L M : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 L] [FiniteDimensional 𝕜 M]
    (hd : finrank 𝕜 L < finrank 𝕜 M) :
    ∃ x ∈ M, x ∈ L.orthogonal ∧ ‖x‖ = 1 := by
  let f : M →ₗ[𝕜] L := L.orthogonalProjectionOnto.toLinearMap.comp M.subtype
  have hni : ¬ Function.Injective f := by
    intro h
    have := LinearMap.finrank_le_finrank_of_injective h
    omega
  have hk : f.ker ≠ ⊥ := fun h => hni (LinearMap.ker_eq_bot.mp h)
  obtain ⟨z, hz, hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hz0 : (z : H) ≠ 0 := by simpa using hzne
  have hperp : (z : H) ∈ L.orthogonal := by
    apply L.orthogonalProjectionOnto_eq_zero_iff.mp
    exact hz
  refine ⟨(‖(z : H)‖⁻¹ : 𝕜) • (z : H), M.smul_mem _ z.property,
    L.orthogonal.smul_mem _ hperp, ?_⟩
  simp [norm_smul, norm_ne_zero_iff.mpr hz0]

lemma finrank_span_fin {m : ℕ} (f : Fin m → H) (hf : LinearIndependent 𝕜 f) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range f)) = m := by
  simpa using finrank_span_eq_card hf

lemma trialSpace_exists {n : ℕ} (hn : Admissible 𝕜 H n) :
    ∃ L : Submodule 𝕜 H, TrialSpace L n := by
  obtain ⟨v, hv⟩ := hn
  let f : Fin n → H := fun i => v i.castSucc
  have hf : LinearIndependent 𝕜 f := hv.comp _ (Fin.castSucc_injective n)
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range f)
  exact ⟨Submodule.span 𝕜 (Set.range f), inferInstance, finrank_span_fin f hf⟩

lemma unit_mem_orthogonal {n : ℕ} (hn : Admissible 𝕜 H n)
    (L : Submodule 𝕜 H) (hL : TrialSpace L n) :
    ∃ x ∈ L.orthogonal, ‖x‖ = 1 := by
  obtain ⟨v, hv⟩ := hn
  let M := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 M := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have : FiniteDimensional 𝕜 L := hL.1
  obtain ⟨x, _, hx, hnorm⟩ := unit_mem_inter_orthogonal L M
    (by rw [hL.2, finrank_span_fin v hv]; omega)
  exact ⟨x, hx, hnorm⟩

lemma orthonormal_norm_sq_sum (e : J → H) (he : Orthonormal 𝕜 e)
    (c : J → 𝕜) (F : Finset J) :
    ‖∑ j ∈ F, c j • e j‖ ^ 2 = ∑ j ∈ F, ‖c j‖ ^ 2 := by
  have h : (((‖∑ j ∈ F, c j • e j‖ : ℝ) : 𝕜) ^ 2) =
      ∑ j ∈ F, ((‖c j‖ : ℝ) : 𝕜) ^ 2 := by
    rw [← inner_self_eq_norm_sq_to_K, he.inner_sum]
    simp only [RCLike.conj_mul]
  exact_mod_cast h

/-- A diagonal quadratic form on a finite spectral span is bounded below
by the smallest displayed diagonal entry times the squared norm. -/
lemma quadratic_ge_on_span {ι : Type*} [Fintype ι]
    (T : H →L[𝕜] H) (e : ι → H) (he : Orthonormal 𝕜 e) (a : ι → ℝ)
    (heig : ∀ i, T (e i) = (a i : 𝕜) • e i) (c : ℝ) (hc : ∀ i, c ≤ a i)
    (x : H) (hx : x ∈ Submodule.span 𝕜 (Set.range e)) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 x (T x)) := by
  classical
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hx
  have hTsum : T (∑ i, b i • e i) = ∑ i, ((a i : 𝕜) * b i) • e i := by
    simp [map_sum, map_smul, heig, smul_smul, mul_comm]
  rw [hTsum]
  have hinner := he.inner_sum b (fun i => (a i : 𝕜) * b i) Finset.univ
  rw [hinner, map_sum]
  have hnorm := orthonormal_norm_sq_sum e he b Finset.univ
  rw [hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hid : conj (b i) * ((a i : 𝕜) * b i) =
      (a i : 𝕜) * (conj (b i) * b i) := by ring
  rw [hid, RCLike.conj_mul]
  simp only [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  exact mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)

/-- The pointwise tail norm bound uses Bessel, allowing the forbidden
coefficients to vanish instead of bounding their diagonal entries. -/
lemma norm_image_le_of_coefficients {J : Type*}
    (T : H →L[𝕜] H) (e : J → H) (he : Orthonormal 𝕜 e) (a : J → 𝕜)
    (hs : ∀ x, HasSum (fun i => (a i * inner 𝕜 (e i) x) • e i) (T x))
    (x : H) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i * inner 𝕜 (e i) x‖ ≤ C * ‖inner 𝕜 (e i) x‖) :
    ‖T x‖ ≤ C * ‖x‖ := by
  apply le_of_tendsto (hs x).norm
  apply Eventually.of_forall
  intro F
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [orthonormal_norm_sq_sum e he, mul_pow]
  calc
    ∑ i ∈ F, ‖a i * inner 𝕜 (e i) x‖ ^ 2 ≤
        ∑ i ∈ F, (C * ‖inner 𝕜 (e i) x‖) ^ 2 := by
      exact Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (ha i) 2
    _ = C ^ 2 * ∑ i ∈ F, ‖inner 𝕜 (e i) x‖ ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ C ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (he.sum_inner_products_le x) (sq_nonneg _)

/-- Extend a finite-dimensional subspace to any admissible finite trial
dimension, without assigning native finrank to the ambient space. -/
lemma extend_trialSpace {n : ℕ} (hn : Admissible 𝕜 H n)
    (M : Submodule 𝕜 H) [FiniteDimensional 𝕜 M] (hM : finrank 𝕜 M ≤ n) :
    ∃ L : Submodule 𝕜 H, M ≤ L ∧ TrialSpace L n := by
  suffices ∀ k, k ≤ n → ∀ (N : Submodule 𝕜 H), TrialSpace N k →
      ∃ L : Submodule 𝕜 H, N ≤ L ∧ TrialSpace L n by
    exact this _ hM M ⟨inferInstance, rfl⟩
  intro k hk
  induction hk using Nat.decreasingInduction with
  | self =>
      intro N hN
      exact ⟨N, le_rfl, hN⟩
  | of_succ k hk ih =>
      intro N hN
      have : FiniteDimensional 𝕜 N := hN.1
      obtain ⟨v, hv⟩ := hn
      let W := Submodule.span 𝕜 (Set.range v)
      have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
      obtain ⟨x, _, hx, hnorm⟩ := unit_mem_inter_orthogonal N W
        (by rw [hN.2, finrank_span_fin v hv]; omega)
      have hxN : x ∉ N := by
        intro hxN
        have hz : x = 0 := (inner_self_eq_zero.mp ((N.mem_orthogonal x).mp hx x hxN))
        simp [hz] at hnorm
      let S := Submodule.span 𝕜 ({x} : Set H)
      have hdis : Disjoint N S := Submodule.disjoint_span_singleton_of_notMem hxN
      have hfin : finrank 𝕜 (N ⊔ S : Submodule 𝕜 H) = k+1 := by
        have hd := N.finrank_sup_add_finrank_inf_eq S
        rw [hdis.eq_bot, finrank_bot, add_zero, hN.2,
          finrank_span_singleton (by intro h; simp [h] at hnorm)] at hd
        exact hd
      obtain ⟨L, hL, hLn⟩ := ih (N ⊔ S) ⟨inferInstance, hfin⟩
      exact ⟨L, le_trans le_sup_left hL, hLn⟩

/-- The first m indices of a lower list containing n, for m ≤ n+1. -/
def prefixIndex {I : Set ℕ} (hI : IsLowerSet I) {n : ℕ} (hn : n ∈ I)
    (m : ℕ) (hm : m ≤ n+1) (i : Fin m) : I :=
  ⟨i, hI (show (i : ℕ) ≤ n by omega) hn⟩

lemma prefixIndex_injective {I : Set ℕ} (hI : IsLowerSet I) {n : ℕ} (hn : n ∈ I)
    (m : ℕ) (hm : m ≤ n+1) : Function.Injective (prefixIndex hI hn m hm) := by
  intro i j h
  exact Fin.ext (congrArg Subtype.val h)

lemma aboveDimension_of_entry {I : Set ℕ} (hI : IsLowerSet I)
    (e : I → H) (he : Orthonormal 𝕜 e) (n : ℕ) (hn : n ∈ I) :
    Admissible 𝕜 H n :=
  ⟨e ∘ prefixIndex hI hn (n+1) le_rfl,
    (he.comp _ (prefixIndex_injective hI hn (n+1) le_rfl)).linearIndependent⟩


lemma rayleigh_eq_native (T : H →L[𝕜] H) (x : H) :
    rayleigh T x = T.rayleighQuotient x := by
  simp only [rayleigh, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]

lemma rayleigh_nonneg (T : H →L[𝕜] H) (hT : T.IsPositive) (x : H) :
    0 ≤ rayleigh T x := div_nonneg (hT.re_inner_nonneg_right x) (sq_nonneg _)

lemma rayleigh_le_norm (T : H →L[𝕜] H) (x : H) : rayleigh T x ≤ ‖T‖ := by
  rw [rayleigh_eq_native]
  exact (le_abs_self _).trans (T.rayleighQuotient_le_norm x)

lemma rayleighValues_eq_unitValues (T : H →L[𝕜] H) (L : Submodule 𝕜 H) :
    rayleighValues T L = unitValues T L := by
  ext t
  constructor
  · rintro ⟨x, hx, hx0, rfl⟩
    let y : H := (‖x‖⁻¹ : 𝕜) • x
    have hyn : ‖y‖ = 1 := by simp [y, norm_smul, norm_ne_zero_iff.mpr hx0]
    refine ⟨y, L.smul_mem _ hx, hyn, ?_⟩
    have heq : rayleigh T y = rayleigh T x := by
      simp only [rayleigh_eq_native, y]
      exact T.rayleigh_smul x (by simpa using hx0)
    simpa only [rayleigh, hyn, one_pow, div_one] using heq
  · rintro ⟨x, hx, hnorm, rfl⟩
    exact ⟨x, hx, by intro h; simp [h] at hnorm, by simp [rayleigh, hnorm]⟩

lemma rayleighValues_bounds (T : H →L[𝕜] H) (hT : T.IsPositive)
    (L : Submodule 𝕜 H) :
    BddBelow (rayleighValues T L) ∧ BddAbove (rayleighValues T L) := by
  constructor
  · exact ⟨0, by rintro _ ⟨x, _, _, rfl⟩; exact rayleigh_nonneg T hT x⟩
  · exact ⟨‖T‖, by rintro _ ⟨x, _, _, rfl⟩; exact rayleigh_le_norm T x⟩

lemma trialSpace_unit {k : ℕ} (L : Submodule 𝕜 H) (hL : TrialSpace L k)
    (hk : 0 < k) : ∃ x ∈ L, ‖x‖ = 1 := by
  letI := hL.1
  have hne : L ≠ ⊥ := by
    intro h
    have hz := hL.2
    rw [h, finrank_bot] at hz
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨(‖x‖⁻¹ : 𝕜) • x, L.smul_mem _ hx,
    by simp [norm_smul, norm_ne_zero_iff.mpr hx0]⟩

lemma finite_trial_minimum (T : H →L[𝕜] H) {k : ℕ}
    (L : Submodule 𝕜 H) (hL : TrialSpace L k) (hk : 0 < k) :
    ∃ r, IsLeast (rayleighValues T L) r := by
  letI : FiniteDimensional 𝕜 L := hL.1
  obtain ⟨x, hx, hxnorm⟩ := trialSpace_unit L hL hk
  have hne : (Metric.sphere (0 : L) 1).Nonempty :=
    ⟨⟨x, hx⟩, by simpa using hxnorm⟩
  have hc : Continuous (fun x : L => RCLike.re (inner 𝕜 (x : H) (T x))) :=
    RCLike.continuous_re.comp (continuous_subtype_val.inner (T.continuous.comp continuous_subtype_val))
  obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : L) 1).exists_isMinOn hne hc.continuousOn
  refine ⟨RCLike.re (inner 𝕜 (y : H) (T y)), ?_⟩
  rw [rayleighValues_eq_unitValues]
  refine ⟨⟨y, y.property, by simpa using hy, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, hznorm, rfl⟩
  exact hmin (by simpa using hznorm : (⟨z, hz⟩ : L) ∈ Metric.sphere (0 : L) 1)

/-- Finite-dimensional lower and upper spectral subspaces, with a common
nonzero vector attaining the boundary value. -/
def SpectralSandwich (T : H →L[𝕜] H) (n : ℕ) (μ : ℝ) : Prop :=
  ∃ L M : Submodule 𝕜 H, TrialSpace L (n+1) ∧ TrialSpace M n ∧
    (∀ x ∈ L, x ≠ 0 → μ ≤ rayleigh T x) ∧
    (∀ x ∈ M.orthogonal, x ≠ 0 → rayleigh T x ≤ μ) ∧
    ∃ x ∈ L, x ∈ M.orthogonal ∧ x ≠ 0 ∧ rayleigh T x = μ

lemma rayleigh_eigenvector (T : H →L[𝕜] H) (a : ℝ) (x : H)
    (hx : x ≠ 0) (heig : T x = (a : 𝕜) • x) : rayleigh T x = a := by
  rw [rayleigh, heig, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  exact mul_div_cancel_right₀ a (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

lemma courantFischer_of_sandwich (T : H →L[𝕜] H) (hp : T.IsPositive)
    (n : ℕ) (μ : ℝ) (hs : SpectralSandwich T n μ) : CourantFischerAt T n μ := by
  obtain ⟨L, M, hL, hM, hlow, hupp, z, hzL, hzM, hz0, hz⟩ := hs
  have bds := rayleighValues_bounds T hp
  have neL (K : Submodule 𝕜 H) (hK : TrialSpace K (n+1)) :
      (rayleighValues T K).Nonempty := by
    obtain ⟨x, hx, hn⟩ := trialSpace_unit K hK (by omega)
    exact ⟨_, x, hx, by intro h; simp [h] at hn, rfl⟩
  have neM (K : Submodule 𝕜 H) (hK : TrialSpace K n) :
      (rayleighValues T K.orthogonal).Nonempty := by
    letI := hL.1
    letI := hK.1
    obtain ⟨x, _, hx, hn⟩ := unit_mem_inter_orthogonal K L (by rw [hL.2, hK.2]; omega)
    exact ⟨_, x, hx, by intro h; simp [h] at hn, rfl⟩
  have hLval : sInf (rayleighValues T L) = μ := by
    apply le_antisymm
    · exact (csInf_le (bds L).1 ⟨z, hzL, hz0, rfl⟩).trans_eq hz
    · apply le_csInf (neL L hL)
      rintro _ ⟨x, hx, hx0, rfl⟩
      exact hlow x hx hx0
  have hMval : sSup (rayleighValues T M.orthogonal) = μ := by
    apply le_antisymm
    · apply csSup_le (neM M hM)
      rintro _ ⟨x, hx, hx0, rfl⟩
      exact hupp x hx hx0
    · exact hz ▸ le_csSup (bds M.orthogonal).2 ⟨z, hzM, hz0, rfl⟩
  refine ⟨?_, ?_, ⟨⟨L, hL, hLval⟩, ?_⟩, ⟨⟨M, hM, hMval⟩, ?_⟩⟩
  · intro K hK
    exact ⟨neL K hK, (bds K).1, finite_trial_minimum T K hK (by omega)⟩
  · intro K hK
    exact ⟨neM K hK, (bds K.orthogonal).2⟩
  · rintro _ ⟨K, hK, rfl⟩
    letI := hK.1
    letI := hM.1
    obtain ⟨x, hxK, hxM, hn⟩ := unit_mem_inter_orthogonal M K (by rw [hM.2, hK.2]; omega)
    have hx0 : x ≠ 0 := by intro h; simp [h] at hn
    exact (csInf_le (bds K).1 ⟨x, hxK, hx0, rfl⟩).trans (hupp x hxM hx0)
  · rintro _ ⟨K, hK, rfl⟩
    letI := hK.1
    letI := hL.1
    obtain ⟨x, hxL, hxK, hn⟩ := unit_mem_inter_orthogonal K L (by rw [hL.2, hK.2]; omega)
    have hx0 : x ≠ 0 := by intro h; simp [h] at hn
    exact (hlow x hxL hx0).trans (le_csSup (bds K.orthogonal).2 ⟨x, hxK, hx0, rfl⟩)

lemma spectral_sandwich (T : H →L[𝕜] H) (hp : T.IsPositive)
    (I : Set ℕ) (e : I → H) (a : I → ℝ) (hd : PositiveSpectralList T I e a)
    (n : ℕ) (hn : Admissible 𝕜 H n) : SpectralSandwich T n (paddedValue I a n) := by
  classical
  obtain ⟨hI, he, hpos, hanti, heig, hs, hspan, hfin, hrank⟩ := hd
  by_cases hni : n ∈ I
  · simp only [paddedValue, dif_pos hni]
    let f : Fin n → I := prefixIndex hI hni n (by omega)
    let g : Fin (n+1) → I := prefixIndex hI hni (n+1) le_rfl
    have hf := prefixIndex_injective hI hni n (by omega)
    have hg := prefixIndex_injective hI hni (n+1) le_rfl
    let M := Submodule.span 𝕜 (Set.range (e ∘ f))
    let L := Submodule.span 𝕜 (Set.range (e ∘ g))
    have hL : TrialSpace L (n+1) :=
      ⟨FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _),
        finrank_span_fin _ (he.comp g hg).linearIndependent⟩
    have hM : TrialSpace M n :=
      ⟨FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _),
        finrank_span_fin _ (he.comp f hf).linearIndependent⟩
    refine ⟨L, M, hL, hM, ?_, ?_, e ⟨n, hni⟩, ?_, ?_, he.ne_zero _, ?_⟩
    · intro x hx hx0
      apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mpr
      exact quadratic_ge_on_span T (e ∘ g) (he.comp g hg) (a ∘ g)
        (fun i => heig (g i)) _
        (fun i => hanti (show g i ≤ (⟨n, hni⟩ : I) by exact Nat.le_of_lt_succ i.isLt)) x hx
    · intro x hx hx0
      have hb : ‖T x‖ ≤ a ⟨n, hni⟩ * ‖x‖ := by
        apply norm_image_le_of_coefficients T e he (fun i => (a i : 𝕜)) hs x _
          (hpos ⟨n, hni⟩).le
        intro i
        by_cases hi : (i : ℕ) < n
        · have hm : e i ∈ M := Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
          have hz := (M.mem_orthogonal x).mp hx (e i) hm
          simp [hz]
        · rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (hpos i)]
          exact mul_le_mul_of_nonneg_right (hanti (show (⟨n, hni⟩ : I) ≤ i from
            Nat.le_of_not_gt hi)) (norm_nonneg _)
      apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mpr
      calc
        RCLike.re (inner 𝕜 x (T x)) ≤ ‖inner 𝕜 x (T x)‖ := RCLike.re_le_norm _
        _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (a ⟨n, hni⟩ * ‖x‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = a ⟨n, hni⟩ * ‖x‖ ^ 2 := by ring
    · exact Submodule.subset_span ⟨⟨n, by omega⟩, rfl⟩
    · apply (CompactNormalClassification.orthogonal_span_range_iff (e ∘ f) _).mpr
      intro i
      exact he.inner_eq_zero (by
        intro hi
        have := congrArg Subtype.val hi
        change (i : ℕ) = n at this
        omega)
    · exact rayleigh_eigenvector T _ _ (he.ne_zero _) (heig _)
  · simp only [paddedValue, dif_neg hni]
    have hsubset : I ⊆ Set.Iio n := by
      intro i hi
      by_contra hh
      exact hni (hI (Nat.le_of_not_gt hh) hi)
    have hIfin : I.Finite := (Set.finite_Iio n).subset hsubset
    obtain ⟨r, hIr⟩ : ∃ r, I = Set.Iio r := by
      rcases hI.eq_univ_or_Iio with hh | hh
      · exact (Set.infinite_univ (hh ▸ hIfin)).elim
      · exact hh
    have hrn : r ≤ n := by
      by_contra hh
      exact hni (by rw [hIr]; exact Nat.lt_of_not_ge hh)
    let f : Fin r → I := fun i => ⟨i, by rw [hIr]; exact i.isLt⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Fin.ext (congrArg Subtype.val hij)
    let V := Submodule.span 𝕜 (Set.range (e ∘ f))
    letI : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
    obtain ⟨M, hVM, hM⟩ := extend_trialSpace hn V (by
      rw [finrank_span_fin _ (he.comp f hf).linearIndependent]; exact hrn)
    obtain ⟨v, hv⟩ := hn
    let L := Submodule.span 𝕜 (Set.range v)
    have hL : TrialSpace L (n+1) :=
      ⟨FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _), finrank_span_fin v hv⟩
    have hzero : ∀ x ∈ M.orthogonal, T x = 0 := by
      intro x hx
      have hc : ∀ i, inner 𝕜 (e i) x = 0 := by
        intro i
        have hi : (i : ℕ) < r := by simpa [hIr] using i.property
        exact (M.mem_orthogonal x).mp hx (e i)
          (hVM (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩))
      have hsum : HasSum (fun _ : I => (0 : H)) (T x) := by
        simpa only [hc, mul_zero, zero_smul] using hs x
      exact hsum.unique hasSum_zero
    letI := hL.1
    letI := hM.1
    obtain ⟨z, hzL, hzM, hz1⟩ := unit_mem_inter_orthogonal M L (by rw [hM.2, hL.2]; omega)
    refine ⟨L, M, hL, hM, fun x _ _ => rayleigh_nonneg T hp x, ?_, z, hzL, hzM, ?_, ?_⟩
    · intro x hx _
      simp [rayleigh, hzero x hx]
    · intro h
      simp [h] at hz1
    · simp [rayleigh, hzero z hzM]

lemma rayleigh_pos_of_expansion (T : H →L[𝕜] H) (hp : T.IsPositive)
    {I : Type*} (e : I → H) (a : I → ℝ) (hpos : ∀ i, 0 < a i)
    (hs : ∀ x, HasSum (fun i => ((a i : 𝕜) * inner 𝕜 (e i) x) • e i) (T x))
    (hinj : Function.Injective T) (x : H) (hx : x ≠ 0) : 0 < rayleigh T x := by
  classical
  have hq : 0 < RCLike.re (inner 𝕜 x (T x)) := by
    by_contra hh
    have hzero : RCLike.re (inner 𝕜 x (T x)) = 0 :=
      le_antisymm (le_of_not_gt hh) (hp.re_inner_nonneg_right x)
    have hsum : HasSum (fun i => a i * ‖inner 𝕜 (e i) x‖ ^ 2)
        (RCLike.re (inner 𝕜 x (T x))) := by
      have ht := RCLike.reCLM.hasSum ((innerSL 𝕜 x).hasSum (hs x))
      convert ht using 1
      · ext i
        simp only [innerSL_apply_apply, RCLike.reCLM_apply, inner_smul_right]
        have hconj : inner 𝕜 x (e i) = conj (inner 𝕜 (e i) x) := by rw [inner_conj_symm]
        rw [hconj, mul_assoc, RCLike.mul_conj]
        simp only [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
      · rfl
    have hcoef (i : I) : inner 𝕜 (e i) x = 0 := by
      have hle : a i * ‖inner 𝕜 (e i) x‖ ^ 2 ≤ 0 := by
        rw [← hzero]
        simpa using sum_le_hasSum ({i} : Finset I)
          (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _)) hsum
      have hz : ‖inner 𝕜 (e i) x‖ ^ 2 = 0 := by
        nlinarith [hpos i, sq_nonneg ‖inner 𝕜 (e i) x‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    have ht : T x = 0 := by
      have ht : HasSum (fun _ : I => (0 : H)) (T x) := by
        simpa only [hcoef, mul_zero, zero_smul] using hs x
      exact ht.unique hasSum_zero
    exact hx (hinj (ht.trans T.map_zero.symm))
  exact div_pos hq (sq_pos_of_pos (norm_pos_iff.mpr hx))

lemma unit_mem_inter_codimension (L W : Submodule 𝕜 H) {n : ℕ}
    (hL : TrialSpace L (n+1)) (hW : ClosedCodimension W n) :
    ∃ x ∈ L, x ∈ W ∧ ‖x‖ = 1 := by
  letI := hL.1
  letI := hW.2.1
  let f : L →ₗ[𝕜] (H ⧸ W) := W.mkQ.comp L.subtype
  have hni : ¬Function.Injective f := by
    intro hi
    have hh := LinearMap.finrank_le_finrank_of_injective hi
    rw [hL.2, hW.2.2] at hh
    omega
  have hk : f.ker ≠ ⊥ := fun h => hni (LinearMap.ker_eq_bot.mp h)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hz0' : (z : H) ≠ 0 := by simpa using hz0
  have hzW : (z : H) ∈ W := by
    change W.mkQ (z : H) = 0 at hz
    exact (Submodule.Quotient.mk_eq_zero W).mp hz
  refine ⟨(‖(z : H)‖⁻¹ : 𝕜) • (z : H), L.smul_mem _ z.property,
    W.smul_mem _ hzW, ?_⟩
  simp [norm_smul, norm_ne_zero_iff.mpr hz0']

lemma closedCodimension_orthogonal [CompleteSpace H] (M : Submodule 𝕜 H) {n : ℕ}
    (hM : TrialSpace M n) : ClosedCodimension M.orthogonal n := by
  letI := hM.1
  let b := Submodule.quotientEquivOfIsCompl M.orthogonal M M.isCompl_orthogonal.symm
  refine ⟨M.isClosed_orthogonal, ?_, ?_⟩
  · exact FiniteDimensional.of_injective b.toLinearMap b.injective
  · exact b.finrank_eq.trans hM.2

lemma reciprocal_of_sandwich [CompleteSpace H] (T : H →L[𝕜] H)
    (n : ℕ) (μ : ℝ) (hq : ∀ x, x ≠ 0 → 0 < rayleigh T x)
    (hs : SpectralSandwich T n μ) : ReciprocalAt T n μ := by
  obtain ⟨L, M, hL, hM, hlow, hupp, z, hzL, hzM, hz0, hz⟩ := hs
  have hμ : 0 < μ := hz ▸ hq z hz0
  have nb (K : Submodule 𝕜 H) (hK : TrialSpace K (n+1)) :
      (reciprocalValues T K).Nonempty ∧ BddAbove (reciprocalValues T K) := by
    obtain ⟨x, hx, hxnorm⟩ := trialSpace_unit K hK (by omega)
    have hx0 : x ≠ 0 := by intro h; simp [h] at hxnorm
    refine ⟨⟨_, x, hx, hx0, rfl⟩, ?_⟩
    obtain ⟨r, hr⟩ := finite_trial_minimum T K hK (by omega)
    obtain ⟨y, hy, hy0, hyr⟩ := hr.1
    have hrpos : 0 < r := hyr ▸ hq y hy0
    refine ⟨r⁻¹, ?_⟩
    rintro _ ⟨w, hw, hw0, rfl⟩
    exact (inv_le_inv₀ (hq w hw0) hrpos).mpr (hr.2 ⟨w, hw, hw0, rfl⟩)
  have nw (W : Submodule 𝕜 H) (hW : ClosedCodimension W n) :
      (reciprocalValues T W).Nonempty ∧ BddBelow (reciprocalValues T W) := by
    obtain ⟨x, _, hx, hxnorm⟩ := unit_mem_inter_codimension L W hL hW
    have hx0 : x ≠ 0 := by intro h; simp [h] at hxnorm
    refine ⟨⟨_, x, hx, hx0, rfl⟩, 0, ?_⟩
    rintro _ ⟨y, _, hy0, rfl⟩
    exact (inv_pos.mpr (hq y hy0)).le
  have hMW : ClosedCodimension M.orthogonal n := closedCodimension_orthogonal M hM
  have hLval : sSup (reciprocalValues T L) = μ⁻¹ := by
    apply le_antisymm
    · apply csSup_le (nb L hL).1
      rintro _ ⟨x, hx, hx0, rfl⟩
      exact (inv_le_inv₀ (hq x hx0) hμ).mpr (hlow x hx hx0)
    · have hm : (rayleigh T z)⁻¹ ∈ reciprocalValues T L := ⟨z, hzL, hz0, rfl⟩
      rw [hz] at hm
      exact le_csSup (nb L hL).2 hm
  have hMval : sInf (reciprocalValues T M.orthogonal) = μ⁻¹ := by
    apply le_antisymm
    · have hm : (rayleigh T z)⁻¹ ∈ reciprocalValues T M.orthogonal := ⟨z, hzM, hz0, rfl⟩
      rw [hz] at hm
      exact csInf_le (nw M.orthogonal hMW).2 hm
    · apply le_csInf (nw M.orthogonal hMW).1
      rintro _ ⟨x, hx, hx0, rfl⟩
      exact (inv_le_inv₀ hμ (hq x hx0)).mpr (hupp x hx hx0)
  refine ⟨hμ, hq, nb, nw, ⟨⟨L, hL, hLval⟩, ?_⟩, ⟨⟨M.orthogonal, hMW, hMval⟩, ?_⟩⟩
  · rintro _ ⟨K, hK, rfl⟩
    letI := hK.1
    letI := hM.1
    obtain ⟨x, hxK, hxM, hxnorm⟩ := unit_mem_inter_orthogonal M K (by rw [hM.2, hK.2]; omega)
    have hx0 : x ≠ 0 := by intro h; simp [h] at hxnorm
    exact ((inv_le_inv₀ hμ (hq x hx0)).mpr (hupp x hxM hx0)).trans
      (le_csSup (nb K hK).2 ⟨x, hxK, hx0, rfl⟩)
  · rintro _ ⟨W, hW, rfl⟩
    obtain ⟨x, hxL, hxW, hxnorm⟩ := unit_mem_inter_codimension L W hL hW
    have hx0 : x ≠ 0 := by intro h; simp [h] at hxnorm
    exact (csInf_le (nw W hW).2 ⟨x, hxW, hx0, rfl⟩).trans
      ((inv_le_inv₀ (hq x hx0) hμ).mpr (hlow x hxL hx0))

/-- The attained Courant--Fischer and reciprocal formulas, with the same
complete multiplicity-counting spectral list for every admissible index. -/
theorem positive_minmax : Spec.Principle.{u,v} := by
  intro 𝕜 H _ _ _ _ T hp hc
  obtain ⟨I, e, a, hd⟩ := ordered_positive_spectrum 𝕜 H T hp hc
  refine ⟨I, e, a, hd, ?_, ?_⟩
  · intro n hn
    exact courantFischer_of_sandwich T hp n _ (spectral_sandwich T hp I e a hd n hn)
  · intro hinj n hn
    exact reciprocal_of_sandwich T n _
      (rayleigh_pos_of_expansion T hp e a hd.2.2.1 hd.2.2.2.2.2.1 hinj)
      (spectral_sandwich T hp I e a hd n hn)

end ExpandedFA.CompactSpectral.PositiveMinMax
