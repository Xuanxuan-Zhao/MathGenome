import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.LocalSpectralAlternatives
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.ApproximateSpectrumBoundary
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.SemiFredholmPerturbations
import Mathlib.RingTheory.Artinian.Module

noncomputable section
namespace ExpandedFA.Fredholm.LocalSpectralAlternatives
open Set Filter
open scoped Topology
universe u v w

theorem unit_sequence : Spec.UnitSequence.{u} := ApproximateSpectrumBoundary.unit_sequence

theorem closed_range_complement : Spec.ClosedRangeComplement.{u} :=
  ApproximateSpectrumBoundary.closed_range_complement

theorem boundary_inclusion : Spec.BoundaryInclusion.{u} :=
  ApproximateSpectrumBoundary.boundary_inclusion

theorem perturbation : Spec.Perturbation.{u,v,w} :=
  SemiFredholmPerturbations.perturbation

theorem real_unit_sequence : Spec.RealUnitSequence.{u} :=
  ApproximateSpectrumBoundary.real_unit_sequence

theorem real_closed_range_complement : Spec.RealClosedRangeComplement.{u} :=
  ApproximateSpectrumBoundary.real_closed_range_complement

theorem real_boundary_inclusion : Spec.RealBoundaryInclusion.{u} :=
  ApproximateSpectrumBoundary.real_boundary_inclusion

section Algebraic
variable {𝕜 : Type*} [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- The hyperrange includes the zeroth power, which imposes no extra condition. -/
def hyperrange (A : Module.End 𝕜 E) : Submodule 𝕜 E :=
  ⨅ n : ℕ, LinearMap.range (A ^ n)

lemma mem_hyperrange (A : Module.End 𝕜 E) (x : E) :
    x ∈ hyperrange A ↔ ∀ n : ℕ, ∃ y : E, (A ^ n) y = x := by
  simp [hyperrange, Submodule.mem_iInf, LinearMap.mem_range]

lemma hyperrange_invariant (A : Module.End 𝕜 E) {x : E}
    (hx : x ∈ hyperrange A) : A x ∈ hyperrange A := by
  rw [mem_hyperrange] at hx ⊢
  intro n
  obtain ⟨y, hy⟩ := hx n
  refine ⟨A y, ?_⟩
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hy]

/-- Nonzero eigenvectors belong to every iterated range. -/
lemma eigenvector_mem_hyperrange (A : Module.End 𝕜 E) {a : 𝕜} (ha : a ≠ 0)
    {x : E} (hx : A x = a • x) : x ∈ hyperrange A := by
  have hp (n : ℕ) : (A ^ n) x = a ^ n • x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]
  rw [mem_hyperrange]
  intro n
  refine ⟨(a ^ n)⁻¹ • x, ?_⟩
  rw [map_smul, hp, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ha), one_smul]

/-- Only the finite kernel is used in stabilizing its intersections with the
iterated ranges; the ambient vector space may have arbitrary dimension. -/
lemma kernel_range_stabilizes (A : Module.End 𝕜 E) [FiniteDimensional 𝕜 A.ker] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      A.ker ⊓ LinearMap.range (A ^ N) = A.ker ⊓ LinearMap.range (A ^ n) := by
  let f : ℕ →o (Submodule 𝕜 A.ker)ᵒᵈ :=
    ⟨fun n => (LinearMap.range (A ^ n)).comap A.ker.subtype,
      fun m n h => Submodule.comap_mono (A.iterateRange.monotone h)⟩
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨N, fun n hn => ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hr⟩
    exact ⟨hx, show (⟨x, hx⟩ : A.ker) ∈ OrderDual.ofDual (f n) from (hN n hn) ▸ hr⟩
  · rintro ⟨hx, hr⟩
    exact ⟨hx, show (⟨x, hx⟩ : A.ker) ∈ OrderDual.ofDual (f N) from (hN n hn).symm ▸ hr⟩

/-- Stabilization permits correcting one fixed preimage into every range.
This is the algebraic heart of the hyperrange argument. -/
lemma hyperrange_surjective (A : Module.End 𝕜 E) [FiniteDimensional 𝕜 A.ker] :
    ∀ x ∈ hyperrange A, ∃ y ∈ hyperrange A, A y = x := by
  obtain ⟨N, hN⟩ := kernel_range_stabilizes A
  intro x hx
  have hx' := (mem_hyperrange A x).mp hx
  obtain ⟨u, hu⟩ := hx' (N + 1)
  let y := (A ^ N) u
  have hy : A y = x := by simpa [y, pow_succ', Module.End.mul_apply] using hu
  refine ⟨y, (mem_hyperrange A y).mpr ?_, hy⟩
  intro n
  by_cases hn : n ≤ N
  · exact A.iterateRange.monotone hn (LinearMap.mem_range_self (A ^ N) u)
  · have hNn : N ≤ n := Nat.le_of_not_ge hn
    obtain ⟨v, hv⟩ := hx' (n + 1)
    let z := (A ^ n) v
    have hz : A z = x := by simpa [z, pow_succ', Module.End.mul_apply] using hv
    have hzrange : z ∈ LinearMap.range (A ^ n) := LinearMap.mem_range_self _ v
    have hyrange : y ∈ LinearMap.range (A ^ N) := LinearMap.mem_range_self _ u
    have hdiff : y - z ∈ A.ker ⊓ LinearMap.range (A ^ N) := by
      refine ⟨?_, Submodule.sub_mem _ hyrange (A.iterateRange.monotone hNn hzrange)⟩
      change A (y - z) = 0
      rw [map_sub, hy, hz, sub_self]
    rw [hN n hNn] at hdiff
    have hymem : y ∈ LinearMap.range (A ^ n) := by
      simpa using (LinearMap.range (A ^ n)).add_mem hdiff.2 hzrange
    exact hymem

end Algebraic
section Hilbert
variable {𝕜 : Type*} [RCLike 𝕜] {H K G : Type*}
  [NormedAddCommGroup H] [NormedAddCommGroup K] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace K] [CompleteSpace G]

lemma leftSemiFredholm_comp (S : K →L[𝕜] G) (T : H →L[𝕜] K)
    (hS : IsLeftSemiFredholm S) (hT : IsLeftSemiFredholm T) :
    IsLeftSemiFredholm (S.comp T) := by
  obtain ⟨L, hL⟩ := (hilbert_left_compact S).mp hS
  obtain ⟨M, hM⟩ := (hilbert_left_compact T).mp hT
  apply (hilbert_left_compact (S.comp T)).mpr
  refine ⟨M.comp L, ?_⟩
  have he : (M.comp L).comp (S.comp T) - ContinuousLinearMap.id 𝕜 H =
      M.comp ((L.comp S - ContinuousLinearMap.id 𝕜 K).comp T) +
      (M.comp T - ContinuousLinearMap.id 𝕜 H) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      add_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  rw [he]
  exact Compactness.compact_add _ _
    (Compactness.compact_postcomp _ M (Compactness.compact_precomp _ T hL)) hM

end Hilbert

section Endomorphism
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

lemma leftSemiFredholm_pow (A : H →L[𝕜] H) (hA : IsLeftSemiFredholm A) (n : ℕ) :
    IsLeftSemiFredholm (A ^ n) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · change IsClosed (LinearMap.range (LinearMap.id : H →ₗ[𝕜] H) : Set H)
      simp
    · change FiniteDimensional 𝕜 (LinearMap.ker (LinearMap.id : H →ₗ[𝕜] H))
      rw [LinearMap.ker_id]
      infer_instance
  | succ n ih =>
    rw [pow_succ']
    exact leftSemiFredholm_comp A (A ^ n) hA ih

lemma isClosed_hyperrange (A : H →L[𝕜] H) (hA : IsLeftSemiFredholm A) :
    IsClosed (hyperrange A.toLinearMap : Set H) := by
  simp only [hyperrange, Submodule.coe_iInf]
  apply isClosed_iInter
  intro n
  have he : A.toLinearMap ^ n = (A ^ n).toLinearMap := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', pow_succ', ih]; rfl
  rw [he]
  exact (leftSemiFredholm_pow A hA n).1


/-- Surjectivity and nullity are stable near a surjective finite-kernel map.
The cokernel estimate is used with its actual quotient, including the zero space. -/
lemma surjective_finiteKernel_eventually (A : H →L[𝕜] H)
    [FiniteDimensional 𝕜 A.ker] (hs : Function.Surjective A) :
    ∀ᶠ (B : H →L[𝕜] H) in 𝓝 A, Function.Surjective B ∧
      Module.finrank 𝕜 B.ker = Module.finrank 𝕜 A.ker := by
  have hAr : A.range = ⊤ := LinearMap.range_eq_top.mpr hs
  let : Subsingleton (H ⧸ A.range) := Submodule.Quotient.subsingleton_iff.mpr hAr
  have hAc : IsClosed (A.range : Set H) := by rw [hAr]; exact isClosed_univ
  have hAf : IsFredholm A := ⟨hAc, inferInstance, inferInstance⟩
  obtain ⟨c, hc, hb⟩ :=
    (Hilbert.ClosedRangeEquivalences.closed_range_iff_lower_bound 𝕜 H H A).mp hAc
  have hn : ∀ᶠ B : H →L[𝕜] H in 𝓝 A, ‖B - A‖ < c := by
    have ht : Tendsto (fun B : H →L[𝕜] H => ‖B - A‖) (𝓝 A) (𝓝 0) := by
      simpa using ((continuous_id.sub continuous_const :
        Continuous (fun B : H →L[𝕜] H => B - A)).norm.tendsto A)
    exact ht.eventually (gt_mem_nhds hc)
  filter_upwards [hn, fredholmIndex_eventually_eq A hAf] with B hnorm hB
  obtain ⟨hBf, hi⟩ := hB
  have hBA : A + (B - A) = B := by abel
  have hdef := SemiFredholmPerturbations.cokernel_rank_le A (B - A) hAc
    (by rw [hBA]; exact hBf.1) hnorm hb
  rw [hBA] at hdef
  have hzero : Module.rank 𝕜 (H ⧸ B.range) = 0 := by
    have hz : Module.rank 𝕜 (H ⧸ A.range) = 0 := rank_zero_iff.mpr inferInstance
    rw [hz] at hdef
    exact le_antisymm hdef bot_le
  let : Subsingleton (H ⧸ B.range) := rank_zero_iff.mp hzero
  refine ⟨LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp inferInstance), ?_⟩
  simpa only [fredholmIndex, Module.finrank_zero_of_subsingleton, sub_zero,
    Nat.cast_zero, Nat.cast_inj] using hi

/-- The continuous restriction to the hyperrange. -/
def hyperrangeRestriction (A : H →L[𝕜] H) :
    hyperrange A.toLinearMap →L[𝕜] hyperrange A.toLinearMap :=
  (A.domRestrict (hyperrange A.toLinearMap)).codRestrict (hyperrange A.toLinearMap)
    fun x => hyperrange_invariant A.toLinearMap x.property

lemma hyperrangeRestriction_surjective (A : H →L[𝕜] H)
    [FiniteDimensional 𝕜 A.ker] : Function.Surjective (hyperrangeRestriction A) := by
  intro x
  obtain ⟨y, hy, hAy⟩ := hyperrange_surjective A.toLinearMap x x.property
  exact ⟨⟨y, hy⟩, Subtype.ext hAy⟩

lemma hyperrangeRestriction_finiteKernel (A : H →L[𝕜] H)
    [FiniteDimensional 𝕜 A.ker] : FiniteDimensional 𝕜 (hyperrangeRestriction A).ker := by
  let f : (hyperrangeRestriction A).ker →ₗ[𝕜] A.ker :=
    { toFun := fun x => ⟨((x : hyperrange A.toLinearMap) : H),
        congrArg Subtype.val x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective f (fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun t : A.ker => (t : H)) h)))

/-- Restricting a nonzero spectral shift to the hyperrange does not change its kernel. -/
def shiftKernelEquiv (A : H →L[𝕜] H) (a : 𝕜) (ha : a ≠ 0) :
    (A - a • (1 : H →L[𝕜] H)).ker ≃ₗ[𝕜]
      (hyperrangeRestriction A - a • (1 : hyperrange A.toLinearMap →L[𝕜]
        hyperrange A.toLinearMap)).ker where
  toFun x := ⟨⟨x, eigenvector_mem_hyperrange A.toLinearMap ha
    (sub_eq_zero.mp x.property)⟩, Subtype.ext x.property⟩
  invFun x := ⟨((x : hyperrange A.toLinearMap) : H), congrArg Subtype.val x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The finite-kernel half of the punctured-neighborhood theorem. -/
lemma left_punctured_nullity (A : H →L[𝕜] H) (hA : IsLeftSemiFredholm A) :
    ∃ r : ℝ, 0 < r ∧ ∃ n : ℕ, ∀ a : 𝕜, a ≠ 0 → ‖a‖ < r →
      Module.finrank 𝕜 (A - a • (1 : H →L[𝕜] H)).ker = n := by
  let := hA.2
  let M := hyperrange A.toLinearMap
  let : CompleteSpace M := (isClosed_hyperrange A hA).completeSpace_coe
  let := hyperrangeRestriction_finiteKernel A
  have he := surjective_finiteKernel_eventually (hyperrangeRestriction A)
    (hyperrangeRestriction_surjective A)
  have hc : Continuous (fun a : 𝕜 => hyperrangeRestriction A - a • (1 : M →L[𝕜] M)) := by
    fun_prop
  have ht : Tendsto (fun a : 𝕜 => hyperrangeRestriction A - a •
      (1 : M →L[𝕜] M)) (𝓝 0) (𝓝 (hyperrangeRestriction A)) := by
    have ht₀ := hc.tendsto (0 : 𝕜)
    have he₀ : (hyperrangeRestriction A - (0 : 𝕜) • (1 : M →L[𝕜] M)) =
        hyperrangeRestriction A := by
      ext x
      change A (x : H) - (0 : 𝕜) • (x : H) = A (x : H)
      rw [zero_smul, sub_zero]
    rw [he₀] at ht₀
    exact ht₀
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (ht.eventually he)
  refine ⟨r, hr, Module.finrank 𝕜 (hyperrangeRestriction A).ker, fun a ha har => ?_⟩
  have hn := (hball (by simpa using har)).2
  exact (shiftKernelEquiv A a ha).finrank_eq.trans hn


lemma adjoint_shift (A : H →L[𝕜] H) (a : 𝕜) :
    (A - a • (1 : H →L[𝕜] H)).adjoint = A.adjoint - star a • (1 : H →L[𝕜] H) := by
  simp only [map_sub, map_smulₛₗ, ContinuousLinearMap.adjoint_one]
  rfl

lemma left_shift_eventually (A : H →L[𝕜] H) (hA : IsLeftSemiFredholm A) :
    ∀ᶠ a : 𝕜 in 𝓝 0, IsLeftSemiFredholm (A - a • (1 : H →L[𝕜] H)) ∧
      (IsFredholm (A - a • (1 : H →L[𝕜] H)) ↔ IsFredholm A) := by
  have hc : Continuous (fun a : 𝕜 => A - a • (1 : H →L[𝕜] H)) := by fun_prop
  have ht : Tendsto (fun a : 𝕜 => A - a • (1 : H →L[𝕜] H)) (𝓝 0) (𝓝 A) := by
    simpa only [zero_smul, sub_zero] using hc.tendsto 0
  exact ht.eventually (IsLeftSemiFredholm.eventually_nhds A hA)

lemma left_punctured_constancy (A : H →L[𝕜] H) (hA : IsLeftSemiFredholm A) :
    ∃ r : ℝ, 0 < r ∧ ∃ n d : ℕ∞, ∀ a : 𝕜, a ≠ 0 → ‖a‖ < r →
      IsLeftSemiFredholm (A - a • (1 : H →L[𝕜] H)) ∧
      (Module.rank 𝕜 (A - a • (1 : H →L[𝕜] H)).ker).toENat = n ∧
      (Module.rank 𝕜 (H ⧸ (A - a • (1 : H →L[𝕜] H)).range)).toENat = d := by
  obtain ⟨r₀, hr₀, h₀⟩ := Metric.mem_nhds_iff.mp (left_shift_eventually A hA)
  obtain ⟨r₁, hr₁, n, hn⟩ := left_punctured_nullity A hA
  by_cases hf : IsFredholm A
  · have hs : IsLeftSemiFredholm A.adjoint := ⟨hf.adjoint.1, hf.adjoint.2.1⟩
    obtain ⟨r₂, hr₂, d, hd⟩ := left_punctured_nullity A.adjoint hs
    refine ⟨min r₀ (min r₁ r₂), lt_min hr₀ (lt_min hr₁ hr₂), n, d, ?_⟩
    intro a ha har
    have hb := h₀ (by simpa using lt_of_lt_of_le har (min_le_left _ _))
    have hfa := hb.2.mpr hf
    let := hfa.2.1
    let := hfa.adjoint.2.1
    refine ⟨hb.1, ?_, ?_⟩
    · rw [← Module.finrank_eq_rank, map_natCast, hn a ha
        (lt_of_lt_of_le har ((min_le_right _ _).trans (min_le_left _ _)))]
    · rw [(cokernelEquivAdjointKer _ hfa.1).rank_eq,
        ← Module.finrank_eq_rank, map_natCast]
      rw [adjoint_shift]
      exact congrArg (fun k : ℕ => (k : ℕ∞))
        (hd (star a) (star_ne_zero.mpr ha) (by
          simpa using lt_of_lt_of_le har ((min_le_right _ _).trans (min_le_right _ _))))
  · refine ⟨min r₀ r₁, lt_min hr₀ hr₁, n, ⊤, ?_⟩
    intro a ha har
    have hb := h₀ (by simpa using lt_of_lt_of_le har (min_le_left _ _))
    let := hb.1.2
    refine ⟨hb.1, ?_, ?_⟩
    · rw [← Module.finrank_eq_rank, map_natCast,
        hn a ha (lt_of_lt_of_le har (min_le_right _ _))]
    · apply Cardinal.toENat_eq_top.mpr
      apply le_of_not_gt
      intro hfin
      have hfd := Module.rank_lt_aleph0_iff.mp hfin
      exact hf (hb.2.mp ⟨hb.1.1, hb.1.2, hfd⟩)

/-- Adjunction supplies the other side, including infinite nullity. -/
lemma semi_punctured_constancy (A : H →L[𝕜] H) (hA : IsSemiFredholm A) :
    ∃ r : ℝ, 0 < r ∧ ∃ n d : ℕ∞, ∀ a : 𝕜, a ≠ 0 → ‖a‖ < r →
      IsSemiFredholm (A - a • (1 : H →L[𝕜] H)) ∧
      (Module.rank 𝕜 (A - a • (1 : H →L[𝕜] H)).ker).toENat = n ∧
      (Module.rank 𝕜 (H ⧸ (A - a • (1 : H →L[𝕜] H)).range)).toENat = d := by
  rcases hA with hl | hr
  · obtain ⟨r, hp, n, d, h⟩ := left_punctured_constancy A hl
    exact ⟨r, hp, n, d, fun a ha har =>
      ⟨Or.inl (h a ha har).1, (h a ha har).2⟩⟩
  · have hs := (hilbert_right_iff_left_adjoint A).mp hr
    obtain ⟨r, hp, n, d, h⟩ := left_punctured_constancy A.adjoint hs
    refine ⟨r, hp, d, n, fun a ha har => ?_⟩
    have he : A.adjoint - star a • (1 : H →L[𝕜] H) =
        (A - a • (1 : H →L[𝕜] H)).adjoint := (adjoint_shift A a).symm
    have hb := h (star a) (star_ne_zero.mpr ha) (by simpa using har)
    rw [he] at hb
    have hrb := (hilbert_right_iff_left_adjoint (A - a • (1 : H →L[𝕜] H))).mpr hb.1
    refine ⟨Or.inr hrb, ?_, ?_⟩
    · have heq := (cokernelEquivAdjointKer _ hb.1.1).rank_eq
      rw [ContinuousLinearMap.adjoint_adjoint] at heq
      rw [← heq]
      exact hb.2.2
    · rw [(cokernelEquivAdjointKer _ hrb.1).rank_eq]
      exact hb.2.1


/-- Zero extended nullity and deficiency are exactly bijectivity. -/
lemma zero_defects_iff_bijective (A : H →L[𝕜] H) :
    ((Module.rank 𝕜 A.ker).toENat = 0 ∧
      (Module.rank 𝕜 (H ⧸ A.range)).toENat = 0) ↔ Function.Bijective A := by
  constructor
  · rintro ⟨hk, hc⟩
    have hkbot : A.ker = ⊥ := Submodule.rank_eq_zero.mp (Cardinal.toENat_eq_zero.mp hk)
    have hq : Subsingleton (H ⧸ A.range) := rank_zero_iff.mp (Cardinal.toENat_eq_zero.mp hc)
    exact ⟨LinearMap.ker_eq_bot.mp hkbot,
      LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp hq)⟩
  · intro h
    have hk : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr h.1
    have hr : A.range = ⊤ := LinearMap.range_eq_top.mpr h.2
    constructor
    · exact Cardinal.toENat_eq_zero.mpr (Submodule.rank_eq_zero.mpr hk)
    · apply Cardinal.toENat_eq_zero.mpr
      exact rank_zero_iff.mpr (Submodule.Quotient.subsingleton_iff.mpr hr)

end Endomorphism

/- Full punctured-neighborhood constancy needs only semi-Fredholmness. -/
section ScalarField
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The same constants work for every nonzero shift of sufficiently small norm,
including both sides of a punctured real interval. -/
theorem punctured_constancy_rclike (T : H →L[𝕜] H) (z : 𝕜)
    (hT : IsSemiFredholm (T - z • (1 : H →L[𝕜] H))) :
    ∃ r : ℝ, 0 < r ∧ ∃ n d : ℕ∞, ∀ w : 𝕜, w ≠ z → ‖w - z‖ < r →
      IsSemiFredholm (T - w • (1 : H →L[𝕜] H)) ∧
      (Module.rank 𝕜 (T - w • (1 : H →L[𝕜] H)).ker).toENat = n ∧
      (Module.rank 𝕜 (H ⧸ (T - w • (1 : H →L[𝕜] H)).range)).toENat = d := by
  change IsSemiFredholm (T - z • (1 : H →L[𝕜] H)) at hT
  obtain ⟨r, hr, n, d, h⟩ := semi_punctured_constancy _ hT
  refine ⟨r, hr, n, d, fun w hw hwr => ?_⟩
  have hb := h (w - z) (sub_ne_zero.mpr hw) hwr
  have he : T - z • (1 : H →L[𝕜] H) - (w - z) • (1 : H →L[𝕜] H) =
      T - w • (1 : H →L[𝕜] H) := by
    rw [sub_smul]
    abel
  rw [he] at hb
  exact hb

lemma notMem_spectrum_iff_bijective_shift (T : H →L[𝕜] H) (z : 𝕜) :
    z ∉ spectrum 𝕜 T ↔ Function.Bijective (T - z • (1 : H →L[𝕜] H)) := by
  rw [spectrum.notMem_iff, ← ContinuousLinearMap.isUnit_iff_bijective]
  have he : algebraMap 𝕜 (H →L[𝕜] H) z - T = -(T - z • (1 : H →L[𝕜] H)) := by
    simp only [Algebra.algebraMap_eq_smul_one, neg_sub]
  rw [he, IsUnit.neg_iff]

/-- At a boundary point a punctured disk with constant defects contains a
resolvent point. Both constants are therefore zero throughout the disk. -/
theorem boundary_alternative_rclike (T : H →L[𝕜] H) (z : 𝕜)
    (hz : z ∈ frontier (spectrum 𝕜 T)) :
    (∃ r : ℝ, 0 < r ∧ ∀ w : 𝕜, w ∈ spectrum 𝕜 T → ‖w - z‖ < r → w = z) ∨
    (¬ IsLeftSemiFredholm (T - z • (1 : H →L[𝕜] H)) ∧
     ¬ IsRightSemiFredholm (T - z • (1 : H →L[𝕜] H))) := by
  by_cases hs : IsSemiFredholm (T - z • (1 : H →L[𝕜] H))
  · left
    obtain ⟨r, hr, n, d, h⟩ := punctured_constancy_rclike T z hs
    have hzspec : z ∈ spectrum 𝕜 T :=
      (spectrum.isClosed (𝕜 := 𝕜) T).closure_eq ▸ frontier_subset_closure hz
    have hzcl : z ∈ closure (spectrum 𝕜 T)ᶜ := by
      rw [frontier_eq_closure_inter_closure] at hz
      exact hz.2
    obtain ⟨w, hw, hwr⟩ := Metric.mem_closure_iff.mp hzcl r hr
    have hwne : w ≠ z := by rintro rfl; exact hw hzspec
    have hwr' : ‖w - z‖ < r := by simpa only [dist_eq_norm, norm_sub_rev] using hwr
    have hdim := (zero_defects_iff_bijective _).mpr
      ((notMem_spectrum_iff_bijective_shift T w).mp hw)
    have hn : n = 0 := (h w hwne hwr').2.1.symm.trans hdim.1
    have hd : d = 0 := (h w hwne hwr').2.2.symm.trans hdim.2
    refine ⟨r, hr, fun a haspec har => ?_⟩
    by_contra hane
    have ha := h a hane har
    have hbij := (zero_defects_iff_bijective _).mp
      ⟨ha.2.1.trans hn, ha.2.2.trans hd⟩
    exact (notMem_spectrum_iff_bijective_shift T a).mpr hbij haspec
  · right
    exact ⟨fun hl => hs (Or.inl hl), fun hr => hs (Or.inr hr)⟩

end ScalarField

/-- Specialization to the original complex Hilbert space. -/
theorem punctured_constancy : Spec.PuncturedConstancy.{u} := by
  intro H _ _ _ T z hT
  exact punctured_constancy_rclike T z hT

theorem boundary_alternative : Spec.BoundaryAlternative.{u} := by
  intro H _ _ _ T z hz
  exact boundary_alternative_rclike T z hz

/-- Specialization to the original real Hilbert space, with real dimensions. -/
theorem real_punctured_constancy : Spec.RealPuncturedConstancy.{u} := by
  intro H _ _ _ T z hT
  exact punctured_constancy_rclike T z hT

/-- Spectrum and frontier here are both taken over the original real field. -/
theorem real_boundary_alternative : Spec.RealBoundaryAlternative.{u} := by
  intro H _ _ _ T z hz
  exact boundary_alternative_rclike T z hz
end ExpandedFA.Fredholm.LocalSpectralAlternatives
