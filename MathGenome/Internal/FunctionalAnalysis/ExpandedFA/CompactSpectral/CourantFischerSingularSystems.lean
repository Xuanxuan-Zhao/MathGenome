import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.CourantFischerSingularSystems
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.SingularApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.PositiveMinMax

noncomputable section
universe u v w v₀ w₀
namespace ExpandedFA.CompactSpectral.CourantFischerSingularSystems
open scoped InnerProductSpace

/-- Assemble the approximation identity, its attainment, all rank cases and the
ideal estimate from the canonical spectral definition of singular numbers. -/
theorem singular_number_properties : Spec.SingularNumberProperties.{u,v,w,v₀,w₀} :=
  ⟨SingularApproximation.singular_sequence_properties,
    SingularApproximation.singular_rank_cases, SingularApproximation.best_approximation,
    SingularApproximation.singularValue_ideal⟩

theorem unit_inf_sup_identities : Spec.UnitInfSupIdentities.{u,v} := by
  intro 𝕜 H _ _ _ C n μ h
  exact ⟨h.2.2.2.csInf_eq.symm, h.2.2.1.csSup_eq.symm⟩

theorem quadratic_real : Spec.QuadraticReal.{u,v} := by
  intro 𝕜 H _ _ _ _ N hN x
  apply (RCLike.conj_eq_iff_re.mp ?_).symm
  rw [inner_conj_symm]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hN x x)

theorem positive_courant_fischer : Spec.PositiveCourantFischer.{u,v} := by
  intro 𝕜 H _ _ _ _ C hp hc
  obtain ⟨I, e, a, hd, hcf, _⟩ := PositiveMinMax.positive_minmax 𝕜 H C hp hc
  refine ⟨I, e, a, hd, ?_⟩
  intro n hn
  have h := hcf n hn
  simpa only [PositiveMinMax.Spec.CourantFischerAt, Spec.UnitCourantFischerAt,
    PositiveMinMax.rayleighValues_eq_unitValues] using h

section Singular
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

/-- Identifies the sorted vectors with the independently defined order statistic;
strict threshold counts handle tied singular values without choosing new vectors. -/
lemma sorted_singular_value (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (I : Set ℕ) (b : I ≃ S.Index) (hI : IsLowerSet I)
    (hb : Antitone (S.sigma ∘ b)) (n : ℕ) :
    PositiveMinMax.Spec.paddedValue I (S.sigma ∘ b) n =
      SingularApproximation.Spec.SingularValueValue T (n+1) := by
  classical
  have hc := SingularApproximation.singular_spectral_counting 𝕜 H K T hT S
  have hu (c : ℝ) (h : ∀ j, c < S.sigma j → (b.symm j).val < n) :
      {j | c < S.sigma j}.ncard < n+1 := by
    have hh := Set.ncard_le_ncard_of_injOn (fun j : S.Index => (b.symm j).val)
      (s := {j | c < S.sigma j}) (t := Set.Iio n)
      (fun j hj => h j hj) (Subtype.val_injective.comp b.symm.injective).injOn
      (Set.finite_Iio n)
    simpa only [Set.ncard_Iio_nat] using Nat.lt_succ_of_le hh
  by_cases hn : n ∈ I
  · let j : I := ⟨n, hn⟩
    have hp : 0 < S.sigma (b j) := S.positive _
    have hup : SingularApproximation.Spec.SingularValueValue T (n+1) ≤ S.sigma (b j) := by
      apply (hc.1 _ hp _ (Nat.succ_pos _)).mpr
      apply hu
      intro k hk
      by_contra h
      have hh := hb (show j ≤ b.symm k from Nat.le_of_not_gt h)
      have : S.sigma k ≤ S.sigma (b j) := by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh
      exact (not_lt_of_ge this) hk
    have hlo : S.sigma (b j) ≤ SingularApproximation.Spec.SingularValueValue T (n+1) := by
      apply (hc.2.1 _ hp _ (Nat.succ_pos _)).mpr
      let f : Fin (n+1) → S.Index := b ∘ PositiveMinMax.prefixIndex hI hn (n+1) le_rfl
      have hfi : Function.Injective f := b.injective.comp
        (PositiveMinMax.prefixIndex_injective hI hn (n+1) le_rfl)
      have hsub : Set.range f ⊆ {k | S.sigma (b j) ≤ S.sigma k} := by
        rintro _ ⟨i, rfl⟩
        apply hb
        change (i : ℕ) ≤ n
        omega
      have hh := Set.ncard_le_ncard hsub (S.finite_away _ hp)
      simpa only [Set.ncard_range_of_injective hfi, Nat.card_fin] using hh
    simpa only [PositiveMinMax.Spec.paddedValue, dite_eq_left hn, Function.comp_apply] using
      (le_antisymm hlo hup)
  · have hp := (SingularApproximation.singular_sequence_properties 𝕜 H K T hT).1
      (n+1) (Nat.succ_pos _)
    have hz : SingularApproximation.Spec.SingularValueValue T (n+1) = 0 := by
      apply le_antisymm _ hp
      by_contra hh
      have hpos : 0 < SingularApproximation.Spec.SingularValueValue T (n+1) := lt_of_not_ge hh
      have hh := (hc.1 _ (half_pos hpos) _ (Nat.succ_pos _)).mpr (hu _ (by
        intro k _
        by_contra hk
        exact hn (hI (Nat.le_of_not_gt hk) (b.symm k).property)))
      linarith
    simp only [PositiveMinMax.Spec.paddedValue, dite_eq_right hn, hz]

/-- Sort one complete singular system without changing any vector or kernel. -/
theorem ordered_singular_systems : Spec.OrderedSingularSystems.{u,v,w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T hT
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT
  letI : Countable S.Index := S.countable
  obtain ⟨I, b, hI, hb⟩ := PositiveMinMax.sorted_enumeration S.sigma S.positive S.finite_away
  refine ⟨I, S.rightVector ∘ b, S.leftVector ∘ b, S.sigma ∘ b, hI,
    S.right_orthonormal.comp b b.injective, S.left_orthonormal.comp b b.injective,
    (fun i => S.positive (b i)), hb, (fun i => S.map_right (b i)),
    (fun i => S.adjoint_left (b i)), ?_, ?_, ?_, ?_⟩
  · intro x
    exact b.hasSum_iff.mpr (S.expansion x)
  · have hr : Set.range (S.rightVector ∘ b) = Set.range S.rightVector := by
      rw [Set.range_comp, b.surjective.range_eq, Set.image_univ]
    simpa only [hr] using S.right_closedSpan
  · intro ε hε
    exact Set.Finite.preimage (f := b) b.injective.injOn (S.finite_away ε hε)
  · exact sorted_singular_value T S hT I b hI hb
end Singular

section Signed
open PositiveMinMax PositiveMinMax.Spec
open Filter
open scoped Topology ComplexConjugate
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A one-sided spectral bound. Negative diagonal entries require no absolute
value bound; this is what distinguishes the signed minmax theorem from SVD. -/
lemma quadratic_le_of_coefficients {J : Type*} (T : H →L[𝕜] H)
    (e : J → H) (he : Orthonormal 𝕜 e) (a : J → ℝ)
    (hs : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • e j) (T x))
    (x : H) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j, a j ≤ C ∨ inner 𝕜 (e j) x = 0) :
    RCLike.re (inner 𝕜 x (T x)) ≤ C * ‖x‖ ^ 2 := by
  have hlim : Continuous (fun y : H => RCLike.re (inner 𝕜 x y)) :=
    RCLike.continuous_re.comp (continuous_const.inner continuous_id)
  apply le_of_tendsto ((hlim.tendsto (T x)).comp (hs x))
  apply Eventually.of_forall
  intro F
  change RCLike.re (inner 𝕜 x (∑ j ∈ F,
    ((a j : 𝕜) * inner 𝕜 (e j) x) • e j)) ≤ _
  have hid (j : J) : RCLike.re (inner 𝕜 x
      (((a j : 𝕜) * inner 𝕜 (e j) x) • e j)) = a j * ‖inner 𝕜 (e j) x‖ ^ 2 := by
    rw [inner_smul_right, ← inner_conj_symm x (e j)]
    rw [mul_assoc, RCLike.mul_conj]
    simp only [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  rw [inner_sum, map_sum]
  simp_rw [hid]
  calc
    ∑ j ∈ F, a j * ‖inner 𝕜 (e j) x‖ ^ 2 ≤
        ∑ j ∈ F, C * ‖inner 𝕜 (e j) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      rcases hb j with h | h
      · exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
      · simp [h]
    _ = C * ∑ j ∈ F, ‖inner 𝕜 (e j) x‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ C * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left (he.sum_inner_products_le x) hC

/-- The dimension intersection argument only needs the two spectral bounds,
not positivity on the rest of the Hilbert space. -/
lemma unit_courant_fischer_of_sandwich (T : H →L[𝕜] H) (n : ℕ) (μ : ℝ)
    (hs : SpectralSandwich T n μ) : Spec.UnitCourantFischerAt T n μ := by
  classical
  obtain ⟨L, M, hL, hM, hlo, hup, z, hzL, hzM, hz0, hz⟩ := hs
  have bds (V : Submodule 𝕜 H) : BddBelow (unitValues T V) ∧ BddAbove (unitValues T V) := by
    have hab : ∀ r ∈ unitValues T V, |r| ≤ ‖T‖ := by
      rintro _ ⟨x, _, hx, rfl⟩
      simpa only [← rayleigh_eq_native, rayleigh, hx, one_pow, div_one] using
        T.rayleighQuotient_le_norm x
    exact ⟨⟨-‖T‖, fun r hr => (abs_le.mp (hab r hr)).1⟩,
      ⟨‖T‖, fun r hr => (abs_le.mp (hab r hr)).2⟩⟩
  have ne (V : Submodule 𝕜 H) (hV : TrialSpace V (n+1)) : (unitValues T V).Nonempty := by
    obtain ⟨x, hx, hn⟩ := trialSpace_unit V hV (Nat.succ_pos _)
    exact ⟨_, x, hx, hn, rfl⟩
  have inter (V W : Submodule 𝕜 H) (hV : TrialSpace V (n+1)) (hW : TrialSpace W n) :
      ∃ x ∈ V, x ∈ W.orthogonal ∧ ‖x‖ = 1 := by
    letI := hV.1
    letI := hW.1
    exact unit_mem_inter_orthogonal W V (by rw [hV.2, hW.2]; omega)
  have neperp (W : Submodule 𝕜 H) (hW : TrialSpace W n) :
      (unitValues T W.orthogonal).Nonempty := by
    obtain ⟨x, _, hx, hn⟩ := inter L W hL hW
    exact ⟨_, x, hx, hn, rfl⟩
  have low : ∀ x ∈ unitValues T L, μ ≤ x := by
    rintro _ ⟨x, hx, hn, rfl⟩
    simpa only [rayleigh, hn, one_pow, div_one] using
      hlo x hx (by intro h; simp [h] at hn)
  have upp : ∀ x ∈ unitValues T M.orthogonal, x ≤ μ := by
    rintro _ ⟨x, hx, hn, rfl⟩
    simpa only [rayleigh, hn, one_pow, div_one] using
      hup x hx (by intro h; simp [h] at hn)
  have hz₁ : μ ∈ unitValues T L := by
    rw [← rayleighValues_eq_unitValues]
    exact ⟨z, hzL, hz0, hz⟩
  have hz₂ : μ ∈ unitValues T M.orthogonal := by
    rw [← rayleighValues_eq_unitValues]
    exact ⟨z, hzM, hz0, hz⟩
  have hmin : sInf (unitValues T L) = μ := (IsLeast.csInf_eq ⟨hz₁, low⟩)
  have hmax : sSup (unitValues T M.orthogonal) = μ := (IsGreatest.csSup_eq ⟨hz₂, upp⟩)
  refine ⟨?_, (fun W hW => ⟨neperp W hW, (bds _).2⟩), ⟨⟨L, hL, hmin⟩, ?_⟩,
    ⟨⟨M, hM, hmax⟩, ?_⟩⟩
  · intro V hV
    exact ⟨ne V hV, (bds V).1, by
      simpa only [rayleighValues_eq_unitValues] using finite_trial_minimum T V hV (Nat.succ_pos _)⟩
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨x, hxV, hxM, hn⟩ := inter V M hV hM
    exact (csInf_le (bds V).1 ⟨x, hxV, hn, rfl⟩).trans (upp _ ⟨x, hxM, hn, rfl⟩)
  · rintro _ ⟨W, hW, rfl⟩
    obtain ⟨x, hxL, hxW, hn⟩ := inter L W hL hW
    exact (low _ ⟨x, hxL, hn, rfl⟩).trans (le_csSup (bds _).2 ⟨x, hxW, hn, rfl⟩)

/-- The first n+1 positive eigenvectors give a lower bound; orthogonality to
the first n removes all larger entries, while every negative entry is harmless. -/
lemma signed_spectral_sandwich {J : Type*} (T : H →L[𝕜] H)
    (e : J → H) (he : Orthonormal 𝕜 e) (a : J → ℝ)
    (heig : ∀ j, T (e j) = (a j : 𝕜) • e j)
    (hs : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • e j) (T x))
    (I : Set ℕ) (b : I ≃ {j : J // 0 < a j}) (hI : IsLowerSet I)
    (hb : Antitone (fun i => a (b i).val)) (n : ℕ) (hn : n ∈ I) :
    SpectralSandwich T n (a (b ⟨n, hn⟩).val) := by
  classical
  let f : Fin n → J := fun i => (b (prefixIndex hI hn n (by omega) i)).val
  let g : Fin (n+1) → J := fun i => (b (prefixIndex hI hn (n+1) le_rfl i)).val
  have hf : Function.Injective f := Subtype.val_injective.comp (b.injective.comp
    (prefixIndex_injective hI hn n (by omega)))
  have hg : Function.Injective g := Subtype.val_injective.comp (b.injective.comp
    (prefixIndex_injective hI hn (n+1) le_rfl))
  let L := Submodule.span 𝕜 (Set.range (e ∘ g))
  let M := Submodule.span 𝕜 (Set.range (e ∘ f))
  have hL : TrialSpace L (n+1) := ⟨FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _),
    finrank_span_fin _ (he.comp g hg).linearIndependent⟩
  have hM : TrialSpace M n := ⟨FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _),
    finrank_span_fin _ (he.comp f hf).linearIndependent⟩
  let j : I := ⟨n, hn⟩
  refine ⟨L, M, hL, hM, ?_, ?_, e (b j).val, ?_, ?_, he.ne_zero _, ?_⟩
  · intro x hx hx0
    apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mpr
    apply quadratic_ge_on_span T (e ∘ g) (he.comp g hg) (a ∘ g)
      (fun i => heig (g i)) _ _ x hx
    intro i
    exact hb (show prefixIndex hI hn (n+1) le_rfl i ≤ j from
      Nat.le_of_lt_succ i.isLt)
  · intro x hx hx0
    apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mpr
    apply quadratic_le_of_coefficients T e he a hs x _ (b j).property.le
    intro k
    by_cases hk : 0 < a k
    · let i : I := b.symm ⟨k, hk⟩
      by_cases hi : (i : ℕ) < n
      · right
        have hmem : e k ∈ M := Submodule.subset_span ⟨⟨i.val, hi⟩, by
          change e (b (⟨i.val, _⟩ : I)).val = e k
          simp only [show (⟨i.val, _⟩ : I) = i from rfl, i, Equiv.apply_symm_apply]⟩
        exact (M.mem_orthogonal x).mp hx _ hmem
      · left
        have hh := hb (show j ≤ i from Nat.le_of_not_gt hi)
        simpa only [i, Equiv.apply_symm_apply] using hh
    · exact Or.inl ((le_of_not_gt hk).trans (b j).property.le)
  · exact Submodule.subset_span ⟨⟨n, Nat.lt_succ_self _⟩, rfl⟩
  · apply (CompactNormalClassification.orthogonal_span_range_iff (e ∘ f) _).mpr
    intro i
    apply he.inner_eq_zero
    intro h
    have hi := congrArg Subtype.val (b.injective (Subtype.val_injective h))
    change (i : ℕ) = n at hi
    omega
  · exact rayleigh_eigenvector T _ _ (he.ne_zero _) (heig _)

/-- Order the positive part of any complete real diagonal expansion. -/
lemma positive_signed_list {J : Type u} [Countable J] (T : H →L[𝕜] H)
    (e : J → H) (he : Orthonormal 𝕜 e) (a : J → ℝ)
    (heig : ∀ j, T (e j) = (a j : 𝕜) • e j)
    (hs : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • e j) (T x))
    (hf : ∀ ε : ℝ, 0 < ε → {j | ε ≤ |a j|}.Finite) :
    ∃ (I : Set ℕ) (b : I ≃ {j : J // 0 < a j}), IsLowerSet I ∧
      Antitone (fun i => a (b i).val) ∧
      ∀ n (hn : n ∈ I), Spec.UnitCourantFischerAt T n (a (b ⟨n, hn⟩).val) := by
  have hf' (ε : ℝ) (hε : 0 < ε) : {j : {j : J // 0 < a j} | ε ≤ a j.val}.Finite := by
    apply ((hf ε hε).preimage (f := fun j : {j : J // 0 < a j} => j.val)
      Subtype.val_injective.injOn).subset
    intro j hj
    exact (show ε ≤ a j.val from hj).trans (le_abs_self _)
  obtain ⟨I, b, hI, hb⟩ := sorted_enumeration (fun j : {j : J // 0 < a j} => a j.val)
    (fun j => j.property) hf'
  exact ⟨I, b, hI, hb, fun n hn => unit_courant_fischer_of_sandwich T n _
    (signed_spectral_sandwich T e he a heig hs I b hI hb n hn)⟩

/-- Positive and negative eigenvalues are ordered and characterized separately,
without any finite-dimensional or separable-kernel assumption. -/
theorem signed_courant_fischer : Spec.SignedCourantFischer.{u,v} := by
  intro 𝕜 H _ _ _ _ N hN hc
  obtain ⟨J, hJ, e, a, he, ha, hspan, _, hs, _, hf⟩ :=
    CompactNormalClassification.selfAdjoint_expansion 𝕜 H N hN hc
  letI : Countable J := hJ
  refine ⟨J, hJ, e, a, he, ha, hspan, (fun x => (hs x).2), hf, ?_⟩
  intro sign hsign
  have heig (j : J) : ((sign : 𝕜) • N) (e j) = ((sign * a j : ℝ) : 𝕜) • e j := by
    simp only [smul_apply, (ha j).2, smul_smul, RCLike.ofReal_mul]
  have hsum (x : H) : HasSum
      (fun j => (((sign * a j : ℝ) : 𝕜) * inner 𝕜 (e j) x) • e j)
      (((sign : 𝕜) • N) x) := by
    simpa only [smul_apply, smul_smul, RCLike.ofReal_mul, mul_assoc] using
      ((hs x).2.const_smul (sign : 𝕜))
  have hfin (ε : ℝ) (hε : 0 < ε) : {j : J | ε ≤ |sign * a j|}.Finite := by
    rcases hsign with rfl | rfl <;> simpa only [one_mul, neg_mul, abs_neg] using hf ε hε
  exact positive_signed_list ((sign : 𝕜) • N) e he (fun j => sign * a j) heig hsum hfin
end Signed

end ExpandedFA.CompactSpectral.CourantFischerSingularSystems
