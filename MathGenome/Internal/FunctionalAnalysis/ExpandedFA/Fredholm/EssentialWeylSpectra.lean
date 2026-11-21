import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.EssentialWeylSpectra
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.EssentialSpectraDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.HilbertSemiFredholmIndex
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
The complex conclusions of `fa2:p2:essential-spectrum` in the adopted source.
The Weyl formula follows from an explicit finite-rank correction of an
index-zero Fredholm operator. For normal operators, a closed-range generalized
inverse gives a punctured spectral gap; conversely the continuous functional
calculus at an isolated spectral value gives a finite-rank parametrix when the
eigenspace is finite dimensional. Neither argument assumes separability.

Only nonemptiness requires infinite dimensionality. The real conclusions of
the adopted theorem have separate owners and use the original real operators.
-/

noncomputable section
namespace ExpandedFA.Fredholm
open scoped Topology
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectrum convention uses zI-T, while the Fredholm convention uses T-zI. -/
lemma mem_operatorSpectrum_iff (T : H →L[ℂ] H) (z : ℂ) :
    z ∈ BanachAlgebra.algebraSpectrum ℂ (H →L[ℂ] H) T ↔ ¬ IsUnit (T - z • 1) := by
  change ¬ IsUnit (algebraMap ℂ (H →L[ℂ] H) z - T) ↔ _
  rw [← neg_sub, IsUnit.neg_iff]
  rfl

/-- Invertibility implies Fredholmness and index zero, for the actual map. -/
lemma isUnit_fredholm_index_zero (A : H →L[ℂ] H) (hA : IsUnit A) :
    ∃ h : IsFredholm A, fredholmIndex A h = 0 := by
  have hb := ContinuousLinearMap.isUnit_iff_bijective.mp hA
  let he := (LinearEquiv.ofBijective A.toLinearMap hb).toContinuousLinearEquivOfContinuous
    A.continuous
  have hn := he.isFredholm
  have heq : he.toContinuousLinearMap = A := by ext x; rfl
  rw [heq] at hn
  refine ⟨isFredholm_of_native hn, ?_⟩
  exact LinearMap.index_of_bijective hb

/-- Atkinson identifies the original essential spectrum with the spectrum in
B(H)/K(H). No nontriviality of that quotient is assumed for this identity. -/
theorem essentialSpectrum_eq_calkinSpectrum (T : H →L[ℂ] H) :
    essentialSpectrum T = spectrum ℂ (calkinProjection ℂ H T) := by
  ext z
  rw [mem_essentialSpectrum]
  have ha := atkinson_calkin (T - z • 1)
  change IsFredholm (T - z • 1) ↔ IsUnit (calkinProjection ℂ H (T - z • 1)) at ha
  rw [ha]
  change ¬ IsUnit (calkinProjection ℂ H (T - z • 1)) ↔
    ¬ IsUnit (algebraMap ℂ (Calkin ℂ H) z - calkinProjection ℂ H T)
  rw [map_sub, map_smul, map_one, ← neg_sub, IsUnit.neg_iff]
  rfl

theorem essentialSpectrum_add_compact (T K : H →L[ℂ] H)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    essentialSpectrum (T + K) = essentialSpectrum T := by
  ext z
  simp only [mem_essentialSpectrum]
  have he : T + K - z • 1 = (T - z • 1) + K := by abel
  rw [he, isFredholm_add_compact_iff _ _ hK]

/-- Infinite-dimensionality makes the Calkin quotient nontrivial: its unit
cannot vanish, since the identity is not compact. -/
lemma calkin_nontrivial (hinf : ¬ FiniteDimensional ℂ H) : Nontrivial (Calkin ℂ H) := by
  apply nontrivial_of_ne (1 : Calkin ℂ H) 0
  intro h
  have hc : Compactness.IsCompactLinearMap (1 : H →L[ℂ] H).toLinearMap :=
    (calkinProjection_eq_zero _).mp (by simpa only [map_one] using h)
  have hn : IsCompactOperator (id : H → H) :=
    (Compactness.compact_iff_isCompactOperator _).mp hc
  exact hinf (FiniteDimensional.of_isCompactOperator_id hn)

theorem essentialSpectrum_nonempty_compact (T : H →L[ℂ] H)
    (hinf : ¬ FiniteDimensional ℂ H) : (essentialSpectrum T).Nonempty ∧ IsCompact (essentialSpectrum T) := by
  letI := calkin_nontrivial hinf
  rw [essentialSpectrum_eq_calkinSpectrum]
  exact ⟨spectrum.nonempty _, spectrum.isCompact _⟩

/-- A zero-index Fredholm map can be made invertible by adding a map
from its kernel onto its orthogonal cokernel, zero on the kernel complement. -/
theorem exists_finiteRank_correction (A : H →L[ℂ] H) (hA : IsFredholm A)
    (hi : fredholmIndex A hA = 0) :
    ∃ F : H →L[ℂ] H, FiniteDimensional ℂ F.range ∧ IsUnit (A + F) := by
  classical
  letI := hA.2.1
  letI := hA.2.2
  letI : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
  letI : CompleteSpace A.range := hA.1.completeSpace_coe
  letI : FiniteDimensional ℂ A.rangeᗮ :=
    A.range.quotientEquivOrthogonal.toLinearEquiv.finiteDimensional
  have hd : Module.finrank ℂ A.ker = Module.finrank ℂ A.rangeᗮ := by
    have hc := A.range.quotientEquivOrthogonal.toLinearEquiv.finrank_eq
    change (Module.finrank ℂ A.ker : ℤ) - (Module.finrank ℂ (H ⧸ A.range) : ℤ) = 0 at hi
    omega
  let e : A.ker ≃L[ℂ] A.rangeᗮ := ContinuousLinearEquiv.ofFinrankEq hd
  let F : H →L[ℂ] H := A.rangeᗮ.subtypeL.comp
    (e.toContinuousLinearMap.comp A.ker.orthogonalProjectionOnto)
  have hF (x : H) : F x ∈ A.rangeᗮ := (e (A.ker.orthogonalProjectionOnto x)).property
  have hf : FiniteDimensional ℂ F.range :=
    Submodule.finiteDimensional_of_le (show F.range ≤ A.rangeᗮ from
      by rintro _ ⟨x, rfl⟩; exact hF x)
  refine ⟨F, hf, ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨?_, ?_⟩⟩
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro x hx
      have hsum : A x + F x = 0 := hx
      have hax : A x = 0 := Submodule.disjoint_def.mp A.range.orthogonal_disjoint
        (A x) ⟨x, rfl⟩ (by rw [eq_neg_of_add_eq_zero_left hsum]; exact neg_mem (hF x))
      have hxk : x ∈ A.ker := hax
      have hfx : F x = 0 := by simpa only [hax, zero_add] using hsum
      have he : e ⟨x, hxk⟩ = 0 := by
        apply Subtype.ext
        change (e (A.ker.orthogonalProjectionOnto x) : H) = 0 at hfx
        have hp := A.ker.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hxk⟩
        rw [hp] at hfx
        exact hfx
      have hxzero := congrArg Subtype.val (e.injective (he.trans e.map_zero.symm))
      exact hxzero
    · exact bot_le
  · intro y
    obtain ⟨x, hx⟩ := (A.range.orthogonalProjectionOnto y).property
    let v : A.ker := e.symm (A.rangeᗮ.orthogonalProjectionOnto y)
    refine ⟨x - A.ker.starProjection x + v, ?_⟩
    have hAv : A v = 0 := v.property
    have hAp : A (A.ker.starProjection x) = 0 :=
      (A.ker.orthogonalProjectionOnto x).property
    have hproj : A.ker.orthogonalProjectionOnto
        (x - A.ker.starProjection x + v) = v := by
      rw [map_add, map_sub]
      simp only [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        sub_self, zero_add]
    change A (x - A.ker.starProjection x + v) +
      (e (A.ker.orthogonalProjectionOnto (x - A.ker.starProjection x + v)) : H) = y
    rw [map_add, map_sub, hAv, hAp, sub_zero, add_zero, hproj, e.apply_symm_apply]
    have hx' : A x = (A.range.orthogonalProjectionOnto y : H) := hx
    rw [hx']
    exact A.range.starProjection_add_starProjection_orthogonal y

/-- Resolvent membership after some compact perturbation is exactly the
zero-index Fredholm condition. -/
theorem not_mem_weylSpectrum_iff (T : H →L[ℂ] H) (z : ℂ) :
    z ∉ weylSpectrum T ↔
      ∃ h : IsFredholm (T - z • 1), fredholmIndex (T - z • 1) h = 0 := by
  classical
  constructor
  · intro hz
    rw [mem_weylSpectrum] at hz
    push Not at hz
    obtain ⟨K, hK, hzK⟩ := hz
    have he : T + K - z • 1 = (T - z • 1) + K := by abel
    have hu : IsUnit ((T - z • 1) + K) := by
      simpa only [mem_operatorSpectrum_iff, not_not, he] using hzK
    obtain ⟨hAK, hiAK⟩ := isUnit_fredholm_index_zero _ hu
    have hA := (isFredholm_add_compact_iff _ K hK).mp hAK
    refine ⟨hA, ?_⟩
    exact (fredholmIndex_add_compact _ K hK hA hAK).symm.trans hiAK
  · rintro ⟨hA, hi⟩ hz
    obtain ⟨F, hF, hu⟩ := exists_finiteRank_correction (T - z • 1) hA hi
    letI := hF
    have hc := compact_of_finiteDimensional_range F
    have hspec := (mem_weylSpectrum T z).mp hz F hc
    rw [mem_operatorSpectrum_iff] at hspec
    have he : T + F - z • 1 = (T - z • 1) + F := by abel
    exact hspec (he.symm ▸ hu)

theorem weylSpectrum_formula (T : H →L[ℂ] H) :
    weylSpectrum T = essentialSpectrum T ∪
      {z | ∃ h : IsFredholm (T - z • 1), fredholmIndex (T - z • 1) h ≠ 0} := by
  classical
  ext z
  have hh := not_mem_weylSpectrum_iff T z
  simp only [Set.mem_union, mem_essentialSpectrum, Set.mem_ofPred_eq]
  by_cases hf : IsFredholm (T - z • 1)
  · constructor
    · intro hz
      exact Or.inr ⟨hf, fun hi => (hh.mpr ⟨hf, hi⟩) hz⟩
    · rintro (hn | ⟨h, hi⟩)
      · exact (hn hf).elim
      · by_contra hz
        obtain ⟨h', hi'⟩ := hh.mp hz
        exact hi hi' 
  · have hn : ¬ ∃ h : IsFredholm (T - z • 1), fredholmIndex (T - z • 1) h = 0 := by
      rintro ⟨h, _⟩; exact hf h
    exact ⟨fun _ => Or.inl hf, fun _ => by_contra fun h => hn (hh.mp h)⟩

/-- Reindexing all compact perturbations proves invariance directly. -/
theorem weylSpectrum_add_compact (T K : H →L[ℂ] H)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    weylSpectrum (T + K) = weylSpectrum T := by
  ext z
  simp only [mem_weylSpectrum]
  constructor
  · intro h L hL
    have hneg : Compactness.IsCompactLinearMap (-K).toLinearMap := by
      simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_neg] using
        Compactness.compact_smul (-1 : ℂ) K.toLinearMap hK
    have hLK := Compactness.compact_add L.toLinearMap (-K).toLinearMap hL hneg
    have he : T + K + (L + -K) = T + L := by abel
    simpa only [he] using h (L + -K) hLK
  · intro h L hL
    have hKL := Compactness.compact_add K.toLinearMap L.toLinearMap hK hL
    simpa only [add_assoc] using h (K + L) hKL

/-- A normal Fredholm operator has index zero because its adjoint has the
same kernel and its cokernel is the adjoint kernel. -/
theorem normal_fredholmIndex_zero (A : H →L[ℂ] H) (hN : IsStarNormal A)
    (hA : IsFredholm A) : fredholmIndex A hA = 0 := by
  have he := (cokernelEquivAdjointKer A hA.1).finrank_eq
  rw [ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker hN] at he
  change (Module.finrank ℂ A.ker : ℤ) - (Module.finrank ℂ (H ⧸ A.range) : ℤ) = 0
  rw [he, sub_self]

theorem normal_weylSpectrum_eq_essentialSpectrum (N : H →L[ℂ] H) (hN : IsStarNormal N) :
    weylSpectrum N = essentialSpectrum N := by
  letI := hN
  rw [weylSpectrum_formula]
  have he : {z : ℂ | ∃ h : IsFredholm (N - z • 1), fredholmIndex (N - z • 1) h ≠ 0} = ∅ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro h
    have hc : Commute N (star (z • (1 : H →L[ℂ] H))) := by
      simp only [star_smul, star_one]
      exact (Commute.one_right N).smul_right _
    exact not_not.mpr (normal_fredholmIndex_zero _ hc.isStarNormal_sub h)
  rw [he, Set.union_empty]

/-- A bounded generalized inverse for a normal closed-range operator,
vanishing on the kernel. -/
lemma normal_partialInverse (A : H →L[ℂ] H) (hN : IsStarNormal A)
    (hc : IsClosed (A.range : Set H)) :
    ∃ S : H →L[ℂ] H, S * A = 1 - A.ker.starProjection ∧
      A * S = 1 - A.ker.starProjection ∧
      S * A.ker.starProjection = 0 ∧ A.ker.starProjection * S = 0 := by
  letI : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
  letI : CompleteSpace A.range := hc.completeSpace_coe
  let P := A.ker.starProjection
  let Q := (1 : H →L[ℂ] H) - P
  have hPP : P * P = P := A.ker.isIdempotentElem_starProjection
  have hPQ : P * Q = 0 := by dsimp [Q]; rw [mul_sub, mul_one, hPP, sub_self]
  have hQP : Q * P = 0 := by dsimp [Q]; rw [sub_mul, one_mul, hPP, sub_self]
  have hQQ : Q * Q = Q := by dsimp [Q]; noncomm_ring [hPP]
  have hAP : A * P = 0 := by
    ext x
    exact (A.ker.orthogonalProjectionOnto x).property
  have hPA : P * A = 0 := by
    ext x
    apply A.ker.starProjection_apply_eq_zero_iff.mpr
    rw [← ContinuousLinearMap.IsStarNormal.orthogonal_range hN]
    exact A.range.le_orthogonal_orthogonal ⟨x, rfl⟩
  have hQA : Q * A = A := by dsimp [Q]; rw [sub_mul, one_mul, hPA, sub_zero]
  have hAQ : A * Q = A := by dsimp [Q]; rw [mul_sub, mul_one, hAP, sub_zero]
  obtain ⟨U, hUA, hAU⟩ := closed_range_generalized_inverse A hc
  change U * A = Q at hUA
  have hAU' : A * U = Q := by
    change A * U = A.range.starProjection at hAU
    have hp := A.range.starProjection_orthogonal
    simp only [ContinuousLinearMap.IsStarNormal.orthogonal_range hN] at hp
    change A.ker.starProjection = (1 : H →L[ℂ] H) - A.range.starProjection at hp
    rw [hAU]
    change A.range.starProjection = 1 - A.ker.starProjection
    rw [hp]
    abel
  refine ⟨Q * U * Q, ?_, ?_, ?_, ?_⟩
  · calc
      Q * U * Q * A = Q * U * (Q * A) := mul_assoc _ _ _
      _ = Q * (U * A) := by rw [hQA, mul_assoc]
      _ = Q := by rw [hUA, hQQ]
  · calc
      A * (Q * U * Q) = (A * Q) * U * Q := by noncomm_ring
      _ = Q := by rw [hAQ, hAU', hQQ]
  · rw [mul_assoc, hQP, mul_zero]
  · rw [← mul_assoc P, ← mul_assoc P, hPQ, zero_mul, zero_mul]

/-- The generalized inverse gives an explicit punctured resolvent disk at 0.
This uses no finite-dimensional assumption on the kernel. -/
lemma normal_closed_range_gap (A : H →L[ℂ] H) (hN : IsStarNormal A)
    (hc : IsClosed (A.range : Set H)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ d : ℂ, d ≠ 0 → ‖d‖ < ε → IsUnit (A - d • 1) := by
  letI : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
  let P := A.ker.starProjection
  obtain ⟨S, hSA, hAS, hSP, hPS⟩ := normal_partialInverse A hN hc
  change S * A = 1 - P at hSA
  change A * S = 1 - P at hAS
  change S * P = 0 at hSP
  change P * S = 0 at hPS
  have hPP : P * P = P := A.ker.isIdempotentElem_starProjection
  have hAP : A * P = 0 := by ext x; exact (A.ker.orthogonalProjectionOnto x).property
  have hPA : P * A = 0 := by
    ext x
    apply A.ker.starProjection_apply_eq_zero_iff.mpr
    rw [← ContinuousLinearMap.IsStarNormal.orthogonal_range hN]
    exact A.range.le_orthogonal_orthogonal ⟨x, rfl⟩
  refine ⟨(‖S‖ + 1)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro d hd hsmall
  have hnorm : ‖d • S‖ < 1 := by
    rw [norm_smul]
    have hbound := mul_lt_mul_of_pos_right hsmall (show 0 < ‖S‖ + 1 from by positivity)
    rw [inv_mul_cancel₀ (show ‖S‖ + 1 ≠ 0 from by positivity)] at hbound
    nlinarith [norm_nonneg d, norm_nonneg S]
  have hneumann : IsUnit (1 - d • S) := isUnit_one_sub_of_norm_lt_one hnorm
  have hunit : IsUnit (A - d • P) := by
    apply isUnit_iff_exists.mpr
    refine ⟨S - d⁻¹ • P, ?_, ?_⟩
    · simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, smul_sub,
        smul_smul, hAP, hPS, hPP, smul_zero, mul_inv_cancel₀ hd, inv_mul_cancel₀ hd,
        one_smul, hAS]
      dsimp [P]
      abel
    · simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, smul_sub,
        smul_smul, hSP, hPA, hPP, smul_zero, mul_inv_cancel₀ hd, inv_mul_cancel₀ hd,
        one_smul, hSA]
      dsimp [P]
      abel
  have he : (A - d • P) * (1 - d • S) = A - d • 1 := by
    simp only [sub_mul, mul_sub, mul_one, mul_smul_comm, smul_mul_assoc, smul_sub,
      smul_smul, hPS, smul_zero, hAS]
    abel
  exact he ▸ hunit.mul hneumann

lemma normal_isolated_partialInverse (N : H →L[ℂ] H) (hN : IsStarNormal N) (z : ℂ)
    (hgap : ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ N, dist w z < ε → w = z) :
    ∃ S : H →L[ℂ] H, S * (N - z • 1) = (N - z • 1) * S ∧
      (N - z • 1) * S * (N - z • 1) = N - z • 1 := by
  classical
  obtain ⟨ε, hε, hgap⟩ := hgap
  let a : C(spectrum ℂ N, ℂ) := (ContinuousMap.id ℂ).restrict _ - z • 1
  have ha (w : spectrum ℂ N) : a w = (w : ℂ) - z := by simp [a]
  have hg : Continuous (fun w : spectrum ℂ N => (a w)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    by_cases hw : (w : ℂ) = z
    · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨ε, hε, ?_⟩
      intro v hv
      have he : (v : ℂ) = z := hgap v v.property (by simpa only [Subtype.dist_eq, hw] using hv)
      simp only [ha, he, sub_self, inv_zero]
    · exact a.continuous.continuousAt.inv₀ (by rw [ha]; exact sub_ne_zero.mpr hw)
  let g : C(spectrum ℂ N, ℂ) := ⟨_, hg⟩
  let φ : C(spectrum ℂ N, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) := cfcHom hN
  have hφa : φ a = N - z • 1 := by
    dsimp only [a, φ]
    rw [map_sub, map_smul, map_one, cfcHom_id]
  have hag : a * g * a = a := by
    ext w
    change a w * (a w)⁻¹ * a w = a w
    by_cases hw : a w = 0
    · simp [hw]
    · rw [mul_inv_cancel₀ hw, one_mul]
  refine ⟨φ g, ?_, ?_⟩
  · rw [← hφa, ← map_mul, ← map_mul, mul_comm g a]
  · rw [← hφa, ← map_mul, ← map_mul, hag]

lemma normal_isolated_fredholm (N : H →L[ℂ] H) (hN : IsStarNormal N) (z : ℂ)
    (hgap : ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ N, dist w z < ε → w = z)
    (hk : FiniteDimensional ℂ (N - z • 1).ker) : IsFredholm (N - z • 1) := by
  let A := N - z • 1
  letI := hk
  obtain ⟨S, hc, hASA⟩ := normal_isolated_partialInverse N hN z hgap
  change S * A = A * S at hc
  change A * S * A = A at hASA
  have hl : (S * A - 1).range ≤ A.ker := by
    rintro _ ⟨x, rfl⟩
    change (A * (S * A - 1)) x = 0
    have he : A * (S * A - 1) = 0 := by rw [mul_sub, mul_one, ← mul_assoc, hASA, sub_self]
    rw [he]; rfl
  have hr : (A * S - 1).range ≤ A.ker := by rw [← hc]; exact hl
  letI : FiniteDimensional ℂ (S * A - 1).range := Submodule.finiteDimensional_of_le hl
  letI : FiniteDimensional ℂ (A * S - 1).range := Submodule.finiteDimensional_of_le hr
  apply (atkinson_finite_rank A).mpr
  exact ⟨S, inferInstance, inferInstance⟩

lemma normal_sub_scalar (N : H →L[ℂ] H) (hN : IsStarNormal N) (z : ℂ) :
    IsStarNormal (N - z • 1) := by
  letI := hN
  have hc : Commute N (star (z • (1 : H →L[ℂ] H))) := by
    simp only [star_smul, star_one]
    exact (Commute.one_right N).smul_right _
  exact hc.isStarNormal_sub

lemma normal_fredholm_isolated (N : H →L[ℂ] H) (hN : IsStarNormal N) (z : ℂ)
    (hF : IsFredholm (N - z • 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ N, dist w z < ε → w = z := by
  obtain ⟨ε, hε, hgap⟩ := normal_closed_range_gap (N - z • 1)
    (normal_sub_scalar N hN z) hF.1
  refine ⟨ε, hε, ?_⟩
  intro w hw hdist
  by_contra hne
  have hu := hgap (w - z) (sub_ne_zero.mpr hne) (by simpa only [dist_eq_norm] using hdist)
  have he : (N - z • 1) - (w - z) • 1 = N - w • 1 := by rw [sub_smul]; abel
  exact (mem_operatorSpectrum_iff N w).mp hw (he ▸ hu)

/-- All nonisolated spectral values and exactly the isolated values whose
actual eigenspace is infinite dimensional. -/
theorem normal_essentialSpectrum_description (N : H →L[ℂ] H) (hN : IsStarNormal N) :
    essentialSpectrum N =
      {z | z ∈ spectrum ℂ N ∧
        ((∀ ε : ℝ, 0 < ε → ∃ w ∈ spectrum ℂ N, w ≠ z ∧ dist w z < ε) ∨
          ((∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ N, dist w z < ε → w = z) ∧
            ¬ FiniteDimensional ℂ (N - z • 1).ker))} := by
  classical
  ext z
  change (¬ IsFredholm (N - z • 1)) ↔ _
  constructor
  · intro hn
    have hspec : z ∈ spectrum ℂ N := by
      apply (mem_operatorSpectrum_iff N z).mpr
      intro hu
      exact hn (isUnit_fredholm_index_zero _ hu).choose
    refine ⟨hspec, ?_⟩
    by_cases hiso : ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ N, dist w z < ε → w = z
    · exact Or.inr ⟨hiso, fun hk => hn (normal_isolated_fredholm N hN z hiso hk)⟩
    · apply Or.inl
      intro ε hε
      by_contra hex
      apply hiso
      refine ⟨ε, hε, ?_⟩
      intro w hw hd
      by_contra hne
      exact hex ⟨w, hw, hne, hd⟩
  · rintro ⟨_, hnon | ⟨_, hinf⟩⟩ hF
    · obtain ⟨ε, hε, hgap⟩ := normal_fredholm_isolated N hN z hF
      obtain ⟨w, hw, hne, hd⟩ := hnon ε hε
      exact hne (hgap w hw hd)
    · exact hinf hF.2.1


end ExpandedFA.Fredholm
