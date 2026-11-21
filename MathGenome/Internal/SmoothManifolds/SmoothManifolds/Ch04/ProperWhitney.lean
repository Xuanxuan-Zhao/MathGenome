import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.ProperWhitney
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.FiniteProperEmbedding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace SmoothManifolds.ProperWhitney
open ModelData AtlasData MapData FiniteRegularityData GoodProjectionData
  MapClassData PartitionData Set Filter
open scoped Topology ContDiff
universe u
variable {n q r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

/-- An image in a bounded tube around an exhaustion axis is proper. -/
theorem proper_of_bounded_remainder (e : M → Euclidean q) (he : Continuous e)
    (ρ : M → ℝ) (hρ : ∀ c : ℝ, IsCompact {x | ρ x ≤ c})
    (hρnonneg : ∀ x, 0 ≤ ρ x) (v : Euclidean q) (hv : v ≠ 0)
    (C : ℝ) (hC : ∀ x, ‖e x - ρ x • v‖ ≤ C) : IsProper e := by
  intro K hK
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  apply (hρ ((B + C) / ‖v‖)).of_isClosed_subset (hK.isClosed.preimage he)
  intro x hx
  change ρ x ≤ (B + C) / ‖v‖
  apply (le_div_iff₀ (norm_pos_iff.mpr hv)).mpr
  calc
    ρ x * ‖v‖ = ‖ρ x • v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρnonneg x)]
    _ ≤ ‖e x‖ + ‖e x - ρ x • v‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le (e x) (e x - ρ x • v)
    _ ≤ B + C := add_le_add (hB _ hx) (hC x)

omit [TopologicalSpace M] in
/-- Linear postcomposition transports the bounded remainder. -/
theorem bounded_remainder_postcomp (P : Euclidean q →L[ℝ] Euclidean r)
    (e : M → Euclidean q) (ρ : M → ℝ) (v : Euclidean q)
    (C : ℝ) (hC : ∀ x, ‖e x - ρ x • v‖ ≤ C) :
    ∀ x, ‖P (e x) - ρ x • P v‖ ≤ ‖P‖ * C := by
  intro x
  rw [← P.map_smul, ← P.map_sub]
  exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg P))

/-- Reduce an injective immersion while retaining a nonzero exhaustion axis.
The optional projective exclusion is used for precisely this axis. -/
theorem reduce_with_axis (S : SmoothManifold n a M) (ρ : M → ℝ) :
    ∀ (q : ℕ) (e : M → Euclidean q), IsEuclideanImmersion S e →
      Function.Injective e →
      (∃ v : Euclidean q, v ≠ 0 ∧ ∃ C : ℝ, ∀ x, ‖e x - ρ x • v‖ ≤ C) →
      ∃ g : M → Euclidean (2 * n + 1), IsEuclideanImmersion S g ∧
        Function.Injective g ∧ ∃ v : Euclidean (2 * n + 1), v ≠ 0 ∧
          ∃ C : ℝ, ∀ x, ‖g x - ρ x • v‖ ≤ C := by
  classical
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro e he hi htube
    obtain ⟨v, hv, C, hC⟩ := htube
    by_cases hq : q ≤ 2 * n + 1
    · obtain ⟨P, hP⟩ := FiniteProperEmbedding.exists_padding hq
      refine ⟨fun x => P (e x), ⟨GoodProjections.smoothEuclidean_postcomp S e he.1 P,
        ?_⟩, hP.comp hi, P v, ?_, ‖P‖ * C,
        bounded_remainder_postcomp P e ρ v C hC⟩
      · intro c hc p hp
        rw [GoodProjections.coordinateDerivative_postcomp c e p hp ((he.1 p).2 c hc hp)]
        exact hP.comp (he.2 c hc p hp)
      · exact fun h => hv (hP (by simpa using h))
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
      let V : Submodule ℝ (Euclidean (d + 1)) := Submodule.span ℝ {v}
      have hVrank : Module.finrank ℝ V = 1 := finrank_span_singleton hv
      have hV : V ≠ ⊤ := by
        intro h
        have hh := hVrank
        rw [h, finrank_top] at hh
        simp only [Module.finrank_pi, Fintype.card_fin] at hh
        omega
      let : Nonempty (ProjectiveData.RealProjectiveSpace d) :=
        ⟨ProjectiveData.projectiveProjection (SphereTorus.sphereBase d)⟩
      obtain ⟨L, havoid, hLi, hLim⟩ :=
        (GoodProjections.injective_immersion_directions_dense S e he hi
          (by omega) V hV).nonempty
      have hvL : projection L v ≠ 0 := by
        intro h
        have hmem := (GoodProjections.projection_eq_zero_iff L v).mp h
        have hle : V ≤ directionSubmodule L := Submodule.span_le.mpr (by
          intro z hz
          rcases Set.mem_singleton_iff.mp hz with rfl
          exact hmem)
        have heq : V = directionSubmodule L := Submodule.eq_of_le_of_finrank_eq hle (by
          rw [hVrank, GoodProjections.directionSubmodule_finrank])
        exact havoid (show directionSubmodule L ≤ V from heq.ge)
      let A : ProjectionSpace L ≃L[ℝ] Euclidean d :=
        ContinuousLinearEquiv.ofFinrankEq (by
          rw [GoodProjections.projectionSpace_finrank]
          simp [Euclidean, ModelData.Euclidean])
      let R : Euclidean (d + 1) →L[ℝ] ProjectionSpace L :=
        (projectionLinear L).rangeRestrict.toContinuousLinearMap
      let P : Euclidean (d + 1) →L[ℝ] Euclidean d := A.toContinuousLinearMap.comp R
      have hP (z w : Euclidean (d + 1)) (h : P z = P w) :
          projection L z = projection L w := congrArg Subtype.val (A.injective h)
      have hPv : P v ≠ 0 := by
        intro h
        apply hvL
        simpa using hP v 0 (by simpa using h)
      let f : M → Euclidean d := fun x => P (e x)
      have hf : IsEuclideanImmersion S f := by
        refine ⟨GoodProjections.smoothEuclidean_postcomp S e he.1 P, ?_⟩
        intro c hc p hp z w hzw
        apply hLim.2 c hc p hp
        change coordinateDerivative c (fun x => projection L (e x)) p z =
          coordinateDerivative c (fun x => projection L (e x)) p w
        rw [GoodProjections.coordinateDerivative_postcomp c e p hp
          ((he.1 p).2 c hc hp)] at hzw ⊢
        exact hP _ _ hzw
      have hfi : Function.Injective f := by
        intro x y hxy
        exact hLi (Subtype.ext (hP _ _ hxy))
      exact ih d (by omega) f hf hfi
        ⟨P v, hPv, ‖P‖ * C, bounded_remainder_postcomp P e ρ v C hC⟩

/-- Smooth ambient postcomposition respects the shared extension convention. -/
theorem smoothEuclidean_comp (S : SmoothManifold n a M)
    (e : M → Euclidean q) (he : IsSmoothEuclidean S e)
    (F : Euclidean q → Euclidean r) (hF : ContDiff ℝ ∞ F) :
    IsSmoothEuclidean S (F ∘ e) := by
  intro p
  refine ⟨hF.continuous.continuousAt.comp (he p).1, ?_⟩
  intro c hc hp
  obtain ⟨U, hU, hpU, G, hG, hEq⟩ := (he p).2 c hc hp
  exact ⟨U, hU, hpU, F ∘ G, hF.comp_contDiffOn hG, hEq.fun_comp F⟩

theorem coordinateDerivative_comp (c : ModelChart n a M) (e : M → Euclidean q)
    (p : M) (hp : p ∈ c.source)
    (he : LocalCoordinateExtension (⊤ : ℕ∞) (fun x => (c x).val) e p)
    (F : Euclidean q → Euclidean r) (hF : DifferentiableAt ℝ F (e p)) :
    coordinateDerivative c (F ∘ e) p =
      (fderiv ℝ F (e p)).comp (coordinateDerivative c e p) := by
  obtain ⟨U, hU, hpU, G, hG, hEq⟩ := he
  have hD := ((hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  rw [FiniteRegularity.coordinateDerivative_eq c e p hp _ ⟨G, hD, hEq⟩]
  apply FiniteRegularity.coordinateDerivative_eq c _ p hp
  refine ⟨F ∘ G, ?_, hEq.fun_comp F⟩
  have hFG : HasFDerivAt F (fderiv ℝ F (e p)) (G (c p).val) := by
    rw [hEq.eq_of_nhds]
    exact hF.hasFDerivAt
  exact hFG.comp _ hD

/-- A bounded coordinatewise compression with injective full derivative. -/
noncomputable def compress (z : Euclidean q) : Euclidean q := fun i => Real.arctan (z i)

theorem compress_smooth : ContDiff ℝ ∞ (compress : Euclidean q → Euclidean q) := by
  exact contDiff_pi.mpr (fun i => Real.contDiff_arctan.comp
    (contDiff_apply ℝ (fun _ : Fin q => ℝ) i))

theorem compress_injective : Function.Injective (compress : Euclidean q → Euclidean q) := by
  intro z w h
  funext i
  exact Real.arctan_injective (congrFun h i)

theorem compress_derivative_injective (z : Euclidean q) :
    Function.Injective (fderiv ℝ compress z) := by
  let D : Euclidean q →L[ℝ] Euclidean q := ContinuousLinearMap.pi
    (fun i => (1 / (1 + z i ^ 2)) • ContinuousLinearMap.proj i)
  have hD : HasFDerivAt compress D z := by
    apply hasFDerivAt_pi.mpr
    intro i
    exact (hasFDerivAt_apply i z).arctan
  rw [hD.fderiv]
  intro v w h
  funext i
  have hh := congrFun h i
  change (1 / (1 + z i ^ 2)) * v i = (1 / (1 + z i ^ 2)) * w i at hh
  exact mul_left_cancel₀ (by positivity : (1 / (1 + z i ^ 2)) ≠ 0) hh

theorem compress_immersion (S : SmoothManifold n a M)
    (e : M → Euclidean q) (he : IsEuclideanImmersion S e) :
    IsEuclideanImmersion S (compress ∘ e) := by
  refine ⟨smoothEuclidean_comp S e he.1 compress compress_smooth, ?_⟩
  intro c hc p hp
  rw [coordinateDerivative_comp c e p hp ((he.1 p).2 c hc hp) compress
    (compress_smooth.differentiable (by simp) (e p))]
  exact (compress_derivative_injective (e p)).comp (he.2 c hc p hp)

/-- Add the exhaustion coordinate to a bounded compression. This yields an
injective immersion in a bounded tube around the last coordinate axis. -/
theorem exists_immersion_with_axis (S : SmoothManifold n a M)
    (e : M → Euclidean q) (he : IsEuclideanImmersion S e) (hi : Function.Injective e)
    (ρ : M → ℝ) (hρ : ScalarSmooth S.smoothStructure.val ρ) :
    ∃ E : M → Euclidean (q + 1), IsEuclideanImmersion S E ∧ Function.Injective E ∧
      ∃ v : Euclidean (q + 1), v ≠ 0 ∧ ∃ C : ℝ, ∀ x, ‖E x - ρ x • v‖ ≤ C := by
  let E : M → Euclidean (q + 1) := fun x => Fin.snoc (compress (e x)) (ρ x)
  let v : Euclidean (q + 1) := Fin.snoc (0 : Euclidean q) 1
  let Q : Euclidean (q + 1) →L[ℝ] Euclidean q :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.castSucc)
  have hQ : (fun x => Q (E x)) = compress ∘ e := by
    funext x i
    simp [Q, E]
  have hcomp := compress_immersion S e he
  have hEs : IsSmoothEuclidean S E := by
    apply (FiniteProperEmbedding.smoothEuclidean_iff_scalar S E).mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [E] using hρ
    · simpa [E] using
        (FiniteProperEmbedding.smoothEuclidean_iff_scalar S (compress ∘ e)).mp hcomp.1 j
  have hEim : IsEuclideanImmersion S E := by
    refine ⟨hEs, ?_⟩
    intro c hc p hp z w hzw
    have hder := hcomp.2 c hc p hp
    rw [← hQ, GoodProjections.coordinateDerivative_postcomp c E p hp
      ((hEs p).2 c hc hp)] at hder
    exact hder (congrArg Q hzw)
  refine ⟨E, hEim, ?_, v, ?_, Real.pi / 2, ?_⟩
  · intro x y hxy
    apply hi
    apply compress_injective
    have h := congrArg Q hxy
    exact (congrFun hQ x).symm.trans (h.trans (congrFun hQ y))
  · intro h
    have hh := congrFun h (Fin.last q)
    simp [v] at hh
  · intro x
    apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)).mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [E, v]
      positivity
    · simpa [E, v, compress, Real.norm_eq_abs] using
        (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan (e x j)).le,
          (Real.arctan_lt_pi_div_two (e x j)).le⟩)

/-- Proper weak Whitney embedding in exactly 2n+1 dimensions, with the
ordinary boundary, empty and dimension-zero cases included. -/
theorem exists_proper_embedding :
    Specs.SmoothManifolds.Ch04.ProperWhitney.exists_proper_embeddingType.{u} := by
  intro n a M _ S
  obtain ⟨q, e, he, hi, _, _⟩ := FiniteProperEmbedding.exists_finite_proper_embedding S
  obtain ⟨ρ, hρ, hρnonneg, hρproper⟩ := exists_smooth_exhaustion S
  obtain ⟨E, hE, hEi, htube⟩ := exists_immersion_with_axis S e he hi ρ hρ
  obtain ⟨g, hg, hgi, v, hv, C, hC⟩ := reduce_with_axis S ρ (q + 1) E hE hEi htube
  have hproper : IsProper g := proper_of_bounded_remainder g
    (continuous_iff_continuousAt.mpr (fun x => (hg.1 x).1)) ρ hρproper hρnonneg v hv C hC
  exact ⟨g, hg, hgi, hproper,
    FiniteProperEmbedding.homeomorph_of_proper_injective S g hg.1 hgi hproper⟩

end SmoothManifolds.ProperWhitney
