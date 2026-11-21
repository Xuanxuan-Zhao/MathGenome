import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.CompactEmbeddingApproximation
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.ProperWhitney

namespace SmoothManifolds.CompactEmbeddingApproximation
open ModelData AtlasData FiniteRegularityData GoodProjectionData ProjectiveData MapClassData Set
open scoped Topology
universe u
variable {n q d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

/-- Restriction to the first coordinates. -/
noncomputable def firstCoordinates {q r : ℕ} (h : q ≤ r) : Euclidean r →L[ℝ] Euclidean q :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (i.castLE h))

@[simp] theorem prefix_apply {q r : ℕ} (h : q ≤ r) (z : Euclidean r) (i : Fin q) :
    firstCoordinates h z i = z (i.castLE h) := rfl

theorem prefix_norm_le {q r : ℕ} (h : q ≤ r) (z : Euclidean r) :
    ‖firstCoordinates h z‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro i
  exact norm_le_pi_norm z (i.castLE h)

/-- Projection along the line represented by (y,1), onto the first d coordinates. -/
noncomputable def oblique (y : Euclidean d) : Euclidean (d + 1) →L[ℝ] Euclidean d :=
  firstCoordinates (Nat.le_succ d) -
    (ContinuousLinearMap.proj (Fin.last d)).smulRight y

@[simp] theorem oblique_apply (y : Euclidean d) (z : Euclidean (d + 1)) (i : Fin d) :
    oblique y z i = z i.castSucc - z (Fin.last d) * y i := rfl

/-- Vanishing under the oblique projection implies vanishing under the
orthogonal projection along the same line. -/
theorem projection_eq_of_oblique_eq (L : RealProjectiveSpace d)
    (hL : L ∈ projectiveLocus (Fin.last d)) (z w : Euclidean (d + 1))
    (h : oblique (projectiveRatios (Fin.last d) L) z =
      oblique (projectiveRatios (Fin.last d) L) w) :
    projection L z = projection L w := by
  apply sub_eq_zero.mp
  rw [← (projection L).map_sub]
  apply (GoodProjections.projection_eq_zero_iff L _).mpr
  have hmem := GoodProjections.insertOne_ratios_mem (Fin.last d)
    (directionSubmodule L) L (show directionSubmodule L ≤ directionSubmodule L from le_rfl) hL
  have heq : z - w = (z (Fin.last d) - w (Fin.last d)) •
      insertOne (Fin.last d) (projectiveRatios (Fin.last d) L) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [insertOne]
    · have hh := congrFun h j
      simp only [oblique_apply] at hh
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, insertOne,
        Fin.insertNth_last', Fin.snoc_castSucc]
      nlinarith
  rw [heq]
  exact (directionSubmodule L).smul_mem _ hmem

/-- Density supplies a good line with arbitrarily small slope over the last axis. -/
theorem exists_small_good_slope (S : SmoothManifold n a M)
    (e : M → Euclidean (d + 1)) (he : IsEuclideanImmersion S e)
    (hi : Function.Injective e) (hd : 2 * n + 1 < d + 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : RealProjectiveSpace d, L ∈ projectiveLocus (Fin.last d) ∧
      ‖projectiveRatios (Fin.last d) L‖ < δ ∧
      Function.Injective (projectedMap L e) ∧
      IsEuclideanImmersion S (fun p => (projectedMap L e p).val) := by
  let O := projectiveLocus (Fin.last d) ∩
    projectiveRatios (Fin.last d) ⁻¹' Metric.ball 0 δ
  have hopen : IsOpen O := (Projective.continuousOn_ratios _).isOpen_inter_preimage
    (Projective.isOpen_locus _) Metric.isOpen_ball
  have hne : O.Nonempty := by
    refine ⟨projectiveInverse (Fin.last d) 0, Projective.inverse_mem_locus _ _, ?_⟩
    simp [Metric.mem_ball, hδ]
  have hbot : (⊥ : Submodule ℝ (Euclidean (d + 1))) ≠ ⊤ := by
    exact bot_ne_top
  obtain ⟨L, hO, hgood⟩ :=
    (GoodProjections.injective_immersion_directions_dense S e he hi hd ⊥ hbot).inter_open_nonempty
      O hopen hne
  exact ⟨L, hO.1, by simpa [Metric.mem_ball, dist_zero_right] using hO.2,
    hgood.2.1, hgood.2.2⟩

/-- Remove one coordinate with an arbitrarily small uniform error. -/
theorem approximate_one_projection [CompactSpace M] (S : SmoothManifold n a M)
    (e : M → Euclidean (d + 1)) (he : IsEuclideanImmersion S e)
    (hi : Function.Injective e) (hd : 2 * n + 1 < d + 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : M → Euclidean d, IsEuclideanImmersion S g ∧ Function.Injective g ∧
      ∀ p, ‖g p - firstCoordinates (Nat.le_succ d) (e p)‖ < ε := by
  have hc : Continuous e := continuous_iff_continuousAt.mpr (fun p => (he.1 p).1)
  obtain ⟨B, hB⟩ := (isCompact_range hc).isBounded.exists_norm_le
  let C := max B 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  obtain ⟨L, hL, hslope, hLi, hLim⟩ :=
    exists_small_good_slope S e he hi hd (ε / C) (div_pos hε hC)
  let P := oblique (projectiveRatios (Fin.last d) L)
  have hP (z w : Euclidean (d + 1)) (h : P z = P w) :
      projection L z = projection L w := projection_eq_of_oblique_eq L hL z w h
  have hg : IsEuclideanImmersion S (fun p => P (e p)) := by
    refine ⟨GoodProjections.smoothEuclidean_postcomp S e he.1 P, ?_⟩
    intro c hc p hp z w hzw
    apply hLim.2 c hc p hp
    change coordinateDerivative c (fun x => projection L (e x)) p z =
      coordinateDerivative c (fun x => projection L (e x)) p w
    rw [GoodProjections.coordinateDerivative_postcomp c e p hp
      ((he.1 p).2 c hc hp)] at hzw ⊢
    exact hP _ _ hzw
  refine ⟨fun p => P (e p), hg, ?_, ?_⟩
  · intro p p' hpp
    exact hLi (Subtype.ext (hP _ _ hpp))
  · intro p
    have hlast : ‖e p (Fin.last d)‖ ≤ C :=
      (norm_le_pi_norm (e p) _).trans ((hB _ (mem_range_self p)).trans (le_max_left B 1))
    have herr : P (e p) - firstCoordinates (Nat.le_succ d) (e p) =
        -(e p (Fin.last d) • projectiveRatios (Fin.last d) L) := by
      ext i
      change e p i.castSucc - e p (Fin.last d) * projectiveRatios (Fin.last d) L i -
        e p i.castSucc = -(e p (Fin.last d) * projectiveRatios (Fin.last d) L i)
      ring
    rw [herr, norm_neg, norm_smul]
    calc
      ‖e p (Fin.last d)‖ * ‖projectiveRatios (Fin.last d) L‖ ≤
          C * ‖projectiveRatios (Fin.last d) L‖ :=
        mul_le_mul_of_nonneg_right hlast (norm_nonneg _)
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hslope hC
      _ = ε := mul_div_cancel₀ ε hC.ne'

/-- Successive small projections approximate the original coordinate restriction.
The error is split at each stage, so no limiting argument is needed. -/
theorem approximate_prefix [CompactSpace M] (S : SmoothManifold n a M)
    (hq : 2 * n + 1 ≤ q) :
    ∀ k : ℕ, ∀ e : M → Euclidean (q + k),
      IsEuclideanImmersion S e → Function.Injective e →
      ∀ ε : ℝ, 0 < ε → ∃ g : M → Euclidean q,
        IsEuclideanImmersion S g ∧ Function.Injective g ∧
        ∀ p, ‖g p - firstCoordinates (Nat.le_add_right q k) (e p)‖ < ε := by
  intro k
  induction k with
  | zero =>
    intro e he hi ε hε
    refine ⟨e, he, hi, ?_⟩
    intro p
    have hid : firstCoordinates (Nat.le_add_right q 0) (e p) = e p := rfl
    rw [hid, sub_self, norm_zero]
    exact hε
  | succ k ih =>
    intro e he hi ε hε
    obtain ⟨e', he', hi', herr⟩ := approximate_one_projection S e he hi
      (Nat.lt_succ_of_le (hq.trans (Nat.le_add_right q k))) (ε / 2) (by positivity)
    obtain ⟨g, hg, hgi, hgerr⟩ := ih e' he' hi' (ε / 2) (by positivity)
    refine ⟨g, hg, hgi, ?_⟩
    intro p
    have hcomp : firstCoordinates (Nat.le_add_right q k)
        (firstCoordinates (Nat.le_succ (q + k)) (e p)) =
        firstCoordinates (Nat.le_add_right q (k + 1)) (e p) := by
      ext i
      rfl
    have hsmall : ‖firstCoordinates (Nat.le_add_right q k) (e' p) -
        firstCoordinates (Nat.le_add_right q (k + 1)) (e p)‖ < ε / 2 := by
      rw [← hcomp, ← map_sub]
      exact (prefix_norm_le _ _).trans_lt (herr p)
    calc
      ‖g p - firstCoordinates (Nat.le_add_right q (k + 1)) (e p)‖ ≤
          ‖g p - firstCoordinates (Nat.le_add_right q k) (e' p)‖ +
          ‖firstCoordinates (Nat.le_add_right q k) (e' p) -
            firstCoordinates (Nat.le_add_right q (k + 1)) (e p)‖ := by
            simpa only [dist_eq_norm] using dist_triangle (g p)
              (firstCoordinates (Nat.le_add_right q k) (e' p))
              (firstCoordinates (Nat.le_add_right q (k + 1)) (e p))
      _ < ε / 2 + ε / 2 := add_lt_add (hgerr p) hsmall
      _ = ε := by ring

/-- Compact smooth manifolds, including ordinary boundary, empty and
zero-dimensional sources, admit arbitrarily close embeddings in the fixed target. -/
theorem compact_embedding_approximation :
    Specs.SmoothManifolds.Ch04.CompactEmbeddingApproximation.compact_embedding_approximationType.{u} := by
  intro n q a M _ _ S hq f hf ε hε
  obtain ⟨e, he, hi, _, _⟩ := ProperWhitney.exists_proper_embedding S
  let E : M → Euclidean (q + (2 * n + 1)) := fun p => Fin.append (f p) (e p)
  let Q : Euclidean (q + (2 * n + 1)) →L[ℝ] Euclidean (2 * n + 1) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (i.natAdd q))
  have hQ : (fun p => Q (E p)) = e := by
    funext p i
    simp [Q, E]
  have hEs : IsSmoothEuclidean S E := by
    apply (FiniteProperEmbedding.smoothEuclidean_iff_scalar S E).mpr
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [E] using (FiniteProperEmbedding.smoothEuclidean_iff_scalar S f).mp hf j
    · simpa [E] using (FiniteProperEmbedding.smoothEuclidean_iff_scalar S e).mp he.1 j
  have hEim : IsEuclideanImmersion S E := by
    refine ⟨hEs, ?_⟩
    intro c hc p hp z w hzw
    have hder := he.2 c hc p hp
    rw [← hQ, GoodProjections.coordinateDerivative_postcomp c E p hp
      ((hEs p).2 c hc hp)] at hder
    exact hder (congrArg Q hzw)
  have hEi : Function.Injective E := by
    intro p p' hpp
    apply hi
    have hh := congrArg Q hpp
    simpa only [← congrFun hQ p, ← congrFun hQ p'] using hh
  obtain ⟨g, hg, hgi, herr⟩ := approximate_prefix S hq (2 * n + 1) E hEim hEi ε hε
  refine ⟨g, hg, hgi, ?_, ?_⟩
  · apply FiniteProperEmbedding.homeomorph_of_proper_injective S g hg.1 hgi
    intro K hK
    exact (hK.isClosed.preimage
      (continuous_iff_continuousAt.mpr (fun p => (hg.1 p).1))).isCompact
  · intro p
    have hprefix : firstCoordinates (Nat.le_add_right q (2 * n + 1)) (E p) = f p := by
      ext i
      simp [E]
    simpa only [hprefix] using herr p

end SmoothManifolds.CompactEmbeddingApproximation
