import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.EmbeddedComparison
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.BoundaryCones

namespace SmoothManifolds
open DifferentialData
open Set Filter
open scoped Topology

abbrev euclideanChart := EmbeddedData.euclideanChart
abbrev IsParametrizationAt := @EmbeddedData.IsParametrizationAt
abbrev HasFullRankParametrizations := @EmbeddedData.HasFullRankParametrizations
abbrev faceHyperplane := EmbeddedData.faceHyperplane

@[simp] theorem euclideanChart_val (N : ℕ) (x : Euclidean N) :
    (euclideanChart N x).val = x := rfl

@[simp] theorem euclideanChart_source (N : ℕ) :
    (euclideanChart N).source = univ := rfl

private theorem euclidean_singleton_atlas (N : ℕ) :
    IsContDiffAtlas (⊤ : ℕ∞) {euclideanChart N} := by
  constructor
  · intro p
    exact ⟨euclideanChart N, rfl, mem_univ p⟩
  · intro e he d hd
    have heq : e = euclideanChart N := Set.mem_singleton_iff.mp he
    have hdq : d = euclideanChart N := Set.mem_singleton_iff.mp hd
    subst e
    subst d
    constructor <;> intro x hx
    all_goals
      refine ⟨univ, isOpen_univ, mem_univ _, id, contDiff_id.contDiffOn, ?_⟩
      intro y hy hyU
      rfl

theorem standardEuclidean_exists :
    Specs.SmoothManifolds.Tangent.EmbeddedComparison.standardEuclidean_existsType := by
  intro N
  have hA := euclidean_singleton_atlas N
  exact ⟨⟨⟨inferInstance, inferInstance, {euclideanChart N}, hA.1⟩,
    ⟨maximalExtension (⊤ : ℕ∞) {euclideanChart N}, maximalExtension_isMaximal hA⟩⟩,
    subset_maximalExtension hA rfl⟩

private theorem embedded_smooth {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (j : M → Euclidean N)
    (hj : HasFullRankParametrizations S j)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (hT : euclideanChart N ∈ T.smoothStructure.val) : IsSmoothMap S T j := by
  intro p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨V, H, hH, _⟩ := hj p e he hp
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 T.smoothStructure.property.1 j p).mpr
  have hecont : ContinuousAt (fun y : M => (e y).val) p :=
    (continuous_subtype_val.continuousAt).comp (e.continuousAt hp)
  have hcont : ContinuousAt (fun y => H (e y).val) p :=
    ((hH.2.2.1.contDiffAt (hH.1.mem_nhds hH.2.1)).continuousAt).comp (f := fun y : M => (e y).val) hecont
  exact ⟨hcont.congr hH.2.2.2, e, he, euclideanChart N, hT, hp, mem_univ _,
    V, hH.1, hH.2.1, H, hH.2.2.1, hH.2.2.2⟩

theorem embedded_differential_exists :
    Specs.SmoothManifolds.Tangent.EmbeddedComparison.embedded_differential_existsType := by
  intro n N a M _ S j hj T hT
  have hs := embedded_smooth S j hj T hT
  refine ⟨hs, ?_⟩
  intro p
  obtain ⟨L, hL, _⟩ := differential_exists S T j hs p
  exact ⟨L, coordinateDerivationEquiv T (j p) (euclideanChart N) hT (mem_univ _), hL,
    coordinateDerivationEquiv_isChartCoordinates T (j p) (euclideanChart N) hT (mem_univ _)⟩

/-- The coordinate representative of the inclusion is the parametrization. -/
theorem embedded_differential_jacobian {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (j : M → Euclidean N)
    (hj : HasFullRankParametrizations S j)
    (T : SmoothManifold N .euclidean (Euclidean N))
    (hT : euclideanChart N ∈ T.smoothStructure.val) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (F : TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N)
    (hL : IsDifferential S T j p L)
    (hF : IsChartCoordinates T (j p) (euclideanChart N) F)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (V : Set (Euclidean n)) (H : Euclidean n → Euclidean N)
    (hH : IsParametrizationAt j e p V H) (v : TangentSpace S p) :
    F (L v) = fderiv ℝ H (e p).val (coordinateDerivationEquiv S p e he hp v) := by
  exact differential_jacobian S T j (embedded_smooth S j hj T hT) p L hL
    e (euclideanChart N) he hT hp (mem_univ _)
    (coordinateDerivationEquiv S p e he hp) F
    (coordinateDerivationEquiv_isChartCoordinates S p e he hp) hF
    V H hH.1 hH.2.1 hH.2.2.1 hH.2.2.2 v

/-- Rank equal to the dimension of the source is exactly injectivity. -/
theorem fullRank_injective {n N : ℕ} (D : Euclidean n →ₗ[ℝ] Euclidean N)
    (hD : Module.finrank ℝ (LinearMap.range D) = n) : Function.Injective D := by
  have hdim : Module.finrank ℝ (Euclidean n) = n := by
    simp [Euclidean, ModelData.Euclidean]
  have hn := D.finrank_range_add_finrank_ker
  rw [hD, hdim] at hn
  have hk : Module.finrank ℝ (LinearMap.ker D) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

theorem embedded_tangent_comparison :
    Specs.SmoothManifolds.Tangent.EmbeddedComparison.embedded_tangent_comparisonType := by
  intro n N a M _ S j hj T hT p L F hL hF
  obtain ⟨d, hd, hpd⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨W, G, hG, hGrank⟩ := hj p d hd hpd
  have hJ : Function.Injective (F.toLinearMap.comp L) := by
    intro v w hvw
    apply (coordinateDerivationEquiv S p d hd hpd).injective
    apply fullRank_injective _ hGrank
    exact (embedded_differential_jacobian S j hj T hT p L F hL hF d hd hpd W G hG v).symm.trans
      (hvw.trans (embedded_differential_jacobian S j hj T hT p L F hL hF d hd hpd W G hG w))
  refine ⟨fun v w hvw => hJ (congrArg F hvw), hJ, ?_⟩
  intro e he hp V H hH
  let E := coordinateDerivationEquiv S p e he hp
  let D := (fderiv ℝ H (e p).val).toLinearMap
  have hformula (v) : F (L v) = D (E v) :=
    embedded_differential_jacobian S j hj T hT p L F hL hF e he hp V H hH v
  have hrange : LinearMap.range (F.toLinearMap.comp L) = LinearMap.range D := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨E v, (hformula v).symm⟩
    · rintro ⟨w, rfl⟩
      refine ⟨E.symm w, ?_⟩
      change F (L (E.symm w)) = D w
      rw [hformula, E.apply_symm_apply]
  refine ⟨hrange, ?_⟩
  let I := (LinearEquiv.ofInjective (F.toLinearMap.comp L) hJ).trans
    (LinearEquiv.ofEq _ _ hrange)
  exact ⟨I, fun _ => rfl⟩

theorem embedded_image_independent :
    Specs.SmoothManifolds.Tangent.EmbeddedComparison.embedded_image_independentType := by
  intro n N a M _ S j hj p e d he hd hp hpd V W H K hH hK
  obtain ⟨T, hT⟩ := standardEuclidean_exists N
  obtain ⟨_, hex⟩ := embedded_differential_exists S j hj T hT
  obtain ⟨L, F, hL, hF⟩ := hex p
  have hc := (embedded_tangent_comparison S j hj T hT p L F hL hF).2.2
  exact ((hc e he hp V H hH).1).symm.trans (hc d hd hpd W K hK).1

theorem embedded_boundary_tangent :
    Specs.SmoothManifolds.Tangent.EmbeddedComparison.embedded_boundary_tangentType := by
  intro n N M _ S j hj T hT
  obtain ⟨B, hB, _⟩ := boundary_tangent_identification S
  refine ⟨B, hB, ?_⟩
  intro p L F K hL hF hK
  refine ⟨differential_comp B S T Subtype.val j hB.1
    (embedded_smooth S j hj T hT) p K L hK hL, ?_⟩
  intro e he hp V H hH
  let E := coordinateDerivationEquiv S p.val e he hp
  let J := F.toLinearMap.comp L
  let D := (fderiv ℝ H (e p.val).val).toLinearMap
  have hformula (v) : J v = D (E v) :=
    embedded_differential_jacobian S j hj T hT p.val L F hL hF e he hp V H hH v
  have hJ : Function.Injective J :=
    (embedded_tangent_comparison S j hj T hT p.val L F hL hF).2.1
  have hKimage := (boundary_inclusion_image S B hB p e he hp K hK E
    (coordinateDerivationEquiv_isChartCoordinates S p.val e he hp)).2
  constructor
  · ext z
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨E (K v), ?_, (hformula (K v)).symm⟩
      exact (hKimage (K v)).mp ⟨v, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hzero : w (Fin.last n) = 0 := hw
      obtain ⟨v, hv⟩ := (hKimage (E.symm w)).mpr (by simpa using hzero)
      refine ⟨v, ?_⟩
      change J (K v) = D w
      rw [hv, hformula, E.apply_symm_apply]
  · apply lt_of_le_of_ne (LinearMap.range_comp_le_range K J)
    intro heq
    let w : TangentSpace S p.val := E.symm (Pi.single (Fin.last n) 1)
    have hmem : J w ∈ LinearMap.range (J.comp K) := by
      rw [heq]
      exact ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    have heqv : K v = w := hJ hv
    have hzero := (hKimage (K v)).mp ⟨v, rfl⟩
    rw [heqv] at hzero
    simpa [w] using hzero

end SmoothManifolds
