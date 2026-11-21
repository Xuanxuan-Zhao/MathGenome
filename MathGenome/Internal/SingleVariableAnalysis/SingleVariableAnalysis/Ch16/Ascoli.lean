import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.AscoliSubsequence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.HeineCantor
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Ascoli

/-!
The family part of K03.16.ascoli. Necessity is proved using finite
sup-norm nets, with explicit bounds and a common continuity radius.
Sufficiency uses the upstream scalar subsequence theorem and closedness,
then the metric equivalence of compactness and sequential compactness.
-/
namespace SingleVariableAnalysis
open scoped Topology
open Filter

theorem ascoli_compactFamily_finite_net :
    Specs.SingleVariableAnalysis.Ch16.Ascoli.compactFamilyFiniteNet := by
  intro E _ K _ F hF ε hε
  classical
  obtain ⟨t, htF, ht, hcover⟩ := hF.finite_cover_balls hε
  refine ⟨ht.toFinset, fun h hh => htF (ht.mem_toFinset.mp hh), ?_⟩
  intro f hf
  obtain ⟨h, hh, hdist⟩ := Set.mem_iUnion₂.mp (hcover hf)
  exact ⟨h, ht.mem_toFinset.mpr hh, by
    simpa only [Metric.mem_ball, dist_eq_norm] using hdist⟩

theorem ascoli_boundedFamily_of_finite_net :
    Specs.SingleVariableAnalysis.Ch16.Ascoli.boundedFamilyOfFiniteNet := by
  intro E _ K _ F ⟨t, hnet⟩
  classical
  refine ⟨1 + ∑ h ∈ t, ‖h‖,
    add_nonneg zero_le_one (Finset.sum_nonneg fun h _ => norm_nonneg h), ?_⟩
  intro f hf x
  obtain ⟨h, hh, hfh⟩ := hnet f hf
  have hsum : ‖h‖ ≤ ∑ g ∈ t, ‖g‖ :=
    Finset.single_le_sum (fun g _ => norm_nonneg g) hh
  calc
    ‖f x‖ ≤ ‖f x - h x‖ + ‖h x‖ := by
      calc
        ‖f x‖ = ‖(f x - h x) + h x‖ := by rw [sub_add_cancel]
        _ ≤ ‖f x - h x‖ + ‖h x‖ := norm_add_le _ _
    _ ≤ ‖f - h‖ + ‖h‖ := add_le_add
      ((f - h).norm_coe_le_norm x) (h.norm_coe_le_norm x)
    _ ≤ 1 + ∑ g ∈ t, ‖g‖ := add_le_add hfh.le hsum

/-- The minimum of finitely many continuity radii is still positive.
The empty set of centers uses radius 1. -/
theorem ascoli_finite_centers_modulus {E : Type} [NormedAddCommGroup E]
    (K : Set ℝ) [CompactSpace K] (t : Finset C(K, E))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ t, ∀ x y : K,
      dist x y < δ → ‖h x - h y‖ < ε := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert h t _ ih =>
    obtain ⟨δ, hδ, ht⟩ := ih
    obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous h.continuous) ε hε
    refine ⟨min r δ, lt_min hr hδ, ?_⟩
    intro g hg x y hxy
    rcases Finset.mem_insert.mp hg with rfl | hg
    · simpa only [dist_eq_norm] using hmod (hxy.trans_le (min_le_left _ _))
    · exact ht g hg x y (hxy.trans_le (min_le_right _ _))

theorem ascoli_equicontinuousFamily_of_finite_nets :
    Specs.SingleVariableAnalysis.Ch16.Ascoli.equicontinuousFamilyOfFiniteNets := by
  intro E _ K _ F hnets ε hε
  obtain ⟨t, ht⟩ := hnets (ε / 3) (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := ascoli_finite_centers_modulus K t (ε / 3) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy f hf
  obtain ⟨h, hh, hfh⟩ := ht f hf
  have hx := ((f - h).norm_coe_le_norm x).trans_lt hfh
  have hy := ((f - h).norm_coe_le_norm y).trans_lt hfh
  have hm := hmod h hh x y hxy
  simp only [ContinuousMap.sub_apply] at hx hy
  calc
    ‖f x - f y‖ ≤ ‖f x - h x‖ + ‖h x - h y‖ + ‖h y - f y‖ := by
      simpa only [dist_eq_norm] using dist_triangle4 (f x) (h x) (h y) (f y)
    _ < ε := by
      rw [norm_sub_rev (h y) (f y)]
      linarith

/-- Finite nets give both a common value bound and a common continuity radius. -/
theorem ascoli_compactFamily_necessary {E : Type} [NormedAddCommGroup E]
    (K : Set ℝ) [CompactSpace K] (F : Set C(K, E)) (hF : IsCompact F) :
    IsClosed F ∧ UniformlyBoundedFamily K F ∧
      UniformlyEquicontinuousFamily K F := by
  have hnets : ∀ ε : ℝ, 0 < ε → ∃ t : Finset C(K, E),
      ∀ f ∈ F, ∃ h ∈ t, ‖f - h‖ < ε := by
    intro ε hε
    obtain ⟨t, _, ht⟩ := ascoli_compactFamily_finite_net K F hF ε hε
    exact ⟨t, ht⟩
  exact ⟨hF.isClosed, ascoli_boundedFamily_of_finite_net K F (hnets 1 zero_lt_one),
    ascoli_equicontinuousFamily_of_finite_nets K F hnets⟩

theorem real_ascoli_compact_iff :
    Specs.SingleVariableAnalysis.Ch16.Ascoli.realAscoliCompactIff := by
  intro K _ F
  constructor
  · intro hF
    obtain ⟨hclosed, hb, heq⟩ := ascoli_compactFamily_necessary K F hF
    exact ⟨hclosed, hb, fun x ε hε => by
      obtain ⟨δ, hδ, hmod⟩ := heq ε hε
      exact ⟨δ, hδ, fun y hy f hf => hmod y x hy f hf⟩⟩
  · rintro ⟨hclosed, hb, heq⟩
    apply isCompact_iff_isSeqCompact.mpr
    intro u hu
    have hb' : UniformlyBoundedFamily K (Set.range u) := by
      obtain ⟨M, hM, hbound⟩ := hb
      exact ⟨M, hM, by rintro f ⟨n, rfl⟩ x; exact hbound (u n) (hu n) x⟩
    have heq' : PointwiseEquicontinuousFamily K (Set.range u) := by
      intro x ε hε
      obtain ⟨δ, hδ, hmod⟩ := heq x ε hε
      refine ⟨δ, hδ, ?_⟩
      rintro y hy f ⟨n, rfl⟩
      exact hmod y hy (u n) (hu n)
    obtain ⟨D, _, _, φ, hφ, _, _, f, _, hlim⟩ :=
      real_ascoli_subsequence K u hb' heq'
    have ht : Tendsto (u ∘ φ) atTop (𝓝 f) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hlim
    exact ⟨f, hclosed.mem_of_tendsto ht (Eventually.of_forall fun n => hu (φ n)),
      φ, hφ, ht⟩

theorem complex_ascoli_compact_iff :
    Specs.SingleVariableAnalysis.Ch16.Ascoli.complexAscoliCompactIff := by
  intro K _ F
  constructor
  · intro hF
    obtain ⟨hclosed, hb, heq⟩ := ascoli_compactFamily_necessary K F hF
    exact ⟨hclosed, hb, fun x ε hε => by
      obtain ⟨δ, hδ, hmod⟩ := heq ε hε
      exact ⟨δ, hδ, fun y hy f hf => hmod y x hy f hf⟩⟩
  · rintro ⟨hclosed, hb, heq⟩
    apply isCompact_iff_isSeqCompact.mpr
    intro u hu
    have hb' : UniformlyBoundedFamily K (Set.range u) := by
      obtain ⟨M, hM, hbound⟩ := hb
      exact ⟨M, hM, by rintro f ⟨n, rfl⟩ x; exact hbound (u n) (hu n) x⟩
    have heq' : PointwiseEquicontinuousFamily K (Set.range u) := by
      intro x ε hε
      obtain ⟨δ, hδ, hmod⟩ := heq x ε hε
      refine ⟨δ, hδ, ?_⟩
      rintro y hy f ⟨n, rfl⟩
      exact hmod y hy (u n) (hu n)
    obtain ⟨D, _, _, φ, hφ, _, _, f, _, hlim⟩ :=
      complex_ascoli_subsequence K u hb' heq'
    have ht : Tendsto (u ∘ φ) atTop (𝓝 f) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hlim
    exact ⟨f, hclosed.mem_of_tendsto ht (Eventually.of_forall fun n => hu (φ n)),
      φ, hφ, ht⟩

end SingleVariableAnalysis
