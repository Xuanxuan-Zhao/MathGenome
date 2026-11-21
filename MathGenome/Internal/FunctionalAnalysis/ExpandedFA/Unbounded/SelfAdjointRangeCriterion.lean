import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SelfAdjointRangeCriterion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosabilityAndDoubleAdjoint
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section
universe u
namespace ExpandedFA.Unbounded
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Negating a linear map does not change its range. This identifies the
shared zI−S shift with the paper's S−zI expression, on the same domain. -/
theorem range_shift_eq_range_sub (S : Operator ℂ H H) (z : ℂ) :
    range (shift z S) = (S.toFun - z • S.domain.subtype).range := by
  change (z • S.domain.subtype - S.toFun).range = _
  rw [← neg_sub S.toFun (z • S.domain.subtype), LinearMap.range_neg]

/-- The nonreal lower bound, also valid before assuming closedness. -/
theorem IsSymmetric.nonreal_lower_bound {S : Operator ℂ H H} (hS : IsSymmetric S)
    (z : ℂ) (x : S.domain) : |z.im| * ‖(x : H)‖ ≤ ‖S x - z • (x : H)‖ := by
  have h := hS.norm_sub_sq z x
  have hn := sq_nonneg ‖S x - (z.re : ℂ) • (x : H)‖
  have ha := abs_nonneg z.im
  have hx := norm_nonneg (x : H)
  have hr := norm_nonneg (S x - z • (x : H))
  nlinarith [sq_nonneg (|z.im| * ‖(x : H)‖ + ‖S x - z • (x : H)‖)]

/-- The conjugate parameter records the conjugate-linear first argument. -/
theorem orthogonal_shift_range (S : Operator ℂ H H) (hS : DenselyDefined S) (z : ℂ) :
    (range (shift z S)).orthogonal = deficiencySpace S (starRingEnd ℂ z) := by
  ext y
  rw [mem_deficiencySpace_iff]
  change (∀ a ∈ (shift z S).toFun.range, inner ℂ a y = 0) ↔ _
  constructor
  · intro h
    have he : ∀ x : S.domain,
        inner ℂ (S x) y = inner ℂ (x : H) ((starRingEnd ℂ z) • y) := by
      intro x
      have hx := h ((shift z S) x) ⟨x, rfl⟩
      change inner ℂ (z • (x : H) - S x) y = 0 at hx
      rw [inner_sub_left, inner_smul_left] at hx
      rw [inner_smul_right]
      exact (sub_eq_zero.mp hx).symm
    have hy := (mem_hilbertAdjoint_domain_iff S hS y).mpr ⟨_, he⟩
    exact ⟨hy, hilbertAdjoint_apply_eq S hS ⟨y, hy⟩ _ he⟩
  · rintro ⟨hy, he⟩ a ⟨x, rfl⟩
    change inner ℂ (z • (x : H) - S x) y = 0
    rw [inner_sub_left, inner_smul_left,
      hilbertAdjoint_inner S hS ⟨y, hy⟩ x, he, inner_smul_right, sub_self]

/-- The range of every nonreal shift of a closed symmetric operator is closed.
We apply the lower bound on the complete graph, whose norm controls both
coordinates, rather than equipping the ambient-norm domain with completeness. -/
theorem closed_symmetric_shift_range_isClosed (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) (z : ℂ) (hz : z.im ≠ 0) :
    _root_.IsClosed (range (shift z S) : Set H) := by
  let : CompleteSpace S.graph := hc.isComplete.completeSpace_coe
  let F : S.graph →L[ℂ] H :=
    (z • ContinuousLinearMap.fst ℂ H H - ContinuousLinearMap.snd ℂ H H).comp
      S.graph.subtypeL
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  have hbound (p : S.graph) :
      ‖p‖ ≤ (1 + (1 + ‖z‖) * |z.im|⁻¹) * ‖F p‖ := by
    obtain ⟨x, hx, hb⟩ := S.mem_graph_iff.mp p.prop
    have hlo : |z.im| * ‖p.val.1‖ ≤ ‖F p‖ := by
      have h := hS.nonreal_lower_bound z x
      rw [hx, hb, norm_sub_rev] at h
      exact h
    have hfst : ‖p.val.1‖ ≤ |z.im|⁻¹ * ‖F p‖ := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hlo)
    have hsnd : ‖p.val.2‖ ≤ ‖F p‖ + ‖z‖ * ‖p.val.1‖ := by
      calc
        ‖p.val.2‖ = ‖z • p.val.1 - F p‖ := by
          congr 1
          change p.val.2 = z • p.val.1 - (z • p.val.1 - p.val.2)
          abel
        _ ≤ ‖z • p.val.1‖ + ‖F p‖ := norm_sub_le _ _
        _ = ‖F p‖ + ‖z‖ * ‖p.val.1‖ := by rw [norm_smul, add_comm]
    have hh := mul_le_mul_of_nonneg_left hfst (norm_nonneg z)
    change max ‖p.val.1‖ ‖p.val.2‖ ≤ _
    apply max_le
    · have : 0 ≤ ‖z‖ * |z.im|⁻¹ * ‖F p‖ := by positivity
      nlinarith [norm_nonneg (F p)]
    · have : 0 ≤ |z.im|⁻¹ * ‖F p‖ := by positivity
      nlinarith
  let C : NNReal := ⟨1 + (1 + ‖z‖) * |z.im|⁻¹, by positivity⟩
  have hanti : AntilipschitzWith C F := F.antilipschitz_of_bound hbound
  have hr : Set.range F = (range (shift z S) : Set H) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx, hb⟩ := S.mem_graph_iff.mp p.prop
      refine ⟨x, ?_⟩
      change z • (x : H) - S x = z • p.val.1 - p.val.2
      rw [hx, hb]
    · rintro ⟨x, rfl⟩
      exact ⟨⟨((x : H), S x), S.mem_graph_iff.mpr ⟨x, rfl, rfl⟩⟩, rfl⟩
  rw [← hr]
  exact hanti.isClosed_range F.uniformContinuous

/-- Closed range upgrades the orthogonality identity to equality of ranges. -/
theorem closed_symmetric_shift_range (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) (z : ℂ) (hz : z.im ≠ 0) :
    range (shift z S) = (deficiencySpace S (starRingEnd ℂ z)).orthogonal := by
  rw [← orthogonal_shift_range S hS.1 z,
    Submodule.orthogonal_orthogonal_eq_closure,
    (closed_symmetric_shift_range_isClosed S hc hS z hz).submodule_topologicalClosure_eq]

/-- Ran(S+i)=N₊⊥ and Ran(S−i)=N₋⊥, with the shared zI−S convention. -/
theorem closed_symmetric_signed_ranges (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) :
    range (shift (-Complex.I) S) = (deficiencyPlus S).orthogonal ∧
    range (shift Complex.I S) = (deficiencyMinus S).orthogonal := by
  change range (shift (-Complex.I) S) = (deficiencySpace S Complex.I).orthogonal ∧
    range (shift Complex.I S) = (deficiencySpace S (-Complex.I)).orthogonal
  constructor
  · simpa only [map_neg, Complex.conj_I, neg_neg] using
      closed_symmetric_shift_range S hc hS (-Complex.I) (by simp)
  · simpa only [Complex.conj_I] using
      closed_symmetric_shift_range S hc hS Complex.I (by simp)

/-- A self-adjoint operator has no nonreal adjoint eigenvectors. -/
theorem IsSelfAdjoint.deficiencySpace_eq_bot {S : Operator ℂ H H}
    (hS : IsSelfAdjoint S) (z : ℂ) (hz : z.im ≠ 0) : deficiencySpace S z = ⊥ := by
  have hd : DenselyDefined S := hS.1
  have heq : S = hilbertAdjoint S := hS.2
  have hs : IsSymmetric S := by
    change DenselyDefined S ∧ S ≤ hilbertAdjoint S
    exact ⟨hd, heq.le⟩
  have hadj : IsSymmetric (hilbertAdjoint S) := by rw [← heq]; exact hs
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  obtain ⟨hy, he⟩ := (mem_deficiencySpace_iff S z y).mp hy
  have h := hadj.nonreal_lower_bound z ⟨y, hy⟩
  rw [he, sub_self, norm_zero] at h
  have hp : 0 < |z.im| := abs_pos.mpr hz
  have hn : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp hn

/-- Surjectivity at conjugate parameters forces equality of the entire domains.
This implication needs symmetry, but does not require closedness. -/
theorem isSelfAdjoint_of_conjugate_shift_ranges (S : Operator ℂ H H)
    (hS : IsSymmetric S) (z : ℂ)
    (hz : range (shift z S) = ⊤)
    (hzc : range (shift (starRingEnd ℂ z) S) = ⊤) : IsSelfAdjoint S := by
  have hd : DenselyDefined S := hS.1
  have hi : S ≤ hilbertAdjoint S := hS.2
  have hk : deficiencySpace S z = ⊥ := by
    have h := orthogonal_shift_range S hd (starRingEnd ℂ z)
    simpa only [RCLike.conj_conj, hzc, Submodule.top_orthogonal_eq_bot] using h.symm
  have hdom : (hilbertAdjoint S).domain ≤ S.domain := by
    intro x hx
    have hm : z • x - hilbertAdjoint S ⟨x, hx⟩ ∈ range (shift z S) := by
      rw [hz]; exact Submodule.mem_top
    obtain ⟨y, hy⟩ := hm
    change z • (y : H) - S y = z • x - hilbertAdjoint S ⟨x, hx⟩ at hy
    let ya : (hilbertAdjoint S).domain := ⟨y, hi.1 y.prop⟩
    have hya : hilbertAdjoint S ya = S y := (hi.2 rfl).symm
    have he : hilbertAdjoint S (⟨x, hx⟩ - ya) = z • (x - (y : H)) := by
      rw [(hilbertAdjoint S).map_sub, hya]
      rw [smul_sub]
      exact (sub_eq_sub_iff_sub_eq_sub.mp hy.symm).symm
    have hw : x - (y : H) ∈ deficiencySpace S z :=
      (mem_deficiencySpace_iff S z _).mpr
        ⟨(hilbertAdjoint S).domain.sub_mem hx ya.prop, he⟩
    rw [hk, Submodule.mem_bot] at hw
    have hxy : x = (y : H) := sub_eq_zero.mp hw
    rw [hxy]
    exact y.prop
  change DenselyDefined S ∧ S = hilbertAdjoint S
  exact ⟨hd, LinearPMap.eq_of_le_of_domain_eq hi (le_antisymm hi.1 hdom)⟩

/-- The two zero deficiency spaces are equivalent to self-adjointness. -/
theorem closed_symmetric_selfAdjoint_iff_deficiencies (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) :
    IsSelfAdjoint S ↔ deficiencyPlus S = ⊥ ∧ deficiencyMinus S = ⊥ := by
  constructor
  · intro hs
    exact ⟨hs.deficiencySpace_eq_bot Complex.I (by simp),
      hs.deficiencySpace_eq_bot (-Complex.I) (by simp)⟩
  · rintro ⟨hp, hm⟩
    obtain ⟨hrp, hrm⟩ := closed_symmetric_signed_ranges S hc hS
    rw [hp, Submodule.bot_orthogonal_eq_top] at hrp
    rw [hm, Submodule.bot_orthogonal_eq_top] at hrm
    apply isSelfAdjoint_of_conjugate_shift_ranges S hS (-Complex.I) hrp
    simpa only [map_neg, Complex.conj_I, neg_neg] using hrm

/-- The self-adjoint range criterion for a closed densely defined symmetric S. -/
theorem closed_symmetric_selfAdjoint_iff_ranges (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) :
    IsSelfAdjoint S ↔ range (shift (-Complex.I) S) = ⊤ ∧ range (shift Complex.I S) = ⊤ := by
  constructor
  · intro hs
    obtain ⟨hp, hm⟩ := (closed_symmetric_selfAdjoint_iff_deficiencies S hc hS).mp hs
    obtain ⟨hrp, hrm⟩ := closed_symmetric_signed_ranges S hc hS
    rw [hp, Submodule.bot_orthogonal_eq_top] at hrp
    rw [hm, Submodule.bot_orthogonal_eq_top] at hrm
    exact ⟨hrp, hrm⟩
  · rintro ⟨hp, hm⟩
    apply isSelfAdjoint_of_conjugate_shift_ranges S hS (-Complex.I) hp
    simpa only [map_neg, Complex.conj_I, neg_neg] using hm

end ExpandedFA.Unbounded
