import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorAffine
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeBoundarySupport
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Separation
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.SupportProperSeparation

open Set
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry

/-- In full dimension use geometric Hahn–Banach; in a proper affine hull use
an annihilator of its direction space. -/
theorem ambientBoundary_support : Specs.ambientBoundary_support.{u} := by
  intro E _ _ _ _ C hne hclosed hC x hx
  have hxC : x ∈ C := hclosed.closure_eq ▸ hx.1
  have hxi : x ∉ interior C := hx.2
  by_cases hfull : affineSpan ℝ C = ⊤
  · obtain ⟨l, hl, hle⟩ := geometric_hahn_banach_of_nonempty_interior_point hC hxi
      (hC.interior_nonempty_iff_affineSpan_eq_top.mpr hfull)
    refine ⟨l.toLinearMap, ?_, hle⟩
    intro h
    apply hl
    ext y
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f y) h
  · have hdir : (affineSpan ℝ C).direction < ⊤ :=
      lt_top_iff_ne_top.mpr (fun h => hfull
        ((AffineSubspace.direction_eq_top_iff_of_nonempty
          (hne.mono (subset_affineSpan ℝ C))).mp h))
    obtain ⟨l, hl, hker⟩ := (affineSpan ℝ C).direction.exists_le_ker_of_lt_top hdir
    refine ⟨l, hl, fun y hy => ?_⟩
    have hz : l (y - x) = 0 := hker (AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hxC))
    rw [map_sub] at hz
    linarith

/-- The earlier relative support lemma is exactly the relative assertion. -/
theorem relativeBoundary_support_corollary : Specs.relativeBoundary_support_corollary.{u} :=
  relativeBoundary_support

/-- Separating a convex set from zero properly, including the case where zero
belongs to its closure. -/
theorem separate_zero_of_not_mem_relativeInterior
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (hQ : Convex ℝ Q) (hne : Q.Nonempty)
    (hzero : (0 : E) ∉ relativeInterior Q) :
    ∃ l : E →ₗ[ℝ] ℝ, (∀ y ∈ Q, 0 ≤ l y) ∧ ∃ y ∈ Q, 0 < l y := by
  by_cases hz : (0 : E) ∈ closure Q
  · have hzr : (0 : E) ∉ relativeInterior (closure Q) := by
      rwa [relativeInterior_closure Q hQ hne]
    obtain ⟨n, _hn, hnle, y, hy, hny⟩ := relativeBoundary_support (closure Q)
      (hne.mono subset_closure) isClosed_closure hQ.closure 0 hz hzr
    obtain ⟨g, hg⟩ := n.exists_extend
    have heval (y : E) (hy : y ∈ closure Q) :
        g y = n ⟨y - 0, AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ (closure Q) hy)
          (subset_affineSpan ℝ (closure Q) hz)⟩ := by
      have h := congrArg (fun f => f ⟨y - 0,
        AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ (closure Q) hy)
          (subset_affineSpan ℝ (closure Q) hz)⟩) hg
      simpa using h
    have hle : ∀ z ∈ closure Q, g z ≤ 0 := fun z hz => heval z hz ▸ hnle z hz
    have hlt : g y < 0 := heval y hy ▸ hny
    have hstrict : ∃ z ∈ Q, g z < 0 := by
      by_contra! h
      have hcl : closure Q ⊆ {z | 0 ≤ g z} :=
        closure_minimal h (isClosed_Ici.preimage g.continuous_of_finiteDimensional)
      exact (not_lt_of_ge (hcl hy)) hlt
    obtain ⟨z, hz, hgz⟩ := hstrict
    exact ⟨-g, fun z hz => by simpa using neg_nonneg.mpr (hle z (subset_closure hz)),
      z, hz, by simpa using neg_pos.mpr hgz⟩
  · obtain ⟨f, r, hr, hf⟩ := geometric_hahn_banach_point_closed hQ.closure isClosed_closure hz
    have hr0 : 0 < r := by simpa using hr
    obtain ⟨y, hy⟩ := hne
    exact ⟨f.toLinearMap, fun y hy => (hr0.trans (hf y (subset_closure hy))).le,
      y, hy, hr0.trans (hf y (subset_closure hy))⟩

/-- Proper separation is equivalent to disjointness of the relative interiors.
The difference set is the linear image of D × C under subtraction. -/
theorem proper_separation : Specs.proper_separation.{u} := by
  intro E _ _ _ _ _ _ _ C D hneC hneD hC hD
  let : IsNormableSpace ℝ E := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup E := IsNormableSpace.toSeminormedAddCommGroup ℝ E
  let : NormedSpace ℝ E := IsNormableSpace.toNormedSpace ℝ E
  let : NormedAddCommGroup E := { MetricSpace.ofT0PseudoMetricSpace E with
    dist_eq := dist_eq_norm_neg_add }
  let A : E × E →ₗ[ℝ] E := LinearMap.fst ℝ E E - LinearMap.snd ℝ E E
  let Q : Set E := A '' (D ×ˢ C)
  have hQ : Convex ℝ Q := (hD.prod hC).linear_image A
  have hneQ : Q.Nonempty := (hneD.prod hneC).image A
  have hri : relativeInterior Q = A '' (relativeInterior D ×ˢ relativeInterior C) := by
    change relativeInterior (A.toAffineMap '' (D ×ˢ C)) = _
    rw [relativeInterior_affine_image A.toAffineMap _ (hD.prod hC) (hneD.prod hneC),
      relativeInterior_product D C hD hneD hC hneC]
    rfl
  have hzero : (0 : E) ∈ relativeInterior Q ↔
      (relativeInterior C ∩ relativeInterior D).Nonempty := by
    rw [hri]
    constructor
    · rintro ⟨⟨d,c⟩, ⟨hd,hc⟩, heq⟩
      have hdc : d = c := sub_eq_zero.mp heq
      exact ⟨c, hc, hdc ▸ hd⟩
    · rintro ⟨x, hxC, hxD⟩
      exact ⟨(x,x), ⟨hxD,hxC⟩, sub_self x⟩
  constructor
  · intro hdis
    change relativeInterior C ∩ relativeInterior D = ∅ at hdis
    have hzr : (0 : E) ∉ relativeInterior Q := by
      rw [hzero, hdis]
      exact not_nonempty_empty
    obtain ⟨l, hle, q, hq, hstrict⟩ :=
      separate_zero_of_not_mem_relativeInterior Q hQ hneQ hzr
    have hpair (c : E) (hc : c ∈ C) (d : E) (hd : d ∈ D) : l c ≤ l d := by
      have h := hle (d-c) ⟨(d,c), ⟨hd,hc⟩, rfl⟩
      rw [map_sub] at h
      linarith
    obtain ⟨⟨d,c⟩, ⟨hd,hc⟩, rfl⟩ := hq
    refine ⟨l, hpair, c, hc, d, hd, ?_⟩
    change 0 < l (d-c) at hstrict
    rw [map_sub] at hstrict
    linarith
  · rintro ⟨l, hle, c, hc, d, hd, hstrict⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hzri : (0 : E) ∈ relativeInterior Q := hzero.mpr ⟨x, hx⟩
    have hn : ∀ q ∈ Q, 0 ≤ l q := by
      rintro _ ⟨⟨d,c⟩, ⟨hd,hc⟩, rfl⟩
      change 0 ≤ l (d-c)
      rw [map_sub]
      exact sub_nonneg.mpr (hle c hc d hd)
    obtain ⟨s, hs, hext⟩ := (mem_relativeInterior_iff_extendible Q hQ 0
      (intrinsicInterior_subset hzri)).mp hzri (d-c) ⟨(d,c), ⟨hd,hc⟩, rfl⟩
    have h := hn _ hext
    simp only [zero_add, zero_sub, map_smul, map_neg, map_sub, smul_eq_mul] at h
    nlinarith

end VariationalNotes.ConvexGeometry
