import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.LcsStrongSeparation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06OpenSeparation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06StrongSeparation
import Mathlib.Tactic.Linarith

/-! Compact--closed separation, `fa2:p1:lcs-strong-separation`.

Open separation follows from the accepted TVS theorem, reversing the two sets
and the sign when the second set is open. For compact--closed separation the
accepted uniform gap, after sign reversal, gives f(k) + δ ≤ f(c). Compactness
attains the supremum at some k; taking the infimum on C retains δ > 0.
The complexification preserves the real part pointwise.
-/
namespace ExpandedFA.P1
universe u

theorem real_tvs_open_separation :
    Specs.ExpandedFA.P1.LcsStrongSeparation.realOpenType.{u} := by
  intro E _ _ _ _ _ A B hA hB hvA hvB hd ho
  rcases ho with ho | ho
  · obtain ⟨h, α, hn, ha, hb⟩ :=
      C06.real_open_convex_separation A B hA hB hvA hvB hd ho
    exact ⟨h, α, hn, fun a haA => (ha a haA).le, hb,
      fun a haA b hbB => (ha a haA).trans_le (hb b hbB)⟩
  · obtain ⟨h, α, hn, hb, ha⟩ :=
      C06.real_open_convex_separation B A hB hA hvB hvA hd.symm ho
    refine ⟨-h, -α, neg_ne_zero.mpr hn, ?_, ?_, ?_⟩
    · intro a haA
      exact neg_le_neg (ha a haA)
    · intro b hbB
      exact neg_le_neg (hb b hbB).le
    · intro a haA b hbB
      exact neg_lt_neg ((hb b hbB).trans_le (ha a haA))

theorem complex_tvs_open_separation :
    Specs.ExpandedFA.P1.LcsStrongSeparation.complexOpenType.{u} := by
  intro E _ _ _ _ _ A B hA hB hvA hvB hd ho
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  obtain ⟨h, α, hn, ha, hb, hab⟩ :=
    real_tvs_open_separation A B hA hB hvA hvB hd ho
  let f : E →L[ℂ] ℂ := StrongDual.extendRCLike h
  have hre : ∀ x, h x = (f x).re := fun x =>
    (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x).symm
  refine ⟨h, f, α, hn, ?_, hre, ha, hb, hab⟩
  intro hf
  apply hn
  ext x
  simpa only [hf, zero_apply, Complex.zero_re] using hre x

theorem real_lcs_compact_closed_separation :
    Specs.ExpandedFA.P1.LcsStrongSeparation.realCompactClosedType.{u} := by
  intro E _ _ _ _ _ _ _ K C hK hC hk hc hvK hvC hd
  obtain ⟨h, δ, hn, hδ, hgap⟩ := C06.real_locally_convex_compact_convex_separation
    C K hC hc hvC hK hk hvK hd.symm
  let f : E →L[ℝ] ℝ := -h
  have hgap' : ∀ k ∈ K, ∀ c ∈ C, f k + δ ≤ f c := by
    intro k hk c hc
    have := hgap c hc k hk
    simp only [f, neg_apply]
    linarith
  obtain ⟨k, hkK, hmax⟩ := hk.exists_sSup_image_eq hK f.continuous.continuousOn
  have hbC : BddBelow (f '' C) := by
    refine ⟨f k + δ, ?_⟩
    rintro y ⟨c, hcC, rfl⟩
    exact hgap' k hkK c hcC
  have hinf : f k + δ ≤ sInf (f '' C) := by
    apply le_csInf (hC.image f)
    rintro y ⟨c, hcC, rfl⟩
    exact hgap' k hkK c hcC
  refine ⟨f, neg_ne_zero.mpr hn, (hk.image f.continuous).bddAbove, hbC,
    ⟨k, hkK, hmax.symm⟩, ?_⟩
  rw [hmax]
  linarith

theorem complex_lcs_compact_closed_separation :
    Specs.ExpandedFA.P1.LcsStrongSeparation.complexCompactClosedType.{u} := by
  intro E _ _ _ _ _ _ _ K C hK hC hk hc hvK hvC hd
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  obtain ⟨h, hn, hbK, hbC, hmax, hsep⟩ :=
    real_lcs_compact_closed_separation K C hK hC hk hc hvK hvC hd
  let f : E →L[ℂ] ℂ := StrongDual.extendRCLike h
  have hre : (fun x => (f x).re) = h := by
    funext x
    exact StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x
  have hfn : f ≠ 0 := by
    intro hf
    apply hn
    ext x
    have := congrFun hre x
    simpa only [hf, zero_apply, Complex.zero_re] using this.symm
  refine ⟨f, hfn, ?_, ?_, ?_, ?_⟩
  · simpa only [hre] using hbK
  · simpa only [hre] using hbC
  · obtain ⟨k, hkK, hkeq⟩ := hmax
    refine ⟨k, hkK, ?_⟩
    rw [hre]
    exact (congrFun hre k).trans hkeq
  · simpa only [hre] using hsep

end ExpandedFA.P1
