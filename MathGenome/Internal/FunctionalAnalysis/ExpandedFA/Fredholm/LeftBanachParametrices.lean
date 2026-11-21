import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.LeftBanachParametrices
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RightBanachParametrices

noncomputable section
namespace ExpandedFA.Fredholm
open scoped Topology
universe u v w
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

open LeftBanachParametricesSpec

/-- A section on the actual range and a bounded range projection give an
exact left inverse with defect projecting onto the actual kernel. -/
theorem exact_left_projection_of_condition [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : LeftCondition T) : ExactProjectionLeftInverse T := by
  let := hT.2.2
  obtain ⟨W, hW⟩ := range_section_of_complemented_kernel T hT.1
    (Submodule.ClosedComplemented.of_finiteDimensional _)
  obtain ⟨p, hp⟩ := hT.2.1
  let U := W.comp p
  have hTU : ∀ x, T (U (T x)) = T x := by
    intro x
    change T (W (p (T x))) = T x
    rw [hW]
    exact congrArg Subtype.val (hp ⟨T x, T.mem_range_self x⟩)
  let Q := ContinuousLinearMap.id 𝕜 E - U.comp T
  have hQx : ∀ x, Q x = x - U (T x) := fun _ => rfl
  have hQr : Q.range = T.ker := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change T (Q y) = 0
      rw [hQx, map_sub, hTU, sub_self]
    · intro hx
      refine ⟨x, ?_⟩
      change x - U (T x) = x
      rw [show T x = 0 from hx, map_zero, sub_zero]
  refine ⟨U, Q, ?_, ?_, ?_, ?_⟩
  · ext x
    change Q (Q x) = Q x
    rw [hQx (Q x), show T (Q x) = 0 from (show Q x ∈ T.ker by
      rw [← hQr]; exact Q.mem_range_self x),
      map_zero, sub_zero]
  · rw [hQr]
    infer_instance
  · dsimp [Q]
    abel
  · rw [hQr]

/-- The projection defect supplies a bounded projection onto the entire
range: first project onto T(ker Q), then correct the finite-dimensional
remaining image T(range Q). -/
theorem left_condition_of_projection_left_inverse
    (T : E →L[𝕜] F) (U : F →L[𝕜] E) (Q : E →L[𝕜] E)
    (hQ : Q.comp Q = Q) [FiniteDimensional 𝕜 Q.range]
    (hUT : U.comp T = ContinuousLinearMap.id 𝕜 E - Q) : LeftCondition T := by
  have hUTx : ∀ x, U (T x) = x - Q x := fun x =>
    congrArg (fun A : E →L[𝕜] E => A x) hUT
  have hQQ : ∀ x, Q (Q x) = Q x := fun x =>
    congrArg (fun A : E →L[𝕜] E => A x) hQ
  have hk : T.ker ≤ Q.range := by
    intro x hx
    refine ⟨x, ?_⟩
    have h := hUTx x
    rw [show T x = 0 from hx, map_zero] at h
    exact (sub_eq_zero.mp h.symm).symm
  have hfinite : FiniteDimensional 𝕜 T.ker := Submodule.finiteDimensional_of_le hk
  let A := T.comp ((ContinuousLinearMap.id 𝕜 E - Q).comp U)
  have hAT : ∀ x, A (T x) = T x - T (Q x) := by
    intro x
    change T (U (T x) - Q (U (T x))) = T x - T (Q x)
    rw [hUTx, map_sub Q, hQQ, sub_self, sub_zero, map_sub]
  let f := T.comp Q
  have hf : FiniteDimensional 𝕜 f.range := by
    change FiniteDimensional 𝕜 (T.toLinearMap.comp Q.toLinearMap).range
    rw [LinearMap.range_comp]
    infer_instance
  let := hf
  obtain ⟨r, hr⟩ := Submodule.ClosedComplemented.of_finiteDimensional f.range
  let a : F →L[𝕜] T.range := A.codRestrict T.range (fun y => ⟨_, rfl⟩)
  have hle : f.range ≤ T.range := LinearMap.range_comp_le_range _ _
  let j : f.range →L[𝕜] T.range := f.range.subtypeL.codRestrict T.range (fun y => hle y.property)
  let p : F →L[𝕜] T.range := a + j.comp (r.comp (ContinuousLinearMap.id 𝕜 F - A))
  have hp : ∀ y : T.range, p y = y := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    change A (T x) + (r (T x - A (T x)) : F) = T x
    have heq : T x - A (T x) = f x := by rw [hAT]; dsimp [f]; abel
    rw [heq]
    have hrx := congrArg Subtype.val (hr ⟨f x, f.mem_range_self x⟩)
    change (r (f x) : F) = f x at hrx
    rw [hrx, hAT]
    change T x - T (Q x) + T (Q x) = T x
    abel
  have hc : T.range.ClosedComplemented := ⟨p, hp⟩
  exact ⟨hc.isClosed, hc, hfinite⟩

/-- Regularize the Fredholm product I+K on the left, then compose the
regularizer with the original approximate inverse. -/
theorem projection_left_inverse_of_compact [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : CompactLeftInverse T) : ProjectionLeftInverse T := by
  obtain ⟨S, K, hK, hST⟩ := hT
  have hneg : Compactness.IsCompactLinearMap (-K).toLinearMap := by
    simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_neg] using
      Compactness.compact_smul (-1 : 𝕜) K.toLinearMap hK
  have hD : IsFredholm (ContinuousLinearMap.id 𝕜 E + K) := by
    simpa only [sub_neg_eq_add] using identity_sub_compact_isFredholm (-K) hneg
  let := hD.2.2
  have hc : LeftCondition (ContinuousLinearMap.id 𝕜 E + K) :=
    ⟨hD.1, Submodule.ClosedComplemented.of_finiteDimensional_quotient hD.1, hD.2.1⟩
  obtain ⟨R, Q, hQ, hfinite, hR, _⟩ := exact_left_projection_of_condition _ hc
  refine ⟨R.comp S, Q, hQ, hfinite, ?_⟩
  rw [ContinuousLinearMap.comp_assoc, hST, hR]

/-- A finite-rank projection gives a compact defect with the opposite sign. -/
theorem compact_left_inverse_of_projection
    (T : E →L[𝕜] F) (hT : ProjectionLeftInverse T) : CompactLeftInverse T := by
  obtain ⟨U, Q, _, hfinite, hUT⟩ := hT
  let := hfinite
  have hc : Compactness.IsCompactLinearMap (-Q).toLinearMap := by
    simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_neg] using
      Compactness.compact_smul (-1 : 𝕜) Q.toLinearMap (compact_of_finiteDimensional_range Q)
  exact ⟨U, -Q, hc, by simpa only [sub_eq_add_neg] using hUT⟩

/-- The three left-sided conditions for arbitrary real or complex Banach
spaces, retaining the substantive range complement in the reverse direction. -/
theorem left_banach_parametrices : LeftBanachParametricesSpec.LeftEquivalences := by
  intro 𝕜 _ E F _ _ _ _ _ _ T
  have hforward (hT : LeftCondition T) : ProjectionLeftInverse T := by
    obtain ⟨U, Q, hQ, hfinite, hUT, _⟩ := exact_left_projection_of_condition T hT
    exact ⟨U, Q, hQ, hfinite, hUT⟩
  have hback (hT : ProjectionLeftInverse T) : LeftCondition T := by
    obtain ⟨U, Q, hQ, hfinite, hUT⟩ := hT
    let := hfinite
    exact left_condition_of_projection_left_inverse T U Q hQ hUT
  exact ⟨⟨fun h => compact_left_inverse_of_projection T (hforward h),
    fun h => hback (projection_left_inverse_of_compact T h)⟩, ⟨hforward, hback⟩⟩

/-- The projection can be chosen with rank exactly the actual kernel dimension,
including when this dimension is zero. -/
theorem left_banach_parametrices_exact_defect : LeftBanachParametricesSpec.ExactDefect := by
  intro 𝕜 _ E F _ _ _ _ _ _ T hT
  exact exact_left_projection_of_condition T hT

end ExpandedFA.Fredholm
