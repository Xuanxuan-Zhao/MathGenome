import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08Splitting
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02Projections
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08BoundedInverse

/-! One-sided inverses from topological complements, and complements from
bounded idempotents. All subspace norms and topologies are inherited. -/

namespace ExpandedFA.P1.C08Splitting

universe u v w

/-- Construct the right inverse from any given topological complement.
The only completeness used here is that of E, F, and the closed subspace N. -/
theorem right_inverse_of_topological_complement
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : Function.Surjective T)
    (N : Submodule 𝕜 E) (hN : Submodule.IsTopCompl T.ker N) :
    ∃ S : F →L[𝕜] E, T.comp S = ContinuousLinearMap.id 𝕜 F := by
  have hclosed : IsClosed (N : Set E) :=
    (C02Projections.topological_direct_sum_closed 𝕜 E T.ker N hN).2
  let : CompleteSpace N := hclosed.isComplete.completeSpace_coe
  let U : N →L[𝕜] F := T.domRestrict N
  have hUinj : Function.Injective U := by
    exact LinearMap.injective_domRestrict_iff.mpr hN.isCompl.disjoint.symm
  have hUsurj : Function.Surjective U := by
    intro y
    obtain ⟨x, hx⟩ := hT y
    obtain ⟨m, n, hmn, _⟩ := Submodule.existsUnique_add_of_isCompl hN.isCompl x
    refine ⟨n, ?_⟩
    change T (n : E) = y
    have hm : T (m : E) = 0 := m.property
    calc
      T (n : E) = T ((m : E) + n) := by rw [map_add, hm, zero_add]
      _ = y := by rw [hmn, hx]
  obtain ⟨V, _, hUV, _⟩ := C08BoundedInverse.bounded_inverse 𝕜 N F U ⟨hUinj, hUsurj⟩
  refine ⟨N.subtypeL.comp V, ?_⟩
  ext y
  exact hUV y

/-- The right-inverse equivalence in Theorem `fa2:p1:c08:splitting`. -/
theorem right_inverse_criterion : Spec.RightInverseCriterion.{u, v, w} := by
  intro 𝕜 E F _ _ _ _ _ _ _ T hT
  constructor
  · rintro ⟨S, hTS⟩
    have hTS_apply : ∀ y : F, T (S y) = y := fun y => DFunLike.congr_fun hTS y
    have hP : (S.comp T).comp (S.comp T) = S.comp T := by
      ext x
      exact congrArg S (hTS_apply (T x))
    have hker : (S.comp T).ker = T.ker := by
      ext x
      change S (T x) = 0 ↔ T x = 0
      constructor
      · intro hx
        calc
          T x = T (S (T x)) := (hTS_apply (T x)).symm
          _ = 0 := by rw [hx, map_zero]
      · intro hx
        rw [hx, map_zero]
    obtain ⟨hcomp, _⟩ :=
      C02Projections.bounded_projection_direct_sum 𝕜 E (S.comp T) hP
    exact ⟨(S.comp T).range, hker ▸ hcomp.symm⟩
  · rintro ⟨N, hN⟩
    exact right_inverse_of_topological_complement T hT N hN

/-- The left-inverse equivalence in Theorem `fa2:p1:c08:splitting`. -/
theorem left_inverse_criterion : Spec.LeftInverseCriterion.{u, v, w} := by
  intro 𝕜 E F _ _ _ _ _ _ _ T hT
  constructor
  · rintro ⟨S, hST⟩
    have hST_apply : ∀ x : E, S (T x) = x := fun x => DFunLike.congr_fun hST x
    let Q : F →L[𝕜] F := T.comp S
    have hQ : Q.comp Q = Q := by
      ext y
      change T (S (T (S y))) = T (S y)
      rw [hST_apply]
    have hRange : Q.range = T.range := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨S z, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨T x, congrArg T (hST_apply x)⟩
    obtain ⟨hcomp, hclosed, _, _, _⟩ :=
      C02Projections.bounded_projection_direct_sum 𝕜 F Q hQ
    rw [hRange] at hcomp hclosed
    exact ⟨hclosed, Q.ker, hcomp⟩
  · rintro ⟨hclosed, N, hN⟩
    let : CompleteSpace T.range := hclosed.isComplete.completeSpace_coe
    let Tr : E →L[𝕜] T.range := T.rangeRestrict
    have hTr : Function.Bijective Tr := by
      constructor
      · intro x y hxy
        exact hT (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨x, hx⟩ := y.property
        exact ⟨x, Subtype.ext hx⟩
    obtain ⟨R, hRT, _, _⟩ :=
      C08BoundedInverse.bounded_inverse 𝕜 E T.range Tr hTr
    refine ⟨R.comp (T.range.projectionOntoL N hN), ?_⟩
    ext x
    change R (T.range.projectionOntoL N hN (Tr x : F)) = x
    rw [Submodule.projectionOntoL_apply_left]
    exact hRT x

end ExpandedFA.P1.C08Splitting
