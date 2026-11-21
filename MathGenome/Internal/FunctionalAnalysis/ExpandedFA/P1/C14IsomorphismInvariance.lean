import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14IsomorphismInvariance
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Reflexive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04DualMaps

/-!
Reflexivity under Banach isomorphisms (`fa2:p1:c14:isomorphism-invariance`).
Pull a bidual element back along the transpose of the inverse, represent it
by evaluation in the reflexive space, and then evaluate at T′f. This is the
elementwise form of J_F T = T″ J_E, using continuous scalar-linear duals.
-/

namespace ExpandedFA.P1.C14IsomorphismInvariance

universe u v w

/-- A bounded linear right inverse suffices to transport canonical
surjectivity. Completeness is not needed for this argument. -/
theorem reflexivity_of_right_inverse (𝕜 : Type u) (E : Type v) (F : Type w)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (S : F →L[𝕜] E)
    (hTS : ∀ y, T (S y) = y) (hE : C04CanonicalMap.IsReflexive 𝕜 E) :
    C04CanonicalMap.IsReflexive 𝕜 F := by
  intro ξ
  obtain ⟨x, hx⟩ := hE (ξ.comp (C04Annihilators.banachTranspose 𝕜 F E S))
  refine ⟨T x, ?_⟩
  ext f
  have h := congrArg (fun η : C04Dual.Bidual 𝕜 E => η (f.comp T)) hx
  change f (T x) = ξ ((f.comp T).comp S) at h
  have hid : (f.comp T).comp S = f := by
    ext y
    change f (T (S y)) = f y
    rw [hTS]
  exact h.trans (congrArg ξ hid)

/-- The normed-space version also applies to equivalent norms. -/
theorem reflexivity_iff_of_equiv (𝕜 : Type u) (E : Type v) (F : Type w)
    [RCLike 𝕜] [nE : NormedAddCommGroup E] [nF : NormedAddCommGroup F]
    [sE : NormedSpace 𝕜 E] [sF : NormedSpace 𝕜 F]
    (T : E ≃L[𝕜] F) :
    C04CanonicalMap.IsReflexive 𝕜 E ↔ C04CanonicalMap.IsReflexive 𝕜 F := by
  constructor
  · exact reflexivity_of_right_inverse 𝕜 E F T.toContinuousLinearMap
      T.symm.toContinuousLinearMap T.apply_symm_apply
  · exact reflexivity_of_right_inverse 𝕜 F E T.symm.toContinuousLinearMap
      T.toContinuousLinearMap T.symm_apply_apply

theorem reflexivity_isomorphism_invariance :
    Spec.IsomorphismInvariance.{u, v, w} := by
  intro 𝕜 E F _ _ _ _ _ _ _ T
  exact reflexivity_iff_of_equiv 𝕜 E F T

theorem reflexivity_equivalent_norms :
    Spec.EquivalentNormsInvariance.{u, v} := by
  intro 𝕜 E _ _ m p q hp hq C D hC hD
  let nE := C01Norm.normedGroup p hp
  let nF := C01Norm.normedGroup q hq
  let sE := @NormedSpace.mk 𝕜 E _ nE.toSeminormedAddCommGroup m
    (fun a x => (map_smul_eq_mul p a x).le)
  let sF := @NormedSpace.mk 𝕜 E _ nF.toSeminormedAddCommGroup m
    (fun a x => (map_smul_eq_mul q a x).le)
  let T := @LinearEquiv.toContinuousLinearEquivOfBounds
    𝕜 𝕜 E E _ _ nE.toSeminormedAddCommGroup nF.toSeminormedAddCommGroup
    m m (RingHom.id 𝕜) (RingHom.id 𝕜) _ _ (LinearEquiv.refl 𝕜 E) C D hC hD
  exact reflexivity_iff_of_equiv 𝕜 E E (nE := nE) (nF := nF) (sE := sE) (sF := sF) T

end ExpandedFA.P1.C14IsomorphismInvariance
