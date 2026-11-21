import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Compactness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.ZeroExtension
import MathGenome.Internal.FourierSobolev.P102.Sobolev.Rellich

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TopologicalSpace Set
open scoped ENNReal
namespace VariationalNotes.Sobolev

variable {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)

/-- A finite family of relatively compact scalar coordinate images gives
relative compactness in the Euclidean-valued Lp space. -/
theorem compact_lp_of_coordinates {X : Type*} (f : X → ValueLp Ω m p) (A : Set X)
    (h : ∀ i : Fin m, IsCompact (closure ((fun x => coordinateLp Ω p i (f x)) '' A))) :
    IsCompact (closure (f '' A)) := by
  let K := Set.univ.pi fun i : Fin m =>
    closure ((fun x => coordinateLp Ω p i (f x)) '' A)
  have hK : IsCompact K := isCompact_univ_pi h
  have hc := hK.image (coordinateLpEquiv (ι := Fin m) Ω p).symm.continuous
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨coordinateLpEquiv Ω p (f x), ?_, ?_⟩
  · intro i _
    exact subset_closure ⟨x, hx, rfl⟩
  · exact (coordinateLpEquiv Ω p).symm_apply_apply (f x)

/-- Vector-valued Rellich, transported through the continuous coordinate bridge. -/
theorem compactness_lipschitz : CompactnessExpected.Lipschitz := by
  intro n e Ω hΩ m p A hA
  apply compact_lp_of_coordinates Ω p (value Ω m p) A
  intro i
  obtain ⟨I, _, hI, hc⟩ := P102.Sobolev.Rellich.same_exponent n e Ω hΩ ℝ
    p.ennreal (by exact ENNReal.ofReal_ne_top)
  let C : W1p Ω m p →L[ℝ] P102.U4.Sobolev ℝ Ω 1 p.ennreal :=
    (ContinuousLinearMap.proj i).comp (coordinateEquiv Ω p).toContinuousLinearMap
  have hEq : (fun u : W1p Ω m p => I (C u)) =
      fun u => coordinateLp Ω p i (value Ω m p u) := by
    funext u
    apply Lp.ext
    exact (hI (C u)).trans (by
      rw [show C u = toCoordinates Ω p u i from rfl, toCoordinates_value])
  have h := hc (C '' A) (C.lipschitzWith.isBounded_image hA)
  rwa [Set.image_image, hEq] at h

/-- Zero-boundary compactness on a bounded open set, before affine translation.
The sole support bound is boundedness of Ω; no boundary geometry enters. -/
theorem compactness_zero {d : ℕ} (hd : 0 < d) (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (m : ℕ) (p : Exponent)
    (A : Set (W1pZero Ω m p)) (hA : Bornology.IsBounded A) :
    IsCompact (closure ((fun u : W1pZero Ω m p => value Ω m p u.val) '' A)) := by
  apply compact_lp_of_coordinates Ω p (fun u : W1pZero Ω m p => value Ω m p u.val) A
  intro i
  let C : W1pZero Ω m p →L[ℝ] P102.Sobolev.WholeSobolev d ℝ p.ennreal :=
    ((ContinuousLinearMap.proj i).comp
      (coordinateEquiv (m := m) (⊤ : Opens (Domain d)) p).toContinuousLinearMap).comp
      (zeroExtensionLI Ω p).toContinuousLinearMap
  have hval (u : W1pZero Ω m p) : P102.U4.sobolevUnderlying (C u) =
      P102.U4.lpZeroExtension Ω p.ennreal (coordinateLp Ω p i (value Ω m p u.val)) := by
    change P102.U4.sobolevUnderlying
      (toCoordinates ⊤ p (zeroExtensionLinear Ω p u) i) = _
    rw [toCoordinates_value, zeroExtensionLinear_value, coordinate_fieldZeroExtension]
  have hc := P102.Sobolev.supported_compactness hd p.ennreal
    (by exact ENNReal.ofReal_ne_top) (C '' A) (C.lipschitzWith.isBounded_image hA)
    (Ω : Set (Domain d)) hΩ (by
      rintro _ ⟨u, hu, rfl⟩
      rw [hval]
      filter_upwards [P102.Sobolev.wholeLp_ae
        (P102.U4.lpZeroExtension Ω p.ennreal (coordinateLp Ω p i (value Ω m p u.val))),
        P102.U4.lpZeroExtension_ae Ω p.ennreal (coordinateLp Ω p i (value Ω m p u.val))]
          with x hx hy
      intro hxΩ
      rw [hx, hy]
      exact Set.indicator_of_notMem hxΩ _)
  let R := ExpandedFA.Sobolev.lpRestrict (E := ℝ) p.ennreal volume (Ω : Set (Domain d))
  have hR : Continuous R := (ExpandedFA.Sobolev.lpRestrict_lipschitz _).continuous
  have hres (u : W1pZero Ω m p) :
      R (P102.Sobolev.wholeLp (P102.U4.sobolevUnderlying (C u))) =
        coordinateLp Ω p i (value Ω m p u.val) := by
    rw [hval]
    apply Lp.ext
    filter_upwards [ExpandedFA.Sobolev.lpRestrict_representative
      (Ω : Set (Domain d))
      (P102.Sobolev.wholeLp (P102.U4.lpZeroExtension Ω p.ennreal
        (coordinateLp Ω p i (value Ω m p u.val)))),
      ae_restrict_of_ae (P102.Sobolev.wholeLp_ae
        (P102.U4.lpZeroExtension Ω p.ennreal (coordinateLp Ω p i (value Ω m p u.val)))),
      ae_restrict_of_ae (P102.U4.lpZeroExtension_ae Ω p.ennreal
        (coordinateLp Ω p i (value Ω m p u.val))),
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hy hz hxΩ
    exact hx.trans (hy.trans (hz.trans (Set.indicator_of_mem hxΩ _)))
  have hEq : R '' ((fun v => P102.Sobolev.wholeLp (P102.U4.sobolevUnderlying v)) '' (C '' A)) =
      (fun u : W1pZero Ω m p => coordinateLp Ω p i (value Ω m p u.val)) '' A := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext u
    exact hres u
  have hi : (fun u : W1pZero Ω m p => coordinateLp Ω p i (value Ω m p u.val)) '' A ⊆
      R '' closure ((fun v => P102.Sobolev.wholeLp (P102.U4.sobolevUnderlying v)) '' (C '' A)) := by
    rw [← hEq]
    exact image_mono subset_closure
  exact (hc.image hR).of_isClosed_subset isClosed_closure
    (closure_minimal hi (hc.image hR).isClosed)

/-- Addition of a fixed prescribed value preserves relative compactness. -/
theorem compactness_affine : CompactnessExpected.Affine := by
  intro d hd Ω hΩ m p u₀ A hA hclass
  let B : Set (W1pZero Ω m p) := {v | v.val + u₀ ∈ A}
  have hB : Bornology.IsBounded B := by
    obtain ⟨M, hM⟩ := hA.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M + ‖u₀‖, ?_⟩
    intro v hv
    have hm : ‖v.val + u₀‖ ≤ M := hM _ hv
    change ‖v.val‖ ≤ M + ‖u₀‖
    calc
      ‖v.val‖ = ‖(v.val + u₀) - u₀‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖v.val + u₀‖ + ‖u₀‖ := norm_sub_le _ _
      _ ≤ M + ‖u₀‖ := by linarith
  have hc := compactness_zero hd Ω hΩ m p B hB
  let T : ValueLp Ω m p → ValueLp Ω m p := fun v => v + value Ω m p u₀
  have hT : Continuous T := continuous_id.add continuous_const
  have hi : (value Ω m p) '' A ⊆
      T '' closure ((fun u : W1pZero Ω m p => value Ω m p u.val) '' B) := by
    rintro _ ⟨u, hu, rfl⟩
    let v : W1pZero Ω m p := ⟨u - u₀, hclass hu⟩
    refine ⟨value Ω m p v.val, subset_closure ⟨v, ?_, rfl⟩, ?_⟩
    · change (u - u₀) + u₀ ∈ A
      simpa using hu
    · change value Ω m p (u - u₀) + value Ω m p u₀ = value Ω m p u
      rw [map_sub, sub_add_cancel]
  exact (hc.image hT).of_isClosed_subset isClosed_closure
    (closure_minimal hi (hc.image hT).isClosed)

end VariationalNotes.Sobolev
