import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompositionOfValuations

namespace CommutativeAlgebraNotes.CompositionOfValuations

open Spec

universe u

variable {K : Type u} [Field K]
variable (U : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField U))

private theorem map_unit_inv {R F : Type*} [CommRing R] [Field F]
    (f : R →+* F) (a : Rˣ) : f (↑a⁻¹) = (f ↑a)⁻¹ :=
  Units.val_inv_eq_inv_val (Units.map f.toMonoidHom a)

private theorem inv_mem_pullback (a : U) (ha : (a : K) ∉ pullback U W) :
    (a : K)⁻¹ ∈ pullback U W := by
  have hr : IsLocalRing.residue U a ∉ W := fun h => ha ⟨a, h, rfl⟩
  have hne : IsLocalRing.residue U a ≠ 0 := fun h => hr (by rw [h]; exact W.zero_mem)
  have hWinv := (W.mem_or_inv_mem (IsLocalRing.residue U a)).resolve_left hr
  obtain ⟨b, rfl⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit a).mp hne
  refine ⟨(↑b⁻¹ : U), ?_, map_unit_inv U.subtype b⟩
  change IsLocalRing.residue U ↑b⁻¹ ∈ W
  rwa [map_unit_inv]

/-- The valuation subring of `K` obtained by composing `U` and `W`. -/
noncomputable def compose : ValuationSubring K :=
  ValuationSubring.ofSubring (pullback U W) fun x => by
    by_cases hx : x ∈ pullback U W
    · exact Or.inl hx
    · right
      rcases U.mem_or_inv_mem x with hu | hu
      · exact inv_mem_pullback U W ⟨x, hu⟩ hx
      · by_contra hinv
        exact hx (by simpa only [Subtype.coe_mk, inv_inv] using
          inv_mem_pullback U W ⟨x⁻¹, hu⟩ hinv)

theorem compose_le : compose U W ≤ U := by
  rintro x ⟨a, _, rfl⟩
  exact a.property

theorem compose_residue_mem (x : compose U W) :
    IsLocalRing.residue U ((compose U W).inclusion U (compose_le U W) x) ∈ W := by
  obtain ⟨a, ha, he⟩ := x.property
  have h : a = (compose U W).inclusion U (compose_le U W) x := Subtype.ext he
  exact h ▸ ha

theorem composition : Spec.Composition.{u} := by
  intro K _ U W
  let V := compose U W
  let h := compose_le U W
  let f := residueHom U W V h (compose_residue_mem U W)
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (w : IsLocalRing.ResidueField U)
    have hmem : IsLocalRing.residue U a ∈ W := by
      rw [ha]
      exact w.property
    let x : V := ⟨a, ⟨a, hmem, rfl⟩⟩
    exact ⟨x, Subtype.ext ha⟩
  refine ⟨V, h, compose_residue_mem U W, rfl,
    ⟨RingHom.quotientKerEquivOfSurjective hf,
      RingHom.quotientKerEquivOfSurjective_apply_mk hf⟩, ?_⟩
  have hP : RingHom.ker f = V.idealOfLE U h := by
    ext x
    rw [RingHom.mem_ker]
    change (f x = 0) ↔ V.inclusion U h x ∈ IsLocalRing.maximalIdeal U
    exact Subtype.ext_iff.trans (IsLocalRing.residue_eq_zero_iff _)
  let _ : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  change V.ofPrime (RingHom.ker f) = U
  simp only [hP, ValuationSubring.ofPrime_idealOfLE]

end CommutativeAlgebraNotes.CompositionOfValuations
