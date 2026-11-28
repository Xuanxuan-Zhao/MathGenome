import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.FiniteAveraging
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.HomogeneousGenerators
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.NoetherBoundIdeal
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.NoetherBound
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

universe u v w

namespace RepTheorySurvey.Invariants

open MvPolynomial

private theorem preserves_homogeneousSubmodule {k : Type u} {ι : Type w} [Field k]
    (e : MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)
    (he : ∀ i, (e (X i)).IsHomogeneous 1) (n : ℕ) {p : MvPolynomial ι k}
    (hp : p ∈ homogeneousSubmodule ι k n) :
    e p ∈ homogeneousSubmodule ι k n := by
  let H := homogeneousSubmodule ι k
  have h₁ : (H 1).map e.toLinearMap ≤ H 1 := by
    apply Submodule.map_le_iff_le_comap.mpr
    calc
      H 1 = Submodule.span k (Set.range X) := homogeneousSubmodule_one_eq_span_X
      _ ≤ (H 1).comap e.toLinearMap := Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact he i)
  have hn : (H n).map e.toLinearMap ≤ H n := calc
    (H n).map e.toLinearMap = ((H 1).map e.toLinearMap) ^ n := by
      change Submodule.map e.toAlgHom.toLinearMap (H n) =
        (Submodule.map e.toAlgHom.toLinearMap (H 1)) ^ n
      rw [← Submodule.map_pow, homogeneousSubmodule_one_pow]
    _ ≤ H 1 ^ n := by gcongr
    _ = H n := homogeneousSubmodule_one_pow k n
  exact Submodule.map_le_iff_le_comap.mp hn hp

/-- Noether's degree bound for finite groups in characteristic zero or larger than the
group order. -/
theorem noetherBound : Specs.NoetherBound.{u,v,w} := by
  intro k G ι _ _ _ _ ρ hρ hchar
  classical
  let S := MvPolynomial ι k
  let m := Fintype.card G
  let H := homogeneousSubmodule ι k
  let B := GroupAlgebraAction.fixedSubalgebra ρ
  let : GradedAlgebra H := MvPolynomial.gradedAlgebra
  have hcard : (Nat.card G : k) ≠ 0 := by
    rw [← Fintype.card_eq_nat_card]
    rcases hchar with h | h
    · let : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp h
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    · exact (ringChar.spec k _).not.mpr
        (Nat.not_dvd_of_pos_of_lt Fintype.card_pos h)
  have hgraded (g : G) (n : ℕ) (p : S) (hp : p ∈ H n) : ρ g p ∈ H n :=
    preserves_homogeneousSubmodule (ρ g) (hρ g) n hp
  obtain ⟨R, hR, havg⟩ := GroupRepresentation.finiteAverage_reynolds ρ hcard
  have hRgraded (n : ℕ) (p : S) (hp : p ∈ H n) : (R p : S) ∈ H n := by
    rw [havg]
    exact GroupRepresentation.finiteAverage_preservesGrading
      (GroupAlgebraAction.toRepresentation ρ) H hgraded n p hp
  have hzero : H 0 = (⊥ : Subalgebra k S).toSubmodule := by
    change homogeneousSubmodule ι k 0 = _
    rw [homogeneousSubmodule_zero, Algebra.toSubmodule_bot]
  let D := ↥(Finset.Icc 1 m)
  have hD (i : D) : 0 < i.val ∧ i.val ≤ m := Finset.mem_Icc.mp i.property
  let V (n : ℕ) : Submodule k S := H n ⊓ B.toSubmodule
  let : ∀ n : ℕ, FiniteDimensional k (H n) := fun n ↦
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg ι k n)
  let : ∀ n : ℕ, FiniteDimensional k (V n) := fun _ ↦
    FiniteDimensional.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective inf_le_left)
  let b (i : D) := Module.finBasis k (V i.val)
  let J := Σ i : D, Fin (Module.finrank k (V i.val))
  let d (j : J) : ℕ := j.1.val
  let f (j : J) : B := ⟨b j.1 j.2, (b j.1 j.2).property.2⟩
  have hf (j : J) : (f j : S) ∈ H (d j) := (b j.1 j.2).property.1
  let I : Ideal S := Ideal.span (Set.range fun j ↦ (f j : S))
  have hV (i : D) : V i.val ≤ I.restrictScalars k := by
    intro p hp
    change (⟨p, hp⟩ : V i.val) ∈ (I.restrictScalars k).comap (V i.val).subtype
    have hb : Submodule.span k (Set.range (b i)) ≤
        (I.restrictScalars k).comap (V i.val).subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact Ideal.subset_span ⟨⟨i, a⟩, rfl⟩
    rw [(b i).span_eq] at hb
    exact hb Submodule.mem_top
  have hlow : lowDegreeInvariantIdeal ρ m ≤ I := by
    apply Ideal.span_le.mpr
    rintro p ⟨hfixed, n, hn, hnm, hp⟩
    let i : D := ⟨n, Finset.mem_Icc.mpr ⟨hn, hnm⟩⟩
    exact hV i ⟨hp, hfixed⟩
  have hspan : I = Ideal.span (positiveHomogeneousInvariants H B) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨(f j).property, d j, (hD j.1).1, hf j⟩
    · apply Ideal.span_le.mpr
      rintro p ⟨hfixed, n, hn, hp⟩
      by_cases hnm : n ≤ m
      · exact hlow (Ideal.subset_span ⟨hfixed, n, hn, hnm, hp⟩)
      · exact hlow (homogeneous_mem_lowDegreeInvariantIdeal ρ hρ hchar n
          (le_of_lt (Nat.lt_of_not_ge hnm)) p hp)
  have hgen := GroupAlgebraAction.adjoin_homogeneous_eq_fixedSubalgebra H ρ R f d
    hzero hgraded hR hRgraded (fun j ↦ (hD j.1).1) hf hspan
  let s : Finset S := Finset.univ.image fun j ↦ (f j : S)
  refine ⟨s, ?_, ?_⟩
  · intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(f j).property, d j, (hD j.1).1, (hD j.1).2, hf j⟩
  · simpa only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgen

end RepTheorySurvey.Invariants
