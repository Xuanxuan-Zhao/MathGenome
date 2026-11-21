import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.ArrowIdealPowers
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.BoundedPaths
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.AdmissibleFiniteness
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Finite-dimensional quotients of a path algebra and independence in degrees zero and one. -/

universe u v w

namespace RM03.PathAlgebra

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]

/-- Containing the `m`-th power of the arrow ideal makes the quotient spanned by
the finite family of images of paths of length below `m`. -/
theorem quotient_finite_and_spanned [Nonempty Q] [Finite (Arrow Q)]
    (I : TwoSidedIdeal (PathAlgebra k Q)) (m : ℕ)
    (hm : 1 ≤ m) (hI : idealPower (arrowIdeal k Q) m ≤ I) :
    FiniteDimensional k (PathAlgebra k Q ⧸ I.asIdeal) ∧
      Submodule.span k (Set.range fun p : {p : Path Q // p.length < m} =>
        Ideal.Quotient.mk I.asIdeal (ofPath k p.val)) = ⊤ := by
  let S := I.asIdeal.restrictScalars k
  let short : {p : Path Q // p.length < m} → PathAlgebra k Q ⧸ S :=
    fun p => S.mkQ (ofPath k p.val)
  have hspan : Submodule.span k (Set.range short) = ⊤ := by
    rw [eq_top_iff, ← S.range_mkQ, ← Submodule.map_top, ← (basis k Q).span_eq,
      Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    rw [basis_apply]
    by_cases hp : p.length < m
    · exact Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩
    · have hlong : ofPath k p ∈ idealPower (arrowIdeal k Q) m := by
        change ofPath k p ∈ (idealPower (arrowIdeal k Q) m : Set (PathAlgebra k Q))
        rw [arrowIdeal_power_eq_span m hm]
        exact Submodule.subset_span ⟨p, Nat.le_of_not_gt hp, rfl⟩
      have hzero : S.mkQ (ofPath k p) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hI hlong
      rw [hzero]
      exact Submodule.zero_mem _
  let := Path.finite_length_lt (V := Q) m
  have hfg := Submodule.fg_span (R := k) (Set.finite_range short)
  rw [hspan] at hfg
  exact ⟨⟨hfg⟩, hspan⟩

/-- An ideal contained in the square of the arrow ideal leaves the vertex and
arrow images jointly linearly independent in the quotient. -/
theorem quotient_short_paths_independent [Nonempty Q] [Finite (Arrow Q)]
    (I : TwoSidedIdeal (PathAlgebra k Q))
    (hI : I ≤ idealPower (arrowIdeal k Q) 2) :
    LinearIndependent k (fun p : {p : Path Q // p.length < 2} =>
      Ideal.Quotient.mk I.asIdeal (ofPath k p.val)) := by
  let S := I.asIdeal.restrictScalars k
  let shortPath : {p : Path Q // p.length < 2} → PathAlgebra k Q := fun p => ofPath k p.val
  change LinearIndependent k (S.mkQ ∘ shortPath)
  have hspan : S ≤ Submodule.span k (ofPath k '' {p : Path Q | 2 ≤ p.length}) := by
    intro x hx
    have hx' : x ∈ (idealPower (arrowIdeal k Q) 2 : Set (PathAlgebra k Q)) := hI hx
    rw [arrowIdeal_power_eq_span 2 (by decide)] at hx'
    exact hx'
  have hdisjoint : Disjoint (Submodule.span k (Set.range shortPath)) (LinearMap.ker S.mkQ) := by
    rw [S.ker_mkQ, show Set.range shortPath = ofPath k '' {p : Path Q | p.length < 2} from
      (Set.image_eq_range _ _).symm]
    refine Disjoint.mono_right hspan ?_
    have hlengths : Disjoint {p : Path Q | p.length < 2} {p : Path Q | 2 ≤ p.length} :=
      Set.disjoint_left.mpr fun _ hshort hlong => Nat.not_lt_of_ge hlong hshort
    simpa only [basis_apply] using (basis k Q).linearIndependent.disjoint_span_image hlengths
  apply (S.mkQ.linearIndependent_iff_of_disjoint hdisjoint).mpr
  simpa only [shortPath, Function.comp_def, basis_apply] using
    (basis k Q).linearIndependent.comp _ Subtype.val_injective

end RM03.PathAlgebra
