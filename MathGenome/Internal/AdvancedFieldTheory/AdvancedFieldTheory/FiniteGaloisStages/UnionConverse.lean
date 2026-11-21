import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteGaloisStages.UnionConverse

/-!
# The converse directed-union theorem

Each element belongs to a Galois stage. Inclusion preserves its minimal
polynomial and separability, and carries a splitting of that polynomial into
L. This proves normality and separability element by element, without any
finiteness assumption on L. Since L is already a field, directedness and
finiteness of the stages are unnecessary for this direction of the argument.
-/

universe u v w

namespace AdvancedFieldTheory

/-- The converse of Theorem F04: a directed union of finite Galois stages
is Galois over the base field. -/
theorem isGalois_of_directed_union
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {ι : Type w} [Nonempty ι] (E : ι → IntermediateField K L)
    (_h_directed : Directed (· ≤ ·) E)
    (_h_finite : ∀ i, FiniteDimensional K (E i))
    (h_galois : ∀ i, IsGalois K (E i))
    (h_cover : ∀ x : L, ∃ i, x ∈ E i) : IsGalois K L := by
  have h_sep : Algebra.IsSeparable K L := by
    constructor
    intro x
    obtain ⟨i, hx⟩ := h_cover x
    have : IsGalois K (E i) := h_galois i
    let y : E i := ⟨x, hx⟩
    have hy : IsSeparable K y := IsGalois.separable K y
    exact (isSeparable_map_iff (x := y) (E i).val (E i).val.injective).mpr hy
  have := h_sep
  have h_normal : Normal K L := normal_iff.mpr fun x => by
    obtain ⟨i, hx⟩ := h_cover x
    have : IsGalois K (E i) := h_galois i
    let y : E i := ⟨x, hx⟩
    refine ⟨(IsGalois.integral K y).map (E i).val, ?_⟩
    have h := (IsGalois.splits K y).map (E i).val.toRingHom
    have hcomp : (E i).val.toRingHom.comp (algebraMap K (E i)) =
        algebraMap K L := by
      ext a
      rfl
    rw [Polynomial.map_map, hcomp] at h
    rw [← minpoly.algHom_eq (E i).val (E i).val.injective y] at h
    exact h
  exact { to_isSeparable := h_sep, to_normal := h_normal }

end AdvancedFieldTheory
