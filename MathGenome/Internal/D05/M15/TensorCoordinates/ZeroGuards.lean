import MathGenome.Internal.D05.M15.TensorCoordinates.TraceDeterminant
import MathGenome.Internal.Specs.D05.M15.TensorCoordinates.ZeroGuards

/-! K05.15.tensor_coordinates: zero-factor guards for tensor maps.
The upstream coordinate theorem proves injectivity preservation by tensoring
linear left inverses, and proves the converse using nonzero elementary tensors.
We reuse those same maps and results, with no finite-dimensional assumption on
the arbitrary-map assertions. Empty coordinate spaces give explicit failures of
the unguarded converses over every field.
-/
namespace D05.M15.TensorCoordinates.ZeroGuards

open scoped TensorProduct

theorem injective_tensor : Specs.D05.M15.TensorCoordinates.ZeroGuards.injective_tensor :=
  D05.M15.TensorCoordinates.injective_tensor

theorem injective_factors : Specs.D05.M15.TensorCoordinates.ZeroGuards.injective_factors :=
  D05.M15.TensorCoordinates.injective_factors

theorem injective_iff : Specs.D05.M15.TensorCoordinates.ZeroGuards.injective_iff := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ S T
  exact ⟨injective_factors S T, fun h => injective_tensor S T h.1 h.2⟩

theorem invertible_factors : Specs.D05.M15.TensorCoordinates.ZeroGuards.invertible_factors := by
  intro K V W _ _ _ _ _ _ _ S T hV hW
  letI := Module.nontrivial_of_finrank_pos hV
  letI := Module.nontrivial_of_finrank_pos hW
  exact D05.M15.TensorCoordinates.invertible_factors S T

theorem zero_dimension_invertible :
    Specs.D05.M15.TensorCoordinates.ZeroGuards.zero_dimension_invertible := by
  intro K V W _ _ _ _ _ _ _ S T h
  have hz : Subsingleton V ∨ Subsingleton W := by
    rcases h with h | h
    · exact Or.inl (Module.finrank_zero_iff.mp h)
    · exact Or.inr (Module.finrank_zero_iff.mp h)
  refine ⟨?_, (D05.M15.TensorCoordinates.zero_factor S T hz).1⟩
  rcases hz with h | h
  · letI := h
    exact fun z => D05.M15.TensorBasis.zero_left z
  · letI := h
    exact fun z => D05.M15.TensorBasis.zero_right z

theorem zero_factor_injective :
    Specs.D05.M15.TensorCoordinates.ZeroGuards.zero_factor_injective := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ S T h
  haveI : Subsingleton (V ⊗[K] W) := by
    rcases h with h | h
    · letI := h
      infer_instance
    · letI := h
      infer_instance
  exact fun _ _ _ => Subsingleton.elim _ _

theorem zero_left_counterexample :
    Specs.D05.M15.TensorCoordinates.ZeroGuards.zero_left_counterexample := by
  intro K _
  let S : Module.End K (Fin 0 → K) := 0
  let T : Module.End K K := 0
  refine ⟨S, T, ?_, ?_, ?_, ?_⟩
  · exact (D05.M15.TensorCoordinates.zero_factor S T (Or.inl inferInstance)).1
  · exact zero_factor_injective S T (Or.inl inferInstance)
  · exact not_isUnit_zero
  · intro h
    exact one_ne_zero (h (show T 1 = T 0 from rfl))

theorem zero_right_counterexample :
    Specs.D05.M15.TensorCoordinates.ZeroGuards.zero_right_counterexample := by
  intro K _
  let S : Module.End K K := 0
  let T : Module.End K (Fin 0 → K) := 0
  refine ⟨S, T, ?_, ?_, ?_, ?_⟩
  · exact (D05.M15.TensorCoordinates.zero_factor S T (Or.inr inferInstance)).1
  · exact zero_factor_injective S T (Or.inr inferInstance)
  · exact not_isUnit_zero
  · intro h
    exact one_ne_zero (h (show S 1 = S 0 from rfl))

end D05.M15.TensorCoordinates.ZeroGuards
