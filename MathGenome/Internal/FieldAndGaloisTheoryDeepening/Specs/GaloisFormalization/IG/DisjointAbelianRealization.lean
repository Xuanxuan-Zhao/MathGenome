import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.PrescribedExtension

namespace Specs.GaloisFormalization.IG

open GH.KrullLayers IntermediateField

universe u v

/-- A finite abelian group is realized by a subfield disjoint from a prescribed
finite Galois layer in the chosen separable closure of `ℚ`. -/
def disjointAbelianRealization_type : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsSepClosure ℚ Ω]
    (A : Type v) [CommGroup A] [Finite A] (E : FiniteGaloisIntermediateField ℚ Ω),
    ∃ (F : FiniteGaloisIntermediateField ℚ Ω) (_ : LayerGroup F ≃* A),
      F.toIntermediateField ⊓ E.toIntermediateField = ⊥ ∧
      (Subsingleton A → F = ⊥)

/-- For the second projection and actual restriction to the prescribed field,
the split embedding problem has a proper solution through the compositum. -/
def disjointAbelianEmbeddingSolution_type : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsSepClosure ℚ Ω]
    (A : Type v) [CommGroup A] [Finite A] (E : FiniteGaloisIntermediateField ℚ Ω),
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    let π := ContinuousMonoidHom.snd A (LayerGroup E)
    let hπ : Function.Surjective π := fun g => ⟨(1, g), rfl⟩
    let P := prescribedProblem E π hπ
    FiniteEmbeddingProblem.isSplitValue P ∧
      ∃ (F : FiniteGaloisIntermediateField ℚ Ω) (e : LayerGroup F ≃* A),
        F.toIntermediateField ⊓ E.toIntermediateField = ⊥ ∧
        (Subsingleton A → F = ⊥) ∧
        ∃ s : P.WeakSolution,
          FiniteEmbeddingProblem.isProperValue s ∧
          s.lift.toMonoidHom =
            ((e.toMonoidHom.comp (transition (le_sup_left : F ≤ F ⊔ E)).toMonoidHom).prod
              (transition (le_sup_right : E ≤ F ⊔ E)).toMonoidHom).comp
                (restrict (F ⊔ E)).toMonoidHom ∧
          fixedField s.lift.toMonoidHom.ker = (F ⊔ E).toIntermediateField

/-- Every finite abelian group occurs as a Galois group over `ℚ`. -/
def finiteAbelianRealization_type : Prop :=
  ∀ (A : Type v) [CommGroup A] [Finite A],
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K),
      FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ Nonempty (Gal(K/ℚ) ≃* A)

end Specs.GaloisFormalization.IG
