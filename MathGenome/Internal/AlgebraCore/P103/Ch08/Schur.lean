import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.Schur
import MathGenome.Internal.AlgebraCore.P103.Ch08.RepresentationModules
import Mathlib.RepresentationTheory.Irreducible

/-! Schur's lemma over arbitrary fields and groups, paper.tex 1364–1381. -/

noncomputable section
namespace P103.Ch08.Schur
open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The library's simple-order condition includes nontriviality. -/
private theorem libraryIrreducible (ρ : Representation k G V)
    (h : Irreducible k G V ρ) : Representation.IsIrreducible ρ := by
  have : Nontrivial V := h.1
  have : Nontrivial (Subrepresentation ρ) := by
    apply nontrivial_of_ne (⊥ : Subrepresentation ρ) ⊤
    intro he
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have : v ∈ (⊥ : Subrepresentation ρ) :=
      he ▸ (show v ∈ (⊤ : Subrepresentation ρ) from trivial)
    exact (Submodule.mem_bot k).mp this
  exact ⟨h.2⟩

/-- A nonzero intertwiner has an equivariant linear inverse. -/
theorem nonzeroIntertwiner : Specs.Schur.nonzeroIntertwinerType := by
  intro k G V W _ _ _ _ _ _ ρ σ hρ hσ f hf
  have := libraryIrreducible ρ hρ
  have := libraryIrreducible σ hσ
  exact ⟨f.ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf), rfl⟩

/-- Transfer inverses from group-algebra endomorphisms, while retaining all
of the existing semiring operations on intertwining maps. -/
theorem endomorphismDivisionRing : Specs.Schur.endomorphismDivisionRingType := by
  intro k G V _ _ _ _ ρ hρ
  classical
  have := libraryIrreducible ρ hρ
  let E := Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)
  let D : DivisionRing (ρ.IntertwiningMap ρ) :=
    { (inferInstance : Semiring (ρ.IntertwiningMap ρ)),
      (inferInstance : AddCommGroup (ρ.IntertwiningMap ρ)) with
      inv := fun f => E.symm ((E f)⁻¹)
      exists_pair_ne := ⟨0, 1, fun he => zero_ne_one (congrArg E he)⟩
      mul_inv_cancel := by
        intro f hf
        apply E.injective
        simp only [map_mul, map_one, AlgEquiv.apply_symm_apply]
        exact mul_inv_cancel₀ (fun he => hf (E.injective (by simpa using he)))
      inv_zero := by simp
      nnqsmul := _
      nnqsmul_def := fun _ _ => rfl
      qsmul := _
      qsmul_def := fun _ _ => rfl }
  exact ⟨D, rfl⟩

/-- Algebraic closure and finite dimension make the scalar map bijective. -/
theorem uniqueScalar : Specs.Schur.uniqueScalarType := by
  intro k G V _ _ _ _ _ _ ρ hρ f
  have := libraryIrreducible ρ hρ
  have hb := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)
  obtain ⟨c, hc⟩ := hb.surjective f
  have scalar_formula (d : k) :
      algebraMap k (ρ.IntertwiningMap ρ) d =
        d • Representation.IntertwiningMap.id ρ := rfl
  refine ⟨c, ?_, ?_⟩
  · exact hc.symm.trans (scalar_formula c)
  · intro d hd
    apply hb.injective
    rw [scalar_formula d, ← hd, hc]

end P103.Ch08.Schur
