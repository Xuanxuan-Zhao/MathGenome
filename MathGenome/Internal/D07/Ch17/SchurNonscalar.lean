import MathGenome.Internal.D07.Ch17.IrreducibleDefinition
import MathGenome.Internal.D07.Ch17.KernelsImages
import MathGenome.Internal.Specs.D07.Ch17.SchurNonscalar

/-! Schur's lemma over arbitrary fields, its division-algebra consequence,
and the nonscalar real quarter-turn example. No finiteness assumptions are used. -/
namespace D07.Ch17.SchurNonscalar

universe u v w x
noncomputable section
open Specs.D07.Ch17.SchurNonscalar

abbrev endomorphismAlgebra : EndomorphismAlgebraType.{u,v,w} := endomorphismAlgebraValue

theorem nonzero_intertwiner_equivalence : NonzeroIntertwinerEquivalence.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ T hρ hσ hT h0
  have hker : LinearMap.ker T = ⊥ := by
    rcases ((IrreducibleDefinition.irreducibility_characterization K G V ρ).mp hρ).2
      (LinearMap.ker T) (KernelsImages.kernel_invariant K G V W ρ σ T hT) with h | h
    · exact h
    · exact False.elim (h0 (LinearMap.ker_eq_top.mp h))
  have hrange : LinearMap.range T = ⊤ := by
    rcases ((IrreducibleDefinition.irreducibility_characterization K G W σ).mp hσ).2
      (LinearMap.range T) (KernelsImages.image_invariant K G V W ρ σ T hT) with h | h
    · exact False.elim (h0 (LinearMap.range_eq_bot.mp h))
    · exact h
  let e := LinearEquiv.ofBijective T
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩
  exact ⟨Representation.Equiv.mk e (fun g => LinearMap.ext (hT.isIntertwining g)), rfl⟩

theorem endomorphism_algebra_characterization : EndomorphismAlgebraCharacterization.{u,v,w} := by
  intro K G V _ _ _ _ ρ T
  change T ∈ Subalgebra.centralizer K (Set.range ρ) ↔ _
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro h
    constructor
    intro g v
    exact (LinearMap.congr_fun (h (ρ g) ⟨g, rfl⟩) v).symm
  · intro h A hA
    obtain ⟨g, rfl⟩ := hA
    exact (LinearMap.ext (h.isIntertwining g)).symm

theorem division_algebra : DivisionAlgebra.{u,v,w} := by
  intro K G V _ _ _ _ ρ hρ
  have hV : Nontrivial V := IrreducibleDefinition.irreducible_nontrivial hρ
  have hn : Nontrivial (endomorphismAlgebra K G V ρ) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  refine ⟨hn, ?_⟩
  intro T h0
  have ht : (T : Module.End K V) ≠ 0 := by
    intro h
    exact h0 (Subtype.ext h)
  obtain ⟨e, he⟩ := nonzero_intertwiner_equivalence K G V V ρ ρ T hρ hρ
    ((endomorphism_algebra_characterization K G V ρ T).mp T.property) ht
  let S : endomorphismAlgebra K G V ρ :=
    ⟨e.symm.toLinearMap,
      (endomorphism_algebra_characterization K G V ρ _).mpr
        ⟨e.symm.toIntertwiningMap.isIntertwining⟩⟩
  refine ⟨⟨T, S, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    apply LinearMap.ext
    intro v
    change (T : Module.End K V) (e.toLinearEquiv.symm v) = v
    rw [← he]
    exact e.toLinearEquiv.apply_symm_apply v
  · apply Subtype.ext
    apply LinearMap.ext
    intro v
    change e.toLinearEquiv.symm ((T : Module.End K V) v) = v
    rw [← he]
    exact e.toLinearEquiv.symm_apply_apply v

theorem real_nonscalar_example : RealNonscalarExample := by
  open Specs.D07.Ch17.IrreducibleDefinition in
  change Representation.IsIrreducible (rotationValue ℝ) ∧ _
  refine ⟨IrreducibleDefinition.real_rotation_irreducible, ?_, ?_,
    IrreducibleDefinition.quarterTurn_square ℝ, ?_⟩
  · constructor
    intro g p
    have hcomm := (Commute.refl (quarterTurn ℝ)).pow_right g.toAdd.val
    exact LinearMap.congr_fun hcomm.eq p
  · intro h
    have hh := LinearMap.congr_fun h ((1 : ℝ), (0 : ℝ))
    have := congrArg Prod.snd hh
    norm_num [Specs.D07.Ch17.IrreducibleDefinition.quarterTurn] at this
  · rintro ⟨a, ha⟩
    have hh := LinearMap.congr_fun ha ((1 : ℝ), (0 : ℝ))
    have := congrArg Prod.snd hh
    norm_num [Specs.D07.Ch17.IrreducibleDefinition.quarterTurn] at this

end
end D07.Ch17.SchurNonscalar
