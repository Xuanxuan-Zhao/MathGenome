import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.AbsoluteGaloisGroup
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.ExponentCoordinates
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.Exhaustion
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.ProfiniteIntegers.ResidueModel
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.InverseLimit.Profiniteness
import Mathlib.Topology.Homeomorph.Lemmas

/-! FT-E06: Frobenius coordinates identify the Krull group with the literal
residue-family model. Compactness realizes all compatible coordinates at once. -/
universe u v
noncomputable section
namespace AdvancedFieldTheory
namespace AbsoluteGalois

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]

local instance closureGalois : IsGalois k Ω := algebraicClosure_isGalois k Ω
local instance layerGalois (n : ℕ+) : IsGalois k (finiteRootField k Ω n) :=
  (finiteRootField_finite_galois k Ω n n.pos).2

private def coordinate (n : ℕ+) : GaloisGroup k Ω →* Multiplicative (ZMod (n : ℕ)) :=
  (frobeniusExponentCoordinates k Ω n n.pos).symm.toMonoidHom.comp
    (restriction (finiteRootField k Ω n))

private theorem coordinate_compatible (σ : GaloisGroup k Ω) (m n : ℕ+)
    (h : (m : ℕ) ∣ (n : ℕ)) :
    ProfiniteIntegers.reduce m n h (coordinate k Ω n σ).toAdd =
      (coordinate k Ω m σ).toAdd := by
  apply Multiplicative.ofAdd.injective
  apply (frobeniusExponentCoordinates k Ω m m.pos).injective
  have hs := DFunLike.congr_fun
    (frobeniusExponentCoordinates_restriction k Ω m.pos n.pos h)
    ((frobeniusExponentCoordinates k Ω n n.pos).symm
      (restriction (finiteRootField k Ω n) σ))
  change stageRestriction (finiteRootField_le_of_dvd k Ω h)
      (frobeniusExponentCoordinates k Ω n n.pos
        ((frobeniusExponentCoordinates k Ω n n.pos).symm
          (restriction (finiteRootField k Ω n) σ))) =
    frobeniusExponentCoordinates k Ω m m.pos
      (Multiplicative.ofAdd (ProfiniteIntegers.reduce m n h
        ((frobeniusExponentCoordinates k Ω n n.pos).symm
          (restriction (finiteRootField k Ω n) σ)).toAdd)) at hs
  rw [MulEquiv.apply_symm_apply] at hs
  change frobeniusExponentCoordinates k Ω m m.pos
      (Multiplicative.ofAdd (ProfiniteIntegers.reduce m n h
        ((frobeniusExponentCoordinates k Ω n n.pos).symm
          (restriction (finiteRootField k Ω n) σ)).toAdd)) =
    frobeniusExponentCoordinates k Ω m m.pos
      ((frobeniusExponentCoordinates k Ω m m.pos).symm
        (restriction (finiteRootField k Ω m) σ))
  rw [MulEquiv.apply_symm_apply]
  exact hs.symm.trans (DFunLike.congr_fun
    (restriction_comp (finiteRootField_le_of_dvd k Ω h)) σ).symm

private def residueHom : GaloisGroup k Ω →* Multiplicative ProfiniteIntegers.Zhat where
  toFun σ := Multiplicative.ofAdd
    ⟨fun n => (coordinate k Ω n σ).toAdd, coordinate_compatible k Ω σ⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply ProfiniteIntegers.ext
    intro n
    exact congrArg Multiplicative.toAdd (map_one (coordinate k Ω n))
  map_mul' σ τ := by
    apply congrArg Multiplicative.ofAdd
    apply ProfiniteIntegers.ext
    intro n
    exact congrArg Multiplicative.toAdd (map_mul (coordinate k Ω n) σ τ)

private theorem continuous_coordinate (n : ℕ+) : Continuous (coordinate k Ω n) := by
  let E : FiniteGaloisIntermediateField k Ω :=
    { toIntermediateField := finiteRootField k Ω n
      finiteDimensional := (finiteRootField_finite_galois k Ω n n.pos).1
      isGalois := inferInstance }
  have hr := ((KrullTopology.continuous_iff_finiteRestrictions k Ω
    (id : GaloisGroup k Ω → GaloisGroup k Ω)).mp continuous_id) E
  let : TopologicalSpace (finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n) := ⊥
  let : DiscreteTopology (finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n) := ⟨rfl⟩
  exact (continuous_of_discreteTopology (f :=
    (frobeniusExponentCoordinates k Ω n n.pos).symm)).comp hr

private theorem continuous_residueHom : Continuous (residueHom k Ω) := by
  exact (continuous_pi (fun n =>
    (continuous_coordinate k Ω n))).subtype_mk _

private theorem residueHom_injective : Function.Injective (residueHom k Ω) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  obtain ⟨n, hn, hx⟩ := mem_some_finiteRootField k Ω x
  let := (finiteRootField_finite_galois k Ω n hn).2
  have hc := congrArg (fun a : Multiplicative ProfiniteIntegers.Zhat =>
    Multiplicative.ofAdd (ProfiniteIntegers.π ⟨n, hn⟩ a.toAdd)) h
  have hr := congrArg (frobeniusExponentCoordinates k Ω n hn) hc
  have he : restriction (finiteRootField k Ω n) σ =
      restriction (finiteRootField k Ω n) τ := by
    change frobeniusExponentCoordinates k Ω n hn
        ((frobeniusExponentCoordinates k Ω n hn).symm
          (restriction (finiteRootField k Ω n) σ)) =
      frobeniusExponentCoordinates k Ω n hn
        ((frobeniusExponentCoordinates k Ω n hn).symm
          (restriction (finiteRootField k Ω n) τ)) at hr
    simpa only [MulEquiv.apply_symm_apply] using hr
  exact (restriction_apply _ σ ⟨x, hx⟩).symm.trans
    ((congrArg (fun f => (f ⟨x, hx⟩ : Ω)) he).trans (restriction_apply _ τ ⟨x, hx⟩))

private theorem coordinate_surjective (n : ℕ+) : Function.Surjective (coordinate k Ω n) :=
  (frobeniusExponentCoordinates k Ω n n.pos).symm.surjective.comp
    (restriction_surjective (finiteRootField k Ω n))

private theorem residueHom_surjective : Function.Surjective (residueHom k Ω) := by
  intro a
  let C (n : ℕ+) : Set (GaloisGroup k Ω) :=
    {σ | coordinate k Ω n σ = Multiplicative.ofAdd (ProfiniteIntegers.π n a.toAdd)}
  have hclosed (n : ℕ+) : IsClosed (C n) :=
    isClosed_eq (continuous_coordinate k Ω n) continuous_const
  have hnonempty (n : ℕ+) : (C n).Nonempty :=
    coordinate_surjective k Ω n (Multiplicative.ofAdd (ProfiniteIntegers.π n a.toAdd))
  have hmono {m n : ℕ+} (h : (m : ℕ) ∣ (n : ℕ)) : C n ⊆ C m := by
    intro σ hσ
    apply Multiplicative.toAdd.injective
    change (coordinate k Ω m σ).toAdd = ProfiniteIntegers.π m a.toAdd
    rw [← coordinate_compatible k Ω σ m n h]
    rw [hσ]
    exact a.toAdd.property m n h
  have hd : Directed (· ⊇ ·) C := by
    intro m n
    refine ⟨m * n, hmono ?_, hmono ?_⟩
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    C hd hnonempty (fun n => (hclosed n).isCompact) hclosed
  refine ⟨σ, ?_⟩
  apply Multiplicative.toAdd.injective
  apply ProfiniteIntegers.ext
  intro n
  exact congrArg Multiplicative.toAdd (Set.mem_iInter.mp hσ n)

local instance residueHausdorff : T2Space (Multiplicative ProfiniteIntegers.Zhat) :=
  ProfiniteIntegers.zhat_hausdorff

private def equiv : GaloisGroup k Ω ≃ₜ* Multiplicative ProfiniteIntegers.Zhat :=
  let e := MulEquiv.ofBijective (residueHom k Ω)
    ⟨residueHom_injective k Ω, residueHom_surjective k Ω⟩
  { e with
    continuous_toFun := continuous_residueHom k Ω
    continuous_invFun := (show Continuous e.toEquiv from continuous_residueHom k Ω).continuous_symm_of_equiv_compact_to_t2 }

/-- The literal inverse-coordinate formula for the constructed isomorphism. -/
private theorem equiv_coordinate_inverse (σ : GaloisGroup k Ω) (n : ℕ+) :
    ProfiniteIntegers.π n ((equiv k Ω σ).toAdd) =
      ((frobeniusExponentCoordinates k Ω n n.pos).symm
        (restriction (finiteRootField k Ω n) σ)).toAdd := rfl

private theorem equiv_coordinate (σ : GaloisGroup k Ω) (n : ℕ+)
    (x : finiteRootField k Ω n) :
    (frobeniusExponentCoordinates k Ω n n.pos
      (Multiplicative.ofAdd (ProfiniteIntegers.π n ((equiv k Ω σ).toAdd))) x : Ω) =
      σ (x : Ω) := by
  rw [equiv_coordinate_inverse]
  change (frobeniusExponentCoordinates k Ω n n.pos
    ((frobeniusExponentCoordinates k Ω n n.pos).symm
      (restriction (finiteRootField k Ω n) σ)) x : Ω) = _
  rw [MulEquiv.apply_symm_apply, restriction_apply]

private theorem equiv_frobenius :
    equiv k Ω (globalFrobenius k Ω) = Multiplicative.ofAdd (ProfiniteIntegers.ι 1) := by
  apply Multiplicative.toAdd.injective
  apply ProfiniteIntegers.ext
  intro n
  apply Multiplicative.ofAdd.injective
  apply (frobeniusExponentCoordinates k Ω n n.pos).injective
  simp only [toAdd_ofAdd, ProfiniteIntegers.π_ι, Int.cast_one]
  change frobeniusExponentCoordinates k Ω n n.pos
    ((frobeniusExponentCoordinates k Ω n n.pos).symm
      (restriction (finiteRootField k Ω n) (globalFrobenius k Ω))) =
    frobeniusExponentCoordinates k Ω n n.pos (Multiplicative.ofAdd (1 : ZMod (n : ℕ)))
  rw [MulEquiv.apply_symm_apply, frobeniusExponentCoordinates_one]
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact restriction_apply _ _ x

/-- The unique topological group isomorphism with arithmetic Frobenius
coordinates. The displayed action is precisely λₙ(Θ(σ)ₙ) = σ|ₖₙ. -/
theorem absoluteGaloisGroup : Specs.AdvancedFieldTheory.absoluteGaloisGroup_type.{u, v} := by
  intro k Ω _ _ _ _ _
  refine ⟨fun n => frobeniusExponentCoordinates k Ω n n.pos,
    fun n a => frobeniusExponentCoordinates_intCast k Ω n n.pos a,
    equiv k Ω, ⟨equiv_coordinate k Ω, equiv_frobenius k Ω⟩, ?_⟩
  intro e he
  apply ContinuousMulEquiv.ext
  intro σ
  apply Multiplicative.toAdd.injective
  apply ProfiniteIntegers.ext
  intro n
  apply Multiplicative.ofAdd.injective
  apply (frobeniusExponentCoordinates k Ω n n.pos).injective
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact (he.1 σ n x).trans (equiv_coordinate k Ω σ n x).symm

end AbsoluteGalois
end AdvancedFieldTheory
