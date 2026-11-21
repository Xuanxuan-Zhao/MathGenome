import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.MaximalTori
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootDecomposition
import Batteries.Tactic.OpenPrivate

/-! LA-D02: ordinary root spaces and their opposite Killing pairings. -/

universe u
namespace LieAlgebrasAndRepresentations

open private toral_genWeightSpace_eq_weightSpace from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.MaximalTori

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

abbrev rootSpace (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) : Submodule ℂ L :=
  Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value H α

abbrev rootSet (H : LieSubalgebra ℂ L) : Set (Module.Dual ℂ H) :=
  Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSet_value H

abbrev rootSummand (H : LieSubalgebra ℂ L) : Option (rootSet H) → Submodule ℂ L :=
  Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSummand_value H

noncomputable abbrev rootPairing (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) :=
  Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootPairing_value H α

@[simp] theorem mem_rootSpace (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) (x : L) :
    x ∈ rootSpace H α ↔ ∀ h : H, ⁅(h : L), x⁆ = α h • x := by
  change x ∈ LieModule.weightSpace L (α : H → ℂ) ↔ _
  simpa only [LieSubalgebra.coe_bracket_of_module] using LieModule.mem_weightSpace (α : H → ℂ) x

theorem rootSpace_eq_bot_of_not_mem (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H)
    (hα : α ≠ 0) (ha : α ∉ rootSet H) : rootSpace H α = ⊥ := by
  by_contra hn
  exact ha ⟨hα, hn⟩

theorem rootSpace_bracket (H : LieSubalgebra ℂ L) (α β : Module.Dual ℂ H) (x y : L)
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) :
    ⁅x, y⁆ ∈ rootSpace H (α + β) := by
  rw [mem_rootSpace] at hx hy ⊢
  intro h
  rw [leibniz_lie, hx h, hy h, smul_lie, lie_smul, LinearMap.add_apply, add_smul]

theorem rootSpace_zero [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) :
    rootSpace H 0 = H.toSubmodule := by
  have he : rootSpace H 0 = (toralCentralizer H).toSubmodule := by
    ext x
    simp only [mem_rootSpace, LinearMap.zero_apply, zero_smul, LieSubalgebra.mem_toSubmodule,
      mem_toralCentralizer]
  rw [he, maximal_toral_centralizer hss H hH]

private theorem rootSpace_eq_gen [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (hH : IsToral H) :
    letI : IsLieAbelian H := hH.1
    ∀ α : Module.Dual ℂ H,
      rootSpace H α = (LieModule.genWeightSpace L (α : H → ℂ)).toSubmodule := by
  letI : IsLieAbelian H := hH.1
  intro α
  exact congrArg LieSubmodule.toSubmodule
    (toral_genWeightSpace_eq_weightSpace H hH α).symm

/-- Independence and spanning use ordinary eigenspaces because each toral
adjoint endomorphism is semisimple. -/
theorem rootSpace_independent [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (hH : IsToral H) :
    iSupIndep (rootSpace H) := by
  letI : IsLieAbelian H := hH.1
  have hi := (LieSubmodule.iSupIndep_toSubmodule.mpr
    (LieModule.iSupIndep_genWeightSpace ℂ H L)).comp
      (show Function.Injective (fun α : Module.Dual ℂ H => (α : H → ℂ)) from
        DFunLike.coe_injective)
  convert hi using 1
  funext α
  exact rootSpace_eq_gen H hH α

theorem iSup_rootSpace_eq_top [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (hH : IsToral H) :
    (⨆ α : Module.Dual ℂ H, rootSpace H α) = ⊤ := by
  letI : IsLieAbelian H := hH.1
  have hs : (⨆ χ : LieModule.Weight ℂ H L,
      (LieModule.genWeightSpace L (χ : H → ℂ)).toSubmodule) = ⊤ :=
    LieSubmodule.iSup_toSubmodule_eq_top.mpr (LieModule.iSup_genWeightSpace_eq_top' ℂ H L)
  apply top_unique
  rw [← hs]
  refine iSup_le fun χ => ?_
  have he := rootSpace_eq_gen H hH (χ : Module.Dual ℂ H)
  simp only [LieModule.Weight.coe_coe] at he
  rw [← he]
  exact le_iSup (rootSpace H) (χ : Module.Dual ℂ H)

theorem rootSet_finite [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (hH : IsToral H) : (rootSet H).Finite := by
  have hf := WellFoundedGT.finite_ne_bot_of_iSupIndep (rootSpace_independent H hH)
  exact hf.subset fun _ ha => ha.2

noncomputable local instance (H : LieSubalgebra ℂ L) : DecidableEq (Option (rootSet H)) := Classical.decEq _

/-- The canonical summation map from H and the nonzero root spaces is bijective. -/
theorem root_decomposition [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) :
    DirectSum.IsInternal (rootSummand H) := by
  classical
  let f : Option (rootSet H) → Module.Dual ℂ H := fun i => i.elim 0 Subtype.val
  have hf : Function.Injective f := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some β => exact False.elim (β.property.1 hij.symm)
    | some α =>
      cases j with
      | none => exact False.elim (α.property.1 hij)
      | some β => exact congrArg some (Subtype.ext hij)
  have he : rootSummand H = fun i => rootSpace H (f i) := by
    funext i
    cases i with
    | none => exact (rootSpace_zero hss H hH).symm
    | some α => rfl
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [he]
    exact (rootSpace_independent H hH.1).comp hf
  · apply top_unique
    rw [← iSup_rootSpace_eq_top H hH.1]
    refine iSup_le fun α => ?_
    by_cases hα : α = 0
    · subst α
      rw [rootSpace_zero hss H hH]
      exact le_iSup (rootSummand H) none
    · by_cases ha : rootSpace H α = ⊥
      · simp [ha]
      · exact le_iSup (rootSummand H) (some ⟨α, hα, ha⟩)

/-- Invariance forces (α(h)+β(h)) B(x,y)=0 for each h. -/
theorem rootSpace_killing_orthogonal [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (α β : Module.Dual ℂ H) (x y : L)
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (hab : α + β ≠ 0) :
    killingForm ℂ L x y = 0 := by
  have hn : ∃ h : H, (α + β) h ≠ 0 := by
    by_contra! hn
    exact hab (LinearMap.ext hn)
  obtain ⟨h, hh⟩ := hn
  have hi := killingForm_invariant ℂ L x (h : L) y
  rw [← lie_skew x (h : L), (mem_rootSpace H α x).mp hx h,
    (mem_rootSpace H β y).mp hy h] at hi
  have hi' : -(α h * killingForm ℂ L x y) = β h * killingForm ℂ L x y := by
    simpa only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply,
      smul_eq_mul, neg_mul] using hi
  have hz : (α h + β h) * killingForm ℂ L x y = 0 := by
    rw [add_mul, ← hi', add_neg_cancel]
  exact (mul_eq_zero.mp hz).resolve_left hh

/-- A vector orthogonal to its opposite space is orthogonal to every weight
space, hence to the whole algebra. -/
private theorem rootSpace_pairing_separating [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α : Module.Dual ℂ H) (x : L) (hx : x ∈ rootSpace H α)
    (hz : ∀ y ∈ rootSpace H (-α), killingForm ℂ L x y = 0) : x = 0 := by
  apply ((semisimple_iff_killingForm_nondegenerate ℂ L).mp hss).1 x
  intro y
  have hy : y ∈ ⨆ β : Module.Dual ℂ H, rootSpace H β := by
    rw [iSup_rootSpace_eq_top H hH.1]
    trivial
  refine Submodule.iSup_induction (rootSpace H)
    (motive := fun z => killingForm ℂ L x z = 0) hy (fun β y hy => ?_) ?_
    (fun y z hy hz => ?_)
  · by_cases hab : α + β = 0
    · have he : β = -α := (add_eq_zero_iff_neg_eq.mp hab).symm
      exact hz y (he ▸ hy)
    · exact rootSpace_killing_orthogonal H α β x y hx hy hab
  · simp
  · simp [hy, hz]

theorem rootPairing_perfect [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (α : Module.Dual ℂ H) :
    (rootPairing H α).IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    apply Subtype.ext
    change (x : L) = 0
    apply rootSpace_pairing_separating hss H hH α x x.property
    intro y hy
    exact congrArg (fun f => f ⟨y, hy⟩) (LinearMap.mem_ker.mp hx)
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro y hy
    apply Subtype.ext
    change (y : L) = 0
    apply rootSpace_pairing_separating hss H hH (-α) y y.property
    intro x hx
    rw [neg_neg] at hx
    rw [killingForm_symmetric]
    exact congrArg (fun f => f ⟨x, hx⟩) (LinearMap.mem_ker.mp hy)

theorem killingForm_restrict_toral_nondegenerate [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) :
    ((killingForm ℂ L).restrict H.toSubmodule).Nondegenerate := by
  have hs : ∀ (x : H), (∀ y : H, killingForm ℂ L (x : L) (y : L) = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    change (x : L) = 0
    apply rootSpace_pairing_separating hss H hH 0 x
    · rw [rootSpace_zero hss H hH]
      exact x.property
    · intro y hy
      rw [neg_zero, rootSpace_zero hss H hH] at hy
      exact hx ⟨y, hy⟩
  refine ⟨hs, ?_⟩
  intro x hx
  apply hs x
  intro y
  rw [killingForm_symmetric]
  exact hx y

end LieAlgebrasAndRepresentations
