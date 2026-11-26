import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion

/-! Ideal torsion and integer-graded local cohomology for modules. -/

open CategoryTheory
open scoped ZeroObject

namespace CommutativeAlgebraNotes

universe v u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The submodule `Γ_I(M)` of elements killed by a power of `I`. -/
abbrev idealTorsion (M : Type v) [AddCommGroup M] [Module R M] : Submodule R M :=
  Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsion I M

theorem mem_idealTorsion {M : Type v} [AddCommGroup M] [Module R M] (x : M) :
    x ∈ idealTorsion I M ↔ ∃ n : ℕ, 1 ≤ n ∧ ∀ a ∈ I ^ n, a • x = 0 := by
  simp only [idealTorsion, Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsion,
    Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff, SetCoe.forall, SetLike.mem_coe]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, Nat.succ_pos n, fun a ha => hn a (Ideal.pow_le_pow_right (Nat.le_succ n) ha)⟩
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩

/-- The annihilators of `I^(n+1)` increase with `n` and have supremum `Γ_I(M)`. -/
theorem idealTorsion_union (M : Type v) [AddCommGroup M] [Module R M] :
    (Monotone fun n : ℕ => Submodule.torsionBySet R M (↑(I ^ (n + 1)) : Set R)) ∧
      idealTorsion I M = ⨆ n : ℕ, Submodule.torsionBySet R M (↑(I ^ (n + 1)) : Set R) := by
  constructor
  · intro m n h
    exact Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.succ_le_succ h) I
  · change (⨆ n : ℕ, Submodule.torsionBySet R M (↑(I ^ n) : Set R)) = _
    refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun n => ?_)
    · exact (Submodule.torsionBySet_le_torsionBySet_pow n (n + 1) (Nat.le_succ n) I).trans
        (le_iSup (fun k : ℕ => Submodule.torsionBySet R M (↑(I ^ (k + 1)) : Set R)) n)
    · exact le_iSup (fun k : ℕ => Submodule.torsionBySet R M (↑(I ^ k) : Set R)) (n + 1)

/-- The functor that sends `M` to `Γ_I(M)` and restricts maps to those submodules. -/
abbrev idealTorsionFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsionFunctor I

theorem idealTorsionFunctor_additive : (idealTorsionFunctor.{v} I).Additive := inferInstance

/-- The natural inclusion `Γ_I ⟶ Id`. -/
abbrev idealTorsionInclusion : idealTorsionFunctor.{v} I ⟶ 𝟭 (ModuleCat.{v} R) :=
  Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsionInclusion I

/-- The local cohomology functor `H_I^q` on `R`-modules. -/
noncomputable abbrev localCohomology [Small.{v} R] (q : ℤ) : ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  Specs.CommutativeAlgebraNotes.IdealTorsion.localCohomology I q

theorem localCohomology_of_nonneg [Small.{v} R] (q : ℤ) (hq : 0 ≤ q) :
    localCohomology.{v} I q = (idealTorsionFunctor I).rightDerived q.toNat := by
  cases q with
  | ofNat n => rfl
  | negSucc n => exact (Int.not_le.mpr (Int.negSucc_lt_zero n) hq).elim

theorem localCohomology_of_neg [Small.{v} R] (q : ℤ) (hq : q < 0) :
    localCohomology.{v} I q = 0 := by
  cases q with
  | ofNat n => exact (Int.not_lt.mpr (Int.natCast_nonneg n) hq).elim
  | negSucc n => rfl

end CommutativeAlgebraNotes
