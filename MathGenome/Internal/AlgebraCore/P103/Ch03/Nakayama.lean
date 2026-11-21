import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.Nakayama

namespace P103.Ch03.Nakayama

open P103.Specs.Ch03.Nakayama

/-- Noncommutative Nakayama, using finite generation, with no nonzero assumption. -/
theorem eq_zero : eq_zeroType := by
  intro R M _ _ _ _ I _ hI hIM
  have hbot : (⊤ : Submodule R M) = ⊥ :=
    Module.Finite.fg_top.eq_bot_of_le_jacobson_smul
      (hIM.ge.trans (Submodule.smul_mono_left hI))
  have hz : ∀ m : M, m = 0 := by
    intro m
    have hm : m ∈ (⊥ : Submodule R M) := hbot ▸ Submodule.mem_top
    exact hm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Apply the zero-module form to the finitely generated quotient `M/N`. -/
theorem sup_iff : sup_iffType := by
  intro R M _ _ _ _ I _ hI N
  constructor
  · intro hN
    have hquot : I • (⊤ : Submodule R (M ⧸ N)) = ⊤ := by
      have hmap := congrArg (Submodule.map N.mkQ) hN
      simpa only [Submodule.map_sup, Submodule.mkQ_map_self, Submodule.map_smul'',
        Submodule.map_top, N.range_mkQ, bot_sup_eq] using hmap
    exact Submodule.Quotient.subsingleton_iff.mp (eq_zero R (M ⧸ N) I hI hquot)
  · rintro rfl
    exact top_sup_eq _

/-- Every family of lifts of generators of `M/IM` generates `M`. -/
theorem generators_lift : generators_liftType := by
  intro R M _ _ _ _ I _ hI ι g x hx hg
  apply (sup_iff R M I hI (Submodule.span R (Set.range x))).mp
  rw [sup_comm]
  apply (Submodule.map_mkQ_eq_top _ _).mp
  rw [Submodule.map_span, ← Set.range_comp']
  have heq : (fun i => (I • (⊤ : Submodule R M)).mkQ (x i)) = g := funext hx
  simpa only [heq] using hg

theorem right_eq_zero : right_eq_zeroType := by
  intro R M _ _ _ _ I _ hI hMI
  exact eq_zero Rᵐᵒᵖ M I hI hMI

theorem right_sup_iff : right_sup_iffType := by
  intro R M _ _ _ _ I _ hI N
  exact sup_iff Rᵐᵒᵖ M I hI N

theorem right_generators_lift : right_generators_liftType := by
  intro R M _ _ _ _ I _ hI ι g x hx hg
  exact generators_lift Rᵐᵒᵖ M I hI ι g x hx hg

end P103.Ch03.Nakayama
