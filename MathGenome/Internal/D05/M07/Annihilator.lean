import MathGenome.Internal.D05.M02.Subspace
import MathGenome.Internal.D05.M03.Kernel
import MathGenome.Internal.D05.M07.Dual
import MathGenome.Internal.Specs.D05.M07.Annihilator

/-! K05.07.annihilator: annihilators and preannihilators in their actual spaces. -/

namespace D05.M07.Annihilator

/-- Functionals in the algebraic dual which vanish on U. -/
abbrev annihilator (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) : Submodule K (Module.Dual K V) :=
  U.dualAnnihilator

/-- Vectors of V killed by every functional in the arbitrary set F. -/
abbrev preannihilator (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (F : Set (Module.Dual K V)) : Submodule K V :=
  (Submodule.span K F).dualCoannihilator

theorem annihilator_eq_set : Specs.D05.M07.Annihilator.annihilator_eq_set := by
  intro K V _ _ _ U
  ext f
  exact Submodule.mem_dualAnnihilator f

theorem preannihilator_eq_set : Specs.D05.M07.Annihilator.preannihilator_eq_set := by
  intro K V _ _ _ F
  exact Submodule.coe_dualCoannihilator_span F

theorem annihilator_linear_combination :
    Specs.D05.M07.Annihilator.annihilator_linear_combination := by
  intro K V _ _ _ U a b f g hf hg
  exact U.dualAnnihilator.add_mem (U.dualAnnihilator.smul_mem a hf)
    (U.dualAnnihilator.smul_mem b hg)

theorem preannihilator_linear_combination :
    Specs.D05.M07.Annihilator.preannihilator_linear_combination := by
  intro K V _ _ _ F a b u v hu hv
  exact (preannihilator K V F).add_mem ((preannihilator K V F).smul_mem a hu)
    ((preannihilator K V F).smul_mem b hv)

theorem preannihilator_eq_iInf : Specs.D05.M07.Annihilator.preannihilator_eq_iInf := by
  intro K V _ _ _ F
  ext v
  rw [← SetLike.mem_coe, preannihilator_eq_set]
  simp only [Set.mem_setOf_eq, Submodule.mem_iInf, LinearMap.mem_ker]

theorem annihilator_antitone : Specs.D05.M07.Annihilator.annihilator_antitone := by
  intro K V _ _ _ U W h
  exact Submodule.dualAnnihilator_anti h

theorem preannihilator_antitone : Specs.D05.M07.Annihilator.preannihilator_antitone := by
  intro K V _ _ _ F G h
  exact Submodule.dualCoannihilator_anti (Submodule.span_mono h)

end D05.M07.Annihilator
