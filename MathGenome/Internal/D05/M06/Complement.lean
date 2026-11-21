import MathGenome.Internal.Specs.D05.M06.Complement
import MathGenome.Internal.D05.M06.DirectSum
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! K05.06.complement: existence and the explicit nonuniqueness example. -/

namespace D05.M06.Complement

theorem exists_complement_sup_inf : Specs.D05.M06.Complement.exists_complement_sup_inf := by
  intro K V _ _ _ _ U
  obtain ⟨W, hW⟩ := U.exists_isCompl
  exact ⟨W, hW.sup_eq_top, hW.inf_eq_bot⟩

theorem exists_complement : Specs.D05.M06.Complement.exists_complement := by
  intro K V _ _ _ _ U
  obtain ⟨W, hW⟩ := exists_complement_sup_inf U
  exact ⟨W, (D05.M06.DirectSum.pair_internal_iff_sup_inf U W).mpr hW⟩

theorem exists_complement_equiv : Specs.D05.M06.Complement.exists_complement_equiv := by
  intro K V _ _ _ _ U
  obtain ⟨W, hW⟩ := U.exists_isCompl
  refine ⟨W, (D05.M06.DirectSum.pair_internal_iff_sup_inf U W).mpr
    ⟨hW.sup_eq_top, hW.inf_eq_bot⟩, U.prodEquivOfIsCompl W hW, ?_⟩
  intro u w
  rfl

/-- Every line of slope vector `(a, 1)` complements the first coordinate line.
The explicit decomposition of `(x, y)` is `(x - ya, 0) + (ya, y)`. -/
theorem coordinate_line_isCompl {K : Type*} [Field K] (a : K) :
    IsCompl (Submodule.span K ({(1, 0)} : Set (K × K)))
      (Submodule.span K ({(a, 1)} : Set (K × K))) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hxU hxW
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hxU
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxW
    have hx₂ : x.2 = 0 := by
      simpa using (congrArg Prod.snd hb).symm
    have hc₀ : c = 0 := by
      simpa [hx₂] using congrArg Prod.snd hc
    simpa [hc₀] using hc.symm
  · apply codisjoint_iff.mpr
    apply Submodule.eq_top_iff'.mpr
    intro x
    refine Submodule.mem_sup.mpr
      ⟨(x.1 - x.2 * a, 0), ?_, (x.2 * a, x.2), ?_, ?_⟩
    · apply Submodule.mem_span_singleton.mpr
      exact ⟨x.1 - x.2 * a, by ext <;> simp⟩
    · apply Submodule.mem_span_singleton.mpr
      exact ⟨x.2, by ext <;> simp⟩
    · ext <;> simp

theorem coordinate_complements : Specs.D05.M06.Complement.coordinate_complements := by
  intro K _
  dsimp only
  have h₀ := coordinate_line_isCompl (0 : K)
  have h₁ := coordinate_line_isCompl (1 : K)
  refine ⟨(D05.M06.DirectSum.pair_internal_iff_sup_inf _ _).mpr
    ⟨h₀.sup_eq_top, h₀.inf_eq_bot⟩, ?_, ?_⟩
  · simpa using (D05.M06.DirectSum.pair_internal_iff_sup_inf _ _).mpr
      ⟨h₁.sup_eq_top, h₁.inf_eq_bot⟩
  · intro heq
    have hmem : ((1, 0) + (0, 1) : K × K) ∈
        Submodule.span K ({(0, 1)} : Set (K × K)) := by
      rw [heq]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hzero : (0 : K) = 1 := by
      simpa using congrArg Prod.fst ha
    exact zero_ne_one hzero

end D05.M06.Complement
