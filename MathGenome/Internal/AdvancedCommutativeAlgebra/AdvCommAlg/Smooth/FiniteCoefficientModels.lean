import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.FiniteCoefficientModels
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! Finite coefficient models, the first assertion of SM-15.
Mathlib's descent theorem collects the coefficients of a finite presentation
and of the identities witnessing a section modulo the square of its kernel.
It returns a subalgebra of the original base, with its canonical inclusion. -/

namespace AdvCommAlg.Smooth

universe u v

theorem exists_finite_coefficient_model :
    Specs.AdvCommAlg.Smooth.finiteCoefficientModel.{u,v} := by
  intro A B _ _ _ h
  let : Algebra.Smooth A B := h
  obtain ⟨A₀, B₀, hB₀, hAB₀, hfg, hsmooth, hequiv⟩ :=
    Algebra.Smooth.exists_subalgebra_fg ℤ A B
  let : CommRing B₀ := hB₀
  let : Algebra A₀ B₀ := hAB₀
  exact ⟨A₀, B₀, hB₀, hAB₀, hfg, Subtype.val_injective,
    ⟨A₀.fg_top.mpr hfg⟩, hsmooth, hequiv⟩

end AdvCommAlg.Smooth
