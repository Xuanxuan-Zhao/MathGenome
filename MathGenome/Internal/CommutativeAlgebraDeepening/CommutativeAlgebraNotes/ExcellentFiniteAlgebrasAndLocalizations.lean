import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteAndLocalizedGRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalizingRegularLociAndChains

universe u v

namespace CommutativeAlgebraNotes.Excellence

/-- Every finite algebra over an excellent ring is excellent. -/
theorem Excellent.of_finite {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (h : Excellent A) : Excellent B := by
  obtain ⟨hNoetherian, hG, hJ2, hCatenary⟩ := h
  let : IsNoetherianRing A := hNoetherian
  exact ⟨IsNoetherianRing.of_finite A B, isGRing_finite hG,
    J2.of_finiteType hJ2, UniversallyCatenary.of_finiteType hCatenary⟩

/-- Every localization of an excellent ring is excellent. -/
theorem Excellent.of_isLocalization {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (M : Submonoid A) [IsLocalization M B] (h : Excellent A) : Excellent B := by
  obtain ⟨hNoetherian, hG, hJ2, hCatenary⟩ := h
  let : IsNoetherianRing A := hNoetherian
  exact ⟨IsLocalization.isNoetherianRing M B hNoetherian, isGRing_localization M hG,
    J2.of_isLocalization M hJ2, UniversallyCatenary.of_isLocalization M hCatenary⟩

end CommutativeAlgebraNotes.Excellence
