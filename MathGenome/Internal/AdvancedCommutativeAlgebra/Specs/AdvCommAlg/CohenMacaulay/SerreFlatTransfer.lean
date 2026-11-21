import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SerreDepthConditions
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! CM-11, paper.tex:3615–3620 and 3635–3645. The descent hypothesis is
Serre's condition on the entire spectrum of the indicated local ring.
The ascent hypothesis uses the displayed source fiber `S ⊗[R] κ(p)`.
The proof also uses the standard library fiber `κ(p) ⊗[R] S`. -/
universe u
open scoped TensorProduct
noncomputable section
namespace AdvCommAlg.CohenMacaulay.Specs

/-- Fibers of a map with Noetherian target are Noetherian: they are quotients
of localizations of the target. No finite-type hypothesis is needed. -/
theorem fiberNoetherian (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] (p : PrimeSpectrum R) : IsNoetherianRing (p.asIdeal.Fiber S) := by
  letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  exact isNoetherianRing_of_ringEquiv _
    (Ideal.Fiber.algEquivQuotient (S := S) p.asIdeal).toRingEquiv.symm

/-- The source's tensor order has the same Noetherian property. -/
theorem rightFiberNoetherian (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] (p : PrimeSpectrum R) :
    IsNoetherianRing (S ⊗[R] p.asIdeal.ResidueField) := by
  letI := fiberNoetherian R S p
  exact isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv

noncomputable def ringSerreCondition_localization_descentType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (k : ℕ) (q : PrimeSpectrum S),
    RingSerreConditionValue (Localization.AtPrime q.asIdeal) k →
    RingSerreConditionValue
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R S) q).asIdeal) k

noncomputable def ringSerreCondition_flat_ascentType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] (k : ℕ),
    RingSerreConditionValue R k →
    (∀ p : PrimeSpectrum R,
      letI := rightFiberNoetherian R S p
      RingSerreConditionValue (S ⊗[R] p.asIdeal.ResidueField) k) →
    RingSerreConditionValue S k

end AdvCommAlg.CohenMacaulay.Specs
