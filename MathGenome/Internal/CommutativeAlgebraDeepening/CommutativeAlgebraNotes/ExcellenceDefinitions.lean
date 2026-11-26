import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.UniversalCatenarity
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.RingTheory.Finiteness.Small

/-! Definition 5.1 and comparisons with the library regularity and
catenarity predicates. -/

universe u v w
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence

def RegularRing : Specs.RegularRingType.{u} := Specs.RegularRingValue
def GeometricallyRegular : Specs.GeometricallyRegularType.{u,v} := Specs.GeometricallyRegularValue
def RegularMap : Specs.RegularMapType.{u,v} := Specs.RegularMapValue
abbrev FormalFiber : Specs.FormalFiberType.{u} := Specs.FormalFiberValue
def IsGRing : Specs.IsGRingType.{u} := Specs.IsGRingValue
def regularLocus : Specs.regularLocusType.{u} := Specs.regularLocusValue
def J2 : Specs.J2Type.{u} := Specs.J2Value
def Catenary : Specs.CatenaryType.{u} := Specs.CatenaryValue
def UniversallyCatenary : Specs.UniversallyCatenaryType.{u} := Specs.UniversallyCatenaryValue
def QuasiExcellent : Specs.QuasiExcellentType.{u} := Specs.QuasiExcellentValue
def Excellent : Specs.ExcellentType.{u} := Specs.ExcellentValue

theorem regularRing_iff (R : Type u) [CommRing R] [IsNoetherianRing R] :
    RegularRing R ↔ IsRegularRing R :=
  isRegularRing_iff.symm

theorem regularMap_algebraMap_iff (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B] :
    RegularMap A B (algebraMap A B) ↔ Module.Flat A B ∧
      ∀ (p : Ideal A) [p.IsPrime], GeometricallyRegular p.ResidueField (p.Fiber B) := by
  let fibers (alg : Algebra A B) : Prop :=
    letI : Algebra A B := alg
    ∀ (p : Ideal A) [p.IsPrime], GeometricallyRegular p.ResidueField (p.Fiber B)
  change ((algebraMap A B).Flat ∧ fibers (algebraMap A B).toAlgebra) ↔
    (Module.Flat A B ∧ fibers inferInstance)
  rw [RingHom.flat_algebraMap_iff, toAlgebra_algebraMap]

theorem catenary_iff (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Catenary R ↔ AdvCommAlg.CohenMacaulay.Catenary R := by
  constructor
  · intro h
    constructor
    · intro p q hpq S hS
      let := AdvCommAlg.CohenMacaulay.finiteDimensional_prime_interval p q hpq
      let : WellFoundedLT (Set.Icc p q) :=
        SetRel.IsWellFounded.of_finiteDimensional {(a, b) : Set.Icc p q × Set.Icc p q | a < b}
      let : WellFoundedGT (Set.Icc p q) :=
        SetRel.IsWellFounded.inv_of_finiteDimensional {(a, b) : Set.Icc p q × Set.Icc p q | a < b}
      exact hS.lt_of_le.finite_of_wellFoundedLT_of_wellFoundedGT
    · intro p q hpq
      obtain ⟨c, hc₁, hc₂⟩ := AdvCommAlg.CohenMacaulay.exists_saturated_prime_chain p q hpq
      refine ⟨c, hc₁, hc₂, fun d hd₁ hd₂ => ?_⟩
      exact h p q hpq d c hd₁ hd₂ hc₁ hc₂
  · intro h p q hpq c d hc₁ hc₂ hd₁ hd₂
    obtain ⟨_, _, _, hlength⟩ := h.2 p q hpq
    exact (hlength c hc₁ hc₂).trans (hlength d hd₁ hd₂).symm

theorem universallyCatenary_iff (R : Type u) [CommRing R] [IsNoetherianRing R] :
    UniversallyCatenary R ↔
      ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B],
        AdvCommAlg.CohenMacaulay.Catenary B := by
  constructor
  · intro h B _ _ _
    let := Algebra.FiniteType.isNoetherianRing R B
    exact (catenary_iff B).mp (h B)
  · intro h B _ _ _
    let := Algebra.FiniteType.isNoetherianRing R B
    exact (catenary_iff B).mpr (h B)

/-- Finite extensions in any universe can be tested by shrinking the field
and transporting the scalar extension along a tensor product equivalence. -/
theorem GeometricallyRegular.regular_tensorProduct {k : Type u} {T : Type v} [Field k] [CommRing T]
    [Algebra k T] (h : GeometricallyRegular k T) (L : Type w)
    [Field L] [Algebra k L] [Module.Finite k L] :
    IsNoetherianRing (L ⊗[k] T) ∧ RegularRing (L ⊗[k] T) := by
  let := Module.Finite.small.{u} k L
  let e := (Algebra.TensorProduct.congr (Shrink.algEquiv.{u} k L)
    (AlgEquiv.refl : T ≃ₐ[k] T)).toRingEquiv
  obtain ⟨hnoeth, hreg⟩ := h (Shrink.{u} L)
  have hreg' : IsRegularRing (Shrink.{u} L ⊗[k] T) :=
    (regularRing_iff _).mp hreg
  have := isNoetherianRing_of_ringEquiv _ e
  exact ⟨inferInstance, (regularRing_iff _).mpr (IsRegularRing.of_ringEquiv e)⟩

/-- Openness holds for finite-type algebras in any universe. -/
theorem J2.isOpen_regularLocus {R : Type u} [CommRing R] [IsNoetherianRing R]
    (h : J2 R) (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] :
    IsOpen (regularLocus B) := by
  let := Algebra.FiniteType.small (R := R) (S := B)
  let e : Shrink.{u} B ≃ₐ[R] B := Shrink.algEquiv R B
  let := Algebra.FiniteType.of_surjective e.symm.toAlgHom e.symm.surjective
  let f := (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm
  have heq : regularLocus B = f ⁻¹' regularLocus (Shrink.{u} B) := by
    ext p
    let q := PrimeSpectrum.comap e.toRingEquiv.toRingHom p
    change IsRegularLocalRing (Localization.AtPrime p.asIdeal) ↔
      IsRegularLocalRing (Localization.AtPrime q.asIdeal)
    have hmap : q.asIdeal.primeCompl.map e.toRingEquiv.toMonoidHom = p.asIdeal.primeCompl :=
      e.toRingEquiv.map_primeCompl_comap_eq p.asIdeal
    let eqv := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime p.asIdeal) e.toRingEquiv hmap
    exact ⟨fun h => IsRegularLocalRing.of_ringEquiv eqv.symm,
      fun h => IsRegularLocalRing.of_ringEquiv eqv⟩
  rw [heq]
  exact (h (Shrink.{u} B)).preimage f.continuous

/-- Universal catenarity tests finite-type algebras in any universe. -/
theorem UniversallyCatenary.catenary {R : Type u} [CommRing R] [IsNoetherianRing R]
    (h : UniversallyCatenary R) (B : Type v) [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] : Catenary B := by
  let := Algebra.FiniteType.small (R := R) (S := B)
  let e : Shrink.{u} B ≃ₐ[R] B := Shrink.algEquiv R B
  let := Algebra.FiniteType.of_surjective e.symm.toAlgHom e.symm.surjective
  let := Algebra.FiniteType.isNoetherianRing R (Shrink.{u} B)
  let := Algebra.FiniteType.isNoetherianRing R B
  exact (catenary_iff B).mpr (AdvCommAlg.CohenMacaulay.catenary_of_surjective
    (Shrink.{u} B) B e.toRingHom e.surjective ((catenary_iff _).mp (h (Shrink.{u} B))))

end CommutativeAlgebraNotes.Excellence
