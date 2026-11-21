import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.FiberDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Flatness
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.LocalStandardCover
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Permanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SmoothAlgebras
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-! CM-17: Noetherianness, field charts, and smooth CM ascent. -/
universe u
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AdvCommAlg.CohenMacaulay

/-- Finite presentation of a smooth algebra gives the required Noetherianness. -/
theorem smooth_noetherian : Specs.smoothNoetherianType.{u} := by
  intro A B _ _ _ _ hB
  letI : Algebra.Smooth A B := hB
  exact Algebra.FiniteType.isNoetherianRing A B

namespace SmoothAlgebras

/-- Module localization of a ring is the usual localized ring. -/
def localizedSelfEquiv (R : Type u) [CommRing R] (T : Submonoid R) :
    LocalizedModule T R ≃ₗ[Localization T] Localization T :=
  (IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap T R)
    (Algebra.linearMap R (Localization T))).extendScalarsOfIsLocalization T (Localization T)

/-- The module and ring versions of the global CM predicate agree. -/
theorem cohenMacaulayRing_iff_self (R : Type u) [CommRing R] [IsNoetherianRing R] :
    CohenMacaulayRing R ↔ IsCohenMacaulay R R := by
  constructor
  · intro h p _
    exact (localCohenMacaulay_iff_of_linearEquiv
      (localizedSelfEquiv R p.asIdeal.primeCompl)).mpr (h p)
  · intro h p
    apply (localCohenMacaulay_iff_of_linearEquiv
      (localizedSelfEquiv R p.asIdeal.primeCompl)).mp
    apply h p
    exact (localizedSelfEquiv R p.asIdeal.primeCompl).symm.nontrivial

/-- SM-12 and CM-08 establish CM at every closed point of a field chart;
CM-06 then gives all primes, without an algebraic-closure descent. -/
theorem standard_smooth_field_cohenMacaulay
    (K B : Type u) [Field K] [CommRing B] [Algebra K B]
    [IsNoetherianRing B] (hB : Smooth.StandardSmooth K B) :
    CohenMacaulayRing B := by
  obtain ⟨n, c, P, hP⟩ := (Smooth.standard_smooth_iff K B).mp hB
  apply (cohenMacaulayRing_iff_self B).mpr
  apply (isCohenMacaulay_iff_maximal B).mpr
  intro m hm
  have hreg := (Smooth.standard_smooth_closed_point_regularity P hP m hm).1
  letI := hreg
  exact (localCohenMacaulay_iff_of_linearEquiv
    (localizedSelfEquiv B m.primeCompl)).mpr
      (regularLocal_cohenMacaulay (Localization.AtPrime m))

/-- Local rings of a localization are the corresponding local rings upstream. -/
theorem cohenMacaulayAt_localization_iff
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (T : Submonoid R) [IsLocalization T S] (q : PrimeSpectrum S) :
    CohenMacaulayAt S q ↔
      CohenMacaulayAt R (PrimeSpectrum.comap (algebraMap R S) q) := by
  letI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    T (Localization.AtPrime q.asIdeal) q.asIdeal
  let e := (IsLocalization.algEquiv
    (q.asIdeal.comap (algebraMap R S)).primeCompl
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
    (Localization.AtPrime q.asIdeal)).toRingEquiv
  exact (localCohenMacaulay_iff_of_semilinearEquiv _ e e.toSemilinearEquiv).symm

/-- Standard smooth neighbourhoods and the field-chart calculation give the
CM property for every smooth field algebra. -/
theorem smooth_field_cohenMacaulay
    (K B : Type u) [Field K] [CommRing B] [Algebra K B]
    [IsNoetherianRing B] (hB : Smooth.Smooth K B) :
    CohenMacaulayRing B := by
  intro q
  obtain ⟨g, hg, hstd⟩ := Smooth.exists_notMem_standardSmooth K B hB q.asIdeal
  let C := Localization.Away g
  have hd : Disjoint (Submonoid.powers g : Set B) (q.asIdeal : Set B) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  let r := q.asIdeal.map (algebraMap B C)
  letI : r.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers g) C q.asIdeal q.isPrime hd
  have hr : r.comap (algebraMap B C) = q.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) C q.isPrime hd
  have hC := standard_smooth_field_cohenMacaulay K C hstd ⟨r, inferInstance⟩
  have h := (cohenMacaulayAt_localization_iff B C (Submonoid.powers g)
    ⟨r, inferInstance⟩).mp hC
  have he : PrimeSpectrum.comap (algebraMap B C) ⟨r, inferInstance⟩ = q :=
    PrimeSpectrum.ext hr
  exact he ▸ h

/-- Flat local ascent at a point of a residue-field fiber. The library fiber
comparison identifies its local ring with the actual closed fiber quotient. -/
theorem cohenMacaulayAt_of_flat_fiber
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    (hA : CohenMacaulayAt A p) (hF : CohenMacaulayRing (p.asIdeal.Fiber B))
    (q : PrimeSpectrum (p.asIdeal.Fiber B)) :
    CohenMacaulayAt B (q.comap Algebra.TensorProduct.includeRight.toRingHom) := by
  let r := q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom
  letI : r.LiesOver p.asIdeal :=
    Ideal.comap_liesOver q.asIdeal p.asIdeal
      (Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B)
  let R := Localization.AtPrime p.asIdeal
  let S := Localization.AtPrime r
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal r
  letI : IsLocalHom (algebraMap R S) := by
    change IsLocalHom (Localization.localRingHom p.asIdeal r (algebraMap A B) _)
    infer_instance
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := Specs.closedFiberLocalRing R S
  have hJ : J = (p.asIdeal.map (algebraMap A B)).map (algebraMap B S) := by
    dsimp only [J]
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal R,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let e : Localization.AtPrime q.asIdeal ≃+* S ⧸ J :=
    (Ideal.Fiber.algEquivAux₂ p.asIdeal q.asIdeal).toRingEquiv.trans
      (Ideal.quotEquivOfEq hJ.symm)
  have hf : LocalCohenMacaulay (S ⧸ J) (S ⧸ J) :=
    (localCohenMacaulay_iff_of_semilinearEquiv _ e e.toSemilinearEquiv).mp (hF q)
  exact (flatLocal_ring_cohenMacaulay R S).mpr ⟨hA, hf⟩

end SmoothAlgebras

/-- A smooth algebra over a Noetherian CM ring is Noetherian and CM.
The field fibers are smooth by base change, and the flat local criterion
applies at every prime, including when the global rings have zero divisors. -/
theorem smooth_cohenMacaulay : Specs.smoothCohenMacaulayType.{u} := by
  intro A B _ _ _ _ hA hB
  letI : IsNoetherianRing B := smooth_noetherian A B hB
  refine ⟨inferInstance, ?_⟩
  change CohenMacaulayRing B
  letI : Module.Flat A B := Smooth.flat A B hB
  intro q
  let p := PrimeSpectrum.comap (algebraMap A B) q
  let F := p.asIdeal.Fiber B
  have hs : Smooth.Smooth p.asIdeal.ResidueField F :=
    Smooth.smooth_base_change A B p.asIdeal.ResidueField hB
  letI : IsNoetherianRing F := smooth_noetherian p.asIdeal.ResidueField F hs
  have hf : CohenMacaulayRing F :=
    SmoothAlgebras.smooth_field_cohenMacaulay p.asIdeal.ResidueField F hs
  let e := PrimeSpectrum.preimageEquivFiber A B p
  let qF := e ⟨q, rfl⟩
  have h := SmoothAlgebras.cohenMacaulayAt_of_flat_fiber A B p (hA p) hf qF
  have he : qF.comap Algebra.TensorProduct.includeRight.toRingHom = q :=
    congrArg Subtype.val (e.symm_apply_apply ⟨q, rfl⟩)
  exact he ▸ h

end AdvCommAlg.CohenMacaulay
