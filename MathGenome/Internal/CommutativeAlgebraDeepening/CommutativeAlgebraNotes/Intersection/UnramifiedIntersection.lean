import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.UnramifiedIntersection
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.PrimeQuotientReduction
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.UnramifiedPrimeQuotientIntersection
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.UnramifiedRegularPresentation
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory IsLocalRing
open scoped BigOperators TensorProduct
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)

namespace CommutativeAlgebraNotes.Intersection.UnramifiedIntersection

open IsolatedIntersectionEuler (intersectionEuler_eq_cutoff)
open IsolatedIntersectionEuler.Specs (intersectionEuler cutoffEuler)
open IsolatedTorSupport (isolated_tensor_iff flatTorBaseChangeEquiv)
open IsolatedTorSupport.Specs (Tor)
open IntersectionEulerCompletion
open IntersectionEulerCompletion.Specs (CompletedRing completedModuleCat)

open private baseChange_length baseChange_dimension baseChangeEquiv completion_nontrivial
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection

universe u v w

private theorem dimension_eq_support (R : Type u) [CommRing R] (L : Type v)
    [AddCommGroup L] [Module R L] [Module.Finite R L] :
    moduleDimensionValue R L = Module.supportDim R L :=
  (Module.supportDim_eq_ringKrullDim_quotient_annihilator R L).symm

private theorem dimension_quotient (R : Type u) [CommRing R] (P : Ideal R) :
    moduleDimensionValue R (R ⧸ P) = ringKrullDim (R ⧸ P) := by
  rw [dimension_eq_support, Module.supportDim_quotient_eq_ringKrullDim]

/-- Extend the dimension bound and signs from prime quotients by additivity. -/
private theorem signs_of_prime_quotients (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ)
    (hprime : ∀ (P Q : Ideal R) [P.IsPrime] [Q.IsPrime],
      let A := ModuleCat.of R (R ⧸ P)
      let B := ModuleCat.of R (R ⧸ Q)
      IsFiniteLength R (A ⊗[R] B) →
        let s := moduleDimensionValue R A + moduleDimensionValue R B
        s ≤ (d : WithBot ℕ∞) ∧
          (s < (d : WithBot ℕ∞) → intersectionEuler A B = 0) ∧
          (s = (d : WithBot ℕ∞) → 0 < intersectionEuler A B))
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hlen : IsFiniteLength R (M ⊗[R] N)) :
    let s := moduleDimensionValue R M + moduleDimensionValue R N
    s ≤ (d : WithBot ℕ∞) ∧
      (s < (d : WithBot ℕ∞) → intersectionEuler M N = 0) ∧
      (s = (d : WithBot ℕ∞) → 0 < intersectionEuler M N) := by
  classical
  obtain ⟨F⟩ := PrimeFiltration.exists_filtration R M
  obtain ⟨G⟩ := PrimeFiltration.exists_filtration R N
  obtain ⟨i, hi, hF⟩ := PrimeQuotientReduction.dimension_maximum M F inferInstance
  obtain ⟨j, hj, hG⟩ := PrimeQuotientReduction.dimension_maximum N G inferInstance
  obtain ⟨hisolated, hsum⟩ := PrimeQuotientReduction.prime_filtration_reduction M N F G
    ((isolated_tensor_iff M N).mp hlen)
  let A (a : Fin F.length) := ModuleCat.of R (R ⧸ (F.prime a).asIdeal)
  let B (b : Fin G.length) := ModuleCat.of R (R ⧸ (G.prime b).asIdeal)
  let s := moduleDimensionValue R M + moduleDimensionValue R N
  let t (a : Fin F.length) (b : Fin G.length) :=
    moduleDimensionValue R (A a) + moduleDimensionValue R (B b)
  have ht (a : Fin F.length) (b : Fin G.length) :
      t a b ≤ (d : WithBot ℕ∞) ∧
        (t a b < (d : WithBot ℕ∞) → intersectionEuler (A a) (B b) = 0) ∧
        (t a b = (d : WithBot ℕ∞) → 0 < intersectionEuler (A a) (B b)) := by
    let : (F.prime a).asIdeal.IsPrime := (F.prime a).isPrime
    let : (G.prime b).asIdeal.IsPrime := (G.prime b).isPrime
    exact hprime _ _ ((isolated_tensor_iff (A a) (B b)).mpr (hisolated a b))
  have hmax : t i j = s := by
    change moduleDimensionValue R (R ⧸ (F.prime i).asIdeal) +
      moduleDimensionValue R (R ⧸ (G.prime j).asIdeal) = _
    rw [dimension_quotient, dimension_quotient, hi, hj,
      ← dimension_eq_support R M, ← dimension_eq_support R N]
  have hle (a : Fin F.length) (b : Fin G.length) : t a b ≤ s := by
    change moduleDimensionValue R (R ⧸ (F.prime a).asIdeal) +
      moduleDimensionValue R (R ⧸ (G.prime b).asIdeal) ≤ _
    rw [dimension_quotient, dimension_quotient]
    exact add_le_add ((hF a).trans_eq (dimension_eq_support R M).symm)
      ((hG b).trans_eq (dimension_eq_support R N).symm)
  have hnonneg (a : Fin F.length) (b : Fin G.length) :
      0 ≤ intersectionEuler (A a) (B b) := by
    rcases (ht a b).1.lt_or_eq with hlt | heq
    · exact ((ht a b).2.1 hlt).symm.le
    · exact ((ht a b).2.2 heq).le
  change s ≤ _ ∧ _ ∧ _
  refine ⟨hmax ▸ (ht i j).1, ?_, ?_⟩
  · intro hs
    rw [hsum]
    exact Finset.sum_eq_zero fun a _ =>
      Finset.sum_eq_zero fun b _ => (ht a b).2.1 ((hle a b).trans_lt hs)
  · intro hs
    rw [hsum]
    exact Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ => hnonneg a b)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun b _ => hnonneg i b)
        ⟨j, Finset.mem_univ _, (ht i j).2.2 (hmax.trans hs)⟩⟩

/-- Transport the prime-quotient argument along the complete power-series presentation. -/
private theorem complete_signs (C : Type u) [CommRing C] [IsRegularLocalRing C]
    [CharZero C] [IsAdicComplete (maximalIdeal C) C]
    (p d : ℕ) (hp : p.Prime) [CharP (ResidueField C) p]
    (hd : ringKrullDim C = (d : WithBot ℕ∞)) (hunram : (p : C) ∉ maximalIdeal C ^ 2)
    (M : ModuleCat.{v} C) (N : ModuleCat.{w} C)
    [Module.Finite C M] [Module.Finite C N] [Nontrivial M] [Nontrivial N]
    (hlen : IsFiniteLength C (M ⊗[C] N)) :
    let s := moduleDimensionValue C M + moduleDimensionValue C N
    s ≤ (d : WithBot ℕ∞) ∧
      (s < (d : WithBot ℕ∞) → intersectionEuler M N = 0) ∧
      (s = (d : WithBot ℕ∞) → 0 < intersectionEuler M N) := by
  obtain ⟨hdpos, V, _, _, _, hcharV, hcompleteV, hgen, eres, φ, hφ, _, _, e, _, _⟩ :=
    CoefficientRings.unramifiedRegularPresentation C p d hp hd hunram
  let : CharZero V := hcharV
  let : IsAdicComplete (maximalIdeal V) V := hcompleteV
  let : Fact p.Prime := ⟨hp⟩
  let : CharP (ResidueField V) p := eres.toRingHom.charP eres.injective p
  have hpV : Irreducible (p : V) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hgen
  let R := MvPowerSeries (Fin (d - 1)) V
  have hsize : d - 1 + 1 = d := by omega
  obtain ⟨hreg, hdim, _, hprime⟩ :=
    UnramifiedPrimeQuotientIntersection.primeQuotientIntersection V p hpV (d - 1)
  let : IsRegularLocalRing R := hreg
  have hdR : ringKrullDim R = (d : WithBot ℕ∞) := by
    simpa only [hsize] using hdim
  let : Algebra C R := e.symm.toRingHom.toAlgebra
  have hb : Function.Bijective (algebraMap C R) := e.symm.bijective
  let : Module.Flat C R := Module.Flat.of_linearEquiv
    (LinearEquiv.ofBijective (Algebra.linearMap C R) hb).symm
  let M' := ModuleCat.of R (R ⊗[C] M)
  let N' := ModuleCat.of R (R ⊗[C] N)
  let : Module.Finite R M' := inferInstanceAs (Module.Finite R (R ⊗[C] M))
  let : Module.Finite R N' := inferInstanceAs (Module.Finite R (R ⊗[C] N))
  let : Nontrivial M' := (baseChangeEquiv hb M).injective.nontrivial
  let : Nontrivial N' := (baseChangeEquiv hb N).injective.nontrivial
  have hlen' : IsFiniteLength R (M' ⊗[R] N') := by
    apply Module.length_ne_top_iff.mp
    rw [← (TensorProduct.AlgebraTensorModule.distribBaseChange C R M N).length_eq,
      baseChange_length hb]
    exact Module.length_ne_top_iff.mpr hlen
  have hsigns := signs_of_prime_quotients R d
    (by simpa only [hsize] using hprime) M' N' hlen'
  have hdimM : moduleDimensionValue R M' = moduleDimensionValue C M :=
    baseChange_dimension e.symm rfl M
  have hdimN : moduleDimensionValue R N' = moduleDimensionValue C N :=
    baseChange_dimension e.symm rfl N
  have hEuler : intersectionEuler M' N' = intersectionEuler M N := by
    change IsolatedIntersectionEuler.intersectionEuler M' N' =
      IsolatedIntersectionEuler.intersectionEuler M N
    rw [intersectionEuler_eq_cutoff M' N' d hdR, intersectionEuler_eq_cutoff M N d hd]
    simp only [IsolatedIntersectionEuler.cutoffEuler, cutoffEuler]
    apply Finset.sum_congr rfl
    intro i _
    let P := P103.Ch11.ExtTorDefinitions.resolutionFamily C M
    let torEquiv : R ⊗[C] Tor M N i ≃ₗ[R] Tor M' N' i :=
      flatTorBaseChangeEquiv M N P.val P.property i
    rw [← torEquiv.length_eq, baseChange_length hb]
  simpa only [hdimM, hdimN, hEuler] using hsigns

/-- The image of an element outside the square of the maximal ideal remains
outside that square after completion, by evaluation modulo the square. -/
private theorem completion_unramified (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : ℕ) (hp : (p : R) ∉ maximalIdeal R ^ 2) :
    (p : CompletedRing R) ∉ maximalIdeal (CompletedRing R) ^ 2 := by
  intro h
  let I := maximalIdeal R
  let f := AdicCompletion.evalₐ I 2
  have hz : (maximalIdeal (CompletedRing R)) ^ 2 ≤ RingHom.ker f := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro x hx
    change f (algebraMap R (CompletedRing R) x) = 0
    rw [AlgHom.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hcast : f (p : CompletedRing R) = (Ideal.Quotient.mk (I ^ 2)) (p : R) := by
    rw [map_natCast, map_natCast]
  apply hp
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hcast ▸ hz h)

/-- Serre's dimension bound and signs for an isolated intersection in an
unramified mixed-characteristic regular local ring. -/
theorem unramifiedIntersection : Specs.unramifiedIntersectionType.{u,v,w} := by
  intro R _ _ _ p d hp _ hd hunram M N _ _ _ _ hlen
  let C := CompletedRing R
  obtain ⟨hreg, hEuler⟩ := completion_euler M N hlen
  let : IsRegularLocalRing C := hreg
  let : Module.FaithfullyFlat R C := AdvCommAlg.CohenMacaulay.completion_faithfullyFlat R
  let : CharZero C := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective R C)
  let : CharP (ResidueField C) p :=
    charP_of_injective_ringHom
      (AdicCompletion.residueField_map_bijective R).injective p
  let Mc := completedModuleCat M
  let Nc := completedModuleCat N
  change intersectionEuler Mc Nc = intersectionEuler M N at hEuler
  let : Module.Finite C Mc := completion_module_finite R M
  let : Module.Finite C Nc := completion_module_finite R N
  let : Nontrivial Mc := completion_nontrivial M
  let : Nontrivial Nc := completion_nontrivial N
  have hsigns := complete_signs C p d hp ((completion_ring_dimension R).trans hd)
    (completion_unramified R p hunram) Mc Nc (completion_tensor_finite_length M N hlen)
  have hdimM : moduleDimensionValue C Mc = moduleDimensionValue R M :=
    (dimension_eq_support C Mc).trans
      ((completion_module_dimension R M).trans (dimension_eq_support R M).symm)
  have hdimN : moduleDimensionValue C Nc = moduleDimensionValue R N :=
    (dimension_eq_support C Nc).trans
      ((completion_module_dimension R N).trans (dimension_eq_support R N).symm)
  simpa only [hdimM, hdimN, hEuler] using hsigns

end CommutativeAlgebraNotes.Intersection.UnramifiedIntersection
