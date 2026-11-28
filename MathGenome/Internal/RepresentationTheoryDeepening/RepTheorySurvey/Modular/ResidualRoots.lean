import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SplittingSystem
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.ResidualRoots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Reduction and lifting of prime-to-`p` roots of unity. -/

namespace RepTheorySurvey.Modular

universe uG uO uK

variable {G : Type uG} [Group G] [Finite G] {p : ℕ}
  {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K]

local notation "m" => primeToPart G p
local notation "k" => IsLocalRing.ResidueField O
local notation "reduceRoots" => restrictRootsOfUnity (IsLocalRing.residue O) m

theorem fractionRoots_surjective (S : SplittingSystem G p O K) :
    Function.Surjective (restrictRootsOfUnity (algebraMap O K) m) := by
  let : IsFractionRing O K := S.fractionRing
  let : NeZero m := ⟨(primeToPart_pos G p).ne'⟩
  intro u
  have hu : (u.val.val : K) ^ m = 1 := (mem_rootsOfUnity' _ _).mp u.property
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := O) (x := u.val.val) (NeZero.pos m) (by rw [hu]; exact isIntegral_one)
  have hxpow : x ^ m = 1 := IsFractionRing.injective O K (by rw [map_pow, hx, hu, map_one])
  exact ⟨rootsOfUnity.mkOfPowEq x hxpow, rootsOfUnity.coe_injective hx⟩

theorem primeToPart_residue_ne_zero (S : SplittingSystem G p O K) : (m : k) ≠ 0 := by
  let : CharP k p := S.residueChar
  exact fun h => (S.prime.coprime_iff_not_dvd.mp
    (primeToPart_greatest G S.prime).2.1.symm) ((CharP.cast_eq_zero_iff k p m).mp h)

private theorem residualRoots_injective (S : SplittingSystem G p O K) :
    Function.Injective reduceRoots := by
  apply (injective_iff_map_eq_one reduceRoots).mpr
  intro u hu
  let x : O := u.val.val
  have hx : x ^ m = 1 := (mem_rootsOfUnity' _ _).mp u.property
  have hred : IsLocalRing.residue O x = 1 := congrArg (fun v : rootsOfUnity m k => v.val.val) hu
  have hsum : (∑ i ∈ Finset.range m, x ^ i) ≠ 0 := by
    intro hzero
    have h := congrArg (IsLocalRing.residue O) hzero
    exact primeToPart_residue_ne_zero S (by simpa only [map_sum, map_pow, hred, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h)
  have hprod : (x - 1) * (∑ i ∈ Finset.range m, x ^ i) = 0 := by
    rw [mul_geom_sum, hx, sub_self]
  exact rootsOfUnity.coe_injective (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum))

private theorem primeToPart_le_card_integralRoots (S : SplittingSystem G p O K) :
    m ≤ Nat.card (rootsOfUnity m O) := by
  let : NeZero m := ⟨(primeToPart_pos G p).ne'⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : K, IsPrimitiveRoot ζ m := S.primitiveRoot
  calc
    m = Nat.card (rootsOfUnity m K) := hζ.card_rootsOfUnity.symm
    _ ≤ Nat.card (rootsOfUnity m O) := Nat.card_le_card_of_surjective _ (fractionRoots_surjective S)

/-- Reduction on `m`-th roots of unity is bijective. -/
theorem residualRoots_bijective (S : SplittingSystem G p O K) :
    Function.Bijective reduceRoots := by
  let : NeZero m := ⟨(primeToPart_pos G p).ne'⟩
  exact (residualRoots_injective S).bijective_of_nat_card_le
    ((card_rootsOfUnity k m).trans (primeToPart_le_card_integralRoots S))

/-- Reduction on `m`-th roots of unity is a multiplicative equivalence. -/
noncomputable def residualRootsEquiv (S : SplittingSystem G p O K) :
    rootsOfUnity m O ≃* rootsOfUnity m k where
  toFun := reduceRoots
  invFun := Function.invFun reduceRoots
  left_inv := Function.leftInverse_invFun (residualRoots_bijective S).injective
  right_inv := Function.rightInverse_invFun (residualRoots_bijective S).surjective
  map_mul' := map_mul reduceRoots

/-- The unique integral lift of an `m`-th root of unity in the residue field. -/
noncomputable def residualRootLift (S : SplittingSystem G p O K) (v : rootsOfUnity m k) :
    rootsOfUnity m O := (residualRootsEquiv S).symm v

@[simp]
theorem residualRootsEquiv_apply (S : SplittingSystem G p O K) (u : rootsOfUnity m O) :
    residualRootsEquiv S u = reduceRoots u := rfl

@[simp]
theorem reduce_residualRootLift (S : SplittingSystem G p O K) (v : rootsOfUnity m k) :
    reduceRoots (residualRootLift S v) = v := (residualRootsEquiv S).apply_symm_apply v

theorem exists_residualRootsEquiv (S : SplittingSystem G p O K) :
    ∃ e : rootsOfUnity m O ≃* rootsOfUnity m k,
      (∀ u, e u = reduceRoots u) ∧ (∀ v, e.symm v = residualRootLift S v) :=
  ⟨residualRootsEquiv S, fun _ => rfl, fun _ => rfl⟩

theorem exists_residue_isPrimitiveRoot (S : SplittingSystem G p O K) :
    ∃ ζ : k, IsPrimitiveRoot ζ m := by
  let : NeZero m := ⟨(primeToPart_pos G p).ne'⟩
  apply card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp
  apply le_antisymm (card_rootsOfUnity k m)
  calc
    m ≤ Nat.card (rootsOfUnity m O) := primeToPart_le_card_integralRoots S
    _ = Nat.card (rootsOfUnity m k) := Nat.card_congr (residualRootsEquiv S).toEquiv

end RepTheorySurvey.Modular
