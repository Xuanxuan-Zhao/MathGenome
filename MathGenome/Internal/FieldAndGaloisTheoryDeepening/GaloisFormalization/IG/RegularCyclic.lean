import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.RegularCyclic
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.CyclicBinomialGroup
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.GeometricGaloisGroup
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.GoodSpecialization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.QuadraticPrimeFibres

namespace GaloisFormalization.IG.RegularCyclic

open Polynomial IntermediateField CyclicBinomial
open _root_.Specs.GaloisFormalization.IG.RegularCyclic
open _root_.Specs.GaloisFormalization.IG.SpecializationData

private theorem regularAt_parameter {k : Type*} [Field k] (a : k) :
    RegularAt a (RatFunc.X : RatFunc k) := by
  simp [Specs.GaloisFormalization.IG.SpecializationData.RegularAt, RatFunc.denom_X]

private noncomputable def binomialOverRegularCoefficients {k : Type*} [Field k]
    (n : ℕ) (a : k) : Polynomial (regularCoefficients a) :=
  X ^ n - C ⟨RatFunc.X, regularAt_parameter a⟩

private theorem map_binomialOverRegularCoefficients {k : Type*} [Field k] (n : ℕ) (a : k) :
    (binomialOverRegularCoefficients n a).map (regularCoefficients a).subtype = binomial k n := by
  simp [binomialOverRegularCoefficients, binomial]

theorem binomial_regular_at : BinomialRegularAt := by
  intro k _ n a j
  rw [← map_binomialOverRegularCoefficients n a, coeff_map]
  exact ((binomialOverRegularCoefficients n a).coeff j).property

theorem binomial_specialize : BinomialSpecialize := by
  intro k _ n a hf
  have h : regularPolynomial a (binomial k n) hf = binomialOverRegularCoefficients n a := by
    apply Polynomial.map_injective (regularCoefficients a).subtype Subtype.val_injective
    exact (map_toSubring _ _ _).trans (map_binomialOverRegularCoefficients n a).symm
  change (regularPolynomial a (binomial k n) hf).map (evalRegular a) = _
  rw [h]
  simp only [binomialOverRegularCoefficients, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  change X ^ n - C (RatFunc.eval (RingHom.id k) a RatFunc.X) = _
  rw [RatFunc.eval_X]

theorem quadratic_prime_full_specialization : QuadraticPrimeFullSpecialization := by
  intro p hp L _ _ _ ℓ _ _ _
  have hf := binomial_regular_at 2 (p : ℚ)
  have hfibre := binomial_specialize 2 (p : ℚ) hf
  have hsep := quadratic_prime_fibre_separable hp
  let : IsSplittingField ℚ ℓ (specialize (p : ℚ) (binomial ℚ 2) hf) := by
    rw [hfibre]
    infer_instance
  have hm : (binomial ℚ 2).Monic := monic_X_pow_sub_C _ (by decide)
  obtain ⟨i, hroots, _, _, _, d, hreduces, _, _, _⟩ :=
    goodSpecialization ℓ (p : ℚ) (binomial ℚ 2) hf L hm (by rw [hfibre]; exact hsep)
  obtain ⟨e⟩ := quadratic_prime_fibre_galoisGroup hp ℓ
  have hunit : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr (by decide)
  obtain ⟨_, _, ⟨g⟩⟩ := cyclic_splitting_field 2 (by decide) hunit
    (-1 : ℚ) (IsPrimitiveRoot.neg_one 0 (by decide)) L inferInstance
  let : Finite (L ≃ₐ[RatFunc ℚ] L) := Finite.of_injective g g.injective
  exact ⟨hsep, ⟨e⟩, hf, i, d, hfibre, hroots, hreduces,
    (Subgroup.card_eq_iff_eq_top _).mp (Nat.card_congr ((d.trans e).trans g.symm).toEquiv)⟩

private theorem irreducible_binomial_of_equiv {D F : Type*} [Field D] [Field F]
    (e : RatFunc D ≃+* F) (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (X ^ n - C (e RatFunc.X)) := by
  have h := (binomial_irreducible (k := D) n hn).map (Polynomial.mapEquiv e)
  simpa only [Polynomial.mapEquiv_apply, binomial, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, RingEquiv.coe_toRingHom] using h

theorem geometric_cyclic_realization : GeometricCyclicRealization := by
  intro k Ω _ _ _ _ t ht _ n hn hunit ζ hζ L hsplit
  let K := adjoin k {t}
  let f : Polynomial K := X ^ n - C (AdjoinSimple.gen k t)
  let D := algebraicClosure k Ω
  let B := rationalWithConstants t D
  let P := L ⊔ B
  let : Algebra B P := (inclusion le_sup_right).toAlgebra
  let : IsSplittingField K L f := hsplit
  let : NeZero n := ⟨by omega⟩
  let eK := RatFunc.algEquivOfTranscendental t ht
  have heK : eK RatFunc.X = AdjoinSimple.gen k t :=
    Subtype.ext (RatFunc.algEquivOfTranscendental_X t ht)
  have hirr : Irreducible f := by
    simpa only [f, ← heK, AlgEquiv.coe_toRingEquiv] using
      irreducible_binomial_of_equiv eK.toRingEquiv n hn
  have htK : (AdjoinSimple.gen k t) ≠ 0 := by
    rw [← heK]
    exact (map_ne_zero eK).mpr RatFunc.X_ne_zero
  have hnK : (n : K) ≠ 0 := by
    simpa using (hunit.map (algebraMap k K)).ne_zero
  let : FiniteDimensional K L := IsSplittingField.finiteDimensional L f
  let : IsGalois K L :=
    IsGalois.of_separable_splitting_field (separable_X_pow_sub_C _ hnK htK)
  let fB : Polynomial B := X ^ n - C (algebraMap K B (AdjoinSimple.gen k t))
  have hfB : fB = f.map (algebraMap K B) := by simp [fB, f]
  -- Adjoining the same roots over the enlarged base gives the compositum.
  have hroots : fB.rootSet Ω = f.rootSet Ω := by rw [hfB, rootSet_map]
  have hL : L = adjoin K (f.rootSet Ω) := (IntermediateField.isSplittingField_iff.mp hsplit).2
  let P' : IntermediateField B Ω := IntermediateField.extendScalars (show B ≤ P from le_sup_right)
  have hP' : P' = adjoin B (fB.rootSet Ω) := by
    apply restrictScalars_injective K
    rw [hroots, restrictScalars_adjoin_eq_sup, ← hL]
    exact sup_comm L B
  have hsplitB : IsSplittingField B P fB := by
    change IsSplittingField B P' fB
    rw [hP']
    exact IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  let : IsSplittingField B P fB := hsplitB
  have : Algebra.IsAlgebraic k D := inferInstance
  have htD : Transcendental D t := ht.extendScalars (S := D)
  have hB : (adjoin D {t}).restrictScalars k = B.restrictScalars k := by
    rw [restrictScalars_adjoin_eq_sup]
    rfl
  let eB : RatFunc D ≃+* B := (RatFunc.algEquivOfTranscendental t htD).toRingEquiv.trans
    (IntermediateField.equivOfEq hB).toRingEquiv
  have heB : eB RatFunc.X = algebraMap K B (AdjoinSimple.gen k t) :=
    Subtype.ext (RatFunc.algEquivOfTranscendental_X t htD)
  have hirrB : Irreducible fB := by
    simpa only [fB, ← heB] using irreducible_binomial_of_equiv eB n hn
  let g := autEquivZmod hirr L (hζ.map_of_injective (algebraMap k K).injective)
  let gB := autEquivZmod hirrB P (hζ.map_of_injective (algebraMap k B).injective)
  let : Finite (P ≃ₐ[B] P) := Finite.of_injective gB gB.injective
  have hgeom := geometricGaloisGroup k Ω t ht L
  have honto : Function.Surjective (geometricRestriction t L) :=
    (Finite.injective_iff_surjective_of_equiv (gB.trans g.symm).toEquiv).mp hgeom.2.1
  exact ⟨hsplitB, ⟨gB⟩, hgeom.2.2.2.mp honto⟩

theorem regular_cyclic_realization : RegularCyclicRealization := by
  intro k _ n hn hunit ζ hζ
  refine ⟨orderOf_tPowerClass n hn, ?_⟩
  intro L _ _ _ _ hsplit
  have := hsplit
  obtain ⟨hfin, hgal, hcyc⟩ := cyclic_splitting_field n hn hunit ζ hζ L hsplit
  refine ⟨hfin, hgal, hcyc, ?_⟩
  let Ω := AlgebraicClosure (RatFunc k)
  let t : Ω := algebraMap (RatFunc k) Ω RatFunc.X
  have ht : Transcendental k t :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc k) Ω).injective).mpr RatFunc.transcendental_X
  let K := adjoin k {t}
  let eK := RatFunc.algEquivOfTranscendental t ht
  let : Algebra (RatFunc k) K := eK.toRingHom.toAlgebra
  have hmap : algebraMap (RatFunc k) Ω = (algebraMap K Ω).comp (algebraMap (RatFunc k) K) := by
    apply RingHom.ext
    intro x
    change algebraMap (RatFunc k) Ω x = (eK x : Ω)
    rw [RatFunc.algEquivOfTranscendental_apply]
    simp only [t, aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap, ← map_div₀,
      RatFunc.num_div_denom]
  let : IsScalarTower (RatFunc k) K Ω := IsScalarTower.of_algebraMap_eq' hmap
  let : Algebra.IsAlgebraic K Ω :=
    Algebra.IsAlgebraic.extendScalars (algebraMap (RatFunc k) K).injective
  let fK : Polynomial K := X ^ n - C (AdjoinSimple.gen k t)
  have hfK : (binomial k n).map (algebraMap (RatFunc k) K) = fK := by
    simp only [fK, binomial, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    congr 2
    exact Subtype.ext (RatFunc.algEquivOfTranscendental_X t ht)
  let M := adjoin K (fK.rootSet Ω)
  have hM : IsSplittingField K M fK :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hreg := (geometric_cyclic_realization k Ω t ht n hn hunit ζ hζ M hM).2.2
  let : Algebra (RatFunc k) M :=
    ((algebraMap K M).comp (algebraMap (RatFunc k) K)).toAlgebra
  let : IsScalarTower (RatFunc k) K M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k (RatFunc k) M := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change algebraMap k M c = algebraMap K M (eK (algebraMap k (RatFunc k) c))
    rw [eK.commutes, IsScalarTower.algebraMap_apply k K M]
  have hsplitM : ((binomial k n).map (algebraMap (RatFunc k) M)).Splits := by
    rw [IsScalarTower.algebraMap_eq (RatFunc k) K M, ← Polynomial.map_map, hfK]
    exact hM.splits'
  let j := (IsSplittingField.lift L (binomial k n) hsplitM).restrictScalars k
  apply eq_bot_iff.mpr
  intro x hx
  have hjx : j x ∈ algebraicClosure k M :=
    mem_algebraicClosure_iff.mpr ((mem_algebraicClosure_iff.mp hx).algHom j)
  change algebraicClosure k M = ⊥ at hreg
  rw [hreg] at hjx
  obtain ⟨c, hc⟩ := mem_bot.mp hjx
  exact mem_bot.mpr ⟨c, j.injective ((j.commutes c).trans hc)⟩

end GaloisFormalization.IG.RegularCyclic
