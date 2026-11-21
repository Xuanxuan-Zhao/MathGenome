import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.InfiniteDimensionalBoundary
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2Model
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWOrdered
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section

open scoped Classical

namespace LieAlgebrasAndRepresentations.InfiniteDimensionalBoundary

open Specs.LieAlgebrasAndRepresentations.InfiniteDimensionalBoundary
open Specs.LieAlgebrasAndRepresentations.Sl2Model
open Shared.Lie.PBW UniversalEnvelopingAlgebra
open _root_.Shared.Lie (augmentation)

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (k : Type u) [Field k]

abbrev vermaZero := VermaZero
abbrev highestVector := highest
abbrev loweringVector := loweringString

private abbrev lowering : Env k := ι k (F k)
private abbrev cartanGenerator : Env k := ι k (H k)
private abbrev raising : Env k := ι k (E k)

/-- The order puts the lowering generator first and the raising generator last. -/
private def triangularBasis : Module.Basis (Fin 3) k (Model k) :=
  (Module.Basis.ofEquivFun (sl2Coordinates k)).reindex
    (Equiv.swap 0 1 |>.trans (Equiv.swap 1 2))

private theorem triangularBasis_zero : triangularBasis k 0 = F k := by
  have h : ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)).symm 0 = 1 := by decide
  rw [triangularBasis, Module.Basis.reindex_apply, h, Module.Basis.coe_ofEquivFun]
  apply (sl2Coordinates k).injective
  rw [LinearEquiv.apply_symm_apply, sl2Coordinates_apply]
  ext i
  fin_cases i <;> simp [sl2_f_val]

private theorem triangularBasis_one : triangularBasis k 1 = H k := by
  have h : ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)).symm 1 = 2 := by decide
  rw [triangularBasis, Module.Basis.reindex_apply, h, Module.Basis.coe_ofEquivFun]
  apply (sl2Coordinates k).injective
  rw [LinearEquiv.apply_symm_apply, sl2Coordinates_apply]
  ext i
  fin_cases i <;> simp [sl2_h_val]

private theorem triangularBasis_two : triangularBasis k 2 = E k := by
  have h : ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)).symm 2 = 0 := by decide
  rw [triangularBasis, Module.Basis.reindex_apply, h, Module.Basis.coe_ofEquivFun]
  apply (sl2Coordinates k).injective
  rw [LinearEquiv.apply_symm_apply, sl2Coordinates_apply]
  ext i
  fin_cases i <;> simp [sl2_e_val]

private def orderedPowers (a b c : ℕ) : OrderedWord (Fin 3) :=
  ⟨List.replicate a 0 ++ List.replicate b 1 ++ List.replicate c 2, by
    simp [List.pairwise_append, List.mem_replicate]⟩

private theorem orderedPowers_cover (l : OrderedWord (Fin 3)) :
    ∃ a b c, l = orderedPowers a b c := by
  refine ⟨l.val.count 0, l.val.count 1, l.val.count 2, Subtype.ext ?_⟩
  refine List.Perm.eq_of_pairwise' l.property (orderedPowers _ _ _).property ?_
  apply List.perm_iff_count.mpr
  intro i
  fin_cases i <;> simp [orderedPowers, List.count_append, List.count_replicate]

private abbrev pbw := orderedBasis (triangularBasis k)

private theorem pbw_powers (a b c : ℕ) :
    pbw k (orderedPowers a b c) = lowering k ^ a * cartanGenerator k ^ b * raising k ^ c := by
  simp [orderedBasis_apply, orderedMonomial, monomial, orderedPowers, Shared.Lie.word,
    List.prod_append, List.prod_replicate, triangularBasis_zero, triangularBasis_one,
    triangularBasis_two, mul_assoc]

/-- Keep only the coefficients of the pure lowering monomials. -/
private def pureCoefficients : Env k →ₗ[k] (ℕ →₀ k) :=
  (pbw k).constr k fun l =>
    if ∀ i ∈ l.val, i = 0 then Finsupp.single l.val.length 1 else 0

private theorem pureCoefficients_powers (a b c : ℕ) :
    pureCoefficients k (lowering k ^ a * cartanGenerator k ^ b * raising k ^ c) =
      if b = 0 ∧ c = 0 then Finsupp.single a 1 else 0 := by
  rw [← pbw_powers, pureCoefficients, Module.Basis.constr_basis]
  cases b with
  | zero =>
    cases c with
    | zero => simp [orderedPowers, List.mem_replicate]
    | succ c =>
      have h : ¬ ∀ i ∈ (orderedPowers a 0 (c+1)).val, i = 0 := by
        intro h
        exact (by decide : (2 : Fin 3) ≠ 0) (h 2 (by simp [orderedPowers]))
      simp [h]
  | succ b =>
    have h : ¬ ∀ i ∈ (orderedPowers a (b+1) c).val, i = 0 := by
      intro h
      exact (by decide : (1 : Fin 3) ≠ 0) (h 1 (by simp [orderedPowers]))
    simp [h]

private theorem raising_mul_cartan :
    raising k * cartanGenerator k = (cartanGenerator k - algebraMap k (Env k) 2) * raising k := by
  have h := (ι k).map_lie (H k) (E k)
  rw [(sl2_relations k).1, map_smul, LieRing.of_associative_ring_bracket] at h
  rw [sub_mul, ← Algebra.smul_def]
  apply eq_sub_of_add_eq
  rw [add_comm]
  exact (sub_eq_iff_eq_add.mp h.symm).symm

private theorem raising_pow_mul_cartan (c : ℕ) :
    raising k ^ c * cartanGenerator k =
      (cartanGenerator k - algebraMap k (Env k) (2 * (c : k))) * raising k ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ, mul_assoc, raising_mul_cartan, ← mul_assoc, mul_sub, ih]
    rw [← (Algebra.commutes (R := k) (2 : k) (raising k ^ c)),
      ← mul_assoc, ← sub_mul, sub_sub, ← map_add, Nat.cast_succ, mul_add, mul_one]

private theorem pureCoefficients_mul_raising (x : Env k) :
    pureCoefficients k (x * raising k) = 0 := by
  have h : (pureCoefficients k).comp (LinearMap.mulRight k (raising k)) = 0 := by
    apply (pbw k).ext
    intro l
    obtain ⟨a,b,c,rfl⟩ := orderedPowers_cover l
    change pureCoefficients k (pbw k (orderedPowers a b c) * raising k) = 0
    rw [pbw_powers, mul_assoc, ← pow_succ, pureCoefficients_powers]
    simp
  exact LinearMap.congr_fun h x

private theorem pureCoefficients_mul_cartan (x : Env k) :
    pureCoefficients k (x * cartanGenerator k) = 0 := by
  have h : (pureCoefficients k).comp (LinearMap.mulRight k (cartanGenerator k)) = 0 := by
    apply (pbw k).ext
    intro l
    obtain ⟨a,b,c,rfl⟩ := orderedPowers_cover l
    change pureCoefficients k (pbw k (orderedPowers a b c) * cartanGenerator k) = 0
    rw [pbw_powers]
    cases c with
    | zero =>
      rw [pow_zero, mul_one, mul_assoc, ← pow_succ]
      simpa using (pureCoefficients_powers k a (b+1) 0)
    | succ c =>
      rw [mul_assoc, raising_pow_mul_cartan, pow_succ (raising k) c]
      simp only [← mul_assoc, pureCoefficients_mul_raising]
  exact LinearMap.congr_fun h x

private theorem cartan_mem_ideal : cartanGenerator k ∈ definingIdeal k :=
  Submodule.subset_span (by simp)

private theorem raising_mem_ideal : raising k ∈ definingIdeal k :=
  Submodule.subset_span (by simp)

private def projection : VermaZero k →ₗ[k] (ℕ →₀ k) :=
  ((definingIdeal k).restrictScalars k).liftQ (pureCoefficients k) (by
    intro x hx
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp (show x ∈ definingIdeal k from hx)
    change pureCoefficients k (a * cartanGenerator k + b * raising k) = 0
    simp only [map_add, pureCoefficients_mul_cartan, pureCoefficients_mul_raising, add_zero])

private theorem loweringString_eq_mkQ (j : ℕ) :
    loweringString k j = (definingIdeal k).mkQ (lowering k ^ j) := by
  unfold loweringString highest
  rw [← map_smul]
  change (definingIdeal k).mkQ (lowering k ^ j * 1) = _
  rw [mul_one]

private theorem projection_string (j : ℕ) :
    projection k (loweringString k j) = Finsupp.single j 1 := by
  rw [loweringString_eq_mkQ]
  change pureCoefficients k (lowering k ^ j) = _
  simpa using pureCoefficients_powers k j 0 0

theorem negativeStringBasis : negativeStringBasisType.{u} := by
  intro k _
  have hi : LinearIndependent k (loweringString k) := by
    apply LinearIndependent.of_comp (projection k)
    simpa only [Function.comp_def, projection_string, Finsupp.coe_basisSingleOne] using
      (Finsupp.basisSingleOne (R := k) (ι := ℕ)).linearIndependent
  let S := Submodule.span k (Set.range (loweringString k))
  let q := (definingIdeal k).mkQ.restrictScalars k
  have hspan : (Submodule.span k (Set.range (pbw k))).map q ≤ S := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨l,rfl⟩,rfl⟩
    obtain ⟨a,b,c,rfl⟩ := orderedPowers_cover l
    change (definingIdeal k).mkQ (pbw k (orderedPowers a b c)) ∈ S
    rw [pbw_powers]
    cases c with
    | succ c =>
      rw [pow_succ, ← mul_assoc]
      have h : (definingIdeal k).mkQ
          ((lowering k ^ a * cartanGenerator k ^ b * raising k ^ c) * raising k) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr
          ((definingIdeal k).smul_mem _ (raising_mem_ideal k))
      rw [h]
      exact S.zero_mem
    | zero =>
      rw [pow_zero, mul_one]
      cases b with
      | succ b =>
        rw [pow_succ, ← mul_assoc]
        have h : (definingIdeal k).mkQ
            ((lowering k ^ a * cartanGenerator k ^ b) * cartanGenerator k) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).mpr
            ((definingIdeal k).smul_mem _ (cartan_mem_ideal k))
        rw [h]
        exact S.zero_mem
      | zero =>
        rw [pow_zero, mul_one, ← loweringString_eq_mkQ]
        exact Submodule.subset_span (Set.mem_range_self a)
  have hs : Function.Surjective q := (definingIdeal k).mkQ_surjective
  rw [(pbw k).span_eq, Submodule.map_top, LinearMap.range_eq_top.mpr hs] at hspan
  exact ⟨Module.Basis.mk hi hspan, Module.Basis.mk_apply hi hspan⟩

theorem infiniteDimension : infiniteDimensionType.{u} := by
  intro k _
  obtain ⟨b, hb⟩ := negativeStringBasis k
  have hi : LinearIndependent k (loweringString k) := by
    rw [show loweringString k = (b : ℕ → VermaZero k) from funext fun j => (hb j).symm]
    exact b.linearIndependent
  refine ⟨hi, fun hf => ?_⟩
  let := hf
  exact Module.Finite.not_linearIndependent_of_infinite _ hi

private theorem highest_is_weight_zero : ⁅H k, highest k⁆ = 0 := by
  change cartanGenerator k • (definingIdeal k).mkQ 1 = _
  rw [← map_smul]
  change (definingIdeal k).mkQ (cartanGenerator k * 1) = 0
  rw [mul_one]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (cartan_mem_ideal k)

private theorem loweringString_succ (n : ℕ) : loweringString k (n+1) = ⁅F k, loweringString k n⁆ := by
  change lowering k ^ (n+1) • highest k = lowering k • (lowering k ^ n • highest k)
  rw [pow_succ', mul_smul]

private theorem loweringString_weight (n : ℕ) :
    ⁅H k, loweringString k n⁆ = (-2 * (n : k)) • loweringString k n := by
  induction n with
  | zero => simpa [loweringString] using highest_is_weight_zero k
  | succ n ih =>
    rw [loweringString_succ, leibniz_lie, (sl2_relations k).2.1, ih,
      smul_lie, lie_smul (R := k), ← add_smul, Nat.cast_succ]
    congr 1
    ring

theorem zeroWeight : zeroWeightType.{u} := by
  intro k _ _
  obtain ⟨b,hb⟩ := negativeStringBasis k
  have hcoord (j : ℕ) (m : VermaZero k) :
      b.repr ⁅H k, m⁆ j = (-2 * (j : k)) * b.repr m j := by
    let c := b.coord j
    let T := LieModule.toEnd k (Model k) (VermaZero k) (H k)
    have h : c.comp T = (-2 * (j : k)) • c := by
      apply b.ext
      intro i
      change b.repr ⁅H k, b i⁆ j = (-2 * (j : k)) * b.repr (b i) j
      rw [hb i, loweringString_weight, map_smul, ← hb i, Module.Basis.repr_self]
      by_cases hij : i = j
      · subst i
        simp
      · simp [hij]
    exact LinearMap.congr_fun h m
  constructor
  · intro m
    constructor
    · intro hm
      let a := b.repr m 0
      refine ⟨a, b.repr.injective ?_⟩
      have hb0 : b 0 = highest k := by simpa [loweringString] using hb 0
      rw [map_smul, ← hb0, Module.Basis.repr_self]
      ext j
      cases j with
      | zero => simp [a]
      | succ j =>
        have hz := hcoord (j+1) m
        rw [hm, map_zero, Finsupp.zero_apply] at hz
        have hscalar : (-2 * ((j+1 : ℕ) : k)) ≠ 0 := by
          exact mul_ne_zero (neg_ne_zero.mpr (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
        have hv : b.repr m (j+1) = 0 := (mul_eq_zero.mp hz.symm).resolve_left hscalar
        simpa [Finsupp.single_apply] using hv
    · rintro ⟨a,rfl⟩
      rw [lie_smul (R := k), highest_is_weight_zero, smul_zero]
  · rw [← show loweringString k 0 = highest k by simp [loweringString],
      ← loweringString_succ, ← hb]
    exact b.ne_zero 1

private def quotientMap : VermaZero k →ₗ⁅k, Model k⁆ TrivialLine k := by
  let ε := augmentation k (Model k)
  letI : Module (Env k) k := Module.compHom k ε.toRingHom
  letI : IsScalarTower k (Env k) k := IsScalarTower.of_algebraMap_smul fun a x => by
    change ε (algebraMap k (Env k) a) * x = a * x
    rw [AlgHom.commutes]
    rfl
  let ev := LinearMap.toSpanSingleton (Env k) k (1 : k)
  have hkill : definingIdeal k ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    intro x hx
    change ε x * 1 = 0
    rcases (show x = cartanGenerator k ∨ x = raising k by simpa using hx) with rfl | rfl
    · simp [ε, augmentation]
    · simp [ε, augmentation]
  let q := (definingIdeal k).liftQ ev hkill
  exact { q.restrictScalars k with
    map_lie' := fun {x m} => by
      change q (ι k x • m) = 0
      rw [map_smul]
      change ε (ι k x) * q m = 0
      simp [ε, augmentation] }

private theorem quotientMap_mkQ (x : Env k) :
    quotientMap k ((definingIdeal k).mkQ x) =
      (show TrivialLine k from augmentation k (Model k) x) := by
  change augmentation k (Model k) x * 1 = augmentation k (Model k) x
  rw [mul_one]

private theorem quotientMap_highest :
    quotientMap k (highest k) = (show TrivialLine k from (1 : k)) := by
  rw [highest, quotientMap_mkQ]
  exact map_one (augmentation k (Model k))

private theorem quotientMap_surjective : Function.Surjective (quotientMap k) := by
  intro a
  refine ⟨(TrivialLieModule.equiv k (Model k) k a) • highest k, ?_⟩
  rw [map_smul, quotientMap_highest]
  change (TrivialLieModule.equiv k (Model k) k a) * 1 = a
  rw [mul_one]
  rfl

private theorem trivialLine_irreducible : LieModule.IsIrreducible k (Model k) (TrivialLine k) := by
  let : Nontrivial (TrivialLine k) :=
    (TrivialLieModule.equiv k (Model k) k).symm.injective.nontrivial
  apply LieModule.IsIrreducible.mk
  intro N hN
  obtain ⟨x, hx, hxn⟩ := N.toSubmodule.ne_bot_iff.mp (by
    intro h
    apply hN
    exact LieSubmodule.toSubmodule_injective (h.trans LieSubmodule.bot_toSubmodule.symm))
  apply top_unique
  intro y _
  have hscalar : TrivialLieModule.equiv k (Model k) k x ≠ 0 :=
    fun h => hxn ((TrivialLieModule.equiv k (Model k) k).map_eq_zero_iff.mp h)
  have hm := N.smul_mem ((TrivialLieModule.equiv k (Model k) k y) /
    (TrivialLieModule.equiv k (Model k) k x)) hx
  have hy : ((TrivialLieModule.equiv k (Model k) k y) /
      (TrivialLieModule.equiv k (Model k) k x)) • x = y := by
    apply (TrivialLieModule.equiv k (Model k) k).injective
    exact div_mul_cancel₀ _ hscalar
  exact hy ▸ hm

private theorem no_invariant_vector [CharZero k] (m : VermaZero k)
    (hh : ⁅H k, m⁆ = 0) (hf : ⁅F k, m⁆ = 0) : m = 0 := by
  obtain ⟨a,rfl⟩ := ((zeroWeight k).1 m).mp hh
  rw [lie_smul (R := k)] at hf
  have ha := (smul_eq_zero.mp hf).resolve_right (zeroWeight k).2
  rw [ha, zero_smul]

theorem nonsplitQuotient : nonsplitQuotientType.{u} := by
  intro k _ _
  refine ⟨quotientMap k, quotientMap_surjective k, quotientMap_highest k, ?_,
    trivialLine_irreducible k, ?_⟩
  · intro j
    rw [loweringString_eq_mkQ, quotientMap_mkQ]
    change augmentation k (Model k) (lowering k ^ (j+1)) = 0
    simp [augmentation, pow_succ]
  · rintro ⟨s, hs⟩
    let one : TrivialLine k := (1 : k)
    have hh : ⁅H k, s one⁆ = 0 :=
      (s.map_lie (H k) one).symm.trans (map_zero s)
    have hf : ⁅F k, s one⁆ = 0 :=
      (s.map_lie (F k) one).symm.trans (map_zero s)
    have h := hs one
    rw [no_invariant_vector k (s one) hh hf, map_zero] at h
    exact zero_ne_one (show (0 : k) = 1 from h)

private theorem sl2_semisimple [CharZero k] :
    Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k (Model k) := by
  let : FiniteDimensional k (Model k) := (sl2Coordinates k).symm.finiteDimensional
  change LieAlgebra.radical k (Model k) = ⊥
  obtain h | h := (sl2_simple k).eq_bot_or_eq_top (LieAlgebra.radical k (Model k))
  · exact h
  exfalso
  have hsolv : LieAlgebra.IsSolvable (⊤ : LieIdeal k (Model k)) :=
    h ▸ LieAlgebra.radicalIsSolvable k (Model k)
  let : LieAlgebra.IsSolvable (Model k) :=
    (LieAlgebra.solvable_iff_equiv_solvable LieIdeal.topEquiv).mp hsolv
  let : Nontrivial (Model k) := (sl2Coordinates k).symm.injective.nontrivial
  have htop : LieAlgebra.derivedSeries k (Model k) 1 ≠ ⊤ := ne_of_lt
    (LieAlgebra.derivedSeries_lt_top_of_solvable k (Model k))
  have hzero := ((sl2_simple k).eq_bot_or_eq_top _).resolve_right htop
  exact sl2_nonabelian k
    ((lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv).mp
      ((LieAlgebra.abelian_iff_derived_one_eq_bot (⊤ : LieIdeal k (Model k))).mpr hzero))

private theorem eq_zero_of_quotient_injective [CharZero k]
    (W : LieSubmodule k (Model k) (VermaZero k))
    (hW : Function.Injective ((quotientMap k).comp W.incl)) (w : W) : (w : VermaZero k) = 0 := by
  have hz (x : Model k) : ⁅x,w⁆ = 0 := hW (by
    rw [LieModuleHom.map_lie, map_zero, trivial_lie_zero])
  exact no_invariant_vector k w.val (congrArg Subtype.val (hz (H k)))
    (congrArg Subtype.val (hz (F k)))

theorem noInvariantComplement : noInvariantComplementType.{u} := by
  intro k _ _
  refine ⟨(sl2Coordinates k).symm.finiteDimensional, sl2_semisimple k, (quotientMap k).ker, ?_⟩
  rintro ⟨C,hC⟩
  have hsurj : Function.Surjective ((quotientMap k).comp C.incl) := by
    intro a
    obtain ⟨m,rfl⟩ := quotientMap_surjective k a
    have hm : m ∈ (quotientMap k).ker ⊔ C := hC.sup_eq_top.symm ▸ LieSubmodule.mem_top m
    obtain ⟨w,hw,c,hc,rfl⟩ := (LieSubmodule.mem_sup _ _ _).mp hm
    refine ⟨⟨c,hc⟩, ?_⟩
    change quotientMap k c = quotientMap k (w+c)
    rw [map_add, LieModuleHom.mem_ker.mp hw, zero_add]
  have hinj : Function.Injective ((quotientMap k).comp C.incl) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro c hc
    apply Subtype.ext
    change c.val = 0
    have hm : c.val ∈ (quotientMap k).ker ⊓ C := ⟨LieModuleHom.mem_ker.mpr hc, c.property⟩
    rw [hC.inf_eq_bot] at hm
    exact (LieSubmodule.mem_bot _).mp hm
  obtain ⟨c, hc⟩ := hsurj (show TrivialLine k from (1 : k))
  have hm := eq_zero_of_quotient_injective k C hinj c
  change quotientMap k c.val = _ at hc
  rw [hm, map_zero] at hc
  exact zero_ne_one (show (0 : k) = 1 from hc)

theorem noSimpleDecomposition : noSimpleDecompositionType.{u} := by
  intro k _ _ S hsimple hsum
  have hle (W : S) : W.val.toSubmodule ≤ (quotientMap k).ker.toSubmodule := by
    let f := (quotientMap k).comp W.val.incl
    let := hsimple W.val W.property
    rcases IsSimpleOrder.eq_bot_or_eq_top f.ker with h | h
    · have hi := f.ker_eq_bot.mp h
      intro x hx
      have hx0 := eq_zero_of_quotient_injective k W.val hi ⟨x, hx⟩
      exact LieModuleHom.mem_ker.mpr (by rw [show x = 0 from hx0, map_zero])
    · intro x hx
      have hx' : (⟨x,hx⟩ : W.val) ∈ f.ker := h.symm ▸ LieSubmodule.mem_top _
      exact LieModuleHom.mem_ker.mpr (LieModuleHom.mem_ker.mp hx')
  have hs : ⨆ W : S, W.val.toSubmodule ≤ (quotientMap k).ker.toSubmodule := iSup_le hle
  rw [hsum.submodule_iSup_eq_top] at hs
  have h := LieModuleHom.mem_ker.mp (show highest k ∈ (quotientMap k).ker from
    hs Submodule.mem_top)
  rw [quotientMap_highest] at h
  exact one_ne_zero (show (1 : k) = 0 from h)

section ComplexComparison

open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple positive)
open LieAlgebrasAndRepresentations (mem_rootSpace)

private theorem diagonal_member (y : diagonalCartan) : ∃ a : ℂ, a • H ℂ = (y : Model ℂ) :=
  Submodule.mem_span_singleton.mp y.property

private theorem diagonal_dual_ext {α β : Module.Dual ℂ diagonalCartan}
    (h : α diagonalGenerator = β diagonalGenerator) : α = β := by
  ext y
  obtain ⟨a, ha⟩ := diagonal_member y
  have hy : y = a • diagonalGenerator := Subtype.ext ha.symm
  rw [hy, map_smul, map_smul, h]

private theorem adjoint_diagonal (x : Model ℂ) :
    ⁅H ℂ, x⁆ = (2 * x.val 0 1) • E ℂ + (-2 * x.val 1 0) • F ℂ := by
  conv_lhs => arg 2; rw [sl2_expansion ℂ x]
  simp only [lie_add, lie_smul (R := ℂ), (sl2_relations ℂ).1,
    (sl2_relations ℂ).2.1, lie_self, smul_zero, add_zero, smul_smul]
  rw [mul_comm (x.val 0 1), mul_comm (x.val 1 0)]

private theorem adjoint_diagonal_coordinates {x : Model ℂ} {a : ℂ}
    (hx : ⁅H ℂ, x⁆ = a • x) :
    2 * x.val 0 1 = a * x.val 0 1 ∧
    -2 * x.val 1 0 = a * x.val 1 0 ∧ 0 = a * x.val 0 0 := by
  rw [adjoint_diagonal] at hx
  refine ⟨?_, ?_, ?_⟩
  · simpa [SetLike.val_smul, sl2_e_val, sl2_f_val] using
      congrArg (fun y : Model ℂ => y.val 0 1) hx
  · simpa [SetLike.val_smul, sl2_e_val, sl2_f_val] using
      congrArg (fun y : Model ℂ => y.val 1 0) hx
  · simpa [SetLike.val_smul, sl2_e_val, sl2_f_val] using
      congrArg (fun y : Model ℂ => y.val 0 0) hx

private theorem diagonal_isCartan : diagonalCartan.IsCartanSubalgebra := by
  constructor
  · change LieModule.IsNilpotent diagonalCartan diagonalCartan
    apply (LieModule.isNilpotent_iff_exists_ucs_eq_top ℂ).mpr
    refine ⟨1, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 by rfl, LieSubmodule.ucs_succ, LieSubmodule.ucs_zero]
    apply top_unique
    intro y _
    rw [LieSubmodule.mem_normalizer]
    intro x
    apply (LieSubmodule.mem_bot _).mpr
    apply Subtype.ext
    obtain ⟨a, ha⟩ := diagonal_member x
    obtain ⟨b, hb⟩ := diagonal_member y
    change ⁅(x : Model ℂ), (y : Model ℂ)⁆ = 0
    rw [← ha, ← hb]
    simp
  · apply le_antisymm _ (LieSubalgebra.le_normalizer _)
    intro x hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      ((diagonalCartan.mem_normalizer_iff' x).mp hx (H ℂ) diagonalGenerator.property)
    have h01 := congrArg (fun y : Model ℂ => y.val 0 1) ha
    have h10 := congrArg (fun y : Model ℂ => y.val 1 0) ha
    have he : x.val 0 1 = 0 := by
      rw [adjoint_diagonal] at h01
      simp [SetLike.val_smul, sl2_h_val, sl2_e_val, sl2_f_val] at h01
      exact h01
    have hf : x.val 1 0 = 0 := by
      rw [adjoint_diagonal] at h10
      simp [SetLike.val_smul, sl2_h_val, sl2_e_val, sl2_f_val] at h10
      exact h10
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x.val 0 0, ?_⟩
    symm
    simpa [he, hf] using sl2_expansion ℂ x

private noncomputable def positiveRoot : Module.Dual ℂ diagonalCartan where
  toFun y := 2 * (y : Model ℂ).val 0 0
  map_add' x y := by
    change (2 : ℂ) * ((x : Model ℂ).val 0 0 + (y : Model ℂ).val 0 0) = _
    exact mul_add _ _ _
  map_smul' a y := by
    change (2 : ℂ) * (a * (y : Model ℂ).val 0 0) = a * (2 * (y : Model ℂ).val 0 0)
    exact mul_left_comm _ _ _

private theorem positiveRoot_eval : positiveRoot diagonalGenerator = 2 := by
  change 2 * (H ℂ).val 0 0 = 2
  simp [sl2_h_val]

private theorem e_in_positiveRoot : E ℂ ∈ rootSpace_value diagonalCartan positiveRoot := by
  apply (mem_rootSpace _ _ _).mpr
  intro y
  obtain ⟨a, ha⟩ := diagonal_member y
  have hy : y = a • diagonalGenerator := Subtype.ext ha.symm
  rw [hy, map_smul, positiveRoot_eval]
  change ⁅a • H ℂ, E ℂ⁆ = (a * 2) • E ℂ
  rw [smul_lie, (sl2_relations ℂ).1, smul_smul]

private theorem e_ne_zero : E ℂ ≠ 0 := by
  intro h
  have he := congrArg (fun y : Model ℂ => y.val 0 1) h
  simp [sl2_e_val] at he

private theorem root_eval {α : Module.Dual ℂ diagonalCartan}
    (hα : α ∈ rootSet_value diagonalCartan) :
    α diagonalGenerator = 2 ∨ α diagonalGenerator = -2 := by
  have hn : α diagonalGenerator ≠ 0 := fun h => hα.1 (diagonal_dual_ext h)
  obtain ⟨x,hx,hxn⟩ := (Submodule.ne_bot_iff _).mp hα.2
  have hweight := (mem_rootSpace _ _ _).mp hx diagonalGenerator
  have ⟨he, hf, hh⟩ := adjoint_diagonal_coordinates hweight
  by_contra hab
  have h01 : x.val 0 1 = 0 := by
    by_contra hne
    exact hab (Or.inl (mul_right_cancel₀ hne he.symm))
  have h10 : x.val 1 0 = 0 := by
    by_contra hne
    exact hab (Or.inr (mul_right_cancel₀ hne hf.symm))
  have h00 : x.val 0 0 = 0 := (mul_eq_zero.mp hh.symm).resolve_left hn
  apply hxn
  simpa [h01, h10, h00] using sl2_expansion ℂ x

private theorem direction_apply (α : Module.Dual ℂ diagonalCartan) :
    standardDirection α = (α diagonalGenerator).re := rfl

private theorem direction_regular : Regular diagonalCartan standardDirection := by
  intro α hα
  rcases root_eval hα with h | h <;> rw [direction_apply, h] <;> norm_num

private theorem positive_eval {α : Module.Dual ℂ diagonalCartan}
    (hα : α ∈ positive diagonalCartan standardDirection) :
    α diagonalGenerator = 2 := by
  rcases root_eval hα.1 with h | h
  · exact h
  · exfalso
    have hh := hα.2
    rw [direction_apply, h] at hh
    norm_num at hh

private theorem positiveRoot_simple : positiveRoot ∈ simple diagonalCartan standardDirection := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro h
    have hh := congrArg (fun α : Module.Dual ℂ diagonalCartan => α diagonalGenerator) h
    norm_num [positiveRoot_eval] at hh
  · exact (Submodule.ne_bot_iff _).mpr ⟨E ℂ, e_in_positiveRoot, e_ne_zero⟩
  · rw [direction_apply, positiveRoot_eval]
    norm_num
  · intro β hβ γ hγ heq
    have hh := congrArg (fun α : Module.Dual ℂ diagonalCartan => α diagonalGenerator) heq
    norm_num [positiveRoot_eval, positive_eval hβ, positive_eval hγ] at hh

theorem complexInduced : complexInducedType := by
  let := diagonal_isCartan
  have hχ : IsWeightCharacter diagonalCartan standardDirection 0 trivialCharacter := by
    constructor <;> intro x <;> simp [trivialCharacter, augmentation]
  refine ⟨diagonal_isCartan, direction_regular, hχ, ?_⟩
  let := (sl2Coordinates ℂ).symm.finiteDimensional
  let e : simple diagonalCartan standardDirection → Model ℂ := fun _ => E ℂ
  have he (i : simple diagonalCartan standardDirection) :
      e i ∈ rootSpace_value diagonalCartan i.val ∧ e i ≠ 0 := by
    have hi : i.val = positiveRoot :=
      diagonal_dual_ext ((positive_eval i.property.1).trans positiveRoot_eval.symm)
    rw [hi]
    exact ⟨e_in_positiveRoot, e_ne_zero⟩
  have heq : definingIdeal_value diagonalCartan standardDirection 0 e = definingIdeal ℂ := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ (⟨y,rfl⟩ | ⟨i,rfl⟩)
      · obtain ⟨a, ha⟩ := diagonal_member y
        simp only [LinearMap.zero_apply, map_zero, sub_zero, ← ha, map_smul]
        exact ((definingIdeal ℂ).restrictScalars ℂ).smul_mem a (cartan_mem_ideal ℂ)
      · exact raising_mem_ideal ℂ
    · apply Submodule.span_le.mpr
      intro x hx
      rcases (show x = cartanGenerator ℂ ∨ x = raising ℂ by simpa using hx) with rfl | rfl
      · apply Submodule.subset_span
        left
        exact ⟨diagonalGenerator, by simp⟩
      · apply Submodule.subset_span
        right
        exact ⟨⟨positiveRoot, positiveRoot_simple⟩, rfl⟩
  have hpres := VermaModules.induced_presentation (sl2_semisimple ℂ) diagonalCartan
    standardDirection direction_regular 0 trivialCharacter hχ e he
  rw [heq] at hpres
  exact hpres

end ComplexComparison

end LieAlgebrasAndRepresentations.InfiniteDimensionalBoundary
