import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.SerreKoszulEulerFormula
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.StaggeredKoszulFiltration
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.CoefficientExactness
import Mathlib.RingTheory.Length
import Mathlib.Data.Nat.Choose.Sum

open CategoryTheory CategoryTheory.Limits AdvCommAlg.Koszul
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open P103.HilbertSamuelPolynomial (quotientLength)
open P103.HilbertSamuelDimension (backwardDifference backwardDifference_degree
  backwardDifference_coeff)
open Specs.CommutativeAlgebraNotes.Intersection.SerreKoszulEulerFormula

namespace CommutativeAlgebraNotes.Intersection.SerreKoszulEulerFormula

open DegreeMultiplicity
open scoped BigOperators

noncomputable section

universe u v

theorem dimensionBound : dimensionBoundType.{u,v} := by
  intro A _ _ _ E _ _ _ z hJ hE hnonzero
  let := hnonzero
  obtain ⟨d, hd, _, hbound⟩ := P103.Ch06.SystemsParameters.parameter_count A E
  have hspan : Ideal.span (Set.range z.get) = listIdeal z := by
    congr 1
    ext a
    exact List.mem_iff_get.symm
  have hdz := hbound z.length z.get
    (fun i => hJ (Ideal.subset_span (List.get_mem z i)))
    (hspan.symm ▸ hE)
  rw [hd]
  exact_mod_cast hdz

private theorem finiteLength_homology {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat.{v} A) ℕ) (i : ℕ) (hi : IsFiniteLength A (K.X i)) :
    IsFiniteLength A (K.homology i) := by
  have hcycles := hi.of_injective
    ((ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance)
  exact hcycles.of_surjective
    ((ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance)

theorem homologyFiniteLength : homologyFiniteLengthType.{u,v} := by
  intro A _ _ _ E _ _ _ z hJ hE i
  obtain ⟨N, hN⟩ := StaggeredKoszul.eventual_acyclic E z
  obtain ⟨hn, h⟩ := hN N le_rfl
  let hstab := StaggeredKoszul.differential_stable E z N
  have := (h hstab).2
  let e := asIso (HomologicalComplex.homologyMap (StaggeredKoszul.projection hstab) i)
  have hl := StaggeredKoszul.quotient_finite_length E z hJ hE N hn hstab i
  exact (finiteLength_homology _ i hl).of_injective e.toLinearEquiv.injective

theorem positiveInteger : positiveIntegerType.{u,v} := by
  intro A _ _ _ E _ _ _ z hJ hE hnonzero hd
  let := hnonzero
  have hpos := hilbertSamuelMultiplicityPositive A E (listIdeal z) hJ hE
  rw [hilbertSamuelMultiplicityAtDimension A E (listIdeal z) z.length hd] at hpos
  obtain ⟨n, hn⟩ := degreeMultiplicityIntegral A E (listIdeal z) hJ hE z.length hd.le
  rw [hn] at hpos
  exact ⟨n, by exact_mod_cast hpos, hn⟩

theorem zeroOfDimensionLT : zeroOfDimensionLTType.{u,v} := by
  intro A _ _ _ E _ _ _ z hJ hE
  exact degreeMultiplicityZeroOfDimensionLT A E (listIdeal z) hJ hE z.length

private def intLength {A : Type u} [CommRing A] (M : ModuleCat.{v} A) : ℤ :=
  (Module.length A M).toNat

private def imageLength {A : Type u} [CommRing A] {X Y : ModuleCat.{v} A} (f : X ⟶ Y) : ℤ :=
  (Module.length A (LinearMap.range f.hom)).toNat

private theorem intLength_exact {A : Type u} [CommRing A] {X Y Z : ModuleCat.{v} A}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hfg : LinearMap.range f.hom = LinearMap.ker g.hom)
    (hY : IsFiniteLength A Y) : intLength Y = imageLength f + imageLength g := by
  have h₁ := hY.of_injective (LinearMap.range f.hom).injective_subtype
  have h₂ := hY.of_surjective g.hom.surjective_rangeRestrict
  have h := Module.length_eq_add_of_exact (LinearMap.range f.hom).subtype g.hom.rangeRestrict
    (LinearMap.range f.hom).injective_subtype g.hom.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict, hfg]))
  unfold intLength imageLength
  rw [h, ENat.toNat_add (Module.length_ne_top_iff.mpr h₁) (Module.length_ne_top_iff.mpr h₂),
    Nat.cast_add]

private theorem imageLength_zero {A : Type u} [CommRing A] {X Y : ModuleCat.{v} A} :
    imageLength (0 : X ⟶ Y) = 0 := by
  rw [imageLength, ModuleCat.hom_zero, LinearMap.range_zero, Module.length_bot]
  rfl

private theorem alternating_sum_adjacent (b : ℕ → ℤ) (r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), (-1 : ℤ)^i * (b i + b (i + 1)) =
      b 0 + (-1 : ℤ)^r * b (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

private theorem imageLength_of_mono {A : Type u} [CommRing A]
    {X Y : ModuleCat.{v} A} (f : X ⟶ Y) [Mono f] : imageLength f = intLength X := by
  unfold imageLength intLength
  rw [← (LinearEquiv.ofInjective f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)).length_eq]

private theorem imageLength_of_epi {A : Type u} [CommRing A]
    {X Y : ModuleCat.{v} A} (f : X ⟶ Y) [Epi f] : imageLength f = intLength Y := by
  unfold imageLength intLength
  rw [LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective f).mp inferInstance),
    Module.length_top]

private theorem imageLength_comp_mono {A : Type u} [CommRing A]
    {X Y Z : ModuleCat.{v} A} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    imageLength (f ≫ g) = imageLength f := by
  have hg : LinearMap.ker g.hom = ⊥ :=
    LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective g).mp inferInstance)
  unfold imageLength
  rw [← ((f ≫ g).hom.quotKerEquivRange).length_eq, ← f.hom.quotKerEquivRange.length_eq]
  rw [ModuleCat.hom_comp, LinearMap.ker_comp_of_ker_eq_bot _ hg]

/-- For a complex term, its length minus the length of its homology is the
sum of the incoming and outgoing image lengths. -/
private theorem intLength_term_sub_homology {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (h : IsFiniteLength A S.X₂) :
    intLength S.X₂ - intLength S.homology = imageLength S.f + imageLength S.g := by
  let T := ShortComplex.mk S.iCycles S.g S.iCycles_g
  let U := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hT : T.Exact := T.exact_of_f_is_kernel S.cyclesIsKernel
  have hU : U.Exact := U.exact_of_g_is_cokernel S.homologyIsCokernel
  have hcycles := h.of_injective ((ModuleCat.mono_iff_injective S.iCycles).mp inferInstance)
  have ht := intLength_exact (ShortComplex.moduleCat_exact_iff_range_eq_ker T |>.mp hT) h
  have hu := intLength_exact (ShortComplex.moduleCat_exact_iff_range_eq_ker U |>.mp hU) hcycles
  change intLength S.X₂ = imageLength S.iCycles + imageLength S.g at ht
  change intLength S.cycles = imageLength S.toCycles + imageLength S.homologyπ at hu
  have hcomp := imageLength_comp_mono S.toCycles S.iCycles
  rw [S.toCycles_i] at hcomp
  rw [imageLength_of_mono S.iCycles, hu, ← hcomp, imageLength_of_epi S.homologyπ] at ht
  omega

private theorem intLength_alternating_eq_homology {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat.{v} A) ℕ) (r : ℕ)
    (hf : ∀ i, IsFiniteLength A (K.X i)) (hbound : IsZero (K.X (r + 1))) :
    (∑ i ∈ Finset.range (r + 1), (-1 : ℤ)^i * intLength (K.X i)) =
      ∑ i ∈ Finset.range (r + 1), (-1 : ℤ)^i * intLength (K.homology i) := by
  let b (i : ℕ) := imageLength (K.d i (i - 1))
  have h₀ : b 0 = 0 := by
    change imageLength (K.d 0 0) = 0
    rw [K.shape 0 0 (by simp [ComplexShape.down_Rel]), imageLength_zero]
  have hr : b (r + 1) = 0 := by
    unfold b
    rw [hbound.eq_of_src (K.d (r + 1) (r + 1 - 1)) 0, imageLength_zero]
  have hterm (i : ℕ) : intLength (K.X i) - intLength (K.homology i) = b i + b (i + 1) := by
    have hprev : (ComplexShape.down ℕ).prev i = i + 1 :=
      ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)
    have hnext : (ComplexShape.down ℕ).next i = i - 1 := by
      cases i with
      | zero => exact ComplexShape.next_eq_self' _ _ (by simp [ComplexShape.down_Rel])
      | succ i => exact ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)
    have h := intLength_term_sub_homology (K.sc i) (hf i)
    change intLength (K.X i) - intLength (K.homology i) =
      imageLength (K.d ((ComplexShape.down ℕ).prev i) i) +
      imageLength (K.d i ((ComplexShape.down ℕ).next i)) at h
    rw [hprev, hnext, add_comm] at h
    exact h
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub, hterm, alternating_sum_adjacent, h₀, hr, mul_zero, add_zero]

/-- Expand the iterated difference by applying the binomial theorem to the
identity and the negative of the translation endomorphism. -/
private theorem eval_iterate_backwardDifference (r : ℕ) (p : Polynomial ℚ) (x : ℚ) :
    ((backwardDifference^[r]) p).eval x =
      ∑ i ∈ Finset.range (r + 1), (-1 : ℚ)^i * (r.choose i : ℚ) * p.eval (x - i) := by
  let t : Module.End ℚ (Polynomial ℚ) := Polynomial.taylor (-1)
  let D : Module.End ℚ (Polynomial ℚ) := 1 + -t
  have hD (q : Polynomial ℚ) : D q = backwardDifference q := by
    change q + -(Polynomial.taylor (-1) q) = _
    rw [backwardDifference, sub_eq_add_neg]
  have hpow (n : ℕ) : (D^n) p = (backwardDifference^[n]) p := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hD, Function.iterate_succ_apply']
  have ht (n : ℕ) (y : ℚ) : ((t^n) p).eval y = p.eval (y - n) := by
    induction n generalizing y with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change (Polynomial.taylor (-1) ((t ^ n) p)).eval y = _
      simp only [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C]
      rw [ih, Nat.cast_succ]
      congr 1
      ring
  rw [← hpow, show D = -t + 1 by exact add_comm _ _,
    (Commute.one_right (-t)).add_pow, LinearMap.sum_apply, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_pow, mul_one, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
  change Polynomial.evalRingHom x (r.choose i • ((-t)^i) p) = _
  rw [map_nsmul, nsmul_eq_mul]
  have hneg : (-t)^i = ((-1 : ℚ)^i) • t^i := by
    rw [← smul_pow, neg_one_smul]
  rw [hneg, LinearMap.smul_apply]
  change (r.choose i : ℚ) * (Polynomial.eval x (((-1 : ℚ)^i) • (t^i) p)) = _
  rw [Polynomial.eval_smul, ht, smul_eq_mul]
  ring

private theorem iterate_backwardDifference_top (r : ℕ) (p : Polynomial ℚ)
    (h : p.natDegree ≤ r) (x : ℚ) :
    ((backwardDifference^[r]) p).eval x = (r.factorial : ℚ) * p.coeff r := by
  induction r generalizing p with
  | zero =>
    rw [Function.iterate_zero_apply, Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)]
    simp
  | succ r ih =>
    rw [Function.iterate_succ_apply]
    by_cases hp : p.natDegree = 0
    · have hd : backwardDifference p = 0 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hp, backwardDifference, Polynomial.taylor_C, sub_self]
      rw [hd, ih 0 (by simp), Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega)]
      simp
    · have hpos : 0 < p.natDegree := Nat.pos_of_ne_zero hp
      have hd := (backwardDifference_degree p hpos).2
      rw [ih _ (by omega)]
      by_cases heq : p.natDegree = r + 1
      · have hc := backwardDifference_coeff p hpos
        rw [← Polynomial.coeff_natDegree, heq, Nat.add_sub_cancel] at hc
        rw [hc, Nat.factorial_succ, Nat.cast_mul]
        ring
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := backwardDifference p) (by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega)]
        simp

theorem serreKoszulEulerFormula : serreKoszulEulerFormulaType.{u,v} := by
  intro A _ _ _ E _ _ _ z hJ hE
  let J := listIdeal z
  let r := z.length
  let p := hilbertSamuelPolynomial J E
  have hp : p.natDegree ≤ r := by
    rcases subsingleton_or_nontrivial E with hs | hn
    · simp [p, hilbertSamuelPolynomialZero A E J]
    · have hd := dimensionBound A E z hJ hE hn
      rw [(hilbertSamuelPolynomialDegree A E J hJ hE).2] at hd
      exact_mod_cast hd
  obtain ⟨N, hN⟩ := StaggeredKoszul.eventual_acyclic E z
  obtain ⟨T, hT⟩ := hilbertSamuelPolynomialEventually A E J hJ hE
  let n := max N (T + r + 1)
  have hn : r < n ∧ ∀ h : StaggeredKoszul.DifferentialStable E z n,
      (StaggeredKoszul.filtration h).Acyclic ∧ QuasiIso (StaggeredKoszul.projection h) :=
    hN n (le_max_left _ _)
  have hlarge : T + r + 1 ≤ n := le_max_right _ _
  let hs := StaggeredKoszul.differential_stable E z n
  have := (hn.2 hs).2
  let Q := StaggeredKoszul.quotient hs
  let K := coefficientComplex E z
  have hfinite := StaggeredKoszul.quotient_finite_length E z hJ hE n hn.1 hs
  have hbound : IsZero (Q.X (r + 1)) := by
    let := coefficientComplex_vanish E z (r + 1) (by omega)
    exact ModuleCat.isZero_iff_subsingleton.mpr (inferInstanceAs
      (Subsingleton (K.X (r + 1) ⧸ StaggeredKoszul.layer E z n (r + 1))))
  have hhom (i : ℕ) : intLength (K.homology i) = intLength (Q.homology i) := by
    let e := asIso (HomologicalComplex.homologyMap (StaggeredKoszul.projection hs) i)
    unfold intLength
    rw [e.toLinearEquiv.length_eq]
  change ((∑ i ∈ Finset.range (r + 1), (-1 : ℤ)^i * intLength (K.homology i) : ℤ) : ℚ) =
    (r.factorial : ℚ) * p.coeff r
  simp only [hhom]
  rw [← intLength_alternating_eq_homology Q r hfinite hbound,
    ← iterate_backwardDifference_top r p hp ((n - 1 : ℕ) : ℚ), eval_iterate_backwardDifference]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hir : i ≤ r := by simpa using (Finset.mem_range.mp hi)
  have hidx : T ≤ n - i - 1 := by omega
  obtain ⟨e⟩ := StaggeredKoszul.quotient_term E z n hs i
  have he : Module.length A (Q.X i) =
      (↑(r.choose i) : ℕ∞) * Module.length A (E ⧸ (J^(n - i) • (⊤ : Submodule A E))) := by
    rw [e.length_eq, Module.length_pi]
    simp [r, J]
  have hcast : ((n - i - 1 : ℕ) : ℚ) = ((n - 1 : ℕ) : ℚ) - i := by
    rw [show n - i - 1 = n - 1 - i by omega, Nat.cast_sub (by omega : i ≤ n - 1)]
  have hval := hT (n - i - 1) hidx
  change (quotientLength J E (n - i - 1) : ℚ) = p.eval _ at hval
  rw [hcast] at hval
  have hlen : (intLength (Q.X i) : ℚ) = (r.choose i : ℚ) * (quotientLength J E (n - i - 1) : ℚ) := by
    unfold intLength
    rw [he, ENat.toNat_mul, ENat.toNat_natCast]
    push_cast
    congr 1
    unfold quotientLength P103.HilbertSamuelPolynomial.Quotient
    rw [show n - i - 1 + 1 = n - i by omega]
    rfl
  rw [hlen, hval]
  ring

/-- In the long exact sequence, the connecting images telescope after
subtracting the middle homology lengths from the two outer lengths. -/
private theorem alternating_homology_additive {A : Type u} [CommRing A]
    (S : ShortComplex (ChainComplex (ModuleCat.{v} A) ℕ)) (hS : S.ShortExact) (r : ℕ)
    (hl : ∀ i, IsFiniteLength A (S.X₁.homology i))
    (hm : ∀ i, IsFiniteLength A (S.X₂.homology i))
    (hn : ∀ i, IsFiniteLength A (S.X₃.homology i))
    (hr : IsZero (S.X₃.homology (r + 1))) :
    (∑ i ∈ Finset.range (r + 1), (-1 : ℤ)^i * intLength (S.X₂.homology i)) =
      (∑ i ∈ Finset.range (r + 1), (-1 : ℤ)^i * intLength (S.X₁.homology i)) +
      (∑ i ∈ Finset.range (r + 1), (-1 : ℤ)^i * intLength (S.X₃.homology i)) := by
  let f := HomologicalComplex.homologyMap S.f
  let g := HomologicalComplex.homologyMap S.g
  let δ (i : ℕ) := hS.δ (i + 1) i (by rfl)
  let b : ℕ → ℤ
    | 0 => 0
    | i + 1 => imageLength (δ i)
  have hend : b (r + 1) = 0 := by
    change imageLength (δ r) = 0
    rw [hr.eq_of_src (δ r) 0, imageLength_zero]
  have hleft (i : ℕ) : intLength (S.X₁.homology i) = b (i + 1) + imageLength (f i) :=
    intLength_exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _ |>.mp
      (hS.homology_exact₁ (i + 1) i rfl)) (hl i)
  have hmiddle (i : ℕ) : intLength (S.X₂.homology i) = imageLength (f i) + imageLength (g i) :=
    intLength_exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _ |>.mp
      (hS.homology_exact₂ i)) (hm i)
  have hright (i : ℕ) : intLength (S.X₃.homology i) = imageLength (g i) + b i := by
    cases i with
    | zero =>
      have := hS.epi_g
      have : Epi (g 0) := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0
        (by simp [ComplexShape.down_Rel])
      change _ = imageLength (g 0) + 0
      rw [imageLength_of_epi, add_zero]
    | succ i =>
      exact intLength_exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _ |>.mp
        (hS.homology_exact₃ (i + 1) i rfl)) (hn (i + 1))
  have hterm (i : ℕ) : intLength (S.X₁.homology i) + intLength (S.X₃.homology i) -
      intLength (S.X₂.homology i) = b i + b (i + 1) := by
    rw [hleft, hright, hmiddle]
    ring
  symm
  apply sub_eq_zero.mp
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  simp only [← mul_add, ← mul_sub, hterm, alternating_sum_adjacent, hend, mul_zero, add_zero]
  rfl

theorem additivity : additivityType.{u,v} := by
  intro A _ _ _ z S _ _ _ hS hJ h₁ h₂ h₃
  rw [← serreKoszulEulerFormula A S.X₁ z hJ h₁, ← serreKoszulEulerFormula A S.X₂ z hJ h₂,
    ← serreKoszulEulerFormula A S.X₃ z hJ h₃, ← Int.cast_add]
  congr 1
  let C := S.map (CoefficientSequences.coefficientChainFunctor z)
  have hC : C.ShortExact := chainCoefficient_shortExact z S hS
  have hlast : IsZero (C.X₃.homology (z.length + 1)) := by
    let := coefficientComplex_vanish S.X₃ z (z.length + 1) (Nat.lt_succ_self _)
    apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (inferInstanceAs (Subsingleton ((coefficientComplex S.X₃ z).X (z.length + 1))))
  exact alternating_homology_additive C hC z.length
    (homologyFiniteLength A S.X₁ z hJ h₁) (homologyFiniteLength A S.X₂ z hJ h₂)
    (homologyFiniteLength A S.X₃ z hJ h₃) hlast

end
end CommutativeAlgebraNotes.Intersection.SerreKoszulEulerFormula
