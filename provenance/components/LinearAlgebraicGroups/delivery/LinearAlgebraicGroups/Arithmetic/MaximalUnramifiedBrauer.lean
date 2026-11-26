import Specs.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
import LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.GaloisSplitting
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Equivalence
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Nakayama
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.FieldTheory.Finite.GaloisField
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer

open ValuativeRel
open scoped TensorProduct WithZero NNReal

open private extendMatrixSplitting from
  MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.GaloisSplitting
universe u v w

/-- The field in the cyclic presentation is unramified for the extended
valuation and splits the division algebra. -/
private theorem division_has_unramified_splitting
    {K : Type v} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : Type w} [DivisionRing D] [Algebra K D]
    (hD : RM03.CSA.IsCentralDivision K D) :
    ∃ (L : Type w) (_ : Field L) (_ : Algebra K L),
      IsUnramified K L ∧ RM03.CSA.Splits K L D := by
  have hDS : RM03.CSA.IsCentralSimple K D := RM03.CSA.isCentralSimple_of_isCentralDivision K D hD
  obtain ⟨s, hs, -⟩ := LocalDivisionAlgebras.valuation_exists hDS
  obtain ⟨residue⟩ := LocalDivisionAlgebras.residue_field hDS s hs
  obtain ⟨_, _, ⟨c⟩⟩ := LocalDivisionAlgebras.cyclic_structure hDS s hs residue
  let : Field c.L := c.fieldL
  let : Algebra K c.L := c.algebraL
  let : IsGalois K c.L := c.galois
  let n := RM03.CSA.degree K D
  have hn : 0 < n := RM03.CSA.degree_pos hDS
  have : FiniteDimensional K c.L := Module.finite_of_finrank_pos (c.degree ▸ hn)
  let t := ValuativeRel.ofValuation c.vL
  have ht : @ValuativeExtension K c.L _ _ _ t _ := by
    let : ValuativeRel c.L := t
    let : c.vL.Compatible := Valuation.Compatible.ofValuation c.vL
    constructor
    intro a b
    rw [(valuation K).vle_iff_le, c.vL.vle_iff_le, c.base_value, c.base_value]
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.le_iff_le
  obtain ⟨r, T, hext, hlocal, _, _, huniq⟩ := finiteExtension_localField (K := K) (L := c.L)
  have htr : t = r := huniq t ht
  have hsurj : Function.Surjective (fun a : K => @valuation c.L _ r (algebraMap K c.L a)) := by
    subst r
    let : ValuativeRel c.L := t
    let : c.vL.Compatible := Valuation.Compatible.ofValuation c.vL
    intro γ
    obtain ⟨x, hx⟩ := valuation_surjective γ
    obtain ⟨y, hy⟩ := (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective (c.vL x)
    obtain ⟨a, rfl⟩ := valuation_surjective y
    refine ⟨a, ?_⟩
    refine Eq.trans ?_ hx
    exact ((valuation c.L).veq_iff_eq).mp (c.vL.veq_iff_eq.mpr ((c.base_value a).trans hy))
  exact ⟨c.L, inferInstance, inferInstance,
    ⟨inferInstance, inferInstance, r, T, hlocal, hext, hsurj⟩,
    n, hn, RM03.CSA.subfield_splits c.embed hD c.degree⟩

section Descent

variable {M : Type v} [Field M] {D : Type w} [DivisionRing D] [Algebra M D]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vectors whose coordinates belong to the field of definition form a
subalgebra when the multiplication table and the unit descend. -/
private def coordinateAlgebra {F : Type u} [Field F] [Algebra F M]
    (E : IntermediateField F M) (b : Module.Basis ι M D)
    (hOne : ∀ k, b.equivFun 1 k ∈ E) (hMul : ∀ i j k, b.equivFun (b i * b j) k ∈ E) :
    Subalgebra E D where
  carrier := {x | ∀ i, b.equivFun x i ∈ E}
  zero_mem' i := by simp
  add_mem' hx hy i := by simpa only [map_add, Pi.add_apply] using E.add_mem (hx i) (hy i)
  one_mem' := hOne
  mul_mem' {x y} hx hy k := by
    have he : x * y = ∑ i, ∑ j, (b.equivFun x i * b.equivFun y j) • (b i * b j) := by
      conv_lhs =>
        rw [← b.sum_equivFun x, ← b.sum_equivFun y]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm (b.equivFun y _) (b.equivFun x _)]
    rw [he]
    simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    exact E.sum_mem fun i _ => E.sum_mem fun j _ => E.mul_mem (E.mul_mem (hx i) (hy j)) (hMul i j k)
  algebraMap_mem' a i := by
    rw [IsScalarTower.algebraMap_apply E M D, Algebra.algebraMap_eq_smul_one]
    change b.equivFun ((a : M) • (1 : D)) i ∈ E
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact E.mul_mem a.property (hOne i)

private theorem basis_mem_coordinateAlgebra {F : Type u} [Field F] [Algebra F M]
    (E : IntermediateField F M) (b : Module.Basis ι M D) (hOne hMul) (i : ι) :
    b i ∈ coordinateAlgebra E b hOne hMul := by
  intro j
  rw [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_apply]
  split <;> simp

/-- Descend a central division algebra to a finite subfield by keeping its
multiplication table and the coordinates of its unit. -/
private theorem descend_division {F : Type u} [Field F] [Algebra F M] [Algebra.IsAlgebraic F M]
    (hD : RM03.CSA.IsCentralDivision M D) :
    ∃ (E : IntermediateField F M), FiniteDimensional F E ∧
      ∃ (D₀ : Type w) (_ : DivisionRing D₀) (_ : Algebra E D₀),
        RM03.CSA.IsCentralDivision E D₀ ∧ Nonempty (RM03.CSA.BaseChange E M D₀ ≃ₐ[M] D) := by
  classical
  let _ := hD.2
  let b := Module.finBasis M D
  let s : Set M := Set.range (b.equivFun 1) ∪
    Set.range (fun t : Fin (Module.finrank M D) × Fin (Module.finrank M D) × Fin (Module.finrank M D) =>
      b.equivFun (b t.1 * b t.2.1) t.2.2)
  let E := IntermediateField.adjoin F s
  have hfin : FiniteDimensional F E := by
    let _ : Finite s := (Set.finite_range _ |>.union (Set.finite_range _)).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let S := coordinateAlgebra E b
    (fun i => IntermediateField.subset_adjoin F s (Or.inl ⟨i, rfl⟩))
    (fun i j k => IntermediateField.subset_adjoin F s (Or.inr ⟨(i, j, k), rfl⟩))
  let c : Fin (Module.finrank M D) → S :=
    fun i => ⟨b i, basis_mem_coordinateAlgebra _ _ _ _ _⟩
  have hcLI : LinearIndependent E c :=
    ((b.linearIndependent.restrict_scalars' E).of_comp (Subalgebra.val S).toLinearMap)
  have hcSpan : ⊤ ≤ Submodule.span E (Set.range c) := by
    intro x _
    have hcoord : ∀ i, b.equivFun (x : D) i ∈ E := x.property
    let a (i : Fin (Module.finrank M D)) : E := ⟨b.equivFun (x : D) i, hcoord i⟩
    have hsum : (∑ i, a i • c i) = x := by
      apply Subtype.ext
      change S.val (∑ i, a i • c i) = x
      rw [map_sum]
      simp only [map_smul, Subalgebra.val_apply, c]
      change (∑ i, (b.equivFun (x : D) i : M) • b i) = x
      exact b.sum_equivFun (x : D)
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b₀ := Module.Basis.mk hcLI hcSpan
  have hsFinite : FiniteDimensional E S := Module.Finite.of_basis b₀
  let dS : DivisionRing S := divisionRingOfFiniteDimensional E S
  let hcomm (a : M) (x : S) : Commute ((Algebra.ofId M D) a) (S.val x) :=
    Algebra.commutes a _
  let f : M ⊗[E] S →ₐ[M] D := Algebra.TensorProduct.lift (Algebra.ofId M D) S.val hcomm
  have hbasis : f ∘ (b₀.baseChange M) = b := by
    funext i
    rw [Function.comp_apply, Module.Basis.baseChange_apply]
    rw [show f (1 ⊗ₜ[E] b₀ i) = (Algebra.ofId M D) 1 * S.val (b₀ i) from
      Algebra.TensorProduct.lift_tmul (Algebra.ofId M D) S.val hcomm 1 (b₀ i)]
    have : b₀ i = c i := Module.Basis.mk_apply _ _ _
    rw [this, map_one, one_mul]
    rfl
  have hf : Function.Bijective f :=
    f.toLinearMap.bijective_of_linearIndependent_of_span_eq_top
      (b₀.baseChange M).span_eq (by simpa only [AlgHom.coe_toLinearMap, hbasis] using b.linearIndependent)
      (by simpa only [AlgHom.coe_toLinearMap, hbasis] using b.span_eq)
  have hc : Algebra.IsCentral E S := by
    constructor
    intro x hx
    have hcomm : (x : D) ∈ Subalgebra.center M D := by
      rw [Subalgebra.mem_center_iff]
      intro y
      rw [← b.sum_equivFun y, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_mul_assoc, mul_smul_comm]
      congr 1
      exact congrArg Subtype.val ((Subalgebra.mem_center_iff.mp hx) (c i))
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (hD.1.out hcomm)
    have hnonzero : ∃ i, b.equivFun 1 i ≠ 0 := by
      by_contra! h
      exact one_ne_zero (b.equivFun.injective (funext fun i => by simp [h i]))
    obtain ⟨i, hi⟩ := hnonzero
    have hunit : b.equivFun 1 i ∈ E := S.one_mem (i := i)
    have hxi : b.equivFun (x : D) i ∈ E := x.property i
    have hcoeff : b.equivFun (x : D) i = a * b.equivFun 1 i := by
      rw [← ha, Algebra.algebraMap_eq_smul_one, map_smul]
      rfl
    rw [hcoeff] at hxi
    have hamem : a ∈ E := by
      simpa only [mul_div_cancel_right₀ _ hi] using E.div_mem hxi hunit
    exact Algebra.mem_bot.mpr ⟨⟨a, hamem⟩, Subtype.ext ha⟩
  exact ⟨E, hfin, S, dS, inferInstance, ⟨hc, hsFinite⟩, ⟨AlgEquiv.ofBijective f hf⟩⟩

end Descent

section Roots

open IsLocalRing Polynomial

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {L : Type v} [Field L] [Algebra F L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension F L]

local notation "O" K => Valuation.integer (valuation K)
local notation "κ" K => ResidueField (O K)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
private theorem valuation_hasExtension :
    (valuation F).HasExtension (valuation L) := by
  constructor
  intro a b
  change valuation F a ≤ valuation F b ↔
    valuation L (algebraMap F L a) ≤ valuation L (algebraMap F L b)
  rw [← (valuation L).vle_iff_le, ← (valuation F).vle_iff_le]
  exact (ValuativeExtension.vle_iff_vle a b).symm

/-- The residue fields in a local-field extension have the same characteristic. -/
private lemma residue_natCast_ne_zero_iff (n : ℕ) : (n : κ F) ≠ 0 ↔ (n : κ L) ≠ 0 := by
  have : (valuation F).HasExtension (valuation L) := valuation_hasExtension
  let φ := ResidueField.map (algebraMap (O F) (O L))
  simpa only [map_natCast, map_ne_zero_iff] using
    (map_ne_zero_iff φ φ.injective (x := (n : κ F))).symm

/-- Lift a residue element to a root of `X^q-X`, where `q` is the size of
the residue field. A nonzero lift is a root of unity of order dividing `q-1`. -/
private theorem lift_residue_root (a : κ L) :
    ∃ x : O L, residue _ x = a ∧
      ((x : L) = 0 ∨ (x : L) ^ (Nat.card (κ L) - 1) = 1) := by
  classical
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  let : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let : Fintype (κ L) := Fintype.ofFinite _
  let q := Fintype.card (κ L)
  have hq : 1 < q := Fintype.one_lt_card
  let P : (O L)[X] := X ^ q - X
  have hmonic : P.Monic :=
    (monic_X_pow q).sub_of_left (by simpa using hq)
  obtain ⟨a₀, ha₀⟩ := residue_surjective a
  have heval : P.eval a₀ ∈ maximalIdeal (O L) := by
    rw [← residue_eq_zero_iff]
    simp [P, FiniteField.pow_card, q]
  have hderivative : IsUnit (Ideal.Quotient.mk (maximalIdeal (O L)) (P.derivative.eval a₀)) := by
    change IsUnit (residue (O L) (P.derivative.eval a₀))
    simp [P, derivative_X_pow, q, Nat.cast_card_eq_zero (κ L)]
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian P hmonic a₀ heval hderivative
  refine ⟨x, ?_, ?_⟩
  · rw [← ha₀, ← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).2 hxa
  · by_cases hzero : (x : L) = 0
    · exact Or.inl hzero
    right
    have hh : (x : L) ^ q = (x : L) := by
      have hh' : x ^ q = x := by
        simpa only [P, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero] using hx
      exact_mod_cast hh'
    rw [show q = (q - 1) + 1 by omega, pow_succ] at hh
    simpa only [Nat.card_eq_fintype_card, q] using
      mul_right_cancel₀ hzero (hh.trans (one_mul (x : L)).symm)

private lemma residue_card_sub_one_cast_ne_zero :
    ((Nat.card (κ L) - 1 : ℕ) : κ L) ≠ 0 := by
  classical
  let : Fintype (κ L) := Fintype.ofFinite _
  have hq : 1 ≤ Fintype.card (κ L) := Fintype.card_pos
  rw [Nat.card_eq_fintype_card, Nat.cast_sub hq, Nat.cast_card_eq_zero]
  simp

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The valuation integers of a finite local extension are the integral
closure of the base valuation integers. -/
private theorem valuation_isIntegralClosure [FiniteDimensional F L]
    [h : (valuation F).HasExtension (valuation L)] :
    IsIntegralClosure (O L) (O F) L := by
  let v := valuation F
  let rL := ‹ValuativeRel L›
  have hextL : @ValuativeExtension F L _ _ _ rL _ := inferInstance
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  let hv := (inferInstance : IsRankLeOne F).nonempty.some
  let : (Valued.v (R := F)).RankOne :=
    { hom' := hv.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := hv.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  let : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField F L
  let : NormedAlgebra F L := spectralNorm.normedAlgebra F L
  let : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (isNonarchimedean_spectralNorm (K := F) (L := L))
  let w₀ : Valuation L ℝ≥0 := NormedField.valuation
  let s : ValuativeRel L := ValuativeRel.ofValuation w₀
  have hs : @ValuativeExtension F L _ _ _ s _ := by
    let : ValuativeRel L := s
    let : w₀.Compatible := Valuation.Compatible.ofValuation w₀
    constructor
    intro x y
    rw [w₀.vle_iff_le, v.vle_iff_le]
    change ‖algebraMap F L x‖₊ ≤ ‖algebraMap F L y‖₊ ↔ _
    rw [← NNReal.coe_le_coe]
    change spectralNorm F L (algebraMap F L x) ≤ spectralNorm F L (algebraMap F L y) ↔ _
    rw [spectralNorm_extends, spectralNorm_extends]
    exact Valued.toNormedField.norm_le_iff
  have hs_eq : s = rL := by
    obtain ⟨r, _, _, _, _, _, huniq⟩ := finiteExtension_localField (K := F) (L := L)
    exact (huniq s hs).trans (huniq rL hextL).symm
  let : ValuativeRel L := rL
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  constructor
  · intro hx
    have hx' : IsIntegral (O L) x := hx.tower_top (A := O L)
    exact ⟨⟨x, (Valuation.integer.integers (valuation L)).mem_of_integral hx'⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hy : valuation L (y : L) ≤ 1 := y.property
    have hy' : w₀ (y : L) ≤ 1 := by
      have hcomp : w₀.Compatible :=
        (congrArg (fun t : ValuativeRel L => @Valuation.Compatible L ℝ≥0 _ _ w₀ t) hs_eq) ▸
          Valuation.Compatible.ofValuation w₀
      exact w₀.vle_one_iff.mp ((valuation L).vle_one_iff.mpr hy)
    have hnorm : spectralNorm F L (y : L) ≤ 1 := by
      change ‖(y : L)‖₊ ≤ 1 at hy'
      exact_mod_cast hy'
    have hm := minpoly.monic (Algebra.IsIntegral.isIntegral (R := F) (y : L))
    have hcoeff := (spectralValue_le_one_iff hm).mp hnorm
    have hcoeff' (i : ℕ) : (minpoly F (y : L)).coeff i ∈ (algebraMap (O F) F).range := by
      exact ⟨⟨_, Valued.toNormedField.norm_le_one_iff.mp (hcoeff i)⟩, rfl⟩
    obtain ⟨p, hp⟩ := (Polynomial.mem_map_range (algebraMap (O F) F)).2 hcoeff'
    change p.map (algebraMap (O F) F) = minpoly F (y : L) at hp
    refine ⟨p, (IsFractionRing.injective (O F) F).monic_map_iff.mpr (hp ▸ hm), ?_⟩
    change aeval (y : L) p = 0
    rw [aeval_eq_aeval_map (IsScalarTower.algebraMap_eq (O F) F L).symm, hp]
    exact minpoly.aeval F (y : L)


omit [ValuativeExtension F L] in
private theorem map_maximalIdeal_of_surjective [h : (valuation F).HasExtension (valuation L)]
    (hsurj : Function.Surjective (fun x : F => valuation L (algebraMap F L x))) :
    (maximalIdeal (O F)).map (algebraMap (O F) (O L)) = maximalIdeal (O L) := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    exact (Valuation.HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal (valuation F) (valuation L)).ge
  · intro y hy
    have hy' : valuation L (y : L) < 1 := Valuation.mem_maximalIdeal_iff (v := valuation L) |>.mp hy
    by_cases hy0 : y = 0
    · simp [hy0]
    obtain ⟨a, ha⟩ := hsurj (valuation L (y : L))
    change valuation L (algebraMap F L a) = valuation L (y : L) at ha
    have haF := (Valuation.HasExtension.val_map_lt_one_iff (valuation F) (valuation L) a).mp
      (ha.trans_lt hy')
    let a₀ : O F := ⟨a, haF.le⟩
    have ha₀ : a₀ ∈ maximalIdeal (O F) := (Valuation.mem_maximalIdeal_iff (v := valuation F)).mpr haF
    apply Ideal.mem_of_dvd _ ?_ (Ideal.mem_map_of_mem _ ha₀)
    apply (Valuation.integer.integers (valuation L)).dvd_iff_le.mpr
    exact ha.ge

/-- An unramified finite extension is generated by roots of unity of order
prime to the residue characteristic. -/
private theorem unramified_adjoin_roots [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (hsurj : Function.Surjective (fun x : F => valuation L (algebraMap F L x))) :
    ∃ n : ℕ, (n : κ F) ≠ 0 ∧ IntermediateField.adjoin F {x : L | x ^ n = 1} = ⊤ := by
  let : (valuation F).HasExtension (valuation L) := valuation_hasExtension
  let : IsIntegralClosure (O L) (O F) L := valuation_isIntegralClosure
  let : Module.Finite (O F) (O L) := IsIntegralClosure.finite (O F) F L (O L)
  let n := Nat.card (κ L) - 1
  refine ⟨n, (residue_natCast_ne_zero_iff (L := L) n).mpr residue_card_sub_one_cast_ne_zero, ?_⟩
  let E := IntermediateField.adjoin F {x : L | x ^ n = 1}
  let S : Submodule (O F) (O L) :=
    (E.toSubalgebra.toSubmodule.restrictScalars (O F)).comap
      ((Algebra.linearMap (O L) L).restrictScalars (O F))
  have hS (x : O L) : x ∈ S ↔ (x : L) ∈ E := Iff.rfl
  have htop : S = ⊤ := by
    refine top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := maximalIdeal (O F)) Module.Finite.fg_top ?_ ?_)
    · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    · intro x _
      obtain ⟨y, hy, hyroot⟩ := lift_residue_root (residue (O L) x)
      have hyS : y ∈ S := (hS _).2 <| hyroot.elim
        (fun h => h.symm ▸ E.zero_mem) (fun h => IntermediateField.subset_adjoin F {x : L | x ^ n = 1} h)
      have hxy : x - y ∈ maximalIdeal (O L) := by
        rw [← residue_eq_zero_iff, map_sub, hy, sub_self]
      have hxy' : x - y ∈ maximalIdeal (O F) • (⊤ : Submodule (O F) (O L)) := by
        rw [← map_maximalIdeal_of_surjective hsurj] at hxy
        rw [Ideal.smul_top_eq_map]
        exact hxy
      exact Submodule.mem_sup.mpr ⟨y, hyS, x - y, hxy', by abel⟩
  apply top_unique
  intro x _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (O L) x
  exact E.div_mem ((hS a).1 (htop ▸ Submodule.mem_top)) ((hS b).1 (htop ▸ Submodule.mem_top))

omit [ValuativeExtension F L] in
private theorem surjective_of_map_maximalIdeal [h : (valuation F).HasExtension (valuation L)]
    (hmap : (maximalIdeal (O F)).map (algebraMap (O F) (O L)) = maximalIdeal (O L)) :
    Function.Surjective (fun x : F => valuation L (algebraMap F L x)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (O F)
  let πL := algebraMap (O F) (O L) π
  have hπL : Irreducible πL := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 <| by
    rw [← hmap, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  intro γ
  obtain ⟨x, rfl⟩ := valuation_surjective γ
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective (O L) x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simpa using hfrac.symm
  obtain ⟨i, s, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπL
  obtain ⟨j, t, hb⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπL
  refine ⟨(π : F) ^ i / (π : F) ^ j, ?_⟩
  have hs : valuation L (algebraMap (O L) L (s : O L)) = 1 :=
    (Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one.mp s.isUnit
  have ht : valuation L (algebraMap (O L) L (t : O L)) = 1 :=
    (Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one.mp t.isUnit
  change valuation L (algebraMap F L _) = valuation L x
  conv_rhs => rw [← hfrac, ha, hb]
  simp only [map_div₀, map_pow, map_mul, hs, ht, one_mul]
  rfl

private theorem map_maximalIdeal_of_finrank_le_residue [FiniteDimensional F L]
    [Algebra.IsSeparable F L] [h : (valuation F).HasExtension (valuation L)]
    (hrank : Module.finrank F L ≤ Module.finrank (κ F) (κ L)) :
    (maximalIdeal (O F)).map (algebraMap (O F) (O L)) = maximalIdeal (O L) := by
  let : IsIntegralClosure (O L) (O F) L := valuation_isIntegralClosure
  let : Module.Finite (O F) (O L) := IsIntegralClosure.finite (O F) F L (O L)
  let : Module.Free (O F) (O L) := IsIntegralClosure.module_free (O F) F L (O L)
  let I := (maximalIdeal (O F)).map (algebraMap (O F) (O L))
  have hle : I ≤ maximalIdeal (O L) := by
    rw [Ideal.map_le_iff_le_comap]
    exact (Valuation.HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal
      (valuation F) (valuation L)).ge
  let k := ↥(O F) ⧸ maximalIdeal (O F)
  let Q := ↥(O L) ⧸ maximalIdeal (O L)
  let : Field k := Ideal.Quotient.field _
  let f : (↥(O L) ⧸ I) →ₐ[k] Q :=
    { Ideal.Quotient.factor hle with
      commutes' := fun a => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        rfl }
  have hsurj : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  have hr : Module.finrank k (↥(O L) ⧸ I) = Module.finrank F L :=
    (IsLocalRing.finrank_quotient_map (R := O F) (S := O L)).trans
      (IsIntegralClosure.rank (O F) F L (O L))
  let : Module.Finite k (↥(O L) ⧸ I) := Module.Finite.of_restrictScalars_finite (O F) _ _
  have hrank' : Module.finrank F L ≤ Module.finrank k Q := hrank
  have hf : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) (le_antisymm (hr ▸ hrank')
        (LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hsurj))).mpr hsurj
  refine le_antisymm hle (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (hf ?_))
  change Ideal.Quotient.mk (maximalIdeal (O L)) x = f 0
  rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact hx

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
private theorem automorphism_preserves_integrality [FiniteDimensional F L]
    (σ : L ≃ₐ[F] L) (x : L) :
    valuation L (σ x) ≤ 1 ↔ valuation L x ≤ 1 := by
  let r := ‹ValuativeRel L›
  have h₀ : @ValuativeExtension F L _ _ _ r _ := inferInstance
  let w := (valuation L).comap σ.toRingHom
  let s := ValuativeRel.ofValuation w
  have hext : @ValuativeExtension F L _ _ _ s _ := by
    let : ValuativeRel L := s
    let : w.Compatible := Valuation.Compatible.ofValuation w
    constructor
    intro a b
    rw [w.vle_iff_le]
    let : ValuativeRel L := r
    change valuation L (σ (algebraMap F L a)) ≤ valuation L (σ (algebraMap F L b)) ↔ _
    rw [σ.commutes, σ.commutes, ← (valuation L).vle_iff_le]
    exact ValuativeExtension.vle_iff_vle a b
  have heq : s = r := by
    obtain ⟨r₀, _, _, _, _, _, uniq⟩ := finiteExtension_localField (K := F) (L := L)
    exact (uniq s hext).trans (uniq r h₀).symm
  have hw : @Valuation.Compatible L _ _ _ w r :=
    (congrArg (fun t : ValuativeRel L => @Valuation.Compatible L _ _ _ w t) heq) ▸
      Valuation.Compatible.ofValuation w
  let : ValuativeRel L := r
  exact w.vle_one_iff.symm.trans (valuation L).vle_one_iff

private def restrictToIntegers [FiniteDimensional F L] [h : (valuation F).HasExtension (valuation L)]
    (σ : L ≃ₐ[F] L) : (O L) ≃ₐ[O F] (O L) where
  toFun x := ⟨σ x, (automorphism_preserves_integrality σ x).mpr x.property⟩
  invFun x := ⟨σ.symm x, (automorphism_preserves_integrality σ.symm x).mpr x.property⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul σ (x : L) y)
  map_add' x y := Subtype.ext (map_add σ (x : L) y)
  commutes' a := Subtype.ext (σ.commutes (a : F))

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
private theorem root_of_unity_mem_integer {n : ℕ} (hn : n ≠ 0) {x : L} (hx : x ^ n = 1) :
    x ∈ O L := by
  change valuation L x ≤ 1
  apply (pow_le_pow_iff_left₀ zero_le zero_le hn).mp
  rw [← map_pow, hx, map_one, one_pow]

/-- Reduction is injective on prime-to-residue-characteristic roots of unity. -/
private theorem root_of_unity_eq_of_residue_eq {n : ℕ} (hn : (n : κ L) ≠ 0)
    {x y : O L} (hx : (x : L) ^ n = 1) (hy : (y : L) ^ n = 1)
    (hred : residue (O L) x = residue (O L) y) : x = y := by
  let f : (O L)[X] := X ^ n - 1
  have hx' : f.eval x = 0 := by
    have : x ^ n = 1 := Subtype.ext hx
    simp [f, this]
  have hy' : f.eval y = 0 := by
    have : y ^ n = 1 := Subtype.ext hy
    simp [f, this]
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hx' hy' ?_ ?_
  · rw [← residue_ne_zero_iff_isUnit, map_sub, hred, sub_self]
    exact not_not_intro rfl
  · have hxr : residue (O L) x ≠ 0 := by
      have hh : residue (O L) x ^ n = 1 := (map_pow (residue (O L)) x n).symm.trans
        (congrArg (residue (O L)) (show x ^ n = 1 from Subtype.ext hx) |>.trans (map_one _))
      have hn' : n ≠ 0 := by
        intro h
        simp [h] at hn
      intro h
      simp [h, hn'] at hh
    rw [← residue_ne_zero_iff_isUnit]
    simpa [f, derivative_X_pow] using mul_ne_zero hn (pow_ne_zero (n - 1) hxr)

/-- A Galois extension generated by prime-to-residue-characteristic roots of
unity has no inertia, so its degree is bounded by the residue degree. -/
private theorem finrank_le_residue_of_adjoin_roots [FiniteDimensional F L] [IsGalois F L]
    [h : (valuation F).HasExtension (valuation L)] {n : ℕ} (hn : (n : κ F) ≠ 0)
    (hgen : IntermediateField.adjoin F {x : L | x ^ n = 1} = ⊤) :
    Module.finrank F L ≤ Module.finrank (κ F) (κ L) := by
  let f (σ : L ≃ₐ[F] L) := ResidueField.mapAlgEquiv' (restrictToIntegers σ)
  have hf : Function.Injective f := by
    intro σ τ heq
    have htop : Algebra.adjoin F {x : L | x ^ n = 1} = ⊤ := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun x _ => Algebra.IsAlgebraic.isAlgebraic (R := F) x), hgen]
      rfl
    have hστ : σ.toAlgHom = τ.toAlgHom := AlgHom.ext_of_adjoin_eq_top htop <| by
      intro x hx
      change x ^ n = 1 at hx
      have hn' : n ≠ 0 := by
        intro h
        simp [h] at hn
      let a : O L := ⟨x, root_of_unity_mem_integer hn' hx⟩
      have heq' : residue (O L) (restrictToIntegers σ a) =
          residue (O L) (restrictToIntegers τ a) :=
        DFunLike.congr_fun heq (residue (O L) a)
      have hxσ : (σ x) ^ n = 1 := by rw [← map_pow, hx, map_one]
      have hxτ : (τ x) ^ n = 1 := by rw [← map_pow, hx, map_one]
      exact congrArg Subtype.val <| root_of_unity_eq_of_residue_eq
        ((residue_natCast_ne_zero_iff (L := L) n).mp hn) hxσ hxτ heq'
    ext x
    exact DFunLike.congr_fun hστ x
  rw [← IsGalois.card_aut_eq_finrank F L, ← IsGalois.card_aut_eq_finrank (κ F) (κ L)]
  exact Nat.card_le_card_of_injective f hf

private lemma roots_X_pow_sub_one {B : Type*} [Field B] {C : Type*} [Field C] [Algebra B C]
    {n : ℕ} (hn : n ≠ 0) : (X ^ n - Polynomial.C (1 : B)).rootSet C = {x : C | x ^ n = 1} := by
  ext x
  rw [Polynomial.mem_rootSet]
  have hp : (X ^ n - 1 : B[X]) ≠ 0 := X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1
  simp [hp, sub_eq_zero]

private noncomputable def cyclotomicStage (F : Type u) [Field F] (n : ℕ) :
    IntermediateField F (SeparableClosure F) :=
  IntermediateField.adjoin F ((X ^ n - Polynomial.C (1 : F)).rootSet (SeparableClosure F))

/-- Splitting fields of prime-to-residue-characteristic roots of unity are unramified. -/
private theorem cyclotomicStage_data {n : ℕ} (hn : (n : κ F) ≠ 0) :
    IsUnramified F (cyclotomicStage F n) ∧
    ((X ^ n - Polynomial.C 1 : F[X]).map (algebraMap F (cyclotomicStage F n))).Splits := by
  let p : F[X] := X ^ n - Polynomial.C 1
  have hnO : (n : O F) ≠ 0 := by
    intro h
    apply hn
    simpa only [map_natCast, map_zero] using congrArg (residue (O F)) h
  have hnF : (n : F) ≠ 0 := by
    simpa only [map_natCast] using map_ne_zero_iff
      (algebraMap (O F) F) (IsFractionRing.injective (O F) F) |>.2 hnO
  have hn' : n ≠ 0 := by
    intro h
    simp [h] at hn
  have hsep : p.Separable := separable_X_pow_sub_C 1 hnF one_ne_zero
  have hsplit : (p.map (algebraMap F (SeparableClosure F))).Splits :=
    IsSepClosed.splits_codomain p hsep
  let E := cyclotomicStage F n
  let : p.IsSplittingField F E := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  let : FiniteDimensional F E := Polynomial.IsSplittingField.finiteDimensional E p
  let : IsGalois F E := IsGalois.of_separable_splitting_field hsep
  have hE : IsUnramified F E := by
    obtain ⟨r, T, hext, hlocal, _, _, _⟩ := finiteExtension_localField (K := F) (L := E)
    let : ValuativeRel E := r
    let : TopologicalSpace E := T
    have : (valuation F).HasExtension (valuation E) := valuation_hasExtension
    have hgen : IntermediateField.adjoin F {x : E | x ^ n = 1} = ⊤ := by
      rw [← roots_X_pow_sub_one (B := F) hn']
      exact (isSplittingField_iff_intermediateField.mp (inferInstance : p.IsSplittingField F E)).2
    have hle := finrank_le_residue_of_adjoin_roots hn hgen
    exact ⟨inferInstance, inferInstance, r, T, hlocal, hext,
       surjective_of_map_maximalIdeal (map_maximalIdeal_of_finrank_le_residue hle)⟩
  exact ⟨hE, Polynomial.IsSplittingField.splits E p⟩

/-- All roots of unity of order prime to the residue characteristic are already
in the maximal unramified field. -/
theorem splits_pow_sub_one_maximalUnramified {n : ℕ} (hn : (n : κ F) ≠ 0) :
    (X ^ n - Polynomial.C (1 : maximalUnramified F)).Splits := by
  let E := cyclotomicStage F n
  let p : F[X] := X ^ n - Polynomial.C 1
  obtain ⟨hE, hsplit⟩ := cyclotomicStage_data hn
  have hEK : E ≤ maximalUnramified F :=
    le_iSup (fun T : {T : IntermediateField F (SeparableClosure F) // IsUnramified F T} => T.val)
      ⟨E, hE⟩
  have hK : (p.map (algebraMap F (maximalUnramified F))).Splits := by
    let i := IntermediateField.inclusion hEK
    have hi : i.toRingHom.comp (algebraMap F E) = algebraMap F (maximalUnramified F) :=
      RingHom.ext i.commutes
    have hs := hsplit.map i.toRingHom
    rwa [Polynomial.map_map, hi] at hs
  simpa only [p, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_one, map_one] using hK

private theorem le_cyclotomicStage_of_unramified {E : IntermediateField F (SeparableClosure F)}
    (hE : IsUnramified F E) :
    ∃ n : ℕ, (n : κ F) ≠ 0 ∧ E ≤ cyclotomicStage F n := by
  obtain ⟨_, _, r, T, hlocal, hext, hsurj⟩ := hE
  let : ValuativeRel E := r
  let : TopologicalSpace E := T
  obtain ⟨n, hn, hgen⟩ := unramified_adjoin_roots hsurj
  have hn' : n ≠ 0 := by
    intro h
    simp [h] at hn
  refine ⟨n, hn, ?_⟩
  rw [← E.fieldRange_val, AlgHom.fieldRange_eq_map, ← hgen, IntermediateField.adjoin_map]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨x, hx, rfl⟩
  apply IntermediateField.subset_adjoin
  rw [roots_X_pow_sub_one hn']
  change E.val x ^ n = 1
  rw [← map_pow, show x ^ n = 1 from hx, map_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem cyclotomicStage_le_of_dvd {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hdiv : m ∣ n) :
    cyclotomicStage F m ≤ cyclotomicStage F n := by
  unfold cyclotomicStage
  simp only [roots_X_pow_sub_one hm, roots_X_pow_sub_one hn]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  apply IntermediateField.subset_adjoin
  obtain ⟨k, rfl⟩ := hdiv
  change x ^ (m * k) = 1
  rw [pow_mul, show x ^ m = 1 from hx, one_pow]

/-- The compositum defining the maximal unramified field is the union of its
finite unramified subextensions. The cyclotomic fields give a directed family
containing every finite unramified subextension. -/
theorem mem_maximalUnramified_iff {x : SeparableClosure F} :
    x ∈ maximalUnramified F ↔
      ∃ E : IntermediateField F (SeparableClosure F), IsUnramified F E ∧ x ∈ E := by
  let S := {E : IntermediateField F (SeparableClosure F) // IsUnramified F E}
  let g (E : S) := E.val
  let : Nonempty S := ⟨⟨cyclotomicStage F 1, (cyclotomicStage_data (n := 1) (by simp)).1⟩⟩
  have hdir : Directed (· ≤ ·) g := by
    intro E T
    obtain ⟨m, hm, hEm⟩ := le_cyclotomicStage_of_unramified E.property
    obtain ⟨n, hn, hTn⟩ := le_cyclotomicStage_of_unramified T.property
    have hm' : m ≠ 0 := fun h => hm (by simp [h])
    have hn' : n ≠ 0 := fun h => hn (by simp [h])
    have hmn : ((m * n : ℕ) : κ F) ≠ 0 := by simpa using mul_ne_zero hm hn
    refine ⟨⟨cyclotomicStage F (m * n), (cyclotomicStage_data hmn).1⟩, ?_, ?_⟩
    · exact hEm.trans (cyclotomicStage_le_of_dvd hm' (mul_ne_zero hm' hn') (dvd_mul_right m n))
    · exact hTn.trans (cyclotomicStage_le_of_dvd hn' (mul_ne_zero hm' hn') (dvd_mul_left n m))
  change x ∈ (↑(⨆ E, g E) : Set (SeparableClosure F)) ↔ _
  rw [IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion]
  exact ⟨fun ⟨E, hx⟩ => ⟨E.val, E.property, hx⟩, fun ⟨E, hE, hx⟩ => ⟨⟨E, hE⟩, hx⟩⟩

/-- A field generated by roots of unity embeds in any field in which the
corresponding polynomial splits. -/
private theorem nonempty_algHom_of_adjoin_roots {B : Type*} [Field B]
    {C : Type*} [Field C] [Algebra B C] [Algebra.IsAlgebraic B C]
    {M : Type*} [Field M] [Algebra B M]
    {n : ℕ} (hn : n ≠ 0) (hgen : IntermediateField.adjoin B {x : C | x ^ n = 1} = ⊤)
    (hsplit : (X ^ n - Polynomial.C (1 : M)).Splits) : Nonempty (C →ₐ[B] M) := by
  let e : C →ₐ[B] AlgebraicClosure M := IsAlgClosed.lift
  let i := IsScalarTower.toAlgHom B M (AlgebraicClosure M)
  have hle : e.fieldRange ≤ i.fieldRange := by
    rw [AlgHom.fieldRange_eq_map, ← hgen, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    change (e x) ∈ (algebraMap M (AlgebraicClosure M)).range
    apply hsplit.mem_range_of_isRoot (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1)
    have hx' : e x ^ n = 1 := by rw [← map_pow, show x ^ n = 1 from hx, map_one]
    simp [Polynomial.IsRoot, hx']
  exact ⟨i.equivFieldRange.symm.toAlgHom.comp
    ((IntermediateField.inclusion hle).comp e.equivFieldRange.toAlgHom)⟩


/-- Descend the division factor to a finite extension of `F`. Its unramified
splitting field embeds in `M` because the requisite roots of unity lie in `Fⁿʳ`. -/
theorem brauer_vanishing : BrauerVanishing.{u, v, w} := by
  intro F _ _ _ _ M _ _ _ _ A _ _ hA
  let K := maximalUnramified F
  let : Algebra F M := ((algebraMap K M).comp (algebraMap F K)).toAlgebra
  let : IsScalarTower F K M := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic F M := Algebra.IsAlgebraic.trans F K M
  obtain ⟨r, D, _, _, hD, hr, ⟨e⟩⟩ :=
    RM03.CSA.MatrixDivision.exists_presentation M A hA
  obtain ⟨E, hfin, D₀, _, _, hD₀, ⟨desc⟩⟩ := descend_division (F := F) hD
  obtain ⟨vE, TE, extE, locE, _, _, _⟩ := finiteExtension_localField (K := F) (L := E)
  let : ValuativeRel E := vE
  let : TopologicalSpace E := TE
  obtain ⟨L, _, _, hL, n, hn, ⟨splitL⟩⟩ :=
    division_has_unramified_splitting hD₀
  obtain ⟨m, hm, hgen⟩ : ∃ m : ℕ, (m : κ E) ≠ 0 ∧
      IntermediateField.adjoin E {x : L | x ^ m = 1} = ⊤ := by
    obtain ⟨_, _, vL, TL, locL, extL, hsurj⟩ := hL
    let : ValuativeRel L := vL
    let : TopologicalSpace L := TL
    exact unramified_adjoin_roots hsurj
  have hmF : (m : κ F) ≠ 0 := (residue_natCast_ne_zero_iff (L := E) m).mpr hm
  have hm0 : m ≠ 0 := by
    intro h
    simp [h] at hm
  have hs := splits_pow_sub_one_maximalUnramified (F := F) hmF
  have hsplitM : (X ^ m - Polynomial.C (1 : M)).Splits := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_one, map_one] using hs.map (algebraMap K M)
  let : FiniteDimensional E L := hL.1
  obtain ⟨f⟩ := nonempty_algHom_of_adjoin_roots hm0 hgen hsplitM
  let : Algebra L M := f.toRingHom.toAlgebra
  let : IsScalarTower E L M := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let splitM : D ≃ₐ[M] Matrix (Fin n) (Fin n) M :=
    desc.symm.trans (extendMatrixSplitting splitL)
  refine ⟨r * n, Nat.mul_pos hr hn, ⟨?_⟩⟩
  exact e.trans splitM.mapMatrix
    |>.trans (Matrix.compAlgEquiv (Fin r) (Fin n) M M)
    |>.trans (Matrix.reindexAlgEquiv M M finProdFinEquiv)

end Roots

/-- Every class equals the scalar class, represented by a universe lift of `M`. -/
theorem brauerGroup_trivial : BrauerGroupTrivial.{u, v, w} := by
  intro F _ _ _ _ M _ _ _ _
  refine ⟨RM03.Brauer.classOf (RM03.Brauer.scalarCSA.{v, w} M), ?_⟩
  intro x
  refine Quotient.inductionOn x ?_
  intro A
  exact (RM03.Brauer.classOf_eq_scalar_iff_split M A).mpr
    (brauer_vanishing.{u, v, max v w} F M A ⟨A.isSimple, A.isCentral, A.fin_dim⟩)

end LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
