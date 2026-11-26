import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
import LinearAlgebraicGroups.Classification.RankOneRelations
import Batteries.Tactic.OpenPrivate

open CategoryTheory
open scoped WithZero TensorProduct

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

open ValuativeRel WithZero
open Specs.ExceptionalLocalRootCoordinates

noncomputable section

variable (F L : Type*) [Field F] [Field L] [Algebra F L]
  [ValuativeRel F] [ValuativeRel L] [TopologicalSpace F] [TopologicalSpace L]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L]

attribute [local instance] canonicalExtension

private theorem normalizedValueGroupMap_apply (x : F) :
    normalizedValueGroupMap F L (normalizedValuation F x) =
      normalizedValuation L (algebraMap F L x) := by
  simp [normalizedValueGroupMap, normalizedValuation, Valuation.map]

private theorem normalizedValueGroupMap_exp (n : ℤ) :
    normalizedValueGroupMap F L (exp n) = exp (ramificationIndex F L * n) := by
  have hn : exp n = (exp (1 : ℤ)) ^ n := by
    calc
      exp n = exp (log ((exp (1 : ℤ)) ^ n)) := by simp
      _ = _ := exp_log (zpow_ne_zero _ exp_ne_zero)
  have h : StrictMono (normalizedValueGroupMap F L) :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).strictMono.comp
      (ValuativeExtension.mapValueGroupWithZero_strictMono.comp
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).symm.strictMono)
  have hzero : normalizedValueGroupMap F L (exp 1) ≠ 0 := by
    have hpos := h (exp_pos (a := (1 : ℤ)))
    rw [map_zero] at hpos
    exact hpos.ne'
  rw [hn, map_zpow₀]
  calc
    _ = exp (log ((normalizedValueGroupMap F L (exp 1)) ^ n)) :=
      (exp_log (zpow_ne_zero _ hzero)).symm
    _ = _ := by rw [log_zpow, zsmul_eq_mul, mul_comm]; rfl

private theorem normalizedValuation_surjective (x : ℤᵐ⁰) :
    ∃ t : L, normalizedValuation L t = x := by
  let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  obtain ⟨t, ht⟩ := valuation_surjective (i.symm x)
  exact ⟨t, by change i (valuation L t) = x; rw [ht, i.apply_symm_apply]⟩

private theorem normalizedValuation_algebraMap_exp {x : F} (hx : x ≠ 0) :
    normalizedValuation L (algebraMap F L x) =
      exp (ramificationIndex F L * log (normalizedValuation F x)) := by
  rw [← normalizedValueGroupMap_apply, ← normalizedValueGroupMap_exp, exp_log]
  simpa using hx

private theorem normalizedValuation_le_one (x : L) :
    normalizedValuation L x ≤ 1 ↔ valuation L x ≤ 1 := by
  let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  change i (valuation L x) ≤ 1 ↔ _
  rw [← map_one i, i.strictMono.le_iff_le]

private theorem normalizedValuation_lt_one (x : L) :
    normalizedValuation L x < 1 ↔ valuation L x < 1 := by
  let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  change i (valuation L x) < 1 ↔ _
  rw [← map_one i, i.strictMono.lt_iff_lt]

private theorem add_of_distinct_values {x y : L}
    (h : normalizedValuation L x ≠ normalizedValuation L y) :
    normalizedValuation L (x + y) = max (normalizedValuation L x) (normalizedValuation L y) := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [max_eq_right h.le, (normalizedValuation L).map_add_eq_of_lt_right h]
  · rw [max_eq_left h.le, (normalizedValuation L).map_add_eq_of_lt_left h]

theorem ramifiedQuadratic : RamifiedQuadratic := by
  intro F L _ _ _ _ _ _ _ _ _ _ hdegree hram
  let e := ramificationIndex F L
  have he : 1 < e := hram
  have hnot : ¬ e ∣ (-1 : ℤ) := fun hd ↦
    (not_le_of_gt he) (Int.le_of_dvd (by decide) (dvd_neg.mp hd))
  obtain ⟨π, hπ⟩ := normalizedValuation_surjective L (exp (-1))
  have hπ₀ : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hMap (a : F) (ha : a ≠ 0) :
      normalizedValuation L (algebraMap F L a) =
        exp (e * log (normalizedValuation F a)) :=
    normalizedValuation_algebraMap_exp F L ha
  have hind : LinearIndependent F ![(1 : L), π] :=
    (LinearIndependent.pair_iff' one_ne_zero).mpr fun a ha ↦ by
      rw [Algebra.smul_def, mul_one] at ha
      have ha₀ : a ≠ 0 := fun h ↦ hπ₀ (by simpa [h] using ha.symm)
      have hv := hMap a ha₀
      rw [ha, hπ, exp_inj] at hv
      have hdiv : e ∣ (-1 : ℤ) := ⟨_, hv⟩
      exact hnot hdiv
  let b : Module.Basis (Fin 2) F L := basisOfLinearIndependentOfCardEqFinrank hind (by
    simp [hdegree])
  have hexpand (z : L) : ∃ a c : F, z = algebraMap F L a + algebraMap F L c * π := by
    refine ⟨b.repr z 0, b.repr z 1, ?_⟩
    have hz := b.sum_repr z
    rw [Fin.sum_univ_two] at hz
    have hb : ⇑b = ![(1 : L), π] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    simpa [hb, Algebra.smul_def] using hz.symm
  have hdiff (a c : F) (h : a ≠ 0 ∨ c ≠ 0) :
      normalizedValuation L (algebraMap F L a) ≠
        normalizedValuation L (algebraMap F L c * π) := by
    rcases eq_or_ne a 0 with rfl | ha
    · have hc := h.resolve_left (not_not_intro rfl)
      rw [map_zero, map_zero, map_mul, hMap c hc, hπ, ← exp_add]
      exact exp_ne_zero.symm
    rcases eq_or_ne c 0 with rfl | hc
    · rw [map_zero, zero_mul, map_zero, hMap a ha]
      exact exp_ne_zero
    rw [map_mul, hMap a ha, hMap c hc, hπ, ← exp_add]
    intro hv
    rw [exp_inj] at hv
    have hdiv : e ∣ (-1 : ℤ) := ⟨log (normalizedValuation F a) -
      log (normalizedValuation F c), by linear_combination -hv⟩
    exact hnot hdiv
  have hsum (a c : F) :
      normalizedValuation L (algebraMap F L a + algebraMap F L c * π) =
        max (normalizedValuation L (algebraMap F L a))
          (normalizedValuation L (algebraMap F L c * π)) := by
    by_cases h : a ≠ 0 ∨ c ≠ 0
    · exact add_of_distinct_values L (hdiff a c h)
    · push Not at h
      simp [h.1, h.2]
  have he₂ : e = 2 := by
    obtain ⟨a, c, hac⟩ := hexpand (π ^ 2)
    have hπ₂ : normalizedValuation L (π ^ 2) = exp (-2) := by
      rw [pow_two, map_mul, hπ, ← exp_add]
      rfl
    have hv := congrArg (normalizedValuation L) hac
    rw [hπ₂, hsum] at hv
    rcases max_cases (normalizedValuation L (algebraMap F L a))
        (normalizedValuation L (algebraMap F L c * π)) with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm] at hv
      have ha : a ≠ 0 := by
        intro h
        simp [h] at hv
      rw [hMap a ha, exp_inj] at hv
      have hdiv : e ∣ (-2 : ℤ) := ⟨_, hv⟩
      have hd : e ∣ (2 : ℤ) := dvd_neg.mp hdiv
      exact le_antisymm (Int.le_of_dvd (by decide) hd) (by omega)
    · rw [hm] at hv
      have hc : c ≠ 0 := by
        intro h
        simp [h] at hv
      rw [map_mul, hMap c hc, hπ, ← exp_add, exp_inj] at hv
      have hdiv : e ∣ (-1 : ℤ) := ⟨log (normalizedValuation F c), by omega⟩
      exact (hnot hdiv).elim
  refine ⟨he₂, ?_, (residueMap F L).injective, ?_⟩
  · intro a
    by_cases ha : a = 0
    · simp [ha]
    rw [hMap a ha, he₂]
    have hv : normalizedValuation F a ≠ 0 := by simpa using ha
    calc
      exp (2 * log (normalizedValuation F a)) =
          exp (log (normalizedValuation F a)) ^ 2 := by
        rw [pow_two, ← exp_add, two_mul]
      _ = _ := by rw [exp_log hv]
  · intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, c, hac⟩ := hexpand (z : L)
    have hz : normalizedValuation L (z : L) ≤ 1 :=
      (normalizedValuation_le_one L _).mpr z.2
    rw [hac, hsum, max_le_iff] at hz
    let a₀ : (valuation F).valuationSubring := ⟨a,
      (Valuation.HasExtension.val_map_le_one_iff (valuation F) (valuation L) a).mp
        ((normalizedValuation_le_one L _).mp hz.1)⟩
    let cπ : (valuation L).valuationSubring :=
      ⟨algebraMap F L c * π, (normalizedValuation_le_one L _).mp hz.2⟩
    have hcπ : normalizedValuation L (cπ : L) < 1 := by
      by_cases hc : c = 0
      · simp [cπ, hc]
      change normalizedValuation L (algebraMap F L c * π) < 1
      rw [map_mul, hMap c hc, hπ, ← exp_add, he₂, exp_lt_one_iff]
      rw [map_mul, hMap c hc, hπ, ← exp_add, he₂, exp_le_one_iff] at hz
      omega
    have hcπ₀ : IsLocalRing.residue _ cπ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        ((valuation L).mem_maximalIdeal_iff.mpr ((normalizedValuation_lt_one L _).mp hcπ))
    have hz' : z = algebraMap _ _ a₀ + cπ := Subtype.ext hac
    refine ⟨IsLocalRing.residue _ a₀, ?_⟩
    change IsLocalRing.residue _ (algebraMap _ _ a₀) = IsLocalRing.residue _ z
    rw [hz', map_add, hcπ₀, add_zero]

theorem involutionPreservesValuation : InvolutionPreservesValuation := by
  intro F L _ _ _ _ rF rL _ tL _ localL extFL σ hσ x
  let v := valuation L
  have hvle (a b : L) : @ValuativeRel.vle L _ rL a b ↔ v a ≤ v b :=
    (valuation L).vle_iff_le
  let w := v.comap σ.toRingEquiv.toRingHom
  let r := ValuativeRel.ofValuation w
  have hdef (a b : L) : @ValuativeRel.vle L _ r a b ↔ v (σ a) ≤ v (σ b) := by
    have hw : @ValuativeRel.vle L _ r a b ↔ w a ≤ w b := Iff.rfl
    rw [hw]
    simp only [w, Valuation.comap_apply]
    rfl
  have hext : @ValuativeExtension F L _ _ rF r _ := by
    constructor
    intro a b
    rw [hdef, σ.commutes, σ.commutes]
    exact (hvle _ _).symm.trans (extFL.vle_iff_vle a b)
  obtain ⟨r₀, T₀, _, _, _, _, huni⟩ :=
    LinearAlgebraicGroups.Arithmetic.finiteExtension_localField (K := F) (L := L)
  have heq : r = rL := (huni r hext).trans (huni rL extFL).symm
  have hle (a b : L) : v (σ a) ≤ v (σ b) ↔ v a ≤ v b := by
    rw [← hdef, heq]
    exact hvle a b
  have hlt (a b : L) : v (σ a) < v (σ b) ↔ v a < v b :=
    lt_iff_lt_of_le_iff_le (hle b a)
  have hv : v (σ x) = v x := by
    rcases lt_trichotomy (v (σ x)) (v x) with h | h | h
    · have hh := (hlt (σ x) x).mpr h
      rw [hσ x] at hh
      exact (h.asymm hh).elim
    · exact h
    · have hh := (hlt x (σ x)).mpr h
      rw [hσ x] at hh
      exact (h.asymm hh).elim
  let i := @IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L _ rL tL localL
  change i (v (σ x)) = i (v x)
  rw [hv]

section PinnedPoints

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A : Type u} [CommRing A] [Algebra k A]

private theorem extendPoint_injective :
    Function.Injective (extendPoint (k := k) (K := K) (A := A)) := by
  intro p q hpq
  ext x
  apply (algebraMap k K).injective
  simpa [extendPoint] using congrFun (congrArg DFunLike.coe hpq) (1 ⊗ₜ[k] x)

private theorem extendPoint_range [FiniteDimensional k K] [IsGalois k K]
    (p : (K ⊗[k] A) →ₐ[K] K) :
    p ∈ Set.range (extendPoint (k := k) (K := K) (A := A)) ↔
    ∀ σ x, p ((SemilinearAction.scalarExtension (K := K) A).act σ x) = σ (p x) := by
  constructor
  · rintro ⟨q, rfl⟩ σ x
    refine TensorProduct.inductionOn (motive := fun x ↦
      extendPoint q ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
        σ (extendPoint (K := K) q x)) x ?_ ?_
    · intro a x
      change extendPoint (K := K) q (σ a ⊗ₜ[k] x) =
        σ (extendPoint (K := K) q (a ⊗ₜ[k] x))
      simp only [extendPoint, AlgHom.liftEquiv_tmul, AlgHom.comp_apply,
        Algebra.ofId_apply, smul_eq_mul, map_mul, AlgEquiv.commutes]
    · intro a b ha hb
      simp only [map_add, ha, hb]
  · intro h
    let f : A →ₐ[k] K := (AlgHom.liftEquiv k K A K).symm p
    let i : k →ₐ[k] K := Algebra.ofId k K
    have hf (x : A) : f x ∈ i.range := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed (f x)).mpr
      intro σ
      have hx := h σ (1 ⊗ₜ[k] x)
      change p (σ 1 ⊗ₜ[k] x) = σ (p (1 ⊗ₜ[k] x)) at hx
      simpa [f] using hx.symm
    let e : k ≃ₐ[k] i.range := AlgEquiv.ofInjective i (algebraMap k K).injective
    let q : A →ₐ[k] k := e.symm.toAlgHom.comp (f.codRestrict i.range hf)
    refine ⟨q, (AlgHom.liftEquiv k K A K).symm.injective ?_⟩
    unfold extendPoint
    rw [Equiv.symm_apply_apply]
    change i.comp q = f
    ext x
    change i (e.symm ⟨f x, hf x⟩) = f x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, hf x⟩)

theorem pinnedFixedPoints : PinnedFixedPoints.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d
  let S := Specs.AdjointCocharacters.coordinateHopf P.pair.G
  let H := Specs.AdjointCocharacters.coordinateHopf G
  let i : (K ⊗[k] S) ≃ₐ[K] (K ⊗[k] H) :=
    { d.groupIso.hom.hom.toAlgHom with
      invFun := d.groupIso.inv.hom
      left_inv := ConcreteCategory.congr_hom d.groupIso.hom_inv_id
      right_inv := ConcreteCategory.congr_hom d.groupIso.inv_hom_id }
  have hi (p : H →ₐ[k] k) : pinnedPointMap d p = (extendPoint p).comp i.toAlgHom := rfl
  have he (σ : Gal(K/k)) (x : K ⊗[k] S) :
      (SemilinearAction.scalarExtension (K := K) H).act σ (i x) =
        i (pinnedOperator d σ x) := d.twistedAction σ x
  constructor
  · intro p q hpq
    apply extendPoint_injective (K := K)
    apply AlgHom.ext
    intro x
    have h := DFunLike.congr_fun (show (extendPoint p).comp i.toAlgHom =
        (extendPoint q).comp i.toAlgHom from hpq) (i.symm x)
    simpa using h
  · intro p
    constructor
    · rintro ⟨q, rfl⟩ σ x
      rw [hi]
      change extendPoint q (i (pinnedOperator d σ x)) = σ (extendPoint q (i x))
      rw [← he]
      exact (extendPoint_range _).mp ⟨q, rfl⟩ σ (i x)
    · intro hp
      let f : (K ⊗[k] H) →ₐ[K] K := p.comp i.symm.toAlgHom
      have hf (σ : Gal(K/k)) (x : K ⊗[k] H) :
          f ((SemilinearAction.scalarExtension (K := K) H).act σ x) = σ (f x) := by
        obtain ⟨y, rfl⟩ := i.surjective x
        rw [he]
        simpa [f] using hp σ y
      obtain ⟨q, hq⟩ := (extendPoint_range f).mpr hf
      refine ⟨q, ?_⟩
      rw [hi, hq]
      ext x
      simp [f]


section TestAlgebras

variable {R : Type u} [CommRing R] [Algebra k R]

private theorem includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) := by
  let b := Module.Free.chooseBasis k R
  intro x y h
  apply b.repr.injective
  ext j
  apply (algebraMap k K).injective
  have hh := congrArg (fun z => (b.baseChange K).repr z j) h
  simpa [Algebra.smul_def] using hh

private theorem includeRight_range [FiniteDimensional k K] [IsGalois k K]
    (z : K ⊗[k] R) :
    z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).range ↔
      ∀ σ, (SemilinearAction.scalarExtension (K := K) R).act σ z = z := by
  classical
  let i : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
  let ρ := SemilinearAction.scalarExtension (k := k) (K := K) R
  constructor
  · rintro ⟨r, rfl⟩ σ
    change σ 1 ⊗ₜ[k] r = 1 ⊗ₜ[k] r
    rw [map_one]
  · intro h
    let b := Module.Free.chooseBasis k R
    let B := b.baseChange K
    have hrepr (σ : Gal(K/k)) (x : K ⊗[k] R) (j : _) :
        B.repr (ρ.act σ x) j = σ (B.repr x j) := by
      refine TensorProduct.inductionOn x ?_ ?_
      · intro a r
        change B.repr (σ a ⊗ₜ[k] r) j = σ (B.repr (a ⊗ₜ[k] r) j)
        simp [B, Algebra.smul_def, AlgEquiv.commutes]
      · intro x y hx hy
        simp only [map_add, Finsupp.add_apply, hx, hy]
    have hj (j : _) : ∃ c : k, algebraMap k K c = B.repr z j := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      rw [← hrepr, h σ]
    let w := ∑ j ∈ (B.repr z).support, (hj j).choose • b j
    refine ⟨w, B.repr.injective ?_⟩
    have hw : i w = ∑ j ∈ (B.repr z).support, (B.repr z j) • B j := by
      change i.toLinearMap w = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [LinearMap.map_smul]
      change (hj j).choose • ((1 : K) ⊗ₜ[k] b j) = _
      rw [← IsScalarTower.algebraMap_smul K ((hj j).choose), (hj j).choose_spec]
      simp [B]
    change B.repr (i w) = B.repr z
    rw [hw]
    exact congrArg B.repr (B.linearCombination_repr z)

private theorem extendAlgebraPoint_injective :
    Function.Injective (extendAlgebraPoint (k := k) (K := K) (A := A) (R := R)) := by
  intro p q hpq
  apply AlgHom.ext
  intro x
  apply includeRight_injective (k := k) (K := K)
  simpa [extendAlgebraPoint, AlgHom.liftEquiv_tmul] using
    DFunLike.congr_fun hpq (1 ⊗ₜ[k] x)

private theorem extendAlgebraPoint_range [FiniteDimensional k K] [IsGalois k K]
    (p : (K ⊗[k] A) →ₐ[K] (K ⊗[k] R)) :
    p ∈ Set.range (extendAlgebraPoint (k := k) (K := K) (A := A) (R := R)) ↔
      ∀ σ x, p ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
        (SemilinearAction.scalarExtension (K := K) R).act σ (p x) := by
  constructor
  · rintro ⟨q, rfl⟩ σ x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro a x
      change extendAlgebraPoint (K := K) q (σ a ⊗ₜ[k] x) =
        (SemilinearAction.scalarExtension (K := K) R).act σ
          (extendAlgebraPoint (K := K) q (a ⊗ₜ[k] x))
      simp only [extendAlgebraPoint, AlgHom.liftEquiv_tmul, AlgHom.comp_apply,
        (SemilinearAction.scalarExtension (k := k) (K := K) R).map_smul]
      congr 1
      change (1 : K) ⊗ₜ[k] q x = σ 1 ⊗ₜ[k] q x
      rw [map_one]
    · intro x y hx hy
      simp only [map_add, hx, hy]
  · intro h
    let f : A →ₐ[k] K ⊗[k] R := (AlgHom.liftEquiv k K A (K ⊗[k] R)).symm p
    let i : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
    have hf (x : A) : f x ∈ i.range := by
      apply (includeRight_range _).mpr
      intro σ
      have hx := h σ (1 ⊗ₜ[k] x)
      change p (σ 1 ⊗ₜ[k] x) =
        (SemilinearAction.scalarExtension (K := K) R).act σ (p (1 ⊗ₜ[k] x)) at hx
      simpa [f] using hx.symm
    let e : R ≃ₐ[k] i.range := AlgEquiv.ofInjective i includeRight_injective
    let q : A →ₐ[k] R := e.symm.toAlgHom.comp (f.codRestrict i.range hf)
    refine ⟨q, (AlgHom.liftEquiv k K A (K ⊗[k] R)).symm.injective ?_⟩
    unfold extendAlgebraPoint
    rw [Equiv.symm_apply_apply]
    change i.comp q = f
    ext x
    change i (e.symm ⟨f x, hf x⟩) = f x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, hf x⟩)

theorem pinnedAlgebraFixedPoints : PinnedAlgebraFixedPoints.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d R _ _
  let S := Specs.AdjointCocharacters.coordinateHopf P.pair.G
  let H := Specs.AdjointCocharacters.coordinateHopf G
  let i : (K ⊗[k] S) ≃ₐ[K] (K ⊗[k] H) :=
    { d.groupIso.hom.hom.toAlgHom with
      invFun := d.groupIso.inv.hom
      left_inv := ConcreteCategory.congr_hom d.groupIso.hom_inv_id
      right_inv := ConcreteCategory.congr_hom d.groupIso.inv_hom_id }
  have hi (p : H →ₐ[k] R) :
      pinnedAlgebraPointMap d p = (extendAlgebraPoint p).comp i.toAlgHom := rfl
  have he (σ : Gal(K/k)) (x : K ⊗[k] S) :
      (SemilinearAction.scalarExtension (K := K) H).act σ (i x) =
        i (pinnedOperator d σ x) := d.twistedAction σ x
  constructor
  · intro p q hpq
    apply extendAlgebraPoint_injective (K := K)
    apply AlgHom.ext
    intro x
    have h := DFunLike.congr_fun (show (extendAlgebraPoint p).comp i.toAlgHom =
        (extendAlgebraPoint q).comp i.toAlgHom from hpq) (i.symm x)
    simpa using h
  · intro p
    constructor
    · rintro ⟨q, rfl⟩ σ x
      rw [hi]
      change extendAlgebraPoint q (i (pinnedOperator d σ x)) =
        (SemilinearAction.scalarExtension (K := K) R).act σ (extendAlgebraPoint q (i x))
      rw [← he]
      exact (extendAlgebraPoint_range _).mp ⟨q, rfl⟩ σ (i x)
    · intro hp
      let f : (K ⊗[k] H) →ₐ[K] (K ⊗[k] R) := p.comp i.symm.toAlgHom
      have hf (σ : Gal(K/k)) (x : K ⊗[k] H) :
          f ((SemilinearAction.scalarExtension (K := K) H).act σ x) =
            (SemilinearAction.scalarExtension (K := K) R).act σ (f x) := by
        obtain ⟨y, rfl⟩ := i.surjective x
        rw [he]
        simpa [f] using hp σ y
      obtain ⟨q, hq⟩ := (extendAlgebraPoint_range f).mpr hf
      refine ⟨q, ?_⟩
      rw [hi, hq]
      ext x
      simp [f]

end TestAlgebras

section PointGroups

open Specs.AdjointBorelCohomology (PinnedTwist)

private def extendHopfPoint {H : HopfAlgebraCategory k}
    {R S : Type u} [CommRing R] [CommRing S] [Algebra k R]
    [Algebra k S] [Algebra K S] [IsScalarTower k K S] (i : R →ₐ[k] S) :
    HopfPoints H R →* HopfPoints (extendedHopf K H) S :=
  MonoidHom.mk' (fun p ↦ WithConv.toConv (AlgHom.liftEquiv k K H S (i.comp p.ofConv))) (by
    intro p q
    apply WithConv.ofConv_injective
    apply (AlgHom.liftEquiv k K H S).symm.injective
    ext a
    change ((AlgHom.liftEquiv k K H S).symm
      (AlgHom.liftEquiv k K H S (i.comp (p * q).ofConv))) a = _
    rw [Equiv.symm_apply_apply, AlgHom.liftEquiv_symm_apply]
    let p' := WithConv.toConv (AlgHom.liftEquiv k K H S (i.comp p.ofConv))
    let q' := WithConv.toConv (AlgHom.liftEquiv k K H S (i.comp q.ofConv))
    change i ((p * q).ofConv a) = (p' * q').ofConv (1 ⊗ₜ[k] a)
    have hpq := AlgHom.convMul_apply (R := k) (A := R) (C := H) p q a
    change (p * q).ofConv a = _ at hpq
    have hpq' := AlgHom.convMul_apply p' q' (1 ⊗ₜ[k] a)
    change (p' * q').ofConv (1 ⊗ₜ[k] a) = _ at hpq'
    rw [hpq, hpq', TensorProduct.comul_tmul, Bialgebra.comul_one]
    generalize Coalgebra.comul (R := k) a = z
    induction z with
    | tmul x y =>
      simp [p', q', Algebra.TensorProduct.one_def, Algebra.TensorProduct.lift_tmul]
    | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy])

private def compHopfPoint {J H : HopfAlgebraCategory K}
    {R : Type u} [CommRing R] [Algebra K R] (f : J ⟶ H) :
    HopfPoints H R →* HopfPoints J R :=
  MonoidHom.mk' (fun p ↦ WithConv.toConv (p.ofConv.comp f.hom.toAlgHom)) (by
    intro p q
    exact WithConv.ofConv_injective (AlgHom.convMul_comp_bialgHom_distrib p q f.hom))

theorem pinnedPointGroups : PinnedPointGroups.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d
  let j := (compHopfPoint (R := K) d.groupIso.hom).comp
    (extendHopfPoint (K := K) (H := Specs.AdjointCocharacters.coordinateHopf G) (Algebra.ofId k K))
  have hj (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) k) : (j p).ofConv = pinnedPointMap d p.ofConv := rfl
  obtain ⟨hinj, hrange⟩ := pinnedFixedPoints d
  have hij : Function.Injective j := fun _ _ h ↦ WithConv.ofConv_injective
    (hinj (congrArg WithConv.ofConv h))
  let e := MonoidHom.ofInjective hij
  refine ⟨j.range, e, hj, fun p ↦ ?_⟩
  rw [← hrange]
  exact ⟨fun ⟨q, hq⟩ ↦ ⟨q.ofConv, congrArg WithConv.ofConv hq⟩,
    fun ⟨q, hq⟩ ↦ ⟨WithConv.toConv q, WithConv.ofConv_injective hq⟩⟩

theorem pinnedAlgebraPointGroups : PinnedAlgebraPointGroups.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d R _ _
  let j := (compHopfPoint (R := K ⊗[k] R) d.groupIso.hom).comp
    (extendHopfPoint (K := K) (H := Specs.AdjointCocharacters.coordinateHopf G)
      (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R))
  have hj (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) R) :
      (j p).ofConv = pinnedAlgebraPointMap d p.ofConv := rfl
  obtain ⟨hinj, hrange⟩ := pinnedAlgebraFixedPoints d R
  have hij : Function.Injective j := fun _ _ h ↦ WithConv.ofConv_injective
    (hinj (congrArg WithConv.ofConv h))
  let e := MonoidHom.ofInjective hij
  refine ⟨j.range, e, hj, fun p ↦ ?_⟩
  rw [← hrange]
  exact ⟨fun ⟨q, hq⟩ ↦ ⟨q.ofConv, congrArg WithConv.ofConv hq⟩,
    fun ⟨q, hq⟩ ↦ ⟨WithConv.toConv q, WithConv.ofConv_injective hq⟩⟩

end PointGroups

/-- A nonidentity element exhausts the nontrivial part of the quadratic Galois group. -/
private theorem quadraticGalois [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : Gal(K/k)) (hσ : σ ≠ 1) :
    (∀ g : Gal(K/k), g = 1 ∨ g = σ) ∧ σ * σ = 1 := by
  have hcard : Nat.card (Gal(K/k)) = 2 := (IsGalois.card_aut_eq_finrank k K).trans hdegree
  have hu := (Nat.card_eq_two_iff' (1 : Gal(K/k))).mp hcard
  have hcases (g : Gal(K/k)) : g = 1 ∨ g = σ := by
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr (ExistsUnique.unique hu hg hσ)
  refine ⟨hcases, (hcases (σ * σ)).resolve_right (fun hs ↦ hσ ?_)⟩
  apply mul_right_cancel (b := σ)
  simpa only [one_mul] using hs

/-- Fixed coordinates of a singleton and a swapped pair, including units. -/
theorem quadraticParameterDescent : QuadraticParameterDescent.{u} := by
  intro k K _ _ _ _ _ hdegree σ hσ R _ _ i τ
  obtain ⟨hcases, hss⟩ := quadraticGalois hdegree σ hσ
  let ρ := SemilinearAction.scalarExtension (k := k) (K := K) R
  have hfix (x : K ⊗[k] R) : τ x = x ↔ ∀ g, ρ.act g x = x := by
    refine ⟨fun hx g ↦ ?_, fun h ↦ h σ⟩
    rcases hcases g with rfl | rfl
    · exact ρ.one_act x
    · exact hx
  have hfixed (x : K ⊗[k] R) : τ x = x ↔ x ∈ Set.range i :=
    (hfix x).trans (includeRight_range x).symm
  have hinv (x : K ⊗[k] R) : τ (τ x) = x := by
    change ρ.act σ (ρ.act σ x) = x
    rw [← ρ.mul_act, hss, ρ.one_act]
  have hi : Function.Injective i := includeRight_injective
  refine ⟨hi, hfixed, fun x y ↦ ?_, fun t ↦ ?_⟩
  · refine ⟨fun h ↦ (congrArg Prod.snd h).symm, fun h ↦ ?_⟩
    rw [h, hinv]
  · let φ : (K ⊗[k] R) →ₐ[k] (K ⊗[k] R) :=
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k R)
    have hφ (x : K ⊗[k] R) : φ x = τ x := by
      induction x using TensorProduct.inductionOn with
      | tmul a r => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    constructor
    · intro ht
      have hU : Units.map φ.toMonoidHom t = t := Units.ext ((hφ t).trans ht)
      have hti : τ (↑t⁻¹ : K ⊗[k] R) = (↑t⁻¹ : K ⊗[k] R) := by
        rw [← hφ]
        exact congrArg Units.val (by rw [map_inv, hU] : Units.map φ.toMonoidHom t⁻¹ = t⁻¹)
      obtain ⟨a, ha⟩ := (hfixed t).mp ht
      obtain ⟨b, hb⟩ := (hfixed (↑t⁻¹ : K ⊗[k] R)).mp hti
      let u : Rˣ := ⟨a, b, hi (by simp [ha, hb]), hi (by simp [ha, hb])⟩
      exact ⟨u, Units.ext ha⟩
    · rintro ⟨u, rfl⟩
      exact (hfixed (i u)).mpr ⟨u, rfl⟩

/-- Coefficient conjugation commutes with all maps of test algebras. -/
theorem quadraticParameterNaturality : QuadraticParameterNaturality.{u} := by
  intro k K R S _ _ _ _ _ _ _ σ f x
  induction x using TensorProduct.inductionOn with
  | tmul a r => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pinnedSimpleCoordinates : PinnedSimpleCoordinates.{u} := by
  intro k _ A P f a
  let x := (a.val.val, (P.pin a).val.hom ≫ (P.roots a.val).val.inclusion)
  let y := (Specs.Pinning.transportCharacter f.asIso.hom.torus x.1, x.2 ≫ f.asIso.hom.group.hom)
  have hy : y ∈ Specs.Pinning.pinGraph P := by
    rw [← f.asIso.hom.pin_comm]
    exact ⟨x, ⟨a, rfl⟩, rfl⟩
  obtain ⟨b, hb⟩ := hy
  have hχ := congrArg Prod.fst hb
  refine ⟨b, ⟨hχ, (congrArg Prod.snd hb).symm⟩, fun c hc ↦ ?_⟩
  exact Subtype.ext (Subtype.ext (hc.1.trans hχ.symm))

end PinnedPoints

section RankOne

open Specs.IntegralRootRelations (upper lower)
open Matrix

private theorem upper_lower_induction {K : Type*} [Field K]
    (P : SpecialLinearGroup (Fin 2) K → Prop)
    (hu : ∀ t, P (upper t)) (hl : ∀ t, P (lower t))
    (hm : ∀ A B, P A → P B → P (A * B)) (A : SpecialLinearGroup (Fin 2) K) :
    P A := by
  apply SL2.transvection_induction P _ hm A
  intro i j hij t
  fin_cases i <;> fin_cases j
  · contradiction
  · convert hu t using 1
    apply Subtype.ext
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [SpecialLinearGroup.transvection_coe, upper, Matrix.single]
  · convert hl t using 1
    apply Subtype.ext
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [SpecialLinearGroup.transvection_coe, lower, Matrix.single]
  · contradiction

private theorem map_upper {K : Type*} [Field K] (σ : K ≃+* K) (t : K) :
    SpecialLinearGroup.map σ.toRingHom (upper t) = upper (σ t) := by
  apply Subtype.ext
  change (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K).map σ = !![1, σ t; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem map_lower {K : Type*} [Field K] (σ : K ≃+* K) (t : K) :
    SpecialLinearGroup.map σ.toRingHom (lower t) = lower (σ t) := by
  apply Subtype.ext
  change (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) K).map σ = !![1, 0; σ t, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem pairedRankOne : PairedRankOne := by
  intro K G _ _ σ τ hσ hτ a b
  dsimp only
  intro comm hu hl
  let s := SpecialLinearGroup.map (n := Fin 2) σ.toRingHom
  have hcomm (A B : SpecialLinearGroup (Fin 2) K) : Commute (a A) (b B) := by
    have aux (X) (hx : X ∈ Set.range (upper (R := K)) ∪ Set.range (lower (R := K)))
        (Y : SpecialLinearGroup (Fin 2) K) : Commute (a X) (b Y) := by
      induction Y using upper_lower_induction
      case hu => exact comm X hx _ (Or.inl (Set.mem_range_self _))
      case hl => exact comm X hx _ (Or.inr (Set.mem_range_self _))
      case hm A B ha hb => exact (map_mul b A B).symm ▸ ha.mul_right hb
    induction A using upper_lower_induction
    case hu => exact aux _ (Or.inl (Set.mem_range_self _)) _
    case hl => exact aux _ (Or.inr (Set.mem_range_self _)) _
    case hm X Y hx hy => exact (map_mul a X Y).symm ▸ hx.mul_left hy
  have ha (A) : τ (a A) = b (s A) := by
    induction A using upper_lower_induction
    case hu t => simpa only [s, map_upper] using hu t
    case hl t => simpa only [s, map_lower] using hl t
    case hm X Y hx hy => simp only [map_mul, hx, hy]
  have hs (A) : s (s A) = A := by
    apply Subtype.ext
    ext i j
    exact hσ _
  have hb (A) : τ (b A) = a (s A) := by
    simpa only [hs] using congrArg τ (ha (s A)).symm |>.trans (hτ _)
  have hb' (A) : τ (b (s A)) = a A := by rw [hb, hs]
  let f : SpecialLinearGroup (Fin 2) K →* G :=
    { toFun := fun A ↦ a A * b (s A)
      map_one' := by simp
      map_mul' := by
        intro A B
        simp only [map_mul]
        calc
          a A * a B * (b (s A) * b (s B)) =
              a A * (a B * b (s A)) * b (s B) := by simp only [mul_assoc]
          _ = _ := by rw [(hcomm B (s A)).eq]; simp only [mul_assoc] }
  have hf (A) : f A ∈ fixedSubgroup τ := by
    change τ (a A * b (s A)) = a A * b (s A)
    rw [map_mul, ha, hb']
    exact (hcomm A (s A)).eq.symm
  refine ⟨f.codRestrict (fixedSubgroup τ) hf, fun _ ↦ rfl, ?_, ?_⟩
  · intro t
    change a (upper t) * b (s (upper t)) = _
    rw [map_upper]
  · intro t
    change a (lower t) * b (s (lower t)) = _
    rw [map_lower]

end RankOne

section OrthogonalRoots

open Specs.Pinning (AttachedDatum BasedRootDatum PinnedGroup)
open Specs.AbstractPairing (Root)

theorem orthogonalRootCombinations : OrthogonalRootCombinations.{u} := by
  intro D hsym a b hab
  have hba : D.datum.pairing b a = 0 := (hsym b a).trans hab
  constructor
  · intro m n hm _ h
    have hh := congrArg (D.datum.coroot' a) h
    change D.datum.coroot' a (m • D.datum.root a) =
      D.datum.coroot' a (n • D.datum.root b) at hh
    simp only [map_smul, D.datum.root_coroot'_eq_pairing, D.datum.pairing_same,
      hba, smul_eq_mul] at hh
    omega
  · intro m n hm hn h
    obtain ⟨i, hi⟩ := h
    have hpa : D.datum.pairing i a = m * 2 := by
      rw [RootPairing.pairing_eq_add_of_root_eq_smul_add_smul hi]
      simp [hba]
    have hpb : D.datum.pairing i b = n * 2 := by
      rw [RootPairing.pairing_eq_add_of_root_eq_smul_add_smul hi]
      simp [hab]
    have he : (2 : ℤ) = m * (m * 2) + n * (n * 2) := by
      calc
        2 = D.datum.pairing i i := (D.datum.pairing_same i).symm
        _ = m • D.datum.pairing a i + n • D.datum.pairing b i :=
          RootPairing.pairing_eq_add_of_root_eq_smul_add_smul hi
        _ = _ := by rw [hsym a i, hsym b i, hpa, hpb, smul_eq_mul, smul_eq_mul]
    have hm₂ : 1 ≤ m ^ 2 := by have := sq_pos_iff.mpr hm; omega
    have hn₂ : 1 ≤ n ^ 2 := by have := sq_pos_iff.mpr hn; omega
    nlinarith only [he, hm₂, hn₂]

theorem orthogonalRootGroups : OrthogonalRootGroups.{u} := by
  intro k _ A P D hsym a b hab i hi j hj R p q
  let := D.comm
  let Q := D.datum.rootDatum
  change Q.pairing a b = 0 at hab
  change i ∈ ({a, Q.reflectionPerm a a} : Set (Root P.pair.T)) at hi
  change j ∈ ({b, Q.reflectionPerm b b} : Set (Root P.pair.T)) at hj
  have hp : Q.pairing i j = 0 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simpa using hab
  obtain ⟨hind, hcone⟩ := orthogonalRootCombinations D.toBased hsym i j hp
  apply Classification.RankOneRelations.independentRootCommutation P.pair.G P.pair.reductive
    P.pair.T P.pair.split P.pair.maximal i.val i.property j.val j.property _ _
    (P.roots i).val (P.roots j).val (P.roots i).property (P.roots j).property R p q
  · rintro ⟨m, n, hm, hn, he⟩
    apply hind m n hm hn
    change m • Q.root i = n • Q.root j
    rw [D.datum.root_eq, D.datum.root_eq]
    exact congrArg Additive.ofMul he
  · intro m n hm hn h
    apply hcone (m : ℤ) (n : ℤ) (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')
    let a₀ : Root P.pair.T := ⟨i.val ^ m * j.val ^ n, h⟩
    refine ⟨a₀, ?_⟩
    change Q.root a₀ = m • Q.root i + n • Q.root j
    rw [D.datum.root_eq, D.datum.root_eq, D.datum.root_eq]
    rfl

end OrthogonalRoots

section IntegralCoordinates

open Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open private additivePoint_surjective integralAdditivePoint_injective from
  LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

private theorem integralAdditivePoint_map {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (z : R) :
    integralSpec.map f.op ≫ additivePoint R z = additivePoint S (f.hom z) := by
  unfold additivePoint
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change f.hom (Polynomial.aeval z Polynomial.X) = Polynomial.aeval (f.hom z) Polynomial.X
  simp

private theorem markedRootPoint_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (a : D.I) (z : R) :
    (integralPointFunctor M.group).map f (markedRootPoint M R a z) =
      markedRootPoint M S a (f.hom z) := by
  change integralSpec.map f.op ≫ (additivePoint R z ≫ (M.root a).hom.hom) = _
  rw [← Category.assoc, integralAdditivePoint_map]
  rfl

private theorem markedRootPoint_injective {D : BasedRootDatum.{u}}
    (M : IntegralMarking D) (R : IntegralAlgebra.{u}) (a : D.I) :
    Function.Injective (markedRootPoint M R a) := by
  have := M.rootClosed a
  have : Mono (M.root a).hom.hom := Over.mono_of_mono_left _
  intro x y h
  apply integralAdditivePoint_injective R
  exact (cancel_mono (M.root a).hom.hom).mp h

private theorem integralPoint_map_injective {X : IntegralScheme.{u}} (hX : IsAffine X.left)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (fun p : integralSpec.obj (op R) ⟶ X ↦ integralSpec.map f.op ≫ p) := by
  let e := X.left.isoSpec
  intro p q h
  apply Over.OverMorphism.ext
  apply (cancel_mono e.hom).mp
  apply Spec.preimage_injective
  let j := CommRingCat.ofHom f.hom.toRingHom
  have hj : Mono j := ConcreteCategory.mono_of_injective j hf
  have h' : Spec.map j ≫ (p.left ≫ e.hom) = Spec.map j ≫ (q.left ≫ e.hom) := by
    have h'' := congrArg (fun t : integralSpec.obj (op S) ⟶ X ↦ t.left ≫ e.hom) h
    change (Spec.map j ≫ p.left) ≫ e.hom = (Spec.map j ≫ q.left) ≫ e.hom at h''
    calc
      _ = (Spec.map j ≫ p.left) ≫ e.hom := (Category.assoc _ _ _).symm
      _ = (Spec.map j ≫ q.left) ≫ e.hom := h''
      _ = _ := Category.assoc _ _ _
  have hh := congrArg Spec.preimage h'
  rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at hh
  exact (cancel_mono j).mp hh

private theorem liftIntegralClosedPoint {X Y : IntegralScheme.{u}} (m : X ⟶ Y)
    [IsClosedImmersion m.left] {R S : IntegralAlgebra.{u}} [IsReduced R]
    (f : R ⟶ S) (hf : Function.Injective f.hom) (p : integralSpec.obj (op R) ⟶ Y)
    (q : integralSpec.obj (op S) ⟶ X) (heq : integralSpec.map f.op ≫ p = q ≫ m) :
    ∃ q₀ : integralSpec.obj (op R) ⟶ X, q₀ ≫ m = p := by
  let j := (integralSpec.map f.op).left
  have : IsDominant j := by
    change IsDominant (Spec.map (CommRingCat.ofHom f.hom.toRingHom))
    rw [isDominant_iff]
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker f.hom.toRingHom ≤ nilradical R
    rw [(RingHom.injective_iff_ker_eq_bot f.hom.toRingHom).mp hf]
    exact bot_le
  have : IsReduced (integralSpec.obj (op R)).left := by
    change IsReduced (Spec (CommRingCat.of R))
    infer_instance
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have hj : (j ≫ p.left).ker = p.left.ker := by
    rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hh : j ≫ p.left = q.left ≫ m.left := congrArg Over.Hom.left heq
  have hker : m.left.ker ≤ p.left.ker := by
    rw [← hj, hh]
    exact q.left.le_ker_comp m.left
  let t := IsClosedImmersion.lift m.left p.left hker
  have ht : t ≫ m.left = p.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk t ?_, Over.OverMorphism.ext ht⟩
  rw [← Over.w m, ← Category.assoc, ht, Over.w p]

theorem integralRootTransportUnits : IntegralRootTransportUnits.{u} := by
  intro D M R S _ f hf g a b c n hg
  have (i : D.I) := M.rootClosed i
  let ψ : IntegralPoints M.group R →* IntegralPoints M.group S :=
    ((integralPointFunctor M.group).map f).hom
  have hroot (i : D.I) (z : R) : ψ (markedRootPoint M R i z) =
      markedRootPoint M S i (f.hom z) := markedRootPoint_map M f i z
  let p := g * markedRootPoint M R a 1 * g⁻¹
  have hp : ψ p = markedRootPoint M S b (c : S) := by
    change ψ (g * markedRootPoint M R a 1 * g⁻¹) = _
    rw [map_mul, map_mul, map_inv, hroot, map_one]
    change n * markedRootPoint M S a 1 * n⁻¹ = _
    simpa only [mul_one] using hg 1
  obtain ⟨p₀, hp₀⟩ := liftIntegralClosedPoint (M.root b).hom.hom f hf p (additivePoint S c) hp
  obtain ⟨d, rfl⟩ := additivePoint_surjective R p₀
  have hd : f.hom d = (c : S) := markedRootPoint_injective M S b <| by
    rw [← hroot, show markedRootPoint M R b d = p from hp₀]
    exact hp
  let q := g⁻¹ * markedRootPoint M R b 1 * g
  have hq : ψ q = markedRootPoint M S a (↑c⁻¹ : S) := by
    have h : n * markedRootPoint M S a (↑c⁻¹ : S) * n⁻¹ = markedRootPoint M S b 1 := by
      simpa only [Units.mul_inv] using hg (↑c⁻¹ : S)
    change ψ (g⁻¹ * markedRootPoint M R b 1 * g) = _
    rw [map_mul, map_mul, map_inv, hroot, map_one, ← h]
    change n⁻¹ * (n * markedRootPoint M S a (↑c⁻¹ : S) * n⁻¹) * n = _
    simp [mul_assoc]
  obtain ⟨q₀, hq₀⟩ := liftIntegralClosedPoint (M.root a).hom.hom f hf q
    (additivePoint S (↑c⁻¹ : S)) hq
  obtain ⟨e, rfl⟩ := additivePoint_surjective R q₀
  have he : f.hom e = (↑c⁻¹ : S) := markedRootPoint_injective M S a <| by
    rw [← hroot, show markedRootPoint M R a e = q from hq₀]
    exact hq
  let v : Rˣ := ⟨d, e, hf (by simp [hd, he]), hf (by simp [hd, he])⟩
  refine ⟨v, Units.ext hd, fun z ↦ ?_⟩
  apply integralPoint_map_injective M.affine f hf
  change ψ (g * markedRootPoint M R a z * g⁻¹) = ψ (markedRootPoint M R b (d * z))
  rw [map_mul, map_mul, map_inv, hroot, hroot, map_mul, hd]
  exact hg (f.hom z)

end IntegralCoordinates

section Torus

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (IntegralAlgebra Integers IntegralMarking IntegralPoints
  TorusValues integerAlgebra torusPoint)

private theorem characterBasis_repr {D : BasedRootDatum.{u}} {ι : Type u} [Fintype ι]
    (b : Module.Basis ι ℤ D.Y) (x : D.X) (i : ι) :
    (characterBasis D b).repr x i = D.datum.toLinearMap x (b i) := by
  classical
  change (b.dualBasis.map D.datum.toPerfPair.symm).repr x i = _
  rw [Module.Basis.map_repr, LinearEquiv.symm_symm]
  exact b.dualBasis_repr (D.datum.toPerfPair x) i

theorem torusBasisCoordinates : TorusBasisCoordinates.{u} := by
  classical
  intro D ι _ b R
  let c := characterBasis D b
  let eval : TorusValues D R →* (ι → Rˣ) :=
    { toFun := fun t i ↦ t (Multiplicative.ofAdd (c i))
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hx (x : D.X) : Multiplicative.ofAdd x =
      ∏ i, Multiplicative.ofAdd (c i) ^ c.repr x i := by
    simpa only [ofAdd_sum, ofAdd_zsmul] using
      congrArg Multiplicative.ofAdd (c.sum_repr x).symm
  have hinj : Function.Injective eval := by
    intro f g h
    apply MonoidHom.ext
    intro x
    change f (Multiplicative.ofAdd x.toAdd) = g (Multiplicative.ofAdd x.toAdd)
    rw [hx, map_prod, map_prod]
    simp only [map_zpow]
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun z : Rˣ ↦ z ^ c.repr x.toAdd i) (congrFun h i)
  have hsurj : Function.Surjective eval := by
    intro u
    let f := c.constr ℤ (fun i ↦ Additive.ofMul (u i))
    refine ⟨f.toAddMonoidHom.toMultiplicativeLeft, ?_⟩
    funext i
    exact congrArg Additive.toMul (c.constr_basis ℤ (fun i ↦ Additive.ofMul (u i)) i)
  let e := MulEquiv.ofBijective eval ⟨hinj, hsurj⟩
  refine ⟨e, fun _ _ ↦ rfl, ?_⟩
  intro u x
  calc
    e.symm u (Multiplicative.ofAdd x) = ∏ i, e.symm u (Multiplicative.ofAdd (c i)) ^
        c.repr x i := by rw [hx x, map_prod]; simp only [map_zpow]
    _ = ∏ i, u i ^ (D.datum.toLinearMap x (b i)) := by
      apply Finset.prod_congr rfl
      intro i _
      have hi : e.symm u (Multiplicative.ofAdd (c i)) = u i :=
        congrFun (e.apply_symm_apply u) i
      rw [hi, characterBasis_repr]

theorem exceptionalCocharacterBases : ExceptionalCocharacterBases.{u} := by
  intro D
  constructor
  · intro h i
    unfold simpleCorootBasis
    exact Module.Basis.mk_apply _ _ i
  · intro h i j
    classical
    let b : Module.Basis D.base.support ℤ D.X :=
      Module.Basis.mk D.base.linearIndepOn_root <| by
        change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.root ∘ ((↑) : D.base.support → D.I)))
        rw [Set.range_comp, Subtype.range_coe, D.base.span_int_root_support, h]
    have hbj : b j = D.datum.root j := by
      dsimp only [b]
      exact Module.Basis.mk_apply _ _ j
    have hi : fundamentalCoweightBasis D h i = D.datum.toLinearMap.flip.toPerfPair.symm
        (b.dualBasis i) := rfl
    rw [hi, ← hbj, ← LinearMap.flip_apply D.datum.toLinearMap]
    exact (congrArg (fun l : Module.Dual ℤ D.X ↦ l (b j))
        (D.datum.toLinearMap.flip.toPerfPair.apply_symm_apply (b.dualBasis i))).trans
      (b.dualBasis_apply_self i j)

attribute [local instance] integerAlgebra

private def integerValuationOnUnits (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (log (normalizedValuation K (u : K)))
  map_one' := by
    change Multiplicative.ofAdd (log (normalizedValuation K 1)) = 1
    rw [map_one, log_one]
    rfl
  map_mul' u v := by
    have hu : normalizedValuation K (u : K) ≠ 0 := by simp
    have hv : normalizedValuation K (v : K) ≠ 0 := by simp
    change Multiplicative.ofAdd (log (normalizedValuation K ((u : K) * (v : K)))) =
      Multiplicative.ofAdd (log (normalizedValuation K (u : K)) +
        log (normalizedValuation K (v : K)))
    rw [map_mul, log_mul hu hv]

private theorem integerValuationOnUnits_surj (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Function.Surjective (integerValuationOnUnits K) := by
  intro n
  obtain ⟨x, hx⟩ := normalizedValuation_surjective K (exp n.toAdd)
  have h₀ : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact exp_ne_zero hx.symm
  use Units.mk0 x h₀
  change Multiplicative.ofAdd (log (normalizedValuation K x)) = n
  rw [hx, log_exp]
  rfl

private theorem integerValuationOnUnits_eq_one (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (u : Kˣ) :
    integerValuationOnUnits K u = 1 ↔ normalizedValuation K (u : K) = 1 := by
  have h : normalizedValuation K (u : K) ≠ 0 := by simp
  change log (normalizedValuation K (u : K)) = 0 ↔ _
  constructor
  · intro hz
    simpa only [exp_log h, exp_zero] using congrArg exp hz
  · intro hz
    rw [hz, log_one]

theorem splitTorusTranslation : SplitTorusTranslation.{u} := by
  classical
  intro K _ _ _ _ D ι _ b
  let R := CommAlgCat.of Integers.{u} K
  obtain ⟨e, he, hcoords⟩ := torusBasisCoordinates D b R
  let del : (ι → (↑R)ˣ) →* Multiplicative D.Y :=
    { toFun := fun u ↦ Multiplicative.ofAdd
        (b.equivFun.symm fun i ↦ (integerValuationOnUnits K (u i)).toAdd)
      map_one' := by
        apply Multiplicative.toAdd.injective
        change b.equivFun.symm (fun i ↦ (integerValuationOnUnits K 1).toAdd) = 0
        simp only [map_one]
        exact map_zero b.equivFun.symm
      map_mul' := fun u v ↦ by
        apply Multiplicative.toAdd.injective
        change b.equivFun.symm (fun i ↦ (integerValuationOnUnits K (u i * v i)).toAdd) =
          b.equivFun.symm (fun i ↦ (integerValuationOnUnits K (u i)).toAdd) +
          b.equivFun.symm (fun i ↦ (integerValuationOnUnits K (v i)).toAdd)
        simp only [map_mul]
        exact map_add b.equivFun.symm _ _ }
  let ν : TorusValues D R →* Multiplicative D.Y :=
    { toFun := fun t ↦ del (e t)
      map_one' := by simp only [map_one]
      map_mul' _ _ := by simp only [map_mul] }
  refine ⟨ν, ?_, ?_, ?_⟩
  · intro y
    choose u hu using fun i : ι ↦ integerValuationOnUnits_surj K
      (Multiplicative.ofAdd (b.equivFun y.toAdd i))
    refine ⟨e.symm u, Multiplicative.toAdd.injective ?_⟩
    change b.equivFun.symm (fun i ↦ (integerValuationOnUnits K (e (e.symm u) i)).toAdd) = _
    rw [e.apply_symm_apply]
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    exact congrArg Multiplicative.toAdd (hu i)
  · intro t x
    let n : ι → ℤ := fun i ↦ (integerValuationOnUnits K (e t i)).toAdd
    have ht : t (Multiplicative.ofAdd x) = ∏ i, (e t i) ^ (D.datum.toLinearMap x (b i)) := by
      simpa only [e.symm_apply_apply] using hcoords (e t) x
    have hn : ∀ i, b.repr (ν t).toAdd i = n i := by
      intro i
      exact congrFun (b.equivFun.apply_symm_apply n) i
    change D.datum.toLinearMap x (ν t).toAdd =
      (integerValuationOnUnits K (t (Multiplicative.ofAdd x))).toAdd
    rw [ht, map_prod, toAdd_prod]
    conv_lhs => rw [← b.sum_repr (ν t).toAdd]
    simp only [map_sum, map_smul, hn, map_zpow, toAdd_zpow, n]
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_comm]
  · intro t
    rw [← Multiplicative.toAdd.injective.eq_iff, ← b.equivFun.injective.eq_iff]
    change b.equivFun (b.equivFun.symm
      (fun i ↦ (integerValuationOnUnits K (e t i)).toAdd)) = b.equivFun 0 ↔ _
    rw [LinearEquiv.apply_symm_apply, map_zero, funext_iff]
    constructor
    · intro h i
      rw [← he, ← integerValuationOnUnits_eq_one]
      exact Multiplicative.toAdd.injective (h i)
    · intro h i
      have hi := (integerValuationOnUnits_eq_one K (e t i)).mpr (by rw [he]; exact h i)
      exact congrArg Multiplicative.toAdd hi

theorem markedTorusLayerConjugation : MarkedTorusLayerConjugation.{u} := by
  intro K _ _ _ _ D M t a z j R g c d
  refine ⟨M.conjugation R t a z, ?_⟩
  have hc : normalizedValuation K c ≠ 0 := by simp [c]
  have hd : exp d = normalizedValuation K c := exp_log hc
  rw [map_mul, sub_eq_add_neg, exp_add, hd]
  exact ⟨mul_le_mul_iff_right₀ (pos_iff_ne_zero.mpr hc),
    mul_lt_mul_iff_right₀ (pos_iff_ne_zero.mpr hc)⟩

theorem foldedTorusFactorValuations : FoldedTorusFactorValuations.{u} := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ hdeg hram σ hσ
  have hv := (ramifiedQuadratic F L hdeg hram).2.1
  have hbase (u : Fˣ) :
      ((log (normalizedValuation L (algebraMap F L (u : F))) : ℤ) : ℚ) / 2 =
        ((integerValuationOnUnits F u).toAdd : ℚ) := by
    change ((log (normalizedValuation L (algebraMap F L (u : F))) : ℤ) : ℚ) / 2 =
      ((log (normalizedValuation F (u : F)) : ℤ) : ℚ)
    rw [hv, log_pow, two_nsmul, Int.cast_add]
    ring
  have hpair (u : Lˣ) :
      (((log (normalizedValuation L (u : L)) : ℤ) : ℚ) / 2,
       ((log (normalizedValuation L (σ (u : L))) : ℤ) : ℚ) / 2) =
      (((integerValuationOnUnits L u).toAdd : ℚ) / 2,
       ((integerValuationOnUnits L u).toAdd : ℚ) / 2) := by
    rw [involutionPreservesValuation σ hσ]
    rfl
  constructor
  · ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(integerValuationOnUnits F u).toAdd, (hbase u).symm⟩
    · rintro ⟨n, rfl⟩
      obtain ⟨u, hu⟩ := integerValuationOnUnits_surj F (Multiplicative.ofAdd n)
      exact ⟨u, by dsimp only; rw [hbase u, hu]; rfl⟩
  · ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(integerValuationOnUnits L u).toAdd, (hpair u).symm⟩
    · rintro ⟨n, rfl⟩
      obtain ⟨u, hu⟩ := integerValuationOnUnits_surj L (Multiplicative.ofAdd n)
      exact ⟨u, by dsimp only; rw [hpair u, hu]; rfl⟩

end Torus

section PointSubgroups

/-- A subgroup defined by positive Borel reduction meets the normalizer in the
integral torus, when the finite representatives retain their labels on reduction. -/
theorem iwahoriNormalizerIntersection : IwahoriNormalizerIntersection := by
  intro G G₀ W _ _ _ K T N hTN red B lift hT hW hN h₁
  ext n
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, han⟩
    obtain ⟨t, w, he⟩ := hN a han
    have htk : (t : G) ∈ K := by
      have h := K.mul_mem a.property (K.inv_mem (lift w).property)
      rwa [he, mul_inv_cancel_right] at h
    let t₀ : K := ⟨t, htk⟩
    have hmul : a = t₀ * lift w := Subtype.ext he
    have htw : red t₀ ∈ B := hT t₀ t.property
    have hw : w = 1 := (hW w).mp <| by
      have h := B.mul_mem (B.inv_mem htw) (show red a ∈ B from ha)
      rwa [hmul, map_mul, inv_mul_cancel_left] at h
    refine ⟨?_, a.property⟩
    change (a : G) ∈ T
    rw [he, hw, h₁, Subgroup.coe_one, mul_one]
    exact t.property
  · rintro ⟨ht, hk⟩
    exact ⟨⟨⟨n, hk⟩, hT ⟨n, hk⟩ ht, rfl⟩, hTN ht⟩

/-- Rational Bruhat coverage and contraction of the root groups into the
Iwahori by normalizer elements suffice for generation. -/
theorem iwahoriNormalizerGeneration : IwahoriNormalizerGeneration := by
  intro G ι _ I N T B X hT hB hbruhat hroot
  let H := I ⊔ N
  have hIH : I ≤ H := le_sup_left
  have hNH : N ≤ H := le_sup_right
  have hX (i : ι) : X i ≤ H := by
    intro x hx
    obtain ⟨t, ht⟩ := hroot i ⟨x, hx⟩
    have htH : (t : G) ∈ H := hNH t.property
    have hh : (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) * (t : G) ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem htH) (hIH ht)) htH
    simpa [mul_assoc] using hh
  have hBH : B ≤ H :=
    hB.trans (sup_le (hT.trans hNH) (iSup_le hX))
  apply top_unique
  intro g _
  obtain ⟨b, c, n, rfl⟩ := hbruhat g
  exact H.mul_mem (H.mul_mem (hBH b.property) (hNH n.property)) (hBH c.property)

/-- Translation quotient of the adjoint point group from the torus
factorization and the simply connected torus image. -/
theorem ordinarySubgroupQuotient : OrdinarySubgroupQuotient := by
  intro Gsc G Y _ _ _ p T ν hν hfactor hstable H Λ
  have hp : p.range.Normal := by
    constructor
    intro g hg a
    rcases hg with ⟨y, rfl⟩
    obtain ⟨x, t, rfl⟩ := hfactor a
    have h₁ := p.range.mul_mem (show p x ∈ p.range from ⟨x, rfl⟩) (hstable t y)
    have h₂ := p.range.mul_mem h₁ (p.range.inv_mem (show p x ∈ p.range from ⟨x, rfl⟩))
    simpa only [mul_inv_rev, mul_assoc] using h₂
  let j : T →* G ⧸ p.range := (QuotientGroup.mk' p.range).comp T.subtype
  have hj : Function.Surjective j := by
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨x, t, rfl⟩ := hfactor a
    refine ⟨t, ?_⟩
    have hx : (QuotientGroup.mk' p.range) (p x) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    change (QuotientGroup.mk' p.range) (t : G) = (QuotientGroup.mk' p.range) (p x * t)
    rw [map_mul, hx, one_mul]
  let l : T →* Y ⧸ Λ := (QuotientGroup.mk' Λ).comp ν
  have hker : j.ker ≤ l.ker := by
    intro t ht
    have ht' : (t : G) ∈ p.range := (QuotientGroup.eq_one_iff _).mp ht
    exact (QuotientGroup.eq_one_iff _).mpr ⟨t, ht', rfl⟩
  let Φ : G ⧸ p.range →* Y ⧸ Λ := (j.liftOfSurjective hj) ⟨l, hker⟩
  have hΦ (t : T) : Φ (j t) = l t := j.liftOfRightInverse_comp_apply _ _ _ _
  let q := Φ.comp (QuotientGroup.mk' p.range)
  have hqt (t : T) : q t = QuotientGroup.mk (ν t) := hΦ t
  have hqp (x : Gsc) : q (p x) = 1 := by
    change Φ ((QuotientGroup.mk' p.range) (p x)) = 1
    rw [show (QuotientGroup.mk' p.range) (p x) = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩,
      map_one]
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨t, rfl⟩ := hν b
    exact ⟨t, hqt t⟩
  have hh : H = q.ker := by
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨x, rfl⟩
        exact hqp x
      · rintro _ ⟨t, ht, rfl⟩
        change q t = 1
        rw [hqt, show ν t = 1 from ht]
        exact (QuotientGroup.eq_one_iff _).mpr Λ.one_mem
    · intro g hg
      obtain ⟨x, t, rfl⟩ := hfactor g
      change q (p x * t) = 1 at hg
      rw [map_mul, hqp, one_mul, hqt, QuotientGroup.eq_one_iff] at hg
      obtain ⟨s, hs, hsν⟩ := hg
      have hunit : t * s⁻¹ ∈ ν.ker := by
        change ν (t * s⁻¹) = 1
        rw [map_mul, map_inv, hsν, mul_inv_cancel]
      have hPH : p.range ≤ H := le_sup_left
      have hUH : ν.ker.map T.subtype ≤ H := le_sup_right
      have hs' : (s : G) ∈ H := hPH hs
      have hx : p x ∈ H := hPH ⟨x, rfl⟩
      have ht : (↑(t * s⁻¹) : G) ∈ H := hUH ⟨_, hunit, rfl⟩
      have h := H.mul_mem (H.mul_mem hx ht) hs'
      simpa [mul_assoc] using h
  have : H.Normal := hh ▸ inferInstance
  refine ⟨‹H.Normal›, QuotientGroup.liftEquiv H hq hh, ?_⟩
  intro t
  rw [QuotientGroup.liftEquiv_mk]
  exact hqt t

end PointSubgroups

section LocalPointGroups

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.IntegralSemisimpleModel (Integers integerAlgebra IntegralPoints)
open Specs.ExceptionalIwahoriImageComparison (markedBorelReduction integralUnitTorus)
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Arithmetic.ExceptionalIwahoriImageComparison (splitMarkedNormalizerPresentation
  foldedMarkedNormalizerPresentation markedPositiveBorelSubgroup markedIwahoriNormalizerIntersection
  splitIwahoriGeneration foldedIwahoriGeneration)
open Arithmetic.ExceptionalMarkedRootDescent (markedFibreExists)
open Arithmetic.ExceptionalValuedTorusNormalizer (markedFibreNormalizer)
open private normalizerOfMarkedFibre markedGroundEquiv markedGroundEquiv_apply
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
theorem splitLocalIwahori : SplitLocalIwahori.{u} := by
  intro K _ _ _ _ D M C index _ b word hword hprod R
  let F := normalizerOfMarkedFibre C
  haveI := F.torusComm
  let e := markedGroundEquiv C
  obtain ⟨N, hN, hw, hsurj, hq, hker⟩ := splitMarkedNormalizerPresentation F b word hword hprod
  have hp (n : 𝟙_ (SchemeOver K) ⟶ F.identification.normalizer.group.X) :
      F.point n = e (n ≫ F.identification.normalizer.inclusion.hom.hom) := by
    rw [F.point_eq, markedGroundEquiv_apply]
    simp only [Specs.ExceptionalIwahoriImageComparison.markedGroundPoint,
      Specs.ExceptionalMarkedRootDescent.markedFibrePoint, Category.assoc]
    rfl
  have hmatch (g : 𝟙_ (SchemeOver K) ⟶ C.realization.pinned.pair.G.val.X) :
      e g ∈ N.normalizer ↔ Normalizes C.realization.pinned.pair.T.inclusion g := by
    rw [hN]
    constructor
    · rintro ⟨n, hn⟩
      exact (F.identification.representsNormalizer _ _).mpr ⟨n, e.injective ((hp n).symm.trans hn)⟩
    · intro hg
      obtain ⟨n, hn⟩ := (F.identification.representsNormalizer _ _).mp hg
      exact ⟨n, (hp n).trans (congrArg e hn)⟩
  let κ := IsLocalRing.ResidueField (valuation K).valuationSubring
  obtain ⟨C₀⟩ := markedFibreExists M κ
  obtain ⟨B₀, hB₀⟩ := markedPositiveBorelSubgroup C₀
  have hmain (n : N.normalizer) : ∃ m, F.point m = (n : IntegralPoints M.group R) ∧
      F.label m = N.label n := by
    obtain ⟨m, hm⟩ : (n : IntegralPoints M.group R) ∈ F.point.range := hN ▸ n.property
    refine ⟨m, hm, ?_⟩
    have hmN : F.point m ∈ N.normalizer := hN.symm ▸ ⟨m, rfl⟩
    have hz : (⟨F.point m, hmN⟩ : N.normalizer) = n := Subtype.ext hm
    simpa only [hz] using (hq m hmN).symm
  have hint := markedIwahoriNormalizerIntersection F (MonoidHom.id _) N
    (fun n => hN ▸ n.property) C₀ B₀ hB₀
  obtain ⟨N', hN', hgen⟩ := splitIwahoriGeneration C B₀
  have he : N' = N.normalizer := by
    ext g
    obtain ⟨g, rfl⟩ := e.surjective g
    exact (markedGroundEquiv_apply C g ▸ hN' g).trans (hmatch g).symm
  have hgen' : (markedBorelReduction M.group B₀).comap (MonoidHom.id _) ⊔ N.normalizer = ⊤ := by
    rw [← he]
    simpa using hgen
  let P : LocalIwahori (M := M) (MonoidHom.id _) D.datum.weylGroup :=
    ⟨N, C₀, B₀, hB₀, hint, hgen'⟩
  exact ⟨P, F, fun g => markedGroundEquiv_apply C g ▸ hmatch g, hmain, hw, hsurj, hker⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
theorem foldedLocalIwahori : FoldedLocalIwahori.{u} := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ D M C l Q hQ ω d σ hd hσ hr e W hsym horth
    b hb ns ps hmatch hn hp word hw hprod R
  have hval := (ramifiedQuadratic k K hd hr).2.1
  obtain ⟨F⟩ := markedFibreNormalizer K M
  obtain ⟨j, N, S, hj, hjp, hS, hNS, hNT, hT, hN, hword, hker, hproj⟩ :=
    foldedMarkedNormalizerPresentation C F hQ d σ hd hσ hsym horth hval b hb word hw hprod
  let κ := IsLocalRing.ResidueField (valuation K).valuationSubring
  obtain ⟨C₀⟩ := markedFibreExists M κ
  obtain ⟨B₀, hB₀⟩ := markedPositiveBorelSubgroup C₀
  have hint := markedIwahoriNormalizerIntersection F j N
    (fun n => by
      obtain ⟨m, hm, _⟩ := hN n
      exact ⟨m, hm⟩) C₀ B₀ hB₀
  obtain ⟨j', S', V, hj'p, _, _, hV, hgen⟩ :=
    foldedIwahoriGeneration C hQ d σ hd hσ hval hsym b hb ns ps hmatch hn hp B₀
  have he : j' = j := MonoidHom.ext fun g => (hj'p g).trans (hjp g).symm
  have hN' : SubgroupSections V.normalizer (𝟙_ (SchemeOver k)) = N.normalizer := by
    ext g
    exact (V.normalizerProperty _ _).symm.trans ((hV g).trans (hNT g).symm)
  rw [he, hN'] at hgen
  let P : LocalIwahori (M := M) j W := ⟨N, C₀, B₀, hB₀, hint, hgen⟩
  exact ⟨j, P, F, S, hj, hjp, hS, hNS, hNT, hT, hN, hword, hker, hproj⟩

end LocalPointGroups

section CentralPointGroups

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom pointHom)
open Arithmetic.ExceptionalIwahoriImageComparison (centralCoverWeylComparison
  splitCentralPointComparison splitTorusPointPreimage splitIwahoriCoverComparison
  markedOrdinaryIwahoriComparison)
open Arithmetic.ExceptionalMarkedRootDescent (markedFibreExists)
open private markedGroundEquiv markedGroundEquiv_apply cover_simple
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private simple_reflections_generate from LinearAlgebraicGroups.Classification.NormalizerComparison

attribute [local instance] integerAlgebra

private theorem simpleWeylWords (D : BasedRootDatum.{u}) :
    ∃ word : D.datum.weylGroup → List D.I,
      (∀ w, ∀ a ∈ word w, a ∈ D.base.support) ∧
      ∀ w, ((word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = w := by
  haveI := D.finiteRoots
  haveI := D.reduced
  let s := RootPairing.weylGroup.ofIdx D.datum
  have hs (a) : (s a)⁻¹ = s a :=
    Subtype.ext (RootPairing.Equiv.reflection_inv D.datum a)
  have hw (w : D.datum.weylGroup) :
      ∃ l : List D.I, (∀ a ∈ l, a ∈ D.base.support) ∧ (l.map s).prod = w := by
    have h : w ∈ Subgroup.closure (Set.range fun a : D.base.support => s a.val) := by
      rw [simple_reflections_generate D.datum D.base]
      exact Subgroup.mem_top _
    induction h using Subgroup.closure_induction with
    | mem _ h =>
      obtain ⟨a, rfl⟩ := h
      exact ⟨[a.val], by simpa using a.property, by simp⟩
    | one => exact ⟨[], by simp, rfl⟩
    | mul _ _ _ _ hx hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      exact ⟨l ++ m, fun a ha => (List.mem_append.mp ha).elim (hl a) (hm a),
        by rw [List.map_append, List.prod_append]⟩
    | inv _ _ hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine ⟨l.reverse, fun a ha => hl a (List.mem_reverse.mp ha), ?_⟩
      rw [List.map_reverse, List.prod_inv_reverse, List.map_map]
      simp only [Function.comp_def, hs]
  choose word hword hlabel using hw
  exact ⟨word, hword, hlabel⟩

private theorem pushCocharacter_range {D E : BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (hD : D.datum.corootSpan ℤ = ⊤) :
    Set.range c.pushCocharacter = (E.datum.corootSpan ℤ : Set E.Y) := by
  have h : (D.datum.corootSpan ℤ).map c.pushCocharacter = E.datum.corootSpan ℤ := by
    change (Submodule.span ℤ (Set.range D.datum.coroot)).map c.pushCocharacter =
      Submodule.span ℤ (Set.range E.datum.coroot)
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨c.rootEquiv a, (c.coroots a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨c.rootEquiv.symm a, (c.coroots (c.rootEquiv.symm a)).trans
        (congrArg E.datum.coroot (c.rootEquiv.apply_symm_apply a))⟩
  rw [hD, Submodule.map_top] at h
  exact congrArg (fun S : Submodule ℤ E.Y => (S : Set E.Y)) h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem splitOrdinaryLocalIwahori : SplitOrdinaryLocalIwahori.{u} := by
  classical
  intro K _ _ _ _ D E M A c hD hE R p
  haveI := D.finiteRoots
  haveI := E.finiteRoots
  haveI : Fintype D.base.support := Fintype.ofFinite _
  haveI : Fintype E.base.support := Fintype.ofFinite _
  let b := Specs.ExceptionalValuedTorusNormalizer.simpleCorootBasis D hD
  let b' := Specs.ExceptionalValuedTorusNormalizer.fundamentalCoweightBasis E hE
  obtain ⟨C⟩ := markedFibreExists M K
  obtain ⟨C'⟩ := markedFibreExists A K
  obtain ⟨e, he, _, _⟩ := centralCoverWeylComparison c hE
  obtain ⟨word, hw, hq⟩ := simpleWeylWords D
  let word' (w : E.datum.weylGroup) := (word (e.symm w)).map c.rootEquiv
  have hw' (w) (a) (ha : a ∈ word' w) : a ∈ E.base.support := by
    change a ∈ (word (e.symm w)).map c.rootEquiv at ha
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp ha
    rw [← heq]
    exact (cover_simple c i).mp (hw (e.symm w) i hi)
  have hq' (w) : ((word' w).map (RootPairing.weylGroup.ofIdx E.datum)).prod = w := by
    have h := congrArg e (hq (e.symm w))
    rw [e.apply_symm_apply] at h
    simpa only [word', List.map_map, Function.comp_def, map_list_prod, he] using h
  obtain ⟨P, _, hN, _, hwP, hv, _⟩ := splitLocalIwahori C b word hw hq
  obtain ⟨P₁, _, hN', _, hwP', hv', _⟩ := splitLocalIwahori C' b' word' hw' hq'
  let P' := P₁.relabel e.symm
  have hwords (w) : (P.normalizer.word w).map c.rootEquiv = P'.normalizer.word w := by
    change _ = P₁.normalizer.word (e.symm.symm w)
    rw [hwP, hwP']
    simp [word']
  obtain ⟨hI, hpreI⟩ :=
    splitIwahoriCoverComparison c C C' P.residueFibre P'.residueFibre
      P.residueBorel P'.residueBorel P.borel_eq P'.borel_eq
  let f := C.groupIso.inv ≫ (fibre K).map c.map ≫ C'.groupIso.hom
  let q := pointHom f (𝟙_ (SchemeOver K))
  let j := markedGroundEquiv C
  let j' := markedGroundEquiv C'
  obtain ⟨hcomp, _, hpreN, hnormal⟩ := splitCentralPointComparison c C C'
  have hcomm (g) : j' (q g) = p (j g) := by
    rw [markedGroundEquiv_apply, markedGroundEquiv_apply]
    exact hcomp g
  have hpreT : P'.normalizer.torus.comap p = P.normalizer.torus := by
    ext g
    rw [Subgroup.mem_comap, P'.normalizer.torusPoints, P.normalizer.torusPoints]
    constructor
    · exact splitTorusPointPreimage c C C' g
    · rintro ⟨t, ht⟩
      refine ⟨t.comp c.pullCharacter.toAddMonoidHom.toMultiplicative, ?_⟩
      change p g = _
      change g = _ at ht
      rw [ht]
      exact c.marking.2.2 R t
  have hpreN' : P'.normalizer.normalizer.comap p = P.normalizer.normalizer := by
    ext g
    obtain ⟨g, rfl⟩ := j.surjective g
    change p (j g) ∈ P₁.normalizer.normalizer ↔ j g ∈ P.normalizer.normalizer
    rw [← hcomm, markedGroundEquiv_apply, (show j g = _ from markedGroundEquiv_apply C g),
      hN', hN]
    exact hpreN g
  have hnormal' : p.range.Normal := by
    have htop : j.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr j.surjective
    have heq : q.range.map j'.toMonoidHom = p.range := by
      rw [← MonoidHom.range_comp, show j'.toMonoidHom.comp q = p.comp j.toMonoidHom from
        MonoidHom.ext hcomm, MonoidHom.range_comp, htop, Subgroup.map_top]
    exact heq ▸ hnormal.map j'.toMonoidHom j'.surjective
  refine ⟨P, P', ?_, hv, hv', ?_, ?_⟩
  · simpa only [LocalIwahori.iwahori, LocalIwahori.relabel, Subgroup.comap_id] using hpreI
  · have hsurj : Function.Surjective (fun t : P.normalizer.torus =>
        (P.normalizer.translation t).toAdd) := fun y => by
      obtain ⟨t, ht⟩ := hv (Multiplicative.ofAdd y)
      exact ⟨t, congrArg Multiplicative.toAdd ht⟩
    rw [show (fun t : P.normalizer.torus => c.pushCocharacter (P.normalizer.translation t).toAdd) =
        c.pushCocharacter ∘ (fun t => (P.normalizer.translation t).toAdd) from rfl,
      Set.range_comp, hsurj.range_eq, Set.image_univ]
    exact pushCocharacter_range c hD
  · apply markedOrdinaryIwahoriComparison c _ _ P.normalizer P'.normalizer p
      (fun _ _ h => h) (fun _ => rfl) hwords hpreT hpreN' hnormal'
      P.iwahori P'.iwahori P.generation P'.generation
    simpa only [LocalIwahori.iwahori, LocalIwahori.relabel, Subgroup.comap_id] using hI

end CentralPointGroups

section FoldedCentralPointGroups

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Integers integerAlgebra IntegralPoints TorusValues Model torusPoint)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom pointHom)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre SimpleRootOrbit TransportedOrbit
  transportedLabels pinnedDiagram)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutation fixedWeylGroup)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Arithmetic.ExceptionalIwahoriImageComparison (centralCoverWeylComparison
  pinnedCentralCoverComparison foldedRootWordCompatibility foldedIwahoriImageAndPreimage
  splitTorusPointPreimage markedOrdinaryIwahoriComparison)
open Arithmetic.ExceptionalMarkedRootDescent (markedFibreExists)
open Arithmetic.ExceptionalValuedTorusNormalizer (markedPinnedDiagramAction)
open private cover_simple enumerates_map
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

attribute [local instance] integerAlgebra

private def coverSimpleIndex {D E : BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (i : D.base.support) : E.base.support :=
  ⟨c.rootEquiv i.val, (cover_simple c i.val).mp i.property⟩

private def coverOrbit {D E : BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (o : SimpleRootOrbit D) : SimpleRootOrbit E :=
  (coverSimpleIndex c o.1, o.2.map (coverSimpleIndex c))

private theorem coverOrbit_roots {D E : BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (o : SimpleRootOrbit D) :
    (coverOrbit c o).roots = o.roots.map c.rootEquiv := by
  obtain ⟨a, b⟩ := o
  cases b <;> rfl

private theorem coverWord_roots {D E : BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (w : List (SimpleRootOrbit D)) :
    (w.map (coverOrbit c)).flatMap SimpleRootOrbit.roots =
      (w.flatMap SimpleRootOrbit.roots).map c.rootEquiv := by
  induction w with
  | nil => rfl
  | cons o w ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append, coverOrbit_roots, ih]

private theorem cover_pairing {D E : BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) (i j : D.I) :
    E.datum.pairing (c.rootEquiv i) (c.rootEquiv j) = D.datum.pairing i j := by
  simpa only [c.roots, c.coroots, RootPairing.root_coroot_eq_pairing] using
    (c.pairing (E.datum.root (c.rootEquiv i)) (D.datum.coroot j)).symm

set_option backward.isDefEq.respectTransparency false in
theorem pinnedSimpleOrbitCriterion : PinnedSimpleOrbitCriterion.{u} := by
  intro k K _ _ _ D M C l Q hQ G B T d σ o e
  have hpin := (markedPinnedDiagramAction C.realization hQ (d.outer σ)).1
  have h (a b : D.base.support) :
      Specs.Pinning.transportCharacter (pinnedDiagram d σ).asIso.hom.torus
        (C.realization.datumIso.val.indexEquiv a.val).val =
        (C.realization.datumIso.val.indexEquiv b.val).val ↔ simplePermutation D e a = b := by
    change Specs.Pinning.transportCharacter (l (d.outer σ)).asIso.hom.torus
      (C.realization.simpleRoot a).val.val = (C.realization.simpleRoot b).val.val ↔ _
    rw [hpin a]
    exact ⟨fun he => Subtype.ext (C.realization.datumIso.val.indexEquiv.injective (Subtype.ext he)),
      fun hb => congrArg (fun i => (C.realization.simpleRoot i).val.val) hb⟩
  obtain ⟨a, b⟩ := o
  cases b with
  | none => exact h a a
  | some b => exact and_congr_right fun _ => and_congr (h a b) (h b a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
theorem foldedOrdinaryLocalIwahori : FoldedOrdinaryLocalIwahori.{u} := by
  classical
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ D E M A c hD hE C C' l l' Q Q' hQ hQ' ω ω' d d' σ
    hd hσ hr e e' W hdiag hsym horth ns ps hmatch hn hp word hw hprod R
  haveI := D.finiteRoots
  haveI := E.finiteRoots
  let b := Specs.ExceptionalValuedTorusNormalizer.simpleCorootBasis D hD
  let b' := Specs.ExceptionalValuedTorusNormalizer.fundamentalCoweightBasis E hE
  have hperm (i : D.base.support) :
      coverSimpleIndex c (simplePermutation D e i) =
        simplePermutation E e' (coverSimpleIndex c i) := Subtype.ext (hdiag i.val)
  have hsym' (a b : E.I) : E.datum.pairing a b = E.datum.pairing b a := by
    obtain ⟨a, rfl⟩ := c.rootEquiv.surjective a
    obtain ⟨b, rfl⟩ := c.rootEquiv.surjective b
    rw [cover_pairing, cover_pairing, hsym]
  have horth' (i' : E.base.support) (hi' : simplePermutation E e' i' ≠ i') :
      E.datum.pairing (simplePermutation E e' i').val i'.val = 0 := by
    obtain ⟨a, ha⟩ := c.rootEquiv.surjective i'.val
    let i : D.base.support := ⟨a, (cover_simple c a).mpr (ha ▸ i'.property)⟩
    have hi : coverSimpleIndex c i = i' := Subtype.ext ha
    rw [← hi, ← hperm] at hi' ⊢
    exact (cover_pairing c _ _).trans (horth i (fun h => hi' (congrArg (coverSimpleIndex c) h)))
  have hmatchOrbit (o : SimpleRootOrbit D) (ho : o.Matches C (pinnedDiagram d.data σ)) :
      (coverOrbit c o).Matches C' (pinnedDiagram d'.data σ) := by
    have h := (pinnedSimpleOrbitCriterion C hQ d.data σ o).mp ho
    apply (pinnedSimpleOrbitCriterion C' hQ' d'.data σ (coverOrbit c o)).mpr
    obtain ⟨a, b⟩ := o
    cases b with
    | none =>
      change simplePermutation D e a = a at h
      exact (hperm a).symm.trans (congrArg (coverSimpleIndex c) h)
    | some b =>
      obtain ⟨hp, ha, hb⟩ := h
      exact ⟨(cover_pairing c a b).trans hp,
        (hperm a).symm.trans (congrArg (coverSimpleIndex c) ha),
        (hperm b).symm.trans (congrArg (coverSimpleIndex c) hb)⟩
  let mapBlock (a : TransportedOrbit D) : TransportedOrbit E :=
    (coverOrbit c a.1, a.2.map (coverOrbit c))
  let ns' := ns.map mapBlock
  let ps' := ps.map mapBlock
  have hcorrespond (l : List (TransportedOrbit D)) :
      l.Forall₂ (fun b b' => b.1.roots.map c.rootEquiv = b'.1.roots ∧
        (b.2.flatMap SimpleRootOrbit.roots).map c.rootEquiv =
          b'.2.flatMap SimpleRootOrbit.roots) (l.map mapBlock) := by
    induction l with
    | nil => exact .nil
    | cons a l ih => exact .cons ⟨(coverOrbit_roots c a.1).symm, (coverWord_roots c a.2).symm⟩ ih
  have hmatch' (a : TransportedOrbit E) (ha : a ∈ ns' ++ ps') :
      a.1.Matches C' (pinnedDiagram d'.data σ) ∧
      ∀ o ∈ a.2, o.Matches C' (pinnedDiagram d'.data σ) := by
    have ha' : a ∈ (ns ++ ps).map mapBlock := by simpa only [List.map_append] using ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨hfirst, hrest⟩ := hmatch b hb
    refine ⟨hmatchOrbit b.1 hfirst, ?_⟩
    intro o ho
    change o ∈ b.2.map (coverOrbit c) at ho
    obtain ⟨o₀, ho₀, heq⟩ := List.mem_map.mp ho
    rw [← heq]
    exact hmatchOrbit o₀ (hrest o₀ ho₀)
  obtain ⟨eqW, eqSimple, _, hfixed⟩ := centralCoverWeylComparison c hE
  obtain ⟨eqFixed, heqFixed⟩ := hfixed e e' hdiag
  let word' (w : fixedWeylGroup E e') := (word (eqFixed.symm w)).map (coverOrbit c)
  have hw' (w) (o) (ho : o ∈ word' w) : o.Matches C' (pinnedDiagram d'.data σ) := by
    change o ∈ (word (eqFixed.symm w)).map (coverOrbit c) at ho
    obtain ⟨o₀, ho₀, heq⟩ := List.mem_map.mp ho
    rw [← heq]
    exact hmatchOrbit o₀ (hw _ o₀ ho₀)
  have hprod' (w) : (((word' w).flatMap SimpleRootOrbit.roots).map
      (RootPairing.weylGroup.ofIdx E.datum)).prod = w.val := by
    have h := congrArg eqW (hprod (eqFixed.symm w))
    rw [← heqFixed, eqFixed.apply_symm_apply] at h
    simpa only [word', coverWord_roots, List.map_map, Function.comp_def, map_list_prod, eqSimple] using h
  let χ := c.pullCharacter.toAddMonoidHom.toMultiplicative
  have hns := (foldedRootWordCompatibility c.map c.rootEquiv χ c.marking c.reflections σ
    ns ns' (hcorrespond ns)).1
  have hps := (foldedRootWordCompatibility c.map c.rootEquiv χ c.marking c.reflections σ
    ps ps' (hcorrespond ps)).1
  obtain ⟨hn', hp'⟩ : Specs.OrderedRootProducts.Enumerates (ns'.flatMap transportedLabels)
        {a | ¬E.base.IsPos a} ∧ Specs.OrderedRootProducts.Enumerates (ps'.flatMap transportedLabels)
        {a | E.base.IsPos a} := by
    rw [← hns, ← hps]
    exact enumerates_map c.rootEquiv c.marking.1 _ _ hn hp
  obtain ⟨j, P, _, _, hj, hjp, _, _, hN, hT, _, hword, _, _⟩ :=
    foldedLocalIwahori C hQ d σ hd hσ hr hsym horth b (Or.inl ⟨hD, rfl⟩)
      ns ps hmatch hn hp word hw hprod
  obtain ⟨j', P₁, _, _, hj', hj'p, _, _, hN', hT', _, hword', _, _⟩ :=
    foldedLocalIwahori C' hQ' d' σ hd hσ hr hsym' horth' b' (Or.inr ⟨hE, rfl⟩) ns' ps' hmatch'
      hn' hp' word' hw' hprod'
  let P' := P₁.relabel eqFixed.symm
  have hwords (w) : (P.normalizer.word w).map c.rootEquiv = P'.normalizer.word w := by
    change _ = P₁.normalizer.word (eqFixed.symm.symm w)
    rw [hword, hword', MulEquiv.symm_symm]
    simp only [word', eqFixed.symm_apply_apply, coverWord_roots]
  obtain ⟨f, _, _, hf, _, _, _, hpreT, hpreN, hnormal, _, hfg⟩ :=
    pinnedCentralCoverComparison c hE C C' hQ hQ' d d' hd σ hσ hdiag
  let p := pointHom f (𝟙_ (SchemeOver k))
  have hcomm (g) : j' (p g) = integralPointHom c.map R (j g) := by
    rw [hj'p, hjp]
    exact hfg g
  have hTpre : P'.normalizer.torus.comap p = P.normalizer.torus := by
    ext g
    exact (hT' (p g)).trans ((hpreT g).trans (hT g).symm)
  have hNpre : P'.normalizer.normalizer.comap p = P.normalizer.normalizer := by
    ext g
    exact (hN' (p g)).trans ((hpreN g).trans (hN g).symm)
  obtain ⟨CK⟩ := markedFibreExists M K
  obtain ⟨CK'⟩ := markedFibreExists A K
  obtain ⟨i, i', _, _, hi, hi', hpreI, hI, _⟩ :=
    foldedIwahoriImageAndPreimage M A c.map c.rootEquiv χ c.marking c.characterIndex c.reflections
      (splitTorusPointPreimage c CK CK') C C' d.data d'.data f hfg hd σ hσ hsym hsym'
      ns ps ns' ps' hmatch hmatch' (hcorrespond ns) (hcorrespond ps) hn' hp'
      P.residueFibre P'.residueFibre P.residueBorel P'.residueBorel P.borel_eq P'.borel_eq
  have heq : i = j := MonoidHom.ext fun g => (hi g).trans (hjp g).symm
  have heq' : i' = j' := MonoidHom.ext fun g => (hi' g).trans (hj'p g).symm
  rw [heq, heq'] at hpreI hI
  refine ⟨f, j, j', P, P', hf, hjp, hj'p, hcomm, hpreI, ?_⟩
  exact markedOrdinaryIwahoriComparison c j j' P.normalizer P'.normalizer p hj' hcomm hwords
    hTpre hNpre hnormal P.iwahori P'.iwahori P.generation P'.generation hI

end FoldedCentralPointGroups

section NormalizerAction

open CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (IntegralPoints Integers integerAlgebra torusPoint
  integralPointFunctor cocharacter Model IntegralMarking IntegralAlgebra TorusValues)
open Specs.ExceptionalMarkedRootDescent (markedRootPoint markedWeylWord weylWordPerm markedWall
  wallMatrix rankOneMatrixWord)
open Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion fixedWeylGroup
  orbitProjection simplePermutation FibreNormalizer)
open Specs.ExceptionalIwahoriImageComparison (integralUnitTorus)
open Specs.IntegralRootRelations (diagonal)
open Arithmetic.ExceptionalMarkedRootDescent (integralWeylWordTransport integralUnitValuation
  wallMatrixRelations markedOrthogonalRankOneCommutation)
open Arithmetic.ExceptionalValuedTorusNormalizer (splitApartmentAction foldedWeylLinearAction
  basedPermutation fibreNormalizerTorusAction splitTranslationAction)
open Arithmetic.ExceptionalIwahoriImageComparison (iwahoriPreservedByLayerAction)
open private normalizedValuation_le_iff from LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private markedWeylWord_map markedTorusPointHom markedTorusPointHom_apply wallMatrix_val
  from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private fibreNormalizerPoint_injective localNormalizer_unitKernel splitMarkedNormalizerWord
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

attribute [local instance] integerAlgebra

private theorem weylWord_index {D : BasedRootDatum.{u}} (l : List D.I) :
    weylWordPerm l = ((l.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val.indexEquiv := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change D.datum.reflectionPerm a * weylWordPerm l = _
    rw [ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedNormalizerRootLayers : MarkedNormalizerRootLayers.{u} := by
  intro K _ _ _ _ D M G W _ _ j N q hword R x v n a b d
  let t := N.torusPart n
  let l := N.word (N.label n)
  let m := N.lift (N.label n)
  obtain ⟨s, hs⟩ := (N.torusPoints t).mp t.property
  obtain ⟨e, he⟩ := integralWeylWordTransport M l a
  let c₀ := s (Multiplicative.ofAdd (D.datum.root b))
  let eK := Units.map (algebraMap Integers.{u} K).toMonoidHom e
  let c := c₀ * eK
  have hn : j n = j t * j m := by
    rw [← map_mul]
    congr 1
    change (n : G) = (n : G) * (m : G)⁻¹ * (m : G)
    exact (inv_mul_cancel_right _ _).symm
  have hb : weylWordPerm l a = b := by
    change weylWordPerm (N.word (N.label n)) a =
      (q (N.label n)).val.indexEquiv a
    rw [weylWord_index, hword]
  have hv : v (c : K) = exp d := by
    have he₀ : v (eK : K) = 1 := by
      change Specs.ExceptionalMarkedRootDescent.normalizedValuation K
        (algebraMap Integers.{u} K (e : Integers.{u})) = 1
      simpa only [mul_one, map_one] using integralUnitValuation K e 1
    change v (((c₀ : K) * (eK : K))) = exp d
    rw [map_mul, he₀, mul_one]
    have hd := N.characterLog t s hs (D.datum.root b)
    change d = log (v (c₀ : K)) at hd
    rw [hd, exp_log ((map_ne_zero v).mpr c₀.ne_zero)]
  refine ⟨c, hv, fun u => ⟨?_, ?_⟩⟩
  · calc
      j n * x a u * (j n)⁻¹ = j t * (j m * x a u * (j m)⁻¹) * (j t)⁻¹ := by
        rw [hn]
        group
      _ = j t * x b ((eK : K) * u) * (j t)⁻¹ := by
        rw [N.lift_point]
        apply congrArg (fun y => j t * y * (j t)⁻¹)
        change _ = x b (algebraMap Integers.{u} R (e : Integers.{u}) * u)
        rw [← hb]
        exact he R u
      _ = x b ((c : K) * u) := by
        rw [hs]
        exact (M.conjugation R s b ((eK : K) * u)).trans (by
          change x b ((c₀ : K) * ((eK : K) * u)) = x b (((c₀ : K) * (eK : K)) * u)
          rw [mul_assoc])
  · intro m₀
    rw [show -(m₀ - d) = d + -m₀ by omega, exp_add, map_mul, hv]
    have hpos : 0 < exp d := pos_iff_ne_zero.mpr exp_ne_zero
    exact ⟨(mul_le_mul_iff_right₀ hpos).symm, (mul_lt_mul_iff_right₀ hpos).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
theorem markedNormalizerApartment : MarkedNormalizerApartment.{u} := by
  classical
  intro K _ _ _ _ D M F index _ b G W _ _ j N q hq hpoints r V
  letI := F.torusComm
  let A := (𝟙_ (SchemeOver K) ⟶ F.identification.normalizer.group.X)
  choose f hf hlabel using hpoints
  let e : N.normalizer →* A := MonoidHom.mk' f (fun n m =>
    fibreNormalizerPoint_injective F (by rw [hf, map_mul, hf, hf, ← map_mul]; rfl))
  have he (n) : F.point (e n) = j n := hf n
  have hqE (n) : F.label (e n) = q (N.label n) := hlabel n
  obtain ⟨T, ν, ρ, p, a, _, _, _, hka, htor, hlog, _, hright, hleft, hact, hind, _⟩ :=
    splitApartmentAction F b
  let J := (((integralPointFunctor M.group).map (valuationRingInclusion K)).hom.range).comap F.point
  have hν (t : N.torus) (m : F.label.ker) (h : F.point m.val = j t) :
      ν (T.symm m) = N.translation t := by
    have hm := htor (T.symm m)
    rw [T.apply_symm_apply, h] at hm
    apply Multiplicative.toAdd.injective
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext x
    exact (hlog (T.symm m) x).trans (N.characterLog t (T.symm m) hm x).symm
  have hJ (w : W) : e (N.lift w) ∈ J := by
    let R := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
    refine ⟨markedWeylWord M.toIntegralMarking R (N.word w), ?_⟩
    rw [he, N.lift_point]
    exact markedWeylWord_map M.toIntegralMarking (valuationRingInclusion K) (N.word w)
  have hpart (n : N.normalizer) : (p (e n)).left = N.translation (N.torusPart n) := by
    let m := N.lift (N.label n)
    have hr : F.label (e n) = F.label (e m) := by
      rw [hqE, hqE, N.lift_label]
    rw [hind (e n) (e m) (hJ (N.label n)) hr]
    apply hν
    rw [map_mul, map_inv, he, he, ← map_inv, ← map_mul]
    rfl
  let h : V ≃ᵃ[ℚ] V := AffineEquiv.homothetyUnitsMulHom (0 : V) r
  let α := (MulAut.conj h).toMonoidHom.comp (a.comp e)
  have hk (n : N.normalizer) : α n = 1 ↔ p (e n) = 1 := by
    change (MulAut.conj h) (a (e n)) = 1 ↔ p (e n) = 1
    rw [← (MulAut.conj h).map_one, (MulAut.conj h).injective.eq_iff]
    change e n ∈ a.ker ↔ e n ∈ p.ker
    rw [hka]
  refine ⟨α, ?_, ?_, ?_⟩
  · rw [← localNormalizer_unitKernel N]
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hp : p (e n) = 1 := (hk n).mp hn
      have h1 : N.label n = 1 := by
        apply hq
        rw [← hqE, ← hright, hp, map_one]
        rfl
      let t : N.torus := ⟨n, (N.labelKernel n).mp h1⟩
      have hem : F.label (e n) = 1 := by rw [hqE, h1, map_one]
      let m : F.label.ker := ⟨e n, hem⟩
      have hv := hν t m (he n)
      have hm : (T (T.symm m)).val = e n := congrArg Subtype.val (T.apply_symm_apply m)
      have hzero := hleft (T.symm m)
      rw [hm, hp] at hzero
      exact ⟨t, hv.symm.trans hzero.symm, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      let n : N.normalizer := ⟨t, N.torus_le t.property⟩
      have h1 : N.label n = 1 := (N.labelKernel n).mpr t.property
      have hem : F.label (e n) = 1 := by rw [hqE, h1, map_one]
      let m : F.label.ker := ⟨e n, hem⟩
      have hv := hν t m (he n)
      have hm : (T (T.symm m)).val = e n := congrArg Subtype.val (T.apply_symm_apply m)
      refine ⟨n, (hk n).mpr ?_, rfl⟩
      apply SemidirectProduct.ext
      · rw [← hm, hleft, hv]
        exact ht
      · rw [hright, hem]
        rfl
  · intro n x
    change h (a (e n) (h.symm x)) = _
    have h₁ (y : V) : h y = (r : ℚ) • y := by
      simp [h, AffineMap.homothety_apply]
    have h₂ : h.symm x = (↑r⁻¹ : ℚ) • x := by
      simp [h, AffineMap.homothety_apply]
    rw [h₁, h₂, hact, hqE, hpart, smul_add, LinearEquiv.map_smul, smul_smul,
      Units.mul_inv, one_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · intro R n m hm hmI t ht χ
    have hsame : F.label (e n) = F.label m := (hqE n).trans hm.symm
    let z : F.label.ker := ⟨e n * m⁻¹, by
      change F.label (e n * m⁻¹) = 1
      rw [map_mul, map_inv, hsame, mul_inv_cancel]⟩
    have hz : ν (T.symm z) = N.translation (N.torusPart n) :=
      (hind (e n) m hmI hsame).symm.trans (hpart n)
    have hs := htor (T.symm z)
    rw [T.apply_symm_apply] at hs
    change F.point (e n * m⁻¹) = _ at hs
    rw [map_mul, map_inv, he, ht] at hs
    letI : IsClosedImmersion M.torus.hom.hom.left := M.torusClosed
    letI : Mono M.torus.hom.hom := Over.mono_of_mono_left _
    have ht' : t = T.symm z :=
      (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).injective
        ((cancel_mono M.torus.hom.hom).mp hs)
    rw [← hz, ← ht']
    exact hlog t χ

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
theorem foldedNormalizerApartment : FoldedNormalizerApartment.{u} := by
  classical
  intro K _ _ _ _ D M F e b hb he hord G _ j N hpoints hproj V
  letI := D.finiteRoots
  letI : Fintype D.base.support := Fintype.ofFinite _
  let W := fixedWeylGroup D e
  let r := Units.mk0 (1 / 2 : ℚ) (by norm_num)
  obtain ⟨a, hker, hact, _⟩ :=
    markedNormalizerApartment F b j N W.subtype Subtype.val_injective hpoints r
  obtain ⟨w, hwi, hw⟩ := foldedWeylLinearAction D e b he hord
  let τ := simplePermutation D e
  have hshift (t : N.torus) : ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd) ∈ V := by
    let y := (N.translation t).toAdd
    have hy : (fun i => ((b.repr y i : ℤ) : ℚ) / 2) ∈ Set.range (orbitProjection τ) := by
      rw [← hproj]
      exact ⟨t, rfl⟩
    obtain ⟨z, hz⟩ := hy
    have hcoords (i : D.base.support) : b.repr y i = b.repr y (τ i) := by
      have hτ : τ (τ i) = i := Subtype.ext (he i.val)
      have h₁ := congrFun hz i
      have h₂ := congrFun hz (τ i)
      simp only [orbitProjection, hτ] at h₁ h₂
      exact_mod_cast (show (b.repr y i : ℚ) = (b.repr y (τ i) : ℚ) by linarith)
    have hy' : e.val.coweightEquiv.symm y = y := by
      have hbperm (i) : e.val.coweightEquiv.symm (b i) = b (τ i) :=
        ((basedPermutation D e b hb) i).1
      calc
        e.val.coweightEquiv.symm y =
            e.val.coweightEquiv.symm (∑ i, b.repr y i • b i) :=
          congrArg e.val.coweightEquiv.symm (b.sum_repr y).symm
        _ = ∑ i, b.repr y i • b (τ i) := by simp only [map_sum, map_smul, hbperm]
        _ = ∑ i, b.repr y (τ i) • b (τ i) :=
          Finset.sum_congr rfl fun i _ => congrArg (· • b (τ i)) (hcoords i)
        _ = y := (Equiv.sum_comp τ (fun i => b.repr y i • b i)).trans (b.sum_repr y)
    apply LinearMap.mem_ker.mpr
    change ((1 / 2 : ℚ) ⊗ₜ[ℤ] e.val.coweightEquiv.symm y) - ((1 / 2 : ℚ) ⊗ₜ[ℤ] y) = 0
    rw [hy', sub_self]
  let v (n : N.normalizer) : V := ⟨_, hshift (N.torusPart n)⟩
  let g (n : N.normalizer) : V ≃ᵃ[ℚ] V :=
    AffineEquiv.ofLinearEquiv (w (N.label n)) 0 (v n)
  have hg (n : N.normalizer) (x : V) : (g n x).val = a n x.val := by
    change (w (N.label n) (x - 0)).val + (v n).val = _
    rw [sub_zero, hw, hact]
    rfl
  let u : N.normalizer →* (V ≃ᵃ[ℚ] V) := MonoidHom.mk' g (fun n m => by
    apply AffineEquiv.ext
    intro x
    apply Subtype.ext
    change (g (n * m) x).val = (g n (g m x)).val
    rw [hg, hg, hg, map_mul]
    rfl)
  have hku : u.ker = a.ker := by
    ext n
    change g n = 1 ↔ a n = 1
    constructor
    · intro hu
      have hl : N.label n = 1 := by
        apply hwi
        have h := congrArg AffineEquiv.linear hu
        change (AffineEquiv.ofLinearEquiv (w (N.label n)) 0 (v n)).linear =
          (1 : V ≃ᵃ[ℚ] V).linear at h
        rw [AffineEquiv.linear_ofLinearEquiv] at h
        exact h.trans (w.map_one).symm
      have hzero := congrArg (fun f : V ≃ᵃ[ℚ] V => (f 0).val) hu
      rw [hg, hact, show ((0 : V).val) = 0 from rfl, map_zero, zero_add] at hzero
      have hv : ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd) = 0 := hzero
      apply AffineEquiv.ext
      intro x
      rw [hact, hl, show (r : ℚ) = 1 / 2 from rfl, hv, add_zero]
      have hOne : (1 : RootPairing.Aut D.datum).coweightEquiv.symm = (1 : D.Y ≃ₗ[ℤ] D.Y) := by
        have heq : (1 : RootPairing.Aut D.datum).coweightEquiv = (1 : D.Y ≃ₗ[ℤ] D.Y) :=
          LinearEquiv.toLinearMap_injective (RootPairing.Equiv.coweightEquiv_one D.datum)
        rw [heq]
        exact inv_one
      rw [W.subtype.map_one, Subgroup.coe_one, hOne, LinearEquiv.baseChange_one]
      rfl
    · intro ha
      apply AffineEquiv.ext
      intro x
      exact Subtype.ext (by rw [hg, ha]; rfl)
  exact ⟨u, hku ▸ hker, fun n x => (hg n x).trans (hact n x.val)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem markedWallWord {K : Type u} [Field K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M K)
    (l : List (D.base.support × Kˣ)) :
    let R := CommAlgCat.of Integers.{u} K
    ∃ m, F.point m = (l.map fun p => markedWall M.toIntegralMarking R p.1.val p.2).prod ∧
      F.label m = (l.map fun p => RootPairing.weylGroup.ofIdx D.datum p.1.val).prod := by
  intro R
  letI := F.torusComm
  obtain ⟨T, hT, _⟩ := fibreNormalizerTorusAction F
  induction l with
  | nil => exact ⟨1, map_one F.point, map_one F.label⟩
  | cons au l ih =>
    obtain ⟨a, u⟩ := au
    obtain ⟨m, hm, hlabel⟩ := ih
    obtain ⟨_, n, _, hn, hp, _⟩ := F.simple a
    let c := cocharacter D (D.datum.coroot a.val) R (-u)
    let t := (T c).val
    have ht : F.label t = 1 := (T c).property
    let ρ : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
      ((M.rankOne a.val).app R).hom
    have hd : F.point t = ρ (diagonal (-u)) :=
      (hT c).trans (M.rankOneDiagonal a.val R (-u)).symm
    have hp' : F.point n = ρ (rankOneMatrixWord 1) := hp
    have hwall : F.point (t * n) = markedWall M.toIntegralMarking R a.val u := by
      rw [map_mul, hd, hp', ← map_mul]
      exact congrArg ρ ((wallMatrixRelations (-u) 1).2.1.symm)
    use (t * n) * m
    constructor
    · rw [map_mul, hwall, hm]
      rfl
    · rw [map_mul, map_mul, ht, hn, hlabel, one_mul]
      rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem markedWallNormalizer : MarkedWallNormalizer.{u} := by
  intro K _ _ _ _ D M F G W _ _ j N q hq hpoints w hw orbit R s u v l hl g hg
  letI := F.torusComm
  obtain ⟨m, hm, hqM⟩ := splitMarkedNormalizerWord F w hw
  obtain ⟨r, hr, hqR⟩ := markedWallWord F orbit
  let z := m * r * m⁻¹
  have hz : F.point z = j g := by
    rw [map_mul, map_mul, map_inv, hm, hr]
    exact hg.symm
  have hzq : F.label z = q l := by
    rw [map_mul, map_mul, map_inv, hqM, hqR, hl]
  obtain ⟨t, ht, htq⟩ := hpoints (N.lift l)
  have hf : F.label (z * t⁻¹) = 1 := by
    rw [map_mul, map_inv, hzq, htq, N.lift_label, mul_inv_cancel]
  obtain ⟨T, hT, _⟩ := fibreNormalizerTorusAction F
  let x : F.label.ker := ⟨z * t⁻¹, hf⟩
  have hx := hT (T.symm x)
  rw [T.apply_symm_apply] at hx
  have he : j (g * (N.lift l : G)⁻¹) =
      torusPoint D R (T.symm x) ≫ M.torus.hom.hom := by
    rw [map_mul, map_inv, ← hz, ← ht, ← map_inv, ← map_mul]
    exact hx
  have ht' : g * (N.lift l : G)⁻¹ ∈ N.torus := (N.torusPoints _).mpr ⟨T.symm x, he⟩
  have hgN : g ∈ N.normalizer := by
    have h := N.normalizer.mul_mem (N.torus_le ht') (N.lift l).property
    simpa only [inv_mul_cancel_right] using h
  let n : N.normalizer := ⟨g, hgN⟩
  obtain ⟨n₀, hn, hn₀⟩ := hpoints n
  have heq : n₀ = z := fibreNormalizerPoint_injective F (hn.trans hz.symm)
  rw [heq, hzq] at hn₀
  exact ⟨n, rfl, hq hn₀.symm⟩

private theorem wall_torus_factor {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (p : Rˣ) :
    markedWall M R a p =
      (torusPoint D R (cocharacter D (D.datum.coroot a) R p) ≫ M.torus.hom.hom :
        IntegralPoints M.group R) * markedWall M R a 1 := by
  let ρ : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne a).app R).hom
  have h : wallMatrix p = diagonal p * wallMatrix 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, wallMatrix_val, wallMatrix_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  change ρ (wallMatrix p) = _ * ρ (wallMatrix 1)
  rw [h, map_mul]
  exact congrArg (fun z => z * ρ (wallMatrix 1)) (M.rankOneDiagonal a R p)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
theorem markedWallDisplacements : MarkedWallDisplacements.{u} := by
  intro K _ _ _ _ D M F index _ b G W _ _ j N q hq hpoints transport htransport R s w c m wall z
  letI := F.torusComm
  obtain ⟨_, _, _, hcomparison⟩ := markedNormalizerApartment F b j N q hq hpoints 1
  obtain ⟨ν, _, hν, _⟩ := Arithmetic.ExceptionalValuedTorusNormalizer.splitTorusTranslation K D b
  obtain ⟨hcochar, hcov⟩ := splitTranslationAction D ν hν
  obtain ⟨T, hT, hConj⟩ := fibreNormalizerTorusAction F
  obtain ⟨v, hv, hvq⟩ := splitMarkedNormalizerWord F transport htransport
  let tor := markedTorusPointHom M.toIntegralMarking R
  have hshift (l : List D.I) (hl : ∀ a ∈ l, a ∈ D.base.support)
      (t : TorusValues D R) (n : N.normalizer)
      (hlabel : q (N.label n) = w * (l.map s).prod * w⁻¹)
      (hn : j n = m * (tor t * markedWeylWord M.toIntegralMarking R l) * m⁻¹) :
      (N.translation (N.torusPart n)).toAdd = c (ν t).toAdd := by
    obtain ⟨v', hv', hvq'⟩ := splitMarkedNormalizerWord F l hl
    let d := v * v' * v⁻¹
    have hd : F.label d = q (N.label n) := by
      change F.label (v * v' * v⁻¹) = _
      rw [map_mul, map_mul, map_inv, hvq, hvq', hlabel]
    have hdp : F.point d = m * markedWeylWord M.toIntegralMarking R l * m⁻¹ := by
      change F.point (v * v' * v⁻¹) = _
      rw [map_mul, map_mul, map_inv, hv, hv']
    have hdI : F.point d ∈ ((integralPointFunctor M.group).map (valuationRingInclusion K)).hom.range := by
      let O := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
      let x := markedWeylWord M.toIntegralMarking O transport
      let y := markedWeylWord M.toIntegralMarking O l
      refine ⟨x * y * x⁻¹, ?_⟩
      let inc := ((integralPointFunctor M.group).map (valuationRingInclusion K)).hom
      change inc (x * y * x⁻¹) = _
      rw [map_mul, map_mul, map_inv, hdp]
      exact congrArg₂ (fun x y => x * y * x⁻¹)
        (markedWeylWord_map M.toIntegralMarking (valuationRingInclusion K) transport)
        (markedWeylWord_map M.toIntegralMarking (valuationRingInclusion K) l)
    let t' := t.comp w.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
    have hconj : j n * (F.point d)⁻¹ = torusPoint D R t' ≫ M.torus.hom.hom := by
      rw [hn, hdp]
      calc
        _ = m * tor t * m⁻¹ := by group
        _ = _ := by
          have h := congrArg (fun t : F.label.ker => F.point t.val) (hConj v t)
          change F.point (v * (T t).val * v⁻¹) =
            F.point (T (t.comp (F.label v).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative)).val at h
          rw [map_mul, map_mul, map_inv, hv, hT, hT, hvq] at h
          exact h
    rw [← hcov w.val t]
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext χ
    exact (hcomparison n d hd hdI t' hconj χ).trans (hν t' χ).symm
  constructor
  · intro a p n hlabel hn
    have h := hshift [a.val] (by simpa using a.property)
      (cocharacter D (D.datum.coroot a.val) R p) n
    have hlabel' : q (N.label n) = w * ([a.val].map s).prod * w⁻¹ := by
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using hlabel
    have hword : markedWeylWord M.toIntegralMarking R [a.val] = wall a.val 1 := by
      simp [markedWeylWord, wall]
    have he := h hlabel' (by rw [hn, hword]; congr 2; exact wall_torus_factor M.toIntegralMarking R a.val p)
    exact he.trans (congrArg c (hcochar (D.datum.coroot a.val) p))
  · intro a b p v n hsym horth hlabel hn
    let x := cocharacter D (D.datum.coroot a.val) R p
    let y := cocharacter D (D.datum.coroot b.val) R v
    have ht : Commute (wall a.val 1) (tor y) := by
      have h := markedOrthogonalRankOneCommutation M hsym a.val b.val horth K
        (CommAlgCat.of K K) (wallMatrix 1) (diagonal v)
      have he : tor y = (M.rankOne b.val).app R (diagonal v) :=
        (markedTorusPointHom_apply M.toIntegralMarking R y).trans
          (M.rankOneDiagonal b.val R v).symm
      rw [he]
      exact h
    have hword : markedWeylWord M.toIntegralMarking R [a.val, b.val] = wall a.val 1 * wall b.val 1 := by
      simp [markedWeylWord, wall]
    have ha : wall a.val p = tor x * wall a.val 1 :=
      wall_torus_factor M.toIntegralMarking R a.val p
    have hb : wall b.val v = tor y * wall b.val 1 :=
      wall_torus_factor M.toIntegralMarking R b.val v
    have hfactor : wall a.val p * wall b.val v =
        tor (x * y) * markedWeylWord M.toIntegralMarking R [a.val, b.val] := by
      rw [ha, hb, map_mul, hword]
      simp only [mul_assoc]
      rw [← mul_assoc (wall a.val 1), ht.eq, mul_assoc]
    have hlabel' : q (N.label n) = w * ([a.val, b.val].map s).prod * w⁻¹ := by
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using hlabel
    have he := hshift [a.val, b.val] (by
      intro i hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      exact hi.elim (fun h => h ▸ a.property) (fun h => h ▸ b.property))
      (x * y) n hlabel' (by rw [hn, hfactor])
    rw [he, map_mul, toAdd_mul, hcochar, hcochar]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 750000 in
theorem splitIwahoriStabilizer : SplitIwahoriStabilizer.{u} := by
  classical
  intro K _ _ _ _ D M F index _ b R j P N hwords hpoints n perm depth hdepth g
  let q := MonoidHom.id D.datum.weylGroup
  obtain ⟨act, hker, _, _⟩ := markedNormalizerApartment F b j N q
    (fun _ _ h => h) hpoints 1
  have hker' : act.ker.map N.normalizer.subtype = integralUnitTorus (K := K) M := by
    simpa only [j, Subgroup.comap_id] using hker
  have hconj (n : N.normalizer) (t : IntegralPoints M.group R)
      (ht : t ∈ integralUnitTorus (K := K) M) :
      (n : IntegralPoints M.group R) * t * (n : IntegralPoints M.group R)⁻¹ ∈
        integralUnitTorus (K := K) M := by
    rw [← hker'] at ht ⊢
    obtain ⟨t, ht, rfl⟩ := ht
    change act t = 1 at ht
    refine ⟨n * t * n⁻¹, ?_, rfl⟩
    change act (n * t * n⁻¹) = 1
    simp [ht]
  have hunits (t : IntegralPoints M.group R) :
      t ∈ integralUnitTorus (K := K) M ↔
        (n : IntegralPoints M.group R) * t * (n : IntegralPoints M.group R)⁻¹ ∈
          integralUnitTorus (K := K) M := by
    refine ⟨hconj n t, fun h => ?_⟩
    simpa only [Subgroup.coe_inv, inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel,
      mul_one] using hconj n⁻¹ _ h
  choose c hc hc' using markedNormalizerRootLayers j N q hwords n
  let v := normalizedValuation K
  have hle (x : K) : valuation K x ≤ 1 ↔ v x ≤ 1 := by
    change valuation K x ≤ 1 ↔
      Specs.ExceptionalValuedTorusNormalizer.normalizedValuation K x ≤ 1
    rw [← map_one (valuation K), ← (valuation K).vle_iff_le]
    simpa only [map_one] using (normalizedValuation_le_iff (K := K) x 1).symm
  have hge (x : K) : 1 ≤ valuation K x ↔ 1 ≤ v x := by
    change 1 ≤ valuation K x ↔
      1 ≤ Specs.ExceptionalValuedTorusNormalizer.normalizedValuation K x
    rw [← map_one (valuation K), ← (valuation K).vle_iff_le]
    simpa only [map_one] using (normalizedValuation_le_iff (K := K) 1 x).symm
  have hlt (x : K) : v x < 1 ↔ v x ≤ exp (-1 : ℤ) := by
    by_cases hx : v x = 0
    · simp [hx]
    · rw [← exp_log hx, exp_lt_one_iff, exp_le_exp]
      omega
  have hallowed (a : D.I) (x : K) :
      (valuation K x ≤ 1 ∧ (¬ D.base.IsPos a → valuation K x < 1)) ↔
        v x ≤ exp (-(depth a)) := by
    by_cases ha : D.base.IsPos a
    · simpa only [depth, if_pos ha, neg_zero, exp_zero, ha, not_true_eq_false,
        false_implies, and_true] using hle x
    · have h : valuation K x < 1 ↔ v x < 1 := by
        rw [lt_iff_not_ge, lt_iff_not_ge, hge]
      rw [show depth a = 1 from if_neg ha]
      constructor
      · exact fun H => (h.trans (hlt x)).mp (H.2 ha)
      · intro H
        have hx := (h.trans (hlt x)).mpr H
        exact ⟨hx.le, fun _ => hx⟩
  have hroot (a : D.I) (x : K) :
      (valuation K x ≤ 1 ∧ (¬ D.base.IsPos a → valuation K x < 1)) ↔
        (valuation K ((c a : K) * x) ≤ 1 ∧
          (¬ D.base.IsPos (perm a) → valuation K ((c a : K) * x) < 1)) := by
    rw [hallowed, hallowed, hdepth a]
    exact ((hc' a x).2 (depth a)).1
  simpa only [LocalIwahori.iwahori, j, Subgroup.comap_id] using
    iwahoriPreservedByLayerAction P.residueFibre P.residueBorel P.borel_eq n.val perm c
      hunits hroot (fun a u => (hc' a u).1) g

end NormalizerAction

section PinnedWalls

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Matrix
open Matrix (SpecialLinearGroup)
open Specs.IntegralSemisimpleModel (IntegralPoints Integers integerAlgebra integralPointFunctor)
open Specs.ExceptionalMarkedRootDescent (SimpleRootOrbit pinnedDiagram markedWeylWord markedWall
  wallMatrix quadraticIntegralAlgebra evaluateGroundTensor)
open Arithmetic.ExceptionalMarkedRootDescent (pinnedSingletonRootModel pinnedRationalPairedRankOne)
open private wallMatrix_val markedWeylWord_map evaluateGroundTensor_includeRight
  from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private groundHopfEquiv pinnedGroundPoint_apply
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

attribute [local instance] integerAlgebra

private theorem wallMatrix_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (p : Kˣ) :
    SpecialLinearGroup.map f (wallMatrix p) = wallMatrix (Units.map f.toMonoidHom p) := by
  apply Subtype.ext
  change (wallMatrix p).val.map f = _
  rw [wallMatrix_val, wallMatrix_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
theorem pinnedRankOneWallLifts : PinnedRankOneWallLifts.{u} := by
  intro k K _ _ _ _ _ _ _ _ D M C F l G B T d hdeg σ hσ hsym R H W _ j N q hj hq hpoints
    w hw word s e n
  have hsimple (i : D.I) (hi : i ∈ word) : i ∈ D.base.support := by
    obtain ⟨⟨a, b⟩, _, hi⟩ := List.mem_flatMap.mp hi
    cases b with
    | none =>
      have h : i = a.val := by simpa [SimpleRootOrbit.roots] using hi
      exact h ▸ a.property
    | some b =>
      have h : i = a.val ∨ i = b.val := by simpa [SimpleRootOrbit.roots] using hi
      exact h.elim (fun h => h ▸ a.property) (fun h => h ▸ b.property)
  have hlift := markedWallNormalizer F j N q hq hpoints word hsimple
  let pointEquiv := groundHopfEquiv G
  let S := CommAlgCat.of k k
  let U := (quadraticIntegralAlgebra k K).obj S
  let f := evaluateGroundTensor k K
  let jout := ((integralPointFunctor M.group).map f).hom
  constructor
  · intro a ha
    obtain ⟨P, hP⟩ := pinnedSingletonRootModel C d hdeg σ hσ hsym w hw a ha
    let ρ := pointEquiv.symm.toMonoidHom.comp (P.pointMap.app S).hom
    have hρ (A : SpecialLinearGroup (Fin 2) k) :
        j (ρ A) = n * (show IntegralPoints M.group R from
          (M.rankOne a).app R (SpecialLinearGroup.map (algebraMap k K) A)) * n⁻¹ := by
      rw [hj, pinnedGroundPoint_apply]
      change jout (Specs.ExceptionalMarkedRootDescent.pinnedMarkedPoint C d S
        (pointEquiv (pointEquiv.symm (P.pointMap.app S A)))) = _
      rw [pointEquiv.apply_symm_apply, hP S A]
      let b := SpecialLinearGroup.map
        (Algebra.TensorProduct.includeRight : k →ₐ[k] K ⊗[k] k).toRingHom A
      let m := markedWeylWord M.toIntegralMarking U word
      change jout (m * (show IntegralPoints M.group U from (M.rankOne a).app U b) * m⁻¹) = _
      have hword : jout m = n := markedWeylWord_map M.toIntegralMarking f word
      have hmap : SpecialLinearGroup.map f.hom.toRingHom b =
          SpecialLinearGroup.map (algebraMap k K) A := by
        apply Subtype.ext
        ext i j
        exact evaluateGroundTensor_includeRight (k := k) (K := K) (A.val i j)
      have hnat : jout ((M.rankOne a).app U b) =
          (M.rankOne a).app R (SpecialLinearGroup.map f.hom.toRingHom b) :=
        (ConcreteCategory.congr_hom ((M.rankOne a).naturality f) b).symm
      rw [map_mul, map_mul, map_inv, hword, hnat, hmap]
    refine ⟨ρ, hρ, fun v hv p => ?_⟩
    let a₁ := Units.map (algebraMap k K).toMonoidHom p
    refine hlift [(a, a₁)] v (by simpa only [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using hv) (ρ (wallMatrix p)) ?_
    rw [hρ, wallMatrix_map]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl
  · intro a b hab
    obtain ⟨ρ₀, hρ₀⟩ := pinnedRationalPairedRankOne C d hdeg σ hσ hsym w hw a b hab
    let ρ := pointEquiv.symm.toMonoidHom.comp ρ₀
    have hρ (A : SpecialLinearGroup (Fin 2) K) :
        j (ρ A) = n * ((show IntegralPoints M.group R from (M.rankOne a).app R A) *
          (show IntegralPoints M.group R from
            (M.rankOne b).app R (SpecialLinearGroup.map σ.toRingHom A))) * n⁻¹ := by
      rw [hj, pinnedGroundPoint_apply]
      change jout (Specs.ExceptionalMarkedRootDescent.pinnedMarkedPoint C d S
        (pointEquiv (pointEquiv.symm (ρ₀ A)))) = _
      rw [pointEquiv.apply_symm_apply]
      exact hρ₀ A
    refine ⟨ρ, hρ, fun v hv p => ?_⟩
    let p' := Units.map σ.toRingHom.toMonoidHom p
    refine hlift [(a, p), (b, p')] v (by simpa only [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using hv) (ρ (wallMatrix p)) ?_
    rw [hρ, wallMatrix_map]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl

end PinnedWalls

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
