import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorGradedLayers
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit
import Mathlib.LinearAlgebra.Dimension.Constructions
import Batteries.Tactic.OpenPrivate

open scoped TensorProduct DirectSum
open CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
open CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit

namespace CommutativeAlgebraNotes.Intersection.ExteriorTensorGradedLayers

noncomputable section

open scoped ExteriorTensorInverseLimit ExteriorTensorGradedLayers

open private jointIdeal_eq rectangle_eq sup_pow_le series_mem_pow pair pair_left pair_right
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3

section QuotientMaps

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

private def layerMkQ (I : Ideal R) (j : ℕ) :
    powerSubmodule (E := E) I j →ₗ[R] PowerLayer I E j :=
  ((powerSubmodule I (j + 1)).comap (powerSubmodule (E := E) I j).subtype).mkQ

private def layerMapQ (I : Ideal R) (j : ℕ) (Q : Submodule R E)
    (h : powerSubmodule I (j + 1) ≤ Q) : PowerLayer I E j →ₗ[R] E ⧸ Q :=
  Submodule.mapQ _ Q (powerSubmodule I j).subtype (fun _ hx => h hx)

private theorem layerClass_eq_zero (I : Ideal R) (j : ℕ) (x : powerSubmodule (E := E) I j)
    (hx : (x : E) ∈ powerSubmodule I (j + 1)) : layerClass I j x = 0 :=
  (Submodule.Quotient.mk_eq_zero ((powerSubmodule I (j + 1)).comap
    (powerSubmodule (E := E) I j).subtype)).2 hx

private theorem layerIntoQuotient_injective (I : Ideal R) (j : ℕ) :
    Function.Injective (layerMapQ (E := E) I j (powerSubmodule I (j + 1)) le_rfl) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  change (powerSubmodule I (j + 1)).mkQ (x : E) = 0 at hz
  exact layerClass_eq_zero I j x ((Submodule.Quotient.mk_eq_zero
    (powerSubmodule (E := E) I (j + 1))).1 hz)

end QuotientMaps

section PowerSeries

variable {k : Type*} [Field k] {σ : Type*} [Finite σ]

local notation "D" => MvPowerSeries σ k
local notation "I" => variableIdeal k σ

private theorem mem_variableIdeal_iff_constantCoeff (r : D) :
    r ∈ I ↔ MvPowerSeries.constantCoeff r = 0 := by
  rw [← pow_one I, series_mem_pow]
  constructor
  · exact fun h => h 0 (by simp)
  · intro h d hd
    have hd' : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    exact h

/-- In finitely many variables over a field, the variable ideal is the maximal ideal. -/
theorem variableIdeal_eq_maximalIdeal : I = IsLocalRing.maximalIdeal D := by
  ext r
  rw [mem_variableIdeal_iff_constantCoeff, IsLocalRing.mem_maximalIdeal]
  change MvPowerSeries.constantCoeff r = 0 ↔ ¬ IsUnit r
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_ne_iff]

variable {E : Type*} [AddCommGroup E] [Module (MvPowerSeries σ k) E]

omit [Finite σ] in
private theorem variableIdeal_smul_layer_eq_zero {j : ℕ} {r : D} (hr : r ∈ I)
    (q : PowerLayer I E j) : r • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [← map_smul]
  apply (Submodule.Quotient.mk_eq_zero _).2
  change r • (x : E) ∈ powerSubmodule I (j + 1)
  rw [powerSubmodule, pow_succ', Submodule.mul_smul]
  exact Submodule.smul_mem_smul hr x.property

private theorem scalar_on_layer {j : ℕ} (r : D) (q : PowerLayer I E j) :
    r • q = MvPowerSeries.constantCoeff r • q := by
  change r • q = (algebraMap k D (MvPowerSeries.constantCoeff r)) • q
  apply sub_eq_zero.mp
  rw [← sub_smul]
  apply variableIdeal_smul_layer_eq_zero
  exact (mem_variableIdeal_iff_constantCoeff _).2 (by
    simp [MvPowerSeries.algebraMap_apply])

end PowerSeries

section Comparison

variable (k : Type*) [Field k] (a b : ℕ) (M N : Type*)
  [AddCommGroup M] [Module (X k a) M] [AddCommGroup N] [Module (Y k b) N]

local notation "A" => X k a
local notation "B" => Y k b
local notation "R" => S k a b
local notation "T" => Product k a b M N
local notation "I" => variableIdeal k (Fin a)
local notation "J" => variableIdeal k (YIndex b)
local notation "K" => jointIdeal k a b
local notation "PX" => xSubmodule k a M
local notation "PY" => ySubmodule k b N
local notation "PT" => powerSubmodule (E := T) K
local notation "L" => JointLayer k a b M N
local notation "G" => LayerTensor k a b M N
local notation "p" => pair k a b M N
local notation "Ix" => fun u => Ideal.map (AlgHom.toRingHom (includeX k a b)) (xIdeal k a u)
local notation "Jy" => fun v => Ideal.map (AlgHom.toRingHom (includeY k a b)) (yIdeal k b v)

private theorem pair_mem_extended (u v : ℕ) {m : M} {n : N}
    (hm : m ∈ PX u) (hn : n ∈ PY v) :
    p m n ∈ ((Ix u * Jy v) • ⊤ : Submodule R T) := by
  refine Submodule.smul_induction_on hm (fun x hx m _ => ?_) (fun m m' h h' => ?_)
  · refine Submodule.smul_induction_on hn (fun y hy n _ => ?_) (fun n n' h h' => ?_)
    · rw [pair_left, pair_right, ← mul_smul]
      exact Submodule.smul_mem_smul
        (Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hx) (Ideal.mem_map_of_mem _ hy))
        Submodule.mem_top
    · simpa only [pair, TensorProduct.tmul_add] using add_mem h h'
  · simpa only [pair, TensorProduct.tmul_add, TensorProduct.add_tmul] using add_mem h h'

private theorem pair_mem_power (u v : ℕ) {m : M} {n : N}
    (hm : m ∈ PX u) (hn : n ∈ PY v) : p m n ∈ PT (u + v) := by
  apply Submodule.smul_mono_left (N := (⊤ : Submodule R T)) ?_
    (pair_mem_extended k a b M N u v hm hn)
  change Ix u * Jy v ≤ K ^ (u + v)
  simp only [xIdeal, yIdeal, Ideal.map_pow, pow_add]
  apply mul_le_mul'
  · exact Ideal.pow_right_mono (by rw [jointIdeal_eq]; exact le_sup_left) _
  · exact Ideal.pow_right_mono (by rw [jointIdeal_eq]; exact le_sup_right) _

private theorem left_right_degrees {j : ℕ} (i : Fin (j + 1)) : (i : ℕ) + (j - i) = j :=
  Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)

private theorem pair_mem_layer {j : ℕ} (i : Fin (j + 1)) (m : PX i) (n : PY (j - i)) :
    p m n ∈ PT j := by
  simpa only [left_right_degrees i] using
    pair_mem_power k a b M N i (j - i) m.property n.property

private def layerPair {j : ℕ} (i : Fin (j + 1)) (m : PX i) (n : PY (j - i)) : L j :=
  layerClass K j ⟨p m n, pair_mem_layer k a b M N i m n⟩

private def layerBilinearOnPowers {j : ℕ} (i : Fin (j + 1)) :
    PX i →ₛₗ[(includeX k a b).toRingHom] PY (j - i) →ₛₗ[(includeY k a b).toRingHom] L j :=
  LinearMap.mk₂'ₛₗ (includeX k a b).toRingHom (includeY k a b).toRingHom
    (layerPair k a b M N i)
    (fun m m' n => congrArg (layerClass (E := T) K j) (Subtype.ext (by
      simp only [pair, Submodule.coe_add, TensorProduct.tmul_add, TensorProduct.add_tmul])))
    (fun x m n => congrArg (layerClass (E := T) K j) (Subtype.ext (pair_left k a b M N x m n)))
    (fun m n n' => congrArg (layerClass (E := T) K j) (Subtype.ext (by
      simp only [pair, Submodule.coe_add, TensorProduct.tmul_add])))
    (fun y m n => congrArg (layerClass (E := T) K j) (Subtype.ext (pair_right k a b M N y m n)))

private def layerBilinear {j : ℕ} (i : Fin (j + 1)) :
    XLayer k a M i →ₛₗ[(includeX k a b).toRingHom]
      YLayer k b N (j - i) →ₛₗ[(includeY k a b).toRingHom] L j := by
  refine (layerBilinearOnPowers k a b M N i).liftQ₂ _ _ ?_ ?_
  · intro m hm
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro n
    change layerPair k a b M N i m n = 0
    apply layerClass_eq_zero (E := T) K j
      ⟨p m n, pair_mem_layer k a b M N i m n⟩
    change p m n ∈ PT (j + 1)
    have h := pair_mem_power k a b M N ((i : ℕ) + 1) (j - i) hm n.property
    rwa [show (i : ℕ) + 1 + (j - i) = j + 1 by have := left_right_degrees i; omega] at h
  · intro n hn
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro m
    change layerPair k a b M N i m n = 0
    apply layerClass_eq_zero (E := T) K j
      ⟨p m n, pair_mem_layer k a b M N i m n⟩
    change p m n ∈ PT (j + 1)
    have h := pair_mem_power k a b M N i (j - i + 1) m.property hn
    rwa [← Nat.add_assoc, left_right_degrees i] at h

private def componentMap {j : ℕ} (i : Fin (j + 1)) : G j i →ₗ[k] L j := by
  let f := layerBilinear k a b M N i
  apply TensorProduct.lift
  refine LinearMap.mk₂ k (fun m n => f m n)
    (fun m m' n => LinearMap.congr_fun (f.map_add m m') n) ?_
    (fun m n n' => (f m).map_add n n') ?_
  · intro c m n
    change f ((algebraMap k A c) • m) n = (algebraMap k R c) • f m n
    rw [f.map_smulₛₗ]
    change includeX k a b (algebraMap k A c) • f m n = _
    rw [AlgHom.commutes]
  · intro c m n
    change f m ((algebraMap k B c) • n) = (algebraMap k R c) • f m n
    rw [(f m).map_smulₛₗ]
    change includeY k a b (algebraMap k B c) • f m n = _
    rw [AlgHom.commutes]

private theorem componentMap_tmul {j : ℕ} (i : Fin (j + 1)) (m : PX i) (n : PY (j - i)) :
    componentMap k a b M N i
      (layerClass I i m ⊗ₜ[k] layerClass J (j - i) n) = layerPair k a b M N i m n := rfl

private def productMap (j : ℕ) : (⨁ i : Fin (j + 1), G j i) →ₗ[k] L j :=
  DirectSum.toModule k _ _ (componentMap k a b M N)

private theorem productMap_lof {j : ℕ} (i : Fin (j + 1)) (z : G j i) :
    productMap k a b M N j (DirectSum.lof k _ _ i z) = componentMap k a b M N i z :=
  DirectSum.toModule_lof k i z

local instance layerTower {k' D E : Type*} [Field k'] [CommRing D] [Algebra k' D]
    [AddCommGroup E] [Module D E] (I' : Ideal D) (j : ℕ) :
    IsScalarTower k' D (PowerLayer I' E j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private def xLayerIn (u : ℕ) : XLayer k a M u →ₗ[k] XM k a M (u + 1) :=
  (layerMapQ I u (PX (u + 1)) le_rfl).restrictScalars k

private def yLayerIn (v : ℕ) : YLayer k b N v →ₗ[k] YN k b N (v + 1) :=
  (layerMapQ J v (PY (v + 1)) le_rfl).restrictScalars k

private theorem rectangle_contains_next {j : ℕ} (i : Fin (j + 1)) :
    K ^ (j + 1) ≤ rectangle k a b ((i : ℕ) + 1) (j - i + 1) := by
  rw [jointIdeal_eq, rectangle_eq]
  have he : (i : ℕ) + 1 + (j - i + 1) - 1 = j + 1 := by
    have := left_right_degrees i
    omega
  simpa only [he] using
    sup_pow_le (Ideal.map (includeX k a b).toRingHom I) (Ideal.map (includeY k a b).toRingHom J)
      ((i : ℕ) + 1) (j - i + 1)

private def layerToTensor {j : ℕ} (i : Fin (j + 1)) :
    L j →ₗ[k] ModuleTensor k a b M N ((i : ℕ) + 1) (j - i + 1) := by
  let g : L j →ₗ[R] ModuleLevel k a b T ((i : ℕ) + 1) (j - i + 1) :=
    layerMapQ (E := T) K j (levelSubmodule k a b T ((i : ℕ) + 1) (j - i + 1))
      (Submodule.smul_mono_left (N := (⊤ : Submodule R T)) (rectangle_contains_next k a b i))
  let f : L j →ₗ[R] ModuleTensor k a b M N ((i : ℕ) + 1) (j - i + 1) :=
    (moduleComparison k a b M N ((i : ℕ) + 1) (j - i + 1)).toLinearMap.comp g
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c z => by
        change f ((algebraMap k R c) • z) = c • f z
        rw [f.map_smul]
        change tensorActionOfSeries k a b M N ringComparison ((i : ℕ) + 1) (j - i + 1)
          (algebraMap k R c) (f z) = _
        rw [AlgHom.commutes]
        rfl }

private theorem layerToTensor_pair {j : ℕ} (i i' : Fin (j + 1)) (m : PX i') (n : PY (j - i')) :
    layerToTensor k a b M N i (layerPair k a b M N i' m n) =
      (PX ((i : ℕ) + 1)).mkQ m ⊗ₜ[k] (PY (j - i + 1)).mkQ n := by
  exact moduleComparison_pair k a b M N _ _ m n

/-- Each degree pair can be detected in its rectangular truncation by splitting
the inclusions of the two layers into the respective vector-space quotients. -/
private def projectComponent {j : ℕ} (i : Fin (j + 1)) : L j →ₗ[k] G j i :=
  (TensorProduct.map (xLayerIn k a M (i : ℕ)).leftInverse
    (yLayerIn k b N (j - i)).leftInverse).comp (layerToTensor k a b M N i)

private theorem project_product {j : ℕ} (i : Fin (j + 1)) :
    (projectComponent k a b M N i).comp (productMap k a b M N j) =
      DirectSum.component k _ _ i := by
  apply DirectSum.linearMap_ext
  intro i'
  apply TensorProduct.ext'
  intro z w
  obtain ⟨m, hm⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨n, hn⟩ := Submodule.mkQ_surjective _ w
  change layerClass I i' m = z at hm
  change layerClass J (j - i') n = w at hn
  rw [← hm, ← hn]
  simp only [LinearMap.comp_apply, productMap_lof, componentMap_tmul]
  rw [projectComponent, LinearMap.comp_apply, layerToTensor_pair, TensorProduct.map_tmul]
  by_cases h : i' = i
  · subst i'
    rw [DirectSum.component.lof_self]
    change (xLayerIn k a M (i : ℕ)).leftInverse
        (xLayerIn k a M (i : ℕ) (layerClass I i m)) ⊗ₜ[k]
      (yLayerIn k b N (j - i)).leftInverse
        (yLayerIn k b N (j - i) (layerClass J (j - i) n)) = _
    have hx : Function.Injective (xLayerIn k a M (i : ℕ)) :=
      layerIntoQuotient_injective (E := M) I i
    have hy : Function.Injective (yLayerIn k b N (j - i)) :=
      layerIntoQuotient_injective (E := N) J (j - i)
    rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hx),
      LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hy)]
  · rw [DirectSum.component.of, dite_eq_right h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hle : j - i + 1 ≤ j - i' := by
        have h₁ : (i' : ℕ) < (i : ℕ) := hlt
        have h₂ : (i : ℕ) ≤ j := Nat.le_of_lt_succ i.isLt
        omega
      have hn : (n : N) ∈ PY (j - i + 1) :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right hle) n.property
      rw [show (PY (j - i + 1)).mkQ n = 0 from (Submodule.Quotient.mk_eq_zero _).2 hn,
        map_zero, TensorProduct.tmul_zero]
    · have hm : (m : M) ∈ PX ((i : ℕ) + 1) :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hgt)) m.property
      rw [show (PX ((i : ℕ) + 1)).mkQ m = 0 from (Submodule.Quotient.mk_eq_zero _).2 hm,
        map_zero, TensorProduct.zero_tmul]

private theorem productMap_injective (j : ℕ) : Function.Injective (productMap k a b M N j) := by
  intro d d' h
  apply DirectSum.ext_component k
  intro i
  exact (LinearMap.congr_fun (project_product k a b M N i) d).symm.trans
    ((congrArg (projectComponent k a b M N i) h).trans
      (LinearMap.congr_fun (project_product k a b M N i) d'))

private theorem extendedProduct_le {P : Submodule R T} (u v : ℕ)
    (h : ∀ (m : PX u) (n : PY v), p m n ∈ P) :
    ((Ix u * Jy v) • ⊤ : Submodule R T) ≤ P := by
  have hx : Ix u = Ideal.span ((includeX k a b).toRingHom '' (xIdeal k a u : Set A)) := by
    rw [← Ideal.map_span, Ideal.span_eq]
  have hy : Jy v = Ideal.span ((includeY k a b).toRingHom '' (yIdeal k b v : Set B)) := by
    rw [← Ideal.map_span, Ideal.span_eq]
  have hp : Submodule.span R (Set.range (fun q : M × N => p q.1 q.2)) = ⊤ :=
    ExteriorTensorProduct.span_pairs (fun m : M => m) (fun n : N => n)
      (by simp) (by simp)
  rw [hx, hy, Ideal.span_mul_span, ← hp, Submodule.span_smul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩, _, ⟨⟨m, n⟩, rfl⟩, rfl⟩
  change (includeX k a b x * includeY k a b y) • p m n ∈ P
  rw [mul_smul, ← pair_right, ← pair_left]
  exact h ⟨x • m, Submodule.smul_mem_smul hx Submodule.mem_top⟩
    ⟨y • n, Submodule.smul_mem_smul hy Submodule.mem_top⟩

/-- The products in complementary degrees generate the joint ideal-power
submodule by the binomial expansion of the sum of the two extended ideals. -/
private theorem jointPower_le {P : Submodule R T} (j : ℕ)
    (h : ∀ (i : Fin (j + 1)) (m : PX i) (n : PY (j - i)), p m n ∈ P) :
    PT j ≤ P := by
  classical
  rw [powerSubmodule, jointIdeal_eq, ← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup,
    Finset.sup_eq_iSup]
  simp only [Submodule.iSup_smul]
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  refine le_trans (Submodule.smul_mono_left Ideal.mul_le_left) ?_
  simp only [← Ideal.map_pow]
  exact extendedProduct_le k a b M N u (j - u) (h ⟨u, Finset.mem_range.mp hu⟩)

private theorem productMap_surjective (j : ℕ) : Function.Surjective (productMap k a b M N j) := by
  let f := productMap k a b M N j
  -- Every joint scalar acts on the layer by its constant coefficient.
  let P : Submodule R (L j) :=
    { carrier := LinearMap.range f
      zero_mem' := (LinearMap.range f).zero_mem
      add_mem' := (LinearMap.range f).add_mem
      smul_mem' := fun r z hz => by
        change r • z ∈ LinearMap.range f
        rw [scalar_on_layer]
        exact (LinearMap.range f).smul_mem _ hz }
  let q : PT j →ₗ[R] L j := layerMkQ (E := T) K j
  have hP : PT j ≤ (P.comap q).map (PT j).subtype := by
    apply jointPower_le k a b M N j
    intro i m n
    refine ⟨⟨p m n, pair_mem_layer k a b M N i m n⟩, ?_, rfl⟩
    change layerPair k a b M N i m n ∈ LinearMap.range f
    refine ⟨DirectSum.lof k _ _ i (layerClass I i m ⊗ₜ[k] layerClass J (j - i) n), ?_⟩
    exact (productMap_lof k a b M N i _).trans (componentMap_tmul k a b M N i m n)
  intro z
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨t', ht', he⟩ := hP t.property
  have ht : t' = t := Subtype.ext he
  subst t'
  exact ht'

end Comparison

theorem gradedComparison : GradedComparison := by
  intro k _ a b M N _ _ _ _ _ _ j
  refine ⟨LinearEquiv.ofBijective (productMap k a b M N j)
    ⟨productMap_injective k a b M N j, productMap_surjective k a b M N j⟩, ?_⟩
  intro i m n
  refine ⟨pair_mem_layer k a b M N i m n, ?_⟩
  exact (productMap_lof k a b M N i _).trans (componentMap_tmul k a b M N i m n)


section Length

variable {k : Type*} [Field k] {σ : Type*} [Finite σ]
  {E : Type*} [AddCommGroup E] [Module (MvPowerSeries σ k) E]

local notation "D" => MvPowerSeries σ k
local notation "I" => variableIdeal k σ

private theorem constantCoeffTower (j : ℕ) :
    let : Algebra D k := (MvPowerSeries.constantCoeff (σ := σ) (R := k)).toAlgebra
    IsScalarTower D k (PowerLayer I E j) := by
  let : Algebra D k := (MvPowerSeries.constantCoeff (σ := σ) (R := k)).toAlgebra
  exact IsScalarTower.of_algebraMap_smul fun r z => (scalar_on_layer r z).symm

private theorem finiteVariableLayer [Module.Finite (MvPowerSeries σ k) E] (j : ℕ) :
    Module.Finite k (PowerLayer I E j) := by
  let : Algebra D k := (MvPowerSeries.constantCoeff (σ := σ) (R := k)).toAlgebra
  let : IsScalarTower D k (PowerLayer I E j) := constantCoeffTower j
  exact Module.Finite.of_restrictScalars_finite D k (PowerLayer I E j)

private theorem variableLayerLength [Module.Finite (MvPowerSeries σ k) E] (j : ℕ) :
    Module.length D (PowerLayer I E j) = Module.finrank k (PowerLayer I E j) := by
  let : Algebra D k := (MvPowerSeries.constantCoeff (σ := σ) (R := k)).toAlgebra
  let : IsScalarTower D k (PowerLayer I E j) := constantCoeffTower j
  let : Module.Finite k (PowerLayer I E j) := finiteVariableLayer j
  have hs : Function.Surjective (algebraMap D k) :=
    fun c => ⟨MvPowerSeries.C c, MvPowerSeries.constantCoeff_C c⟩
  exact (Module.length_eq_of_surjective (M := PowerLayer I E j) hs).trans
    (Module.length_eq_finrank k (PowerLayer I E j))

end Length

theorem layerLengthConvolution : LayerLengthConvolution := by
  intro k _ a b M N _ _ _ _ _ _ j
  obtain ⟨e, _⟩ := gradedComparison k a b M N j
  let : Module.Finite (S k a b) (Product k a b M N) :=
    ExteriorTensorProduct.finite
  let (i : Fin (j + 1)) : Module.Finite k (LayerTensor k a b M N j i) := by
    let : Module.Finite k (XLayer k a M i) := finiteVariableLayer (E := M) i
    let : Module.Finite k (YLayer k b N (j - i)) := finiteVariableLayer (E := N) (j - i)
    infer_instance
  rw [variableLayerLength, ← e.finrank_eq, Module.finrank_directSum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [variableLayerLength, variableLayerLength]
  simp only [LayerTensor, Module.finrank_tensorProduct, Nat.cast_mul]

end

end CommutativeAlgebraNotes.Intersection.ExteriorTensorGradedLayers
