import MathGenome.Internal.Specs.D05.M15.InnerTensor.ExteriorMetric
import MathGenome.Internal.D05.M15.ExteriorPairing
import MathGenome.Internal.D05.M12.InnerProduct
import MathGenome.Internal.D05.M11.Nondegenerate

noncomputable section
namespace D05.M15.InnerTensor.ExteriorMetric

open Specs.D05.M15.InnerTensor.ExteriorMetric

abbrev bilinear : bilinear_type := @bilinear_value
abbrev basisMetric : basisMetric_type := @basisMetric_value
abbrev metric : metric_type := @metric_value

theorem bilinear_elementary : Specs.D05.M15.InnerTensor.ExteriorMetric.bilinear_elementary := by
  intro K V _ _ _ B p x y
  change exteriorPower.pairingDual K V p
    (exteriorPower.map p B (exteriorPower.ιMulti K p x)) (exteriorPower.ιMulti K p y) = _
  rw [exteriorPower.map_apply_ιMulti]
  exact D05.M15.ExteriorPairing.elementary p (B ∘ x) y

theorem bilinear_unique : Specs.D05.M15.InnerTensor.ExteriorMetric.bilinear_unique := by
  intro K V _ _ _ B p C hC
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro y
  exact (hC x y).trans (bilinear_elementary B p x y).symm

theorem bilinear_symmetric : Specs.D05.M15.InnerTensor.ExteriorMetric.bilinear_symmetric := by
  intro K V _ _ _ B hB p
  have heq : (bilinear_value B p).flip = bilinear_value B p := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro y
    change bilinear_value B p (exteriorPower.ιMulti K p y) (exteriorPower.ιMulti K p x) =
      bilinear_value B p (exteriorPower.ιMulti K p x) (exteriorPower.ιMulti K p y)
    rw [bilinear_elementary, bilinear_elementary]
    change (Matrix.of (fun i j => B (y i) (x j))).det =
      (Matrix.of (fun i j => B (x i) (y j))).det
    calc
      _ = (Matrix.of (fun i j => B (x i) (y j))).transpose.det := by
        congr 1
        ext i j
        exact hB.eq _ _
      _ = _ := Matrix.det_transpose _
  exact ⟨fun x y => (LinearMap.congr_fun (LinearMap.congr_fun heq y) x)⟩

theorem bilinear_nondegenerate :
    Specs.D05.M15.InnerTensor.ExteriorMetric.bilinear_nondegenerate := by
  intro K V _ _ _ _ B hB p
  have hbij : Function.Bijective (bilinear_value B p) :=
    B.bijective_exteriorPower p (B.toDual hB).bijective
  apply (D05.M11.Nondegenerate.nondegenerate_iff_left _).mpr
  apply LinearMap.ker_eq_bot.mpr
  exact hbij.injective

theorem bilinear_degree_zero :
    Specs.D05.M15.InnerTensor.ExteriorMetric.bilinear_degree_zero := by
  intro K V _ _ _ B a b
  simp only [exteriorPower.zeroEquiv_symm_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  erw [bilinear_elementary, Matrix.det_isEmpty]
  simp [mul_comm]

section Positive

variable {F V I : Type*} [RCLike F] [AddCommGroup V] [Module F V]
  [Fintype I] [LinearOrder I]

/-- The coordinate construction is positive on the exterior quotient itself. -/
theorem basisMetric_axioms (b : Module.Basis I F V) (p : ℕ) :
    D05.IsFirstInnerProduct (basisMetric b p) := by
  have hc := D05.M12.InnerProduct.coordinateInner_axioms (F := F)
    (ι := Set.powersetCard I p)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a c u v w
    simp only [basisMetric, basisMetric_value, D05.coordinateInner, map_add, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
  · exact fun u v => hc.2.1 _ _
  · exact fun v => hc.2.2.1 _
  · intro v hv
    apply hc.2.2.2
    intro hz
    apply hv
    apply (b.exteriorPower p).repr.injective
    ext s
    simpa only [map_zero, Finsupp.zero_apply, Pi.zero_apply] using congrFun hz s

/-- For a fixed second argument the coordinate metric is linear in the first. -/
def basisMetricLeft (b : Module.Basis I F V) (p : ℕ) (y : ⋀[F]^p V) :
    Module.Dual F (⋀[F]^p V) where
  toFun x := basisMetric b p x y
  map_add' x z := by
    simpa using (basisMetric_axioms b p).1 1 1 x z y
  map_smul' a x := by
    simpa using (basisMetric_axioms b p).1 a 0 x 0 y

lemma basisMetric_basis_left (b : Module.Basis I F V) (p : ℕ)
    (s : Set.powersetCard I p) (y : ⋀[F]^p V) :
    basisMetric b p (b.exteriorPower p s) y =
      starRingEnd F ((b.exteriorPower p).repr y s) := by
  classical
  simp only [basisMetric, basisMetric_value, D05.coordinateInner, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

end Positive

section Orthonormal

variable {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
  [Fintype I] [LinearOrder I]

/-- Comparing functionals on increasing basis wedges proves the Gram formula,
without factorials or a characteristic-zero alternation model. -/
theorem basisMetric_elementary (b : OrthonormalBasis I F V) (p : ℕ)
    (x y : Fin p → V) :
    basisMetric b.toBasis p (exteriorPower.ιMulti F p x) (exteriorPower.ιMulti F p y) =
      Matrix.det (fun i j => D05.firstInner (F := F) (x i) (y j)) := by
  let f : Fin p → Module.Dual F V := fun j => (innerSL F (y j)).toLinearMap
  have heq : basisMetricLeft b.toBasis p (exteriorPower.ιMulti F p y) =
      exteriorPower.pairingDual F V p (exteriorPower.ιMulti F p f) := by
    apply (b.toBasis.exteriorPower p).ext
    intro s
    change basisMetric b.toBasis p (b.toBasis.exteriorPower p s)
      (exteriorPower.ιMulti F p y) = _
    rw [basisMetric_basis_left, exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, exteriorPower.basis_apply,
      exteriorPower.ιMulti_family, exteriorPower.pairingDual_ιMulti_ιMulti]
    rw [RingHom.map_det]
    calc
      _ = (Matrix.of (fun i j => f j
          ((b.toBasis ∘ (Set.powersetCard.ofFinEmbEquiv.symm s)) i))).transpose.det := by
        congr 1
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.of_apply, Matrix.transpose_apply,
          Module.Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
          Function.comp_apply, f, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
        exact inner_conj_symm _ _
      _ = _ := Matrix.det_transpose _
  have hv := LinearMap.congr_fun heq (exteriorPower.ιMulti F p x)
  change basisMetric b.toBasis p _ _ = _ at hv
  rw [exteriorPower.pairingDual_ιMulti_ιMulti] at hv
  exact hv

end Orthonormal

section Uniqueness

variable {F X : Type*} [RCLike F] [AddCommGroup X] [Module F X]

/-- Bundle the two slot rules, retaining the manuscript's linear first slot. -/
def firstInnerForm (h : X → X → F) (hh : D05.IsFirstInnerProduct h) :
    X →ₗ[F] X →ₗ⋆[F] F where
  toFun x := {
    toFun := h x
    map_add' y z := by
      simpa using D05.M12.InnerProduct.second_slot_of_axioms h hh 1 1 x y z
    map_smul' a y := by
      simpa using D05.M12.InnerProduct.second_slot_of_axioms h hh a 0 x y 0 }
  map_add' u v := by
    ext w
    simpa using hh.1 1 1 u v w
  map_smul' a u := by
    ext w
    simpa using hh.1 a 0 u 0 w

/-- A basis tests semilinear maps as well as linear maps, so no positivity
assumption is needed for the uniqueness argument. -/
lemma sesquilinear_ext {V I : Type*} [AddCommGroup V] [Module F V]
    [LinearOrder I] (b : Module.Basis I F V) (p : ℕ)
    (h g : (⋀[F]^p V) →ₗ[F] (⋀[F]^p V) →ₗ⋆[F] F)
    (heq : ∀ x y, h (exteriorPower.ιMulti F p x) (exteriorPower.ιMulti F p y) =
      g (exteriorPower.ιMulti F p x) (exteriorPower.ιMulti F p y)) : h = g := by
  apply (b.exteriorPower p).ext
  intro s
  apply (b.exteriorPower p).ext
  intro t
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.ιMulti_family]
  exact heq _ _

end Uniqueness

section Canonical

variable {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
  [FiniteDimensional F V]

theorem positive_axioms : Specs.D05.M15.InnerTensor.ExteriorMetric.positive_axioms := by
  intro F V _ _ _ _ p
  exact basisMetric_axioms (stdOrthonormalBasis F V).toBasis p

theorem positive_elementary : Specs.D05.M15.InnerTensor.ExteriorMetric.positive_elementary := by
  intro F V _ _ _ _ p x y
  exact basisMetric_elementary (stdOrthonormalBasis F V) p x y

theorem sesquilinear_unique : Specs.D05.M15.InnerTensor.ExteriorMetric.sesquilinear_unique := by
  intro F V _ _ _ _ p h hh u v
  let g := firstInnerForm (metric (F := F) (V := V) p) (positive_axioms p)
  have heq : h = g := by
    apply sesquilinear_ext (stdOrthonormalBasis F V).toBasis p
    intro x y
    exact (hh x y).trans (positive_elementary p x y).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun heq u) v

theorem positive_unique : Specs.D05.M15.InnerTensor.ExteriorMetric.positive_unique := by
  intro F V _ _ _ _ p h hh he
  funext u v
  exact sesquilinear_unique p (firstInnerForm h hh) he u v

theorem basis_independent : Specs.D05.M15.InnerTensor.ExteriorMetric.basis_independent := by
  intro F V I _ _ _ _ _ _ b p
  apply positive_unique p _ (basisMetric_axioms b.toBasis p)
  exact basisMetric_elementary b p

theorem orthonormal_wedges : Specs.D05.M15.InnerTensor.ExteriorMetric.orthonormal_wedges := by
  intro F V I _ _ _ _ _ _ b p s t
  rw [← basis_independent b p]
  change basisMetric b.toBasis p (b.toBasis.exteriorPower p s)
    (b.toBasis.exteriorPower p t) = _
  rw [basisMetric_basis_left]
  classical
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : s = t
  · subst t
    simp
  · simp [h, Ne.symm h]

theorem positive_degree_zero : Specs.D05.M15.InnerTensor.ExteriorMetric.positive_degree_zero := by
  intro F V _ _ _ _ a b
  have hh := positive_axioms (F := F) (V := V) 0
  have hs := D05.M12.InnerProduct.second_slot_of_axioms _ hh
  simp only [exteriorPower.zeroEquiv_symm_apply]
  have hl (c : F) (u v : ⋀[F]^0 V) : metric_value 0 (c • u) v = c * metric_value 0 u v := by
    simpa using hh.1 c 0 u 0 v
  have hr (c : F) (u v : ⋀[F]^0 V) :
      metric_value 0 u (c • v) = starRingEnd F c * metric_value 0 u v := by
    simpa using hs c 0 u v 0
  rw [hl, hr]
  erw [positive_elementary, Matrix.det_isEmpty]
  simp only [mul_one]

theorem positive_above_dimension :
    Specs.D05.M15.InnerTensor.ExteriorMetric.positive_above_dimension := by
  intro F V _ _ _ _ p hp x y
  have hz : Subsingleton (⋀[F]^p V) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt
      (Module.finBasis F V) (Module.finBasis F V).span_eq p (by simpa using hp)
  have hxy : x = 0 := Subsingleton.elim _ _
  rw [hxy]
  exact (D05.M12.InnerProduct.zero_of_axioms _ (positive_axioms p) y).1

end Canonical

end D05.M15.InnerTensor.ExteriorMetric
