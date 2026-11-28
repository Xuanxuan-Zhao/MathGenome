import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.BialgebraDeformation.SkewPrimitiveHopf
import MathGenome.Internal.LieTheoryDeepening.LieNotes.BialgebraDeformation.CompletedPolynomialMaps
import Mathlib.RingTheory.PowerSeries.Exp

open scoped TensorProduct

namespace LieNotes.BialgebraDeformation

open PowerSeries

noncomputable section

section Series

variable {k A D : Type*} [Field k] [CommRing A] [CommRing D] [Algebra k A] [Algebra k D]

@[simp] theorem coeff_parameterExp (a : A) (n : ℕ) :
    coeff n (parameterExp (k := k) a) = a ^ n * algebraMap k A (1 / (n.factorial : k)) :=
  coeff_mk _ _

@[simp] theorem constantCoeff_parameterExp (a : A) :
    constantCoeff (parameterExp (k := k) a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_parameterExp]
  simp

@[simp] theorem parameterExp_zero :
    parameterExp (k := k) (0 : A) = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n => simp

theorem parameterExp_add [CharZero k] (a b : A) :
    parameterExp (k := k) (a + b) = parameterExp (k := k) a * parameterExp (k := k) b := by
  let : Algebra ℚ A := ((algebraMap k A).comp (algebraMap ℚ k)).toAlgebra
  have h (c : A) : parameterExp (k := k) c = rescale c (exp A) := by
    apply PowerSeries.ext
    intro n
    rw [coeff_parameterExp, coeff_rescale, coeff_exp]
    congr 1
    change algebraMap k A (1 / (n.factorial : k)) =
      algebraMap k A (algebraMap ℚ k (1 / (n.factorial : ℚ)))
    rw [map_div₀ (algebraMap ℚ k), map_one, map_natCast]
  rw [h, h a, h b, exp_mul_exp_eq_exp_add]

@[simp] theorem seriesMap_parameterExp (f : A →ₐ[k] D) (a : A) :
    seriesMap f (parameterExp (k := k) a) = parameterExp (k := k) (f a) := by
  apply PowerSeries.ext
  intro n
  simp [map_mul, map_pow, f.commutes]

private theorem extendSeries_extends (a : A →ₐ[k] PowerSeries D) :
    ExtendsSeriesMap a (extendSeries a) :=
  ⟨extendSeries_continuous a, extendSeries_X a, extendSeries_C a⟩

private theorem extendSeries_parameterExp (f : A →ₐ[k] PowerSeries D) (a : A) (b : D)
    (h : f a = C b) :
    extendSeries f (parameterExp (k := k) a) = parameterExp (k := k) b := by
  have hcoeff (j : ℕ) :
      f (coeff j (parameterExp (k := k) a)) = C (coeff j (parameterExp (k := k) b)) := by
    simp only [coeff_parameterExp, map_mul, map_pow, h]
    rw [f.commutes, PowerSeries.algebraMap_apply]
  apply PowerSeries.ext
  intro n
  rw [extendSeries_coeff]
  simp only [hcoeff]
  rw [Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr (Nat.lt_succ_self n))]
  · simp
  · intro j hj hne
    apply coeff_C_of_ne_zero
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_of_le_of_ne
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hne))

end Series

/-- Evaluation at the formal parameter zero is the quotient by its principal ideal. -/
theorem constantCoeff_ker_eq_seriesVariableIdeal (A : Type*) [CommRing A] :
    RingHom.ker (constantCoeff (R := A)) = seriesVariableIdeal A := by
  ext p
  rw [RingHom.mem_ker, seriesVariableIdeal, Ideal.mem_span_singleton, X_dvd_iff]

section Tensor

variable {k A B D : Type*} [Field k] [CommRing A] [CommRing B] [CommRing D]
    [Algebra k A] [Algebra k B] [Algebra k D]

omit [CommRing A] [CommRing B] [CommRing D] in
private theorem continuous_comp_series
    {f : PowerSeries A → PowerSeries B} {g : PowerSeries B → PowerSeries D}
    (hg : SeriesContinuous g) (hf : SeriesContinuous f) :
    SeriesContinuous (g ∘ f) :=
  @Continuous.comp _ _ _ (seriesTopology A) (seriesTopology B) (seriesTopology D) f g hg hf

omit [CommRing A] in
private theorem continuous_id_series : SeriesContinuous (id : PowerSeries A → PowerSeries A) :=
  @continuous_id _ (seriesTopology A)

@[simp] private theorem onSeriesConstants_apply
    (f : PowerSeries A →ₐ[PowerSeries k] PowerSeries D) (a : A) :
    onSeriesConstants f a = f (C a) := rfl

private theorem extends_onSeriesConstants (f : PowerSeries A →ₐ[PowerSeries k] PowerSeries D)
    (hf : SeriesContinuous f) : ExtendsSeriesMap (onSeriesConstants f) f := by
  refine ⟨hf, ?_, fun _ => rfl⟩
  simpa only [PowerSeries.algebraMap_apply'', PowerSeries.map_X] using f.commutes (X : PowerSeries k)

private theorem id_series_extends :
    ExtendsSeriesMap (seriesConstants k A) (AlgHom.id (PowerSeries k) (PowerSeries A)) :=
  ⟨continuous_id_series, rfl, fun _ => rfl⟩

private def seriesProductMap
    (f : PowerSeries A →ₐ[PowerSeries k] PowerSeries D)
    (g : PowerSeries B →ₐ[PowerSeries k] PowerSeries D) :
    PowerSeries (A ⊗[k] B) →ₐ[PowerSeries k] PowerSeries D :=
  extendSeries (Algebra.TensorProduct.productMap (onSeriesConstants f) (onSeriesConstants g))

private theorem seriesProductMap_extends
    (f : PowerSeries A →ₐ[PowerSeries k] PowerSeries D)
    (g : PowerSeries B →ₐ[PowerSeries k] PowerSeries D) :
    ExtendsSeriesProduct f g (seriesProductMap f g) :=
  extendSeries_extends _

private theorem seriesProductMap_pair
    (f : PowerSeries A →ₐ[PowerSeries k] PowerSeries D)
    (g : PowerSeries B →ₐ[PowerSeries k] PowerSeries D)
    (hf : SeriesContinuous f) (hg : SeriesContinuous g)
    (p : PowerSeries A) (q : PowerSeries B) :
    seriesProductMap f g (seriesTensorPair (k := k) p q) = f p * g q := by
  let l : A →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeLeft
  let r : B →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeRight
  have hF : SeriesContinuous (seriesProductMap f g) := (seriesProductMap_extends f g).1
  have hl : (seriesProductMap f g).comp (seriesMap l) = f := by
    refine seriesHom_ext _ _ (continuous_comp_series (g := seriesProductMap f g) (f := seriesMap l)
      hF (seriesMap_continuous l)) hf ?_
    intro a
    simp [seriesProductMap, l, Algebra.TensorProduct.includeLeft_apply]
  have hr : (seriesProductMap f g).comp (seriesMap r) = g := by
    refine seriesHom_ext _ _ (continuous_comp_series (g := seriesProductMap f g) (f := seriesMap r)
      hF (seriesMap_continuous r)) hg ?_
    intro b
    simp [seriesProductMap, r, Algebra.TensorProduct.includeRight_apply]
  change seriesProductMap f g (seriesMap l p * seriesMap r q) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (AlgHom.congr_fun hl p) (AlgHom.congr_fun hr q)

@[simp] private theorem seriesTensorPair_one_one :
    seriesTensorPair (k := k) (1 : PowerSeries A) (1 : PowerSeries B) = 1 := by
  simp [seriesTensorPair]

private theorem seriesTensorPair_add_left (p p' : PowerSeries A) (q : PowerSeries B) :
    seriesTensorPair (k := k) (p + p') q =
      seriesTensorPair (k := k) p q + seriesTensorPair (k := k) p' q := by
  simp [seriesTensorPair, add_mul]

private theorem seriesTensorPair_add_right (p : PowerSeries A) (q q' : PowerSeries B) :
    seriesTensorPair (k := k) p (q + q') =
      seriesTensorPair (k := k) p q + seriesTensorPair (k := k) p q' := by
  simp [seriesTensorPair, mul_add]

end Tensor

section Deformation

variable {k : Type*} [Field k]

local notation "P" => Plane k
local notation "Q" => PlaneTensorSquare k
local notation "tens" => seriesTensorPair (k := k)
local notation "a" => parameterExp (k := k) (planeX : P)
local notation "ainv" => parameterExp (k := k) (-(planeX : P))
local notation "cx" => (C (planeX : P))
local notation "cy" => (C (planeY : P))

private def planeComulCoefficients : P →ₐ[k] PowerSeries Q :=
  MvPolynomial.aeval fun i => if i = 0 then tens cx 1 + tens 1 cx else tens cy 1 + tens a cy

private def planeAntipodeCoefficients : P →ₐ[k] PowerSeries P :=
  MvPolynomial.aeval fun i => if i = 0 then -cx else -ainv * cy

private abbrev completedComul : PowerSeries P →ₐ[PowerSeries k] PowerSeries Q :=
  extendSeries planeComulCoefficients

private abbrev completedCounit : PowerSeries P →ₐ[PowerSeries k] PowerSeries k :=
  seriesMap primitivePlaneCounit

private abbrev completedAntipode : PowerSeries P →ₐ[PowerSeries k] PowerSeries P :=
  extendSeries planeAntipodeCoefficients

@[simp] private theorem completedComul_x : completedComul (k := k) cx = tens cx 1 + tens 1 cx := by
  simp [planeComulCoefficients]

@[simp] private theorem completedComul_y : completedComul (k := k) cy = tens cy 1 + tens a cy := by
  simp [planeComulCoefficients, show (1 : Fin 2) ≠ 0 by decide]

@[simp] private theorem completedCounit_x : completedCounit (k := k) cx = 0 := by
  change seriesMap (k := k) primitivePlaneCounit _ = _
  rw [seriesMap_C]
  simp [primitivePlaneCounit]

@[simp] private theorem completedCounit_y : completedCounit (k := k) cy = 0 := by
  change seriesMap (k := k) primitivePlaneCounit _ = _
  rw [seriesMap_C]
  simp [primitivePlaneCounit]

@[simp] private theorem completedAntipode_x : completedAntipode (k := k) cx = -cx := by
  simp [planeAntipodeCoefficients]

@[simp] private theorem completedAntipode_y : completedAntipode (k := k) cy = -ainv * cy := by
  simp [planeAntipodeCoefficients, show (1 : Fin 2) ≠ 0 by decide]

@[simp] private theorem completedCounit_exp : completedCounit (k := k) a = 1 := by
  change seriesMap (k := k) primitivePlaneCounit _ = _
  rw [seriesMap_parameterExp]
  simp [primitivePlaneCounit]

@[simp] private theorem completedAntipode_exp : completedAntipode (k := k) a = ainv := by
  apply extendSeries_parameterExp
  simp [planeAntipodeCoefficients]

private theorem completedComul_exp [CharZero k] :
    completedComul (k := k) a = tens a a := by
  let l : P →ₐ[k] Q := Algebra.TensorProduct.includeLeft
  let r : P →ₐ[k] Q := Algebra.TensorProduct.includeRight
  calc
    completedComul (k := k) a = parameterExp (k := k) (l planeX + r planeX) := by
      apply extendSeries_parameterExp
      simp [planeComulCoefficients, seriesTensorPair, l, r]
    _ = tens a a := by rw [parameterExp_add]; simp [seriesTensorPair, l, r]

private theorem completed_plane_ext {D : Type*} [CommRing D] [Algebra k D]
    (f g : PowerSeries P →ₐ[PowerSeries k] PowerSeries D)
    (hf : SeriesContinuous f) (hg : SeriesContinuous g) (hx : f cx = g cx)
    (hy : f cy = g cy) : f = g :=
  seriesPolynomialExt f g hf hg (Fin.forall_fin_two.mpr ⟨hx, hy⟩)

private abbrev completedComulLeft :
    PowerSeries Q →ₐ[PowerSeries k] PowerSeries (PlaneTensorCube k) :=
  tensorSeriesMap (onSeriesConstants completedComul) (seriesConstants k P)

private abbrev completedComulRight :
    PowerSeries Q →ₐ[PowerSeries k] PowerSeries (PlaneTensorCubeRight k) :=
  tensorSeriesMap (seriesConstants k P) (onSeriesConstants completedComul)

private theorem completedComulLeft_extends :
    ExtendsLeftPlaneTensor (completedComul (k := k)) completedComulLeft :=
  extendSeries_extends _

private theorem completedComulRight_extends :
    ExtendsRightPlaneTensor (completedComul (k := k)) completedComulRight :=
  extendSeries_extends _

private theorem completedComulLeft_pair (p q : PowerSeries P) :
    completedComulLeft (tens p q) = tens (completedComul p) q :=
  seriesTensorMaps _ _ _ _ _ (extends_onSeriesConstants _ (extendSeries_continuous _))
    id_series_extends completedComulLeft_extends p q

private theorem completedComulRight_pair (p q : PowerSeries P) :
    completedComulRight (tens p q) = tens p (completedComul q) :=
  seriesTensorMaps _ _ _ _ _ id_series_extends
    (extends_onSeriesConstants _ (extendSeries_continuous _)) completedComulRight_extends p q

set_option maxHeartbeats 800000 in
private theorem completedComul_coassoc [CharZero k] (p : PowerSeries P) :
    seriesMap (k := k) (Algebra.TensorProduct.assoc k k k P P P).toAlgHom
      (completedComulLeft (completedComul p)) = completedComulRight (completedComul p) := by
  let e : PlaneTensorCube k →ₐ[k] PlaneTensorCubeRight k :=
    (Algebra.TensorProduct.assoc k k k P P P).toAlgHom
  let E := seriesMap (k := k) (A := PlaneTensorCube k) (B := PlaneTensorCubeRight k) e
  have hassoc (u v w : PowerSeries P) :
      E (tens (tens u v) w) = tens u (tens v w) :=
    seriesTensorAssociativity u v w
  have hlast (w : PowerSeries P) :
      E (tens (1 : PowerSeries Q) w) = tens (1 : PowerSeries P) (tens (1 : PowerSeries P) w) := by
    simpa only [seriesTensorPair_one_one] using hassoc 1 1 w
  have heq : E.comp ((completedComulLeft (k := k)).comp (completedComul (k := k))) =
      (completedComulRight (k := k)).comp (completedComul (k := k)) := by
    apply completed_plane_ext (k := k) (D := PlaneTensorCubeRight k)
    · exact continuous_comp_series (g := E) (f := (completedComulLeft (k := k)).comp (completedComul (k := k)))
        (seriesMap_continuous (A := PlaneTensorCube k) (B := PlaneTensorCubeRight k) e) (continuous_comp_series
          (g := completedComulLeft (k := k)) (f := completedComul (k := k))
          completedComulLeft_extends.1 (extendSeries_continuous _))
    · exact continuous_comp_series (g := completedComulRight (k := k)) (f := completedComul (k := k))
        completedComulRight_extends.1 (extendSeries_continuous _)
    · simp only [AlgHom.comp_apply, completedComul_x, map_add,
        completedComulLeft_pair, completedComulRight_pair, map_one,
        seriesTensorPair_add_left, seriesTensorPair_add_right, hassoc, hlast,
        seriesTensorPair_one_one, add_assoc]
    · simp only [AlgHom.comp_apply, completedComul_y, completedComul_exp, map_add,
        completedComulLeft_pair, completedComulRight_pair, map_one,
        seriesTensorPair_add_left, seriesTensorPair_add_right, hassoc,
        seriesTensorPair_one_one, add_assoc]
  exact AlgHom.congr_fun heq p

private abbrev completedUnitCounit : PowerSeries P →ₐ[PowerSeries k] PowerSeries P :=
  completedPlaneUnit.comp completedCounit

private theorem completedUnitCounit_continuous :
    SeriesContinuous (completedUnitCounit (k := k)) :=
  continuous_comp_series (g := completedPlaneUnit) (f := completedCounit)
    (seriesMap_continuous _) (seriesMap_continuous _)

private abbrev planeSeriesId : PowerSeries P →ₐ[PowerSeries k] PowerSeries P :=
  AlgHom.id _ _

private theorem left_counit_completed :
    (seriesProductMap completedUnitCounit planeSeriesId).comp (completedComul (k := k)) =
      planeSeriesId := by
  have h := seriesProductMap_pair (k := k) completedUnitCounit planeSeriesId
    completedUnitCounit_continuous continuous_id_series
  apply completed_plane_ext
  · exact continuous_comp_series (g := seriesProductMap completedUnitCounit planeSeriesId)
      (f := completedComul) (seriesProductMap_extends _ _).1 (extendSeries_continuous _)
  · exact continuous_id_series
  · simp only [AlgHom.comp_apply, completedComul_x, map_add, h, AlgHom.id_apply, map_one,
      completedCounit_x, map_zero, zero_mul, one_mul, zero_add]
  · simp only [AlgHom.comp_apply, completedComul_y, map_add, h, AlgHom.id_apply, map_one,
      completedCounit_y, completedCounit_exp, map_zero, zero_mul, one_mul, zero_add]

private theorem right_counit_completed :
    (seriesProductMap planeSeriesId completedUnitCounit).comp (completedComul (k := k)) =
      planeSeriesId := by
  have h := seriesProductMap_pair (k := k) planeSeriesId completedUnitCounit
    continuous_id_series completedUnitCounit_continuous
  apply completed_plane_ext
  · exact continuous_comp_series (g := seriesProductMap planeSeriesId completedUnitCounit)
      (f := completedComul) (seriesProductMap_extends _ _).1 (extendSeries_continuous _)
  · exact continuous_id_series
  · simp only [AlgHom.comp_apply, completedComul_x, map_add, h, AlgHom.id_apply, map_one,
      completedCounit_x, map_zero, mul_zero, mul_one, add_zero]
  · simp only [AlgHom.comp_apply, completedComul_y, map_add, h, AlgHom.id_apply, map_one,
      completedCounit_y, map_zero, mul_zero, mul_one, add_zero]

private theorem left_antipode_completed :
    (seriesProductMap completedAntipode planeSeriesId).comp (completedComul (k := k)) =
      completedUnitCounit := by
  have h := seriesProductMap_pair (k := k) completedAntipode planeSeriesId
    (extendSeries_continuous _) continuous_id_series
  apply completed_plane_ext
  · exact continuous_comp_series (g := seriesProductMap completedAntipode planeSeriesId)
      (f := completedComul) (seriesProductMap_extends _ _).1 (extendSeries_continuous _)
  · exact completedUnitCounit_continuous
  · simp only [AlgHom.comp_apply, completedComul_x, map_add, h, AlgHom.id_apply, map_one,
      completedAntipode_x, completedCounit_x, map_zero, mul_one, one_mul, neg_add_cancel]
  · simp only [AlgHom.comp_apply, completedComul_y, map_add, h, AlgHom.id_apply, map_one,
      completedAntipode_y, completedAntipode_exp, completedCounit_y, map_zero, mul_one,
      neg_mul, neg_add_cancel]

private theorem right_antipode_completed [CharZero k] :
    (seriesProductMap planeSeriesId completedAntipode).comp (completedComul (k := k)) =
      completedUnitCounit := by
  have h := seriesProductMap_pair (k := k) planeSeriesId completedAntipode
    continuous_id_series (extendSeries_continuous _)
  apply completed_plane_ext
  · exact continuous_comp_series (g := seriesProductMap planeSeriesId completedAntipode)
      (f := completedComul) (seriesProductMap_extends _ _).1 (extendSeries_continuous _)
  · exact completedUnitCounit_continuous
  · simp only [AlgHom.comp_apply, completedComul_x, map_add, h, AlgHom.id_apply, map_one,
      completedAntipode_x, completedCounit_x, map_zero, mul_one, one_mul, add_neg_cancel]
  · have hmul : a * ainv = (1 : PowerSeries P) := by
      rw [← parameterExp_add, add_neg_cancel, parameterExp_zero]
    simp only [AlgHom.comp_apply, completedComul_y, map_add, h, AlgHom.id_apply, map_one,
      completedAntipode_y, completedCounit_y, map_zero, mul_one, neg_mul, mul_neg,
      ← mul_assoc, hmul, one_mul, add_neg_cancel]

@[simp] private theorem primitivePlaneComul_X (i : Fin 2) :
    primitivePlaneComul (k := k) (MvPolynomial.X i) =
      MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i :=
  MvPolynomial.aeval_X _ _

@[simp] private theorem primitivePlaneCounit_X (i : Fin 2) :
    primitivePlaneCounit (k := k) (MvPolynomial.X i) = 0 :=
  MvPolynomial.aeval_X _ _

@[simp] private theorem primitivePlaneAntipode_X (i : Fin 2) :
    primitivePlaneAntipode (k := k) (MvPolynomial.X i) = -MvPolynomial.X i :=
  MvPolynomial.aeval_X _ _

private theorem constantCoeff_seriesMap {A D : Type*} [CommRing A] [CommRing D]
    [Algebra k A] [Algebra k D] (f : A →ₐ[k] D) (p : PowerSeries A) :
    constantCoeff (seriesMap f p) = f (constantCoeff p) := by
  simpa only [coeff_zero_eq_constantCoeff_apply] using seriesMap_coeff f p 0

private theorem constantCoeff_plane_pair (p q : PowerSeries P) :
    constantCoeff (tens p q) = constantCoeff p ⊗ₜ[k] constantCoeff q := by
  simp [seriesTensorPair, constantCoeff_seriesMap, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]

private def constantCoeffOver {D : Type*} [CommRing D] [Algebra k D] :
    PowerSeries D →ₐ[k] D where
  toRingHom := constantCoeff
  commutes' c := by
    change constantCoeff (algebraMap k (PowerSeries D) c) = algebraMap k D c
    rw [PowerSeries.algebraMap_apply, constantCoeff_C]

private theorem extendSeries_specialize {D : Type*} [CommRing D] [Algebra k D]
    (f : P →ₐ[k] PowerSeries D) (g : P →ₐ[k] D)
    (h : (constantCoeffOver (k := k)).comp f = g) (p : PowerSeries P) :
    constantCoeff (extendSeries f p) = g (constantCoeff p) := by
  calc
    constantCoeff (extendSeries f p) = constantCoeff (f (constantCoeff p)) := by
      simp only [← coeff_zero_eq_constantCoeff_apply, extendSeries_coeff, Nat.zero_add, Finset.sum_range_one,
        Nat.zero_sub]
    _ = g (constantCoeff p) := AlgHom.congr_fun h (constantCoeff p)

private theorem specialize_completedComul (p : PowerSeries P) :
    constantCoeff (completedComul p) = primitivePlaneComul (constantCoeff p) := by
  apply extendSeries_specialize
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_fin_two]
  constructor
  · change constantCoeff (planeComulCoefficients (k := k) planeX) = primitivePlaneComul planeX
    rw [← extendSeries_C]
    change constantCoeff (completedComul (k := k) cx) = primitivePlaneComul planeX
    simp only [completedComul_x, map_add, constantCoeff_plane_pair, constantCoeff_C,
      constantCoeff_one, primitivePlaneComul_X]
  · change constantCoeff (planeComulCoefficients (k := k) planeY) = primitivePlaneComul planeY
    rw [← extendSeries_C]
    change constantCoeff (completedComul (k := k) cy) = primitivePlaneComul planeY
    simp only [completedComul_y, map_add, constantCoeff_plane_pair, constantCoeff_C,
      constantCoeff_one, constantCoeff_parameterExp, primitivePlaneComul_X]

private theorem specialize_completedAntipode (p : PowerSeries P) :
    constantCoeff (completedAntipode p) = primitivePlaneAntipode (constantCoeff p) := by
  apply extendSeries_specialize
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_fin_two]
  constructor
  · change constantCoeff (planeAntipodeCoefficients (k := k) planeX) = primitivePlaneAntipode planeX
    rw [← extendSeries_C]
    change constantCoeff (completedAntipode (k := k) cx) = primitivePlaneAntipode planeX
    simp only [completedAntipode_x, map_neg, constantCoeff_C, primitivePlaneAntipode_X]
  · change constantCoeff (planeAntipodeCoefficients (k := k) planeY) = primitivePlaneAntipode planeY
    rw [← extendSeries_C]
    change constantCoeff (completedAntipode (k := k) cy) = primitivePlaneAntipode planeY
    simp only [completedAntipode_y, map_mul, map_neg, constantCoeff_parameterExp,
      constantCoeff_C, primitivePlaneAntipode_X, neg_one_mul]

@[instance_reducible] private def primitivePlaneBialgebra : Bialgebra k P := by
  refine Bialgebra.ofAlgHom primitivePlaneComul primitivePlaneCounit ?_ ?_ ?_
  · apply MvPolynomial.algHom_ext
    intro i
    simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.assoc_tmul,
      TensorProduct.add_tmul, TensorProduct.tmul_add,
      Algebra.TensorProduct.one_def, add_assoc]
  · apply MvPolynomial.algHom_ext
    intro i
    simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_symm_apply]
  · apply MvPolynomial.algHom_ext
    intro i
    simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_symm_apply]

@[instance_reducible] private def primitivePlaneHopfAlgebra : HopfAlgebra k P := by
  letI : Bialgebra k P := primitivePlaneBialgebra
  refine HopfAlgebra.ofAlgHom primitivePlaneAntipode ?_ ?_
  · change (Algebra.TensorProduct.lift primitivePlaneAntipode (AlgHom.id k P)
        (fun _ _ => Commute.all _ _)).comp primitivePlaneComul =
      (Algebra.ofId k P).comp primitivePlaneCounit
    apply MvPolynomial.algHom_ext
    intro i
    simp [Algebra.TensorProduct.lift_tmul]
  · change (Algebra.TensorProduct.lift (AlgHom.id k P) primitivePlaneAntipode
        (fun _ _ => Commute.all _ _)).comp primitivePlaneComul =
      (Algebra.ofId k P).comp primitivePlaneCounit
    apply MvPolynomial.algHom_ext
    intro i
    simp [Algebra.TensorProduct.lift_tmul]

private theorem primitivePlaneComul_flip :
    (Algebra.TensorProduct.comm k P P).toAlgHom.comp primitivePlaneComul = primitivePlaneComul := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [Algebra.TensorProduct.comm_tmul, add_comm]

/-- The skew-primitive formal deformation with the ordinary primitive specialization. -/
theorem completedPlaneHopf : CompletedPlaneHopfSpec := by
  intro k _ _
  exact ⟨{
    comul := completedComul
    counit := completedCounit
    antipode := completedAntipode
    comul_continuous := extendSeries_continuous _
    counit_continuous := seriesMap_continuous _
    antipode_continuous := extendSeries_continuous _
    comul_x := completedComul_x
    comul_y := completedComul_y
    counit_x := completedCounit_x
    counit_y := completedCounit_y
    antipode_x := completedAntipode_x
    antipode_y := completedAntipode_y
    exp_groupLike := completedComul_exp
    counit_exp := completedCounit_exp
    coassociative := ⟨completedComulLeft, completedComulRight, completedComulLeft_extends,
      completedComulRight_extends, completedComul_coassoc⟩
    left_counit := ⟨_, seriesProductMap_extends _ _, left_counit_completed⟩
    right_counit := ⟨_, seriesProductMap_extends _ _, right_counit_completed⟩
    left_antipode := ⟨_, seriesProductMap_extends _ _, left_antipode_completed⟩
    right_antipode := ⟨_, seriesProductMap_extends _ _, right_antipode_completed⟩
    specialize_comul := specialize_completedComul
    specialize_counit := constantCoeff_seriesMap primitivePlaneCounit
    specialize_antipode := specialize_completedAntipode
    primitive_hopf := ⟨primitivePlaneHopfAlgebra, rfl, fun _ => ⟨HEq.rfl, rfl, rfl⟩⟩
    primitive_cocommutative := primitivePlaneComul_flip
  }⟩

end Deformation

end

end LieNotes.BialgebraDeformation
