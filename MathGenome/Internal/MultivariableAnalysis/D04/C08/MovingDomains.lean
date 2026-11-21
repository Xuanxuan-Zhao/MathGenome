import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.MovingDomains
import MathGenome.Internal.MultivariableAnalysis.D04.C08.ProperDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C08.PositiveJacobian
import MathGenome.Internal.MultivariableAnalysis.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C07.LinearVolume
import MathGenome.Internal.MultivariableAnalysis.D04.C11.EuclideanVectorOperators
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open Set Filter Topology
open scoped Matrix.Norms.Elementwise
namespace D04.MovingDomains
open JordanRegions
open Specs.D04.C08.MovingDomains.Model

variable {m n : ℕ} {P : Set (E m)} {W S : Set (E n)} {e : Family m n}

lemma forward_regular (he : RegularFamily P W e) {p : E m} (hp : p ∈ P) :
    ContDiffOn ℝ 1 (e p) (e p).source := by
  rw [he.1 p hp]
  exact he.2.1.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun x hx => ⟨hp, hx⟩)

lemma spatialMatrix_det (e : Family m n) (p : E m) (x : E n) :
    (spatialMatrix e p x).det = (fderiv ℝ (e p) x).det := by
  change (matrixOfLinearMap (fderiv ℝ (e p) x).toLinearMap).det = _
  rw [← LinearMap.det_toLin (standardBasis n)]
  exact congrArg LinearMap.det (matrix_linear_roundtrip _)

theorem jordan_image : Specs.D04.C08.MovingDomains.jordan_imageType := by
  intro m n S P W e hS _hP _hW hSW he p hp
  apply (RegionSubstitution.jordan_image (e p) (forward_regular he hp)
    (he.2.2.1 p hp) S hS (jordan_bounded hS).isCompact_closure ?_).2
  simpa only [he.1 p hp] using hSW


lemma scalar_continuous_closure_integrable (hS : Jordan S) (g : closure S → ℝ)
    (hg : Continuous g) :
    RegionIntegrable (fun x : S => g ⟨x, subset_closure x.property⟩) := by
  by_cases hn : n = 0
  · subst n
    exact region_integrable_zero_dim _ _
  · exact integrable_continuous_on_closure (Nat.pos_of_ne_zero hn) hS g hg

lemma density_continuous (he : RegularFamily P W e) {p : E m} (hp : p ∈ P)
    (hSW : closure S ⊆ W) (O : Set (E m × E n)) (f : E m × E n → ℝ)
    (hf : ContinuousOn f O) (hgraph : ∀ x ∈ closure S, (p, e p x) ∈ O) :
    Continuous (fun x : closure S => f (p, e p x)) := by
  have hsrc : ∀ x : closure S, (x : E n) ∈ (e p).source := by
    intro x
    rw [he.1 p hp]
    exact hSW x.property
  exact hf.comp_continuous (continuous_const.prodMk
    ((e p).continuousOn.comp_continuous continuous_subtype_val hsrc))
    (fun x => hgraph x x.property)

theorem pullback : Specs.D04.C08.MovingDomains.pullbackType := by
  intro m n S P W e O f hS _hP _hW hSW he _hO hf hgraph p hp
  have he1 := forward_regular he hp
  have hei := he.2.2.1 p hp
  have hsrc : closure S ⊆ (e p).source := by simpa only [he.1 p hp] using hSW
  have hfc := density_continuous he hp hSW O f hf.continuousOn (hgraph p hp)
  have hK := (jordan_bounded hS).isCompact_closure
  let : CompactSpace (closure S) := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := (isCompact_range hfc).isBounded.exists_norm_le
  have hb : RegionBounded (fun y : (e p) '' S => f (p, y)) := by
    refine ⟨M, ?_⟩
    rintro ⟨y, x, hx, rfl⟩
    exact hM _ ⟨⟨x, subset_closure hx⟩, rfl⟩
  have hJ : Continuous (fun x : closure S => |(fderiv ℝ (e p) x).det|) :=
    (ContinuousLinearMap.continuous_det.comp
      (he1.continuousOn_fderiv_of_isOpen (e p).open_source le_rfl
        |>.comp_continuous continuous_subtype_val (fun x => hsrc x.property))).abs
  have hgi := scalar_continuous_closure_integrable hS _ (hfc.mul hJ)
  have hs := RegionSubstitution.region_substitution (e p) he1 hei S hS hK hsrc
    (fun y : (e p) '' S => f (p, y)) hb
  have hfi := hs.2.1.mpr hgi
  refine ⟨hfi, ?_, ?_⟩
  · simpa only [Pi.mul_apply, spatialMatrix_det] using hgi
  · simpa only [movingIntegral, spatialMatrix_det] using hs.2.2 (Or.inl hfi)

lemma spatialMatrix_ne_zero (he : RegularFamily P W e) {p : E m} (hp : p ∈ P)
    {x : E n} (hx : x ∈ W) : (spatialMatrix e p x).det ≠ 0 := by
  rw [spatialMatrix_det]
  apply RiemannSubstitution.jacobian_ne_zero (e p).toHomeomorphSourceTarget
    (e p) (e p).symm (e p).open_source (e p).open_target
    (forward_regular he hp) (he.2.2.1 p hp) (fun _ => rfl) (fun _ => rfl) x
  simpa only [he.1 p hp] using hx

lemma jacobian_parameter_derivative (he : RegularFamily P W e) {p : E m} (hp : p ∈ P)
    {x : E n} (hx : x ∈ W) (h : E m) :
    fderiv ℝ (fun q => |(spatialMatrix e q x).det|) p h =
      |(spatialMatrix e p x).det| *
        ((spatialMatrix e p x)⁻¹ * parameterJacobian e p x h).trace :=
  (PositiveJacobian.positive_jacobian_derivative_at (fun q => spatialMatrix e q x) p
    (he.2.2.2.1 p hp x hx) (spatialMatrix_ne_zero he hp hx)).2 h


section PartialDerivatives
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma partial_left {g : X × Y → Z} {p : X} {x : Y}
    (hg : DifferentiableAt ℝ g (p, x)) :
    fderiv ℝ (fun q => g (q, x)) p =
      (fderiv ℝ g (p, x)).comp (ContinuousLinearMap.inl ℝ X Y) := by
  exact (hg.hasFDerivAt.comp p
    ((hasFDerivAt_id p).prodMk (hasFDerivAt_const x p))).fderiv

lemma partial_right {g : X × Y → Z} {p : X} {x : Y}
    (hg : DifferentiableAt ℝ g (p, x)) :
    fderiv ℝ (fun y => g (p, y)) x =
      (fderiv ℝ g (p, x)).comp (ContinuousLinearMap.inr ℝ X Y) := by
  exact (hg.hasFDerivAt.comp x
    ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))).fderiv

lemma continuous_partial_left {U : Set (X × Y)} (hU : IsOpen U)
    {g : X × Y → Z} (hg : ContDiffOn ℝ 1 g U) :
    ContinuousOn (fun z : X × Y => fderiv ℝ (fun q => g (q, z.2)) z.1) U := by
  apply ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).clm_comp continuousOn_const).congr
  intro z hz
  exact partial_left ((hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))

lemma continuous_partial_right {U : Set (X × Y)} (hU : IsOpen U)
    {g : X × Y → Z} (hg : ContDiffOn ℝ 1 g U) :
    ContinuousOn (fun z : X × Y => fderiv ℝ (fun y => g (z.1, y)) z.2) U := by
  apply ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).clm_comp continuousOn_const).congr
  intro z hz
  exact partial_right ((hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
end PartialDerivatives

lemma scalar_parameter_derivative (hS : Jordan S) (hP : IsOpen P)
    (g : closure S → E m → ℝ) (A : closure S → E m → E m →L[ℝ] ℝ)
    (hg : Continuous (fun z : closure S × P => g z.1 z.2))
    (hA : Continuous (fun z : closure S × P => A z.1 z.2))
    (hd : ∀ x : S, ∀ p ∈ P, HasFDerivAt (g ⟨x, subset_closure x.property⟩)
      (A ⟨x, subset_closure x.property⟩ p) p) :
    CrOn 1 P (fun p => regionIntegral (fun x : S => g ⟨x, subset_closure x.property⟩ p)) ∧
    ∀ p ∈ P, ∀ h : E m,
      RegionIntegrable (fun x : S => A ⟨x, subset_closure x.property⟩ p h) ∧
      fderiv ℝ (fun p => regionIntegral (fun x : S => g ⟨x, subset_closure x.property⟩ p)) p h =
        regionIntegral (fun x : S => A ⟨x, subset_closure x.property⟩ p h) := by
  let L : ℝ →L[ℝ] E 1 := ContinuousLinearMap.toSpanSingleton ℝ (standardBasis 1 0)
  let R : E 1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0
  have hL (a : ℝ) : R (L a) = a := by
    simp [L, R, standardBasis_apply]
  have hI (a : S → ℝ) : R (vectorRegionIntegral (fun x => L (a x))) = regionIntegral a := by
    change regionIntegral (fun x => R (L (a x))) = _
    simp only [hL]
  have hres := ProperDerivative.continuous_parameter_derivative hS hP
    (fun x p => L (g x p)) (fun x p => L.comp (A x p))
    (L.continuous.comp hg) (continuous_const.clm_comp hA)
    (fun x p hp => L.hasFDerivAt.comp p (hd x p hp))
  dsimp only at hres
  have hF : (fun p => R (vectorRegionIntegral
      (fun x : S => L (g ⟨x, subset_closure x.property⟩ p)))) =
      (fun p => regionIntegral (fun x : S => g ⟨x, subset_closure x.property⟩ p)) := by
    funext p
    change regionIntegral (fun x : S => R (L (g ⟨x, subset_closure x.property⟩ p))) = _
    simp only [hL]
  have hCr := (crOn_iff_contDiffOn 1 P _ hP).mp hres.2.1
  have hRc := (crOn_iff_contDiffOn 1 P _ hP).mpr (R.contDiff.comp_contDiffOn hCr)
  simp only [Function.comp_def] at hRc
  rw [hF] at hRc
  refine ⟨hRc, ?_⟩
  intro p hp h
  have hcont : Continuous (fun x : closure S => A x p h) :=
    (continuous_clm_apply.mp (hA.comp (continuous_id.prodMk (continuous_const (y := (⟨p, hp⟩ : P)))))) h
  have hi := scalar_continuous_closure_integrable hS _ hcont
  refine ⟨hi, ?_⟩
  have hder := R.hasFDerivAt.comp p (hres.2.2.2 p hp).1
  have he := congrArg R ((hres.2.2.2 p hp).2 h)
  have he' : R ((ProperDerivative.operatorRegionIntegral
      (fun x : S => L.comp (A ⟨x, subset_closure x.property⟩ p))) h) =
      regionIntegral (fun x : S => A ⟨x, subset_closure x.property⟩ p h) := by
    rw [← (hres.2.2.2 p hp).1.fderiv]
    simpa only [ContinuousLinearMap.comp_apply, hI] using he
  have hder' := hder
  simp only [Function.comp_def] at hder'
  rw [hF] at hder'
  rw [hder'.fderiv]
  exact he'


lemma spatialMatrix_continuous (hP : IsOpen P) (hW : IsOpen W)
    (he : RegularFamily P W e) :
    ContinuousOn (fun z : E m × E n => spatialMatrix e z.1 z.2) (P ×ˢ W) := by
  have hc := continuous_partial_right (hP.prod hW) he.2.1
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  change ContinuousOn (fun z : E m × E n =>
    D04.matrixOfLinearMap (fderiv ℝ (e z.1) z.2).toLinearMap i j) (P ×ˢ W)
  simp only [matrixOfLinearMap_apply]
  exact
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp_continuousOn
      (hc.clm_apply (continuousOn_const (c := standardBasis n j)))

private lemma determinant_contDiff :
    ContDiff ℝ 1 (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (Matrix.entryLinearMap ℝ ℝ (σ i) i).toContinuousLinearMap.contDiff

private def absDet (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := |A.det|

private lemma absDet_contDiffAt (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ContDiffAt ℝ 1 absDet A := determinant_contDiff.contDiffAt.abs hA

private def pulledDerivative (e : Family m n) (f : E m × E n → ℝ)
    (p : E m) (x : E n) : E m →L[ℝ] ℝ :=
  f (p, e p x) • ((fderiv ℝ absDet (spatialMatrix e p x)).comp (parameterJacobian e p x)) +
    |(spatialMatrix e p x).det| • ((fderiv ℝ f (p, e p x)).comp
      ((ContinuousLinearMap.id ℝ (E m)).prod (fderiv ℝ (fun q => e q x) p)))

lemma parameter_differentiable (he : RegularFamily P W e)
    (hP : IsOpen P) (hW : IsOpen W) {p : E m} (hp : p ∈ P) {x : E n} (hx : x ∈ W) :
    DifferentiableAt ℝ (fun q => e q x) p := by
  have hd : DifferentiableAt ℝ (fun z : E m × E n => e z.1 z.2) (p, x) :=
    (he.2.1.contDiffAt ((hP.prod hW).mem_nhds ⟨hp, hx⟩)).differentiableAt (by norm_num)
  have hin : HasFDerivAt (fun q : E m => (q, x)) (ContinuousLinearMap.inl ℝ (E m) (E n)) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const x p)
  exact hd.comp p hin.differentiableAt

private lemma pulledDerivative_hasFDerivAt (he : RegularFamily P W e)
    (hP : IsOpen P) (hW : IsOpen W) (O : Set (E m × E n)) (hO : IsOpen O)
    (f : E m × E n → ℝ) (hf : ContDiffOn ℝ 1 f O)
    {p : E m} (hp : p ∈ P) {x : E n} (hx : x ∈ W) (hgraph : (p, e p x) ∈ O) :
    HasFDerivAt (fun q => f (q, e q x) * |(spatialMatrix e q x).det|)
      (pulledDerivative e f p x) p := by
  have hd := parameter_differentiable he hP hW hp hx
  have hdf := (hf.contDiffAt (hO.mem_nhds hgraph)).differentiableAt (by norm_num)
  have hdg := hdf.hasFDerivAt.comp p ((hasFDerivAt_id p).prodMk hd.hasFDerivAt)
  have hdJ := ((absDet_contDiffAt _ (spatialMatrix_ne_zero he hp hx)).differentiableAt
    (by norm_num)).hasFDerivAt.comp p (he.2.2.2.1 p hp x hx).hasFDerivAt
  exact hdg.mul hdJ

private lemma pulledDerivative_apply (he : RegularFamily P W e)
    (hP : IsOpen P) (hW : IsOpen W) (O : Set (E m × E n)) (hO : IsOpen O)
    (f : E m × E n → ℝ) (hf : ContDiffOn ℝ 1 f O)
    {p : E m} (hp : p ∈ P) {x : E n} (hx : x ∈ W) (hgraph : (p, e p x) ∈ O)
    (h : E m) : pulledDerivative e f p x h = referenceIntegrand e f p h x := by
  have hdf := (hf.contDiffAt (hO.mem_nhds hgraph)).differentiableAt (by norm_num)
  have hdA := he.2.2.2.1 p hp x hx
  have hdJ := ((absDet_contDiffAt _ (spatialMatrix_ne_zero he hp hx)).differentiableAt
    (by norm_num)).hasFDerivAt.comp p hdA.hasFDerivAt
  have hJ := jacobian_parameter_derivative he hp hx h
  dsimp only [Function.comp_def, absDet] at hdJ
  rw [hdJ.fderiv] at hJ
  dsimp only [pulledDerivative, referenceIntegrand]
  simp only [add_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  change (fderiv ℝ absDet (spatialMatrix e p x)) (parameterJacobian e p x h) = _ at hJ
  rw [hJ, partial_left hdf, partial_right hdf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply]
  have hadd := (fderiv ℝ f (p, e p x)).map_add (h, 0)
    (0, fderiv ℝ (fun q => e q x) p h)
  simp only [Prod.mk_add_mk, add_zero, zero_add] at hadd
  rw [hadd]
  ring


private lemma pulledDerivative_continuous (hP : IsOpen P) (hW : IsOpen W)
    (he : RegularFamily P W e) (hSW : closure S ⊆ W)
    (O : Set (E m × E n)) (hO : IsOpen O) (f : E m × E n → ℝ)
    (hf : ContDiffOn ℝ 1 f O)
    (hgraph : ∀ p ∈ P, ∀ x ∈ closure S, (p, e p x) ∈ O) :
    Continuous (fun z : closure S × P => pulledDerivative e f z.2 z.1) := by
  have hcoord : Continuous (fun z : closure S × P => ((z.2 : E m), (z.1 : E n))) :=
    continuous_snd.subtype_val.prodMk continuous_fst.subtype_val
  have hsub (z : closure S × P) : ((z.2 : E m), (z.1 : E n)) ∈ P ×ˢ W :=
    ⟨z.2.property, hSW z.1.property⟩
  have hPhi := he.2.1.continuousOn.comp_continuous hcoord hsub
  have hAc := (spatialMatrix_continuous hP hW he).comp_continuous hcoord hsub
  have hBc := he.2.2.2.2.comp_continuous hcoord hsub
  have hPc := (continuous_partial_left (hP.prod hW) he.2.1).comp_continuous hcoord hsub
  have hmap : Continuous (fun z : closure S × P => ((z.2 : E m), e z.2 z.1)) :=
    continuous_snd.subtype_val.prodMk hPhi
  have hmapO (z : closure S × P) : ((z.2 : E m), e z.2 z.1) ∈ O :=
    hgraph z.2 z.2.property z.1 z.1.property
  have hfc := hf.continuousOn.comp_continuous hmap hmapO
  have hdfc := (hf.continuousOn_fderiv_of_isOpen hO le_rfl).comp_continuous hmap hmapO
  have hJc := hAc.matrix_det.abs
  have hdJc : Continuous (fun z : closure S × P => fderiv ℝ absDet (spatialMatrix e z.2 z.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((absDet_contDiffAt _ (spatialMatrix_ne_zero he z.2.property (hSW z.1.property))).continuousAt_fderiv
      (by norm_num)).comp
        (f := fun w : closure S × P => spatialMatrix e w.2 w.1) hAc.continuousAt
  have hprod : Continuous (fun z : closure S × P =>
      (ContinuousLinearMap.id ℝ (E m)).prod (fderiv ℝ (fun q => e q z.1) z.2)) := by
    apply continuous_clm_apply.mpr
    intro h
    exact continuous_const.prodMk (continuous_clm_apply.mp hPc h)
  exact (hfc.smul (hdJc.clm_comp hBc)).add (hJc.smul (hdfc.clm_comp hprod))

theorem moving_domain : Specs.D04.C08.MovingDomains.moving_domainType := by
  intro m n S P W e O f hS hP hW hSW he hO hf hgraph
  have hcD := pulledDerivative_continuous hP hW he hSW O hO f hf hgraph
  have hcoord : Continuous (fun z : closure S × P => ((z.2 : E m), (z.1 : E n))) :=
    continuous_snd.subtype_val.prodMk continuous_fst.subtype_val
  have hsub (z : closure S × P) : ((z.2 : E m), (z.1 : E n)) ∈ P ×ˢ W :=
    ⟨z.2.property, hSW z.1.property⟩
  have hPhi := he.2.1.continuousOn.comp_continuous hcoord hsub
  have hAc := (spatialMatrix_continuous hP hW he).comp_continuous hcoord hsub
  have hmap : Continuous (fun z : closure S × P => ((z.2 : E m), e z.2 z.1)) :=
    continuous_snd.subtype_val.prodMk hPhi
  have hmapO (z : closure S × P) : ((z.2 : E m), e z.2 z.1) ∈ O :=
    hgraph z.2 z.2.property z.1 z.1.property
  have hfc := hf.continuousOn.comp_continuous hmap hmapO
  have hc := hfc.mul hAc.matrix_det.abs
  have hr := scalar_parameter_derivative hS hP
    (fun x p => f (p, e p x) * |(spatialMatrix e p x).det|)
    (fun x p => pulledDerivative e f p x) hc hcD
    (fun x p hp => pulledDerivative_hasFDerivAt he hP hW O hO f hf hp
      (hSW (subset_closure x.property)) (hgraph p hp x (subset_closure x.property)))
  have hEq : EqOn (movingIntegral S e f)
      (fun p => regionIntegral (fun x : S => f (p, e p x) * |(spatialMatrix e p x).det|)) P :=
    fun p hp => (pullback S P W e O f hS hP hW hSW he hO hf hgraph p hp).2.2
  refine ⟨(crOn_congr 1 P _ _ hP hEq).mpr hr.1, ?_⟩
  intro p hp h
  have heq (x : S) : pulledDerivative e f p x h = referenceIntegrand e f p h x :=
    pulledDerivative_apply he hP hW O hO f hf hp (hSW (subset_closure x.property))
      (hgraph p hp x (subset_closure x.property)) h
  have hefun : (fun x : S => pulledDerivative e f p x h) =
      (fun x : S => referenceIntegrand e f p h x) := funext heq
  have hrp := hr.2 p hp h
  change RegionIntegrable (fun x : S => pulledDerivative e f p x h) ∧ _ at hrp
  refine ⟨hefun ▸ hrp.1, ?_⟩
  have hev : movingIntegral S e f =ᶠ[𝓝 p]
      (fun p => regionIntegral (fun x : S => f (p, e p x) * |(spatialMatrix e p x).det|)) :=
    Filter.eventuallyEq_of_mem (hP.mem_nhds hp) hEq
  rw [hev.fderiv_eq, hrp.2]
  exact congrArg regionIntegral hefun


lemma matrixOf_comp (A B : E n →L[ℝ] E n) :
    matrixOfLinearMap (A.comp B).toLinearMap =
      matrixOfLinearMap A.toLinearMap * matrixOfLinearMap B.toLinearMap := by
  apply (matrixLinearEquiv n n).injective
  rw [matrix_linear_roundtrip, matrix_composition, matrix_linear_roundtrip, matrix_linear_roundtrip]
  rfl

lemma matrixOf_id : matrixOfLinearMap (LinearMap.id : E n →ₗ[ℝ] E n) = 1 := by
  ext i j
  rw [matrixOfLinearMap_apply]
  simp [standardBasis_apply, Matrix.one_apply]

lemma matrixOf_matrix (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixOfLinearMap (matrixLinearEquiv n n A) = A :=
  (matrixLinearEquiv n n).symm_apply_apply A

lemma inverse_derivative_matrix (he : RegularFamily P W e)
    {p : E m} (hp : p ∈ P) {x : E n} (hx : x ∈ W) :
    matrixOfLinearMap (fderiv ℝ (e p).symm (e p x)).toLinearMap = (spatialMatrix e p x)⁻¹ := by
  have hsrc : x ∈ (e p).source := by simpa only [he.1 p hp] using hx
  have htar := (e p).map_source hsrc
  have hd := ((forward_regular he hp).contDiffAt
    ((e p).open_source.mem_nhds hsrc)).differentiableAt (by norm_num)
  have hdi := ((he.2.2.1 p hp).contDiffAt
    ((e p).open_target.mem_nhds htar)).differentiableAt (by norm_num)
  have hid : ((e p).symm ∘ (e p)) =ᶠ[𝓝 x] id :=
    Filter.eventuallyEq_of_mem ((e p).open_source.mem_nhds hsrc) (fun z hz => (e p).left_inv hz)
  have hder : (fderiv ℝ (e p).symm (e p x)).comp (fderiv ℝ (e p) x) =
      ContinuousLinearMap.id ℝ (E n) :=
    ((hdi.hasFDerivAt.comp x hd.hasFDerivAt).congr_of_eventuallyEq hid.symm).unique (hasFDerivAt_id x)
  have hmat := congrArg (fun L : E n →L[ℝ] E n => matrixOfLinearMap L.toLinearMap) hder
  rw [matrixOf_comp] at hmat
  change matrixOfLinearMap (fderiv ℝ (e p).symm (e p x)).toLinearMap *
    spatialMatrix e p x = matrixOfLinearMap (LinearMap.id : E n →ₗ[ℝ] E n) at hmat
  rw [matrixOf_id] at hmat
  exact (Matrix.inv_eq_left_inv hmat).symm

lemma velocity_divergence (he : RegularFamily P W e) (hm : MixedCommutes P W e)
    {p : E m} (hp : p ∈ P) {x : E n} (hx : x ∈ W) (h : E m) :
    DifferentiableAt ℝ (velocity e p h) (e p x) ∧
      divergence (velocity e p h) (e p x) =
        ((spatialMatrix e p x)⁻¹ * parameterJacobian e p x h).trace := by
  have hsrc : x ∈ (e p).source := by simpa only [he.1 p hp] using hx
  have hdi := ((he.2.2.1 p hp).contDiffAt
    ((e p).open_target.mem_nhds ((e p).map_source hsrc))).differentiableAt (by norm_num)
  have hdg := hm p hp x hx h
  have hdg' : HasFDerivAt (fun z => fderiv ℝ (fun q => e q z) p h)
      (LinearMap.toContinuousLinearMap (matrixLinearEquiv n n (parameterJacobian e p x h)))
      ((e p).symm (e p x)) := by
    rw [(e p).left_inv hsrc]
    exact hdg
  have hdv := hdg'.comp (e p x) hdi.hasFDerivAt
  change HasFDerivAt (velocity e p h) _ (e p x) at hdv
  refine ⟨hdv.differentiableAt, ?_⟩
  rw [divergence_eq_jacobian_trace]
  change (matrixOfLinearMap (fderiv ℝ (velocity e p h) (e p x)).toLinearMap).trace = _
  rw [hdv.fderiv, matrixOf_comp]
  change (matrixOfLinearMap (matrixLinearEquiv n n (parameterJacobian e p x h)) *
    matrixOfLinearMap (fderiv ℝ (e p).symm (e p x)).toLinearMap).trace = _
  rw [matrixOf_matrix, inverse_derivative_matrix he hp hx, Matrix.trace_mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem mixed_commutes_of_operator_derivative :
    Specs.D04.C08.MovingDomains.mixed_commutes_of_operator_derivativeType := by
  intro m n P W e hC p hp x hx h
  obtain ⟨C, hd, heq⟩ := hC p hp x hx
  have hh := hd.clm_apply (hasFDerivAt_const h x)
  simp only [ContinuousLinearMap.comp_zero, zero_add] at hh
  have hlin : C.flip h = LinearMap.toContinuousLinearMap
      (matrixLinearEquiv n n (parameterJacobian e p x h)) := by
    apply ContinuousLinearMap.ext
    intro k
    exact heq h k
  rw [hlin] at hh
  exact hh

lemma reference_eq_spatial (he : RegularFamily P W e) (hm : MixedCommutes P W e)
    (f : E m × E n → ℝ) {p : E m} (hp : p ∈ P) {x : E n} (hx : x ∈ W) (h : E m) :
    referenceIntegrand e f p h x =
      spatialIntegrand e f p h (e p x) * |(spatialMatrix e p x).det| := by
  have hsrc : x ∈ (e p).source := by simpa only [he.1 p hp] using hx
  have hv : velocity e p h (e p x) = fderiv ℝ (fun q => e q x) p h := by
    simp only [velocity, (e p).left_inv hsrc]
  dsimp only [referenceIntegrand, spatialIntegrand]
  have hdiv : Specs.D04.C11.EuclideanVectorOperators.Model.divergence (velocity e p h) (e p x) =
      ((spatialMatrix e p x)⁻¹ * parameterJacobian e p x h).trace :=
    (velocity_divergence he hm hp hx h).2
  rw [hv, hdiv]
  exact mul_comm _ _

theorem velocity_formula : Specs.D04.C08.MovingDomains.velocity_formulaType := by
  intro m n S P W e O f hS hP hW hSW he hO hf hgraph hm p hp h
  have hcD := pulledDerivative_continuous hP hW he hSW O hO f hf hgraph
  have hcA := spatialMatrix_continuous hP hW he
  have hcoord : Continuous (fun x : closure S => (p, (x : E n))) :=
    continuous_const.prodMk continuous_subtype_val
  have hsub (x : closure S) : (p, (x : E n)) ∈ P ×ˢ W := ⟨hp, hSW x.property⟩
  have hAc := hcA.comp_continuous hcoord hsub
  have hDc := hcD.comp (continuous_id.prodMk (continuous_const (y := (⟨p, hp⟩ : P))))
  have hnum : Continuous (fun x : closure S => pulledDerivative e f p x h) :=
    continuous_clm_apply.mp hDc h
  have hden : Continuous (fun x : closure S => |(spatialMatrix e p x).det|) := hAc.matrix_det.abs
  have hden0 (x : closure S) : |(spatialMatrix e p x).det| ≠ 0 :=
    abs_ne_zero.mpr (spatialMatrix_ne_zero he hp (hSW x.property))
  have hquot := hnum.div hden hden0
  have hK := (jordan_bounded hS).isCompact_closure
  let : CompactSpace (closure S) := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := (isCompact_range hquot).isBounded.exists_norm_le
  have hval (x : closure S) : spatialIntegrand e f p h (e p x) =
      pulledDerivative e f p x h / |(spatialMatrix e p x).det| := by
    rw [pulledDerivative_apply he hP hW O hO f hf hp (hSW x.property)
      (hgraph p hp x x.property) h, reference_eq_spatial he hm f hp (hSW x.property) h]
    exact (mul_div_cancel_right₀ _ (hden0 x)).symm
  have hb : RegionBounded (fun y : (e p) '' S => spatialIntegrand e f p h y) := by
    refine ⟨M, ?_⟩
    rintro ⟨y, x, hx, rfl⟩
    change ‖spatialIntegrand e f p h (e p x)‖ ≤ M
    rw [hval ⟨x, subset_closure hx⟩]
    exact hM _ ⟨⟨x, subset_closure hx⟩, rfl⟩
  have hsrc : closure S ⊆ (e p).source := by simpa only [he.1 p hp] using hSW
  have hsubstitution := RegionSubstitution.region_substitution (e p) (forward_regular he hp)
    (he.2.2.1 p hp) S hS hK hsrc (fun y => spatialIntegrand e f p h y) hb
  have hr := (moving_domain S P W e O f hS hP hW hSW he hO hf hgraph).2 p hp h
  have hw : (fun x : S => spatialIntegrand e f p h (e p x) * |(fderiv ℝ (e p) x).det|) =
      (fun x : S => referenceIntegrand e f p h x) := by
    funext x
    rw [← spatialMatrix_det]
    exact (reference_eq_spatial he hm f hp (hSW (subset_closure x.property)) h).symm
  have hfi := hsubstitution.2.1.mpr (hw ▸ hr.1)
  refine ⟨fun x hx => velocity_divergence he hm hp hx h, hfi, ?_⟩
  rw [hr.2, hsubstitution.2.2 (Or.inl hfi), hw]


lemma scalar_real_parameter_derivative (hS : Jordan S) {T : Set ℝ} (hT : IsOpen T)
    (g d : closure S → ℝ → ℝ)
    (hg : Continuous (fun z : closure S × T => g z.1 z.2))
    (hdc : Continuous (fun z : closure S × T => d z.1 z.2))
    (hd : ∀ x : S, ∀ t ∈ T, HasDerivAt (g ⟨x, subset_closure x.property⟩)
      (d ⟨x, subset_closure x.property⟩ t) t) :
    ∀ t ∈ T, HasDerivAt (fun u => regionIntegral (fun x : S => g ⟨x, subset_closure x.property⟩ u))
      (regionIntegral (fun x : S => d ⟨x, subset_closure x.property⟩ t)) t := by
  let R : E 1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0
  let L : ℝ →L[ℝ] E 1 := ContinuousLinearMap.toSpanSingleton ℝ (standardBasis 1 0)
  have hRL (a : ℝ) : R (L a) = a := by simp [R, L, standardBasis_apply]
  let Q : Set (E 1) := R ⁻¹' T
  have hQ : IsOpen Q := hT.preimage R.continuous
  have hmap : Continuous (fun z : closure S × Q => (z.1, (⟨R z.2, z.2.property⟩ : T))) :=
    continuous_fst.prodMk ((R.continuous.comp continuous_snd.subtype_val).subtype_mk _)
  have hres := scalar_parameter_derivative hS hQ
    (fun x p => g x (R p)) (fun x p => d x (R p) • R)
    (hg.comp hmap) ((hdc.comp hmap).smul continuous_const)
    (fun x p hp => by
      have hh := (hd x (R p) hp).hasFDerivAt.comp p R.hasFDerivAt
      have heq : (ContinuousLinearMap.toSpanSingleton ℝ (d ⟨x, subset_closure x.property⟩ (R p))).comp R =
          d ⟨x, subset_closure x.property⟩ (R p) • R := by
        ext h
        simp [smul_eq_mul, mul_comm]
      rw [heq] at hh
      exact hh)
  intro t ht
  have hp : L t ∈ Q := by change R (L t) ∈ T; simpa only [hRL] using ht
  have hdiff := (((crOn_iff_contDiffOn 1 Q _ hQ).mp hres.1).contDiffAt
    (hQ.mem_nhds hp)).differentiableAt (by norm_num)
  have hder := hdiff.hasFDerivAt.comp_hasDerivAt t (L.hasDerivAt (x := t))
  have hfun : ((fun p : E 1 => regionIntegral (fun x : S => g ⟨x, subset_closure x.property⟩ (R p))) ∘ L) =
      (fun u => regionIntegral (fun x : S => g ⟨x, subset_closure x.property⟩ u)) := by
    funext u
    simp only [Function.comp_apply, hRL]
  rw [hfun] at hder
  have heq := (hres.2 (L t) hp (L 1)).2
  simp only [hRL, smul_apply, smul_eq_mul, mul_one] at heq
  rw [heq] at hder
  exact hder

lemma dilation_substitution (S : Set (E n)) (hS : Jordan S) (t : ℝ) (ht : 0 < t)
    (O : Set (E n)) (f : E n → ℝ) (hf : ContinuousOn f O)
    (hgraph : ∀ x ∈ closure S, t • x ∈ O) :
    RegionIntegrable (fun y : ((fun x : E n => t • x) '' S) => f y) ∧
    RegionIntegrable (fun x : S => f (t • (x : E n))) ∧
    regionIntegral (fun y : ((fun x : E n => t • x) '' S) => f y) =
      t ^ n * regionIntegral (fun x : S => f (t • (x : E n))) := by
  let A := LinearEquiv.smulOfNeZero ℝ (E n) t ht.ne'
  have hA (x : E n) : A x = t • x := rfl
  have hfc : Continuous (fun x : closure S => f (A x)) :=
    hf.comp_continuous (continuous_const.smul continuous_subtype_val)
      (fun x => hgraph x x.property)
  have hgi := scalar_continuous_closure_integrable hS _ hfc
  have hK := (jordan_bounded hS).isCompact_closure
  let : CompactSpace (closure S) := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := (isCompact_range hfc).isBounded.exists_norm_le
  have hb : RegionBounded (fun y : A '' S => f y) := by
    refine ⟨M, ?_⟩
    rintro ⟨y, x, hx, rfl⟩
    exact hM _ ⟨⟨x, subset_closure hx⟩, rfl⟩
  have hsub := LinearVolume.linear_substitution A S hS (fun y => f y) hb
  have hfi := hsub.2.1.mpr hgi
  have hdet : |(A : E n →ₗ[ℝ] E n).det| = t ^ n := by
    change |(t • (LinearMap.id : E n →ₗ[ℝ] E n)).det| = _
    simp only [LinearMap.det_smul, finrank_euclideanSpace_fin, LinearMap.det_id,
      mul_one, abs_of_nonneg (pow_nonneg ht.le n)]
  refine ⟨hfi, hgi, ?_⟩
  rw [hdet] at hsub
  exact hsub.2.2 (Or.inl hfi)


private def matrixMap : (E n →L[ℝ] E n) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => matrixOfLinearMap A.toLinearMap
      map_add' := fun A B => (matrixLinearEquiv n n).symm.map_add A.toLinearMap B.toLinearMap
      map_smul' := fun c A => (matrixLinearEquiv n n).symm.map_smul c A.toLinearMap }

private lemma matrixMap_apply (A : E n →L[ℝ] E n) :
    matrixMap A = matrixOfLinearMap A.toLinearMap := rfl

private lemma matrixMap_roundtrip (A : E n →L[ℝ] E n) :
    LinearMap.toContinuousLinearMap (matrixLinearEquiv n n (matrixMap A)) = A := by
  rw [matrixMap_apply, matrix_linear_roundtrip]
  rfl

lemma spatialMatrix_c1_of_c2 (hP : IsOpen P) (hW : IsOpen W)
    (hΦ : ContDiffOn ℝ 2 (fun z : E m × E n => e z.1 z.2) (P ×ˢ W)) :
    ContDiffOn ℝ 1 (fun z : E m × E n => spatialMatrix e z.1 z.2) (P ×ˢ W) := by
  have hc := (hΦ.fderiv_of_isOpen (hP.prod hW) (m := 1) (by norm_num)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ (E m) (E n)))
  apply (matrixMap.contDiff.comp_contDiffOn hc).congr
  intro z hz
  have hd := (hΦ.contDiffAt ((hP.prod hW).mem_nhds hz)).differentiableAt (by norm_num)
  change matrixOfLinearMap (fderiv ℝ (e z.1) z.2).toLinearMap = _
  rw [partial_right hd]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem c2_sufficient : Specs.D04.C08.MovingDomains.c2_sufficientType := by
  intro m n P W e hP hW hsrc hΦ hinv
  let Φ : E m × E n → E n := fun z => e z.1 z.2
  have hU : IsOpen (P ×ˢ W) := hP.prod hW
  have hAc := spatialMatrix_c1_of_c2 hP hW hΦ
  have hA (p : E m) (hp : p ∈ P) (x : E n) (hx : x ∈ W) :
      DifferentiableAt ℝ (fun q => spatialMatrix e q x) p := by
    have hc : DifferentiableAt ℝ (fun z : E m × E n => spatialMatrix e z.1 z.2) (p, x) :=
      (hAc.contDiffAt (hU.mem_nhds ⟨hp, hx⟩)).differentiableAt (by norm_num)
    have hi : HasFDerivAt (fun q : E m => (q, x)) (ContinuousLinearMap.inl ℝ (E m) (E n)) p :=
      (hasFDerivAt_id p).prodMk (hasFDerivAt_const x p)
    have hh : HasFDerivAt (fun q => spatialMatrix e q x)
        ((fderiv ℝ (fun z : E m × E n => spatialMatrix e z.1 z.2) (p, x)).comp
          (ContinuousLinearMap.inl ℝ (E m) (E n))) p := hc.hasFDerivAt.comp (f := fun q : E m => (q, x)) p hi
    exact hh.differentiableAt
  have hB : ContinuousOn (fun z : E m × E n => parameterJacobian e z.1 z.2) (P ×ˢ W) :=
    continuous_partial_left hU hAc
  refine ⟨⟨hsrc, hΦ.of_le (by norm_num), hinv, hA, hB⟩, ?_⟩
  intro p hp x hx h
  have hz : (p, x) ∈ P ×ˢ W := ⟨hp, hx⟩
  have hΦat : ContDiffAt ℝ 2 Φ (p, x) := hΦ.contDiffAt (hU.mem_nhds hz)
  have hT : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (p, x)) (p, x) :=
    ((hΦat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hiL : HasFDerivAt (fun q : E m => (q, x)) (ContinuousLinearMap.inl ℝ (E m) (E n)) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const x p)
  have hiR : HasFDerivAt (fun z : E n => (p, z)) (ContinuousLinearMap.inr ℝ (E m) (E n)) x :=
    (hasFDerivAt_const p x).prodMk (hasFDerivAt_id x)
  have hTX := (hT.comp p hiL).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.inr ℝ (E m) (E n)) p)
  have hMA := matrixMap.hasFDerivAt.comp p hTX
  have heA : (fun q => spatialMatrix e q x) =ᶠ[𝓝 p]
      (fun q => matrixMap ((fderiv ℝ Φ (q, x)).comp (ContinuousLinearMap.inr ℝ (E m) (E n)))) := by
    filter_upwards [hP.mem_nhds hp] with q hq
    have hd : DifferentiableAt ℝ Φ (q, x) :=
      (hΦ.contDiffAt (hU.mem_nhds ⟨hq, hx⟩)).differentiableAt (by norm_num)
    change matrixMap (fderiv ℝ (e q) x) = _
    rw [partial_right hd]
  have hMA' := hMA.congr_of_eventuallyEq heA
  have hTV := (hT.comp x hiR).clm_apply (hasFDerivAt_const (h, (0 : E n)) x)
  have heV : (fun z => fderiv ℝ (fun q => e q z) p h) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ Φ (p, z) (h, (0 : E n))) := by
    filter_upwards [hW.mem_nhds hx] with z hz
    have hd : DifferentiableAt ℝ Φ (p, z) :=
      (hΦ.contDiffAt (hU.mem_nhds ⟨hp, hz⟩)).differentiableAt (by norm_num)
    rw [partial_left hd]
    rfl
  have hTV' := hTV.congr_of_eventuallyEq heV
  have hBval : parameterJacobian e p x h = _ := congrArg (fun L => L h) hMA'.fderiv
  change HasFDerivAt (fun z => fderiv ℝ (fun q => e q z) p h)
    (LinearMap.toContinuousLinearMap (matrixLinearEquiv n n (parameterJacobian e p x h))) x
  rw [hBval, ContinuousLinearMap.comp_apply, matrixMap_roundtrip]
  convert hTV' using 1
  apply ContinuousLinearMap.ext
  intro k
  simp only [ContinuousLinearMap.comp_apply, add_apply, zero_apply,
    map_zero, zero_add, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  exact (hΦat.isSymmSndFDerivAt (by norm_num)).eq (h, 0) (0, k)

lemma dilation_volume_eq (S : Set (E n)) (hS : Jordan S) (t : ℝ) (ht : 0 ≤ t) :
    Jordan ((fun x : E n => t • x) '' S) ∧
    volume ((fun x : E n => t • x) '' S) = t ^ n * volume S := by
  have hh := LinearVolume.linear_volume (t • (LinearMap.id : E n →ₗ[ℝ] E n)) S hS
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.det_smul,
    finrank_euclideanSpace_fin, LinearMap.det_id, mul_one, abs_of_nonneg (pow_nonneg ht n)] using hh

theorem dilation_volume : Specs.D04.C08.MovingDomains.dilation_volumeType := by
  intro n S hS t ht
  have hh := dilation_volume_eq S hS t ht.le
  refine ⟨hh.1, hh.2, ?_⟩
  have hd := ((hasDerivAt_id t).pow n).mul_const (volume S)
  simp only [id_eq, mul_one] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact (dilation_volume_eq S hS u hu.le).2

lemma dilation_velocity_derivative (t : ℝ) (y : E n) :
    fderiv ℝ (fun z : E n => t⁻¹ • z) y = t⁻¹ • ContinuousLinearMap.id ℝ (E n) :=
  ((hasFDerivAt_id y).const_smul t⁻¹).fderiv

lemma dilation_divergence (t : ℝ) (y : E n) :
    divergence (fun z : E n => t⁻¹ • z) y = (n : ℝ) / t := by
  rw [divergence_eq_trace]
  change LinearMap.trace ℝ (E n) (fderiv ℝ (fun z : E n => t⁻¹ • z) y).toLinearMap = _
  rw [dilation_velocity_derivative]
  simp [LinearMap.trace_id, div_eq_mul_inv, mul_comm]


theorem dilation : Specs.D04.C08.MovingDomains.dilationType := by
  intro n S T O f hS hT hTpos hO hf hgraph t ht
  have htpos : 0 < t := hTpos ht
  let g : closure S → ℝ → ℝ := fun x u => u ^ n * f (u • (x : E n))
  let d : closure S → ℝ → ℝ := fun x u =>
    (n : ℝ) * u ^ (n - 1) * f (u • (x : E n)) +
      u ^ n * fderiv ℝ f (u • (x : E n)) x
  have hmap : Continuous (fun z : closure S × T => (z.2 : ℝ) • (z.1 : E n)) :=
    continuous_snd.subtype_val.smul continuous_fst.subtype_val
  have hmapO (z : closure S × T) : (z.2 : ℝ) • (z.1 : E n) ∈ O :=
    hgraph z.2 z.2.property z.1 z.1.property
  have hfc := hf.continuousOn.comp_continuous hmap hmapO
  have hdfc := (hf.continuousOn_fderiv_of_isOpen hO le_rfl).comp_continuous hmap hmapO
  have hgc : Continuous (fun z : closure S × T => g z.1 z.2) :=
    (continuous_snd.subtype_val.pow n).mul hfc
  have hdc : Continuous (fun z : closure S × T => d z.1 z.2) :=
    ((continuous_const.mul (continuous_snd.subtype_val.pow (n - 1))).mul hfc).add
      ((continuous_snd.subtype_val.pow n).mul (hdfc.clm_apply continuous_fst.subtype_val))
  have hd (x : S) (u : ℝ) (hu : u ∈ T) :
      HasDerivAt (g ⟨x, subset_closure x.property⟩) (d ⟨x, subset_closure x.property⟩ u) u := by
    have hline : HasDerivAt (fun v : ℝ => v • (x : E n)) x u := by
      have hh := (hasDerivAt_id u).smul_const (x : E n)
      simp only [id_eq, one_smul] at hh
      exact hh
    have hdf := (hf.contDiffAt (hO.mem_nhds
      (hgraph u hu x (subset_closure x.property)))).differentiableAt (by norm_num)
    have hh := ((hasDerivAt_id u).pow n).mul (hdf.hasFDerivAt.comp_hasDerivAt u hline)
    simp only [id_eq, mul_one, Function.comp_apply, Pi.pow_apply] at hh
    exact hh
  have hder := scalar_real_parameter_derivative hS hT g d hgc hdc hd t ht
  have hvalue (u : ℝ) (hu : u ∈ T) :
      regionIntegral (fun y : ((fun x : E n => u • x) '' S) => f y) =
        regionIntegral (fun x : S => g ⟨x, subset_closure x.property⟩ u) := by
    have hs := dilation_substitution S hS u (hTpos hu) O f hf.continuousOn (hgraph u hu)
    have hl := SlicingAndMoments.region_smul (jordan_bounded hS)
      (fun x : S => f (u • (x : E n))) hs.2.1 (u ^ n)
    exact hs.2.2.trans hl.2.symm
  have hev : (fun u : ℝ => regionIntegral (fun y : ((fun x : E n => u • x) '' S) => f y)) =ᶠ[𝓝 t]
      (fun u => regionIntegral (fun x : S => g ⟨x, subset_closure x.property⟩ u)) :=
    Filter.eventuallyEq_of_mem (hT.mem_nhds ht) hvalue
  have hderF := hder.congr_of_eventuallyEq hev
  let k : E n → ℝ := fun y => fderiv ℝ f y y + (n : ℝ) * f y
  have hkc : ContinuousOn k O :=
    ((hf.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_id).add
      (continuousOn_const.mul hf.continuousOn)
  have hk := dilation_substitution S hS t htpos O k hkc (hgraph t ht)
  have hcoef : (n : ℝ) * t ^ (n - 1) = (t⁻¹ * t ^ n) * (n : ℝ) := by
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
  have heq (x : S) : d ⟨x, subset_closure x.property⟩ t =
      (t⁻¹ * t ^ n) * k (t • (x : E n)) := by
    dsimp only [d, k]
    rw [hcoef, map_smul]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hefun : (fun x : S => d ⟨x, subset_closure x.property⟩ t) =
      (fun x : S => (t⁻¹ * t ^ n) * k (t • (x : E n))) := funext heq
  have hlin := SlicingAndMoments.region_smul (jordan_bounded hS)
    (fun x : S => k (t • (x : E n))) hk.2.1 (t⁻¹ * t ^ n)
  have hint : regionIntegral (fun x : S => d ⟨x, subset_closure x.property⟩ t) =
      t⁻¹ * regionIntegral (fun y : ((fun x : E n => t • x) '' S) => k y) := by
    rw [hefun, hlin.2, hk.2.2]
    ring
  rw [hint] at hderF
  exact ⟨(dilation_volume_eq S hS t htpos.le).1,
    fun y => ⟨dilation_velocity_derivative t y, dilation_divergence t y⟩, hk.1, hderF⟩

end D04.MovingDomains
