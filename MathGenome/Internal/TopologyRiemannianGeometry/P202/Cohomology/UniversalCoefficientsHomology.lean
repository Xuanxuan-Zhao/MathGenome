import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficientsHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains
import MathGenome.Internal.AlgebraCore.P103.Ch11.UniversalCoefficientsSplitting
import MathGenome.Internal.AlgebraCore.P103.Ch12.TorBaseChange
import MathGenome.Internal.AlgebraCore.P103.Ch11.FlatResolutions
import MathGenome.Internal.AlgebraCore.P103.Ch11.VanishingAndFlatness

noncomputable section
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open scoped TensorProduct
namespace P202.UniversalCoefficientsHomology
universe u v w t s
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.UniversalCoefficientsHomology
variable (R : Type u) [CommRing R]
variable (A : Type v) [AddCommGroup A] [Module R A]

/-- Coordinates specified by the actual quotient projection. -/
def relativeCoordinates (P : Pair.{w}) (n : ℕ) :
    (nonnegative R A P).X n ≃ₗ[R] (Outside P n →₀ A) :=
  (P202.RelativeSingularChains.quotient_coordinates R A P n).choose

@[simp] theorem relativeCoordinates_projection (P : Pair.{w}) (n : ℕ)
    (c : Chains A P.space n) :
    relativeCoordinates R A P n ((projection (chainFunctor R A) P).f n c) =
      outsideProjection R A P n c :=
  (P202.RelativeSingularChains.quotient_coordinates R A P n).choose_spec c

/-- The quotient projection is surjective in each degree. -/
theorem projection_surjective (P : Pair.{w}) (n : ℕ) :
    Function.Surjective ((projection (chainFunctor R A) P).f n) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Tensor comparison constructed from the remaining simplex coordinates. -/
def relativeTensorEquiv (P : Pair.{w}) (n : ℕ) :
    ((nonnegative R R P).X n ⊗[R] A) ≃ₗ[R] (nonnegative R A P).X n := by
  classical
  exact (TensorProduct.congr (relativeCoordinates R R P n) (LinearEquiv.refl R A)).trans
    ((TensorProduct.finsuppScalarLeft R A (Outside P n)).trans
      (relativeCoordinates R A P n).symm)

theorem relativeTensorEquiv_projection (P : Pair.{w}) (n : ℕ)
    (c : Chains R P.space n ⊗[R] A) :
    relativeTensorEquiv R A P n
        (((projection (chainFunctor R R) P).f n).hom.rTensor A c) =
      (projection (chainFunctor R A) P).f n (tensorEquiv R A P.space n c) := by
  classical
  apply (relativeCoordinates R A P n).injective
  induction c using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul c a =>
    simp only [LinearMap.rTensor_tmul, relativeTensorEquiv, LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply,
      relativeCoordinates_projection]
    ext s
    simp only [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
    change (outsideProjection R R P n c) s • a = (tensorEquiv R A P.space n (c ⊗ₜ a)) s.val
    exact (TensorProduct.finsuppScalarLeft_apply_tmul_apply c a s.val).symm

/-- The projection remains surjective after tensoring; no flatness is needed. -/
theorem tensor_projection_surjective (P : Pair.{w}) (n : ℕ) :
    Function.Surjective (((projection (chainFunctor R R) P).f n).hom.rTensor A) := by
  exact LinearMap.rTensor_surjective A (projection_surjective R R P n)

theorem relativeTensorEquiv_boundary (P : Pair.{w}) (n : ℕ)
    (c : (nonnegative R R P).X (n+1) ⊗[R] A) :
    relativeTensorEquiv R A P n (((nonnegative R R P).d (n+1) n).hom.rTensor A c) =
      (nonnegative R A P).d (n+1) n (relativeTensorEquiv R A P (n+1) c) := by
  obtain ⟨c, rfl⟩ := tensor_projection_surjective R A P (n+1) c
  have hR := (projection (chainFunctor R R) P).comm (n+1) n
  have hA := (projection (chainFunctor R A) P).comm (n+1) n
  have ht : ((nonnegative R R P).d (n+1) n).hom.rTensor A
      ((((projection (chainFunctor R R) P).f (n+1)).hom.rTensor A) c) =
      (((projection (chainFunctor R R) P).f n).hom.rTensor A)
        ((boundary R R P.space n).rTensor A c) := by
    induction c using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x a => exact congrArg (fun c => c ⊗ₜ[R] a) (congrArg (fun f => f x) hR)
  rw [ht, relativeTensorEquiv_projection, relativeTensorEquiv_projection,
    P202.SingularChains.tensorEquiv_boundary]
  exact congrArg (fun f => f (tensorEquiv R A P.space (n+1) c)) hA.symm

theorem relativeTensorEquiv_natural (P Q : Pair.{w}) (f : P ⟶ Q) (n : ℕ)
    (c : (nonnegative R R P).X n ⊗[R] A) :
    relativeTensorEquiv R A Q n (((relativeMap (chainFunctor R R) f).f n).hom.rTensor A c) =
      (relativeMap (chainFunctor R A) f).f n (relativeTensorEquiv R A P n c) := by
  obtain ⟨c, rfl⟩ := tensor_projection_surjective R A P n c
  have hR := congrArg (fun φ => φ.f n) (projection_map (chainFunctor R R) f)
  have hA := congrArg (fun φ => φ.f n) (projection_map (chainFunctor R A) f)
  have ht : ((relativeMap (chainFunctor R R) f).f n).hom.rTensor A
      ((((projection (chainFunctor R R) P).f n).hom.rTensor A) c) =
      (((projection (chainFunctor R R) Q).f n).hom.rTensor A)
        ((((chainMap R R f.map).f n).hom.rTensor A) c) := by
    induction c using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x a => exact congrArg (fun c => c ⊗ₜ[R] a) (congrArg (fun φ => φ x) hR)
  rw [ht, relativeTensorEquiv_projection, relativeTensorEquiv_projection,
    P202.SingularChains.tensorEquiv_natural]
  exact congrArg (fun φ => φ (tensorEquiv R A P.space n c)) hA.symm

theorem relative_tensor : Expected.relativeTensor.{u,v,w} R A :=
  ⟨⟨relativeTensorEquiv R A, relativeTensorEquiv_projection R A,
    relativeTensorEquiv_boundary R A, relativeTensorEquiv_natural R A⟩⟩

theorem absoluteTensor_coefficient {B : Type v} [AddCommGroup B] [Module R B]
    (g : A →ₗ[R] B) (X : TopCat.{w}) (n : ℕ) (c : Chains R X n ⊗[R] A) :
    tensorEquiv R B X n (TensorProduct.map LinearMap.id g c) =
      (coefficientMap R A g X).f n (tensorEquiv R A X n c) := by
  classical
  induction c using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul c a =>
    ext s
    change (TensorProduct.finsuppScalarLeft R B _ (c ⊗ₜ[R] (g a))) s =
      g ((TensorProduct.finsuppScalarLeft R A _ (c ⊗ₜ[R] a)) s)
    simp only [TensorProduct.finsuppScalarLeft_apply_tmul_apply, map_smul]

/-- Naturality in coefficients for the same relative comparison. -/
theorem relativeTensorEquiv_coefficient {B : Type v} [AddCommGroup B] [Module R B]
    (g : A →ₗ[R] B) (P : Pair.{w}) (n : ℕ) (c : (nonnegative R R P).X n ⊗[R] A) :
    relativeTensorEquiv R B P n (TensorProduct.map LinearMap.id g c) =
      (relativeCoefficientMap R A g P).f n (relativeTensorEquiv R A P n c) := by
  obtain ⟨c, rfl⟩ := tensor_projection_surjective R A P n c
  have ht : TensorProduct.map LinearMap.id g
      ((((projection (chainFunctor R R) P).f n).hom.rTensor A) c) =
      (((projection (chainFunctor R R) P).f n).hom.rTensor B)
        (TensorProduct.map LinearMap.id g c) := by
    induction c using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x a => rfl
  rw [ht, relativeTensorEquiv_projection, relativeTensorEquiv_projection]
  have hc := absoluteTensor_coefficient R A g P.space n c
  have hc' := congrArg (fun c => (projection (chainFunctor R B) P).f n c) hc
  apply hc'.trans
  have h := congrArg (fun φ => φ.f n) (cokernel.π_desc
    (inclusion (chainFunctor R A) P)
    (coefficientMap R A g P.space ≫ projection (chainFunctor R B) P)
    (by rw [← Category.assoc, coefficientMap_inclusion, Category.assoc,
          cokernel.condition, HasZeroMorphisms.comp_zero]))
  exact congrArg (fun φ => φ (tensorEquiv R A P.space n c)) h.symm

theorem relative_tensor_family : Nonempty (RelativeTensorFamily.{u,v,w} R) := by
  refine ⟨{ data := fun A _ _ =>
    ⟨relativeTensorEquiv R A, relativeTensorEquiv_projection R A,
      relativeTensorEquiv_boundary R A, relativeTensorEquiv_natural R A⟩
            natural_coefficient := ?_ }⟩
  intro A B _ _ _ _ g P n c
  exact relativeTensorEquiv_coefficient R A g P n c

/-- Actual isomorphism of nonnegative relative complexes over R. -/
def relativeTensorIso (P : Pair.{w}) :
    tensorComplex R A (nonnegative R R P) ≅
      ((ModuleCat.uliftFunctor.{u} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (nonnegative R A P) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => ((relativeTensorEquiv R A P n).trans
    (ULift.moduleEquiv.symm : _ ≃ₗ[R] ULift.{u} _)).toModuleIso)
    (by
      intro i j hij
      obtain rfl : j+1 = i := hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply ULift.ext
      exact (relativeTensorEquiv_boundary R A P j c).symm)

/-- Actual isomorphism of nonnegative absolute complexes over R. -/
def absoluteTensorIso (X : TopCat.{w}) :
    tensorComplex R A (complex R R X) ≅
      ((ModuleCat.uliftFunctor.{u} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (complex R A X) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => ((tensorEquiv R A X n).trans
    (ULift.moduleEquiv.symm : _ ≃ₗ[R] ULift.{u} _)).toModuleIso)
    (by
      intro i j hij
      obtain rfl : j+1 = i := hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply ULift.ext
      exact (P202.SingularChains.tensorEquiv_boundary R A X j c).symm)

theorem absolute_tensor : Expected.absoluteTensor.{u,v,w} R A := by
  intro X
  exact ⟨absoluteTensorIso R A X, fun _ _ => rfl⟩

theorem absoluteDegree_boundary (X : TopCat.{w}) (n : ℕ)
    (x : (ordinaryComplex R A X).X (n+1 : ℕ)) :
    (ordinaryNonnegativeIso R A X n).hom ((ordinaryComplex R A X).d (n+1 : ℕ) n x) =
      (complex R A X).d (n+1) n ((ordinaryNonnegativeIso R A X (n+1)).hom x) := by
  have h := P202.SingularChains.ordinary_boundary R A X n
  have hh := congrArg (fun f => f ((ordinaryNonnegativeIso R A X (n+1)).hom x)) h
  simpa using hh

theorem relativeDegree_boundary (P : Pair.{w}) (n : ℕ)
    (x : (ordinary R A P).X (n+1 : ℕ)) :
    (ordinaryDegreeIso R A P n).hom ((ordinary R A P).d (n+1 : ℕ) n x) =
      (nonnegative R A P).d (n+1) n ((ordinaryDegreeIso R A P (n+1)).hom x) := by
  have h := P202.RelativeSingularChains.ordinary_boundary R A P n
  have hh := congrArg (fun f => f ((ordinaryDegreeIso R A P (n+1)).hom x)) h
  simpa using hh

theorem relativeDegree_zero (P : Pair.{w}) : (ordinary R A P).d 0 (-1) = 0 := by
  apply (cancel_epi ((projection (ordinaryFunctor R A) P).f 0)).mp
  rw [(projection (ordinaryFunctor R A) P).comm]
  change (ordinaryComplex R A P.space).d 0 (-1) ≫ _ = _ ≫ 0
  rw [P202.SingularChains.ordinary_boundary_zero, zero_comp, comp_zero]

theorem ordinary_homology : Expected.ordinaryHomology.{u,v,w} R A := by
  intro X
  exact ⟨nonnegativeHomologyData R (complex R A X) (ordinaryComplex R A X)
    (fun n => (ordinaryNonnegativeIso R A X n).toLinearEquiv)
    (absoluteDegree_boundary R A X) (P202.SingularChains.ordinary_boundary_zero R A X (-1))⟩

theorem relative_homology : Expected.relativeHomology.{u,v,w} R A := by
  intro P
  exact ⟨nonnegativeHomologyData R (nonnegative R A P) (ordinary R A P)
    (fun n => (ordinaryDegreeIso R A P n).toLinearEquiv)
    (relativeDegree_boundary R A P) (relativeDegree_zero R A P)⟩

section BalancedHomology
variable (C : ChainComplex (ModuleCat.{t} R) ℕ) (D : ChainComplex (ModuleCat.{s} R) ℕ)
  (e : ∀ n, (C.X n ⊗[R] A) ≃ₗ[R] D.X n)
  (he : ∀ i j x, e j ((C.d i j).hom.rTensor A x) = D.d i j (e i x))

abbrev balancedTermComparison (n : ℕ) :=
  (balancedTensorEquiv R A (C.X n)).trans (e n).toAddEquiv

include he in
lemma balancedTermComparison_boundary (i j : ℕ)
    (x : (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A).X i) :
    balancedTermComparison R A C D e j
        ((P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A).d i j x) =
      D.d i j (balancedTermComparison R A C D e i x) := by
  change e j (balancedTensorEquiv R A (C.X j)
    (P103.Specs.Ch11.ExtTorDefinitions.tensorMap
      ((oppositeFunctor R).map (C.d i j)).hom LinearMap.id x)) = _
  rw [balancedTensorEquiv_natural]
  exact he i j _

def balancedCyclesComparison (n : ℕ) :=
  P103.Ch12.TorBaseChange.additiveCyclesEquiv
    (K := P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A) (L := D)
    (balancedTermComparison R A C D e) (balancedTermComparison_boundary R A C D e he) n

def balancedQuotientHomologyComparison (n : ℕ) :=
  P103.Ch12.TorBaseChange.additiveHomologyEquiv
    (K := P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A) (L := D)
    (balancedTermComparison R A C D e) (balancedTermComparison_boundary R A C D e he) n

def balancedHomologyComparison (n : ℕ) :=
  (balancedQuotientHomologyComparison R A C D e he n).trans
    (quotientHomologyEquiv R D n).symm.toAddEquiv

lemma balancedHomologyComparison_formula (n : ℕ)
    (z : Algebraic.cycles
      (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A) n) :
    quotientHomologyEquiv R D n
      (balancedHomologyComparison R A C D e he n (Algebraic.homologyClass _ n z)) =
      Algebraic.homologyClass D n (balancedCyclesComparison R A C D e he n z) := by
  change quotientHomologyEquiv R D n
    ((quotientHomologyEquiv R D n).symm
      (balancedQuotientHomologyComparison R A C D e he n (Algebraic.homologyClass _ n z))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma balancedHomologyComparison_scalar (n : ℕ) (r : R) (x : Algebraic.Homology
    (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A) n) :
    balancedHomologyComparison R A C D e he n (Algebraic.homologyMap
      (P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R C)
        (r • (LinearMap.id : A →ₗ[R] A))) n x) =
      r • balancedHomologyComparison R A C D e he n x := by
  obtain ⟨z, rfl⟩ := (Algebraic.cycleBoundaries _ n).mkQ_surjective x
  apply (quotientHomologyEquiv R D n).injective
  rw [map_smul]
  change quotientHomologyEquiv R D n (balancedHomologyComparison R A C D e he n
    (Algebraic.homologyClass _ n (Algebraic.cyclesMap _ n z))) =
      r • quotientHomologyEquiv R D n (balancedHomologyComparison R A C D e he n
        (Algebraic.homologyClass _ n z))
  rw [balancedHomologyComparison_formula, balancedHomologyComparison_formula, ← map_smul]
  apply congrArg (Algebraic.homologyClass D n)
  apply Subtype.ext
  change e n (balancedTensorEquiv R A (C.X n)
    (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id (r • LinearMap.id) z.val)) =
      r • e n (balancedTensorEquiv R A (C.X n) z.val)
  rw [balancedTensorEquiv_scalar, map_smul]

end BalancedHomology

theorem balanced_homology_comparison : Expected.balancedHomologyComparison.{u,v,t,s} R A := by
  intro C D e he
  refine ⟨{ equiv := balancedHomologyComparison R A C D e he
            formula := ?_
            scalar := balancedHomologyComparison_scalar R A C D e he }⟩
  intro n z
  exact ⟨balancedCyclesComparison R A C D e he n z, rfl,
    balancedHomologyComparison_formula R A C D e he n z⟩

/-- Apply the balanced-model homology bridge to actual absolute chains. -/
theorem absolute_tensor_homology : Expected.absoluteTensorHomology.{u,v,w} R A := by
  intro X
  apply balanced_homology_comparison R A (complex R R X) (complex R A X) (tensorEquiv R A X)
  intro i j x
  by_cases h : j+1 = i
  · subst i
    exact P202.SingularChains.tensorEquiv_boundary R A X j x
  · rw [(complex R R X).shape i j h, (complex R A X).shape i j h]
    simp

/-- The relative bridge is simultaneous in pairs and coefficients, and lands
in the actual relative homology with its original R-module action. -/
theorem relative_tensor_homology : Expected.relativeTensorHomology.{u,v,w} R := by
  obtain ⟨F⟩ := relative_tensor_family.{u,v,w} R
  refine ⟨F, ?_⟩
  intro A _ _ P
  apply balanced_homology_comparison R A (nonnegative R R P) (nonnegative R A P)
    ((F.data A).equiv P)
  intro i j x
  by_cases h : j+1 = i
  · subst i
    exact (F.data A).boundary P j x
  · rw [(nonnegative R R P).shape i j h, (nonnegative R A P).shape i j h]
    simp

/-- The fixed natural-degree modules are free with their original scalar action. -/
theorem ordinary_free (X : TopCat.{w}) (n : ℕ) :
    Module.Free R ((complex R R X).X n) := by
  change Module.Free R (Simplex X n →₀ R)
  infer_instance

theorem relative_free (P : Pair.{w}) (n : ℕ) :
    Module.Free R ((nonnegative R R P).X n) := by
  obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis R P n
  exact Module.Free.of_basis b

/-- Changing to the canonical opposite action preserves arbitrary-rank freeness. -/
theorem opposite_free {C : ChainComplex (ModuleCat.{t} R) ℕ}
    (h : ∀ n, Module.Free R (C.X n)) (n : ℕ) :
    Module.Free Rᵐᵒᵖ ((oppositeComplex R C).X n) := by
  letI := h n
  letI : RingHomInvPair (RingEquiv.toOpposite R).toRingHom
      (RingEquiv.toOpposite R).symm.toRingHom := RingHomInvPair.of_ringEquiv (RingEquiv.toOpposite R)
  letI : RingHomInvPair (RingEquiv.toOpposite R).symm.toRingHom
      (RingEquiv.toOpposite R).toRingHom := RingHomInvPair.of_ringEquiv_symm (RingEquiv.toOpposite R)
  exact Module.Free.of_equiv (oppositeTermEquiv R (C.X n))

/-- The PID theorem applies to the actual opposite-action complexes and their
boundary modules. In particular its proof uses no finite generation condition. -/
theorem pid_hypotheses [IsDomain R] [IsPrincipalIdealRing R] :
    Expected.pidHypotheses.{u,v,w} R := by
  constructor
  · intro X
    obtain ⟨h, S, _⟩ := P103.Ch11.UniversalCoefficientsSplitting.pid_homology
      (oppositeComplex R (complex R R X)) (opposite_free R (ordinary_free R X))
    exact ⟨h, ⟨S⟩⟩
  · intro P
    obtain ⟨h, S, _⟩ := P103.Ch11.UniversalCoefficientsSplitting.pid_homology
      (oppositeComplex R (nonnegative R R P)) (opposite_free R (relative_free R P))
    exact ⟨h, ⟨S⟩⟩

/-- Apply the algebraic theorem in a single natural family, using the actual
singular complexes. These model-level sequences are transported to the fixed topological
homology objects by `topological_uct` below. -/
theorem algebraic_model [IsDomain R] [IsPrincipalIdealRing R] :
    Expected.algebraicModel.{u,v,w} R := by
  obtain ⟨U⟩ := P103.Ch11.UniversalCoefficientsHomology.universal_coefficients R
  refine ⟨U, ?_, ?_⟩
  · intro X
    obtain ⟨h, ⟨S⟩⟩ := (pid_hypotheses.{u,v,w} R).1 X
    exact ⟨h, fun M =>
      P103.Ch11.UniversalCoefficientsSplitting.homology_scalar_splitting U _ h S M⟩
  · intro P
    obtain ⟨h, ⟨S⟩⟩ := (pid_hypotheses.{u,v,w} R).2 P
    exact ⟨h, fun M =>
      P103.Ch11.UniversalCoefficientsSplitting.homology_scalar_splitting U _ h S M⟩

section QuotientNaturality
variable {ι : Type*} {c : ComplexShape ι}
  (C D : HomologicalComplex (ModuleCat.{t} R) c)

lemma quotientHomologyEquiv_class (n : ι) (z : Algebraic.cycles C n) :
    quotientHomologyEquiv R C n
      ((C.sc n).homologyπ ((C.sc n).moduleCatCyclesIso.inv z)) =
        Algebraic.homologyClass C n z := by
  unfold quotientHomologyEquiv
  simp only [LinearEquiv.trans_apply]
  erw [ShortComplex.π_moduleCatCyclesIso_hom_apply]
  simp only [Iso.inv_hom_id_apply]
  rfl

lemma quotientHomologyEquiv_natural (f : C ⟶ D) (n : ι) (x : C.homology n) :
    quotientHomologyEquiv R D n (HomologicalComplex.homologyMap f n x) =
      Algebraic.homologyMap f n (quotientHomologyEquiv R C n x) := by
  obtain ⟨z, hz⟩ := (Algebraic.cycleBoundaries C n).mkQ_surjective
    (quotientHomologyEquiv R C n x)
  have hx : x = (C.sc n).homologyπ ((C.sc n).moduleCatCyclesIso.inv z) := by
    apply (quotientHomologyEquiv R C n).injective
    rw [quotientHomologyEquiv_class]
    exact hz.symm
  rw [hx, quotientHomologyEquiv_class]
  have hcy : HomologicalComplex.cyclesMap f n ((C.sc n).moduleCatCyclesIso.inv z) =
      (D.sc n).moduleCatCyclesIso.inv (Algebraic.cyclesMap f n z) := by
    apply (ModuleCat.mono_iff_injective (D.sc n).iCycles).mp inferInstance
    change ((HomologicalComplex.cyclesMap f n ≫ D.iCycles n)
      ((C.sc n).moduleCatCyclesIso.inv z)) = _
    rw [HomologicalComplex.cyclesMap_i]
    change (f.f n) ((C.sc n).iCycles ((C.sc n).moduleCatCyclesIso.inv z)) = _
    simp only [ShortComplex.moduleCatCyclesIso_inv_iCycles_apply]
    rfl
  have hh := congrArg (fun k => k ((C.sc n).moduleCatCyclesIso.inv z))
    (ShortComplex.homologyπ_naturality ((shortComplexFunctor _ _ n).map f))
  change HomologicalComplex.homologyMap f n
    ((C.sc n).homologyπ ((C.sc n).moduleCatCyclesIso.inv z)) =
    (D.sc n).homologyπ (HomologicalComplex.cyclesMap f n
      ((C.sc n).moduleCatCyclesIso.inv z)) at hh
  rw [hh, hcy, quotientHomologyEquiv_class]
  rfl

end QuotientNaturality

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v w t s
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.UniversalCoefficientsHomology
variable (R : Type u) [CommRing R]

section NonnegativeNaturality
variable (N N' : ChainComplex (ModuleCat.{t} R) ℕ)
  (Z Z' : ChainComplex (ModuleCat.{t} R) ℤ)
  (e : ∀ n : ℕ, Z.X (n : ℤ) ≃ₗ[R] N.X n)
  (e' : ∀ n : ℕ, Z'.X (n : ℤ) ≃ₗ[R] N'.X n)
  (hd : ∀ (n : ℕ) (x : Z.X (n+1 : ℕ)),
    e n (Z.d (n+1 : ℕ) n x) = N.d (n+1) n (e (n+1) x))
  (hd' : ∀ (n : ℕ) (x : Z'.X (n+1 : ℕ)),
    e' n (Z'.d (n+1 : ℕ) n x) = N'.d (n+1) n (e' (n+1) x))
  (hzero : Z.d 0 (-1) = 0) (hzero' : Z'.d 0 (-1) = 0)
  (f : Z ⟶ Z') (g : N ⟶ N')
  (hfg : ∀ (n : ℕ) (x : Z.X (n : ℤ)), e' n (f.f n x) = g.f n (e n x))

include hfg in
lemma nonnegativeQuotientHomologyEquiv_natural (n : ℕ)
    (x : Algebraic.Homology Z (n : ℤ)) :
    nonnegativeQuotientHomologyEquiv R N' Z' e' hd' hzero' n
      (Algebraic.homologyMap f n x) =
      Algebraic.homologyMap g n
        (nonnegativeQuotientHomologyEquiv R N Z e hd hzero n x) := by
  obtain ⟨z, rfl⟩ := (Algebraic.cycleBoundaries Z (n : ℤ)).mkQ_surjective x
  change Algebraic.homologyClass N' n
      (nonnegativeCyclesEquiv R N' Z' e' hd' hzero' n (Algebraic.cyclesMap f n z)) =
    Algebraic.homologyClass N' n (Algebraic.cyclesMap g n
      (nonnegativeCyclesEquiv R N Z e hd hzero n z))
  apply congrArg (Algebraic.homologyClass N' n)
  apply Subtype.ext
  exact hfg n z.val

include hfg in
lemma nonnegativeHomologyEquiv_natural (n : ℕ) (x : Z.homology (n : ℤ)) :
    nonnegativeHomologyEquiv R N' Z' e' hd' hzero' n
      (HomologicalComplex.homologyMap f n x) =
      HomologicalComplex.homologyMap g n
        (nonnegativeHomologyEquiv R N Z e hd hzero n x) := by
  apply (quotientHomologyEquiv R N' n).injective
  simp only [nonnegativeHomologyEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [quotientHomologyEquiv_natural, nonnegativeQuotientHomologyEquiv_natural
    R N N' Z Z' e e' hd hd' hzero hzero' f g hfg]
  rw [quotientHomologyEquiv_natural]
  congr 1
  exact ((quotientHomologyEquiv R N n).apply_symm_apply _).symm

end NonnegativeNaturality

variable (A : Type v) [AddCommGroup A] [Module R A]

lemma absoluteDegree_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    ((ordinaryFunctor R A).map f).f (n : ℤ) ≫ (ordinaryNonnegativeIso R A Y n).hom =
      (ordinaryNonnegativeIso R A X n).hom ≫ (chainMap R A f).f n := by
  change (HomologicalComplex.extendMap (chainMap R A f) (degreeEmbedding 0)).f _ ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (i := n) (by change (0 : ℤ)+n = n; omega)]
  simp [ordinaryNonnegativeIso]

lemma relativeDegree_natural {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ) :
    (relativeMap (ordinaryFunctor R A) f).f (n : ℤ) ≫ (ordinaryDegreeIso R A Q n).hom =
      (ordinaryDegreeIso R A P n).hom ≫ (relativeMap (chainFunctor R A) f).f n := by
  apply (cancel_epi ((projection (ordinaryFunctor R A) P).f (n : ℤ))).mp
  have hz := congrArg (fun φ => φ.f (n : ℤ)) (projection_map (ordinaryFunctor R A) f)
  have hn := congrArg (fun φ => φ.f n) (projection_map (chainFunctor R A) f)
  change (projection (ordinaryFunctor R A) P).f (n : ℤ) ≫
      (relativeMap (ordinaryFunctor R A) f).f (n : ℤ) =
    ((ordinaryFunctor R A).map f.map).f (n : ℤ) ≫
      (projection (ordinaryFunctor R A) Q).f (n : ℤ) at hz
  change (projection (chainFunctor R A) P).f n ≫
      (relativeMap (chainFunctor R A) f).f n =
    (chainMap R A f.map).f n ≫ (projection (chainFunctor R A) Q).f n at hn
  rw [← Category.assoc, hz, Category.assoc, P202.RelativeSingularChains.ordinary_degree,
    ← Category.assoc, absoluteDegree_natural, Category.assoc, ← hn,
    ← Category.assoc, ← P202.RelativeSingularChains.ordinary_degree, Category.assoc]


section BalancedNaturality
variable {A B : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (C C' : ChainComplex (ModuleCat.{t} R) ℕ)
  (D D' : ChainComplex (ModuleCat.{s} R) ℕ)
  (e : ∀ n, (C.X n ⊗[R] A) ≃ₗ[R] D.X n)
  (e' : ∀ n, (C'.X n ⊗[R] B) ≃ₗ[R] D'.X n)
  (he : ∀ i j x, e j ((C.d i j).hom.rTensor A x) = D.d i j (e i x))
  (he' : ∀ i j x, e' j ((C'.d i j).hom.rTensor B x) = D'.d i j (e' i x))
  (f : C ⟶ C') (g : A →ₗ[R] B) (k : D ⟶ D')
  (h : ∀ n x, e' n (TensorProduct.map (f.f n).hom g x) = k.f n (e n x))

include h in
lemma balancedHomologyComparison_natural (n : ℕ) (x : Algebraic.Homology
    (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A) n) :
    balancedHomologyComparison R B C' D' e' he' n
      (Algebraic.homologyMap
        (P103.Specs.Ch11.ExtTorDefinitions.tensorFirstMap
          (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map f) A ≫
          P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R C') g) n x) =
      HomologicalComplex.homologyMap k n (balancedHomologyComparison R A C D e he n x) := by
  obtain ⟨z, rfl⟩ := (Algebraic.cycleBoundaries _ n).mkQ_surjective x
  apply (quotientHomologyEquiv R D' n).injective
  rw [quotientHomologyEquiv_natural]
  change quotientHomologyEquiv R D' n
      (balancedHomologyComparison R B C' D' e' he' n (Algebraic.homologyClass _ n
        (Algebraic.cyclesMap _ n z))) =
      Algebraic.homologyMap k n (quotientHomologyEquiv R D n
        (balancedHomologyComparison R A C D e he n (Algebraic.homologyClass _ n z)))
  rw [balancedHomologyComparison_formula, balancedHomologyComparison_formula]
  change Algebraic.homologyClass D' n
      (balancedCyclesComparison R B C' D' e' he' n (Algebraic.cyclesMap _ n z)) =
    Algebraic.homologyClass D' n
      (Algebraic.cyclesMap k n (balancedCyclesComparison R A C D e he n z))
  apply congrArg (Algebraic.homologyClass D' n)
  apply Subtype.ext
  have ht : ∀ (x : (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex
      (oppositeComplex R C) A).X n),
      balancedTermComparison R B C' D' e' n
        ((P103.Specs.Ch11.ExtTorDefinitions.tensorFirstMap
          (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map f) A ≫
          P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R C') g).f n x) =
        k.f n (balancedTermComparison R A C D e n x) := by
    intro x
    induction x using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht x a => exact h n (x ⊗ₜ[R] a)
    | ha x y hx hy => simp only [map_add, hx, hy]
  exact ht z.val
end BalancedNaturality

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v t
open P202Specs.UniversalCoefficientsHomology
variable (R : Type u) [CommRing R]
variable {ι : Type*} {c : ComplexShape ι}
variable (C D : HomologicalComplex (ModuleCat.{t} R) c)

@[simp] lemma oppositeQuotientHomologyEquiv_class (n : ι) (z : Algebraic.cycles C n) :
    oppositeQuotientHomologyEquiv R C n (Algebraic.homologyClass C n z) =
      Algebraic.homologyClass (oppositeComplex R C) n (oppositeCyclesEquiv R C n z) := rfl

@[simp] lemma oppositeQuotientHomologyEquiv_symm_class (n : ι)
    (z : Algebraic.cycles (oppositeComplex R C) n) :
    (oppositeQuotientHomologyEquiv R C n).symm
        (Algebraic.homologyClass (oppositeComplex R C) n z) =
      Algebraic.homologyClass C n ((oppositeCyclesEquiv R C n).symm z) := by
  apply (oppositeQuotientHomologyEquiv R C n).injective
  rw [LinearEquiv.apply_symm_apply, oppositeQuotientHomologyEquiv_class,
    LinearEquiv.apply_symm_apply]

lemma oppositeQuotientHomologyEquiv_natural (f : C ⟶ D) (n : ι)
    (x : Algebraic.Homology C n) :
    oppositeQuotientHomologyEquiv R D n (Algebraic.homologyMap f n x) =
      Algebraic.homologyMap (((oppositeFunctor R).mapHomologicalComplex c).map f) n
        (oppositeQuotientHomologyEquiv R C n x) := by
  obtain ⟨z, rfl⟩ := (Algebraic.cycleBoundaries C n).mkQ_surjective x
  rfl

lemma oppositeQuotientHomologyEquiv_symm_natural (f : C ⟶ D) (n : ι)
    (x : Algebraic.Homology (oppositeComplex R C) n) :
    (oppositeQuotientHomologyEquiv R D n).symm
        (Algebraic.homologyMap (((oppositeFunctor R).mapHomologicalComplex c).map f) n x) =
      Algebraic.homologyMap f n ((oppositeQuotientHomologyEquiv R C n).symm x) := by
  apply (oppositeQuotientHomologyEquiv R D n).injective
  rw [LinearEquiv.apply_symm_apply, oppositeQuotientHomologyEquiv_natural,
    LinearEquiv.apply_symm_apply]

@[simp] lemma quotient_oppositeHomologyEquiv (n : ι)
    (x : Algebraic.Homology (oppositeComplex R C) n) :
    quotientHomologyEquiv R C n (oppositeHomologyEquiv R C n x) =
      (oppositeQuotientHomologyEquiv R C n).symm x := by
  change quotientHomologyEquiv R C n ((quotientHomologyEquiv R C n).symm _) = _
  rw [LinearEquiv.apply_symm_apply]

@[simp] lemma oppositeHomologyEquiv_class (n : ι)
    (z : Algebraic.cycles (oppositeComplex R C) n) :
    oppositeHomologyEquiv R C n (Algebraic.homologyClass (oppositeComplex R C) n z) =
      (quotientHomologyEquiv R C n).symm
        (Algebraic.homologyClass C n ((oppositeCyclesEquiv R C n).symm z)) := by
  apply (quotientHomologyEquiv R C n).injective
  rw [quotient_oppositeHomologyEquiv, LinearEquiv.apply_symm_apply,
    oppositeQuotientHomologyEquiv_symm_class]

lemma oppositeHomologyEquiv_natural (f : C ⟶ D) (n : ι)
    (x : Algebraic.Homology (oppositeComplex R C) n) :
    oppositeHomologyEquiv R D n
        (Algebraic.homologyMap (((oppositeFunctor R).mapHomologicalComplex c).map f) n x) =
      HomologicalComplex.homologyMap f n (oppositeHomologyEquiv R C n x) := by
  apply (quotientHomologyEquiv R D n).injective
  rw [quotient_oppositeHomologyEquiv, quotientHomologyEquiv_natural,
    quotient_oppositeHomologyEquiv, oppositeQuotientHomologyEquiv_symm_natural]

variable (A : Type v) [AddCommGroup A] [Module R A]
@[simp] lemma homologyTensorEquiv_tmul (n : ι)
    (x : Algebraic.Homology (oppositeComplex R C) n) (a : A) :
    homologyTensorEquiv R A C n (P103.BalancedTensor.tmul R x a) =
      oppositeHomologyEquiv R C n x ⊗ₜ[R] a := rfl

lemma homologyTensorEquiv_natural {B : Type v} [AddCommGroup B] [Module R B]
    (f : C ⟶ D) (g : A →ₗ[R] B) (n : ι)
    (x : P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R C) n) A) :
    homologyTensorEquiv R B D n
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap
        (Algebraic.homologyMap (((oppositeFunctor R).mapHomologicalComplex c).map f) n) g x) =
      TensorProduct.map (HomologicalComplex.homologyMap f n).hom g
        (homologyTensorEquiv R A C n x) := by
  induction x using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht x a =>
    change oppositeHomologyEquiv R D n (Algebraic.homologyMap
      (((oppositeFunctor R).mapHomologicalComplex c).map f) n x) ⊗ₜ[R] g a =
      HomologicalComplex.homologyMap f n (oppositeHomologyEquiv R C n x) ⊗ₜ[R] g a
    rw [oppositeHomologyEquiv_natural]
  | ha x y hx hy => simp only [map_add, hx, hy]

lemma homologyTensorEquiv_scalar (n : ι) (r : R)
    (x : P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R C) n) A) :
    homologyTensorEquiv R A C n
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id (r • LinearMap.id) x) =
      r • homologyTensorEquiv R A C n x := by
  induction x using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht x a =>
    change oppositeHomologyEquiv R C n x ⊗ₜ[R] (r • a) =
      r • (oppositeHomologyEquiv R C n x ⊗ₜ[R] a)
    exact TensorProduct.tmul_smul r _ _
  | ha x y hx hy => simp only [map_add, smul_add, hx, hy]

section OrdinaryBridge
variable (N : ChainComplex (ModuleCat.{t} R) ℕ)
  (Z : ChainComplex (ModuleCat.{t} R) ℤ)
  (e : ∀ n : ℕ, Z.X (n : ℤ) ≃ₗ[R] N.X n)
  (hd : ∀ (n : ℕ) (x : Z.X (n+1 : ℕ)),
    e n (Z.d (n+1 : ℕ) n x) = N.d (n+1) n (e (n+1) x))
  (hzero : Z.d 0 (-1) = 0)

/-- Canonical bridge from P103's opposite homology to ordinary integer-graded homology. -/
def ordinaryOppositeHomologyEquiv (n : ℕ) :
    Algebraic.Homology (oppositeComplex R N) n ≃ₗ[Rᵐᵒᵖ]
      (oppositeFunctor R).obj (Z.homology (n : ℤ)) :=
  (oppositeHomologyEquiv R N n).trans
    (((oppositeFunctor R).mapIso
      (nonnegativeHomologyEquiv R N Z e hd hzero n).symm.toModuleIso).toLinearEquiv)

/-- The corresponding bridge on the left tensor of the UCT sequence. -/
def ordinaryHomologyTensorEquiv (n : ℕ) :
    P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R N) n) A ≃+
      (Z.homology (n : ℤ) ⊗[R] A) :=
  (homologyTensorEquiv R A N n).trans
    (TensorProduct.congr (nonnegativeHomologyEquiv R N Z e hd hzero n).symm
      (LinearEquiv.refl R A)).toAddEquiv

@[simp] lemma ordinaryHomologyTensorEquiv_tmul (n : ℕ)
    (x : Algebraic.Homology (oppositeComplex R N) n) (a : A) :
    ordinaryHomologyTensorEquiv R A N Z e hd hzero n (P103.BalancedTensor.tmul R x a) =
      ordinaryOppositeHomologyEquiv R N Z e hd hzero n x ⊗ₜ[R] a := rfl

lemma ordinaryHomologyTensorEquiv_scalar (n : ℕ) (r : R)
    (x : P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R N) n) A) :
    ordinaryHomologyTensorEquiv R A N Z e hd hzero n
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id (r • LinearMap.id) x) =
      r • ordinaryHomologyTensorEquiv R A N Z e hd hzero n x := by
  change (TensorProduct.congr (nonnegativeHomologyEquiv R N Z e hd hzero n).symm
      (LinearEquiv.refl R A))
    (homologyTensorEquiv R A N n
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id (r • LinearMap.id) x)) = _
  rw [homologyTensorEquiv_scalar, map_smul]
  rfl

lemma ordinaryHomologyTensorEquiv_symm_scalar (n : ℕ) (r : R)
    (x : Z.homology (n : ℤ) ⊗[R] A) :
    (ordinaryHomologyTensorEquiv R A N Z e hd hzero n).symm (r • x) =
      P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id (r • LinearMap.id)
        ((ordinaryHomologyTensorEquiv R A N Z e hd hzero n).symm x) := by
  apply (ordinaryHomologyTensorEquiv R A N Z e hd hzero n).injective
  rw [AddEquiv.apply_symm_apply, ordinaryHomologyTensorEquiv_scalar,
    AddEquiv.apply_symm_apply]

lemma ordinaryOppositeHomologyEquiv_class (n : ℕ) (z : Algebraic.cycles Z (n : ℤ)) :
    ordinaryOppositeHomologyEquiv R N Z e hd hzero n
      (Algebraic.homologyClass (oppositeComplex R N) n
        (oppositeCyclesEquiv R N n (nonnegativeCyclesEquiv R N Z e hd hzero n z))) =
      (quotientHomologyEquiv R Z n).symm (Algebraic.homologyClass Z n z) := by
  change (nonnegativeHomologyEquiv R N Z e hd hzero n).symm
    (oppositeHomologyEquiv R N n _) = _
  rw [oppositeHomologyEquiv_class, LinearEquiv.symm_apply_apply]
  apply (nonnegativeHomologyEquiv R N Z e hd hzero n).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [nonnegativeHomologyEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rfl

lemma ordinaryHomologyTensorEquiv_class (n : ℕ) (z : Algebraic.cycles Z (n : ℤ)) (a : A) :
    ordinaryHomologyTensorEquiv R A N Z e hd hzero n
      (P103.BalancedTensor.tmul R
        (Algebraic.homologyClass (oppositeComplex R N) n
          (oppositeCyclesEquiv R N n (nonnegativeCyclesEquiv R N Z e hd hzero n z))) a) =
      (quotientHomologyEquiv R Z n).symm (Algebraic.homologyClass Z n z) ⊗ₜ[R] a := by
  rw [ordinaryHomologyTensorEquiv_tmul, ordinaryOppositeHomologyEquiv_class]

lemma ordinaryOppositeHomologyEquiv_class' (n : ℕ)
    (z : Algebraic.cycles (oppositeComplex R N) n) :
    ordinaryOppositeHomologyEquiv R N Z e hd hzero n
      (Algebraic.homologyClass (oppositeComplex R N) n z) =
      (quotientHomologyEquiv R Z n).symm
        (Algebraic.homologyClass Z n ((nonnegativeCyclesEquiv R N Z e hd hzero n).symm
          ((oppositeCyclesEquiv R N n).symm z))) := by
  have h := ordinaryOppositeHomologyEquiv_class R N Z e hd hzero n
    ((nonnegativeCyclesEquiv R N Z e hd hzero n).symm
      ((oppositeCyclesEquiv R N n).symm z))
  simpa only [LinearEquiv.apply_symm_apply] using h

variable (N' : ChainComplex (ModuleCat.{t} R) ℕ)
  (Z' : ChainComplex (ModuleCat.{t} R) ℤ)
  (e' : ∀ n : ℕ, Z'.X (n : ℤ) ≃ₗ[R] N'.X n)
  (hd' : ∀ (n : ℕ) (x : Z'.X (n+1 : ℕ)),
    e' n (Z'.d (n+1 : ℕ) n x) = N'.d (n+1) n (e' (n+1) x))
  (hzero' : Z'.d 0 (-1) = 0)

lemma ordinaryOppositeHomologyEquiv_natural (f : N ⟶ N') (F : Z ⟶ Z')
    (hf : ∀ (n : ℕ) (x : Z.X (n : ℤ)), e' n (F.f n x) = f.f n (e n x))
    (n : ℕ) (x : Algebraic.Homology (oppositeComplex R N) n) :
    ordinaryOppositeHomologyEquiv R N' Z' e' hd' hzero' n
      (Algebraic.homologyMap
        (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map f) n x) =
      HomologicalComplex.homologyMap F (n : ℤ)
        (ordinaryOppositeHomologyEquiv R N Z e hd hzero n x) := by
  obtain ⟨z, rfl⟩ := (Algebraic.cycleBoundaries (oppositeComplex R N) n).mkQ_surjective x
  change ordinaryOppositeHomologyEquiv R N' Z' e' hd' hzero' n
      (Algebraic.homologyClass (oppositeComplex R N') n
        (Algebraic.cyclesMap
          (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map f) n z)) =
      HomologicalComplex.homologyMap F (n : ℤ)
        (ordinaryOppositeHomologyEquiv R N Z e hd hzero n
          (Algebraic.homologyClass (oppositeComplex R N) n z))
  erw [ordinaryOppositeHomologyEquiv_class', ordinaryOppositeHomologyEquiv_class']
  apply (quotientHomologyEquiv R Z' n).injective
  rw [LinearEquiv.apply_symm_apply, quotientHomologyEquiv_natural,
    LinearEquiv.apply_symm_apply]
  apply congrArg (Algebraic.homologyClass Z' (n : ℤ))
  apply Subtype.ext
  change (e' n).symm (f.f n z.val) = F.f (n : ℤ) ((e n).symm z.val)
  apply (e' n).injective
  rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]

lemma ordinaryHomologyTensorEquiv_natural {B : Type v} [AddCommGroup B] [Module R B]
    (f : N ⟶ N') (F : Z ⟶ Z') (g : A →ₗ[R] B)
    (hf : ∀ (n : ℕ) (x : Z.X (n : ℤ)), e' n (F.f n x) = f.f n (e n x))
    (n : ℕ)
    (x : P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R N) n) A) :
    ordinaryHomologyTensorEquiv R B N' Z' e' hd' hzero' n
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap
        (Algebraic.homologyMap
          (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map f) n) g x) =
      TensorProduct.map (HomologicalComplex.homologyMap F (n : ℤ)).hom g
        (ordinaryHomologyTensorEquiv R A N Z e hd hzero n x) := by
  induction x using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht x a =>
    change ordinaryOppositeHomologyEquiv R N' Z' e' hd' hzero' n
      (Algebraic.homologyMap
        (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map f) n x) ⊗ₜ[R] g a =
      HomologicalComplex.homologyMap F (n : ℤ)
        (ordinaryOppositeHomologyEquiv R N Z e hd hzero n x) ⊗ₜ[R] g a
    rw [ordinaryOppositeHomologyEquiv_natural R N Z e hd hzero N' Z' e' hd' hzero' f F hf]
  | ha x y hx hy => simp only [map_add, hx, hy]

end OrdinaryBridge

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
open CategoryTheory
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
noncomputable section
universe u t v
variable (R : Type u) [CommRing R]

/-- Transport of genuine Tor along an isomorphism in its first argument. -/
def torLinearEquiv (n : ℕ) (T : TorMaps.{u,t,v} R n)
    {V W : ModuleCat.{t} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ V)
    (Q : ProjectiveChoice Rᵐᵒᵖ W) (e : V ≃ₗ[Rᵐᵒᵖ] W)
    (A : ModuleCat.{v} R) :
    letI := torModule T P A
    letI := torModule T Q A
    TorWith P.val A n ≃ₗ[R] TorWith Q.val A n := by
  letI := torModule T P A
  letI := torModule T Q A
  refine
    { toFun := T.map P Q (ModuleCat.ofHom e.toLinearMap) (𝟙 A)
      invFun := T.map Q P (ModuleCat.ofHom e.symm.toLinearMap) (𝟙 A)
      left_inv := ?_
      right_inv := ?_
      map_add' := map_add _
      map_smul' := fun r x => P103.Ch11.ExtTorDefinitions.tor_linear R n T P Q
        (ModuleCat.ofHom e.toLinearMap) (𝟙 A) r x }
  · intro x
    have h := T.comp P Q P (ModuleCat.ofHom e.toLinearMap)
      (ModuleCat.ofHom e.symm.toLinearMap) (𝟙 A) (𝟙 A)
    have he : ModuleCat.ofHom e.toLinearMap ≫ ModuleCat.ofHom e.symm.toLinearMap = 𝟙 V := by
      ext x
      exact e.symm_apply_apply x
    rw [he, Category.id_comp, T.id] at h
    exact (LinearMap.congr_fun h x).symm
  · intro x
    have h := T.comp Q P Q (ModuleCat.ofHom e.symm.toLinearMap)
      (ModuleCat.ofHom e.toLinearMap) (𝟙 A) (𝟙 A)
    have he : ModuleCat.ofHom e.symm.toLinearMap ≫ ModuleCat.ofHom e.toLinearMap = 𝟙 W := by
      ext x
      exact e.apply_symm_apply x
    rw [he, Category.id_comp, T.id] at h
    exact (LinearMap.congr_fun h x).symm

/-- Every projective model of positive Tor of a zero module is zero. -/
theorem tor_subsingleton_of_subsingleton {V : ModuleCat.{t} Rᵐᵒᵖ}
    [Subsingleton V] (P : ProjectiveChoice Rᵐᵒᵖ V) (A : ModuleCat.{v} R) (n : ℕ) :
    Subsingleton (TorWith P.val A (n+1)) := by
  exact P103.Ch11.VanishingAndFlatness.tor_right_flat R V A
    (P103.Ch11.FlatResolutions.rightFlat_of_subsingleton V) P.val P.property n

/-- Genuine Tor transport respects simultaneous maps of both arguments. -/
theorem torLinearEquiv_natural (n : ℕ) (T : TorMaps.{u,t,v} R n)
    {V W V' W' : ModuleCat.{t} Rᵐᵒᵖ}
    (P : ProjectiveChoice Rᵐᵒᵖ V) (Q : ProjectiveChoice Rᵐᵒᵖ W)
    (P' : ProjectiveChoice Rᵐᵒᵖ V') (Q' : ProjectiveChoice Rᵐᵒᵖ W')
    (e : V ≃ₗ[Rᵐᵒᵖ] W) (e' : V' ≃ₗ[Rᵐᵒᵖ] W')
    {A A' : ModuleCat.{v} R} (f : V ⟶ V') (h : W ⟶ W') (g : A ⟶ A')
    (he : ModuleCat.ofHom e.toLinearMap ≫ h = f ≫ ModuleCat.ofHom e'.toLinearMap)
    (x : TorWith P.val A n) :
    T.map Q Q' h g (torLinearEquiv R n T P Q e A x) =
      torLinearEquiv R n T P' Q' e' A' (T.map P P' f g x) := by
  change ((T.map Q Q' h g).comp (T.map P Q (ModuleCat.ofHom e.toLinearMap) (𝟙 A))) x =
    ((T.map P' Q' (ModuleCat.ofHom e'.toLinearMap) (𝟙 A')).comp (T.map P P' f g)) x
  rw [← T.comp, ← T.comp, he]
  simp

/-- The negative ordinary absolute homology used by T27 has vanishing Tor. -/
theorem ordinary_negative_tor (A : ModuleCat.{v} R) (X : TopCat.{t})
    (i : ℤ) (hi : i < 0)
    (P : ProjectiveChoice Rᵐᵒᵖ
      ((P202Specs.UniversalCoefficientsHomology.oppositeFunctor R).obj
        (P202Specs.SingularChains.homology R R X i))) (n : ℕ) :
    Subsingleton (TorWith P.val A (n+1)) := by
  letI : Subsingleton (P202Specs.SingularChains.homology R R X i) :=
    ModuleCat.subsingleton_of_isZero
      (P202.SingularChains.ordinary_negative_homology R R X i hi)
  letI : Subsingleton ((P202Specs.UniversalCoefficientsHomology.oppositeFunctor R).obj
      (P202Specs.SingularChains.homology R R X i)) := by
    change Subsingleton (P202Specs.SingularChains.homology R R X i)
    infer_instance
  exact tor_subsingleton_of_subsingleton R P A n

/-- The relative ordinary negative homology has the same vanishing endpoint. -/
theorem relative_negative_tor (A : ModuleCat.{v} R)
    (X : P202Specs.RelativeSingularChains.Pair.{t}) (i : ℤ) (hi : i < 0)
    (P : ProjectiveChoice Rᵐᵒᵖ
      ((P202Specs.UniversalCoefficientsHomology.oppositeFunctor R).obj
        ((P202Specs.RelativeSingularChains.ordinary R R X).homology i))) (n : ℕ) :
    Subsingleton (TorWith P.val A (n+1)) := by
  letI : Subsingleton ((P202Specs.RelativeSingularChains.ordinary R R X).homology i) :=
    ModuleCat.subsingleton_of_isZero
      (P202.RelativeSingularChains.ordinary_negative R R X i hi).2
  letI : Subsingleton ((P202Specs.UniversalCoefficientsHomology.oppositeFunctor R).obj
      ((P202Specs.RelativeSingularChains.ordinary R R X).homology i)) := by
    change Subsingleton ((P202Specs.RelativeSingularChains.ordinary R R X).homology i)
    infer_instance
  exact tor_subsingleton_of_subsingleton R P A n
end
end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v w
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.UniversalCoefficientsHomology
variable (R : Type u) [CommRing R]
variable (A : Type v) [AddCommGroup A] [Module R A]
variable {B : Type v} [AddCommGroup B] [Module R B]

lemma ordinaryCoefficientMap_degree (g : A →ₗ[R] B) (X : TopCat.{w}) (n : ℕ) :
    (ordinaryCoefficientMap R A g X).f (n : ℤ) ≫ (ordinaryNonnegativeIso R B X n).hom =
      (ordinaryNonnegativeIso R A X n).hom ≫ (coefficientMap R A g X).f n := by
  unfold ordinaryCoefficientMap
  rw [HomologicalComplex.extendMap_f _ _ (i := n) (by change (0 : ℤ)+n = n; omega)]
  simp [ordinaryNonnegativeIso]

lemma relativeOrdinaryCoefficientMap_degree (g : A →ₗ[R] B) (P : Pair.{w}) (n : ℕ) :
    (relativeOrdinaryCoefficientMap R A g P).f (n : ℤ) ≫ (ordinaryDegreeIso R B P n).hom =
      (ordinaryDegreeIso R A P n).hom ≫ (relativeCoefficientMap R A g P).f n := by
  apply (cancel_epi ((projection (ordinaryFunctor R A) P).f (n : ℤ))).mp
  have hz := congrArg (fun φ => φ.f (n : ℤ)) (cokernel.π_desc
    (inclusion (ordinaryFunctor R A) P)
    (ordinaryCoefficientMap R A g P.space ≫ projection (ordinaryFunctor R B) P)
    (by rw [← Category.assoc, ordinaryCoefficientMap_inclusion, Category.assoc,
          cokernel.condition, HasZeroMorphisms.comp_zero]))
  have hn := congrArg (fun φ => φ.f n) (cokernel.π_desc
    (inclusion (chainFunctor R A) P)
    (coefficientMap R A g P.space ≫ projection (chainFunctor R B) P)
    (by rw [← Category.assoc, coefficientMap_inclusion, Category.assoc,
          cokernel.condition, HasZeroMorphisms.comp_zero]))
  change (projection (ordinaryFunctor R A) P).f (n : ℤ) ≫
      (relativeOrdinaryCoefficientMap R A g P).f (n : ℤ) =
    (ordinaryCoefficientMap R A g P.space).f (n : ℤ) ≫
      (projection (ordinaryFunctor R B) P).f (n : ℤ) at hz
  change (projection (chainFunctor R A) P).f n ≫ (relativeCoefficientMap R A g P).f n =
    (coefficientMap R A g P.space).f n ≫ (projection (chainFunctor R B) P).f n at hn
  rw [← Category.assoc, hz, Category.assoc, P202.RelativeSingularChains.ordinary_degree,
    ← Category.assoc, ordinaryCoefficientMap_degree, Category.assoc, ← hn,
    ← Category.assoc, ← P202.RelativeSingularChains.ordinary_degree, Category.assoc]

lemma absoluteTensorEquiv_mixed (g : A →ₗ[R] B) {X Y : TopCat.{w}} (f : X ⟶ Y)
    (n : ℕ) (c : Chains R X n ⊗[R] A) :
    tensorEquiv R B Y n (TensorProduct.map ((chainMap R R f).f n).hom g c) =
      (chainMap R A f ≫ coefficientMap R A g Y).f n (tensorEquiv R A X n c) := by
  have ht : TensorProduct.map ((chainMap R R f).f n).hom g c =
      TensorProduct.map LinearMap.id g (((chainMap R R f).f n).hom.rTensor A c) := by
    induction c using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x a => rfl
  rw [ht]
  erw [absoluteTensor_coefficient, P202.SingularChains.tensorEquiv_natural]
  rfl

lemma relativeTensorEquiv_mixed (g : A →ₗ[R] B) {P Q : Pair.{w}} (f : P ⟶ Q)
    (n : ℕ) (c : (nonnegative R R P).X n ⊗[R] A) :
    relativeTensorEquiv R B Q n
      (TensorProduct.map ((relativeMap (chainFunctor R R) f).f n).hom g c) =
      (relativeMap (chainFunctor R A) f ≫ relativeCoefficientMap R A g Q).f n
        (relativeTensorEquiv R A P n c) := by
  have ht : TensorProduct.map ((relativeMap (chainFunctor R R) f).f n).hom g c =
      TensorProduct.map LinearMap.id g
        (((relativeMap (chainFunctor R R) f).f n).hom.rTensor A c) := by
    induction c using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x a => rfl
  rw [ht, relativeTensorEquiv_coefficient, relativeTensorEquiv_natural]
  rfl


lemma absoluteDegree_mixed (g : A →ₗ[R] B) {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g Y).f (n : ℤ) ≫
      (ordinaryNonnegativeIso R B Y n).hom =
    (ordinaryNonnegativeIso R A X n).hom ≫
      (chainMap R A f ≫ coefficientMap R A g Y).f n := by
  change (((ordinaryFunctor R A).map f).f (n : ℤ) ≫
      (ordinaryCoefficientMap R A g Y).f (n : ℤ)) ≫ _ =
    _ ≫ (chainMap R A f).f n ≫ (coefficientMap R A g Y).f n
  rw [Category.assoc, ordinaryCoefficientMap_degree, ← Category.assoc,
    absoluteDegree_natural, Category.assoc]

lemma relativeDegree_mixed (g : A →ₗ[R] B) {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ) :
    (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g Q).f
        (n : ℤ) ≫ (ordinaryDegreeIso R B Q n).hom =
    (ordinaryDegreeIso R A P n).hom ≫
      (relativeMap (chainFunctor R A) f ≫ relativeCoefficientMap R A g Q).f n := by
  change ((relativeMap (ordinaryFunctor R A) f).f (n : ℤ) ≫
      (relativeOrdinaryCoefficientMap R A g Q).f (n : ℤ)) ≫ _ =
    _ ≫ (relativeMap (chainFunctor R A) f).f n ≫ (relativeCoefficientMap R A g Q).f n
  rw [Category.assoc, relativeOrdinaryCoefficientMap_degree, ← Category.assoc,
    relativeDegree_natural, Category.assoc]


@[reassoc] lemma relativeCoefficientMap_projection (g : A →ₗ[R] B) (P : Pair.{w}) :
    projection (chainFunctor R A) P ≫ relativeCoefficientMap R A g P =
      coefficientMap R A g P.space ≫ projection (chainFunctor R B) P :=
  cokernel.π_desc _ _ _

@[reassoc] lemma relativeOrdinaryCoefficientMap_projection (g : A →ₗ[R] B) (P : Pair.{w}) :
    projection (ordinaryFunctor R A) P ≫ relativeOrdinaryCoefficientMap R A g P =
      ordinaryCoefficientMap R A g P.space ≫ projection (ordinaryFunctor R B) P :=
  cokernel.π_desc _ _ _

lemma relativeCoefficientMap_natural (g : A →ₗ[R] B) {P Q : Pair.{w}} (f : P ⟶ Q) :
    relativeMap (chainFunctor R A) f ≫ relativeCoefficientMap R A g Q =
      relativeCoefficientMap R A g P ≫ relativeMap (chainFunctor R B) f := by
  apply (cancel_epi (projection (chainFunctor R A) P)).mp
  rw [← Category.assoc, projection_map, Category.assoc, relativeCoefficientMap_projection,
    ← Category.assoc, coefficientMap_natural, Category.assoc, ← projection_map,
    ← Category.assoc, ← relativeCoefficientMap_projection, Category.assoc]

lemma relativeOrdinaryCoefficientMap_natural (g : A →ₗ[R] B) {P Q : Pair.{w}} (f : P ⟶ Q) :
    relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g Q =
      relativeOrdinaryCoefficientMap R A g P ≫ relativeMap (ordinaryFunctor R B) f := by
  apply (cancel_epi (projection (ordinaryFunctor R A) P)).mp
  rw [← Category.assoc, projection_map, Category.assoc,
    relativeOrdinaryCoefficientMap_projection, ← Category.assoc,
    ordinaryCoefficientMap_natural, Category.assoc, ← projection_map,
    ← Category.assoc, ← relativeOrdinaryCoefficientMap_projection, Category.assoc]

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v t s q
open P202Specs.UniversalCoefficientsHomology
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison
variable (R : Type u) [CommRing R]

variable {R} {L₀ M₀ N₀ L M N : Type*}
  [AddCommGroup L₀] [AddCommGroup M₀] [AddCommGroup N₀]
  [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
  [Module R L] [Module R M] [Module R N]

def transportLinearMap (f : L₀ →+ M₀) (e : L₀ ≃+ L) (e' : M₀ ≃+ M)
    (F : R → L₀ → L₀) (G : R → M₀ → M₀)
    (he : ∀ r x, e (F r x) = r • e x)
    (he' : ∀ r x, e' (G r x) = r • e' x)
    (hf : ∀ r x, f (F r x) = G r (f x)) : L →ₗ[R] M where
  toFun x := e' (f (e.symm x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    have h : e.symm (r • x) = F r (e.symm x) := by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    rw [h, hf, he']
    rfl

/-- Transport preserves the full split exact sequence, with specified scalar
endomorphisms on the algebraic models. -/
def transportSplitExact
    (α : L₀ →+ M₀) (β : M₀ →+ N₀)
    (hα : Function.Injective α) (hex : Function.Exact α β)
    (hβ : Function.Surjective β)
    (eL : L₀ ≃+ L) (eM : M₀ ≃+ M) (eN : N₀ ≃+ N)
    (FL : R → L₀ → L₀) (FM : R → M₀ → M₀) (FN : R → N₀ → N₀)
    (hL : ∀ r x, eL (FL r x) = r • eL x)
    (hM : ∀ r x, eM (FM r x) = r • eM x)
    (hN : ∀ r x, eN (FN r x) = r • eN x)
    (hαs : ∀ r x, α (FL r x) = FM r (α x))
    (hβs : ∀ r x, β (FM r x) = FN r (β x))
    (hs : ∃ σ : N₀ →+ M₀, β.comp σ = AddMonoidHom.id N₀ ∧
      ∀ r x, σ (FN r x) = FM r (σ x)) : SplitExactSequence R L M N := by
  let a := transportLinearMap α eL eM FL FM hL hM hαs
  let b := transportLinearMap β eM eN FM FN hM hN hβs
  refine ⟨a, b, eM.injective.comp (hα.comp eL.symm.injective), ?_,
    eN.surjective.comp (hβ.comp eM.symm.surjective), ?_⟩
  · intro x
    change eN (β (eM.symm x)) = 0 ↔ ∃ y, eM (α (eL.symm y)) = x
    rw [← eN.map_zero, eN.injective.eq_iff, hex]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨eL y, ?_⟩
      rw [eL.symm_apply_apply, hy, eM.apply_symm_apply]
    · rintro ⟨y, hy⟩
      exact ⟨eL.symm y, eM.injective (hy.trans (eM.apply_symm_apply x).symm)⟩
  · obtain ⟨σ, hσ, hσs⟩ := hs
    refine ⟨transportLinearMap σ eN eM FN FM hN hM hσs, ?_⟩
    apply LinearMap.ext
    intro x
    change eN (β (eM.symm (eM (σ (eN.symm x))))) = x
    rw [eM.symm_apply_apply]
    have h := DFunLike.congr_fun hσ (eN.symm x)
    change β (σ (eN.symm x)) = eN.symm x at h
    rw [h, eN.apply_symm_apply]

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v t s q
open P202Specs.UniversalCoefficientsHomology
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison
variable (R : Type u) [CommRing R]

def positiveLinearSequence (U : UniversalCoefficients.{u,t,v} R)
    (C : Complex.{u,t} R) (hC : FlatTermsAndBoundaries.{u,t,v} C)
    (A : ModuleCat.{v} R) (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology C n)))
    (T : TorMaps.{u,t,v} R 1) (hs : AlgebraicUCT.ScalarSplittings R U C hC)
    {L M N : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (eL : P103.BalancedTensor.Tensor R (Algebraic.Homology C (n+1)) A ≃+ L)
    (eM : Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex C A) (n+1) ≃+ M)
    (eN : TorWith P.val A 1 ≃+ N)
    (hL : ∀ r x, eL (tensorMap LinearMap.id (scalarMap A r).hom x) = r • eL x)
    (hM : ∀ r x, eM (Algebraic.homologyMap (tensorSecondMap C (scalarMap A r).hom) (n+1) x) = r • eM x)
    (hN : ∀ r x, eN (T.map P P (𝟙 _) (scalarMap A r) x) = r • eN x) :
    SplitExactSequence R L M N := by
  let S := U.positive C hC A n P
  have hsc := (P103.Ch11.UniversalCoefficientsHomology.scalar_compatibility R U C hC A).2 n P T
  apply transportSplitExact S.α.toAddMonoidHom S.β.toAddMonoidHom
    S.injective_α S.exact S.surjective_β eL eM eN
    (fun r => tensorMap LinearMap.id (scalarMap A r).hom)
    (fun r => Algebraic.homologyMap (tensorSecondMap C (scalarMap A r).hom) (n+1))
    (fun r => T.map P P (𝟙 _) (scalarMap A r)) hL hM hN
  · intro r x
    exact (LinearMap.congr_fun (hsc.1 r) x).symm
  · intro r x
    exact hsc.2 r x
  · letI := torModule T P A
    obtain ⟨σ, hσ, hσs⟩ := (hs A).2 n P T
    refine ⟨σ.toAddMonoidHom, ?_, hσs⟩
    exact congrArg LinearMap.toAddMonoidHom hσ

@[simp] lemma positiveLinearSequence_α (U : UniversalCoefficients.{u,t,v} R)
    (C : Complex.{u,t} R) (hC : FlatTermsAndBoundaries.{u,t,v} C)
    (A : ModuleCat.{v} R) (n : ℕ)
    (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology C n)))
    (T : TorMaps.{u,t,v} R 1) (hs : AlgebraicUCT.ScalarSplittings R U C hC)
    {L M N : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (eL : P103.BalancedTensor.Tensor R (Algebraic.Homology C (n+1)) A ≃+ L)
    (eM : Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex C A) (n+1) ≃+ M)
    (eN : TorWith P.val A 1 ≃+ N)
    (hL : ∀ r x, eL (tensorMap LinearMap.id (scalarMap A r).hom x) = r • eL x)
    (hM : ∀ r x, eM (Algebraic.homologyMap (tensorSecondMap C (scalarMap A r).hom) (n+1) x) = r • eM x)
    (hN : ∀ r x, eN (T.map P P (𝟙 _) (scalarMap A r) x) = r • eN x) (x : L) :
    (positiveLinearSequence R U C hC A n P T hs eL eM eN hL hM hN).α x =
      eM ((U.positive C hC A n P).α (eL.symm x)) := rfl

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u t v l m
open P202Specs.UniversalCoefficientsHomology
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.ExtTorDefinitions
variable (R : Type u) [CommRing R]

/-- The degree-zero algebraic edge map transports to an isomorphism for the
specified standard scalar actions. Its value is the prescribed conjugation. -/
def zeroLinearEquiv
    (U : UniversalCoefficients.{u,t,v} R)
    (C : Complex.{u,t} R) (hC : FlatTermsAndBoundaries.{u,t,v} C)
    (A : ModuleCat.{v} R)
    {L : Type l} {M : Type m} [AddCommGroup L] [AddCommGroup M]
    [Module R L] [Module R M]
    (eL : P103.BalancedTensor.Tensor R (Algebraic.Homology C 0) A ≃+ L)
    (eM : Algebraic.Homology (tensorComplex C A) 0 ≃+ M)
    (hL : ∀ r x, eL (tensorMap LinearMap.id (scalarMap A r).hom x) = r • eL x)
    (hM : ∀ r x, eM (Algebraic.homologyMap
      (tensorSecondMap C (scalarMap A r).hom) 0 x) = r • eM x) : L ≃ₗ[R] M := by
  let a : L →ₗ[R] M :=
    { toFun := fun x => eM ((U.zero C hC A).α (eL.symm x))
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro r x
        have h : eL.symm (r • x) = tensorMap LinearMap.id (scalarMap A r).hom (eL.symm x) := by
          apply eL.injective
          rw [eL.apply_symm_apply, hL, eL.apply_symm_apply]
        rw [h]
        have hs := LinearMap.congr_fun
          ((P103.Ch11.UniversalCoefficientsHomology.scalar_compatibility R U C hC A).1 r)
          (eL.symm x)
        change Algebraic.homologyMap (tensorSecondMap C (scalarMap A r).hom) 0
          ((U.zero C hC A).α (eL.symm x)) =
          (U.zero C hC A).α (tensorMap LinearMap.id (scalarMap A r).hom (eL.symm x)) at hs
        rw [← hs, hM]
        rfl }
  exact LinearEquiv.ofBijective a
    ⟨eM.injective.comp ((U.zero C hC A).bijective_α.1.comp eL.symm.injective),
      eM.surjective.comp ((U.zero C hC A).bijective_α.2.comp eL.symm.surjective)⟩

@[simp] theorem zeroLinearEquiv_apply
    (U : UniversalCoefficients.{u,t,v} R)
    (C : Complex.{u,t} R) (hC : FlatTermsAndBoundaries.{u,t,v} C)
    (A : ModuleCat.{v} R)
    {L : Type l} {M : Type m} [AddCommGroup L] [AddCommGroup M]
    [Module R L] [Module R M]
    (eL : P103.BalancedTensor.Tensor R (Algebraic.Homology C 0) A ≃+ L)
    (eM : Algebraic.Homology (tensorComplex C A) 0 ≃+ M)
    (hL : ∀ r x, eL (tensorMap LinearMap.id (scalarMap A r).hom x) = r • eL x)
    (hM : ∀ r x, eM (Algebraic.homologyMap
      (tensorSecondMap C (scalarMap A r).hom) 0 x) = r • eM x)
    (x : L) :
    zeroLinearEquiv R U C hC A eL eM hL hM x = eM ((U.zero C hC A).α (eL.symm x)) := rfl
end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology

/-- Transport a naturality square through specified additive comparisons.
The arrow maps may be linear maps or additive homomorphisms via coercion. -/
theorem conjugate_natural
    {L₀ M₀ L₀' M₀' L M L' M' : Type*}
    [Add L₀] [Add M₀] [Add L₀'] [Add M₀']
    [Add L] [Add M] [Add L'] [Add M']
    (α : L₀ → M₀) (α' : L₀' → M₀')
    (f₀ : L₀ → L₀') (g₀ : M₀ → M₀')
    (eL : L₀ ≃+ L) (eM : M₀ ≃+ M)
    (eL' : L₀' ≃+ L') (eM' : M₀' ≃+ M')
    (f : L → L') (g : M → M')
    (hα : ∀ x, g₀ (α x) = α' (f₀ x))
    (hL : ∀ x, eL' (f₀ x) = f (eL x))
    (hM : ∀ x, eM' (g₀ x) = g (eM x))
    (x : L) :
    g (eM (α (eL.symm x))) = eM' (α' (eL'.symm (f x))) := by
  rw [← hM, hα]
  congr 2
  apply eL'.injective
  rw [eL'.apply_symm_apply, hL, eL.apply_symm_apply]

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v t s
open P202Specs.UniversalCoefficientsHomology
open P103.Specs.Ch11.UniversalCoefficientsHomology
variable (R : Type u) [CommRing R]
variable (A : Type v) [AddCommGroup A] [Module R A]
variable (C : ChainComplex (ModuleCat.{t} R) ℕ)
  (D : ChainComplex (ModuleCat.{s} R) ℕ)
  (e : ∀ n, (C.X n ⊗[R] A) ≃ₗ[R] D.X n)
  (he : ∀ i j x, e j ((C.d i j).hom.rTensor A x) = D.d i j (e i x))
  (W : ChainComplex (ModuleCat.{s} R) ℤ)
  (ew : ∀ n : ℕ, W.X (n : ℤ) ≃ₗ[R] D.X n)
  (hdw : ∀ (n : ℕ) (x : W.X (n+1 : ℕ)),
    ew n (W.d (n+1 : ℕ) n x) = D.d (n+1) n (ew (n+1) x))
  (hzw : W.d 0 (-1) = 0)

/-- Balanced coefficient homology compared to the actual integer-graded homology. -/
def ordinaryBalancedHomologyComparison (n : ℕ) :
    Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex
      (oppositeComplex R C) A) n ≃+ W.homology (n : ℤ) :=
  (balancedHomologyComparison R A C D e he n).trans
    (nonnegativeHomologyEquiv R D W ew hdw hzw n).symm.toAddEquiv

lemma ordinaryBalancedHomologyComparison_scalar (n : ℕ) (r : R)
    (x : Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex
      (oppositeComplex R C) A) n) :
    ordinaryBalancedHomologyComparison R A C D e he W ew hdw hzw n
      (Algebraic.homologyMap
        (P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R C)
          (r • (LinearMap.id : A →ₗ[R] A))) n x) =
      r • ordinaryBalancedHomologyComparison R A C D e he W ew hdw hzw n x := by
  change (nonnegativeHomologyEquiv R D W ew hdw hzw n).symm
    (balancedHomologyComparison R A C D e he n _) = _
  rw [balancedHomologyComparison_scalar, map_smul]
  rfl

lemma ordinaryBalancedHomologyComparison_formula (n : ℕ)
    (z : Algebraic.cycles (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex
      (oppositeComplex R C) A) n) :
    ∃ z' : Algebraic.cycles W (n : ℤ),
      ew n z'.val = e n (balancedTensorEquiv R A (C.X n) z.val) ∧
      quotientHomologyEquiv R W n
        (ordinaryBalancedHomologyComparison R A C D e he W ew hdw hzw n
          (Algebraic.homologyClass _ n z)) = Algebraic.homologyClass W n z' := by
  let zD := balancedCyclesComparison R A C D e he n z
  refine ⟨(nonnegativeCyclesEquiv R D W ew hdw hzw n).symm zD, ?_, ?_⟩
  · change ew n ((ew n).symm (e n (balancedTensorEquiv R A (C.X n) z.val))) = _
    rw [LinearEquiv.apply_symm_apply]
  · change quotientHomologyEquiv R W n ((quotientHomologyEquiv R W n).symm
      ((nonnegativeQuotientHomologyEquiv R D W ew hdw hzw n).symm
        (quotientHomologyEquiv R D n
          (balancedHomologyComparison R A C D e he n
            (Algebraic.homologyClass _ n z))))) = _
    rw [LinearEquiv.apply_symm_apply, balancedHomologyComparison_formula]
    apply (nonnegativeQuotientHomologyEquiv R D W ew hdw hzw n).injective
    rw [LinearEquiv.apply_symm_apply]
    change Algebraic.homologyClass D n zD = Algebraic.homologyClass D n
      ((nonnegativeCyclesEquiv R D W ew hdw hzw n)
        ((nonnegativeCyclesEquiv R D W ew hdw hzw n).symm zD))
    rw [LinearEquiv.apply_symm_apply]

variable (Z : ChainComplex (ModuleCat.{t} R) ℤ)
  (ez : ∀ n : ℕ, Z.X (n : ℤ) ≃ₗ[R] C.X n)
  (hdz : ∀ (n : ℕ) (x : Z.X (n+1 : ℕ)),
    ez n (Z.d (n+1 : ℕ) n x) = C.d (n+1) n (ez (n+1) x))
  (hzz : Z.d 0 (-1) = 0)

/-- Any algebraic UCT left arrow with its prescribed cycle formula transports
with the expected representative formula, in degree zero and positive degrees. -/
lemma ordinaryUCTAlpha_formula (n : ℕ)
    (α : P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R C) n) A →ₗ[ℤ]
      Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex
        (oppositeComplex R C) A) n)
    (hα : ∀ (z : Algebraic.cycles (oppositeComplex R C) n) (a : A),
      α (P103.BalancedTensor.tmul R (Algebraic.homologyClass _ n z) a) =
        Algebraic.homologyClass _ n
          (tensorCycle (oppositeComplex R C) (ModuleCat.of R A) n z a))
    (z : Algebraic.cycles Z (n : ℤ)) (a : A) :
    ∃ z' : Algebraic.cycles W (n : ℤ),
      ew n z'.val = e n (ez n z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R W n
        (ordinaryBalancedHomologyComparison R A C D e he W ew hdw hzw n
          (α ((ordinaryHomologyTensorEquiv R A C Z ez hdz hzz n).symm
            ((quotientHomologyEquiv R Z n).symm (Algebraic.homologyClass Z n z) ⊗ₜ[R] a)))) =
          Algebraic.homologyClass W n z' := by
  let zC := oppositeCyclesEquiv R C n (nonnegativeCyclesEquiv R C Z ez hdz hzz n z)
  have hL : (ordinaryHomologyTensorEquiv R A C Z ez hdz hzz n).symm
      ((quotientHomologyEquiv R Z n).symm (Algebraic.homologyClass Z n z) ⊗ₜ[R] a) =
      P103.BalancedTensor.tmul R (Algebraic.homologyClass _ n zC) a := by
    apply (ordinaryHomologyTensorEquiv R A C Z ez hdz hzz n).injective
    rw [AddEquiv.apply_symm_apply]
    exact (ordinaryHomologyTensorEquiv_class R A C Z ez hdz hzz n z a).symm
  rw [hL, hα]
  obtain ⟨z', hv, hq⟩ := ordinaryBalancedHomologyComparison_formula R A C D e he W ew hdw hzw n
    (tensorCycle (oppositeComplex R C) (ModuleCat.of R A) n zC a)
  exact ⟨z', hv, hq⟩

lemma ordinaryUCTZeroAlpha_formula
    (S : ZeroSequence (oppositeComplex R C) (ModuleCat.of R A))
    (z : Algebraic.cycles Z (0 : ℤ)) (a : A) :
    ∃ z' : Algebraic.cycles W (0 : ℤ),
      ew 0 z'.val = e 0 (ez 0 z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R W 0
        (ordinaryBalancedHomologyComparison R A C D e he W ew hdw hzw 0
          (S.α ((ordinaryHomologyTensorEquiv R A C Z ez hdz hzz 0).symm
            ((quotientHomologyEquiv R Z 0).symm (Algebraic.homologyClass Z 0 z) ⊗ₜ[R] a)))) =
          Algebraic.homologyClass W 0 z' :=
  ordinaryUCTAlpha_formula R A C D e he W ew hdw hzw Z ez hdz hzz 0 S.α S.α_formula z a

lemma ordinaryUCTPositiveAlpha_formula (n : ℕ)
    (P : P103.Specs.Ch10.Comparison.ProjectiveChoice Rᵐᵒᵖ
      (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R C) n)))
    (S : PositiveSequence (oppositeComplex R C) (ModuleCat.of R A) n P)
    (z : Algebraic.cycles Z (n+1 : ℕ)) (a : A) :
    ∃ z' : Algebraic.cycles W (n+1 : ℕ),
      ew (n+1) z'.val = e (n+1) (ez (n+1) z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R W (n+1 : ℕ)
        (ordinaryBalancedHomologyComparison R A C D e he W ew hdw hzw (n+1)
          (S.α ((ordinaryHomologyTensorEquiv R A C Z ez hdz hzz (n+1)).symm
            ((quotientHomologyEquiv R Z (n+1 : ℕ)).symm
              (Algebraic.homologyClass Z (n+1 : ℕ) z) ⊗ₜ[R] a)))) =
          Algebraic.homologyClass W (n+1 : ℕ) z' :=
  ordinaryUCTAlpha_formula R A C D e he W ew hdw hzw Z ez hdz hzz (n+1) S.α S.α_formula z a

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v t s
open P202Specs.UniversalCoefficientsHomology
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison
variable (R : Type u) [CommRing R]

/-- Comparison of the first UCT term with a specified actual homology family. -/
def topologicalPositiveLeftEquiv (A : ModuleCat.{v} R)
    (C : ChainComplex (ModuleCat.{t} R) ℕ) (H : ℕ → ModuleCat.{t} R)
    (hbase : ∀ k, C.homology k ≃ₗ[R] H k) (k : ℕ) :
    P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R C) k) A ≃+
      (H k ⊗[R] A) :=
  (homologyTensorEquiv R A C k).trans
    (TensorProduct.congr (hbase k) (LinearEquiv.refl R A)).toAddEquiv

/-- Comparison of the coefficient homology with its actual target family. -/
def topologicalPositiveMiddleEquiv (A : ModuleCat.{v} R)
    (C : ChainComplex (ModuleCat.{t} R) ℕ)
    (D : ChainComplex (ModuleCat.{s} R) ℕ)
    (e : ∀ k, (C.X k ⊗[R] A) ≃ₗ[R] D.X k)
    (B : BalancedHomologyData R A C D e) (K : ℕ → ModuleCat.{s} R)
    (hcoef : ∀ k, D.homology k ≃ₗ[R] K k) (k : ℕ) :
    Algebraic.Homology
      (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A) k ≃+ K k :=
  (B.equiv k).trans (hcoef k).toAddEquiv

/-- The genuine right-module identification used to transport Tor. -/
def topologicalPositiveRightEquiv
    (C : ChainComplex (ModuleCat.{t} R) ℕ) (H : ℕ → ModuleCat.{t} R)
    (hbase : ∀ k, C.homology k ≃ₗ[R] H k) (k : ℕ) :
    Algebraic.Homology (oppositeComplex R C) k ≃ₗ[Rᵐᵒᵖ]
      (oppositeFunctor R).obj (H k) :=
  (oppositeHomologyEquiv R C k).trans
    (((oppositeFunctor R).mapIso (hbase k).toModuleIso).toLinearEquiv)

/-- Positive UCT on the specified actual homology families. Both arrows and
the linear section are transported from the algebraic theorem. -/
def topologicalPositiveSequence
    (U : UniversalCoefficients.{u,t,v} R)
    (C : ChainComplex (ModuleCat.{t} R) ℕ)
    (hC : FlatTermsAndBoundaries.{u,t,v} (oppositeComplex R C))
    (A : ModuleCat.{v} R)
    (D : ChainComplex (ModuleCat.{s} R) ℕ)
    (e : ∀ k, (C.X k ⊗[R] A) ≃ₗ[R] D.X k)
    (B : BalancedHomologyData R A C D e)
    (hs : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R C) hC)
    (H : ℕ → ModuleCat.{t} R) (K : ℕ → ModuleCat.{s} R)
    (hbase : ∀ k, C.homology k ≃ₗ[R] H k)
    (hcoef : ∀ k, D.homology k ≃ₗ[R] K k)
    (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (H n)))
    (T : TorMaps.{u,t,v} R 1) :
    letI := torModule T Q A
    SplitExactSequence R (H (n+1) ⊗[R] A) (K (n+1)) (TorWith Q.val A 1) := by
  let P := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R C) n))
  letI := torModule T P A
  letI := torModule T Q A
  let eTor := torLinearEquiv R 1 T P Q (topologicalPositiveRightEquiv R C H hbase n) A
  apply positiveLinearSequence R U (oppositeComplex R C) hC A n P T hs
    (topologicalPositiveLeftEquiv R A C H hbase (n+1))
    (topologicalPositiveMiddleEquiv R A C D e B K hcoef (n+1)) eTor.toAddEquiv
  · intro r x
    change (TensorProduct.congr (hbase (n+1)) (LinearEquiv.refl R A))
      (homologyTensorEquiv R A C (n+1)
        (tensorMap LinearMap.id (r • (LinearMap.id : A →ₗ[R] A)) x)) =
      r • (TensorProduct.congr (hbase (n+1)) (LinearEquiv.refl R A))
        (homologyTensorEquiv R A C (n+1) x)
    rw [homologyTensorEquiv_scalar, map_smul]
  · intro r x
    change hcoef (n+1) (B.equiv (n+1)
      (Algebraic.homologyMap (tensorSecondMap (oppositeComplex R C) (r • (LinearMap.id : A →ₗ[R] A)))
        (n+1) x)) = r • hcoef (n+1) (B.equiv (n+1) x)
    rw [B.scalar, map_smul]
  · intro r x
    exact eTor.map_smul r x


section Formula
variable (U : UniversalCoefficients.{u,t,v} R)
    (C : ChainComplex (ModuleCat.{t} R) ℕ)
    (hC : FlatTermsAndBoundaries.{u,t,v} (oppositeComplex R C))
    (A : ModuleCat.{v} R)
    (D : ChainComplex (ModuleCat.{s} R) ℕ)
    (e : ∀ k, (C.X k ⊗[R] A) ≃ₗ[R] D.X k)
    (B : BalancedHomologyData R A C D e)
    (hs : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R C) hC)
    (H : ℕ → ModuleCat.{t} R) (K : ℕ → ModuleCat.{s} R)
    (hbase : ∀ k, C.homology k ≃ₗ[R] H k)
    (hcoef : ∀ k, D.homology k ≃ₗ[R] K k)
    (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (H n)))
    (T : TorMaps.{u,t,v} R 1)

@[simp] theorem topologicalPositiveSequence_α (x : H (n+1) ⊗[R] A) :
    let P := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
      (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R C) n))
    letI := torModule T Q A
    (topologicalPositiveSequence R U C hC A D e B hs H K hbase hcoef n Q T).α x =
      topologicalPositiveMiddleEquiv R A C D e B K hcoef (n+1)
        ((U.positive (oppositeComplex R C) hC A n P).α
          ((topologicalPositiveLeftEquiv R A C H hbase (n+1)).symm x)) := rfl

@[simp] theorem topologicalPositiveSequence_β (x : K (n+1)) :
    let P := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
      (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R C) n))
    letI := torModule T P A
    letI := torModule T Q A
    (topologicalPositiveSequence R U C hC A D e B hs H K hbase hcoef n Q T).β x =
      torLinearEquiv R 1 T P Q (topologicalPositiveRightEquiv R C H hbase n) A
        ((U.positive (oppositeComplex R C) hC A n P).β
          ((topologicalPositiveMiddleEquiv R A C D e B K hcoef (n+1)).symm x)) := rfl
end Formula

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v w
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.UniversalCoefficientsHomology
variable (R : Type u) [CommRing R]
variable (A : Type v) [AddCommGroup A] [Module R A]

def absoluteBaseHomologyEquiv (X : TopCat.{w}) (n : ℕ) :
    (complex R R X).homology n ≃ₗ[R] (ordinaryComplex R R X).homology (n : ℤ) :=
  (nonnegativeHomologyEquiv R (complex R R X) (ordinaryComplex R R X)
    (fun k => (ordinaryNonnegativeIso R R X k).toLinearEquiv)
    (absoluteDegree_boundary R R X) (P202.SingularChains.ordinary_boundary_zero R R X (-1)) n).symm

def relativeBaseHomologyEquiv (P : Pair.{w}) (n : ℕ) :
    (nonnegative R R P).homology n ≃ₗ[R] (ordinary R R P).homology (n : ℤ) :=
  (nonnegativeHomologyEquiv R (nonnegative R R P) (ordinary R R P)
    (fun k => (ordinaryDegreeIso R R P k).toLinearEquiv)
    (relativeDegree_boundary R R P) (relativeDegree_zero R R P) n).symm

def absoluteOppositeHomologyEquiv (X : TopCat.{w}) (n : ℕ) :
    Algebraic.Homology (oppositeComplex R (complex R R X)) n ≃ₗ[Rᵐᵒᵖ]
      (oppositeFunctor R).obj ((ordinaryComplex R R X).homology (n : ℤ)) :=
  ordinaryOppositeHomologyEquiv R (complex R R X) (ordinaryComplex R R X)
    (fun k => (ordinaryNonnegativeIso R R X k).toLinearEquiv)
    (absoluteDegree_boundary R R X) (P202.SingularChains.ordinary_boundary_zero R R X (-1)) n

def relativeOppositeHomologyEquiv (P : Pair.{w}) (n : ℕ) :
    Algebraic.Homology (oppositeComplex R (nonnegative R R P)) n ≃ₗ[Rᵐᵒᵖ]
      (oppositeFunctor R).obj ((ordinary R R P).homology (n : ℤ)) :=
  ordinaryOppositeHomologyEquiv R (nonnegative R R P) (ordinary R R P)
    (fun k => (ordinaryDegreeIso R R P k).toLinearEquiv)
    (relativeDegree_boundary R R P) (relativeDegree_zero R R P) n

def absoluteHomologyTensorEquiv (X : TopCat.{w}) (n : ℕ) :
    P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R (complex R R X)) n) A ≃+
      ((ordinaryComplex R R X).homology (n : ℤ) ⊗[R] A) :=
  ordinaryHomologyTensorEquiv R A (complex R R X) (ordinaryComplex R R X)
    (fun k => (ordinaryNonnegativeIso R R X k).toLinearEquiv)
    (absoluteDegree_boundary R R X) (P202.SingularChains.ordinary_boundary_zero R R X (-1)) n

def relativeHomologyTensorEquiv (P : Pair.{w}) (n : ℕ) :
    P103.BalancedTensor.Tensor R (Algebraic.Homology (oppositeComplex R (nonnegative R R P)) n) A ≃+
      ((ordinary R R P).homology (n : ℤ) ⊗[R] A) :=
  ordinaryHomologyTensorEquiv R A (nonnegative R R P) (ordinary R R P)
    (fun k => (ordinaryDegreeIso R R P k).toLinearEquiv)
    (relativeDegree_boundary R R P) (relativeDegree_zero R R P) n

lemma absoluteOppositeHomologyEquiv_natural {X Y : TopCat.{w}} (f : X ⟶ Y)
    (n : ℕ) (x : Algebraic.Homology (oppositeComplex R (complex R R X)) n) :
    absoluteOppositeHomologyEquiv R Y n
      (Algebraic.homologyMap
        (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (chainMap R R f)) n x) =
      HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n : ℤ)
        (absoluteOppositeHomologyEquiv R X n x) := by
  apply ordinaryOppositeHomologyEquiv_natural
  intro k x
  exact congrArg (fun φ => φ x) (absoluteDegree_natural R R f k)

lemma relativeOppositeHomologyEquiv_natural {P Q : Pair.{w}} (f : P ⟶ Q)
    (n : ℕ) (x : Algebraic.Homology (oppositeComplex R (nonnegative R R P)) n) :
    relativeOppositeHomologyEquiv R Q n
      (Algebraic.homologyMap
        (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (relativeMap (chainFunctor R R) f)) n x) =
      HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) (n : ℤ)
        (relativeOppositeHomologyEquiv R P n x) := by
  apply ordinaryOppositeHomologyEquiv_natural
  intro k x
  exact congrArg (fun φ => φ x) (relativeDegree_natural R R f k)

lemma absoluteHomologyTensorEquiv_natural {B : Type v} [AddCommGroup B] [Module R B]
    {X Y : TopCat.{w}} (f : X ⟶ Y) (g : A →ₗ[R] B) (n : ℕ)
    (x : P103.BalancedTensor.Tensor R
      (Algebraic.Homology (oppositeComplex R (complex R R X)) n) A) :
    absoluteHomologyTensorEquiv R B Y n
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap
        (Algebraic.homologyMap
          (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (chainMap R R f)) n) g x) =
      TensorProduct.map (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n : ℤ)).hom g
        (absoluteHomologyTensorEquiv R A X n x) := by
  apply ordinaryHomologyTensorEquiv_natural
  intro k x
  exact congrArg (fun φ => φ x) (absoluteDegree_natural R R f k)

lemma relativeHomologyTensorEquiv_natural {B : Type v} [AddCommGroup B] [Module R B]
    {P Q : Pair.{w}} (f : P ⟶ Q) (g : A →ₗ[R] B) (n : ℕ)
    (x : P103.BalancedTensor.Tensor R
      (Algebraic.Homology (oppositeComplex R (nonnegative R R P)) n) A) :
    relativeHomologyTensorEquiv R B Q n
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap
        (Algebraic.homologyMap
          (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (relativeMap (chainFunctor R R) f)) n) g x) =
      TensorProduct.map
        (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) (n : ℤ)).hom g
        (relativeHomologyTensorEquiv R A P n x) := by
  apply ordinaryHomologyTensorEquiv_natural
  intro k x
  exact congrArg (fun φ => φ x) (relativeDegree_natural R R f k)

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v w t s
open P202Specs.UniversalCoefficientsHomology
variable (R : Type u) [CommRing R]
section Generic
variable {A B : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (C C' : ChainComplex (ModuleCat.{t} R) ℕ)
  (D D' : ChainComplex (ModuleCat.{s} R) ℕ)
  (e : ∀ n, (C.X n ⊗[R] A) ≃ₗ[R] D.X n)
  (e' : ∀ n, (C'.X n ⊗[R] B) ≃ₗ[R] D'.X n)
  (he : ∀ i j x, e j ((C.d i j).hom.rTensor A x) = D.d i j (e i x))
  (he' : ∀ i j x, e' j ((C'.d i j).hom.rTensor B x) = D'.d i j (e' i x))
  (W W' : ChainComplex (ModuleCat.{s} R) ℤ)
  (ew : ∀ n : ℕ, W.X (n : ℤ) ≃ₗ[R] D.X n)
  (ew' : ∀ n : ℕ, W'.X (n : ℤ) ≃ₗ[R] D'.X n)
  (hdw : ∀ (n : ℕ) (x : W.X (n+1 : ℕ)),
    ew n (W.d (n+1 : ℕ) n x) = D.d (n+1) n (ew (n+1) x))
  (hdw' : ∀ (n : ℕ) (x : W'.X (n+1 : ℕ)),
    ew' n (W'.d (n+1 : ℕ) n x) = D'.d (n+1) n (ew' (n+1) x))
  (hzw : W.d 0 (-1) = 0) (hzw' : W'.d 0 (-1) = 0)
  (f : C ⟶ C') (g : A →ₗ[R] B) (k : D ⟶ D') (K : W ⟶ W')
  (h : ∀ n x, e' n (TensorProduct.map (f.f n).hom g x) = k.f n (e n x))
  (hK : ∀ (n : ℕ) (x : W.X (n : ℤ)), ew' n (K.f n x) = k.f n (ew n x))

include h hK in
lemma ordinaryBalancedHomologyComparison_natural (n : ℕ) (x : Algebraic.Homology
    (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R C) A) n) :
    ordinaryBalancedHomologyComparison R B C' D' e' he' W' ew' hdw' hzw' n
      (Algebraic.homologyMap
        (P103.Specs.Ch11.ExtTorDefinitions.tensorFirstMap
          (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map f) A ≫
          P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R C') g) n x) =
      HomologicalComplex.homologyMap K (n : ℤ)
        (ordinaryBalancedHomologyComparison R A C D e he W ew hdw hzw n x) := by
  change (nonnegativeHomologyEquiv R D' W' ew' hdw' hzw' n).symm
      (balancedHomologyComparison R B C' D' e' he' n _) =
    HomologicalComplex.homologyMap K (n : ℤ)
      ((nonnegativeHomologyEquiv R D W ew hdw hzw n).symm
        (balancedHomologyComparison R A C D e he n x))
  apply (nonnegativeHomologyEquiv R D' W' ew' hdw' hzw' n).injective
  rw [LinearEquiv.apply_symm_apply, nonnegativeHomologyEquiv_natural
    R D D' W W' ew ew' hdw hdw' hzw hzw' K k hK, LinearEquiv.apply_symm_apply]
  exact balancedHomologyComparison_natural R C C' D D' e e' he he' f g k h n x
end Generic

open P202Specs.SingularChains P202Specs.RelativeSingularChains
variable (A : Type v) [AddCommGroup A] [Module R A]

lemma absoluteTensorEquiv_d (X : TopCat.{w}) (i j : ℕ)
    (x : (complex R R X).X i ⊗[R] A) :
    tensorEquiv R A X j (((complex R R X).d i j).hom.rTensor A x) =
      (complex R A X).d i j (tensorEquiv R A X i x) := by
  by_cases h : j+1 = i
  · subst i
    exact P202.SingularChains.tensorEquiv_boundary R A X j x
  · rw [(complex R R X).shape i j h, (complex R A X).shape i j h]
    simp

lemma relativeTensorEquiv_d (P : Pair.{w}) (i j : ℕ)
    (x : (nonnegative R R P).X i ⊗[R] A) :
    relativeTensorEquiv R A P j (((nonnegative R R P).d i j).hom.rTensor A x) =
      (nonnegative R A P).d i j (relativeTensorEquiv R A P i x) := by
  by_cases h : j+1 = i
  · subst i
    exact relativeTensorEquiv_boundary R A P j x
  · rw [(nonnegative R R P).shape i j h, (nonnegative R A P).shape i j h]
    simp

/-- Canonical representative and scalar-compatible balanced homology comparison. -/
def canonicalBalancedHomologyData
    (C : ChainComplex (ModuleCat.{t} R) ℕ)
    (D : ChainComplex (ModuleCat.{s} R) ℕ)
    (e : ∀ n, (C.X n ⊗[R] A) ≃ₗ[R] D.X n)
    (he : ∀ i j x, e j ((C.d i j).hom.rTensor A x) = D.d i j (e i x)) :
    BalancedHomologyData R A C D e where
  equiv := balancedHomologyComparison R A C D e he
  formula n z := ⟨balancedCyclesComparison R A C D e he n z, rfl,
    balancedHomologyComparison_formula R A C D e he n z⟩
  scalar := balancedHomologyComparison_scalar R A C D e he

def absoluteBalancedHomologyData (X : TopCat.{w}) :
    BalancedHomologyData R A (complex R R X) (complex R A X) (tensorEquiv R A X) :=
  canonicalBalancedHomologyData R A (complex R R X) (complex R A X)
    (tensorEquiv R A X) (absoluteTensorEquiv_d R A X)

def relativeBalancedHomologyData (P : Pair.{w}) :
    BalancedHomologyData R A (nonnegative R R P) (nonnegative R A P) (relativeTensorEquiv R A P) :=
  canonicalBalancedHomologyData R A (nonnegative R R P) (nonnegative R A P)
    (relativeTensorEquiv R A P) (relativeTensorEquiv_d R A P)

/-- Canonical comparison to absolute ordinary homology with the original scalars. -/
def absoluteOrdinaryHomologyComparison (X : TopCat.{w}) (n : ℕ) :
    Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex
      (oppositeComplex R (complex R R X)) A) n ≃+ (ordinaryComplex R A X).homology (n : ℤ) :=
  ordinaryBalancedHomologyComparison R A (complex R R X) (complex R A X)
    (tensorEquiv R A X) (absoluteTensorEquiv_d R A X) (ordinaryComplex R A X)
    (fun n => (ordinaryNonnegativeIso R A X n).toLinearEquiv)
    (absoluteDegree_boundary R A X) (P202.SingularChains.ordinary_boundary_zero R A X (-1)) n

/-- Canonical comparison to relative ordinary homology with the original scalars. -/
def relativeOrdinaryHomologyComparison (P : Pair.{w}) (n : ℕ) :
    Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex
      (oppositeComplex R (nonnegative R R P)) A) n ≃+ (ordinary R A P).homology (n : ℤ) :=
  ordinaryBalancedHomologyComparison R A (nonnegative R R P) (nonnegative R A P)
    (relativeTensorEquiv R A P) (relativeTensorEquiv_d R A P) (ordinary R A P)
    (fun n => (ordinaryDegreeIso R A P n).toLinearEquiv)
    (relativeDegree_boundary R A P) (relativeDegree_zero R A P) n

lemma absoluteOrdinaryHomologyComparison_scalar (X : TopCat.{w}) (n : ℕ) (r : R)
    (x : Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex
      (oppositeComplex R (complex R R X)) A) n) :
    absoluteOrdinaryHomologyComparison R A X n
      (Algebraic.homologyMap
        (P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R (complex R R X))
          (r • (LinearMap.id : A →ₗ[R] A))) n x) =
      r • absoluteOrdinaryHomologyComparison R A X n x :=
  ordinaryBalancedHomologyComparison_scalar R A (complex R R X) (complex R A X)
    (tensorEquiv R A X) (absoluteTensorEquiv_d R A X) (ordinaryComplex R A X)
    (fun n => (ordinaryNonnegativeIso R A X n).toLinearEquiv)
    (absoluteDegree_boundary R A X) (P202.SingularChains.ordinary_boundary_zero R A X (-1)) n r x

lemma relativeOrdinaryHomologyComparison_scalar (P : Pair.{w}) (n : ℕ) (r : R)
    (x : Algebraic.Homology (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex
      (oppositeComplex R (nonnegative R R P)) A) n) :
    relativeOrdinaryHomologyComparison R A P n
      (Algebraic.homologyMap
        (P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R (nonnegative R R P))
          (r • (LinearMap.id : A →ₗ[R] A))) n x) =
      r • relativeOrdinaryHomologyComparison R A P n x :=
  ordinaryBalancedHomologyComparison_scalar R A (nonnegative R R P) (nonnegative R A P)
    (relativeTensorEquiv R A P) (relativeTensorEquiv_d R A P) (ordinary R A P)
    (fun n => (ordinaryDegreeIso R A P n).toLinearEquiv)
    (relativeDegree_boundary R A P) (relativeDegree_zero R A P) n r x

variable {B : Type v} [AddCommGroup B] [Module R B]
lemma absoluteOrdinaryHomologyComparison_natural (g : A →ₗ[R] B) {X Y : TopCat.{w}}
    (f : X ⟶ Y) (n : ℕ) (x : Algebraic.Homology
      (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R (complex R R X)) A) n) :
    absoluteOrdinaryHomologyComparison R B Y n
      (Algebraic.homologyMap
        (P103.Specs.Ch11.ExtTorDefinitions.tensorFirstMap
          (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map (chainMap R R f)) A ≫
          P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R (complex R R Y)) g) n x) =
      HomologicalComplex.homologyMap
        ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g Y) (n : ℤ)
        (absoluteOrdinaryHomologyComparison R A X n x) := by
  apply ordinaryBalancedHomologyComparison_natural R
    (complex R R X) (complex R R Y) (complex R A X) (complex R B Y)
    (tensorEquiv R A X) (tensorEquiv R B Y)
    (absoluteTensorEquiv_d R A X) (absoluteTensorEquiv_d R B Y)
    (ordinaryComplex R A X) (ordinaryComplex R B Y)
    (fun n => (ordinaryNonnegativeIso R A X n).toLinearEquiv)
    (fun n => (ordinaryNonnegativeIso R B Y n).toLinearEquiv)
    (absoluteDegree_boundary R A X) (absoluteDegree_boundary R B Y)
    (P202.SingularChains.ordinary_boundary_zero R A X (-1))
    (P202.SingularChains.ordinary_boundary_zero R B Y (-1))
    (chainMap R R f) g (chainMap R A f ≫ coefficientMap R A g Y)
    ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g Y)
    (absoluteTensorEquiv_mixed R A g f)
  intro n x
  exact congrArg (fun φ => φ x) (absoluteDegree_mixed R A g f n)

lemma relativeOrdinaryHomologyComparison_natural (g : A →ₗ[R] B) {P Q : Pair.{w}}
    (f : P ⟶ Q) (n : ℕ) (x : Algebraic.Homology
      (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (oppositeComplex R (nonnegative R R P)) A) n) :
    relativeOrdinaryHomologyComparison R B Q n
      (Algebraic.homologyMap
        (P103.Specs.Ch11.ExtTorDefinitions.tensorFirstMap
          (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (relativeMap (chainFunctor R R) f)) A ≫
          P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (oppositeComplex R (nonnegative R R Q)) g) n x) =
      HomologicalComplex.homologyMap
        (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g Q) (n : ℤ)
        (relativeOrdinaryHomologyComparison R A P n x) := by
  apply ordinaryBalancedHomologyComparison_natural R
    (nonnegative R R P) (nonnegative R R Q) (nonnegative R A P) (nonnegative R B Q)
    (relativeTensorEquiv R A P) (relativeTensorEquiv R B Q)
    (relativeTensorEquiv_d R A P) (relativeTensorEquiv_d R B Q)
    (ordinary R A P) (ordinary R B Q)
    (fun n => (ordinaryDegreeIso R A P n).toLinearEquiv)
    (fun n => (ordinaryDegreeIso R B Q n).toLinearEquiv)
    (relativeDegree_boundary R A P) (relativeDegree_boundary R B Q)
    (relativeDegree_zero R A P) (relativeDegree_zero R B Q)
    (relativeMap (chainFunctor R R) f) g
    (relativeMap (chainFunctor R A) f ≫ relativeCoefficientMap R A g Q)
    (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g Q)
    (relativeTensorEquiv_mixed R A g f)
  intro n x
  exact congrArg (fun φ => φ x) (relativeDegree_mixed R A g f n)
end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v t
open P202Specs.UniversalCoefficientsHomology
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison
variable (R : Type u) [CommRing R]
variable (U : UniversalCoefficients.{u,t,v} R)
  (C D : Complex.{u,t} R)
  (hC : FlatTermsAndBoundaries.{u,t,v} C) (hD : FlatTermsAndBoundaries.{u,t,v} D)
  (A A' : ModuleCat.{v} R) (f : C ⟶ D) (g : A ⟶ A') (n : ℕ)
  (P : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology C n)))
  (P' : ProjectiveChoice Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology D n)))
  (T : TorMaps.{u,t,v} R 1)
  (hs : AlgebraicUCT.ScalarSplittings R U C hC)
  (hs' : AlgebraicUCT.ScalarSplittings R U D hD)
  {L M N L' M' N' : Type*}
  [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup L'] [AddCommGroup M'] [AddCommGroup N']
  [Module R L] [Module R M] [Module R N]
  [Module R L'] [Module R M'] [Module R N']
  (eL : P103.BalancedTensor.Tensor R (Algebraic.Homology C (n+1)) A ≃+ L)
  (eM : Algebraic.Homology (tensorComplex C A) (n+1) ≃+ M)
  (eN : TorWith P.val A 1 ≃+ N)
  (eL' : P103.BalancedTensor.Tensor R (Algebraic.Homology D (n+1)) A' ≃+ L')
  (eM' : Algebraic.Homology (tensorComplex D A') (n+1) ≃+ M')
  (eN' : TorWith P'.val A' 1 ≃+ N')
  (hL : ∀ r x, eL (tensorMap LinearMap.id (scalarMap A r).hom x) = r • eL x)
  (hM : ∀ r x, eM (Algebraic.homologyMap (tensorSecondMap C (scalarMap A r).hom) (n+1) x) = r • eM x)
  (hN : ∀ r x, eN (T.map P P (𝟙 _) (scalarMap A r) x) = r • eN x)
  (hL' : ∀ r x, eL' (tensorMap LinearMap.id (scalarMap A' r).hom x) = r • eL' x)
  (hM' : ∀ r x, eM' (Algebraic.homologyMap (tensorSecondMap D (scalarMap A' r).hom) (n+1) x) = r • eM' x)
  (hN' : ∀ r x, eN' (T.map P' P' (𝟙 _) (scalarMap A' r) x) = r • eN' x)

/-- Simultaneous naturality survives the scalar-compatible transport of both
arrows, for arbitrary chosen comparisons satisfying their naturality squares. -/
theorem positiveLinearSequence_natural
    (F : L → L') (G : M → M') (H : N → N')
    (hFn : ∀ x, eL' (tensorMap (Algebraic.homologyMap f (n+1)) g.hom x) = F (eL x))
    (hGn : ∀ x, eM' (Algebraic.homologyMap
      (tensorFirstMap f A ≫ tensorSecondMap D g.hom) (n+1) x) = G (eM x))
    (hHn : ∀ x, eN' (T.map P P' (ModuleCat.ofHom (Algebraic.homologyMap f n)) g x) = H (eN x)) :
    (∀ x, G ((positiveLinearSequence R U C hC A n P T hs eL eM eN hL hM hN).α x) =
      (positiveLinearSequence R U D hD A' n P' T hs' eL' eM' eN' hL' hM' hN').α (F x)) ∧
    (∀ x, H ((positiveLinearSequence R U C hC A n P T hs eL eM eN hL hM hN).β x) =
      (positiveLinearSequence R U D hD A' n P' T hs' eL' eM' eN' hL' hM' hN').β (G x)) := by
  have hnat := U.natural_positive C D hC hD f A A' g n P P' T
  constructor
  · intro x
    change G (eM ((U.positive C hC A n P).α (eL.symm x))) =
      eM' ((U.positive D hD A' n P').α (eL'.symm (F x)))
    apply conjugate_natural _ _ _ _ eL eM eL' eM' F G _ hFn hGn x
    intro z
    exact LinearMap.congr_fun hnat.1 z
  · intro x
    change H (eN ((U.positive C hC A n P).β (eM.symm x))) =
      eN' ((U.positive D hD A' n P').β (eM'.symm (G x)))
    apply conjugate_natural _ _ _ _ eM eN eM' eN' G H _ hGn hHn x
    intro z
    exact LinearMap.congr_fun hnat.2 z

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v w
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.UniversalCoefficientsHomology
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison
variable (R : Type u) [CommRing R]

def absoluteCoefficientHomologyEquiv (A : ModuleCat.{v} R) (X : TopCat.{w}) (n : ℕ) :
    (complex R A X).homology n ≃ₗ[R] (ordinaryComplex R A X).homology (n : ℤ) :=
  (nonnegativeHomologyEquiv R (complex R A X) (ordinaryComplex R A X)
    (fun k => (ordinaryNonnegativeIso R A X k).toLinearEquiv)
    (absoluteDegree_boundary R A X) (P202.SingularChains.ordinary_boundary_zero R A X (-1)) n).symm

def relativeCoefficientHomologyEquiv (A : ModuleCat.{v} R) (P : Pair.{w}) (n : ℕ) :
    (nonnegative R A P).homology n ≃ₗ[R] (ordinary R A P).homology (n : ℤ) :=
  (nonnegativeHomologyEquiv R (nonnegative R A P) (ordinary R A P)
    (fun k => (ordinaryDegreeIso R A P k).toLinearEquiv)
    (relativeDegree_boundary R A P) (relativeDegree_zero R A P) n).symm

def absolutePositiveSequence (U : UniversalCoefficients.{u,max u w,v} R) (X : TopCat.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (complex R R X)))
    (hs : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (complex R R X)) h)
    (A : ModuleCat.{v} R) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ
      ((oppositeFunctor R).obj ((ordinaryComplex R R X).homology (n : ℤ))))
    (T : TorMaps.{u,max u w,v} R 1) :
    letI := torModule T Q A
    SplitExactSequence R ((ordinaryComplex R R X).homology (n+1 : ℕ) ⊗[R] A)
      ((ordinaryComplex R A X).homology (n+1 : ℕ)) (TorWith Q.val A 1) :=
  topologicalPositiveSequence R U (complex R R X) h A (complex R A X)
    (tensorEquiv R A X) (absoluteBalancedHomologyData R A X) hs
    (fun k => (ordinaryComplex R R X).homology (k : ℤ))
    (fun k => (ordinaryComplex R A X).homology (k : ℤ))
    (absoluteBaseHomologyEquiv R X) (absoluteCoefficientHomologyEquiv R A X) n Q T

def relativePositiveSequence (U : UniversalCoefficients.{u,max u w,v} R) (P : Pair.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (nonnegative R R P)))
    (hs : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (nonnegative R R P)) h)
    (A : ModuleCat.{v} R) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ
      ((oppositeFunctor R).obj ((ordinary R R P).homology (n : ℤ))))
    (T : TorMaps.{u,max u w,v} R 1) :
    letI := torModule T Q A
    SplitExactSequence R ((ordinary R R P).homology (n+1 : ℕ) ⊗[R] A)
      ((ordinary R A P).homology (n+1 : ℕ)) (TorWith Q.val A 1) :=
  topologicalPositiveSequence R U (nonnegative R R P) h A (nonnegative R A P)
    (relativeTensorEquiv R A P) (relativeBalancedHomologyData R A P) hs
    (fun k => (ordinary R R P).homology (k : ℤ))
    (fun k => (ordinary R A P).homology (k : ℤ))
    (relativeBaseHomologyEquiv R P) (relativeCoefficientHomologyEquiv R A P) n Q T

section AbsoluteFormula
variable (U : UniversalCoefficients.{u,max u w,v} R) (X : TopCat.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (complex R R X)))
    (hs : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (complex R R X)) h)
    (A : ModuleCat.{v} R) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ
      ((oppositeFunctor R).obj ((ordinaryComplex R R X).homology (n : ℤ))))
    (T : TorMaps.{u,max u w,v} R 1)

@[simp] theorem absolutePositiveSequence_α
    (x : (ordinaryComplex R R X).homology (n+1 : ℕ) ⊗[R] A) :
    let P := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
      (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (complex R R X)) n))
    letI := torModule T Q A
    (absolutePositiveSequence R U X h hs A n Q T).α x =
      absoluteOrdinaryHomologyComparison R A X (n+1)
        ((U.positive (oppositeComplex R (complex R R X)) h A n P).α
          ((absoluteHomologyTensorEquiv R A X (n+1)).symm x)) := rfl

@[simp] theorem absolutePositiveSequence_β
    (x : (ordinaryComplex R A X).homology (n+1 : ℕ)) :
    let P := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
      (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (complex R R X)) n))
    letI := torModule T P A
    letI := torModule T Q A
    (absolutePositiveSequence R U X h hs A n Q T).β x =
      torLinearEquiv R 1 T P Q (absoluteOppositeHomologyEquiv R X n) A
        ((U.positive (oppositeComplex R (complex R R X)) h A n P).β
          ((absoluteOrdinaryHomologyComparison R A X (n+1)).symm x)) := rfl
end AbsoluteFormula

section RelativeFormula
variable (U : UniversalCoefficients.{u,max u w,v} R) (P : Pair.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (nonnegative R R P)))
    (hs : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (nonnegative R R P)) h)
    (A : ModuleCat.{v} R) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ
      ((oppositeFunctor R).obj ((ordinary R R P).homology (n : ℤ))))
    (T : TorMaps.{u,max u w,v} R 1)

@[simp] theorem relativePositiveSequence_α
    (x : (ordinary R R P).homology (n+1 : ℕ) ⊗[R] A) :
    let Q' := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
      (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (nonnegative R R P)) n))
    letI := torModule T Q A
    (relativePositiveSequence R U P h hs A n Q T).α x =
      relativeOrdinaryHomologyComparison R A P (n+1)
        ((U.positive (oppositeComplex R (nonnegative R R P)) h A n Q').α
          ((relativeHomologyTensorEquiv R A P (n+1)).symm x)) := rfl

@[simp] theorem relativePositiveSequence_β
    (x : (ordinary R A P).homology (n+1 : ℕ)) :
    let Q' := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
      (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (nonnegative R R P)) n))
    letI := torModule T Q' A
    letI := torModule T Q A
    (relativePositiveSequence R U P h hs A n Q T).β x =
      torLinearEquiv R 1 T Q' Q (relativeOppositeHomologyEquiv R P n) A
        ((U.positive (oppositeComplex R (nonnegative R R P)) h A n Q').β
          ((relativeOrdinaryHomologyComparison R A P (n+1)).symm x)) := rfl
end RelativeFormula

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v w
open P202Specs.UniversalCoefficientsHomology P202Specs.SingularChains P202Specs.RelativeSingularChains
open P103.Specs.Ch11.UniversalCoefficientsHomology P103.Specs.Ch11.ExtTorDefinitions
variable (R : Type u) [CommRing R]
variable (U : UniversalCoefficients.{u,max u w,v} R)

def absoluteZeroIso (A : ModuleCat.{v} R) (X : TopCat.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (complex R R X))) :
    (homology R R X 0 ⊗[R] A) ≃ₗ[R] homology R A X 0 :=
  zeroLinearEquiv R U (oppositeComplex R (complex R R X)) h A
    (absoluteHomologyTensorEquiv R A X 0) (absoluteOrdinaryHomologyComparison R A X 0)
    (ordinaryHomologyTensorEquiv_scalar R A (complex R R X) (ordinaryComplex R R X)
      (fun n => (ordinaryNonnegativeIso R R X n).toLinearEquiv)
      (absoluteDegree_boundary R R X) (P202.SingularChains.ordinary_boundary_zero R R X (-1)) 0)
    (absoluteOrdinaryHomologyComparison_scalar R A X 0)

def relativeZeroIso (A : ModuleCat.{v} R) (P : Pair.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (nonnegative R R P))) :
    (relativeHomology R R P 0 ⊗[R] A) ≃ₗ[R] relativeHomology R A P 0 :=
  zeroLinearEquiv R U (oppositeComplex R (nonnegative R R P)) h A
    (relativeHomologyTensorEquiv R A P 0) (relativeOrdinaryHomologyComparison R A P 0)
    (ordinaryHomologyTensorEquiv_scalar R A (nonnegative R R P) (ordinary R R P)
      (fun n => (ordinaryDegreeIso R R P n).toLinearEquiv)
      (relativeDegree_boundary R R P) (relativeDegree_zero R R P) 0)
    (relativeOrdinaryHomologyComparison_scalar R A P 0)

lemma absoluteZeroIso_formula (A : ModuleCat.{v} R) (X : TopCat.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (complex R R X)))
    (z : Algebraic.cycles (ordinaryComplex R R X) 0) (a : A) :
    ∃ z' : Algebraic.cycles (ordinaryComplex R A X) 0,
      (ordinaryNonnegativeIso R A X 0).hom z'.val =
        tensorEquiv R A X 0 ((ordinaryNonnegativeIso R R X 0).hom z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R (ordinaryComplex R A X) 0
        (absoluteZeroIso R U A X h
          ((quotientHomologyEquiv R (ordinaryComplex R R X) 0).symm
            (Algebraic.homologyClass _ _ z) ⊗ₜ[R] a)) = Algebraic.homologyClass _ _ z' := by
  exact ordinaryUCTZeroAlpha_formula R A (complex R R X) (complex R A X)
    (tensorEquiv R A X) (absoluteTensorEquiv_d R A X) (ordinaryComplex R A X)
    (fun n => (ordinaryNonnegativeIso R A X n).toLinearEquiv)
    (absoluteDegree_boundary R A X) (P202.SingularChains.ordinary_boundary_zero R A X (-1))
    (ordinaryComplex R R X) (fun n => (ordinaryNonnegativeIso R R X n).toLinearEquiv)
    (absoluteDegree_boundary R R X) (P202.SingularChains.ordinary_boundary_zero R R X (-1))
    (U.zero _ h A) z a

lemma relativeZeroIso_formula (A : ModuleCat.{v} R) (P : Pair.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (nonnegative R R P)))
    (z : Algebraic.cycles (ordinary R R P) 0) (a : A) :
    ∃ z' : Algebraic.cycles (ordinary R A P) 0,
      (ordinaryDegreeIso R A P 0).hom z'.val =
        relativeTensorEquiv R A P 0 ((ordinaryDegreeIso R R P 0).hom z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R (ordinary R A P) 0
        (relativeZeroIso R U A P h
          ((quotientHomologyEquiv R (ordinary R R P) 0).symm
            (Algebraic.homologyClass _ _ z) ⊗ₜ[R] a)) = Algebraic.homologyClass _ _ z' := by
  exact ordinaryUCTZeroAlpha_formula R A (nonnegative R R P) (nonnegative R A P)
    (relativeTensorEquiv R A P) (relativeTensorEquiv_d R A P) (ordinary R A P)
    (fun n => (ordinaryDegreeIso R A P n).toLinearEquiv)
    (relativeDegree_boundary R A P) (relativeDegree_zero R A P)
    (ordinary R R P) (fun n => (ordinaryDegreeIso R R P n).toLinearEquiv)
    (relativeDegree_boundary R R P) (relativeDegree_zero R R P) (U.zero _ h A) z a

lemma absoluteZeroIso_natural (A B : ModuleCat.{v} R) {X Y : TopCat.{w}}
    (f : X ⟶ Y) (g : A ⟶ B)
    (hX : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (complex R R X)))
    (hY : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (complex R R Y)))
    (x : homology R R X 0 ⊗[R] A) :
    HomologicalComplex.homologyMap
      ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g.hom Y) 0
        (absoluteZeroIso R U A X hX x) =
      absoluteZeroIso R U B Y hY (TensorProduct.map
        (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) 0).hom g.hom x) := by
  change _ = absoluteOrdinaryHomologyComparison R B Y 0
    ((U.zero _ hY B).α ((absoluteHomologyTensorEquiv R B Y 0).symm _))
  apply conjugate_natural _ _ _ _
    (absoluteHomologyTensorEquiv R A X 0) (absoluteOrdinaryHomologyComparison R A X 0)
    (absoluteHomologyTensorEquiv R B Y 0) (absoluteOrdinaryHomologyComparison R B Y 0)
    _ _ _ (absoluteHomologyTensorEquiv_natural R A f g.hom 0)
    (absoluteOrdinaryHomologyComparison_natural R A g.hom f 0) x
  intro y
  exact LinearMap.congr_fun (U.natural_zero _ _ hX hY
    (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map (chainMap R R f))
    A B g) y

lemma relativeZeroIso_natural (A B : ModuleCat.{v} R) {P P' : Pair.{w}}
    (f : P ⟶ P') (g : A ⟶ B)
    (hP : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (nonnegative R R P)))
    (hP' : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (nonnegative R R P')))
    (x : relativeHomology R R P 0 ⊗[R] A) :
    HomologicalComplex.homologyMap
      (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g.hom P') 0
        (relativeZeroIso R U A P hP x) =
      relativeZeroIso R U B P' hP' (TensorProduct.map
        (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) 0).hom g.hom x) := by
  change _ = relativeOrdinaryHomologyComparison R B P' 0
    ((U.zero _ hP' B).α ((relativeHomologyTensorEquiv R B P' 0).symm _))
  apply conjugate_natural _ _ _ _
    (relativeHomologyTensorEquiv R A P 0) (relativeOrdinaryHomologyComparison R A P 0)
    (relativeHomologyTensorEquiv R B P' 0) (relativeOrdinaryHomologyComparison R B P' 0)
    _ _ _ (relativeHomologyTensorEquiv_natural R A f g.hom 0)
    (relativeOrdinaryHomologyComparison_natural R A g.hom f 0) x
  intro y
  exact LinearMap.congr_fun (U.natural_zero _ _ hP hP'
    (((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (relativeMap (chainFunctor R R) f)) A B g) y

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v w
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.UniversalCoefficientsHomology
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison
variable (R : Type u) [CommRing R]

lemma absolutePositiveSequence_formula (U : UniversalCoefficients.{u,max u w,v} R)
    (X : TopCat.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (complex R R X)))
    (hs : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (complex R R X)) h)
    (A : ModuleCat.{v} R) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (homology R R X n)))
    (T : TorMaps.{u,max u w,v} R 1)
    (z : Algebraic.cycles (ordinaryComplex R R X) (n+1 : ℕ)) (a : A) :
    letI := torModule T Q A
    ∃ z' : Algebraic.cycles (ordinaryComplex R A X) (n+1 : ℕ),
      (ordinaryNonnegativeIso R A X (n+1)).hom z'.val =
        tensorEquiv R A X (n+1) ((ordinaryNonnegativeIso R R X (n+1)).hom z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R (ordinaryComplex R A X) (n+1 : ℕ)
        ((absolutePositiveSequence R U X h hs A n Q T).α
          ((quotientHomologyEquiv R (ordinaryComplex R R X) (n+1 : ℕ)).symm
            (Algebraic.homologyClass _ _ z) ⊗ₜ[R] a)) = Algebraic.homologyClass _ _ z' := by
  letI := torModule T Q A
  rw [absolutePositiveSequence_α]
  let P := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (complex R R X)) n))
  exact ordinaryUCTPositiveAlpha_formula R A (complex R R X) (complex R A X)
    (tensorEquiv R A X) (absoluteTensorEquiv_d R A X) (ordinaryComplex R A X)
    (fun k => (ordinaryNonnegativeIso R A X k).toLinearEquiv)
    (absoluteDegree_boundary R A X) (P202.SingularChains.ordinary_boundary_zero R A X (-1))
    (ordinaryComplex R R X) (fun k => (ordinaryNonnegativeIso R R X k).toLinearEquiv)
    (absoluteDegree_boundary R R X) (P202.SingularChains.ordinary_boundary_zero R R X (-1))
    n P (U.positive (oppositeComplex R (complex R R X)) h A n P) z a

lemma relativePositiveSequence_formula (U : UniversalCoefficients.{u,max u w,v} R)
    (P : Pair.{w})
    (h : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (nonnegative R R P)))
    (hs : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (nonnegative R R P)) h)
    (A : ModuleCat.{v} R) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ ((oppositeFunctor R).obj (relativeHomology R R P n)))
    (T : TorMaps.{u,max u w,v} R 1)
    (z : Algebraic.cycles (ordinary R R P) (n+1 : ℕ)) (a : A) :
    letI := torModule T Q A
    ∃ z' : Algebraic.cycles (ordinary R A P) (n+1 : ℕ),
      (ordinaryDegreeIso R A P (n+1)).hom z'.val =
        relativeTensorEquiv R A P (n+1) ((ordinaryDegreeIso R R P (n+1)).hom z.val ⊗ₜ[R] a) ∧
      quotientHomologyEquiv R (ordinary R A P) (n+1 : ℕ)
        ((relativePositiveSequence R U P h hs A n Q T).α
          ((quotientHomologyEquiv R (ordinary R R P) (n+1 : ℕ)).symm
            (Algebraic.homologyClass _ _ z) ⊗ₜ[R] a)) = Algebraic.homologyClass _ _ z' := by
  letI := torModule T Q A
  rw [relativePositiveSequence_α]
  let Q' := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (nonnegative R R P)) n))
  exact ordinaryUCTPositiveAlpha_formula R A (nonnegative R R P) (nonnegative R A P)
    (relativeTensorEquiv R A P) (relativeTensorEquiv_d R A P) (ordinary R A P)
    (fun k => (ordinaryDegreeIso R A P k).toLinearEquiv)
    (relativeDegree_boundary R A P) (relativeDegree_zero R A P)
    (ordinary R R P) (fun k => (ordinaryDegreeIso R R P k).toLinearEquiv)
    (relativeDegree_boundary R R P) (relativeDegree_zero R R P)
    n Q' (U.positive (oppositeComplex R (nonnegative R R P)) h A n Q') z a

end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v w
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.UniversalCoefficientsHomology
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison
variable (R : Type u) [CommRing R]

/-- Both positive absolute UCT arrows are natural simultaneously in the
continuous map, coefficient map, and chosen Tor resolutions. -/
theorem absolutePositiveSequence_natural
    (U : UniversalCoefficients.{u,max u w,v} R) {X Y : TopCat.{w}}
    (hX : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (complex R R X)))
    (hY : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (complex R R Y)))
    (hsX : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (complex R R X)) hX)
    (hsY : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (complex R R Y)) hY)
    (A B : ModuleCat.{v} R) (f : X ⟶ Y) (g : A ⟶ B) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ
      ((oppositeFunctor R).obj ((ordinaryComplex R R X).homology (n : ℤ))))
    (Q' : ProjectiveChoice Rᵐᵒᵖ
      ((oppositeFunctor R).obj ((ordinaryComplex R R Y).homology (n : ℤ))))
    (T : TorMaps.{u,max u w,v} R 1) :
    letI := torModule T Q A
    letI := torModule T Q' B
    (∀ x, HomologicalComplex.homologyMap
        ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g.hom Y) (n+1 : ℕ)
        ((absolutePositiveSequence R U X hX hsX A n Q T).α x) =
      (absolutePositiveSequence R U Y hY hsY B n Q' T).α
        (TensorProduct.map
          (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n+1 : ℕ)).hom g.hom x)) ∧
    (∀ x, T.map Q Q'
        ((oppositeFunctor R).map (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n : ℤ))) g
        ((absolutePositiveSequence R U X hX hsX A n Q T).β x) =
      (absolutePositiveSequence R U Y hY hsY B n Q' T).β
        (HomologicalComplex.homologyMap
          ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g.hom Y) (n+1 : ℕ) x)) := by
  let PX := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (complex R R X)) n))
  let PY := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (complex R R Y)) n))
  let fc := ((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map (chainMap R R f)
  letI := torModule T PX A
  letI := torModule T PY B
  letI := torModule T Q A
  letI := torModule T Q' B
  let eTX := torLinearEquiv R 1 T PX Q (absoluteOppositeHomologyEquiv R X n) A
  let eTY := torLinearEquiv R 1 T PY Q' (absoluteOppositeHomologyEquiv R Y n) B
  have hnat := U.natural_positive _ _ hX hY fc A B g n PX PY T
  constructor
  · intro x
    change HomologicalComplex.homologyMap
        ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g.hom Y) (n+1 : ℕ)
        (absoluteOrdinaryHomologyComparison R A X (n+1)
          ((U.positive _ hX A n PX).α ((absoluteHomologyTensorEquiv R A X (n+1)).symm x))) =
      absoluteOrdinaryHomologyComparison R B Y (n+1)
        ((U.positive _ hY B n PY).α ((absoluteHomologyTensorEquiv R B Y (n+1)).symm
          (TensorProduct.map
            (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n+1 : ℕ)).hom g.hom x)))
    apply conjugate_natural _ _ _ _
      (absoluteHomologyTensorEquiv R A X (n+1)) (absoluteOrdinaryHomologyComparison R A X (n+1))
      (absoluteHomologyTensorEquiv R B Y (n+1)) (absoluteOrdinaryHomologyComparison R B Y (n+1)) _ _
      (fun z => LinearMap.congr_fun hnat.1 z)
      (absoluteHomologyTensorEquiv_natural R A f g.hom (n+1))
      (absoluteOrdinaryHomologyComparison_natural R A g.hom f (n+1)) x
  · intro x
    change T.map Q Q'
        ((oppositeFunctor R).map (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n : ℤ))) g
        (eTX ((U.positive _ hX A n PX).β ((absoluteOrdinaryHomologyComparison R A X (n+1)).symm x))) =
      eTY ((U.positive _ hY B n PY).β ((absoluteOrdinaryHomologyComparison R B Y (n+1)).symm
        (HomologicalComplex.homologyMap
          ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g.hom Y) (n+1 : ℕ) x)))
    apply conjugate_natural
      (U.positive _ hX A n PX).β (U.positive _ hY B n PY).β
      (Algebraic.homologyMap (tensorFirstMap fc A ≫ tensorSecondMap _ g.hom) (n+1))
      (T.map PX PY (ModuleCat.ofHom (Algebraic.homologyMap fc n)) g)
      (absoluteOrdinaryHomologyComparison R A X (n+1)) eTX.toAddEquiv
      (absoluteOrdinaryHomologyComparison R B Y (n+1)) eTY.toAddEquiv
      (HomologicalComplex.homologyMap
        ((ordinaryFunctor R A).map f ≫ ordinaryCoefficientMap R A g.hom Y) (n+1 : ℕ))
      (T.map Q Q'
        ((oppositeFunctor R).map (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n : ℤ))) g)
      (fun z => LinearMap.congr_fun hnat.2 z)
      (absoluteOrdinaryHomologyComparison_natural R A g.hom f (n+1)) _ x
    intro z
    symm
    apply torLinearEquiv_natural R 1 T PX Q PY Q'
      (absoluteOppositeHomologyEquiv R X n) (absoluteOppositeHomologyEquiv R Y n)
      (ModuleCat.ofHom (Algebraic.homologyMap fc n))
      ((oppositeFunctor R).map (HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n : ℤ))) g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (absoluteOppositeHomologyEquiv_natural R f n a).symm
/-- Both positive relative UCT arrows are natural simultaneously in the
map of pairs, coefficient map, and chosen Tor resolutions. -/
theorem relativePositiveSequence_natural
    (U : UniversalCoefficients.{u,max u w,v} R) {X Y : Pair.{w}}
    (hX : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (nonnegative R R X)))
    (hY : FlatTermsAndBoundaries.{u,max u w,v} (oppositeComplex R (nonnegative R R Y)))
    (hsX : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (nonnegative R R X)) hX)
    (hsY : AlgebraicUCT.ScalarSplittings R U (oppositeComplex R (nonnegative R R Y)) hY)
    (A B : ModuleCat.{v} R) (f : X ⟶ Y) (g : A ⟶ B) (n : ℕ)
    (Q : ProjectiveChoice Rᵐᵒᵖ
      ((oppositeFunctor R).obj ((ordinary R R X).homology (n : ℤ))))
    (Q' : ProjectiveChoice Rᵐᵒᵖ
      ((oppositeFunctor R).obj ((ordinary R R Y).homology (n : ℤ))))
    (T : TorMaps.{u,max u w,v} R 1) :
    letI := torModule T Q A
    letI := torModule T Q' B
    (∀ x, HomologicalComplex.homologyMap
        (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g.hom Y) (n+1 : ℕ)
        ((relativePositiveSequence R U X hX hsX A n Q T).α x) =
      (relativePositiveSequence R U Y hY hsY B n Q' T).α
        (TensorProduct.map
          (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) (n+1 : ℕ)).hom g.hom x)) ∧
    (∀ x, T.map Q Q'
        ((oppositeFunctor R).map (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) (n : ℤ))) g
        ((relativePositiveSequence R U X hX hsX A n Q T).β x) =
      (relativePositiveSequence R U Y hY hsY B n Q' T).β
        (HomologicalComplex.homologyMap
          (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g.hom Y) (n+1 : ℕ) x)) := by
  let PX := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (nonnegative R R X)) n))
  let PY := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖ (Algebraic.Homology (oppositeComplex R (nonnegative R R Y)) n))
  let fc := ((oppositeFunctor R).mapHomologicalComplex (ComplexShape.down ℕ)).map (relativeMap (chainFunctor R R) f)
  letI := torModule T PX A
  letI := torModule T PY B
  letI := torModule T Q A
  letI := torModule T Q' B
  let eTX := torLinearEquiv R 1 T PX Q (relativeOppositeHomologyEquiv R X n) A
  let eTY := torLinearEquiv R 1 T PY Q' (relativeOppositeHomologyEquiv R Y n) B
  have hnat := U.natural_positive _ _ hX hY fc A B g n PX PY T
  constructor
  · intro x
    change HomologicalComplex.homologyMap
        (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g.hom Y) (n+1 : ℕ)
        (relativeOrdinaryHomologyComparison R A X (n+1)
          ((U.positive _ hX A n PX).α ((relativeHomologyTensorEquiv R A X (n+1)).symm x))) =
      relativeOrdinaryHomologyComparison R B Y (n+1)
        ((U.positive _ hY B n PY).α ((relativeHomologyTensorEquiv R B Y (n+1)).symm
          (TensorProduct.map
            (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) (n+1 : ℕ)).hom g.hom x)))
    apply conjugate_natural _ _ _ _
      (relativeHomologyTensorEquiv R A X (n+1)) (relativeOrdinaryHomologyComparison R A X (n+1))
      (relativeHomologyTensorEquiv R B Y (n+1)) (relativeOrdinaryHomologyComparison R B Y (n+1)) _ _
      (fun z => LinearMap.congr_fun hnat.1 z)
      (relativeHomologyTensorEquiv_natural R A f g.hom (n+1))
      (relativeOrdinaryHomologyComparison_natural R A g.hom f (n+1)) x
  · intro x
    change T.map Q Q'
        ((oppositeFunctor R).map (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) (n : ℤ))) g
        (eTX ((U.positive _ hX A n PX).β ((relativeOrdinaryHomologyComparison R A X (n+1)).symm x))) =
      eTY ((U.positive _ hY B n PY).β ((relativeOrdinaryHomologyComparison R B Y (n+1)).symm
        (HomologicalComplex.homologyMap
          (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g.hom Y) (n+1 : ℕ) x)))
    apply conjugate_natural
      (U.positive _ hX A n PX).β (U.positive _ hY B n PY).β
      (Algebraic.homologyMap (tensorFirstMap fc A ≫ tensorSecondMap _ g.hom) (n+1))
      (T.map PX PY (ModuleCat.ofHom (Algebraic.homologyMap fc n)) g)
      (relativeOrdinaryHomologyComparison R A X (n+1)) eTX.toAddEquiv
      (relativeOrdinaryHomologyComparison R B Y (n+1)) eTY.toAddEquiv
      (HomologicalComplex.homologyMap
        (relativeMap (ordinaryFunctor R A) f ≫ relativeOrdinaryCoefficientMap R A g.hom Y) (n+1 : ℕ))
      (T.map Q Q'
        ((oppositeFunctor R).map (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) (n : ℤ))) g)
      (fun z => LinearMap.congr_fun hnat.2 z)
      (relativeOrdinaryHomologyComparison_natural R A g.hom f (n+1)) _ x
    intro z
    symm
    apply torLinearEquiv_natural R 1 T PX Q PY Q'
      (relativeOppositeHomologyEquiv R X n) (relativeOppositeHomologyEquiv R Y n)
      (ModuleCat.ofHom (Algebraic.homologyMap fc n))
      ((oppositeFunctor R).map (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor R R) f) (n : ℤ))) g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (relativeOppositeHomologyEquiv_natural R f n a).symm
end P202.UniversalCoefficientsHomology

namespace P202.UniversalCoefficientsHomology
universe u v w
open P202Specs.UniversalCoefficientsHomology P202Specs.SingularChains P202Specs.RelativeSingularChains
open P103.Specs.Ch11.UniversalCoefficientsHomology P103.Specs.Ch11.ExtTorDefinitions
variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem topological_uct :
    ∃ (T : TorMaps.{u,max u w,v} R 1) (F : RelativeTensorFamily.{u,v,w} R),
      Nonempty (TopologicalUCT.Family R T F) := by
  classical
  obtain ⟨U, hAbs, hRel⟩ := algebraic_model.{u,v,w} R
  choose hA hsA using hAbs
  choose hP hsP using hRel
  let T := P103.Ch11.ExtTorDefinitions.torMaps (R := R) 1
  let F : RelativeTensorFamily.{u,v,w} R :=
    { data := fun A _ _ =>
        ⟨relativeTensorEquiv R A, relativeTensorEquiv_projection R A,
          relativeTensorEquiv_boundary R A, relativeTensorEquiv_natural R A⟩
      natural_coefficient := fun A B _ _ _ _ g P n c =>
        relativeTensorEquiv_coefficient R A g P n c }
  refine ⟨T, F, ⟨{
    absolute := fun A X n Q => absolutePositiveSequence R U X (hA X) (hsA X) A n Q T
    relative := fun A P n Q => relativePositiveSequence R U P (hP P) (hsP P) A n Q T
    absoluteZero := fun A X => absoluteZeroIso R U A X (hA X)
    relativeZero := fun A P => relativeZeroIso R U A P (hP P)
    absoluteZeroTor := fun A X Q => ordinary_negative_tor R A X (-1) (by omega) Q 0
    relativeZeroTor := fun A P Q => relative_negative_tor R A P (-1) (by omega) Q 0
    absolute_formula := ?_
    relative_formula := ?_
    absolute_zero_formula := ?_
    relative_zero_formula := ?_
    absolute_natural_left := ?_
    absolute_natural_right := ?_
    relative_natural_left := ?_
    relative_natural_right := ?_
    absolute_zero_natural := ?_
    relative_zero_natural := ?_ }⟩⟩
  · intro A X n Q z a
    exact absolutePositiveSequence_formula R U X (hA X) (hsA X) A n Q T z a
  · intro A P n Q z a
    exact relativePositiveSequence_formula R U P (hP P) (hsP P) A n Q T z a
  · intro A X z a
    exact absoluteZeroIso_formula R U A X (hA X) z a
  · intro A P z a
    exact relativeZeroIso_formula R U A P (hP P) z a
  · intro A B X Y f g n Q Q' x
    exact (absolutePositiveSequence_natural R U (hA X) (hA Y) (hsA X) (hsA Y)
      A B f g n Q Q' T).1 x
  · intro A B X Y f g n Q Q' x
    exact (absolutePositiveSequence_natural R U (hA X) (hA Y) (hsA X) (hsA Y)
      A B f g n Q Q' T).2 x
  · intro A B P P' f g n Q Q' x
    exact (relativePositiveSequence_natural R U (hP P) (hP P') (hsP P) (hsP P')
      A B f g n Q Q' T).1 x
  · intro A B P P' f g n Q Q' x
    exact (relativePositiveSequence_natural R U (hP P) (hP P') (hsP P) (hsP P')
      A B f g n Q Q' T).2 x
  · intro A B X Y f g x
    exact absoluteZeroIso_natural R U A B f g (hA X) (hA Y) x
  · intro A B P P' f g x
    exact relativeZeroIso_natural R U A B f g (hP P) (hP P') x

end P202.UniversalCoefficientsHomology
