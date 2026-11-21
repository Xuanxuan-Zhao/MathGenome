import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.AbsoluteIsomorphism
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.RelativeIsomorphism
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ContinuousCohomology
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.GaloisSplitting
import Batteries.Tactic.OpenPrivate

/-! Compatibility of the scalar-defect class under extension of scalars. -/

namespace RM03.Brauer.AbsoluteIsomorphism

open ContinuousCohomology ProjectiveClassification RelativeIsomorphism ScalarObstruction
open Specs.RM03.Brauer.AbsoluteIsomorphism
open Specs.RM03.Brauer.ScalarObstruction
open Matrix Algebra.TensorProduct
open scoped TensorProduct MatrixGroups

universe u v w x

noncomputable section

variable {k : Type u} [Field k]
variable {E : Type v} [Field E] [Algebra k E]
variable {F : Type w} [Field F] [Algebra k F] [Algebra E F] [IsScalarTower k E F]
variable {A : Type x} [Ring A] [Algebra k A]
variable {n : ℕ}

private def extendSplitting (s : (E ⊗[k] A) ≃ₐ[E] Mat E n) :
    (F ⊗[k] A) ≃ₐ[F] Mat F n :=
  (baseChangeTower k E F A).symm |>.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) s)
    |>.trans (baseChangeMatrix E F n E)
    |>.trans (Algebra.TensorProduct.rid E F F).mapMatrix

private theorem extendSplitting_tmul (s : (E ⊗[k] A) ≃ₐ[E] Mat E n)
    (b : F) (a : A) (i j : Fin n) :
    extendSplitting s (b ⊗ₜ[k] a) i j =
      b * algebraMap E F (s ((1 : E) ⊗ₜ[k] a) i j) := by
  have h : (baseChangeTower k E F A).symm (b ⊗ₜ[k] a) =
      b ⊗ₜ[E] ((1 : E) ⊗ₜ[k] a) := by
    apply (baseChangeTower k E F A).injective
    simp
  simp only [extendSplitting, AlgEquiv.trans_apply, h, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply,
    AlgEquiv.mapMatrix_apply, Matrix.map_apply, baseChangeMatrix_tmul, Algebra.TensorProduct.rid_tmul]
  rw [Algebra.smul_def, mul_comm]
  rfl

private theorem extendSplitting_tmul_matrix (s : (E ⊗[k] A) ≃ₐ[E] Mat E n)
    (b : F) (a : A) :
    extendSplitting s (b ⊗ₜ[k] a) =
      b • (s ((1 : E) ⊗ₜ[k] a)).map (algebraMap E F) :=
  Matrix.ext fun i j => extendSplitting_tmul s b a i j

open private presents_apply presents_of_formula from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ScalarObstruction

section Tower

variable {S : Type v} [Field S] [Algebra k S] {I J : Stage k S}

private abbrev stageGL (h : I ≤ J) : GL (Fin n) I →* GL (Fin n) J :=
  GeneralLinearGroup.map (IntermediateField.inclusion h).toRingHom

private theorem stageGL_mapGL (h : I ≤ J) (g : Gal(J/k)) (U : GL (Fin n) I) :
    stageGL h (mapGL (stageRestrict h g) U) = mapGL g (stageGL h U) := by
  apply GeneralLinearGroup.ext
  intro i j
  exact stageRestrict_apply h g (U i j)

private theorem stageGL_scalar (h : I ≤ J) (a : Iˣ) :
    stageGL h (GeneralLinearGroup.scalar (Fin n) a) =
      GeneralLinearGroup.scalar (Fin n) (stageUnits h a) := by
  apply GeneralLinearGroup.ext
  intro i j
  change (IntermediateField.inclusion h) (Matrix.scalar (Fin n) (a : I) i j) =
    Matrix.scalar (Fin n) ((stageUnits h a : Jˣ) : J) i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [stageUnits]

private theorem inflate_records (h : I ≤ J) {G : Gal(I/k) → GL (Fin n) I}
    {c : ScalarCocycle k I} (hc : RecordsDefect G c) :
    RecordsDefect (fun g => stageGL h (G (stageRestrict h g))) (inflateCocycle h c) := by
  intro g j
  simpa only [inflateCocycle_apply, map_mul, map_inv, stageGL_scalar, stageGL_mapGL] using
    congrArg (stageGL h) (hc (stageRestrict h g) (stageRestrict h j))

private theorem extend_presents (h : I ≤ J) (hn : 0 < n)
    (s : (I ⊗[k] A) ≃ₐ[I] Mat I n) (G : Gal(I/k) → GL (Fin n) I)
    (hG : Presents s G) :
    ∃ t : (J ⊗[k] A) ≃ₐ[J] Mat J n,
      Presents t (fun g => stageGL h (G (stageRestrict h g))) := by
  let : Algebra I J := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower k I J := IsScalarTower.of_algebraMap_eq
    (fun x => ((IntermediateField.inclusion h).commutes x).symm)
  refine ⟨extendSplitting s, presents_of_formula hn _ _ ?_⟩
  intro g b a
  let r := stageRestrict h g
  let i := (IntermediateField.inclusion h).toRingHom
  have fixed := presents_apply hG r (1 : I) a
  rw [map_one] at fixed
  have mapped := congrArg (RingHom.mapMatrix (m := Fin n) i) fixed
  simp only [map_mul, RingHom.mapMatrix_apply] at mapped
  have hmap : ((s ((1 : I) ⊗ₜ[k] a)).map r).map i =
      ((s ((1 : I) ⊗ₜ[k] a)).map i).map g :=
    Matrix.ext fun p q => stageRestrict_apply h g (s ((1 : I) ⊗ₜ[k] a) p q)
  rw [hmap] at mapped
  rw [extendSplitting_tmul_matrix, extendSplitting_tmul_matrix,
    Matrix.map_smul' _ _ _ (map_mul g), Matrix.mul_smul, Matrix.smul_mul]
  exact congrArg (fun X : Mat J n => g b • X) mapped

end Tower

section Relative

variable {S : Type v} [Field S] [Algebra k S] {I J : Stage k S}

private theorem stage_kernel_le (h : I ≤ J) [AddCommGroup (BrauerGroup.{u, max u v w} k)]
    {B C : AddSubgroup (BrauerGroup.{u, max u v w} k)}
    (hB : IsStageKernel I B) (hC : IsStageKernel J C) : B ≤ C := by
  let : Algebra I J := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower k I J := IsScalarTower.of_algebraMap_eq
    (fun x => ((IntermediateField.inclusion h).commutes x).symm)
  intro a
  refine Quotient.inductionOn a fun A hA => ?_
  obtain ⟨n, hn, ⟨s⟩⟩ := (hB A).mp hA
  exact (hC A).mpr ⟨n, hn, ⟨extendSplitting s⟩⟩

/-- The relative obstruction commutes with extension through finite Galois stages. -/
theorem relative_inflation : RelativeInflation.{u,v,w} := by
  intro k S _ _ _ I J h g B C hB hC φ ψ hφ hψ
  let _ := g
  let le : B ≤ C := stage_kernel_le h hB hC
  refine ⟨le, AddMonoidHom.ext ?_⟩
  rintro ⟨a, ha⟩
  revert ha
  refine Quotient.inductionOn a fun A hA => ?_
  obtain ⟨n, hn, ⟨s⟩⟩ := (hB A).mp hA
  obtain ⟨G, hG⟩ := exists_presentation hn s
  obtain ⟨c, hc⟩ := exists_recorded_defect hn hG
  obtain ⟨t, ht⟩ := extend_presents h hn s G hG
  calc
    ψ ⟨Specs.RM03.Brauer.classOf A, le hA⟩ =
        Additive.ofMul (cocycleClass k J (inflateCocycle h c)) :=
      hψ A (le hA) hn t _ ht _ (inflate_records h hc)
    _ = stageTransition I J h (Additive.ofMul (cocycleClass k I c)) := rfl
    _ = stageTransition I J h (φ ⟨Specs.RM03.Brauer.classOf A, hA⟩) :=
      congrArg (stageTransition I J h) (hφ A hA hn s G hG c hc).symm

/-- The relative Brauer group at a finite Galois stage of the given closure. -/
abbrev StageBrauer (I : Stage k S) := relativeBrauerGroup.{u,v,w} k I

private theorem stage_isKernel (I : Stage k S) : IsStageKernel I (StageBrauer.{u,v,w} I) :=
  classOf_mem_relativeBrauerGroup_iff k I

/-- The subgroup inclusion, acting by the identity on the underlying Brauer class. -/
def stageInclusion (h : I ≤ J) : StageBrauer.{u,v,w} I →+ StageBrauer.{u,v,w} J :=
  AddSubgroup.inclusion (stage_kernel_le h (stage_isKernel I) (stage_isKernel J))

abbrev stageEquiv (I : Stage k S) : StageBrauer.{u,v,w} I ≃+ StageCohomology I :=
  relativeBrauerEquiv.{u,v,w} (k := k) (K := I)

/-- The canonical relative isomorphisms intertwine inclusion and inflation. -/
theorem relativeBrauerEquiv_compatible (h : I ≤ J) (a : StageBrauer.{u,v,w} I) :
    stageEquiv J (stageInclusion h a) = stageTransition I J h (stageEquiv I a) := by
  have hI : IsStageObstruction I (stageEquiv.{u,v,w} I).toAddMonoidHom :=
    obstruction_formula.{u,v,w} k I
  have hJ : IsStageObstruction J (stageEquiv.{u,v,w} J).toAddMonoidHom :=
    obstruction_formula.{u,v,w} k J
  obtain ⟨le, he⟩ := relative_inflation.{u,v,w} h (stage_isKernel I) (stage_isKernel J)
    _ _ hI hJ
  exact DFunLike.congr_fun he a

end Relative

section Absolute

variable {S : Type v} [Field S] [Algebra k S] [hSep : IsSepClosure k S]

/-- Finite Galois splitting fields can be taken inside the given separable closure. -/
theorem finite_stage_cover : FiniteStageCover.{u,v,w} := by
  intro k S _ _ _ _ a
  refine Quotient.inductionOn a fun (A : _root_.CSA.{u, max u v w} k) => ?_
  obtain ⟨hn, _, K, hK, hAlg, hFin, hGal, ⟨s⟩⟩ :=
    CSA.galois_splitting (A := A) ⟨A.isSimple, A.isCentral, A.fin_dim⟩
  let _ := hK
  let _ := hAlg
  let _ := hFin
  let _ := hGal
  let : IsSepClosed S := IsSepClosure.sep_closed k
  let f : K →ₐ[k] S := IsSepClosed.lift
  let e : K ≃ₐ[k] f.fieldRange := f.equivFieldRange
  let I : Stage k S := {
    toIntermediateField := f.fieldRange
    finiteDimensional := FiniteDimensional.of_surjective e.toLinearMap e.surjective
    isGalois := IsGalois.of_algEquiv e }
  let : Algebra K I := e.toAlgHom.toAlgebra
  let : IsScalarTower k K I := IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  exact ⟨I, A, rfl, _, hn, ⟨extendSplitting s⟩⟩

/-- The finite relative kernels cover the full Brauer group. -/
theorem exists_relative_stage (a : BrauerGroup.{u, max u v w} k) :
    ∃ I : Stage k S, a ∈ StageBrauer.{u,v,w} I := by
  obtain ⟨I, A, rfl, hA⟩ := finite_stage_cover.{u,v,w} (S := S) a
  exact ⟨I, (stage_isKernel I A).mpr hA⟩

private def continuousObstruction (I : Stage k S) :
    StageBrauer.{u,v,w} I →+ Additive (H2Continuous k S) :=
  (toContinuous I).toAdditive.comp (stageEquiv I).toAddMonoidHom

omit [IsSepClosure k S] in
private theorem continuousObstruction_compatible {I J : Stage k S} (h : I ≤ J)
    (a : StageBrauer.{u,v,w} I) :
    continuousObstruction J (stageInclusion h a) = continuousObstruction I a := by
  change Additive.ofMul (toContinuous J (stageEquiv J (stageInclusion h a)).toMul) =
    Additive.ofMul (toContinuous I (stageEquiv I a).toMul)
  rw [relativeBrauerEquiv_compatible h a]
  exact congrArg Additive.ofMul (DFunLike.congr_fun (toContinuous_compatible h)
    (stageEquiv I a).toMul)

omit [IsSepClosure k S] in
private theorem continuousObstruction_eq {I J : Stage k S}
    (a : StageBrauer.{u,v,w} I) (b : StageBrauer.{u,v,w} J) (h : a.val = b.val) :
    continuousObstruction I a = continuousObstruction J b := by
  rw [← continuousObstruction_compatible (J := I ⊔ J) le_sup_left a,
    ← continuousObstruction_compatible (J := I ⊔ J) le_sup_right b]
  exact congrArg (continuousObstruction (I ⊔ J)) (Subtype.ext h)

include hSep

private def absoluteValue (a : BrauerGroup.{u, max u v w} k) :
    Additive (H2Continuous k S) :=
  let I := (exists_relative_stage.{u,v,w} (S := S) a).choose
  continuousObstruction.{u,v,w} I ⟨a, (exists_relative_stage.{u,v,w} (S := S) a).choose_spec⟩

private theorem absoluteValue_stage (I : Stage k S) (a : StageBrauer.{u,v,w} I) :
    absoluteValue.{u,v,w} a.val = continuousObstruction.{u,v,w} I a :=
  continuousObstruction_eq.{u,v,w} _ a rfl

private def absoluteHom :
    letI := instAddCommGroup.{u, max v w} k
    BrauerGroup.{u, max u v w} k →+ Additive (H2Continuous k S) := by
  letI := instAddCommGroup.{u, max v w} k
  refine {
    toFun := absoluteValue.{u,v,w} (S := S)
    map_zero' := ?_
    map_add' := ?_ }
  · let I : Stage k S := ⊥
    calc
      absoluteValue.{u,v,w} (S := S) 0 =
          continuousObstruction.{u,v,w} I (0 : StageBrauer.{u,v,w} I) :=
        absoluteValue_stage.{u,v,w} I 0
      _ = 0 := map_zero (continuousObstruction.{u,v,w} I)
  · intro a b
    obtain ⟨I, ha⟩ := exists_relative_stage.{u,v,w} (S := S) a
    obtain ⟨J, hb⟩ := exists_relative_stage.{u,v,w} (S := S) b
    let L : Stage k S := I ⊔ J
    let a' := stageInclusion.{u,v,w} (J := L) le_sup_left ⟨a, ha⟩
    let b' := stageInclusion.{u,v,w} (J := L) le_sup_right ⟨b, hb⟩
    have hab : (a' + b').val = a + b := rfl
    calc
      absoluteValue.{u,v,w} (S := S) (a + b) =
          absoluteValue.{u,v,w} (S := S) (a' + b').val :=
        congrArg (absoluteValue.{u,v,w} (S := S)) hab.symm
      _ = continuousObstruction.{u,v,w} L (a' + b') := absoluteValue_stage.{u,v,w} L _
      _ = continuousObstruction.{u,v,w} L a' + continuousObstruction.{u,v,w} L b' :=
        map_add (continuousObstruction.{u,v,w} L) _ _
      _ = absoluteValue.{u,v,w} (S := S) a + absoluteValue.{u,v,w} (S := S) b :=
        congrArg₂ (· + ·) (absoluteValue_stage.{u,v,w} L a').symm
          (absoluteValue_stage.{u,v,w} L b').symm

private theorem absoluteHom_injective :
    Function.Injective (absoluteHom.{u,v,w} (k := k) (S := S)) := by
  intro a b hab
  obtain ⟨I, ha⟩ := exists_relative_stage.{u,v,w} (S := S) a
  obtain ⟨J, hb⟩ := exists_relative_stage.{u,v,w} (S := S) b
  let a' : StageBrauer.{u,v,w} I := ⟨a, ha⟩
  let b' : StageBrauer.{u,v,w} J := ⟨b, hb⟩
  change absoluteValue.{u,v,w} (S := S) a'.val = absoluteValue.{u,v,w} (S := S) b'.val at hab
  rw [absoluteValue_stage.{u,v,w} I a', absoluteValue_stage.{u,v,w} J b'] at hab
  have heq : toContinuous I (stageEquiv.{u,v,w} I a').toMul = toContinuous J (stageEquiv.{u,v,w} J b').toMul :=
    congrArg Additive.toMul hab
  obtain ⟨L, hIL, hJL, h⟩ := (equal_at_finite_stage _ _).mp heq
  have hh : stageEquiv.{u,v,w} L (stageInclusion.{u,v,w} hIL a') = stageEquiv.{u,v,w} L (stageInclusion.{u,v,w} hJL b') := by
    rw [relativeBrauerEquiv_compatible.{u,v,w} hIL a', relativeBrauerEquiv_compatible.{u,v,w} hJL b']
    exact congrArg Additive.ofMul h
  exact congrArg Subtype.val ((stageEquiv.{u,v,w} L).injective hh)

private theorem absoluteHom_surjective :
    Function.Surjective (absoluteHom.{u,v,w} (k := k) (S := S)) := by
  intro z
  obtain ⟨I, c, hc⟩ := finite_class_representative (k := k) z.toMul
  let a : StageBrauer.{u,v,w} I := (stageEquiv.{u,v,w} I).symm (Additive.ofMul c)
  refine ⟨a.val, (absoluteValue_stage.{u,v,w} I a).trans ?_⟩
  change Additive.ofMul (toContinuous I ((stageEquiv.{u,v,w} I) a).toMul) = z
  rw [(stageEquiv.{u,v,w} I).apply_symm_apply]
  exact congrArg Additive.ofMul hc

/-- The absolute Brauer group isomorphism in the scalar-defect convention. -/
def absoluteBrauerEquiv :
    letI := instAddCommGroup.{u, max v w} k
    BrauerGroup.{u, max u v w} k ≃+ Additive (H2Continuous k S) := by
  letI := instAddCommGroup.{u, max v w} k
  exact AddEquiv.ofBijective absoluteHom.{u,v,w}
    ⟨absoluteHom_injective.{u,v,w}, absoluteHom_surjective.{u,v,w}⟩

/-- The absolute map on a class split at a finite Galois stage is the inflation
of the canonical relative scalar class at that stage. -/
theorem absoluteBrauerEquiv_apply (I : Stage k S) (a : StageBrauer.{u,v,w} I) :
    absoluteBrauerEquiv.{u,v,w} (S := S) a.val =
      Additive.ofMul (toContinuous I (stageEquiv.{u,v,w} I a).toMul) :=
  absoluteValue_stage.{u,v,w} I a

end Absolute

open private groupLaws from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.BaseChange

theorem absolute_brauer_isomorphism : AbsoluteBrauerIsomorphism.{u,v,w} := by
  intro k S _ _ _ _
  refine ⟨instAddCommGroup.{u,max v w} k, groupLaws.{u,max v w} k, absoluteBrauerEquiv.{u,v,w}, ?_⟩
  intro I A n hn s G hG c hc
  have hA : classOf A ∈ StageBrauer.{u,v,w} I :=
    (stage_isKernel.{u,v,w} I A).mpr ⟨n, hn, ⟨s⟩⟩
  let a : StageBrauer.{u,v,w} I := ⟨classOf A, hA⟩
  have hf : stageEquiv.{u,v,w} I a = Additive.ofMul (cocycleClass k I c) :=
    obstruction_formula.{u,v,w} k I A hA hn s G hG c hc
  exact (absoluteBrauerEquiv_apply.{u,v,w} I a).trans
    (congrArg (fun z => Additive.ofMul (toContinuous I z.toMul)) hf)

end
end RM03.Brauer.AbsoluteIsomorphism
