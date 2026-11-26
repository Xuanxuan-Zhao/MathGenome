import Specs.LinearAlgebraicGroups.Arithmetic.OddFixedVectorDensity
import LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
import LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic
import LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity
import LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.RealClasses
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.OddFixedVectorDensity

open LinearAlgebraicGroups.Specs
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.Arithmetic.QuaternionSpinOddCharacteristic (LocalQuaternionGeneration)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive)
open Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open Specs.Arithmetic.QuaternionSpinScaleCover (QuaternionHyperbolicPresentation)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open _root_.Specs.RM03.CSA (degree isCentralSimple isCentralDivision)

open private absolutelyAlmostSimpleForRadicals
  from LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity
open private reductive_of_semisimple
  from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private testPointSections
  from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso
  from LinearAlgebraicGroups.Relative.RationalDensity
open private map_test_subgroup nonarchimedean_local_infinite
  from LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

private theorem centralOfScalarEquiv {k L A B : Type*} [Field k] [Field L]
    [Ring A] [Algebra k A] [Ring B] [Algebra L B]
    [Algebra.IsCentral k A] (r : k ≃+* L) (e : A ≃+* B)
    (h : (algebraMap L B).comp r.toRingHom = e.toRingHom.comp (algebraMap k A)) :
    Algebra.IsCentral L B := by
  constructor
  intro x hx
  have hx' : e.symm x ∈ Subalgebra.center k A :=
    (MulEquivClass.apply_mem_center_iff e.symm).mpr hx
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).mp hx'
  apply Algebra.mem_bot.mpr
  refine ⟨r a, ?_⟩
  exact (DFunLike.congr_fun h a).trans ((congrArg e ha.symm).trans (e.apply_symm_apply x))

private theorem finiteOfScalarEquiv {k L A B : Type*} [Field k] [Field L]
    [Ring A] [Algebra k A] [Ring B] [Algebra L B]
    [Module.Finite k A] (r : k ≃+* L) (e : A ≃+* B)
    (h : (algebraMap L B).comp r.toRingHom = e.toRingHom.comp (algebraMap k A)) :
    Module.Finite L B := by
  let f : A →ₛₗ[r.toRingHom] B :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a x => by
        simp only [Algebra.smul_def, map_mul]
        exact congrArg (fun y : B => y * e x) (DFunLike.congr_fun h a).symm }
  have : RingHomSurjective r.toRingHom := ⟨r.surjective⟩
  exact Module.Finite.of_surjective f e.surjective

/-- Carry the real matrix factorization to the field of the actual completion. -/
private theorem realMatrixFactors (division : ArchimedeanDivision.{u}) (r : F ≃+* ℝ)
    {A : Type u} [Ring A] [Algebra F A] (hA : isCentralSimple F A) :
    (∃ n : ℕ, Nonempty (A ≃ₐ[F] Matrix (Fin n) (Fin n) F)) ∨
      ∃ (B : Type u) (_ : DivisionRing B) (_ : Algebra F B),
        isCentralSimple F B ∧ degree F B = 2 ∧
          ∃ n : ℕ, Nonempty (A ≃ₐ[F] Matrix (Fin n) (Fin n) B) := by
  classical
  let realScalar : ℝ →+* A := (algebraMap F A).comp r.symm.toRingHom
  let : Algebra ℝ A := realScalar.toAlgebra' fun a x => Algebra.commutes (r.symm a) x
  have hr : (algebraMap ℝ A).comp r.toRingHom =
      (RingEquiv.refl A).toRingHom.comp (algebraMap F A) := by
    apply RingHom.ext
    intro a
    change algebraMap F A (r.symm (r a)) = algebraMap F A a
    rw [r.symm_apply_apply]
  have := hA.2.1
  have := hA.2.2
  have hAr : isCentralSimple ℝ A := ⟨hA.1, centralOfScalarEquiv r (RingEquiv.refl A) hr,
    finiteOfScalarEquiv r (RingEquiv.refl A) hr⟩
  have lift {C : Type} [Ring C] [Algebra ℝ C] {B : Type u} [Ring B] [Algebra F B]
      (b : C ≃+* B) (hb : ∀ a : F, b (algebraMap ℝ C (r a)) = algebraMap F B a)
      {n : ℕ} (e : A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) C) :
      Nonempty (A ≃ₐ[F] Matrix (Fin n) (Fin n) B) := by
    refine ⟨{ toRingEquiv := e.toRingEquiv.trans b.mapMatrix, commutes' := ?_ }⟩
    intro a
    change b.mapMatrix (e (algebraMap F A a)) = _
    rw [show algebraMap F A a = algebraMap ℝ A (r a) from (DFunLike.congr_fun hr a).symm,
      e.commutes]
    ext i j
    by_cases hij : i = j <;> simp [RingEquiv.mapMatrix_apply, Matrix.algebraMap_eq_diagonal, hij, hb]
  obtain ⟨n, _, h⟩ := division.1 hAr
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨n, lift r.symm (fun a => r.symm_apply_apply a) e⟩
  · obtain ⟨e⟩ := h
    let B := ULift.{u} (Quaternion ℝ)
    let b : Quaternion ℝ ≃+* B := ULift.ringEquiv.symm
    let bScalar : F →+* B :=
      b.toRingHom.comp ((algebraMap ℝ (Quaternion ℝ)).comp r.toRingHom)
    let : Algebra F B := bScalar.toAlgebra' fun a x => by
      change b (algebraMap ℝ (Quaternion ℝ) (r a)) * x = x * b (algebraMap ℝ (Quaternion ℝ) (r a))
      simpa only [map_mul, b.apply_symm_apply] using
        congrArg b (Algebra.commutes (r a) (b.symm x))
    have hbr : (algebraMap F B).comp r.symm.toRingHom =
        b.toRingHom.comp (algebraMap ℝ (Quaternion ℝ)) := by
      apply RingHom.ext
      intro a
      change b (algebraMap ℝ (Quaternion ℝ) (r (r.symm a))) = b (algebraMap ℝ (Quaternion ℝ) a)
      rw [r.apply_symm_apply]
    have hH : isCentralDivision ℝ (Quaternion ℝ) := RM03.Brauer.quaternion_isCentralDivision
    have := hH.1
    have := hH.2
    have hB : isCentralDivision F B :=
      ⟨centralOfScalarEquiv r.symm b hbr, finiteOfScalarEquiv r.symm b hbr⟩
    have hd : degree F B = 2 := by
      have h := Algebra.finrank_eq_of_equiv_equiv r.symm b hbr
      unfold degree
      rw [← h, Quaternion.finrank_eq_four]
      exact Nat.sqrt_eq 2
    exact Or.inr ⟨B, inferInstance, inferInstance,
      RM03.CSA.isCentralSimple_of_isCentralDivision F B hB, hd, n, lift b (fun _ => rfl) e⟩

/-- Precomposition with the ground-field point isomorphism takes the two
contracting subgroups into the subgroup generated by all parabolic radicals. -/
private theorem twoRadicalPoints_le {c : Cocharacter G.val} (hG : IsReductive G)
    (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c)) :
    let R := CommAlgCat.of F F
    let X := (testSpec F).obj (op R)
    let e : Points G.val.X R ≃* (𝟙_ (SchemeOver F) ⟶ G.val.X) := testPointSections G.val
    (SubgroupSections U.contracting X ⊔ SubgroupSections V.contracting X).map
      e.toMonoidHom ≤ unipotentGenerated G := by
  dsimp only
  let R := CommAlgCat.of F F
  let X := (testSpec F).obj (op R)
  let T := 𝟙_ (SchemeOver F)
  let e : Points G.val.X R ≃* (T ⟶ G.val.X) := testPointSections G.val
  let A := SubgroupSections U.contracting X
  let B := SubgroupSections V.contracting X
  calc
    (A ⊔ B).map e.toMonoidHom = A.map e.toMonoidHom ⊔ B.map e.toMonoidHom :=
      Subgroup.map_sup A B e.toMonoidHom
    _ = SubgroupSections U.contracting T ⊔ SubgroupSections V.contracting T :=
      congrArg₂ (· ⊔ ·) (map_test_subgroup U.contracting) (map_test_subgroup V.contracting)
    _ ≤ unipotentGenerated G := RelativeRayGeneration.twoRadicals_le_unipotentGenerated hG U V

/-- Use the same point of the matrix realization to witness membership in the
larger subgroup of rational parabolic radicals. -/
private theorem densityFromTwoRadicals [TopologicalSpace F] (hG : IsReductive G)
    {c : Cocharacter G.val} (U : LimitDecomposition c)
    (V : LimitDecomposition (oppositeCocharacter c)) (i : MatrixRealization G)
    (h : Dense {g : PointsIn i F |
      (show Points G.val.X (CommAlgCat.of F F) from g) ∈
        SubgroupSections U.contracting ((testSpec F).obj (op (CommAlgCat.of F F))) ⊔
        SubgroupSections V.contracting ((testSpec F).obj (op (CommAlgCat.of F F)))}) :
    Dense {g : PointsIn i F | ∃ p ∈ unipotentGenerated G,
      toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ p = g} := by
  apply h.mono
  intro g hg
  let e := testPointSections G.val
  let p := e g
  refine ⟨p, twoRadicalPoints_le hG U V ⟨g, hg, rfl⟩, ?_⟩
  have hp := e.symm_apply_apply g
  change (rationalSourceIso F).inv ≫ p = g at hp
  exact (congrArg (· ≫ p) (toUnit_unique _ _)).trans hp

private theorem densityFromQuaternionModel [TopologicalSpace F]
    {K I B : Type u} [Field K] [Algebra F K] [Fintype I] [DecidableEq I]
    [DivisionRing B] [Algebra F B]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {D : DescendedQuadraticPair ρ} {P : SpinModel G D}
    {hB : isCentralSimple F B} {d : ℕ} {Q : QuaternionHyperbolicPresentation D hB d}
    (hG : IsReductive G) (h : LocalQuaternionGeneration Q P) (i : MatrixRealization G) :
    Dense {g : PointsIn i F | ∃ p ∈ unipotentGenerated G,
      toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ p = g} := by
  obtain ⟨c, _, _, _, _, _, ⟨⟨U⟩, ⟨V⟩⟩, hgen⟩ := h
  exact densityFromTwoRadicals hG U V i (hgen U V i).2.2

/-- Local density for the actual descended spin group at a finite or real place. -/
theorem oddFixedVectorDensity : Specs.Arithmetic.OddFixedVectorDensity.Statement.{u} := by
  classical
  intro F _ _ h₂ hlocal G hG hSC hfixed c hc i
  obtain ⟨K, _, _, _, _, ρ, D, _, horth, ⟨P⟩⟩ :=
    NontrialitarianSpinModels.nontrialitarianSpinModel F G 4 le_rfl hG hSC hfixed
  have hrank : 4 ≤ Fintype.card (ULift.{u} (Fin 4)) := by simp
  have hsimple := absolutelyAlmostSimpleForRadicals hG
  have hred := reductive_of_semisimple G hG.1
  rcases hlocal with ⟨v, hv⟩ | ⟨r, hr⟩
  · let : ValuativeRel F := v
    let : IsNonarchimedeanLocalField F := hv
    let : Infinite F := nonarchimedean_local_infinite F
    obtain ⟨B, _, _, n, hB, _, ⟨e⟩, hdivision⟩ :=
      NontrialitarianSpinModels.nonarchimedeanDivision h₂ D.centralSimple
        (toDivisionInvolution D.involution)
    rcases hdivision with hscalar | hdegree
    · obtain ⟨b⟩ := hscalar
      exact ScalarEvenSpinLocalDensity.scalarEvenSpinLocalDensity h₂ hrank G hG hSC
        D P (horth h₂) n (e.trans b.mapMatrix) c hc i
    · obtain ⟨d, hd, ⟨Q⟩⟩ :=
        QuaternionSpinOddCharacteristic.quaternionPresentationAtIsotropy P hrank h₂
          hB hdegree ⟨n, ⟨e⟩⟩ ⟨c, hc⟩
      exact densityFromQuaternionModel hred
        (QuaternionSpinOddCharacteristic.localGeneration.1 P hsimple hrank h₂
          hB hdegree d hd Q) i
  · let : Infinite F := Infinite.of_injective r.symm r.symm.injective
    rcases realMatrixFactors NontrialitarianSpinModels.archimedeanDivision r D.centralSimple
      with ⟨n, ⟨e⟩⟩ | ⟨B, _, _, hB, hdegree, n, ⟨e⟩⟩
    · exact ScalarEvenSpinLocalDensity.scalarEvenSpinLocalDensity h₂ hrank G hG hSC
        D P (horth h₂) n e c hc i
    · obtain ⟨d, hd, ⟨Q⟩⟩ :=
        QuaternionSpinOddCharacteristic.quaternionPresentationAtIsotropy P hrank h₂
          hB hdegree ⟨n, ⟨e⟩⟩ ⟨c, hc⟩
      exact densityFromQuaternionModel hred
        (QuaternionSpinOddCharacteristic.localGeneration.2 r hr P hsimple hrank
          hB hdegree d hd Q) i

end

end LinearAlgebraicGroups.Arithmetic.OddFixedVectorDensity
