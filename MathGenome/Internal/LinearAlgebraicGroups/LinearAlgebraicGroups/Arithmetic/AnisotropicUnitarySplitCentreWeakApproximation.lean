import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryCayleyChart
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitarySplitCentreWeakApproximation
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Topology
open scoped TensorProduct commutatorElement

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicUnitarySplitCentreWeakApproximation

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.AnisotropicUnitarySplitCentreWeakApproximation (SplitCentreWeakApproximation)
open Specs.OuterTypeAModels (RepresentsUnitary)
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (Index)
open Specs.StandardGroups (generalLinearPoints)
open AdelicGroups (LocalPoints PointsIn asMatrix changePoints localPoint)
open ArithmeticLatticeProjection (FinitePoints rationalProjection)
open UnitaryNormEquations (IsSpecialUnitary SecondKind adjointAt unitaryNorm)
open UnitaryCayleyChart (groundInvolution isometryExtension)
open LocalNormOneCommutators.Spec (coordinateTopology)
open _root_.Specs.RM03.CSA (isCentralSimple reducedNorm)
open Algebra.TensorProduct (includeRight lid)

open private groundInvolution_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryCayleyChart
open private coord_change from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
open private continuous_linear_coordinate from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

set_option backward.isDefEq.respectTransparency false

section RegularRepresentation

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
variable {n : ℕ} (c : Module.Basis (Index.{u} n) K A)

private def regularUnits (R : Type u) [CommRing R] [Algebra K R] :
    (R ⊗[K] A)ˣ →* GL (Index.{u} n) R :=
  Units.map (Algebra.leftMulMatrix (c.baseChange R)).toMonoidHom

private theorem regularUnits_natural {R S : Type u} [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : (R ⊗[K] A)ˣ) :
    regularUnits c S (Units.map (Algebra.TensorProduct.map f (.id K A)).toMonoidHom x) =
      Matrix.GeneralLinearGroup.map f.toRingHom (regularUnits c R x) := by
  apply Units.ext
  ext i j
  let F := Algebra.TensorProduct.map f (.id K A)
  change Algebra.leftMulMatrix (c.baseChange S) (F x.val) i j =
    f (Algebra.leftMulMatrix (c.baseChange R) x.val i j)
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  have hb : F (c.baseChange R j) = c.baseChange S j := by
    simp [F]
  rw [← hb, ← map_mul F]
  exact coord_change c f (x.val * c.baseChange R j) i

set_option maxHeartbeats 650000 in
/-- Represent the unitary equations by the matrices of left multiplication on
the full algebra. The equality specifies the matrix of each individual point. -/
private theorem regularRealization (c : Module.Basis (Index.{u} n) K A)
    {E : Type u} [Field E] [Algebra K E] [Algebra E A] [IsScalarTower K E A] {I : Type u} [Fintype I] (hA : isCentralSimple E A)
    (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K)
    (point : ∀ R : TestAlgebra K, Points G.val.X R ≃
      {x : (R ⊗[K] A)ˣ // IsSpecialUnitary hA b s x})
    (hmul : ∀ R (x y : ((groupPointsFunctor K).obj G.val).obj R),
      (point R (x * y)).val = (point R x).val * (point R y).val)
    (hnatural : ∀ {R S : TestAlgebra K} (f : R ⟶ S) (x : Points G.val.X R),
      (point S (mapPoints f x)).val =
        Units.map (Algebra.TensorProduct.map f.hom (.id K A)).toMonoidHom (point R x).val) :
    ∃ (i : MatrixRealization G) (c' : Module.Basis (Index.{u} i.size) K A),
      ∀ (R : Type u) [CommRing R] [Algebra K R] (x : PointsIn i R),
        asMatrix i R x = regularUnits c' R (point (CommAlgCat.of K R) x).val := by
  let F := (groupPointsFunctor K).obj G.val
  let H := StandardGroups.generalLinearGroup K (Index.{u} n)
  let e := StandardGroups.generalLinearGroupPointsIso K (Index.{u} n)
  let rep (R : TestAlgebra K) : F.obj R →* (generalLinearPoints K (Index.{u} n)).obj R :=
    MonoidHom.mk' (fun x => regularUnits c R (point R x).val) (by
      intro x y
      rw [hmul R x y, map_mul])
  have hrep (R : TestAlgebra K) : Function.Injective (rep R) := by
    intro x y he
    apply (point R).injective
    apply Subtype.ext
    apply Units.ext
    apply Algebra.leftMulMatrix_injective (c.baseChange R)
    exact congrArg (fun m : GL (Index.{u} n) R => m.val) he
  let α : F ⟶ generalLinearPoints K (Index.{u} n) :=
    { app := fun R => ConcreteCategory.ofHom (X := F.obj R)
        (Y := (generalLinearPoints K (Index.{u} n)).obj R) (rep R)
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro x
        change regularUnits c S (point S (mapPoints f x)).val =
          Matrix.GeneralLinearGroup.map f.hom.toRingHom (regularUnits c R (point R x).val)
        rw [hnatural, regularUnits_natural] }
  obtain ⟨ρ, hρ⟩ := (LinearAlgebraicGroups.groupHomComparison K G.val H.val G.prop.1).2
    (α ≫ e.inv)
  have hρcoord (R : TestAlgebra K) (x : F.obj R) :
      e.hom.app R (x ≫ ρ.hom.hom) = rep R x := by
    have he := DFunLike.congr_fun (congrArg (fun m => (m.app R).hom) hρ) x
    change x ≫ ρ.hom.hom = e.inv.app R (rep R x) at he
    rw [he]
    exact GrpCat.hom_inv_apply (e.app R) (rep R x)
  have hclosed : IsClosedImmersion ρ.hom.hom.left :=
    RootData.RootGroups.isClosedImmersion_of_injectivePoints G H ρ (fun R x y hxy =>
      hrep R ((hρcoord R x).symm.trans ((congrArg (e.hom.app R) hxy).trans (hρcoord R y))))
  exact ⟨⟨n, H, e, ρ, hclosed⟩, c, fun R _ _ x => hρcoord (CommAlgCat.of K R) x⟩

end RegularRepresentation

section RationalNorm

variable {K E A : Type u} [Field K] [Field E] [Algebra K E] [Ring A] [Algebra K A]
  [Algebra E A] [IsScalarTower K E A]
variable {I : Type u} [Fintype I] (hA : isCentralSimple E A) (b : Module.Basis I E A)

private theorem unitaryNorm_scalar (a : A) :
    unitaryNorm hA b ((1 : K) ⊗ₜ[K] a) =
      includeRight (R := K) (A := K) (reducedNorm hA a) := by
  unfold unitaryNorm
  rw [UnitaryNormEquations.associateCentre_tmul]
  let C := UnitaryNormEquations.Centre K E K
  let : Algebra E C := Algebra.TensorProduct.rightAlgebra
  have hA' : _root_.RM03.CSA.IsCentralSimple E A := hA
  change _root_.RM03.CSA.NormOneGroup.normAt hA' b
    ((1 : C) ⊗ₜ[E] a) = algebraMap E C (_root_.RM03.CSA.reducedNorm hA' a)
  rw [← _root_.RM03.CSA.reducedNorm_basis_eval hA' b a]
  unfold MvPolynomial.eval
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂]
  simp only [_root_.RM03.CSA.NormOneGroup.normAt, RingHom.comp_id,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

private theorem groundPointCondition (s : SecondKind K E A)
    (g : (groundInvolution s).isometries) (hg : reducedNorm hA g.val.val = 1) :
    IsSpecialUnitary hA b s (Units.map (lid K A).symm.toMonoidHom g.val) := by
  constructor
  · change adjointAt s (1 ⊗ₜ[K] g.val.val) * (1 ⊗ₜ[K] g.val.val) = 1
    rw [UnitaryNormEquations.adjointAt_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    change (1 : K) ⊗ₜ[K] ((s.adjoint g.val.val).unop * g.val.val) = _
    have he : (s.adjoint g.val.val).unop * g.val.val = 1 := g.property
    rw [he]
    rfl
  · change unitaryNorm hA b (1 ⊗ₜ[K] g.val.val) = 1
    rw [unitaryNorm_scalar, hg, map_one]

end RationalNorm

section Completion

variable {K E A : Type u} [Field K] [Field E] [Algebra K E] [Ring A] [Algebra K A]
  [Algebra E A] [IsScalarTower K E A]
variable {I : Type u} [Fintype I] (hA : isCentralSimple E A) (b : Module.Basis I E A)
variable (s : SecondKind K E A)

private def asIsometry {F : Type u} [Field F] [Algebra K F]
    (x : (F ⊗[K] A)ˣ) (hx : IsSpecialUnitary hA b s x) :
    ((groundInvolution s).baseChange F).isometries :=
  ⟨x, by
    change ((groundInvolution s).baseChange F).toLinearMap x.val * x.val = 1
    rw [groundInvolution_baseChange]
    exact hx.1⟩

private theorem localCommutatorClosure [Algebra.IsQuadraticExtension K E]
    [Algebra.IsSeparable K E] (D : GlobalFieldData.{u,v} K) (p : D.Place)
    (hp : ∃ w : D.FinitePlace,
      p = Sum.inl w ∧ Nonempty (E →ₐ[K] D.Completion (Sum.inl w)))
    (c : Module.Basis (Fin (Module.finrank (D.Completion p) (D.Completion p ⊗[K] A)))
      (D.Completion p) (D.Completion p ⊗[K] A))
    (x : ((groundInvolution s).baseChange (D.Completion p)).isometries)
    (hx : IsSpecialUnitary hA b s x.val) :
    letI := coordinateTopology c
    x ∈ closure (commutator (((groundInvolution s).baseChange (D.Completion p)).isometries) :
      Set ((groundInvolution s).baseChange (D.Completion p)).isometries) := by
  obtain ⟨w, rfl, ⟨j⟩⟩ := hp
  let F := D.Completion (Sum.inl w)
  let : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  let : Algebra E F := j.toRingHom.toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun k => (j.commutes k).symm
  exact UnitaryCayleyChart.finiteSplitCentreCommutators (F := F) hA b s c x hx

omit [IsScalarTower K E A] in
private theorem extension_unit {F : Type u} [Field F] [Algebra K F]
    (g : (groundInvolution s).isometries) :
    Units.map (Algebra.TensorProduct.map (Algebra.ofId K F) (.id K A)).toMonoidHom
        (Units.map (lid K A).symm.toMonoidHom g.val) =
      (isometryExtension (F := F) (groundInvolution s) g).val := by
  apply Units.ext
  change Algebra.TensorProduct.map (Algebra.ofId K F) (.id K A) (1 ⊗ₜ[K] g.val.val) =
    includeRight (A := F) g.val.val
  simp [Algebra.TensorProduct.map_tmul]

end Completion

private theorem continuous_regularValue {F B ι : Type u} {κ : Type*} [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] [Ring B] [Algebra F B]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (b : Module.Basis ι F B) (c : Module.Basis κ F B) (U : Subgroup Bˣ) :
    letI := coordinateTopology c
    Continuous (fun x : U => Algebra.leftMulMatrix b x.val.val) := by
  let := coordinateTopology c
  have hmatrix : Continuous (Algebra.leftMulMatrix b) := by
    refine continuous_matrix fun i j => ?_
    simp_rw [Algebra.leftMulMatrix_eq_repr_mul]
    exact continuous_linear_coordinate c ((b.coord i).comp (LinearMap.mulRight F (b j)))
  have hval : Continuous (fun x : U => x.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  exact hmatrix.comp hval

private theorem densityChangeRealization {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i j : MatrixRealization G) (J : Finset D.Place)
    (h : DenseRange (rationalProjection D j J)) :
    DenseRange (rationalProjection D i J) := by
  let f : FinitePoints D j J → FinitePoints D i J :=
    fun x w => changePoints j i (D.Completion w.1) (x w)
  have hcont : Continuous f :=
    continuous_pi fun w => (AdelicGroups.continuous_changePoints j i (D.Completion w.1)).comp
      (continuous_apply w)
  have hsurj : Function.Surjective f := fun x =>
    ⟨fun w => (changePoints j i (D.Completion w.1)).symm (x w), funext fun w =>
      (changePoints j i (D.Completion w.1)).apply_symm_apply (x w)⟩
  exact hsurj.denseRange.comp h hcont

set_option maxHeartbeats 650000 in
private theorem finiteMatricesInducing {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (j : MatrixRealization G) (J : Finset D.Place) :
    IsInducing (fun (x : FinitePoints D j J) (p : J) =>
      (asMatrix j (D.Completion p.1) (x p)).val) := by
  refine IsInducing.piMap (f := fun (p : J) (x : LocalPoints D j p.1) =>
    (asMatrix j (D.Completion p.1) x).val) ?_
  intro p
  exact (AdelicGroups.usualLocalTopology D j p.1).isInducing

set_option maxHeartbeats 900000 in
/-- The split-centre density follows directly from the represented equations.
This formulation also applies when the representation has been obtained
without imposing separate hypotheses on the geometric root datum. -/
theorem splitCentreWeakApproximationOfUnitaryModel
    {K E A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    {I : Type u} [Fintype I] (hA : isCentralSimple E A)
    (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K)
    (hunitary : RepresentsUnitary hA b s G)
    (i : MatrixRealization G) (J : Finset D.Place)
    (hJ : ∀ p ∈ J, ∃ w : D.FinitePlace,
      p = Sum.inl w ∧ Nonempty (E →ₐ[K] D.Completion (Sum.inl w))) :
    DenseRange (rationalProjection D i J) := by
  let : Module.Finite E A := hA.2.2
  let : Module.Finite K A := Module.Finite.trans E A
  obtain ⟨point, hmul, hnatural⟩ := hunitary
  let c₀ : Module.Basis (Index.{u} (Module.finrank K A)) K A :=
    (Module.finBasis K A).reindex Equiv.ulift.symm
  obtain ⟨j, c, hj⟩ := regularRealization c₀ hA b s G point hmul hnatural
  apply densityChangeRealization D i j J
  let F (p : J) := D.Completion p.1
  let B (p : J) := F p ⊗[K] A
  let U (p : J) := ((groundInvolution s).baseChange (F p)).isometries
  let basis (p : J) := Module.finBasis (F p) (B p)
  let (p : J) : TopologicalSpace (B p) := coordinateTopology (basis p)
  let M (p : J) := Matrix (Index.{u} j.size) (Index.{u} j.size) (F p)
  let fromIsometries : (∀ p : J, U p) → (∀ p : J, M p) :=
    fun x p => Algebra.leftMulMatrix (c.baseChange (F p)) (x p).val.val
  have hfactor (p : J) : Continuous (fun x : U p =>
      Algebra.leftMulMatrix (c.baseChange (F p)) x.val.val) := by
    let : IsTopologicalRing (F p) := inferInstanceAs (IsTopologicalRing (D.Completion p.1))
    exact continuous_regularValue (F := F p) (B := B p) (c.baseChange (F p)) (basis p) (U p)
  have hcontinuous : Continuous fromIsometries :=
    Continuous.piMap (f := fun p (x : U p) =>
      Algebra.leftMulMatrix (c.baseChange (F p)) x.val.val) hfactor
  let realized : FinitePoints D j J → (∀ p : J, M p) :=
    fun x p => (asMatrix j (F p) (x p)).val
  have hind : IsInducing realized := finiteMatricesInducing D j J
  intro x
  let y : ∀ p : J, U p := fun p =>
    asIsometry hA b s (point (CommAlgCat.of K (F p)) (x p)).val (point _ (x p)).property
  have hy : ∀ p : J, y p ∈ closure (commutator (U p) : Set (U p)) := fun p =>
    localCommutatorClosure hA b s D p.1 (hJ p.1 p.2) (basis p) (y p) (point _ (x p)).property
  let rationalExtension (a : {g : (groundInvolution s).isometries // reducedNorm hA g.val.val = 1}) :
      ∀ p : J, U p := fun p => isometryExtension (F := F p) (groundInvolution s) a.val
  have hclosure : y ∈ closure (Set.range rationalExtension) :=
    UnitaryCayleyChart.simultaneousNormOneApproximation D hA s J basis y hy
  have heval : fromIsometries y = realized x := by
    funext p
    exact (congrArg Units.val (hj (F p) (x p))).symm
  rw [hind.closure_eq_preimage_closure_image]
  change realized x ∈ closure (realized '' Set.range (rationalProjection D j J))
  rw [← heval]
  refine closure_mono ?_ (mem_closure_image hcontinuous.continuousAt hclosure)
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  let aK : {x : (K ⊗[K] A)ˣ // IsSpecialUnitary hA b s x} :=
    ⟨Units.map (lid K A).symm.toMonoidHom a.val.val, groundPointCondition hA b s a.val a.property⟩
  let g : RationalPoints G := (point (CommAlgCat.of K K)).symm aK
  refine ⟨rationalProjection D j J g, ⟨g, rfl⟩, ?_⟩
  funext p
  have hbase : (point (CommAlgCat.of K K) g).val = aK.val :=
    congrArg Subtype.val ((point (CommAlgCat.of K K)).apply_symm_apply aK)
  have hpoint : (point (CommAlgCat.of K (F p)) (localPoint D j p.1 g)).val =
      (rationalExtension a p).val := by
    rw [show localPoint D j p.1 g =
      mapPoints (CommAlgCat.ofHom (Algebra.ofId K (F p))) g from rfl, hnatural, hbase]
    exact extension_unit s a.val
  change (asMatrix j (F p) (localPoint D j p.1 g)).val =
    Algebra.leftMulMatrix (c.baseChange (F p)) (rationalExtension a p).val.val
  rw [hj, hpoint]
  rfl

theorem splitCentreWeakApproximation : SplitCentreWeakApproximation.{u,v} := by
  intro K E A _ D _ _ _ _ _ _ _ hKE I _ hA _ b s G _ _ hunitary i J hJ
  let : Algebra.IsQuadraticExtension K E := ⟨hKE⟩
  exact splitCentreWeakApproximationOfUnitaryModel D hA b s G hunitary i J hJ

end LinearAlgebraicGroups.Arithmetic.AnisotropicUnitarySplitCentreWeakApproximation
