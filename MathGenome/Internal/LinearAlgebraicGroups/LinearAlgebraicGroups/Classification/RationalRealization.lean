import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.RationalRealization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.EuclideanComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Orthogonality
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreSimplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.UniversalEnveloping
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightClassification
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Smooth.Field
import Mathlib.LinearAlgebra.RootSystem.Chain
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Group
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Lie.Engel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootStrings
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SemisimpleBaseChange

open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.RationalRealization

open Specs.RationalRealization (generator rationalWeightSpace)
open LieAlgebra.ExtendScalars (bracket_tmul)
open LieAlgebrasAndRepresentations

noncomputable section

private def serreProjection (K : Type*) [CommRing K] {ι : Type*} [DecidableEq ι]
    (A : Matrix ι ι ℤ) :
    FreeLieAlgebra K (CartanMatrix.Generators ι) →ₗ⁅K⁆ Matrix.ToLieAlgebra K A :=
  { (CartanMatrix.Relations.toIdeal K A).toSubmodule.mkQ with
    map_lie' := fun {_ _} => rfl }

private def quotientLift {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing M] [LieAlgebra K M] (I : LieIdeal K L) (f : L →ₗ⁅K⁆ M)
    (hf : I ≤ f.ker) : L ⧸ I →ₗ⁅K⁆ M :=
  { I.toSubmodule.liftQ f.toLinearMap hf with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with | _ x =>
      induction y using Submodule.Quotient.induction_on with | _ y =>
      exact f.map_lie x y }

private theorem hom_ext {K ι L : Type*} [CommRing K] [DecidableEq ι]
    [LieRing L] [LieAlgebra K L] (A : Matrix ι ι ℤ)
    {f g : Matrix.ToLieAlgebra K A →ₗ⁅K⁆ L}
    (h : ∀ s, f (generator K A s) = g (generator K A s)) : f = g := by
  have hh : f.comp (serreProjection K A) = g.comp (serreProjection K A) :=
    FreeLieAlgebra.hom_ext h
  apply LieHom.ext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, serreProjection K A y = x := Quot.mk_surjective x
  exact LieHom.congr_fun hh y

section Lift

variable {K K' L : Type*} [CommRing K] [CommRing K'] [LieRing L] [LieAlgebra K' L]
variable {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℤ)

private theorem map_iterBracket {M N : Type*} [LieRing M] [LieRing N]
    (f : M →+ N) (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆)
    (x y : M) (n : ℕ) :
    f (Serre.iterBracket x n y) = Serre.iterBracket (f x) n (f y) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Serre.iterBracket, hf, ih, Serre.iterBracket]

private theorem iterBracket_eq_ad_pow {R M : Type*} [CommRing R] [LieRing M]
    [LieAlgebra R M] (x y : M) (n : ℕ) :
    Serre.iterBracket x n y = (LieAlgebra.ad R M x ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Serre.iterBracket, ih, pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]

/-- Every additive bracket-preserving map carries the integral relators
to the same expressions in the images of the generators. -/
private theorem relations_le_ker
    (f : Matrix.ToLieAlgebra K A →+ L)
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) :
    CartanMatrix.Relations.toIdeal K' A ≤
      (FreeLieAlgebra.lift K' (f ∘ generator K A)).ker := by
  let p := serreProjection K A
  let q := FreeLieAlgebra.lift K' (f ∘ generator K A)
  have maple (x y : FreeLieAlgebra K (CartanMatrix.Generators ι)) (n : ℕ) :
      p (Serre.iterBracket x n y) = Serre.iterBracket (p x) n (p y) :=
    map_iterBracket (p.toLinearMap.toAddMonoidHom) p.map_lie x y n
  have maql (x y : FreeLieAlgebra K' (CartanMatrix.Generators ι)) (n : ℕ) :
      q (Serre.iterBracket x n y) = Serre.iterBracket (q x) n (q y) :=
    map_iterBracket (q.toLinearMap.toAddMonoidHom) q.map_lie x y n
  have mapfl (x y : Matrix.ToLieAlgebra K A) (n : ℕ) :
      f (Serre.iterBracket x n y) = Serre.iterBracket (f x) n (f y) :=
    map_iterBracket f hf x y n
  have hp (s : CartanMatrix.Generators ι) :
      p (FreeLieAlgebra.of K s) = generator K A s := rfl
  have hq (s : CartanMatrix.Generators ι) :
      q (FreeLieAlgebra.of K' s) = f (generator K A s) :=
    FreeLieAlgebra.lift_of_apply _ _
  have rel_zero {z} (hz : z ∈ CartanMatrix.Relations.toSet K A) : p z = 0 :=
    LieSubmodule.Quotient.mk_eq_zero'.2 (LieSubmodule.subset_lieSpan hz)
  apply LieSubmodule.lieSpan_le.mpr
  intro z hz
  change q z = 0
  simp only [CartanMatrix.Relations.toSet, Set.mem_union] at hz
  rcases hz with (((((hz | hz) | hz) | hz) | hz) | hz)
  · rcases hz with ⟨i, rfl⟩
    have h := congrArg f (rel_zero (show CartanMatrix.Relations.HH K i ∈ _ from
      Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Set.mem_range_self i)))))))
    simpa only [CartanMatrix.Relations.HH, Function.uncurry, Function.comp_apply,
      LieHom.map_lie, hp, hq, hf, map_zero] using h
  · rcases hz with ⟨⟨i, j⟩, rfl⟩
    have h := congrArg f (rel_zero (show CartanMatrix.Relations.EF K (i,j) ∈ _ from
      Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_range_self (i,j))))))))
    by_cases hij : i = j <;>
      simpa [CartanMatrix.Relations.EF, Function.uncurry, Function.comp_apply,
        hij, LieHom.map_lie, hp, hq, hf] using h
  · rcases hz with ⟨i, rfl⟩
    have h := congrArg f (rel_zero (show CartanMatrix.Relations.HE K A i ∈ _ from
      Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_range_self i))))))
    simpa only [CartanMatrix.Relations.HE, Function.uncurry, Function.comp_apply,
      LieHom.map_lie, hp, hq, hf, map_sub, map_zsmul, map_zero] using h
  · rcases hz with ⟨i, rfl⟩
    have h := congrArg f (rel_zero (show CartanMatrix.Relations.HF K A i ∈ _ from
      Or.inl (Or.inl (Or.inr (Set.mem_range_self i)))))
    simpa only [CartanMatrix.Relations.HF, Function.uncurry, Function.comp_apply,
      LieHom.map_lie, hp, hq, hf, map_add, map_zsmul, map_zero] using h
  · rcases hz with ⟨i, rfl⟩
    have h := congrArg f (rel_zero (show CartanMatrix.Relations.adE K A i ∈ _ from
      Or.inl (Or.inr (Set.mem_range_self i))))
    rcases i with ⟨i, j⟩
    simpa only [CartanMatrix.Relations.adE, Function.uncurry, Function.comp_apply,
      ← iterBracket_eq_ad_pow, maple, maql, LieHom.map_lie, hp, hq, hf,
      mapfl, map_zero] using h
  · rcases hz with ⟨i, rfl⟩
    have h := congrArg f (rel_zero (show CartanMatrix.Relations.adF K A i ∈ _ from
      Or.inr (Set.mem_range_self i)))
    rcases i with ⟨i, j⟩
    simpa only [CartanMatrix.Relations.adF, Function.uncurry, Function.comp_apply,
      ← iterBracket_eq_ad_pow, maple, maql, LieHom.map_lie, hp, hq, hf,
      mapfl, map_zero] using h

private def liftFromGenerators (f : Matrix.ToLieAlgebra K A →+ L)
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) : Matrix.ToLieAlgebra K' A →ₗ⁅K'⁆ L :=
  quotientLift _ (FreeLieAlgebra.lift K' (f ∘ generator K A)) (relations_le_ker A f hf)

@[simp] private theorem liftFromGenerators_generator (f : Matrix.ToLieAlgebra K A →+ L)
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) (s : CartanMatrix.Generators ι) :
    liftFromGenerators (K' := K') A f hf (generator K' A s) = f (generator K A s) :=
  FreeLieAlgebra.lift_of_apply _ _

end Lift

private def oneTensor (R S L : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [LieRing L] [LieAlgebra R L] : L →ₗ⁅R⁆ S ⊗[R] L :=
  { TensorProduct.mk R S L 1 with
    map_lie' := by
      intro x y
      change (1 : S) ⊗ₜ[R] ⁅x, y⁆ = ⁅(1 : S) ⊗ₜ[R] x, (1 : S) ⊗ₜ[R] y⁆
      rw [bracket_tmul, one_mul] }

private def extendLieHom {R S L M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M] [LieAlgebra S M]
    [IsScalarTower R S M] (f : L →ₗ⁅R⁆ M) : S ⊗[R] L →ₗ⁅S⁆ M :=
  { f.toLinearMap.liftBaseChange S with
    map_lie' := by
      intro x y
      change f.toLinearMap.liftBaseChange S ⁅x, y⁆ =
        ⁅f.toLinearMap.liftBaseChange S x, f.toLinearMap.liftBaseChange S y⁆
      refine x.inductionOn ?_ ?_
      · intro a x
        refine y.inductionOn ?_ ?_
        · intro b y
          simp [mul_smul, smul_comm a b]
        · intro y z hy hz
          simp [hy, hz]
      · intro x z hx hz
        simp [hx, hz] }

@[simp] private theorem extendLieHom_tmul {R S L M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
    [LieAlgebra S M] [IsScalarTower R S M] (f : L →ₗ⁅R⁆ M) (a : S) (x : L) :
    extendLieHom f (a ⊗ₜ[R] x) = a • f x := rfl

/-- Scalar extension commutes with the Serre presentation. The forward and
inverse maps are fixed by the same labelled generators. -/
theorem serreBaseChange : Specs.RationalRealization.SerreBaseChange.{u} := by
  intro ι _ A
  let Q := Matrix.ToLieAlgebra ℚ A
  let C := Matrix.ToLieAlgebra ℂ A
  let V := ℂ ⊗[ℚ] Q
  let : Module ℚ C := Module.compHom C (algebraMap ℚ ℂ)
  let : LieAlgebra ℚ C :=
    { lie_smul := fun r x y => lie_smul (algebraMap ℚ ℂ r) x y }
  let q : Q →ₗ⁅ℚ⁆ V := oneTensor ℚ ℂ Q
  let f₀ : Q →ₗ⁅ℚ⁆ C := liftFromGenerators A (AddMonoidHom.id C) (fun _ _ => rfl)
  let f : V →ₗ⁅ℂ⁆ C := extendLieHom f₀
  let g : C →ₗ⁅ℂ⁆ V := liftFromGenerators A q.toLinearMap.toAddMonoidHom q.map_lie
  have hf (s : CartanMatrix.Generators ι) :
      f (q (generator ℚ A s)) = generator ℂ A s := by
    change extendLieHom f₀ (1 ⊗ₜ[ℚ] generator ℚ A s) = generator ℂ A s
    rw [extendLieHom_tmul, one_smul]
    exact liftFromGenerators_generator A (AddMonoidHom.id C) _ s
  have hg (s : CartanMatrix.Generators ι) :
      g (generator ℂ A s) = q (generator ℚ A s) :=
    liftFromGenerators_generator A _ _ _
  have hfg : f.comp g = LieHom.id := by
    apply hom_ext A
    intro s
    change f (g (generator ℂ A s)) = generator ℂ A s
    rw [hg, hf]
  let g₀ : C →ₗ⁅ℚ⁆ V :=
    { toFun := fun x => g x
      map_add' := map_add g
      map_smul' := map_rat_smul g.toLinearMap.toAddMonoidHom
      map_lie' := fun {x y} => g.map_lie x y }
  have hgf₀ : g₀.comp f₀ = q := by
    apply hom_ext A
    intro s
    change g (f₀ (generator ℚ A s)) = q (generator ℚ A s)
    exact (congrArg g (liftFromGenerators_generator A _ _ s)).trans (hg s)
  have hgf : ∀ x, g (f x) = x := by
    intro x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro a y
      change g (extendLieHom f₀ (a ⊗ₜ[ℚ] y)) = a ⊗ₜ[ℚ] y
      rw [extendLieHom_tmul, map_smul]
      have hh : g (f₀ y) = 1 ⊗ₜ[ℚ] y := LieHom.congr_fun hgf₀ y
      rw [hh, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  refine ⟨LieEquiv.ofBijective f ⟨Function.LeftInverse.injective hgf, ?_⟩, hf⟩
  intro x
  exact ⟨g x, LieHom.congr_fun hfg x⟩


section WeightBaseChange

variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

private def jointWeightEquations (K : Type*) [Field K] (χ : ι → K) :
    Matrix.ToLieAlgebra K A →ₗ[K] (ι → Matrix.ToLieAlgebra K A) :=
  LinearMap.pi fun i => LieAlgebra.ad K _ (generator K A (.H i)) - χ i • LinearMap.id

private theorem ker_jointWeightEquations (χ : ι → ℚ) :
    (jointWeightEquations A ℚ χ).ker = rationalWeightSpace A χ := by
  ext x
  rw [LinearMap.mem_ker, funext_iff]
  simp only [jointWeightEquations, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LieAlgebra.ad_apply, Pi.zero_apply, sub_eq_zero]
  rfl

private theorem complex_ker_jointWeightEquations (χ : ι → ℂ) :
    (jointWeightEquations A ℂ χ).ker = Serre.weightSpace A χ := by
  ext x
  rw [LinearMap.mem_ker, funext_iff]
  simp only [jointWeightEquations, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LieAlgebra.ad_apply, Pi.zero_apply, sub_eq_zero]
  rfl

end WeightBaseChange

theorem rationalWeightsBaseChange : Specs.RationalRealization.RationalWeightBaseChange.{u} := by
  intro ι _ _ A
  obtain ⟨e, he⟩ := serreBaseChange A
  refine ⟨e, he, fun χ => ?_⟩
  let Q := Matrix.ToLieAlgebra ℚ A
  let : Module ℚ (Serre.Algebra A) := Module.compHom _ (algebraMap ℚ ℂ)
  let p := TensorProduct.piRight ℚ ℂ ℂ (fun _ : ι => Q)
  let j := p.trans (LinearEquiv.piCongrRight fun _ : ι => e.toLinearEquiv)
  let f := jointWeightEquations A ℚ χ
  let g := jointWeightEquations A ℂ (fun i => (χ i : ℂ))
  have hcomp : j.toLinearMap.comp (f.baseChange ℂ) = g.comp e.toLinearEquiv.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    funext i
    change e (a ⊗ₜ[ℚ] (⁅generator ℚ A (.H i), x⁆ - χ i • x)) =
      ⁅generator ℂ A (.H i), e (a ⊗ₜ[ℚ] x)⁆ - (χ i : ℂ) • e (a ⊗ₜ[ℚ] x)
    have hbr : e (a ⊗ₜ[ℚ] ⁅generator ℚ A (.H i), x⁆) =
        ⁅generator ℂ A (.H i), e (a ⊗ₜ[ℚ] x)⁆ := by
      rw [← he, ← e.map_lie, bracket_tmul, one_mul]
    rw [TensorProduct.tmul_sub, map_sub, hbr]
    congr 1
    rw [TensorProduct.tmul_smul, ← map_smul, TensorProduct.smul_tmul']
    exact congrArg (fun c : ℂ => e (c ⊗ₜ[ℚ] x)) (Rat.cast_smul_eq_qsmul ℂ (χ i) a).symm
  have hker : LinearMap.ker (f.baseChange ℂ) = (LinearMap.ker f).baseChange ℂ :=
    Module.Flat.ker_lTensor_eq ℂ ℂ f
  rw [← ker_jointWeightEquations A, ← hker, ← complex_ker_jointWeightEquations A]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hx0 : f.baseChange ℂ x = 0 := LinearMap.mem_ker.mp hx
    calc
      g (e x) = j (f.baseChange ℂ x) := (LinearMap.congr_fun hcomp x).symm
      _ = 0 := by rw [hx0, map_zero]
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, LinearMap.mem_ker.mpr (j.injective ?_), rfl⟩
    have hy0 : g (e x) = 0 := LinearMap.mem_ker.mp hy
    calc
      j (f.baseChange ℂ x) = g (e x) := LinearMap.congr_fun hcomp x
      _ = j 0 := by rw [hy0, map_zero]

section FiniteType

variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

private theorem abelianBracket {x y : Serre.Algebra A}
    (hx : x ∈ Serre.cartan A) (hy : y ∈ Serre.weightSpace A 0) :
    ⁅x, y⁆ = 0 := by
  refine Submodule.span_induction (p := fun x _ => ⁅x, y⁆ = 0) ?_ (by simp)
    (fun x z _ _ hx hz => by simp [hx, hz]) (fun a x _ h => by simp [smul_lie, h]) hx
  rintro _ ⟨i, rfl⟩
  simpa using hy i

private def cartanSubalgebra (hzero : Serre.weightSpace A 0 = Serre.cartan A) :
    LieSubalgebra ℂ (Serre.Algebra A) where
  toSubmodule := Serre.cartan A
  lie_mem' := by
    intro x y hx hy
    rw [abelianBracket A hx (hzero.symm ▸ hy)]
    exact (Serre.cartan A).zero_mem

private theorem cartanSubalgebra_isCartan (hzero : Serre.weightSpace A 0 = Serre.cartan A) :
    (cartanSubalgebra A hzero).IsCartanSubalgebra := by
  classical
  let H := cartanSubalgebra A hzero
  let S := ⨆ χ ∈ {χ : ι → ℂ | χ ≠ 0}, Serre.weightSpace A χ
  have hH : H.toSubmodule = Serre.weightSpace A 0 := hzero.symm
  let : IsLieAbelian H :=
    ⟨fun x y => Subtype.ext (abelianBracket A x.property (hH.symm ▸ y.property))⟩
  refine ⟨inferInstance, le_antisymm ?_ H.le_normalizer⟩
  have htop : H.toSubmodule ⊔ S = ⊤ := by
    apply top_unique
    rw [← Serre.weightSpace_iSup_eq_top A]
    refine iSup_le fun χ => ?_
    rcases eq_or_ne χ 0 with rfl | h
    · exact hH.ge.trans le_sup_left
    · exact (le_iSup₂ (f := fun χ _ => Serre.weightSpace A χ) χ h).trans le_sup_right
  have hdis : Disjoint H.toSubmodule S := by
    rw [hH]
    exact (Serre.weightSpace_iSupIndep A).disjoint_biSup (by simp)
  have hS (i : ι) (x : Serre.Algebra A) (hx : x ∈ S) : ⁅Serre.h A i, x⁆ ∈ S := by
    refine Submodule.iSup_induction _ (motive := fun x => ⁅Serre.h A i, x⁆ ∈ S) hx
      ?_ (by simp) (fun x y hx hy => by simpa only [lie_add] using S.add_mem hx hy)
    intro χ x hx
    refine Submodule.iSup_induction _ (motive := fun x => ⁅Serre.h A i, x⁆ ∈ S) hx
      ?_ (by simp) (fun x y hx hy => by simpa only [lie_add] using S.add_mem hx hy)
    intro h x hx
    rw [show ⁅Serre.h A i, x⁆ = χ i • x from hx i]
    exact S.smul_mem _ (le_iSup₂ (f := fun χ _ => Serre.weightSpace A χ) χ h hx)
  intro x hx
  have hx' : x ∈ H.toSubmodule ⊔ S := by rw [htop]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
  have hz0 : z ∈ Serre.weightSpace A 0 := by
    intro i
    have hi : Serre.h A i ∈ H := Submodule.subset_span (Set.mem_range_self i)
    have hy0 : y ∈ Serre.weightSpace A 0 := hH ▸ hy
    have hyi : ⁅Serre.h A i, y⁆ = 0 := by simpa using hy0 i
    have hzi := (H.mem_normalizer_iff' _).mp hx (Serre.h A i) hi
    rw [lie_add, hyi, zero_add] at hzi
    have heq : ⁅Serre.h A i, z⁆ = 0 :=
      Submodule.disjoint_def.mp hdis _ hzi (hS i z hz)
    simpa using heq
  have hzH : z ∈ H.toSubmodule := hH.symm ▸ hz0
  exact H.add_mem hy hzH

private theorem radical_eq_bot_of_components
    (ha : ∀ i j, i ≠ j → A i j ≤ 0)
    (hs : ∀ c : Serre.Component A, LieAlgebra.IsSimple ℂ (Serre.Algebra (Serre.componentMatrix A c))) :
    LieAlgebra.radical ℂ (Serre.Algebra A) = ⊥ := by
  classical
  have htrivial := LieAlgebra.hasTrivialRadical_of_no_solvable_ideals
    (R := ℂ) (L := Serre.Algebra A) (fun I hI => by
      have hzero (c : Serre.Component A) : I.map (Serre.componentProjection A ha c) = ⊥ := by
        let p := Serre.componentProjection A ha c
        have hp : Function.Surjective p := fun y => ⟨Serre.componentInclusion A ha c y,
          LieHom.congr_fun (Serre.componentProjection_comp_inclusion A ha c) y⟩
        let pI : I →ₗ⁅ℂ⁆ I.map p :=
          { toFun := fun x => ⟨p x, LieIdeal.mem_map (f := p) x.property⟩
            map_add' := fun x y => Subtype.ext (map_add p (x : Serre.Algebra A) (y : Serre.Algebra A))
            map_smul' := fun a x => Subtype.ext (map_smul p a (x : Serre.Algebra A))
            map_lie' := fun {x y} => Subtype.ext (p.map_lie x y) }
        have hpI : Function.Surjective pI := by
          intro y
          obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective (I := I) hp y.property
          exact ⟨x, Subtype.ext hx⟩
        let := hI
        let := hpI.lieAlgebra_isSolvable (f := pI)
        let := hs c
        exact LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable _
      apply le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨y, rfl⟩ := Serre.componentSumHom_surjective A ha x
      have hy : y = 0 := by
        ext c
        rw [← Serre.componentProjection_sum A ha c]
        have hc := LieIdeal.mem_map (f := Serre.componentProjection A ha c) hx
        rw [hzero c, LieSubmodule.mem_bot] at hc
        exact hc
      rw [hy, map_zero]
      exact LieSubmodule.zero_mem _)
  exact htrivial.radical_eq_bot

end FiniteType

/-- Apply the pinned finite-type, triangular and connected-component
theorems to the real span of the specified integral datum. -/
theorem serreStructure : Specs.RationalRealization.SerreStructure.{u} := by
  intro D _
  let : Module.Free ℤ D.X := D.freeX
  let : Module.Free ℤ D.Y := D.freeY
  let : Module.Finite ℤ D.X := D.finiteX
  let : Module.Finite ℤ D.Y := D.finiteY
  let : Finite D.I := D.finiteRoots
  let : D.datum.IsReduced := D.reduced
  let A := RootData.integralCartan D.datum D.base
  change Serre.Triangular A ∧ _
  let R := Set.range (RootData.realRoot D.datum)
  obtain ⟨hinj, _, _, _, _, metric, _, _, _, hR, z, b, hz, _, _, _, hb, hcartan, hweights, _⟩ :=
    RootData.euclideanComparison D.datum D.base
  let : NormedAddCommGroup (RootData.realRootSpan D.datum) := metric.toNormedAddCommGroup
  let : InnerProductSpace ℝ (RootData.realRootSpan D.datum) := InnerProductSpace.ofCore metric.toCore
  have hA (i j : D.base.support) : (A i j : ℝ) = cartanMatrix b i j :=
    (congrArg (fun M => M i j) hcartan).symm
  have htriangle := Serre.triangular_spec R hR z hz b hb A hA
  obtain ⟨hfinite, hspan, hsupport, hrank, hzero, _, hdimension⟩ :=
    Serre.finiteType_spec R hR z hz b hb A hA
  have hroot (j : D.I) :
      Serre.rootWeight b (RootData.realRoot D.datum j) = Specs.RationalRealization.rootWeight D j := by
    funext i
    change ((rootCartan (RootData.realRoot D.datum j) (b i) : ℝ) : ℂ) = _
    rw [show rootCartan (RootData.realRoot D.datum j) (b i) = (D.datum.pairing j i : ℝ) from
      by
        simpa only [rootCartan, coroot, real_inner_smul_right, div_eq_mul_inv,
          mul_assoc, mul_left_comm, mul_comm] using hweights i j]
    exact Complex.ofReal_intCast _
  have hcard : Nat.card R = Nat.card D.I :=
    (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
  rcases serreBaseChange A with ⟨e, _⟩
  have : Module.Finite ℂ (ℂ ⊗[ℚ] Matrix.ToLieAlgebra ℚ A) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have hfiniteQ : Module.Finite ℚ (Matrix.ToLieAlgebra ℚ A) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat ℂ
  have hdimQ : Module.finrank ℚ (Matrix.ToLieAlgebra ℚ A) =
      D.base.support.card + Nat.card D.I := by
    rw [← Module.finrank_baseChange (R := ℂ), e.toLinearEquiv.finrank_eq, hdimension, hcard]
    simp
  have hC := Serre.cartanConditions_spec R hR z hz b hb A hA
  have hrad := radical_eq_bot_of_components A hC.2.1 (Serre.componentSimple_spec R hR z hz b hb A hA)
  refine ⟨htriangle, hfinite, hfiniteQ, hdimQ, hrad, hspan, ?_, ?_,
    cartanSubalgebra A hzero, rfl, hzero, cartanSubalgebra_isCartan A hzero⟩
  · intro χ hχ
    rw [hsupport χ hχ]
    constructor
    · rintro ⟨x, ⟨j, rfl⟩, hx⟩
      exact ⟨j, hx.trans (hroot j)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨RootData.realRoot D.datum j, Set.mem_range_self j, (hroot j).symm⟩
  · intro j
    rw [← hroot j]
    exact hrank _ (Set.mem_range_self j)

open Specs.RationalRealization (rootWeight)

theorem rationalSerreDecomposition : Specs.RationalRealization.RationalSerreDecomposition.{u} := by
  intro D _ A w
  obtain ⟨_, _, _, _, _, hspan, hsupport, hdim, H, hH, hzero, _⟩ := serreStructure D
  obtain ⟨e, he, hweights⟩ := rationalWeightsBaseChange A
  let f := e.toLinearEquiv.toLinearMap
  have hcast (j : D.I) : (fun i => (w j i : ℂ)) = rootWeight D j := by
    funext i
    simp [w, rootWeight]
  have hcastZero : (fun i : D.base.support => ((0 : D.base.support → ℚ) i : ℂ)) = 0 := by
    funext i
    simp
  have hrw (j : D.I) :
      ((rationalWeightSpace A (w j)).baseChange ℂ).map f = Serre.weightSpace A (rootWeight D j) :=
    (hweights (w j)).trans (congrArg (Serre.weightSpace A) (hcast j))
  have hrz : ((rationalWeightSpace A 0).baseChange ℂ).map f = Serre.weightSpace A 0 :=
    (hweights 0).trans (congrArg (Serre.weightSpace A) hcastZero)
  refine ⟨?_, ?_, ?_⟩
  · let S := rationalWeightSpace A 0 ⊔ ⨆ j, rationalWeightSpace A (w j)
    have h : (S.baseChange ℂ).map f = ⊤ := by
      apply top_unique
      rw [← hspan]
      refine iSup_le fun χ => ?_
      rcases eq_or_ne χ 0 with rfl | hχ
      · rw [← hrz]
        exact Submodule.map_mono (Submodule.baseChange_mono ℂ le_sup_left)
      · rcases eq_or_ne (Serre.weightSpace A χ) ⊥ with h | h
        · rw [h]
          exact bot_le
        · obtain ⟨j, rfl⟩ := (hsupport χ hχ).mp h
          rw [← hrw]
          have hle : rationalWeightSpace A (w j) ≤ S :=
            (le_iSup (fun i : D.I => rationalWeightSpace A (w i)) j).trans le_sup_right
          exact Submodule.map_mono (Submodule.baseChange_mono ℂ hle)
    apply Submodule.baseChange_injective (A := ℂ)
    apply Submodule.map_injective_of_injective e.injective
    change (S.baseChange ℂ).map f = ((⊤ : Submodule ℚ _).baseChange ℂ).map f
    rw [h, Submodule.baseChange_top, Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr (show Function.Surjective f from e.surjective)).symm
  · intro j
    let P := rationalWeightSpace A (w j)
    have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ)
      P.subtype P.injective_subtype
    let E := LinearEquiv.ofBijective (P.toBaseChange ℂ)
      ⟨fun _ _ h => hinj (congrArg Subtype.val h), P.toBaseChange_surjective ℂ⟩
    calc
      Module.finrank ℚ P = Module.finrank ℂ (ℂ ⊗[ℚ] P) :=
        Module.finrank_baseChange.symm
      _ = Module.finrank ℂ (P.baseChange ℂ) := E.finrank_eq
      _ = Module.finrank ℂ ((P.baseChange ℂ).map f) :=
        (e.toLinearEquiv.submoduleMap (P.baseChange ℂ)).finrank_eq
      _ = 1 := by rw [hrw, hdim]
  · apply Submodule.baseChange_injective (A := ℂ)
    apply Submodule.map_injective_of_injective e.injective
    change ((rationalWeightSpace A 0).baseChange ℂ).map f =
      ((Submodule.span ℚ (Set.range fun i : D.base.support => generator ℚ A (.H i))).baseChange ℂ).map f
    rw [hrz, hzero, hH, Submodule.baseChange_span, Submodule.map_span]
    apply congrArg (Submodule.span ℂ)
    rw [Set.image_image, ← Set.range_comp]
    exact congrArg Set.range (funext (fun i => (he (.H i)).symm))

section Dominance

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Finite ι]
variable (P : RootDatum ι X Y) [P.IsReduced] (B : P.Base)

private theorem positiveSum_pairing [Fintype ι] [DecidablePred B.IsPos] (i : B.support) :
    P.coroot' i (∑ j : ι with B.IsPos j, P.root j) = 2 := by
  classical
  let s := Finset.univ.filter B.IsPos
  let r := P.reflectionPerm i
  have hi : (i : ι) ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, B.isPos_of_mem_support i.property⟩
  have hs (j : ι) (hj : j ∈ s.erase i.val) : r j ∈ s.erase i.val := by
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    have hjp : B.IsPos j := (Finset.mem_filter.mp hjs).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    · intro heq
      have hneg : P.reflectionPerm i i = j := by
        calc
          r i = r (r j) := congrArg r heq.symm
          _ = j := P.reflectionPerm_self i j
      have hrneg : B.IsPos (P.reflectionPerm i i) ↔ ¬ B.IsPos i :=
        RootPairing.Base.IsPos.neg_iff_not B (i : ι)
      exact hrneg.mp (hneg.symm ▸ hjp) (B.isPos_of_mem_support i.property)
    · exact hjp.reflectionPerm i.property hji
  have hs' (j : ι) : j ∈ s.erase i.val ↔ r j ∈ s.erase i.val := by
    refine ⟨hs j, fun hj => ?_⟩
    simpa only [r, P.reflectionPerm_self] using hs (r j) hj
  have hsum : ∑ j ∈ s.erase i.val, P.pairing j i = 0 := by
    have heq : (∑ j ∈ s.erase i.val, P.pairing j i) =
        ∑ j ∈ s.erase i.val, P.pairing (r j) i :=
      Finset.sum_equiv r hs' (fun j _ => by rw [show r (r j) = j from P.reflectionPerm_self i j])
    -- The summands on the second side are evaluated on the reflected root.
    have hpair (j : ι) : P.pairing (r j) i = -P.pairing j i := by
      rw [← P.pairing_reflectionPerm, P.pairing_reflectionPerm_self_right]
    simp only [hpair, Finset.sum_neg_distrib] at heq
    omega
  change P.coroot' i (∑ j ∈ s, P.root j) = 2
  rw [map_sum]
  change (∑ j ∈ s, P.pairing j i) = 2
  rw [← Finset.sum_erase_add s (fun j => P.pairing j i) hi, hsum, zero_add, P.pairing_same]

private theorem dominantGenerators [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ s : Finset X, (∀ x ∈ s, ∀ i : B.support, 0 ≤ P.coroot' i x) ∧
      Submodule.span ℤ (s : Set X) = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  let ρ := ∑ j : ι with B.IsPos j, P.root j
  let b := Module.finBasis ℤ X
  let m (x : X) : ℤ := ∑ i : B.support, (P.coroot' i x).natAbs
  have hm (x : X) : 0 ≤ m x := Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  let s : Finset X := insert ρ (Finset.univ.image fun j => b j + m (b j) • ρ)
  refine ⟨s, ?_, ?_⟩
  · intro x hx i
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rw [positiveSum_pairing P B i]
      decide
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      rw [map_add, map_zsmul, zsmul_eq_mul, positiveSum_pairing P B i]
      have hle : ((P.coroot' i (b j)).natAbs : ℤ) ≤ m (b j) :=
        Finset.single_le_sum (f := fun i : B.support => ((P.coroot' i (b j)).natAbs : ℤ))
          (fun _ _ => Int.natCast_nonneg _) (Finset.mem_univ i)
      have hneg : - P.coroot' i (b j) ≤ ((P.coroot' i (b j)).natAbs : ℤ) := by
        simpa using (Int.le_natAbs (a := -(P.coroot' i (b j))))
      have := hm (b j)
      simp only [Int.cast_id]
      omega
  · apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    let W := Submodule.span ℤ (s : Set X)
    have hρ : ρ ∈ W := Submodule.subset_span (Finset.mem_insert_self ..)
    have hj : b j + m (b j) • ρ ∈ W := Submodule.subset_span
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    change b j ∈ W
    simpa only [add_sub_cancel_right] using W.sub_mem hj (W.smul_mem (m (b j)) hρ)


end Dominance

theorem dominantCharactersGenerate : Specs.RationalRealization.DominantGenerators.{u} := by
  intro D
  let : Module.Free ℤ D.X := D.freeX
  let : Module.Finite ℤ D.X := D.finiteX
  let : Finite D.I := D.finiteRoots
  let : D.datum.IsReduced := D.reduced
  exact dominantGenerators D.datum D.base

section ComplexCartan

open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open _root_.Specs.LieAlgebrasAndRepresentations.SerreRelations (simple positive)
open _root_.Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open _root_.Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)

private theorem mem_rootSpace_iff_serre {ι : Type*} [DecidableEq ι]
    {A : Matrix ι ι ℤ} {H : LieSubalgebra ℂ (Serre.Algebra A)} (c : Module.Basis ι ℂ H)
    (hc : ∀ i, (c i : Serre.Algebra A) = Serre.h A i)
    (α : Module.Dual ℂ H) (x : Serre.Algebra A) :
    x ∈ rootSpace_value H α ↔ x ∈ Serre.weightSpace A (fun i => α (c i)) := by
  rw [LieAlgebrasAndRepresentations.mem_rootSpace H α x]
  constructor
  · intro hx i
    simpa only [hc] using hx (c i)
  · intro hx
    let f : H →ₗ[ℂ] Serre.Algebra A :=
      { toFun := fun y => ⁅(y : Serre.Algebra A), x⁆
        map_add' := fun y z => add_lie (y : Serre.Algebra A) (z : Serre.Algebra A) x
        map_smul' := fun r y => smul_lie r (y : Serre.Algebra A) x }
    have heq : f = α.smulRight x := c.ext (fun i => by
      change ⁅(c i : Serre.Algebra A), x⁆ = α (c i) • x
      rw [hc]
      exact hx i)
    exact LinearMap.congr_fun heq

private def realRootToCartanDual {ι V L : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [LieRing L] [LieAlgebra ℂ L] {H : LieSubalgebra ℂ L}
    (b : Module.Basis ι ℝ V) (c : Module.Basis ι ℂ H) : V →ₗ[ℝ] Module.Dual ℂ H where
  toFun v := c.constr ℂ (Serre.rootWeight b v)
  map_add' x y := by
    apply c.ext
    intro i
    simp only [LinearMap.add_apply, Module.Basis.constr_basis, Serre.rootWeight,
      rootCartan, inner_add_left, mul_add, add_div, Complex.ofReal_add]
  map_smul' r x := by
    apply c.ext
    intro i
    simp only [LinearMap.smul_apply, Module.Basis.constr_basis, Serre.rootWeight, rootCartan,
      real_inner_smul_left, ← mul_assoc, mul_left_comm (2 : ℝ) r, mul_div_assoc,
      Complex.ofReal_mul, Complex.real_smul]
    rfl

private theorem serre_coroot_eq {ι : Type*} [DecidableEq ι] {A : Matrix ι ι ℤ}
    [Module.Finite ℂ (Serre.Algebra A)] {H : LieSubalgebra ℂ (Serre.Algebra A)}
    [H.IsCartanSubalgebra] (hss : IsSemisimple ℂ (Serre.Algebra A))
    (c : Module.Basis ι ℂ H) (hc : ∀ i, (c i : Serre.Algebra A) = Serre.h A i)
    (i : ι) (α : Module.Dual ℂ H) (hα : α (c i) = 2)
    (he : Serre.e A i ∈ rootSpace_value H α) (hf : Serre.f A i ∈ rootSpace_value H (-α)) :
    killingCoroot H α = c i := by
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  have hb := opposite_root_bracket hss H hH α (Serre.e A i) (Serre.f A i) he hf
  rw [Serre.ef, ite_eq_left rfl, ← hc] at hb
  let q := LieAlgebrasAndRepresentations.killingForm ℂ (Serre.Algebra A) (Serre.e A i) (Serre.f A i)
  have hci : c i = q • tAlpha H α := Subtype.ext hb
  have ht := congrArg α hci
  rw [hα, map_smul, smul_eq_mul, ← rootForm_eq_apply hss H hH] at ht
  have hnon : rootForm H α α ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at ht
    exact (by norm_num : (2 : ℂ) ≠ 0) ht
  calc
    killingCoroot H α = (2 / rootForm H α α) • tAlpha H α := rfl
    _ = q • tAlpha H α := congrArg (fun a : ℂ => a • tAlpha H α)
      ((div_eq_iff hnon).mpr ht)
    _ = c i := hci.symm

/-- Identify the actual positive and simple roots of the complex Serre algebra,
including the Killing-normalized coroots of the simple triples. -/
theorem complexCartan : Specs.RationalRealization.ComplexCartan.{u} := by
  intro D _
  let A := RootData.integralCartan D.datum D.base
  let : Finite D.I := D.finiteRoots
  let : Module.Free ℤ D.X := D.freeX
  let : Module.Free ℤ D.Y := D.freeY
  let : Module.Finite ℤ D.X := D.finiteX
  let : Module.Finite ℤ D.Y := D.finiteY
  let : D.datum.IsReduced := D.reduced
  let R := Set.range (RootData.realRoot D.datum)
  obtain ⟨htri, hfinite, _, _, hss, _, hsupport, _, H, hH, _, hCartan⟩ := serreStructure D
  let := hfinite
  let := hCartan
  obtain ⟨c₀, hc₀⟩ := htri.2.1
  let c := c₀.map (LinearEquiv.ofEq _ _ hH.symm)
  have hc (i : D.base.support) : (c i : Serre.Algebra A) = Serre.h A i := hc₀ i
  obtain ⟨_, _, _, _, _, metric, _, _, _, hR, z, b, hz, hheight, _, hbroot, hb, _, hw, _⟩ :=
    RootData.euclideanComparison D.datum D.base
  let : NormedAddCommGroup (RootData.realRootSpan D.datum) := metric.toNormedAddCommGroup
  let : InnerProductSpace ℝ (RootData.realRootSpan D.datum) := InnerProductSpace.ofCore metric.toCore
  let F := realRootToCartanDual b c
  have hF : Function.Injective F := (c.constr ℂ).injective.comp (Serre.rootWeight_injective b)
  have hFroot (j : D.I) :
      F (RootData.realRoot D.datum j) = c.constr ℂ (rootWeight D j) := by
    apply c.ext
    intro i
    simp only [F, realRootToCartanDual, LinearMap.coe_mk, AddHom.coe_mk,
      Module.Basis.constr_basis, Serre.rootWeight, rootWeight]
    have h : rootCartan (RootData.realRoot D.datum j) (b i) = (D.datum.pairing j i : ℝ) := by
      simpa only [rootCartan, coroot, real_inner_smul_right, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using hw i j
    rw [h, Complex.ofReal_intCast]
  have hspace (α : Module.Dual ℂ H) :
      rootSpace_value H α = Serre.weightSpace A (fun i => α (c i)) := by
    ext x
    exact mem_rootSpace_iff_serre c hc α x
  have hne (α : Module.Dual ℂ H) : α ≠ 0 ↔ (fun i => α (c i)) ≠ 0 :=
    ⟨fun h he => h (c.ext fun i => congrFun he i), fun h he => h (by rw [he]; rfl)⟩
  have hroots : F '' R = rootSet_value H := by
    ext α
    change α ∈ F '' R ↔ α ≠ 0 ∧ rootSpace_value H α ≠ ⊥
    rw [hspace, hne]
    constructor
    · rintro ⟨a, ⟨j, rfl⟩, rfl⟩
      rw [hFroot]
      simp only [Module.Basis.constr_basis]
      have hj : rootWeight D j ≠ 0 := by
        intro he
        have h := hFroot j
        rw [he, map_zero] at h
        exact hR.nonzero _ (Set.mem_range_self j) (hF (h.trans (map_zero F).symm))
      exact ⟨hj, (hsupport _ hj).mpr ⟨j, rfl⟩⟩
    · rintro ⟨hα, hw⟩
      obtain ⟨j, hj⟩ := (hsupport _ hα).mp hw
      exact ⟨RootData.realRoot D.datum j, Set.mem_range_self j,
        (hFroot j).trans (c.ext fun i => (c.constr_basis ℂ _ i).trans (congrFun hj i).symm)⟩
  let φ : Direction H := (innerₗ (RootData.realRootSpan D.datum) z).comp F.leftInverse
  have hφ (a : RootData.realRootSpan D.datum) : φ (F a) = inner ℝ z a := by
    change inner ℝ z (F.leftInverse (F a)) = _
    rw [F.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hF)]
  have hreg : Regular H φ := by
    intro α hα
    rw [← hroots] at hα
    obtain ⟨a, ha, rfl⟩ := hα
    rw [hφ]
    exact hz a ha
  have hpos : F '' positiveRoots R z = positive H φ := by
    ext α
    change α ∈ F '' positiveRoots R z ↔ α ∈ rootSet_value H ∧ 0 < φ α
    rw [← hroots]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha.1, rfl⟩, (hφ a).symm ▸ ha.2⟩
    · rintro ⟨⟨a, ha, rfl⟩, hp⟩
      exact ⟨a, ⟨ha, (hφ a) ▸ hp⟩, rfl⟩
  have hsimple : F '' simpleRoots R z = simple H φ := by
    ext α
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hpos ▸ ⟨a, ha.1, rfl⟩, ?_⟩
      intro β hβ γ hγ h
      rw [← hpos] at hβ hγ
      obtain ⟨x, hx, rfl⟩ := hβ
      obtain ⟨y, hy, rfl⟩ := hγ
      exact ha.2 x hx y hy (hF (h.trans (map_add F x y).symm))
    · intro ha
      have hp := ha.1
      rw [← hpos] at hp
      obtain ⟨a, ha₀, rfl⟩ := hp
      refine ⟨a, ⟨ha₀, ?_⟩, rfl⟩
      intro x hx y hy h
      exact ha.2 _ (hpos ▸ ⟨x, hx, rfl⟩) _ (hpos ▸ ⟨y, hy, rfl⟩)
        ((congrArg F h).trans (map_add F x y))
  have hsimpleRange : Set.range (fun i : D.base.support => F (b i)) = simple H φ := by
    rw [← hsimple, ← hb, ← Set.range_comp']
  let simpleIndex : D.base.support ≃ simple H φ :=
    Equiv.ofBijective (fun i => ⟨F (b i), hsimpleRange ▸ Set.mem_range_self i⟩) (by
      constructor
      · intro i j h
        exact b.injective (hF (congrArg Subtype.val h))
      · intro a
        obtain ⟨i, hi⟩ := show a.val ∈ Set.range (fun i : D.base.support => F (b i)) from
          hsimpleRange.symm ▸ a.property
        exact ⟨i, Subtype.ext hi⟩)
  have his (i : D.base.support) : (simpleIndex i).val = c.constr ℂ (rootWeight D i) :=
    (congrArg F (hbroot i)).trans (hFroot i)
  refine ⟨⟨hfinite, H, hCartan, c, hc, φ, hreg, ?_, ?_, simpleIndex, his, ?_⟩⟩
  · rw [← hroots, ← Set.range_comp']
    exact congrArg Set.range (funext fun j => (hFroot j).symm)
  · intro j
    rw [← hFroot, hφ, hheight]
  · intro a
    obtain ⟨i, rfl⟩ := simpleIndex.surjective a
    simp only [Equiv.symm_apply_apply]
    have hweight (j : D.base.support) : (simpleIndex i).val (c j) = (A j i : ℂ) := by
      rw [his, Module.Basis.constr_basis]
      rfl
    have he : Serre.e A i ∈ rootSpace_value H (simpleIndex i).val := by
      rw [hspace]
      intro j
      change ⁅Serre.h A j, Serre.e A i⁆ = (simpleIndex i).val (c j) • Serre.e A i
      rw [hweight, Serre.he, Int.cast_smul_eq_zsmul]
    have hf : Serre.f A i ∈ rootSpace_value H (- (simpleIndex i).val) := by
      rw [hspace]
      intro j
      change ⁅Serre.h A j, Serre.f A i⁆ = (-(simpleIndex i).val) (c j) • Serre.f A i
      rw [LinearMap.neg_apply, hweight, Serre.hf, neg_smul, Int.cast_smul_eq_zsmul]
    have hii : A i i = 2 := D.datum.pairing_same i
    have hα : (simpleIndex i).val (c i) = 2 := by rw [hweight, hii]; norm_num
    refine ⟨he, hf, (htri.2.2.2.2 i).1, (htri.2.2.2.2 i).2.1, ?_⟩
    change ⁅Serre.e A i, Serre.f A i⁆ = (killingCoroot H (simpleIndex i).val : Serre.Algebra A)
    rw [serre_coroot_eq hss c hc i _ hα he hf, hc, Serre.ef, ite_eq_left rfl]


set_option maxHeartbeats 750000 in
/-- The respective root strings have the same endpoints, which determine
the pairings with the Killing-normalized coroot. -/
theorem complexCorootPairings : Specs.RationalRealization.ComplexCorootPairings.{u} := by
  intro D _ C i j
  let : Finite D.I := D.finiteRoots
  let : Module.Free ℤ D.X := D.freeX
  let : Module.Free ℤ D.Y := D.freeY
  let : Module.Finite ℤ D.X := D.finiteX
  let : Module.Finite ℤ D.Y := D.finiteY
  let : D.datum.IsReduced := D.reduced
  let := C.finite
  let := C.isCartan
  let H := C.cartan
  let f (i : D.I) : Module.Dual ℂ H := C.cartanBasis.constr ℂ (rootWeight D i)
  change f j (killingCoroot H (f i)) = _
  have hss := (serreStructure D).2.2.2.2.1
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  have hf (i : D.I) : f i ∈ rootSet_value H := C.roots_eq ▸ Set.mem_range_self i
  have hself : f i (killingCoroot H (f i)) = 2 := by
    rw [killingCoroot_pairing hss H hH, mul_div_cancel_right₀]
    exact rootForm_self_ne_zero hss H hH _ (hf i)
  rcases eq_or_ne j i with rfl | hji
  · rw [hself, RootPairing.pairing_same]
    norm_num
  · obtain ⟨_, _, _, _, _, metric, _, _, _, _, _, b, _, _, _, _, _, _, hw, _⟩ :=
      RootData.euclideanComparison D.datum D.base
    let E := RootData.realRootSpan D.datum
    let : NormedAddCommGroup E := metric.toNormedAddCommGroup
    let : InnerProductSpace ℝ E := InnerProductSpace.ofCore metric.toCore
    let F := realRootToCartanDual b C.cartanBasis
    have hF : Function.Injective F :=
      (C.cartanBasis.constr ℂ).injective.comp (Serre.rootWeight_injective b)
    let e : D.X →ₗ[ℤ] ℝ ⊗[ℤ] D.X := TensorProduct.mk ℤ ℝ D.X 1
    have he : Function.Injective e := Module.Flat.tensorProduct_mk_injective ℤ D.X ℝ
    have hFroot (l : D.I) : F (RootData.realRoot D.datum l) = f l := by
      apply C.cartanBasis.ext
      intro s
      simp only [F, realRootToCartanDual, LinearMap.coe_mk, AddHom.coe_mk,
        f, Module.Basis.constr_basis, Serre.rootWeight, rootWeight]
      have hh : rootCartan (RootData.realRoot D.datum l) (b s) = (D.datum.pairing l s : ℝ) := by
        simpa only [rootCartan, coroot, real_inner_smul_right, div_eq_mul_inv,
          mul_assoc, mul_left_comm, mul_comm] using hw s l
      rw [hh, Complex.ofReal_intCast]
    have hsum (n : ℤ) (l : D.I) : D.datum.root l = D.datum.root j + n • D.datum.root i ↔
        f l = f j + n • f i := by
      rw [← hFroot l, ← hFroot j, ← hFroot i, ← map_zsmul F, ← F.map_add, hF.eq_iff]
      constructor
      · intro eh
        apply Subtype.ext
        change e (D.datum.root l) = e (D.datum.root j) + n • e (D.datum.root i)
        rw [eh, map_add, map_zsmul]
      · intro eh
        apply he
        rw [map_add, map_zsmul]
        exact congrArg Subtype.val eh
    have hinj : Function.Injective f := by
      intro a b eq
      apply D.datum.root.injective
      apply he
      have hreal : RootData.realRoot D.datum a = RootData.realRoot D.datum b :=
        hF ((hFroot a).trans (eq.trans (hFroot b).symm))
      exact congrArg Subtype.val hreal
    have hneg : f j = -f i ↔ D.datum.root j = -D.datum.root i := by
      rw [← hFroot j, ← hFroot i, ← F.map_neg, hF.eq_iff]
      constructor
      · intro h
        apply he
        rw [map_neg]
        exact congrArg Subtype.val h
      · intro h
        apply Subtype.ext
        change e (D.datum.root j) = -e (D.datum.root i)
        rw [h, map_neg]
    by_cases hopen : D.datum.root j = -D.datum.root i
    · rw [hneg.mpr hopen, LinearMap.neg_apply, hself]
      have hh : D.datum.pairing j i = -2 := by
        rw [← RootPairing.root_coroot'_eq_pairing, hopen, map_neg,
          RootPairing.root_coroot'_eq_pairing, RootPairing.pairing_same]
      rw [hh]
      norm_num
    have hLi' : LinearIndependent ℤ ![D.datum.root i, D.datum.root j] :=
      RootPairing.IsReduced.linearIndependent D.datum hji.symm (by
        intro h
        exact hopen (by rw [h, neg_neg]))
    obtain ⟨p, q, hc, hs⟩ := LieAlgebrasAndRepresentations.RootStrings.root_string hss H hH (f i) (f j) (hf i) (hf j)
      (hinj.ne hji) (fun h => hopen (hneg.mp h))
    let b := D.datum.chainBotCoeff i j
    let a := D.datum.chainTopCoeff i j
    have hinterval (n : ℤ) :
        (-(b : ℤ) ≤ n ∧ n ≤ (a : ℤ)) ↔ (-(p : ℤ) ≤ n ∧ n ≤ (q : ℤ)) := by
      rw [← Set.mem_Icc, ← D.datum.root_add_zsmul_mem_range_iff hLi', ← hs]
      change _ ↔ f j + n • f i ∈ rootSet_value C.cartan
      rw [← C.roots_eq]
      exact ⟨fun ⟨l, hl⟩ => ⟨l, (hsum n l).mp hl⟩, fun ⟨l, hl⟩ => ⟨l, (hsum n l).mpr hl⟩⟩
    have hb : b = p := by
      have h₁ := ((hinterval (-(b : ℤ))).mp ⟨le_rfl, by omega⟩).1
      have h₂ := ((hinterval (-(p : ℤ))).mpr ⟨le_rfl, by omega⟩).1
      omega
    have ha : a = q := by
      have h₁ := ((hinterval (a : ℤ)).mp ⟨by omega, le_rfl⟩).2
      have h₂ := ((hinterval (q : ℤ)).mpr ⟨by omega, le_rfl⟩).2
      omega
    have hpair := D.datum.chainBotCoeff_sub_chainTopCoeff hLi'
    change (b : ℤ) - (a : ℤ) = _ at hpair
    rw [hb, ha] at hpair
    have hp' : D.datum.pairingIn ℤ j i = D.datum.pairing j i := by
      simpa using (D.datum.algebraMap_pairingIn ℤ j i)
    rw [hp'] at hpair
    rw [hc]
    exact_mod_cast hpair

set_option maxHeartbeats 850000 in
theorem oppositeRationalRootBracket : Specs.RationalRealization.OppositeRationalRootBracket.{u} := by
  intro D _ i A W W' x hx y hy hx0 hy0
  let L := Matrix.ToLieAlgebra ℚ A
  let j := D.datum.reflectionPerm i i
  have hp (s : D.base.support) : D.datum.pairing j s = -D.datum.pairing i s :=
    D.datum.pairing_reflectionPerm_self_left i s
  constructor
  · intro s
    rw [leibniz_lie, hx s, hy s]
    change ⁅(D.datum.pairing i s : ℚ) • x, y⁆ + ⁅x, (D.datum.pairing j s : ℚ) • y⁆ = _
    rw [hp, Int.cast_neg, lie_smul, smul_lie, neg_smul, add_neg_cancel]
    exact (zero_smul ℚ _).symm
  · intro hxy
    obtain ⟨e, he⟩ := serreBaseChange A
    obtain ⟨C⟩ := complexCartan D
    let := C.finite
    let := C.isCartan
    have hss : IsSemisimple ℂ (Serre.Algebra A) := (serreStructure D).2.2.2.2.1
    have htoral := RealRootSpace.cartan_isMaximalToral hss C.cartan
    let α := C.cartanBasis.constr ℂ (rootWeight D i)
    have hα : α ∈ rootSet_value C.cartan := C.roots_eq ▸ Set.mem_range_self i
    let : Module ℚ (Serre.Algebra A) := Module.compHom _ (algebraMap ℚ ℂ)
    let : IsScalarTower ℚ ℂ (Serre.Algebra A) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let a : L →ₗ[ℚ] Serre.Algebra A :=
      (e.toLinearEquiv.toLinearMap.restrictScalars ℚ).comp (TensorProduct.mk ℚ ℂ L 1)
    have hinj : Function.Injective a := e.injective.comp (Module.Flat.tensorProduct_mk_injective ℚ L ℂ)
    have hbr (l m : L) : a ⁅l, m⁆ = ⁅a l, a m⁆ := by
      change e (1 ⊗ₜ[ℚ] ⁅l, m⁆) = ⁅e (1 ⊗ₜ[ℚ] l), e (1 ⊗ₜ[ℚ] m)⁆
      rw [← e.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, mul_one]
    have hm (r : ℚ) (m : L) : a (r • m) = (r : ℂ) • a m := a.map_smul r m
    have ha : a x ∈ rootSpace_value C.cartan α := by
      apply (mem_rootSpace_iff_serre C.cartanBasis C.cartanBasis_eq α _).mpr
      intro s
      have hs : Serre.h A s = a (generator ℚ A (.H s)) := (he (.H s)).symm
      change ⁅Serre.h A s, a x⁆ = α (C.cartanBasis s) • a x
      rw [hs, ← hbr, hx s, hm, Module.Basis.constr_basis]
      rfl
    have hb : a y ∈ rootSpace_value C.cartan (-α) := by
      apply (mem_rootSpace_iff_serre C.cartanBasis C.cartanBasis_eq (-α) _).mpr
      intro s
      have hs : Serre.h A s = a (generator ℚ A (.H s)) := (he (.H s)).symm
      change ⁅Serre.h A s, a y⁆ = (-α) (C.cartanBasis s) • a y
      rw [hs, ← hbr, hy s, hm, LinearMap.neg_apply, Module.Basis.constr_basis]
      change ((D.datum.pairing j s : ℚ) : ℂ) • a y = -(D.datum.pairing i s : ℂ) • a y
      rw [hp]
      push_cast
      rfl
    obtain ⟨b, c, hb', hc', hb0, hc0, hbc, hcb, _⟩ :=
      exists_root_triple hss C.cartan htoral α hα
    have hαneg : -α ∈ rootSet_value C.cartan := by
      rw [← C.roots_eq]
      refine ⟨j, ?_⟩
      apply C.cartanBasis.ext
      intro s
      change C.cartanBasis.constr ℂ (rootWeight D j) (C.cartanBasis s) = (-α) (C.cartanBasis s)
      rw [LinearMap.neg_apply, Module.Basis.constr_basis]
      change (D.datum.pairing j s : ℂ) = -C.cartanBasis.constr ℂ (rootWeight D i) (C.cartanBasis s)
      rw [Module.Basis.constr_basis, hp, Int.cast_neg]
      rfl
    have hmem {z : L} (h : z ≠ 0) : a z ≠ 0 :=
      fun hz => h (hinj (hz.trans a.map_zero.symm))
    obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one
      (finrank_rootSpace_eq_one hss C.cartan htoral α hα)
      (show (⟨a x, ha⟩ : rootSpace_value C.cartan α) ≠ 0 from fun h => hmem hx0 (congrArg Subtype.val h))
      (⟨b, hb'⟩ : rootSpace_value C.cartan α)
    obtain ⟨s, hs⟩ := exists_smul_eq_of_finrank_eq_one
      (finrank_rootSpace_eq_one hss C.cartan htoral (-α) hαneg)
      (show (⟨a y, hb⟩ : rootSpace_value C.cartan (-α)) ≠ 0 from fun h => hmem hy0 (congrArg Subtype.val h))
      (⟨c, hc'⟩ : rootSpace_value C.cartan (-α))
    have hr' : r • a x = b := congrArg Subtype.val hr
    have hs' : s • a y = c := congrArg Subtype.val hs
    have hz : ⁅a x, a y⁆ = 0 := by rw [← hbr, hxy, map_zero]
    have hzero : (killingCoroot C.cartan α : Serre.Algebra A) = 0 := by
      rw [← hbc, ← hr', ← hs', smul_lie, lie_smul, hz, smul_zero, smul_zero]
    rw [hzero, zero_lie] at hcb
    exact hb0 ((smul_eq_zero.mp hcb.symm).resolve_left (by norm_num))

open Specs.RationalRealization (rationalCharacter)
open private rootSet_spans rootSet_separates from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace

set_option maxHeartbeats 950000 in
/-- The bracket of opposite rational root lines determines the coroot line
in the marked full rational cocharacter space. -/
theorem rationalCorootBracket : Specs.RationalRealization.RationalCorootBracket.{u} := by
  classical
  intro D _ A L H Z e he i x y hx hy hx₀ hy₀
  let : Module.Free ℤ D.Y := D.freeY
  choose hGen hGen_val hGen_image using he
  have hspan : Submodule.span ℚ (Set.range hGen) = ⊤ := by
    apply Submodule.map_injective_of_injective H.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    change Submodule.span ℚ (Set.range fun j => (hGen j).val) = H
    rw [show (fun j => (hGen j).val) = (fun j => generator ℚ A (.H j)) from funext hGen_val]
    exact (rationalSerreDecomposition D).2.2.symm
  let jH : H →ₗ[ℚ] H × Z := (LinearMap.id (R := ℚ) (M := H)).prod 0
  let l := e.toLinearMap.comp jH
  let t : D.Y →ₗ[ℤ] ℚ ⊗[ℤ] D.Y := TensorProduct.mk ℤ ℚ D.Y 1
  have hu : t (D.datum.coroot i) ∈ LinearMap.range l := by
    have hs := D.base.coroot_mem_span_int i
    refine Submodule.span_induction (p := fun y _ => t y ∈ LinearMap.range l) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨hGen ⟨s, hs⟩, hGen_image ⟨s, hs⟩⟩
    · rw [t.map_zero]
      exact (LinearMap.range l).zero_mem
    · intro a b _ _ ha hb
      rw [t.map_add]
      exact (LinearMap.range l).add_mem ha hb
    · intro n a _ ha
      rw [t.map_smul]
      simpa only [Int.cast_smul_eq_zsmul] using (LinearMap.range l).smul_mem (n : ℚ) ha
  obtain ⟨v, hv⟩ := hu
  obtain ⟨lift, hlift⟩ := serreBaseChange A
  obtain ⟨C⟩ := complexCartan D
  let := C.finite
  let := C.isCartan
  let L' := Serre.Algebra A
  let : Module ℚ L' := Module.compHom L' (algebraMap ℚ ℂ)
  let : IsScalarTower ℚ ℂ L' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let H' := C.cartan
  let a : L →ₗ[ℚ] L' :=
    (lift.toLinearEquiv.toLinearMap.restrictScalars ℚ).comp (TensorProduct.mk ℚ ℂ L 1)
  have ha : Function.Injective a :=
    lift.injective.comp (Module.Flat.tensorProduct_mk_injective ℚ L ℂ)
  have hbr (x y : L) : a ⁅x, y⁆ = ⁅a x, a y⁆ := by
    change lift (1 ⊗ₜ[ℚ] ⁅x, y⁆) = ⁅lift (1 ⊗ₜ[ℚ] x), lift (1 ⊗ₜ[ℚ] y)⁆
    rw [← lift.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, mul_one]
  have ha_smul (q : ℚ) (z : L) : a (q • z) = (q : ℂ) • a z := a.map_smul q z
  have haGen (s : D.base.support) : a (hGen s).val = (C.cartanBasis s : L') := by
    rw [hGen_val, C.cartanBasis_eq]
    exact hlift (.H s)
  have ha_mem (h : H) : a h.val ∈ H' := by
    have he : h ∈ Submodule.span ℚ (Set.range hGen) := hspan.symm ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun h _ => a h.val ∈ H') ?_ ?_ ?_ ?_ he
    · rintro _ ⟨s, rfl⟩
      rw [haGen]
      exact (C.cartanBasis s).property
    · rw [Submodule.coe_zero, map_zero]
      exact H'.zero_mem
    · intro a₁ a₂ _ _ h₁ h₂
      rw [Submodule.coe_add, map_add]
      exact H'.add_mem h₁ h₂
    · intro q h _ hh
      rw [Submodule.coe_smul, ha_smul]
      exact H'.smul_mem (q : ℂ) hh
  let : Module ℚ H' := Module.compHom H' (algebraMap ℚ ℂ)
  let : IsScalarTower ℚ ℂ H' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let aH : H →ₗ[ℚ] H' :=
    { toFun := fun h => ⟨a h.val, ha_mem h⟩
      map_add' := fun _ _ => Subtype.ext (a.map_add _ _)
      map_smul' := fun q h => Subtype.ext (ha_smul q h) }
  let α (i : D.I) := C.cartanBasis.constr ℂ (rootWeight D i)
  have heval (j : D.I) (h : H) :
      α j (aH h) = (rationalCharacter D (D.datum.root j) (l h) : ℂ) := by
    let m₁ := ((α j).restrictScalars ℚ).comp aH
    let m₂ := (Algebra.linearMap ℚ ℂ).comp ((rationalCharacter D (D.datum.root j)).comp l)
    have hm : m₁ = m₂ := by
      apply LinearMap.ext_on hspan
      rintro _ ⟨s, rfl⟩
      change α j (aH (hGen s)) = (rationalCharacter D (D.datum.root j) (l (hGen s)) : ℂ)
      have h₁ : aH (hGen s) = C.cartanBasis s := Subtype.ext (haGen s)
      have h₂ : l (hGen s) = 1 ⊗ₜ[ℤ] D.datum.coroot s := hGen_image s
      rw [h₁, h₂]
      change C.cartanBasis.constr ℂ (rootWeight D j) (C.cartanBasis s) =
        ((RootData.extendFunctional ℚ (D.datum.toLinearMap (D.datum.root j))
          (1 ⊗ₜ[ℤ] D.datum.coroot s)) : ℂ)
      rw [Module.Basis.constr_basis, RootData.extendFunctional_one_tmul, Rat.cast_intCast]
      rfl
    exact DFunLike.congr_fun hm h
  have hss := (serreStructure D).2.2.2.2.1
  have htoral := RealRootSpace.cartan_isMaximalToral hss H'
  have hα : α i ∈ rootSet_value H' := C.roots_eq ▸ Set.mem_range_self i
  have hmatch : aH v = killingCoroot H' (α i) := by
    apply eq_of_sub_eq_zero
    apply rootSet_separates (rootSet_spans hss htoral)
    intro β hβ
    change β ∈ rootSet_value H' at hβ
    rw [← C.roots_eq] at hβ
    obtain ⟨j, rfl⟩ := hβ
    change α j (aH v - killingCoroot H' (α i)) = 0
    rw [map_sub, heval, hv, complexCorootPairings D C i j]
    change ((RootData.extendFunctional ℚ (D.datum.toLinearMap (D.datum.root j))
      (1 ⊗ₜ[ℤ] D.datum.coroot i)) : ℂ) - _ = 0
    rw [RootData.extendFunctional_one_tmul, Rat.cast_intCast]
    exact sub_self _
  have ha_root : a x ∈ rootSpace_value H' (α i) := by
    apply (mem_rootSpace_iff_serre C.cartanBasis C.cartanBasis_eq _ _).mpr
    intro s
    have hs : Serre.h A s = a (generator ℚ A (.H s)) := (hlift (.H s)).symm
    change ⁅Serre.h A s, a x⁆ = (α i) (C.cartanBasis s) • a x
    rw [hs, ← hbr, hx s, ha_smul]
    change ((D.datum.pairing i s : ℚ) : ℂ) • a x =
      C.cartanBasis.constr ℂ (rootWeight D i) (C.cartanBasis s) • a x
    rw [Module.Basis.constr_basis]
    simp only [rootWeight, Rat.cast_intCast]
  have ha_neg : a y ∈ rootSpace_value H' (-α i) := by
    apply (mem_rootSpace_iff_serre C.cartanBasis C.cartanBasis_eq _ _).mpr
    intro s
    have hs : Serre.h A s = a (generator ℚ A (.H s)) := (hlift (.H s)).symm
    change ⁅Serre.h A s, a y⁆ = (-α i) (C.cartanBasis s) • a y
    rw [hs, ← hbr, hy s, ha_smul, LinearMap.neg_apply]
    change ((D.datum.pairing (D.datum.reflectionPerm i i) s : ℚ) : ℂ) • a y =
      -(C.cartanBasis.constr ℂ (rootWeight D i) (C.cartanBasis s)) • a y
    rw [Module.Basis.constr_basis, D.datum.pairing_reflectionPerm_self_left i s]
    simp only [rootWeight, Int.cast_neg, Rat.cast_neg, Rat.cast_intCast]
  obtain ⟨hb, hb₀⟩ := oppositeRationalRootBracket D i x hx y hy hx₀ hy₀
  let h : H := ⟨⁅x, y⁆, hb⟩
  have ht := rootForm_self_ne_zero hss H' htoral _ hα
  let q := LieAlgebrasAndRepresentations.killingForm ℂ L' (a x) (a y) *
    rootForm H' (α i) (α i) / 2
  have hq : aH h = q • aH v := by
    rw [hmatch, killingCoroot_eq, smul_smul]
    have hcoef : q * (2 / rootForm H' (α i) (α i)) =
        LieAlgebrasAndRepresentations.killingForm ℂ L' (a x) (a y) := by
      dsimp only [q]
      field_simp
    rw [hcoef]
    apply Subtype.ext
    change a ⁅x, y⁆ = _
    rw [hbr]
    exact opposite_root_bracket hss H' htoral _ _ _ ha_root ha_neg
  let r : ℚ := rationalCharacter D (D.datum.root i) (l h) / 2
  have hv₂ : α i (aH v) = 2 := by
    rw [hmatch, killingCoroot_pairing hss H' htoral, mul_div_cancel_right₀ _ ht]
  have hr : (r : ℂ) = q := by
    simp only [r, Rat.cast_div, Rat.cast_ofNat]
    rw [← heval, hq, map_smul, hv₂, smul_eq_mul, mul_div_cancel_right₀]
    norm_num
  have hh : h = r • v := by
    apply Subtype.ext
    apply ha
    change (aH h : L') = a (r • v.val)
    rw [ha_smul, hr, hq]
    rfl
  have hr₀ : r ≠ 0 := by
    intro hzero
    apply hb₀
    exact congrArg Subtype.val (by simpa only [hzero, zero_smul] using hh)
  refine ⟨h, r, hr₀, rfl, ?_⟩
  change l h = r • t (D.datum.coroot i)
  rw [hh, l.map_smul, hv]

end ComplexCartan

section HighestWeightModules

attribute [local instance 100] LieRing.ofAssociativeRing

open UniversalEnvelopingAlgebra (ι)

open _root_.Shared.Lie (representationEquiv)

open Specs.RationalRealization (CartanIdentification CyclicPresentation cyclicVector cyclicRepresentation
  cyclicLieRingModule cyclicLieModule extendedCyclicLieRingModule extendedCyclicLieModule
  highestRelations serreHighestRelations loweringWeight loweringWord RationalHighestWeight
  RationalWeightWords RationalWeightBasis)

attribute [local instance] cyclicLieRingModule cyclicLieModule

variable {R S L L' W : Type*} [Field R] [Field S] [Algebra R S]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra S L']
  [AddCommGroup W] [Module S W] [LieRingModule L' W] [LieModule S L' W]

private theorem cyclicRepresentation_lift (s : Set (UniversalEnvelopingAlgebra R L)) :
    representationEquiv R L (CyclicPresentation s) (cyclicRepresentation s) =
      Algebra.lsmul R R (CyclicPresentation s) := by
  exact (representationEquiv R L (CyclicPresentation s)).apply_symm_apply
    (Algebra.lsmul R R (CyclicPresentation s))

variable (e : (S ⊗[R] L) ≃ₗ⁅S⁆ L')
variable [Module R W] [IsScalarTower R S W]

private def restrictRepresentation : L →ₗ⁅R⁆ Module.End R W where
  toFun x := (LieModule.toEnd S L' W (e (1 ⊗ₜ[R] x))).restrictScalars R
  map_add' x y := by
    ext w
    simp [TensorProduct.tmul_add]
  map_smul' r x := by
    ext w
    change ⁅e (1 ⊗ₜ[R] (r • x)), w⁆ = r • ⁅e (1 ⊗ₜ[R] x), w⁆
    rw [TensorProduct.tmul_smul, ← algebraMap_smul S r (1 ⊗ₜ[R] x),
      map_smul, smul_lie, algebraMap_smul S]
  map_lie' := by
    intro x y
    ext w
    change ⁅e (1 ⊗ₜ[R] ⁅x,y⁆), w⁆ = ⁅e (1 ⊗ₜ[R] x), ⁅e (1 ⊗ₜ[R] y), w⁆⁆ -
      ⁅e (1 ⊗ₜ[R] y), ⁅e (1 ⊗ₜ[R] x), w⁆⁆
    have hxy : (1 : S) ⊗ₜ[R] ⁅x, y⁆ = ⁅(1 : S) ⊗ₜ[R] x, (1 : S) ⊗ₜ[R] y⁆ := by
      rw [bracket_tmul, one_mul]
    rw [hxy, e.map_lie, lie_lie]

private theorem cyclicBaseChange_presentation (s : Set (UniversalEnvelopingAlgebra R L))
    (w : W)
    (h : ∀ a ∈ s, representationEquiv R L W (restrictRepresentation e) a w = 0) :
    let := extendedCyclicLieRingModule e s
    letI := extendedCyclicLieModule e s
    ∃! f : (S ⊗[R] CyclicPresentation s) →ₗ⁅S,L'⁆ W, f (1 ⊗ₜ[R] cyclicVector s) = w := by
  let := extendedCyclicLieRingModule e s
  let := extendedCyclicLieModule e s
  let U := UniversalEnvelopingAlgebra R L
  let Q := CyclicPresentation s
  let p := Submodule.span U s
  let ρ : L →ₗ⁅R⁆ Module.End R W := restrictRepresentation e
  let a := representationEquiv R L W ρ
  let : Module U W := _root_.Shared.Lie.actionModule R L W a
  let := _root_.Shared.Lie.action_tower R L W a
  let ev : U →ₗ[U] W := LinearMap.id.smulRight w
  have hker : p ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    intro u hu
    exact h u hu
  let f₀ : Q →ₗ[R] W := (p.liftQ ev hker).restrictScalars R
  have hf₀ (x : L) (v : Q) : f₀ ⁅x,v⁆ = ρ x (f₀ v) := by
    change (p.liftQ ev hker) ((ι R x : U) • v) = _
    rw [map_smul]
    change a (ι R x) (f₀ v) = _
    rw [show a (ι R x) = ρ x from UniversalEnvelopingAlgebra.lift_ι_apply R ρ x]
  let f : (S ⊗[R] Q) →ₗ⁅S,L'⁆ W :=
    { f₀.liftBaseChange S with
      map_lie' := by
        intro x v
        obtain ⟨x, rfl⟩ := e.surjective x
        change f₀.liftBaseChange S ⁅e.symm (e x), v⁆ = ⁅e x, f₀.liftBaseChange S v⁆
        rw [e.symm_apply_apply]
        induction x using TensorProduct.inductionOn with
        | tmul b x =>
          induction v using TensorProduct.inductionOn with
          | tmul c v =>
            rw [bracket_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, hf₀]
            have he : e (b ⊗ₜ[R] x) = b • e (1 ⊗ₜ[R] x) := by
              rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            rw [he, smul_lie, lie_smul, smul_smul]
            rfl
          | add v z hv hz => rw [lie_add, map_add, hv, hz, map_add, lie_add]
        | add x z hx hz => rw [add_lie x z v, map_add, hx, hz, map_add, add_lie] }
  have hf : f (1 ⊗ₜ[R] cyclicVector s) = w := by
    change f₀.liftBaseChange S _ = _
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    change ev 1 = w
    exact one_smul U w
  refine ⟨f, hf, ?_⟩
  intro g hg
  let g₀ : Q →ₗ[R] W := (g.toLinearMap.restrictScalars R).comp (TensorProduct.mk R S Q 1)
  have hg₀ : ∀ x v, g₀ (cyclicRepresentation s x v) = ρ x (g₀ v) := by
    intro x v
    have H := g.map_lie (e (1 ⊗ₜ[R] x)) (1 ⊗ₜ[R] v)
    change g ⁅e.symm (e (1 ⊗ₜ[R] x)), 1 ⊗ₜ[R] v⁆ = _
      at H
    rw [e.symm_apply_apply, bracket_tmul, one_mul] at H
    exact H
  have hgU := (_root_.Shared.Lie.morphism_correspondence R L Q W
    (cyclicRepresentation s) ρ g₀).mpr hg₀
  have hgQ : g₀ = f₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := p.mkQ_surjective v
    have hh := hgU u (cyclicVector s)
    have hg₁ : g₀ (cyclicVector s) = w := hg
    rw [cyclicRepresentation_lift, hg₁] at hh
    change g₀ (u • cyclicVector s) = a u w at hh
    change g₀ (p.mkQ u) = a u w
    have hs : u • cyclicVector s = p.mkQ u := by
      rw [cyclicVector, ← p.mkQ.map_smul, smul_eq_mul, mul_one]
    rwa [hs] at hh
  apply LieModuleHom.ext
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul b v =>
    change g (b ⊗ₜ[R] v) = f₀.liftBaseChange S (b ⊗ₜ[R] v)
    rw [LinearMap.liftBaseChange_tmul, ← hgQ]
    change g (b ⊗ₜ[R] v) = b • g (1 ⊗ₜ[R] v)
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add v z hv hz => rw [map_add, map_add, hv, hz]

open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules
  (Direction U borel_value induced_value IsWeightCharacter)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
  (inducedLieRingModule inducedLieModule)
open _root_.Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
  (coroots IsDominant Normalized simpleCoordinate)
open _root_.Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open _root_.Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
  (simpleQuotient_value quotientHighestVector)

open Specs.Pinning (BasedRootDatum)

local instance {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    {H : LieSubalgebra ℂ L} {φ : Direction H} {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) :=
  inducedLieRingModule H φ χ

local instance {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    {H : LieSubalgebra ℂ L} {φ : Direction H} {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) :=
  inducedLieModule H φ χ

private theorem highestRelations_iff {L L' W J : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing L'] [LieAlgebra ℂ L']
    [AddCommGroup W] [Module ℂ W] [LieRingModule L' W] [LieModule ℂ L' W]
    [Module ℚ W] [IsScalarTower ℚ ℂ W]
    (e : (ℂ ⊗[ℚ] L) ≃ₗ⁅ℂ⁆ L') (E F H : J → L) (m : J → ℤ) (w : W) :
    (∀ a ∈ highestRelations E F H m, representationEquiv ℚ L W (restrictRepresentation e) a w = 0) ↔
      (∀ i, ⁅e (1 ⊗ₜ[ℚ] E i), w⁆ = 0) ∧
      (∀ i, ⁅e (1 ⊗ₜ[ℚ] H i), w⁆ = (m i : ℂ) • w) ∧
      (∀ i, (LieModule.toEnd ℂ L' W (e (1 ⊗ₜ[ℚ] F i)) ^ ((m i).toNat + 1)) w = 0) := by
  have power (x : L) (n : ℕ) (v : W) :
      (restrictRepresentation e x ^ n) v =
        (LieModule.toEnd ℂ L' W (e (1 ⊗ₜ[ℚ] x)) ^ n) v := by
    induction n generalizing v with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  simp only [highestRelations, Set.forall_mem_union, Set.forall_mem_range]
  change ((∀ i, UniversalEnvelopingAlgebra.lift ℚ (restrictRepresentation e) (ι ℚ (E i)) w = 0) ∧
    (∀ i, UniversalEnvelopingAlgebra.lift ℚ (restrictRepresentation e)
      (ι ℚ (H i) - algebraMap ℚ _ (m i : ℚ)) w = 0) ∧
    (∀ i, UniversalEnvelopingAlgebra.lift ℚ (restrictRepresentation e)
      (ι ℚ (F i) ^ ((m i).toNat + 1)) w = 0)) ↔ _
  simp only [map_sub, LinearMap.sub_apply, AlgHom.commutes, Module.algebraMap_end_apply, map_pow,
    UniversalEnvelopingAlgebra.lift_ι_apply, power, sub_eq_zero]
  simp [restrictRepresentation, ← algebraMap_smul ℂ (m _ : ℚ) w]

private theorem cyclicVector_killed {R L : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    {s : Set (UniversalEnvelopingAlgebra R L)} {a : UniversalEnvelopingAlgebra R L}
    (ha : a ∈ s) : a • cyclicVector s = 0 := by
  change a • (Submodule.span (UniversalEnvelopingAlgebra R L) s).mkQ 1 = 0
  rw [← map_smul, smul_eq_mul, mul_one]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ha)

private theorem extendedCyclic_relations {L L' : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing L'] [LieAlgebra ℂ L']
    (e : (ℂ ⊗[ℚ] L) ≃ₗ⁅ℂ⁆ L') (s : Set (UniversalEnvelopingAlgebra ℚ L)) :
    letI := extendedCyclicLieRingModule e s
    letI := extendedCyclicLieModule e s
    ∀ a ∈ s, representationEquiv ℚ L (ℂ ⊗[ℚ] CyclicPresentation s)
      (restrictRepresentation e) a (1 ⊗ₜ[ℚ] cyclicVector s) = 0 := by
  let := extendedCyclicLieRingModule e s
  let := extendedCyclicLieModule e s
  let Q := CyclicPresentation s
  let T := ℂ ⊗[ℚ] Q
  let f : Q →ₗ[ℚ] T := TensorProduct.mk ℚ ℂ Q 1
  have hf (x : L) (v : Q) :
      f (cyclicRepresentation s x v) = restrictRepresentation (W := T) e x (f v) := by
    change (1 : ℂ) ⊗ₜ[ℚ] ⁅x,v⁆ = ⁅e.symm (e (1 ⊗ₜ[ℚ] x)), (1 : ℂ) ⊗ₜ[ℚ] v⁆
    rw [e.symm_apply_apply, bracket_tmul, one_mul]
  intro a ha
  have heq := (_root_.Shared.Lie.morphism_correspondence ℚ L Q T (cyclicRepresentation s)
    (restrictRepresentation e) f).mpr hf a (cyclicVector s)
  rw [cyclicRepresentation_lift] at heq
  have hzero : a • cyclicVector s = 0 := cyclicVector_killed ha
  change f (a • cyclicVector s) = _ at heq
  rw [hzero, map_zero] at heq
  exact heq.symm

/-- Compare the two cyclic presentations on their specified highest vectors. -/
theorem rationalHighestWeight : RationalHighestWeight.{u} := by
  intro D _ weight hdom
  let A := RootData.integralCartan D.datum D.base
  let L := Matrix.ToLieAlgebra ℚ A
  let L' := Serre.Algebra A
  let s := serreHighestRelations D weight
  let m (i : D.base.support) := D.datum.coroot' i weight
  obtain ⟨e, he⟩ := serreBaseChange A
  obtain ⟨C⟩ := complexCartan D
  let := C.finite
  let := C.isCartan
  let H := C.cartan
  let φ := C.direction
  let complexWeight := C.cartanBasis.constr ℂ (fun i => (m i : ℂ))
  let E (i : simple H φ) := Serre.e A (C.simpleIndex.symm i)
  let F (i : simple H φ) := Serre.f A (C.simpleIndex.symm i)
  have hnorm : Normalized H φ E F := C.normalized
  have hcoroot (i : D.base.support) : coroots H φ (C.simpleIndex i) = C.cartanBasis i := by
    apply Subtype.ext
    have h := (hnorm (C.simpleIndex i)).2.2.2.2
    simpa only [E, F, Equiv.symm_apply_apply, Serre.ef, ite_true, C.cartanBasis_eq] using h.symm
  have hweight (i : D.base.support) : complexWeight (C.cartanBasis i) = ((m i).toNat : ℂ) := by
    rw [Module.Basis.constr_basis, ← Int.cast_natCast, Int.toNat_of_nonneg (hdom i)]
  have hd : IsDominant H φ complexWeight := by
    intro i
    obtain ⟨j, rfl⟩ := C.simpleIndex.surjective i
    exact ⟨(m j).toNat, (congrArg complexWeight (hcoroot j)).trans (hweight j)⟩
  have hcoord (i : D.base.support) :
      simpleCoordinate H φ hd (C.simpleIndex i) = (m i).toNat := by
    apply Nat.cast_injective (R := ℂ)
    exact (IntegrableHighestWeightQuotient.simpleCoordinate_eq H φ hd (C.simpleIndex i)).symm.trans
      ((congrArg complexWeight (hcoroot i)).trans (hweight i))
  have hss : IsSemisimple ℂ L' := (serreStructure D).2.2.2.2.1
  obtain ⟨χ, hχ, hfinite, _⟩ :=
    HighestWeightClassification.dominant_has_simple_quotient hss H φ C.regular complexWeight hd
  let V := simpleQuotient_value H φ χ
  let v : V := quotientHighestVector H φ χ
  let T := ℂ ⊗[ℚ] CyclicPresentation s
  let t : T := 1 ⊗ₜ[ℚ] cyclicVector s
  let := extendedCyclicLieRingModule e s
  let := extendedCyclicLieModule e s
  let : Module ℚ V := Module.compHom V (algebraMap ℚ ℂ)
  let : IsScalarTower ℚ ℂ V := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨hv, hvf, hsimple⟩ :=
    HighestWeightClassification.defining_relations.{u,u} hss H φ C.regular complexWeight χ hχ hd E F hnorm
  have liftPresentation (W : Type u) [AddCommGroup W] [Module ℂ W]
      [LieRingModule L' W] [LieModule ℂ L' W] [Module ℚ W] [IsScalarTower ℚ ℂ W] (w : W) :
      (∀ a ∈ s, representationEquiv ℚ L W (restrictRepresentation e) a w = 0) ↔
      (∀ h : H, ⁅(h : L'), w⁆ = complexWeight h • w) ∧
        (∀ i, ⁅E i, w⁆ = 0) ∧
        (∀ i, (LieModule.toEnd ℂ L' W (F i) ^ (simpleCoordinate H φ hd i + 1)) w = 0) := by
    have h := highestRelations_iff e (fun i => generator ℚ A (.E i))
      (fun i => generator ℚ A (.F i)) (fun i => generator ℚ A (.H i)) m w
    simp only [he] at h
    rw [show s = highestRelations (fun i => generator ℚ A (.E i))
      (fun i => generator ℚ A (.F i)) (fun i => generator ℚ A (.H i)) m from rfl, h]
    have hE (i : D.base.support) : E (C.simpleIndex i) = generator ℂ A (.E i) := by
      simp only [E, Equiv.symm_apply_apply]
      rfl
    have hF (i : D.base.support) : F (C.simpleIndex i) = generator ℂ A (.F i) := by
      simp only [F, Equiv.symm_apply_apply]
      rfl
    have hH (i : D.base.support) : (C.cartanBasis i : L') = generator ℂ A (.H i) :=
      C.cartanBasis_eq i
    constructor
    · intro ⟨heq, hh, hfq⟩
      refine ⟨?_, ?_, ?_⟩
      · let act : H →ₗ[ℂ] W :=
          { toFun := fun h => ⁅(h : L'), w⁆
            map_add' := fun x y => add_lie (x : L') (y : L') w
            map_smul' := fun a x => smul_lie a (x : L') w }
        have heqH : act = complexWeight.smulRight w := C.cartanBasis.ext (fun i => by
          change ⁅(C.cartanBasis i : L'), w⁆ = complexWeight (C.cartanBasis i) • w
          rw [hH, Module.Basis.constr_basis]
          exact hh i)
        exact LinearMap.congr_fun heqH
      · intro i
        obtain ⟨j, rfl⟩ := C.simpleIndex.surjective i
        rw [hE]
        exact heq j
      · intro i
        obtain ⟨j, rfl⟩ := C.simpleIndex.surjective i
        rw [hF, hcoord]
        exact hfq j
    · intro ⟨hh, heq, hfq⟩
      refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
      · rw [← hE]
        exact heq (C.simpleIndex i)
      · rw [← hH, hh, Module.Basis.constr_basis]
      · rw [← hF, ← hcoord]
        exact hfq (C.simpleIndex i)
  have hV := (liftPresentation V v).mpr ⟨hv.2.1, hv.2.2.1, hvf⟩
  have hT := (liftPresentation T t).mp (extendedCyclic_relations e s)
  have hfwd := cyclicBaseChange_presentation e s v hV
  have hback := hsimple T t hT.1 hT.2.1 hT.2.2
  obtain ⟨f, hf, _⟩ := hfwd
  obtain ⟨g, hg, _⟩ := hback
  have hleft : g.comp f = LieModuleHom.id :=
    (cyclicBaseChange_presentation e s t (extendedCyclic_relations e s)).unique
      (by rwa [LieModuleHom.comp_apply, hf]) rfl
  have hright : f.comp g = LieModuleHom.id :=
    (hsimple V v hv.2.1 hv.2.2.1 hvf).unique
      (by rwa [LieModuleHom.comp_apply, hg]) rfl
  let iso : T ≃ₗ⁅ℂ,L'⁆ V :=
    { __ := f
      invFun := g
      left_inv := fun x => LieModuleHom.congr_fun hleft x
      right_inv := fun x => LieModuleHom.congr_fun hright x }
  have : Module.Finite ℂ T := by
    let := hfinite
    exact Module.Finite.equiv iso.toLinearEquiv.symm
  have hrat : Module.Finite ℚ (CyclicPresentation s) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat ℂ
  have hn : cyclicVector s ≠ 0 := by
    intro hz
    apply hv.1
    change f (1 ⊗ₜ[ℚ] cyclicVector s) = v at hf
    rw [hz, TensorProduct.tmul_zero, map_zero] at hf
    exact hf.symm
  exact ⟨e, he, C, χ, hχ, iso, hf, hrat, hn⟩

private theorem rationalSerre_brackets {J : Type u} [DecidableEq J] (A : Matrix J J ℤ) :
    (∀ i j, ⁅generator ℚ A (.H i), generator ℚ A (.F j)⁆ = -(A i j • generator ℚ A (.F j))) ∧
    (∀ i j, ⁅generator ℚ A (.E i), generator ℚ A (.F j)⁆ =
      if i = j then generator ℚ A (.H i) else 0) := by
  obtain ⟨e, he⟩ := serreBaseChange A
  let L := Matrix.ToLieAlgebra ℚ A
  let j := oneTensor ℚ ℂ L
  let a := e.toLinearEquiv.toLinearMap.toAddMonoidHom.comp j.toLinearMap.toAddMonoidHom
  have haLie (x y : L) : a ⁅x, y⁆ = ⁅a x, a y⁆ :=
    (congrArg e (j.map_lie x y)).trans (e.map_lie (j x) (j y))
  have ha : Function.Injective a := e.injective.comp
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := ℚ) (B := ℂ) L)
  have h (s : CartanMatrix.Generators J) : a (generator ℚ A s) = generator ℂ A s := he s
  constructor
  · intro i j
    apply ha
    rw [haLie, map_neg, map_zsmul, h, h]
    exact Serre.hf A i j
  · intro i j
    apply ha
    rw [haLie, h, h]
    have hb : ⁅generator ℂ A (.E i), generator ℂ A (.F j)⁆ =
        if i = j then generator ℂ A (.H i) else 0 := Serre.ef A i j
    by_cases hij : i = j <;> simpa only [hij, ite_true, ite_false, h, map_zero] using hb

private theorem eq_top_of_serreGenerators {J : Type u} [DecidableEq J] (A : Matrix J J ℤ)
    (K : LieSubalgebra ℚ (Matrix.ToLieAlgebra ℚ A))
    (h : ∀ s, generator ℚ A s ∈ K) : K = ⊤ := by
  let L := Matrix.ToLieAlgebra ℚ A
  let f : FreeLieAlgebra ℚ (CartanMatrix.Generators J) →ₗ⁅ℚ⁆ K :=
    FreeLieAlgebra.lift ℚ fun s => ⟨generator ℚ A s, h s⟩
  have hcomp : K.incl.comp f = serreProjection ℚ A :=
    FreeLieAlgebra.hom_ext (fun s => by
      change (f (FreeLieAlgebra.of ℚ s) : L) = generator ℚ A s
      exact congrArg Subtype.val (FreeLieAlgebra.lift_of_apply _ _))
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ : ∃ y, serreProjection ℚ A y = x := Quot.mk_surjective x
  rw [← LieHom.congr_fun hcomp y]
  exact (f y).property

/-- The rational module is spanned by lowering words with their integral weights. -/
theorem rationalWeightWords : RationalWeightWords.{u} := by
  intro D _ weight
  let A := RootData.integralCartan D.datum D.base
  let L := Matrix.ToLieAlgebra ℚ A
  let s := serreHighestRelations D weight
  let Q := CyclicPresentation s
  let q := cyclicVector s
  let E (i : D.base.support) := generator ℚ A (.E i)
  let F (i : D.base.support) := generator ℚ A (.F i)
  let H (i : D.base.support) := generator ℚ A (.H i)
  let v := loweringWord D weight
  let μ := loweringWeight D weight
  have hvnil : v [] = q := rfl
  have hvcons (j : D.base.support) (w : List D.base.support) : v (j :: w) = ⁅F j, v w⁆ := rfl
  have hEq (i : D.base.support) : ⁅E i, q⁆ = 0 :=
    cyclicVector_killed (show ι ℚ (E i) ∈ s from
      Or.inl (Set.mem_range_self i))
  have hHq (i : D.base.support) : ⁅H i, q⁆ = (D.datum.coroot' i weight : ℚ) • q := by
    let z := ι ℚ (H i) - algebraMap ℚ (UniversalEnvelopingAlgebra ℚ L) (D.datum.coroot' i weight : ℚ)
    have h := cyclicVector_killed (show z ∈ s from Or.inr (Or.inl (Set.mem_range_self i)))
    dsimp only [z] at h
    rw [sub_smul, algebraMap_smul] at h
    exact sub_eq_zero.mp h
  obtain ⟨hHF, hEF⟩ := rationalSerre_brackets A
  have hweight (w : List D.base.support) (i : D.base.support) :
      ⁅H i, v w⁆ = (D.datum.coroot' i (μ w) : ℚ) • v w := by
    induction w with
    | nil =>
      change ⁅H i, q⁆ = (D.datum.coroot' i (weight - 0) : ℚ) • q
      rw [sub_zero]
      exact hHq i
    | cons j w ih =>
      have hc : (D.datum.coroot' i (μ (j :: w)) : ℚ) =
          (D.datum.coroot' i (μ w) : ℚ) - (A i j : ℚ) := by
        change ((D.datum.coroot' i) (weight - (D.datum.root j + (w.map fun k => D.datum.root k).sum)) :
          ℚ) = _
        simp only [μ, loweringWeight, map_sub, map_add, Int.cast_sub, Int.cast_add]
        change _ = _ - (D.datum.coroot' i (D.datum.root j) : ℚ)
        abel
      have hbr : ⁅H i, F j⁆ = -(A i j • F j) := hHF i j
      rw [hvcons, leibniz_lie, hbr, ih, lie_smul, neg_lie, zsmul_lie, hc, sub_smul,
        Int.cast_smul_eq_zsmul]
      exact sub_eq_neg_add _ _ |>.symm
  refine ⟨hweight, ?_⟩
  let W : Submodule ℚ Q := Submodule.span ℚ (Set.range v)
  have hmem (w : List D.base.support) : v w ∈ W := Submodule.subset_span (Set.mem_range_self w)
  have hF (i : D.base.support) (x : Q) (hx : x ∈ W) : ⁅F i, x⁆ ∈ W := by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hmem (i :: w)
    | zero => simp
    | add x y _ _ hx hy => exact lie_add (F i) x y ▸ W.add_mem hx hy
    | smul a x _ hx => exact lie_smul a (F i) x ▸ W.smul_mem a hx
  have hH (i : D.base.support) (x : Q) (hx : x ∈ W) : ⁅H i, x⁆ ∈ W := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      rw [hweight]
      exact W.smul_mem _ (hmem w)
    | zero => simp
    | add x y _ _ hx hy => exact lie_add (H i) x y ▸ W.add_mem hx hy
    | smul a x _ hx => exact lie_smul a (H i) x ▸ W.smul_mem a hx
  have hEword (i : D.base.support) (w : List D.base.support) : ⁅E i, v w⁆ ∈ W := by
    induction w with
    | nil => rw [hvnil, hEq]; exact W.zero_mem
    | cons j w ih =>
      have hbr : ⁅E i, F j⁆ = if i = j then H i else 0 := hEF i j
      rw [hvcons, leibniz_lie, hbr]
      apply W.add_mem _ (hF j _ ih)
      split
      · exact hH i _ (hmem w)
      · simp
  have hE (i : D.base.support) (x : Q) (hx : x ∈ W) : ⁅E i, x⁆ ∈ W := by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hEword i w
    | zero => simp
    | add x y _ _ hx hy => exact lie_add (E i) x y ▸ W.add_mem hx hy
    | smul a x _ hx => exact lie_smul a (E i) x ▸ W.smul_mem a hx
  let K : LieSubalgebra ℚ L :=
    { carrier := {x | ∀ y ∈ W, ⁅x,y⁆ ∈ W}
      zero_mem' := by intro y _; rw [zero_lie]; exact W.zero_mem
      add_mem' := by intro a b ha hb y hy; rw [add_lie]; exact W.add_mem (ha y hy) (hb y hy)
      smul_mem' := by intro r a ha y hy; rw [smul_lie]; exact W.smul_mem r (ha y hy)
      lie_mem' := by
        intro a b ha hb y hy
        rw [lie_lie]
        exact W.sub_mem (ha _ (hb y hy)) (hb _ (ha y hy)) }
  have hK : K = ⊤ := eq_top_of_serreGenerators A K (by
    intro x
    cases x with
    | E i => exact hE i
    | F i => exact hF i
    | H i => exact hH i)
  have stable (x : L) (y : Q) (hy : y ∈ W) : ⁅x,y⁆ ∈ W := by
    have hx : x ∈ K := hK.symm ▸ LieSubalgebra.mem_top x
    exact hx y hy
  have stableU (a : UniversalEnvelopingAlgebra ℚ L) (y : Q) (hy : y ∈ W) : a • y ∈ W := by
    induction a using _root_.Shared.Lie.enveloping_induction ℚ L generalizing y with
    | scalar r => rw [algebraMap_smul]; exact W.smul_mem r hy
    | generator x => exact stable x y hy
    | mul a b ha hb => rw [mul_smul]; exact ha _ (hb _ hy)
    | add a b ha hb => rw [add_smul]; exact W.add_mem (ha _ hy) (hb _ hy)
  apply top_unique
  intro x _
  obtain ⟨a, rfl⟩ := (Submodule.span (UniversalEnvelopingAlgebra ℚ L) s).mkQ_surjective x
  have hq : q ∈ W := hmem []
  have ha := stableU a q hq
  change a • (Submodule.span (UniversalEnvelopingAlgebra ℚ L) s).mkQ 1 ∈ W at ha
  rwa [← (Submodule.span (UniversalEnvelopingAlgebra ℚ L) s).mkQ.map_smul, smul_eq_mul, mul_one] at ha

/-- Choose a finite weight basis containing the highest vector. -/
theorem rationalWeightBasis : RationalWeightBasis.{u} := by
  classical
  intro D _ weight hdom
  let s := serreHighestRelations D weight
  let Q := CyclicPresentation s
  let q := cyclicVector s
  let v := loweringWord D weight
  obtain ⟨_, _, _, _, _, _, _, hfinite, hq⟩ := rationalHighestWeight D weight hdom
  let : Module.Finite ℚ Q := hfinite
  have hl : LinearIndepOn ℚ id ({q} : Set Q) := (linearIndepOn_singleton_iff ℚ).mpr hq
  have hi : ({q} : Set Q) ⊆ Set.range v := Set.singleton_subset_iff.mpr ⟨[], rfl⟩
  have hspan : ⊤ ≤ Submodule.span ℚ (Set.range v) := ((rationalWeightWords D weight).2).ge
  let b := Module.Basis.extendLe hl hi hspan
  let jtype := hl.extend hi
  let : Finite jtype := Module.Finite.finite_basis b
  let : Fintype jtype := Fintype.ofFinite jtype
  let b' := b.reindex (Fintype.equivFin jtype)
  have hb' (i : Fin (Fintype.card jtype)) : b' i ∈ Set.range v :=
    Module.Basis.extendLe_subset hl hi hspan
      ⟨(Fintype.equivFin jtype).symm i, (Module.Basis.reindex_apply _ _ _).symm⟩
  have hbq : q ∈ Set.range b' := by
    obtain ⟨i, hi⟩ := Module.Basis.subset_extendLe hl hi hspan (Set.mem_singleton q)
    exact ⟨Fintype.equivFin jtype i, by rw [Module.Basis.reindex_apply,
      Equiv.symm_apply_apply, hi]⟩
  let w (i : Fin (Fintype.card jtype)) : List D.base.support :=
    if b' i = q then [] else Classical.choose (hb' i)
  refine ⟨_, b', w, ?_, ?_⟩
  · intro i
    change b' i = v (if b' i = q then [] else Classical.choose (hb' i))
    by_cases h : b' i = q
    · rw [ite_eq_left h, h]
      rfl
    · rw [ite_eq_right h]
      exact (Classical.choose_spec (hb' i)).symm
  · obtain ⟨i, hi⟩ := hbq
    exact ⟨i, ite_eq_left hi⟩

open Specs.RationalRealization (DominantWeightFamily rationalCharacter RationalCentralAction)
open RootData (integralCartan rationalRootAnnihilator extendFunctional)

theorem dominantWeightFamily : DominantWeightFamily.{u} := by
  classical
  intro D _
  obtain ⟨s, hdom, hspan⟩ := dominantCharactersGenerate D
  have hex (x : s) := rationalWeightBasis D (x : D.X) (hdom _ x.property)
  choose n b words hwords hhighest using hex
  let v : (Σ x : s, Fin (n x)) → List D.base.support := fun i => words i.1 i.2
  refine ⟨s, n, b, v, fun x => hdom _ x.property, hwords, ?_⟩
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨j, hj⟩ := hhighest ⟨x, hx⟩
  apply Submodule.subset_span
  refine ⟨⟨⟨x, hx⟩, j⟩, ?_⟩
  change loweringWeight D x (words ⟨x, hx⟩ j) = x
  rw [hj]
  change x - 0 = x
  exact sub_zero x

private theorem rationalCharacter_add (D : BasedRootDatum.{u}) (x y : D.X) :
    rationalCharacter D (x + y) = rationalCharacter D x + rationalCharacter D y := by
  simp [rationalCharacter, extendFunctional, LinearMap.baseChange_add, LinearMap.comp_add]

private theorem rationalCharacter_lowering (D : BasedRootDatum.{u}) (x : D.X)
    (w : List D.base.support) (z : rationalRootAnnihilator D.datum) :
    rationalCharacter D (loweringWeight D x w) z = rationalCharacter D x z := by
  induction w with
  | nil => simp [loweringWeight]
  | cons i w ih =>
    have hz : rationalCharacter D (D.datum.root i) z = 0 := by
      have h' : z.val ∈ ⨅ j : D.I, (extendFunctional ℚ (D.datum.root' j)).ker := z.property
      have h := (Submodule.mem_iInf _).mp h' i.val
      exact h
    have he : loweringWeight D x (i :: w) + D.datum.root i = loweringWeight D x w := by
      change (x - (D.datum.root i + (w.map fun k => D.datum.root k).sum)) + D.datum.root i =
        x - (w.map fun k => D.datum.root k).sum
      abel
    have h := DFunLike.congr_fun (rationalCharacter_add D (loweringWeight D x (i :: w)) (D.datum.root i)) z.val
    have h' : rationalCharacter D (loweringWeight D x w) z =
        rationalCharacter D (loweringWeight D x (i :: w)) z := by
      rw [he] at h
      simpa only [LinearMap.add_apply, hz, add_zero] using h
    exact h'.symm.trans ih

theorem rationalCentralAction : RationalCentralAction.{u} := by
  intro D _ weight
  let A := integralCartan D.datum D.base
  let L := Matrix.ToLieAlgebra ℚ A
  let Z := rationalRootAnnihilator D.datum
  let s := serreHighestRelations D weight
  let V := CyclicPresentation s
  let f := cyclicRepresentation s
  let c : Z →ₗ[ℚ] Module.End ℚ V :=
    (Algebra.linearMap ℚ _).comp ((rationalCharacter D weight).comp Z.subtype)
  let ρ := f.toLinearMap.coprod c
  have hρ (x : L × Z) : ρ x = f x.1 + algebraMap ℚ (Module.End ℚ V) (rationalCharacter D weight x.2) := rfl
  have hcentral (z : Z) (u : Module.End ℚ V) :
      ⁅algebraMap ℚ (Module.End ℚ V) (rationalCharacter D weight z), u⁆ = 0 :=
    sub_eq_zero.mpr (Algebra.commute_algebraMap_left _ _).eq
  have hcentral' (u : Module.End ℚ V) (z : Z) :
      ⁅u, algebraMap ℚ (Module.End ℚ V) (rationalCharacter D weight z)⁆ = 0 := by
    rw [← lie_skew u, hcentral, neg_zero]
  have hzero (z : Z) (v : V) : ρ (0, z) v = rationalCharacter D weight z • v := by
    rw [hρ]
    simp only [map_zero, zero_add]
    exact Module.algebraMap_end_apply ℚ ℚ V _ _
  refine ⟨ρ, ?_, ?_, hzero, ?_⟩
  · intro x y
    rw [hρ x, hρ y, hρ]
    simp only [Submodule.coe_zero, map_zero, add_zero, add_lie, lie_add, hcentral, hcentral']
    exact f.map_lie _ _
  · intro x
    rw [hρ]
    simp only [Submodule.coe_zero, map_zero, add_zero]
    rfl
  · intro w z
    rw [hzero, rationalCharacter_lowering]

end HighestWeightModules

set_option maxHeartbeats 450000 in
theorem rationalCartanLattice : Specs.RationalRealization.RationalCartanLattice.{u} := by
  intro D _
  let A := RootData.integralCartan D.datum D.base
  let L := Matrix.ToLieAlgebra ℚ A
  let L' := Serre.Algebra A
  let Z := RootData.rationalRootAnnihilator D.datum
  let S := RootData.rationalSimpleCorootSpan D.datum D.base
  let H := rationalWeightSpace A 0
  let g (i : D.base.support) : L := generator ℚ A (.H i)
  let g' (i : D.base.support) : L' := generator ℂ A (.H i)
  let t (i : D.base.support) : ℚ ⊗[ℤ] D.Y := 1 ⊗ₜ[ℤ] D.datum.coroot i
  let : Module.Free ℤ D.X := D.freeX
  let : Module.Free ℤ D.Y := D.freeY
  let : Module.Finite ℤ D.X := D.finiteX
  let : Module.Finite ℤ D.Y := D.finiteY
  let : Finite D.I := D.finiteRoots
  let : D.datum.IsReduced := D.reduced
  obtain ⟨b, hb⟩ := (serreStructure D).1.2.1
  obtain ⟨e, he⟩ := serreBaseChange A
  have hc : H = Submodule.span ℚ (Set.range g) := (rationalSerreDecomposition D).2.2
  let : Module ℚ L' := Module.compHom L' (algebraMap ℚ ℂ)
  let : IsScalarTower ℚ ℂ L' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hLi : LinearIndependent ℂ g' := by
    have hl := b.linearIndependent.map' (Serre.cartan A).subtype (Submodule.ker_subtype _)
    convert hl using 1
    exact funext fun i => (hb i).symm
  let a := (e.toLinearEquiv.toLinearMap.restrictScalars ℚ).comp (TensorProduct.mk ℚ ℂ L 1)
  have hLiQ : LinearIndependent ℚ g := by
    apply LinearIndependent.of_comp a
    rw [show a ∘ g = g' from funext fun i => he (.H i)]
    exact hLi.restrict_scalars' ℚ
  let hBasis : Module.Basis D.base.support ℚ H :=
    (Module.Basis.span hLiQ).map (LinearEquiv.ofEq _ _ hc.symm)
  let cBasis : Module.Basis D.base.support ℚ S :=
    Module.Basis.span (Module.Flat.linearIndependent_one_tmul D.base.linearIndepOn_coroot)
  have hhBasis (i : D.base.support) : (hBasis i).val = g i :=
    Module.Basis.coe_span_apply hLiQ i
  have hcBasis (i : D.base.support) : (cBasis i).val = t i :=
    Module.Basis.coe_span_apply _ i
  let f : H ≃ₗ[ℚ] S := hBasis.equiv cBasis (Equiv.refl _)
  have hf (i : D.base.support) : f (hBasis i) = cBasis i := hBasis.equiv_apply i cBasis (Equiv.refl _)
  have hcomp : IsCompl S Z := (RootData.rationalComplement D.datum D.base).2
  let h := (f.prodCongr (LinearEquiv.refl ℚ Z)).trans (Submodule.prodEquivOfIsCompl S Z hcomp)
  refine ⟨h, fun i => ⟨hBasis i, hhBasis i, ?_⟩, ?_⟩
  · change (Submodule.prodEquivOfIsCompl S Z hcomp) (f (hBasis i), 0) = t i
    rw [Submodule.coe_prodEquivOfIsCompl', hf, hcBasis]
    simp
  · intro z
    change (Submodule.prodEquivOfIsCompl S Z hcomp) (f 0, z) = _
    simp

section CartanAction

attribute [local instance 100] LieRing.ofAssociativeRing

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (CyclicPresentation serreHighestRelations loweringWeight loweringWord
  cyclicRepresentation rationalCharacter)
open RootData (integralCartan rationalRootAnnihilator extendFunctional extendFunctional_one_tmul)

set_option maxHeartbeats 650000 in
theorem rationalWeightsDetectCocharacters : Specs.RationalRealization.RationalWeightsDetectCocharacters.{u} := by
  intro D J w hw z z' h
  let := D.freeY
  let := D.finiteY
  let t := z - z'
  have ht (x : D.X) : rationalCharacter D x t = 0 := by
    have hz : x ∈ Submodule.span ℤ (Set.range w) := hw.symm ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      change rationalCharacter D (w j) (z - z') = 0
      rw [map_sub, sub_eq_zero]
      exact congrFun h j
    | zero => simp [rationalCharacter, extendFunctional]
    | add x y _ _ hx hy => rw [rationalCharacter_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul a x _ hx =>
      have he : rationalCharacter D (a • x) = a • rationalCharacter D x := by
        simp only [rationalCharacter, extendFunctional, map_smul, LinearMap.baseChange_smul,
          LinearMap.comp_smul]
      rw [he, LinearMap.smul_apply, hx, smul_zero]
  let b := Module.finBasis ℤ D.Y
  let bQ := b.baseChange ℚ
  suffices hz : t = 0 by exact sub_eq_zero.mp hz
  apply bQ.repr.injective
  ext j
  obtain ⟨x, hx⟩ := D.datum.toPerfPair.surjective (b.coord j)
  have he : bQ.coord j = rationalCharacter D x := by
    apply bQ.ext
    intro i
    change bQ.repr (b.baseChange ℚ i) j = extendFunctional ℚ (D.datum.toLinearMap x) (b.baseChange ℚ i)
    rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_repr_tmul, extendFunctional_one_tmul]
    have hx' : D.datum.toLinearMap x (b i) = b.repr (b i) j := DFunLike.congr_fun hx (b i)
    rw [hx', zsmul_eq_mul, mul_one]
  change (bQ.coord j) t = (bQ.coord j) 0
  rw [he, ht, map_zero]

set_option maxHeartbeats 700000 in
theorem rationalCartanAction : Specs.RationalRealization.RationalCartanAction.{u} := by
  intro D _
  let A := integralCartan D.datum D.base
  let L := Matrix.ToLieAlgebra ℚ A
  let H := rationalWeightSpace A 0
  let Z := rationalRootAnnihilator D.datum
  obtain ⟨e, he, heZ⟩ := rationalCartanLattice D
  refine ⟨e, he, heZ, ?_⟩
  intro weight
  let s := serreHighestRelations D weight
  let V := CyclicPresentation s
  obtain ⟨ρ, hρ, hρL, _, hρZ⟩ := rationalCentralAction D weight
  refine ⟨ρ, hρ, hρL, ?_⟩
  intro h z w
  let μ := loweringWeight D weight w
  let v := loweringWord D weight w
  let iH : H →ₗ[ℚ] L × Z := H.subtype.prod 0
  let iH' : H →ₗ[ℚ] H × Z := (LinearMap.id (R := ℚ) (M := H)).prod 0
  let f : H →ₗ[ℚ] V := (LinearMap.applyₗ (R := ℚ) v).comp (ρ.comp iH)
  let g : H →ₗ[ℚ] V := ((rationalCharacter D μ).comp (e.toLinearMap.comp iH')).smulRight v
  have hH : H = Submodule.span ℚ (Set.range fun i => generator ℚ A (.H i)) :=
    (rationalSerreDecomposition D).2.2
  choose hgen hmark heq using he
  have hg : Submodule.span ℚ (Set.range hgen) = ⊤ := by
    apply Submodule.map_injective_of_injective H.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    change Submodule.span ℚ (Set.range fun i => (hgen i).val) = H
    simp only [hmark, hH]
    rfl
  have hf : f = g := by
    apply LinearMap.ext_on hg
    rintro _ ⟨i, rfl⟩
    change ρ ((hgen i).val, 0) v = rationalCharacter D μ (e (hgen i, 0)) • v
    rw [hρL, hmark, heq]
    change cyclicRepresentation s (generator ℚ A (.H i)) v =
      extendFunctional ℚ (D.datum.toLinearMap μ) (1 ⊗ₜ[ℤ] D.datum.coroot i) • v
    rw [extendFunctional_one_tmul]
    exact (rationalWeightWords D weight).1 w i
  have ha : ρ (h.val, 0) v = rationalCharacter D μ (e (h, 0)) • v :=
    DFunLike.congr_fun hf h
  have hb : ρ (0, z) v = rationalCharacter D μ (e (0, z)) • v := by
    rw [heZ]
    exact hρZ w z
  have hsum₁ : (h.val, z) = ((h.val, 0) : L × Z) + (0, z) := by simp
  have hsum₂ : (h, z) = ((h, 0) : H × Z) + (0, z) := by simp
  change ρ (h.val, z) v = rationalCharacter D μ (e (h, z)) • v
  rw [hsum₁, hsum₂, map_add, LinearMap.add_apply, ha, hb, map_add, map_add, add_smul]

end CartanAction

open AlgebraicGeometry in
theorem genericPoint_mem_smoothLocus_of_dominant : Specs.RationalRealization.DominantGenericSmoothness.{u} := by
  intro k _ _ X Y _ _ p f _ _
  have hf : f (genericPoint X) = genericPoint Y := by
    apply IsGenericPoint.eq _ (genericPoint_spec Y)
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec X).image f.continuous
  let y := f (genericPoint X)
  have hy : IsField (Y.presheaf.stalk y) := by
    rw [show y = genericPoint Y from hf]
    exact Field.toIsField Y.functionField
  let : Field (Y.presheaf.stalk y) := hy.toField
  let i : k →+* Y.presheaf.stalk y :=
    (p.stalkMap y).hom.comp (StructureSheaf.toStalk k (p y)).hom
  have : CharZero (Y.presheaf.stalk y) := charZero_of_injective_ringHom i.injective
  have := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(f.stalkMap (genericPoint X)).hom]
  exact Algebra.FormallySmooth.of_perfectField

section WordMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup AffineAlgebraicGroup)
open Specs.FiniteWordClosure (power wordDomain evaluate)
open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private wordMap affine_power kernel_stabilizes word_kernel_le
  liftClosed liftClosed_fac dominant_toImage dominant_tensor ker_comp_eq
  one_isWord pair_isWord comp_wordMap IsWord isWord_mul isWord_inv isWord_wordMap subgroupStructure
  isWord_factors isMonHom_of_factor
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure

set_option maxHeartbeats 600000 in
theorem wordGeneratedGroup : Specs.RationalRealization.WordGeneratedGroup.{u} := by
  intro k _ G X f x₀ hAffine hx₀ hpowers
  have : IsAffine G.val.X.left := G.property.1
  have : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  obtain ⟨n, hn, hmin⟩ := kernel_stabilizes f x₀ hpowers
  let p := wordMap f n
  let Y : SchemeOver k := Over.mk (p.left.imageι ≫ G.val.X.hom)
  let i : Y ⟶ G.val.X := Over.homMk p.left.imageι rfl
  let w : wordDomain X n ⟶ Y := Over.homMk p.left.toImage (by
    change p.left.toImage ≫ p.left.imageι ≫ G.val.X.hom = _
    rw [← Category.assoc, p.left.toImage_imageι, p.w])
  have fac : w ≫ i = p := Over.OverMorphism.ext p.left.toImage_imageι
  have : IsAffine (wordDomain X n).left := affine_power (2 * n)
  have : QuasiCompact w.left := inferInstanceAs (QuasiCompact p.left.toImage)
  have hdom : IsSchemeTheoreticallyDominant w.left := dominant_toImage p.left
  have : IsIntegral (wordDomain X n).left := hpowers (2 * n)
  have hy : IsIntegral Y.left := by
    let := hdom
    refine (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr
      ⟨(irreducibleSpace_def _).mpr ?_, IsSchemeTheoreticallyDominant.isReduced w.left⟩
    change IsIrreducible (Set.univ : Set Y.left)
    rw [← w.left.denseRange.closure_eq]
    exact (by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ w.left.continuous.continuousOn :
        IsIrreducible (Set.range w.left)).closure
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion p.left.imageι)
  have : Mono i := Over.mono_of_mono_left i
  have liftWord {S : SchemeOver k} {m : ℕ} {z : S ⟶ G.val.X}
      (hz : IsWord f m z) : i.left.ker ≤ z.left.ker := by
    change p.left.imageι.ker ≤ _
    rw [p.left.ker.ker_subschemeι]
    exact (hmin m).trans (word_kernel_le f hz)
  have hunit : i.left.ker ≤ (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X).left.ker :=
    liftWord (one_isWord f)
  have hinv : i.left.ker ≤ (i⁻¹).left.ker := by
    rw [← ker_comp_eq w i⁻¹, GrpObj.comp_inv, fac]
    exact liftWord (isWord_inv f (isWord_wordMap f n))
  let mul := (fst Y Y ≫ i) * (snd Y Y ≫ i)
  have hmul : i.left.ker ≤ mul.left.ker := by
    let : IsSchemeTheoreticallyDominant (w ⊗ₘ w).left := dominant_tensor w
    rw [← ker_comp_eq (w ⊗ₘ w) mul]
    have hx := isWord_mul f
      (show IsWord f n (fst _ _ ≫ p) from ⟨fst _ _, rfl⟩)
      (show IsWord f n (snd _ _ ≫ p) from ⟨snd _ _, rfl⟩)
    apply liftWord
    simpa only [mul, MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc, fac] using hx
  let one := liftClosed i _ hunit
  let inv := liftClosed i _ hinv
  let prod := liftClosed i _ hmul
  let := subgroupStructure i one prod inv
    (liftClosed_fac i _ hunit) (liftClosed_fac i _ hmul) (liftClosed_fac i _ hinv)
  have : IsMonHom i := by
    constructor
    · exact (liftClosed_fac i _ hunit).trans (MonObj.one_eq_one G.val.X).symm
    · change prod ≫ i = (i ⊗ₘ i) ≫ μ[G.val.X]
      rw [liftClosed_fac i _ hmul, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
  let N : ClosedSubgroup G.val := ⟨Grp.mk Y, Grp.ofHom i, ‹IsClosedImmersion i.left›⟩
  have ht : i.left.ker ≤ f.left.ker := by
    let b := toUnit X ≫ x₀
    have hb : b ≫ f = 1 := by rw [Category.assoc, hx₀, MonObj.comp_one]
    apply liftWord
    simpa only [hb, inv_one, mul_one, Category.id_comp] using pair_isWord f (𝟙 X) b
  refine ⟨N, n, w, hn, hy, hdom, ?_, ⟨liftClosed i _ ht, liftClosed_fac i _ ht⟩, ?_, ?_⟩
  · intro K _ _
    have : Flat (pullback.fst Y.hom (fieldSpecMap k K)) := inferInstance
    exact IsSchemeTheoreticallyDominant.of_isPullback (baseChangeMapPullback (K := K) w).flip
  · rintro M ⟨a, ha⟩
    let j := M.inclusion.hom.hom
    have : IsClosedImmersion j.left := M.isClosedImmersion
    have : Mono j := Over.mono_of_mono_left j
    obtain ⟨wM, hwM⟩ := isWord_factors f M.inclusion a ha (isWord_wordMap f n)
    have hj : j.left.ker ≤ i.left.ker := by
      change j.left.ker ≤ p.left.imageι.ker
      rw [p.left.ker.ker_subschemeι, ← show wM ≫ j = p from hwM]
      exact wM.left.le_ker_comp j.left
    let q := liftClosed j i hj
    have hq := liftClosed_fac j i hj
    have : IsMonHom q := isMonHom_of_factor N.inclusion M.inclusion q hq
    exact ⟨Grp.homMk q, Grp.hom_ext _ _ hq⟩
  · intro S q
    change q ≫ w ≫ i = _
    rw [fac, comp_wordMap]

end WordMaps

theorem dominantGenericLift : Specs.RationalRealization.DominantGenericLift.{u} := by
  intro A B _ _ _ _ _ _ _ hinj q hq
  let L := FractionRing B
  let F := FractionRing A
  let c : A →+* L := (algebraMap B L).comp (algebraMap A B)
  have hc : Function.Injective c := (IsFractionRing.injective B L).comp hinj
  let j : F →+* L := IsFractionRing.lift hc
  let : Algebra F L := j.toAlgebra
  have hj : ∀ a : A, j (algebraMap A F a) = c a := IsFractionRing.lift_algebraMap hc
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (hj a).symm)
  have : CharZero F := charZero_of_injective_ringHom (IsFractionRing.injective A F)
  have : Algebra.EssFiniteType B L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors B)
  have : Algebra.EssFiniteType A L := Algebra.EssFiniteType.comp A B L
  have : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp A F L
  have : Algebra.FormallySmooth F L := Algebra.FormallySmooth.of_perfectField
  have hunit : ∀ a : nonZeroDivisors A, IsUnit (q a) := by
    intro a
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    rw [hq]
    apply isUnit_iff_ne_zero.mpr
    change c (a : A) ≠ 0
    simpa only [map_zero] using hc.ne (nonZeroDivisors.ne_zero a.property)
  let q' : F →+* DualNumber L := IsLocalization.lift hunit
  have hq' : ∀ a : A, q' (algebraMap A F a) = q a := IsLocalization.lift_eq hunit
  let : Algebra F (DualNumber L) := q'.toAlgebra
  let pr : DualNumber L →+* L := (TrivSqZeroExt.fstHom L L L).toRingHom
  have hpr : pr.comp q' = j := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    change (q' (algebraMap A F a)).fst = j (algebraMap A F a)
    rw [hq', hj]
    exact hq a
  let π : DualNumber L →ₐ[F] L := { pr with commutes' := fun a => DFunLike.congr_fun hpr a }
  have hπ : Function.Surjective π := TrivSqZeroExt.fst_surjective
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, TrivSqZeroExt.kerIdeal_sq L L⟩
  let p' := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id F L) π hπ hnil
  refine ⟨p'.toRingHom.comp (algebraMap B L), ?_, ?_⟩
  · intro b
    exact Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id F L) π hπ hnil _
  · apply RingHom.ext
    intro a
    change p' (c a) = q a
    rw [← hj, ← hq' a]
    exact p'.commutes (algebraMap A F a)

section ExponentialAdjoint

open MulOpposite

variable {A : Type u} [Ring A] [Algebra ℚ A]

private def leftMultiplication : A →+* Module.End ℚ A where
  toFun := LinearMap.mulLeft ℚ
  map_one' := by ext x; exact one_mul x
  map_zero' := by ext x; exact zero_mul x
  map_mul' a b := by ext x; exact mul_assoc a b x
  map_add' a b := by ext x; exact add_mul a b x

private def rightMultiplication : Aᵐᵒᵖ →+* Module.End ℚ A where
  toFun a := LinearMap.mulRight ℚ a.unop
  map_one' := by ext x; exact mul_one x
  map_zero' := by ext x; exact mul_zero x
  map_mul' a b := by ext x; exact (mul_assoc x b.unop a.unop).symm
  map_add' a b := by ext x; exact mul_add x a.unop b.unop

theorem exponentialAdjoint : Specs.RationalRealization.ExponentialAdjoint.{u} := by
  intro A _ _ n hn
  let l : A →+* Module.End ℚ A := leftMultiplication
  let r : Aᵐᵒᵖ →+* Module.End ℚ A := rightMultiplication
  have hLn : IsNilpotent (l n) := hn.map l
  obtain ⟨m, hm⟩ := hn.neg
  have hm' : (op (-n)) ^ m = 0 := by rw [← op_pow, hm, op_zero]
  have hRn : IsNilpotent (r (op (-n))) := (show IsNilpotent (op (-n)) from ⟨m, hm'⟩).map r
  have comm : Commute (l n) (r (op (-n))) := by
    ext x
    exact (mul_assoc n x (-n)).symm
  let D := l n + r (op (-n))
  have hD : IsNilpotent D := comm.isNilpotent_add hLn hRn
  refine ⟨D, hD, ?_, ?_⟩
  · intro x
    change n * x + x * (-n) = n * x - x * n
    rw [mul_neg, sub_eq_add_neg]
  · intro x
    change IsNilpotent.exp (l n + r (op (-n))) x = _
    have hop : IsNilpotent.exp (op (-n)) = op (IsNilpotent.exp (-n)) := by
      rw [IsNilpotent.exp_eq_sum hm, IsNilpotent.exp_eq_sum hm']
      apply unop_injective
      let f : Aᵐᵒᵖ →+ A :=
        { toFun := unop
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      change f _ = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      change unop ((j.factorial : ℚ)⁻¹ • op (-n) ^ j) = _
      simp only [unop_smul, unop_pow, unop_op]
    rw [IsNilpotent.exp_add_of_commute comm hLn hRn,
      ← IsNilpotent.map_exp hn l, ← IsNilpotent.map_exp (show IsNilpotent (op (-n)) from ⟨m, hm'⟩) r, hop]
    change IsNilpotent.exp n * (x * IsNilpotent.exp (-n)) = _
    exact (mul_assoc _ _ _).symm

end ExponentialAdjoint

section MatrixGroups

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open Specs.StandardGroups (generalLinearPoints additivePoints)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.RationalRealization (matrixAlgebra exponentialMatrix MatrixExponential
  FaithfulDiagonalAction SplitDiagonalPair)
open WithConv

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]

omit [CharZero k] in
private theorem scaledMatrix_nilpotent (N : Matrix J J k) (hN : IsNilpotent N)
    (R : TestAlgebra k) (t : R) : IsNilpotent (t • (algebraMap k R).mapMatrix N) :=
  (hN.map (algebraMap k R).mapMatrix).smul t

private def exponentialUnit (N : Matrix J J k) (hN : IsNilpotent N)
    (R : TestAlgebra k) (t : R) : Matrix.GeneralLinearGroup J R :=
  letI := matrixAlgebra R
  (IsNilpotent.isUnit_exp (scaledMatrix_nilpotent N hN R t)).unit

private theorem exponentialUnit_val (N : Matrix J J k) (hN : IsNilpotent N)
    (R : TestAlgebra k) (t : R) :
    (exponentialUnit N hN R t).val = exponentialMatrix N R t := by
  let := matrixAlgebra R
  exact IsUnit.unit_spec (IsNilpotent.isUnit_exp (scaledMatrix_nilpotent N hN R t))

private def matrixExponentialPoints (N : Matrix J J k) (hN : IsNilpotent N) :
    additivePoints k ⟶ generalLinearPoints k J where
  app R := GrpCat.ofHom
    { toFun := fun t => exponentialUnit N hN R (Multiplicative.toAdd t)
      map_one' := by
        apply Units.ext
        change (exponentialUnit N hN R 0).val = 1
        rw [exponentialUnit_val]
        let := matrixAlgebra R
        simp [exponentialMatrix]
      map_mul' a b := by
        apply Units.ext
        change (exponentialUnit N hN R (a.toAdd + b.toAdd)).val =
          (exponentialUnit N hN R a.toAdd).val * (exponentialUnit N hN R b.toAdd).val
        simp only [exponentialUnit_val]
        let := matrixAlgebra R
        let M := (algebraMap k R).mapMatrix N
        change IsNilpotent.exp ((a.toAdd + b.toAdd) • M) =
          IsNilpotent.exp (a.toAdd • M) * IsNilpotent.exp (b.toAdd • M)
        rw [add_smul]
        apply IsNilpotent.exp_add_of_commute _ (scaledMatrix_nilpotent N hN R _)
          (scaledMatrix_nilpotent N hN R _)
        exact ((Commute.refl M).smul_left _).smul_right _ }
  naturality {R S} a := by
    apply GrpCat.ext
    intro t
    apply Units.ext
    change (exponentialUnit N hN S (a.hom (Multiplicative.toAdd t))).val =
      a.hom.toRingHom.mapMatrix (exponentialUnit N hN R (Multiplicative.toAdd t)).val
    simp only [exponentialUnit_val]
    let := matrixAlgebra R
    let := matrixAlgebra S
    let M := (algebraMap k R).mapMatrix N
    let x : R := Multiplicative.toAdd t
    change IsNilpotent.exp (a.hom x • (algebraMap k S).mapMatrix N) =
      a.hom.toRingHom.mapMatrix (IsNilpotent.exp (x • M))
    rw [IsNilpotent.map_exp (scaledMatrix_nilpotent N hN R _) _]
    congr 1
    ext i j
    change a.hom x * algebraMap k S (N i j) = a.hom (x * algebraMap k R (N i j))
    rw [map_mul, AlgHom.commutes]

/-- The linear term of the exponential on a square-zero parameter. -/
theorem exponentialMatrix_of_sq_zero : Specs.RationalRealization.MatrixExponentialSquareZero.{u} := by
  intro k J _ _ _ _ N R t ht
  let := matrixAlgebra R
  have h : (t • (algebraMap k R).mapMatrix N) ^ 2 = 0 := by
    rw [smul_pow, ht, zero_smul]
  change IsNilpotent.exp (t • (algebraMap k R).mapMatrix N) = _
  rw [IsNilpotent.exp_eq_sum h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul]

private theorem exponentialMatrix_mul_power (N : Matrix J J k) (hN : IsNilpotent N)
    (n : ℕ) (hn : N ^ (n + 2) = 0) (R : TestAlgebra k) (t : R) :
    let M := (algebraMap k R).mapMatrix N
    exponentialMatrix N R t * M ^ n = M ^ n + t • M ^ (n + 1) := by
  let := matrixAlgebra R
  let M := (algebraMap k R).mapMatrix N
  have hz : M ^ (2 + n) = 0 := by
    rw [Nat.add_comm, ← map_pow, hn, map_zero]
  have H : ((t • M) ^ 2) • (M ^ n) = 0 := by
    change (t • M) ^ 2 * M ^ n = 0
    rw [smul_pow, smul_mul_assoc, ← pow_add, hz, smul_zero]
  change IsNilpotent.exp (t • M) • M ^ n = _
  rw [IsNilpotent.exp_smul_eq_sum H (scaledMatrix_nilpotent N hN R t)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul]
  change M ^ n + (t • M) * M ^ n = M ^ n + t • M ^ (n + 1)
  rw [smul_mul_assoc, pow_succ']

private theorem exponentialMatrix_injective (N : Matrix J J k) (hN : IsNilpotent N) (hne : N ≠ 0)
    (R : TestAlgebra k) : Function.Injective (exponentialMatrix N R) := by
  let : Nontrivial (Matrix J J k) := nontrivial_of_ne N 0 hne
  have hn := pos_nilpotencyClass_iff.mpr hN
  have hm : 2 ≤ nilpotencyClass N := by
    have hnot : nilpotencyClass N ≠ 1 := fun h => hne (eq_zero_of_nilpotencyClass_eq_one h)
    exact Nat.succ_le_of_lt (lt_of_le_of_ne hn hnot.symm)
  let n := nilpotencyClass N - 2
  have hn2 : N ^ (n + 2) = 0 := by
    rw [Nat.sub_add_cancel hm]
    exact pow_nilpotencyClass hN
  have hn1 : N ^ (n + 1) ≠ 0 := by
    rw [show n + 1 = nilpotencyClass N - 1 by dsimp [n]; omega]
    exact pow_pred_nilpotencyClass hN
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn1
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  let M := (algebraMap k R).mapMatrix N
  have hentry : IsUnit ((M ^ (n + 1)) i j) := by
    rw [← map_pow]
    change IsUnit (algebraMap k R ((N ^ (n + 1)) i j))
    exact (isUnit_iff_ne_zero.mpr hj).map (algebraMap k R)
  intro a b hab
  have he := congrArg (fun T : Matrix J J R => T * M ^ n) hab
  rw [exponentialMatrix_mul_power N hN n hn2, exponentialMatrix_mul_power N hN n hn2] at he
  have hm' := add_left_cancel he
  exact hentry.mul_right_cancel (congrFun (congrFun hm' i) j)

omit [CharZero k] in
set_option maxHeartbeats 650000 in
private theorem closedImmersion_of_injective_test_points {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val)
    (hf : ∀ R : TestAlgebra k, Function.Injective (fun p : Points G.val.X R => p ≫ f.hom.hom)) :
    IsClosedImmersion f.hom.hom.left := by
  have : Mono f.hom.hom.left := by
    constructor
    intro Z a b hab
    have hover : a ≫ G.val.X.hom = b ≫ G.val.X.hom := by
      rw [← Over.w f.hom.hom, ← Category.assoc, hab, Category.assoc]
    apply Z.affineCover.hom_ext
    intro j
    let i := Z.affineCover.f j
    let S : SchemeOver k := Over.mk ((i ≫ a) ≫ G.val.X.hom)
    let a' : S ⟶ G.val.X := Over.homMk (i ≫ a) rfl
    let b' : S ⟶ G.val.X := Over.homMk (i ≫ b) (by
      change (i ≫ b) ≫ G.val.X.hom = (i ≫ a) ≫ G.val.X.hom
      simp only [Category.assoc, hover])
    have hS : IsAffine S.left := Z.isAffine_affineCover j
    obtain ⟨B, ⟨e⟩⟩ := essImage_algSpec.mpr hS
    have heq : e.hom ≫ a' = e.hom ≫ b' := hf B.unop (by
      apply Over.OverMorphism.ext
      change (e.hom.left ≫ i ≫ a) ≫ f.hom.hom.left =
        (e.hom.left ≫ i ≫ b) ≫ f.hom.hom.left
      simp only [Category.assoc, hab])
    apply (cancel_epi e.hom.left).mp
    exact congrArg Over.Hom.left heq
  obtain ⟨I, p, i, hi, _, _⟩ := schemeImageFactorization G H f
  have : Mono (p.hom.hom.left ≫ i.hom.hom.left) := by
    change Mono (p ≫ i).hom.hom.left
    rw [hi.1]
    infer_instance
  have : Mono p.hom.hom.left := mono_of_mono _ i.hom.hom.left
  have : Flat p.hom.hom.left := hi.2.1
  have : Surjective p.hom.hom.left := hi.2.2.1
  have : IsAffineHom p.hom.hom.left := hi.2.2.2.2.1
  have : IsIso p.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  have : IsClosedImmersion i.hom.hom.left := hi.2.2.2.2.2
  rw [← hi.1]
  exact IsClosedImmersion.comp _ _

omit [CharZero k] in
private theorem rootPoint_id_postcomp (A : AdditiveLine k) {G : GroupScheme k}
    (f : A.group ⟶ G) (R : TestAlgebra k) (t : R) :
    rootPoint (𝟙 A.group) R t ≫ f.hom.hom = rootPoint f R t := by
  let p : Points A.group.X R :=
    (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval t : Polynomial k →ₐ[k] R)).op
  change (p ≫ (𝟙 A.group : A.group ⟶ A.group).hom.hom) ≫ f.hom.hom = p ≫ f.hom.hom
  have hId : (𝟙 A.group : A.group ⟶ A.group).hom.hom = 𝟙 A.group.X := rfl
  rw [hId, Category.comp_id]

set_option maxHeartbeats 850000 in
private theorem matrixExponentialForModels (A : AdditiveLine k) (Q G : AffineAlgebraicGroup k)
    (hQ : Q.val = A.group)
    (b : (groupPointsFunctor k).obj A.group ≅ additivePoints k)
    (g : (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k J)
    (hparameter : ∀ (R : TestAlgebra k) (t : R),
      b.hom.app R (rootPoint (𝟙 A.group) R t) = Multiplicative.ofAdd t)
    (N : Matrix J J k) (hN : IsNilpotent N) :
    ∃ f : A.group ⟶ G.val,
      (∀ (R : TestAlgebra k) (t : R),
        ((g.hom.app R).hom (rootPoint f R t)).val = exponentialMatrix N R t) ∧
      (N ≠ 0 → IsClosedImmersion f.hom.hom.left) := by
  let F := b.hom ≫ matrixExponentialPoints N hN ≫ g.inv
  let e := groupHomEquiv A.group G.val (by rw [← hQ]; exact Q.property.1)
  let f : A.group ⟶ G.val := e.symm F
  have hf : (groupPointsFunctor k).map f = F := e.apply_symm_apply _
  have hcomp : (groupPointsFunctor k).map f ≫ g.hom = b.hom ≫ matrixExponentialPoints N hN := by
    rw [hf]
    simp only [F, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hvalue (R : TestAlgebra k) (t : R) :
      ((g.hom.app R).hom (rootPoint f R t)).val = exponentialMatrix N R t := by
    have h := DFunLike.congr_fun (congrArg (fun a => (a.app R).hom) hcomp)
      (rootPoint (𝟙 A.group) R t)
    change g.hom.app R (rootPoint (𝟙 A.group) R t ≫ f.hom.hom) =
      (matrixExponentialPoints N hN).app R (b.hom.app R (rootPoint (𝟙 A.group) R t)) at h
    rw [rootPoint_id_postcomp, hparameter R t] at h
    exact (congrArg Units.val h).trans (exponentialUnit_val N hN R t)
  refine ⟨f, hvalue, fun hne => ?_⟩
  obtain ⟨Qgroup, Qproof⟩ := Q
  dsimp only at hQ
  subst Qgroup
  apply closedImmersion_of_injective_test_points (G := ⟨A.group, Qproof⟩) f
  intro R
  have hsurj : Function.Surjective (rootPoint (𝟙 A.group) R) := by
    intro p
    use (b.hom.app R p).toAdd
    apply (ConcreteCategory.bijective_of_isIso (b.hom.app R)).1
    exact hparameter R _
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨c, rfl⟩ := hsurj y
  change rootPoint (𝟙 A.group) R a ≫ f.hom.hom = rootPoint (𝟙 A.group) R c ≫ f.hom.hom at hxy
  rw [rootPoint_id_postcomp, rootPoint_id_postcomp] at hxy
  have ht : a = c := exponentialMatrix_injective N hN hne R (by
    rw [← hvalue R a, ← hvalue R c, hxy])
  rw [ht]

private theorem standardAdditiveModel (k : Type u) [Field k] :
    ∃ (A : AdditiveLine k) (G : AffineAlgebraicGroup k)
      (b : (groupPointsFunctor k).obj A.group ≅ additivePoints k), G.val = A.group ∧
      ∀ (R : TestAlgebra k) (t : R), b.hom.app R (rootPoint (𝟙 A.group) R t) = Multiplicative.ofAdd t := by
  obtain ⟨ops, hd, he, hi, hp⟩ := StandardGroups.additiveGroupSpecification k
  let A : AdditiveLine k := ⟨ops, hd, he, hi⟩
  let := ops.hopf
  obtain ⟨a, ha, b, hb⟩ := hp
  refine ⟨A, Specs.StandardGroups.spectrum k (Polynomial k), b, rfl, ?_⟩
  intro R t
  let ev : Polynomial k →ₐ[k] R := Polynomial.aeval t
  have hpR : a.hom.app R (toConv ev) = rootPoint (𝟙 A.group) R t := by
    apply Over.OverMorphism.ext
    have hId : (𝟙 A.group : A.group ⟶ A.group).hom.hom = 𝟙 A.group.X := rfl
    let p : Points A.group.X R := (testSpec k).map (CommAlgCat.ofHom ev).op
    change (a.hom.app R (toConv ev) : Points A.group.X R).left =
      (p ≫ (𝟙 A.group : A.group ⟶ A.group).hom.hom).left
    rw [hId, Category.comp_id]
    exact ha R ev
  rw [← hpR]
  exact Multiplicative.toAdd.injective ((hb R ev).trans (Polynomial.aeval_X t))

set_option maxHeartbeats 600000 in
theorem matrixExponential : MatrixExponential.{u} := by
  intro k J _ _ _ _
  obtain ⟨A, Q, b, hQ, hb⟩ := standardAdditiveModel k
  let G := StandardGroups.generalLinearGroup k J
  let g := StandardGroups.generalLinearGroupPointsIso k J
  exact ⟨A, G, g, matrixExponentialForModels A Q G hQ b g hb⟩

open private baseChangePointIso groupIsoOfPointIso isAffine_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

set_option maxHeartbeats 700000 in
private theorem additiveParameterBaseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : AdditiveLine k) (B : AdditiveLine K)
    (a : (groupPointsFunctor k).obj A.group ≅ additivePoints k)
    (b : (groupPointsFunctor K).obj B.group ≅ additivePoints K)
    (ha : ∀ (R : TestAlgebra k) (t : R),
      a.hom.app R (rootPoint (𝟙 A.group) R t) = Multiplicative.ofAdd t)
    (hb : ∀ (R : TestAlgebra K) (t : R),
      b.hom.app R (rootPoint (𝟙 B.group) R t) = Multiplicative.ofAdd t) :
    ∃ e : (groupBaseChange k K).obj A.group ≅ B.group,
      ∀ (R : TestAlgebra K) (t : R),
        baseChangePoint k K A.group.X R (rootPoint e.inv R t) =
          rootPoint (𝟙 A.group) ((restrictTestAlgebra k K).obj R) t := by
  let F := groupBaseChange k K
  let σ := restrictTestAlgebra k K
  let c : additivePoints K ≅ σ ⋙ additivePoints k :=
    NatIso.ofComponents (fun R => Iso.refl _) (by
      intro R S f
      apply GrpCat.ext
      intro t
      rfl)
  let x : (groupPointsFunctor K).obj B.group ≅ (groupPointsFunctor K).obj (F.obj A.group) :=
    b ≪≫ c ≪≫ Functor.isoWhiskerLeft σ a.symm ≪≫ (baseChangePointIso K A.group).symm
  have : IsAffine A.group.X.left := by
    change IsAffine (Spec (CommRingCat.of (Polynomial k)))
    infer_instance
  have : IsAffine B.group.X.left := by
    change IsAffine (Spec (CommRingCat.of (Polynomial K)))
    infer_instance
  have : IsAffine (F.obj A.group).X.left := isAffine_baseChange K A.group
  let e := groupIsoOfPointIso x
  have he : (groupPointsFunctor K).map e.hom = x.hom :=
    (groupHomEquiv B.group (F.obj A.group) ‹IsAffine B.group.X.left›).apply_symm_apply _
  refine ⟨e.symm, fun R t => ?_⟩
  rw [← rootPoint_id_postcomp]
  have hx := DFunLike.congr_fun (congrArg (fun s => (s.app R).hom) he)
    (rootPoint (𝟙 B.group) R t)
  change rootPoint (𝟙 B.group) R t ≫ e.hom.hom.hom =
    (baseChangePointIso K A.group).inv.app R
      (a.inv.app (σ.obj R) (c.hom.app R (b.hom.app R (rootPoint (𝟙 B.group) R t)))) at hx
  change baseChangePoint k K A.group.X R (rootPoint (𝟙 B.group) R t ≫ e.hom.hom.hom) =
    rootPoint (𝟙 A.group) (σ.obj R) t
  refine (congrArg (baseChangePoint k K A.group.X R) hx).trans ?_
  rw [hb]
  change (baseChangePointIso K A.group).hom.app R
    ((baseChangePointIso K A.group).inv.app R (a.inv.app (σ.obj R) (Multiplicative.ofAdd t))) = _
  rw [Iso.inv_hom_id_app_apply]
  apply (ConcreteCategory.bijective_of_isIso (a.hom.app (σ.obj R))).1
  exact (Iso.inv_hom_id_app_apply a (σ.obj R) (Multiplicative.ofAdd t)).trans (ha (σ.obj R) t).symm

theorem additiveScalarExtension : Specs.RationalRealization.AdditiveScalarExtension.{u} := by
  intro k _
  obtain ⟨A, _, a, _, ha⟩ := standardAdditiveModel k
  refine ⟨A, ?_⟩
  intro K _ _
  obtain ⟨B, _, b, _, hb⟩ := standardAdditiveModel K
  obtain ⟨e, he⟩ := additiveParameterBaseChange A B a b ha hb
  exact ⟨B, e, he⟩

set_option maxHeartbeats 600000 in
theorem weightShiftMatrix : Specs.RationalRealization.WeightShiftMatrix.{u,v} := by
  classical
  intro J X k _ _ _ _ _ w α N hα hN
  constructor
  · have shift (m : ℕ) (i j : J) : (N ^ m) i j ≠ 0 → w i = w j + m • α := by
      induction m generalizing i j with
      | zero =>
        intro hn
        have h : i = j := by
          by_contra hij
          exact hn (by simp [hij])
        subst j
        simp
      | succ m ih =>
        intro hn
        have he : ∃ p, (N ^ m) i p * N p j ≠ 0 := by
          by_contra! he
          apply hn
          simp only [pow_succ, Matrix.mul_apply, he, Finset.sum_const_zero]
        obtain ⟨p, hp⟩ := he
        rcases mul_ne_zero_iff.mp hp with ⟨hp₁, hp₂⟩
        rw [ih i p hp₁, hN p j hp₂, succ_nsmul]
        abel
    by_contra hn
    have hpow (m : ℕ) : N ^ m ≠ 0 := fun h => hn ⟨m, h⟩
    have hfind (m : ℕ) : ∃ i j, (N ^ m) i j ≠ 0 := by
      by_contra! h
      exact hpow m (Matrix.ext h)
    choose i j hij using hfind
    have hinj : Function.Injective (fun n => (i n, j n)) := by
      intro n m h
      have s₁ := shift n (i n) (j n) (hij n)
      have s₂ := shift m (i m) (j m) (hij m)
      rw [show i n = i m from congrArg Prod.fst h, show j n = j m from congrArg Prod.snd h] at s₁
      have hs := add_left_cancel (s₁.symm.trans s₂)
      have : (n : ℤ) = (m : ℤ) :=
        smul_left_injective ℤ hα (by simpa only [Nat.cast_smul_eq_nsmul] using hs)
      exact_mod_cast this
    have : Finite ℕ := Finite.of_injective _ hinj
    exact not_finite ℕ
  · intro R χ
    dsimp only
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal]
    change _ * algebraMap k R (N i j) = _ * (algebraMap k R (N i j) * _)
    by_cases h : N i j = 0
    · simp [h]
    · rw [hN i j h]
      have hmul : Multiplicative.ofAdd (w j + α) =
          Multiplicative.ofAdd (w j) * Multiplicative.ofAdd α := rfl
      rw [hmul, map_mul, Units.val_mul]
      ring

set_option maxHeartbeats 600000 in
theorem weightShiftExponential : Specs.RationalRealization.WeightShiftExponential.{u} := by
  intro J X k _ _ _ _ _ _ w α N hα hshift R χ t
  let D := Matrix.diagonal (fun j => (χ (Multiplicative.ofAdd (w j))).val)
  let r : R := (χ (Multiplicative.ofAdd α)).val
  let N' := (algebraMap k R).mapMatrix N
  obtain ⟨hN, hD⟩ := weightShiftMatrix w α N hα hshift
  let := matrixAlgebra R
  let x := t • N'
  let y := (r * t) • N'
  have hx : IsNilpotent x := scaledMatrix_nilpotent N hN R t
  have hy : IsNilpotent y := scaledMatrix_nilpotent N hN R (r * t)
  have h : D * x = y * D := by
    change D * (t • N') = (r * t) • N' * D
    rw [mul_smul_comm, smul_mul_assoc, hD R χ, smul_smul, mul_comm t r]
  have hp (m : ℕ) : D * x ^ m = y ^ m * D := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_succ]
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  let n := max a b
  have hx' : x ^ n = 0 := pow_eq_zero_of_le (le_max_left _ _) ha
  have hy' : y ^ n = 0 := pow_eq_zero_of_le (le_max_right _ _) hb
  change D * IsNilpotent.exp x = IsNilpotent.exp y * D
  rw [IsNilpotent.exp_eq_sum hx', IsNilpotent.exp_eq_sum hy', Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [mul_smul_comm, smul_mul_assoc, hp]

section FaithfulDiagonal

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (diagonalTorus)
open Specs.DiagonalizableGroups (characterValuedPoints groupAlgebra)
open private pointsIso_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

variable {M : Type u} [CommGroup M]
variable (k) (weights : J → M)

private def diagonalUnit (R : TestAlgebra k) (u : M →* Rˣ) : Matrix.GeneralLinearGroup J R :=
  Units.map (Matrix.diagonalRingHom J R).toMonoidHom
    ⟨fun i => (u (weights i)).val, fun i => (u (weights i)⁻¹).val,
      by funext i; change (u (weights i)).val * (u (weights i)⁻¹).val = 1
         rw [map_inv]; exact Units.mul_inv (u (weights i)),
      by funext i; change (u (weights i)⁻¹).val * (u (weights i)).val = 1
         rw [map_inv]; exact Units.inv_mul (u (weights i))⟩

omit [CharZero k] in
private theorem diagonalUnit_val (R : TestAlgebra k) (u : M →* Rˣ) :
    (diagonalUnit k weights R u).val = Matrix.diagonal (fun i => (u (weights i)).val) := rfl

private def diagonalPointsMap : characterValuedPoints k M ⟶ generalLinearPoints k J where
  app R := GrpCat.ofHom
    { toFun := diagonalUnit k weights R
      map_one' := by apply Units.ext; simp [diagonalUnit_val]
      map_mul' a b := by
        apply Units.ext
        simp only [diagonalUnit_val, Units.val_mul, MonoidHom.mul_apply, Matrix.diagonal_mul_diagonal'] }
  naturality R S a := by
    apply GrpCat.ext
    intro u
    let t : M →* Rˣ := u
    apply Units.ext
    change Matrix.diagonal (fun i => a.hom (t (weights i)).val) =
      a.hom.toRingHom.mapMatrix (Matrix.diagonal (fun i => (t (weights i)).val))
    rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]; rfl

set_option maxHeartbeats 650000 in
theorem faithfulDiagonalAction : FaithfulDiagonalAction.{u} := by
  intro k _ D J _ _ w hw G g
  let T := diagonalTorus k D
  let M := Multiplicative D.X
  let θ := DiagonalizableGroups.groupAlgebraPointsIso k M
  let W (i : J) : M := Multiplicative.ofAdd (w i)
  let Gmap := θ.hom ≫ diagonalPointsMap k W ≫ g.inv
  let e := AffineAlgebraicGroup.groupHomEquiv T G
  let f := e.symm Gmap
  have hf : (groupPointsFunctor k).map f = Gmap := e.apply_symm_apply _
  have hval (R : TestAlgebra k) (t : Points T.val.X R) :
      ((g.hom.app R).hom (t ≫ f.hom.hom)).val =
        Matrix.diagonal (fun i => ((show M →* Rˣ from (θ.hom.app R).hom t) (W i)).val) := by
    have hcomp : (groupPointsFunctor k).map f ≫ g.hom = θ.hom ≫ diagonalPointsMap k W := by
      rw [hf]
      have hgg : (diagonalPointsMap k W ≫ g.inv) ≫ g.hom = diagonalPointsMap k W := by
        rw [Category.assoc, g.inv_hom_id, Category.comp_id]
      exact (Category.assoc θ.hom _ _).trans (congrArg (θ.hom ≫ ·) hgg)
    have h := DFunLike.congr_fun (congrArg (fun a => (a.app R).hom) hcomp) t
    exact (congrArg Units.val h).trans (diagonalUnit_val k W R (θ.hom.app R t))
  refine ⟨θ, ?_, f, ?_, hval⟩
  · intro R a t ht m
    let B := groupAlgebra k M
    let h := (hopfSpecPointIso B).hom.app R (toConv a)
    have ht' : t = h := by
      apply Over.OverMorphism.ext
      exact ht
    rw [ht']
    exact pointsIso_spec M R a m
  · apply closedImmersion_of_injective_test_points f
    intro R t s heq
    apply (ConcreteCategory.bijective_of_isIso (θ.hom.app R)).1
    let a : M →* Rˣ := θ.hom.app R t
    let b : M →* Rˣ := θ.hom.app R s
    change a = b
    have hd := (hval R t).symm.trans ((congrArg (fun p => ((g.hom.app R).hom p).val) heq).trans (hval R s))
    have h (i : J) : a (W i) = b (W i) := by
      apply Units.ext
      simpa only [Matrix.diagonal_apply_eq] using congrFun (congrFun hd i) i
    have hall (x : D.X) (hm : x ∈ Submodule.span ℤ (Set.range w)) :
        a (Multiplicative.ofAdd x) = b (Multiplicative.ofAdd x) := by
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact h i
      | zero => exact (map_one a).trans (map_one b).symm
      | add x y _ _ hx hy =>
        change a (Multiplicative.ofAdd x * Multiplicative.ofAdd y) =
          b (Multiplicative.ofAdd x * Multiplicative.ofAdd y)
        rw [map_mul, map_mul, hx, hy]
      | smul n x _ hx =>
        change a (Multiplicative.ofAdd x ^ n) = b (Multiplicative.ofAdd x ^ n)
        rw [map_zpow, map_zpow, hx]
    apply MonoidHom.ext
    intro m
    exact hall m.toAdd (hw.symm ▸ Submodule.mem_top)

end FaithfulDiagonal

end MatrixGroups

section RationalMatrixAction

attribute [local instance 100] LieRing.ofAssociativeRing

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (CyclicPresentation serreHighestRelations loweringWeight loweringWord
  rationalCharacter)
open RootData (integralCartan rationalRootAnnihilator extendFunctional extendFunctional_one_tmul)

set_option maxHeartbeats 850000 in
theorem rationalMatrixAction : Specs.RationalRealization.RationalMatrixAction.{u} := by
  classical
  intro D _
  let A := integralCartan D.datum D.base
  let L := Matrix.ToLieAlgebra ℚ A
  let H := rationalWeightSpace A 0
  let Z := rationalRootAnnihilator D.datum
  obtain ⟨e, he, hz, hρ⟩ := rationalCartanAction D
  obtain ⟨S, n, basis, words, _, hwords, hspan⟩ := dominantWeightFamily D
  let J := Σ x : S, Fin (n x)
  let w (j : J) := loweringWeight D j.1 (words j)
  have hrep (x : S) := hρ (x : D.X)
  choose act hbracket _ hact using hrep
  let r (x : S) : (L × Z) →ₗ[ℚ] Matrix (Fin (n x)) (Fin (n x)) ℚ :=
    (LinearMap.toMatrixAlgEquiv (basis x)).toLinearMap.comp (act x)
  let B : (∀ x : S, Matrix (Fin (n x)) (Fin (n x)) ℚ) →ₗ[ℚ] Matrix J J ℚ :=
    { Matrix.blockDiagonal'AddMonoidHom (fun x : S => Fin (n x)) (fun x : S => Fin (n x)) ℚ with
      map_smul' := Matrix.blockDiagonal'_smul }
  let ρ := B.comp (LinearMap.pi r)
  have hρ (x : L × Z) : ρ x = Matrix.blockDiagonal' (fun i => r i x) := rfl
  have hlie (x y : L × Z) : ρ (⁅x.1, y.1⁆, 0) = ⁅ρ x, ρ y⁆ := by
    let b := Matrix.blockDiagonal'RingHom (fun i : S => Fin (n i)) ℚ
    change b (fun i => r i (⁅x.1, y.1⁆, 0)) = b (fun i => r i x) * b (fun i => r i y) -
      b (fun i => r i y) * b (fun i => r i x)
    rw [← map_mul, ← map_mul, ← map_sub]
    congr 1
    funext i
    change (LinearMap.toMatrixAlgEquiv (basis i)) (act i (⁅x.1, y.1⁆, 0)) = _
    rw [hbracket]
    change _ = (LinearMap.toMatrixAlgEquiv (basis i)) (act i x) *
      (LinearMap.toMatrixAlgEquiv (basis i)) (act i y) -
      (LinearMap.toMatrixAlgEquiv (basis i)) (act i y) * (LinearMap.toMatrixAlgEquiv (basis i)) (act i x)
    simp only [Ring.lie_def, map_sub, map_mul]
  have hdiag (h : H) (z : Z) : ρ (h.val, z) = Matrix.diagonal fun j => rationalCharacter D (w j) (e (h, z)) := by
    have hm (i : S) : r i (h.val, z) = Matrix.diagonal fun j => rationalCharacter D (w ⟨i, j⟩) (e (h, z)) := by
      ext a b
      change (LinearMap.toMatrix (basis i) (basis i) (act i (h.val, z))) a b = _
      rw [LinearMap.toMatrix_apply]
      have hb : act i (h.val, z) (basis i b) = rationalCharacter D (w ⟨i, b⟩) (e (h, z)) • basis i b := by
        rw [hwords, hact]
      rw [hb, map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
      by_cases hab : a = b
      · subst b
        simp
      · simp [hab, Ne.symm hab]
    rw [hρ, show (fun i => r i (h.val, z)) = _ from funext hm, Matrix.blockDiagonal'_diagonal]
  have hinjCartan : Function.Injective (fun (x : H × Z) => ρ (x.1.val, x.2)) := by
    intro x y hxy
    apply e.injective
    apply rationalWeightsDetectCocharacters D w hspan
    apply Matrix.diagonal_injective
    exact (hdiag x.1 x.2).symm.trans (hxy.trans (hdiag y.1 y.2))
  let W (i : D.I) := rationalWeightSpace A (fun j => D.datum.pairing i j)
  have hroots (i : D.I) (x : L) (hx : x ∈ W i) :
      (∀ a b, ρ (x, 0) a b ≠ 0 → w a = w b + D.datum.root i) ∧ IsNilpotent (ρ (x, 0)) := by
    let α := D.datum.root i
    let N := ρ (x, (0 : Z))
    have he' := he
    choose hgen hmark heq using he'
    have hspanH : Submodule.span ℚ (Set.range hgen) = ⊤ := by
      apply Submodule.map_injective_of_injective H.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
      change Submodule.span ℚ (Set.range fun j => (hgen j).val) = H
      rw [show (fun j => (hgen j).val) = (fun j => generator ℚ A (.H j)) from funext hmark]
      exact (rationalSerreDecomposition D).2.2.symm
    let f : H →ₗ[ℚ] L := (LinearMap.applyₗ (R := ℚ) x).comp
      ((LieAlgebra.ad ℚ L).toLinearMap.comp H.subtype)
    let p : H →ₗ[ℚ] H × Z := (LinearMap.id (R := ℚ) (M := H)).prod 0
    let g : H →ₗ[ℚ] L := ((rationalCharacter D α).comp (e.toLinearMap.comp p)).smulRight x
    have hf : f = g := by
      apply LinearMap.ext_on hspanH
      rintro _ ⟨j, rfl⟩
      change ⁅(hgen j).val, x⁆ = rationalCharacter D α (e (hgen j, 0)) • x
      rw [hmark, heq]
      change _ = extendFunctional ℚ (D.datum.toLinearMap α) (1 ⊗ₜ[ℤ] D.datum.coroot j) • x
      rw [extendFunctional_one_tmul]
      exact hx j
    have hf' (h : H) (z : Z) : ⁅h.val, x⁆ = rationalCharacter D α (e (h, z)) • x := by
      have hsplit : (h, z) = ((h, 0) : H × Z) + (0, z) := by simp
      have hval : rationalCharacter D α z.val = 0 := by
        have h' : z.val ∈ ⨅ j : D.I, (extendFunctional ℚ (D.datum.root' j)).ker := z.property
        exact (Submodule.mem_iInf _).mp h' i
      rw [hsplit, map_add, map_add, hz, hval, add_zero]
      exact DFunLike.congr_fun hf h
    have hshift (a b : J) (hab : N a b ≠ 0) : w a = w b + α := by
      apply D.datum.toPerfPair.injective
      apply LinearMap.ext
      intro y
      obtain ⟨⟨h, z⟩, he⟩ := e.surjective (1 ⊗ₜ[ℤ] y)
      have hbr := hlie (h.val, z) (x, 0)
      change ρ (⁅h.val, x⁆, 0) = ⁅ρ (h.val, z), N⁆ at hbr
      rw [hf' h z, hdiag] at hbr
      let v := e (h, z)
      have hsmul : ((rationalCharacter D α v • x, 0) : L × Z) =
          rationalCharacter D α v • (x, 0) := by simp
      change ρ (rationalCharacter D α v • x, 0) =
        Matrix.diagonal (fun j => rationalCharacter D (w j) v) * N -
          N * Matrix.diagonal (fun j => rationalCharacter D (w j) v) at hbr
      rw [hsmul, map_smul] at hbr
      have hentry := congrArg (fun m : Matrix J J ℚ => m a b) hbr
      rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
      change rationalCharacter D α v * N a b =
        rationalCharacter D (w a) v * N a b - N a b * rationalCharacter D (w b) v at hentry
      have hv : rationalCharacter D (w a) v = rationalCharacter D (w b + α) v := by
        rw [rationalCharacter_add, LinearMap.add_apply]
        apply mul_right_cancel₀ hab
        calc
          _ = rationalCharacter D α v * N a b + N a b * rationalCharacter D (w b) v :=
            sub_eq_iff_eq_add.mp hentry.symm
          _ = _ := by ring
      change rationalCharacter D (w a) (e (h, z)) = rationalCharacter D (w b + α) (e (h, z)) at hv
      rw [he] at hv
      change extendFunctional ℚ (D.datum.toLinearMap (w a)) (1 ⊗ₜ[ℤ] y) =
        extendFunctional ℚ (D.datum.toLinearMap (w b + α)) (1 ⊗ₜ[ℤ] y) at hv
      rw [extendFunctional_one_tmul, extendFunctional_one_tmul] at hv
      exact_mod_cast hv
    refine ⟨hshift, ?_⟩
    let := D.freeX
    exact (weightShiftMatrix w α N (D.datum.ne_zero i) hshift).1

  have hroot (i : D.I) (x : W i) (hx : (x : L) ≠ 0) : ρ (x, 0) ≠ 0 := by
    let j := D.datum.reflectionPerm i i
    have hfin : Module.finrank ℚ (W j) = 1 := (rationalSerreDecomposition D).2.1 j
    let : Nontrivial (W j) := by
      rcases subsingleton_or_nontrivial (W j) with hs | hn
      · have hzero : Module.finrank ℚ (W j) = 0 := Module.finrank_eq_zero_of_subsingleton ℚ (W j)
        omega
      · exact hn
    obtain ⟨y, hy⟩ := exists_ne (0 : W j)
    have hy' : (y : L) ≠ 0 := fun h => hy (Subtype.ext h)
    obtain ⟨hmem, hne⟩ := oppositeRationalRootBracket D i x x.property y y.property hx hy'
    intro hzero
    have h := hlie (x, 0) (y, 0)
    change ρ (⁅(x : L), (y : L)⁆, 0) = ⁅ρ (x, 0), ρ (y, 0)⁆ at h
    rw [hzero, zero_lie] at h
    have h0 : (⟨⁅(x : L), (y : L)⁆, hmem⟩, (0 : Z)) = (0 : H × Z) :=
      hinjCartan (h.trans ρ.map_zero.symm)
    exact hne (congrArg (fun q : H × Z => q.1.val) h0)
  have hinj : Function.Injective ρ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro t ht
    have hρt : ρ t = 0 := LinearMap.mem_ker.mp ht
    have htop : (H ⊔ ⨆ i, W i) = ⊤ := (rationalSerreDecomposition D).1
    have ht' : t.1 ∈ H ⊔ ⨆ i, W i := htop.symm ▸ Submodule.mem_top
    obtain ⟨h, hh, x, hx, hs⟩ := Submodule.mem_sup.mp ht'
    let z : H := ⟨h, hh⟩
    let : Finite D.I := D.finiteRoots
    let : Fintype D.I := Fintype.ofFinite D.I
    have hx' : x ∈ ⨆ i ∈ (Finset.univ : Finset D.I), W i := by simpa using hx
    obtain ⟨r, hr⟩ := (Submodule.mem_iSup_finset_iff_exists_sum W x).mp hx'
    let P (i : D.I) : Matrix J J ℚ := ρ (r i, 0)
    have hv : ρ (h, t.2) + ∑ i, P i = 0 := by
      have he : (h, t.2) + ∑ i : D.I, ((r i : L), (0 : Z)) = t := by
        apply Prod.ext
        · change h + (∑ i : D.I, ((r i : L), (0 : Z))).1 = t.1
          simp only [Prod.fst_sum, hr, hs]
        · simp [Prod.snd_sum]
      rw [← he, map_add, map_sum] at hρt
      exact hρt
    have hP (i : D.I) : P i = 0 := by
      ext a b
      by_contra hne
      have hne' : P i a b ≠ 0 := hne
      have hshift := (hroots i (r i) (r i).property).1 a b hne'
      have hab : a ≠ b := by
        intro he
        subst b
        exact D.datum.ne_zero i (add_left_cancel (hshift.symm.trans (add_zero _).symm))
      have he := congrArg (fun m : Matrix J J ℚ => m a b) hv
      change ρ (z.val, t.2) a b + (∑ j, P j) a b = _ at he
      rw [hdiag, Matrix.diagonal_apply_ne _ hab, zero_add, Matrix.sum_apply] at he
      rw [Finset.sum_eq_single i] at he
      · exact hne' he
      · intro j hj hj'
        by_contra hn
        have hs' := (hroots j (r j) (r j).property).1 a b hn
        exact hj' (D.datum.root.injective (add_left_cancel (hs'.symm.trans hshift)))
      · simp
    have hr0 (i : D.I) : (r i : L) = 0 := by
      by_contra h
      exact hroot i (r i) h (hP i)
    have hCartan : ρ (z.val, t.2) = 0 := by simpa only [hP, Finset.sum_const_zero, add_zero] using hv
    have hzero : (z, t.2) = (0 : H × Z) := hinjCartan (hCartan.trans ρ.map_zero.symm)
    have hz' : h = 0 := congrArg (fun q : H × Z => q.1.val) hzero
    have h2 : t.2 = 0 := congrArg Prod.snd hzero
    have hx0 : x = 0 := by simpa only [hr0, Finset.sum_const_zero] using hr.symm
    have h1 : t.1 = 0 := by simpa only [hz', hx0, add_zero] using hs.symm
    rw [Submodule.mem_bot]
    exact Prod.ext h1 h2
  exact ⟨J, inferInstance, inferInstance, w, e, ρ, hlie, he, hz, hspan, hdiag, hinj, hroots⟩

end RationalMatrixAction

section DiagonalizableGroupSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open Specs.RationalRealization (diagonalTorus SplitDiagonalPair multiplicativeLine)
open Specs.CharacterPairing (characterValue)
open Specs.Pinning (BasedRootDatum SplitBorelPair)
open Specs.GeometricRadicals (IsSplitTorus IsTorus IsReductive)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters integerGenerator FGAbelianGroup)
open Specs.CharacterDescent (StandardLattice)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)

open private extendedGroupIso extendedSpecIso extendedSpecIso_hom_fst extendedSpecIso_natural specGroupMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private isCommMonObj_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
open private solvable_iff_sections rationalSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable (D : BasedRootDatum.{u})

private def diagonalBaseChange (M : Type u) [CommGroup M] :
    (groupBaseChange k K).obj (specGroup (groupAlgebra k M)) ≅ specGroup (groupAlgebra K M) :=
  (extendedGroupIso K (groupAlgebra k M)).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso
      (CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k K M)).symm.op

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalBaseChange_natural {M N : Type u} [CommGroup M] [CommGroup N]
    (f : M →* N) :
    (groupBaseChange k K).map (specGroupMap (groupAlgebraMap k f)) ≫
        (diagonalBaseChange k K M).hom =
      (diagonalBaseChange k K N).hom ≫ specGroupMap (groupAlgebraMap K f) := by
  let A := groupAlgebra k M
  let B := groupAlgebra k N
  let a := groupAlgebraMap k f
  let eA := extendedGroupIso K A
  let eB := extendedGroupIso K B
  let dA := (CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k K M)).symm
  let dB := (CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k K N)).symm
  have hn : specGroupMap (extendedHopfMap K a) ≫ eA.hom =
      eB.hom ≫ (groupBaseChange k K).map (specGroupMap a) := by
    apply Grp.hom_ext
    exact extendedSpecIso_natural K a
  apply (cancel_epi eB.hom).mp
  change eB.hom ≫ (groupBaseChange k K).map (specGroupMap a) ≫ eA.inv ≫ specGroupMap dA.hom =
    eB.hom ≫ (eB.inv ≫ specGroupMap dB.hom) ≫ specGroupMap (groupAlgebraMap K f)
  rw [← Category.assoc eB.hom ((groupBaseChange k K).map (specGroupMap a)), ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← specGroupMap_comp]
  congr 1
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply MonoidAlgebra.algHom_ext
  · intro m
    have hdA : dA.hom.hom (MonoidAlgebra.single m (1 : K)) =
        (1 : K) ⊗ₜ[k] MonoidAlgebra.single m (1 : k) :=
      MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) m 1
    have hdB : dB.hom.hom (MonoidAlgebra.single (f m) (1 : K)) =
        (1 : K) ⊗ₜ[k] MonoidAlgebra.single (f m) (1 : k) :=
      MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) (f m) 1
    change (extendedHopfMap K a).hom (dA.hom.hom (MonoidAlgebra.single m 1)) =
      dB.hom.hom (MonoidAlgebra.mapDomainBialgHom K f (MonoidAlgebra.single m 1))
    rw [hdA, MonoidAlgebra.mapDomainBialgHom_single, hdB]
    change Bialgebra.TensorProduct.map (BialgHom.id K K) (MonoidAlgebra.mapDomainBialgHom k f)
      ((1 : K) ⊗ₜ[k] MonoidAlgebra.single m 1) = _
    rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply, MonoidAlgebra.mapDomainBialgHom_single]
  · ext

/-- Scalar extension preserves the coordinate monomials of a diagonalizable group. -/
theorem diagonalScalarExtension : Specs.RationalRealization.DiagonalScalarExtension.{u} := by
  intro k K _ _ _
  refine ⟨diagonalBaseChange k K, ?_⟩
  intro M N _ _ f
  exact diagonalBaseChange_natural k K f

private theorem characterValue_id_coordinate {k : Type u} [Field k] (R : TestAlgebra k)
    (a : MonoidAlgebra k IntegerCharacters →ₐ[k] R) (t : Points (multiplicativeLine k).X R)
    (h : t.left = Spec.map (CommRingCat.ofHom a.toRingHom)) :
    characterValue (𝟙 (multiplicativeLine k)) R t = a (MonoidAlgebra.single integerGenerator 1) := by
  have ht : t = (testSpec k).map (CommAlgCat.ofHom a).op := Over.OverMorphism.ext h
  have hid : (𝟙 (multiplicativeLine k) : multiplicativeLine k ⟶ multiplicativeLine k).hom.hom =
      𝟙 (multiplicativeLine k).X := rfl
  unfold characterValue
  erw [hid, Category.comp_id]
  have hp := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage_map (CommAlgCat.ofHom a).op
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage t).unop.hom
    (MonoidAlgebra.single integerGenerator 1) = _
  exact congrArg (fun f => f.unop.hom (MonoidAlgebra.single integerGenerator 1)) <|
    (congrArg (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage ht).trans hp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
private theorem diagonalBaseChange_characterValue (R : TestAlgebra K)
    (t : Points (multiplicativeLine K).X R) :
    characterValue (𝟙 (multiplicativeLine k)) ((restrictTestAlgebra k K).obj R)
      (baseChangePoint k K (multiplicativeLine k).X R
        (t ≫ (diagonalBaseChange k K IntegerCharacters).inv.hom.hom)) =
      characterValue (𝟙 (multiplicativeLine K)) R t := by
  let M := IntegerCharacters.{u}
  let G := multiplicativeLine k
  let H := multiplicativeLine K
  let A := groupAlgebra k M
  let d := CharacterDescent.groupAlgebraBaseChange k K M
  let e : (groupBaseChange k K).obj G ≅ H := diagonalBaseChange k K M
  let R₀ := (restrictTestAlgebra k K).obj R
  let q : Points G.X R₀ := baseChangePoint k K G.X R (t ≫ e.inv.hom.hom)
  let a : MonoidAlgebra K M →ₐ[K] R :=
    (((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage t).unop).hom
  have ha : t.left = Spec.map (CommRingCat.ofHom a.toRingHom) :=
    congrArg (fun p : Points H.X R => p.left)
      ((algSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage t).symm
  let : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' rfl
  let i : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let b : MonoidAlgebra k M →ₐ[k] R₀ := ((a.comp d.toAlgEquiv.toAlgHom).restrictScalars k).comp i
  have hb : q.left = Spec.map (CommRingCat.ofHom b.toRingHom) := by
    change (t.left ≫ Spec.map (CommRingCat.ofHom d.toAlgEquiv.toAlgHom.toRingHom) ≫
      (extendedSpecIso K A).hom.left) ≫ pullback.fst G.X.hom (fieldSpecMap k K) = _
    rw [Category.assoc, Category.assoc]
    erw [extendedSpecIso_hom_fst K A, ha]
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  change characterValue (𝟙 G) R₀ q = characterValue (𝟙 H) R t
  rw [characterValue_id_coordinate R₀ b q hb, characterValue_id_coordinate R a t ha]
  change a (d ((1 : K) ⊗ₜ[k] MonoidAlgebra.single integerGenerator (1 : k))) =
    a (MonoidAlgebra.single integerGenerator (1 : K))
  congr 1
  apply d.symm.injective
  exact (d.symm_apply_apply _).trans
    (MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) integerGenerator 1).symm

theorem multiplicativeScalarExtension : Specs.RationalRealization.MultiplicativeScalarExtension.{u} := by
  intro k K _ _ _
  exact ⟨diagonalBaseChange k K IntegerCharacters, diagonalBaseChange_characterValue k K⟩

private def latticeCoordinates :
    Multiplicative D.X ≃* StandardLattice.{u} (Module.finrank ℤ D.X) := by
  let := D.freeX
  let := D.finiteX
  let b := Module.finBasis ℤ D.X
  let e := b.equivFun.toAddEquiv
  exact
    { toFun := fun x i => ⟨Multiplicative.ofAdd (e x.toAdd i)⟩
      invFun := fun f => Multiplicative.ofAdd (e.symm fun i => (f i).down.toAdd)
      left_inv := fun x => e.symm_apply_apply x.toAdd
      right_inv := fun f => congrArg (fun g i => (⟨Multiplicative.ofAdd (g i)⟩ :
        IntegerCharacters.{u})) (e.apply_symm_apply (fun i => (f i).down.toAdd))
      map_mul' := fun x y => by ext i; exact congrFun (e.map_add x.toAdd y.toAdd) i }

private theorem diagonalSplit : IsSplitTorus (diagonalTorus k D).val := by
  obtain ⟨e⟩ := CharacterDescent.standardSplitTorus (k := k) (Module.finrank ℤ D.X)
  let a := CommHopfAlgCat.isoMk
    (MonoidAlgebra.domCongrBialgEquiv k k (latticeCoordinates D))
  exact ⟨_, ⟨(hopfSpec (CommRingCat.of k)).mapIso a.symm.op ≪≫ e⟩⟩

private theorem diagonalGeometricallyConnected :
    GeometricallyConnected (diagonalTorus k D).val.X.hom := by
  constructor
  refine (geometrically_iff_of_commRing
    (P := fun X : Scheme.{u} => ConnectedSpace X)
    (f := (diagonalTorus k D).val.X.hom) (R := k)).mpr ?_
  intro E _ _ Y fst snd h
  let e := diagonalBaseChange k E (Multiplicative D.X)
  obtain ⟨r, ⟨d⟩⟩ := diagonalSplit E D
  let F := Grp.forget (SchemeOver E) ⋙ Over.forget _
  let i := h.isoPullback ≪≫ F.mapIso (e ≪≫ d)
  have hC : ConnectedSpace (Specs.StandardGroups.multiplicativePowerGroup E
      (ULift.{u} (Fin r))).val.X.left :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum (AddMonoidAlgebra E (ULift (Fin r) → ℤ))))
  exact i.hom.homeomorph.connectedSpace_iff.mpr hC


private theorem diagonalIsTorus : IsTorus (diagonalTorus k D).val := by
  refine ⟨k, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := diagonalSplit k D
  exact ⟨r, ⟨diagonalBaseChange k k (Multiplicative D.X) ≪≫ e⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalReductive [CharZero k] : IsReductive (diagonalTorus k D) := by
  let T := diagonalTorus k D
  refine ⟨characteristicZeroSmoothness k T, diagonalGeometricallyConnected k D, ?_⟩
  let E := AlgebraicClosure k
  let N := Specs.GeometricRadicals.geometricUnipotentRadical T
  have hN := (GeometricRadicals.geometricUnipotentRadicalLargest T).2.1
  let e := diagonalBaseChange k E (Multiplicative D.X)
  have hmult : (Specs.CharacterDescent.multiplicativeTypeSpecFunctor E).essImage
      (diagonalTorus E D) := by
    apply (CharacterDescent.multiplicativeTypeGroupCriterion _).mpr
    let : Module.Finite ℤ D.X := D.finiteX
    let : Group.FG (Multiplicative D.X) :=
      GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp D.finiteX)
    let M : FGAbelianGroup.{u} := ⟨CommGrpCat.of (Multiplicative D.X), inferInstance⟩
    exact ⟨E, inferInstance, inferInstance, inferInstance, M,
      ⟨diagonalBaseChange E E (Multiplicative D.X)⟩⟩
  have h := Unipotent.homFromUnipotentToMultiplicativeType (closedSubgroupAlgebraicGroup N)
    (diagonalTorus E D) (N.inclusion ≫ e.hom) hN hmult
  have : Mono N.inclusion := by
    let F := Grp.forget (SchemeOver E) ⋙ Over.forget _
    have := N.isClosedImmersion
    exact F.mono_of_mono_map (inferInstanceAs (Mono N.inclusion.hom.hom.left))
  have hz : N.inclusion = 0 := by
    apply (cancel_mono e.hom).mp
    rw [zero_comp]
    exact h
  have hzero : IsZero N.group := (IsZero.iff_id_eq_zero _).mpr (by
    apply (cancel_mono N.inclusion).mp
    rw [Category.id_comp, zero_comp, hz])
  exact ⟨hzero.iso (Grp.isZero_trivial _)⟩

private def wholeSubgroup (G : GroupScheme k) : ClosedSubgroup G :=
  ⟨G, 𝟙 G, inferInstanceAs (IsClosedImmersion (𝟙 G.X.left))⟩

private theorem isTorus_of_iso {E : Type u} [Field E] {G H : GroupScheme E}
    (f : G ≅ H) (hH : IsTorus H) : IsTorus G := by
  obtain ⟨F, _, _, _, r, ⟨i⟩⟩ := hH
  exact ⟨F, inferInstance, inferInstance, inferInstance, r, ⟨(groupBaseChange E F).mapIso f ≪≫ i⟩⟩

set_option maxHeartbeats 750000 in
private def diagonalPair [CharZero k] : SplitBorelPair k where
  G := diagonalTorus k D
  reductive := diagonalReductive k D
  T := wholeSubgroup k _
  split := diagonalSplit k D
  maximal := by
    let E := AlgebraicClosure k
    let F := groupBaseChange k E
    let T := (diagonalTorus k D).val
    have h : IsClosedImmersion (F.map (𝟙 T)).hom.hom.left := by
      rw [F.map_id]
      exact inferInstanceAs (IsClosedImmersion (𝟙 (F.obj T).X.left))
    refine ⟨h, ?_, ?_⟩
    · exact isTorus_of_iso (diagonalBaseChange k E (Multiplicative D.X)) (diagonalIsTorus E D)
    · intro U _ _
      exact ⟨U.inclusion, by
        change _ ≫ F.map (𝟙 T) = _
        rw [F.map_id, Category.comp_id]⟩
  B := wholeSubgroup k _
  borel := by
    let E := AlgebraicClosure k
    let F := groupBaseChange k E
    let T := diagonalTorus k D
    let U := baseChangedAlgebraicGroup E T
    let e := diagonalBaseChange k E (Multiplicative D.X)
    have h : IsClosedImmersion (F.map (𝟙 T.val)).hom.hom.left := by
      rw [F.map_id]
      exact inferInstanceAs (IsClosedImmersion (𝟙 (F.obj T.val).X.left))
    have hs : Smooth U.val.X.hom := characteristicZeroSmoothness E U
    have hc : ConnectedSpace U.val.X.left :=
      (diagonalGeometricallyConnected k D).geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
    have : IsCommMonObj U.val.X := isCommMonObj_of_groupIso e.symm inferInstance
    have hsolvable := (solvable_iff_sections U hs hc).mpr <|
      Group.isSolvable_of_comm (G := rationalSections U.val) mul_comm
    refine ⟨h, ⟨hs, hc, hsolvable⟩, ?_⟩
    intro S _ _
    exact ⟨S.inclusion, by
      change _ ≫ F.map (𝟙 T.val) = _
      rw [F.map_id, Category.comp_id]⟩
  containsTorus := ⟨𝟙 _, Category.id_comp _⟩

theorem splitDiagonalPair : SplitDiagonalPair.{u} := by
  intro k _ _ D
  exact ⟨diagonalPair k D, rfl, inferInstanceAs (IsIso (𝟙 (diagonalTorus k D).val)),
    inferInstanceAs (IsIso (𝟙 (diagonalTorus k D).val))⟩

end DiagonalizableGroupSchemes

section Rootless

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix

open _root_.LinearAlgebraicGroups.Specs
open Specs.RationalRealization (diagonalTorus Realization RationalField ExtendsRational multiplicativeLine)
open Specs.Pinning (BasedRootDatum SplitBorelPair AttachedDatum BasedIso PinnedGroup)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters integerGenerator)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.AdjointRepresentation (GroupPoints conjugate)
open Specs.CharacterPairing (adjointWeightVectors characterValue pairing powerMorphism)
open Specs.RootGroups (AdditiveLine)
open LinearAlgebraicGroups.CharacterDescent (monomialCharacterEquiv groupLikeCharacterEquiv)
open Specs.AbstractPairing (Root)
open private isCommMonObj_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
open private characterValue_one extendCoordinates adjointWeightVectors_iff canonicalZero_eq
  homToDual pairing_eq_iff integerExponent integerExponent_zpow
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private splitGroupHomEquiv integerHopfHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable (k : Type u) [Field k]

private theorem diagonalNoRoots (G : AffineAlgebraicGroup k) [IsCommMonObj G.val.X]
    (hT : IsSplitTorus G.val) : IsEmpty (Specs.AbstractPairing.Root (wholeSubgroup k G.val)) := by
  constructor
  intro ⟨χ, hχ, v, hv, hn⟩
  let s := identityLieStructure G
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, b, C, L, l, Ad, hAd, _, _⟩ := adjointRepresentation k G s
  let T := wholeSubgroup k G.val
  have hv' := (adjointWeightVectors_iff C l Ad hAd T χ v).mp hv
  have hn' : b.equivFun v ≠ 0 := by
    intro H
    apply hn
    rw [canonicalZero_eq s]
    exact b.equivFun.injective (H.trans b.equivFun.map_zero.symm)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn'
  apply hχ
  apply RootData.CharacterPairing.characterValuesDetectCharacters hT
  intro R t
  let w := extendCoordinates b R v
  let g := t ≫ T.inclusion.hom.hom
  have hconj : conjugate g (C.equiv R w) = (C.equiv R w).toMul.val := by
    change (mapPoints (Specs.AdjointRepresentation.constants R) g) * _ *
        (mapPoints (Specs.AdjointRepresentation.constants R) g)⁻¹ = _
    rw [mul_comm (mapPoints (Specs.AdjointRepresentation.constants R) g),
      mul_inv_cancel_right]
  have h := hAd R g w
  rw [hconj] at h
  have h' : ((l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g)).val *ᵥ w = w :=
    (C.equiv R).injective (Subtype.ext h)
  have hw : w = characterValue χ R t • w := by
    apply h'.symm.trans
    have ht : (((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app R) t =
        (((groupPointsFunctor k).map Ad).app R) g := rfl
    have h := hv' R t
    change ((l.hom.app R).hom ((((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app R) t)).val
      *ᵥ w = characterValue χ R t • w at h
    exact (congrArg (fun p => ((l.hom.app R).hom p).val *ᵥ w) ht).symm.trans h
  rw [characterValue_one]
  have hwi : IsUnit (w i) := (isUnit_iff_ne_zero.mpr hi).map (algebraMap k R)
  have he := congrFun hw i
  change w i = characterValue χ R t * w i at he
  exact hwi.mul_right_cancel (he.symm.trans ((one_mul (w i)).symm))

variable (D : BasedRootDatum.{u})
local notation "T" => specGroup (groupAlgebra k (Multiplicative D.X))

private def diagonalCharacters : D.X ≃ₗ[ℤ] Additive (Character T) :=
  ((monomialCharacterEquiv (M := Multiplicative D.X) k).trans
    (groupLikeCharacterEquiv (groupAlgebra k (Multiplicative D.X)))).toAdditive.toIntLinearEquiv

private theorem diagonalCharacters_eq (x : D.X) :
    Additive.toMul (diagonalCharacters k D x) =
      specGroupMap (groupAlgebraMap k ((zpowersHom (Multiplicative D.X)
        (Multiplicative.ofAdd x)).comp MulEquiv.ulift.toMonoidHom)) := by
  change specGroupMap (integerHopfHomEquiv (groupAlgebra k (Multiplicative D.X)) _) = _
  congr 1
  apply (integerHopfHomEquiv (groupAlgebra k (Multiplicative D.X))).symm.injective
  rw [Equiv.symm_apply_apply]
  apply GroupLike.val_injective
  change MonoidAlgebra.single (Multiplicative.ofAdd x) (1 : k) =
    MonoidAlgebra.mapDomainBialgHom k
      ((zpowersHom (Multiplicative D.X) (Multiplicative.ofAdd x)).comp MulEquiv.ulift.toMonoidHom)
      (MonoidAlgebra.single integerGenerator 1)
  rw [MonoidAlgebra.mapDomainBialgHom_single]
  change MonoidAlgebra.single (Multiplicative.ofAdd x) (1 : k) =
    MonoidAlgebra.single ((Multiplicative.ofAdd x) ^ (1 : ℤ)) (1 : k)
  rw [zpow_one]

private def diagonalExponent (y : D.Y) : Multiplicative D.X →* IntegerCharacters :=
  Additive.toMul ((homToDual (Multiplicative D.X)).symm (D.datum.flip.toPerfPair y))

private def diagonalCocharacters : D.Y ≃ₗ[ℤ] Additive (Cocharacter T) :=
  (D.datum.flip.toPerfPair.trans (homToDual (Multiplicative D.X)).symm).trans
    (splitGroupHomEquiv (k := k) (Multiplicative D.X) IntegerCharacters).toAdditive.toIntLinearEquiv

private theorem diagonalCocharacters_eq (y : D.Y) :
    Additive.toMul (diagonalCocharacters k D y) = specGroupMap (groupAlgebraMap k (diagonalExponent D y)) :=
  rfl

private theorem diagonalPairing (x : D.X) (y : D.Y) :
    pairing T (Additive.toMul (diagonalCharacters k D x)) (Additive.toMul (diagonalCocharacters k D y)) =
      D.datum.toLinearMap x y := by
  rw [diagonalCharacters_eq, diagonalCocharacters_eq]
  apply (pairing_eq_iff _ _ _).mp
  rw [compositionPairing, ← specGroupMap_comp]
  change specGroupMap (groupAlgebraMap k _ ≫ groupAlgebraMap k _) = _
  rw [powerMorphism]
  congr 1
  apply CommHopfAlgCat.hom_ext
  change (MonoidAlgebra.mapDomainBialgHom k (diagonalExponent D y)).comp
    (MonoidAlgebra.mapDomainBialgHom k ((zpowersHom (Multiplicative D.X)
      (Multiplicative.ofAdd x)).comp MulEquiv.ulift.toMonoidHom)) = _
  rw [← MonoidAlgebra.mapDomainBialgHom_comp]
  congr 1
  apply MonoidHom.ext
  intro a
  have he : integerExponent (diagonalExponent D y (Multiplicative.ofAdd x)) =
      D.datum.toLinearMap x y := by
    change (homToDual (Multiplicative D.X) ((homToDual (Multiplicative D.X)).symm
      (D.datum.flip.toPerfPair y))) x = _
    exact DFunLike.congr_fun
      ((homToDual (Multiplicative D.X)).apply_symm_apply (D.datum.flip.toPerfPair y)) x
  have hx : diagonalExponent D y (Multiplicative.ofAdd x) =
      integerGenerator.{u} ^ D.datum.toLinearMap x y :=
    integerExponent.{u}.injective (he.trans (integerExponent_zpow.{u} _).symm)
  change diagonalExponent D y ((Multiplicative.ofAdd x) ^ a.down.toAdd) =
    (integerGenerator.{u} ^ D.datum.toLinearMap x y) ^ a.down.toAdd
  rw [map_zpow, hx]

private theorem wholeGroup_normalizerAction (G : AffineAlgebraicGroup k) [IsCommMonObj G.val.X]
    (Q : RootDatum (Root (wholeSubgroup k G.val)) (Additive (Character G.val))
      (Additive (Cocharacter G.val))) :
    letI : IsCommMonObj (wholeSubgroup k G.val).group.X := ‹IsCommMonObj G.val.X›
    Specs.AbstractPairing.NormalizerAction (wholeSubgroup k G.val) Q := by
  let N := wholeSubgroup k G.val
  have hc {S : SchemeOver k} (x y : S ⟶ G.val.X) : x * y * x⁻¹ = y := by
    rw [mul_comm x y, mul_inv_cancel_right]
  refine ⟨N, ?_, 1, ?_⟩
  · intro S g
    refine ⟨fun _ => ⟨g, ?_⟩, fun _ => ⟨Iso.refl _, by simp, ?_⟩⟩
    · change g ≫ 𝟙 _ = g
      exact Category.comp_id g
    · change 𝟙 _ ≫ fst G.val.X S ≫ (𝟙 G.val.X) = _
      rw [Category.id_comp]
      exact (hc _ _).symm
  · intro n
    refine ⟨Iso.refl _, ?_, ?_, ?_⟩
    · change (𝟙 G.val.X : G.val.X ⟶ G.val.X) ≫ 𝟙 G.val.X =
        ((toUnit G.val.X ≫ n ≫ 𝟙 G.val.X) * 𝟙 G.val.X) * (toUnit G.val.X ≫ n ≫ 𝟙 G.val.X)⁻¹
      rw [hc]
      exact Category.id_comp _
    · intro χ
      change Additive.ofMul χ = Additive.ofMul (𝟙 _ ≫ χ)
      exact congrArg Additive.ofMul (Category.id_comp χ).symm
    · intro c
      let e := (1 : Q.Aut).coweightEquiv
      change e.symm (Additive.ofMul c) = Additive.ofMul (c ≫ 𝟙 _)
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      change Additive.ofMul c = Additive.ofMul (c ≫ 𝟙 _)
      exact congrArg Additive.ofMul (Category.comp_id c).symm

set_option maxHeartbeats 900000 in
private def rootlessModel [CharZero k] [IsEmpty D.I] (A : AdditiveLine k) :
    Realization D A := by
  classical
  let P := diagonalPair k D
  let hComm : IsCommMonObj P.T.group.X := inferInstanceAs (IsCommMonObj (specGroup (groupAlgebra k (Multiplicative D.X))).X)
  let : IsCommMonObj P.G.val.X := inferInstanceAs
    (IsCommMonObj (specGroup (groupAlgebra k (Multiplicative D.X))).X)
  let hEmpty : IsEmpty (Root P.T) := diagonalNoRoots k P.G P.split
  let e := Equiv.equivOfIsEmpty D.I (Root P.T)
  let f := diagonalCharacters k D
  let g := diagonalCocharacters k D
  let : Finite D.I := D.finiteRoots
  let Q := D.datum.map e f g
  let i : D.datum.Equiv Q :=
    { weightMap := f.toLinearMap
      coweightMap := g.symm.toLinearMap
      indexEquiv := e
      weight_coweight_transpose := by
        ext y x
        change D.datum.toLinearMap (f.symm (f x)) (g.symm y) = D.datum.toLinearMap x (g.symm y)
        rw [LinearEquiv.symm_apply_apply]
      root_weightMap := funext isEmptyElim
      coroot_coweightMap := funext isEmptyElim
      bijective_weightMap := f.bijective
      bijective_coweightMap := g.symm.bijective }
  let E : AttachedDatum P :=
    { comm := hComm
      datum :=
        { finiteRoots := Finite.of_injective e.symm e.symm.injective
          freeCharacters := by have := D.freeX; exact Module.Free.of_equiv f
          finiteCharacters := by have := D.finiteX; exact Module.Finite.equiv f
          freeCocharacters := by have := D.freeY; exact Module.Free.of_equiv g
          finiteCocharacters := by have := D.finiteY; exact Module.Finite.equiv g
          rootDatum := Q
          root_eq := isEmptyElim
          pairing_eq := by
            intro χ c
            obtain ⟨x, rfl⟩ := f.surjective (Additive.ofMul χ)
            obtain ⟨y, rfl⟩ := g.surjective (Additive.ofMul c)
            change D.datum.toLinearMap (f.symm (f x)) (g.symm (g y)) =
              pairing T (Additive.toMul (f x)) (Additive.toMul (g y))
            rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
            exact (diagonalPairing k D x y).symm
          attached := isEmptyElim
          reduced := ⟨fun a => isEmptyElim a⟩
          reducedCoroots := ⟨fun a => isEmptyElim a⟩
          opposite := isEmptyElim
          normalizerAction := wholeGroup_normalizerAction k P.G Q }
      base := D.base.map i
      simple_iff := isEmptyElim }
  exact ⟨⟨P, isEmptyElim, fun α => isEmptyElim α.val⟩, E,
    ⟨i, Set.ext fun r => (hEmpty.false (show Root P.T from r)).elim⟩⟩

private theorem rootlessModel_coweightEquiv [CharZero k] [IsEmpty D.I] (A : AdditiveLine k) (y : D.Y) :
    (rootlessModel k D A).datumIso.val.coweightEquiv.symm y = diagonalCocharacters k D y := by
  let e := (rootlessModel k D A).datumIso.val.coweightEquiv
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((diagonalCocharacters k D).symm_apply_apply y).symm


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
theorem rootlessRealization : Specs.RationalRealization.RootlessRealization.{u} := by
  intro D hD
  let F := RationalField.{u}
  let e : ℚ ≃+* F := ULift.ringEquiv.symm
  have : CharZero F := charZero_of_injective_ringHom (f := e.toRingHom) e.injective
  obtain ⟨A, hA⟩ := additiveScalarExtension F
  let Q := rootlessModel F D A
  refine ⟨A, Q, ⟨Iso.refl (diagonalTorus F D).val⟩, ?_⟩
  intro k _ _
  let : Algebra F k := ((algebraMap ℚ k).comp ULift.ringEquiv.toRingHom).toAlgebra
  obtain ⟨B, a, ha⟩ := hA k
  let K := rootlessModel k D B
  let d := diagonalBaseChange F k (Multiplicative D.X)
  let m := diagonalBaseChange F k IntegerCharacters
  refine ⟨B, K, ⟨{
    group := d
    torus := d
    borel := d
    additive := a
    multiplicative := m
    additive_parameter := ha
    multiplicative_parameter := diagonalBaseChange_characterValue F k
    torus_comm := ?_
    borel_comm := ?_
    pin_comm := fun i => isEmptyElim i.val
    character_comm := ?_
    cocharacter_comm := ?_ }⟩⟩
  · change (groupBaseChange F k).map (𝟙 _) ≫ d.hom = d.hom ≫ 𝟙 _
    rw [(groupBaseChange F k).map_id, Category.id_comp, Category.comp_id]
  · change (groupBaseChange F k).map (𝟙 _) ≫ d.hom = d.hom ≫ 𝟙 _
    rw [(groupBaseChange F k).map_id, Category.id_comp, Category.comp_id]
  · intro x
    change (groupBaseChange F k).map (Additive.toMul (diagonalCharacters F D x)) ≫ m.hom =
      d.hom ≫ Additive.toMul (diagonalCharacters k D x)
    rw [diagonalCharacters_eq, diagonalCharacters_eq]
    exact diagonalBaseChange_natural F k _
  · intro y
    change (groupBaseChange F k).map
        (Additive.toMul ((rootlessModel F D A).datumIso.val.coweightEquiv.symm y)) ≫ d.hom =
      m.hom ≫ Additive.toMul ((rootlessModel k D B).datumIso.val.coweightEquiv.symm y)
    erw [rootlessModel_coweightEquiv, rootlessModel_coweightEquiv, diagonalCocharacters_eq,
      diagonalCocharacters_eq]
    exact diagonalBaseChange_natural F k _

end Rootless

section DominantWordTangents

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

open Specs.AdjointRepresentation (reduction)

private theorem injective_of_dominant_spec {A B : CommRingCat.{u}} (r : A ⟶ B)
    [IsSchemeTheoreticallyDominant (Spec.map r)] :
    Function.Injective r.hom := by
  have he : (Scheme.ΓSpecIso _).inv ≫ (Spec.map r).appTop ≫ (Scheme.ΓSpecIso _).hom = r := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).1.comp
    (((Spec.map r).app_injective ⊤).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1)

set_option maxHeartbeats 650000 in
theorem dominantAffinePointLift : Specs.RationalRealization.DominantAffinePointLift.{u} := by
  intro k _ _ X Y _ _ _ _ w _ _
  let F := testSpec k
  let FF := algSpec.fullyFaithful (R := CommRingCat.of k)
  obtain ⟨A, ⟨eY⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr (show IsAffine Y.left from inferInstance)
  obtain ⟨B, ⟨eX⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr (show IsAffine X.left from inferInstance)
  let w' := eX.hom ≫ w ≫ eY.inv
  let f : A.unop ⟶ B.unop := (FF.preimage w').unop
  have hmap : F.map f.op = w' := FF.map_preimage w'
  have hIsoX : IsIso eX.inv.left := (Over.forget _).map_isIso eX.inv
  have hIsoY : IsIso eY.inv.left := (Over.forget _).map_isIso eY.inv
  have hX : IsIntegral (Spec (CommRingCat.of B.unop)) :=
    @IsIntegral.of_isIso X.left _ inferInstance eX.inv.left hIsoX
  have hY : IsIntegral (Spec (CommRingCat.of A.unop)) :=
    @IsIntegral.of_isIso Y.left _ inferInstance eY.inv.left hIsoY
  let : IsDomain A.unop := (affine_isIntegral_iff _).mp hY
  let : IsDomain B.unop := (affine_isIntegral_iff _).mp hX
  have hspec : Spec.map (CommRingCat.ofHom f.hom.toRingHom) = w'.left :=
    congrArg Over.Hom.left hmap
  have h₁ : LocallyOfFiniteType w'.left := by
    change LocallyOfFiniteType (eX.hom.left ≫ w.left ≫ eY.inv.left)
    infer_instance
  have h₂ : IsSchemeTheoreticallyDominant w'.left := by
    change IsSchemeTheoreticallyDominant (eX.hom.left ≫ w.left ≫ eY.inv.left)
    infer_instance
  let : Algebra A.unop B.unop := f.hom.toRingHom.toAlgebra
  have : Algebra.FiniteType A.unop B.unop := by
    apply RingHom.finiteType_algebraMap.mp
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp (hspec ▸ h₁)
  have hf : Function.Injective (algebraMap A.unop B.unop) := by
    let : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) := hspec ▸ h₂
    exact injective_of_dominant_spec (CommRingCat.ofHom f.hom.toRingHom)
  let : CharZero A.unop := charZero_of_injective_ringHom (algebraMap k A.unop).injective
  let K := FractionRing B.unop
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of k (DualNumber K)
  let incl : B.unop ⟶ R := CommAlgCat.ofHom (IsScalarTower.toAlgHom k B.unop K)
  let x : Points X R := F.map incl.op ≫ eX.hom
  refine ⟨K, inferInstance, inferInstance, x, ?_⟩
  intro q hq
  let q' : A.unop ⟶ S := (FF.preimage (q ≫ eY.inv)).unop
  have hq' : F.map q'.op = q ≫ eY.inv := FF.map_preimage _
  have hq'' : q' ≫ reduction R = f ≫ incl := by
    apply Quiver.Hom.op_inj
    apply FF.map_injective
    change F.map ((q' ≫ reduction R).op) = F.map ((f ≫ incl).op)
    simp only [op_comp, F.map_comp, hq', hmap, w']
    change mapPoints (reduction R) q ≫ eY.inv = (x ≫ w) ≫ eY.inv
    rw [hq]
  obtain ⟨p', hp', hcomp⟩ := dominantGenericLift (A := A.unop) (B := B.unop) hf q'.hom.toRingHom
    (fun a => ConcreteCategory.congr_hom hq'' a)
  let pAlg : B.unop →ₐ[k] DualNumber K :=
    { p' with
      commutes' := fun a => by
        have eq := RingHom.congr_fun hcomp (algebraMap k A.unop a)
        change p' (f.hom (algebraMap k A.unop a)) = q'.hom (algebraMap k A.unop a) at eq
        rwa [f.hom.commutes, q'.hom.commutes] at eq }
  let pMor : B.unop ⟶ S := CommAlgCat.ofHom pAlg
  have hp₀ : pMor ≫ reduction R = incl := by
    apply CommAlgCat.hom_ext
    exact AlgHom.ext hp'
  have hp₁ : f ≫ pMor = q' := by
    apply CommAlgCat.hom_ext
    exact AlgHom.ext (RingHom.congr_fun hcomp)
  refine ⟨F.map pMor.op ≫ eX.hom, ?_, ?_⟩
  · change F.map (reduction R).op ≫ F.map pMor.op ≫ eX.hom = x
    rw [← Category.assoc, ← F.map_comp, ← op_comp, hp₀]
  · apply (cancel_mono eY.inv).mp
    change (F.map pMor.op ≫ eX.hom) ≫ w ≫ eY.inv = q ≫ eY.inv
    rw [Category.assoc, ← show F.map f.op = eX.hom ≫ w ≫ eY.inv from hmap,
      ← F.map_comp, ← op_comp, hp₁, hq']

section TranslatedTangents

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.AdjointRepresentation (GroupPoints constants reduction)
open Specs.FiniteWordClosure (wordDomain evaluate)

/-- A subgroup condition on a point and the translate of that point by
the inverse of its constant reduction. -/
private def translatedSubgroup {E : Type*} [Group E] (L : Subgroup E) (c : E →* E) :
    Subgroup E where
  carrier := {p | c p ∈ (Subgroup.normalizer (L : Set _)) ∧ p * (c p)⁻¹ ∈ L}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change c a ∈ (Subgroup.normalizer (L : Set _)) ∧ a * (c a)⁻¹ ∈ L at ha
    change c b ∈ (Subgroup.normalizer (L : Set _)) ∧ b * (c b)⁻¹ ∈ L at hb
    change c (a * b) ∈ (Subgroup.normalizer (L : Set _)) ∧ (a * b) * (c (a * b))⁻¹ ∈ L
    rw [map_mul]
    refine ⟨Subgroup.mul_mem (Subgroup.normalizer (L : Set E)) ha.1 hb.1, ?_⟩
    have h : c a * (b * (c b)⁻¹) * (c a)⁻¹ ∈ L :=
      ((Subgroup.mem_normalizer_iff.mp ha.1) _).mp hb.2
    have eq : a * b * (c a * c b)⁻¹ =
        (a * (c a)⁻¹) * (c a * (b * (c b)⁻¹) * (c a)⁻¹) := by group
    exact eq ▸ L.mul_mem ha.2 h
  inv_mem' := by
    intro a ha
    change c a ∈ (Subgroup.normalizer (L : Set _)) ∧ a * (c a)⁻¹ ∈ L at ha
    change c a⁻¹ ∈ (Subgroup.normalizer (L : Set _)) ∧ a⁻¹ * (c a⁻¹)⁻¹ ∈ L
    rw [map_inv, inv_inv]
    refine ⟨Subgroup.inv_mem (Subgroup.normalizer (L : Set E)) ha.1, ?_⟩
    have h : (c a)⁻¹ * (a * (c a)⁻¹)⁻¹ * c a ∈ L :=
      ((Subgroup.mem_normalizer_iff''.mp ha.1) _).mp (L.inv_mem ha.2)
    have eq : a⁻¹ * c a = (c a)⁻¹ * (a * (c a)⁻¹)⁻¹ * c a := by group
    exact eq ▸ h

private abbrev reduce {k : Type u} [Field k] (G : GroupScheme k) (R : TestAlgebra k) :=
  (((groupPointsFunctor k).obj G).map (reduction R)).hom

private abbrev constant {k : Type u} [Field k] (G : GroupScheme k) (R : TestAlgebra k) :=
  (((groupPointsFunctor k).obj G).map (constants R)).hom

private theorem reduce_constant {k : Type u} [Field k] (G : GroupScheme k) (R : TestAlgebra k)
    (p : GroupPoints G R) : reduce G R (constant G R p) = p := by
  let F := (groupPointsFunctor k).obj G
  have h : constants R ≫ reduction R = 𝟙 R := by
    apply CommAlgCat.hom_ext
    ext r
    rfl
  have eq : F.map (constants R) ≫ F.map (reduction R) = 𝟙 (F.obj R) := by
    rw [← F.map_comp, h, F.map_id]
  exact congrArg (fun e : F.obj R ⟶ F.obj R => e p) eq

private theorem wordEvaluation_mem {k : Type u} [Field k] {X : SchemeOver k}
    {G : GroupScheme k} (f : X ⟶ G.X) (R : TestAlgebra k) (H : Subgroup (GroupPoints G R))
    (hf : ∀ x : Points X R, x ≫ f ∈ H) :
    ∀ n (p : Points (wordDomain X n) R), evaluate f n p ∈ H := by
  intro n
  induction n with
  | zero => exact fun _ => H.one_mem
  | succ n ih =>
    intro p
    exact H.mul_mem (H.mul_mem (hf _) (H.inv_mem (hf _))) (ih _)

set_option maxHeartbeats 650000 in
private theorem wordTangentContainment
    {k : Type u} [Field k] [CharZero k] {X : SchemeOver k} {H G : GroupScheme k}
    (f : X ⟶ G.X) (i : H ⟶ G)
    (n : ℕ) (w : wordDomain X n ⟶ H.X)
    [IsAffine (wordDomain X n).left] [IsIntegral (wordDomain X n).left]
    [IsAffine H.X.left] [IsIntegral H.X.left]
    [LocallyOfFiniteType w.left] [IsSchemeTheoreticallyDominant w.left]
    (hw : ∀ (S : SchemeOver k) (p : S ⟶ wordDomain X n),
      p ≫ w ≫ i.hom.hom = evaluate f n p) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      let R := CommAlgCat.of k K
      let S := CommAlgCat.of k (DualNumber K)
      let c := (constant G R).comp (reduce G R)
      ∀ L : Subgroup (GroupPoints G S),
        (∀ x : Points X S, let z : GroupPoints G S := x ≫ f
          c z ∈ Subgroup.normalizer (L : Set (GroupPoints G S)) ∧ z * (c z)⁻¹ ∈ L) →
        ∀ t : GroupPoints H S, reduce H R t = 1 → t ≫ i.hom.hom ∈ L := by
  obtain ⟨K, _, _, x, hx⟩ := dominantAffinePointLift w
  refine ⟨K, inferInstance, inferInstance, ?_⟩
  dsimp only
  intro L hL t ht
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of k (DualNumber K)
  let y : GroupPoints H R := x ≫ w
  let q : GroupPoints H S := t * constant H R y
  have hq : reduce H R q = y := by
    rw [show q = t * constant H R y from rfl, map_mul, ht, reduce_constant, one_mul]
  obtain ⟨p, _, hpw⟩ := hx q hq
  let C := (constant G R).comp (reduce G R)
  have heval : q ≫ i.hom.hom ∈ translatedSubgroup L C := by
    have hw' : (q ≫ i.hom.hom : GroupPoints G S) = evaluate f n p := by
      have h := hw ((testSpec k).obj (op S)) p
      rw [← Category.assoc, hpw] at h
      exact h
    rw [hw']
    exact wordEvaluation_mem f S (translatedSubgroup L C) hL n p
  let z : GroupPoints G S := q ≫ i.hom.hom
  have htranslate : z * (C z)⁻¹ ∈ L := (show C z ∈
    Subgroup.normalizer (L : Set (GroupPoints G S)) ∧ z * (C z)⁻¹ ∈ L from heval).2
  have hc : C z = constant H R y ≫ i.hom.hom := by
    change mapPoints (constants R) (mapPoints (reduction R) (q ≫ i.hom.hom)) = _
    have er : mapPoints (reduction R) (q ≫ i.hom.hom) =
        mapPoints (reduction R) q ≫ i.hom.hom := (Category.assoc _ _ _).symm
    rw [er, show mapPoints (reduction R) q = y from hq]
    exact (Category.assoc _ _ _).symm
  let incl : GroupPoints H S →* GroupPoints G S := (((groupPointsFunctor k).map i).app S).hom
  have hp : z = incl t * incl (constant H R y) := incl.map_mul _ _
  have hc' : C z = incl (constant H R y) := hc
  rw [hc', hp, mul_inv_cancel_right] at htranslate
  exact htranslate

end TranslatedTangents

open private matrixDual from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open Specs.StandardGroups (generalLinearPoints)

section MatrixTangents

variable {K J : Type u} [Field K] [Fintype J] [DecidableEq J]

private abbrev M := Matrix J J K
private abbrev InvertibleMatrix := Matrix.GeneralLinearGroup J K
private abbrev GLε := Matrix.GeneralLinearGroup J (DualNumber K)

private abbrev dualMatrix (p : GLε (K := K) (J := J)) : DualNumber (M (K := K) (J := J)) :=
  matrixDual p.val

private theorem dualMatrix_mul (a b : GLε (K := K) (J := J)) :
    dualMatrix (a * b) = dualMatrix a * dualMatrix b := matrixDual.map_mul _ _

private theorem dualMatrix_one : dualMatrix (1 : GLε (K := K) (J := J)) = 1 :=
  matrixDual.map_one

private def matrixConstants : InvertibleMatrix (K := K) (J := J) →* GLε (K := K) (J := J) :=
  Matrix.GeneralLinearGroup.map (TrivSqZeroExt.inlHom K K)

private theorem dualMatrix_constants (a : InvertibleMatrix (K := K) (J := J)) :
    dualMatrix (matrixConstants a) = TrivSqZeroExt.inl a.val := rfl

/-- The first-order matrices (1+epsilon x) for (x) in the given subspace. -/
private def matrixTangentSubgroup (L : Submodule K (M (K := K) (J := J))) :
    Subgroup (GLε (K := K) (J := J)) where
  carrier := {a | (dualMatrix a).fst = 1 ∧ (dualMatrix a).snd ∈ L}
  one_mem' := by simp [dualMatrix_one]
  mul_mem' := by
    intro a b ha hb
    rcases (show _ ∧ _ from ha) with ⟨ha₁, ha₂⟩
    rcases (show _ ∧ _ from hb) with ⟨hb₁, hb₂⟩
    change (dualMatrix (a * b)).fst = 1 ∧ (dualMatrix (a * b)).snd ∈ L
    rw [dualMatrix_mul, TrivSqZeroExt.fst_mul, DualNumber.snd_mul, ha₁, hb₁]
    simpa only [one_mul, mul_one, true_and] using L.add_mem hb₂ ha₂
  inv_mem' := by
    intro a ha
    rcases (show _ ∧ _ from ha) with ⟨ha₁, ha₂⟩
    have h := dualMatrix_mul a a⁻¹
    rw [mul_inv_cancel, dualMatrix_one] at h
    have h₀ := congrArg TrivSqZeroExt.fst h
    rw [TrivSqZeroExt.fst_mul, ha₁, one_mul] at h₀
    have h₁ := congrArg TrivSqZeroExt.snd h
    rw [DualNumber.snd_mul, ha₁, ← h₀, TrivSqZeroExt.fst_one, one_mul, mul_one] at h₁
    change (dualMatrix a⁻¹).fst = 1 ∧ (dualMatrix a⁻¹).snd ∈ L
    exact ⟨h₀.symm, (eq_neg_of_add_eq_zero_left h₁.symm).symm ▸ L.neg_mem ha₂⟩

private theorem matrixConstant_conjugation (g : InvertibleMatrix (K := K) (J := J)) (p : GLε (K := K) (J := J)) :
    let a := matrixConstants g
    dualMatrix (a * p * a⁻¹) =
      (g.val * (dualMatrix p).fst * g⁻¹.val, g.val * (dualMatrix p).snd * g⁻¹.val) := by
  dsimp only
  rw [← matrixConstants.map_inv, dualMatrix_mul, dualMatrix_mul, dualMatrix_constants,
    dualMatrix_constants]
  apply TrivSqZeroExt.ext
  · rfl
  · simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_inl, mul_zero, zero_mul, add_zero, zero_add]
    rfl

private theorem matrixConstant_normalizes (L : Submodule K (M (K := K) (J := J)))
    (g : InvertibleMatrix (K := K) (J := J))
    (h : ∀ V ∈ L, g.val * V * g⁻¹.val ∈ L)
    (h' : ∀ V ∈ L, g⁻¹.val * V * g.val ∈ L) :
    matrixConstants g ∈ Subgroup.normalizer
      (matrixTangentSubgroup L : Set (GLε (K := K) (J := J))) := by
  let P := matrixTangentSubgroup L
  have hforward {w : InvertibleMatrix (K := K) (J := J)}
      (hw : ∀ V ∈ L, w.val * V * w⁻¹.val ∈ L)
      {p : GLε (K := K) (J := J)} (hp : p ∈ P) :
      matrixConstants w * p * (matrixConstants w)⁻¹ ∈ P := by
    have hp' : (dualMatrix p).fst = 1 ∧ (dualMatrix p).snd ∈ L := hp
    change (dualMatrix _).fst = 1 ∧ (dualMatrix _).snd ∈ L
    rw [matrixConstant_conjugation]
    refine ⟨?_, hw _ hp'.2⟩
    change w.val * (dualMatrix p).fst * w⁻¹.val = 1
    rw [hp'.1, mul_one]
    exact congrArg Units.val (mul_inv_cancel w)
  apply Subgroup.mem_normalizer_iff.mpr
  intro p
  constructor
  · exact hforward h
  · intro hp
    have hh := hforward (w := g⁻¹) (by simpa only [inv_inv] using h') hp
    rw [map_inv, inv_inv] at hh
    have eq : (matrixConstants g)⁻¹ * (matrixConstants g * p * (matrixConstants g)⁻¹) *
        matrixConstants g = p := by group
    rwa [eq] at hh

private theorem reduceMatrix_mem (L : Submodule K (M (K := K) (J := J)))
    (p : GLε (K := K) (J := J)) (g : InvertibleMatrix (K := K) (J := J))
    (h : (dualMatrix p).fst = g.val)
    (hsub : (dualMatrix p).snd * g⁻¹.val ∈ L) :
    p * (matrixConstants g)⁻¹ ∈ matrixTangentSubgroup L := by
  change (dualMatrix _).fst = 1 ∧ (dualMatrix _).snd ∈ L
  rw [← matrixConstants.map_inv, dualMatrix_mul, dualMatrix_constants,
    TrivSqZeroExt.fst_mul, DualNumber.snd_mul, h, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, mul_zero, zero_add]
  exact ⟨congrArg Units.val (mul_inv_cancel g), hsub⟩

end MatrixTangents

section WordMatrixTangents

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme Lie)
open Specs.AdjointRepresentation (GroupPoints constants reduction dualMap)
open Specs.FiniteWordClosure (wordDomain evaluate)
open InfinitesimalCommutator (matrixDifferential)

variable {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
variable {K : Type u} [Field K] [Algebra k K]

/-- Entrywise scalar extension of a matrix subspace. -/
def matrixSpanExtension (L : Submodule k (Matrix J J k)) :
    Submodule K (Matrix J J K) :=
  Submodule.span K ((algebraMap k K).mapMatrix '' (L : Set (Matrix J J k)))

private theorem mem_of_mapMatrix_mem_spanExtension (L : Submodule k (Matrix J J k))
    (x : Matrix J J k) (h : (algebraMap k K).mapMatrix x ∈ matrixSpanExtension L) :
    x ∈ L := by
  let f := Algebra.linearMap k K
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k K).injective)
  have hg' (a : k) : g (algebraMap k K a) = a := DFunLike.congr_fun hg a
  let P (m : Matrix J J K) : Matrix J J k := fun i j => g (m i j)
  have he :
      ∀ v ∈ matrixSpanExtension (K := K) L, ∀ b : K, P (b • v) ∈ L := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∀ b : K, P (b • v) ∈ L)
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨v, hv, rfl⟩ b
      have eq : P (b • (algebraMap k K).mapMatrix v) = g b • v := by
        ext i j
        change g (b * algebraMap k K (v i j)) = g b * v i j
        rw [mul_comm b, ← Algebra.smul_def, g.map_smul, smul_eq_mul, mul_comm]
      rw [eq]
      exact L.smul_mem _ hv
    · intro b
      have eq : P (b • (0 : Matrix J J K)) = 0 := by rw [smul_zero]; ext; exact g.map_zero
      rw [eq]
      exact L.zero_mem
    · intro v w _ _ hv hw b
      have eq : P (b • (v + w)) = P (b • v) + P (b • w) := by
        rw [smul_add]
        ext i j
        exact g.map_add _ _
      rw [eq]
      exact L.add_mem (hv b) (hw b)
    · intro b v _ hv c
      rw [smul_smul]
      exact hv _
  have hP := he _ h 1
  rw [one_smul] at hP
  have e : P ((algebraMap k K).mapMatrix x) = x := Matrix.ext fun i j => hg' (x i j)
  exact e ▸ hP

private abbrev toMatrixPoint {G : GroupScheme k}
    (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J) (R : TestAlgebra k) :
    GroupPoints G R →* Matrix.GeneralLinearGroup J R :=
  (g.hom.app R).hom

private theorem toMatrixPoint_natural {G : GroupScheme k}
    (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    {R S : TestAlgebra k} (a : R ⟶ S) (p : GroupPoints G R) :
    toMatrixPoint g S (mapPoints a p) =
      Matrix.GeneralLinearGroup.map a.hom.toRingHom (toMatrixPoint g R p) :=
  congrArg (fun φ : _ ⟶ (generalLinearPoints k J).obj S => φ p) (g.hom.naturality a)

private abbrev matrixReduction (F : Type u) [Field F] :
    Matrix.GeneralLinearGroup J (DualNumber F) →* Matrix.GeneralLinearGroup J F :=
  Matrix.GeneralLinearGroup.map (TrivSqZeroExt.fstHom F F F).toRingHom

private theorem matrixReduction_val (F : Type u) [Field F]
    (p : Matrix.GeneralLinearGroup J (DualNumber F)) :
    (matrixReduction F p).val = (dualMatrix p).fst := by
  apply Matrix.ext
  intro i j
  rfl

private theorem reduce_mapDual {G : GroupScheme k} {R S : TestAlgebra k}
    (a : R ⟶ S) (p : GroupPoints G (CommAlgCat.of k (DualNumber R))) :
    reduce G S (mapPoints (dualMap a) p) = mapPoints a (reduce G R p) := by
  let F := (groupPointsFunctor k).obj G
  have h : dualMap a ≫ reduction S = reduction R ≫ a := rfl
  have h' := congrArg (F.map) h
  rw [F.map_comp, F.map_comp] at h'
  exact congrArg (fun f : F.obj _ ⟶ F.obj S => f p) h'

private def matrixPointsWithTangents {G : GroupScheme k}
    (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (L : Submodule k (Matrix J J k)) :
    Subgroup (GroupPoints G (CommAlgCat.of k (DualNumber K))) :=
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of k (DualNumber K)
  let T := matrixTangentSubgroup (matrixSpanExtension (K := K) L)
  translatedSubgroup (T.comap (toMatrixPoint g S)) ((constant G R).comp (reduce G R))

set_option maxHeartbeats 800000 in
private theorem wordMatrixLieBound_of_membership
    [CharZero k] {G H : GroupScheme k} {X : SchemeOver k}
    (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (i : H ⟶ G) (f : X ⟶ G.X) (n : ℕ) (w : wordDomain X n ⟶ H.X)
    [IsAffine (wordDomain X n).left] [IsIntegral (wordDomain X n).left]
    [IsAffine H.X.left] [IsIntegral H.X.left]
    [LocallyOfFiniteType w.left] [IsSchemeTheoreticallyDominant w.left]
    (hw : ∀ (S : SchemeOver k) (p : S ⟶ wordDomain X n),
      p ≫ w ≫ i.hom.hom = evaluate f n p)
    (L : Submodule k (Matrix J J k))
    (hL : ∀ (K : Type u) [Field K] [Algebra k K],
      ∀ x : Points X (CommAlgCat.of k (DualNumber K)),
        (x ≫ f) ∈ matrixPointsWithTangents (K := K) g L) :
    ∀ p : Lie k H, matrixDifferential i g p ∈ L := by
  obtain ⟨K, _, _, hK⟩ := wordTangentContainment f i n w hw
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of k (DualNumber K)
  let a : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k K)
  let T := matrixTangentSubgroup (matrixSpanExtension (K := K) L)
  let U := T.comap (toMatrixPoint g S)
  have hf : ∀ x : Points X S, let z : GroupPoints G S := x ≫ f
      let c := (constant G R).comp (reduce G R)
      c z ∈ Subgroup.normalizer (U : Set (GroupPoints G S)) ∧ z * (c z)⁻¹ ∈ U :=
    hL K
  intro p
  let t : GroupPoints H S := mapPoints (dualMap a) p.toMul.val
  have ht : reduce H R t = 1 := by
    rw [reduce_mapDual]
    have hp : reduce H (CommAlgCat.of k k) p.toMul.val = 1 := p.toMul.property
    rw [hp]
    exact (((groupPointsFunctor k).obj H).map a).hom.map_one
  have h := hK U hf t ht
  have he : (dualMatrix (toMatrixPoint g S (t ≫ i.hom.hom))).snd ∈
      matrixSpanExtension (K := K) L :=
    (show _ ∧ _ from h).2
  apply mem_of_mapMatrix_mem_spanExtension (K := K)
  have hm : (dualMatrix (toMatrixPoint g S (t ≫ i.hom.hom))).snd =
      (algebraMap k K).mapMatrix (matrixDifferential i g p) := by
    have eq : (t ≫ i.hom.hom : GroupPoints G S) =
        mapPoints (dualMap a) (p.toMul.val ≫ i.hom.hom) := Category.assoc _ _ _
    rw [eq, toMatrixPoint_natural]
    rfl
  exact hm ▸ he

set_option maxHeartbeats 800000 in
theorem wordMatrixLieBound
    [CharZero k] {G H : GroupScheme k} {X : SchemeOver k}
    (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (i : H ⟶ G) (f : X ⟶ G.X) (n : ℕ) (w : wordDomain X n ⟶ H.X)
    [IsAffine (wordDomain X n).left] [IsIntegral (wordDomain X n).left]
    [IsAffine H.X.left] [IsIntegral H.X.left]
    [LocallyOfFiniteType w.left] [IsSchemeTheoreticallyDominant w.left]
    (hw : ∀ (S : SchemeOver k) (p : S ⟶ wordDomain X n),
      p ≫ w ≫ i.hom.hom = evaluate f n p)
    (L : Submodule k (Matrix J J k))
    (hL : ∀ (K : Type u) [Field K] [Algebra k K],
      let S := CommAlgCat.of k (DualNumber K)
      let L' := matrixSpanExtension (K := K) L
      ∀ x : Points X S,
        let z := toMatrixPoint g S (x ≫ f)
        let a := matrixReduction K z
        (∀ v ∈ L', a.val * v * a⁻¹.val ∈ L') ∧
        (∀ v ∈ L', a⁻¹.val * v * a.val ∈ L') ∧
        (dualMatrix z).snd * a⁻¹.val ∈ L') :
    ∀ p : Lie k H, matrixDifferential i g p ∈ L := by
  apply wordMatrixLieBound_of_membership g i f n w hw L
  intro K _ _
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of k (DualNumber K)
  let T := matrixTangentSubgroup (matrixSpanExtension (K := K) L)
  let U := T.comap (toMatrixPoint g S)
  let c := (constant G R).comp (reduce G R)
  change ∀ x : Points X S, let z : GroupPoints G S := x ≫ f
    c z ∈ Subgroup.normalizer (U : Set (GroupPoints G S)) ∧ z * (c z)⁻¹ ∈ U
  intro x
  let z : GroupPoints G S := x ≫ f
  let b := matrixReduction K (toMatrixPoint g S z)
  obtain ⟨h₁, h₂, h₃⟩ := hL K x
  have hc : toMatrixPoint g S (c z) = matrixConstants b := by
    change toMatrixPoint g S (mapPoints (constants R) (mapPoints (reduction R) z)) = _
    rw [toMatrixPoint_natural, toMatrixPoint_natural]
    rfl
  have hnormal := matrixConstant_normalizes (matrixSpanExtension (K := K) L) b h₁ h₂
  have htranslate := reduceMatrix_mem (matrixSpanExtension (K := K) L) (toMatrixPoint g S z)
    b (matrixReduction_val K _).symm h₃
  change c z ∈ Subgroup.normalizer (U : Set (GroupPoints G S)) ∧ z * (c z)⁻¹ ∈ U
  refine ⟨Subgroup.mem_normalizer_iff.mpr ?_, ?_⟩
  · intro p
    change toMatrixPoint g S p ∈ T ↔ toMatrixPoint g S (c z * p * (c z)⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv, hc]
    exact (Subgroup.mem_normalizer_iff.mp hnormal) _
  · change toMatrixPoint g S (z * (c z)⁻¹) ∈ T
    rwa [map_mul, map_inv, hc]

end WordMatrixTangents

section ExponentialTangents

variable {A : Type u} [Ring A] [Algebra ℚ A]

/-- Exponentiating after a square-zero perturbation has its expected
linear term when the perturbation commutes with the constant term. -/
private theorem exponentialDualNumber {a b : A} (ha : IsNilpotent a) (hab : Commute a b) :
    IsNilpotent.exp (A := DualNumber A) (a, b) =
      ((IsNilpotent.exp a, b * IsNilpotent.exp a) : DualNumber A) := by
  let x : DualNumber A := TrivSqZeroExt.inl a
  let y : DualNumber A := TrivSqZeroExt.inr b
  have hxy : Commute y x := by
    apply TrivSqZeroExt.ext <;>
      simp [x, y, TrivSqZeroExt.fst_mul, hab.eq]
  have hx : IsNilpotent x := ha.map (TrivSqZeroExt.inlHom A A)
  have hy₂ : y ^ 2 = 0 := by
    apply TrivSqZeroExt.ext <;>
      simp [y, pow_two, TrivSqZeroExt.fst_mul]
  have hy : IsNilpotent y := ⟨2, hy₂⟩
  have hY : IsNilpotent.exp y = 1 + y := by
    rw [IsNilpotent.exp_eq_sum hy₂, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have hX : IsNilpotent.exp x = TrivSqZeroExt.inl (IsNilpotent.exp a) :=
    (IsNilpotent.map_exp ha (TrivSqZeroExt.inlHom A A)).symm
  have hsum : ((a, b) : DualNumber A) = y + x := by
    apply TrivSqZeroExt.ext <;> simp [x, y]
  rw [hsum, IsNilpotent.exp_add_of_commute hxy hy hx, hY, hX]
  apply TrivSqZeroExt.ext <;>
    simp [y, TrivSqZeroExt.fst_mul]

/-- Nilpotent conjugation preserves every rational linear subspace stable
under its commutator operator. -/
private theorem exponentialConjugationMem 
    (S : Submodule ℚ A) (n : A) (hn : IsNilpotent n)
    (hS : ∀ x ∈ S, n * x - x * n ∈ S) {x : A} (hx : x ∈ S) :
    IsNilpotent.exp n * x * IsNilpotent.exp (-n) ∈ S := by
  obtain ⟨D, hD, hDx, hExp⟩ := exponentialAdjoint n hn
  obtain ⟨r, hr⟩ := hD
  have hiter (m : ℕ) : (D ^ m) x ∈ S := by
    induction m with
    | zero => simpa only [pow_zero, Module.End.one_apply] using hx
    | succ m ihm =>
      rw [pow_succ', Module.End.mul_apply, hDx]
      exact hS _ ihm
  rw [← hExp, IsNilpotent.exp_eq_sum hr, LinearMap.sum_apply]
  exact S.sum_mem (fun m _ => S.smul_mem _ (hiter m))

end ExponentialTangents

section MatrixExponentialTangents

open Specs.RationalRealization (exponentialMatrix matrixAlgebra)

variable {k K J : Type u} [Field k] [CharZero k] [Field K] [Algebra k K]
  [Fintype J] [DecidableEq J]

set_option maxHeartbeats 600000 in
private theorem matrixExponentialDualNumber (N : Matrix J J k) (hN : IsNilpotent N)
    (t : DualNumber K) :
    let N' := (algebraMap k K).mapMatrix N
    letI := matrixAlgebra (CommAlgCat.of k K)
    matrixDual (exponentialMatrix N (CommAlgCat.of k (DualNumber K)) t) =
      (IsNilpotent.exp (t.fst • N'), (t.snd • N') * IsNilpotent.exp (t.fst • N')) := by
  let R := CommAlgCat.of k (DualNumber K)
  let := matrixAlgebra R
  let := matrixAlgebra (CommAlgCat.of k K)
  let N' := (algebraMap k K).mapMatrix N
  let M : Matrix J J (DualNumber K) := (algebraMap k R).mapMatrix N
  have hMR : IsNilpotent (t • M) := (hN.map (algebraMap k R).mapMatrix).smul t
  have hM' : IsNilpotent (t.fst • N') := (hN.map (algebraMap k K).mapMatrix).smul t.fst
  have hcomm : Commute (t.fst • N') (t.snd • N') := Commute.smul_right
    (Commute.smul_left (Commute.refl N') t.fst) t.snd
  have he : matrixDual (t • M) = ((t.fst • N', t.snd • N') : DualNumber (Matrix J J K)) := by
    apply TrivSqZeroExt.ext <;> apply Matrix.ext <;> intro i j
    · change (t * TrivSqZeroExt.inl (algebraMap k K (N i j)) : DualNumber K).fst = _
      rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
      rfl
    · change (t * TrivSqZeroExt.inl (algebraMap k K (N i j)) : DualNumber K).snd = _
      rw [DualNumber.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, mul_zero, zero_add]
      rfl
  have hexp : exponentialMatrix N R t = IsNilpotent.exp (t • M) := by
    unfold exponentialMatrix
    exact congrArg (fun inst : Module ℚ (Matrix J J (DualNumber K)) =>
      @IsNilpotent.exp _ _ inst (t • M)) (Subsingleton.elim _ _)
  rw [hexp]
  exact (IsNilpotent.map_exp hMR matrixDual).trans
    (he ▸ exponentialDualNumber hM' hcomm)

set_option maxHeartbeats 600000 in
private theorem matrixExponentialNormalizedTangent
    (N : Matrix J J k) (hN : IsNilpotent N)
    (L : Submodule K (Matrix J J K))
    (hL : ∀ x ∈ L, (algebraMap k K).mapMatrix N * x - x * (algebraMap k K).mapMatrix N ∈ L)
    (hNL : (algebraMap k K).mapMatrix N ∈ L)
    (t : DualNumber K) (z : Matrix.GeneralLinearGroup J (DualNumber K))
    (hz : z.val = exponentialMatrix N (CommAlgCat.of k (DualNumber K)) t) :
    let a := matrixReduction K z
    (∀ x ∈ L, a.val * x * a⁻¹.val ∈ L) ∧
    (∀ x ∈ L, a⁻¹.val * x * a.val ∈ L) ∧
    (dualMatrix z).snd * a⁻¹.val ∈ L := by
  let R := CommAlgCat.of k K
  let := matrixAlgebra R
  let N' := (algebraMap k K).mapMatrix N
  let n := t.fst • N'
  let a := matrixReduction K z
  have h₀ : IsNilpotent n := (hN.map (algebraMap k K).mapMatrix).smul t.fst
  have hm : dualMatrix z = ((IsNilpotent.exp n,
      (t.snd • N') * IsNilpotent.exp n) : DualNumber (Matrix J J K)) := by
    rw [show dualMatrix z = matrixDual z.val from rfl, hz]
    exact matrixExponentialDualNumber N hN t
  have ha : a.val = IsNilpotent.exp n :=
    (matrixReduction_val K z).trans (congrArg TrivSqZeroExt.fst hm)
  have hainv : a⁻¹.val = IsNilpotent.exp (-n) := by
    apply (IsUnit.mul_right_cancel a.isUnit)
    calc
      a⁻¹.val * a.val = 1 := congrArg Units.val (inv_mul_cancel a)
      _ = IsNilpotent.exp (-n) * a.val := by rw [ha, IsNilpotent.exp_neg_mul_exp_self h₀]
  have hsn (x : Matrix J J K) (hx : x ∈ L) : n * x - x * n ∈ L := by
    change (t.fst • N') * x - x * (t.fst • N') ∈ L
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact L.smul_mem _ (hL x hx)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [ha, hainv]
    exact exponentialConjugationMem (L.restrictScalars ℚ) n h₀ hsn hx
  · intro x hx
    rw [ha, hainv]
    have hneg (y : Matrix J J K) (hy : y ∈ L) : (-n) * y - y * (-n) ∈ L := by
      rw [neg_mul, mul_neg, neg_sub_neg, ← neg_sub]
      exact L.neg_mem (hsn y hy)
    have hmem := exponentialConjugationMem
      (L.restrictScalars ℚ) (-n) h₀.neg hneg hx
    change _ ∈ L at hmem
    simpa only [neg_neg] using hmem
  · have hder : (dualMatrix z).snd = (t.snd • N') * IsNilpotent.exp n :=
      congrArg TrivSqZeroExt.snd hm
    rw [hder, hainv, mul_assoc, IsNilpotent.exp_mul_exp_neg_self h₀, mul_one]
    exact L.smul_mem _ hNL

end MatrixExponentialTangents

section DiagonalTangents

variable {K J X : Type u} [Field K] [Fintype J] [DecidableEq J] [AddCommGroup X]

private def unitReduction : (DualNumber K)ˣ →* Kˣ :=
  Units.map (TrivSqZeroExt.fstHom K K K).toRingHom

private def unitDerivative : (DualNumber K)ˣ →* Multiplicative K where
  toFun u := Multiplicative.ofAdd (u.val.snd * ((unitReduction u)⁻¹ : Kˣ).val)
  map_one' := by simp [unitReduction]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    change (u.val.fst * v.val.snd + u.val.snd * v.val.fst) *
        ((unitReduction (u * v))⁻¹ : Kˣ).val =
      u.val.snd * ((unitReduction u)⁻¹ : Kˣ).val +
        v.val.snd * ((unitReduction v)⁻¹ : Kˣ).val
    rw [map_mul, mul_inv_rev, Units.val_mul]
    have hu : u.val.fst * ((unitReduction u)⁻¹ : Kˣ).val = 1 :=
      congrArg Units.val (mul_inv_cancel (unitReduction u))
    have hv : v.val.fst * ((unitReduction v)⁻¹ : Kˣ).val = 1 :=
      congrArg Units.val (mul_inv_cancel (unitReduction v))
    calc
      _ = (u.val.fst * ((unitReduction u)⁻¹ : Kˣ).val) *
            (v.val.snd * ((unitReduction v)⁻¹ : Kˣ).val) +
          (v.val.fst * ((unitReduction v)⁻¹ : Kˣ).val) *
            (u.val.snd * ((unitReduction u)⁻¹ : Kˣ).val) := by ring
      _ = _ := by rw [hu, hv, one_mul, one_mul, add_comm]

private def characterDerivative (χ : Multiplicative X →* (DualNumber K)ˣ) : X →ₗ[ℤ] K :=
  ((unitDerivative.comp χ).toAdditive).toIntLinearMap

set_option maxHeartbeats 650000 in
private theorem diagonalNormalizedTangent
    (w : J → X) (L : Submodule K (Matrix J J K))
    (hdiag : ∀ φ : X →ₗ[ℤ] K, Matrix.diagonal (fun j => φ (w j)) ∈ L)
    (hstable : ∀ χ : Multiplicative X →* Kˣ, ∀ M ∈ L,
      Matrix.diagonal (fun j => (χ (Multiplicative.ofAdd (w j))).val) * M *
      Matrix.diagonal (fun j => ((χ (Multiplicative.ofAdd (w j)))⁻¹ : Kˣ).val) ∈ L)
    (χ : Multiplicative X →* (DualNumber K)ˣ)
    (z : Matrix.GeneralLinearGroup J (DualNumber K))
    (hz : z.val = Matrix.diagonal (fun j => (χ (Multiplicative.ofAdd (w j))).val)) :
    let a := matrixReduction K z
    (∀ M ∈ L, a.val * M * a⁻¹.val ∈ L) ∧
    (∀ M ∈ L, a⁻¹.val * M * a.val ∈ L) ∧
    (dualMatrix z).snd * a⁻¹.val ∈ L := by
  let a := matrixReduction K z
  let ψ := unitReduction.comp χ
  let v (j : J) := (ψ (Multiplicative.ofAdd (w j))).val
  let v' (j : J) := ((ψ (Multiplicative.ofAdd (w j)))⁻¹ : Kˣ).val
  let d (j : J) := (χ (Multiplicative.ofAdd (w j))).val.snd
  have ha : a.val = Matrix.diagonal v := by
    rw [matrixReduction_val]
    ext i j
    change (z.val i j).fst = _
    rw [hz]
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      rfl
    · simp only [Matrix.diagonal_apply_ne _ hij, TrivSqZeroExt.fst_zero]
  have ha' : a⁻¹.val = Matrix.diagonal v' := by
    apply (IsUnit.mul_right_cancel a.isUnit)
    calc
      a⁻¹.val * a.val = 1 := congrArg Units.val (inv_mul_cancel a)
      _ = Matrix.diagonal v' * a.val := by
        rw [ha, Matrix.diagonal_mul_diagonal]
        have eq : (fun j => v' j * v j) = (fun _ : J => (1 : K)) := by
          funext j
          exact congrArg Units.val (inv_mul_cancel (ψ (Multiplicative.ofAdd (w j))))
        rw [eq, Matrix.diagonal_one]
  have hs : (dualMatrix z).snd = Matrix.diagonal d := by
    ext i j
    change (z.val i j).snd = _
    rw [hz]
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · simp only [Matrix.diagonal_apply_ne _ hij, TrivSqZeroExt.snd_zero]
  dsimp only
  change (∀ M ∈ L, a.val * M * a⁻¹.val ∈ L) ∧
    (∀ M ∈ L, a⁻¹.val * M * a.val ∈ L) ∧
    (dualMatrix z).snd * a⁻¹.val ∈ L
  rw [ha, ha', hs, Matrix.diagonal_mul_diagonal]
  refine ⟨hstable ψ, ?_, hdiag (characterDerivative χ)⟩
  intro M hM
  simpa only [v, v', MonoidHom.inv_apply, inv_inv] using (hstable (ψ⁻¹) M hM)

end DiagonalTangents


end DominantWordTangents

section MatrixExtension

open AlgebraicGeometry CategoryTheory Opposite

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.StandardGroups (generalLinearPoints)
open Specs.RationalRealization (exponentialMatrix matrixAlgebra)
open private baseChangePointIso groupIsoOfPointIso isAffine_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

variable {k K J : Type u} [Field k] [Field K] [Algebra k K]
  [Fintype J] [DecidableEq J]

set_option maxHeartbeats 650000 in
theorem generalLinearScalarExtension (G : AffineAlgebraicGroup k) (H : AffineAlgebraicGroup K)
    (g : (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k J)
    (h : (groupPointsFunctor K).obj H.val ≅ generalLinearPoints K J) :
    ∃ e : (groupBaseChange k K).obj G.val ≅ H.val,
      ∀ (R : TestAlgebra K) (p : GroupPoints ((groupBaseChange k K).obj G.val) R),
        h.hom.app R (p ≫ e.hom.hom.hom) =
          g.hom.app ((restrictTestAlgebra k K).obj R) (baseChangePoint k K G.val.X R p) := by
  let σ := restrictTestAlgebra k K
  let F := groupBaseChange k K
  let c : generalLinearPoints K J ≅ σ ⋙ generalLinearPoints k J :=
    NatIso.ofComponents (fun R => Iso.refl _) (by
      intro R S f
      apply GrpCat.ext
      intro t
      rfl)
  let τ : (groupPointsFunctor K).obj (F.obj G.val) ≅ (groupPointsFunctor K).obj H.val :=
    baseChangePointIso K G.val ≪≫ Functor.isoWhiskerLeft σ g ≪≫ c.symm ≪≫ h.symm
  have : IsAffine G.val.X.left := G.property.1
  have : IsAffine H.val.X.left := H.property.1
  have : IsAffine (F.obj G.val).X.left := isAffine_baseChange K G.val
  let e := groupIsoOfPointIso τ
  have he : (groupPointsFunctor K).map e.hom = τ.hom :=
    (groupHomEquiv (F.obj G.val) H.val ‹IsAffine (F.obj G.val).X.left›).apply_symm_apply _
  refine ⟨e, fun R p => ?_⟩
  have hp := DFunLike.congr_fun (congrArg (fun s => (s.app R).hom) he) p
  change (p ≫ e.hom.hom.hom : GroupPoints H.val R) =
    h.inv.app R (c.inv.app R (g.hom.app (σ.obj R) (baseChangePoint k K G.val.X R p))) at hp
  rw [hp, Iso.inv_hom_id_app_apply]
  rfl

set_option maxHeartbeats 550000 in
theorem exponentialScalarExtension [CharZero k] [CharZero K]
    (N : Matrix J J k) (R : TestAlgebra K) (t : R) :
    exponentialMatrix ((algebraMap k K).mapMatrix N) R t =
      exponentialMatrix N ((restrictTestAlgebra k K).obj R) t := by
  let S := (restrictTestAlgebra k K).obj R
  have hmat : (algebraMap K R).mapMatrix ((algebraMap k K).mapMatrix N) =
      (algebraMap k S).mapMatrix N := by ext i j; rfl
  have hrat : matrixAlgebra R = (show Algebra ℚ R from matrixAlgebra S) :=
    Subsingleton.elim _ _
  unfold exponentialMatrix
  rw [hmat, hrat]

end MatrixExtension

section Semisimplicity

set_option maxHeartbeats 650000 in
/-- All characteristic-zero scalar extensions of the rational Serre algebra
have zero solvable radical, by comparison of their Killing forms. -/
theorem serreSemisimpleOver : Specs.RationalRealization.SerreSemisimpleOver.{u} := by
  classical
  intro D _ K _ _
  let A := RootData.integralCartan D.datum D.base
  let L := Matrix.ToLieAlgebra ℚ A
  let M := Serre.Algebra A
  let := (serreStructure D).2.1
  obtain ⟨e, he⟩ := serreBaseChange A
  let : Module.Finite ℂ (ℂ ⊗[ℚ] L) := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have : Module.Finite ℚ L := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat ℂ
  have hformM := (semisimple_iff_killingForm_nondegenerate ℂ M).mp (serreStructure D).2.2.2.2.1
  have hform : (LieAlgebrasAndRepresentations.killingForm ℂ (ℂ ⊗[ℚ] L)).Nondegenerate := by
    have eq (x y : ℂ ⊗[ℚ] L) : LieAlgebrasAndRepresentations.killingForm ℂ (ℂ ⊗[ℚ] L) x y =
        LieAlgebrasAndRepresentations.killingForm ℂ M (e x) (e y) :=
      (LieAlgebra.killingForm_of_equiv_apply e x y).symm
    constructor
    · intro x hx
      apply e.injective
      change e x = e 0
      rw [show e 0 = 0 from e.toLinearEquiv.map_zero]
      apply hformM.1
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      exact (eq x z).symm.trans (hx z)
    · intro x hx
      apply e.injective
      change e x = e 0
      rw [show e 0 = 0 from e.toLinearEquiv.map_zero]
      apply hformM.2
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      exact (eq z x).symm.trans (hx z)
  let b := Module.finBasis ℚ L
  have hz := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange ℂ)).mp hform
  rw [killingForm_baseChange_matrix ℚ ℂ L b, ← (algebraMap ℚ ℂ).mapMatrix_apply,
    ← RingHom.map_det] at hz
  have hn := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mpr
    ((map_ne_zero (algebraMap ℚ ℂ)).mp hz)
  exact lieAlgebra_semisimple_baseChange ℚ K L
    ((semisimple_iff_killingForm_nondegenerate ℚ L).mpr hn)

end Semisimplicity

section IdealsOfMatrices

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K J L S : Type u} [Field K] [Fintype J] [DecidableEq J]
  [LieRing L] [LieAlgebra K L] [Module.Finite K L] [LieRing S] [LieAlgebra K S]

set_option maxHeartbeats 700000 in
/-- A faithful matrix Lie algebra with a semisimple quotient and diagonal
kernel has no nonzero ideal whose elements are nilpotent matrices. -/
theorem nilpotentMatrixIdeal_eq_bot
    [CharZero K] (π : L →ₗ⁅K⁆ S) (hπ : Function.Surjective π)
    (hS : LieAlgebra.radical K S = ⊥) (ρ : L →ₗ⁅K⁆ Matrix J J K)
    (hρ : Function.Injective ρ)
    (hdiag : ∀ x, π x = 0 → ∃ d : J → K, ρ x = Matrix.diagonal d)
    (I : LieIdeal K L) (hI : ∀ x ∈ I, IsNilpotent (ρ x)) : I = ⊥ := by
  let ρI : I →ₗ⁅K⁆ Matrix J J K := ρ.comp I.incl
  have hρI : Function.Injective ρI := hρ.comp Subtype.val_injective
  have hnil : LieRing.IsNilpotent I := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
    intro x
    obtain ⟨D, ⟨m, hm⟩, hD, _⟩ := exponentialAdjoint (ρI x) (hI x x.property)
    let Y := LieAlgebra.ad K I x
    have hpow (n : ℕ) (y : I) : ρI ((Y ^ n) y) = (D ^ n) (ρI y) := by
      induction n with
      | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
      | succ n ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
        change ρI ⁅x, (Y ^ n) y⁆ = D ((D ^ n) (ρI y))
        rw [ρI.map_lie, ih, hD]
        rfl
    refine ⟨m, LinearMap.ext fun y => hρI ?_⟩
    change ρI ((Y ^ m) y) = ρI 0
    rw [hpow, hm, LinearMap.zero_apply, map_zero]
  let := hnil
  let πI : I →ₗ⁅K⁆ I.map π :=
    { toFun := fun x => ⟨π x, LieIdeal.mem_map (f := π) x.property⟩
      map_add' := fun x y => Subtype.ext (π.map_add x y)
      map_smul' := fun a x => Subtype.ext (π.map_smul a x)
      map_lie' := fun {x y} => Subtype.ext (π.map_lie x y) }
  have hpI : Function.Surjective πI := by
    intro y
    obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective (I := I) hπ y.property
    exact ⟨x, Subtype.ext hx⟩
  let := hpI.lieAlgebra_isSolvable (f := πI)
  let : LieAlgebra.HasTrivialRadical K S := ⟨hS⟩
  have he : I.map π = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable _
  apply le_antisymm ?_ bot_le
  intro x hx
  have hπx : π x = 0 := by
    have hp := LieIdeal.mem_map (f := π) hx
    rwa [he, LieSubmodule.mem_bot] at hp
  obtain ⟨d, hd⟩ := hdiag x hπx
  obtain ⟨n, hn⟩ := hI x hx
  rw [hd, Matrix.diagonal_pow, ← Matrix.diagonal_zero, Matrix.diagonal_injective.eq_iff] at hn
  have hz (j : J) : d j = 0 :=
    eq_zero_of_pow_eq_zero (congrFun hn j)
  have h0 : ρ x = 0 := by
    rw [hd, show d = (fun _ => 0) from funext hz, Matrix.diagonal_zero]
  rw [LieSubmodule.mem_bot]
  exact hρ (h0.trans (ρ.map_zero).symm)

end IdealsOfMatrices


section WordFamilies

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.FiniteWordClosure (power wordDomain evaluate)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private affine_tensor affine_power isMonHom_of_factor from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private geometricallyConnected_of_connected geometricallyIrreducible_of_connected
  smooth_geometricallyIrreducible_tensor geometry_of_smooth_geometricallyIrreducible from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

variable {k : Type u} [Field k] {G : GroupScheme k}

private abbrev GroupFactor (G : GroupScheme k) :=
  Σ H : AffineAlgebraicGroup k, H.val ⟶ G

private def familyDomain : List (GroupFactor G) → SchemeOver k
  | [] => 𝟙_ (SchemeOver k)
  | a :: l => a.1.val.X ⊗ familyDomain l

private def familyPoint : (l : List (GroupFactor G)) → (𝟙_ (SchemeOver k) ⟶ familyDomain l)
  | [] => 𝟙 _
  | a :: l => lift (η[a.1.val.X]) (familyPoint l)

private def familyMap : (l : List (GroupFactor G)) → (familyDomain l ⟶ G.X)
  | [] => 1
  | a :: l => (fst a.1.val.X (familyDomain l) ≫ a.2.hom.hom) *
    (snd a.1.val.X (familyDomain l) ≫ familyMap l)

private theorem familyPoint_map : ∀ l : List (GroupFactor G), familyPoint l ≫ familyMap l = 1 := by
  intro l
  induction l with
  | nil => exact Category.id_comp _
  | cons a l ih =>
    rw [familyMap, MonObj.comp_mul, familyPoint, lift_fst_assoc, lift_snd_assoc,
      IsMonHom.one_hom, MonObj.one_eq_one, ih, one_mul]

private theorem familyMap_affine : ∀ l : List (GroupFactor G), IsAffine (familyDomain l).left := by
  intro l
  induction l with
  | nil => change IsAffine (Spec (.of k)); infer_instance
  | cons a l ih =>
    have := a.1.property.1
    change IsAffine (a.1.val.X ⊗ familyDomain l).left
    exact affine_tensor

private theorem familyGroupFactor (a : GroupFactor G) (l : List (GroupFactor G)) (ha : a ∈ l) :
    ∃ j : a.1.val.X ⟶ familyDomain l, j ≫ familyMap l = a.2.hom.hom := by
  induction l with
  | nil => exact (List.not_mem_nil ha).elim
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · let j := lift (𝟙 a.1.val.X) (toUnit a.1.val.X ≫ familyPoint l)
      refine ⟨j, ?_⟩
      rw [familyMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        Category.id_comp, Category.assoc, familyPoint_map, MonObj.comp_one, mul_one]
    · obtain ⟨j, hj⟩ := ih ha'
      let p : a.1.val.X ⟶ familyDomain (b :: l) := lift (1 : _ ⟶ b.1.val.X) j
      refine ⟨p, ?_⟩
      change _ ≫ ((fst _ _ ≫ b.2.hom.hom) * (snd _ _ ≫ familyMap l)) = _
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, hj, one_mul]

set_option maxHeartbeats 750000 in
private theorem familyMap_mem (R : TestAlgebra k) (S : Subgroup (GroupPoints G R))
    (l : List (GroupFactor G))
    (hS : ∀ a ∈ l, ∀ x : GroupPoints a.1.val R, x ≫ a.2.hom.hom ∈ S)
    (p : Points (familyDomain l) R) : p ≫ familyMap l ∈ S := by
  induction l with
  | nil =>
    rw [familyMap, MonObj.comp_one]
    exact S.one_mem
  | cons a l ih =>
    rw [familyMap, MonObj.comp_mul]
    let p₁ : GroupPoints a.1.val R := p ≫ fst a.1.val.X (familyDomain l)
    let p₂ : Points (familyDomain l) R := p ≫ snd a.1.val.X (familyDomain l)
    have h₁ := hS a (List.mem_cons_self) p₁
    have h₂ := ih (fun b hb => hS b (List.mem_cons_of_mem _ hb)) p₂
    rw [← Category.assoc, ← Category.assoc]
    exact S.mul_mem h₁ h₂

private theorem familyMap_factors {N : GroupScheme k} (i : N ⟶ G)
    (l : List (GroupFactor G)) (h : ∀ a ∈ l, ∃ j : a.1.val ⟶ N, j ≫ i = a.2) :
    ∃ f : familyDomain l ⟶ N.X, f ≫ i.hom.hom = familyMap l := by
  induction l with
  | nil => exact ⟨1, MonObj.one_comp _⟩
  | cons a l ih =>
    obtain ⟨j, hj⟩ := h a List.mem_cons_self
    obtain ⟨q, hq⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨(fst a.1.val.X (familyDomain l) ≫ j.hom.hom) *
      (snd a.1.val.X (familyDomain l) ≫ q), ?_⟩
    rw [familyMap, MonObj.mul_comp, Category.assoc, Category.assoc, hq]
    have hj' : j.hom.hom ≫ i.hom.hom = a.2.hom.hom :=
      congrArg (fun m : a.1.val ⟶ G => m.hom.hom) hj
    rw [hj']

private theorem geometricallyIrreducible_field_identity :
    GeometricallyIrreducible (𝟙 (Spec (.of k))) := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => IrreducibleSpace X) (R := k)).mpr
  intro K _ _
  let r := fieldSpecMap k K
  let s := pullback.snd (𝟙 (Spec (.of k))) r
  have : IsIso s := inferInstanceAs (IsIso (pullback.snd (𝟙 _) r))
  exact s.homeomorph.irreducibleSpace_iff.mpr inferInstance

private theorem familyDomain_geometry [CharZero k] (l : List (GroupFactor G))
    (h : ∀ a ∈ l, ConnectedSpace a.1.val.X.left) :
    Smooth (familyDomain l).hom ∧ GeometricallyIrreducible (familyDomain l).hom := by
  induction l with
  | nil =>
    change Smooth (𝟙 (Spec (.of k))) ∧ GeometricallyIrreducible (𝟙 (Spec (.of k)))
    exact ⟨inferInstance, geometricallyIrreducible_field_identity⟩
  | cons a l ih =>
    have : ConnectedSpace a.1.val.X.left := h a List.mem_cons_self
    have := characteristicZeroSmoothness k a.1
    have := geometricallyIrreducible_of_connected a.1
    have h' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have := h'.1
    have := h'.2
    exact smooth_geometricallyIrreducible_tensor a.1.val.X (familyDomain l)

private theorem wordPower_geometry (X : SchemeOver k)
    [Smooth X.hom] [GeometricallyIrreducible X.hom] :
    ∀ m, Smooth (power X m).hom ∧ GeometricallyIrreducible (power X m).hom := by
  intro m
  induction m with
  | zero =>
    change Smooth (𝟙 (Spec (.of k))) ∧ GeometricallyIrreducible (𝟙 (Spec (.of k)))
    exact ⟨inferInstance, geometricallyIrreducible_field_identity⟩
  | succ m ih =>
    have := ih.1
    have := ih.2
    exact smooth_geometricallyIrreducible_tensor X (power X m)

set_option maxHeartbeats 850000 in
theorem finiteFamilyWordGroup
    [CharZero k] (G : AffineAlgebraicGroup k)
    (l : List (GroupFactor G.val)) (hl : ∀ a ∈ l, ConnectedSpace a.1.val.X.left) :
    ∃ (N : ClosedSubgroup G.val) (n : ℕ) (w : wordDomain (familyDomain l) n ⟶ N.group.X),
      0 < n ∧ IsIntegral N.group.X.left ∧ Smooth N.group.X.hom ∧
      GeometricallyConnected N.group.X.hom ∧
      IsAffine (wordDomain (familyDomain l) n).left ∧
      IsIntegral (wordDomain (familyDomain l) n).left ∧
      LocallyOfFiniteType w.left ∧ IsSchemeTheoreticallyDominant w.left ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        IsSchemeTheoreticallyDominant ((baseChange k K).map w).left) ∧
      (∀ a ∈ l, ∃ j : a.1.val ⟶ N.group, j ≫ N.inclusion = a.2) ∧
      (∀ M : ClosedSubgroup G.val, (∀ a ∈ l, ∃ j : a.1.val ⟶ M.group, j ≫ M.inclusion = a.2) →
        ∃ j : N.group ⟶ M.group, j ≫ M.inclusion = N.inclusion) ∧
      ∀ (S : SchemeOver k) (p : S ⟶ wordDomain (familyDomain l) n),
        p ≫ w ≫ N.inclusion.hom.hom = evaluate (familyMap l) n p := by
  let X := familyDomain l
  let f := familyMap l
  have hX : IsAffine X.left := familyMap_affine l
  have hgeom := familyDomain_geometry l hl
  have := hgeom.1
  have := hgeom.2
  have hPow (m : ℕ) := wordPower_geometry X m
  have hI (m : ℕ) : IsIntegral (power X m).left := by
    have := (hPow m).1
    have := (hPow m).2
    exact (geometry_of_smooth_geometricallyIrreducible (power X m)).2.2
  obtain ⟨N, n, w, hn, hN, hdom, hdomExt, ⟨a, ha⟩, hmin, he⟩ :=
    wordGeneratedGroup G X f (familyPoint l) hX (familyPoint_map l) hI
  let N' := closedSubgroupAlgebraicGroup N
  have : ConnectedSpace N'.val.X.left := by
    change ConnectedSpace N.group.X.left
    infer_instance
  have hft : LocallyOfFiniteType w.left := by
    have : LocallyOfFiniteType ((wordDomain X n).hom) := by
      have := (hPow (2*n)).1
      infer_instance
    have : LocallyOfFiniteType (w.left ≫ N.group.X.hom) := by
      rw [w.w]
      infer_instance
    exact locallyOfFiniteType_of_comp w.left N.group.X.hom
  have : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  have : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  refine ⟨N, n, w, hn, hN, characteristicZeroSmoothness k N',
    geometricallyConnected_of_connected N', affine_power _, hI _, hft, hdom, hdomExt, ?_, ?_, he⟩
  · intro b hb
    obtain ⟨j, hj⟩ := familyGroupFactor b l hb
    have eq : (j ≫ a) ≫ N.inclusion.hom.hom = b.2.hom.hom := by
      rw [Category.assoc, ha, hj]
    have := isMonHom_of_factor b.2 N.inclusion (j ≫ a) eq
    exact ⟨Grp.homMk (j ≫ a), Grp.hom_ext _ _ eq⟩
  · intro M hM
    exact hmin M (familyMap_factors M.inclusion l hM)

end WordFamilies


section WordExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup)
open Specs.FiniteWordClosure (wordDomain evaluate)
open Specs.AdjointRepresentation (GroupPoints)
open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private liftClosed liftClosed_fac isMonHom_of_factor ker_comp_eq from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {G : GroupScheme k}
variable {X : SchemeOver k} (f : X ⟶ G.X)

private theorem extendedWordPointFactors (M : ClosedSubgroup ((groupBaseChange k K).obj G))
    (b : (baseChange k K).obj X ⟶ M.group.X)
    (hb : b ≫ M.inclusion.hom.hom = (baseChange k K).map f)
    (R : TestAlgebra K) (n : ℕ)
    (p : Points (wordDomain X n) ((restrictTestAlgebra k K).obj R)) :
    ∃ q : GroupPoints M.group R,
      baseChangePoint k K G.X R (q ≫ M.inclusion.hom.hom) = evaluate f n p := by
  let A := (restrictTestAlgebra k K).obj R
  let e := baseChangePointGroupEquiv K G R
  have hLift (u : Points X A) :
      ∃ q : GroupPoints M.group R,
        e (q ≫ M.inclusion.hom.hom) = u ≫ f := by
    let v := (baseChangePointsEquiv K X R).symm u
    refine ⟨v ≫ b, ?_⟩
    change baseChangePoint k K G.X R ((v ≫ b) ≫ M.inclusion.hom.hom) = _
    rw [Category.assoc, hb, baseChangePointsSchemeNaturality]
    exact congrArg (· ≫ f) ((baseChangePointsEquiv K X R).apply_symm_apply u)
  induction n with
  | zero =>
    refine ⟨1, ?_⟩
    change e ((1 : GroupPoints M.group R) ≫ M.inclusion.hom.hom) = 1
    rw [MonObj.one_comp, map_one]
  | succ n ih =>
    let a := p ≫ fst X (X ⊗ wordDomain X n)
    let z := p ≫ snd X (X ⊗ wordDomain X n)
    let b := z ≫ fst X (wordDomain X n)
    let r := z ≫ snd X (wordDomain X n)
    obtain ⟨a', ha'⟩ := hLift a
    obtain ⟨b', hb'⟩ := hLift b
    obtain ⟨r', hr'⟩ := ih r
    refine ⟨a' * b'⁻¹ * r', ?_⟩
    let a₀ : GroupPoints G A := a ≫ f
    let b₀ : GroupPoints G A := b ≫ f
    let v : GroupPoints G A := evaluate f n r
    change e ((a' * b'⁻¹ * r') ≫ M.inclusion.hom.hom) = a₀ * b₀⁻¹ * v
    have h₁ : e (a' ≫ M.inclusion.hom.hom) = a₀ := ha'
    have h₂ : e (b' ≫ M.inclusion.hom.hom) = b₀ := hb'
    have h₃ : e (r' ≫ M.inclusion.hom.hom) = v := hr'
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, map_mul, map_mul, map_inv, h₁, h₂, h₃]

set_option maxHeartbeats 850000 in
theorem extendedWordImageMinimal
    (N : ClosedSubgroup G) (n : ℕ) (w : wordDomain X n ⟶ N.group.X)
    (hX : IsAffine (wordDomain X n).left)
    (hdom : IsSchemeTheoreticallyDominant ((baseChange k K).map w).left)
    (hw : ∀ (S : SchemeOver k) (p : S ⟶ wordDomain X n),
      p ≫ w ≫ N.inclusion.hom.hom = evaluate f n p)
    (M : ClosedSubgroup ((groupBaseChange k K).obj G))
    (b : (baseChange k K).obj X ⟶ M.group.X)
    (hb : b ≫ M.inclusion.hom.hom = (baseChange k K).map f) :
    ∃ j : (groupBaseChange k K).obj N.group ⟶ M.group,
      j ≫ M.inclusion = (groupBaseChange k K).map N.inclusion := by
  let F := groupBaseChange k K
  let wK := (baseChange k K).map w
  let i := (F.map N.inclusion).hom.hom
  let j := M.inclusion.hom.hom
  have hAff : IsAffine ((baseChange k K).obj (wordDomain X n)).left :=
    inferInstanceAs (IsAffine (pullback (wordDomain X n).hom (fieldSpecMap k K)))
  obtain ⟨B, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of K)).mpr hAff
  let R := B.unop
  let p : Points ((baseChange k K).obj (wordDomain X n)) R := e.hom
  let p' := baseChangePoint k K (wordDomain X n) R p
  obtain ⟨q, hq⟩ := extendedWordPointFactors f M b hb R n p'
  have hpoints : q ≫ j = p ≫ wK ≫ i := by
    apply (baseChangePoints k K G.X R).injective
    change baseChangePoint k K G.X R (q ≫ M.inclusion.hom.hom) =
      baseChangePoint k K G.X R
        (p ≫ (baseChange k K).map w ≫ (baseChange k K).map N.inclusion.hom.hom)
    rw [← Category.assoc, baseChangePointsSchemeNaturality, baseChangePointsSchemeNaturality, hq]
    exact (hw _ p').symm
  have hfac : (e.inv ≫ q) ≫ j = wK ≫ i := by
    rw [Category.assoc, hpoints, ← Category.assoc, show p = e.hom from rfl, e.inv_hom_id, Category.id_comp]
  have : IsSchemeTheoreticallyDominant wK.left := hdom
  have hk : j.left.ker ≤ i.left.ker := by
    rw [← ker_comp_eq wK i, ← hfac, Over.comp_left]
    exact (e.inv ≫ q).left.le_ker_comp j.left
  have : IsClosedImmersion j.left := M.isClosedImmersion
  have : Mono j := Over.mono_of_mono_left _
  let t := liftClosed j i hk
  have ht := liftClosed_fac j i hk
  have := isMonHom_of_factor (F.map N.inclusion) M.inclusion t ht
  exact ⟨Grp.homMk t, Grp.hom_ext _ _ ht⟩

end WordExtension


section FamilyLieComparison

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup Lie GroupScheme)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.StandardGroups (generalLinearPoints)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open InfinitesimalCommutator (matrixDifferential)

open private matrixDifferentialLinear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]

omit [CharZero k] in
private theorem matrixDifferential_comp {A H G : GroupScheme k}
    (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (i : H ⟶ G) (j : A ⟶ H) (p : Lie k A) :
    matrixDifferential i g (mapPointKernel j p) = matrixDifferential (j ≫ i) g p := by
  have h : (mapPointKernel i (mapPointKernel j p)).toMul.val =
      (mapPointKernel (j ≫ i) p).toMul.val := by
    let F := groupPointsFunctor k
    have eq := F.map_comp j i
    exact (congrArg (fun s : F.obj A ⟶ F.obj G =>
      (s.app (CommAlgCat.of k (DualNumber k))).hom p.toMul.val) eq).symm
  unfold matrixDifferential
  rw [h]

set_option maxHeartbeats 950000 in
/-- A finite connected family generates a group with the prescribed Lie image
when its tangents span that image and its conjugations preserve it. -/
theorem finiteFamilyMatrixLie
    (G : AffineAlgebraicGroup k) (g : (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k J)
    (l : List (GroupFactor G.val)) (hc : ∀ a ∈ l, ConnectedSpace a.1.val.X.left)
    (L : Submodule k (Matrix J J k))
    (hL : ∀ (K : Type u) [Field K] [Algebra k K], ∀ a ∈ l,
      ∀ p : GroupPoints a.1.val (CommAlgCat.of k (DualNumber K)),
        (p ≫ a.2.hom.hom) ∈ matrixPointsWithTangents (K := K) g L)
    (hspan : L ≤ Submodule.span k {M | ∃ a ∈ l, ∃ p : Lie k a.1.val,
      matrixDifferential a.2 g p = M}) :
    ∃ N : ClosedSubgroup G.val,
      Smooth N.group.X.hom ∧ GeometricallyConnected N.group.X.hom ∧
      (∀ a ∈ l, ∃ j : a.1.val ⟶ N.group, j ≫ N.inclusion = a.2) ∧
      (∀ M : ClosedSubgroup G.val, (∀ a ∈ l, ∃ j : a.1.val ⟶ M.group, j ≫ M.inclusion = a.2) →
        ∃ j : N.group ⟶ M.group, j ≫ M.inclusion = N.inclusion) ∧
      Set.range (matrixDifferential N.inclusion g) = (L : Set (Matrix J J k)) := by
  obtain ⟨N, n, w, _, hn, hs, hgeom, haff, hint, hft, hdom, _, hfac, hmin, heval⟩ :=
    finiteFamilyWordGroup G l hc
  let N' := closedSubgroupAlgebraicGroup N
  have : IsAffine N.group.X.left := N'.property.1
  have hf : ∀ (K : Type u) [Field K] [Algebra k K],
      ∀ p : Points (familyDomain l) (CommAlgCat.of k (DualNumber K)),
        (p ≫ familyMap l) ∈ matrixPointsWithTangents (K := K) g L := by
    intro K _ _ p
    exact familyMap_mem _ _ l (hL K) p
  have hup :=
    wordMatrixLieBound_of_membership g N.inclusion (familyMap l) n w heval L hf
  let d := matrixDifferentialLinear N.inclusion g
  have hd : ⇑d = matrixDifferential N.inclusion g := rfl
  have hle : LinearMap.range d ≤ L := by
    rintro _ ⟨p, rfl⟩
    exact hup p
  have hge : L ≤ LinearMap.range d := hspan.trans (Submodule.span_le.mpr (by
    rintro m ⟨a, ha, p, hp⟩
    obtain ⟨j, hj⟩ := hfac a ha
    refine ⟨mapPointKernel j p, ?_⟩
    change matrixDifferential N.inclusion g (mapPointKernel j p) = m
    rw [matrixDifferential_comp, hj, hp]))
  exact ⟨N, hs, hgeom, hfac, hmin, hd ▸ (SetLike.coe_set_eq.mpr (le_antisymm hle hge))⟩

end FamilyLieComparison


section MatrixRootOperators

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (generator rationalWeightSpace rationalCharacter)
open RootData (integralCartan rationalRootAnnihilator)

section RootOperators

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 950000 in
/-- Choose a nonzero matrix in each root line, retaining the prescribed
Cartan matrix and the opposite-root bracket. -/
theorem rationalRootOperators : Specs.RationalRealization.RationalRootOperators.{u} := by
  classical
  intro D _
  let A := integralCartan D.datum D.base
  let V := Matrix.ToLieAlgebra ℚ A
  let Z := rationalRootAnnihilator D.datum
  let H := rationalWeightSpace A 0
  let W (i : D.I) := rationalWeightSpace A (fun j => D.datum.pairing i j)
  obtain ⟨J, _, _, w, e, ρ, hLie, he, _, hw, hd, hinj, hr⟩ := rationalMatrixAction D
  let j : H × Z →ₗ[ℚ] V × Z := H.subtype.prodMap (LinearMap.id (R := ℚ) (M := Z))
  let d := ρ.comp (j.comp e.symm.toLinearMap)
  have hde (h : H) (z : Z) : d (e (h, z)) = ρ (h.val, z) := by
    change ρ (j (e.symm (e (h, z)))) = _
    rw [e.symm_apply_apply]
    rfl
  have hdiag (y : ℚ ⊗[ℤ] D.Y) :
      d y = Matrix.diagonal fun a => rationalCharacter D (w a) y := by
    obtain ⟨⟨h, z⟩, rfl⟩ := e.surjective y
    exact (hde h z).trans (hd h z)
  have hj : Function.Injective j := Prod.map_injective.mpr ⟨H.injective_subtype, Function.injective_id⟩
  have hdinj : Function.Injective d := hinj.comp (hj.comp e.symm.injective)
  have heach (i : D.I) : ∃ v : W i, v ≠ 0 := by
    have hf : Module.finrank ℚ (W i) = 1 := (rationalSerreDecomposition D).2.1 i
    rcases subsingleton_or_nontrivial (W i) with hs | hs
    · rw [Module.finrank_eq_zero_of_subsingleton ℚ (W i)] at hf
      exact (Nat.zero_ne_one hf).elim
    · exact exists_ne (0 : W i)
  choose v hv using heach
  have hv₀ (i : D.I) : (v i : V) ≠ 0 := fun h => hv i (Subtype.ext h)
  let N (i : D.I) := ρ ((v i : V), 0)
  let L := LinearMap.range ρ
  let L' := LinearMap.range d ⊔ ⨆ i, ℚ ∙ N i
  have hsub : L' ≤ L := by
    refine sup_le ?_ (iSup_le fun i => ?_)
    · rintro _ ⟨y, rfl⟩
      exact ⟨j (e.symm y), rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ rfl
      exact ⟨((v i : V), 0), rfl⟩
  have hW (i : D.I) (x : V) (hx : x ∈ W i) : ρ (x, 0) ∈ L' := by
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
      ((rationalSerreDecomposition D).2.1 i) (hv i) (⟨x, hx⟩ : W i)
    have hc' : x = c • (v i : V) := (congrArg Subtype.val hc).symm
    apply (le_iSup (fun i => ℚ ∙ N i) i).trans le_sup_right
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    change c • ρ ((v i : V), 0) = _
    rw [← ρ.map_smul]
    congr 1
    exact Prod.ext hc'.symm (smul_zero _)
  have hall (x : V × Z) : ρ x ∈ L' := by
    have hs : x.1 ∈ H ⊔ ⨆ i, W i := (rationalSerreDecomposition D).1.symm ▸ Submodule.mem_top
    obtain ⟨h, hh, s, hs, heq⟩ := Submodule.mem_sup.mp hs
    have hh' : ρ (h, x.2) ∈ L' :=
      Submodule.mem_sup.mpr ⟨_, ⟨e (⟨h, hh⟩, x.2), hde ⟨h, hh⟩ x.2⟩,
        0, Submodule.zero_mem _, add_zero _⟩
    have hs' : ρ (s, 0) ∈ L' := by
      refine Submodule.iSup_induction W (motive := fun z => ρ (z, 0) ∈ L') hs hW ?_ ?_
      · rw [show ((0 : V), (0 : Z)) = 0 from rfl, ρ.map_zero]
        exact L'.zero_mem
      · intro y z hy hz
        rw [show ((y + z, 0) : V × Z) = (y, 0) + (z, 0) from by simp, ρ.map_add]
        exact L'.add_mem hy hz
    have hx : x = (h, x.2) + (s, 0) := Prod.ext heq.symm (add_zero x.2).symm
    rw [hx, ρ.map_add]
    exact L'.add_mem hh' hs'
  have hL' : L = L' := le_antisymm (by rintro _ ⟨x, rfl⟩; exact hall x) hsub
  refine ⟨J, inferInstance, inferInstance, w, d, N, L, hw, hdinj, hdiag, hL', ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨(⁅x.1, y.1⁆, 0), hLie x y⟩
  · intro i
    have hi : N i ≠ 0 := by
      intro eq
      apply hv₀ i
      have h := hinj (eq.trans ρ.map_zero.symm)
      exact congrArg Prod.fst h
    obtain ⟨hs, hn⟩ := hr i (v i) (v i).property
    exact ⟨hi, hn, hs⟩
  · intro i
    let i' := D.datum.reflectionPerm i i
    obtain ⟨t, c, hc, ht, hc'⟩ := rationalCorootBracket D e he i
      (v i) (v i') (v i).property (v i').property (hv₀ i) (hv₀ i')
    refine ⟨c, hc, ?_⟩
    show ⁅N i, N i'⁆ = _
    change ⁅ρ ((v i : V), 0), ρ ((v i' : V), 0)⁆ = _
    rw [← hLie, ← ht, ← hde, hc', d.map_smul]

end RootOperators


end MatrixRootOperators

section RankOneConjugation

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K A : Type u} [Field K] [CharZero K] [Ring A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ K A]

private def innerExp (n : A) : A →ₗ[K] A :=
  (LinearMap.mulRight K (IsNilpotent.exp (-n))).comp (LinearMap.mulLeft K (IsNilpotent.exp n))

omit [CharZero K] [IsScalarTower ℚ K A] in
private theorem innerExp_apply (n x : A) :
    innerExp (K := K) n x = IsNilpotent.exp n * x * IsNilpotent.exp (-n) := rfl

set_option maxHeartbeats 650000 in
private theorem innerExp_apply_of_lie_cube_zero
    (n : A) (hn : IsNilpotent n) (x : A) (hc : ⁅n, ⁅n, ⁅n, x⁆⁆⁆ = 0) :
    innerExp (K := K) n x = x + ⁅n, x⁆ + (2⁻¹ : K) • ⁅n, ⁅n, x⁆⁆ := by
  obtain ⟨D, hD, hcomm, he⟩ := exponentialAdjoint n hn
  have hD' (y : A) : D y = ⁅n, y⁆ := hcomm y
  have hpow : (D ^ 3) x = 0 := by
    rw [pow_succ', pow_succ', pow_one, Module.End.mul_apply, Module.End.mul_apply]
    simp only [hD', hc]
  rw [innerExp_apply, ← he]
  change IsNilpotent.exp D • x = _
  rw [IsNilpotent.exp_smul_eq_sum hpow hD]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, inv_one,
    zero_add, pow_zero, pow_one, one_smul]
  change x + D x + (2 : ℚ)⁻¹ • ((D ^ 2) x) = _
  rw [pow_two, Module.End.mul_apply]
  simp only [hD']
  rw [← IsScalarTower.algebraMap_smul K ((2 : ℚ)⁻¹) _, map_inv₀, map_ofNat]

set_option maxHeartbeats 700000 in
theorem rankOneWordCartan
    (H E F : A) (hE : ⁅H, E⁆ = (2 : K) • E) (hF : ⁅H, F⁆ = (-2 : K) • F)
    (a : K) (hEF : ⁅E, F⁆ = a • H)
    (hEnil : IsNilpotent E) (hFnil : IsNilpotent F) :
    innerExp (K := K) E (innerExp (K := K) (-F) (innerExp (K := K) E H)) =
      (1 - 4 * a + 2 * a ^ 2) • H + (-4 + 6 * a - 2 * a ^ 2) • E +
        (2 * a - 2) • F := by
  have hEH : ⁅E, H⁆ = (-2 : K) • E := by rw [← lie_skew E H, hE, neg_smul]
  have hFH : ⁅-F, H⁆ = (-2 : K) • F := by rw [neg_lie, ← lie_skew F H, neg_neg, hF]
  have hFE : ⁅-F, E⁆ = a • H := by rw [neg_lie, lie_skew E F, hEF]
  have hEEH : ⁅E, ⁅E, H⁆⁆ = 0 := by rw [hEH, (lie_smul (R := K)), lie_self, smul_zero]
  have hFFH : ⁅-F, ⁅-F, H⁆⁆ = 0 := by rw [hFH, (lie_smul (R := K)), neg_lie, lie_self, neg_zero, smul_zero]
  have hEEF : ⁅E, ⁅E, F⁆⁆ = (-2 * a) • E := by rw [hEF, (lie_smul (R := K)), hEH, smul_smul, mul_comm]
  have hFFE : ⁅-F, ⁅-F, E⁆⁆ = (-2 * a) • F := by rw [hFE, (lie_smul (R := K)), hFH, smul_smul, mul_comm]
  have h1 : innerExp (K := K) E H = H + (-2 : K) • E := by
    rw [innerExp_apply_of_lie_cube_zero E hEnil H (by rw [hEEH, lie_zero]), hEEH, hEH,
      smul_zero, add_zero]
  have h2 : innerExp (K := K) (-F) H = H + (-2 : K) • F := by
    rw [innerExp_apply_of_lie_cube_zero (-F) hFnil.neg H (by rw [hFFH, lie_zero]),
      hFFH, hFH, smul_zero, add_zero]
  have h3 : innerExp (K := K) E F = F + a • H - a • E := by
    rw [innerExp_apply_of_lie_cube_zero E hEnil F (by rw [hEEF, (lie_smul (R := K)), lie_self, smul_zero]),
      hEEF, hEF, smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 1
    congr 1
    field_simp
  have h4 : innerExp (K := K) (-F) E = E + a • H - a • F := by
    rw [innerExp_apply_of_lie_cube_zero (-F) hFnil.neg E
      (by rw [hFFE, (lie_smul (R := K)), neg_lie, lie_self, neg_zero, smul_zero]),
      hFFE, hFE, smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 1
    congr 1
    field_simp
  have h5 : innerExp (K := K) E E = E := by
    rw [innerExp_apply_of_lie_cube_zero E hEnil E (by simp [lie_self])]
    simp
  rw [h1, map_add, map_smul, h2, h4]
  simp only [map_add, map_sub, map_smul, h1, h3, h5]
  module

set_option maxHeartbeats 750000 in
theorem rankOneWordReflection
    (H E F : A) (hE : ⁅H, E⁆ = (2 : K) • E) (hF : ⁅H, F⁆ = (-2 : K) • F)
    (hEF : ⁅E, F⁆ = H) (hEnil : IsNilpotent E) (hFnil : IsNilpotent F)
    (x : A) (a : K) (hxE : ⁅x, E⁆ = a • E) (hxF : ⁅x, F⁆ = -a • F) :
    innerExp (K := K) E (innerExp (K := K) (-F) (innerExp (K := K) E x)) =
      x - a • H := by
  let C := (innerExp (K := K) E).comp ((innerExp (K := K) (-F)).comp (innerExp (K := K) E))
  have hCH : C H = -H := by
    change innerExp (K := K) E (innerExp (K := K) (-F) (innerExp (K := K) E H)) = _
    rw [rankOneWordCartan H E F hE hF 1 (by simpa using hEF) hEnil hFnil]
    norm_num
  let b := a / 2
  have hb : b * 2 = a := by dsimp [b]; field_simp
  let z := x - b • H
  have hzE : ⁅E, z⁆ = 0 := by
    change ⁅E, x - b • H⁆ = 0
    rw [← lie_skew E (x - b • H), sub_lie, (smul_lie (R := K)), hxE, hE, smul_smul,
      hb, sub_self, neg_zero]
  have hzF : ⁅-F, z⁆ = 0 := by
    change ⁅-F, x - b • H⁆ = 0
    rw [neg_lie, ← lie_skew F (x - b • H), neg_neg, sub_lie, (smul_lie (R := K)),
      hxF, hF, smul_smul, mul_neg, hb, sub_self]
  have hCz : C z = z := by
    have h₁ : innerExp (K := K) E z = z := by
      rw [innerExp_apply_of_lie_cube_zero E hEnil z (by simp [hzE]), hzE, lie_zero,
        smul_zero, add_zero, add_zero]
    have h₂ : innerExp (K := K) (-F) z = z := by
      rw [innerExp_apply_of_lie_cube_zero (-F) hFnil.neg z (by simp [hzF]), hzF, lie_zero,
        smul_zero, add_zero, add_zero]
    change innerExp (K := K) E (innerExp (K := K) (-F) (innerExp (K := K) E z)) = _
    rw [h₁, h₂, h₁]
  change C x = x - a • H
  calc
    C x = C (z + b • H) := by rw [show z + b • H = x from sub_add_cancel _ _]
    _ = z - b • H := by rw [map_add, map_smul, hCz, hCH, smul_neg, sub_eq_add_neg]
    _ = x - a • H := by
      change x - b • H - b • H = _
      rw [sub_sub, ← add_smul, ← mul_two b, hb]

end RankOneConjugation

section MatchingRootScalars

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K J : Type u} [Field K] [CharZero K] [Fintype J] [DecidableEq J]

set_option maxHeartbeats 750000 in
/-- The opposite support entry forces the scalar of the rank-one bracket. -/
theorem rankOneWordForcesNormalization
    (H E F : Matrix J J K) (hE : ⁅H, E⁆ = (2 : K) • E) (hF : ⁅H, F⁆ = (-2 : K) • F)
    (c : K) (hc : ⁅E, F⁆ = c • H) (hEnil : IsNilpotent E) (hFnil : IsNilpotent F)
    (i j : J) (hH : H i j = 0) (hE₀ : E i j = 0) (hF₀ : F i j ≠ 0)
    (hdiag : (innerExp (K := K) E (innerExp (K := K) (-F) (innerExp (K := K) E H))) i j = 0) :
    c = 1 := by
  have h := congrArg (fun M : Matrix J J K => M i j) (rankOneWordCartan H E F hE hF c hc hEnil hFnil)
  rw [hdiag, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.smul_apply, hH, hE₀, smul_zero, smul_zero, zero_add, zero_add, smul_eq_mul] at h
  have h₂ : 2 * c - 2 = 0 := (mul_eq_zero.mp h.symm).resolve_right hF₀
  apply mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0)
  rw [mul_one]
  exact sub_eq_zero.mp h₂

end MatchingRootScalars


section PositiveCocharacters

open scoped Matrix

open Specs.Pinning (BasedRootDatum)

set_option maxHeartbeats 550000 in
theorem positiveIntegralCocharacter : Specs.RationalRealization.PositiveIntegralCocharacter.{u} := by
  classical
  intro D
  let : Finite D.I := D.finiteRoots
  let : Module.Free ℤ D.X := D.freeX
  let : Module.Free ℤ D.Y := D.freeY
  let : Module.Finite ℤ D.X := D.finiteX
  let : Module.Finite ℤ D.Y := D.finiteY
  let : D.datum.IsReduced := D.reduced
  let A := RootData.integralCartan D.datum D.base
  let B := A.transpose
  have hdet : A.det ≠ 0 := by
    have hunit := (RootData.rationalComplement D.datum D.base).1
    rw [← RingHom.map_det] at hunit
    intro hz
    rw [hz, map_zero] at hunit
    exact not_isUnit_zero hunit
  have hdetB : B.det ≠ 0 := by simpa only [B, Matrix.det_transpose] using hdet
  let v : D.base.support → ℤ := B.det • B.cramer (fun _ => 1)
  let y := ∑ j : D.base.support, v j • D.datum.coroot j
  let m := B.det * B.det
  have hpos : 0 < m := mul_self_pos.mpr hdetB
  have hm : B *ᵥ v = fun _ => m := by
    rw [show v = B.det • B.cramer (fun _ => 1) from rfl, Matrix.mulVec_smul,
      Matrix.mulVec_cramer, smul_smul]
    funext i
    change (B.det * B.det) * (1 : ℤ) = m
    simp [m]
  have hsimple (i : D.base.support) : D.datum.root' i y = m := by
    change D.datum.root' i (∑ j : D.base.support, v j • D.datum.coroot j) = m
    simp only [map_sum, map_zsmul, D.datum.root_coroot_eq_pairing, zsmul_eq_mul]
    calc
      _ = (B *ᵥ v) i := by
        change ∑ j : D.base.support, v j * D.datum.pairing i j =
          ∑ j : D.base.support, D.datum.pairing i j * v j
        simp only [mul_comm]
      _ = m := congrFun hm i
  refine ⟨y, m, hpos, fun i => ?_⟩
  obtain ⟨f, _, _, hf⟩ := D.base.exists_root_eq_sum_int i
  rw [D.base.height_eq_sum hf]
  change D.datum.toLinearMap (D.datum.root i) y = _
  rw [hf]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change f j * D.datum.root' j y = m * f j
  rw [hsimple ⟨j, hj⟩, mul_comm]


end PositiveCocharacters

section GeneratorTangents

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme Lie)
open Specs.AdjointRepresentation (GroupPoints reduction)
open Specs.StandardGroups (generalLinearPoints additivePoints)
open Specs.DiagonalizableGroups (characterValuedPoints)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.RationalRealization (exponentialMatrix)
open InfinitesimalCommutator (matrixDifferential)

variable {k J X : Type u} [Field k] [Fintype J] [DecidableEq J] [AddCommGroup X]

private def onePlusInfinitesimal : Multiplicative k →* (DualNumber k)ˣ where
  toFun a :=
    { val := (1, a.toAdd)
      inv := (1, -a.toAdd)
      val_inv := by apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul]
      inv_val := by apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul] }
  map_one' := by apply Units.ext; exact rfl
  map_mul' a b := by
    apply Units.ext
    apply TrivSqZeroExt.ext
    · exact (one_mul (1 : k)).symm
    · change (a.toAdd + b.toAdd) = 1 * b.toAdd + a.toAdd * 1
      simp only [one_mul, mul_one, add_comm]

set_option maxHeartbeats 850000 in
/-- The infinitesimal characters of a diagonal torus give all of its
diagonal weight matrices in the ambient matrix Lie algebra. -/
theorem diagonalMatrixTangents {T G : GroupScheme k}
    (t : T ⟶ G) (w : J → X)
    (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (θ : (groupPointsFunctor k).obj T ≅ characterValuedPoints k (Multiplicative X))
    (h : ∀ (R : TestAlgebra k) (p : GroupPoints T R),
      ((g.hom.app R).hom (p ≫ t.hom.hom)).val = Matrix.diagonal (fun i =>
        ((show Multiplicative X →* Rˣ from (θ.hom.app R).hom p) (Multiplicative.ofAdd (w i))).val))
    (φ : X →ₗ[ℤ] k) :
    ∃ p : Lie k T, matrixDifferential t g p = Matrix.diagonal (fun i => φ (w i)) := by
  let k₀ := CommAlgCat.of k k
  let kε := CommAlgCat.of k (DualNumber k)
  let χ : Multiplicative X →* (DualNumber k)ˣ :=
    onePlusInfinitesimal.comp φ.toAddMonoidHom.toMultiplicative
  let p : GroupPoints T kε := (θ.inv.app kε).hom χ
  have hp : (θ.hom.app kε).hom p = χ := Iso.inv_hom_id_app_apply θ kε χ
  have hred : (((groupPointsFunctor k).obj T).map (reduction k₀)).hom p = 1 := by
    apply (ConcreteCategory.bijective_of_isIso (θ.hom.app k₀)).1
    rw [map_one]
    have hnat := congrArg (fun f : _ ⟶ (characterValuedPoints k (Multiplicative X)).obj k₀ => f p)
      (θ.hom.naturality (reduction k₀))
    change (θ.hom.app k₀).hom ((((groupPointsFunctor k).obj T).map (reduction k₀)).hom p) =
      ((characterValuedPoints k (Multiplicative X)).map (reduction k₀)).hom
        ((θ.hom.app kε).hom p) at hnat
    rw [hnat, hp]
    apply MonoidHom.ext
    intro x
    exact Units.ext rfl
  let p' : Lie k T := Additive.ofMul ⟨p, hred⟩
  refine ⟨p', ?_⟩
  have hm := h kε p
  change ((g.hom.app kε).hom (p ≫ t.hom.hom)).val =
    Matrix.diagonal (fun i => ((show Multiplicative X →* (DualNumber k)ˣ from (θ.hom.app kε).hom p) (Multiplicative.ofAdd (w i))).val) at hm
  rw [hp] at hm
  ext i j
  change (((g.hom.app kε).hom (p ≫ t.hom.hom)).val i j).snd = _
  rw [hm]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    rfl
  · simp only [Matrix.diagonal_apply_ne _ hij, TrivSqZeroExt.snd_zero]

set_option maxHeartbeats 750000 in
/-- Differentiating the polynomial exponential at the standard additive
coordinate recovers its original nilpotent matrix. -/
theorem rootExponentialTangent [CharZero k] {A : AdditiveLine k} {G : GroupScheme k}
    (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (b : (groupPointsFunctor k).obj A.group ≅ additivePoints k)
    (hb : ∀ (R : TestAlgebra k) (t : R), b.hom.app R (rootPoint (𝟙 A.group) R t) = Multiplicative.ofAdd t)
    (N : Matrix J J k) (x : A.group ⟶ G)
    (hx : ∀ (R : TestAlgebra k) (t : R),
      ((g.hom.app R).hom (rootPoint x R t)).val = exponentialMatrix N R t) :
    ∃ p : Lie k A.group, matrixDifferential x g p = N := by
  let k₀ := CommAlgCat.of k k
  let kε := CommAlgCat.of k (DualNumber k)
  let p : GroupPoints A.group kε := rootPoint (𝟙 A.group) kε DualNumber.eps
  have hp : (b.hom.app kε).hom p = Multiplicative.ofAdd (DualNumber.eps : DualNumber k) :=
    hb kε DualNumber.eps
  have hred : (((groupPointsFunctor k).obj A.group).map (reduction k₀)).hom p = 1 := by
    apply (ConcreteCategory.bijective_of_isIso (b.hom.app k₀)).1
    rw [map_one]
    have hnat := congrArg (fun f : _ ⟶ (additivePoints k).obj k₀ => f p)
      (b.hom.naturality (reduction k₀))
    change (b.hom.app k₀).hom ((((groupPointsFunctor k).obj A.group).map (reduction k₀)).hom p) =
      ((additivePoints k).map (reduction k₀)).hom ((b.hom.app kε).hom p) at hnat
    rw [hnat, hp]
    rfl
  refine ⟨Additive.ofMul ⟨p, hred⟩, ?_⟩
  have ep : (DualNumber.eps : DualNumber k) ^ 2 = 0 := by rw [pow_two, DualNumber.eps_mul_eps]
  have eq : p ≫ x.hom.hom = rootPoint x kε DualNumber.eps := by
    let ev : Points A.group.X kε := (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval (DualNumber.eps : kε))).op
    change (ev ≫ 𝟙 A.group.X) ≫ x.hom.hom = ev ≫ x.hom.hom
    exact congrArg (fun q : Points A.group.X kε => q ≫ x.hom.hom) (Category.comp_id ev)
  ext i j
  change (((g.hom.app kε).hom (p ≫ x.hom.hom)).val i j).snd = N i j
  rw [eq, hx, exponentialMatrix_of_sq_zero N kε ep, Matrix.add_apply, Matrix.smul_apply]
  rw [TrivSqZeroExt.snd_add]
  rw [show (((1 : Matrix J J (DualNumber k)) i j).snd) = 0 by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij], zero_add]
  change ((DualNumber.eps : DualNumber k) * TrivSqZeroExt.inl (N i j)).snd = N i j
  simp

end GeneratorTangents


section LatticeMatrices

open Specs.RationalRealization (integralWeightDiagonal latticeMatrixSpan)

section CoefficientExtension

variable {k : Type v} {K J : Type u} [Field k] [Field K] [Algebra k K]
  [Fintype J] [DecidableEq J]

/-- Extending coefficients commutes with taking the span of a set of matrices. -/
theorem matrixSpanExtension_span (s : Set (Matrix J J k)) :
    Submodule.span K ((algebraMap k K).mapMatrix '' (Submodule.span k s : Set (Matrix J J k))) =
      Submodule.span K ((algebraMap k K).mapMatrix '' s) := by
  let f : Matrix J J k →ₛₗ[algebraMap k K] Matrix J J K :=
    { toFun := (algebraMap k K).mapMatrix
      map_add' := map_add _
      map_smul' := by intro c M; ext i j; exact map_mul (algebraMap k K) c (M i j) }
  apply le_antisymm
  · exact Submodule.span_le.mpr (Submodule.image_span_subset_span f s)
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

omit [Algebra k K] in
private theorem mapMatrix_diagonal (f : k →+* K) (d : J → k) :
    f.mapMatrix (Matrix.diagonal d) = Matrix.diagonal (f ∘ d) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [RingHom.mapMatrix_apply]
  · simp [RingHom.mapMatrix_apply, Matrix.diagonal_apply_ne _ h]

/-- A bracket-closed matrix subspace remains bracket-closed after scalar extension. -/
theorem matrixSpanExtension_bracket (L : Submodule k (Matrix J J k))
    (hL : ∀ x ∈ L, ∀ y ∈ L, x * y - y * x ∈ L) :
    let E := Submodule.span K ((algebraMap k K).mapMatrix '' (L : Set (Matrix J J k)))
    ∀ x ∈ E, ∀ y ∈ E, x * y - y * x ∈ E := by
  let E := Submodule.span K ((algebraMap k K).mapMatrix '' (L : Set (Matrix J J k)))
  let f : Matrix J J k →+* Matrix J J K := (algebraMap k K).mapMatrix
  have hmap (x : Matrix J J k) (hx : x ∈ L) (y : Matrix J J K) (hy : y ∈ E) :
      f x * y - y * f x ∈ E := by
    refine Submodule.span_induction (p := fun y _ => f x * y - y * f x ∈ E) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨z, hz, rfl⟩
      change f x * f z - f z * f x ∈ E
      rw [← f.map_mul, ← f.map_mul, ← f.map_sub]
      exact Submodule.subset_span ⟨x * z - z * x, hL x hx z hz, rfl⟩
    · simpa only [mul_zero, zero_mul, sub_zero] using E.zero_mem
    · intro a b _ _ ha hb
      rw [mul_add, add_mul, add_sub_add_comm]
      exact E.add_mem ha hb
    · intro a b _ hb
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
      exact E.smul_mem a hb
  dsimp only
  intro x hx y hy
  change x * y - y * x ∈ E
  refine Submodule.span_induction (p := fun x _ => x * y - y * x ∈ E) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨z, hz, rfl⟩
    exact hmap z hz y hy
  · simpa only [mul_zero, zero_mul, sub_zero] using E.zero_mem
  · intro a b _ _ ha hb
    rw [add_mul, mul_add, add_sub_add_comm]
    exact E.add_mem ha hb
  · intro a b _ hb
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact E.smul_mem a hb

end CoefficientExtension

section LatticeMatrixSpan

variable {k : Type v} {X J I : Type u} [Field k] [AddCommGroup X] [DecidableEq J]

/-- The diagonal subspace for the weights of a lattice representation. -/
def weightDiagonal (w : J → X) : (X →ₗ[ℤ] k) →ₗ[k] Matrix J J k where
  toFun φ := Matrix.diagonal fun j => φ (w j)
  map_add' a b := by
    change Matrix.diagonal (fun j => a (w j) + b (w j)) = _
    exact (Matrix.diagonal_add (fun j => a (w j)) (fun j => b (w j))).symm
  map_smul' c a := by
    change Matrix.diagonal (fun j => c • a (w j)) = _
    exact Matrix.diagonal_smul c (fun j => a (w j))

theorem span_integralWeightDiagonal [Module.Free ℤ X] [Module.Finite ℤ X] (w : J → X) :
    Submodule.span k (Set.range (integralWeightDiagonal k w)) =
      LinearMap.range (weightDiagonal (k := k) w) := by
  classical
  let e := weightDiagonal (k := k) w
  let S := Submodule.span k (Set.range (integralWeightDiagonal k w))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact ⟨(Int.castAddHom k).toIntLinearMap.comp l, rfl⟩
  · rintro _ ⟨l, rfl⟩
    let b := Module.finBasis ℤ X
    have h : l = ∑ j, l (b j) • (Int.castAddHom k).toIntLinearMap.comp (b.coord j) := by
      ext x
      conv_lhs => rw [← b.sum_repr x]
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, Int.coe_castAddHom,
        smul_eq_mul, Module.Basis.coord_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_smul_eq_zsmul k, smul_eq_mul, mul_comm]
    change e l ∈ S
    rw [h, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact S.smul_mem _ (Submodule.subset_span ⟨b.coord i, rfl⟩)

theorem latticeMatrixSpan_eq [Module.Free ℤ X] [Module.Finite ℤ X]
    (w : J → X) (N : I → Matrix J J k) :
    latticeMatrixSpan w N =
      LinearMap.range (weightDiagonal (k := k) w) ⊔ ⨆ i, k ∙ N i := by
  rw [latticeMatrixSpan, Submodule.span_union, span_integralWeightDiagonal,
    ← Submodule.span_iUnion, Set.iUnion_singleton_eq_range]

theorem latticeMatrixSpan_extension {K : Type u} [Field K] [Algebra k K] [Fintype J]
    (w : J → X) (N : I → Matrix J J k) :
    Submodule.span K ((algebraMap k K).mapMatrix '' (latticeMatrixSpan w N : Set (Matrix J J k))) =
      latticeMatrixSpan w (fun i => (algebraMap k K).mapMatrix (N i)) := by
  rw [latticeMatrixSpan, matrixSpanExtension_span, Set.image_union, ← Set.range_comp]
  have h (l : X →ₗ[ℤ] ℤ) :
      (algebraMap k K).mapMatrix (integralWeightDiagonal k w l) =
        integralWeightDiagonal K w l := by
    rw [integralWeightDiagonal, mapMatrix_diagonal]
    congr 1
    funext i
    exact map_intCast _ _
  rw [show (algebraMap k K).mapMatrix ∘ integralWeightDiagonal k w =
    integralWeightDiagonal K w from funext h]
  rw [← Set.range_comp, latticeMatrixSpan]
  rfl

end LatticeMatrixSpan

end LatticeMatrices

section ScalarExtensionOfLatticeMatrices

open Specs.RationalRealization (integralWeightDiagonal latticeMatrixSpan)

open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (rationalCharacter)
open RootData (extendFunctional_one_tmul)

variable {D : BasedRootDatum.{u}} {J : Type u} [Fintype J] [DecidableEq J]

theorem rationalCartanSpan {D : BasedRootDatum.{u}} {J : Type u} [DecidableEq J]
    (w : J → D.X) (d : (ℚ ⊗[ℤ] D.Y) →ₗ[ℚ] Matrix J J ℚ)
    (hd : ∀ y, d y = Matrix.diagonal fun j => rationalCharacter D (w j) y) :
    Submodule.span ℚ (Set.range (integralWeightDiagonal ℚ w)) = LinearMap.range d := by
  let E := Submodule.span ℚ (Set.range (integralWeightDiagonal ℚ w))
  let e := D.datum.flip.toPerfPair
  have h (y : D.Y) : d (1 ⊗ₜ[ℤ] y) = integralWeightDiagonal ℚ w (e y) := by
    rw [hd, integralWeightDiagonal]
    congr 1
    funext j
    exact extendFunctional_one_tmul ℚ (D.datum.toLinearMap (w j)) y
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact ⟨1 ⊗ₜ[ℤ] e.symm f, (h _).trans (congrArg _ (e.apply_symm_apply f))⟩
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.inductionOn with
    | tmul a y =>
      have ha : a ⊗ₜ[ℤ] y = a • ((1 : ℚ) ⊗ₜ[ℤ] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ha, map_smul, h]
      exact E.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    | add x y hx hy =>
      rw [map_add]
      exact E.add_mem hx hy

/-- The rational operators span the indicated Lie subspace after extending
their coefficients to any characteristic-zero field. -/
theorem rationalLatticeMatrixSpan_bracket
    (w : J → D.X) (N : D.I → Matrix J J ℚ)
    (d : (ℚ ⊗[ℤ] D.Y) →ₗ[ℚ] Matrix J J ℚ)
    (hd : ∀ y, d y = Matrix.diagonal fun j => rationalCharacter D (w j) y)
    (L : Submodule ℚ (Matrix J J ℚ))
    (hL : L = LinearMap.range d ⊔ ⨆ i, ℚ ∙ N i)
    (hb : ∀ x ∈ L, ∀ y ∈ L, x * y - y * x ∈ L)
    (k : Type u) [Field k] [CharZero k] :
    let N' i := (algebraMap ℚ k).mapMatrix (N i)
    ∀ x ∈ latticeMatrixSpan w N', ∀ y ∈ latticeMatrixSpan w N',
      x * y - y * x ∈ latticeMatrixSpan w N' := by
  have h : L = latticeMatrixSpan w N := by
    rw [hL, latticeMatrixSpan, Submodule.span_union, rationalCartanSpan w d hd,
      ← Submodule.span_iUnion, Set.iUnion_singleton_eq_range]
  have E := matrixSpanExtension_bracket (K := k) L hb
  dsimp only at E
  rw [h, latticeMatrixSpan_extension] at E
  exact E

/-- Nonzero rational root operators retain their support and nilpotence
after entrywise scalar extension. -/
theorem extendRootMatrix
    (w : J → D.X) (i : D.I) (N : Matrix J J ℚ)
    (h : N ≠ 0 ∧ IsNilpotent N ∧ ∀ a b, N a b ≠ 0 → w a = w b + D.datum.root i)
    (k : Type u) [Field k] [CharZero k] :
    let N' := (algebraMap ℚ k).mapMatrix N
    N' ≠ 0 ∧ IsNilpotent N' ∧ ∀ a b, N' a b ≠ 0 → w a = w b + D.datum.root i := by
  let f := algebraMap ℚ k
  refine ⟨?_, h.2.1.map f.mapMatrix, ?_⟩
  · intro hzero
    apply h.1
    apply Matrix.ext
    intro a b
    apply f.injective
    have he := congrArg (fun M : Matrix J J k => M a b) hzero
    exact he.trans (map_zero f).symm
  · intro a b hab
    apply h.2.2 a b
    intro he
    exact hab ((congrArg f he).trans (map_zero f))

end ScalarExtensionOfLatticeMatrices

section GeneratedMatrixGroups

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme Lie)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization
  (exponentialMatrix diagonalTorus integralWeightDiagonal latticeMatrixSpan RationalMatrixGroups)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RootGroups (AdditiveLine rootPoint)
open _root_.LinearAlgebraicGroups.Specs.StandardGroups (generalLinearPoints additivePoints)
open _root_.LinearAlgebraicGroups.Specs.DiagonalizableGroups (characterValuedPoints)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints constants reduction)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open InfinitesimalCommutator (matrixDifferential)
open RootData (extendFunctional extendFunctional_one_tmul)


open Specs.RationalRealization (MatrixGroup)
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable {k K J : Type u} [Field k] [CharZero k] [Field K] [Algebra k K]
  [Fintype J] [DecidableEq J]

omit [CharZero k] in
private theorem matrixPoint_with_normalized_tangent
    {G : GroupScheme k} (g : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (L : Submodule k (Matrix J J k)) (p : GroupPoints G (CommAlgCat.of k (DualNumber K)))
    (h : let E := matrixSpanExtension (K := K) L
         let z := toMatrixPoint g (CommAlgCat.of k (DualNumber K)) p
         let a := matrixReduction K z
         (∀ M ∈ E, a.val * M * a⁻¹.val ∈ E) ∧
         (∀ M ∈ E, a⁻¹.val * M * a.val ∈ E) ∧ (dualMatrix z).snd * a⁻¹.val ∈ E) :
    p ∈ matrixPointsWithTangents (K := K) g L := by
  let R := CommAlgCat.of k K
  let S := CommAlgCat.of k (DualNumber K)
  let E := matrixSpanExtension (K := K) L
  let T := matrixTangentSubgroup E
  let U := T.comap (toMatrixPoint g S)
  let c := (constant G R).comp (reduce G R)
  let z := toMatrixPoint g S p
  let b := matrixReduction K z
  obtain ⟨h₁, h₂, h₃⟩ := h
  have hc : toMatrixPoint g S (c p) = matrixConstants b := by
    change toMatrixPoint g S (mapPoints (constants R) (mapPoints (reduction R) p)) = _
    rw [toMatrixPoint_natural, toMatrixPoint_natural]
    rfl
  have hnormal := matrixConstant_normalizes E b h₁ h₂
  have htranslate := reduceMatrix_mem E z b (matrixReduction_val K z).symm h₃
  change c p ∈ Subgroup.normalizer (U : Set (GroupPoints G S)) ∧ p * (c p)⁻¹ ∈ U
  refine ⟨Subgroup.mem_normalizer_iff.mpr ?_, ?_⟩
  · intro q
    change toMatrixPoint g S q ∈ T ↔ toMatrixPoint g S (c p * q * (c p)⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv, hc]
    exact (Subgroup.mem_normalizer_iff.mp hnormal) _
  · change toMatrixPoint g S (p * (c p)⁻¹) ∈ T
    rwa [map_mul, map_inv, hc]

variable (D : BasedRootDatum.{u})

omit [CharZero k] in
private theorem latticeMatrixSpan_conjugation
    (w : J → D.X) (N : D.I → Matrix J J k)
    (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + D.datum.root i)
    (χ : Multiplicative D.X →* kˣ) :
    let g := Matrix.diagonal (fun j => (χ (Multiplicative.ofAdd (w j))).val)
    let g' := Matrix.diagonal (fun j => ((χ (Multiplicative.ofAdd (w j)))⁻¹ : kˣ).val)
    ∀ M ∈ latticeMatrixSpan w N, g * M * g' ∈ latticeMatrixSpan w N := by
  let S := latticeMatrixSpan w N
  let a j := (χ (Multiplicative.ofAdd (w j))).val
  let b j := ((χ (Multiplicative.ofAdd (w j)))⁻¹ : kˣ).val
  let g := Matrix.diagonal a
  let g' := Matrix.diagonal b
  have inv (i : J) : a i * b i = 1 := Units.mul_inv _
  dsimp only
  intro M hM
  change g * M * g' ∈ S
  refine Submodule.span_induction (p := fun M _ => g * M * g' ∈ S) ?_ ?_ ?_ ?_ hM
  · rintro _ (⟨φ, rfl⟩ | ⟨r, rfl⟩)
    · have h : g * integralWeightDiagonal k w φ * g' = integralWeightDiagonal k w φ := by
        simp only [g, g', integralWeightDiagonal, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        change a i * (φ (w i) : k) * b i = _
        rw [mul_comm (a i), mul_assoc, inv, mul_one]
      rw [h]
      exact Submodule.subset_span (Or.inl ⟨φ, rfl⟩)
    · have h : g * N r * g' =
            (χ (Multiplicative.ofAdd (D.datum.root r))).val • N r := by
        ext i j
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
        change (a i * N r i j) * b j = _
        by_cases hz : N r i j = 0
        · simp [hz]
        · have ha : a i = a j * (χ (Multiplicative.ofAdd (D.datum.root r))).val := by
            change (χ (Multiplicative.ofAdd (w i))).val = _
            rw [hN r i j hz]
            exact congrArg Units.val (χ.map_mul _ _)
          rw [ha]
          calc
            _ = (χ (Multiplicative.ofAdd (D.datum.root r))).val * N r i j * (a j * b j) := by ring
            _ = _ := by rw [inv, mul_one]
      rw [h]
      exact S.smul_mem _ (Submodule.subset_span (Or.inr ⟨r, rfl⟩))
  · simpa only [mul_zero, zero_mul] using S.zero_mem
  · intro a b _ _ ha hb
    rw [mul_add, add_mul]
    exact S.add_mem ha hb
  · intro a M _ h
    rw [mul_smul_comm, smul_mul_assoc]
    exact S.smul_mem _ h

omit [CharZero k] in
private theorem closedInclusion_factor {S T G : GroupScheme k} (i : T ⟶ G) (f : S ⟶ T)
    (h : IsClosedImmersion (f ≫ i).hom.hom.left) (hi : IsClosedImmersion i.hom.hom.left) :
    IsClosedImmersion f.hom.hom.left := by
  letI := hi
  have h' : IsClosedImmersion (f.hom.hom.left ≫ i.hom.hom.left) := h
  letI := h'
  exact IsClosedImmersion.of_comp_isClosedImmersion _ i.hom.hom.left

set_option maxHeartbeats 1600000 in
/-- The torus and the exponentials generate a smooth group with exactly the
specified matrix Lie algebra. -/
private theorem generateMatrixGroup
    (w : J → D.X) (N : D.I → Matrix J J k)
    (hw : Submodule.span ℤ (Set.range w) = ⊤)
    (hN : ∀ i, N i ≠ 0 ∧ IsNilpotent (N i) ∧
      ∀ a b, N i a b ≠ 0 → w a = w b + D.datum.root i)
    (hL : ∀ x ∈ latticeMatrixSpan w N, ∀ y ∈ latticeMatrixSpan w N,
      x * y - y * x ∈ latticeMatrixSpan w N) :
    Nonempty (MatrixGroup D k J w N) := by
  classical
  let := D.freeX
  let := D.finiteX
  let := D.finiteRoots
  let := Fintype.ofFinite D.I
  let L := latticeMatrixSpan w N
  let T := diagonalTorus k D
  let G := StandardGroups.generalLinearGroup k J
  let g := StandardGroups.generalLinearGroupPointsIso k J
  obtain ⟨A, Q, b, hQ, hb⟩ := standardAdditiveModel k
  obtain ⟨θ, hθ, t, htc, ht⟩ := faithfulDiagonalAction k D J w hw G g
  have hexp := matrixExponentialForModels A Q G hQ b g hb
  choose x hx hxc using fun i => hexp (N i) (hN i).2.1
  let := A.operations.hopf
  let Q' := Specs.StandardGroups.spectrum k (Polynomial k)
  let f (i : D.I) : GroupFactor G.val := ⟨Q', x i⟩
  let a : GroupFactor G.val := ⟨T, t⟩
  let l := a :: (Finset.univ.toList.map f)
  have ha : a ∈ l := by simp [l]
  have hf (i : D.I) : f i ∈ l := List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, by simp, rfl⟩)
  have hcase (c : GroupFactor G.val) (hc : c ∈ l) : c = a ∨ ∃ i, c = f i := by
    rcases List.mem_cons.mp hc with h | h
    · exact Or.inl h
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨i, rfl⟩
  have hconn (c : GroupFactor G.val) (hc : c ∈ l) : ConnectedSpace c.1.val.X.left := by
    rcases hcase c hc with rfl | ⟨i, rfl⟩
    · exact self_of_isIntegral_of_geometrically
        (diagonalGeometricallyConnected k D).geometrically_connectedSpace
    · change ConnectedSpace (PrimeSpectrum (Polynomial k))
      infer_instance
  have htest : ∀ (K : Type u) [Field K] [Algebra k K], ∀ c ∈ l,
      ∀ p : GroupPoints c.1.val (CommAlgCat.of k (DualNumber K)),
        (p ≫ c.2.hom.hom) ∈ matrixPointsWithTangents (K := K) g L := by
    intro K _ _ c hc p
    let R := CommAlgCat.of k (DualNumber K)
    let N' i := (algebraMap k K).mapMatrix (N i)
    let E := matrixSpanExtension (K := K) L
    have he : E = latticeMatrixSpan w N' := latticeMatrixSpan_extension w N
    apply matrixPoint_with_normalized_tangent g L
    change let z := toMatrixPoint g R (p ≫ c.2.hom.hom)
      let u := matrixReduction K z
      (∀ M ∈ E, u.val * M * u⁻¹.val ∈ E) ∧
      (∀ M ∈ E, u⁻¹.val * M * u.val ∈ E) ∧ (dualMatrix z).snd * u⁻¹.val ∈ E
    rcases hcase c hc with rfl | ⟨i, rfl⟩
    · refine diagonalNormalizedTangent w E (fun φ => ?_) (fun χ => ?_) _ _ (ht R p)
      · rw [he, latticeMatrixSpan_eq]
        exact Submodule.mem_sup_left ⟨φ, rfl⟩
      · rw [he]
        exact latticeMatrixSpan_conjugation D w N' (fun i a b h => (hN i).2.2 a b fun hz =>
          h ((congrArg (algebraMap k K) hz).trans (map_zero _))) χ
    · let t' : R := (Multiplicative.toAdd ((b.hom.app R).hom p))
      have hp : rootPoint (𝟙 A.group) R t' = p :=
        (ConcreteCategory.bijective_of_isIso (b.hom.app R)).1 (hb R t')
      have hz : (toMatrixPoint g R (p ≫ (x i).hom.hom)).val =
          exponentialMatrix (N i) R t' := by
        rw [← hp, ← rootPoint_id_postcomp]
        exact hx i R t'
      exact matrixExponentialNormalizedTangent (N i) (hN i).2.1 E
        (fun M hM => matrixSpanExtension_bracket L hL _ (Submodule.subset_span
          ⟨N i, Submodule.subset_span (Or.inr ⟨i, rfl⟩), rfl⟩) M hM)
        (Submodule.subset_span ⟨N i, Submodule.subset_span (Or.inr ⟨i, rfl⟩), rfl⟩) t' _ hz
  have hspan : L ≤ Submodule.span k {M | ∃ c ∈ l, ∃ p : Lie k c.1.val,
      matrixDifferential c.2 g p = M} := by
    apply Submodule.span_mono
    rintro _ (⟨φ, rfl⟩ | ⟨i, rfl⟩)
    · let φ' := (Int.castAddHom k).toIntLinearMap.comp φ
      obtain ⟨p, hp⟩ := diagonalMatrixTangents t w g θ ht φ'
      exact ⟨a, ha, p, hp⟩
    · obtain ⟨p, hp⟩ := rootExponentialTangent g b hb (N i) (x i) (hx i)
      exact ⟨f i, hf i, p, hp⟩
  obtain ⟨H, hHs, hHc, hfac, hgen, hLie⟩ := finiteFamilyMatrixLie G g l hconn L htest hspan
  obtain ⟨t', ht'⟩ := hfac a ha
  choose x' hx' using fun i => hfac (f i) (hf i)
  have ht'' : t' ≫ H.inclusion = t := ht'
  have hx'' (i : D.I) : x' i ≫ H.inclusion = x i := hx' i
  refine ⟨⟨A, b, hb, G, g, θ, H, hHs, hHc, t', closedInclusion_factor H.inclusion t' (ht'' ▸ htc)
    H.isClosedImmersion, x', fun i => closedInclusion_factor H.inclusion (x' i) (hx'' i ▸
    hxc i (hN i).1) H.isClosedImmersion, hθ, ?_, ?_, ?_, hLie⟩⟩
  · intro R p
    rw [ht'']
    exact ht R p
  · intro i R s
    rw [hx'']
    exact hx i R s
  · intro M hmT hmX
    apply hgen
    intro c hc
    rcases hcase c hc with rfl | ⟨i, rfl⟩
    · rw [ht''] at hmT
      exact hmT
    · specialize hmX i
      rw [hx''] at hmX
      exact hmX


/-- Apply the word construction to the same rational root operators over
each characteristic-zero field. -/
theorem rationalMatrixGroups : RationalMatrixGroups.{u} := by
  intro D
  classical
  obtain ⟨J, _, _, w, d, N, L, hw, _, hd, hL, hb, hN, _⟩ := rationalRootOperators D
  refine ⟨J, inferInstance, inferInstance, w, N, hw, hN, fun k _ _ => ?_⟩
  exact generateMatrixGroup D w (fun i => (algebraMap ℚ k).mapMatrix (N i)) hw
    (fun i => extendRootMatrix w i (N i) (hN i) k)
    (rationalLatticeMatrixSpan_bracket w N d hd L hL hb k)

end GeneratedMatrixGroups

section MatrixRootWeights

open Specs.RationalRealization (latticeMatrixSpan)

variable {k : Type v} {X J I : Type u} [Field k] [AddCommGroup X]
  [Fintype J] [DecidableEq J] [Fintype I]
  [Module.Free ℤ X] [Module.Finite ℤ X]
  {w : J → X} {N : I → Matrix J J k} {α : I → X}

omit [Fintype J] in
/-- A matrix in the Lie span is a sum of its lattice diagonal and the root matrices. -/
theorem latticeMatrixSpan_decompose {M : Matrix J J k} (hM : M ∈ latticeMatrixSpan w N) :
    ∃ φ : X →ₗ[ℤ] k, ∃ c : I → k, M = (weightDiagonal w) φ + ∑ i, c i • N i := by
  rw [latticeMatrixSpan, Submodule.span_union, span_integralWeightDiagonal] at hM
  obtain ⟨_, ⟨φ, rfl⟩, n, hn, hM⟩ := Submodule.mem_sup.mp hM
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hn
  exact ⟨φ, c, hM.symm⟩

omit [Fintype J] [Module.Free ℤ X] [Module.Finite ℤ X] in
private theorem weightShifts_entry
    (hα : Function.Injective α) (hα₀ : ∀ i, α i ≠ 0)
    (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + α i)
    (φ : X →ₗ[ℤ] k) (c : I → k) {i : I} {a b : J} (h : N i a b ≠ 0) :
    ((weightDiagonal w) φ + ∑ r, c r • N r) a b = c i * N i a b := by
  classical
  have hab : a ≠ b := by
    intro ea
    apply hα₀ i
    have he := hN i a b h
    rw [ea] at he
    exact add_left_cancel (he.symm.trans (add_zero _).symm)
  rw [Matrix.add_apply, show ((weightDiagonal w) φ) a b = 0 from Matrix.diagonal_apply_ne _ hab,
    zero_add, Matrix.sum_apply, Finset.sum_eq_single i]
  · rfl
  · intro r _ hr
    have hz : N r a b = 0 := by
      by_contra h'
      exact hr (hα (add_left_cancel ((hN r a b h').symm.trans (hN i a b h))))
    simp [Matrix.smul_apply, hz]
  · simp

omit [Fintype J] in
/-- The only lattice-span elements whose nonzero entries connect equal weights
are the diagonals from the character lattice. -/
theorem latticeMatrixSpan_diagonal (hα : Function.Injective α) (hα₀ : ∀ i, α i ≠ 0)
    (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + α i)
    {M : Matrix J J k} (hM : M ∈ latticeMatrixSpan w N)
    (hD : ∀ a b, M a b ≠ 0 → w a = w b) :
    ∃ φ : X →ₗ[ℤ] k, M = (weightDiagonal w) φ := by
  obtain ⟨φ, c, h⟩ := latticeMatrixSpan_decompose hM
  refine ⟨φ, ?_⟩
  have hzero (i : I) : c i • N i = 0 := by
    ext a b
    change c i * N i a b = 0
    by_contra hc
    have hp := (mul_ne_zero_iff.mp hc).2
    have he := weightShifts_entry hα hα₀ hN φ c hp
    have hd : M a b ≠ 0 := by rw [h, he]; exact hc
    exact hα₀ i (add_left_cancel ((hN i a b hp).symm.trans ((hD a b hd).trans (add_zero _).symm)))
  simp only [h, hzero, Finset.sum_const_zero, add_zero]

omit [Fintype I] [Module.Free ℤ X] [Module.Finite ℤ X] in
private theorem weightDiagonal_bracket
    (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + α i) (φ : X →ₗ[ℤ] k) (i : I) :
    weightDiagonal w φ * N i - N i * weightDiagonal w φ = φ (α i) • N i := by
  change Matrix.diagonal (fun j => φ (w j)) * N i -
    N i * Matrix.diagonal (fun j => φ (w j)) = φ (α i) • N i
  ext a b
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  change φ (w a) * N i a b - N i a b * φ (w b) = _
  by_cases h : N i a b = 0
  · simp [h]
  · rw [hN i a b h, map_add]
    ring

private theorem exists_latticeFunctional_separating [CharZero k] {x y : X} (h : x ≠ y) :
    ∃ φ : X →ₗ[ℤ] k, φ x ≠ φ y := by
  let b := Module.finBasis ℤ X
  have hrepr : b.repr x ≠ b.repr y := fun h' => h (b.repr.injective h')
  have hs : ∃ i, b.repr x i ≠ b.repr y i := by
    by_contra! hz
    exact hrepr (Finsupp.ext hz)
  obtain ⟨i, hi⟩ := hs
  refine ⟨(Int.castAddHom k).toIntLinearMap.comp (b.coord i), ?_⟩
  exact fun h' => hi (Int.cast_injective h')

/-- An ideal in the lattice span which is disjoint from the lattice diagonal
vanishes if every opposite-root bracket is a nonzero diagonal. -/
theorem eq_bot_of_disjoint_lattice_diagonal [CharZero k]
    (hα : Function.Injective α) (hα₀ : ∀ i, α i ≠ 0)
    (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + α i)
    (hop : ∀ i, ∃ j φ, N j * N i - N i * N j = weightDiagonal w φ ∧ weightDiagonal w φ ≠ 0)
    (S : Submodule k (Matrix J J k)) (hS : S ≤ latticeMatrixSpan w N)
    (hbr : ∀ x ∈ latticeMatrixSpan w N, ∀ y ∈ S, x * y - y * x ∈ S)
    (hd : Disjoint S (LinearMap.range (weightDiagonal (k := k) w))) : S = ⊥ := by
  classical
  have hdiag (φ : X →ₗ[ℤ] k) : weightDiagonal w φ ∈ latticeMatrixSpan w N := by
    rw [latticeMatrixSpan_eq]
    exact Submodule.mem_sup_left ⟨φ, rfl⟩
  have hroot (r : I) : N r ∈ latticeMatrixSpan w N :=
    Submodule.subset_span (Or.inr ⟨r, rfl⟩)
  have hcomm (φ : X →ₗ[ℤ] k) (d : X →ₗ[ℤ] k) (c : I → k) :
      weightDiagonal w φ * (weightDiagonal w d + ∑ j, c j • N j) -
        (weightDiagonal w d + ∑ j, c j • N j) * weightDiagonal w φ =
        ∑ j, (c j * φ (α j)) • N j := by
    rw [mul_add, add_mul, add_sub_add_comm,
      show weightDiagonal w φ * weightDiagonal w d =
        weightDiagonal w d * weightDiagonal w φ from by
          change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
          rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
          congr 1
          funext i
          exact mul_comm _ _,
      sub_self, zero_add, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, weightDiagonal_bracket hN,
      smul_smul]

  -- Project a root component by successively subtracting the other eigenvalues.
  have hproj (r : I) (c : I → k) (hc : (∑ j, c j • N j) ∈ S) :
      c r • N r ∈ S := by
    suffices ∀ s : Finset I, r ∉ s → ∀ (d : I → k),
        (∑ j ∈ insert r s, d j • N j) ∈ S → d r • N r ∈ S by
      refine this (Finset.univ.erase r) (Finset.notMem_erase _ _) c ?_
      rwa [Finset.insert_erase (Finset.mem_univ r)]
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hjs ih =>
      intro hr d hsum
      have hjr : j ≠ r := fun eq => hr (eq ▸ Finset.mem_insert_self _ _)
      have hrs : r ∉ s := fun hs => hr (Finset.mem_insert_of_mem hs)
      have hji : j ∉ insert r s := by simp [hjr, hjs]
      rw [Finset.insert_comm] at hsum
      obtain ⟨φ, hφ⟩ := exists_latticeFunctional_separating (k := k)
        (fun he => hjr (hα he.symm))
      let d' (i : I) := d i * (φ (α i) - φ (α j))
      have he :
          weightDiagonal w φ * (∑ i ∈ insert j (insert r s), d i • N i) -
            (∑ i ∈ insert j (insert r s), d i • N i) * weightDiagonal w φ -
            φ (α j) • (∑ i ∈ insert j (insert r s), d i • N i) =
            ∑ i ∈ insert r s, d' i • N i := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib, Finset.sum_insert hji]
        have term (i : I) : weightDiagonal w φ * (d i • N i) -
            d i • N i * weightDiagonal w φ - φ (α j) • (d i • N i) = d' i • N i := by
          rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, weightDiagonal_bracket hN,
            smul_smul, smul_smul, ← sub_smul]
          congr 1
          simp only [d', mul_sub, mul_comm (φ (α j))]
        rw [term j, show d' j = 0 by simp [d'], zero_smul, zero_add]
        exact Finset.sum_congr rfl fun i _ => term i
      have hm := S.sub_mem (hbr _ (hdiag φ) _ hsum) (S.smul_mem (φ (α j)) hsum)
      rw [he] at hm
      have hr' := S.smul_mem ((φ (α r) - φ (α j))⁻¹) (ih hrs d' hm)
      dsimp only [d'] at hr'
      rwa [smul_smul, mul_comm (d r), ← mul_assoc,
        inv_mul_cancel₀ (sub_ne_zero.mpr hφ), one_mul] at hr'


  apply le_antisymm ?_ bot_le
  intro M hM
  rw [Submodule.mem_bot]
  obtain ⟨d, c, hM'⟩ := latticeMatrixSpan_decompose (hS hM)
  have hz (i : I) : c i = 0 := by
    by_contra hc
    obtain ⟨φ, hφ⟩ := exists_latticeFunctional_separating (k := k) (hα₀ i)
    have hp := hbr (weightDiagonal w φ) (hdiag φ) M hM
    rw [hM', hcomm] at hp
    have hr := hproj i (fun j => c j * φ (α j)) hp
    have hmem : N i ∈ S := by
      have hr' := S.smul_mem (c i * φ (α i))⁻¹ hr
      rw [smul_smul, inv_mul_cancel₀, one_smul] at hr'
      · exact hr'
      · exact mul_ne_zero hc (by simpa only [map_zero] using hφ)
    obtain ⟨j, ψ, he, hne⟩ := hop i
    have hb := hbr (N j) (hroot j) (N i) hmem
    rw [he] at hb
    exact hne (Submodule.disjoint_def.mp hd _ hb ⟨ψ, rfl⟩)
  have eq : M = weightDiagonal w d := by simp [hM', hz]
  exact Submodule.disjoint_def.mp hd _ hM ⟨d, eq.symm⟩

end MatrixRootWeights

section NormalSubgroupTangents

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs
  (AffineAlgebraicGroup ClosedSubgroup GroupScheme IdentityLieStructure IsNormalSubgroup Lie)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open InfinitesimalCommutator (matrixDifferential commutator)
open private atS atT atST dropS dropT twoVariableTest dualTest mixed_factor nat_apply
  dropS_commutator dropT_commutator point_liftST_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open private presentationPointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

variable {k : Type u} [Field k]

private theorem tangent_of_mixed_point (U : GroupScheme k) [IsAffine U.X.left]
    (z : GroupPoints U (twoVariableTest (k := k)))
    (hS : (((groupPointsFunctor k).obj U).map dropS).hom z = 1)
    (hT : (((groupPointsFunctor k).obj U).map dropT).hom z = 1) :
    ∃ p : Lie k U, (((groupPointsFunctor k).obj U).map atST).hom p.toMul.val = z := by
  let G : AffineGroupCategory k := ⟨U, inferInstance⟩
  let i : hopfSpectrum (coordinateHopf G) ≅ U :=
    (affineGroupInclusion k).mapIso (coordinateHopfSpecIso G)
  let e := presentationPointIso i
  obtain ⟨p, hp⟩ := mixed_factor (coordinateHopf G) ((e.inv.app twoVariableTest).hom z)
    (by rw [← nat_apply, hT, map_one]) (by rw [← nat_apply, hS, map_one])
  refine ⟨mapDualKernel e.hom p, ?_⟩
  change (((groupPointsFunctor k).obj U).map atST).hom ((e.hom.app dualTest).hom p.toMul.val) = z
  rw [← nat_apply, hp, Iso.inv_hom_id_app_apply]

/-- Normality of an affine subgroup gives closure of its tangent image under
bracketing with all tangents to the ambient group. -/
theorem normalSubgroup_tangent_bracket {H G : GroupScheme k}
    [IsAffine H.X.left] [IsAffine G.X.left] (i : H ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left) (hn : IsNormalSubgroup i)
    (s : IdentityLieStructure G) (p : Lie k G) (q : Lie k H) :
    s.lieRing.toBracket.bracket p (mapPointKernel i q) ∈ Set.range (mapPointKernel i) := by
  let F := (groupPointsFunctor k).obj G
  let E := (groupPointsFunctor k).obj H
  let Fι := (groupPointsFunctor k).map i
  let X : GroupPoints G (twoVariableTest (k := k)) := (F.map atS).hom p.toMul.val
  let Y : GroupPoints H (twoVariableTest (k := k)) := (E.map atT).hom q.toMul.val
  have hY : (Fι.app twoVariableTest).hom Y = (F.map atT).hom (mapPointKernel i q).toMul.val :=
    (nat_apply Fι atT q.toMul.val).symm
  obtain ⟨a, ha⟩ := normalSubgroup_conjugate_sections hn X Y
  let a' : GroupPoints H (twoVariableTest (k := k)) := a
  let z : GroupPoints H (twoVariableTest (k := k)) := a' * Y⁻¹
  have hz : (Fι.app twoVariableTest).hom z = commutator F p (mapPointKernel i q) := by
    change (Fι.app twoVariableTest).hom (a' * Y⁻¹) = _
    rw [map_mul, map_inv, show (Fι.app twoVariableTest).hom a' = X * (Fι.app twoVariableTest).hom Y * X⁻¹ from ha,
      hY]
    rfl
  letI := hi
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  have hinj : Function.Injective (Fι.app dualTest).hom :=
    fun a b hab => (cancel_mono i.hom.hom).mp hab
  have hS : (E.map dropS).hom z = 1 := by
    apply hinj
    rw [nat_apply, hz, dropS_commutator, map_one]
  have hT : (E.map dropT).hom z = 1 := by
    apply hinj
    rw [nat_apply, hz, dropT_commutator, map_one]
  obtain ⟨v, hv⟩ := tangent_of_mixed_point H z hS hT
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply point_liftST_injective G
  change (F.map atST).hom ((Fι.app dualTest).hom v.toMul.val) =
    (F.map atST).hom (s.lieRing.toBracket.bracket p (mapPointKernel i q)).toMul.val
  rw [← nat_apply, hv, hz]
  exact (s.commutator_law p (mapPointKernel i q)).symm

end NormalSubgroupTangents

section MatrixLieExtension

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme Lie)
open _root_.LinearAlgebraicGroups.Specs.StandardGroups (generalLinearPoints)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (baseChangedAlgebraicGroup)
open InfinitesimalCommutator (matrixDifferential)
open private matrixDifferentialLinear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

variable {k K J : Type u} [Field k] [Field K] [Algebra k K] [Fintype J] [DecidableEq J]

set_option maxHeartbeats 1000000 in
/-- An affine group's Lie image in a general linear group extends by taking
the span of the original coefficient matrices over the new field. -/
theorem matrixDifferential_range_baseChange
    {G H : AffineAlgebraicGroup k} {G' : AffineAlgebraicGroup K}
    (g : (groupPointsFunctor k).obj G.val ≅ generalLinearPoints k J)
    (g' : (groupPointsFunctor K).obj G'.val ≅ generalLinearPoints K J)
    (i : H.val ⟶ G.val) (s : (groupBaseChange k K).obj G.val ⟶ G'.val)
    (hs : ∀ (R : TestAlgebra K) (p : GroupPoints ((groupBaseChange k K).obj G.val) R),
      g'.hom.app R (p ≫ s.hom.hom) =
        g.hom.app ((restrictTestAlgebra k K).obj R) (baseChangePoint k K G.val.X R p) )
    (L : Submodule k (Matrix J J k))
    (hL : Set.range (matrixDifferential i g) = (L : Set (Matrix J J k))) :
    Set.range (matrixDifferential ((groupBaseChange k K).map i ≫ s) g') =
      (Submodule.span K ((algebraMap k K).mapMatrix '' (L : Set (Matrix J J k))) :
        Set (Matrix J J K)) := by
  let H' := baseChangedAlgebraicGroup K H
  letI : IsAffine H.val.X.left := H.property.1
  letI : IsAffine ((groupBaseChange k K).obj H.val).X.left := H'.property.1
  let b := identityLieStructure H
  let c : Specs.IdentityLieStructure ((groupBaseChange k K).obj H.val) := identityLieStructure H'
  letI := b.lieRing
  letI := b.lieAlgebra
  letI := c.lieRing
  letI := c.lieAlgebra
  let d' := matrixDifferentialLinear ((groupBaseChange k K).map i ≫ s) g'
  obtain ⟨e, he⟩ := (identityLieBracketBaseChange k K H).2 b c
  let Q := CommAlgCat.of K (DualNumber K)
  let R := (restrictTestAlgebra k K).obj Q
  let a := extendDualNumber (k := k) K
  have hgen (p : Lie k H.val) :
      matrixDifferential ((groupBaseChange k K).map i ≫ s) g' (e (1 ⊗ₜ[k] p)) =
        (algebraMap k K).mapMatrix (matrixDifferential i g p) := by
    let u : GroupPoints H'.val Q := (e (1 ⊗ₜ[k] p)).toMul.val
    have h :
        (g'.hom.app Q).hom (u ≫ ((groupBaseChange k K).map i ≫ s).hom.hom) =
          (generalLinearPoints k J).map a ((g.hom.app (CommAlgCat.of k (DualNumber k))).hom
            (p.toMul.val ≫ i.hom.hom)) := by
      have h₀ : ((groupBaseChange k K).map i).hom.hom = (baseChange k K).map i.hom.hom := rfl
      rw [Grp.comp_hom_hom, ← Category.assoc]
      change g'.hom.app Q ((u ≫ ((groupBaseChange k K).map i).hom.hom) ≫ s.hom.hom) = _
      rw [hs, h₀, baseChangePointsSchemeNaturality]
      change (g.hom.app R).hom (baseChangePoint k K H.val.X Q u ≫ i.hom.hom) = _
      rw [he p]
      change (g.hom.app R).hom (mapPoints a (p.toMul.val ≫ i.hom.hom)) = _
      exact congrArg (fun j => j (p.toMul.val ≫ i.hom.hom)) (g.hom.naturality a)
    ext x y
    change (((g'.hom.app Q).hom (u ≫ ((groupBaseChange k K).map i ≫ s).hom.hom)).val x y).snd = _
    rw [h]
    rfl
  let E := Submodule.span K ((algebraMap k K).mapMatrix '' (L : Set (Matrix J J k)))
  have hd : ⇑d' = matrixDifferential ((groupBaseChange k K).map i ≫ s) g' := rfl
  have heq : LinearMap.range d' = E := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      obtain ⟨x, rfl⟩ := e.surjective p
      let f := d'.comp e.toLinearEquiv.toLinearMap
      change f x ∈ E
      refine TensorProduct.inductionOn x ?_ ?_
      · intro a p
        have ha : a ⊗ₜ[k] p = a • ((1 : K) ⊗ₜ[k] p) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [ha, f.map_smul]
        change a • matrixDifferential ((groupBaseChange k K).map i ≫ s) g' (e (1 ⊗ₜ[k] p)) ∈ E
        rw [hgen p]
        have hp : matrixDifferential i g p ∈ (L : Set (Matrix J J k)) :=
          hL ▸ Set.mem_range_self p
        exact E.smul_mem a (Submodule.subset_span ⟨_, hp, rfl⟩)
      · intro x y hx hy
        rw [f.map_add]
        exact E.add_mem hx hy
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨M, hM, rfl⟩
      obtain ⟨p, rfl⟩ := hL.symm ▸ hM
      exact ⟨e (1 ⊗ₜ[k] p), hgen p⟩
  exact hd ▸ congrArg SetLike.coe heq

end MatrixLieExtension

section MatrixAdjointWeights

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup Lie)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints constants scale dualMap)
open _root_.LinearAlgebraicGroups.Specs.StandardGroups (generalLinearPoints)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (adjointWeightVectors characterValue)
open InfinitesimalCommutator (matrixDifferential)
open private matrixDual nat_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

variable {k J : Type u} [Field k] [Fintype J] [DecidableEq J]

set_option maxHeartbeats 1100000 in
/-- The equation for an adjoint weight, evaluated in a matrix representation
on a point of the torus acting by a diagonal matrix. -/
theorem adjointWeight_on_matrix_entries {G M : GroupScheme k}
    (f : G ⟶ M) (g : (groupPointsFunctor k).obj M ≅ generalLinearPoints k J)
    (T : ClosedSubgroup G) (χ : Character T.group) (p : Lie k G)
    (hp : p ∈ adjointWeightVectors T χ)
    (R : TestAlgebra k) (t : GroupPoints T.group R) (d : J → R)
    (hd : ((g.hom.app R).hom (t ≫ (T.inclusion ≫ f).hom.hom)).val = Matrix.diagonal d) :
    ∀ a b, d a * algebraMap k R (matrixDifferential f g p a b) =
      characterValue χ R t * (algebraMap k R (matrixDifferential f g p a b) * d b) := by
  let F := (groupPointsFunctor k).obj G
  let U := generalLinearPoints k J
  let f' : F ⟶ U := (groupPointsFunctor k).map f ≫ g.hom
  let kε := CommAlgCat.of k (DualNumber k)
  let Rε := CommAlgCat.of k (DualNumber R)
  let θ := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
  let q : GroupPoints G Rε := mapPoints θ p.toMul.val
  let v : GroupPoints G R := t ≫ T.inclusion.hom.hom
  let c : GroupPoints G Rε := mapPoints (constants R) v
  let a := characterValue χ R t
  have hp' : c * q * c⁻¹ = mapPoints (scale R a) q := hp R t
  let q' : GroupPoints G Rε := mapPoints (scale R a) q
  have hp'' : c * q = q' * c := by
    change c * q * c⁻¹ = q' at hp'
    rw [← hp', inv_mul_cancel_right]
  let pm : GroupPoints G Rε →* Matrix.GeneralLinearGroup J (DualNumber R) := (f'.app Rε).hom
  have hconst : (pm c).val = Matrix.diagonal (fun j => (TrivSqZeroExt.inl (d j) : DualNumber R)) := by
    change (pm (mapPoints (constants R) v)).val = _
    have h := nat_apply f' (constants R) v
    change pm (mapPoints (constants R) v) = (U.map (constants R)).hom ((f'.app R).hom v) at h
    rw [h]
    have hv : ((f'.app R).hom v).val = Matrix.diagonal d := hd
    apply Matrix.ext
    intro i j
    change (TrivSqZeroExt.inl (((f'.app R).hom v).val i j) : DualNumber R) = _
    rw [hv]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, TrivSqZeroExt.inl_zero]
  have hconst' : matrixDual (pm c).val = ((Matrix.diagonal d, 0) : DualNumber (Matrix J J R)) := by
    rw [hconst]
    apply TrivSqZeroExt.ext <;> ext i j <;>
      by_cases h : i = j <;> simp [matrixDual, Matrix.diagonal_apply, h]
  let qM := matrixDual (pm q).val
  have hq (i j : J) : qM.snd i j = algebraMap k R (matrixDifferential f g p i j) := by
    have hh := nat_apply f' θ p.toMul.val
    change pm q = (U.map θ).hom ((f'.app kε).hom p.toMul.val) at hh
    change ((pm q).val i j).snd = _
    rw [hh]
    rfl
  have hq' : (matrixDual (pm (mapPoints (scale R a) q)).val).snd = a • qM.snd := by
    have hh := nat_apply f' (scale R a) q
    change pm (mapPoints (scale R a) q) = (U.map (scale R a)).hom (pm q) at hh
    rw [hh]
    ext i j
    rfl
  have he := congrArg (fun t => (matrixDual (pm t).val).snd) hp'' 
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, map_mul, map_mul, hconst'] at he
  change Matrix.diagonal d * qM.snd + 0 * qM.fst =
    (matrixDual (pm (mapPoints (scale R a) q)).val).fst * 0 +
      (matrixDual (pm (mapPoints (scale R a) q)).val).snd * Matrix.diagonal d at he
  rw [zero_mul, add_zero, mul_zero, zero_add, hq', smul_mul_assoc] at he
  intro i j
  have hh := congrArg (fun B : Matrix J J R => B i j) he
  rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, hq] at hh
  exact hh

end MatrixAdjointWeights

section PositiveHeight

open scoped TensorProduct
set_option linter.style.haveILetI false
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open RootData (realRoot realRootSpan)
open LieAlgebrasAndRepresentations
open private latticeEmbedding_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.EuclideanComparison

/-- The specified simple roots are precisely the indecomposable roots
of positive height. -/
theorem simple_of_positive_height (D : BasedRootDatum.{u}) (i : D.I) :
    i ∈ D.base.support ↔
      0 < D.base.height i ∧
      ∀ j, 0 < D.base.height j → ∀ l, 0 < D.base.height l →
        D.datum.root i ≠ D.datum.root j + D.datum.root l := by
  let := D.finiteRoots
  let := D.freeX
  let := D.freeY
  let := D.finiteX
  let := D.finiteY
  let := D.reduced
  obtain ⟨hi, _, _, _, _, ⟨metric, h⟩⟩ := RootData.euclideanComparison D.datum D.base
  letI := metric.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore metric.toCore
  obtain ⟨_, _, _, _, z, b, _, hheight, _, hb, hsimple, _, _, _⟩ := h
  let r := realRoot D.datum
  let R := Set.range r
  have hpos (j : D.I) : r j ∈ positiveRoots R z ↔ 0 < D.base.height j := by
    change (r j ∈ R ∧ 0 < inner ℝ z (r j)) ↔ _
    rw [hheight]
    exact ⟨fun h => Int.cast_pos.mp h.2, fun h => ⟨Set.mem_range_self _, Int.cast_pos.mpr h⟩⟩
  have hsum (j l : D.I) : r i = r j + r l ↔ D.datum.root i = D.datum.root j + D.datum.root l := by
    have H : (1 : ℝ) ⊗ₜ[ℤ] (D.datum.root j + D.datum.root l) =
         (r j + r l : realRootSpan D.datum).val := TensorProduct.tmul_add _ _ _
    constructor
    · intro eq
      apply latticeEmbedding_injective (X := D.X)
      exact (congrArg Subtype.val eq).trans H.symm
    · intro eq
      apply Subtype.ext
      exact (congrArg (fun x : D.X => (1 : ℝ) ⊗ₜ[ℤ] x) eq).trans H
  have he : i ∈ D.base.support ↔ r i ∈ simpleRoots R z := by
    rw [← hsimple]
    constructor
    · intro hp
      exact ⟨⟨i, hp⟩, hb _⟩
    · rintro ⟨j, hj⟩
      have eq : j.val = i := hi ((hb j).symm.trans hj)
      simpa only [← eq] using j.property
  rw [he]
  constructor
  · rintro ⟨h', h''⟩
    refine ⟨(hpos i).mp h', fun j hj l hl eq => ?_⟩
    exact h'' _ ((hpos j).mpr hj) _ ((hpos l).mpr hl) ((hsum j l).mpr eq)
  · rintro ⟨h', h''⟩
    refine ⟨(hpos i).mpr h', ?_⟩
    intro a ha c hc
    obtain ⟨j, rfl⟩ := ha.1
    obtain ⟨l, rfl⟩ := hc.1
    exact fun eq => h'' j ((hpos j).mp ha) l ((hpos l).mp hc) ((hsum j l).mp eq)

end PositiveHeight

section NormalUnipotentMatrixGroups

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open Specs.RationalRealization (latticeMatrixSpan)
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs
  (AffineAlgebraicGroup ClosedSubgroup GroupScheme Lie)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.StandardGroups (generalLinearPoints)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup IsUnipotent)
open _root_.LinearAlgebraicGroups.Specs.GeometricRadicals (IsTrivialSubgroup identitySubgroup)
open InfinitesimalCommutator (matrixDifferential)
open private matrixDifferentialLinear matrixDifferential_injective matrixDifferential_bracket
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open private isIso_of_closedImmersion_of_differential
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k J : Type u} [Field k] [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
/-- Unipotent and multiplicative-type subgroups have no common nonzero tangent. -/
private theorem unipotent_tangent_disjoint {G : AffineAlgebraicGroup k}
    (U T : ClosedSubgroup G.val) (hU : IsUnipotent (closedSubgroupAlgebraicGroup U))
    (hT : (Specs.CharacterDescent.multiplicativeTypeSpecFunctor k).essImage
      (closedSubgroupAlgebraicGroup T))
    (p : Lie k U.group) (q : Lie k T.group)
    (h : mapPointKernel U.inclusion p = mapPointKernel T.inclusion q) : p = 0 := by
  let P := pullback U.inclusion T.inclusion
  let a := pullback.fst U.inclusion T.inclusion
  let b := pullback.snd U.inclusion T.inclusion
  let hp := IsPullback.of_hasPullback U.inclusion T.inclusion
  let hX := hp.map (Grp.forget (SchemeOver k))
  have hP : IsZero P :=
    Unipotent.unipotentMultiplicativeTypeIntersection G U T a b hp hU hT
  let e := (Grp.forget (SchemeOver k)).mapIso (hP.iso (Grp.isZero_trivial (SchemeOver k)))
  have hterm : IsTerminal P.X := (isTerminalTensorUnit (C := SchemeOver k)).ofIso e.symm
  have h' : p.toMul.val ≫ U.inclusion.hom.hom = q.toMul.val ≫ T.inclusion.hom.hom :=
    congrArg (fun x : Lie k G.val => x.toMul.val) h
  let z : GroupPoints P (CommAlgCat.of k (DualNumber k)) := hX.lift p.toMul.val q.toMul.val h'
  have hz : z ≫ a.hom.hom = p.toMul.val := hX.lift_fst _ _ _
  have hz' : z = 1 := hterm.hom_ext _ _
  rw [hz', MonObj.one_comp] at hz
  exact Subtype.ext hz.symm

omit [Fintype J] [DecidableEq J] in
private theorem trivialSubgroup_of_zero_tangent [CharZero k] {G : AffineAlgebraicGroup k}
    (U : ClosedSubgroup G.val) (hU : ConnectedSpace U.group.X.left)
    (hLie : ∀ p : Lie k U.group, p = 0) : IsTrivialSubgroup U := by
  let V := closedSubgroupAlgebraicGroup U
  let Q := closedSubgroupAlgebraicGroup (identitySubgroup V)
  let s : Q.val ⟶ V.val := (identitySubgroup V).inclusion
  have hclosed : IsClosedImmersion s.hom.hom.left := (identitySubgroup V).isClosedImmersion
  have hc : ConnectedSpace Q.val.X.left := inferInstanceAs (ConnectedSpace (PrimeSpectrum k))
  have hsurj : Function.Surjective (mapPointKernel s) := by
    intro q
    exact ⟨0, (hLie _).trans (hLie q).symm⟩
  letI := isIso_of_closedImmersion_of_differential s hclosed
    (characteristicZeroSmoothness k Q) hc (characteristicZeroSmoothness k V) hU hsurj
  exact ⟨(asIso s).symm⟩

set_option maxHeartbeats 1000000 in
/-- The lattice matrix Lie algebra forces any connected normal unipotent
subgroup of the matrix group to be trivial. -/
theorem trivial_normal_unipotent_of_matrix_roots [CharZero k]
    {X I : Type u} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Fintype I]
    {G M : AffineAlgebraicGroup k} (i : G.val ⟶ M.val) (hi : IsClosedImmersion i.hom.hom.left)
    (g : (groupPointsFunctor k).obj M.val ≅ generalLinearPoints k J)
    (w : J → X) (N : I → Matrix J J k) (α : I → X)
    (hα : Function.Injective α) (hα₀ : ∀ r, α r ≠ 0)
    (hN : ∀ r a b, N r a b ≠ 0 → w a = w b + α r)
    (hop : ∀ r, ∃ s φ, N s * N r - N r * N s = weightDiagonal w φ ∧ weightDiagonal w φ ≠ 0)
    (hL : Set.range (matrixDifferential i g) = (latticeMatrixSpan w N : Set (Matrix J J k)))
    (T : ClosedSubgroup G.val)
    (hT : (Specs.CharacterDescent.multiplicativeTypeSpecFunctor k).essImage
      (closedSubgroupAlgebraicGroup T))
    (hTd : ∀ φ : X →ₗ[ℤ] k, ∃ p : Lie k T.group,
      matrixDifferential i g (mapPointKernel T.inclusion p) = weightDiagonal w φ)
    (U : ClosedSubgroup G.val) (hU : IsUnipotent (closedSubgroupAlgebraicGroup U))
    (hc : ConnectedSpace U.group.X.left) (hn : Specs.IsNormalSubgroup U.inclusion) :
    IsTrivialSubgroup U := by
  let H := closedSubgroupAlgebraicGroup U
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine U.group.X.left := H.property.1
  let s := identityLieStructure G
  let d := matrixDifferentialLinear (U.inclusion ≫ i) g
  let L := latticeMatrixSpan w N
  let S := LinearMap.range d
  have hd (p : Lie k U.group) : d p = matrixDifferential i g (mapPointKernel U.inclusion p) :=
    matrixDifferential_comp g i U.inclusion p |> Eq.symm
  have hs : S ≤ L := by
    rintro _ ⟨p, rfl⟩
    change d p ∈ (L : Set (Matrix J J k))
    exact hL ▸ ⟨_, (hd p).symm⟩
  have hb : ∀ x ∈ L, ∀ y ∈ S, x * y - y * x ∈ S := by
    intro x hx y hy
    have hx' : x ∈ Set.range (matrixDifferential i g) :=
      hL.symm ▸ show x ∈ (L : Set (Matrix J J k)) from hx
    obtain ⟨p, rfl⟩ := hx' 
    obtain ⟨q, rq⟩ := hy
    rw [← rq, hd]
    obtain ⟨v, hv⟩ := normalSubgroup_tangent_bracket U.inclusion U.isClosedImmersion hn s p q
    refine ⟨v, ?_⟩
    rw [hd, hv]
    exact matrixDifferential_bracket i g s.commutator_law p (mapPointKernel U.inclusion q)
  have disj : Disjoint S (LinearMap.range (weightDiagonal (k := k) w)) := by
    apply Submodule.disjoint_def.mpr
    rintro _ ⟨p, rfl⟩ ⟨φ, hφ⟩
    obtain ⟨q, hq⟩ := hTd φ
    have h := matrixDifferential_injective i g hi ((hd p).symm.trans (hφ.symm.trans hq.symm))
    have hp := unipotent_tangent_disjoint U T hU hT p q h
    rw [hp, map_zero]
  have hS := eq_bot_of_disjoint_lattice_diagonal hα hα₀ hN hop S hs hb disj
  apply trivialSubgroup_of_zero_tangent U hc
  intro p
  have hp : d p ∈ S := ⟨p, rfl⟩
  rw [hS, Submodule.mem_bot] at hp
  apply matrixDifferential_injective (U.inclusion ≫ i) g
  · letI := U.isClosedImmersion
    letI := hi
    exact inferInstanceAs (IsClosedImmersion (U.inclusion.hom.hom.left ≫ i.hom.hom.left))
  · exact hp.trans d.map_zero.symm

end NormalUnipotentMatrixGroups

section OppositeRootMatrices

open scoped TensorProduct

open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (rationalCharacter)
open RootData (extendFunctional extendFunctional_one_tmul)

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} (w : J → D.X)

omit [CharZero k] [Fintype J] in
/-- Diagonal evaluation is injective on functionals when the weights
generate the full character lattice. -/
theorem weightDiagonal_injective (hw : Submodule.span ℤ (Set.range w) = ⊤) :
    Function.Injective (weightDiagonal (k := k) w) := by
  intro φ ψ h
  apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _ hw).mpr
  rintro ⟨_, j, rfl⟩
  have eq := congrArg (fun H : Matrix J J k => H j j) h
  change Matrix.diagonal (fun i => φ (w i)) j j =
    Matrix.diagonal (fun i => ψ (w i)) j j at eq
  simpa only [Matrix.diagonal_apply_eq] using eq

private def integralFunctionalOver (k : Type u) [Field k] (f : D.X →ₗ[ℤ] ℤ) :
    D.X →ₗ[ℤ] k := (Int.castAddHom k).toIntLinearMap.comp f

private def corootFunctional (k : Type u) [Field k] (i : D.I) : D.X →ₗ[ℤ] k :=
  integralFunctionalOver k (D.datum.coroot' i)

omit [CharZero k] [Fintype J] in
private theorem corootFunctional_apply (i : D.I) (x : D.X) :
    corootFunctional k i x = (D.datum.coroot' i x : k) := rfl

omit [CharZero k] [Fintype J] in
private theorem corootFunctional_root (i : D.I) :
    corootFunctional k i (D.datum.root i) = 2 := by
  rw [corootFunctional_apply, RootPairing.root_coroot'_eq_pairing, RootPairing.pairing_same]
  norm_num

omit [Fintype J] in
private theorem corootDiagonal_ne_zero (hw : Submodule.span ℤ (Set.range w) = ⊤) (i : D.I) :
    weightDiagonal (k := k) w (corootFunctional k i) ≠ 0 := by
  intro h
  have eq := weightDiagonal_injective w hw (h.trans (weightDiagonal (k := k) w).map_zero.symm)
  have z := DFunLike.congr_fun eq (D.datum.root i)
  rw [corootFunctional_root] at z
  exact (by norm_num : (2 : k) ≠ 0) z

set_option maxHeartbeats 450000 in
/-- The opposite-root commutator remains a nonzero multiple of the prescribed
diagonal after extension from the rationals. -/
theorem rationalCorootBracket_over
    (N : D.I → Matrix J J ℚ)
    (d : (ℚ ⊗[ℤ] D.Y) →ₗ[ℚ] Matrix J J ℚ)
    (hd : ∀ y, d y = Matrix.diagonal fun j => rationalCharacter D (w j) y)
    (h : ∀ i, ∃ c : ℚ, c ≠ 0 ∧
      N i * N (D.datum.reflectionPerm i i) - N (D.datum.reflectionPerm i i) * N i =
        c • d (1 ⊗ₜ[ℤ] D.datum.coroot i))
    (i : D.I) :
    let N' a := (algebraMap ℚ k).mapMatrix (N a)
    ∃ c : k, c ≠ 0 ∧ N' i * N' (D.datum.reflectionPerm i i) -
      N' (D.datum.reflectionPerm i i) * N' i = c • weightDiagonal w (corootFunctional k i) := by
  let f := algebraMap ℚ k
  obtain ⟨c, hc, he⟩ := h i
  refine ⟨f c, (map_ne_zero_iff f f.injective).2 hc, ?_⟩
  dsimp only
  rw [← f.mapMatrix.map_mul, ← f.mapMatrix.map_mul]
  erw [← map_sub f.mapMatrix, he, hd]
  apply Matrix.ext
  intro a b
  change f (c * (Matrix.diagonal fun j =>
    rationalCharacter D (w j) (1 ⊗ₜ[ℤ] D.datum.coroot i)) a b) =
      f c * (Matrix.diagonal fun j => corootFunctional k i (w j)) a b
  rw [map_mul]
  by_cases ha : a = b
  · subst b
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    congr 1
    change f (extendFunctional ℚ (D.datum.toLinearMap (w a)) (1 ⊗ₜ[ℤ] D.datum.coroot i)) =
      (D.datum.toLinearMap (w a) (D.datum.coroot i) : k)
    rw [extendFunctional_one_tmul, map_intCast]
  · rw [Matrix.diagonal_apply_ne _ ha, Matrix.diagonal_apply_ne _ ha, map_zero]

end OppositeRootMatrices

section GeneratedGroupExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme Lie)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RootGroups (AdditiveLine rootPoint)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (MatrixGroup diagonalTorus latticeMatrixSpan)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.StandardGroups (generalLinearPoints additivePoints)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.DiagonalizableGroups (groupAlgebra)
open InfinitesimalCommutator (matrixDifferential)
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private extendedSpecIso extendedSpecIso_hom_fst from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private matrixDifferential_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open private isIso_of_closedImmersion_of_differential
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

section CompareMatrixGroups

variable {k K J : Type u} [Field k] [CharZero k] [Field K] [CharZero K] [Algebra k K]
  [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X} {N : D.I → Matrix J J k}

local notation "M" => Multiplicative D.X

set_option maxHeartbeats 850000 in
private theorem matrixGroup_torusPoints_baseChange
    (Q : MatrixGroup D k J w N)
    (K' : MatrixGroup D K J w (fun i => (algebraMap k K).mapMatrix (N i)))
    (R : TestAlgebra K) (t : GroupPoints (diagonalTorus K D).val R) (m : M) :
    let q := baseChangePoint k K (diagonalTorus k D).val.X R (t ≫ (diagonalBaseChange k K M).inv.hom.hom)
    ((show M →* Rˣ from (K'.torusPoints.hom.app R).hom t) m).val =
      ((show M →* Rˣ from (Q.torusPoints.hom.app ((restrictTestAlgebra k K).obj R)).hom q) m).val := by
  let A := groupAlgebra k M
  let d := CharacterDescent.groupAlgebraBaseChange k K M
  let e : (groupBaseChange k K).obj (diagonalTorus k D).val ≅ (diagonalTorus K D).val := diagonalBaseChange k K M
  let R₀ := (restrictTestAlgebra k K).obj R
  let q : Points (diagonalTorus k D).val.X R₀ := baseChangePoint k K (diagonalTorus k D).val.X R (t ≫ e.inv.hom.hom)
  let a : MonoidAlgebra K M →ₐ[K] R :=
    (((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage t).unop).hom
  have ha : t.left = Spec.map (CommRingCat.ofHom a.toRingHom) :=
    congrArg (fun p : Points (diagonalTorus K D).val.X R => p.left)
      ((algSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage t).symm
  let : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' rfl
  let i : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let b : MonoidAlgebra k M →ₐ[k] R₀ := ((a.comp d.toAlgEquiv.toAlgHom).restrictScalars k).comp i
  have hb : q.left = Spec.map (CommRingCat.ofHom b.toRingHom) := by
    change (t.left ≫ Spec.map (CommRingCat.ofHom d.toAlgEquiv.toAlgHom.toRingHom) ≫
      (extendedSpecIso K A).hom.left) ≫ pullback.fst (diagonalTorus k D).val.X.hom (fieldSpecMap k K) = _
    rw [Category.assoc, Category.assoc]
    erw [extendedSpecIso_hom_fst K A, ha]
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  dsimp only
  change ((show M →* Rˣ from (K'.torusPoints.hom.app R).hom t) m).val =
    ((show M →* Rˣ from (Q.torusPoints.hom.app R₀).hom q) m).val
  rw [K'.torusCoordinate R a t ha, Q.torusCoordinate R₀ b q hb]
  change a (MonoidAlgebra.single m 1) = a (d ((1 : K) ⊗ₜ[k] MonoidAlgebra.single m (1 : k)))
  congr 1
  apply d.symm.injective
  exact (MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) m 1).trans (d.symm_apply_apply _).symm

private theorem groupHom_ext_on_points {k : Type u} [Field k] {G H : GroupScheme k}
    (hG : IsAffine G.X.left) {f g : G ⟶ H}
    (h : ∀ (R : TestAlgebra k) (p : GroupPoints G R), p ≫ f.hom.hom = p ≫ g.hom.hom) :
    f = g := by
  apply (groupHomEquiv G H hG).injective
  ext R p
  exact h R p

/-- Identifications of the generated group and its parameters with their
scalar extensions, characterized by the given inclusions. -/
private structure MatrixGroupBaseChange
    (Q : MatrixGroup D k J w N)
    (K' : MatrixGroup D K J w (fun i => (algebraMap k K).mapMatrix (N i))) where
  group : (groupBaseChange k K).obj Q.group.group ≅ K'.group.group
  torus : (groupBaseChange k K).obj (diagonalTorus k D).val ≅ (diagonalTorus K D).val
  additive : (groupBaseChange k K).obj Q.additive.group ≅ K'.additive.group
  torusIso : torus = diagonalBaseChange k K M
  additive_parameter : ∀ (R : TestAlgebra K) (t : R),
      baseChangePoint k K Q.additive.group.X R (rootPoint additive.inv R t) =
        rootPoint (𝟙 Q.additive.group) ((restrictTestAlgebra k K).obj R) t
  torus_comm : (groupBaseChange k K).map Q.torus ≫ group.hom = torus.hom ≫ K'.torus
  root_comm : ∀ i, (groupBaseChange k K).map (Q.root i) ≫ group.hom = additive.hom ≫ K'.root i

set_option maxHeartbeats 3800000 in
private theorem matrixGroup_baseChange
    (Q : MatrixGroup D k J w N)
    (K' : MatrixGroup D K J w (fun i => (algebraMap k K).mapMatrix (N i))) :
    Nonempty (MatrixGroupBaseChange Q K') := by
  obtain ⟨g, hg⟩ := generalLinearScalarExtension Q.ambient K'.ambient Q.matrixPoints K'.matrixPoints
  obtain ⟨a, ha⟩ := additiveParameterBaseChange Q.additive K'.additive Q.additivePointsIso
    K'.additivePointsIso Q.additiveParameter K'.additiveParameter
  let t : (groupBaseChange k K).obj (diagonalTorus k D).val ≅ (diagonalTorus K D).val := diagonalBaseChange k K M
  let Hₖ := closedSubgroupAlgebraicGroup Q.group
  let H := baseChangedAlgebraicGroup K Hₖ
  let j : H.val ⟶ K'.ambient.val := (groupBaseChange k K).map Q.group.inclusion ≫ g.hom
  have hj : IsClosedImmersion j.hom.hom.left := by
    haveI := baseChangeClosedSubgroup k K _ Q.group.isClosedImmersion
    haveI : IsIso g.hom.hom.hom.left := (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso g.hom
    exact inferInstanceAs (IsClosedImmersion ((((groupBaseChange k K).map Q.group.inclusion).hom.hom.left) ≫ g.hom.hom.hom.left))
  let C : ClosedSubgroup K'.ambient.val := ⟨H.val, j, hj⟩
  have compare (S : GroupScheme k) (f : S ⟶ Q.group.group)
      (R : TestAlgebra K) (q : GroupPoints ((groupBaseChange k K).obj S) R) :
      (K'.matrixPoints.hom.app R).hom (q ≫ ((groupBaseChange k K).map f ≫ j).hom.hom) =
      (Q.matrixPoints.hom.app ((restrictTestAlgebra k K).obj R)).hom
        (baseChangePoint k K S.X R q ≫ (f ≫ Q.group.inclusion).hom.hom) := by
    let m := (groupBaseChange k K).map (f ≫ Q.group.inclusion)
    have hm : (groupBaseChange k K).map f ≫ j = m ≫ g.hom := by
      simp only [m, Functor.map_comp, j, Category.assoc]
    rw [hm, Grp.comp_hom_hom, ← Category.assoc]
    have e := hg R (q ≫ m.hom.hom)
    change (K'.matrixPoints.hom.app R).hom ((q ≫ m.hom.hom) ≫ g.hom.hom.hom) =
      (Q.matrixPoints.hom.app ((restrictTestAlgebra k K).obj R)).hom
        (baseChangePoint k K Q.ambient.val.X R (q ≫ m.hom.hom)) at e
    rw [show m.hom.hom = (baseChange k K).map (f ≫ Q.group.inclusion).hom.hom from rfl,
      baseChangePointsSchemeNaturality] at e
    exact e
  have ht₀ : t.inv ≫ (groupBaseChange k K).map Q.torus ≫ j = K'.torus ≫ K'.group.inclusion := by
    apply groupHom_ext_on_points (diagonalTorus K D).property.1
    intro R p
    apply (ConcreteCategory.bijective_of_isIso (K'.matrixPoints.hom.app R)).1
    apply Units.ext
    let q := p ≫ t.inv.hom.hom
    let R₀ := (restrictTestAlgebra k K).obj R
    have hq :
        (K'.matrixPoints.hom.app R).hom (p ≫ (t.inv ≫ (groupBaseChange k K).map Q.torus ≫ j).hom.hom) =
        (Q.matrixPoints.hom.app R₀).hom
          (baseChangePoint k K (diagonalTorus k D).val.X R q ≫ (Q.torus ≫ Q.group.inclusion).hom.hom) := by
      simpa only [q, Grp.comp_hom_hom, Category.assoc] using compare _ Q.torus R q
    change ((K'.matrixPoints.hom.app R).hom (p ≫ (t.inv ≫ (groupBaseChange k K).map Q.torus ≫ j).hom.hom)).val =
      ((K'.matrixPoints.hom.app R).hom (p ≫ (K'.torus ≫ K'.group.inclusion).hom.hom)).val
    rw [hq, K'.torusMatrix, Q.torusMatrix]
    exact congrArg Matrix.diagonal (funext fun i => (matrixGroup_torusPoints_baseChange Q K' R p
      (Multiplicative.ofAdd (w i))).symm)
  have hr₀ (i : D.I) :
      a.inv ≫ (groupBaseChange k K).map (Q.root i) ≫ j = K'.root i ≫ K'.group.inclusion := by
    have hAff : IsAffine K'.additive.group.X.left := inferInstanceAs (IsAffine (Spec (.of (Polynomial K))))
    apply groupHom_ext_on_points hAff
    intro R p
    let c : R := Multiplicative.toAdd ((K'.additivePointsIso.hom.app R).hom p)
    have hp : rootPoint (𝟙 K'.additive.group) R c = p :=
      (ConcreteCategory.bijective_of_isIso (K'.additivePointsIso.hom.app R)).1 (K'.additiveParameter R c)
    rw [← hp, rootPoint_id_postcomp, rootPoint_id_postcomp]
    apply (ConcreteCategory.bijective_of_isIso (K'.matrixPoints.hom.app R)).1
    apply Units.ext
    let R₀ := (restrictTestAlgebra k K).obj R
    have hq :
        (K'.matrixPoints.hom.app R).hom (rootPoint (a.inv ≫ (groupBaseChange k K).map (Q.root i) ≫ j) R c) =
        (Q.matrixPoints.hom.app R₀).hom (rootPoint (Q.root i ≫ Q.group.inclusion) R₀ c) := by
      have h := compare _ (Q.root i) R (rootPoint a.inv R c)
      rw [ha, rootPoint_id_postcomp] at h
      rw [rootPoint_comp]
      exact h
    rw [hq, Q.rootMatrix, K'.rootMatrix, exponentialScalarExtension]
  obtain ⟨r, hr⟩ := K'.generated C
    ⟨t.inv ≫ (groupBaseChange k K).map Q.torus, by rw [Category.assoc]; exact ht₀⟩
    (fun i => ⟨a.inv ≫ (groupBaseChange k K).map (Q.root i), by rw [Category.assoc]; exact hr₀ i⟩)
  have hrc : IsClosedImmersion r.hom.hom.left := by
    haveI := hj
    haveI : IsClosedImmersion (r.hom.hom.left ≫ j.hom.hom.left) := by
      change IsClosedImmersion (r ≫ C.inclusion).hom.hom.left
      rw [hr]
      exact K'.group.isClosedImmersion
    exact IsClosedImmersion.of_comp_isClosedImmersion _ j.hom.hom.left
  have hL : Set.range (matrixDifferential Q.group.inclusion Q.matrixPoints) =
      (latticeMatrixSpan w N : Set (Matrix J J k)) := Q.lie
  have hLieH := matrixDifferential_range_baseChange (H := Hₖ)
    Q.matrixPoints K'.matrixPoints Q.group.inclusion g.hom hg (latticeMatrixSpan w N) hL
  rw [latticeMatrixSpan_extension] at hLieH
  have hsurj : Function.Surjective (mapPointKernel r) := by
    intro q
    have hm : matrixDifferential j K'.matrixPoints q ∈
      (latticeMatrixSpan w (fun i => (algebraMap k K).mapMatrix (N i)) : Set (Matrix J J K)) :=
      hLieH ▸ Set.mem_range_self q
    obtain ⟨p, hp⟩ := K'.lie.symm ▸ hm
    refine ⟨p, matrixDifferential_injective j K'.matrixPoints hj ?_⟩
    rw [matrixDifferential_comp, show r ≫ j = K'.group.inclusion from hr, hp]
  let K₀ := closedSubgroupAlgebraicGroup K'.group
  have hc₀ : ConnectedSpace K₀.val.X.left := self_of_isIntegral_of_geometrically K'.connected.geometrically_connectedSpace
  have hcH : ConnectedSpace H.val.X.left := by
    haveI := Q.connected
    change ConnectedSpace (↥(Limits.pullback Q.group.group.X.hom (fieldSpecMap k K) : Scheme.{u}))
    exact GeometricallyConnected.geometrically_connectedSpace _ _ _ (IsPullback.of_hasPullback _ _)
  letI := isIso_of_closedImmersion_of_differential (A := K₀) (B := H) r hrc K'.smooth hc₀
    (characteristicZeroSmoothness K H) hcH hsurj
  let e : (groupBaseChange k K).obj Q.group.group ≅ K'.group.group := (asIso r).symm
  have her : e.hom ≫ r = 𝟙 _ := (asIso r).inv_hom_id
  have hrj : r ≫ j = K'.group.inclusion := hr
  haveI : Mono j := (Grp.forget (SchemeOver K) ⋙ Over.forget _).mono_of_mono_map
    (inferInstanceAs (Mono j.hom.hom.left))
  refine ⟨⟨e, t, a, rfl, ha, ?_, ?_⟩⟩
  · apply (cancel_mono r).mp
    have htr : K'.torus ≫ r = t.inv ≫ (groupBaseChange k K).map Q.torus := by
      apply (cancel_mono j).mp
      calc
        (K'.torus ≫ r) ≫ j = K'.torus ≫ K'.group.inclusion := by rw [Category.assoc, hrj]
        _ = (t.inv ≫ (groupBaseChange k K).map Q.torus) ≫ j :=
          ht₀.symm.trans (Category.assoc _ _ _).symm
    rw [Category.assoc, her, Category.comp_id, Category.assoc, htr, Iso.hom_inv_id_assoc]
  · intro i
    apply (cancel_mono r).mp
    have hxr : K'.root i ≫ r = a.inv ≫ (groupBaseChange k K).map (Q.root i) := by
      apply (cancel_mono j).mp
      calc
        (K'.root i ≫ r) ≫ j = K'.root i ≫ K'.group.inclusion := by rw [Category.assoc, hrj]
        _ = (a.inv ≫ (groupBaseChange k K).map (Q.root i)) ≫ j :=
          (hr₀ i).symm.trans (Category.assoc _ _ _).symm
    rw [Category.assoc, her, Category.comp_id, Category.assoc, hxr, Iso.hom_inv_id_assoc]

end CompareMatrixGroups

end GeneratedGroupExtension

section GeneratedGroupWeights

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs
  (AffineAlgebraicGroup ClosedSubgroup GroupScheme Lie)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (MatrixGroup diagonalTorus latticeMatrixSpan)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (characterValue adjointWeightVectors absoluteRoots)
open _root_.LinearAlgebraicGroups.Specs.RootGroups (HasScalarAction RootSubgroups rootPoint)
open _root_.LinearAlgebraicGroups.Specs.AbstractPairing (Root)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open InfinitesimalCommutator (matrixDifferential)
open RootData.CharacterPairing (characterValuesDetectCharacters)
open private characterValue_monomial characterValue_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private matrixDifferential_injective matrixDifferentialLinear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open private tangent_weight_of_scalarAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X} {N : D.I → Matrix J J k}

/-- The marked torus as a closed subgroup of the generated group. -/
private def matrixTorus (G : MatrixGroup D k J w N) : ClosedSubgroup G.group.group :=
  ⟨(diagonalTorus k D).val, G.torus, G.torusClosed⟩

private def matrixCharacter (k : Type u) [Field k] (D : BasedRootDatum.{u}) (x : D.X) :
    Character (diagonalTorus k D).val :=
  specGroupMap (groupAlgebraMap k ((zpowersHom (Multiplicative D.X) (Multiplicative.ofAdd x)).comp
    MulEquiv.ulift.toMonoidHom))

private theorem matrixCharacter_value (G : MatrixGroup D k J w N)
    (R : TestAlgebra k) (t : GroupPoints (diagonalTorus k D).val R) (x : D.X) :
    characterValue (matrixCharacter k D x) R t =
      ((show Multiplicative D.X →* Rˣ from (G.torusPoints.hom.app R).hom t)
        (Multiplicative.ofAdd x)).val := by
  let a : MonoidAlgebra k (Multiplicative D.X) →ₐ[k] R :=
    ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage t).unop.hom
  have h : (testSpec k).map (CommAlgCat.ofHom a).op = t :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage t
  rw [G.torusCoordinate R a t (congrArg (fun p : Points (diagonalTorus k D).val.X R => p.left) h.symm)]
  rw [← h]
  exact characterValue_monomial R a (Multiplicative.ofAdd x)

private theorem matrixCharacter_injective (G : MatrixGroup D k J w N) :
    Function.Injective (matrixCharacter k D) := by
  intro x y he
  let A := MonoidAlgebra k (Multiplicative D.X)
  let R := CommAlgCat.of k A
  let t : GroupPoints (diagonalTorus k D).val R := 𝟙 _
  have h (z : D.X) : characterValue (matrixCharacter k D z) R t =
      MonoidAlgebra.single (Multiplicative.ofAdd z) (1 : k) := by
    rw [matrixCharacter_value G]
    exact G.torusCoordinate R (AlgHom.id k A) t (by change 𝟙 _ = Spec.map (𝟙 _); exact (Spec.map_id _).symm) _
  have eq := congrArg (fun χ => characterValue χ R t) he
  rw [h, h] at eq
  classical
  by_contra hn
  have hp := congrArg (fun c : A => c.coeff (Multiplicative.ofAdd x)) eq
  change (Finsupp.single (Multiplicative.ofAdd x) (1 : k)) (Multiplicative.ofAdd x) =
    (Finsupp.single (Multiplicative.ofAdd y) (1 : k)) (Multiplicative.ofAdd x) at hp
  simp [hn] at hp

private theorem matrixCharacter_zero (G : MatrixGroup D k J w N) :
    matrixCharacter k D 0 = 1 := by
  apply characterValuesDetectCharacters (diagonalSplit k D)
  intro R t
  rw [matrixCharacter_value G, characterValue_one]
  change ((show Multiplicative D.X →* Rˣ from (G.torusPoints.hom.app R).hom t) 1).val = 1
  rw [map_one, Units.val_one]

set_option maxHeartbeats 650000 in
private theorem matrixCharacter_of_weight_entry (G : MatrixGroup D k J w N)
    (χ : Character (matrixTorus G).group) (v : Lie k G.group.group)
    (hv : v ∈ adjointWeightVectors (matrixTorus G) χ) {a b : J}
    (h : matrixDifferential G.group.inclusion G.matrixPoints v a b ≠ 0) :
    χ = matrixCharacter k D (w a - w b) := by
  apply characterValuesDetectCharacters (diagonalSplit k D)
  intro R t
  let c : Multiplicative D.X →* Rˣ := (G.torusPoints.hom.app R).hom t
  let d (j : J) : R := (c (Multiplicative.ofAdd (w j))).val
  let r := algebraMap k R (matrixDifferential G.group.inclusion G.matrixPoints v a b)
  have eq := adjointWeight_on_matrix_entries G.group.inclusion G.matrixPoints (matrixTorus G)
    χ v hv R t d (G.torusMatrix R t) a b
  change d a * r = characterValue χ R t * (r * d b) at eq
  have he : d a = (c (Multiplicative.ofAdd (w a - w b))).val * d b := by
    change (c (Multiplicative.ofAdd (w a))).val = _
    calc
      _ = (c (Multiplicative.ofAdd ((w a - w b) + w b))).val :=
        congrArg (fun u => (c (Multiplicative.ofAdd u)).val) (sub_add_cancel _ _).symm
      _ = _ := congrArg Units.val (c.map_mul _ _)
  have hu : IsUnit (r * d b) := ((isUnit_iff_ne_zero.mpr h).map (algebraMap k R)).mul (c _).isUnit
  rw [matrixCharacter_value G]
  apply hu.mul_right_cancel
  rw [show ((c (Multiplicative.ofAdd (w a - w b))).val * (r * d b)) = d a * r from by
    rw [he]; ring]
  exact eq.symm

private theorem matrixGroup_diagonal_tangent (G : MatrixGroup D k J w N)
    (φ : D.X →ₗ[ℤ] k) :
    ∃ p : Lie k (matrixTorus G).group,
      matrixDifferential G.group.inclusion G.matrixPoints (mapPointKernel G.torus p) =
        weightDiagonal w φ := by
  obtain ⟨p, hp⟩ := diagonalMatrixTangents (G.torus ≫ G.group.inclusion) w G.matrixPoints G.torusPoints G.torusMatrix φ
  exact ⟨p, (matrixDifferential_comp G.matrixPoints G.group.inclusion G.torus p).trans hp⟩

private theorem matrixGroup_zeroWeight_tangent (G : MatrixGroup D k J w N)
    (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + D.datum.root i)
    (v : Lie k G.group.group) (hv : v ∈ adjointWeightVectors (matrixTorus G) 1) :
    v ∈ Set.range (mapPointKernel G.torus) := by
  classical
  let := D.freeX
  let := D.finiteX
  let := D.finiteRoots
  let := Fintype.ofFinite D.I
  let d := matrixDifferential G.group.inclusion G.matrixPoints
  have hm : d v ∈ (latticeMatrixSpan w N : Set (Matrix J J k)) :=
    G.lie ▸ Set.mem_range_self v
  obtain ⟨φ, hφ⟩ := latticeMatrixSpan_diagonal D.datum.root.injective (fun i => D.datum.ne_zero i) hN hm
    (fun a b h => sub_eq_zero.mp ((matrixCharacter_injective G)
      ((matrixCharacter_of_weight_entry G 1 v hv h).symm.trans (matrixCharacter_zero G).symm)))
  obtain ⟨p, hp⟩ := matrixGroup_diagonal_tangent G φ
  exact ⟨p, matrixDifferential_injective G.group.inclusion G.matrixPoints G.group.isClosedImmersion
    (hp.trans hφ.symm)⟩

set_option maxHeartbeats 1000000 in
private theorem matrixGroup_root_scalarAction (G : MatrixGroup D k J w N) (i : D.I)
    (hN : ∀ a b, N i a b ≠ 0 → w a = w b + D.datum.root i) :
    HasScalarAction (matrixTorus G) (matrixCharacter k D (D.datum.root i)) (G.root i) := by
  letI := D.freeX
  letI : Module.IsTorsionFree ℤ D.X := inferInstance
  letI := G.group.isClosedImmersion
  letI : Mono G.group.inclusion.hom.hom := Over.mono_of_mono_left _
  intro R t a
  let z : GroupPoints G.group.group R := t ≫ G.torus.hom.hom
  let r : R := characterValue (matrixCharacter k D (D.datum.root i)) R t
  let p : GroupPoints G.group.group R := rootPoint (G.root i) R a
  let q : GroupPoints G.group.group R := rootPoint (G.root i) R (r * a)
  change z * p * z⁻¹ = q
  apply mul_inv_eq_iff_eq_mul.mpr
  apply (cancel_mono G.group.inclusion.hom.hom).mp
  apply (ConcreteCategory.bijective_of_isIso (G.matrixPoints.hom.app R)).1
  apply Units.ext
  change ((G.matrixPoints.hom.app R).hom ((z * p) ≫ G.group.inclusion.hom.hom)).val =
    ((G.matrixPoints.hom.app R).hom ((q * z) ≫ G.group.inclusion.hom.hom)).val
  rw [MonObj.mul_comp, MonObj.mul_comp, map_mul, map_mul, Units.val_mul, Units.val_mul]
  change (((G.matrixPoints.hom.app R).hom (t ≫ (G.torus ≫ G.group.inclusion).hom.hom)).val *
      ((G.matrixPoints.hom.app R).hom (rootPoint (G.root i ≫ G.group.inclusion) R a)).val) =
    (((G.matrixPoints.hom.app R).hom (rootPoint (G.root i ≫ G.group.inclusion) R (r * a))).val *
      ((G.matrixPoints.hom.app R).hom (t ≫ (G.torus ≫ G.group.inclusion).hom.hom)).val)
  rw [G.torusMatrix R t, G.rootMatrix, G.rootMatrix]
  dsimp only [r]
  rw [matrixCharacter_value G]
  exact weightShiftExponential w (D.datum.root i) (N i) (D.datum.ne_zero i) hN R
    ((G.torusPoints.hom.app R).hom t) a

private theorem matrixGroup_root_mem (G : MatrixGroup D k J w N) (i : D.I)
    (hne : N i ≠ 0) (hN : ∀ a b, N i a b ≠ 0 → w a = w b + D.datum.root i) :
    matrixCharacter k D (D.datum.root i) ∈ absoluteRoots (matrixTorus G) := by
  let X : ClosedSubgroup G.group.group := ⟨G.additive.group, G.root i, G.rootClosed i⟩
  let e : G.additive.group ≅ X.group := Iso.refl _
  have hs : HasScalarAction (matrixTorus G) (matrixCharacter k D (D.datum.root i)) (e.hom ≫ X.inclusion) := by
    change HasScalarAction _ _ (𝟙 _ ≫ G.root i)
    rw [Category.id_comp]
    exact matrixGroup_root_scalarAction G i hN
  obtain ⟨p, hp⟩ := rootExponentialTangent G.matrixPoints G.additivePointsIso G.additiveParameter
    (N i) (G.root i ≫ G.group.inclusion) (G.rootMatrix i)
  let v := mapPointKernel X.inclusion p
  refine ⟨fun eq => D.datum.ne_zero i ((matrixCharacter_injective G) (eq.trans (matrixCharacter_zero G).symm)),
    v, tangent_weight_of_scalarAction (matrixTorus G) X _ G.additive e hs ⟨p, rfl⟩, ?_⟩
  intro hz
  have h := matrixDifferential_comp G.matrixPoints G.group.inclusion (G.root i) p
  change matrixDifferential G.group.inclusion G.matrixPoints v = _ at h
  rw [hz, hp] at h
  letI : IsAffine G.group.group.X.left := (closedSubgroupAlgebraicGroup G.group).property.1
  exact hne (h.symm.trans (matrixDifferentialLinear G.group.inclusion G.matrixPoints).map_zero)

set_option maxHeartbeats 850000 in
private theorem matrixGroup_roots (G : MatrixGroup D k J w N)
    (hne : ∀ i, N i ≠ 0) (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + D.datum.root i) :
    let T := matrixTorus G
    let roots : Set (Character (diagonalTorus k D).val) := absoluteRoots T
    ∃ e : D.I ≃ roots, ∀ i : D.I, (e i).val = matrixCharacter k D (D.datum.root i) := by
  classical
  let := D.freeX
  let := D.finiteX
  let := D.finiteRoots
  let := Fintype.ofFinite D.I
  let roots : Set (Character (diagonalTorus k D).val) := absoluteRoots (matrixTorus G)
  change ∃ e : D.I ≃ roots, ∀ i : D.I, (e i).val = matrixCharacter k D (D.datum.root i)
  let f (i : D.I) : roots := ⟨matrixCharacter k D (D.datum.root i),
    matrixGroup_root_mem G i (hne i) (hN i)⟩
  refine ⟨Equiv.ofBijective f ⟨fun a b eq => D.datum.root.injective
    (matrixCharacter_injective G (congrArg (fun r : roots => r.val) eq)), ?_⟩, fun _ => rfl⟩
  intro χ
  obtain ⟨hχ, v, hv, hv₀⟩ := χ.property
  letI : IsAffine G.group.group.X.left := (closedSubgroupAlgebraicGroup G.group).property.1
  let d := matrixDifferentialLinear G.group.inclusion G.matrixPoints
  have hne : d v ≠ 0 := fun h => hv₀ (matrixDifferential_injective G.group.inclusion G.matrixPoints
    G.group.isClosedImmersion (h.trans d.map_zero.symm))
  obtain ⟨a, b, hab⟩ : ∃ a b, d v a b ≠ 0 := by
    by_contra! h
    exact hne (Matrix.ext h)
  have eq := matrixCharacter_of_weight_entry G χ.val v hv hab
  have hdiff : w a ≠ w b := by
    intro h
    exact hχ (eq.trans (by rw [h, sub_self, matrixCharacter_zero G]))
  have ne : a ≠ b := fun h => hdiff (congrArg w h)
  have hm : d v ∈ (latticeMatrixSpan w N : Set (Matrix J J k)) :=
    G.lie ▸ Set.mem_range_self v
  obtain ⟨φ, c, hde⟩ := latticeMatrixSpan_decompose hm
  have hcoeff := congrArg (fun M : Matrix J J k => M a b) hde
  rw [Matrix.add_apply, show (weightDiagonal w φ) a b = 0 from Matrix.diagonal_apply_ne _ ne,
    zero_add, Matrix.sum_apply] at hcoeff
  obtain ⟨i, hi⟩ : ∃ i, N i a b ≠ 0 := by
    by_contra! hs
    apply hab
    simp only [hcoeff, Matrix.smul_apply, hs, smul_zero, Finset.sum_const_zero]
  refine ⟨i, Subtype.ext ?_⟩
  change matrixCharacter k D (D.datum.root i) = χ.val
  rw [eq, hN i a b hi, add_sub_cancel_left]

end GeneratedGroupWeights

section ReductiveMatrixGroups

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme Lie)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (MatrixGroup diagonalTorus latticeMatrixSpan)
open _root_.LinearAlgebraicGroups.Specs.GeometricRadicals
  (IsMaximalTorus IsReductive GeometricGroup baseChangedSubgroup geometricUnipotentRadical)
open _root_.LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (adjointWeightVectors)
open _root_.LinearAlgebraicGroups.Specs.DiagonalizableGroups (FGAbelianGroup groupAlgebra)
open InfinitesimalCommutator (matrixDifferential)
open private isTorus_of_split zeroWeightVectors_iff_centralizes from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private torus_has_split_coordinates split_torus_sections_commute
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private isIso_of_closedImmersion_of_differential
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private transportSubgroup maximal_of_square from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X} {N : D.I → Matrix J J k}

private theorem diagonal_isMultiplicativeType (G : MatrixGroup D k J w N) :
    (Specs.CharacterDescent.multiplicativeTypeSpecFunctor k).essImage
      (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup G.group) (matrixTorus G)) := by
  change (Specs.CharacterDescent.multiplicativeTypeSpecFunctor k).essImage (diagonalTorus k D)
  apply (CharacterDescent.multiplicativeTypeGroupCriterion _).mpr
  let : Module.Finite ℤ D.X := D.finiteX
  let : Group.FG (Multiplicative D.X) :=
    GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp D.finiteX)
  let M : FGAbelianGroup.{u} := ⟨CommGrpCat.of (Multiplicative D.X), inferInstance⟩
  exact ⟨k, inferInstance, inferInstance, inferInstance, M,
    ⟨diagonalBaseChange k k (Multiplicative D.X)⟩⟩

private theorem torus_contains_tangent_centralizes (G : MatrixGroup D k J w N)
    (S : ClosedSubgroup G.group.group) (hS : Specs.GeometricRadicals.IsSplitTorus S.group)
    (j : (matrixTorus G).group ⟶ S.group) (hj : j ≫ S.inclusion = G.torus)
    (p : Lie k S.group) :
    mapPointKernel S.inclusion p ∈ adjointWeightVectors (matrixTorus G) 1 := by
  apply (zeroWeightVectors_iff_centralizes (matrixTorus G) (diagonalTorus k D).property.1 _).mpr
  let X := (testSpec k).obj (op (CommAlgCat.of k (DualNumber k)))
  let A := (matrixTorus G).group.X
  let a : A ⊗ X ⟶ S.group.X := fst A X ≫ j.hom.hom
  let b : A ⊗ X ⟶ S.group.X := snd A X ≫ p.toMul.val
  have eq : b * a * b⁻¹ = a := by
    rw [(split_torus_sections_commute hS b a).eq, mul_inv_cancel_right]
  have h := congrArg (fun u : A ⊗ X ⟶ S.group.X => u ≫ S.inclusion.hom.hom) eq
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp] at h
  have ha : a ≫ S.inclusion.hom.hom = fst A X ≫ G.torus.hom.hom := by
    change fst A X ≫ (j ≫ S.inclusion).hom.hom = _
    rw [hj]
  rw [ha] at h
  exact h

set_option maxHeartbeats 900000 in
private theorem matrixTorus_maximal [IsAlgClosed k] (G : MatrixGroup D k J w N)
    (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + D.datum.root i) :
    IsMaximalTorus (matrixTorus G) := by
  refine ⟨isTorus_of_split (diagonalSplit k D), ?_⟩
  intro S hS hTS
  obtain ⟨j, hj⟩ := hTS
  have hS' := torus_has_split_coordinates
    (G := closedSubgroupAlgebraicGroup G.group) S hS
  have hj' : j ≫ S.inclusion = G.torus := hj
  have hsurj : Function.Surjective (mapPointKernel j) := by
    intro q
    obtain ⟨p, hp⟩ := matrixGroup_zeroWeight_tangent G hN (mapPointKernel S.inclusion q)
      (torus_contains_tangent_centralizes G S hS' j hj' q)
    have h := (lieFunctoriality k).2.2 _ _ _ j S.inclusion p
    rw [hj'] at h
    haveI := S.isClosedImmersion
    haveI : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
    refine ⟨p, Subtype.ext ?_⟩
    apply (cancel_mono S.inclusion.hom.hom).mp
    exact congrArg (fun v : Lie k G.group.group => v.toMul.val) (h.symm.trans hp)
  let A := diagonalTorus k D
  let B := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup G.group) S
  letI := S.isClosedImmersion
  haveI : IsClosedImmersion (j.hom.hom.left ≫ S.inclusion.hom.hom.left) := by
    change IsClosedImmersion (j ≫ S.inclusion).hom.hom.left
    rw [hj']
    exact G.torusClosed
  have hjc := IsClosedImmersion.of_comp_isClosedImmersion j.hom.hom.left S.inclusion.hom.hom.left
  have hAc : ConnectedSpace A.val.X.left := self_of_isIntegral_of_geometrically
    (diagonalGeometricallyConnected k D).geometrically_connectedSpace
  have hBc : ConnectedSpace B.val.X.left := by
    obtain ⟨r, ⟨e⟩⟩ := hS'
    let ee := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e
    have h : ConnectedSpace (Specs.StandardGroups.multiplicativePowerGroup k
        (ULift.{u} (Fin r))).val.X.left :=
      inferInstanceAs (ConnectedSpace (PrimeSpectrum (AddMonoidAlgebra k (ULift (Fin r) → ℤ))))
    exact ee.hom.homeomorph.connectedSpace_iff.mpr h
  letI := isIso_of_closedImmersion_of_differential (A := A) (B := B) j hjc
    (characteristicZeroSmoothness k A) hAc (characteristicZeroSmoothness k B) hBc hsurj
  exact ⟨inv j, by change inv j ≫ G.torus = _; rw [← hj', IsIso.inv_hom_id_assoc]⟩

set_option maxHeartbeats 1400000 in
private theorem matrixGroup_reductive_and_maximal
    (G : MatrixGroup D k J w N)
    (G' : MatrixGroup D (AlgebraicClosure k) J w
      (fun i => (algebraMap k (AlgebraicClosure k)).mapMatrix (N i)))
    (hN : ∀ i a b, ((algebraMap k (AlgebraicClosure k)).mapMatrix (N i)) a b ≠ 0 →
      w a = w b + D.datum.root i)
    (hop : ∀ r, ∃ s φ,
      let N' i := (algebraMap k (AlgebraicClosure k)).mapMatrix (N i)
      N' s * N' r - N' r * N' s = weightDiagonal w φ ∧ weightDiagonal w φ ≠ 0) :
    IsReductive (closedSubgroupAlgebraicGroup G.group) ∧ IsGeometricallyMaximal (matrixTorus G) := by
  classical
  let := D.freeX
  let := D.finiteX
  let := D.finiteRoots
  let := Fintype.ofFinite D.I
  let E := AlgebraicClosure k
  let H := closedSubgroupAlgebraicGroup G.group
  let H' := closedSubgroupAlgebraicGroup G'.group
  obtain ⟨⟨e, et, _, _, _, htcomp, _⟩⟩ := matrixGroup_baseChange G G'
  let U := geometricUnipotentRadical H
  let V := transportSubgroup e U
  have hU := GeometricRadicals.geometricUnipotentRadicalLargest H
  have hV : Specs.IsNormalSubgroup V.inclusion := by
    exact normalSubgroup_of_iso e.symm (Iso.refl _) (by
      change (U.inclusion ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ U.inclusion
      simp) hU.1.2.2
  have hL : Set.range (matrixDifferential G'.group.inclusion G'.matrixPoints) =
      (latticeMatrixSpan w (fun i => (algebraMap k E).mapMatrix (N i)) : Set (Matrix J J E)) :=
    G'.lie
  have hV' := trivial_normal_unipotent_of_matrix_roots (G := H') G'.group.inclusion
    G'.group.isClosedImmersion G'.matrixPoints w _ D.datum.root D.datum.root.injective
    (fun i => D.datum.ne_zero i) hN hop hL (matrixTorus G') (diagonal_isMultiplicativeType G')
    (matrixGroup_diagonal_tangent G') V hU.2.1 hU.1.2.1 hV
  refine ⟨⟨G.smooth, G.connected, hV'⟩, ?_⟩
  let T := matrixTorus G
  have ht := baseChangeClosedSubgroup k E T.inclusion T.isClosedImmersion
  refine ⟨ht, maximal_of_square e.symm (matrixTorus G') (baseChangedSubgroup E T ht)
    et.symm ?_ (matrixTorus_maximal G' hN)⟩
  change et.inv ≫ (groupBaseChange k E).map G.torus = G'.torus ≫ e.inv
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, htcomp, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end ReductiveMatrixGroups

section MatrixRootCoordinates

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (MatrixGroup diagonalTorus latticeMatrixSpan)
open _root_.LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive)
open _root_.LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.RootGroups (AdditiveLine IsRootSubgroup HasScalarAction rootPoint)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open RootData.RootGroups (additivePoints rankOneRootGroups rootSubgroups)
open private root_coordinate_lifts_to_centralizer root_coordinate_contracts
  additiveLineGroup rootPoint_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private subgroupInclusionFactors from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private subgroupIso_of_same from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X} {N : D.I → Matrix J J k}

set_option maxHeartbeats 1100000 in
/-- In a split reductive matrix model the polynomial root map gives a
coordinate on the actual rank-one root subgroup. -/
private theorem matrixGroup_root_coordinate (G : MatrixGroup D k J w N)
    (hG : IsReductive (closedSubgroupAlgebraicGroup G.group))
    (hm : IsGeometricallyMaximal (matrixTorus G))
    (i : D.I) (hne : N i ≠ 0) (hN : ∀ a b, N i a b ≠ 0 → w a = w b + D.datum.root i)
    (U : ClosedSubgroup G.group.group)
    (hU : IsRootSubgroup (matrixTorus G) U (matrixCharacter k D (D.datum.root i))) :
    ∃ q : G.additive.group ≅ U.group, q.hom ≫ U.inclusion = G.root i := by
  let C₀ := closedSubgroupAlgebraicGroup G.group
  let T := matrixTorus G
  let α := matrixCharacter k D (D.datum.root i)
  have ha := matrixGroup_root_mem G i hne hN
  have hs := diagonalSplit k D
  obtain ⟨C, c, _, hc, P, _, _, _, _, _, A, p, _, hV, _, _⟩ :=
    rankOneRootGroups C₀ hG T hs hm α ha
  have hx := matrixGroup_root_scalarAction G i hN
  obtain ⟨f, hf⟩ := root_coordinate_lifts_to_centralizer T C (G.root i) hx
  have hx' : HasScalarAction T α (f ≫ C.subgroup.inclusion) := hf ▸ hx
  have points (R : TestAlgebra k) (b : GroupPoints G.additive.group R) :
      ∃ z : GroupPoints P.contracting.group R,
        z ≫ P.contracting.inclusion.hom.hom = b ≫ f.hom.hom := by
    obtain ⟨a, rfl⟩ := (additivePoints G.additive R).surjective b
    rw [← rootPoint_eq]
    exact (P.contracting_points R _).mp (root_coordinate_contracts T α C c hc f hx' R a)
  obtain ⟨j, hj⟩ := subgroupInclusionFactors (additiveLineGroup G.additive).property.1
    P.contracting f points
  let V := subgroupOfSubgroup C.subgroup P.contracting
  have h : j ≫ V.inclusion = G.root i := by
    change j ≫ P.contracting.inclusion ≫ C.subgroup.inclusion = _
    rw [← Category.assoc, hj, hf]
  have hjc := closedInclusion_factor V.inclusion j (h ▸ G.rootClosed i) V.isClosedImmersion
  let s := j ≫ p.root.inv
  have hs' : IsClosedImmersion s.hom.hom.left := by
    change IsClosedImmersion (j.hom.hom.left ≫ p.root.inv.hom.hom.left)
    letI := hjc
    letI : IsIso p.root.inv.hom.hom.left :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso p.root.inv
    exact IsClosedImmersion.comp _ _
  letI := RootData.RootGroups.additiveLine_closedImmersion_isIso G.additive A s hs'
  let s' : G.additive.group ≅ V.group := asIso s ≪≫ p.root
  have hs'': s'.hom ≫ V.inclusion = G.root i := by
    change (j ≫ p.root.inv) ≫ p.root.hom ≫ V.inclusion = _
    rw [Category.assoc, Iso.inv_hom_id_assoc, h]
  obtain ⟨U₀, _, _, _, _, hunique⟩ := (rootSubgroups C₀ hG T hs hm).2 α ha |>.2.2
  obtain ⟨⟨b, hb⟩, ⟨a, ha'⟩⟩ := hunique V hV
  obtain ⟨⟨d, hd⟩, ⟨c, hc'⟩⟩ := hunique U hU
  have hh : SameSubgroup V U := ⟨⟨a ≫ d, by rw [Category.assoc, hd, ha']⟩,
    ⟨c ≫ b, by rw [Category.assoc, hb, hc']⟩⟩
  obtain ⟨e, he⟩ := subgroupIso_of_same hh
  refine ⟨s' ≪≫ e, ?_⟩
  change (s'.hom ≫ e.hom) ≫ U.inclusion = G.root i
  rw [Category.assoc, he, hs'']

end MatrixRootCoordinates

section MatrixBorelPairs

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum SplitBorelPair IsSimple)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (MatrixGroup diagonalTorus latticeMatrixSpan)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive)
open _root_.LinearAlgebraicGroups.Specs.GeometricBorelConjugacy (IsKBorel)
open _root_.LinearAlgebraicGroups.Specs.SchemeDerivedGroup (IsSubgroupOf)
open _root_.LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)
open _root_.LinearAlgebraicGroups.Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Character Cocharacter)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (absoluteRoots pairing)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open _root_.LinearAlgebraicGroups.Specs.Pinning (SimpleRoot)
open _root_.LinearAlgebraicGroups.Specs.AbstractPairing (Root)
open _root_.LinearAlgebraicGroups.Specs.RootGroups (IsRootSubgroup HasScalarAction)
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (RootSubgroupFamily)

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X} {N : D.I → Matrix J J k}

private structure MatrixBorel (G : MatrixGroup D k J w N) where
  reductive : IsReductive (closedSubgroupAlgebraicGroup G.group)
  maximal : IsGeometricallyMaximal (matrixTorus G)
  direction : Cocharacter (diagonalTorus k D).val
  limits : LimitDecomposition (direction ≫ G.torus)
  isBorel : IsKBorel limits.parabolic
  containsTorus : IsSubgroupOf (matrixTorus G) limits.parabolic
  rootIndex : D.I ≃ {χ : Character (diagonalTorus k D).val // χ ∈ absoluteRoots (matrixTorus G)}
  rootCharacter : ∀ i, (rootIndex i).val = matrixCharacter k D (D.datum.root i)
  positivity : ∀ i, rootIndex i ∈ subgroupRoots (matrixTorus G) limits.parabolic ↔ 0 < D.base.height i

private def MatrixBorel.pair {G : MatrixGroup D k J w N} (B : MatrixBorel G) : SplitBorelPair k :=
  ⟨closedSubgroupAlgebraicGroup G.group, B.reductive, matrixTorus G, diagonalSplit k D,
    B.maximal, B.limits.parabolic, B.isBorel, B.containsTorus⟩

-- The two maps in these hypotheses are the integral character and cocharacter markings.
set_option maxHeartbeats 1000000 in
private theorem matrixGroup_borel (G : MatrixGroup D k J w N)
    (hG : IsReductive (closedSubgroupAlgebraicGroup G.group))
    (hT : IsGeometricallyMaximal (matrixTorus G))
    (hne : ∀ i, N i ≠ 0) (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + D.datum.root i)
    (c : Cocharacter (diagonalTorus k D).val)
    (m : ℤ) (hm : 0 < m)
    (hc : ∀ i, pairing (diagonalTorus k D).val (matrixCharacter k D (D.datum.root i)) c =
      m * D.base.height i) :
    ∃ B : MatrixBorel G, B.direction = c := by
  let H := closedSubgroupAlgebraicGroup G.group
  let T := matrixTorus G
  obtain ⟨e, he⟩ := matrixGroup_roots G hne hN
  have hval (i : D.I) : pairing T.group (e i).val c = m * D.base.height i := by
    rw [he i]
    exact hc i
  have hr : IsRegular T c := by
    intro α
    obtain ⟨i, rfl⟩ := e.surjective α
    rw [hval]
    exact mul_ne_zero hm.ne' (D.base.height_ne_zero i)
  obtain ⟨L⟩ := CocharacterDynamics.existsLimitDecomposition H (c ≫ G.torus)
  obtain ⟨_, hB, hB', hpos, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel H hG T (diagonalSplit k D) hT c hr L
  refine ⟨⟨hG, hT, c, L, hB, hB', e, he, fun i => ?_⟩, rfl⟩
  change e i ∈ subgroupRoots T L.parabolic ↔ 0 < _
  rw [hpos]
  change 0 < pairing T.group (e i).val c ↔ _
  rw [hval]
  exact mul_pos_iff_of_pos_left hm

set_option maxHeartbeats 850000 in
private theorem MatrixBorel.simple_iff {G : MatrixGroup D k J w N} (B : MatrixBorel G)
    (χ : D.X ≃ₗ[ℤ] Additive (Character (diagonalTorus k D).val))
    (hχ : ∀ x, Additive.toMul (χ x) = matrixCharacter k D x) (i : D.I) :
    IsSimple B.pair (B.rootIndex i) ↔ i ∈ D.base.support := by
  classical
  rw [simple_of_positive_height]
  change (B.rootIndex i ∈ subgroupRoots (matrixTorus G) B.limits.parabolic ∧
    ∀ β ∈ subgroupRoots (matrixTorus G) B.limits.parabolic,
      ∀ δ ∈ subgroupRoots (matrixTorus G) B.limits.parabolic, (B.rootIndex i).val ≠ β.val * δ.val) ↔ _
  have eq (r : D.I) : (B.rootIndex r).val = Additive.toMul (χ (D.datum.root r)) :=
    (B.rootCharacter r).trans (hχ _).symm
  have hr (j l : D.I) : (B.rootIndex i).val = (B.rootIndex j).val * (B.rootIndex l).val ↔
      D.datum.root i = D.datum.root j + D.datum.root l := by
    rw [eq i, eq j, eq l]
    change Additive.toMul (χ (D.datum.root i)) =
      Additive.toMul (χ (D.datum.root j) + χ (D.datum.root l)) ↔ _
    rw [← map_add]
    exact (Additive.toMul.injective.eq_iff).trans χ.injective.eq_iff
  constructor
  · rintro ⟨hp, hd⟩
    exact ⟨(B.positivity i).mp hp, fun j hj l hl eq => hd _ ((B.positivity j).mpr hj)
      _ ((B.positivity l).mpr hl) ((hr j l).mpr eq)⟩
  · rintro ⟨hp, hd⟩
    refine ⟨(B.positivity i).mpr hp, ?_⟩
    intro a ha b hb
    obtain ⟨j, rfl⟩ := B.rootIndex.surjective a
    obtain ⟨l, rfl⟩ := B.rootIndex.surjective b
    exact fun eq => hd j ((B.positivity j).mp ha) l ((B.positivity l).mp hb) ((hr j l).mp eq)


set_option maxHeartbeats 950000 in
private theorem MatrixBorel.pinning {G : MatrixGroup D k J w N} (B : MatrixBorel G)
    (hne : ∀ i, N i ≠ 0) (hN : ∀ i a b, N i a b ≠ 0 → w a = w b + D.datum.root i) :
    ∃ (U : RootSubgroupFamily B.pair.T) (p : Specs.Pinning.Pinning G.additive B.pair U),
      ∀ a : SimpleRoot B.pair,
        (p a).val.hom ≫ (U a.val).val.inclusion = G.root (B.rootIndex.symm a.val) := by
  classical
  let P := B.pair
  have hU (a : Root P.T) :
      ∃ U : ClosedSubgroup P.G.val, IsRootSubgroup P.T U a.val := by
    obtain ⟨U, hU, _⟩ := (RootData.RootGroups.rootSubgroups
      P.G P.reductive P.T P.split P.maximal).2 a.val a.property |>.2.2
    exact ⟨U, hU⟩
  choose U hU using hU
  let roots : RootSubgroupFamily P.T := fun a => ⟨U a, hU a⟩
  have hchar (a : Root P.T) : a.val = matrixCharacter k D (D.datum.root (B.rootIndex.symm a)) :=
    (congrArg Subtype.val (B.rootIndex.apply_symm_apply a)).symm.trans (B.rootCharacter _)
  have hcoords (a : Root P.T) : ∃ e : G.additive.group ≅ (U a).group,
      e.hom ≫ (U a).inclusion = G.root (B.rootIndex.symm a) := by
    let i := B.rootIndex.symm a
    have h : IsRootSubgroup (matrixTorus G) (U a) (matrixCharacter k D (D.datum.root i)) :=
      hchar a ▸ hU a
    exact matrixGroup_root_coordinate G P.reductive P.maximal i (hne i) (hN i) (U a) h
  choose f hf using hcoords
  refine ⟨roots, fun a => ⟨f a.val, ?_⟩, fun a => hf a.val⟩
  have h : HasScalarAction P.T a.val.val (G.root (B.rootIndex.symm a.val)) := by
    rw [hchar a.val]
    exact matrixGroup_root_scalarAction G (B.rootIndex.symm a.val) (hN _) 
  exact (hf a.val).symm ▸ h

end MatrixBorelPairs

section RationalReductiveGroups

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (MatrixGroup diagonalTorus RationalReductiveMatrixGroups)
open _root_.LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive IsSplitTorus)
open _root_.LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (absoluteRoots)
open _root_.LinearAlgebraicGroups.Specs.DiagonalizableGroups (groupAlgebraMap)

set_option maxHeartbeats 1200000 in
theorem rationalReductiveMatrixGroups
    :
    RationalReductiveMatrixGroups.{u} := by
  intro D
  classical
  obtain ⟨J, _, _, w, d, N, L, hw, _, hd, hL, hb, hN, hcoroot⟩ := rationalRootOperators D
  let Nₖ (k : Type u) [Field k] [CharZero k] i := (algebraMap ℚ k).mapMatrix (N i)
  have hroots (k : Type u) [Field k] [CharZero k] (i : D.I) :=
    extendRootMatrix w i (N i) (hN i) k
  have existsGroup (k : Type u) [Field k] [CharZero k] : Nonempty (MatrixGroup D k J w (Nₖ k)) :=
    generateMatrixGroup D w (Nₖ k) hw (hroots k) (rationalLatticeMatrixSpan_bracket w N d hd L hL hb k)
  refine ⟨J, inferInstance, inferInstance, w, N, hw, ?_⟩
  intro k _ _
  let E := AlgebraicClosure k
  obtain ⟨G⟩ := existsGroup k
  obtain ⟨H⟩ := existsGroup E
  let N' (i : D.I) := (algebraMap k E).mapMatrix (Nₖ k i)
  have hcomp : Nₖ E = N' := by
    have h : (algebraMap k E).comp (algebraMap ℚ k) = algebraMap ℚ E := Subsingleton.elim _ _
    funext i
    ext a b
    exact (RingHom.congr_fun h (N i a b)).symm
  have hshift : ∀ i a b, N' i a b ≠ 0 →
      w a = w b + D.datum.root i := by
    rw [← hcomp]
    exact fun i => (hroots E i).2.2
  have hop : ∀ r, ∃ s φ,
      N' s * N' r - N' r * N' s = weightDiagonal w φ ∧ weightDiagonal w φ ≠ 0 := by
    rw [← hcomp]
    intro r
    obtain ⟨c, hc, he⟩ := rationalCorootBracket_over (k := E) w N d hd hcoroot r
    let s := D.datum.reflectionPerm r r
    let φ := corootFunctional E r
    refine ⟨s, (-c) • φ, ?_, ?_⟩
    · rw [← neg_sub, he, map_smul, neg_smul]
    · rw [map_smul]
      exact smul_ne_zero (neg_ne_zero.mpr hc) (corootDiagonal_ne_zero w hw r)
  have H' : MatrixGroup D E J w N' := hcomp ▸ H
  have ⟨hG, hm⟩ := matrixGroup_reductive_and_maximal G H' hshift hop
  obtain ⟨e, he⟩ := matrixGroup_roots G (fun i => (hroots k i).1) (fun i => (hroots k i).2.2)
  exact ⟨G, hG, diagonalSplit k D, hm, e, he⟩

end RationalReductiveGroups

section RankOneWordDerivative

variable {K A : Type u} [Field K] [CharZero K] [Ring A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ K A]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 950000 in
/-- The translated derivative of the three-factor rank-one word at one.
The first and third parameters have derivative one, as does the middle
parameter `-t⁻¹`. The formula allows an arbitrary opposite-root bracket scalar. -/
theorem rankOneWordTranslatedDerivative
    (H E F : A) (hE : ⁅H, E⁆ = (2 : K) • E) (hF : ⁅H, F⁆ = (-2 : K) • F)
    (c : K) (hc : ⁅E, F⁆ = c • H) (hEnil : IsNilpotent E) (hFnil : IsNilpotent F) :
    E + innerExp (K := K) E F + innerExp (K := K) E (innerExp (K := K) (-F) E) =
      (2 - 3*c + c^2) • E + (2*c - c^2) • H + (1-c) • F := by
  have hEH : ⁅E, H⁆ = (-2 : K) • E := by rw [← lie_skew E H, hE, neg_smul]
  have hFH : ⁅-F, H⁆ = (-2 : K) • F := by rw [neg_lie, ← lie_skew F H, neg_neg, hF]
  have hFE : ⁅-F, E⁆ = c • H := by rw [neg_lie, lie_skew E F, hc]
  have hEEH : ⁅E, ⁅E, H⁆⁆ = 0 := by rw [hEH, (lie_smul (R := K)), lie_self, smul_zero]
  have hEEF : ⁅E, ⁅E, F⁆⁆ = (-2 * c) • E := by rw [hc, (lie_smul (R := K)), hEH, smul_smul, mul_comm]
  have hFFE : ⁅-F, ⁅-F, E⁆⁆ = (-2 * c) • F := by rw [hFE, (lie_smul (R := K)), hFH, smul_smul, mul_comm]
  have h1 : innerExp (K := K) E H = H + (-2 : K) • E := by
    rw [innerExp_apply_of_lie_cube_zero E hEnil H (by rw [hEEH, lie_zero]), hEEH, hEH, smul_zero, add_zero]
  have h2 : innerExp (K := K) E F = F + c • H - c • E := by
    rw [innerExp_apply_of_lie_cube_zero E hEnil F (by rw [hEEF, (lie_smul (R := K)), lie_self, smul_zero]),
      hEEF, hc, smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 1
    congr 1
    field_simp
  have h3 : innerExp (K := K) (-F) E = E + c • H - c • F := by
    rw [innerExp_apply_of_lie_cube_zero (-F) hFnil.neg E (by rw [hFFE, (lie_smul (R := K)), neg_lie, lie_self, neg_zero, smul_zero]),
      hFFE, hFE, smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 1
    congr 1
    field_simp
  have h4 : innerExp (K := K) E E = E := by
    rw [innerExp_apply_of_lie_cube_zero E hEnil E (by simp [lie_self])]
    simp
  rw [h3, h2]
  simp only [map_add, map_sub, map_smul, h1, h2, h4]
  module

section DualCoefficient

variable {B : Type u} [Ring B]

/-- The translated linear coefficient of a dual unit is the second
coefficient multiplied by the inverse of the constant coefficient. -/
def translatedCoefficient (x : (DualNumber B)ˣ) : B := x.val.snd * x⁻¹.val.fst

theorem translatedCoefficient_mul (x y : (DualNumber B)ˣ) :
    translatedCoefficient (x * y) = translatedCoefficient x +
      x.val.fst * translatedCoefficient y * x⁻¹.val.fst := by
  let f : DualNumber B →+* B :=
    { toFun := TrivSqZeroExt.fst
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let r := Units.map f.toMonoidHom
  have h (y : (DualNumber B)ˣ) : y.val.fst * y⁻¹.val.fst = 1 :=
    congrArg Units.val (mul_inv_cancel (r y))
  change ((x.val.fst * y.val.snd + x.val.snd * y.val.fst) *
    (y⁻¹.val.fst * x⁻¹.val.fst)) = x.val.snd * x⁻¹.val.fst +
      x.val.fst * (y.val.snd * y⁻¹.val.fst) * x⁻¹.val.fst
  have right : (x.val.snd * y.val.fst) * (y⁻¹.val.fst * x⁻¹.val.fst) =
      x.val.snd * x⁻¹.val.fst := by
    calc
      _ = x.val.snd * (y.val.fst * y⁻¹.val.fst) * x⁻¹.val.fst := by simp only [mul_assoc]
      _ = _ := by rw [h, mul_one]
  rw [add_mul, right, add_comm]
  simp only [mul_assoc]

end DualCoefficient

end RankOneWordDerivative

section CocharacterDifferentials

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (MatrixGroup diagonalTorus)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Character Cocharacter)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (characterValue pairing)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X} {N : D.I → Matrix J J k}

omit [CharZero k] in
private theorem snd_infinitesimal_power (n : ℤ) :
    ((onePlusInfinitesimal (Multiplicative.ofAdd (1 : k))) ^ n).val.snd = (n : k) := by
  rw [← map_zpow]
  change n • (1 : k) = (n : k)
  simp [zsmul_eq_mul]

set_option maxHeartbeats 900000 in
/-- The diagonal entries of the cocharacter differential give its
integer pairing on the weights of the faithful matrix representation. -/
theorem cocharacter_matrix_coefficient
    (G : MatrixGroup D k J w N) (c : Cocharacter (diagonalTorus k D).val) (j : J) :
    let R := CommAlgCat.of k (DualNumber k)
    let t := onePlusInfinitesimal (Multiplicative.ofAdd (1 : k))
    let q := cocharacterPoint c R t
    ((((G.matrixPoints.hom.app R).hom (q ≫ (G.torus ≫ G.group.inclusion).hom.hom)).val j j).snd) =
      (pairing (diagonalTorus k D).val (matrixCharacter k D (w j)) c : k) := by
  let R := CommAlgCat.of k (DualNumber k)
  let t := onePlusInfinitesimal (Multiplicative.ofAdd (1 : k))
  let q := cocharacterPoint c R t
  dsimp only
  change ((((G.matrixPoints.hom.app R).hom (q ≫ (G.torus ≫ G.group.inclusion).hom.hom)).val j j).snd) = _
  rw [G.torusMatrix R q, Matrix.diagonal_apply_eq, ← matrixCharacter_value G]
  rw [(RootData.CharacterPairing.characterPairingComposition _ _ _).2 R t, snd_infinitesimal_power]

set_option maxHeartbeats 900000 in
/-- Once its diagonal differential is identified, the coroot is determined
on the full cocharacter lattice by the generating weights. -/
theorem cocharacter_eq_of_matrix_coefficients
    (G : MatrixGroup D k J w N) (hw : Submodule.span ℤ (Set.range w) = ⊤)
    (c : Cocharacter (diagonalTorus k D).val) (i : D.I)
    (h : let R := CommAlgCat.of k (DualNumber k)
         let t := onePlusInfinitesimal (Multiplicative.ofAdd (1 : k))
         let q := cocharacterPoint c R t
         ∀ j, (((G.matrixPoints.hom.app R).hom (q ≫ (G.torus ≫ G.group.inclusion).hom.hom)).val j j).snd =
           corootFunctional k i (w j)) :
    c = Additive.toMul (diagonalCocharacters k D (D.datum.coroot i)) := by
  let T := (diagonalTorus k D).val
  let e := diagonalCocharacters k D
  let y := e.symm (Additive.ofMul c)
  have hy : Additive.toMul (e y) = c := congrArg Additive.toMul (e.apply_symm_apply _)
  have hyj (j : J) :
      D.datum.toLinearMap (w j) y = D.datum.toLinearMap (w j) (D.datum.coroot i) := by
    have he := (cocharacter_matrix_coefficient G c j).symm.trans (h j)
    have he' := Int.cast_injective he
    change pairing T (matrixCharacter k D (w j)) c = D.datum.toLinearMap (w j) (D.datum.coroot i) at he'
    have eq : Additive.toMul (diagonalCharacters k D (w j)) = matrixCharacter k D (w j) :=
      diagonalCharacters_eq k D _
    rw [← eq, ← hy] at he'
    exact (diagonalPairing k D (w j) y).symm.trans he'
  have eq : D.datum.flip.toPerfPair y = D.datum.flip.toPerfPair (D.datum.coroot i) := by
    apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _ hw).mpr
    rintro ⟨_, j, rfl⟩
    exact hyj j
  exact hy.symm.trans (congrArg (fun x => Additive.toMul (e x)) (D.datum.flip.toPerfPair.injective eq))

end CocharacterDifferentials

section RankOneSchemeDerivative

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme Lie)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (MatrixGroup exponentialMatrix matrixAlgebra)
open _root_.LinearAlgebraicGroups.Specs.RootGroups (AdditiveLine CorootReflection rankOneWord rootPoint)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open CocharacterDynamics (cocharacterPoint)
open private matrixDual from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

section DualUnits

variable {B : Type u} [Ring B]

private def constantRingHom : DualNumber B →+* B where
  toFun := TrivSqZeroExt.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def constantPart : (DualNumber B)ˣ →* Bˣ := Units.map constantRingHom.toMonoidHom

private theorem constantPart_val (a : (DualNumber B)ˣ) : (constantPart a).val = a.val.fst := rfl

private theorem constant_inv (y : (DualNumber B)ˣ) (hy : y.val.snd = 0) :
    y⁻¹.val.snd = 0 := by
  have h := congrArg (fun a : (DualNumber B)ˣ => a.val.snd) (mul_inv_cancel y)
  rw [Units.val_mul, DualNumber.snd_mul, hy, zero_mul, add_zero] at h
  exact (constantPart y).isUnit.mul_left_cancel (h.trans (mul_zero _).symm)

private theorem translatedCoefficient_of_snd
    (x : (DualNumber B)ˣ) (a : B) (hx : x.val.snd = a * x.val.fst) :
    translatedCoefficient x = a := by
  have h := congrArg Units.val (mul_inv_cancel (constantPart x))
  change x.val.fst * x⁻¹.val.fst = 1 at h
  rw [translatedCoefficient, hx, mul_assoc, h, mul_one]

private theorem translatedCoefficient_eq_snd_mul_inv (x y : (DualNumber B)ˣ)
    (hy : y.val.snd = 0) (hxy : x.val.fst = y.val.fst) :
    (x * y⁻¹).val.snd = translatedCoefficient x := by
  have eq : constantPart x = constantPart y := Units.ext hxy
  have h := congrArg (fun a : Bˣ => a⁻¹.val) eq
  change (constantPart x)⁻¹.val = (constantPart y)⁻¹.val at h
  rw [← (constantPart (B := B)).map_inv, ← (constantPart (B := B)).map_inv, constantPart_val,
    constantPart_val] at h
  rw [Units.val_mul, DualNumber.snd_mul, constant_inv y hy, mul_zero, zero_add, ← h]
  rfl

end DualUnits

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X} {N : D.I → Matrix J J k}

set_option maxHeartbeats 850000 in
private theorem exponentialMatrix_pair_self
    (n : Matrix J J k) (hn : IsNilpotent n) (t : DualNumber k) :
    matrixDual (exponentialMatrix n (CommAlgCat.of k (DualNumber k)) t) =
      ((IsNilpotent.exp (t.fst • n), (t.snd • n) * IsNilpotent.exp (t.fst • n)) :
        DualNumber (Matrix J J k)) := by
  have eq : (algebraMap k k).mapMatrix n = n := by
    apply Matrix.ext
    intro i j
    exact RingHom.congr_fun (Algebra.algebraMap_self : algebraMap k k = RingHom.id k) (n i j)
  have h := matrixExponentialDualNumber (K := k) n hn t
  dsimp only at h
  rw [eq] at h
  have he (x : Matrix J J k) :
      (letI := matrixAlgebra (CommAlgCat.of k k); IsNilpotent.exp x) = IsNilpotent.exp x :=
    congrArg (fun M : Module ℚ (Matrix J J k) => @IsNilpotent.exp _ _ M x) (Subsingleton.elim _ _)
  convert h using 2
  · exact (he _).symm
  · exact congrArg (fun x : Matrix J J k => (t.snd • n) * x) (he _).symm

set_option maxHeartbeats 1500000 in
private theorem rankOneCoroot_matrix_derivative
    (G : MatrixGroup D k J w N) {A : AdditiveLine k}
    (α : Character (matrixTorus G).group) (xpos xneg : A.group ⟶ G.group.group)
    (r : CorootReflection (matrixTorus G) α xpos xneg)
    (H E F : Matrix J J k) (hEnil : IsNilpotent E) (hFnil : IsNilpotent F)
    (hE : ⁅H, E⁆ = (2 : k) • E) (hF : ⁅H, F⁆ = (-2 : k) • F)
    (c : k) (hEF : ⁅E, F⁆ = c • H)
    (he : ∀ (R : TestAlgebra k) (t : R),
      ((G.matrixPoints.hom.app R).hom (rootPoint (xpos ≫ G.group.inclusion) R t)).val =
        exponentialMatrix E R t)
    (hf : ∀ (R : TestAlgebra k) (t : R),
      ((G.matrixPoints.hom.app R).hom (rootPoint (xneg ≫ G.group.inclusion) R t)).val =
        exponentialMatrix F R t) :
    let R := CommAlgCat.of k (DualNumber k)
    let t := onePlusInfinitesimal (Multiplicative.ofAdd (1 : k))
    let p := cocharacterPoint r.coroot R t
    let B := ((G.matrixPoints.hom.app R).hom (p ≫ (G.torus ≫ G.group.inclusion).hom.hom)).val
    (matrixDual B).snd = (2 - 3*c + c^2) • E + (2*c - c^2) • H + (1-c) • F := by
  let R := CommAlgCat.of k (DualNumber k)
  let t := onePlusInfinitesimal (Multiplicative.ofAdd (1 : k))
  let ρ : GroupPoints G.group.group R →* (DualNumber (Matrix J J k))ˣ :=
    (Units.map matrixDual.toMonoidHom).comp
      ((G.matrixPoints.hom.app R).hom.comp
        (((groupPointsFunctor k).map G.group.inclusion).app R).hom)
  let p := ρ (rootPoint xpos R t.val)
  let q := ρ (rootPoint xneg R (-(t⁻¹.val : R)))
  let p₀ := ρ (rootPoint xpos R 1)
  let q₀ := ρ (rootPoint xneg R (-1))
  have hp (a : R) : (ρ (rootPoint xpos R a)).val =
      ((IsNilpotent.exp (a.fst • E), (a.snd • E) * IsNilpotent.exp (a.fst • E)) :
        DualNumber (Matrix J J k)) := by
    change matrixDual ((G.matrixPoints.hom.app R).hom
      (rootPoint (xpos ≫ G.group.inclusion) R a)).val = _
    rw [he]
    exact exponentialMatrix_pair_self E hEnil a
  have hq (a : R) : (ρ (rootPoint xneg R a)).val =
      ((IsNilpotent.exp (a.fst • F), (a.snd • F) * IsNilpotent.exp (a.fst • F)) :
        DualNumber (Matrix J J k)) := by
    change matrixDual ((G.matrixPoints.hom.app R).hom
      (rootPoint (xneg ≫ G.group.inclusion) R a)).val = _
    rw [hf]
    exact exponentialMatrix_pair_self F hFnil a
  have hp' : p.val = ((IsNilpotent.exp E, E * IsNilpotent.exp E) : DualNumber (Matrix J J k)) := by
    change (ρ (rootPoint xpos R (1, 1))).val = _
    rw [hp]
    simp
  have hq' : q.val = ((IsNilpotent.exp (-F), F * IsNilpotent.exp (-F)) : DualNumber (Matrix J J k)) := by
    change (ρ (rootPoint xneg R (-1, -(-1 : k)))).val = _
    rw [hq]
    simp
  have hp₀ : p₀.val = ((IsNilpotent.exp E, 0) : DualNumber (Matrix J J k)) := by
    change (ρ (rootPoint xpos R 1)).val = _
    rw [hp]
    simp
  have hq₀ : q₀.val = ((IsNilpotent.exp (-F), 0) : DualNumber (Matrix J J k)) := by
    change (ρ (rootPoint xneg R (-1))).val = _
    rw [hq]
    rw [TrivSqZeroExt.fst_neg, TrivSqZeroExt.snd_neg, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, neg_zero, neg_smul, one_smul, zero_smul, zero_mul]
  have hfst : (p * q * p).val.fst = (p₀ * q₀ * p₀).val.fst := by
    simp only [Units.val_mul, TrivSqZeroExt.fst_mul, hp', hp₀, hq', hq₀]
    rfl
  have hsnd : (p₀ * q₀ * p₀).val.snd = 0 := by
    simp only [Units.val_mul, DualNumber.snd_mul, TrivSqZeroExt.fst_mul, hp₀, hq₀]
    change (IsNilpotent.exp E * IsNilpotent.exp (-F)) * 0 +
      (IsNilpotent.exp E * 0 + 0 * IsNilpotent.exp (-F)) * IsNilpotent.exp E = (0 : Matrix J J k)
    simp
  have hnorm₁ : translatedCoefficient p = E :=
    translatedCoefficient_of_snd p E (by rw [hp']; rfl)
  have hnorm₂ : translatedCoefficient q = F :=
    translatedCoefficient_of_snd q F (by rw [hq']; rfl)
  have hinv (x : (DualNumber (Matrix J J k))ˣ) (a : Matrix J J k) (ha : IsNilpotent a)
      (hx : x.val.fst = IsNilpotent.exp a) : x⁻¹.val.fst = IsNilpotent.exp (-a) := by
    have h := congrArg Units.val (inv_mul_cancel (constantPart x))
    change x⁻¹.val.fst * x.val.fst = 1 at h
    apply (constantPart x).isUnit.mul_right_cancel
    change x⁻¹.val.fst * x.val.fst = IsNilpotent.exp (-a) * x.val.fst
    rw [h, hx, IsNilpotent.exp_neg_mul_exp_self ha]
  have hpInv := hinv p E hEnil (congrArg TrivSqZeroExt.fst hp')
  have hqInv := hinv q (-F) hFnil.neg (congrArg TrivSqZeroExt.fst hq')
  let z := cocharacterPoint r.coroot R t ≫ G.torus.hom.hom
  have hz : ρ z = (p * q * p) * (p₀ * q₀ * p₀)⁻¹ := by
    have eq := congrArg ρ (r.coroot_word R t)
    simpa only [rankOneWord, map_mul, map_inv, inv_one, Units.val_one, matrixTorus, z, p, q, p₀, q₀] using eq
  dsimp only
  change (ρ z).val.snd = _
  rw [hz, translatedCoefficient_eq_snd_mul_inv _ _ hsnd hfst,
    translatedCoefficient_mul, translatedCoefficient_mul, hnorm₁, hnorm₂]
  simp only [Units.val_mul, mul_inv_rev, TrivSqZeroExt.fst_mul,
    hpInv, hqInv, neg_neg, congrArg TrivSqZeroExt.fst hp', congrArg TrivSqZeroExt.fst hq']
  have calcEq := rankOneWordTranslatedDerivative H E F hE hF c hEF hEnil hFnil
  simp only [innerExp_apply, neg_neg, mul_assoc] at calcEq ⊢
  exact calcEq

end RankOneSchemeDerivative

section AttachedCorootComparison

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (MatrixGroup diagonalTorus exponentialMatrix)
open _root_.LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive)
open _root_.LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.RootGroups (AdditiveLine IsRootSubgroup rootPoint)
open _root_.LinearAlgebraicGroups.Specs.AbstractPairing (Root IsAttachedCoroot)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open CocharacterDynamics (cocharacterPoint)
open private additiveIso_linear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
open private rootPoint_eq rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private matrixDual from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X} {N : D.I → Matrix J J k}

private theorem exponentialMatrix_rescale (n : Matrix J J k) (c : k) (R : TestAlgebra k) (a : R) :
    exponentialMatrix n R (algebraMap k R c * a) = exponentialMatrix (c • n) R a := by
  unfold exponentialMatrix
  congr 1
  ext i j
  change (algebraMap k R c * a) * algebraMap k R (n i j) =
    a * algebraMap k R (c * n i j)
  rw [map_mul]; ring

omit [CharZero k] in
private theorem rootPoint_change_coordinate {G : GroupScheme k} {A B : AdditiveLine k}
    (U : ClosedSubgroup G) (x : A.group ≅ U.group) (y : B.group ≅ U.group) :
    ∃ c : kˣ, ∀ (R : TestAlgebra k) (a : R),
      rootPoint (x.hom ≫ U.inclusion) R a =
        rootPoint (y.hom ≫ U.inclusion) R (algebraMap k R (c : k) * a) := by
  let e := x ≪≫ y.symm
  obtain ⟨c, hc⟩ := additiveIso_linear A B e
  refine ⟨c, fun R a => ?_⟩
  have h : e.hom ≫ (y.hom ≫ U.inclusion) = x.hom ≫ U.inclusion := by simp [e]
  rw [← h, rootPoint_comp, hc, rootPoint_eq]

set_option maxHeartbeats 2000000 in
private theorem matrixGroup_attached_coroot (G : MatrixGroup D k J w N)
    (hw : Submodule.span ℤ (Set.range w) = ⊤)
    (hG : IsReductive (closedSubgroupAlgebraicGroup G.group))
    (hm : IsGeometricallyMaximal (matrixTorus G))
    (hN : ∀ i, N i ≠ 0 ∧ IsNilpotent (N i) ∧ ∀ a b, N i a b ≠ 0 → w a = w b + D.datum.root i)
    (i : D.I) (α : @Root k _ (closedSubgroupAlgebraicGroup G.group) (matrixTorus G)) (hα : α.val = matrixCharacter k D (D.datum.root i))
    (s : k) (hs : N i * N (D.datum.reflectionPerm i i) - N (D.datum.reflectionPerm i i) * N i =
      s • weightDiagonal w (corootFunctional k i))
    (c : Cocharacter (matrixTorus G).group) (hc : @IsAttachedCoroot k _ (closedSubgroupAlgebraicGroup G.group) (matrixTorus G) α c) :
    c = Additive.toMul (diagonalCocharacters k D (D.datum.coroot i)) := by
  obtain ⟨C, c₀, _, _, P, Q, _, _, _, _, A, p, q, hp, hq, _, _, r, hr⟩ := hc
  let U := subgroupOfSubgroup C.subgroup P.contracting
  let V := subgroupOfSubgroup C.subgroup Q.contracting
  let j := D.datum.reflectionPerm i i
  have hneg : D.datum.root j = - D.datum.root i := by
    change D.datum.root (D.datum.reflectionPerm i i) = _
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have hβ : matrixCharacter k D (D.datum.root j) = α.val⁻¹ := by
    have eq (x : D.X) : Additive.toMul (diagonalCharacters k D x) = matrixCharacter k D x :=
      diagonalCharacters_eq k D x
    rw [hneg, hα, ← eq, ← eq, map_neg]
    rfl
  obtain ⟨p', hp'⟩ := matrixGroup_root_coordinate G hG hm i (hN i).1 (hN i).2.2 U (hα ▸ hp)
  obtain ⟨q', hq'⟩ := matrixGroup_root_coordinate G hG hm j (hN j).1 (hN j).2.2 V (hβ.symm ▸ hq)
  obtain ⟨a, ha⟩ := rootPoint_change_coordinate U p.root p'
  obtain ⟨b, hb⟩ := rootPoint_change_coordinate V q.root q'
  let E := (a : k) • N i
  let F := (b : k) • N j
  let H := weightDiagonal w (corootFunctional k i)
  let s' := (a : k) * ((b : k) * s)
  let xpos := p.root.hom ≫ U.inclusion
  let xneg := q.root.hom ≫ V.inclusion
  have hcoord {l : D.I} (x : A.group ⟶ G.group.group) (e : kˣ)
      (h : ∀ (R : TestAlgebra k) (a : R), rootPoint x R a = rootPoint (G.root l) R (algebraMap k R (e : k) * a)) :
      ∀ (R : TestAlgebra k) (a : R),
        ((G.matrixPoints.hom.app R).hom (rootPoint (x ≫ G.group.inclusion) R a)).val =
          exponentialMatrix ((e : k) • N l) R a := by
    intro R t
    rw [rootPoint_comp, h, ← rootPoint_comp, G.rootMatrix, exponentialMatrix_rescale]
  have heq := hcoord xpos a (fun R t => (ha R t).trans (by rw [hp']))
  have hfeq := hcoord xneg b (fun R t => (hb R t).trans (by rw [hq']))
  have hshiftE (a b : J) (h : E a b ≠ 0) : w a = w b + D.datum.root i :=
    (hN i).2.2 a b (fun hz => h (by simp [E, Matrix.smul_apply, hz]))
  have hshiftF (a b : J) (h : F a b ≠ 0) : w a = w b + D.datum.root j :=
    (hN j).2.2 a b (fun hz => h (by simp [F, Matrix.smul_apply, hz]))
  have hβv : corootFunctional k i (D.datum.root j) = -2 := by
    rw [hneg, map_neg, corootFunctional_root]
  have hE : ⁅H, E⁆ = (2 : k) • E := by
    have e := weightDiagonal_bracket (w := w) (N := fun _ : D.I => E)
      (α := fun _ => D.datum.root i) (fun _ => hshiftE) (corootFunctional k i) i
    change H * E - E * H = corootFunctional k i (D.datum.root i) • E at e
    rw [corootFunctional_root] at e
    exact e
  have hF : ⁅H, F⁆ = (-2 : k) • F := by
    have e := weightDiagonal_bracket (w := w) (N := fun _ : D.I => F)
      (α := fun _ => D.datum.root j) (fun _ => hshiftF) (corootFunctional k i) i
    change H * F - F * H = corootFunctional k i (D.datum.root j) • F at e
    rw [hβv] at e
    exact e
  have hEF : ⁅E, F⁆ = s' • H := by
    change ⁅(a : k) • N i, (b : k) • N j⁆ = _
    rw [smul_lie, lie_smul, show ⁅N i, N j⁆ = s • H from hs, smul_smul, smul_smul, mul_assoc]
  have deriv := rankOneCoroot_matrix_derivative G α.val xpos xneg r H E F
    ((hN i).2.1.smul (a : k)) ((hN j).2.1.smul (b : k)) hE hF s' hEF heq hfeq
  let R := CommAlgCat.of k (DualNumber k)
  let t := onePlusInfinitesimal (Multiplicative.ofAdd (1 : k))
  let z := cocharacterPoint r.coroot R t
  let M := ((G.matrixPoints.hom.app R).hom (z ≫ (G.torus ≫ G.group.inclusion).hom.hom)).val
  change (matrixDual M).snd = _ at deriv
  have nF : F ≠ 0 := smul_ne_zero b.ne_zero (hN j).1
  obtain ⟨v, u, hvu⟩ : ∃ v u, F v u ≠ 0 := by
    by_contra! eq
    exact nF (Matrix.ext eq)
  have huv := hshiftF v u hvu
  have hne : v ≠ u := fun h => D.datum.ne_zero j
    (add_left_cancel ((congrArg w h).symm.trans huv |>.symm.trans (add_zero _).symm))
  have he₀ : E v u = 0 := by
    by_contra h
    have eq := add_left_cancel ((hshiftE v u h).symm.trans huv)
    have eq' := congrArg (corootFunctional k i) eq
    rw [corootFunctional_root, hβv] at eq'
    norm_num at eq'
  have hh₀ : H v u = 0 := Matrix.diagonal_apply_ne _ hne
  have hm₀ : (matrixDual M).snd v u = 0 := by
    change (M v u).snd = 0
    rw [show M = _ from G.torusMatrix R z, Matrix.diagonal_apply_ne _ hne, TrivSqZeroExt.snd_zero]
  have eq := congrArg (fun m : Matrix J J k => m v u) deriv
  rw [hm₀, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.smul_apply, hh₀, he₀, smul_zero, smul_zero, zero_add, zero_add, smul_eq_mul] at eq
  have hs₁ : s' = 1 := (sub_eq_zero.mp ((mul_eq_zero.mp eq.symm).resolve_right hvu)).symm
  have hd : (matrixDual M).snd = H := by
    rw [deriv, hs₁]
    norm_num
  rw [← hr]
  apply cocharacter_eq_of_matrix_coefficients G hw _ i
  intro R' t' z' l
  have h := congrArg (fun d : Matrix J J k => d l l) hd
  exact h.trans (Matrix.diagonal_apply_eq _ _)

end AttachedCorootComparison

section BorelBaseChange

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization (multiplicativeLine)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (characterValue)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)
open CocharacterDynamics (LimitDecomposition HasExtension unitPoint unitCoordinates)
open private unitEquiv unitEquiv_unitPoint subgroupInclusionFactors
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private cocharacter_ext_units map_hasLimit subgroupIso_of_same
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem multLineValue_unitPoint (R : TestAlgebra k) (t : Rˣ) :
    characterValue (𝟙 (multiplicativeLine k)) R (unitPoint R t) = t.val := by
  rw [characterValue_id_coordinate R (unitCoordinates R t) _ rfl]
  rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  change (t ^ (1 : ℤ)).val = t.val
  rw [zpow_one]

private theorem multLineValue_injective (R : TestAlgebra k) :
    Function.Injective (characterValue (𝟙 (multiplicativeLine k)) R) := by
  intro a b h
  have hUnit (p : GroupPoints (multiplicativeLine k) R) : unitPoint R (unitEquiv R p) = p :=
    (unitEquiv R).injective (unitEquiv_unitPoint R (unitEquiv R p))
  apply (unitEquiv R).injective
  apply Units.ext
  rw [← multLineValue_unitPoint R (unitEquiv R a), ← multLineValue_unitPoint R (unitEquiv R b),
    hUnit, hUnit]
  exact h

private theorem limitMultiplicativeExtension_eq
    (e : multiplicativeLine K ≅ (groupBaseChange k K).obj (multiplicativeLine k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      baseChangePoint k K (multiplicativeLine k).X R (unitPoint R s ≫ e.hom.hom.hom) =
        unitPoint ((restrictTestAlgebra k K).obj R) s) :
    e.hom = (diagonalBaseChange k K IntegerCharacters).inv := by
  apply cocharacter_ext_units
  intro R s
  apply (baseChangePoints k K (multiplicativeLine k).X R).injective
  change baseChangePoint k K (multiplicativeLine k).X R (unitPoint R s ≫ e.hom.hom.hom) =
    baseChangePoint k K (multiplicativeLine k).X R
      (unitPoint R s ≫ (diagonalBaseChange k K IntegerCharacters).inv.hom.hom)
  rw [he]
  apply multLineValue_injective ((restrictTestAlgebra k K).obj R)
  rw [diagonalBaseChange_characterValue, multLineValue_unitPoint, multLineValue_unitPoint]

private theorem postcomposeHasExtension {k : Type u} [Field k] {A G : GroupScheme k}
    (f : A ⟶ G) (c : Cocharacter A) {R : TestAlgebra k} {x : GroupPoints A R}
    (h : HasExtension c x) :
    HasExtension (c ≫ f) (show GroupPoints G R from x ≫ f.hom.hom) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z ≫ f.hom.hom, map_hasLimit f c hz⟩

set_option maxHeartbeats 2100000 in
/-- The regular limit subgroup follows the marked cocharacter under base change. -/
private theorem limit_parabolic_baseChange_iso
    (G : AffineAlgebraicGroup k) (H : AffineAlgebraicGroup K)
    (c : Cocharacter G.val) (c' : Cocharacter H.val)
    (B : LimitDecomposition c) (B' : LimitDecomposition c')
    (e : (groupBaseChange k K).obj G.val ≅ H.val)
    (hc : (diagonalBaseChange k K IntegerCharacters).inv ≫
      (groupBaseChange k K).map c ≫ e.hom = c') :
    ∃ b : (groupBaseChange k K).obj B.parabolic.group ≅ B'.parabolic.group,
      (groupBaseChange k K).map B.parabolic.inclusion ≫ e.hom = b.hom ≫ B'.parabolic.inclusion := by
  obtain ⟨d, hd, hp, _, _, hP, _⟩ := CocharacterDynamics.limitSubgroupsBaseChange (K := K) G c B
  have hde := limitMultiplicativeExtension_eq d hd
  let G' := baseChangedAlgebraicGroup K G
  let S : ClosedSubgroup G'.val := scalarExtendedSubgroup K B.parabolic hp
  let S' := transportSubgroup e S
  let x := d.hom ≫ (groupBaseChange k K).map c
  have heq : x ≫ e.hom = c' := by
    dsimp only [x]
    rw [hde, Category.assoc, hc]
  have hinv : c' ≫ e.inv = x := by rw [← heq, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hS : CocharacterDynamics.RepresentsOnAlgebras S (fun _ p => HasExtension x p) := hP
  have hSaff : IsAffine S.group.X.left := (closedSubgroupAlgebraicGroup S).property.1
  have hBaff : IsAffine B'.parabolic.group.X.left := (closedSubgroupAlgebraicGroup B'.parabolic).property.1
  obtain ⟨j, hj⟩ := subgroupInclusionFactors hSaff B'.parabolic (S.inclusion ≫ e.hom) (by
    intro R t
    let z : GroupPoints G'.val R := t ≫ S.inclusion.hom.hom
    have ht : HasExtension x z := (hS R z).mpr ⟨t, rfl⟩
    have hz := postcomposeHasExtension e.hom x ht
    rw [heq] at hz
    exact (B'.parabolic_points R _).mp (show HasExtension c' _ from hz))
  obtain ⟨j', hj'⟩ := subgroupInclusionFactors hBaff S (B'.parabolic.inclusion ≫ e.inv) (by
    intro R t
    let z : GroupPoints H.val R := t ≫ B'.parabolic.inclusion.hom.hom
    have ht : HasExtension c' z := (B'.parabolic_points R z).mpr ⟨t, rfl⟩
    have hz := postcomposeHasExtension e.inv c' ht
    rw [hinv] at hz
    exact (hS R _).mp (show HasExtension x _ from hz))
  have hj'' : j' ≫ S'.inclusion = B'.parabolic.inclusion := by
    change j' ≫ S.inclusion ≫ e.hom = B'.parabolic.inclusion
    rw [← Category.assoc, hj', Category.assoc, e.inv_hom_id, Category.comp_id]
  obtain ⟨b, hb⟩ := subgroupIso_of_same
    (A := S') (B := B'.parabolic) ⟨⟨j, hj⟩, ⟨j', hj''⟩⟩
  exact ⟨b, hb.symm⟩

end BorelBaseChange

section RationalPinning

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open _root_.LinearAlgebraicGroups.Specs.Pinning
  (BasedRootDatum SplitBorelPair AttachedDatum BasedIso SimpleRoot PinnedGroup)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization
  (MatrixGroup diagonalTorus Realization ExtendsRational RationalField)
open _root_.LinearAlgebraicGroups.Specs.OrderedRootProducts (RootSubgroupFamily)
open _root_.LinearAlgebraicGroups.Specs.RootGroups (AdditiveLine rootPoint)
open _root_.LinearAlgebraicGroups.Specs.CharacterDescent (Character Cocharacter)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (pairing)
open _root_.LinearAlgebraicGroups.Specs.DiagonalizableGroups
  (groupAlgebraMap IntegerCharacters)
open _root_.LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)

section MarkedRealization

variable {k J : Type u} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X} {N : D.I → Matrix J J k}
variable {G : MatrixGroup D k J w N}

private structure MarkedMatrixRealization (B : MatrixBorel G) where
  roots : RootSubgroupFamily B.pair.T
  pins : Specs.Pinning.Pinning G.additive B.pair roots
  attached : AttachedDatum B.pair
  marking : BasedIso D attached.toBased
  character_eq : ∀ x, marking.val.weightEquiv x = diagonalCharacters k D x
  cocharacter_eq : ∀ y, marking.val.coweightEquiv.symm y = diagonalCocharacters k D y
  index_eq : ∀ i, marking.val.indexEquiv i = B.rootIndex i
  coordinates : ∀ a : SimpleRoot B.pair,
    (pins a).val.hom ≫ (roots a.val).val.inclusion = G.root (B.rootIndex.symm a.val)

private def MarkedMatrixRealization.realization {B : MatrixBorel G}
    (R : MarkedMatrixRealization B) : Realization D G.additive :=
  ⟨⟨B.pair, R.roots, R.pins⟩, R.attached, R.marking⟩

private theorem MarkedMatrixRealization.rootMap_eq {B : MatrixBorel G}
    (R : MarkedMatrixRealization B) (i : D.base.support) :
    R.realization.rootMap i = G.root i.val := by
  let a := R.realization.simpleRoot i
  have he : B.rootIndex.symm a.val = i.val := by
    change B.rootIndex.symm (R.marking.val.indexEquiv i.val) = i.val
    rw [R.index_eq, Equiv.symm_apply_apply]
  change (R.pins a).val.hom ≫ (R.roots a.val).val.inclusion = _
  rw [R.coordinates, he]

set_option maxHeartbeats 1600000 in
private theorem MatrixBorel.markedRealization (B : MatrixBorel G)
    (hw : Submodule.span ℤ (Set.range w) = ⊤)
    (hN : ∀ i, N i ≠ 0 ∧ IsNilpotent (N i) ∧ ∀ a b, N i a b ≠ 0 → w a = w b + D.datum.root i)
    (hcoroot : ∀ i, ∃ s : k, N i * N (D.datum.reflectionPerm i i) -
      N (D.datum.reflectionPerm i i) * N i = s • weightDiagonal w (corootFunctional k i)) :
    Nonempty (MarkedMatrixRealization B) := by
  classical
  obtain ⟨U, p, hp⟩ := B.pinning (fun i => (hN i).1) (fun i => (hN i).2.2)
  let A := LinearAlgebraicGroups.Classification.Pinning.attachedDatum B.pair
  letI := A.comm
  let f := diagonalCharacters k D
  let g := diagonalCocharacters k D
  let e := B.rootIndex
  have hco (i : D.I) : A.datum.rootDatum.coroot (e i) = g (D.datum.coroot i) := by
    obtain ⟨s, hs⟩ := hcoroot i
    apply Additive.toMul.injective
    exact matrixGroup_attached_coroot G hw B.reductive B.maximal hN i (e i)
      (B.rootCharacter i) s hs _ (A.datum.attached (e i))
  let r : D.datum.Equiv A.toBased.datum :=
    { weightMap := f.toLinearMap
      coweightMap := g.symm.toLinearMap
      indexEquiv := e
      weight_coweight_transpose := by
        ext y x
        obtain ⟨z, rfl⟩ := g.surjective y
        change A.datum.rootDatum.toLinearMap (f x) (g z) =
          D.datum.toLinearMap x (g.symm (g z))
        rw [LinearEquiv.symm_apply_apply]
        exact (A.datum.pairing_eq (Additive.toMul (f x)) (Additive.toMul (g z))).trans
          (diagonalPairing k D x z)
      root_weightMap := by
        funext i
        change f (D.datum.root i) = A.datum.rootDatum.root (e i)
        rw [A.datum.root_eq]
        apply Additive.toMul.injective
        exact (diagonalCharacters_eq k D _).trans (B.rootCharacter i).symm
      coroot_coweightMap := by
        funext a
        obtain ⟨i, rfl⟩ := e.surjective a
        change g.symm (A.datum.rootDatum.coroot (e i)) = D.datum.coroot (e.symm (e i))
        rw [hco i, LinearEquiv.symm_apply_apply, Equiv.symm_apply_apply]
      bijective_weightMap := f.bijective
      bijective_coweightMap := g.symm.bijective }
  have hf (x : D.X) : Additive.toMul (f x) = matrixCharacter k D x :=
    diagonalCharacters_eq k D x
  have hs (i : D.I) : e i ∈ A.base.support ↔ i ∈ D.base.support :=
    (A.simple_iff (e i)).trans (B.simple_iff f hf i)
  have hbase : e '' (D.base.support : Set D.I) = (A.toBased.base.support : Set A.toBased.I) := by
    ext a
    obtain ⟨i, rfl⟩ := e.surjective a
    constructor
    · rintro ⟨j, hj, h⟩
      exact (hs i).mpr (show i ∈ D.base.support from e.injective h ▸ hj)
    · intro hi
      exact ⟨i, (hs i).mp hi, rfl⟩
  refine ⟨⟨U, p, A, ⟨r, hbase⟩, fun _ => rfl, ?_, fun _ => rfl, hp⟩⟩
  intro y
  apply r.coweightEquiv.injective
  rw [r.coweightEquiv.apply_symm_apply]
  exact (g.symm_apply_apply y).symm

end MarkedRealization

local instance : CharZero (RationalField.{u}) := by
  let e : ℚ ≃+* RationalField.{u} := ULift.ringEquiv.symm
  exact charZero_of_injective_ringHom (f := e.toRingHom) e.injective

section ExtensionOfMarkings

variable {k J : Type u} [Field k] [CharZero k] [Algebra (RationalField.{u}) k]
  [Fintype J] [DecidableEq J]
variable {D : BasedRootDatum.{u}} {w : J → D.X}
variable {N : D.I → Matrix J J (RationalField.{u})} {N' : D.I → Matrix J J k}

set_option maxHeartbeats 1850000 in
private theorem matrixRealization_baseChange
    {G : MatrixGroup D (RationalField.{u}) J w N} {H : MatrixGroup D k J w N'}
    {B : MatrixBorel G} {C : MatrixBorel H}
    (Q : MarkedMatrixRealization B) (K : MarkedMatrixRealization C)
    (h : N' = fun i => (algebraMap RationalField k).mapMatrix (N i))
    (y : D.Y) (hB : B.direction = Additive.toMul (diagonalCocharacters RationalField D y))
    (hC : C.direction = Additive.toMul (diagonalCocharacters k D y)) :
    Nonempty (ExtendsRational Q.realization K.realization) := by
  subst N'
  obtain ⟨⟨e, t, a, ht, ha, htorus, hroot⟩⟩ := matrixGroup_baseChange G H
  subst t
  let F := groupBaseChange RationalField k
  let t := diagonalBaseChange RationalField k (Multiplicative D.X)
  let m := diagonalBaseChange RationalField k IntegerCharacters
  have hχ (x : D.X) :
      F.map (Additive.toMul (diagonalCharacters RationalField D x)) ≫ m.hom =
        t.hom ≫ Additive.toMul (diagonalCharacters k D x) := by
    rw [diagonalCharacters_eq RationalField D x, diagonalCharacters_eq k D x]
    exact diagonalBaseChange_natural RationalField k _
  have hcochar (z : D.Y) :
      F.map (Additive.toMul (diagonalCocharacters RationalField D z)) ≫ t.hom =
        m.hom ≫ Additive.toMul (diagonalCocharacters k D z) := by
    rw [diagonalCocharacters_eq RationalField D z, diagonalCocharacters_eq k D z]
    exact diagonalBaseChange_natural RationalField k _
  have c : m.inv ≫ F.map (B.direction ≫ G.torus) ≫ e.hom = C.direction ≫ H.torus := by
    calc
      _ = m.inv ≫ (F.map B.direction ≫ t.hom) ≫ H.torus := by
        simp only [F, t, Functor.map_comp, Category.assoc, htorus]
      _ = _ := by
        rw [hB, hcochar, hC]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
  obtain ⟨b, hb⟩ := limit_parabolic_baseChange_iso (closedSubgroupAlgebraicGroup G.group)
    (closedSubgroupAlgebraicGroup H.group) _ _ B.limits C.limits e c
  refine ⟨⟨e, t, b, a, m, ha, diagonalBaseChange_characterValue RationalField k,
    htorus, hb, ?_, ?_, ?_⟩⟩
  · intro i
    rw [Q.rootMap_eq, K.rootMap_eq]
    exact hroot i
  · intro x
    change F.map (Additive.toMul (Q.marking.val.weightEquiv x)) ≫ m.hom =
      t.hom ≫ Additive.toMul (K.marking.val.weightEquiv x)
    rw [Q.character_eq, K.character_eq]
    exact hχ x
  · intro y
    change F.map (Additive.toMul (Q.marking.val.coweightEquiv.symm y)) ≫ t.hom =
      m.hom ≫ Additive.toMul (K.marking.val.coweightEquiv.symm y)
    rw [Q.cocharacter_eq, K.cocharacter_eq]
    exact hcochar y

end ExtensionOfMarkings

section RealizationOverRationals

/-- The same rational root coefficients have the same entrywise image along
any tower of characteristic-zero fields. -/
private theorem rationalMatrix_map_tower
    {k K J : Type u} [Field k] [Field K] [CharZero k] [CharZero K] [Algebra k K]
    [Fintype J] [DecidableEq J] (N : Matrix J J ℚ) :
    (algebraMap ℚ K).mapMatrix N = (algebraMap k K).mapMatrix ((algebraMap ℚ k).mapMatrix N) := by
  have h : (algebraMap k K).comp (algebraMap ℚ k) = algebraMap ℚ K := Subsingleton.elim _ _
  ext a b
  exact (RingHom.congr_fun h (N a b)).symm

set_option maxHeartbeats 2100000 in
/-- The characteristic-zero realization of the full based root datum from C08. -/
theorem existsRationalRealization : Specs.RationalRealization.Statement.{u} := by
  intro D
  classical
  by_cases h : IsEmpty D.I
  · obtain ⟨A, Q, hQ, hK⟩ := rootlessRealization D h
    exact ⟨A, Q, fun _ => hQ, hK⟩
  obtain ⟨J, _, _, w, d, N, L, hw, _, hd, hL, hb, hN, hco⟩ := rationalRootOperators D
  obtain ⟨y, m, hm, hy⟩ := positiveIntegralCocharacter D
  let Nₖ (k : Type u) [Field k] [CharZero k] i := (algebraMap ℚ k).mapMatrix (N i)
  have hroot (k : Type u) [Field k] [CharZero k] (i : D.I) :=
    extendRootMatrix w i (N i) (hN i) k
  have existsGroup (k : Type u) [Field k] [CharZero k] : Nonempty (MatrixGroup D k J w (Nₖ k)) :=
    generateMatrixGroup D w (Nₖ k) hw (hroot k)
      (rationalLatticeMatrixSpan_bracket w N d hd L hL hb k)
  have hbr (k : Type u) [Field k] [CharZero k] (i : D.I) :=
    rationalCorootBracket_over (k := k) w N d hd hco i
  have construct (k : Type u) [Field k] [CharZero k] :
      ∃ (G : MatrixGroup D k J w (Nₖ k)) (B : MatrixBorel G) (M : MarkedMatrixRealization B),
        B.direction = Additive.toMul (diagonalCocharacters k D y) := by
    let E := AlgebraicClosure k
    obtain ⟨G⟩ := existsGroup k
    obtain ⟨G₀⟩ := existsGroup E
    let N' (i : D.I) := (algebraMap k E).mapMatrix (Nₖ k i)
    have hcomp : Nₖ E = N' := funext fun i => rationalMatrix_map_tower (N i)
    have G' : MatrixGroup D E J w N' := hcomp ▸ G₀
    have hshift : ∀ i a b, N' i a b ≠ 0 → w a = w b + D.datum.root i := by
      rw [← hcomp]
      exact fun i => (hroot E i).2.2
    have hop : ∀ r, ∃ s φ,
        N' s * N' r - N' r * N' s = weightDiagonal w φ ∧ weightDiagonal w φ ≠ 0 := by
      rw [← hcomp]
      intro r
      obtain ⟨c, hc, he⟩ := hbr E r
      refine ⟨D.datum.reflectionPerm r r, (-c) • corootFunctional E r, ?_, ?_⟩
      · rw [← neg_sub, he, map_smul, neg_smul]
      · rw [map_smul]
        exact smul_ne_zero (neg_ne_zero.mpr hc) (corootDiagonal_ne_zero w hw r)
    obtain ⟨hG, hM⟩ := matrixGroup_reductive_and_maximal G G' hshift hop
    let c := Additive.toMul (diagonalCocharacters k D y)
    have hc (i : D.I) : pairing (diagonalTorus k D).val (matrixCharacter k D (D.datum.root i)) c =
        m * D.base.height i := by
      have hmark : Additive.toMul (diagonalCharacters k D (D.datum.root i)) =
          matrixCharacter k D (D.datum.root i) := diagonalCharacters_eq k D _
      rw [← hmark]
      exact (diagonalPairing k D (D.datum.root i) y).trans (hy i)
    obtain ⟨B, hB⟩ := matrixGroup_borel G hG hM (fun i => (hroot k i).1) (fun i => (hroot k i).2.2)
      c m hm hc
    obtain ⟨P⟩ := B.markedRealization hw (hroot k) (fun i => by
      obtain ⟨a, _, ha⟩ := hbr k i
      exact ⟨a, ha⟩)
    exact ⟨G, B, P, hB⟩
  obtain ⟨G, B, Q, hQ⟩ := construct RationalField
  refine ⟨G.additive, Q.realization, fun hh => (h hh).elim, ?_⟩
  intro k _ _
  letI : Algebra (RationalField.{u}) k :=
    ((algebraMap ℚ k).comp ULift.ringEquiv.toRingHom).toAlgebra
  obtain ⟨H, C, K, hK⟩ := construct k
  refine ⟨H.additive, K.realization, matrixRealization_baseChange Q K ?_ y hQ hK⟩
  exact funext fun i => rationalMatrix_map_tower (N i)

end RealizationOverRationals

end RationalPinning

end

end LinearAlgebraicGroups.RationalRealization
