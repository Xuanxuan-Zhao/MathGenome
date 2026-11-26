import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TypeCSplitRecognition
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OddSpinModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Tactic.LinearCombination

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial Matrix Topology
open scoped Matrix
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels

universe u v

namespace LinearAlgebraicGroups.Arithmetic.OddSpinModels

private theorem squareRootAlgebraFin (A : Type u) [CommRing A] [Nontrivial A] (n : ℕ)
    (c : Fin n → A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Nontrivial B) (z : Fin n → B),
      PresentsSquareRoots c z ∧ Module.Free A B ∧ Module.Finite A B := by
  induction n with
  | zero =>
    refine ⟨A, inferInstance, inferInstance, inferInstance, Fin.elim0, ⟨?_, ?_⟩, inferInstance,
      inferInstance⟩
    · exact fun i => Fin.elim0 i
    · intro S _ f l hl
      refine ⟨f, ⟨by simp, fun i => Fin.elim0 i⟩, ?_⟩
      rintro g ⟨hg, _⟩
      simpa using hg
  | succ n ih =>
    obtain ⟨C, hC, hAC, hnonC, z, ⟨hz, hLift⟩, hfreeC, hfiniteC⟩ :=
      ih (fun i => c i.succ)
    let p : C[X] := X ^ 2 - Polynomial.C (algebraMap A C (c 0))
    let B := AdjoinRoot p
    let w : Fin (n + 1) → B :=
      Fin.cons (AdjoinRoot.root p) (fun i => AdjoinRoot.of p (z i))
    have hp : p.Monic := monic_X_pow_sub_C _ (by decide)
    have hpdeg : p.natDegree = 2 := natDegree_X_pow_sub_C
    have hf : Function.Injective (AdjoinRoot.of p) :=
      AdjoinRoot.of.injective_of_monic_of_degree_pos hp
        (by rw [Polynomial.degree_eq_natDegree hp.ne_zero, hpdeg]; decide)
    have : Nontrivial B := hf.nontrivial
    have : Module.Free C B := hp.free_adjoinRoot
    have : Module.Finite C B := hp.finite_adjoinRoot
    refine ⟨B, inferInstance, inferInstance, inferInstance, w, ⟨?_, ?_⟩,
      Module.Free.trans (S := C), Module.Finite.trans C B⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change AdjoinRoot.root p ^ 2 = algebraMap A B (c 0)
        have h := AdjoinRoot.eval₂_root p
        dsimp only [p] at h
        simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
        rw [AdjoinRoot.algebraMap_eq']
        exact h
      · change (AdjoinRoot.of p (z j)) ^ 2 = algebraMap A B (c j.succ)
        rw [← map_pow, hz j, AdjoinRoot.algebraMap_eq']
        rfl
    · intro S _ f l hl
      obtain ⟨g, ⟨hg, hgz⟩, hu⟩ := hLift S f (fun i => l i.succ) (fun i => hl i.succ)
      have hroot : p.eval₂ g (l 0) = 0 := by
        simp only [p, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero, hl]
        exact DFunLike.congr_fun hg.symm (c 0)
      let e := AdjoinRoot.lift g (l 0) hroot
      refine ⟨e, ⟨?_, ?_⟩, ?_⟩
      · rw [AdjoinRoot.algebraMap_eq', ← RingHom.comp_assoc, AdjoinRoot.lift_comp_of, hg]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact AdjoinRoot.lift_root _
        · exact (AdjoinRoot.lift_of hroot).trans (hgz j)
      · rintro e' ⟨he', hw⟩
        apply AdjoinRoot.ringHom_ext
        · rw [AdjoinRoot.lift_comp_of]
          refine hu _ ⟨?_, fun j => hw j.succ⟩
          rw [RingHom.comp_assoc, ← AdjoinRoot.algebraMap_eq', he']
        · exact (hw 0).trans (AdjoinRoot.lift_root hroot).symm

private theorem square_eq_square_injective {S : Type u} [Field S] (h₂ : (2 : S) = 0)
    {a b : S} (h : a ^ 2 = b ^ 2) : a = b := by
  have hz : (a - b) ^ 2 = 0 := by
    rw [sub_sq, h₂, zero_mul, zero_mul, sub_zero, h]
    linear_combination h₂ * b ^ 2
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)

private theorem squareRootRadicial {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type v} {c : ι → A} {z : ι → B} (h : PresentsSquareRoots c z)
    (h₂ : (2 : A) = 0) :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  apply (tfae_universallyInjective _).out 2 1 |>.mp
  intro S _ g₁ g₂ hg
  obtain ⟨f₁, rfl⟩ := Spec.map_surjective g₁
  obtain ⟨f₂, rfl⟩ := Spec.map_surjective g₂
  simp only [← Spec.map_comp] at hg
  have he : f₁.hom.comp (algebraMap A B) = f₂.hom.comp (algebraMap A B) := by
    have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using h'
  have hchar : (2 : S) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (f₁.hom.comp (algebraMap A B)) h₂
  have hp₁ (i : ι) : (f₁.hom (z i)) ^ 2 = (f₁.hom.comp (algebraMap A B)) (c i) := by
    rw [← map_pow, h.1 i]; rfl
  have hp₂ (i : ι) : (f₂.hom (z i)) ^ 2 = (f₁.hom.comp (algebraMap A B)) (c i) := by
    rw [he, ← map_pow, h.1 i]; rfl
  obtain ⟨g, _, hg⟩ := h.2 S (f₁.hom.comp (algebraMap A B)) (fun i => f₁.hom (z i)) hp₁
  congr 1
  apply CommRingCat.hom_ext
  exact (hg _ ⟨rfl, fun _ => rfl⟩).trans
    (hg _ ⟨he.symm, fun i => square_eq_square_injective hchar ((hp₂ i).trans (hp₁ i).symm)⟩).symm

theorem squareRootProjection : SquareRootProjection.{u, v} := by
  classical
  intro A _ _ ι _ c h₂
  let e := Finite.equivFin ι
  obtain ⟨B, hB, hAB, hnonB, z, ⟨hz, hLift⟩, hfree, hfinite⟩ :=
    squareRootAlgebraFin A _ (c ∘ e.symm)
  have hff : Module.FaithfullyFlat A B := inferInstance
  have hw : PresentsSquareRoots c (z ∘ e) := by
    refine ⟨fun i => by simpa using hz (e i), ?_⟩
    intro S _ f l hl
    obtain ⟨g, ⟨hg, hgz⟩, hu⟩ := hLift S f (l ∘ e.symm) (fun i => hl (e.symm i))
    refine ⟨g, ⟨hg, fun i => by simpa using hgz (e i)⟩, ?_⟩
    rintro g' ⟨hg', hw'⟩
    exact hu g' ⟨hg', fun i => by simpa using hw' (e.symm i)⟩
  let f := CommRingCat.ofHom (algebraMap A B)
  have hf : IsFinite (Spec.map f) :=
    (IsFinite.SpecMap_iff f).mpr (RingHom.finite_algebraMap.mpr hfinite)
  have hfs : Flat (Spec.map f) ∧ Surjective (Spec.map f) :=
    (flat_and_surjective_SpecMap_iff f).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
  exact ⟨B, hB, hAB, z ∘ e, hw, hfree, hfinite, hff, hf, hfs.1, hfs.2,
    squareRootRadicial hw h₂⟩

open LinearAlgebraicGroups.Specs.SymplecticMatrixStructure (Indices PointGroup Coordinates alternatingForm
  universalSymplecticMatrix)
open private Representation Representation.equiv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private symplecticRepresentation tangentMatrix_mem
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure

noncomputable section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {R : Type u} [CommRing R]

theorem hyperbolicForm_apply (x : Indices ι → R) :
    hyperbolicForm ι R x = ∑ i, x (.inl i) * x (.inr i) := by
  rw [hyperbolicForm, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  simp [dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Matrix.one_apply]

theorem hyperbolicForm_standardVector (i : Indices ι) :
    hyperbolicForm ι R (standardVector R i) = 0 := by
  cases i <;> simp [hyperbolicForm_apply, standardVector, Pi.single_apply]

private theorem neg_one_of_two_eq_zero (h₂ : (2 : R) = 0) : (-1 : R) = 1 := by
  linear_combination -h₂

theorem hyperbolicPolar : HyperbolicPolar.{u} := by
  intro ι R _ _ _ h₂
  change (hyperbolicForm ι R).polarBilin = Matrix.toLinearMap₂' R (Matrix.J ι R)
  rw [hyperbolicForm, LinearMap.BilinMap.polarBilin_toQuadraticMap]
  let b := Pi.basisFun R (Indices ι)
  apply b.ext
  intro i
  apply b.ext
  intro j
  let M : Matrix (Indices ι) (Indices ι) R := Matrix.fromBlocks 0 1 0 0
  simp only [b, Pi.basisFun_apply, LinearMap.add_apply, LinearMap.flip_apply]
  change Matrix.toLinearMap₂' R M (Pi.single i 1) (Pi.single j 1) +
      Matrix.toLinearMap₂' R M (Pi.single j 1) (Pi.single i 1) =
    Matrix.toLinearMap₂' R (Matrix.J ι R) (Pi.single i 1) (Pi.single j 1)
  have he (N : Matrix (Indices ι) (Indices ι) R) (a b : Indices ι) :
      Matrix.toLinearMap₂' R N (Pi.single a (1 : R)) (Pi.single b (1 : R)) = N a b := by
    rw [Matrix.toLinearMap₂'_apply', Matrix.mulVec_single_one]
    simp
  rw [he, he, he]
  cases i <;> cases j <;> simp [M, Matrix.J, Matrix.neg_apply, Matrix.one_apply, eq_comm]
  split_ifs <;> simp [neg_one_of_two_eq_zero h₂]

private theorem square_comp_polar {M : Type u} [AddCommGroup M] [Module R M]
    (h₂ : (2 : R) = 0) (l : M →ₗ[R] R) :
    ((QuadraticMap.sq (R := R) (A := R)).comp l).polarBilin = 0 := by
  apply LinearMap.ext₂
  intro x y
  change l (x + y) * l (x + y) - l x * l x - l y * l y = 0
  rw [map_add]
  linear_combination h₂ * l x * l y

private theorem eq_zero_of_zero_polar_of_basis {M : Type u} {I : Type u} [AddCommGroup M]
    [Module R M] [Fintype I] (q : QuadraticForm R M) (b : Module.Basis I R M)
    (hp : q.polarBilin = 0) (hq : ∀ i, q (b i) = 0) (x : M) : q x = 0 := by
  classical
  rw [← b.sum_repr x]
  have hsum (s : Finset I) : q (∑ i ∈ s, b.repr x i • b i) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, QuadraticMap.map_add q, ← QuadraticMap.polarBilin_apply_apply, hp,
        ih, QuadraticMap.map_smul, hq]
      simp
  exact hsum Finset.univ

/-- A pair preserves the odd norm precisely when the equations on basis columns hold. -/
theorem pairEquations : PairEquations.{u} := by
  intro ι R _ _ _ h₂ A l
  constructor
  · intro h i
    have hi := h (standardVector R i)
    rw [hyperbolicForm_standardVector] at hi
    exact eq_neg_of_add_eq_zero_right hi
  · intro h x
    let Q := hyperbolicForm ι R
    let d := Q.comp (Matrix.toLin' A.val) + (QuadraticMap.sq (R := R) (A := R)).comp l - Q
    have hd : d.polarBilin = 0 := by
      have hpol : (Q.comp (Matrix.toLin' A.val)).polarBilin = Q.polarBilin := by
        rw [QuadraticMap.polarBilin_comp, hyperbolicPolar ι R h₂,
          LinearAlgebraicGroups.Specs.SymplecticMatrixStructure.alternatingForm, Matrix.toLinearMap₂'_comp,
          SymplecticGroup.mem_iff'.mp A.property]
      apply LinearMap.ext₂
      intro y z
      have hp := congrArg (fun f : LinearMap.BilinForm R (Indices ι → R) => f y z) hpol
      have hz := congrArg (fun f : LinearMap.BilinForm R (Indices ι → R) => f y z)
        (square_comp_polar h₂ l)
      change _ = 0
      simp only [LinearMap.zero_apply] at hz
      rw [QuadraticMap.polarBilin_apply_apply] at hp hz
      change QuadraticMap.polar
        ((Q.comp (Matrix.toLin' A.val) : (Indices ι → R) → R) +
          ((QuadraticMap.sq (R := R) (A := R)).comp l : (Indices ι → R) → R) -
          (Q : (Indices ι → R) → R)) y z = 0
      rw [sub_eq_add_neg, QuadraticMap.polar_add, QuadraticMap.polar_add, QuadraticMap.polar_neg,
        hp, hz, ← QuadraticMap.polarBilin_apply_apply, add_zero, add_neg_cancel]
    have hb (i : Indices ι) : d (Pi.basisFun R (Indices ι) i) = 0 := by
      rw [Pi.basisFun_apply]
      change hyperbolicForm ι R (A.val *ᵥ standardVector R i) +
        l (standardVector R i) * l (standardVector R i) - hyperbolicForm ι R (standardVector R i) = 0
      rw [← pow_two, h, hyperbolicForm_standardVector, add_neg_cancel, sub_zero]
    have he := eq_zero_of_zero_polar_of_basis d (Pi.basisFun R (Indices ι)) hd hb x
    change hyperbolicForm ι R (A.val *ᵥ x) + l x * l x - hyperbolicForm ι R x = 0 at he
    rw [← pow_two] at he
    exact sub_eq_zero.mp he


private theorem map_universalCoefficient {k : Type u} [Field k] [Algebra k R]
    (f : Coordinates k ι →ₐ[k] R) (i : Indices ι) :
    f (universalCoefficient k ι i) =
      -hyperbolicForm ι R ((f.mapMatrix (universalSymplecticMatrix k ι)) *ᵥ standardVector R i) := by
  simp only [universalCoefficient, standardVector, Matrix.mulVec_single_one,
    hyperbolicForm_apply, map_neg, map_sum, map_mul, Matrix.col_apply]
  rfl

private theorem geometricallyConnected_of_finite_radicial_surjection
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [Surjective f] [UniversallyInjective f] [GeometricallyConnected g] :
    GeometricallyConnected (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.connectedSpace_iff]
  have hconn : ConnectedSpace ↥(pullback g x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback g x)
  let p := pullback.snd f (pullback.fst g x)
  have : UniversallyInjective p :=
    UniversallyInjective.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (pullback.fst g x)) inferInstance
  have hhomeo : IsHomeomorph p :=
    isHomeomorph_iff_isQuotientMap_injective.mpr
      ⟨p.isClosedMap.isQuotientMap p.continuous p.surjective, p.injective⟩
  exact (hhomeo.homeomorph p).connectedSpace_iff.mpr hconn

theorem pairCoordinatePresentation : PairCoordinatePresentation.{u} := by
  intro k ι _ _ _ h₂
  let A := Coordinates k ι
  let equiv (R : Type u) [CommRing R] [Algebra k R] : (A →ₐ[k] R) ≃ PointGroup ι R :=
    Representation.equiv (symplecticRepresentation (k := k) (ι := ι)) (CommAlgCat.of k R)
  have : Nontrivial A := ((equiv k).symm 1).toRingHom.domain_nontrivial
  have hA : (2 : A) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap k A) h₂
  obtain ⟨B, hB, hAB, z, hz, hfree, hfinite, hff, hp⟩ :=
    squareRootProjection A (Indices ι) (universalCoefficient k ι) hA
  let p := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have hfin : IsFinite p := hp.1
  have hsurj : Surjective p := hp.2.2.1
  have hrad : UniversallyInjective p := hp.2.2.2
  let g := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hgc : GeometricallyConnected g := SymplecticMatrixStructure.geometricConnectedness k ι
  have hpconn : GeometricallyConnected (p ≫ g) :=
    geometricallyConnected_of_finite_radicial_surjection p g
  have hhomeo : IsHomeomorph p :=
    isHomeomorph_iff_isQuotientMap_injective.mpr
      ⟨p.isClosedMap.isQuotientMap p.continuous p.surjective, p.injective⟩
  have hdim : ringKrullDim B = ringKrullDim A := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact IsHomeomorph.topologicalKrullDim_eq p hhomeo
  refine ⟨B, hB, hAB, z, hz, hfree, hfinite, hff, ⟨hfin, hp.2.1, hsurj, hrad, hpconn⟩,
    hdim.trans (SymplecticMatrixStructure.dimension k ι), ?_⟩
  intro R _ _
  refine ⟨equiv R, fun f i j => rfl, ?_⟩
  intro f l
  have hchar : (2 : R) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap k R) h₂
  rw [pairEquations ι R hchar]
  have hc (i : Indices ι) :
      f (universalCoefficient k ι i) =
        -hyperbolicForm ι R (((equiv R) f).val *ᵥ standardVector R i) :=
    map_universalCoefficient f i
  constructor
  · intro h
    exact hz.2 R f.toRingHom (fun i => l (standardVector R i)) (fun i => (h i).trans (hc i).symm)
  · rintro ⟨g, ⟨hg, hl⟩, _⟩ i
    rw [← hl, ← map_pow, hz.1, ← RingHom.comp_apply, hg]
    exact hc i

theorem oddForm_apply (x : (Indices ι → R) × R) :
    oddForm ι R x = hyperbolicForm ι R x.1 + x.2 ^ 2 := by
  rw [pow_two]
  rfl

theorem oddForm_polar_apply (h₂ : (2 : R) = 0) (x y : (Indices ι → R) × R) :
    (oddForm ι R).polarBilin x y = (hyperbolicForm ι R).polarBilin x.1 y.1 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, oddForm_apply, Prod.fst_add,
    Prod.snd_add]
  linear_combination h₂ * x.2 * y.2

theorem fixesNormComparison : FixesNormComparison.{u} := by
  intro ι R _ _ _ h₂ g hr
  constructor
  · intro hg
    let L := g.toLinearMap.comp (LinearMap.inl R (Indices ι → R) R)
    let M := (LinearMap.fst R (Indices ι → R) R).comp L
    let l := (LinearMap.snd R (Indices ι → R) R).comp L
    let A := LinearMap.toMatrix' M
    have hM : Matrix.toLin' A = M := Matrix.toLin'_toMatrix' M
    have hAx (x : Indices ι → R) : A *ᵥ x = (g (x, 0)).1 :=
      congrArg (fun f : (Indices ι → R) →ₗ[R] (Indices ι → R) => f x) hM
    have hpol (x y : (Indices ι → R) × R) :
        (oddForm ι R).polarBilin (g x) (g y) = (oddForm ι R).polarBilin x y := by
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add g, hg]
    have hA : A ∈ Matrix.symplecticGroup ι R := by
      rw [SymplecticGroup.mem_iff']
      let e : Matrix (Indices ι) (Indices ι) R ≃ₗ[R] LinearMap.BilinForm R (Indices ι → R) :=
        Matrix.toLinearMap₂' R
      apply e.injective
      change Matrix.toLinearMap₂' R (Aᵀ * Matrix.J ι R * A) =
        Matrix.toLinearMap₂' R (Matrix.J ι R)
      rw [← Matrix.toLinearMap₂'_comp]
      apply LinearMap.ext₂
      intro x y
      have he := hpol (x, 0) (y, 0)
      rw [oddForm_polar_apply h₂, oddForm_polar_apply h₂, hyperbolicPolar ι R h₂] at he
      change Matrix.toLinearMap₂' R (Matrix.J ι R) (g (x, 0)).1 (g (y, 0)).1 =
        Matrix.toLinearMap₂' R (Matrix.J ι R) x y at he
      change Matrix.toLinearMap₂' R (Matrix.J ι R) (A *ᵥ x) (A *ᵥ y) =
        Matrix.toLinearMap₂' R (Matrix.J ι R) x y
      rwa [← hAx, ← hAx] at he
    refine ⟨⟨A, hA⟩, l, ?_, ?_⟩
    · intro x
      have he := hg (x, 0)
      simp only [oddForm_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at he
      rw [hAx]
      exact he
    · intro x t
      rw [show (x, t) = (x, 0) + t • ((0, 1) : (Indices ι → R) × R) by simp,
        map_add, map_smul, hr, hAx]
      apply Prod.ext <;> simp [l, L]
  · rintro ⟨A, l, hl, hap⟩ ⟨x, t⟩
    rw [hap, oddForm_apply, oddForm_apply]
    simp only
    rw [add_sq, h₂, zero_mul, zero_mul, add_zero, ← add_assoc, hl]


theorem pairAction : PairAction.{u} := by
  intro ι R _ _ _ h₂ A l hl
  let H := Indices ι → R
  let f : H ≃ₗ[R] H :=
    (Matrix.GeneralLinearGroup.toLin (SymplecticMatrixStructure.toGeneralLinear A)).toLinearEquiv
  let g : (H × R) ≃ₗ[R] (H × R) :=
    { toFun := fun x => (f x.1, l x.1 + x.2)
      invFun := fun x => (f.symm x.1, x.2 - l (f.symm x.1))
      map_add' := fun x y => by
        apply Prod.ext
        · exact map_add f x.1 y.1
        · simp only [Prod.fst_add, Prod.snd_add, map_add]
          ac_rfl
      map_smul' := fun r x => by
        apply Prod.ext
        · exact map_smul f r x.1
        · simp [mul_add]
      left_inv := fun x => by
        apply Prod.ext
        · exact f.symm_apply_apply x.1
        · simp
      right_inv := fun x => by
        apply Prod.ext
        · exact f.apply_symm_apply x.1
        · simp }
  have hact (x : H) (t : R) : g (x, t) = (A.val *ᵥ x, l x + t) := rfl
  have hr : g (0, 1) = (0, 1) := by rw [hact]; simp
  have hnorm := (fixesNormComparison ι R h₂ g hr).mpr ⟨A, l, hl, hact⟩
  refine ⟨g, ⟨hact, hr, hnorm⟩, ?_⟩
  rintro g' ⟨hg', _⟩
  apply LinearEquiv.ext
  rintro ⟨x, t⟩
  exact (hg' x t).trans (hact x t).symm

theorem splitRadical : SplitRadical.{u} := by
  intro ι R _ _ _ h₂
  constructor
  · ext x
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro hx
      have hf : x.1 = 0 := by
        apply (SymplecticMatrixStructure.perfectAlternatingForm ι R).2.1.1
        intro y
        have h := congrArg (fun f : ((Indices ι → R) × R) →ₗ[R] R => f (y, 0)) hx
        simpa only [oddForm_polar_apply h₂, hyperbolicPolar ι R h₂, LinearMap.zero_apply] using h
      exact ⟨x.2, by apply Prod.ext <;> simp [hf]⟩
    · rintro ⟨t, rfl⟩
      apply LinearMap.ext
      intro y
      rw [oddForm_polar_apply h₂]
      simp
  · simp [oddForm_apply]


section Tangent

variable {k : Type u} [Field k]

private theorem hyperbolicForm_tangent_zero_iff (X : Matrix (Indices ι) (Indices ι) k)
    (i : Indices ι) :
    hyperbolicForm ι (DualNumber k) (tangentMatrix X *ᵥ standardVector (DualNumber k) i) = 0 ↔
      (Matrix.J ι k * X) i i = 0 := by
  simp only [standardVector, Matrix.mulVec_single_one, hyperbolicForm_apply, Matrix.col_apply]
  cases i with
  | inl i =>
    have hq : (∑ j : ι, tangentMatrix X (.inl j) (.inl i) *
        tangentMatrix X (.inr j) (.inl i)) = (⟨0, X (.inr i) (.inl i)⟩ : DualNumber k) := by
      apply TrivSqZeroExt.ext
      · simp only [TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul]
        simp [tangentMatrix, Matrix.one_apply]
      · simp only [TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, smul_eq_mul,
          MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        simp [tangentMatrix, Matrix.one_apply, ite_mul]
    have hJ : (Matrix.J ι k * X) (.inl i) (.inl i) = -X (.inr i) (.inl i) := by
      simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply, ite_mul]
    rw [hq, hJ, neg_eq_zero]
    exact ⟨fun h => congrArg TrivSqZeroExt.snd h, fun h => TrivSqZeroExt.ext rfl h⟩
  | inr i =>
    have hq : (∑ j : ι, tangentMatrix X (.inl j) (.inr i) *
        tangentMatrix X (.inr j) (.inr i)) = (⟨0, X (.inl i) (.inr i)⟩ : DualNumber k) := by
      apply TrivSqZeroExt.ext
      · simp only [TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul]
        simp [tangentMatrix, Matrix.one_apply]
      · simp only [TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, smul_eq_mul,
          MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        simp [tangentMatrix, Matrix.one_apply]
    have hJ : (Matrix.J ι k * X) (.inr i) (.inr i) = X (.inl i) (.inr i) := by
      simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply, ite_mul]
    rw [hq, hJ]
    exact ⟨fun h => congrArg TrivSqZeroExt.snd h, fun h => TrivSqZeroExt.ext rfl h⟩


theorem pairTangent : PairTangent.{u} := by
  intro k ι _ _ _ h₂ X l hl
  have h₂' : (2 : DualNumber k) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap k (DualNumber k)) h₂
  have hl₂ (i : Indices ι) : l (standardVector (DualNumber k) i) ^ 2 = 0 := by
    rw [pow_two]
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, hl]
    · simp [TrivSqZeroExt.snd_mul, hl]
  have hM : tangentMatrix X ∈ Matrix.symplecticGroup ι (DualNumber k) ↔
      (Matrix.J ι k * X).IsSymm := tangentMatrix_mem X
  constructor
  · rintro ⟨A, hA, hp⟩
    refine ⟨hM.mp (hA ▸ A.property), fun i => (hyperbolicForm_tangent_zero_iff X i).mp ?_⟩
    have he := (pairEquations ι (DualNumber k) h₂' A l).mp hp i
    rw [hl₂, hA] at he
    simpa using he.symm
  · rintro ⟨hsym, hdiag⟩
    let A : PointGroup ι (DualNumber k) := ⟨tangentMatrix X, hM.mpr hsym⟩
    refine ⟨A, rfl, (pairEquations ι (DualNumber k) h₂' A l).mpr fun i => ?_⟩
    have hzero := (hyperbolicForm_tangent_zero_iff X i).mpr (hdiag i)
    change l (standardVector (DualNumber k) i) ^ 2 =
      -hyperbolicForm ι (DualNumber k) (tangentMatrix X *ᵥ standardVector (DualNumber k) i)
    rw [hl₂, hzero, neg_zero]

end Tangent

private theorem span_coroots (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Submodule.span ℤ (coroots ι) = evenSum ι := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v (⟨i, rfl | rfl⟩ | ⟨i, j, _, rfl | rfl | rfl⟩)
    all_goals
      change Even (∑ a, _)
      simp [Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Finset.sum_neg_distrib,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  · intro v hv
    let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    let L := Submodule.span ℤ (coroots ι)
    have hdiff (i : ι) : coordinateVector ι i - coordinateVector ι i₀ ∈ L := by
      by_cases h : i = i₀
      · simp [h, L]
      · exact Submodule.subset_span (Or.inr ⟨i, i₀, h, Or.inl rfl⟩)
    have hdouble : (2 : ℤ) • coordinateVector ι i₀ ∈ L :=
      Submodule.subset_span (Or.inl ⟨i₀, Or.inl rfl⟩)
    obtain ⟨m, hm⟩ : Even (∑ i, v i) := hv
    have hsum : (∑ i, v i • coordinateVector ι i) = v := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_ite]
    have hdecomp : (∑ i, v i • (coordinateVector ι i - coordinateVector ι i₀)) + m • ((2 : ℤ) • coordinateVector ι i₀) = v := by
      have hm' : m • ((2 : ℤ) • coordinateVector ι i₀) = (m + m) • coordinateVector ι i₀ := by
        rw [two_smul, smul_add, add_smul]
      rw [Finset.sum_congr rfl (fun i _ => smul_sub (v i) (coordinateVector ι i) (coordinateVector ι i₀)),
        Finset.sum_sub_distrib, hsum, ← Finset.sum_smul, hm, hm', sub_add_cancel]
    rw [← hdecomp]
    exact L.add_mem (L.sum_mem fun i _ => L.smul_mem _ (hdiff i)) (L.smul_mem _ hdouble)


theorem corootLattice : CorootLattice.{u} := by
  intro ι _ _ _
  refine ⟨span_coroots ι, fun v => ?_⟩
  change (∃ a : ℤ, 2 * a + ∑ i, v i = 0) ↔ Even (∑ i, v i)
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨-a, by omega⟩
  · rintro ⟨a, ha⟩
    exact ⟨-a, by omega⟩

end

end LinearAlgebraicGroups.Arithmetic.OddSpinModels

namespace LinearAlgebraicGroups.Arithmetic.OddSpinModels

open Specs.SymplecticMatrixStructure (Indices PointGroup Coordinates universalSymplecticMatrix
  mapSymplecticPoint)
open Specs.Arithmetic.OddSpinCharTwoStabilizer (OddIndex OddModule MarkedIsometries oddMatrixAction
  radicalVector)
open Albert.SpinSpecification (GroupScheme SchemePoints)
open Opposite
open scoped CategoryTheory.MonObj
open private OddSpinCharTwoStabilizer.oddForm_apply
  oddMatrixAction_entry markedMap markedPointEquiv markedPointEquiv_natural
  OddIsometryRing markedScheme markedSchemePoints markedSchemePoints_natural markedSchemePoints_onSpec
  markedRing_smooth markedScheme_affine markedScheme_finitePresentation smooth_source_reductive
  groupHom_of_affine_point_law
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
open private Representation Representation.equiv Representation.convolutionIso
  spectrumPointsIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private symplecticRepresentation evaluatePoint evaluateCoordinates evaluateCoordinates_entry
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure

noncomputable section

section MarkedPairs

variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

private theorem splitCoordinates_norm (x : OddModule R n) :
    Specs.Arithmetic.OddSpinCharTwoStabilizer.oddForm R n x =
      oddForm (PlaneIndex.{u} n) R (splitCoordinates R n x) := by
  rw [LinearAlgebraicGroups.Arithmetic.OddSpinModels.oddForm_apply, hyperbolicForm_apply,
    OddSpinCharTwoStabilizer.oddForm_apply]

  rw [← (Equiv.ulift : PlaneIndex.{u} n ≃ Fin n).sum_comp]
  rfl

private theorem splitCoordinates_marked :
    splitCoordinates R n (radicalVector R n) = (0, 1) := by
  apply Prod.ext
  · funext j
    change (Pi.single (⊤ : OddIndex n) 1 : OddModule R n)
      (↑(toLex (hyperbolicIndices n j)) : OddIndex n) = 0
    simp
  · change (Pi.single (⊤ : OddIndex n) 1 : OddModule R n) ⊤ = 1
    simp

private def pairActionInCoordinates (g : MarkedIsometries R n) :
    ((Indices (PlaneIndex.{u} n) → R) × R) ≃ₗ[R] ((Indices (PlaneIndex.{u} n) → R) × R) :=
  (splitCoordinates R n).symm.trans ((oddMatrixAction g.val).trans (splitCoordinates R n))

private theorem coordinates_fixes (g : MarkedIsometries R n) :
    pairActionInCoordinates g (0, 1) = (0, 1) := by
  have hr : oddMatrixAction g.val (radicalVector R n) = radicalVector R n := g.property.2
  change splitCoordinates R n (oddMatrixAction g.val ((splitCoordinates R n).symm (0, 1))) = _
  rw [← splitCoordinates_marked (R := R) (n := n), LinearEquiv.symm_apply_apply, hr]

private theorem coordinates_preserves (g : MarkedIsometries R n)
    (x : (Indices (PlaneIndex.{u} n) → R) × R) :
    oddForm (PlaneIndex.{u} n) R (pairActionInCoordinates g x) = oddForm (PlaneIndex.{u} n) R x := by
  change oddForm (PlaneIndex.{u} n) R
    (splitCoordinates R n (oddMatrixAction g.val ((splitCoordinates R n).symm x))) = _
  rw [← splitCoordinates_norm, g.property.1, splitCoordinates_norm, LinearEquiv.apply_symm_apply]

private abbrev PairData (R : Type u) [CommRing R] (n : ℕ) :=
  {p : PointGroup (PlaneIndex.{u} n) R × ((Indices (PlaneIndex.{u} n) → R) →ₗ[R] R) // IsOddPair p.1 p.2}

private def markedPair (h₂ : (2 : R) = 0) (g : MarkedIsometries R n) : PairData R n :=
  let h := (fixesNormComparison (PlaneIndex.{u} n) R h₂ _ (coordinates_fixes g)).mp (coordinates_preserves g)
  ⟨(h.choose, h.choose_spec.choose), h.choose_spec.choose_spec.1⟩

private theorem markedPair_action (h₂ : (2 : R) = 0) (g : MarkedIsometries R n)
    (x : Indices (PlaneIndex.{u} n) → R) (t : R) :
    pairActionInCoordinates g (x, t) = ((markedPair h₂ g).val.1.val *ᵥ x,
      (markedPair h₂ g).val.2 x + t) :=
  ((fixesNormComparison (PlaneIndex.{u} n) R h₂ _ (coordinates_fixes g)).mp
    (coordinates_preserves g)).choose_spec.choose_spec.2 x t

private theorem pairData_ext {p q : PairData R n}
    (h : ∀ i : Indices (PlaneIndex.{u} n),
      (p.val.1.val *ᵥ standardVector R i, p.val.2 (standardVector R i)) =
        (q.val.1.val *ᵥ standardVector R i, q.val.2 (standardVector R i))) : p = q := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    simpa only [standardVector, Matrix.mulVec_single_one, Matrix.col_apply] using
      congrFun (congrArg Prod.fst (h j)) i
  · apply (Pi.basisFun R (Indices (PlaneIndex.{u} n))).ext
    intro i
    simpa only [Pi.basisFun_apply] using congrArg Prod.snd (h i)

private theorem markedPair_injective (h₂ : (2 : R) = 0) :
    Function.Injective (markedPair (n := n) h₂) := by
  intro g h he
  apply Subtype.ext
  apply oddMatrixAction.injective
  apply LinearEquiv.ext
  intro z
  obtain ⟨⟨x, t⟩, rfl⟩ := (splitCoordinates R n).symm.surjective z
  apply (splitCoordinates R n).injective
  change pairActionInCoordinates g (x, t) = pairActionInCoordinates h (x, t)
  rw [markedPair_action h₂ g, markedPair_action h₂ h, he]

private theorem markedPair_surjective (h₂ : (2 : R) = 0) :
    Function.Surjective (markedPair (n := n) h₂) := by
  intro p
  obtain ⟨a, ⟨ha, hr, hq⟩, _⟩ := pairAction (PlaneIndex.{u} n) R h₂ _ _ p.property
  let b := (splitCoordinates R n).trans (a.trans (splitCoordinates R n).symm)
  let g := oddMatrixAction.symm b
  have hg : oddMatrixAction g = b := oddMatrixAction.apply_symm_apply _
  have gm : g ∈ MarkedIsometries R n := by
    change (∀ x, Specs.Arithmetic.OddSpinCharTwoStabilizer.oddForm R n (oddMatrixAction g x) =
      Specs.Arithmetic.OddSpinCharTwoStabilizer.oddForm R n x) ∧
        oddMatrixAction g (radicalVector R n) = radicalVector R n
    rw [hg]
    constructor
    · intro x
      rw [splitCoordinates_norm, splitCoordinates_norm]
      change oddForm (PlaneIndex.{u} n) R (splitCoordinates R n ((splitCoordinates R n).symm
        (a (splitCoordinates R n x)))) = _
      rw [LinearEquiv.apply_symm_apply, hq]
    · change (splitCoordinates R n).symm (a (splitCoordinates R n (radicalVector R n))) = _
      rw [splitCoordinates_marked, hr, ← splitCoordinates_marked, LinearEquiv.symm_apply_apply]
  refine ⟨⟨g, gm⟩, pairData_ext fun i => ?_⟩
  have h := markedPair_action h₂ (⟨g, gm⟩ : MarkedIsometries R n) (standardVector R i) 0
  change splitCoordinates R n (oddMatrixAction g ((splitCoordinates R n).symm
    (standardVector R i, 0))) = _ at h
  rw [hg] at h
  have hb (x : (Indices (PlaneIndex.{u} n) → R) × R) :
      splitCoordinates R n (b ((splitCoordinates R n).symm x)) = a x := by
    simp [b]
  rw [hb, ha] at h
  simpa only [add_zero] using h.symm

private def markedPairEquiv (h₂ : (2 : R) = 0) : MarkedIsometries R n ≃ PairData R n :=
  Equiv.ofBijective _ ⟨markedPair_injective h₂, markedPair_surjective h₂⟩

private abbrev hyperbolicIndex (i : Indices (PlaneIndex.{u} n)) : OddIndex n := ↑(toLex (hyperbolicIndices n i))

private theorem splitCoordinates_symm_standardVector (j : Indices (PlaneIndex.{u} n)) :
    (splitCoordinates R n).symm (standardVector R j, 0) =
      Specs.Arithmetic.OddSpinCharTwoStabilizer.oddBasis R n ⟨hyperbolicIndex j⟩ := by
  funext l
  cases l using WithTop.recTopCoe <;>
    simp [splitCoordinates, Specs.Arithmetic.OddSpinCharTwoStabilizer.oddBasis,
      Pi.basisFun_apply, Pi.single_apply, hyperbolicIndex, Equiv.symm_apply_eq]
  rfl

private theorem symplectic_entry (h₂ : (2 : R) = 0) (g : MarkedIsometries R n)
    (i j : Indices (PlaneIndex.{u} n)) :
    (markedPair h₂ g).val.1.val i j = g.val.val ⟨hyperbolicIndex i⟩ ⟨hyperbolicIndex j⟩ := by
  have h := congrFun (congrArg Prod.fst (markedPair_action h₂ g (standardVector R j) 0)) i
  change oddMatrixAction g.val ((splitCoordinates R n).symm
    (standardVector R j, 0)) (hyperbolicIndex i) = _ at h
  rw [splitCoordinates_symm_standardVector, oddMatrixAction_entry] at h
  simpa only [standardVector, Matrix.mulVec_single_one, Matrix.col_apply] using h.symm

private theorem covector_entry (h₂ : (2 : R) = 0) (g : MarkedIsometries R n)
    (j : Indices (PlaneIndex.{u} n)) :
    (markedPair h₂ g).val.2 (standardVector R j) = g.val.val ⟨⊤⟩ ⟨hyperbolicIndex j⟩ := by
  have h := congrArg Prod.snd (markedPair_action h₂ g (standardVector R j) 0)
  change oddMatrixAction g.val ((splitCoordinates R n).symm
    (standardVector R j, 0)) ⊤ = _ at h
  rw [splitCoordinates_symm_standardVector, oddMatrixAction_entry, add_zero] at h
  exact h.symm

private def markedProjection (h₂ : (2 : R) = 0) :
    MarkedIsometries R n →* PointGroup (PlaneIndex.{u} n) R where
  toFun g := (markedPair h₂ g).val.1
  map_one' := by
    apply Subtype.ext
    ext i j
    change (markedPair h₂ (1 : MarkedIsometries R n)).val.1.val i j = _
    rw [symplectic_entry]
    change (1 : Matrix _ _ R) _ _ = (1 : Matrix _ _ R) _ _
    have he : (⟨hyperbolicIndex i⟩ : ULift.{u} (OddIndex n)) =
        ⟨hyperbolicIndex j⟩ ↔ i = j := by
      constructor
      · intro h
        exact (hyperbolicIndices n).injective
          (congrArg ofLex (WithTop.coe_eq_coe.mp (congrArg ULift.down h)))
      · rintro rfl
        rfl
    simp only [Matrix.one_apply, he]
  map_mul' g h := by
    apply Subtype.ext
    have hcomp (x : (Indices (PlaneIndex.{u} n) → R) × R) :
        pairActionInCoordinates (g * h) x =
          pairActionInCoordinates g (pairActionInCoordinates h x) := by
      change splitCoordinates R n (oddMatrixAction (g.val * h.val)
        ((splitCoordinates R n).symm x)) =
          splitCoordinates R n (oddMatrixAction g.val
            ((splitCoordinates R n).symm (splitCoordinates R n
              (oddMatrixAction h.val ((splitCoordinates R n).symm x)))))
      rw [LinearEquiv.symm_apply_apply, map_mul, LinearEquiv.mul_apply]
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    have hx := congrArg Prod.fst (hcomp (x, 0))
    rw [markedPair_action h₂ (g * h), markedPair_action h₂ h, markedPair_action h₂ g] at hx
    simp only [Matrix.mulVec_mulVec] at hx
    exact hx

private theorem markedProjection_natural (h₂ : (2 : R) = 0) (h₂' : (2 : S) = 0)
    (f : R →+* S) (g : MarkedIsometries R n) :
    markedProjection h₂' (markedMap n f g) = mapSymplecticPoint f (markedProjection h₂ g) := by
  apply Subtype.ext
  ext i j
  change (markedPair h₂' (markedMap n f g)).val.1.val i j =
    f ((markedPair h₂ g).val.1.val i j)
  rw [symplectic_entry, symplectic_entry]
  rfl

private theorem markedCovector_natural (h₂ : (2 : R) = 0) (h₂' : (2 : S) = 0)
    (f : R →+* S) (g : MarkedIsometries R n) (j : Indices (PlaneIndex.{u} n)) :
    (markedPair h₂' (markedMap n f g)).val.2 (standardVector S j) =
      f ((markedPair h₂ g).val.2 (standardVector R j)) := by
  rw [covector_entry, covector_entry]
  rfl

end MarkedPairs

section PairScheme

variable {k : Type u} [Field k] (n : ℕ)

private abbrev SymplecticRing := Coordinates k (PlaneIndex.{u} n)
private abbrev MarkedRing := OddIsometryRing k n

private theorem two_eq_zero_of_algebra {R : Type u} [CommRing R] [Algebra k R]
    (h₂ : (2 : k) = 0) : (2 : R) = 0 := by
  simpa only [map_ofNat, map_zero] using congrArg (algebraMap k R) h₂

private def universalMarked : MarkedIsometries (MarkedRing (k := k) n) n :=
  markedPointEquiv k n _ (.id k _)

private theorem markedPointEquiv_generic {R : Type u} [CommRing R] [Algebra k R]
    (f : MarkedRing (k := k) n →ₐ[k] R) :
    markedPointEquiv k n R f = markedMap n f.toRingHom (universalMarked n) := by
  simpa only [AlgHom.comp_id, universalMarked] using markedPointEquiv_natural k n f (.id k _)

private def pairRingMap (h₂ : (2 : k) = 0) :
    SymplecticRing (k := k) n →ₐ[k] MarkedRing (k := k) n :=
  evaluateCoordinates (markedProjection (two_eq_zero_of_algebra h₂) (universalMarked n))

private def pairRoot (h₂ : (2 : k) = 0) (j : Indices (PlaneIndex.{u} n)) :
    MarkedRing (k := k) n :=
  (markedPair (two_eq_zero_of_algebra h₂) (universalMarked n)).val.2 (standardVector _ j)

private theorem evaluatePoint_pairRingMap {R : Type u} [CommRing R] [Algebra k R]
    (h₂ : (2 : k) = 0) (f : MarkedRing (k := k) n →ₐ[k] R) :
    evaluatePoint (f.comp (pairRingMap n h₂)) =
      markedProjection (two_eq_zero_of_algebra h₂) (markedPointEquiv k n R f) := by
  rw [markedPointEquiv_generic, markedProjection_natural]
  apply Subtype.ext
  ext i j
  change f (pairRingMap n h₂ (universalSymplecticMatrix k (PlaneIndex.{u} n) i j)) =
    f ((markedProjection (two_eq_zero_of_algebra h₂) (universalMarked n)).val i j)
  rw [pairRingMap, evaluateCoordinates_entry]

private theorem eval_pairRoot {R : Type u} [CommRing R] [Algebra k R]
    (h₂ : (2 : k) = 0) (f : MarkedRing (k := k) n →ₐ[k] R) (j : Indices (PlaneIndex.{u} n)) :
    f (pairRoot n h₂ j) =
      (markedPair (two_eq_zero_of_algebra h₂) (markedPointEquiv k n R f)).val.2 (standardVector R j) := by
  rw [markedPointEquiv_generic, markedCovector_natural]
  rfl

private abbrev SpGroup := SymplecticMatrixStructure.symplecticGroup k (PlaneIndex.{u} n)

private def symplecticSchemePoints (S : CommAlgCat.{u} k) :
    SchemePoints (SpGroup (k := k) n).val S ≃* PointGroup (PlaneIndex.{u} n) S :=
  ((SymplecticMatrixStructure.symplecticGroupPointsIso k (PlaneIndex.{u} n)).app S).groupIsoToMulEquiv

private theorem symplecticSchemePoints_onSpec {S : CommAlgCat.{u} k}
    (p : SymplecticRing (k := k) n →ₐ[k] S) :
    symplecticSchemePoints n S ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom p).op) =
      evaluatePoint p := by
  letI := SymplecticMatrixStructure.symplecticHopf k (PlaneIndex.{u} n)
  let A := CommHopfAlgCat.of k (SymplecticRing (k := k) n)
  let e := hopfSpecPointIso A
  let c := Representation.convolutionIso
    (show Representation (SymplecticRing (k := k) n) _ from symplecticRepresentation)
  change ((e ≪≫ (e.symm ≪≫ c)).hom.app S) (WithConv.toConv p) = _
  have he : e ≪≫ (e.symm ≪≫ c) = c := by simp
  rw [he]
  rfl

private theorem symplecticSchemePoints_natural {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    (p : SchemePoints (SpGroup (k := k) n).val R) :
    symplecticSchemePoints n S ((algSpec (CommRingCat.of k)).map f.op ≫ p) =
      mapSymplecticPoint f.hom.toRingHom (symplecticSchemePoints n R p) := by
  let e := SymplecticMatrixStructure.symplecticGroupPointsIso k (PlaneIndex.{u} n)
  exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.hom.naturality f)) p

private def pairSchemeMap (h₂ : (2 : k) = 0) :
    (markedScheme k n).X ⟶ (SpGroup (k := k) n).val.X :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (pairRingMap n h₂)).op

set_option maxHeartbeats 900000 in
private theorem pairSchemeMap_points (h₂ : (2 : k) = 0) (S : CommAlgCat k)
    (x : SchemePoints (markedScheme k n) S) :
    symplecticSchemePoints n S (x ≫ pairSchemeMap n h₂) =
      markedProjection (two_eq_zero_of_algebra h₂) (markedSchemePoints k n S x) := by
  let F := algSpec (CommRingCat.of k)
  let d := (CommAlgCat.ofHom (pairRingMap n h₂)).op
  let a : op S ⟶ op (CommAlgCat.of k (MarkedRing (k := k) n)) :=
    algSpec.fullyFaithful.preimage x
  have ha : F.map a = x := algSpec.fullyFaithful.map_preimage _
  calc
    _ = symplecticSchemePoints n S (F.map (a ≫ d)) := by
      exact congrArg (symplecticSchemePoints n S)
        ((congrArg (fun y => y ≫ F.map d) ha.symm).trans (F.map_comp a d).symm)
    _ = evaluatePoint (a.unop.hom.comp (pairRingMap n h₂)) :=
      symplecticSchemePoints_onSpec n _
    _ = markedProjection (two_eq_zero_of_algebra h₂) (markedPointEquiv k n S a.unop.hom) :=
      evaluatePoint_pairRingMap n h₂ _
    _ = _ := congrArg _ ((markedSchemePoints_onSpec k n a).symm.trans
      (congrArg (markedSchemePoints k n S) ha))

set_option maxHeartbeats 900000 in
private theorem existsPairProjection (h₂ : (2 : k) = 0) :
    ∃ p : markedScheme k n ⟶ (SpGroup (k := k) n).val,
      p.hom.hom = pairSchemeMap n h₂ := by
  let φ (S : CommAlgCat k) :=
    (symplecticSchemePoints n S).symm.toMonoidHom.comp
      ((markedProjection (n := n) (two_eq_zero_of_algebra h₂)).comp (markedSchemePoints k n S).toMonoidHom)
  have : IsAffine (markedScheme k n).X.left := markedScheme_affine k n
  apply groupHom_of_affine_point_law (pairSchemeMap n h₂) φ
  intro S x
  apply (symplecticSchemePoints n S).injective
  rw [pairSchemeMap_points]
  exact ((symplecticSchemePoints n S).apply_symm_apply _).symm

private abbrev pairAlgebra (h₂ : (2 : k) = 0) :
    Algebra (SymplecticRing (k := k) n) (MarkedRing (k := k) n) :=
  (pairRingMap n h₂).toRingHom.toAlgebra

set_option maxHeartbeats 1000000 in
private theorem markedRing_presents (h₂ : (2 : k) = 0) :
    letI := pairAlgebra n h₂
    PresentsSquareRoots (universalCoefficient k (PlaneIndex.{u} n)) (pairRoot n h₂) := by
  let A := SymplecticRing (k := k) n
  let D := MarkedRing (k := k) n
  letI : Algebra A D := pairAlgebra n h₂
  have hmap : algebraMap A D = (pairRingMap n h₂).toRingHom := rfl
  refine ⟨fun j => ?_, ?_⟩
  · rw [hmap]
    have he : evaluatePoint (pairRingMap n h₂) =
        markedProjection (two_eq_zero_of_algebra (R := D) h₂) (universalMarked n) := by
      have h := evaluatePoint_pairRingMap n h₂ (AlgHom.id k (MarkedRing (k := k) n))
      rw [AlgHom.id_comp] at h
      exact h
    change pairRoot n h₂ j ^ 2 = pairRingMap n h₂ (universalCoefficient k (PlaneIndex.{u} n) j)
    rw [map_universalCoefficient, ← show (evaluatePoint (pairRingMap n h₂)).val =
      (pairRingMap n h₂).mapMatrix _ from rfl, he]
    exact (pairEquations _ D (two_eq_zero_of_algebra h₂) _ _).mp
      (markedPair _ (universalMarked n)).property j
  · intro R _ f l hl
    letI : Algebra k R := (f.comp (algebraMap k A)).toAlgebra
    let a : A →ₐ[k] R := ⟨f, fun _ => rfl⟩
    let b := Pi.basisFun R (Indices (PlaneIndex.{u} n))
    let ℓ := b.constr R l
    have hℓ j : ℓ (standardVector R j) = l j := by
      simpa only [b, Pi.basisFun_apply] using b.constr_basis R l j
    have hchar : (2 : R) = 0 := two_eq_zero_of_algebra h₂
    have hpair : IsOddPair (evaluatePoint a) ℓ := by
      apply (pairEquations _ R hchar _ _).mpr
      intro j
      rw [hℓ]
      exact (hl j).trans (map_universalCoefficient a j)
    let q : PairData R n := ⟨(evaluatePoint a, ℓ), hpair⟩
    let e := markedPairEquiv (n := n) hchar
    let g := (markedPointEquiv k n R).symm (e.symm q)
    have hg : markedPair hchar (markedPointEquiv k n R g) = q := by
      change e (markedPointEquiv k n R g) = q
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    let ev := Representation.equiv (show Representation A _ from symplecticRepresentation)
      (CommAlgCat.of k R)
    have hge : g.comp (pairRingMap n h₂) = a := by
      apply ev.injective
      change evaluatePoint (g.comp (pairRingMap n h₂)) = evaluatePoint a
      rw [evaluatePoint_pairRingMap]
      exact congrArg (fun p : PairData R n => p.val.1) hg
    refine ⟨g.toRingHom, ⟨?_, ?_⟩, ?_⟩
    · rw [hmap]
      exact congrArg AlgHom.toRingHom hge
    · intro j
      change g (pairRoot n h₂ j) = l j
      rw [eval_pairRoot]
      change (markedPair hchar (markedPointEquiv k n R g)).val.2 (standardVector R j) = l j
      rw [hg]
      exact hℓ j
    · rintro g' ⟨hgf, hgl⟩
      have hgf' : g'.comp (pairRingMap n h₂).toRingHom = f := hgf
      let d : D →ₐ[k] R :=
        ⟨g', fun c => by
          change g' (algebraMap k D c) = f (algebraMap k A c)
          rw [← (pairRingMap n h₂).commutes c]
          exact DFunLike.congr_fun hgf' (algebraMap k A c)⟩
      have hd : d.comp (pairRingMap n h₂) = a :=
        AlgHom.ext fun x => DFunLike.congr_fun hgf' x
      have hq : markedPair hchar (markedPointEquiv k n R d) = q := by
        apply pairData_ext
        intro j
        have hA : markedProjection hchar (markedPointEquiv k n R d) = evaluatePoint a := by
          rw [← evaluatePoint_pairRingMap n h₂, hd]
        have hL := (eval_pairRoot n h₂ d j).symm.trans (hgl j)
        exact Prod.ext (congrArg (fun p : PointGroup (PlaneIndex.{u} n) R =>
          p.val *ᵥ standardVector R j) hA) (hL.trans (hℓ j).symm)
      have hdg : d = g :=
        (markedPointEquiv k n R).injective (e.injective (hq.trans hg.symm))
      exact congrArg AlgHom.toRingHom hdg

private theorem squareRootPresentation_iso {A B D : Type u} [CommRing A] [CommRing B]
    [CommRing D] [Algebra A B] [Algebra A D] {I : Type u} {c : I → A} {z : I → B} {w : I → D}
    (hz : PresentsSquareRoots c z) (hw : PresentsSquareRoots c w) :
    Nonempty (B ≃ₐ[A] D) := by
  obtain ⟨f, ⟨hf, hfz⟩, hfuniq⟩ := hz.2 D (algebraMap A D) w hw.1
  obtain ⟨g, ⟨hg, hgw⟩, hguniq⟩ := hw.2 B (algebraMap A B) z hz.1
  have hfg : f.comp g = RingHom.id D := by
    obtain ⟨t, _, hu⟩ := hw.2 D (algebraMap A D) w hw.1
    exact (hu _ ⟨by rw [RingHom.comp_assoc, hg, hf],
      fun j => by rw [RingHom.comp_apply, hgw, hfz]⟩).trans
        (hu _ ⟨rfl, fun _ => rfl⟩).symm
  have hgf : g.comp f = RingHom.id B := by
    obtain ⟨t, _, hu⟩ := hz.2 B (algebraMap A B) z hz.1
    exact (hu _ ⟨by rw [RingHom.comp_assoc, hf, hg],
      fun j => by rw [RingHom.comp_apply, hfz, hgw]⟩).trans
        (hu _ ⟨rfl, fun _ => rfl⟩).symm
  let e := RingEquiv.ofRingHom f g hfg hgf
  exact ⟨AlgEquiv.ofRingEquiv (f := e) (DFunLike.congr_fun hf)⟩

private def pairProjection (h₂ : (2 : k) = 0) : markedScheme k n ⟶ (SpGroup (k := k) n).val :=
  (existsPairProjection n h₂).choose

private theorem pairProjection_onSpec (h₂ : (2 : k) = 0) :
    (pairProjection n h₂).hom.hom.left = Spec.map (CommRingCat.ofHom (pairRingMap n h₂).toRingHom) :=
  congrArg Over.Hom.left (existsPairProjection n h₂).choose_spec

private theorem pairProjection_points (h₂ : (2 : k) = 0) (S : CommAlgCat k)
    (x : SchemePoints (markedScheme k n) S) :
    symplecticSchemePoints n S (x ≫ (pairProjection n h₂).hom.hom) =
      markedProjection (two_eq_zero_of_algebra h₂) (markedSchemePoints k n S x) :=
  (congrArg (fun a => symplecticSchemePoints n S (x ≫ a))
    (existsPairProjection n h₂).choose_spec).trans (pairSchemeMap_points n h₂ S x)

private theorem pairProjection_represents (h₂ : (2 : k) = 0) :
    RepresentsPairProjection (pairProjection n h₂) (markedSchemePoints k n) (symplecticSchemePoints n) := by
  refine ⟨fun f p => congrArg Subtype.val (markedSchemePoints_natural k n f p),
    fun f p => symplecticSchemePoints_natural n f p, ?_, ?_⟩
  · intro R a
    rw [pairProjection_points]
    let g := markedSchemePoints k n R a
    let hR : (2 : R) = 0 := two_eq_zero_of_algebra h₂
    let l := (markedPair hR g).val.2
    refine ⟨l, ⟨(markedPair hR g).property, markedPair_action hR g⟩, ?_⟩
    rintro l' ⟨_, hp⟩
    apply LinearMap.ext
    intro x
    exact (by simpa only [add_zero] using
      (congrArg Prod.snd (hp x 0)).symm.trans (congrArg Prod.snd (markedPair_action hR g x 0)))
  · intro R A l hl
    let hR : (2 : R) = 0 := two_eq_zero_of_algebra h₂
    let e := markedPairEquiv (n := n) hR
    let q : PairData R n := ⟨(A, l), hl⟩
    let a := (markedSchemePoints k n R).symm (e.symm q)
    have ha : markedPair hR (markedSchemePoints k n R a) = q := by
      change e (markedSchemePoints k n R a) = q
      rw [MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine ⟨a, ⟨?_, ?_⟩, ?_⟩
    · rw [pairProjection_points]
      exact congrArg (fun v : PairData R n => v.val.1) ha
    · intro x t
      have h := markedPair_action hR (markedSchemePoints k n R a) x t
      rw [ha] at h
      exact h
    · rintro a' ⟨hA, hx⟩
      apply (markedSchemePoints k n R).injective
      apply e.injective
      change markedPair hR (markedSchemePoints k n R a') = markedPair hR (markedSchemePoints k n R a)
      rw [ha]
      apply pairData_ext
      intro j
      have hh := (markedPair_action hR (markedSchemePoints k n R a') (standardVector R j) 0).symm
      exact (by simpa only [add_zero] using hh.trans (hx (standardVector R j) 0))

private def pairAlgebraicGroup (k : Type u) [Field k] : Specs.AffineAlgebraicGroup k :=
  ⟨markedScheme k n, markedScheme_affine k n,
    (letI := markedScheme_finitePresentation k n; inferInstance),
    (by change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (MarkedRing (k := k) n))))
        infer_instance)⟩

set_option maxHeartbeats 500000 in
private theorem pairCoordinateProperties (h₂ : (2 : k) = 0) :
    letI := pairAlgebra n h₂
    Module.Free (SymplecticRing (k := k) n) (MarkedRing (k := k) n) ∧
    Module.Finite (SymplecticRing (k := k) n) (MarkedRing (k := k) n) ∧
    Module.FaithfullyFlat (SymplecticRing (k := k) n) (MarkedRing (k := k) n) := by
  let A := SymplecticRing (k := k) n
  let D := MarkedRing (k := k) n
  letI : Algebra A D := pairAlgebra n h₂
  have hA : Nontrivial A := (evaluateCoordinates (k := k) (1 : PointGroup (PlaneIndex.{u} n) k)).toRingHom.domain_nontrivial
  have hD : Nontrivial D := ((markedPointEquiv k n k).symm 1).toRingHom.domain_nontrivial
  have hpres := markedRing_presents n h₂
  obtain ⟨B, _, _, z, hz, hfree, hfinite, _, _⟩ :=
    squareRootProjection A _ (universalCoefficient k (PlaneIndex.{u} n)) (two_eq_zero_of_algebra h₂)
  obtain ⟨e⟩ := squareRootPresentation_iso hz hpres
  have hfreeD : Module.Free A D := Module.Free.of_equiv e.toLinearEquiv
  have hfiniteD : Module.Finite A D := Module.Finite.equiv e.toLinearEquiv
  have hffD : Module.FaithfullyFlat A D := inferInstance
  exact ⟨hfreeD, hfiniteD, hffD⟩

set_option maxHeartbeats 500000 in
private theorem pairGeometry (h₂ : (2 : k) = 0) :
    let p := pairProjection n h₂
    IsFinite p.hom.hom.left ∧ Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      UniversallyInjective p.hom.hom.left ∧ Smooth (markedScheme k n).X.hom ∧
      GeometricallyConnected (markedScheme k n).X.hom ∧
      (0 < n → Specs.GeometricRadicals.IsReductive (pairAlgebraicGroup n k)) := by
  let A := SymplecticRing (k := k) n
  let D := MarkedRing (k := k) n
  letI : Algebra A D := pairAlgebra n h₂
  have hpres := markedRing_presents n h₂
  have ⟨_, hfiniteD, hffD⟩ := pairCoordinateProperties n h₂
  let p := pairProjection n h₂
  let f := CommRingCat.ofHom (algebraMap A D)
  have hp : p.hom.hom.left = Spec.map f := by
    rw [pairProjection_onSpec]
  have hfin : IsFinite p.hom.hom.left := by
    rw [hp]
    exact (IsFinite.SpecMap_iff f).mpr (RingHom.finite_algebraMap.mpr hfiniteD)
  have hfs : Flat p.hom.hom.left ∧ Surjective p.hom.hom.left := by
    exact hp.symm ▸ (flat_and_surjective_SpecMap_iff f).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hffD)
  have hrad : UniversallyInjective p.hom.hom.left := by
    rw [hp]
    exact squareRootRadicial hpres (two_eq_zero_of_algebra h₂)
  have hsm : Smooth (markedScheme k n).X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k D)))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (markedRing_smooth k n h₂))
  have hconn : GeometricallyConnected (markedScheme k n).X.hom := by
    letI : Surjective p.hom.hom.left := hfs.2
    haveI : GeometricallyConnected (SpGroup (k := k) n).val.X.hom :=
      SymplecticMatrixStructure.geometricConnectedness k (PlaneIndex.{u} n)
    have hc := geometricallyConnected_of_finite_radicial_surjection p.hom.hom.left
      (SpGroup (k := k) n).val.X.hom
    exact p.hom.hom.w ▸ hc
  refine ⟨hfin, hfs.1, hfs.2, hrad, hsm, hconn, ?_⟩
  intro hn
  haveI : Nonempty (PlaneIndex.{u} n) := ⟨⟨⟨0, hn⟩⟩⟩
  have hSp := SymplecticMatrixStructure.reductivity k (PlaneIndex.{u} n) (SpGroup n)
    ⟨SymplecticMatrixStructure.symplecticGroupPointsIso k (PlaneIndex.{u} n)⟩
  exact smooth_source_reductive (pairAlgebraicGroup n k) (SpGroup n) p hfs.2 hrad hsm hconn hSp

set_option maxHeartbeats 650000 in
theorem representedPairGroup : RepresentedPairGroup.{u} := by
  intro k _ n h₂
  let A := SymplecticRing (k := k) n
  let D := MarkedRing (k := k) n
  letI : Algebra A D := pairAlgebra n h₂
  have htower : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq' (pairRingMap n h₂).comp_algebraMap.symm
  let p := pairProjection n h₂
  let f := CommRingCat.ofHom (algebraMap A D)
  have hp : p.hom.hom.left = Spec.map f := pairProjection_onSpec n h₂
  obtain ⟨hfin, hflat, hsurj, hrad, hsm, hc, hred⟩ := pairGeometry n h₂
  obtain ⟨hfreeD, hfiniteD, hffD⟩ := pairCoordinateProperties n h₂
  have hdim : ringKrullDim D = (n * (2 * n + 1) : ℕ) := by
    haveI : IsFinite (Spec.map f) := hp ▸ hfin
    haveI : Surjective (Spec.map f) := hp ▸ hsurj
    haveI : UniversallyInjective (Spec.map f) := hp ▸ hrad
    have hh : IsHomeomorph (Spec.map f) :=
      isHomeomorph_iff_isQuotientMap_injective.mpr ⟨(Spec.map f).isClosedMap.isQuotientMap
        (Spec.map f).continuous (Spec.map f).surjective, (Spec.map f).injective⟩
    calc
      ringKrullDim D = topologicalKrullDim (PrimeSpectrum D) :=
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim D).symm
      _ = topologicalKrullDim (PrimeSpectrum A) := IsHomeomorph.topologicalKrullDim_eq _ hh
      _ = ringKrullDim A := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A
      _ = _ := by simpa only [Fintype.card_ulift, Fintype.card_fin] using
        SymplecticMatrixStructure.dimension k (PlaneIndex.{u} n)
  refine ⟨pairAlgebraicGroup n k, SpGroup n, p, markedSchemePoints k n, symplecticSchemePoints n,
    pairProjection_represents n h₂, rfl, hfin, hflat, hsurj, hrad, hsm, hc, hred,
    D, inferInstance, inferInstance, ‹Algebra A D›, pairRoot n h₂, htower, rfl, ?_,
    markedRing_presents n h₂, hfreeD, hfiniteD, hffD, hdim⟩
  change p.hom.hom.left = 𝟙 (Spec (CommRingCat.of D)) ≫ Spec.map f ≫ 𝟙 (Spec (CommRingCat.of A))
  simpa only [Category.id_comp, Category.comp_id] using hp

end PairScheme

section DiagonalTorus

set_option backward.isDefEq.respectTransparency false

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open Specs.GeometricRadicals (IsMaximalTorus IsSplitTorus baseChangedSubgroup)
open Specs.SymplecticMatrixStructure (hyperbolicDiagonal IsOwnSchemeCentralizer)
open Specs.StandardGroups (multiplicativePowerPoints)
open private diagonalMarked diagonalMarked_natural diagonalGL_action equal_of_radicial_composites
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private baseChangePowerPointsIso baseChange_diagonal_points diagonal_isOwnSchemeCentralizer
  torusImageCommutes
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure

variable {k : Type u} [Field k] {n : ℕ}

private def downScales {R : Type u} [CommRing R] :
    (PlaneIndex.{u} n → Rˣ) →* (Fin n → Rˣ) where
  toFun t i := t ⟨i⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem diagonalMarked_action {R : Type u} [CommRing R]
    (t : PlaneIndex.{u} n → Rˣ) (x : Indices (PlaneIndex.{u} n) → R) (a : R) :
    pairActionInCoordinates (diagonalMarked (downScales t)) (x, a) =
      (hyperbolicDiagonal t *ᵥ x, a) := by
  change splitCoordinates R n (oddMatrixAction (diagonalMarked (downScales t)).val
    ((splitCoordinates R n).symm (x, a))) = _
  rw [show oddMatrixAction (diagonalMarked (downScales t)).val
    ((splitCoordinates R n).symm (x, a)) = _ from diagonalGL_action _ _]
  apply Prod.ext
  · funext i
    change _ = (hyperbolicDiagonal t *ᵥ x) i
    rw [hyperbolicDiagonal, Matrix.mulVec_diagonal]
    rcases i with ⟨i⟩ | ⟨i⟩ <;> rfl
  · rfl

private theorem markedProjection_diagonal {R : Type u} [CommRing R] (h₂ : (2 : R) = 0)
    (t : PlaneIndex.{u} n → Rˣ) :
    (markedProjection h₂ (diagonalMarked (downScales t))).val = hyperbolicDiagonal t := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  exact congrArg Prod.fst ((markedPair_action h₂ (diagonalMarked (downScales t)) x 0).symm.trans
    (diagonalMarked_action t x 0))

private def diagonalPointMap (U : ClosedSubgroup (SpGroup (k := k) n).val)
    (d : (groupPointsFunctor k).obj U.group ≅ multiplicativePowerPoints k (PlaneIndex.{u} n)) :
    (groupPointsFunctor k).obj U.group ⟶ (groupPointsFunctor k).obj (markedScheme k n) where
  app R := GrpCat.ofHom ((markedSchemePoints k n R).symm.toMonoidHom.comp
    (diagonalMarked.comp (downScales.comp (d.hom.app R).hom)))
  naturality R S f := by
    apply GrpCat.ext
    intro a
    apply (markedSchemePoints k n S).injective
    let t (R : TestAlgebra k) (a : SchemePoints U.group R) (i : Fin n) := d.hom.app R a (⟨i⟩ : PlaneIndex.{u} n)
    change markedSchemePoints k n S ((markedSchemePoints k n S).symm (diagonalMarked (t S (mapPoints f a)))) =
      markedSchemePoints k n S (mapPoints f ((markedSchemePoints k n R).symm (diagonalMarked (t R a))))
    rw [MulEquiv.apply_symm_apply, markedSchemePoints_natural, MulEquiv.apply_symm_apply,
      ← diagonalMarked_natural]
    congr 1
    funext i
    exact congrFun (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (d.hom.naturality f)) a) ⟨i⟩

private abbrev torusAffine (U : ClosedSubgroup (SpGroup (k := k) n).val) :
    IsAffine U.group.X.left :=
  (Specs.Unipotent.closedSubgroupAlgebraicGroup U).property.1

private def diagonalLiftMorphism (U : ClosedSubgroup (SpGroup (k := k) n).val)
    (d : (groupPointsFunctor k).obj U.group ≅ multiplicativePowerPoints k (PlaneIndex.{u} n)) :
    U.group ⟶ markedScheme k n :=
  (groupHomEquiv U.group _ (torusAffine U)).symm (diagonalPointMap U d)

private theorem diagonalLiftMorphism_points (U : ClosedSubgroup (SpGroup (k := k) n).val)
    (d : (groupPointsFunctor k).obj U.group ≅ multiplicativePowerPoints k (PlaneIndex.{u} n))
    (R : TestAlgebra k) (t : SchemePoints U.group R) :
    markedSchemePoints k n R (t ≫ (diagonalLiftMorphism U d).hom.hom) =
      diagonalMarked (downScales (d.hom.app R t)) := by
  let e := groupHomEquiv U.group (markedScheme k n) (torusAffine U)
  have he := e.apply_symm_apply (diagonalPointMap U d)
  have h : t ≫ (diagonalLiftMorphism U d).hom.hom = (diagonalPointMap U d).app R t :=
    DFunLike.congr_fun (congrArg (fun τ => (τ.app R).hom) he) t
  exact (congrArg (markedSchemePoints k n R) h).trans (MulEquiv.apply_symm_apply _ _)

private abbrev SymplecticPointIso := SymplecticMatrixStructure.symplecticGroupPointsIso k (PlaneIndex.{u} n)

private theorem diagonalLiftMorphism_projection (h₂ : (2 : k) = 0)
    (U : ClosedSubgroup (SpGroup (k := k) n).val)
    (d : (groupPointsFunctor k).obj U.group ≅ multiplicativePowerPoints k (PlaneIndex.{u} n))
    (hd : ∀ (R : TestAlgebra k) (t : PlaneIndex.{u} n → Rˣ),
      (symplecticSchemePoints n R (d.inv.app R t ≫ U.inclusion.hom.hom)).val = hyperbolicDiagonal t) :
    diagonalLiftMorphism U d ≫ pairProjection n h₂ = U.inclusion := by
  apply Grp.hom_ext
  apply hom_ext_of_points (torusAffine U)
  intro R t
  apply (symplecticSchemePoints n R).injective
  change symplecticSchemePoints n R ((t ≫ (diagonalLiftMorphism U d).hom.hom) ≫
    (pairProjection n h₂).hom.hom) = symplecticSchemePoints n R (t ≫ U.inclusion.hom.hom)
  rw [pairProjection_points, diagonalLiftMorphism_points]
  apply Subtype.ext
  rw [markedProjection_diagonal]
  have h := hd R (d.hom.app R t)
  rw [Iso.hom_inv_id_app_apply] at h
  exact h.symm

private theorem torus_reduced_of_algClosed {K : Type u} [Field K] [IsAlgClosed K] {T : GroupScheme K}
    (hT : Specs.GeometricRadicals.IsTorus T) : IsReduced T.X.left := by
  obtain ⟨E, _, _, hsep, r, ⟨e⟩⟩ := hT
  letI := hsep
  let er : K ≃+* E := RingEquiv.ofBijective (algebraMap K E)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsIso (fieldSpecMap K E) :=
    (Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme).map_isIso ((RingEquiv.toCommRingCatIso er).hom.op)
  let pr : ((groupBaseChange K E).obj T).X.left ⟶ T.X.left :=
    pullback.fst T.X.hom (fieldSpecMap K E)
  haveI : IsIso pr := inferInstanceAs (IsIso (pullback.fst _ _))
  let es : ((groupBaseChange K E).obj T).X.left ≅
      (Specs.StandardGroups.multiplicativePowerGroup E (ULift.{u} (Fin r))).val.X.left :=
    (Over.forget (Spec (CommRingCat.of E))).mapIso ((Grp.forget (SchemeOver E)).mapIso e)
  let B := Specs.StandardGroups.LaurentPowerCoordinates E (ULift.{u} (Fin r))
  haveI : IsReduced (Specs.StandardGroups.multiplicativePowerGroup E (ULift.{u} (Fin r))).val.X.left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of B)))
  haveI : IsIso es.hom := Iso.isIso_hom es
  have hS : IsReduced ((groupBaseChange K E).obj T).X.left :=
    isReduced_of_isOpenImmersion es.hom
  exact isReduced_of_isOpenImmersion (inv pr)

set_option maxHeartbeats 850000 in
private theorem maximal_lift_of_radicial {K : Type u} [Field K] [IsAlgClosed K]
    {G P : AffineAlgebraicGroup K} (p : G.val ⟶ P.val)
    [UniversallyInjective p.hom.hom.left] [IsSeparated p.hom.hom.left]
    (c : (groupPointsFunctor K).obj P.val ≅ Specs.SymplecticMatrixStructure.symplecticPoints K (PlaneIndex.{u} n))
    (U : ClosedSubgroup P.val) (j : U.group ⟶ G.val) (hj : IsClosedImmersion j.hom.hom.left)
    (hproj : j ≫ p = U.inclusion)
    (hU : IsMaximalTorus U) (hc : IsOwnSchemeCentralizer U) :
    IsMaximalTorus (⟨U.group, j, hj⟩ : ClosedSubgroup G.val) := by
  refine ⟨hU.1, ?_⟩
  intro S hS hsub
  obtain ⟨i, hi⟩ := hsub
  let S' := Specs.Unipotent.closedSubgroupAlgebraicGroup S
  let q := S.inclusion ≫ p
  have hcomp : i ≫ q = U.inclusion := by
    change i ≫ S.inclusion ≫ p = U.inclusion
    rw [← Category.assoc, hi, hproj]
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr S'.property.1
  let x : SchemePoints P.val A.unop := e.hom ≫ q.hom.hom
  have ht : ∀ (R : TestAlgebra K) (f : A.unop ⟶ R) (t : SchemePoints U.group R),
      Commute (mapPoints f x) (t ≫ U.inclusion.hom.hom) := by
    intro R f t
    let a : Points S.group.X R := (testSpec K).map f.op ≫ e.hom
    let b : Points S.group.X R := t ≫ i.hom.hom
    have h := torusImageCommutes c q hS R a b
    let φ := ((c.app R).groupIsoToMulEquiv)
    have h' : Commute (a ≫ q.hom.hom) (b ≫ q.hom.hom) := by
      apply φ.injective
      exact ((φ.map_mul _ _).trans h.eq).trans (φ.map_mul _ _).symm
    change Commute (((testSpec K).map f.op ≫ e.hom) ≫ q.hom.hom)
      ((t ≫ i.hom.hom) ≫ q.hom.hom) at h'
    simp only [Category.assoc] at h'
    have hi' : i.hom.hom ≫ q.hom.hom = U.inclusion.hom.hom :=
      congrArg (fun r : U.group ⟶ P.val => r.hom.hom) hcomp
    rwa [hi'] at h'
  obtain ⟨a, ha⟩ := (hc A.unop x).mp ht
  change a ≫ U.inclusion.hom.hom = x at ha
  let b : S.group.X ⟶ U.group.X := e.inv ≫ a
  have hb : b ≫ U.inclusion.hom.hom = q.hom.hom := by
    change (e.inv ≫ a) ≫ U.inclusion.hom.hom = q.hom.hom
    rw [Category.assoc, ha]
    exact e.inv_hom_id_assoc _
  have hred : IsReduced S.group.X.left := torus_reduced_of_algClosed hS
  have hb' : (b ≫ j.hom.hom) ≫ p.hom.hom = S.inclusion.hom.hom ≫ p.hom.hom := by
    rw [Category.assoc]
    change b ≫ (j ≫ p).hom.hom = q.hom.hom
    rw [hproj, hb]
  have heq : b ≫ j.hom.hom = S.inclusion.hom.hom := by
    apply Over.OverMorphism.ext
    exact equal_of_radicial_composites p.hom.hom.left _ _ (congrArg Over.Hom.left hb')
  haveI : Mono j.hom.hom := by
    letI := hj
    exact Over.mono_of_mono_left _
  refine ⟨Grp.homMk'' b ?_ ?_, ?_⟩
  · apply (cancel_mono j.hom.hom).mp
    simp only [Category.assoc, heq, IsMonHom.one_hom]
  · apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, heq, Category.assoc, IsMonHom.mul_hom j.hom.hom,
      CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc, heq]
    exact IsMonHom.mul_hom S.inclusion.hom.hom
  · exact Grp.hom_ext _ _ heq

set_option maxHeartbeats 1200000 in
theorem pairDiagonalTorus : PairDiagonalTorus.{u} := by
  intro k _ n h₂
  let O := pairAlgebraicGroup n k
  let P := SpGroup (k := k) n
  let p := pairProjection n h₂
  let c := SymplecticPointIso (k := k) (n := n)
  have hrad : UniversallyInjective p.hom.hom.left := by
    letI := pairAlgebra n h₂
    have h := squareRootRadicial (markedRing_presents n h₂) (two_eq_zero_of_algebra h₂)
    exact (pairProjection_onSpec n h₂).symm ▸ h
  have hsep : IsSeparated p.hom.hom.left := by
    have : IsAffine O.val.X.left := O.property.1
    have : IsAffine P.val.X.left := P.property.1
    exact inferInstanceAs (IsSeparated (show O.val.X.left ⟶ P.val.X.left from p.hom.hom.left))
  obtain ⟨U, d, hrank, hd, hc, hUcl, hUmax⟩ := SymplecticMatrixStructure.diagonalTorus
    k (PlaneIndex.{u} n) P c
  let j := diagonalLiftMorphism U d
  have hj : j ≫ p = U.inclusion := diagonalLiftMorphism_projection h₂ U d hd
  have hjcl : IsClosedImmersion j.hom.hom.left := by
    have h := congrArg (fun f : U.group ⟶ P.val => f.hom.hom.left) hj
    change j.hom.hom.left ≫ p.hom.hom.left = U.inclusion.hom.hom.left at h
    have : IsClosedImmersion (j.hom.hom.left ≫ p.hom.hom.left) := h.symm ▸ U.isClosedImmersion
    exact IsClosedImmersion.of_comp j.hom.hom.left p.hom.hom.left
  let T : ClosedSubgroup O.val := ⟨U.group, j, hjcl⟩
  have hTmax : Specs.RankOneFlag.IsGeometricallyMaximal T := by
    let K := AlgebraicClosure k
    let F := groupBaseChange k K
    let P' := Specs.Unipotent.baseChangedAlgebraicGroup K P
    let O' := Specs.Unipotent.baseChangedAlgebraicGroup K O
    let p' : O'.val ⟶ P'.val := F.map p
    let U' := baseChangedSubgroup K U hUcl
    have hTcl : IsClosedImmersion (F.map T.inclusion).hom.hom.left :=
      MorphismProperty.overPullbackMap (P := @IsClosedImmersion) (fieldSpecMap k K) T.inclusion.hom.hom T.isClosedImmersion
    refine ⟨hTcl, ?_⟩
    let j' : U'.group ⟶ O'.val := F.map j
    have hj' : j' ≫ p' = U'.inclusion := (F.map_comp j p).symm.trans (congrArg F.map hj)
    have hp' := (baseChangeMapPullback (K := K) p.hom.hom).flip
    have : UniversallyInjective p'.hom.hom.left := MorphismProperty.of_isPullback hp' hrad
    have : IsSeparated p'.hom.hom.left := MorphismProperty.of_isPullback hp' hsep
    let c' := SymplecticMatrixStructure.baseChangeSymplecticPointsIso K c
    let d' := baseChangePowerPointsIso (K := K) d
    have hc' : IsOwnSchemeCentralizer U' :=
      diagonal_isOwnSchemeCentralizer c' U' d' (baseChange_diagonal_points c U d hd)
    exact maximal_lift_of_radicial p' c' U' j' hTcl hj' hUmax hc'
  refine ⟨O, P, p, markedSchemePoints k n, symplecticSchemePoints n, pairProjection_represents n h₂,
    rfl, T, U, Iso.refl _, d, ?_, ?_, hTmax, ?_⟩
  · change j ≫ p = 𝟙 _ ≫ U.inclusion
    rw [Category.id_comp, hj]
  · have hcard : Fintype.card (PlaneIndex.{u} n) = n := by simp [PlaneIndex]
    change Nonempty (U.group ≅ (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin n))).val)
    rw [hcard] at hrank
    exact hrank
  · intro R a x t
    change pairActionInCoordinates (markedSchemePoints k n R (a ≫ j.hom.hom)) (x, t) = _
    rw [diagonalLiftMorphism_points]
    exact diagonalMarked_action (d.hom.app R a) x t

end DiagonalTorus

section PairCentre

set_option backward.isDefEq.respectTransparency false

open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private diagonalMarked from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
open Specs.SymplecticMatrixStructure (hyperbolicDiagonal)

private theorem pair_composite_action {R : Type u} [CommRing R] {n : ℕ}
    (g h : MarkedIsometries R n) (x : (Indices (PlaneIndex.{u} n) → R) × R) :
    pairActionInCoordinates (g * h) x =
      pairActionInCoordinates g (pairActionInCoordinates h x) := by
  change splitCoordinates R n (oddMatrixAction (g.val * h.val)
    ((splitCoordinates R n).symm x)) =
      splitCoordinates R n (oddMatrixAction g.val
        ((splitCoordinates R n).symm (splitCoordinates R n
          (oddMatrixAction h.val ((splitCoordinates R n).symm x)))))
  rw [LinearEquiv.symm_apply_apply, map_mul, LinearEquiv.mul_apply]

private theorem covector_mul {R : Type u} [CommRing R] {n : ℕ} (h₂ : (2 : R) = 0)
    (g h : MarkedIsometries R n) (x : Indices (PlaneIndex.{u} n) → R) :
    (markedPair h₂ (g * h)).val.2 x =
      (markedPair h₂ g).val.2 ((markedProjection h₂ h).val *ᵥ x) +
        (markedPair h₂ h).val.2 x := by
  have hh := congrArg Prod.snd (pair_composite_action g h (x, 0))
  rw [markedPair_action h₂ (g * h), markedPair_action h₂ h, markedPair_action h₂ g] at hh
  change (markedPair h₂ (g * h)).val.2 x =
    (markedPair h₂ g).val.2 ((markedPair h₂ h).val.1.val *ᵥ x) + (markedPair h₂ h).val.2 x
  simpa only [Prod.snd, add_zero] using hh

private abbrev dualConstants (R : Type u) [CommRing R] : R →+* DualNumber R :=
  (TrivSqZeroExt.inlAlgHom R R R).toRingHom

private def tangentScale (R : Type u) [CommRing R] : (DualNumber R)ˣ where
  val := ⟨1, 1⟩
  inv := ⟨1, -1⟩
  val_inv := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.snd_mul]
  inv_val := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.snd_mul]

private theorem central_projection_eq_one {R : Type u} [CommRing R] {n : ℕ}
    (h₂ : (2 : R) = 0) (g : MarkedIsometries R n)
    (hc : ∀ b : MarkedIsometries (DualNumber R) n, Commute (markedMap n (dualConstants R) g) b) :
    markedProjection h₂ g = 1 := by
  let D := DualNumber R
  let f := dualConstants R
  let hD : (2 : D) = 0 := by simpa only [map_ofNat, map_zero] using congrArg f h₂
  let g' := markedMap n f g
  let A := markedProjection hD g'
  let L := (markedPair hD g').val.2
  apply Subtype.ext
  ext i j
  let m : (Indices (PlaneIndex.{u} n) → D) →ₗ[D] D :=
    (DualNumber.eps : D) • LinearMap.proj i
  have hm : IsOddPair (1 : PointGroup (PlaneIndex.{u} n) D) m := by
    intro x
    change hyperbolicForm _ D ((1 : Matrix _ _ D) *ᵥ x) + (DualNumber.eps * x i) ^ 2 = _
    rw [Matrix.one_mulVec, mul_pow, pow_two (DualNumber.eps : D), DualNumber.eps_mul_eps, zero_mul, add_zero]
  let b : PairData D n := ⟨(1, m), hm⟩
  let s := (markedPairEquiv hD).symm b
  have hs : markedPair hD s = b := (markedPairEquiv hD).apply_symm_apply b
  let x := standardVector D j
  have he := congrArg (fun p : MarkedIsometries D n => (markedPair hD p).val.2 x) (hc s).eq
  rw [covector_mul, covector_mul] at he
  change L ((markedPair hD s).val.1.val *ᵥ x) + (markedPair hD s).val.2 x =
    (markedPair hD s).val.2 (A.val *ᵥ x) + L x at he
  rw [hs] at he
  change L ((1 : Matrix _ _ D) *ᵥ x) + m x = m (A.val *ᵥ x) + L x at he
  rw [Matrix.one_mulVec, add_comm (L x)] at he
  have he' := add_right_cancel he
  change DualNumber.eps * x i = DualNumber.eps * (A.val *ᵥ x) i at he'
  have hEntry : (A.val *ᵥ x) i = f ((markedProjection h₂ g).val i j) := by
    change (A.val *ᵥ standardVector D j) i = _
    rw [standardVector, Matrix.mulVec_single_one, Matrix.col_apply]
    exact congrArg (fun p : PointGroup (PlaneIndex.{u} n) D => p.val i j)
      (markedProjection_natural h₂ hD f g)
  rw [hEntry] at he'
  have hh := congrArg TrivSqZeroExt.snd he'
  have hε (z : D) : ((DualNumber.eps : D) * z).snd = z.fst := by
    change (0 : R) * z.snd + 1 * z.fst = z.fst
    rw [zero_mul, one_mul, zero_add]
  rw [hε, hε] at hh
  change (x i).fst = ((markedProjection h₂ g).val i j) at hh
  have hx : (x i).fst = (1 : Matrix _ _ R) i j := by
    by_cases hij : i = j
    · subst i
      simp [x, standardVector]
    · simp [x, standardVector, hij]
  exact hh.symm.trans hx

private theorem central_covector_eq_zero {R : Type u} [CommRing R] {n : ℕ}
    (h₂ : (2 : R) = 0) (g : MarkedIsometries R n)
    (hc : ∀ b : MarkedIsometries (DualNumber R) n, Commute (markedMap n (dualConstants R) g) b) :
    (markedPair h₂ g).val.2 = 0 := by
  let D := DualNumber R
  let f := dualConstants R
  let hD : (2 : D) = 0 := by simpa only [map_ofNat, map_zero] using congrArg f h₂
  let g' := markedMap n f g
  let L := (markedPair hD g').val.2
  let t : PlaneIndex.{u} n → Dˣ := fun _ => tangentScale R
  let s := diagonalMarked (downScales t)
  have hL (x : Indices (PlaneIndex.{u} n) → D) : (markedPair hD s).val.2 x = 0 := by
    have hh := congrArg Prod.snd ((markedPair_action hD s x 0).symm.trans (diagonalMarked_action t x 0))
    simpa only [Prod.snd, add_zero] using hh
  have hu (i : Fin n) : (↑((t ⟨i⟩)⁻¹) : D) = ↑(t ⟨i⟩) := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact neg_one_of_two_eq_zero h₂
  apply (Pi.basisFun R (Indices (PlaneIndex.{u} n))).ext
  intro j
  let x := standardVector D j
  have he := congrArg (fun p : MarkedIsometries D n => (markedPair hD p).val.2 x) (hc s).eq
  rw [covector_mul, covector_mul, hL, hL, add_zero, zero_add] at he
  change L ((markedProjection hD s).val *ᵥ x) = L x at he
  rw [markedProjection_diagonal] at he
  have hd : hyperbolicDiagonal t *ᵥ x = (↑(tangentScale R) : D) • x := by
    funext i
    rw [hyperbolicDiagonal, Matrix.mulVec_diagonal]
    cases i with
    | inl i => rfl
    | inr i =>
      obtain ⟨i⟩ := i
      change (↑((t ⟨i⟩)⁻¹) : D) * x (Sum.inr ⟨i⟩) = _
      rw [hu i]
      rfl
  rw [hd, LinearMap.map_smul, smul_eq_mul] at he
  change ↑(tangentScale R) * L (standardVector D j) = L (standardVector D j) at he
  rw [markedCovector_natural h₂ hD f g] at he
  have hh := congrArg TrivSqZeroExt.snd he
  let a := (markedPair h₂ g).val.2 (standardVector R j)
  let c : DualNumber R := (tangentScale R : DualNumber R)
  have hf : c.fst = (1 : R) := rfl
  have hs : c.snd = (1 : R) := rfl
  change (c * (TrivSqZeroExt.inl a : DualNumber R)).snd = (TrivSqZeroExt.inl a : DualNumber R).snd at hh
  have ha : a = 0 := by
    simpa only [DualNumber.snd_mul, hf, hs, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, mul_zero, one_mul, zero_add] using hh
  simpa only [a, Pi.basisFun_apply, LinearMap.zero_apply] using ha

private theorem central_marked_eq_one {k : Type u} [Field k] (n : ℕ) (h₂ : (2 : k) = 0)
    (R : TestAlgebra k) (a : SchemePoints (markedScheme k n) R)
    (ha : Centralizes (𝟙 (markedScheme k n)) a) : a = 1 := by
  let e := markedSchemePoints k n R
  let g := e a
  let f : R ⟶ CommAlgCat.of k (DualNumber R) :=
    Specs.AdjointRepresentation.constants R
  have hc (b : MarkedIsometries (DualNumber R) n) :
      Commute (markedMap n (dualConstants R) g) b := by
    let e' := markedSchemePoints k n (CommAlgCat.of k (DualNumber R))
    have hh := (centralizes_iff _ _).mp ha _ ((testSpec k).map f.op) (e'.symm b)
    have hx : Commute (mapPoints f a) (e'.symm b) := by
      change Commute (mapPoints f a) ((e'.symm b) ≫ 𝟙 _) at hh
      rwa [Category.comp_id] at hh
    have hy := hx.map e'.toMonoidHom
    change Commute (e' (mapPoints f a)) (e' (e'.symm b)) at hy
    rw [MulEquiv.apply_symm_apply, markedSchemePoints_natural] at hy
    exact hy
  have hR : (2 : R) = 0 := two_eq_zero_of_algebra h₂
  have hA := central_projection_eq_one hR g hc
  have hL := central_covector_eq_zero hR g hc
  apply e.injective
  rw [map_one]
  apply (markedPair_injective hR)
  apply pairData_ext
  intro j
  have h1 : pairActionInCoordinates (1 : MarkedIsometries R n) (standardVector R j, 0) =
      (standardVector R j, 0) := by
    change splitCoordinates R n (oddMatrixAction 1 ((splitCoordinates R n).symm _)) = _
    rw [map_one]
    exact LinearEquiv.apply_symm_apply _ _
  rw [markedPair_action hR] at h1
  change ((markedProjection hR g).val *ᵥ _, (markedPair hR g).val.2 _) = _
  rw [hA, hL]
  change ((1 : Matrix _ _ R) *ᵥ standardVector R j, (0 : R)) = _
  simpa only [Matrix.one_mulVec, add_zero] using h1.symm

private theorem pair_centre_trivial {k : Type u} [Field k] (n : ℕ) (h₂ : (2 : k) = 0)
    (Y : SchemeOver k) (g : Y ⟶ (markedScheme k n).X)
    (hg : Centralizes (𝟙 (markedScheme k n)) g) : g = 1 := by
  let O := pairAlgebraicGroup n k
  let U : Specs.ClosedSubgroup O.val := ⟨O.val, 𝟙 O.val, by
    change IsClosedImmersion (𝟙 O.val.X.left)
    infer_instance⟩
  obtain ⟨Z, hZ⟩ := centralizerScheme k O U
  let Z' := Specs.Unipotent.closedSubgroupAlgebraicGroup Z
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr Z'.property.1
  have hz : e.hom ≫ Z.inclusion.hom.hom = 1 :=
    central_marked_eq_one n h₂ A.unop _ ((hZ _ _).mpr ⟨e.hom, rfl⟩)
  have hz' : Z.inclusion.hom.hom = 1 := by
    calc
      _ = e.inv ≫ (e.hom ≫ Z.inclusion.hom.hom) := (e.inv_hom_id_assoc _).symm
      _ = 1 := by rw [hz, MonObj.comp_one]
  obtain ⟨a, ha⟩ := (hZ Y g).mp hg
  rw [← ha, hz', MonObj.comp_one]

end PairCentre

section PairSpinCover

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

open Specs.Arithmetic.OddSpinCharTwoStabilizer
  (ambientForm inclusion radicalVector oddBasis HasDiagonalExponents typeBCoroots)
open Albert.SpinSpecification (ScalarClifford IsSpinPointRepresentation IsVectorAction vectors coefficientMap)
open private ambientGroupScheme ambientStabilizer ambientStabilizerInclusion ambientPointValues
  markedVector ambientBasis stabInclusion_closed stabScheme_points stabScheme_affine StabilizerRing
  stabilizerRing_smooth restrictionToMarked restrictionToMarked_points restriction_finite
  restriction_flat_surjective restriction_radicial restriction_geometricallyConnected
  actualScalarRestrictionKernel oddSpinToStabilizer oddSpinToStabilizer_bijective
  stabilizerSchemePoints ambientPointValues_stabilizer oddCliffordMap restrictPoint markedAction
  oddVectorAction oddCoordinates diagonalCocharacterExists actualDiagonalCocharacters
  ambientCliffordEquiv diagonalLift diagonalLift_tensor_natural diagonalRestrictionFibre
  nativeClifford_vector ambient_map
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
open private spinUnitPoints_represents from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private abbrev markedForm (k : Type u) [Field k] (n : ℕ) :=
  Specs.Arithmetic.OddSpinCharTwoStabilizer.oddForm k n

variable {k : Type u} [Field k] (n : ℕ)

private def intrinsicStabilizerEquiv (h₂ : (2 : k) = 0) (S : TestAlgebra k) :
    SchemePoints (ambientStabilizer k n) S ≃* Albert.SpinFunctor.Spin (markedForm k n) S (oddBasis k n) :=
  (stabilizerSchemePoints k n S).trans
    (MulEquiv.ofBijective (oddSpinToStabilizer n h₂) (oddSpinToStabilizer_bijective n h₂)).symm

private def intrinsicStabilizerPoints (h₂ : (2 : k) = 0) (S : TestAlgebra k) :
    SchemePoints (ambientStabilizer k n) S →* (ScalarClifford (markedForm k n) S)ˣ :=
  (Albert.SpinFunctor.spinSubgroup (markedForm k n) S (oddBasis k n)).subtype.comp
    (intrinsicStabilizerEquiv n h₂ S).toMonoidHom

private theorem intrinsicStabilizerPoints_ambient (h₂ : (2 : k) = 0) (S : TestAlgebra k)
    (a : SchemePoints (ambientStabilizer k n) S) :
    Units.map (oddCliffordMap k S n).toMonoidHom (intrinsicStabilizerPoints n h₂ S a) =
      ambientPointValues k n S (a ≫ (ambientStabilizerInclusion k n).hom.hom) := by
  rw [ambientPointValues_stabilizer]
  let e := MulEquiv.ofBijective (oddSpinToStabilizer (S := S) n h₂)
    (oddSpinToStabilizer_bijective n h₂)
  exact congrArg (fun x => x.val.val) (e.apply_symm_apply (stabilizerSchemePoints k n S a))

private theorem intrinsicStabilizer_represents (h₂ : (2 : k) = 0) :
    IsSpinPointRepresentation (markedForm k n) (ambientStabilizer k n) (intrinsicStabilizerPoints n h₂) := by
  refine ⟨fun S => ⟨Subtype.val_injective.comp (intrinsicStabilizerEquiv n h₂ S).injective, ?_⟩, ?_⟩
  · ext a
    change (∃ b, intrinsicStabilizerPoints n h₂ S b = a) ↔ a ∈ Albert.SpinSpecification.spinUnits (markedForm k n) S
    constructor
    · rintro ⟨b, rfl⟩
      exact (intrinsicStabilizerEquiv n h₂ S b).property
    · intro ha
      exact ⟨(intrinsicStabilizerEquiv n h₂ S).symm ⟨a, ha⟩, by
        change (intrinsicStabilizerEquiv n h₂ S ((intrinsicStabilizerEquiv n h₂ S).symm ⟨a, ha⟩)).val = a
        rw [MulEquiv.apply_symm_apply]⟩
  · intro S T f a
    let hS := LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer.tensorSpinComparison k n h₂ S
    let hT := LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer.tensorSpinComparison k n h₂ T
    apply Units.ext
    apply hT.1
    change (Units.map (oddCliffordMap k T n).toMonoidHom
      (intrinsicStabilizerPoints n h₂ T (mapPoints f a))).val =
        oddCliffordMap k T n (coefficientMap (markedForm k n) S f.hom
          (intrinsicStabilizerPoints n h₂ S a).val)
    rw [intrinsicStabilizerPoints_ambient, ← hS.2.2.2.2 T f.hom]
    change (ambientPointValues k n T ((mapPoints f a) ≫ (ambientStabilizerInclusion k n).hom.hom)).val =
      coefficientMap (ambientForm k n) S f.hom ((Units.map (oddCliffordMap k S n).toMonoidHom
        (intrinsicStabilizerPoints n h₂ S a)).val)
    rw [intrinsicStabilizerPoints_ambient]
    have he := (spinUnitPoints_represents (ambientForm k n) (ambientBasis k n)).2 f
      (a ≫ (ambientStabilizerInclusion k n).hom.hom)
    exact congrArg Units.val (by simpa only [Category.assoc] using he)

set_option maxRecDepth 1500 in
private theorem intrinsicStabilizer_action (h₂ : (2 : k) = 0) (S : TestAlgebra k)
    (a : SchemePoints (ambientStabilizer k n) S) :
    let v := ((Pi.basisFun k (OddIndex n)).baseChange S).equivFun
    IsVectorAction (markedForm k n) S (intrinsicStabilizerPoints n h₂ S a)
      (v.trans ((oddMatrixAction (markedSchemePoints k n S
        (a ≫ (restrictionToMarked k n h₂).hom.hom)).val).trans v.symm)) := by
  dsimp only
  rw [restrictionToMarked_points]
  let b := intrinsicStabilizerEquiv n h₂ S a
  let v := oddCoordinates k S n
  change IsVectorAction (markedForm k n) S b.val
    (v.trans ((oddMatrixAction (markedAction n h₂ b).val).trans v.symm))
  have he : oddMatrixAction (markedAction n h₂ b).val = oddVectorAction n b :=
    oddMatrixAction.apply_symm_apply _
  rw [he]
  intro x
  change vectors (markedForm k n) S
    (v.symm (v (Albert.SpinFunctor.vectorAction (markedForm k n) S (oddBasis k n) b (v.symm (v x))))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact Albert.SpinFunctor.vectorAction_characterization (markedForm k n) S (oddBasis k n) b x

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1700 in
theorem pairStabilizerCover : PairStabilizerCover.{u} := by
  intro k _ n h₂ hn
  let Q := ambientForm k n
  let b := ambientBasis k n
  let r := markedVector k n
  let H := ambientStabilizer k n
  let O := pairAlgebraicGroup n k
  let P := SpGroup (k := k) n
  let p := pairProjection n h₂
  let f := restrictionToMarked k n h₂
  obtain ⟨_, _, _, _, _, hOconn, hOred⟩ := pairGeometry n h₂
  have hHsmooth : Smooth H.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (StabilizerRing Q b r))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (stabilizerRing_smooth k n h₂ hn))
  have hHa : IsAffine H.X.left := stabScheme_affine Q b r
  have hHfinite : IsAffine H.X.left ∧ LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom := by
    refine ⟨hHa, inferInstance, ?_⟩
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (StabilizerRing Q b r))))
    infer_instance
  have hflat := restriction_flat_surjective k n h₂
  have hrad := restriction_radicial k n h₂
  have hHred : GeometricRadicals.IsReductive (⟨H, hHfinite⟩ : Specs.AffineAlgebraicGroup k) :=
    smooth_source_reductive ⟨H, hHfinite⟩ O f hflat.2 hrad hHsmooth
      (restriction_geometricallyConnected k n h₂ hOconn) (hOred hn)
  refine ⟨ambientGroupScheme k n, H, O, P, ambientStabilizerInclusion k n, f, p,
    ambientPointValues k n, intrinsicStabilizerPoints n h₂, markedSchemePoints k n, symplecticSchemePoints n,
    pairProjection_represents n h₂, rfl, hOred hn, pair_centre_trivial n h₂, spinUnitPoints_represents Q b,
    intrinsicStabilizer_represents n h₂, stabInclusion_closed Q b r, ⟨hHfinite, hHred⟩,
    restriction_finite k n h₂, hflat.1, hflat.2, hrad, actualScalarRestrictionKernel n h₂,
    ?_, fun m => diagonalCocharacterExists m, ?_, ?_⟩
  · refine ⟨fun S => ambientCliffordEquiv k S n, fun _ t => diagonalLift n t,
      diagonalLift_tensor_natural n, fun S => ⟨?_, diagonalRestrictionFibre n h₂ S⟩⟩
    exact nativeClifford_vector (ambientForm k n) (ambientForm S n) (ambient_map n)
  · intro χ m hm
    obtain ⟨t, ht, hχ⟩ := hm
    have hb := actualDiagonalCocharacters n h₂ hn χ m t ht hχ
    have hspan : Submodule.span ℤ (typeBCoroots n) = evenSum (Fin n) := by
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact (corootLattice (Fin n)).1
    rw [hspan] at hb
    exact hb
  · intro R
    exact ⟨stabScheme_points Q b r R, fun a =>
      ⟨intrinsicStabilizerPoints_ambient n h₂ R a, intrinsicStabilizer_action n h₂ R a⟩⟩

end PairSpinCover


section PairRoots

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup AffineAlgebraicGroup)
open Specs.GeometricRadicals (IsSplitTorus baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open private orthogonalTorusModel orthogonalTorusFunIso torusPointsToUnits
  orthogonalTorusModel_comm characterCoordinates cocharacterCoordinates characterCoordinates_evaluation
  pairing_coordinates cocharacterExponents_point
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
open private diagonalGroupPointsIso diagonalTorus_points diagonal_isMaximalTorus
  diagonal_isOwnSchemeCentralizer baseChangePowerPointsIso baseChange_diagonal_points
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private groupIsoOfPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
open private diagonalMarked from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer

variable {k : Type u} [Field k] (n : ℕ)

private abbrev coordinateTorus := orthogonalTorusModel (k := k) n

private abbrev symplecticDiagonal := SymplecticMatrixStructure.symplecticDiagonalTorus k (PlaneIndex.{u} n)

private def symplecticDiagonalIso :
    (coordinateTorus (k := k) n).val ≅ (symplecticDiagonal (k := k) n).group :=
  groupIsoOfPoints (G := coordinateTorus n)
    (H := Specs.Unipotent.closedSubgroupAlgebraicGroup (symplecticDiagonal n))
    (orthogonalTorusFunIso n ≪≫ (diagonalGroupPointsIso k (PlaneIndex.{u} n)).symm)

private theorem symplecticDiagonalIso_points (R : TestAlgebra k)
    (a : SchemePoints (coordinateTorus (k := k) n).val R) :
    a ≫ (symplecticDiagonalIso n).hom.hom.hom =
      (diagonalGroupPointsIso k (PlaneIndex.{u} n)).inv.app R ((orthogonalTorusFunIso n).hom.app R a) := by
  let G := coordinateTorus (k := k) n
  let H := Specs.Unipotent.closedSubgroupAlgebraicGroup (symplecticDiagonal (k := k) n)
  let e := orthogonalTorusFunIso n ≪≫ (diagonalGroupPointsIso k (PlaneIndex.{u} n)).symm
  have h : (groupPointsFunctor k).map (symplecticDiagonalIso n).hom = e.hom :=
    Classical.choose_spec ((groupHomComparison k G.val H.val G.property.1).2 e.hom)
  exact DFunLike.congr_fun (congrArg (fun z => (z.app R).hom) h) a

private def coordinateSpTorus : ClosedSubgroup (SpGroup (k := k) n).val where
  group := (coordinateTorus (k := k) n).val
  inclusion := (symplecticDiagonalIso n).hom ≫ (symplecticDiagonal n).inclusion
  isClosedImmersion := by
    change IsClosedImmersion
      ((symplecticDiagonalIso n).hom.hom.hom.left ≫ (symplecticDiagonal n).inclusion.hom.hom.left)
    haveI : IsIso (symplecticDiagonalIso (k := k) n).hom.hom.hom.left :=
      inferInstanceAs (IsIso
        (((Grp.forget (SchemeOver k)) ⋙ Over.forget (Spec (CommRingCat.of k))).map
          (symplecticDiagonalIso n).hom))
    haveI := (symplecticDiagonal (k := k) n).isClosedImmersion
    infer_instance

private theorem coordinateSpTorus_points (R : TestAlgebra k) (t : PlaneIndex.{u} n → Rˣ) :
    (symplecticSchemePoints n R ((orthogonalTorusFunIso n).inv.app R t ≫
      (coordinateSpTorus n).inclusion.hom.hom)).val =
        Specs.SymplecticMatrixStructure.hyperbolicDiagonal t := by
  change (symplecticSchemePoints n R ((orthogonalTorusFunIso n).inv.app R t ≫
    (symplecticDiagonalIso n).hom.hom.hom ≫ (symplecticDiagonal n).inclusion.hom.hom)).val = _
  rw [← Category.assoc, symplecticDiagonalIso_points, Iso.inv_hom_id_app_apply]
  exact diagonalTorus_points R t

private abbrev coordinatePairTorus (h₂ : (2 : k) = 0) : ClosedSubgroup (pairAlgebraicGroup n k).val where
  group := (coordinateTorus (k := k) n).val
  inclusion := diagonalLiftMorphism (coordinateSpTorus n) (orthogonalTorusFunIso n)
  isClosedImmersion := by
    let j := diagonalLiftMorphism (coordinateSpTorus (k := k) n) (orthogonalTorusFunIso n)
    let p := pairProjection n h₂
    have he := diagonalLiftMorphism_projection h₂ (coordinateSpTorus n)
      (orthogonalTorusFunIso n) (coordinateSpTorus_points n)
    have h := congrArg (fun f : (coordinateTorus (k := k) n).val ⟶ (SpGroup n).val =>
      f.hom.hom.left) he
    change j.hom.hom.left ≫ p.hom.hom.left = (coordinateSpTorus (k := k) n).inclusion.hom.hom.left at h
    have : IsClosedImmersion (j.hom.hom.left ≫ p.hom.hom.left) :=
      h.symm ▸ (coordinateSpTorus (k := k) n).isClosedImmersion
    have := (pairGeometry n h₂).1
    exact IsClosedImmersion.of_comp j.hom.hom.left p.hom.hom.left

private theorem coordinatePairTorus_points (h₂ : (2 : k) = 0) (R : TestAlgebra k)
    (t : SchemePoints (coordinatePairTorus n h₂).group R) :
    markedSchemePoints k n R (t ≫ (coordinatePairTorus n h₂).inclusion.hom.hom) =
      diagonalMarked (torusPointsToUnits n R t) :=
  diagonalLiftMorphism_points (coordinateSpTorus n) (orthogonalTorusFunIso n) R t

private theorem coordinatePairTorus_split (h₂ : (2 : k) = 0) :
    IsSplitTorus (coordinatePairTorus n h₂).group :=
  ⟨n, ⟨Iso.refl _⟩⟩

set_option maxHeartbeats 1100000 in
private theorem coordinatePairTorus_maximal (h₂ : (2 : k) = 0) :
    IsGeometricallyMaximal (coordinatePairTorus n h₂) := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let O' := Specs.Unipotent.baseChangedAlgebraicGroup K (pairAlgebraicGroup n k)
  let P' := Specs.Unipotent.baseChangedAlgebraicGroup K (SpGroup (k := k) n)
  let p := pairProjection n h₂
  let p' : O'.val ⟶ P'.val := F.map p
  obtain ⟨hpfin, _, _, hrad, _, _, _⟩ := pairGeometry n h₂
  haveI : IsFinite p.hom.hom.left := hpfin
  let T := coordinatePairTorus n h₂
  let U := coordinateSpTorus (k := k) n
  let j := T.inclusion
  have hj : j ≫ p = U.inclusion := diagonalLiftMorphism_projection h₂ U
    (orthogonalTorusFunIso n) (coordinateSpTorus_points n)
  have hUcl : IsClosedImmersion (F.map U.inclusion).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
      (fieldSpecMap k K) U.inclusion.hom.hom U.isClosedImmersion
  have hTcl : IsClosedImmersion (F.map j).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
      (fieldSpecMap k K) j.hom.hom T.isClosedImmersion
  refine ⟨hTcl, ?_⟩
  let U' := baseChangedSubgroup K U hUcl
  let j' : U'.group ⟶ O'.val := F.map j
  have hj' : j' ≫ p' = U'.inclusion := (F.map_comp j p).symm.trans (congrArg F.map hj)
  have hpb := (baseChangeMapPullback (K := K) p.hom.hom).flip
  have : UniversallyInjective p'.hom.hom.left := MorphismProperty.of_isPullback hpb hrad
  have : IsSeparated p'.hom.hom.left := MorphismProperty.of_isPullback hpb inferInstance
  let c := SymplecticPointIso (k := k) (n := n)
  let c' := SymplecticMatrixStructure.baseChangeSymplecticPointsIso K c
  let d := orthogonalTorusFunIso (k := k) n
  let d' := baseChangePowerPointsIso (K := K) d
  have hd' := baseChange_diagonal_points (K := K) c U d (coordinateSpTorus_points n)
  exact maximal_lift_of_radicial p' c' U' j' hTcl hj'
    (diagonal_isMaximalTorus (G := P') c' U' d' hd') (diagonal_isOwnSchemeCentralizer c' U' d' hd')

end PairRoots

section PairMatrices

set_option backward.isDefEq.respectTransparency false

open Specs.AdjointRepresentation (GroupPoints constants scale dualMap)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors pairing characterValue)
open Specs.Arithmetic.OddSpinCharTwoStabilizer (OddMatrixIndex)
open Specs.Arithmetic.OddSpinOrthogonalRootDatum (Index partner diagonalUnit)
open private torusPointsToUnits from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
open private matrixDual from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open private matrixDual_injective vectorWeight vectorWeight_injective vectorWeight_partner
  roots_iff_entries monomial monomial_sub monomial_vectorWeight vectorWeight_isAxis
  IsAxis markedCoroot partner_partner partner_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalRootDatum
open private diagonalWeights from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer

variable {k : Type u} [Field k] {n : ℕ}

private def markedIndexEquiv (n : ℕ) : Index.{u} n ≃ OddMatrixIndex.{u} n where
  toFun i := ⟨i.down.elim (fun j : Fin n ⊕ Fin n => (↑(toLex j) : OddIndex n)) (fun _ => ⊤)⟩
  invFun i := ⟨WithTop.recTopCoe (.inr ()) (fun j => .inl (ofLex j)) i.down⟩
  left_inv i := by
    rcases i with ⟨j | ⟨⟩⟩ <;> rfl
  right_inv i := by
    rcases i with ⟨i⟩
    cases i using WithTop.recTopCoe <;> rfl

private def pairMatrix (R : TestAlgebra k) (a : SchemePoints (markedScheme k n) R) :
    Matrix (Index.{u} n) (Index.{u} n) R :=
  Matrix.reindexRingEquiv R (markedIndexEquiv n).symm (markedSchemePoints k n R a).val.val

private theorem pairMatrix_injective (R : TestAlgebra k) :
    Function.Injective (pairMatrix (n := n) R) := by
  intro a b h
  exact (markedSchemePoints k n R).injective (Subtype.ext
    (Units.ext ((Matrix.reindexRingEquiv R (markedIndexEquiv n).symm).injective h)))

private theorem pairMatrix_one (R : TestAlgebra k) : pairMatrix (n := n) R 1 = 1 := by
  simp only [pairMatrix, map_one, Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one]

private theorem pairMatrix_mul (R : TestAlgebra k) (a b : SchemePoints (markedScheme k n) R) :
    pairMatrix R (a * b) = pairMatrix R a * pairMatrix R b := by
  simp only [pairMatrix, map_mul, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]

private theorem pairMatrix_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (a : SchemePoints (markedScheme k n) R) :
    pairMatrix S (mapPoints f a) = f.hom.toRingHom.mapMatrix (pairMatrix R a) := by
  unfold pairMatrix
  rw [markedSchemePoints_natural]
  rfl

private theorem pairMatrix_diagonal (h₂ : (2 : k) = 0) (R : TestAlgebra k)
    (t : SchemePoints (coordinatePairTorus n h₂).group R) :
    pairMatrix R (t ≫ (coordinatePairTorus n h₂).inclusion.hom.hom) =
      diagonal (fun i => (diagonalUnit (torusPointsToUnits n R t) i : R)) := by
  unfold pairMatrix
  rw [coordinatePairTorus_points]
  change Matrix.reindexRingEquiv R (markedIndexEquiv n).symm
    (diagonal (fun i : OddMatrixIndex.{u} n => (diagonalWeights (torusPointsToUnits n R t) i.down : R))) = _
  ext i j
  change diagonal (fun l : OddMatrixIndex.{u} n => (diagonalWeights (torusPointsToUnits n R t) l.down : R))
    (markedIndexEquiv n i) (markedIndexEquiv n j) = _
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    rcases i with ⟨(i | i) | ⟨⟩⟩ <;> rfl
  · rw [Matrix.diagonal_apply_ne _ ((markedIndexEquiv n).injective.ne h), Matrix.diagonal_apply_ne _ h]

private abbrev fieldAlgebra (k : Type u) [Field k] := CommAlgCat.of k k

private abbrev dualAlgebra (R : TestAlgebra k) : TestAlgebra k := CommAlgCat.of k (DualNumber R)

private def pairTangentMatrix (v : Specs.Lie k (markedScheme k n)) :
    Matrix (Index.{u} n) (Index.{u} n) k :=
  (matrixDual (pairMatrix (dualAlgebra (fieldAlgebra k)) v.toMul.val)).snd

private theorem pairTangentMatrix_dual (v : Specs.Lie k (markedScheme k n)) :
    matrixDual (pairMatrix (dualAlgebra (fieldAlgebra k)) v.toMul.val) =
      (1, pairTangentMatrix v) := by
  refine TrivSqZeroExt.ext ?_ rfl
  have h := pairMatrix_natural (dualReduction k) v.toMul.val
  change pairMatrix (fieldAlgebra k) (reduceTangentPoints (markedScheme k n) v.toMul.val) = _ at h
  rw [v.toMul.property, pairMatrix_one] at h
  exact h.symm

private theorem pairTangentMatrix_injective : Function.Injective (pairTangentMatrix (k := k) (n := n)) := by
  intro x y h
  change x.toMul = y.toMul
  apply Subtype.ext
  apply pairMatrix_injective (dualAlgebra (fieldAlgebra k))
  apply matrixDual_injective
  exact (pairTangentMatrix_dual x).trans
    ((congrArg (fun m : Matrix (Index.{u} n) (Index.{u} n) k => ((1 : Matrix _ _ k), m) :
      Matrix _ _ k → DualNumber (Matrix _ _ k)) h).trans (pairTangentMatrix_dual y).symm)

private theorem pairTangentMatrix_zero :
    pairTangentMatrix (k := k) (n := n) 0 = 0 := by
  change (matrixDual (pairMatrix (n := n) (dualAlgebra (fieldAlgebra k)) 1)).snd = 0
  rw [pairMatrix_one, map_one]
  rfl

private theorem pairWeight_iff (h₂ : (2 : k) = 0)
    (χ : Character (coordinatePairTorus n h₂).group) (v : Specs.Lie k (markedScheme k n)) :
    v ∈ adjointWeightVectors (coordinatePairTorus n h₂) χ ↔
      ∀ (R : TestAlgebra k) (t : GroupPoints (coordinatePairTorus n h₂).group R)
        (i j : Index.{u} n),
        (diagonalUnit (torusPointsToUnits n R t) i : R) * algebraMap k R (pairTangentMatrix v i j) =
          characterValue χ R t * algebraMap k R (pairTangentMatrix v i j) *
            (diagonalUnit (torusPointsToUnits n R t) j : R) := by
  classical
  change (∀ (R : TestAlgebra k) (t : GroupPoints (coordinatePairTorus n h₂).group R), _) ↔ _
  have key (R : TestAlgebra k) (t : GroupPoints (coordinatePairTorus n h₂).group R) :
      let a : fieldAlgebra k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
      let x : GroupPoints (markedScheme k n) (dualAlgebra R) := mapPoints (dualMap a) v.toMul.val
      let g : GroupPoints (markedScheme k n) (dualAlgebra R) := mapPoints (constants R) (t ≫ (coordinatePairTorus n h₂).inclusion.hom.hom)
      let y : GroupPoints (markedScheme k n) (dualAlgebra R) := mapPoints (scale R (characterValue χ R t)) x
      g * x * g⁻¹ = y ↔
        ∀ i j : Index.{u} n,
          (diagonalUnit (torusPointsToUnits n R t) i : R) * algebraMap k R (pairTangentMatrix v i j) =
            characterValue χ R t * algebraMap k R (pairTangentMatrix v i j) *
              (diagonalUnit (torusPointsToUnits n R t) j : R) := by
    intro a x g y
    have hmul : g * x * g⁻¹ = y ↔ g * x = y * g := by
      constructor
      · intro h
        simpa using congrArg (· * g) h
      · intro h
        rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hmul, ← (pairMatrix_injective (dualAlgebra R)).eq_iff, pairMatrix_mul, pairMatrix_mul,
      ← (matrixDual_injective (n := n) R).eq_iff, map_mul, map_mul]
    let D := diagonal (fun i : Index.{u} n => (diagonalUnit (torusPointsToUnits n R t) i : R))
    let X := (algebraMap k R).mapMatrix (pairTangentMatrix v)
    let s := characterValue χ R t
    have hx : matrixDual (pairMatrix (dualAlgebra R) x) = (1, X) := by
      dsimp only [x]
      rw [pairMatrix_natural]
      apply TrivSqZeroExt.ext
      · ext i j
        have he := congrArg (fun z : DualNumber (Matrix (Index.{u} n) (Index.{u} n) k) => z.fst i j)
          (pairTangentMatrix_dual v)
        change a.hom ((pairMatrix (dualAlgebra (fieldAlgebra k)) v.toMul.val i j).fst) = _
        change (pairMatrix (dualAlgebra (fieldAlgebra k)) v.toMul.val i j).fst = _ at he
        rw [he]
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
      · rfl
    have hg : matrixDual (pairMatrix (dualAlgebra R) g) = (D, 0) := by
      dsimp only [g]
      rw [pairMatrix_natural, pairMatrix_diagonal]
      rfl
    have hy : matrixDual (pairMatrix (dualAlgebra R) y) = (1, s • X) := by
      dsimp only [y]
      rw [pairMatrix_natural]
      apply TrivSqZeroExt.ext
      · change (matrixDual (pairMatrix (dualAlgebra R) x)).fst = 1
        exact congrArg TrivSqZeroExt.fst hx
      · change s • (matrixDual (pairMatrix (dualAlgebra R) x)).snd = s • X
        exact congrArg (fun z : DualNumber (Matrix (Index.{u} n) (Index.{u} n) R) => s • z.snd) hx
    rw [hg, hx, hy]
    let A : DualNumber (Matrix (Index.{u} n) (Index.{u} n) R) := (D, 0)
    let B : DualNumber (Matrix (Index.{u} n) (Index.{u} n) R) := (1, X)
    let C : DualNumber (Matrix (Index.{u} n) (Index.{u} n) R) := (1, s • X)
    change A * B = C * A ↔ _
    have he : A * B = (D, D * X) := by
      apply TrivSqZeroExt.ext (mul_one _)
      change D * X + 0 * 1 = D * X
      simp
    have he' : C * A = (D, (s • X) * D) := by
      apply TrivSqZeroExt.ext (one_mul _)
      change 1 * 0 + (s • X) * D = (s • X) * D
      simp
    rw [he, he']
    constructor
    · intro he i j
      have h' := congrArg (fun z : DualNumber (Matrix (Index.{u} n) (Index.{u} n) R) =>
        z.snd i j) he
      simpa [D, X, s, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc] using h'
    · intro he
      refine TrivSqZeroExt.ext ?_ ?_
      · rfl
      · change D * X = (s • X) * D
        ext i j
        simpa [D, X, s, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc] using he i j
  exact ⟨fun h R t => (key R t).mp (h R t), fun h R t => (key R t).mpr (h R t)⟩

end PairMatrices

section TangentEntries

set_option backward.isDefEq.respectTransparency false

open Specs.Arithmetic.OddSpinCharTwoStabilizer (oddBasis OddMatrixIndex)
open Specs.Arithmetic.OddSpinOrthogonalRootDatum (Index partner)
open private oddMatrixAction_entry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer

variable {k : Type u} [Field k] {n : ℕ}

private abbrev HyperbolicLabels (n : ℕ) := Indices (PlaneIndex.{u} n)

private def planeLabel (i : HyperbolicLabels.{u} n) : Index.{u} n :=
  ⟨.inl (hyperbolicIndices n i)⟩

private abbrev markLabel (n : ℕ) : Index.{u} n := ⟨.inr ()⟩

private theorem planeLabel_injective : Function.Injective (planeLabel (n := n)) := by
  intro i j hij
  exact (hyperbolicIndices n).injective (Sum.inl.inj (congrArg ULift.down hij))

private theorem planeLabel_ne_mark (i : HyperbolicLabels.{u} n) : planeLabel i ≠ markLabel n :=
  fun h => by
    have he : Sum.inl (hyperbolicIndices n i) = Sum.inr () :=
      congrArg (fun a : Index.{u} n => a.down) h
    cases he

private theorem planeLabel_swap (i : HyperbolicLabels.{u} n) :
    planeLabel i.swap = partner (planeLabel i) := by
  rcases i with ⟨i⟩ | ⟨i⟩ <;> rfl

private theorem cases_pairLabel (i : Index.{u} n) :
    i = markLabel n ∨ ∃ j, i = planeLabel j := by
  rcases i with ⟨x | ⟨⟩⟩
  · exact Or.inr ⟨(hyperbolicIndices n).symm x,
      congrArg (fun j => (⟨.inl j⟩ : Index.{u} n)) ((hyperbolicIndices n).apply_symm_apply x).symm⟩
  · exact Or.inl rfl

private theorem pairMatrix_plane_entry (R : TestAlgebra k) (h₂ : (2 : R) = 0)
    (a : SchemePoints (markedScheme k n) R) (i j : HyperbolicLabels.{u} n) :
    pairMatrix R a (planeLabel i) (planeLabel j) =
      (markedPair h₂ (markedSchemePoints k n R a)).val.1.val i j :=
  (symplectic_entry h₂ (markedSchemePoints k n R a) i j).symm

private theorem pairMatrix_covector_entry (R : TestAlgebra k) (h₂ : (2 : R) = 0)
    (a : SchemePoints (markedScheme k n) R) (j : HyperbolicLabels.{u} n) :
    pairMatrix R a (markLabel n) (planeLabel j) =
      (markedPair h₂ (markedSchemePoints k n R a)).val.2 (standardVector R j) :=
  (covector_entry h₂ (markedSchemePoints k n R a) j).symm

private theorem pairMatrix_mark_column (R : TestAlgebra k) (a : SchemePoints (markedScheme k n) R)
    (i : Index.{u} n) :
    pairMatrix R a i (markLabel n) = (1 : Matrix (Index.{u} n) (Index.{u} n) R) i (markLabel n) := by
  let j := markedIndexEquiv n i
  let g := markedSchemePoints k n R a
  have h : oddBasis R n (⟨⊤⟩ : OddMatrixIndex.{u} n) = radicalVector R n := by
    simp [oddBasis, Pi.basisFun_apply]
  change g.val.val j ⟨⊤⟩ = _
  rw [← oddMatrixAction_entry, h, g.property.2]
  rw [Matrix.one_apply]
  have he : j.down = ⊤ ↔ i = markLabel n := by
    change (markedIndexEquiv n i).down = (markedIndexEquiv n (markLabel n)).down ↔ _
    rw [ULift.down_inj, (markedIndexEquiv n).injective.eq_iff]
  simp [radicalVector, Pi.single_apply, he]

private theorem J_mul_eq_swap (h₂ : (2 : k) = 0)
    (X : Matrix (HyperbolicLabels.{u} n) (HyperbolicLabels.{u} n) k)
    (i j : HyperbolicLabels.{u} n) :
    (Matrix.J (PlaneIndex.{u} n) k * X) i j = X i.swap j := by
  have hneg : (-1 : k) = 1 := neg_one_of_two_eq_zero h₂
  rcases i with i | i
  · simp only [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Fintype.sum_sum_type, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.neg_apply]
    simp [Matrix.one_apply, ite_mul]
    rw [← neg_one_mul, hneg, one_mul]
  · simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply, ite_mul]

private theorem pairTangentMatrix_mark_column (v : Specs.Lie k (markedScheme k n)) (i : Index.{u} n) :
    pairTangentMatrix v i (markLabel n) = 0 := by
  change (pairMatrix (dualAlgebra (fieldAlgebra k)) v.toMul.val i (markLabel n)).snd = 0
  rw [pairMatrix_mark_column, Matrix.one_apply]
  split <;> rfl

private theorem pairTangentMatrix_opposite_zero (h₂ : (2 : k) = 0)
    (v : Specs.Lie k (markedScheme k n)) (j : Index.{u} n) :
    pairTangentMatrix v (partner j) j = 0 := by
  rcases cases_pairLabel j with rfl | ⟨j, rfl⟩
  · exact pairTangentMatrix_mark_column v _
  let D := dualAlgebra (fieldAlgebra k)
  let a := v.toMul.val
  have hD : (2 : D) = 0 := two_eq_zero_of_algebra h₂
  let p := (markedPair hD (markedSchemePoints k n D a)).val
  let X : Matrix (HyperbolicLabels.{u} n) (HyperbolicLabels.{u} n) k :=
    fun a b => pairTangentMatrix v (planeLabel a) (planeLabel b)
  have hp : p.1.val = tangentMatrix X := by
    apply Matrix.ext
    intro i j
    have he := pairMatrix_plane_entry D hD a i j
    apply TrivSqZeroExt.ext
    · rw [← he]
      have hf := congrArg
        (fun z : DualNumber (Matrix (Index.{u} n) (Index.{u} n) k) => z.fst (planeLabel i) (planeLabel j))
        (pairTangentMatrix_dual v)
      change _ = (1 : Matrix (HyperbolicLabels.{u} n) (HyperbolicLabels.{u} n) k) i j
      rw [show (pairMatrix D a (planeLabel i) (planeLabel j)).fst =
        (1 : Matrix (Index.{u} n) (Index.{u} n) k) (planeLabel i) (planeLabel j) from hf]
      simp [Matrix.one_apply, planeLabel_injective.eq_iff]
    · change (p.1.val i j).snd = (pairMatrix D a (planeLabel i) (planeLabel j)).snd
      exact congrArg TrivSqZeroExt.snd he.symm
  have hl (j) : (p.2 (standardVector D j)).fst = 0 := by
    rw [← pairMatrix_covector_entry D hD a j]
    have hf := congrArg
      (fun z : DualNumber (Matrix (Index.{u} n) (Index.{u} n) k) => z.fst (markLabel n) (planeLabel j))
      (pairTangentMatrix_dual v)
    change (pairMatrix D a (markLabel n) (planeLabel j)).fst = _
    rw [show (pairMatrix D a (markLabel n) (planeLabel j)).fst =
      (1 : Matrix (Index.{u} n) (Index.{u} n) k) (markLabel n) (planeLabel j) from hf]
    exact Matrix.one_apply_ne (planeLabel_ne_mark j).symm
  have hd := ((pairTangent k (PlaneIndex.{u} n) h₂ X p.2 hl).mp
    ⟨p.1, hp, (markedPair hD (markedSchemePoints k n D a)).property⟩).2 j
  rw [J_mul_eq_swap h₂] at hd
  rwa [← planeLabel_swap]

private theorem exists_pairTangentMatrix (h₂ : (2 : k) = 0)
    (X : Matrix (HyperbolicLabels.{u} n) (HyperbolicLabels.{u} n) k)
    (m : HyperbolicLabels.{u} n → k)
    (hsym : ∀ i j, X i.swap j = X j.swap i) (hdiag : ∀ i, X i.swap i = 0) :
    ∃ v : Specs.Lie k (markedScheme k n),
      (∀ i j, pairTangentMatrix v (planeLabel i) (planeLabel j) = X i j) ∧
      (∀ j, pairTangentMatrix v (markLabel n) (planeLabel j) = m j) := by
  let D := dualAlgebra (fieldAlgebra k)
  have hD : (2 : D) = 0 := two_eq_zero_of_algebra h₂
  let l : (HyperbolicLabels.{u} n → D) →ₗ[D] D :=
    (Pi.basisFun D _).constr D (fun i => (⟨0, m i⟩ : DualNumber k))
  have hl (j) : l (standardVector D j) = ⟨0, m j⟩ := by
    change l (Pi.single j 1) = _
    rw [← Pi.basisFun_apply]
    exact (Pi.basisFun D (HyperbolicLabels.{u} n)).constr_basis D _ j
  have hJ : (Matrix.J (PlaneIndex.{u} n) k * X).IsSymm := by
    ext i j
    rw [Matrix.transpose_apply, J_mul_eq_swap h₂, J_mul_eq_swap h₂, hsym]
  obtain ⟨A, hA, hp⟩ := (pairTangent k (PlaneIndex.{u} n) h₂ X l (fun j =>
    congrArg TrivSqZeroExt.fst (hl j))).mpr ⟨hJ, fun j => (J_mul_eq_swap h₂ X j j).trans (hdiag j)⟩
  let g := (markedPairEquiv hD).symm ⟨(A, l), hp⟩
  let a := (markedSchemePoints k n D).symm g
  have he : markedPair hD (markedSchemePoints k n D a) = ⟨(A, l), hp⟩ := by
    change markedPairEquiv hD _ = _
    rw [show markedSchemePoints k n D a = g from MulEquiv.apply_symm_apply _ _,
      show g = (markedPairEquiv hD).symm ⟨(A, l), hp⟩ from rfl, Equiv.apply_symm_apply]
  have hplane (i j : HyperbolicLabels.{u} n) :
      pairMatrix D a (planeLabel i) (planeLabel j) = tangentMatrix X i j := by
    rw [pairMatrix_plane_entry D hD a, he]
    exact congrFun (congrFun hA i) j
  have hrow (j : HyperbolicLabels.{u} n) :
      pairMatrix D a (markLabel n) (planeLabel j) = ⟨0, m j⟩ := by
    rw [pairMatrix_covector_entry D hD a, he]
    exact hl j
  have ha : reduceTangentPoints (markedScheme k n) a = 1 := by
    apply pairMatrix_injective (fieldAlgebra k)
    change pairMatrix (fieldAlgebra k) (mapPoints (dualReduction k) a) = _
    rw [pairMatrix_natural, pairMatrix_one]
    ext i j
    change (pairMatrix D a i j).fst = _
    rcases cases_pairLabel j with rfl | ⟨j, rfl⟩
    · rw [pairMatrix_mark_column, Matrix.one_apply, Matrix.one_apply]
      split <;> rfl
    rcases cases_pairLabel i with rfl | ⟨i, rfl⟩
    · rw [hrow, Matrix.one_apply_ne (planeLabel_ne_mark j).symm]
      rfl
    · rw [hplane]
      change (1 : Matrix (HyperbolicLabels.{u} n) (HyperbolicLabels.{u} n) k) i j =
        (1 : Matrix (Index.{u} n) (Index.{u} n) k) (planeLabel i) (planeLabel j)
      simp [Matrix.one_apply, planeLabel_injective.eq_iff]
  let v : Specs.Lie k (markedScheme k n) := Additive.ofMul ⟨a, ha⟩
  exact ⟨v, fun i j => congrArg TrivSqZeroExt.snd (hplane i j), fun j => congrArg TrivSqZeroExt.snd (hrow j)⟩

end TangentEntries

section RootWeights

set_option backward.isDefEq.respectTransparency false

open Specs.Arithmetic.OddSpinOrthogonalRootDatum (Index partner diagonalUnit roots)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue)
open Specs.AdjointRepresentation (GroupPoints)
open private vectorWeight vectorWeight_injective roots_iff_entries monomial OddSpinOrthogonalRootDatum.monomial_sub
  monomial_vectorWeight vectorWeight_partner partner_partner
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalRootDatum
open private characterCoordinates characterCoordinates_evaluation torusPointsToUnits
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo

variable {k : Type u} [Field k] {n : ℕ}

private theorem pairCharacterCoordinates_of_eval (h₂ : (2 : k) = 0)
    (χ : Character (coordinatePairTorus n h₂).group) (m : Fin n → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : GroupPoints (coordinatePairTorus n h₂).group R),
      characterValue χ R t = (monomial (torusPointsToUnits n R t) m : R)) :
    characterCoordinates n (Additive.ofMul χ) = m := by
  let ψ : Character (coordinatePairTorus n h₂).group :=
    Additive.toMul ((characterCoordinates (k := k) n).symm m)
  have hm : characterCoordinates n (Additive.ofMul ψ) = m := (characterCoordinates n).apply_symm_apply _
  have hχ : χ = ψ := RootData.CharacterPairing.characterValuesDetectCharacters
    (coordinatePairTorus_split n h₂) (fun R t => by
      rw [h R t, characterCoordinates_evaluation, hm]
      rfl)
  rw [hχ, hm]

private theorem character_of_tangent_entry (h₂ : (2 : k) = 0)
    {χ : Character (coordinatePairTorus n h₂).group} {v : Specs.Lie k (markedScheme k n)}
    (hv : v ∈ adjointWeightVectors (coordinatePairTorus n h₂) χ)
    {i j : Index.{u} n} (hij : pairTangentMatrix v i j ≠ 0) :
    characterCoordinates n (Additive.ofMul χ) = vectorWeight i - vectorWeight j := by
  apply pairCharacterCoordinates_of_eval h₂
  intro R t
  let u := torusPointsToUnits n R t
  have hc := (pairWeight_iff h₂ χ v).mp hv R t i j
  let a := algebraMap k R (pairTangentMatrix v i j)
  have ha : IsUnit a := (isUnit_iff_ne_zero.mpr hij).map (algebraMap k R)
  rw [mul_right_comm] at hc
  have he := ha.mul_left_inj.mp hc
  rw [OddSpinOrthogonalRootDatum.monomial_sub, monomial_vectorWeight, monomial_vectorWeight, Units.val_mul]
  apply (diagonalUnit u j).mul_left_inj.mp
  simpa only [u, mul_assoc, Units.inv_mul, mul_one] using he.symm

private theorem pairWeight_of_support (h₂ : (2 : k) = 0)
    (χ : Character (coordinatePairTorus n h₂).group) (v : Specs.Lie k (markedScheme k n))
    (h : ∀ i j, pairTangentMatrix v i j ≠ 0 →
      characterCoordinates n (Additive.ofMul χ) = vectorWeight i - vectorWeight j) :
    v ∈ adjointWeightVectors (coordinatePairTorus n h₂) χ := by
  apply (pairWeight_iff h₂ χ v).mpr
  intro R t i j
  by_cases hz : pairTangentMatrix v i j = 0
  · simp [hz]
  rw [characterCoordinates_evaluation, h i j hz]
  let u := torusPointsToUnits n R t
  let a := algebraMap k R (pairTangentMatrix v i j)
  change (diagonalUnit u i : R) * a = (monomial u (vectorWeight i - vectorWeight j) : R) *
    a * (diagonalUnit u j : R)
  rw [OddSpinOrthogonalRootDatum.monomial_sub, monomial_vectorWeight, monomial_vectorWeight, Units.val_mul]
  calc
    (diagonalUnit u i : R) * a =
        ((diagonalUnit u i : R) * a) * (((diagonalUnit u j)⁻¹ : Rˣ) : R) * (diagonalUnit u j : R) := by
          rw [mul_assoc ((diagonalUnit u i : R) * a), Units.inv_mul, mul_one]
    _ = _ := by ring

private theorem short_root_vector (h₂ : (2 : k) = 0)
    (χ : Character (coordinatePairTorus n h₂).group) (j : HyperbolicLabels.{u} n)
    (hχ : characterCoordinates n (Additive.ofMul χ) =
      vectorWeight (markLabel.{u} n) - vectorWeight (planeLabel j)) :
    ∃ v ∈ adjointWeightVectors (coordinatePairTorus n h₂) χ, v ≠ 0 := by
  obtain ⟨v, hv, hm⟩ := exists_pairTangentMatrix h₂ 0 (Pi.single j 1) (by simp) (by simp)
  refine ⟨v, pairWeight_of_support h₂ χ v ?_, ?_⟩
  · intro i l h
    rcases cases_pairLabel l with rfl | ⟨l, rfl⟩
    · exact (h (pairTangentMatrix_mark_column v i)).elim
    rcases cases_pairLabel i with rfl | ⟨i, rfl⟩
    · have he : j = l := by
        by_contra hn
        exact h (by rw [hm]; simp [Pi.single_apply, hn, Ne.symm hn])
      subst l
      exact hχ
    · exact (h (hv i l)).elim
  · intro he
    have h1 := hm j
    rw [he, pairTangentMatrix_zero] at h1
    exact zero_ne_one (α := k) (by simpa using h1)

private theorem long_root_vector (h₂ : (2 : k) = 0)
    (χ : Character (coordinatePairTorus n h₂).group)
    (i j : HyperbolicLabels.{u} n) (hij : i ≠ j.swap)
    (hχ : characterCoordinates n (Additive.ofMul χ) =
      vectorWeight (planeLabel i) - vectorWeight (planeLabel j)) :
    ∃ v ∈ adjointWeightVectors (coordinatePairTorus n h₂) χ, v ≠ 0 := by
  let X : Matrix (HyperbolicLabels.{u} n) (HyperbolicLabels.{u} n) k :=
    Matrix.single i j 1 + Matrix.single j.swap i.swap 1
  have hswap (a b : HyperbolicLabels.{u} n) : a = b.swap ↔ a.swap = b :=
    ⟨fun h => by rw [h, Sum.swap_swap], fun h => by rw [← h, Sum.swap_swap]⟩
  have hsym (a b) : X a.swap b = X b.swap a := by
    simp only [X, Matrix.add_apply, Matrix.single_apply, hswap, Sum.swap_swap]
    simp only [@and_comm (j = a) (i.swap = b), @and_comm (j = b) (i.swap = a)]
    exact add_comm _ _
  have hd (a) : X a.swap a = 0 := by
    have h₁ : ¬ (i = a.swap ∧ j = a) := fun h => hij (h.1.trans (congrArg Sum.swap h.2).symm)
    have h₂' : ¬ (j.swap = a.swap ∧ i.swap = a) := fun h => hij ((hswap i a).mpr h.2 |>.trans h.1.symm)
    simp [X, Matrix.single_apply, h₁, h₂']
  obtain ⟨v, hv, hm⟩ := exists_pairTangentMatrix h₂ X 0 hsym hd
  have h1 : pairTangentMatrix v (planeLabel i) (planeLabel j) = 1 := by
    simp [hv, X, Matrix.single_apply, Ne.symm hij]
  refine ⟨v, pairWeight_of_support h₂ χ v ?_, ?_⟩
  · intro a b h
    rcases cases_pairLabel b with rfl | ⟨b, rfl⟩
    · exact (h (pairTangentMatrix_mark_column v a)).elim
    rcases cases_pairLabel a with rfl | ⟨a, rfl⟩
    · exact (h (hm b)).elim
    rw [hv] at h
    by_cases h₁ : i = a ∧ j = b
    · rcases h₁ with ⟨rfl, rfl⟩
      exact hχ
    by_cases h₂' : j.swap = a ∧ i.swap = b
    · rcases h₂' with ⟨rfl, rfl⟩
      rw [hχ, planeLabel_swap, planeLabel_swap, vectorWeight_partner, vectorWeight_partner]
      abel
    exact (h (by simp [X, Matrix.single_apply, h₁, h₂'])).elim
  · intro he
    rw [he, pairTangentMatrix_zero] at h1
    exact zero_ne_one (α := k) (by simpa using h1)

set_option maxHeartbeats 650000 in
private theorem pair_roots_eq (h₂ : (2 : k) = 0) :
    (fun χ => characterCoordinates n (Additive.ofMul χ)) '' absoluteRoots (coordinatePairTorus n h₂) =
      roots n := by
  classical
  ext m
  constructor
  · rintro ⟨χ, ⟨hχ, v, hv, hn⟩, rfl⟩
    have hm : pairTangentMatrix v ≠ 0 := fun h => hn (pairTangentMatrix_injective
      (h.trans pairTangentMatrix_zero.symm))
    obtain ⟨i, j, hij⟩ : ∃ i j, pairTangentMatrix v i j ≠ 0 := by
      by_contra! h
      exact hm (Matrix.ext h)
    have he := character_of_tangent_entry h₂ hv hij
    apply (roots_iff_entries _).mpr
    refine ⟨i, j, ?_, ?_, he⟩
    · rintro rfl
      rw [sub_self, ← (characterCoordinates (k := k) n).map_zero] at he
      exact hχ (congrArg Additive.toMul ((characterCoordinates (k := k) n).injective he))
    · rintro rfl
      exact hij (pairTangentMatrix_opposite_zero h₂ v j)
  · intro hm
    obtain ⟨i, j, hij, hip, rfl⟩ := (roots_iff_entries _).mp hm
    let χ : Character (coordinatePairTorus n h₂).group :=
      Additive.toMul ((characterCoordinates (k := k) n).symm (vectorWeight i - vectorWeight j))
    have hχ : characterCoordinates n (Additive.ofMul χ) = vectorWeight i - vectorWeight j :=
      (characterCoordinates n).apply_symm_apply _
    refine ⟨χ, ⟨?_, ?_⟩, hχ⟩
    · intro h
      have hz : characterCoordinates n (Additive.ofMul χ) = 0 := by
        rw [h]
        exact (characterCoordinates (k := k) n).map_zero
      exact hij (vectorWeight_injective (sub_eq_zero.mp (hχ.symm.trans hz)))
    rcases cases_pairLabel i with rfl | ⟨a, rfl⟩
    · rcases cases_pairLabel j with rfl | ⟨b, rfl⟩
      · exact (hij rfl).elim
      · exact short_root_vector h₂ χ b hχ
    rcases cases_pairLabel j with rfl | ⟨b, rfl⟩
    · apply short_root_vector h₂ χ a.swap
      rw [hχ, planeLabel_swap, vectorWeight_partner]
      change vectorWeight (planeLabel a) - 0 = 0 - -vectorWeight (planeLabel a)
      abel
    · exact long_root_vector h₂ χ a b (fun hab => hip
        ((congrArg planeLabel hab).trans (planeLabel_swap b))) hχ

end RootWeights

section AttachedCoroots

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup AffineAlgebraicGroup)
open Specs.AbstractPairing (Datum Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (absoluteRoots pairing characterValue)
open Specs.Arithmetic.OddSpinOrthogonalRootDatum (Index partner diagonalUnit roots corootPairs coordinate)
open private vectorWeight vectorWeight_isAxis IsAxis markedCoroot monomial monomial_vectorWeight
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalRootDatum
open private characterCoordinates cocharacterCoordinates characterCoordinates_evaluation
  pairing_coordinates torusPointsToUnits orthogonalTorusModel_comm
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
open private pointConj constantPoint comp_pointConj comp_constantPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing

variable {k : Type u} [Field k] {n : ℕ}

private theorem pair_normalizer_preserves_weights (h₂ : (2 : k) = 0)
    (s : (coordinatePairTorus n h₂).group ≅ (coordinatePairTorus n h₂).group)
    (g : 𝟙_ (SchemeOver k) ⟶ (markedScheme k n).X)
    (hg : (s.hom ≫ (coordinatePairTorus n h₂).inclusion).hom.hom =
      pointConj g (coordinatePairTorus n h₂).inclusion.hom.hom)
    (j : Index.{u} n) (χ : Character (coordinatePairTorus n h₂).group)
    (hχ : characterCoordinates n (Additive.ofMul χ) = vectorWeight j) :
    ∃ i : Index.{u} n, characterCoordinates n (Additive.ofMul (s.inv ≫ χ)) = vectorWeight i := by
  let T := coordinatePairTorus n h₂
  let B := fieldAlgebra k
  let b : GroupPoints (markedScheme k n) B := constantPoint g _
  let A := pairMatrix B b
  obtain ⟨i, hi⟩ : ∃ i, A i j ≠ 0 := by
    by_contra! h
    have he : pairMatrix B b⁻¹ * A = 1 := by
      rw [show A = pairMatrix B b from rfl, ← pairMatrix_mul, inv_mul_cancel, pairMatrix_one]
    have hz : (pairMatrix B b⁻¹ * A) j j = 0 := by simp [Matrix.mul_apply, h]
    rw [he, Matrix.one_apply_eq] at hz
    exact one_ne_zero hz
  refine ⟨i, pairCharacterCoordinates_of_eval h₂ (s.inv ≫ χ) _ ?_⟩
  intro R t
  let u : GroupPoints T.group R := t ≫ s.inv.hom.hom
  let G : GroupPoints (markedScheme k n) R := constantPoint g _
  let x : GroupPoints (markedScheme k n) R := t ≫ T.inclusion.hom.hom
  let y : GroupPoints (markedScheme k n) R := u ≫ T.inclusion.hom.hom
  have hcomp : u ≫ (s.hom ≫ T.inclusion).hom.hom = x := by
    change (t ≫ s.inv.hom.hom) ≫ (s.hom ≫ T.inclusion).hom.hom = _
    rw [Category.assoc]
    change t ≫ (s.inv ≫ s.hom ≫ T.inclusion).hom.hom = x
    rw [s.inv_hom_id_assoc]
  rw [hg, comp_pointConj] at hcomp
  change G * y * G⁻¹ = x at hcomp
  have hp : x * G = G * y := by rw [← hcomp, inv_mul_cancel_right]
  have h := congrArg (pairMatrix R) hp
  rw [pairMatrix_mul, pairMatrix_mul, show pairMatrix R x = _ from pairMatrix_diagonal h₂ R t,
    show pairMatrix R y = _ from pairMatrix_diagonal h₂ R u] at h
  have hG : pairMatrix R G = (algebraMap k R).mapMatrix A := by
    let f : B ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have hf : mapPoints f b = G := comp_constantPoint g _
    exact (congrArg (pairMatrix R) hf).symm.trans (pairMatrix_natural f b)
  rw [hG] at h
  have he := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) R => M i j) h
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply] at he
  rw [mul_comm (algebraMap k R (A i j))] at he
  have hweights := ((isUnit_iff_ne_zero.mpr hi).map (algebraMap k R)).mul_left_inj.mp he
  have hc : characterValue (s.inv ≫ χ) R t = characterValue χ R u := by
    unfold characterValue u
    congr 2
  rw [hc, characterCoordinates_evaluation, hχ]
  change (monomial (torusPointsToUnits n R u) (vectorWeight j) : R) = _
  rw [monomial_vectorWeight, monomial_vectorWeight]
  exact hweights.symm

local instance (h₂ : (2 : k) = 0) : IsCommMonObj (coordinatePairTorus n h₂).group.X :=
  orthogonalTorusModel_comm n

private theorem pair_attached_reflection (h₂ : (2 : k) = 0)
    (D : Datum (coordinatePairTorus n h₂)) (α : Root (coordinatePairTorus n h₂)) :
    let a := characterCoordinates n (Additive.ofMul α.val)
    let c := cocharacterCoordinates n (D.rootDatum.coroot α)
    (∑ i, a i * c i) = 2 ∧ ∀ i, IsAxis (coordinate n i - c i • a) := by
  dsimp only
  obtain ⟨C, cochar, hC, hcochar, D', E, hDE, Q, F, P, A, xpos, xneg, hpos, hneg,
    hscalarpos, hscalarneg, reflection, hr⟩ := D.attached α
  have hc : Additive.ofMul reflection.coroot = D.rootDatum.coroot α := congrArg Additive.ofMul hr
  refine ⟨?_, ?_⟩
  · rw [← hc, ← pairing_coordinates]
    exact reflection.root_pairing
  · intro i
    let χ : Character (coordinatePairTorus n h₂).group :=
      Additive.toMul ((characterCoordinates (k := k) n).symm (coordinate n i))
    have hχ : characterCoordinates n (Additive.ofMul χ) = coordinate n i :=
      (characterCoordinates n).apply_symm_apply _
    let j : Index.{u} n := ⟨.inl (.inl i)⟩
    obtain ⟨l, hl⟩ := pair_normalizer_preserves_weights h₂ reflection.conjugation
      reflection.representative reflection.conjugates j χ hχ
    have h := congrArg (fun a : Character (coordinatePairTorus n h₂).group =>
      characterCoordinates n (Additive.ofMul a)) (reflection.reflection χ)
    change _ = characterCoordinates n (Additive.ofMul χ +
      (-pairing (coordinatePairTorus n h₂).group χ reflection.coroot) • Additive.ofMul α.val) at h
    rw [hl, map_add, map_smul, hχ, pairing_coordinates, hχ, hc] at h
    have he : (∑ j, coordinate n i j * cocharacterCoordinates n (D.rootDatum.coroot α) j) =
        cocharacterCoordinates n (D.rootDatum.coroot α) i := by
      simp [coordinate, Pi.single_apply, ite_mul]
    rw [he, neg_smul, ← sub_eq_add_neg] at h
    rw [← h]
    exact vectorWeight_isAxis l

private theorem pair_isTypeBDatum (h₂ : (2 : k) = 0)
    (D : Datum (coordinatePairTorus n h₂)) :
    Specs.Arithmetic.OddSpinAwayFromTwo.IsTypeBDatum n (coordinatePairTorus n h₂) D
      (characterCoordinates n) (cocharacterCoordinates n) := by
  have hr := pair_roots_eq (n := n) h₂
  refine ⟨pairing_coordinates n, hr, ?_⟩
  rw [Set.image_univ]
  change Set.range (fun α : Root (coordinatePairTorus n h₂) =>
    (characterCoordinates n (Additive.ofMul α.val), cocharacterCoordinates n (D.rootDatum.coroot α))) =
      corootPairs n
  ext ⟨a, c⟩
  constructor
  · rintro ⟨α, he⟩
    rw [← he]
    obtain ⟨hp, haxis⟩ := pair_attached_reflection h₂ D α
    exact (markedCoroot hp haxis _).mpr ⟨hr ▸ ⟨α.val, α.property, rfl⟩, rfl⟩
  · intro h
    have ha : a ∈ Specs.Arithmetic.OddSpinOrthogonalRootDatum.roots n := by
      rcases h with (⟨i, ⟨he, _⟩ | ⟨he, _⟩⟩ | ⟨i, j, hij, _, he⟩)
      · exact Or.inl ⟨i, Or.inl he⟩
      · exact Or.inl ⟨i, Or.inr he⟩
      · exact Or.inr ⟨i, j, hij, he⟩
    obtain ⟨χ, hχ, he⟩ := hr.symm ▸ ha
    let α : Root (coordinatePairTorus n h₂) := ⟨χ, hχ⟩
    refine ⟨α, Prod.ext he ?_⟩
    obtain ⟨hp, haxis⟩ := pair_attached_reflection h₂ D α
    apply ((markedCoroot hp haxis c).mp ?_).2
    change (characterCoordinates n (Additive.ofMul χ), c) ∈ corootPairs n
    exact (congrArg (fun b => (b, c) ∈ corootPairs n) he).mpr h

private theorem pair_typeBDatum (h₂ : (2 : k) = 0) (hn : 0 < n) :
    ∃ D : Datum (coordinatePairTorus n h₂),
      Specs.Arithmetic.OddSpinAwayFromTwo.IsTypeBDatum n (coordinatePairTorus n h₂) D
        (characterCoordinates n) (cocharacterCoordinates n) := by
  obtain ⟨_, _, _, _, _, _, hred⟩ := pairGeometry n h₂
  obtain ⟨_, ⟨D⟩⟩ := RootData.AbstractPairing.abstractPairing (pairAlgebraicGroup n k)
    (hred hn) (coordinatePairTorus n h₂) (coordinatePairTorus_split n h₂)
    (coordinatePairTorus_maximal n h₂)
  exact ⟨D, pair_isTypeBDatum h₂ D⟩

end AttachedCoroots

section AdjointPair

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.CartesianMonoidalCategory
open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup AffineAlgebraicGroup)
open Specs.GeometricRadicals (IsSemisimple identitySubgroup)
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private torusPointsToUnits torusPointsToUnits_natural characterCoordinates cocharacterCoordinates
  characterCoordinates_evaluation cocharacterExponents_point orthogonalTorusModel_comm
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
open private diagonalGL_action from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer

variable {k : Type u} [Field k] (n : ℕ)

private theorem pair_identity_is_centre (h₂ : (2 : k) = 0) :
    Specs.CentralTorus.IsSchemeCentre (identitySubgroup (pairAlgebraicGroup n k)) := by
  intro Y g
  constructor
  · intro h
    rw [pair_centre_trivial n h₂ Y g h]
    exact ⟨1, MonObj.one_comp _⟩
  · rintro ⟨x, rfl⟩
    have h : x = 1 := isTerminalTensorUnit.hom_ext _ _
    rw [h, MonObj.one_comp]
    exact (centralizes_iff _ _).mpr (fun U p q ↦ by rw [MonObj.comp_one]; exact Commute.one_left _)

private theorem pair_semisimple (h₂ : (2 : k) = 0) (hn : 0 < n) :
    IsSemisimple (pairAlgebraicGroup n k) := by
  have hred := (pairGeometry n h₂).2.2.2.2.2.2 hn
  apply (Reductive.CentralDerived.semisimpleIffFiniteCentre _ hred _
    (pair_identity_is_centre n h₂)).mpr
  change IsFinite (𝟙 (Spec (CommRingCat.of k)))
  infer_instance

set_option maxHeartbeats 650000 in
theorem pairRootDatum : PairRootDatum.{u} := by
  intro k _ n h₂ hn
  let O := pairAlgebraicGroup n k
  let P := SpGroup (k := k) n
  let p := pairProjection n h₂
  let T := coordinatePairTorus n h₂
  obtain ⟨D, hD⟩ := pair_typeBDatum (n := n) h₂ hn
  refine ⟨O, P, p, markedSchemePoints k n, symplecticSchemePoints n,
    pairProjection_represents n h₂, rfl, pair_semisimple n h₂ hn, pair_centre_trivial n h₂, T,
    coordinatePairTorus_split n h₂, coordinatePairTorus_maximal n h₂, torusPointsToUnits n, ?_, ?_, ?_⟩
  · intro R S f a i
    exact congrFun (torusPointsToUnits_natural n f a) i
  · intro R a x
    change oddMatrixAction (markedSchemePoints k n R
      (a ≫ (coordinatePairTorus n h₂).inclusion.hom.hom)).val x = _
    rw [coordinatePairTorus_points]
    exact diagonalGL_action _ _
  · exact ⟨orthogonalTorusModel_comm n, D, characterCoordinates n, cocharacterCoordinates n, hD,
      fun R a χ => characterCoordinates_evaluation n χ R a,
      fun R z c i => cocharacterExponents_point n c R z i⟩

end AdjointPair

section SpinTorusTwo

set_option backward.isDefEq.respectTransparency false
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct
open Specs.Arithmetic.OddSpinAwayFromTwo (liftTorus)
open Specs.Arithmetic.OddSpinCharTwoStabilizer (ambientForm diagonalOddVector)
open Specs.GeometricRadicals (IsSplitTorus IsSemisimple)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open Albert.SpinSpecification (coefficientMap ScalarClifford)
open private ambientGroupScheme ambientStabilizer ambientStabilizerInclusion ambientPointValues
  ambientBasis ambientCliffordEquiv ambientCoefficients ambientCoefficients_apply nativeStabilizerValue
  nativeStabilizerValue_injective diagonalRestrictionFibre diagonalLift diagonalLift_natural
  restrictionToMarked restriction_flat_surjective restriction_finite restriction_radicial
  actualScalarRestrictionKernel stabilizerRing_smooth StabilizerRing markedVector restriction_geometricallyConnected
  stabScheme_affine cocharacter_of_underlying_lift scaledDiagUnit_unique
  diagonalMarked diagonalGL diagonalGL_action equal_of_radicial_composites
  transportedCoefficients_scalar from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
open private spinUnitPoints_represents from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private torusPointsToUnits spinTorusParameters spinTorusParameters_natural
  spinTorusProjection_points spinTorusOrthogonalPoints_eval mapLiftedTorus liftTorus_norm
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open LinearAlgebraicGroups.StandardGroups (tensorLaurentEquiv)
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

variable {k : Type u} [Field k] (m : ℕ)

private abbrev restriction (h₂ : (2 : k) = 0) :=
  restrictionToMarked k (m + 1) h₂

private abbrev spinProjectionTwo := OddSpinAwayFromTwo.spinTorusProjection (k := k) m

private theorem nativeStabilizerValue_natural {S T : TestAlgebra k} (f : S ⟶ T)
    (a : SchemePoints (ambientStabilizer k (m + 1)) S) :
    nativeStabilizerValue (m + 1) (mapPoints f a) =
      Units.map (ambientCoefficients (m + 1) f.hom).toMonoidHom (nativeStabilizerValue (m + 1) a) := by
  let n := m + 1
  let i := ambientStabilizerInclusion k n
  let q := ambientForm k n
  apply Units.ext
  change ambientCliffordEquiv k T n (ambientPointValues k n T ((mapPoints f a) ≫ i.hom.hom)).val =
    ambientCoefficients n f.hom (ambientCliffordEquiv k S n (ambientPointValues k n S (a ≫ i.hom.hom)).val)
  rw [ambientCoefficients_apply]
  have h := (spinUnitPoints_represents q (ambientBasis k n)).2 f (a ≫ i.hom.hom)
  exact congrArg (fun x : (ScalarClifford q T)ˣ => ambientCliffordEquiv k T n x.val)
    (by simpa only [Category.assoc] using h)

private abbrev scaledLift {S : TestAlgebra k} (z : liftTorus (R := S) (m + 1)) :=
  Units.map (algebraMap S (CliffordAlgebra (ambientForm S (m + 1)))).toMonoidHom z.val.2 *
    diagonalLift (m + 1) z.val.1

private theorem scaledLift_natural {S T : TestAlgebra k}
    (f : S ⟶ T) (z : liftTorus (R := S) (m + 1)) :
    Units.map (ambientCoefficients (m + 1) f.hom).toMonoidHom (scaledLift m z) =
      scaledLift m (mapLiftedTorus (m + 1) f z) := by
  unfold scaledLift
  rw [map_mul, ← diagonalLift_natural]
  congr 1
  apply Units.ext
  change ambientCoefficients (m + 1) f.hom (algebraMap S _ (z.val.2 : S)) =
    algebraMap T _ (f.hom (z.val.2 : S))
  exact transportedCoefficients_scalar _ _ _ _ _ _

private theorem normTorusPoint_exists (h₂ : (2 : k) = 0) (S : TestAlgebra k)
    (z : liftTorus (R := S) (m + 1)) :
    ∃ a : SchemePoints (ambientStabilizer k (m + 1)) S,
      nativeStabilizerValue (m + 1) a = scaledLift m z ∧
      ∀ x, oddMatrixAction (markedSchemePoints k (m + 1) S
        (a ≫ (restriction m h₂).hom.hom)).val x = diagonalOddVector z.val.1 x := by
  have hz : (z.val.2 : S) ^ 2 * ∏ j, (z.val.1 j : S) = 1 := by
    have h := congrArg (Units.val : Sˣ → S) (liftTorus_norm z)
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_one] using h
  exact ((diagonalRestrictionFibre (m + 1) h₂ S z.val.1).2.2.2 z.val.2 hz).exists

private def normTorusPoint (h₂ : (2 : k) = 0) (S : TestAlgebra k)
    (z : liftTorus (R := S) (m + 1)) :=
  (normTorusPoint_exists m h₂ S z).choose

private theorem normTorusPoint_value (h₂ : (2 : k) = 0) (S : TestAlgebra k)
    (z : liftTorus (R := S) (m + 1)) :
    nativeStabilizerValue (m + 1) (normTorusPoint m h₂ S z) = scaledLift m z :=
  (normTorusPoint_exists m h₂ S z).choose_spec.1

private theorem normTorusPoint_natural (h₂ : (2 : k) = 0) {S T : TestAlgebra k}
    (f : S ⟶ T) (z : liftTorus (R := S) (m + 1)) :
    mapPoints f (normTorusPoint m h₂ S z) = normTorusPoint m h₂ T (mapLiftedTorus (m + 1) f z) := by
  apply nativeStabilizerValue_injective (m + 1) T
  rw [nativeStabilizerValue_natural, normTorusPoint_value, normTorusPoint_value, scaledLift_natural]

private theorem normTorusPoint_restriction (h₂ : (2 : k) = 0) (S : TestAlgebra k)
    (z : liftTorus (R := S) (m + 1)) :
    markedSchemePoints k (m + 1) S (normTorusPoint m h₂ S z ≫ (restriction m h₂).hom.hom) =
      diagonalMarked z.val.1 := by
  apply Subtype.ext
  apply (oddMatrixAction (R := S)).injective
  apply LinearEquiv.ext
  intro x
  change _ = oddMatrixAction (diagonalGL z.val.1) x
  rw [diagonalGL_action]
  exact (normTorusPoint_exists m h₂ S z).choose_spec.2 x

private abbrev coordinateTorusRing (k : Type u) [Field k] (n : ℕ) :=
  Specs.StandardGroups.LaurentPowerCoordinates k (PlaneIndex.{u} n)

private def spinTorusInclusionOver (h₂ : (2 : k) = 0) :
    (coordinateTorus (k := k) (m + 1)).val.X ⟶ (ambientStabilizer k (m + 1)).X :=
  normTorusPoint m h₂ (CommAlgCat.of k (coordinateTorusRing k (m + 1)))
    (spinTorusParameters m _ (𝟙 _))

private theorem spinTorusInclusionOver_points (h₂ : (2 : k) = 0) (S : TestAlgebra k)
    (a : SchemePoints (coordinateTorus (k := k) (m + 1)).val S) :
    a ≫ spinTorusInclusionOver m h₂ = normTorusPoint m h₂ S (spinTorusParameters m S a) := by
  let B := CommAlgCat.of k (coordinateTorusRing k (m + 1))
  let E := algSpec (CommRingCat.of k)
  let b : SchemePoints (coordinateTorus (k := k) (m + 1)).val B := 𝟙 _
  let f : B ⟶ S := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage a).unop
  have hf : E.map f.op = a := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage a
  have hfa : mapPoints f b = a := by
    change E.map f.op ≫ 𝟙 _ = a
    rwa [Category.comp_id]
  calc
    _ = mapPoints f (normTorusPoint m h₂ B (spinTorusParameters m B b)) := by
      change a ≫ spinTorusInclusionOver m h₂ = E.map f.op ≫ _
      rw [hf]
      rfl
    _ = _ := by rw [normTorusPoint_natural, ← spinTorusParameters_natural, hfa]

set_option maxHeartbeats 650000 in
private theorem spinTorusInclusionOver_restriction (h₂ : (2 : k) = 0) :
    spinTorusInclusionOver m h₂ ≫ (restriction m h₂).hom.hom =
    (spinProjectionTwo m).hom.hom ≫ (coordinatePairTorus (m + 1) h₂).inclusion.hom.hom := by
  let n := m + 1
  let q := spinProjectionTwo (k := k) m
  let T := coordinatePairTorus n h₂
  let i := spinTorusInclusionOver m h₂
  let f := restriction m h₂
  apply hom_ext_of_points (coordinateTorus (k := k) n).property.1
  intro S a
  change a ≫ i ≫ f.hom.hom = a ≫ q.hom.hom ≫ T.inclusion.hom.hom
  rw [← Category.assoc, ← Category.assoc]
  let o := markedSchemePoints k n S
  apply o.injective
  have hl : o ((a ≫ i) ≫ f.hom.hom) = diagonalMarked (spinTorusParameters m S a).val.1 :=
    (congrArg (fun b => o (b ≫ f.hom.hom)) (spinTorusInclusionOver_points m h₂ S a)).trans
      (normTorusPoint_restriction m h₂ S (spinTorusParameters m S a))
  have hq : torusPointsToUnits n S (a ≫ q.hom.hom) = (spinTorusParameters m S a).val.1 :=
    (congrArg (torusPointsToUnits n S) (spinTorusProjection_points m S a)).trans
      (spinTorusOrthogonalPoints_eval m S a)
  have hR : o ((a ≫ q.hom.hom) ≫ T.inclusion.hom.hom) = diagonalMarked (spinTorusParameters m S a).val.1 :=
    (coordinatePairTorus_points n h₂ S (a ≫ q.hom.hom)).trans (congrArg diagonalMarked hq)
  exact hl.trans hR.symm

private theorem coordinateTorus_product_reduced (n : ℕ) :
    IsReduced (((coordinateTorus (k := k) n).val.X ⊗ (coordinateTorus (k := k) n).val.X).left) := by
  let A := coordinateTorusRing k n
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  change IsReduced (pullback f f)
  let e := pullbackSpecIso k A A
  let t := tensorLaurentEquiv k (PlaneIndex.{u} n) (PlaneIndex.{u} n)
  haveI : IsDomain (A ⊗[k] A) := t.toRingEquiv.toMulEquiv.isDomain _
  haveI : IsReduced (Spec (CommRingCat.of (A ⊗[k] A))) := inferInstance
  exact isReduced_of_isOpenImmersion e.hom

private theorem exists_spinTorusInclusion (h₂ : (2 : k) = 0) :
    ∃ j : (coordinateTorus (k := k) (m + 1)).val ⟶ ambientStabilizer k (m + 1),
      j.hom.hom = spinTorusInclusionOver m h₂ := by
  let f := restriction m h₂
  haveI : UniversallyInjective f.hom.hom.left := restriction_radicial k _ h₂
  haveI : IsFinite f.hom.hom.left := restriction_finite k _ h₂
  haveI := coordinateTorus_product_reduced (k := k) (m + 1)
  let a := spinProjectionTwo (k := k) m ≫ (coordinatePairTorus (m + 1) h₂).inclusion
  obtain ⟨j, hj⟩ := cocharacter_of_underlying_lift (f := f) a (spinTorusInclusionOver m h₂)
    (spinTorusInclusionOver_restriction m h₂)
  have he := congrArg (fun g : (coordinateTorus (k := k) (m + 1)).val ⟶ markedScheme k (m + 1) =>
      g.hom.hom) hj
  change j.hom.hom ≫ f.hom.hom = _ at he
  refine ⟨j, ?_⟩
  apply Over.OverMorphism.ext
  haveI : IsReduced (coordinateTorus (k := k) (m + 1)).val.X.left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of (coordinateTorusRing k (m + 1)))))
  have hh := he.trans (spinTorusInclusionOver_restriction m h₂).symm
  exact equal_of_radicial_composites f.hom.hom.left _ _
    (congrArg Over.Hom.left hh)

private def spinTorusInclusionTwo (h₂ : (2 : k) = 0) := (exists_spinTorusInclusion m h₂).choose

private theorem spinTorusInclusionTwo_points (h₂ : (2 : k) = 0) (S : TestAlgebra k)
    (a : SchemePoints (coordinateTorus (k := k) (m + 1)).val S) :
    a ≫ (spinTorusInclusionTwo m h₂).hom.hom = normTorusPoint m h₂ S (spinTorusParameters m S a) := by
  rw [show (spinTorusInclusionTwo m h₂).hom.hom = spinTorusInclusionOver m h₂ from
    (exists_spinTorusInclusion m h₂).choose_spec]
  exact spinTorusInclusionOver_points m h₂ S a

end SpinTorusTwo

section SpinTorusPullback

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open Specs.Arithmetic.OddSpinAwayFromTwo (liftTorus)
open Specs.Arithmetic.OddSpinCharTwoStabilizer (ambientForm diagonalOddVector)
open Specs.GeometricRadicals (IsSplitTorus IsSemisimple)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open private ambientStabilizer nativeStabilizerValue nativeStabilizerValue_injective
  diagonalRestrictionFibre diagonalLift restriction_flat_surjective restriction_finite stabScheme_affine
  StabilizerRing ambientBasis markedVector stabilizerRing_smooth restriction_geometricallyConnected
  stabScheme_finitePresentation
  actualScalarRestrictionKernel scaledDiagUnit_unique diagonalMarked diagonalGL diagonalGL_action
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
open private torusPointsToUnits spinTorusParameters spinTorusProjection_points spinTorusOrthogonalPoints_eval
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

variable {k : Type u} [Field k] (m : ℕ)

private theorem affine_pullback_of_points {A B C D : SchemeOver k}
    [IsAffine A.left] [IsAffine B.left] [IsAffine C.left] [IsAffine D.left]
    (f : A ⟶ B) (g : A ⟶ C) (i : B ⟶ D) (j : C ⟶ D)
    (comm : f ≫ i = g ≫ j)
    (h : ∀ (S : TestAlgebra k) (x : Points B S) (y : Points C S),
      x ≫ i = y ≫ j → ∃! a : Points A S, a ≫ f = x ∧ a ≫ g = y) :
    IsPullback f g i j := by
  let P := pullback i j
  have hp : IsPullback (pullback.fst i j) (pullback.snd i j) i j := IsPullback.of_hasPullback i j
  let F := Over.forget (Spec (CommRingCat.of k))
  haveI : IsAffine (F.obj B) := inferInstanceAs (IsAffine B.left)
  haveI : IsAffine (F.obj C) := inferInstanceAs (IsAffine C.left)
  haveI : IsAffine (F.obj D) := inferInstanceAs (IsAffine D.left)
  have hAff : IsAffine P.left := IsAffine.of_isPullback (F.map_isPullback hp)
  let u := hp.lift f g comm
  have hu₁ : u ≫ pullback.fst i j = f := hp.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd i j = g := hp.lift_snd _ _ _
  obtain ⟨V, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hAff
  obtain ⟨c, ⟨hc₁, hc₂⟩, _⟩ := h V.unop (e.hom ≫ pullback.fst i j) (e.hom ≫ pullback.snd i j)
    (by simpa only [Category.assoc] using congrArg (e.hom ≫ ·) hp.w)
  let v := e.inv ≫ c
  have hv₁ : v ≫ f = pullback.fst i j := by
    change (e.inv ≫ c) ≫ f = _
    rw [Category.assoc, hc₁, Iso.inv_hom_id_assoc]
  have hv₂ : v ≫ g = pullback.snd i j := by
    change (e.inv ≫ c) ≫ g = _
    rw [Category.assoc, hc₂, Iso.inv_hom_id_assoc]
  have huv : u ≫ v = 𝟙 A := by
    apply hom_ext_of_points (show IsAffine A.left from inferInstance)
    intro S a
    obtain ⟨b, _, hb⟩ := h S (a ≫ f) (a ≫ g)
      (by simpa only [Category.assoc] using congrArg (a ≫ ·) comm)
    rw [Category.comp_id]
    refine (hb (a ≫ u ≫ v) ⟨?_, ?_⟩).trans (hb a ⟨rfl, rfl⟩).symm
    · simp only [Category.assoc, hv₁]
      exact congrArg (a ≫ ·) hu₁
    · simp only [Category.assoc, hv₂]
      exact congrArg (a ≫ ·) hu₂
  have hvu : v ≫ u = 𝟙 P := by
    apply hp.hom_ext
    · simp only [Category.assoc, hu₁, hv₁, Category.id_comp]
    · simp only [Category.assoc, hu₂, hv₂, Category.id_comp]
  exact IsPullback.of_iso_pullback ⟨comm⟩ ⟨u, v, huv, hvu⟩ hu₁ hu₂

set_option maxRecDepth 1700 in
set_option maxHeartbeats 650000 in
private theorem spinTorusTwo_pullbackPoints (h₂ : (2 : k) = 0) (S : TestAlgebra k)
    (a : SchemePoints (coordinateTorus (k := k) (m + 1)).val S)
    (b : SchemePoints (ambientStabilizer k (m + 1)) S)
    (h : a ≫ (coordinatePairTorus (m + 1) h₂).inclusion.hom.hom =
      b ≫ (restriction m h₂).hom.hom) :
    ∃! c : SchemePoints (coordinateTorus (k := k) (m + 1)).val S,
      c ≫ (spinProjectionTwo m).hom.hom = a ∧
      c ≫ (spinTorusInclusionTwo m h₂).hom.hom = b := by
  let n := m + 1
  let t := torusPointsToUnits n S a
  let E := spinTorusParameters m S
  have hb : ∀ x, oddMatrixAction (markedSchemePoints k n S
      (b ≫ (restriction m h₂).hom.hom)).val x = diagonalOddVector t x := by
    intro x
    rw [← h, coordinatePairTorus_points]
    exact diagonalGL_action t x
  obtain ⟨u, ⟨hu, hv⟩, _⟩ := ((diagonalRestrictionFibre n h₂ S t).2.2.1 b).mp hb
  have hz : u ^ 2 * (∏ j, t j) = 1 := by
    apply Units.ext
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_one] using hu
  let z : liftTorus (R := S) n := ⟨(t, u), hz⟩
  let c := E.symm z
  have hc : E c = z := E.apply_symm_apply z
  have he (a' : SchemePoints (coordinateTorus (k := k) n).val S) :
      torusPointsToUnits n S (a' ≫ (spinProjectionTwo m).hom.hom) = (E a').val.1 := by
    rw [spinTorusProjection_points, spinTorusOrthogonalPoints_eval]
  have hv' (a' : SchemePoints (coordinateTorus (k := k) n).val S) :
      nativeStabilizerValue n (a' ≫ (spinTorusInclusionTwo m h₂).hom.hom) = scaledLift m (E a') := by
    rw [spinTorusInclusionTwo_points, normTorusPoint_value]
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · apply (torusPointsToUnits n S).injective
    exact (he c).trans (congrArg (fun s => s.val.1) hc)
  · apply nativeStabilizerValue_injective n S
    rw [hv' c, hc]
    exact hv.symm
  · rintro a' ⟨h₁, h₂'⟩
    apply E.injective
    rw [hc]
    have ht : (E a').val.1 = t := (he a').symm.trans (congrArg (torusPointsToUnits n S) h₁)
    have hn : scaledLift m (E a') = scaledLift m z := (hv' a').symm.trans
      ((congrArg (nativeStabilizerValue n) h₂').trans hv)
    change Units.map (algebraMap S (CliffordAlgebra (ambientForm S n))).toMonoidHom (E a').val.2 *
      diagonalLift n (E a').val.1 = _ at hn
    rw [ht] at hn
    exact Subtype.ext (Prod.ext ht (scaledDiagUnit_unique n (diagonalLift n t) _ u hn))

private theorem spinTorusTwo_pullback (h₂ : (2 : k) = 0) :
    IsPullback (spinProjectionTwo (k := k) m).hom.hom (spinTorusInclusionTwo m h₂).hom.hom
      (coordinatePairTorus (m + 1) h₂).inclusion.hom.hom (restriction m h₂).hom.hom := by
  have := (coordinateTorus (k := k) (m + 1)).property.1
  have := (pairAlgebraicGroup (m + 1) k).property.1
  have := stabScheme_affine (ambientForm k (m + 1)) (ambientBasis k (m + 1)) (markedVector k (m + 1))
  apply affine_pullback_of_points
  · rw [show (spinTorusInclusionTwo m h₂).hom.hom = spinTorusInclusionOver m h₂ from
      (exists_spinTorusInclusion m h₂).choose_spec]
    exact (spinTorusInclusionOver_restriction m h₂).symm
  · exact spinTorusTwo_pullbackPoints m h₂

private abbrev stabilizerAlgebraicGroup (k : Type u) [Field k] (n : ℕ) : AffineAlgebraicGroup k :=
  ⟨ambientStabilizer k n, stabScheme_affine (ambientForm k n) (ambientBasis k n) (markedVector k n),
    (letI := stabScheme_finitePresentation (ambientForm k n) (ambientBasis k n) (markedVector k n)
     inferInstance), by
      change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k
        (StabilizerRing (ambientForm k n) (ambientBasis k n) (markedVector k n)))))
      infer_instance⟩

private def spinTorusTwo (h₂ : (2 : k) = 0) :
    ClosedSubgroup (stabilizerAlgebraicGroup k (m + 1)).val :=
  ⟨(coordinateTorus (m + 1)).val, spinTorusInclusionTwo m h₂, by
    have h := (Over.forget (Spec (CommRingCat.of k))).map_isPullback (spinTorusTwo_pullback m h₂)
    exact MorphismProperty.of_isPullback h (coordinatePairTorus (m + 1) h₂).isClosedImmersion⟩

private theorem spinTorusTwo_restriction (h₂ : (2 : k) = 0) :
    IsTorusRestriction (restriction m h₂) (T := spinTorusTwo m h₂)
      (S := coordinatePairTorus (m + 1) h₂) (spinProjectionTwo m) := by
  have h := spinTorusTwo_pullback m h₂
  have h' := (Over.forget (Spec (CommRingCat.of k))).map_isPullback h
  have hf := restriction_flat_surjective k (m + 1) h₂
  exact ⟨Grp.hom_ext _ _ h.w, MorphismProperty.of_isPullback h'.flip hf.1,
    MorphismProperty.of_isPullback h'.flip hf.2⟩

end SpinTorusPullback

section SplitSpinTwo

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open Specs.GeometricRadicals (IsSemisimple IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.AbstractPairing (Datum)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLatticeOf)
open Specs.Arithmetic.OddSpinCharTwoStabilizer (ambientForm)
open private ambientStabilizer restriction_flat_surjective restriction_finite restriction_radicial
  ambientStabilizerInclusion ambientPointValues restriction_geometricallyConnected
  StabilizerRing ambientBasis markedVector stabilizerRing_smooth actualScalarRestrictionKernel
  diagonalGL_action from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
open private torusPointsToUnits spinTorusParameters spinTorusProjection_points spinTorusOrthogonalPoints_eval
  semisimple_of_finite_cover geometricallyMaximal_of_full_torus_preimage centre_of_cover
  map_corootLattice_of_isogeny marked_corootLattice_eq spinProjection_cocharacter_injective
  spinProjection_exponents orthogonalTorusModel_comm characterCoordinates cocharacterCoordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private pushCocharacters from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

variable {k : Type u} [Field k] (m : ℕ)

private theorem spinTwo_isogeny (h₂ : (2 : k) = 0) : IsCentralIsogeny (restriction m h₂) := by
  obtain ⟨M, hM, Z, j, hZ, hc, _⟩ := actualScalarRestrictionKernel (m + 1) h₂
  have h := restriction_flat_surjective k (m + 1) h₂
  exact ⟨restriction_finite k (m + 1) h₂, h.1, h.2, Z, hZ, hc⟩

private theorem spinTwo_semisimple (h₂ : (2 : k) = 0) :
    IsSemisimple (stabilizerAlgebraicGroup k (m + 1)) := by
  let n := m + 1
  let Q := ambientForm k n
  let b := ambientBasis k n
  let r := markedVector k n
  have hs : Smooth (ambientStabilizer k n).X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (StabilizerRing Q b r))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (stabilizerRing_smooth k n h₂ (Nat.succ_pos m)))
  have ho := pair_semisimple n h₂ (Nat.succ_pos m)
  have hh := restriction_geometricallyConnected k n h₂ ho.2.1
  exact semisimple_of_finite_cover (G := stabilizerAlgebraicGroup k n)
    (H := pairAlgebraicGroup n k) (restriction m h₂) (spinTwo_isogeny m h₂) hs hh ho

private theorem spinTorusTwo_split (h₂ : (2 : k) = 0) : IsSplitTorus (spinTorusTwo m h₂).group :=
  ⟨m + 1, ⟨Iso.refl _⟩⟩

private theorem spinTorusTwo_maximal (h₂ : (2 : k) = 0) : IsGeometricallyMaximal (spinTorusTwo m h₂) := by
  let n := m + 1
  let O := pairAlgebraicGroup n k
  let H := stabilizerAlgebraicGroup k n
  let T := coordinatePairTorus n h₂
  let U := spinTorusTwo m h₂
  have hO := (pairGeometry n h₂).2.2.2.2.2.2 (Nat.succ_pos m)
  have hTC := Reductive.TorusCentralizer.maximalTorusCentralizer O hO T
    (isTorus_of_split (coordinatePairTorus_split n h₂)) (coordinatePairTorus_maximal n h₂)
  have hC := LinearAlgebraicGroups.centralizerSchemeBaseChange k (AlgebraicClosure k) T.inclusion T hTC
  exact geometricallyMaximal_of_full_torus_preimage (G := H) (H := O) (U := U) (T := T)
    (spinTorusTwo_split m h₂) (restriction m h₂) (spinProjectionTwo m)
    (spinTorusTwo_restriction m h₂) (spinTorusTwo_pullback m h₂) hC

private theorem spinTwo_simplyConnected (h₂ : (2 : k) = 0) :
    GeometricallySimplyConnected (stabilizerAlgebraicGroup k (m + 1)) := by
  let n := m + 1
  let H := stabilizerAlgebraicGroup k n
  let O := pairAlgebraicGroup n k
  let T := coordinatePairTorus n h₂
  let U := spinTorusTwo m h₂
  let f := restriction m h₂
  let q := spinProjectionTwo (k := k) m
  have hH := spinTwo_semisimple m h₂
  have hOr : IsReductive O := (pairGeometry n h₂).2.2.2.2.2.2 (Nat.succ_pos m)
  have hHr := reductive_of_semisimple H hH
  have hUs := spinTorusTwo_split m h₂
  have hUm := spinTorusTwo_maximal m h₂
  have hTs := coordinatePairTorus_split n h₂
  have hTm := coordinatePairTorus_maximal n h₂
  haveI : IsCommMonObj T.group.X := orthogonalTorusModel_comm n
  obtain ⟨D, hD⟩ := pair_typeBDatum (n := n) h₂ (Nat.succ_pos m)
  obtain ⟨cU, ⟨E⟩⟩ := RootData.AbstractPairing.abstractPairing H hHr U hUs hUm
  let Y := cocharacterCoordinates (k := k) n
  let push : Additive (Cocharacter U.group) →ₗ[ℤ] (Fin n → ℤ) := Y.toLinearMap.comp (pushCocharacters q)
  have hinj : Function.Injective push := by
    intro a b hab
    exact congrArg Additive.ofMul
      (spinProjection_cocharacter_injective (k := k) m (congrArg Additive.toMul (Y.injective hab)))
  have hRange : LinearMap.range push = evenSum (Fin n) :=
    SetLike.coe_injective (spinProjection_exponents (k := k) m)
  have hMap := map_corootLattice_of_isogeny hHr hOr hUs hUm hTs hTm f
    (spinTwo_isogeny m h₂) q (spinTorusTwo_restriction m h₂) E D
  have hLat := marked_corootLattice_eq (Nat.succ_pos m) D (characterCoordinates n) Y hD
  have hCoroot : (corootLatticeOf E).map push = evenSum (Fin n) :=
    (Submodule.map_comp (pushCocharacters q) Y.toLinearMap _).trans
      ((congrArg (Submodule.map Y.toLinearMap) hMap).trans hLat)
  have hFull : corootLatticeOf E = ⊤ :=
    (Submodule.map_injective_of_injective hinj)
      (hCoroot.trans (hRange.symm.trans (Submodule.map_top push).symm))
  exact (Classification.SimplyConnectedLattice.latticeCriterion H hH U hUs hUm E).mpr hFull

end SplitSpinTwo


section QuadraticAction

set_option backward.isDefEq.respectTransparency false
open CliffordAlgebra
open scoped TensorProduct
open Albert.SpinSpecification (ScalarClifford vectors spinUnits reversion evenPart coefficientMap conjugate IsVectorAction)
open Albert.CliffordSpecification (coefficientForm)
open Specs.Arithmetic.OddSpinCharTwoStabilizer (oddBasis OddIndex OddModule MarkedIsometries oddMatrixAction)
open private oddCoordinates oddCoordinates_preserves oddCoordinates_change oddMatrixAction_apply oddApply_map
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
open private cliffordEquiv cliffordEquiv_vector cliffordEquiv_even changeModule changeCoefficients_vector
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel
open private map_isometry_reverse map_isometry_evenOdd from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

variable {k : Type u} [Field k] (n : ℕ)

set_option maxRecDepth 1500 in
private def pairLinear (S : TestAlgebra k) :
    SchemePoints (markedScheme k n) S →*
      ((S ⊗[k] OddModule k n) ≃ₗ[S] (S ⊗[k] OddModule k n)) where
  toFun a :=
    let c := oddCoordinates k S n
    c.trans ((oddMatrixAction (markedSchemePoints k n S a).val).trans c.symm)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change (oddCoordinates k S n).symm
      (oddMatrixAction (markedSchemePoints k n S 1).val (oddCoordinates k S n x)) = x
    rw [map_one]
    change (oddCoordinates k S n).symm (oddMatrixAction 1 (oddCoordinates k S n x)) = x
    rw [map_one]
    exact (oddCoordinates k S n).symm_apply_apply x
  map_mul' a b := by
    apply LinearEquiv.ext
    intro x
    change (oddCoordinates k S n).symm
      (oddMatrixAction (markedSchemePoints k n S (a * b)).val (oddCoordinates k S n x)) =
      (oddCoordinates k S n).symm (oddMatrixAction (markedSchemePoints k n S a).val
        (oddCoordinates k S n ((oddCoordinates k S n).symm
          (oddMatrixAction (markedSchemePoints k n S b).val (oddCoordinates k S n x)))))
    rw [LinearEquiv.apply_symm_apply, map_mul]
    change (oddCoordinates k S n).symm
      (oddMatrixAction ((markedSchemePoints k n S a).val * (markedSchemePoints k n S b).val)
        (oddCoordinates k S n x)) = _
    rw [map_mul, LinearEquiv.mul_apply]

private theorem pairLinear_preserves (S : TestAlgebra k) (a : SchemePoints (markedScheme k n) S)
    (x : S ⊗[k] OddModule k n) :
    coefficientForm S (markedForm k n) (oddBasis k n) (pairLinear n S a x) =
      coefficientForm S (markedForm k n) (oddBasis k n) x := by
  rw [← oddCoordinates_preserves, ← oddCoordinates_preserves]
  change Specs.Arithmetic.OddSpinCharTwoStabilizer.oddForm S n (oddCoordinates k S n ((oddCoordinates k S n).symm
    (oddMatrixAction (markedSchemePoints k n S a).val (oddCoordinates k S n x)))) =
      Specs.Arithmetic.OddSpinCharTwoStabilizer.oddForm S n (oddCoordinates k S n x)
  rw [LinearEquiv.apply_symm_apply]
  exact (markedSchemePoints k n S a).property.1 _

private theorem pairLinear_natural {S T : TestAlgebra k} (f : S ⟶ T)
    (a : SchemePoints (markedScheme k n) S) (x : S ⊗[k] OddModule k n) :
    changeModule f.hom (pairLinear n S a x) = pairLinear n T (mapPoints f a) (changeModule f.hom x) := by
  apply (oddCoordinates k T n).injective
  rw [oddCoordinates_change]
  have h (S : TestAlgebra k) (a : SchemePoints (markedScheme k n) S) (x : S ⊗[k] OddModule k n) :
      oddCoordinates k S n (pairLinear n S a x) =
        oddMatrixAction (markedSchemePoints k n S a).val (oddCoordinates k S n x) :=
    (oddCoordinates k S n).apply_symm_apply _
  rw [h, h, markedSchemePoints_natural, oddCoordinates_change]
  simp only [oddMatrixAction_apply]
  exact (oddApply_map f.hom.toRingHom (markedSchemePoints k n S a).val.val (oddCoordinates k S n x)).symm

private def pairQuadraticIsometry (S : TestAlgebra k) (a : SchemePoints (markedScheme k n) S) :
    let Q := coefficientForm S (markedForm k n) (oddBasis k n)
    Q.IsometryEquiv Q :=
  ⟨pairLinear n S a, pairLinear_preserves n S a⟩

private def pairCliffordEquiv (S : TestAlgebra k) (a : SchemePoints (markedScheme k n) S) :
    ScalarClifford (markedForm k n) S ≃ₐ[S] ScalarClifford (markedForm k n) S :=
  let e := cliffordEquiv (markedForm k n) S (oddBasis k n)
  (e.trans (equivOfIsometry (pairQuadraticIsometry n S a))).trans e.symm

private theorem pairCliffordEquiv_vectors (S : TestAlgebra k) (a : SchemePoints (markedScheme k n) S)
    (x : S ⊗[k] OddModule k n) :
    pairCliffordEquiv n S a (vectors (markedForm k n) S x) =
      vectors (markedForm k n) S (pairLinear n S a x) := by
  let q := markedForm k n
  let e := cliffordEquiv q S (oddBasis k n)
  apply e.injective
  change e (e.symm (CliffordAlgebra.map (pairQuadraticIsometry n S a).toIsometry
    (e (vectors q S x)))) = _
  rw [AlgEquiv.apply_symm_apply, cliffordEquiv_vector, map_apply_ι, cliffordEquiv_vector]
  rfl

private theorem pairCliffordEquiv_natural {S T : TestAlgebra k} (f : S ⟶ T)
    (a : SchemePoints (markedScheme k n) S) (x : ScalarClifford (markedForm k n) S) :
    coefficientMap (markedForm k n) S f.hom (pairCliffordEquiv n S a x) =
      pairCliffordEquiv n T (mapPoints f a) (coefficientMap (markedForm k n) S f.hom x) := by
  let q := markedForm k n
  let c := coefficientMap q S f.hom
  let F := pairCliffordEquiv n S a
  let G := pairCliffordEquiv n T (mapPoints f a)
  have h : c.comp (F.toAlgHom.restrictScalars k) = (G.toAlgHom.restrictScalars k).comp c := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro s
      change c (F (algebraMap S _ s)) = G (c (algebraMap S _ s))
      rw [F.commutes]
      exact (G.commutes (f.hom s)).symm
    · apply CliffordAlgebra.hom_ext
      apply LinearMap.ext
      intro v
      change c (F (vectors q S (1 ⊗ₜ[k] v))) = G (c (vectors q S (1 ⊗ₜ[k] v)))
      change coefficientMap q S f.hom (pairCliffordEquiv n S a (vectors q S (1 ⊗ₜ[k] v))) =
        pairCliffordEquiv n T (mapPoints f a) (coefficientMap q S f.hom (vectors q S (1 ⊗ₜ[k] v)))
      rw [pairCliffordEquiv_vectors]
      change Albert.SpinFunctor.changeCoefficients q f.hom (vectors q S (pairLinear n S a (1 ⊗ₜ[k] v))) =
        pairCliffordEquiv n T (mapPoints f a)
          (Albert.SpinFunctor.changeCoefficients q f.hom (vectors q S (1 ⊗ₜ[k] v)))
      rw [changeCoefficients_vector, changeCoefficients_vector, pairCliffordEquiv_vectors, pairLinear_natural]
  exact DFunLike.congr_fun h x

private theorem pairCliffordEquiv_reversion (S : TestAlgebra k) (a : SchemePoints (markedScheme k n) S)
    (x : ScalarClifford (markedForm k n) S) :
    pairCliffordEquiv n S a (reversion (markedForm k n) S x) =
      reversion (markedForm k n) S (pairCliffordEquiv n S a x) := by
  let q := markedForm k n
  let b := oddBasis k n
  let e := cliffordEquiv q S b
  let j := CliffordAlgebra.map (pairQuadraticIsometry n S a).toIsometry
  apply e.injective
  rw [show e (reversion q S (pairCliffordEquiv n S a x)) = reverse (e (pairCliffordEquiv n S a x)) from
    baseChangeEquiv_reverse S q b _]
  change e (e.symm (j (e (reversion q S x)))) = reverse (e (e.symm (j (e x))))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    show e (reversion q S x) = reverse (e x) from baseChangeEquiv_reverse S q b x]
  exact map_isometry_reverse _ _

private theorem pairCliffordEquiv_even (S : TestAlgebra k) (a : SchemePoints (markedScheme k n) S)
    {x : ScalarClifford (markedForm k n) S} (hx : x ∈ evenPart (markedForm k n) S) :
    pairCliffordEquiv n S a x ∈ evenPart (markedForm k n) S := by
  let q := markedForm k n
  let b := oddBasis k n
  let e := cliffordEquiv q S b
  let j := CliffordAlgebra.map (pairQuadraticIsometry n S a).toIsometry
  apply (cliffordEquiv_even q S b _).mp
  change e (e.symm (j (e x))) ∈ _
  rw [AlgEquiv.apply_symm_apply]
  exact map_isometry_evenOdd _ ((cliffordEquiv_even q S b x).mpr hx)

private theorem pairCliffordEquiv_spin (S : TestAlgebra k) (p : SchemePoints (markedScheme k n) S)
    {a : (ScalarClifford (markedForm k n) S)ˣ} (ha : a ∈ spinUnits (markedForm k n) S) :
    Units.map (pairCliffordEquiv n S p).toMonoidHom a ∈ spinUnits (markedForm k n) S := by
  let q := markedForm k n
  let g := pairLinear n S p
  let F := pairCliffordEquiv n S p
  have hr (c : (ScalarClifford q S)ˣ)
      (hc : Set.MapsTo (conjugate q S c) (LinearMap.range (vectors q S)) (LinearMap.range (vectors q S))) :
      Set.MapsTo (conjugate q S (Units.map F.toMonoidHom c))
        (LinearMap.range (vectors q S)) (LinearMap.range (vectors q S)) := by
    rintro y ⟨x, rfl⟩
    obtain ⟨w, hw⟩ := hc (LinearMap.mem_range_self (vectors q S) (g.symm x))
    refine ⟨g w, ?_⟩
    have hF (y) : F (vectors q S y) = vectors q S (g y) := pairCliffordEquiv_vectors n S p y
    rw [← hF w, hw]
    have he := hF (g.symm x)
    rw [g.apply_symm_apply] at he
    rw [← he]
    simp only [conjugate, map_mul, Units.coe_map]
    rfl
  rcases ha with ⟨he, hn, h₁, h₂⟩
  refine ⟨pairCliffordEquiv_even n S p he, ?_, hr a h₁, ?_⟩
  · change reversion q S (pairCliffordEquiv n S p a.val) * pairCliffordEquiv n S p a.val = 1
    rw [← pairCliffordEquiv_reversion, ← map_mul, hn, map_one]
  · rw [← map_inv]
    exact hr a⁻¹ h₂

private theorem pairCliffordEquiv_conjugates (S : TestAlgebra k) (p : SchemePoints (markedScheme k n) S)
    (a : (ScalarClifford (markedForm k n) S)ˣ)
    (h : IsVectorAction (markedForm k n) S a (pairLinear n S p))
    (x : ScalarClifford (markedForm k n) S) :
    pairCliffordEquiv n S p x = conjugate (markedForm k n) S a x := by
  let q := markedForm k n
  let e := cliffordEquiv q S (oddBasis k n)
  let F := pairCliffordEquiv n S p
  let g : ScalarClifford q S →ₐ[S] ScalarClifford q S :=
    { toFun := conjugate q S a
      map_one' := by simp [conjugate]
      map_zero' := by simp [conjugate]
      map_add' x y := by simp [conjugate, mul_add, add_mul]
      map_mul' x y := by simp [conjugate, mul_assoc, ← mul_assoc (a⁻¹).val a.val (y * (a⁻¹).val)]
      commutes' s := by
        change a.val * algebraMap S _ s * (a⁻¹).val = algebraMap S _ s
        rw [← Algebra.commutes s a.val, mul_assoc, Units.mul_inv, mul_one] }
  have he : F.toAlgHom.comp e.symm.toAlgHom = g.comp e.symm.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro y
    change F (e.symm (CliffordAlgebra.ι _ y)) = g (e.symm (CliffordAlgebra.ι _ y))
    have hv : e.symm (CliffordAlgebra.ι _ y) = vectors q S y :=
      e.symm_apply_eq.mpr (cliffordEquiv_vector q S (oddBasis k n) y).symm
    rw [hv]
    exact (pairCliffordEquiv_vectors n S p y).trans (h y)
  have hh : F (e.symm (e x)) = g (e.symm (e x)) := DFunLike.congr_fun he (e x)
  rw [e.symm_apply_apply] at hh
  exact hh

private def pairCliffordAction : QuadraticCliffordAction (markedForm k n) (oddBasis k n) (markedScheme k n) where
  linear := pairLinear n
  preserves := pairLinear_preserves n
  natural := pairLinear_natural n
  clifford := pairCliffordEquiv n
  generators := pairCliffordEquiv_vectors n
  clifford_natural := pairCliffordEquiv_natural n
  preservesSpin R p _ := pairCliffordEquiv_spin n R p
  conjugates := pairCliffordEquiv_conjugates n

end QuadraticAction

section SimplyConnectedPair

set_option backward.isDefEq.respectTransparency false
open Specs.GeometricRadicals (IsSemisimple)
open private actualScalarRestrictionKernel restriction_radicial diagonalGL_action
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
open private centre_of_cover orthogonalTorusModel_comm torusPointsToUnits spinTorusParameters
  spinTorusProjection_points spinTorusOrthogonalPoints_eval characterCoordinates cocharacterCoordinates
  marked_corootLattice_eq spinProjection_cocharacter_injective spinProjection_exponents
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo

set_option maxHeartbeats 900000 in
set_option maxRecDepth 1700 in
theorem pairSplitSpin : PairSplitSpin.{u} := by
  intro k _ n h₂ hn
  rcases n with _ | m
  · exact (Nat.not_lt_zero _ hn).elim
  let n := m + 1
  let H := stabilizerAlgebraicGroup k n
  let O := pairAlgebraicGroup n k
  let P := SpGroup (k := k) n
  let f := restriction m h₂
  let p := pairProjection n h₂
  let T := coordinatePairTorus n h₂
  let U := spinTorusTwo m h₂
  let q := spinProjectionTwo (k := k) m
  have hf := spinTwo_isogeny m h₂
  have : Flat f.hom.hom.left := hf.2.1
  have : Surjective f.hom.hom.left := hf.2.2.1
  have hn : 0 < n := Nat.succ_pos m
  obtain ⟨M, hM, Z, j, hZ, hc, _⟩ := actualScalarRestrictionKernel n h₂
  have hCentre := centre_of_cover f hZ hc (pair_centre_trivial n h₂)
  obtain ⟨D, hD⟩ := pair_typeBDatum (n := n) h₂ hn
  refine ⟨H, O, P, f, p, intrinsicStabilizerPoints n h₂, markedSchemePoints k n, symplecticSchemePoints n,
    pairProjection_represents n h₂, rfl, intrinsicStabilizer_represents n h₂,
    spinTwo_semisimple m h₂, spinTwo_simplyConnected m h₂, pair_semisimple n h₂ hn,
    hf, restriction_radicial k n h₂, ⟨pairCliffordAction n, fun _ _ => rfl⟩, intrinsicStabilizer_action n h₂, ⟨M, Z, hM, ⟨j⟩, hZ, hCentre⟩,
    T, U, q, coordinatePairTorus_split n h₂, coordinatePairTorus_maximal n h₂,
    spinTorusTwo_split m h₂, spinTorusTwo_maximal m h₂, spinTorusTwo_restriction m h₂,
    spinTorusTwo_pullback m h₂, torusPointsToUnits n, spinTorusParameters m, ?_, ?_, ?_⟩
  · intro R a x
    change oddMatrixAction (markedSchemePoints k n R
      (a ≫ (coordinatePairTorus n h₂).inclusion.hom.hom)).val x = _
    rw [coordinatePairTorus_points]
    exact diagonalGL_action _ _
  · intro R a
    exact ((congrArg (torusPointsToUnits n R) (spinTorusProjection_points m R a)).trans
      (spinTorusOrthogonalPoints_eval m R a)).symm
  · exact ⟨orthogonalTorusModel_comm n, D, characterCoordinates n, cocharacterCoordinates n, hD,
      marked_corootLattice_eq hn D _ _ hD, spinProjection_cocharacter_injective m,
      spinProjection_exponents m⟩

end SimplyConnectedPair

section Approximation

open Specs.Arithmetic.IsotropicSpinGeneration (IsIsotropic)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.OddSpinInnerDescent

set_option backward.isDefEq.respectTransparency false in
theorem typeBDescentApproximation : TypeBDescentApproximation.{u, v} := by
  classical
  intro k S V I _ _ _ _ _ _ _ _ L P D l J E n simple q₀ b₀ g₀ A G i hc hs hq hd hg
  have ho : Odd (Module.finrank k V) := by
    rw [hd]
    exact ⟨n + 1, rfl⟩
  have hinner := OddSpinInnerDescent.typeBInnerDisplacement E n simple hc hs G i
  obtain ⟨K, d, a, q, g, _, _, _, _, _, _, hreg, hfin, hdim, hspin, _⟩ :=
    OddSpinInnerDescent.effectiveOddSpinDescent q₀ b₀ P.pair.G G J E.toExactSequence
      g₀ A i hq ho hg hinner
  letI : Module.Finite k a.fixed := hfin
  letI : Module.Free k a.fixed := Module.Free.of_divisionRing k a.fixed
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank k a.fixed))) k a.fixed :=
    (Module.finBasis k a.fixed).reindex Equiv.ulift.symm
  let g' : ∀ R : TestAlgebra k, Specs.AdjointRepresentation.GroupPoints G.val R →* (Albert.SpinSpecification.ScalarClifford q R)ˣ := g
  have hiso (c : Cocharacter G.val) (h : IsNoncentral c) : IsIsotropic q :=
    by
      have aux : SpinCocharacterIsotropy.{u} := @OddSpinInnerDescent.spinCocharacterIsotropy.{u}
      unfold SpinCocharacterIsotropy at aux
      have hh := @aux k (↥a.fixed) (ULift.{u} (Fin (Module.finrank k a.fixed))) _ _ _ _ _ q b G
      exact hh g' hreg hspin c h
  refine ⟨a.fixed, inferInstance, inferInstance, hfin, q, g, hdim.trans hd, hreg, hspin, hiso, ?_⟩
  rintro F hsimple ⟨c, hc⟩
  have aux : Specs.Arithmetic.IsotropicSpinGeneration.GlobalSpinApproximation.{u, v} :=
    @IsotropicSpinGeneration.globalSpinApproximation.{u, v}
  unfold Specs.Arithmetic.IsotropicSpinGeneration.GlobalSpinApproximation at aux
  have hh := @aux k _ F (↥a.fixed) _ _ hfin q G
  exact hh g' hspin hreg (hiso c hc) hsimple

end Approximation

section SpinDatumComparison

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped TensorProduct

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open Specs.Arithmetic.OddSpinModels
open Specs.AbstractPairing (Datum Root)
open Specs.Arithmetic.OddSpinAwayFromTwo (corootPairs IsTypeBDatum)
open Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction characterPullback)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.CharacterPairing (pairing)
open Specs.SimplyConnectedLattice (corootLatticeOf)
open Specs.Pinning (AttachedDatum SplitBorelPair)

open private pushCocharacters
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private marked_corootLattice_eq map_corootLattice_of_isogeny
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo

variable {k : Type u} [Field k]

/-- The central isogeny transports the paired roots to the even-sum cocharacter lattice. -/
private theorem spin_marking_of_cover {n : ℕ}
    {H O : AffineAlgebraicGroup k} (hH : IsReductive H) (hO : IsReductive O)
    {U : ClosedSubgroup H.val} {T : ClosedSubgroup O.val}
    [IsCommMonObj U.group.X] [IsCommMonObj T.group.X]
    (hUs : IsSplitTorus U.group) (hUm : IsGeometricallyMaximal U)
    (hTs : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (p : H.val ⟶ O.val) (hp : IsCentralIsogeny p)
    (q : U.group ⟶ T.group) (hq : IsTorusRestriction p q)
    (D : Datum T) (E : Datum U)
    (X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
    (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ))
    (hD : IsTypeBDatum n T D X Y)
    (hinj : Function.Injective (fun c : Cocharacter U.group => c ≫ q))
    (hrange : Set.range (fun c : Cocharacter U.group => Y (Additive.ofMul (c ≫ q))) =
      evenSum (Fin n)) :
    Nonempty (SimplyConnectedTypeBMarking n E) := by
  obtain ⟨_, _, hroots, hcoroots⟩ :=
    Classification.CentralIsogenies.centralIsogenyComparison H O hH hO U T
      hUs hUm hTs hTm p q hp hq.1 hq.2.2
  let j : Root T ≃ Root U := hroots.equiv
  let coords (β : Root T) :=
    (X (Additive.ofMul β.val), Y (D.rootDatum.coroot β))
  have hcoords : Set.range coords = corootPairs n := by
    rw [← Set.image_univ]
    exact hD.2.2
  let i : Root T ≃ ↥(corootPairs n) :=
    Equiv.ofBijective (fun β => ⟨coords β, hcoords ▸ Set.mem_range_self β⟩) ⟨by
      intro a b he
      apply Subtype.ext
      exact Additive.ofMul.injective (X.injective (congrArg (fun w => w.val.1) he)),
      by
        intro a
        have ha : a.val ∈ Set.range coords := hcoords.symm ▸ a.property
        obtain ⟨b, hb⟩ := ha
        exact ⟨b, Subtype.ext hb⟩⟩
  let F := Y.toLinearMap.comp (pushCocharacters q)
  have hF : Function.Injective F := fun _ _ h =>
    congrArg Additive.ofMul (hinj (congrArg Additive.toMul (Y.injective h)))
  have hFrange : LinearMap.range F = evenSum (Fin n) := SetLike.coe_injective hrange
  let C := (LinearEquiv.ofInjective F hF).trans
    (LinearEquiv.ofEq (LinearMap.range F) (evenSum (Fin n)) hFrange)
  have hc (a : Additive (Cocharacter U.group)) : (C a).val = Y (Additive.ofMul (a.toMul ≫ q)) := rfl
  refine ⟨⟨C, j.symm.trans i, ?_, ?_⟩⟩
  · intro a c
    obtain ⟨b, rfl⟩ := j.surjective a
    change E.rootDatum.toLinearMap (E.rootDatum.root (j b)) c =
      ∑ l, ((i (j.symm (j b))).val.1 l) * (C c).val l
    rw [j.symm_apply_apply, hc, E.root_eq]
    change E.rootDatum.toLinearMap (Additive.ofMul (characterPullback q b.val)) c =
      ∑ l, X (Additive.ofMul b.val) l * Y (Additive.ofMul (c.toMul ≫ q)) l
    calc
      _ = pairing U.group (q ≫ b.val) c.toMul :=
        E.pairing_eq (q ≫ b.val) c.toMul
      _ = pairing T.group b.val (c.toMul ≫ q) := by
        unfold pairing Specs.CharacterDescent.compositionPairing
        rw [Category.assoc]
      _ = _ := hD.1 _ _
  · intro a
    obtain ⟨b, rfl⟩ := j.surjective a
    change (C (E.rootDatum.coroot (j b))).val = (i (j.symm (j b))).val.2
    rw [j.symm_apply_apply, hc]
    exact congrArg (Y ∘ Additive.ofMul)
      ((hcoroots b.val b.property (j b).property).2 _ _ (E.attached (j b)) (D.attached b))

private theorem cocharacter_push_injective {G O : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {T : ClosedSubgroup O.val}
    [IsCommMonObj U.group.X] (E : Datum U) (q : U.group ⟶ T.group)
    (hindex : Finite (Character U.group ⧸ (characterPullback q).range)) :
    Function.Injective (fun c : Cocharacter U.group => c ≫ q) := by
  intro c d h
  apply Additive.ofMul.injective
  apply E.rootDatum.flip.toLinearMap.toPerfPair.injective
  ext x
  let χ := x.toMul
  let M := (characterPullback q).range
  have hN : (M.index : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr M.index_ne_zero_of_finite
  obtain ⟨ψ, hψ⟩ := M.pow_index_mem χ
  have hpair (c : Cocharacter U.group) :
      E.rootDatum.toLinearMap (Additive.ofMul (characterPullback q ψ)) (Additive.ofMul c) =
        pairing T.group ψ (c ≫ q) := by
    rw [E.pairing_eq]
    change pairing U.group (q ≫ ψ) c = _
    unfold pairing compositionPairing
    rw [Category.assoc]
  have heq := (hpair c).trans ((congrArg (pairing T.group ψ) h).trans (hpair d).symm)
  rw [hψ] at heq
  change E.rootDatum.toLinearMap (M.index • x) (Additive.ofMul c) =
    E.rootDatum.toLinearMap (M.index • x) (Additive.ofMul d) at heq
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at heq
  exact mul_left_cancel₀ hN heq

set_option maxHeartbeats 750000 in
/-- The coroot lattice criterion gives the standard simply connected datum
from the marked adjoint one. -/
theorem typeBMarkingFromAdjoint : TypeBMarkingFromAdjoint.{u} := by
  intro k _ P E n hn hG hs O hO T hTs hTm f hf q hq _ D X Y hD
  letI := E.comm
  obtain ⟨_, hindex, _, _⟩ := Classification.CentralIsogenies.centralIsogenyComparison P.G O
    P.reductive hO P.T T P.split P.maximal hTs hTm f q hf hq.1 hq.2.2
  have hfull := (Classification.SimplyConnectedLattice.latticeCriterion P.G hG P.T P.split
    P.maximal E.datum).mp hs
  have hmap := map_corootLattice_of_isogeny P.reductive hO P.split P.maximal hTs hTm f hf q hq E.datum D
  have heven := marked_corootLattice_eq hn D X Y hD
  let push := Y.toLinearMap.comp (pushCocharacters q)
  have hR : push.range = evenSum (Fin n) := by
    rw [← Submodule.map_top, ← hfull]
    change (corootLatticeOf E.datum).map (Y.toLinearMap.comp (pushCocharacters q)) = _
    rw [Submodule.map_comp, hmap]
    exact heven
  exact spin_marking_of_cover P.reductive hO P.split P.maximal hTs hTm f hf q hq D E.datum X Y hD
    (cocharacter_push_injective E.datum q hindex) (congrArg SetLike.coe hR)


/-- The perfect pairing identifies the full character lattices from the common marks. -/
private def marked_datum_equiv {n : ℕ} {G H : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {V : ClosedSubgroup H.val}
    [IsCommMonObj U.group.X] [IsCommMonObj V.group.X]
    {D : Datum U} {E : Datum V}
    (hD : SimplyConnectedTypeBMarking n D) (hE : SimplyConnectedTypeBMarking n E) :
    D.rootDatum.Equiv E.rootDatum := by
  let y := hD.cocharacters.trans hE.cocharacters.symm
  let x := D.rootDatum.toLinearMap.toPerfPair.trans
    (y.symm.dualMap.trans E.rootDatum.toLinearMap.toPerfPair.symm)
  let i := hD.roots.trans hE.roots.symm
  have hp (a b) : E.rootDatum.toLinearMap (x a) b = D.rootDatum.toLinearMap a (y.symm b) := by
    change (E.rootDatum.toLinearMap.toPerfPair (x a)) b = _
    change (E.rootDatum.toLinearMap.toPerfPair
      (E.rootDatum.toLinearMap.toPerfPair.symm (y.symm.dualMap (D.rootDatum.toLinearMap.toPerfPair a)))) b = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hi (a : Root U) : hE.roots (i a) = hD.roots a := hE.roots.apply_symm_apply _
  have hy (c) : hD.cocharacters (y.symm c) = hE.cocharacters c :=
    hD.cocharacters.apply_symm_apply _
  refine { weightMap := x
           coweightMap := y.symm
           indexEquiv := i
           bijective_weightMap := x.bijective
           bijective_coweightMap := y.symm.bijective
           weight_coweight_transpose := by ext b a; exact hp a b
           root_weightMap := ?_
           coroot_coweightMap := ?_ }
  · funext a
    apply E.rootDatum.toLinearMap.toPerfPair.injective
    ext c
    change E.rootDatum.toLinearMap (x (D.rootDatum.root a)) c =
      E.rootDatum.toLinearMap (E.rootDatum.root (i a)) c
    rw [hp, hD.pairing_eq, hE.pairing_eq, hy, hi]
  · funext b
    apply hD.cocharacters.injective
    apply Subtype.ext
    change (hD.cocharacters (y.symm (E.rootDatum.coroot b))).val =
      (hD.cocharacters (D.rootDatum.coroot (i.symm b))).val
    rw [hy, hE.coroot_eq, hD.coroot_eq]
    exact congrArg (fun a => (hE.roots a).val.2) (i.apply_symm_apply b).symm |>.trans
      (congrArg (fun a : ↥(corootPairs n) => a.val.2) (hi (i.symm b)))

end SpinDatumComparison

section AdjointActionComparison

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped TensorProduct

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup IsSchemeKernel)
open Specs.Fppf (IsFppf)
open Specs.Arithmetic.OddSpinModels
open Specs.Arithmetic.OddSpinInnerDescent (SpinAdjointAction)
open Specs.AutomorphismSequence (AdjointQuotient ExactSequence RelativeAut restrictAut innerAut)
open LinearAlgebraicGroups.Descent.AutomorphismSequence (innerAut_eq_one_iff)
open Albert.SpinSpecification (SchemePoints ScalarClifford IsSpinPointRepresentation IsVectorAction
  spinUnits coefficientMap conjugate)
open private projection_eq_one_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private quotientIsoOfKernel centralizesIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private restrictHom_apply_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent

variable {k : Type u} [Field k]

private abbrev pointHom {G H : GroupScheme k} (a : G ⟶ H) (R : TestAlgebra k) :
    SchemePoints G R →* SchemePoints H R :=
  ((yonedaGrp.map a).app (op ((algSpec (CommRingCat.of k)).obj (op R)))).hom

private theorem cover_isFppf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hfin : IsFinite f) (hflat : Flat f) (hsurj : Surjective f) [IsLocallyNoetherian Y] :
    IsFppf f := by
  exact ⟨hflat, hsurj, inferInstance⟩

private theorem lift_over_affine_cover {H O : AffineAlgebraicGroup k} (p : H.val ⟶ O.val)
    (hf : Flat p.hom.hom.left) (hs : Surjective p.hom.hom.left)
    (T : TestAlgebra k) (z : SchemePoints O.val T) :
    ∃ (B : TestAlgebra k) (g : T ⟶ B) (y : SchemePoints H.val B),
      Epi ((algSpec (CommRingCat.of k)).map g.op) ∧
      y ≫ p.hom.hom = mapPoints g z := by
  let S := algSpec (CommRingCat.of k)
  let v := p.hom.hom
  let W := pullback v z
  let w := pullback.snd v z
  have h := (IsPullback.of_hasPullback v z).map (Over.forget (Spec (CommRingCat.of k)))
  haveI : IsAffine H.val.X.left := H.property.1
  haveI : IsAffine O.val.X.left := O.property.1
  haveI : IsAffine (S.obj (op T)).left := by
    change IsAffine (Spec (CommRingCat.of T))
    infer_instance
  have ha : IsAffine W.left := IsAffine.of_isPullback (show
    IsPullback (pullback.fst v z).left w.left v.left z.left from h)
  obtain ⟨B, ⟨i⟩⟩ := essImage_algSpec.mpr ha
  let ff : S.FullyFaithful := algSpec.fullyFaithful
  let g := (ff.preimage (i.hom ≫ w)).unop
  have hg : S.map g.op = i.hom ≫ w := ff.map_preimage _
  haveI : Flat w.left := MorphismProperty.of_isPullback h hf
  haveI : Surjective w.left := MorphismProperty.of_isPullback h hs
  haveI : Epi w.left := Flat.epi_of_flat_of_surjective w.left
  haveI : Epi w := Over.epi_of_epi_left w
  refine ⟨B.unop, g, i.hom ≫ pullback.fst v z, hg.symm ▸ (inferInstance : Epi (i.hom ≫ w)), ?_⟩
  change (i.hom ≫ pullback.fst v z) ≫ v = S.map g.op ≫ z
  rw [hg, Category.assoc, Category.assoc, pullback.condition]

private theorem adjoint_cover_iso {G H O : AffineAlgebraicGroup k} (e : G.val ≅ H.val)
    (J : AdjointQuotient G) (p : H.val ⟶ O.val) (hp : IsFppf p.hom.hom.left)
    (Z : ClosedSubgroup H.val) (hZ : IsSchemeKernel p Z)
    (hc : RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 H.val) z)) :
    ∃ d : J.quotient.val ≅ O.val, J.projection ≫ d.hom = e.hom ≫ p := by
  let J' : AdjointQuotient H := ⟨Z, hc, O, p, hp, hZ⟩
  apply quotientIsoOfKernel J.projection p e J.fppf hp
  intro S x
  exact (projection_eq_one_iff J x).trans ((innerAut_eq_one_iff x).trans
    ((centralizesIso e x).trans ((innerAut_eq_one_iff _).symm.trans (projection_eq_one_iff J' _).symm)))

set_option maxHeartbeats 750000 in
/-- Compare inner conjugation with the Clifford action after lifting through the cover. -/
private theorem transported_action {G H O : AffineAlgebraicGroup k}
    {V I : Type u} [AddCommGroup V] [Module k V] [LinearOrder I]
    {Q : QuadraticForm k V} {b : Module.Basis I k V}
    (p : H.val ⟶ O.val) (hp : IsFppf p.hom.hom.left)
    (e : G.val ≅ H.val) {J : AdjointQuotient G} {Outer : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}}
    (E : ExactSequence G J Outer)
    (d : J.quotient.val ≅ O.val) (hd : J.projection ≫ d.hom = e.hom ≫ p)
    (h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford Q R)ˣ)
    (hh : IsSpinPointRepresentation Q H.val h) (A : QuadraticCliffordAction Q b O.val)
    (hvec : ∀ (R : TestAlgebra k) (x : SchemePoints H.val R),
      IsVectorAction Q R (h R x) (A.linear R (pointHom p R x))) :
    let g := fun R => (h R).comp (pointHom e.hom R)
    IsSpinPointRepresentation Q G.val g ∧ Nonempty (SpinAdjointAction Q b G J.quotient E.inner g) := by
  let g := fun R => (h R).comp (pointHom e.hom R)
  have hg : IsSpinPointRepresentation Q G.val g := by
    let Z := yonedaGrp.mapIso e
    constructor
    · intro R
      let j := Z.app (op ((algSpec (CommRingCat.of k)).obj (op R)))
      have hj : Function.Bijective j.hom := ConcreteCategory.bijective_of_isIso j.hom
      refine ⟨(hh.1 R).1.comp hj.1, ?_⟩
      change Set.range (h R ∘ j.hom) = _
      rw [hj.2.range_comp, (hh.1 R).2]
    · intro R T f x
      change h T (((algSpec (CommRingCat.of k)).map f.op ≫ x) ≫ e.hom.hom.hom) =
        Units.map (coefficientMap Q R f.hom).toMonoidHom (h R (x ≫ e.hom.hom.hom))
      rw [Category.assoc]
      exact hh.2 f _
  refine ⟨hg, ⟨{
    linear := fun R => (A.linear R).comp (pointHom d.hom R)
    preserves := fun R z x => A.preserves R (pointHom d.hom R z) x
    natural := ?_
    clifford := fun R z => A.clifford R (pointHom d.hom R z)
    generators := fun R z x => A.generators R (pointHom d.hom R z) x
    innerAction := ?_ }⟩⟩
  · intro R T f z x
    have hz : mapPoints f (pointHom d.hom R z) = pointHom d.hom T (mapPoints f z) :=
      (Category.assoc _ _ _).symm
    simpa only [MonoidHom.comp_apply, hz] using A.natural f (pointHom d.hom R z) x
  · intro R T f z x
    let S := algSpec (CommRingCat.of k)
    let u := S.map f.op
    let a : RelativeAut G.val (S.obj (op R)) := E.inner.app (op (S.obj (op R))) ⟨z⟩
    let U := Over.mk u
    let zT : SchemePoints O.val T := pointHom d.hom T (mapPoints f z)
    change g T ((a.asIso.hom.app (op U)).hom x) =
      Units.map (A.clifford T zT).toMonoidHom (g T x)
    let m := g T x
    have hm : m ∈ spinUnits Q T := (hg.1 T).2 ▸ Set.mem_range_self x
    let m' := Units.map (A.clifford T zT).toMonoidHom m
    obtain ⟨x', hx'⟩ := (hg.1 T).2.symm ▸ A.preservesSpin T zT m hm
    change g T x' = m' at hx'
    change g T ((a.asIso.hom.app (op U)).hom x) = m'
    rw [← hx']
    apply congrArg (g T)
    obtain ⟨B, j, y, hj, hy⟩ := lift_over_affine_cover p hp.1 hp.2.1 T zT
    let w := S.map j.op
    let v := w ≫ u
    let W := Over.mk v
    let β : W ⟶ U := Over.homMk w rfl
    have hβ : (a.asIso.hom.app (op W)).hom (w ≫ x) =
        w ≫ (a.asIso.hom.app (op U)).hom x :=
      NatTrans.naturality_apply a.asIso.hom β.op x
    haveI : Epi w := hj
    apply (cancel_epi w).mp
    rw [← hβ]
    let y' : SchemePoints G.val B := pointHom e.inv B y
    have he' : pointHom e.hom B y' = y := by
      change (y ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = y
      rw [Category.assoc, show e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ from
        congrArg (Grp.forget _).map e.inv_hom_id, Category.comp_id]
    have hzB : y' ≫ J.projection.hom.hom = v ≫ z := by
      haveI : Mono d.hom.hom.hom := inferInstanceAs (Mono ((Grp.forget _).map d.hom))
      apply (cancel_mono d.hom.hom.hom).mp
      have hd' := congrArg (Grp.forget (SchemeOver k)).map hd
      change J.projection.hom.hom ≫ d.hom.hom.hom = e.hom.hom.hom ≫ p.hom.hom at hd'
      change _ = (w ≫ u ≫ z) ≫ d.hom.hom.hom
      simp only [Category.assoc]
      rw [hd', ← Category.assoc y', show y' ≫ e.hom.hom.hom = y from he']
      change y ≫ p.hom.hom = w ≫ (u ≫ z) ≫ d.hom.hom.hom at hy
      simpa only [Category.assoc] using hy
    have hres : restrictAut v a = innerAut y' := by
      have hh := NatTrans.naturality_apply E.inner v.op (ULift.up z)
      change E.inner.app (op (S.obj (op B))) ⟨v ≫ z⟩ = restrictAut v a at hh
      rw [← hh, ← hzB, E.onLift]
    have heval : (a.asIso.hom.app (op W)).hom (w ≫ x) = y' * (w ≫ x) * y'⁻¹ := by
      have heq := restrictHom_apply_eq a.asIso (𝟙 (S.obj (op B))) v v (Category.id_comp _) (w ≫ x)
      rw [← heq]
      change ((restrictAut v a).asIso.hom.app (op (Over.mk (𝟙 (S.obj (op B)))))).hom
        (w ≫ x) = _
      rw [hres]
      change ((𝟙 _ ≫ y') * (w ≫ x) * (𝟙 _ ≫ y')⁻¹) = _
      rw [Category.id_comp]
    rw [heval]
    apply (hg.1 B).1
    have hs : g B y' = h B y := congrArg (h B) he'
    have hx : g B (w ≫ x) = Units.map (coefficientMap Q T j.hom).toMonoidHom m := hg.2 j x
    have hx₁ := hg.2 j x'
    change g B (w ≫ x') = Units.map (coefficientMap Q T j.hom).toMonoidHom (g T x') at hx₁
    have hzB' : mapPoints j zT = pointHom p B y := hy.symm
    rw [hx₁, hx', map_mul, map_mul, map_inv, hs, hx]
    apply Units.ext
    have hn := A.clifford_natural j zT m.val
    rw [hzB', A.conjugates B _ (h B y) (hvec B y)] at hn
    exact hn.symm

end AdjointActionComparison

section BasedTypeBRigidity

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped TensorProduct

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open Specs.Arithmetic.OddSpinModels
open Specs.Arithmetic.OddSpinAwayFromTwo (corootPairs coordinate)
open Specs.AbstractPairing (Datum Root)
open Specs.Pinning (AttachedDatum SplitBorelPair BasedIso)
open Specs.BorelsAndChambers (subgroupRoots IsPositiveSystem)

open private basedIso_pos base_isPos_iff_subgroupRoots
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence

variable {k : Type u} [Field k] {n : ℕ}
variable {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
variable {D : Datum T}

private abbrev rootCoordinates (m : SimplyConnectedTypeBMarking n D) (α : Root T) :=
  (m.roots α).val.1

private theorem root_eq_of_coordinates (m : SimplyConnectedTypeBMarking n D) {α β : Root T}
    (h : rootCoordinates m α = rootCoordinates m β) : α = β := by
  apply D.rootDatum.root.injective
  apply D.rootDatum.toLinearMap.toPerfPair.injective
  ext c
  change D.rootDatum.toLinearMap (D.rootDatum.root α) c =
    D.rootDatum.toLinearMap (D.rootDatum.root β) c
  rw [m.pairing_eq, m.pairing_eq]
  exact congrArg (fun w => ∑ i, w i * (m.cocharacters c).val i) h

private theorem root_coordinates_sub (m : SimplyConnectedTypeBMarking n D) {α β delta : Root T}
    (h : rootCoordinates m delta = rootCoordinates m β - rootCoordinates m α) :
    D.rootDatum.root delta = D.rootDatum.root β - D.rootDatum.root α := by
  apply D.rootDatum.toLinearMap.toPerfPair.injective
  ext c
  change D.rootDatum.toLinearMap (D.rootDatum.root delta) c =
    (D.rootDatum.toLinearMap (D.rootDatum.root β - D.rootDatum.root α)) c
  simp only [map_sub, LinearMap.sub_apply, m.pairing_eq, h, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

private def IsShortRoot (m : SimplyConnectedTypeBMarking n D) (α : Root T) : Prop :=
  ∃ i, rootCoordinates m α = coordinate n i ∧
      (m.roots α).val.2 = 2 • coordinate n i ∨
    rootCoordinates m α = -coordinate n i ∧ (m.roots α).val.2 = -(2 • coordinate n i)

private theorem short_root_at (m : SimplyConnectedTypeBMarking n D) (i : Fin n) :
    ∃ α : Root T, rootCoordinates m α = coordinate n i ∧ IsShortRoot m α := by
  let p : ↥(corootPairs n) := ⟨(coordinate n i, 2 • coordinate n i),
    Or.inl ⟨i, Or.inl ⟨rfl, rfl⟩⟩⟩
  let α := m.roots.symm p
  have h : m.roots α = p := m.roots.apply_symm_apply _
  refine ⟨α, congrArg (fun x : ↥(corootPairs n) => x.val.1) h,
    i, Or.inl ⟨congrArg (fun x : ↥(corootPairs n) => x.val.1) h,
      congrArg (fun x : ↥(corootPairs n) => x.val.2) h⟩⟩

private theorem short_root_iff_even (m : SimplyConnectedTypeBMarking n D) (α : Root T) :
    IsShortRoot m α ↔ ∀ β : Root T, Even (D.rootDatum.pairing β α) := by
  have hp (β : Root T) : D.rootDatum.pairing β α =
      ∑ i, (rootCoordinates m β i) * (m.roots α).val.2 i := by
    rw [← RootPairing.root_coroot_eq_pairing, m.pairing_eq, m.coroot_eq]
  constructor
  · rintro ⟨i, ⟨_, hi⟩ | ⟨_, hi⟩⟩ β
    · rw [hp, hi]
      simp [coordinate, Pi.single_apply, Pi.smul_apply]
    · rw [hp, hi]
      simp [coordinate, Pi.single_apply]
  · intro he
    rcases (m.roots α).property with h | ⟨i, j, hij, hc, hr⟩
    · exact h
    · obtain ⟨β, hβ, _⟩ := short_root_at m i
      have he' := he β
      rw [hp, hβ, ← hc] at he'
      rcases hr with hr | hr | hr <;>
        simp [hr, coordinate, Pi.single_apply, hij] at he'

private theorem difference_of_distinct_signed_coordinates (i j : Fin n) (hij : i ≠ j)
    {a b : Fin n → ℤ} (ha : a = coordinate n i ∨ a = -coordinate n i)
    (hb : b = coordinate n j ∨ b = -coordinate n j) :
    (b - a, b - a) ∈ corootPairs n := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inr ⟨j, i, Ne.symm hij, rfl, Or.inl rfl⟩
  · exact Or.inr ⟨j, i, Ne.symm hij, rfl, Or.inr (Or.inr (by abel_nf))⟩
  · exact Or.inr ⟨j, i, Ne.symm hij, rfl, Or.inr (Or.inl (by abel_nf))⟩
  · exact Or.inr ⟨i, j, hij, rfl, Or.inl (by abel_nf)⟩

private theorem finite_strictly_increasing_preserves_value
    {A : Type u} [Finite A] (v : A → ℝ) (f : A → A)
    (h : ∀ a b, v a < v b → v (f a) < v (f b)) (a : A) :
    v (f a) = v a := by
  have nondecreasing (w : A → ℝ)
      (hw : ∀ a b, w a < w b → w (f a) < w (f b)) (a : A) : w a ≤ w (f a) := by
    let r (a b : A) := w a < w b
    letI : IsTrans A r := ⟨fun _ _ _ => lt_trans⟩
    letI : Std.Irrefl r := ⟨fun a => lt_irrefl (w a)⟩
    apply (Finite.wellFounded_of_trans_of_irrefl r).induction a
    intro a ih
    by_contra! ha
    exact (not_lt_of_ge (ih _ ha)) (hw _ _ ha)
  exact le_antisymm (by
    have hw := nondecreasing (fun a => -v a)
      (fun a b hab => neg_lt_neg (h b a (neg_lt_neg_iff.mp hab))) a
    exact neg_le_neg_iff.mp hw) (nondecreasing v h a)

/-- A based automorphism preserves the ordered list of positive short roots. -/
private theorem marked_based_datum_rigid {P : SplitBorelPair k} (E : AttachedDatum P)
    (m : letI := E.comm; SimplyConnectedTypeBMarking n E.datum) (f : Aut E.toBased) :
    f = 1 := by
  classical
  letI := E.comm
  letI := E.datum.finiteRoots
  let P₀ := E.datum.rootDatum
  let s : BasedIso E.toBased E.toBased := f.asIso.hom
  let a : P₀.Equiv P₀ := s.val
  obtain ⟨_, _, _, hc, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity P.G P.reductive P.T P.split P.maximal
  have hsys := hc.1 P.B P.borel P.containsTorus
  have hbase := base_isPos_iff_subgroupRoots E hsys
  obtain ⟨l, hreg, hsign⟩ := hsys
  let v (α : Root P.T) := l (P₀.root α)
  have nz (α : Root P.T) : v α ≠ 0 := by
    simpa only [v, P₀, E.datum.root_eq] using hreg α
  have hp (α : Root P.T) : 0 < v α ↔ E.base.IsPos α := by
    rw [hbase, hsign]
    simp only [Set.mem_ofPred_eq, v, P₀, E.datum.root_eq]
  have hpos (α) (h : 0 < v α) : 0 < v (a.indexEquiv α) :=
    (hp _).mpr (basedIso_pos s α ((hp _).mp h))
  have hshort (α) (h : IsShortRoot m α) : IsShortRoot m (a.indexEquiv α) := by
    apply (short_root_iff_even m _).mpr
    intro β
    obtain ⟨delta, rfl⟩ := a.indexEquiv.surjective β
    rw [a.toHom.pairing]
    exact (short_root_iff_even m α).mp h delta
  let PosShort := {α : Root P.T // IsShortRoot m α ∧ 0 < v α}
  let fpos : PosShort → PosShort := fun α => ⟨a.indexEquiv α.val,
    hshort α.val α.property.1, hpos α.val α.property.2⟩
  have hneg (α β : Root P.T) (h : rootCoordinates m β = -rootCoordinates m α) :
      P₀.root β = -P₀.root α := by
    apply P₀.toLinearMap.toPerfPair.injective
    ext c
    change P₀.toLinearMap (P₀.root β) c = P₀.toLinearMap (-P₀.root α) c
    simp only [P₀, m.pairing_eq, map_neg, LinearMap.neg_apply, h, Pi.neg_apply,
      neg_mul, Finset.sum_neg_distrib]
  have diffRoot (α β : PosShort) (hne : α ≠ β) :
      ∃ delta : Root P.T, P₀.root delta = P₀.root β.val - P₀.root α.val := by
    obtain ⟨i, hi⟩ := α.property.1
    obtain ⟨j, hj⟩ := β.property.1
    have hwα := hi.imp And.left And.left
    have hwβ := hj.imp And.left And.left
    have hij : i ≠ j := by
      rintro rfl
      rcases hwα with hα | hα <;> rcases hwβ with hβ | hβ
      · exact hne (Subtype.ext (root_eq_of_coordinates m (hα.trans hβ.symm)))
      · have he := congrArg l (hneg α.val β.val (by rw [hα, hβ]))
        change v β.val = l (-P₀.root α.val) at he
        rw [map_neg] at he
        exact (not_lt_of_ge (neg_nonpos.mpr α.property.2.le)) (he ▸ β.property.2)
      · have he := congrArg l (hneg β.val α.val (by rw [hα, hβ]))
        change v α.val = l (-P₀.root β.val) at he
        rw [map_neg] at he
        exact (not_lt_of_ge (neg_nonpos.mpr β.property.2.le)) (he ▸ α.property.2)
      · exact hne (Subtype.ext (root_eq_of_coordinates m (hα.trans hβ.symm)))
    let p : ↥(corootPairs n) :=
      ⟨_, difference_of_distinct_signed_coordinates i j hij hwα hwβ⟩
    exact ⟨m.roots.symm p, root_coordinates_sub m
      (congrArg (fun z : ↥(corootPairs n) => z.val.1) (m.roots.apply_symm_apply p))⟩
  have hvinj : Function.Injective (fun α : PosShort => v α.val) := by
    intro α β he
    by_contra hne
    obtain ⟨delta, hdelta⟩ := diffRoot α β hne
    have hzero : v delta = v β.val - v α.val := by simp [v, hdelta]
    change v α.val = v β.val at he
    exact nz delta (by rw [hzero, he, sub_self])
  have froot (α : Root P.T) : a.weightEquiv (P₀.root α) = P₀.root (a.indexEquiv α) :=
    a.toHom.root_weightMap_apply _ _ α
  have hinc (α β : PosShort) (hlt : v α.val < v β.val) :
      v (fpos α).val < v (fpos β).val := by
    have hne : α ≠ β := fun h => (lt_irrefl _ (h ▸ hlt))
    obtain ⟨delta, hdelta⟩ := diffRoot α β hne
    have hdeltapos : 0 < v delta := by
      change 0 < l (P₀.root delta)
      rw [hdelta, map_sub]
      exact sub_pos.mpr hlt
    have hdelta' : P₀.root (a.indexEquiv delta) =
        P₀.root (a.indexEquiv β.val) - P₀.root (a.indexEquiv α.val) := by
      calc
        _ = a.weightEquiv (P₀.root delta) := (froot delta).symm
        _ = a.weightEquiv (P₀.root β.val - P₀.root α.val) := congrArg _ hdelta
        _ = a.weightEquiv (P₀.root β.val) - a.weightEquiv (P₀.root α.val) :=
          a.weightEquiv.toLinearMap.map_sub _ _
        _ = _ := congrArg₂ (· - ·) (froot β.val) (froot α.val)
    have h := hpos delta hdeltapos
    change 0 < l (P₀.root (a.indexEquiv delta)) at h
    rw [hdelta', l.map_sub] at h
    exact sub_pos.mp h
  have hfix (α : PosShort) : a.indexEquiv α.val = α.val :=
    congrArg Subtype.val (hvinj (finite_strictly_increasing_preserves_value
      (fun α : PosShort => v α.val) fpos hinc α))
  have haxis (i : Fin n) : ∃ (α : PosShort) (ε : ℤ), ε ≠ 0 ∧
      rootCoordinates m α.val = ε • coordinate n i := by
    obtain ⟨α, hα, hαs⟩ := short_root_at m i
    rcases lt_or_gt_of_ne (nz α) with h | h
    · let p : ↥(corootPairs n) := ⟨(-coordinate n i, -(2 • coordinate n i)),
        Or.inl ⟨i, Or.inr ⟨rfl, rfl⟩⟩⟩
      let β := m.roots.symm p
      have hb : m.roots β = p := m.roots.apply_symm_apply _
      have hβ : rootCoordinates m β = -coordinate n i := congrArg (fun z => z.val.1) hb
      have hβs : IsShortRoot m β :=
        ⟨i, Or.inr ⟨hβ, congrArg (fun z => z.val.2) hb⟩⟩
      have hv : v β = -v α := by
        change l (P₀.root β) = _
        rw [hneg α β (by rw [hα, hβ]), map_neg]
      exact ⟨⟨β, hβs, hv ▸ neg_pos.mpr h⟩, -1, by decide, by rwa [neg_one_smul]⟩
    · exact ⟨⟨α, hαs, h⟩, 1, by decide, by rwa [one_smul]⟩
  have hdual (c) : a.coweightEquiv c = c := by
    apply m.cocharacters.injective
    apply Subtype.ext
    funext i
    obtain ⟨α, ε, hε, hα⟩ := haxis i
    have hf := a.toLinearMap_weightEquiv (P₀.root α.val) c
    rw [froot, hfix, m.pairing_eq, m.pairing_eq] at hf
    change _ at hf
    simp only [hα, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, coordinate,
      Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hf
    exact (mul_left_cancel₀ hε hf).symm
  have hweight (x) : a.weightEquiv x = x := by
    apply P₀.toLinearMap.toPerfPair.injective
    ext c
    change P₀.toLinearMap (a.weightEquiv x) c = P₀.toLinearMap x c
    rw [a.toLinearMap_weightEquiv, hdual]
  have hind (i : Root P.T) : a.indexEquiv i = i :=
    P₀.root.injective ((froot i).symm.trans (hweight _))
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  change a = (RootPairing.Equiv.id P₀)
  apply RootPairing.Equiv.ext
  · exact LinearMap.ext hweight
  · exact LinearMap.ext hdual
  · exact Equiv.ext hind

end BasedTypeBRigidity

section TypeBForms

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped TensorProduct

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup IsSchemeKernel)
open Specs.Arithmetic.OddSpinModels
open Specs.Arithmetic.OddSpinInnerDescent (SpinAdjointAction)
open Specs.Arithmetic.IsotropicSpinGeneration (IsRegular IsIsotropic GlobalSpinApproximation)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.Pinning (AttachedDatum SplitBorelPair PinnedGroup)
open Specs.AutomorphismSequence (AdjointQuotient ExactSequence SplitSequence relativePoints)
open Specs.RelativeFormComparison (fieldTest transportedAut)
open Specs.AbstractPairing (Datum)
open Specs.Arithmetic.OddSpinAwayFromTwo (IsTypeBDatum)
open Specs.GeometricRadicals (IsSemisimple IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open Albert.SpinSpecification (SchemePoints ScalarClifford IsSpinPointRepresentation IsVectorAction
  ExtendedForm)
open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)

open private splitBorelPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies

variable {k : Type u} [Field k]

private def transport_marking {n : ℕ} {G H : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {V : ClosedSubgroup H.val}
    [IsCommMonObj U.group.X] [IsCommMonObj V.group.X]
    {D : Datum U} {E : Datum V} (e : D.rootDatum.Equiv E.rootDatum)
    (m : SimplyConnectedTypeBMarking n D) : SimplyConnectedTypeBMarking n E where
  cocharacters := e.coweightEquiv.trans m.cocharacters
  roots := e.indexEquiv.symm.trans m.roots
  pairing_eq a y := by
    obtain ⟨b, rfl⟩ := e.indexEquiv.surjective a
    change E.rootDatum.toLinearMap (E.rootDatum.root (e.indexEquiv b)) y =
      ∑ i, (m.roots (e.indexEquiv.symm (e.indexEquiv b))).val.1 i *
        (m.cocharacters (e.coweightEquiv y)).val i
    rw [e.indexEquiv.symm_apply_apply,
      ← e.toHom.root_weightMap_apply D.rootDatum E.rootDatum b]
    exact (e.toLinearMap_weightEquiv _ _).trans (m.pairing_eq _ _)
  coroot_eq a := by
    change (m.cocharacters (e.coweightEquiv (E.rootDatum.coroot a))).val =
      (m.roots (e.indexEquiv.symm a)).val.2
    rw [e.coweightEquiv_apply, e.toHom.coroot_coweightMap_apply]
    exact m.coroot_eq _

set_option maxHeartbeats 900000 in
private theorem descent_with_split_model {S V I : Type u} [Field S] [Algebra k S]
    [IsSepClosure k S] [AddCommGroup V] [Module k V] [Module.Finite k V] [LinearOrder I]
    {P : SplitBorelPair k} (D₀ : AttachedDatum P)
    {n : ℕ} (hn : 0 < n) (m₀ : letI := D₀.comm; SimplyConnectedTypeBMarking n D₀.datum)
    (G : AffineAlgebraicGroup k)
    (i : relativePoints P.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    {J : AdjointQuotient P.G} {Outer : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}}
    (E : ExactSequence P.G J Outer)
    (hinner : ∀ σ, transportedAut k S i σ ∈ (E.inner.app (op (fieldTest k S))).hom.range)
    (Q : QuadraticForm k V) (b : Module.Basis I k V) (hreg : IsRegular Q)
    (hdim : Module.finrank k V = 2 * n + 1)
    {H O : AffineAlgebraicGroup k} (hH : IsSemisimple H) (hsc : GeometricallySimplyConnected H)
    (hO : IsSemisimple O)
    (p : H.val ⟶ O.val) (hp : IsCentralIsogeny p)
    (Z : ClosedSubgroup H.val) (hZ : IsSchemeKernel p Z)
    (hc : RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 H.val) z))
    (h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford Q R)ˣ)
    (hh : IsSpinPointRepresentation Q H.val h) (A : QuadraticCliffordAction Q b O.val)
    (hvec : ∀ (R : TestAlgebra k) (x : SchemePoints H.val R),
      IsVectorAction Q R (h R x) (A.linear R (pointHom p R x)))
    {U : ClosedSubgroup H.val} {T : ClosedSubgroup O.val}
    (hUs : IsSplitTorus U.group) (hUm : IsGeometricallyMaximal U)
    (hTs : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (pT : U.group ⟶ T.group) (hpT : IsTorusRestriction p pT)
    [IsCommMonObj T.group.X] (D : Datum T)
    (X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
    (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ))
    (hD : IsTypeBDatum n T D X Y) :
    OddSpinDescription.{u,v} n G := by
  let P' := splitBorelPair H (reductive_of_semisimple H hH) U hUs hUm
  let D' := Classification.Pinning.attachedDatum P'
  letI := D'.comm
  letI := D₀.comm
  obtain ⟨m'⟩ := typeBMarkingFromAdjoint P' D' n hn hH hsc
    O (reductive_of_semisimple O hO) T hTs hTm p hp pT hpT D X Y hD
  obtain ⟨e⟩ := (((Classification.PinnedEquivalence.pinnedEquivalence.{u}).2 k).2.1 P P' D₀ D').mpr
    ⟨marked_datum_equiv m₀ m'⟩
  haveI : LocallyOfFiniteType O.val.X.hom := O.property.2.1
  haveI : IsLocallyNoetherian O.val.X.left := LocallyOfFiniteType.isLocallyNoetherian O.val.X.hom
  have hfp := cover_isFppf p.hom.hom.left hp.1 hp.2.1 hp.2.2.1
  obtain ⟨d, hd⟩ := adjoint_cover_iso e J p hfp Z hZ hc
  obtain ⟨hg, ⟨action⟩⟩ := transported_action p hfp e E d hd h hh A hvec
  let g := fun R => (h R).comp (pointHom e.hom R)
  have ho : Odd (Module.finrank k V) := hdim ▸ ⟨n, rfl⟩
  obtain ⟨L, _, a, q, spin, _, _, _, _, _, _, hq, hfin, hdim', hspin, _⟩ :=
    OddSpinInnerDescent.effectiveOddSpinDescent Q b P.G G J E g action i hreg ho hg hinner
  letI : Module.Finite k a.fixed := hfin
  letI : Module.Free k a.fixed := Module.Free.of_divisionRing k a.fixed
  let spin' : ∀ R : TestAlgebra k, Specs.AdjointRepresentation.GroupPoints G.val R →*
      (ScalarClifford q R)ˣ := spin
  let b' : Module.Basis (ULift.{u} (Fin (Module.finrank k a.fixed))) k a.fixed :=
    (Module.finBasis k a.fixed).reindex Equiv.ulift.symm
  have hiso (c : Cocharacter G.val) (hnc : IsNoncentral c) : IsIsotropic q := by
    have aux : Specs.Arithmetic.OddSpinInnerDescent.SpinCocharacterIsotropy.{u} :=
      @OddSpinInnerDescent.spinCocharacterIsotropy.{u}
    unfold Specs.Arithmetic.OddSpinInnerDescent.SpinCocharacterIsotropy at aux
    exact (@aux k (↥a.fixed) (ULift.{u} (Fin (Module.finrank k a.fixed))) _ _ _ _ _ q b' G)
      spin' hq hspin c hnc
  refine ⟨a.fixed, inferInstance, inferInstance, hfin, q, spin, hdim'.trans hdim, hq, hspin, hiso, ?_⟩
  rintro F hsimple ⟨c, hnc⟩
  have aux : GlobalSpinApproximation.{u,v} := @IsotropicSpinGeneration.globalSpinApproximation.{u,v}
  unfold GlobalSpinApproximation at aux
  have hh' := @aux k _ F (↥a.fixed) _ _ hfin q G
  exact hh' spin' hspin hq (hiso c hnc) hsimple

private abbrev awayBasis (n : ℕ) (k : Type u) [Field k] :=
  (Specs.Arithmetic.OddSpinAwayFromTwo.basis n k).reindex Equiv.ulift.{u}.symm

private theorem orthogonal_quadratic_action {n : ℕ} {O : AffineAlgebraicGroup k}
    (o : ∀ R : TestAlgebra k, SchemePoints O.val R ≃*
      Specs.Arithmetic.OddSpinAwayFromTwo.specialOrthogonal n R)
    (hnat : Specs.Arithmetic.OddSpinAwayFromTwo.RepresentsSpecialOrthogonal O.val o)
    (hA : Specs.Arithmetic.OddSpinAwayFromTwo.RepresentsCliffordAction O.val o) :
    ∃ A : QuadraticCliffordAction (Specs.Arithmetic.OddSpinAwayFromTwo.form n k)
        (awayBasis n k) O.val,
      ∀ (R : TestAlgebra k) (z : SchemePoints O.val R), A.linear R z = (o R z).val := by
  obtain ⟨C, hC, hCnat⟩ := hA
  refine ⟨{
    linear := fun R => (Specs.Arithmetic.OddSpinAwayFromTwo.specialOrthogonal n R).subtype.comp
      (o R).toMonoidHom
    preserves := ?_
    natural := ?_
    clifford := fun R z => C R z
    generators := ?_
    clifford_natural := ?_
    preservesSpin := ?_
    conjugates := ?_ }, fun _ _ => rfl⟩
  · intro R z x
    let Q := Specs.Arithmetic.OddSpinAwayFromTwo.form n k
    have hf : ExtendedForm Q R (Specs.Arithmetic.OddSpinAwayFromTwo.basis n k) =
        ExtendedForm Q R (awayBasis n k) := by
      apply (Albert.CliffordModel.coefficient_form_unique R Q (awayBasis n k) _).mpr
      intro w
      simpa only [one_mul] using
        Albert.CliffordModel.coefficientForm_tmul R Q (Specs.Arithmetic.OddSpinAwayFromTwo.basis n k) 1 w
    change ExtendedForm Q R (awayBasis n k) ((o R z).val x) = ExtendedForm Q R (awayBasis n k) x
    rw [← hf]
    exact (o R z).property.1 x
  · intro R T f z x
    exact hnat f z x
  · intro R z x
    exact (hC R z).1 x
  · intro R T f z x
    exact hCnat f z x
  · intro R z a
    exact (hC R z).2.1 a
  · intro R z a
    exact (hC R z).2.2 a

set_option maxHeartbeats 1700000 in
private theorem descent_from_marked_split_form {S : Type u} [Field S] [Algebra k S] [IsSepClosure k S]
    (P : SplitBorelPair k) (D : AttachedDatum P)
    (m : ℕ) (mark : letI := D.comm; SimplyConnectedTypeBMarking (m + 1) D.datum)
    (G : AffineAlgebraicGroup k)
    (i : relativePoints P.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S)) :
    OddSpinDescription.{u,v} (m + 1) G := by
  let L := Classification.Pinning.standardAdditiveLine k
  obtain ⟨r, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist L P
  let P' : PinnedGroup L := ⟨P, r, pin⟩
  obtain ⟨D', l, J, E, _, _⟩ := Descent.QuasiSplitInnerForms.automorphismSequences P'
  letI := D.comm
  letI := D'.comm
  obtain ⟨e⟩ := (((Classification.PinnedEquivalence.pinnedEquivalence.{u}).2 k).2.1 P P D D').mp
    ⟨Iso.refl _⟩
  let mark' : SimplyConnectedTypeBMarking (m + 1) D'.datum :=
    transport_marking e mark
  have hinner (σ : Gal(S/k)) : transportedAut k S i σ ∈
      (E.inner.app (op (fieldTest k S))).hom.range := by
    apply (Descent.QuasiSplitInnerForms.splitKernel E _).mp
    exact marked_based_datum_rigid D' mark' _
  let n := m + 1
  have hn : 0 < n := Nat.succ_pos m
  by_cases h₂ : (2 : k) = 0
  · obtain ⟨H, O, _, p, _, h, o, _, _, _, hh, hH, hsc, hO, hp, _, ⟨A, hA⟩, hvec,
      ⟨_, Z, _, _, hZ, hc⟩, T, U, pT, hTs, hTm, hUs, hUm, hpT, _, _, _, _, _,
      comm, DT, X, Y, hDT, _, _, _⟩ := pairSplitSpin k n h₂ hn
    letI := comm
    let Q := Specs.Arithmetic.OddSpinCharTwoStabilizer.oddForm k n
    let b := Specs.Arithmetic.OddSpinCharTwoStabilizer.oddBasis k n
    have hreg : IsRegular Q := by
      obtain ⟨_, _, _, hn, hr⟩ := OddSpinCharTwoStabilizer.splitHyperplane k n h₂
      exact Or.inr ⟨_, hn.symm ▸ one_ne_zero, hr⟩
    have hdim : Module.finrank k (Specs.Arithmetic.OddSpinCharTwoStabilizer.OddModule k n) =
        2 * n + 1 := by
      rw [Module.finrank_eq_card_basis (Pi.basisFun k (Specs.Arithmetic.OddSpinCharTwoStabilizer.OddIndex n))]
      change Fintype.card (Option (Fin n ⊕ Fin n)) = 2 * n + 1
      simp [two_mul]
    refine descent_with_split_model D hn mark G i E.toExactSequence hinner Q b hreg hdim hH hsc hO
      p hp Z hZ hc h hh A ?_ hUs hUm hTs hTm pT hpT DT X Y hDT
    intro R x
    rw [hA]
    exact hvec R x
  · obtain ⟨H, O, p, h, o, _, hA, hh, hnat, hvec, hH, hsc, hO, hp, _, _,
      Z, hZ, _, hc, _, _, T, U, pT, hTs, hTm, hUs, hUm, hpT, _, _, _, _, _, _, _,
      comm, DT, X, Y, hDT, _, _, _, _, _⟩ := OddSpinAwayFromTwo.splitOddSpin k n h₂ hn
    letI := comm
    let Q := Specs.Arithmetic.OddSpinAwayFromTwo.form n k
    let b := awayBasis n k
    obtain ⟨A, hAlin⟩ := orthogonal_quadratic_action o hnat hA
    have hreg : IsRegular Q := Or.inl (LinearMap.ker_eq_bot.mpr (OddSpinAwayFromTwo.perfectPolar n k h₂).1)
    have hdim : Module.finrank k (Specs.Arithmetic.OddSpinAwayFromTwo.Space n k) = 2 * n + 1 := by
      rw [Module.finrank_eq_card_basis b]
      simp [Specs.Arithmetic.OddSpinAwayFromTwo.OddIndices, Specs.Arithmetic.OddSpinAwayFromTwo.Indices,
        two_mul]
    refine descent_with_split_model D hn mark G i E.toExactSequence hinner Q b hreg hdim hH hsc hO
      p hp Z hZ hc h hh A ?_ hUs hUm hTs hTm pT hpT DT X Y hDT
    intro R x
    rw [hAlin]
    exact hvec R x

/-- Every simply connected type-B form has the intrinsic odd spin representation. -/
theorem typeBFormDescent : TypeBFormDescent.{u,v} := by
  intro k _ P D m G hm ⟨S, _, _, _, ⟨e⟩⟩
  obtain ⟨mark⟩ := hm
  obtain ⟨j, _⟩ := Descent.RelativeFormComparison.schemeIsomorphismComparison
    (S := S) P.G.val G.val
  exact descent_from_marked_split_form P D m mark G (j e)

end TypeBForms

section AbsoluteTypeB

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped BigOperators
open Specs.Arithmetic.OddSpinAwayFromTwo (coordinate corootPairs)

private def simpleBRoot {n : ℕ} (i : Fin n) : Fin n → ℤ :=
  if h : i.val + 1 < n then coordinate n i - coordinate n ⟨i.val + 1, h⟩
  else coordinate n i

private def simpleBCoroot {n : ℕ} (i : Fin n) : Fin n → ℤ :=
  if h : i.val + 1 < n then coordinate n i - coordinate n ⟨i.val + 1, h⟩
  else 2 • coordinate n i

private theorem simpleB_mem {n : ℕ} (i : Fin n) :
    (simpleBRoot i, simpleBCoroot i) ∈ corootPairs n := by
  unfold simpleBRoot simpleBCoroot
  split_ifs with h
  · exact Or.inr ⟨i, ⟨i.val + 1, h⟩, fun hi => by
      have he : i.val = i.val + 1 := congrArg Fin.val hi
      omega,
      rfl, Or.inl rfl⟩
  · exact Or.inl ⟨i, Or.inl ⟨rfl, rfl⟩⟩

private def typeBHeight (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] ℤ :=
  ∑ j : Fin n, ((n : ℤ) - j.val) • LinearMap.proj j

private theorem typeBHeight_apply {n : ℕ} (a : Fin n → ℤ) :
    typeBHeight n a = ∑ j, ((n : ℤ) - j.val) * a j := by
  simp [typeBHeight, LinearMap.sum_apply]

@[simp] private theorem typeBHeight_coordinate {n : ℕ} (i : Fin n) :
    typeBHeight n (coordinate n i) = (n : ℤ) - i.val := by
  simp [typeBHeight_apply, coordinate, Pi.single_apply, mul_ite]

private theorem simpleB_height {n : ℕ} (i : Fin n) : typeBHeight n (simpleBRoot i) = 1 := by
  have hi := i.isLt
  unfold simpleBRoot
  split
  all_goals simp
  omega

private theorem typeBHeight_ne_zero {n : ℕ} (a : ↥(corootPairs n)) :
    typeBHeight n a.val.1 ≠ 0 := by
  rcases a with ⟨⟨x, y⟩, h⟩
  change typeBHeight n x ≠ 0
  rcases h with (⟨i, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩) | ⟨i, j, hij, _, rfl | rfl | rfl⟩
  all_goals
    have hi := i.isLt
    try have hj := j.isLt
    try have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [map_add, map_sub, map_neg, typeBHeight_coordinate]
    omega

private def positiveShortB {n : ℕ} (i : Fin n) : ↥(corootPairs n) :=
  ⟨(coordinate n i, 2 • coordinate n i), Or.inl ⟨i, Or.inl ⟨rfl, rfl⟩⟩⟩

private def differenceB {n : ℕ} (i j : Fin n) (hne : i ≠ j) : ↥(corootPairs n) :=
  ⟨(coordinate n i - coordinate n j, coordinate n i - coordinate n j),
    Or.inr ⟨i, j, hne, rfl, Or.inl rfl⟩⟩

/-- Positive coordinate roots of type B are simple or sums of two positive roots. -/
private theorem simpleB_or_sum {n : ℕ} (a : ↥(corootPairs n)) (hp : 0 < typeBHeight n a.val.1) :
    (∃ i, a.val.1 = simpleBRoot i) ∨
    ∃ b c : ↥(corootPairs n), a.val.1 = b.val.1 + c.val.1 ∧
      0 < typeBHeight n b.val.1 ∧ 0 < typeBHeight n c.val.1 := by
  rcases a with ⟨⟨x, y⟩, h⟩
  change 0 < typeBHeight n x at hp
  change (∃ i, x = simpleBRoot i) ∨
    ∃ b c : ↥(corootPairs n), x = b.val.1 + c.val.1 ∧
      0 < typeBHeight n b.val.1 ∧ 0 < typeBHeight n c.val.1
  rcases h with (⟨i, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩) | ⟨i, j, hij, _, rfl | rfl | rfl⟩
  · have hi := i.isLt
    by_cases h : i.val + 1 < n
    · let j : Fin n := ⟨i.val + 1, h⟩
      have hne : i ≠ j := fun he => by have := congrArg Fin.val he; simp [j] at this
      exact Or.inr ⟨differenceB i j hne, positiveShortB j,
        by change _ = (_ - _) + coordinate n j; abel,
        by simp [differenceB, j],
        by simp [positiveShortB, j]; omega⟩
    · exact Or.inl ⟨i, by simp [simpleBRoot, h]⟩
  · have hi := i.isLt
    simp only [map_neg, typeBHeight_coordinate] at hp
    omega
  · simp only [map_sub, typeBHeight_coordinate] at hp
    have hj := j.isLt
    have h : i.val + 1 < n := by omega
    by_cases hadj : i.val + 1 = j.val
    · have he : (⟨i.val + 1, h⟩ : Fin n) = j := Fin.ext hadj
      exact Or.inl ⟨i, by simp [simpleBRoot, h, he]⟩
    · let l : Fin n := ⟨i.val + 1, h⟩
      have hi : i ≠ l := fun he => by have := congrArg Fin.val he; simp [l] at this
      have hl : l ≠ j := fun he => hadj (congrArg Fin.val he)
      refine Or.inr ⟨differenceB i l hi, differenceB l j hl, ?_, ?_, ?_⟩
      · change _ = (_ - coordinate n l) + (coordinate n l - _)
        abel
      · simp [differenceB, l]
      · simp [differenceB, l]
        omega
  · refine Or.inr ⟨positiveShortB i, positiveShortB j, rfl, ?_, ?_⟩
    · have hi := i.isLt
      simp [positiveShortB]
    · have hj := j.isLt
      simp [positiveShortB]
  · have hi := i.isLt
    have hj := j.isLt
    simp only [map_neg, map_add, typeBHeight_coordinate] at hp
    omega

private theorem dot_coordinate {n : ℕ} (a : Fin n → ℤ) (i : Fin n) :
    ∑ k, a k * coordinate n i k = a i := by
  simp [coordinate, Pi.single_apply, mul_ite]

private theorem typeB_cartan_coordinates {n : ℕ} (i j : Fin n) :
    ∑ k, simpleBRoot j k * simpleBCoroot i k = CartanMatrix.C n i j := by
  have hi := i.isLt
  have hj := j.isLt
  unfold simpleBCoroot
  split_ifs with hit
  · have hd : ∀ a : Fin n → ℤ, (∑ k, a k * (coordinate n i - coordinate n ⟨i.val + 1, hit⟩) k) =
        a i - a ⟨i.val + 1, hit⟩ := by
      intro a
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, dot_coordinate]
    rw [hd]
    simp only [simpleBRoot, CartanMatrix.C, Matrix.of_apply]
    split_ifs with hjt heq hforward hback hlast
    all_goals
      simp only [Pi.sub_apply, coordinate, Pi.single_apply, Fin.ext_iff] at *
      split_ifs <;> omega
  · have hd : ∀ a : Fin n → ℤ, (∑ k, a k * (2 • coordinate n i : Fin n → ℤ) k) =
        2 * a i := by
      intro a
      simp only [Pi.smul_apply, two_nsmul, mul_add, Finset.sum_add_distrib, dot_coordinate, two_mul]
    rw [hd]
    simp only [simpleBRoot, CartanMatrix.C, Matrix.of_apply]
    split_ifs with hjt heq hforward hback hlast
    all_goals
      simp only [Pi.sub_apply, coordinate, Pi.single_apply, Fin.ext_iff] at *
      split_ifs <;> omega


open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.OddSpinModels
open Specs.AbstractPairing (Datum Root)
open Specs.Pinning (AttachedDatum BasedRootDatum BasedIso SplitBorelPair PinnedGroup)
open Specs.Arithmetic.OddSpinAwayFromTwo (IsTypeBDatum)
open Specs.GeometricRadicals (GeometricGroup IsSemisimple IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.BorelsAndChambers (IsPositiveSystem subgroupRoots)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.AbsoluteDynkinTypes (PreservesCartan HasDynkinType)
open LieAlgebrasAndRepresentations (FiniteDynkinType)

open private basedIso_base_iff pinnedLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private splitBorelPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private basedIsoOfScalarExtension geometricCorootSpan
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TypeCSplitRecognition
open private groupBaseChangeTower from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange

variable {k : Type u} [Field k]

private theorem marked_split_reference_of_cover {n : ℕ} (hn : 0 < n)
    {H O : AffineAlgebraicGroup k} (hH : IsSemisimple H) (hSC : GeometricallySimplyConnected H)
    (hO : IsSemisimple O) {U : ClosedSubgroup H.val} {T : ClosedSubgroup O.val}
    (hsU : IsSplitTorus U.group) (hmU : IsGeometricallyMaximal U)
    (hsT : IsSplitTorus T.group) (hmT : IsGeometricallyMaximal T)
    (p : H.val ⟶ O.val) (hp : IsCentralIsogeny p)
    (q : U.group ⟶ T.group) (hq : IsTorusRestriction p q)
    [IsCommMonObj T.group.X] (D : Datum T)
    (X : Additive (CharacterDescent.Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
    (Y : Additive (CharacterDescent.Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ))
    (hD : IsTypeBDatum n T D X Y) :
    ∃ (P : SplitBorelPair k) (E : AttachedDatum P),
      IsSemisimple P.G ∧ GeometricallySimplyConnected P.G ∧
        (letI := E.comm; Nonempty (SimplyConnectedTypeBMarking n E.datum)) := by
  let P := splitBorelPair H (reductive_of_semisimple H hH) U hsU hmU
  let E := Classification.Pinning.attachedDatum P
  exact ⟨P, E, hH, hSC, typeBMarkingFromAdjoint P E n hn hH hSC O
    (reductive_of_semisimple O hO) T hsT hmT p hp q hq D X Y hD⟩

set_option maxHeartbeats 700000 in
private theorem marked_split_reference (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    ∃ (P : SplitBorelPair k) (E : AttachedDatum P),
      IsSemisimple P.G ∧ GeometricallySimplyConnected P.G ∧
        (letI := E.comm; Nonempty (SimplyConnectedTypeBMarking n E.datum)) := by
  by_cases h₂ : (2 : k) = 0
  · obtain ⟨H, O, _, p, _, h, o, _, _, _, hh, hH, hSC, hO, hp, _, _, _, _,
      T, U, q, hsT, hmT, hsU, hmU, hq, _, _, _, _, _, comm, D, X, Y, hD, _, _, _⟩ :=
      pairSplitSpin k n h₂ hn
    letI := comm
    exact marked_split_reference_of_cover hn hH hSC hO hsU hmU hsT hmT p hp q hq D X Y hD
  · obtain ⟨H, O, p, _, _, _, _, _, _, _, hH, hSC, hO, hp, _, _,
      _, _, _, _, _, _, T, U, q, hsT, hmT, hsU, hmU, hq, _, _, _, _, _, _, _,
      comm, D, X, Y, hD, _, _, _, _, _⟩ := OddSpinAwayFromTwo.splitOddSpin k n h₂ hn
    letI := comm
    exact marked_split_reference_of_cover hn hH hSC hO hsU hmU hsT hmT p hp q hq D X Y hD

private theorem mark_root_add {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} {n : ℕ} (m : SimplyConnectedTypeBMarking n D)
    (a b c : Root T) (h : (m.roots a).val.1 = (m.roots b).val.1 + (m.roots c).val.1) :
    D.rootDatum.root a = D.rootDatum.root b + D.rootDatum.root c := by
  apply D.rootDatum.toLinearMap.toPerfPair.injective
  ext y
  change D.rootDatum.toLinearMap (D.rootDatum.root a) y =
    D.rootDatum.toLinearMap (D.rootDatum.root b + D.rootDatum.root c) y
  simp only [map_add, LinearMap.add_apply, m.pairing_eq, h, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

set_option maxHeartbeats 800000 in
/-- The chamber with descending positive coordinate values gives the standard
type-B simple roots on the marked torus of the split spin cover. -/
private theorem reference_borel_cartan (P : SplitBorelPair k) (D : AttachedDatum P)
    {n : ℕ} (hn : 2 ≤ n)
    (m : letI := D.comm; SimplyConnectedTypeBMarking n D.datum) :
    ∃ (Q : SplitBorelPair k) (E : AttachedDatum Q), Q.G = P.G ∧
      (letI := E.comm; Nonempty (SimplyConnectedTypeBMarking n E.datum)) ∧
      HasDynkinType (RootData.integralCartan E.toBased.datum E.toBased.base) (.B n hn) := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.reduced
  let v : evenSum (Fin n) := ⟨fun j => 2 * ((n : ℤ) - j.val), by
    change Even (∑ j : Fin n, 2 * ((n : ℤ) - j.val))
    rw [← Finset.mul_sum]
    exact even_two_mul _⟩
  let y := m.cocharacters.symm v
  let F := D.datum.rootDatum.toLinearMap.flip y
  have value (a : Root P.T) : F (D.datum.rootDatum.root a) = 2 * typeBHeight n (m.roots a).val.1 := by
    change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root a) y = _
    rw [m.pairing_eq, show m.cocharacters y = v from m.cocharacters.apply_symm_apply _, typeBHeight_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change _ * (2 * ((n : ℤ) - i.val)) = _
    ring
  have regular (a : Root P.T) : F (D.datum.rootDatum.root a) ≠ 0 := by
    rw [value]
    exact mul_ne_zero two_ne_zero (typeBHeight_ne_zero (m.roots a))
  have positive (a : Root P.T) :
      a ∈ Specs.SimpleRoots.positive D.datum.rootDatum F ↔ 0 < typeBHeight n (m.roots a).val.1 := by
    change 0 < F (D.datum.rootDatum.root a) ↔ _
    rw [value]
    omega
  have positiveSystem : IsPositiveSystem P.T (Specs.SimpleRoots.positive D.datum.rootDatum F) := by
    refine ⟨Specs.SimpleRoots.realFunctional F, ?_, ?_⟩
    · intro a
      change (F (Additive.ofMul a.val) : ℝ) ≠ 0
      rw [← D.datum.root_eq]
      exact_mod_cast regular a
    · ext a
      change (0 < F (D.datum.rootDatum.root a)) ↔ 0 < (F (Additive.ofMul a.val) : ℝ)
      rw [← D.datum.root_eq]
      exact Int.cast_pos.symm
  obtain ⟨B, hB, hBT, hpos, _⟩ :=
    ((RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).2 _).mp
      positiveSystem
  let Q : SplitBorelPair k := { P with B := B, borel := hB, containsTorus := hBT }
  obtain ⟨base, hbase⟩ := RootData.SimpleRoots.baseFor D.datum.rootDatum F regular
  let E : AttachedDatum Q := ⟨D.comm, D.datum, base, fun a => by
    change a ∈ base.support ↔ Specs.Pinning.IsSimple Q a
    rw [hbase.simple_iff]
    simp only [Specs.Pinning.IsSimple, Q, hpos, D.datum.root_eq]
    rfl⟩
  let s (i : Fin n) : Root P.T := m.roots.symm ⟨(simpleBRoot i, simpleBCoroot i), simpleB_mem i⟩
  have ms (i : Fin n) : (m.roots (s i)).val = (simpleBRoot i, simpleBCoroot i) :=
    congrArg Subtype.val (m.roots.apply_symm_apply _)
  have simple (i : Fin n) : s i ∈ base.support := by
    refine (hbase.simple_iff (s i)).mpr ⟨(positive _).mpr (by rw [ms, simpleB_height]; decide), ?_⟩
    intro a ha b hb hab
    have heq := congrArg F hab
    rw [map_add, value, value, value, ms, simpleB_height] at heq
    have ha' := (positive a).mp ha
    have hb' := (positive b).mp hb
    omega
  have cartan (i j : Fin n) :
      D.datum.rootDatum.pairing (s j) (s i) = CartanMatrix.C n i j := by
    rw [← RootPairing.root_coroot_eq_pairing, m.pairing_eq, m.coroot_eq, ms, ms]
    exact typeB_cartan_coordinates i j
  let t (i : Fin n) : ↥base.support := ⟨s i, simple i⟩
  have inj : Function.Injective t := by
    intro i j h
    by_contra hne
    have e : s i = s j := congrArg Subtype.val h
    have hb := cartan i j
    rw [← e, cartan, CartanMatrix.C_diag] at hb
    simp only [CartanMatrix.C, Matrix.of_apply, hne, ite_false] at hb
    split_ifs at hb
    all_goals omega
  have surj : Function.Surjective t := by
    rintro ⟨a, ha⟩
    obtain ⟨hp, hi⟩ := (hbase.simple_iff a).mp ha
    rcases simpleB_or_sum (m.roots a) ((positive a).mp hp) with ⟨i, he⟩ | ⟨b, c, he, hb, hc⟩
    · refine ⟨i, Subtype.ext (root_eq_of_coordinates m ?_)⟩
      change (m.roots (s i)).val.1 = (m.roots a).val.1
      rw [ms, he]
    · let a₁ := m.roots.symm b
      let a₂ := m.roots.symm c
      have h₁ : m.roots a₁ = b := m.roots.apply_symm_apply _
      have h₂ : m.roots a₂ = c := m.roots.apply_symm_apply _
      have hm : D.datum.rootDatum.root a = D.datum.rootDatum.root a₁ + D.datum.rootDatum.root a₂ :=
        mark_root_add m a a₁ a₂ (by rwa [h₁, h₂])
      exact (hi a₁ ((positive _).mpr (by rwa [h₁]))
        a₂ ((positive _).mpr (by rwa [h₂])) hm).elim
  let e := Equiv.ofBijective t ⟨inj, surj⟩
  refine ⟨Q, E, rfl, ⟨m⟩, e.symm, ?_⟩
  intro a b
  obtain ⟨i, rfl⟩ := e.surjective a
  obtain ⟨j, rfl⟩ := e.surjective b
  change D.datum.rootDatum.pairing (s j) (s i) =
    CartanMatrix.C n (e.symm (e i)) (e.symm (e j))
  simpa only [Equiv.symm_apply_apply] using cartan i j

private def simple_vertices {D E : BasedRootDatum.{u}} (e : BasedIso D E) :
    ↥D.base.support ≃ ↥E.base.support :=
  e.val.indexEquiv.subtypeEquiv (basedIso_base_iff e)

private theorem based_iso_preserves_cartan {D E : BasedRootDatum.{u}} (e : BasedIso D E) :
    PreservesCartan (RootData.integralCartan D.datum D.base)
      (RootData.integralCartan E.datum E.base) (simple_vertices e) := by
  intro i j
  exact e.val.toHom.pairing.symm

private theorem full_coroots_of_based_iso {D E : BasedRootDatum.{u}} (e : BasedIso D E)
    (h : Submodule.span ℤ (Set.range E.datum.coroot) = ⊤) :
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ := by
  have he (i : E.I) :
      e.val.coweightEquiv (E.datum.coroot i) = D.datum.coroot (e.val.indexEquiv.symm i) :=
    e.val.toHom.coroot_coweightMap_apply D.datum E.datum i
  have himage : e.val.coweightEquiv '' Set.range E.datum.coroot = Set.range D.datum.coroot := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, (he a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, Set.mem_range_self (e.val.indexEquiv a), by rw [he, Equiv.symm_apply_apply]⟩
  rw [← himage]
  change Submodule.span ℤ (e.val.coweightEquiv.toLinearMap '' Set.range E.datum.coroot) = ⊤
  rw [← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  exact e.val.coweightEquiv.surjective

private theorem type_of_based_iso {D E : BasedRootDatum.{u}} (e : BasedIso D E) {t : FiniteDynkinType}
    (h : HasDynkinType (RootData.integralCartan E.datum E.base) t) :
    HasDynkinType (RootData.integralCartan D.datum D.base) t := by
  obtain ⟨j, hj⟩ := h
  exact ⟨(simple_vertices e).trans j, fun i l =>
    (based_iso_preserves_cartan e i l).trans (hj _ _)⟩

private theorem same_type_cartan {D E : BasedRootDatum.{u}} {t : FiniteDynkinType}
    (hD : HasDynkinType (RootData.integralCartan D.datum D.base) t)
    (hE : HasDynkinType (RootData.integralCartan E.datum E.base) t) :
    ∃ e, PreservesCartan (RootData.integralCartan D.datum D.base)
      (RootData.integralCartan E.datum E.base) e := by
  obtain ⟨i, hi⟩ := hD
  obtain ⟨j, hj⟩ := hE
  exact ⟨i.trans j.symm, fun a b => (hi a b).trans (by simpa using (hj (j.symm (i a)) (j.symm (i b))).symm)⟩

set_option maxHeartbeats 1200000 in
theorem typeBApplicability : TypeBApplicability.{u,v} := by
  intro k _ rank hRank G hG hSC P hP D hType
  cases rank with
  | zero => omega
  | succ n =>
    let S := SeparableClosure k
    let K := AlgebraicClosure k
    obtain ⟨Q, hQ⟩ := TypeCSplitRecognition.separableBorelPair (S := S) G
      (reductive_of_semisimple G hG.1)
    let E := Classification.Pinning.attachedDatum Q
    let eQ : Q.G.val ≅ (groupBaseChange k S).obj G.val := eqToIso (congrArg Subtype.val hQ)
    let eP : (groupBaseChange k K).obj G.val ≅ P.G.val := eqToIso (congrArg Subtype.val hP.symm)
    let f : (groupBaseChange S K).obj Q.G.val ≅ P.G.val :=
      (groupBaseChange S K).mapIso eQ ≪≫ ((groupBaseChangeTower (K := S) K).app G.val).symm ≪≫ eP
    -- The integral model gives the same marked datum in both field fibres.
    -- Identifying the geometric fibre uses conjugacy of the actual Borel pairs.
    obtain ⟨e⟩ := basedIsoOfScalarExtension Q E P D f
    have hE := full_coroots_of_based_iso e (geometricCorootSpan G hG.1 hSC P D hP)
    have hET := type_of_based_iso e hType
    obtain ⟨R₀, D₀, hR₀, hSC₀, ⟨m⟩⟩ := marked_split_reference k (n + 1) (Nat.succ_pos n)
    obtain ⟨R, B, hR, hMark, hBT⟩ := reference_borel_cartan R₀ D₀ hRank m
    have hRs : IsSemisimple R.G := hR.symm ▸ hR₀
    have hSCr : GeometricallySimplyConnected R.G := hR.symm ▸ hSC₀
    letI := B.comm
    have hB : Submodule.span ℤ (Set.range B.toBased.datum.coroot) = ⊤ :=
      (Classification.SimplyConnectedLattice.latticeCriterion R.G hRs R.T R.split R.maximal B.datum).mp
        hSCr
    obtain ⟨Rₛ, hRₛ⟩ := TypeCSplitRecognition.separableBorelPair (S := S) R.G R.reductive
    let Bₛ := Classification.Pinning.attachedDatum Rₛ
    let eR : (groupBaseChange k S).obj R.G.val ≅ Rₛ.G.val := eqToIso (congrArg Subtype.val hRₛ.symm)
    obtain ⟨r⟩ := basedIsoOfScalarExtension R B Rₛ Bₛ eR
    let r' : BasedIso Bₛ.toBased B.toBased :=
      Groupoid.inv (show B.toBased ⟶ Bₛ.toBased from r)
    have hBₛ := full_coroots_of_based_iso r' hB
    have hBₛT := type_of_based_iso r' hBT
    obtain ⟨z, hz⟩ := same_type_cartan hBₛT hET
    obtain ⟨d, _, _⟩ :=
      (RootData.AbsoluteDynkinTypes.cartanDeterminesBasedDatum Bₛ.toBased E.toBased hBₛ hE z).mp hz
    let A := Classification.Pinning.standardAdditiveLine S
    obtain ⟨U, ⟨p⟩⟩ := Classification.Pinning.pinningsExist A Rₛ
    obtain ⟨V, ⟨q⟩⟩ := Classification.Pinning.pinningsExist A Q
    let P₁ : PinnedGroup A := ⟨Rₛ, U, p⟩
    let P₂ : PinnedGroup A := ⟨Q, V, q⟩
    obtain ⟨j, _⟩ := pinnedLift P₁ P₂ Bₛ E d
    exact typeBFormDescent R B n G hMark
      ⟨S, inferInstance, inferInstance, inferInstance, ⟨eR ≪≫ j.group ≪≫ eQ⟩⟩

end AbsoluteTypeB

end

end LinearAlgebraicGroups.Arithmetic.OddSpinModels
