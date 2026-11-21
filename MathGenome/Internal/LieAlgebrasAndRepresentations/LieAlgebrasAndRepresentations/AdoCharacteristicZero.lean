import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AdoCharacteristicZero
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AdoComplexReal
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Jacobson.Ring

noncomputable section

namespace LieAlgebrasAndRepresentations.AdoCharacteristicZero

open Module
open scoped BigOperators TensorProduct Cardinal

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

/-- Map a transcendence basis into one of the complex field and extend algebraically. -/
private theorem embeds_complex (F : Type u) [Field F] [CharZero F]
    [Algebra.EssFiniteType ℚ F] :
    Nonempty (F →+* ℂ) := by
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis ℚ F
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hC : ℵ₀ < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  have htlarge : ℵ₀ < Cardinal.mk t :=
    (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      _ ht Cardinal.mk_le_aleph0 hC) ▸ hC
  have hst : Cardinal.lift.{0} (Cardinal.mk s) ≤ Cardinal.lift.{u} (Cardinal.mk t) := by
    calc
      _ ≤ ℵ₀ := by simp
      _ ≤ _ := by simpa using htlarge.le
  obtain ⟨e⟩ := Cardinal.lift_mk_le.mp hst
  let y : s → ℂ := fun i => (e i : ℂ)
  let A := Algebra.adjoin ℚ (Set.range ((↑) : s → F))
  let f : A →+* ℂ := ((MvPolynomial.aeval y).comp hs.1.aevalEquiv.symm.toAlgHom).toRingHom
  let : Algebra A ℂ := f.toAlgebra
  have hy : AlgebraicIndependent ℚ y := ht.1.comp e e.injective
  have : IsTorsionFree A ℂ := isTorsionFree_iff_algebraMap_injective.mpr
    ((algebraicIndependent_iff_injective_aeval.mp hy).comp hs.1.aevalEquiv.symm.injective)
  have : Algebra.IsAlgebraic A F := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift : F →ₐ[A] ℂ).toRingHom⟩

/-- A polynomial system in finitely many variables with a complex solution
also has a solution over a finite extension of any extension field of its coefficient field. -/
private theorem specialize {F K σ : Type*} [Field F] [Field K] [Algebra F K]
    [Algebra F ℂ] [Finite σ] (P : Set (MvPolynomial σ F)) (z : σ → ℂ)
    (hz : ∀ p ∈ P, MvPolynomial.aeval z p = 0) :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
      ∃ x : σ → E, ∀ p ∈ P, MvPolynomial.aeval x p = 0 := by
  let I := Ideal.span P
  have hI : I ≠ ⊤ := by
    have hle : I ≤ RingHom.ker (MvPolynomial.aeval z : MvPolynomial σ F →ₐ[F] ℂ) :=
      Ideal.span_le.mpr hz
    exact ne_top_of_le_ne_top (RingHom.ker_ne_top _) hle
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I hI
  have : J.IsMaximal := hJ
  let L := MvPolynomial σ F ⧸ J
  let : Field L := Ideal.Quotient.field J
  have : FiniteDimensional F L := finite_of_finite_type_of_isJacobsonRing F L
  have : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  let f : L →ₐ[F] AlgebraicClosure K := IsAlgClosed.lift
  let q := f.comp (Ideal.Quotient.mkₐ F J)
  let y : σ → AlgebraicClosure K := fun s => q (MvPolynomial.X s)
  let E := IntermediateField.adjoin K (Set.range y)
  let x : σ → E := fun s => ⟨y s, IntermediateField.subset_adjoin K _ ⟨s, rfl⟩⟩
  have : IsScalarTower F E (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hq : MvPolynomial.aeval y = q := by ext s; simp [y]
  refine ⟨E, inferInstance, x, fun p hp => E.val.injective ?_⟩
  change (IsScalarTower.toAlgHom F E (AlgebraicClosure K)) (MvPolynomial.aeval x p) = 0
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, show
    (fun s => IsScalarTower.toAlgHom F E (AlgebraicClosure K) (x s)) = y from rfl, hq]
  have hmem : p ∈ J := hIJ (Ideal.subset_span hp)
  have hp0 : (Ideal.Quotient.mkₐ F J) p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simp [q, hp0]

private def matrixPairing {R n : Type*} [CommSemiring R] [Fintype n]
    (Y X : Matrix n n R) : R :=
  ∑ a, ∑ b, Y a b * X a b

/-- Matrices satisfy the bracket equations and have coefficient-extracting
linear functionals. The latter equations are a polynomial certificate of faithfulness. -/
private def MatrixRelations {F R ι n : Type*} [Field F] [CommRing R] [Algebra F R]
    [Fintype ι] [DecidableEq ι] [Fintype n]
    (c : ι → ι → ι → F) (X Y : ι → Matrix n n R) : Prop :=
  (∀ i j, X i * X j - X j * X i = ∑ k, algebraMap F R (c i j k) • X k) ∧
    (∀ i j, matrixPairing (Y i) (X j) = if i = j then 1 else 0)

private abbrev MatrixVariable (ι n : Type*) := (ι × n × n) ⊕ (ι × n × n)

private def bracketPolynomial {F ι n : Type*} [Field F] [Fintype ι] [Fintype n]
    (c : ι → ι → ι → F) (i j : ι) (a b : n) : MvPolynomial (MatrixVariable ι n) F :=
  let X := fun k l m => MvPolynomial.X (R := F) (.inl (k, l, m) : MatrixVariable ι n)
  (∑ d, X i a d * X j d b) - (∑ d, X j a d * X i d b) -
    ∑ k, MvPolynomial.C (c i j k) * X k a b

private def dualPolynomial {F ι n : Type*} [Field F] [DecidableEq ι] [Fintype n]
    (i j : ι) : MvPolynomial (MatrixVariable ι n) F :=
  (∑ a : n, ∑ b : n, MvPolynomial.X (.inr (i, a, b)) *
    MvPolynomial.X (.inl (j, a, b))) - if i = j then 1 else 0

private def matrixPoint {R ι n : Type*} (X Y : ι → Matrix n n R) : MatrixVariable ι n → R :=
  Sum.elim (fun (i, a, b) => X i a b) (fun (i, a, b) => Y i a b)

private def matrixEquations {F ι n : Type*} [Field F] [Fintype ι] [DecidableEq ι] [Fintype n]
    (c : ι → ι → ι → F) : Set (MvPolynomial (MatrixVariable ι n) F) :=
  Set.range (fun (⟨i, j, a, b⟩ : ι × ι × n × n) => bracketPolynomial c i j a b) ∪
    Set.range (fun (⟨i, j⟩ : ι × ι) => dualPolynomial (n := n) i j)

private theorem matrixRelations_iff {F R ι n : Type*} [Field F] [CommRing R] [Algebra F R]
    [Fintype ι] [DecidableEq ι] [Fintype n]
    (c : ι → ι → ι → F) (X Y : ι → Matrix n n R) :
    MatrixRelations c X Y ↔
      ∀ p ∈ matrixEquations (n := n) c, MvPolynomial.aeval (matrixPoint X Y) p = 0 := by
  have eval_bracket (i j : ι) (a b : n) :
      MvPolynomial.aeval (matrixPoint X Y) (bracketPolynomial c i j a b) =
        (X i * X j - X j * X i - ∑ k, algebraMap F R (c i j k) • X k) a b := by
    simp only [bracketPolynomial, map_sub, map_sum, map_mul, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, matrixPoint, Sum.elim_inl, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have eval_dual (i j : ι) :
      MvPolynomial.aeval (matrixPoint X Y) (dualPolynomial (F := F) i j) =
        matrixPairing (Y i) (X j) - if i = j then 1 else 0 := by
    by_cases hij : i = j <;> simp [dualPolynomial, matrixPoint, matrixPairing, hij]
  constructor
  · rintro h p (⟨⟨i, j, a, b⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩)
    · change MvPolynomial.aeval (matrixPoint X Y) (bracketPolynomial c i j a b) = 0
      rw [eval_bracket, h.1 i j, sub_self]
      rfl
    · change MvPolynomial.aeval (matrixPoint X Y) (dualPolynomial (F := F) i j) = 0
      rw [eval_dual, h.2 i j, sub_self]
  · intro h
    refine ⟨fun i j => sub_eq_zero.mp ?_, fun i j => sub_eq_zero.mp ?_⟩
    · apply Matrix.ext
      intro a b
      change (X i * X j - X j * X i - ∑ k, algebraMap F R (c i j k) • X k) a b = 0
      rw [← eval_bracket]
      exact h _ (Or.inl ⟨(i, j, a, b), rfl⟩)
    · rw [← eval_dual]
      exact h _ (Or.inr ⟨(i, j), rfl⟩)

private theorem specializeMatrices {F K ι n : Type*} [Field F] [Field K] [Algebra F K]
    [Algebra F ℂ] [Fintype ι] [DecidableEq ι] [Fintype n]
    (c : ι → ι → ι → F) (X Y : ι → Matrix n n ℂ) (h : MatrixRelations c X Y) :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
      ∃ X' Y' : ι → Matrix n n E, MatrixRelations c X' Y' := by
  obtain ⟨E, hE, z, hz⟩ := specialize (K := K) _
    (matrixPoint X Y) ((matrixRelations_iff c X Y).mp h)
  let X' : ι → Matrix n n E := fun i a b => z (.inl (i, a, b))
  let Y' : ι → Matrix n n E := fun i a b => z (.inr (i, a, b))
  have hpoint : matrixPoint X' Y' = z := by
    funext p
    rcases p with ⟨i, a, b⟩ | ⟨i, a, b⟩ <;> rfl
  exact ⟨E, hE, X', Y', (matrixRelations_iff c X' Y').mpr (hpoint.symm ▸ hz)⟩

/-- Obtain coefficient-extracting matrices from a linear left inverse. -/
private theorem exists_dual_matrices {R ι n : Type*} [Field R] [Fintype n] [DecidableEq n]
    [DecidableEq ι] {G : Type*} [AddCommGroup G] [Module R G]
    (b : Basis ι R G) (f : G →ₗ[R] Matrix n n R) (hf : Function.Injective f) :
    ∃ Y : ι → Matrix n n R,
      ∀ i j, matrixPairing (Y i) (f (b j)) = if i = j then 1 else 0 := by
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let coord : ι → Matrix n n R →ₗ[R] R := fun i => (b.coord i).comp g
  let Y : ι → Matrix n n R := fun i a d => coord i (Matrix.single a d 1)
  have hY (i : ι) (M : Matrix n n R) : matrixPairing (Y i) M = coord i M := by
    conv_rhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum, matrixPairing, Y]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro d _
    have hm : Matrix.single a d (M a d) = M a d • Matrix.single a d (1 : R) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hm, map_smul, smul_eq_mul, mul_comm]
  refine ⟨Y, fun i j => ?_⟩
  rw [hY]
  have hgj : g (f (b j)) = b j := DFunLike.congr_fun hg (b j)
  simp [coord, hgj, Basis.coord_apply, Finsupp.single_apply, eq_comm]

private theorem complexMatrices {F : Type u} {K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Algebra F ℂ] [Fintype ι] [DecidableEq ι]
    {G : Type v} [LieRing G] [LieAlgebra K G]
    (b : Basis ι K G) (c : ι → ι → ι → F)
    (hc : ∀ i j k, algebraMap F K (c i j k) = b.repr ⁅b i, b j⁆ k) :
    ∃ m : ℕ, ∃ X Y : ι → Matrix (Fin m) (Fin m) ℂ, MatrixRelations c X Y := by
  let : LieAlgebra F G :=
    { Module.restrictScalars F K G with
      lie_smul := fun t x y => lie_smul (algebraMap F K t) x y }
  have : IsScalarTower F K G := IsScalarTower.restrictScalars F K G
  let S : Submodule F G := Submodule.span F (Set.range b)
  have hbr (i j : ι) : ⁅b i, b j⁆ = ∑ k, c i j k • b k := by
    simpa only [show ∀ (t : F) (x : G), t • x = (algebraMap F K t) • x from fun _ _ => rfl, hc]
      using (b.sum_repr ⁅b i, b j⁆).symm
  let A : LieSubalgebra F G :=
    { S with
      lie_mem' := by
        intro x y hx hy
        exact Submodule.span_induction₂ (p := fun x y _ _ => ⁅x, y⁆ ∈ S)
          (by
            rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
            rw [hbr]
            exact S.sum_mem fun k _ => S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩))
          (by simp [S]) (by simp [S])
          (by intros; rw [add_lie]; apply S.add_mem <;> assumption)
          (by intros; rw [lie_add]; apply S.add_mem <;> assumption)
          (by intros; rw [smul_lie]; apply S.smul_mem; assumption)
          (by intros; rw [lie_smul]; apply S.smul_mem; assumption)
          hx hy }
  let bF : Basis ι F A := Basis.span (b.linearIndependent.restrict_scalars' F)
  have hbF (i : ι) : (bF i : G) = b i :=
    Basis.coe_span_apply (b.linearIndependent.restrict_scalars' F) i
  have hF (i j : ι) : ⁅bF i, bF j⁆ = ∑ k, c i j k • bF k := by
    apply Subtype.ext
    change A.incl ⁅bF i, bF j⁆ = A.incl (∑ k, c i j k • bF k)
    simpa only [map_sum, LieHom.map_lie, map_smul, LieSubalgebra.coe_incl, hbF]
      using hbr i j
  let bC := bF.baseChange ℂ
  have : FiniteDimensional ℂ (ℂ ⊗[F] A) := Module.Finite.of_basis bC
  obtain ⟨V, hVadd, hVmod, hVfin, ρ, hρ⟩ := AdoComplexReal.complexAdo (ℂ ⊗[F] A)
  let _ := hVadd
  let _ := hVmod
  have := hVfin
  let m := finrank ℂ V
  let e : Module.End ℂ V ≃ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ :=
    LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)
  let f := e.toLieEquiv.toLieHom.comp ρ
  have hf : Function.Injective f := e.injective.comp hρ
  let X : ι → Matrix (Fin m) (Fin m) ℂ := fun i => f (bC i)
  obtain ⟨Y, hY⟩ := exists_dual_matrices bC f.toLinearMap hf
  refine ⟨m, X, Y, ?_, hY⟩
  intro i j
  have hC : ⁅bC i, bC j⁆ = ∑ k, algebraMap F ℂ (c i j k) • bC k := by
    simp only [bC, Basis.baseChange_apply, LieAlgebra.ExtendScalars.bracket_tmul,
      hF, TensorProduct.tmul_sum, TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul, mul_one]
  change ⁅f (bC i), f (bC j)⁆ = _
  rw [← f.map_lie, hC, map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul f (algebraMap F ℂ (c i j k)) (bC k)

/-- Interpret a matrix as an endomorphism after restricting the scalars of its column space. -/
private def matrixAction (K E : Type*) [Field K] [Field E] [Algebra K E] (n : ℕ) :
    Matrix (Fin n) (Fin n) E →ₗ⁅K⁆ Module.End K (Fin n → E) where
  toLinearMap :=
    (LinearMap.restrictScalarsₗ K E (Fin n → E) (Fin n → E) K).comp
      ((Matrix.toLinAlgEquiv' (R := E) (n := Fin n)).toLinearMap.restrictScalars K)
  map_lie' := by
    intro X Y
    apply LinearMap.ext
    intro x
    change Matrix.toLinAlgEquiv' (X * Y - Y * X) x =
      Matrix.toLinAlgEquiv' X (Matrix.toLinAlgEquiv' Y x) -
        Matrix.toLinAlgEquiv' Y (Matrix.toLinAlgEquiv' X x)
    rw [map_sub, map_mul, map_mul]
    rfl

private theorem matrixAction_injective (K E : Type*) [Field K] [Field E] [Algebra K E]
    (n : ℕ) : Function.Injective (matrixAction K E n) := by
  intro X Y h
  apply Matrix.toLinAlgEquiv'.injective
  apply LinearMap.restrictScalars_injective K
  exact h

private theorem matricesGiveRepresentation
    {F K E ι : Type*} [Field F] [Field K] [Field E] [Algebra F K] [Algebra K E]
    [Algebra F E] [IsScalarTower F K E] [Fintype ι] [DecidableEq ι]
    {G : Type*} [LieRing G] [LieAlgebra K G] (b : Basis ι K G)
    (c : ι → ι → ι → F)
    (hc : ∀ i j k, algebraMap F K (c i j k) = b.repr ⁅b i, b j⁆ k)
    {n : ℕ} (X Y : ι → Matrix (Fin n) (Fin n) E) (h : MatrixRelations c X Y) :
    ∃ ρ : G →ₗ⁅K⁆ Module.End K (Fin n → E), Function.Injective ρ := by
  let f : G →ₗ[K] Matrix (Fin n) (Fin n) E := b.constr K X
  have hf (i : ι) : f (b i) = X i := b.constr_basis K X i
  have hbr (i j : ι) : f ⁅b i, b j⁆ = ⁅f (b i), f (b j)⁆ := by
    rw [hf, hf]
    change f ⁅b i, b j⁆ = X i * X j - X j * X i
    rw [h.1, ← b.sum_repr ⁅b i, b j⁆]
    simp only [map_sum, map_smul, hf, ← hc, IsScalarTower.algebraMap_apply F K E,
      IsScalarTower.algebraMap_smul]
  have hbil :
      ((LieAlgebra.ad K G).toLinearMap).compr₂ f =
        ((LieAlgebra.ad K (Matrix (Fin n) (Fin n) E)).toLinearMap).compl₁₂ f f :=
    LinearMap.ext_basis b b hbr
  let g : G →ₗ⁅K⁆ Matrix (Fin n) (Fin n) E :=
    { f with map_lie' := fun {x y} =>
        DFunLike.congr_fun (DFunLike.congr_fun hbil x) y }
  have hginj : Function.Injective g := by
    intro x y hxy
    apply b.repr.injective
    ext i
    let readE : Matrix (Fin n) (Fin n) E →ₗ[E] E :=
      ∑ a, ∑ d, Y i a d • Matrix.entryLinearMap E E a d
    let read := readE.restrictScalars K
    have hread (M : Matrix (Fin n) (Fin n) E) : read M = matrixPairing (Y i) M := by
      simp [read, readE, matrixPairing, smul_eq_mul]
    have he : read.comp f = (Algebra.linearMap K E).comp (b.coord i) := by
      apply b.ext
      intro j
      change read (f (b j)) = algebraMap K E (b.coord i (b j))
      rw [hf, hread, h.2]
      by_cases hij : i = j <;> simp [Basis.coord_apply, hij]
    have hxy' : f x = f y := hxy
    have hx := DFunLike.congr_fun he x
    have hy := DFunLike.congr_fun he y
    rw [LinearMap.comp_apply, hxy', ← LinearMap.comp_apply, hy] at hx
    exact (algebraMap K E).injective (by simpa [Basis.coord_apply] using hx.symm)
  exact ⟨(matrixAction K E n).comp g, (matrixAction_injective K E n).comp hginj⟩

/-- Ado's theorem over an arbitrary field of characteristic zero. -/
theorem characteristicZeroAdo :
    Specs.LieAlgebrasAndRepresentations.AdoCharacteristicZero.characteristicZeroAdoType.{u, v} := by
  classical
  intro K _ _ G _ _ _
  let ι := Fin (finrank K G)
  let b : Basis ι K G := Module.finBasis K G
  let constants : ι × ι × ι → K := fun (i, j, k) => b.repr ⁅b i, b j⁆ k
  let F := IntermediateField.adjoin ℚ (Set.range constants)
  let c : ι → ι → ι → F := fun i j k =>
    ⟨constants (i, j, k), IntermediateField.subset_adjoin ℚ _ ⟨(i, j, k), rfl⟩⟩
  have hc (i j k : ι) : algebraMap F K (c i j k) = b.repr ⁅b i, b j⁆ k := rfl
  obtain ⟨e⟩ := embeds_complex F
  let : Algebra F ℂ := e.toAlgebra
  obtain ⟨n, X, Y, h⟩ := complexMatrices b c hc
  obtain ⟨E, hE, X', Y', h'⟩ := specializeMatrices (K := K) c X Y h
  have : FiniteDimensional K E := hE
  obtain ⟨ρ, hρ⟩ := matricesGiveRepresentation b c hc X' Y' h'
  exact ⟨Fin n → E, inferInstance, inferInstance, inferInstance, ρ, hρ⟩

end LieAlgebrasAndRepresentations.AdoCharacteristicZero

