import MathGenome.Internal.Specs.D05.M13.NormalReducing.Subspace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel

noncomputable section
open scoped ComplexOrder
namespace D05.M13.NormalReducing.Subspace

universe u v w
variable {F : Type u} [RCLike F]

/-- A zero trace of a Gram matrix forces every column, hence every entry, to
vanish. This is the finite sum of nonnegative squared absolute values. -/
theorem eq_zero_of_trace_adjoint_comp_self
    {E : Type v} {G : Type w} [NormedAddCommGroup E] [NormedAddCommGroup G]
    [InnerProductSpace F E] [InnerProductSpace F G]
    [FiniteDimensional F E] [FiniteDimensional F G]
    (D : E →ₗ[F] G) (h : LinearMap.trace F E (D.adjoint.comp D) = 0) : D = 0 := by
  classical
  let b := stdOrthonormalBasis F E
  let c := stdOrthonormalBasis F G
  rw [LinearMap.trace_eq_matrix_trace F b.toBasis,
    LinearMap.toMatrix_comp b.toBasis c.toBasis b.toBasis,
    LinearMap.toMatrix_adjoint b c] at h
  have hz := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h
  exact (LinearMap.toMatrix b.toBasis c.toBasis).injective (by simpa using hz)

variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace F V]
  [FiniteDimensional F V]

/-- The inclusion of a subspace is an isometry: its adjoint is a left inverse. -/
theorem adjoint_subtype_comp (M : Submodule F V) :
    M.subtype.adjoint.comp M.subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right F
  intro y
  rw [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.adjoint_inner_left]
  rfl

/-- Coordinate-free form of the upper-left block trace calculation.
Here I is the isometric inclusion of M, A = T|M and
D = T† I - I A†. In orthonormal block coordinates D has columns (0,B*),
so D†D = BB*. Normality gives D†D = A†A - AA†. -/
theorem adjoint_invariant : Specs.D05.M13.NormalReducing.Subspace.adjoint_invariant := by
  intro F V _ _ _ _ T M hT hM
  let I := M.subtype
  let A := T.restrict hM
  let D := T.adjoint.comp I - I.comp A.adjoint
  have hII : I.adjoint.comp I = LinearMap.id := adjoint_subtype_comp M
  have hTI : T.comp I = I.comp A := rfl
  have hIIx (x : M) : I.adjoint (I x) = x := DFunLike.congr_fun hII x
  have hTIx (x : M) : T (I x) = I (A x) := DFunLike.congr_fun hTI x
  have hIT : I.adjoint.comp T.adjoint = A.adjoint.comp I.adjoint := by
    simpa only [LinearMap.adjoint_comp] using congrArg LinearMap.adjoint hTI
  have h1 : (I.adjoint.comp T).comp (T.adjoint.comp I) = A.adjoint.comp A := by
    calc
      _ = I.adjoint.comp ((T.comp T.adjoint).comp I) := by simp only [LinearMap.comp_assoc]
      _ = I.adjoint.comp ((T.adjoint.comp T).comp I) := by rw [hT]
      _ = (I.adjoint.comp T.adjoint).comp (T.comp I) := by simp only [LinearMap.comp_assoc]
      _ = (A.adjoint.comp I.adjoint).comp (I.comp A) := by rw [hIT, hTI]
      _ = A.adjoint.comp A := by
        apply LinearMap.ext
        intro x
        exact congrArg A.adjoint (hIIx (A x))
  have h2 : (I.adjoint.comp T).comp (I.comp A.adjoint) = A.comp A.adjoint := by
    ext x
    simp only [LinearMap.comp_apply, hTIx, hIIx]
  have h3 : (A.comp I.adjoint).comp (T.adjoint.comp I) = A.comp A.adjoint := by
    apply LinearMap.ext
    intro x
    change A (I.adjoint (T.adjoint (I x))) = A (A.adjoint x)
    have hx := DFunLike.congr_fun hIT (I x)
    change I.adjoint (T.adjoint (I x)) = A.adjoint (I.adjoint (I x)) at hx
    rw [hx, hIIx]
  have h4 : (A.comp I.adjoint).comp (I.comp A.adjoint) = A.comp A.adjoint := by
    apply LinearMap.ext
    intro x
    exact congrArg A (hIIx (A.adjoint x))
  have hD : D.adjoint.comp D = A.adjoint.comp A - A.comp A.adjoint := by
    dsimp [D]
    simp only [map_sub, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
      LinearMap.sub_comp, LinearMap.comp_sub]
    rw [h1, h2, h3, h4]
    abel
  have htrace : LinearMap.trace F M (D.adjoint.comp D) = 0 := by
    rw [hD, map_sub, LinearMap.trace_comp_comm' A A.adjoint, sub_self]
  have hz : D = 0 := eq_zero_of_trace_adjoint_comp_self D htrace
  have he : T.adjoint.comp I = I.comp A.adjoint := sub_eq_zero.mp hz
  intro x hx
  have hv := DFunLike.congr_fun he (⟨x, hx⟩ : M)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hv
  change T.adjoint x = (A.adjoint ⟨x, hx⟩ : V) at hv
  rw [hv]
  exact (A.adjoint ⟨x, hx⟩).property



/-- The adjoint identity transports invariance to the perpendicular subspace. -/
theorem orthogonal_invariant_of_adjoint (T : V →ₗ[F] V) (M : Submodule F V)
    (h : ∀ x ∈ M, T.adjoint x ∈ M) : ∀ x ∈ M.orthogonal, T x ∈ M.orthogonal := by
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro y hy
  rw [← LinearMap.adjoint_inner_left T x y]
  exact M.inner_right_of_mem_orthogonal (h y hy) hx

/-- On a subspace preserved by both maps, adjoints restrict to adjoints. -/
theorem adjoint_restriction (T : V →ₗ[F] V) (M : Submodule F V)
    (hM : ∀ x ∈ M, T x ∈ M) (hMa : ∀ x ∈ M, T.adjoint x ∈ M) :
    (T.restrict hM).adjoint = T.adjoint.restrict hMa := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner F (T.adjoint (x : V)) (y : V) = inner F (x : V) (T (y : V))
  exact LinearMap.adjoint_inner_left T y x

/-- Restrict the ambient commutation identity after identifying the adjoint. -/
theorem normal_restriction (T : V →ₗ[F] V) (M : Submodule F V)
    (hT : _root_.D05.normalOperator T)
    (hM : ∀ x ∈ M, T x ∈ M) (hMa : ∀ x ∈ M, T.adjoint x ∈ M) :
    _root_.D05.normalOperator (T.restrict hM) := by
  unfold _root_.D05.normalOperator
  rw [adjoint_restriction T M hM hMa]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun hT (x : V)

/-- Normality is preserved by taking the adjoint, by involutivity alone. -/
theorem normal_adjoint (T : V →ₗ[F] V) (hT : _root_.D05.normalOperator T) :
    _root_.D05.normalOperator T.adjoint := by
  unfold _root_.D05.normalOperator
  rw [LinearMap.adjoint_adjoint]
  exact hT.symm

theorem invariant_and_normal_restrictions :
    Specs.D05.M13.NormalReducing.Subspace.invariant_and_normal_restrictions := by
  intro F V _ _ _ _ T M hT hM
  have hMa := adjoint_invariant T M hT hM
  have hP := orthogonal_invariant_of_adjoint T M hMa
  have hPa : ∀ x ∈ M.orthogonal, T.adjoint x ∈ M.orthogonal := by
    apply orthogonal_invariant_of_adjoint T.adjoint M
    intro x hx
    simpa only [LinearMap.adjoint_adjoint] using hM x hx
  refine ⟨hMa, hP, hPa, normal_restriction T M hT hM hMa,
    normal_restriction T M.orthogonal hT hP hPa, ?_, ?_,
    adjoint_restriction T M hM hMa, adjoint_restriction T M.orthogonal hP hPa⟩

  · apply normal_restriction T.adjoint M (normal_adjoint T hT) hMa
    intro x hx
    simpa only [LinearMap.adjoint_adjoint] using hM x hx
  · apply normal_restriction T.adjoint M.orthogonal (normal_adjoint T hT) hPa
    intro x hx
    simpa only [LinearMap.adjoint_adjoint] using hP x hx

/-- In an orthonormal upper-triangular block matrix, normality kills the other
 off-diagonal block. This exposes the exact AA* + BB* = A*A calculation. -/
theorem block_trace_vanishing :
    Specs.D05.M13.NormalReducing.Subspace.block_trace_vanishing := by
  intro F _ m n _ _ A B C
  dsimp only
  intro h
  classical
  have hblock : A * A.conjTranspose + B * B.conjTranspose = A.conjTranspose * A := by
    have hh := congrArg (fun Q : Matrix (Sum m n) (Sum m n) F => Q.toBlocks₁₁) h
    simpa only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁,
      Matrix.mul_zero, Matrix.zero_mul, add_zero] using hh
  have ht : (B * B.conjTranspose).trace = 0 := by
    have hh := congrArg Matrix.trace hblock
    rw [Matrix.trace_add, Matrix.trace_mul_comm A A.conjTranspose] at hh
    exact add_eq_left.mp hh
  have hsum : (∑ i, ∑ j, ‖B i j‖ ^ 2) = 0 := by
    have hh := congrArg RCLike.re ht
    simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, map_sum, RCLike.star_def, RCLike.mul_conj,
      RCLike.re_ofReal_pow, RCLike.zero_re] using hh
  have hz : B = 0 := by
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖B i j‖))).mp hsum i
        (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg ‖B i j‖)).mp hi j (Finset.mem_univ j)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hij)
  exact ⟨hblock, ht, hsum, hz⟩

end D05.M13.NormalReducing.Subspace
