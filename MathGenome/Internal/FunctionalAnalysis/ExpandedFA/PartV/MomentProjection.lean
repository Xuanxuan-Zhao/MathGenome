import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.MomentProjection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Adjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection

/-!
Exact moment projection (`paper.tex:23091–23126`). The finite equations are
orthogonality against A*V, so their solution is the native orthogonal projector.
The moment matrix is the Gram matrix of the independent vectors A*b_i.
For density, the orthogonal complement of A*(sup V_n) is the preimage under A
of (sup V_n)ᗮ = ker A*. The identity ker(A*A) = ker A then finishes the argument.
Monotone projection convergence is applied to precisely this closed supremum.
-/
noncomputable section
open scoped InnerProductSpace Topology ComplexOrder

namespace ExpandedFA.PartV.MomentProjection
universe u v w z
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
  [CompleteSpace X] [CompleteSpace Y]

open Spec (trialSpace momentOperator momentMatrix)

theorem adjoint_injective : Spec.AdjointInjective.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V hV y z h
  change A.adjoint (y : Y) = A.adjoint (z : Y) at h
  apply Subtype.ext
  have hk : (y : Y) - (z : Y) ∈ A.adjoint.ker := by
    change A.adjoint ((y : Y) - z) = 0
    rw [map_sub, h, sub_self]
  have ho := hV (V.sub_mem y.prop z.prop)
  have hzero := ho _ hk
  rw [inner_self_eq_zero] at hzero
  exact sub_eq_zero.mp hzero

/-- Testing a projection against a vector in its range removes the projector. -/
theorem inner_projected_moment (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 V] (y t : V) :
    ⟪(y : Y), V.starProjection (A (A.adjoint t))⟫_𝕜 =
      ⟪A.adjoint y, A.adjoint t⟫_𝕜 := by
  rw [← V.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr y.prop,
    ← A.adjoint_inner_left]

theorem moment_quadratic : Spec.MomentQuadratic.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hV y
  have hi : ⟪(y : Y), V.starProjection (A (A.adjoint y))⟫_𝕜 =
      (‖A.adjoint y‖ ^ 2 : ℝ) := by
    rw [inner_projected_moment, inner_self_eq_norm_sq_to_K]
    simp only [map_pow]
  refine ⟨hi, ?_⟩
  intro hy
  rw [hi, RCLike.ofReal_re]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hzero
  apply hy
  apply adjoint_injective A V hV
  simpa using hzero

theorem moment_matrix_positive :
    Spec.MomentMatrixPositive.{u, v, w, z} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hV ι _ _ b
  let T : V →ₗ[𝕜] X := A.adjoint.toLinearMap.comp V.subtype
  have hT : Function.Injective T := adjoint_injective A V hV
  have hli : LinearIndependent 𝕜 (fun i => A.adjoint (b i : Y)) :=
    b.toBasis.linearIndependent.map' T (LinearMap.ker_eq_bot.mpr hT)
  have hgram : momentMatrix A V b = Matrix.gram 𝕜 (fun i => A.adjoint (b i : Y)) := by
    ext i j
    exact inner_projected_moment A V (b i) (b j)
  have hpd : (momentMatrix A V b).PosDef := by
    rw [hgram]
    exact Matrix.posDef_gram_of_linearIndependent hli
  exact ⟨hpd, hpd.isUnit⟩

theorem moment_operator_bijective :
    Spec.MomentOperatorBijective.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hV
  have hzero (y : V) (hy : momentOperator A V y = 0) : y = 0 := by
    by_contra hne
    have hp := (moment_quadratic A V hV y).2 hne
    have hproj : V.starProjection (A (A.adjoint y)) = 0 :=
      congrArg (fun t : V => (t : Y)) hy
    rw [hproj, inner_zero_right, RCLike.zero_re] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  have hinj : Function.Injective (momentOperator A V) := by
    intro y t hyt
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hyt, sub_self]
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The residual is tested in Y, with the adjoint transferring it to X. -/
theorem projected_equation_iff_orthogonal (A : X →L[𝕜] Y)
    (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V] (x z : X) :
    V.starProjection (A z) = V.starProjection (A x) ↔
      x - z ∈ (trialSpace A V).orthogonal := by
  constructor
  · intro h u hu
    rcases hu with ⟨y, hy, rfl⟩
    change ⟪A.adjoint y, x - z⟫_𝕜 = 0
    rw [A.adjoint_inner_left]
    have hp : V.starProjection (A (x - z)) = 0 := by
      rw [map_sub, map_sub, h, sub_self]
    exact (V.starProjection_apply_eq_zero_iff.mp hp) y hy
  · intro h
    have hp : V.starProjection (A (x - z)) = 0 := by
      apply V.starProjection_apply_eq_zero_iff.mpr
      intro y hy
      rw [← A.adjoint_inner_left]
      exact h _ ⟨y, hy, rfl⟩
    exact (sub_eq_zero.mp (by simpa only [map_sub] using hp)).symm

theorem equation_iff_projection :
    Spec.EquationIffProjection.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ x z
  constructor
  · rintro ⟨hz, heq⟩
    exact Submodule.eq_starProjection_of_mem_orthogonal hz
      ((projected_equation_iff_orthogonal A V x z).mp heq) |>.symm
  · intro hz
    subst z
    exact ⟨(trialSpace A V).starProjection_apply_mem x,
      (projected_equation_iff_orthogonal A V x _).mpr
        ((trialSpace A V).sub_starProjection_mem_orthogonal x)⟩

/-- Orthogonal complement of the image under the adjoint, in exact native types. -/
theorem orthogonal_adjoint_image (A : X →L[𝕜] Y) (U : Submodule 𝕜 Y) :
    (U.map A.adjoint.toLinearMap).orthogonal = U.orthogonal.comap A.toLinearMap := by
  ext x
  constructor
  · intro hx y hy
    change ⟪y, A x⟫_𝕜 = 0
    rw [← A.adjoint_inner_left]
    exact hx _ ⟨y, hy, rfl⟩
  · intro hx u hu
    rcases hu with ⟨y, hy, rfl⟩
    change ⟪A.adjoint y, x⟫_𝕜 = 0
    rw [A.adjoint_inner_left]
    exact hx y hy

theorem trial_space_density :
    Spec.TrialSpaceDensity.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hdense
  have horth : (⨆ n, V n).orthogonal = A.adjoint.ker := by
    rw [← Submodule.orthogonal_closure, hdense, Submodule.orthogonal_orthogonal]
  have hker : A.adjoint.ker.comap A.toLinearMap = A.ker := by
    change (A.adjoint.comp A).ker = A.ker
    exact A.ker_adjoint_comp_self
  change (⨆ n, (V n).map A.adjoint.toLinearMap).topologicalClosure = _
  rw [← Submodule.map_iSup, ← Submodule.orthogonal_orthogonal_eq_closure,
    orthogonal_adjoint_image, horth, hker]

omit [CompleteSpace Y] in
/-- Directed suprema of submodules really are their set-theoretic unions. -/
theorem closure_union_eq_closed_sup (V : ℕ → Submodule 𝕜 Y) (hmono : Monotone V) :
    closure (⋃ n, (V n : Set Y)) = ((⨆ n, V n).topologicalClosure : Set Y) := by
  rw [Submodule.topologicalClosure_coe,
    Submodule.coe_iSup_of_directed V hmono.directed_le]

/-- Converts the source's literal union-density hypothesis to the native submodule form. -/
theorem closed_sup_of_dense_union (A : X →L[𝕜] Y) (V : ℕ → Submodule 𝕜 Y)
    (hmono : Monotone V)
    (hdense : closure (⋃ n, (V n : Set Y)) = (A.adjoint.ker.orthogonal : Set Y)) :
    (⨆ n, V n).topologicalClosure = A.adjoint.ker.orthogonal := by
  apply SetLike.coe_injective
  rw [← closure_union_eq_closed_sup V hmono]
  exact hdense

theorem stage_properties : Spec.StageProperties.{u, v, w, z} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hmono hdense n
  have hd := closed_sup_of_dense_union A V hmono hdense
  have hn : V n ≤ A.adjoint.ker.orthogonal := by
    rw [← hd]
    exact (le_iSup V n).trans (⨆ n, V n).le_topologicalClosure
  exact ⟨hn, adjoint_injective A (V n) hn, moment_operator_bijective A (V n) hn,
    fun ι _ _ b => moment_matrix_positive A (V n) hn ι b⟩

theorem trial_union_density : Spec.TrialUnionDensity.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V hmono hdense
  have hm : Monotone (fun n => trialSpace A (V n)) :=
    fun i j hij => Submodule.map_mono (hmono hij)
  rw [closure_union_eq_closed_sup _ hm,
    trial_space_density A V hmono (closed_sup_of_dense_union A V hmono hdense)]

theorem moment_projection : Spec.ExactDataProjection.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A V _ hmono hdense f x hf hx
  have hdense' := closed_sup_of_dense_union A V hmono hdense
  subst f
  refine ⟨?_, ?_, ?_⟩
  · intro n
    refine ⟨(trialSpace A (V n)).starProjection x,
      (equation_iff_projection A (V n) x _).mpr rfl, ?_⟩
    intro z hz
    exact (equation_iff_projection A (V n) x z).mp hz
  · intro n z hz heq
    exact (equation_iff_projection A (V n) x z).mp ⟨hz, heq⟩
  · have hm : Monotone (fun n => trialSpace A (V n)) :=
      fun i j hij => Submodule.map_mono (hmono hij)
    have hd := trial_space_density A V hmono hdense'
    have hs : (⨆ n, trialSpace A (V n)).topologicalClosure.starProjection x = x :=
      Submodule.starProjection_eq_self_iff.mpr (by rw [hd]; exact hx)
    simpa only [hs] using
      Submodule.starProjection_tendsto_closure_iSup (fun n => trialSpace A (V n)) hm x

theorem zero_stage : Spec.ZeroStage.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A x
  simp [trialSpace]

end ExpandedFA.PartV.MomentProjection
