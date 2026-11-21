import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.SeparableMASA
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.OperatorTopology.DoubleCommutant
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.ScalarMultiplicationCommutant
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.SeparableAbelianSeparating
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.CyclicAbelianScalarRepresentation
import Mathlib.LinearAlgebra.Complex.Module

/-! Cyclic vectors, separating vectors, and the full scalar multiplication
model for separable maximal abelian von Neumann algebras. -/
noncomputable section
open scoped ComplexStarModule

namespace ExpandedFA.VonNeumann.SeparableMASA
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The commutant is a unital star algebra, with exactly the set-theoretic
commutation condition because the original algebra is already star closed. -/
def commutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarSubalgebra.centralizer ℂ (A : Set (H →L[ℂ] H))

@[simp] theorem coe_commutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (commutant A : Set (H →L[ℂ] H)) = Set.centralizer (A : Set (H →L[ℂ] H)) := by
  simp [commutant, StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq]

/-- Cyclicity for an algebra implies separation for every commuting operator.
There is no separability or commutativity hypothesis in this bridge. -/
theorem cyclic_separates_commutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H)
    (he : Spec.IsCyclic A e) : Spec.IsSeparating (commutant A) e := by
  intro T hT hTe
  have hc : T ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
    simpa only [← SetLike.mem_coe, coe_commutant] using hT
  apply ContinuousLinearMap.ext
  have hz : (fun x : H => T x) = fun _ => 0 :=
    he.equalizer T.continuous continuous_const (by
      funext a
      have h := congrArg (fun S : H →L[ℂ] H => S e) (hc a a.property)
      simpa [mul_apply_eq_comp, hTe] using h.symm)
  exact congrFun hz

/-- In particular an abelian algebra's cyclic vector is separating. -/
theorem cyclic_is_separating (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : Spec.IsAbelian A) (e : H) (he : Spec.IsCyclic A e) :
    Spec.IsSeparating A e := by
  intro T hT hTe
  apply cyclic_separates_commutant A e he T _ hTe
  rw [← SetLike.mem_coe, coe_commutant]
  exact fun S hS => hA S hS T hT

/-- Maximality forces any commuting self-adjoint operator into the algebra. -/
theorem selfAdjoint_mem_of_commutes (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : Spec.IsMaximalAbelian A) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hc : T ∈ Set.centralizer (A : Set (H →L[ℂ] H))) : T ∈ A := by
  let s : Set (H →L[ℂ] H) := (A : Set (H →L[ℂ] H)) ∪ {T}
  have hs (x : H →L[ℂ] H) (hx : x ∈ s) : IsStarNormal x := by
    rcases hx with hx | hx
    · exact ⟨hA.1 _ (star_mem hx) _ hx⟩
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact hT.isStarNormal
  have hcomm : s.Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hA.1 x hx y hy
    · rcases Set.mem_singleton_iff.mp hy with rfl
      exact hc x hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact (hc y hy).symm
    · rcases Set.mem_singleton_iff.mp hx with rfl
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact Commute.refl _
  have hstar : ∀ x ∈ s, star x ∈ s := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (star_mem hx)
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact Or.inr (by simpa only [hT.star_eq] using Set.mem_singleton _)
  have hcs : s.Pairwise (Commute · <| star ·) := by
    intro x hx y hy _
    by_cases hxy : x = star y
    · rw [hxy]
    · exact hcomm hx (hstar y hy) hxy
  let B := StarAlgebra.adjoin ℂ s
  have : IsMulCommutative B := StarAlgebra.isMulCommutative_adjoin ℂ hs hcomm hcs
  have hB : Spec.IsAbelian B := fun x hx y hy => setLike_mul_comm hx hy
  have hAB : A ≤ B := fun x hx => StarAlgebra.subset_adjoin ℂ s (Or.inl hx)
  have hBA : B = A := hA.2 B hB hAB
  rw [← hBA]
  exact StarAlgebra.subset_adjoin ℂ s (Or.inr (Set.mem_singleton T))

/-- A maximal abelian star algebra equals its commutant. The decomposition
uses the real and imaginary self-adjoint parts of the actual operator. -/
theorem maximalAbelian_eq_commutant (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : Spec.IsMaximalAbelian A) : commutant A = A := by
  apply le_antisymm
  · intro T hT
    have hc : T ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
      simpa only [← SetLike.mem_coe, coe_commutant] using hT
    have hr : (ℜ T : H →L[ℂ] H) ∈ commutant A := by
      rw [realPart_apply_coe, ← Complex.coe_smul]
      exact (commutant A).smul_mem ((commutant A).add_mem hT (show star T ∈ commutant A from star_mem hT)) _
    have hi : (ℑ T : H →L[ℂ] H) ∈ commutant A := by
      rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
      exact (commutant A).smul_mem
        ((commutant A).smul_mem ((commutant A).sub_mem hT (show star T ∈ commutant A from star_mem hT)) _) _
    have hrA := selfAdjoint_mem_of_commutes A hA _ (ℜ T).property
      (show (ℜ T : H →L[ℂ] H) ∈ Set.centralizer (A : Set (H →L[ℂ] H)) from by
        simpa only [← SetLike.mem_coe, coe_commutant] using hr)
    have hiA := selfAdjoint_mem_of_commutes A hA _ (ℑ T).property
      (show (ℑ T : H →L[ℂ] H) ∈ Set.centralizer (A : Set (H →L[ℂ] H)) from by
        simpa only [← SetLike.mem_coe, coe_commutant] using hi)
    rw [← realPart_add_I_smul_imaginaryPart T]
    exact A.add_mem hrA (A.smul_mem hiA _)
  · intro T hT
    rw [← SetLike.mem_coe, coe_commutant]
    exact fun S hS => hA.1 S hS T hT

/-- The linear orbit map for an arbitrary unital star algebra. -/
def orbitMap (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H) : A →ₗ[ℂ] H where
  toFun a := (a : H →L[ℂ] H) e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The usual closed cyclic subspace in the original Hilbert topology. -/
def cyclicSpace (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H) : Submodule ℂ H :=
  (orbitMap A e).range.topologicalClosure

theorem self_mem_cyclicSpace (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H) :
    e ∈ cyclicSpace A e := by
  apply Submodule.le_topologicalClosure
  exact ⟨1, rfl⟩

theorem cyclicSpace_invariant (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H)
    (T : A) {x : H} (hx : x ∈ cyclicSpace A e) : T.val x ∈ cyclicSpace A e := by
  have h : (orbitMap A e).range.topologicalClosure ≤
      (cyclicSpace A e).comap T.val.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro y ⟨S, rfl⟩
      apply Submodule.le_topologicalClosure
      exact ⟨T * S, rfl⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.val.continuous
  exact h hx

instance cyclicSpace_complete (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H) :
    CompleteSpace (cyclicSpace A e) :=
  inferInstanceAs (CompleteSpace (orbitMap A e).range.topologicalClosure)

/-- The closed cyclic space reduces every element of the star algebra. -/
theorem cyclicSpace_projection_commutes (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H) :
    (cyclicSpace A e).starProjection ∈ commutant A := by
  rw [← SetLike.mem_coe, coe_commutant]
  intro T hT
  symm
  apply OperatorTopology.DoubleCommutantProof.starProjection_commutes_of_invariant
  · exact fun x hx => cyclicSpace_invariant A e ⟨T, hT⟩ hx
  · exact fun x hx => cyclicSpace_invariant A e ⟨star T, star_mem hT⟩ hx

/-- Separation for the commutant forces the original orbit to be dense. -/
theorem separating_commutant_is_cyclic (A : StarSubalgebra ℂ (H →L[ℂ] H)) (e : H)
    (he : Spec.IsSeparating (commutant A) e) : Spec.IsCyclic A e := by
  let P := (cyclicSpace A e).starProjection
  have hP : 1 - P ∈ commutant A :=
    (commutant A).sub_mem (commutant A).one_mem (cyclicSpace_projection_commutes A e)
  have hPe : (1 - P) e = 0 := by
    change e - P e = 0
    exact sub_eq_zero.mpr
      ((Submodule.starProjection_eq_self_iff.mpr (self_mem_cyclicSpace A e)).symm)
  have hzero := he (1 - P) hP hPe
  have htop : cyclicSpace A e = ⊤ := by
    apply top_unique
    intro x _
    have hx := congrArg (fun T : H →L[ℂ] H => T x) hzero
    change x - P x = 0 at hx
    rw [sub_eq_zero.mp hx]
    exact (cyclicSpace A e).starProjection_apply_mem x
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr htop
  exact hd

/-- On a MASA the same vector is cyclic exactly when it is separating.
This equivalence itself does not require separability. -/
theorem maximalAbelian_cyclic_iff_separating (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : Spec.IsMaximalAbelian A) (e : H) : Spec.IsCyclic A e ↔ Spec.IsSeparating A e := by
  refine ⟨cyclic_is_separating A hA.1 e, fun he => ?_⟩
  apply separating_commutant_is_cyclic
  simpa only [maximalAbelian_eq_commutant A hA] using he

/-- Every commutant is closed in the shared WOT. -/
theorem commutant_wotClosed (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Spec.IsWOTClosed (commutant A) := by
  unfold Spec.IsWOTClosed
  rw [coe_commutant]
  exact OperatorTopology.weak_closed_centralizer _

/-- The algebra lies in its double commutant. -/
theorem le_doubleCommutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    A ≤ commutant (commutant A) := by
  intro T hT
  rw [← SetLike.mem_coe, coe_commutant]
  intro S hS
  have hS' : S ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
    simpa only [← SetLike.mem_coe, coe_commutant] using hS
  exact (hS' T hT).symm

/-- The double commutant of an abelian star algebra is abelian. -/
theorem abelian_doubleCommutant (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : Spec.IsAbelian A) : Spec.IsAbelian (commutant (commutant A)) := by
  have hAC : A ≤ commutant A := by
    intro T hT
    rw [← SetLike.mem_coe, coe_commutant]
    exact fun S hS => hA S hS T hT
  have hCA : commutant (commutant A) ≤ commutant A := by
    intro T hT
    rw [← SetLike.mem_coe, coe_commutant] at hT ⊢
    exact fun S hS => hT S (hAC hS)
  intro T hT S hS
  rw [← SetLike.mem_coe, coe_commutant] at hT
  exact (hT S (hCA hS)).symm

/-- Maximal abelian star algebras are automatically WOT closed. -/
theorem maximalAbelian_wotClosed (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : Spec.IsMaximalAbelian A) : Spec.IsWOTClosed A := by
  rw [← maximalAbelian_eq_commutant A hA]
  exact commutant_wotClosed A

/-- In particular our maximality convention is equivalent to maximality
only among WOT-closed abelian unital star algebras, as in the source. -/
theorem masa_iff_wot_maximal (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Spec.IsMASA A ↔ Spec.IsWOTClosed A ∧ Spec.IsAbelian A ∧
      ∀ B : StarSubalgebra ℂ (H →L[ℂ] H), Spec.IsWOTClosed B → Spec.IsAbelian B →
        A ≤ B → B = A := by
  constructor
  · rintro ⟨⟨hA, hmax⟩, hclosed⟩
    exact ⟨hclosed, hA, fun B _ hB hAB => hmax B hB hAB⟩
  · rintro ⟨hclosed, hA, hmax⟩
    refine ⟨⟨hA, ?_⟩, hclosed⟩
    intro B hB hAB
    have hBA := hmax (commutant (commutant B))
      (commutant_wotClosed _) (abelian_doubleCommutant B hB)
      (hAB.trans (le_doubleCommutant B))
    apply le_antisymm
    · rw [← hBA]
      exact le_doubleCommutant B
    · exact hAB

/-- The zero vector is cyclic on a zero Hilbert space, without a
nonzero-vector convention or a unit-vector assumption. -/
theorem zero_cyclic [Subsingleton H] (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Spec.IsCyclic A 0 := by
  apply Function.Surjective.denseRange
  intro x
  exact ⟨0, Subsingleton.elim _ _⟩

/-- Evaluation is faithful on every operator algebra on the zero space. -/
theorem zero_separating [Subsingleton H] (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Spec.IsSeparating A 0 := by
  intro T _ _
  ext x
  exact Subsingleton.elim _ _

/-- The scalar model on a zero Hilbert space uses the actual zero measure.
No positive-mass or nonempty-spectrum assumption enters the theorem. -/
theorem zero_scalarModel [Subsingleton H] (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Spec.HasScalarModel A := by
  let : MeasurableSpace H := ⊥
  let μ : MeasureTheory.Measure H := 0
  have : MeasureTheory.IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have : Subsingleton (MeasureTheory.Lp ℂ 2 μ) := by
    constructor
    intro f g
    apply MeasureTheory.Lp.ext
    simp only [μ, MeasureTheory.ae_zero]
    exact Filter.eventually_bot
  let U : H ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ := {
    LinearEquiv.ofSubsingleton (R := ℂ) H (MeasureTheory.Lp ℂ 2 μ) with
    norm_map' := fun x => by
      rw [Subsingleton.elim x 0, map_zero, norm_zero, norm_zero]
  }
  refine ⟨H, inferInstance, μ, inferInstance, U, ?_⟩
  intro T
  constructor
  · intro _
    exact ⟨0, fun x => Subsingleton.elim _ _⟩
  · intro _
    have hT : T = 0 := by ext x; exact Subsingleton.elim _ _
    rw [hT]
    exact A.zero_mem

/-- Once a unitary makes the algebra act by scalar multiplications,
maximality gives equality with the whole multiplication algebra. In
particular, the analytic representation construction need only establish
the forward intertwining assertion. -/
theorem scalarModel_of_multiplication_representation
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hA : Spec.IsMaximalAbelian A)
    (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (U : H ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (hU : ∀ T ∈ A, ∃ h : MeasureTheory.Lp ℂ ⊤ μ, ∀ x : H,
      U (T x) = ScalarMultiplicationCommutant.Spec.multiplier μ h (U x)) :
    Spec.HasScalarModel A := by
  refine ⟨X, inferInstance, μ, inferInstance, U, fun T => ⟨hU T, ?_⟩⟩
  rintro ⟨h, hT⟩
  rw [← maximalAbelian_eq_commutant A hA]
  rw [← SetLike.mem_coe, coe_commutant]
  intro S hS
  obtain ⟨g, hg⟩ := hU S hS
  ext x
  apply U.injective
  change U (S (T x)) = U (T (S x))
  rw [hg, hT, hT, hg]
  exact congrArg (fun R : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ => R (U x))
    (ScalarMultiplicationCommutant.multipliers_commute μ g h)

/-- This supplies the C*-algebra completeness hypothesis for the scalar
representation construction, using the existing ambient operator norm. -/
theorem maximalAbelian_normClosed (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : Spec.IsMaximalAbelian A) : IsClosed (A : Set (H →L[ℂ] H)) := by
  rw [← maximalAbelian_eq_commutant A hA, coe_commutant]
  exact Set.isClosed_centralizer _

/-- A separating vector for the abelian algebra is cyclic when the algebra
equals its commutant. Separability is used only in constructing that vector. -/
theorem masa_cyclic : Spec.MASACyclic.{u} := by
  intro H _ _ _ _ A hA
  obtain ⟨e, he⟩ := SeparableAbelianSeparating.exists_separating_vector H A hA.1.1
  exact ⟨e, (maximalAbelian_cyclic_iff_separating A hA.1 e).mpr he⟩

/-- The cyclic scalar representation is onto L². Maximality then ensures
that every L∞ multiplier belongs to the transported algebra. -/
theorem masa_scalar_representation : Spec.MASAScalarRepresentation.{u} := by
  intro H _ _ _ _ A hA
  obtain ⟨e, he⟩ := masa_cyclic H A hA
  obtain ⟨X, mX, μ, hμ, U, hU⟩ :=
    CyclicAbelianScalarRepresentation.cyclic_scalar_representation H A hA.1.1
      (maximalAbelian_normClosed A hA.1) e he
  let := mX
  let := hμ
  exact scalarModel_of_multiplication_representation A hA.1 X μ U hU

/-- Every abelian von Neumann algebra on a separable Hilbert space has a
separating vector; the upstream geometric result needs no closure assumption. -/
theorem abelian_separating : Spec.AbelianSeparating.{u} := by
  intro H _ _ _ _ A hA _
  exact SeparableAbelianSeparating.exists_separating_vector H A hA

section RealScalar
variable {HR : Type u} [NormedAddCommGroup HR] [InnerProductSpace ℝ HR]
  [CompleteSpace HR]

/-- Adjoining a commuting self-adjoint real operator preserves abelianness. -/
theorem real_selfAdjoint_mem_of_commutes (A : StarSubalgebra ℝ (HR →L[ℝ] HR))
    (hA : Spec.RealIsMaximalAbelian A) (T : HR →L[ℝ] HR) (hT : IsSelfAdjoint T)
    (hc : T ∈ Set.centralizer (A : Set (HR →L[ℝ] HR))) : T ∈ A := by
  let s : Set (HR →L[ℝ] HR) := (A : Set (HR →L[ℝ] HR)) ∪ {T}
  have hs (x : HR →L[ℝ] HR) (hx : x ∈ s) : IsStarNormal x := by
    rcases hx with hx | hx
    · exact ⟨hA.1 _ (star_mem hx) _ hx⟩
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact hT.isStarNormal
  have hcomm : s.Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hA.1 x hx y hy
    · rcases Set.mem_singleton_iff.mp hy with rfl
      exact hc x hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact (hc y hy).symm
    · rcases Set.mem_singleton_iff.mp hx with rfl
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact Commute.refl _
  have hstar : ∀ x ∈ s, star x ∈ s := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (star_mem hx)
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact Or.inr (by simpa only [hT.star_eq] using Set.mem_singleton _)
  have hcs : s.Pairwise (Commute · <| star ·) := by
    intro x hx y hy _
    by_cases hxy : x = star y
    · rw [hxy]
    · exact hcomm hx (hstar y hy) hxy
  let B := StarAlgebra.adjoin ℝ s
  have : IsMulCommutative B := StarAlgebra.isMulCommutative_adjoin ℝ hs hcomm hcs
  have hB : Spec.RealIsAbelian B := fun x hx y hy => setLike_mul_comm hx hy
  have hAB : A ≤ B := fun x hx => StarAlgebra.subset_adjoin ℝ s (Or.inl hx)
  have hBA : B = A := hA.2 B hB hAB
  rw [← hBA]
  exact StarAlgebra.subset_adjoin ℝ s (Or.inr (Set.mem_singleton T))

/-- The actual real commutant, with no complex structure on HR. -/
def real_commutant (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) :
    StarSubalgebra ℝ (HR →L[ℝ] HR) :=
  StarSubalgebra.centralizer ℝ (A : Set (HR →L[ℝ] HR))

@[simp] theorem coe_real_commutant (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) :
    (real_commutant A : Set (HR →L[ℝ] HR)) =
      Set.centralizer (A : Set (HR →L[ℝ] HR)) := by
  simp [real_commutant, StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq]

theorem real_commutant_wotClosed (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) :
    Spec.RealIsWOTClosed (real_commutant A) := by
  unfold Spec.RealIsWOTClosed
  rw [coe_real_commutant]
  exact OperatorTopology.weak_closed_centralizer _

theorem real_le_doubleCommutant (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) :
    A ≤ real_commutant (real_commutant A) := by
  intro T hT
  rw [← SetLike.mem_coe, coe_real_commutant]
  intro S hS
  have hS' : S ∈ Set.centralizer (A : Set (HR →L[ℝ] HR)) := by
    simpa only [← SetLike.mem_coe, coe_real_commutant] using hS
  exact (hS' T hT).symm

theorem real_abelian_doubleCommutant (A : StarSubalgebra ℝ (HR →L[ℝ] HR))
    (hA : Spec.RealIsAbelian A) :
    Spec.RealIsAbelian (real_commutant (real_commutant A)) := by
  have hAC : A ≤ real_commutant A := by
    intro T hT
    rw [← SetLike.mem_coe, coe_real_commutant]
    exact fun S hS => hA S hS T hT
  have hCA : real_commutant (real_commutant A) ≤ real_commutant A := by
    intro T hT
    rw [← SetLike.mem_coe, coe_real_commutant] at hT ⊢
    exact fun S hS => hT S (hAC hS)
  intro T hT S hS
  rw [← SetLike.mem_coe, coe_real_commutant] at hT
  exact (hT S (hCA hS)).symm

/-- The real maximality convention also covers maximality only among
WOT-closed abelian real star algebras. -/
theorem real_masa_iff_wot_maximal (A : StarSubalgebra ℝ (HR →L[ℝ] HR)) :
    Spec.RealIsMASA A ↔ Spec.RealIsWOTClosed A ∧ Spec.RealIsAbelian A ∧
      ∀ B : StarSubalgebra ℝ (HR →L[ℝ] HR),
        Spec.RealIsWOTClosed B → Spec.RealIsAbelian B → A ≤ B → B = A := by
  constructor
  · rintro ⟨⟨hA, hmax⟩, hclosed⟩
    exact ⟨hclosed, hA, fun B _ hB hAB => hmax B hB hAB⟩
  · rintro ⟨hclosed, hA, hmax⟩
    refine ⟨⟨hA, ?_⟩, hclosed⟩
    intro B hB hAB
    have hBA := hmax (real_commutant (real_commutant B))
      (real_commutant_wotClosed _) (real_abelian_doubleCommutant B hB)
      (hAB.trans (real_le_doubleCommutant B))
    apply le_antisymm
    · rw [← hBA]
      exact real_le_doubleCommutant B
    · exact hAB

/-- The projection onto the real cyclic subspace commutes with A and is
self-adjoint, so maximality puts it in A. Separation then makes it the identity. -/
theorem real_cyclic_of_separating (A : StarSubalgebra ℝ (HR →L[ℝ] HR))
    (hA : Spec.RealIsMaximalAbelian A) (e : HR)
    (he : Spec.RealIsSeparating A e) : Spec.RealIsCyclic A e := by
  let K := SeparableAbelianSeparating.cyclicSpace A e
  let P := K.starProjection
  have hP : P ∈ A := by
    apply real_selfAdjoint_mem_of_commutes A hA P (isSelfAdjoint_starProjection K)
    intro T hT
    exact (SeparableAbelianSeparating.cyclicProjection_commutes A e ⟨T, hT⟩).symm
  have hPe : (1 - P) e = 0 := by
    change e - P e = 0
    exact sub_eq_zero.mpr
      ((Submodule.starProjection_eq_self_iff.mpr
        (SeparableAbelianSeparating.self_mem_cyclicSpace A e)).symm)
  have hzero := he (1 - P) (A.sub_mem A.one_mem hP) hPe
  have htop : K = ⊤ := by
    apply top_unique
    intro x _
    have hx := congrArg (fun T : HR →L[ℝ] HR => T x) hzero
    change x - P x = 0 at hx
    rw [sub_eq_zero.mp hx]
    exact K.starProjection_apply_mem x
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htop

/-- Real MASA cyclicity on the original real space, including the zero space. -/
theorem real_masa_cyclic : Spec.RealMASACyclic.{u} := by
  intro H _ _ _ _ A hA
  obtain ⟨e, he⟩ := SeparableAbelianSeparating.exists_real_separating_vector H A hA.1.1
  exact ⟨e, real_cyclic_of_separating A hA.1 e he⟩

/-- The upstream real geometric theorem needs no closedness hypothesis. -/
theorem real_abelian_separating : Spec.RealAbelianSeparating.{u} := by
  intro H _ _ _ _ A hA _
  exact SeparableAbelianSeparating.exists_real_separating_vector H A hA

end RealScalar

end ExpandedFA.VonNeumann.SeparableMASA
