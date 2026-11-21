import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompactCartanConjugacy
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClosedMatrixGroups
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InnerDerivations
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ReductiveDecomposition
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Order.Compact

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing

attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup
attribute [local instance]
  LieAlgebrasAndRepresentations.CompactCartanConjugacy.coreInnerProductSpace

namespace LieAlgebrasAndRepresentations.CompactCartanConjugacy

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  [InnerProductSpace.Core ℝ L] [FiniteDimensional ℝ L]

local instance : IsTopologicalRing (L →L[ℝ] L) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (inferInstance : NonUnitalSeminormedRing (L →L[ℝ] L))

lemma abelian_bracket {T : LieSubalgebra ℝ L} (hT : IsLieAbelian T)
    {x y : L} (hx : x ∈ T) (hy : y ∈ T) : ⁅x, y⁆ = 0 := by
  exact congrArg Subtype.val (hT.trivial (⟨x, hx⟩ : T) (⟨y, hy⟩ : T))

/-- Maximal abelian subalgebras are self-centralizing. -/
theorem mem_of_centralizes {T : LieSubalgebra ℝ L}
    (hT : Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T)
    {x : L} (hx : ∀ y ∈ T, ⁅y, x⁆ = 0) : x ∈ T := by
  let S := LieSubalgebra.lieSpan ℝ L (insert x (T : Set L))
  have hS : IsLieAbelian S := by
    apply LieSubalgebra.isLieAbelian_lieSpan_iff.mpr
    intro y hy z hz
    rcases hy with rfl | hy <;> rcases hz with rfl | hz
    · exact lie_self _
    · rw [← lie_skew, hx _ hz, neg_zero]
    · exact hx _ hy
    · exact abelian_bracket hT.prop hy hz
  have hTS : T ≤ S := fun y hy => LieSubalgebra.subset_lieSpan (Set.mem_insert_of_mem x hy)
  exact hT.2 hS hTS (LieSubalgebra.subset_lieSpan (Set.mem_insert x _))

/-- For a skew-adjoint real operator the generalized zero eigenspace is
its kernel. This proof uses positivity, without any spectral theorem. -/
theorem apply_eq_zero_of_pow_eq_zero (A : Module.End ℝ L)
    (hA : ∀ x y : L, inner ℝ (A x) y = -inner ℝ x (A y))
    (n : ℕ) (x : L) (hx : (A ^ n) x = 0) : A x = 0 := by
  induction n generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this]
  | succ n ih =>
    have hAx : A (A x) = 0 := ih (A x) (by
      simpa only [pow_succ, Module.End.mul_apply] using hx)
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hA, hAx, inner_zero_right, neg_zero]

/-- Every maximal abelian subalgebra contains a regular element. The
minimal Engel subalgebra is selected within this particular subalgebra. -/
theorem exists_regular
    (hInv : ∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆)
    (T : LieSubalgebra ℝ L)
    (hT : Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T) :
    ∃ x ∈ T, ∀ y : L, ⁅x, y⁆ = 0 ↔ y ∈ T := by
  classical
  let p : ℕ → Prop := fun n => ∃ x ∈ T, Module.finrank ℝ (LieSubalgebra.engel ℝ x) = n
  have hp : ∃ n, p n := ⟨_, 0, T.zero_mem, rfl⟩
  obtain ⟨x, hx, hdim⟩ := Nat.find_spec hp
  have hle (y : L) (hy : y ∈ T) : T ≤ LieSubalgebra.engel ℝ y := by
    intro z hz
    exact (LieSubalgebra.mem_engel_iff ℝ y z).mpr
      ⟨1, by simpa using abelian_bracket hT.prop hy hz⟩
  let E : {E : LieSubalgebra ℝ L | ∃ x ∈ T, LieSubalgebra.engel ℝ x = E} :=
    ⟨LieSubalgebra.engel ℝ x, x, hx, rfl⟩
  have hmin : IsMin E := by
    rintro ⟨_, y, hy, rfl⟩ h
    have hdim' : Module.finrank ℝ (LieSubalgebra.engel ℝ x) ≤
        Module.finrank ℝ (LieSubalgebra.engel ℝ y) := by
      rw [hdim]
      exact Nat.find_min' hp ⟨y, hy, rfl⟩
    have heq := LieSubalgebra.toSubmodule_injective
      (Submodule.eq_of_le_of_finrank_le h hdim')
    exact heq.ge
  have hbot := LieAlgebra.engel_isBot_of_isMin
    (Cardinal.natCast_le_aleph0.trans (Cardinal.infinite_iff.mp (inferInstance : Infinite ℝ)))
    T E (hle x hx) hmin
  have hcentral (z : L) (hz : z ∈ LieSubalgebra.engel ℝ x) : z ∈ T := by
    apply mem_of_centralizes hT
    intro y hy
    have hz' := hbot (⟨LieSubalgebra.engel ℝ y, y, hy, rfl⟩) hz
    obtain ⟨n, hn⟩ := (LieSubalgebra.mem_engel_iff ℝ y z).mp hz'
    exact apply_eq_zero_of_pow_eq_zero (LieAlgebra.ad ℝ L y) (hInv y) n z hn
  refine ⟨x, hx, fun y => ⟨fun hy => ?_, fun hy => abelian_bracket hT.prop hx hy⟩⟩
  apply hcentral
  exact (LieSubalgebra.mem_engel_iff ℝ x y).mpr ⟨1, by simpa using hy⟩


@[simp] lemma adContinuous_apply (z x : L) : adContinuous z x = ⁅z, x⁆ := rfl

@[simp] lemma adContinuous_neg (z : L) : adContinuous (-z) = -adContinuous z := by
  ext x
  simp

@[simp] lemma innerProduct_nil : innerProduct ([] : List L) = 1 := rfl

@[simp] lemma innerProduct_cons (z : L) (zs : List L) :
    innerProduct (z :: zs) = ClosedMatrixGroups.expUnit (adContinuous z) * innerProduct zs := rfl

lemma innerProduct_append (xs ys : List L) :
    innerProduct (xs ++ ys) = innerProduct xs * innerProduct ys := by
  simp [innerProduct, List.prod_append]

lemma exp_ad_neg (z : L) :
    ClosedMatrixGroups.expUnit (adContinuous (-z)) =
      (ClosedMatrixGroups.expUnit (adContinuous z))⁻¹ := by
  apply Units.ext
  simp only [ClosedMatrixGroups.coe_expUnit, ClosedMatrixGroups.coe_expUnit_inv,
    adContinuous_neg]

lemma innerProduct_inverse (zs : List L) :
    innerProduct (zs.reverse.map Neg.neg) = (innerProduct zs)⁻¹ := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    rw [List.reverse_cons, List.map_append, innerProduct_append, ih]
    simp only [List.map_cons, List.map_nil, innerProduct_cons, innerProduct_nil,
      mul_one, exp_ad_neg, mul_inv_rev]

/-- Algebraic generation is exactly finite multiplication of adjoint
exponentials; inverse factors are exponentials of negative elements. -/
theorem mem_innerGroup_iff (g : (L →L[ℝ] L)ˣ) :
    g ∈ innerGroup (L := L) ↔ ∃ zs : List L, innerProduct zs = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨z, rfl⟩ := hg
      exact ⟨[z], by simp⟩
    | one => exact ⟨[], rfl⟩
    | mul g h _ _ hg hh =>
      obtain ⟨xs, rfl⟩ := hg
      obtain ⟨ys, rfl⟩ := hh
      exact ⟨xs ++ ys, innerProduct_append xs ys⟩
    | inv g _ hg =>
      obtain ⟨zs, rfl⟩ := hg
      exact ⟨zs.reverse.map Neg.neg, innerProduct_inverse zs⟩
  · rintro ⟨zs, rfl⟩
    induction zs with
    | nil => exact (innerGroup (L := L)).one_mem
    | cons z zs ih =>
      exact (innerGroup (L := L)).mul_mem (Subgroup.subset_closure ⟨z, rfl⟩) ih

/-- The algebraic end of the maximum argument: commuting regular elements
force equality of the transported maximal abelian subalgebras. -/
theorem image_eq_of_regular_commute
    {T₁ T₂ : LieSubalgebra ℝ L}
    (hT₁ : IsLieAbelian T₁)
    (hT₂ : Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₂)
    {x y : L} (hx : x ∈ T₁) (hy : y ∈ T₂)
    (hregX : ∀ z : L, ⁅x, z⁆ = 0 ↔ z ∈ T₁)
    (hregY : ∀ z : L, ⁅y, z⁆ = 0 ↔ z ∈ T₂)
    (g : L ≃ₗ⁅ℝ⁆ L) (hcomm : ⁅g x, y⁆ = 0) :
    g '' (T₁ : Set L) = (T₂ : Set L) := by
  have hgx : g x ∈ T₂ := (hregY _).mp (by rw [← lie_skew, hcomm, neg_zero])
  have hle : T₂ ≤ T₁.map g.toLieHom := by
    intro z hz
    apply (LieSubalgebra.mem_map _ _ _).mpr
    refine ⟨g.symm z, (hregX _).mp ?_, g.apply_symm_apply z⟩
    apply g.injective
    change g ⁅x, g.symm z⁆ = g 0
    rw [map_zero, g.map_lie, g.apply_symm_apply]
    exact abelian_bracket hT₂.prop hgx hz
  have hab : IsLieAbelian (T₁.map g.toLieHom) := by
    constructor
    intro a b
    apply Subtype.ext
    obtain ⟨a', ha', heqa⟩ := (LieSubalgebra.mem_map _ _ _).mp a.property
    obtain ⟨b', hb', heqb⟩ := (LieSubalgebra.mem_map _ _ _).mp b.property
    change ⁅(a : L), (b : L)⁆ = 0
    rw [← heqa, ← heqb, ← g.toLieHom.map_lie, abelian_bracket hT₁ ha' hb', map_zero]
  have heq : T₁.map g.toLieHom = T₂ := le_antisymm (hT₂.2 hab hle) hle
  exact congrArg (fun T : LieSubalgebra ℝ L => (T : Set L)) heq

@[simp] lemma zero_smul_adContinuous (z : L) :
    (0 : ℝ) • adContinuous z = (0 : L →L[ℝ] L) := by
  ext a
  change (0 : ℝ) • ⁅z, a⁆ = 0
  exact zero_smul ℝ _

/-- At a maximum of the adjoint orbit pairing, the two elements commute.
Only the explicitly displayed one-parameter inequalities are needed. -/
theorem commute_of_maximum
    (hInv : ∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆)
    (x y : L)
    (hmax : ∀ z : L, ∀ t : ℝ,
      inner ℝ ((NormedSpace.exp (t • adContinuous z) : L →L[ℝ] L) x) y ≤ inner ℝ x y) :
    ⁅x, y⁆ = 0 := by
  have hd (z : L) :
      HasDerivAt (fun t : ℝ => inner ℝ ((NormedSpace.exp (t • adContinuous z) : L →L[ℝ] L) x) y)
        (inner ℝ ⁅z, x⁆ y) 0 := by
    have he : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • adContinuous z))
        (adContinuous z) 0 := by
      simpa only [zero_smul_adContinuous, NormedSpace.exp_zero, one_mul,
        one_apply_eq_self] using hasDerivAt_exp_smul_const (𝕂 := ℝ) (adContinuous z) 0
    have hx := he.clm_apply (hasDerivAt_const (0 : ℝ) x)
    simpa using hx.inner ℝ (hasDerivAt_const (0 : ℝ) y)
  have hzero (z : L) : inner ℝ ⁅z, x⁆ y = 0 := by
    apply IsLocalMax.hasDerivAt_eq_zero _ (hd z)
    have hh : IsMaxOn
        (fun t : ℝ => inner ℝ ((NormedSpace.exp (t • adContinuous z) : L →L[ℝ] L) x) y)
        Set.univ 0 := by
      apply isMaxOn_univ_iff.mpr
      simpa only [zero_smul_adContinuous, NormedSpace.exp_zero, one_mul,
        one_apply_eq_self] using hmax z
    exact hh.isLocalMax (by simp)
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hi := hInv x ⁅x, y⁆ y
  rw [← lie_skew x ⁅x, y⁆, inner_neg_left, hzero, neg_zero] at hi
  exact (neg_eq_zero.mp hi.symm)

/-- Maximize on any compact matrix subgroup containing the adjoint
one-parameter groups. This produces a commuting conjugate. -/
theorem exists_commuting_conjugate
    (hInv : ∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆)
    (H : Subgroup (L →L[ℝ] L)ˣ) (hH : IsCompact (H : Set (L →L[ℝ] L)ˣ))
    (hExp : ∀ z : L, ClosedMatrixGroups.expUnit (adContinuous z) ∈ H)
    (x y : L) : ∃ g ∈ H, ⁅(g : L →L[ℝ] L) x, y⁆ = 0 := by
  let f : (L →L[ℝ] L)ˣ → ℝ := fun g => inner ℝ ((g : L →L[ℝ] L) x) y
  have hf : Continuous f := by
    exact (Continuous.clm_apply Units.continuous_val continuous_const).inner continuous_const
  obtain ⟨g, hg, hmax⟩ := hH.exists_isMaxOn ⟨1, H.one_mem⟩ hf.continuousOn
  refine ⟨g, hg, commute_of_maximum hInv _ y ?_⟩
  intro z t
  have hsmul : adContinuous (t • z) = t • adContinuous z := by ext a; simp
  have hh := isMaxOn_iff.mp hmax
    (ClosedMatrixGroups.expUnit (adContinuous (t • z)) * g) (H.mul_mem (hExp _) hg)
  simpa only [f, Units.val_mul, mul_apply_eq_comp,
    ClosedMatrixGroups.coe_expUnit, hsmul] using hh

/-- All analytic and regular-element work for the source theorem is
assembled here. The remaining hypotheses concern the compact inner group,
not the desired conjugacy conclusion. -/
theorem conjugacy_of_compact_group
    (hInv : ∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆)
    (H : Subgroup (L →L[ℝ] L)ˣ) (hH : IsCompact (H : Set (L →L[ℝ] L)ˣ))
    (hExp : ∀ z : L, ClosedMatrixGroups.expUnit (adContinuous z) ∈ H)
    (hLie : ∀ g ∈ H, ∀ x y : L,
      (g : L →L[ℝ] L) ⁅x, y⁆ = ⁅(g : L →L[ℝ] L) x, (g : L →L[ℝ] L) y⁆)
    (hInner : H ≤ innerGroup (L := L))
    (T₁ T₂ : LieSubalgebra ℝ L)
    (hT₁ : Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₁)
    (hT₂ : Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₂) :
    ∃ zs : List L,
      (fun x : L => (innerProduct zs : L →L[ℝ] L) x) '' (T₁ : Set L) = (T₂ : Set L) := by
  obtain ⟨x, hx, hregX⟩ := exists_regular hInv T₁ hT₁
  obtain ⟨y, hy, hregY⟩ := exists_regular hInv T₂ hT₂
  obtain ⟨g, hg, hcomm⟩ := exists_commuting_conjugate hInv H hH hExp x y
  let e : L ≃ₗ⁅ℝ⁆ L :=
    { (ContinuousLinearEquiv.ofUnit g).toLinearEquiv with
      map_lie' := fun {x y} => hLie g hg x y }
  have heq := image_eq_of_regular_commute hT₁.prop hT₂ hx hy hregX hregY e hcomm
  obtain ⟨zs, hzs⟩ := (mem_innerGroup_iff g).mp (hInner hg)
  refine ⟨zs, ?_⟩
  change (fun a => (innerProduct zs : L →L[ℝ] L) a) '' (T₁ : Set L) = (T₂ : Set L)
  rw [hzs]
  exact heq


/-- The closed-matrix-group theorem turns the identification of velocities
with adjoint operators into algebraic, finite inner generation of the
identity component. This is the final group-theoretic assembly. -/
theorem conjugacy_of_compact_automorphisms
    (hInv : ∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆)
    (H : Subgroup (L →L[ℝ] L)ˣ) (hH : IsCompact (H : Set (L →L[ℝ] L)ˣ))
    (hExp : ∀ z : L, ClosedMatrixGroups.expUnit (adContinuous z) ∈ H)
    (hLie : ∀ g ∈ H, ∀ x y : L,
      (g : L →L[ℝ] L) ⁅x, y⁆ = ⁅(g : L →L[ℝ] L) x, (g : L →L[ℝ] L) y⁆)
    (hVel : ∀ X : L →L[ℝ] L, X ∈ ClosedMatrixGroups.velocities H →
      ∃ z : L, adContinuous z = X)
    (T₁ T₂ : LieSubalgebra ℝ L)
    (hT₁ : Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₁)
    (hT₂ : Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₂) :
    ∃ zs : List L,
      (fun x : L => (innerProduct zs : L →L[ℝ] L) x) '' (T₁ : Set L) = (T₂ : Set L) := by
  let K := (Subgroup.connectedComponentOfOne H).map H.subtype
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have hK : IsCompact (K : Set (L →L[ℝ] L)ˣ) := by
    change IsCompact (H.subtype '' (connectedComponent (1 : H)))
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hgen : ClosedMatrixGroups.exponentialSubgroup (A := L →L[ℝ] L) H ≤
      (innerGroup (L := L)).comap H.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨X, rfl⟩
    obtain ⟨z, hz⟩ := hVel X.val X.property
    change ClosedMatrixGroups.expUnit X.val ∈ innerGroup (L := L)
    rw [← hz]
    exact Subgroup.subset_closure ⟨z, rfl⟩
  have hKI : K ≤ innerGroup (L := L) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← ClosedMatrixGroups.exponentialSubgroup_eq_identityComponent (A := L →L[ℝ] L) H hH.isClosed] at hg
    exact hgen hg
  apply conjugacy_of_compact_group hInv K hK ?_ ?_ hKI T₁ T₂ hT₁ hT₂
  · intro z
    have hv : adContinuous z ∈ ClosedMatrixGroups.velocities H := by
      intro t
      have hs : adContinuous (t • z) = t • adContinuous z := by ext a; simp
      rw [← hs]
      exact hExp (t • z)
    exact ⟨ClosedMatrixGroups.expIn H ⟨adContinuous z, hv⟩,
      ClosedMatrixGroups.expIn_mem_identityComponent (A := L →L[ℝ] L) H
        ⟨adContinuous z, hv⟩, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩ x y
    exact hLie g.val g.property x y

/-- Orthogonal Lie automorphisms fixing the center pointwise, in the
ordinary topology on units of the endomorphism algebra. -/
def orthogonalAutGroup : Subgroup (L →L[ℝ] L)ˣ where
  carrier := {g | (∀ x : L, ‖(g : L →L[ℝ] L) x‖ = ‖x‖) ∧
    (∀ x y : L, (g : L →L[ℝ] L) ⁅x, y⁆ = ⁅(g : L →L[ℝ] L) x, (g : L →L[ℝ] L) y⁆) ∧
    (∀ z ∈ LieAlgebra.center ℝ L, (g : L →L[ℝ] L) z = z)}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hgN, hgB, hgZ⟩ ⟨hhN, hhB, hhZ⟩
    refine ⟨fun x => ?_, fun x y => ?_, fun z hz => ?_⟩
    · change ‖(g : L →L[ℝ] L) ((h : L →L[ℝ] L) x)‖ = ‖x‖
      rw [hgN, hhN]
    · change (g : L →L[ℝ] L) ((h : L →L[ℝ] L) ⁅x, y⁆) = _
      rw [hhB, hgB]; rfl
    · change (g : L →L[ℝ] L) ((h : L →L[ℝ] L) z) = z
      rw [hhZ z hz, hgZ z hz]
  inv_mem' := by
    rintro g ⟨hgN, hgB, hgZ⟩
    let e := ContinuousLinearEquiv.ofUnit g
    have he (x : L) : (g : L →L[ℝ] L) (((g⁻¹ : (L →L[ℝ] L)ˣ) : L →L[ℝ] L) x) = x :=
      e.apply_symm_apply x
    refine ⟨fun x => ?_, fun x y => ?_, fun z hz => ?_⟩
    · simpa only [he] using (hgN (((g⁻¹ : (L →L[ℝ] L)ˣ) : L →L[ℝ] L) x)).symm
    · apply e.injective
      change (g : L →L[ℝ] L) (((g⁻¹ : (L →L[ℝ] L)ˣ) : L →L[ℝ] L) ⁅x, y⁆) =
        (g : L →L[ℝ] L) ⁅((g⁻¹ : (L →L[ℝ] L)ˣ) : L →L[ℝ] L) x, ((g⁻¹ : (L →L[ℝ] L)ˣ) : L →L[ℝ] L) y⁆
      rw [he, hgB, he, he]
    · apply e.injective
      change (g : L →L[ℝ] L) (((g⁻¹ : (L →L[ℝ] L)ˣ) : L →L[ℝ] L) z) = (g : L →L[ℝ] L) z
      rw [he, hgZ z hz]

/-- The bracket is continuous in both entries in finite dimension. -/
def bracketContinuous : L →L[ℝ] L →L[ℝ] L :=
  LinearMap.toContinuousLinearMap
    ((Module.End.toContinuousLinearMap (𝕜 := ℝ) L).toLinearMap.comp
      (LieModule.toEnd ℝ L L).toLinearMap)

@[simp] lemma bracketContinuous_apply (x y : L) : bracketContinuous x y = ⁅x, y⁆ := rfl

theorem orthogonalAutGroup_isClosed :
    IsClosed (orthogonalAutGroup (L := L) : Set (L →L[ℝ] L)ˣ) := by
  change IsClosed {g : (L →L[ℝ] L)ˣ | (∀ x : L, ‖(g : L →L[ℝ] L) x‖ = ‖x‖) ∧
    (∀ x y : L, (g : L →L[ℝ] L) ⁅x, y⁆ = ⁅(g : L →L[ℝ] L) x, (g : L →L[ℝ] L) y⁆) ∧
    (∀ z ∈ LieAlgebra.center ℝ L, (g : L →L[ℝ] L) z = z)}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun x => isClosed_eq
      ((Continuous.clm_apply Units.continuous_val continuous_const).norm) continuous_const
  · apply IsClosed.inter
    · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq
        (Continuous.clm_apply Units.continuous_val continuous_const)
        (by
          exact ((bracketContinuous (L := L)).continuous.comp
            (Continuous.clm_apply Units.continuous_val continuous_const)).clm_apply
              (Continuous.clm_apply Units.continuous_val continuous_const))
    · exact isClosed_iInter fun z => isClosed_iInter fun hz => isClosed_eq
        (Continuous.clm_apply Units.continuous_val continuous_const) continuous_const

/-- Compactness includes the inverse operator; this avoids using the
nonclosed embedding of all invertible matrices into endomorphisms. -/
theorem orthogonalAutGroup_isCompact :
    IsCompact (orthogonalAutGroup (L := L) : Set (L →L[ℝ] L)ˣ) := by
  let S : Submonoid (L →L[ℝ] L) :=
    { carrier := {f | ‖f‖ ≤ 1}
      one_mem' := ContinuousLinearMap.norm_id_le
      mul_mem' := fun {f g} hf hg => (norm_mul_le f g).trans ((mul_le_mul_of_nonneg_right hf (norm_nonneg g)).trans (by simpa using hg)) }
  have hS : IsCompact (S : Set (L →L[ℝ] L)) := by
    have hs : (S : Set (L →L[ℝ] L)) = Metric.closedBall 0 1 := by
      ext f
      change (‖f‖ ≤ 1) ↔ dist f 0 ≤ 1
      exact (dist_zero_right f).symm ▸ Iff.rfl
    rw [hs]
    letI : ProperSpace (L →L[ℝ] L) := FiniteDimensional.proper_real (L →L[ℝ] L)
    exact isCompact_closedBall _ _
  apply (Submonoid.units_isCompact hS).of_isClosed_subset orthogonalAutGroup_isClosed
  intro g hg
  change (g : L →L[ℝ] L) ∈ S ∧ (g⁻¹ : (L →L[ℝ] L)ˣ).val ∈ S
  constructor
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by rw [hg.1 x, one_mul])
  · have hi := (orthogonalAutGroup (L := L)).inv_mem hg
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by rw [hi.1 x, one_mul])


/-- A derivation of a reductive algebra which kills its center is inner.
The preservation of the semisimple summand follows from its perfection;
no semisimplicity hypothesis on the entire algebra is used. -/
theorem derivation_inner_of_center_zero
    (hRed : Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition.IsReductive_value ℝ L)
    (D : LieDerivation ℝ L L)
    (hZ : ∀ z ∈ LieAlgebra.center ℝ L, D z = 0) :
    ∃ z : L, ∀ x : L, D x = ⁅z, x⁆ := by
  obtain ⟨S, hS, hc⟩ := (ReductiveDecomposition.reductive_iff ℝ L).mp hRed
  have hDS : ∀ x : S, D (x : L) ∈ S := by
    let P : Submodule ℝ S := S.toSubmodule.comap
      (D.toLinearMap.comp S.toSubmodule.subtype)
    have hp : (⁅(⊤ : LieIdeal ℝ S), (⊤ : LieIdeal ℝ S)⁆ : LieIdeal ℝ S).toSubmodule ≤ P := by
      rw [LieSubmodule.lieIdeal_oper_eq_linear_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, y, rfl⟩
      change D ⁅(x.val : S).val, (y.val : S).val⁆ ∈ S
      rw [D.apply_lie_eq_add]
      exact S.add_mem (by rw [← lie_skew]; exact S.neg_mem (S.lie_mem x.val.property))
        (S.lie_mem y.val.property)
    rw [semisimple_perfect ℝ S hS] at hp
    exact fun x => hp (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ S))
  let d : LieDerivation ℝ S S :=
    { toLinearMap := (D.toLinearMap.comp S.toSubmodule.subtype).codRestrict S.toSubmodule hDS
      leibniz' := by
        intro a b
        apply Subtype.ext
        exact D.apply_lie_eq_sub a b }
  obtain ⟨z, hz, _⟩ := derivation_inner_unique ℝ S hS d
  refine ⟨z, fun x => ?_⟩
  obtain ⟨e, he⟩ := ReductiveDecomposition.center_direct_sum ℝ L S hc
  obtain ⟨⟨s, c⟩, rfl⟩ := e.surjective x
  change D (e (s, c)) = ⁅(z : L), e (s, c)⁆
  rw [he, map_add, hZ c c.property, add_zero, lie_add]
  have hs : D (s : L) = ⁅(z : L), (s : L)⁆ := by
    have hh := congrArg (fun f : LieDerivation ℝ S S => (f s : L)) hz
    calc
      D (s : L) = (d s : L) := rfl
      _ = (((adjoint ℝ S) z) s : L) := hh.symm
      _ = ⁅(z : L), (s : L)⁆ := by rw [adjoint_apply]; rfl
  rw [hs, c.property, add_zero]

@[simp] lemma velocity_zero_smul (X : L →L[ℝ] L) : (0 : ℝ) • X = 0 := by
  ext a
  change (0 : ℝ) • X a = 0
  exact zero_smul ℝ _

lemma velocity_hasDerivAt (X : L →L[ℝ] L) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
  simpa only [velocity_zero_smul, NormedSpace.exp_zero, one_mul, one_apply_eq_self] using
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0

lemma velocity_leibniz (X : L →L[ℝ] L)
    (hX : X ∈ ClosedMatrixGroups.velocities (orthogonalAutGroup (L := L)))
    (x y : L) : X ⁅x, y⁆ = ⁅x, X y⁆ - ⁅y, X x⁆ := by
  have he := velocity_hasDerivAt X
  have hd (a : L) : HasDerivAt
      (fun t : ℝ => (NormedSpace.exp (t • X) : L →L[ℝ] L) a) (X a) 0 := by
    simpa using he.clm_apply (hasDerivAt_const (0 : ℝ) a)
  have hb := (bracketContinuous (L := L)).hasDerivAt_of_bilinear
    (fun _ => hd x) (fun _ => hd y)
  have hb' : HasDerivAt
      (fun t : ℝ => ⁅(NormedSpace.exp (t • X) : L →L[ℝ] L) x,
        (NormedSpace.exp (t • X) : L →L[ℝ] L) y⁆)
      (⁅x, X y⁆ + ⁅X x, y⁆) 0 := by
    simpa only [velocity_zero_smul, NormedSpace.exp_zero, one_apply_eq_self, bracketContinuous_apply] using hb
  have ht : (fun t : ℝ => (NormedSpace.exp (t • X) : L →L[ℝ] L) ⁅x,y⁆) =
      (fun t : ℝ => ⁅(NormedSpace.exp (t • X) : L →L[ℝ] L) x,
        (NormedSpace.exp (t • X) : L →L[ℝ] L) y⁆) := by
    funext t
    exact (hX t).2.1 x y
  rw [← ht] at hb'
  have hh := (hd ⁅x,y⁆).unique hb'
  rw [← lie_skew (X x) y] at hh
  simpa only [sub_eq_add_neg] using hh

lemma velocity_center_zero (X : L →L[ℝ] L)
    (hX : X ∈ ClosedMatrixGroups.velocities (orthogonalAutGroup (L := L)))
    (z : L) (hz : z ∈ LieAlgebra.center ℝ L) : X z = 0 := by
  have hd : HasDerivAt
      (fun t : ℝ => (NormedSpace.exp (t • X) : L →L[ℝ] L) z) (X z) 0 := by
    simpa using (velocity_hasDerivAt X).clm_apply (hasDerivAt_const (0 : ℝ) z)
  have ht : (fun t : ℝ => (NormedSpace.exp (t • X) : L →L[ℝ] L) z) =
      (fun _ : ℝ => z) := by
    funext t
    exact (hX t).2.2 z hz
  rw [ht] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) z)

def velocityDerivation (X : L →L[ℝ] L)
    (hX : X ∈ ClosedMatrixGroups.velocities (orthogonalAutGroup (L := L))) :
    LieDerivation ℝ L L where
  toLinearMap := X.toLinearMap
  leibniz' := velocity_leibniz X hX

lemma velocity_is_ad_of_inner_derivations
    (hInner : ∀ D : LieDerivation ℝ L L,
      (∀ z ∈ LieAlgebra.center ℝ L, D z = 0) →
      ∃ z : L, ∀ x : L, D x = ⁅z, x⁆)
    (X : L →L[ℝ] L)
    (hX : X ∈ ClosedMatrixGroups.velocities (orthogonalAutGroup (L := L))) :
    ∃ z : L, adContinuous z = X := by
  obtain ⟨z, hz⟩ := hInner (velocityDerivation X hX) (velocity_center_zero X hX)
  refine ⟨z, ?_⟩
  ext x
  exact (hz x).symm

lemma end_one_smul (A : L →L[ℝ] L) : (1 : ℝ) • A = A := by
  ext x
  change (1 : ℝ) • A x = A x
  exact one_smul ℝ _

lemma exp_apply_of_eq_zero (A : L →L[ℝ] L) (x : L) (hx : A x = 0) :
    (NormedSpace.exp A : L →L[ℝ] L) x = x := by
  have hd (t : ℝ) : HasDerivAt
      (fun t : ℝ => (NormedSpace.exp (t • A) : L →L[ℝ] L) x) 0 t := by
    have he := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A t).clm_apply
      (hasDerivAt_const t x)
    simpa only [mul_apply_eq_comp, hx, map_zero, add_zero] using he
  have hh := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) (1 : ℝ) 0
  simpa only [end_one_smul, velocity_zero_smul, NormedSpace.exp_zero, one_apply_eq_self] using hh

lemma exp_ad_center (a z : L) (hz : z ∈ LieAlgebra.center ℝ L) :
    (NormedSpace.exp (adContinuous a) : L →L[ℝ] L) z = z := by
  apply exp_apply_of_eq_zero
  exact hz a

local instance : NormedAlgebra ℚ (L →L[ℝ] L) :=
  NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)

lemma adContinuous_skewAdjoint
    (hInv : ∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆) (z : L) :
    adContinuous z ∈ skewAdjoint (L →L[ℝ] L) := by
  change star (adContinuous z) = -adContinuous z
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ x ⁅z, y⁆ = inner ℝ (-⁅z, x⁆) y
  rw [inner_neg_left, hInv z x y, neg_neg]

lemma exp_ad_norm
    (hInv : ∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆) (z x : L) :
    ‖NormedSpace.exp (adContinuous z) x‖ = ‖x‖ := by
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (adContinuous_skewAdjoint hInv z)
lemma exp_ad_bracket (z x y : L) :
    NormedSpace.exp (adContinuous z) ⁅x, y⁆ =
      ⁅NormedSpace.exp (adContinuous z) x, NormedSpace.exp (adContinuous z) y⁆ := by
  let A := adContinuous z
  let E : ℝ → L →L[ℝ] L := fun t => NormedSpace.exp (t • A)
  let F : ℝ → L →L[ℝ] L := fun t => NormedSpace.exp (t • -A)
  have hE (t : ℝ) (v : L) : HasDerivAt (fun t => E t v) (A (E t v)) t := by
    simpa only [E, mul_apply_eq_comp, map_zero, add_zero] using
      (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t v)
  have hB (t : ℝ) : HasDerivAt (fun t => ⁅E t x, E t y⁆)
      (A ⁅E t x, E t y⁆) t := by
    have ht := (bracketContinuous (L := L)).hasDerivAt_of_bilinear
      (fun _ => hE t x) (fun _ => hE t y)
    change HasDerivAt (fun t => ⁅E t x, E t y⁆)
      (⁅E t x, A (E t y)⁆ + ⁅A (E t x), E t y⁆) t at ht
    apply ht.congr_deriv
    change ⁅E t x, ⁅z, E t y⁆⁆ + ⁅⁅z, E t x⁆, E t y⁆ = ⁅z, ⁅E t x, E t y⁆⁆
    rw [leibniz_lie z (E t x) (E t y), add_comm]
  have hd (t : ℝ) : HasDerivAt (fun t => F t ⁅E t x, E t y⁆) 0 t := by
    convert (hasDerivAt_exp_smul_const (-A) t).clm_apply (hB t) using 1
    simp only [mul_apply_eq_comp, neg_apply, map_neg, neg_add_cancel]
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) (1 : ℝ) 0
  have hOne (B : L →L[ℝ] L) : (1 : ℝ) • B = B := by ext v; exact one_smul ℝ (B v)
  have hZero (B : L →L[ℝ] L) : (0 : ℝ) • B = 0 := by ext v; exact zero_smul ℝ (B v)
  have hh : NormedSpace.exp (-A) ⁅NormedSpace.exp A x, NormedSpace.exp A y⁆ = ⁅x, y⁆ := by
    simpa only [F, E, hOne, hZero, NormedSpace.exp_zero, one_apply_eq_self] using h
  have hi : NormedSpace.exp A * NormedSpace.exp (-A) = (1 : L →L[ℝ] L) := by
    have hu := congrArg (fun g : (L →L[ℝ] L)ˣ => g.val)
      (mul_inv_cancel (ClosedMatrixGroups.expUnit A))
    simpa only [Units.val_mul, ClosedMatrixGroups.coe_expUnit,
      ClosedMatrixGroups.coe_expUnit_inv, Units.val_one] using hu
  have := congrArg (fun v => NormedSpace.exp A v) hh
  simpa only [← mul_apply_eq_comp, hi, one_apply_eq_self] using this.symm

/-- Maximal abelian subalgebras of a compact reductive real Lie algebra
are conjugate by a finite product of genuine inner exponentials. -/
theorem maximalAbelian_conjugacy
    (hRed : Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition.IsReductive_value ℝ L)
    (hInv : ∀ z x y : L, inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆)
    (T₁ T₂ : LieSubalgebra ℝ L)
    (hT₁ : Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₁)
    (hT₂ : Maximal (fun T : LieSubalgebra ℝ L => IsLieAbelian T) T₂) :
    ∃ zs : List L,
      (fun x : L => (innerProduct zs : L →L[ℝ] L) x) '' (T₁ : Set L) = (T₂ : Set L) := by
  apply conjugacy_of_compact_automorphisms hInv (orthogonalAutGroup (L := L))
    orthogonalAutGroup_isCompact ?_ ?_ ?_ T₁ T₂ hT₁ hT₂
  · intro z
    exact ⟨exp_ad_norm hInv z, exp_ad_bracket z, exp_ad_center z⟩
  · intro g hg x y
    exact hg.2.1 x y
  · intro X hX
    exact velocity_is_ad_of_inner_derivations
      (derivation_inner_of_center_zero hRed) X hX

end LieAlgebrasAndRepresentations.CompactCartanConjugacy
