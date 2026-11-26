import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralLattices
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRootRelations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.EuclideanComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Substitution
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWOrdered

universe u

namespace LinearAlgebraicGroups.Classification.IntegralLattices

open scoped BigOperators

open Module
open Specs.IntegralLattices
open _root_.LinearAlgebraicGroups.Specs (Lie)

/-- The simple coroots span the coroot lattice and are independent; perfect
duality carries their dual basis to the character lattice. -/
theorem fundamentalWeights_of_coroot_span : FundamentalWeights.{u} := by
  classical
  intro D _ hcoroot
  let y : D.base.support → D.Y := fun j => D.datum.coroot j
  have hyspan : Submodule.span ℤ (Set.range y) = ⊤ := by
    have hrange : Set.range y = D.datum.coroot '' (D.base.support : Set D.I) := by
      ext v
      exact ⟨fun ⟨j, hj⟩ => ⟨j, j.property, hj⟩, fun ⟨j, hj, hv⟩ => ⟨⟨j, hj⟩, hv⟩⟩
    rw [hrange, D.base.span_int_coroot_support, hcoroot]
  let c := Basis.mk D.base.linearIndepOn_coroot hyspan.ge
  let b := c.dualBasis.map D.datum.toPerfPair.symm
  refine ⟨b, fun i j => ?_⟩
  change D.datum.toLinearMap (D.datum.toPerfPair.symm (c.dualBasis i)) (y j) = _
  rw [LinearMap.apply_symm_toPerfPair_self]
  have hcy (j : D.base.support) : c j = y j := Basis.mk_apply _ _ _
  rw [← hcy j, Basis.dualBasis_apply_self]

/-- An integral character functional inducing the prescribed positive system.
Its values on roots are a common positive multiple of the base heights. -/
theorem exists_integralHeight (D : Specs.Pinning.BasedRootDatum.{u}) :
    ∃ (height : D.X →ₗ[ℤ] ℤ) (d : ℤ), 0 < d ∧
      ∀ a, height (D.datum.root a) = d * D.base.height a := by
  classical
  let : Finite D.I := D.finiteRoots
  let : Module.Free ℤ D.X := D.freeX
  let : Module.Free ℤ D.Y := D.freeY
  let : Module.Finite ℤ D.X := D.finiteX
  let : Module.Finite ℤ D.Y := D.finiteY
  let : D.datum.IsReduced := D.reduced
  let C := RootData.integralCartan D.datum D.base
  let M := C.transpose
  have hdet : M.det ≠ 0 := by
    have hu := (RootData.rationalComplement D.datum D.base).1
    change IsUnit ((Int.castRingHom ℚ).mapMatrix C).det at hu
    rw [← (Int.castRingHom ℚ).map_det, Int.coe_castRingHom] at hu
    exact Matrix.det_transpose C ▸ Int.cast_ne_zero.mp hu.ne_zero
  let c := M.adjugate.mulVec (fun _ => 1)
  let height : D.X →ₗ[ℤ] ℤ := M.det • ∑ j, c j • D.datum.coroot' j
  have hc : M.mulVec c = fun _ => M.det := by
    rw [show c = M.adjugate.mulVec (fun _ => 1) from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext j
    simp
  have hsimple (i : D.base.support) : height (D.datum.root i) = M.det ^ 2 := by
    have he : (∑ j : D.base.support, c j * D.datum.pairing i j) = M.det := by
      simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, M, C,
        RootData.integralCartan, mul_comm] using congrFun hc i
    simp only [height, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
      pow_two]
    change M.det * (∑ j : D.base.support, c j * D.datum.pairing i j) = _
    rw [he]
  refine ⟨height, M.det ^ 2, sq_pos_of_ne_zero hdet, fun i => ?_⟩
  obtain ⟨f, _, _, hf⟩ := D.base.exists_root_eq_sum_int i
  calc
    height (D.datum.root i) = ∑ j ∈ D.base.support, f j * M.det ^ 2 := by
      rw [hf, map_sum, ← Finset.sum_finset_coe]
      simp only [map_smul, hsimple, smul_eq_mul]
      exact Finset.sum_finset_coe (fun j : D.I => f j * M.det ^ 2) D.base.support
    _ = M.det ^ 2 * D.base.height i := by
      rw [D.base.height_eq_sum hf, Finset.mul_sum]
      congr 1
      ext j
      exact mul_comm _ _

section HighestWeight

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (Enumerates)

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {lam : D.X}

/-- An exponent at or beyond the nilpotence bound makes the ordered coefficient zero. -/
theorem negativeCoefficient_eq_zero_of_bound (V : RationalHighestWeight z e h lam)
    (negative : List (Negative D)) {a : Negative D} (ha : a ∈ negative)
    (m : Negative D →₀ ℕ) (hm : V.nilpotenceBound ≤ m a) :
    V.negativeCoefficient negative m = 0 := by
  have hp : (V.rootOperator a) ^ m a = 0 := pow_eq_zero_of_le hm (V.nilpotent a)
  have hzero : dividedPower (V.rootOperator a) (m a) = 0 := by
    simp [dividedPower, hp]
  have hprod : (negative.map (fun i : Negative D => dividedPower (V.rootOperator i.val) (m i))).prod = 0 :=
    List.prod_eq_zero (hzero ▸ List.mem_map_of_mem ha)
  simp [RationalHighestWeight.negativeCoefficient, hprod]

/-- The lattice of ordered coefficients is generated by finitely many vectors. -/
theorem lattice_finite (V : RationalHighestWeight z e h lam)
    (negative : List (Negative D)) (hnegative : Enumerates negative Set.univ) :
    Module.Finite ℤ (V.lattice negative) := by
  classical
  let : Finite D.I := D.finiteRoots
  let S : Set (Negative D →₀ ℕ) := {m | ∀ a, m a < V.nilpotenceBound}
  have hS : S.Finite := by
    let f : S → (Negative D → Fin V.nilpotenceBound) := fun m a => ⟨m.val a, m.property a⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      ext a
      exact congrArg Fin.val (congrFun hxy a)
    let : Finite S := Finite.of_injective f hf
    exact Set.toFinite S
  apply Module.Finite.span_of_finite
  refine ((hS.image (V.negativeCoefficient negative)).insert 0).subset ?_
  rintro _ ⟨m, rfl⟩
  by_cases hm : m ∈ S
  · exact Set.mem_insert_of_mem _ ⟨m, hm, rfl⟩
  · simp only [S, Set.mem_ofPred_eq, not_forall, not_lt] at hm
    obtain ⟨a, ha⟩ := hm
    rw [negativeCoefficient_eq_zero_of_bound V negative ((hnegative.2 a).2 (Set.mem_univ _)) m ha]
    exact Set.mem_insert _ _

/-- The finitely generated lattice lies in a torsion-free abelian group and is free over ℤ. -/
theorem lattice_free (V : RationalHighestWeight z e h lam)
    (negative : List (Negative D)) (hnegative : Enumerates negative Set.univ) :
    Module.Free ℤ (V.lattice negative) := by
  let := lattice_finite V negative hnegative
  exact Module.free_of_finite_type_torsion_free'

@[simp] theorem dividedPower_zero {n : ℕ}
    (E : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u}) :
    dividedPower E 0 = 1 := by
  simp [dividedPower]

@[simp] theorem dividedPower_one {n : ℕ}
    (E : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u}) :
    dividedPower E 1 = E := by
  simp [dividedPower]

/-- The coefficient of each power in the root polynomial is its divided power,
including the coefficients past the nilpotence cutoff. -/
theorem exponentialPolynomial_coeff {n N : ℕ}
    (E : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u}) (hN : E ^ N = 0)
    (m : ℕ) (i j : Index.{u} n) :
    ((exponentialPolynomial E N) i j).coeff m = (dividedPower E m) i j := by
  classical
  simp only [exponentialPolynomial, Matrix.sum_apply, Polynomial.finsetSum_coeff,
    Matrix.smul_apply, RingHom.mapMatrix_apply, smul_eq_mul, mul_comm (Polynomial.X ^ _)]
  by_cases hm : m < N
  · rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr hm)]
    · simp
    · intro a _ ha
      simp [Ne.symm ha]
  · have hz : E ^ m = 0 := pow_eq_zero_of_le (Nat.le_of_not_gt hm) hN
    rw [show dividedPower E m = 0 by simp [dividedPower, hz]]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : m ≠ a := fun h => hm (h ▸ Finset.mem_range.mp ha)
    simp [hne]

/-- The constant coefficient of the product is the highest vector itself. -/
@[simp] theorem negativeCoefficient_zero (V : RationalHighestWeight z e h lam)
    (negative : List (Negative D)) :
    V.negativeCoefficient negative 0 = V.highest := by
  simp [RationalHighestWeight.negativeCoefficient]

theorem highest_mem_lattice (V : RationalHighestWeight z e h lam)
    (negative : List (Negative D)) : V.highest ∈ V.lattice negative := by
  exact Submodule.subset_span ⟨0, negativeCoefficient_zero V negative⟩

/-- A negative root operator applied to the highest vector is the coefficient
of its own parameter to the first power, with all other exponents zero. -/
theorem rootOperator_mulVec_highest_mem_lattice (V : RationalHighestWeight z e h lam)
    (negative : List (Negative D)) (hnegative : Enumerates negative Set.univ)
    (a : Negative D) : (V.rootOperator a).mulVec V.highest ∈ V.lattice negative := by
  classical
  apply Submodule.subset_span
  refine ⟨Finsupp.single a 1, ?_⟩
  have ha := (hnegative.2 a).2 (Set.mem_univ _)
  unfold RationalHighestWeight.negativeCoefficient
  let f (b : Negative D) := dividedPower (V.rootOperator b) (Finsupp.single a 1 b)
  have hf : ∀ b, b ≠ a → f b = 1 := by
    intro b hb
    simp [f, Finsupp.single_eq_of_ne hb]
  obtain ⟨left, right, hlist⟩ := List.append_of_mem ha
  have hnd : (left ++ a :: right).Nodup := hlist ▸ hnegative.1
  have hleft : a ∉ left := fun ht =>
    List.disjoint_left.mp (List.disjoint_of_nodup_append hnd) ht List.mem_cons_self
  have hright : a ∉ right := (List.nodup_cons.mp hnd.of_append_right).1
  have prod_one (l : List (Negative D)) (hl : a ∉ l) :
      (l.map f).prod = 1 := by
    apply List.prod_eq_one
    rintro _ hmem
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hmem
    exact hf b (fun h => hl (h ▸ hb))
  change ((negative.map f).prod).mulVec V.highest = _
  rw [hlist, List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    prod_one left hleft, prod_one right hright, mul_one, one_mul]
  simp [f]

/-- An operator supported on a fixed weight difference shifts every weight space. -/
theorem mulVec_mem_weightSpace (V : RationalHighestWeight z e h lam)
    {E : Matrix (Index.{u} V.dimension) (Index.{u} V.dimension) RationalField.{u}}
    {delta mu : D.X}
    (hE : ∀ i j, V.weight i ≠ V.weight j + delta → E i j = 0)
    {v : V.space} (hv : v ∈ V.weightSpace mu) :
    E.mulVec v ∈ V.weightSpace (mu + delta) := by
  intro i hi
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : V.weight j = mu
  · rw [hE i j (by simpa only [hj] using hi), zero_mul]
  · rw [hv j hj, mul_zero]

/-- Dividing a power by its factorial leaves its weight shift unchanged. -/
theorem dividedPower_mulVec_mem_weightSpace (V : RationalHighestWeight z e h lam) (a : D.I)
    (hE : ∀ i j, V.weight i ≠ V.weight j + D.datum.root a → V.rootOperator a i j = 0)
    (m : ℕ) {mu : D.X} {v : V.space} (hv : v ∈ V.weightSpace mu) :
    (dividedPower (V.rootOperator a) m).mulVec v ∈ V.weightSpace (mu + m • D.datum.root a) := by
  have hpow : ((V.rootOperator a) ^ m).mulVec v ∈ V.weightSpace (mu + m • D.datum.root a) := by
    induction m with
    | zero => simpa only [pow_zero, Matrix.one_mulVec, zero_nsmul, add_zero]
    | succ m ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, succ_nsmul']
      simpa only [add_assoc, add_left_comm, add_comm] using mulVec_mem_weightSpace V hE ih
  rw [dividedPower, Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ hpow

/-- The weight of an ordered coefficient is the highest weight plus the sum
of its root shifts counted with multiplicity. -/
theorem negativeCoefficient_mem_weightSpace (V : RationalHighestWeight z e h lam)
    (hE : ∀ a i j, V.weight i ≠ V.weight j + D.datum.root a → V.rootOperator a i j = 0)
    (negative : List (Negative D)) (m : Negative D →₀ ℕ) :
    V.negativeCoefficient negative m ∈
      V.weightSpace (lam + (negative.map (fun a : Negative D => m a • D.datum.root a.val)).sum) := by
  induction negative with
  | nil =>
    have hv : V.highest ∈ V.weightSpace lam := V.highest_support
    simpa [RationalHighestWeight.negativeCoefficient] using hv
  | cons a l ih =>
    change (dividedPower (V.rootOperator a) (m a) *
        ((l.map fun b : Negative D => dividedPower (V.rootOperator b) (m b)).prod)).mulVec
          V.highest ∈ _
    rw [← Matrix.mulVec_mulVec, List.map_cons, List.sum_cons]
    simpa only [RationalHighestWeight.negativeCoefficient, add_assoc, add_left_comm, add_comm] using
      dividedPower_mulVec_mem_weightSpace V a (hE a) (m a) ih

/-- A nonconstant negative coefficient has strictly smaller height than the
highest vector whenever all the negative roots have negative height. -/
theorem negativeCoefficient_height_lt
    (height : D.X →ₗ[ℤ] ℤ) (hheight : ∀ a : Negative D, height (D.datum.root a.val) < 0)
    (negative : List (Negative D)) (hnegative : Enumerates negative Set.univ)
    (m : Negative D →₀ ℕ) (hm : m ≠ 0) (mu : D.X) :
    height (mu + (negative.map (fun a : Negative D => m a • D.datum.root a.val)).sum) <
      height mu := by
  have hex : ∃ a, m a ≠ 0 := by
    by_contra! h
    apply hm
    ext a
    exact h a
  obtain ⟨a, ha⟩ := hex
  have hmem := (hnegative.2 a).2 (Set.mem_univ _)
  let f (b : Negative D) := height (m b • D.datum.root b.val)
  have hn (b : Negative D) : f b ≤ 0 := by
    simp only [f, map_nsmul, nsmul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hheight b).le
  have hp : f a < 0 := by
    simp only [f, map_nsmul, nsmul_eq_mul]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero ha) (hheight a)
  have hnonpos (l : List (Negative D)) : (l.map f).sum ≤ 0 := by
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.map_cons, List.sum_cons]
      exact add_nonpos (hn b) ih
  have hs : (negative.map f).sum < 0 := by
    clear hnegative
    induction negative with
    | nil => simp at hmem
    | cons b l ih =>
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hmem with hab | hal
      · subst b
        have hrest := hnonpos l
        omega
      · have hb := hn b
        have hrest := ih hal
        omega
  rw [map_add, add_lt_iff_neg_left]
  rw [map_list_sum, List.map_map]
  exact hs


/-- Homogeneous generators split the lattice into its weight sublattices. -/
theorem lattice_weight_decomposition (V : RationalHighestWeight z e h lam)
    (negative : List (Negative D)) (grade : (Negative D →₀ ℕ) → D.X)
    (hgrade : ∀ m, V.negativeCoefficient negative m ∈ V.weightSpace (grade m)) :
    (⨆ mu, V.lattice negative ⊓ (V.weightSpace mu).restrictScalars ℤ) =
      V.lattice negative := by
  apply le_antisymm (iSup_le fun _ => inf_le_left)
  apply Submodule.span_le.mpr
  rintro _ ⟨m, rfl⟩
  exact le_iSup (fun mu => V.lattice negative ⊓ (V.weightSpace mu).restrictScalars ℤ) (grade m)
    ⟨Submodule.subset_span ⟨m, rfl⟩, hgrade m⟩

/-- If the nonconstant ordered coefficients have lower weights, the
coefficient lattice meets the highest space in exactly the primitive line. -/
theorem lattice_highest_line (V : RationalHighestWeight z e h lam)
    (negative : List (Negative D)) (grade : (Negative D →₀ ℕ) → D.X)
    (hgrade : ∀ m, V.negativeCoefficient negative m ∈ V.weightSpace (grade m))
    (hlower : ∀ m ≠ 0, grade m ≠ lam) :
    V.lattice negative ⊓ (V.weightSpace lam).restrictScalars ℤ =
      Submodule.span ℤ {V.highest} := by
  classical
  let proj : V.space →ₗ[ℤ] V.space :=
    { toFun := fun v j => if V.weight j = lam then v j else 0
      map_add' := by
        intro v w
        funext j
        by_cases hj : V.weight j = lam <;> simp [hj]
      map_smul' := by
        intro r v
        funext j
        by_cases hj : V.weight j = lam <;> simp [hj] }
  have hproj (v : V.space) (hv : v ∈ V.weightSpace lam) : proj v = v := by
    funext j
    by_cases hj : V.weight j = lam
    · simp [proj, hj]
    · simp [proj, hj, hv j hj]
  have hmap : V.lattice negative ≤ (Submodule.span ℤ {V.highest}).comap proj := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    change proj (V.negativeCoefficient negative m) ∈ Submodule.span ℤ {V.highest}
    by_cases hm : m = 0
    · rw [hm, negativeCoefficient_zero, hproj _ V.highest_support]
      exact Submodule.subset_span (Set.mem_singleton _)
    · have hz : proj (V.negativeCoefficient negative m) = 0 := by
        funext j
        by_cases hj : V.weight j = lam
        · simp [proj, hj, hgrade m j (hj.trans_ne (hlower m hm).symm)]
        · simp [proj, hj]
      rw [hz]
      exact Submodule.zero_mem _
  apply le_antisymm
  · intro v hv
    have hv' := hmap hv.1
    change proj v ∈ Submodule.span ℤ {V.highest} at hv'
    rwa [hproj v hv.2] at hv'
  · apply Submodule.span_le.mpr
    rintro _ rfl
    exact ⟨highest_mem_lattice V negative, V.highest_support⟩

/-- The actual weight decomposition and primitive highest line follow from
the root shifts and the sign of a regular height function. -/
theorem lattice_weight_facts (V : RationalHighestWeight z e h lam)
    (hE : ∀ a i j, V.weight i ≠ V.weight j + D.datum.root a → V.rootOperator a i j = 0)
    (height : D.X →ₗ[ℤ] ℤ) (hheight : ∀ a : Negative D, height (D.datum.root a.val) < 0)
    (negative : List (Negative D)) (hnegative : Enumerates negative Set.univ) :
    (⨆ mu, V.lattice negative ⊓ (V.weightSpace mu).restrictScalars ℤ) = V.lattice negative ∧
      V.lattice negative ⊓ (V.weightSpace lam).restrictScalars ℤ =
        Submodule.span ℤ {V.highest} := by
  let grade (m : Negative D →₀ ℕ) :=
    lam + (negative.map (fun a : Negative D => m a • D.datum.root a.val)).sum
  have hgrade : ∀ m, V.negativeCoefficient negative m ∈ V.weightSpace (grade m) :=
    negativeCoefficient_mem_weightSpace V hE negative
  refine ⟨lattice_weight_decomposition V negative grade hgrade,
    lattice_highest_line V negative grade hgrade ?_⟩
  intro m hm he
  exact (negativeCoefficient_height_lt height hheight negative hnegative m hm lam).ne
    (congrArg height he)

/-- A positive root operator annihilates the cyclic highest vector by its
defining Verma relation. -/
theorem positive_root_mulVec_highest (V : RationalHighestWeight z e h lam) (a : Positive D) :
    (V.rootOperator a).mulVec V.highest = 0 := by
  apply (V.relations _).2
  exact Submodule.subset_span (Or.inl (Or.inl ⟨a, rfl⟩))

/-- Cartan acts on the cyclic vector by evaluation of its marked character. -/
theorem simple_coroot_mulVec_highest (V : RationalHighestWeight z e h lam) (i : D.base.support) :
    (V.envelopingAction (UniversalEnvelopingAlgebra.ι RationalField (h i))).mulVec V.highest =
      (D.datum.coroot' i lam : RationalField.{u}) • V.highest := by
  have hv := (V.relations _).2 (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))
  simp only [map_sub, AlgHom.commutes, Matrix.sub_mulVec, Matrix.algebraMap_eq_diagonal,
    Pi.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply, Matrix.diagonal_const_mulVec,
    sub_eq_zero] at hv
  exact hv

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The rank-one highest weight calculation giving the simple root
coefficient with integer value one. -/
theorem simple_root_mulVec_lowering (V : RationalHighestWeight z e h lam)
    (i : D.base.support) (hi : D.base.IsPos i) (a : D.I)
    (hbracket : ⁅e i, e a⁆ = h i) (hweight : D.datum.coroot' i lam = 1) :
    (V.rootOperator i).mulVec ((V.rootOperator a).mulVec V.highest) = V.highest := by
  have hm : V.rootOperator i * V.rootOperator a - V.rootOperator a * V.rootOperator i =
      V.envelopingAction (UniversalEnvelopingAlgebra.ι RationalField (h i)) := by
    have hlie := (UniversalEnvelopingAlgebra.ι RationalField).map_lie (e i) (e a)
    simpa only [RationalHighestWeight.rootOperator, Ring.lie_def, hbracket, map_sub, map_mul]
      using (congrArg V.envelopingAction hlie).symm
  have hv := congrArg (fun E : Matrix _ _ RationalField.{u} => E.mulVec V.highest) hm
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, positive_root_mulVec_highest V ⟨i, hi⟩,
    Matrix.mulVec_zero, sub_zero, simple_coroot_mulVec_highest, hweight, Int.cast_one, one_smul] at hv
  exact hv

private theorem pairwise_idxOf {J : Type*} [BEq J] [LawfulBEq J] (l : List J) (hl : l.Nodup) :
    l.Pairwise (fun a b => l.idxOf a ≤ l.idxOf b) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hrank (k : ℕ) (hk : k < l.length) : l.idxOf l[k] = k := by
    have hx : l[k] ∈ l := List.getElem_mem hk
    have hlt := List.idxOf_lt_length_of_mem hx
    exact (List.Nodup.getElem_inj_iff hl).mp (List.getElem_idxOf hlt)
  rw [hrank i hi, hrank j hj]
  exact hij.le

private theorem orderedWord_eq_replicate {J : Type*} [BEq J] [LawfulBEq J] [LinearOrder J]
    (l w : List J) (hl : l.Nodup) (hls : l.Pairwise (· ≤ ·))
    (hw : w.Pairwise (· ≤ ·)) (hmem : ∀ a ∈ w, a ∈ l) :
    w = l.flatMap (fun a => List.replicate (w.count a) a) := by
  have hs (xs : List J) (hxs : xs.Pairwise (· ≤ ·)) :
      (xs.flatMap fun a => List.replicate (w.count a) a).Pairwise (· ≤ ·) := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      rw [List.flatMap_cons, List.pairwise_append]
      refine ⟨by simp, ih hxs.of_cons, ?_⟩
      intro x hx y hy
      obtain rfl := List.eq_of_mem_replicate hx
      obtain ⟨b, hb, hy⟩ := List.mem_flatMap.mp hy
      obtain rfl := List.eq_of_mem_replicate hy
      exact (List.pairwise_cons.mp hxs).1 _ hb
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hw (hs l hls) ?_
  rw [List.perm_iff_count]
  intro a
  rw [List.count_flatMap]
  have hcount (xs : List J) (hxs : xs.Nodup) :
      (xs.map (fun b => (List.replicate (w.count b) b).count a)).sum =
        if a ∈ xs then w.count a else 0 := by
    induction xs with
    | nil => simp
    | cons b xs ih =>
      rw [List.map_cons, List.sum_cons, ih hxs.of_cons]
      by_cases hab : a = b
      · subst b
        simp [(List.nodup_cons.mp hxs).1]
      · simp [List.count_replicate, hab, Ne.symm hab]
  change w.count a =
    (l.map (fun b => (List.replicate (w.count b) b).count a)).sum
  rw [hcount l hl]
  by_cases ha : a ∈ l
  · simp [ha]
  · have hn : a ∉ w := fun hm => ha (hmem a hm)
    simp [ha, List.count_eq_zero_of_not_mem hn]

set_option maxHeartbeats 800000 in
/-- The ordered negative-root coefficients span the cyclic highest-weight
module over the rational field. -/
theorem negativeCoefficient_span (V : RationalHighestWeight z e h lam)
    (B : Basis (D.base.support ⊕ D.I) RationalField.{u}
      (Lie RationalField.{u} Q.pinned.pair.G.val))
    (Bh : ∀ i, B (.inl i) = h i) (Be : ∀ a, B (.inr a) = e a)
    (negative : List (Negative D)) (positive : List (Positive D))
    (hn : Enumerates negative Set.univ) (hp : Enumerates positive Set.univ) :
    Submodule.span RationalField.{u} (Set.range (V.negativeCoefficient negative)) = ⊤ := by
  classical
  let : Finite D.I := D.finiteRoots
  let K := RationalField.{u}
  let J := D.base.support ⊕ D.I
  let : DecidableEq J := Classical.decEq J
  let : BEq J := instBEqOfDecidableEq
  let U := UniversalEnvelopingAlgebra K (Lie K Q.pinned.pair.G.val)
  let S := Submodule.span K (Set.range (V.negativeCoefficient negative))
  let ineg : Negative D ↪ J := ⟨fun a => .inr a.val, fun _ _ hh =>
    Subtype.ext (Sum.inr.inj hh)⟩
  let ipos : Positive D ↪ J := ⟨fun a => .inr a.val, fun _ _ hh =>
    Subtype.ext (Sum.inr.inj hh)⟩
  let simple : List D.base.support := (Finset.univ : Finset D.base.support).toList
  let neg := negative.map ineg
  let mid := simple.map (Sum.inl : D.base.support → J)
  let pos := positive.map ipos
  let order := neg ++ mid ++ pos
  have horder : order.Nodup := by
    simp only [order, List.nodup_append]
    refine ⟨⟨hn.1.map ineg.injective, ?_, ?_⟩, hp.1.map ipos.injective, ?_⟩
    · exact (Finset.nodup_toList _).map Sum.inl_injective
    · intro a ha b hb hab
      subst b
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, _, hy⟩ := List.mem_map.mp hb
      change Sum.inl y = Sum.inr x.val at hy
      cases hy
    · intro a ha b hb hab
      subst b
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨x, _, hx⟩ := List.mem_map.mp ha
        exact x.property (Sum.inr.inj hx ▸ y.property)
      · obtain ⟨x, _, hx⟩ := List.mem_map.mp ha
        change Sum.inl x = Sum.inr y.val at hx
        cases hx
  have hmem (a : J) : a ∈ order := by
    cases a with
    | inl i => simp [order, mid, simple]
    | inr i =>
      by_cases hi : D.base.IsPos i
      · have hm := (hp.2 ⟨i, hi⟩).2 (Set.mem_univ _)
        exact List.mem_append_right _ (List.mem_map_of_mem (f := ipos) hm)
      · have hm := (hn.2 ⟨i, hi⟩).2 (Set.mem_univ _)
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_map_of_mem (f := ineg) hm))
  let : LinearOrder J := LinearOrder.lift' order.idxOf (fun a _ hab =>
    (List.idxOf_inj (hmem a)).mp hab)
  let F : U →ₗ[K] V.space :=
    ((Matrix.mulVecBilin K K).flip V.highest).comp V.envelopingAction.toLinearMap
  have hF : Function.Surjective F := V.cyclic
  have hordered (w : Shared.Lie.PBW.OrderedWord J) :
      F (Shared.Lie.PBW.orderedMonomial B w) ∈ S := by
    let P (a : J) := V.envelopingAction (UniversalEnvelopingAlgebra.ι K (B a))
    let powers (l : List J) := (l.map fun a => P a ^ (w.val.count a)).prod
    have ho : order.Pairwise (· ≤ ·) := by
      change order.Pairwise (fun a b => order.idxOf a ≤ order.idxOf b)
      exact pairwise_idxOf order horder
    have hw := orderedWord_eq_replicate order w.val horder ho
      w.property (fun a _ => hmem a)
    have hrep (l : List J) :
        ((l.flatMap fun a => List.replicate (w.val.count a) a).map P).prod = powers l := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp [List.flatMap_cons, List.map_append, List.prod_append, List.prod_replicate, ih, powers]
    have hP (l : List J) :
        V.envelopingAction (Shared.Lie.PBW.monomial B l) = (l.map P).prod := by
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [Shared.Lie.PBW.monomial_cons, map_mul, ih, List.map_cons, List.prod_cons]
        rfl
    have hscalar (a : J) (ha : a ∈ mid ++ pos) :
        ∃ c : K, (P a).mulVec V.highest = c • V.highest := by
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        exact ⟨_, by simpa only [P, Bh] using simple_coroot_mulVec_highest V i⟩
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        refine ⟨0, ?_⟩
        change (V.envelopingAction (UniversalEnvelopingAlgebra.ι K (B (.inr i.val)))).mulVec
          V.highest = 0 • V.highest
        simpa only [Be, zero_smul, RationalHighestWeight.rootOperator]
          using positive_root_mulVec_highest V i
    have hpow (l : List J) (hl : ∀ a ∈ l, a ∈ mid ++ pos) :
        ∃ c : K, (powers l).mulVec V.highest = c • V.highest := by
      induction l with
      | nil => exact ⟨1, by simp [powers]⟩
      | cons a l ih =>
        obtain ⟨c, hc⟩ := hscalar a (hl a List.mem_cons_self)
        obtain ⟨d, hd⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
        have hant (m : ℕ) : ((P a) ^ m).mulVec V.highest = c ^ m • V.highest := by
          induction m with
          | zero => simp
          | succ m ih =>
            rw [pow_succ, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
        exact ⟨d * c ^ (w.val.count a), by
          simp only [powers, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
            hd, Matrix.mulVec_smul, hant, smul_smul]⟩
    let m : Negative D →₀ ℕ := Finsupp.equivFunOnFinite.symm
      (fun a => w.val.count (ineg a))
    have hm (a : Negative D) : m a = w.val.count (ineg a) := by simp [m]
    have hneg :
        powers neg =
          (negative.map fun a => ((m a).factorial : K)).prod •
            (negative.map fun a : Negative D => dividedPower (V.rootOperator a) (m a)).prod := by
      have ha (a : Negative D) :
          P (ineg a) ^ w.val.count (ineg a) =
            ((m a).factorial : K) • dividedPower (V.rootOperator a) (m a) := by
        rw [← hm]
        have hfac : ((m a).factorial : K) ≠ 0 := by
          intro hzero
          have hzero' := congrArg (ULift.ringEquiv : K ≃+* ℚ) hzero
          rw [map_natCast, map_zero] at hzero'
          exact Nat.factorial_ne_zero _ (Nat.cast_eq_zero.mp hzero')
        change (V.envelopingAction (UniversalEnvelopingAlgebra.ι K (B (.inr a.val)))) ^ m a =
          ((m a).factorial : K) • dividedPower (V.rootOperator a) (m a)
        rw [Be, dividedPower, smul_smul, mul_inv_cancel₀ hfac, one_smul]
        rfl
      have hprod (l : List (Negative D)) :
          (l.map fun a => ((m a).factorial : K) • dividedPower (V.rootOperator a) (m a)).prod =
          (l.map fun a => ((m a).factorial : K)).prod •
            (l.map fun a : Negative D => dividedPower (V.rootOperator a) (m a)).prod := by
        induction l with
        | nil => simp
        | cons a l ih =>
          simp only [List.map_cons, List.prod_cons, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          rw [mul_comm]
      simpa only [powers, neg, List.map_map, Function.comp_def, ha] using hprod negative
    obtain ⟨c, hc⟩ := hpow (mid ++ pos) (fun _ ha => ha)
    have hsplit : powers order = powers neg * powers (mid ++ pos) := by
      simp only [powers, order, List.append_assoc, List.map_append, List.prod_append]
    change (V.envelopingAction (Shared.Lie.PBW.monomial B w.val)).mulVec V.highest ∈ S
    rw [hP, congrArg (fun l => (l.map P).prod) hw, hrep order, hsplit,
      ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hneg, Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨m, rfl⟩))
  have hspan : ⊤ ≤ S.comap F := by
    rw [← Shared.Lie.PBW.ordered_span B]
    exact Submodule.span_le.mpr (by rintro _ ⟨w, rfl⟩; exact hordered w)
  apply top_unique
  intro v _
  obtain ⟨a, rfl⟩ := hF v
  exact hspan (Submodule.mem_top : a ∈ (⊤ : Submodule K U))

end HighestWeight

/-- A generating set of lattice weights and their negatives generates the
integral group algebra, so the associated diagonal torus is a closed subgroup. -/
theorem torusCoordinatesGenerate_of_span_eq_top {D : Specs.Pinning.BasedRootDatum.{u}}
    {n : ℕ} (w : Index.{u} n → D.X) (hw : Submodule.span ℤ (Set.range w) = ⊤) :
    TorusCoordinatesGenerate w := by
  let c (x : D.X) : AddMonoidAlgebra ℤ D.X := AddMonoidAlgebra.single x 1
  let S := Algebra.adjoin ℤ (Set.range (fun i => c (w i)) ∪ Set.range (fun i => c (-w i)))
  have c_mul (x y : D.X) : c x * c y = c (x + y) := by
    simp [c, AddMonoidAlgebra.single_mul_single]
  let weights : AddSubgroup D.X :=
    { carrier := {x | c x ∈ S ∧ c (-x) ∈ S}
      zero_mem' := by simp [c, ← AddMonoidAlgebra.one_def]
      add_mem' := by
        intro x y hx hy
        exact ⟨c_mul x y ▸ S.mul_mem hx.1 hy.1,
          by simpa only [neg_add, c_mul] using S.mul_mem hx.2 hy.2⟩
      neg_mem' := by
        intro x hx
        exact ⟨hx.2, by simpa only [neg_neg] using hx.1⟩ }
  have hweights : Submodule.span ℤ (Set.range w) ≤ weights.toIntSubmodule :=
    Submodule.span_le.mpr fun _ ⟨i, hi⟩ => hi ▸
      ⟨Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩), Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)⟩
  change S = ⊤
  rw [eq_top_iff]
  suffices H : ∀ x : AddMonoidAlgebra ℤ D.X, x ∈ S by exact fun x _ => H x
  intro x
  induction x using AddMonoidAlgebra.induction_on with
  | of m =>
    have hm : m ∈ Submodule.span ℤ (Set.range w) := hw ▸ Submodule.mem_top
    exact (hweights hm).1
  | add x y hx hy => exact S.add_mem hx hy
  | smul r x hx => exact S.smul_mem hx r

/-- If each entry test isolates one root variable up to terms in strictly
smaller heights, every root variable is in the coordinate image. -/
theorem recover_coordinates {σ τ : Type*} (height : σ → ℕ)
    (entry : τ → MvPolynomial σ ℤ)
    (hentry : ∀ a, ∃ P : MvPolynomial τ ℤ, ∃ r : MvPolynomial σ ℤ,
      r ∈ Algebra.adjoin ℤ (MvPolynomial.X '' {b | height b < height a}) ∧
      MvPolynomial.aeval entry P = MvPolynomial.X a + r) :
    ∀ a, ∃ P : MvPolynomial τ ℤ, MvPolynomial.aeval entry P = MvPolynomial.X a := by
  let f : MvPolynomial τ ℤ →ₐ[ℤ] MvPolynomial σ ℤ := MvPolynomial.aeval entry
  have recover (n : ℕ) (a : σ) (ha : height a = n) : MvPolynomial.X a ∈ f.range := by
    induction n using Nat.strong_induction_on generalizing a with
    | h n ih =>
      obtain ⟨P, r, hr, hP⟩ := hentry a
      have hrange : r ∈ f.range := by
        apply (Algebra.adjoin_le ?_) hr
        rintro _ ⟨b, hb, rfl⟩
        exact ih (height b) (ha ▸ hb) b rfl
      have hsum : MvPolynomial.X a + r ∈ f.range := ⟨P, hP⟩
      simpa using f.range.sub_mem hsum hrange
  intro a
  exact recover (height a) a rfl

/-- A monomial of root weight either consists of the root variable itself
or uses variables of strictly smaller height. -/
theorem lower_variables_or_single {σ X : Type*} [AddCommGroup X] (root : σ ↪ X)
    (h : X →ₗ[ℤ] ℤ) (hpos : ∀ b, 0 < h (root b)) (a : σ) (m : σ →₀ ℕ)
    (hs : m.sum (fun b n => n • root b) = root a) :
    m = Finsupp.single a 1 ∨ ∀ b ∈ m.support, h (root b) < h (root a) := by
  classical
  by_cases hsmall : ∀ b ∈ m.support, h (root b) < h (root a)
  · exact Or.inr hsmall
  left
  push Not at hsmall
  obtain ⟨b, hb, hba⟩ := hsmall
  let term (c : σ) := (m c : ℤ) * h (root c)
  have htotal : ∑ c ∈ m.support, term c = h (root a) := by
    simpa only [term, Finsupp.sum, map_sum, map_nsmul, nsmul_eq_mul] using congrArg h hs
  have hpos_term (c : σ) (hc : c ∈ m.support) : 0 < term c :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hc)) (hpos c)
  have hrest : 0 ≤ ∑ c ∈ m.support.erase b, term c := Finset.sum_nonneg
    (fun c hc => (hpos_term c (Finset.mem_of_mem_erase hc)).le)
  have hm : 1 ≤ (m b : ℤ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hb)
  have hterm : h (root a) ≤ term b := hba.trans (by
    simpa only [term, one_mul] using mul_le_mul_of_nonneg_right hm (hpos b).le)
  have hsplit := (Finset.sum_erase_add m.support term hb).trans htotal
  have hrest_zero : (∑ c ∈ m.support.erase b, term c) = 0 := by omega
  have hterm_eq : term b = h (root a) := by omega
  have hmb : m b = 1 := by
    by_contra hne
    have hm' : (1 : ℤ) < (m b : ℤ) := by omega
    have hh : h (root b) < term b := by
      simpa only [term, one_mul] using mul_lt_mul_of_pos_right hm' (hpos b)
    omega
  have hsingle : m = Finsupp.single b 1 := by
    ext c
    by_cases he : c = b
    · subst c
      simp [hmb]
    · have hc : m c = 0 := by
        by_contra hne
        have hmem : c ∈ m.support.erase b := Finset.mem_erase.mpr
          ⟨he, Finsupp.mem_support_iff.mpr hne⟩
        have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj =>
          (hpos_term j (Finset.mem_of_mem_erase hj)).le)).mp hrest_zero c hmem
        exact (hpos_term c (Finset.mem_of_mem_erase hmem)).ne' hz
      simp [hc, Finsupp.single_eq_of_ne he]
  have hr : root b = root a := by simpa [hsingle, Finsupp.sum_single_index] using hs
  rw [hsingle, root.injective hr]

/-- Removing the linear root term leaves a polynomial generated by the
variables of strictly smaller height. -/
theorem coeff_weight_remainder {σ X : Type*} [AddCommGroup X] (root : σ ↪ X)
    (h : X →ₗ[ℤ] ℤ) (hpos : ∀ b, 0 < h (root b)) (a : σ) (p : MvPolynomial σ ℤ)
    (hlinear : p.coeff (Finsupp.single a 1) = 1)
    (hweight : ∀ m, p.coeff m ≠ 0 → m.sum (fun b n => n • root b) = root a) :
    p - MvPolynomial.X a ∈ Algebra.adjoin ℤ (MvPolynomial.X '' {b | h (root b) < h (root a)}) := by
  classical
  let S : Subalgebra ℤ (MvPolynomial σ ℤ) := Algebra.adjoin ℤ (MvPolynomial.X '' {b | h (root b) < h (root a)})
  let q := p - MvPolynomial.X a
  change q ∈ S
  rw [q.as_sum]
  apply S.sum_mem
  intro m hm
  have hm' := MvPolynomial.mem_support_iff.mp hm
  have hne : m ≠ Finsupp.single a 1 := by
    rintro rfl
    apply hm'
    simp [q, hlinear, MvPolynomial.coeff_X]
  have hp : p.coeff m ≠ 0 := by
    intro hz
    apply hm'
    simp [q, hz, MvPolynomial.coeff_X, Ne.symm hne]
  have hsmall := (lower_variables_or_single root h hpos a m (hweight m hp)).resolve_left hne
  rw [MvPolynomial.monomial_eq]
  apply S.mul_mem (S.algebraMap_mem _)
  apply S.prod_mem
  intro b hb
  exact S.pow_mem (Algebra.subset_adjoin ⟨b, hsmall b hb, rfl⟩) _

/-- Weight-homogeneous coefficient tests with linear coefficient one provide
integral polynomial inverse coordinates on the whole product. -/
theorem recover_coordinates_of_weights {σ τ X : Type*} [AddCommGroup X]
    (root : σ ↪ X) (height : X →ₗ[ℤ] ℤ) (hpos : ∀ a, 0 < height (root a))
    (entry : τ → MvPolynomial σ ℤ) (test : σ → MvPolynomial τ ℤ)
    (hlinear : ∀ a, (MvPolynomial.aeval entry (test a)).coeff (Finsupp.single a 1) = 1)
    (hweight : ∀ a m, (MvPolynomial.aeval entry (test a)).coeff m ≠ 0 →
      m.sum (fun b n => n • root b) = root a) :
    ∀ a, ∃ f : MvPolynomial τ ℤ, MvPolynomial.aeval entry f = MvPolynomial.X a := by
  apply recover_coordinates (fun a => (height (root a)).toNat)
  intro a
  let p := MvPolynomial.aeval entry (test a)
  refine ⟨test a, p - MvPolynomial.X a, ?_, (add_sub_cancel _ _).symm⟩
  apply (Algebra.adjoin_mono ?_) (coeff_weight_remainder root height hpos a p (hlinear a) (hweight a))
  rintro _ ⟨b, hb, rfl⟩
  have hh : height (root b) < height (root a) := hb
  have hn := hpos b
  have hlt : (height (root b)).toNat < (height (root a)).toNat := by omega
  exact ⟨b, hlt, rfl⟩

/-- Having an inverse polynomial for every variable makes the restriction
homomorphism on coordinate rings surjective. -/
theorem aeval_surjective_of_coordinates {σ τ : Type*} (entry : τ → MvPolynomial σ ℤ)
    (h : ∀ a, ∃ f : MvPolynomial τ ℤ, MvPolynomial.aeval entry f = MvPolynomial.X a) :
    Function.Surjective (MvPolynomial.aeval (R := ℤ) entry) := by
  let F : MvPolynomial τ ℤ →ₐ[ℤ] MvPolynomial σ ℤ := MvPolynomial.aeval entry
  classical
  choose f hf using h
  have hcomp : F.comp (MvPolynomial.aeval f) = AlgHom.id ℤ (MvPolynomial σ ℤ) := by
    ext a : 1
    simpa [F] using hf a
  intro p
  exact ⟨MvPolynomial.aeval f p, DFunLike.congr_fun hcomp p⟩

/-- After integral series substitution and multiplication by an integral
scalar series, each coefficient remains in the original coefficient span. -/
theorem coeff_substitution_mem_span {R S σ τ ι : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Fintype ι]
    (p : ι → MvPolynomial σ S) (g : σ → MvPowerSeries τ R)
    (c : MvPowerSeries τ R) (d : τ →₀ ℕ) :
    (fun j => MvPowerSeries.coeff d
      (MvPowerSeries.map (algebraMap R S) c *
        MvPolynomial.eval₂Hom MvPowerSeries.C
          (fun a => MvPowerSeries.map (algebraMap R S) (g a)) (p j))) ∈
        Submodule.span R (Set.range fun m j => (p j).coeff m) := by
  classical
  let T := Finset.univ.biUnion (fun j => (p j).support)
  let r (m : σ →₀ ℕ) :=
    MvPowerSeries.coeff d (c * m.prod fun a n => g a ^ n)
  have hsum : (fun j => MvPowerSeries.coeff d
      (MvPowerSeries.map (algebraMap R S) c *
        MvPolynomial.eval₂Hom MvPowerSeries.C
          (fun a => MvPowerSeries.map (algebraMap R S) (g a)) (p j))) =
      ∑ m ∈ T, r m • (fun j => (p j).coeff m) := by
    funext j
    have hsupport : (p j).support ⊆ T :=
      Finset.subset_biUnion_of_mem (fun i => (p i).support) (Finset.mem_univ j)
    have hp : p j = ∑ m ∈ T, MvPolynomial.monomial m ((p j).coeff m) := by
      rw [← Finset.sum_subset hsupport]
      · exact MvPolynomial.as_sum _
      · intro m _ hm
        simp [MvPolynomial.notMem_support_iff.mp hm]
    rw [hp]
    simp only [map_sum, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro m _
    rw [MvPolynomial.eval₂Hom_monomial]
    rw [← mul_left_comm, MvPowerSeries.coeff_C_mul]
    have hmap : MvPowerSeries.map (algebraMap R S) c *
        m.prod (fun a n => MvPowerSeries.map (algebraMap R S) (g a) ^ n) =
        MvPowerSeries.map (algebraMap R S) (c * m.prod fun a n => g a ^ n) := by
      simp [Finsupp.prod, map_prod]
    rw [hmap, MvPowerSeries.coeff_map, Algebra.smul_def, mul_comm]
  rw [hsum]
  exact Submodule.sum_mem _ fun m _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-- In separate formal variables, extraction of a root parameter coefficient
and then a cell coefficient is the corresponding coefficient matrix acting
on the cell coefficient vector. -/
theorem coeff_mulVec_powerSeries {K σ ι : Type*} [CommRing K] [Fintype ι]
    (P : Matrix ι ι (Polynomial K)) (x : ι → MvPowerSeries σ K)
    (m : ℕ) (d : σ →₀ ℕ) :
    (fun i => MvPowerSeries.coeff d (PowerSeries.coeff m
       ((Matrix.of (fun i j => ((((P i j).map MvPowerSeries.C) :
         Polynomial (MvPowerSeries σ K)) : PowerSeries (MvPowerSeries σ K)))).mulVec (fun j => PowerSeries.C (x j)) i))) =
    (Matrix.of (fun i j => (P i j).coeff m)).mulVec
      (fun j => MvPowerSeries.coeff d (x j)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, PowerSeries.coeff_mul_C,
    Polynomial.coeff_coe, Polynomial.coeff_map, MvPowerSeries.coeff_C_mul]

/-- A polynomial image with polynomial inverse coordinates descends along an
injective change of coefficients. Applied to the universal matrix for a
product or inverse, this allows the subgroup identities to descend. -/
theorem polynomial_image_descends {σ τ R S : Type*} [CommRing R] [CommRing S]
    (P : τ → MvPolynomial σ ℤ) (inverse : σ → MvPolynomial τ ℤ)
    (hleft : ∀ a, MvPolynomial.aeval P (inverse a) = MvPolynomial.X a)
    (f : R →+* S) (hf : Function.Injective f) (Y : τ → R)
    (hY : ∃ x : σ → S, ∀ i, (P i).eval₂ (Int.castRingHom S) x = f (Y i)) :
    ∃ x : σ → R, ∀ i, (P i).eval₂ (Int.castRingHom R) x = Y i := by
  obtain ⟨x, hx⟩ := hY
  let y (a : σ) := (inverse a).eval₂ (Int.castRingHom R) Y
  have hmap : f.comp (Int.castRingHom R) = Int.castRingHom S := by
    ext n
    exact map_intCast f n
  have hy (a : σ) : f (y a) = x a := by
    have hh := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom S) x) (hleft a)
    rw [MvPolynomial.eval₂Hom_X'] at hh
    rw [MvPolynomial.aeval_eq_eval₂Hom] at hh
    rw [MvPolynomial.map_eval₂Hom] at hh
    rw [show (MvPolynomial.eval₂Hom (Int.castRingHom S) x).comp
        (algebraMap ℤ (MvPolynomial σ ℤ)) = Int.castRingHom S from Subsingleton.elim _ _] at hh
    rw [MvPolynomial.eval₂_comp_left, hmap]
    rw [show (fun i => (MvPolynomial.eval₂Hom (Int.castRingHom S) x) (P i)) = f ∘ Y
      from funext hx] at hh
    exact hh
  refine ⟨y, fun i => hf ?_⟩
  rw [MvPolynomial.eval₂_comp_left, hmap]
  rw [show (⇑f ∘ y) = x from funext hy]
  exact hx i

/-- A sorted identity with integral formal parameters implies that every root
polynomial coefficient preserves the integer span of the cell coefficients. -/
theorem coeff_mulVec_mem_span_of_collection {K σ ι : Type*}
    [Field K] [CharZero K] [Fintype ι]
    (P : Matrix ι ι (Polynomial K)) (cell : ι → MvPolynomial σ K)
    (g : σ → MvPowerSeries (Option σ) ℤ) (c : MvPowerSeries (Option σ) ℤ)
    (hsort : ∀ i,
      (Matrix.of (fun i j => ((((P i j).map MvPowerSeries.C) :
          Polynomial (MvPowerSeries σ K)) : PowerSeries (MvPowerSeries σ K)))).mulVec
        (fun j => PowerSeries.C (cell j : MvPowerSeries σ K)) i =
      MvPowerSeries.optionEquivLeft σ K
        (MvPowerSeries.map (algebraMap ℤ K) c *
          MvPolynomial.eval₂Hom MvPowerSeries.C
            (fun a => MvPowerSeries.map (algebraMap ℤ K) (g a)) (cell i)))
    (m : ℕ) {v : ι → K}
    (hv : v ∈ Submodule.span ℤ (Set.range fun d j => (cell j).coeff d)) :
    (Matrix.of (fun i j => (P i j).coeff m)).mulVec v ∈
      Submodule.span ℤ (Set.range fun d j => (cell j).coeff d) := by
  let L := Submodule.span ℤ (Set.range fun d j => (cell j).coeff d)
  let F : (ι → K) →ₗ[ℤ] (ι → K) :=
    (Matrix.of (fun i j => (P i j).coeff m)).mulVecLin.restrictScalars ℤ
  have hstable : L ≤ L.comap F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    change (Matrix.of (fun i j => (P i j).coeff m)).mulVec (fun j => (cell j).coeff d) ∈ L
    have hcoeff := coeff_mulVec_powerSeries P (fun j => (cell j : MvPowerSeries σ K)) m d
    simp only [MvPolynomial.coeff_coe, hsort, MvPowerSeries.coeff_coeff_optionEquivLeft] at hcoeff
    rw [← hcoeff]
    exact coeff_substitution_mem_span cell g c (d.optionElim m)
  exact hstable hv

section

open CategoryTheory
open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates rootIndex)
open Specs.RootGroups (AdditiveLine)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (characterValue pairing)
open Specs.AdjointRepresentation (GroupPoints)
open CocharacterDynamics (cocharacterPoint)
open Specs.IntegralLattices

noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}

private def markedCharacter (Q : Realization D A) (x : D.X) : Character Q.pinned.pair.T.group :=
  Additive.toMul (Q.datumIso.val.weightEquiv x)

private def markedCocharacter (Q : Realization D A) (y : D.Y) : Cocharacter Q.pinned.pair.T.group :=
  Additive.toMul (Q.datumIso.val.coweightEquiv.symm y)

private theorem markedCharacter_root (Q : Realization D A) (a : D.I) :
    markedCharacter Q (D.datum.root a) = (rootIndex Q a).val := by
  let : IsCommMonObj Q.pinned.pair.T.group.X := Q.attached.comm
  unfold markedCharacter
  rw [RootPairing.Equiv.weightEquiv_apply, RootPairing.Hom.root_weightMap_apply]
  exact congrArg Additive.toMul (Q.attached.datum.root_eq _)

private theorem markedCharacter_pairing (Q : Realization D A) (x : D.X) (y : D.Y) :
    pairing _ (markedCharacter Q x) (markedCocharacter Q y) = D.datum.toLinearMap x y := by
  let : IsCommMonObj Q.pinned.pair.T.group.X := Q.attached.comm
  let F := Q.datumIso.val
  rw [← Q.attached.datum.pairing_eq]
  have ht := LinearMap.congr_fun
    (F.toHom.weight_coweight_transpose_apply D.datum Q.attached.toBased.datum
      (F.coweightEquiv.symm y)) x
  change Q.attached.toBased.datum.toLinearMap (F.weightEquiv x) (F.coweightEquiv.symm y) =
    D.datum.toLinearMap x (F.coweightEquiv (F.coweightEquiv.symm y)) at ht
  rw [LinearEquiv.apply_symm_apply] at ht
  exact ht

private theorem polynomial_coeff_eval₂_C_mul_X {K : Type*} [CommRing K]
    (p : Polynomial K) (c : K) (m : ℕ) :
    (p.eval₂ Polynomial.C (Polynomial.C c * Polynomial.X)).coeff m = c ^ m * p.coeff m := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, mul_pow, ← map_pow, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.C_mul_X_pow_eq_monomial]
    by_cases h : n = m
    · subst n
      simp [mul_comm]
    · simp [Polynomial.coeff_monomial, h]

variable [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {lam : D.X}

/-- Torus conjugation on the actual root coordinates gives the weight shift
of the root operator in each rational highest-weight module. -/
theorem rootOperator_weight_shift
    (V : RationalHighestWeight z e h lam) (a : D.I) (i j : Index.{u} V.dimension)
    (hij : V.weight i ≠ V.weight j + D.datum.root a) : V.rootOperator a i j = 0 := by
  classical
  let K := RationalField.{u}
  let R : TestAlgebra K := CommAlgCat.of K (Polynomial K)
  let c : Kˣ := Units.mk0 2 (by
    intro hz
    have h' : (2 : ℚ) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg (ULift.ringEquiv : K ≃+* ℚ) hz
    exact (by norm_num : (2 : ℚ) ≠ 0) h')
  let B (x : D.X) (y : D.Y) : ℤ := D.datum.toLinearMap x y
  let P := exponentialPolynomial (V.rootOperator a) V.nilpotenceBound
  by_contra hne
  have he (y : D.Y) : B (V.weight i) y = B (V.weight j + D.datum.root a) y := by
    let s : Rˣ := Units.map Polynomial.C.toMonoidHom c
    let t : GroupPoints Q.pinned.pair.T.group R := cocharacterPoint (markedCocharacter Q y) R s
    let g : GroupPoints Q.pinned.pair.G.val R := t ≫ Q.pinned.pair.T.inclusion.hom.hom
    let l (x : D.X) : K := ((c ^ B x y : Kˣ) : K)
    have hl (x : D.X) : characterValue (markedCharacter Q x) R t = Polynomial.C (l x) := by
      dsimp only [t]
      rw [(RootData.CharacterPairing.characterPairingComposition _ _ _).2, markedCharacter_pairing]
      change (↑((Units.map Polynomial.C.toMonoidHom c) ^ B x y) : Polynomial K) = _
      rw [← map_zpow]
      rfl
    have hconj := (z a).property R t (Polynomial.X : R)
    change g * Specs.IntegralRootRelations.root Q z a R (Polynomial.X : R) * g⁻¹ =
        Specs.IntegralRootRelations.root Q z a R
          (characterValue (rootIndex Q a).val R t * Polynomial.X) at hconj
    rw [← markedCharacter_root Q a, hl] at hconj
    have hm := congrArg (fun x => x * g) hconj
    rw [mul_assoc, inv_mul_cancel, mul_one] at hm
    let f : GroupPoints Q.pinned.pair.G.val R →*
        Matrix.GeneralLinearGroup (Index.{u} V.dimension) R := (V.action.app R).hom
    have hmm := congrArg (fun x => (f x).val) hm
    simp only [map_mul, Units.val_mul] at hmm
    have hg : (f g).val = Matrix.diagonal (fun k => Polynomial.C (l (V.weight k))) := by
      change (V.action.app R g : Matrix.GeneralLinearGroup _ R).val = _
      rw [V.torus_action R t]
      congr 1
      funext k
      exact hl (V.weight k)
    have hx := V.root_action a R (Polynomial.X : R)
    have hx' := V.root_action a R (Polynomial.C (l (D.datum.root a)) * Polynomial.X)
    change (f (Specs.IntegralRootRelations.root Q z a R Polynomial.X)).val = _ at hx
    change (f (Specs.IntegralRootRelations.root Q z a R
      (Polynomial.C (l (D.datum.root a)) * Polynomial.X))).val = _ at hx'
    rw [hg, hx, hx'] at hmm
    have hentry := congrArg (fun M : Matrix (Index.{u} V.dimension) _ R => M i j) hmm
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
    change Polynomial.C (l (V.weight i)) * (P i j).eval₂ Polynomial.C Polynomial.X =
      (P i j).eval₂ Polynomial.C (Polynomial.C (l (D.datum.root a)) * Polynomial.X) *
        Polynomial.C (l (V.weight j)) at hentry
    rw [Polynomial.eval₂_C_X] at hentry
    have hcoeffP : (P i j).coeff 1 = V.rootOperator a i j := by
      exact (exponentialPolynomial_coeff (V.rootOperator a) (V.nilpotent a) 1 i j).trans
        (congrArg (fun E : Matrix _ _ K => E i j) (dividedPower_one (V.rootOperator a)))
    have hcoeff := congrArg (fun p : Polynomial K => p.coeff 1) hentry
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, polynomial_coeff_eval₂_C_mul_X,
      pow_one, hcoeffP] at hcoeff
    have hc : l (V.weight i) = l (D.datum.root a) * l (V.weight j) := by
      apply mul_right_cancel₀ hne
      rw [hcoeff, mul_right_comm]
    have hB : B (V.weight j + D.datum.root a) y = B (D.datum.root a) y + B (V.weight j) y := by
      simp only [B, LinearMap.map_add, LinearMap.add_apply, add_comm]
    dsimp only [l] at hc
    rw [← Units.val_mul, ← zpow_add] at hc
    have hd := congrArg (ULift.ringEquiv : K ≃+* ℚ) hc
    simp only [Units.val_zpow_eq_zpow_val, c, Units.val_mk0] at hd
    change (2 : ℚ) ^ B (V.weight i) y = (2 : ℚ) ^ (B (D.datum.root a) y + B (V.weight j) y) at hd
    rw [hB]
    exact zpow_right_injective₀ (show (0 : ℚ) < 2 by norm_num) (by norm_num) hd
  apply hij
  apply D.datum.toPerfPair.injective
  ext y
  exact he y

end

end

section

open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (Enumerates)
open Specs.IntegralLattices
open scoped Classical
noncomputable section

private theorem coeff_aeval_X_mul_of_independent {σ K : Type*} [CommRing K] [DecidableEq σ]
    (a : σ) (p : Polynomial K) (q : MvPolynomial σ K)
    (hq : ∀ d : σ →₀ ℕ, d a ≠ 0 → q.coeff d = 0) (m : σ →₀ ℕ) :
    (Polynomial.aeval (MvPolynomial.X a) p * q).coeff m =
      p.coeff (m a) * q.coeff (m.erase a) := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' =>
    simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hp, hp']
  | monomial n c =>
    rw [Polynomial.aeval_def, Polynomial.eval₂_monomial, MvPolynomial.algebraMap_eq,
      MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul']
    simp only [Finsupp.single_le_iff, Polynomial.coeff_monomial]
    rcases lt_trichotomy n (m a) with h | h | h
    · have hne : (m - Finsupp.single a n) a ≠ 0 := by
        simpa using Nat.sub_ne_zero_of_lt h
      rw [ite_eq_left h.le, hq _ hne, ite_eq_right h.ne, mul_zero, zero_mul]
    · subst n
      have hd : m - Finsupp.single a (m a) = m.erase a := by
        ext b
        by_cases hb : b = a
        · subst b
          simp
        · simp [Finsupp.single_eq_of_ne hb, Finsupp.erase_ne hb]
      rw [ite_eq_left le_rfl, ite_eq_left rfl, hd]
    · rw [ite_eq_right (not_le_of_gt h), ite_eq_right h.ne', zero_mul]

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {lam : D.X}

/-- The negative-root factors applied to the highest vector in their
independent polynomial coordinates. -/
def negativeCellPolynomial (V : RationalHighestWeight z e h lam) :
    List (Negative D) → Index.{u} V.dimension → MvPolynomial (Negative D) RationalField.{u}
  | [] => fun j => MvPolynomial.C (V.highest j)
  | a :: l => ((Polynomial.aeval (MvPolynomial.X a)).toRingHom.mapMatrix
      (exponentialPolynomial (V.rootOperator a) V.nilpotenceBound)).mulVec
        (negativeCellPolynomial V l)

private theorem negativeCellPolynomial_coeff_of_nodup (V : RationalHighestWeight z e h lam)
    (l : List (Negative D)) (hn : l.Nodup) (m : Negative D →₀ ℕ) :
    (fun j => (negativeCellPolynomial V l j).coeff m) =
      if ∀ a, m a ≠ 0 → a ∈ l then V.negativeCoefficient l m else 0 := by
  classical
  induction l generalizing m with
  | nil =>
    have hm : (∀ a, m a ≠ 0 → a ∈ ([] : List (Negative D))) ↔ m = 0 := by
      simp [Finsupp.ext_iff]
    rw [hm]
    funext j
    by_cases hm' : m = 0
    · subst m
      simp [negativeCellPolynomial]
    · simp [hm', Ne.symm hm', negativeCellPolynomial, MvPolynomial.coeff_C]
  | cons a l ih =>
    let R := exponentialPolynomial (V.rootOperator a) V.nilpotenceBound
    let q := negativeCellPolynomial V l
    have hq (j : Index.{u} V.dimension) (d : Negative D →₀ ℕ) (hd : d a ≠ 0) :
        (q j).coeff d = 0 := by
      have h := congrFun (ih hn.of_cons d) j
      rw [ite_eq_right (fun hh => hn.notMem (hh a hd))] at h
      exact h
    have hcoeff : (fun j => (negativeCellPolynomial V (a :: l) j).coeff m) =
        (dividedPower (V.rootOperator a) (m a)).mulVec (fun j => (q j).coeff (m.erase a)) := by
      funext j
      simp only [negativeCellPolynomial, Matrix.mulVec, dotProduct, MvPolynomial.coeff_sum, RingHom.mapMatrix_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (Polynomial.aeval (MvPolynomial.X a) (R j i) * q i).coeff m = _
      rw [coeff_aeval_X_mul_of_independent a _ _ (hq i)]
      exact congrArg (· * (q i).coeff (m.erase a))
        (exponentialPolynomial_coeff (V.rootOperator a) (V.nilpotent a) (m a) j i)
    have hmem : (∀ b, m b ≠ 0 → b ∈ a :: l) ↔ (∀ b, m.erase a b ≠ 0 → b ∈ l) := by
      constructor
      · intro H b hb
        have hba : b ≠ a := by
          rintro rfl
          simp at hb
        rw [Finsupp.erase_ne hba] at hb
        exact (List.mem_cons.mp (H b hb)).resolve_left hba
      · intro H b hb
        by_cases hba : b = a
        · simp [hba]
        · apply List.mem_cons_of_mem
          apply H
          simpa only [Finsupp.erase_ne hba]
    have herase : V.negativeCoefficient l (m.erase a) = V.negativeCoefficient l m := by
      unfold RationalHighestWeight.negativeCoefficient
      congr 2
      apply List.map_congr_left
      intro b hb
      have hba : b ≠ a := fun hh => (List.nodup_cons.mp hn).1 (hh ▸ hb)
      rw [Finsupp.erase_ne hba]
    rw [hcoeff, hmem, show (fun j => (q j).coeff (m.erase a)) =
      if ∀ b, m.erase a b ≠ 0 → b ∈ l then V.negativeCoefficient l (m.erase a) else 0
        from ih hn.of_cons (m.erase a)]
    split_ifs
    · rw [herase]
      simp only [RationalHighestWeight.negativeCoefficient, List.map_cons, List.prod_cons,
        Matrix.mulVec_mulVec]
    · exact Matrix.mulVec_zero _

theorem negativeCellPolynomial_coeff (V : RationalHighestWeight z e h lam)
    (l : List (Negative D)) (hl : Enumerates l Set.univ) (m : Negative D →₀ ℕ) :
    (fun j => (negativeCellPolynomial V l j).coeff m) = V.negativeCoefficient l m := by
  rw [negativeCellPolynomial_coeff_of_nodup V l hl.1 m, ite_eq_left]
  exact fun a _ => (hl.2 a).mpr (Set.mem_univ a)

end

end

section

open CategoryTheory
open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates FormalBigCellProduct CellVariables CellAlgebra
  onePlusSeries cellPoint genericCellPoint integralCellPoint torus)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (Enumerates)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralLattices
open CocharacterDynamics (cocharacterPoint)
open scoped Classical

noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {lam : D.X}

local notation "B" => D.datum.toLinearMap

private theorem mapMatrix_mulVec {R S ι : Type*} [CommRing R] [CommRing S]
    [Fintype ι] [DecidableEq ι] (f : R →+* S) (M : Matrix ι ι R) (v : ι → R) :
    f ∘ M.mulVec v = (f.mapMatrix M).mulVec (f ∘ v) :=
  funext (f.map_mulVec M v)

private def rootMatrixAt (V : RationalHighestWeight z e h lam)
    {R : Type*} [CommRing R] [Algebra RationalField.{u} R] (a : D.I) (x : R) :
    Matrix (Index.{u} V.dimension) (Index.{u} V.dimension) R :=
  (Polynomial.eval₂RingHom (algebraMap RationalField.{u} R) x).mapMatrix
    (exponentialPolynomial (V.rootOperator a) V.nilpotenceBound)

private theorem map_rootMatrixAt (V : RationalHighestWeight z e h lam)
    {R S : Type*} [CommRing R] [CommRing S] [Algebra RationalField.{u} R] [Algebra RationalField.{u} S]
    (f : R →ₐ[RationalField.{u}] S) (a : D.I) (x : R) :
    f.toRingHom.mapMatrix (rootMatrixAt V a x) = rootMatrixAt V a (f x) := by
  ext i j
  simp only [rootMatrixAt, RingHom.mapMatrix_apply, Matrix.map_apply]
  change f ((exponentialPolynomial (V.rootOperator a) V.nilpotenceBound i j).eval₂
      (algebraMap RationalField.{u} R) x) =
    (exponentialPolynomial (V.rootOperator a) V.nilpotenceBound i j).eval₂ (algebraMap RationalField.{u} S) (f x)
  rw [← f.comp_algebraMap]
  exact Polynomial.hom_eval₂ _ (algebraMap _ R) f.toRingHom x

private theorem rootMatrixAt_zero (V : RationalHighestWeight z e h lam)
    {R : Type*} [CommRing R] [Algebra RationalField.{u} R] (a : D.I) :
    rootMatrixAt V a (0 : R) = 1 := by
  have h0 : (Polynomial.evalRingHom (0 : RationalField.{u})).mapMatrix
      (exponentialPolynomial (V.rootOperator a) V.nilpotenceBound) = 1 := by
    apply Matrix.ext
    intro i j
    change (exponentialPolynomial (V.rootOperator a) V.nilpotenceBound i j).eval 0 = _
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      exponentialPolynomial_coeff (V.rootOperator a) (V.nilpotent a), dividedPower_zero]
  have hcomp : Polynomial.eval₂RingHom (algebraMap RationalField.{u} R) (0 : R) =
      (algebraMap RationalField.{u} R).comp (Polynomial.evalRingHom 0) := by
    ext <;> simp [Polynomial.coe_evalRingHom]
  rw [rootMatrixAt, hcomp]
  change (algebraMap RationalField.{u} R).mapMatrix ((Polynomial.evalRingHom (0 : RationalField.{u})).mapMatrix
      (exponentialPolynomial (V.rootOperator a) V.nilpotenceBound)) = _
  rw [h0, map_one]

private theorem positive_rootMatrixAt_highest (V : RationalHighestWeight z e h lam)
    {R : Type*} [CommRing R] [Algebra RationalField.{u} R] (a : Positive D) (x : R) :
    (rootMatrixAt V a.val x).mulVec (algebraMap RationalField.{u} R ∘ V.highest) =
      algebraMap RationalField.{u} R ∘ V.highest := by
  let P := exponentialPolynomial (V.rootOperator a.val) V.nilpotenceBound
  have hp : P.mulVec (Polynomial.C ∘ V.highest) = Polynomial.C ∘ V.highest := by
    funext i
    ext m
    simp only [Matrix.mulVec, dotProduct, Polynomial.finsetSum_coeff, Function.comp_apply,
      Polynomial.coeff_mul_C]
    have hv (m : ℕ) :
        (dividedPower (V.rootOperator a.val) m).mulVec V.highest =
          if m = 0 then V.highest else 0 := by
      cases m with
      | zero => simp
      | succ n =>
        rw [dividedPower, Matrix.smul_mulVec, pow_succ, ← Matrix.mulVec_mulVec,
          positive_root_mulVec_highest V a, Matrix.mulVec_zero]
        simp
    have he := congrFun (hv m) i
    rw [Matrix.mulVec, dotProduct] at he
    simp only [P, exponentialPolynomial_coeff (V.rootOperator a.val) (V.nilpotent a.val)]
    rw [he]
    by_cases hm : m = 0 <;> simp [Polynomial.coeff_C, hm]
  let f := Polynomial.eval₂RingHom (algebraMap RationalField.{u} R) x
  have h' := congrArg (fun v => f ∘ v) hp
  rw [mapMatrix_mulVec] at h'
  have hc : f ∘ Polynomial.C ∘ V.highest = algebraMap RationalField.{u} R ∘ V.highest := by
    funext i
    exact RingHom.congr_fun (Polynomial.eval₂RingHom_comp_C _ _) (V.highest i)
  rw [hc] at h'
  exact h' 

private def torusMatrixAt (V : RationalHighestWeight z e h lam)
    {R : Type*} [CommRing R] (y : D.Y) (t : Rˣ) :
    Matrix (Index.{u} V.dimension) (Index.{u} V.dimension) R :=
  Matrix.diagonal (fun j => ↑(t ^ B (V.weight j) y))

private theorem map_torusMatrixAt (V : RationalHighestWeight z e h lam)
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (y : D.Y) (t : Rˣ) :
    f.mapMatrix (torusMatrixAt V y t) = torusMatrixAt V y (Units.map f.toMonoidHom t) := by
  ext i j
  by_cases hi : i = j
  · subst j
    simp only [torusMatrixAt, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq]
    rw [← map_zpow]
    rfl
  · simp [torusMatrixAt, RingHom.mapMatrix_apply, Matrix.diagonal_apply_ne _ hi]

private theorem torusMatrixAt_highest (V : RationalHighestWeight z e h lam)
    {R : Type*} [CommRing R] [Algebra RationalField.{u} R] (y : D.Y) (t : Rˣ) :
    (torusMatrixAt V y t).mulVec (algebraMap RationalField.{u} R ∘ V.highest) =
      (↑(t ^ B lam y) : R) • (algebraMap RationalField.{u} R ∘ V.highest) := by
  funext j
  rw [torusMatrixAt, Matrix.mulVec_diagonal]
  by_cases hj : V.weight j = lam
  · simp [hj, smul_eq_mul]
  · simp [V.highest_support j hj]

private def cellMatrix (V : RationalHighestWeight z e h lam)
    {R : Type*} [CommRing R] [Algebra RationalField.{u} R] {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative : List (Negative D)) (positive : List (Positive D))
    (v : D.I → R) (t : Fin r → Rˣ) :
    Matrix (Index.{u} V.dimension) (Index.{u} V.dimension) R :=
  (negative.map (fun a => rootMatrixAt V a.val (v a.val))).prod *
    ((List.finRange r).map (fun i => torusMatrixAt V (b i) (t i))).prod *
    (positive.map (fun a => rootMatrixAt V a.val (v a.val))).prod

private theorem cellPoint_action_matrix
    (V : RationalHighestWeight z e h lam) {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative : List (Negative D)) (positive : List (Positive D))
    (R : TestAlgebra RationalField.{u}) (v : D.I → R) (t : Fin r → Rˣ) :
    (V.action.app R (cellPoint Q z b (negative.map Subtype.val) (positive.map Subtype.val)
      R v t) : Matrix.GeneralLinearGroup (Index.{u} V.dimension) R).val =
      cellMatrix V b negative positive v t := by
  let ρ : GroupPoints Q.pinned.pair.G.val R →*
      Matrix (Index.{u} V.dimension) (Index.{u} V.dimension) R :=
    (Units.coeHom _).comp (V.action.app R).hom
  change ρ (cellPoint Q z b (negative.map Subtype.val) (positive.map Subtype.val) R v t) = _
  simp only [cellPoint, List.map_map, map_mul, map_list_prod, cellMatrix]
  congr 1
  · congr 1
    · apply congrArg List.prod
      apply List.map_congr_left
      intro a _
      exact V.root_action a.val R (v a.val)
    · apply congrArg List.prod
      apply List.map_congr_left
      intro i _
      change (V.action.app R (torus Q (b i) R (t i)) :
        Matrix.GeneralLinearGroup (Index.{u} V.dimension) R).val = torusMatrixAt V (b i) (t i)
      rw [torus, V.torus_action]
      apply congrArg Matrix.diagonal
      funext j
      change Specs.CharacterPairing.characterValue
        (markedCharacter Q (V.weight j)) R (cocharacterPoint (markedCocharacter Q (b i)) R (t i)) = _
      rw [(RootData.CharacterPairing.characterPairingComposition _ _ _).2, markedCharacter_pairing]
  · apply congrArg List.prod
    apply List.map_congr_left
    intro a _
    exact V.root_action a.val R (v a.val)

private theorem map_cellMatrix (V : RationalHighestWeight z e h lam)
    {R S : Type*} [CommRing R] [CommRing S] [Algebra RationalField.{u} R] [Algebra RationalField.{u} S]
    (f : R →ₐ[RationalField.{u}] S) {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative : List (Negative D)) (positive : List (Positive D))
    (v : D.I → R) (t : Fin r → Rˣ) :
    f.toRingHom.mapMatrix (cellMatrix V b negative positive v t) =
      cellMatrix V b negative positive (fun a => f (v a)) (fun i => Units.map f.toMonoidHom (t i)) := by
  simp only [cellMatrix, map_mul, map_list_prod, List.map_map, Function.comp_def,
    map_rootMatrixAt, map_torusMatrixAt]

private theorem negativeCellPolynomial_eval (V : RationalHighestWeight z e h lam)
    (negative : List (Negative D)) {R : Type*} [CommRing R] [Algebra RationalField.{u} R] (x : Negative D → R) :
    (fun j => MvPolynomial.aeval x (negativeCellPolynomial V negative j)) =
      ((negative.map (fun a => rootMatrixAt V a.val (x a))).prod).mulVec (algebraMap RationalField.{u} R ∘ V.highest) := by
  induction negative with
  | nil =>
    simp only [negativeCellPolynomial, MvPolynomial.aeval_C, List.map_nil, List.prod_nil,
      Matrix.one_mulVec]
    rfl
  | cons a l ih =>
    simp only [negativeCellPolynomial, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    let f : MvPolynomial (Negative D) RationalField.{u} →+* R := (MvPolynomial.aeval x).toRingHom
    have hm : f.mapMatrix ((Polynomial.aeval (MvPolynomial.X a)).toRingHom.mapMatrix
          (exponentialPolynomial (V.rootOperator a.val) V.nilpotenceBound)) =
        rootMatrixAt V a.val (x a) := by
      have hf : f.comp (Polynomial.aeval (MvPolynomial.X a)).toRingHom =
          Polynomial.eval₂RingHom (algebraMap RationalField.{u} R) (x a) := by
        ext <;> simp [f, Polynomial.eval₂_X]
      ext i j
      change (f.comp (Polynomial.aeval (MvPolynomial.X a)).toRingHom)
        (exponentialPolynomial (V.rootOperator a.val) V.nilpotenceBound i j) = _
      rw [hf]
      rfl
    change f ∘ (((Polynomial.aeval (MvPolynomial.X a)).toRingHom.mapMatrix
      (exponentialPolynomial (V.rootOperator a.val) V.nilpotenceBound)).mulVec
        (negativeCellPolynomial V l)) = _
    rw [mapMatrix_mulVec, hm]
    exact congrArg ((rootMatrixAt V a.val (x a)).mulVec) ih

private theorem cellMatrix_highest (V : RationalHighestWeight z e h lam)
    {R : Type*} [CommRing R] [Algebra RationalField.{u} R]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative : List (Negative D)) (positive : List (Positive D))
    (v : D.I → R) (t : Fin r → Rˣ) :
    (cellMatrix V b negative positive v t).mulVec (algebraMap RationalField.{u} R ∘ V.highest) =
      ((List.finRange r).map (fun i => (↑(t i ^ B lam (b i)) : R))).prod •
        (fun j => MvPolynomial.aeval (fun a : Negative D => v a.val)
          (negativeCellPolynomial V negative j)) := by
  let high := algebraMap RationalField.{u} R ∘ V.highest
  have hp : ((positive.map fun a => rootMatrixAt V a.val (v a.val)).prod).mulVec high = high := by
    induction positive with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih]
      exact positive_rootMatrixAt_highest V a (v a.val)
  have ht (l : List (Fin r)) :
      ((l.map fun i => torusMatrixAt V (b i) (t i)).prod).mulVec high =
        (l.map fun i => (↑(t i ^ B lam (b i)) : R)).prod • high := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]
      change (List.map _ l).prod • (torusMatrixAt V (b i) (t i)).mulVec high = _
      rw [torusMatrixAt_highest, smul_smul, mul_comm]
  change (_ : Matrix _ _ R).mulVec high = _
  rw [cellMatrix, ← Matrix.mulVec_mulVec, hp, ← Matrix.mulVec_mulVec, ht,
    Matrix.mulVec_smul, ← negativeCellPolynomial_eval]

private theorem list_prod_map_eq_of_single {J M : Type*} [Monoid M]
    (l : List J) (hl : l.Nodup) (F : J → M) {j : J} (hj : j ∈ l)
    (hF : ∀ i ∈ l, i ≠ j → F i = 1) :
    (l.map F).prod = F j := by
  obtain ⟨p, q, rfl⟩ := List.append_of_mem hj
  have hq : j ∉ q := (List.nodup_cons.mp hl.of_append_right).1
  have hp : j ∉ p := fun hh =>
    List.disjoint_left.mp (List.disjoint_of_nodup_append hl) hh List.mem_cons_self
  have hprod (s : List J) (hs : j ∉ s) (hsub : ∀ i ∈ s, i ∈ p ++ j :: q) :
      (s.map F).prod = 1 := by
    apply List.prod_eq_one
    rintro _ he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    exact hF i (hsub i hi) (fun hh => hs (hh ▸ hi))
  rw [List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    hprod p hp (fun i hi => List.mem_append_left _ hi),
    hprod q hq (fun i hi => List.mem_append_right _ (List.mem_cons_of_mem _ hi)),
    one_mul, mul_one]

private theorem cellMatrix_single_root (V : RationalHighestWeight z e h lam)
    {R : Type*} [CommRing R] [Algebra RationalField.{u} R]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative : List (Negative D)) (positive : List (Positive D))
    (hn : Enumerates negative Set.univ) (hp : Enumerates positive Set.univ)
    (a : D.I) (x : R) :
    cellMatrix V b negative positive (fun i => if i = a then x else 0) (fun _ => 1) =
      rootMatrixAt V a x := by
  let F (i : D.I) := rootMatrixAt V i (if i = a then x else 0)
  have hF (i : D.I) (hi : i ≠ a) : F i = 1 := by
    simp only [F, ite_eq_right hi, rootMatrixAt_zero]
  have ha : F a = rootMatrixAt V a x := by simp [F]
  have ht : (List.map (fun i => torusMatrixAt V (b i) (1 : Rˣ)) (List.finRange r)).prod =
      (1 : Matrix _ _ R) := by
    apply List.prod_eq_one
    rintro _ hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    simp [torusMatrixAt, Matrix.diagonal_one]
  rw [cellMatrix, ht, mul_one]
  change (negative.map (fun j => F j.val)).prod * (positive.map (fun j => F j.val)).prod = _
  by_cases hs : D.base.IsPos a
  · have hneg : (negative.map (fun j => F j.val)).prod = 1 := by
      apply List.prod_eq_one
      rintro _ hm
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
      exact hF i (fun hi => i.property (hi.symm ▸ hs))
    rw [hneg, one_mul, list_prod_map_eq_of_single positive hp.1 _
      ((hp.2 ⟨a, hs⟩).mpr (Set.mem_univ _)) (fun i _ hi => hF i (fun h => hi (Subtype.ext h)))]
    exact ha
  · have hpos : (positive.map (fun j => F j.val)).prod = 1 := by
      apply List.prod_eq_one
      rintro _ hm
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
      exact hF i (fun hi => hs (hi ▸ i.property))
    rw [hpos, mul_one, list_prod_map_eq_of_single negative hn.1 _
      ((hn.2 ⟨a, hs⟩).mpr (Set.mem_univ _)) (fun i _ hi => hF i (fun h => hi (Subtype.ext h)))]
    exact ha

private theorem enumerates_map_subtype {J : Type u} {p : J → Prop} {l : List (Subtype p)}
    (hl : Enumerates l Set.univ) : Enumerates (l.map Subtype.val) {a | p a} := by
  refine ⟨hl.1.map Subtype.val_injective, fun i => ?_⟩
  rw [List.mem_map]
  exact ⟨fun ⟨j, _, h⟩ => h ▸ j.property,
    fun hi => ⟨⟨i, hi⟩, (hl.2 _).mpr (Set.mem_univ _), rfl⟩⟩

private def seriesUnit {σ R : Type*} [CommRing R] (x : MvPowerSeries σ R)
    (hx : x.constantCoeff = 0) : (MvPowerSeries σ R)ˣ :=
  (MvPowerSeries.isUnit_iff_constantCoeff.mpr (show IsUnit (1 + x).constantCoeff by
    rw [map_add, map_one, hx, add_zero]
    exact isUnit_one)).unit

private theorem seriesUnit_coe {σ R : Type*} [CommRing R] (x : MvPowerSeries σ R)
    (hx : x.constantCoeff = 0) : (↑(seriesUnit x hx) : MvPowerSeries σ R) = 1 + x :=
  IsUnit.unit_spec _

private theorem map_seriesUnit {σ τ R S : Type*} [CommRing R] [CommRing S]
    (f : MvPowerSeries σ R →+* MvPowerSeries τ S)
    {x : MvPowerSeries σ R} {y : MvPowerSeries τ S}
    (hx : x.constantCoeff = 0) (hy : y.constantCoeff = 0) (hxy : f x = y) :
    Units.map f.toMonoidHom (seriesUnit x hx) = seriesUnit y hy := by
  apply Units.ext
  change f (↑(seriesUnit x hx) : MvPowerSeries σ R) = _
  rw [seriesUnit_coe, seriesUnit_coe, map_add, map_one, hxy]

private theorem seriesUnit_zero {σ K : Type*} [CommRing K] :
    seriesUnit (0 : MvPowerSeries σ K) (map_zero _) = 1 := by
  apply Units.ext
  simp [seriesUnit_coe]

private theorem optionEquivLeft_eval₂_X_none {σ K : Type*} [CommRing K] (p : Polynomial K) :
    MvPowerSeries.optionEquivLeft σ K
        (Polynomial.eval₂ MvPowerSeries.C (MvPowerSeries.X none) p) =
      (((p.map MvPowerSeries.C) : Polynomial (MvPowerSeries σ K)) :
        PowerSeries (MvPowerSeries σ K)) := by
  have he : (MvPowerSeries.optionEquivLeft σ K).toRingHom.comp
      (Polynomial.eval₂RingHom MvPowerSeries.C (MvPowerSeries.X none)) =
      Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom MvPowerSeries.C) := by
    ext <;> simp [Polynomial.coeToPowerSeries.ringHom_apply]
  exact RingHom.congr_fun he p

private theorem optionEquivLeft_aeval_X_some {σ K : Type*} [CommRing K] (p : MvPolynomial σ K) :
    MvPowerSeries.optionEquivLeft σ K
        (MvPolynomial.aeval (fun a => MvPowerSeries.X (some a)) p) =
      PowerSeries.C (p : MvPowerSeries σ K) := by
  have he : (MvPowerSeries.optionEquivLeft σ K).toRingHom.comp
      (MvPolynomial.aeval (fun a => MvPowerSeries.X (some a))).toRingHom =
      PowerSeries.C.comp MvPolynomial.coeToMvPowerSeries.ringHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C]
      rw [PowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    · intro a
      simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]
  exact RingHom.congr_fun he p

set_option maxHeartbeats 1000000 in
/-- Apply the formal big-cell product to a single root factor times the
negative-root product on the highest vector. The resulting coefficients
preserve its integer coefficient lattice. -/
theorem lattice_stable_of_formalBigCell
    (V : RationalHighestWeight z e h lam) (collection : FormalBigCellProduct Q z)
    {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative : List (Negative D)) (positive : List (Positive D))
    (hn : Enumerates negative Set.univ) (hp : Enumerates positive Set.univ)
    (a : D.I) (m : ℕ) {v : V.space} (hv : v ∈ V.lattice negative) :
    (dividedPower (V.rootOperator a) m).mulVec v ∈ V.lattice negative := by
  classical
  let : Finite D.I := D.finiteRoots
  let K := RationalField.{u}
  let : CharZero K :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv.symm : ℚ ≃+* K).toRingHom)
      (ULift.ringEquiv.symm : ℚ ≃+* K).injective
  let τ := Option (Negative D)
  let σ := CellVariables D r
  let R := CellAlgebra D r
  let S := MvPowerSeries τ K
  let intMap := Int.castRingHom K
  obtain ⟨f, hf, _⟩ := collection r b (negative.map Subtype.val) (positive.map Subtype.val)
    (enumerates_map_subtype hn) (enumerates_map_subtype hp)
  let vars : σ → MvPowerSeries τ ℤ
    | (false, .inl j) => if j = a then MvPowerSeries.X none else 0
    | (true, .inl j) => if hj : ¬ D.base.IsPos j then MvPowerSeries.X (some ⟨j, hj⟩) else 0
    | (_, .inr _) => 0
  have hcenter (i : σ) : (vars i).constantCoeff = 0 := by
    obtain ⟨s, i⟩ := i
    cases s <;> cases i <;> simp [vars] <;> split <;> simp
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hcenter
  let ψ : MvPowerSeries σ K →ₐ[K] S := MvPowerSeries.substAlgHom (hsub.map intMap)
  let ψZ : MvPowerSeries σ ℤ →ₐ[ℤ] MvPowerSeries τ ℤ := MvPowerSeries.substAlgHom hsub
  let F (i : D.I ⊕ Fin r) := ψZ (f i).val
  have hF (i : D.I ⊕ Fin r) : (F i).constantCoeff = 0 := by
    change (MvPowerSeries.substAlgHom hsub (f i).val).constantCoeff = 0
    rw [MvPowerSeries.substAlgHom_apply]
    exact MvPowerSeries.constantCoeff_subst_eq_zero hsub hcenter (f i).property
  have hmap (i : D.I ⊕ Fin r) :
      ψ (MvPowerSeries.map intMap (f i).val) = MvPowerSeries.map intMap (F i) := by
    change MvPowerSeries.substAlgHom (hsub.map intMap) (MvPowerSeries.map intMap (f i).val) =
      MvPowerSeries.map intMap (MvPowerSeries.substAlgHom hsub (f i).val)
    rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply]
    exact (MvPowerSeries.map_subst hsub (h := intMap) (f i).val).symm
  have hX (i : σ) : ψ (MvPowerSeries.X i) = MvPowerSeries.map intMap (vars i) :=
    MvPowerSeries.substAlgHom_X (hsub.map intMap) i
  let tZ (i : Fin r) := seriesUnit (F (.inr i)) (hF _)
  let rz (i : D.I) := MvPowerSeries.map intMap (F (.inl i))
  let tz (i : Fin r) := Units.map (MvPowerSeries.map intMap).toMonoidHom (tZ i)
  let ρ : GroupPoints Q.pinned.pair.G.val R →*
      Matrix (Index.{u} V.dimension) (Index.{u} V.dimension) R :=
    (Units.coeHom _).comp (V.action.app R).hom
  let x₀ (side : Bool) (j : D.I) : R := MvPowerSeries.X (side, .inl j)
  let t₀ (side : Bool) (i : Fin r) : Rˣ :=
    onePlusSeries (MvPowerSeries.X (side, .inr i)) (MvPowerSeries.constantCoeff_X _)
  let xf (j : D.I) : R := MvPowerSeries.map intMap (f (.inl j)).val
  let tf (i : Fin r) : Rˣ := onePlusSeries (MvPowerSeries.map intMap (f (.inr i)).val)
    (by simp [(f (.inr i)).property])
  have hgen (side : Bool) :
      ρ (genericCellPoint Q z b (negative.map Subtype.val) (positive.map Subtype.val) side) =
        cellMatrix V b negative positive (x₀ side) (t₀ side) :=
    cellPoint_action_matrix V b negative positive R (x₀ side) (t₀ side)
  have hint :
      ρ (integralCellPoint Q z b (negative.map Subtype.val) (positive.map Subtype.val) f) =
        cellMatrix V b negative positive xf tf :=
    cellPoint_action_matrix V b negative positive R xf tf
  have hmat := congrArg ρ hf
  rw [map_mul, hgen false, hgen true, hint] at hmat
  have hmat' := congrArg ψ.toRingHom.mapMatrix hmat
  simp only [map_mul, map_cellMatrix] at hmat'
  have hleft (j : D.I) : ψ (x₀ false j) = if j = a then MvPowerSeries.X none else 0 := by
    rw [hX (false, .inl j)]
    by_cases hj : j = a <;> simp [vars, hj]
  have hright (j : Negative D) : ψ (x₀ true j) = MvPowerSeries.X (some j) := by
    rw [hX (true, .inl j.val)]
    simp only [vars, dite_eq_left j.property, Subtype.eta, MvPowerSeries.map_X]
  have ht₀ (side : Bool) (i : Fin r) : Units.map ψ.toMonoidHom (t₀ side i) = 1 := by
    change Units.map ψ.toMonoidHom
      (seriesUnit (MvPowerSeries.X (side, Sum.inr i)) (MvPowerSeries.constantCoeff_X _)) = 1
    have hzero : ψ.toRingHom (MvPowerSeries.X (side, Sum.inr i)) = 0 := by
      change ψ (MvPowerSeries.X (side, Sum.inr i)) = 0
      rw [hX]
      cases side <;> simp [vars]
    rw [map_seriesUnit ψ.toRingHom _ (map_zero _) hzero, seriesUnit_zero]
  have htf (i : Fin r) : Units.map ψ.toMonoidHom (tf i) = tz i := by
    have htf0 : (MvPowerSeries.map intMap (f (.inr i)).val).constantCoeff = 0 := by
      simp [(f (.inr i)).property]
    have hh : Units.map ψ.toMonoidHom (tf i) = seriesUnit
        (MvPowerSeries.map intMap (F (.inr i))) (by simp [hF]) :=
      map_seriesUnit ψ.toRingHom htf0 _ (hmap _)
    rw [hh]
    exact (map_seriesUnit (MvPowerSeries.map intMap) _ _ rfl).symm
  simp only [funext hleft, funext (ht₀ false), funext (ht₀ true), funext htf,
    show (fun j => ψ (xf j)) = rz from funext (fun j => hmap (.inl j))] at hmat'
  rw [cellMatrix_single_root V b negative positive hn hp] at hmat'
  have hvect := congrArg (fun M : Matrix (Index.{u} V.dimension) _ S =>
    M.mulVec (algebraMap K S ∘ V.highest)) hmat'
  rw [← Matrix.mulVec_mulVec, cellMatrix_highest V b negative positive,
    cellMatrix_highest V b negative positive] at hvect
  let cell := negativeCellPolynomial V negative
  let c : MvPowerSeries τ ℤ :=
    ((List.finRange r).map (fun i => (↑(tZ i ^ B lam (b i)) : MvPowerSeries τ ℤ))).prod
  have hc : ((List.finRange r).map (fun i => (↑(tz i ^ B lam (b i)) : S))).prod =
      MvPowerSeries.map intMap c := by
    unfold c
    simp only [map_list_prod, List.map_map, Function.comp_def, tz, ← map_zpow]
    rfl
  have hones : ((List.finRange r).map (fun _ => (1 : S))).prod = 1 := by
    apply List.prod_eq_one
    simp
  simp only [one_zpow, Units.val_one, hones, one_smul, hright, hc, rz] at hvect
  have hC : algebraMap K S = MvPowerSeries.C := by
    ext x : 1
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hsorted (j : Index.{u} V.dimension) :
      (Matrix.of (fun i j => (((
        ((exponentialPolynomial (V.rootOperator a) V.nilpotenceBound) i j).map MvPowerSeries.C) :
          Polynomial (MvPowerSeries (Negative D) K)) : PowerSeries (MvPowerSeries (Negative D) K)))).mulVec
        (fun j => PowerSeries.C (cell j : MvPowerSeries (Negative D) K)) j =
      MvPowerSeries.optionEquivLeft (Negative D) K
        (MvPowerSeries.map intMap c *
          MvPolynomial.eval₂Hom MvPowerSeries.C (fun i => rz i.val) (cell j)) := by
    let E := (MvPowerSeries.optionEquivLeft (Negative D) K).toRingHom
    have hh := congrArg (fun x : Index.{u} V.dimension → S => E ∘ x) hvect
    rw [mapMatrix_mulVec E] at hh
    have hE : E.mapMatrix (rootMatrixAt V a (MvPowerSeries.X none : S)) =
        Matrix.of (fun i j => (((
          ((exponentialPolynomial (V.rootOperator a) V.nilpotenceBound) i j).map MvPowerSeries.C) :
            Polynomial (MvPowerSeries (Negative D) K)) : PowerSeries (MvPowerSeries (Negative D) K))) := by
      apply Matrix.ext
      intro i j
      change (MvPowerSeries.optionEquivLeft (Negative D) K)
        (((exponentialPolynomial (V.rootOperator a) V.nilpotenceBound) i j).eval₂
          (algebraMap K S) (MvPowerSeries.X none)) = _
      rw [hC]
      exact optionEquivLeft_eval₂_X_none _
    rw [hE, show (E ∘ fun j => MvPolynomial.aeval
        (fun i : Negative D => MvPowerSeries.X (some i)) (cell j)) =
        (fun j => PowerSeries.C (cell j : MvPowerSeries (Negative D) K))
      from funext (fun _ => optionEquivLeft_aeval_X_some _)] at hh
    have hj := congrFun hh j
    change _ = (MvPowerSeries.optionEquivLeft (Negative D) K)
      (MvPowerSeries.map intMap c * MvPolynomial.aeval (fun i : Negative D => rz i.val) (cell j)) at hj
    rw [MvPolynomial.aeval_eq_eval₂Hom, hC] at hj
    exact hj
  have hspan : Submodule.span ℤ (Set.range fun d j => (cell j).coeff d) = V.lattice negative := by
    unfold RationalHighestWeight.lattice
    rw [show (fun d j => (cell j).coeff d) = V.negativeCoefficient negative from
      funext (negativeCellPolynomial_coeff V negative hn)]
  have hInt : intMap = algebraMap ℤ K := Subsingleton.elim _ _
  have hstable := coeff_mulVec_mem_span_of_collection
    (exponentialPolynomial (V.rootOperator a) V.nilpotenceBound) cell
    (fun i => F (.inl i.val)) c (by simpa only [rz, hInt] using hsorted) m (hspan.symm ▸ hv)
  rw [hspan] at hstable
  have hcoeff : Matrix.of (fun i j =>
      ((exponentialPolynomial (V.rootOperator a) V.nilpotenceBound) i j).coeff m) =
        dividedPower (V.rootOperator a) m :=
    Matrix.ext (fun i j => exponentialPolynomial_coeff (V.rootOperator a) (V.nilpotent a) m i j)
  exact hcoeff ▸ hstable

/-- The integer coefficient span is the required lattice on every supplied
rational highest-weight action on the marked model. -/
theorem isIntegralLattice_of_formalBigCell
    (V : RationalHighestWeight z e h lam) (collection : FormalBigCellProduct Q z)
    (basis : Basis (D.base.support ⊕ D.I) RationalField.{u}
      (Lie RationalField.{u} Q.pinned.pair.G.val))
    (basis_h : ∀ i, basis (.inl i) = h i) (basis_e : ∀ a, basis (.inr a) = e a)
    (negative : List (Negative D)) (positive : List (Positive D))
    (hn : Enumerates negative Set.univ) (hp : Enumerates positive Set.univ) :
    V.IsIntegralLattice negative := by
  let : Module.Free ℤ D.Y := D.freeY
  let : Module.Finite ℤ D.Y := D.finiteY
  obtain ⟨height, d, hd, hheight⟩ := exists_integralHeight D
  have hneg (a : Negative D) : height (D.datum.root a.val) < 0 := by
    rw [hheight]
    have h : D.base.height a.val < 0 :=
      lt_of_le_of_ne (not_lt.mp a.property) (D.base.height_ne_zero a.val)
    exact mul_neg_of_pos_of_neg hd h
  obtain ⟨hdecomp, hline⟩ := lattice_weight_facts V
    (rootOperator_weight_shift V) height hneg negative hn
  refine ⟨lattice_finite V negative hn, lattice_free V negative hn, ?_,
    hdecomp, hline, ?_⟩
  · apply top_unique
    rw [← negativeCoefficient_span V basis basis_h basis_e negative positive hn hp]
    apply Submodule.span_mono
    exact Submodule.subset_span
  · intro a m v hv
    exact lattice_stable_of_formalBigCell V collection
      (Module.finBasis ℤ D.Y) negative positive hn hp a m hv

end

end

section

open Specs.IntegralLattices
noncomputable section

private theorem unitriangular_det {n : ℕ} {R : Type*} [CommRing R] {upper : Bool}
    (P : Matrix (Index.{u} n) (Index.{u} n) R)
    (hP : ∀ i j, (if upper then ¬ i < j else ¬ j < i) → P i j = (1 : Matrix _ _ R) i j) :
    P.det = 1 := by
  have hd (i : Index.{u} n) : P i i = 1 := by
    rw [hP i i (by cases upper <;> exact lt_irrefl i), Matrix.one_apply_eq]
  suffices he : P.det = ∏ i, P i i by simp [he, hd]
  cases upper with
  | true =>
    apply Matrix.det_of_isUpperTriangular
    intro i j hji
    change j < i at hji
    rw [hP i j (not_lt_of_gt hji), Matrix.one_apply_ne (ne_of_gt hji)]
  | false =>
    apply Matrix.det_of_isLowerTriangular P
    intro i j hij
    change i < j at hij
    rw [hP i j (not_lt_of_gt hij), Matrix.one_apply_ne (ne_of_lt hij)]

set_option maxHeartbeats 650000 in
/-- If an ordered unitriangular product has integral inverse coordinates,
its rational subgroup law descends to the closed integral image. -/
theorem closedRootImage_of_rational {K σ : Type u} [Field K] [CharZero K]
    {n : ℕ} (upper : Bool) (P : Matrix (Index.{u} n) (Index.{u} n) (MvPolynomial σ ℤ))
    (htri : ∀ i j, (if upper then ¬ i < j else ¬ j < i) → P i j = (1 : Matrix _ _ _) i j)
    (hcoords : ∀ a : σ, ∃ p : MvPolynomial (triangularEntries n upper) ℤ,
      MvPolynomial.aeval (fun ij => P ij.val.1 ij.val.2) p = MvPolynomial.X a)
    (hRat : ∀ (R : Type u) [CommRing R] [Algebra K R],
      ∃ f : (σ → R) → Matrix.GeneralLinearGroup (Index.{u} n) R,
        (∀ x, (f x).val = (MvPolynomial.eval₂Hom (Int.castRingHom R) x).mapMatrix P) ∧
        ∃ H : Subgroup (Matrix.GeneralLinearGroup (Index.{u} n) R), Set.range f = H) :
    ClosedRootImage upper P := by
  classical
  let U : Matrix.GeneralLinearGroup (Index.{u} n) (MvPolynomial σ ℤ) :=
    ((Matrix.isUnit_iff_isUnit_det P).mpr (unitriangular_det P htri ▸ isUnit_one)).unit
  have hU : U.val = P := IsUnit.unit_spec _
  let family (R : Type u) [CommRing R] (x : σ → R) :=
    Matrix.GeneralLinearGroup.map (MvPolynomial.eval₂Hom (Int.castRingHom R) x) U
  have hval (R : Type u) [CommRing R] (x : σ → R) :
      (family R x).val = (MvPolynomial.eval₂Hom (Int.castRingHom R) x).mapMatrix P := by
    change (MvPolynomial.eval₂Hom (Int.castRingHom R) x).mapMatrix U.val = _
    rw [hU]
  have hnat {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : σ → R) :
      Matrix.GeneralLinearGroup.map f (family R x) = family S (f ∘ x) := by
    apply Units.ext
    change f.mapMatrix (family R x).val = _
    rw [hval, hval]
    have hm : f.comp (MvPolynomial.eval₂Hom (Int.castRingHom R) x) =
        MvPolynomial.eval₂Hom (Int.castRingHom S) (f ∘ x) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp
      · intro a
        simp
    apply Matrix.ext
    intro i j
    exact RingHom.congr_fun hm (P i j)
  let τ := Index.{u} n × Index.{u} n
  let entry (i : τ) := P i.1 i.2
  have hcoord (a : σ) : ∃ q : MvPolynomial τ ℤ, MvPolynomial.aeval entry q = MvPolynomial.X a := by
    obtain ⟨q, hq⟩ := hcoords a
    let val : triangularEntries n upper → τ := fun i => i.val
    refine ⟨MvPolynomial.rename val q, ?_⟩
    rw [MvPolynomial.aeval_rename]
    exact hq
  choose inverse hinverse using hcoord
  let S := MvPolynomial (Bool × σ) ℤ
  let T := MvPolynomial (Bool × σ) K
  let I : S →+* T := MvPolynomial.map (Int.castRingHom K)
  have hI : Function.Injective I := MvPolynomial.map_injective _ Int.cast_injective
  obtain ⟨g, hg, H, hH⟩ := hRat T
  have hg' (x : σ → T) : g x = family T x := Units.ext ((hg x).trans (hval T x).symm)
  have hin (x : σ → S) : Matrix.GeneralLinearGroup.map I (family S x) ∈ H := by
    rw [hnat, ← hg']
    change g (I ∘ x) ∈ (H : Set _)
    rw [← hH]
    exact Set.mem_range_self _
  have hdesc (A : Matrix.GeneralLinearGroup (Index.{u} n) S)
      (hA : Matrix.GeneralLinearGroup.map I A ∈ H) : A ∈ Set.range (family S) := by
    change Matrix.GeneralLinearGroup.map I A ∈ (H : Set _) at hA
    rw [← hH] at hA
    obtain ⟨y, hy⟩ := hA
    obtain ⟨x, hx⟩ := polynomial_image_descends entry inverse hinverse I hI
      (fun i => A.val i.1 i.2) ⟨y, fun i => by
        have hh := congrArg (fun M : Matrix.GeneralLinearGroup _ T => M.val i.1 i.2) hy
        rw [hg] at hh
        exact hh⟩
    refine ⟨x, Units.ext (Matrix.ext (fun i j => ?_))⟩
    rw [hval]
    exact hx (i, j)
  let x₀ (a : σ) : S := MvPolynomial.X (false, a)
  let x₁ (a : σ) : S := MvPolynomial.X (true, a)
  obtain ⟨zmul, hmul⟩ := hdesc (family S x₀ * family S x₁)
    (by rw [map_mul]; exact H.mul_mem (hin x₀) (hin x₁))
  obtain ⟨zinv, hinv⟩ := hdesc (family S x₀)⁻¹
    (by rw [map_inv]; exact H.inv_mem (hin x₀))
  refine ⟨htri, hcoords, fun R _ => ⟨family R, hval R, ?_⟩⟩
  have hmulR (x y : σ → R) : family R x * family R y ∈ Set.range (family R) := by
    let ev : S →+* R :=
      MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => if i.1 then y i.2 else x i.2)
    have h₀ : ev ∘ x₀ = x := funext (fun j => MvPolynomial.eval₂Hom_X' _ _ (false, j))
    have h₁ : ev ∘ x₁ = y := funext (fun j => MvPolynomial.eval₂Hom_X' _ _ (true, j))
    refine ⟨ev ∘ zmul, ?_⟩
    rw [← hnat, hmul, map_mul, hnat, hnat, h₀, h₁]
  have hinvR (x : σ → R) : (family R x)⁻¹ ∈ Set.range (family R) := by
    let ev : S →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => x i.2)
    have h₀ : ev ∘ x₀ = x := funext (fun j => MvPolynomial.eval₂Hom_X' _ _ (false, j))
    refine ⟨ev ∘ zinv, ?_⟩
    rw [← hnat, hinv, map_inv, hnat, h₀]
  have hOne : (1 : Matrix.GeneralLinearGroup (Index.{u} n) R) ∈ Set.range (family R) := by
    obtain ⟨y, hy⟩ := hinvR 0
    simpa only [hy, mul_inv_cancel] using hmulR 0 y
  refine ⟨{ carrier := Set.range (family R)
            one_mem' := hOne
            mul_mem' := ?_
            inv_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact hmulR x y
  · rintro _ ⟨x, rfl⟩
    exact hinvR x

end

end

section ChevalleyGenerators

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralRootRelations (IsRootString)
open Module
noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}

/-- The simple Chevalley triples generate the Lie algebra of the marked
rational group. This uses the Chevalley bracket coefficient on each
nontrivial root sum. -/
theorem lieSpan_simpleChevalley_eq_top (s : IdentityLieStructure Q.pinned.pair.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (B : Basis (D.base.support ⊕ D.I) RationalField.{u}
      (Lie RationalField.{u} Q.pinned.pair.G.val))
    (_Bh : ∀ i, B (.inl i) = h i) (_Be : ∀ a, B (.inr a) = e a)
    (_bracket : ∀ i j k, D.datum.root i + D.datum.root j = D.datum.root k →
      ∃ (p q : ℕ) (n : ℤ), IsRootString i j p q ∧
        (n = (p : ℤ) + 1 ∨ n = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = n • e k),
    LieSubalgebra.lieSpan RationalField.{u} _
      (Set.range (fun i : D.base.support => h i) ∪
       Set.range (fun i : D.base.support => e i) ∪
       Set.range (fun i : D.base.support => e (D.datum.reflectionPerm i i))) = ⊤ := by
  classical
  let := s.lieRing
  let := s.lieAlgebra
  intro B Bh Be bracket
  let : Finite D.I := D.finiteRoots
  let := D.datum.indexNeg
  let K := RationalField.{u}
  let : SMul K (Lie K Q.pinned.pair.G.val) :=
    s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  let S := LieSubalgebra.lieSpan K _
      (Set.range (fun i : D.base.support => h i) ∪
       Set.range (fun i : D.base.support => e i) ∪
       Set.range (fun i : D.base.support => e (D.datum.reflectionPerm i i)))
  have hs (i : D.I) (hi : i ∈ D.base.support) :
      h i ∈ S ∧ e i ∈ S ∧ e (-i) ∈ S :=
    ⟨LieSubalgebra.subset_lieSpan (Or.inl (Or.inl ⟨⟨i, hi⟩, rfl⟩)),
      LieSubalgebra.subset_lieSpan (Or.inl (Or.inr ⟨⟨i, hi⟩, rfl⟩)),
      LieSubalgebra.subset_lieSpan (Or.inr ⟨⟨i, hi⟩, rfl⟩)⟩
  have hadd (i j k : D.I) (hijk : D.datum.root k = D.datum.root i + D.datum.root j)
      (hi : e i ∈ S) (hj : e j ∈ S) : e k ∈ S := by
    obtain ⟨p, _, n, _, hn, he⟩ := bracket i j k hijk.symm
    have hn' : n ≠ 0 := by rcases hn with h | h <;> omega
    have hK : (n : K) ≠ 0 := by
      intro hzero
      have hh := congrArg (ULift.ringEquiv : K ≃+* ℚ) hzero
      rw [map_intCast, map_zero] at hh
      exact hn' (Int.cast_eq_zero.mp hh)
    have hadditive := congrArg
      (fun law : AddGroup (PointKernel Q.pinned.pair.G.val) => law.zsmul n (e k)) s.group_law
    have hscale : (n : K) • e k = ⁅e i, e j⁆ :=
      (Int.cast_smul_eq_zsmul K n (e k)).trans (hadditive.trans he.symm)
    have hh : (n : K) • e k ∈ S := hscale.symm ▸ S.lie_mem hi hj
    have hk := S.smul_mem (n : K)⁻¹ hh
    rwa [smul_smul, inv_mul_cancel₀ hK, one_smul] at hk
  have hneg (j : D.I) : D.datum.root (-j) = -D.datum.root j := by
    change D.datum.root (D.datum.reflectionPerm j j) = _
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self]
  have hpos (i : D.I) (hi : D.base.IsPos i) : e i ∈ S ∧ e (-i) ∈ S := by
    apply RootPairing.Base.IsPos.induction_on_add hi
    · exact fun j hj => (hs j hj).2
    · intro j l k hh hj hl
      refine ⟨hadd j l k hh hj.1 (hs l hl).2.1, hadd (-j) (-l) (-k) ?_ hj.2 (hs l hl).2.2⟩
      simpa only [hneg, neg_add_rev, add_comm] using congrArg (fun x : D.X => -x) hh
  have hroot (i : D.I) : e i ∈ S := by
    rcases RootPairing.Base.IsPos.or_neg D.base i with hi | hi
    · exact (hpos i hi).1
    · simpa only [neg_neg] using (hpos (-i) hi).2
  have hb (j : D.base.support ⊕ D.I) : B j ∈ S := by
    cases j with
    | inl j => rw [Bh]; exact (hs j j.property).1
    | inr j => rw [Be]; exact hroot j
  change S = ⊤
  apply (LieSubalgebra.toSubmodule_eq_top S).mp
  apply top_unique
  rw [← B.span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hb j)

end

end ChevalleyGenerators

section WeightBases

open Specs.IntegralLattices (Index)
open Module
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 900000 in
/-- A finite integer lattice spanning a rational coordinate space admits
a homogeneous basis in any prescribed decreasing order of weight height
when its weight projections preserve the lattice. -/
theorem exists_orderedLatticeBasis
    {K J X : Type u} [Field K] [IsFractionRing ℤ K] [Fintype J] [DecidableEq X]
    (L : Submodule ℤ (J → K)) [Module.Finite ℤ L]
    (hL : Submodule.span K (L : Set (J → K)) = ⊤)
    (grade : J → X) (height : X → ℤ)
    (proj_mem : ∀ (q : X) (x : J → K), x ∈ L →
      (fun j => if grade j = q then x j else 0) ∈ L) :
    ∃ (n : ℕ) (b : Basis (Index.{u} n) K (J → K)) (w : Index.{u} n → X),
      Submodule.span ℤ (Set.range b) = L ∧
      (∀ i j, grade j ≠ w i → b i j = 0) ∧ Antitone (height ∘ w) := by
  classical
  let W := J → K
  let weight := Set.range grade
  let : Fintype weight := (Set.finite_range grade).fintype
  let proj (q : weight) : W →ₗ[ℤ] W :=
    { toFun x j := if grade j = q.val then x j else 0
      map_add' x y := by
        funext j
        change (if grade j = q.val then x j + y j else 0) =
          (if grade j = q.val then x j else 0) + (if grade j = q.val then y j else 0)
        by_cases hj : grade j = q.val <;> simp [hj]
      map_smul' r x := by
        funext j
        change (if grade j = q.val then r • x j else 0) =
          r • (if grade j = q.val then x j else 0)
        by_cases hj : grade j = q.val <;> simp [hj] }
  let M (q : weight) : Submodule ℤ L := (LinearMap.ker (proj q - LinearMap.id)).comap L.subtype
  have hM (q : weight) (x : L) : x ∈ M q ↔ proj q (x : W) = x := by
    change proj q (x : W) - x.val = 0 ↔ _
    exact sub_eq_zero
  have hdisj : iSupIndep M := iSupIndep_def.mpr fun q => by
    have hker : (⨆ (t) (_ : t ≠ q), M t) ≤ LinearMap.ker ((proj q).comp L.subtype) := by
      refine iSup_le fun t => iSup_le fun ht x hx => ?_
      have h := (hM t x).mp hx
      change proj q (x : W) = 0
      funext j
      change (if grade j = q.val then x.val j else 0) = (0 : K)
      by_cases hj : grade j = q.val
      · have hjt : grade j ≠ t.val := fun he => ht (Subtype.ext (he.symm.trans hj))
        have h0 := congrFun h j
        simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hjt] at h0
        simpa only [ite_eq_left hj] using h0.symm
      · simp [hj]
    rw [Submodule.disjoint_def]
    intro x hq hx
    exact Subtype.ext (((hM q x).mp hq).symm.trans (hker hx))
  have htop : (⨆ q, M q) = ⊤ := by
    apply top_unique
    intro x _
    let v (q : weight) : L := ⟨proj q (x : W), proj_mem q.val x x.property⟩
    have hsum : ∑ q : weight, v q = x := by
      apply L.subtype_injective
      rw [map_sum]
      funext j
      change (∑ q : weight, (v q : W)) j = x.val j
      simp only [Finset.sum_apply]
      let qj : weight := ⟨grade j, Set.mem_range_self j⟩
      rw [Finset.sum_eq_single_of_mem qj (Finset.mem_univ qj)]
      · simp [v, proj, qj]
      · intro q _ hq
        have hj : grade j ≠ q.val := fun he => hq (Subtype.ext he.symm)
        simp [v, proj, hj]
    rw [← hsum]
    apply Submodule.sum_mem
    intro q _
    refine (le_iSup M q) ((hM q (v q)).mpr ?_)
    funext j
    by_cases hj : grade j = q.val <;> simp [v, proj, hj]
  have hInt := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hdisj htop
  let pieceBasis (q : weight) := Module.finBasis ℤ (M q)
  let bZ := hInt.collectedBasis pieceBasis
  let I := Σ q : weight, Fin (Module.finrank ℤ (M q))
  let v : I → W := L.subtype ∘ bZ
  have hZ : Submodule.span ℤ (Set.range v) = L := by
    change Submodule.span ℤ (Set.range (L.subtype ∘ bZ)) = L
    rw [Set.range_comp, ← Submodule.map_span, bZ.span_eq, Submodule.map_subtype_top]
  have hlinZ : LinearIndependent ℤ v :=
    bZ.linearIndependent.map' L.subtype L.ker_subtype
  have hlin : LinearIndependent K v :=
    hlinZ.localization K (nonZeroDivisors ℤ)
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    apply top_unique
    rw [← hL]
    apply Submodule.span_le.mpr
    have hh : L ≤ (Submodule.span K (Set.range v)).restrictScalars ℤ := by
      rw [← hZ]
      apply Submodule.span_le.mpr
      exact Submodule.subset_span
    exact hh
  let bK := Basis.mk hlin hspan.ge
  let n := Fintype.card I
  let eqFin : I ≃ Fin n := Fintype.equivFin I
  let score (i : Fin n) : ℤᵒᵈ := height (eqFin.symm i).1.val
  let order : Index.{u} n ≃ I := Equiv.ulift.trans ((Tuple.sort score).trans eqFin.symm)
  let b := bK.reindex order.symm
  let w (i : Index.{u} n) := (order i).1.val
  have hb (i : Index.{u} n) : b i = v (order i) := by
    exact (Basis.reindex_apply _ _ _).trans (Basis.mk_apply _ _ _)
  refine ⟨n, b, w, ?_, ?_, ?_⟩
  · rw [show (⇑b : Index.{u} n → W) = v ∘ order from funext hb, Set.range_comp,
      order.surjective.range_eq, Set.image_univ, hZ]
  · intro i j hj
    rw [hb]
    have hmem : bZ (order i) ∈ M (order i).1 := hInt.collectedBasis_mem pieceBasis _
    have hfix := congrFun ((hM (order i).1 _).mp hmem) j
    have hj' : grade j ≠ (order i).1.val := hj
    simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hj'] at hfix
    exact hfix.symm
  · intro i j hij
    exact (Tuple.monotone_sort score) (show i.down ≤ j.down from hij)

end

end WeightBases

section FundamentalBasis

open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralLattices
open Module
open scoped BigOperators
noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}

set_option maxHeartbeats 750000 in
/-- The sum of the fundamental lattices has an integral basis that is a
rational weight basis in decreasing order of height. -/
theorem exists_orderedFundamentalBasis
    (ω : Basis D.base.support ℤ D.X)
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    (negative : List (Negative D)) (hV : ∀ i, (V i).IsIntegralLattice negative)
    (height : D.X →ₗ[ℤ] ℤ) :
    ∃ (n : ℕ)
      (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
      (w : Index.{u} n → D.X),
      Submodule.span ℤ (Set.range b) = Submodule.pi Set.univ (fun i => (V i).lattice negative) ∧
      (∀ j i, b j i ∈ (V i).weightSpace (w j)) ∧ Antitone (height ∘ w) := by
  classical
  let K := RationalField.{u}
  let τ := D.base.support
  let W := (i : τ) → (V i).space
  let J := Σ i : τ, Index.{u} (V i).dimension
  let L (i : τ) := (V i).lattice negative
  let P : Submodule ℤ W := Submodule.pi Set.univ L
  let F : W ≃ₗ[K] (J → K) := (LinearEquiv.piCurry K (fun _ _ => K)).symm
  let FZ := F.restrictScalars ℤ
  let P' := P.map FZ.toLinearMap
  let : ∀ i, Module.Finite ℤ (L i) := fun i => (hV i).1
  let incl : P →ₗ[ℤ] ((i : τ) → L i) :=
    { toFun x i := ⟨x.val i, Submodule.mem_pi.mp x.property i (Set.mem_univ i)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have incl_injective : Function.Injective incl := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  let : Module.Finite ℤ P := Module.Finite.of_injective incl incl_injective
  let : Module.Finite ℤ P' := Module.Finite.map _ _
  have hP : Submodule.span K (P : Set W) = ⊤ := by
    let Z := Submodule.span K (P : Set W)
    have hsingle (i : τ) (x : (V i).space) : Pi.single i x ∈ Z := by
      let s := LinearMap.single K (fun j : τ => (V j).space) i
      have hs : (⊤ : Submodule K (V i).space) ≤ Z.comap s := by
        rw [← (hV i).2.2.1]
        apply Submodule.span_le.mpr
        intro y hy
        change s y ∈ Z
        apply Submodule.subset_span
        rw [SetLike.mem_coe, Submodule.mem_pi]
        intro j _
        by_cases hj : j = i
        · subst j
          simpa [s] using hy
        · rw [LinearMap.single_apply, Pi.single_eq_of_ne hj]
          exact Submodule.zero_mem _
      exact hs Submodule.mem_top
    apply top_unique
    intro x _
    change x ∈ Z
    rw [← LinearMap.sum_single_apply (φ := fun j : τ => (V j).space) x]
    exact Submodule.sum_mem _ (fun i _ => hsingle i (x i))
  have hP' : Submodule.span K (P' : Set (J → K)) = ⊤ := by
    have hmap : Submodule.span K (P' : Set (J → K)) =
        (Submodule.span K (P : Set W)).map F.toLinearMap := by
      rw [Submodule.map_span]
      rfl
    rw [hmap, hP, Submodule.map_top, LinearMap.range_eq_top.mpr F.surjective]
  let grade (j : J) := (V j.1).weight j.2
  have hprojection (i : τ) (μ : D.X) (x : (V i).space) (hx : x ∈ L i) :
      (fun j => if (V i).weight j = μ then x j else 0) ∈ L i := by
    let p : (V i).space →ₗ[ℤ] (V i).space :=
      { toFun x j := if (V i).weight j = μ then x j else 0
        map_add' x y := by
          funext j
          by_cases h : (V i).weight j = μ <;> simp [h, Pi.add_apply]
        map_smul' r x := by
          funext j
          by_cases h : (V i).weight j = μ <;> simp [h, Pi.smul_apply] }
    have hpres : L i ≤ (L i).comap p := by
      calc
        L i = ⨆ ν, L i ⊓ ((V i).weightSpace ν).restrictScalars ℤ := (hV i).2.2.2.1.symm
        _ ≤ (L i).comap p := by
          apply iSup_le
          intro ν y hy
          change p y ∈ L i
          by_cases hν : ν = μ
          · have he : p y = y := by
              funext j
              by_cases hj : (V i).weight j = μ
              · simp [p, hj]
              · have hz : y j = 0 := hy.2 j (fun he => hj (he.trans hν))
                simp [p, hj, hz]
            rw [he]
            exact hy.1
          · have he : p y = 0 := by
              funext j
              by_cases hj : (V i).weight j = μ
              · have hz : y j = 0 := hy.2 j (fun he => hν (he.symm.trans hj))
                simp [p, hj, hz]
              · simp [p, hj]
            rw [he]
            exact Submodule.zero_mem _
    exact hpres hx
  have hproj (μ : D.X) (x : J → K) (hx : x ∈ P') :
      (fun j => if grade j = μ then x j else 0) ∈ P' := by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    have h : (fun i (j : Index.{u} (V i).dimension) => if (V i).weight j = μ then y i j else 0) ∈ P := by
      rw [Submodule.mem_pi]
      intro i _
      exact hprojection i μ (y i) (Submodule.mem_pi.mp hy i (Set.mem_univ i))
    exact Submodule.mem_map.mpr ⟨_, h, rfl⟩
  let E : ℚ ≃ₐ[ℤ] K :=
    { (ULift.ringEquiv.symm : ℚ ≃+* K) with
      commutes' n := by
        change (ULift.ringEquiv.symm : ℚ ≃+* K) (n : ℚ) = (n : K)
        exact map_intCast (ULift.ringEquiv.symm : ℚ ≃+* K) n }
  let : IsFractionRing ℤ K := IsFractionRing.of_algEquiv E
  let : Fintype J := inferInstanceAs (Fintype (Σ i : τ, Index.{u} (V i).dimension))
  obtain ⟨n, b, w, hb, hw, hs⟩ := exists_orderedLatticeBasis P' hP' grade height hproj
  refine ⟨n, b.map F.symm, w, ?_, ?_, hs⟩
  · have hRange : Set.range (b.map F.symm) = FZ.symm '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    change Submodule.span ℤ (Set.range (b.map F.symm)) = P
    rw [hRange]
    change Submodule.span ℤ (FZ.symm.toLinearMap '' Set.range b) = P
    rw [← Submodule.map_span, hb]
    change (P.map FZ.toLinearMap).map FZ.symm.toLinearMap = P
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
      simpa using hv
    · intro x hx
      exact Submodule.mem_map.mpr
        ⟨FZ x, Submodule.mem_map.mpr ⟨x, hx, rfl⟩, FZ.symm_apply_apply x⟩
  · intro j i k hk
    exact hw j ⟨i, k⟩ hk

end

end FundamentalBasis

section IntegralMatrices

open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralLattices
open Module
open scoped BigOperators
noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}

/-- In any rational basis spanning the sum of the integer lattices over ℤ,
the divided root powers are the coefficients of integer polynomial matrices. -/
theorem exists_integralRootPolynomials
    (ω : Basis D.base.support ℤ D.X)
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    (negative : List (Negative D)) (hV : ∀ i, (V i).IsIntegralLattice negative)
    {n : ℕ}
    (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (hb : Submodule.span ℤ (Set.range b) =
      Submodule.pi Set.univ (fun i => (V i).lattice negative)) :
    ∃ p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ),
      ∀ (a : D.I) (m : ℕ) (j : Index.{u} n) (i : D.base.support),
        ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
          (dividedPower ((V i).rootOperator a) m).mulVec (b j i) := by
  classical
  let N := Finset.univ.sup (fun i : D.base.support => (V i).nilpotenceBound)
  let F (a : D.I) (m : ℕ) (j : Index.{u} n) (i : D.base.support) : (V i).space :=
    (dividedPower ((V i).rootOperator a) m).mulVec (b j i)
  have hmem (j : Index.{u} n) (i : D.base.support) :
      b j i ∈ (V i).lattice negative := by
    have hj : b j ∈ Submodule.span ℤ (Set.range b) := Submodule.subset_span (Set.mem_range_self j)
    rw [hb] at hj
    exact Submodule.mem_pi.mp hj i (Set.mem_univ i)
  have hsum (a : D.I) (m : ℕ) (j : Index.{u} n) :
      ∃ c : Index.{u} n → ℤ, ∑ l, c l • b l = F a m j := by
    apply (Submodule.mem_span_range_iff_exists_fun ℤ).mp
    rw [hb, Submodule.mem_pi]
    intro i _
    exact (hV i).2.2.2.2.2 a m (b j i) (hmem j i)
  choose c hc using hsum
  let p (a : D.I) := Matrix.of fun l j : Index.{u} n =>
    ∑ m ∈ Finset.range N, Polynomial.monomial m (c a m j l)
  refine ⟨p, fun a m j i => ?_⟩
  have hcoeff (l : Index.{u} n) :
      (p a l j).coeff m = if m < N then c a m j l else 0 := by
    simp [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_range]
  simp only [hcoeff]
  by_cases hm : m < N
  · simpa only [ite_eq_left hm, Finset.sum_apply, Pi.smul_apply, Int.cast_smul_eq_zsmul, F] using
      congrFun (hc a m j) i
  · have hN : (V i).nilpotenceBound ≤ m :=
      (Finset.le_sup (f := fun i : D.base.support => (V i).nilpotenceBound)
        (Finset.mem_univ i)).trans (Nat.le_of_not_gt hm)
    have hzero : ((V i).rootOperator a) ^ m = 0 :=
      pow_eq_zero_of_le hN ((V i).nilpotent a)
    rw [dividedPower, hzero]
    simp [hm]

end

end IntegralMatrices

section TorusWeights

open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralLattices
open Module
noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}

/-- The weights of the homogeneous basis span the entire character lattice. -/
theorem fundamentalWeights_span_of_weightBasis
    (ω : Basis D.base.support ℤ D.X)
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ}
    (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (w : Index.{u} n → D.X) (hb : ∀ j i, b j i ∈ (V i).weightSpace (w j)) :
    Submodule.span ℤ (Set.range w) = ⊤ := by
  classical
  apply top_unique
  rw [← ω.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  by_contra hi
  obtain ⟨k, hk⟩ : ∃ k, (V i).highest k ≠ 0 := by
    by_contra! hm
    exact (V i).highest_ne_zero (funext hm)
  have hw : (V i).weight k = ω i := by
    by_contra h
    exact hk ((V i).highest_support k h)
  let K := RationalField.{u}
  let f : ((i : D.base.support) → (V i).space) →ₗ[K] K :=
    { toFun v := v i k
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hker : ⊤ ≤ f.ker := by
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change b j i k = 0
    exact hb j i k (fun he => hi ⟨j, he.symm.trans hw⟩)
  have he : (Pi.single i (V i).highest : (i : D.base.support) → (V i).space) ∈ f.ker :=
    hker Submodule.mem_top
  change (Pi.single i (V i).highest :
    (i : D.base.support) → (V i).space) i k = 0 at he
  exact hk (by simpa only [Pi.single_eq_same] using he)

/-- The weights of a homogeneous basis of the sum of the fundamental
modules generate the full character algebra of the split torus. -/
theorem torusCoordinatesGenerate_of_fundamentalWeightBasis
    (ω : Basis D.base.support ℤ D.X)
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ}
    (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (w : Index.{u} n → D.X) (hb : ∀ j i, b j i ∈ (V i).weightSpace (w j)) :
    TorusCoordinatesGenerate w :=
  torusCoordinatesGenerate_of_span_eq_top w (fundamentalWeights_span_of_weightBasis ω V b w hb)


end

end TorusWeights

section TriangularProducts

open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralLattices
open Module
open scoped BigOperators
noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}

private theorem basis_coord_zero_of_weight
    {ω : D.base.support → D.X}
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ} (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (w : Index.{u} n → D.X) (hb : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    {μ : D.X} {x : (i : D.base.support) → (V i).space}
    (hx : ∀ i, x i ∈ (V i).weightSpace μ)
    (k : Index.{u} n) (hk : w k ≠ μ) :
    b.coord k x = 0 := by
  classical
  let K := RationalField.{u}
  let W := (i : D.base.support) → (V i).space
  let pr : W →ₗ[K] W :=
    { toFun v i j := if (V i).weight j = μ then v i j else 0
      map_add' v u := by
        funext i j
        change (if (V i).weight j = μ then v i j + u i j else 0) =
          (if (V i).weight j = μ then v i j else 0) + (if (V i).weight j = μ then u i j else 0)
        by_cases h : (V i).weight j = μ <;> simp [h]
      map_smul' r v := by
        funext i j
        change (if (V i).weight j = μ then r • v i j else 0) =
          r • (if (V i).weight j = μ then v i j else 0)
        by_cases h : (V i).weight j = μ <;> simp [h] }
  have hpr : pr x = x := by
    funext i j
    by_cases h : (V i).weight j = μ
    · simp [pr, h]
    · simp [pr, h, hx i j h]
  have hcomp : (b.coord k).comp pr = 0 := by
    apply b.ext
    intro l
    change b.coord k (pr (b l)) = 0
    by_cases hl : w l = μ
    · have hpr' : pr (b l) = b l := by
        funext i j
        by_cases h : (V i).weight j = μ
        · simp [pr, h]
        · simp [pr, h, hb l i j (fun h' => h (h'.trans hl))]
      rw [hpr', Basis.coord_apply, Basis.repr_self_apply]
      exact ite_eq_right (fun h : l = k => hk (h ▸ hl))
    · have hp : pr (b l) = 0 := by
        funext i j
        change (if (V i).weight j = μ then b l i j else 0) = (0 : K)
        by_cases h : (V i).weight j = μ
        · simp [h, hb l i j (h.trans_ne (Ne.symm hl))]
        · simp [h]
      rw [hp, map_zero]
  have he := LinearMap.congr_fun hcomp x
  change b.coord k (pr x) = 0 at he
  rwa [hpr] at he

/-- The integral matrix coefficients have the same weight shifts as the
divided root powers, and their degree-zero matrix is the identity. -/
theorem integralRootPolynomials_support
    {ω : D.base.support → D.X}
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ} (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (w : Index.{u} n → D.X) (hb : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ a m j i, ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
      (dividedPower ((V i).rootOperator a) m).mulVec (b j i)) :
    (∀ a k j, (p a k j).coeff 0 = (1 : Matrix (Index.{u} n) (Index.{u} n) ℤ) k j) ∧
    (∀ a m k j, w k ≠ w j + m • D.datum.root a → (p a k j).coeff m = 0) := by
  classical
  let K := RationalField.{u}
  let : CharZero K :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv.symm : ℚ ≃+* K).toRingHom)
      (ULift.ringEquiv.symm : ℚ ≃+* K).injective
  let x (a : D.I) (m : ℕ) (j : Index.{u} n) (i : D.base.support) :=
    (dividedPower ((V i).rootOperator a) m).mulVec (b j i)
  have hcoord (a : D.I) (m : ℕ) (k j : Index.{u} n) :
      b.coord k (x a m j) = ((p a k j).coeff m : K) := by
    have hs : x a m j = ∑ l : Index.{u} n, ((p a l j).coeff m : K) • b l := by
      funext i
      simpa only [Finset.sum_apply, Pi.smul_apply] using (hp a m j i).symm
    rw [hs, ← b.equivFun_symm_apply]
    exact b.coord_equivFun_symm k _
  constructor
  · intro a k j
    have hx : x a 0 j = b j := by
      funext i
      simp [x]
    apply Int.cast_injective (α := K)
    rw [← hcoord, hx, Basis.coord_apply, Basis.repr_self_apply]
    by_cases h : j = k
    · subst k
      simp
    · simp [h, Ne.symm h, Matrix.one_apply_ne]
  · intro a m k j hweight
    have hx (i : D.base.support) : x a m j i ∈
        (V i).weightSpace (w j + m • D.datum.root a) :=
      dividedPower_mulVec_mem_weightSpace (V i) a
        (rootOperator_weight_shift (V i) a) m (hb j i)
    have hc := basis_coord_zero_of_weight V b w hb hx k hweight
    rw [hcoord] at hc
    exact Int.cast_eq_zero.mp hc


private theorem unitriangular_mul {ι R : Type*} [LinearOrder ι] [DecidableEq ι] [Fintype ι] [Semiring R]
    (upper : Bool) (P Q : Matrix ι ι R)
    (hP : ∀ i j, (if upper then ¬ i < j else ¬ j < i) → P i j = (1 : Matrix ι ι R) i j)
    (hQ : ∀ i j, (if upper then ¬ i < j else ¬ j < i) → Q i j = (1 : Matrix ι ι R) i j)
    (i j : ι) (h : if upper then ¬ i < j else ¬ j < i) :
    (P * Q) i j = (1 : Matrix ι ι R) i j := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · rw [hP i i (by cases upper <;> exact lt_irrefl i), Matrix.one_apply_eq, one_mul, hQ i j h]
  · intro k _ hk
    cases upper with
    | true =>
      have hij : j ≤ i := le_of_not_gt h
      by_cases hik : i < k
      · have hjk := hij.trans_lt hik
        rw [hQ k j (not_lt_of_gt hjk), Matrix.one_apply_ne (ne_of_gt hjk), mul_zero]
      · rw [hP i k hik, Matrix.one_apply_ne (Ne.symm hk), zero_mul]
    | false =>
      have hij : i ≤ j := le_of_not_gt h
      by_cases hki : k < i
      · have hkj := hki.trans_le hij
        rw [hQ k j (not_lt_of_gt hkj), Matrix.one_apply_ne hkj.ne, mul_zero]
      · rw [hP i k hki, Matrix.one_apply_ne (Ne.symm hk), zero_mul]

/-- The degree-zero identity and the sign of the nonzero weight shifts make
each ordered product unitriangular in the prescribed order. -/
theorem orderedMatrix_unitriangular
    {n : ℕ} {σ X : Type u} [AddCommGroup X]
    (l : List σ) (root : σ → X) (w : Index.{u} n → X) (height : X →ₗ[ℤ] ℤ)
    (hw : Antitone (height ∘ w)) (upper : Bool)
    (hs : ∀ a, if upper then 0 < height (root a) else height (root a) < 0)
    (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hzero : ∀ a i j, (p a i j).coeff 0 = (1 : Matrix _ _ ℤ) i j)
    (hcoeff : ∀ a m i j, w i ≠ w j + m • root a → (p a i j).coeff m = 0) :
    ∀ i j, (if upper then ¬ i < j else ¬ j < i) →
      orderedMatrix l p i j = (1 : Matrix _ _ _) i j := by
  classical
  have hone (a : σ) (i j : Index.{u} n) (h : if upper then ¬ i < j else ¬ j < i) :
      p a i j = (1 : Matrix _ _ (Polynomial ℤ)) i j := by
    ext m
    cases m with
    | zero =>
      rw [hzero]
      by_cases hij : i = j
      · subst j
        simp
      · simp [Matrix.one_apply_ne hij]
    | succ m =>
      have hne : w i ≠ w j + (m + 1) • root a := by
        intro he
        have hmul : height (w i) = height (w j) + ((m + 1 : ℕ) : ℤ) * height (root a) := by
          rw [he, map_add, map_nsmul, nsmul_eq_mul]
        have hm : (0 : ℤ) < ((m + 1 : ℕ) : ℤ) := by omega
        cases upper with
        | true =>
          have hle : height (w i) ≤ height (w j) := hw (le_of_not_gt h)
          have hp := mul_pos hm (show 0 < height (root a) from hs a)
          omega
        | false =>
          have hle : height (w j) ≤ height (w i) := hw (le_of_not_gt h)
          have hp := mul_neg_of_pos_of_neg hm (show height (root a) < 0 from hs a)
          omega
      rw [hcoeff a _ i j hne]
      by_cases hij : i = j
      · subst j
        rw [Matrix.one_apply_eq, ← Polynomial.C_1, Polynomial.coeff_C]
        simp
      · simp [Matrix.one_apply_ne hij]
  induction l with
  | nil => simp [orderedMatrix]
  | cons a l ih =>
    intro i j hij
    let f : Polynomial ℤ →+* MvPolynomial σ ℤ :=
      (Polynomial.aeval (MvPolynomial.X a)).toRingHom
    have hA (i j : Index.{u} n) (h : if upper then ¬ i < j else ¬ j < i) :
        f.mapMatrix (p a) i j = (1 : Matrix _ _ _) i j := by
      have he : f.mapMatrix (p a) i j = f.mapMatrix 1 i j :=
        congrArg f (hone a i j h)
      simpa only [map_one] using he
    exact unitriangular_mul upper _ (orderedMatrix l p) hA ih i j hij

end

end TriangularProducts

section ProductCoordinates

open Module
open Specs.IntegralLattices
open scoped Classical
noncomputable section

private def coefficientMatrix {n : ℕ} {R : Type*} [Semiring R]
    (P : Matrix (Index.{u} n) (Index.{u} n) (Polynomial R)) (m : ℕ) :
    Matrix (Index.{u} n) (Index.{u} n) R :=
  Matrix.of fun i j => (P i j).coeff m

private theorem orderedMatrix_coeff {n : ℕ} {σ : Type u}
    (l : List σ) (hl : l.Nodup)
    (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (m : σ →₀ ℕ) :
    (Matrix.of fun i j => (orderedMatrix l p i j).coeff m) =
      if ∀ a, m a ≠ 0 → a ∈ l then
        (l.map (fun a => coefficientMatrix (p a) (m a))).prod
      else 0 := by
  classical
  induction l generalizing m with
  | nil =>
    have hm : (∀ a, m a ≠ 0 → a ∈ ([] : List σ)) ↔ m = 0 := by
      simp [Finsupp.ext_iff]
    rw [hm]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases h : m = 0
      · simp [orderedMatrix, h]
      · simp [orderedMatrix, h, Ne.symm h, MvPolynomial.coeff_one]
    · by_cases h : m = 0 <;> simp [orderedMatrix, Matrix.one_apply_ne hij, h]
  | cons a l ih =>
    let q := orderedMatrix l p
    have hq (i j : Index.{u} n) (d : σ →₀ ℕ) (hd : d a ≠ 0) :
        (q i j).coeff d = 0 := by
      have h := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) ℤ => M i j)
        (ih hl.of_cons d)
      rwa [ite_eq_right (fun hall => hl.notMem (hall a hd))] at h
    have hmul :
        (Matrix.of fun i j => (orderedMatrix (a :: l) p i j).coeff m) =
          coefficientMatrix (p a) (m a) *
            (Matrix.of fun i j => (q i j).coeff (m.erase a)) := by
      ext i j
      simp only [orderedMatrix, List.map_cons, List.prod_cons, Matrix.of_apply, Matrix.mul_apply,
        MvPolynomial.coeff_sum, RingHom.mapMatrix_apply]
      apply Finset.sum_congr rfl
      intro k _
      exact coeff_aeval_X_mul_of_independent a _ _ (hq k j) m
    have hmem : (∀ b, m b ≠ 0 → b ∈ a :: l) ↔ (∀ b, m.erase a b ≠ 0 → b ∈ l) := by
      constructor
      · intro H b hb
        have hba : b ≠ a := by
          rintro rfl
          simp at hb
        rw [Finsupp.erase_ne hba] at hb
        exact (List.mem_cons.mp (H b hb)).resolve_left hba
      · intro H b hb
        by_cases hba : b = a
        · simp [hba]
        · exact List.mem_cons_of_mem _ (H b (by simpa only [Finsupp.erase_ne hba]))
    have herase : (l.map (fun b => coefficientMatrix (p b) (m.erase a b))) =
        l.map (fun b => coefficientMatrix (p b) (m b)) := by
      apply List.map_congr_left
      intro b hb
      have hn : b ≠ a := fun he => hl.notMem (he ▸ hb)
      rw [Finsupp.erase_ne hn]
    rw [hmul, hmem, show (Matrix.of fun i j => (q i j).coeff (m.erase a)) = _ from
      ih hl.of_cons (m.erase a)]
    split_ifs
    · rw [herase, List.map_cons, List.prod_cons]
    · exact mul_zero _

private theorem matrixProduct_weight_support {n : ℕ} {σ X : Type u} [AddCommGroup X]
    (l : List σ) (w : Index.{u} n → X) (d : σ → X)
    (M : σ → Matrix (Index.{u} n) (Index.{u} n) ℤ)
    (hs : ∀ a i j, w i ≠ w j + d a → M a i j = 0) :
    ∀ i j, w i ≠ w j + (l.map d).sum → (l.map M).prod i j = 0 := by
  induction l with
  | nil =>
    intro i j h
    have hij : i ≠ j := by
      rintro rfl
      exact h (by simp)
    simp [Matrix.one_apply_ne hij]
  | cons a l ih =>
    intro i j h
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : w i = w k + d a
    · have hkj : w k ≠ w j + (l.map d).sum := by
        intro hk
        apply h
        simp only [List.map_cons, List.sum_cons]
        rw [hki, hk]
        abel
      rw [ih k j hkj, mul_zero]
    · rw [hs a i k hki, zero_mul]

private theorem list_weight_sum_eq {σ X : Type*} [DecidableEq σ] [AddCommGroup X]
    (l : List σ) (hl : l.Nodup) (root : σ → X) (m : σ →₀ ℕ)
    (hm : ∀ a, m a ≠ 0 → a ∈ l) :
    (l.map (fun a => m a • root a)).sum = m.sum (fun a n => n • root a) := by
  classical
  rw [← List.sum_toFinset _ hl, Finsupp.sum]
  symm
  apply Finset.sum_subset
  · intro a ha
    exact List.mem_toFinset.mpr (hm a (Finsupp.mem_support_iff.mp ha))
  · intro a _ ha
    simp [Finsupp.notMem_support_iff.mp ha]

private theorem orderedMatrix_coeff_weight {n : ℕ} {σ X : Type u} [AddCommGroup X]
    (l : List σ) (hl : l.Nodup) (root : σ → X) (w : Index.{u} n → X)
    (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hs : ∀ a m i j, w i ≠ w j + m • root a → (p a i j).coeff m = 0)
    (m : σ →₀ ℕ) (i j : Index.{u} n)
    (hij : w i ≠ w j + m.sum (fun a t => t • root a)) :
    (orderedMatrix l p i j).coeff m = 0 := by
  classical
  have hc := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) ℤ => M i j)
    (orderedMatrix_coeff l hl p m)
  simp only [Matrix.of_apply] at hc
  by_cases hm : ∀ a, m a ≠ 0 → a ∈ l
  · rw [ite_eq_left hm] at hc
    rw [hc]
    exact matrixProduct_weight_support l w (fun a => m a • root a)
      (fun a => coefficientMatrix (p a) (m a)) (fun a i j => hs a (m a) i j) i j
      (by rwa [list_weight_sum_eq l hl root m hm])
  · rwa [ite_eq_right hm] at hc

private theorem orderedMatrix_linear_coeff {n : ℕ} {σ : Type u}
    (l : List σ) (hl : l.Nodup)
    (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hzero : ∀ a i j, (p a i j).coeff 0 = (1 : Matrix _ _ ℤ) i j) {a : σ} (ha : a ∈ l) :
    (Matrix.of fun i j => (orderedMatrix l p i j).coeff (Finsupp.single a 1)) =
      coefficientMatrix (p a) 1 := by
  classical
  have hc (b : σ) : coefficientMatrix (p b) 0 = 1 := Matrix.ext (hzero b)
  rw [orderedMatrix_coeff l hl, ite_eq_left (by
    intro b hb
    by_cases h : b = a
    · simpa [h] using ha
    · exact False.elim (hb (Finsupp.single_eq_of_ne h)))]
  rw [list_prod_map_eq_of_single l hl _ ha (fun b _ hb => by
    rw [Finsupp.single_eq_of_ne hb, hc]), Finsupp.single_eq_same]

private def triangularEntry {n : ℕ} (upper : Bool) (i j : Index.{u} n) :
    MvPolynomial (triangularEntries n upper) ℤ :=
  if h : if upper then i < j else j < i then MvPolynomial.X ⟨(i, j), h⟩
  else MvPolynomial.C ((1 : Matrix _ _ ℤ) i j)

private theorem aeval_triangularEntry {n : ℕ} {σ : Type u} (upper : Bool)
    (P : Matrix (Index.{u} n) (Index.{u} n) (MvPolynomial σ ℤ))
    (ht : ∀ i j, (if upper then ¬ i < j else ¬ j < i) → P i j = (1 : Matrix _ _ _) i j)
    (i j : Index.{u} n) :
    MvPolynomial.aeval (fun k : triangularEntries n upper => P k.val.1 k.val.2)
      (triangularEntry upper i j) = P i j := by
  by_cases h : if upper then i < j else j < i
  · rw [triangularEntry, dite_eq_left h]
    exact MvPolynomial.aeval_X (fun k : triangularEntries n upper => P k.val.1 k.val.2)
      (⟨(i, j), h⟩ : triangularEntries n upper)
  · rw [triangularEntry, dite_eq_right h, MvPolynomial.aeval_C, ht i j (by cases upper <;> exact h)]
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.one_apply_ne hij]

private theorem linearMap_pi_apply_eq_sum {n : ℕ}
    (φ : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ) (v : Index.{u} n → ℤ) :
    φ v = ∑ i, φ (Pi.single i 1) * v i := by
  conv_lhs => rw [← (Pi.basisFun ℤ (Index.{u} n)).sum_repr v, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.basisFun_repr, Pi.basisFun_apply, LinearMap.map_smul, smul_eq_mul, mul_comm]

/-- A homogeneous integral coefficient equal to one on each root operator
gives inverse coordinates in the entries of the ordered triangular product. -/
theorem orderedMatrix_inverse_coordinates {n : ℕ} {σ X : Type u} [AddCommGroup X]
    (upper : Bool) (l : List σ) (hl : Specs.OrderedRootProducts.Enumerates l Set.univ)
    (root : σ ↪ X) (w : Index.{u} n → X) (height : X →ₗ[ℤ] ℤ)
    (hr : ∀ a, 0 < height (root a))
    (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hzero : ∀ a i j, (p a i j).coeff 0 = (1 : Matrix _ _ ℤ) i j)
    (hs : ∀ a m i j, w i ≠ w j + m • root a → (p a i j).coeff m = 0)
    (ht : ∀ i j, (if upper then ¬ i < j else ¬ j < i) →
      orderedMatrix l p i j = (1 : Matrix _ _ _) i j)
    (hunit : ∀ a, ∃ (μ : X) (v : Index.{u} n → ℤ) (φ : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ),
      (∀ j, w j ≠ μ → v j = 0) ∧
      (∀ j, w j ≠ μ + root a → φ (Pi.single j 1) = 0) ∧
      φ ((coefficientMatrix (p a) 1).mulVec v) = 1) :
    ∀ a : σ, ∃ q : MvPolynomial (triangularEntries n upper) ℤ,
      MvPolynomial.aeval (fun ij => orderedMatrix l p ij.val.1 ij.val.2) q = MvPolynomial.X a := by
  classical
  choose μ v φ hv hφ hu using hunit
  let P := orderedMatrix l p
  let entry := fun ij : triangularEntries n upper => P ij.val.1 ij.val.2
  let test (a : σ) := ∑ i : Index.{u} n, ∑ j : Index.{u} n,
    MvPolynomial.C (φ a (Pi.single i 1) * v a j) * triangularEntry upper i j
  have ht' (a : σ) (m : σ →₀ ℕ) :
      (MvPolynomial.aeval entry (test a)).coeff m =
        ∑ i : Index.{u} n, ∑ j : Index.{u} n,
          (φ a (Pi.single i 1) * v a j) * (P i j).coeff m := by
    simp only [test, map_sum, map_mul, MvPolynomial.coeff_sum]
    simp only [entry, aeval_triangularEntry upper P ht, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
    simp only [← MvPolynomial.C_mul, MvPolynomial.coeff_C_mul]
  apply recover_coordinates_of_weights root height hr entry test
  · intro a
    rw [ht']
    refine Eq.trans ?_ (hu a)
    rw [linearMap_pi_apply_eq_sum]
    have hc := orderedMatrix_linear_coeff l hl.1 p hzero ((hl.2 a).mpr (Set.mem_univ a))
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change _ * (Matrix.of (fun i j => (P i j).coeff (Finsupp.single a 1))) i j =
      _ * ((coefficientMatrix (p a) 1) i j * _)
    rw [hc]
    ring
  · intro a m hm
    by_contra hweight
    apply hm
    rw [ht']
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : w i = μ a + root a
    · apply Finset.sum_eq_zero
      intro j _
      by_cases hj : w j = μ a
      · rw [orderedMatrix_coeff_weight l hl.1 root w p hs m i j (by simpa [hi, hj] using Ne.symm hweight),
          mul_zero]
      · rw [hv a j hj, mul_zero, zero_mul]
    · simp [hφ a i hi]

end

end ProductCoordinates

section HighestWeightPresentation

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (IsRootString)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralLattices

noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 650000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- The simple raising relations already imply the relations for all
positive root vectors in the cyclic highest-weight presentation. -/
theorem highestWeightRelations_eq_simple
    (s : IdentityLieStructure Q.pinned.pair.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val) (lam : D.X),
      (∀ i j k, D.datum.root i + D.datum.root j = D.datum.root k →
        ∃ (p q : ℕ) (n : ℤ), IsRootString i j p q ∧
          (n = (p : ℤ) + 1 ∨ n = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = n • e k) →
      highestWeightRelations e h lam =
        Submodule.span (UniversalEnvelopingAlgebra RationalField (Lie RationalField Q.pinned.pair.G.val))
          (Set.range (fun a : D.base.support => UniversalEnvelopingAlgebra.ι RationalField (e a)) ∪
            Set.range (fun j : D.base.support =>
              UniversalEnvelopingAlgebra.ι RationalField (h j) -
                algebraMap RationalField _ (D.datum.coroot' j lam : RationalField)) ∪
            Set.range (fun j : D.base.support =>
              UniversalEnvelopingAlgebra.ι RationalField (e (D.datum.reflectionPerm j j)) ^
                ((D.datum.coroot' j lam).toNat + 1))) := by
  classical
  let := s.lieRing
  let := s.lieAlgebra
  intro e h lam bracket
  let : Finite D.I := D.finiteRoots
  let K := RationalField.{u}
  let : CharZero K :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv.symm : ℚ ≃+* K).toRingHom)
      (ULift.ringEquiv.symm : ℚ ≃+* K).injective
  let U := UniversalEnvelopingAlgebra K (Lie K Q.pinned.pair.G.val)
  let ι := UniversalEnvelopingAlgebra.ι K (L := Lie K Q.pinned.pair.G.val)
  let S : Submodule U U := Submodule.span U
    (Set.range (fun a : D.base.support => ι (e a)) ∪
      Set.range (fun j : D.base.support => ι (h j) - algebraMap K U (D.datum.coroot' j lam : K)) ∪
      Set.range (fun j : D.base.support => ι (e (D.datum.reflectionPerm j j)) ^
        ((D.datum.coroot' j lam).toNat + 1)))
  have hsimple (i : D.I) (hi : i ∈ D.base.support) : ι (e i) ∈ S :=
    Submodule.subset_span (Or.inl (Or.inl ⟨⟨i, hi⟩, rfl⟩))
  have hpos (i : D.I) (hi : D.base.IsPos i) : ι (e i) ∈ S := by
    apply RootPairing.Base.IsPos.induction_on_add hi
    · exact hsimple
    · intro j l k hsum hj hl
      have hl' := hsimple l hl
      obtain ⟨p, _, n, _, hn, he⟩ := bracket j l k hsum.symm
      have hn' : (n : K) ≠ 0 := Int.cast_ne_zero.mpr (by rcases hn with h | h <;> omega)
      have hmul : ι ⁅e j, e l⁆ ∈ S := by
        rw [ι.map_lie, Ring.lie_def]
        exact S.sub_mem (S.smul_mem (ι (e j)) hl') (S.smul_mem (ι (e l)) hj)
      have hmul' : (n : K) • ι (e k) ∈ S := by
        have hadditive := congrArg
          (fun law : AddGroup (PointKernel Q.pinned.pair.G.val) => law.zsmul n (e k)) s.group_law
        have hz : ι ⁅e j, e l⁆ = (n : K) • ι (e k) := calc
          _ = ι (s.lieRing.toAddCommGroup.toAddGroup.zsmul n (e k)) :=
            congrArg ι (he.trans hadditive.symm)
          _ = n • ι (e k) := @AddMonoidHom.map_zsmul _ _
            s.lieRing.toAddCommGroup.toAddGroup inferInstance ι.toLinearMap.toAddMonoidHom n (e k)
          _ = _ := (Int.cast_smul_eq_zsmul K n (ι (e k))).symm
        exact hz ▸ hmul
      have hres := S.smul_mem (algebraMap K U ((n : K)⁻¹)) hmul'
      change (algebraMap K U ((n : K)⁻¹)) * ((n : K) • ι (e k)) ∈ S at hres
      rwa [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hn', one_smul] at hres
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ((⟨a, rfl⟩ | ha) | ha)
    · exact hpos a a.property
    · exact Submodule.subset_span (Or.inl (Or.inr ha))
    · exact Submodule.subset_span (Or.inr ha)
  · apply Submodule.span_le.mpr
    rintro _ ((⟨a, rfl⟩ | ha) | ha)
    · exact Submodule.subset_span (Or.inl (Or.inl ⟨(⟨a, D.base.isPos_of_mem_support a.property⟩ :
        Positive D), rfl⟩))
    · exact Submodule.subset_span (Or.inl (Or.inr ha))
    · exact Submodule.subset_span (Or.inr ha)

end

end HighestWeightPresentation

section RationalPresentations

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (CyclicPresentation serreHighestRelations loweringWord loweringWeight cyclicVector)
open Module
open scoped Classical

noncomputable section

variable {D : BasedRootDatum.{u}}

private theorem loweringWeight_eq_initial (height : D.X →ₗ[ℤ] ℤ)
    (hpositive : ∀ i : D.base.support, 0 < height (D.datum.root i))
    (lam : D.X) (l : List D.base.support) :
    loweringWeight D lam l = lam ↔ l = [] := by
  constructor
  · intro h
    have hw : (l.map (fun i : D.base.support => height (D.datum.root i))).sum = 0 := by
      have h' : (l.map fun i : D.base.support => D.datum.root i).sum = 0 := by
        change lam - ((l.flatMap fun i => [i.val]).map D.datum.root).sum = lam at h
        have h' : lam - (l.map fun i : D.base.support => D.datum.root i).sum = lam - 0 := by
          simpa only [← List.map_eq_flatMap, List.map_map, Function.comp_def, sub_zero] using h
        exact (sub_right_inj.mp h')
      simpa only [map_zero, map_list_sum, List.map_map, Function.comp_def] using congrArg height h'
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [List.map_cons, List.sum_cons] at hw
      have htail : 0 ≤ (l.map (fun i : D.base.support => height (D.datum.root i))).sum := by
        apply List.sum_nonneg
        rintro _ hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact (hpositive i).le
      linarith [hpositive a]
  · rintro rfl
    simp [loweringWeight]

variable [DecidableEq D.base.support]

/-- In a lowering-word basis of the rational cyclic quotient, the original
weight labels exactly the basis vector of the empty word. -/
theorem loweringWordBasis_highest_line {J : Type u}
    (lam : D.X) (b : Basis J ℚ (CyclicPresentation (serreHighestRelations D lam)))
    (words : J → List D.base.support) (hb : ∀ j, b j = loweringWord D lam (words j))
    (j₀ : J) (hj₀ : words j₀ = [])
    (height : D.X →ₗ[ℤ] ℤ) (hpos : ∀ i : D.base.support, 0 < height (D.datum.root i)) :
    b j₀ = cyclicVector (serreHighestRelations D lam) ∧
    ∀ j : J, loweringWeight D lam (words j) = lam ↔ j = j₀ := by
  have h₀ : b j₀ = cyclicVector (serreHighestRelations D lam) := by
    rw [hb, hj₀]
    rfl
  refine ⟨h₀, fun j => ?_⟩
  rw [loweringWeight_eq_initial height hpos]
  constructor
  · intro he
    apply b.injective
    rw [hb j, he, h₀]
    rfl
  · rintro rfl
    exact hj₀

end

end RationalPresentations

section SimpleRootCoefficients

open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralLattices
open Module
open scoped Classical

noncomputable section


variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}} {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)] [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {ω : D.base.support → D.X}

private def latticeFunctional {n : ℕ} (d : Index.{u} n → ℤ) : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ∑ j, d j * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

private theorem latticeFunctional_single {n : ℕ} (d : Index.{u} n → ℤ) (j : Index.{u} n) :
    latticeFunctional d (Pi.single j 1) = d j := by
  change ∑ i, d i * Pi.single (M := fun _ : Index.{u} n => ℤ) j 1 i = d j
  simp [Pi.single_apply, mul_ite]

/-- A highest-weight line supplies an integral linear functional on the
sum of the lattices. The simple lowering of its highest vector tests
the linear coefficient of the simple raising operator. -/
theorem simpleRoot_unit_coefficient
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    (negative : List (Negative D)) (hV : ∀ i, (V i).IsIntegralLattice negative)
    {n : ℕ} (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (w : Index.{u} n → D.X) (hw : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    (hb : Submodule.span ℤ (Set.range b) =
      Submodule.pi Set.univ (fun i => (V i).lattice negative))
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ a m j i, ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
      (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    (i : D.base.support) (hi : D.base.IsPos i)
    (hbracket : ⁅e i, e (D.datum.reflectionPerm i i)⁆ = h i)
    (hweight : D.datum.coroot' i (ω i) = 1) :
    ∃ (μ : D.X) (v : Index.{u} n → ℤ) (φ : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ),
      (∀ j, w j ≠ μ → v j = 0) ∧
      (∀ j, w j ≠ μ + D.datum.root i → φ (Pi.single j 1) = 0) ∧
      φ ((coefficientMatrix (p i) 1).mulVec v) = 1 := by
  classical
  let : CharZero RationalField.{u} :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
      (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective
  let a := D.datum.reflectionPerm i i
  have ha : D.datum.root a = -D.datum.root i := by simp [a]
  let μ := ω i + D.datum.root a
  have hμ : μ + D.datum.root i = ω i := by simp [μ, ha]
  let y := ((V i).rootOperator a).mulVec (V i).highest
  let x : (j : D.base.support) → (V j).space := Pi.single i y
  have hy : y ∈ (V i).lattice negative := by
    simpa only [y, dividedPower, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one]
      using (hV i).2.2.2.2.2 a 1 _ (highest_mem_lattice (V i) negative)
  have hx : x ∈ Submodule.span ℤ (Set.range b) := by
    rw [hb, Submodule.mem_pi]
    intro j _
    by_cases hj : i = j
    · subst j
      simpa [x] using hy
    · simp [x, Pi.single_eq_of_ne (Ne.symm hj)]
  have hxμ : ∀ j, x j ∈ (V j).weightSpace μ := by
    intro j
    by_cases hj : i = j
    · subst j
      simpa only [x, Pi.single_eq_same] using
        mulVec_mem_weightSpace (V i) (rootOperator_weight_shift (V i) a) (V i).highest_support
    · simp [x, Pi.single_eq_of_ne (Ne.symm hj)]
  obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  have hvK : ∑ j : Index.{u} n, (v j : RationalField.{u}) • b j = x := by
    simpa only [Int.cast_smul_eq_zsmul] using hv
  have hvi (j : Index.{u} n) (hj : w j ≠ μ) : v j = 0 := by
    have hz := basis_coord_zero_of_weight V b w hw hxμ j hj
    rw [← hvK, ← b.equivFun_symm_apply, Basis.coord_equivFun_symm] at hz
    exact Int.cast_eq_zero.mp hz
  obtain ⟨k, hk⟩ : ∃ k, (V i).highest k ≠ 0 := by
    by_contra! h
    exact (V i).highest_ne_zero (funext h)
  have hcoeff (j : Index.{u} n) : ∃ c : ℤ,
      (c : RationalField.{u}) * (V i).highest k = b j i k ∧ (w j ≠ ω i → c = 0) := by
    by_cases hj : w j = ω i
    · have hjl : b j i ∈ (V i).lattice negative := by
        have hmem : b j ∈ Submodule.span ℤ (Set.range b) :=
          Submodule.subset_span (Set.mem_range_self j)
        rw [hb, Submodule.mem_pi] at hmem
        exact hmem i (Set.mem_univ i)
      have hw' := hw j i
      rw [hj] at hw'
      have hij : b j i ∈ (V i).lattice negative ⊓
          ((V i).weightSpace (ω i)).restrictScalars ℤ := ⟨hjl, hw'⟩
      rw [(hV i).2.2.2.2.1, Submodule.mem_span_singleton] at hij
      obtain ⟨c, hc⟩ := hij
      refine ⟨c, ?_, fun hn => (hn hj).elim⟩
      simpa only [Int.cast_smul_eq_zsmul, Pi.smul_apply, smul_eq_mul]
        using (Int.cast_smul_eq_zsmul RationalField.{u} c ((V i).highest k)).trans (congrFun hc k)
    · have hki : (V i).weight k = ω i := by
        by_contra hn
        exact hk ((V i).highest_support k hn)
      exact ⟨0, by simpa using (hw j i k (by rwa [hki, ne_comm])).symm, fun _ => rfl⟩
  choose d hd hd0 using hcoeff
  let φ := latticeFunctional d
  refine ⟨μ, v, φ, hvi, fun j hj => ?_, ?_⟩
  · rw [hμ] at hj
    rw [latticeFunctional_single]
    exact hd0 j hj
  let E := coefficientMatrix (p i) 1
  have hre (j : Index.{u} n) :
      ∑ l, ((E l j : ℤ) : RationalField.{u}) * b l i k = ((V i).rootOperator i).mulVec (b j i) k := by
    simpa only [E, coefficientMatrix, Matrix.of_apply, dividedPower, Nat.factorial_one,
      Nat.cast_one, inv_one, one_smul, pow_one, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using congrFun (hp i 1 j i) k
  have hxik : ∑ j : Index.{u} n, (v j : RationalField.{u}) • b j i = y := by
    simpa only [Finset.sum_apply, Pi.smul_apply, x, Pi.single_eq_same] using congrFun hvK i
  have htop : ((V i).rootOperator i).mulVec y = (V i).highest :=
    simple_root_mulVec_lowering (V i) i hi a hbracket hweight
  change φ (E.mulVec v) = 1
  apply Int.cast_injective (α := RationalField.{u})
  rw [Int.cast_one]
  apply mul_right_cancel₀ hk
  rw [one_mul]
  calc
    _ = ∑ l : Index.{u} n, ∑ j : Index.{u} n,
        (v j : RationalField.{u}) * (((E l j : ℤ) : RationalField.{u}) * b l i k) := by
      change ((↑(∑ l, d l * E.mulVec v l) : RationalField.{u}) * (V i).highest k) = _
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hd l]
      ring
    _ = ∑ j : Index.{u} n, (v j : RationalField.{u}) * ((V i).rootOperator i).mulVec (b j i) k := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hre]
    _ = (V i).highest k := by
      let L := ((V i).rootOperator i).mulVecLin
      have he := congrArg L hxik
      rw [map_sum] at he
      simp only [map_smul] at he
      have hv := congrFun he k
      change (∑ j, (v j : RationalField.{u}) • L (b j i)) k = _ at hv
      rw [show L y = (V i).highest from htop] at hv
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, L, Matrix.mulVecLin_apply] using hv

end

end SimpleRootCoefficients

section RankOneWords

variable {R G : Type*} [CommRing R] [Group G]

private def rankOnePoint (x y : R → G) (t : Rˣ) : G :=
  x (t : R) * y (-(↑t⁻¹ : R)) * x (t : R)

/-- The opposite-root factorization with a unit denominator compares the two
rank-one words at a unit parameter and at one. -/
theorem rankOnePoint_eq_torus_mul
    (x y : R → G) (h : Rˣ →* G)
    (hx : ∀ a b, x (a + b) = x a * x b)
    (hscale : ∀ (s : Rˣ) a, h s * x a * (h s)⁻¹ = x ((s : R)^2 * a))
    (hop : ∀ (a b : R) (s : Rˣ), (s : R) = 1 + a * b →
      y a * x b = x (b * (↑s⁻¹ : R)) * h s⁻¹ * y (a * (↑s⁻¹ : R)))
    (t : Rˣ) :
    rankOnePoint x y t = h t * rankOnePoint x y 1 := by
  have ht : (↑t⁻¹ : R) = 1 + -(↑t⁻¹ : R) * ((t : R) - 1) := by
    rw [neg_mul, mul_sub, Units.inv_mul, mul_one]
    ring
  have he := hop (-(↑t⁻¹ : R)) ((t : R) - 1) t⁻¹ ht
  simp only [inv_inv, neg_mul, Units.inv_mul] at he
  have hgroup : x ((t : R) ^ 2) * h t = h t * x 1 := by
    rw [← mul_one ((t : R)^2), ← hscale t 1, mul_assoc, inv_mul_cancel, mul_one]
  have hsum : (t : R) + ((t : R) - 1) * t = (t : R) ^ 2 := by ring
  calc
    rankOnePoint x y t =
        x (t : R) * (y (-(↑t⁻¹ : R)) * x ((t : R) - 1)) * x 1 := by
      unfold rankOnePoint
      have ht' : x ((t : R) - 1) * x 1 = x (t : R) := by
        rw [← hx, sub_add_cancel]
      rw [← ht']
      group
    _ = x ((t : R)^2) * h t * y (-1) * x 1 := by
      rw [he, ← mul_assoc (x _) _ _, ← mul_assoc (x _) _ _, ← hx, hsum]
    _ = h t * rankOnePoint x y 1 := by
      rw [hgroup]
      simp only [rankOnePoint, inv_one, Units.val_one, mul_assoc]

/-- Once the change of parameter is the marked coroot, torus conjugation
of the rank-one word identifies its conjugation action on the torus. -/
theorem rankOnePoint_conjugates
    (x y : R → G) (h : Rˣ →* G) (g : G) (a : Rˣ)
    (hscale : g * rankOnePoint x y 1 * g⁻¹ = rankOnePoint x y a)
    (hchange : rankOnePoint x y a = h a * rankOnePoint x y 1) :
    rankOnePoint x y 1 * g * (rankOnePoint x y 1)⁻¹ = (h a)⁻¹ * g := by
  let n := rankOnePoint x y (1 : Rˣ)
  have hl : g * n = h a * n * g :=
    (mul_inv_eq_iff_eq_mul).mp (hscale.trans hchange)
  calc
    n * g * n⁻¹ = (h a)⁻¹ * (h a * n * g) * n⁻¹ := by group
    _ = (h a)⁻¹ * g := by rw [← hl]; group

end RankOneWords

section MarkedRankOneWords

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped CategoryTheory.MonObj
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.RootGroups (AdditiveLine rankOneWord)
open Specs.IntegralRootRelations (RootCoordinates OppositeRootRelations root rootIndex torus)
open Specs.AdjointRepresentation (GroupPoints)
open CocharacterDynamics (cocharacterPoint unitPoint)
open private rootPoint_eq additivePoints_add characterUnit characterValue_eq_unit characterUnit_inv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private unitPointHom unitPointHom_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}} {Q : Realization D A}

private def rootMapAt (z : RootCoordinates Q) (a : D.I) :
    A.group ⟶ Q.pinned.pair.G.val :=
  (z a).val.hom ≫ (Q.pinned.roots (rootIndex Q a)).val.inclusion

private theorem marked_root_add (z : RootCoordinates Q) (R : TestAlgebra RationalField.{u})
    (a : D.I) (x y : R) : root Q z a R (x + y) = root Q z a R x * root Q z a R y := by
  let f := rootMapAt z a
  change Specs.RootGroups.rootPoint f R (x + y) = _
  change Specs.RootGroups.rootPoint f R (x + y) =
    Specs.RootGroups.rootPoint f R x * Specs.RootGroups.rootPoint f R y
  rw [rootPoint_eq, rootPoint_eq, rootPoint_eq, additivePoints_add, MonObj.mul_comp]

private theorem marked_torus_neg (y : D.Y) (R : TestAlgebra RationalField.{u}) (s : Rˣ) :
    torus Q (-y) R s = (torus Q y R s)⁻¹ := by
  let : IsCommMonObj Q.pinned.pair.T.group.X := Q.attached.comm
  have hn : markedCocharacter Q (-y) = (markedCocharacter Q y)⁻¹ := by
    unfold markedCocharacter
    rw [map_neg]
    rfl
  unfold torus
  change cocharacterPoint (markedCocharacter Q (-y)) R s ≫ Q.pinned.pair.T.inclusion.hom.hom = _
  rw [hn]
  change (unitPoint R s ≫ ((markedCocharacter Q y).hom.hom)⁻¹) ≫
      Q.pinned.pair.T.inclusion.hom.hom =
    ((unitPoint R s ≫ (markedCocharacter Q y).hom.hom) ≫
      Q.pinned.pair.T.inclusion.hom.hom)⁻¹
  rw [GrpObj.comp_inv, GrpObj.inv_comp]

private theorem marked_root_scale_coroot (z : RootCoordinates Q) (a : D.I)
    (R : TestAlgebra RationalField.{u}) (t : Rˣ) (x : R) :
    torus Q (D.datum.coroot a) R t * root Q z a R x *
      (torus Q (D.datum.coroot a) R t)⁻¹ = root Q z a R ((t : R) ^ 2 * x) := by
  let y := D.datum.coroot a
  let T := cocharacterPoint (markedCocharacter Q y) R t
  have h := (z a).property R T x
  change torus Q y R t * root Q z a R x * (torus Q y R t)⁻¹ =
      root Q z a R (Specs.CharacterPairing.characterValue (rootIndex Q a).val R T * x) at h
  rw [← markedCharacter_root Q a] at h
  dsimp only [T] at h
  rw [(RootData.CharacterPairing.characterPairingComposition _ _ _).2,
    markedCharacter_pairing] at h
  change _ = root Q z a R ((↑(t ^ D.datum.pairing a a) : R) * x) at h
  rw [D.datum.pairing_same, zpow_ofNat, Units.val_pow_eq_pow_val] at h
  exact h

private def markedTorusPointHom (y : D.Y) (R : TestAlgebra RationalField.{u}) :
    Rˣ →* GroupPoints Q.pinned.pair.G.val R :=
  (((groupPointsFunctor RationalField.{u}).map
    (markedCocharacter Q y ≫ Q.pinned.pair.T.inclusion)).app R).hom.comp (unitPointHom R)

private theorem markedTorusPointHom_apply (y : D.Y) (R : TestAlgebra RationalField.{u}) (t : Rˣ) :
    markedTorusPointHom (Q := Q) y R t = torus Q y R t := by
  change unitPointHom R t ≫ (markedCocharacter Q y ≫ Q.pinned.pair.T.inclusion).hom.hom = _
  rw [unitPointHom_apply]
  rfl

/-- For the chosen Chevalley coordinates the rank-one word at a unit
parameter differs from the word at one by the marked coroot. -/
theorem marked_rankOneWord_eq_coroot_mul (z : RootCoordinates Q)
    (ho : OppositeRootRelations Q z) (a : D.I) (R : TestAlgebra RationalField.{u}) (t : Rˣ) :
    let b := D.datum.reflectionPerm a a
    rankOneWord (rootMapAt z a) (rootMapAt z b) R t =
      torus Q (D.datum.coroot a) R t * rankOneWord (rootMapAt z a) (rootMapAt z b) R 1 := by
  let b := D.datum.reflectionPerm a a
  have hb : D.datum.root b = -D.datum.root a := by simp [b]
  have hb' : D.datum.root a = -D.datum.root b := by rw [hb, neg_neg]
  have hbY : D.datum.coroot b = -D.datum.coroot a := by simp [b]
  let h := markedTorusPointHom (Q := Q) (D.datum.coroot a) R
  have he (s) : h s = torus Q (D.datum.coroot a) R s := markedTorusPointHom_apply _ _ _
  have hs (s : Rˣ) (x : R) :
      h s * root Q z a R x * (h s)⁻¹ = root Q z a R ((s : R)^2 * x) := by
    rw [he]
    exact marked_root_scale_coroot z a R s x
  have hh (x y : R) (s : Rˣ) (hxy : (s : R) = 1 + x * y) :
      root Q z b R x * root Q z a R y =
        root Q z a R (y * (↑s⁻¹ : R)) * h s⁻¹ * root Q z b R (x * (↑s⁻¹ : R)) := by
    have e := ho b a hb' R x y s hxy
    rwa [hbY, marked_torus_neg, ← he, ← map_inv] at e
  have heq := rankOnePoint_eq_torus_mul (root Q z a R) (root Q z b R) h
    (marked_root_add z R a) hs hh t
  rw [he] at heq
  exact heq

/-- The rank-one word built from the chosen root coordinates conjugates the
marked torus by the reflection formula on every rational test algebra. -/
theorem marked_rankOneWord_conjugates_torus (z : RootCoordinates Q)
    (ho : OppositeRootRelations Q z) (a : D.I) (R : TestAlgebra RationalField.{u})
    (t : GroupPoints Q.pinned.pair.T.group R) :
    let b := D.datum.reflectionPerm a a
    let n := rankOneWord (rootMapAt z a) (rootMapAt z b) R 1
    let g : GroupPoints Q.pinned.pair.G.val R := t ≫ Q.pinned.pair.T.inclusion.hom.hom
    let c := characterUnit (rootIndex Q a).val R t
    n * g * n⁻¹ = (torus Q (D.datum.coroot a) R c)⁻¹ * g := by
  let b := D.datum.reflectionPerm a a
  let α := (rootIndex Q a).val
  let c := characterUnit α R t
  let H := markedTorusPointHom (Q := Q) (D.datum.coroot a) R
  have hb : D.datum.root b = -D.datum.root a := by simp [b]
  have hχ : (rootIndex Q b).val = α⁻¹ := by
    rw [← markedCharacter_root Q b, hb, show α = markedCharacter Q (D.datum.root a) from
      (markedCharacter_root Q a).symm]
    unfold markedCharacter
    rw [map_neg]
    rfl
  have hpos : Specs.RootGroups.HasScalarAction Q.pinned.pair.T α (rootMapAt z a) := (z a).property
  have hneg : Specs.RootGroups.HasScalarAction Q.pinned.pair.T α⁻¹ (rootMapAt z b) := by
    rw [← hχ]
    exact (z b).property
  have he := RootData.RootGroups.conjugateRankOneWord Q.pinned.pair.T hpos hneg R t c 1
    (characterValue_eq_unit _ _ _) (by rw [characterValue_eq_unit, characterUnit_inv])
  dsimp only at he
  rw [mul_one] at he
  have hh := marked_rankOneWord_eq_coroot_mul z ho a R c
  dsimp only at hh
  rw [← markedTorusPointHom_apply] at hh
  let g : GroupPoints Q.pinned.pair.G.val R := t ≫ Q.pinned.pair.T.inclusion.hom.hom
  change rankOnePoint (root Q z a R) (root Q z b R) 1 * g *
    (rankOnePoint (root Q z a R) (root Q z b R) 1)⁻¹ =
    (torus Q (D.datum.coroot a) R c)⁻¹ * g
  rw [← markedTorusPointHom_apply (Q := Q) (D.datum.coroot a) R c]
  exact rankOnePoint_conjugates _ _ H g c he hh


end

end MarkedRankOneWords

section RootReflections

open Specs.Pinning (BasedRootDatum)

/-- A property verified on the simple roots and preserved by their
reflections holds on every root of the finite based datum. -/
theorem all_roots_of_simple_reflections (D : BasedRootDatum.{u})
    (height : D.X →ₗ[ℤ] ℤ) (hpos : ∀ i : Positive D, 0 < height (D.datum.root i))
    (P : D.I → Prop) (hsimple : ∀ i : D.base.support, P i)
    (hreflect : ∀ (i : D.base.support) (a : D.I), P a → P (D.datum.reflectionPerm i a)) :
    ∀ i, P i := by
  classical
  let : Finite D.I := D.finiteRoots
  let : D.datum.IsReduced := D.reduced
  let := D.datum.indexNeg
  have hneg (j : D.I) : D.datum.root (-j) = -D.datum.root j := by
    change D.datum.root (D.datum.reflectionPerm j j) = _
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self]
  have hrefneg (j i : D.I) :
      D.datum.reflectionPerm j (-i) = -D.datum.reflectionPerm j i := by
    apply D.datum.root.injective
    rw [hneg, D.datum.root_reflectionPerm, D.datum.root_reflectionPerm, hneg, map_neg]
  have hplus (a : D.I) (ha : D.base.IsPos a) : P a ∧ P (-a) := by
    generalize hn : (height (D.datum.root a)).toNat = n
    induction n using Nat.strong_induction_on generalizing a with
    | h n ih =>
      by_cases has : a ∈ D.base.support
      · let i : D.base.support := ⟨a, has⟩
        exact ⟨hsimple i, hreflect i i (hsimple i)⟩
      obtain ⟨j, hj, ht⟩ := ha.exists_mem_support_pos_pairingIn
      rw [D.datum.zero_lt_pairingIn_iff'] at ht
      let i : D.base.support := ⟨j, hj⟩
      let b := D.datum.reflectionPerm i a
      have hne : a ≠ j := fun he => has (he ▸ hj)
      have hb : D.base.IsPos b := ha.reflectionPerm hj hne
      have hdecrease : height (D.datum.root b) < height (D.datum.root a) := by
        rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_root' ℤ, map_sub, map_zsmul,
          zsmul_eq_mul]
        exact sub_lt_self _ (mul_pos ht (hpos ⟨i, D.base.isPos_of_mem_support hj⟩))
      have hm : (height (D.datum.root b)).toNat < n := by
        have hb' : 0 < height (D.datum.root b) := hpos ⟨b, hb⟩
        have ha' : 0 < height (D.datum.root a) := hpos ⟨a, ha⟩
        omega
      obtain ⟨hp, hpn⟩ := ih _ hm b hb rfl
      refine ⟨?_, ?_⟩
      · have h := hreflect i b hp
        rwa [show D.datum.reflectionPerm i b = a from D.datum.reflectionPerm_self i a] at h
      · have h := hreflect i (-b) hpn
        rwa [hrefneg, show D.datum.reflectionPerm i b = a from D.datum.reflectionPerm_self i a] at h
  intro a
  rcases RootPairing.Base.IsPos.or_neg D.base a with ha | ha
  · exact (hplus a ha).1
  · simpa only [neg_neg] using (hplus (-a) ha).2

open Module in
/-- Each coroot admits an integral character pairing to one. -/
theorem coroot_pairing_eq_one (D : BasedRootDatum.{u})
    (height : D.X →ₗ[ℤ] ℤ) (hpos : ∀ i : Positive D, 0 < height (D.datum.root i))
    (ω : Basis D.base.support ℤ D.X)
    (hω : ∀ j : D.base.support, D.datum.coroot' j (ω j) = 1) :
    ∀ a, ∃ x : D.X, D.datum.coroot' a x = 1 := by
  apply all_roots_of_simple_reflections D height hpos
  · exact fun i => ⟨ω i, hω i⟩
  · rintro i a ⟨x, hx⟩
    refine ⟨(D.datum.reflection i).symm x, ?_⟩
    rw [D.datum.coroot'_reflectionPerm, LinearMap.comp_apply]
    change D.datum.coroot' a (D.datum.reflection i ((D.datum.reflection i).symm x)) = 1
    rw [LinearEquiv.apply_symm_apply, hx]

/-- A coroot diagonal on a family of weights spanning the character lattice
has an integral linear combination of diagonal entries equal to one. -/
theorem exists_coroot_diagonal_test
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : BasedRootDatum.{u})
    (height : D.X →ₗ[ℤ] ℤ) (hpos : ∀ i : Positive D, 0 < height (D.datum.root i))
    (ω : Module.Basis D.base.support ℤ D.X)
    (hω : ∀ j : D.base.support, D.datum.coroot' j (ω j) = 1)
    (w : I → D.X) (hw : Submodule.span ℤ (Set.range w) = ⊤) (a : D.I) :
    ∃ d : I → ℤ, ∑ i, d i * (Matrix.diagonal (fun j => D.datum.coroot' a (w j))) i i = 1 := by
  obtain ⟨x, hx⟩ := coroot_pairing_eq_one D height hpos ω hω a
  have hmem : x ∈ Submodule.span ℤ (Set.range w) := hw ▸ Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  refine ⟨d, ?_⟩
  have h := congrArg (D.datum.coroot' a) hd
  rw [hx] at h
  simpa only [map_sum, map_smul, smul_eq_mul, Matrix.diagonal_apply_eq] using h

end RootReflections

/-- A coroot commutator with an integral diagonal combination equal to one
forces any rational scalar preserving integrality of the root operator to
be an integer. -/
theorem scalar_is_integer_of_commutator_test
    {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (A B C : Matrix I I ℤ) (c : K)
    (hc : (Int.castRingHom K).mapMatrix C = c • (Int.castRingHom K).mapMatrix A)
    (d : I → ℤ) (hd : ∑ i, d i * (A * B - B * A) i i = 1) :
    ∃ z : ℤ, (z : K) = c := by
  let f := Int.castRingHom K
  change f.mapMatrix C = c • f.mapMatrix A at hc
  let z := ∑ i, d i * (C * B - B * C) i i
  have hm : f.mapMatrix (C * B - B * C) = c • f.mapMatrix (A * B - B * A) := by
    simp only [map_sub, map_mul, hc, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  have hZ : (z : K) = ∑ i, (d i : K) * f.mapMatrix (C * B - B * C) i i := by
    dsimp only [z]
    push_cast
    rfl
  refine ⟨z, ?_⟩
  rw [hZ, hm]
  calc
    _ = c * ∑ i, (d i : K) * f.mapMatrix (A * B - B * A) i i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.smul_apply, smul_eq_mul]
      ring
    _ = c := by
      have hcast := congrArg (fun t : ℤ => (t : K)) hd
      push_cast at hcast
      change ∑ i, (d i : K) * f.mapMatrix (A * B - B * A) i i = 1 at hcast
      rw [hcast, mul_one]

section CorootMatrices

open CategoryTheory
open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates IsRootTangent torus dualUnit)
open Specs.RootGroups (AdditiveLine)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralLattices
open InfinitesimalCommutator (matrixDifferential)
open private matrixDifferential_bracket from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}} {Q : Realization D A}
  {z : RootCoordinates Q}

private theorem eval_eps_snd {K : Type u} [CommRing K] (p : Polynomial K) :
    (p.eval₂ (algebraMap K (DualNumber K)) DualNumber.eps).snd = p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add, TrivSqZeroExt.snd_add, Polynomial.coeff_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, Polynomial.coeff_monomial]
    rcases n with _ | n
    · simp [TrivSqZeroExt.algebraMap_eq_inl]
    · rcases n with _ | n
      · simp only [pow_one, DualNumber.snd_mul, TrivSqZeroExt.algebraMap_eq_inl,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.fst_eps, DualNumber.snd_eps,
          mul_one, mul_zero, zero_add, add_zero, ite_true]
      · have hn : (DualNumber.eps : DualNumber K) ^ (n + 2) = 0 :=
          pow_eq_zero_of_le (show 2 ≤ n + 2 by omega) DualNumber.eps_pow_two
        change ((algebraMap K (DualNumber K) a) * (DualNumber.eps : DualNumber K) ^ (n + 2)).snd = _
        rw [hn, mul_zero, TrivSqZeroExt.snd_zero]
        simp

private theorem dual_unit_zpow_snd (n : ℤ) :
    ((Specs.IntegralRootRelations.dualUnit.{u}) ^ n).val.snd = (n : Specs.RationalRealization.RationalField.{u}) := by
  let K := Specs.RationalRealization.RationalField.{u}
  let U := Specs.IntegralRootRelations.dualUnit.{u}
  have hU : (U : DualNumber K) = 1 + DualNumber.eps := IsUnit.unit_spec _
  have hU' : (↑U⁻¹ : DualNumber K) = 1 - DualNumber.eps := by
    have hg : (1 - DualNumber.eps : DualNumber K) * (U : DualNumber K) = 1 := by
      rw [hU, sub_mul, one_mul, mul_add, mul_one, DualNumber.eps_mul_eps, add_zero,
        add_sub_cancel_right]
    have eq := congrArg (fun a : DualNumber K => a * (↑U⁻¹ : DualNumber K)) hg
    simpa only [mul_assoc, Units.mul_inv, mul_one, one_mul] using eq.symm
  have hpow (v : (DualNumber K)ˣ) (hf : v.val.fst = 1) (m : ℕ) :
      (v ^ m).val.fst = 1 ∧ (v ^ m).val.snd = (m : K) * v.val.snd := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ, Units.val_mul]
      constructor
      · simp only [TrivSqZeroExt.fst_mul, ih.1, hf, mul_one]
      · rw [DualNumber.snd_mul, ih.1, ih.2, hf]
        rw [Nat.cast_succ]
        ring
  cases n with
  | ofNat m =>
    change (U ^ (m : ℤ)).val.snd = _
    rw [zpow_natCast, (hpow U (by rw [hU]; simp) m).2]
    rw [hU]
    simp
  | negSucc m =>
    change (U ^ (Int.negSucc m)).val.snd = _
    have hm : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by omega
    rw [hm, zpow_neg, zpow_natCast, ← inv_pow, (hpow U⁻¹ (by rw [hU']; simp) (m + 1)).2]
    rw [hU']
    simp
    rw [Nat.cast_succ]
    ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- In a rational highest-weight action the opposite root commutator
is the diagonal action of the marked coroot. -/
theorem coroot_matrix_commutator (s : IdentityLieStructure Q.pinned.pair.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val) (lam : D.X)
      (V : RationalHighestWeight z e h lam) (a b : D.I),
      IsRootTangent Q z a (e a) → IsRootTangent Q z b (e b) →
      (h a).toMul.val = torus Q (D.datum.coroot a)
        (CommAlgCat.of _ (DualNumber RationalField.{u})) dualUnit →
      ⁅e a, e b⁆ = h a →
      V.rootOperator a * V.rootOperator b - V.rootOperator b * V.rootOperator a =
        Matrix.diagonal (fun j => (D.datum.coroot' a (V.weight j) : RationalField.{u})) := by
  classical
  let := s.lieRing
  let := s.lieAlgebra
  intro e h lam V a b ha hb ht hbr
  let K := RationalField.{u}
  let I := Index.{u} V.dimension
  let R := CommAlgCat.of K (DualNumber K)
  let M := StandardGroups.generalLinearGroup K I
  let η := StandardGroups.generalLinearGroupPointsIso K I
  let A := groupHomEquiv Q.pinned.pair.G.val M.val Q.pinned.pair.G.property.1
  let f := A.symm (V.action ≫ η.inv)
  have hη : (groupPointsFunctor K).map f ≫ η.hom = V.action := by
    change A f ≫ η.hom = V.action
    rw [show A f = V.action ≫ η.inv from A.apply_symm_apply _,
      Category.assoc, η.inv_hom_id, Category.comp_id]
  have hinf (p : Lie K Q.pinned.pair.G.val) (i j : I) :
      matrixDifferential f η p i j =
        (((V.action.app R).hom p.toMul.val).val i j).snd := by
    exact congrArg
      (fun ξ : _ ⟶ _ => (((ξ.app R).hom p.toMul.val :
          Matrix.GeneralLinearGroup I (DualNumber K)).val i j).snd) hη
  have hroot (x : D.I) (hx : IsRootTangent Q z x (e x)) :
      matrixDifferential f η (e x) = V.rootOperator x := by
    apply Matrix.ext
    intro i j
    rw [hinf, hx]
    change ((V.action.app R (Specs.IntegralRootRelations.root Q z x R DualNumber.eps) :
      Matrix.GeneralLinearGroup I (DualNumber K)).val i j).snd = _
    rw [V.root_action]
    let P := exponentialPolynomial (V.rootOperator x) V.nilpotenceBound
    change ((P i j).eval₂ (algebraMap K (DualNumber K)) DualNumber.eps).snd = _
    rw [eval_eps_snd]
    have hpow : V.rootOperator x ^ V.nilpotenceBound = 0 := V.nilpotent x
    exact (exponentialPolynomial_coeff (V.rootOperator x) hpow 1 i j).trans
      (congrArg (fun M : Matrix I I K => M i j) (dividedPower_one (V.rootOperator x)))
  have htorus : matrixDifferential f η (h a) =
      Matrix.diagonal (fun j => (D.datum.coroot' a (V.weight j) : K)) := by
    apply Matrix.ext
    intro i j
    rw [hinf, ht]
    let y := D.datum.coroot a
    let t := CocharacterDynamics.cocharacterPoint (markedCocharacter Q y) R dualUnit
    change ((V.action.app R (t ≫ Q.pinned.pair.T.inclusion.hom.hom) :
      Matrix.GeneralLinearGroup I (DualNumber K)).val i j).snd = _
    rw [V.torus_action R t]
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      change (Specs.CharacterPairing.characterValue (markedCharacter Q (V.weight i)) R t).snd = _
      rw [(RootData.CharacterPairing.characterPairingComposition _ _ _).2,
        markedCharacter_pairing, dual_unit_zpow_snd]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, TrivSqZeroExt.snd_zero]
  have he := matrixDifferential_bracket f η s.commutator_law (e a) (e b)
  rw [hbr, htorus, hroot a ha, hroot b hb] at he
  exact he.symm

end

end CorootMatrices

/-- An integral matrix conjugation that carries one primitive root line to
another rescales the chosen root operator by an integer unit. -/
theorem matrix_conjugation_unit_of_commutator_tests
    {I K : Type*} [Fintype I] [DecidableEq I] [Field K] [CharZero K]
    (P Q E F E' F' : Matrix I I ℤ) (hQP : Q * P = 1)
    (c : K) (hc : c ≠ 0)
    (hconj : (Int.castRingHom K).mapMatrix (P * E * Q) =
      c • (Int.castRingHom K).mapMatrix F)
    (dE dF : I → ℤ)
    (hE : ∑ i, dE i * (E * E' - E' * E) i i = 1)
    (hF : ∑ i, dF i * (F * F' - F' * F) i i = 1) :
    ∃ a : ℤˣ, F * P = (a : ℤ) • (P * E) := by
  let f := Int.castRingHom K
  change f.mapMatrix (P * E * Q) = c • f.mapMatrix F at hconj
  have h1 : Q * (P * E * Q) * P = E := by
    calc
      _ = (Q * P) * E * (Q * P) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  have h2 : f.mapMatrix E = c • f.mapMatrix (Q * F * P) := by
    rw [← h1, map_mul, map_mul, hconj, Matrix.mul_smul, Matrix.smul_mul]
    simp only [map_mul]
  have hrev : f.mapMatrix (Q * F * P) = c⁻¹ • f.mapMatrix E := by
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨a, ha⟩ := scalar_is_integer_of_commutator_test F F' (P * E * Q) c hconj dF hF
  obtain ⟨b, hb⟩ := scalar_is_integer_of_commutator_test E E' (Q * F * P) c⁻¹ hrev dE hE
  have hu : b * a = 1 := by
    apply Int.cast_injective (α := K)
    push_cast
    rw [hb, ha, inv_mul_cancel₀ hc]
  let u : ℤˣ := ⟨b, a, hu, by rwa [mul_comm]⟩
  refine ⟨u, ?_⟩
  change F * P = b • (P * E)
  apply Matrix.map_injective (f := f) Int.cast_injective
  change f.mapMatrix (F * P) = f.mapMatrix (b • (P * E))
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul K, hb]
  have h3 : (P * E * Q) * P = P * E := by
    rw [Matrix.mul_assoc, hQP, Matrix.mul_one]
  conv_rhs =>
    rw [← h3, map_mul, hconj, Matrix.smul_mul, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  exact map_mul f.mapMatrix F P

section IntegralCorootMatrices

open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralLattices
open Module

noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {ω : D.base.support → D.X}

/-- The rational coroot commutator descends to the integral matrices in
the homogeneous lattice basis. -/
theorem integral_coroot_matrix
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ} (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (w : Index.{u} n → D.X) (hw : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ a m j i, ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
      (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    (a a' : D.I)
    (hcomm : ∀ i : D.base.support,
      (V i).rootOperator a * (V i).rootOperator a' - (V i).rootOperator a' * (V i).rootOperator a =
        Matrix.diagonal (fun j => (D.datum.coroot' a ((V i).weight j) : RationalField.{u}))) :
    coefficientMatrix (p a) 1 * coefficientMatrix (p a') 1 -
      coefficientMatrix (p a') 1 * coefficientMatrix (p a) 1 =
      Matrix.diagonal (fun j => D.datum.coroot' a (w j)) := by
  classical
  let K := RationalField.{u}
  let : CharZero K :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv.symm : ℚ ≃+* K).toRingHom)
      (ULift.ringEquiv.symm : ℚ ≃+* K).injective
  let F (r : D.I) : Module.End K ((i : D.base.support) → (V i).space) :=
    LinearMap.pi (fun i => ((V i).rootOperator r).mulVecLin.comp (LinearMap.proj i))
  let I := Index.{u} n
  let cast := (Int.castRingHom K).mapMatrix (m := I)
  let M := LinearMap.toMatrixAlgEquiv b
  have hx (r : D.I) (j : I) :
      F r (b j) = ∑ l : I, ((p r l j).coeff 1 : K) • b l := by
    funext i
    simpa only [F, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Matrix.mulVecLin_apply, Finset.sum_apply, Pi.smul_apply, dividedPower_one]
      using (hp r 1 j i).symm
  have hmat (r : D.I) : M (F r) = cast (coefficientMatrix (p r) 1) := by
    apply Matrix.ext
    intro l j
    rw [show M (F r) l j = b.coord l (F r (b j)) from
      LinearMap.toMatrixAlgEquiv_apply b (F r) l j]
    change b.coord l (F r (b j)) = ((p r l j).coeff 1 : K)
    rw [hx, ← b.equivFun_symm_apply, Basis.coord_equivFun_symm]
  let N := F a * F a' - F a' * F a
  have hNv (j : I) : N (b j) = (D.datum.coroot' a (w j) : K) • b j := by
    funext i k
    let E := (V i).rootOperator a
    let E' := (V i).rootOperator a'
    change (E.mulVec (E'.mulVec (b j i))) k - (E'.mulVec (E.mulVec (b j i))) k =
      (D.datum.coroot' a (w j) : K) * b j i k
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Pi.sub_apply, ← Matrix.sub_mulVec,
      show E * E' - E' * E = _ from hcomm i, Matrix.mulVec_diagonal]
    by_cases hk : (V i).weight k = w j
    · rw [hk]
    · simp only [hw j i k hk, mul_zero]
  have hN : M N = cast (Matrix.diagonal (fun j => D.datum.coroot' a (w j))) := by
    apply Matrix.ext
    intro l j
    rw [show M N l j = b.coord l (N (b j)) from LinearMap.toMatrixAlgEquiv_apply b N l j]
    rw [hNv, map_smul, Basis.coord_apply, Basis.repr_self_apply]
    by_cases hl : l = j
    · subst l
      simp [cast]
    · simp [cast, hl, Ne.symm hl]
  apply Matrix.map_injective (f := Int.castRingHom K) Int.cast_injective
  change cast _ = cast _
  rw [map_sub, map_mul, map_mul, ← hmat, ← hmat, ← map_mul, ← map_mul, ← map_sub]
  exact hN

end

end IntegralCorootMatrices

section RootCoefficientTransport

open Specs.IntegralLattices
open scoped Classical

noncomputable section

private theorem mulVec_supported_on_weight {n : ℕ} {X : Type u}
    (w : Index.{u} n → X) (σ : X → X)
    (P : Matrix (Index.{u} n) (Index.{u} n) ℤ)
    (hP : ∀ i j, w i ≠ σ (w j) → P i j = 0)
    {μ : X} {v : Index.{u} n → ℤ} (hv : ∀ j, w j ≠ μ → v j = 0) :
    ∀ i, w i ≠ σ μ → P.mulVec v i = 0 := by
  intro i hi
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : w j = μ
  · rw [hP i j (by rwa [hj]), zero_mul]
  · rw [hv j hj, mul_zero]

/-- Conjugation by an integral change of basis that permutes the weights
carries a homogeneous unit coefficient to the reflected root. -/
theorem unit_coefficient_of_weight_conjugation {n : ℕ} {X : Type u} [AddCommGroup X]
    (w : Index.{u} n → X) (σ : X ≃ₗ[ℤ] X)
    (P Q E F : Matrix (Index.{u} n) (Index.{u} n) ℤ)
    (hinv : Q * P = 1)
    (hP : ∀ i j, w i ≠ σ (w j) → P i j = 0)
    (hQ : ∀ i j, w i ≠ σ.symm (w j) → Q i j = 0)
    (c : ℤˣ) (hF : F * P = (c : ℤ) • (P * E)) (root : X)
    (μ : X) (v : Index.{u} n → ℤ) (φ : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ)
    (hv : ∀ j, w j ≠ μ → v j = 0)
    (hφ : ∀ j, w j ≠ μ + root → φ (Pi.single j 1) = 0)
    (hunit : φ (E.mulVec v) = 1) :
    ∃ (ν : X) (v' : Index.{u} n → ℤ) (ψ : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ),
      (∀ j, w j ≠ ν → v' j = 0) ∧
      (∀ j, w j ≠ ν + σ root → ψ (Pi.single j 1) = 0) ∧
      ψ (F.mulVec v') = 1 := by
  let ψ := (↑c⁻¹ : ℤ) • (φ.comp Q.mulVecLin)
  refine ⟨σ μ, P.mulVec v, ψ, mulVec_supported_on_weight w σ P hP hv, ?_, ?_⟩
  · intro j hj
    have hj' : σ.symm (w j) ≠ μ + root := by
      intro he
      apply hj
      have h := congrArg σ he
      rwa [σ.apply_symm_apply, map_add] at h
    have hu : ∀ k, w k ≠ w j → (Pi.single (M := fun _ => ℤ) j 1) k = 0 :=
      fun k hk => Pi.single_eq_of_ne (fun he => hk (congrArg w he)) _
    have hqu := mulVec_supported_on_weight w σ.symm Q hQ hu
    change (↑c⁻¹ : ℤ) * φ (Q.mulVec (Pi.single j 1)) = 0
    rw [linearMap_pi_apply_eq_sum φ]
    suffices hsum : ∑ i, φ (Pi.single i 1) * Q.mulVec (Pi.single j 1) i = 0 by
      rw [hsum, mul_zero]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : w k = σ.symm (w j)
    · rw [hφ k (hk ▸ hj'), zero_mul]
    · rw [hqu k hk, mul_zero]
  · change (↑c⁻¹ : ℤ) * φ (Q.mulVec (F.mulVec (P.mulVec v))) = 1
    rw [show F.mulVec (P.mulVec v) = (F * P).mulVec v from Matrix.mulVec_mulVec _ _ _,
      hF, Matrix.smul_mulVec]
    have hq : Q.mulVec ((↑c : ℤ) • (P * E).mulVec v) = (↑c : ℤ) • E.mulVec v := by
      change Q.mulVecLin ((↑c : ℤ) • (P * E).mulVec v) = _
      rw [map_smul, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        hinv, Matrix.one_mul]
    rw [hq, map_smul, hunit, smul_eq_mul, mul_one, Units.inv_mul]

end

end RootCoefficientTransport

section RationalRootImages

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Classical
open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates root rootIndex)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.OrderedRootProducts (Enumerates product rootProduct)
open Specs.BorelsAndChambers (positiveRoots)
open Specs.AdjointRepresentation (GroupPoints)
open private rootPoint_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open Specs.IntegralLattices
open Module

noncomputable section

set_option backward.isDefEq.respectTransparency false


variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}} {Q : Realization D A}

private abbrev markedRootIndex (Q : Realization D A) (a : D.I) :
    Specs.AbstractPairing.Root Q.pinned.pair.T := rootIndex Q a

private def rootProductPoint (z : RootCoordinates Q) (R : TestAlgebra RationalField.{u})
    {S : Set D.I} (x : S → R) (l : List S) :
    Points (product (fun α => (Q.pinned.roots α).val.group.X) (l.map (fun a => markedRootIndex Q a.val))) R :=
  match l with
  | [] => toUnit _
  | a :: l => lift (rootPoint (z a.val).val.hom R (x a)) (rootProductPoint z R x l)

private theorem rootProductPoint_congr (z : RootCoordinates Q) (R : TestAlgebra RationalField.{u})
    {S : Set D.I} (x y : S → R) (l : List S) (h : ∀ a ∈ l, x a = y a) :
    rootProductPoint z R x l = rootProductPoint z R y l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [rootProductPoint, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

private theorem rootProductPoint_surjective (z : RootCoordinates Q) (R : TestAlgebra RationalField.{u})
    {S : Set D.I} (l : List S) (hl : l.Nodup) :
    Function.Surjective (fun x => rootProductPoint z R x l) := by
  classical
  induction l with
  | nil => exact fun p => ⟨0, toUnit_unique _ _⟩
  | cons a l ih =>
    intro p
    obtain ⟨x, hx⟩ := rootPoint_surjective (z a.val).val R (p ≫ fst _ _)
    obtain ⟨y, hy⟩ := ih hl.of_cons (p ≫ snd _ _)
    refine ⟨Function.update y a x, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · change lift (rootPoint (z a.val).val.hom R (Function.update y a x a))
          (rootProductPoint z R (Function.update y a x) l) ≫ fst _ _ = p ≫ fst _ _
      rw [lift_fst, Function.update_self]
      exact hx
    · change lift (rootPoint (z a.val).val.hom R (Function.update y a x a))
          (rootProductPoint z R (Function.update y a x) l) ≫ snd _ _ = p ≫ snd _ _
      rw [lift_snd, ← hy]
      apply rootProductPoint_congr
      intro b hb
      have hba : b ≠ a := fun h => hl.notMem (h ▸ hb)
      exact Function.update_of_ne hba x y

private theorem rootProductPoint_mul (z : RootCoordinates Q) (R : TestAlgebra RationalField.{u})
    {S : Set D.I} (l : List S) (x : S → R) :
    rootProductPoint z R x l ≫
      rootProduct Q.pinned.roots (l.map (fun a => markedRootIndex Q a.val)) =
      (l.map (fun a => root Q z a.val R (x a))).prod := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons a l ih =>
    change lift (rootPoint (z a.val).val.hom R (x a)) (rootProductPoint z R x l) ≫
        ((fst _ _ ≫ (Q.pinned.roots (markedRootIndex Q a.val)).val.inclusion.hom.hom) *
          (snd _ _ ≫ rootProduct Q.pinned.roots (l.map (fun a => markedRootIndex Q a.val)))) =
        root Q z a.val R (x a) * _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ih]
    rfl

/-- The marked ordered product over any rational test algebra is the image of
the contracting subgroup under its inclusion. -/
private theorem rootProductPoint_subgroup (z : RootCoordinates Q)
    {S : Set D.I} (y : D.Y) (hS : ∀ a, a ∈ S ↔ 0 < D.datum.toLinearMap (D.datum.root a) y)
    (l : List S) (hl : Enumerates l Set.univ) (R : TestAlgebra RationalField.{u}) :
    ∃ H : Subgroup (GroupPoints Q.pinned.pair.G.val R),
      Set.range (fun x : S → R => (l.map (fun a => root Q z a.val R (x a))).prod) = H := by
  let P := Q.pinned.pair
  let c := markedCocharacter Q y
  let f : S → Specs.AbstractPairing.Root P.T := fun a => markedRootIndex Q a.val
  have hf : Function.Injective f := fun a b hab => Subtype.ext (Q.datumIso.val.indexEquiv.injective hab)
  have hl' : Enumerates (l.map f) (positiveRoots P.T c) := by
    refine ⟨hl.1.map hf, ?_⟩
    intro α
    obtain ⟨a, rfl⟩ := Q.datumIso.val.indexEquiv.surjective α
    change _ ↔ 0 < Specs.CharacterPairing.pairing _ (markedRootIndex Q a).val c
    rw [← markedCharacter_root Q a, markedCharacter_pairing]
    constructor
    · intro hm
      obtain ⟨b, _, hb⟩ := List.mem_map.mp hm
      exact (hS a).mp (Q.datumIso.val.indexEquiv.injective hb ▸ b.property)
    · intro ha
      let b : S := ⟨a, (hS a).mpr ha⟩
      exact List.mem_map.mpr ⟨b, (hl.2 b).mpr (Set.mem_univ _), rfl⟩
  obtain ⟨hC, hparam⟩ :=
    (RootData.OrderedRootProducts.contractingProduct P.G P.reductive P.T P.split P.maximal).2.2 c
  obtain ⟨C⟩ := hC
  obtain ⟨g, hg⟩ := hparam C Q.pinned.roots (l.map f) hl'
  let i : GroupPoints C.contracting.group R →* GroupPoints P.G.val R :=
    (((groupPointsFunctor RationalField.{u}).map C.contracting.inclusion).app R).hom
  refine ⟨i.range, ?_⟩
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨rootProductPoint z R x l ≫ g.hom, ?_⟩
    change (rootProductPoint z R x l ≫ g.hom) ≫ C.contracting.inclusion.hom.hom = _
    rw [Category.assoc, hg, rootProductPoint_mul]
  · rintro ⟨p, rfl⟩
    obtain ⟨x, hx⟩ := rootProductPoint_surjective z R l hl.1 (p ≫ g.inv)
    refine ⟨x, ?_⟩
    change (l.map (fun a => root Q z a.val R (x a))).prod =
      p ≫ C.contracting.inclusion.hom.hom
    change rootProductPoint z R x l = p ≫ g.inv at hx
    rw [← rootProductPoint_mul z R l x, hx, ← hg, Category.assoc, g.inv_hom_id_assoc]

private theorem blockDiagonal'_map {I₀ : Type*} {κ : I₀ → Type*} [DecidableEq I₀]
    {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (A : ∀ i : I₀, Matrix (κ i) (κ i) R) :
    (Matrix.blockDiagonal' A).map f = Matrix.blockDiagonal' (fun i => (A i).map f) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rcases eq_or_ne i k with rfl | h
  · simp
  · rw [Matrix.map_apply, Matrix.blockDiagonal'_apply_ne _ _ _ h,
      Matrix.blockDiagonal'_apply_ne _ _ _ h, map_zero]

private def conjugateRectangular {I J R : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Semiring R]
    (C : Matrix I J R) (E : Matrix J I R)
    (he : E * C = 1) (hc : C * E = 1) : Matrix I I R →+* Matrix J J R where
  toFun M := E * M * C
  map_zero' := by simp
  map_one' := by simpa using he
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' M N := by
    symm
    calc
      (E * M * C) * (E * N * C) = E * M * (C * E) * N * C := by simp only [Matrix.mul_assoc]
      _ = _ := by simp [hc, Matrix.mul_assoc]

variable [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)] [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {ω : D.base.support → D.X}

private def combinedAction (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    (R : TestAlgebra RationalField.{u}) :
    GroupPoints Q.pinned.pair.G.val R →*
      Matrix.GeneralLinearGroup (Σ i : D.base.support, Index.{u} (V i).dimension) R :=
  (Units.map (Matrix.blockDiagonal'RingHom (fun i => Index.{u} (V i).dimension) R).toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun i : D.base.support =>
        Matrix (Index.{u} (V i).dimension) (Index.{u} (V i).dimension) R)).symm.toMonoidHom.comp
      (MonoidHom.pi fun i => ((V i).action.app R).hom))

private theorem combinedAction_val (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    (R : TestAlgebra RationalField.{u}) (g : GroupPoints Q.pinned.pair.G.val R) :
    (combinedAction V R g).val = Matrix.blockDiagonal' (fun i => ((V i).action.app R g).val) := rfl

/-- The chosen lattice basis conjugates the ordered polynomial matrices to the
direct sum of the rational actions. This identifies the rational image with
the image of a contracting subgroup on every rational test algebra. -/
theorem orderedMatrix_rational_subgroup
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ} (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ a m j i, ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
      (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    {S : Set D.I} (y : D.Y) (hS : ∀ a, a ∈ S ↔ 0 < D.datum.toLinearMap (D.datum.root a) y)
    (l : List S) (hl : Enumerates l Set.univ)
    (R : Type u) [CommRing R] [Algebra RationalField.{u} R] :
    ∃ f : (S → R) → Matrix.GeneralLinearGroup (Index.{u} n) R,
      (∀ x, (f x).val = (MvPolynomial.eval₂Hom (Int.castRingHom R) x).mapMatrix
        (orderedMatrix l (fun a => p a.val))) ∧
      ∃ H : Subgroup (Matrix.GeneralLinearGroup (Index.{u} n) R), Set.range f = H := by
  classical
  let J := Σ i : D.base.support, Index.{u} (V i).dimension
  let c : Basis J RationalField.{u} ((i : D.base.support) → (V i).space) :=
    (Pi.basisFun RationalField.{u} J).map (LinearEquiv.piCurry RationalField.{u} (fun _ _ => RationalField.{u}))
  let C := c.toMatrix b
  let E := b.toMatrix c
  have hC (i : D.base.support) (k : Index.{u} (V i).dimension) (j : Index.{u} n) :
      C ⟨i, k⟩ j = b j i k := by
    simp [C, c, Basis.toMatrix_apply]; rfl
  let R' : TestAlgebra RationalField.{u} := CommAlgCat.of RationalField.{u} R
  let C' := C.map (algebraMap RationalField.{u} R)
  let E' := E.map (algebraMap RationalField.{u} R)
  have he : E' * C' = 1 := by
    rw [← Matrix.map_mul]
    simp [E, C]
  have hc : C' * E' = 1 := by
    rw [← Matrix.map_mul]
    simp [E, C]
  let χ := conjugateRectangular C' E' he hc
  let ρ := (Units.map χ.toMonoidHom).comp (combinedAction V R')
  have hroot (a : D.I) (t : R) :
      (ρ (root Q z a R' t)).val = (Polynomial.eval₂RingHom (Int.castRingHom R) t).mapMatrix (p a) := by
    let τ (i : D.base.support) :=
      exponentialPolynomial ((V i).rootOperator a) (V i).nilpotenceBound
    let B := Matrix.blockDiagonal' τ
    let P := (Polynomial.mapRingHom (Int.castRingHom RationalField.{u})).mapMatrix (p a)
    have hP : B * C.map (Polynomial.C : RationalField.{u} →+* Polynomial RationalField.{u}) =
        C.map (Polynomial.C : RationalField.{u} →+* Polynomial RationalField.{u}) * P := by
      apply Matrix.ext
      rintro ⟨i, k⟩ j
      apply Polynomial.ext
      intro m
      simp only [Matrix.mul_apply, Polynomial.finsetSum_coeff, Matrix.map_apply,
        Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, RingHom.mapMatrix_apply,
        Polynomial.coeff_map, hC, P, Polynomial.coe_mapRingHom]
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.sum_eq_single i]
      · simp only [B, Matrix.blockDiagonal'_apply_eq, τ,
          exponentialPolynomial_coeff ((V i).rootOperator a) ((V i).nilpotent a) m]
        change (∑ x, dividedPower ((V i).rootOperator a) m k x * b j i x) =
          ∑ x, b x i k * ((p a x j).coeff m : RationalField.{u})
        simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
          using (congrFun (hp a m j i) k).symm
      · intro a _ ha
        apply Finset.sum_eq_zero
        intro l _
        simp [B, Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm ha), Polynomial.coeff_zero]
      · simp
    let ev : Polynomial RationalField.{u} →+* R := Polynomial.eval₂RingHom (algebraMap RationalField.{u} R) t
    have hPC : (C.map (Polynomial.C : RationalField.{u} →+* Polynomial RationalField.{u})).map ev = C' := by
      ext i j
      exact RingHom.congr_fun (Polynomial.eval₂RingHom_comp_C _ _) (C i j)
    have hEval : ev.comp (Polynomial.mapRingHom (Int.castRingHom RationalField.{u})) =
        Polynomial.eval₂RingHom (Int.castRingHom R) t := by
      apply Polynomial.ringHom_ext
      · intro r
        simp [ev]
      · simp [ev]
    have hAct : (combinedAction V R' (root Q z a R' t)).val = B.map ev := by
      rw [combinedAction_val, blockDiagonal'_map]
      congr 1
      funext i
      exact (V i).root_action a R' t
    have hM := congrArg (fun M : Matrix J (Index.{u} n) (Polynomial RationalField.{u}) => M.map ev) hP
    rw [Matrix.map_mul, Matrix.map_mul, hPC, ← hAct] at hM
    change E' * (combinedAction V R' (root Q z a R' t)).val * C' = _
    rw [Matrix.mul_assoc, hM, ← Matrix.mul_assoc, he, Matrix.one_mul]
    ext i j
    exact RingHom.congr_fun hEval (p a i j)
  obtain ⟨H, hH⟩ := rootProductPoint_subgroup z y hS l hl R'
  let f (x : S → R) := ρ ((l.map (fun a => root Q z a.val R' (x a))).prod)
  refine ⟨f, ?_, H.map ρ, ?_⟩
  · intro x
    let ev := (MvPolynomial.eval₂Hom (Int.castRingHom R) x)
    change (Units.coeHom _) (ρ ((l.map (fun a => root Q z a.val R' (x a))).prod)) =
      ev.mapMatrix ((l.map fun a =>
        (Polynomial.aeval (MvPolynomial.X a)).toRingHom.mapMatrix (p a.val)).prod)
    simp only [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    change (ρ (root Q z a.val R' (x a))).val =
      ev.mapMatrix ((Polynomial.aeval (MvPolynomial.X a)).toRingHom.mapMatrix (p a.val))
    rw [hroot]
    have hp' : ev.comp (Polynomial.aeval (MvPolynomial.X a)).toRingHom =
        Polynomial.eval₂RingHom (Int.castRingHom R) (x a) := by
      apply Polynomial.ringHom_ext
      · intro r
        simp [ev]
      · simp [ev]
    ext i j
    exact (RingHom.congr_fun hp' (p a.val i j)).symm
  · change Set.range (ρ ∘ (fun x : S → R =>
      (l.map (fun a => root Q z a.val R' (x a))).prod)) = _
    rw [Set.range_comp, hH, Subgroup.coe_map]

end

end RationalRootImages

section ClosedRootImages

open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (Enumerates)
open Specs.IntegralLattices
open Module

noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {ω : D.base.support → D.X}

/-- The homogeneous unit coefficient tests give the closed subgroup images
of both ordered root products, over every commutative ring. -/
theorem closedRootImages_of_unit_coefficients
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ} (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (w : Index.{u} n → D.X) (hb : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    (height : D.X →ₗ[ℤ] ℤ) (hw : Antitone (height ∘ w))
    (hpositive : ∀ a : Positive D, 0 < height (D.datum.root a))
    (hnegative : ∀ a : Negative D, height (D.datum.root a) < 0)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ a m j i, ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
      (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    (negative : List (Negative D)) (positive : List (Positive D))
    (hn : Enumerates negative Set.univ) (hpos : Enumerates positive Set.univ)
    (hunit : ∀ a : D.I, ∃ (μ : D.X) (v : Index.{u} n → ℤ)
      (φ : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ),
      (∀ j, w j ≠ μ → v j = 0) ∧
      (∀ j, w j ≠ μ + D.datum.root a → φ (Pi.single j 1) = 0) ∧
      φ ((coefficientMatrix (p a) 1).mulVec v) = 1) :
    ClosedRootImage false (orderedMatrix negative (fun a => p a.val)) ∧
    ClosedRootImage true (orderedMatrix positive (fun a => p a.val)) := by
  let : CharZero (RationalField.{u}) :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
      (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective
  obtain ⟨hzero, hshift⟩ := integralRootPolynomials_support V b w hb p hp
  let χ := D.datum.flip.toPerfPair
  obtain ⟨y, hy⟩ := χ.surjective height
  have hy' (a : D.I) : D.datum.toLinearMap (D.datum.root a) y = height (D.datum.root a) :=
    DFunLike.congr_fun hy _
  have hyneg (a : D.I) : D.datum.toLinearMap (D.datum.root a) (-y) = -(height (D.datum.root a)) := by
    rw [map_neg, hy']
  have hneg (a : D.I) :
      a ∈ ({a | ¬ D.base.IsPos a} : Set D.I) ↔ 0 < D.datum.toLinearMap (D.datum.root a) (-y) := by
    rw [hyneg, neg_pos]
    constructor
    · exact fun h => hnegative ⟨a, h⟩
    · exact fun h hp => (not_lt_of_gt (hpositive ⟨a, hp⟩)) h
  have hpos' (a : D.I) :
      a ∈ ({a | D.base.IsPos a} : Set D.I) ↔ 0 < D.datum.toLinearMap (D.datum.root a) y := by
    rw [hy']
    constructor
    · exact fun h => hpositive ⟨a, h⟩
    · intro h
      by_contra hp
      exact (not_lt_of_gt (hnegative ⟨a, hp⟩)) h
  have htneg := orderedMatrix_unitriangular negative (fun a => D.datum.root a.val) w height hw
    false hnegative (fun a => p a.val) (fun a => hzero a.val) (fun a => hshift a.val)
  have htpos := orderedMatrix_unitriangular positive (fun a => D.datum.root a.val) w height hw
    true hpositive (fun a => p a.val) (fun a => hzero a.val) (fun a => hshift a.val)
  refine ⟨closedRootImage_of_rational (K := RationalField.{u}) false _ htneg ?_ ?_,
    closedRootImage_of_rational (K := RationalField.{u}) true _ htpos ?_ ?_⟩
  · exact orderedMatrix_inverse_coordinates false negative hn
      ((Function.Embedding.subtype _).trans D.datum.root) w (-height)
      (fun a => by
        change 0 < -(height (D.datum.root a.val))
        exact neg_pos.mpr (hnegative a))
      (fun a => p a.val) (fun a => hzero a.val) (fun a => hshift a.val) htneg (fun a => hunit a.val)
  · exact orderedMatrix_rational_subgroup V b p hp (-y) hneg negative hn
  · exact orderedMatrix_inverse_coordinates true positive hpos
      ((Function.Embedding.subtype _).trans D.datum.root) w height hpositive
      (fun a => p a.val) (fun a => hzero a.val) (fun a => hshift a.val) htpos (fun a => hunit a.val)
  · exact orderedMatrix_rational_subgroup V b p hp y hpos' positive hpos

end

end ClosedRootImages

section FundamentalProducts

open _root_.LinearAlgebraicGroups.Specs (Lie)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates FormalBigCellProduct)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (Enumerates)
open Specs.IntegralLattices
open Module
open scoped BigOperators
noncomputable section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q} {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}

/-- The integral lattice construction and the unitriangularity assertion
for the specified rational fundamental highest-weight actions. -/
theorem fundamentalLattices_and_triangularProducts
    (ω : Basis D.base.support ℤ D.X)
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    (collection : FormalBigCellProduct Q z)
    (B : Basis (D.base.support ⊕ D.I) RationalField.{u}
      (Lie RationalField.{u} Q.pinned.pair.G.val))
    (Bh : ∀ i, B (.inl i) = h i) (Be : ∀ a, B (.inr a) = e a)
    (negative : List (Negative D)) (positive : List (Positive D))
    (hn : Enumerates negative Set.univ) (hp : Enumerates positive Set.univ) :
    ∃ (n : ℕ)
      (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
      (w : Index.{u} n → D.X) (height : D.X →ₗ[ℤ] ℤ)
      (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)),
        (∀ i, (V i).IsIntegralLattice negative) ∧
        Submodule.span ℤ (Set.range b) = Submodule.pi Set.univ
          (fun i => (V i).lattice negative) ∧
        (∀ j i, b j i ∈ (V i).weightSpace (w j)) ∧
        Antitone (height ∘ w) ∧
        (∀ a : Positive D, 0 < height (D.datum.root a)) ∧
        (∀ a : Negative D, height (D.datum.root a) < 0) ∧
        TorusCoordinatesGenerate w ∧
        (∀ (a : D.I) (m : ℕ) (j : Index.{u} n) (i : D.base.support),
          ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
            (dividedPower ((V i).rootOperator a) m).mulVec (b j i)) ∧
        (∀ i j, ¬ j < i →
          orderedMatrix negative (fun a => p a.val) i j = (1 : Matrix _ _ _) i j) ∧
        (∀ i j, ¬ i < j →
          orderedMatrix positive (fun a => p a.val) i j = (1 : Matrix _ _ _) i j) := by
  have hV (i : D.base.support) : (V i).IsIntegralLattice negative :=
    isIntegralLattice_of_formalBigCell (V i) collection B Bh Be negative positive hn hp
  obtain ⟨height, d, hd, hheight⟩ := exists_integralHeight D
  have hpos (a : Positive D) : 0 < height (D.datum.root a) := by
    rw [hheight]
    exact mul_pos hd a.property
  have hneg (a : Negative D) : height (D.datum.root a) < 0 := by
    rw [hheight]
    exact mul_neg_of_pos_of_neg hd (lt_of_le_of_ne (not_lt.mp a.property) (D.base.height_ne_zero a))
  obtain ⟨n, b, w, hb, hw, hanti⟩ := exists_orderedFundamentalBasis ω V negative hV height
  obtain ⟨p, hcoeff⟩ := exists_integralRootPolynomials ω V negative hV b hb
  obtain ⟨hzero, hshift⟩ := integralRootPolynomials_support V b w hw p hcoeff
  exact ⟨n, b, w, height, p, hV, hb, hw, hanti, hpos, hneg,
    torusCoordinatesGenerate_of_fundamentalWeightBasis ω V b w hw, hcoeff,
    orderedMatrix_unitriangular negative (fun a => D.datum.root a.val) w height hanti false
      hneg (fun a => p a.val) (fun a => hzero a.val) (fun a => hshift a.val),
    orderedMatrix_unitriangular positive (fun a => D.datum.root a.val) w height hanti true
      hpos (fun a => p a.val) (fun a => hzero a.val) (fun a => hshift a.val)⟩

end

end FundamentalProducts

section WeylTransport

open CategoryTheory

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates IsRootTangent torus dualUnit)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralLattices
open Module
open scoped Matrix Classical

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

local instance rationalFieldCharZero : CharZero (RationalField.{u}) :=
  charZero_of_injective_ringHom
    (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
    (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}}
  {Q : Realization D A} {z : RootCoordinates Q}

local notation "𝔤" => Lie RationalField Q.pinned.pair.G.val

section EnvelopingAction
variable [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {ω : D.base.support → D.X}

local notation "U" => UniversalEnvelopingAlgebra RationalField 𝔤

/-- The direct sum of the given enveloping-algebra actions in a common basis. -/
private def directSumEnvelopingAction
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ} (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space)) :
    U →ₐ[RationalField.{u}] Matrix (Index.{u} n) (Index.{u} n) RationalField.{u} :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp
    { toFun := fun a => LinearMap.pi fun i =>
        ((V i).envelopingAction a).mulVecLin.comp (LinearMap.proj i)
      map_one' := by
        apply LinearMap.ext
        intro v
        funext i
        change ((V i).envelopingAction 1).mulVec (v i) = v i
        rw [map_one, Matrix.one_mulVec]
      map_zero' := by
        apply LinearMap.ext
        intro v
        funext i
        change ((V i).envelopingAction 0).mulVec (v i) = 0
        rw [map_zero, Matrix.zero_mulVec]
      map_add' := by
        intro a c
        apply LinearMap.ext
        intro v
        funext i
        change ((V i).envelopingAction (a + c)).mulVec (v i) =
          ((V i).envelopingAction a).mulVec (v i) + ((V i).envelopingAction c).mulVec (v i)
        rw [map_add, Matrix.add_mulVec]
      map_mul' := by
        intro a c
        apply LinearMap.ext
        intro v
        funext i
        change ((V i).envelopingAction (a * c)).mulVec (v i) =
          ((V i).envelopingAction a).mulVec (((V i).envelopingAction c).mulVec (v i))
        rw [map_mul, Matrix.mulVec_mulVec]
      commutes' := by
        intro t
        apply LinearMap.ext
        intro v
        funext i
        change ((V i).envelopingAction (algebraMap RationalField.{u} U t)).mulVec (v i) = t • v i
        rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
          Matrix.one_mulVec] }

private theorem directSumEnvelopingAction_entry
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ} (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (a : U) (l j : Index.{u} n) :
    directSumEnvelopingAction V b a l j =
      b.coord l (fun i => ((V i).envelopingAction a).mulVec (b j i)) :=
  LinearMap.toMatrixAlgEquiv_apply b _ _ _

private theorem directSumEnvelopingAction_coeff
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    {n : ℕ} (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ a m j i, ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
      (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    (a : D.I) (m : ℕ) :
    (Int.castRingHom RationalField.{u}).mapMatrix (coefficientMatrix (p a) m) =
      dividedPower (directSumEnvelopingAction V b (UniversalEnvelopingAlgebra.ι RationalField.{u} (e a))) m := by
  classical
  let t : U := (m.factorial : RationalField.{u})⁻¹ • UniversalEnvelopingAlgebra.ι RationalField.{u} (e a) ^ m
  have hmap : directSumEnvelopingAction V b t =
      dividedPower (directSumEnvelopingAction V b (UniversalEnvelopingAlgebra.ι RationalField.{u} (e a))) m := by
    simp [t, dividedPower, map_pow]
  rw [← hmap]
  ext l j
  rw [directSumEnvelopingAction_entry V b]
  have hj : (fun i => ((V i).envelopingAction t).mulVec (b j i)) =
      b.equivFun.symm (fun k => ((p a k j).coeff m : RationalField.{u})) := by
    rw [b.equivFun_symm_apply]
    funext i
    simpa only [t, map_smul, map_pow, RationalHighestWeight.rootOperator, dividedPower,
      Finset.sum_apply, Pi.smul_apply] using (hp a m j i).symm
  rw [hj, Basis.coord_equivFun_symm]
  rfl

end EnvelopingAction

/-- Evaluating an integral root polynomial at one or minus one gives
the exponential of the corresponding rational root matrix. -/
private theorem integralRoot_eval_sign {n N : ℕ}
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (E : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u}) (hN : E ^ N = 0)
    (hp : ∀ m, (Int.castRingHom RationalField.{u}).mapMatrix (coefficientMatrix p m) = dividedPower E m)
    (t : ℤ) :
    (Int.castRingHom RationalField.{u}).mapMatrix ((Polynomial.evalRingHom t).mapMatrix p) =
      IsNilpotent.exp ((t : RationalField.{u}) • E) := by
  classical
  have hn : ((t : RationalField.{u}) • E) ^ (N + 1) = 0 := by
    rw [smul_pow, pow_eq_zero_of_le (Nat.le_succ N) hN, smul_zero]
  rw [IsNilpotent.exp_eq_sum hn]
  apply Matrix.ext
  intro i j
  have hcoeff (m : ℕ) : ((p i j).coeff m : RationalField.{u}) = dividedPower E m i j :=
    congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u} => M i j) (hp m)
  have hz (m : ℕ) (hm : N ≤ m) : (p i j).coeff m = 0 := by
    apply Int.cast_injective (α := RationalField.{u})
    rw [hcoeff, dividedPower, pow_eq_zero_of_le hm hN, smul_zero, Matrix.zero_apply, Int.cast_zero]
  change ((Polynomial.eval t (p i j) : ℤ) : RationalField.{u}) = _
  have hdeg : (p i j).natDegree < N + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => hz m hm.le)
  rw [Polynomial.eval_eq_sum_range' hdeg t]
  push_cast
  simp only [Matrix.sum_apply, smul_pow, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [hcoeff, dividedPower, Matrix.smul_apply]
  rw [← IsScalarTower.algebraMap_smul RationalField.{u} ((m.factorial : ℚ)⁻¹) (_ : RationalField.{u})]
  simp only [map_inv₀, map_natCast, smul_eq_mul]
  ring

/-- Inside the span of the diagonal and the root shifts, the matrices of
a given nonzero root weight lie in its root line. -/
private theorem rootLine_of_span {I J X F : Type*}
    [Field F] [AddCommGroup X] [Fintype I] [DecidableEq I] [DecidableEq J]
    (α : I ↪ X) (hα : ∀ r, α r ≠ 0) (w : J → X)
    (δ : Set (Matrix J J F)) (hδ : ∀ M ∈ δ, ∀ i j, i ≠ j → M i j = 0)
    (E : I → Matrix J J F)
    (hE : ∀ r i j, w i ≠ w j + α r → E r i j = 0)
    (r : I) {M : Matrix J J F}
    (hM : M ∈ Submodule.span F (δ ∪ Set.range E))
    (hshift : ∀ i j, w i ≠ w j + α r → M i j = 0) :
    ∃ c : F, M = c • E r := by
  classical
  let cut : Matrix J J F →ₗ[F] Matrix J J F :=
    { toFun := fun B i j => if w i = w j + α r then B i j else 0
      map_add' := by
        intro B C
        ext i j
        change (if w i = w j + α r then B i j + C i j else 0) =
          (if w i = w j + α r then B i j else 0) + (if w i = w j + α r then C i j else 0)
        by_cases h : w i = w j + α r <;> simp [h]
      map_smul' := by
        intro t B
        ext i j
        change (if w i = w j + α r then t * B i j else 0) =
          t * (if w i = w j + α r then B i j else 0)
        by_cases h : w i = w j + α r <;> simp [h] }
  have hm : cut M = M := by
    ext i j
    change (if w i = w j + α r then M i j else 0) = M i j
    by_cases h : w i = w j + α r
    · rw [if_pos h]
    · rw [if_neg h, hshift _ _ h]
  have hle : Submodule.span F (δ ∪ Set.range E) ≤ (F ∙ E r).comap cut := by
    apply Submodule.span_le.mpr
    rintro B (hB | ⟨s, rfl⟩)
    · have hzero : cut B = 0 := by
        ext i j
        change (if w i = w j + α r then B i j else 0) = 0
        split
        · rename_i h
          apply hδ B hB
          intro hij
          apply hα r
          rw [hij] at h
          exact add_left_cancel (h.symm.trans (add_zero _).symm)
        · rfl
      change cut B ∈ F ∙ E r
      rw [hzero]
      exact Submodule.zero_mem _
    · by_cases hs : s = r
      · subst s
        have heq : cut (E r) = E r := by
          ext i j
          change (if w i = w j + α r then E r i j else 0) = E r i j
          split
          · rfl
          · rw [hE _ _ _ (by assumption)]
        change cut (E r) ∈ F ∙ E r
        rw [heq]
        exact Submodule.mem_span_singleton_self _
      · have heq : cut (E s) = 0 := by
          ext i j
          change (if w i = w j + α r then E s i j else 0) = 0
          split
          · rename_i hj
            apply hE
            intro he
            exact hs (α.injective (add_left_cancel (he.symm.trans hj)))
          · rfl
        change cut (E s) ∈ F ∙ E r
        rw [heq]
        exact Submodule.zero_mem _
  have h := hle hM
  change cut M ∈ F ∙ E r at h
  rw [hm, Submodule.mem_span_singleton] at h
  exact h.imp fun c hc => hc.symm

private theorem reflected_weight_of_diagonal_intertwining
    (ω : Basis D.base.support ℤ D.X)
    (hω : ∀ i j : D.base.support, D.datum.coroot' j (ω i) = if j = i then 1 else 0)
    {n : ℕ} (w : Index.{u} n → D.X) (s : D.I)
    (P : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u}) (γ : Bool)
    (hP : ∀ j : D.base.support,
      P * Matrix.diagonal (fun i =>
        (D.datum.coroot' j (if γ then D.datum.reflection s (w i) else w i) : RationalField.{u})) =
      Matrix.diagonal (fun i =>
        (D.datum.coroot' j (if γ then w i else D.datum.reflection s (w i)) : RationalField.{u})) * P) :
    ∀ i j, w i ≠ D.datum.reflection s (w j) → P i j = 0 := by
  classical
  have hsep {x y : D.X} (hxy : ∀ j : D.base.support,
      D.datum.coroot' j x = D.datum.coroot' j y) : x = y := by
    have hCoord (j : D.base.support) : D.datum.coroot' j = ω.coord j := by
      apply ω.ext
      intro i
      rw [hω, Basis.coord_apply, Basis.repr_self_apply]
      by_cases h : j = i <;> simp [h, eq_comm]
    apply ω.repr.injective
    ext j
    simpa only [hCoord, Basis.coord_apply] using hxy j
  intro i j hij
  by_contra hp
  have h (l : D.base.support) :
      D.datum.coroot' l (if γ then w i else D.datum.reflection s (w i)) =
      D.datum.coroot' l (if γ then D.datum.reflection s (w j) else w j) := by
    have hl := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u} => M i j) (hP l)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm (P i j)] at hl
    exact Int.cast_injective (α := RationalField.{u}) (mul_right_cancel₀ hp hl.symm)
  cases γ
  · have he : D.datum.reflection s (w i) = w j := hsep h
    exact hij (by rw [← he, D.datum.reflection_same])
  · exact hij (hsep h)

private theorem reflected_root_support {n : ℕ} (w : Index.{u} n → D.X)
    (σ : D.X ≃ₗ[ℤ] D.X) (hσ : Function.Involutive σ)
    (P E Q : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u}) (α : D.X)
    (hP : ∀ i j, w i ≠ σ (w j) → P i j = 0)
    (hQ : ∀ i j, w i ≠ σ (w j) → Q i j = 0)
    (hE : ∀ i j, w i ≠ w j + α → E i j = 0) :
    ∀ i j, w i ≠ w j + σ α → (P * E * Q) i j = 0 := by
  classical
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : w k = σ (w j)
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro l _
    by_cases hl : w i = σ (w l)
    · rw [hE l k, mul_zero]
      intro h
      apply hij
      rw [hl, h, map_add, hk, hσ]
    · rw [hP i l hl, zero_mul]
  · rw [hQ k j hk, mul_zero]
open _root_.LinearAlgebraicGroups.RationalRealization (rankOneWordReflection)
open private innerExp innerExp_apply exponentialConjugationMem
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
/-- Transport the simple-root unit coefficients through the integral rank-one
words on the fundamental lattices. -/
theorem root_unit_coefficients (s : IdentityLieStructure Q.pinned.pair.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (e h : D.I → 𝔤)
      (B : Basis (D.base.support ⊕ D.I) RationalField.{u} 𝔤)
      (Bh : ∀ i, B (.inl i) = h i) (Be : ∀ a, B (.inr a) = e a)
      (htan : ∀ a, IsRootTangent Q z a (e a) ∧
        (h a).toMul.val = torus Q (D.datum.coroot a)
          (CommAlgCat.of _ (DualNumber RationalField.{u})) dualUnit)
      (hopp : ∀ a, ⁅e a, e (D.datum.reflectionPerm a a)⁆ = h a)
      (hCartan : ∀ a r, ⁅h a, e r⁆ = D.datum.pairing r a • e r)
      (ω : Basis D.base.support ℤ D.X)
      (hω : ∀ i j : D.base.support, D.datum.coroot' j (ω i) = if j = i then 1 else 0)
      (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
      (negative : List (Negative D)) (hV : ∀ i, (V i).IsIntegralLattice negative)
      (n : ℕ) (b : Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
      (w : Index.{u} n → D.X)
      (hw : ∀ j i, b j i ∈ (V i).weightSpace (w j))
      (hb : Submodule.span ℤ (Set.range b) =
        Submodule.pi Set.univ (fun i => (V i).lattice negative))
      (height : D.X →ₗ[ℤ] ℤ) (hpos : ∀ i : Positive D, 0 < height (D.datum.root i))
      (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
      (hp : ∀ a m j i, ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
        (dividedPower ((V i).rootOperator a) m).mulVec (b j i)),
    ∀ a : D.I, ∃ (μ : D.X) (v : Index.{u} n → ℤ)
      (φ : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ),
      (∀ j, w j ≠ μ → v j = 0) ∧
      (∀ j, w j ≠ μ + D.datum.root a → φ (Pi.single j 1) = 0) ∧
      φ ((coefficientMatrix (p a) 1).mulVec v) = 1 := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  intro e h B Bh Be htan hopp hCartan ω hω V negative hV n b w hw hb height hpos p hp
  let := D.finiteRoots
  let := Fintype.ofFinite D.I
  let I := Index.{u} n
  let ι := UniversalEnvelopingAlgebra.ι RationalField.{u} (L := 𝔤)
  let cast := (Int.castRingHom RationalField.{u}).mapMatrix (m := I)
  let E (a : D.I) := coefficientMatrix (p a) 1
  let d : 𝔤 →ₗ⁅RationalField.{u}⁆ Matrix I I RationalField.{u} :=
    (directSumEnvelopingAction V b).toLieHom.comp ι
  have hE (a : D.I) : d (e a) = cast (E a) := by
    change directSumEnvelopingAction V b (ι (e a)) = cast (E a)
    simpa only [dividedPower_one] using (directSumEnvelopingAction_coeff V b p hp a 1).symm
  let opp (a : D.I) := D.datum.reflectionPerm a a
  let cartan (a : D.I) : Matrix I I ℤ := Matrix.diagonal (fun j => D.datum.coroot' a (w j))
  have hcomm (a : D.I) : E a * E (opp a) - E (opp a) * E a = cartan a :=
    integral_coroot_matrix V b w hw p hp a (opp a) (fun i =>
      coroot_matrix_commutator s e h (ω i) (V i) a (opp a)
        (htan a).1 (htan (opp a)).1 (htan a).2 (hopp a))
  have hcartan (a : D.I) : d (h a) =
      Matrix.diagonal (fun j => (D.datum.coroot' a (w j) : RationalField.{u})) := by
    rw [← hopp, d.map_lie, hE, hE, Ring.lie_def, ← map_mul, ← map_mul, ← map_sub, hcomm]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [cast, cartan]
    · simp [cast, cartan, Matrix.diagonal_apply_ne _ hij, hij]
  have hbr (a r : D.I) : ⁅d (h a), d (e r)⁆ = (D.datum.pairing r a : RationalField.{u}) • d (e r) := by
    rw [← d.map_lie]
    have he := hCartan a r
    have hz := congrArg
      (fun law : AddGroup (PointKernel Q.pinned.pair.G.val) => law.zsmul (D.datum.pairing r a) (e r))
      s.group_law
    change d ⁅h a, e r⁆ = _
    rw [show ⁅h a, e r⁆ = s.lieRing.toAddCommGroup.toAddGroup.zsmul
      (D.datum.pairing r a) (e r) from he.trans hz.symm]
    exact (@AddMonoidHom.map_zsmul _ _
      s.lieRing.toAddCommGroup.toAddGroup inferInstance
      d.toLinearMap.toAddMonoidHom _ _).trans (Int.cast_smul_eq_zsmul RationalField.{u} _ _).symm
  have hnegPair (r a : D.I) : D.datum.pairing (opp r) a = -D.datum.pairing r a := by
    change D.datum.coroot' a (D.datum.root (opp r)) = -D.datum.coroot' a (D.datum.root r)
    rw [show D.datum.root (opp r) = -D.datum.root r by simp [opp], map_neg]
  have hbound (a : D.I) : ∃ N : ℕ, d (e a) ^ N = 0 := by
    let N : ℕ := ∑ i : D.base.support, (V i).nilpotenceBound
    refine ⟨N, ?_⟩
    change directSumEnvelopingAction V b (ι (e a)) ^ N = 0
    rw [← map_pow]
    apply Matrix.ext
    intro i j
    rw [directSumEnvelopingAction_entry]
    have hzero (l : D.base.support) : ((V l).envelopingAction (ι (e a) ^ N)) = 0 := by
      rw [map_pow]
      exact pow_eq_zero_of_le (Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ l))
        ((V l).nilpotent a)
    simp only [hzero, Matrix.zero_mulVec, ← Pi.zero_def, map_zero, Matrix.zero_apply]
  have hrootEval (a : D.I) (t : ℤ) :
      cast ((Polynomial.evalRingHom t).mapMatrix (p a)) = IsNilpotent.exp ((t : RationalField.{u}) • d (e a)) := by
    obtain ⟨N, hN⟩ := hbound a
    exact integralRoot_eval_sign _ _ hN (directSumEnvelopingAction_coeff V b p hp a) t
  have hnil (a : D.I) : IsNilpotent (d (e a)) := hbound a
  obtain ⟨_, hshift⟩ := integralRootPolynomials_support V b w hw p hp
  have hshift' (a : D.I) (i j : I) (hij : w i ≠ w j + D.datum.root a) :
      d (e a) i j = 0 := by
    have hz := hshift a 1 i j (by simpa only [one_nsmul] using hij)
    rw [hE]
    change ((p a i j).coeff 1 : RationalField.{u}) = 0
    rw [hz, Int.cast_zero]
  have htest (a : D.I) := exists_coroot_diagonal_test D height hpos ω
    (fun j => by simp [hω]) w (fundamentalWeights_span_of_weightBasis ω V b w hw) a
  have hEne (a : D.I) : d (e a) ≠ 0 := by
    intro hz
    obtain ⟨t, ht⟩ := htest a
    have he : E a = 0 := Matrix.map_injective (f := Int.castRingHom RationalField.{u}) Int.cast_injective
      ((hE a).symm.trans (hz.trans (map_zero cast).symm))
    change (∑ i : I, t i * cartan a i i) = 1 at ht
    rw [← hcomm, he, Matrix.zero_mul, Matrix.mul_zero, sub_zero] at ht
    simp at ht
  let Test (a : D.I) : Prop :=
    ∃ (μ : D.X) (v : I → ℤ) (φ : (I → ℤ) →ₗ[ℤ] ℤ),
      (∀ j, w j ≠ μ → v j = 0) ∧
      (∀ j, w j ≠ μ + D.datum.root a → φ (Pi.single j 1) = 0) ∧ φ ((E a).mulVec v) = 1
  change ∀ a, Test a
  apply all_roots_of_simple_reflections D height hpos Test
  · intro i
    exact simpleRoot_unit_coefficient V negative hV b w hw hb p hp i
      (D.base.isPos_of_mem_support i.property) (hopp i) (by simp [hω])
  rintro i a ⟨μ, v, φ, hv, hφ, hunit⟩
  let σ := D.datum.reflection i
  have hσ : Function.Involutive σ := D.datum.reflection_same i
  let Ev (a : D.I) (t : ℤ) := (Polynomial.evalRingHom t).mapMatrix (p a)
  have heval (a : D.I) (t : ℤ) :
      cast (Ev a t) = IsNilpotent.exp ((t : RationalField.{u}) • d (e a)) :=
    hrootEval a t
  let P := Ev i 1 * Ev (opp i) (-1) * Ev i 1
  let P' := Ev i (-1) * Ev (opp i) 1 * Ev i (-1)
  let x := d (e i)
  let y := d (e (opp i))
  have hPexp : cast P = IsNilpotent.exp x * IsNilpotent.exp (-y) * IsNilpotent.exp x := by
    simp only [P, map_mul, heval, Int.cast_one, Int.cast_neg, one_smul, neg_smul, x, y]
  have hP'exp : cast P' = IsNilpotent.exp (-x) * IsNilpotent.exp y * IsNilpotent.exp (-x) := by
    simp only [P', map_mul, heval, Int.cast_one, Int.cast_neg, one_smul, neg_smul, x, y]
  have hQP : P' * P = 1 := by
    apply Matrix.map_injective (f := Int.castRingHom RationalField.{u}) Int.cast_injective
    change cast _ = cast 1
    rw [map_mul, hPexp, hP'exp, map_one]
    calc
      _ = IsNilpotent.exp (-x) *
          (IsNilpotent.exp y * ((IsNilpotent.exp (-x) * IsNilpotent.exp x) *
            IsNilpotent.exp (-y))) * IsNilpotent.exp x := by simp only [mul_assoc]
      _ = 1 := by
        rw [IsNilpotent.exp_neg_mul_exp_self (hnil i), one_mul,
          IsNilpotent.exp_mul_exp_neg_self (hnil (opp i)), mul_one,
          IsNilpotent.exp_neg_mul_exp_self (hnil i)]
  have hQP' : cast P' * cast P = 1 := by rw [← map_mul, hQP, map_one]
  have hword (M : Matrix I I RationalField.{u}) :
      cast P * M * cast P' = innerExp (K := RationalField.{u}) x (innerExp (K := RationalField.{u}) (-y) (innerExp (K := RationalField.{u}) x M)) := by
    simp only [hPexp, hP'exp, innerExp_apply, neg_neg, mul_assoc]
  have hCartanConj (j : D.base.support) :
      cast P * d (h j) * cast P' =
        Matrix.diagonal (fun k => (D.datum.coroot' j (σ (w k)) : RationalField.{u})) := by
    have hop := hbr i (opp i)
    rw [hnegPair, D.datum.pairing_same, Int.cast_neg, Int.cast_ofNat] at hop
    have hxy : ⁅x, y⁆ = d (h i) := by
      change ⁅d (e i), d (e (opp i))⁆ = d (h i)
      rw [← d.map_lie, hopp]
    have he := hbr j (opp i)
    rw [hnegPair, Int.cast_neg] at he
    rw [hword, rankOneWordReflection (d (h i)) x y
      (by simpa only [x, D.datum.pairing_same, Int.cast_ofNat] using hbr i i)
      hop hxy (hnil i) (hnil (opp i)) (d (h j)) _ (hbr j i) he, hcartan j, hcartan i]
    apply Matrix.ext
    intro k l
    by_cases hl : k = l
    · subst l
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
      rw [show σ (w k) = w k - (D.datum.coroot' i (w k)) • D.datum.root i
        from D.datum.reflection_apply i (w k)]
      simp only [map_sub, map_smul, Int.cast_sub, smul_eq_mul, Int.cast_mul]
      rw [RootPairing.root_coroot'_eq_pairing, mul_comm
        (D.datum.pairing (i : D.I) j : RationalField.{u})]
    · simp [Matrix.diagonal_apply_ne _ hl, hl]
  have hPs : ∀ k l, w k ≠ σ (w l) → cast P k l = 0 := by
    apply reflected_weight_of_diagonal_intertwining ω hω w i _ false
    intro j
    change cast P * Matrix.diagonal (fun k => (D.datum.coroot' j (w k) : RationalField.{u})) =
      Matrix.diagonal (fun k => (D.datum.coroot' j (σ (w k)) : RationalField.{u})) * cast P
    rw [← hcartan j, ← hCartanConj j, mul_assoc (cast P * d (h j)), hQP', mul_one]
  have hP's : ∀ k l, w k ≠ σ (w l) → cast P' k l = 0 := by
    apply reflected_weight_of_diagonal_intertwining ω hω w i _ true
    intro j
    change cast P' * Matrix.diagonal (fun k => (D.datum.coroot' j (σ (w k)) : RationalField.{u})) =
      Matrix.diagonal (fun k => (D.datum.coroot' j (w k) : RationalField.{u})) * cast P'
    rw [← hcartan j, ← hCartanConj j, ← mul_assoc (cast P') (cast P * d (h j)),
      ← mul_assoc (cast P') (cast P), hQP', one_mul]
  let S := LinearMap.range d.toLinearMap
  have hclose {M N : Matrix I I RationalField.{u}} (hM : M ∈ S) (hN : N ∈ S) : M * N - N * M ∈ S := by
    obtain ⟨m, rfl⟩ := hM
    obtain ⟨n, rfl⟩ := hN
    exact ⟨⁅m, n⁆, d.map_lie m n⟩
  have hmem (r : D.I) : d (e r) ∈ S := ⟨e r, rfl⟩
  have hxe {M : Matrix I I RationalField.{u}} (hm : M ∈ S) : innerExp (K := RationalField.{u}) x M ∈ S :=
    exponentialConjugationMem (S.restrictScalars ℚ) x (hnil i) (fun _ hm' => hclose (hmem i) hm') hm
  have hye {M : Matrix I I RationalField.{u}} (hm : M ∈ S) : innerExp (K := RationalField.{u}) (-y) M ∈ S :=
    exponentialConjugationMem (S.restrictScalars ℚ) (-y) (hnil (opp i)).neg
      (fun M hm' => hclose (S.neg_mem (hmem (opp i))) hm') hm
  have hS : S = Submodule.span RationalField.{u}
      (Set.range (fun j : D.base.support => d (h j)) ∪ Set.range (fun r => d (e r))) := by
    rw [show S = (⊤ : Submodule RationalField.{u} 𝔤).map d.toLinearMap by simp [S],
      ← B.span_eq, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext M
    constructor
    · rintro ⟨j | r, rfl⟩
      · exact Or.inl ⟨j, congrArg d (Bh j).symm⟩
      · exact Or.inr ⟨r, congrArg d (Be r).symm⟩
    · rintro (⟨j, rfl⟩ | ⟨r, rfl⟩)
      · exact ⟨Sum.inl j, congrArg d (Bh j)⟩
      · exact ⟨Sum.inr r, congrArg d (Be r)⟩
  have hcS : cast P * d (e a) * cast P' ∈ S := by
    rw [hword]
    exact hxe (hye (hxe (hmem a)))
  let r := D.datum.reflectionPerm i a
  have hr : D.datum.root r = σ (D.datum.root a) := D.datum.root_reflectionPerm i a
  obtain ⟨c, hc⟩ := rootLine_of_span D.datum.root (fun a => D.datum.ne_zero a) w _
    (by
      rintro _ ⟨j, rfl⟩ k l hkl
      change d (h j) k l = 0
      rw [hcartan]
      exact Matrix.diagonal_apply_ne _ hkl)
    (fun r => d (e r)) hshift' r (hS ▸ hcS)
    (by simpa only [hr] using
      reflected_root_support w σ hσ _ _ _ _ hPs hP's (hshift' a))
  have hPc : cast (P * E a * P') = c • cast (E r) := by
    rw [map_mul, map_mul, ← hE, ← hE]
    exact hc
  have hc₀ : c ≠ 0 := by
    rintro rfl
    have hZero : cast P * d (e a) * cast P' = 0 := by simpa using hc
    have hCancel : cast P' * (cast P * d (e a) * cast P') * cast P = d (e a) := by
      calc
        _ = (cast P' * cast P) * d (e a) * (cast P' * cast P) := by simp only [mul_assoc]
        _ = _ := by rw [hQP', one_mul, mul_one]
    rw [hZero, mul_zero, zero_mul] at hCancel
    exact hEne a hCancel.symm
  obtain ⟨dE, hdE⟩ := htest a
  obtain ⟨dF, hdF⟩ := htest r
  change (∑ i : I, dE i * cartan a i i) = 1 at hdE
  change (∑ i : I, dF i * cartan r i i) = 1 at hdF
  rw [← hcomm a] at hdE
  rw [← hcomm r] at hdF
  obtain ⟨c', hc'⟩ := matrix_conjugation_unit_of_commutator_tests P P' (E a) (E r)
    (E (opp a)) (E (opp r)) hQP c hc₀ hPc dE dF hdE hdF
  have hPs' (k l : I) (hkl : w k ≠ σ (w l)) : P k l = 0 :=
    Int.cast_eq_zero.mp (hPs k l hkl)
  have hP's' (k l : I) (hkl : w k ≠ σ.symm (w l)) : P' k l = 0 := by
    have hh : cast P' k l = 0 :=
      hP's k l (by simpa only [show σ.symm = σ from D.datum.reflection_inv i] using hkl)
    exact Int.cast_eq_zero.mp hh
  change Test r
  unfold Test
  rw [hr]
  exact unit_coefficient_of_weight_conjugation w σ P P' (E a) (E r)
    hQP hPs' hP's' c' hc' (D.datum.root a) μ v φ hv hφ hunit

end

end WeylTransport

section Assembly
open CategoryTheory
open scoped Classical

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates IsChevalley OppositeRootRelations IndependentRootRelations
  FormalBigCellProduct IsRootTangent torus dualUnit)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralLattices
open Module

private def HasRationalFundamentalActions {D : BasedRootDatum.{u}}
    {A : AdditiveLine RationalField.{u}} {Q : Realization D A} (z : RootCoordinates Q) : Prop :=
  ∃ s : IdentityLieStructure Q.pinned.pair.G.val,
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ (e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val)
      (B : Basis (D.base.support ⊕ D.I) RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val))
      (ω : Basis D.base.support ℤ D.X),
    IsChevalley Q z ∧ OppositeRootRelations Q z ∧ IndependentRootRelations Q z ∧
    FormalBigCellProduct Q z ∧
    (∀ a, IsRootTangent Q z a (e a) ∧
      (h a).toMul.val = torus Q (D.datum.coroot a)
        (CommAlgCat.of _ (DualNumber RationalField.{u})) dualUnit) ∧
    (∀ i, B (.inl i) = h i) ∧ (∀ a, B (.inr a) = e a) ∧
    (∀ a, ⁅e a, e (D.datum.reflectionPerm a a)⁆ = h a) ∧
    (∀ a r, ⁅h a, e r⁆ = D.datum.pairing r a • e r) ∧
    (∀ i j : D.base.support, D.datum.coroot' j (ω i) = if j = i then 1 else 0) ∧
    Nonempty (∀ i : D.base.support, RationalHighestWeight z e h (ω i))

/-- Existence of the rational fundamental modules on a common model with
the marked Chevalley coordinates used in the integral construction. -/
def RationalFundamentalActions : Prop :=
  ∀ (D : BasedRootDatum.{u}), RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∃ (A : AdditiveLine RationalField.{u}) (Q : Realization D A) (z : RootCoordinates Q),
      HasRationalFundamentalActions z

theorem integralLattices_of_rational_actions (hmodel : RationalFundamentalActions.{u}) :
    Statement.{u} := by
  intro D hss hcor
  obtain ⟨A, Q, z, s, H⟩ := hmodel D hss hcor
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨e, h, B, ω, hChev, hOpp, hInd, hCollect, htan, Bh, Be, hbr, hCartan, hω, ⟨V⟩⟩ := H
  refine ⟨A, Q, z, s, e, h, ω, hChev, hOpp, hInd, hCollect, htan, hω, ?_⟩
  intro negative positive hn hp
  obtain ⟨n, b, w, height, p, hV, hb, hw, ha, hpos, hneg, ht, hcoeff, _, _⟩ :=
    fundamentalLattices_and_triangularProducts ω V hCollect B Bh Be negative positive hn hp
  have hunit := root_unit_coefficients (z := z) s e h B Bh Be htan hbr hCartan ω hω
    V negative hV n b w hw hb height hpos p hcoeff
  obtain ⟨hClosedNeg, hClosedPos⟩ :=
    closedRootImages_of_unit_coefficients V b w hw height ha hpos hneg p hcoeff negative positive hn hp hunit
  exact ⟨V, n, b, w, height, p, hV, hb, hw, ha, hpos, hneg, ht, hcoeff, hunit, hClosedNeg, hClosedPos⟩

end Assembly

section EnvelopingComparison

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k K L M : Type*} [Field k] [Field K] [Algebra k K]
  [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra K M]
  [LieAlgebra k M] [IsScalarTower k K M]

local notation "U₀" => UniversalEnvelopingAlgebra k L
local notation "U₁" => UniversalEnvelopingAlgebra K M

variable [Algebra k (UniversalEnvelopingAlgebra K M)]
  [IsScalarTower k K (UniversalEnvelopingAlgebra K M)]

private def envelopingComparison (f : L →ₗ⁅k⁆ M) : U₀ →ₐ[k] U₁ :=
  let ι₁ : M →ₗ⁅k⁆ U₁ :=
    { (ι K (L := M)).toLinearMap.restrictScalars k with
      map_lie' := fun {x y} => (ι K (L := M)).map_lie x y }
  lift k (ι₁.comp f)

private theorem envelopingComparison_apply (f : L →ₗ⁅k⁆ M) (x : L) :
    envelopingComparison (K := K) f (ι k x) = ι K (f x) :=
  by rw [envelopingComparison, lift_ι_apply]; rfl

/-- A surjective map of Lie algebras and a surjective coefficient map give
a surjective map of their enveloping algebras. -/
private theorem envelopingComparison_surjective (f : L →ₗ⁅k⁆ M)
    (hf : Function.Surjective f) (hk : Function.Surjective (algebraMap k K)) :
    Function.Surjective (envelopingComparison (K := K) f) := by
  let F := envelopingComparison (K := K) f
  have hq : Function.Surjective (mkAlgHom K M) :=
    RingCon.mkₐ_surjective _
  intro b
  obtain ⟨b, rfl⟩ := hq b
  induction b using TensorAlgebra.induction with
  | algebraMap t =>
    obtain ⟨r, rfl⟩ := hk t
    refine ⟨algebraMap k U₀ r, ?_⟩
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply k K U₁]
  | ι x =>
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨ι k y, envelopingComparison_apply f y⟩
  | mul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    exact ⟨a' * b', by rw [map_mul, ha', hb', map_mul]⟩
  | add a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    exact ⟨a' + b', by rw [map_add, ha', hb', map_add]⟩

/-- The image of a left ideal generated by given relators lies in any
left ideal containing their images. -/
private theorem map_mem_span_of_mem {B C : Type*} [Ring B] [Ring C]
    (f : B →+* C) (S : Set B) (J : Submodule C C)
    (hJ : ∀ b ∈ S, f b ∈ J) {b : B} (hb : b ∈ Submodule.span B S) : f b ∈ J := by
  induction hb using Submodule.span_induction with
  | mem b hb => exact hJ b hb
  | zero => simpa only [map_zero] using J.zero_mem
  | add b c _ _ hb hc => simpa only [map_add] using J.add_mem hb hc
  | smul a b _ hb =>
    change f (a * b) ∈ J
    simpa only [map_mul, smul_eq_mul] using J.smul_mem (f a) hb

end EnvelopingComparison

section MatrixBlocks

open scoped Matrix
noncomputable section

variable {J : Type*} {ι : J → Type*}
  [Fintype J] [DecidableEq J] [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]
  {R : Type*} [CommRing R]

private def blockDiagonalUnits :
    (∀ j, Matrix.GeneralLinearGroup (ι j) R) →*
      Matrix.GeneralLinearGroup (Σ j, ι j) R :=
  (Units.map (Matrix.blockDiagonal'RingHom ι R).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun j => Matrix (ι j) (ι j) R)).symm.toMonoidHom

private theorem blockDiagonalUnits_val (g : ∀ j, Matrix.GeneralLinearGroup (ι j) R) :
    (blockDiagonalUnits g).val = Matrix.blockDiagonal' (fun j => (g j).val) := rfl

private theorem blockDiagonalUnits_injective :
    Function.Injective (blockDiagonalUnits (ι := ι) (R := R)) := by
  intro g h he
  funext j
  apply Units.ext
  exact congrFun (Matrix.blockDiagonal'_injective (congrArg Units.val he)) j

private theorem blockDiagonalUnits_exists
    (g : Matrix.GeneralLinearGroup (Σ j, ι j) R)
    (hg : ∀ j k, j ≠ k → ∀ (i : ι j) (l : ι k), g.val ⟨j, i⟩ ⟨k, l⟩ = 0)
    (hi : ∀ j k, j ≠ k → ∀ (i : ι j) (l : ι k), g⁻¹.val ⟨j, i⟩ ⟨k, l⟩ = 0) :
    ∃ a, blockDiagonalUnits a = g := by
  let B := Matrix.blockDiagonal'RingHom ι R
  let a (j : J) : Matrix (ι j) (ι j) R := fun i l => g.val ⟨j, i⟩ ⟨j, l⟩
  let b (j : J) : Matrix (ι j) (ι j) R := fun i l => g⁻¹.val ⟨j, i⟩ ⟨j, l⟩
  have ha : B a = g.val := by
    ext ⟨j, i⟩ ⟨k, l⟩
    by_cases h : j = k
    · subst k
      exact Matrix.blockDiagonal'_apply_eq a _ _ _
    · exact (Matrix.blockDiagonal'_apply_ne a _ _ h).trans (hg j k h i l).symm
  have hb : B b = g⁻¹.val := by
    ext ⟨j, i⟩ ⟨k, l⟩
    by_cases h : j = k
    · subst k
      exact Matrix.blockDiagonal'_apply_eq b _ _ _
    · exact (Matrix.blockDiagonal'_apply_ne b _ _ h).trans (hi j k h i l).symm
  have hab : a * b = 1 := by
    apply Matrix.blockDiagonal'_injective
    change B (a * b) = B 1
    rw [map_mul, map_one, ha, hb, Units.mul_inv]
  have hba : b * a = 1 := by
    apply Matrix.blockDiagonal'_injective
    change B (b * a) = B 1
    rw [map_mul, map_one, ha, hb, Units.inv_mul]
  refine ⟨fun j => ⟨a j, b j, congrFun hab j, congrFun hba j⟩, Units.ext ?_⟩
  exact ha

variable {K : Type*} [Field K] [Algebra K R]

/-- Commuting with a diagonal having distinct base-field values on distinct
blocks forces every off-block entry to vanish, over any test algebra. -/
private theorem commutes_diagonal_blocks (s : J → K) (hs : Function.Injective s)
    (g : Matrix (Σ j, ι j) (Σ j, ι j) R)
    (hg : Commute g (Matrix.diagonal fun i => algebraMap K R (s i.1))) :
    ∀ j k, j ≠ k → ∀ (i : ι j) (l : ι k), g ⟨j, i⟩ ⟨k, l⟩ = 0 := by
  intro j k h i l
  have hm := congrArg (fun M : Matrix (Σ j, ι j) (Σ j, ι j) R => M ⟨j, i⟩ ⟨k, l⟩) hg.eq
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hm
  let q := g ⟨j, i⟩ ⟨k, l⟩
  change q * (algebraMap K R (s k)) = (algebraMap K R (s j)) * q at hm
  have hz : algebraMap K R (s k - s j) * q = 0 := by
    rw [map_sub, sub_mul, mul_comm (algebraMap K R (s k)), hm, sub_self]
  have hu := (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hs.ne h.symm))).map (algebraMap K R)
  exact hu.mul_left_cancel (hz.trans (mul_zero _).symm)

end
end MatrixBlocks

section BlockActions

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup GroupScheme)
open _root_.LinearAlgebraicGroups.Specs.StandardGroups (generalLinearPoints)
open private closedSubgroupOfLocus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private theorem centralizerOfPoint {G : GroupScheme k} [IsSeparated G.X.hom]
    (c : 𝟙_ (SchemeOver k) ⟶ G.X) :
    ∃ H : ClosedSubgroup G, ∀ (T : SchemeOver k) (p : T ⟶ G.X),
      Commute p (toUnit T ≫ c) ↔ ∃ z : T ⟶ H.group.X, z ≫ H.inclusion.hom.hom = p := by
  let t := toUnit G.X ≫ c
  let f := (𝟙 G.X) * t
  let g := t * (𝟙 G.X)
  let P (T : SchemeOver k) := Subgroup.centralizer ({toUnit T ≫ c} : Set (T ⟶ G.X))
  have hP (T : SchemeOver k) (p : T ⟶ G.X) : p ∈ P T ↔ p ≫ f = p ≫ g := by
    change (p ∈ Subgroup.centralizer ({toUnit T ≫ c} : Set (T ⟶ G.X))) ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    dsimp only [f, g, t]
    rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  obtain ⟨H, hH⟩ := closedSubgroupOfLocus P (equalizer.ι f g) inferInstance (by
    intro T p
    rw [hP]
    refine ⟨fun h => ⟨equalizer.lift p h, equalizer.lift_ι _ _⟩, ?_⟩
    rintro ⟨z, rfl⟩
    exact congrArg (z ≫ ·) (equalizer.condition f g))
  refine ⟨H, fun T p => ?_⟩
  rw [← hH]
  change _ ↔ p ∈ Subgroup.centralizer ({toUnit T ≫ c} : Set (T ⟶ G.X))
  rw [Subgroup.mem_centralizer_singleton_iff]
  rfl

variable {J : Type u} {I : J → Type u}
  [Fintype J] [DecidableEq J] [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  {F : TestAlgebra k ⥤ GrpCat.{u}}

private theorem exists_blockUnitPreimage (a : F ⟶ generalLinearPoints k (Σ j, I j))
    (ha : ∀ (R : TestAlgebra k) (g : F.obj R) j l, j ≠ l →
      ∀ (i : I j) (s : I l), ((a.app R).hom g).val ⟨j, i⟩ ⟨l, s⟩ = 0)
    (R : TestAlgebra k) (g : F.obj R) :
    ∃ v, blockDiagonalUnits v = (a.app R).hom g := by
  apply blockDiagonalUnits_exists _ (ha R g)
  intro j l hjl i s
  have hh : ((a.app R).hom g)⁻¹ = (a.app R).hom g⁻¹ :=
    (map_inv (a.app R).hom g).symm
  exact (congrArg (fun p : Matrix.GeneralLinearGroup (Σ j, I j) R =>
    p.val ⟨j, i⟩ ⟨l, s⟩) hh).trans (ha R g⁻¹ j l hjl i s)

/-- Project a group action preserving the blocks onto one of its blocks. -/
private def blockRepresentation (a : F ⟶ generalLinearPoints k (Σ j, I j))
    (ha : ∀ (R : TestAlgebra k) (g : F.obj R) j l, j ≠ l →
      ∀ (i : I j) (s : I l), ((a.app R).hom g).val ⟨j, i⟩ ⟨l, s⟩ = 0)
    (j : J) : F ⟶ generalLinearPoints k (I j) := by
  let h := exists_blockUnitPreimage a ha
  let p (R : TestAlgebra k) (g : F.obj R) := (h R g).choose
  have hp (R : TestAlgebra k) (g : F.obj R) :
      blockDiagonalUnits (p R g) = (a.app R).hom g := (h R g).choose_spec
  have hval (R : TestAlgebra k) (g : F.obj R) (j : J) (i l : I j) :
      (p R g j).val i l = ((a.app R).hom g).val ⟨j, i⟩ ⟨j, l⟩ := by
    rw [← hp R g, blockDiagonalUnits_val, Matrix.blockDiagonal'_apply_eq]
  refine
    { app := fun R => GrpCat.ofHom
        { toFun := fun g => p R g j
          map_one' := by
            suffices h' : p R 1 = 1 from congrFun h' j
            apply blockDiagonalUnits_injective
            simp only [hp, map_one]
          map_mul' := fun x y => by
            suffices h' : p R (x * y) = p R x * p R y from congrFun h' j
            apply blockDiagonalUnits_injective
            rw [hp, map_mul (a.app R).hom, map_mul blockDiagonalUnits, hp, hp] }
      naturality := fun {R S} f => ?_ }
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i l
  change (p S ((F.map f).hom g) j).val i l = f.hom ((p R g j).val i l)
  rw [hval, hval]
  exact congrArg (fun m : Matrix.GeneralLinearGroup (Σ j, I j) S => m.val ⟨j, i⟩ ⟨j, l⟩)
    (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (a.naturality f)) g)

private theorem blockRepresentation_val (a : F ⟶ generalLinearPoints k (Σ j, I j))
    (ha : ∀ (R : TestAlgebra k) (g : F.obj R) j l, j ≠ l →
      ∀ (i : I j) (s : I l), ((a.app R).hom g).val ⟨j, i⟩ ⟨l, s⟩ = 0)
    (R : TestAlgebra k) (g : F.obj R) (j : J) (i l : I j) :
    (((blockRepresentation a ha j).app R).hom g).val i l =
      ((a.app R).hom g).val ⟨j, i⟩ ⟨j, l⟩ := by
  let h := exists_blockUnitPreimage a ha R g
  unfold blockRepresentation
  change (h.choose j).val i l = _
  calc
    _ = (blockDiagonalUnits h.choose).val ⟨j, i⟩ ⟨j, l⟩ :=
      (Matrix.blockDiagonal'_apply_eq _ _ _ _).symm
    _ = _ := congrArg (fun m : Matrix.GeneralLinearGroup (Σ j, I j) R => m.val ⟨j, i⟩ ⟨j, l⟩)
      h.choose_spec

end
end BlockActions

section FundamentalBlocks

open _root_.LinearAlgebraicGroups.Specs.RationalRealization
  (generator CyclicPresentation cyclicRepresentation cyclicVector serreHighestRelations
    loweringWord loweringWeight RationalWeightWords rationalWeightSpace)
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.IntegralLattices (Index)
open Module
open scoped TensorProduct Matrix Classical

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : BasedRootDatum.{u}} [DecidableEq D.base.support]

private abbrev rationalSerreAlgebra (D : BasedRootDatum.{u}) [DecidableEq D.base.support] :=
  Matrix.ToLieAlgebra ℚ (RootData.integralCartan D.datum D.base)

private abbrev cyclicHighestWeight (lam : D.X) :=
  CyclicPresentation (serreHighestRelations D lam)

private abbrev datumCartanMatrix (D : BasedRootDatum.{u}) :=
  RootData.integralCartan D.datum D.base

private def cyclicBlock {lam : D.X} {n : ℕ}
    (b : Basis (Index.{u} n) ℚ (cyclicHighestWeight lam)) :
    rationalSerreAlgebra D →ₗ⁅ℚ⁆ Matrix (Index.{u} n) (Index.{u} n) ℚ :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.toLieHom.comp
    (cyclicRepresentation (serreHighestRelations D lam))

private theorem cyclicBlockCartan (wordsTheorem : RationalWeightWords.{u})
    {lam : D.X} {n : ℕ} (b : Basis (Index.{u} n) ℚ (cyclicHighestWeight lam))
    (words : Index.{u} n → List D.base.support)
    (hb : ∀ j, b j = loweringWord D lam (words j))
    (i : D.base.support) :
    cyclicBlock b (generator ℚ (datumCartanMatrix D) (.H i)) =
      Matrix.diagonal (fun j => (D.datum.coroot' i (loweringWeight D lam (words j)) : ℚ)) := by
  classical
  apply Matrix.ext
  intro j k
  change (LinearMap.toMatrixAlgEquiv b
    (cyclicRepresentation (serreHighestRelations D lam) (generator ℚ (datumCartanMatrix D) (.H i)))) j k = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  have hw : cyclicRepresentation (serreHighestRelations D lam)
      (generator ℚ (datumCartanMatrix D) (.H i)) (b k) =
      (D.datum.coroot' i (loweringWeight D lam (words k)) : ℚ) • b k := by
    rw [hb]
    exact (wordsTheorem D lam).1 (words k) i
  rw [hw, map_smul, Finsupp.smul_apply, Basis.repr_self_apply]
  by_cases hjk : j = k
  · subst k
    simp
  · simp [hjk, Ne.symm hjk]

/-- The block matrices of a root vector have their original character shift. -/
private theorem cyclicBlockRootShift (wordsTheorem : RationalWeightWords.{u})
    (hsep : Function.Injective (fun x : D.X => fun i : D.base.support => D.datum.coroot' i x))
    {lam : D.X} {n : ℕ} (b : Basis (Index.{u} n) ℚ (cyclicHighestWeight lam))
    (words : Index.{u} n → List D.base.support)
    (hb : ∀ j, b j = loweringWord D lam (words j))
    (a : D.I) (x : rationalSerreAlgebra D)
    (hx : x ∈ rationalWeightSpace (datumCartanMatrix D) (fun i => D.datum.pairing a i)) :
    ∀ i j, cyclicBlock b x i j ≠ 0 →
      loweringWeight D lam (words i) = loweringWeight D lam (words j) + D.datum.root a := by
  intro i j hne
  apply hsep
  funext k
  let N := cyclicBlock b x
  have h := congrArg (cyclicBlock b) (hx k)
  change cyclicBlock b ⁅generator ℚ (datumCartanMatrix D) (.H k), x⁆ =
    cyclicBlock b ((D.datum.pairing a k : ℚ) • x) at h
  rw [(cyclicBlock b).map_lie, Ring.lie_def, cyclicBlockCartan wordsTheorem b words hb, map_smul] at h
  have hentry := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) ℚ => M i j) h
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply] at hentry
  let wi := loweringWeight D lam (words i)
  let wj := loweringWeight D lam (words j)
  change (D.datum.coroot' k wi : ℚ) * N i j - N i j * (D.datum.coroot' k wj : ℚ) =
    (D.datum.pairing a k : ℚ) * N i j at hentry
  have he : (D.datum.coroot' k wi : ℚ) =
      (D.datum.coroot' k wj : ℚ) + (D.datum.pairing a k : ℚ) := by
    apply mul_right_cancel₀ hne
    rw [add_mul, ← hentry]
    ring
  change D.datum.coroot' k wi = D.datum.coroot' k (wj + D.datum.root a)
  rw [map_add]
  exact_mod_cast he

private def cyclicBlockAction {lam : D.X} {n : ℕ}
    (b : Basis (Index.{u} n) ℚ (cyclicHighestWeight lam)) :
    UniversalEnvelopingAlgebra ℚ (rationalSerreAlgebra D) →ₐ[ℚ]
      Matrix (Index.{u} n) (Index.{u} n) ℚ :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lsmul ℚ ℚ (cyclicHighestWeight lam))

private theorem cyclicBlockAction_apply {lam : D.X} {n : ℕ}
    (b : Basis (Index.{u} n) ℚ (cyclicHighestWeight lam)) (x : rationalSerreAlgebra D) :
    cyclicBlockAction b (UniversalEnvelopingAlgebra.ι ℚ x) = cyclicBlock b x := rfl

private theorem cyclicBlockAction_mulVec_highest {lam : D.X} {n : ℕ}
    (b : Basis (Index.{u} n) ℚ (cyclicHighestWeight lam))
    (a : UniversalEnvelopingAlgebra ℚ (rationalSerreAlgebra D)) :
    (cyclicBlockAction b a).mulVec (b.equivFun (cyclicVector (serreHighestRelations D lam))) =
      b.equivFun ((Submodule.span _ (serreHighestRelations D lam)).mkQ a) := by
  have h := LinearMap.toMatrix_mulVec_repr b b (Algebra.lsmul ℚ ℚ (cyclicHighestWeight lam) a)
    (cyclicVector (serreHighestRelations D lam))
  change (cyclicBlockAction b a).mulVec (b.equivFun (cyclicVector (serreHighestRelations D lam))) =
    b.equivFun (a • cyclicVector (serreHighestRelations D lam)) at h
  rw [h]
  congr 1
  let S := Submodule.span (UniversalEnvelopingAlgebra ℚ (rationalSerreAlgebra D))
    (serreHighestRelations D lam)
  change a • S.mkQ 1 = S.mkQ a
  rw [← S.mkQ.map_smul, smul_eq_mul, mul_one]

end

end FundamentalBlocks

section MarkedRationalMatrixModel

open CategoryTheory AlgebraicGeometry
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization
  (RationalField MatrixGroup rationalCharacter diagonalTorus)
open _root_.LinearAlgebraicGroups.Specs.CharacterPairing (pairing)
open _root_.LinearAlgebraicGroups.RationalRealization
  (positiveIntegralCocharacter extendRootMatrix rationalLatticeMatrixSpan_bracket rationalCorootBracket_over
    weightDiagonal)
open private generateMatrixGroup matrixGroup_reductive_and_maximal matrixGroup_borel
  MatrixBorel MarkedMatrixRealization MatrixBorel.markedRealization
  rationalMatrix_map_tower diagonalCocharacters diagonalCharacters diagonalCharacters_eq diagonalPairing
  corootFunctional corootDiagonal_ne_zero matrixCharacter
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
open scoped Matrix TensorProduct

noncomputable section

local instance : CharZero (RationalField.{u}) :=
  charZero_of_injective_ringHom
    (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
    (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective

variable {D : BasedRootDatum.{u}} {J : Type u} [Fintype J] [DecidableEq J]

/-- The word construction with prescribed rational operators and their
weight labels produces the marked matrix model over the lifted rationals. -/
private theorem markedRationalMatrixModel
    (w : J → D.X) (hw : Submodule.span ℤ (Set.range w) = ⊤) (N : D.I → Matrix J J ℚ)
    (d : (ℚ ⊗[ℤ] D.Y) →ₗ[ℚ] Matrix J J ℚ)
    (hd : ∀ y, d y = Matrix.diagonal fun i => rationalCharacter D (w i) y)
    (L : Submodule ℚ (Matrix J J ℚ))
    (hL : L = LinearMap.range d ⊔ ⨆ i, ℚ ∙ N i)
    (hbr : ∀ x ∈ L, ∀ y ∈ L, x * y - y * x ∈ L)
    (hN : ∀ i, N i ≠ 0 ∧ IsNilpotent (N i) ∧ ∀ a b, N i a b ≠ 0 → w a = w b + D.datum.root i)
    (hop : ∀ i, ∃ c : ℚ, c ≠ 0 ∧
      N i * N (D.datum.reflectionPerm i i) - N (D.datum.reflectionPerm i i) * N i =
        c • d (1 ⊗ₜ[ℤ] D.datum.coroot i)) :
    ∃ (G : MatrixGroup D RationalField.{u} J w
        (fun i => (algebraMap ℚ RationalField.{u}).mapMatrix (N i)))
      (B : MatrixBorel G), Nonempty (MarkedMatrixRealization B) := by
  classical
  let k := RationalField.{u}
  let K := AlgebraicClosure k
  let Nk (F : Type u) [Field F] [CharZero F] i := (algebraMap ℚ F).mapMatrix (N i)
  have hroot (F : Type u) [Field F] [CharZero F] (i : D.I) := extendRootMatrix w i (N i) (hN i) F
  have hG (F : Type u) [Field F] [CharZero F] : Nonempty (MatrixGroup D F J w (Nk F)) :=
    generateMatrixGroup D w (Nk F) hw (hroot F) (rationalLatticeMatrixSpan_bracket w N d hd L hL hbr F)
  obtain ⟨G⟩ := hG k
  obtain ⟨H⟩ := hG K
  let N' (i : D.I) := (algebraMap k K).mapMatrix (Nk k i)
  have hNk : Nk K = N' := funext fun i => rationalMatrix_map_tower (N i)
  let H' : MatrixGroup D K J w N' := hNk ▸ H
  have hshift : ∀ i a b, N' i a b ≠ 0 → w a = w b + D.datum.root i := by
    rw [← hNk]
    exact fun i => (hroot K i).2.2
  have hOpp (i : D.I) := rationalCorootBracket_over (k := K) w N d hd hop i
  have hOpp' : ∀ r, ∃ s φ,
      N' s * N' r - N' r * N' s = weightDiagonal w φ ∧ weightDiagonal w φ ≠ 0 := by
    rw [← hNk]
    intro r
    obtain ⟨s, hs, he⟩ := hOpp r
    refine ⟨D.datum.reflectionPerm r r, (-s) • corootFunctional K r, ?_, ?_⟩
    · rw [← neg_sub, he, map_smul, neg_smul]
    · rw [map_smul]
      exact smul_ne_zero (neg_ne_zero.mpr hs) (corootDiagonal_ne_zero w hw r)
  obtain ⟨hred, hmax⟩ := matrixGroup_reductive_and_maximal G H' hshift hOpp'
  obtain ⟨y, m, hm, hy⟩ := positiveIntegralCocharacter D
  let c := Additive.toMul (diagonalCocharacters k D y)
  have hc (i : D.I) : pairing (diagonalTorus k D).val (matrixCharacter k D (D.datum.root i)) c =
      m * D.base.height i := by
    have hmark : Additive.toMul (diagonalCharacters k D (D.datum.root i)) =
        matrixCharacter k D (D.datum.root i) := diagonalCharacters_eq k D _
    rw [← hmark]
    exact (diagonalPairing k D (D.datum.root i) y).trans (hy i)
  obtain ⟨B, _⟩ := matrixGroup_borel G hred hmax (fun i => (hroot k i).1)
    (fun i => (hroot k i).2.2) c m hm hc
  refine ⟨G, B, MatrixBorel.markedRealization B hw (hroot k) ?_⟩
  intro i
  obtain ⟨s, _, hs⟩ := rationalCorootBracket_over (k := k) w N d hd hop i
  exact ⟨s, hs⟩

end
end MarkedRationalMatrixModel

section FundamentalMatrixModel

open Module CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct Classical
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open _root_.LinearAlgebraicGroups.Specs.IntegralLattices (Index)
open _root_.LinearAlgebraicGroups.Specs.RationalRealization
  (generator rationalWeightSpace rationalCharacter loweringWord loweringWeight
    MatrixGroup RationalField)
open _root_.LinearAlgebraicGroups.RationalRealization
  (rationalWeightWords rationalSerreDecomposition rationalCartanLattice
    rationalCorootBracket weightShiftMatrix extendRootMatrix)
open _root_.LinearAlgebraicGroups.Classification.IntegralRootRelations (simpleCorootEvaluations_injective)
open private MatrixBorel MarkedMatrixRealization
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
open RootData (rationalRootAnnihilator)

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : BasedRootDatum.{u}} [DecidableEq D.base.support]

private abbrev blockIndices (n : D.base.support → ℕ) := Σ i : D.base.support, Index.{u} (n i)

private def fundamentalMatrices (ω : D.base.support → D.X) (n : D.base.support → ℕ)
    (b : ∀ i, Basis (Index.{u} (n i)) ℚ (cyclicHighestWeight (ω i))) :
    rationalSerreAlgebra D →ₗ⁅ℚ⁆ Matrix (blockIndices n) (blockIndices n) ℚ :=
  let A : (∀ i : D.base.support, Matrix (Index.{u} (n i)) (Index.{u} (n i)) ℚ) →ₐ[ℚ]
      Matrix (blockIndices n) (blockIndices n) ℚ :=
    { Matrix.blockDiagonal'RingHom (fun i : D.base.support => Index.{u} (n i)) ℚ with
      commutes' := by
        intro c
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        change Matrix.blockDiagonal' (c • (1 : ∀ i : D.base.support,
          Matrix (Index.{u} (n i)) (Index.{u} (n i)) ℚ)) =
          c • (1 : Matrix (blockIndices n) (blockIndices n) ℚ)
        rw [Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one] }
  (A.comp (AlgHom.pi fun i => cyclicBlockAction (b i))).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℚ)

private theorem fundamentalMatrices_val (ω : D.base.support → D.X) (n : D.base.support → ℕ)
    (b : ∀ i, Basis (Index.{u} (n i)) ℚ (cyclicHighestWeight (ω i))) (x : rationalSerreAlgebra D) :
    fundamentalMatrices ω n b x = Matrix.blockDiagonal' (fun i => cyclicBlock (b i) x) := rfl

set_option maxHeartbeats 1200000 in
private theorem fundamentalMatrixModel
    (hss : rationalRootAnnihilator D.datum = ⊥)
    (hcor : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤)
    (ω : Basis D.base.support ℤ D.X)
    (n : D.base.support → ℕ)
    (b : ∀ i, Basis (Index.{u} (n i)) ℚ (cyclicHighestWeight (ω i)))
    (words : ∀ i, Index.{u} (n i) → List D.base.support)
    (hb : ∀ i j, b i j = loweringWord D (ω i) (words i j))
    (hhigh : ∀ i, ∃ j, words i j = [])
    (v : D.I → rationalSerreAlgebra D)
    (B₀ : Basis (D.base.support ⊕ D.I) ℚ (rationalSerreAlgebra D))
    (hv : ∀ a, v a ≠ 0 ∧ v a ∈ rationalWeightSpace (datumCartanMatrix D) (fun i => D.datum.pairing a i))
    (hB₀ : ∀ i, B₀ (.inl i) = generator ℚ (datumCartanMatrix D) (.H i))
    (hB₁ : ∀ a, B₀ (.inr a) = v a) :
    let w (j : blockIndices n) := loweringWeight D (ω j.1) (words j.1 j.2)
    let N (a : D.I) := (algebraMap ℚ RationalField.{u}).mapMatrix (fundamentalMatrices ω n b (v a))
    letI : CharZero (RationalField.{u}) :=
      charZero_of_injective_ringHom
        (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
        (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective
    (∀ a, N a ≠ 0 ∧ IsNilpotent (N a) ∧ ∀ i j, N a i j ≠ 0 → w i = w j + D.datum.root a) ∧
    ∃ (G : MatrixGroup D RationalField.{u} (blockIndices n) w N)
      (B : MatrixBorel G), Nonempty (MarkedMatrixRealization B) := by
  classical
  letI : CharZero (RationalField.{u}) :=
    charZero_of_injective_ringHom
      (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
      (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective
  letI : Finite D.I := D.finiteRoots
  letI : Fintype D.I := Fintype.ofFinite D.I
  letI := D.freeX
  let w (j : blockIndices n) := loweringWeight D (ω j.1) (words j.1 j.2)
  let ρ := fundamentalMatrices ω n b
  let N (a : D.I) := ρ (v a)
  let S := rationalSerreAlgebra D
  let H := rationalWeightSpace (datumCartanMatrix D) 0
  let Z := rationalRootAnnihilator D.datum
  have hz : ∀ z : Z, z = 0 := by
    intro z
    apply Subtype.ext
    have h : (z : ℚ ⊗[ℤ] D.Y) ∈ (⊥ : Submodule ℚ (ℚ ⊗[ℤ] D.Y)) := hss ▸ z.property
    simpa only [Submodule.mem_bot, Submodule.coe_zero] using h
  have hw : Submodule.span ℤ (Set.range w) = ⊤ := by
    apply top_unique
    rw [← ω.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hhigh i
    apply Submodule.subset_span
    refine ⟨⟨i, j⟩, ?_⟩
    change loweringWeight D (ω i) (words i j) = ω i
    simp [hj, loweringWeight]
  have hroot (a : D.I) (i j : blockIndices n) (hij : N a i j ≠ 0) :
      w i = w j + D.datum.root a := by
    rcases i with ⟨i, s⟩
    rcases j with ⟨j, t⟩
    change ρ (v a) ⟨i, s⟩ ⟨j, t⟩ ≠ 0 at hij
    rw [show ρ (v a) = _ from fundamentalMatrices_val ω n b (v a)] at hij
    by_cases h : i = j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq] at hij
      exact cyclicBlockRootShift rationalWeightWords (simpleCorootEvaluations_injective D hcor)
        (b i) (words i) (hb i) a (v a) (hv a).2 s t hij
    · exact ((hij (Matrix.blockDiagonal'_apply_ne _ _ _ h))).elim
  obtain ⟨η, hη, _⟩ := rationalCartanLattice D
  have hη₀ := hη
  choose H₀ hH₀ hHη using hη
  have hspanH : Submodule.span ℚ (Set.range H₀) = ⊤ := by
    apply Submodule.map_injective_of_injective H.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    change Submodule.span ℚ (Set.range fun i => (H₀ i).val) = H
    simp_rw [hH₀]
    exact (rationalSerreDecomposition D).2.2.symm
  let inH : H →ₗ[ℚ] H × Z := LinearMap.id.prod 0
  let f := ρ.toLinearMap.comp H.subtype
  let g := (Matrix.diagonalLinearMap (blockIndices n) ℚ ℚ).comp
    (LinearMap.pi fun j => (rationalCharacter D (w j)).comp (η.toLinearMap.comp inH))
  have hfg : f = g := by
    apply LinearMap.ext_on hspanH
    rintro _ ⟨i, rfl⟩
    change ρ (H₀ i).val = Matrix.diagonal (fun j => rationalCharacter D (w j) (η (H₀ i, 0)))
    rw [hH₀, hHη, fundamentalMatrices_val]
    have h (j : blockIndices n) : rationalCharacter D (w j) (1 ⊗ₜ[ℤ] D.datum.coroot i) =
        (D.datum.coroot' i (w j) : ℚ) := RootData.extendFunctional_one_tmul _ _ _
    have hdiag :
        Matrix.diagonal (fun j : blockIndices n => rationalCharacter D (w j) (1 ⊗ₜ[ℤ] D.datum.coroot i)) =
          Matrix.blockDiagonal' (fun j : D.base.support =>
            Matrix.diagonal (fun l => (D.datum.coroot' i (w ⟨j, l⟩) : ℚ))) := by
      rw [Matrix.blockDiagonal'_diagonal]
      exact congrArg Matrix.diagonal (funext h)
    rw [hdiag]
    congr 1
    funext j
    exact cyclicBlockCartan rationalWeightWords (b j) (words j) (hb j) i
  let d := f.comp ((LinearMap.fst ℚ H Z).comp η.symm.toLinearMap)
  have hd' (h : H) : d (η (h, 0)) = ρ h.val := by
    change f (η.symm (η (h, 0))).1 = _
    rw [η.symm_apply_apply]
    rfl
  have hd (y : ℚ ⊗[ℤ] D.Y) : d y = Matrix.diagonal fun j => rationalCharacter D (w j) y := by
    obtain ⟨⟨h, z⟩, rfl⟩ := η.surjective y
    rw [hz z, hd']
    exact DFunLike.congr_fun hfg h
  have hOpp (a : D.I) : ∃ c : ℚ, c ≠ 0 ∧
      N a * N (D.datum.reflectionPerm a a) - N (D.datum.reflectionPerm a a) * N a =
        c • d (1 ⊗ₜ[ℤ] D.datum.coroot a) := by
    let a' := D.datum.reflectionPerm a a
    obtain ⟨h, c, hne, hL, he⟩ := rationalCorootBracket D η hη₀ a (v a) (v a')
      (hv a).2 (hv a').2 (hv a).1 (hv a').1
    refine ⟨c, hne, ?_⟩
    change ⁅ρ (v a), ρ (v a')⁆ = _
    rw [← ρ.map_lie, ← hL, ← hd', he, map_smul]
  have hN (a : D.I) : N a ≠ 0 ∧ IsNilpotent (N a) ∧
      ∀ i j, N a i j ≠ 0 → w i = w j + D.datum.root a := by
    refine ⟨?_, (weightShiftMatrix w _ _ (D.datum.ne_zero a) (hroot a)).1, hroot a⟩
    intro h
    obtain ⟨c, hc, he⟩ := hOpp a
    rw [h, Matrix.zero_mul, Matrix.mul_zero, sub_zero] at he
    apply smul_ne_zero hc _ he.symm
    intro hz
    rw [hd] at hz
    have hvanish (j : blockIndices n) : D.datum.coroot' a (w j) = 0 := by
      have h := congrArg (fun M : Matrix (blockIndices n) (blockIndices n) ℚ => M j j) hz
      rw [Matrix.diagonal_apply_eq, Matrix.zero_apply] at h
      change RootData.extendFunctional ℚ (D.datum.toLinearMap (w j))
        (1 ⊗ₜ[ℤ] D.datum.coroot a) = 0 at h
      rw [RootData.extendFunctional_one_tmul] at h
      exact Int.cast_eq_zero.mp h
    have hle : Submodule.span ℤ (Set.range w) ≤ (D.datum.coroot' a).ker :=
      Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact LinearMap.mem_ker.mpr (hvanish j))
    have hbad := LinearMap.mem_ker.mp (hle (hw ▸ (Submodule.mem_top : D.datum.root a ∈ ⊤)))
    rw [RootPairing.root_coroot'_eq_pairing, D.datum.pairing_same] at hbad
    omega
  let L := LinearMap.range ρ.toLinearMap
  have hrange : LinearMap.range d = H.map ρ.toLinearMap := by
    ext M
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨⟨h, z⟩, rfl⟩ := η.surjective y
      rw [hz z, hd']
      exact ⟨h.val, h.property, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨η (⟨h, hh⟩, 0), hd' ⟨h, hh⟩⟩
  have hL : L = LinearMap.range d ⊔ ⨆ a, ℚ ∙ N a := by
    have hH := (rationalSerreDecomposition D).2.2
    change H = _ at hH
    rw [hrange, hH, Submodule.map_span,
      ← Set.range_comp, ← Submodule.span_iUnion, Set.iUnion_singleton_eq_range, ← Submodule.span_union]
    rw [show L = (⊤ : Submodule ℚ S).map ρ.toLinearMap by simp [L],
      ← B₀.span_eq, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨i | a, rfl⟩
      · exact Or.inl ⟨i, congrArg ρ (hB₀ i).symm⟩
      · exact Or.inr ⟨a, congrArg ρ (hB₁ a).symm⟩
    · rintro (⟨i, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl i, congrArg ρ (hB₀ i)⟩
      · exact ⟨Sum.inr a, congrArg ρ (hB₁ a)⟩
  have hbr : ∀ x ∈ L, ∀ y ∈ L, x * y - y * x ∈ L := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨⁅x, y⁆, ρ.map_lie x y⟩
  exact ⟨fun a => extendRootMatrix w a (N a) (hN a) RationalField.{u},
    markedRationalMatrixModel w hw N d hd L hL hbr hN hOpp⟩

end

end FundamentalMatrixModel

section MarkedLieComparison

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization generator)
open Specs.RootGroups (AdditiveLine)
open Specs.IntegralRootRelations (IsRootString)
open _root_.LinearAlgebraicGroups.Classification.IntegralRootRelations
  (simpleCorootEvaluations_injective)
open private HasCartanWeight serreRelations_of_cartanBasis exists_serreHom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRootRelations
open Module
open scoped Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}} {Q : Realization D A}
  [DecidableEq D.base.support]

local notation "𝔤" => Lie RationalField Q.pinned.pair.G.val

private theorem rationalCoefficient_surjective :
    Function.Surjective (algebraMap ℚ RationalField.{u}) := by
  let r : ℚ ≃+* RationalField.{u} := ULift.ringEquiv.symm
  have h : algebraMap ℚ RationalField.{u} = r.toRingHom := Subsingleton.elim _ _
  rw [h]
  exact r.surjective

set_option maxHeartbeats 1000000 in
/-- Compare the actual tangent Lie algebra with the rational Serre
presentation, retaining the simple Chevalley generators. -/
private theorem markedSerreMap (s : IdentityLieStructure Q.pinned.pair.G.val)
    (hcor : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI : LieAlgebra ℚ 𝔤 :=
      inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ RationalField.{u} 𝔤))
    ∀ (e h : D.I → 𝔤) (b : Basis (D.base.support ⊕ D.I) RationalField.{u} 𝔤),
      (∀ i, b (.inl i) = h i) → (∀ a, b (.inr a) = e a) →
      (∀ i j, ⁅h i, h j⁆ = 0) →
      (∀ i j, ⁅h i, e j⁆ = D.datum.pairing j i • e j) →
      (∀ i, ⁅e i, e (D.datum.reflectionPerm i i)⁆ = h i) →
      (∀ i j k, D.datum.root i + D.datum.root j = D.datum.root k →
        ∃ (p q : ℕ) (n : ℤ), IsRootString i j p q ∧
          (n = (p : ℤ) + 1 ∨ n = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = n • e k) →
      ∃ f : rationalSerreAlgebra D →ₗ⁅ℚ⁆ 𝔤, Function.Surjective f ∧
        (∀ i, f (generator ℚ (datumCartanMatrix D) (.H i)) = h i) ∧
        (∀ i, f (generator ℚ (datumCartanMatrix D) (.E i)) = e i) ∧
        (∀ i, f (generator ℚ (datumCartanMatrix D) (.F i)) = e (D.datum.reflectionPerm i i)) := by
  let K := RationalField.{u}
  letI : CharZero K :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv.symm : ℚ ≃+* K).toRingHom)
      (ULift.ringEquiv.symm : ℚ ≃+* K).injective
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : LieAlgebra ℚ 𝔤 := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ K 𝔤))
  letI : IsScalarTower ℚ K 𝔤 := IsScalarTower.restrictScalars ℚ K 𝔤
  intro e h b hb he hHH hHE hEF hroots
  let H (i : D.base.support) := h i
  let E (i : D.base.support) := e i
  let opp (a : D.I) := D.datum.reflectionPerm a a
  let F (i : D.base.support) := e (opp i)
  have hWeight (i : D.base.support ⊕ D.I) :
      HasCartanWeight (K := K) H (i.elim (fun _ => 0) D.datum.root) (b i) := by
    intro j
    cases i with
    | inl i =>
      rw [hb]
      have hz := congrArg (fun law : AddGroup (PointKernel Q.pinned.pair.G.val) =>
        law.toAddMonoid.toAddZeroClass.toZero.zero) s.group_law
      change ⁅h j, h i⁆ =
        (D.datum.toLinearMap (0 : D.X) (D.datum.coroot j) : K) • h i
      rw [map_zero, LinearMap.zero_apply, Int.cast_zero]
      rw [zero_smul]
      exact (hHH j i).trans hz.symm
    | inr a =>
      have hz := congrArg
        (fun law : AddGroup (PointKernel Q.pinned.pair.G.val) => law.zsmul (D.datum.pairing a j) (e a))
        s.group_law
      rw [he]
      change ⁅h j, e a⁆ = (D.datum.pairing a j : K) • e a
      exact (hHE j a).trans (hz.symm.trans (Int.cast_smul_eq_zsmul K _ _).symm)
  have hWeightF (i : D.base.support) : HasCartanWeight (K := K) H (-D.datum.root i) (F i) := by
    have hh := hWeight (.inr (opp i))
    simpa only [Sum.elim_inr, he, F, opp, D.datum.root_reflectionPerm, D.datum.reflection_apply_self] using hh
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    serreRelations_of_cartanBasis b H E F hWeight (simpleCorootEvaluations_injective D hcor)
      hb (fun i => he i) hWeightF (fun i => hEF i)
  have had (x y : 𝔤) (n : ℕ) :
      ((LieAlgebra.ad ℚ 𝔤 x) ^ n) y = ((LieAlgebra.ad K 𝔤 x) ^ n) y := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, ih]
  obtain ⟨f, hfH, hfE, hfF⟩ := exists_serreHom (K := ℚ) (datumCartanMatrix D) H E F h₁ h₂ h₃ h₄
    (fun i j hij => (had _ _ _).trans (h₅ i j hij)) (fun i j hij => (had _ _ _).trans (h₆ i j hij))
  let S : LieSubalgebra K 𝔤 :=
    { carrier := Set.range f
      zero_mem' := ⟨0, f.map_zero⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, f.map_add x y⟩
      smul_mem' := by
        rintro t _ ⟨x, rfl⟩
        obtain ⟨r, rfl⟩ := rationalCoefficient_surjective t
        refine ⟨r • x, ?_⟩
        rw [map_smul, algebraMap_smul K]
      lie_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨⁅x, y⁆, f.map_lie x y⟩ }
  have htop : S = ⊤ := by
    apply top_unique
    rw [← lieSpan_simpleChevalley_eq_top s b hb he hroots]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨_, hfH i⟩
    · exact ⟨_, hfE i⟩
    · exact ⟨_, hfF i⟩
  refine ⟨f, ?_, hfH, hfE, hfF⟩
  intro x
  change x ∈ S
  rw [htop]
  trivial

end
end MarkedLieComparison

section CyclicBaseChange

open Specs.RationalRealization (CyclicPresentation serreHighestRelations cyclicVector RationalField)
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralLattices (Index)
open Module

noncomputable section

variable {D : BasedRootDatum.{u}} [DecidableEq D.base.support]

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the cyclic highest-vector map is preserved when the old
action is compared with a surjective map of enveloping algebras. -/
private theorem cyclicBlockPresentation {lam : D.X} {n : ℕ}
    (b : Basis (Index.{u} n) ℚ (cyclicHighestWeight lam))
    {B : Type u} [Ring B] [Algebra RationalField.{u} B]
    (F : UniversalEnvelopingAlgebra ℚ (rationalSerreAlgebra D) →+* B) (hF : Function.Surjective F)
    (ρ : B →ₐ[RationalField.{u}] Matrix (Index.{u} n) (Index.{u} n) RationalField.{u})
    (hρ : ∀ a, ρ (F a) = (algebraMap ℚ RationalField.{u}).mapMatrix (cyclicBlockAction b a)) :
    let v (i : Index.{u} n) := algebraMap ℚ RationalField.{u}
      (b.equivFun (cyclicVector (serreHighestRelations D lam)) i)
    Function.Surjective (fun a => (ρ a).mulVec v) ∧
      ∀ a, (ρ a).mulVec v = 0 ↔ a ∈ Submodule.span B (F '' serreHighestRelations D lam) := by
  let K := RationalField.{u}
  letI : CharZero K :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv.symm : ℚ ≃+* K).toRingHom)
      (ULift.ringEquiv.symm : ℚ ≃+* K).injective
  let I := Index.{u} n
  let A := UniversalEnvelopingAlgebra ℚ (rationalSerreAlgebra D)
  let S : Set A := serreHighestRelations D lam
  let L := Submodule.span A S
  let f := algebraMap ℚ K
  let v := f ∘ b.equivFun (cyclicVector S)
  have he (a : A) : (ρ (F a)).mulVec v = f ∘ (b.equivFun (L.mkQ a)) := by
    rw [hρ, ← mapMatrix_mulVec, cyclicBlockAction_mulVec_highest]
  have hz (a : A) : (ρ (F a)).mulVec v = 0 ↔ a ∈ L := by
    rw [he]
    have hq : L.mkQ a = 0 ↔ a ∈ L := Submodule.Quotient.mk_eq_zero L
    rw [← hq]
    constructor
    · intro h
      apply b.equivFun.injective
      funext j
      rw [map_zero, Pi.zero_apply]
      apply f.injective
      rw [map_zero]
      exact congrFun h j
    · intro h
      rw [h, map_zero]
      funext j
      exact map_zero f
  change Function.Surjective (fun a => (ρ a).mulVec v) ∧ _
  constructor
  · intro x
    choose t ht using fun j : I => rationalCoefficient_surjective (x j)
    obtain ⟨a, ha⟩ := L.mkQ_surjective (b.equivFun.symm t)
    refine ⟨F a, ?_⟩
    change (ρ (F a)).mulVec v = x
    rw [he, ha, b.equivFun.apply_symm_apply]
    exact funext ht
  · intro x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := hF x
      refine map_mem_span_of_mem F S (Submodule.span B (F '' S)) ?_ ((hz a).mp hx)
      exact fun r hr => Submodule.subset_span ⟨r, hr, rfl⟩
    · intro hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact (hz a).mpr (Submodule.subset_span ha)
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add, Matrix.add_mulVec, hx, hy, add_zero]
      | smul r x _ hx => simp only [smul_eq_mul, map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

end

end CyclicBaseChange

section MatrixDifferential

open CategoryTheory
open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure AffineAlgebraicGroup)
open Specs.RationalRealization (RationalField exponentialMatrix matrixAlgebra)
open Specs.IntegralLattices
open Specs.StandardGroups (generalLinearPoints)
open InfinitesimalCommutator (matrixDifferential)
open private matrixDifferentialLinear matrixDifferential_bracket from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

local instance : CharZero (RationalField.{u}) :=
  charZero_of_injective_ringHom
    (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
    (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective

/-- Evaluation of the finite exponential agrees with its expression by
nilpotence, over every rational test algebra. -/
private theorem exponentialPolynomial_eval {n N : ℕ}
    (E : Matrix (Index.{u} n) (Index.{u} n) RationalField.{u}) (hE : E ^ N = 0)
    (R : TestAlgebra RationalField.{u}) (t : R) :
    (Polynomial.eval₂RingHom (algebraMap RationalField.{u} R) t).mapMatrix (exponentialPolynomial E N) =
      exponentialMatrix E R t := by
  let K := RationalField.{u}
  let F := (algebraMap K R).mapMatrix (m := Index.{u} n)
  let := matrixAlgebra R
  have hN : (t • F E) ^ N = 0 := by
    rw [smul_pow, ← map_pow, hE, map_zero, smul_zero]
  change _ = IsNilpotent.exp (t • F E)
  rw [IsNilpotent.exp_eq_sum hN, exponentialPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Matrix.ext
  intro i j
  change (Polynomial.eval₂ (algebraMap K R) t
    ((Polynomial.X ^ m) * Polynomial.C (dividedPower E m i j))) =
      (((m.factorial : ℚ)⁻¹) • (t • F E) ^ m) i j
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Matrix.smul_apply, smul_pow, Matrix.smul_apply]
  change t ^ m * algebraMap K R ((m.factorial : K)⁻¹ * (E ^ m) i j) =
      ((m.factorial : ℚ)⁻¹) • (t ^ m * (F E ^ m) i j)
  rw [← map_pow F, map_mul]
  have hnum : algebraMap K R ((m.factorial : K)⁻¹) =
      algebraMap ℚ R ((m.factorial : ℚ)⁻¹) := by
    change algebraMap K R _ = algebraMap K R (algebraMap ℚ K ((m.factorial : ℚ)⁻¹))
    rw [map_inv₀ (algebraMap ℚ K), map_natCast]
  change t ^ m * (algebraMap K R ((m.factorial : K)⁻¹) *
    algebraMap K R ((E ^ m) i j)) = algebraMap ℚ R ((m.factorial : ℚ)⁻¹) *
      (t ^ m * algebraMap K R ((E ^ m) i j))
  rw [hnum]
  ring

variable {G : AffineAlgebraicGroup RationalField.{u}} {J : Type u} [Fintype J] [DecidableEq J]

/-- Recover the Lie action from a natural matrix action on the actual group. -/
private def lieActionOfPointAction (s : IdentityLieStructure G.val)
    (a : (groupPointsFunctor RationalField.{u}).obj G.val ⟶ generalLinearPoints RationalField.{u} J) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Lie RationalField.{u} G.val →ₗ⁅RationalField.{u}⁆ Matrix J J RationalField.{u} := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let K := RationalField.{u}
  let M := StandardGroups.generalLinearGroup K J
  let η := StandardGroups.generalLinearGroupPointsIso K J
  let E := groupHomEquiv G.val M.val G.property.1
  let f := E.symm (a ≫ η.inv)
  let : AlgebraicGeometry.IsAffine G.val.X.left := G.property.1
  let d := matrixDifferentialLinear f η
  refine
    { toFun := matrixDifferential f η
      map_add' := fun p q => ?_
      map_smul' := fun c p => ?_
      map_lie' := fun {p q} => matrixDifferential_bracket f η s.commutator_law p q }
  · have h := congrArg
      (fun law : AddGroup (PointKernel G.val) => law.toAdd.add p q) s.group_law
    exact (congrArg (matrixDifferential f η) h).trans (map_add d p q)
  · have h := congrFun (congrFun s.scalar_law c) p
    exact (congrArg (matrixDifferential f η) h).trans (map_smul d c p)

private theorem lieActionOfPointAction_apply (s : IdentityLieStructure G.val)
    (a : (groupPointsFunctor RationalField.{u}).obj G.val ⟶ generalLinearPoints RationalField.{u} J)
    (p : Lie RationalField.{u} G.val) (i j : J) :
    (lieActionOfPointAction s a) p i j =
      (((a.app (CommAlgCat.of _ (DualNumber RationalField.{u}))).hom p.toMul.val).val i j).snd := by
  let K := RationalField.{u}
  let M := StandardGroups.generalLinearGroup K J
  let η := StandardGroups.generalLinearGroupPointsIso K J
  let E := groupHomEquiv G.val M.val G.property.1
  let f := E.symm (a ≫ η.inv)
  have hη : (groupPointsFunctor K).map f ≫ η.hom = a := by
    change E f ≫ η.hom = a
    rw [show E f = a ≫ η.inv from E.apply_symm_apply _, Category.assoc, η.inv_hom_id, Category.comp_id]
  exact congrArg (fun x : _ ⟶ _ =>
    (((x.app (CommAlgCat.of K (DualNumber K))).hom p.toMul.val :
      Matrix.GeneralLinearGroup J (DualNumber K)).val i j).snd) hη

end
end MatrixDifferential

section MatrixGroupActions

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix
open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup GroupScheme)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (MatrixGroup diagonalTorus exponentialMatrix matrixAlgebra)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootGroups (AdditiveLine rootPoint)
open private subgroupInclusionFactors from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open Specs.StandardGroups (generalLinearPoints)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k J : Type u} [Field k] [CharZero k] {I : J → Type u}
  [Fintype J] [DecidableEq J] [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  {D : BasedRootDatum.{u}} {w : (Σ j, I j) → D.X} {N : D.I → Matrix (Σ j, I j) (Σ j, I j) k}

private abbrev matrixGroupPointAction (G : MatrixGroup D k (Σ j, I j) w N) :
    (groupPointsFunctor k).obj G.group.group ⟶ generalLinearPoints k (Σ j, I j) :=
  (groupPointsFunctor k).map G.group.inclusion ≫ G.matrixPoints.hom

private theorem preservesBlock_commute {R : Type u} [CommRing R] (s : J → R)
    (X : Matrix (Σ j, I j) (Σ j, I j) R)
    (hX : ∀ j l, j ≠ l → ∀ (i : I j) (p : I l), X ⟨j, i⟩ ⟨l, p⟩ = 0) :
    Commute X (Matrix.diagonal fun u => s u.1) := by
  apply Matrix.ext
  rintro ⟨a, i⟩ ⟨b, j⟩
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_ne a b with rfl | h
  · exact mul_comm _ _
  · rw [hX a b h i j, zero_mul, mul_zero]

/-- The generated matrix group preserves the blocks preserved by its torus
and the root matrices. The centralizer argument works over every test ring. -/
private theorem matrixModel_preserves_blocks (G : MatrixGroup D k (Σ j, I j) w N)
    (hN : ∀ a, IsNilpotent (N a))
    (hBlock : ∀ a j l, j ≠ l → ∀ (i : I j) (p : I l), N a ⟨j, i⟩ ⟨l, p⟩ = 0) :
    ∀ (R : TestAlgebra k) (g : GroupPoints G.group.group R) j l, j ≠ l →
      ∀ (i : I j) (p : I l), ((matrixGroupPointAction G).app R g).val ⟨j, i⟩ ⟨l, p⟩ = 0 := by
  classical
  let : IsAffine G.ambient.val.X.left := G.ambient.property.1
  let : IsSeparated G.ambient.val.X.hom := IsSeparated.of_isAffineHom _
  let R₀ := CommAlgCat.of k k
  let c (j : J) : k := ((Fintype.equivFin J j).val + 1 : ℕ)
  have hc (j : J) : c j ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hcInj : Function.Injective c := by
    intro j l he
    apply (Fintype.equivFin J).injective
    apply Fin.ext
    have h : (Fintype.equivFin J j).val + 1 = (Fintype.equivFin J l).val + 1 :=
      Nat.cast_injective he
    omega
  let U : Matrix.GeneralLinearGroup (Σ j, I j) k :=
    Units.map (Matrix.diagonalRingHom (Σ j, I j) k).toMonoidHom
      ((MulEquiv.piUnits (M := fun _ : (Σ j, I j) => k)).symm fun i => Units.mk0 (c i.1) (hc i.1))
  let p₀ : GroupPoints G.ambient.val R₀ := G.matrixPoints.inv.app R₀ U
  let e₀ : (testSpec k).obj (op R₀) ≅ 𝟙_ (SchemeOver k) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
      rw [Spec.map_id, Category.comp_id])
  let p := e₀.inv ≫ p₀
  obtain ⟨H, hH⟩ := centralizerOfPoint p
  let diag (R : TestAlgebra k) : Matrix (Σ j, I j) (Σ j, I j) R :=
    Matrix.diagonal (fun i => algebraMap k R (c i.1))
  have hconst (R : TestAlgebra k) :
      (G.matrixPoints.hom.app R (toUnit ((testSpec k).obj (op R)) ≫ p)).val = diag R := by
    let f : R₀ ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have he : toUnit ((testSpec k).obj (op R)) ≫ e₀.inv = (testSpec k).map f.op := by
      apply (cancel_mono e₀.hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact Subsingleton.elim _ _
    have hn := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (G.matrixPoints.hom.naturality f)) p₀
    change G.matrixPoints.hom.app R ((testSpec k).map f.op ≫ p₀) =
      Matrix.GeneralLinearGroup.map (algebraMap k R) (G.matrixPoints.hom.app R₀ p₀) at hn
    change (G.matrixPoints.hom.app R (toUnit ((testSpec k).obj (op R)) ≫ (e₀.inv ≫ p₀))).val = _
    rw [← Category.assoc, he, hn]
    have heval : G.matrixPoints.hom.app R₀ p₀ = U := by
      apply (G.matrixPoints.app R₀).groupIsoToMulEquiv.symm.injective
      exact (G.matrixPoints.app R₀).groupIsoToMulEquiv.symm_apply_apply p₀
    rw [heval]
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [U, diag]
    · simp [U, diag, hij]
  have hchar (R : TestAlgebra k) (g : GroupPoints G.ambient.val R) :
      (∃ z : GroupPoints H.group R, z ≫ H.inclusion.hom.hom = g) ↔
        Commute (G.matrixPoints.hom.app R g).val (diag R) := by
    let T := (testSpec k).obj (op R)
    have hr := hH T g
    change (∃ z : T ⟶ H.group.X, z ≫ H.inclusion.hom.hom = g) ↔ _
    refine hr.symm.trans ?_
    let f := (G.matrixPoints.app R).groupIsoToMulEquiv
    change Commute g (toUnit T ≫ p) ↔ Commute (f g).val (diag R)
    rw [← hconst R]
    constructor
    · intro hg
      exact (hg.map f.toMonoidHom).map (Units.coeHom _)
    · intro hg
      apply f.injective
      apply Units.ext
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
      exact hg.eq
  have htorus : ∃ t : (diagonalTorus k D).val ⟶ H.group,
      t ≫ H.inclusion = G.torus ≫ G.group.inclusion := by
    apply subgroupInclusionFactors (diagonalTorus k D).property.1 H
    intro R t
    apply (hchar R _).mpr
    change Commute ((G.matrixPoints.hom.app R).hom
      (t ≫ (G.torus ≫ G.group.inclusion).hom.hom)).val (diag R)
    rw [G.torusMatrix]
    exact Matrix.commute_diagonal _ _
  have hroot (a : D.I) : ∃ x : G.additive.group ⟶ H.group,
      x ≫ H.inclusion = G.root a ≫ G.group.inclusion := by
    let := G.additive.operations.hopf
    apply subgroupInclusionFactors (Specs.StandardGroups.spectrum k (Polynomial k)).property.1 H
    intro R x
    let t : R := Multiplicative.toAdd (G.additivePointsIso.hom.app R x)
    have hx : rootPoint (𝟙 G.additive.group) R t = x := by
      apply (G.additivePointsIso.app R).groupIsoToMulEquiv.injective
      exact G.additiveParameter R t
    change ∃ z : GroupPoints H.group R, z ≫ H.inclusion.hom.hom =
      x ≫ (G.root a ≫ G.group.inclusion).hom.hom
    rw [← hx]
    have hpoint : rootPoint (𝟙 G.additive.group) R t ≫
        (G.root a ≫ G.group.inclusion).hom.hom =
        rootPoint (G.root a ≫ G.group.inclusion) R t := by
      let p := (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval t : Polynomial k →ₐ[k] R)).op
      change (p ≫ 𝟙 _) ≫ (G.root a ≫ G.group.inclusion).hom.hom =
        p ≫ (G.root a ≫ G.group.inclusion).hom.hom
      rw [Category.comp_id]
    rw [hpoint]
    apply (hchar R _).mpr
    rw [G.rootMatrix]
    let := matrixAlgebra R
    let M := t • (algebraMap k R).mapMatrix (N a)
    have hM : Commute M (diag R) :=
      preservesBlock_commute (fun j => algebraMap k R (c j)) M (by
        intro j l h i q
        change t * (algebraMap k R (N a ⟨j, i⟩ ⟨l, q⟩)) = 0
        rw [hBlock a j l h i q, map_zero, mul_zero])
    obtain ⟨n, hn⟩ := ((hN a).map (algebraMap k R).mapMatrix).smul t
    change Commute (IsNilpotent.exp M) (diag R)
    rw [IsNilpotent.exp_eq_sum (show M ^ n = 0 from hn)]
    exact Commute.sum_left _ _ _ (fun m _ => (hM.pow_left m).smul_left _)
  obtain ⟨f, hf⟩ := G.generated H htorus hroot
  intro R g
  apply commutes_diagonal_blocks c hcInj
  apply (hchar R _).mp
  refine ⟨g ≫ f.hom.hom, ?_⟩
  rw [Category.assoc]
  change g ≫ (f ≫ H.inclusion).hom.hom = g ≫ G.group.inclusion.hom.hom
  rw [hf]

end
end MatrixGroupActions

section MarkedModelActions

open CategoryTheory AlgebraicGeometry
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField MatrixGroup Realization diagonalTorus exponentialMatrix matrixAlgebra)
open Specs.IntegralRootRelations (RootCoordinates root rootIndex)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.RootGroups (rootPoint IsRootSubgroup)
open private MatrixBorel MarkedMatrixRealization MarkedMatrixRealization.realization matrixTorus
  MatrixBorel.rootCharacter MatrixBorel.reductive MatrixBorel.maximal
  MarkedMatrixRealization.marking MarkedMatrixRealization.character_eq MarkedMatrixRealization.index_eq
  MarkedMatrixRealization.rootMap_eq MatrixBorel.pair matrixCharacter matrixCharacter_value diagonalCharacters_eq
  matrixGroup_root_coordinate rootPoint_change_coordinate exponentialMatrix_rescale
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open scoped Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

local instance : CharZero (RationalField.{u}) :=
  charZero_of_injective_ringHom
    (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
    (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective

variable {D : BasedRootDatum.{u}}
  {J : Type u} {I : J → Type u} [Fintype J] [DecidableEq J]
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {w : (Σ j, I j) → D.X}
  {N : D.I → Matrix (Σ j, I j) (Σ j, I j) RationalField.{u}}

private theorem matrixModel_markedTorus
    {G : MatrixGroup D RationalField.{u} (Σ j, I j) w N} {B : MatrixBorel G}
    (P : MarkedMatrixRealization B)
    (R : TestAlgebra RationalField.{u}) (t : GroupPoints (MarkedMatrixRealization.realization P).pinned.pair.T.group R) :
    ((matrixGroupPointAction G).app R (t ≫ (MarkedMatrixRealization.realization P).pinned.pair.T.inclusion.hom.hom)).val =
      Matrix.diagonal (fun j =>
        characterValue (markedCharacter (MarkedMatrixRealization.realization P) (w j)) R t) := by
  change ((G.matrixPoints.hom.app R).hom (t ≫ (G.torus ≫ G.group.inclusion).hom.hom)).val = _
  rw [G.torusMatrix]
  congr 1
  funext j
  have h : markedCharacter (MarkedMatrixRealization.realization P) (w j) = matrixCharacter RationalField.{u} D (w j) := by
    unfold markedCharacter
    change Additive.toMul ((MarkedMatrixRealization.marking P).val.weightEquiv (w j)) = _
    exact (congrArg Additive.toMul (MarkedMatrixRealization.character_eq P (w j))).trans
      (diagonalCharacters_eq RationalField.{u} D _)
  rw [h]
  exact (matrixCharacter_value G R t _).symm

/-- Rescaling a constructed root coordinate to the chosen Chevalley
coordinate gives the matching rescaled matrix exponential on every algebra. -/
private theorem matrixModel_markedRoots
    {G : MatrixGroup D RationalField.{u} (Σ j, I j) w N} {B : MatrixBorel G}
    (P : MarkedMatrixRealization B) (z : RootCoordinates (MarkedMatrixRealization.realization P))
    (hs : ∀ i : D.base.support, z i.val = (MarkedMatrixRealization.realization P).pinned.pin ((MarkedMatrixRealization.realization P).simpleRoot i))
    (hne : ∀ a, N a ≠ 0) (hshift : ∀ a i j, N a i j ≠ 0 → w i = w j + D.datum.root a) :
    ∃ c : D.I → RationalField.{u}ˣ,
      (∀ i : D.base.support, c i = 1) ∧
      ∀ a (R : TestAlgebra RationalField.{u}) (t : R),
        ((matrixGroupPointAction G).app R (root (MarkedMatrixRealization.realization P) z a R t)).val =
          exponentialMatrix ((c a : RationalField.{u}) • N a) R t := by
  classical
  have h (a : D.I) : ∃ c : RationalField.{u}ˣ,
      (∀ hi : a ∈ D.base.support, c = 1) ∧
      ∀ (R : TestAlgebra RationalField.{u}) (t : R),
        ((matrixGroupPointAction G).app R (root (MarkedMatrixRealization.realization P) z a R t)).val =
          exponentialMatrix ((c : RationalField.{u}) • N a) R t := by
    by_cases ha : a ∈ D.base.support
    · let i : D.base.support := ⟨a, ha⟩
      refine ⟨1, fun _ => rfl, fun R t => ?_⟩
      rw [Units.val_one, one_smul]
      have hmap : (z a).val.hom ≫ ((MarkedMatrixRealization.realization P).pinned.roots (rootIndex (MarkedMatrixRealization.realization P) a)).val.inclusion =
          G.root a := by
        have hh := congrArg (fun z => z.val.hom ≫
          ((MarkedMatrixRealization.realization P).pinned.roots (rootIndex (MarkedMatrixRealization.realization P) a)).val.inclusion) (hs i)
        exact hh.trans (MarkedMatrixRealization.rootMap_eq P i)
      unfold root
      rw [hmap]
      change ((G.matrixPoints.hom.app R).hom (rootPoint (G.root a) R t ≫ G.group.inclusion.hom.hom)).val = _
      rw [← rootPoint_comp, G.rootMatrix]
    · let U := (MarkedMatrixRealization.realization P).pinned.roots (rootIndex (MarkedMatrixRealization.realization P) a)
      have hU : IsRootSubgroup (matrixTorus G) U.val
          (matrixCharacter RationalField.{u} D (D.datum.root a)) := by
        have hchar : (rootIndex (MarkedMatrixRealization.realization P) a).val =
            matrixCharacter RationalField.{u} D (D.datum.root a) := by
          exact (congrArg Subtype.val (MarkedMatrixRealization.index_eq P a)).trans (MatrixBorel.rootCharacter B a)
        rw [← hchar]
        exact U.property
      obtain ⟨y, hy⟩ := matrixGroup_root_coordinate G (MatrixBorel.reductive B) (MatrixBorel.maximal B) a (hne a) (hshift a) U.val hU
      obtain ⟨c, hc⟩ := rootPoint_change_coordinate U.val (z a).val y
      refine ⟨c, fun hi => (ha hi).elim, ?_⟩
      intro R t
      rw [root, hc, hy]
      change ((G.matrixPoints.hom.app R).hom
        (rootPoint (G.root a) R (algebraMap RationalField.{u} R (c : RationalField.{u}) * t) ≫
          G.group.inclusion.hom.hom)).val = _
      rw [← rootPoint_comp, G.rootMatrix, exponentialMatrix_rescale]
  choose c hc hd using h
  exact ⟨c, fun i => hc i i.property, hd⟩

private theorem mapMatrix_blockDiagonal' {I₀ : Type*} {κ : I₀ → Type*}
    [Fintype I₀] [DecidableEq I₀] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (A : ∀ i : I₀, Matrix (κ i) (κ i) R) :
    f.mapMatrix (Matrix.blockDiagonal' A) = Matrix.blockDiagonal' (fun i => f.mapMatrix (A i)) :=
  blockDiagonal'_map f A

/-- Restrict a polynomial exponential to a block of a block-diagonal matrix. -/
private theorem exponentialMatrix_block {k : Type u} [Field k] [CharZero k]
    (M : ∀ j, Matrix (I j) (I j) k) (hm : IsNilpotent (Matrix.blockDiagonal' M))
    (R : TestAlgebra k) (t : R) (j : J) (a b : I j) :
    exponentialMatrix (Matrix.blockDiagonal' M) R t ⟨j, a⟩ ⟨j, b⟩ =
      exponentialMatrix (M j) R t a b := by
  let := matrixAlgebra R
  let T : ∀ j, Matrix (I j) (I j) R :=
    fun j => t • (algebraMap k R).mapMatrix (M j)
  let D := Matrix.blockDiagonal'RingHom I R
  have he : t • (algebraMap k R).mapMatrix (Matrix.blockDiagonal' M) = D T := by
    rw [mapMatrix_blockDiagonal', ← Matrix.blockDiagonal'_smul]
    rfl
  have hnil : IsNilpotent (D T) := he ▸ (hm.map (algebraMap k R).mapMatrix).smul t
  obtain ⟨n, hn⟩ := hnil
  have hnT : T ^ n = 0 := by
    apply Matrix.blockDiagonal'_injective
    change D (T ^ n) = D 0
    rw [map_pow, hn, map_zero]
  change IsNilpotent.exp (t • (algebraMap k R).mapMatrix (Matrix.blockDiagonal' M)) ⟨j, a⟩ ⟨j, b⟩ =
    IsNilpotent.exp (T j) a b
  rw [he, ← IsNilpotent.map_exp (show IsNilpotent T from ⟨n, hnT⟩) D]
  rw [show D (IsNilpotent.exp T) ⟨j, a⟩ ⟨j, b⟩ =
      (IsNilpotent.exp T j) a b from Matrix.blockDiagonal'_apply_eq _ _ _ _]
  exact congrArg (fun x : Matrix (I j) (I j) R => x a b)
    (IsNilpotent.map_exp (show IsNilpotent T from ⟨n, hnT⟩) (Pi.evalRingHom _ j))

end

end MarkedModelActions

section MarkedDifferentials

open CategoryTheory
open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization exponentialMatrix)
open Specs.IntegralRootRelations (RootCoordinates IsRootTangent root torus dualUnit)
open Specs.RootGroups (AdditiveLine)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.StandardGroups (generalLinearPoints)
open _root_.LinearAlgebraicGroups.RationalRealization (exponentialMatrix_of_sq_zero)

noncomputable section

set_option backward.isDefEq.respectTransparency false

local instance : CharZero (RationalField.{u}) :=
  charZero_of_injective_ringHom
    (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
    (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective

variable {D : BasedRootDatum.{u}} {A : AdditiveLine RationalField.{u}} {Q : Realization D A}
  {z : RootCoordinates Q} {J : Type u} [Fintype J] [DecidableEq J]

private theorem markedRootAction_differential
    (s : IdentityLieStructure Q.pinned.pair.G.val)
    (a : (groupPointsFunctor RationalField.{u}).obj Q.pinned.pair.G.val ⟶ generalLinearPoints RationalField.{u} J)
    (r : D.I) (x : Lie RationalField.{u} Q.pinned.pair.G.val) (hx : IsRootTangent Q z r x)
    (M : Matrix J J RationalField.{u})
    (hroot : ∀ (R : TestAlgebra RationalField.{u}) (t : R),
      (a.app R (root Q z r R t)).val = exponentialMatrix M R t) :
    lieActionOfPointAction s a x = M := by
  let K := RationalField.{u}
  let R := CommAlgCat.of K (DualNumber K)
  apply Matrix.ext
  intro i j
  rw [lieActionOfPointAction_apply, hx]
  change ((a.app R (root Q z r R DualNumber.eps)).val i j).snd = _
  rw [hroot, exponentialMatrix_of_sq_zero _ _ (DualNumber.eps_pow_two (R := K))]
  rw [Matrix.add_apply, Matrix.smul_apply, TrivSqZeroExt.snd_add]
  have h1 : ((1 : Matrix J J (DualNumber K)) i j).snd = 0 := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [h1, zero_add]
  change ((DualNumber.eps : DualNumber K) * TrivSqZeroExt.inl (M i j)).snd = M i j
  simp

private theorem markedTorusAction_differential
    (s : IdentityLieStructure Q.pinned.pair.G.val)
    (a : (groupPointsFunctor RationalField.{u}).obj Q.pinned.pair.G.val ⟶ generalLinearPoints RationalField.{u} J)
    (w : J → D.X) (y : D.Y) (x : Lie RationalField.{u} Q.pinned.pair.G.val)
    (hx : x.toMul.val = torus Q y (CommAlgCat.of _ (DualNumber RationalField.{u})) dualUnit)
    (htorus : ∀ (R : TestAlgebra RationalField.{u}) (t : GroupPoints Q.pinned.pair.T.group R),
      (a.app R (t ≫ Q.pinned.pair.T.inclusion.hom.hom)).val =
        Matrix.diagonal (fun i => characterValue (markedCharacter Q (w i)) R t)) :
    lieActionOfPointAction s a x =
      Matrix.diagonal (fun j => (D.datum.toLinearMap (w j) y : RationalField.{u})) := by
  let K := RationalField.{u}
  let R := CommAlgCat.of K (DualNumber K)
  let t := CocharacterDynamics.cocharacterPoint (markedCocharacter Q y) R dualUnit
  apply Matrix.ext
  intro i j
  rw [lieActionOfPointAction_apply, hx]
  change ((a.app R (t ≫ Q.pinned.pair.T.inclusion.hom.hom)).val i j).snd = _
  rw [htorus]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    dsimp only [t]
    rw [(RootData.CharacterPairing.characterPairingComposition _ _ _).2,
      markedCharacter_pairing, dual_unit_zpow_snd]
  · simp [hij]

end

end MarkedDifferentials

section RationalFundamentalIntegration

open CategoryTheory Module
open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization cyclicVector serreHighestRelations highestRelations
  generator loweringWord loweringWeight exponentialMatrix)
open Specs.IntegralRootRelations
  (RootCoordinates IsChevalley OppositeRootRelations IndependentRootRelations FormalBigCellProduct root)
open Specs.RootGroups (AdditiveLine)
open Specs.StandardGroups (generalLinearPoints)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralLattices
open _root_.LinearAlgebraicGroups.RationalRealization
  (rationalWeightBasis rationalWeightWords complexCartan serreStructure serreBaseChange)
open _root_.LinearAlgebraicGroups.Classification.IntegralRootRelations
  (integralRootRelationsForRealization simpleCorootEvaluations_injective)
open private normalizedRationalSerreRoots from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRootRelations
open private MarkedMatrixRealization.realization rationalSerre_brackets mapMatrix_diagonal hom_ext
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
open scoped Matrix

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

local instance : CharZero (RationalField.{u}) :=
  charZero_of_injective_ringHom
    (f := (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).toRingHom)
    (ULift.ringEquiv.symm : ℚ ≃+* RationalField.{u}).injective

set_option maxHeartbeats 2600000 in
set_option synthInstance.maxHeartbeats 90000 in
/-- Compare the marked matrix block actions with the cyclic presentations of
the fundamental highest-weight modules. -/
private theorem fundamentalActionsOfMatrixAction {D : BasedRootDatum.{u}}
    {A₀ : AdditiveLine RationalField.{u}} {Q : Realization D A₀} [DecidableEq D.base.support]
    (z : RootCoordinates Q)
    (hcor : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤)
    (ω : Basis D.base.support ℤ D.X)
    (hω : ∀ i j : D.base.support, D.datum.coroot' j (ω i) = if j = i then 1 else 0)
    (n : D.base.support → ℕ)
    (b : ∀ i, Basis (Index.{u} (n i)) ℚ (cyclicHighestWeight (ω i)))
    (words : ∀ i, Index.{u} (n i) → List D.base.support)
    (hwords : ∀ i j, b i j = loweringWord D (ω i) (words i j))
    (hhigh : ∀ i, ∃ j, words i j = [])
    (v : D.I → rationalSerreAlgebra D)
    (hSimple : ∀ i : D.base.support, v i = generator ℚ (datumCartanMatrix D) (.E i) ∧
      v (D.datum.reflectionPerm i i) = generator ℚ (datumCartanMatrix D) (.F i))
    (hChev : IsChevalley Q z) (hOpp : OppositeRootRelations Q z)
    (hInd : IndependentRootRelations Q z) (hCol : FormalBigCellProduct Q z) :
    let J := blockIndices n
    let w (j : J) := loweringWeight D (ω j.1) (words j.1 j.2)
    let N (a : D.I) := (algebraMap ℚ RationalField.{u}).mapMatrix (fundamentalMatrices ω n b (v a))
    ∀ (A : (groupPointsFunctor RationalField.{u}).obj Q.pinned.pair.G.val ⟶ generalLinearPoints RationalField.{u} J),
      (∀ (R : TestAlgebra RationalField.{u}) (g : GroupPoints Q.pinned.pair.G.val R) j l, j ≠ l →
        ∀ (i : Index.{u} (n j)) (q : Index.{u} (n l)), (A.app R g).val ⟨j, i⟩ ⟨l, q⟩ = 0) →
      (∀ (R : TestAlgebra RationalField.{u}) (t : GroupPoints Q.pinned.pair.T.group R),
        (A.app R (t ≫ Q.pinned.pair.T.inclusion.hom.hom)).val =
          Matrix.diagonal (fun j => Specs.CharacterPairing.characterValue (markedCharacter Q (w j)) R t)) →
      (∀ a, IsNilpotent (N a)) →
      ∀ (c : D.I → (RationalField.{u})ˣ), (∀ i : D.base.support, c i = 1) →
        (∀ a (R : TestAlgebra RationalField.{u}) (t : R), (A.app R (root Q z a R t)).val =
          exponentialMatrix ((c a : RationalField.{u}) • N a) R t) →
        HasRationalFundamentalActions z := by
  classical
  let := D.finiteRoots
  let := Fintype.ofFinite D.I
  let J := blockIndices n
  let w (j : J) := loweringWeight D (ω j.1) (words j.1 j.2)
  let F := algebraMap ℚ RationalField.{u}
  let N (a : D.I) := F.mapMatrix (fundamentalMatrices ω n b (v a))
  dsimp only
  intro A hpres hTor hN c hcs hRoot
  have hz := hChev
  obtain ⟨_, s, e, h, B', htan, Bh, Be, hop, hsum, _, hHH, hCartan, _⟩ := hz
  let := s.lieRing
  let := s.lieAlgebra
  letI : LieAlgebra ℚ (Lie RationalField.{u} Q.pinned.pair.G.val) :=
    inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)))
  letI : IsScalarTower ℚ RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val) :=
    IsScalarTower.restrictScalars ℚ RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)
  let U := UniversalEnvelopingAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)
  letI : Algebra ℚ U := Algebra.compHom U (algebraMap ℚ RationalField.{u})
  letI : IsScalarTower ℚ RationalField.{u} U := IsScalarTower.of_algebraMap_eq' rfl
  let opp (a : D.I) := D.datum.reflectionPerm a a
  have hopp (a : D.I) : ⁅e a, e (opp a)⁆ = h a := hop a (opp a) (by simp [opp])
  obtain ⟨f, hf, hfH, hfE, hfF⟩ := markedSerreMap s hcor e h B' Bh Be hHH hCartan hopp
    (fun a r t ht => by
      obtain ⟨p, q, m, hs, hm, hb, _⟩ := hsum a r t ht
      exact ⟨p, q, m, hs, hm, hb⟩)
  let Ψ := envelopingComparison (K := RationalField.{u}) f
  have hΨ := envelopingComparison_surjective f hf rationalCoefficient_surjective
  let Nᵢ (i : D.base.support) (a : D.I) := F.mapMatrix (cyclicBlock (b i) (v a))
  have hNb (a : D.I) : N a = Matrix.blockDiagonal' (fun i => Nᵢ i a) := by
    rw [show N a = F.mapMatrix (fundamentalMatrices ω n b (v a)) from rfl,
      fundamentalMatrices_val, mapMatrix_blockDiagonal']
  let At (i : D.base.support) := blockRepresentation A hpres i
  let d := lieActionOfPointAction s A
  have hdE (a : D.I) : d (e a) = (c a : RationalField.{u}) • N a :=
    markedRootAction_differential (z := z) s A a (e a) (htan a).1 _ (hRoot a)
  have hdH (a : D.I) : d (h a) = Matrix.diagonal (fun j => (D.datum.coroot' a (w j) : RationalField.{u})) :=
    markedTorusAction_differential s A w _ (h a) (htan a).2 hTor
  let H (i : D.base.support) := Matrix.diagonal (fun j : J => (D.datum.coroot' i (w j) : RationalField.{u}))
  have hHmatrix (i : D.base.support) :
      F.mapMatrix (fundamentalMatrices ω n b (generator ℚ (datumCartanMatrix D) (.H i))) = H i := by
    rw [fundamentalMatrices_val, mapMatrix_blockDiagonal']
    simp_rw [cyclicBlockCartan rationalWeightWords _ _ (hwords _)]
    simp_rw [mapMatrix_diagonal]
    rw [Matrix.blockDiagonal'_diagonal]
    congr 1
  have hcomm (i : D.base.support) : N i * N (opp i) - N (opp i) * N i = H i := by
    have h := (rationalSerre_brackets (datumCartanMatrix D)).2 i i
    rw [if_pos rfl, ← (hSimple i).1, ← (hSimple i).2] at h
    have hm := congrArg F.mapMatrix (congrArg (fundamentalMatrices ω n b) h)
    rw [(fundamentalMatrices ω n b).map_lie, Ring.lie_def, map_sub, map_mul, map_mul, hHmatrix] at hm
    exact hm
  have hcOpp (i : D.base.support) : (c (opp i) : RationalField.{u}) = 1 := by
    have he := d.map_lie (e i) (e (opp i))
    rw [hopp, hdH, hdE, hdE, hcs i, Units.val_one, one_smul, Ring.lie_def,
      Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hcomm] at he
    change H i = (c (opp i) : RationalField.{u}) • H i at he
    obtain ⟨j, hj⟩ := hhigh i
    have hw : w ⟨i, j⟩ = ω i := by simp [w, loweringWeight, hj]
    have hp := congrArg (fun M : Matrix J J RationalField.{u} => M ⟨i, j⟩ ⟨i, j⟩) he
    simp only [H, Matrix.smul_apply, Matrix.diagonal_apply_eq, hw, hω, ite_true,
      Int.cast_one] at hp
    change (1 : RationalField.{u}) = (c (opp i) : RationalField.{u}) * 1 at hp
    simpa only [mul_one] using hp.symm
  have hat (i : D.base.support) (R : TestAlgebra RationalField.{u}) (t : GroupPoints Q.pinned.pair.T.group R) :
      ((At i).app R (t ≫ Q.pinned.pair.T.inclusion.hom.hom)).val =
        Matrix.diagonal (fun j => Specs.CharacterPairing.characterValue (markedCharacter Q (w ⟨i, j⟩)) R t) := by
    apply Matrix.ext
    intro j l
    have ht : (A.app R (t ≫ Q.pinned.pair.T.inclusion.hom.hom)).val =
        Matrix.diagonal (fun j : J => Specs.CharacterPairing.characterValue (markedCharacter Q (w j)) R t) := hTor R t
    rw [blockRepresentation_val, ht]
    by_cases h : j = l
    · subst l
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · have hs : (⟨i, j⟩ : J) ≠ ⟨i, l⟩ :=
        fun he => h (eq_of_heq (Sigma.mk.inj he).2)
      rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ hs]
  have hnilBlock (i : D.base.support) (a : D.I) : IsNilpotent ((c a : RationalField.{u}) • Nᵢ i a) := by
    obtain ⟨r, hr⟩ := hN a
    change (N a) ^ r = 0 at hr
    rw [hNb, ← Matrix.blockDiagonal'_pow, ← Matrix.blockDiagonal'_zero] at hr
    have hp := congrFun (Matrix.blockDiagonal'_injective hr) i
    exact (show IsNilpotent (Nᵢ i a) from ⟨r, hp⟩).smul _
  have har (i : D.base.support) (a : D.I) (R : TestAlgebra RationalField.{u}) (t : R) :
      ((At i).app R (root Q z a R t)).val = exponentialMatrix ((c a : RationalField.{u}) • Nᵢ i a) R t := by
    apply Matrix.ext
    intro j l
    rw [blockRepresentation_val, hRoot]
    change exponentialMatrix ((c a : RationalField.{u}) • N a) R t ⟨i, j⟩ ⟨i, l⟩ = _
    rw [hNb, ← Matrix.blockDiagonal'_smul]
    have hnil : IsNilpotent (Matrix.blockDiagonal'
        ((c a : RationalField.{u}) • (fun i => Nᵢ i a))) := by
      rw [Matrix.blockDiagonal'_smul, ← hNb]
      exact (hN a).smul (c a : RationalField.{u})
    exact exponentialMatrix_block _ hnil R t i j l
  refine ⟨s, e, h, B', ω, hChev, hOpp, hInd, hCol, htan, Bh, Be,
    hopp, hCartan, (fun i j => by
      by_cases hji : j = i <;> simpa [hji] using hω i j), ?_⟩
  suffices hV : ∀ i : D.base.support, Nonempty (RationalHighestWeight z e h (ω i)) from
    ⟨fun i => (hV i).some⟩
  intro i
  let dᵢ := lieActionOfPointAction s (At i)
  let ρ := UniversalEnvelopingAlgebra.lift RationalField.{u} dᵢ
  letI : LieAlgebra ℚ (Matrix (Index.{u} (n i)) (Index.{u} (n i)) RationalField.{u}) :=
    inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ RationalField.{u} (Matrix (Index.{u} (n i)) (Index.{u} (n i)) RationalField.{u})))
  let cast : Matrix (Index.{u} (n i)) (Index.{u} (n i)) ℚ →ₐ[ℚ] Matrix (Index.{u} (n i)) (Index.{u} (n i)) RationalField.{u} :=
    { F.mapMatrix with
      commutes' := by
        intro r
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        apply Matrix.ext
        intro j l
        by_cases hj : j = l
        · subst l
          simp [F, Matrix.smul_apply]
        · simp [F, Matrix.one_apply_ne hj, Matrix.smul_apply] }
  have hD (a : D.I) : dᵢ (e a) = (c a : RationalField.{u}) • Nᵢ i a :=
    markedRootAction_differential (z := z) s (At i) a (e a) (htan a).1 _ (har i a)
  have hHd (a : D.I) : dᵢ (h a) =
      Matrix.diagonal (fun j => (D.datum.coroot' a (w ⟨i, j⟩) : RationalField.{u})) :=
    markedTorusAction_differential s (At i) (fun j => w ⟨i, j⟩) _ (h a) (htan a).2 (hat i)
  have hcomparison : (ρ.restrictScalars ℚ).comp Ψ = cast.comp (cyclicBlockAction (b i)) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply hom_ext (datumCartanMatrix D)
    intro x
    change ρ (Ψ (UniversalEnvelopingAlgebra.ι ℚ (generator ℚ (datumCartanMatrix D) x))) =
      F.mapMatrix (cyclicBlock (b i) (generator ℚ (datumCartanMatrix D) x))
    rw [envelopingComparison_apply, UniversalEnvelopingAlgebra.lift_ι_apply]
    cases x with
    | H j =>
      rw [hfH, hHd, cyclicBlockCartan rationalWeightWords _ _ (hwords i), mapMatrix_diagonal]
      congr 1
    | E j => rw [hfE, hD, hcs j, Units.val_one, one_smul, ← (hSimple j).1]
    | F j => rw [hfF, hD, hcOpp j, one_smul, ← (hSimple j).2]
  have hRels : highestWeightRelations e h (ω i) =
      Submodule.span U (Ψ.toRingHom '' serreHighestRelations D (ω i)) := by
    rw [highestWeightRelations_eq_simple s e h (ω i) (fun a r t ht => by
      obtain ⟨p, q, m, hs, hm, hb, _⟩ := hsum a r t ht
      exact ⟨p, q, m, hs, hm, hb⟩)]
    change _ = Submodule.span U (Ψ '' serreHighestRelations D (ω i))
    have hgen (x : CartanMatrix.Generators D.base.support) :
        Ψ (UniversalEnvelopingAlgebra.ι ℚ (generator ℚ (datumCartanMatrix D) x)) =
          UniversalEnvelopingAlgebra.ι RationalField.{u} (f (generator ℚ (datumCartanMatrix D) x)) :=
      envelopingComparison_apply f _
    congr 1
    simp only [serreHighestRelations, highestRelations, Set.image_union, ← Set.range_comp,
      Function.comp_def, hgen, hfE, hfH, hfF, map_sub, map_pow,
      map_intCast, Set.union_assoc]
  let v₀ (j : Index.{u} (n i)) := F ((b i).equivFun (cyclicVector (serreHighestRelations D (ω i))) j)
  obtain ⟨hcyc, hker⟩ := cyclicBlockPresentation (b i) Ψ.toRingHom hΨ ρ
    (fun a => DFunLike.congr_fun hcomparison a)
  obtain ⟨height, m, hm, hheight⟩ := exists_integralHeight D
  obtain ⟨j₀, hj₀⟩ := hhigh i
  obtain ⟨hb₀, hline⟩ := loweringWordBasis_highest_line (ω i) (b i) (words i) (hwords i)
    j₀ hj₀ height (fun j => by rw [hheight]; exact mul_pos hm (D.base.isPos_of_mem_support j.property))
  have hv₀ : v₀ = Pi.single j₀ 1 := by
    funext j
    change F ((b i).equivFun (cyclicVector _) j) = (Pi.single j₀ 1 : Index.{u} (n i) → RationalField.{u}) j
    rw [← hb₀]
    by_cases he : j = j₀
    · subst j
      simp [F]
    · simp [he, Ne.symm he, F]
  choose N₀ hN₀ using hnilBlock i
  let r := ∑ a : D.I, N₀ a
  have hPow (a : D.I) : ((c a : RationalField.{u}) • Nᵢ i a) ^ r = 0 :=
    pow_eq_zero_of_le (Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ a)) (hN₀ a)
  refine ⟨
    { dimension := n i
      highest := v₀
      highest_ne_zero := by
        rw [hv₀]
        intro h
        have he := congrFun h j₀
        simp at he
      envelopingAction := ρ
      cyclic := hcyc
      relations := fun a => by rw [hRels]; exact hker a
      weight := fun j => w ⟨i, j⟩
      highest_support := ?_
      highest_line := ?_
      nilpotenceBound := r
      nilpotent := ?_
      action := At i
      torus_action := hat i
      root_action := ?_ }⟩
  · intro j hj
    rw [hv₀]
    exact Pi.single_eq_of_ne (fun he => hj ((hline j).mpr he)) _
  · intro y hy
    rw [hv₀, Submodule.mem_span_singleton]
    refine ⟨y j₀, ?_⟩
    funext j
    by_cases he : j = j₀
    · subst j; simp
    · rw [Pi.smul_apply, Pi.single_eq_of_ne he, smul_zero, hy j (fun heq => he ((hline j).mp heq))]
  · intro a
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, hD]
    exact hPow a
  · intro a R t
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, hD, exponentialPolynomial_eval _ (hPow a)]
    exact har i a R t

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 90000 in
theorem rationalFundamentalActions : RationalFundamentalActions.{u} := by
  classical
  intro D hss hcor
  let := D.finiteRoots
  let := Fintype.ofFinite D.I
  let K := RationalField.{u}
  obtain ⟨ω, hω⟩ := fundamentalWeights_of_coroot_span D hss hcor
  have hdom (i j : D.base.support) : 0 ≤ D.datum.coroot' j (ω i) := by
    rw [hω]
    split <;> omega
  choose n b₀ words₀ hwords₀ hhigh₀ using
    fun i : D.base.support => rationalWeightBasis D (ω i) (hdom i)
  let b (i : D.base.support) := (b₀ i).reindex (Equiv.ulift : Index.{u} (n i) ≃ Fin (n i)).symm
  let words (i : D.base.support) (j : Index.{u} (n i)) := words₀ i j.down
  have hwords (i : D.base.support) (j : Index.{u} (n i)) : b i j = loweringWord D (ω i) (words i j) := by
    simp only [b, Basis.reindex_apply, Equiv.symm_symm]
    exact hwords₀ i j.down
  have hhigh (i : D.base.support) : ∃ j, words i j = [] := by
    obtain ⟨j, h⟩ := hhigh₀ i
    exact ⟨ULift.up j, h⟩
  obtain ⟨v, B₀, hv, hSimple, hB₀, hB₁, _, _, _⟩ :=
    normalizedRationalSerreRoots D complexCartan serreStructure serreBaseChange
      (simpleCorootEvaluations_injective D hcor)
  let J := blockIndices n
  let F := algebraMap ℚ K
  let N (a : D.I) := F.mapMatrix (fundamentalMatrices ω n b (v a))
  obtain ⟨hN, G, B, ⟨P⟩⟩ := fundamentalMatrixModel hss hcor ω n b words hwords hhigh v B₀ hv hB₀ hB₁
  let Q := MarkedMatrixRealization.realization P
  obtain ⟨z, hz, hOpp, hInd, hCol⟩ := integralRootRelationsForRealization D hss hcor G.additive Q
  let A := matrixGroupPointAction G
  let Nᵢ (i : D.base.support) (a : D.I) := F.mapMatrix (cyclicBlock (b i) (v a))
  have hNb (a : D.I) : N a = Matrix.blockDiagonal' (fun i => Nᵢ i a) := by
    rw [show N a = F.mapMatrix (fundamentalMatrices ω n b (v a)) from rfl,
      fundamentalMatrices_val, mapMatrix_blockDiagonal']
  have hpres := matrixModel_preserves_blocks G (fun a => (hN a).2.1) (by
    intro a i j hij p q
    change N a ⟨i, p⟩ ⟨j, q⟩ = 0
    rw [hNb, Matrix.blockDiagonal'_apply_ne _ _ _ hij])
  have hTor := matrixModel_markedTorus P
  obtain ⟨c, hcs, hRoot⟩ := matrixModel_markedRoots P z hz.1 (fun a => (hN a).1) (fun a => (hN a).2.2)
  exact ⟨G.additive, Q, z,
    fundamentalActionsOfMatrixAction (Q := Q) z hcor ω hω n b words hwords hhigh v hSimple
      hz hOpp hInd hCol A hpres hTor (fun a => (hN a).2.1) c hcs hRoot⟩

theorem integralLattices : Statement.{u} :=
  integralLattices_of_rational_actions rationalFundamentalActions

end
end RationalFundamentalIntegration


end LinearAlgebraicGroups.Classification.IntegralLattices
