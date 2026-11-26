import Specs.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
import LinearAlgebraicGroups.Solvable.Triangularization
import LinearAlgebraicGroups.Solvable.WordDomainGeometry
import LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import LinearAlgebraicGroups.Affine.Components
import LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj CategoryTheory.GrpObj commutatorElement TensorProduct BigOperators

universe u

namespace LinearAlgebraicGroups.EquivariantUnipotentSeries

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Specs.EquivariantUnipotentSeries
open Specs.Unipotent

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section Matrices

open Specs.Triangularization (upperTriangular)
open private Unipotent.difference Unipotent.difference_lower Unipotent.difference_upper
  Unipotent.rank_lt_of_height_lt from LinearAlgebraicGroups.Unipotent.CentralSeries

variable {n : ℕ} {R : Type u} [CommRing R]

private lemma triangular_mul_entry
    (A B N : Matrix (Index.{u} n) (Index.{u} n) R)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular)
    (hN : ∀ l m, m ≤ l → N l m = 0)
    (p : StrictUpper.{u} n)
    (hsmall : ∀ q : StrictUpper.{u} n, entryHeight q < entryHeight p → N q.1.1 q.1.2 = 0) :
    (A * N * B) p.1.1 p.1.2 = A p.1.1 p.1.1 * N p.1.1 p.1.2 * B p.1.2 p.1.2 := by
  classical
  obtain ⟨⟨i, j⟩, hij⟩ := p
  change (A * N * B) i j = _
  have hz (l m : Index.{u} n) (hil : i ≤ l) (hlm : l < m) (hmj : m ≤ j)
      (hne : l ≠ i ∨ m ≠ j) : N l m = 0 := by
    apply hsmall ⟨(l, m), hlm⟩
    have hi : i.down.val ≤ l.down.val := hil
    have hj : m.down.val ≤ j.down.val := hmj
    have hlt : l.down.val < m.down.val := hlm
    change m.down.val - l.down.val < j.down.val - i.down.val
    rcases hne with h | h
    · have : i < l := lt_of_le_of_ne hil (Ne.symm h)
      have : i.down.val < l.down.val := this
      omega
    · have : m < j := lt_of_le_of_ne hmj h
      have : m.down.val < j.down.val := this
      omega
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro l _ hli
      by_cases hil : i ≤ l
      · by_cases hlj : l < j
        · rw [hz l j hil hlj le_rfl (Or.inl hli), mul_zero]
        · rw [hN l j (le_of_not_gt hlj), mul_zero]
      · rw [hA (lt_of_not_ge hil), zero_mul]
    · simp
  · intro m _ hmj
    by_cases hm : m ≤ j
    · have hinner : (A * N) i m = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro l _
        by_cases hil : i ≤ l
        · by_cases hlm : l < m
          · rw [hz l m hil hlm hm (Or.inr hmj), mul_zero]
          · rw [hN l m (le_of_not_gt hlm), mul_zero]
        · rw [hA (lt_of_not_ge hil), zero_mul]
      rw [hinner, zero_mul]
    · rw [hB (lt_of_not_ge hm), mul_zero]
  · simp

/-- A triangular conjugation preserves the coordinate flag on unitriangular matrices. -/
theorem coordinateFlag_conjugation {s : ℕ} (g : upperTriangular (Index.{u} n) R)
    (x y : UnitriangularMatrix n R) (hy : InCoordinateFlag s x)
    (hconj : y.val = g.val * x.val * g.val⁻¹) : InCoordinateFlag s y := by
  intro p hp
  have hd : Unipotent.difference y = g.val.val * Unipotent.difference x * g⁻¹.val.val := by
    unfold Unipotent.difference
    rw [show y.val.val = g.val.val * x.val.val * g⁻¹.val.val from congrArg Units.val hconj]
    rw [mul_sub, sub_mul, mul_one, show g.val.val * g⁻¹.val.val = 1 from g.val.val_inv]
  rw [← Unipotent.difference_upper y, hd, triangular_mul_entry _ _ _ g.property g⁻¹.property
    (fun _ _ => Unipotent.difference_lower x) p]
  · rw [Unipotent.difference_upper, hy p hp, mul_zero, zero_mul]
  · intro q hq
    rw [Unipotent.difference_upper]
    exact hy q ((Unipotent.rank_lt_of_height_lt hq).trans hp)

end Matrices

section TriangularEmbedding

variable {k : Type u} [Field k]

open _root_.LinearAlgebraicGroups.Specs (IsSchemeKernel IsNormalSubgroup)
open Specs.Triangularization
open private groupPresentation schemeKernel_exists
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private SchemeDerivedGroup.kernel_normal
  from LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private Triangularization.diagonalMap Triangularization.diagonalMap_eq_one_iff
  Triangularization.kernelDiagonalPointsIso
  from LinearAlgebraicGroups.Solvable.Triangularization
open private Unipotent.kernel_points Unipotent.factor_through_closed Unipotent.closed_of_comp
  from LinearAlgebraicGroups.Unipotent.CentralSeries

private theorem groupLike_eq_one_of_invariant_vectors (A : HopfAlgebraCategory k)
    (hA : HasInvariantVectors A) {x : A} (hx : IsGroupLikeElem k x) : x = 1 := by
  let f : k →ₗ[k] k ⊗[k] A := LinearMap.toSpanSingleton k _ ((1 : k) ⊗ₜ[k] x)
  have hf (v : k) : f v = v ⊗ₜ[k] x := by
    rw [show f v = v • ((1 : k) ⊗ₜ[k] x) from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let ρ : RightComodule k A k :=
    { coaction := f
      coassoc v := by rw [hf, LinearMap.rTensor_tmul, hf, TensorProduct.assoc_tmul,
        LinearMap.lTensor_tmul, hx.comul_eq_tmul_self]
      counit v := by rw [hf, LinearMap.lTensor_tmul, hx.counit_eq_one,
        TensorProduct.rid_tmul, one_smul] }
  obtain ⟨v, hv, hfix⟩ := hA k ρ
  change v ∈ LinearMap.ker _ at hfix
  rw [LinearMap.mem_ker] at hfix
  have he : f v = v ⊗ₜ[k] (1 : A) := sub_eq_zero.mp hfix
  rw [hf] at he
  have hs : v • x = v • (1 : A) :=
    congrArg (TensorProduct.lid k A) he
  exact (smul_right_injective A hv) hs

/-- A split torus quotient with unipotent kernel provides a triangular embedding,
with no choice of section. -/
theorem exists_triangular_embedding (G T : AffineAlgebraicGroup k)
    (U : ClosedSubgroup G.val) (p : G.val ⟶ T.val) (hp : IsFppfGroupQuotient U p)
    (hT : IsSplitTorus T.val) (hU : IsUnipotent (closedSubgroupAlgebraicGroup U)) :
    EmbedsUpperTriangular G := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  obtain ⟨r, ⟨eT⟩⟩ := hT
  obtain ⟨ed⟩ := DiagonalizableGroups.diagonalIntegerPowers k (Index.{u} r)
  exact (Triangularization.triangularization G A e).2.2.mpr
    ⟨U, T, p, SchemeDerivedGroup.kernel_normal hp.1, hU, hp,
      Multiplicative (Index.{u} r → ℤ), inferInstance, inferInstance, ⟨eT.trans ed.symm⟩⟩

open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem unipotent_diagonal_points_eq_one (V : AffineAlgebraicGroup k)
    (hV : IsUnipotent V) (M : Type u) [CommGroup M] [Group.FG M]
    (f : V.val ⟶ (Specs.DiagonalizableGroups.diagonalGroup k M).val)
    (R : TestAlgebra k) (x : GroupPoints V.val R) : onPoints f R x = 1 := by
  obtain ⟨A, ⟨e⟩, hA⟩ := hV
  let B := Specs.DiagonalizableGroups.groupAlgebra k M
  let ff := AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let a : B ⟶ A := (ff.preimage (e.hom ≫ f)).unop
  have he : specGroupMap a = e.hom ≫ f := ff.map_preimage _
  have ha : a = hopfCounit B ≫ hopfUnit A := by
    apply CommHopfAlgCat.hom_ext
    apply MonoidAlgebra.bialgHom_ext
    · intro m
      have h := groupLike_eq_one_of_invariant_vectors A hA
        ((MonoidAlgebra.isGroupLikeElem_of m).map a.hom)
      change a.hom (MonoidAlgebra.of k M m) = 1 at h
      change a.hom (MonoidAlgebra.of k M m) =
        algebraMap k A (Coalgebra.counit (R := k) (MonoidAlgebra.of k M m))
      rw [(MonoidAlgebra.isGroupLikeElem_of m).counit_eq_one, map_one, h]
    · exact Subsingleton.elim _ _
  have ht : specGroupMap (hopfUnit A) ≫ specGroupMap (hopfCounit B) = e.hom ≫ f :=
    (specGroupMap_comp _ _).symm.trans ((congrArg (fun b : B ⟶ A => specGroupMap b) ha).symm.trans he)
  have hcomp : f = e.inv ≫ specGroupMap (hopfUnit A) ≫ specGroupMap (hopfCounit B) := by
    rw [ht, Iso.inv_hom_id_assoc]
  rw [hcomp]
  change onPoints (specGroupMap (hopfCounit B)) R
    (onPoints (specGroupMap (hopfUnit A)) R (onPoints e.inv R x)) = 1
  let c := hopfSpecPointIso (CommHopfAlgCat.of k k)
  let y := onPoints (specGroupMap (hopfUnit A)) R (onPoints e.inv R x)
  have hy : y = 1 := by
    apply ((c.app R).groupIsoToMulEquiv.symm.injective)
    apply WithConv.ofConv_injective
    exact Subsingleton.elim (α := k →ₐ[k] R) _ _
  rw [show onPoints (specGroupMap (hopfUnit A)) R (onPoints e.inv R x) = 1 from hy, map_one]

private theorem unipotent_multiplicative_power_points_eq_one (V : AffineAlgebraicGroup k)
    (hV : IsUnipotent V) (n : ℕ)
    (f : V.val ⟶ (StandardGroups.multiplicativePowerGroup k (Index.{u} n)).val)
    (R : TestAlgebra k) (x : GroupPoints V.val R) : onPoints f R x = 1 := by
  obtain ⟨e⟩ := DiagonalizableGroups.diagonalIntegerPowers k (Index.{u} n)
  apply (((groupPointsFunctor k).mapIso e.symm).app R).groupIsoToMulEquiv.injective
  change onPoints (f ≫ e.inv) R x = onPoints e.inv R 1
  rw [map_one]
  exact unipotent_diagonal_points_eq_one V hV _ _ R x


private theorem flag_normal {n : ℕ} {G T : AffineAlgebraicGroup k}
    (f : G.val ⟶ T.val)
    (e : (groupPointsFunctor k).obj T.val ≅ upperTriangularPoints k n)
    (K : ClosedSubgroup G.val) (hK : IsNormalSubgroup K.inclusion)
    (V : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj V.val ≅ unitriangularPoints k n)
    (a : K.group ⟶ V.val)
    (ha : ∀ (R : TestAlgebra k) (x : GroupPoints K.group R),
      (c.hom.app R (onPoints a R x)).val = (e.hom.app R (onPoints (K.inclusion ≫ f) R x)).val)
    {m : ℕ} (H : AffineAlgebraicGroup k) (b : H.val ⟶ K.group)
    (hb : ∀ (R : TestAlgebra k) (x : GroupPoints K.group R),
      InCoordinateFlag m (c.hom.app R (onPoints a R x)) ↔
        ∃ y : GroupPoints H.val R, onPoints b R y = x) :
    IsNormalSubgroup (b ≫ K.inclusion) := by
  classical
  have hpoints (R : TestAlgebra k) (g : GroupPoints G.val R) (y : GroupPoints H.val R) :
      ∃ z : GroupPoints H.val R, onPoints (b ≫ K.inclusion) R z =
        g * onPoints (b ≫ K.inclusion) R y * g⁻¹ := by
    obtain ⟨x, hx⟩ := normalSubgroup_conjugate_sections hK g (onPoints b R y)
    change onPoints K.inclusion R x =
      g * onPoints K.inclusion R (onPoints b R y) * g⁻¹ at hx
    let v : GroupPoints G.val R →* upperTriangular (Index.{u} n) R :=
      (e.hom.app R).hom.comp (onPoints f R)
    have hm : (c.hom.app R (onPoints a R x)).val =
        (v g).val * (c.hom.app R (onPoints a R (onPoints b R y))).val * (v g).val⁻¹ := by
      rw [ha R x, ha R (onPoints b R y)]
      change (v (onPoints K.inclusion R x)).val =
        (v g).val * (v (onPoints K.inclusion R (onPoints b R y))).val * (v g).val⁻¹
      rw [hx, map_mul, map_mul, map_inv]
      rfl
    obtain ⟨z, hz⟩ := (hb R x).mp
      (coordinateFlag_conjugation _ _ _ ((hb R _).mpr ⟨y, rfl⟩) hm)
    exact ⟨z, (congrArg (onPoints K.inclusion R) hz).trans hx⟩
  have := G.property.1
  have := H.property.1
  have hX : IsAffine (G.val.X ⊗ H.val.X).left := by
    rw [Over.tensorObj_left]
    infer_instance
  obtain ⟨A, ⟨i⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  obtain ⟨z, hz⟩ := hpoints A.unop (i.hom ≫ fst _ _) (i.hom ≫ snd _ _)
  change z ≫ (b ≫ K.inclusion).hom.hom =
    (i.hom ≫ fst G.val.X H.val.X) *
      ((i.hom ≫ snd G.val.X H.val.X) ≫ (b ≫ K.inclusion).hom.hom) *
      (i.hom ≫ fst G.val.X H.val.X)⁻¹ at hz
  have hz' : z ≫ (b ≫ K.inclusion).hom.hom =
      i.hom ≫ Specs.subgroupConjugation (b ≫ K.inclusion) := by
    simpa only [Specs.subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] using hz
  exact ⟨i.inv ≫ z, by rw [Category.assoc, hz', Iso.inv_hom_id_assoc]⟩

/-- Before taking reduced identity components, the coordinate series is normal
in the whole extension and has factors that are closed additive subgroups. -/
theorem exists_normal_central_series_with_additive_subgroup_factors
    (G T : AffineAlgebraicGroup k) (U : ClosedSubgroup G.val) (p : G.val ⟶ T.val)
    (hp : IsFppfGroupQuotient U p) (hT : IsSplitTorus T.val)
    (hU : IsUnipotent (closedSubgroupAlgebraicGroup U)) :
    ∃ (r : ℕ) (S : ClosedSeries (closedSubgroupAlgebraicGroup U) r),
      S.IsCentral ∧ S.HasAdditiveSubgroupFactors ∧
      ∀ i, IsNormalSubgroup (S.inclusion i ≫ U.inclusion) := by
  obtain ⟨n, B, ⟨e⟩, f, hf⟩ := exists_triangular_embedding G T U p hp hT hU
  have := (StandardGroups.multiplicativePowerGroup k (Index.{u} n)).property.1
  let d := Triangularization.diagonalMap e
  obtain ⟨N, hN⟩ := schemeKernel_exists d
  let V := closedSubgroupAlgebraicGroup N
  let c := Triangularization.kernelDiagonalPointsIso e N hN
  have hc : IsClosedImmersion (U.inclusion ≫ f).hom.hom.left := by
    have := U.isClosedImmersion
    have := hf
    change IsClosedImmersion (U.inclusion.hom.hom.left ≫ f.hom.hom.left)
    infer_instance
  obtain ⟨a, ha⟩ := Unipotent.factor_through_closed
    (A := closedSubgroupAlgebraicGroup U) (B := V) (C := B)
    (U.inclusion ≫ f) N.inclusion N.isClosedImmersion (fun R x => by
      apply (Unipotent.kernel_points d N hN R _).mp
      exact unipotent_multiplicative_power_points_eq_one
        (closedSubgroupAlgebraicGroup U) hU n ((U.inclusion ≫ f) ≫ d) R x)
  have hclosed := Unipotent.closed_of_comp a N.inclusion (ha ▸ hc) N.isClosedImmersion
  have ham (R : TestAlgebra k) (x : GroupPoints U.group R) :
      (c.hom.app R (onPoints a R x)).val =
        (e.hom.app R (onPoints (U.inclusion ≫ f) R x)).val := by
    rw [← ha]
    rfl
  obtain ⟨S, hS, hF, hflag⟩ := Unipotent.embeddedCentralSeries n
    (closedSubgroupAlgebraicGroup U) V c a hclosed
  refine ⟨_, S, hS, hF, fun i => ?_⟩
  exact flag_normal f e U (SchemeDerivedGroup.kernel_normal hp.1) V c a ham
    (S.term i) (S.inclusion i) (hflag i)

end TriangularEmbedding



section Reduction

variable {k : Type u} [Field k] {p : ℕ} [ExpChar k p]

private def frobeniusLinear (A : Type*) [CommRing A] [Algebra k A] [ExpChar A p] :
    A →ₛₗ[frobenius k p] A where
  toFun := frobenius A p
  map_add' := map_add _
  map_smul' r x := by
    simp only [Algebra.smul_def, map_mul, RingHom.map_frobenius]

/-- In positive characteristic, the tensor basis shows the Frobenius is injective. -/
private theorem tensorReduced_of_perfectRing
    [Fact p.Prime] [PerfectRing k p] (A B : Type*) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Nontrivial A] [Nontrivial B]
    [IsReduced A] [IsReduced B] : IsReduced (A ⊗[k] B) := by
  classical
  let : ExpChar A p := expChar_of_injective_algebraMap (algebraMap k A).injective p
  let : ExpChar B p := expChar_of_injective_algebraMap (algebraMap k B).injective p
  let : Nontrivial (A ⊗[k] B) :=
    (Algebra.TensorProduct.includeLeft_injective (S := k) (RingHom.injective (algebraMap k B))).nontrivial
  let : ExpChar (A ⊗[k] B) p :=
    expChar_of_injective_algebraMap (algebraMap k (A ⊗[k] B)).injective p
  let bA := Module.Free.chooseBasis k A
  let bB := Module.Free.chooseBasis k B
  let b := bA.tensorProduct bB
  let fA : A →ₛₗ[frobenius k p] A := frobeniusLinear A
  let fB : B →ₛₗ[frobenius k p] B := frobeniusLinear B
  let f : (A ⊗[k] B) →ₛₗ[frobenius k p] (A ⊗[k] B) := frobeniusLinear (A ⊗[k] B)
  have hA := bA.linearIndependent.map_of_surjective_injectiveₛ (frobenius k p)
    fA.toAddMonoidHom (surjective_frobenius k p)
    (frobenius_inj A p) fA.map_smulₛₗ
  have hB := bB.linearIndependent.map_of_surjective_injectiveₛ (frobenius k p)
    fB.toAddMonoidHom (surjective_frobenius k p)
    (frobenius_inj B p) fB.map_smulₛₗ
  have hlin : LinearIndependent k (f ∘ b) := by
    convert hA.tmul_of_flat_left hB using 1
    funext i
    dsimp only [b, Function.comp_apply]
    rw [Module.Basis.tensorProduct_apply']
    change (bA i.1 ⊗ₜ[k] bB i.2) ^ p = (bA i.1 ^ p) ⊗ₜ[k] (bB i.2 ^ p)
    exact Algebra.TensorProduct.tmul_pow (bA i.1) (bB i.2) p
  have hfin (x : A ⊗[k] B) : f x = 0 → x = 0 := by
    intro hx
    have he := congrArg f (b.linearCombination_repr x)
    have hz : ∑ i ∈ (b.repr x).support,
        frobenius k p (b.repr x i) • (f ∘ b) i = 0 := by
      rw [hx] at he
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, LinearMap.map_smulₛₗ, Function.comp_apply] using he
    apply b.repr.injective
    ext i
    by_cases hi : i ∈ (b.repr x).support
    · have h := (linearIndependent_iff'.mp hlin) _ _ hz i hi
      simpa using (injective_frobenius k p) (h.trans ((frobenius k p).map_zero).symm)
    · simpa using Finsupp.notMem_support_iff.mp hi
  have hinj : Function.Injective f := by
    intro x y h
    exact sub_eq_zero.mp (hfin _ (by rw [map_sub, h, sub_self]))
  constructor
  rintro x ⟨m, hm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m ≤ p ^ n := by
    exact ⟨m, m.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)⟩
  have hp : x ^ p ^ n = 0 := pow_eq_zero_of_le hn hm
  have hiter : (iterateFrobenius (A ⊗[k] B) p n) x = 0 := hp
  apply hinj.iterate n
  change (frobenius (A ⊗[k] B) p)^[n] x = (frobenius (A ⊗[k] B) p)^[n] 0
  rw [← coe_iterateFrobenius]
  exact hiter.trans ((iterateFrobenius (A ⊗[k] B) p n).map_zero).symm


private theorem nilradical_isHopfIdeal [Fact p.Prime] [PerfectRing k p]
    (A : HopfAlgebraCategory k) : (nilradical A).IsHopfIdeal k := by
  let I := nilradical A
  let q := Ideal.Quotient.mkₐ k I
  have hc (x : A) (hx : x ∈ I) : Bialgebra.counitAlgHom k A x = 0 :=
    IsReduced.eq_zero _ ((mem_nilradical.mp hx).map (Bialgebra.counitAlgHom k A))
  let c := Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom k A) hc
  let : Nontrivial (A ⧸ I) := c.toRingHom.domain_nontrivial
  let : _root_.IsReduced (A ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp (Ideal.radical_isRadical ⊥)
  let : _root_.IsReduced ((A ⧸ I) ⊗[k] (A ⧸ I)) := tensorReduced_of_perfectRing (p := p) _ _
  refine { toIsCoideal := ⟨hc, ?_⟩, antipode_mem := ?_ }
  · intro x hx
    change Algebra.TensorProduct.map q q (Coalgebra.comul (R := k) x) = 0
    exact IsReduced.eq_zero _ ((mem_nilradical.mp hx).map
      ((Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom k A)))
  · intro x hx
    exact mem_nilradical.mpr ((mem_nilradical.mp hx).map (HopfAlgebra.antipodeAlgHom k A))

end Reduction


section SmoothReduction

open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {k : Type u} [Field k] [PerfectField k]

private theorem factor_spectrum_through_reduction (A : CommRingCat.{u}) (X : Scheme.{u})
    [IsReduced X] (f : X ⟶ Spec A) :
    ∃ g : X ⟶ Spec (CommRingCat.of (A ⧸ nilradical A)),
      g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical A))) = f := by
  let adj := ΓSpec.adjunction
  let a : A ⟶ Γ(X, ⊤) := ((adj.homEquiv X (op A)).symm f).unop
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (nilradical A))
  let b : CommRingCat.of (A ⧸ nilradical A) ⟶ Γ(X, ⊤) :=
    CommRingCat.ofHom (Ideal.Quotient.lift (nilradical A) a.hom fun _ hx =>
      IsReduced.eq_zero _ ((mem_nilradical.mp hx).map a.hom))
  refine ⟨(adj.homEquiv X _ ) b.op, ?_⟩
  change (adj.homEquiv X _) b.op ≫ Scheme.Spec.map q.op = f
  rw [← adj.homEquiv_naturality_right b.op q.op]
  have he : b.op ≫ q.op = a.op := by
    apply Quiver.Hom.unop_inj
    rfl
  rw [he]
  exact (adj.homEquiv X (op A)).apply_symm_apply f

/-- The reduced closed subgroup of an affine algebraic group over a perfect
field is smooth and has the universal property of the reduction. -/
theorem exists_smooth_reduction (H : AffineAlgebraicGroup k) :
    ∃ D : ClosedSubgroup H.val, Smooth D.group.X.hom ∧
      Surjective D.inclusion.hom.hom.left ∧
      ∀ (X : SchemeOver k) [IsReduced X.left] (f : X ⟶ H.val.X),
        ∃ g : X ⟶ D.group.X, g ≫ D.inclusion.hom.hom = f := by
  classical
  rcases CharP.exists' k with h | ⟨p, hp, hkp⟩
  · let D : ClosedSubgroup H.val :=
      ⟨H.val, 𝟙 H.val, inferInstanceAs (IsClosedImmersion (𝟙 H.val.X.left))⟩
    exact ⟨D, characteristicZeroSmoothness k H,
      inferInstanceAs (Surjective (𝟙 H.val.X.left)), fun X _ f => ⟨f, Category.comp_id f⟩⟩
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation H
  let I := nilradical A
  let hI : I.IsHopfIdeal k := nilradical_isHopfIdeal (p := p) A
  let B := hopfQuotient A I
  let q := hopfQuotientMap A I
  let j := specGroupMap q
  let : IsClosedImmersion j.hom.hom.left :=
    (hopfMapClosedImmersion k q).mpr Ideal.Quotient.mk_surjective
  let : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
  let D : ClosedSubgroup H.val := ⟨specGroup B, j ≫ e.hom,
    inferInstanceAs (IsClosedImmersion (j.hom.hom.left ≫ e.hom.hom.hom.left))⟩
  let : _root_.IsReduced (A ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp (Ideal.radical_isRadical ⊥)
  let : LocallyOfFiniteType D.group.X.hom :=
    (closedSubgroupAlgebraicGroup D).property.2.1
  have hred : IsReduced D.group.X.left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of (A ⧸ I))))
  let : Surjective j.hom.hom.left := by
    rw [surjective_iff, ← Set.range_eq_univ]
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = Set.univ
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.zeroLocus_eq_univ_iff]
  refine ⟨D, smoothOfReducedOverPerfectField k D.group hred,
    inferInstanceAs (Surjective (j.hom.hom.left ≫ e.hom.hom.hom.left)), ?_⟩
  intro X _ f
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
  let f' : X.left ⟶ (specGroup A).X.left := f.left ≫ F.map e.inv
  obtain ⟨g, hg⟩ := factor_spectrum_through_reduction (CommRingCat.of A) X.left f'
  have he : g ≫ D.inclusion.hom.hom.left = f.left := by
    change g ≫ j.hom.hom.left ≫ F.map e.hom = _
    calc
      _ = (g ≫ j.hom.hom.left) ≫ F.map e.hom := (Category.assoc _ _ _).symm
      _ = f' ≫ F.map e.hom := congrArg (· ≫ F.map e.hom) hg
      _ = f.left := by
        dsimp only [f']
        rw [Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id]
        exact Category.comp_id (f.left : X.left ⟶ F.obj H.val)
  refine ⟨Over.homMk g ?_, ?_⟩
  · rw [← Over.w D.inclusion.hom.hom, ← Category.assoc, he, Over.w f]
  · exact Over.OverMorphism.ext he



/-- A finite product of multiplicative groups over a perfect field is smooth
and connected. -/
theorem split_torus_smooth_connected (T : AffineAlgebraicGroup k)
    (hT : IsSplitTorus T.val) : Smooth T.val.X.hom ∧ ConnectedSpace T.val.X.left := by
  obtain ⟨r, ⟨e⟩⟩ := hT
  let A := Specs.StandardGroups.LaurentPowerCoordinates k (Index.{u} r)
  let B := Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} r)
  let : IsDomain A := inferInstanceAs (IsDomain (AddMonoidAlgebra k (Index.{u} r → ℤ)))
  let : LocallyOfFiniteType B.val.X.hom := B.property.2.1
  let : Smooth B.val.X.hom := smoothOfReducedOverPerfectField k B.val
    (inferInstanceAs (IsReduced (Spec (CommRingCat.of A))))
  let : ConnectedSpace B.val.X.left := inferInstanceAs (ConnectedSpace (PrimeSpectrum A))
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
  have hf : IsIso e.hom.hom.hom.left := F.map_isIso e.hom
  exact ⟨by
    rw [← Over.w e.hom.hom.hom]
    infer_instance,
    (F.mapIso e).hom.homeomorph.connectedSpace_iff.mpr (inferInstanceAs (ConnectedSpace B.val.X.left))⟩

/-- The reduction of the identity component, characterized on reduced connected
pointed schemes. -/
structure ReducedIdentityComponent (H : AffineAlgebraicGroup k) where
  subgroup : ClosedSubgroup H.val
  smooth : Smooth subgroup.group.X.hom
  connected : ConnectedSpace subgroup.group.X.left
  open_range : IsOpen (Set.range subgroup.inclusion.hom.hom.left)
  factors (X : SchemeOver k) [IsReduced X.left] [ConnectedSpace X.left]
      (s : 𝟙_ (SchemeOver k) ⟶ X) (f : X ⟶ H.val.X) :
      s ≫ f = η[H.val.X] → ∃ g : X ⟶ subgroup.group.X, g ≫ subgroup.inclusion.hom.hom = f

/-- Maps from a reduced connected scheme taking its marked point to the identity
factor through the reduced identity component. -/
theorem exists_smooth_identity_component (H : AffineAlgebraicGroup k) :
    Nonempty (ReducedIdentityComponent H) := by
  obtain ⟨J, hs, hsurj, hJ⟩ := exists_smooth_reduction H
  let A := closedSubgroupAlgebraicGroup J
  obtain ⟨Q, D, q, i, hd, _, _, _⟩ := identityComponentAndQuotient k A
  have := J.isClosedImmersion
  have := hd.closedImmersion
  have := hd.openImmersion
  let I : ClosedSubgroup H.val :=
    ⟨D, i ≫ J.inclusion,
      inferInstanceAs (IsClosedImmersion (i.hom.hom.left ≫ J.inclusion.hom.hom.left))⟩
  have hsD : Smooth D.X.hom := by
    let : Smooth A.val.X.hom := hs
    rw [← Over.w i.hom.hom]
    infer_instance
  have hcD : ConnectedSpace D.X.left :=
    letI := hd.geometricallyConnected
    GeometricallyConnected.connectedSpace_of_subsingleton D.X.hom
  let j : A.val.X.left ⟶ H.val.X.left := J.inclusion.hom.hom.left
  let hsurj' := (surjective_iff _).mp hsurj
  let hq : Topology.IsQuotientMap j :=
    j.isClosedMap.isQuotientMap j.continuous hsurj'
  have ho : IsOpen (Set.range I.inclusion.hom.hom.left) := by
    apply hq.isOpen_preimage.mp
    change IsOpen (j ⁻¹' Set.range (i.hom.hom.left ≫ j))
    change IsOpen (j ⁻¹' Set.range (⇑j ∘ ⇑i.hom.hom.left))
    rw [Set.range_comp,
      Set.preimage_image_eq _ j.isClosedEmbedding.injective]
    exact i.hom.hom.left.isOpenEmbedding.isOpen_range
  refine ⟨⟨I, hsD, hcD, ho, ?_⟩⟩
  intro X _ _ s f hf
  obtain ⟨g, hg⟩ := hJ X f
  let : Mono J.inclusion.hom.hom := Over.mono_of_mono_left _
  have he : s ≫ g = η[A.val.X] := by
    apply (cancel_mono J.inclusion.hom.hom).mp
    rw [Category.assoc, hg, hf, IsMonHom.one_hom]
  let t : Spec (CommRingCat.of k) := Classical.choice inferInstance
  have ht : η[A.val.X].left t ∈ Set.range g.left := by
    refine ⟨s.left t, ?_⟩
    exact congrArg (fun h : 𝟙_ (SchemeOver k) ⟶ A.val.X => h.left t) he
  have hsub : Set.range g.left ⊆ Set.range i.hom.hom.left :=
    hd.identityComponent ▸ (isConnected_range g.left.continuous).subset_connectedComponent ht
  let z := IsOpenImmersion.lift i.hom.hom.left g.left hsub
  have hz : z ≫ i.hom.hom.left = g.left := IsOpenImmersion.lift_fac _ _ _
  let z' : X ⟶ D.X := Over.homMk z (by
    rw [← Over.w i.hom.hom, ← Category.assoc, hz]
    exact Over.w g)
  have hz' : z' ≫ i.hom.hom = g := Over.OverMorphism.ext hz
  exact ⟨z', (Category.assoc z' i.hom.hom J.inclusion.hom.hom).symm.trans
    ((congrArg (· ≫ J.inclusion.hom.hom) hz').trans hg)⟩


/-- Normality in a smooth connected ambient group is preserved on passing to the
reduced identity component of a normal closed subgroup. -/
theorem smooth_identity_component_normal {G : AffineAlgebraicGroup k}
    (hG : Smooth G.val.X.hom) (hcG : ConnectedSpace G.val.X.left)
    (H : ClosedSubgroup G.val) (hH : Specs.IsNormalSubgroup H.inclusion)
    (C : ReducedIdentityComponent (closedSubgroupAlgebraicGroup H)) :
    Specs.IsNormalSubgroup (C.subgroup.inclusion ≫ H.inclusion) := by
  let D := C.subgroup
  have hs := C.smooth
  have hc := C.connected
  have hD := C.factors
  let V := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup H) D
  let X := G.val.X ⊗ D.group.X
  have hX := WordDomainGeometry.smoothConnectedGroupProduct G V hG hcG hs hc
  have : IsIntegral X.left := hX.2.2
  have : IsReduced X.left := inferInstance
  have : ConnectedSpace X.left := hX.2.1
  let g := fst G.val.X D.group.X
  let v := snd G.val.X D.group.X
  obtain ⟨b, hb⟩ := normalSubgroup_conjugate_sections hH g (v ≫ D.inclusion.hom.hom)
  let o : 𝟙_ (SchemeOver k) ⟶ X := lift η[G.val.X] η[D.group.X]
  have := H.isClosedImmersion
  have : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  have hb1 : o ≫ b = η[H.group.X] := by
    apply (cancel_mono H.inclusion.hom.hom).mp
    rw [Category.assoc, hb, IsMonHom.one_hom]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, o, g, v,
      lift_fst, lift_snd, IsMonHom.one_hom]
    change (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) * 1 * 1⁻¹ = 1
    simp
  obtain ⟨c, hc⟩ := hD X o b hb1
  refine ⟨c, ?_⟩
  change (c ≫ D.inclusion.hom.hom ≫ H.inclusion.hom.hom) = _
  rw [← Category.assoc, hc, hb]
  rfl

end SmoothReduction


section SemidirectProduct

variable {k : Type u} [Field k] {T U : GroupScheme k}

/-- The given algebraic action induces an action by group automorphisms over each test ring. -/
def pointAction (a : AutomorphismAction T U) (R : TestAlgebra k) :
    GroupPoints T R →* MulAut (GroupPoints U R) where
  toFun t :=
    { toFun := fun x => lift t x ≫ a.action
      invFun := fun x => lift t⁻¹ x ≫ a.action
      left_inv x := by
        change lift t⁻¹ (lift t x ≫ a.action) ≫ a.action = x
        rw [← a.mul_act, inv_mul_cancel, a.one_act]
      right_inv x := by
        change lift t (lift t⁻¹ x ≫ a.action) ≫ a.action = x
        rw [← a.mul_act, mul_inv_cancel, a.one_act]
      map_mul' := a.act_mul R t }
  map_one' := MulEquiv.ext (a.one_act R)
  map_mul' s t := MulEquiv.ext (a.mul_act R s t)

private def semidirectPointsEquiv (a : AutomorphismAction T U) (R : TestAlgebra k) :
    Points (U.X ⊗ T.X) R ≃ GroupPoints U R ⋊[pointAction a R] GroupPoints T R where
  toFun z := ⟨z ≫ fst _ _, z ≫ snd _ _⟩
  invFun z := lift z.left z.right
  left_inv z := by simp
  right_inv z := by ext <;> simp

private abbrev changeTestAlgebra (G : GroupScheme k) {R S : TestAlgebra k} (f : R ⟶ S) :
    GroupPoints G R →* GroupPoints G S :=
  (((groupPointsFunctor k).obj G).map f).hom

private lemma pointAction_natural (a : AutomorphismAction T U)
    {R S : TestAlgebra k} (f : R ⟶ S) (t : GroupPoints T R) (x : GroupPoints U R) :
    changeTestAlgebra U f (pointAction a R t x) =
      pointAction a S (changeTestAlgebra T f t) (changeTestAlgebra U f x) := by
  let b := (testSpec k).map f.op
  change b ≫ (lift t x ≫ a.action) = lift (b ≫ t) (b ≫ x) ≫ a.action
  rw [← Category.assoc, comp_lift]

private lemma semidirectPointsEquiv_natural (a : AutomorphismAction T U)
    {R S : TestAlgebra k} (f : R ⟶ S) (z : Points (U.X ⊗ T.X) R) :
    semidirectPointsEquiv a S (mapPoints f z) =
      ⟨changeTestAlgebra U f (semidirectPointsEquiv a R z).left,
        changeTestAlgebra T f (semidirectPointsEquiv a R z).right⟩ := by
  apply SemidirectProduct.ext <;> exact Category.assoc _ _ _

/-- The point functor of the product scheme carries the natural semidirect product law. -/
def semidirectProductLaw (a : AutomorphismAction T U) : NaturalGroupLaw (U.X ⊗ T.X) where
  group R := (semidirectPointsEquiv a R).group
  map_one {R S} f := by
    let eR := semidirectPointsEquiv a R
    let eS := semidirectPointsEquiv a S
    apply eS.injective
    change eS (mapPoints f (eR.symm 1)) = eS (eS.symm 1)
    rw [semidirectPointsEquiv_natural]
    simp only [eR, eS, Equiv.apply_symm_apply, SemidirectProduct.one_left,
      SemidirectProduct.one_right, map_one]
    rfl
  map_mul {R S} f z w := by
    let eR := semidirectPointsEquiv a R
    let eS := semidirectPointsEquiv a S
    apply eS.injective
    change eS (mapPoints f (eR.symm (eR z * eR w))) =
      eS (eS.symm (eS (mapPoints f z) * eS (mapPoints f w)))
    rw [Equiv.apply_symm_apply]
    simp only [eR, eS, semidirectPointsEquiv_natural, Equiv.apply_symm_apply]
    apply SemidirectProduct.ext <;>
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        map_mul, pointAction_natural]


/-- The natural semidirect product law is represented by a group scheme
on the product of the two affine schemes. -/
theorem semidirectProduct_representable (U T : AffineAlgebraicGroup k)
    (a : AutomorphismAction T.val U.val) :
    ∃ h : GrpObj (U.val.X ⊗ T.val.X),
      inducedGroupLaw (U.val.X ⊗ T.val.X) h = semidirectProductLaw a := by
  have := U.property.1
  have := T.property.1
  have hX : IsAffine (U.val.X ⊗ T.val.X).left := by
    rw [Over.tensorObj_left]
    infer_instance
  exact (groupLawComparison k _ hX).surjective (semidirectProductLaw a)

end SemidirectProduct




open Polynomial in
/-- Over a reduced ring, an invertible polynomial substitution fixing zero is linear. -/
theorem polynomial_eq_linear_of_comp_eq_X {A : Type*} [CommRing A] [IsReduced A]
    (P Q : A[X]) (hzero : P.coeff 0 = 0) (hcomp : P.comp Q = X) :
    P = C (P.coeff 1) * X := by
  have hd (n : ℕ) (hn : 1 < n) : P.coeff n = 0 := by
    apply IsReduced.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    let f := Ideal.Quotient.mk J
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change f (P.coeff n) = 0
    rw [← coeff_map]
    have h := congrArg (map f) hcomp
    simp only [map_comp, map_X] at h
    have hdeg := congrArg natDegree h
    rw [natDegree_comp, natDegree_X] at hdeg
    exact coeff_eq_zero_of_natDegree_lt ((Nat.eq_one_of_mul_eq_one_right hdeg) ▸ hn)
  ext n
  rcases n with _ | n
  · simpa using hzero
  rcases n with _ | n
  · simp
  rw [hd _ (by omega), coeff_C_mul, coeff_X]
  simp

section QuotientMaps

open _root_.LinearAlgebraicGroups.Specs
open Specs.HomogeneousQuotient (rightMultiplication)
open private WordDomainGeometry.geometricallyConnected_of_connected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open CategoryTheory.MonoidalCategory
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private tensorHom_property from LinearAlgebraicGroups.Affine.Components

variable {k : Type u} [Field k]

private lemma epiOver_of_flat_surjective {X Y : SchemeOver k} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] : Epi f :=
  (Over.forget _).epi_of_epi_map (Flat.epi_of_flat_of_surjective f.left)

private lemma sections_comp {G H : GroupScheme k} {X : SchemeOver k}
    (f : G ⟶ H) (x y : X ⟶ G.X) :
    (x * y) ≫ f.hom.hom = (x ≫ f.hom.hom) * (y ≫ f.hom.hom) := by
  exact (IsMonHom.monoidHom f.hom.hom X).map_mul x y

private lemma sections_inv {G H : GroupScheme k} {X : SchemeOver k}
    (f : G ⟶ H) (x : X ⟶ G.X) :
    x⁻¹ ≫ f.hom.hom = (x ≫ f.hom.hom)⁻¹ := by
  change (x ≫ ι[G.X]) ≫ f.hom.hom = (x ≫ f.hom.hom) ≫ ι[H.X]
  rw [Category.assoc, GrpObj.inv_hom, Category.assoc]

private lemma sections_one {G H : GroupScheme k} {X : SchemeOver k}
    (f : G ⟶ H) : (1 : X ⟶ G.X) ≫ f.hom.hom = 1 := by
  change (toUnit X ≫ η[G.X]) ≫ f.hom.hom = toUnit X ≫ η[H.X]
  rw [Category.assoc, IsMonHom.one_hom]

private lemma difference_in_kernel {G H : GroupScheme k} {N : ClosedSubgroup G}
    {p : G ⟶ H} (hp : IsSchemeKernel p N) {X : SchemeOver k} {x y : X ⟶ G.X}
    (h : x ≫ p.hom.hom = y ≫ p.hom.hom) :
    ∃ v : X ⟶ N.group.X, x * (v ≫ N.inclusion.hom.hom) = y := by
  have hv : (x⁻¹ * y) ≫ p.hom.hom = 1 := by
    rw [sections_comp p, sections_inv p, h, inv_mul_cancel]
  obtain ⟨v, hv⟩ := (schemeKernel_sections hp _).mpr hv
  change v ≫ N.inclusion.hom.hom = x⁻¹ * y at hv
  exact ⟨v, by rw [hv, mul_inv_cancel_left]⟩

private theorem descendOver {X Y Z : SchemeOver k} (p : X ⟶ Y) (f : X ⟶ Z)
    [Flat p.left] [Surjective p.left] [QuasiCompact p.left]
    (h : ∀ {W : SchemeOver k} (a b : W ⟶ X), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    ∃ g : Y ⟶ Z, p ≫ g = f := by
  letI : EffectiveEpi p.left := inferInstance
  let l := pullback.fst p p
  let r := pullback.snd p p
  have hp := (Over.forget (Spec (CommRingCat.of k))).map_isPullback (IsPullback.of_hasPullback p p)
  have hf : l.left ≫ f.left = r.left ≫ f.left :=
    congrArg (fun x : pullback p p ⟶ Z => x.left) (h l r pullback.condition)
  obtain ⟨g, hg⟩ := IsRegularEpi.exists_of_isKernelPair p.left hp f.left hf
  have hw : g ≫ Z.hom = Y.hom := by
    letI : Epi p.left := Flat.epi_of_flat_of_surjective p.left
    rw [← cancel_epi p.left, ← Category.assoc, hg, Over.w f, Over.w p]
  exact ⟨Over.homMk g hw, Over.OverMorphism.ext hg⟩

private theorem liftGroupHomOfQuotient {G H A : AffineAlgebraicGroup k}
    {N : ClosedSubgroup G.val} (p : G.val ⟶ H.val) (hp : IsFppfGroupQuotient N p)
    (f : G.val ⟶ A.val) (hf : N.inclusion.hom.hom ≫ f.hom.hom = 1) :
    ∃ g : H.val ⟶ A.val, p ≫ g = f := by
  letI := G.property.1
  letI := H.property.1
  letI := hp.2.1
  letI := hp.2.2.1
  letI : QuasiCompact p.hom.hom.left := inferInstance
  obtain ⟨g, hg⟩ := descendOver p.hom.hom f.hom.hom (fun a b hab => by
    obtain ⟨v, hv⟩ := difference_in_kernel hp.1 hab
    rw [← hv, sections_comp f, Category.assoc, hf, MonObj.comp_one, mul_one])
  letI : Flat (p.hom.hom ⊗ₘ p.hom.hom).left := tensorHom_property _ _ @Flat hp.2.1 hp.2.1
  letI : Surjective (p.hom.hom ⊗ₘ p.hom.hom).left :=
    tensorHom_property _ _ @Surjective hp.2.2.1 hp.2.2.1
  letI : Epi (p.hom.hom ⊗ₘ p.hom.hom) := epiOver_of_flat_surjective _
  have h₁ : η[H.val.X] ≫ g = η[A.val.X] := by
    rw [← IsMonHom.one_hom p.hom.hom, Category.assoc, hg, IsMonHom.one_hom]
  have h₂ : μ[H.val.X] ≫ g = (g ⊗ₘ g) ≫ μ[A.val.X] := by
    rw [← cancel_epi (p.hom.hom ⊗ₘ p.hom.hom), ← IsMonHom.mul_hom_assoc, hg,
      IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hg]
  exact ⟨Grp.homMk'' g h₁ h₂, Grp.hom_ext _ _ hg⟩

private theorem quotient_kernel_pair {G H : GroupScheme k} {N : ClosedSubgroup G}
    {p : G ⟶ H} (hp : IsSchemeKernel p N) :
    IsPullback (prod.fst : G.X ⨯ N.group.X ⟶ G.X) (rightMultiplication N)
      p.hom.hom p.hom.hom := by
  have hmul {X : SchemeOver k} (z : X ⟶ G.X ⨯ N.group.X) :
      z ≫ rightMultiplication N =
        (z ≫ prod.fst) * ((z ≫ prod.snd) ≫ N.inclusion.hom.hom) := by
    simp [rightMultiplication, MonObj.comp_mul, Category.assoc]
  have hcomm : (prod.fst : G.X ⨯ N.group.X ⟶ G.X) ≫ p.hom.hom =
      rightMultiplication N ≫ p.hom.hom := by
    let y : G.X ⨯ N.group.X ⟶ N.group.X := prod.snd
    have h := (schemeKernel_sections hp (y ≫ N.inclusion.hom.hom)).mp ⟨y, rfl⟩
    have hr := sections_comp p (prod.fst : G.X ⨯ N.group.X ⟶ G.X)
      (prod.snd ≫ N.inclusion.hom.hom)
    rw [h, mul_one] at hr
    exact hr.symm
  have h (s : PullbackCone p.hom.hom p.hom.hom) :
      ∃ a : s.pt ⟶ N.group.X, s.fst * (a ≫ N.inclusion.hom.hom) = s.snd :=
    difference_in_kernel hp s.condition
  choose a ha using h
  letI := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk hcomm
    (fun s => prod.lift s.fst (a s)) (fun s => prod.lift_fst _ _) (fun s => ?_)
    (fun s z hz₁ hz₂ => ?_))
  · rw [hmul, prod.lift_fst, prod.lift_snd, ha]
  · apply prod.hom_ext
    · rw [hz₁, prod.lift_fst]
    · rw [prod.lift_snd, ← cancel_mono N.inclusion.hom.hom, ← mul_right_inj (a := s.fst)]
      simpa only [ha, hmul, hz₁] using hz₂

private theorem extension_smooth_connected (G T : AffineAlgebraicGroup k)
    (U : ClosedSubgroup G.val) (p : G.val ⟶ T.val) (hp : IsFppfGroupQuotient U p)
    (hsT : Smooth T.val.X.hom) (hcT : ConnectedSpace T.val.X.left)
    (hsU : Smooth U.group.X.hom) (hcU : ConnectedSpace U.group.X.left) :
    Smooth G.val.X.hom ∧ ConnectedSpace G.val.X.left := by
  letI := G.property.1
  letI := T.property.1
  letI := hp.2.1
  letI := hp.2.2.1
  letI := hp.2.2.2.1
  letI : QuasiCompact p.hom.hom.left := inferInstance
  letI := hsT
  letI := hcT
  letI := hcU
  letI : GeometricallyConnected U.group.X.hom :=
    @WordDomainGeometry.geometricallyConnected_of_connected k _ (closedSubgroupAlgebraicGroup U) hcU
  have hprod := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd G.val.X U.group.X)
  have hsm : Smooth (prod.fst : G.val.X ⨯ U.group.X ⟶ G.val.X).left :=
    MorphismProperty.of_isPullback (P := @Smooth) hprod.flip hsU
  have hgeom : GeometricallyConnected (prod.fst : G.val.X ⨯ U.group.X ⟶ G.val.X).left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hprod.flip inferInstance
  have hpair := ((quotient_kernel_pair hp.1).map (Over.forget _))
  have hfp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      p.hom.hom.left := ⟨⟨hp.2.2.1, hp.2.1⟩, inferInstance⟩
  letI : Smooth p.hom.hom.left := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) hpair hfp hsm
  letI : GeometricallyConnected (pullback.snd p.hom.hom.left p.hom.hom.left) := by
    let e := hpair.isoPullback ≪≫ pullbackSymmetry p.hom.hom.left p.hom.hom.left
    have hr : e.hom ≫ pullback.snd _ _ = (prod.fst : G.val.X ⨯ U.group.X ⟶ G.val.X).left := by
      simp [e]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected e.hom _).mp
      (hr.symm ▸ hgeom : GeometricallyConnected (e.hom ≫ pullback.snd _ _))
  letI : GeometricallyConnected p.hom.hom.left :=
    geometricallyConnectedOfSurjectiveBaseChange p.hom.hom.left p.hom.hom.left
  exact ⟨by rw [← Over.w p.hom.hom]; infer_instance,
    GeometricallyConnected.connectedSpace p.hom.hom.left p.hom.hom.left.isOpenMap⟩

end QuotientMaps

section ReducedSeries

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.MonoidalCategory
open private Unipotent.closed_of_comp from LinearAlgebraicGroups.Unipotent.CentralSeries
open private Unipotent.closedSeries_inclusion_closed Unipotent.closedSeries_commutator
    from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

variable {k : Type u} [Field k] [PerfectField k]

private abbrev ReducedIdentityComponent.group {H : AffineAlgebraicGroup k}
    (C : ReducedIdentityComponent H) := closedSubgroupAlgebraicGroup C.subgroup

private abbrev ReducedIdentityComponent.inclusion {H : AffineAlgebraicGroup k}
    (C : ReducedIdentityComponent H) := C.subgroup.inclusion

private theorem ReducedIdentityComponent.factorHom {H A : AffineAlgebraicGroup k}
    (C : ReducedIdentityComponent H) (f : A.val ⟶ H.val)
    (hs : Smooth A.val.X.hom) (hc : ConnectedSpace A.val.X.left) :
    ∃ g : A.val ⟶ C.group.val, g ≫ C.inclusion = f := by
  letI : ConnectedSpace A.val.X.left := hc
  letI : Smooth A.val.X.hom := hs
  letI : IsReduced A.val.X.left := isReduced_of_smooth_over_field A.val.X.hom
  obtain ⟨g, hg⟩ := C.factors A.val.X η[A.val.X] f.hom.hom (IsMonHom.one_hom _)
  letI := C.subgroup.isClosedImmersion
  letI : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
  have hone : η[A.val.X] ≫ g = η[C.group.val.X] := by
    rw [← cancel_mono C.inclusion.hom.hom, Category.assoc, hg, IsMonHom.one_hom,
      IsMonHom.one_hom]
  have hmul : μ[A.val.X] ≫ g = (g ⊗ₘ g) ≫ μ[C.group.val.X] := by
    rw [← cancel_mono C.inclusion.hom.hom, Category.assoc, hg, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hg]
  exact ⟨Grp.homMk'' g hone hmul, Grp.hom_ext _ _ hg⟩

private theorem ReducedIdentityComponent.isIso_inclusion {H : AffineAlgebraicGroup k}
    (C : ReducedIdentityComponent H) (hs : Smooth H.val.X.hom)
    (hc : ConnectedSpace H.val.X.left) : IsIso C.inclusion := by
  obtain ⟨g, hg⟩ := C.factorHom (𝟙 H.val) hs hc
  let := C.subgroup.isClosedImmersion
  let : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
  let : Mono C.inclusion := (Grp.forget _).mono_of_mono_map ‹_›
  exact ⟨⟨g, (cancel_mono C.inclusion).mp (by simp [hg]), hg⟩⟩

private theorem ReducedIdentityComponent.normal_chain {G H : AffineAlgebraicGroup k}
    (hG : Smooth G.val.X.hom) (hcG : ConnectedSpace G.val.X.left)
    (i : H.val ⟶ G.val) (hi : IsClosedImmersion i.hom.hom.left)
    (hn : IsNormalSubgroup i) (C : ReducedIdentityComponent H) :
    IsNormalSubgroup (C.inclusion ≫ i) := by
  let J : ClosedSubgroup G.val := ⟨_, i, hi⟩
  exact smooth_identity_component_normal hG hcG J hn C

private theorem normal_in_subgroup {G H V : GroupScheme k}
    {f : H ⟶ G} (hf : IsClosedImmersion f.hom.hom.left) {j : V ⟶ H}
    (h : IsNormalSubgroup (j ≫ f)) : IsNormalSubgroup j := by
  letI := hf
  letI : Mono f.hom.hom := Over.mono_of_mono_left _
  obtain ⟨c, hc⟩ := normalSubgroup_conjugate_sections h
    (fst H.X V.X ≫ f.hom.hom) (snd H.X V.X)
  refine ⟨c, (cancel_mono f.hom.hom).mp ?_⟩
  change c ≫ (j ≫ f).hom.hom = _
  rw [hc]
  change _ = (fst H.X V.X * (snd H.X V.X ≫ j.hom.hom) * (fst H.X V.X)⁻¹) ≫ f.hom.hom
  rw [sections_comp, sections_comp, sections_inv, Category.assoc]
  rfl

private theorem ReducedIdentityComponent.central_chain
    {V : AffineAlgebraicGroup k} {r i : ℕ} (S : ClosedSeries V r)
    (hi : i < r) (hS : S.IsCentral)
    (hsV : Smooth V.val.X.hom) (hcV : ConnectedSpace V.val.X.left)
    (C : ReducedIdentityComponent (S.term i))
    (D : ReducedIdentityComponent (S.term (i + 1))) :
    ∀ {X : SchemeOver k} (g : X ⟶ V.val.X) (v : X ⟶ C.group.val.X),
      ∃ w : X ⟶ D.group.val.X, w ≫ (D.inclusion ≫ S.inclusion (i + 1)).hom.hom =
        g * (v ≫ (C.inclusion ≫ S.inclusion i).hom.hom) * g⁻¹ *
          (v ≫ (C.inclusion ≫ S.inclusion i).hom.hom)⁻¹ := by
  letI := V.property.1
  letI := C.group.property.1
  let Y := V.val.X ⊗ C.group.val.X
  have hY := WordDomainGeometry.smoothConnectedGroupProduct V C.group hsV hcV C.smooth C.connected
  letI : IsIntegral Y.left := hY.2.2
  letI : ConnectedSpace Y.left := hY.2.1
  let a := fst V.val.X C.group.val.X
  let b := snd V.val.X C.group.val.X
  obtain ⟨d, hd⟩ := Unipotent.closedSeries_commutator S hS hi
    (show IsAffine Y.left from by dsimp only [Y]; rw [Over.tensorObj_left]; infer_instance)
    a (b ≫ C.inclusion.hom.hom)
  let o : 𝟙_ (SchemeOver k) ⟶ Y := lift η[V.val.X] η[C.group.val.X]
  letI := Unipotent.closedSeries_inclusion_closed S (i + 1)
  letI : Mono (S.inclusion (i + 1)).hom.hom := Over.mono_of_mono_left _
  have ho : o ≫ d = η[(S.term (i + 1)).val.X] := by
    rw [← cancel_mono (S.inclusion (i + 1)).hom.hom, Category.assoc, hd, IsMonHom.one_hom]
    simp only [commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      o, a, b, lift_fst, lift_snd, IsMonHom.one_hom]
    change (1 : 𝟙_ (SchemeOver k) ⟶ V.val.X) * 1 * 1⁻¹ * 1⁻¹ = 1
    simp
  obtain ⟨d', hd'⟩ := D.factors Y o d ho
  intro X g v
  refine ⟨lift g v ≫ d', ?_⟩
  change (lift g v ≫ d') ≫ D.inclusion.hom.hom ≫ (S.inclusion (i + 1)).hom.hom = _
  rw [Category.assoc, reassoc_of% hd', hd]
  change _ = g * (v ≫ C.inclusion.hom.hom ≫ (S.inclusion i).hom.hom) *
    g⁻¹ * (v ≫ C.inclusion.hom.hom ≫ (S.inclusion i).hom.hom)⁻¹
  simp only [commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    a, b, lift_fst, lift_snd]

end ReducedSeries

section AdditiveFactors

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.MonoidalCategory
open private groupPresentation schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private Unipotent.identityDimension Unipotent.identityDimension_lt Unipotent.IsCentralIn
  Unipotent.exists_central_additive_charZero Unipotent.exists_central_additive_charP
  Unipotent.affine_quotient_smooth_connected Unipotent.central_normal
  Unipotent.sections_eq_one_of_trivial Unipotent.trivial_inclusion_closed
  from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
variable {k : Type u} [Field k]

private lemma groupHom_identity {G H : GroupScheme k} (f : G ⟶ H) :
    f.hom.hom.left (groupIdentityPoint G) = groupIdentityPoint H :=
  congrArg (fun h : (𝟙_ (SchemeOver k)) ⟶ H.X => h.left (IsLocalRing.closedPoint k))
    (IsMonHom.one_hom f.hom.hom)

private lemma range_kernel {G H : GroupScheme k} (f : G ⟶ H)
    {N : ClosedSubgroup G} (hN : IsSchemeKernel f N) :
    Set.range N.inclusion.hom.hom.left = f.hom.hom.left ⁻¹' {groupIdentityPoint H} := by
  have hp := (Over.forget (Spec (CommRingCat.of k))).map_isPullback hN
  let e := hp.isoPullback
  have he : e.hom ≫ pullback.fst _ _ = N.inclusion.hom.hom.left := hp.isoPullback_hom_fst
  let a := pullback.fst f.hom.hom.left (groupIdentitySection H)
  rw [← he]
  change Set.range (⇑a ∘ ⇑e.hom) = _
  rw [e.hom.surjective.range_comp]
  change Set.range (pullback.fst f.hom.hom.left (groupIdentitySection H)) = _
  rw [Scheme.Pullback.range_fst]
  congr 1
  exact Set.range_eq_singleton fun x =>
    congrArg (groupIdentitySection H) (Subsingleton.elim x (IsLocalRing.closedPoint k))

open Polynomial in
private theorem ga_identity_ideal :
    (groupIdentityPoint (StandardGroups.additiveGroup k).val).asIdeal =
      Ideal.span {X} := by
  let := StandardGroups.additiveHopf k
  let A := CommHopfAlgCat.of k (Polynomial k)
  have h : groupIdentitySection (StandardGroups.additiveGroup k).val =
      (specGroupMap (hopfCounit A)).hom.hom.left := rfl
  change (groupIdentitySection (StandardGroups.additiveGroup k).val
    (IsLocalRing.closedPoint k)).asIdeal = _
  rw [h]
  change Ideal.comap (Bialgebra.counitAlgHom k (k[X])).toRingHom _ = _
  rw [show (IsLocalRing.closedPoint k).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot]
  ext f
  change (Bialgebra.counitAlgHom k (k[X]) f = 0) ↔ f ∈ Ideal.span {X}
  have hc : Bialgebra.counitAlgHom k (k[X]) = aeval (0 : k) := by
    apply algHom_ext
    rfl
  rw [hc, aeval_def, Algebra.algebraMap_self]
  change f.eval 0 = 0 ↔ _
  rw [← coeff_zero_eq_eval_zero, Ideal.mem_span_singleton, X_dvd_iff]

attribute [local instance] specializationOrder

/-- If the identity has no other generization in the additive map's kernel,
its prime ideal is minimal over the pullback of the additive coordinate. -/
private theorem identityDimension_le_one_of_isolated_kernel (Q : AffineAlgebraicGroup k)
    (f : Q.val ⟶ (StandardGroups.additiveGroup k).val)
    (h : ∀ x : Q.val.X.left, x ⤳ groupIdentityPoint Q.val →
      f.hom.hom.left x = groupIdentityPoint (StandardGroups.additiveGroup k).val →
      x = groupIdentityPoint Q.val) :
    Unipotent.identityDimension Q ≤ 1 := by
  obtain ⟨A, hA, ⟨e⟩⟩ := groupPresentation Q
  letI := hA
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  letI := StandardGroups.additiveHopf k
  let P := CommHopfAlgCat.of k (Polynomial k)
  let a : P ⟶ A :=
    ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage (e.hom ≫ f)).unop
  have ha : specGroupMap a = e.hom ≫ f := (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  let E := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e
  let x₀ := groupIdentityPoint (specGroup A)
  have hE : E.hom x₀ = groupIdentityPoint Q.val := groupHom_identity e.hom
  have map_eq (x : Spec (CommRingCat.of A)) :
      PrimeSpectrum.comap a.hom.toAlgHom.toRingHom x = f.hom.hom.left (E.hom x) :=
    congrArg (fun b : specGroup A ⟶ (StandardGroups.additiveGroup k).val => b.hom.hom.left x) ha
  have hm (x : Spec (CommRingCat.of A)) :
      a.hom Polynomial.X ∈ x.asIdeal ↔
        f.hom.hom.left (E.hom x) = groupIdentityPoint (StandardGroups.additiveGroup k).val := by
    rw [← map_eq]
    constructor
    · intro hx
      let y := PrimeSpectrum.comap a.hom.toAlgHom.toRingHom x
      have hcl := Unipotent.trivial_inclusion_closed (StandardGroups.additiveGroup k)
      have hr : Set.range (groupIdentitySection (StandardGroups.additiveGroup k).val) =
          {groupIdentityPoint (StandardGroups.additiveGroup k).val} :=
        Set.range_eq_singleton fun x =>
          congrArg (groupIdentitySection (StandardGroups.additiveGroup k).val)
            (Subsingleton.elim x (IsLocalRing.closedPoint k))
      have hclosed : IsClosed ({groupIdentityPoint (StandardGroups.additiveGroup k).val} :
          Set (PrimeSpectrum (Polynomial k))) := hr ▸ hcl.isClosedEmbedding.isClosed_range
      have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hclosed
      apply PrimeSpectrum.ext
      change y.asIdeal = _
      exact (hmax.eq_of_le y.isPrime.ne_top (by
        rw [ga_identity_ideal, Ideal.span_le]
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact hx)).symm
    · intro hx
      have hx' := congrArg PrimeSpectrum.asIdeal hx
      change Polynomial.X ∈ (PrimeSpectrum.comap a.hom.toAlgHom.toRingHom x).asIdeal
      rw [hx', ga_identity_ideal]
      exact Ideal.subset_span (Set.mem_singleton _)
  let I : Ideal A := Ideal.span {a.hom Polynomial.X}
  have hmem : x₀.asIdeal ∈ I.minimalPrimes := by
    refine ⟨⟨x₀.isPrime, Ideal.span_le.mpr (by
      simpa using (hm x₀).mpr (hE ▸ groupHom_identity f))⟩, ?_⟩
    intro J hJ hle
    let x : PrimeSpectrum A := ⟨J, hJ.1⟩
    have hs : x ⤳ x₀ := (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have hf := (hm x).mp (hJ.2 (Ideal.subset_span (Set.mem_singleton _)))
    have he := h (E.hom x) (hE ▸ hs.map E.hom.continuous) hf
    have hx : x = x₀ := E.hom.homeomorph.injective (he.trans hE.symm)
    exact (congrArg PrimeSpectrum.asIdeal hx).ge
  have hh := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I _ hmem
  rw [idealHeight_eq_coheight] at hh
  unfold Unipotent.identityDimension
  rw [← hE, coheight_eq_of_isOpenImmersion]
  exact ENat.toNat_le_of_le_natCast hh

private theorem isIso_kernel_of_trivial_target {G H : GroupScheme k} (f : G ⟶ H)
    {N : ClosedSubgroup G} (hN : IsSchemeKernel f N)
    (hH : Nonempty (H ≅ Grp.trivial (SchemeOver k))) : IsIso N.inclusion := by
  have hv : (𝟙 G.X) ≫ f.hom.hom = 1 := Unipotent.sections_eq_one_of_trivial hH _
  obtain ⟨g, hg⟩ := (schemeKernel_sections hN (𝟙 G.X)).mpr hv
  change g ≫ N.inclusion.hom.hom = 𝟙 G.X at hg
  letI := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have hi : IsIso N.inclusion.hom.hom := ⟨⟨g, (cancel_mono N.inclusion.hom.hom).mp
    (by rw [Category.assoc, hg, Category.comp_id, Category.id_comp]), hg⟩⟩
  let E : N.group ≅ G := Grp.mkIso' (asIso N.inclusion.hom.hom)
  have he : E.hom = N.inclusion := Grp.hom_ext _ _ rfl
  rw [← he]
  infer_instance

variable [PerfectField k]

private theorem exists_central_additive_of_nontrivial (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (hu : IsUnipotent G) (ht : ¬ Nonempty (G.val ≅ Grp.trivial (SchemeOver k))) :
    ∃ j : (StandardGroups.additiveGroup k).val ⟶ G.val,
      IsClosedImmersion j.hom.hom.left ∧ Unipotent.IsCentralIn j := by
  rcases CharP.exists' k with hz | ⟨p, hp, hkp⟩
  · exact Unipotent.exists_central_additive_charZero G hu ht
  · exact Unipotent.exists_central_additive_charP (p := p) G hu hs hc ht

private theorem trivial_of_identityDimension_zero (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (hu : IsUnipotent G) (hd : Unipotent.identityDimension G = 0) :
    Nonempty (G.val ≅ Grp.trivial (SchemeOver k)) := by
  classical
  by_contra h
  obtain ⟨j, hj, hn⟩ := exists_central_additive_of_nontrivial G hs hc hu h
  let N : ClosedSubgroup G.val := ⟨_, j, hj⟩
  obtain ⟨_, _, Q, q, _, _, hk, hF, _, _⟩ :=
    normalAffineQuotient G N (Unipotent.central_normal hn)
  letI := hF.2.1
  exact (Nat.not_lt_zero _ (hd ▸ Unipotent.identityDimension_lt q j hj hk))

private theorem trivial_or_additive_of_identityDimension_le_one (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (hu : IsUnipotent G) (hd : Unipotent.identityDimension G ≤ 1) :
    Nonempty (G.val ≅ Grp.trivial (SchemeOver k)) ∨
      Nonempty (G.val ≅ (StandardGroups.additiveGroup k).val) := by
  classical
  by_cases h : Nonempty (G.val ≅ Grp.trivial (SchemeOver k))
  · exact Or.inl h
  obtain ⟨j, hj, hn⟩ := exists_central_additive_of_nontrivial G hs hc hu h
  let N : ClosedSubgroup G.val := ⟨_, j, hj⟩
  obtain ⟨_, _, Q, q, _, _, hk, hF, _, _⟩ :=
    normalAffineQuotient G N (Unipotent.central_normal hn)
  letI := hF.2.1
  have hlt := Unipotent.identityDimension_lt q j hj hk
  obtain ⟨hQs, hQc⟩ := Unipotent.affine_quotient_smooth_connected q hF.2.1 hF.2.2.1 hs hc
  have hQu := Unipotent.faithfullyFlatQuotientsUnipotent G Q q hF.2.1 hF.2.2.1 hu
  have hQt := trivial_of_identityDimension_zero Q hQs hQc hQu (by omega)
  letI : IsIso j := isIso_kernel_of_trivial_target q hk hQt
  exact Or.inr ⟨(asIso j).symm⟩

private theorem reduced_step_quotient {A B V : AffineAlgebraicGroup k}
    (s : B.val ⟶ A.val) (hs : IsClosedImmersion s.hom.hom.left)
    (f : A.val ⟶ V.val) (j : V.val ⟶ (StandardGroups.additiveGroup k).val)
    (hj : IsClosedImmersion j.hom.hom.left)
    (hf : IsFppfGroupQuotient ⟨_, s, hs⟩ f)
    (C : ReducedIdentityComponent A) (D : ReducedIdentityComponent B)
    (v : D.group.val ⟶ C.group.val) (hv : v ≫ C.inclusion = D.inclusion ≫ s)
    (hvc : IsClosedImmersion v.hom.hom.left) (hvn : IsNormalSubgroup v)
    (hu : IsUnipotent C.group) :
    IsIso v ∨ ∃ (Q : AffineAlgebraicGroup k) (q : C.group.val ⟶ Q.val),
      IsFppfGroupQuotient ⟨_, v, hvc⟩ q ∧
      Nonempty ((groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k) := by
  let N : ClosedSubgroup C.group.val := ⟨_, v, hvc⟩
  obtain ⟨_, _, Q, q, _, _, hk, hF, _, he⟩ := normalAffineQuotient C.group N hvn
  have hq : IsFppfGroupQuotient N q := ⟨hk, hF.2.1, hF.2.2.1, hF.2.2.2.1, he⟩
  letI := hF.2.1
  letI := hs
  letI := hj
  let j' := C.inclusion ≫ f ≫ j
  have hkill : v.hom.hom ≫ j'.hom.hom = 1 := by
    change (v ≫ C.inclusion ≫ f ≫ j).hom.hom = 1
    rw [← Category.assoc v, hv]
    change (D.inclusion.hom.hom ≫ s.hom.hom) ≫ f.hom.hom ≫ j.hom.hom = 1
    have h : s.hom.hom ≫ f.hom.hom = 1 := by
      apply (schemeKernel_sections hf.1 _).mp
      refine ⟨𝟙 _, ?_⟩
      change 𝟙 _ ≫ s.hom.hom = s.hom.hom
      exact Category.id_comp _
    rw [Category.assoc, ← Category.assoc s.hom.hom, h, sections_one, MonObj.comp_one]
  obtain ⟨l, hl⟩ := liftGroupHomOfQuotient q hq j' hkill
  -- A generization in the quotient kernel lifts to one in the raw next term.
  -- The reduced identity component has open range there and contains the identity.
  have hdim : Unipotent.identityDimension Q ≤ 1 := by
    apply identityDimension_le_one_of_isolated_kernel Q l
    intro x hx hx₀
    have hx' : x ⤳ q.hom.hom.left (groupIdentityPoint C.group.val) :=
      (groupHom_identity q).symm ▸ hx
    obtain ⟨y, hy, hyq⟩ := (Flat.generalizingMap q.hom.hom.left) hx'
    have hyf : f.hom.hom.left (C.inclusion.hom.hom.left y) = groupIdentityPoint V.val := by
      apply j.hom.hom.left.isClosedEmbedding.injective
      rw [groupHom_identity j]
      have h := congrArg (fun a : C.group.val ⟶ (StandardGroups.additiveGroup k).val =>
        a.hom.hom.left y) hl
      exact h.symm.trans ((congrArg l.hom.hom.left hyq).trans hx₀)
    have hmem : C.inclusion.hom.hom.left y ∈ Set.range s.hom.hom.left := by
      rw [range_kernel f hf.1]
      exact hyf
    obtain ⟨z, hz⟩ := hmem
    have hze : z ⤳ groupIdentityPoint B.val := by
      apply hs.isClosedEmbedding.isInducing.specializes_iff.mp
      rw [hz, groupHom_identity s, ← groupHom_identity C.inclusion]
      exact hy.map C.inclusion.hom.hom.left.continuous
    have hzero : groupIdentityPoint B.val ∈ Set.range D.inclusion.hom.hom.left :=
      ⟨_, groupHom_identity D.inclusion⟩
    obtain ⟨w, hw⟩ := (specializes_iff_forall_open.mp hze) _ D.open_range hzero
    have hwv : v.hom.hom.left w = y := by
      letI := C.subgroup.isClosedImmersion
      apply C.inclusion.hom.hom.left.isClosedEmbedding.injective
      have h := congrArg (fun a : D.group.val ⟶ A.val => a.hom.hom.left w) hv
      exact h.trans ((congrArg s.hom.hom.left hw).trans hz)
    have hwq := congrArg (fun a : D.group.val.X ⟶ Q.val.X => a.left w) hk.w
    have hwq' : q.hom.hom.left (v.hom.hom.left w) = groupIdentityPoint Q.val :=
      hwq.trans (congrArg (groupIdentitySection Q.val) (Subsingleton.elim _ _))
    exact hyq.symm.trans (hwv ▸ hwq')
  obtain ⟨hQs, hQc⟩ := Unipotent.affine_quotient_smooth_connected q hF.2.1 hF.2.2.1 C.smooth C.connected
  have hQu := Unipotent.faithfullyFlatQuotientsUnipotent C.group Q q hF.2.1 hF.2.2.1 hu
  rcases trivial_or_additive_of_identityDimension_le_one Q hQs hQc hQu hdim with ht | ⟨⟨e⟩⟩
  · exact Or.inl (isIso_kernel_of_trivial_target q hk ht)
  · exact Or.inr ⟨Q, q, hq, ⟨(groupPointsFunctor k).mapIso e ≪≫ StandardGroups.additiveGroupPointsIso k⟩⟩

end AdditiveFactors

section QuotientActions

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.MonoidalCategory
open private tensorHom_property from LinearAlgebraicGroups.Affine.Components
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {k : Type u} [Field k]

private lemma eq_of_lifts {V Y X Z : SchemeOver k} (p : V ⟶ Y)
    [Flat p.left] [Surjective p.left] (s : X ⟶ Y) {a b : X ⟶ Z}
    (h : ∀ {W : SchemeOver k} (w : W ⟶ X) (v : W ⟶ V),
      v ≫ p = w ≫ s → w ≫ a = w ≫ b) : a = b := by
  let w := pullback.snd p s
  have hw := (Over.forget (Spec (CommRingCat.of k))).map_isPullback (IsPullback.of_hasPullback p s)
  letI : Flat w.left := MorphismProperty.of_isPullback (P := @Flat) hw (show Flat p.left from inferInstance)
  letI : Surjective w.left := MorphismProperty.of_isPullback (P := @Surjective) hw (show Surjective p.left from inferInstance)
  letI : Epi w := epiOver_of_flat_surjective w
  exact (cancel_epi w).mp (h w (pullback.fst p s) pullback.condition)

/-- Normality and centrality let conjugation descend along the product
of the quotient maps. -/
private theorem act_on_quotient {G T D Q : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} (p : G.val ⟶ T.val) (hp : IsFppfGroupQuotient U p)
    {N : ClosedSubgroup D.val} (q : D.val ⟶ Q.val) (hq : IsFppfGroupQuotient N q)
    (i : D.val ⟶ G.val) (hi : IsClosedImmersion i.hom.hom.left)
    (hni : IsNormalSubgroup i) (hnn : IsNormalSubgroup (N.inclusion ≫ i))
    (hcentral : ∀ {X : SchemeOver k} (u : X ⟶ U.group.X) (v : X ⟶ D.val.X),
      ∃ w : X ⟶ N.group.X, w ≫ (N.inclusion ≫ i).hom.hom =
        (u ≫ U.inclusion.hom.hom) * (v ≫ i.hom.hom) *
          (u ≫ U.inclusion.hom.hom)⁻¹ * (v ≫ i.hom.hom)⁻¹) :
    ∃ a : AutomorphismAction T.val Q.val,
      ∀ (R : TestAlgebra k) (g : GroupPoints G.val R) (y z : GroupPoints D.val R),
        onPoints i R z = g * onPoints i R y * g⁻¹ →
        lift (onPoints p R g) (onPoints q R y) ≫ a.action = onPoints q R z := by
  obtain ⟨c, hc⟩ := hni
  letI := hi
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  let b {X : SchemeOver k} (g : X ⟶ G.val.X) (y : X ⟶ D.val.X) := lift g y ≫ c
  have hb {X : SchemeOver k} (g : X ⟶ G.val.X) (y : X ⟶ D.val.X) :
      b g y ≫ i.hom.hom = g * (y ≫ i.hom.hom) * g⁻¹ := by
    rw [show b g y = lift g y ≫ c from rfl, Category.assoc, hc]
    simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      lift_fst, lift_snd]
  have hB₁ {X : SchemeOver k} (y : X ⟶ D.val.X) : b 1 y = y := by
    apply (cancel_mono i.hom.hom).mp
    rw [hb]; simp
  have hBm {X : SchemeOver k} (g h : X ⟶ G.val.X) (y : X ⟶ D.val.X) :
      b (g * h) y = b g (b h y) := by
    apply (cancel_mono i.hom.hom).mp
    rw [hb, hb, hb]
    group
  have hBz {X : SchemeOver k} (g : X ⟶ G.val.X) : b g 1 = 1 := by
    apply (cancel_mono i.hom.hom).mp
    rw [hb, sections_one, mul_one, mul_inv_cancel]
  have hBy {X : SchemeOver k} (g : X ⟶ G.val.X) (y z : X ⟶ D.val.X) :
      b g (y * z) = b g y * b g z := by
    apply (cancel_mono i.hom.hom).mp
    rw [hb, sections_comp i, sections_comp i, hb, hb]
    group
  have hk : N.inclusion.hom.hom ≫ q.hom.hom = 1 := by
    apply (schemeKernel_sections hq.1 _).mp
    refine ⟨𝟙 _, ?_⟩
    change 𝟙 _ ≫ N.inclusion.hom.hom = N.inclusion.hom.hom
    exact Category.id_comp _
  have hY {X : SchemeOver k} (g : X ⟶ G.val.X) {y z : X ⟶ D.val.X}
      (he : y ≫ q.hom.hom = z ≫ q.hom.hom) : b g y ≫ q.hom.hom = b g z ≫ q.hom.hom := by
    obtain ⟨w, hw⟩ := difference_in_kernel hq.1 he
    obtain ⟨v, hv⟩ := normalSubgroup_conjugate_sections hnn g w
    have hE : b g (w ≫ N.inclusion.hom.hom) = v ≫ N.inclusion.hom.hom := by
      apply (cancel_mono i.hom.hom).mp
      rw [hb, Category.assoc]
      exact hv.symm
    rw [← hw, hBy, hE, sections_comp q, Category.assoc v, hk, MonObj.comp_one, mul_one]
  have hU {X : SchemeOver k} (u : X ⟶ U.group.X) (y : X ⟶ D.val.X) :
      b (u ≫ U.inclusion.hom.hom) y ≫ q.hom.hom = y ≫ q.hom.hom := by
    obtain ⟨w, hw⟩ := hcentral u y
    have he : b (u ≫ U.inclusion.hom.hom) y = (w ≫ N.inclusion.hom.hom) * y := by
      apply (cancel_mono i.hom.hom).mp
      rw [hb, sections_comp i]
      change _ = (w ≫ (N.inclusion ≫ i).hom.hom) * (y ≫ i.hom.hom)
      rw [hw, inv_mul_cancel_right]
    rw [he, sections_comp q, Category.assoc w, hk, MonObj.comp_one, one_mul]
  have hG {X : SchemeOver k} {g h : X ⟶ G.val.X} (y : X ⟶ D.val.X)
      (he : g ≫ p.hom.hom = h ≫ p.hom.hom) :
      b g y ≫ q.hom.hom = b h y ≫ q.hom.hom := by
    obtain ⟨u, hu⟩ := difference_in_kernel hp.1 he
    rw [← hu, hBm]
    exact hY g (hU u y).symm
  let l := p.hom.hom ⊗ₘ q.hom.hom
  letI : Flat l.left := tensorHom_property _ _ @Flat hp.2.1 hq.2.1
  letI : Surjective l.left := tensorHom_property _ _ @Surjective hp.2.2.1 hq.2.2.1
  letI := G.property.1
  letI := T.property.1
  letI := D.property.1
  letI := Q.property.1
  letI : IsAffine (G.val.X ⊗ D.val.X).left := by rw [Over.tensorObj_left]; infer_instance
  letI : IsAffine (T.val.X ⊗ Q.val.X).left := by rw [Over.tensorObj_left]; infer_instance
  obtain ⟨a, ha⟩ := descendOver l (c ≫ q.hom.hom) (fun u v huv => by
    have h₁ : (u ≫ fst _ _) ≫ p.hom.hom = (v ≫ fst _ _) ≫ p.hom.hom := by
      simpa [l, Category.assoc] using congrArg (· ≫ fst T.val.X Q.val.X) huv
    have h₂ : (u ≫ snd _ _) ≫ q.hom.hom = (v ≫ snd _ _) ≫ q.hom.hom := by
      simpa [l, Category.assoc] using congrArg (· ≫ snd T.val.X Q.val.X) huv
    have htot := (hG (u ≫ snd _ _) h₁).trans (hY (v ≫ fst _ _) h₂)
    simpa [b, lift_comp_fst_snd, Category.assoc] using htot)
  have hA {X : SchemeOver k} (g : X ⟶ G.val.X) (y : X ⟶ D.val.X) :
      lift (g ≫ p.hom.hom) (y ≫ q.hom.hom) ≫ a = b g y ≫ q.hom.hom := by
    have h : lift (g ≫ p.hom.hom) (y ≫ q.hom.hom) = lift g y ≫ l := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [l]
    rw [h, Category.assoc, ha]
    exact (Category.assoc _ _ _).symm
  letI := hp.2.1
  letI := hp.2.2.1
  letI := hq.2.1
  letI := hq.2.2.1
  have act_comp {X Y : SchemeOver k} (m : X ⟶ Y) (t : Y ⟶ T.val.X) (y : Y ⟶ Q.val.X) :
      m ≫ lift t y ≫ a = lift (m ≫ t) (m ≫ y) ≫ a := comp_lift_assoc m t y a
  have hA₁ {X : SchemeOver k} (x : X ⟶ Q.val.X) :
      lift (1 : X ⟶ T.val.X) x ≫ a = x := by
    apply eq_of_lifts q.hom.hom x
    intro W w y hy
    simp only [act_comp, MonObj.comp_one, ← hy, ← sections_one p (X := W),
      hA, hB₁]
  have hAz {X : SchemeOver k} (t : X ⟶ T.val.X) :
      lift t (1 : X ⟶ Q.val.X) ≫ a = 1 := by
    apply eq_of_lifts p.hom.hom t
    intro W w g hg
    simp only [act_comp, MonObj.comp_one, ← hg, ← sections_one q (X := W),
      hA, hBz]
  have hAm {X : SchemeOver k} (t s : X ⟶ T.val.X) (x : X ⟶ Q.val.X) :
      lift (t * s) x ≫ a = lift t (lift s x ≫ a) ≫ a := by
    apply eq_of_lifts p.hom.hom t
    intro Y w g hg
    simp only [act_comp, MonObj.comp_mul, ← hg]
    apply eq_of_lifts p.hom.hom (w ≫ s)
    intro Z v h hh
    simp only [act_comp, MonObj.comp_mul, ← hh]
    apply eq_of_lifts q.hom.hom (v ≫ w ≫ x)
    intro W l' y hy
    simp only [act_comp, MonObj.comp_mul, ← hy]
    let g' := l' ≫ v ≫ g
    let h' := l' ≫ h
    have h₁ : l' ≫ v ≫ g ≫ p.hom.hom = g' ≫ p.hom.hom := by simp [g', Category.assoc]
    have h₂ : l' ≫ h ≫ p.hom.hom = h' ≫ p.hom.hom := (Category.assoc _ _ _).symm
    simp only [h₁, h₂, ← sections_comp p, hA, hBm]
  have hAy {X : SchemeOver k} (t : X ⟶ T.val.X) (x y : X ⟶ Q.val.X) :
      lift t (x * y) ≫ a = (lift t x ≫ a) * (lift t y ≫ a) := by
    apply eq_of_lifts p.hom.hom t
    intro Y w g hg
    simp only [act_comp, MonObj.comp_mul, ← hg]
    apply eq_of_lifts q.hom.hom (w ≫ x)
    intro Z v y₁ hy₁
    simp only [act_comp, MonObj.comp_mul, ← hy₁]
    apply eq_of_lifts q.hom.hom (v ≫ w ≫ y)
    intro W l' y₂ hy₂
    simp only [act_comp, MonObj.comp_mul, ← hy₂]
    let g' := l' ≫ v ≫ g
    let z := l' ≫ y₁
    have h₁ : l' ≫ v ≫ g ≫ p.hom.hom = g' ≫ p.hom.hom := by simp [g', Category.assoc]
    have h₂ : l' ≫ y₁ ≫ q.hom.hom = z ≫ q.hom.hom := (Category.assoc _ _ _).symm
    simp only [h₁, h₂, ← sections_comp q, hA, hBy]
  refine ⟨⟨a, fun _ => hA₁, fun _ => hAm, fun _ => hAz, fun _ => hAy⟩, ?_⟩
  intro R g y z hz
  have hz' : b g y = z := (cancel_mono i.hom.hom).mp ((hb g y).trans hz.symm)
  change lift (g ≫ p.hom.hom) (y ≫ q.hom.hom) ≫ a = z ≫ q.hom.hom
  rw [hA, hz']

end QuotientActions

section Characters

open _root_.LinearAlgebraicGroups.Specs
open Polynomial
open private Unipotent.scheme_hom_spec from LinearAlgebraicGroups.Unipotent.CentralSeries
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

variable {k : Type u} [Field k] {T Q : AffineAlgebraicGroup k}

private abbrev AdditivePointsIso (Q : AffineAlgebraicGroup k) :=
  (groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k

private def actionValue (a : AutomorphismAction T.val Q.val) (e : AdditivePointsIso Q)
    (R : TestAlgebra k) (t : GroupPoints T.val R) (x : R) : R :=
  Multiplicative.toAdd (show Multiplicative R from e.hom.app R
    (pointAction a R t (e.inv.app R (Multiplicative.ofAdd x))))

private lemma actionValue_natural (a : AutomorphismAction T.val Q.val) (e : AdditivePointsIso Q)
    {R S : TestAlgebra k} (b : R ⟶ S) (t : GroupPoints T.val R) (x : R) :
    b.hom (actionValue a e R t x) =
      actionValue a e S (changeTestAlgebra T.val b t) (b.hom x) := by
  unfold actionValue
  apply Multiplicative.ofAdd.injective
  change (StandardGroups.additivePoints k).map b (e.hom.app R _) = e.hom.app S _
  rw [← NatTrans.naturality_apply e.hom, pointAction_natural]
  congr 2
  exact NatTrans.naturality_apply e.inv _ _ |>.symm

private lemma actionValue_one (a : AutomorphismAction T.val Q.val) (e : AdditivePointsIso Q)
    (R : TestAlgebra k) (x : R) : actionValue a e R 1 x = x := by
  unfold actionValue
  rw [map_one]
  change Multiplicative.toAdd (show Multiplicative R from e.hom.app R
    (e.inv.app R (Multiplicative.ofAdd x))) = _
  exact congrArg Multiplicative.toAdd (ConcreteCategory.congr_hom (e.inv_hom_id_app R) _)

private lemma actionValue_zero (a : AutomorphismAction T.val Q.val) (e : AdditivePointsIso Q)
    (R : TestAlgebra k) (t : GroupPoints T.val R) : actionValue a e R t 0 = 0 := by
  change Multiplicative.toAdd (show Multiplicative R from e.hom.app R
    (pointAction a R t (e.inv.app R 1))) = 0
  rw [map_one, map_one, map_one]
  rfl

private lemma actionValue_mul (a : AutomorphismAction T.val Q.val) (e : AdditivePointsIso Q)
    (R : TestAlgebra k) (t s : GroupPoints T.val R) (x : R) :
    actionValue a e R (t * s) x = actionValue a e R t (actionValue a e R s x) := by
  unfold actionValue
  rw [map_mul]
  have h (y : GroupPoints Q.val R) : e.inv.app R (e.hom.app R y) = y :=
    ConcreteCategory.congr_hom (e.hom_inv_id_app R) y
  change (Multiplicative.toAdd (show Multiplicative R from e.hom.app R
    (pointAction a R t (pointAction a R s (e.inv.app R (Multiplicative.ofAdd x)))))) =
    Multiplicative.toAdd (show Multiplicative R from e.hom.app R
      (pointAction a R t (e.inv.app R (e.hom.app R
        (pointAction a R s (e.inv.app R (Multiplicative.ofAdd x)))))))
  rw [h]

private def actionPolynomial (a : AutomorphismAction T.val Q.val) (e : AdditivePointsIso Q)
    (R : TestAlgebra k) (t : GroupPoints T.val R) : R[X] :=
  let R' := CommAlgCat.of k R[X]
  let i : R ⟶ R' := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R R[X])
  actionValue a e R' (changeTestAlgebra T.val i t) X

private lemma actionPolynomial_evaluate (a : AutomorphismAction T.val Q.val)
    (e : AdditivePointsIso Q) {R S : TestAlgebra k} (b : R ⟶ S)
    (t : GroupPoints T.val R) (x : S) :
    (actionPolynomial a e R t).eval₂ b.hom.toRingHom x =
      actionValue a e S (changeTestAlgebra T.val b t) x := by
  let R' := CommAlgCat.of k R[X]
  let i : R ⟶ R' := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R R[X])
  let f : R' ⟶ S := CommAlgCat.ofHom (show R[X] →ₐ[k] S from
    { toRingHom := eval₂RingHom b.hom.toRingHom x
      commutes' := fun r => by
        change (C (algebraMap k R r)).eval₂ b.hom.toRingHom x = _
        rw [eval₂_C]
        exact b.hom.commutes r })
  have hcomp : i ≫ f = b := by
    ext y
    exact eval₂_C _ _
  have hmap : changeTestAlgebra T.val f (changeTestAlgebra T.val i t) =
      changeTestAlgebra T.val b t := by
    unfold changeTestAlgebra
    rw [← hcomp, Functor.map_comp]
    rfl
  have h := actionValue_natural a e f (changeTestAlgebra T.val i t) (X : R[X])
  rw [hmap, show f.hom X = x from eval₂_X _ _] at h
  exact h

/-- At the universal point of a smooth acting group the action and its
inverse are polynomial substitutions over the reduced coordinate algebra. -/
private theorem actionValue_linear (a : AutomorphismAction T.val Q.val)
    (e : AdditivePointsIso Q) (hT : Smooth T.val.X.hom) (R : TestAlgebra k)
    (t : GroupPoints T.val R) (x : R) :
    actionValue a e R t x = actionValue a e R t 1 * x := by
  letI := hT
  letI : IsReduced T.val.X.left := isReduced_of_smooth_over_field T.val.X.hom
  obtain ⟨A, ⟨d⟩⟩ := essImage_algSpec.mpr T.property.1
  let B := A.unop
  letI : IsReduced ((testSpec k).obj A).left := by
    let f := ((Over.forget (Spec (CommRingCat.of k))).mapIso d).hom
    letI : IsOpenImmersion f := inferInstance
    exact @isReduced_of_isOpenImmersion _ _ f ‹_› (isReduced_of_smooth_over_field T.val.X.hom)
  letI : _root_.IsReduced B := (affine_isReduced_iff (CommRingCat.of B)).mp
    (inferInstanceAs (IsReduced ((testSpec k).obj A).left))
  let w : GroupPoints T.val B := d.hom
  let P := actionPolynomial a e B w
  let Q' := actionPolynomial a e B w⁻¹
  let B' := CommAlgCat.of k B[X]
  let i : B ⟶ B' := CommAlgCat.ofHom (IsScalarTower.toAlgHom k B B[X])
  have hz : P.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    have h := actionPolynomial_evaluate a e (𝟙 B) w (0 : B)
    have h₀ : (𝟙 B : B ⟶ B).hom.toRingHom = RingHom.id B := rfl
    rw [h₀, actionValue_zero] at h
    exact h
  have hP : P.comp Q' = X := by
    have h₁ : P.comp Q' = actionValue a e B' (changeTestAlgebra T.val i w) Q' :=
      actionPolynomial_evaluate a e i w Q'
    rw [h₁]
    change actionValue a e B' (changeTestAlgebra T.val i w)
      (actionValue a e B' (changeTestAlgebra T.val i w⁻¹) X) = X
    rw [← actionValue_mul, ← map_mul, mul_inv_cancel, map_one, actionValue_one]
  have hlin : P = C (P.coeff 1) * X := polynomial_eq_linear_of_comp_eq_X P Q' hz hP
  let b : B ⟶ R := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (t ≫ d.inv)).unop
  have hb : changeTestAlgebra T.val b w = t := by
    change (testSpec k).map b.op ≫ d.hom = t
    have he := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage (t ≫ d.inv)
    change (testSpec k).map b.op = t ≫ d.inv at he
    rw [he, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he (z : R) : actionValue a e R t z = b.hom (P.coeff 1) * z := by
    rw [← hb, ← actionPolynomial_evaluate]
    change P.eval₂ b.hom.toRingHom z = _
    rw [hlin, eval₂_mul, eval₂_C, eval₂_X]
    simp
  rw [he x, he 1, mul_one]

private theorem action_character (a : AutomorphismAction T.val Q.val)
    (e : AdditivePointsIso Q) (hT : Smooth T.val.X.hom) :
    ∃ χ : T.val ⟶ (StandardGroups.multiplicativeGroup k).val,
      ∀ (R : TestAlgebra k) (t : GroupPoints T.val R) (x : R),
        actionValue a e R t x =
          (show Rˣ from (StandardGroups.multiplicativeGroupPointsIso k).hom.app R
            (onPoints χ R t)).val * x := by
  have hlin := actionValue_linear a e hT
  have hmul (R : TestAlgebra k) (t s : GroupPoints T.val R) :
      actionValue a e R (t * s) 1 = actionValue a e R t 1 * actionValue a e R s 1 :=
    (actionValue_mul a e R t s 1).trans (hlin R t _)
  let character (R : TestAlgebra k) (t : GroupPoints T.val R) : Rˣ :=
    ⟨actionValue a e R t 1, actionValue a e R t⁻¹ 1,
      by rw [← hmul, mul_inv_cancel, actionValue_one],
      by rw [← hmul, inv_mul_cancel, actionValue_one]⟩
  let h : (groupPointsFunctor k).obj T.val ⟶ StandardGroups.multiplicativePoints k :=
    { app R := GrpCat.ofHom
        { toFun := character R
          map_one' := by apply Units.ext; exact actionValue_one a e R 1
          map_mul' := fun t s => Units.ext (hmul R t s) }
      naturality R S b := by
        apply GrpCat.ext
        intro t
        apply Units.ext
        change actionValue a e S (changeTestAlgebra T.val b t) 1 =
          b.hom (actionValue a e R t 1)
        simpa only [map_one] using (actionValue_natural a e b t 1).symm }
  let m := StandardGroups.multiplicativeGroupPointsIso k
  let χ := (AffineAlgebraicGroup.groupHomEquiv T (StandardGroups.multiplicativeGroup k)).symm
    (h ≫ m.inv)
  refine ⟨χ, fun R t x => ?_⟩
  have hh : onPoints χ R t = m.inv.app R (h.app R t) := Unipotent.scheme_hom_spec _ _ _
  rw [hh]
  have hm := ConcreteCategory.congr_hom (m.inv_hom_id_app R) (h.app R t)
  change m.hom.app R (m.inv.app R (h.app R t)) = h.app R t at hm
  rw [hm]
  exact hlin R t x

end Characters

section AssembleSeries

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.MonoidalCategory
open private Unipotent.onPoints_comp Unipotent.closed_of_comp Unipotent.factor_through_closed
  Unipotent.kernel_points Unipotent.scheme_kernel_of_points Unipotent.onPoints_injective
    from LinearAlgebraicGroups.Unipotent.CentralSeries
open private Unipotent.groupIsoOfPoints from LinearAlgebraicGroups.Unipotent.PerfectFieldVectorGroups
open private Unipotent.closedSeries_inclusion_closed Unipotent.represented_quotient_of_kernel
  Unipotent.closedSeries_commutator from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness

variable {k : Type u} [Field k] [PerfectField k]
variable {G : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val}

private abbrev KernelGroup (U : ClosedSubgroup G.val) := closedSubgroupAlgebraicGroup U

private def CentralIn {A : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries A n) (j : A.val ⟶ U.group) : Prop :=
  ∀ i < n, ∀ (R : TestAlgebra k) (g : GroupPoints U.group R)
      (x : GroupPoints (S.term i).val R),
    ∃ y : GroupPoints (S.term (i + 1)).val R,
      onPoints (S.inclusion (i + 1) ≫ j) R y =
        g * onPoints (S.inclusion i ≫ j) R x * g⁻¹ * (onPoints (S.inclusion i ≫ j) R x)⁻¹

private def admissibleSeries {A : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries A n) (j : A.val ⟶ U.group) : Prop :=
  CentralIn S j ∧
    (∀ i ≤ n, Smooth (S.term i).val.X.hom ∧ ConnectedSpace (S.term i).val.X.left) ∧
    (∀ i ≤ n, IsNormalSubgroup ((S.inclusion i ≫ j) ≫ U.inclusion)) ∧
    ∀ i < n, ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
      IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧ Nonempty (AdditivePointsIso Q)

private def retargetSeries {A B : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries A n) (e : A.val ≅ B.val) : ClosedSeries B n :=
  { S with top := S.top.trans e }

@[simp] private theorem retargetSeries_inclusion {A B : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries A n) (e : A.val ≅ B.val) (i : ℕ) :
    (retargetSeries S e).inclusion i = S.inclusion i ≫ e.hom := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change S.step i ≫ (retargetSeries S e).inclusion i = (S.step i ≫ S.inclusion i) ≫ e.hom
    rw [ih, Category.assoc]

private theorem admissibleSeries_retarget {A B : AffineAlgebraicGroup k} {n : ℕ}
    {S : ClosedSeries A n} {i : A.val ⟶ U.group} {j : B.val ⟶ U.group} (e : A.val ≅ B.val)
    (he : e.hom ≫ j = i) (hS : admissibleSeries S i) :
    admissibleSeries (retargetSeries S e) j := by
  have h (m : ℕ) : (retargetSeries S e).inclusion m ≫ j = S.inclusion m ≫ i := by
    rw [retargetSeries_inclusion, Category.assoc, he]
  refine ⟨?_, hS.2.1, ?_, hS.2.2.2⟩
  · intro m hm R g x
    rw [h (m + 1), h m]
    exact hS.1 m hm R g x
  · intro m hm
    rw [h m]
    exact hS.2.2.1 m hm

private def prependSeries {A B : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries B n) (f : B.val ⟶ A.val) (hf : IsClosedImmersion f.hom.hom.left) :
    ClosedSeries A (n + 1) where
  term
    | 0 => A
    | i + 1 => S.term i
  top := Iso.refl A.val
  bottom := S.bottom
  step
    | 0 => S.top.hom ≫ f
    | i + 1 => S.step i
  closed i := by
    cases i with
    | zero =>
      letI := hf
      change IsClosedImmersion ((Grp.forget _ ⋙ Over.forget _).map S.top.hom ≫ f.hom.hom.left)
      infer_instance
    | succ i => exact S.closed i

@[simp] private theorem prependSeries_inclusion_succ {A B : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries B n) (f : B.val ⟶ A.val) (hf : IsClosedImmersion f.hom.hom.left) (i : ℕ) :
    (prependSeries S f hf).inclusion (i + 1) = S.inclusion i ≫ f := by
  induction i with
  | zero =>
    change (S.top.hom ≫ f) ≫ 𝟙 A.val = S.top.hom ≫ f
    exact Category.comp_id _
  | succ i ih =>
    change S.step i ≫ (prependSeries S f hf).inclusion (i + 1) =
      (S.step i ≫ S.inclusion i) ≫ f
    rw [ih, Category.assoc]

private theorem admissibleSeries_prepend {A B Q : AffineAlgebraicGroup k} {n : ℕ}
    {S : ClosedSeries B n}
    {i : A.val ⟶ U.group} {j : B.val ⟶ U.group} (f : B.val ⟶ A.val)
    (hf : IsClosedImmersion f.hom.hom.left) (hij : f ≫ i = j)
    (hS : admissibleSeries S j) (hs : Smooth A.val.X.hom)
    (hc : ConnectedSpace A.val.X.left) (hn : IsNormalSubgroup (i ≫ U.inclusion))
    (hcentral : ∀ (R : TestAlgebra k) (g : GroupPoints U.group R) (x : GroupPoints A.val R),
      ∃ y : GroupPoints B.val R,
        onPoints j R y = g * onPoints i R x * g⁻¹ * (onPoints i R x)⁻¹)
    (q : A.val ⟶ Q.val) (hq : IsFppfGroupQuotient ⟨_, f, hf⟩ q)
    (hQ : Nonempty (AdditivePointsIso Q)) :
    admissibleSeries (prependSeries S f hf) i := by
  let C := prependSeries S f hf
  have hC (m : ℕ) : C.inclusion (m + 1) ≫ i = S.inclusion m ≫ j := by
    change (prependSeries S f hf).inclusion (m + 1) ≫ i = _
    rw [prependSeries_inclusion_succ, Category.assoc, hij]
  have hC₀ : C.inclusion 0 ≫ i = i := Category.id_comp _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm R g x
    cases m with
    | zero =>
      rw [hC, hC₀]
      obtain ⟨y, hy⟩ := hcentral R g x
      refine ⟨onPoints S.top.inv R y, ?_⟩
      rw [Unipotent.onPoints_comp]
      change onPoints j R (onPoints S.top.hom R (onPoints S.top.inv R y)) = _
      have hp : onPoints S.top.hom R (onPoints S.top.inv R y) = y := by
        rw [← Unipotent.onPoints_comp S.top.inv S.top.hom, Iso.inv_hom_id]
        rfl
      rw [hp]
      exact hy
    | succ m =>
      rw [hC (m + 1), hC m]
      exact hS.1 m (by omega) R g x
  · intro m hm
    cases m with
    | zero => exact ⟨hs, hc⟩
    | succ m => exact hS.2.1 m (by omega)
  · intro m hm
    cases m with
    | zero => rwa [hC₀]
    | succ m => rw [hC m]; exact hS.2.2.1 m (by omega)
  · intro m hm
    cases m with
    | zero =>
      let N : ClosedSubgroup A.val := ⟨_, C.step 0, C.closed 0⟩
      have hk : IsSchemeKernel q N := by
        apply Unipotent.scheme_kernel_of_points q (C.step 0) (C.closed 0)
        intro R x
        constructor
        · intro hx
          obtain ⟨y, hy⟩ := (Unipotent.kernel_points q ⟨_, f, hf⟩ hq.1 R x).mp hx
          refine ⟨onPoints S.top.inv R y, ?_⟩
          change onPoints (S.top.hom ≫ f) R (onPoints S.top.inv R y) = x
          rw [← Unipotent.onPoints_comp, Iso.inv_hom_id_assoc]
          exact hy
        · rintro ⟨y, hy⟩
          apply (Unipotent.kernel_points q ⟨_, f, hf⟩ hq.1 R x).mpr
          exact ⟨onPoints S.top.hom R y, hy⟩
      exact ⟨Q, q, Unipotent.represented_quotient_of_kernel q N hk hq.2.1 hq.2.2.1 hq.2.2.2.1, hQ⟩
    | succ m => exact hS.2.2.2 m (by omega)

private theorem mono_into_trivial_isIso {A B : GroupScheme k} (f : A ⟶ B) [Mono f]
    (e : B ≅ Grp.trivial (SchemeOver k)) : IsIso f := by
  let g : B ⟶ A := e.hom ≫ default
  have hg : g ≫ f = 𝟙 B := by
    apply Grp.hom_ext
    apply (cancel_mono e.hom.hom.hom).mp
    exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  exact ⟨⟨g, (cancel_mono f).mp (by rw [Category.assoc, hg, Category.comp_id, Category.id_comp]), hg⟩⟩

set_option maxHeartbeats 1000000 in
private theorem smooth_stable_series_of_raw
    {r : ℕ} (S : ClosedSeries (KernelGroup U) r)
    (hS : S.IsCentral) (hF : S.HasAdditiveSubgroupFactors)
    (hN : ∀ i, IsNormalSubgroup (S.inclusion i ≫ U.inclusion))
    (hsG : Smooth G.val.X.hom) (hcG : ConnectedSpace G.val.X.left)
    (hsU : Smooth U.group.X.hom) (hcU : ConnectedSpace U.group.X.left)
    (hu : IsUnipotent (KernelGroup U)) :
    ∃ (n : ℕ) (C : ClosedSeries (KernelGroup U) n), admissibleSeries C (𝟙 U.group) := by
  classical
  let D (i : ℕ) := (exists_smooth_identity_component (S.term i)).some
  let inc (i : ℕ) : (D i).group.val ⟶ U.group := (D i).inclusion ≫ S.inclusion i
  have hincc (i : ℕ) : IsClosedImmersion (inc i).hom.hom.left := by
    letI := (D i).subgroup.isClosedImmersion
    letI := Unipotent.closedSeries_inclusion_closed S i
    change IsClosedImmersion ((D i).inclusion.hom.hom.left ≫ (S.inclusion i).hom.hom.left)
    infer_instance
  have hina (i : ℕ) : IsClosedImmersion (inc i ≫ U.inclusion).hom.hom.left := by
    letI := hincc i
    letI := U.isClosedImmersion
    change IsClosedImmersion ((inc i).hom.hom.left ≫ U.inclusion.hom.hom.left)
    infer_instance
  have hnormal (i : ℕ) : IsNormalSubgroup (inc i ≫ U.inclusion) := by
    letI := Unipotent.closedSeries_inclusion_closed S i
    letI := U.isClosedImmersion
    have hi : IsClosedImmersion (S.inclusion i ≫ U.inclusion).hom.hom.left := by
      change IsClosedImmersion ((S.inclusion i).hom.hom.left ≫ U.inclusion.hom.hom.left)
      infer_instance
    rw [Category.assoc]
    exact (D i).normal_chain hsG hcG _ hi (hN i)
  choose v hv using fun (i : ℕ) => (D i).factorHom (A := (D (i + 1)).group) ((D (i + 1)).inclusion ≫ S.step i)
    (D (i + 1)).smooth (D (i + 1)).connected
  have hvc (i : ℕ) : IsClosedImmersion (v i).hom.hom.left := by
    letI := (D (i + 1)).subgroup.isClosedImmersion
    letI := S.closed i
    have h : IsClosedImmersion ((D (i + 1)).inclusion ≫ S.step i).hom.hom.left := by
      change IsClosedImmersion ((D (i + 1)).inclusion.hom.hom.left ≫ (S.step i).hom.hom.left)
      infer_instance
    exact Unipotent.closed_of_comp _ _ (hv i ▸ h) (D i).subgroup.isClosedImmersion
  have hV (i : ℕ) : v i ≫ inc i = inc (i + 1) := by
    change v i ≫ (D i).inclusion ≫ S.inclusion i =
      (D (i + 1)).inclusion ≫ S.step i ≫ S.inclusion i
    rw [← Category.assoc, hv, Category.assoc]
  have hvn (i : ℕ) : IsNormalSubgroup (v i) := by
    apply normal_in_subgroup (f := inc i ≫ U.inclusion) (hina i)
    rw [← Category.assoc, hV]
    exact hnormal (i + 1)
  have hC (i : ℕ) (hi : i < r) (R : TestAlgebra k)
      (g : GroupPoints U.group R) (x : GroupPoints (D i).group.val R) :
      ∃ y : GroupPoints (D (i + 1)).group.val R,
        onPoints (inc (i + 1)) R y =
          g * onPoints (inc i) R x * g⁻¹ * (onPoints (inc i) R x)⁻¹ :=
    (D i).central_chain S hi hS hsU hcU (D (i + 1)) g x
  have hstep (i : ℕ) (hi : i < r) :
      IsIso (v i) ∨ ∃ (Q : AffineAlgebraicGroup k) (q : (D i).group.val ⟶ Q.val),
        IsFppfGroupQuotient ⟨_, v i, hvc i⟩ q ∧ Nonempty (AdditivePointsIso Q) := by
    obtain ⟨Q, A, q, j, ⟨e⟩, hj, hq⟩ := hF i hi
    let Ga := StandardGroups.additiveGroup k
    let b := Unipotent.groupIsoOfPoints A.property.1 Ga.property.1
      (e ≪≫ (StandardGroups.additiveGroupPointsIso k).symm)
    letI := hj
    have hcl : IsClosedImmersion (j ≫ b.hom).hom.hom.left := by
      change IsClosedImmersion (j.hom.hom.left ≫ (Grp.forget _ ⋙ Over.forget _).map b.hom)
      infer_instance
    have hu' : IsUnipotent (D i).group :=
      Unipotent.closedSubgroupsUnipotent (KernelGroup U) ⟨_, inc i, hincc i⟩ hu
    exact reduced_step_quotient (S.step i) (S.closed i) q (j ≫ b.hom) hcl hq
      (D i) (D (i + 1)) (v i) (hv i) (hvc i) (hvn i) hu'
  have hlast : Nonempty ((D r).group.val ≅ Grp.trivial (SchemeOver k)) := by
    letI := (D r).subgroup.isClosedImmersion
    letI : Mono (D r).inclusion.hom.hom := Over.mono_of_mono_left _
    letI : Mono (D r).inclusion := (Grp.forget _).mono_of_mono_map ‹_›
    letI := mono_into_trivial_isIso (D r).inclusion S.bottom
    exact ⟨asIso (D r).inclusion ≪≫ S.bottom⟩
  -- Build the series from its bottom, discarding each isomorphic inclusion.
  have hbuild (d i : ℕ) (hd : i + d = r) :
      ∃ (n : ℕ) (C : ClosedSeries (D i).group n), admissibleSeries C (inc i) := by
    induction d generalizing i with
    | zero =>
      have he : i = r := by omega
      subst i
      let C : ClosedSeries (D r).group 0 :=
        ⟨fun _ => (D r).group, Iso.refl _, hlast.some, fun _ => 𝟙 _,
          fun _ => inferInstanceAs (IsClosedImmersion (𝟙 (D r).group.val.X.left))⟩
      refine ⟨0, C, fun i hi => (Nat.not_lt_zero i hi).elim,
        fun _ _ => ⟨(D r).smooth, (D r).connected⟩, ?_,
        fun i hi => (Nat.not_lt_zero i hi).elim⟩
      intro i hi
      have he : i = 0 := by omega
      subst i
      change IsNormalSubgroup ((𝟙 _ ≫ inc r) ≫ U.inclusion)
      rw [Category.id_comp]
      exact hnormal r
    | succ d ih =>
      have hi : i < r := by omega
      obtain ⟨n, C, hC'⟩ := ih (i + 1) (by omega)
      rcases hstep i hi with he | ⟨Q, q, hq, hQ⟩
      · letI := he
        exact ⟨n, _, admissibleSeries_retarget (asIso (v i)) (hV i) hC'⟩
      · exact ⟨n + 1, _, admissibleSeries_prepend (v i) (hvc i) (hV i) hC'
          (D i).smooth (D i).connected (hnormal i) (hC i hi) q hq hQ⟩
  obtain ⟨n, C, hC'⟩ := hbuild r 0 (by omega)
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
  have hS₀ : Smooth (S.term 0).val.X.hom := by
    letI := hsU
    rw [← Over.w S.top.hom.hom.hom]
    change Smooth (F.map S.top.hom ≫ U.group.X.hom)
    infer_instance
  have hc₀ : ConnectedSpace (S.term 0).val.X.left :=
    (F.mapIso S.top).hom.homeomorph.connectedSpace_iff.mpr hcU
  letI : IsIso (D 0).inclusion := (D 0).isIso_inclusion hS₀ hc₀
  let e := asIso (D 0).inclusion ≪≫ S.top
  exact ⟨n, _, admissibleSeries_retarget e (Category.comp_id (inc 0)) hC'⟩

/-- A smooth connected unipotent kernel of a split torus quotient over a perfect
field has an ambient-normal smooth central series with additive character factors. -/
theorem stableSeriesForTorusExtension : StableSeriesForTorusExtension.{u} := by
  intro k _ _ G T U p hp hT hsU hcU hu
  obtain ⟨hsT, hcT⟩ := split_torus_smooth_connected T hT
  obtain ⟨hsG, hcG⟩ := extension_smooth_connected G T U p hp hsT hcT hsU hcU
  obtain ⟨r, S, hS, hF, hN⟩ := exists_normal_central_series_with_additive_subgroup_factors G T U p hp hT hu
  obtain ⟨n, C, hC, hs, hn, hf⟩ := smooth_stable_series_of_raw S hS hF hN hsG hcG hsU hcU hu
  have hn' (i : ℕ) (hi : i ≤ n) : IsNormalSubgroup (C.inclusion i ≫ U.inclusion) := by
    have h := hn i hi
    have he : C.inclusion i ≫ 𝟙 U.group = C.inclusion i := Category.comp_id _
    rw [he] at h
    exact h
  have hcent : C.IsCentral := by
    intro i hi R g x
    have he (m : ℕ) : C.inclusion m ≫ 𝟙 U.group = C.inclusion m := Category.comp_id _
    obtain ⟨y, hy⟩ := hC i hi R g x
    rw [he i, he (i + 1)] at hy
    exact ⟨y, hy⟩
  refine ⟨n, C, hcent, hs, hn', ?_⟩
  intro i hi
  obtain ⟨Q, q, hq, ⟨e⟩⟩ := hf i hi
  let j := C.inclusion i ≫ U.inclusion
  have hj : IsClosedImmersion j.hom.hom.left := by
    letI := Unipotent.closedSeries_inclusion_closed C i
    letI := U.isClosedImmersion
    change IsClosedImmersion ((C.inclusion i).hom.hom.left ≫ U.inclusion.hom.hom.left)
    infer_instance
  have hNext : IsNormalSubgroup (C.step i ≫ j) := by
    rw [← Category.assoc]
    exact hn' (i + 1) (by omega)
  have hfactor {X : SchemeOver k} (u : X ⟶ U.group.X) (v : X ⟶ (C.term i).val.X) :
      ∃ w : X ⟶ (C.term (i + 1)).val.X,
        w ≫ (C.step i ≫ j).hom.hom = (u ≫ U.inclusion.hom.hom) * (v ≫ j.hom.hom) *
          (u ≫ U.inclusion.hom.hom)⁻¹ * (v ≫ j.hom.hom)⁻¹ := by
    let D := (C.term i).val
    let V := KernelGroup U
    letI := V.property.1
    letI := (C.term i).property.1
    let a := fst V.val.X D.X
    let b := snd V.val.X D.X
    obtain ⟨w, hw⟩ := Unipotent.closedSeries_commutator C hcent hi
      (show IsAffine (V.val.X ⊗ D.X).left from by rw [Over.tensorObj_left]; infer_instance) a b
    let z := lift u v
    have he : w ≫ (C.step i ≫ j).hom.hom =
        (a ≫ U.inclusion.hom.hom) * (b ≫ j.hom.hom) *
          (a ≫ U.inclusion.hom.hom)⁻¹ * (b ≫ j.hom.hom)⁻¹ := by
      change w ≫ (C.step i).hom.hom ≫ (C.inclusion i).hom.hom ≫ U.inclusion.hom.hom = _
      rw [← Category.assoc w, ← Category.assoc (w ≫ (C.step i).hom.hom)]
      change (w ≫ (C.inclusion (i + 1)).hom.hom) ≫ U.inclusion.hom.hom = _
      rw [hw, commutatorElement_def]
      simp only [sections_comp, sections_inv, Category.assoc]
      rfl
    refine ⟨z ≫ w, ?_⟩
    rw [Category.assoc, he]
    have ha : z ≫ a = u := lift_fst _ _
    have hb : z ≫ b = v := lift_snd _ _
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ha, hb]
  obtain ⟨a, ha⟩ := act_on_quotient p hp q hq j hj (hn' i hi.le) hNext hfactor
  obtain ⟨χ, hχ⟩ := action_character a e hsT
  refine ⟨Q, q, e, StandardGroups.multiplicativeGroup k, StandardGroups.multiplicativeGroupPointsIso k,
    χ, hq, ?_⟩
  intro R g y z
  dsimp only
  intro hj'
  have h := ha R g y z hj'
  let x : R := Multiplicative.toAdd (show Multiplicative R from e.hom.app R (onPoints q R y))
  have hx : e.inv.app R (Multiplicative.ofAdd x) = onPoints q R y :=
    ConcreteCategory.congr_hom (e.hom_inv_id_app R) (onPoints q R y)
  have he := hχ R (onPoints p R g) x
  unfold actionValue at he
  rw [hx] at he
  change Multiplicative.toAdd (show Multiplicative R from e.hom.app R
    (lift (onPoints p R g) (onPoints q R y) ≫ a.action)) = _ at he
  rw [h] at he
  exact he

end AssembleSeries

section TorusActions

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.MonoidalCategory
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private Unipotent.scheme_hom_spec Unipotent.onPoints_comp Unipotent.scheme_kernel_of_points
  Unipotent.onPoints_injective
  from LinearAlgebraicGroups.Unipotent.CentralSeries
open private Triangularization.quotient_of_surjective_points
  from LinearAlgebraicGroups.Solvable.Triangularization

variable {k : Type u} [Field k]

private def semidirectProjection {G U T : GroupScheme k} {a : AutomorphismAction T U}
    (e : ∀ R : TestAlgebra k, GroupPoints G R ≃*
      GroupPoints U R ⋊[pointAction a R] GroupPoints T R)
    (he : ∀ (R S : TestAlgebra k) (b : R ⟶ S) (x : GroupPoints G R),
      (e S (changeTestAlgebra G b x)).right = changeTestAlgebra T b (e R x).right) :
    (groupPointsFunctor k).obj G ⟶ (groupPointsFunctor k).obj T where
  app R :=
    ConcreteCategory.ofHom (C := GrpCat)
      (SemidirectProduct.rightHom.comp (e R).toMonoidHom)
  naturality R S b := by
    apply GrpCat.ext
    exact he R S b

private theorem semidirect_extension (U T : AffineAlgebraicGroup k)
    (a : AutomorphismAction T.val U.val) :
    ∃ (G : AffineAlgebraicGroup k) (j : U.val ⟶ G.val) (p : G.val ⟶ T.val)
        (hj : IsClosedImmersion j.hom.hom.left),
      IsFppfGroupQuotient ⟨_, j, hj⟩ p ∧
      ∀ (R : TestAlgebra k) (t : GroupPoints T.val R),
        ∃ g : GroupPoints G.val R, ∀ x : GroupPoints U.val R,
          onPoints j R (lift t x ≫ a.action) = g * onPoints j R x * g⁻¹ := by
  obtain ⟨s, hs⟩ := semidirectProduct_representable U T a
  let V := U.val.X ⊗ T.val.X
  let G' : GroupScheme k := @Grp.mk _ _ _ V s
  letI := U.property.1
  letI := T.property.1
  letI := U.property.2.1
  letI := T.property.2.1
  have ha : IsAffine G'.X.left := by
    change IsAffine V.left
    rw [Over.tensorObj_left]
    infer_instance
  letI := ha
  have hf : LocallyOfFiniteType G'.X.hom := by
    change LocallyOfFiniteType (pullback.fst U.val.X.hom T.val.X.hom ≫ U.val.X.hom)
    infer_instance
  let G : AffineAlgebraicGroup k := ⟨G', ha, hf, inferInstance⟩
  let e (R : TestAlgebra k) :
      GroupPoints G.val R ≃* GroupPoints U.val R ⋊[pointAction a R] GroupPoints T.val R :=
    { semidirectPointsEquiv a R with
      map_mul' := fun x y => by
        have h := congrArg (fun F : NaturalGroupLaw V => (F.group R).mul x y) hs
        exact (congrArg (semidirectPointsEquiv a R) h).trans (Equiv.apply_symm_apply _ _) }
  let proj := semidirectProjection e (fun _ _ _ _ => Category.assoc _ _ _)
  let incl : (groupPointsFunctor k).obj U.val ⟶ (groupPointsFunctor k).obj G.val :=
    { app R := GrpCat.ofHom ((e R).symm.toMonoidHom.comp SemidirectProduct.inl)
      naturality R S b := by
        apply GrpCat.ext
        intro x
        change lift (changeTestAlgebra U.val b x) (1 : GroupPoints T.val S) =
          mapPoints b (lift x (1 : GroupPoints T.val R))
        change _ = (testSpec k).map b.op ≫ lift x (1 : GroupPoints T.val R)
        rw [comp_lift]
        exact (congrArg (lift (changeTestAlgebra U.val b x))
          ((changeTestAlgebra T.val b).map_one)).symm }
  let p := (AffineAlgebraicGroup.groupHomEquiv G T).symm proj
  let j := (AffineAlgebraicGroup.groupHomEquiv U G).symm incl
  have hp (R : TestAlgebra k) (x : GroupPoints G.val R) :
      onPoints p R x = (e R x).right :=
    Unipotent.scheme_hom_spec (G := G) (H := T) proj R x
  have hj (R : TestAlgebra k) (x : GroupPoints U.val R) :
      e R (onPoints j R x) = SemidirectProduct.inl x := by
    have h : onPoints j R x = (e R).symm (SemidirectProduct.inl x) :=
      Unipotent.scheme_hom_spec incl R x
    rw [h, MulEquiv.apply_symm_apply]
  have hinj : j.hom.hom ≫ fst U.val.X T.val.X = 𝟙 U.val.X := by
    apply hom_ext_of_points U.property.1
    intro R x
    have h := congrArg SemidirectProduct.left (hj R x)
    change (x ≫ j.hom.hom) ≫ fst U.val.X T.val.X = x at h
    rw [← Category.assoc, h, Category.comp_id]
  have hc : IsClosedImmersion j.hom.hom.left := by
    let π := (fst U.val.X T.val.X).left
    haveI : IsSeparated π := IsSeparated.of_isAffineHom _
    have h := congrArg (fun f : U.val.X ⟶ U.val.X => f.left) hinj
    change j.hom.hom.left ≫ π = 𝟙 _ at h
    letI : IsClosedImmersion (j.hom.hom.left ≫ π) :=
      h.symm ▸ inferInstanceAs (IsClosedImmersion (𝟙 U.val.X.left))
    exact IsClosedImmersion.of_comp j.hom.hom.left π
  let N : ClosedSubgroup G.val := ⟨_, j, hc⟩
  have hker : IsSchemeKernel p N := by
    apply Unipotent.scheme_kernel_of_points p j hc
    intro R x
    constructor
    · intro h
      refine ⟨(e R x).left, (e R).injective ?_⟩
      rw [hj]
      apply SemidirectProduct.ext
      · rfl
      · exact (h.symm.trans (hp R x))
    · rintro ⟨y, rfl⟩
      rw [hp, hj]
      rfl
  have hsurj (R : TestAlgebra k) : Function.Surjective (onPoints p R) := by
    intro t
    refine ⟨(e R).symm (SemidirectProduct.inr t), ?_⟩
    rw [hp, MulEquiv.apply_symm_apply]
    rfl
  have hproj : p.hom.hom = snd U.val.X T.val.X := by
    apply hom_ext_of_points G.property.1
    exact hp
  have hpr : IsPullback p.hom.hom.left (fst U.val.X T.val.X).left T.val.X.hom U.val.X.hom := by
    rw [hproj, Over.snd_left, Over.fst_left]
    exact (IsPullback.of_hasPullback _ _).flip
  have hpF : Flat p.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Flat) hpr.flip (inferInstance : Flat U.val.X.hom)
  have hpP : LocallyOfFinitePresentation p.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpr.flip
      (inferInstance : LocallyOfFinitePresentation U.val.X.hom)
  have hpS : Surjective p.hom.hom.left := by
    have huS : Surjective U.val.X.hom := ⟨fun y => ⟨groupIdentityPoint U.val, Subsingleton.elim _ _⟩⟩
    exact MorphismProperty.of_isPullback (P := @Surjective) hpr.flip huS
  refine ⟨G, j, p, hc, ⟨hker, hpF, hpS, hpP,
    Triangularization.quotient_of_surjective_points p N hker hsurj⟩, ?_⟩
  intro R t
  let g := (e R).symm (SemidirectProduct.inr t)
  refine ⟨g, fun x => (e R).injective ?_⟩
  rw [map_mul, map_mul, map_inv, hj, hj]
  have hg : e R g = SemidirectProduct.inr t := (e R).apply_symm_apply _
  rw [hg]
  change SemidirectProduct.inl (pointAction a R t x) = _
  simpa only [map_inv] using (SemidirectProduct.inl_aut (φ := pointAction a R) t x)

/-- A split torus action on a smooth connected unipotent group over a perfect
field preserves a smooth central series with one-dimensional additive factors. -/
theorem stableSeriesForTorusAction : StableSeriesForTorusAction.{u} := by
  intro k _ _ U T hs hc hu hT a
  obtain ⟨G, j, p, hj, hp, hconj⟩ := semidirect_extension U T a
  let K : ClosedSubgroup G.val := ⟨_, j, hj⟩
  obtain ⟨n, S, hS, hsm, hn, hq⟩ :=
    stableSeriesForTorusExtension G T K p hp hT hs hc hu
  refine ⟨n, S, ⟨hS, hsm, ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨Q, q, e, M, m, χ, hqi, hχ⟩ := hq i hi
    exact ⟨Q, q, hqi, ⟨e⟩⟩
  · intro i hi R t x
    obtain ⟨g, hg⟩ := hconj R t
    obtain ⟨z, hz⟩ := normalSubgroup_conjugate_sections (hn i hi) g x
    refine ⟨z, ?_⟩
    apply Unipotent.onPoints_injective j hj R
    rw [hg, ← Unipotent.onPoints_comp]
    exact hz

end TorusActions

end

end LinearAlgebraicGroups.EquivariantUnipotentSeries
