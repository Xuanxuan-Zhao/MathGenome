import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldVectorGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj commutatorElement

universe u

namespace LinearAlgebraicGroups.Unipotent

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme IsSchemeKernel
  IsNormalSubgroup)
open Specs.Unipotent
open Specs.SchemeDerivedGroup (LowerCentralSeries FactorsThrough commutatorMap)

noncomputable section

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k]

open private GPoints onPoints onPoints_comp onPoints_injective group_hom_ext scheme_hom_spec
  terminalIso kernel_points closed_surjective_points_iso
  factor_through_closed closed_of_comp
  difference difference_lower
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private groupIsoOfPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldVectorGroups
open private schemeKernel_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private unipotent_iff_exists_embedding
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.ExactOperations

private def IsCentralIn {G Z : GroupScheme k} (i : Z ⟶ G) : Prop :=
  ∀ (T : SchemeOver k) (x : T ⟶ G.X) (z : T ⟶ Z.X), Commute x (z ≫ i.hom.hom)

private theorem central_normal {G Z : GroupScheme k} {i : Z ⟶ G} (hi : IsCentralIn i) :
    IsNormalSubgroup i := by
  refine ⟨snd G.X Z.X, ?_⟩
  unfold Specs.subgroupConjugation
  rw [(hi _ (fst G.X Z.X) (snd G.X Z.X)).eq, mul_inv_cancel_right]

private theorem commute_of_central {G Z : GroupScheme k} {i : Z ⟶ G}
    (hc : IsClosedImmersion i.hom.hom.left) (hi : IsCentralIn i)
    (R : TestAlgebra k) (x y : GPoints Z R) : Commute x y := by
  apply onPoints_injective i hc R
  rw [map_mul, map_mul]
  exact hi _ (onPoints i R x) y

private theorem central_comp {G Z H : GroupScheme k} {i : Z ⟶ G} (hi : IsCentralIn i)
    (j : H ⟶ Z) : IsCentralIn (j ≫ i) := by
  intro T x y
  exact (Category.assoc y j.hom.hom i.hom.hom).symm ▸ hi T x (y ≫ j.hom.hom)

private theorem central_of_commutatorMap {G Z : GroupScheme k} {i : Z ⟶ G}
    (h : commutatorMap (𝟙 G) i = 1) : IsCentralIn i := by
  intro T x y
  have he := congrArg (fun f => lift x y ≫ f) h
  apply commutatorElement_eq_one_iff_commute.mp
  simpa [commutatorMap, commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv,
    MonObj.comp_one, ← Category.assoc] using he

private theorem trivial_of_iso_target {G H : GroupScheme k} (h : Nonempty (H ≅ Grp.trivial (SchemeOver k)))
    (e : G ≅ H) : Nonempty (G ≅ Grp.trivial (SchemeOver k)) :=
  h.elim fun j => ⟨e ≪≫ j⟩

private theorem sections_eq_one_of_trivial {G : GroupScheme k}
    (h : Nonempty (G ≅ Grp.trivial (SchemeOver k))) {T : SchemeOver k} (x : T ⟶ G.X) :
    x = 1 := by
  obtain ⟨e⟩ := h
  apply (cancel_mono e.hom.hom.hom).mp
  exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _

private theorem trivial_map_eq_one {G H : GroupScheme k}
    (h : Nonempty (G ≅ Grp.trivial (SchemeOver k))) (f : G ⟶ H)
    {T : SchemeOver k} (x : T ⟶ G.X) : x ≫ f.hom.hom = 1 := by
  have ho := (IsMonHom.monoidHom f.hom.hom T).map_one
  rw [sections_eq_one_of_trivial h x]
  exact ho

private theorem closedSeries_inclusion_closed {G : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries G n) (i : ℕ) : IsClosedImmersion (S.inclusion i).hom.hom.left := by
  induction i with
  | zero =>
    change IsClosedImmersion ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map S.top.hom)
    infer_instance
  | succ i hi =>
    change IsClosedImmersion ((S.step i).hom.hom.left ≫ (S.inclusion i).hom.hom.left)
    let := S.closed i
    infer_instance

private theorem sections_factor_of_affine {G : GroupScheme k} (N : ClosedSubgroup G)
    {T : SchemeOver k} (hT : IsAffine T.left) (f : T ⟶ G.X)
    (hf : ∀ (R : TestAlgebra k) (x : Points T R),
      ∃ y : Points N.group.X R, y ≫ N.inclusion.hom.hom = x ≫ f) :
    FactorsThrough N f := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hT
  obtain ⟨y, hy⟩ := hf A.unop e.hom
  refine ⟨e.inv ≫ y, ?_⟩
  change (e.inv ≫ y) ≫ N.inclusion.hom.hom = f
  simp [Category.assoc, hy]

private theorem closedSeries_commutator {G : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries G n) (hS : S.IsCentral) {i : ℕ} (hi : i < n)
    {T : SchemeOver k} (hT : IsAffine T.left) (x : T ⟶ G.val.X) (y : T ⟶ (S.term i).val.X) :
    ∃ z : T ⟶ (S.term (i + 1)).val.X,
      z ≫ (S.inclusion (i + 1)).hom.hom = ⁅x, (y ≫ (S.inclusion i).hom.hom : T ⟶ G.val.X)⁆ := by
  let N : ClosedSubgroup G.val := ⟨_, S.inclusion (i + 1), closedSeries_inclusion_closed S _⟩
  apply sections_factor_of_affine N hT
  intro R w
  obtain ⟨z, hz⟩ := hS i hi R (w ≫ x) (w ≫ y)
  refine ⟨z, ?_⟩
  change z ≫ (S.inclusion (i + 1)).hom.hom =
    (w ≫ x) * ((w ≫ y) ≫ (S.inclusion i).hom.hom) * (w ≫ x)⁻¹ *
      (((w ≫ y) ≫ (S.inclusion i).hom.hom)⁻¹) at hz
  simpa only [commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] using hz

private theorem closedSeries_normal {G : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries G n) (hS : S.IsCentral) {i : ℕ} (hi : i < n) :
    IsNormalSubgroup (S.inclusion i) := by
  have := G.property.1
  have := (S.term i).property.1
  let x := fst G.val.X (S.term i).val.X
  let y := snd G.val.X (S.term i).val.X
  obtain ⟨z, hz⟩ := closedSeries_commutator S hS hi
    (show IsAffine (G.val.X ⊗ (S.term i).val.X).left from by rw [Over.tensorObj_left]; infer_instance) x y
  refine ⟨(z ≫ (S.step i).hom.hom) * y, ?_⟩
  have he : (S.inclusion (i + 1)).hom.hom =
      (S.step i).hom.hom ≫ (S.inclusion i).hom.hom := rfl
  rw [he, ← Category.assoc] at hz
  change _ = x * (y ≫ (S.inclusion i).hom.hom) * x⁻¹
  have hh := (IsMonHom.monoidHom (S.inclusion i).hom.hom _).map_mul
    (z ≫ (S.step i).hom.hom) y
  calc
    _ = ((z ≫ (S.step i).hom.hom) ≫ (S.inclusion i).hom.hom) *
          (y ≫ (S.inclusion i).hom.hom) := hh
    _ = _ := by rw [hz, commutatorElement_def, inv_mul_cancel_right]

/-- Compare the lower central series with any central series on the universal
commutator. Each term lies in the corresponding term of the given series. -/
private theorem lowerCentral_factors_closedSeries {G : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries G n) (hS : S.IsCentral) (i : ℕ) (hi : i ≤ n)
    {D : ClosedSubgroup G.val} (hD : LowerCentralSeries G.val i D) :
    ∃ a : D.group ⟶ (S.term i).val, a ≫ S.inclusion i = D.inclusion := by
  induction hD with
  | zero D _ =>
    exact ⟨D.inclusion ≫ S.top.inv, by simp [ClosedSeries.inclusion]⟩
  | @succ i H hH D hD ih =>
    let N : ClosedSubgroup G.val :=
      ⟨(S.term (i + 1)).val, S.inclusion (i + 1), closedSeries_inclusion_closed S (i + 1)⟩
    obtain ⟨a, ha⟩ := ih (by omega)
    have hnormal : IsNormalSubgroup N.inclusion := by
      by_cases hn : i + 1 < n
      · exact closedSeries_normal S hS hn
      · have hb : i + 1 = n := by omega
        exact central_normal (fun T x y => by
          have ht : Nonempty ((S.term (i + 1)).val ≅ Grp.trivial (SchemeOver k)) := by
            rw [hb]
            exact ⟨S.bottom⟩
          rw [trivial_map_eq_one (show Nonempty (N.group ≅ _) from ht) N.inclusion y]
          exact Commute.one_right x)
    have hfactor : FactorsThrough N (commutatorMap (𝟙 G.val) H.inclusion) := by
      have := G.property.1
      have : IsAffine H.group.X.left := (closedSubgroupAlgebraicGroup (G := G) H).property.1
      let x := fst G.val.X H.group.X
      let y := snd G.val.X H.group.X
      obtain ⟨z, hz⟩ := closedSeries_commutator S hS (show i < n by omega)
        (show IsAffine (G.val.X ⊗ H.group.X).left from by rw [Over.tensorObj_left]; infer_instance) x (y ≫ a.hom.hom)
      have ha' : a.hom.hom ≫ (S.inclusion i).hom.hom = H.inclusion.hom.hom :=
        congrArg (fun f => f.hom.hom) ha
      rw [Category.assoc, ha'] at hz
      refine ⟨z, ?_⟩
      change z ≫ (S.inclusion (i + 1)).hom.hom = _
      simpa [commutatorMap, commutatorElement_def, x, y] using hz
    exact hD.2.2 N hnormal hfactor

private theorem exists_central_lowerCentral [PerfectField k] (G : AffineAlgebraicGroup k)
    (hG : IsUnipotent G) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (htr : ¬ Nonempty (G.val ≅ Grp.trivial (SchemeOver k))) :
    ∃ D : ClosedSubgroup G.val, IsCentralIn D.inclusion ∧
      Smooth D.group.X.hom ∧ ConnectedSpace D.group.X.left ∧
      ¬ Nonempty (D.group ≅ Grp.trivial (SchemeOver k)) := by
  classical
  obtain ⟨n, S, hS, _⟩ := unipotentCentralSeries G hG
  obtain ⟨N, hN⟩ := SchemeDerivedGroup.lowerCentralSeriesExists G n
  obtain ⟨a, ha⟩ := lowerCentral_factors_closedSeries S hS n le_rfl hN
  have hT : ∃ m, ∃ D : ClosedSubgroup G.val, LowerCentralSeries G.val m D ∧
      Nonempty (D.group ≅ Grp.trivial (SchemeOver k)) := by
    refine ⟨n, N, hN, ⟨terminalIso (closedSubgroupAlgebraicGroup N) ?_⟩⟩
    intro R
    change ∀ x : GPoints N.group R, x = 1
    intro x
    apply onPoints_injective N.inclusion N.isClosedImmersion R
    have hx : onPoints N.inclusion R x = 1 := by
      rw [← ha, onPoints_comp]
      exact trivial_map_eq_one ⟨S.bottom⟩ (S.inclusion n) _
    exact hx.trans (onPoints N.inclusion R).map_one.symm
  obtain ⟨D, hD, hdtr⟩ := Nat.find_spec hT
  generalize hm : Nat.find hT = m at hD
  cases hD with
  | zero D hi => exact (htr (trivial_of_iso_target hdtr (asIso D.inclusion).symm)).elim
  | @succ j Z hZ D hComm =>
    have hnz : ¬ Nonempty (Z.group ≅ Grp.trivial (SchemeOver k)) := by
      intro h
      have hj : Nat.find hT ≤ j := Nat.find_min' hT ⟨Z, hZ, h⟩
      omega
    obtain ⟨f, hf⟩ := hComm.2.1
    have he : commutatorMap (𝟙 G.val) Z.inclusion = 1 :=
      hf.symm.trans (trivial_map_eq_one hdtr D.inclusion f)
    obtain ⟨hzs, hzc⟩ := SchemeDerivedGroup.lowerCentralSeriesSmoothConnected G j Z hZ hs hc
    exact ⟨Z, central_of_commutatorMap he, hzs, hzc, hnz⟩

private theorem affine_quotient_smooth_connected [PerfectField k] {G Q : AffineAlgebraicGroup k}
    (f : G.val ⟶ Q.val) (hf : Flat f.hom.hom.left) (hfs : Surjective f.hom.hom.left)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    Smooth Q.val.X.hom ∧ ConnectedSpace Q.val.X.left := by
  let := G.property.1
  let := Q.property.1
  let := Q.property.2.1
  let : Smooth G.val.X.hom := hs
  let : GeometricallyReduced G.val.X.hom := ((affineGroupSmoothnessCriteria k G).1.mp hs)
  let : IsReduced G.val.X.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.val.X.hom
  let : ConnectedSpace G.val.X.left := hc
  have hff := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f.hom.hom.left).mp ⟨hf, hfs⟩
  let : IsReduced Γ(Q.val.X.left, ⊤) :=
    isReduced_of_injective _ hff.injective
  have hred : IsReduced Q.val.X.left := isReduced_of_isAffine_isReduced _
  exact ⟨smoothOfReducedOverPerfectField k Q.val hred,
    (surjective_iff _ |>.mp hfs).connectedSpace f.hom.hom.left.continuous⟩

private theorem specGroupMap_on_convolution {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    (R : TestAlgebra k) (b : WithConv (B →ₐ[k] R)) :
    onPoints (specGroupMap a) R ((hopfSpecPointIso B).hom.app R b) =
      (hopfSpecPointIso A).hom.app R (toConv (b.ofConv.comp a.hom.toAlgHom)) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom a.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom b.ofConv.toRingHom)).symm

/-- A nonzero polynomial over a field of characteristic zero cannot vanish on
all the natural multiples of a nonzero element. -/
private theorem eq_zero_of_eval_natMultiples {K : Type u} [Field K] [CharZero K]
    {f : Polynomial K} (hf : f ≠ 0) (x : K)
    (h : ∀ n : ℕ, f.eval (n • x) = 0) : x = 0 := by
  by_contra hx
  apply (Set.infinite_range_of_injective (f := fun n : ℕ => n • x) ?_).not_finite
    ((Polynomial.finite_setOfPred_isRoot hf).subset (Set.range_subset_iff.mpr h))
  intro m n he
  simp only [nsmul_eq_mul] at he
  exact Nat.cast_injective (mul_right_cancel₀ hx he)

open private StandardGroups.spectrumPointsIso StandardGroups.Representation.convolutionIso
  StandardGroups.additiveRepresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

private theorem additive_iso_eval (R : TestAlgebra k) (b : Polynomial k →ₐ[k] R) :
    letI := StandardGroups.additiveHopf k
    let A := CommHopfAlgCat.of k (Polynomial k)
    (StandardGroups.additiveGroupPointsIso k).hom.app R ((hopfSpecPointIso A).hom.app R
      (toConv b)) = Multiplicative.ofAdd (b Polynomial.X) := by
  intro A
  let e := hopfSpecPointIso A
  have he := ConcreteCategory.congr_hom (e.hom_inv_id_app R) (toConv b)
  change e.inv.app R (e.hom.app R (toConv b)) = toConv b at he
  change ((StandardGroups.Representation.convolutionIso (StandardGroups.additiveRepresentation k)).hom.app R)
    (e.inv.app R (e.hom.app R (toConv b))) = _
  rw [he]
  rfl

private theorem additive_hopf_map_X_zero [CharZero k] {B : HopfAlgebraCategory k}
    [IsReduced B]
    (a : (letI := StandardGroups.additiveHopf k; CommHopfAlgCat.of k (Polynomial k)) ⟶ B) {f : Polynomial k} (hf : f ≠ 0)
    (hfa : a.hom f = 0) :
    a.hom Polynomial.X = 0 := by
  let := StandardGroups.additiveHopf k
  let e := hopfSpecPointIso (k := k)
  let A := CommHopfAlgCat.of k (Polynomial k)
  let c := StandardGroups.additiveGroupPointsIso k
  have heval (R : TestAlgebra k) (x : GPoints (specGroup B) R) :
      let fR : Polynomial R := f.map (algebraMap k R)
      fR.eval (@Multiplicative.toAdd R (c.hom.app R (onPoints (specGroupMap a) R x))) = 0 := by
    dsimp only
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((e B).hom.app R)).2 x
    rw [specGroupMap_on_convolution, additive_iso_eval]
    change (Polynomial.map (algebraMap k R) f).eval (b.ofConv (a.hom Polynomial.X)) = 0
    rw [Polynomial.eval_map]
    have hab : Polynomial.aeval (b.ofConv (a.hom Polynomial.X)) = b.ofConv.comp a.hom.toAlgHom :=
      Polynomial.algHom_ext (by simp)
    rw [← Polynomial.aeval_def, hab]
    exact (congrArg b.ofConv hfa).trans (map_zero _)
  have hnil : a.hom Polynomial.X ∈ nilradical B := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    let : P.IsPrime := hP
    let K := FractionRing (B ⧸ P)
    let b : B →ₐ[k] K := (IsScalarTower.toAlgHom k (B ⧸ P) K).comp (Ideal.Quotient.mkₐ k P)
    let R := CommAlgCat.of k K
    have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    let x := (e B).hom.app R (toConv b)
    let φ : GPoints (specGroup B) R →* Multiplicative K :=
      (c.hom.app R).hom.comp (onPoints (specGroupMap a) R)
    have hx : (φ x).toAdd = b (a.hom Polynomial.X) := by
      change (c.hom.app R (onPoints (specGroupMap a) R x)).toAdd = _
      rw [specGroupMap_on_convolution a R (toConv b), additive_iso_eval]
      rfl
    have hfK : Polynomial.map (algebraMap k K) f ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap k K).injective).mpr hf
    have hz : (φ x).toAdd = 0 := eq_zero_of_eval_natMultiples hfK _ (fun n => by
      have hn := heval R (x ^ n)
      change (Polynomial.map (algebraMap k K) f).eval ((φ (x ^ n)).toAdd) = 0 at hn
      rw [map_pow] at hn
      exact hn)
    rw [hx] at hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (IsFractionRing.injective (B ⧸ P) K) (hz.trans (map_zero _).symm)
  simpa [nilradical, Ideal.radical_bot_of_isReduced] using hnil

theorem additiveSubgroupCharZero : AdditiveSubgroupCharZero.{u} := by
  intro k _ _ H A f ⟨e⟩ hf
  let L := StandardGroups.additiveGroup k
  let j := groupIsoOfPoints A.property.1 L.property.1
    (e ≪≫ (StandardGroups.additiveGroupPointsIso k).symm)
  let := StandardGroups.additiveHopf k
  let C := CommHopfAlgCat.of k (Polynomial k)
  have hf' : IsClosedImmersion (f ≫ j.hom).hom.hom.left := by
    have hj : IsIso j.hom.hom.hom.left := by
      change IsIso ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map j.hom)
      infer_instance
    change IsClosedImmersion (f.hom.hom.left ≫ j.hom.hom.hom.left)
    let : IsClosedImmersion f.hom.hom.left := hf
    exact IsClosedImmersion.comp _ _
  obtain ⟨I, ⟨hI, eH, he⟩, _⟩ := (closedSubgroupClassification k C H.val (f ≫ j.hom)).mp hf'
  let := hI
  let B := hopfQuotient C I
  let a := hopfQuotientMap C I
  by_cases hinj : Function.Injective a.hom
  · right
    have ha : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr
      ⟨hinj, Ideal.Quotient.mk_surjective⟩
    have hi : IsIso (specGroupMap a) := (hopfSpec (CommRingCat.of k)).map_isIso a.op
    have : IsIso (eH.hom ≫ specGroupMap a ≫ j.inv) := inferInstance
    rw [← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id] at this
    exact this
  · left
    have hzero : ∃ z : Polynomial k, z ≠ 0 ∧ a.hom z = 0 := by
      by_contra hh
      apply hinj
      intro x y hxy
      have hxy' : a.hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      exact sub_eq_zero.mp (not_not.mp (fun hne => hh ⟨x-y, hne, hxy'⟩))
    obtain ⟨z, hz, hza⟩ := hzero
    have : Algebra.FiniteType k B := Algebra.FiniteType.of_surjective a.hom.toAlgHom
      Ideal.Quotient.mk_surjective
    let P := Specs.StandardGroups.spectrum k B
    have hs : Smooth P.val.X.hom := characteristicZeroSmoothness k P
    let : Smooth P.val.X.hom := hs
    let : GeometricallyReduced P.val.X.hom := (affineGroupSmoothnessCriteria k P).1.mp hs
    have hr : IsReduced P.val.X.left :=
      GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian P.val.X.hom
    have : IsReduced B := (affine_isReduced_iff (CommRingCat.of B)).mp hr
    have hx := additive_hopf_map_X_zero a hz hza
    have hall (R : TestAlgebra k) : ∀ x : GPoints P.val R, x = 1 := by
      change ∀ x : GPoints (specGroup B) R, x = 1
      intro x
      have hc := (hopfMapClosedImmersion k a).mpr Ideal.Quotient.mk_surjective
      apply onPoints_injective (specGroupMap a) hc R
      refine Eq.trans ?_ (onPoints (specGroupMap a) R).map_one.symm
      obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((hopfSpecPointIso B).hom.app R)).2 x
      let c := StandardGroups.additiveGroupPointsIso k
      apply (ConcreteCategory.bijective_of_isIso (c.hom.app R)).1
      rw [specGroupMap_on_convolution, additive_iso_eval]
      have h := (c.hom.app R).hom.map_one
      change c.hom.app R 1 = Multiplicative.ofAdd (0 : R) at h
      change Multiplicative.ofAdd (b.ofConv (a.hom Polynomial.X)) = _
      rw [hx, map_zero]
      exact h.symm
    exact trivial_of_iso_target ⟨terminalIso P hall⟩ eH

private theorem closed_commutator_term_central {G : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries G n) (hS : S.IsCentral) {i : ℕ} (hi : i < n)
    (ht : Nonempty ((S.term (i + 1)).val ≅ Grp.trivial (SchemeOver k))) :
    IsCentralIn (S.inclusion i) := by
  apply central_of_commutatorMap
  let x := fst G.val.X (S.term i).val.X
  let y := snd G.val.X (S.term i).val.X
  have := G.property.1
  have := (S.term i).property.1
  obtain ⟨z, hz⟩ := closedSeries_commutator S hS hi
    (show IsAffine (G.val.X ⊗ (S.term i).val.X).left from by rw [Over.tensorObj_left]; infer_instance) x y
  rw [trivial_map_eq_one ht (S.inclusion (i + 1)) z] at hz
  simpa [commutatorMap, commutatorElement_def, x, y] using hz.symm

private theorem isIso_of_trivial_kernel {G Q : AffineAlgebraicGroup k} (q : G.val ⟶ Q.val)
    (N : ClosedSubgroup G.val) (hN : IsFppfGroupQuotient N q)
    (ht : Nonempty (N.group ≅ Grp.trivial (SchemeOver k))) : IsIso q := by
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
  let : Mono q.hom.hom := ⟨fun {T} x y he => by
    let φ : (T ⟶ G.val.X) →* (T ⟶ Q.val.X) := ((yonedaGrp.map q).app (op T)).hom
    have hxy : φ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr he
    obtain ⟨z, hz⟩ := (schemeKernel_sections hN.1 (x * y⁻¹)).mpr hxy
    exact mul_inv_eq_one.mp (hz.symm.trans (trivial_map_eq_one ht N.inclusion z))⟩
  let := hN.2.1
  let := hN.2.2.1
  let := G.property.1
  let := Q.property.1
  have hh : IsIso (F.map q) := Flat.isIso_of_surjective_of_mono q.hom.hom.left
  let : IsIso ((Over.forget (Spec (CommRingCat.of k))).map q.hom.hom) := hh
  have : IsIso q.hom.hom := isIso_of_reflects_iso q.hom.hom (Over.forget (Spec (CommRingCat.of k)))
  let e : G.val ≅ Q.val := Grp.mkIso' (asIso q.hom.hom)
  have he : e.hom = q := by apply Grp.hom_ext; rfl
  rw [← he]
  infer_instance

private theorem exists_central_additive_charZero [CharZero k] (G : AffineAlgebraicGroup k)
    (hG : IsUnipotent G) (htr : ¬ Nonempty (G.val ≅ Grp.trivial (SchemeOver k))) :
    ∃ i : (StandardGroups.additiveGroup k).val ⟶ G.val,
      IsClosedImmersion i.hom.hom.left ∧ IsCentralIn i := by
  classical
  obtain ⟨n, S, hS, hF⟩ := unipotentCentralSeries G hG
  have he : ∃ i, Nonempty ((S.term i).val ≅ Grp.trivial (SchemeOver k)) := ⟨n, ⟨S.bottom⟩⟩
  have hb := Nat.find_spec he
  cases hm : Nat.find he with
  | zero =>
    exact (htr (trivial_of_iso_target (hm ▸ hb) S.top.symm)).elim
  | succ i =>
    have hnext : Nonempty ((S.term (i + 1)).val ≅ Grp.trivial (SchemeOver k)) := hm ▸ hb
    have hi : i < n := by
      have h := Nat.find_min' he (m := n) ⟨S.bottom⟩
      omega
    have hit : ¬ Nonempty ((S.term i).val ≅ Grp.trivial (SchemeOver k)) := by
      intro h
      have h' := Nat.find_min' he (m := i) h
      omega
    obtain ⟨Q, A, q, j, hjA, hj, hq⟩ := hF i hi
    let := isIso_of_trivial_kernel q ⟨_, S.step i, S.closed i⟩ hq hnext
    have hji : IsIso j := (additiveSubgroupCharZero Q A j hjA hj).resolve_left
      (fun ht => hit (trivial_of_iso_target ht (asIso q)))
    let L := StandardGroups.additiveGroup k
    let e := groupIsoOfPoints L.property.1 A.property.1
      (StandardGroups.additiveGroupPointsIso k ≪≫ hjA.some.symm)
    let a := e.hom ≫ inv j ≫ inv q
    refine ⟨a ≫ S.inclusion i, ?_, central_comp (closed_commutator_term_central S hS hi hnext) a⟩
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
    let : IsIso (F.map a) := F.map_isIso a
    let := closedSeries_inclusion_closed S i
    change IsClosedImmersion (F.map a ≫ (S.inclusion i).hom.hom.left)
    let : IsClosedImmersion (S.inclusion i).hom.hom.left := closedSeries_inclusion_closed S i
    exact @IsClosedImmersion.comp _ _ _ (F.map a) (S.inclusion i).hom.hom.left
      (inferInstanceAs (IsClosedImmersion (F.map a))) (closedSeries_inclusion_closed S i)

private theorem difference_pow_entry {n : ℕ} {R : Type u} [CommRing R]
    (x : UnitriangularMatrix n R) (m : ℕ) {i j : Index.{u} n}
    (h : j.down.val < i.down.val + m) :
    (difference x ^ m) i j = 0 := by
  induction m generalizing i j with
  | zero =>
    rw [pow_zero]
    apply Matrix.one_apply_ne
    intro he
    subst j
    omega
  | succ m ih =>
    rw [pow_succ]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : j ≤ l
    · rw [difference_lower x hl, mul_zero]
    · have hl' : l.down.val < j.down.val := lt_of_not_ge hl
      rw [ih (show l.down.val < i.down.val + m by omega), zero_mul]

private theorem unitriangular_pow_char {p : ℕ} [Fact p.Prime] [CharP k p] {n : ℕ}
    (m : ℕ) (hm : n ≤ p ^ m) (R : TestAlgebra k) (x : UnitriangularMatrix n R) :
    x ^ (p ^ m) = 1 := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    apply Subtype.ext
    apply Units.ext
    exact Subsingleton.elim _ _
  | inr h =>
    let := h
    by_cases hn : Nonempty (Index.{u} n)
    · let := hn
      have : CharP R p := charP_of_injective_algebraMap' k p
      have hzero : difference x ^ (p ^ m) = 0 := by
        ext i j
        have hj : j.down.val < n := j.down.isLt
        exact difference_pow_entry x _ (by omega)
      apply Subtype.ext
      apply Units.ext
      change x.val.val ^ (p ^ m) = 1
      let D := difference x
      have h := add_pow_char_pow_of_commute p m (Commute.one_left D)
      have hD : 1 + D = x.val.val := by simp [D, difference]
      rw [← hD, h, one_pow, hzero, add_zero]
    · apply Subtype.ext
      apply Units.ext
      ext i j
      exact (hn ⟨i⟩).elim

private theorem unipotent_power_bound {p : ℕ} [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k) (hG : IsUnipotent G) :
    ∃ m : ℕ, ∀ (R : TestAlgebra k) (x : GPoints G.val R), x ^ (p ^ m) = 1 := by
  obtain ⟨n, A, ⟨e⟩, j, hj⟩ := (unipotent_iff_exists_embedding G).mp hG
  have hₚ : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt n hₚ
  refine ⟨m, fun R x => onPoints_injective j hj R ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1
  rw [map_pow, map_one, map_pow, map_one]
  exact unitriangular_pow_char m hm.le R _

private def powerHom (G : AffineAlgebraicGroup k)
    (hc : ∀ (R : TestAlgebra k) (x y : GPoints G.val R), Commute x y) (m : ℕ) :
    G.val ⟶ G.val :=
  (AffineAlgebraicGroup.groupHomEquiv G G).symm
    { app R := GrpCat.ofHom
        { toFun x := x ^ m
          map_one' := one_pow _
          map_mul' x y := (hc R x y).mul_pow _ }
      naturality R T a := by
        apply GrpCat.ext
        intro x
        change _ = (((groupPointsFunctor k).obj G.val).map a).hom (x ^ m)
        exact (map_pow (((groupPointsFunctor k).obj G.val).map a).hom _ _).symm }

private theorem powerHom_points {G : AffineAlgebraicGroup k}
    (hc : ∀ (R : TestAlgebra k) (x y : GPoints G.val R), Commute x y)
    (m : ℕ) (R : TestAlgebra k) (x : GPoints G.val R) :
    onPoints (powerHom G hc m) R x = x ^ m :=
  scheme_hom_spec _ R x

private theorem eq_of_flat_surjective_comp {G Q H : GroupScheme k}
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    {f g : Q ⟶ H} (h : q ≫ f = q ≫ g) : f = g := by
  let : Epi q.hom.hom.left := Flat.epi_of_flat_of_surjective _
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_epi q.hom.hom.left).mp (congrArg (fun a => a.hom.hom.left) h)

private theorem last_power_image [PerfectField k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k) (hG : IsUnipotent G) (D : ClosedSubgroup G.val)
    (hD : IsCentralIn D.inclusion) (hs : Smooth D.group.X.hom) (hc : ConnectedSpace D.group.X.left)
    (htr : ¬ Nonempty (D.group ≅ Grp.trivial (SchemeOver k))) :
    ∃ H : ClosedSubgroup G.val, IsCentralIn H.inclusion ∧ Smooth H.group.X.hom ∧
      ConnectedSpace H.group.X.left ∧
      ¬ Nonempty (H.group ≅ Grp.trivial (SchemeOver k)) ∧
      ∀ (R : TestAlgebra k) (x : GPoints H.group R), x ^ p = 1 := by
  classical
  let Z := closedSubgroupAlgebraicGroup D
  have hz := closedSubgroupsUnipotent G D hG
  have hcomm := commute_of_central D.isClosedImmersion hD
  obtain ⟨m, hm⟩ := unipotent_power_bound (p := p) Z hz
  have hex : ∃ n, ∀ (R : TestAlgebra k) (x : GPoints D.group R), x ^ (p ^ n) = 1 := ⟨m, hm⟩
  let a := Nat.find hex
  have ha := Nat.find_spec hex
  have h0 : a ≠ 0 := by
    intro he
    apply htr
    refine ⟨terminalIso Z fun R => ?_⟩
    change ∀ x : GPoints D.group R, x = 1
    intro x
    simpa [a, he] using ha R x
  let t := a - 1
  have hat : t + 1 = a := by omega
  let f := powerHom Z hcomm (p ^ t)
  obtain ⟨I, q, j, hfac, _⟩ := schemeImageFactorization Z Z f
  obtain ⟨he, hf, hsurj, _, _, hj⟩ := hfac
  let N : ClosedSubgroup G.val := ⟨I.val, j ≫ D.inclusion, by
    change IsClosedImmersion (j.hom.hom.left ≫ D.inclusion.hom.hom.left)
    let : IsClosedImmersion j.hom.hom.left := hj
    let : IsClosedImmersion D.inclusion.hom.hom.left := D.isClosedImmersion
    exact @IsClosedImmersion.comp _ _ _ j.hom.hom.left D.inclusion.hom.hom.left hj D.isClosedImmersion⟩
  obtain ⟨hIs, hIc⟩ := affine_quotient_smooth_connected q hf hsurj hs hc
  have hcen : IsCentralIn N.inclusion := central_comp hD j
  have hnt : ¬ Nonempty (I.val ≅ Grp.trivial (SchemeOver k)) := by
    intro h
    have ht : a ≤ t := Nat.find_min' hex (show ∀ R x, x ^ (p ^ t) = 1 from fun R x => by
      change (x : GPoints Z.val R) ^ (p ^ t) = 1
      have hx := powerHom_points (G := Z) hcomm (p ^ t) R x
      rw [← show q ≫ j = powerHom Z hcomm (p ^ t) from he, onPoints_comp] at hx
      exact hx.symm.trans (trivial_map_eq_one h j _))
    omega
  refine ⟨N, hcen, hIs, hIc, hnt, ?_⟩
  let pow := powerHom I (commute_of_central N.isClosedImmersion hcen) p
  let one : I.val ⟶ I.val := (default : I.val ⟶ Grp.trivial _) ≫ default
  have hone (R : TestAlgebra k) (x : GPoints I.val R) : onPoints one R x = 1 := by
    change onPoints ((default : I.val ⟶ Grp.trivial _) ≫ default) R x = 1
    rw [onPoints_comp]
    exact trivial_map_eq_one ⟨Iso.refl _⟩ _ _
  let := hf
  let := hsurj
  have hp : pow = one := by
    apply eq_of_flat_surjective_comp q
    apply group_hom_ext Z.property.1
    intro R x
    rw [onPoints_comp, onPoints_comp, hone, powerHom_points]
    apply onPoints_injective j hj R
    rw [map_pow, map_one, ← onPoints_comp, he, powerHom_points, ← pow_mul, ← pow_succ, hat]
    exact ha R x
  intro R x
  rw [← powerHom_points (commute_of_central N.isClosedImmersion hcen), ← show
    pow = powerHom I (commute_of_central N.isClosedImmersion hcen) p from rfl, hp]
  exact hone R x

private theorem exists_central_additive_charP [PerfectField k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k) (hG : IsUnipotent G) (hs : Smooth G.val.X.hom)
    (hc : ConnectedSpace G.val.X.left)
    (htr : ¬ Nonempty (G.val ≅ Grp.trivial (SchemeOver k))) :
    ∃ i : (StandardGroups.additiveGroup k).val ⟶ G.val,
      IsClosedImmersion i.hom.hom.left ∧ IsCentralIn i := by
  classical
  obtain ⟨D, hD, hDs, hDc, hDt⟩ := exists_central_lowerCentral G hG hs hc htr
  obtain ⟨N, hN, hNs, hNc, hNt, hNp⟩ := last_power_image (p := p) G hG D hD hDs hDc hDt
  let H := closedSubgroupAlgebraicGroup N
  let : Smooth H.val.X.hom := hNs
  let : ConnectedSpace H.val.X.left := hNc
  obtain ⟨d, V, ⟨j⟩, ⟨e⟩⟩ := perfectFieldVectorGroups p H
    (closedSubgroupsUnipotent G N hG) (commute_of_central N.isClosedImmersion hN) hNp
  let e' := (groupPointsFunctor k).mapIso j ≪≫ e
  have he : Nonempty (Index.{u} d) := by
    by_contra hn
    let : IsEmpty (Index.{u} d) := not_nonempty_iff.mp hn
    apply hNt
    refine ⟨terminalIso H (fun R x => ?_)⟩
    apply (ConcreteCategory.bijective_of_isIso (e'.hom.app R)).1
    change (_ : Index.{u} d → Multiplicative R) = _
    funext idx
    exact isEmptyElim idx
  let idx := he.some
  let A := StandardGroups.additiveGroup k
  let inPoints : Specs.StandardGroups.additivePoints k ⟶
      Specs.StandardGroups.additivePowerPoints k (Index.{u} d) :=
    { app R := GrpCat.ofHom
        { toFun t i := if i = idx then t else 1
          map_one' := by funext i; simp
          map_mul' x y := by funext i; by_cases h : i = idx <;> simp [h] }
      naturality R T a := by
        apply GrpCat.ext
        intro x
        funext i
        change (if i = idx then (((Specs.StandardGroups.additivePoints k).map a).hom x) else 1) =
          ((Specs.StandardGroups.additivePoints k).map a).hom (if i = idx then x else 1)
        by_cases hi : i = idx <;> simp [hi] }
  let outPoints : Specs.StandardGroups.additivePowerPoints k (Index.{u} d) ⟶
      Specs.StandardGroups.additivePoints k :=
    { app R := GrpCat.ofHom (Pi.evalMonoidHom _ idx)
      naturality _ _ _ := rfl }
  let u := (AffineAlgebraicGroup.groupHomEquiv A H).symm
    ((StandardGroups.additiveGroupPointsIso k).hom ≫ inPoints ≫ e'.inv)
  let v := (AffineAlgebraicGroup.groupHomEquiv H A).symm
    (e'.hom ≫ outPoints ≫ (StandardGroups.additiveGroupPointsIso k).inv)
  have huv : u ≫ v = 𝟙 A.val := by
    apply (AffineAlgebraicGroup.groupHomEquiv A A).injective
    change (groupPointsFunctor k).map (u ≫ v) = (groupPointsFunctor k).map (𝟙 A.val)
    have hop : inPoints ≫ outPoints = 𝟙 _ := by
      ext R x
      exact ite_eq_left rfl
    have hu : (groupPointsFunctor k).map u = _ :=
      (AffineAlgebraicGroup.groupHomEquiv A H).apply_symm_apply _
    have hv : (groupPointsFunctor k).map v = _ :=
      (AffineAlgebraicGroup.groupHomEquiv H A).apply_symm_apply _
    rw [Functor.map_comp, hu, hv]
    trans 𝟙 _
    · simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc inPoints, hop, Category.id_comp, Iso.hom_inv_id]
    · exact ((groupPointsFunctor k).map_id A.val).symm
  have hu : IsClosedImmersion u.hom.hom.left := by
    let := H.property.1
    let := A.property.1
    let : IsSeparated v.hom.hom.left := IsSeparated.of_isAffineHom _
    have hh : u.hom.hom.left ≫ v.hom.hom.left = 𝟙 A.val.X.left :=
      congrArg (fun a => a.hom.hom.left) huv
    let : IsClosedImmersion (u.hom.hom.left ≫ v.hom.hom.left) := hh ▸ inferInstance
    exact IsClosedImmersion.of_comp u.hom.hom.left v.hom.hom.left
  refine ⟨u ≫ N.inclusion, ?_, central_comp hN u⟩
  change IsClosedImmersion (u.hom.hom.left ≫ N.inclusion.hom.hom.left)
  let : IsClosedImmersion u.hom.hom.left := hu
  exact @IsClosedImmersion.comp _ _ _ u.hom.hom.left N.inclusion.hom.hom.left hu N.isClosedImmersion


attribute [local instance] specializationOrder

private def identityDimension (G : AffineAlgebraicGroup k) : ℕ :=
  (Order.coheight (groupIdentityPoint G.val)).toNat

private theorem group_coheight_lt_top (G : AffineAlgebraicGroup k) (x : G.val.X.left) :
    Order.coheight x < ⊤ := by
  have := G.property.2.1
  have := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  have h := ringKrullDim_lt_top (R := G.val.X.left.presheaf.stalk x)
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_lt_coe.mp h

private theorem identityDimension_eq_zero {G : AffineAlgebraicGroup k}
    (h : topologicalKrullDim G.val.X.left ≤ 0) : identityDimension G = 0 := by
  have hd : Order.krullDim G.val.X.left = topologicalKrullDim G.val.X.left :=
    (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm
  have hh := (Order.coheight_le_krullDim (groupIdentityPoint G.val)).trans (hd ▸ h)
  have hzero : Order.coheight (groupIdentityPoint G.val) ≤ 0 := WithBot.coe_le_coe.mp hh
  have he : Order.coheight (groupIdentityPoint G.val) = 0 := le_antisymm hzero bot_le
  simp only [identityDimension, he, ENat.toNat_zero]

private theorem ringKrullDim_le_of_faithfullyFlat (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [FiniteRingKrullDim A] [Module.FaithfullyFlat A B] :
    ringKrullDim A ≤ ringKrullDim B := by
  let l := LTSeries.longestOf (PrimeSpectrum A)
  obtain ⟨P, hP⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B)) l.last
  let : P.asIdeal.LiesOver l.last.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hP.symm⟩
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P.asIdeal
  change Order.krullDim (PrimeSpectrum A) ≤ _
  rw [Order.krullDim_eq_length_of_finiteDimensionalOrder, ← show l.length = _ from rfl, ← hlen]
  exact Order.LTSeries.length_le_krullDim L

private theorem coheight_le_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IsLocallyNoetherian Y] (x : X) :
    Order.coheight (f x) ≤ Order.coheight x := by
  rw [← WithBot.coe_le_coe, ← ringKrullDim_stalk_eq_coheight, ← ringKrullDim_stalk_eq_coheight]
  algebraize [(f.stalkMap x).hom]
  have := @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
    (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ringKrullDim_le_of_faithfullyFlat _ _

private theorem additive_point_specialization :
    ∃ x : (StandardGroups.additiveGroup k).val.X.left,
      x ≠ groupIdentityPoint (StandardGroups.additiveGroup k).val ∧
      x ⤳ groupIdentityPoint (StandardGroups.additiveGroup k).val := by
  let A := StandardGroups.additiveGroup k
  let y := groupIdentityPoint A.val
  let x : PrimeSpectrum (Polynomial k) := ⊥
  have hy : IsClosed ({y} : Set A.val.X.left) := by
    let : IsAffine A.val.X.left := A.property.1
    let : IsSeparated A.val.X.hom := IsSeparated.of_isAffineHom _
    let s := groupIdentitySection A.val
    have he : s ≫ A.val.X.hom = 𝟙 _ := (η[A.val.X]).w
    let : IsClosedImmersion (s ≫ A.val.X.hom) := he ▸ inferInstance
    have h : IsClosedImmersion s := IsClosedImmersion.of_comp s A.val.X.hom
    have hr : Set.range ⇑s = {y} := by
      ext t
      constructor
      · rintro ⟨z, rfl⟩
        exact Set.mem_singleton_iff.mpr (congrArg s (Subsingleton.elim z _))
      · rintro (rfl : t = y)
        exact ⟨IsLocalRing.closedPoint k, rfl⟩
    exact hr ▸ s.isClosedEmbedding.isClosed_range
  refine ⟨x, ?_, ?_⟩
  · intro h
    have hclosed : IsClosed ({x} : Set (PrimeSpectrum (Polynomial k))) := h ▸ hy
    have hx : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hclosed
    have hx0 : (⊥ : Ideal (Polynomial k)).IsMaximal := hx
    have hn := hx0.eq_of_le (Ideal.span_singleton_ne_top (Polynomial.not_isUnit_X (R := k))) bot_le
    exact Polynomial.X_ne_zero (Ideal.span_singleton_eq_bot.mp hn.symm)
  · exact (PrimeSpectrum.le_iff_specializes x y).mp bot_le

private theorem identityDimension_lt {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) [Flat q.hom.hom.left]
    (i : (StandardGroups.additiveGroup k).val ⟶ G.val) (hi : IsClosedImmersion i.hom.hom.left)
    (hk : IsSchemeKernel q ⟨_, i, hi⟩) :
    identityDimension Q < identityDimension G := by
  let : IsClosedImmersion i.hom.hom.left := hi
  obtain ⟨x, hne, hx⟩ := additive_point_specialization (k := k)
  let g := i.hom.hom.left x
  have hgid : i.hom.hom.left (groupIdentityPoint (StandardGroups.additiveGroup k).val) =
      groupIdentityPoint G.val := by
    exact congrArg (fun f : 𝟙_ (SchemeOver k) ⟶ G.val.X => f.left (IsLocalRing.closedPoint k))
      (IsMonHom.one_hom i.hom.hom)
  have hg : groupIdentityPoint G.val < g := by
    change g ⤳ groupIdentityPoint G.val ∧ ¬ groupIdentityPoint G.val ⤳ g
    rw [← hgid]
    refine ⟨hx.map i.hom.hom.left.continuous, ?_⟩
    intro h
    exact hne (i.hom.hom.left.isClosedEmbedding.injective
      ((hx.map i.hom.hom.left.continuous).antisymm h).eq)
  have hqg : q.hom.hom.left g = groupIdentityPoint Q.val := by
    have hw := congrArg (fun f => f.left x) hk.w
    exact hw.trans (congrArg (groupIdentitySection Q.val) (Subsingleton.elim _ _))
  have hlt := Order.coheight_strictAnti hg (group_coheight_lt_top G g)
  have := Q.property.2.1
  have := LocallyOfFiniteType.isLocallyNoetherian Q.val.X.hom
  have hle := coheight_le_of_flat q.hom.hom.left g
  rw [hqg] at hle
  unfold identityDimension
  have h := hle.trans_lt hlt
  have h' : (↑((Order.coheight (groupIdentityPoint Q.val)).toNat) : ℕ∞) <
      ↑((Order.coheight (groupIdentityPoint G.val)).toNat) := by
    rwa [ENat.natCast_toNat (group_coheight_lt_top Q _).ne,
      ENat.natCast_toNat (group_coheight_lt_top G _).ne]
  exact_mod_cast h'

open private quotientRepresentsImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private scheme_kernel_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

private theorem represented_quotient_of_kernel {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) (D : ClosedSubgroup G.val) (hk : IsSchemeKernel q D)
    (hf : Flat q.hom.hom.left) (hs : Surjective q.hom.hom.left)
    (hp : LocallyOfFinitePresentation q.hom.hom.left) :
    IsFppfGroupQuotient D q := by
  let := G.property.1
  let := Q.property.1
  refine ⟨hk, hf, hs, hp, ?_⟩
  exact quotientRepresentsImage (i := 𝟙 Q.val)
    ⟨Category.comp_id _, hf, hs, hp, inferInstance,
      inferInstanceAs (IsClosedImmersion (𝟙 Q.val.X.left))⟩ hk

private theorem trivial_inclusion_closed (G : AffineAlgebraicGroup k) :
    IsClosedImmersion (default : Grp.trivial (SchemeOver k) ⟶ G.val).hom.hom.left := by
  let := G.property.1
  let : IsSeparated G.val.X.hom := IsSeparated.of_isAffineHom _
  let f := (default : Grp.trivial (SchemeOver k) ⟶ G.val).hom.hom
  have hf : f.left ≫ G.val.X.hom = 𝟙 _ := f.w
  let : IsClosedImmersion (f.left ≫ G.val.X.hom) := hf ▸
    inferInstanceAs (IsClosedImmersion (𝟙 (Spec (CommRingCat.of k))))
  exact IsClosedImmersion.of_comp f.left G.val.X.hom

section LiftSeries

variable {G Q : AffineAlgebraicGroup k} {n : ℕ}
variable (q : G.val ⟶ Q.val) (S : ClosedSeries Q n)

private abbrev inverseImageGroup (i : ℕ) :=
  pullback q (S.inclusion i)

private abbrev inverseImageInclusion (i : ℕ) :
    inverseImageGroup q S i ⟶ G.val :=
  pullback.fst q (S.inclusion i)

private abbrev inverseImageProjection (i : ℕ) :
    inverseImageGroup q S i ⟶ (S.term i).val :=
  pullback.snd q (S.inclusion i)

private theorem inverseImage_square (i : ℕ) :
    IsPullback (inverseImageInclusion q S i).hom.hom (inverseImageProjection q S i).hom.hom
      q.hom.hom (S.inclusion i).hom.hom :=
  (Grp.forget (SchemeOver k)).map_isPullback (.of_hasPullback q (S.inclusion i))

private theorem inverseImage_closed (i : ℕ) :
    IsClosedImmersion (inverseImageInclusion q S i).hom.hom.left :=
  MorphismProperty.of_isPullback ((inverseImage_square q S i).map (Over.forget _)).flip
    (closedSeries_inclusion_closed S i)

private abbrev inverseImage (i : ℕ) : AffineAlgebraicGroup k :=
  ⟨inverseImageGroup q S i,
    (closedSubgroupAlgebraicGroup (G := G)
      ⟨_, inverseImageInclusion q S i, inverseImage_closed q S i⟩).property⟩

private def inverseImageStep (i : ℕ) :
    (inverseImage q S (i + 1)).val ⟶ (inverseImage q S i).val :=
  pullback.lift (inverseImageInclusion q S (i + 1))
    (inverseImageProjection q S (i + 1) ≫ S.step i) (by
      rw [Category.assoc]
      exact pullback.condition)

private theorem inverseImageStep_fst (i : ℕ) :
    inverseImageStep q S i ≫ inverseImageInclusion q S i =
      inverseImageInclusion q S (i + 1) :=
  pullback.lift_fst ..

private theorem inverseImageStep_snd (i : ℕ) :
    inverseImageStep q S i ≫ inverseImageProjection q S i =
      inverseImageProjection q S (i + 1) ≫ S.step i :=
  pullback.lift_snd ..

private theorem inverseImageStep_closed (i : ℕ) :
    IsClosedImmersion (inverseImageStep q S i).hom.hom.left := by
  have he := congrArg (fun a => a.hom.hom.left) (inverseImageStep_fst q S i)
  change (inverseImageStep q S i).hom.hom.left ≫ (inverseImageInclusion q S i).hom.hom.left =
    (inverseImageInclusion q S (i + 1)).hom.hom.left at he
  exact @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ (inverseImageStep q S i).hom.hom.left
    (inverseImageInclusion q S i).hom.hom.left (inverseImage_closed q S i)
    (he.symm ▸ inverseImage_closed q S (i + 1))

private theorem inverseImageInclusion_top :
    IsIso (inverseImageInclusion q S 0) := by
  let : IsIso (S.inclusion 0) := inferInstanceAs (IsIso S.top.hom)
  exact (IsPullback.of_hasPullback q (S.inclusion 0)).isIso_fst_of_isIso

private theorem inverseImage_point (i : ℕ) (R : TestAlgebra k)
    (x : GPoints G.val R) (y : GPoints (S.term i).val R)
    (h : onPoints q R x = onPoints (S.inclusion i) R y) :
    ∃ z : GPoints (inverseImage q S i).val R,
      onPoints (inverseImageInclusion q S i) R z = x ∧
        onPoints (inverseImageProjection q S i) R z = y := by
  let pb := inverseImage_square q S i
  exact ⟨pb.lift x y h, pb.lift_fst x y h, pb.lift_snd x y h⟩

private def trivialAffine (k : Type u) [Field k] : AffineAlgebraicGroup k := by
  refine ⟨Grp.trivial (SchemeOver k), ?_, ?_, ?_⟩
  · change IsAffine (Spec (CommRingCat.of k))
    infer_instance
  · change LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  · change QuasiCompact (𝟙 (Spec (CommRingCat.of k)))
    infer_instance

private def liftedTerm (i : ℕ) : AffineAlgebraicGroup k :=
  if i ≤ n then inverseImage q S i else trivialAffine k

private def liftedTermIso (i : ℕ) (hi : i ≤ n) :
    (liftedTerm q S i).val ≅ (inverseImage q S i).val :=
  eqToIso (congrArg Subtype.val (ite_eq_left hi))

private def liftedTermTrivial (i : ℕ) (hi : n < i) :
    (liftedTerm q S i).val ≅ Grp.trivial (SchemeOver k) :=
  eqToIso (congrArg Subtype.val (ite_eq_right hi.not_ge))

private def liftedStep (i : ℕ) :
    (liftedTerm q S (i + 1)).val ⟶ (liftedTerm q S i).val :=
  if hi : i < n then
    (liftedTermIso q S (i + 1) hi).hom ≫ inverseImageStep q S i ≫
      (liftedTermIso q S i hi.le).inv
  else
    (liftedTermTrivial q S (i + 1) (by omega)).hom ≫ default

private theorem liftedStep_closed (i : ℕ) :
    IsClosedImmersion (liftedStep q S i).hom.hom.left := by
  unfold liftedStep
  split
  · rename_i hi
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    change IsClosedImmersion (F.map (liftedTermIso q S (i + 1) hi).hom ≫
      F.map (inverseImageStep q S i) ≫ F.map (liftedTermIso q S i hi.le).inv)
    let : IsClosedImmersion (F.map (inverseImageStep q S i)) := inverseImageStep_closed q S i
    infer_instance
  · rename_i hi
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    change IsClosedImmersion (F.map (liftedTermTrivial q S (i + 1) (by omega)).hom ≫
      F.map (default : Grp.trivial (SchemeOver k) ⟶ (liftedTerm q S i).val))
    let : IsClosedImmersion (F.map
        (default : Grp.trivial (SchemeOver k) ⟶ (liftedTerm q S i).val)) :=
      trivial_inclusion_closed (liftedTerm q S i)
    infer_instance

private abbrev liftSeries : ClosedSeries G (n + 1) where
  term := liftedTerm q S
  top := by
    let e : inverseImageGroup q S 0 ≅ G.val :=
      @asIso _ _ _ _ (inverseImageInclusion q S 0) (inverseImageInclusion_top q S)
    exact liftedTermIso q S 0 (Nat.zero_le n) ≪≫ e
  bottom := liftedTermTrivial q S (n + 1) (Nat.lt_succ_self _)
  step := liftedStep q S
  closed := liftedStep_closed q S

private theorem liftSeries_inclusion {i : ℕ} (hi : i ≤ n) :
    (liftSeries q S).inclusion i =
      (liftedTermIso q S i hi).hom ≫ inverseImageInclusion q S i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change liftedStep q S i ≫ (liftSeries q S).inclusion i = _
    rw [ih (by omega)]
    unfold liftedStep
    rw [dite_eq_left (show i < n by omega)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, inverseImageStep_fst]

private theorem inverseImageEnd_kernel (D : ClosedSubgroup G.val) (hd : IsSchemeKernel q D) :
    ∃ e : (liftedTerm q S n).val ≅ D.group,
      e.hom ≫ D.inclusion = (liftSeries q S).inclusion n := by
  let P := inverseImage q S n
  let p := inverseImageInclusion q S n
  have hp := inverseImage_closed q S n
  let A := closedSubgroupAlgebraicGroup D
  have hs (R : TestAlgebra k) (x : GPoints P.val R) :
      ∃ y : GPoints A.val R, onPoints D.inclusion R y = onPoints p R x := by
    apply (kernel_points q D hd R _).mp
    have hw := congrArg (fun f => x ≫ f) (inverseImage_square q S n).w
    exact hw.trans
      ((Category.assoc x (inverseImageProjection q S n).hom.hom (S.inclusion n).hom.hom).symm.trans
        (trivial_map_eq_one ⟨S.bottom⟩ (S.inclusion n) _))
  obtain ⟨f, hf⟩ := factor_through_closed (A := P) (B := A) p D.inclusion D.isClosedImmersion hs
  have hcl : IsClosedImmersion f.hom.hom.left :=
    closed_of_comp f D.inclusion (hf.symm ▸ hp) D.isClosedImmersion
  have hsur (R : TestAlgebra k) (y : GPoints A.val R) :
      ∃ x : GPoints P.val R, onPoints f R x = y := by
    have he : onPoints q R (onPoints D.inclusion R y) = 1 :=
      (kernel_points q D hd R _).mpr ⟨y, rfl⟩
    obtain ⟨x, hx, _⟩ := inverseImage_point q S n R (onPoints D.inclusion R y) 1
      (he.trans (onPoints (S.inclusion n) R).map_one.symm)
    refine ⟨x, onPoints_injective D.inclusion D.isClosedImmersion R ?_⟩
    calc
      _ = onPoints (f ≫ D.inclusion) R x := rfl
      _ = _ := (congrArg (fun a => onPoints a R x) hf).trans hx
  let e : P.val ≅ A.val := @asIso _ _ _ _ f (closed_surjective_points_iso f hcl hsur)
  refine ⟨liftedTermIso q S n le_rfl ≪≫ e, ?_⟩
  rw [liftSeries_inclusion q S le_rfl]
  change (_ ≫ f) ≫ D.inclusion = _
  rw [Category.assoc, hf]

end LiftSeries

section LiftSeriesExact

variable {G Q : AffineAlgebraicGroup k} {n : ℕ}
variable (q : G.val ⟶ Q.val) (S : ClosedSeries Q n)

private abbrev liftSeries_map (i : ℕ) (hi : i ≤ n) :
    ((liftSeries q S).term i).val ⟶ (S.term i).val :=
  (liftedTermIso q S i hi).hom ≫ inverseImageProjection q S i

private theorem liftSeries_comm (i : ℕ) (hi : i ≤ n) :
    (liftSeries q S).inclusion i ≫ q =
      liftSeries_map q S i hi ≫ S.inclusion i := by
  rw [liftSeries_inclusion q S hi]
  simp only [liftSeries_map, Category.assoc]
  exact congrArg ((liftedTermIso q S i hi).hom ≫ ·) (pullback.condition (f := q) (g := S.inclusion i))

private theorem liftSeries_point (i : ℕ) (hi : i ≤ n) (R : TestAlgebra k)
    (x : GPoints G.val R) (y : GPoints (S.term i).val R)
    (h : onPoints q R x = onPoints (S.inclusion i) R y) :
    ∃ z : GPoints ((liftSeries q S).term i).val R,
      onPoints ((liftSeries q S).inclusion i) R z = x ∧
        onPoints (liftSeries_map q S i hi) R z = y := by
  obtain ⟨z, hx, hy⟩ := inverseImage_point q S i R x y h
  let e := liftedTermIso q S i hi
  refine ⟨onPoints e.inv R z, ?_, ?_⟩
  · rw [liftSeries_inclusion q S hi, ← onPoints_comp, ← Category.assoc, e.inv_hom_id,
      Category.id_comp, hx]
  · change onPoints (e.hom ≫ inverseImageProjection q S i) R (onPoints e.inv R z) = _
    rw [← onPoints_comp, ← Category.assoc, e.inv_hom_id, Category.id_comp, hy]

private theorem liftSeries_central (hS : S.IsCentral)
    (D : ClosedSubgroup G.val) (hD : IsCentralIn D.inclusion) (hk : IsSchemeKernel q D) :
    (liftSeries q S).IsCentral := by
  intro i hi R x y
  change ∃ z : GPoints ((liftSeries q S).term (i + 1)).val R,
    onPoints ((liftSeries q S).inclusion (i + 1)) R z =
      x * onPoints ((liftSeries q S).inclusion i) R y * x⁻¹ *
        (onPoints ((liftSeries q S).inclusion i) R y)⁻¹
  by_cases hit : i < n
  · have hle : i ≤ n := hit.le
    obtain ⟨z, hz⟩ := hS i hit R (onPoints q R x) (onPoints (liftSeries_map q S i hle) R y)
    change onPoints (S.inclusion (i + 1)) R z = _ at hz
    let a := onPoints ((liftSeries q S).inclusion i) R y
    have hqa : onPoints q R a = onPoints (S.inclusion i) R (onPoints (liftSeries_map q S i hle) R y) := by
      rw [← onPoints_comp, liftSeries_comm q S i hle, onPoints_comp]
    have hq : onPoints q R (x * a * x⁻¹ * a⁻¹) = onPoints (S.inclusion (i + 1)) R z := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hqa]
      exact hz.symm
    obtain ⟨w, hw, _⟩ := liftSeries_point q S (i + 1) hit R _ z hq
    exact ⟨w, hw⟩
  · have hi' : i = n := by omega
    subst i
    obtain ⟨e, he⟩ := inverseImageEnd_kernel q S D hk
    refine ⟨1, ?_⟩
    rw [map_one, ← he, onPoints_comp]
    have hh : Commute x (onPoints D.inclusion R (onPoints e.hom R y)) :=
      hD _ x (onPoints e.hom R y)
    exact (commutatorElement_eq_one_iff_commute.mpr hh).symm

private theorem liftSeries_factor {i : ℕ} (hi : i < n) [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    {L : AffineAlgebraicGroup k} (p : (S.term i).val ⟶ L.val)
    (hp : IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ p) :
    IsFppfGroupQuotient ⟨_, (liftSeries q S).step i, (liftSeries q S).closed i⟩
      (liftSeries_map q S i hi.le ≫ p) := by
  let T := liftSeries q S
  let r := liftSeries_map q S i hi.le
  have hr : r ≫ S.inclusion i = T.inclusion i ≫ q := (liftSeries_comm q S i hi.le).symm
  have hstep : T.step i ≫ r =
      liftSeries_map q S (i + 1) hi ≫ S.step i := by
    change liftedStep q S i ≫ _ = _
    unfold liftedStep
    rw [dite_eq_left hi]
    dsimp only [r, liftSeries_map]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, inverseImageStep_snd]
  have hflat : Flat r.hom.hom.left := by
    have hpb := (inverseImage_square q S i).map (Over.forget _)
    have h := MorphismProperty.of_isPullback (P := @Flat) hpb
      (inferInstance : Flat q.hom.hom.left)
    change Flat ((liftedTermIso q S i hi.le).hom.hom.hom.left ≫
      (inverseImageProjection q S i).hom.hom.left)
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    have : IsIso (F.map (liftedTermIso q S i hi.le).hom) := F.map_isIso _
    exact MorphismProperty.comp_mem _ (F.map (liftedTermIso q S i hi.le).hom) _ inferInstance h
  have hsurj : Surjective r.hom.hom.left := by
    have hpb := (inverseImage_square q S i).map (Over.forget _)
    have h := MorphismProperty.of_isPullback (P := @Surjective) hpb
      (inferInstance : Surjective q.hom.hom.left)
    change Surjective ((liftedTermIso q S i hi.le).hom.hom.hom.left ≫
      (inverseImageProjection q S i).hom.hom.left)
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    have : IsIso (F.map (liftedTermIso q S i hi.le).hom) := F.map_isIso _
    exact MorphismProperty.comp_mem _ (F.map (liftedTermIso q S i hi.le).hom) _ inferInstance h
  have hfp : LocallyOfFinitePresentation r.hom.hom.left := by
    have hpb := (inverseImage_square q S i).map (Over.forget _)
    have h := MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb
      (inferInstance : LocallyOfFinitePresentation q.hom.hom.left)
    change LocallyOfFinitePresentation ((liftedTermIso q S i hi.le).hom.hom.hom.left ≫
      (inverseImageProjection q S i).hom.hom.left)
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    have : IsIso (F.map (liftedTermIso q S i hi.le).hom) := F.map_isIso _
    exact MorphismProperty.comp_mem _ (F.map (liftedTermIso q S i hi.le).hom) _ inferInstance h
  refine represented_quotient_of_kernel (r ≫ p) _ ?_ ?_ ?_ ?_
  · apply scheme_kernel_of_points
    intro R x
    rw [onPoints_comp, kernel_points p ⟨_, S.step i, S.closed i⟩ hp.1]
    constructor
    · rintro ⟨y, hy⟩
      have he : onPoints q R (onPoints (T.inclusion i) R x) =
          onPoints (S.inclusion (i + 1)) R y := by
        rw [← onPoints_comp, ← hr, onPoints_comp, ← hy]
        rfl
      obtain ⟨z, hz, _⟩ := liftSeries_point q S (i + 1) hi R _ y he
      refine ⟨z, onPoints_injective (T.inclusion i) (closedSeries_inclusion_closed T i) R ?_⟩
      rwa [← onPoints_comp]
    · rintro ⟨z, rfl⟩
      refine ⟨onPoints (liftSeries_map q S (i + 1) hi) R z, ?_⟩
      rw [← onPoints_comp, ← onPoints_comp, hstep]
  · exact MorphismProperty.comp_mem @Flat _ _ hflat hp.2.1
  · exact MorphismProperty.comp_mem @Surjective _ _ hsurj hp.2.2.1
  · exact MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ hfp hp.2.2.2.1

private theorem liftSeries_last_factor (i : (StandardGroups.additiveGroup k).val ⟶ G.val)
    (hi : IsClosedImmersion i.hom.hom.left) (hk : IsSchemeKernel q ⟨_, i, hi⟩) :
    ∃ p : ((liftSeries q S).term n).val ⟶ (StandardGroups.additiveGroup k).val,
      IsFppfGroupQuotient ⟨_, (liftSeries q S).step n, (liftSeries q S).closed n⟩ p := by
  obtain ⟨e, _⟩ := inverseImageEnd_kernel q S ⟨_, i, hi⟩ hk
  refine ⟨e.hom, represented_quotient_of_kernel e.hom _ ?_ ?_ ?_ ?_⟩
  · apply scheme_kernel_of_points
    intro R x
    have hT : Nonempty (((liftSeries q S).term (n + 1)).val ≅ Grp.trivial (SchemeOver k)) :=
      ⟨(liftSeries q S).bottom⟩
    constructor
    · intro hx
      refine ⟨1, ?_⟩
      rw [map_one]
      apply (ConcreteCategory.bijective_of_isIso (((groupPointsFunctor k).map e.hom).app R)).1
      exact ((onPoints e.hom R).map_one.trans hx.symm)
    · rintro ⟨y, rfl⟩
      rw [show onPoints ((liftSeries q S).step n) R y = 1 from trivial_map_eq_one hT _ y,
        map_one]
  · exact inferInstanceAs (Flat ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map e.hom))
  · exact inferInstanceAs (Surjective ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map e.hom))
  · exact inferInstanceAs (LocallyOfFinitePresentation ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map e.hom))

end LiftSeriesExact

theorem perfectFieldSplitness : PerfectFieldSplitness.{u} := by
  intro k _ _ G
  suffices h : ∀ d : ℕ, ∀ G : AffineAlgebraicGroup k, identityDimension G = d →
      Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsUnipotent G →
      ∃ (length : ℕ) (S : ClosedSeries G length), S.IsCentral ∧
        (topologicalKrullDim G.val.X.left ≤ 0 → length = 0) ∧
        ∀ i < length, ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
          IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
          Nonempty ((groupPointsFunctor k).obj Q.val ≅ Specs.StandardGroups.additivePoints k) from
    h (identityDimension G) G rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro G hG hs hc hu
    classical
    by_cases ht : Nonempty (G.val ≅ Grp.trivial (SchemeOver k))
    · refine ⟨0, ⟨fun _ => G, Iso.refl _, ht.some, fun _ => 𝟙 _, fun _ => inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left))⟩,
        fun i hi => (Nat.not_lt_zero i hi).elim, fun _ => rfl,
        fun i hi => (Nat.not_lt_zero i hi).elim⟩
    · obtain ⟨j, hj, hcentral⟩ :
          ∃ j : (StandardGroups.additiveGroup k).val ⟶ G.val,
            IsClosedImmersion j.hom.hom.left ∧ IsCentralIn j := by
        rcases CharP.exists' k with h | ⟨p, hp, hkp⟩
        · exact exists_central_additive_charZero G hu ht
        · exact exists_central_additive_charP (p := p) G hu hs hc ht
      let D : ClosedSubgroup G.val := ⟨_, j, hj⟩
      obtain ⟨L, f, Q, q, e, _, hk, hfac, _, _⟩ :=
        normalAffineQuotient G D (central_normal hcentral)
      let : Flat q.hom.hom.left := hfac.2.1
      let : Surjective q.hom.hom.left := hfac.2.2.1
      let : LocallyOfFinitePresentation q.hom.hom.left := hfac.2.2.2.1
      obtain ⟨hQs, hQc⟩ := affine_quotient_smooth_connected q hfac.2.1 hfac.2.2.1 hs hc
      have hQ : identityDimension Q < d := hG ▸ identityDimension_lt q j hj hk
      have hQu := faithfullyFlatQuotientsUnipotent G Q q hfac.2.1 hfac.2.2.1 hu
      obtain ⟨n, S, hS, _, hF⟩ := ih _ hQ Q rfl hQs hQc hQu
      refine ⟨n + 1, liftSeries q S, liftSeries_central q S hS D hcentral hk, ?_, ?_⟩
      · intro h
        have hd : d = 0 := hG.symm.trans (identityDimension_eq_zero h)
        exact (Nat.not_lt_zero _ (hd ▸ hQ)).elim
      intro i hi
      by_cases hin : i < n
      · obtain ⟨A, a, ha, hGa⟩ := hF i hin
        exact ⟨A, liftSeries_map q S i hin.le ≫ a, liftSeries_factor q S hin a ha, hGa⟩
      · have he : i = n := by omega
        subst i
        obtain ⟨p, hp⟩ := liftSeries_last_factor q S j hj hk
        exact ⟨StandardGroups.additiveGroup k, p, hp, ⟨StandardGroups.additiveGroupPointsIso k⟩⟩

theorem perfectFieldIsSplitUnipotent : PerfectFieldIsSplitUnipotent.{u} := by
  intro k _ _ G hs hc hu
  obtain ⟨n, S, _, _, hF⟩ := perfectFieldSplitness G hs hc hu
  refine ⟨hu, n, S, fun i hi => ?_⟩
  obtain ⟨Q, q, hq, hGa⟩ := hF i hi
  exact ⟨Q, q, hq, Or.inr hGa⟩

end

end LinearAlgebraicGroups.Unipotent
