import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SteinbergGeometricFibres
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SteinbergPinnedDescent
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.List.NodupEquivFin
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalSteinbergSection
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

open scoped BigOperators

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalSteinbergSection

open Specs.ExceptionalSteinbergSection

section CoxeterWord

variable {R I X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]

@[simp] private theorem reflectionWord_nil (P : RootPairing I R X Y) :
    reflectionWord P [] = 1 := rfl

@[simp] private theorem reflectionWord_cons (P : RootPairing I R X Y)
    (a : I) (l : List I) :
    reflectionWord P (a :: l) = P.reflection a * reflectionWord P l := rfl

private theorem reflectionWord_append (P : RootPairing I R X Y) (l m : List I) :
    reflectionWord P (l ++ m) = reflectionWord P l * reflectionWord P m := by
  simp [reflectionWord, List.prod_append]

private theorem reflectionWord_sub_mem_span (P : RootPairing I R X Y) (l : List I)
    (x : X) : reflectionWord P l x - x ∈ Submodule.span R (P.root '' {a | a ∈ l}) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl : Submodule.span R (P.root '' {a | a ∈ l}) ≤
        Submodule.span R (P.root '' {i | i ∈ a :: l}) :=
      Submodule.span_mono (Set.image_mono (fun _ hi ↦ List.mem_cons_of_mem _ hi))
    have ha : P.root a ∈ Submodule.span R (P.root '' {i | i ∈ a :: l}) :=
      Submodule.subset_span ⟨a, List.mem_cons_self, rfl⟩
    simpa [LinearEquiv.mul_apply, P.reflection_apply, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using
      Submodule.sub_mem _ (hl ih) (Submodule.smul_mem _ (P.coroot' a (reflectionWord P l x)) ha)

theorem coxeterTriangularity : CoxeterTriangularity := by
  intro R I X Y _ _ _ _ _ P roots i
  exact reflectionWord_sub_mem_span P (roots.take i.val) (P.root (roots.get i))

private theorem reflectionWord_fix (P : RootPairing I R X Y) (l : List I) (x : X)
    (h : ∀ a ∈ l, P.toLinearMap x (P.coroot a) = 0) :
    reflectionWord P l x = x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [reflectionWord_cons, LinearEquiv.mul_apply, ih (fun a ha ↦ h a (by simp [ha])),
      P.reflection_apply]
    change x - P.toLinearMap x (P.coroot a) • P.root a = x
    simp [h a (by simp)]

theorem coxeterDisplacement : CoxeterDisplacement := by
  classical
  intro R I X Y _ _ _ _ _ P roots i ω hω
  have hi := i.isLt
  have hsplit : roots = roots.take i.val ++ roots.get i :: roots.drop (i.val + 1) := by
    conv_lhs => rw [← List.take_append_drop i.val roots, List.drop_eq_getElem_cons hi]
    rfl
  have hfixpre : reflectionWord P (roots.take i.val) ω = ω := by
    apply reflectionWord_fix
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hj' : j < i.val := by simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] using hj
    have hne : (⟨j, hj'.trans hi⟩ : Fin roots.length) ≠ i := by
      intro he
      exact (Nat.ne_of_lt hj') (congrArg Fin.val he)
    simpa [List.getElem_take, hne] using hω ⟨j, hj'.trans hi⟩
  have hfixpost : reflectionWord P (roots.drop (i.val + 1)) ω = ω := by
    apply reflectionWord_fix
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hj' : i.val + 1 + j < roots.length := by
      rw [List.length_drop] at hj
      omega
    have hne : (⟨i.val + 1 + j, hj'⟩ : Fin roots.length) ≠ i := by
      intro he
      have := congrArg Fin.val he
      change i.val + 1 + j = i.val at this
      omega
    simpa [List.getElem_drop, hne] using hω ⟨i.val + 1 + j, hj'⟩
  have href : P.reflection (roots.get i) ω = ω - P.root (roots.get i) := by
    rw [P.reflection_apply]
    change ω - P.toLinearMap ω (P.coroot (roots.get i)) • P.root (roots.get i) = _
    rw [hω i, ite_eq_left rfl, one_smul]
  change _ = reflectionWord P (roots.take i.val) (P.root (roots.get i))
  rw [congrArg (fun l ↦ reflectionWord P l ω) hsplit,
    reflectionWord_append, reflectionWord_cons, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    hfixpost, href, map_sub, hfixpre, sub_sub_cancel]

private theorem reflectionWord_fixed_pairings (P : RootPairing I R X Y) (l : List I)
    (hn : l.Nodup) (hli : LinearIndepOn R P.root {a | a ∈ l}) (x : X)
    (hx : reflectionWord P l x = x) :
    ∀ a ∈ l, P.toLinearMap x (P.coroot a) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    have htail : reflectionWord P l x = P.reflection a x := by
      apply (P.reflection a).injective
      simpa [LinearEquiv.mul_apply] using hx
    have hs := reflectionWord_sub_mem_span P l x
    rw [htail, P.reflection_apply, sub_sub_cancel_left] at hs
    have hsmul : P.toLinearMap x (P.coroot a) • P.root a ∈
        Submodule.span R (P.root '' {i | i ∈ l}) := by
      simpa using Submodule.neg_mem _ hs
    have ha : P.toLinearMap x (P.coroot a) = 0 := by
      apply hli.eq_zero_of_smul_mem_span (List.mem_cons_self (a := a)) _
      refine Submodule.span_mono (Set.image_mono ?_) hsmul
      intro i hi
      exact ⟨List.mem_cons_of_mem _ hi, fun (he : i = a) ↦ hn'.1 (he ▸ hi)⟩
    have htail' : reflectionWord P l x = x := by
      rw [htail, P.reflection_apply]
      change x - P.toLinearMap x (P.coroot a) • P.root a = x
      simp [ha]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact ih hn'.2 (hli.mono (fun _ hi ↦ List.mem_cons_of_mem _ hi)) htail' b hb

theorem coxeterInjectivity : CoxeterInjectivity := by
  intro R I X Y _ _ _ _ _ P roots hn hli hdetect x y hxy
  have hzero : x - (reflectionWord P roots) x - (y - (reflectionWord P roots) y) = 0 :=
    sub_eq_zero.mpr hxy
  have hfix : reflectionWord P roots (x - y) = x - y := by
    rw [map_sub, ← sub_eq_zero]
    calc
      reflectionWord P roots x - reflectionWord P roots y - (x - y) =
          -(x - reflectionWord P roots x - (y - reflectionWord P roots y)) := by abel
      _ = 0 := by rw [hzero, neg_zero]
  exact sub_eq_zero.mp (hdetect _ (reflectionWord_fixed_pairings P roots hn hli _ hfix))

theorem coxeterWeightRouting : CoxeterWeightRouting := by
  intro R I X Y _ _ _ _ _ P roots ω hω hc m μ hm
  apply hc
  calc
    μ - reflectionWord P roots μ = ∑ i, m i • transportedRoot P roots i :=
      sub_eq_of_eq_add (by simpa only [add_comm] using hm.symm)
    _ = (∑ i, m i • ω i) - reflectionWord P roots (∑ i, m i • ω i) := by
      simp_rw [← coxeterDisplacement P roots _ _ (fun j ↦ hω _ j), nsmul_sub,
        Finset.sum_sub_distrib, map_sum, map_nsmul]

end CoxeterWord

theorem fundamentalCoordinates : FundamentalCoordinates := by
  classical
  intro I X Y _ _ P b hspan
  let corootBasis : Module.Basis b.support ℤ Y :=
    Module.Basis.mk b.linearIndepOn_coroot (ge_of_eq (by
      rw [← Set.image_eq_range, b.span_int_coroot_support, hspan]))
  refine ⟨P.toLinearMap.toPerfPair.trans corootBasis.dualBasis.equivFun, ?_⟩
  intro x i
  change corootBasis.dualBasis.equivFun (P.toLinearMap x) i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]
  congr 1
  exact Module.Basis.mk_apply _ _ _

theorem attachedFundamentalCoordinates : AttachedFundamentalCoordinates.{u} := by
  intro k _ P D hspan
  let := D.comm
  exact fundamentalCoordinates D.datum.rootDatum D.base hspan

theorem rationalCoxeterBijectivity : RationalCoxeterBijectivity := by
  intro I X Y _ _ _ _ _ P roots hnodup hind hspan
  have hinj := coxeterInjectivity P roots hnodup hind (by
    intro x hx
    apply P.toLinearMap.toPerfPair.injective
    ext y
    simp only [map_zero, LinearMap.zero_apply]
    change P.toLinearMap x y = 0
    apply LinearMap.mem_ker.mp
    have hle : Submodule.span ℚ (P.coroot '' {a | a ∈ roots}) ≤ (P.toLinearMap x).ker := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact hx i hi
    exact hle (by simp [hspan]))
  let f : X →ₗ[ℚ] X := LinearMap.id - (reflectionWord P roots).toLinearMap
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := f)).mp hinj⟩

theorem rewriteRootWord : RewriteRootWord := by
  intro J G _ order x n initial
  induction order generalizing initial with
  | nil => simp [rootWord]
  | cons a order ih =>
    have hzero : conjugatedRoot (a :: order) x n initial 0 = initial * x a * initial⁻¹ := by
      simp [conjugatedRoot]
    have hsucc :
        conjugatedRoot (a :: order) x n initial ∘
          (Fin.succ : Fin order.length → Fin (a :: order).length) =
        conjugatedRoot order x n (initial * n a) := by
      funext i
      simp [conjugatedRoot, mul_assoc]
    simp only [rootWord, List.length_cons, List.finRange_succ, List.map_cons, List.map_map,
      List.prod_cons, hzero, hsucc] at ih ⊢
    rw [← mul_assoc initial (n a), mul_assoc (initial * x a * initial⁻¹),
      ← ih (initial * n a)]
    group


theorem permuteRootWordBlocks : PermuteRootWordBlocks := by
  intro J G _ blocks blocks' x n h
  induction h with
  | nil => rfl
  | cons hblock _ ih =>
    simp only [List.flatten_cons, rootWord, List.map_append, List.prod_append] at ih ⊢
    rw [ih, (hblock.1.map _).prod_eq' hblock.2]

section TraceParameters

variable {L J : Type*} [Field L]

private noncomputable def solveCoordinates (height : J → ℤ) (d : J → L)
    (p : J → MvPolynomial J L) (b : J → L) : J → L :=
  (measure (fun i ↦ (height i).toNat)).wf.fix fun j lower ↦
    (b j - MvPolynomial.eval
      (fun i ↦ if h : (height i).toNat < (height j).toNat then lower i h else 0) (p j)) / d j

theorem triangularParameters : TriangularParameters := by
  classical
  intro L J _ height d p hpos hd hp
  have hsmall : ∀ {j i : J} {m : J →₀ ℕ}, i ∈ m.support → (p j).coeff m ≠ 0 →
      (height i).toNat < (height j).toNat := by
    intro j i m hi hm
    have := hp j m hm i hi
    have := hpos i
    have := hpos j
    omega
  constructor
  · intro t u htu
    funext j
    induction j using (measure (fun i ↦ (height i).toNat)).wf.induction with
    | h j ih =>
      have hev : MvPolynomial.eval t (p j) = MvPolynomial.eval u (p j) := by
        apply MvPolynomial.eval₂_congr
        intro i m hi hm
        exact ih i (hsmall hi hm)
      have heq := congrFun htu j
      change d j * t j + MvPolynomial.eval t (p j) =
        d j * u j + MvPolynomial.eval u (p j) at heq
      rw [hev] at heq
      exact mul_left_cancel₀ (hd j) (add_right_cancel heq)
  · intro b
    refine ⟨solveCoordinates height d p b, funext fun j ↦ ?_⟩
    have hev : MvPolynomial.eval
        (fun i ↦ if (height i).toNat < (height j).toNat then solveCoordinates height d p b i else 0)
        (p j) = MvPolynomial.eval (solveCoordinates height d p b) (p j) := by
      apply MvPolynomial.eval₂_congr
      intro i m hi hm
      rw [ite_eq_left (hsmall hi hm)]
    have hsolve : solveCoordinates height d p b j =
        (b j - MvPolynomial.eval (solveCoordinates height d p b) (p j)) / d j := by
      conv_lhs => rw [solveCoordinates, WellFounded.fix_eq]
      simpa only [solveCoordinates, dite_eq_ite] using congrArg (fun a ↦ (b j - a) / d j) hev
    change d j * solveCoordinates height d p b j +
      MvPolynomial.eval (solveCoordinates height d p b) (p j) = b j
    rw [hsolve, mul_comm (d j), div_mul_cancel₀ _ (hd j), sub_add_cancel]

end TraceParameters

theorem outerE6Orthogonality : OuterE6Orthogonality := by
  unfold OuterE6Orthogonality
  decide

section InvariantLaurentPolynomials

variable {L X W : Type*} [Field L] [CommGroup X] [Group W]

@[simp] private theorem eval_single (z : X →* Lˣ) (x : X) (c : L) :
    laurentEvaluation z (MonoidAlgebra.single x c) = c * (z x : L) := by
  unfold laurentEvaluation
  rw [MonoidAlgebra.liftNCRingHom_single]
  rfl

private theorem eval_translate (e : MulAut X) (z : X →* Lˣ) (p : MonoidAlgebra L X) :
    laurentEvaluation z (MonoidAlgebra.mapDomainRingEquiv L e p) =
      laurentEvaluation (z.comp e.toMonoidHom) p := by
  apply DFunLike.congr_fun (f := (laurentEvaluation z).comp
    (MonoidAlgebra.mapDomainRingEquiv L e).toRingHom)
  apply MonoidAlgebra.ringHom_ext
  · intro l
    simp
  · intro x
    simp

theorem invariantLaurentSeparation : InvariantLaurentSeparation := by
  classical
  intro L X W _ _ _ _ a t u h
  let v (w : W) : X →* Lˣ := t.comp (a w).toMonoidHom
  let u' (w : W) : X →* Lˣ := u.comp (a w).toMonoidHom
  have huv (w w' : W) : u' w ≠ v w' := by
    intro he
    apply h (w' * w⁻¹)
    apply MonoidHom.ext
    intro x
    have he' := DFunLike.congr_fun he ((a w⁻¹) x)
    change u ((a w) ((a w⁻¹) x)) = t ((a w') ((a w⁻¹) x)) at he'
    change t ((a (w' * w⁻¹)) x) = u x
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply] at he'
    exact he'.symm
  have hchar (w w' : W) : ∃ c : X, (u' w c : L) ≠ (v w' c : L) := by
    obtain ⟨c, hc⟩ := DFunLike.ne_iff.mp (huv w w')
    exact ⟨c, fun he ↦ hc (Units.ext he)⟩
  choose char hchar using hchar
  -- Use a binomial for each pair of points in the two orbits.
  let q (w w' : W) : MonoidAlgebra L X :=
    let c := char w w'
    MonoidAlgebra.single 1 (((u' w c : L) - (v w' c : L))⁻¹) *
      (MonoidAlgebra.single c 1 - MonoidAlgebra.single 1 (v w' c : L))
  have hq (w w' : W) : laurentEvaluation (v w') (q w w') = 0 := by
    simp [q]
  have hqu (w w' : W) : laurentEvaluation (u' w) (q w w') = 1 := by
    have hn := sub_ne_zero.mpr (hchar w w')
    simp [q, hn]
  let r (w : W) : MonoidAlgebra L X := ∏ w', q w w'
  let sep : MonoidAlgebra L X := 1 - ∏ w, (1 - r w)
  have hsepv (w : W) : laurentEvaluation (v w) sep = 0 := by
    have hrv (i : W) : laurentEvaluation (v w) (r i) = 0 := by
      rw [show laurentEvaluation (v w) (r i) = ∏ j, laurentEvaluation (v w) (q i j) by
        exact map_prod _ _ _]
      exact Finset.prod_eq_zero (Finset.mem_univ w) (hq i w)
    simp [sep, map_prod, hrv]
  have hsepu (w : W) : laurentEvaluation (u' w) sep = 1 := by
    have hru : laurentEvaluation (u' w) (r w) = 1 := by
      simp [r, map_prod, hqu]
    dsimp only [sep]
    rw [map_sub, map_one, map_prod]
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hru]), sub_zero]
  let shift (w : W) := MonoidAlgebra.mapDomainRingEquiv L (a w)
  refine ⟨∏ w, shift w sep, fun w ↦ ?_, ?_, ?_⟩
  · rw [map_prod]
    apply Fintype.prod_equiv (Equiv.mulLeft w)
    intro i
    change ((shift i).trans (shift w)) sep = shift (w * i) sep
    dsimp only [shift]
    rw [← MonoidAlgebra.mapDomainRingEquiv_trans, map_mul]
    rfl
  · simp only [map_prod, shift, eval_translate]
    change (∏ w, laurentEvaluation (v w) sep) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ (1 : W)) (hsepv 1)
  · simp only [map_prod, shift, eval_translate]
    change (∏ w, laurentEvaluation (u' w) sep) = 1
    simp only [hsepu, Finset.prod_const_one]

end InvariantLaurentPolynomials

section SectionPoints

open _root_.LinearAlgebraicGroups.Specs
open CategoryTheory
open Pinning (SimpleRoot)
open SteinbergPinnedDescent
open private height_fundamental_pos from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces

set_option backward.isDefEq.respectTransparency false in
theorem wordTracePolynomials : WordTracePolynomials.{u} := by
  classical
  intro k _ A P D hG hsc N U hU M hw n blocks hn hall
  let r := blocks.flatten.length
  let e : Fin r ≃ SimpleRoot P.pair := List.Nodup.getEquivOfForallMemList blocks.flatten hn hall
  let ω := M.weight ∘ e
  have hω : SteinbergFundamentalTraces.IsFundamental D e ω := by
    intro i j
    simpa [ω, simpleCorootValues] using hw (e j) (e i)
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  intro j
  let V : SteinbergFundamentalTraces.HighestWeightModule U (ω j) :=
    ⟨M.index (e j), M.representation (e j), M.simple (e j), M.highest (e j)⟩
  obtain ⟨d, p, hd, hp, ht⟩ :=
    Arithmetic.SteinbergFundamentalTraces.tracePolynomial P hG hsc D e n ω hω U hU j V
  refine ⟨d, p, hd, hp, ?_⟩
  intro R t
  have hword : SteinbergFundamentalTraces.sectionWord D e n R (fun i ↦ t (e i)) =
      word n blocks R t := by
    let f := fun i ↦ factor i (n i) R (t i)
    change ((List.finRange r).map (f ∘ e)).prod = (blocks.flatten.map f).prod
    rw [← List.map_map]
    exact congrArg (fun L ↦ (L.map f).prod) (List.map_get_finRange blocks.flatten)
  rw [← hword]
  exact ht R (fun i ↦ t (e i))

set_option backward.isDefEq.respectTransparency false in
theorem splitTraceBijection : SplitTraceBijection.{u} := by
  classical
  intro k S _ _ _ A P D hG hsc N U hU M hw n blocks hn hall
  let r := blocks.flatten.length
  obtain ⟨e, _, hp⟩ := wordTracePolynomials D hG hsc hU M hw n blocks hn hall
  let ω := M.weight ∘ e
  have hω : SteinbergFundamentalTraces.IsFundamental D e ω := by
    intro i j
    simpa [ω, simpleCorootValues] using hw (e j) (e i)
  choose d p hd hs ht using hp
  let R := CommAlgCat.of k S
  let F : (SimpleRoot P.pair → S) ≃ (Fin r → S) := Equiv.arrowCongr e.symm (Equiv.refl S)
  let q (j : Fin r) := MvPolynomial.map (algebraMap k S) (p j)
  let a (j : Fin r) := algebraMap k S (d j)
  have hbij := triangularParameters (fun j ↦ SteinbergFundamentalTraces.height D (ω j)) a q
    (fun j ↦ (height_fundamental_pos D e ω hω j).le)
    (fun j ↦ fun h ↦ hd j ((FaithfulSMul.algebraMap_injective k S) (h.trans (map_zero _).symm))) (by
      intro j m hm i hi
      apply hs j m (MvPolynomial.mem_support_iff.mpr ?_) i hi
      intro hz
      exact hm (by simp [q, MvPolynomial.coeff_map, hz]))
  have heval (t : SimpleRoot P.pair → S) :
      F (wordTraces M n blocks t) = triangularCoordinates a q (F t) := by
    funext j
    change traceValue (M.representation (e j)) R (word n blocks R t) = _
    rw [ht j R t]
    simp [triangularCoordinates, MvPolynomial.aeval_def, F, q, a, R]
    exact congrArg ((algebraMap k S (d j) * t (e j)) + ·)
      (MvPolynomial.eval_map (algebraMap k S) (fun i ↦ t (e i)) (p j)).symm
  have heq : wordTraces M n blocks = F.symm ∘ triangularCoordinates a q ∘ F := by
    funext t
    exact F.injective (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using heval t)
  rw [heq]
  exact F.symm.bijective.comp (hbij.comp F.bijective)

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Pinning (AttachedDatum PinnedGroup)
open RootGroups (AdditiveLine)
open CharacterDescent (Character Cocharacter)
open Specs.GeometricRadicals (IsSemisimple IsUnipotentRadical)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)
open BorelsAndChambers (subgroupRoots)
open FormalCharacters (formalCharacter)
open private datum_eq_of_coroots coroot_eq_of_linked_coordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.NormalizerComparison
open private dominant_base_iff dominant_orbits restrictedCharacter
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CharacterRing
open private coefficientFormula from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters
open private heightLinear positiveSystem_isBaseFor height_strict_of_dominance highestWeight_bound
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces

set_option backward.isDefEq.respectTransparency false in
theorem pinnedCoxeterWord : PinnedCoxeterWord.{u} := by
  classical
  intro k _ A P D hG hsc ω hω order hn hall
  let := D.comm
  let C := D.datum.rootDatum
  let roots := order.map Subtype.val
  let e : Fin order.length ≃ Fin roots.length := finCongr (by simp [roots])
  have hget (i : Fin order.length) : roots.get (e i) = (order.get i).val := by
    simp [roots, e]
  have hweights (i j : Fin order.length) :
      C.toLinearMap (Additive.ofMul (ω (order.get i))) (C.coroot (roots.get (e j))) =
        if e j = e i then 1 else 0 := by
    rw [hget]
    have hp := hω (order.get i) (order.get j)
    change C.toLinearMap (Additive.ofMul (ω (order.get i))) (C.coroot (order.get j).val) =
      _ at hp
    by_cases hij : j = i
    · subst j
      simpa using hp
    · have hne : order.get j ≠ order.get i := fun h ↦ hij (hn.get_inj_iff.mp h)
      have he : e j ≠ e i := fun h ↦ hij (e.injective h)
      simpa only [hne, he, ite_false] using hp
  have hn' : roots.Nodup := hn.map Subtype.val_injective
  have hs : {a | a ∈ roots} = (D.base.support : Set _) := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, hi⟩ := List.mem_map.mp ha
      exact (D.simple_iff _).mpr (hi ▸ i.property)
    · intro ha
      exact List.mem_map.mpr ⟨⟨a, (D.simple_iff _).mp ha⟩, hall _, rfl⟩
  have hind : LinearIndepOn ℤ C.root {a | a ∈ roots} := hs ▸ D.base.linearIndepOn_root
  have hcoro := (Classification.SimplyConnectedLattice.latticeCriterion
    P.pair.G hG P.pair.T P.pair.split P.pair.maximal D.datum).mp hsc
  obtain ⟨coords, hcoords⟩ := attachedFundamentalCoordinates P.pair D hcoro
  have hc := coxeterInjectivity C roots hn' hind (fun x hx ↦ by
    apply coords.injective
    funext i
    rw [hcoords, LinearEquiv.map_zero, Pi.zero_apply]
    exact hx i.val (show i.val ∈ {a | a ∈ roots} from hs.symm ▸ i.property))
  refine ⟨?_, hc, ?_⟩
  · intro i
    change Additive.ofMul (ω (order.get i)) -
        reflectionWord C roots (Additive.ofMul (ω (order.get i))) = transportedRoot C roots (e i) ∧
      transportedRoot C roots (e i) - C.root (order.get i).val ∈
        Submodule.span ℤ (C.root '' {a | a ∈ roots.take i.val})
    refine ⟨coxeterDisplacement C roots (e i) _ ?_, ?_⟩
    · intro j
      obtain ⟨l, rfl⟩ := e.surjective j
      exact hweights i l
    · rw [← hget i]
      exact coxeterTriangularity C roots (e i)
  · let := D.datum.finiteCharacters
    let := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
    let f := LinearMap.id - (reflectionWord C roots).toLinearMap
    have hf : Function.Injective (f.baseChange ℚ) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) f hc
    exact ⟨hf, LinearMap.injective_iff_surjective.mp hf⟩

set_option backward.isDefEq.respectTransparency false in
theorem pinnedCharacterGeneration : PinnedCharacterGeneration.{u} := by
  classical
  intro k _ A P D hG hsc N U hU M hw
  let := D.comm
  let : IsCommMonObj N.pair.torus.group.X := D.comm
  let := D.datum.finiteRoots
  let : Fintype (SimpleRoot P.pair) := Fintype.ofFinite _
  obtain ⟨comm, D', ⟨W⟩, order⟩ :=
    Representation.DominantOrder.dominantOrder P.pair.G P.pair.reductive
      P.pair.T P.pair.split P.pair.maximal
  have hD : D' = D.datum := by
    apply datum_eq_of_coroots
    intro i
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r, hr⟩ := D'.attached i
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s, hs⟩ := D.datum.attached i
    apply Additive.toMul.injective
    rw [← hr, ← hs]
    exact coroot_eq_of_linked_coordinates W.image W.representsNormalizer D' r s
  subst D'
  let := W.image.finite
  let : Finite D.datum.rootDatum.weylGroup :=
    Finite.of_injective W.labelEquiv W.labelEquiv.injective
  obtain ⟨_, _, _, corr, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity P.pair.G P.pair.reductive
      P.pair.T P.pair.split P.pair.maximal
  let S := subgroupRoots P.pair.T P.pair.B
  have laws := (order S (corr.1 P.pair.B P.pair.borel P.pair.containsTorus)).2
    D.base (positiveSystem_isBaseFor D)
  have hdom := dominant_base_iff N.pair D.datum D.base
    (fun a ↦ (D.simple_iff a).trans
      ⟨fun h ↦ ⟨⟨a, h⟩, rfl⟩, fun ⟨j, hj⟩ ↦ hj ▸ j.property⟩)
  obtain ⟨hex, hu⟩ := dominant_orbits N.pair W D.base hdom laws.orbitRepresentative
  refine ⟨W, hex, hu, ?_⟩
  let incl : CharacterRing.dominantWeights N.pair ↪ Character P.pair.T.group :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let height := heightLinear D
  let degree := height.toAddMonoidHom.toMultiplicative
  let χ (i : SimpleRoot P.pair) := formalCharacter P.pair.T (M.representation i)
  apply Arithmetic.SteinbergGeometricFibres.integralGeneration
    (CharacterRing.weylAction W) incl degree M.weight χ hex hu
  · intro j
    exact laws.nonnegative _ ((hdom _).mp j.property)
  · intro j
    have hspan := (Classification.SimplyConnectedLattice.latticeCriterion
      P.pair.G hG P.pair.T P.pair.split P.pair.maximal D.datum).mp hsc
    obtain ⟨coords, hcoords⟩ := attachedFundamentalCoordinates P.pair D hspan
    let idx : D.base.support ≃ SimpleRoot P.pair := (Equiv.refl _).subtypeEquiv D.simple_iff
    let m (i : SimpleRoot P.pair) := (coords (Additive.ofMul j.val) (idx.symm i)).toNat
    refine ⟨m, Additive.ofMul.injective (coords.injective ?_)⟩
    ext r
    have hn : 0 ≤ coords (Additive.ofMul j.val) r := by
      rw [hcoords]
      exact (hdom _).mp j.property r.val r.property
    have he (s : SimpleRoot P.pair) :
        coords (Additive.ofMul (M.weight s)) r = if idx r = s then 1 else 0 := by
      rw [hcoords]
      have hs := hw s (idx r)
      change D.datum.rootDatum.toLinearMap (Additive.ofMul (M.weight s))
        (D.datum.rootDatum.coroot r.val) = _ at hs
      by_cases h : idx r = s <;> simpa [h] using hs
    let wt : Character P.pair.T.group := j.val
    change coords (Additive.ofMul wt) r =
      coords (Additive.ofMul (∏ i, M.weight i ^ m i)) r
    rw [ofMul_prod]
    simp only [ofMul_pow]
    change coords.toLinearMap (Additive.ofMul wt) r =
      coords.toLinearMap (∑ i, m i • Additive.ofMul (M.weight i)) r
    rw [map_sum]
    simp only [map_nsmul, Finset.sum_apply, Pi.smul_apply]
    change coords (Additive.ofMul wt) r = ∑ i, m i • coords (Additive.ofMul (M.weight i)) r
    simp only [he, nsmul_eq_mul]
    rw [Finset.sum_eq_single (idx r)]
    · simp [m, Int.toNat_of_nonneg hn, wt]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · intro j
    exact (restrictedCharacter P.pair.split W
      (⟨M.index j, M.representation j⟩ : CharacterRing.Rep P.pair.G)).property
  · intro j
    let V : SteinbergFundamentalTraces.HighestWeightModule U (M.weight j) :=
      ⟨M.index j, M.representation j, M.simple j, M.highest j⟩
    obtain ⟨v, hv, _, hl, htop⟩ := highestWeight_bound hU V
    have coeff := (coefficientFormula P.pair.T P.pair.split (M.representation j)).2
    refine ⟨?_, ?_⟩
    · rw [show (χ j).coeff (M.weight j) = _ from coeff (M.weight j),
        FormalCharacters.multiplicity, hl, finrank_span_singleton hv]
      rfl
    · intro wt hne hn
      have hweight : RootWeightAction.weightSpace (M.representation j) P.pair.T wt ≠ ⊥ := by
        intro hz
        exact hn (by rw [coeff, FormalCharacters.multiplicity, hz, finrank_bot]; rfl)
      exact height_strict_of_dominance D hne (htop wt hne hweight)

section GeometricFibres

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open Specs.GeometricRadicals (GeometricGroup IsSplitTorus baseChangedSubgroup)
open GeometricBorelConjugacy (IsKBorel)
open SchemeDerivedGroup (IsSubgroupOf)
open BorelsAndChambers (IsPositiveSystem positiveRoots)
open AdjointRepresentation (GroupPoints)
open CharacterPairing (characterValue)
open FlagLineBundle (OppositeBorelPair)
open RootWeightAction (Representation extendVector mem_weightSpace)
open SteinbergGeometricFibres (integralEvaluation pointTrace pointHom)
open _root_.LinearAlgebraicGroups.Affine (RationalPoints IsRationalJordanDecomposition)
open private reductive_geometricGroup splitTorus_baseChange geometricallyMaximal_of_maximal_split
  exists_regular_cocharacter from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private splitPresentation charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private splitPointPresentation splitCharacterValue characterOfBasis
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters
open private exists_weightBasis matrixInBasis matrixInBasis_trace matrixInBasis_entry
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces
open private fibreTorsor splitFibrePoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private apply_conjugateFamily_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction

private theorem oppositePairOnTorus {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (hG : Specs.GeometricRadicals.IsReductive G)
    (hs : IsSplitTorus T.group) (hm : RankOneFlag.IsGeometricallyMaximal T) :
    ∃ Bp Bn : ClosedSubgroup G.val, IsKBorel Bp ∧ IsKBorel Bn ∧
      IsSubgroupOf T Bp ∧ IsSubgroupOf T Bn ∧ OpenCell.AreOpposite T Bp Bn := by
  obtain ⟨comm, _, _, corr, _, _, _⟩ := RootData.BorelPositivity.borelPositivity G hG T hs hm
  let := comm
  obtain ⟨c, hc⟩ := exists_regular_cocharacter G T hs
  have hp := (RootData.BorelsAndChambers.positiveSystemsFromCocharacters G hG T hs hm
    (positiveRoots T c)).mpr ⟨c, hc, rfl⟩
  obtain ⟨f, hf, hfS⟩ := hp
  have hn : IsPositiveSystem T (positiveRoots T c)ᶜ := by
    refine ⟨-f, fun α ↦ by simpa using hf α, ?_⟩
    rw [hfS]
    ext α
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, LinearMap.neg_apply, neg_pos]
    constructor
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) (hf α)
    · exact fun h ↦ not_lt_of_ge h.le
  obtain ⟨Bp, hBp, hpT, hpS⟩ := corr.2.1 _ (show IsPositiveSystem T _ from ⟨f, hf, hfS⟩)
  obtain ⟨Bn, hBn, hnT, hnS⟩ := corr.2.1 _ hn
  exact ⟨Bp, Bn, hBp, hBn, hpT, hnT, hnS.trans (congrArg Set.compl hpS.symm)⟩

/-- Characters of the original split torus still give point coordinates over
the extension. This uses the same monomials in the split presentation. -/
private theorem torusCoordinatesOver {k K : Type u} [Field k] [Field K] [Algebra k K]
    {T : GroupScheme k} (hT : IsSplitTorus T) :
    let R := (restrictTestAlgebra k K).obj (CommAlgCat.of K K)
    ∃ z : GroupPoints T R → (Character T →* Kˣ), Function.Injective z ∧
      ∀ t χ, (z t χ : K) = characterValue χ R t := by
  classical
  intro R
  obtain ⟨r, ⟨s⟩⟩ := splitPresentation hT
  let M := CharacterDescent.StandardLattice.{u} r
  obtain ⟨χ, _, hχ, _, _⟩ := _root_.LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) r
  let e := χ.trans (charactersOfIso s)
  choose f hf using fun t : GroupPoints T R ↦ splitPointPresentation s R t
  let z (t : GroupPoints T R) : Character T →* Kˣ :=
    (((f t).toMonoidHom.comp (MonoidAlgebra.of k M)).toHomUnits).comp e.symm.toMonoidHom
  have hz (t : GroupPoints T R) (c : Character T) : (z t c : K) = characterValue c R t := by
    change (f t) (MonoidAlgebra.of k M (e.symm c)) = _
    have h := splitCharacterValue s χ hχ (e.symm c) R (f t)
    rw [e.apply_symm_apply, hf t] at h
    exact h.symm
  refine ⟨z, ?_, hz⟩
  intro t t' ht
  have he : f t = f t' := by
    let : CommRing R := CommAlgCat.instCommRingObjForgetAlgHomCarrier (A := R)
    let : Algebra k R := CommAlgCat.instAlgebraObjForgetAlgHomCarrier (A := R)
    change (f t : MonoidAlgebra k M →ₐ[k] R) = f t'
    apply MonoidAlgebra.algHom_ext (R := k) (A := k) (B := R) (M := M)
    · intro m
      have h := congrArg (fun ψ : Character T →* Kˣ ↦ (ψ (e m) : K)) ht
      change (f t) (MonoidAlgebra.of k M (e.symm (e m))) =
        (f t') (MonoidAlgebra.of k M (e.symm (e m))) at h
      rwa [e.symm_apply_apply] at h
    · ext
  rw [← hf t, ← hf t', he]

private theorem torusTraceOver {k K I : Type u} [Field k] [Field K] [Algebra k K]
    [Fintype I] [DecidableEq I] {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (hs : IsSplitTorus T.group) [IsCommMonObj T.group.X] (ρ : Representation G.val I) :
    let R := (restrictTestAlgebra k K).obj (CommAlgCat.of K K)
    ∀ (t : GroupPoints T.group R) (z : Character T.group →* Kˣ),
      (∀ χ, (z χ : K) = characterValue χ R t) →
      Matrix.trace (ρ.app R (t ≫ T.inclusion.hom.hom)).val =
        integralEvaluation z (formalCharacter T ρ) := by
  classical
  intro R t z hz
  obtain ⟨b, wt, hb, _⟩ := exists_weightBasis ρ T hs
  rw [← matrixInBasis_trace b ρ R, characterOfBasis T hs ρ b wt hb, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change matrixInBasis b ρ R (t ≫ T.inclusion.hom.hom) j j = _
  rw [matrixInBasis_entry, (mem_weightSpace.mp (hb j)) R t]
  simp only [Pi.smul_apply, smul_eq_mul, extendVector]
  have hsum := congrArg (algebraMap k R) (b.sum_repr_mul_repr (Pi.basisFun k I) (b j) j)
  simp only [Module.Basis.repr_self, Pi.basisFun_repr, Finsupp.single_eq_same,
    map_sum, map_mul, map_one] at hsum
  calc
    _ = (∑ l, algebraMap k R (b.repr (Pi.basisFun k I l) j) * algebraMap k R (b j l)) *
          characterValue (wt j) R t := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ac_rfl)
    _ = _ := by
      rw [hsum, one_mul, ← hz, integralEvaluation, MonoidAlgebra.liftNCRingHom_single]
      simp

/-- A split-field Weyl lift acts on torus points over every test algebra. -/
private theorem weylConjugacyOnPoints {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D : AbstractPairing.Datum T}
    (W : DatumAndWeyl.Identification D) (hs : IsSplitTorus T.group) (R : TestAlgebra k)
    (w : D.rootDatum.weylGroup) (t : GroupPoints T.group R) :
    let a := W.image.conjugation (W.labelEquiv w)
    ∃ g : GroupPoints G.val R,
      g * (show GroupPoints G.val R from (t ≫ a.inv.hom.hom) ≫ T.inclusion.hom.hom) * g⁻¹ =
        (show GroupPoints G.val R from t ≫ T.inclusion.hom.hom) := by
  let a := W.image.conjugation (W.labelEquiv w)
  let T' : ClosedSubgroup W.normalizer.group := ⟨T.group, W.torusInclusion, W.torusClosed⟩
  let p := W.image.constantGroup.sectionPoint (W.labelEquiv w)
  have htor := fibreTorsor (G := closedSubgroupAlgebraicGroup W.normalizer)
    (W := W.scheme) T' W.quotient W.isQuotient p
  obtain ⟨n, hn⟩ := splitFibrePoint (G := closedSubgroupAlgebraicGroup W.normalizer)
    (W := W.scheme) T' hs W.quotient p htor
  let Y := (testSpec k).obj (op R)
  let n' : Y ⟶ W.normalizer.group.X := toUnit Y ≫ n
  have hlift : n' ≫ W.quotient.hom.hom = toUnit Y ≫ p := by
    change (toUnit Y ≫ n) ≫ W.quotient.hom.hom = _
    exact (Category.assoc (toUnit Y) n W.quotient.hom.hom).trans
      (congrArg (fun f ↦ toUnit Y ≫ f) hn)
  let g : GroupPoints G.val R := n' ≫ W.normalizer.inclusion.hom.hom
  let t' : GroupPoints T.group R := t ≫ a.inv.hom.hom
  have h := apply_conjugateFamily_eq T.inclusion g a
    (W.image.conjugates Y n' (W.labelEquiv w) hlift) (𝟙 Y) t'
  have hback : t' ≫ (a.hom ≫ T.inclusion).hom.hom = t ≫ T.inclusion.hom.hom := by
    change (t ≫ a.inv.hom.hom) ≫ a.hom.hom.hom ≫ T.inclusion.hom.hom = _
    erw [Category.assoc (t : Y ⟶ T.group.X) a.inv.hom.hom
      (a.hom.hom.hom ≫ T.inclusion.hom.hom)]
    have hh : a.inv.hom.hom ≫ a.hom.hom.hom = 𝟙 _ :=
      (Grp.forget _).congr_map a.inv_hom_id
    rw [← Category.assoc (f := a.inv.hom.hom), hh, Category.id_comp]
  refine ⟨g, ?_⟩
  exact (by simpa only [Category.id_comp, hback] using h.symm)

private theorem weylConjugacyOver {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : AbstractPairing.Datum T} (W : DatumAndWeyl.Identification D) (hs : IsSplitTorus T.group) :
    let R := (restrictTestAlgebra k K).obj (CommAlgCat.of K K)
    ∀ (z : GroupPoints T.group R → (Character T.group →* Kˣ)), Function.Injective z →
      (∀ t χ, (z t χ : K) = characterValue χ R t) →
      ∀ (w : D.rootDatum.weylGroup) (t t' : GroupPoints T.group R),
        (z t).comp (CharacterRing.weylAction W w).toMonoidHom = z t' →
        ∃ g : GroupPoints G.val R,
          g * (show GroupPoints G.val R from t ≫ T.inclusion.hom.hom) * g⁻¹ =
            (show GroupPoints G.val R from t' ≫ T.inclusion.hom.hom) := by
  intro R z hz₀ hz w t t' hw
  let a := W.image.conjugation (W.labelEquiv w)
  have hEq : t' = t ≫ a.inv.hom.hom := by
    apply hz₀
    ext χ
    rw [hz, hz]
    have hv := congrArg (fun f : Character T.group →* Kˣ ↦ (f χ : K)) hw
    change (z t (CharacterRing.weylAction W w χ) : K) = (z t' χ : K) at hv
    have hact : CharacterRing.weylAction W w χ = a.inv ≫ χ := W.image.characterAction _ _
    rw [hz, hz, hact] at hv
    simpa only [characterValue, Grp.comp_hom_hom, Category.assoc] using hv.symm
  obtain ⟨g, hg⟩ := weylConjugacyOnPoints W hs R w t
  change g * (show GroupPoints G.val R from (t ≫ a.inv.hom.hom) ≫ T.inclusion.hom.hom) * g⁻¹ =
    (show GroupPoints G.val R from t ≫ T.inclusion.hom.hom) at hg
  rw [← hEq] at hg
  refine ⟨g⁻¹, ?_⟩
  rw [← hg, inv_inv]
  group

set_option backward.isDefEq.respectTransparency false in
theorem pinnedGeometricTraceFibres : PinnedGeometricTraceFibres.{u} := by
  classical
  intro k _ A P D hG hsc N U hU M hw
  let K := AlgebraicClosure k
  let H := GeometricGroup P.pair.G
  intro x y htrace s r v w hx hy
  let := D.comm
  let : IsCommMonObj N.pair.torus.group.X := D.comm
  obtain ⟨W, hex, hu, hgen⟩ := pinnedCharacterGeneration D hG hsc hU M hw
  let := W.image.finite
  let : Finite D.datum.rootDatum.weylGroup :=
    Finite.of_injective W.labelEquiv W.labelEquiv.injective
  obtain ⟨hclosed, hmax⟩ := P.pair.maximal
  let T : ClosedSubgroup H.val := baseChangedSubgroup K P.pair.T hclosed
  have hsplit : IsSplitTorus T.group := splitTorus_baseChange P.pair.split
  have hred : Specs.GeometricRadicals.IsReductive H :=
    reductive_geometricGroup P.pair.G P.pair.reductive
  have hgeom := geometricallyMaximal_of_maximal_split H T hmax hsplit
  obtain ⟨Bp, Bn, hBp, hBn, hTp, hTn, hOpp⟩ := oppositePairOnTorus H T hred hsplit hgeom
  let Q : OppositeBorelPair H := ⟨T, Bp, Bn, hred, hsplit, hgeom, hBp, hBn, hTp, hTn, hOpp⟩
  obtain ⟨a, t₀, ht₀⟩ := Arithmetic.SteinbergGeometricFibres.semisimpleTorusRepresentatives H Q hx
  obtain ⟨b, t₁, ht₁⟩ := Arithmetic.SteinbergGeometricFibres.semisimpleTorusRepresentatives H Q hy
  change a * s * a⁻¹ = pointHom T.inclusion t₀ at ht₀
  change b * r * b⁻¹ = pointHom T.inclusion t₁ at ht₁
  let B := CommAlgCat.of K K
  let R := (restrictTestAlgebra k K).obj B
  let liftG := baseChangePointGroupEquiv K P.pair.G.val B
  let liftT := baseChangePointGroupEquiv K P.pair.T.group B
  have hlift (t : RationalPoints T.group) :
      liftG (pointHom T.inclusion t) = liftT t ≫ P.pair.T.inclusion.hom.hom :=
    baseChangePointsSchemeNaturality k K P.pair.T.inclusion.hom.hom B t
  obtain ⟨z, hz₀, hz⟩ := torusCoordinatesOver (K := K) P.pair.split
  have hchar {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation P.pair.G.val I)
      {g gₛ gᵤ : RationalPoints H.val}
      (hJ : IsRationalJordanDecomposition ⟨H.val, H.property.1⟩ g gₛ gᵤ)
      {p : RationalPoints H.val} {t : RationalPoints T.group}
      (ht : p * gₛ * p⁻¹ = pointHom T.inclusion t) :
      extendedTrace (S := K) ρ g =
        integralEvaluation (z (liftT t)) (formalCharacter P.pair.T ρ) := by
    obtain ⟨σ, hσ⟩ := Arithmetic.SteinbergGeometricFibres.representationExtension (K := K) ρ
    have he (q : RationalPoints H.val) : pointTrace σ q = extendedTrace (S := K) ρ q :=
      congrArg Matrix.trace (hσ B q)
    rw [← he g, Arithmetic.SteinbergGeometricFibres.jordanTrace H σ hJ,
      ← Arithmetic.SteinbergGeometricFibres.traceConjugation σ p gₛ, ht, he]
    change Matrix.trace (ρ.app R (liftG (pointHom T.inclusion t))).val = _
    rw [hlift]
    exact torusTraceOver P.pair.T P.pair.split ρ (liftT t) (z (liftT t)) (hz (liftT t))
  let i : CharacterRing.dominantWeights N.pair ↪ Character P.pair.T.group :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have heq (j : SimpleRoot P.pair) :
      integralEvaluation (z (liftT t₀)) (formalCharacter P.pair.T (M.representation j)) =
        integralEvaluation (z (liftT t₁)) (formalCharacter P.pair.T (M.representation j)) :=
    (hchar (M.representation j) hx ht₀).symm.trans
      ((htrace j).trans (hchar (M.representation j) hy ht₁))
  have hagree := Arithmetic.SteinbergGeometricFibres.integralEvaluationAgreement
    (CharacterRing.weylAction W) (fun j ↦ formalCharacter P.pair.T (M.representation j))
    (z (liftT t₀)) (z (liftT t₁)) hgen heq
  obtain ⟨w₀, hw₀⟩ := Arithmetic.SteinbergGeometricFibres.integralOrbitSeparation
    (show SteinbergGeometricFibres.InvariantLaurentSeparation.{u,u,u} from invariantLaurentSeparation)
    (CharacterRing.weylAction W) i (z (liftT t₀)) (z (liftT t₁)) hex hu hagree
  obtain ⟨g, hg⟩ := weylConjugacyOver W P.pair.split z hz₀ hz w₀ (liftT t₀) (liftT t₁) hw₀
  let p : RationalPoints H.val := liftG.symm g
  have hconj : p * pointHom T.inclusion t₀ * p⁻¹ = pointHom T.inclusion t₁ := by
    apply liftG.injective
    simp only [map_mul, map_inv, hlift, p, MulEquiv.apply_symm_apply]
    exact hg
  let h := b⁻¹ * p * a
  have hs : h * s * h⁻¹ = r := by
    show (b⁻¹ * p * a) * s * (b⁻¹ * p * a)⁻¹ = r
    rw [show (b⁻¹ * p * a) * s * (b⁻¹ * p * a)⁻¹ =
      b⁻¹ * (p * (a * s * a⁻¹) * p⁻¹) * b by group, ht₀, hconj, ← ht₁]
    group
  refine ⟨h, hs, ?_⟩
  intro C y₀ htor hC hy₀ hry
  exact (Arithmetic.SteinbergGeometricFibres.torusCentralizerCollapse H C y₀ htor hC hx h
    (hs.trans (hry.trans hy₀))).trans hy₀.symm

theorem geometricTraceExtension : GeometricTraceExtension.{u} := by
  intro k S I _ _ _ _ _ H ρ f g
  let K := AlgebraicClosure k
  let B := CommAlgCat.of K K
  let R := (restrictTestAlgebra k K).obj B
  let e := baseChangePointGroupEquiv K H B
  let a := geometricTestMap f
  let y := mapPoints a g
  let x := e.symm y
  have hx : IsGeometricImage f g x := e.apply_symm_apply y
  refine ⟨x, ⟨hx, ?_⟩, fun x' hx' ↦ e.injective (hx'.1.trans hx.symm)⟩
  change Matrix.trace (ρ.app R (e x)).val = _
  rw [show e x = y from hx]
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality a)) g
  have hm := congrArg (fun v : Matrix.GeneralLinearGroup I R ↦ v.val) h.symm
  change f.toRingHom.mapMatrix (ρ.app (CommAlgCat.of k S) g).val = (ρ.app R y).val at hm
  rw [← hm]
  exact (AddMonoidHom.map_trace f.toRingHom (ρ.app (CommAlgCat.of k S) g).val).symm

private theorem splitFieldTraceFibres {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {N : OppositeBorel P.pair}
    {U : ClosedSubgroup P.pair.B.group} {M : HighestWeightModules N U}
    (hF : HasGeometricTraceFibres M) : HasSplitFieldTraceFibres (S := S) M := by
  intro f g y ht
  let K := AlgebraicClosure k
  let B := CommAlgCat.of K K
  let e := baseChangePointGroupEquiv K P.pair.G.val B
  let geo (z : GroupPoints P.pair.G.val (CommAlgCat.of k S)) :=
    e.symm (mapPoints (geometricTestMap f) z)
  have hgeo (z : GroupPoints P.pair.G.val (CommAlgCat.of k S)) :
      IsGeometricImage f z (geo z) := e.apply_symm_apply _
  have htr (i : SimpleRoot P.pair) (z : GroupPoints P.pair.G.val (CommAlgCat.of k S)) :
      extendedTrace (S := K) (M.representation i) (geo z) =
        f (traceValue (M.representation i) _ z) := by
    obtain ⟨z', hz', _⟩ := geometricTraceExtension (M.representation i) f z
    have he : z' = geo z := e.injective (hz'.1.trans (hgeo z).symm)
    rw [← he]
    exact hz'.2
  refine ⟨geo g, geo y, hgeo g, hgeo y, hF _ _ ?_⟩
  intro i
  rw [htr, htr, ht i]

end GeometricFibres

open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints)
open RelativeFormComparison (fieldTest)
open NormalizerComparison (SimpleRepresentative)
open AdjointRepresentation (GroupPoints)
open private bourbakiPermutation_preserves simpleCorootCoordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SteinbergPinnedDescent
open private simple_representatives_exist
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.NormalizerComparison

private theorem e6BlockOrbit (b : List (Fin 6)) (hb : b ∈ e6Blocks) :
    ∀ i ∈ b, ∀ j ∈ b, j = i ∨ j = e6Involution i := by
  simp only [e6Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide

private theorem orbitBlockOrder {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) {Γ : Type u} [Group Γ]
    (outer : Γ →* Aut D.toBased) (htype : ExceptionalDiagram D outer) :
    ∃ blocks : List (List (SimpleRoot P.pair)),
      blocks.flatten.Nodup ∧ (∀ i, i ∈ blocks.flatten) ∧
      (∀ σ b, b ∈ blocks → (b.map (diagramPermutation D (outer σ))).Perm b) ∧
      (∀ b ∈ blocks, ∀ i ∈ b, ∀ j ∈ b, ∃ σ, diagramPermutation D (outer σ) i = j) ∧
      ∀ b ∈ blocks, b.Pairwise (fun i j ↦ i ≠ j ∧ Orthogonal D i j) := by
  classical
  let := D.comm
  by_cases h : ∀ σ, diagramPermutation D (outer σ) = 1
  · let := D.datum.finiteRoots
    let : Fintype (SimpleRoot P.pair) := Fintype.ofFinite _
    let roots := (Finset.univ : Finset (SimpleRoot P.pair)).toList
    have hflat : (roots.map (fun i ↦ [i])).flatten = roots := by
      induction roots with
      | nil => rfl
      | cons i roots ih => simp [ih]
    refine ⟨roots.map (fun i ↦ [i]), hflat.symm ▸ Finset.nodup_toList _, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [hflat]
      exact Finset.mem_toList.mpr (Finset.mem_univ _)
    · intro σ b _
      simp [h σ]
    · intro b hb i hi j hj
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      rw [List.mem_singleton] at hi hj
      exact ⟨1, by rw [h 1, hi, hj]; rfl⟩
    · intro b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      exact List.pairwise_singleton _ a
  · obtain ⟨e, he⟩ := htype.resolve_left h
    have horder := Arithmetic.SteinbergPinnedDescent.e6BlockOrder
    have horbit := Arithmetic.SteinbergPinnedDescent.e6DiagramOrbits D outer e he (not_forall.mp h)
    refine ⟨e6Blocks.map (fun b ↦ b.map e), ?_, ?_, ?_, ?_, ?_⟩
    · rw [← List.map_flatten]
      exact horder.1.map e.injective
    · intro i
      rw [← List.map_flatten]
      exact List.mem_map.mpr ⟨e.symm i, horder.2.1 _, e.apply_symm_apply _⟩
    · intro σ b hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      let p := diagramPermutation D (outer σ)
      let q : Equiv.Perm (Fin 6) := (e.trans p).trans e.symm
      have hq (i : Fin 6) : e (q i) = p (e i) := e.apply_symm_apply _
      simpa only [List.map_map, Function.comp_def, hq] using
        (horder.2.2.1 q (bourbakiPermutation_preserves D e he (outer σ)) b' hb').map e
    · intro b hb i hi j hj
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hj
      exact (horbit i' j').mpr (e6BlockOrbit b' hb' i' hi' j' hj')
    · intro b hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      rw [List.pairwise_map]
      exact (horder.2.2.2 b' hb').imp (fun {i j} hij ↦
        ⟨e.injective.ne hij.1, (he i j).trans hij.2.1, (he j i).trans hij.2.2⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem sectionFromDescent
    {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (E : SplitSequence P D l Q)
    (outer : Gal(S/k) →* Aut D.toBased) {G : AffineAlgebraicGroup k}
    {e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S)}
    (descend : ∀ y : GroupPoints P.pair.G.val (CommAlgCat.of k S),
      (∀ σ, pinnedAction S (l (outer σ)).asIso.hom σ y = y) →
      ∃ x : GroupPoints G.val (CommAlgCat.of k k),
        mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x = comparisonOnPoints e y)
    {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group}
    {M : HighestWeightModules N U}
    (hG : IsSemisimple P.pair.G) (hsc : GeometricallySimplyConnected P.pair.G)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U)
    (hw : IsFundamental D M.weight) (htype : ExceptionalDiagram D outer) :
    SectionOnPoints D l outer e M := by
  obtain ⟨n⟩ := simple_representatives_exist P D
  obtain ⟨blocks, hn, ha, hb, horbit, ho⟩ := orbitBlockOrder D outer htype
  have hpolys := wordTracePolynomials D hG hsc hU M hw n blocks hn ha
  have hbijection := splitTraceBijection (S := S) D hG hsc hU M hw n blocks hn ha
  have hfibres := pinnedGeometricTraceFibres D hG hsc hU M hw
  refine ⟨n, blocks, hn, ha, hb, horbit, ho, ?_, pinnedCoxeterWord D hG hsc M.weight hw _ hn ha,
    hfibres, splitFieldTraceFibres hfibres, hpolys, hbijection, ?_⟩
  · intro b hb R t
    rw [List.pairwise_map]
    exact (ho b hb).imp (fun h ↦ Arithmetic.SteinbergPinnedDescent.orthogonalFactors
      D _ _ h.1 h.2 _ _ R _ _)
  · let R := CommAlgCat.of k S
    let tr := fun g i ↦ traceValue (M.representation i) R g
    let wrd := word n blocks R
    let a := fun σ : Gal(S/k) ↦ pinnedAction S (l (outer σ)).asIso.hom σ
    let π := fun σ : Gal(S/k) ↦ diagramPermutation D (outer σ)
    let scalars := fun (σ : Gal(S/k)) (c : S) ↦ σ c
    let changeParameters := fun σ ↦ permuteParameters (π σ) (scalars σ)
    have hlift (σ : Gal(S/k)) :=
      Arithmetic.SteinbergPinnedDescent.pinnedSequenceLifts E (outer σ)
    have he (σ : Gal(S/k)) (t : SimpleRoot P.pair → S) :
        a σ (wrd t) = wrd (changeParameters σ t) :=
      Arithmetic.SteinbergPinnedDescent.wordEquivariance D (outer σ) _ (hlift σ)
        n blocks (hb σ) ho σ t
    have htr (σ : Gal(S/k)) (g : GroupPoints P.pair.G.val R) :
        tr (a σ g) = changeParameters σ (tr g) :=
      Arithmetic.SteinbergPinnedDescent.tracePermutation D (outer σ) _ N U hU M
        (Arithmetic.SteinbergPinnedDescent.fundamentalWeightPermutation D (outer σ) _ (hlift σ)
          (simpleCorootCoordinates D hG hsc).injective M.weight hw) σ g
    have hc (g z : GroupPoints P.pair.G.val R) : tr (z * g * z⁻¹) = tr g :=
      funext (fun i ↦ Arithmetic.SteinbergPinnedDescent.traceConjugacy (M.representation i) R g z)
    refine ⟨he, htr, ?_⟩
    intro v hv
    obtain ⟨t, ht⟩ := hbijection.surjective v
    obtain ⟨t', ht', hfix, hword⟩ := Arithmetic.SteinbergPinnedDescent.fixedMatching
      π scalars a wrd tr he htr hc v hv ⟨t, ht, fun p hp ↦ hbijection.injective (hp.trans ht.symm)⟩
    obtain ⟨x, hx⟩ := descend (wrd t') hword
    exact ⟨t', x, ht', hfix, hx⟩

theorem referenceSection : ReferenceSection.{u} := by
  intro k S _ _ _ _ A P D l Q E ω V hG hsc htype
  obtain ⟨N, U, hU, M, hw⟩ := Arithmetic.SteinbergPinnedDescent.fundamentalModulesExist D hG hsc
  have hm (σ τ : Gal(S/k)) : ω (σ * τ) = ω σ * ω τ := by
    simpa using ω.property.2 σ τ
  let outer : Gal(S/k) →* Aut D.toBased :=
    { toFun := fun σ ↦ ω σ
      map_one' := by
        have h : ω 1 = ω 1 * ω 1 := by rw [← hm, mul_one]
        exact mul_left_cancel (h.symm.trans (mul_one _).symm)
      map_mul' := hm }
  exact ⟨N, U, hU, M, hw, sectionFromDescent E outer (e := V.trivialization)
    (Arithmetic.SteinbergPinnedDescent.referenceDescent V) hG hsc hU hw htype⟩

theorem finiteReferenceSection : FiniteReferenceSection.{u} := by
  intro k S _ _ _ _ _ A P D l Q G B T V E hG hsc htype
  obtain ⟨N, U, hU, M, hw⟩ := Arithmetic.SteinbergPinnedDescent.fundamentalModulesExist D hG hsc
  obtain ⟨t, e, ht, hi, hd⟩ := Arithmetic.SteinbergPinnedDescent.finiteReferenceDescent V
  exact ⟨N, U, hU, M, hw, t, e, ht, hi, sectionFromDescent E V.outer hd hG hsc hU hw htype⟩

end SectionPoints

end LinearAlgebraicGroups.Arithmetic.ExceptionalSteinbergSection
