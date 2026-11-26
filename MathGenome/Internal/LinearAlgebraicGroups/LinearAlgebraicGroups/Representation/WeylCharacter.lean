import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.WeylCharacter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagEulerAndVanishing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylModules
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.Representation.WeylCharacter

open _root_.LinearAlgebraicGroups.Specs
open Specs.WeylCharacter
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterDescent (Character)
open Specs.DatumAndWeyl (Identification)
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection covariantFunctions)
open Specs.FormalCharacters (formalCharacter)
open Specs.PrimitiveLine (IsSimple)
open Specs.RootWeightAction (Representation weightSpace)
open Specs.SimpleClassification (SocleModel)
open Specs.WeylDenominator (GroupRing alternant monomial rho weylSign)
open Specs.WeylModules (IsDual Isomorphic oppositeWeight)
open Specs.FlagEulerCharacteristic (halfWeightDomain includeCharacters)

noncomputable section

open private coefficientFormula from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters
open private dual_weight_finrank equivariant_weight socleInclusion socleInclusion_equivariant
  socleInclusion_injective socleInclusion_range induced_simple_of_charZero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylModules
open private includeCharacters_eChar includeCharacters_injective weylLabelEquiv weylLabelEquiv_label
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagEulerCharacteristic
open private longest_flips_sign rootOfNeg base_eq_of_same_positives from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
open private laws from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.DominantOrder
open private formula sign_sq weight_mul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylDenominator
open private weylAction_of_normalizer from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {k I J : Type u} [Field k] {G : AffineAlgebraicGroup k}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private def characterInversion (T : GroupScheme k) :=
  MonoidAlgebra.mapDomainRingEquiv ℤ (MulEquiv.inv (Character T))

private theorem characterInversion_coeff (T : GroupScheme k)
    (c : MonoidAlgebra ℤ (Character T)) (χ : Character T) :
    (characterInversion T c).coeff χ = c.coeff χ⁻¹ := by
  rw [characterInversion, MonoidAlgebra.coeff_mapDomainRingEquiv]
  rfl

private theorem dual_character (P : OppositeBorelPair G) {r s : Representation G.val I}
    (h : IsDual r s) :
    formalCharacter P.torus s = characterInversion P.torus.group (formalCharacter P.torus r) := by
  ext χ
  rw [characterInversion_coeff, (coefficientFormula P.torus P.split s).2,
    (coefficientFormula P.torus P.split r).2]
  have hm := dual_weight_finrank P h χ⁻¹
  rw [inv_inv] at hm
  exact congrArg (fun n : ℕ => (n : ℤ)) hm

private theorem isomorphic_character (P : OppositeBorelPair G) {r : Representation G.val I}
    {s : Representation G.val J} (h : Isomorphic r s) :
    formalCharacter P.torus r = formalCharacter P.torus s := by
  obtain ⟨⟨e, he⟩⟩ := h
  ext χ
  rw [(coefficientFormula P.torus P.split r).2, (coefficientFormula P.torus P.split s).2]
  unfold FormalCharacters.multiplicity
  congr 1
  apply LinearEquiv.finrank_eq (e.ofSubmodules _ _ ?_)
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  have he' : PrimitiveLine.IsEquivariant s r e.symm.toLinearMap := by
    intro R g ℓ v
    apply e.injective
    change e (e.symm (PrimitiveLine.orbitCoefficient s R g ℓ v)) =
      e (PrimitiveLine.orbitCoefficient r R g ℓ (e.symm v))
    rw [e.apply_symm_apply, show e (PrimitiveLine.orbitCoefficient r R g ℓ (e.symm v)) =
      PrimitiveLine.orbitCoefficient s R g ℓ (e (e.symm v)) from he R g ℓ _,
      e.apply_symm_apply]
  exact ⟨equivariant_weight he, fun hw => by
    simpa only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using equivariant_weight he' hw⟩

private theorem simple_socle_character {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) (h : IsSimple S.inducedAction) :
    formalCharacter P.torus S.socleAction = formalCharacter P.torus S.inducedAction := by
  have hs : S.socle = ⊤ :=
    (h.2 _ S.socle_simple.1).resolve_left S.socle_simple.2.1
  let f := socleInclusion S
  have hinj : Function.Injective f := socleInclusion_injective S
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp
    ((socleInclusion_range S).trans hs)
  exact isomorphic_character P ⟨⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩,
    socleInclusion_equivariant S⟩⟩

section Alternants

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {Idx : Type*} (p : RootPairing Idx ℤ X Y)
  [Finite p.weylGroup] (b : p.Base)

private def halfWeightInversion (X : Type*) [AddCommGroup X] :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (AddEquiv.neg X)

private theorem negate_alternant (x : X) :
    halfWeightInversion X (alternant p b x) = alternant p b (-x) := by
  classical
  unfold alternant halfWeightInversion
  simp [monomial]

private theorem alternant_at_translate
    (hm : ∀ v w, weylSign p b (v * w) = weylSign p b v * weylSign p b w)
    (w : p.weylGroup) (x : X) :
    alternant p b (w.val.weightEquiv x) = weylSign p b w • alternant p b x := by
  classical
  letI := Fintype.ofFinite p.weylGroup
  unfold alternant
  simp only [Finset.smul_sum]
  calc
    _ = ∑ v : p.weylGroup, weylSign p b w •
        (weylSign p b (v * w) • monomial ((v * w).val.weightEquiv x)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hm, smul_smul, mul_left_comm, sign_sq, mul_one, weight_mul]
    _ = _ := Equiv.sum_comp (Equiv.mulRight w)
      (fun v => weylSign p b w • (weylSign p b v • monomial (v.val.weightEquiv x)))

private theorem halfWeightInversion_include (T : GroupScheme k)
    (c : MonoidAlgebra ℤ (Character T)) :
    halfWeightInversion (Additive (Character T)) (includeCharacters T c) =
      includeCharacters T (characterInversion T c) := by
  have h :
      (halfWeightInversion (Additive (Character T))).toRingHom.comp (includeCharacters T) =
      (includeCharacters T).comp (characterInversion T).toRingHom := by
    apply MonoidAlgebra.ringHom_ext
    · intro n
      change (halfWeightInversion (Additive (Character T))) ((includeCharacters T) (n : MonoidAlgebra ℤ (Character T))) =
        (includeCharacters T) (characterInversion T (n : MonoidAlgebra ℤ (Character T)))
      simp only [map_intCast]
    · intro χ
      change halfWeightInversion (Additive (Character T))
          (includeCharacters T (MonoidAlgebra.single χ 1)) =
        includeCharacters T (characterInversion T (MonoidAlgebra.single χ 1))
      rw [characterInversion, MonoidAlgebra.mapDomainRingEquiv_single]
      change _ = includeCharacters T (MonoidAlgebra.single χ⁻¹ 1)
      rw [show MonoidAlgebra.single χ (1 : ℤ) = EquivariantAffineModules.eChar χ from rfl,
        show MonoidAlgebra.single χ⁻¹ (1 : ℤ) = EquivariantAffineModules.eChar (χ⁻¹) from rfl,
        includeCharacters_eChar, includeCharacters_eChar]
      change AddMonoidAlgebra.mapDomainRingEquiv ℤ (AddEquiv.neg _) (AddMonoidAlgebra.single _ _) = _
      rw [AddMonoidAlgebra.mapDomainRingEquiv_single]
      congr 1
      exact (smul_neg _ _).symm
  exact DFunLike.congr_fun h c

end Alternants

section RootDatum

open Specs.SimpleRoots (evaluate wordLength)
open Specs.InducedNonvanishing (Dominant)

variable (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
  {D E : Datum P.torus} (e : Identification D) (f : Identification E)

private theorem label_transport_perm (w : D.rootDatum.weylGroup) (α : Root P.torus) :
    E.rootDatum.weylGroupToPerm (weylLabelEquiv e f P.split w) α =
      D.rootDatum.weylGroupToPerm w α := by
  apply Subtype.ext
  apply Additive.ofMul.injective
  rw [← E.root_eq, ← D.root_eq, ← E.rootDatum.weylGroup_apply_root,
    ← D.rootDatum.weylGroup_apply_root, E.root_eq, D.root_eq]
  change (weylLabelEquiv e f P.split w).val.weightEquiv (Additive.ofMul α.val) =
    w.val.weightEquiv (Additive.ofMul α.val)
  rw [f.characterAction, e.characterAction, weylLabelEquiv_label]

/-- The common action on the actual torus lattice identifies inversion sets
for any two presentations of the marked root datum. -/
private theorem length_transport [Finite (Root P.torus)] (b : D.rootDatum.Base)
    (c : E.rootDatum.Base)
    (hb : DominantOrder.IsBaseFor D.rootDatum (subgroupRoots P.torus P.positive) b)
    (hc : DominantOrder.IsBaseFor E.rootDatum (subgroupRoots P.torus P.positive) c)
    (w : D.rootDatum.weylGroup) :
    wordLength E.rootDatum c (weylLabelEquiv e f P.split w) = wordLength D.rootDatum b w := by
  let := D.freeCharacters
  let := D.finiteCharacters
  let := D.reduced
  let := E.reduced
  obtain ⟨z, _, hz, _, hpos⟩ := (RootData.BorelsAndChambers.borelsThroughT G P.reductive
    P.torus P.split P.maximal).1 P.positive P.positiveBorel P.inPositive
  let F := evaluate D z
  have heval (α : Root P.torus) : F (Additive.ofMul α.val) =
      CharacterPairing.pairing P.torus.group α.val z := D.pairing_eq _ _
  have hregD α : F (D.rootDatum.root α) ≠ 0 := by rw [D.root_eq, heval]; exact hz α
  have hregE α : F (E.rootDatum.root α) ≠ 0 := by rw [E.root_eq, heval]; exact hz α
  obtain ⟨b', hb'⟩ := RootData.SimpleRoots.baseFor D.rootDatum F hregD
  obtain ⟨c', hc'⟩ := RootData.SimpleRoots.baseFor E.rootDatum F hregE
  have hmem (α : Root P.torus) :
      α ∈ subgroupRoots P.torus P.positive ↔ 0 < F (Additive.ofMul α.val) := by
    rw [hpos, heval]
    rfl
  have hbEq : b = b' := base_eq_of_same_positives b b' fun α => by
    rw [hb, hb'.positive_iff]
    change _ ↔ 0 < F (D.rootDatum.root α)
    rw [D.root_eq]
    exact hmem α
  have hcEq : c = c' := base_eq_of_same_positives c c' fun α => by
    rw [hc, hc'.positive_iff]
    change _ ↔ 0 < F (E.rootDatum.root α)
    rw [E.root_eq]
    exact hmem α
  let L := weylLabelEquiv e f P.split
  have hi : (L w)⁻¹ = L (w⁻¹) := by
    apply f.labelEquiv.injective
    apply Subtype.ext
    rw [map_inv, Subgroup.coe_inv, show (f.labelEquiv (L w)).val = _ from
      weylLabelEquiv_label e f P.split w, show (f.labelEquiv (L (w⁻¹))).val = _ from
      weylLabelEquiv_label e f P.split w⁻¹, map_inv, Subgroup.coe_inv]
  rw [hbEq, hcEq, hb'.length_eq, hc'.length_eq]
  congr 1
  ext α
  change (0 < F (E.rootDatum.root α) ∧
    F (E.rootDatum.root (E.rootDatum.weylGroupToPerm (L w)⁻¹ α)) < 0) ↔
      (0 < F (D.rootDatum.root α) ∧ F (D.rootDatum.root (D.rootDatum.weylGroupToPerm w⁻¹ α)) < 0)
  rw [hi, label_transport_perm P e f, E.root_eq, D.root_eq, E.root_eq, D.root_eq]

private theorem longest_rho [Finite (Root P.torus)] (b : D.rootDatum.Base)
    (hb : DominantOrder.IsBaseFor D.rootDatum (subgroupRoots P.torus P.positive) b)
    (w : D.rootDatum.weylGroup)
    (hw : ∀ v, wordLength D.rootDatum b v ≤ wordLength D.rootDatum b w) :
    w.val.weightEquiv (rho D.rootDatum (subgroupRoots P.torus P.positive)) =
      -rho D.rootDatum (subgroupRoots P.torus P.positive) := by
  classical
  let := D.freeCharacters
  let := D.finiteCharacters
  let := D.reduced
  obtain ⟨c, _, hr, _, hc⟩ := (RootData.BorelsAndChambers.borelsThroughT
    G P.reductive P.torus P.split P.maximal).1 P.positive P.positiveBorel P.inPositive
  let F := evaluate D c
  have hF (α : Root P.torus) : F (D.rootDatum.root α) =
      CharacterPairing.pairing P.torus.group α.val c := by
    change D.rootDatum.toLinearMap (D.rootDatum.root α) (Additive.ofMul c) = _
    rw [D.root_eq, D.pairing_eq]
  have hreg α : F (D.rootDatum.root α) ≠ 0 := hF α ▸ hr α
  have hp α : b.IsPos α ↔ α ∈ Specs.SimpleRoots.positive D.rootDatum F := by
    rw [hb, hc]
    change _ ↔ 0 < F (D.rootDatum.root α)
    rw [hF]
    rfl
  letI := D.rootDatum.indexNeg
  let g : Root P.torus ≃ Root P.torus := (D.rootDatum.weylGroupToPerm w).trans (Equiv.neg _)
  have hmem α : g α ∈ subgroupRoots P.torus P.positive ↔ α ∈ subgroupRoots P.torus P.positive := by
    change -(D.rootDatum.weylGroupToPerm w α) ∈ _ ↔ _
    rw [← hb, ← hb, RootPairing.Base.IsPos.neg_iff_not,
      longest_flips_sign b F hreg hp w hw α, not_not]
  letI : Fintype (Root P.torus) := Fintype.ofFinite _
  let A := WeylDenominator.positiveRoots (subgroupRoots P.torus P.positive)
  change w.val.weightEquiv.toLinearMap (∑ α ∈ A, D.rootDatum.root α) =
    -(∑ α ∈ A, D.rootDatum.root α)
  rw [map_sum, ← Finset.sum_neg_distrib]
  simp only [LinearEquiv.coe_coe]
  dsimp only [A]
  simp only [show ∀ α, w.val.weightEquiv (D.rootDatum.root α) =
    D.rootDatum.root (D.rootDatum.weylGroupToPerm w α) from D.rootDatum.weylGroup_apply_root w]
  apply Finset.sum_bij (fun α _ => g α)
  · intro α hα
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem α).mpr (Finset.mem_filter.mp hα).2⟩
  · intro α _ β _ he
    exact g.injective he
  · intro β hβ
    refine ⟨g.symm β, ?_, g.apply_symm_apply β⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem (g.symm β)).mp
      (by simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hβ).2)⟩
  · intro α _
    change D.rootDatum.root (D.rootDatum.weylGroupToPerm w α) =
      -D.rootDatum.root (-(D.rootDatum.weylGroupToPerm w α))
    have hneg := rootOfNeg (P := D.rootDatum) (D.rootDatum.weylGroupToPerm w α)
    rw [hneg, neg_neg]

private theorem denominator_laws [Finite (Root P.torus)] [Finite D.rootDatum.weylGroup]
    (e : Identification D)
    (b : D.rootDatum.Base)
    (hb : DominantOrder.IsBaseFor D.rootDatum (subgroupRoots P.torus P.positive) b) :
    Specs.WeylDenominator.Laws D.rootDatum (subgroupRoots P.torus P.positive) b := by
  let := D.freeCharacters
  let := D.freeCocharacters
  let := D.reduced
  let := D.reducedCoroots
  have act := weylAction_of_normalizer RootData.BorelNormalizer.weylSimplyTransitiveOnPositiveSystems
    P.reductive P.split P.maximal e
  have hS := (RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal)
  obtain ⟨_, _, _, hBorel, _, _, _⟩ := hS
  have hpos := hBorel.1 P.positive P.positiveBorel P.inPositive
  obtain ⟨_, _, huniq⟩ := act.2.2 _ _ hpos hpos
  have hfree (w : D.rootDatum.weylGroup)
      (hw : D.rootDatum.weylGroupToPerm w '' subgroupRoots P.torus P.positive =
        subgroupRoots P.torus P.positive) : w = 1 :=
    (huniq w hw).trans (huniq 1 (by simp)).symm
  exact formula D.rootDatum hb (laws D.rootDatum _ b hb hfree)

/-- Inverting exponents in the character at the opposite weight yields the
formula at the original weight. The Weyl sign occurs in both alternants. -/
private theorem opposite_formula [Finite (Root P.torus)] [Finite D.rootDatum.weylGroup]
    (b : D.rootDatum.Base)
    (hb : DominantOrder.IsBaseFor D.rootDatum (subgroupRoots P.torus P.positive) b)
    (w : D.rootDatum.weylGroup)
    (hw : ∀ v, wordLength D.rootDatum b v ≤ wordLength D.rootDatum b w)
    (χ : Character P.torus.group) (c : MonoidAlgebra ℤ (Character P.torus.group))
    (hc : SatisfiesFormula D b (oppositeWeight e w χ) c) :
    SatisfiesFormula D b χ (characterInversion P.torus.group c) := by
  let S := subgroupRoots P.torus P.positive
  let p := D.rootDatum
  let r := rho p S
  let x := 2 • Additive.ofMul χ + r
  let a := alternant p b x
  let d := alternant p b r
  let T := P.torus.group
  let := D.freeCharacters
  let := halfWeightDomain T
  let A := GroupRing (Additive (Character T))
  let j := algebraMap A (FractionRing A)
  change j d ≠ 0 ∧ j (includeCharacters T c) =
    j (alternant p b (2 • Additive.ofMul (oppositeWeight e w χ) + r)) / j d at hc
  change j d ≠ 0 ∧ j (includeCharacters T (characterInversion T c)) = j a / j d
  refine ⟨hc.1, (eq_div_iff hc.1).mpr ?_⟩
  have he := (eq_div_iff hc.1).mp hc.2
  rw [← map_mul] at he
  have he' := IsFractionRing.injective A (FractionRing A) he
  have hflip : w.val.weightEquiv r = -r := longest_rho P b hb w hw
  have hx : -(2 • Additive.ofMul (oppositeWeight e w χ) + r) = w.val.weightEquiv x := by
    dsimp only [x]
    let m := w.val.weightEquiv.toAddEquiv.toAddMonoidHom
    change _ = m (2 • Additive.ofMul χ + r)
    rw [map_add, map_nsmul]
    change _ = 2 • w.val.weightEquiv (Additive.ofMul χ) + w.val.weightEquiv r
    rw [hflip, e.characterAction]
    change -((2 : ℕ) • (-Additive.ofMul ((e.labelEquiv w).val χ)) + r) = _
    rw [smul_neg, neg_add_rev, neg_neg, add_comm]
  have hi := congrArg (halfWeightInversion (Additive (Character T))) he'
  have hmul := (denominator_laws P e b hb).sign_mul
  rw [map_mul, halfWeightInversion_include, negate_alternant, negate_alternant, hx,
    ← hflip, alternant_at_translate p b hmul w x, alternant_at_translate p b hmul w r] at hi
  have heq := congrArg (fun z : A => weylSign p b w • z) hi
  rw [mul_smul_comm, smul_smul, smul_smul, sign_sq, one_smul, one_smul] at heq
  rw [← map_mul, heq]

end RootDatum

open Specs.FlagCohomology (FlagKernelPair CohomologyIndex CohomologyBasis flagCohomology
  IsFlagCohomologyAction equivariantEulerCharacteristic)
open Specs.QuotientEmbedding (Presentation)
open Specs.InducedNonvanishing (Dominant)

private theorem zero_character (P : OppositeBorelPair G) [IsEmpty I]
    (r : Representation G.val I) : formalCharacter P.torus r = 0 := by
  ext ψ
  rw [(coefficientFormula P.torus P.split r).2, MonoidAlgebra.coeff_zero]
  have h : weightSpace r P.torus ψ = ⊥ := Subsingleton.elim _ _
  simp [FormalCharacters.multiplicity, h]

private theorem euler_eq_degree_zero {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagKernelPair Q)
    (r : ∀ n, Representation G.val (CohomologyIndex (p := p) (χ := χ) h n))
    (N : ℕ) (hN : ∀ i ≥ N, IsZero (flagCohomology Q p χ h i))
    (hVan : ∀ i, 0 < i → IsZero (flagCohomology Q p χ h i)) :
    equivariantEulerCharacteristic h r N = formalCharacter P.torus (r 0) := by
  have hz (n : ℕ) (hn : IsZero (flagCohomology Q p χ h n)) :
      formalCharacter P.torus (r n) = 0 := by
    have := ModuleCat.isZero_iff_subsingleton.mp hn
    have hn' : Module.finrank k (flagCohomology Q p χ h n) = 0 := Module.finrank_zero_of_subsingleton
    letI : IsEmpty (CohomologyIndex (p := p) (χ := χ) h n) :=
      ⟨fun i => Nat.not_lt_zero _ (show i.down.val < 0 by simpa only [hn'] using i.down.isLt)⟩
    exact zero_character P (r n)
  cases N with
  | zero =>
      simpa only [equivariantEulerCharacteristic, Finset.range_zero, Finset.sum_empty] using
        (hz 0 (hN 0 le_rfl)).symm
  | succ N =>
      rw [equivariantEulerCharacteristic, Finset.sum_eq_single 0]
      · simp
      · intro i _ hi
        rw [hz i (hVan i (Nat.pos_of_ne_zero hi)), smul_zero]
      · simp

section DegreeZero

open WithConv
open scoped TensorProduct
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AssociatedFlagLineSheaves (groundScalars evalOn lineCoordinate)
open Specs.CharacterPairing (characterValue)
open Specs.EquivariantAffineModules (Linearization HasSectionWeight actOn pullCongr
  pullSection transport characterFunction)
open Specs.FlagCohomology (flagLineData flagLineSheaf cohomologyZero sectionsFunctor
  structureModule pullbackRegular)
open Specs.FlagCovarianceLinearization (flagLineCoordinate PreservesFlagLineCoordinate torusAction)
open Specs.FlagLineBundle (AssociatedBundle linePoint)
open Specs.RootWeightAction (act extendVector mem_weightSpace)
open LinearAlgebraicGroups.RationalRepresentations (evaluate tensorCoordinate)
open LinearAlgebraicGroups.AssociatedFlagLineSheaves (realizeSections globalCovariantSections)
open LinearAlgebraicGroups.Representation.EquivariantAffineModules
  (transport_sectionWeight pullSection_congr)
open LinearAlgebraicGroups.Representation.FlagEquivariantEulerMap
  (cohomologyPullbacks_nonempty flagLineSheaf_finitePresentation)
open private internalWeights characterOfBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters
open private exists_associatedFlagSheafIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AmpleFlagTwistVanishing
open private flagLineCohomology_weight characterValue_eval
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagEquivariantEulerMap
open private transpose_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCovarianceLinearization
open private pullbackRegular_app exists_associatedBundle from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private pointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle
open private eval_coordinateFunction coordinateFunction leftEval leftCoactionHom_linear
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle
open private coordinate_unique evalOn_top lineCoordinate_linePoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
open private characterValue_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open private tensorCoordinate_tmul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

variable {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
  {χ : Character P.torus.group} {Q : Presentation P.negative}
  {a : ModObj G.val.X Q.scheme} {p : BorelProjection P} (h : FlagKernelPair Q)

private theorem flagLineCoordinate_section {Z : SchemeOver k} (g : Z ⟶ G.val.X)
    (s : Γ(flagLineSheaf Q p χ h, ⊤)) :
    (flagLineCoordinate Q p χ h g).app ⊤
      (pullSection (g ≫ Q.projection).left (flagLineSheaf Q p χ h) s) =
    g.left.appTop ((flagLineData Q p χ h).inclusion.app ⊤ s) := by
  let D := flagLineData Q p χ h
  let A := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ Q.projection).left
  let α := A.homEquiv D.sheaf (structureModule Z.left) (flagLineCoordinate Q p χ h g)
  have hα : α = D.inclusion ≫
      (Scheme.Modules.pushforward Q.projection.left).map (pullbackRegular g.left) ≫
      (Scheme.Modules.pushforwardComp g.left Q.projection.left).hom.app _ := by
    apply (A.homEquiv _ _).symm.injective
    dsimp only [α]
    rw [Equiv.symm_apply_apply]
    unfold flagLineCoordinate
    exact (transpose_comp Q.projection.left g.left D.inclusion (pullbackRegular g.left)).symm
  have hα' : α.app ⊤ s =
      (flagLineCoordinate Q p χ h g).app ⊤
        (pullSection (g ≫ Q.projection).left D.sheaf s) := by
    dsimp only [α]
    rw [Adjunction.homEquiv_unit]
    rfl
  rw [← hα', hα]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply]
  change (pullbackRegular g.left).app ⊤ (D.inclusion.app ⊤ s) =
    g.left.appTop (D.inclusion.app ⊤ s)
  rw [pullbackRegular_app]
  rfl

private theorem degreeZeroCovariants (S : SocleModel P U χ)
    (L : AssociatedBundle Q a S.projection χ) (h : FlagKernelPair Q) :
    ∃ e : flagCohomology Q S.projection χ h 0 ≃ₗ[k] covariantFunctions S.restriction S.coordinate,
      ∀ (R : TestAlgebra k) (x : S.A →ₐ[k] R) (v : flagCohomology Q S.projection χ h 0),
        let g := (pointIso S.groupIso).hom.app R (toConv x)
        let s := (cohomologyZero Q.scheme).hom.app (flagLineSheaf Q S.projection χ h) v
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom
          (g.left.appTop ((flagLineData Q S.projection χ h).inclusion.app ⊤ s)) = x (e v : S.A) := by
  let M := realizeSections L
  obtain ⟨j, hj⟩ := exists_associatedFlagSheafIso L h
  let j₀ := (cohomologyZero Q.scheme).app (flagLineSheaf Q S.projection χ h) ≪≫
    (sectionsFunctor Q.scheme).mapIso j.symm
  letI : Module k Γ(M.sheaf, ⊤) := Module.compHom _ (groundScalars Q.scheme).hom
  obtain ⟨E, hE⟩ := globalCovariantSections M S.groupIso S.borelIso S.restriction S.character
    S.restriction_spec S.character_spec S.coordinate S.coordinate_spec
  let e := j₀.toLinearEquiv.trans E
  refine ⟨e, ?_⟩
  intro R x v g s
  let X := (testSpec k).obj (op R)
  let z := j₀.hom v
  have hz : j.hom.app ⊤ z = s := by
    change ((j₀.hom ≫ (sectionsFunctor Q.scheme).map j.hom) v) = _
    simp only [j₀, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id]
    rfl
  rw [← hz, hj]
  let i := g.left ≫ Q.projection.left ≫ Q.scheme.left.topIso.inv
  have hi : i ≫ (⊤ : Q.scheme.left.Opens).ι = g.left ≫ Q.projection.left := by
    simp only [i, Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  obtain ⟨u, hu, hu'⟩ := M.evaluation ⊤ z X g i hi (by simp)
  have hgeom := congrArg (g.left ≫ ·) (hE z)
  change g.left ≫ Q.projection.left ≫ Q.scheme.left.topIso.inv ≫ (M.sections ⊤ z).val =
    (g ≫ prod.lift (𝟙 G.val.X) (coordinateFunction S.groupIso (E z : S.A)) ≫ L.trivialization).left
    at hgeom
  have hx : g ≫ coordinateFunction S.groupIso (E z : S.A) = linePoint R (x (E z : S.A)) :=
    eval_coordinateFunction S.groupIso R x _
  rw [← Category.assoc g, prod.comp_lift, Category.comp_id, hx] at hgeom
  have hLine : u = linePoint R (x (E z : S.A)) := coordinate_unique L g _ _
    (Over.OverMorphism.ext (hu'.symm.trans (by simpa only [i, Category.assoc] using hgeom)))
  change lineCoordinate u = evalOn g.left (⊤ : G.val.X.left.Opens) (by simp)
    (M.functionVal ⊤ z) at hu
  rw [evalOn_top] at hu
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom (g.left.appTop (M.functionVal ⊤ z)) =
    x (E z : S.A)
  rw [← hu, hLine, lineCoordinate_linePoint]

private theorem section_weight_on_torsor {ℓ : Linearization (torusAction a) (flagLineSheaf Q p χ h)}
    (hl : PreservesFlagLineCoordinate Q a p χ h ℓ)
    {s : Γ(flagLineSheaf Q p χ h, ⊤)} {ψ : Character P.torus.group}
    (hs : HasSectionWeight ℓ s ψ) {Z : SchemeOver k} (t : Z ⟶ P.torus.group.X) (g : Z ⟶ G.val.X) :
    let x := (flagLineData Q p χ h).inclusion.app ⊤ s
    g.left.appTop x = t.left.appTop (characterFunction ψ) *
      (((t ≫ P.torus.inclusion.hom.hom) * g).left.appTop x) := by
  intro x
  obtain ⟨w, hw⟩ := hl Z t g
  let F := flagLineSheaf Q p χ h
  let g' : Z ⟶ G.val.X := (t ≫ P.torus.inclusion.hom.hom) * g
  let s₀ := pullSection (g ≫ Q.projection).left F s
  have hTransport := transport_sectionWeight ℓ hs t (g ≫ Q.projection)
  have H := ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f ⊤) hw) s₀
  change ((pullCongr F w).hom ≫ flagLineCoordinate Q p χ h g').app ⊤
      ((transport (torusAction a) ℓ.iso t (g ≫ Q.projection)).hom.app ⊤ s₀) =
    (flagLineCoordinate Q p χ h g).app ⊤ s₀ at H
  have hCongr : (pullCongr F w).hom.app ⊤ (pullSection (actOn (torusAction a) t
        (g ≫ Q.projection)).left F s) = pullSection (g' ≫ Q.projection).left F s :=
    pullSection_congr (congrArg Over.Hom.left w) F s
  rw [hTransport, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, hCongr] at H
  let r : Γ(Z.left, ⊤) := t.left.appTop (characterFunction ψ)
  let x' : Γ(Z.left, ⊤) := (flagLineCoordinate Q p χ h g').app ⊤
    (pullSection (g' ≫ Q.projection).left F s)
  calc
    g.left.appTop x = (flagLineCoordinate Q p χ h g).app ⊤ s₀ :=
      (flagLineCoordinate_section h g s).symm
    _ = r * x' := H.symm
    _ = r * g'.left.appTop x := congrArg (r * ·) (flagLineCoordinate_section h g' s)

/-- Testing on the universal point over the scalar extension gives the
coaction equation, since tensoring the inclusion of covariants is injective. -/
private theorem coaction_weight {A : HopfAlgebraCategory k}
    {D : HopfAlgebraCategory k} {q : A ⟶ D} {c : GroupLike k D}
    (δ : RightComodule k A (covariantFunctions q c))
    (hδ : ((covariantFunctions q c).subtype.rTensor A).comp δ.coaction =
      (Specs.FlagLineBundle.leftRegularCoaction A).comp (covariantFunctions q c).subtype)
    (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (f : covariantFunctions q c) (r : R)
    (h : let B := CommAlgCat.of k (A ⊗[k] R)
         letI := convolutionGroup A B
         let x : WithConv (A →ₐ[k] B) := toConv Algebra.TensorProduct.includeLeft
         let y : WithConv (A →ₐ[k] B) :=
           toConv (Algebra.TensorProduct.includeRight.comp g.ofConv)
         (y⁻¹ * x) (f : A) = (f : A) ⊗ₜ[k] r) :
    evaluate A δ g.ofConv f = f ⊗ₜ[k] r := by
  let W := covariantFunctions q c
  apply Module.Flat.rTensor_preserves_injective_linearMap (M := R) W.subtype
    Subtype.val_injective
  rw [LinearMap.rTensor_tmul]
  let f₁ := W.subtype
  let i : A →ₐ[k] A ⊗[k] R := Algebra.TensorProduct.includeLeft
  let j : R →ₐ[k] A ⊗[k] R := Algebra.TensorProduct.includeRight
  let φ := Algebra.TensorProduct.lift i (j.comp g.ofConv) (fun _ _ => Commute.all _ _)
  have H : (f₁.rTensor R).comp (g.ofConv.toLinearMap.lTensor W) =
      φ.toLinearMap.comp (f₁.rTensor A) := by
    apply TensorProduct.ext'
    intro a b
    simp [φ, i, j, f₁, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  have hd := LinearMap.congr_fun hδ f
  change (f₁.rTensor A) (δ.coaction f) =
    Specs.FlagLineBundle.leftRegularCoaction A (f : A) at hd
  change ((f₁.rTensor R).comp (g.ofConv.toLinearMap.lTensor W)) (δ.coaction f) = _
  rw [H, LinearMap.comp_apply, hd, ← leftCoactionHom_linear]
  exact (leftEval (R := CommAlgCat.of k (A ⊗[k] R)) i (j.comp g.ofConv) (f : A)).trans h

private theorem induced_weight_of_section (S : SocleModel P U χ) (h : FlagKernelPair Q)
    {ℓ : Linearization (torusAction a) (flagLineSheaf Q S.projection χ h)}
    (hl : PreservesFlagLineCoordinate Q a S.projection χ h ℓ)
    (v : flagCohomology Q S.projection χ h 0) (ψ : Character P.torus.group)
    (hv : HasSectionWeight ℓ ((cohomologyZero Q.scheme).hom.app _ v) ψ)
    (f : covariantFunctions S.restriction S.coordinate)
    (hf : ∀ (R : TestAlgebra k) (x : S.A →ₐ[k] R),
      let g := (pointIso S.groupIso).hom.app R (toConv x)
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom (g.left.appTop
        ((flagLineData Q S.projection χ h).inclusion.app ⊤
          ((cohomologyZero Q.scheme).hom.app _ v))) = x (f : S.A)) :
    S.inducedBasis.equivFun f ∈ weightSpace S.inducedAction P.torus ψ := by
  apply mem_weightSpace.mpr
  intro R t
  let A := S.A
  let B := CommAlgCat.of k (A ⊗[k] R)
  let i : R ⟶ B := CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R)
  letI := convolutionGroup A R
  letI := convolutionGroup A B
  let j : A →ₐ[k] B := Algebra.TensorProduct.includeLeft
  let g : GroupPoints G.val R := t ≫ P.torus.inclusion.hom.hom
  let y := (pointIso S.groupIso).inv.app R g
  have hy : (pointIso S.groupIso).hom.app R y = g :=
    Iso.inv_hom_id_apply ((evaluation _ _).obj R |>.mapIso (pointIso S.groupIso)) g
  let y' : WithConv (A →ₐ[k] B) := toConv (i.hom.comp y.ofConv)
  let x : WithConv (A →ₐ[k] B) := toConv j
  let t' : GroupPoints P.torus.group B := (testSpec k).map i.op ≫ t
  have hy' : (pointIso S.groupIso).hom.app B y' = t' ≫ P.torus.inclusion.hom.hom := by
    have he := DFunLike.congr_fun (congrArg GrpCat.Hom.hom ((pointIso S.groupIso).hom.naturality i)) y
    change (pointIso S.groupIso).hom.app B y' =
      (testSpec k).map i.op ≫ ((pointIso S.groupIso).hom.app R y) at he
    rw [hy] at he
    exact he.trans (Category.assoc _ _ _).symm
  let z := y'⁻¹ * x
  let Pₓ : GroupPoints G.val B := (pointIso S.groupIso).hom.app B x
  let Pz : GroupPoints G.val B := (pointIso S.groupIso).hom.app B z
  let tG : GroupPoints G.val B := t' ≫ P.torus.inclusion.hom.hom
  have hm : tG * Pz = Pₓ := by
    change tG * (pointIso S.groupIso).hom.app B (y'⁻¹ * x) =
      (pointIso S.groupIso).hom.app B x
    rw [show tG = (pointIso S.groupIso).hom.app B y' from hy'.symm,
      ← map_mul, mul_inv_cancel_left]
  have H := section_weight_on_torsor h hl hv t' Pz
  let c := (flagLineData Q S.projection χ h).inclusion.app ⊤
    ((cohomologyZero Q.scheme).hom.app _ v)
  change Pz.left.appTop c = t'.left.appTop (characterFunction ψ) * (tG * Pz).left.appTop c at H
  rw [hm] at H
  have H' := congrArg (fun c => (Scheme.ΓSpecIso (CommRingCat.of B)).hom c) H
  rw [map_mul, hf B z.ofConv, hf B x.ofConv, characterValue_eval] at H'
  have hv' : characterValue ψ B t' = i.hom (characterValue ψ R t) :=
    characterValue_natural ψ i t
  rw [hv'] at H'
  have hp : z (f : A) = (f : A) ⊗ₜ[k] characterValue ψ R t := by
    refine H'.trans ?_
    change ((1 : A) ⊗ₜ[k] characterValue ψ R t) * ((f : A) ⊗ₜ[k] (1 : R)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have actEq := coaction_weight S.inducedCoaction S.leftTranslation R y f (characterValue ψ R t) hp
  funext j₀
  change act S.inducedAction R g (extendVector R (S.inducedBasis.equivFun f)) j₀ = _
  rw [← hy]
  change act S.inducedAction R
    ((testSpec k).map (CommAlgCat.ofHom y.ofConv).op ≫ S.groupIso.hom.hom.hom)
    (extendVector R (S.inducedBasis.equivFun f)) j₀ = _
  rw [S.inducedAction_spec, LinearEquiv.symm_apply_apply, actEq, tensorCoordinate_tmul]
  simp [extendVector, Module.Basis.equivFun_apply, Module.Basis.coord_apply, Algebra.smul_def, mul_comm]

/-- Under the linear identification of global sections with covariant
functions, a torus weight basis keeps its weights. -/
private theorem degreeZero_character (S : SocleModel P U χ)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (h : FlagKernelPair Q) (b : CohomologyBasis (p := S.projection) (χ := χ) h 0)
    (ρ : Representation G.val (CohomologyIndex (p := S.projection) (χ := χ) h 0))
    (hρ : IsFlagCohomologyAction h a 0 b ρ) :
    formalCharacter P.torus (ρ) = formalCharacter P.torus S.inducedAction := by
  classical
  obtain ⟨L⟩ := exists_associatedBundle Q S.projection χ a ha
  obtain ⟨e, he⟩ := degreeZeroCovariants S L h
  obtain ⟨ℓ, hℓ, hcmp⟩ := FlagCovarianceLinearization.flagCovarianceLinearization Q a S.projection χ h ha
  have hF := flagLineSheaf_finitePresentation Q a S.projection χ h ha
  obtain ⟨m⟩ := cohomologyPullbacks_nonempty
    (⟨_, hF, ℓ⟩ : EquivariantAffineModules.EquivariantCoherent (torusAction a)) 0
  let E := b.equivFun.symm.trans (e.trans S.inducedBasis.equivFun)
  have hwt (ψ : Character P.torus.group) (z) (hz : z ∈ weightSpace ρ P.torus ψ) :
      E z ∈ weightSpace S.inducedAction P.torus ψ := by
    let v := b.equivFun.symm z
    have hv := (flagLineCohomology_weight ℓ hcmp hF 0 b ρ hρ m ψ v).mpr
      (by simpa only [v, LinearEquiv.apply_symm_apply] using hz)
    have hs := (FlagEquivariantEulerMap.cohomologyWeights_zero m ψ v).mp hv
    exact induced_weight_of_section S h hℓ v ψ hs (e v) (fun R x => he R x v)
  let F := internalWeights P.torus P.split ρ
  let A := weightSpace ρ P.torus
  let c := F.collectedBasis (fun ψ => Module.finBasis k (A ψ))
  letI := FiniteDimensional.fintypeBasisIndex c
  have hc (i : Σ ψ, Fin (Module.finrank k (A ψ))) : c i ∈ A i.1 :=
    F.collectedBasis_mem _ i
  rw [characterOfBasis P.torus P.split ρ c Sigma.fst hc,
    characterOfBasis P.torus P.split S.inducedAction (c.map E) Sigma.fst
      (fun i => by simpa only [Module.Basis.map_apply] using hwt i.1 (c i) (hc i))]

end DegreeZero

private theorem formula_unique {P : OppositeBorelPair G} [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) [Finite (Root P.torus)] [Finite D.rootDatum.weylGroup]
    (b : D.rootDatum.Base) (χ : Character P.torus.group)
    {c d : MonoidAlgebra ℤ (Character P.torus.group)}
    (hc : SatisfiesFormula D b χ c) (hd : SatisfiesFormula D b χ d) : c = d := by
  let T := P.torus.group
  let := D.freeCharacters
  let := halfWeightDomain T
  let A := GroupRing (Additive (Character T))
  exact includeCharacters_injective T
    (IsFractionRing.injective A (FractionRing A) (hc.2.trans hd.2.symm))

/-- The Weyl character formula for the induced module, its opposition dual,
and the simple socle when induction is simple. -/
theorem weylCharacter : Statement.{u} := by
  classical
  intro k _ G P U hU
  obtain ⟨_, ⟨Q⟩, hQ⟩ := LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P
  obtain ⟨_, _, _, _, _, _, _, a, _, _, ha⟩ := hQ Q
  obtain ⟨hC, D, e, hW, hR, b, hb, _hRep, _hEmpty, _hFib, _hProj, h, euler⟩ :=
    (FlagEulerAndVanishing.flagEulerAndVanishing.{u}).1 P Q a ha
  letI := hC
  letI := hR
  letI := hW
  obtain ⟨_, D', e', b', w', hb', hw', modules⟩ := WeylModules.weylModules G P U hU
  let l := weylLabelEquiv e' e P.split
  let w := l w'
  have hw (v : D.rootDatum.weylGroup) :
      SimpleRoots.wordLength D.rootDatum b v ≤ SimpleRoots.wordLength D.rootDatum b w := by
    obtain ⟨v', rfl⟩ := l.surjective v
    change SimpleRoots.wordLength D.rootDatum b (weylLabelEquiv e' e P.split v') ≤
      SimpleRoots.wordLength D.rootDatum b (weylLabelEquiv e' e P.split w')
    rw [length_transport P e' e b' b hb' hb, length_transport P e' e b' b hb' hb]
    exact hw' _
  have hop (χ : Character P.torus.group) : oppositeWeight e' w' χ = oppositeWeight e w χ := by
    unfold oppositeWeight
    rw [show (e.labelEquiv w).val = (e'.labelEquiv w').val from weylLabelEquiv_label e' e P.split w']
  have inducedFormula (χ : Character P.torus.group) (hχ : Dominant P χ) (S : SocleModel P U χ) :
      SatisfiesFormula D b χ (formalCharacter P.torus S.inducedAction) := by
    obtain ⟨⟨r, basis, N, hr, hN⟩, he⟩ := euler S.projection χ h
    have hf : SatisfiesFormula D b χ (equivariantEulerCharacteristic h r N) :=
      he r basis hr N hN
    have hz := euler_eq_degree_zero Q S.projection χ h r N hN
      (fun i hi => (FlagEulerAndVanishing.flagEulerAndVanishing.{u}).2 P χ hχ Q S.projection h i hi)
    rw [hz, degreeZero_character S ha h (basis 0) (r 0) (hr 0)] at hf
    exact hf
  refine ⟨hC, D, e, hR, hW, b, w, hb, hw, ?_⟩
  intro χ hχ
  obtain ⟨hχ', S₀, S₀', Δ₀, _, hΔ₀, _, _, _, _, _, _, _⟩ := modules χ hχ
  have hDominantOpp : Dominant P (oppositeWeight e w χ) := by
    rw [← hop χ]
    exact hχ'
  refine ⟨hDominantOpp, ?_, ?_⟩
  · rw [← hop χ]
    exact ⟨S₀, S₀', Δ₀, hΔ₀⟩
  · intro S
    have hInd := inducedFormula χ hχ S
    refine ⟨hInd, ?_, ?_, ?_⟩
    · intro S' Δ hΔ
      have hOpp := inducedFormula _ hDominantOpp S'
      have hWeyl : SatisfiesFormula D b χ (formalCharacter P.torus Δ) := by
        rw [dual_character P hΔ]
        exact opposite_formula P e b hb w hw χ _ hOpp
      exact formula_unique D b χ hWeyl hInd
    · intro hs
      rwa [simple_socle_character S hs]
    · intro hz
      letI := hz
      rwa [simple_socle_character S (induced_simple_of_charZero S).1]

end

end LinearAlgebraicGroups.Representation.WeylCharacter
