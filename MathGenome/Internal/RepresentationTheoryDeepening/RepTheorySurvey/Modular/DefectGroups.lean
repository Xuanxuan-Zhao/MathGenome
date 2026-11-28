import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.DefectGroups
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.ModularBlocks
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.BrauerHomomorphism
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.CentralTraceIdeals
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.GroupAlgebraCenter
import Mathlib.RingTheory.LocalRing.Basic

noncomputable section

open scoped MonoidAlgebra

namespace RepTheorySurvey.Modular.DefectGroups

open CentralTraceIdeals GroupAlgebraCenter
open DefectGroupsSpec (sylowImage)

universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G]

/-- The Brauer projection of a block idempotent. -/
abbrev brauerImage := @DefectGroupsSpec.brauerImage

/-- An inclusion-maximal p-subgroup with nonzero Brauer image of the block. -/
abbrev isDefectGroup := @DefectGroupsSpec.isDefectGroup

private theorem brauerImage_ne_zero_iff (b : BlockIdempotent k G) (P : Subgroup G) :
    brauerImage b P ≠ 0 ↔
    ∃ x : G, P ≤ Subgroup.centralizer ({x} : Set G) ∧ b.element.coeff x ≠ 0 := by
  constructor
  · intro h
    by_contra! hz
    apply h
    ext x
    exact hz x (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (x.property y hy))
  · rintro ⟨x, hx, hn⟩ h
    let y : Subgroup.centralizer (P : Set G) :=
      ⟨x, fun z hz => Subgroup.mem_centralizer_singleton_iff.mp (hx hz)⟩
    exact hn (congrArg (fun a : BrauerHomomorphism.CentralizerAlgebra k P => a.coeff y) h)

private theorem map_conj_one (D : Subgroup G) :
    D.map (MulAut.conj (1 : G)).toMonoidHom = D := by
  rw [map_one]
  exact D.map_id

private theorem map_conj_mul (D : Subgroup G) (g h : G) :
    (D.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      D.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

private theorem sylowImage_le {p : ℕ} {x : G}
    (S : Sylow p (Subgroup.centralizer ({x} : Set G))) :
    sylowImage S ≤ Subgroup.centralizer ({x} : Set G) := by
  rintro _ ⟨y, _, rfl⟩
  exact y.property

private theorem card_sylowImage {p : ℕ} {x : G}
    (S : Sylow p (Subgroup.centralizer ({x} : Set G))) :
    Nat.card (sylowImage S) = Nat.card S :=
  Subgroup.card_map_of_injective Subtype.coe_injective

variable [Finite G] {p : ℕ} [Fact p.Prime]

private theorem sylowImage_conjugate {x : G}
    (S T : Sylow p (Subgroup.centralizer ({x} : Set G))) :
    ∃ g : G, sylowImage T = (sylowImage S).map (MulAut.conj g).toMonoidHom := by
  let C := Subgroup.centralizer ({x} : Set G)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S T
  refine ⟨g, ?_⟩
  have hm : (S : Subgroup C).map (MulAut.conj g).toMonoidHom = (T : Subgroup C) :=
    congrArg Sylow.toSubgroup hg
  change (T : Subgroup C).map C.subtype =
    ((S : Subgroup C).map C.subtype).map (MulAut.conj (g : G)).toMonoidHom
  rw [← hm, Subgroup.map_map, Subgroup.map_map]
  rfl

omit [Fact p.Prime] in
private theorem isDefectGroup_iff_of_brauer_criterion
    (b : BlockIdempotent k G) (D : Subgroup G) (hD : IsPGroup p D)
    (h : ∀ P : Subgroup G, IsPGroup p P →
      (brauerImage b P ≠ 0 ↔ ∃ g : G, P ≤ D.map (MulAut.conj g).toMonoidHom))
    (P : Subgroup G) :
    isDefectGroup p b P ↔ ∃ g : G, P = D.map (MulAut.conj g).toMonoidHom := by
  have hgood (g : G) :
      IsPGroup p (D.map (MulAut.conj g).toMonoidHom) ∧
        brauerImage b (D.map (MulAut.conj g).toMonoidHom) ≠ 0 := by
    have hp := hD.map (MulAut.conj g).toMonoidHom
    exact ⟨hp, (h _ hp).mpr ⟨g, le_rfl⟩⟩
  have hcard (g : G) : Nat.card (D.map (MulAut.conj g).toMonoidHom) = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  constructor
  · intro hP
    obtain ⟨g, hg⟩ := (h P hP.1.1).mp hP.1.2
    exact ⟨g, le_antisymm hg (hP.2 (hgood g) hg)⟩
  · rintro ⟨g, rfl⟩
    refine ⟨hgood g, ?_⟩
    intro Q hQ hle
    obtain ⟨a, ha⟩ := (h Q hQ.1).mp hQ.2
    apply (Subgroup.eq_of_le_of_card_ge hle ?_).ge
    rw [hcard g, ← hcard a]
    exact Subgroup.card_le_of_le ha

variable [CharP k p]

private theorem exists_support_sylow_trace (b : BlockIdempotent k G) :
    ∃ (x : G) (S : Sylow p (Subgroup.centralizer ({x} : Set G))),
      b.element.coeff x ≠ 0 ∧ b.val ∈ traceIdeal k (sylowImage S) := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite (ConjClasses G)
  let : IsLocalRing b.Center := b.center_isLocal
  let Z := Subalgebra.center k k[G]
  let cut : Z →+ b.Center :=
    { toFun := fun z => ⟨b.val * z, (Subsemigroup.mem_corner_iff
        b.center_idempotent).mpr ⟨by rw [← mul_assoc, b.center_idempotent.eq],
          by rw [mul_comm (b.val * z) b.val, ← mul_assoc, b.center_idempotent.eq]⟩⟩
      map_zero' := Subtype.ext (mul_zero _)
      map_add' := fun x y => Subtype.ext (mul_add _ _ _) }
  let a (C : ConjClasses G) : Z := centerClassEquiv k b.val C • classSumBasis k C
  have hsum : ∑ C, a C = b.val := by
    have hcoeff : (classSumBasis (G := G) k).equivFun = centerClassEquiv k :=
      Module.Basis.equivFun_ofEquivFun _
    have hb := (classSumBasis (G := G) k).sum_equivFun b.val
    rwa [hcoeff] at hb
  have hsum_cut : ∑ C, cut (a C) = 1 := by
    rw [← map_sum, hsum]
    exact Subtype.ext b.center_idempotent.eq
  obtain ⟨C, _, hunit⟩ := IsLocalRing.exists_of_isUnit_sum (hsum_cut ▸ isUnit_one)
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective C
  have hx : b.element.coeff x ≠ 0 := by
    intro hz
    have ha : a (ConjClasses.mk x) = 0 := by
      dsimp only [a]
      rw [centerClassEquiv_apply_mk, show b.val.val.coeff x = 0 from hz, zero_smul]
    exact not_isUnit_zero (by simpa only [ha, map_zero] using hunit)
  let S : Sylow p (Subgroup.centralizer ({x} : Set G)) := default
  let D := sylowImage S
  let I := traceIdeal k D
  have hBasis : classSumBasis k (ConjClasses.mk x) ∈ I :=
    (classBasis_mem_traceIdeal_iff k p D (S.isPGroup'.map _) x).mpr
      ⟨S, 1, (map_conj_one D).le⟩
  have ha : a (ConjClasses.mk x) ∈ I := by
    dsimp only [a]
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hBasis
  obtain ⟨unit, hunit⟩ := hunit
  have hu := congrArg (fun c : b.Center => c.val) unit.inv_mul
  change unit.inv.val * (unit.val : b.Center).val = b.val at hu
  rw [hunit] at hu
  change unit.inv.val * (b.val * a (ConjClasses.mk x)) = b.val at hu
  exact ⟨x, S, hx, hu ▸ I.mul_mem_left _ (I.mul_mem_left _ ha)⟩

private theorem brauer_criterion_of_support_sylow_trace
    (b : BlockIdempotent k G) {x : G}
    (S : Sylow p (Subgroup.centralizer ({x} : Set G)))
    (hx : b.element.coeff x ≠ 0) (hb : b.val ∈ traceIdeal k (sylowImage S))
    (P : Subgroup G) (hP : IsPGroup p P) :
    brauerImage b P ≠ 0 ↔ ∃ g : G, P ≤ (sylowImage S).map (MulAut.conj g).toMonoidHom := by
  classical
  let := Fintype.ofFinite G
  let D := sylowImage S
  rw [brauerImage_ne_zero_iff]
  constructor
  · rintro ⟨y, hy, hcoeff⟩
    let C := Subgroup.centralizer ({y} : Set G)
    obtain ⟨T, hT⟩ := (hP.comap_subtype (K := C)).exists_le_sylow
    have hPT : P ≤ sylowImage T := by
      intro z hz
      exact ⟨⟨z, hy hz⟩, hT hz, rfl⟩
    obtain ⟨U, g, hg⟩ :=
      sylowConjugateInto_of_mem_traceIdeal k p D (S.isPGroup'.map _) y b.val hb hcoeff
    obtain ⟨a, ha⟩ := sylowImage_conjugate U T
    refine ⟨a * g⁻¹, hPT.trans ?_⟩
    rw [ha]
    have hm := Subgroup.map_mono (f := (MulAut.conj (a * g⁻¹)).toMonoidHom) hg
    simpa only [map_conj_mul, mul_assoc, inv_mul_cancel, mul_one] using hm
  · rintro ⟨g, hg⟩
    let e := MulAut.conj g
    refine ⟨e x, ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := hg hy
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact (map_mul e z x).symm.trans
        ((congrArg e (Subgroup.mem_centralizer_singleton_iff.mp (sylowImage_le S hz))).trans
          (map_mul e x z))
    · have hconj : ConjClasses.mk x = ConjClasses.mk (e x) :=
        ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, rfl⟩)
      rwa [← (mem_center_iff b.element).mp b.val.property x (e x) hconj]

/-- A Sylow subgroup of a centralizer from the support controls every Brauer image
and has maximal order among the Sylow subgroups arising from the support. -/
theorem exists_support_sylow : DefectGroupsSpec.existsSupportSylowType.{u, v} := by
  intro k _ G _ _ p _ _ b
  classical
  let := Fintype.ofFinite G
  obtain ⟨x, S, hx, hb⟩ := exists_support_sylow_trace (p := p) b
  let D := sylowImage S
  have hD : IsPGroup p D := S.isPGroup'.map _
  have h := brauer_criterion_of_support_sylow_trace b S hx hb
  have hdef := isDefectGroup_iff_of_brauer_criterion b D hD h D
  refine ⟨x, S, hx, hb, hdef.mpr ⟨1, (map_conj_one D).symm⟩, h, ?_⟩
  intro y hy T
  obtain ⟨U, g, hg⟩ := sylowConjugateInto_of_mem_traceIdeal k p D hD y b.val hb hy
  have hcard := Subgroup.card_le_of_le hg
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    card_sylowImage U, card_sylowImage S] at hcard
  simpa only [Sylow.card_eq_multiplicity T, Sylow.card_eq_multiplicity U] using hcard

/-- All defect groups of a block are the conjugates of any representative
supplied by the support criterion. -/
theorem defect_groups_conjugacy : DefectGroupsSpec.defectGroupsConjugacyType.{u, v} := by
  intro k _ G _ _ p _ _ b
  obtain ⟨x, S, _, _, hD, h, _⟩ := exists_support_sylow p b
  exact ⟨sylowImage S, hD, isDefectGroup_iff_of_brauer_criterion b _ (S.isPGroup'.map _) h⟩

end RepTheorySurvey.Modular.DefectGroups
