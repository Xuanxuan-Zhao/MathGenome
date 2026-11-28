import MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.Basic
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.AdjointCohomology
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic.Module

/-! Adjoint cohomology of a Heisenberg algebra with its ordered basis. -/

noncomputable section

namespace LieNotes.Heisenberg.AdjointCohomology

open AdvancedHomologicalAlgebra.CE
open LieAlgebrasAndRepresentations.AbelianExtensions LieModule.Cohomology
open Specs.LieNotes.Heisenberg.AdjointCohomology
open Set.powersetCard

universe u v

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]

theorem d_formula : HasLieCEFormula (d k L) :=
  (Classical.choose_spec (canonicalCEExists_spec (k := k) (g := L) (M := L))).2

theorem d_squared (n : ℕ) (f : Cochains k L n) : d k L (n + 1) (d k L n f) = 0 :=
  LinearMap.congr_fun
    ((Classical.choose_spec (canonicalCEExists_spec (k := k) (g := L) (M := L))).1 n) f

private def pairIndex (i j : Fin 3) (h : i < j) : Set.powersetCard (Fin 3) 2 :=
  ofFinEmbEquiv (OrderEmbedding.ofStrictMono ![i, j] (by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact (lt_irrefl _ hab).elim
    · exact h
    · exact ((by decide : ¬ (1 : Fin 2) < 0) hab).elim
    · exact (lt_irrefl _ hab).elim))

private abbrev xyIndex := pairIndex 0 1 (by decide)
private abbrev xzIndex := pairIndex 0 2 (by decide)
private abbrev yzIndex := pairIndex 1 2 (by decide)

private def tripleIndex : Set.powersetCard (Fin 3) 3 :=
  ofFinEmbEquiv ((OrderIso.refl (Fin 3)).toOrderEmbedding)

private theorem pairIndex_cases (s : Set.powersetCard (Fin 3) 2) :
    s = xyIndex ∨ s = xzIndex ∨ s = yzIndex := by
  let f := ofFinEmbEquiv.symm s
  have hlt : f 0 < f 1 := f.strictMono (by decide)
  have hs : s = pairIndex (f 0) (f 1) hlt := by
    calc
      s = ofFinEmbEquiv f := (ofFinEmbEquiv.apply_symm_apply s).symm
      _ = _ := by
        apply congrArg ofFinEmbEquiv
        apply DFunLike.ext
        intro i
        fin_cases i <;> rfl
  rw [hs]
  generalize f 0 = i at hlt ⊢
  generalize f 1 = j at hlt ⊢
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | contradiction

private theorem tripleIndex_unique (s : Set.powersetCard (Fin 3) 3) :
    s = tripleIndex := by
  apply Subtype.ext
  trans Finset.univ
  · exact (Finset.card_eq_iff_eq_univ _).mp (s.prop.trans (Fintype.card_fin 3).symm)
  · exact ((Finset.card_eq_iff_eq_univ _).mp
      (tripleIndex.prop.trans (Fintype.card_fin 3).symm)).symm

variable (b : Module.Basis (Fin 3) k L)

private abbrev xy := wedge k L 2 ![b 0, b 1]
private abbrev xz := wedge k L 2 ![b 0, b 2]
private abbrev yz := wedge k L 2 ![b 1, b 2]
private abbrev xyz := wedge k L 3 ![b 0, b 1, b 2]

private theorem exterior_pair (i j : Fin 3) (h : i < j) :
    b.exteriorPower 2 (pairIndex i j h) = wedge k L 2 ![b i, b j] := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, pairIndex, Equiv.symm_apply_apply]
  congr 1
  funext a
  fin_cases a <;> rfl

private theorem exterior_triple : b.exteriorPower 3 tripleIndex = xyz b := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, tripleIndex, Equiv.symm_apply_apply]
  congr 1
  funext a
  fin_cases a <;> rfl

private theorem two_ext {f g : Cochains k L 2}
    (hxy : f (xy b) = g (xy b)) (hxz : f (xz b) = g (xz b))
    (hyz : f (yz b) = g (yz b)) : f = g := by
  apply (b.exteriorPower 2).ext
  intro s
  rcases pairIndex_cases s with rfl | rfl | rfl
  all_goals rw [exterior_pair]
  exacts [hxy, hxz, hyz]

private theorem three_ext {f g : Cochains k L 3}
    (h : f (xyz b) = g (xyz b)) : f = g := by
  apply (b.exteriorPower 3).ext
  intro s
  rw [tripleIndex_unique s, exterior_triple]
  exact h

private def makeTwo (A B C : L) : Cochains k L 2 :=
  (b.exteriorPower 2).constr k (fun s => if s = xyIndex then A else if s = xzIndex then B else C)

private theorem makeTwo_values (A B C : L) :
    makeTwo b A B C (xy b) = A ∧
    makeTwo b A B C (xz b) = B ∧
    makeTwo b A B C (yz b) = C := by
  have h₁ : xzIndex ≠ xyIndex := by decide
  have h₂ : yzIndex ≠ xyIndex := by decide
  have h₃ : yzIndex ≠ xzIndex := by decide
  unfold makeTwo xy xz yz
  rw [← exterior_pair b 0 1 (by decide), ← exterior_pair b 0 2 (by decide),
    ← exterior_pair b 1 2 (by decide)]
  simp only [Module.Basis.constr_basis, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃, ite_true, true_and]

private def makeThree (A : L) : Cochains k L 3 :=
  (b.exteriorPower 3).constr k (fun _ => A)

@[simp] private theorem makeThree_apply (A : L) : makeThree b A (xyz b) = A := by
  rw [← exterior_triple b, makeThree, Module.Basis.constr_basis]

private theorem bracket_x (h : HeisenbergBasis b) (p : L) :
    ⁅b 0, p⁆ = b.repr p 1 • b 2 := by
  have hmap : LieAlgebra.ad k L (b 0) = (b.coord 1).smulRight (b 2) := by
    apply b.ext
    intro i
    fin_cases i <;> simp [Module.Basis.coord_apply, h.1, h.2.1]
  exact LinearMap.congr_fun hmap p

private theorem bracket_y (h : HeisenbergBasis b) (p : L) :
    ⁅b 1, p⁆ = (-b.repr p 0) • b 2 := by
  have hyx : ⁅b 1, b 0⁆ = -b 2 := by rw [← lie_skew, h.1]
  have hmap : LieAlgebra.ad k L (b 1) = -((b.coord 0).smulRight (b 2)) := by
    apply b.ext
    intro i
    fin_cases i <;> simp [Module.Basis.coord_apply, hyx, h.2.2]
  simpa using LinearMap.congr_fun hmap p

private theorem bracket_z (h : HeisenbergBasis b) (p : L) : ⁅b 2, p⁆ = 0 := by
  have hzx : ⁅b 2, b 0⁆ = 0 := by rw [← lie_skew, h.2.1, neg_zero]
  have hzy : ⁅b 2, b 1⁆ = 0 := by rw [← lie_skew, h.2.2, neg_zero]
  have hmap : LieAlgebra.ad k L (b 2) = 0 := by
    apply b.ext
    intro i
    fin_cases i <;> simp [hzx, hzy]
  exact LinearMap.congr_fun hmap p

private theorem d_two (h : HeisenbergBasis b) (f : Cochains k L 2) :
    d k L 2 f (xyz b) = (b.repr (f (yz b)) 1 + b.repr (f (xz b)) 0) • b 2 := by
  let e := twoCochainExteriorEquiv (k := k) (g := L) (M := L)
  let c := e.symm f
  have he : cochainExterior c = f := e.apply_symm_apply f
  have hc (p q : L) : c p q = f (wedge k L 2 ![p, q]) := rfl
  calc
    d k L 2 f (xyz b) = d₂₃ k L L c (b 0) (b 1) (b 2) := by
      rw [← he, ce_two_formula _ d_formula]
    _ = _ := by
      have hzero (p : L) : c 0 p = 0 :=
        LinearMap.congr_fun (map_zero (c : L →ₗ[k] L →ₗ[k] L)) p
      rw [d₂₃_apply, h.1, h.2.1, h.2.2, twoCochain_alt c (b 2), hzero, hzero,
        bracket_z b h, add_zero, sub_zero, add_zero, sub_zero, hc, hc,
        bracket_x b h, bracket_y b h, neg_smul, sub_neg_eq_add, add_smul]

theorem differential_two : DifferentialTwoType := by
  intro k _ _ L _ _ b h f
  exact d_two b h f

private theorem d_two_image (h : HeisenbergBasis b) (v : L) :
    (∃ f : Cochains k L 2, d k L 2 f (xyz b) = v) ↔ v ∈ k ∙ b 2 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨_, (d_two b h f).symm⟩
  · rintro ⟨r, rfl⟩
    refine ⟨makeTwo b 0 (r • b 0) 0, ?_⟩
    rw [d_two b h, (makeTwo_values b _ _ _).2.1, (makeTwo_values b _ _ _).2.2]
    simp

theorem differential_two_image : DifferentialTwoImageType := by
  intro k _ _ L _ _ b h v
  exact d_two_image b h v

include b in
private theorem cochains_four : Subsingleton (Cochains k L 4) := by
  have : Module.Finite k L := Module.Finite.of_basis b
  have h : Module.finrank k (W k L 4) = 0 := by
    change Module.finrank k (⋀[k]^4 L) = 0
    rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b, Fintype.card_fin]
    decide
  have : Subsingleton (W k L 4) := Module.finrank_zero_iff.mp h
  infer_instance

theorem cochains_four_zero : CochainsFourType := by
  intro k _ _ L _ _ b
  exact cochains_four b

private abbrev evalOne (f : Cochains k L 1) (p : L) := f (wedge k L 1 ![p])

private theorem d_one_values (h : HeisenbergBasis b) (f : Cochains k L 1) :
    d k L 1 f (xy b) =
        (b.repr (evalOne f (b 1)) 1 + b.repr (evalOne f (b 0)) 0) • b 2 - evalOne f (b 2) ∧
    d k L 1 f (xz b) = b.repr (evalOne f (b 2)) 1 • b 2 ∧
    d k L 1 f (yz b) = (-b.repr (evalOne f (b 2)) 0) • b 2 := by
  have hz : wedge k L 1 ![(0 : L)] = 0 :=
    (wedge k L 1).map_coord_zero 0 rfl
  simp only [xy, xz, yz, ce_one_formula _ d_formula, h.1, h.2.1, h.2.2, hz,
    bracket_x b h, bracket_y b h, bracket_z b h, map_zero, sub_zero, neg_smul,
    sub_neg_eq_add, add_smul, and_self]

private theorem boundary_pair_values (h : HeisenbergBasis b)
    {f : Cochains k L 2} (hf : f ∈ LinearMap.range (d k L 1)) :
    f (xz b) = (-b.repr (f (xy b)) 1) • b 2 ∧
    f (yz b) = b.repr (f (xy b)) 0 • b 2 := by
  obtain ⟨g, rfl⟩ := hf
  obtain ⟨ha, hb, hc⟩ := d_one_values b h g
  rw [ha, hb, hc]
  simp [Finsupp.sub_apply]

private def makeOne (f : L →ₗ[k] L) : Cochains k L 1 :=
  exteriorPower.alternatingMapLinearEquiv (AlternatingMap.ofSubsingleton k L L 0 f)

@[simp] private theorem makeOne_apply (f : L →ₗ[k] L) (p : L) : evalOne (makeOne f) p = f p :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

private theorem boundaries_two (h : HeisenbergBasis b) (v : L) :
    ∃! f : Cochains k L 2, f ∈ LinearMap.range (d k L 1) ∧ f (xy b) = v := by
  let g := makeOne ((b.coord 2).smulRight (-v))
  have hg : d k L 1 g (xy b) = v := by
    rw [(d_one_values b h g).1]
    simp [g, Module.Basis.coord_apply]
  refine ⟨d k L 1 g, ⟨⟨g, rfl⟩, hg⟩, ?_⟩
  intro f hf
  have hgf : d k L 1 g ∈ LinearMap.range (d k L 1) := ⟨g, rfl⟩
  have ha : f (xy b) = d k L 1 g (xy b) := hf.2.trans hg.symm
  obtain ⟨hxz, hyz⟩ := boundary_pair_values b h hf.1
  obtain ⟨gxz, gyz⟩ := boundary_pair_values b h hgf
  exact two_ext b ha (by rw [hxz, gxz, ha]) (by rw [hyz, gyz, ha])

theorem coboundaries_two : BoundariesTwoType := by
  intro k _ _ L _ _ b h v
  exact boundaries_two b h v

private def evalThree : Cycles k L 3 →ₗ[k] L where
  toFun f := f.1 (xyz b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalThree_bijective : Function.Bijective (evalThree b) := by
  have : Subsingleton (Cochains k L 4) := cochains_four b
  constructor
  · intro f g he
    exact Subtype.ext (three_ext b he)
  · intro v
    exact ⟨⟨makeThree b v, Subsingleton.elim _ _⟩, makeThree_apply b v⟩

theorem evaluation_three : EvaluationThreeType := by
  intro k _ _ L _ _ b h
  let e := LinearEquiv.ofBijective (evalThree b) (evalThree_bijective b)
  have he : (boundaries k L 2).map e.toLinearMap = k ∙ b 2 := by
    ext v
    constructor
    · rintro ⟨f, hf, hv⟩
      obtain ⟨g, hg⟩ := hf
      apply (d_two_image b h v).mp
      exact ⟨g, (congrArg (fun ψ : Cochains k L 3 => ψ (xyz b)) hg).trans hv⟩
    · intro hv
      obtain ⟨f, hf⟩ := (d_two_image b h v).mpr hv
      exact ⟨⟨d k L 2 f, d_squared 2 f⟩, ⟨f, rfl⟩, hf⟩
  exact ⟨Submodule.Quotient.equiv _ _ e he, fun _ => rfl⟩

private def normalCochain (p : Fin 5 → k) : Cochains k L 2 :=
  makeTwo b 0 (p 0 • b 0 + p 1 • b 1 + p 2 • b 2) (p 3 • b 0 - p 0 • b 1 + p 4 • b 2)

private theorem normalCochain_values (p : Fin 5 → k) :
    HasNormalValues b p (normalCochain b p) :=
  makeTwo_values b _ _ _

private theorem normalValues_ext {p : Fin 5 → k} {f g : Cochains k L 2}
    (hf : HasNormalValues b p f) (hg : HasNormalValues b p g) : f = g :=
  two_ext b (hf.1.trans hg.1.symm) (hf.2.1.trans hg.2.1.symm) (hf.2.2.trans hg.2.2.symm)

private def normalCycle (h : HeisenbergBasis b) (p : Fin 5 → k) : Cycles k L 2 :=
  ⟨normalCochain b p, by
    apply three_ext b
    obtain ⟨_, hB, hC⟩ := normalCochain_values b p
    rw [d_two b h, hB, hC, LinearMap.zero_apply]
    simp [Finsupp.add_apply, Finsupp.sub_apply]⟩

private def parameters (f : Cochains k L 2) : Fin 5 → k :=
  ![b.repr (f (xz b)) 0, b.repr (f (xz b)) 1, b.repr (f (xz b)) 2,
    b.repr (f (yz b)) 0, b.repr (f (yz b)) 2]

private theorem parameters_normal (p : Fin 5 → k) :
    parameters b (normalCochain b p) = p := by
  obtain ⟨_, hB, hC⟩ := normalCochain_values b p
  funext i
  fin_cases i <;> simp [parameters, hB, hC, Finsupp.add_apply, Finsupp.sub_apply]

private theorem basis_expansion (v : L) :
    v = b.repr v 0 • b 0 + b.repr v 1 • b 1 + b.repr v 2 • b 2 := by
  simpa only [Fin.sum_univ_three, add_assoc] using (b.sum_repr v).symm

private theorem normalized_cycle_values (h : HeisenbergBasis b) (f : Cycles k L 2)
    (hxy : f.1 (xy b) = 0) : HasNormalValues b (parameters b f.1) f.1 := by
  have hz : d k L 2 f.1 (xyz b) = 0 := LinearMap.congr_fun f.2 _
  rw [d_two b h] at hz
  have hs := (smul_eq_zero.mp hz).resolve_right (b.ne_zero 2)
  have hC : b.repr (f.1 (yz b)) 1 = -b.repr (f.1 (xz b)) 0 := eq_neg_of_add_eq_zero_left hs
  refine ⟨hxy, ?_, ?_⟩
  · exact basis_expansion b (f.1 (xz b))
  · simpa [parameters, hC, neg_smul, sub_eq_add_neg] using basis_expansion b (f.1 (yz b))

private def normalCyclesMap (h : HeisenbergBasis b) : (Fin 5 → k) →ₗ[k] Cycles k L 2 where
  toFun := normalCycle b h
  map_add' p q := by
    obtain ⟨hpA, hpB, hpC⟩ := normalCochain_values b p
    obtain ⟨hqA, hqB, hqC⟩ := normalCochain_values b q
    obtain ⟨hrA, hrB, hrC⟩ := normalCochain_values b (p + q)
    apply Subtype.ext
    apply two_ext b
    · change normalCochain b (p + q) (xy b) = (normalCochain b p + normalCochain b q) (xy b)
      simp only [LinearMap.add_apply, hpA, hqA, hrA, add_zero]
    · change normalCochain b (p + q) (xz b) = (normalCochain b p + normalCochain b q) (xz b)
      simp only [LinearMap.add_apply, hpB, hqB, hrB, Pi.add_apply]
      module
    · change normalCochain b (p + q) (yz b) = (normalCochain b p + normalCochain b q) (yz b)
      simp only [LinearMap.add_apply, hpC, hqC, hrC, Pi.add_apply]
      module
  map_smul' r p := by
    obtain ⟨hpA, hpB, hpC⟩ := normalCochain_values b p
    obtain ⟨hrA, hrB, hrC⟩ := normalCochain_values b (r • p)
    apply Subtype.ext
    apply two_ext b
    · change normalCochain b (r • p) (xy b) = (r • normalCochain b p) (xy b)
      simp only [LinearMap.smul_apply, hpA, hrA, smul_zero]
    · change normalCochain b (r • p) (xz b) = (r • normalCochain b p) (xz b)
      simp only [LinearMap.smul_apply, hpB, hrB, Pi.smul_apply, smul_eq_mul]
      module
    · change normalCochain b (r • p) (yz b) = (r • normalCochain b p) (yz b)
      simp only [LinearMap.smul_apply, hpC, hrC, Pi.smul_apply, smul_eq_mul]
      module

private def normalClassMap (h : HeisenbergBasis b) : (Fin 5 → k) →ₗ[k] H2 k L :=
  (boundaries k L 1).mkQ.comp (normalCyclesMap b h)

private theorem normalClassMap_bijective (h : HeisenbergBasis b) :
    Function.Bijective (normalClassMap b h) := by
  constructor
  · intro p q he
    change Submodule.Quotient.mk (normalCycle b h p) =
      Submodule.Quotient.mk (normalCycle b h q) at he
    have hd := (Submodule.Quotient.eq (p := boundaries k L 1)).mp he
    have hxy : (normalCochain b p - normalCochain b q) (xy b) = 0 := by
      simp only [LinearMap.sub_apply, (normalCochain_values b p).1,
        (normalCochain_values b q).1, sub_self]
    have hzero : normalCochain b p - normalCochain b q = 0 := by
      obtain ⟨f, _, hu⟩ := boundaries_two b h 0
      exact (hu _ ⟨hd, hxy⟩).trans (hu 0 ⟨Submodule.zero_mem _, rfl⟩).symm
    have heq := congrArg (parameters b) (sub_eq_zero.mp hzero)
    simpa only [parameters_normal] using heq
  · intro c
    obtain ⟨f, rfl⟩ := (boundaries k L 1).mkQ_surjective c
    obtain ⟨g, ⟨hg, hgf⟩, _⟩ := boundaries_two b h (f.1 (xy b))
    have hgc : d k L 2 g = 0 := by
      obtain ⟨t, rfl⟩ := hg
      exact d_squared 1 t
    let z : Cycles k L 2 := ⟨g, hgc⟩
    let f' := f - z
    have hxy : f'.1 (xy b) = 0 := by
      change f.1 (xy b) - g (xy b) = 0
      rw [hgf, sub_self]
    let p := parameters b f'.1
    have heq : normalCycle b h p = f' :=
      Subtype.ext (normalValues_ext b (normalCochain_values b p) (normalized_cycle_values b h f' hxy))
    refine ⟨p, ?_⟩
    change Submodule.Quotient.mk (normalCycle b h p) = Submodule.Quotient.mk f
    rw [heq, Submodule.Quotient.eq]
    change f - z - f ∈ boundaries k L 1
    have hz : z ∈ boundaries k L 1 := hg
    convert neg_mem hz using 1
    abel

theorem normal_form : NormalFormType := by
  intro k _ _ L _ _ b h
  let e := LinearEquiv.ofBijective (normalClassMap b h) (normalClassMap_bijective b h)
  have hex (p : Fin 5 → k) :
      ∃! f : Cycles k L 2, HasNormalValues b p f.1 ∧ Submodule.Quotient.mk f = e p := by
    refine ⟨normalCycle b h p, ⟨normalCochain_values b p, rfl⟩, ?_⟩
    intro f hf
    exact Subtype.ext (normalValues_ext b hf.1 (normalCochain_values b p))
  refine ⟨e, hex, ?_⟩
  intro c
  obtain ⟨p, rfl⟩ := e.surjective c
  obtain ⟨f, hf, _⟩ := hex p
  refine ⟨f, ⟨⟨p, hf.1⟩, hf.2⟩, ?_⟩
  rintro g ⟨⟨q, hq⟩, hg⟩
  obtain ⟨g', hg', _⟩ := hex q
  have heq : g = g' := Subtype.ext (normalValues_ext b hq hg'.1)
  have hpq : q = p := e.injective (hg'.2.symm.trans (heq ▸ hg))
  exact Subtype.ext (normalValues_ext b (hpq ▸ hq) hf.1)

theorem model_normal_form : ModelNormalFormType := by
  intro k _ _
  obtain ⟨hx, hy, hz⟩ := basis_vectors k
  have hb : HeisenbergBasis (basis k) := by
    unfold HeisenbergBasis
    rw [hx, hy, hz]
    exact ⟨lie_xy k, lie_z_right k _, lie_z_right k _⟩
  obtain ⟨e, hparams, _⟩ := normal_form k (Model k) (basis k) hb
  refine ⟨e, fun p => ?_⟩
  obtain ⟨f, hf, _⟩ := hparams p
  refine ⟨f, normalValues_ext (basis k) hf.1 ?_, hf.2⟩
  change HasNormalValues (basis k) p (phiExterior k (p 0) (p 1) (p 2) (p 3) (p 4))
  unfold HasNormalValues
  rw [hx, hy, hz]
  simp [wedge]

theorem dimensions : DimensionsType := by
  intro k _ _ L _ _ b h
  obtain ⟨e₂, _⟩ := normal_form k L b h
  obtain ⟨e₃, _⟩ := evaluation_three k L b h
  have : Module.Finite k L := Module.Finite.of_basis b
  constructor
  · rw [← e₂.finrank_eq, Module.finrank_eq_card_basis (Pi.basisFun k (Fin 5)), Fintype.card_fin]
  · rw [e₃.finrank_eq]
    have hdim := (k ∙ b 2 : Submodule k L).finrank_quotient_add_finrank
    rw [finrank_span_singleton (b.ne_zero 2), Module.finrank_eq_card_basis b, Fintype.card_fin] at hdim
    omega

end LieNotes.Heisenberg.AdjointCohomology
