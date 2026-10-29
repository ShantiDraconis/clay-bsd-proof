import ClayBSDProof.MordellWeil.WeakNumberField
import ClayBSDProof.MordellWeil.ChangeOfVariables
import ClayBSDProof.Continuation
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Northcott
import Mathlib.GroupTheory.Descent
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Teorema de Mordell–Weil para toda curva elíptica sobre `ℚ`

Portado do ATK kernel (espelho público, M-Core commit `390e378`), `ATK/MordellWeilGeral.lean`, com
`MordellWeilFraco`, `fg_of_fraco` e `mordellWeil_of_fraco` de `ATK/BSDInvariantes.lean` (o resto
de `BSDInvariantes` — altura canônica, regulador, período — não foi portado).

Prova **`MordellWeilFraco`** (`mordellWeilFraco`): para toda curva elíptica `E/ℚ`, `E(ℚ)/2E(ℚ)`
é finito; e daí, pela descida da Mathlib com a altura ingênua (`AddCommGroup.fg_of_descent'`,
lei do paralelogramo aproximada e Northcott), **`mordellWeil_fg`**: `E(ℚ)` é finitamente gerado,
e **`algebraicRank_lt_aleph0`**: o posto do enunciado fixado (`ClayBSD.algebraicRank`) é finito.
O teorema de Mordell–Weil não está na Mathlib. Não é BSD.

Roteiro:

1. **descida de Galois abstrata** (`descida`): se `ι : A → B` é injetiva, um grupo finito `G` age em
   `B` fixando `ι(A)` e com pontos fixos `ι(A)`, `B[2]` é finito e `B/2B` é finito, então `A/2A` é
   finito — pelos cociclos `σ ↦ σQ − Q ∈ B[2]` para `2Q = ι(P)`;
2. **completar o quadrado** (`ClayBSDProof.MordellWeil.ChangeOfVariables`): basta `a₁ = a₃ = 0`;
3. **o corpo de decomposição** `L` da cúbica `x³ + a₂x² + a₄x + a₆` (`raizes_cubica`): é um corpo de
   números galoisiano, e sobre `L` a curva é `y² = (x − e₁)(x − e₂)(x − e₃)` com `eᵢ` distintos
   (`Δ ≠ 0`), logo `E(L)/2E(L)` é finito (`ClayBSDProof.MordellWeil.WeakNumberField.fraco_numero`);
4. a ação de `Gal(L/ℚ)` nos pontos (`Point.map` da Mathlib) e os pontos fixos racionais
   (`IsGalois.mem_bot_iff_fixed`).
-/

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace ClayBSDProof.MordellWeil

/-! ## Descida de Galois abstrata -/

section Descida

variable {A B G : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **Descida**: `A/2A` é finito a partir de `B/2B` finito, via uma ação finita com pontos fixos
`ι(A)` e `B[2]` finito. -/
theorem descida (ι : A →+ B) (hι : Function.Injective ι) [Finite G] (act : G → B →+ B)
    (hfix : ∀ b : B, (∀ g, act g b = b) → b ∈ Set.range ι)
    (hιfix : ∀ a g, act g (ι a) = ι a)
    (htors : {b : B | b + b = 0}.Finite)
    (hB : (nsmulAddMonoidHom (α := B) 2).range.FiniteIndex) :
    (nsmulAddMonoidHom (α := A) 2).range.FiniteIndex := by
  classical
  set B2 := (nsmulAddMonoidHom (α := B) 2).range with hB2
  set A2 := (nsmulAddMonoidHom (α := A) 2).range with hA2
  set π : A →+ B ⧸ B2 := (QuotientAddGroup.mk' B2).comp ι with hπ
  have : Finite (B ⧸ B2) := inferInstance
  have hA1 : Finite (A ⧸ π.ker) :=
    Finite.of_injective _ (QuotientAddGroup.kerLift_injective π)
  have memK : ∀ d, d ∈ π.ker → ∃ c : B, c + c = ι d := by
    intro d hd
    rw [AddMonoidHom.mem_ker, hπ, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, hB2, AddMonoidHom.mem_range] at hd
    obtain ⟨c, hc⟩ := hd
    exact ⟨c, by rw [← two_nsmul]; exact hc⟩
  let s : B → B := fun b => if h : ∃ c : B, c + c = b then h.choose else 0
  have hs : ∀ d, d ∈ π.ker → s (ι d) + s (ι d) = ι d := by
    intro d hd
    have h := memK d hd
    simp only [s, h, dite_true]
    exact h.choose_spec
  have htv : ∀ d, d ∈ π.ker → ∀ g,
      act g (s (ι d)) - s (ι d) ∈ {b : B | b + b = 0} := by
    intro d hd g
    show act g (s (ι d)) - s (ι d) + (act g (s (ι d)) - s (ι d)) = 0
    have h1 : act g (s (ι d)) + act g (s (ι d)) = ι d := by
      rw [← map_add, hs d hd, hιfix]
    have h2 := hs d hd
    calc act g (s (ι d)) - s (ι d) + (act g (s (ι d)) - s (ι d))
        = (act g (s (ι d)) + act g (s (ι d))) - (s (ι d) + s (ι d)) := by abel
      _ = 0 := by rw [h1, h2, sub_self]
  let r : A ⧸ π.ker → A := fun q => q.out
  have hr : ∀ a : A, a - r (QuotientAddGroup.mk a) ∈ π.ker := by
    intro a
    have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk a : A ⧸ π.ker))
    have he : a - r (QuotientAddGroup.mk a) = -(QuotientAddGroup.mk a : A ⧸ π.ker).out + a := by
      simp only [r]; abel
    rw [he]
    exact h
  let T := {b : B | b + b = 0}
  have : Finite T := htors.to_subtype
  let Φ : A → (A ⧸ π.ker) × (G → T) := fun a =>
    (QuotientAddGroup.mk a, fun g => ⟨act g (s (ι (a - r (QuotientAddGroup.mk a)))) -
      s (ι (a - r (QuotientAddGroup.mk a))), htv _ (hr a) g⟩)
  have key : ∀ a a', Φ a = Φ a' → a - a' ∈ A2 := by
    intro a a' h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    set d := a - r (QuotientAddGroup.mk a) with hd
    set d' := a' - r (QuotientAddGroup.mk a') with hd'
    have hdd : a - a' = d - d' := by rw [hd, hd', h1]; abel
    set Q := s (ι d)
    set Q' := s (ι d')
    have hg : ∀ g, act g (Q - Q') = Q - Q' := by
      intro g
      have := congrArg Subtype.val (congrFun h2 g)
      simp only at this
      rw [map_sub]
      calc act g Q - act g Q' = (act g Q - Q) - (act g Q' - Q') + (Q - Q') := by abel
        _ = Q - Q' := by rw [this, sub_self, zero_add]
    obtain ⟨t, ht⟩ := hfix _ hg
    have hQ := hs d (hr a)
    have hQ' := hs d' (hr a')
    have : d - d' = t + t := hι (by
      rw [map_sub, map_add, ht, ← hQ, ← hQ']
      abel)
    rw [hdd, this, hA2, AddMonoidHom.mem_range]
    exact ⟨t, by rw [nsmulAddMonoidHom_apply, two_nsmul]⟩
  have hfinQ : Finite (A ⧸ A2) := by
    refine Finite.of_injective (fun q : A ⧸ A2 => Φ q.out) ?_
    intro q q' h
    have hk := key _ _ h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
    have he : -q.out + q'.out = -(q.out - q'.out) := by abel
    rw [he]
    exact A2.neg_mem hk
  exact AddSubgroup.finiteIndex_of_finite_quotient

end Descida

/-! ## O corpo de decomposição da cúbica -/

section Cubica

variable (W : WeierstrassCurve ℚ)

/-- A cúbica `x³ + a₂x² + a₄x + a₆`. -/
noncomputable def cubica : ℚ[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

theorem cubica_monic : (cubica W).Monic := by
  unfold cubica
  monicity!

theorem cubica_natDegree : (cubica W).natDegree = 3 := by
  unfold cubica
  compute_degree!

theorem eval_cubica {K : Type*} [Field K] [Algebra ℚ K] (x : K) :
    eval x ((cubica W).map (algebraMap ℚ K)) = x ^ 3 + algebraMap ℚ K W.a₂ * x ^ 2 +
      algebraMap ℚ K W.a₄ * x + algebraMap ℚ K W.a₆ := by
  simp [cubica]

/-- O corpo de decomposição `L` da cúbica. -/
abbrev Lc := (cubica W).SplittingField

/-- **A cúbica se decompõe em `L`.** -/
theorem raizes_cubica : ∃ r₁ r₂ r₃ : Lc W, ∀ x : Lc W,
    x ^ 3 + algebraMap ℚ (Lc W) W.a₂ * x ^ 2 + algebraMap ℚ (Lc W) W.a₄ * x +
      algebraMap ℚ (Lc W) W.a₆ = (x - r₁) * (x - r₂) * (x - r₃) := by
  set p := (cubica W).map (algebraMap ℚ (Lc W)) with hp
  have hsplit : p.Splits := SplittingField.splits _
  have hmon : p.Monic := (cubica_monic W).map _
  have hdeg : p.natDegree = 3 := by
    rw [hp, natDegree_map, cubica_natDegree]
  have hcard : Multiset.card p.roots = 3 := by rw [← hsplit.natDegree_eq_card_roots, hdeg]
  obtain ⟨r₁, r₂, r₃, hr⟩ := Multiset.card_eq_three.mp hcard
  refine ⟨r₁, r₂, r₃, fun x => ?_⟩
  have h := hsplit.eval_eq_prod_roots_of_monic hmon x
  rw [hr] at h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
    Multiset.prod_singleton] at h
  rw [← mul_assoc] at h
  rw [← h, hp, eval_cubica]

/-- **Viète** para a cúbica decomposta. -/
theorem vieta {F : Type*} [Field F] [NeZero (2 : F)] {A₂ A₄ A₆ r₁ r₂ r₃ : F}
    (h : ∀ x : F, x ^ 3 + A₂ * x ^ 2 + A₄ * x + A₆ = (x - r₁) * (x - r₂) * (x - r₃)) :
    A₂ = -(r₁ + r₂ + r₃) ∧ A₄ = r₁ * r₂ + r₁ * r₃ + r₂ * r₃ ∧ A₆ = -(r₁ * r₂ * r₃) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have h2' : (2 : F) ≠ 0 := NeZero.ne 2
  have e6 : A₆ = -(r₁ * r₂ * r₃) := by linear_combination h0
  have hs : 2 * (A₂ + (r₁ + r₂ + r₃)) = 0 := by linear_combination h1 + h2 - 2 * h0
  have hd : 2 * (A₄ - (r₁ * r₂ + r₁ * r₃ + r₂ * r₃)) = 0 := by linear_combination h1 - h2
  refine ⟨?_, ?_, e6⟩
  · have := (mul_eq_zero.mp hs).resolve_left h2'
    linear_combination this
  · have := (mul_eq_zero.mp hd).resolve_left h2'
    linear_combination this

variable [W.IsElliptic]

/-- **As raízes da cúbica em `L`** (distintas, pois `Δ ≠ 0`) e `E/L = y² = (x − e₁)(x − e₂)(x − e₃)`
quando `a₁ = a₃ = 0`. -/
theorem existe_raizes (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) :
    ∃ R : ClayBSDProof.MordellWeil.Field.Raizes (Lc W),
      W.baseChange (Lc W) = ClayBSDProof.MordellWeil.Field.curva R := by
  obtain ⟨r₁, r₂, r₃, hr⟩ := raizes_cubica W
  obtain ⟨e2, e4, e6⟩ := vieta hr
  have hΔ : algebraMap ℚ (Lc W) W.Δ = 16 * ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, ha1, ha3, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat,
      map_zero, e2, e4, e6]
    ring
  have hΔ0 : algebraMap ℚ (Lc W) W.Δ ≠ 0 :=
    (map_ne_zero (algebraMap ℚ (Lc W))).mpr W.isUnit_Δ.ne_zero
  rw [hΔ] at hΔ0
  have h12 : r₁ ≠ r₂ := by
    intro h; apply hΔ0; rw [h]; ring
  have h13 : r₁ ≠ r₃ := by
    intro h; apply hΔ0; rw [h]; ring
  have h23 : r₂ ≠ r₃ := by
    intro h; apply hΔ0; rw [h]; ring
  refine ⟨⟨r₁, r₂, r₃, h12, h13, h23⟩, ?_⟩
  ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map, ClayBSDProof.MordellWeil.Field.curva,
    ha1, ha3, e2, e4, e6]

end Cubica

/-! ## Mordell–Weil fraco para `a₁ = a₃ = 0` -/

section Fraco

variable (W : WeierstrassCurve ℚ)

instance numberField_Lc : NumberField (Lc W) := NumberField.of_module_finite ℚ _

instance isGalois_Lc : IsGalois ℚ (Lc W) := ⟨⟩

/-- **Pontos fixos por Galois são racionais.** -/
theorem fixos_racionais [DecidableEq (Lc W)] (b : (W.baseChange (Lc W)).toAffine.Point)
    (hb : ∀ σ : (Lc W) ≃ₐ[ℚ] (Lc W), Point.map (W' := W) (σ : (Lc W) →ₐ[ℚ] (Lc W)) b = b) :
    b ∈ Set.range (Point.baseChange (W' := W) ℚ (Lc W)) := by
  cases b with
  | zero => exact ⟨0, rfl⟩
  | some x y h =>
    have hσ : ∀ σ : (Lc W) ≃ₐ[ℚ] (Lc W), σ x = x ∧ σ y = y := by
      intro σ
      have := hb σ
      rw [Point.map_some, Point.some.injEq] at this
      exact this
    have hx : x ∈ (⊥ : IntermediateField ℚ (Lc W)) :=
      (IsGalois.mem_bot_iff_fixed x).mpr fun σ => (hσ σ).1
    have hy : y ∈ (⊥ : IntermediateField ℚ (Lc W)) :=
      (IsGalois.mem_bot_iff_fixed y).mpr fun σ => (hσ σ).2
    obtain ⟨x₀, rfl⟩ := IntermediateField.mem_bot.mp hx
    obtain ⟨y₀, rfl⟩ := IntermediateField.mem_bot.mp hy
    have h₀ : (WeierstrassCurve.Affine.baseChange W ℚ).Nonsingular x₀ y₀ :=
      ((WeierstrassCurve.Affine.baseChange W ℚ).baseChange_nonsingular
        (f := Algebra.ofId ℚ (Lc W)) (Algebra.ofId ℚ (Lc W)).injective x₀ y₀).mp h
    exact ⟨.some x₀ y₀ h₀, rfl⟩

variable [W.IsElliptic]

/-- **Mordell–Weil fraco** para curvas com `a₁ = a₃ = 0`. -/
theorem fraco_a1a3 (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex := by
  classical
  obtain ⟨R, hW⟩ := existe_raizes W ha1 ha3
  have hB : (nsmulAddMonoidHom (α := (W.baseChange (Lc W)).toAffine.Point) 2).range.FiniteIndex := by
    rw [hW]
    exact ClayBSDProof.MordellWeil.WeakNumberField.fraco_numero R
  have htors : {b : (W.baseChange (Lc W)).toAffine.Point | b + b = 0}.Finite := by
    rw [hW]
    exact ClayBSDProof.MordellWeil.Field.finito_dois_torcao (R := R)
  exact descida (G := (Lc W) ≃ₐ[ℚ] (Lc W)) (Point.baseChange (W' := W) ℚ (Lc W))
    (Point.map_injective _)
    (fun σ => Point.map (W' := W) (σ : (Lc W) →ₐ[ℚ] (Lc W)))
    (fixos_racionais W)
    (fun a σ => Point.map_baseChange (W' := W) (F := ℚ) (K := Lc W) (L := Lc W)
      (σ : (Lc W) →ₐ[ℚ] (Lc W)) a) htors hB

end Fraco

/-! ## Mordell–Weil para toda curva elíptica sobre `ℚ` -/

/-- O teorema de Mordell–Weil **fraco**: `E(ℚ)/2E(ℚ)` é finito. -/
def MordellWeilFraco : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
    (nsmulAddMonoidHom (α := E.toAffine.Point) 2).range.FiniteIndex

/-- **Descida**: se `E(ℚ)/2E(ℚ)` é finito, `E(ℚ)` é finitamente gerado (`AddCommGroup.fg_of_descent'`
da Mathlib, com a altura ingênua: não negativa, lei do paralelogramo aproximada e Northcott). -/
theorem fg_of_fraco (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : (nsmulAddMonoidHom (α := E.toAffine.Point) 2).range.FiniteIndex) :
    AddGroup.FG E.toAffine.Point := by
  classical
  obtain ⟨C, hC⟩ := WeierstrassCurve.Affine.approx_parallelogram_law E.toAffine
  exact AddCommGroup.fg_of_descent' (h := WeierstrassCurve.Affine.Point.naiveHeight) h
    (fun x => Height.logHeight_nonneg _) hC

/-- **Teorema de Mordell–Weil fraco**: para toda curva elíptica `E/ℚ`, `E(ℚ)/2E(ℚ)` é finito. -/
theorem mordellWeilFraco : MordellWeilFraco := by
  intro E hE
  exact ClayBSDProof.MordellWeil.ChangeOfVariables.fraco_de_normal E
    (fraco_a1a3 (ClayBSDProof.MordellWeil.ChangeOfVariables.normal E) rfl rfl)

/-- **Teorema de Mordell–Weil**: `E(ℚ)` é finitamente gerado para toda curva elíptica `E/ℚ`. -/
theorem mordellWeil_fg (E : WeierstrassCurve ℚ) [E.IsElliptic] : AddGroup.FG E.toAffine.Point :=
  fg_of_fraco E (mordellWeilFraco E inferInstance)

/-- O posto do enunciado fixado é finito: `ClayBSD.algebraicRank E < ℵ₀`. -/
theorem algebraicRank_lt_aleph0 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ClayBSD.algebraicRank E < Cardinal.aleph0 := by
  have : Module.Finite ℤ E.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr (mordellWeil_fg E)
  exact Module.rank_lt_aleph0 ℤ _

/-- `postoMW E ≠ ⊤` para toda curva elíptica `E/ℚ`. -/
theorem postoMW_ne_top (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ClayBSDProof.Continuation.postoMW E ≠ ⊤ := by
  unfold ClayBSDProof.Continuation.postoMW
  rw [Ne, Cardinal.toENat_eq_top, not_le]
  exact algebraicRank_lt_aleph0 E

end ClayBSDProof.MordellWeil
