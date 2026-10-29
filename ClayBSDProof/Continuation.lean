import ClayBSD
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.FieldTheory.Cardinality

/-!
# Continuação de `L(E, s)` e o coeficiente `a₁ = 1`

Portado do ATK kernel (espelho público `atk-math-core-public`, `imports/M-Core/atk-kernel`,
M-Core commit `390e378`): `ATK/LigacaoBSD.lean` (`Continuacao`, `postoMW`, `continuacao_unica`) e
`ATK/LigacaoBSDTestes.lean` (`fator_multiplicativo`, `LFunction_um`, `coef`, `coef_um`).
Não portados: o modelo paramétrico `BSDModel` e as reformulações do enunciado do Clay do ATK
(este repositório usa só o enunciado fixado `ClayBSD.Statement`).

* `Continuacao E F`: `F` inteira e igual a `E.LSeries` em `Re s > 3/2` (sem a cláusula de
  somabilidade do enunciado fixado);
* `isContinuation_iff`: `ClayBSD.IsContinuation E F` é `Continuacao E F` mais a somabilidade
  absoluta da série em `Re s > 3/2`;
* `postoMW E = (Module.rank ℤ E(ℚ)).toENat`, e `algebraicRank_eq_zero_iff`;
* `LFunction_um`: o primeiro coeficiente do produto de Euler da Mathlib é `1`.

Nada aqui prova BSD.
-/

open WeierstrassCurve Complex

namespace ClayBSDProof.Continuation

/-- `F` continua a série L de `E`: é inteira e coincide com `L(E, s)` em `Re s > 3/2`. -/
def Continuacao (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s

/-- Posto de Mordell–Weil de `E(ℚ)`, em `ℕ∞` (`⊤` se não fosse finito). -/
noncomputable def postoMW (E : WeierstrassCurve ℚ) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℤ E.toAffine.Point)

/-- **A continuação é única**: duas funções inteiras que coincidem em `Re s > 3/2` são iguais. -/
theorem continuacao_unica {E : WeierstrassCurve ℚ} {F G : ℂ → ℂ} (hF : Continuacao E F)
    (hG : Continuacao E G) : F = G := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.1.analyticAt z
  have hGa : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.1.analyticAt z
  refine hFa.eq_of_eventuallyEq hGa (z₀ := 2) ?_
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
  filter_upwards [hopen.mem_nhds hmem] with s hs
  rw [hF.2 s hs, hG.2 s hs]

/-- Coeficientes `aₙ` de `L(E, s)`, em `ℂ`. -/
noncomputable def coef (W : WeierstrassCurve ℚ) : ℕ → ℂ := fun n => (W.LFunction n : ℂ)

theorem lseries_coef (W : WeierstrassCurve ℚ) (s : ℂ) : W.LSeries s = LSeries (coef W) s := rfl

/-- **Ligação com o enunciado fixado**: `ClayBSD.IsContinuation` é `Continuacao` mais a
somabilidade absoluta da série L em `Re s > 3/2`. -/
theorem isContinuation_iff (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) :
    ClayBSD.IsContinuation E F ↔
      Continuacao E F ∧ ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable (coef E) s := by
  constructor
  · rintro ⟨hd, h⟩
    exact ⟨⟨hd, fun s hs => (h s hs).2⟩, fun s hs => (h s hs).1⟩
  · rintro ⟨⟨hd, h⟩, hs⟩
    exact ⟨hd, fun s hs' => ⟨hs s hs', h s hs'⟩⟩

/-- O posto do enunciado fixado é `0` exatamente quando `postoMW` é `0`. -/
theorem algebraicRank_eq_zero_iff (E : WeierstrassCurve ℚ) :
    ClayBSD.algebraicRank E = 0 ↔ postoMW E = 0 := by
  unfold ClayBSD.algebraicRank ClayBSD.MordellWeil postoMW
  rw [Cardinal.toENat_eq_zero]

/-! ## `a₁ = 1` -/

/-- Cada fator de Euler local da Mathlib é multiplicativo. -/
theorem fator_multiplicativo (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K) :
    (W.localEulerFactor R).IsMultiplicative := by
  have hc : (W.localPowerSeries R).constantCoeff = 1 := by
    simp [WeierstrassCurve.localPowerSeries, PowerSeries.constantCoeff_invOfUnit]
  unfold WeierstrassCurve.localEulerFactor
  by_cases hq : IsPrimePow (Nat.card (IsLocalRing.ResidueField R))
  · exact ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow _ hq _ hc
  · have h0 : Nat.card (IsLocalRing.ResidueField R) = 0 := by
      by_contra hne
      have : Finite (IsLocalRing.ResidueField R) := Nat.finite_of_card_ne_zero hne
      have := Fintype.ofFinite (IsLocalRing.ResidueField R)
      exact hq (by rw [Nat.card_eq_fintype_card]; exact Fintype.isPrimePow_card_of_field)
    rw [h0]
    have h1 : ArithmeticFunction.ofPowerSeries 0 (W.localPowerSeries R) = 1 := by
      ext n
      simp [ArithmeticFunction.ofPowerSeries, hc]
    rw [h1]
    exact ArithmeticFunction.isMultiplicative_one

/-- `a₁ = 1`: o primeiro coeficiente de `L(E, s)`. -/
theorem LFunction_um (W : WeierstrassCurve ℚ) : W.LFunction 1 = 1 := by
  have key : W.LFunction.IsMultiplicative := by
    unfold WeierstrassCurve.LFunction
    exact ArithmeticFunction.isMultiplicative_eulerProduct _ fun _ => fator_multiplicativo _ _
  exact key.map_one

theorem coef_um (W : WeierstrassCurve ℚ) : coef W 1 = 1 := by
  simp [coef, LFunction_um]

end ClayBSDProof.Continuation
