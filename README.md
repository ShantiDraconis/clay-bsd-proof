# Birch e Swinnerton-Dyer — prova (Lean 4 / Mathlib)

Depende do enunciado em [`ShantiDraconis/clay-bsd-statement`](https://github.com/ShantiDraconis/clay-bsd-statement),
fixado no commit `09f1c87`. O alvo é `ClayBSD.Conjecture`, sem redefinição.

Estado: sem prova. `OPEN_MATH = true`. Nenhum resultado abaixo prova `ClayBSD.Conjecture`: é um
caso particular (uma curva), um teorema clássico auxiliar (Mordell–Weil) e uma decomposição exata
do enunciado.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms ClayBSDProof.main`
fixado com `#guard_msgs` quando `main` existir.

Toolchain: Lean `v4.36.0-rc2`, Mathlib `8fe7ce4` (ver `lake-manifest.json`).

## Origem do material portado

Os módulos abaixo foram portados do ATK kernel, espelho público
`atk-math-core-public/imports/M-Core/atk-kernel/ATK/` (fontes de `ShantiDraconis/M-Core` no
commit `390e378`, 2026-10-27), adaptados ao Mathlib `8fe7ce4` e ligados ao enunciado fixado. Cada
arquivo cita no cabeçalho o arquivo ATK de origem.

| Módulo | Origem (ATK) |
|---|---|
| `FermatRightTriangle` | `FermatRightTriangle.lean` |
| `CongruentCurve` | `CongruentCurve.lean` |
| `Continuation` | `LigacaoBSD.lean` (parte), `LigacaoBSDTestes.lean` (parte) |
| `RankZeroE32` | `LigacaoBSDTestes.lean` (`curva32_eliptica`, `dois_torcao`, `posto_curva32`) |
| `MellinFold` | `BaseRiemannTeta.lean` (parte abstrata) |
| `AtaqueBSD` | `AtaqueBSD.lean` |
| `HasseE32` | `BaseHasseCurva32.lean` |
| `CoefBoundE32` | `PonteCoefCurva32.lean` |
| `GoodReductionE32` | `BSDTamagawaE32.lean` (`boa_reducao_de_unidade`, `dois_unidade`, `boa_E32`) |
| `LocalFactorsE32` | `PonteFatoresCurva32.lean` |
| `GaussPrimary` | `BaseGaussPrimario.lean` |
| `HeckeCharE32` | `BaseGaussCurva32.lean` |
| `ModularE32` | `PonteModularCurva32.lean` (até `bsd_posto_curva32_completo`) |
| `CaseE32` | novo: liga `PonteModularCurva32` ao enunciado fixado |
| `MordellWeil/ChangeOfVariables` | `MudancaVariaveis.lean` |
| `MordellWeil/Field` | `MordellWeilCorpo.lean` |
| `MordellWeil/SelmerFinite` | `SelmerFinito.lean` |
| `MordellWeil/WeakNumberField` | `MordellWeilNumero.lean` |
| `MordellWeil` | `MordellWeilGeral.lean` + `BSDInvariantes.lean` (`MordellWeilFraco`, `fg_of_fraco`) |
| `RankDecomposition` | reescrita de `Conditional/BSD.lean` sobre o enunciado fixado |

## 1. BSD para `y² = x³ − x` (`ClayBSDProof.CaseE32`)

```lean
abbrev ClayBSDProof.RankZeroE32.E32 : WeierstrassCurve ℚ   -- a₄ = −1, demais 0
instance ClayBSDProof.RankZeroE32.isElliptic_E32 : E32.IsElliptic
theorem ClayBSDProof.CaseE32.statement_E32 : ClayBSD.Statement E32
```

**O que é.** Teorema sobre o enunciado fixado, sem hipóteses: existe `L` inteira com
`ClayBSD.IsContinuation E32 L` (inclusive a somabilidade absoluta da série em `Re s > 3/2`) e
`analyticOrderAt L 1 = ClayBSD.algebraicRank E32 = 0`. Cadeia:

* `E32(ℚ) = {O, (0,0), (±1,0)}` pela descida de Fermat (`x⁴ − y⁴ ≠ z²`, `1` não é congruente),
  logo `rank_ℤ E32(ℚ) = 0` (`RankZeroE32.algebraicRank_E32`);
* os coeficientes de `WeierstrassCurve.LFunction` (Mathlib) para `E32` são desdobrados primo a
  primo (`LocalFactorsE32.fatoresPadrao`: redução aditiva em 2, boa fora de 2, contagem de pontos
  sobre `𝔽_p`), dão `|aₙ| ≤ n` (cota de Hasse, `HasseE32`) e coincidem com o caráter de Hecke de
  `ℚ(i)`: `aₙ = Σ_{α primário, N α = n} α` (`HeckeCharE32.coef_gauss`);
* daí a equação funcional de peso 2 e sinal `+1`, `g(1/x) = x² g(x)`, via os núcleos de Hurwitz
  da Mathlib (`ModularE32.ponteModular_curva32`), a continuação inteira
  `Lcurva32 = c^s Λ(s)/Γ(s)` (`ModularE32.existe_continuacao`) e a convergência absoluta em
  `Re s > 3/2` pela soma de Eisenstein (`ModularE32.lseriesSummable_curva32`);
* `L(E32, 1) = 2c Σ aₙ e^{−cn}/(cn)` com parte real `> 0` (`AtaqueBSD.L1_ne_zero`), logo ordem `0`.

**O que não é.** Não é `ClayBSD.Conjecture` (que quantifica sobre todas as curvas). É o caso de
posto analítico 0 de uma curva com multiplicação complexa, coberto classicamente por
**Coates–Wiles (1977)**; para esta curva, o posto 0 já era de Fermat. Nada trata posto analítico
`≥ 1`. Também provado: `CaseE32.continuation_one_ne_zero` (toda continuação tem `L(1) ≠ 0`).

**Axiomas.** `statement_E32`: `[propext, Classical.choice, Quot.sound]`.

## 2. Teorema de Mordell–Weil sobre `ℚ` (`ClayBSDProof.MordellWeil`)

```lean
theorem ClayBSDProof.MordellWeil.mordellWeilFraco : MordellWeilFraco
  -- ∀ E : WeierstrassCurve ℚ, E.IsElliptic → (nsmulAddMonoidHom (α := E.toAffine.Point) 2).range.FiniteIndex
theorem ClayBSDProof.MordellWeil.mordellWeil_fg (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    AddGroup.FG E.toAffine.Point
theorem ClayBSDProof.MordellWeil.algebraicRank_lt_aleph0 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ClayBSD.algebraicRank E < Cardinal.aleph0
```

**O que é.** Teorema de Mordell–Weil (1922/1928) para toda curva elíptica sobre `ℚ`, sem
hipóteses; não está no Mathlib. Prova: completar o quadrado; corpo de decomposição `L` da cúbica;
2-descida sobre `L` com finitude do grupo de Selmer `L⟮S, 2⟯` (número de classes e unidades de
Dirichlet do Mathlib); descida de Galois para `ℚ`; e a descida por alturas do Mathlib
(`AddCommGroup.fg_of_descent'`, Northcott). Consequência para o enunciado fixado: o posto
`ClayBSD.algebraicRank E` é sempre finito.

**O que não é.** Não diz nada sobre `L(E, s)` nem sobre BSD.

**Axiomas.** `[propext, Classical.choice, Quot.sound]`.

## 3. Decomposição do enunciado e `RankOpen` (`ClayBSDProof.RankDecomposition`)

```lean
def ContinuationExists : Prop  -- ∀ E [E.IsElliptic], ∃ L, ClayBSD.IsContinuation E L
def LowRankTheorem : Prop      -- ord ≤ 1 ⇒ ord = posto  (para toda continuação)
def RankOpen : Prop            -- ord ≥ 2 ⇒ ord = posto  (para toda continuação)
theorem conjecture_iff :
    ClayBSD.Conjecture ↔ ContinuationExists ∧ LowRankTheorem ∧ RankOpen
theorem conjecture_iff_rankOpen (hC : ContinuationExists) (hLow : LowRankTheorem) :
    ClayBSD.Conjecture ↔ RankOpen
```

**O que é.** `conjecture_iff` é uma equivalência provada sem hipóteses. `conjecture_iff_rankOpen` é
**condicional** a dois resultados externos publicados, escritos como `Prop` com referências nas
docstrings: `ContinuationExists` (modularidade: Wiles 1995, Taylor–Wiles 1995,
Breuil–Conrad–Diamond–Taylor 2001; cota de Hasse) e `LowRankTheorem` (Gross–Zagier 1986,
Kolyvagin 1990, com Bump–Friedberg–Hoffstein 1990 e Murty–Murty 1991). Módulo esses resultados, o
que falta para o enunciado fixado é exatamente `RankOpen`.

**O que não é.** `RankOpen` é **aberto** e não é provado aqui. `ContinuationExists` e
`LowRankTheorem` não estão no Mathlib nem são provados aqui; a sua fidelidade aos teoremas
publicados supõe que `WeierstrassCurve.LFunction` seja a função L clássica (a mesma suposição do
enunciado fixado).

**Axiomas.** `[propext, Classical.choice, Quot.sound]`.

## Não portado

* `ATK/BSDRefinada.lean`, `ATK/BSDTamagawaE32.lean` (Tamagawa), `ATK/BSDInvariantes.lean` (altura
  canônica, regulador, período): pertencem à fórmula refinada, que não faz parte do enunciado
  fixado.
* `ATK/L4Base.lean`, `ATK/LigacaoBSD.lean` (`ClayBSD`, `BSDModel`, `posto_iff`): reformulações do
  enunciado do Clay no ATK; aqui só se usa `ClayBSD.Statement`.
* `ATK/BaseRiemannXi.lean` e a parte de `BaseRiemannTeta.lean` sobre `ζ`: não usadas.

## Auditoria

`ClayBSDProof/Audit.lean` (importado por último): um `#guard_msgs in #print axioms` por declaração
pública nova (400), com a saída real do Lean. Só aparecem `propext`, `Classical.choice` e
`Quot.sound` (ou subconjuntos).

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.
