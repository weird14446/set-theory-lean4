# ZFC Set Theory in Lean 4 (`set-theory-lean4`)

Lean 4로 형식화한 **체르멜로-프렝켈 집합론 및 선택 공리(ZFC, Zermelo-Fraenkel Set Theory with the Axiom of Choice)** 공리계와 기초 집합론, 명제 논리, 폰 노이만 서수 기반 자연수 집합 체계입니다.

---

## 📌 주요 구성 및 형식화 내용

### 1. 기본 개념 (Primitive Notions)
- **집합 타입 및 소속 관계**: `Set`, `∈`, `∉`
- **부분집합 및 추이성**: `⊆` (`subset`), `subset_trans`
- **유일 존재 한정자**: `∃! x, P x` (`ExistsUnique`)
- **공집합이 아닌 집합 (Nonempty)**: `nonempty`

### 2. 명제 논리: 배타적 논리합 (Propositional Logic: XOR)
- **배타적 논리합 정의**: `p ⊻ q` (`(p ∧ ¬q) ∨ (¬p ∧ q)`)
- **교환법칙**: `p ⊻ q ↔ q ⊻ p`
- **자기 자신과의 XOR**: `p ⊻ p ↔ False`
- **동치 부정과의 동치**: `p ⊻ q ↔ ¬(p ↔ q)`
- **동치 표현 정리**: `p ⊻ q ↔ (p ∨ q) ∧ ¬(p ∧ q)` (자연 연역 및 드 모르간 법칙 기반)

### 3. 공식 ZFC 9대 공리계 (Official ZFC Axioms 1 ~ 9)
1. **외연성 공리 (Axiom of Extensionality)**: `∀ x y, (∀ a, a ∈ x ↔ a ∈ y) ↔ x = y`
2. **분리 공리꼴 (Axiom Schema of Separation / Specification)**: `∀ P x, ∃ y, ∀ a, a ∈ y ↔ (a ∈ x ∧ P a)`
3. **짝의 공리 (Axiom of Unordered Pairs)**: `∀ a b, ∃ x, a ∈ x ∧ b ∈ x`
4. **합집합 공리 (Axiom of Union)**: `∀ x, ∃ U, ∀ a, (∃ b, b ∈ x ∧ a ∈ b) → a ∈ U`
5. **멱집합 공리 (Axiom of Power Set)**: `∀ x, ∃ P, ∀ y, y ⊆ x → y ∈ P`
6. **무한 공리 (Axiom of Infinity)**: `∃ I, (∅ ∈ I) ∧ (∀ x ∈ I, succ x ∈ I)`
7. **정칙성 / 기초 공리 (Axiom of Regularity / Foundation)**: 순환 소속 배제 및 무한 하강 사슬 방지
8. **치환 공리꼴 (Axiom Schema of Replacement)**: 함수적 관계 하에서의 상(image) 집합 존재
9. **선택 공리 (Axiom of Choice)**: 비어있지 않은 집합들의 족에 대한 선택 함수 존재

### 4. 유도된 집합 연산 및 주요 정리 (Derived Operations & Theorems)
- **분리 연산자**: `sep P x` (`{a ∈ x | P a}`)
- **비순서쌍 및 한원소 집합**: `pair a b` (`{a, b}`), `singleton a` (`{a}`)
- **정칙성 공리의 귀결 (순환 소속 배제)**:
  - `x ∉ x` (`no_self_mem`)
  - `m ∈ n → n ∈ m → False` (`no_two_cycle`)
- **합집합, 교집합, 차집합, 멱집합**:
  - 일반 합집합 `⋃ x`, 이항 합집합 `x ∪ y`
  - 교집합 `x ∩ y`, 차집합 `A - B` (`A \ B`), 멱집합 `𝒫 x`
- **대칭차집합 (Symmetric Difference)**:
  - `A ⊕ B = (A - B) ∪ (B - A)`
  - 교환법칙: `A ⊕ B = B ⊕ A`
  - 동치 정리: `A ⊕ B = (A ∪ B) - (A ∩ B)`
  - 명제 논리 XOR과의 대응: `x ∈ A ⊕ B ↔ (x ∈ A) ⊻ (x ∈ B)`
- **쿠라토프스키 순서쌍 및 데카르트 곱 (Cartesian Product)**:
  - 쿠라토프스키 순서쌍: `opair a b` (`⟪a, b⟫ = {{a}, {a, b}}`)
  - 순서쌍 상등 기본 정리: `opair_inj` (`⟪a, b⟫ = ⟪c, d⟫ ↔ a = c ∧ b = d`)
  - 데카르트 곱: `A ⨯ B` (`{ ⟪a, b⟫ | a ∈ A ∧ b ∈ B } ⊆ 𝒫(𝒫(A ∪ B))`)
  - 멱집합 상위 포함 관계: `(A ⨯ B) ⊆ 𝒫(𝒫(A ∪ B))`
  - 원소 판정 동치 정리: `z ∈ A ⨯ B ↔ ∃ a ∈ A, b ∈ B, z = ⟪a, b⟫`
- **함수와 전단사(Bijection) 및 데카르트 곱의 대칭성**:
  - 함수, 단사, 전사, 전단사 및 동형(대등) 관계 정의: `is_function`, `is_injective`, `is_surjective`, `is_bijective`, `X ≅ Y` (`equipotent`)
  - 대칭 사상 (Swap Function): `swap_func A B` ($f(a, b) = (b, a)$)
  - 데카르트 곱의 대칭성 (동형적 교환법칙): `(A ⨯ B) ≅ (B ⨯ A)` (`prod_comm_iso`)
  - **동형(대등) 관계의 동치 관계 정리**:
    - 반사율: `X ≅ X` (`equipotent_refl`, 항등 함수 `id_func`)
    - 대칭율: `X ≅ Y → Y ≅ X` (`equipotent_symm`, 역함수 `inv_func`)
    - 추이율: `X ≅ Y → Y ≅ Z → X ≅ Z` (`equipotent_trans`, 합성 함수 `comp_func`)
    - 동치 관계 종합: `equipotent_is_equivalence`
- **칸토어의 정리 및 기수 대소 관계 (Cantor's Theorem & Cardinal Inequality)**:
  - **전사 함수 부존재 정리**: 임의의 집합 $X$에서 멱집합 $\mathcal{P}(X)$로의 전사 함수는 존재하지 않는다 (`cantor_theorem`, `cantor_theorem_not_surjective`).
  - **대등 부존재 정리**: 임의의 집합 $X$와 멱집합 $\mathcal{P}(X)$는 대등(동형)하지 않다 (`cantor_theorem_not_equipotent`, $X \not\cong \mathcal{P}(X)$).
  - **기수 대소 관계 정의 및 원순서 성질**: `X ≼ Y` (`card_le`), `X ≺ Y` (`card_lt`), 반사율(`card_le_refl`), 추이율(`card_le_trans`), 대등 함의(`equipotent_imp_card_le`).
  - **한원소 집합 단사 매장**: $x \mapsto \{x\}$ (`singleton_func`, `singleton_func_is_injective`), `X ≼ 𝒫 X` (`card_le_powerset`).
  - **엄격한 칸토어 부등식**: `X ≺ 𝒫 X` (`cantor_strict_inequality`, $|X| < |\mathcal{P}(X)|$).
- **불가능성 정리 (러셀의 역설)**:
  - **전체집합(Universal Set)의 부존재 정리**: `¬ ∃ V, ∀ x, x ∈ V`
  - **절대적 여집합의 부존재 정리**: `¬ ∃ C, ∀ x, x ∈ C ↔ x ∉ A` (정칙성 공리 및 러셀의 역설 2가지 방식으로 증명)

### 5. 자연수 집합 및 페아노 공리계 (Von Neumann Naturals & Peano Structure)
- **다음수 연산 (Successor)**: `succ y = y ∪ {y}`
- **공집합(∅) 및 무한 집합(infinite_set)** 추출
- **귀납적 집합 (Inductive Set)**: `is_inductive x := ∅ ∈ x ∧ ∀ a ∈ x, succ a ∈ x`
- **자연수 집합 ($\mathbb{N}_{\mathrm{set}}$)**: 모든 귀납적 집합의 교집합으로 구성
- **페아노 공리 체계 유도**:
  - `∅ ∈ ℕ_set`
  - `∀ n ∈ ℕ_set, succ n ∈ ℕ_set`
  - 자연수 집합 스스로 귀납적 집합임 (`Nat_set_is_inductive`)
  - 다음수의 비공집합성: `succ n ≠ ∅`
  - 다음수의 자기 비일치성: `succ n ≠ n` (`succ_ne_self`)
  - 다음수 함수의 단사성: `succ m = succ n → m = n`
  - 최소 귀납적 집합 성질: `ℕ_set ⊆ X` (임의의 귀납적 집합 `X`에 대해)
  - 수학적 귀납법 원리 (페아노 5번 공리): `nat_induction`
  - 영 또는 다음수 분해 정리: `n = ∅ ∨ ∃ m ∈ ℕ_set, n = succ m` (`nat_zero_or_succ`)
- **데데킨트 무한성 및 힐베르트의 호텔 정리 (Hilbert's Hotel)**:
  - 진부분집합(`A ⊂ B`, `is_proper_subset`) 및 데데킨트 무한 집합(`is_dedekind_infinite`) 정의
  - 양의 자연수 진부분집합: `Nat_pos = ℕ_set - {∅} ⊂ ℕ_set` (`Nat_pos_proper_subset`)
  - 힐베르트의 호텔 정리: `ℕ_set ≅ ℕ_set - {∅}` (`hilbert_hotel`)
  - 자연수 집합의 데데킨트 무한성: `is_dedekind_infinite ℕ_set` (`Nat_set_is_dedekind_infinite`)
- **자연수의 순서 구조, 삼분법(Trichotomy) 및 정렬성(Well-Ordering Principle)**:
  - 따름연산의 순서 보존성: `succ m ∈ succ n ↔ m ∈ n` (`mem_succ_iff_mem_of_nat`)
  - 자연수의 삼분법: `m ∈ n ∨ m = n ∨ n ∈ m` (`nat_trichotomy`)
  - 부분집합과 이하 관계의 일치: `m ⊆ n ↔ (m ∈ n ∨ m = n)` (`nat_subset_iff_mem_or_eq`)
  - 자연수의 정렬성 원리: 공집합이 아닌 모든 부분집합 $S \subseteq \mathbb{N}_{\mathrm{set}}$는 $\in$-최소 원소를 가짐 (`nat_well_ordering`)

### 6. 추이적 집합, 폰 노이만 서수(Ordinals) 및 부랄리-포르티 역설
- **추이적 집합 정의**: `is_transitive X := ∀ y ∈ X, y ⊆ X`
- **합집합 동치 조건**: `is_transitive X ↔ ⋃ X ⊆ X` (`is_transitive_iff_union_all_subset`)
- **공집합 및 따름연산의 추이성**: `empty_is_transitive`, `succ_is_transitive`, `⋃ (succ X) = X` (`union_all_succ_of_is_transitive`)
- **연산에 대한 닫힘 성질**: `inter_is_transitive`, `union_is_transitive`, `union_all_is_transitive`
- **자연수 집합의 추이성**: `nat_is_transitive`, `nat_elements_in_Nat_set`, `Nat_set_is_transitive`
- **폰 노이만 서수 (Von Neumann Ordinals)**:
  - 서수 정의: `is_ordinal α := is_transitive α ∧ ∀ β ∈ α, is_transitive β`
  - 기본 성질: `empty_is_ordinal` ($0$은 서수), `elem_of_ordinal_is_ordinal` (서수의 원소는 서수), `succ_is_ordinal` ($\alpha + 1$은 서수), `ordinal_mem_trans` ($\in$의 추이성)
  - 유한 서수 및 최초의 초한 서수 $\omega$: `nat_is_ordinal`, `Nat_set_is_ordinal`
- **부랄리-포르티 역설 (Burali-Forti Paradox)**:
  - 모든 서수를 원소로 가지는 집합 $\Omega$는 존재하지 않는다 (`burali_forti_paradox`, `¬ ∃ Ω, ∀ α, α ∈ Ω ↔ is_ordinal α`)

### 7. 유리수 코시 수열 동치류로서의 실수($\mathbb{R}$), $\varepsilon$-$\delta$ 미적분학 및 미적분학의 기본 정리 (`RealAnalysis`)
- **유리수 코시 수열 및 동치류로서의 실수 구성**:
  - 유리수 코시 수열 정의: `IsCauchy`, `CauchySeq` ($\forall \varepsilon > 0, \exists N, \forall m, n \ge N, |a_m - a_n| < \varepsilon$)
  - 코시 수열 동치 관계(`CauchyEquiv`) 및 동치 관계 증명: 반사율(`cauchy_equiv_refl`), 대칭율(`cauchy_equiv_symm`), 추이율(`cauchy_equiv_trans`), `CauchySetoid`
  - 동치류로서의 실수 정의: `ℝ := Quotient CauchySetoid`
  - 코시 수열 연산의 잘 정의됨(Well-definedness) 및 동치류 아벨군 성질 증명: `add_is_cauchy`, `addCauchy_congr`, `neg_is_cauchy`, `negCauchy_congr`, `r_add_comm`, `r_add_assoc`, `r_add_zero`, `r_add_left_neg`
- **$\varepsilon$-$\delta$ 논법을 통한 극한, 연속, 미분**:
  - 함수의 극한(`HasLimit f a L`) 및 극한의 유일성(`limit_unique`), 상수·항등·합·차의 극한(`limit_const`, `limit_id`, `limit_add`, `limit_sub`), 조임 정리(`squeeze_theorem`)
  - 점 및 구간에서의 연속성: `ContinuousAt`, `ContinuousOn`, `continuousAt_imp_hasLimit`
  - $\varepsilon$-$\delta$ 미분계수(`HasDerivAt f a L`): 미분계수의 유일성(`hasDerivAt_unique`), 상수·항등·합·차의 미분법(`hasDerivAt_const`, `hasDerivAt_id`, `hasDerivAt_add`, `hasDerivAt_sub`), 미분가능 함수의 연속성(`differentiable_imp_continuousAt`)
- **다르부 적분 (Darboux Integral)**:
  - 분할(`Partition`), 하다르부 합(`lowerDarbouxSum`), 상다르부 합(`upperDarbouxSum`), 리만-다르부 $\varepsilon$-판정법 기반 정적분(`DarbouxIntegral f a b I`)
  - 다르부 적분값의 유일성(`darboux_integral_unique`) 및 상·하다르부 적분 일치 정리(`darboux_lower_eq_upper_of_integrable`)
- **미적분학의 기본 정리 (Fundamental Theorem of Calculus, Part 1 & Part 2)**:
  - **제1정리 (`fundamental_theorem_of_calculus_part1`)**: $f$가 점 $c \in (a, b)$에서 연속일 때 정적분 함수 $F(x) = \int_a^x f(t)\,dt$는 $c$에서 미분가능하며 $F'(c) = f(c)$ (`HasDerivAt F c (f c)`)임을 $\varepsilon$-$\delta$ 논법으로 증명.
  - **제2정리 (`fundamental_theorem_of_calculus_part2`)**: $f$가 $[a, b]$에서 다르부 적분가능하고 $F$가 원시함수(`IsAntiderivativeOn F f a b`)일 때, 부분구간 평균값 정리 부등식(`mvt_subinterval_darboux_bound`)과 리만-다르부 $\varepsilon$-판정법을 결합하여 $\int_a^b f(x)\,dx = F(b) - F(a)$ 증명.
  - **종합 정리 (`fundamental_theorem_of_calculus`)**: 제1정리와 제2정리 통합.

---

## 🛠️ 실행 및 검증 방법

Lean 4 환경에서 `main.lean` 파일을 직접 컴파일하여 모든 증명과 타입 검사를 확인할 수 있습니다.

```bash
lean main.lean
```

오류 없이 종료되면 모든 공리 정의, 연산자 구성 및 정리가 성공적으로 형식화 및 검증된 것입니다.

---

## 📄 라이선스 (License)

이 프로젝트는 [MIT License](LICENSE)에 따라 배포됩니다.