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
- **불가능성 정리 (러셀의 역설)**:
  - **전체집합(Universal Set)의 부존재 정리**: `¬ ∃ V, ∀ x, x ∈ V`
  - **절대적 여집합의 부존재 정리**: `¬ ∃ C, ∀ x, x ∈ C ↔ x ∉ A` (정칙성 공리 및 러셀의 역설 2가지 방식으로 증명)

### 5. 자연수 집합 및 페아노 공리계 (Von Neumann Ordinals & Peano Structure)
- **다음수 연산 (Successor)**: `succ y = y ∪ {y}`
- **공집합(∅) 및 무한 집합(infinite_set)** 추출
- **귀납적 집합 (Inductive Set)**: `is_inductive x := ∅ ∈ x ∧ ∀ a ∈ x, succ a ∈ x`
- **자연수 집합 ($\mathbb{N}_{\mathrm{set}}$)**: 모든 귀납적 집합의 교집합으로 구성
- **페아노 공리 체계 유도**:
  - `∅ ∈ ℕ_set`
  - `∀ n ∈ ℕ_set, succ n ∈ ℕ_set`
  - 자연수 집합 스스로 귀납적 집합임 (`Nat_set_is_inductive`)
  - 다음수의 비공집합성: `succ n ≠ ∅`
  - 다음수 함수의 단사성: `succ m = succ n → m = n`
  - 최소 귀납적 집합 성질: `ℕ_set ⊆ X` (임의의 귀납적 집합 `X`에 대해)
  - 수학적 귀납법 원리 (페아노 5번 공리): `nat_induction` (임의의 술어 `P`에 대해 `P ∅`와 `P n → P (succ n)`로부터 `∀ n ∈ ℕ_set, P n` 유도)

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