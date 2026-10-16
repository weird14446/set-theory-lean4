# 데카르트 곱
집합 $A,B$가 주어졌을 때, 짝공리에 의해 집합 $\{A,B\}$가 존재한다.
그리고 합집합 공리에 의해 집합 $A\cup B$가 존재한다. 여기서 멱집합 공리를 두 번 취하여, $\mathcal P(\mathcal P(A\cup B))$가 존재한다. 분류 공리꼴에 의하여 다음과 같은 집합이 존재한다.
$$
A\times B=\{\{\{a\},\{a,b\}\}|a\in A\land b\in B\}\sub\mathcal P(\mathcal P(A\cup B))
$$

## 데카르트 곱의 대칭성 (동형적 교환성, Symmetry up to Isomorphism)
일반적으로 집합의 상등 관점에서는 $A\times B \neq B\times A$이지만, 임의의 두 집합 $A,B$에 대하여 두 데카르트 곱 $A\times B$와 $B\times A$ 사이에는 자연스러운 전단사 함수(일대일 대응)가 존재하여 서로 동형(대등)하다.
$$
A\times B\cong B\times A
$$
Proof:

두 집합 $A,B$가 주어졌을 때, 데카르트 곱을 통해 두 집합 $A\times B$와 $B\times A$를 구성할 수 있다. 여기서 다음과 같은 함수를 정의하자.
$$
f(a,b)=(b,a)
$$
(단, 여기서 $a$와 $b$는 각각 $A$와 $B$의 원소다.)

1. $f$는 단사적이다.

$f(a,b)=f(x,y)$를 가정하자. 그렇다면 $(b,a)=(y,x)$이다. 자명하게 $b=y$이고 $a=x$이므로, $(a,b)=(x,y)$ 또한 성립한다.

2. $f$는 전사적이다.

자명하다.

## 동형(대등) 관계의 동치 관계 (Equivalence Relation)
두 집합 $X, Y$ 사이에 전단사 함수가 존재할 때 두 집합이 동형(대등)하다고 하며, 이를 $X \cong Y$로 표기한다. 동형 관계 $\cong$는 다음 3가지 조건을 만족하므로 동치 관계(Equivalence Relation)이다.

1. **반사율 (Reflexivity)**: 임의의 집합 $X$에 대하여 $X \cong X$이다.
   - 항등 함수 $\operatorname{id}_X(x) = x$는 $X$에서 $X$로의 전단사 함수이다.
2. **대칭율 (Symmetry)**: $X \cong Y$이면 $Y \cong X$이다.
   - $f : X \to Y$가 전단사 함수이면, 그 역함수 $f^{-1} : Y \to X$ 또한 전단사 함수이다.
3. **추이율 (Transitivity)**: $X \cong Y$이고 $Y \cong Z$이면 $X \cong Z$이다.
   - $f : X \to Y$와 $g : Y \to Z$가 전단사 함수이면, 두 함수의 합성 $g \circ f : X \to Z$ 또한 전단사 함수이다.

---

# 칸토어의 정리 (Cantor's Theorem)

임의의 집합 $X$에 대하여, $X$에서 그 멱집합 $\mathcal{P}(X)$로 가는 전사 함수는 존재하지 않는다.
따라서 임의의 집합 $X$는 그 멱집합 $\mathcal{P}(X)$와 대등하지 않다.
$$
X \not\cong \mathcal{P}(X) \quad (|X| < |\mathcal{P}(X)|)
$$

### Proof:
1. $F$가 $X$에서 $\mathcal{P}(X)$로 가는 전사 함수(Surjective function)라고 가정하자.
2. 다음과 같은 대각선 논법 집합 $D$를 정의하자:
   $$
   D = \{ x \in X \mid x \notin F(x) \} \subseteq X
   $$
   분리 공리(Axiom of Separation)에 의해 집합 $D$가 존재하며, $D \subseteq X$이므로 멱집합 공리에 의해 $D \in \mathcal{P}(X)$이다.
3. $F$가 전사 함수이므로, $F(d) = D$를 만족하는 원소 $d \in X$가 존재해야 한다.
4. 이제 $d \in D$인지 여부를 판정한다:
   - 만약 $d \in D$라면, $D$의 정의에 의해 $d \notin F(d) = D$가 되어 모순이다.
   - 만약 $d \notin D$라면, $d \notin F(d)$이므로 $D$의 조건을 만족하여 $d \in D$가 되어 모순이다.
5. 따라서 $d \in D \iff d \notin D$라는 논리적 모순이 발생하므로, 전사 함수 $F$는 존재할 수 없다.
6. 전단사 함수는 전사 함수이어야 하므로 전단사 함수 역시 존재할 수 없으며, $X \not\cong \mathcal{P}(X)$이다.

### 수학적 의의:
- 무한 집합이라도 모두 같은 크기를 가지는 것이 아니며, 임의의 집합 $X$에 대해 $\mathcal{P}(X)$는 항상 $X$보다 엄격하게 큰 기수(Cardinality)를 가진다.
- 이는 가산 무한($|\mathbb{N}| = \aleph_0$)을 넘어 비가산 무한($|\mathcal{P}(\mathbb{N})| = 2^{\aleph_0}$) 및 끝없이 확장되는 무한 기수의 계층 구조를 보장한다.

---

# 서수(Ordinal)와 기수(Cardinal)의 기초: 추이적 집합 (Transitive Set)

## 1. 추이적 집합의 정의
집합 $X$의 모든 원소가 $X$의 부분집합일 때, $X$를 **추이적 집합(Transitive Set)**이라 한다.
$$
\operatorname{is\_transitive}(X) \iff \forall y \in X, y \subseteq X \iff (\forall z, y, z \in y \land y \in X \implies z \in X)
$$

## 2. 주요 성질 및 정리
1. **합집합과의 동치 조건**:
   $$
   \operatorname{is\_transitive}(X) \iff \bigcup X \subseteq X
   $$
2. **공집합의 추이성**:
   - $0 = \emptyset$은 추이적 집합이다 (`empty_is_transitive`).
3. **따름집합 연산에 대한 닫힘**:
   - $X$가 추이적 집합이면, 그 따름집합 $\operatorname{succ}(X) = X \cup \{X\}$ 또한 추이적 집합이다 (`succ_is_transitive`).
4. **따름집합의 합집합 정리**:
   - $X$가 추이적 집합이면, $\bigcup (\operatorname{succ}(X)) = X$이다 (`union_all_succ_of_is_transitive`).
5. **교집합 및 합집합의 보존**:
   - 두 추이적 집합 $X, Y$에 대하여 $X \cap Y$와 $X \cup Y$ 모두 추이적 집합이다 (`inter_is_transitive`, `union_is_transitive`).
   - 추이적 집합 $X$에 대하여 $\bigcup X$ 또한 추이적 집합이다 (`union_all_is_transitive`).

## 3. 자연수 집합과 폰 노이만 서수 (Von Neumann Ordinals)
1. **모든 자연수의 추이성**:
   - 수학적 귀납법(`nat_induction`)에 의해, 모든 자연수 $n \in \mathbb{N}_{\mathrm{set}}$은 추이적 집합이다 (`nat_is_transitive`).
   - 예:
     - $0 = \emptyset$
     - $1 = \{0\}$
     - $2 = \{0, 1\}$
     - $n = \{0, 1, 2, \dots, n-1\}$
2. **자연수 원소의 소속성**:
   - $n \in \mathbb{N}_{\mathrm{set}}$이고 $m \in n$이면 $m \in \mathbb{N}_{\mathrm{set}}$이다 (`nat_elements_in_Nat_set`). 즉, 자연수의 원소는 항상 자연수이다.
3. **자연수 집합(첫 번째 무한 서수 $\omega$)의 추이성**:
   - 자연수 집합 $\mathbb{N}_{\mathrm{set}}$ 자체도 추이적 집합이다 (`Nat_set_is_transitive`).

### 수학적 의의:
- 폰 노이만 체계에서 **서수(Ordinal)**는 "소속 관계 $\in$에 의해 엄격 정렬된(well-ordered) 추이적 집합"으로 정의된다.
- 각 유한 자연수 $n$ 및 자연수 전체의 집합 $\omega = \mathbb{N}_{\mathrm{set}}$이 추이적 집합임을 증명함으로써, ZFC 공리계 위에서 일반 서수 및 기수 이론으로 나아가는 핵심 가교를 완성한다.

---

# 기수 대소 관계 ($\preceq, \prec$) 및 엄격한 칸토어 부등식

## 1. 기수 이하 및 기수 미만 관계의 정의
- **기수 이하 관계 ($X \preceq Y$, `card_le`)**: $X$에서 $Y$로 가는 단사 함수(Injective function)가 존재할 때 $X \preceq Y$로 표기한다 ($|X| \le |Y|$).
- **기수 미만 관계 ($X \prec Y$, `card_lt`)**: $X \preceq Y$이면서 $X \not\cong Y$일 때 $X \prec Y$로 표기한다 ($|X| < |Y|$).

## 2. 기본 성질 (원순서, Preorder)
1. **반사율 (`card_le_refl`)**: 임의의 집합 $X$에 대하여 $X \preceq X$이다 (항등 함수 $\operatorname{id}_X$는 단사 함수).
2. **추이율 (`card_le_trans`)**: $X \preceq Y$이고 $Y \preceq Z$이면 $X \preceq Z$이다 (단사 함수의 합성은 단사 함수).
3. **대등과의 관계 (`equipotent_imp_card_le`)**: $X \cong Y$이면 $X \preceq Y$이다.

## 3. 한원소 집합 매장 사상과 엄격한 칸토어 부등식
1. **한원소 집합 사상 (`singleton_func`)**:
   - $x \in X$를 한원소 부분집합 $\{x\} \in \mathcal{P}(X)$로 보내는 사상 $f(x) = \{x\}$는 단사 함수이다 (`singleton_func_is_injective`).
   - 따라서 임의의 집합 $X$에 대하여 $X \preceq \mathcal{P}(X)$가 성립한다 (`card_le_powerset`).
2. **엄격한 칸토어 부등식 (`cantor_strict_inequality`)**:
   - $X \preceq \mathcal{P}(X)$와 칸토어의 정리 $X \not\cong \mathcal{P}(X)$를 결합하면, 임의의 집합 $X$에 대하여 다음이 성립한다:
   $$
   X \prec \mathcal{P}(X) \quad (|X| < |\mathcal{P}(X)|)
   $$

---

# 힐베르트의 호텔 정리 및 자연수 집합의 데데킨트 무한성

## 1. 자연수의 분해 정리 (`nat_zero_or_succ`)
수학적 귀납법에 의해, 모든 자연수 $n \in \mathbb{N}_{\mathrm{set}}$은 $0(\emptyset)$이거나 어떤 자연수 $m \in \mathbb{N}_{\mathrm{set}}$의 다음수 $n = \operatorname{succ}(m)$이다.

## 2. 데데킨트 무한 집합과 힐베르트의 호텔 (`hilbert_hotel`, `Nat_set_is_dedekind_infinite`)
- **데데킨트 무한(Dedekind-Infinite)**: 집합 $X$가 자신의 진부분집합 $Y \subsetneq X$와 대등($X \cong Y$)할 때, $X$를 데데킨트 무한 집합이라 한다.
- 양의 자연수 집합 $\mathbb{N}^+ = \mathbb{N}_{\mathrm{set}} \setminus \{\emptyset\}$ (`Nat_pos`)은 $\mathbb{N}_{\mathrm{set}}$의 진부분집합이다 (`Nat_pos_proper_subset`).
- 다음수 사상 $S : \mathbb{N}_{\mathrm{set}} \to \mathbb{N}_{\mathrm{set}} \setminus \{\emptyset\}$, $S(n) = \operatorname{succ}(n)$은 전단사 함수이다 (`succ_func_nat_is_bijective`):
  - **단사성**: 페아노 4번 공리(`succ_injective`)에 의해 성립.
  - **전사성**: 자연수의 분해 정리(`nat_zero_or_succ`)에 의해 $0$이 아닌 모든 자연수는 어떤 자연수의 다음수이므로 성립.
- 따라서 $\mathbb{N}_{\mathrm{set}} \cong \mathbb{N}_{\mathrm{set}} \setminus \{\emptyset\}$이 성립하며, $\mathbb{N}_{\mathrm{set}}$은 데데킨트 무한 집합이다.

---

# 자연수의 순서 구조, 삼분법(Trichotomy) 및 정렬성(Well-Ordering)

폰 노이만 자연수 체계에서는 원소 소속 관계 $m \in n$이 곧 엄격한 대소 관계 $m < n$을 정의하며, 부분집합 관계 $m \subseteq n$이 $m \le n$을 정의한다.

1. **따름연산의 순서 보존성 (`mem_succ_iff_mem_of_nat`)**:
   - 자연수 $n \in \mathbb{N}_{\mathrm{set}}$에 대하여 $m \in n \iff \operatorname{succ}(m) \in \operatorname{succ}(n)$이다.
2. **자연수의 삼분법 (`nat_trichotomy`)**:
   - 임의의 두 자연수 $m, n \in \mathbb{N}_{\mathrm{set}}$에 대하여 다음 셋 중 하나가 성립한다:
   $$
   m \in n \;\lor\; m = n \;\lor\; n \in m
   $$
3. **부분집합과 대소 관계의 일치 (`nat_subset_iff_mem_or_eq`)**:
   - 임의의 두 자연수 $m, n \in \mathbb{N}_{\mathrm{set}}$에 대하여 다음이 성립한다:
   $$
   m \subseteq n \iff (m \in n \lor m = n)
   $$
4. **자연수의 정렬성 원리 (`nat_well_ordering`, Well-Ordering Principle)**:
   - $\mathbb{N}_{\mathrm{set}}$의 공집합이 아닌 임의의 부분집합 $S \subseteq \mathbb{N}_{\mathrm{set}}$는 $\in$-최소 원소 $m \in S$를 가진다:
   $$
   \exists m \in S,\; \forall x \in S,\; (m \in x \lor m = x)
   $$
   - 증명: 정칙성 공리(`axiom_regularity`)로부터 $m \cap S = \emptyset$인 원소 $m \in S$를 취하고, 자연수의 삼분법(`nat_trichotomy`)을 결합하면 $x \in S$에 대해 $x \in m$이 불가능하므로 $m \in x \lor m = x$가 즉시 도출된다.

---

# 폰 노이만 서수 (Von Neumann Ordinals) 및 부랄리-포르티 역설

## 1. 서수의 정의 (`is_ordinal`)
정칙성 공리가 성립하는 ZFC 체계에서, 집합 $\alpha$가 **폰 노이만 서수(Ordinal)**라는 것은 $\alpha$가 추이적 집합이고 $\alpha$의 모든 원소 또한 추이적 집합임을 의미한다:
$$
\operatorname{is\_ordinal}(\alpha) \iff \operatorname{is\_transitive}(\alpha) \land (\forall \beta \in \alpha,\; \operatorname{is\_transitive}(\beta))
$$

## 2. 서수의 기본 정리
1. **영 서수 (`empty_is_ordinal`)**: $\emptyset$은 서수이다.
2. **원소의 서수성 (`elem_of_ordinal_is_ordinal`)**: 서수 $\alpha$의 모든 원소 $\beta \in \alpha$는 다시 서수이다.
3. **다음수 서수 (`succ_is_ordinal`)**: $\alpha$가 서수이면 $\operatorname{succ}(\alpha) = \alpha \cup \{\alpha\}$ 또한 서수이다.
4. **소속 관계의 추이성 (`ordinal_mem_trans`)**: 서수 $\alpha$ 내부에서 $x \in y \land y \in z \land z \in \alpha \implies x \in z$이다.
5. **유한 서수와 최초의 초한 서수 (`nat_is_ordinal`, `Nat_set_is_ordinal`)**:
   - 모든 자연수 $n \in \mathbb{N}_{\mathrm{set}}$은 서수이다 (유한 서수).
   - 자연수 전체의 집합 $\omega = \mathbb{N}_{\mathrm{set}}$은 서수이다 (최초의 무한/극한 서수).

## 3. 부랄리-포르티 역설 (`burali_forti_paradox`, Burali-Forti Paradox)
**정리**: 모든 서수를 원소로 가지는 집합 $\Omega$는 존재하지 않는다.
$$
\neg \exists \Omega,\; \forall \alpha,\; (\alpha \in \Omega \iff \operatorname{is\_ordinal}(\alpha))
$$
- **Proof**:
  1. 그러한 집합 $\Omega$가 존재한다고 가정하자.
  2. 서수의 원소는 다시 서수이므로(`elem_of_ordinal_is_ordinal`), $\alpha \in \Omega$이고 $\beta \in \alpha$이면 $\beta$도 서수여서 $\beta \in \Omega$이다. 즉 $\Omega$는 추이적 집합이다.
  3. 또한 $\Omega$의 모든 원소는 서수이므로 추이적 집합이다. 따라서 정의에 의해 $\Omega$ 자신도 서수(`is_ordinal Ω`)이다.
  4. $\Omega$가 서수이므로 $\Omega \in \Omega$가 되어야 하나, 이는 정칙성 공리에서 유도된 자기 소속 배제 정리(`no_self_mem`)에 모순이다.
  5. 따라서 모든 서수의 모임은 집합(Set)이 될 수 없으며 고유 모임(Proper Class)이다.

---

# 유리수 코시 수열의 동치류로서의 실수($\mathbb{R}$) 구성

## 1. 유리수 코시 수열 (`IsCauchy`, `CauchySeq`)
유리수 수열 $a : \mathbb{N} \to \mathbb{Q}$가 다음 조건을 만족할 때 **코시 수열(Cauchy Sequence)**이라 한다:
$$
\operatorname{IsCauchy}(a) \iff \forall \varepsilon \in \mathbb{Q},\; \varepsilon > 0 \implies \exists N \in \mathbb{N},\; \forall m, n \ge N,\; |a_m - a_n|_{\mathbb{Q}} < \varepsilon
$$

## 2. 코시 수열의 동치 관계 (`CauchyEquiv`) 및 실수의 정의 (`ℝ`)
두 유리수 코시 수열 $a = (a_n)$, $b = (b_n)$에 대하여 동치 관계 $a \sim b$를 다음과 같이 정의한다:
$$
a \sim b \iff \forall \varepsilon \in \mathbb{Q},\; \varepsilon > 0 \implies \exists N \in \mathbb{N},\; \forall n \ge N,\; |a_n - b_n|_{\mathbb{Q}} < \varepsilon
$$
- **동치 관계 증명 (`cauchy_equiv_is_equivalence`)**:
  1. **반사율 (`cauchy_equiv_refl`)**: $|a_n - a_n| = 0 < \varepsilon$ ($N = 0$).
  2. **대칭율 (`cauchy_equiv_symm`)**: $|b_n - a_n| = |a_n - b_n| < \varepsilon$.
  3. **추이율 (`cauchy_equiv_trans`)**: $\varepsilon / 2 > 0$에 대해 $N_1, N_2$를 택하고 $N = \max(N_1, N_2)$로 두면, $n \ge N$일 때 삼각부등식에 의해
     $$|a_n - c_n| \le |a_n - b_n| + |b_n - c_n| < \frac{\varepsilon}{2} + \frac{\varepsilon}{2} = \varepsilon$$
- **실수 집합의 정의**:
  $$
  \mathbb{R} := \operatorname{Quotient}(\operatorname{CauchySetoid}) = \{ [a] \mid a \text{는 유리수 코시 수열} \}
  $$
- **연산의 잘 정의됨(Well-definedness) 및 아벨군 성질**:
  - 코시 수열의 합 `addCauchy`와 부호 반전 `negCauchy`가 코시 성질 및 동치 관계 $\sim$를 보존함을 증명(`add_is_cauchy`, `addCauchy_congr`, `neg_is_cauchy`, `negCauchy_congr`)하여 동치류 $\mathbb{R}$ 위로 덧셈과 뺄셈을 리프팅한다.
  - 동치류 위에서 교환법칙(`r_add_comm`), 결합법칙(`r_add_assoc`), 항등원(`r_add_zero`), 역원(`r_add_left_neg`)을 증명한다.

---

# $\varepsilon$-$\delta$ 논법을 통한 극한, 연속, 미분 및 다르부 적분

## 1. 함수의 극한 (`HasLimit`)
함수 $f : \mathbb{R} \to \mathbb{R}$가 점 $a$에서 극한 $L$을 가짐($\lim_{x \to a} f(x) = L$)을 $\varepsilon$-$\delta$ 논법으로 다음과 같이 정의한다:
$$
\operatorname{HasLimit}(f, a, L) \iff \forall \varepsilon > 0,\; \exists \delta > 0,\; \forall x \in \mathbb{R},\; \left(0 < |x - a| < \delta \implies |f(x) - L| < \varepsilon\right)
$$
- **주요 정리**:
  - **극한의 유일성 (`limit_unique`)**: $\varepsilon/2$와 $\delta = \min(\delta_1, \delta_2)$ 및 삼각부등식을 통해 $L_1 = L_2$ 증명.
  - **상수·항등·합·차의 극한 법칙 (`limit_const`, `limit_id`, `limit_add`, `limit_sub`)**
  - **조임 정리 / 샌드위치 정리 (`squeeze_theorem`)**: 천공 근방에서 $g(x) \le f(x) \le h(x)$이고 $\lim g = \lim h = L$이면 $\lim f = L$.

## 2. 연속성과 미분계수 (`ContinuousAt`, `HasDerivAt`)
- **점 $a$에서의 연속 (`ContinuousAt f a`)**:
  $$
  \forall \varepsilon > 0,\; \exists \delta > 0,\; \forall x \in \mathbb{R},\; \left(|x - a| < \delta \implies |f(x) - f(a)| < \varepsilon\right)
  $$
- **점 $a$에서의 미분계수 (`HasDerivAt f a L`)**:
  $$
  \forall \varepsilon > 0,\; \exists \delta > 0,\; \forall x \in \mathbb{R},\; \left(0 < |x - a| < \delta \implies \left|\frac{f(x) - f(a)}{x - a} - L\right| < \varepsilon\right)
  $$
- **주요 정리**:
  - 미분계수의 유일성(`hasDerivAt_unique`), 상수함수 미분(`hasDerivAt_const`), 항등함수 미분(`hasDerivAt_id`), 합·차의 미분법(`hasDerivAt_add`, `hasDerivAt_sub`).
  - **미분가능하면 연속이다 (`differentiable_imp_continuousAt`)**.

## 3. 다르부 적분 (`DarbouxIntegral`)
닫힌구간 $[a, b]$의 분할 $P = \{x_0, x_1, \dots, x_n\}$에 대하여:
- **하다르부 합**: $L(f, P) = \sum_{i=1}^n m_i (x_i - x_{i-1})$ ($m_i = \inf_{[x_{i-1}, x_i]} f$)
- **상다르부 합**: $U(f, P) = \sum_{i=1}^n M_i (x_i - x_{i-1})$ ($M_i = \sup_{[x_{i-1}, x_i]} f$)
- **다르부 적분가능성 (`DarbouxIntegral f a b I`)**:
  1. 모든 분할 $P$에 대하여 $L(f, P) \le I \le U(f, P)$이다.
  2. **리만-다르부 $\varepsilon$-판정법**: 임의의 $\varepsilon > 0$에 대하여 $U(f, P) - L(f, P) < \varepsilon$을 만족하는 분할 $P$가 존재한다.
- **정리**:
  - 다르부 적분값 $I$는 유일하다 (`darboux_integral_unique`).
  - 다르부 적분가능하면 하다르부 적분과 상다르부 적분이 일치한다 (`darboux_lower_eq_upper_of_integrable`).

---

# 미적분학의 기본 정리 (Fundamental Theorem of Calculus, Part 1 & Part 2)

## 제1정리 (`fundamental_theorem_of_calculus_part1`)
**정리**: 함수 $f : [a, b] \to \mathbb{R}$가 다르부 적분가능하고 $F(x) = \int_a^x f(t)\,dt$로 정의될 때, $f$가 점 $c \in (a, b)$에서 연속이면 $F$는 점 $c$에서 미분가능하며 $F'(c) = f(c)$이다.

### Proof ($\varepsilon$-$\delta$ 증명):
1. 임의의 $\varepsilon > 0$이 주어졌다고 하자.
2. $f$가 점 $c$에서 연속이므로 $\varepsilon / 2 > 0$에 대응하는 $\delta > 0$이 존재하여, $|t - c| < \delta \implies |f(t) - f(c)| < \varepsilon / 2$이다.
3. $0 < |x - c| < \delta$인 임의의 $x$를 택하면, $c$와 $x$ 사이의 모든 $t$ ($|t - c| \le |x - c| < \delta$)에 대하여 $|f(t) - f(c)| < \varepsilon / 2$이다.
4. 정적분의 구간 가법성 $F(x) - F(c) = \int_c^x f(t)\,dt$와 다르부 상하계 평균값 부등식에 의해:
   $$
   \left|\frac{F(x) - F(c)}{x - c} - f(c)\right| \le \frac{\varepsilon}{2} < \varepsilon
   $$
5. 따라서 `HasDerivAt F c (f c)` ($F'(c) = f(c)$)가 성립한다.

---

## 제2정리 (`fundamental_theorem_of_calculus_part2`, 뉴턴-라이프니츠 공식)
**정리**: 함수 $f : [a, b] \to \mathbb{R}$가 다르부 적분가능하여 적분값 $I = \int_a^b f(x)\,dx$를 갖고, 함수 $F : [a, b] \to \mathbb{R}$가 $[a, b]$에서 연속이며 $(a, b)$에서 $F'(x) = f(x)$인 원시함수이면:
$$
\int_a^b f(x)\,dx = F(b) - F(a)
$$

### Proof (다르부 상하합 + 평균값 정리 증명):
1. 임의의 분할 $P = \{x_0, x_1, \dots, x_n\}$에 대하여, 각 부분구간 $[x_{i-1}, x_i]$에서 평균값 정리(MVT)를 적용하면 $c_i \in (x_{i-1}, x_i)$가 존재하여
   $$F(x_i) - F(x_{i-1}) = F'(c_i)(x_i - x_{i-1}) = f(c_i)(x_i - x_{i-1})$$
   이다.
2. 부분구간 상하한 정의에 의해 $m_i \le f(c_i) \le M_i$이므로(`mvt_subinterval_darboux_bound`):
   $$m_i (x_i - x_{i-1}) \le F(x_i) - F(x_{i-1}) \le M_i (x_i - x_{i-1})$$
3. 이를 $i = 1, \dots, n$에 대해 모두 더하면 망원합(Telescoping sum) $\sum_{i=1}^n (F(x_i) - F(x_{i-1})) = F(b) - F(a)$에 의해 모든 분할 $P$에 대하여 다음이 성립한다:
   $$L(f, P) \le F(b) - F(a) \le U(f, P)$$
4. 한편 적분값 $I$ 역시 모든 분할 $P$에 대하여 $L(f, P) \le I \le U(f, P)$를 만족한다.
5. 이제 임의의 $\varepsilon > 0$에 대하여, 리만-다르부 $\varepsilon$-판정법으로 $U(f, P) - L(f, P) < \varepsilon$인 분할 $P$를 택하면, 동일한 구간 $[L(f, P), U(f, P)]$에 속하는 두 실수 $I$와 $F(b) - F(a)$의 거리는:
   $$|I - (F(b) - F(a))| \le U(f, P) - L(f, P) < \varepsilon$$
6. 위 부등식이 모든 $\varepsilon > 0$에 대하여 성립하므로 $I = F(b) - F(a)$이다.