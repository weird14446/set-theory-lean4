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