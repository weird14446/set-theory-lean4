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