# 군론
집합 $X$와 함수 $\cdot:X\to X$가 주어졌을 때, 다음과 같은 공리를 만족한다고 하자.

1. 임의의 $x,y,z\in X$에 대하여, $(x\cdot y)\cdot z = x\cdot (y\cdot z)$이다. 즉, 결합법칙이 성립한다.
2. 어떤 $1\in X$가 존재하여, 임의의 $x\in X$에 대하여, $1\cdot x=x$이다. 여기서 $1$을 항등원이라 한다.
3. 임의의 $x\in X$에 대하여, 어떤 $x^\prime\in X$가 존재하여, $x\cdot x^\prime=1$이다. 여기서 $x^\prime$을 $x$의 역원이라 한다.

그렇다면 튜플 $(X,\cdot)$을 군(Group)이라 한다.

Lemma 1. 임의의 $x,y,z\in X$에 대하여, $x=y$이면 $x\cdot z=y\cdot z$이다.

Theorem (항등원의 교환법칙) 임의의 $x\in X$에 대하여, 다음을 만족한다.
$$
1\cdot x=x\cdot 1 = x
$$
Proof.


Theorem (역원의 교환법칙) 임의의 $x$와 공리 2로부터 얻어낸 $x$의 역원 $x^\prime$에 대하여, 다음이 성립한다.
$$
x\cdot x^\prime = x^\prime\cdot x=1
$$
Proof.
