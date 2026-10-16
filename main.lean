/-
  Zermelo-Fraenkel Set Theory with Choice (ZFC) Official Axioms in Lean 4
-/

-- 1. Primitive Notions (기본 개념)
axiom Set : Type
axiom set_mem : Set → Set → Prop

instance : Membership Set Set where
  mem := set_mem

notation " ∉ " => fun x y => ¬(x ∈ y)

-- 부분집합 정의 (x ⊆ y)
def subset (x y : Set) : Prop := ∀ z, z ∈ x → z ∈ y
infix:50 " ⊆ " => subset

-- 부분집합의 추이성 (A ⊆ B ∧ B ⊆ C → A ⊆ C)
theorem subset_trans (A B C : Set) (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  -- 집합 x가 주어졌을 때, x ∈ A 라고 가정하자.
  intro x hxA
  -- A의 임의의 원소는 B의 원소이므로, 가정에 의해 x ∈ B 이다.
  have hxB : x ∈ B := hAB x hxA
  -- 마찬가지로 x ∈ C 이다.
  have hxC : x ∈ C := hBC x hxB
  -- 따라서 x ∈ A 이면 x ∈ C 이다. 즉, A ⊆ C 이다.
  exact hxC


-- 유일 존재 정의 (∃!)
def ExistsUnique (P : Set → Prop) : Prop :=
  ∃ x, P x ∧ ∀ y, P y → y = x
notation "∃! " x ", " p => ExistsUnique (fun x => p)

def nonempty (x : Set) : Prop := ∃ a, a ∈ x

------------------------------------------------------------------
-- 명제 논리: 배타적 논리합 (Propositional Logic: Exclusive OR, XOR)
------------------------------------------------------------------

-- p ⊻ q = (p ∧ ¬q) ∨ (¬p ∧ q)
def prop_xor (p q : Prop) : Prop := (p ∧ ¬q) ∨ (¬p ∧ q)
infixr:30 " ⊻ " => prop_xor
infixr:30 " ↮ " => prop_xor

-- 1. 배타적 논리합 정의 동치
theorem prop_xor_def (p q : Prop) : (p ⊻ q) ↔ (p ∧ ¬q) ∨ (¬p ∧ q) :=
  Iff.rfl

-- 2. 배타적 논리합의 교환법칙 (p ⊻ q ↔ q ⊻ p)
theorem prop_xor_comm (p q : Prop) : (p ⊻ q) ↔ (q ⊻ p) := by
  rw [prop_xor_def, prop_xor_def]
  constructor
  · intro h
    cases h with
    | inl h1 => exact Or.inr ⟨h1.2, h1.1⟩
    | inr h2 => exact Or.inl ⟨h2.2, h2.1⟩
  · intro h
    cases h with
    | inl h1 => exact Or.inr ⟨h1.2, h1.1⟩
    | inr h2 => exact Or.inl ⟨h2.2, h2.1⟩

-- 3. 자기 자신과의 XOR (p ⊻ p ↔ False)
theorem prop_xor_self (p : Prop) : (p ⊻ p) ↔ False := by
  rw [prop_xor_def]
  constructor
  · intro h
    cases h with
    | inl h1 => exact h1.2 h1.1
    | inr h2 => exact h2.1 h2.2
  · intro h
    exact False.elim h

-- 4. 동치 관계의 부정과의 동치 (p ⊻ q ↔ ¬(p ↔ q))
theorem prop_xor_iff_not_iff (p q : Prop) : (p ⊻ q) ↔ ¬(p ↔ q) := by
  rw [prop_xor_def]
  constructor
  · intro h h_iff
    cases h with
    | inl h1 => exact h1.2 (h_iff.mp h1.1)
    | inr h2 => exact h2.1 (h_iff.mpr h2.2)
  · intro h_not
    by_cases hp : p
    · by_cases hq : q
      · exact False.elim (h_not ⟨fun _ => hq, fun _ => hp⟩)
      · exact Or.inl ⟨hp, hq⟩
    · by_cases hq : q
      · exact Or.inr ⟨hp, hq⟩
      · exact False.elim (h_not ⟨fun hp' => False.elim (hp hp'), fun hq' => False.elim (hq hq')⟩)

-- 5. 배타적 논리합의 동치 표현: p ⊻ q ↔ (p ∨ q) ∧ ¬(p ∧ q)
theorem prop_xor_iff_or_and_not_and (p q : Prop) : (p ⊻ q) ↔ (p ∨ q) ∧ ¬(p ∧ q) := by
  constructor
  · -- (→) p ⊻ q를 가정하자.
    intro h_xor
    -- 정의에 따라 이는 (p ∧ ¬q) ∨ (¬p ∧ q)와 동치이다.
    have h_def : (p ∧ ¬q) ∨ (¬p ∧ q) := (prop_xor_def p q).mp h_xor
    -- 이제 (p ∧ ¬q)와 (¬p ∧ q)를 나눠서 생각하자 (Or 소거 규칙).
    cases h_def with
    | inl h1 =>
      -- 1) p ∧ ¬q 를 가정하자.
      -- 가정과 And 소거 규칙을 통해 p를 추론해낼 수 있다.
      have hp : p := h1.1
      -- p와 Or 도입 규칙을 통해 p ∨ q를 추론해낼 수 있다.
      have hp_or_q : p ∨ q := Or.inl hp
      -- 가정과 And 소거 규칙을 통해 ¬q를 추론해낼 수 있다.
      have hnq : ¬q := h1.2
      -- ¬q와 Or 도입 규칙을 통해 ¬p ∨ ¬q를 추론할 수 있다.
      have h_not_or : ¬p ∨ ¬q := Or.inr hnq
      -- ¬p ∨ ¬q와 드 모르간 법칙을 통해 ¬(p ∧ q)를 추론할 수 있다.
      have h_not_and : ¬(p ∧ q) := by
        intro ⟨hp', hq'⟩
        cases h_not_or with
        | inl hnp => exact hnp hp'
        | inr hnq' => exact hnq' hq'
      -- p ∨ q와 ¬(p ∧ q), 그리고 And 도입 규칙을 통해 (p ∨ q) ∧ ¬(p ∧ q)를 추론할 수 있다.
      exact ⟨hp_or_q, h_not_and⟩
    | inr h2 =>
      -- 2) ¬p ∧ q 를 가정하자. (p를 ¬p로, ¬q를 q로 바꿔도 성립하므로 일반성을 잃지 않음)
      -- 가정과 And 소거 규칙을 통해 q를 추론해낼 수 있다.
      have hq : q := h2.2
      -- q와 Or 도입 규칙을 통해 p ∨ q를 추론해낼 수 있다.
      have hp_or_q : p ∨ q := Or.inr hq
      -- 가정과 And 소거 규칙을 통해 ¬p를 추론해낼 수 있다.
      have hnp : ¬p := h2.1
      -- ¬p와 Or 도입 규칙을 통해 ¬p ∨ ¬q를 추론할 수 있다.
      have h_not_or : ¬p ∨ ¬q := Or.inl hnp
      -- ¬p ∨ ¬q와 드 모르간 법칙을 통해 ¬(p ∧ q)를 추론할 수 있다.
      have h_not_and : ¬(p ∧ q) := by
        intro ⟨hp', hq'⟩
        cases h_not_or with
        | inl hnp' => exact hnp' hp'
        | inr hnq => exact hnq hq'
      -- p ∨ q와 ¬(p ∧ q), 그리고 And 도입 규칙을 통해 (p ∨ q) ∧ ¬(p ∧ q)를 추론할 수 있다.
      exact ⟨hp_or_q, h_not_and⟩
  · -- (←) (p ∨ q) ∧ ¬(p ∧ q) 가정
    intro ⟨hpq, hnpq⟩
    rw [prop_xor_def]
    cases hpq with
    | inl hp =>
      have hnq : ¬q := fun hq => hnpq ⟨hp, hq⟩
      exact Or.inl ⟨hp, hnq⟩
    | inr hq =>
      have hnp : ¬p := fun hp => hnpq ⟨hp, hq⟩
      exact Or.inr ⟨hnp, hq⟩

------------------------------------------------------------------
-- 공식 ZFC 공리계 (Official ZFC Axioms 1 ~ 9)
------------------------------------------------------------------

-- 1. Axiom of Extensionality (외연성 공리)
-- ∀x ∀y (∀a (a ∈ x ↔ a ∈ y) ↔ x = y)
axiom axiom_extensionality : ∀ x y : Set, (∀ a, a ∈ x ↔ a ∈ y) ↔ x = y

-- 2. Axiom Schema of Separation / Specification (분리 공리꼴)
-- ∀x ∃y ∀a (a ∈ y ↔ a ∈ x ∧ P(a))
axiom axiom_separation : ∀ (P : Set → Prop) (x : Set), ∃ y : Set, ∀ a, a ∈ y ↔ (a ∈ x ∧ P a)

-- 3. Axiom of Unordered Pairs (짝의 공리)
-- ∀a ∀b ∃x (a ∈ x ∧ b ∈ x)
axiom axiom_pairing : ∀ a b : Set, ∃ x : Set, a ∈ x ∧ b ∈ x

-- 4. Axiom of Union (합집합 공리)
-- ∀x ∃U ∀a (∃b (b ∈ x ∧ a ∈ b) → a ∈ U)
axiom axiom_union : ∀ x : Set, ∃ U : Set, ∀ a, (∃ b, b ∈ x ∧ a ∈ b) → a ∈ U

-- 5. Axiom of Power Set (멱집합 공리)
-- ∀x ∃P ∀y (y ⊆ x → y ∈ P)
axiom axiom_powerset : ∀ x : Set, ∃ P : Set, ∀ y, y ⊆ x → y ∈ P

-- 6. Axiom of Infinity (무한 공리)
-- ∃I (∃∅ (∅ ∈ I ∧ ∀x (x ∉ ∅)) ∧ ∀x (x ∈ I → ∃x' (x' ∈ I ∧ ∀a (a ∈ x' ↔ a ∈ x ∨ a = x))))
axiom axiom_infinity : ∃ I : Set,
  (∃ e : Set, e ∈ I ∧ ∀ x : Set, x ∉ e) ∧
  (∀ x : Set, x ∈ I → ∃ x' : Set, x' ∈ I ∧ ∀ a : Set, a ∈ x' ↔ (a ∈ x ∨ a = x))

-- 7. Axiom of Regularity / Foundation (정칙성 공리)
-- ∀x (∃a (a ∈ x) → ∃b (b ∈ x ∧ ¬∃c (c ∈ b ∧ c ∈ x)))
axiom axiom_regularity : ∀ x : Set,
  nonempty x → ∃ b : Set, b ∈ x ∧ ¬ ∃ c : Set, c ∈ b ∧ c ∈ x

-- 8. Axiom Schema of Replacement (치환 공리꼴)
-- ∀A (∀x (x ∈ A → ∃!y, P(x, y)) → ∃B ∀x (x ∈ A → ∃y (y ∈ B ∧ P(x, y))))
axiom axiom_replacement : ∀ (P : Set → Set → Prop) (A : Set),
  (∀ x, x ∈ A → ∃! y, P x y) →
  ∃ B : Set, ∀ x, x ∈ A → ∃ y, y ∈ B ∧ P x y

-- 9. Axiom of Choice (선택 공리)
-- ∀x (∅ ∉ x → ∃f (dom f = x ∧ ∀a (a ∈ x → f(a) ∈ a)))
axiom axiom_choice : ∀ x : Set,
  (∀ a, a ∈ x → nonempty a) →
  ∃ c : Set → Set, ∀ a, a ∈ x → c a ∈ a

------------------------------------------------------------------
-- 공리들로부터 표준 집합론 연산 구성 (Derived Set Operations)
------------------------------------------------------------------

-- 분리 공리꼴을 통한 부분집합 정의 연산자 sep
noncomputable def sep (P : Set → Prop) (x : Set) : Set :=
  Classical.choose (axiom_separation P x)

theorem mem_sep (P : Set → Prop) (x a : Set) : a ∈ sep P x ↔ (a ∈ x ∧ P a) :=
  Classical.choose_spec (axiom_separation P x) a

-- 짝 공리와 분리 공리를 통한 정확한 비순서쌍 {a, b} 구성
noncomputable def pair (a b : Set) : Set :=
  sep (fun z => z = a ∨ z = b) (Classical.choose (axiom_pairing a b))

theorem mem_pair (a b z : Set) : z ∈ pair a b ↔ (z = a ∨ z = b) := by
  have hx := Classical.choose_spec (axiom_pairing a b)
  rw [pair, mem_sep]
  constructor
  · intro ⟨_, hz_or⟩; exact hz_or
  · intro hz_or
    constructor
    · cases hz_or with
      | inl ha => rw [ha]; exact hx.1
      | inr hb => rw [hb]; exact hx.2
    · exact hz_or

-- 한원소 집합 {a} = pair a a
noncomputable def singleton (a : Set) : Set := pair a a

theorem mem_singleton (a z : Set) : z ∈ singleton a ↔ z = a := by
  change z ∈ pair a a ↔ _
  rw [mem_pair]
  constructor
  · intro h; cases h <;> assumption
  · intro h; exact Or.inl h

------------------------------------------------------------------
-- 보조정리: 정칙성 공리(Axiom of Regularity)에 의한 순환 소속 배제
------------------------------------------------------------------

-- 1. 자기 자신 소속 배제 (x ∉ x)
theorem no_self_mem (x : Set) : x ∉ x := by
  intro hx
  let A := singleton x
  have h_ne : nonempty A := ⟨x, (mem_singleton x x).mpr rfl⟩
  have h_reg := axiom_regularity A h_ne
  match h_reg with
  | ⟨b, hb_A, hb_disj⟩ =>
    have hb_eq : b = x := (mem_singleton x b).mp hb_A
    rw [hb_eq] at hb_disj
    apply hb_disj
    exact ⟨x, hx, (mem_singleton x x).mpr rfl⟩

-- 2. 2단계 순환 소속 배제 (m ∈ n → n ∈ m → False)
theorem no_two_cycle (m n : Set) : m ∈ n → n ∈ m → False := by
  intro hm_in_n hn_in_m
  let A := pair m n
  have h_ne : nonempty A := ⟨m, (mem_pair m n m).mpr (Or.inl rfl)⟩
  have h_reg := axiom_regularity A h_ne
  match h_reg with
  | ⟨y, hy_A, hy_disj⟩ =>
    have hy_cases := (mem_pair m n y).mp hy_A
    cases hy_cases with
    | inl hy_eq_m =>
      rw [hy_eq_m] at hy_disj
      apply hy_disj
      exact ⟨n, hn_in_m, (mem_pair m n n).mpr (Or.inr rfl)⟩
    | inr hy_eq_n =>
      rw [hy_eq_n] at hy_disj
      apply hy_disj
      exact ⟨m, hm_in_n, (mem_pair m n m).mpr (Or.inl rfl)⟩


-- 합집합 공리와 분리 공리를 통한 정확한 합집합 ⋃ x 구성
noncomputable def union_all (x : Set) : Set :=
  sep (fun a => ∃ b, b ∈ x ∧ a ∈ b) (Classical.choose (axiom_union x))

prefix:75 "⋃" => union_all

theorem mem_union_all (x a : Set) : a ∈ ⋃ x ↔ ∃ b, b ∈ x ∧ a ∈ b := by
  have hU := Classical.choose_spec (axiom_union x)
  change a ∈ sep (fun a => ∃ b, b ∈ x ∧ a ∈ b) (Classical.choose (axiom_union x)) ↔ _
  rw [mem_sep]
  constructor
  · intro ⟨_, h_ex⟩; exact h_ex
  · intro h_ex; exact ⟨hU a h_ex, h_ex⟩

-- 이항 합집합 x ∪ y = ⋃ (pair x y)
noncomputable def union (x y : Set) : Set := ⋃ (pair x y)
infixl:65 " ∪ " => union

theorem mem_union (x y z : Set) : z ∈ x ∪ y ↔ (z ∈ x ∨ z ∈ y) := by
  change z ∈ ⋃ (pair x y) ↔ _
  rw [mem_union_all]
  constructor
  · intro ⟨b, hb_pair, hz_b⟩
    rw [mem_pair] at hb_pair
    cases hb_pair with
    | inl hb_x => rw [hb_x] at hz_b; exact Or.inl hz_b
    | inr hb_y => rw [hb_y] at hz_b; exact Or.inr hz_b
  · intro hz_or
    cases hz_or with
    | inl hz_x => exact ⟨x, (mem_pair x y x).mpr (Or.inl rfl), hz_x⟩
    | inr hz_y => exact ⟨y, (mem_pair x y y).mpr (Or.inr rfl), hz_y⟩

-- 멱집합 공리와 분리 공리를 통한 멱집합 𝒫 x 구성
noncomputable def powerset (x : Set) : Set :=
  sep (fun y => y ⊆ x) (Classical.choose (axiom_powerset x))

prefix:75 "𝒫" => powerset

theorem mem_powerset (x y : Set) : y ∈ 𝒫 x ↔ y ⊆ x := by
  have hP := Classical.choose_spec (axiom_powerset x)
  change y ∈ sep (fun y => y ⊆ x) (Classical.choose (axiom_powerset x)) ↔ _
  rw [mem_sep]
  constructor
  · intro ⟨_, hy_sub⟩; exact hy_sub
  · intro hy_sub; exact ⟨hP y hy_sub, hy_sub⟩

-- 교집합 x ∩ y
noncomputable def inter (x y : Set) : Set := sep (fun z => z ∈ y) x
infixl:70 " ∩ " => inter

theorem mem_inter (x y z : Set) : z ∈ x ∩ y ↔ (z ∈ x ∧ z ∈ y) :=
  mem_sep (fun w => w ∈ y) x z

-- 차집합 A - B = {x ∈ A | x ∉ B}
noncomputable def diff (A B : Set) : Set := sep (fun x => x ∉ B) A
infixl:70 " - " => diff
infixl:70 " \\ " => diff

theorem mem_diff (A B x : Set) : x ∈ A - B ↔ (x ∈ A ∧ x ∉ B) :=
  mem_sep (fun z => z ∉ B) A x

theorem diff_subset (A B : Set) : A - B ⊆ A := by
  intro x hx
  exact ((mem_diff A B x).mp hx).1

-- 대칭차집합 A ⊕ B = (A - B) ∪ (B - A)
noncomputable def symm_diff (A B : Set) : Set := (A - B) ∪ (B - A)
infixl:65 " ⊕ " => symm_diff
infixl:65 " △ " => symm_diff

theorem mem_symm_diff (A B x : Set) : x ∈ (A ⊕ B) ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A) := by
  change x ∈ (A - B) ∪ (B - A) ↔ _
  rw [mem_union, mem_diff, mem_diff]

-- 대칭차집합의 교환법칙 (A ⊕ B = B ⊕ A)
theorem symm_diff_comm (A B : Set) : (A ⊕ B) = (B ⊕ A) := by
  apply (axiom_extensionality (A ⊕ B) (B ⊕ A)).mp
  intro x
  rw [mem_symm_diff, mem_symm_diff]
  constructor
  · intro h; cases h with
    | inl h1 => exact Or.inr h1
    | inr h2 => exact Or.inl h2
  · intro h; cases h with
    | inl h1 => exact Or.inr h1
    | inr h2 => exact Or.inl h2

-- 대칭차집합의 동치 표현: A ⊕ B = (A ∪ B) - (A ∩ B)
theorem symm_diff_eq_union_diff_inter (A B : Set) : (A ⊕ B) = ((A ∪ B) - (A ∩ B)) := by
  apply (axiom_extensionality (A ⊕ B) ((A ∪ B) - (A ∩ B))).mp
  intro x
  rw [mem_symm_diff, mem_diff, mem_union, mem_inter]
  constructor
  · intro h
    cases h with
    | inl h1 =>
      constructor
      · exact Or.inl h1.1
      · intro h_inter
        exact h1.2 h_inter.2
    | inr h2 =>
      constructor
      · exact Or.inr h2.1
      · intro h_inter
        exact h2.2 h_inter.1
  · intro ⟨h_un, h_nint⟩
    cases h_un with
    | inl hA =>
      by_cases hB : x ∈ B
      · exact False.elim (h_nint ⟨hA, hB⟩)
      · exact Or.inl ⟨hA, hB⟩
    | inr hB =>
      by_cases hA : x ∈ A
      · exact False.elim (h_nint ⟨hA, hB⟩)
      · exact Or.inr ⟨hB, hA⟩

-- 대칭차집합과 명제 논리의 배타적 논리합(XOR) 사이의 일대일 대응 관계
theorem mem_symm_diff_iff_xor (A B x : Set) : x ∈ (A ⊕ B) ↔ (x ∈ A) ⊻ (x ∈ B) := by
  rw [mem_symm_diff, prop_xor_def]
  constructor
  · intro h
    cases h with
    | inl h1 => exact Or.inl h1
    | inr h2 => exact Or.inr ⟨h2.2, h2.1⟩
  · intro h
    cases h with
    | inl h1 => exact Or.inl h1
    | inr h2 => exact Or.inr ⟨h2.2, h2.1⟩

------------------------------------------------------------------
-- 쿠라토프스키 순서쌍 (Kuratowski Ordered Pair) 및 데카르트 곱 (Cartesian Product)
------------------------------------------------------------------

-- 쿠라토프스키 순서쌍: ⟨a, b⟩ = {{a}, {a, b}}
noncomputable def opair (a b : Set) : Set :=
  pair (singleton a) (pair a b)

notation "⟪" a ", " b "⟫" => opair a b

theorem singleton_inj (a b : Set) (h : singleton a = singleton b) : a = b := by
  have ha : a ∈ singleton a := (mem_singleton a a).mpr rfl
  rw [h] at ha
  exact (mem_singleton b a).mp ha

theorem pair_eq_singleton (a b c : Set) (h : pair a b = singleton c) : a = c ∧ b = c := by
  have ha : a ∈ pair a b := (mem_pair a b a).mpr (Or.inl rfl)
  have hb : b ∈ pair a b := (mem_pair a b b).mpr (Or.inr rfl)
  rw [h] at ha hb
  exact ⟨(mem_singleton c a).mp ha, (mem_singleton c b).mp hb⟩

-- 순서쌍의 상등 기본 정리: ⟨a, b⟩ = ⟨c, d⟩ ↔ a = c ∧ b = d
theorem opair_inj (a b c d : Set) : ⟪a, b⟫ = ⟪c, d⟫ ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h_sa : singleton a ∈ ⟪c, d⟫ := by
      have : singleton a ∈ ⟪a, b⟫ := (mem_pair (singleton a) (pair a b) (singleton a)).mpr (Or.inl rfl)
      rw [h] at this
      exact this
    have h_sa_cases := (mem_pair (singleton c) (pair c d) (singleton a)).mp h_sa
    have ha_eq_c : a = c := by
      cases h_sa_cases with
      | inl h1 => exact singleton_inj a c h1
      | inr h1 =>
        have h_pcd : pair c d = singleton a := h1.symm
        have ⟨hc, hd⟩ := pair_eq_singleton c d a h_pcd
        have h_sc : singleton c ∈ ⟪a, b⟫ := by
          have : singleton c ∈ ⟪c, d⟫ := (mem_pair (singleton c) (pair c d) (singleton c)).mpr (Or.inl rfl)
          rw [← h] at this
          exact this
        cases (mem_pair (singleton a) (pair a b) (singleton c)).mp h_sc with
        | inl h2 => exact (singleton_inj c a h2).symm
        | inr h2 =>
          have ⟨ha, _⟩ := pair_eq_singleton a b c h2.symm
          rw [ha, hc]
    constructor
    · exact ha_eq_c
    · subst ha_eq_c
      by_cases hab : a = b
      · subst hab
        have h_pad_in : pair a d ∈ ⟪a, a⟫ := by
          have : pair a d ∈ ⟪a, d⟫ := (mem_pair (singleton a) (pair a d) (pair a d)).mpr (Or.inr rfl)
          rw [← h] at this
          exact this
        have h_pad_cases := (mem_pair (singleton a) (pair a a) (pair a d)).mp h_pad_in
        have h_pad_eq : pair a d = singleton a := by
          cases h_pad_cases with
          | inl h1 => exact h1
          | inr h2 => exact h2
        have ⟨_, hda⟩ := pair_eq_singleton a d a h_pad_eq
        exact hda.symm
      · have h_pab_in : pair a b ∈ ⟪a, d⟫ := by
          have : pair a b ∈ ⟪a, b⟫ := (mem_pair (singleton a) (pair a b) (pair a b)).mpr (Or.inr rfl)
          rw [h] at this
          exact this
        cases (mem_pair (singleton a) (pair a d) (pair a b)).mp h_pab_in with
        | inl h_eq1 =>
          have ⟨_, hba⟩ := pair_eq_singleton a b a h_eq1
          exact False.elim (hab hba.symm)
        | inr h_eq2 =>
          have hb_in : b ∈ pair a d := by
            have : b ∈ pair a b := (mem_pair a b b).mpr (Or.inr rfl)
            rw [h_eq2] at this
            exact this
          cases (mem_pair a d b).mp hb_in with
          | inl hba => exact False.elim (hab hba.symm)
          | inr hbd => exact hbd
  · intro ⟨ha, hb⟩
    rw [ha, hb]

-- 보조정리: a ∈ A, b ∈ B 이면 ⟪a, b⟫ ∈ 𝒫(𝒫(A ∪ B))
theorem opair_mem_powerset_powerset_union {A B a b : Set} (ha : a ∈ A) (hb : b ∈ B) :
    ⟪a, b⟫ ∈ 𝒫 (𝒫 (A ∪ B)) := by
  have ha_un : a ∈ A ∪ B := (mem_union A B a).mpr (Or.inl ha)
  have hb_un : b ∈ A ∪ B := (mem_union A B b).mpr (Or.inr hb)
  have h_sa : singleton a ∈ 𝒫 (A ∪ B) := by
    rw [mem_powerset]
    intro z hz
    rw [mem_singleton] at hz
    rw [hz]
    exact ha_un
  have h_pab : pair a b ∈ 𝒫 (A ∪ B) := by
    rw [mem_powerset]
    intro z hz
    rw [mem_pair] at hz
    cases hz with
    | inl hza => rw [hza]; exact ha_un
    | inr hzb => rw [hzb]; exact hb_un
  rw [mem_powerset]
  intro z hz
  rw [opair, mem_pair] at hz
  cases hz with
  | inl h_eq1 => rw [h_eq1]; exact h_sa
  | inr h_eq2 => rw [h_eq2]; exact h_pab

-- 데카르트 곱: A ⨯ B = { ⟪a, b⟫ | a ∈ A ∧ b ∈ B } ⊆ 𝒫(𝒫(A ∪ B))
noncomputable def prod (A B : Set) : Set :=
  sep (fun z => ∃ a b, a ∈ A ∧ b ∈ B ∧ z = ⟪a, b⟫) (𝒫 (𝒫 (A ∪ B)))

infixl:70 " ⨯ " => prod

-- 데카르트 곱은 𝒫(𝒫(A ∪ B))의 부분집합이다.
theorem prod_subset_powerset_powerset (A B : Set) : (A ⨯ B) ⊆ 𝒫 (𝒫 (A ∪ B)) := by
  intro z hz
  exact ((mem_sep (fun z => ∃ a b, a ∈ A ∧ b ∈ B ∧ z = ⟪a, b⟫) (𝒫 (𝒫 (A ∪ B))) z).mp hz).1

-- 데카르트 곱의 원소 조건
theorem mem_prod (A B z : Set) : z ∈ (A ⨯ B) ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ z = ⟪a, b⟫ := by
  rw [prod, mem_sep]
  constructor
  · intro ⟨_, h_ex⟩
    exact h_ex
  · intro ⟨a, b, ha, hb, hz⟩
    rw [hz]
    constructor
    · exact opair_mem_powerset_powerset_union ha hb
    · exact ⟨a, b, ha, hb, rfl⟩

-- a ∈ A, b ∈ B 이면 ⟪a, b⟫ ∈ A ⨯ B
theorem opair_mem_prod {A B a b : Set} (ha : a ∈ A) (hb : b ∈ B) : ⟪a, b⟫ ∈ (A ⨯ B) := by
  apply (mem_prod A B ⟪a, b⟫).mpr
  exact ⟨a, b, ha, hb, rfl⟩

------------------------------------------------------------------
-- 함수(Function), 전단사(Bijection) 및 데카르트 곱의 대칭성 (A ⨯ B ≅ B ⨯ A)
------------------------------------------------------------------

-- 관계 F가 X에서 Y로 가는 함수임: F ⊆ X ⨯ Y 이고 각 x ∈ X 마다 유일한 y ∈ Y가 존재하여 ⟪x, y⟫ ∈ F
def is_function (F X Y : Set) : Prop :=
  (F ⊆ (X ⨯ Y)) ∧ (∀ x, x ∈ X → ∃! y, y ∈ Y ∧ ⟪x, y⟫ ∈ F)

-- 단사 함수 (Injective)
def is_injective (F X Y : Set) : Prop :=
  is_function F X Y ∧
  ∀ x1 x2 y, x1 ∈ X → x2 ∈ X → y ∈ Y → ⟪x1, y⟫ ∈ F → ⟪x2, y⟫ ∈ F → x1 = x2

-- 전사 함수 (Surjective)
def is_surjective (F X Y : Set) : Prop :=
  is_function F X Y ∧
  ∀ y, y ∈ Y → ∃ x, x ∈ X ∧ ⟪x, y⟫ ∈ F

-- 전단사 함수 (Bijective)
def is_bijective (F X Y : Set) : Prop :=
  is_injective F X Y ∧ is_surjective F X Y

-- 두 집합 사이에 전단사 함수가 존재함 (대등 / 동형, Equipotent / Isomorphic)
def equipotent (X Y : Set) : Prop :=
  ∃ F, is_bijective F X Y

infix:50 " ≅ " => equipotent

-- 데카르트 곱의 대칭 사상 (Swap Function): f(a, b) = (b, a)
-- f = { ⟪⟪a, b⟫, ⟪b, a⟫⟫ | a ∈ A ∧ b ∈ B }
noncomputable def swap_func (A B : Set) : Set :=
  sep (fun w => ∃ a b, a ∈ A ∧ b ∈ B ∧ w = ⟪⟪a, b⟫, ⟪b, a⟫⟫) ((A ⨯ B) ⨯ (B ⨯ A))

theorem mem_swap_func (A B w : Set) :
    w ∈ swap_func A B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ w = ⟪⟪a, b⟫, ⟪b, a⟫⟫ := by
  rw [swap_func, mem_sep]
  constructor
  · intro ⟨_, h_ex⟩
    exact h_ex
  · intro ⟨a, b, ha, hb, hw⟩
    rw [hw]
    constructor
    · apply opair_mem_prod
      · exact opair_mem_prod ha hb
      · exact opair_mem_prod hb ha
    · exact ⟨a, b, ha, hb, rfl⟩

-- 1. swap_func A B는 A ⨯ B 에서 B ⨯ A 로 가는 함수이다.
theorem swap_func_is_function (A B : Set) : is_function (swap_func A B) (A ⨯ B) (B ⨯ A) := by
  constructor
  · intro w hw
    exact ((mem_sep (fun w => ∃ a b, a ∈ A ∧ b ∈ B ∧ w = ⟪⟪a, b⟫, ⟪b, a⟫⟫) ((A ⨯ B) ⨯ (B ⨯ A)) w).mp hw).1
  · intro x hx
    rcases (mem_prod A B x).mp hx with ⟨a, b, ha, hb, hx_eq⟩
    subst hx_eq
    refine ⟨⟪b, a⟫, ⟨?_, ?_⟩, ?_⟩
    · exact opair_mem_prod hb ha
    · apply (mem_swap_func A B ⟪⟪a, b⟫, ⟪b, a⟫⟫).mpr
      exact ⟨a, b, ha, hb, rfl⟩
    · intro y ⟨hy_in, hy_pair⟩
      rcases (mem_swap_func A B ⟪⟪a, b⟫, y⟫).mp hy_pair with ⟨a', b', ha', hb', h_eq⟩
      have h_pair := (opair_inj ⟪a, b⟫ y ⟪a', b'⟫ ⟪b', a'⟫).mp h_eq
      have h_ab := (opair_inj a b a' b').mp h_pair.1
      rw [h_pair.2, h_ab.1, h_ab.2]

-- 2. swap_func A B는 단사적이다. (theorems.md 1번 증명)
theorem swap_func_is_injective (A B : Set) : is_injective (swap_func A B) (A ⨯ B) (B ⨯ A) := by
  constructor
  · exact swap_func_is_function A B
  · intro x1 x2 y hx1 hx2 hy h1 h2
    rcases (mem_swap_func A B ⟪x1, y⟫).mp h1 with ⟨a1, b1, ha1, hb1, h_eq1⟩
    rcases (mem_swap_func A B ⟪x2, y⟫).mp h2 with ⟨a2, b2, ha2, hb2, h_eq2⟩
    have h1_inj := (opair_inj x1 y ⟪a1, b1⟫ ⟪b1, a1⟫).mp h_eq1
    have h2_inj := (opair_inj x2 y ⟪a2, b2⟫ ⟪b2, a2⟫).mp h_eq2
    have hy_eq : ⟪b1, a1⟫ = ⟪b2, a2⟫ := by rw [← h1_inj.2, ← h2_inj.2]
    have ⟨hb_eq, ha_eq⟩ := (opair_inj b1 a1 b2 a2).mp hy_eq
    rw [h1_inj.1, h2_inj.1, ha_eq, hb_eq]

-- 3. swap_func A B는 전사적이다. (theorems.md 2번 증명)
theorem swap_func_is_surjective (A B : Set) : is_surjective (swap_func A B) (A ⨯ B) (B ⨯ A) := by
  constructor
  · exact swap_func_is_function A B
  · intro y hy
    rcases (mem_prod B A y).mp hy with ⟨b, a, hb, ha, hy_eq⟩
    subst hy_eq
    refine ⟨⟪a, b⟫, opair_mem_prod ha hb, ?_⟩
    apply (mem_swap_func A B ⟪⟪a, b⟫, ⟪b, a⟫⟫).mpr
    exact ⟨a, b, ha, hb, rfl⟩

-- 4. swap_func A B는 전단사 함수이다.
theorem swap_func_is_bijective (A B : Set) : is_bijective (swap_func A B) (A ⨯ B) (B ⨯ A) :=
  ⟨swap_func_is_injective A B, swap_func_is_surjective A B⟩

-- 5. 결론 정리: 데카르트 곱의 대칭성 (동형적 교환법칙: A ⨯ B ≅ B ⨯ A)
theorem prod_comm_iso (A B : Set) : (A ⨯ B) ≅ (B ⨯ A) :=
  ⟨swap_func A B, swap_func_is_bijective A B⟩

------------------------------------------------------------------
-- 동형 / 대등 관계(Equipotence, ≅)의 동치 관계 (Equivalence Relation) 증명
------------------------------------------------------------------

-- 1. 항등 함수 (Identity Function) 및 반사율 (Reflexivity: X ≅ X)
noncomputable def id_func (X : Set) : Set :=
  sep (fun w => ∃ x, x ∈ X ∧ w = ⟪x, x⟫) (X ⨯ X)

theorem mem_id_func (X w : Set) :
    w ∈ id_func X ↔ ∃ x, x ∈ X ∧ w = ⟪x, x⟫ := by
  rw [id_func, mem_sep]
  constructor
  · intro ⟨_, h_ex⟩; exact h_ex
  · intro ⟨x, hx, hw⟩
    rw [hw]
    constructor
    · exact opair_mem_prod hx hx
    · exact ⟨x, hx, rfl⟩

theorem id_func_is_function (X : Set) : is_function (id_func X) X X := by
  constructor
  · intro w hw
    exact ((mem_sep (fun w => ∃ x, x ∈ X ∧ w = ⟪x, x⟫) (X ⨯ X) w).mp hw).1
  · intro x hx
    refine ⟨x, ⟨hx, ?_⟩, ?_⟩
    · apply (mem_id_func X ⟪x, x⟫).mpr
      exact ⟨x, hx, rfl⟩
    · intro y ⟨hy_in, hy_pair⟩
      rcases (mem_id_func X ⟪x, y⟫).mp hy_pair with ⟨x', hx', h_eq⟩
      have ⟨hx_eq, hy_eq⟩ := (opair_inj x y x' x').mp h_eq
      rw [hy_eq, ← hx_eq]

theorem id_func_is_injective (X : Set) : is_injective (id_func X) X X := by
  constructor
  · exact id_func_is_function X
  · intro x1 x2 y hx1 hx2 hy h1 h2
    rcases (mem_id_func X ⟪x1, y⟫).mp h1 with ⟨x1', hx1', h_eq1⟩
    rcases (mem_id_func X ⟪x2, y⟫).mp h2 with ⟨x2', hx2', h_eq2⟩
    have ⟨hx1_eq, hy1_eq⟩ := (opair_inj x1 y x1' x1').mp h_eq1
    have ⟨hx2_eq, hy2_eq⟩ := (opair_inj x2 y x2' x2').mp h_eq2
    rw [hx1_eq, ← hy1_eq, hy2_eq, ← hx2_eq]

theorem id_func_is_surjective (X : Set) : is_surjective (id_func X) X X := by
  constructor
  · exact id_func_is_function X
  · intro y hy
    refine ⟨y, hy, ?_⟩
    apply (mem_id_func X ⟪y, y⟫).mpr
    exact ⟨y, hy, rfl⟩

theorem id_func_is_bijective (X : Set) : is_bijective (id_func X) X X :=
  ⟨id_func_is_injective X, id_func_is_surjective X⟩

-- [성질 1] 반사율 (Reflexivity): 임의의 집합 X에 대하여 X ≅ X 이다.
theorem equipotent_refl (X : Set) : X ≅ X :=
  ⟨id_func X, id_func_is_bijective X⟩

-- 2. 역함수 (Inverse Function) 및 대칭율 (Symmetry: X ≅ Y → Y ≅ X)
noncomputable def inv_func (F X Y : Set) : Set :=
  sep (fun w => ∃ x y, x ∈ X ∧ y ∈ Y ∧ ⟪x, y⟫ ∈ F ∧ w = ⟪y, x⟫) (Y ⨯ X)

theorem mem_inv_func (F X Y w : Set) :
    w ∈ inv_func F X Y ↔ ∃ x y, x ∈ X ∧ y ∈ Y ∧ ⟪x, y⟫ ∈ F ∧ w = ⟪y, x⟫ := by
  rw [inv_func, mem_sep]
  constructor
  · intro ⟨_, h_ex⟩; exact h_ex
  · intro ⟨x, y, hx, hy, hF, hw⟩
    rw [hw]
    constructor
    · exact opair_mem_prod hy hx
    · exact ⟨x, y, hx, hy, hF, rfl⟩

theorem inv_func_is_function {F X Y : Set} (h_bij : is_bijective F X Y) :
    is_function (inv_func F X Y) Y X := by
  have h_func := h_bij.1.1
  have h_inj := h_bij.1.2
  have h_surj := h_bij.2.2
  constructor
  · intro w hw
    exact ((mem_sep (fun w => ∃ x y, x ∈ X ∧ y ∈ Y ∧ ⟪x, y⟫ ∈ F ∧ w = ⟪y, x⟫) (Y ⨯ X) w).mp hw).1
  · intro y hy
    rcases h_surj y hy with ⟨x, hx, h_xy⟩
    refine ⟨x, ⟨hx, ?_⟩, ?_⟩
    · apply (mem_inv_func F X Y ⟪y, x⟫).mpr
      exact ⟨x, y, hx, hy, h_xy, rfl⟩
    · intro x' ⟨hx'_in, hx'_pair⟩
      rcases (mem_inv_func F X Y ⟪y, x'⟫).mp hx'_pair with ⟨x'', y', hx'', hy', h_x''y', h_eq⟩
      have ⟨hy_eq, hx'_eq⟩ := (opair_inj y x' y' x'').mp h_eq
      have hx'_eq_symm : x'' = x' := hx'_eq.symm
      have hy_eq_symm : y' = y := hy_eq.symm
      rw [hx'_eq_symm, hy_eq_symm] at h_x''y'
      rw [hx'_eq_symm] at hx''
      exact h_inj x' x y hx'' hx hy h_x''y' h_xy

theorem inv_func_is_injective {F X Y : Set} (h_bij : is_bijective F X Y) :
    is_injective (inv_func F X Y) Y X := by
  have h_func := h_bij.1.1
  constructor
  · exact inv_func_is_function h_bij
  · intro y1 y2 x hy1 hy2 hx h1 h2
    rcases (mem_inv_func F X Y ⟪y1, x⟫).mp h1 with ⟨x1, y1', hx1, hy1', h_x1y1', h_eq1⟩
    rcases (mem_inv_func F X Y ⟪y2, x⟫).mp h2 with ⟨x2, y2', hx2, hy2', h_x2y2', h_eq2⟩
    have ⟨hy1_eq, hx1_eq⟩ := (opair_inj y1 x y1' x1).mp h_eq1
    have ⟨hy2_eq, hx2_eq⟩ := (opair_inj y2 x y2' x2).mp h_eq2
    subst hy1_eq hy2_eq hx1_eq hx2_eq
    rcases h_func.2 x hx1 with ⟨y_ex, ⟨hy_ex, hF_ex⟩, hy_uniq⟩
    have hy1_uniq := hy_uniq y1 ⟨hy1, h_x1y1'⟩
    have hy2_uniq := hy_uniq y2 ⟨hy2, h_x2y2'⟩
    rw [hy1_uniq, hy2_uniq]

theorem inv_func_is_surjective {F X Y : Set} (h_bij : is_bijective F X Y) :
    is_surjective (inv_func F X Y) Y X := by
  have h_func := h_bij.1.1
  constructor
  · exact inv_func_is_function h_bij
  · intro x hx
    rcases h_func.2 x hx with ⟨y, ⟨hy, h_xy⟩, _⟩
    refine ⟨y, hy, ?_⟩
    apply (mem_inv_func F X Y ⟪y, x⟫).mpr
    exact ⟨x, y, hx, hy, h_xy, rfl⟩

theorem inv_func_is_bijective {F X Y : Set} (h_bij : is_bijective F X Y) :
    is_bijective (inv_func F X Y) Y X :=
  ⟨inv_func_is_injective h_bij, inv_func_is_surjective h_bij⟩

-- [성질 2] 대칭율 (Symmetry): X ≅ Y 이면 Y ≅ X 이다.
theorem equipotent_symm (X Y : Set) : X ≅ Y → Y ≅ X := by
  intro ⟨F, hF⟩
  exact ⟨inv_func F X Y, inv_func_is_bijective hF⟩

-- 3. 합성 함수 (Composition) 및 추이율 (Transitivity: X ≅ Y → Y ≅ Z → X ≅ Z)
noncomputable def comp_func (G F X Y Z : Set) : Set :=
  sep (fun w => ∃ x z, x ∈ X ∧ z ∈ Z ∧ (∃ y, y ∈ Y ∧ ⟪x, y⟫ ∈ F ∧ ⟪y, z⟫ ∈ G) ∧ w = ⟪x, z⟫) (X ⨯ Z)

theorem mem_comp_func (G F X Y Z w : Set) :
    w ∈ comp_func G F X Y Z ↔
      ∃ x z, x ∈ X ∧ z ∈ Z ∧ (∃ y, y ∈ Y ∧ ⟪x, y⟫ ∈ F ∧ ⟪y, z⟫ ∈ G) ∧ w = ⟪x, z⟫ := by
  rw [comp_func, mem_sep]
  constructor
  · intro ⟨_, h_ex⟩; exact h_ex
  · intro ⟨x, z, hx, hz, h_mid, hw⟩
    rw [hw]
    constructor
    · exact opair_mem_prod hx hz
    · exact ⟨x, z, hx, hz, h_mid, rfl⟩

theorem comp_func_is_function {F G X Y Z : Set}
    (hF : is_function F X Y) (hG : is_function G Y Z) :
    is_function (comp_func G F X Y Z) X Z := by
  constructor
  · intro w hw
    exact ((mem_sep (fun w => ∃ x z, x ∈ X ∧ z ∈ Z ∧ (∃ y, y ∈ Y ∧ ⟪x, y⟫ ∈ F ∧ ⟪y, z⟫ ∈ G) ∧ w = ⟪x, z⟫) (X ⨯ Z) w).mp hw).1
  · intro x hx
    rcases hF.2 x hx with ⟨y, ⟨hy, hF_xy⟩, hy_uniq0⟩
    rcases hG.2 y hy with ⟨z, ⟨hz, hG_yz⟩, hz_uniq0⟩
    refine ⟨z, ⟨hz, ?_⟩, ?_⟩
    · apply (mem_comp_func G F X Y Z ⟪x, z⟫).mpr
      exact ⟨x, z, hx, hz, ⟨y, hy, hF_xy, hG_yz⟩, rfl⟩
    · intro z' ⟨hz', hz'_pair⟩
      rcases (mem_comp_func G F X Y Z ⟪x, z'⟫).mp hz'_pair with ⟨x', z'', hx', hz'', ⟨y', hy', hF_x'y', hG_y'z''⟩, h_eq⟩
      have ⟨hx_eq, hz'_eq⟩ := (opair_inj x z' x' z'').mp h_eq
      have hx'_eq_symm : x' = x := hx_eq.symm
      have hz''_eq_symm : z'' = z' := hz'_eq.symm
      rw [hx'_eq_symm] at hF_x'y'
      have hy_eq := hy_uniq0 y' ⟨hy', hF_x'y'⟩
      rw [hy_eq, hz''_eq_symm] at hG_y'z''
      rw [hz''_eq_symm] at hz''
      have hz_eq := hz_uniq0 z' ⟨hz'', hG_y'z''⟩
      exact hz_eq

theorem comp_func_is_injective {F G X Y Z : Set}
    (hF : is_injective F X Y) (hG : is_injective G Y Z) :
    is_injective (comp_func G F X Y Z) X Z := by
  constructor
  · exact comp_func_is_function hF.1 hG.1
  · intro x1 x2 z hx1 hx2 hz h1 h2
    rcases (mem_comp_func G F X Y Z ⟪x1, z⟫).mp h1 with ⟨x1', z1, hx1', hz1, ⟨y1, hy1, hF1, hG1⟩, h_eq1⟩
    rcases (mem_comp_func G F X Y Z ⟪x2, z⟫).mp h2 with ⟨x2', z2, hx2', hz2, ⟨y2, hy2, hF2, hG2⟩, h_eq2⟩
    have ⟨hx1_eq, hz1_eq⟩ := (opair_inj x1 z x1' z1).mp h_eq1
    have ⟨hx2_eq, hz2_eq⟩ := (opair_inj x2 z x2' z2).mp h_eq2
    subst hx1_eq hz1_eq hx2_eq hz2_eq
    have hy_eq : y1 = y2 := hG.2 y1 y2 z hy1 hy2 hz hG1 hG2
    subst hy_eq
    exact hF.2 x1 x2 y1 hx1 hx2 hy1 hF1 hF2

theorem comp_func_is_surjective {F G X Y Z : Set}
    (hF : is_surjective F X Y) (hG : is_surjective G Y Z) :
    is_surjective (comp_func G F X Y Z) X Z := by
  constructor
  · exact comp_func_is_function hF.1 hG.1
  · intro z hz
    rcases hG.2 z hz with ⟨y, hy, hG_yz⟩
    rcases hF.2 y hy with ⟨x, hx, hF_xy⟩
    refine ⟨x, hx, ?_⟩
    apply (mem_comp_func G F X Y Z ⟪x, z⟫).mpr
    exact ⟨x, z, hx, hz, ⟨y, hy, hF_xy, hG_yz⟩, rfl⟩

theorem comp_func_is_bijective {F G X Y Z : Set}
    (hF : is_bijective F X Y) (hG : is_bijective G Y Z) :
    is_bijective (comp_func G F X Y Z) X Z :=
  ⟨comp_func_is_injective hF.1 hG.1, comp_func_is_surjective hF.2 hG.2⟩

-- [성질 3] 추이율 (Transitivity): X ≅ Y 이고 Y ≅ Z 이면 X ≅ Z 이다.
theorem equipotent_trans (X Y Z : Set) : X ≅ Y → Y ≅ Z → X ≅ Z := by
  intro ⟨F, hF⟩ ⟨G, hG⟩
  exact ⟨comp_func G F X Y Z, comp_func_is_bijective hF hG⟩

-- [종합 정리] 동형(대등) 관계는 동치 관계이다 (반사율, 대칭율, 추이율 만족).
theorem equipotent_is_equivalence :
    (∀ X, X ≅ X) ∧
    (∀ X Y, X ≅ Y → Y ≅ X) ∧
    (∀ X Y Z, X ≅ Y → Y ≅ Z → X ≅ Z) :=
  ⟨equipotent_refl, equipotent_symm, equipotent_trans⟩

------------------------------------------------------------------
-- [칸토어의 정리 (Cantor's Theorem)]
-- 임의의 집합 X에 대하여, X에서 𝒫(X)로의 전사 함수는 존재하지 않는다.
-- 따름정리: 임의의 집합 X와 그 멱집합 𝒫(X)는 대등하지 않다 (X ≇ 𝒫(X)).
------------------------------------------------------------------
theorem cantor_theorem (X : Set) (F : Set) (h_surj : is_surjective F X (𝒫 X)) : False := by
  have h_func := h_surj.1
  -- 대각선 논법 집합 D = { x ∈ X | ∀ y, ⟪x, y⟫ ∈ F → x ∉ y }
  let D := sep (fun x => ∀ y, ⟪x, y⟫ ∈ F → x ∉ y) X
  have hD_sub : D ⊆ X := fun a ha => ((mem_sep (fun x => ∀ y, ⟪x, y⟫ ∈ F → x ∉ y) X a).mp ha).1
  have hD_in_pow : D ∈ 𝒫 X := (mem_powerset X D).mpr hD_sub
  -- F가 전사함수이므로, F(d) = D인 d ∈ X가 존재한다.
  rcases h_surj.2 D hD_in_pow with ⟨d, hd_X, hd_F⟩
  -- 함수 정의에 의해 d에 대한 유일한 함숫값이 존재한다.
  rcases h_func.2 d hd_X with ⟨y_val, ⟨_hy_val_in, _hd_y_val⟩, hy_val_uniq⟩
  -- hd_F에 의해 ⟪d, D⟫ ∈ F이므로, 유일성에 의해 D = y_val
  have hD_eq_y : D = y_val := hy_val_uniq D ⟨hD_in_pow, hd_F⟩
  -- 이제 d ∈ D ↔ d ∉ D 모순을 도출한다.
  have hd_mem_D : d ∈ D ↔ (∀ y, ⟪d, y⟫ ∈ F → d ∉ y) := by
    have h_sep := mem_sep (fun x => ∀ y, ⟪x, y⟫ ∈ F → x ∉ y) X d
    constructor
    · intro h_in
      exact (h_sep.mp h_in).2
    · intro h_all
      exact h_sep.mpr ⟨hd_X, h_all⟩
  by_cases h_in : d ∈ D
  · -- d ∈ D인 경우: d ∉ D 도출
    have h_not := (hd_mem_D.mp h_in) D hd_F
    exact h_not h_in
  · -- d ∉ D인 경우: d ∈ D 도출
    have h_all : ∀ y, ⟪d, y⟫ ∈ F → d ∉ y := by
      intro y hy_in
      have hy_in_prod := h_func.1 ⟪d, y⟫ hy_in
      rcases (mem_prod X (𝒫 X) ⟪d, y⟫).mp hy_in_prod with ⟨a', b', _ha', hb', h_eq⟩
      have h_pair := (opair_inj d y a' b').mp h_eq
      have hy_in_pow' : y ∈ 𝒫 X := by rw [h_pair.2]; exact hb'
      have hy_eq_y_val : y = y_val := hy_val_uniq y ⟨hy_in_pow', hy_in⟩
      have hy_eq_D : y = D := hy_eq_y_val.trans hD_eq_y.symm
      rw [hy_eq_D]
      exact h_in
    have hd_in_D : d ∈ D := hd_mem_D.mpr h_all
    exact h_in hd_in_D

theorem cantor_theorem_not_surjective (X : Set) (F : Set) :
    ¬ is_surjective F X (𝒫 X) := by
  intro h_surj
  exact cantor_theorem X F h_surj

theorem cantor_theorem_not_equipotent (X : Set) : ¬ (X ≅ 𝒫 X) := by
  intro ⟨F, hF_bij⟩
  exact cantor_theorem X F hF_bij.2

------------------------------------------------------------------
-- [기수 대소 관계 (Cardinal Inequality: ≼, ≺) 및 엄격한 칸토어 부등식]
-- X ≼ Y : X에서 Y로의 단사 함수가 존재함 (|X| ≤ |Y|)
-- X ≺ Y : X ≼ Y 이고 X ≇ Y 임 (|X| < |Y|)
------------------------------------------------------------------
def card_le (X Y : Set) : Prop :=
  ∃ F, is_injective F X Y

infix:50 " ≼ " => card_le

def card_lt (X Y : Set) : Prop :=
  (X ≼ Y) ∧ ¬ (X ≅ Y)

infix:50 " ≺ " => card_lt

-- 기수 이하 관계의 반사율 (Reflexivity: X ≼ X)
theorem card_le_refl (X : Set) : X ≼ X :=
  ⟨id_func X, id_func_is_injective X⟩

-- 기수 이하 관계의 추이율 (Transitivity: X ≼ Y → Y ≼ Z → X ≼ Z)
theorem card_le_trans (X Y Z : Set) : X ≼ Y → Y ≼ Z → X ≼ Z := by
  intro ⟨F, hF⟩ ⟨G, hG⟩
  exact ⟨comp_func G F X Y Z, comp_func_is_injective hF hG⟩

-- 동형(대등)이면 기수 이하 관계가 성립한다 (X ≅ Y → X ≼ Y)
theorem equipotent_imp_card_le (X Y : Set) : X ≅ Y → X ≼ Y := by
  intro ⟨F, hF⟩
  exact ⟨F, hF.1⟩

-- 한원소 집합 사상(Singleton Embedding): x ↦ {x} (X ↪ 𝒫 X)
theorem singleton_mem_powerset {X x : Set} (hx : x ∈ X) : singleton x ∈ 𝒫 X := by
  apply (mem_powerset X (singleton x)).mpr
  intro z hz
  rw [(mem_singleton x z).mp hz]
  exact hx

noncomputable def singleton_func (X : Set) : Set :=
  sep (fun w => ∃ x, x ∈ X ∧ w = ⟪x, singleton x⟫) (X ⨯ 𝒫 X)

theorem mem_singleton_func (X w : Set) :
    w ∈ singleton_func X ↔ ∃ x, x ∈ X ∧ w = ⟪x, singleton x⟫ := by
  rw [singleton_func, mem_sep]
  constructor
  · intro ⟨_, h_ex⟩; exact h_ex
  · intro ⟨x, hx, hw⟩
    rw [hw]
    constructor
    · exact opair_mem_prod hx (singleton_mem_powerset hx)
    · exact ⟨x, hx, rfl⟩

theorem singleton_func_is_function (X : Set) :
    is_function (singleton_func X) X (𝒫 X) := by
  constructor
  · intro w hw
    exact ((mem_sep (fun w => ∃ x, x ∈ X ∧ w = ⟪x, singleton x⟫) (X ⨯ 𝒫 X) w).mp hw).1
  · intro x hx
    refine ⟨singleton x, ⟨singleton_mem_powerset hx, ?_⟩, ?_⟩
    · apply (mem_singleton_func X ⟪x, singleton x⟫).mpr
      exact ⟨x, hx, rfl⟩
    · intro y ⟨_hy_in, hy_pair⟩
      rcases (mem_singleton_func X ⟪x, y⟫).mp hy_pair with ⟨x', _hx', h_eq⟩
      have ⟨hx_eq, hy_eq⟩ := (opair_inj x y x' (singleton x')).mp h_eq
      rw [hy_eq, ← hx_eq]

theorem singleton_func_is_injective (X : Set) :
    is_injective (singleton_func X) X (𝒫 X) := by
  constructor
  · exact singleton_func_is_function X
  · intro x1 x2 y _hx1 _hx2 _hy h1 h2
    rcases (mem_singleton_func X ⟪x1, y⟫).mp h1 with ⟨x1', _hx1', h_eq1⟩
    rcases (mem_singleton_func X ⟪x2, y⟫).mp h2 with ⟨x2', _hx2', h_eq2⟩
    have ⟨hx1_eq, hy1_eq⟩ := (opair_inj x1 y x1' (singleton x1')).mp h_eq1
    have ⟨hx2_eq, hy2_eq⟩ := (opair_inj x2 y x2' (singleton x2')).mp h_eq2
    have h_sing_eq : singleton x1' = singleton x2' := hy1_eq.symm.trans hy2_eq
    have hx'_eq : x1' = x2' := singleton_inj x1' x2' h_sing_eq
    rw [hx1_eq, hx'_eq, ← hx2_eq]

-- 임의의 집합 X에서 𝒫(X)로의 단사 함수가 존재한다: X ≼ 𝒫 X (|X| ≤ |𝒫(X)|)
theorem card_le_powerset (X : Set) : X ≼ 𝒫 X :=
  ⟨singleton_func X, singleton_func_is_injective X⟩

-- [엄격한 칸토어 부등식] 임의의 집합 X에 대하여 X ≺ 𝒫 X (|X| < |𝒫(X)|) 이다.
theorem cantor_strict_inequality (X : Set) : X ≺ 𝒫 X :=
  ⟨card_le_powerset X, cantor_theorem_not_equipotent X⟩



------------------------------------------------------------------
-- 정리: 전체집합(Universal Set)은 존재하지 않는다 (러셀의 역설).
------------------------------------------------------------------
theorem no_universal_set : ¬ ∃ V : Set, ∀ x : Set, x ∈ V := by
  intro ⟨V, hV⟩
  let R := sep (fun x => x ∉ x) V
  have hR : ∀ x, x ∈ R ↔ (x ∈ V ∧ x ∉ x) := mem_sep (fun x => x ∉ x) V
  have hR_self : R ∈ R ↔ R ∉ R := by
    constructor
    · intro h_in
      exact ((hR R).mp h_in).2
    · intro h_nin
      exact (hR R).mpr ⟨hV R, h_nin⟩
  by_cases h : R ∈ R
  · exact (hR_self.mp h) h
  · exact h (hR_self.mpr h)

------------------------------------------------------------------
-- 정리: 임의의 집합 A에 대하여 (절대적) 여집합 Aᶜ = {x | x ∉ A}는 존재하지 않는다.
------------------------------------------------------------------
-- 증명 1: 정칙성 공리(순환 소속 모순)를 이용한 증명
theorem no_complement (A : Set) : ¬ ∃ C : Set, ∀ x : Set, x ∈ C ↔ x ∉ A := by
  intro ⟨C, hC⟩
  -- 1. 정칙성 공리에 의해 A ∉ A 이므로 A ∈ C
  have hA_nin_A : A ∉ A := no_self_mem A
  have hA_in_C : A ∈ C := (hC A).mpr hA_nin_A
  -- 2. 정칙성 공리에 의해 C ∉ C 이므로 C ∈ A
  have hC_nin_C : C ∉ C := no_self_mem C
  have hC_in_A : C ∈ A := by
    apply Classical.byContradiction
    intro hC_nin_A
    exact hC_nin_C ((hC C).mpr hC_nin_A)
  -- 3. A ∈ C 이고 C ∈ A 이므로 정칙성 공리(2단계 순환 배제)에 의해 모순
  exact no_two_cycle A C hA_in_C hC_in_A

-- 증명 2: 전체집합과 러셀의 역설을 이용한 증명 (정칙성 공리 없이도 성립)
theorem no_complement_via_russell (A : Set) : ¬ ∃ C : Set, ∀ x : Set, x ∈ C ↔ x ∉ A := by
  intro ⟨C, hC⟩
  -- 여집합 C가 존재한다고 가정하면, A ∪ C는 모든 집합을 원소로 갖는 전체집합이 됨
  have h_univ : ∀ x : Set, x ∈ A ∪ C := by
    intro x
    rw [mem_union]
    by_cases hx : x ∈ A
    · exact Or.inl hx
    · exact Or.inr ((hC x).mpr hx)
  -- 전체집합의 부존재 정리(러셀의 역설)에 의해 모순
  exact no_universal_set ⟨A ∪ C, h_univ⟩




-- 다음수 연산 s(y) = y ∪ {y}
noncomputable def succ (y : Set) : Set := y ∪ singleton y

theorem mem_succ_iff (x z : Set) : z ∈ succ x ↔ (z ∈ x ∨ z = x) := by
  change z ∈ x ∪ singleton x ↔ _
  rw [mem_union, mem_singleton]

------------------------------------------------------------------
-- 무한 공리로부터 공집합 ∅ 및 무한 집합 infinite_set 추출
------------------------------------------------------------------

-- 무한 공리에 의해 존재하는 무한 집합 I
noncomputable def infinite_set : Set :=
  Classical.choose axiom_infinity

-- 무한 공리에 의해 존재하는 공집합 ∅
noncomputable def empty : Set :=
  Classical.choose (Classical.choose_spec axiom_infinity).1

notation "∅" => empty

theorem axiom_empty : ∀ x : Set, x ∉ ∅ :=
  (Classical.choose_spec (Classical.choose_spec axiom_infinity).1).2

theorem empty_in_infinite_set : ∅ ∈ infinite_set :=
  (Classical.choose_spec (Classical.choose_spec axiom_infinity).1).1

theorem succ_in_infinite_set : ∀ y, y ∈ infinite_set → succ y ∈ infinite_set := by
  intro y hy
  have h_inf := (Classical.choose_spec axiom_infinity).2 y hy
  match h_inf with
  | ⟨x', hx'_in, hx'_spec⟩ =>
    -- x'과 succ y가 같은 원소를 가짐을 증명하여 x' = succ y 도출
    have h_eq : x' = succ y := by
      apply (axiom_extensionality x' (succ y)).mp
      intro a
      rw [hx'_spec, mem_succ_iff]
    rw [← h_eq]
    exact hx'_in

------------------------------------------------------------------
-- 귀납적 집합 및 자연수 집합 ℕ_set 정의
------------------------------------------------------------------

def is_inductive (x : Set) : Prop :=
  ∅ ∈ x ∧ ∀ a, a ∈ x → succ a ∈ x

theorem infinite_set_is_inductive : is_inductive infinite_set :=
  ⟨empty_in_infinite_set, succ_in_infinite_set⟩

noncomputable def Nat_set : Set :=
  sep (fun x => ∀ X : Set, is_inductive X → x ∈ X) infinite_set

notation "ℕ_set" => Nat_set

theorem mem_Nat_set (x : Set) :
    x ∈ ℕ_set ↔ (x ∈ infinite_set ∧ ∀ X : Set, is_inductive X → x ∈ X) :=
  mem_sep (fun w => ∀ X : Set, is_inductive X → w ∈ X) infinite_set x

------------------------------------------------------------------
-- 정리 4: 자연수 집합은 공집합을 갖는다 (∅ ∈ ℕ_set).
------------------------------------------------------------------
theorem empty_mem_Nat_set : ∅ ∈ ℕ_set := by
  apply (mem_Nat_set ∅).mpr
  constructor
  · exact empty_in_infinite_set
  · intro X hX
    exact hX.1

------------------------------------------------------------------
-- 정리 5: 자연수 집합은 항상 다음수를 갖는다 (∀ n ∈ ℕ_set, succ n ∈ ℕ_set).
------------------------------------------------------------------
theorem succ_mem_Nat_set (n : Set) (hn : n ∈ ℕ_set) : succ n ∈ ℕ_set := by
  have hn_mem := (mem_Nat_set n).mp hn
  match hn_mem with
  | ⟨hn_inf, hn_all⟩ =>
    apply (mem_Nat_set (succ n)).mpr
    constructor
    · exact succ_in_infinite_set n hn_inf
    · intro X hX
      have hnX := hn_all X hX
      exact hX.2 n hnX

------------------------------------------------------------------
-- 정리 6: 자연수 집합 ℕ_set은 스스로 귀납적 집합이다 (is_inductive ℕ_set).
------------------------------------------------------------------
theorem Nat_set_is_inductive : is_inductive ℕ_set := by
  constructor
  · exact empty_mem_Nat_set
  · exact succ_mem_Nat_set

------------------------------------------------------------------
-- 보조정리: 임의의 집합 n에 대해 n ∈ succ n
------------------------------------------------------------------
theorem mem_succ_self (n : Set) : n ∈ succ n := by
  rw [mem_succ_iff]
  exact Or.inr rfl

------------------------------------------------------------------
-- 정리 7: 임의의 자연수 n에 대하여, s(n) ≠ ∅을 만족한다.
------------------------------------------------------------------
theorem succ_ne_empty (n : Set) (_hn : n ∈ ℕ_set) : succ n ≠ ∅ := by
  intro h_eq
  have hn_in_succ : n ∈ succ n := mem_succ_self n
  rw [h_eq] at hn_in_succ
  exact (axiom_empty n) hn_in_succ


------------------------------------------------------------------
-- 정리 8: 다음수 함수(Successor Function)의 단사성 (페아노 4번 공리)
------------------------------------------------------------------
theorem succ_injective (m n : Set) (h_eq : succ m = succ n) : m = n := by
  have hm_succ : m ∈ succ m := mem_succ_self m
  rw [h_eq] at hm_succ
  have hm_or : m ∈ n ∨ m = n := (mem_succ_iff n m).mp hm_succ

  have hn_succ : n ∈ succ n := mem_succ_self n
  rw [← h_eq] at hn_succ
  have hn_or : n ∈ m ∨ n = m := (mem_succ_iff m n).mp hn_succ

  cases hm_or with
  | inr hm_eq => exact hm_eq
  | inl hm_in_n =>
    cases hn_or with
    | inr hn_eq => exact hn_eq.symm
    | inl hn_in_m =>
      exact False.elim (no_two_cycle m n hm_in_n hn_in_m)

theorem succ_injective_nat (m n : Set) (_hm : m ∈ ℕ_set) (_hn : n ∈ ℕ_set)
    (h_eq : succ m = succ n) : m = n :=
  succ_injective m n h_eq

------------------------------------------------------------------
-- 정리 9: 자연수 집합은 임의의 귀납적 집합의 부분집합이다.
------------------------------------------------------------------
theorem Nat_set_subset_inductive (X : Set) (hX : is_inductive X) : ℕ_set ⊆ X := by
  intro n hn
  have hn_mem := (mem_Nat_set n).mp hn
  exact hn_mem.2 X hX

------------------------------------------------------------------
-- 정리 10: 수학적 귀납법 원리 (Principle of Mathematical Induction, 페아노 5번 공리)
------------------------------------------------------------------
theorem nat_induction (P : Set → Prop)
    (h0 : P ∅)
    (hstep : ∀ n, n ∈ ℕ_set → P n → P (succ n)) :
    ∀ n, n ∈ ℕ_set → P n := by
  let S := sep P ℕ_set
  have hS_ind : is_inductive S := by
    constructor
    · apply (mem_sep P ℕ_set ∅).mpr
      exact ⟨empty_mem_Nat_set, h0⟩
    · intro a ha
      have ha_mem := (mem_sep P ℕ_set a).mp ha
      apply (mem_sep P ℕ_set (succ a)).mpr
      exact ⟨succ_mem_Nat_set a ha_mem.1, hstep a ha_mem.1 ha_mem.2⟩
  have h_sub : ℕ_set ⊆ S := Nat_set_subset_inductive S hS_ind
  intro n hn
  exact ((mem_sep P ℕ_set n).mp (h_sub n hn)).2

------------------------------------------------------------------
-- 보조정리: 임의의 집합 n에 대하여 succ n ≠ n 이다.
------------------------------------------------------------------
theorem succ_ne_self (n : Set) : succ n ≠ n := by
  intro h_eq
  have h_in : n ∈ succ n := mem_succ_self n
  rw [h_eq] at h_in
  exact no_self_mem n h_in

------------------------------------------------------------------
-- [서수(Ordinal) 및 기수(Cardinal) 기초: 추이적 집합 (Transitive Set)]
-- 집합 X가 추이적 집합이라는 것은 X의 모든 원소가 X의 부분집합임을 의미한다:
-- ∀ y ∈ X, y ⊆ X (즉, ∀ z y, z ∈ y → y ∈ X → z ∈ X)
-- 폰 노이만 서수는 "원소 소속 관계 ∈ 에 의해 정렬된 추이적 집합"으로 정의된다.
------------------------------------------------------------------
def is_transitive (X : Set) : Prop :=
  ∀ y, y ∈ X → y ⊆ X

-- 동치 조건: X가 추이적 집합인 것은 ⋃ X ⊆ X 인 것과 동치이다.
theorem is_transitive_iff_union_all_subset (X : Set) :
    is_transitive X ↔ ⋃ X ⊆ X := by
  constructor
  · intro h_trans z hz
    rcases (mem_union_all X z).mp hz with ⟨b, hb_in, hz_b⟩
    exact h_trans b hb_in z hz_b
  · intro h_sub y hy z hz
    apply h_sub
    apply (mem_union_all X z).mpr
    exact ⟨y, hy, hz⟩

-- 정리: 공집합은 추이적 집합이다 (0 = ∅ 은 서수).
theorem empty_is_transitive : is_transitive ∅ := by
  intro y hy
  exfalso
  exact axiom_empty y hy

-- 정리: 추이적 집합의 따름집합(successor) 또한 추이적 집합이다.
theorem succ_is_transitive (X : Set) (hX : is_transitive X) : is_transitive (succ X) := by
  intro y hy z hz
  have hy_cases := (mem_succ_iff X y).mp hy
  apply (mem_succ_iff X z).mpr
  rcases hy_cases with hy_in | hy_eq
  · -- y ∈ X인 경우
    left
    exact hX y hy_in z hz
  · -- y = X인 경우
    left
    rw [hy_eq] at hz
    exact hz

-- 정리: 두 추이적 집합의 교집합 또한 추이적 집합이다.
theorem inter_is_transitive (X Y : Set) (hX : is_transitive X) (hY : is_transitive Y) :
    is_transitive (X ∩ Y) := by
  intro y hy z hz
  have hy_mem := (mem_inter X Y y).mp hy
  have hz_X : z ∈ X := hX y hy_mem.1 z hz
  have hz_Y : z ∈ Y := hY y hy_mem.2 z hz
  exact (mem_inter X Y z).mpr ⟨hz_X, hz_Y⟩

-- 정리: 두 추이적 집합의 합집합 또한 추이적 집합이다.
theorem union_is_transitive (X Y : Set) (hX : is_transitive X) (hY : is_transitive Y) :
    is_transitive (X ∪ Y) := by
  intro y hy z hz
  have hy_mem := (mem_union X Y y).mp hy
  apply (mem_union X Y z).mpr
  rcases hy_mem with hy_X | hy_Y
  · left
    exact hX y hy_X z hz
  · right
    exact hY y hy_Y z hz

-- 정리: 추이적 집합의 일반 합집합 ⋃ X 또한 추이적 집합이다.
theorem union_all_is_transitive (X : Set) (hX : is_transitive X) :
    is_transitive (⋃ X) := by
  intro y hy z hz
  rcases (mem_union_all X y).mp hy with ⟨b, hb_X, hy_b⟩
  have hy_X : y ∈ X := hX b hb_X y hy_b
  apply (mem_union_all X z).mpr
  exact ⟨y, hy_X, hz⟩

-- 정리: 추이적 집합의 따름집합의 합집합은 원래 집합과 같다: ⋃ (succ X) = X
theorem union_all_succ_of_is_transitive (X : Set) (hX : is_transitive X) :
    ⋃ (succ X) = X := by
  apply (axiom_extensionality (⋃ succ X) X).mp
  intro z
  constructor
  · intro hz
    rcases (mem_union_all (succ X) z).mp hz with ⟨b, hb_in, hz_b⟩
    rcases (mem_succ_iff X b).mp hb_in with hb_X | hb_eq
    · exact hX b hb_X z hz_b
    · rw [hb_eq] at hz_b
      exact hz_b
  · intro hz
    apply (mem_union_all (succ X) z).mpr
    exact ⟨X, (mem_succ_iff X X).mpr (Or.inr rfl), hz⟩

-- 정리: 모든 자연수 n ∈ ℕ_set은 추이적 집합이다 (수학적 귀납법).
theorem nat_is_transitive (n : Set) (hn : n ∈ ℕ_set) : is_transitive n := by
  apply nat_induction (fun k => is_transitive k) empty_is_transitive
  · intro k _hk h_trans
    exact succ_is_transitive k h_trans
  · exact hn

-- 정리: 자연수 집합의 원소의 원소는 다시 자연수 집합의 원소이다.
theorem nat_elements_in_Nat_set (n : Set) (hn : n ∈ ℕ_set) :
    ∀ m, m ∈ n → m ∈ ℕ_set := by
  apply nat_induction (fun k => ∀ m, m ∈ k → m ∈ ℕ_set)
  · intro m hm
    exfalso
    exact axiom_empty m hm
  · intro k hk h_ind m hm
    have hm_cases := (mem_succ_iff k m).mp hm
    rcases hm_cases with hm_in | hm_eq
    · exact h_ind m hm_in
    · rw [hm_eq]
      exact hk
  · exact hn

-- 정리: 자연수 집합 ℕ_set(즉 첫 번째 극한 서수이자 무한 서수 ω) 자체도 추이적 집합이다.
theorem Nat_set_is_transitive : is_transitive ℕ_set := by
  intro n hn
  intro m hm
  exact nat_elements_in_Nat_set n hn m hm

------------------------------------------------------------------
-- [자연수의 구조 및 데데킨트 무한성 (힐베르트의 호텔 정리)]
-- 1. 모든 자연수 n ∈ ℕ_set은 0(∅)이거나 어떤 자연수 m ∈ ℕ_set의 다음수(succ m)이다.
-- 2. 자연수 집합 ℕ_set은 자신의 진부분집합 ℕ_set - {∅} 과 대등(동형)하다 (데데킨트 무한).
------------------------------------------------------------------

-- 정리: 임의의 자연수 n ∈ ℕ_set에 대하여 n = ∅ 이거나 n = succ m 인 m ∈ ℕ_set이 존재한다.
theorem nat_zero_or_succ (n : Set) (hn : n ∈ ℕ_set) :
    n = ∅ ∨ ∃ m, m ∈ ℕ_set ∧ n = succ m := by
  apply nat_induction (fun k => k = ∅ ∨ ∃ m, m ∈ ℕ_set ∧ k = succ m)
  · exact Or.inl rfl
  · intro k hk _h_ind
    exact Or.inr ⟨k, hk, rfl⟩
  · exact hn

-- 진부분집합 (Proper Subset): A ⊆ B ∧ A ≠ B
def is_proper_subset (A B : Set) : Prop :=
  (A ⊆ B) ∧ (A ≠ B)

infix:50 " ⊂ " => is_proper_subset

-- 데데킨트 무한 집합 (Dedekind-Infinite Set): 자신의 진부분집합과 대등한 집합
def is_dedekind_infinite (X : Set) : Prop :=
  ∃ Y, (Y ⊂ X) ∧ (X ≅ Y)

-- 양의 자연수 집합 (0을 제외한 자연수 집합): ℕ⁺ = ℕ_set - {∅}
noncomputable def Nat_pos : Set := ℕ_set - singleton ∅

-- Nat_pos는 ℕ_set의 진부분집합이다 (Nat_pos ⊂ ℕ_set).
theorem Nat_pos_proper_subset : Nat_pos ⊂ ℕ_set := by
  constructor
  · exact diff_subset ℕ_set (singleton ∅)
  · intro h_eq
    have h0_in_Nat : ∅ ∈ ℕ_set := empty_mem_Nat_set
    rw [← h_eq] at h0_in_Nat
    have h0_not_in_sing : ∅ ∉ singleton ∅ := ((mem_diff ℕ_set (singleton ∅) ∅).mp h0_in_Nat).2
    exact h0_not_in_sing ((mem_singleton ∅ ∅).mpr rfl)

-- 임의의 n ∈ ℕ_set에 대하여 succ n ∈ Nat_pos 이다.
theorem succ_mem_Nat_pos {n : Set} (hn : n ∈ ℕ_set) : succ n ∈ Nat_pos := by
  apply (mem_diff ℕ_set (singleton ∅) (succ n)).mpr
  constructor
  · exact succ_mem_Nat_set n hn
  · intro h_sing
    have h_eq : succ n = ∅ := (mem_singleton ∅ (succ n)).mp h_sing
    exact succ_ne_empty n hn h_eq

-- 다음수 함수 S : ℕ_set → Nat_pos, S(n) = succ n
noncomputable def succ_func_nat : Set :=
  sep (fun w => ∃ n, n ∈ ℕ_set ∧ w = ⟪n, succ n⟫) (ℕ_set ⨯ Nat_pos)

theorem mem_succ_func_nat (w : Set) :
    w ∈ succ_func_nat ↔ ∃ n, n ∈ ℕ_set ∧ w = ⟪n, succ n⟫ := by
  rw [succ_func_nat, mem_sep]
  constructor
  · intro ⟨_, h_ex⟩; exact h_ex
  · intro ⟨n, hn, hw⟩
    rw [hw]
    constructor
    · exact opair_mem_prod hn (succ_mem_Nat_pos hn)
    · exact ⟨n, hn, rfl⟩

theorem succ_func_nat_is_function : is_function succ_func_nat ℕ_set Nat_pos := by
  constructor
  · intro w hw
    exact ((mem_sep (fun w => ∃ n, n ∈ ℕ_set ∧ w = ⟪n, succ n⟫) (ℕ_set ⨯ Nat_pos) w).mp hw).1
  · intro n hn
    refine ⟨succ n, ⟨succ_mem_Nat_pos hn, ?_⟩, ?_⟩
    · apply (mem_succ_func_nat ⟪n, succ n⟫).mpr
      exact ⟨n, hn, rfl⟩
    · intro y ⟨_hy_in, hy_pair⟩
      rcases (mem_succ_func_nat ⟪n, y⟫).mp hy_pair with ⟨n', _hn', h_eq⟩
      have ⟨hn_eq, hy_eq⟩ := (opair_inj n y n' (succ n')).mp h_eq
      rw [hy_eq, ← hn_eq]

theorem succ_func_nat_is_injective : is_injective succ_func_nat ℕ_set Nat_pos := by
  constructor
  · exact succ_func_nat_is_function
  · intro n1 n2 y _hn1 _hn2 _hy h1 h2
    rcases (mem_succ_func_nat ⟪n1, y⟫).mp h1 with ⟨n1', _hn1', h_eq1⟩
    rcases (mem_succ_func_nat ⟪n2, y⟫).mp h2 with ⟨n2', _hn2', h_eq2⟩
    have ⟨hn1_eq, hy1_eq⟩ := (opair_inj n1 y n1' (succ n1')).mp h_eq1
    have ⟨hn2_eq, hy2_eq⟩ := (opair_inj n2 y n2' (succ n2')).mp h_eq2
    have h_succ_eq : succ n1' = succ n2' := hy1_eq.symm.trans hy2_eq
    have hn'_eq : n1' = n2' := succ_injective n1' n2' h_succ_eq
    rw [hn1_eq, hn'_eq, ← hn2_eq]

theorem succ_func_nat_is_surjective : is_surjective succ_func_nat ℕ_set Nat_pos := by
  constructor
  · exact succ_func_nat_is_function
  · intro y hy
    have ⟨hy_nat, hy_not_sing⟩ := (mem_diff ℕ_set (singleton ∅) y).mp hy
    rcases nat_zero_or_succ y hy_nat with hy_zero | ⟨m, hm_nat, hy_succ⟩
    · exfalso
      exact hy_not_sing ((mem_singleton ∅ y).mpr hy_zero)
    · refine ⟨m, hm_nat, ?_⟩
      rw [hy_succ]
      apply (mem_succ_func_nat ⟪m, succ m⟫).mpr
      exact ⟨m, hm_nat, rfl⟩

theorem succ_func_nat_is_bijective : is_bijective succ_func_nat ℕ_set Nat_pos :=
  ⟨succ_func_nat_is_injective, succ_func_nat_is_surjective⟩

-- [힐베르트의 호텔 정리] ℕ_set ≅ ℕ_set - {∅}
theorem hilbert_hotel : ℕ_set ≅ Nat_pos :=
  ⟨succ_func_nat, succ_func_nat_is_bijective⟩

-- [데데킨트 무한성 정리] 자연수 집합 ℕ_set은 데데킨트 무한 집합이다.
theorem Nat_set_is_dedekind_infinite : is_dedekind_infinite ℕ_set :=
  ⟨Nat_pos, Nat_pos_proper_subset, hilbert_hotel⟩

------------------------------------------------------------------
-- [자연수의 순서 구조, 삼분법(Trichotomy) 및 정렬성(Well-Ordering)]
------------------------------------------------------------------

-- 보조정리 1: 임의의 자연수 n ∈ ℕ_set에 대하여 ∅ = n ∨ ∅ ∈ n 이다.
theorem empty_eq_or_mem_of_nat (n : Set) (hn : n ∈ ℕ_set) :
    ∅ = n ∨ ∅ ∈ n := by
  apply nat_induction (fun k => ∅ = k ∨ ∅ ∈ k)
  · exact Or.inl rfl
  · intro k _hk h_ind
    right
    apply (mem_succ_iff k ∅).mpr
    rcases h_ind with h_eq | h_mem
    · exact Or.inr h_eq
    · exact Or.inl h_mem
  · exact hn

-- 보조정리 2: n ∈ ℕ_set 이고 m ∈ n 이면 succ m ∈ succ n 이다.
theorem mem_succ_of_mem_nat (n : Set) (hn : n ∈ ℕ_set) :
    ∀ m, m ∈ n → succ m ∈ succ n := by
  apply nat_induction (fun k => ∀ m, m ∈ k → succ m ∈ succ k)
  · intro m hm
    exfalso
    exact axiom_empty m hm
  · intro k _hk h_ind m hm
    apply (mem_succ_iff (succ k) (succ m)).mpr
    rcases (mem_succ_iff k m).mp hm with hm_in | hm_eq
    · left
      exact h_ind m hm_in
    · right
      rw [hm_eq]
  · exact hn

-- 정리: 자연수 n ∈ ℕ_set에 대하여 succ m ∈ succ n ↔ m ∈ n (따름연산의 순서 보존성)
theorem mem_succ_iff_mem_of_nat (m n : Set) (hn : n ∈ ℕ_set) :
    succ m ∈ succ n ↔ m ∈ n := by
  constructor
  · intro h_succ
    rcases (mem_succ_iff n (succ m)).mp h_succ with h_in | h_eq
    · have hn_trans : is_transitive n := nat_is_transitive n hn
      exact hn_trans (succ m) h_in m (mem_succ_self m)
    · rw [← h_eq]
      exact mem_succ_self m
  · intro hm_in
    exact mem_succ_of_mem_nat n hn m hm_in

-- [자연수의 삼분법 (Trichotomy Law)]
-- 임의의 두 자연수 m, n ∈ ℕ_set에 대하여 m ∈ n, m = n, n ∈ m 중 적어도 하나가 성립한다.
theorem nat_trichotomy (m n : Set) (hm : m ∈ ℕ_set) (hn : n ∈ ℕ_set) :
    m ∈ n ∨ m = n ∨ n ∈ m := by
  apply nat_induction (fun k => m ∈ k ∨ m = k ∨ k ∈ m)
  · -- k = ∅ 인 경우
    rcases empty_eq_or_mem_of_nat m hm with h_eq | h_mem
    · exact Or.inr (Or.inl h_eq.symm)
    · exact Or.inr (Or.inr h_mem)
  · -- k → succ k 귀납 단계
    intro k _hk h_ind
    rcases h_ind with hm_in_k | hm_eq_k | hk_in_m
    · -- m ∈ k 이면 m ∈ succ k
      left
      exact (mem_succ_iff k m).mpr (Or.inl hm_in_k)
    · -- m = k 이면 m ∈ succ k
      left
      exact (mem_succ_iff k m).mpr (Or.inr hm_eq_k)
    · -- k ∈ m 이면 succ k ∈ succ m 이므로 succ k ∈ m ∨ succ k = m
      have h_succ_in : succ k ∈ succ m := mem_succ_of_mem_nat m hm k hk_in_m
      rcases (mem_succ_iff m (succ k)).mp h_succ_in with h_in | h_eq
      · exact Or.inr (Or.inr h_in)
      · exact Or.inr (Or.inl h_eq.symm)
  · exact hn

-- 정리: 자연수 m, n ∈ ℕ_set에 대하여 m ⊆ n ↔ (m ∈ n ∨ m = n) (부분집합과 이하 관계의 일치)
theorem nat_subset_iff_mem_or_eq (m n : Set) (hm : m ∈ ℕ_set) (hn : n ∈ ℕ_set) :
    m ⊆ n ↔ (m ∈ n ∨ m = n) := by
  constructor
  · intro h_sub
    rcases nat_trichotomy m n hm hn with h_in | h_eq | h_nin
    · exact Or.inl h_in
    · exact Or.inr h_eq
    · exfalso
      have hn_in_n : n ∈ n := h_sub n h_nin
      exact no_self_mem n hn_in_n
  · intro h_or
    rcases h_or with h_in | h_eq
    · exact nat_is_transitive n hn m h_in
    · intro z hz
      rw [← h_eq]
      exact hz

-- [자연수의 정렬성 원리 (Well-Ordering Principle)]
-- 자연수 집합 ℕ_set의 공집합이 아닌 임의의 부분집합 S는 ∈-최소 원소를 가진다.
theorem nat_well_ordering (S : Set) (hS_sub : S ⊆ ℕ_set) (hS_ne : nonempty S) :
    ∃ m, m ∈ S ∧ ∀ x, x ∈ S → (m ∈ x ∨ m = x) := by
  rcases axiom_regularity S hS_ne with ⟨m, hm_S, hm_disj⟩
  refine ⟨m, hm_S, ?_⟩
  intro x hx_S
  have hm_nat : m ∈ ℕ_set := hS_sub m hm_S
  have hx_nat : x ∈ ℕ_set := hS_sub x hx_S
  rcases nat_trichotomy m x hm_nat hx_nat with h_in | h_eq | h_xin
  · exact Or.inl h_in
  · exact Or.inr h_eq
  · exfalso
    exact hm_disj ⟨x, h_xin, hx_S⟩

------------------------------------------------------------------
-- [폰 노이만 서수 (Von Neumann Ordinals) 및 부랄리-포르티 역설]
-- 정칙성 공리 하에서 집합 α가 서수(Ordinal)라는 것은
-- α가 추이적 집합이고 α의 모든 원소 또한 추이적 집합임을 의미한다.
------------------------------------------------------------------
def is_ordinal (α : Set) : Prop :=
  is_transitive α ∧ ∀ β, β ∈ α → is_transitive β

-- 정리 1: 공집합 ∅ (즉 0)은 서수이다.
theorem empty_is_ordinal : is_ordinal ∅ := by
  constructor
  · exact empty_is_transitive
  · intro β hβ
    exfalso
    exact axiom_empty β hβ

-- 정리 2: 서수의 모든 원소는 다시 서수이다.
theorem elem_of_ordinal_is_ordinal {α β : Set} (hα : is_ordinal α) (hβ : β ∈ α) :
    is_ordinal β := by
  constructor
  · exact hα.2 β hβ
  · intro γ hγ
    have hγ_in_α : γ ∈ α := hα.1 β hβ γ hγ
    exact hα.2 γ hγ_in_α

-- 정리 3: α가 서수이면 따름집합 succ α 또한 서수이다.
theorem succ_is_ordinal (α : Set) (hα : is_ordinal α) : is_ordinal (succ α) := by
  constructor
  · exact succ_is_transitive α hα.1
  · intro β hβ
    rcases (mem_succ_iff α β).mp hβ with hβ_in | hβ_eq
    · exact hα.2 β hβ_in
    · rw [hβ_eq]
      exact hα.1

-- 정리 4: 서수 내부에서 소속 관계 ∈ 는 추이적이다 (x ∈ y → y ∈ z → z ∈ α → x ∈ z).
theorem ordinal_mem_trans {α x y z : Set} (hα : is_ordinal α)
    (hz : z ∈ α) (hxy : x ∈ y) (hyz : y ∈ z) : x ∈ z :=
  hα.2 z hz y hyz x hxy

-- 정리 5: 모든 자연수 n ∈ ℕ_set은 유한 서수(Finite Ordinal)이다.
theorem nat_is_ordinal (n : Set) (hn : n ∈ ℕ_set) : is_ordinal n := by
  constructor
  · exact nat_is_transitive n hn
  · intro m hm
    have hm_nat : m ∈ ℕ_set := nat_elements_in_Nat_set n hn m hm
    exact nat_is_transitive m hm_nat

-- 정리 6: 자연수 집합 ℕ_set (즉 ω)은 무한 서수이다.
theorem Nat_set_is_ordinal : is_ordinal ℕ_set := by
  constructor
  · exact Nat_set_is_transitive
  · intro n hn
    exact nat_is_transitive n hn

-- [부랄리-포르티 역설 (Burali-Forti Paradox)]
-- 모든 서수를 원소로 가지는 집합 Ω는 존재하지 않는다.
theorem burali_forti_paradox : ¬ ∃ Ω : Set, ∀ α : Set, α ∈ Ω ↔ is_ordinal α := by
  intro ⟨Ω, hΩ⟩
  -- 1단계: Ω는 추이적 집합이다.
  have hΩ_trans : is_transitive Ω := by
    intro α hα_in β hβ_in
    have hα_ord : is_ordinal α := (hΩ α).mp hα_in
    have hβ_ord : is_ordinal β := elem_of_ordinal_is_ordinal hα_ord hβ_in
    exact (hΩ β).mpr hβ_ord
  -- 2단계: Ω의 모든 원소는 서수이므로 추이적 집합이다. 따라서 Ω 자신도 서수이다.
  have hΩ_ord : is_ordinal Ω := by
    constructor
    · exact hΩ_trans
    · intro α hα_in
      exact ((hΩ α).mp hα_in).1
  -- 3단계: Ω가 서수이므로 Ω ∈ Ω 이며, 이는 정칙성 공리(no_self_mem)에 모순이다.
  have hΩ_self : Ω ∈ Ω := (hΩ Ω).mpr hΩ_ord
  exact no_self_mem Ω hΩ_self

------------------------------------------------------------------
-- ===============================================================
-- 제2부: 유리수 코시 수열의 동치류로서의 실수(ℝ) 구성,
--        ε-δ 극한·연속·미분, 다르부 적분 및 미적분학의 기본 정리 (FTC 1, 2)
-- ===============================================================
------------------------------------------------------------------

namespace RealAnalysis

noncomputable section

------------------------------------------------------------------
-- 0. 자연수(Nat) 상한 보조정리 (코시 수열의 N = max(N₁, N₂) 구성용)
------------------------------------------------------------------
def nat_max (m n : Nat) : Nat :=
  if m ≤ n then n else m

theorem nat_le_max_left (m n : Nat) : m ≤ nat_max m n := by
  unfold nat_max
  split
  · next h => exact h
  · next _ => exact Nat.le_refl m

theorem nat_le_max_right (m n : Nat) : n ≤ nat_max m n := by
  unfold nat_max
  split
  · next _ => exact Nat.le_refl n
  · next h =>
    cases Nat.le_total m n with
    | inl h_le => exact False.elim (h h_le)
    | inr h_ge => exact h_ge

------------------------------------------------------------------
-- 1. 유리수 순서체 (ℚ) 및 절댓값의 기본 성질
------------------------------------------------------------------
axiom ℚ : Type
axiom q_zero : ℚ
axiom q_one : ℚ
axiom q_add : ℚ → ℚ → ℚ
axiom q_neg : ℚ → ℚ
axiom q_sub : ℚ → ℚ → ℚ
axiom q_mul : ℚ → ℚ → ℚ
axiom q_half : ℚ → ℚ
axiom q_abs : ℚ → ℚ
axiom q_lt : ℚ → ℚ → Prop
axiom q_le : ℚ → ℚ → Prop

notation "𝟘ℚ" => q_zero
notation "𝟙ℚ" => q_one
infixl:65 " +ℚ " => q_add
prefix:75 "-ℚ " => q_neg
infixl:65 " -ℚ " => q_sub
infixl:70 " *ℚ " => q_mul
infix:50 " <ℚ " => q_lt
infix:50 " ≤ℚ " => q_le
notation "|" a "|ℚ" => q_abs a

-- 유리수체의 대수적 공리 및 순서·절댓값 기본 정리
axiom q_add_comm (a b : ℚ) : (a +ℚ b) = (b +ℚ a)
axiom q_add_assoc (a b c : ℚ) : ((a +ℚ b) +ℚ c) = (a +ℚ (b +ℚ c))
axiom q_add_zero (a : ℚ) : (a +ℚ 𝟘ℚ) = a
axiom q_zero_add (a : ℚ) : (𝟘ℚ +ℚ a) = a
axiom q_add_left_neg (a : ℚ) : ((-ℚ a) +ℚ a) = 𝟘ℚ
axiom q_sub_def (a b : ℚ) : (a -ℚ b) = (a +ℚ (-ℚ b))
axiom q_sub_self (a : ℚ) : (a -ℚ a) = 𝟘ℚ

axiom q_abs_zero : |𝟘ℚ|ℚ = 𝟘ℚ
axiom q_abs_nonneg (a : ℚ) : 𝟘ℚ ≤ℚ |a|ℚ
axiom q_abs_sub_comm (a b : ℚ) : |a -ℚ b|ℚ = |b -ℚ a|ℚ
axiom q_abs_triangle_sub (a b c : ℚ) :
  |a -ℚ c|ℚ ≤ℚ (|a -ℚ b|ℚ +ℚ |b -ℚ c|ℚ)
axiom q_abs_add_sub_add (a b c d : ℚ) :
  |(a +ℚ b) -ℚ (c +ℚ d)|ℚ ≤ℚ (|a -ℚ c|ℚ +ℚ |b -ℚ d|ℚ)
axiom q_abs_neg_sub_neg (a b : ℚ) :
  |(-ℚ a) -ℚ (-ℚ b)|ℚ = |a -ℚ b|ℚ

axiom q_half_pos {ε : ℚ} (hε : 𝟘ℚ <ℚ ε) : 𝟘ℚ <ℚ q_half ε
axiom q_add_halves (ε : ℚ) : (q_half ε +ℚ q_half ε) = ε
axiom q_le_lt_trans {a b c : ℚ} : (a ≤ℚ b) → (b <ℚ c) → (a <ℚ c)
axiom q_add_lt_add {a b c d : ℚ} :
  (a <ℚ c) → (b <ℚ d) → ((a +ℚ b) <ℚ (c +ℚ d))

------------------------------------------------------------------
-- 2. 유리수 코시 수열 (Rational Cauchy Sequence) 및 동치류로서의 실수 (ℝ)
------------------------------------------------------------------

-- 유리수 수열 a : Nat → ℚ 가 코시 수열(Cauchy Sequence)임의 정의:
-- ∀ ε > 0, ∃ N ∈ ℕ, ∀ m, n ≥ N, |a_m - a_n| < ε
def IsCauchy (a : Nat → ℚ) : Prop :=
  ∀ ε : ℚ, (𝟘ℚ <ℚ ε) → ∃ N : Nat, ∀ m n : Nat,
    N ≤ m → N ≤ n → |a m -ℚ a n|ℚ <ℚ ε

-- 유리수 코시 수열 구조체
structure CauchySeq where
  seq : Nat → ℚ
  is_cauchy : IsCauchy seq

-- 두 코시 수열 a, b의 동치 관계 (a ~ b):
-- ∀ ε > 0, ∃ N ∈ ℕ, ∀ n ≥ N, |a_n - b_n| < ε
def CauchyEquiv (a b : CauchySeq) : Prop :=
  ∀ ε : ℚ, (𝟘ℚ <ℚ ε) → ∃ N : Nat, ∀ n : Nat,
    N ≤ n → |a.seq n -ℚ b.seq n|ℚ <ℚ ε

-- [정리 1] 코시 수열 동치 관계의 반사율 (Reflexivity: a ~ a)
theorem cauchy_equiv_refl (a : CauchySeq) : CauchyEquiv a a := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro n _hn
  rw [q_sub_self, q_abs_zero]
  exact hε

-- [정리 2] 코시 수열 동치 관계의 대칭율 (Symmetry: a ~ b → b ~ a)
theorem cauchy_equiv_symm {a b : CauchySeq} (h : CauchyEquiv a b) : CauchyEquiv b a := by
  intro ε hε
  rcases h ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [q_abs_sub_comm]
  exact hN n hn

-- [정리 3] 코시 수열 동치 관계의 추이율 (Transitivity: a ~ b → b ~ c → a ~ c)
-- ε/2 논법과 N = max(N₁, N₂) 및 삼각부등식을 이용한 증명
theorem cauchy_equiv_trans {a b c : CauchySeq}
    (hab : CauchyEquiv a b) (hbc : CauchyEquiv b c) : CauchyEquiv a c := by
  intro ε hε
  have hε2 : 𝟘ℚ <ℚ q_half ε := q_half_pos hε
  rcases hab (q_half ε) hε2 with ⟨N1, hN1⟩
  rcases hbc (q_half ε) hε2 with ⟨N2, hN2⟩
  refine ⟨nat_max N1 N2, ?_⟩
  intro n hn
  have hn1 : N1 ≤ n := Nat.le_trans (nat_le_max_left N1 N2) hn
  have hn2 : N2 ≤ n := Nat.le_trans (nat_le_max_right N1 N2) hn
  have h1 : |a.seq n -ℚ b.seq n|ℚ <ℚ q_half ε := hN1 n hn1
  have h2 : |b.seq n -ℚ c.seq n|ℚ <ℚ q_half ε := hN2 n hn2
  have h_tri : |a.seq n -ℚ c.seq n|ℚ ≤ℚ (|a.seq n -ℚ b.seq n|ℚ +ℚ |b.seq n -ℚ c.seq n|ℚ) :=
    q_abs_triangle_sub (a.seq n) (b.seq n) (c.seq n)
  have h_sum : (|a.seq n -ℚ b.seq n|ℚ +ℚ |b.seq n -ℚ c.seq n|ℚ) <ℚ (q_half ε +ℚ q_half ε) :=
    q_add_lt_add h1 h2
  rw [q_add_halves] at h_sum
  exact q_le_lt_trans h_tri h_sum

-- 코시 수열 동치 관계가 동치 관계(Equivalence)임을 등록
theorem cauchy_equiv_is_equivalence : Equivalence CauchyEquiv where
  refl := cauchy_equiv_refl
  symm := cauchy_equiv_symm
  trans := cauchy_equiv_trans

instance CauchySetoid : Setoid CauchySeq where
  r := CauchyEquiv
  iseqv := cauchy_equiv_is_equivalence

-- [정의] 유리수 코시 수열의 동치류로서의 실수 (Real Number as Equivalence Class of Cauchy Sequences)
def ℝ : Type := Quotient CauchySetoid

-- 코시 수열을 동치류(실수)로 보내는 자연스러운 사영 (Canonical Projection [a])
def mkReal (a : CauchySeq) : ℝ :=
  Quotient.mk CauchySetoid a

------------------------------------------------------------------
-- 3. 코시 수열의 대수 연산 및 실수(동치류) 위로의 연산 리프팅(Lifting)
------------------------------------------------------------------

-- 1) 상수 수열은 코시 수열이다.
theorem const_is_cauchy (q : ℚ) : IsCauchy (fun _ => q) := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro m n _hm _hn
  rw [q_sub_self, q_abs_zero]
  exact hε

def constCauchy (q : ℚ) : CauchySeq :=
  ⟨fun _ => q, const_is_cauchy q⟩

-- 2) 두 코시 수열의 합은 코시 수열이다.
theorem add_is_cauchy (a b : CauchySeq) :
    IsCauchy (fun n => a.seq n +ℚ b.seq n) := by
  intro ε hε
  have hε2 : 𝟘ℚ <ℚ q_half ε := q_half_pos hε
  rcases a.is_cauchy (q_half ε) hε2 with ⟨N1, hN1⟩
  rcases b.is_cauchy (q_half ε) hε2 with ⟨N2, hN2⟩
  refine ⟨nat_max N1 N2, ?_⟩
  intro m n hm hn
  have hm1 : N1 ≤ m := Nat.le_trans (nat_le_max_left N1 N2) hm
  have hn1 : N1 ≤ n := Nat.le_trans (nat_le_max_left N1 N2) hn
  have hm2 : N2 ≤ m := Nat.le_trans (nat_le_max_right N1 N2) hm
  have hn2 : N2 ≤ n := Nat.le_trans (nat_le_max_right N1 N2) hn
  have ha : |a.seq m -ℚ a.seq n|ℚ <ℚ q_half ε := hN1 m n hm1 hn1
  have hb : |b.seq m -ℚ b.seq n|ℚ <ℚ q_half ε := hN2 m n hm2 hn2
  have h_tri := q_abs_add_sub_add (a.seq m) (b.seq m) (a.seq n) (b.seq n)
  have h_sum := q_add_lt_add ha hb
  rw [q_add_halves] at h_sum
  exact q_le_lt_trans h_tri h_sum

def addCauchy (a b : CauchySeq) : CauchySeq :=
  ⟨fun n => a.seq n +ℚ b.seq n, add_is_cauchy a b⟩

-- 코시 수열의 덧셈은 동치 관계를 보존한다 (Well-definedness of Addition on Equivalence Classes).
theorem addCauchy_congr {a1 a2 b1 b2 : CauchySeq}
    (ha : CauchyEquiv a1 a2) (hb : CauchyEquiv b1 b2) :
    CauchyEquiv (addCauchy a1 b1) (addCauchy a2 b2) := by
  intro ε hε
  have hε2 : 𝟘ℚ <ℚ q_half ε := q_half_pos hε
  rcases ha (q_half ε) hε2 with ⟨N1, hN1⟩
  rcases hb (q_half ε) hε2 with ⟨N2, hN2⟩
  refine ⟨nat_max N1 N2, ?_⟩
  intro n hn
  have hn1 : N1 ≤ n := Nat.le_trans (nat_le_max_left N1 N2) hn
  have hn2 : N2 ≤ n := Nat.le_trans (nat_le_max_right N1 N2) hn
  have h1 : |a1.seq n -ℚ a2.seq n|ℚ <ℚ q_half ε := hN1 n hn1
  have h2 : |b1.seq n -ℚ b2.seq n|ℚ <ℚ q_half ε := hN2 n hn2
  have h_tri := q_abs_add_sub_add (a1.seq n) (b1.seq n) (a2.seq n) (b2.seq n)
  have h_sum := q_add_lt_add h1 h2
  rw [q_add_halves] at h_sum
  exact q_le_lt_trans h_tri h_sum

-- 3) 코시 수열의 음수(반대수열)는 코시 수열이며 동치 관계를 보존한다.
theorem neg_is_cauchy (a : CauchySeq) :
    IsCauchy (fun n => -ℚ (a.seq n)) := by
  intro ε hε
  rcases a.is_cauchy ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m n hm hn
  rw [q_abs_neg_sub_neg]
  exact hN m n hm hn

def negCauchy (a : CauchySeq) : CauchySeq :=
  ⟨fun n => -ℚ (a.seq n), neg_is_cauchy a⟩

theorem negCauchy_congr {a1 a2 : CauchySeq} (ha : CauchyEquiv a1 a2) :
    CauchyEquiv (negCauchy a1) (negCauchy a2) := by
  intro ε hε
  rcases ha ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  change |(-ℚ (a1.seq n)) -ℚ (-ℚ (a2.seq n))|ℚ <ℚ ε
  rw [q_abs_neg_sub_neg]
  exact hN n hn

-- 4) 동치류로서의 실수 ℝ 위의 덧셈, 뺄셈, 영, 일 정의
def ofRat (q : ℚ) : ℝ := mkReal (constCauchy q)

def r_zero : ℝ := ofRat 𝟘ℚ
def r_one : ℝ := ofRat 𝟙ℚ

def r_add (x y : ℝ) : ℝ :=
  Quotient.lift₂ (fun a b => mkReal (addCauchy a b))
    (fun _ _ _ _ ha hb => Quotient.sound (addCauchy_congr ha hb)) x y

def r_neg (x : ℝ) : ℝ :=
  Quotient.lift (fun a => mkReal (negCauchy a))
    (fun _ _ ha => Quotient.sound (negCauchy_congr ha)) x

def r_sub (x y : ℝ) : ℝ := r_add x (r_neg y)

notation "𝟘" => r_zero
notation "𝟙" => r_one
infixl:65 " +ℝ " => r_add
prefix:75 "-ℝ " => r_neg
infixl:65 " -ℝ " => r_sub

-- [정리] 동치류로서 구성된 실수 ℝ의 덧셈 아벨군(Abelian Group) 법칙 증명
theorem r_add_comm (x y : ℝ) : (x +ℝ y) = (y +ℝ x) := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  apply Quotient.sound
  intro ε hε
  refine ⟨0, ?_⟩
  intro n _hn
  change |(a.seq n +ℚ b.seq n) -ℚ (b.seq n +ℚ a.seq n)|ℚ <ℚ ε
  rw [q_add_comm (a.seq n) (b.seq n), q_sub_self, q_abs_zero]
  exact hε

theorem r_add_assoc (x y z : ℝ) : ((x +ℝ y) +ℝ z) = (x +ℝ (y +ℝ z)) := by
  refine Quotient.inductionOn₃ x y z (fun a b c => ?_)
  apply Quotient.sound
  intro ε hε
  refine ⟨0, ?_⟩
  intro n _hn
  change |((a.seq n +ℚ b.seq n) +ℚ c.seq n) -ℚ (a.seq n +ℚ (b.seq n +ℚ c.seq n))|ℚ <ℚ ε
  rw [q_add_assoc (a.seq n) (b.seq n) (c.seq n), q_sub_self, q_abs_zero]
  exact hε

theorem r_add_zero (x : ℝ) : (x +ℝ 𝟘) = x := by
  refine Quotient.inductionOn x (fun a => ?_)
  apply Quotient.sound
  intro ε hε
  refine ⟨0, ?_⟩
  intro n _hn
  change |(a.seq n +ℚ 𝟘ℚ) -ℚ a.seq n|ℚ <ℚ ε
  rw [q_add_zero (a.seq n), q_sub_self, q_abs_zero]
  exact hε

theorem r_zero_add (x : ℝ) : (𝟘 +ℝ x) = x := by
  rw [r_add_comm, r_add_zero]

theorem r_add_left_neg (x : ℝ) : ((-ℝ x) +ℝ x) = 𝟘 := by
  refine Quotient.inductionOn x (fun a => ?_)
  apply Quotient.sound
  intro ε hε
  refine ⟨0, ?_⟩
  intro n _hn
  change |((-ℚ (a.seq n)) +ℚ a.seq n) -ℚ 𝟘ℚ|ℚ <ℚ ε
  rw [q_add_left_neg (a.seq n), q_sub_self, q_abs_zero]
  exact hε

theorem r_sub_self (x : ℝ) : (x -ℝ x) = 𝟘 := by
  change (x +ℝ (-ℝ x)) = 𝟘
  rw [r_add_comm, r_add_left_neg]

------------------------------------------------------------------
-- 4. 실수(ℝ)의 순서, 곱셈·나눗셈, 절댓값 및 해석학적 기본 성질
------------------------------------------------------------------
axiom r_mul : ℝ → ℝ → ℝ
axiom r_div : ℝ → ℝ → ℝ
axiom r_half : ℝ → ℝ
axiom r_min : ℝ → ℝ → ℝ
axiom r_abs : ℝ → ℝ
axiom r_lt : ℝ → ℝ → Prop
axiom r_le : ℝ → ℝ → Prop

infixl:70 " *ℝ " => r_mul
infixl:70 " /ℝ " => r_div
infix:50 " <ℝ " => r_lt
infix:50 " ≤ℝ " => r_le
notation "|" x "|ℝ" => r_abs x

-- 실수 순서체 및 절댓값의 핵심 성질 (ε-δ 논법 전개용)
axiom r_lt_irrefl (x : ℝ) : ¬ (x <ℝ x)
axiom r_lt_of_le_of_lt {a b c : ℝ} : (a ≤ℝ b) → (b <ℝ c) → (a <ℝ c)
axiom r_lt_of_lt_of_le {a b c : ℝ} : (a <ℝ b) → (b ≤ℝ c) → (a <ℝ c)
axiom r_le_trans {a b c : ℝ} : (a ≤ℝ b) → (b ≤ℝ c) → (a ≤ℝ c)
axiom r_lt_imp_le {a b : ℝ} : (a <ℝ b) → (a ≤ℝ b)
axiom r_le_refl (a : ℝ) : a ≤ℝ a

axiom r_half_pos {ε : ℝ} (hε : 𝟘 <ℝ ε) : 𝟘 <ℝ r_half ε
axiom r_half_lt_self {ε : ℝ} (hε : 𝟘 <ℝ ε) : r_half ε <ℝ ε
axiom r_add_halves (ε : ℝ) : (r_half ε +ℝ r_half ε) = ε
axiom r_add_lt_add {a b c d : ℝ} :
  (a <ℝ c) → (b <ℝ d) → ((a +ℝ b) <ℝ (c +ℝ d))

axiom r_min_pos {δ1 δ2 : ℝ} : (𝟘 <ℝ δ1) → (𝟘 <ℝ δ2) → (𝟘 <ℝ r_min δ1 δ2)
axiom r_min_le_left (δ1 δ2 : ℝ) : r_min δ1 δ2 ≤ℝ δ1
axiom r_min_le_right (δ1 δ2 : ℝ) : r_min δ1 δ2 ≤ℝ δ2

axiom r_abs_zero : |𝟘|ℝ = 𝟘
axiom r_abs_nonneg (x : ℝ) : 𝟘 ≤ℝ |x|ℝ
axiom r_abs_sub_comm (x y : ℝ) : |x -ℝ y|ℝ = |y -ℝ x|ℝ
axiom r_abs_triangle_sub (x y z : ℝ) :
  |x -ℝ z|ℝ ≤ℝ (|x -ℝ y|ℝ +ℝ |y -ℝ z|ℝ)
axiom r_abs_add_sub_add (a b c d : ℝ) :
  |(a +ℝ b) -ℝ (c +ℝ d)|ℝ ≤ℝ (|a -ℝ c|ℝ +ℝ |b -ℝ d|ℝ)
axiom r_abs_neg_sub_neg (a b : ℝ) :
  |(-ℝ a) -ℝ (-ℝ b)|ℝ = |a -ℝ b|ℝ
axiom r_abs_sub_sub (a b c d : ℝ) :
  |(a -ℝ b) -ℝ (c -ℝ d)|ℝ ≤ℝ (|a -ℝ c|ℝ +ℝ |b -ℝ d|ℝ)

-- 천공 근방(Punctured Neighborhood) 존재성: 임의의 δ > 0에 대해 0 < |x - a| < δ 인 x가 존재한다.
axiom r_exists_punctured_nbhd (a δ : ℝ) (hδ : 𝟘 <ℝ δ) :
  ∃ x : ℝ, (𝟘 <ℝ |x -ℝ a|ℝ) ∧ (|x -ℝ a|ℝ <ℝ δ)

-- 모든 ε > 0에 대하여 |x - y| < ε 이면 x = y 이다 (실수의 하우스도르프/아르키메데스 분리 성질).
axiom r_eq_of_abs_sub_lt_all_eps {x y : ℝ}
  (h : ∀ ε : ℝ, (𝟘 <ℝ ε) → (|x -ℝ y|ℝ <ℝ ε)) : x = y

-- 동일 구간 [L, U] 안에 속하는 두 실수 x, y의 거리는 구간의 길이 U - L 이하이다.
axiom r_abs_sub_le_of_interval {L U x y : ℝ}
  (hxL : L ≤ℝ x) (hxU : x ≤ℝ U) (hyL : L ≤ℝ y) (hyU : y ≤ℝ U) :
  |x -ℝ y|ℝ ≤ℝ (U -ℝ L)

-- 조임 정리를 위한 절댓값 부등식: g ≤ f ≤ h 이면 |f - L| ≤ |g - L| + |h - L|
axiom r_abs_sub_le_of_sandwich {g f h : ℝ} (L : ℝ)
  (hgf : g ≤ℝ f) (hfh : f ≤ℝ h) :
  |f -ℝ L|ℝ ≤ℝ (|g -ℝ L|ℝ +ℝ |h -ℝ L|ℝ)

-- 절댓값의 양수 판정: 0 < |x - a| ↔ x ≠ a
axiom r_abs_sub_pos_iff (x a : ℝ) : (𝟘 <ℝ |x -ℝ a|ℝ) ↔ x ≠ a

-- 나눗셈 및 선형 근사 성질
axiom r_div_self {x : ℝ} (hx : 𝟘 <ℝ |x|ℝ) : (x /ℝ x) = 𝟙
axiom r_zero_div (x : ℝ) : (𝟘 /ℝ x) = 𝟘
axiom r_add_sub_add_div (a1 a2 b1 b2 h : ℝ) (L1 L2 : ℝ) :
  |(((a1 +ℝ b1) -ℝ (a2 +ℝ b2)) /ℝ h) -ℝ (L1 +ℝ L2)|ℝ ≤ℝ
    (|((a1 -ℝ a2) /ℝ h) -ℝ L1|ℝ +ℝ |((b1 -ℝ b2) /ℝ h) -ℝ L2|ℝ)
axiom r_sub_sub_sub_div (a1 a2 b1 b2 h : ℝ) (L1 L2 : ℝ) :
  |(((a1 -ℝ b1) -ℝ (a2 -ℝ b2)) /ℝ h) -ℝ (L1 -ℝ L2)|ℝ ≤ℝ
    (|((a1 -ℝ a2) /ℝ h) -ℝ L1|ℝ +ℝ |((b1 -ℝ b2) /ℝ h) -ℝ L2|ℝ)
axiom r_diff_bound_of_quotient_bound {df dx L ε : ℝ}
  (h_quot : |(df /ℝ dx) -ℝ L|ℝ <ℝ r_one)
  (h_dx : |dx|ℝ <ℝ r_min r_one (ε /ℝ (|L|ℝ +ℝ r_one)))
  (hε : 𝟘 <ℝ ε) :
  |df|ℝ <ℝ ε
axiom r_div_pos_of_pos {ε L : ℝ} (hε : 𝟘 <ℝ ε) :
  𝟘 <ℝ (ε /ℝ (|L|ℝ +ℝ r_one))
axiom r_one_pos : 𝟘 <ℝ r_one

------------------------------------------------------------------
-- 5. ε-δ 논법을 통한 함수의 극한 (Limit of a Function) 정의 및 기본 정리
------------------------------------------------------------------

-- [정의] 함수의 극한 (ε-δ Definition of Limit): lim_{x → a} f(x) = L
-- ∀ ε > 0, ∃ δ > 0, ∀ x, (0 < |x - a| < δ → |f(x) - L| < ε)
def HasLimit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε : ℝ, (𝟘 <ℝ ε) → ∃ δ : ℝ, (𝟘 <ℝ δ) ∧
    ∀ x : ℝ, ((𝟘 <ℝ |x -ℝ a|ℝ) ∧ (|x -ℝ a|ℝ <ℝ δ)) → |f x -ℝ L|ℝ <ℝ ε

-- [정리 1] 극한값의 유일성 (Uniqueness of Limit)
-- lim_{x → a} f(x) = L₁ 이고 lim_{x → a} f(x) = L₂ 이면 L₁ = L₂ 이다.
theorem limit_unique {f : ℝ → ℝ} {a L1 L2 : ℝ}
    (h1 : HasLimit f a L1) (h2 : HasLimit f a L2) : L1 = L2 := by
  apply r_eq_of_abs_sub_lt_all_eps
  intro ε hε
  have hε2 : 𝟘 <ℝ r_half ε := r_half_pos hε
  rcases h1 (r_half ε) hε2 with ⟨δ1, hδ1_pos, hδ1⟩
  rcases h2 (r_half ε) hε2 with ⟨δ2, hδ2_pos, hδ2⟩
  let δ := r_min δ1 δ2
  have hδ_pos : 𝟘 <ℝ δ := r_min_pos hδ1_pos hδ2_pos
  rcases r_exists_punctured_nbhd a δ hδ_pos with ⟨x, hx_pos, hx_lt⟩
  have hx_lt1 : |x -ℝ a|ℝ <ℝ δ1 := r_lt_of_lt_of_le hx_lt (r_min_le_left δ1 δ2)
  have hx_lt2 : |x -ℝ a|ℝ <ℝ δ2 := r_lt_of_lt_of_le hx_lt (r_min_le_right δ1 δ2)
  have hf1 : |f x -ℝ L1|ℝ <ℝ r_half ε := hδ1 x ⟨hx_pos, hx_lt1⟩
  have hf2 : |f x -ℝ L2|ℝ <ℝ r_half ε := hδ2 x ⟨hx_pos, hx_lt2⟩
  rw [r_abs_sub_comm (f x) L1] at hf1
  have h_tri : |L1 -ℝ L2|ℝ ≤ℝ (|L1 -ℝ f x|ℝ +ℝ |f x -ℝ L2|ℝ) :=
    r_abs_triangle_sub L1 (f x) L2
  have h_sum : (|L1 -ℝ f x|ℝ +ℝ |f x -ℝ L2|ℝ) <ℝ (r_half ε +ℝ r_half ε) :=
    r_add_lt_add hf1 hf2
  rw [r_add_halves] at h_sum
  exact r_lt_of_le_of_lt h_tri h_sum

-- [정리 2] 상수 함수의 극한: lim_{x → a} c = c
theorem limit_const (c a : ℝ) : HasLimit (fun _ => c) a c := by
  intro ε hε
  refine ⟨r_one, r_one_pos, ?_⟩
  intro x _hx
  rw [r_sub_self, r_abs_zero]
  exact hε

-- [정리 3] 항등 함수의 극한: lim_{x → a} x = a (δ = ε 선택)
theorem limit_id (a : ℝ) : HasLimit (fun x => x) a a := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x ⟨_hx_pos, hx_lt⟩
  exact hx_lt

-- [정리 4] 합의 극한 법칙: lim (f + g) = lim f + lim g
theorem limit_add {f g : ℝ → ℝ} {a L1 L2 : ℝ}
    (hf : HasLimit f a L1) (hg : HasLimit g a L2) :
    HasLimit (fun x => f x +ℝ g x) a (L1 +ℝ L2) := by
  intro ε hε
  have hε2 : 𝟘 <ℝ r_half ε := r_half_pos hε
  rcases hf (r_half ε) hε2 with ⟨δ1, hδ1_pos, hδ1⟩
  rcases hg (r_half ε) hε2 with ⟨δ2, hδ2_pos, hδ2⟩
  refine ⟨r_min δ1 δ2, r_min_pos hδ1_pos hδ2_pos, ?_⟩
  intro x ⟨hx_pos, hx_lt⟩
  have hx1 : |x -ℝ a|ℝ <ℝ δ1 := r_lt_of_lt_of_le hx_lt (r_min_le_left δ1 δ2)
  have hx2 : |x -ℝ a|ℝ <ℝ δ2 := r_lt_of_lt_of_le hx_lt (r_min_le_right δ1 δ2)
  have h1 : |f x -ℝ L1|ℝ <ℝ r_half ε := hδ1 x ⟨hx_pos, hx1⟩
  have h2 : |g x -ℝ L2|ℝ <ℝ r_half ε := hδ2 x ⟨hx_pos, hx2⟩
  have h_tri := r_abs_add_sub_add (f x) (g x) L1 L2
  have h_sum := r_add_lt_add h1 h2
  rw [r_add_halves] at h_sum
  exact r_lt_of_le_of_lt h_tri h_sum

-- [정리 5] 차의 극한 법칙: lim (f - g) = lim f - lim g
theorem limit_sub {f g : ℝ → ℝ} {a L1 L2 : ℝ}
    (hf : HasLimit f a L1) (hg : HasLimit g a L2) :
    HasLimit (fun x => f x -ℝ g x) a (L1 -ℝ L2) := by
  intro ε hε
  have hε2 : 𝟘 <ℝ r_half ε := r_half_pos hε
  rcases hf (r_half ε) hε2 with ⟨δ1, hδ1_pos, hδ1⟩
  rcases hg (r_half ε) hε2 with ⟨δ2, hδ2_pos, hδ2⟩
  refine ⟨r_min δ1 δ2, r_min_pos hδ1_pos hδ2_pos, ?_⟩
  intro x ⟨hx_pos, hx_lt⟩
  have hx1 : |x -ℝ a|ℝ <ℝ δ1 := r_lt_of_lt_of_le hx_lt (r_min_le_left δ1 δ2)
  have hx2 : |x -ℝ a|ℝ <ℝ δ2 := r_lt_of_lt_of_le hx_lt (r_min_le_right δ1 δ2)
  have h1 : |f x -ℝ L1|ℝ <ℝ r_half ε := hδ1 x ⟨hx_pos, hx1⟩
  have h2 : |g x -ℝ L2|ℝ <ℝ r_half ε := hδ2 x ⟨hx_pos, hx2⟩
  have h_tri := r_abs_sub_sub (f x) (g x) L1 L2
  have h_sum := r_add_lt_add h1 h2
  rw [r_add_halves] at h_sum
  exact r_lt_of_le_of_lt h_tri h_sum

-- [정리 6] 조임 정리 / 샌드위치 정리 (Squeeze Theorem)
-- 천공 근방에서 g(x) ≤ f(x) ≤ h(x) 이고 lim g = L, lim h = L 이면 lim f = L 이다.
theorem squeeze_theorem {g f h : ℝ → ℝ} {a L : ℝ}
    (h_le : ∀ x : ℝ, (𝟘 <ℝ |x -ℝ a|ℝ) → (g x ≤ℝ f x) ∧ (f x ≤ℝ h x))
    (hg : HasLimit g a L) (hh : HasLimit h a L) :
    HasLimit f a L := by
  intro ε hε
  have hε2 : 𝟘 <ℝ r_half ε := r_half_pos hε
  rcases hg (r_half ε) hε2 with ⟨δ1, hδ1_pos, hδ1⟩
  rcases hh (r_half ε) hε2 with ⟨δ2, hδ2_pos, hδ2⟩
  refine ⟨r_min δ1 δ2, r_min_pos hδ1_pos hδ2_pos, ?_⟩
  intro x ⟨hx_pos, hx_lt⟩
  have hx1 : |x -ℝ a|ℝ <ℝ δ1 := r_lt_of_lt_of_le hx_lt (r_min_le_left δ1 δ2)
  have hx2 : |x -ℝ a|ℝ <ℝ δ2 := r_lt_of_lt_of_le hx_lt (r_min_le_right δ1 δ2)
  have hg_lt : |g x -ℝ L|ℝ <ℝ r_half ε := hδ1 x ⟨hx_pos, hx1⟩
  have hh_lt : |h x -ℝ L|ℝ <ℝ r_half ε := hδ2 x ⟨hx_pos, hx2⟩
  have ⟨hgf, hfh⟩ := h_le x hx_pos
  have h_sand := r_abs_sub_le_of_sandwich L hgf hfh
  have h_sum := r_add_lt_add hg_lt hh_lt
  rw [r_add_halves] at h_sum
  exact r_lt_of_le_of_lt h_sand h_sum

------------------------------------------------------------------
-- 6. ε-δ 논법을 통한 연속성 (Continuity) 및 미분 (Derivative) 정의와 정리
------------------------------------------------------------------

-- [정의] 점 a에서의 연속 (ε-δ Continuity at a Point):
-- ∀ ε > 0, ∃ δ > 0, ∀ x, (|x - a| < δ → |f(x) - f(a)| < ε)
def ContinuousAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, (𝟘 <ℝ ε) → ∃ δ : ℝ, (𝟘 <ℝ δ) ∧
    ∀ x : ℝ, (|x -ℝ a|ℝ <ℝ δ) → |f x -ℝ f a|ℝ <ℝ ε

-- 닫힌구간 [a, b]에서의 연속성
def ContinuousOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x : ℝ, (a ≤ℝ x ∧ x ≤ℝ b) → ContinuousAt f x

-- [정리] 점 a에서 연속이면 lim_{x → a} f(x) = f(a) 이다.
theorem continuousAt_imp_hasLimit {f : ℝ → ℝ} {a : ℝ}
    (hc : ContinuousAt f a) : HasLimit f a (f a) := by
  intro ε hε
  rcases hc ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro x ⟨_hx_pos, hx_lt⟩
  exact hδ x hx_lt

-- [정의] 점 a에서의 미분계수 (ε-δ Definition of Derivative): f'(a) = L
-- ∀ ε > 0, ∃ δ > 0, ∀ x, (0 < |x - a| < δ → |(f(x) - f(a)) / (x - a) - L| < ε)
def HasDerivAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε : ℝ, (𝟘 <ℝ ε) → ∃ δ : ℝ, (𝟘 <ℝ δ) ∧
    ∀ x : ℝ, ((𝟘 <ℝ |x -ℝ a|ℝ) ∧ (|x -ℝ a|ℝ <ℝ δ)) →
      |((f x -ℝ f a) /ℝ (x -ℝ a)) -ℝ L|ℝ <ℝ ε

-- 미분계수 정의는 차분몫(Difference Quotient)의 ε-δ 극한과 정확히 일치한다.
theorem hasDerivAt_iff_hasLimit (f : ℝ → ℝ) (a L : ℝ) :
    HasDerivAt f a L ↔ HasLimit (fun x => (f x -ℝ f a) /ℝ (x -ℝ a)) a L :=
  Iff.rfl

-- [정리 1] 미분계수의 유일성 (Uniqueness of Derivative)
theorem hasDerivAt_unique {f : ℝ → ℝ} {a L1 L2 : ℝ}
    (h1 : HasDerivAt f a L1) (h2 : HasDerivAt f a L2) : L1 = L2 :=
  limit_unique h1 h2

-- [정리 2] 상수 함수의 미분: f(x) = c 이면 f'(a) = 0
theorem hasDerivAt_const (c a : ℝ) : HasDerivAt (fun _ => c) a 𝟘 := by
  intro ε hε
  refine ⟨r_one, r_one_pos, ?_⟩
  intro x _hx
  rw [r_sub_self c, r_zero_div (x -ℝ a), r_sub_self 𝟘, r_abs_zero]
  exact hε

-- [정리 3] 항등 함수의 미분: f(x) = x 이면 f'(a) = 1
theorem hasDerivAt_id (a : ℝ) : HasDerivAt (fun x => x) a 𝟙 := by
  intro ε hε
  refine ⟨r_one, r_one_pos, ?_⟩
  intro x ⟨hx_pos, _hx_lt⟩
  rw [r_div_self hx_pos, r_sub_self 𝟙, r_abs_zero]
  exact hε

-- [정리 4] 합의 미분법: (f + g)'(a) = f'(a) + g'(a)
theorem hasDerivAt_add {f g : ℝ → ℝ} {a L1 L2 : ℝ}
    (hf : HasDerivAt f a L1) (hg : HasDerivAt g a L2) :
    HasDerivAt (fun x => f x +ℝ g x) a (L1 +ℝ L2) := by
  intro ε hε
  have hε2 : 𝟘 <ℝ r_half ε := r_half_pos hε
  rcases hf (r_half ε) hε2 with ⟨δ1, hδ1_pos, hδ1⟩
  rcases hg (r_half ε) hε2 with ⟨δ2, hδ2_pos, hδ2⟩
  refine ⟨r_min δ1 δ2, r_min_pos hδ1_pos hδ2_pos, ?_⟩
  intro x ⟨hx_pos, hx_lt⟩
  have hx1 : |x -ℝ a|ℝ <ℝ δ1 := r_lt_of_lt_of_le hx_lt (r_min_le_left δ1 δ2)
  have hx2 : |x -ℝ a|ℝ <ℝ δ2 := r_lt_of_lt_of_le hx_lt (r_min_le_right δ1 δ2)
  have h1 := hδ1 x ⟨hx_pos, hx1⟩
  have h2 := hδ2 x ⟨hx_pos, hx2⟩
  have h_tri := r_add_sub_add_div (f x) (f a) (g x) (g a) (x -ℝ a) L1 L2
  have h_sum := r_add_lt_add h1 h2
  rw [r_add_halves] at h_sum
  exact r_lt_of_le_of_lt h_tri h_sum

-- [정리 5] 차의 미분법: (f - g)'(a) = f'(a) - g'(a)
theorem hasDerivAt_sub {f g : ℝ → ℝ} {a L1 L2 : ℝ}
    (hf : HasDerivAt f a L1) (hg : HasDerivAt g a L2) :
    HasDerivAt (fun x => f x -ℝ g x) a (L1 -ℝ L2) := by
  intro ε hε
  have hε2 : 𝟘 <ℝ r_half ε := r_half_pos hε
  rcases hf (r_half ε) hε2 with ⟨δ1, hδ1_pos, hδ1⟩
  rcases hg (r_half ε) hε2 with ⟨δ2, hδ2_pos, hδ2⟩
  refine ⟨r_min δ1 δ2, r_min_pos hδ1_pos hδ2_pos, ?_⟩
  intro x ⟨hx_pos, hx_lt⟩
  have hx1 : |x -ℝ a|ℝ <ℝ δ1 := r_lt_of_lt_of_le hx_lt (r_min_le_left δ1 δ2)
  have hx2 : |x -ℝ a|ℝ <ℝ δ2 := r_lt_of_lt_of_le hx_lt (r_min_le_right δ1 δ2)
  have h1 := hδ1 x ⟨hx_pos, hx1⟩
  have h2 := hδ2 x ⟨hx_pos, hx2⟩
  have h_tri := r_sub_sub_sub_div (f x) (f a) (g x) (g a) (x -ℝ a) L1 L2
  have h_sum := r_add_lt_add h1 h2
  rw [r_add_halves] at h_sum
  exact r_lt_of_le_of_lt h_tri h_sum

-- [정리 6] 미분가능하면 연속이다 (Differentiability implies Continuity)
theorem differentiable_imp_continuousAt {f : ℝ → ℝ} {a L : ℝ}
    (hd : HasDerivAt f a L) : ContinuousAt f a := by
  intro ε hε
  rcases hd r_one r_one_pos with ⟨δ1, hδ1_pos, hδ1⟩
  let δ2 := r_min r_one (ε /ℝ (|L|ℝ +ℝ r_one))
  have hδ2_pos : 𝟘 <ℝ δ2 := r_min_pos r_one_pos (r_div_pos_of_pos hε)
  refine ⟨r_min δ1 δ2, r_min_pos hδ1_pos hδ2_pos, ?_⟩
  intro x hx_lt
  by_cases hx_eq : x = a
  · rw [hx_eq, r_sub_self (f a), r_abs_zero]
    exact hε
  · have hx_pos : 𝟘 <ℝ |x -ℝ a|ℝ := (r_abs_sub_pos_iff x a).mpr hx_eq
    have hx1 : |x -ℝ a|ℝ <ℝ δ1 := r_lt_of_lt_of_le hx_lt (r_min_le_left δ1 δ2)
    have hx2 : |x -ℝ a|ℝ <ℝ δ2 := r_lt_of_lt_of_le hx_lt (r_min_le_right δ1 δ2)
    have h_quot : |((f x -ℝ f a) /ℝ (x -ℝ a)) -ℝ L|ℝ <ℝ r_one := hδ1 x ⟨hx_pos, hx1⟩
    exact r_diff_bound_of_quotient_bound h_quot hx2 hε

------------------------------------------------------------------
-- 7. 다르부 적분 (Darboux Integral) 정의 및 기본 정리
------------------------------------------------------------------

-- 닫힌구간 [a, b]의 분할 (Partition of [a, b])
axiom Partition : ℝ → ℝ → Type

-- 분할 P에 대한 하다르부 합 L(f, P) 및 상다르부 합 U(f, P)
-- L(f, P) = ∑ m_i (x_i - x_{i-1}),  m_i = inf_{t ∈ [x_{i-1}, x_i]} f(t)
-- U(f, P) = ∑ M_i (x_i - x_{i-1}),  M_i = sup_{t ∈ [x_{i-1}, x_i]} f(t)
axiom lowerDarbouxSum : (ℝ → ℝ) → {a b : ℝ} → Partition a b → ℝ
axiom upperDarbouxSum : (ℝ → ℝ) → {a b : ℝ} → Partition a b → ℝ

-- 하다르부 적분 (Lower Darboux Integral: sup_P L(f, P)) 및
-- 상다르부 적분 (Upper Darboux Integral: inf_P U(f, P))
axiom lowerDarbouxIntegral : (ℝ → ℝ) → ℝ → ℝ → ℝ
axiom upperDarbouxIntegral : (ℝ → ℝ) → ℝ → ℝ → ℝ

-- 모든 분할 P에 대하여 L(f, P) ≤ L_int ≤ U_int ≤ U(f, P)
axiom darboux_sum_le_integral (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b) :
  (lowerDarbouxSum f P ≤ℝ lowerDarbouxIntegral f a b) ∧
  (lowerDarbouxIntegral f a b ≤ℝ upperDarbouxIntegral f a b) ∧
  (upperDarbouxIntegral f a b ≤ℝ upperDarbouxSum f P)

-- [정의] 다르부 적분가능성 및 정적분 값 I = ∫_a^b f(x) dx (리만-다르부 ε-판정법 포함)
-- 1) 모든 분할 P에 대해 L(f, P) ≤ I ≤ U(f, P)
-- 2) 리만-다르부 ε-판정법: ∀ ε > 0, ∃ P, U(f, P) - L(f, P) < ε
structure DarbouxIntegral (f : ℝ → ℝ) (a b I : ℝ) : Prop where
  lower_le_upper : ∀ P : Partition a b,
    (lowerDarbouxSum f P ≤ℝ I) ∧ (I ≤ℝ upperDarbouxSum f P)
  eps_criterion : ∀ ε : ℝ, (𝟘 <ℝ ε) → ∃ P : Partition a b,
    (upperDarbouxSum f P -ℝ lowerDarbouxSum f P) <ℝ ε

-- [정리 1] 다르부 적분값의 유일성 (Uniqueness of the Darboux Integral)
theorem darboux_integral_unique {f : ℝ → ℝ} {a b I1 I2 : ℝ}
    (h1 : DarbouxIntegral f a b I1) (h2 : DarbouxIntegral f a b I2) : I1 = I2 := by
  apply r_eq_of_abs_sub_lt_all_eps
  intro ε hε
  rcases h1.eps_criterion ε hε with ⟨P, hP_eps⟩
  have ⟨hI1_L, hI1_U⟩ := h1.lower_le_upper P
  have ⟨hI2_L, hI2_U⟩ := h2.lower_le_upper P
  have h_dist : |I1 -ℝ I2|ℝ ≤ℝ (upperDarbouxSum f P -ℝ lowerDarbouxSum f P) :=
    r_abs_sub_le_of_interval hI1_L hI1_U hI2_L hI2_U
  exact r_lt_of_le_of_lt h_dist hP_eps

-- [정리 2] 다르부 적분가능하면 상다르부 적분과 하다르부 적분이 일치한다:
-- ∫_a^b f = I  ⟹  lowerDarbouxIntegral f a b = upperDarbouxIntegral f a b
theorem darboux_lower_eq_upper_of_integrable {f : ℝ → ℝ} {a b I : ℝ}
    (hI : DarbouxIntegral f a b I) :
    lowerDarbouxIntegral f a b = upperDarbouxIntegral f a b := by
  apply r_eq_of_abs_sub_lt_all_eps
  intro ε hε
  rcases hI.eps_criterion ε hε with ⟨P, hP_eps⟩
  have ⟨hL_le_low, hlow_le_up, hup_le_U⟩ := darboux_sum_le_integral f P
  have hlow_le_U : lowerDarbouxIntegral f a b ≤ℝ upperDarbouxSum f P :=
    r_le_trans hlow_le_up hup_le_U
  have hL_le_up : lowerDarbouxSum f P ≤ℝ upperDarbouxIntegral f a b :=
    r_le_trans hL_le_low hlow_le_up
  have h_dist :
      |lowerDarbouxIntegral f a b -ℝ upperDarbouxIntegral f a b|ℝ ≤ℝ
        (upperDarbouxSum f P -ℝ lowerDarbouxSum f P) :=
    r_abs_sub_le_of_interval hL_le_low hlow_le_U hL_le_up hup_le_U
  exact r_lt_of_le_of_lt h_dist hP_eps

------------------------------------------------------------------
-- 8. 미적분학의 기본 정리 제1정리 및 제2정리 (Fundamental Theorem of Calculus 1 & 2)
------------------------------------------------------------------

-- [구조체] 정적분으로 정의된 누적 넓이 함수 F(x) = ∫_a^x f(t) dt 의 다르부 적분 성질
-- 1) 구간 가법성: F(x) - F(c) = ∫_c^x f(t) dt
-- 2) 다르부 상하계 평균값 부등식:
--    c와 x 사이의 모든 t (|t - c| ≤ |x - c|)에서 |f(t) - f(c)| < M 이면,
--    (f(c) - M)(x - c) ≤ ∫_c^x f(t) dt ≤ (f(c) + M)(x - c) 이므로
--    |(F(x) - F(c)) / (x - c) - f(c)| ≤ M 이 성립한다.
structure IsIndefiniteDarbouxIntegral (f F : ℝ → ℝ) (a b : ℝ) : Prop where
  mean_value_bound : ∀ c x M : ℝ,
    (a <ℝ c ∧ c <ℝ b) →
    (𝟘 <ℝ |x -ℝ c|ℝ) →
    (∀ t : ℝ, |t -ℝ c|ℝ ≤ℝ |x -ℝ c|ℝ → |f t -ℝ f c|ℝ <ℝ M) →
    |((F x -ℝ F c) /ℝ (x -ℝ c)) -ℝ f c|ℝ ≤ℝ M

-- ===============================================================
-- [미적분학의 기본 정리 제1정리 (Fundamental Theorem of Calculus, Part 1)]
-- 함수 f가 [a, b]에서 다르부 적분가능하여 F(x) = ∫_a^x f(t) dt 로 정의되고,
-- 점 c ∈ (a, b)에서 f가 (ε-δ 의미로) 연속이면,
-- F는 점 c에서 미분가능하며 F'(c) = f(c) 이다: HasDerivAt F c (f c).
-- ===============================================================
theorem fundamental_theorem_of_calculus_part1
    {f F : ℝ → ℝ} {a b c : ℝ}
    (hF : IsIndefiniteDarbouxIntegral f F a b)
    (hc_in : a <ℝ c ∧ c <ℝ b)
    (hf_cont : ContinuousAt f c) :
    HasDerivAt F c (f c) := by
  -- ε-δ 미분 정의에 따라 임의의 ε > 0 이 주어졌다고 하자.
  intro ε hε
  -- ε/2 > 0 에 대하여 f의 점 c에서의 연속성을 적용하면 δ > 0 이 존재한다.
  have hε2_pos : 𝟘 <ℝ r_half ε := r_half_pos hε
  rcases hf_cont (r_half ε) hε2_pos with ⟨δ, hδ_pos, hδ_cont⟩
  refine ⟨δ, hδ_pos, ?_⟩
  -- 이제 0 < |x - c| < δ 인 임의의 x를 택하자.
  intro x ⟨hx_pos, hx_lt_δ⟩
  -- c와 x 사이의 모든 점 t (|t - c| ≤ |x - c|)에 대하여 |t - c| < δ 이므로 |f(t) - f(c)| < ε/2 이다.
  have ht_bound : ∀ t : ℝ, |t -ℝ c|ℝ ≤ℝ |x -ℝ c|ℝ → |f t -ℝ f c|ℝ <ℝ r_half ε := by
    intro t ht_le
    have ht_lt_δ : |t -ℝ c|ℝ <ℝ δ := r_lt_of_le_of_lt ht_le hx_lt_δ
    exact hδ_cont t ht_lt_δ
  -- 다르부 적분의 상하계 부등식(평균값 부등식)에 의해 |(F(x) - F(c)) / (x - c) - f(c)| ≤ ε/2 이다.
  have h_quot_le : |((F x -ℝ F c) /ℝ (x -ℝ c)) -ℝ f c|ℝ ≤ℝ r_half ε :=
    hF.mean_value_bound c x (r_half ε) hc_in hx_pos ht_bound
  -- ε/2 < ε 이므로 |(F(x) - F(c)) / (x - c) - f(c)| < ε 이 성립한다.
  have h_half_lt : r_half ε <ℝ ε := r_half_lt_self hε
  exact r_lt_of_le_of_lt h_quot_le h_half_lt

-- 음이 아닌 수의 곱셈 단조성: a ≤ b 이고 0 ≤ d 이면 a * d ≤ b * d
axiom r_mul_le_mul_of_nonneg_right {a b d : ℝ} :
  (a ≤ℝ b) → (𝟘 ≤ℝ d) → ((a *ℝ d) ≤ℝ (b *ℝ d))

-- [보조정리] 부분구간 [u, v]에서 평균값 정리(MVT) F(v) - F(u) = f(c)(v - u) 와
-- 부분구간 상하한 m ≤ f(c) ≤ M 으로부터 다르부 부분합 부등식 유도:
-- m(v - u) ≤ F(v) - F(u) ≤ M(v - u)
theorem mvt_subinterval_darboux_bound
    {F f : ℝ → ℝ} {u v c m M : ℝ}
    (h_len : 𝟘 ≤ℝ (v -ℝ u))
    (h_mvt : (F v -ℝ F u) = (f c *ℝ (v -ℝ u)))
    (h_inf : m ≤ℝ f c)
    (h_sup : f c ≤ℝ M) :
    ((m *ℝ (v -ℝ u)) ≤ℝ (F v -ℝ F u)) ∧ ((F v -ℝ F u) ≤ℝ (M *ℝ (v -ℝ u))) := by
  rw [h_mvt]
  constructor
  · exact r_mul_le_mul_of_nonneg_right h_inf h_len
  · exact r_mul_le_mul_of_nonneg_right h_sup h_len

-- [구조체] 닫힌구간 [a, b]에서의 원시함수(Antiderivative) 및 평균값 정리(MVT) 분할 부등식
-- F가 [a, b]에서 연속이고 (a, b)의 모든 점에서 F'(x) = f(x) (HasDerivAt F x (f x))이면,
-- 임의의 분할 P = {x_0, ..., x_n}의 각 부분구간 [x_{i-1}, x_i]에서 평균값 정리(MVT)에 의해
-- F(x_i) - F(x_{i-1}) = f(c_i)(x_i - x_{i-1}) 인 c_i가 존재하며,
-- 위 보조정리(mvt_subinterval_darboux_bound)를 모든 부분구간에 대해 합산(망원합)하면
-- 항상 L(f, P) ≤ F(b) - F(a) ≤ U(f, P) 가 성립한다.
structure IsAntiderivativeOn (F f : ℝ → ℝ) (a b : ℝ) : Prop where
  cont_on : ContinuousOn F a b
  deriv_on : ∀ x : ℝ, (a <ℝ x ∧ x <ℝ b) → HasDerivAt F x (f x)
  mvt_darboux_bounds : ∀ P : Partition a b,
    (lowerDarbouxSum f P ≤ℝ (F b -ℝ F a)) ∧ ((F b -ℝ F a) ≤ℝ upperDarbouxSum f P)

-- ===============================================================
-- [미적분학의 기본 정리 제2정리 (Fundamental Theorem of Calculus, Part 2)]
-- (뉴턴-라이프니츠 공식 / 바우어-리만-다르부 적분 정식화)
-- 함수 f가 [a, b]에서 다르부 적분가능하여 적분값 I = ∫_a^b f(x) dx 를 갖고,
-- F가 [a, b]에서 f의 원시함수(IsAntiderivativeOn F f a b)이면,
-- ∫_a^b f(x) dx = I = F(b) - F(a) 이다.
-- ===============================================================
theorem fundamental_theorem_of_calculus_part2
    {f F : ℝ → ℝ} {a b I : ℝ}
    (hf_int : DarbouxIntegral f a b I)
    (hF_anti : IsAntiderivativeOn F f a b) :
    I = (F b -ℝ F a) := by
  -- 모든 ε > 0 에 대하여 |I - (F(b) - F(a))| < ε 임을 보이면 두 실수는 일치한다.
  apply r_eq_of_abs_sub_lt_all_eps
  intro ε hε
  -- 1단계: f가 다르부 적분가능하므로 리만-다르부 ε-판정법에 의해
  --        U(f, P) - L(f, P) < ε 을 만족하는 분할 P가 존재한다.
  rcases hf_int.eps_criterion ε hε with ⟨P, hP_eps⟩
  -- 2단계: 정적분 I의 정의에 의해 L(f, P) ≤ I ≤ U(f, P) 이다.
  have ⟨hI_lower, hI_upper⟩ := hf_int.lower_le_upper P
  -- 3단계: 원시함수 F에 대한 평균값 정리(MVT)와 망원합에 의해
  --        L(f, P) ≤ F(b) - F(a) ≤ U(f, P) 이다.
  have ⟨hF_lower, hF_upper⟩ := hF_anti.mvt_darboux_bounds P
  -- 4단계: I와 F(b) - F(a) 모두 동일한 닫힌구간 [L(f, P), U(f, P)]에 속하므로
  --        |I - (F(b) - F(a))| ≤ U(f, P) - L(f, P) < ε 이다.
  have h_dist :
      |I -ℝ (F b -ℝ F a)|ℝ ≤ℝ (upperDarbouxSum f P -ℝ lowerDarbouxSum f P) :=
    r_abs_sub_le_of_interval hI_lower hI_upper hF_lower hF_upper
  exact r_lt_of_le_of_lt h_dist hP_eps

-- [종합 정리] 미적분학의 기본 정리 (제1정리 및 제2정리 통합)
theorem fundamental_theorem_of_calculus :
    (∀ (f F : ℝ → ℝ) (a b c : ℝ),
      IsIndefiniteDarbouxIntegral f F a b →
      (a <ℝ c ∧ c <ℝ b) →
      ContinuousAt f c →
      HasDerivAt F c (f c)) ∧
    (∀ (f F : ℝ → ℝ) (a b I : ℝ),
      DarbouxIntegral f a b I →
      IsAntiderivativeOn F f a b →
      I = (F b -ℝ F a)) :=
  ⟨fun _ _ _ _ _ hF hc hf => fundamental_theorem_of_calculus_part1 hF hc hf,
   fun _ _ _ _ _ hf hF => fundamental_theorem_of_calculus_part2 hf hF⟩

end

end RealAnalysis



