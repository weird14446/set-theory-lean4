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
