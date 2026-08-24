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
