import tactic.induction
import order.min_max

abbreviation vname  := string
abbreviation val    := ℕ
abbreviation pstate := vname → val

inductive aexp : Type
| N    : ℕ → aexp
| V    : vname → aexp
| Plus : aexp → aexp → aexp

open aexp

def aval : aexp → pstate → val
| (N n)        _ := n
| (V x)        s := s x
| (Plus a₁ a₂) s := (aval a₁ s) + (aval a₂ s)

def state_update (s : pstate) (x : vname) (v : val) : pstate :=
  λ y, if (y = x) then v else s y

notation s `[` x ` ↦ ` v `]`:100 := state_update s x v
notation   `[` x ` ↦ ` v `]` := (λ _, 0 ) [x ↦ v]

/--
Lemma tecnico utile all'utilizzo del tattico `simp` per l'applicazione degli stati
-/
@[simp] def apply_state_update_pos {x y : vname} {s : pstate} {v : val} :
  (y = x) → s[x ↦ v] y = v := 
begin
  intro,
  dsimp[state_update],
  apply if_pos,
  assumption
end

/--
Lemma tecnico utile all'utilizzo del tattico `simp` per l'applicazione degli stati
-/
@[simp] def apply_state_update_neg {x y : vname} {s : pstate} {v : val} :
  ¬(y = x) → s[x ↦ v] y = (s y) :=
begin
  intro,
  dsimp[state_update],
  apply if_neg,
  assumption
end

inductive bexp : Type
| Bc   : bool → bexp
| Not  : bexp → bexp
| And  : bexp → bexp → bexp
| Less : aexp → aexp → bexp

open bexp

def bval : bexp → pstate → bool
| (Bc v)       _ := v
| (Not b)      s := ¬(bval b s)
| (And b₁ b₂)  s := (bval b₁ s) ∧ (bval b₂ s)
| (Less a₁ a₂) s := (aval a₁ s) < (aval a₂ s)

abbreviation lv := ℕ

def sec : vname → lv :=
  λ (x : vname), x.length

def secₐ : aexp → lv
| (N n)        := 0
| (V x)        := sec x
| (Plus a₁ a₂) := max (secₐ a₁) (secₐ a₂)

def sec₆ : bexp → lv
| (Bc v)       := 0
| (Not b)      := sec₆ b
| (And b₁ b₂)  := max (sec₆ b₁) (sec₆ b₂)
| (Less a₁ a₂) := max (secₐ a₁) (secₐ a₂)

notation s ` = ` t ` ⦅<= ` l `⦆` := ∀ (z : vname), (sec z <= l) → s z = t z
notation s ` = ` t ` ⦅< ` l `⦆` := ∀ (z : vname), (sec z < l) → s z = t z

namespace state_eq_below_lv

lemma refl {s : pstate} {l : lv} : s = s ⦅< l⦆ :=
begin
  intros,
  reflexivity
end

@[trans] lemma trans {s₁ s₂ s₃ : pstate} {l : lv} : 
  s₁ = s₂ ⦅< l⦆ →  s₂ = s₃ ⦅< l⦆ → s₁ = s₃ ⦅< l⦆ :=
begin
  intros _ _ x _,

  have : s₁ x = s₂ x, from ‹s₁ = s₂ ⦅< l⦆› x ‹sec x < l›,
  have : s₂ x = s₃ x, from ‹s₂ = s₃ ⦅< l⦆› x ‹sec x < l›,

  show s₁ x = s₃ x, from trans ‹s₁ x = s₂ x› ‹s₂ x = s₃ x›
end

end state_eq_below_lv

open state_eq_below_lv

lemma noninterference_aexp {s t : pstate} {l : lv} {a : aexp} :
  s = t ⦅<= l⦆ → (secₐ a <= l) → (aval a s = aval a t) :=
begin
  intros,
  induction' a,
    case N : {
      trivial
    },
    case V : x {
      dsimp[secₐ] at *,

      show aval (V x) s = aval (V x) t, by
        simp_rw[aval, ‹s = t ⦅<= l⦆› x ‹sec x ≤ l›]
    },
    case Plus : a₁ a₂ ih₁ ih₂ {
      dsimp[secₐ] at *,

      have : (secₐ a₁ <= l) ∧ (secₐ a₂ <= l), by 
        simpa using ‹max (secₐ a₁) (secₐ a₂) ≤ l›,
      cases' ‹(secₐ a₁ <= l) ∧ (secₐ a₂ <= l)›,

      have : aval a₁ s = aval a₁ t, from ih₁ ‹s = t ⦅<= l⦆› ‹(secₐ a₁ <= l)›,
      have : aval a₂ s = aval a₂ t, from ih₂ ‹s = t ⦅<= l⦆› ‹(secₐ a₂ <= l)›,

      show aval (Plus a₁ a₂) s = aval (Plus a₁ a₂) t, by
        simp_rw[aval, ‹aval a₁ s = aval a₁ t›, ‹aval a₂ s = aval a₂ t›]
    }
end

lemma noninterference_bexp {s t : pstate} {l : lv} {b : bexp} :
  s = t ⦅<= l⦆ → (sec₆ b <= l) → (bval b s = bval b t) :=
begin
  intros,
  induction' b,
    case Bc : {
      trivial
    },
    case Not : {
      dsimp[sec₆] at *,

      have : bval b s = bval b t, from ih ‹s = t ⦅<= l⦆› ‹sec₆ b ≤ l›,

      show bval (Not b) s = bval (Not b) t, by 
        simp_rw[bval, ‹bval b s = bval b t›]
    },
    case And : b₁ b₂ ih₁ ih₂ {
      dsimp[sec₆] at *,

      have : (sec₆ b₁ <= l) ∧ (sec₆ b₂ <= l), by
        simpa using ‹max (sec₆ b₁) (sec₆ b₂) <= l›,
      cases' ‹(sec₆ b₁ <= l) ∧ (sec₆ b₂ <= l)›,

      have : bval b₁ s = bval b₁ t, from ih₁ ‹s = t ⦅<= l⦆› ‹sec₆ b₁ ≤ l›,
      have : bval b₂ s = bval b₂ t, from ih₂ ‹s = t ⦅<= l⦆› ‹sec₆ b₂ ≤ l›,

      show bval (And b₁ b₂) s = bval (And b₁ b₂) t, by
        simp_rw[bval, ‹bval b₁ s = bval b₁ t›, ‹bval b₂ s = bval b₂ t›]
    },
    case Less : a₁ a₂ {
      dsimp[sec₆] at *,

      have : (secₐ a₁ <= l) ∧ (secₐ a₂ <= l), by
        simpa using ‹max (secₐ a₁) (secₐ a₂) <= l›,
      cases' ‹(secₐ a₁ <= l) ∧ (secₐ a₂ <= l)›,

      have : aval a₁ s = aval a₁ t, from 
        noninterference_aexp ‹s = t ⦅<= l⦆› ‹(secₐ a₁ <= l)›,
      have : aval a₂ s = aval a₂ t, from 
        noninterference_aexp ‹s = t ⦅<= l⦆› ‹(secₐ a₂ <= l)›,

      show bval (Less a₁ a₂) s = bval (Less a₁ a₂) t, by
        simp_rw[bval, ‹aval a₁ s = aval a₁ t›, ‹aval a₂ s = aval a₂ t›]
    }
end

inductive com : Type
| SKIP   : com
| Assign : vname → aexp → com
| Seq    : com → com → com
| If     : bexp → com → com → com
| While  : bexp → com → com

infix ` ::= `:68                                    := com.Assign
infix ` ;; `:67                                     := com.Seq
notation `IF `:0 b ` THEN `:0 c₁ ` ELSE `:68 c₂:68  := com.If b c₁ c₂
notation `WHILE `:0 b ` DO `:68 c:68                := com.While b c

abbreviation conf := com × pstate

open com

inductive big_step : conf → pstate → Prop
| Skip {s : pstate} : 
  big_step (SKIP, s) s

| Assign {s : pstate} {x : vname} {a : aexp} : 
  big_step (x ::= a, s) (s[x ↦ aval a s])

| Seq {c₁ c₂ : com} {s₁ s₂ s₃ : pstate} : 
  big_step (c₁, s₁) s₂ →
  big_step (c₂, s₂) s₃ → 
  big_step (c₁ ;; c₂, s₁) s₃

| IfTrue {b : bexp} {c₁ c₂ : com} {s t : pstate}  : 
  bval b s →
  big_step (c₁, s) t → 
  big_step (IF b THEN c₁ ELSE c₂, s) t

| IfFalse {b : bexp}  {c₁ c₂ : com} {s t : pstate} :
  ¬ bval b s → 
  big_step (c₂, s) t →
  big_step (IF b THEN c₁ ELSE c₂, s) t

| WhileFalse {b : bexp} {c : com} {s : pstate} :
  ¬ bval b s →
  big_step (WHILE b DO c, s) s

| WhileTrue {b : bexp} {c : com} {s₁ s₂ s₃ : pstate } :
  bval b s₁ →
  big_step (c, s₁) s₂ →
  big_step (WHILE b DO c, s₂) s₃ →
  big_step (WHILE b DO c, s₁) s₃

infix ` ⟹ `:70 := big_step

open big_step

inductive sec_type : lv → com → Prop
| Skip {l : lv} : 
  sec_type l SKIP

| Assign {x : vname} {a : aexp} {l : lv} :
  secₐ a <= sec x →
  l <= sec x →
  sec_type l (x ::= a)

| Seq {l : lv} {c₁ c₂ : com} :
  sec_type l c₁ →
  sec_type l c₂ →
  sec_type l (c₁ ;; c₂)

| If {b : bexp} {l : lv} {c₁ c₂ : com} :
  sec_type (max (sec₆ b) l) c₁ →
  sec_type (max (sec₆ b) l) c₂ →
  sec_type l (IF b THEN c₁ ELSE c₂)

| While {b : bexp} {l : lv} {c : com} :
  sec_type (max (sec₆ b) l) c →
  sec_type l (WHILE b DO c)

infix ` ⊢ₛ `:50 := sec_type

open sec_type

lemma anti_monotonicity {l l' : lv} {c : com} :
  (l ⊢ₛ c) → (l' <= l) → (l' ⊢ₛ c) :=
begin
  intros,
  induction' ‹l ⊢ₛ c›,
    case Skip : {
      show l' ⊢ₛ SKIP, from Skip
    },
    case Assign : {
      have : l' <= sec x, from le_trans ‹l' <= l› ‹l <= sec x›,

      show l' ⊢ₛ x ::= a, from Assign ‹secₐ a ≤ sec x› ‹l' <= sec x›
    },
    case Seq : l c₁ c₂ _ _ ih₁ ih₂ {
      have : l' ⊢ₛ c₁, from ih₁ ‹l' <= l›,
      have : l' ⊢ₛ c₂, from ih₂ ‹l' <= l›,

      show l' ⊢ₛ c₁ ;; c₂, from Seq ‹l' ⊢ₛ c₁› ‹ l' ⊢ₛ c₂›
    },
    case If : _ _ c₁ c₂ _ _ ih₁ ih₂ {
      have : max (sec₆ b) l' <= max (sec₆ b) l, from max_le_max (le_refl _) ‹l' ≤ l›,
      
      have : max (sec₆ b) l' ⊢ₛ c₁, from ih₁ ‹max (sec₆ b) l' <= max (sec₆ b) l›,
      have : max (sec₆ b) l' ⊢ₛ c₂, from ih₂ ‹max (sec₆ b) l' <= max (sec₆ b) l›,

      show l' ⊢ₛ IF b THEN c₁ ELSE c₂, from 
        If ‹max (sec₆ b) l' ⊢ₛ c₁› ‹max (sec₆ b) l' ⊢ₛ c₂›
    },
    case While : {
      have : max (sec₆ b) l' <= max (sec₆ b) l, from max_le_max (le_refl _) ‹l' ≤ l›,

      have : max (sec₆ b) l' ⊢ₛ c, from ih ‹max (sec₆ b) l' <= max (sec₆ b) l›,

      show l' ⊢ₛ WHILE b DO c, from While ‹max (sec₆ b) l' ⊢ₛ c›
    }
end

lemma confinement {c : com} {s t : pstate} {l : lv} :
  (c, s) ⟹ t → (l ⊢ₛ c) →  s = t ⦅< l⦆ :=
begin
  intros _ _,
  induction' ‹(c, s) ⟹ t›,
    case Skip : {
      show t = t ⦅< l⦆, from refl
    },
    case Assign : { -- TODO: migliorabile?
      intros,

      cases' ‹l ⊢ₛ x ::= a›,
    
      have : (z = x) ∨ ¬(z = x), from em (z = x),
      cases' ‹(z = x) ∨ ¬(z = x)›,
        case or.inl : {
          rw ‹z = x› at *,
          have : ¬(sec x < l), from not_lt_of_le ‹l ≤ sec x›,
          contradiction
        },
        case or.inr : {
          show t z = t[x ↦ aval a t] z, by simp[‹¬(z = x)›]
        }
    },
    case Seq :  _ _ s s' t _ _ ih₁ ih₂{
      cases' ‹l ⊢ₛ c₁ ;; c₂›,
      
      have : s = s' ⦅< l⦆, from ih₁ ‹l ⊢ₛ c₁›,
      have : s' = t ⦅< l⦆, from ih₂ ‹l ⊢ₛ c₂›,

      show s = t ⦅< l⦆, from trans ‹s = s' ⦅< l⦆› ‹s' = t ⦅< l⦆›
    },
    case IfTrue : {
      cases' ‹l ⊢ₛ IF b THEN c₁ ELSE c₂›,

      have : l <= max (sec₆ b) l, from le_max_right (sec₆ b) l,
      have : l ⊢ₛ c₁, from anti_monotonicity ‹max (sec₆ b) l ⊢ₛ c₁› ‹l <= max (sec₆ b) l›,

      show s = t ⦅< l⦆, from ih ‹l ⊢ₛ c₁›
    },
    case IfFalse : {
      cases' ‹l ⊢ₛ IF b THEN c₁ ELSE c₂›,

      have : l <= max (sec₆ b) l, from le_max_right (sec₆ b) l,
      have : l ⊢ₛ c₂, from anti_monotonicity ‹max (sec₆ b) l ⊢ₛ c₂› ‹l <= max (sec₆ b) l›,

      show s = t ⦅< l⦆, from ih ‹l ⊢ₛ c₂›
    },
    case WhileTrue : _ _ s s' t _ _ _ ih₁ ih₂ {
      cases' ‹l ⊢ₛ WHILE b DO c›,

      have : l <= max (sec₆ b) l, from le_max_right (sec₆ b) l,
      have : l ⊢ₛ c, from anti_monotonicity ‹max (sec₆ b) l ⊢ₛ c› ‹l <= max (sec₆ b) l›,

      have : s = s' ⦅< l⦆, from ih₁ ‹l ⊢ₛ c›,
      have : s' = t ⦅< l⦆, from ih₂ (While ‹max (sec₆ b) l ⊢ₛ c›),

      show s = t ⦅< l⦆, from trans ‹s = s' ⦅< l⦆› ‹s'= t ⦅< l⦆›
    },
    case WhileFalse : {
      show t = t ⦅< l⦆, from refl
    }
end

theorem noninterference {c : com} {s s' t t' : pstate} {l : lv}:
  (c, s) ⟹ s' → (c, t) ⟹ t' → (0 ⊢ₛ c) → s = t ⦅<= l⦆ → s' = t' ⦅<= l⦆ :=
begin
  intros _ _ _ _,
  induction' ‹(c, s) ⟹ s'›,
    case Skip : { 
      cases' ‹(SKIP, t) ⟹ t'›,

      show s' = t' ⦅<= l⦆, by assumption
    },
    case Assign : s _ _ { -- TODO: migliorabile?
      intros,
      cases' ‹(x ::= a, t) ⟹ t'› with _ t _,
      cases' ‹0 ⊢ₛ x ::= a›,

      have : (sec x <= l) ∨ (sec x > l), from le_or_lt (sec x) l,
      cases' ‹(sec x <= l) ∨ (sec x > l)›,
        case or.inl : { -- sec x <= l
          have : (z = x) ∨ ¬(z = x), from em (z = x),
          cases' ‹(z = x) ∨ ¬(z = x)›,
            case or.inl : {
              simp[‹z = x›],

              have : secₐ a <= l, from trans ‹secₐ a ≤ sec x› ‹sec x ≤ l›,
              
              show aval a s = aval a t, from 
                noninterference_aexp ‹s = t ⦅<= l⦆› ‹secₐ a <= l›
            },
            case or.inr : {
              simp[‹¬(z = x)›],

              show s z = t z, from ‹s = t ⦅<= l⦆› z ‹sec z ≤ l› 
            }
        },
        case or.inr : { -- sec x > l
          have : (z = x) ∨ ¬(z = x), from em (z = x),
          cases' ‹(z = x) ∨ ¬(z = x)›,
          case or.inl : {
              rw[‹z = x›] at *,
              have : ¬(sec x <= l), from not_le_of_gt ‹sec x > l›,
              contradiction
            },
            case or.inr : {
              simp[‹¬(z = x)›],

              show s z = t z, from ‹s = t ⦅<= l⦆› z ‹sec z ≤ l› 
            }
        }
    },
    case Seq : { sorry },
    case IfTrue : { sorry },
    case IfFalse : { sorry },
    case WhileTrue : { sorry },
    case WhileFalse : { sorry } 
end