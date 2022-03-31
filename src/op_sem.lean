import IMP
import tactic.induction

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

namespace big_step

namespace rule_inversion

lemma skip {s t : pstate} (h : (SKIP, s) ⟹ t) : 
  t = s :=
begin cases ‹(SKIP, s) ⟹ t›, reflexivity end

lemma assign {x : vname} {a : aexp} {s t : pstate} (h : (x ::= a, s) ⟹ t) : 
  t = (s[x ↦ aval a s]) :=
begin cases ‹(x ::= a, s) ⟹ t›, reflexivity end 

lemma seq {c₁ c₂ : com} {s₁ s₃ : pstate} (h : (c₁ ;; c₂, s₁) ⟹ s₃) : 
  ∃ (s₂ : pstate), (c₁, s₁) ⟹ s₂ ∧ (c₂, s₂) ⟹ s₃ :=
begin
  cases ‹(c₁ ;; c₂, s₁) ⟹ s₃›,
  apply exists.intro,
  split,
    exact ‹(c₁, s₁) ⟹ h_s₂›,
    exact ‹(c₂, h_s₂) ⟹ s₃›
end

lemma ifte {b : bexp} {c₁ c₂ : com} {s t : pstate} (h : (IF b THEN c₁ ELSE c₂, s) ⟹ t) :
  (bval b s ∧ (c₁, s) ⟹ t) ∨ (¬bval b s ∧ (c₂, s) ⟹ t) :=
begin
  cases ‹(IF b THEN c₁ ELSE c₂, s) ⟹ t›,
    case IfTrue : { exact or.inl ⟨‹↥(bval b s)›, ‹(c₁, s) ⟹ t›⟩ },
    case IfFalse : { exact or.inr ⟨‹¬↥(bval b s)›, ‹(c₂, s) ⟹ t›⟩ }
end

lemma while {b : bexp} {c : com} {s t : pstate} (h : (WHILE b DO c, s) ⟹ t) :
  (¬bval b s ∧ t = s) ∨ (bval b s ∧ ∃ (s₁ : pstate), (c, s) ⟹ s₁ ∧ (WHILE b DO c, s₁) ⟹ t) :=
begin
  cases ‹(WHILE b DO c, s) ⟹ t›,
    case WhileTrue : { 
      have : ∃ (s₁ : pstate), (c, s) ⟹ s₁ ∧ (WHILE b DO c, s₁) ⟹ t := 
        ⟨h_s₂, ⟨‹(c, s) ⟹ h_s₂›, ‹(WHILE b DO c, h_s₂) ⟹ t›⟩⟩,
      exact or.inr ⟨‹↥(bval b s)›, ‹∃ (s₁ : pstate), (c, s) ⟹ s₁ ∧ (WHILE b DO c, s₁) ⟹ t›⟩ 
    },
    case WhileFalse : { exact or.inl ⟨‹¬↥(bval b s)›, rfl⟩ }
end

end rule_inversion

lemma seq_assoc {c₁ c₂ c₃ : com} {s t : pstate} :
  (c₁ ;; c₂ ;; c₃, s) ⟹ t ↔ (c₁ ;; (c₂ ;; c₃), s) ⟹ t :=
begin
  split,
    {
      assume : (c₁ ;; c₂ ;; c₃, s) ⟹ t,
      have : ∃ s₁, (c₁ ;; c₂, s) ⟹ s₁ ∧ (c₃, s₁) ⟹ t := 
        rule_inversion.seq ‹(c₁ ;; c₂ ;; c₃, s) ⟹ t›,
      cases ‹∃ s₁, (c₁ ;; c₂, s) ⟹ s₁ ∧ (c₃, s₁) ⟹ t› with s₁,
      cases ‹(c₁ ;; c₂, s) ⟹ s₁ ∧ (c₃, s₁) ⟹ t›,
      have : ∃ s₂, (c₁, s) ⟹ s₂ ∧ (c₂, s₂) ⟹ s₁ := 
        rule_inversion.seq ‹(c₁ ;; c₂, s) ⟹ s₁›,
      cases ‹∃ s₂, (c₁, s) ⟹ s₂ ∧ (c₂, s₂) ⟹ s₁› with s₂,
      cases ‹(c₁, s) ⟹ s₂ ∧ (c₂, s₂) ⟹ s₁›,
      show (c₁ ;; (c₂ ;; c₃), s) ⟹ t, from
        Seq ‹(c₁, s) ⟹ s₂› (Seq ‹(c₂, s₂) ⟹ s₁› ‹(c₃, s₁) ⟹ t›)
    },
    {
      assume : (c₁ ;; (c₂ ;; c₃), s) ⟹ t,
      have : ∃ s₁, (c₁, s) ⟹ s₁ ∧ (c₂ ;; c₃, s₁) ⟹ t :=
        rule_inversion.seq ‹(c₁ ;; (c₂ ;; c₃), s) ⟹ t›,
      cases ‹∃ s₁, (c₁, s) ⟹ s₁ ∧ (c₂ ;; c₃, s₁) ⟹ t› with s₁,
      cases ‹(c₁, s) ⟹ s₁ ∧ (c₂ ;; c₃, s₁) ⟹ t›,
      have : ∃ s₂, (c₂, s₁) ⟹ s₂ ∧ (c₃, s₂) ⟹ t :=
        rule_inversion.seq ‹(c₂ ;; c₃, s₁) ⟹ t›,
      cases ‹∃ s₂, (c₂, s₁) ⟹ s₂ ∧ (c₃, s₂) ⟹ t› with s₂,
      cases ‹(c₂, s₁) ⟹ s₂ ∧ (c₃, s₂) ⟹ t›,
      show (c₁ ;; c₂ ;; c₃, s) ⟹ t, from
        Seq (Seq ‹(c₁, s) ⟹ s₁› ‹(c₂, s₁) ⟹ s₂›) ‹(c₃, s₂) ⟹ t›
    }
end

notation c₁ `∼` c₂ := ∀{s t : pstate}, (c₁, s) ⟹ t = (c₂, s) ⟹ t

lemma eq_while_ifwhile {b : bexp} {c : com} : WHILE b DO c ∼ IF b THEN (c ;; WHILE b DO c) ELSE SKIP :=
begin
  intros,
  apply iff.to_eq,
  split,
    { 
      intros,
      cases ‹(WHILE b DO c, s) ⟹ t›,
        case WhileFalse : {
          show  (IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s) ⟹ s, from
            IfFalse ‹¬↥(bval b s)› Skip
        },
        case WhileTrue : {
          rename ᾰ_s₂ → s',
          show (IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s) ⟹ t, from
            IfTrue ‹↥(bval b s)› (Seq ‹(c, s) ⟹ s'› ‹(WHILE b DO c, s') ⟹ t›)
        }
    },
    {
      intros,
      cases ‹(IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s) ⟹ t›,
        case IfTrue : {
          cases ‹(c ;; WHILE b DO c, s) ⟹ t›,
          rename ᾰ_ᾰ_1_s₂ → s',
          show (WHILE b DO c, s) ⟹ t, from
            WhileTrue ‹↥(bval b s)› ‹(c, s) ⟹ s'› ‹(WHILE b DO c, s') ⟹ t›
        },
        case IfFalse : {
          cases ‹(SKIP, s) ⟹ t›,
          show (WHILE b DO c, s) ⟹ s, from
            WhileFalse ‹¬↥(bval b s)›
        }
    }
end

theorem deterministic {c : com} {s : pstate} :
   ∀{t : pstate}, (c, s) ⟹ t → ∀{r : pstate}, (c, s) ⟹ r → (t = r) :=
begin
  assume t : pstate,
  assume : (c, s) ⟹ t,
  induction ‹(c, s) ⟹ t›,
    case Skip : s {
      assume r : pstate,
      assume : (SKIP, s) ⟹ r,
      cases ‹(SKIP, s) ⟹ r›,
      reflexivity
    },
    case Assign : s x a {
      assume r : pstate,
      assume : (x ::= a, s) ⟹ r, 
      cases ‹(x ::= a, s) ⟹ r›,
      reflexivity
    },
    case Seq : c₁ c₂ s s₁ t _ _ ih₁ ih₂ {
      assume r : pstate,
      assume : (c₁ ;; c₂, s) ⟹ r,
      cases ‹(c₁ ;; c₂, s) ⟹ r›, rename this_s₂ → s₂,
      have : (s₂ = s₁) := (ih₁ ‹(c₁, s) ⟹ s₂›).symm,
      rw ‹s₂ = s₁› at *,
      exact ih₂ ‹(c₂, s₁) ⟹ r›
    },
    case IfTrue : b c₁ c₂ s _ _ _ ih {
      assume r : pstate,
      assume : (IF b THEN c₁ ELSE c₂, s) ⟹ r,
      cases ‹(IF b THEN c₁ ELSE c₂, s) ⟹ r›,
        case IfTrue : { exact ih ‹(c₁, s) ⟹ r› },
        case IfFalse : { contradiction }
    },
    case IfFalse : b c₁ c₂ s _ _ _ ih {
      assume r : pstate,
      assume : (IF b THEN c₁ ELSE c₂, s) ⟹ r,
      cases ‹(IF b THEN c₁ ELSE c₂, s) ⟹ r›,
        case IfTrue : { contradiction },
        case IfFalse : { exact ih ‹(c₂, s) ⟹ r› }
    },
    case WhileTrue : b c s s₁ _ _ _ _ ih₁ ih₂ {
      assume r : pstate,
      assume : (WHILE b DO c, s) ⟹ r,
      cases ‹(WHILE b DO c, s) ⟹ r›,
        case WhileTrue : { 
          rename this_s₂ → s₂,
          have : (s₂ = s₁) := (ih₁ ‹(c, s) ⟹ s₂›).symm,
          rw ‹s₂ = s₁› at *,
          exact ih₂ ‹(WHILE b DO c, s₁) ⟹ r›
        },
        case WhileFalse : { contradiction }
    },
    case WhileFalse : b c s {
      assume r : pstate,
      assume : (WHILE b DO c, s) ⟹ r,
      cases ‹(WHILE b DO c, s) ⟹ r›,
        case WhileTrue : { contradiction },
        case WhileFalse : { reflexivity }
    }
end

end big_step

inductive small_step : conf → conf → Prop
| Assign  {s : pstate} {x : vname} {a : aexp} :
  small_step (x ::= a, s) (SKIP, s[x ↦ aval a s])

| Seq1 {c₂ : com} {s : pstate} :
  small_step (SKIP;;c₂, s) (c₂, s)

| Seq2 {c₁ c₁' c₂ : com} {s s' : pstate} :
  small_step (c₁, s) (c₁', s') →
  small_step (c₁ ;; c₂, s) (c₁' ;; c₂, s')

| IfTrue {b : bexp} {s : pstate} {c₁ c₂ : com}:
  bval b s →
  small_step (IF b THEN c₁ ELSE c₂, s) (c₁, s)

| IfFalse {b : bexp} {s : pstate} {c₁ c₂ : com}:
  ¬bval b s →
  small_step (IF b THEN c₁ ELSE c₂, s) (c₂, s)

| While {b : bexp} {c : com} {s : pstate} :
  small_step (WHILE b DO c, s) (IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s)

infix `↝`:70 := small_step

open small_step

namespace small_step

inductive small_step_star : conf → conf → Prop
| refl {c : com} {s : pstate} : small_step_star (c, s) (c, s)

| step {c c₁ c₂ : com} {s s₁ s₂ : pstate}:
  small_step (c, s) (c₁, s₁) →
  small_step_star (c₁, s₁) (c₂, s₂) →
  small_step_star (c, s) (c₂, s₂)

infix `↝*`:70 := small_step_star

namespace trans

open small_step_star

@[trans] lemma small_step_star_small_step_star_trans {st st₁ st₂: conf} :
  st ↝* st₁ → st₁ ↝* st₂ → st ↝* st₂ :=
begin
  cases st with c s,
  cases st₁ with c₁ s₁,
  cases st₂ with c₂ s₂,
  intros,
  induction ‹(c, s)↝*(c₁, s₁)›,
    case refl : c s { exact ‹(c, s)↝*(c₂, s₂)› },
    case step : c c₃ c₁ s s₃ s₁  _ _ ih {
      have : (c₃, s₃)↝*(c₂, s₂) := ih ‹(c₁, s₁)↝*(c₂, s₂)›,
      exact step ‹(c, s)↝(c₃, s₃)› ‹(c₃, s₃)↝*(c₂, s₂)›
    }
end

@[trans] lemma small_step_star_small_step_trans {st st₁ st₂: conf} :
  st ↝* st₁ → st₁ ↝ st₂ → st ↝* st₂ :=
begin
  cases st with c s,
  cases st₁ with c₁ s₁,
  cases st₂ with c₂ s₂,
  intros,
  induction ‹(c, s)↝*(c₁, s₁)›,
    case refl : c s { exact step ‹(c, s)↝(c₂, s₂)› refl },
    case step : c c₃ c₁ s s₃ s₁ _ _ ih {
      have : (c₃, s₃)↝*(c₂, s₂) := ih ‹(c₁, s₁)↝(c₂, s₂)›,
      exact step ‹(c, s)↝(c₃, s₃)› ‹(c₃, s₃)↝*(c₂, s₂)›
    }
end 

@[trans] lemma small_step_small_step_star_trans {st st₁ st₂: conf} :
  st ↝ st₁ → st₁ ↝* st₂ → st ↝* st₂ :=
begin
  cases st with c s,
  cases st₁ with c₁ s₁,
  cases st₂ with c₂ s₂,
  intros,
  exact step ‹(c, s)↝(c₁, s₁)› ‹(c₁, s₁)↝*(c₂, s₂)›
end

@[trans] lemma small_step_small_step_trans {st st₁ st₂: conf} :
  st ↝ st₁ → st₁ ↝ st₂ → st ↝* st₂ :=
begin
  cases st with c s, 
  cases st₁ with c₁ s₁,
  cases st₂ with c₂ s₂,
  intros,
  have : (c₁, s₁)↝*(c₁, s₁) := refl,
  have : (c, s)↝*(c₁, s₁) := step ‹(c, s)↝(c₁, s₁)› ‹(c₁, s₁)↝*(c₁, s₁)›,
  exact small_step_star_small_step_trans ‹(c, s)↝*(c₁, s₁)› ‹(c₁, s₁)↝(c₂, s₂)›
end

section small_step_calc_ex

open bexp

variable s : pstate
variable p : ↥(bval (Bc tt) s) 

example : (IF (Bc tt) THEN SKIP ;; SKIP ELSE SKIP, s)↝*(SKIP, s) :=
  calc
    (IF (Bc tt) THEN SKIP ;; SKIP ELSE SKIP, s)↝ (SKIP ;; SKIP, s) : small_step.IfTrue p
    ...                                        ↝ (SKIP, s)         : small_step.Seq1
    ...                                        ↝*(SKIP, s)         : small_step_star.refl 

end small_step_calc_ex

end trans

theorem deterministic {c : com} {s : pstate} {cs₁ cs₂ : conf}: 
  (c, s)↝cs₁ ∧ (c, s)↝cs₂ → cs₁ = cs₂ :=
begin
  intros,
  cases ‹(c, s)↝cs₁ ∧ (c, s)↝cs₂›,
  induction' ‹(c, s)↝cs₁›,
    case Assign : s x a {
      cases ‹(x ::= a, s)↝cs₂›,
      trivial
    },
    case Seq1 : c₂ s {
      cases ‹(SKIP ;; c₂, s)↝cs₂›,
        case Seq1 : { trivial },
        case Seq2 : c₁' _ _ s' { cases ‹(SKIP, s)↝(c₁', s')› }
    },
    case Seq2 : c₁ c₁' c₂ s s' _ ih {
      cases ‹(c₁ ;; c₂, s)↝cs₂›,
        case Seq1 : { cases ‹(SKIP, s)↝(c₁', s')› },
        case Seq2 : _ c₁'' _ _ s'' _ {
          have : (c₁', s') = (c₁'', s'') := ih ‹(c₁, s)↝(c₁'', s'')›,
          have : c₁' = c₁'' := by injection ‹(c₁', s') = (c₁'', s'')›,
          have : s' = s'' := by injection ‹(c₁', s') = (c₁'', s'')›,
          rw[‹c₁' = c₁''›, ‹s' = s''›]
        }
    },
    case IfTrue : b s c' c'' {
      cases ‹(IF b THEN c' ELSE c'', s)↝cs₂›,
        case IfTrue : { trivial },
        case IfFalse : { trivial }
    },
    case IfFalse : b s c' c'' {
      cases ‹(IF b THEN c' ELSE c'', s)↝cs₂›,
        case IfTrue : { trivial },
        case IfFalse : { trivial }
    },
    case While : b c s {
      cases ‹(WHILE b DO c, s)↝cs₂›,
      trivial
    }                                           
end

end small_step

namespace equivalence

open small_step.small_step_star
open small_step

lemma seq_star {c c₁ c₂ : com} {s₁ s₂ : pstate} :
  (c₁, s₁)↝*(c, s₂) → (c₁ ;; c₂, s₁)↝*(c ;; c₂, s₂) :=
begin
  intro,
  induction' ‹(c₁, s₁)↝*(c, s₂)›,
    case refl : { exact refl },
    case step : c₁ c₃ c s₁ s₃ s₂ {
      have : (c₁ ;; c₂, s₁)↝(c₃ ;; c₂, s₃) := Seq2 ‹(c₁, s₁)↝(c₃, s₃)›,
      have : (c₃ ;; c₂, s₃)↝*(c ;; c₂, s₂) := ih,
      exact step ‹(c₁ ;; c₂, s₁)↝(c₃ ;; c₂, s₃)› ‹(c₃ ;; c₂, s₃)↝*(c ;; c₂, s₂)›
    }
end

lemma big_step_imp_small_step {c : com} {s t : pstate} : 
  (c, s) ⟹ t → (c, s)↝*(SKIP, t) :=
begin
  intro,
  induction' ‹(c, s) ⟹ t›,
    case Skip : {
      calc
        (SKIP, t)↝*(SKIP, t) : refl
    },
    case Assign : {
      calc
        (x ::= a, t)↝ (SKIP, t[x ↦ aval a t]) : Assign
        ...         ↝*(SKIP, t[x ↦ aval a t]) : refl

    },
    case Seq : _ _ _ _ _ _ _ ih₁ ih₂ {
      calc
        (c₁ ;; c₂, s₁)↝*(SKIP ;; c₂, s₂) : seq_star ‹(c₁, s₁)↝*(SKIP, s₂)›
        ...           ↝ (c₂, s₂)         : Seq1
        ...           ↝*(SKIP, t)        : ih₂
      
    },
    case IfTrue : {
      calc
        (IF b THEN c₁ ELSE c₂, s)↝(c₁, s)    : IfTrue ‹↥(bval b s)›
        ...                      ↝*(SKIP, t) : ih
    },
    case IfFalse : {
      calc
        (IF b THEN c₁ ELSE c₂, s)↝(c₂, s)    : IfFalse ‹¬↥(bval b s)›
        ...                      ↝*(SKIP, t) : ih
    },
    case WhileTrue : _ _ _ _ _ _ _ _ ih₁ ih₂ {
      calc
        (WHILE b DO c, s₁)↝ (IF b THEN c ;; WHILE b DO c ELSE SKIP, s₁) : While
        ...               ↝ (c ;; WHILE b DO c, s₁)                     : IfTrue ‹↥(bval b s₁)›
        ...               ↝*(SKIP ;; WHILE b DO c, s₂)                  : seq_star ‹(c, s₁)↝*(SKIP, s₂)›
        ...               ↝ (WHILE b DO c, s₂)                          : Seq1
        ...               ↝*(SKIP, t)                                   : ih₂
    },
    case WhileFalse : {
      calc
        (WHILE b DO c, t)↝(IF b THEN c ;; WHILE b DO c ELSE SKIP, t) : While
        ...              ↝(SKIP, t)                                  : IfFalse ‹¬↥(bval b t)›
    }
end

end equivalence
