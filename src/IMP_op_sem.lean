/-
Authore: Andrea Delmastro
-/
import tactic.induction

/-!
# Semantica per IMP

Questo file definisce le semantiche big-step e small-step per il linguaggio di programmazione IMP e 
ne dimostra l'equivalenza.

La semantica di un linguaggio di programmazione fornisce una descrizione computazionale delle 
strutture sintattiche del linguaggio.

## Note di implementazione

Questo file utilizza i tattici `cases'` e `induction'` definiti in `tactic.induction`. 
Nonostante le medesime dimostrazioni siano ottenibili tramite i tattici `cases` e `induction` 
classici, le due versioni qui utilizzate meglio si prestano all'utilizzo con predicati induttivi e 
sono più 'naturali' rispetto alla medesima dimostrazione svolta su carta.

## Notazione

* `vname` : nome di variabile, `string`
* `val` : valore di un'espressione, `ℕ`
* `pstate` : stato di programma, funzione da `vname` a `val`
* `s [ x  ↦  v ]` : aggiornamento dello stato `s`, con assegnazione di `v` a `x`
* `::=` : comando di assegnamento
* `;;` : concatenazione sequenziale di comandi
* `conf` : configurazione, coppia `com × pstate`
* `⟹` : relazione big-step
* `∼` : equivalenza di comandi
* `↝` : riduzione small-step
* `↝*` : chiusura riflessiva e transitiva di `↝`

## Teoremi principali

* `big_step.deterministic : ∀ {c : com} {s t r : pstate}, (c, s) ⟹ t → (c, s) ⟹ r → t = r`
* `small_step.deterministic : ∀ {c : com} {s : pstate} {cs₁ cs₂ : conf}, (c, s)↝cs₁ → (c, s)↝cs₂ → cs₁ = cs₂`
* `big_step_equiv_small_step : ∀ {c : com} {s t : pstate} (c, s) ⟹ t ↔ (c, s)↝*(SKIP, t)`

## Riferimenti

* [Nipkow, Klein, Concrete Semantics with Isabelle/HOL][Nipkow]
-/

abbreviation vname  := string
abbreviation val    := ℕ
abbreviation pstate := vname → val

/-!
### Espressioni aritmetiche

Sintassi e valutazione
-/

inductive aexp : Type
| N    : ℕ → aexp
| V    : vname → aexp
| Plus : aexp → aexp → aexp

open aexp

/--
Funzione di valutazione di un'espressione aritmetica: associa ad ogni espressione il proprio valore.
Ogni espressione ha un valore ben definito.
-/
def aval : aexp → pstate → val
| (N n)        _ := n
| (V x)        s := s x
| (Plus a₁ a₂) s := (aval a₁ s) + (aval a₂ s)

/--
Aggiornamento dello stato: associa ad una variabile entro uno stato un nuovo valore.
-/
def state_update (s : pstate) (x : vname) (v : val) : pstate :=
  λ (y : vname), if (y = x) then v else s y

/--
Stato vuoto, associa ad ogni variabile il valore 0.
-/
def emp : pstate := (λ _, 0)

notation s `[` x ` ↦ ` v `]`:100 := state_update s x v
notation   `[` x ` ↦ ` v `]`     := emp [x ↦ v]

/-!
### Espressioni booleane
Sintassi e valutazione
-/

inductive bexp : Type
| Bc   : bool → bexp
| Not  : bexp → bexp
| And  : bexp → bexp → bexp
| Less : aexp → aexp → bexp

open bexp

/--
Funzione di valutazione di un'espressione booleana: associa ad ogni espressione il proprio valore.
Ogni espressione ha un valore ben definito.
-/
def bval : bexp → pstate → bool
| (Bc v)       _ := v
| (Not b)      s := ¬(bval b s)
| (And b₁ b₂)  s := (bval b₁ s) ∧ (bval b₂ s)
| (Less a₁ a₂) s := (aval a₁ s) < (aval a₂ s)

/-!
### Sintassi per il linguaggio di programmazione IMP
-/

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

/-!
### Semantica operazionale big-step di IMP

La semantica big-step ([Nipkow] Fig. 7.1) è una relazione a tre posti il cui significato è 
`(c, s)⇒ t` se l'esecuzione del comando c nello stato iniziale s termina con lo stato  t. Gli stati 
intermedi nell'esecuzione del programma non sono visibili nella relazione: la relazione in sé 
considera il programma come se venisse eseguito in un unico grande step.
-/

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

/-!
### Inversione delle regole

Le regole di inversione per la semantica big-step permettono di inferire informazioni a partire
da termini di tipo `(c, s)⇒ t`. Dipendono dal fatto che un predicato induttivo è vero solo se le
regole di inferenza lo permettono, ovvero esiste una derivazione per il predicato. 
-/

/--
Regola di inversione per `Skip`: da `(SKIP, s) ⟹ t` è possibile inferire `s = t`.
-/
lemma skip {s t : pstate} (h : (SKIP, s) ⟹ t) : 
  s = t :=
begin cases' ‹(SKIP, s) ⟹ t›, reflexivity end

/--
Regola di inversione per `Assign`: da `(x ::= a, s) ⟹ t` è possibile inferire 
`s[x ↦ aval a s] = t`.
-/
lemma assign {x : vname} {a : aexp} {s t : pstate} (h : (x ::= a, s) ⟹ t) : 
  s[x ↦ aval a s] = t :=
begin cases' ‹(x ::= a, s) ⟹ t›, reflexivity end 

/--
Regola di inversione per `Seq`: da `(c₁ ;; c₂, s₁) ⟹ s₃` è possibile inferire l'esistenza di uno
stato intermedio `s₂` tale che `(c₁, s₁) ⟹ s₂` e `(c₂, s₂) ⟹ s₃`.
-/
lemma seq {c₁ c₂ : com} {s₁ s₃ : pstate} (h : (c₁ ;; c₂, s₁) ⟹ s₃) : 
  ∃ (s₂ : pstate), (c₁, s₁) ⟹ s₂ ∧ (c₂, s₂) ⟹ s₃ :=
begin
  cases' ‹(c₁ ;; c₂, s₁) ⟹ s₃› with _ _ _ _ _ _ _ s₂,
  apply exists.intro,
  split,
    exact ‹(c₁, s₁) ⟹ s₂›,
    exact ‹(c₂, s₂) ⟹ s₃›
end

/--
Regola di inversione per `IfTrue` e `IfFalse`: da `(IF b THEN c₁ ELSE c₂, s) ⟹ t` è possibile
inferire `(bval b s ∧ (c₁, s) ⟹ t)`, corrispondente a una derivazione che termina in `IfTrue` 
oppure `(¬bval b s ∧ (c₂, s) ⟹ t)`, corrispondente a una derivazione che termina in `IfFalse`
-/
lemma ifte {b : bexp} {c₁ c₂ : com} {s t : pstate} (h : (IF b THEN c₁ ELSE c₂, s) ⟹ t) :
  (bval b s ∧ (c₁, s) ⟹ t) ∨ (¬bval b s ∧ (c₂, s) ⟹ t) :=
begin
  cases ‹(IF b THEN c₁ ELSE c₂, s) ⟹ t›,
    case IfTrue : { exact or.inl ⟨‹↥(bval b s)›, ‹(c₁, s) ⟹ t›⟩ },
    case IfFalse : { exact or.inr ⟨‹¬↥(bval b s)›, ‹(c₂, s) ⟹ t›⟩ }
end

/--
Regola di inversione per `WhileTrue` e `WhileFalse`: da `(WHILE b DO c, s) ⟹ t` è possibile inferire 
`(¬bval b s ∧ t = s)`, corrispondente a una derivazione che termina in `WhileFalse` oppure 
`(bval b s ∧ ∃ (s₁ : pstate), (c, s) ⟹ s₁ ∧ (WHILE b DO c, s₁) ⟹ t)`, corrispondente a una
derivazione che termina in `WhileTrue`.
-/
lemma while {b : bexp} {c : com} {s t : pstate} (h : (WHILE b DO c, s) ⟹ t) :
  (¬bval b s ∧ t = s) ∨ (bval b s ∧ ∃ (s₁ : pstate), (c, s) ⟹ s₁ ∧ (WHILE b DO c, s₁) ⟹ t) :=
begin
  cases ‹(WHILE b DO c, s) ⟹ t›,
    case WhileTrue : _ _ _ s₂ _ _ _ _ { 
      have : ∃ (s₁ : pstate), (c, s) ⟹ s₁ ∧ (WHILE b DO c, s₁) ⟹ t := 
        ⟨s₂, ⟨‹(c, s) ⟹ s₂›, ‹(WHILE b DO c, s₂) ⟹ t›⟩⟩,
      exact or.inr ⟨‹↥(bval b s)›, ‹∃ (s₁ : pstate), (c, s) ⟹ s₁ ∧ (WHILE b DO c, s₁) ⟹ t›⟩ 
    },
    case WhileFalse : { exact or.inl ⟨‹¬↥(bval b s)›, rfl⟩ }
end

end rule_inversion

/--
Associatività della composizione sequenziale.
-/
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

namespace com_equivalence

/-!
### Equivalenza di comandi

Due comandi `c₁` e `c₂` sono definiti equivalenti se a partire dallo stesso s stato terminano nel 
medesimo stato `t`. 
-/

notation c₁ `∼` c₂ := ∀ {s t : pstate}, (c₁, s) ⟹ t = (c₂, s) ⟹ t

/--
Il comando `WHILE d DO c` è equivalente al suo unfolding in 
`IF b THEN (c ;; WHILE b DO c) ELSE SKIP`.
-/
lemma eq_while_ifwhile {b : bexp} {c : com} : 
  WHILE b DO c ∼ IF b THEN (c ;; WHILE b DO c) ELSE SKIP :=
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
        case WhileTrue : _ _ _ s₁ _ _ _ _ {
          show (IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s) ⟹ t, from
            IfTrue ‹↥(bval b s)› (Seq ‹(c, s) ⟹ s₁› ‹(WHILE b DO c, s₁) ⟹ t›)
        }
    },
    {
      intros,
      cases ‹(IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s) ⟹ t›,
        case IfTrue : {
          cases ‹(c ;; WHILE b DO c, s) ⟹ t› with _ _ _ _ _ _ _ s₁,
          show (WHILE b DO c, s) ⟹ t, from
            WhileTrue ‹↥(bval b s)› ‹(c, s) ⟹ s₁› ‹(WHILE b DO c, s₁) ⟹ t›
        },
        case IfFalse : {
          cases ‹(SKIP, s) ⟹ t›,
          show (WHILE b DO c, s) ⟹ s, from
            WhileFalse ‹¬↥(bval b s)›
        }
    }
end

end com_equivalence

/--
Determinismo della semantica big-step. 
Se l'esecuzione di `c` in `s` termina, allora esiste un unico `t` tale che `(c, s) ⟹ t`.
-/
theorem deterministic {c : com} {s t r : pstate} :
  (c, s) ⟹ t → (c, s) ⟹ r → (t = r) :=
begin
  intros,
  induction' ‹(c, s) ⟹ t›,
    case Skip : s { 
      cases' ‹(SKIP, s) ⟹ r›, 
      trivial 
    },
    case Assign : s x a {
      cases' ‹(x ::= a, s) ⟹ r›, 
      trivial 
    },
    case Seq : _ _ s s₁ _ _ _ ih₁ ih₂ {
      cases' ‹(c₁ ;; c₂, s) ⟹ r› with _ _ _ _ _ _ s _ _,
      have : (s₁ = s₂) := ih₁ ‹(c₁, s) ⟹ s₂›,
      rw ‹s₁ = s₂› at *,
      show t = r, from  ih₂ ‹(c₂, s₂) ⟹ r›
    },
    case IfTrue : {
      cases' ‹(IF b THEN c₁ ELSE c₂, s) ⟹ r›,
        case IfTrue : { show t = r, from ih ‹(c₁, s) ⟹ r› },
        case IfFalse : { trivial }
    },
    case IfFalse : {
      cases' ‹(IF b THEN c₁ ELSE c₂, s) ⟹ r›,
        case IfTrue : { trivial },
        case IfFalse : { show t = r, from ih ‹(c₂, s) ⟹ r› }
    },
    case WhileTrue : _ _ s s₁ _ _ _ _ ih₁ ih₂ {
      cases' ‹(WHILE b DO c, s) ⟹ r›,
        case WhileTrue : _ _ s _ _ _ _ _ { 
          have : (s₁ = s₂) := ih₁ ‹(c, s) ⟹ s₂›,
          rw ←‹s₁ = s₂› at *,
          show t = r, from ih₂ ‹(WHILE b DO c, s₁) ⟹ r›
        },
        case WhileFalse : { trivial }
    },
    case WhileFalse : _ _ s _ { 
      cases' ‹(WHILE b DO c, s) ⟹ r›, 
        case WhileTrue : { trivial },
        case WhileFalse : { trivial }
    }
end

end big_step

/-!
### Semantica operazionale small-step di IMP

La riduzione small-step ([Nipkow] Fig. 7.5)  `(c₁ , s₁)→(c₂ , s₂)` è una relazione tra due coppie 
comando/stato che rappresenta l'esecuzione di un singolo passo di calcolo di `c₁` nello stato `s₁` 
che produce lo stato `s₂`, mentre `c₂` é la continuazione (ciò che resta da eseguire) di `c₁`. 
-/

inductive small_step : conf → conf → Prop
| Assign  {s : pstate} {x : vname} {a : aexp} :
  small_step (x ::= a, s) (SKIP, s[x ↦ aval a s])

| Seq1 {c₂ : com} {s : pstate} :
  small_step (SKIP ;; c₂, s) (c₂, s)

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

/-!
### Lemmi di transitività per ↝ e ↝*

I seguenti lemmi sono puramente tecnici e utili alla configurazione dell'ambiente `calc`.
-/

open small_step_star

@[trans] lemma small_step_star_small_step_star_trans {cf cf₁ cf₂: conf} :
  cf ↝* cf₁ → cf₁ ↝* cf₂ → cf ↝* cf₂ :=
begin
  cases cf with c s,
  cases cf₁ with c₁ s₁,
  cases cf₂ with c₂ s₂,
  intros,
  induction ‹(c, s)↝*(c₁, s₁)›,
    case refl : c s { exact ‹(c, s)↝*(c₂, s₂)› },
    case step : c c₃ c₁ s s₃ s₁  _ _ ih {
      have : (c₃, s₃)↝*(c₂, s₂) := ih ‹(c₁, s₁)↝*(c₂, s₂)›,
      show (c, s)↝*(c₂, s₂), from step ‹(c, s)↝(c₃, s₃)› ‹(c₃, s₃)↝*(c₂, s₂)›
    }
end

@[trans] lemma small_step_star_small_step_trans {cf cf₁ cf₂: conf} :
  cf ↝* cf₁ → cf₁ ↝ cf₂ → cf ↝* cf₂ :=
begin
  cases cf with c s,
  cases cf₁ with c₁ s₁,
  cases cf₂ with c₂ s₂,
  intros,
  induction ‹(c, s)↝*(c₁, s₁)›,
    case refl : c s { exact step ‹(c, s)↝(c₂, s₂)› refl },
    case step : c c₃ c₁ s s₃ s₁ _ _ ih {
      have : (c₃, s₃)↝*(c₂, s₂) := ih ‹(c₁, s₁)↝(c₂, s₂)›,
      show (c, s)↝*(c₂, s₂), from step ‹(c, s)↝(c₃, s₃)› ‹(c₃, s₃)↝*(c₂, s₂)›
    }
end 

@[trans] lemma small_step_small_step_star_trans {cf cf₁ cf₂: conf} :
  cf ↝ cf₁ → cf₁ ↝* cf₂ → cf ↝* cf₂ :=
begin
  cases cf with c s,
  cases cf₁ with c₁ s₁,
  cases cf₂ with c₂ s₂,
  intros,
  show (c, s)↝*(c₂, s₂), from step ‹(c, s)↝(c₁, s₁)› ‹(c₁, s₁)↝*(c₂, s₂)›
end

@[trans] lemma small_step_small_step_trans {cf cf₁ cf₂: conf} :
  cf ↝ cf₁ → cf₁ ↝ cf₂ → cf ↝* cf₂ :=
begin
  cases cf with c s, 
  cases cf₁ with c₁ s₁,
  cases cf₂ with c₂ s₂,
  intros,
  have : (c₁, s₁)↝*(c₁, s₁) := refl,
  have : (c, s)↝*(c₁, s₁) := step ‹(c, s)↝(c₁, s₁)› ‹(c₁, s₁)↝*(c₁, s₁)›,
  show (c, s)↝*(c₂, s₂), from
     small_step_star_small_step_trans ‹(c, s)↝*(c₁, s₁)› ‹(c₁, s₁)↝(c₂, s₂)›
end

end trans

/--
Determinismo della semantica small-step. 
Se la configurazione `(c, s)` si riduce di un passo, allora esiste un'unica configurazione `cs` tale 
che `(c, s)↝cs`.
-/
theorem deterministic {c : com} {s : pstate} {cs₁ cs₂ : conf} : 
  (c, s)↝cs₁ → (c, s)↝cs₂ → cs₁ = cs₂ :=
begin
  intros,
  induction' ‹(c, s)↝cs₁›,
    case Assign : s x a {
      cases' ‹(x ::= a, s)↝cs₂›,
      trivial
    },
    case Seq1 : c₂ s {
      cases' ‹(SKIP ;; c₂, s)↝cs₂›,
        case Seq1 : { trivial },
        case Seq2 : c₁' _ _ s' { cases' ‹(SKIP, s)↝(c₁', s')› }
    },
    case Seq2 : c₁ c₁' c₂ s s' _ ih {
      cases' ‹(c₁ ;; c₂, s)↝cs₂›,
        case Seq1 : { cases ‹(SKIP, s)↝(c₁', s')› },
        case Seq2 : _ c₁'' _ _ s'' _ {
          have : (c₁', s') = (c₁'', s'') := ih ‹(c₁, s)↝(c₁'', s'')›,
          have : c₁' = c₁'' := by injection ‹(c₁', s') = (c₁'', s'')›,
          have : s' = s'' := by injection ‹(c₁', s') = (c₁'', s'')›,
          rw[‹c₁' = c₁''›, ‹s' = s''›]
        }
    },
    case IfTrue : b s c' c'' {
      cases' ‹(IF b THEN c' ELSE c'', s)↝cs₂›,
        case IfTrue : { trivial },
        case IfFalse : { trivial }
    },
    case IfFalse : b s c' c'' {
      cases' ‹(IF b THEN c' ELSE c'', s)↝cs₂›,
        case IfTrue : { trivial },
        case IfFalse : { trivial }
    },
    case While : b c s {
      cases' ‹(WHILE b DO c, s)↝cs₂›,
      trivial
    }                                           
end

end small_step

namespace equivalence

open small_step.small_step_star

lemma seq_star {c c₁ c₂ : com} {s₁ s₂ : pstate} :
  (c₁, s₁)↝*(c, s₂) → (c₁ ;; c₂, s₁)↝*(c ;; c₂, s₂) :=
begin
  intro,
  induction' ‹(c₁, s₁)↝*(c, s₂)›,
    case refl : { exact refl },
    case step : c₁ c₃ c s₁ s₃ s₂ { 
      show (c₁ ;; c₂, s₁)↝*(c ;; c₂, s₂), from
        calc
          (c₁ ;; c₂, s₁)↝ (c₃ ;; c₂, s₃) : Seq2 ‹(c₁, s₁)↝(c₃, s₃)›
          ...           ↝*(c ;; c₂, s₂)  : ih
    }
end

/--
La semantica big-step implica la semantica small-step.
Se l'esecuzione di `c` in `s` termina in uno stato `t`, allora `(c, s)` si riduce in zero o più 
passi a `(SKIP, t)`.
-/
lemma big_step_imp_small_step {c : com} {s t : pstate} : 
  (c, s) ⟹ t → (c, s)↝*(SKIP, t) :=
begin
  intro,
  induction' ‹(c, s) ⟹ t›,
    case Skip : { exact refl },
    case Assign : {
      calc
        (x ::= a, t)↝ (SKIP, t[x ↦ aval a t]) : Assign
        ...         ↝*(SKIP, t[x ↦ aval a t]) : refl

    },
    case Seq : _ _ s s₁ _ _ _ ih₁ ih₂ {
      calc
        (c₁ ;; c₂, s)↝*(SKIP ;; c₂, s₁) : seq_star ‹(c₁, s)↝*(SKIP, s₁)›
        ...          ↝ (c₂, s₁)         : Seq1
        ...          ↝*(SKIP, t)        : ih₂
      
    },
    case IfTrue : {
      calc
        (IF b THEN c₁ ELSE c₂, s)↝ (c₁, s)   : IfTrue ‹↥(bval b s)›
        ...                      ↝*(SKIP, t) : ih
    },
    case IfFalse : {
      calc
        (IF b THEN c₁ ELSE c₂, s)↝ (c₂, s)   : IfFalse ‹¬↥(bval b s)›
        ...                      ↝*(SKIP, t) : ih
    },
    case WhileTrue : _ _ s s₁ _ _ _ _ ih₁ ih₂ {
      calc
        (WHILE b DO c, s)↝ (IF b THEN c ;; WHILE b DO c ELSE SKIP, s) : While
        ...              ↝ (c ;; WHILE b DO c, s)                     : IfTrue ‹↥(bval b s)›
        ...              ↝*(SKIP ;; WHILE b DO c, s₁)                 : seq_star ih₁
        ...              ↝ (WHILE b DO c, s₁)                         : Seq1
        ...              ↝*(SKIP, t)                                  : ih₂
    },
    case WhileFalse : {
      calc
        (WHILE b DO c, t)↝(IF b THEN c ;; WHILE b DO c ELSE SKIP, t) : While
        ...              ↝(SKIP, t)                                  : IfFalse ‹¬↥(bval b t)›
    }
end

/--
Se la configurazione `(c, s)` si riduce in un passo a `(c₁, s₁)` e l'esecuzione di `c₁` in `s₁` 
termina in `t`, allora l'esecuzione di `c` in `s` termina in `t`.
-/
lemma step_case {c c₁ : com} {s s₁ t : pstate} : 
  (c, s)↝(c₁, s₁) → (c₁, s₁) ⟹ t → (c, s) ⟹ t :=
begin
  intros,
  induction' ‹(c, s)↝(c₁, s₁)›,
    case Assign : {
      cases' ‹(SKIP, s[x ↦ aval a s]) ⟹ t›,
      show (x ::= a, s) ⟹ s[x ↦ aval a s], from Assign
    },
    case Seq1 : {
      have : (SKIP, s) ⟹ s, from Skip,
      show (SKIP ;; c₂, s) ⟹ t, from Seq ‹(SKIP, s) ⟹ s› ‹(c₂, s) ⟹ t›
    },
    case Seq2 : {
      cases' ‹(c₁' ;; c₂, s') ⟹ t› with _ _ _ _ c₃ _ _ _ _,
      have : (c₁, s) ⟹ s₂, from ih ‹(c₃, s₁) ⟹ s₂›,
      show (c₁ ;; c₂, s) ⟹ t, from Seq ‹(c₁, s) ⟹ s₂› ‹(c₂, s₂) ⟹ t›
    },
    case IfTrue : {
      show (IF b THEN c₁ ELSE c₂, s) ⟹ t, from 
        IfTrue ‹↥(bval b s)› ‹(c₁, s) ⟹ t›
    },
    case IfFalse : {
      show (IF b THEN c₁ ELSE c₂, s) ⟹ t, from 
        IfFalse ‹¬↥(bval b s)› ‹(c₂, s) ⟹ t›
    },
    case While : {
      cases' ‹(IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s) ⟹ t›,
        case IfTrue : {
          cases' ‹(c ;; WHILE b DO c, s) ⟹ t› with _ _ _ _ _ _ s s₁ _,
          show (WHILE b DO c₁, s) ⟹ t, from
            WhileTrue ‹↥(bval b s)› ‹(c₁, s) ⟹ s₁› ‹(WHILE b DO c₁, s₁) ⟹ t›
        },
        case IfFalse : {
          cases' ‹(SKIP, s) ⟹ t›,
          show (WHILE b DO c, t) ⟹ t, from  WhileFalse ‹¬↥(bval b t)› 
        }
    }
end

/--
La semantica small-step implica la semantica big-step.
Se la configurazione `(c, s)` si riduce in zero o più passi a `(SKIP, t)`, allora l'esecuzione di 
`c` in `s` termina nello stato `t`.
La dimostrazione per il caso `refl` é banale, mentre nel caso `step` segue immediatamente dal lemma 
`step_case`.
-/
lemma small_step_imp_big_step {c : com} {s t : pstate} :
  (c, s)↝*(SKIP, t) → (c, s) ⟹ t :=
begin
  intros,
  induction' ‹(c, s)↝*(SKIP, t)›,
    case refl : t {
      show (SKIP, t) ⟹ t, from Skip
    },
    case step : _ _ _ _ t _ _ _ {
      show (c, s) ⟹ t, from step_case ‹(c, s)↝(c₁, s₁)› ‹(c₁, s₁) ⟹ t›
    }
end

/--
Equivalenza tra le due semantiche big-step e small-step.
Il teorema segue immediatamente dai lemmi `big_step_imp_small_step` e `small_step_imp_big_step`.
-/
theorem big_step_equiv_small_step {c : com} {s t : pstate} :
  (c, s) ⟹ t ↔ (c, s)↝*(SKIP, t) :=
begin
  intros,
  apply iff.intro,
    exact big_step_imp_small_step,
    exact small_step_imp_big_step
end

end equivalence
