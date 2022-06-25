/-
Authore: Andrea Delmastro
-/
import tactic.induction
import order.min_max
import data.nat.basic

import IMP_op_sem
open aexp
open bexp
open com
open big_step

/-!
# Tipi per la sicurezza per IMP

Questo file definisce un sistema di tipi per IMP per garantire una semplice proprietà di sicurezza: 
l’assenza di flussi di dati privati verso osservatori pubblici, e ne prova la correttezza.

## Note di implementazione

Questo file utilizza i tattici `cases'` e `induction'` definiti in `tactic.induction`. 
Nonostante le medesime dimostrazioni siano ottenibili tramite i tattici `cases` e `induction` 
classici, le due versioni qui utilizzate meglio si prestano all'utilizzo con predicati induttivi e 
sono più 'naturali' rispetto alla medesima dimostrazione svolta su carta.

## Notazione

* `vname` : nome di variabile, `string`
* `val` : valore di un'espressione, `ℕ`
* `pstate` : stato di programma, funzione da `vname` a `val`
* `emp` : stato vuoto, assegna ad ogni variabile il valore 0
* `lv` : livello di sicurezza, `ℕ`
* `s [ x  ↦  v ]` : aggiornamento dello stato `s`, con assegnazione di `v` a `x`
* `::=` : comando di assegnamento
* `;;` : concatenazione sequenziale di comandi
* `IF THEN ELSE` : comando ramificazione condizionale
* `WHILE DO` : comando di ciclo
* `conf` : configurazione, coppia `com × pstate`
* `⟹` : relazione big-step

## Risultati principali

* `noninterference : ∀ {c : com} {s s' t t' : pstate} {l : lv}, (c, s) ⟹ s' → (c, t) ⟹ t' → (0 ⊢. c) → s = t [<= l] → s' = t' [<= l]`

## Riferimenti

* [Nipkow, Klein, Concrete Semantics with Isabelle/HOL][Nipkow]
-/


abbreviation lv := ℕ

/--
Funzione che associa ad ogni variabile un livello di sicurezza determinato dalla lunghezza del
suo nome.
-/
def sec : vname → lv :=
  λ (x : vname), x.length

/--
Funzione che associa ad ogni espressione aritmetica un livello di sicurezza calcolato come il
massimo tra i livelli di sicurezza delle variabili che vi compaiono.
-/
def secₐ : aexp → lv
| (N n)        := 0
| (V x)        := sec x
| (Plus a₁ a₂) := max (secₐ a₁) (secₐ a₂)

/--
Funzione che associa ad ogni espressione booleana un livello di sicurezza calcolato come il
massimo tra i livelli di sicurezza delle variabili che vi compaiono.
-/
def sec₆ : bexp → lv
| (Bc v)       := 0
| (Not b)      := sec₆ b
| (And b₁ b₂)  := max (sec₆ b₁) (sec₆ b₂)
| (Less a₁ a₂) := max (secₐ a₁) (secₐ a₂)

notation s ` = ` t ` [<= ` l `]` := ∀ (z : vname), (sec z <= l) → s z = t z
notation s ` = ` t ` [< ` l `]` := ∀ (z : vname), (sec z < l) → s z = t z

namespace state_eq_below_lv

/-!
### Equivalenza tra stati al di sotto di una soglia di sicurezza (<)

Vengono dimostrate alcune semplici proprietà relativamente alle definizioni di equivalenza tra stati 
al di sotto di una soglia di sicurezza.
-/

lemma refl {s : pstate} {l : lv} : s = s [< l] :=
begin
  intros,
  reflexivity
end

lemma trans {s₁ s₂ s₃ : pstate} {l : lv} : 
  s₁ = s₂ [< l] → s₂ = s₃ [< l] → s₁ = s₃ [< l] :=
begin
  intros _ _ x _,
  have : s₁ x = s₂ x, from ‹s₁ = s₂ [< l]› x ‹sec x < l›,
  have : s₂ x = s₃ x, from ‹s₂ = s₃ [< l]› x ‹sec x < l›,
  show s₁ x = s₃ x, from trans ‹s₁ x = s₂ x› ‹s₂ x = s₃ x›
end

lemma symm {s t : pstate} {l : lv} :
  s = t [< l] → t = s [< l] :=
begin
  intros _ x _, 
  show t x = s x, from symm (‹s = t [< l]› x ‹sec x < l›)
end

lemma restrict {s t : pstate} {l₁ l₂ : lv} :
  s = t [< l₁] → (l₂ < l₁) → s = t [<= l₂] :=
begin
  intros _ _ x _,
  have : sec x < l₁, from gt_of_gt_of_ge ‹l₂ < l₁› ‹sec x <= l₂›,
  show s x = t x, from ‹s = t [< l₁]› x ‹sec x < l₁› 
end

end state_eq_below_lv

open state_eq_below_lv

namespace state_eq_beloweq_lv

/-!
### Equivalenza tra stati al di sotto di una soglia di sicurezza (<=)

Vengono dimostrate alcune semplici proprietà relativamente alle definizioni di equivalenza tra stati 
al di sotto di una soglia di sicurezza.
-/

lemma refl {s : pstate} {l : lv} : s = s [<= l] :=
begin
  intros,
  reflexivity
end

lemma trans {s₁ s₂ s₃ : pstate} {l : lv} : 
  s₁ = s₂ [<= l] → s₂ = s₃ [<= l] → s₁ = s₃ [<= l] :=
begin
  intros _ _ x _,
  have : s₁ x = s₂ x, from ‹s₁ = s₂ [<= l]› x ‹sec x <= l›,
  have : s₂ x = s₃ x, from ‹s₂ = s₃ [<= l]› x ‹sec x <= l›,
  show s₁ x = s₃ x, from trans ‹s₁ x = s₂ x› ‹s₂ x = s₃ x›
end

lemma symm {s t : pstate} {l : lv} :
  s = t [<= l] → t = s [<= l] :=
begin
  intros _ x _, 
  show t x = s x, from symm (‹s = t [<= l]› x ‹sec x <= l›)
end

lemma restrict {s t : pstate} {l₁ l₂ : lv} :
  s = t [<= l₁] → (l₂ < l₁) → s = t [<= l₂] :=
begin
  intros _ _ x _,
  have : sec x <= l₁, from le_of_lt (gt_of_gt_of_ge ‹l₂ < l₁› ‹sec x <= l₂›),
  show s x = t x, from ‹s = t [<= l₁]› x ‹sec x <= l₁› 
end

end state_eq_beloweq_lv

open state_eq_beloweq_lv

/--
Lemma di noninterferenza per espressioni aritmetiche: la valutazione di un'espressione aritmetica
in due stati uguali al di sotto di una soglia di sicurezza produce il medesimo valore se il livello 
di sicurezza associato all'espressione è al di sotto della soglia.
-/
lemma noninterference_aexp {s t : pstate} {l : lv} {a : aexp} :
  s = t [<= l] → (secₐ a <= l) → (aval a s = aval a t) :=
begin
  intros,
  induction' a,
    case N : {
      trivial
    },
    case V : x {
      show aval (V x) s = aval (V x) t, by
        simp[aval, ‹s = t [<= l]› x ‹sec x ≤ l›]
    },
    case Plus : a₁ a₂ ih₁ ih₂ {
      have : (secₐ a₁ <= l) ∧ (secₐ a₂ <= l), from
         max_le_iff.elim_left ‹max (secₐ a₁) (secₐ a₂) ≤ l›,
      cases' ‹(secₐ a₁ <= l) ∧ (secₐ a₂ <= l)›,

      have : aval a₁ s = aval a₁ t, from ih₁ ‹s = t [<= l]› ‹(secₐ a₁ <= l)›,
      have : aval a₂ s = aval a₂ t, from ih₂ ‹s = t [<= l]› ‹(secₐ a₂ <= l)›,

      show aval (Plus a₁ a₂) s = aval (Plus a₁ a₂) t, by
        simp[aval, ‹aval a₁ s = aval a₁ t›, ‹aval a₂ s = aval a₂ t›]
    }
end

/--
Lemma di noninterferenza per espressioni booleane: la valutazione di un'espressione booleana
in due stati uguali al di sotto di una soglia di sicurezza produce il medesimo valore se il livello 
di sicurezza associato all'espressione è al di sotto della soglia.
-/
lemma noninterference_bexp {s t : pstate} {l : lv} {b : bexp} :
  s = t [<= l] → (sec₆ b <= l) → (bval b s = bval b t) :=
begin
  intros,
  induction' b,
    case Bc : {
      trivial
    },
    case Not : {
      have : bval b s = bval b t, from 
        ih ‹s = t [<= l]› ‹sec₆ b ≤ l›,

      show bval (Not b) s = bval (Not b) t, by 
        simp[bval, ‹bval b s = bval b t›]
    },
    case And : b₁ b₂ ih₁ ih₂ {
      have : (sec₆ b₁ <= l) ∧ (sec₆ b₂ <= l), from
        max_le_iff.elim_left ‹max (sec₆ b₁) (sec₆ b₂) <= l›,
      cases' ‹(sec₆ b₁ <= l) ∧ (sec₆ b₂ <= l)›,

      have : bval b₁ s = bval b₁ t, from ih₁ ‹s = t [<= l]› ‹sec₆ b₁ ≤ l›,
      have : bval b₂ s = bval b₂ t, from ih₂ ‹s = t [<= l]› ‹sec₆ b₂ ≤ l›,

      show bval (And b₁ b₂) s = bval (And b₁ b₂) t, by
        simp[bval, ‹bval b₁ s = bval b₁ t›, ‹bval b₂ s = bval b₂ t›]
    },
    case Less : a₁ a₂ {
      have : (secₐ a₁ <= l) ∧ (secₐ a₂ <= l), from
        max_le_iff.elim_left ‹max (secₐ a₁) (secₐ a₂) ≤ l›,
      cases' ‹(secₐ a₁ <= l) ∧ (secₐ a₂ <= l)›,

      have : aval a₁ s = aval a₁ t, from 
        noninterference_aexp ‹s = t [<= l]› ‹(secₐ a₁ <= l)›,
      have : aval a₂ s = aval a₂ t, from 
        noninterference_aexp ‹s = t [<= l]› ‹(secₐ a₂ <= l)›,

      show bval (Less a₁ a₂) s = bval (Less a₁ a₂) t, by
        simp[bval, ‹aval a₁ s = aval a₁ t›, ‹aval a₂ s = aval a₂ t›]
    }
end


/-!
### Giudizi per i comandi

Il sistema permette di derivare giudizi della forma: `l ⊢. c` se ogni flusso di informazione
entro `c` è crescente rispetto al livello di sicurezza (da livello basso a livello alto) e avviene 
verso variabili di livello maggiore o uguale a `l`.
-/

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
  sec_type (max l (sec₆ b)) c₁ →
  sec_type (max l (sec₆ b)) c₂ →
  sec_type l (IF b THEN c₁ ELSE c₂)

| While {b : bexp} {l : lv} {c : com} :
  sec_type (max l (sec₆ b)) c →
  sec_type l (WHILE b DO c)

infix ` ⊢. `:50 := sec_type

open sec_type

/--
Lemma di anti monotonicità: è possibile abbassare il livello sotto il quale non sono permessi
assegnamenti, mantenendo il comando ben tipato.
-/
lemma anti_monotonicity {l l' : lv} {c : com} :
  (l ⊢. c) → (l' <= l) → (l' ⊢. c) :=
begin
  intros,
  induction' ‹l ⊢. c›,
    case Skip : {
      show l' ⊢. SKIP, from Skip
    },
    case Assign : {
      have : l' <= sec x, from le_trans ‹l' <= l› ‹l <= sec x›,

      show l' ⊢. x ::= a, from Assign ‹secₐ a ≤ sec x› ‹l' <= sec x›
    },
    case Seq : l c₁ c₂ _ _ ih₁ ih₂ {
      have : l' ⊢. c₁, from ih₁ ‹l' <= l›,
      have : l' ⊢. c₂, from ih₂ ‹l' <= l›,

      show l' ⊢. c₁ ;; c₂, from Seq ‹l' ⊢. c₁› ‹ l' ⊢. c₂›
    },
    case If : _ _ c₁ c₂ _ _ ih₁ ih₂ {
      have : max l' (sec₆ b) <= max l (sec₆ b), from max_le_max ‹l' ≤ l› (le_refl _) ,
      
      have : max l' (sec₆ b) ⊢. c₁, from ih₁ ‹max l' (sec₆ b) <= max l (sec₆ b)›,
      have : max l' (sec₆ b) ⊢. c₂, from ih₂ ‹max l' (sec₆ b) <= max l (sec₆ b)›,

      show l' ⊢. IF b THEN c₁ ELSE c₂, from 
        If ‹max l' (sec₆ b) ⊢. c₁› ‹max l' (sec₆ b) ⊢. c₂›
    },
    case While : {
      have : max l' (sec₆ b) <= max l (sec₆ b), from max_le_max ‹l' ≤ l› (le_refl _),

      have : max l' (sec₆ b) ⊢. c, from ih ‹max l' (sec₆ b) <= max l (sec₆ b)›,

      show l' ⊢. WHILE b DO c, from While ‹max l' (sec₆ b) ⊢. c›
    }
end

/--
Lemma di confinamento: un comando `c` ben tipato in un livello `l` ha effetto esclusivamente sulle
variabili di livello superiore o ugale a `l`. 
-/
lemma confinement {c : com} {s t : pstate} {l : lv} :
  (c, s) ⟹ t → (l ⊢. c) → s = t [< l] :=
begin
  intros _ _,
  induction' ‹(c, s) ⟹ t›,
    case Skip : {
      show t = t [< l], from refl
    },
    case Assign : {
      intros,

      cases' ‹l ⊢. x ::= a›,
    
      have : (z = x) ∨ (z ≠ x), from em (z = x),
      cases' ‹(z = x) ∨ (z ≠ x)›,
        case or.inl : {
          rw ‹z = x› at *,
          have : ¬(sec x < l), from not_lt_of_le ‹l ≤ sec x›,
          contradiction
        },
        case or.inr : {
          show t z = t[x ↦ aval a t] z, by simp[‹z ≠ x›]
        }
    },
    case Seq :  _ _ s s' t _ _ ih₁ ih₂{
      cases' ‹l ⊢. c₁ ;; c₂›,
      
      have : s = s' [< l], from ih₁ ‹l ⊢. c₁›,
      have : s' = t [< l], from ih₂ ‹l ⊢. c₂›,

      show s = t [< l], from trans ‹s = s' [< l]› ‹s' = t [< l]›
    },
    case IfTrue : {
      cases' ‹l ⊢. IF b THEN c₁ ELSE c₂›,

      have : l <= max l (sec₆ b), from le_max_left l (sec₆ b),
      have : l ⊢. c₁, from anti_monotonicity ‹max l (sec₆ b) ⊢. c₁› ‹l <= max  l (sec₆ b)›,

      show s = t [< l], from ih ‹l ⊢. c₁›
    },
    case IfFalse : {
      cases' ‹l ⊢. IF b THEN c₁ ELSE c₂›,

      have : l <= max l (sec₆ b), from le_max_left l (sec₆ b),
      have : l ⊢. c₂, from anti_monotonicity ‹max l (sec₆ b) ⊢. c₂› ‹l <= max l (sec₆ b)›,

      show s = t [< l], from ih ‹l ⊢. c₂›
    },
    case WhileTrue : _ _ s s' t _ _ _ ih₁ ih₂ {
      cases' ‹l ⊢. WHILE b DO c›,

      have : l <= max l (sec₆ b), from le_max_left l (sec₆ b),
      have : l ⊢. c, from anti_monotonicity ‹max l (sec₆ b) ⊢. c› ‹l <= max l (sec₆ b)›,

      have : s = s' [< l], from ih₁ ‹l ⊢. c›,
      have : s' = t [< l], from ih₂ (While ‹max l (sec₆ b) ⊢. c›),

      show s = t [< l], from trans ‹s = s' [< l]› ‹s'= t [< l]›
    },
    case WhileFalse : {
      show t = t [< l], from refl
    }
end

/--
Teorema di non interferenza: dimostra la correttezza del sistema di tipi, mostrando come la
gli output inferiori o uguali ad una data soglia di sicurezza `l` non siano influenzati dagli
input di livello superiore a `l`.
-/
theorem noninterference {c : com} {s s' t t' : pstate} {l : lv}:
  (c, s) ⟹ s' → (c, t) ⟹ t' → (0 ⊢. c) → s = t [<= l] → s' = t' [<= l] :=
begin
  intro,
  revert t t',
  induction' ‹(c, s) ⟹ s'›,
    all_goals { intros _ _ _ _ _ },
    case Skip : { 
      cases' ‹(SKIP, t) ⟹ t'›,

      show s' = t' [<= l], by assumption
    },
    case Assign : s _ _ {
      intros,
      cases' ‹(x ::= a, t) ⟹ t'› with _ t _,
      cases' ‹0 ⊢. x ::= a›,

      have : (sec x <= l) ∨ (sec x > l), from le_or_lt (sec x) l,
      have : (z = x) ∨ (z ≠ x), from em (z = x),

      cases' ‹(z = x) ∨ (z ≠ x)›,
        case inl : { 
          simp[‹z = x›] at *,
          cases' ‹(sec x <= l) ∨ (sec x > l)›,
            case inl : {
              have : secₐ a <= l, from trans ‹secₐ a ≤ sec x› ‹sec x ≤ l›,
              show aval a s = aval a t, from noninterference_aexp ‹s = t [<= l]› ‹secₐ a <= l›
            },
            case inr : {
              have : ¬(sec x <= l), from not_le_of_gt ‹sec x > l›,
              contradiction
            }
        },
        case inr : {
          simp[‹z ≠ x›],
          show s z = t z, from ‹s = t [<= l]› z ‹sec z ≤ l› 
        }
    },
    case Seq : _ _ s s₁ s' _ _ ih₁ ih₂ {
      cases' ‹(c₁ ;; c₂, t) ⟹ t'› with _ _ _ _ _ _ t t₁,
      cases' ‹0 ⊢. c₁ ;; c₂›,

      have : s₁ = t₁ [<= l], from ih₁ ‹(c₁, t) ⟹ t₁› ‹0 ⊢. c₁› ‹s = t [<= l]›,
      
      show s' = t' [<= l], from ih₂ ‹(c₂, t₁) ⟹ t'› ‹0 ⊢. c₂› ‹s₁ = t₁ [<= l]›
    },
    case IfTrue : {
      cases' ‹0 ⊢. IF b THEN c₁ ELSE c₂›,

      have : sec₆ b ⊢. c₁, by simpa[nat.zero_max] using ‹max 0 (sec₆ b) ⊢. c₁›,
      have : sec₆ b ⊢. c₂, by simpa[nat.zero_max] using ‹max 0 (sec₆ b) ⊢. c₂›,

      cases ‹(IF b THEN c₁ ELSE c₂, t) ⟹ t'›,
        case IfTrue : { -- IfTrue, IfTrue
          have : 0 <= sec₆ b, from nat.zero_le (sec₆ b),
          have : 0 ⊢. c₁, from anti_monotonicity ‹sec₆ b ⊢. c₁› ‹0 <= sec₆ b›,

          show s' = t' [<= l], from ih ‹(c₁, t) ⟹ t'› ‹0 ⊢. c₁› ‹s = t [<= l]›
        },
        case IfFalse : {
          have : (sec₆ b <= l) ∨ (sec₆ b > l), from le_or_lt (sec₆ b) l,
          cases' ‹(sec₆ b <= l) ∨ (sec₆ b > l)›,
            case inr : { -- IfTrue, IfFalse, (sec₆ b > l)
              have : s = s' [< sec₆ b], from confinement ‹(c₁, s) ⟹ s'› ‹sec₆ b ⊢. c₁›,
              have : t = t' [< sec₆ b], from confinement ‹(c₂, t) ⟹ t'› ‹sec₆ b ⊢. c₂›,

              have : s = s' [<= l], from restrict ‹s = s' [< sec₆ b]› ‹sec₆ b > l›,
              have : t = t' [<= l], from restrict ‹t = t' [< sec₆ b]› ‹sec₆ b > l›,

              show s' = t' [<= l], from
                trans (trans (symm ‹s = s' [<= l]›) ‹s = t [<= l]›) ‹t = t' [<= l]›
            },
            case inl : { -- IfTrue, IfFalse, (sec₆ b <= l)
              rw[noninterference_bexp ‹s = t [<= l]› ‹sec₆ b ≤ l›] at *,
              contradiction
            }
        }
    },
    case IfFalse : {
      cases' ‹0 ⊢. IF b THEN c₁ ELSE c₂›,

      have : sec₆ b ⊢. c₁, by simpa[nat.zero_max] using ‹max 0 (sec₆ b) ⊢. c₁›,
      have : sec₆ b ⊢. c₂, by simpa[nat.zero_max] using ‹max 0 (sec₆ b) ⊢. c₂›,

      cases ‹(IF b THEN c₁ ELSE c₂, t) ⟹ t'›,
        case IfFalse : { -- IfFalse, IfFalse
          have : 0 <= sec₆ b, from nat.zero_le (sec₆ b),
          have : 0 ⊢. c₂, from anti_monotonicity ‹sec₆ b ⊢. c₂› ‹0 <= sec₆ b›,

          show s' = t' [<= l], from ih ‹(c₂, t) ⟹ t'› ‹0 ⊢. c₂› ‹s = t [<= l]›
        },
        case IfTrue : {
          have : (sec₆ b <= l) ∨ (sec₆ b > l), from le_or_lt (sec₆ b) l,
          cases' ‹(sec₆ b <= l) ∨ (sec₆ b > l)›,
            case inr : { -- IfFalse, IfTrue, (sec₆ b > l)
              have : s = s' [< sec₆ b], from confinement ‹(c₂, s) ⟹ s'› ‹sec₆ b ⊢. c₂›,
              have : t = t' [< sec₆ b], from confinement ‹(c₁, t) ⟹ t'› ‹sec₆ b ⊢. c₁›,

              have : s = s' [<= l], from restrict ‹s = s' [< sec₆ b]› ‹sec₆ b > l›,
              have : t = t' [<= l], from restrict ‹t = t' [< sec₆ b]› ‹sec₆ b > l›,

              show s' = t' [<= l], from
                trans (trans (symm ‹s = s' [<= l]›) ‹s = t [<= l]›) ‹t = t' [<= l]›
            },
            case inl : { -- IfFalse, IfTrue, (sec₆ b <= l)
              rw[noninterference_bexp ‹s = t [<= l]› ‹sec₆ b ≤ l›] at *,
              contradiction
            }
        }
    },
    case WhileTrue : _ _ s s₁ s' _ _ _ ih₁ ih₂ {
      cases' ‹0 ⊢. WHILE b DO c›,

      have : sec₆ b ⊢. c, by simpa[nat.zero_max] using ‹max 0 (sec₆ b) ⊢. c›,
      
      cases' ‹(WHILE b DO c, t) ⟹ t'›,
        case WhileTrue : _ _ t t₁ t' _ _ _ { -- WhileTrue, WhileTrue
          have : 0 <= sec₆ b, from nat.zero_le (sec₆ b),
          have : 0 ⊢. c, from anti_monotonicity ‹sec₆ b ⊢. c› ‹0 <= sec₆ b›,

          have : s₁ = t₁ [<= l], from ih₁ ‹(c, t) ⟹ t₁› ‹0 ⊢. c› ‹s = t [<= l]›,

          show s' = t' [<= l], from
            ih₂ ‹(WHILE b DO c, t₁) ⟹ t'› (While ‹max 0 (sec₆ b) ⊢. c›) ‹s₁ = t₁ [<= l]›
        },
        case WhileFalse : _ _ t _ {
          have : (sec₆ b <= l) ∨ (sec₆ b > l), from le_or_lt (sec₆ b) l,
          cases' ‹(sec₆ b <= l) ∨ (sec₆ b > l)›,
            case inr : { -- WhileTrue, WhileFalse, (sec₆ b > l)
              have : max (sec₆ b) (sec₆ b) ⊢. c, by simpa[max_self] using ‹sec₆ b ⊢. c›,
              
              have : s = s₁ [< sec₆ b], from confinement ‹(c, s) ⟹ s₁› ‹sec₆ b ⊢. c›,
              have : s₁ = s' [< sec₆ b], from 
                confinement ‹(WHILE b DO c, s₁) ⟹ s'› (While ‹max (sec₆ b) (sec₆ b) ⊢. c›),

              have : s = s₁ [<= l], from restrict ‹s = s₁ [< sec₆ b]› ‹sec₆ b > l›,
              have : s₁ = s' [<= l], from restrict ‹s₁ = s' [< sec₆ b]› ‹sec₆ b > l›,

              show s' = t [<= l], from
                symm (trans (symm ‹s = t [<= l]›) (trans ‹s = s₁ [<= l]› ‹s₁ = s' [<= l]›))
            },
            case inl : { -- WhileTrue, WhileFalse, (sec₆ b <= l)  
              rw[noninterference_bexp ‹s = t [<= l]› ‹sec₆ b ≤ l›] at *,
              contradiction
            }
        }
    },
    case WhileFalse : _ _ s _ {
      cases' ‹0 ⊢. WHILE b DO c›,

      have : sec₆ b ⊢. c, by simpa[nat.zero_max] using ‹max 0 (sec₆ b) ⊢. c›,
      
      cases' ‹(WHILE b DO c, t) ⟹ t'›,
        case WhileFalse : _ _ t _ { -- WhileFalse, WhileFalse
          show s = t [<= l], by assumption
        },
        case WhileTrue : _ _ t t₁ {
          have : (sec₆ b <= l) ∨ (sec₆ b > l), from le_or_lt (sec₆ b) l,
          cases' ‹(sec₆ b <= l) ∨ (sec₆ b > l)›,
            case inr : { -- WhileFalse, WhileTrue, (sec₆ b > l)
              have : max (sec₆ b) (sec₆ b) ⊢. c, by simpa[max_self] using ‹sec₆ b ⊢. c›,

              have : t = t₁ [< sec₆ b], from confinement ‹(c, t) ⟹ t₁› ‹sec₆ b ⊢. c›,
              have : t₁ = t' [< sec₆ b], from 
                confinement ‹(WHILE b DO c, t₁) ⟹ t'› (While ‹max (sec₆ b) (sec₆ b) ⊢. c›),
              
              have : t = t₁ [<= l], from restrict ‹t = t₁ [< sec₆ b]› ‹sec₆ b > l›,
              have : t₁ = t' [<= l], from restrict ‹t₁ = t' [< sec₆ b]› ‹sec₆ b > l›,
              
              show s = t' [<= l], from
                trans (trans ‹s = t [<= l]› ‹t = t₁ [<= l]›) ‹t₁ = t' [<= l]›
            },
            case inl : { -- WhileFalse, WhileTrue, (sec₆ b <= l)
              rw[noninterference_bexp ‹s = t [<= l]› ‹sec₆ b ≤ l›] at *,
              contradiction
            }
        }
    } 
end