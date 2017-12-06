From Autosubst Require Import Autosubst.

(* Formalization of Peano's arithmetic.                             *
 * Introduction of the inductive types of Peano naturals and Peano  *
 * formulae                                                         *)

Inductive Pnat : Set :=
  | PO : Pnat
  | PS : Pnat -> Pnat
  | plus : Pnat -> Pnat -> Pnat
  | times : Pnat -> Pnat -> Pnat
  | Pvar : var -> Pnat.

Inductive Pprop :=
  | Pfalse : Pprop
  | Ptrue : Pprop
  | Peq : Pnat -> Pnat -> Pprop
  | Pfa (_ : {bind Pnat in Pprop}) (* {bind Pnat in Pprop} -> Pprop *)
  | Pex (_ : {bind Pnat in Pprop})
  | Pim : Pprop -> Pprop -> Pprop
  | Pan : Pprop -> Pprop -> Pprop
  | Por : Pprop -> Pprop -> Pprop
  | dummy (_ : var). (* type var -> Pprop *)

(*
Bind Scope pnat_scope with Pnat.
Bind Scope pprop_scope with Pprop.

Open Scope pnat_scope.
Open Scope pprop_scope.

*)

Notation "'Pno' f" := (Pim f Pfalse) (at level 0).



(* To make autosubst work on custom inductive types Pnat and Pprop  *)

Instance Ids_Pnat : Ids Pnat. derive. Defined.
Instance Rename_Pnat : Rename Pnat. derive. Defined.
Instance Subst_Pnat : Subst Pnat. derive. Defined.

Instance SubstLemmas_Pnat : SubstLemmas Pnat. derive. Qed.

Instance Hsubst_Pprop : HSubst Pnat Pprop. derive. Defined.

Instance Ids_Pprop : Ids Pprop. derive. Defined.
Instance Rename_Pprop : Rename Pprop. derive. Defined.
Instance Subst_Pprop : Subst Pprop. derive. Defined.

Instance HSubstLemmas_Pprop : HSubstLemmas Pnat Pprop. derive. Qed.
Instance SubstHSubstComp_Pnat_Pprop : SubstHSubstComp Pnat Pprop. derive. Qed.
Instance SubstLemmas_Pprop : SubstLemmas Pprop. derive. Qed.



(* Test for substitution on expressions of type Pnat                *)

Check ((Pvar 0).[PO/]).
Eval compute in ((Pvar 0).[PO/]).



(* Test for substitution on expressions of type Pprop               *)

Check (Pfa (Peq (Pvar 0) (Pvar 0))).
Eval compute in (Pfalse.|[PO/]).
Eval compute in ((Peq (Pvar 0) (Pvar 0)).|[PO/]).
Eval compute in ((Peq (Pvar 0) (Pvar 1)).|[PO.:ids]).



(* Definition of the context (for natural deduction)                *
 * nilc is the empty context                                        *
 * intc is a counter for variables present in the context           *
 * assume appends a proposition to a context                        *)

Inductive Ctxt : Type :=
  | nilc : Ctxt
  | intc : Ctxt -> Ctxt 
  | assume : Pprop -> Ctxt -> Ctxt. 



(* var_to_nat is a function that retrieves the x-th element in a list of nat. *
 * The list l stores natural values that correspond to Peano-variables :      *
 * the i_th element of the list l is thus the nat-interpretation of the       *
 * Peano-variable i                                                           *)

Fixpoint var_to_nat (x : var) (l : list nat) : nat :=
  match x, l  with
   | 0, (cons v _) => v
   | S y, (cons _ l)  => (var_to_nat y l)
   | _, _ => 0
  end.


Fixpoint refl_Pnat (x : Pnat) (l : list nat) : nat :=
  match x with
   | PO => O
   | PS x => S (refl_Pnat x l)
   | plus y z => (refl_Pnat y l) + (refl_Pnat z l)
   | times y z => (refl_Pnat y l) * (refl_Pnat z l)
   | Pvar y => var_to_nat y l
  end.

Eval compute in ((Pvar O).[ren(+ 2)]).

Fixpoint refl_Pprop (P : Pprop) (l : list nat) : Prop :=
  match P with
   | Pfalse => False
   | Ptrue => True
   | Peq x y => (refl_Pnat x l) = (refl_Pnat y l)
    (* if a forall is the n-th binder that is seen by the reflection,
       then the bound variable x will be the n-th variable stored in
       the list l. All these variables will be translated into nat
       using this index, and the function refl_Pnat for a P-variable *) 
   | Pfa Q => forall (x : nat), refl_Pprop Q (cons x l)
   | Pex Q => exists (x : nat), refl_Pprop Q (cons x l)
   | Pim Q R => (refl_Pprop Q l) -> (refl_Pprop R l)
   | Pan Q R => (refl_Pprop Q l) /\ (refl_Pprop R l)
   | Por Q R => (refl_Pprop Q l) \/ (refl_Pprop R l)
   | dummy x => True
  end.

Fixpoint refl_Ctxt (C : Ctxt) (l : list nat) : Prop :=
  match C with
    | nilc => False
    | intc D => refl_Ctxt D l
    | assume P D => (refl_Pprop P l)/\(refl_Ctxt D l)
  end.


(* On va tester si refl_Pprop(∀x.∃y.x = S(y) ∨ x = 0) se réduit     *
 * bien vers l’objet de type Prop forall x, exists y, x=(S y)\/x=O  *
 * comme cela devrait être le cas selon l'énoncé                    *)

Eval compute in (refl_Pprop (Pfa (Pex (Por (Peq (Pvar 1) (PS (Pvar 0))) (Peq (Pvar 1) (PO))))) nil).

Eval compute in (refl_Pprop (Pfa (Pfa (Pim (Peq (PS (Pvar 1)) (PS (Pvar 0))) (Peq (Pvar 1) (Pvar 0)) ))) nil).

Axiom succ_is_non_zero : refl_Pprop (Pfa (Pno (Peq (PS (Pvar 0)) PO))) nil.

Axiom non_zero_has_succ : refl_Pprop (Pfa (Pex (Pim (Pno (Peq (Pvar 1) PO)) (Peq (PS (Pvar 0)) (Pvar 1))))) nil.

Axiom eq_succ_implies_eq : refl_Pprop (Pfa (Pfa (Pim (Peq (PS (Pvar 1)) (PS (Pvar 0))) (Peq (Pvar 1) (Pvar 0)) ))) nil.

Axiom zero_is_neutral : refl_Pprop (Pfa (Peq (plus (Pvar 0) (PO)) (Pvar 0))) nil.

Axiom succ_can_extend : refl_Pprop (Pfa (Pfa (Peq (plus (PS (Pvar 1)) (Pvar 0)) (PS (plus (Pvar 1) (Pvar 0)))))) nil.

Axiom zero_absorbs : refl_Pprop (Pfa (Peq (times PO (Pvar 0)) (PO))) nil.

Axiom times_distributes : refl_Pprop (Pfa (Pfa (Peq (times (PS (Pvar 1)) (Pvar 0)) (plus (times (Pvar 1) (Pvar 0)) (Pvar 0))))) nil.

Axiom reflexivity : refl_Pprop (Pfa (Pfa (Pim (Peq (Pvar 0) (Pvar 1)) (Peq (Pvar 1) (Pvar 0))))) nil.

Axiom elimination : refl_Pprop (Pfa (Pfa (Pfa (Pim (Peq (plus (Pvar 0) (Pvar 1)) (plus (Pvar 0) (Pvar 2))) (Peq (Pvar 1) (Pvar 2)))))) nil.

Axiom recurrence_scheme : forall (P : Pprop), refl_Pprop (P.|[PO/]) nil -> refl_Pprop (Pfa (Pim (P.|[Pvar 0/]) (P.|[(PS (Pvar 0))/]))) nil -> refl_Pprop (Pfa (P.|[Pvar 0/])) nil.

(* Axiom recurrence_scheme : forall (P : Pprop), refl_Pprop (Pim (P.|[PO/]) (Pim (Pfa (Pim (P (Pvar 0)) (P (PS (Pvar 0))))) (Pfa (P (Pvar 0))))) nil. *)

Fixpoint find_lift (G : Ctxt): nat :=
  match G with
  | nilc => 0
  | intc H => find_lift H + 1
  | assume _ H => find_lift H
  end.



(*
Fixpoint is_free (A : Prop) (x : Pnat) := 

Fixpoint up_free (A : Pprop) : Pnat -> Pnat := fun x => if (is_free x A) then (PS x) else x.


Fixpoint up (C : Pprop) (A : Pprop) : Pprop := C.[up_free A].


Eval compute in (find_lift (assume (Peq (Pvar 0)(Pvar 0)) (intc (assume (Peq (Pvar 0) PO) (intc nilc))))).

*)


(* Logical rules for natural deduction *)

Inductive ded_nat : Ctxt -> Pprop -> Prop :=

  | axiom G A : ded_nat (assume A G) A

  | weak G A B : ded_nat G A -> ded_nat (assume B (intc G)) A 

  | impi G A B : ded_nat (assume A (intc G)) B -> ded_nat G (Pim A B) 

  | impe G A B : ded_nat G (Pim A B) -> ded_nat G A -> ded_nat G B 

  | andi G A B : ded_nat G A -> ded_nat G B -> ded_nat G (Pan A B)

  | andle G A B : ded_nat G (Pan A B) -> ded_nat G A

  | andre G A B : ded_nat G (Pan A B) -> ded_nat G B

  | orli G A B : ded_nat G A -> ded_nat G (Por A B)

  | orri G A B : ded_nat G B -> ded_nat G (Por A B)

  | ore G A B C : ded_nat G (Por A B) -> ded_nat (assume A (intc G)) C -> ded_nat (assume B (intc G)) C -> ded_nat G C

  | bote G A : ded_nat G Pfalse -> ded_nat G A

  | foralli G A : ded_nat (intc G) A -> ded_nat G (Pfa A)

  | foralle G A t : ded_nat G (Pfa A) -> ded_nat G (A.|[t.:ids])

  | existi G A t : ded_nat G (A.|[t.:ids]) -> ded_nat G (Pex A)

  | existe G A C : ded_nat G (Pex A) -> ded_nat (assume A (intc G)) (C.|[ren(+1)]) -> ded_nat G C.


(* 4.2 Questions : implémentation                                   *
 * On demande, dans un premier temps d’écrire en Coq les fonctions  *
 * de réflection. Ensuite, de prouver que s’il existe une           *
 * dérivation dans l’arithmétique de Peano intuitionniste d’une     *
 * formule P dans un contexte Γ, alors, il existe un terme Coq de   *
 * type tr(Γ) → tr(P). C’est cette dernière étape qui constitue la  *
 * réflection proprement dite.                                      *)


Theorem reflection (G : Ctxt) (P : Pprop): ded_nat G P -> (refl_Ctxt G nil) -> (refl_Pprop P nil).
Proof.
induction 1.
- simpl; intros; destruct H; induction A; asimpl.
  -- trivial.
  -- trivial.
  -- ainv. 



Fixpoint Friedman (P : Pprop) (A : Pprop) : Pprop :=
  match P with
    | Pfalse => Por Pfalse A
    | Ptrue => Ptrue
    | Peq x y => Por (Peq x y) A
    | Pfa B => Pfa (Pim (Pim (Friedman B A) A) A)
    | Pex B => Pim (Pim (Pex (Friedman B A)) A) A
    | Pim B C => Pim (Pim (Pim (Friedman B A) A) A) (Pim (Pim (Friedman C A) A) A)
    | Pan B C => Pan (Pim (Pim (Friedman B A) A) A) (Pim (Pim (Friedman C A) A) A)
    | Por B C => Por (Pim (Pim (Friedman B A) A) A) (Pim (Pim (Friedman C A) A) A)
    | dummy x => Ptrue
  end.

Fixpoint Friedman_ctxt (C : Ctxt) (A : Pprop) :=
  match C with
    | nilc => nilc
    | intc D => Friedman_ctxt D A
    | assume P D => assume (Friedman P A) (Friedman_ctxt D A)
  end.

 (*
Lemma peano_to_heyting G P : ded_nat G P -> ded_nat_heyting G P.
Defined.
*)

Fixpoint not_quant (P : Pprop) : Prop :=
  match P with
    | Pfalse => True
    | Ptrue => True
    | Peq x y => True
    | Pfa B => False
    | Pex B => False
    | Pim B C => (not_quant B) /\ (not_quant C)
    | Pan B C => (not_quant B) /\ (not_quant C)
    | Por B C => (not_quant B) /\ (not_quant C)
    | dummy x => True
  end.


Lemma friedman_equiv_A_disjunction (P : Pprop) (A : Pprop) : (not_quant P) -> ((Friedman P A -> Por P A) /\ (Por P A -> Friedman P A)).





