  From Autosubst Require Import Autosubst.

(* Formalisation de l'arithmétique de Peano                         *
 * Introduction des types inductifs corespondant aux entiers de     *
 * Peano (Pnat) et aux propriétés portant sur ces entiers (Pprop)   *)

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


Notation "'Pno' f" := (Pim f Pfalse) (at level 0).



(* Les déclarations suivantes proviennent du manuel d'autosubst et  *
 * permettent de faire fonctionner la substitution sur les          *
 * expressions de type Pnat et Pprop.                               *)

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



(* On teste la substitution sur des expressions de type Pnat        *)

Check ((Pvar 0).[PO/]).
Eval compute in ((Pvar 0).[PO/]).

(* On teste la substitution sur des expressions de type Pprop       *)

Check (Pfa (Peq (Pvar 0) (Pvar 0))).
Eval compute in (Pfalse.|[PO/]).
Eval compute in ((Peq (Pvar 0) (Pvar 0)).|[PO/]).
Eval compute in ((Peq (Pvar 0) (Pvar 1)).|[PO.:ids]).



(* On définit les 7 axiomes de Peano :                              *
 * 1. ∀x.¬S(x) = 0                                                  *
 * 2. ∀x.∃y.(¬x = 0 ⇒ S(y) = x)                                     *
 * 3. ∀x.∀y.(S(x) = S(y) ⇒ x = y)                                   *
 * 4. ∀x.x + 0 = x                                                  *
 * 5. ∀x.∀y.S(x) + y = S(x + y)                                     *
 * 6. ∀x.(0 ∗ x = 0)                                                *
 * 7. ∀x.∀y.S(x) ∗ y = (x ∗ y) + y                                  *)

Definition succ_is_non_zero : Pprop :=
  Pfa (Pno (Peq (PS (Pvar 0)) PO)).

Definition non_zero_has_succ : Pprop :=
  Pfa (Pex (Pim (Pno (Peq (Pvar 1) PO)) (Peq (PS (Pvar 0)) (Pvar 1)))).

Definition eq_succ_implies_eq : Pprop :=
  Pfa (Pfa (Pim (Peq (PS (Pvar 1)) (PS (Pvar 0))) (Peq (Pvar 1) (Pvar 0)) )).

Definition zero_is_neutral : Pprop :=
  Pfa (Peq (plus (Pvar 0) (PO)) (Pvar 0)).

Definition succ_can_extend : Pprop :=
  Pfa (Pfa (Peq (plus (PS (Pvar 1)) (Pvar 0)) (PS (plus (Pvar 1) (Pvar 0))))).

Definition zero_absorbs : Pprop :=
  Pfa (Peq (times (Pvar 0) PO) (PO)).

Definition times_distributes : Pprop :=
  Pfa (Pfa (Peq (times (Pvar 1) (PS (Pvar 0))) (plus (times (Pvar 1) (Pvar 0)) (Pvar 1)))).

(* On ajoute aussi le schéma de récurrence, paramétré par un objet  *
 * de type Pprop                                                    *)

Definition recurrence_scheme : Pprop -> Pprop :=
  fun (P : Pprop) => (Pim (P.|[PO/]) (Pim (Pfa (Pim (P.|[Pvar 0/]) (P.|[(PS (Pvar 0))/]))) (Pfa (P.|[Pvar 0/])))).

(* On traite également le tiers exclu comme un axiome, qui          *
 * permettra d'étendre l'arithmétique de Heyting en l'arithmétique  *
 * de Heyting.                                                      *)

Definition excluded_middle : Pprop -> Pprop :=
  fun (P : Pprop) => (Por P (Pno P)).

(* Enfin, on définit les propriétés habituelles de l’égalité        *
 * (reflexivité, élimination).                                      *)

Definition reflexivity : Pprop :=
  Pfa (Pfa (Pim (Peq (Pvar 0) (Pvar 1)) (Peq (Pvar 1) (Pvar 0)))).

Definition elimination : Pprop :=
  Pfa (Pfa (Pfa (Pim (Peq (plus (Pvar 0) (Pvar 1)) (plus (Pvar 0) (Pvar 2))) (Peq (Pvar 1) (Pvar 2))))).



(* Définition du contexte Γ utilisé dans la déduction naturelle:    *
 *   -- nilc est les contexte vide;                                 *
 *   -- intc signale une déclaration de variable;                   *
 *   -- assume ajoute une proposition (contenant éventuellement des *
 *      variables libres) à un contexte.                            *
 * Note : on suppose qu'un contexte bien formé est un contexte où   *
 * il n'existe pas de formule contenant de variable libre non liée  *
 * par un intc, càd que l'on ne pourra écrire Pvar k dans une       *
 * formule que si l'on a traversé au moins k+1 'binders' intc.      *)

Inductive Ctxt : Type :=
  | nilc : Ctxt
  | intc : Ctxt -> Ctxt 
  | assume : Pprop -> Ctxt -> Ctxt. 

(* On teste la définition du contexte sur le contexte               *
 * [x : nat; x = x; y : nat; y = 2]                                 *
 * Note : on choisit de placer les déclarations de variables en     *
 * amont des propositions qui les concernent, afin de faciliter la  *
 * réflection sur les contextes dans la suite.                      *)

Eval compute in (intc (assume (Peq (Pvar 0) (Pvar 0)) (intc (assume (Peq (Pvar 0) (PS (PS (PO)))) (nilc))))).

(* On définit ensuite un contexte formé par les axiomes qui         *
 * permettent de paramétrer la déduction naturelle, le problème     *
 * étant que le schéma d'induction et le tiers exclu (pour le cas   * 
 * de la logique classique) ne peuvent être ajoutés à ce contexte   *)

Definition HAxioms : Ctxt :=
  assume succ_is_non_zero (assume non_zero_has_succ (assume eq_succ_implies_eq (assume zero_is_neutral (assume succ_can_extend (assume zero_absorbs (assume times_distributes (nilc))))))).



(* Dans cette section on définit la fonction de réflection.         *
 * Cette fonction est en fait divisée en trois :                    *
 *   -- une réflection pour les entiers de Peano de type Pnat;      *
 *   -- une réflection pour les proposition de Peano de type Pprop; *
 *   -- une réflection sur les contextes de type Ctxt.              *
 * On va également paramétrer la fonction de réflection par une     *
 * interprétation des variables (de type var), qui prend la forme   *
 * d'une liste de naturels (de type nat). La fonction var_to_nat    *
 * permet alors de retourner l'interprétation de la variable i en   *
 * tant que naturel.                                                *)

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


Fixpoint refl_Pprop (P : Pprop) (l : list nat) : Prop :=
  match P with
   | Pfalse => False
   | Ptrue => True
   | Peq x y => (refl_Pnat x l) = (refl_Pnat y l)
   | Pfa Q => forall (x : nat), refl_Pprop Q (cons x l)
   | Pex Q => exists (x : nat), refl_Pprop Q (cons x l)
   | Pim Q R => (refl_Pprop Q l) -> (refl_Pprop R l)
   | Pan Q R => (refl_Pprop Q l) /\ (refl_Pprop R l)
   | Por Q R => (refl_Pprop Q l) \/ (refl_Pprop R l)
   | dummy x => True
  end.


Fixpoint refl_Ctxt (C : Ctxt) (l : list nat) : Prop :=
  match C with
    | nilc => True
    | intc D => forall x, refl_Ctxt D (cons x l)
    | assume P D => (refl_Pprop P l)/\(refl_Ctxt D l)
  end.


(* On va tester si refl_Pprop (∀x.∃y.x = S(y) ∨ x = 0) se réduit    *
 * bien vers l’objet de type Prop forall x, exists y, x=(S y)\/x=O  *
 * comme cela devrait être le cas selon l'énoncé                    *)

Eval compute in (refl_Pprop (Pfa (Pex (Por (Peq (Pvar 1) (PS (Pvar 0))) (Peq (Pvar 1) (PO))))) nil).

Eval compute in (refl_Pprop (Pfa (Pfa (Pim (Peq (PS (Pvar 1)) (PS (Pvar 0))) (Peq (Pvar 1) (Pvar 0)) ))) nil).

(* On teste la réflection sur le contexte                           *
 * [x : nat; x = x; y : nat; y = x], qui devrait donner             *
 * forall x : nat, x = x /\ (forall y : nat, y = x /\ True)         *) 

Eval compute in (refl_Ctxt (intc (assume (Peq (Pvar 0) (Pvar 0)) (intc (assume (Peq (Pvar 0) (Pvar 1)) (nilc))))) nil).



(* Dans cette section on définit les règles logiques de la          *
 * déduction naturelle adaptées aux objets de type Pprop et aux     *
 * contextes de type Ctxt. La définition est 'dédoublée' en une     *
 * définition 'intuitionniste' (sans règle em) et une définition    *
 * 'classique' (avec une règle em) : c'est un peu maladroit mais je *
 * n'ai pas réussi à faire mieux malheureusement.                   *)

Inductive ded_nat : Ctxt -> Pprop -> Prop :=

  | axiom G A : ded_nat (assume A G) A

  | weak G A B : ded_nat G A -> ded_nat (assume B G) A 

  | impi G A B : ded_nat (assume A G) B -> ded_nat G (Pim A B) 

  | impe G A B : ded_nat G (Pim A B) -> ded_nat G A -> ded_nat G B 

  | andi G A B : ded_nat G A -> ded_nat G B -> ded_nat G (Pan A B)

  | andle G A B : ded_nat G (Pan A B) -> ded_nat G A

  | andre G A B : ded_nat G (Pan A B) -> ded_nat G B

  | orli G A B : ded_nat G A -> ded_nat G (Por A B)

  | orri G A B : ded_nat G B -> ded_nat G (Por A B)

  | ore G A B C : ded_nat G (Por A B) -> ded_nat (assume A G) C -> ded_nat (assume B G) C -> ded_nat G C

  | bote G A : ded_nat G Pfalse -> ded_nat G A

  | topi G : ded_nat G Ptrue

  | foralli G A : ded_nat (intc G) A -> ded_nat G (Pfa A)

  | foralle G A t : ded_nat G (Pfa A) -> ded_nat G (A.|[t.:ids])

  | existi G A t : ded_nat G (A.|[t.:ids]) -> ded_nat G (Pex A)

  | existe G A C : ded_nat G (Pex A) -> ded_nat (assume A (intc G)) (C.|[ren(+1)]) -> ded_nat G C.



Inductive ded_nat_em : Ctxt -> Pprop -> Prop :=

  | axiom_em G A : ded_nat_em (assume A G) A

  | weak_em G A B : ded_nat_em G A -> ded_nat_em (assume B G) A 

  | impi_em G A B : ded_nat_em (assume A G) B -> ded_nat_em G (Pim A B) 

  | impe_em G A B : ded_nat_em G (Pim A B) -> ded_nat_em G A -> ded_nat_em G B 

  | andi_em G A B : ded_nat_em G A -> ded_nat_em G B -> ded_nat_em G (Pan A B)

  | andle_em G A B : ded_nat_em G (Pan A B) -> ded_nat_em G A

  | andre_em G A B : ded_nat_em G (Pan A B) -> ded_nat_em G B

  | orli_em G A B : ded_nat_em G A -> ded_nat_em G (Por A B)

  | orri_em G A B : ded_nat_em G B -> ded_nat_em G (Por A B)

  | ore_em G A B C : ded_nat_em G (Por A B) -> ded_nat_em (assume A G) C -> ded_nat_em (assume B G) C -> ded_nat_em G C

  | bote_em G A : ded_nat_em G Pfalse -> ded_nat_em G A

  | topi_em G : ded_nat_em G Ptrue

  | foralli_em G A : ded_nat_em (intc G) A -> ded_nat_em G (Pfa A)

  | foralle_em G A t : ded_nat_em G (Pfa A) -> ded_nat_em G (A.|[t.:ids])

  | existi_em G A t : ded_nat_em G (A.|[t.:ids]) -> ded_nat_em G (Pex A)

  | existe_em G A C : ded_nat_em G (Pex A) -> ded_nat_em (assume A (intc G)) (C.|[ren(+1)]) -> ded_nat_em G C

  | em G A : ded_nat_em G (Por A (Pno A)).


(* 4.2 Questions : implémentation                                   *
 * On demande, dans un premier temps d’écrire en Coq les fonctions  *
 * de réflection. Ensuite, de prouver que s’il existe une           *
 * dérivation dans l’arithmétique de Peano intuitionniste d’une     *
 * formule P dans un contexte Γ, alors, il existe un terme Coq de   *
 * type tr(Γ) → tr(P). C’est cette dernière étape qui constitue la  *
 * réflection proprement dite.                                      *)

(* On peut commencer par prouver que les axiomes de l'arithmétique  *
 * de Peano définis ci-dessus sont prouvables dans Coq.             *)


Theorem succ_is_non_zero_is_provable : refl_Pprop succ_is_non_zero nil.
Proof.
simpl refl_Pprop; apply PeanoNat.Nat.neq_succ_0.
Qed.

Theorem eq_succ_implies_eq_is_provable : refl_Pprop eq_succ_implies_eq nil.
Proof.
simpl refl_Pprop; apply PeanoNat.Nat.succ_inj.
Qed.

Theorem zero_is_neutral_is_provable : refl_Pprop zero_is_neutral nil.
Proof.
simpl refl_Pprop; apply PeanoNat.Nat.add_0_r.
Qed.

Theorem succ_can_extend_is_provable : refl_Pprop succ_can_extend nil.
Proof.
simpl refl_Pprop; trivial.
Qed.

Theorem zero_absorbs_is_provable : refl_Pprop zero_absorbs nil.
Proof.
simpl refl_Pprop; apply PeanoNat.Nat.mul_0_r.
Qed.

Theorem times_distributes_is_provable : refl_Pprop times_distributes nil.
Proof.
simpl refl_Pprop; apply PeanoNat.Nat.mul_succ_r.
Qed.

(*

Theorem recurrence_scheme_is_provable : forall P : Pprop, (refl_Pprop (recurrence_scheme P) nil).
Proof.
intros.
simpl refl_Pprop.
intros.
revert.

*)

Theorem reflection (G : Ctxt) (P : Pprop): ded_nat G P -> (refl_Ctxt G nil) -> (refl_Pprop P nil).
Proof.
induction 1.
- simpl; intros; destruct H; trivial.
- simpl; intros; destruct H0; apply IHded_nat; trivial.
- simpl; intros; apply IHded_nat; simpl; refine (conj _ _); trivial.
- intros; simpl refl_Pprop in IHded_nat1; apply IHded_nat1; trivial; apply IHded_nat2; trivial.
- simpl; intros; refine (conj _ _).
  -- apply IHded_nat1; trivial.
  -- apply IHded_nat2; trivial.
- intros; simpl refl_Pprop in IHded_nat; apply IHded_nat; trivial.
- intros; simpl refl_Pprop in IHded_nat; apply IHded_nat; trivial.
- simpl; intros; left; apply IHded_nat; trivial.
- simpl; intros; right; apply IHded_nat; trivial.
- intros; simpl refl_Pprop in IHded_nat1.
  simpl refl_Ctxt in IHded_nat2; simpl refl_Ctxt in IHded_nat3.
  pose (H3 := IHded_nat1 H2); case H3.
  -- intros; apply IHded_nat2; refine (conj _ _).
     --- trivial.
     --- trivial.
  -- intros; apply IHded_nat3; refine (conj _ _).
     --- trivial.
     --- trivial.
- intros; simpl refl_Pprop in IHded_nat; pose (H1 := IHded_nat H0); case H1.
- simpl; intros; exact I.
- simpl.
 intros; simpl refl_Ctxt in IHded_nat.

Admitted.

(* La preuve du théorème de reflection permettrait de montrer que   *
 * tout ce qui est prouvable dans notre formalisme intuitionniste   *
 * est aussi prouvable dans Coq, autrement dit que notre formalisme *
 * est consistant avec Coq.                                         *)


(* Dans cette section on définit la traduction de Friedman pour les *
 * propriétés et les contextes.                                     *)

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
    | dummy x => Por (dummy x) A 
  end.

Fixpoint Friedman_ctxt (C : Ctxt) (A : Pprop) :=
  match C with
    | nilc => nilc
    | intc D => Friedman_ctxt D A
    | assume P D => assume (Friedman P A) (Friedman_ctxt D A)
  end.



(* Lemme 1: On étend, de manière triviale, la transformée par double*
 * négation aux contextes. S’il existe une dérivation de Γ t P dans *
 * l’arithmétique de Peano, il existe une dérivation de             *
 * Γ^A t ¬^A ¬^A P^A dans l’arithmétique de Heyting.                *)  

Lemma Peano_Heyting (P : Pprop) (C : Ctxt) (A : Pprop) : (ded_nat_em C P ) -> ded_nat (Friedman_ctxt C A) (Pim (Pim (Friedman P A) A) A).
Proof.
induction 1.
- simpl.
  apply (impi ((assume (Friedman A0 A) (Friedman_ctxt G A))) ((Pim (Friedman A0 A) A)) (A)).
  apply (impe (assume (Pim (Friedman A0 A) A) (assume (Friedman A0 A) (Friedman_ctxt G A))) (Friedman A0 A) A).
 -- apply (axiom (assume (Friedman A0 A) (Friedman_ctxt G A)) (Pim (Friedman A0 A) A)).
 -- apply (weak ((assume (Friedman A0 A) (Friedman_ctxt G A))) ((Friedman A0 A)) ((Pim (Friedman A0 A) A))).
    apply (axiom ((Friedman_ctxt G A)) ((Friedman A0 A))).
- simpl.
  apply (impi ((assume (Friedman B A) (Friedman_ctxt G A))) ((Pim (Friedman A0 A) A)) (A)).
  admit.
- simpl.
admit.
- simpl.
  apply (impi ((Friedman_ctxt G A)) (Pim (Friedman B A) A) A).
  apply (impe ((assume (Pim (Friedman B A) A) (Friedman_ctxt G A))) (Friedman B A) (A)).
  -- apply (axiom ( (Friedman_ctxt G A)) ((Pim (Friedman B A) A))).
  -- admit.
- apply (impi ((Friedman_ctxt G A)) ((Pim (Friedman (Pan A0 B) A) A)) (A)).
  apply (impe ((assume (Pim (Friedman (Pan A0 B) A) A)
     (Friedman_ctxt G A))) (Friedman (Pan A0 B) A) (A)).
  -- apply (axiom ( (Friedman_ctxt G A)) ((Pim (Friedman (Pan A0 B) A) A))).
  -- simpl Friedman.
     apply (andi ((assume (Pim (Pan (Pim (Pim (Friedman A0 A) A) A) (Pim (Pim (Friedman B A) A) A)) A) (Friedman_ctxt G A))) ((Pim (Pim (Friedman A0 A) A) A)) ((Pim (Pim (Friedman B A) A) A))).
     --- apply (impi ((assume (Pim (Pan (Pim (Pim (Friedman A0 A) A) A) (Pim (Pim (Friedman B A) A) A)) A) (Friedman_ctxt G A))) ((Pim (Friedman A0 A) A)) (A)).
         apply (impe ((assume (Pim (Friedman A0 A) A) (assume (Pim (Pan (Pim (Pim (Friedman A0 A) A) A) (Pim (Pim (Friedman B A) A) A)) A) (Friedman_ctxt G A)))) (A0) (A)).   
         ----- 
(* Lemme 2 : Les formules sans quantificateurs sont décidables      *
 * (en particulier dans Coq).                                       *)

(* On définit d'abord une fonction qui détermine si une formule     *
 * contient ou non des quantifieurs :                               *)

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


Lemma not_quant_decidable (P : Pprop) (A : Pprop) : not_quant P -> (refl_Pprop (Friedman P A) nil) \/ (refl_Pprop (Pno (Friedman P A)) nil).
Proof.
induction P, A; simpl refl_Pprop.
- right.
right.



(* Lemme 3 : Soit P une formule sans quantificateurs. On a, dans    * 
 * Coq, P^A ⇐⇒ P ∨ A.                                               *)

Lemma Friedman_equiv_A_disj (P : Pprop) (A : Pprop) : (not_quant P) -> ((Friedman P A -> Por P A) /\ (Por P A -> Friedman P A)).




