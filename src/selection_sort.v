(* begin hide *)
Require Import Arith List Lia.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.
Require Import Recdef.
(* end hide *)

(** A função [select_min] a seguir, recebe uma lista de naturais e retorna o menor elemento desta lista. Se a lista for vazia, [select_min nil] retorna None. *)

Function select_min (l : list nat) {measure length l} : option nat :=
  match l with
  | nil => None
  | h::nil => Some h
  | h1::h2::tl => if h1 <=? h2 then select_min (h1::tl) else select_min (h2::tl)
  end.
Proof.
  - auto.
  - auto.
Defined.

Definition le_all x l := forall y, In y l -> x <= y.

(** A correção da função [select_min] é estabelecida provando-se que, se [select_min l] retorna um natural [m] então [m] é menor ou igual do que todos os elementos de [l]. *)

Lemma select_min_correct : forall l m, select_min l = Some m -> le_all m l.
Proof.
  (* O mínimo devolvido é um piso da lista (lema pedido no enunciado). *)
Lemma select_min_correct : forall l m, select_min l = Some m -> le_all m l.
Proof.
  intro l. functional induction (select_min l); intros m H.
  - discriminate H.                         (* nil: None <> Some m *)
  - injection H as H. subst.                (* [h]: m = h *)
    intros z Hz. simpl in Hz. destruct Hz as [Hz | Hz].
    + subst. apply le_n.                     (* z = m *)
    + contradiction.                         (* z em nil *)
  - (* h1 <= h2: recursao em (h1::tl) *)
    apply Nat.leb_le in e0.
    assert (Hpiso : le_all m (h1::tl)) by (apply IHo; exact H).
    intros z Hz. simpl in Hz. destruct Hz as [Hz | [Hz | Hz]].
    + subst. apply Hpiso. simpl. left. reflexivity.                       (* z = h1 *)
    + subst. assert (m <= h1) by (apply Hpiso; simpl; left; reflexivity). lia. (* z = h2 *)
    + apply Hpiso. simpl. right. exact Hz.                                (* z em tl *)
  - (* h1 > h2: recursao em (h2::tl) *)
    apply Nat.leb_gt in e0.
    assert (Hpiso : le_all m (h2::tl)) by (apply IHo; exact H).
    intros z Hz. simpl in Hz. destruct Hz as [Hz | [Hz | Hz]].
    + subst. assert (m <= h2) by (apply Hpiso; simpl; left; reflexivity). lia. (* z = h1 *)
    + subst. apply Hpiso. simpl. left. reflexivity.                       (* z = h2 *)
    + apply Hpiso. simpl. right. exact Hz.                                (* z em tl *)
Qed.

(* O mínimo devolvido pertence à lista. *)
Lemma select_min_in : forall l m, select_min l = Some m -> In m l.
Proof.
  intro l. functional induction (select_min l); intros m H.
  - discriminate H.
  - injection H as H. subst. simpl. left. reflexivity.
  - apply IHo in H. simpl in H. simpl. destruct H as [H | H].
    + left. exact H.
    + right. right. exact H.
  - apply IHo in H. simpl in H. simpl. destruct H as [H | H].
    + right. left. exact H.
    + right. right. exact H.
Qed.

(* select_min só devolve None quando a lista é vazia. *)
Lemma select_min_None_nil : forall l, select_min l = None -> l = nil.
Proof.
  intro l. functional induction (select_min l); intro H.
  - reflexivity.
  - discriminate H.
  - apply IHo in H. discriminate H.
  - apply IHo in H. discriminate H.
Qed.

(* Remove a primeira ocorrência de x em l. *)
Fixpoint remove_one (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: tl => if x =? h then tl else h :: remove_one x tl
  end.

(* Todo elemento de remove_one m l já estava em l. *)
Lemma remove_one_in_orig : forall x m l, In x (remove_one m l) -> In x l.
Proof.
  intros x m l. induction l as [| h tl IH]; intro Hx.
  - simpl in Hx. contradiction.
  - simpl in Hx. destruct (m =? h) eqn:E.
    + simpl. right. exact Hx.
    + simpl in Hx. destruct Hx as [Hx | Hx].
      * subst. simpl. left. reflexivity.
      * simpl. right. apply IH. exact Hx.
Qed.

(* Se m está em l, remover m diminui o tamanho. *)
Lemma remove_one_len : forall l m, In m l -> length (remove_one m l) < length l.
Proof.
  induction l as [| h tl IH]; intros m Hin.
  - contradiction.
  - simpl. destruct (m =? h) eqn:E.
    + simpl. lia.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * subst. rewrite Nat.eqb_refl in E. discriminate.
      * simpl. apply IH in Hin. lia.
Qed.

(* Se m está em l, l é permutação de m :: remove_one m l. *)
Lemma remove_one_perm : forall l m, In m l -> Permutation l (m :: remove_one m l).
Proof.
  induction l as [| h tl IH]; intros m Hin.
  - contradiction.
  - simpl. destruct (m =? h) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply Permutation_refl.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * subst. rewrite Nat.eqb_refl in E. discriminate.
      * apply perm_trans with (l' := h :: m :: remove_one m tl).
        -- apply perm_skip. apply IH. exact Hin.
        -- apply perm_swap.
Qed.

(** A função principal [ss] recebe uma lista de naturais [l], e retorna uma permutação ordenada de [l]: *)
  
Function ss (l : list nat) {measure length l} : list nat :=
  match l with
  | nil => nil
  | _ => match select_min l with
         | None => nil
         | Some m => m :: ss (remove_one m l)
         end
  end.
Proof.
  (* obrigacao de terminacao: length (remove_one m l) < length l *)
  intros l n l0 m teq teq0.
  apply remove_one_len.
  apply select_min_in. exact teq0.
Defined.

(* Ponte: piso + cauda ordenada => lista ordenada (reaproveitada do bubble). *)
Lemma le_all_cons_sorted : forall x l, le_all x l -> Sorted le l -> Sorted le (x :: l).
Proof.
  intros x l Hall Hs. apply Sorted_cons.
  - exact Hs.
  - destruct l as [| y l'].
    + apply HdRel_nil.
    + apply HdRel_cons. apply Hall. simpl. left. reflexivity.
Qed.

(** A correção do algoritmo [ss] é obtida a partir da prova de que [ss] retorna uma permutação ordenada da lista de entrada. *)

Theorem selectionsort_correct: forall l, Sorted le (ss l) /\ Permutation l (ss l).
Proof.
  intro l. functional induction (ss l).
  - (* l = nil *)
    split. apply Sorted_nil. apply perm_nil.
  - (* select_min l = None (com l <> nil): impossivel, mas o ramo devolve nil *)
    apply select_min_None_nil in e0. subst.
    split. apply Sorted_nil. apply perm_nil.
  - (* select_min l = Some m *)
    destruct IHl0 as [Hsort Hperm].
    split.
    + (* Sorted le (m :: ss (remove_one m l)) *)
      apply le_all_cons_sorted.
      * (* m e piso de ss(remove_one m l) *)
        intros z Hz.
        assert (Hfloor : le_all m l) by (apply select_min_correct; exact e0).
        apply Hfloor.
        apply remove_one_in_orig with (m := m).
        apply Permutation_in with (l := ss (remove_one m l)).
        -- apply Permutation_sym. exact Hperm.
        -- exact Hz.
      * exact Hsort.
    + (* Permutation l (m :: ss (remove_one m l)) *)
      apply perm_trans with (l' := m :: remove_one m l).
      * apply remove_one_perm. apply select_min_in. exact e0.
      * apply perm_skip. exact Hperm.
Qed.

(** Repositório: %\url{https://github.com/flaviodemoura/selection_sort}% *)
   
 
  
