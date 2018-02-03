Set Implicit Arguments.
  (* From SoftwareFoundations *)
Require Import Maps.
Require Import List.

From Coq Require Import
     Omega
     String
     Arith.Max
     FSets.FMapAVL
     FSets.FMapFacts
     Structures.OrdersEx
     Structures.OrdersAlt
     Unicode.Utf8.     

Ltac des_ex := repeat match goal with
               | [ H : ex _  |- _ ]  => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H
                      end.

Module Nat_as_OT := (Backport_OT Nat_as_OT).
Module M := FMapAVL.Make(Nat_as_OT).
Module MFacts := FMapFacts.WProperties_fun(Nat_as_OT)(M).

Section Heaps.
  Variable a : Type.
  Definition h := M.t a.
  Definition empty := M.empty a.
  Definition heapEq (h1 h2:h) := M.Equal h1 h2.
  Definition find k (h:h) := M.find k h. 
  Definition updateHp k v (h:h) := M.add k v h.
  Definition singleton k v := M.add k v empty.
  Definition remove k (h:h) := M.remove k h.
  Definition inHeap k (h:h) := M.In k h.
  Definition mem k (h:h) := M.mem k h.
  Definition disjoint (h1:h) (h2:h) := MFacts.Disjoint h1 h2.
  Definition union (h1:h) (h2:h) := MFacts.update h1 h2.
  Definition isEmpty (h:h) := M.Empty h.
  Definition isEmptyBool (h:h) := M.is_empty h.
  Definition isEmptyListBool {A:Type} (l: list A) :=
    match l with
      nil => true
    |  _  => false
    end
  .
  Definition defUnion (h1:h) (h2:h) :=
    forall k v1 v2, M.find k h1 = Some v1 ->
                    M.find k h2 = Some v2 ->
                    v1 = v2.
  (* 例えば(1,full) (1,full)もunionできるが
     使うときはpermHpUnionと一緒に使うので問題ない
  *)
  Definition mapPrFst {A B : Type}(f: (prod A B) -> A) h := M.map f h.

  Definition toList (h:h) := MFacts.to_list h.
  Definition ofList (l:list (M.key * a)) : h := MFacts.of_list l.

  (* unionはh2の要素が優先される *)

  Lemma defUnionCom_iff : forall h1 h2,
      defUnion h1 h2 <-> defUnion h2 h1.
  Proof.
    unfold defUnion. split.
    intros.
    eapply H.
    apply H with (v1 := v2) in H0.
    subst.
    apply H1.
    apply H1.
    apply H with (v2 := v1) in H1.
    subst.
    apply H0.
    apply H0.
    
    intros.
    eapply H.
    apply H with (v1 := v2) in H0.
    subst.
    apply H1.
    apply H1.
    apply H with (v2 := v1) in H1.
    subst.
    apply H0.
    apply H0.
  Qed.
  
  Lemma eqHpRefl : forall h,
      heapEq h h.
  Proof.
    unfold heapEq.
    intros.
    apply MFacts.F.Equal_refl.
  Qed.
  
  Lemma hpEqTrans : forall h1 h2 h3,
      heapEq h1 h2 -> heapEq h2 h3 -> heapEq h1 h3.
  Proof.
    apply MFacts.F.Equal_trans.
  Qed.

  Lemma hpEqSym : forall h1 h2,
      heapEq h1 h2 -> heapEq h2 h1.
  Proof.
    apply MFacts.F.Equal_sym.
  Qed.
  
  Lemma findIn : forall s h v,
    find s h = Some v ->
    inHeap s h.
  Proof.
    unfold find. intros.
    unfold inHeap.
    intros.
    apply MFacts.F.in_find_iff.
    unfold not. intros.
    rewrite H0 in H. inversion H.
  Qed.

  Lemma emptyNotEqAdd : forall k v h,
      heapEq empty (updateHp k v h) -> False.
  Proof.
    unfold updateHp, heapEq.
    intros.
    rewrite <-MFacts.F.empty_mapsto_iff.
    rewrite MFacts.F.Equal_mapsto_iff in H.
    apply (H k v).
    apply M.find_2.
    apply MFacts.F.add_eq_o. auto.
  Qed.

  Lemma isEmptyEq : forall h,
      isEmpty h <-> heapEq h empty.
  Proof.
    unfold heapEq, M.Equal.
    unfold isEmpty, M.Empty. unfold M.Raw.Proofs.Empty. split.
    intros. unfold not in H.
    rewrite MFacts.F.empty_o.
    apply MFacts.F.not_find_in_iff.
    unfold not. intros.
    unfold M.In in H0.
    rewrite M.Raw.Proofs.In_alt in H0.
    apply M.Raw.Proofs.In_MapsTo in H0.
    destruct H0.
    eapply H.
    apply H0.
    intros.
    unfold empty in H.
    unfold not. intros.
    assert (M.find (elt:=a) a0 h0 = M.find (elt:=a) a0 (M.empty a)).
    auto.
    rewrite MFacts.F.empty_o in H1.
    rewrite <-MFacts.F.not_find_in_iff in H1.
    unfold not in H1. apply H1.
    apply M.Raw.Proofs.MapsTo_In in H0.
    unfold M.In.
    rewrite M.Raw.Proofs.In_alt.
    apply H0.
  Qed.

  Lemma isEmptyFind : forall k h,
      isEmpty h -> find k h = None.
  Proof.
    unfold isEmpty, M.Empty, M.Raw.Proofs.Empty.
    unfold not. 
    unfold find.
    intros.
    apply MFacts.F.not_find_in_iff.
    unfold not. intros.
    unfold M.In in H0.
    rewrite M.Raw.Proofs.In_alt in H0.
    apply M.Raw.Proofs.In_MapsTo in H0.
    destruct H0.
    eapply H.
    apply H0.
  Qed.
           
  Lemma empDefUnion1 : forall h2,
      defUnion empty h2.
  Proof.
    unfold defUnion.
    intros h k v1 v2 H1 H2. inversion H1.
  Qed.
  
  Lemma empDefUnion2 : forall h1,
      defUnion h1 empty.
  Proof.
    unfold defUnion.
    intros h k v1 v2 H1 H2. inversion H2.
  Qed.
  
  Lemma findUpdate : forall k v h,
    find k (updateHp k v h) = Some v.
  Proof.
    intros.
    apply M.find_1. now apply M.add_1.
  Qed.
  
  Lemma disjEmp1 : forall h,
      disjoint empty h.
  Proof.
    intros.
    unfold disjoint, MFacts.Disjoint,not.
    intros.
    destruct H.
    inversion H.
    inversion H1.
  Qed.
  
  Lemma disjEmp2 : forall h,
      disjoint h empty.
  Proof.
    intros.
    unfold disjoint, MFacts.Disjoint,not.
    intros.
    destruct H.
    inversion H0.
    inversion H1.
  Qed.
  
  Lemma disjSingle : forall k k' x x',
      disjoint (singleton k x) (singleton k' x') <->
      k <> k'.
  Proof.
    unfold disjoint,MFacts.Disjoint,singleton,not. split.
    - intros.
      apply H with (k0:=k).
      split;subst;apply MFacts.F.add_in_iff;left;auto.
    - intros.
      destruct H0.
      apply MFacts.F.add_in_iff in H0.
      apply MFacts.F.add_in_iff in H1.
      destruct H0.
      + destruct H1.
        apply H. subst. auto.
        apply MFacts.F.empty_in_iff in H1.
        auto.
      + apply MFacts.F.empty_in_iff in H0.
        auto.
  Qed.
  
  Lemma empUnion1 : forall h,
      heapEq (union empty h)  h.
  Proof.
    intros.
    unfold heapEq.
    unfold union.
    apply MFacts.fold_identity.
  Qed.

  Lemma empUnion2 : forall h,
      heapEq (union h empty) h.
  Proof.
    intros. unfold union. 
    apply MFacts.F.Equal_mapsto_iff.
    split;intros.
    apply MFacts.update_mapsto_iff in H.
    destruct H. inversion H.
    destruct H;auto.
    apply MFacts.update_mapsto_iff.
    right.
    split;auto.
    unfold not.
    apply MFacts.F.empty_in_iff.
  Qed.
  
End Heaps.

(* store : Variable (Id) -> Value (nat)*)
Definition store := total_map nat.
Definition emptyStore : store := t_empty 42.
Eval compute in (t_update emptyStore (Id "x") 3) (Id "x").

(* heap : Location (nat) -> Value (nat) *)
Definition heap := h nat.
Definition emptyHeap: heap := empty nat.
Eval compute in (find 2 (updateHp 2 3 emptyHeap)).

Definition st := prod store heap.
Definition token := nat.
Definition state := prod st token.
Definition init_st : st := (emptyStore, emptyHeap).

Definition allocN (k:nat) (len:nat) (h:heap) : heap :=
  (fix alcN (n:nat) (h':heap): heap :=
    match n with
    | 0 => h'
    | S n' => alcN n' (updateHp ((len-n)+k) 0 h')
    end) len h.

Definition isDisjointN (h:heap) (k:nat) (len:nat) :=
  (fix disjN (m:nat) (len':nat) :=
     match len' with
     | 0 => True
     | S n' => (disjoint h (singleton m 0)) /\ disjN (m+1) n'
     end) k len.

Definition relation (X: Type) := X->X->Prop.

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros.
  apply multi_step with y.
  apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z H1 H2.
  induction H1;auto.
  apply multi_step with y;auto.
Qed.

(* Arith Exp*)
Inductive aexp : Type :=
| AVar   (x:id)
| ANum   (n:nat)
| APlus  (a1:aexp) (a2:aexp)
| AMinus (a1:aexp) (a2:aexp)
| AMult  (a1:aexp) (a2:aexp).
  
Fixpoint aeval (s : store) (a : aexp) : nat :=
  match a with
  | AVar x => s x
  | ANum n => n
  | APlus a1 a2 => (aeval s a1) + (aeval s a2)
  | AMinus a1 a2  => (aeval s a1) - (aeval s a2)
  | AMult a1 a2 => (aeval s a1) * (aeval s a2)
  end.

(* y:=3, eval(y+4)  *)
Eval compute in (aeval (t_update emptyStore (Id "y") 3)
                       (APlus (AVar (Id "y")) (ANum 4))
                ).

(* Bool Exp *)
Inductive bexp : Type :=
| BTrue  
| BFalse 
| BEq    (a1:aexp) (a2:aexp)
| BLt    (a1:aexp) (a2:aexp)
| BOr    (b1:bexp) (b2:bexp)
| BAnd   (b1:bexp) (b2:bexp)
| BNot   (b:bexp).

Fixpoint beval (s : store) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq  a1 a2  => Nat.eqb (aeval s a1) (aeval s a2)
  | BLt  a1 a2  => Nat.ltb (aeval s a1) (aeval s a2)
  | BOr  b1 b2  => orb  (beval s b1) (beval s b2)
  | BAnd b1 b2  => andb (beval s b1) (beval s b2)
  | BNot b1     => negb (beval s b1)
  end.


(* command *)
Inductive com : Type :=
| CSkip   
| CAss    (x:id)   (a:aexp)
| CLook   (x:id)   (a:aexp)
| CMut    (l:aexp) (a:aexp)
| CSeq    (c1:com) (c2:com)
| CIf     (b:bexp) (c1:com) (c2:com)
| CWhile  (b:bexp) (c1:com)
| CMal    (x:id)   (a:aexp) (* a個マロック *)
| CFree   (a:aexp)
| CAtomic (c:com)
| CPar    (c1:com) (c2:com).

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf b c2 c3) (at level 80, right associativity).
Notation " x '::='  [ v ]  " :=
  (CLook x v) (at level 60).
Notation "[ x ] '::=' v  " :=
  (CMut x v) (at level 60).
Notation "'FREE' a" :=
  (CFree a) (at level 60).
Notation "c1 |||| c2" :=
  (CPar c1 c2) (at level 60).
Notation "'ATOMIC' c" :=
  (CAtomic c) (at level 60).
Notation "x '::=' 'ALLOC' n" :=
  (CMal x n) (at level 60).

Fixpoint size (c:com) :=
  match c with
  | CSkip         => 0
  | CSeq c1 c2    => (size c1) + (size c2) + 1
  | CIf  b c1 c2  => (max (size c1) (size c2)) + 1
  | CWhile b c    => (size c) + 1
  | CAtomic c     => (size c) + 1
  | CPar c1 c2    => (size c1) + (size c2) + 1
  | _             => 1
  end.

(* 
論文では
(com, state) -> (com, state) 
*)
Inductive configurations : Type :=
| nonterminal : com -> state -> configurations
| terminal    : state -> configurations
| abort       : configurations.


Inductive cevalSm : configurations -> configurations -> Prop :=
| E_Skip : forall s h t,
    cevalSm (nonterminal SKIP (s,h,t))
            (terminal (s,h,t))             
| E_Ass  : forall s h t E n x,
    aeval s E = n ->
    cevalSm (nonterminal (x ::= E) (s,h,t))
            (nonterminal SKIP ((t_update s x n),h,t))
(* c1;;c2 *)
| E_Seq1 : forall c1 c1' c2 s h t s' h' t',
    cevalSm (nonterminal c1 (s,h,t))
            (nonterminal c1' (s',h',t')) ->
    cevalSm (nonterminal (c1';;c2) (s,h,t))
            (nonterminal (c1';;c2) (s',h',t'))
| E_Seq2 : forall c s h t,
    cevalSm (nonterminal (SKIP;;c) (s,h,t))
             (nonterminal c (s,h,t))
| E_SeqAbort : forall c1 c2 s h t,
    cevalSm (nonterminal c1 (s,h,t)) abort ->
    cevalSm (nonterminal (c1;;c2) (s,h,t)) abort
(* IF *)
| E_IfTrue : forall s h t b c1 c2,
    beval s b = true ->
    cevalSm (nonterminal (IFB b THEN c1 ELSE c2 FI) (s,h,t))
            (nonterminal  c1 (s,h,t))
| E_IfFalse : forall s h t b c1 c2,
    beval s b = false ->
    cevalSm (nonterminal (IFB b THEN c1 ELSE c2 FI) (s,h,t))
            (nonterminal  c2 (s,h,t))
(* WHILE *)
| E_WhileSkip : forall b s h t c,
    beval s b = false ->
    cevalSm (nonterminal (WHILE b DO c END) (s,h,t))
            (nonterminal SKIP (s,h,t))
| E_WhileLoop : forall s h t b c,
    beval s b = true ->
    t > 0 ->
    cevalSm (nonterminal (WHILE b DO c END) (s,h,t))
            (nonterminal (c;;WHILE b DO c END) (s,h,t-1))
| E_WhileAbort : forall s h t b c,
    beval s b = true ->
    t = 0 ->
    cevalSm (nonterminal (WHILE b DO c END) (s,h,t)) abort
(* C1||C2 *)
| E_Par1 : forall c1 c1' c2 s h t s' h' t',
    cevalSm (nonterminal c1 (s,h,t))
            (nonterminal c1' (s',h',t')) ->
    cevalSm (nonterminal (c1 |||| c2) (s,h,t))
            (nonterminal (c1' |||| c2) (s',h',t'))
| E_Par2 : forall c1 c2 c2' s h t s' h' t',
    cevalSm (nonterminal c2 (s,h,t))
            (nonterminal c2' (s',h',t')) ->
    cevalSm (nonterminal (c1 |||| c2) (s,h,t))
            (nonterminal (c1 |||| c2') (s',h',t'))
| E_ParSkip : forall s h t,
    cevalSm (nonterminal (SKIP |||| SKIP) (s,h,t))
            (nonterminal SKIP (s,h,t))
| E_ParAbort1 : forall c1 c2 s h t,
    cevalSm (nonterminal c1 (s,h,t)) abort ->
    cevalSm (nonterminal (c1 |||| c2) (s,h,t)) abort
| E_ParAbort2 : forall c1 c2 s h t,
    cevalSm (nonterminal c2 (s,h,t)) abort ->
    cevalSm (nonterminal (c1 |||| c2) (s,h,t)) abort
(* atomic(C) *)
| E_Atom : forall c s h t s' h' t',
    multi cevalSm (nonterminal c (s,h,t))
                  (nonterminal SKIP (s',h',t')) ->
    cevalSm (nonterminal (ATOMIC c) (s,h,t))
            (nonterminal SKIP (s',h',t'))
| E_AtomAbort : forall c s h t,
    multi cevalSm (nonterminal c (s,h,t))
                   abort ->
    cevalSm (nonterminal (ATOMIC c) (s,h,t))
             abort
(* x := [l] *)
| E_LookUp : forall s h X v l n t,
    aeval s l = n ->
    find n h = Some v ->  
    cevalSm (nonterminal (X ::= [l]) (s,h,t))
            (nonterminal SKIP ((t_update s X v),h,t))
| E_LookUpAbort : forall s h t X e n,
    aeval s e = n ->
    find n h = None ->
    cevalSm (nonterminal (X ::= [e]) (s,h,t)) abort
(* [l] ::= E*)
| E_Mutate :forall s h t v l E n,
    aeval s l = n ->
    find n h = Some v ->
    cevalSm (nonterminal ([l] ::= E) (s,h,t))
            (nonterminal SKIP (s, (updateHp n (aeval s E) h), t))
| E_MutateAbort :forall s h t l E n,
    aeval s l = n ->
    find n h = None ->
    cevalSm (nonterminal ([l] ::= E) (s,h,t)) abort
(* Free l *)
| E_Free : forall s h t l v n,
    aeval s l = n ->
    find n h = Some v ->
    cevalSm (nonterminal (FREE l) (s,h,t))
            (nonterminal SKIP (s, remove n h,t))
| E_FreeAbort : forall s h t l n,
    aeval s l = n ->
    find n h = None ->
    cevalSm (nonterminal (FREE l) (s,h,t)) abort
(* malloc *)
| E_Malloc : forall s h t X n l,
        isDisjointN h l (aeval s n) ->
        cevalSm (nonterminal (X ::= ALLOC n) (s,h,t))
                (nonterminal SKIP ((t_update s X l), allocN l (aeval s n) h, t)).
Definition exmX := Id "1".
Definition exmSt := t_update emptyStore exmX 20.
Definition exmHp := singleton 2 5.
Definition exmTkn := 0.

Example Malloc :
  cevalSm (nonterminal
              (exmX ::= ALLOC (ANum 3))
              (exmSt, exmHp,exmTkn)
           )
           (nonterminal
              SKIP
              (t_update exmSt exmX 40,
               allocN 40 (aeval exmSt (ANum 3)) exmHp,
               exmTkn)
              
           ).
Proof.
  apply E_Malloc.
  unfold isDisjointN. simpl.
  do 3 (try split;try apply disjSingle;try omega);auto.
Qed.

  
Lemma mul_ref : forall s h s' h',
    multi cevalSm (terminal (s,h)) (terminal (s',h')) <->
    s = s' /\ h = h'.
Proof.
  split. intros.
  inversion H. split. auto. auto.
  subst.  inversion H0. intros.
  destruct H. subst.
  apply multi_refl.
Qed.

(* permission heap *)
(* 
 (v, full) <-> (v, read) ++ (v, read)
 (v, read) ++  (v, full) -> (v,undefined)
 (a, read) ++  (b, read) -> (a,undefined)
*)
Inductive perm :=
|read :perm
|full :perm
|undefined : perm.

Definition permHeap := h (prod nat perm).
Definition permEmptyHeap: permHeap := empty (prod nat perm).
Definition permSt := prod store permHeap.
Definition permState := prod permSt nat.

Definition permUnion (r1:perm) (r2:perm) :perm :=
  match r1,r2 with
  | read,read => full
  | _ , _ => undefined
  end.


Definition permHpUnion (h1 h2:permHeap) :=
  if isEmptyListBool (toList h2) then h1
  else if isEmptyListBool (toList h1) then h2
       else
    (fix pmUnion l :=
       match l with
       | nil         => h2 
       | (key,(v1,pm1))::tl =>
         match find key h2 with
         | Some (v2,pm2) =>
           if v1 =? v2 then
             let newp := permUnion pm1 pm2 in
             updateHp key (v1,newp) (pmUnion tl)
           else
             updateHp key (v1,undefined) (pmUnion tl)
         | None => updateHp key (v1,pm1) (pmUnion tl)
         end
       end
    ) (toList h1).
    
Definition takeSt {A B C:Type} (σ:prod (prod A B) C) :=
  fst (fst σ).
Definition takeHp {A B C:Type} (σ:prod (prod A B) C) :=
  snd (fst σ).
Definition takeTkn {A B C:Type} (σ:prod (prod A B) C) :=
  snd σ.

(* Assertion : permState -> Prop *)

Inductive assn : Type :=
| AsEmp 
| AsTkn
| AsBool    (b:bexp)
| AsOr      (P:assn) (Q:assn)
| AsAnd     (P:assn) (Q:assn)
| AsEx      (Pa:nat->assn)
| AsAll     (Pa:nat->assn)
| AsMpFl    (l:aexp) (v:aexp)
| AsMpRd    (l:aexp) (v:aexp)
| AsStar    (P:assn) (Q:assn)
| AsWand    (P:assn) (Q:assn)
| AsLseg    (x:aexp) (y:aexp)
.

Notation "P ** Q" :=
  (AsStar P Q) (at level 80).
Notation "P -* Q" :=
  (AsWand P Q) (at level 80).
Notation "◇" := AsTkn.
Notation " h1 === h2 " :=
  (heapEq h1 h2) (at level 60).

Inductive assnJdg (σ:permState) : assn  -> Prop :=
  jdg_emp   :
    isEmpty (takeHp σ) ->
    assnJdg σ AsEmp
| jdg_tkn   :
    takeTkn σ > 0 /\
    isEmpty (takeHp σ) ->
    assnJdg σ AsTkn
| jdg_bool  : forall b,
    beval (takeSt σ) b = true ->
    assnJdg σ (AsBool b) 
| jdg_or_l  : forall P Q,
    assnJdg σ P ->
    assnJdg σ (AsOr P Q)
| jdg_or_r  : forall P Q,
    assnJdg σ Q ->
    assnJdg σ (AsOr P Q)
| jdg_and   : forall P Q,
    assnJdg σ P ->
    assnJdg σ Q ->
    assnJdg σ (AsAnd P Q)
| jdg_ex    : forall Pa,
    (exists v, assnJdg σ (Pa v)) ->
    assnJdg σ (AsEx Pa)
| jdg_all   : forall Pa,
    (forall v, assnJdg σ (Pa v)) ->
    assnJdg σ (AsAll Pa)
| jdg_mpFl  : forall l v,
    takeHp σ === singleton (aeval (takeSt σ) l) ((aeval (takeSt σ) v),full) ->
    assnJdg σ (AsMpFl l v)
| jdg_mpRd  : forall l v,
    takeHp σ === singleton (aeval (takeSt σ) l) ((aeval (takeSt σ) v),read) ->
    assnJdg σ (AsMpRd l v)
| jdg_star  : forall P Q,
    (exists hp hq tp tq,
      takeTkn σ = tp+tq /\
      defUnion hp hq /\
      takeHp σ === permHpUnion hp hq /\
      (assnJdg (takeSt σ,hp,tp) P) /\ (assnJdg (takeSt σ,hq,tq) Q)) ->
    assnJdg σ (P ** Q)
| jdg_wand  : forall h' t' P Q,
    (defUnion (takeHp σ) h' /\
    (assnJdg (takeSt σ, takeHp σ, t') P) /\
    (assnJdg (takeSt σ, permHpUnion (takeHp σ ) h',(takeTkn σ)+t') Q)) ->
    assnJdg σ (P -* Q)
| jdg_lnil  : forall x y,
    assnJdg σ (AsBool(BEq x y)) ->
    assnJdg σ (AsLseg x y)
| jdg_lcons : forall x y,
    assnJdg σ
     (AsEx(fun v =>
           AsEx(fun z =>
                  (
                    (AsMpFl x (ANum v))**
                    (AsMpFl (APlus x (ANum 1)) (ANum z))) **
                    AsLseg (ANum z) y
               )
     )) ->
    assnJdg σ (AsLseg x y)
.

(* assertion for stack proof *)
Fixpoint AstarN n p :=
  match n with
  | 0    => AsEmp
  | S n' => p ** (AstarN n' p)
  end.

Definition AstarAlpha (from:nat) (len:nat) (p:nat->nat->assn) u :=
  (fix AAlp (n:nat) :=
    match n with
    | 0 => AsEmp
    | S n' => let ind := (len+from) - n in
              (p ind u) ** (AAlp n')
    end) len.

Definition AstarBeta (from:nat) (len:nat) (p:nat->nat->nat->assn) u v :=
  (fix ABet (n:nat) :=
    match n with
    | 0 => AsEmp
    | S n' => let ind := (len+from) - n in
              (p ind u v) ** (ABet n')
    end) len.

Definition AstarExcludeJAlpha (from:nat) (j:nat) (len:nat) (α:nat->nat->assn) u :=
  (fix AEJ (n:nat) :=
    match n with
    | 0 => AsEmp
    | S n' => let ind := (len+from) - n in
              if j =? ind then AEJ n'
              else (α ind u) ** (AEJ n')
    end) len.

Definition AstarExcludeJGamma (from:nat) (j:nat) (len:nat) γ :=
  (fix AEJ (n:nat) :=
    match n with
    | 0 => AsEmp
    | S n' => let ind := (len+from) - n in
              if j =? ind then AEJ n'
              else (γ ind) ** (AEJ n')
    end) len.

Definition exmP := fun v u => AsMpRd (ANum v) (ANum u).

Eval compute in (AstarExcludeJAlpha 0 2 4 exmP 1).
Eval compute in (AstarAlpha 0 4 exmP 1).

(* definition by Vafeiadis *)

(* Fixpoint assnJdg (σ :permState) p := *)
(*   let s := takeSt σ in *)
(*   let h := takeHp σ in *)
(*   let t := takeTkn σ in *)
(*   match p with *)
(*   | AsEmp       => isEmpty h *)
(*   | AsTkn       => t > 0 /\ isEmpty h *)
(*   | AsBool b    => beval s b = true *)
(*   | AsOr   P Q  => (assnJdg σ P) \/ (assnJdg σ Q) *)
(*   | AsAnd  P Q  => (assnJdg σ P) /\ (assnJdg σ Q) *)
(*   | AsNot  P    => ~(assnJdg σ P) *)
(*   | AsEx   Pa    => exists x, (assnJdg σ (Pa x)) *)
(*   | AsAll  Pa    => forall x, (assnJdg σ (Pa x)) *)
(*   | AsMpFl l v  => h === *)
(*                    singleton (aeval s l) (aeval s v,full) *)
(*   | AsMpRd l v  => h === *)
(*                    singleton (aeval s l) (aeval s v,read) *)
(*   | AsStar P Q  => exists hp hq tp tq, *)
(*                    t = tp + tq /\ *)
(*                    defUnion hp hq /\ *)
(*                    h === permHpUnion hp hq /\ *)
(*                    (assnJdg (s,hp,tp) P) /\ (assnJdg (s,hq,tq) Q) *)
(*   | AsWand P Q  => forall h' t', *)
(*       defUnion h h' /\ *)
(*       (assnJdg (s,h,t') P) /\ *)
(*       (assnJdg (s, permHpUnion h h',t+t') Q) *)
(*   | AsLseg σ x y => assnJdg σ (AsOr (AsBool (BEq x y )) *)
(*                     (AsEx(fun z => AsLseg σ y (ANum z)))) *)
(*   end. *)


Check (AsEx (fun x => AsMpFl (ANum 3) (ANum x) ** (AsOr (AsBool (BEq (ANum x) (ANum 0))) AsTkn))).

Notation " σ '|=' Q " :=
  (assnJdg σ Q) (at level 60).

Definition asnImp P Q :=
  (forall σ, σ |= P -> σ |= Q).

Notation "P ->> Q" :=
  (asnImp P Q) (at level 80).
Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80).

Lemma permEmpHpUnion_eq1 : forall h1,
    permHpUnion h1 permEmptyHeap === h1.
Proof.
  intros.
  unfold permHpUnion.
  simpl.
  apply eqHpRefl.
Qed.

Lemma permEmpHpUnion_eq2 : forall h2,
    permHpUnion permEmptyHeap h2 === h2.
Proof.
  intros. unfold permHpUnion.
  unfold heapEq, M.Equal.
  intros.
  simpl.
  assert (isEmpty permEmptyHeap).
  rewrite isEmptyEq. apply eqHpRefl.
  remember (toList h2) as b. destruct b.
  simpl.
  unfold toList in Heqb. unfold MFacts.to_list in Heqb.
  unfold isEmpty in H.
  symmetry in Heqb.
  apply MFacts.elements_Empty in Heqb.
  apply (isEmptyFind y) in H.
  apply (isEmptyFind y) in Heqb.
  auto. simpl.
  auto.
Qed.

  
Definition tsHp1 := updateHp 4 (2,read)
                   (updateHp 2 (2,read)
                   (updateHp 2 (3,read) permEmptyHeap)).

Definition tsHp2 := updateHp 5 (1,full)
                   (updateHp 4 (2,read)
                   (updateHp 2 (3,read) permEmptyHeap)).

Eval compute in (find 3 (permHpUnion tsHp1 tsHp2)).
Eval compute in (M.elements tsHp1).
Eval compute in (M.elements tsHp2).

Notation "h1 '|+|' h2" :=
  (permHpUnion h1 h2) (at level 60).
Notation "h1 '|+|' h2 '|+|' .. '|+|' hn" :=
  (permHpUnion .. (permHpUnion h1 h2) .. hn) (at level 60).

Check ((fun σ =>  exists x, σ |=  AsMpRd x (ANum 3))).

Eval compute in (find 2 (updateHp 2 (3,read) (updateHp 2 (3,full) permEmptyHeap))).


Inductive safe : nat -> com -> permState -> assn -> assn -> Prop:=
| safe_0 : forall c σ I Q, safe 0 c σ I Q
| safe_n1 : forall n c c' (s s':store) (h h' hi hf:permHeap) (t ti t':token) (I Q:assn),
    let H := mapPrFst fst (h |+| hi |+| hf) in
    let σ := (s,h,t) in
    let p1 := (c = SKIP -> (σ |= Q)) in
    let p2 :=
        ((s,hi,ti) |= I  /\
         (defUnion h hi /\ defUnion hi hf /\ defUnion h hf) /\
         (~ cevalSm (nonterminal c (s, H ,t+ti)) abort))
    in
    let p3:=
    ((s,hi,ti) |= I  /\
     (defUnion h hi /\ defUnion hi hf /\ defUnion h hf) /\
      (cevalSm (nonterminal c (s, H, t+ti))
               (nonterminal c' (s', (mapPrFst fst h'), t')) ->
       exists h'' hi' t'',
         h' ===  (h'' |+| hi' |+| hf) /\
         t'' <= t' /\
         (s',hi',t'') |= I /\
         safe n c' (s', h'',t'-t'') I Q))
    in
    p1 /\ p2 /\ p3
    -> safe (S n) c σ I Q.

(* free variable *)

Fixpoint fvAexpList (a:aexp) : list id :=
  match a with
  | ANum   _     => nil
  | AVar   X     => cons X nil
  | APlus  a1 a2 => (fvAexpList a1) ++ (fvAexpList a2) 
  | AMinus a1 a2 => (fvAexpList a1) ++ (fvAexpList a2)
  | AMult  a1 a2 => (fvAexpList a1) ++ (fvAexpList a2)
  end.

Fixpoint fvBexpList (b:bexp) : list id :=
  match b with
  | BTrue      => nil
  | BFalse     => nil
  | BEq  a1 a2 => (fvAexpList a1) ++ (fvAexpList a2)
  | BLt  a1 a2 => (fvAexpList a1) ++ (fvAexpList a2)
  | BOr  b1 b2 => (fvBexpList b1) ++ (fvBexpList b2)
  | BAnd b1 b2 => (fvBexpList b1) ++ (fvBexpList b2)
  | BNot b     => fvBexpList b
  end.

Fixpoint fvAsn (AS:assn) (v:id) :=
  match AS with
  | AsEmp       => False
  | AsTkn       => False
  | AsBool b    => List.In v (fvBexpList b)
  | AsOr   P Q  => fvAsn P v \/ fvAsn Q v
  | AsAnd  P Q  => fvAsn P v \/ fvAsn Q v
  | AsEx   Pa   => exists n, fvAsn (Pa n) v
  | AsAll  Pa   => exists n, fvAsn (Pa n) v
  | AsMpRd l a  => List.In v (fvAexpList l ++ fvAexpList a)
  | AsMpFl l a  => List.In v (fvAexpList l ++ fvAexpList a)
  | AsStar P Q  => fvAsn P v \/ fvAsn Q v
  | AsWand P Q  => fvAsn P v \/ fvAsn Q v
  | AsLseg x y  => List.In v (fvAexpList x ++ fvAexpList y)
  end.

Fixpoint fvComList (C:com) : list id :=
  match C with
  | CSkip           => nil
  | CAss    X  _    => X :: nil
  | CLook   X  _    => X :: nil
  | CMut   a1 a2    => fvAexpList a1 ++ fvAexpList a2
  | CSeq   c1 c2    => fvComList c1 ++ fvComList c2
  | CIf     b c1 c2 => fvBexpList b ++ fvComList c1 ++ fvComList c2
  | CWhile  b c1    => fvBexpList b ++ fvComList c1
  | CMal    X  _    => X :: nil
  | CFree   l       => fvAexpList l
  | CAtomic c       => fvComList c
  | CPar   c1 c2    => fvComList c1 ++ fvComList c2
  end.

Fixpoint wrComList c : list id:=
  match c with
  | CSkip           => nil
  | CAss    X  _    => X :: nil
  | CLook   X  _    => X :: nil
  | CMut    _  _    => nil      (* アドレスの中身しか変更しないから *)
  | CSeq   c1 c2    => wrComList c1 ++ wrComList c2
  | CIf     _ c1 c2 => wrComList c1 ++ wrComList c2
  | CWhile  _ c1    => wrComList c1
  | CMal    X  _    => X :: nil
  | CFree   l       => nil
  | CAtomic c       => wrComList c
  | CPar   c1 c2    => wrComList c1 ++ wrComList c2
  end.

(* Axiom of separation logic 1 *)

Axiom sepStarCom_iff : forall P Q σ,
    σ |= (P ** Q) <-> σ |= (Q ** P).
Axiom sepStarAssoc_iff : forall P Q R σ,
    σ |= ((P ** Q) ** R)  <-> σ |= (P ** (Q ** R)).
Axiom sepStarEmp_iff : forall P σ,
    σ |= (P ** AsEmp)  <-> σ |= P.
Axiom sepStarOr_iff : forall P Q R σ,
    σ |= ((AsOr P Q) ** R)  <-> σ |= (AsOr (P ** R) (Q ** R)).
Axiom sepStarAnd_iff : forall P Q R σ,
    σ |= ((AsAnd P Q) ** R)  <-> σ |= (AsAnd (P ** R) (Q ** R)).
                 
Lemma sepStarImp : forall p1 p2 q1 q2,
    p1 ->> p2 ->
    q1 ->> q2 ->
    (p1 ** q1) ->> (p2 ** q2).
Proof.
  unfold asnImp.
  intros.
  constructor.
  inversion H1.
  des_ex.
  exists x,x0,x1,x2.
  repeat (try split;auto).
Qed.

Lemma sepStarImpSt : forall p1 p2 q1 q2 σ',
    (forall σ, σ |= p1 -> σ |= p2) ->
    (forall σ, σ |= q1 -> σ |= q2) ->
    σ' |= (p1 ** q1) -> σ' |= (p2 ** q2).
Proof.
  intros.
  inversion H1.
  des_ex. constructor.
  exists x,x0,x1,x2.
  repeat (try split;auto).
Qed.

Axiom sepStarWand : forall p1 p2 p3,
    p1 ** p2 ->> p3 ->
    p1 ->> (p2 -* p3).
Axiom sepStarWandSt : forall P Q R σ,
    (forall σ', σ' |= (P**Q) -> σ' |= R) ->
    σ |= P -> σ|= (Q -* R).

Lemma sepStarExAssocSt : forall Pa Q σ,
    σ |= ((AsEx (fun u => Pa u)) ** Q) <-> σ |= ((AsEx (fun u => ((Pa u) ** Q)))).
Proof.
  split;intros.
  inversion H. des_ex.
  inversion H5. subst.
  des_ex.
  constructor.
  exists x3. constructor.
  exists x,x0,x1,x2.
  repeat (split;auto).
  inversion H. des_ex. inversion H1.
  des_ex.
  constructor. exists x0,x1,x2,x3.
  repeat split;auto.
  constructor. exists x. 
  auto.
Qed.

Lemma sepStarExAssoc : forall Pa Q,
    (AsEx (fun u => Pa u)) ** Q <<->> (AsEx (fun u => ((Pa u) ** Q))).
  split;
  intros σ H;inversion H;
    des_ex. inversion H5. constructor.
  des_ex. exists x3.
  constructor.
  exists x,x0,x1,x2.
  repeat (split;auto).
  constructor.
  inversion H1.
  des_ex.
  exists x0,x1,x2,x3.
  repeat (split;auto).
  constructor.
  exists x. auto.
Qed.

Axiom sepWandStar : forall p1 p2 p3,
    p1 ->> (p2 -* p3) ->
    p1 ** p2 ->> p3.

(* Axiom of thesis *)
Axiom rdFl_iff : forall l v σ,
    σ |= AsMpFl l v <-> σ |= (AsMpRd l v ** AsMpRd l v).

Fixpoint isPure p :=
  match p with
    AsEmp      => False
  | AsTkn      => False
  | AsBool   b => True         
  | AsOr   P Q => isPure P /\ isPure Q
  | AsAnd  P Q => isPure P /\ isPure Q
  | AsEx    Pa => exists x, isPure (Pa x) 
  | AsAll   Pa => forall x, isPure (Pa x)
  | AsMpFl l v => False
  | AsMpRd l v => False
  | AsStar P Q => isPure P /\ isPure Q
  | AsWand P Q => isPure P /\ isPure Q
  | AsLseg x y => False
  end.

(* Axiom of separation logic 2 *)

Axiom sepStarPureAnd : forall P Q R σ,
    isPure P ->
    σ |= ((AsAnd P Q) ** R) <-> σ |= (AsAnd P (Q ** R)). 
Axiom sepAndStarIsPure : forall P Q,
    isPure P \/ isPure Q ->
    (AsAnd P Q) ->> (P ** Q).
Axiom sepAndStarIsPureSt : forall P Q σ,
    isPure P \/ isPure Q ->
    σ|= (AsAnd P Q) -> σ |= (P ** Q).
Axiom sepStarAndIsPure : forall P Q,
    isPure P ->
    isPure Q ->
    (P ** Q) ->> (AsAnd P Q).
  
Lemma isEmptyPermHpUnion1 : forall h h1 h2,
    isEmpty h1 ->
    h === (h1 |+| h2) ->
    h === h2.
Proof.
  intros.
  apply MFacts.elements_Empty in H.
  unfold permHpUnion in H0.
  unfold toList in H0. unfold MFacts.to_list in H0.
  rewrite H in H0.
  simpl in H0.
  remember (M.elements (elt:=nat * perm) h2) as b.
  destruct b.  simpl in *.
  symmetry in Heqb.
  apply MFacts.F.Empty_m in H0.
  destruct H0.
  apply MFacts.elements_Empty in H.
  apply H1 in H.
  apply MFacts.elements_Empty in Heqb.
  unfold heapEq , M.Equal.
  intros.
  apply (isEmptyFind y)in Heqb.
  apply (isEmptyFind y)in H.
  unfold find in *.
  rewrite H. rewrite Heqb. auto.
  simpl in H0.
  apply H0.
Qed.
  
Definition isPrecise P :=
  forall h1 h2 h1' h2' s t,
    defUnion h1 h2 /\
    defUnion h1' h2' /\
    heapEq (h1 |+| h2) (h1' |+| h2') /\
    (s,h1,t) |= P /\ (s,h1',t) |= P
    -> heapEq h1 h1'.

Definition acN (k:nat) (len:nat) (h:heap) : heap :=
  (fix alcN (n:nat) (h':heap): heap :=
    match n with
    | 0 => h'
    | S n' => alcN n' (updateHp ((len-n)+k) 0 h')
    end) len h.

Definition asMllocN x len : assn :=
  (fix asMlcN n :=
    match n with
    | 0 => AsEmp
    | S n' =>
      AsStar
        (AsMpFl (APlus (ANum (len - n)) (AVar x)) (ANum 0))
        (asMlcN n')
    end) len.

(* I |- [P]C[Q] *)
Inductive CSepTriple : assn -> assn -> com -> assn -> Prop :=
  csep_skip : forall I P,
    CSepTriple I P SKIP P
| csep_assign : forall I P X v,
    ~ (fvAsn I X) ->
    CSepTriple I (P v) (X ::= v) (P (AVar X))
| csep_lookup : forall I X l v,
    ~ In X (fvAexpList l) ->
    ~ In X (fvAexpList v) ->
    ~ (fvAsn I X) ->
    let P := AsMpRd l v in
    CSepTriple I P (X ::= [l]) (AsAnd P (AsBool (BEq (AVar X) v)))
| csep_mutate : forall I l v,
    let P := AsEx (fun v => AsMpFl l (ANum v)) in
     CSepTriple I P ([l] ::= v) (AsMpFl l v)
| csep_alloc : forall I N X,
    ~ (fvAsn I X) ->
    CSepTriple I (AsEmp) (X ::= ALLOC (ANum N))
               (asMllocN X N)
| csep_free : forall I l,
    let P := AsEx (fun v => AsMpFl l (ANum v)) in
    CSepTriple I P (FREE l) AsEmp
| csep_seq : forall I P Q R c1 c2,
    CSepTriple I Q c2 R ->
    CSepTriple I P c1 Q ->
    CSepTriple I P (c1;;c2) R
| csep_par : forall I P1 P2 Q1 Q2 c1 c2,
    let fvl1 := fun x => (fvAsn I x) \/ (fvAsn P1 x) \/ (fvAsn Q1 x) in
    let fvl2 := fun x => (fvAsn I x) \/ (fvAsn P2 x) \/ (fvAsn Q2 x) in
    let cl1  := wrComList c1 in
    let cl2  := wrComList c2 in
    ((forall X, ~(fvl1 X /\ In X cl1)) /\
     (forall X, ~(fvl2 X /\ In X cl2)) /\
     CSepTriple I P1 c1 Q1 /\
     CSepTriple I P2 c2 Q2) ->
    CSepTriple I (P1 ** P2) (c1||||c2) (Q1 ** Q2)
| csep_if : forall I P Q b c1 c2,
    CSepTriple I (AsAnd P (AsBool b)) c1 Q ->
    CSepTriple I (AsAnd P (AsBool (BNot b))) c2 Q ->
    CSepTriple I P (IFB b THEN c1 ELSE c2 FI) Q
| csep_while : forall I P P' b c ,
    ((AsAnd P (AsBool b)) ->> (P' ** AsTkn)) /\
    CSepTriple I P' c P -> 
    CSepTriple I P (WHILE b DO c END) (AsAnd P (AsBool (BNot b)))
| csep_atom : forall P I Q c,
    CSepTriple AsEmp (P**I) c (Q**I) ->
    CSepTriple I P (ATOMIC c) Q
| csep_share : forall I J P Q c,
    CSepTriple (I**J) P c Q ->
    CSepTriple I (P**J) (ATOMIC c) (Q**J)
| csep_frame : forall I P Q R  c,
    CSepTriple I P c Q /\
    (forall X, (fvAsn R X) -> In X (wrComList c) -> False) ->
    CSepTriple I (P**R) c (Q**R)
| csep_conseq : forall I P P' Q Q' c,
    CSepTriple I P c Q /\
    (P'->> P ) /\
    (Q ->> Q') ->
    CSepTriple I P' c Q'
| csep_or : forall I P1 P2 Q c,
    CSepTriple I P2 c Q ->
    CSepTriple I P1 c Q ->
    CSepTriple I (AsOr P1 P2) c Q
| csep_ex : forall Pa Qa I c,
    (forall n, CSepTriple I (Pa n) c (Qa n)) ->
    CSepTriple I (AsEx Pa) c (AsEx Qa)
| csep_and : forall I P Q1 Q2 c,
    CSepTriple I P c Q1 /\
    CSepTriple I P c Q2 /\
    isPrecise I ->
    CSepTriple I P c (AsAnd Q1 Q2).

Notation "I '|-' {{ P }}  c  {{ Q }}" :=
  (CSepTriple I P c Q) (at level 90, c at next level).

Definition exmY := Id "3".


(* example *)

Example assign :
  (AsBool BTrue) |-
        {{ AsBool (BEq (AVar exmX) (ANum 5)) }}
           exmY ::= (AVar exmX)
        {{ AsBool (BEq (AVar exmY) (ANum 5)) }}.
Proof.
  eapply csep_conseq with
      (P := AsBool (BEq (AVar exmX) (ANum 5)))
  .
  split.
  apply csep_assign with
      (P := fun x => AsBool (BEq x (ANum 5)))
  .
  unfold not. simpl;auto.
  split;
  unfold asnImp;
  simpl;auto.
Qed.


(* thesis definition & lemma  *)

Definition wfOrder (p p':prod com state) :=
  let c  := fst p  in
  let c' := fst p' in
  let σ  := snd p  in
  let σ' := snd p' in
  let t := takeTkn σ  in
  let t':= takeTkn σ' in
  t' < t \/ (t' = t /\ size(c') < size(c)).

Axiom step_wfOrd : forall (σ σ': state) (c c': com),
    (cevalSm (nonterminal c σ) (nonterminal c' σ') \/
     cevalSm (nonterminal SKIP σ) (terminal σ)) ->
    wfOrder (c,σ) (c',σ').

Axiom isWF_wfOrder :
  well_founded wfOrder.


Definition bigStep (σ σ': state) (c: com) :=
  multi cevalSm (nonterminal c σ) (nonterminal SKIP σ').
Definition bigStepAbort (σ : state) (c: com) :=
  multi cevalSm (nonterminal c σ) abort.

Definition Termination (σ : state) (c: com) :=
  ~bigStepAbort σ c.

Axiom safe_mn : forall σ I Q R c1 c2 n,
    (safe n c1 σ I Q /\
    forall m σ',
      m <= n /\
      σ' |= Q /\
      safe m c2 σ' I R) ->
    safe n (c1;;c2) σ I R.

(* Theorem 4 *)
Axiom tripleSafe : forall I P C Q n σ,
    I |- {{P}} C {{Q}} ->
         (σ |= P ) ->
         safe n C σ I P.
  
Axiom safeWhile : forall n σ I P P' B C,
    (σ |= P) /\
    (σ |= (AsAnd P (AsBool B)) -> σ|= (P' ** AsTkn)) /\
    (I |- {{P'}} C {{P}}) ->
         safe n (WHILE B DO C END) σ I (AsAnd P (AsBool (BNot B))).

(* Theorem 5 *)
Axiom totalCorrectness : forall I P C Q s h t s' h' t',
    (s,h,t) |= (AsStar P I) ->
    I |- {{P}} C {{Q}} ->
    let H  := mapPrFst fst h  in
    let H' := mapPrFst fst h' in
    ((bigStep (s,H,t) (s',H',t') C) /\ (s',h',t') |= (AsStar P I)).
   
