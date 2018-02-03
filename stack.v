Require Import lang.
Require Import Maps.

Notation "x '!=' a":=
  (BNot (BEq x a)) (at level 60).
Notation "x '==' a":=
  (BEq x a) (at level 60).

(* global variable *)
Definition Stack := Id "Stack".
Definition A := Id "A".
Definition C := Id "C".
(* local variable *)
Definition x := Id "x".
Definition t := Id "t".
Definition s := Id "s".
Definition idPush := Id "ip".   (* 10 => True , _ => False *)
Definition pushed := (AVar idPush) == ANum 10.

Definition asnPushedTrue := AsBool pushed.

Definition nToken n := AstarN n ◇.

Eval compute in (AstarN 2 ◇).

Lemma nTokenEmp : forall n σ,
    σ |= (nToken n) -> σ |= AsEmp.
Proof.
  intro.
  induction n;intros.
  unfold nToken, AstarN in H. apply H.
  apply IHn.
  unfold nToken, AstarN in H.
  inversion_clear H.
  des_ex.
  rewrite <-sepStarEmp_iff.
  rewrite sepStarCom_iff.
  constructor.
  exists x0,x1,x2,x3.
  repeat split;auto.
  inversion H2.
  des_ex. constructor.
  unfold takeHp in *. simpl in *. auto.
Qed.

Definition γ tid (P:aexp->aexp->assn) a c :=
  let la := (APlus (AVar A) (ANum tid)) in
  let lc := (APlus (AVar C) (ANum tid)) in
  (P la a) ** (P lc c).

Definition γread tid a c :=
  γ tid AsMpRd a c.
Definition γfull tid a c :=
  γ tid AsMpFl a c.
Definition γreadEx tid :=
  AsEx (fun a => (AsEx (fun c =>γ tid AsMpRd (ANum a) (ANum c)))).
Definition γfullEx tid :=
  AsEx (fun a => (AsEx (fun c =>γ tid AsMpFl (ANum a) (ANum c)))).

Definition andEmp P :=
  AsAnd AsEmp P.

Definition c0Emp c :=
  andEmp (AsBool (c == ANum 0)).
Definition auEmp a u :=
  andEmp (AsBool (a == u)).

Definition loopInv tid n :=
  (AsOr asnPushedTrue (nToken n)) ** γreadEx tid.

Definition alpha i a c u :=
      (AsMpRd (APlus(AVar C) (ANum i)) (ANum c) **
       AsMpRd (APlus(AVar A) (ANum i)) (ANum a)) ** 
      (AsOr
         (AsOr (c0Emp (ANum c)) (auEmp (ANum a) (ANum u)))
          ◇
      ).

(* ∃a,c. (C[i] |->r c) ** (A[i] |->r a) ** (c = 0 \/ a= u \/ ◇)*)
Definition alphaEx i u :=
  AsEx (fun a =>
          AsEx (fun c =>
                  alpha i a c u
               )
  ).

(* 0 <= j < n, U ** alphaEx j u *)
Definition I' j n u :=
  AstarExcludeJAlpha 0 j n alphaEx u.

Eval compute in (I' 2 3 0).

(* 自明だけど証明が大変そう *)
Lemma lemma4 : forall n j σ u,
    σ |= (nToken (n-1) ** AstarExcludeJGamma 0 j n γreadEx) ->
    σ |= (I' j n u).
Proof.
Admitted.  
Lemma lemma5 : forall j t u σ,
    σ |= (AsAnd (AsBool(t != (ANum u)))
                 (γread j t (ANum 1)) **
                 alphaEx j u) ->
    σ |= (◇ ** (γfull j t (ANum 1))).
Proof.
Admitted.

Eval compute in (AstarExcludeJGamma 1 2 4 γreadEx).


(* 
  (∃u. A→_r u ** C→_r u) ** (∃t.A→_r t ** C→_r t) 
⇒ (∃u. A→u ** C→u) ?
もっと噛み砕くなら
(∃u. A→_r u) ** (∃t. A→_r t)
⇒ (∃u. A→ u) これは成り立つ。readなら値は一緒でないといけない。u = t 
  ((c = 0 ∧ emp) \/ (a = u ∧ emp) \/ ◇) 
⇒ emp
 *)

Lemma eqAsExRdEx : forall σ,
    σ |= (AsEx (fun u => AsMpRd (AVar A) (ANum u)) **
                AsEx (fun t => AsMpRd (AVar A) (ANum t))) ->
    σ |= (AsEx (fun u => AsMpFl (AVar A) (ANum u))).
Proof.
  intros.
  inversion_clear H. des_ex.
  inversion_clear H2. inversion_clear H3.
  des_ex.
  inversion_clear H3.
  inversion_clear H2. unfold takeHp in *. simpl in *.
  unfold defUnion in H0.
  unfold heapEq in H4. unfold M.Equal in H4.
  assert(M.find (elt:=nat * perm) (takeSt (takeSt σ, x0, x2) A) x0 =
       M.find (elt:=nat * perm) (takeSt (takeSt σ, x0, x2) A)
         (singleton (takeSt (takeSt σ, x0, x2) A) (x5, read))).
  apply H4.
  assert(M.find (elt:=nat * perm) (takeSt (takeSt σ, x0, x2) A)
                (singleton (takeSt (takeSt σ, x0, x2) A) (x5, read)) = Some (x5,read)).
  unfold takeSt in *. simpl in *.
  apply MFacts.F.add_eq_o.
  auto.
  unfold takeSt in*. simpl in *.
  rewrite <-H4 in H5.
  apply H0 with (v2:= (x4,read))in H5.
  inversion H5.
  constructor.
  exists x4.
  rewrite rdFl_iff.
  constructor.
  exists x0,x1,x2,x3.
  repeat split;auto. constructor. rewrite <-H7. auto.
  constructor. auto. 
  unfold heapEq in H3. unfold M.Equal in H3.
  assert(M.find (elt:=nat * perm) ((fst (fst σ) A))
         (singleton (fst (fst σ) A) (x4, read)) = Some (x4,read)).
  apply MFacts.F.add_eq_o. auto.
  rewrite <-H3 in H6. auto.
Qed.

Lemma gmExAlExInvEmp : forall tid σ u,
    σ |= ((γreadEx tid) ** alphaEx tid u) ->
    σ |= (γfullEx tid).
Proof.
Admitted.
  

(* 自明だが証明が大変そう *)
Lemma alInvSep_iff : forall j n u σ,
    σ |= AstarAlpha 0 n alphaEx u <->
    σ |= (alphaEx j u ** I' j n u).
Proof.
Admitted.

(* 自明だが証明が大変そう *)
Lemma gmAlPickRdFl_iff : forall j a c u n σ,
      σ |= (γread j a c ** AstarAlpha 0 n alphaEx u) -> 
      σ |= (γfull j a c ** AstarExcludeJGamma 0 j n γreadEx).
Proof.
Admitted.


Definition Iinv j a c n :=
  AsEx(
      fun u =>
        AsMpFl (AVar Stack) (ANum u) **
        (alpha a c j u ** (I' j n u))
    ).

(* I = ∃u. S |-> u ** (alphaEx j u) ** (I' j n u) *)
Definition I j n :=
  AsEx(
      fun u =>
        AsMpFl (AVar Stack) (ANum u) **
        (alphaEx j u ** (I' j n u))
    ).

(* 自明だけど証明が大変そう *)
Axiom invRewrite_iff : forall j n σ,
    j < n ->
    σ |= I j n ->
    σ |= AsEx (
                  fun u => 
                    AsMpFl (AVar Stack) (ANum u) **
                    AstarAlpha 0 n alphaEx u
              ).

Lemma nTokenAbs : forall n,
    1 <= n ->
    (◇ ** nToken (n-1)) = (nToken n).
Proof.
  intros.
  unfold nToken.
  destruct n. inversion H.
  simpl.
  rewrite OrdersEx.Nat_as_DT.sub_0_r.
  auto.  
Qed.


(* x |-> v * ∃u. x+1 |-> u *)
Definition asnAlcX v :=
  (AsMpFl (AVar x) v) **
  (AsEx (fun u => (AsMpFl (APlus(AVar x) (ANum 1)) (ANum u)))).
Definition lpInv n v :=
  asnAlcX v **  AsOr (andEmp asnPushedTrue) (nToken n).

Lemma fvAsnNtIn : forall tid u X,
    ~X = A ->
    ~X = C ->
    fvAsn (alphaEx tid u) X-> False.
Proof.
  intros.
  simpl in H1.
  des_ex. repeat destruct H1;congruence.
Qed.
(* 自明だけど証明が大変そう *)
Axiom I'ntInAsn : forall tid u n X,
    ~ X = A ->
    ~ X = C ->
    ~fvAsn (I' tid n u) X.
Axiom alphantInAsn : forall from n u X,
    ~ X = A ->
    ~ X = C ->
    ~ fvAsn (AstarAlpha from n alphaEx u) X.

Lemma nTokenNtInAsn : forall n X,
    ~ fvAsn (nToken n) X.
Proof.
  induction n;intros X H;simpl in H. auto.
  destruct H. auto.
  unfold nToken in IHn.
  unfold not in IHn. eapply IHn. apply H.
Qed.

Definition push v tid :=
  idPush ::= (ANum 9);;         (* pushed := False *)
  x ::= ALLOC (ANum 2);;
  ([AVar x] ::= v);;
  (WHILE (BNot pushed) DO
    ATOMIC (
      t::= [AVar Stack];;
      ([APlus(AVar C) (ANum tid)] ::= (ANum 1));; (* C[tid] ::= 1 *)
      ([APlus(AVar A) (ANum tid)] ::= AVar t)     (* A[tid] ::= t *)
    );;
    ([APlus(AVar x) (ANum 1)]   ::= AVar t);;
    ATOMIC (
      s::= [AVar Stack];;                  (*  s  := [S] *)
      IFB ((AVar s) == (AVar t)) THEN
        ([AVar Stack]::= (AVar x));;       (* [S] := x *)
        idPush  ::= (ANum 10)         (* pushed := True *)
      ELSE                   
        SKIP
      FI;;
      ([APlus(AVar C) (ANum tid)]::= (ANum 0))     (* C[tid] ::= 0 *)
    )
  END)
.


Theorem pushValid : forall tid v n,
    1 <= n ->
    tid < n ->
    I tid n |-
    {{γreadEx tid ** nToken n}}
        push (ANum v) tid
    {{AsEx (fun var =>
                AsMpFl (ANum var) (ANum v) **
          AsEx (fun u : nat => AsMpFl (APlus (ANum var) (ANum 1)) (ANum u))) **
    γreadEx tid}}.
Proof.
  unfold push.
  intros tid v n Hn Htid.
  eapply csep_conseq with
      ( P := γreadEx tid ** nToken n).
  split.
  do 3 try eapply csep_seq.
  (* while (!pushed) *)
  eapply csep_while
    with (P := ((AsMpFl (AVar x) (ANum v)) ** (AsEx (fun u=> (AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)))) ** (AsOr (andEmp asnPushedTrue) (nToken n)) ** (γreadEx tid)))
         (P' := ((AsMpFl (AVar x) (ANum v)) ** (AsEx (fun u=> (AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))))) ** ((nToken (n-1)) ** (γreadEx tid)))
  .
  split.
  Focus 5.
  eapply csep_conseq. split.
  (* pushed := false *)
  apply csep_assign with
      (P := fun v => AsAnd (γreadEx tid ** nToken n) (AsBool (ANum 9 == v)) ).
  simpl.  intros H. des_ex.
  do 2 destruct H;auto.  inversion H.
  do 5 destruct H;auto;try inversion H. auto. auto. auto. auto.
  assert (~fvAsn (I' tid n x0) idPush).
  apply I'ntInAsn. auto.
  intros not. inversion not.
  intros not. inversion not. congruence.

  split;intros σ H.
  constructor. apply H.
  constructor. auto. eauto.

  (* x := alloc(2) *)
  Focus 4.
  eapply csep_conseq.
  split.
  eapply csep_frame with
      ( P := AsEmp)
      ( Q := (AsMpFl (AVar x) (ANum 0)) **  (AsMpFl (APlus (AVar x) (ANum 1)) (ANum 0)))
      ( R := AsAnd (γreadEx tid ** nToken n) (AsBool (ANum 9 == AVar idPush))).
  split.
  eapply csep_conseq. split.
  apply csep_alloc.
  intros H. simpl in H.
  do 3 destruct H;auto. inversion H.
  do 5 destruct H;auto. inversion H. inversion H. destruct H;auto.
  destruct H;auto.
  assert (~fvAsn (I' tid n x0) x).
  apply I'ntInAsn. auto.
  intros not. inversion not.
  intros not. inversion not. congruence.
  split;intros σ H. auto. unfold asMllocN in H.
  rewrite <-sepStarAssoc_iff in H.
  rewrite sepStarEmp_iff in H. 
  inversion_clear H. des_ex.
  constructor. 
  unfold takeSt, takeHp in*;simpl in *.
  exists x0,x1,x2,x3.
  repeat (split;auto).
  inversion_clear H2. constructor. auto.
  inversion_clear H3. constructor. 
  unfold takeSt, takeHp in*;simpl in *.
  rewrite PeanoNat.Nat.add_1_r. auto.
  intros. simpl in *.
  destruct H0.
  destruct H. destruct H. do 4 destruct H.  subst. inversion H0.
  auto. subst. inversion H0. auto. assert (~fvAsn (nToken n) X).
  apply nTokenNtInAsn. congruence.
  destruct H. subst. inversion H0. auto. auto.
  split;intros σ H.
  rewrite sepStarCom_iff.
  rewrite sepStarEmp_iff. auto.
  eauto.

  (* [x] := v *)
  Focus 3.
  eapply csep_conseq. split.
  apply csep_frame with
      (R :=
       AsAnd (γreadEx tid ** nToken n)
         (AsBool (ANum 9 == AVar idPush))).
  split.
  apply csep_frame with
      (R := (AsMpFl (APlus (AVar x) (ANum 1)) (ANum 0))).
  split.
  apply csep_mutate.
  simpl. intros. auto.
  simpl. intros. auto.
  split;intros σ H.
  remember ((AsMpFl (AVar x) (ANum 0) **
             AsMpFl (APlus (AVar x) (ANum 1)) (ANum 0))) as alc.
  remember ((γreadEx tid ** nToken n)) as g.
  remember (AsBool (ANum 9 == AVar idPush)) as f.
  remember (alc ** AsAnd g f).
  remember ((AsEx (fun v0 : nat => AsMpFl (AVar x) (ANum v0)) **
       AsMpFl (APlus (AVar x) (ANum 1)) (ANum 0))).
  apply sepStarImpSt with
      (p1 := alc)
      (q1 := AsAnd g f)
  .
  intros.
  subst a0.
  subst alc.
  constructor.
  inversion_clear H0.
  des_ex.
  exists x0,x1,x2,x3.
  repeat split;auto.
  constructor.
  exists 0. auto.
  auto.
  subst alc. subst a. apply H.
  remember (AsAnd (γreadEx tid ** nToken n)
                  (AsBool (ANum 9 == AVar idPush))).
  remember ((AsMpFl (AVar x) (ANum v) **
                    AsMpFl (APlus (AVar x) (ANum 1)) (ANum 0))).
  remember ((AsMpFl (AVar x) (ANum v) **
        AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)))).
  repeat rewrite sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := a0)
      (q1 := a)
  ;intros;auto.
  subst a0. subst a1.
  inversion_clear H0.
  constructor. des_ex.
  exists x0,x1,x2,x3.
  repeat split;auto.
  constructor.
  exists 0. auto.
  subst a. clear Heqa1. clear H. clear Heqa0.
  remember((AsBool (ANum 9 == AVar idPush))).
  remember (γreadEx tid ** nToken n).
  inversion_clear H0.
  subst a2.
  rewrite sepStarCom_iff.
  inversion_clear H.
  des_ex.
  constructor.
  exists x0,x1,x2,x3.
  repeat split;auto.
  apply jdg_or_r. apply H4.
  intros σ H.
  remember ((((AsMpFl (AVar x) (ANum v) **
              AsEx
                (fun u : nat =>
                 AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))) **
             AsOr (andEmp asnPushedTrue) (nToken n)) ** 
                                                     γreadEx tid)).
  inversion_clear H.
  subst a.
  inversion_clear H0.
  des_ex.
  remember ((AsMpFl (AVar x) (ANum v) **
            AsEx
              (fun u : nat =>
                 AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)))).
  rewrite sepStarCom_iff.
  assert (σ |= ( a ** ((◇ ** (nToken (n - 1))) ** γreadEx tid))).
  rewrite nTokenAbs.
  inversion_clear H3.
  des_ex.
  rewrite <-sepStarAssoc_iff.
  constructor.
  unfold takeHp, takeSt in *. simpl in *.
  exists x0,x1,x2,x3.
  repeat split;auto.
  constructor.
  exists x4,x5,x6,x7.
  repeat split;auto.
  inversion_clear H8.
  inversion_clear H9.
  inversion H1.
  inversion H10. subst. simpl in *.
  unfold takeSt in *. simpl in *.
  rewrite H13 in H11. inversion H11. auto. auto.
  rewrite <-sepStarAssoc_iff in H5.
  do 2 rewrite <-sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := (a ** (◇ ** nToken (n - 1))))
      (q1 := γreadEx tid)
  .
  intros.
  clear H1. clear H.
  rewrite sepStarCom_iff.
  rewrite <-sepStarAssoc_iff.
  rewrite nTokenAbs in H6.
  rewrite sepStarCom_iff.
  apply sepStarImpSt with
      (p1 := a)
      (q1 := nToken n)
  ;auto.
  intros.
  rewrite sepStarCom_iff. rewrite nTokenAbs.
  auto. auto. auto. auto. auto.
  (* x |-> vをframe ruleで消去 *)
  apply csep_conseq with
      (P := AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) **
       (nToken (n - 1) ** γreadEx tid) ** AsMpFl (AVar x) (ANum v))
      (Q := ((AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) **
          AsOr (andEmp asnPushedTrue) (nToken n)) ** γreadEx tid) ** AsMpFl (AVar x) (ANum v)).
  split. Focus 2.
  split;intros σ H.
  remember (AsEx
              (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))).
  remember ((nToken (n - 1) ** γreadEx tid)).
  rewrite sepStarCom_iff.
  rewrite <-sepStarAssoc_iff.
  auto.
  remember (AsEx
              (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))).
  remember (AsOr (andEmp asnPushedTrue) (nToken n)).
  repeat rewrite sepStarAssoc_iff.
  rewrite sepStarCom_iff.
  apply sepStarImpSt with
      (p1 := ((a ** a0) ** γreadEx tid))
      (q1 := AsMpFl (AVar x) (ANum v));auto.
  intros.
  rewrite <-sepStarAssoc_iff. auto.
  
  apply csep_frame. split.
  apply csep_seq with
      (Q := ((AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))) ** γread tid (AVar t) (ANum 1)) ** nToken (n-1)).

  Focus 2.
  (* atomic 1 *)
  apply csep_atom.
  unfold I.
  remember ((AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) **
          (nToken (n - 1) ** γreadEx tid))).
  remember (((AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) **
      γread tid (AVar t) (ANum 1)) ** nToken (n - 1))).
  apply csep_conseq with
      (P := AsEx( fun k => a ** AsMpFl (AVar Stack) (ANum k) **
          (alphaEx tid k ** I' tid n k)))
      (Q := AsEx( fun k => a0 ** AsMpFl (AVar Stack) (ANum k) **
          (alphaEx tid k ** I' tid n k))).
  split.
  apply csep_ex.
  intro k.
  apply csep_conseq with
      (P := ((a ** AsMpFl (AVar Stack) (ANum k)) **
       alphaEx tid k) ** I' tid n k)
      (Q := ((a0 ** AsMpFl (AVar Stack) (ANum k)) **
    (alphaEx tid k)) ** I' tid n k).
  split. apply csep_frame. split.

  subst a.
  apply csep_seq with
      (Q :=
         (AsAnd
           (AsMpFl (AVar Stack) (ANum k))
           (AsBool ((AVar t) == (ANum k)))) **
                   γfullEx tid ** AsEx
           (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) **
           (nToken (n - 1))).
  
  (* t ::= [S] *)
  Focus 2.
  eapply csep_conseq with
      (P := (AsMpFl (AVar Stack) (ANum k) ** (γreadEx tid ** alphaEx tid k)) ** AsEx
           (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) **
         (nToken (n - 1))).
  split.

  Focus 2. split;intros σ H.
  remember (AsMpFl (AVar Stack) (ANum k)).
  remember (AsEx
              (fun u : nat =>
                 AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))).
  rewrite sepStarCom_iff.
  rewrite <-sepStarAssoc_iff.
  rewrite sepStarCom_iff.
  repeat rewrite sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := a1)
      (q1 := ((nToken (n - 1) ** γreadEx tid) ** (a ** alphaEx tid k)));
    intros;auto.
  clear H.
  rewrite sepStarAssoc_iff in H0.
  apply sepStarImpSt with
      (p1 := nToken (n - 1))
      (q1 := (γreadEx tid ** (a ** alphaEx tid k)));intros;auto.
  clear H0.
  rewrite sepStarCom_iff in H.
  rewrite sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := a)
      (q1 := (alphaEx tid k ** γreadEx tid));intros;auto.
  rewrite sepStarCom_iff. auto. eauto.

  apply csep_frame. split.
  apply csep_frame. split.
  eapply csep_conseq with
      (P :=(AsMpFl (AVar Stack) (ANum k)) ** γfullEx tid)
  .
  split.
  Focus 2.  
  split;intros σ H;eauto.
  apply sepStarImpSt with
      (p1 :=(AsMpFl (AVar Stack) (ANum k)))
      (q1 := (γreadEx tid ** alphaEx tid k));auto.
  intros.

  apply gmExAlExInvEmp in H0. auto.
  apply csep_frame. split.
  apply csep_conseq with
      (P := AsMpRd (AVar Stack) (ANum k) ** AsMpRd (AVar Stack) (ANum k))
      (Q := AsAnd
              (AsMpRd (AVar Stack) (ANum k))
              ((AsBool (AVar t == ANum k))) **
              AsMpRd (AVar Stack) (ANum k)
      ).
  split. Focus 2.
  split;intros σ H.
  rewrite rdFl_iff in H. auto.
  remember ((AsBool (AVar t == ANum k))).
  remember (AsMpFl (AVar Stack) (ANum k)).
  constructor.
  subst a1. rewrite rdFl_iff.
  inversion_clear H. des_ex.
  constructor.
  exists x0,x1,x2,x3.
  repeat split;auto. inversion_clear H2.
  auto.
  subst a.
  inversion_clear H.
  des_ex. inversion_clear H2. inversion_clear H5. constructor. auto.

  apply csep_frame.
  split. apply csep_lookup;simpl;auto. intro. destruct H;inversion H.
  simpl. intros. destruct H. destruct H0. subst. inversion H0. auto.
  auto. simpl. intros. des_ex.
  destruct H. destruct H. destruct H0. subst. inversion H0. auto.
  auto. destruct H. destruct H0. subst. inversion H0. auto. auto.
  simpl. intros. des_ex. destruct H. destruct H0. subst. inversion H0.
  auto. auto. simpl. intros.
  apply nTokenNtInAsn in H. auto.

  (* C[tid] := 1 *)
  apply csep_seq with
      (Q := AsEx(fun a => γfull tid (ANum a) (ANum 1)) **
            (AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) ** 
            nToken (n - 1)) ** (AsAnd (AsMpFl (AVar Stack) (ANum k))
            (AsBool (AVar t == ANum k))))
  .
  Focus 2.
  eapply csep_conseq with
      (P := γfullEx tid **
       ((AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))) ** 
       nToken (n - 1)) ** (AsAnd (AsMpFl (AVar Stack) (ANum k))
           (AsBool (AVar t == ANum k)))).
  split.
  Focus 2.
  split;intros σ H;eauto.
  remember (AsAnd (AsMpFl (AVar Stack) (ANum k))
                  (AsBool (AVar t == ANum k))).
  remember (AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))).
  rewrite sepStarCom_iff.
  repeat rewrite <-sepStarAssoc_iff.
  auto.

  repeat (try apply csep_frame;try split).

  unfold γfullEx. unfold γfull. unfold γ.
  apply csep_ex. intro a.
  apply csep_conseq with
      (P := AsEx
         (fun c : nat =>
          AsMpFl (APlus (AVar C) (ANum tid)) (ANum c)) **
         AsMpFl (APlus (AVar A) (ANum tid)) (ANum a)
      )
      (Q := 
         AsMpFl (APlus (AVar C) (ANum tid)) (ANum 1) **
         AsMpFl (APlus (AVar A) (ANum tid)) (ANum a)
      ).
  split.
  Focus 2. split;intros σ H.
  rewrite sepStarExAssocSt.
  remember ((fun c : nat =>
            AsMpFl (APlus (AVar A) (ANum tid)) (ANum a) **
                   AsMpFl (APlus (AVar C) (ANum tid)) (ANum c))).
  inversion_clear H. des_ex.
  subst a1. rewrite sepStarCom_iff in H.
  inversion_clear H.
  des_ex.
  constructor. exists x0. constructor.
  exists x1,x2,x3,x4. repeat split;auto.
  rewrite sepStarCom_iff. auto.

  apply csep_frame. split.
  apply csep_mutate.
  simpl. intros. auto.
  simpl. intros. auto.
  simpl. intros. auto.

  (* A[tid] := t *)
  subst a0.
  remember (APlus (AVar A) (ANum tid)) as la.
  remember (APlus (AVar C) (ANum tid)) as lc.
  remember (AsEx(fun a => AsMpFl la (ANum a)) ** AsMpFl lc (ANum 1)) as gmP.
  remember (γread tid (AVar t) (ANum 1)) as gmQ.
  remember (alphaEx tid k) as alQ.
  apply csep_conseq with
      (P := (gmP ** AsAnd (AsMpFl (AVar Stack) (ANum k))
         (AsBool (AVar t == ANum k))) ** (AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) ** nToken (n - 1)))
      (Q := ((gmQ ** alQ) ** AsMpFl (AVar Stack) (ANum k)) **
         (AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) ** nToken (n - 1))
      ).
  split.
  Focus 2.
  split;intros σ H.
  remember (AsEx (fun a : nat => γfull tid (ANum a) (ANum 1))) as gmpH.
  remember (AsAnd (AsMpFl (AVar Stack) (ANum k))
                  (AsBool (AVar t == ANum k))) as stk.
  remember ((AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) **
                    nToken (n - 1))) as fr.
  rewrite sepStarAssoc_iff in H.
  rewrite sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := gmpH)
      (q1 := (fr ** stk)).
  clear H. intros.
  subst.
  inversion_clear H. des_ex.
  constructor. unfold γfull,γ in H.
  inversion_clear H. des_ex.
  exists x1,x2,x3,x4. repeat split;auto.
  constructor.
  exists x0. auto.
  intros. rewrite sepStarCom_iff. auto. auto.
  remember (AsEx
          (fun u : nat => AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))) as x1t.
  remember ((x1t ** nToken (n - 1))).
  rewrite sepStarCom_iff in H.
  rewrite <-sepStarAssoc_iff in H.
  remember (((x1t ** gmQ) ** nToken (n - 1))).
  rewrite sepStarCom_iff.
  rewrite <-sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := (a ** (gmQ ** alQ)))
      (q1 := AsMpFl (AVar Stack) (ANum k));auto.
  intros.
  rewrite <-sepStarAssoc_iff in H0.
  rewrite sepStarCom_iff.
  apply sepStarImpSt with
      (p1 := a ** gmQ)
      (q1 := alQ);auto.
  intros. subst a0. subst a.
  rewrite sepStarAssoc_iff in H1.
  rewrite sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := x1t)
      (q1 := nToken (n - 1) ** gmQ);auto.
  intros. rewrite sepStarCom_iff. auto.

  apply csep_frame. split.
  subst gmP.
  remember (AsEx (fun a : nat => AsMpFl la (ANum a))).
  
  apply csep_conseq with
      (P := a ** AsAnd (AsMpFl (AVar Stack) (ANum k))
               (AsBool (AVar t == ANum k)) ** AsMpFl lc (ANum 1))
      (Q :=  (((AsMpRd lc (ANum 1) ** AsMpRd lc (ANum 1)) **
             (AsMpRd la (AVar t))) ** AsMpRd la (AVar t)) ** (AsAnd AsEmp (AsBool (AVar t == ANum k))) ** AsMpFl (AVar Stack) (ANum k)).
  split.
  Focus 2.
  split;intros σ H.
  rewrite sepStarAssoc_iff.
  rewrite sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := a)
      (q1 := (AsMpFl lc (ANum 1) **
           AsAnd (AsMpFl (AVar Stack) (ANum k))
           (AsBool (AVar t == ANum k))));auto.
  intros.
  rewrite sepStarCom_iff. auto.
  apply sepStarImpSt with
      (p1 := ((((AsMpRd lc (ANum 1) ** AsMpRd lc (ANum 1)) **
             AsMpRd la (AVar t)) ** AsMpRd la (AVar t)) **
           AsAnd AsEmp (AsBool (AVar t == ANum k)))
      )
      (q1 := AsMpFl (AVar Stack) (ANum k));auto.
  intros. clear H.

  assert (σ0
       |= ((AsMpRd lc (ANum 1) ** AsMpRd la (AVar t)) **
             ((AsMpRd lc (ANum 1)) ** AsMpRd la (AVar t)) **
           AsAnd AsEmp (AsBool (AVar t == ANum k)))).

  remember (AsAnd AsEmp (AsBool (AVar t == ANum k))).
  remember ((((AsMpRd lc (ANum 1) ** AsMpRd lc (ANum 1)) **
             AsMpRd la (AVar t)) ** AsMpRd la (AVar t))).

  apply sepStarImpSt with
      (p1 := a1)
      (q1 := a0);auto.
  intros.
  rewrite sepStarAssoc_iff.
  subst a1.
  repeat rewrite sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := AsMpRd lc (ANum 1))
      (q1 := (AsMpRd lc (ANum 1) **
           (AsMpRd la (AVar t) ** AsMpRd la (AVar t))));auto.
  intros.
  rewrite <-sepStarAssoc_iff.
  rewrite <-sepStarAssoc_iff in H1.
  apply sepStarImpSt with
      (p1 := (AsMpRd lc (ANum 1) ** AsMpRd la (AVar t)))
      (q1 := AsMpRd la (AVar t));auto.
  intros.
  rewrite sepStarCom_iff. auto.
  clear H0.
  apply sepStarImpSt with
      (p1 := (AsMpRd lc (ANum 1) ** AsMpRd la (AVar t)))
      (q1 := (AsMpRd lc (ANum 1) ** AsMpRd la (AVar t)) **
          AsAnd AsEmp (AsBool (AVar t == ANum k)));auto.
  intros.
  subst gmQ. unfold γread,γ. rewrite sepStarCom_iff. subst lc la.
  apply H0.
  intros.
  subst alQ. unfold alphaEx, alpha.
  clear H.
  inversion_clear H0.
  des_ex. inversion_clear H2. des_ex.
  constructor.
  subst.
  unfold takeHp, takeSt in *. simpl in *.
  exists (fst (fst σ1) t).
  constructor. exists 1.
  constructor.
  exists x0,x1,x2,x3.
  repeat split;auto.
  constructor.
  exists x4,x5,x6,x7.
  repeat split;auto.
  constructor.
  inversion_clear H7. auto.
  apply jdg_or_l. apply jdg_or_r.
  constructor. inversion_clear H3.
  auto.
  inversion_clear H3. inversion_clear H9.
  constructor. auto.
  rewrite sepStarAssoc_iff in H. auto.
  eapply csep_conseq with
      (Q := ((((AsMpFl lc (ANum 1)) **
       AsMpFl la (AVar t))) **
     AsAnd AsEmp (AsBool (AVar t == ANum k))) **
    AsMpFl (AVar Stack) (ANum k)).
  split.
  Focus 2.
  split;intros σ H;eauto.
  apply sepStarImpSt with
      (p1 := ((AsMpFl lc (ANum 1) ** AsMpFl la (AVar t)) **
           AsAnd AsEmp (AsBool (AVar t == ANum k))))
      (q1 := AsMpFl (AVar Stack) (ANum k));auto.
  intros.
  eapply sepStarImpSt with
      (p1 := (AsMpFl lc (ANum 1) ** AsMpFl la (AVar t)));eauto.
  intros.
  rewrite sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := (AsMpFl lc (ANum 1)))
      (q1 := AsMpFl la (AVar t));
    intros;try rewrite rdFl_iff in H2;auto.

  eapply csep_conseq with
      (Q := (AsMpFl la (AVar t) ** AsEmp) **
            (AsAnd (AsMpFl (AVar Stack) (ANum k))
          (AsBool (AVar t == ANum k))) ** (AsMpFl lc (ANum 1))).

  split.
  Focus 2.
  split;intros σ H;eauto.

  remember (AsAnd (AsMpFl (AVar Stack) (ANum k))
                  (AsBool (AVar t == ANum k))) as stk.
  remember (AsMpFl la (AVar t)) as Ha.
  remember (AsMpFl lc (ANum 1)) as Hc.
  rewrite sepStarCom_iff in H.
  repeat rewrite sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := Hc)
      (q1 := ((Ha ** AsEmp) ** stk));auto.
  intros. clear HeqHc. clear H.
  rewrite sepStarAssoc_iff in H0.
  apply sepStarImpSt with
      (p1 := Ha)
      (q1 := (AsEmp ** stk));auto.
  intros.
  assert (σ1 |= AsAnd (AsBool (AVar t == ANum k)) (AsMpFl (AVar Stack) (ANum k))).
  constructor.
  rewrite sepStarCom_iff in H.
  rewrite sepStarEmp_iff in H.
  subst stk.
  inversion_clear H. auto.
  rewrite sepStarCom_iff in H.
  rewrite sepStarEmp_iff in H.
  subst stk. inversion_clear H. auto.
  rewrite <-sepStarEmp_iff in H1.
  rewrite sepStarPureAnd in H1.

  assert (σ1 |= AsAnd (AsBool (AVar t == ANum k))
              (AsEmp ** AsMpFl (AVar Stack) (ANum k))).
  remember (AsMpFl (AVar Stack) (ANum k) ** AsEmp).
  inversion_clear H1. 
  remember ((AsEmp ** AsMpFl (AVar Stack) (ANum k))).
  constructor. 
  subst a0 a1. auto.
  subst.
  rewrite sepStarCom_iff. auto.
  rewrite <-sepStarPureAnd in H2. clear H1. clear H0. clear H.
  inversion_clear H2. des_ex. constructor.
  exists x0,x1,x2,x3.
  repeat split;auto.
  inversion_clear H2. constructor. auto. auto.
  simpl. auto. simpl. auto.
  apply csep_frame. split.
  apply csep_frame. split.
  subst a.
  eapply csep_conseq. split.
  apply csep_mutate.
  split;intros σ H;auto.
  rewrite sepStarEmp_iff. auto.
  simpl. intros. auto.   simpl. intros. auto.
  simpl. intros. auto. simpl. intros. apply I'ntInAsn in H;auto.
  destruct H0. intro.  subst. inversion H1. auto.
  intro. destruct H0. subst. inversion H1. auto.

  split;intros σ H.
  rewrite sepStarAssoc_iff. auto.
  rewrite <-sepStarAssoc_iff. auto.
  split;intros σ H.

  remember ((fun u : nat =>
             AsMpFl (AVar Stack) (ANum u) **
                    (alphaEx tid u ** I' tid n u))).
  inversion_clear H.
  des_ex.
  inversion_clear H3. des_ex.
  remember ((fun k : nat =>
        (a ** AsMpFl (AVar Stack) (ANum k)) **
        (alphaEx tid k ** I' tid n k))).
  constructor. exists x4.
  subst a2.
  rewrite sepStarAssoc_iff.
  remember ((AsMpFl (AVar Stack) (ANum x4) **
                    (alphaEx tid x4 ** I' tid n x4))).
  constructor.
  exists x0,x1,x2,x3.
  repeat split;auto. subst. auto.
  remember ((fun u : nat =>
               AsMpFl (AVar Stack) (ANum u) ** (alphaEx tid u ** I' tid n u))).
  remember ((fun k : nat =>
            (a0 ** AsMpFl (AVar Stack) (ANum k)) **
            (alphaEx tid k ** I' tid n k))).
  subst a2.
  inversion_clear H. des_ex.
  rewrite sepStarAssoc_iff in H.
  remember ((AsMpFl (AVar Stack) (ANum x0) **
                    (alphaEx tid x0 ** I' tid n x0))).
  inversion_clear H. des_ex. constructor.
  exists x1,x2,x3,x4.
  repeat split;auto.
  constructor.
  exists x0. subst. auto.
  
  (* [x+1] := t *)
  apply csep_seq with
      (Q := (AsMpFl (APlus (AVar x) (ANum 1)) (AVar t) **
        γread tid (AVar t) (ANum 1)) ** nToken (n - 1)).
  Focus 2.
  apply csep_frame. split.
  apply csep_frame. split.
  apply csep_mutate. simpl. intros. auto.
  simpl. intros. auto.

  (* atomic 2 *)
  eapply csep_conseq with
      (Q := (AsMpFl (APlus (AVar x) (ANum 1)) (AVar t) **
           AsOr (andEmp asnPushedTrue) (nToken n)) ** 
      γreadEx tid).
  split.
  Focus 2.
  split;intros σ H;eauto.
  rewrite sepStarAssoc_iff.
  rewrite sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := AsMpFl (APlus (AVar x) (ANum 1)) (AVar t))
      (q1 := (AsOr (andEmp asnPushedTrue) (nToken n) ** γreadEx tid));
    auto.
  intros. clear H.
  inversion_clear H0. constructor.
  simpl in *.
  exists (takeSt σ0 t).
  constructor.
  auto.

  eapply csep_conseq with
      (P := (γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
             AsMpFl (APlus (AVar x) (ANum 1)) (AVar t)
      )
      (Q := ((AsOr (andEmp asnPushedTrue) (nToken n)) ** 
    γreadEx tid) ** AsMpFl (APlus (AVar x) (ANum 1)) (AVar t)).
  split.
  Focus 2.
  split;intros σ H.
  rewrite sepStarAssoc_iff in H.
  rewrite sepStarCom_iff;auto.
  rewrite sepStarAssoc_iff.
  rewrite sepStarCom_iff. auto.
  apply csep_frame. split.

  apply csep_atom.

  apply csep_conseq with
      (P := AsEx
              (fun u =>
                 (γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
         AsMpFl (AVar Stack) (ANum u) ** AstarAlpha 0 n alphaEx u)
      )
      (Q :=
         AsEx
           (fun u =>
           (AsOr (andEmp asnPushedTrue) (nToken n) ** γreadEx tid) **

           (AsMpFl (AVar Stack) (ANum u) ** (alphaEx tid u ** I' tid n u))
           )
      ).
  split.
  Focus 2.
  split;intros σ H.
  remember ((γread tid (AVar t) (ANum 1) ** nToken (n - 1))).
  remember ((fun u : nat =>
             AsMpFl (AVar Stack) (ANum u) ** AstarAlpha 0 n alphaEx u)).
  inversion_clear H.
  des_ex.
  apply invRewrite_iff in H3.
  inversion_clear H3. des_ex.
  constructor.
  exists x4.
  rewrite sepStarAssoc_iff.
  subst a0.
  remember ((AsMpFl (AVar Stack) (ANum x4) ** AstarAlpha 0 n alphaEx x4)).
  constructor.
  exists x0,x1,x2,x3. repeat split;auto.
  auto.
  inversion_clear H. des_ex.
  unfold I.
  apply sepStarImpSt with
      (p1 := (AsOr (andEmp asnPushedTrue) (nToken n) ** γreadEx tid))
      (q1 := (AsMpFl (AVar Stack) (ANum x0) **
                     (alphaEx tid x0 ** I' tid n x0)));auto.
  intros.
  remember ((fun u : nat =>
        AsMpFl (AVar Stack) (ANum u) ** (alphaEx tid u ** I' tid n u))).
  constructor.
  exists x0. subst a. auto.

  apply csep_seq with
      (Q := AsEx (fun u =>
         ((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
             (AsAnd (AsBool (ANum u == AVar s))
                    (AsMpFl (AVar Stack) (ANum u)))
             ** AstarAlpha 0 n alphaEx u))).
  Focus 2.

  (* s := [S] *)
  apply csep_ex. intro k.

  apply csep_conseq with
      (P := AsMpFl (AVar Stack) (ANum k) **
                   (((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
        AstarAlpha 0 n alphaEx k)))
      (Q := (AsAnd (AsBool (ANum k == AVar s))
                   (AsMpFl (AVar Stack) (ANum k))) **
                   (((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
        AstarAlpha 0 n alphaEx k)))
  .
  split. Focus 2.
  split;intros σ H.
  remember ((γread tid (AVar t) (ANum 1) ** nToken (n - 1))).
  rewrite <-sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := (a ** AsMpFl (AVar Stack) (ANum k)))
      (q1 := AstarAlpha 0 n alphaEx k);auto.
  intros.
  rewrite sepStarCom_iff. auto.
  remember ((γread tid (AVar t) (ANum 1) ** nToken (n - 1))).
  rewrite <-sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := AsAnd (AsBool (ANum k == AVar s))
                   (AsMpFl (AVar Stack) (ANum k)) ** a)
      (q1 := AstarAlpha 0 n alphaEx k);auto.
  intros.
  rewrite sepStarCom_iff. auto.
  apply csep_frame. split.

  apply csep_conseq with
      (P := AsMpRd (AVar Stack) (ANum k) **
            AsMpRd (AVar Stack) (ANum k)
      )
      (Q := AsAnd (AsBool (ANum k == AVar s))
                  (AsMpRd (AVar Stack) (ANum k))**
            AsMpRd (AVar Stack) (ANum k)
      ).
  split.
  Focus 2.
  split;intros σ H.
  rewrite rdFl_iff in H. auto.
  rewrite sepStarPureAnd in H.
  remember ((AsMpRd (AVar Stack) (ANum k) **
            AsMpRd (AVar Stack) (ANum k))).
  inversion_clear H.
  subst a.
  constructor. auto.
  rewrite rdFl_iff. auto.
  simpl;auto.
  apply csep_frame. split.
  eapply csep_conseq with
      (Q := AsAnd (AsMpRd (AVar Stack) (ANum k)) (AsBool (AVar s == ANum k))).
  split.  
  apply csep_lookup. simpl. intro. destruct H. inversion H. auto.
  simpl. auto. auto.
  split;intros σ H;auto.
  simpl in *.
  inversion_clear H. inversion_clear H1.
  constructor. constructor. simpl in *.
  apply EqNat.beq_nat_true in H.
  rewrite H. rewrite <-EqNat.beq_nat_refl. auto.
  auto.
  simpl. intros. destruct H;destruct H0;subst;try inversion H;auto.
  inversion H0.
  simpl. intros. destruct H0;auto. destruct H. destruct H. destruct H.
  destruct H;subst;try inversion H0. destruct H;try inversion H;auto.
  destruct H. subst. inversion H0. auto.
  apply nTokenNtInAsn in H;auto.
  apply alphantInAsn in H;auto;intro;subst;try inversion H1.

  apply csep_seq with
      (Q :=
              AsEx
                (fun u : nat =>
                   (AsOr (andEmp asnPushedTrue) (nToken n) **
                         (γfullEx tid)) **
                   AsMpFl (AVar Stack) (ANum u) ** I' tid n u
                )
      ).

  (* C[tid] := 0  最後のプログラム *)
  
  apply csep_ex.
  intro k.
  apply csep_conseq with
      (P :=
         γfullEx tid **
         ((AsOr (andEmp asnPushedTrue) (nToken n)) **
         (AsMpFl (AVar Stack) (ANum k)) ** I' tid n k)
      )
      (Q :=
         (γreadEx tid ** alphaEx tid k) **
         ((AsOr (andEmp asnPushedTrue) (nToken n)) **
         (AsMpFl (AVar Stack) (ANum k)) ** I' tid n k)
      ).
  split. Focus 2.

  split;intros σ H.
  remember (AsOr (andEmp asnPushedTrue) (nToken n)).
  rewrite <-sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 :=((a ** γfullEx tid) ** AsMpFl (AVar Stack) (ANum k)))
      (q1 := I' tid n k)
  ;auto.
  intros.
  rewrite <-sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := a ** γfullEx tid)
      (q1 := AsMpFl (AVar Stack) (ANum k))
  ;auto.
  intros. rewrite sepStarCom_iff. auto.
  remember (AsOr (andEmp asnPushedTrue) (nToken n)).
  remember (γreadEx tid).
  repeat rewrite <-sepStarAssoc_iff.
  repeat rewrite <-sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := ((a0 ** alphaEx tid k) ** (a ** AsMpFl (AVar Stack) (ANum k))))
      (q1 := I' tid n k)
  ;auto.
  intros. clear H.
  rewrite sepStarCom_iff in H0.
  rewrite <-sepStarAssoc_iff in H0.
  apply sepStarImpSt with
      (p1 := ((a ** AsMpFl (AVar Stack) (ANum k)) ** a0))
      (q1 := alphaEx tid k);auto.

  intros. clear H0.
  rewrite sepStarCom_iff in H.
  rewrite <-sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := a0 ** a)
      (q1 := AsMpFl (AVar Stack) (ANum k));auto.
  intros.
  rewrite sepStarCom_iff.
  apply sepStarImpSt with
      (p1 := a0)
      (q1 := a );auto.

  apply csep_frame. split.
  remember(APlus (AVar A) (ANum tid)) as la.
  remember(APlus (AVar C) (ANum tid)) as lc.

  eapply csep_conseq with
      (Q :=
         AsEx(fun a =>
           AsEx(fun c =>
                (AsMpRd (APlus (AVar A) (ANum tid)) (ANum a) **
                 AsMpRd (APlus (AVar C) (ANum tid)) (ANum c)) **
                ((AsMpRd (APlus (AVar C) (ANum tid)) (ANum c) **
                  AsMpRd (APlus (AVar A) (ANum tid)) (ANum a)) **
             AsOr (AsOr (c0Emp (ANum c)) (auEmp (ANum a) (ANum k))) ◇)
               )
             )
      ).
  split.
  Focus 2.
  split;intros σ H;eauto.
  inversion_clear H. des_ex.
  inversion_clear H. des_ex.
  apply sepStarImpSt with
      (p1 := (AsMpRd (APlus (AVar A) (ANum tid)) (ANum x0) **
                     AsMpRd (APlus (AVar C) (ANum tid)) (ANum x1)))
      (q1 := ((AsMpRd (APlus (AVar C) (ANum tid)) (ANum x1) **
            AsMpRd (APlus (AVar A) (ANum tid)) (ANum x0)) **
           AsOr (AsOr (c0Emp (ANum x1)) (auEmp (ANum x0) (ANum k))) ◇));auto;intros;clear H.
  unfold γreadEx,γ. constructor.
  exists x0. constructor. exists x1. auto.
  unfold alphaEx,alpha.  constructor.
  exists x0. constructor. exists x1. auto.
  apply csep_ex.
  intro a.

  apply csep_conseq with
      (P := AsEx(fun c => AsMpFl lc (ANum c)) ** AsMpFl la (ANum a))
      (Q := AsEx(fun c =>
                   (AsMpFl lc (ANum c) ** AsMpFl la (ANum a)) **
                                                              AsOr (AsOr (c0Emp (ANum c)) (auEmp (ANum a) (ANum k))) ◇)
      ).
  split. Focus 2.
  split;intros σ H.
  inversion_clear H. des_ex.
  inversion_clear H.
  des_ex.
  rewrite sepStarCom_iff.
  constructor.
  exists x1,x2,x3,x4.
  repeat split;auto. subst la. apply H2.
  constructor.
  exists x0. subst lc.
  apply H3.
  constructor.
  inversion_clear H. des_ex.
  exists x0.
  repeat rewrite <-sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := (AsMpFl lc (ANum x0) ** AsMpFl la (ANum a))) 
      (q1 := AsOr (AsOr (c0Emp (ANum x0)) (auEmp (ANum a) (ANum k))) ◇);auto.
  intros.
  rewrite sepStarCom_iff.
  remember (AsMpRd (APlus (AVar C) (ANum tid)) (ANum x0)).
  remember (AsMpRd (APlus (AVar A) (ANum tid)) (ANum a)).
  assert (σ0 |= ((a0**a0) ** (a1**a1))).
  apply sepStarImpSt with
      (p1 := AsMpFl lc (ANum x0))
      (q1 := AsMpFl la (ANum a)).
  intros. subst a0. rewrite rdFl_iff in H1. subst lc;auto.
  intros. subst a1. rewrite rdFl_iff in H1. subst la;auto.
  auto.
  rewrite sepStarAssoc_iff.
  rewrite sepStarAssoc_iff in H1.
  apply sepStarImpSt with
      (p1 := a0)
      (q1 := (a0 ** (a1 ** a1)));auto.
  intros.
  rewrite <-sepStarAssoc_iff. rewrite sepStarCom_iff. apply H2.

  eapply csep_conseq with
      (Q := AsEx
      (fun c : nat =>
       (AsMpFl lc (ANum c) ** AsOr (AsOr (c0Emp (ANum c)) (auEmp (ANum a) (ANum k))) ◇)) ** AsMpFl la (ANum a)
      ). split.
  Focus 2. split;intros σ H;eauto.
  remember ((fun c : nat =>
             AsMpFl lc (ANum c) **
                    AsOr (AsOr (c0Emp (ANum c)) (auEmp (ANum a) (ANum k))) ◇)).
  inversion_clear H.
  des_ex. inversion_clear H2.
  constructor. des_ex.
  exists x4.
  subst a0.
  rewrite sepStarCom_iff in H2.
  rewrite sepStarCom_iff.
  rewrite <-sepStarAssoc_iff.
  inversion_clear H2. des_ex.
  constructor.   
  exists x0,x1,x2,x3.
  repeat split;auto.
  constructor.
  exists x5,x6,x7,x8. repeat split;auto.

  apply csep_frame. split.
  eapply csep_conseq with
      (Q := AsEx
              (fun c =>
                 AsMpFl lc (ANum c) **
                        AsAnd AsEmp (AsBool (ANum c == ANum 0))
              )
      ). split.
  Focus 2. split;intros σ H;eauto.
  inversion_clear H. des_ex.
  constructor. exists x0.
  inversion_clear H.
  des_ex. constructor. 
  exists x1,x2,x3,x4. repeat split;auto.
  constructor. constructor. apply H3.
  
  eapply csep_conseq. split.
  apply csep_mutate.
  split;intros σ H.
  constructor. inversion_clear H. des_ex. exists x0. auto.
  rewrite <-sepStarEmp_iff in H.
  constructor. exists 0.
  inversion_clear H. des_ex.
  constructor.  exists x0,x1,x2,x3. repeat split;auto.
  constructor. auto. constructor. auto.
  simpl. intros. auto. simpl. intros. auto.

  (* IF *)
  
  apply csep_if.
  eapply csep_conseq with
      (P := (AsEx
            (fun u : nat =>
             ((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
              AsAnd (AsBool (ANum u == AVar s))
                (AsMpFl (AVar Stack) (ANum u))) **
                                                AstarAlpha 0 n alphaEx u))). split.
  Focus 2. split;intros σ H;eauto.
  remember ((AsEx
              (fun u : nat =>
               ((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
                AsAnd (AsBool (ANum u == AVar s))
                  (AsMpFl (AVar Stack) (ANum u))) **
                                                  AstarAlpha 0 n alphaEx u))).
  inversion_clear H. auto.
  apply csep_seq with
      (Q :=
         AsEx (fun u=>
                 (γfullEx tid ** (AsAnd (AsBool (ANum u == AVar x))
                                       (AsMpFl (AVar Stack) (ANum u))))
                   ** I' tid n u )
      ).

  (* IFBTrue *)
  Focus 2.
  (* [S] := x *)


  eapply csep_conseq with
      (P := ((γfull tid (AVar t) (ANum 1) ** AstarExcludeJGamma 0 tid n γreadEx)
               ** (nToken (n-1))) **
               (AsMpFl (AVar Stack) (AVar s))
      ).
  split. Focus 2.
  split;intros σ H;eauto.
  remember (fun u : nat =>
            ((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
             AsAnd (AsBool (ANum u == AVar s))
               (AsMpFl (AVar Stack) (ANum u))) **
            AstarAlpha 0 n alphaEx u).
  inversion_clear H. des_ex.
  subst a.
  
  remember (AsAnd (AsBool (ANum x0 == AVar s))
                  (AsMpFl (AVar Stack) (ANum x0))).
  remember (AstarAlpha 0 n alphaEx x0).
  rewrite sepStarCom_iff in H.
  rewrite <-sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := (a0 ** (γread tid (AVar t) (ANum 1) ** nToken (n - 1))))
      (q1 := a);intros.

  clear H Heqa.
  rewrite <-sepStarAssoc_iff in H0.
  apply sepStarImpSt with
      (p1 := (a0 ** γread tid (AVar t) (ANum 1)))
      (q1 := nToken (n-1));intros;auto.
  subst a0.
  rewrite sepStarCom_iff in H. apply gmAlPickRdFl_iff in H.
  auto. clear H.
  subst a.
  inversion_clear H0. constructor.
  inversion_clear H. inversion_clear H1. 
  apply EqNat.beq_nat_true in H0.
  rewrite <-H0. auto. auto.

  apply csep_conseq with
      (P := (AsMpFl (AVar Stack) (AVar s) ** γfullEx tid) **
          AsEx (fun u : nat => AsAnd (I' tid n u) (AsBool (ANum u == (AVar x)))
      ))
      (Q:= AsEx
      (fun u : nat =>
       (γfullEx tid **
        AsAnd (AsBool (ANum u == AVar x))
        (AsMpFl (AVar Stack) (ANum u)))) **
      AsEx (fun u : nat => AsAnd (I' tid n u) (AsBool (ANum u == (AVar x)))
           )).
  split.
  Focus 2.
  split;intros σ H.
  rewrite sepStarAssoc_iff.
  rewrite sepStarCom_iff.
  apply sepStarImpSt with
      (p1:= ((γfull tid (AVar t) (ANum 1) **
            AstarExcludeJGamma 0 tid n γreadEx) ** 
                                                 nToken (n - 1)))
      (q1 :=AsMpFl (AVar Stack) (AVar s));auto;intros;clear H.

  rewrite sepStarAssoc_iff in H0.
  apply sepStarImpSt with
      (p1 := γfull tid (AVar t) (ANum 1))
      (q1 := (AstarExcludeJGamma 0 tid n γreadEx ** nToken (n - 1)));intros;auto;clear H0.
  inversion_clear H.
  des_ex.
  constructor. 
  exists (takeSt (takeSt σ1, x0, x2) t).
  constructor. exists 1.
  constructor.
  exists x0,x1,x2,x3.
  repeat split;auto.
  constructor. inversion_clear H2. auto.

  rewrite sepStarCom_iff in H.
  apply lemma4 with (u := aeval (takeSt σ1) (AVar x)) in H.
  constructor. exists (aeval (takeSt σ1) (AVar x)).
  constructor. auto. constructor. simpl.
  rewrite PeanoNat.Nat.eqb_eq. auto. auto.

  remember ((fun u : nat =>
             γfullEx tid **
             AsAnd (AsBool (ANum u == AVar x))
               (AsMpFl (AVar Stack) (ANum u)))).
  remember ((fun u : nat =>
               AsAnd (I' tid n u) (AsBool (ANum u == AVar x)))).
  inversion_clear H.
  des_ex.
  inversion_clear H2. inversion_clear H3.
  subst a. subst a0.
  des_ex.
  constructor.
  exists x5.
  remember (γfullEx tid **
       AsAnd (AsBool (ANum x5 == AVar x))
       (AsMpFl (AVar Stack) (ANum x5))).
  constructor.
  exists x0,x1,x2,x3.
  repeat split;auto.
  subst a.
  inversion_clear H2.
  inversion_clear H3.
  des_ex.
  unfold takeSt in *. simpl in *.
  inversion_clear H8.
  inversion_clear H5. inversion_clear H9.
  apply EqNat.beq_nat_true in H8.
  apply EqNat.beq_nat_true in H5.
  unfold takeSt in *. simpl in *.
  rewrite H5.
  rewrite H8 in H4. auto.
  apply csep_frame. split.

  eapply csep_conseq with
      (Q := AsEx
      (fun u : nat =>
       AsAnd (AsBool (ANum u == AVar x))
         (AsMpFl (AVar Stack) (ANum u))) ** γfullEx tid).
  split.
  Focus 2. split;intros σ H;eauto.
  remember ((fun u : nat =>
            AsAnd (AsBool (ANum u == AVar x))
                  (AsMpFl (AVar Stack) (ANum u)))).
  inversion_clear H.
  des_ex. constructor.
  inversion_clear H2. des_ex.
  exists x4.
  rewrite sepStarCom_iff.
  subst a.
  constructor. 
  exists x0,x1,x2,x3. repeat split;auto. 

  apply csep_frame. split.
  eapply csep_conseq.
  split. apply csep_mutate.
  split;intros σ H.
  inversion_clear H. constructor.
  exists ((takeSt σ s)). constructor. auto.
  inversion_clear H. constructor.
  exists ((takeSt σ x)). constructor. constructor.
  simpl. symmetry.
  apply EqNat.beq_nat_refl. constructor. auto.
  simpl. intros;auto.
  simpl. intros;auto.

  
  (* pushed := true *)

  apply csep_ex. intro u.
  apply csep_conseq with
      (P := AsEmp ** ((γfullEx tid ** (AsMpFl (AVar Stack) (ANum u)))
                        ** I' tid n u))
      (Q := AsOr (andEmp asnPushedTrue) (nToken n) **
                 ((γfullEx tid ** (AsMpFl (AVar Stack) (ANum u)))
                    ** I' tid n u)).
  split.
  Focus 2. split;intros σ H.
  rewrite sepStarCom_iff. rewrite sepStarEmp_iff.

  apply sepStarImpSt with
      (p1 := (γfullEx tid **
           AsAnd (AsBool (ANum u == AVar x))
           (AsMpFl (AVar Stack) (ANum u))))
      (q1 := I' tid n u);intros;auto; clear H.
  remember (γfullEx tid).
  inversion_clear H0. des_ex.
  constructor. 
  exists x0,x1,x2,x3. repeat split;auto.
  inversion_clear H3. auto.
  rewrite <-sepStarAssoc_iff in H.
  apply sepStarImpSt with
      (p1 := (AsOr (andEmp asnPushedTrue) (nToken n) **
                   (γfullEx tid ** AsMpFl (AVar Stack) (ANum u))))
      (q1 := I' tid n u);intros;auto;clear H.
  rewrite <-sepStarAssoc_iff in H0. auto.

  apply csep_frame. split.
  eapply csep_conseq. split.

  eapply csep_assign with
      (P := fun v => AsAnd AsEmp (AsBool (v == ANum 10))).
  auto.
  split;intros σ H.
  constructor;auto. constructor. auto.
  constructor.
  inversion_clear H. constructor. auto. constructor.
  inversion_clear H1. unfold takeSt in *. simpl in *. auto.
  simpl. intros. destruct H. destruct H.
  do 4 destruct H. destruct H0. subst. inversion H0. auto. auto.
  destruct H0. subst. inversion H0. auto. auto.
  destruct H;auto. destruct H0;auto. subst. inversion H0.
  assert (~ fvAsn (I' tid n u) X).
  apply I'ntInAsn;auto;try intro;try destruct H0;subst;try inversion H1.
  auto. auto. congruence.

  (* IFBFalse *)
  (* SKIP *)


  remember ((AsBool (AVar s != AVar t))) as sNeqt.
  eapply csep_conseq with
      (P := AsEx (fun u=>
                    ((AsAnd
                      (AsAnd sNeqt (γread tid (AVar t) (ANum 1)))
                      (AsBool (ANum u == AVar s))
                    ) ** nToken (n-1) **
                      (AsMpFl (AVar Stack) (ANum u))) **
                      (alphaEx tid u ** I' tid n u)
                 )
      ).
  split.
  Focus 2.
  split;intros σ H.
  assert (σ|=(AsEx
             (fun u : nat =>
               (AsAnd sNeqt
               ((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
                AsAnd (AsBool (ANum u == AVar s))
                  (AsMpFl (AVar Stack) (ANum u)))) **
                                                   AstarAlpha 0 n alphaEx u))).

  remember ((fun u : nat =>
            ((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
             AsAnd (AsBool (ANum u == AVar s))
               (AsMpFl (AVar Stack) (ANum u))) **
                                               AstarAlpha 0 n alphaEx u)).
  inversion_clear H.
  inversion_clear H0. des_ex.
  subst a.
  constructor.
  exists x0.
  remember (((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
         AsAnd (AsBool (ANum x0 == AVar s))
         (AsMpFl (AVar Stack) (ANum x0)))).
  inversion_clear H. des_ex.
  constructor.
  exists x1,x2,x3,x4.
  subst sNeqt.
  repeat split;auto.
  subst a. inversion_clear H3.
  des_ex.
  constructor.
  inversion_clear H1. constructor.
  auto.
  constructor.
  exists x5,x6,x7,x8. repeat split;auto.
  
  clear H.
  remember ((fun u : nat =>
        ((AsAnd (AsAnd sNeqt (γread tid (AVar t) (ANum 1)))
            (AsBool (ANum u == AVar s)) ** nToken (n - 1)) **
         AsMpFl (AVar Stack) (ANum u)) **
        (alphaEx tid u ** I' tid n u))).

  remember ((fun u : nat =>
             AsAnd sNeqt
               ((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
                AsAnd (AsBool (ANum u == AVar s))
                  (AsMpFl (AVar Stack) (ANum u))) **
               AstarAlpha 0 n alphaEx u)).
  inversion_clear H0.
  constructor. des_ex.

  exists x0. subst a a0.

  apply sepStarImpSt with
      (p1 := AsAnd sNeqt
            ((γread tid (AVar t) (ANum 1) ** nToken (n - 1)) **
             AsAnd (AsBool (ANum x0 == AVar s))
             (AsMpFl (AVar Stack) (ANum x0))))
      (q1 := AstarAlpha 0 n alphaEx x0);intros;auto;clear H.
  remember ((γread tid (AVar t) (ANum 1))).
  remember ((AsMpFl (AVar Stack) (ANum x0))).
  inversion_clear H0. inversion_clear H1.
  des_ex.
  inversion_clear H4.
  inversion_clear H3.
  constructor.
  exists x1,x2,x3,x4.
  repeat split;auto.
  des_ex.
  constructor.
  exists x5,x6,x7,x8.
  repeat split;auto.
  subst sNeqt.
  constructor. constructor. inversion_clear H.
  constructor. auto. auto. inversion_clear H5. constructor.
  auto.
  apply alInvSep_iff. auto. eauto.

  apply csep_ex. intro u.
  apply csep_conseq with
  (P :=
     nToken (n-1) **
            (AsAnd (AsBool ((AVar t) != ANum u)) (γread tid (AVar t) (ANum 1))
                   ** alphaEx tid u) ** (AsMpFl (AVar Stack) (ANum u) ** I' tid n u))
  (Q := (AsOr (andEmp asnPushedTrue) (nToken n) ** γfullEx tid)
          ** (AsMpFl (AVar Stack) (ANum u) ** I' tid n u)).
  split.
  Focus 2. split;intros σ H.

  remember ((AsAnd (AsAnd sNeqt (γread tid (AVar t) (ANum 1)))
                   (AsBool (ANum u == AVar s)))).
  remember (AsMpFl (AVar Stack) (ANum u)) as stk.
  remember (AsAnd (AsBool (AVar t != ANum u))
                  (γread tid (AVar t) (ANum 1))).
  rewrite sepStarCom_iff.
  rewrite sepStarAssoc_iff.
  rewrite sepStarCom_iff in H.
  rewrite <-sepStarAssoc_iff in H.
  rewrite sepStarCom_iff.
  apply sepStarImpSt with
      (p1 := ((alphaEx tid u ** I' tid n u) ** (a ** nToken (n - 1))))
      (q1 := stk);intros;auto;clear H.
  rewrite sepStarCom_iff in H0.
  rewrite <-sepStarAssoc_iff in H0.
  rewrite sepStarCom_iff.
  apply sepStarImpSt with
      (p1 := ((a ** nToken (n - 1)) ** alphaEx tid u))
      (q1 := I' tid n u);intros;auto;clear H0.
  rewrite <-sepStarAssoc_iff.
  apply sepStarImpSt with
      (p1 := a ** nToken (n - 1))
      (q1 := alphaEx tid u);intros;auto;clear H.
  rewrite sepStarCom_iff.
  apply sepStarImpSt with
      (p1 := a)
      (q1 := nToken (n-1));intros;auto;clear H0.
  subst a a0.
  remember ((γread tid (AVar t) (ANum 1))).
  subst sNeqt.
  inversion_clear H. inversion_clear H0.
  inversion_clear H. inversion_clear H1.
  constructor. constructor. 
  simpl in *.
  apply EqNat.beq_nat_true in H.
  rewrite <-H in H0.
  apply Bool.negb_true_iff in H0.
  apply Bool.negb_true_iff.
  apply EqNat.beq_nat_false in H0.
  rewrite PeanoNat.Nat.eqb_neq.
  unfold not in *.
  intros. apply H0. symmetry. auto. auto.
  rewrite sepStarAssoc_iff. auto.

  apply csep_frame. split.

  eapply csep_conseq with
      (P := nToken (n-1) ** (◇ ** γfull tid (AVar t) (ANum 1))).
  split.
  Focus 2.
  split;intros σ H;eauto.
  apply sepStarImpSt with
      (p1 := nToken (n-1))
      (q1 := (AsAnd (AsBool (AVar t != ANum u))
             (γread tid (AVar t) (ANum 1)) ** 
             alphaEx tid u));auto;clear H.
  intros.
  apply lemma5 in H. auto.
  eapply csep_conseq.
  split. apply csep_skip.
  split;intros σ H;eauto.
  rewrite <-sepStarAssoc_iff in H.

  apply sepStarImpSt with
      (p1 := (nToken (n - 1) ** ◇))
      (q1 := γfull tid (AVar t) (ANum 1))
  ;auto;clear H;clear σ.
  intros.
  rewrite sepStarCom_iff in H.
  rewrite nTokenAbs in H;auto.
  apply jdg_or_r. auto.
  intros.
  inversion_clear H. des_ex.
  constructor.
  exists (takeSt (takeSt σ, x0, x2) t).
  constructor. exists 1.
  constructor.
  inversion_clear H2. inversion_clear H3.
  exists x0,x1,x2,x3.
  repeat split;auto.
  constructor. auto. constructor. auto.
  simpl. intros. auto. simpl. intros.
  destruct H;auto;destruct H0;auto;subst;try discriminate.
  destruct H0;auto;try discriminate.
  destruct H;auto;try discriminate.
  destruct H;auto;destruct H0;auto;subst;try discriminate.
  simpl. intros.
  destruct H;auto;destruct H0;auto;subst;try discriminate.
  destruct H0;auto;try discriminate.
  destruct H;auto;try discriminate.

  split;intros σ H;auto.
  assert (σ|=(((AsMpFl (AVar x) (ANum v) **
              AsEx
                (fun u : nat =>
                 AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))) **
             AsEmp) ** 
                    γreadEx tid)).
  remember ((AsMpFl (AVar x) (ANum v) **
              AsEx
                (fun u : nat =>
                   AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)))).
  remember (γreadEx tid).
  inversion_clear H.
  inversion_clear H0. des_ex.
  inversion_clear H3.
  des_ex.
  constructor.
  des_ex. exists x0,x1,x2,x3.
  repeat split;auto.
  constructor.
  exists x4,x5,x6,x7.
  repeat split;auto.
  inversion_clear H8.
  inversion_clear H9. auto.
  apply nTokenEmp in H9.
  apply H9.
  clear H.
  remember ((fun var : nat =>
         AsMpFl (ANum var) (ANum v) **
         AsEx
         (fun u : nat => AsMpFl (APlus (ANum var) (ANum 1)) (ANum u)))).
  remember (γreadEx tid).
  constructor.
  remember (((AsMpFl (AVar x) (ANum v) **
             AsEx
               (fun u : nat =>
                  AsMpFl (APlus (AVar x) (ANum 1)) (ANum u))) ** AsEmp)).
  inversion_clear H0.
  des_ex.
  exists x0,x1,x2,x3.
  subst.
  repeat split;auto.
  rewrite sepStarAssoc_iff in H2.
  remember ((AsEx
              (fun u : nat =>
                 AsMpFl (APlus (AVar x) (ANum 1)) (ANum u)) ** AsEmp)).
  inversion_clear H2. 
  des_ex.
  unfold takeSt in *.
  constructor.
  exists ((fst (fst σ) x)).
  constructor.
  exists x4,x5,x6,x7.
  repeat split;auto.
  constructor.
  inversion_clear H6. auto.
  subst.
  rewrite <-sepStarEmp_iff.
  inversion_clear H7. des_ex.
  inversion_clear H10. des_ex. constructor.
  exists x8,x9,x10,x11.
  repeat split;auto.
  constructor. exists x12.
  constructor.
  inversion_clear H10.
  unfold takeHp,takeSt in *. simpl in *. auto.
Qed.
