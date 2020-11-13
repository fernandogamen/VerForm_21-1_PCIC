Require Import Coq.Lists.List.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
 

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).


Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Check exp_match_ind.  
  
Example reg_exp_ex2 : [1, 2] =~ App (Char 1) (Char 2).
Proof.
apply (MApp [1]).
- apply MChar.
- apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1, 2] =~ Char 1).
Proof.
intros H.
inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1, 2, 3] =~ reg_exp_of_list [1, 2, 3].
Admitted.

Lemma MStar1 :
  forall T s (re : reg_exp T),
    s =~ re ->
    s =~ Star re.
Proof.
intros T s re H.
rewrite <- (app_nil_r s).
constructor.
- assumption.
- constructor.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  (* FILL IN HERE *) 
intros T s H.
inversion H.  
Qed.
  
Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  (* FILL IN HERE *)
intros T s re1 re2 H.
destruct H.
- constructor.
  assumption.
- constructor 5.  (*constructor FAILS, we choose the 5th constructor *)
  assumption.    
Qed.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
   match l1 with
     | nil => l2
     | cons h t => cons h (app t l2)
   end.  
   
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  (* FILL IN HERE *) Admitted.   
   

Fixpoint fold {X Y: Type} (f: X -> Y -> Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
  

Definition app' {X : Type} (l1 l2 : list X)
             : (list X) := l1 ++ l2.
  
Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app' ss [] =~ Star re.
Proof.  (* FILL IN HERE *)
intros T ss re HIn.
induction ss.
- simpl.
  constructor.
- simpl.
  constructor.
  * apply HIn.
    apply in_eq.
  * apply IHss.
    intros.
    apply HIn.
    apply in_cons.
    assumption.
Qed.         

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Admitted.


     
Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
   s =~ re ->
   In x s ->
   In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.
  simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    inversion Hin.
  - (* MStarApp *)
    simpl.
    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.  

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  (* FILL IN HERE *) Admitted.
  


Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1 H2.
(*    inversion H1.
  - simpl. auto.
  - intro. 
    constructor.
 *) 
(*  generalize s2.  *) 
 generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
   - (* MEmpty *)
    simpl. intros s2 H. apply H.
   - (* MChar. *) intros s2 H. simpl. (* Stuck... *)
Abort.     
  
Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
intros T s1 s2 re re' H H1 H2.
induction H1.
- simpl. assumption.
- inversion H.
- inversion H.
- inversion H.
- inversion H.
- simpl.
  assumption.
- rewrite <- app_assoc.
  constructor.
  + inversion H. 
    rewrite <- H1.
    assumption.
  + exact (IHexp_match2 H).   
    
  Abort.
  
Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1. (* H2. *)
  remember (Star re) as re'.  
  (* generalize s2. clear s2. *)
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) (* discriminate. *) inversion Heqre'.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.      
 - (* MStar0 *) 
    (* injection Heqre' *)
    injection Heqre' as Heqre''. 
    intros s H. apply H.
  - (* MStarApp *)
    (* inversion Heqre'. *)
    injection Heqre' as Heqre''.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + (* rewrite <- H0. apply Hmatch1. *)  apply Hmatch1.
    +  apply IH2.
      * (* assumption. *) rewrite Heqre''. reflexivity.
      * apply H1.  (* apply H1. *)  
Qed.       
    
Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app' ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  (* FILL IN HERE *) 
intros T s re H.
(* induction H.
- exists [].
  simpl.
  tauto.
- exists [[x]].
  simpl.
inversion H.
 *)
remember (Star re) as re'.
induction H.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- injection Heqre' as Heqre'.
  exists [].
  simpl.
  tauto.
- assert(K:=Heqre').
  apply IHexp_match2 in Heqre'.
  destruct Heqre' as [ss2 Heqre''].
  injection K as K.
  exists ([s1] ++ ss2).
  split.
  + simpl.
  destruct Heqre''.
  rewrite H1.
  reflexivity.
  + intros.
    apply in_app_or in H1.
    destruct H1.
    inversion H1.
    * rewrite <- K.
      rewrite <- H2.
      assumption.
    * inversion H2.
    * destruct Heqre''.
      apply H3.
      assumption.  
Qed. 
 

   
Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.
  
Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Admitted.  
  
Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  inversion Hp1 as [Hp1'| p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.     
    
Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.    

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Admitted.
  
Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Admitted.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  (* FILL IN HERE *) Admitted.
    
Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  (* FILL IN HERE *) Admitted.


End Pumping.    
      

    
  