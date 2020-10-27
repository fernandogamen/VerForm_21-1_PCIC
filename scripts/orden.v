Require Import Coq.Program.Equality.

(* Orden suave definición 1 directa *)
Inductive ord1: nat -> nat -> Prop :=
  o1refl:  forall n, ord1 n n
 |o1suc: forall n m, ord1 n m -> ord1 n (S m).

Notation "x <=1 y" := (ord1 x y) (at level 60).

(* Orden estricto definición 1 como azucar sintáctica del orden suave  *)

Definition orde1 n m := ord1 (S n) m.

Notation "x <1 y" := (orde1 x y) (at level 60).


(* Orden estricto definicion 2 directa *)

Inductive ord2: nat -> nat -> Prop :=
  o2z:  forall n, ord2 0 (S n)
 |o2suc:  forall n m, ord2 n m -> ord2 (S n) (S m).

Notation "x <2 y" := (ord2 x y) (at level 60).

(* Orden suave definicion 2 como azucar sintactica del orden estricto *)

Definition ords2 n m := ord2 n m \/ n = m.

Notation "x <=2 y" := (ords2 x y) (at level 60).


Simulacion de las reglas del orden 2 en el 
Lemma sim_oe1_o2z: forall n, 0 <1 S n.
Proof.
intros.
unfold orde1.
induction n.
- constructor.
- constructor.
  assumption.
Qed.

Lemma oe1_nSn: forall n, n <1 S n.
Proof.
intros.
unfold orde1.
constructor.
Qed.

Lemma sim_oe1_o2suc: forall n m, n <1 m -> S n <1 S m.
Proof.
intros.
induction H.
- apply oe1_nSn.
- constructor.
  unfold orde1 in IHord1.
  assumption.
Qed.

Lemma sim_o1_o2refl: forall n m, n = m -> n <=1 m.
Proof.
intros.
rewrite H.
constructor.
Qed.  


Lemma o1_trans_swap: forall n m, n <=1 m -> forall p, p <=1 n -> 
                               p <=1 m.
Proof.
intros n m H.
induction H.
- intuition.
- intros.
  constructor.
  apply IHord1.
  assumption.
Qed.

Lemma o1_trans: forall n m p, p <=1 n -> n <=1 m -> 
                               p <=1 m.
Proof.
intros.
eapply o1_trans_swap.
exact H0.
assumption.
Qed.

Lemma sim_oe1_o2es: forall n m, n <1 m -> n <=1 m.
Proof.
intros.
unfold orde1 in H.
eapply o1_trans_swap.
exact H.
constructor.
constructor.
Qed.
  

Lemma os2_refl: forall n, n <=2 n.
Proof.
intros.
unfold ords2.
right. 
reflexivity.
Qed.

Lemma o2_antirefl: forall n, ~ n <2 n.
Admitted.

Lemma o2_Sn_not_n: forall n, ~ S n <2 n.
Proof.
intros.
unfold not.
intro.
induction n.
- inversion H.
- apply IHn.
  inversion H.
  assumption.
Qed.  

Lemma o2_nSn: forall n, n <2 S n.
Proof.
intros.
induction n.
- constructor.
- constructor.
  assumption.
Qed.

Lemma sim_os2_o1s: forall n m, n <=2 m -> n <=2 S m.
Proof.
intros.
unfold ords2 in H.
destruct H.
- induction H.
 * unfold ords2.
   left.
   constructor.
 * unfold ords2.
   left.
   constructor.
   unfold ords2 in IHord2.
   destruct IHord2.
   + assumption.
   + rewrite <- H0.
     rewrite H0 in H.
     contradict H.
     apply o2_Sn_not_n.
- rewrite H.
  left.
  apply o2_nSn.
Qed.  
        
     

Lemma o2_trans: forall n m, n <2 m -> forall p, m <2 p -> n <2 p.
Proof.
intros n m H.
induction H.
- intros.
  destruct p.
  + inversion H.
  + constructor.
- intros.
  destruct p.
  * inversion H0.
  * constructor.
    apply IHord2.
    inversion H0.
    assumption.
Qed.  


Lemma sim_o1_o2z: forall n, 0 <=1 n.
Proof.
intros.
induction n.
- constructor.
- constructor.
  assumption.
Qed.

Lemma o1_nSn: forall n, n <=1 S n.
Proof.
intros.
constructor.
constructor.
Qed.


  
Lemma o1_ss_equiv: forall n m, n <=1 m <-> S n <=1 S m.
Proof.
intros.
split.
+ intro.
  induction H.
  - constructor.
  - constructor.
    assumption.
+ intro.
  destruct n.
  - apply sim_o1_o2z.
  - inversion H.
    * constructor.
    * eapply o1_trans.
      apply o1_nSn.
      exact H2.
Qed.   

Lemma sim_o1_o2s: forall n m, n <=1 m -> S n <=1 S m.
Proof.
intros.
induction H.
- constructor.
- constructor.
  exact IHord1. 
Qed.

Proposition equiv_o1_os2: forall n m, n <=1 m <-> n <=2 m.
Proof.
intros.
split.
+ intro. induction H.
- apply os2_refl.
- destruct IHord1.
 * unfold ords2.
   left.
   eapply o2_trans. 
   eassumption.
   apply o2_nSn.
 * rewrite H0.
   unfold ords2.
   left. 
   apply o2_nSn.
+ intro.
  unfold ords2 in H.
  destruct H.
  * induction H.
    - apply sim_o1_o2z.
    - apply sim_o1_o2s.
      assumption.
  * rewrite H. 
    constructor.  
Qed.


Lemma os2_ss_equiv: forall n m, n <=2 m <-> S n <=2 S m.
Proof.
intros.
split.
- intros.
  apply equiv_ords1_ords2.
  apply equiv_ords1_ords2 in H.
  apply ords1_ss in H.
  assumption.
- intros.
  apply equiv_ords1_ords2.
  apply equiv_ords1_ords2 in H.
  apply ords1_ss in H.
  assumption.   
Qed.



Proposition equiv_oe1_o2: forall n m, n <1 m <-> n <2 m.
Proof.
intros.
split.
- intro. unfold orde1 in H.
  destruct n.
  * destruct m.
    + inversion H.
    + constructor. 
  * apply equiv_ords1_ords2 in H.
    unfold ords2 in H.
    destruct H.
    + eapply orde2_trans.
      apply orde2_nSn.
      assumption.
    + rewrite <- H.
      apply orde2_nSn.  
- intro.
  unfold orde1.
  induction H.
  + destruct n.
    * constructor.
    * constructor.
      apply ords1_ss.
      apply ord1_zn.
  + apply ords1_ss.
    assumption.
Qed.



   
Lemma o2_ss_equiv: forall n m, S n <2 S m <-> n <2 m.
Proof.
intros.
split.
- intro.
  dependent induction H.
  assumption.
- intro.
  induction H.
  + constructor.
    constructor.
  + constructor.
    assumption.
Qed.

      
Lemma oe1_ss_equiv: forall n m, S n <1 S m <-> n <1 m.
Proof.
intros.
split.
- intros.
  unfold orde1.
  unfold orde1 in H.
  apply equiv_orde1_orde2.
  apply equiv_orde1_orde2 in H.  
  apply orde2_ss.
  assumption.
- intros.
  unfold orde1.
  unfold orde1 in H.
  apply equiv_orde1_orde2.
  apply equiv_orde1_orde2 in H.  
  apply orde2_ss.
  assumption.
Qed.    


Check min.

Lemma min_eq: forall n, min n n = n.
Proof.
induction n.
- reflexivity.
- simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma min_SS: forall n m, min (S n) (S m) = S (min n m).
Proof.
intro.
induction n.
- intro.
  simpl.
  reflexivity.
- intro.
  destruct m.
  + simpl.
    reflexivity.
  + simpl.
    reflexivity.       
Qed.


Lemma min_s: forall n m, n <2 m -> min (S n) m = S( min n m).
Proof.
intros.
induction H.
- simpl.
  reflexivity.
- destruct m.
  + inversion H.
  + change (Nat.min (S (S n)) (S (S m))) with 
            (S (Nat.min (S n) (S m))).
    rewrite IHord2.
    rewrite min_SS.
    reflexivity.
Qed.    
      



Proposition min_lt_l: forall n m, n <=1 m -> min n m = n.
Proof.
intros.
induction H.
- apply min_eq.
- destruct n.
  + reflexivity.
  + simpl.
    rewrite <- min_s.
    rewrite IHord1.
    reflexivity.
    admit.
Admitted.        


Lemma min_comm: forall n m, min n m = min m n.
Proof.
intro.
induction n.
- simpl.
  destruct m.
  + reflexivity.
  + reflexivity.
- intros.
  destruct m.
  + reflexivity.
  + simpl.
    rewrite IHn.
    reflexivity.
Qed.      
  

Proposition min_lt_r: forall n m, m <=1 n -> min n m = m.
Proof.
intros.
rewrite min_comm.
apply min_lt_l.
assumption.
Qed.






