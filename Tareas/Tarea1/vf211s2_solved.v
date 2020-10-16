(* Verificación Formal 2021-I PCIC UNAM
   Dr. Favio E. Miranda Perea.
   Script 2.
   Dos definiciones de orden en naturales
 *)

Require Import Utf8.

(* Orden suave definición 1 directa *)
Inductive ord1: nat -> nat -> Prop :=
| o1refl:  forall n, ord1 n n
| o1suc: forall n m, ord1 n m -> ord1 n (S m).

Notation "x <=1 y" := (ord1 x y) (at level 60).

(* Orden estricto definición 1 como azucar sintáctica del orden suave  *)

Definition orde1 n m := ord1 (S n) m.

Notation "x <1 y" := (orde1 x y) (at level 60).

(* Orden estricto definicion 2 directa *)

Inductive ord2: nat -> nat -> Prop :=
| o2z:  forall n, ord2 0 (S n)
| o2suc:  forall n m, ord2 n m -> ord2 (S n) (S m).

Notation "x <2 y" := (ord2 x y) (at level 60).

(* Orden suave definicion 2 como azucar sintactica del orden estricto *)

Definition ords2 n m := ord2 n m \/ n = m.

Notation "x <=2 y" := (ords2 x y) (at level 60).

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


Lemma o1_nSn: forall n, n <=1 S n.
Proof.
intros.
constructor.
constructor.
Qed.


Lemma o1_trans: forall n m p, p <=1 n -> n <=1 m -> 
                               p <=1 m.
Proof.
intros.
induction H0.
- assumption.
- constructor.
  apply IHord1.
  assumption.
Qed.

Lemma sim_oe1_o2sdef: forall n m, n <1 m -> n <=1 m.
Proof.
intros.
unfold orde1 in H.
eapply o1_trans.
apply o1_nSn.
assumption.
Qed.
  

Lemma sim_os2_o1refl: forall n, n <=2 n.
Proof.
intros.
unfold ords2.
right. 
reflexivity.
Qed.

 

Lemma o2_nSn: forall n, n <2 S n.
Proof.
intros.
induction n.
- constructor.
- constructor.
  assumption.
Qed.


Lemma o2_antirefl: forall n, ~ n <2 n.
Proof.
unfold not.
induction n.
intros.
- inversion H.
- intros.
  apply IHn.
  inversion H.
  assumption.
Qed.

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
  inversion H.
  constructor.
- intros.
  inversion H0.
  constructor.
  apply IHord2.
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

Proposition equiv_o1_os2: forall n m, n <=1 m <-> n <=2 m.
Proof.
intros.
split.
+ intro. induction H.
- apply sim_os2_o1refl.
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
    - apply o1_ss_equiv in IHord2.
      assumption.
  * rewrite H. 
    constructor.  
Qed.

Lemma os2_ss_equiv: forall n m, n <=2 m <-> S n <=2 S m.
Proof.
intros.
split.
- intros.
  apply equiv_o1_os2.
  apply equiv_o1_os2 in H.
  apply o1_ss_equiv in H.
  assumption.
- intros.
  apply equiv_o1_os2.
  apply equiv_o1_os2 in H.
  apply o1_ss_equiv in H.
  assumption.   
Qed.

Proposition equiv_oe1_o2: forall n m, n <1 m <-> n <2 m.
Proof.
unfold iff.
split.
- intros.
  unfold orde1 in H.
  apply equiv_o1_os2 in H.
  destruct H.
  + inversion H.
    apply o2_trans with m0.
    * assumption.
    * apply o2_nSn.
  + induction m.
    * inversion H.
    * inversion H.
      apply o2_nSn.
- intros.
  revert H.
  revert n.
  revert m.
  induction m.
  + intros.
    inversion H.
  + intros.
    induction n.
    * apply sim_oe1_o2z.
    * apply sim_oe1_o2suc.
      unfold orde1 in *.
      apply IHm.
      inversion H.
      assumption.
Qed.

Lemma o2_ss_equiv: forall n m, S n <2 S m <-> n <2 m.
Proof.
unfold iff.
split.
- intros.
  inversion H.
  assumption.
- intros.
  constructor.
  assumption.
Qed.

Lemma oe1_ss_equiv: forall n m, S n <1 S m <-> n <1 m.
Proof.
unfold iff.
split.
- intros.
  unfold orde1 in *.
  apply equiv_o1_os2 in H.
  apply equiv_o1_os2.
  destruct H.
  + unfold ords2.
    left.
    destruct m.
    * inversion H.
      inversion H2.
    * inversion H.
      assumption.
  + unfold ords2.
    right.
    inversion H.
    reflexivity.
- intros.
  apply sim_oe1_o2suc.
  assumption.
Qed.

Proposition o2_sb : forall n m, 
{n <2 m} + {~(n <2 m)}.
Proof.
induction n.
- destruct m.
  + right.
    unfold not;intros.
    inversion H.
  + left.
    constructor.
- induction m.
  + right.
    unfold not;intros.
    inversion H.
  + destruct IHm.
    * destruct IHn with m.
      -- left.
         constructor.
         assumption.
      -- right.
         unfold not;intros.
         apply n0.
         inversion H.
         assumption.
    * destruct IHn with m.
      -- left.
         constructor.
         assumption.
      -- right.
         unfold not;intros.
         apply n1.
         inversion H.
         assumption.
Qed.

Definition min (n m:nat) : nat :=
if (o2_sb n m) then n else m.

Example ex1 : min 0 3 = 0.
Proof.
unfold min.
destruct o2_sb.
- reflexivity.
- unfold not in n.
  exfalso.
  apply n.
  constructor.
Qed.

Proposition ex3a: forall n m, n <=2 m -> min n m = n.
Proof.
intros.
destruct H.
- induction H.
  + unfold min.
    destruct o2_sb.
    * reflexivity.
    * exfalso.
      apply n0.
      constructor.
  + unfold min.
    destruct o2_sb.
    * reflexivity.
    * exfalso.
      apply n0.
      constructor.
      assumption.
- rewrite H.
  unfold min.
  destruct o2_sb.
  + reflexivity.
  + reflexivity.
Qed.

Proposition ex3b : forall m n, m <=2 n -> min n m = m.
Proof.
intros.
destruct H.
- unfold min.
  destruct o2_sb.
  + induction H.
    * inversion o.
    * inversion o.
      apply IHord2 in H2.
      rewrite H2.
      reflexivity.
  + reflexivity.
- unfold min.
  destruct o2_sb.
  + symmetry.
    assumption.
  + reflexivity.
Qed.

Require Import PeanoNat.

Proposition ex3c : forall n m, n <=2 (n + m).
Proof.
induction n.
- intros.
  apply equiv_o1_os2.
  simpl.
  apply sim_o1_o2z.
- intros.
  destruct IHn with m.
  + unfold ords2.
    left.
    simpl.
    constructor.
    assumption.
  + unfold ords2.
    right.
    simpl.
    rewrite <- H.
    reflexivity.
Qed.

Proposition ex3d : forall m n, m <=2 (n + m).
Proof.
induction m.
- intros.
  apply equiv_o1_os2.
  rewrite Nat.add_0_r.
  apply sim_o1_o2z.
- intros.
  destruct IHm with n.
  + unfold ords2.
    left.
    rewrite Nat.add_succ_r.
    constructor.
    assumption.
  + unfold ords2.
    right.
    rewrite Nat.add_succ_r.
    rewrite <- H.
    reflexivity.
Qed.

Proposition ex3e : forall p n m, n <=2 m ->
n + p <=2 m + p.
Proof.
induction p.
- intros.
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r.
  assumption.
- intros.
  rewrite Nat.add_succ_r.
  rewrite Nat.add_succ_r.
  apply IHp in H.
  destruct H.
  + unfold ords2.
    left.
    constructor.
    assumption.
  + unfold ords2.
    right.
    rewrite H.
    reflexivity.
Qed.

Proposition ex3f: forall n m, n <=2 m \/ m <=2 n.
Proof.
induction n.
- intros.
  left.
  apply equiv_o1_os2.
  apply sim_o1_o2z.
- destruct m.
  + right.
    apply equiv_o1_os2.
    apply sim_o1_o2z.
  + destruct IHn with m.
    * destruct H.
      -- left.
         unfold ords2.
         left.
         constructor.
         assumption.
      -- left.
         rewrite H.
         unfold ords2.
         right.
         reflexivity.
    * destruct H.
      -- right.
         unfold ords2.
         left.
         constructor.
         assumption.
      -- right.
         rewrite H.
         unfold ords2.
         right.
         reflexivity.
Qed.

Proposition ex3g : forall n m, n <=2 m -> exists p, m = n + p.
Proof.
intros.
destruct H.
- induction H.
  + exists (S n).
    reflexivity.
  + destruct IHord2.
    exists x.
    simpl.
    rewrite <- H0.
    reflexivity.
- exists 0.
  rewrite Nat.add_0_r.
  symmetry.
  assumption.
Qed.

Require Import List.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Variable A : Type.

Fixpoint take (n:nat) (l:list A) : list A :=
match l with
| [] => []
| (x::xs) => match n with
| 0 => []
| 1 => [x]
| S n => x::take n xs
end
end.

Proposition takeSN : forall l n x, take (S n) (x::l) = x :: take n l.
Proof.
destruct l.
- simpl.
  intros.
  destruct n.
  + reflexivity.
  + reflexivity.
- intros.
  simpl.
  destruct n.
  + reflexivity.
  + reflexivity.
Qed.

Proposition Smin: forall n m, min (S n) (S m) = S (min n m).
Proof.
intros.
unfold min.
destruct o2_sb.
- destruct o2_sb.
  + reflexivity.
  + exfalso.
    apply n0.
    inversion o.
    assumption.
- destruct o2_sb.
  + exfalso.
    apply n0.
    constructor.
    assumption.
  + reflexivity.
Qed.

Proposition ex4 : forall m n l, 
take n (take m l) = take (min n m) l.
Proof.
induction m.
- intros.
  simpl.
  destruct l.
  + unfold min.
    destruct o2_sb.
    * reflexivity.
    * simpl.
      destruct n.
      -- reflexivity.
      -- reflexivity.
  + unfold min.
    destruct o2_sb.
    * destruct n.
      -- reflexivity.
      -- inversion o.
    * simpl.
      destruct n.
      -- reflexivity.
      -- reflexivity.
- intros.
  destruct l.
  + simpl.
    unfold min.
    destruct o2_sb.
    * reflexivity.
    * simpl.
      destruct n.
      -- reflexivity.
      -- reflexivity.
  + rewrite takeSN.
    induction n.
    -- simpl.
       unfold min.
       destruct o2_sb.
       ++ reflexivity.
       ++ exfalso.
          apply n.
          constructor.
    -- rewrite takeSN.
       rewrite IHm.
       rewrite Smin.
       rewrite takeSN.
       reflexivity.
Qed.