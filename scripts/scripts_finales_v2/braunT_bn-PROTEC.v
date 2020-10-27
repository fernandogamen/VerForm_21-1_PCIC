Load orderbn.
Load binary_tree.

(* Function size on binary trees defined next*)
Fixpoint bsize (t:BTree): BN :=
 match t with
  E => Z
 |N x s t =>  sucBN ((bsize s) ⊞ (bsize t))
 end.

Check bsize.



Lemma bsize_Z: forall (t:BTree), bsize t = Z -> t = E.
Proof.
intros t0.
destruct t0.
trivial.
intros.
simpl in H.
symmetry in H.
contradict H.
apply ZnotSucBN.
Qed.



Lemma bsize_nonZ: forall (t:BTree), t <> E -> bsize t <> Z.
Proof.
intros.
contradict H.
apply bsize_Z.
trivial.
Qed.



(* Balance condition on Braun trees *)
Inductive bbal : BTree -> Prop:= 
 |bbalE : bbal E 
 |bbalN : forall (a: A) (s t: BTree), bbal s -> bbal t -> (bsize t) ≤BN (bsize s) -> (bsize s) ≤BN (sucBN (bsize t)) -> 
                                      bbal (N a s t).

Check bbal_ind.



Parameter (allBal: forall (t:BTree), bbal t).

          

Theorem bbal_size_l: forall (a:A) (t1 t2:BTree), (bsize (N a t1 t2)) ≤BN (U (bsize t1)). 
Proof.
intros a t1 t2.
assert (HBal := allBal (N a t1 t2)).
inversion HBal.
simpl.
inversion H4.
rewrite H8.
assert ((sucBN ((bsize t1) ⊞ (bsize t1))) = U (bsize t1)).
apply plus_U.
rewrite H7.
apply lteqBN_refl.
inversion H5.
assert (sucBN ((bsize t1) ⊞ (bsize t2)) = ((bsize t1) ⊞ (sucBN (bsize t2)))).
apply plusSuc_2.
rewrite H10.
rewrite <- H11.
assert (sucBN ((bsize t1) ⊞ (bsize t1)) = U (bsize t1)).
apply plus_U.
rewrite <- H12.
apply lteqs.
assert (exists (b:BN), (bsize t2) <BN b /\ b <BN (sucBN (bsize t2)) ).
exists (bsize t1).
split.
trivial.
trivial.
contradict H12.
apply not_lt_suc.
Qed.



Lemma lt_U_bsize: forall (b:BN) (a:A) (t1 t2:BTree), (U b) <BN (bsize (N a t1 t2)) -> b <BN (bsize t1).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) ≤BN (U (bsize t1))).
apply bbal_size_l.
assert ((U b) <BN (U (bsize t1))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.



Theorem rightE: forall (a:A) (t1 t2:BTree), bbal(N a t1 t2) -> t2 = E -> (t1 = E \/ exists (aa:A), t1 = (N aa E E)).
Proof.
intros a t1 t2 HBal H.
inversion HBal.
rewrite H in H5.
simpl in H5.
inversion H5.
assert (bsize t1 = Z).
intuition.
apply bsize_Z in H8.
left.
trivial.
rewrite H in H6.
simpl in H6.
inversion H6.
destruct t1.
left; trivial.
simpl in H12.
replace (U Z) with (sucBN Z) in H12.
apply SucBNinj in H12.
apply plusBN_Z_Z in H12.
destruct H12.
apply bsize_Z in H11.
apply bsize_Z in H12.
right.
exists a3.
rewrite H11.
rewrite H12.
trivial.
simpl.
trivial.
inversion H10.
assert (bsize t1 = Z).
rewrite H14; trivial.
apply bsize_Z in H13.
left.
trivial.
inversion H15.
inversion H15.
Qed.



Theorem bbal_size_r: forall (a:A) (t1 t2:BTree), bsize (N a t1 t2) = U (bsize t2) \/ bsize (N a t1 t2) = D (bsize t2).
Proof.
intros a t1 t2.
assert (HBal:=allBal (N a t1 t2)).
inversion HBal.
inversion H4.
clear H H0 H1 H6 a1.
simpl.
rewrite H8.
rewrite plus_U.
left;trivial.
clear H H0 H1 H7 H8.
inversion H5.
clear H a1 a2 b.
simpl.
rewrite H1.
rewrite plus_D.
right;trivial.
exfalso.
eapply not_lt_suc.
exists (bsize t1).
split.
eexact H6.
exact H.
Qed.



Theorem bbal_size_r2: forall (a:A) (t1 t2:BTree), (bsize (N a t1 t2)) ≤BN (D (bsize t2)). 
Proof.
intros a t1 t2.
assert (bsize (N a t1 t2) = U (bsize t2) \/ bsize (N a t1 t2) = D (bsize t2)).
apply bbal_size_r.
destruct H.
constructor.
rewrite H.
constructor.
rewrite H.
constructor.
Qed.



Lemma lt_D_bsize: forall (b:BN) (a:A) (t1 t2:BTree), (D b) <BN (bsize (N a t1 t2)) -> b <BN (bsize t2).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) ≤BN (D (bsize t2))).
apply bbal_size_r2.
assert ((D b) <BN (D (bsize t2))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.



Lemma bbal_leaf: forall (a:A), bbal (N a E E).
Proof.
intro a.
constructor.
constructor.
constructor.
apply lteqBN_refl. (* cambié _sym por _refl aquí, en orderbn.v y en extensions.v  C.V. *)
apply lteqs.
Qed.



Theorem leftE_leaf: forall (t1 t2:BTree) (a:A), bbal (N a t1 t2) -> t1 = E -> t2 = E.
Proof.
intros t1 t2 c HBal H.
inversion HBal.
rewrite H in H5.
simpl in H5.
inversion H5.
apply bsize_Z in H9.
trivial.
inversion H7.
Qed.



Lemma bbal_inv: forall (t:BTree), t <> E ->  
                          (exists (z:A), t = N z E E)  \/ 
                           exists (z:A) (r1 r2:BTree), bbal r1 /\ bbal r2 /\ r1 <> E /\ t = N z r1 r2.
Proof.
intros.
assert (tBal := allBal t).
inversion tBal.
rewrite H0 in H.
intuition.
destruct (eq_btree_dec s E).
rewrite e.
rewrite e in H0.
cut (t0 = E). (* propiedad leaf... arriba *)
intros.
rewrite H5.
left;exists a;trivial.
eapply leftE_leaf.
rewrite <- H4 in tBal.
eexact tBal.
trivial.
right.
exists a.
exists s.
exists t0.
intuition.
Qed.



Theorem size_caseU: forall (w:A) (t1 t2:BTree) (b:BN), bsize (N w t1 t2) = U b -> bsize t1 = bsize t2.
Proof.
intros.
assert (HBal := allBal (N w t1 t2)).
inversion HBal.
inversion H5.
trivial.
inversion H6.
simpl in H.
rewrite H12 in H.
rewrite plus_D in H.
inversion H.
exfalso.
eapply not_lt_suc.
exists (bsize t1).
split.
eexact H7.
exact H10.
Qed.



Theorem size_caseD: forall (w:A) (t1 t2:BTree) (b:BN), bsize (N w t1 t2) = D b -> bsize t1 = sucBN (bsize t2).
Proof.
intros.
assert ( HBal := allBal (N w t1 t2)).
inversion HBal.
simpl in H.
inversion H5.
rewrite H9 in H.
rewrite plus_U in H.
inversion H.
inversion H6.
trivial.
exfalso.
eapply not_lt_suc.
exists (bsize t1).
split.
eexact H7.
exact H10.
Qed.



Lemma tnonE: forall (t:BTree), t <> E -> exists w r1 r2, t = N w r1 r2.
Proof.
intros.
assert (tBal:=allBal t).
apply bbal_inv in H.
destruct H.
destruct H.
exists x.
exists E.
exists E.
trivial.
destruct H.
destruct H.
destruct H.
exists x.
exists x0.
exists x1.
intuition.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - -
Property 0 of Hoogerwood's paper:
bal <a,s,t> /\ #<a,s,t>=d+1 -> #s = d 'div' 2 + d 'mod' 2 /\ #t = d 'div' 2
- - - - - - - - - - - - - - - - - - - - - - - - - - *)
Lemma prop_0_U : forall (a:A) (s t:BTree) (b:BN), bbal (N a s t) -> bsize(N a s t) = U b -> bsize s = b /\ bsize t = b.
Proof.
intros.
assert (U_size:=H0).
apply size_caseU in U_size.
simpl in H0.
rewrite U_size in H0.
rewrite plus_U in H0.
apply UInj in H0.
rewrite H0 in U_size.
split.
trivial.
trivial.
Qed.

Lemma prop_0_D : forall (a:A) (s t:BTree) (b:BN), bbal (N a s t) -> bsize(N a s t) = D b -> bsize s = sucBN b /\ bsize t = b.
Proof.
intros.
assert (D_size:=H0).
apply size_caseD in D_size.
simpl in H0.
rewrite D_size in H0.
rewrite plus_D in H0.
apply DInj in H0.
rewrite H0 in D_size.
split.
trivial.
trivial.
Qed.
