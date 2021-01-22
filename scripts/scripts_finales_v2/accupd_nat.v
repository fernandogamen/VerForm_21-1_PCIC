Load braunT_nat.

(* 
- - - - - - - - - - - - - - - - - - - -
A call to lookup with index 'i' on a balanced Braun tree 't', 
that has just been updated with 'x' at same index 'i', 
returns 'x' itself
- - - - - - - - - - - - - - - - - - - -
*)
Lemma lkp_upd: forall (t:BTree) (x:A) (i:nat), bal t -> t <> E 
                                               -> i < size t -> lookup (upd t i x) i = x.
Proof.
intros t x.
(*Induction on t*)
induction t.  
(*Base case t=E *)
intuition.
(*Induction step t=N t1 t2*)
intros.
(*Cases on index*)
destruct (eq_nat_dec i 0).
(*i=0*)
rewrite e.
intuition.
(*i<>0*)
(*Cases on modulo i 2*) 
destruct (mod_0_1 i).
(* i is even, i.e., modulo i 2 = 0*)
destruct (eq_btree_dec t2 E).
(* ==> Cases on t2 <== *)
(*i) t2 = E*)
assert (t2_E:=e).
destruct (rightE_nat a t1 t2).
trivial.
(* To use rightE_nat we need to prove t2 = E *)
trivial.
(*t1=E and t2=E *)
rewrite H3 in H1.
rewrite t2_E in H1.
simpl in H1.
inversion H1.
(*Contradiction: i = 0*)
intuition.
(*Contradiction S i <= 0*)
inversion H5.
(*t1= N b E E and t2=E *)
rewrite t2_E in H1.
destruct H3.
rewrite H3 in H1.
simpl in H1.
inversion H1.
(* i = 1 *)
rewrite H5 in H2.
simpl in H2.
inversion H2.
(* i=0 *)
assert (i = 0).
intuition.
(* Contradiction i=0 *)
intuition.
(* ii) t2<>E *)
replace (upd (N a t1 t2) i x) with (N a t1 (upd t2 (div i 2 - 1) x)).
replace (lookup (N a t1 (upd t2 (i / 2 - 1) x)) i) with (lookup (upd t2 (i / 2 - 1) x) (div i 2 - 1)).
apply IHt2.
inversion H.
trivial.
trivial.
(* As required by the inductive hypothesis, we need to prove that  i / 2 - 1 < size t2 *)
apply (even_index_btree i a t1 t2).
trivial.
trivial.
trivial.
trivial.
(* We neeed to prove the replace statement: lookup (upd t2 (i / 2 - 1) x) (i / 2 - 1) = lookup (N a t1 (upd t2 (i / 2 - 1) x)) i*)
simpl.
destruct i.
intuition.
simpl in H2.
simpl (divmod (S i) 1 0 1).
rewrite H2.
intuition.
(* We need to prove the replace statement: N a t1 (upd t2 (i / 2 - 1) x) = upd (N a t1 t2) i x*)
simpl.
simpl in H2.
rewrite H2.
simpl.
apply Nat.neq_0_r in n.
destruct n.
rewrite H3.
trivial.
(* i is odd, i.e., modulo i 2 = 1*)
destruct (eq_btree_dec t1 E).
(* ==> Cases on t1 <== *)
(* i) t1 = E *)
assert (t1_E:= e).
apply (leftE_leaf_nat a t1 t2) in e.
(*t1=E and t2=E *)
rewrite e in H1.
rewrite t1_E in  H1.
simpl in H1.
inversion H1.
(*Contradiction: i = 0*)
intuition.
(*Contradiction: S i <= 0*)
inversion H4.
(* An assumption of leftE_leaf_nat is that bal(N a t1 t2) *)
trivial.
(* ii) t1<>E *)
replace (upd (N a t1 t2) i x) with (N a (upd t1 (div i 2) x) t2).
replace (lookup (N a (upd t1 (i / 2) x) t2) i) with (lookup (upd t1 (i / 2) x) (div i 2)).
apply IHt1.
inversion H.
trivial.
trivial.
(* As required by the inductive hypothesis, we need to prove that i/2 < size t1*)
apply (odd_index_btree i a t1 t2).
trivial.
trivial.
trivial.
(* We need to prove the replace statement: lookup (upd t1 (i / 2) x) (i / 2) = lookup (N a (upd t1 (i / 2) x) t2) i *)
simpl.
destruct i.
intuition.
simpl in H2.
simpl (divmod (S i) 1 0 1).
rewrite H2.
intuition.
(* We need to prove the replace statement: N a (upd t1 (i / 2) x) t2 = upd (N a t1 t2) i x *)
simpl.
simpl in H2.
rewrite H2.
apply Nat.neq_0_r in n.
destruct n.
rewrite H3.
trivial.
Qed.


(* We lookup an element in a Braun tree *)
(*Eval compute in lookup (N 1 (N 2 (N 4 E E) (N 5 E E)) (N 3 (N 6 E E) E)) 3.*)


Lemma equiv_lookup : forall (t:BTree), bal t -> bbal t -> t<>E -> forall (i:nat), i < size t -> lookup_bn t (toBN i) = lookup t i.
Proof.
intro.
(* Induction on t *)
induction t.
(* Base case t= E *)
intuition.
(* Induction step t = N t1 t2*)
intros.
(* Cases on i *)
destruct (eq_nat_dec i 0).
(* i=0 *)
rewrite e.
simpl.
trivial.
(* i<>0 *)
(* Cases on modulo i 2 *)
destruct (mod_0_1 i).
(* i is even, i.e., modulo i 2 = 0 *)
destruct (eq_btree_dec t2 E).
(*Cases on t2*)
(*1) t2=E A*)
assert (t2_E:=e).
apply (rightE_nat a t1 t2) in e.
destruct e.
(*t1=E and t2=E *)
rewrite H4 in H2.
rewrite t2_E in H2.
simpl in H2.
inversion H2.
(*Contradiction: i=0*)
intuition.
(*Contradiction S i <= 0*)
inversion H6.
(*t1= N b E E and t2=E *)
rewrite t2_E in H2.
destruct H4.
rewrite H4 in H2.
simpl in H2.
inversion H2.
(* i=1 *)
rewrite H4.
rewrite t2_E.
reflexivity.
(* i=0 *)
assert (i = 0).
intuition.
(* Contradiction i=0 *)
intuition.
trivial.
(*2) t<>E *)
assert (iEven:=H3).
assert (iEven2:=H3).
assert (iEven3:=H3).
apply parity_nat_bn in H3.
rewrite H3.
simpl in iEven.
simpl.
rewrite iEven.
simpl.
(* Cases on i *)
destruct i.
(* i = 0, contradiction! *)
intuition.
(* i = S n *)
apply IHt2.
inversion H.
trivial.
inversion H0.
trivial.
trivial.
apply mod_i in iEven2.
destruct (bal_size_r a t1 t2).
trivial.
(* Case 1: size (N a t1 t2) = 2 * size t2 + 1 *)
rewrite H4 in H2.
apply lt_solve in H2.
rewrite iEven2 in H2.
trivial.
lia.
(* Case 2: size (N A a t1 t2) = 2 * size t2 + 2 *)
rewrite H4 in H2.
inversion H2.
(* S i = 2*size t2 + 1 *)
assert (S i = S(2*size t2)).
lia.
rewrite H5 in iEven3.
assert (modulo (S (2 * size t2)) 2 = 1).
apply even_odd_mod.
rewrite H7 in iEven3.
intuition.
(* S i < 2*size t2 + 1 *)
assert (S i < 2 * size t2 + 1).
lia.
apply lt_solve in H7.
rewrite iEven2 in H7.
trivial.
lia.
trivial.
(* i is odd, i.e., modulo i 2 = 1 *)
destruct (eq_btree_dec t1 E).
(*Cases on t1*)
(* 1) t=E *)
assert (t1_E:=e).
apply (leftE_leaf_nat a t1 t2) in e.
(*t1=E A and t2=E *)
rewrite e in H2.
rewrite t1_E in H2.
simpl in H2.
inversion H2.
(*Contradiction: i<>0*)
intuition.
(*Contradiction: S i <= 0*)
inversion H5.
trivial.
(* 2) t1<>E *)
assert (iOdd:=H3).
assert (iOdd2:=H3).
apply parity_nat_bn in H3.
rewrite H3.
simpl in iOdd.
simpl.
rewrite iOdd.
simpl.
destruct i.
(* i=0, contradiction! *)
intuition.
(* i = S n *)
apply IHt1.
inversion H.
trivial.
inversion H0.
trivial.
trivial.
apply mod_i in iOdd2.
apply (bal_size_l a t1 t2) in H.
(* S i < 2*size t1 + 1 *)
assert (S i <  2 * size t1 + 1).
lia.
apply lt_solve in H4.
rewrite iOdd2 in H4.
trivial.
lia.
Qed.


Lemma equiv_update : forall (t:BTree), bal t -> bbal t -> t<>E -> forall (i:nat), i < size t -> forall (a:A), update t (toBN i) a = upd t i a.
Proof. 
intro.
(* Induction on t *)
induction t.
(* Base case t= E *)
intuition.
(* Induction step t = N t1 t2*)
intros.
(* Cases on index *)
destruct (eq_nat_dec i 0).
(* i = 0 *)
rewrite e.
simpl.
trivial.
(* i <> 0 *)
destruct (mod_0_1 i).
(* Cases on modulo i 2 *)
(* i is even, i.e., modulo i 2 = 0 *)
destruct (eq_btree_dec t2 E).
(*Cases on t2*)
(*1) t2=E A*)
assert (t2_E:=e).
apply (rightE_nat a t1 t2) in e.
destruct e.
(*t1=E A and t2=E A*)
rewrite H4 in H2.
rewrite t2_E in H2.
simpl in H2.
inversion H2.
(*Contradiction: i=0*)
intuition.
(*Contradiction S i <= 0*)
inversion H6.
(*t1= N A aa (E A) (E A) and t2=E A*)
rewrite t2_E in H2.
destruct H4.
rewrite H4 in H2.
simpl in H2.
inversion H2.
(* i=1 *)
rewrite H4.
rewrite t2_E.
reflexivity.
(* i=0 *)
assert (i = 0).
intuition.
(* Contradiction i=0 *)
intuition.
trivial.
(*2) t<>E *)
assert (iEven:=H3).
assert (iEven2:=H3).
assert (iEven3:=H3).
apply parity_nat_bn in H3.
rewrite H3.
simpl in iEven.
simpl.
rewrite iEven.
simpl.
(* Cases on i *)
destruct i.
(* i = 0, contradiction! *)
intuition.
(* i = S n *)
rewrite IHt2.
trivial.
inversion H.
trivial.
inversion H0.
trivial.
trivial.
apply mod_i in iEven2.
destruct (bal_size_r a t1 t2).
trivial.
(* Case 1: size (N A a t1 t2) = 2 * size t2 + 1 *)
rewrite H4 in H2.
apply lt_solve in H2.
rewrite iEven2 in H2.
trivial.
lia.
(* Case 2: size (N A a t1 t2) = 2 * size t2 + 2 *)
rewrite H4 in H2.
inversion H2.
(* S i = 2*size t2 + 1 *)
assert (S i = S(2*size t2)).
lia.
rewrite H5 in iEven3.
assert (modulo (S (2 * size t2)) 2 = 1).
apply even_odd_mod.
rewrite H7 in iEven3.
intuition.
(* S i < 2*size t2 + 1 *)
assert (S i < 2 * size t2 + 1).
lia.
apply lt_solve in H7.
rewrite iEven2 in H7.
trivial.
lia.
trivial.
(* i is odd, i.e., modulo i 2 = 1 *)
destruct (eq_btree_dec t1 E).
(*Cases on t1*)
(* 1) t=E *)
assert (t1_E:=e).
apply (leftE_leaf_nat a t1 t2) in e.
(*t1=E A and t2=E *)
rewrite e in H2.
rewrite t1_E in H2.
simpl in H2.
inversion H2.
(*Contradiction: i<>0*)
intuition.
(*Contradiction: S i <= 0*)
inversion H5.
trivial.
(* 2) t1<>E *)
assert (iOdd:=H3).
assert (iOdd2:=H3).
apply parity_nat_bn in H3.
rewrite H3.
simpl in iOdd.
simpl.
rewrite iOdd.
simpl.
destruct i.
(* i=0, contradiction! *)
intuition.
(* i = S n *)
rewrite IHt1.
trivial.
inversion H.
trivial.
inversion H0.
trivial.
trivial.
apply mod_i in iOdd2.
apply (bal_size_l a t1 t2) in H.
(* S i < 2*size t1 + 1 *)
assert (S i <  2 * size t1 + 1).
lia.
apply lt_solve in H4.
rewrite iOdd2 in H4.
trivial.
lia.
Qed.


