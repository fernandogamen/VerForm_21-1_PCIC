(* Verificación Formal 2021-I PCIC UNAM
   Dr. Favio E. Miranda Perea.
   Script 1.
   Razonamiento con listas 1: propiedades de take y drop
 *)

(* Listas polimórficas predefinidas *)

Check list.

Print list.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).


Fixpoint app {A:Type} (l1 l2:list A):list A :=
 match l1 with
  |nil => l2
  |h :: t => h :: (app t l2)
 end.

Notation "x ++ y" := (app  x y)
                     (right associativity, at level 60).



Section TakeDrop.

Variable A:Type.

Fixpoint take (n:nat) (l:list A) :=
 match n,l with
  | 0, l => nil
  | S n, nil => nil
  | S n, cons h t => cons h (take n t)
 end.

Fixpoint drop (n:nat) (l:list A) :=
 match n,l with
  | 0, l => l
  | S n, nil => nil
  | S n, cons h t => drop n t
 end.



Proposition td1: forall n l, l = take n l ++ drop n l.
Proof.
intro.
induction n.
- simpl.
  reflexivity.
- intros.
  destruct l.
  + simpl.
    reflexivity.
  + simpl.    
    rewrite <- IHn.
    reflexivity.
Qed.

Lemma dropn_taken_nil: forall n l, drop n (take n l) = [ ].
Proof.
intro.
induction n.
- intro.
  simpl.
  reflexivity.
- intro.
  destruct l.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHn.
    reflexivity.
Qed.       

Proposition td2: forall m n l, take m (drop n l) = drop n (take (m+n) l).
Proof.
intro.
induction m.
- intros.
  simpl.
  rewrite dropn_taken_nil.
  reflexivity.
- intro.
  induction n.
  + rewrite <- plus_n_O.
    reflexivity.
  + replace (S m + S n) with (S (S m+ n)).
    -- destruct l.
       * simpl.
         reflexivity.
       * change (take (S (S m + n)) (a :: l)) with
                (a:: take (S m + n) l).     
         change (drop (S n) (a :: l)) with (drop n l).
         change (drop (S n) (a :: take (S m + n) l)) with 
                (drop n (take (S m + n) l)).
         exact (IHn l). (* apply IHn *)
    -- admit.
Admitted.

Proposition td4: forall m n l, drop m (drop n l) = drop (m+n) l.
Proof.
intro.
induction m.
- simpl. 
  reflexivity.
- (* intro. *)
  induction n.
  + rewrite <- plus_n_O.
    reflexivity.
  + replace (S m + S n) with (S(S m + n)).
    2: admit.
    (* intro. *)
    destruct l.
    * simpl.
      reflexivity.
    * change (drop (S n) (a :: l)) with (drop n l).
      change (drop (S(S m + n)) (a :: l)) with (drop (S m + n) l).
      rewrite IHn.
      reflexivity.
Admitted.      

Check td4.


End TakeDrop.

Check td4.
