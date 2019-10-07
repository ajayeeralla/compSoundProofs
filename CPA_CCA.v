Load "DH_AUTH".
  
(******dec of encryption is plaintext****)

Axiom dep_enc :  forall(n:nat) (x z :message), (dec (enc x (pk n) z) (sk n)) # x.



(********************************check if (r n) occurs**************************************)
(******************************* return TRUE if (r n) occurs, FALSE otherwise***************)

Eval compute in (r 1).
Fixpoint  rn_occ_bol (n:nat) (t:Bool) : bool :=
 match t with 
| Bvar n' =>  false
| FAlse =>  false
| TRue => false
| EQ_B  b1 b2 =>  (orb (rn_occ_bol n b1)  (rn_occ_bol n b2))
| EQ_M t1 t2 => orb (rn_occ_msg n t1) (rn_occ_msg n t2)
|if_then_else_B t1 t2 t3 => orb (rn_occ_bol n t1)(orb (rn_occ_bol n t2)(rn_occ_bol n t3) )
| EQL t1 t2 => orb (rn_occ_msg n t1) (rn_occ_msg n t2)
| ver t1 t2 t3 => (orb  (orb (rn_occ_msg n t1) (rn_occ_msg n t2)) (rn_occ_msg n t3))
 end
with rn_occ_msg (n:nat) (t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => orb (rn_occ_bol n b3) (orb (rn_occ_msg n  t1)(rn_occ_msg n t2))
| (Mvar n') =>  false
| O => false
| acc =>  false
| N n'=> false
|new =>  false
|exp t1 t2 t3 => orb (rn_occ_msg n t1) (orb ( rn_occ_msg  n t2) (rn_occ_msg n t3))
| pair t1 t2 => orb ( rn_occ_msg n t1) ( rn_occ_msg n t2)
| pi1 t1 => ( rn_occ_msg n t1)
| pi2 t1 =>  ( rn_occ_msg n t1)
| ggen t1 => ( rn_occ_msg n t1)
| act t1 => ( rn_occ_msg n t1)
| (rr t1 ) => (rn_occ_msg n t1)
| rs t1 =>  match t1 with 
               | (N n') => if (beq_nat n' n) then true else false
               | _ => (rn_occ_msg n t1)
              end
| L t1 => (rn_occ_msg n t1)
| m t1 => (rn_occ_msg n t1)
|enc t1 t2 t3 =>  orb ( rn_occ_msg n t1) (orb ( rn_occ_msg n t2) ( rn_occ_msg n t3))
|dec t1 t2 => orb (rn_occ_msg n t1) (rn_occ_msg n t2)
| k t1 => (rn_occ_msg n t1)
| nonce t1 => (rn_occ_msg n t1)
 | to t1 => (rn_occ_msg n t1) 
| reveal t1 => (rn_occ_msg n t1)
| sign t1 t2 => (orb (rn_occ_msg n t1) (rn_occ_msg n t2))
| i n' => false
| f  l => (@existsb message (rn_occ_msg n) l)
end.


Eval compute in rn_occ_msg 1 ((rs (N 2))  ).


(*********In a term os*****************************)

Definition rn_occ_os (n:nat)(t:oursum): bool :=
match t with 
|bol b =>rn_occ_bol n b 
|msg t =>rn_occ_msg n t
end.
(*
(**** In a message list: ilist message n********)

Fixpoint rn_occ_mlist {m:nat}(x:nat) (ml : ilist message m):bool :=
match ml with
| [] => true
| h :: ml1 => (orb (rn_occ_msg x h) (rn_occ_mlist x ml1))
end.

(*******In a Bool list:  ilist Bool n************)

Fixpoint rn_occ_blist {m:nat}(x:nat) (ml : ilist Bool m):bool :=
match ml with
| [] => true
| h :: ml1 => (orb (rn_occ_bol x h) (rn_occ_blist x ml1))
end.
*)
(********In a mylist : mylist n********)

Fixpoint rn_occ_mylist {m:nat}(x:nat) (ml :  mylist m):bool :=
match ml with
| [] => false
| h :: ml1 => (orb (rn_occ_os x h) (rn_occ_mylist x ml1))
end.
(****************************************************************************************)
(********************returns TRUE if a term sk(n) occur, FALSE otherwise *********)

(*********************In a term : message and Bool********)
Fixpoint  skn_occ_bol (n:nat) (t:Bool) : bool :=
 match t with 
| Bvar n' =>  false
| FAlse =>  false
| TRue => false
| EQ_B  b1 b2 =>  (orb (skn_occ_bol n b1)  (skn_occ_bol n b2))
| EQ_M t1 t2 => orb (skn_occ_msg n t1) (skn_occ_msg n t2)
|if_then_else_B t1 t2 t3 => orb (skn_occ_bol n t1)(orb (skn_occ_bol n t2)(skn_occ_bol n t3) )
| EQL t1 t2 => orb (skn_occ_msg n t1) (skn_occ_msg n t2)
| ver t1 t2 t3 => (orb  (orb (skn_occ_msg n t1) (skn_occ_msg n t2)) (skn_occ_msg n t3))
 end
with skn_occ_msg (n:nat) (t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => orb (skn_occ_bol n b3) (orb (skn_occ_msg n  t1)(skn_occ_msg n t2))
| (Mvar n') =>  false
| O => false
| acc =>  false
| N n'=> false
|new =>  false
|exp t1 t2 t3 => orb (skn_occ_msg n t1) (orb ( skn_occ_msg  n t2) (skn_occ_msg n t3))
| pair t1 t2 => orb ( skn_occ_msg n t1) ( skn_occ_msg n t2)
| pi1 t1 => ( skn_occ_msg n t1)
| pi2 t1 => match t1 with 
             | k (N n') => if (beq_nat n' n) then true else false
             | _ => false
               end
| ggen t1 => ( skn_occ_msg n t1)
| act t1 => ( skn_occ_msg n t1)
| rr n' => false
| rs t1 => (skn_occ_msg n t1)
| L t1 => (skn_occ_msg n t1)
| m t1 => (skn_occ_msg n t1)
|enc t1 t2 t3 =>  orb ( skn_occ_msg n t1) (orb ( skn_occ_msg n t2) ( skn_occ_msg n t3))
|dec t1 t2 => orb (skn_occ_msg n t1) (skn_occ_msg n t2)
| k t1 => (skn_occ_msg n t1)
| nonce t1 => (skn_occ_msg n t1)
 | to t1 => (skn_occ_msg n t1) 
| reveal t1 => (skn_occ_msg n t1)
| sign t1 t2 => (orb (skn_occ_msg n t1) (skn_occ_msg n t2))
| i n' => false
| f  l => (@existsb message (skn_occ_msg n) l)
end.


Eval compute in skn_occ_msg 1 ((pi2(k (N 1)))  ).


(*********In a term os*****************************)

Definition skn_occ_os (n:nat)(t:oursum): bool :=
match t with 
|bol b =>skn_occ_bol n b 
|msg t =>skn_occ_msg n t
end.
(*
(**** In a message list: ilist message n********)

Fixpoint skn_occ_mlist {m:nat}(x:nat) (ml : ilist message m):bool :=
match ml with
| [] => true
| h :: ml1 => (orb (skn_occ_msg x h) (skn_occ_mlist x ml1))
end.

(*******In a Bool list:  ilist Bool n************)

Fixpoint skn_occ_blist {m:nat}(x:nat) (ml : ilist Bool m):bool :=
match ml with
| [] => true
| h :: ml1 => (orb (skn_occ_bol x h) (skn_occ_blist x ml1))
end.
*)
(********In a mylist : mylist n********)

Fixpoint skn_occ_mylist {m:nat}(x:nat) (ml :  mylist m):bool :=
match ml with
| [] => true
| h :: ml1 => (orb (skn_occ_os x h) (skn_occ_mylist x ml1))
end.

(********* returns TRUE if skn occurs only as dec(_, (sk n))  FALSE otherwise *********)

(*********************In a term : message and Bool********)

Fixpoint  skn_in_dec_bol (n : nat )(t:Bool) : bool :=
 match t with 
| Bvar n' => true
| FAlse => true
| TRue => true
| EQ_B  b1 b2 =>  (andb ( skn_in_dec_bol n b1)  (skn_in_dec_bol n b2))
| EQ_M t1 t2 => andb (skn_in_dec_msg n t1) ( skn_in_dec_msg n t2)
| if_then_else_B t1 t2 t3 => andb ( skn_in_dec_bol n t1)  (andb (skn_in_dec_bol n t2)(skn_in_dec_bol n t3) )
| EQL t1 t2 => andb (skn_in_dec_msg n t1) ( skn_in_dec_msg n t2)
| ver t1 t2 t3 => (andb  (andb (skn_in_dec_msg n t1) (skn_in_dec_msg n t2)) (skn_in_dec_msg n t3))
 end
with skn_in_dec_msg (n : nat )(t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => andb (skn_in_dec_bol n b3) (andb ( skn_in_dec_msg n  t1)(skn_in_dec_msg n t2))
| (Mvar n') =>  if (beq_nat n' n) then false else true
| O => true
| acc => true
| N n'=> true
|new => true
| exp t1 t2 t3 => andb ( skn_in_dec_msg n t1) (andb (  skn_in_dec_msg  n t2) ( skn_in_dec_msg n t3))
| pair t1 t2 => andb (  skn_in_dec_msg n t1) (  skn_in_dec_msg n t2)
| pi1 t1 => (  skn_in_dec_msg n t1)
| pi2 t1 => match t1 with 
             | k t2 => match t2 with
                       | N n' => if (beq_nat n' n) then false else true
                       | _ => true
                         end
             | _ => true

               end

| ggen t1 => (  skn_in_dec_msg n t1)
| act t1 => (  skn_in_dec_msg n t1)
| rr n' =>  true
| rs t1 => ( skn_in_dec_msg n t1)
| L t1 => ( skn_in_dec_msg n t1)
| m t1 => ( skn_in_dec_msg n t1)
|enc t1 t2 t3 =>  andb (  skn_in_dec_msg n t1) (andb (  skn_in_dec_msg n t2) (  skn_in_dec_msg n t3))
|dec t1 t2 => match t2 with 
             | (pi2 (k (N n'))) => if (beq_nat n' n) then (andb true (skn_in_dec_msg n t1))  else true
             | t2' => (skn_in_dec_msg n t1)
              end
| k t1 => (skn_in_dec_msg n t1)
| nonce t1 => (skn_in_dec_msg n t1)
| to t1 => (skn_in_dec_msg n t1) 
| reveal t1 => ( skn_in_dec_msg n t1)
| sign t1 t2 => (andb ( skn_in_dec_msg n t1) ( skn_in_dec_msg n t2))
| i n' => true
| f  l => (@forallb message (skn_in_dec_msg n) l)
end.


(*******************************************)

Eval compute in skn_in_dec_msg 1 (k(N 1)).
Eval compute in skn_in_dec_msg 1 (dec (pi2(k (N 2))) O ).

Eval compute in skn_in_dec_msg 1 (r  2).
(*********In a term os*****************************)

Definition skn_in_dec_os (n:nat)(t:oursum): bool :=
match t with 
|bol b => skn_in_dec_bol n b 
|msg t => skn_in_dec_msg n t
end.
(*
(**** In a message list: ilist message n********)

Fixpoint skn_in_dec_mlist {m:nat}(x:nat) (ml : ilist message m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (skn_in_dec_msg x h) (skn_in_dec_mlist x ml1))
end.

(*******In a Bool list:  ilist Bool n************)

Fixpoint skn_in_dec_blist {m:nat}(x:nat) (ml : ilist Bool m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (skn_in_dec_bol x h) (skn_in_dec_blist x ml1))
end.
*)
(********In a mylist : mylist n********)

Fixpoint skn_in_dec_mylist {m:nat}(x:nat) (ml :  mylist m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (skn_in_dec_os x h) (skn_in_dec_mylist x ml1))
end.



(***********************************************)
(*******************************************)




(********return TRUE if the term dec(t , sk(n)) occurs, FALSE otherwise *********)

(*********************In a term : message and Bool********)

Fixpoint  dect_skn_bol (n:nat) (t:message)(k:Bool) : bool :=
 match k with 
| Bvar n' =>  false
| FAlse => false
| TRue => false
| EQ_B  b1 b2 =>  (orb ( dect_skn_bol n t b1)  (dect_skn_bol n t b2))
| EQ_M t1 t2 => orb (dect_skn_msg n t t1) ( dect_skn_msg n t t2)
| if_then_else_B t1 t2 t3 => orb ( dect_skn_bol n t t1)  (orb (dect_skn_bol n t t2)(dect_skn_bol n t t3) )
| EQL t1 t2 => orb (dect_skn_msg n t t1) ( dect_skn_msg n t t2)
| ver t1 t2 t3 => (orb  (orb (dect_skn_msg n t t1) (dect_skn_msg n t t2)) (dect_skn_msg n t t3))
 end
with dect_skn_msg (n:nat) (t:message) (k:message) : bool :=
 match k with 
| if_then_else_M b3 t1 t2 => orb (dect_skn_bol n t b3) (orb ( dect_skn_msg n t  t1)(dect_skn_msg n t t2))
| (Mvar n') =>  false
| O =>  false
| acc =>  false
| N n'=>  false
|new => false
| exp t1 t2 t3 => orb ( dect_skn_msg n t t1) (orb (  dect_skn_msg  n t t2) ( dect_skn_msg n t t3))
| pair t1 t2 => orb (  dect_skn_msg n t t1) (  dect_skn_msg n t t2)
| pi1 t1 => (  dect_skn_msg n t t1)
| pi2 t1 => (dect_skn_msg n t t1)
| ggen t1 => (  dect_skn_msg n t t1)
| act t1 => (  dect_skn_msg n t t1)
| rr n' => false
| rs t1 => ( dect_skn_msg n t t1)
| L t1 => ( dect_skn_msg n t t1)
| m t1 => ( dect_skn_msg n  t t1)
|enc t1 t2 t3 =>  orb (  dect_skn_msg n t t1) (orb (  dect_skn_msg n t t2) (  dect_skn_msg n t t3))
|dec t1 t2 =>  match (check_eq_msg t1 t) , t2  with
              | true , pi2(k (N n')) => if (beq_nat n' n) then true else false
              | _ , _ => false
            
                   end
                           
| k t1 => (dect_skn_msg n t t1)
| nonce t1 => (dect_skn_msg n t t1)
 | to t1 => (dect_skn_msg n t t1) 
| reveal t1 => ( dect_skn_msg n t t1)
| sign t1 t2 => (orb ( dect_skn_msg n t t1) ( dect_skn_msg n t t2))
| i n' => false
| f  l => (@existsb message (dect_skn_msg n t) l)

end.



(***********************************************)
(*******************************************)


Eval compute in dect_skn_msg 1 O (dec (f [O;O]) (pi2 (k (N 1)))).

(*********In a term os*****************************)

Definition  dect_skn_os (n:nat)(t:message)(k:oursum): bool :=
match k with 
|bol b => dect_skn_bol n t b 
|msg t1 => dect_skn_msg n t t1
end.

(**** In a message list: ilist message n********)

Fixpoint dect_skn_mlist (x:nat) (t:message) (ml : list message):bool :=
match ml with
| nil  => true
| cons h tl => (orb (dect_skn_msg x t h) (dect_skn_mlist x  t tl ))
end.

(*******In a Bool list:  ilist Bool n************)

Fixpoint dect_skn_blist (x:nat) (t:message)(ml : list Bool ):bool :=
match ml with
| nil => true
| cons h tl => (orb (dect_skn_bol x t h) (dect_skn_blist x t tl))
end.

(********In a mylist : mylist n********)

Fixpoint dect_skn_mylist {m:nat}(x:nat)(t:message) (ml :  mylist m):bool :=
match ml with
| [] => true
| h :: ml1 => (orb (dect_skn_os x t h) (dect_skn_mylist x t ml1))
end.

(********return TRUE if n occur only as (k n) FALSE otherwise *********)

(*********************In a term : message and Bool********)

Fixpoint  n_kn_bol (n:nat) (k:Bool) : bool :=
 match k with 
| Bvar n' =>  if (beq_nat n' n) then false else true 
| FAlse => true
| TRue => true
| EQ_B  b1 b2 =>  (andb ( n_kn_bol n  b1)  (n_kn_bol n  b2))
| EQ_M t1 t2 => (andb (n_kn_msg n  t1) ( n_kn_msg n  t2))
| if_then_else_B t1 t2 t3 => andb ( n_kn_bol n  t1)  (andb (n_kn_bol n  t2)(n_kn_bol n  t3) )
| EQL t1 t2 => andb (n_kn_msg n  t1) ( n_kn_msg n  t2)
| ver t1 t2 t3 => (andb  (andb (n_kn_msg n  t1) (n_kn_msg n  t2)) (n_kn_msg n  t3))
 end
with n_kn_msg (n:nat)  (k:message) : bool :=
 match k with 
| if_then_else_M b3 t1 t2 => andb (n_kn_bol n b3) (andb ( n_kn_msg n  t1)(n_kn_msg n t2))
| (Mvar n') => if (beq_nat n' n) then false else true
| O =>  true 
| acc =>  true 
| N n'=>  true
|new =>  true
| exp t1 t2 t3 => andb ( n_kn_msg n  t1) (andb (  n_kn_msg  n  t2) ( n_kn_msg n  t3))
| pair t1 t2 => andb (  n_kn_msg n  t1) (  n_kn_msg n  t2)
| pi1 t1 => (  n_kn_msg n  t1)
| pi2 t1 => (n_kn_msg n  t1)
| ggen t1 => (  n_kn_msg n  t1)
| act t1 => (  n_kn_msg n  t1)
| rr t1 => match t1 with 
            | N n' =>  if (beq_nat n' n) then false else true 
            | _ => (n_kn_msg n t1)
             end
| rs t1 => ( n_kn_msg n  t1)
| L t1 => ( n_kn_msg n  t1)
| m t1 => ( n_kn_msg n   t1)
|enc t1 t2 t3 =>  orb (  n_kn_msg n  t1) (orb (  n_kn_msg n  t2) (  n_kn_msg n  t3))
|dec t1 t2 => (orb (n_kn_msg n t1) (n_kn_msg n t2))                                    
| k t1 => (n_kn_msg n  t1)
| nonce t1 => (n_kn_msg n  t1)
 | to t1 => (n_kn_msg n  t1) 
| reveal t1 => ( n_kn_msg n  t1)
| sign t1 t2 => (orb ( n_kn_msg n  t1) ( n_kn_msg n  t2))
| i n' => if (beq_nat n' n) then false else true
| f  l => (@forallb message (n_kn_msg n ) l)

end.



(***********************************************)
(*******************************************)


Eval compute in n_kn_msg 1  (dec (f [O;O]) (pi2 (k (N 1)))).

(*********In a term os*****************************)

Definition  n_kn_os (n:nat)(k:oursum): bool :=
match k with 
|bol b => n_kn_bol n  b 
|msg t1 => n_kn_msg n t1
end.
(*
(**** In a message list: ilist message n********)

Fixpoint n_kn_mlist (x:nat) (t:message) (ml : list message):bool :=
match ml with
| nil  => true
| cons h tl => (orb (n_kn_msg x t h) (n_kn_mlist x  t tl ))
end.

(*******In a Bool list:  ilist Bool n************)

Fixpoint n_kn_blist (x:nat) (t:message)(ml : list Bool ):bool :=
match ml with
| nil => true
| cons h tl => (orb (n_kn_bol x t h) (n_kn_blist x t tl))
end.
*)
(********In a mylist : mylist n********)

Fixpoint n_kn_mylist {m:nat}(x:nat) (ml :  mylist m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (n_kn_os x  h) (n_kn_mylist x  ml1))
end.





(********************ENCCPA*******************************************)
(*********************************************************************)
Eval compute in r.

Axiom ENCCPA: forall (u u' u'': message) (n n1 n2 n3 :nat){m} (l:mylist m), ( (var_free_mylist n l) = true) /\ (clos_listm [u; u'; u''] = true) /\ ((rn_occ_mylist n2 l) = false) /\ ((rn_occ_mylist n3 l) = false)/\ (( skn_in_dec_mylist n1 l) = true) /\  (skn_occ_mylist n1  ((submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (rs (N n2))) u'') l) ++
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (rs (N n3))) u'') l)) = false)  -> (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (rs (N n2))) u'') l) ~
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (rs (N n3))) u'') l).


(********************ENCCCA1*****************************************)
(********************************************************************)

Axiom ENCCCA1 : forall (t u u' u'': message) (n n1 n2 n3 :nat){m} (l :mylist m), (var_free_msg n t = true) /\ (var_free_mylist n l = true) /\ (clos_listm [u; u'; u''] = true) /\ ((rn_occ_mylist n2 l) = false) /\ ((rn_occ_mylist n3 l) = false)/\ (( skn_in_dec_mylist n1 l) = true)  /\ (dect_skn_mlist n1 t  (subtrmls_mylist  l ) = false) -> (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (rs (N n2))) u'') l) ~
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (rs (N n3))) u'') l).
(**********************ENCCCA2*************************************)
(******************************************************************)
(**((rn_occ_mylist n2 l) = false) /\ ((rn_occ_mylist n3 l) = false)  /\ (( skn_in_dec_mylist n1 l) = true) /\ ((dect_skn_mlist n1 t  (subtrmls_mylist  l ) = true) ->  exists t'', (var_free_msg n t'' = true) /\ (dec t (sk n1)) # (if_then_else_M (EQ_M t (Mvar n)) & (EQ_M (L u) (L u')) t'' (dec t (sk n1))))**)

Eval compute in occmsg_in_msg (dec O (sk 1)) (if_then_else_M (EQ_M O (Mvar 1)) & (EQ_M (L O) (L O)) O (dec O (sk 1))).
Fixpoint sup_trm  (t:message) {n}  (l':mylist n)  : list message :=
match l'  with 
| [] => nil
| h :: tl =>
             if (occmsg_in_msg t (ostomsg h)) then (cons (ostomsg h) (sup_trm t  tl )) else (sup_trm t  tl )
end.

Eval compute in sup_trm O   [msg O; msg ( O); msg O ; msg (N 1)].

Fixpoint trm_listm (t:message) (l:list message): bool :=
match l with 
| nil => true
| cons h tl => (andb (occmsg_in_msg t h) (trm_listm t tl))
end.

Axiom ENCCCA2 : forall (t t'' t''' u u' u'': message) (n n1 n2 n3 :nat){m} (l :mylist m), (var_free_mylist n ([msg t ; msg t''] ++ l) = true) /\ (clos_listm [u; u'; u''] = true) /\ ( (dect_skn_mlist n1 t  (subtrmls_mylist  l ) = true) -> ((occmsg_in_msg t t''') = true) /\ (trm_listm (if_then_else_M (EQ_M t (Mvar n)) (* (EQ_M (L u) (L u'))*) t'' t''') (sup_trm (dec t (sk n1)) l) = true)) /\ (rn_occ_mylist n2 l = false) /\ (rn_occ_mylist n3 l = false) -> (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (rs (N n2))) u'') l) ~
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u' (pk n1) (rs (N n3))) u'') l).
(*
(*********************ENCCA2***************************************)
(******************************************************************)
Abort All.
Section comp.
Variable m n r :nat.
Variable u u' t' t'' :message.
Variable l : list message.
Variable comp: nat-> nat -> message -> message -> message -> message  -> message -> bool.
Fixpoint check_comp (l:list message) : bool :=
match l with
| nil => true
| cons h t => (andb (comp m n u u' t' t'' h) (check_comp t))
end. 
End comp.
Check check_comp.


Fixpoint nuu'cca2 (m n:nat) ( u u'  t' t'' t :message) : bool  :=
match (var_free_msg m t)  with
| true =>  match (clos_msg t) with 
           | true => (check_eq_msg t (N n))
           | false => match (check_eq_msg t (pk n)) with 
                       | true =>  true
                       | false => match (check_eq_msg t (Mvar m)) with 
                                  | true => true
                                  | false => match t  with 
                                               | f l => match  (@check_comp m n u u' t' t'' nuu'cca2 l) with
                                                                  | true =>  (var_free_msg m t') && (negb (check_eq_msg t (dec t' (pi2 (k (N n)))))) 
                                                                             
                                                                   | false =>  false
                                                                   end
                                               | _ =>       match (var_free_mylist  m  [msg t'; msg t'']) with 
                                                            | true =>                                                       

 match t with
| (if_then_else_M b t5 t''') => match b with
                                  | (if_then_else_B b1 b2 FAlse) => match (check_eq_bol b1 (EQ_M t' (Mvar n))) with 
                                                                    |  true =>  
                                                                        match b2 with 
                                                                          | (EQ_M (L u) (L u')) => (check_eq_msg t''' (dec t' (pi2 (k (N n)))))  && (check_eq_msg t5 t'') && (nuu'cca2 m n u u' t' t'' t5) 
                                                                                                            
       | _                         => false 
end

| false => false
 
end

|  _ => false

end

| _  => false
end
| _ => false


end
end
end
end
end
| false => false
end.
       
(*************check if every element of list is nuu' compliant****************************)

Fixpoint list_nuu'  {s} (m n:nat) (u u'  t' t'' :message) (l: mylist s) : bool :=
match l with
| [] => true
| h :: t => (andb (match h with
             | msg t1 =>  (nuu'cca2 m n u u'  t' t'' t1)
             | _ => true
               end) (list_nuu' m n u u'  t' t'' t))
end.


Axiom ENCCCA2: forall (t' t'' u u' u'': message) (n n1 n2 n3 m :nat) (l:mylist m),  (var_free_mylist m ([msg t'; msg t''] ++ l) = true) /\  ((notocc_dec_mlist n1 t'  (subterm_list_mylist  l ) = false) ->  (dec t' (sk n1)) # (if_then_else_M  ((EQ_M t'  (Mvar 2))& (EQ_M (L u) (L u'))) t'' (dec t' (sk n1)))) -> ((list_nuu' m n u u' t' t'' l) = true) ->
 (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n2)) u'') l) ~
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n3)) u'') l). *)
(*****nonce and key generation ******)
Variable lnonce : message.
Axiom ln: forall n, lnonce # (L (N n)).
(**Definition lskey {n} := (L (sk n)).**)




(*******length regular********)

Axiom len_regular: forall (x1 x2 y1 y2 :message), (L x1) # (L y1) /\ (L x2) # (L y2) -> (L (pair x1 x2)) # (L (pair y1 y2)).

(******Idempotent L(L(x)) = L(x)**********)

Axiom idemp_L: forall x,  (L (L x)) # (L x).
Variable lskey : message.

Axiom lsk: forall n, lskey # (L (sk n)). 

(**************real or random secrecy of n****)



(** ( Fresh [n;n';n1; n2; n3; n4;n5; n6; n7] [] = true)**)

Theorem RRS_n: forall (n n' n1 n2 n3 n4 n5 n6 n7 :nat),  beq_nat n4 n3 = false /\   beq_nat n1 n = false /\
 beq_nat n2 n = false /\   beq_nat n3 n = false /\   beq_nat n4 n = false /\
  beq_nat n5 n = false /\   beq_nat n6 n = false /\ beq_nat n7 n = false /\    beq_nat n1 n' = false /\   beq_nat n2 n' = false /\    beq_nat n3 n' = false /\    beq_nat n4 n' = false /\    beq_nat n5 n' = false /\    beq_nat n6 n' = false /\
  beq_nat n7 n' = false ->
 [ msg (enc (pair (sk  n1) (N n5)) (pk n2) (rs (N (n3)))); msg (enc (pair (pi2 (dec (f [ (enc (pair (sk  n1) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n)] ~
 [ msg (enc (pair (sk  n1) (N n5)) (pk n2) (rs (N (n3)))); msg (enc (pair (pi2 (dec (f [ (enc (pair (sk  n1) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n')].


Proof. intros .
(******************************************************************************************)
assert(tfx: (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]) # (if_then_else_M (EQ_M (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))])  (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))) (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]) (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]))).

rewrite IFSAME_M with (b:=  (EQ_M (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))])  (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3)))))) (x:= (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))])). 
reflexivity.

assert (tdecfx:  (pi2 (dec (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))) # (if_then_else_M  (EQ_M (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))])  (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))) (N n5)  (pi2 (dec (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))))).

rewrite tfx at 1.

pose proof(Example11_M).
apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))])) in H0. simpl in H0.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (enc (pair (sk n1) ( N n5 )) (pk n2) (rs (N n3))) ) in H0. simpl in H0.
apply  Forall_ELM_EVAL_M1 with (n:=3) (x :=  (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))])) in H0. simpl in H0.
 
rewrite H0 .


assert(H3:  (pi2 (dec (if_then_else_M (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk n2))) # (if_then_else_M (Bvar 0) (pi2 (dec (Mvar 1) (sk n2))) (pi2 (dec (Mvar 2) (sk n2))))).


rewrite <- IFSAME_M with (b:= (Bvar 0)) (x:=  (pi2 (dec (if_then_else_M (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk n2)))).

rewrite IFEVAL_M .
simpl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
reflexivity.
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))]) (enc (pair (pi2 (k (N n1))) (N n5)) (pi1 (k (N n2))) (rs (N n3))))) in H3.
simpl in H3.
apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (enc (pair (pi2 (k (N n1))) (N n5)) (pi1 (k (N n2))) (rs (N n3)))) in H3. simpl in H3.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (f [enc (pair (sk n1)  (N n5)) (pk n2) (rs (N n3))])) in H3. simpl in H3.

rewrite H3.
pose proof(dep_enc).
rewrite dep_enc with (n:=n2) (x:=  (pair (pi2 (k (N n1))) (N n5 ))) .
rewrite proj2 with (m1:= (pi2 (k (N n1)))) (m2 := (N n5)) .
reflexivity.

(************************************************************************************************)
assert(ufx: (f [ (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))]) # (if_then_else_M (EQ_M (f [ (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))])  (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))) (f [ (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))]) (f [ (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))]))).
pose proof (IFSAME_M).
rewrite IFSAME_M with (b:=  (EQ_M (f [ (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))])  (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3)))))) (x:= (f [ (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))])). 
reflexivity.

assert (udecfx:  (pi2 (dec (f [ (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))) # (if_then_else_M  (EQ_M (f [ (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))])  (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))) (N n5)  (pi2 (dec (f [ (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))))).

rewrite ufx at 1.

pose proof(Example11_M).

apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))])) in H0. simpl in H0.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (enc (pair (sk n6) ( N n5 )) (pk n2) (rs (N n3))) ) in H0. simpl in H0.
apply  Forall_ELM_EVAL_M1 with (n:=3) (x :=  (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))])) in H0. simpl in H0.
 

rewrite H0 .


assert(Hf3:  (pi2 (dec (if_then_else_M (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk n2))) # (if_then_else_M (Bvar 0) (pi2 (dec (Mvar 1) (sk n2))) (pi2 (dec (Mvar 2) (sk n2))))).


rewrite <- IFSAME_M with (b:= (Bvar 0)) (x:=  (pi2 (dec (if_then_else_M (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk n2)))).

rewrite IFEVAL_M .
simpl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
reflexivity.
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (enc (pair (pi2 (k (N n6))) (N n5)) (pi1 (k (N n2))) (rs (N n3))))) in Hf3.
simpl in Hf3.
apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (enc (pair (pi2 (k (N n6))) (N n5)) (pi1 (k (N n2))) (rs (N n3)))) in Hf3. simpl in Hf3.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (f [enc (pair (sk n6)  (N n5)) (pk n2) (rs (N n3))])) in Hf3. simpl in Hf3.

rewrite Hf3.
pose proof(dep_enc).
rewrite dep_enc with (n:=n2) (x:=  (pair (pi2 (k (N n6))) (N n5 ))) .
rewrite proj2 with (m1:= (pi2 (k (N n6)))) (m2 := (N n5)) .
reflexivity.

(********************************************************************)

(**************L<sk1 , n5> , L<sk6, n5> *********)

assert(H2: (L (pair (sk n1) (N n5))) # (L (pair (sk n6) (N n5)))).

apply len_regular.  split.
Focus 2.
reflexivity.

assert(H3: lskey # ( L (sk n1))).
rewrite lsk with (n:= n1).

reflexivity.

assert(H4: lskey # ( L (sk  n6))).
rewrite lsk with (n:= n6).

reflexivity.

rewrite <- H3.
rewrite <- H4.
reflexivity.
apply EQmsg in H2.

pose proof (IFTRUE_M  (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3)))) O).
rewrite <- H2 in H0.

pose proof (IFTRUE_M  (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3)))) O).
rewrite <- H2 in H1.

simpl.
(*************************************************************************************************)
(*************************************************************************************************)


assert(TT: ( submsg_mylist 1   (if_then_else_M (EQ_M (L (pair (sk n1) (N n5))) (L (pair (sk n6) (N n5))))
          (enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))) O) [msg (Mvar 1); msg (enc (pair (if_then_else_M (EQ_M (f [Mvar 1]) (Mvar 1)) (N n5) (pi2 (dec (f [Mvar 1]) (sk n2)))) (N n))  (pk n1) (rs (N n4))) ; msg (N n)]) ~ (submsg_mylist 1  (if_then_else_M (EQ_M (L (pair (sk n1) (N n5))) (L (pair (sk n6) (N n5))))
           (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))) O) [msg (Mvar 1); msg (enc (pair (if_then_else_M (EQ_M (f [Mvar 1]) (Mvar 1)) (N n5) (pi2 (dec (f [Mvar 1]) (sk n2)))) (N n))  (pk n1) (rs (N n4))) ; msg (N n)])).



apply ENCCCA2 with (n:=1) (t''' := (pi2 (dec (f [Mvar 1]) (sk n2)))) (t'':= (N n5)) (t:=  (f [Mvar 1])) (u:= (pair (sk n1) (N n5))) (u':= (pair (sk n6) (N n5))) (u'':= O) (n1:= n2) (n2:=n3) (n3:= n3)  (l:=   [msg (Mvar 1); msg (enc (pair (if_then_else_M (EQ_M (f [Mvar 1]) (Mvar 1)) (N n5) (pi2 (dec (f [Mvar 1]) (sk n2)))) (N n)) (pk n1) (rs (N n4)))  ; msg (N n)]).
unfold rn_occ_mylist.
simpl.
inversion H.
repeat rewrite H3.
repeat rewrite <- beq_nat_refl. 

simpl. 
 repeat (try split; try reflexivity).  intros.
simpl. repeat rewrite <- beq_nat_refl.  simpl.
reflexivity.
 
assert(UU: ( submsg_mylist 1   (if_then_else_M (EQ_M (L (pair (sk n1) (N n5))) (L (pair (sk n6) (N n5))))
          (enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))) O)   [msg (Mvar 1); msg (enc (pair (if_then_else_M (EQ_M (f [Mvar 1]) (Mvar 1)) (N n5) (pi2 (dec (f [Mvar 1]) (sk n2)))) (N n))  (pk n1) (rs (N n4))) ; msg (N n')]) ~ (submsg_mylist 1  (if_then_else_M (EQ_M (L (pair (sk n1) (N n5))) (L (pair (sk n6) (N n5))))
           (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))) O)   [msg (Mvar 1); msg (enc (pair (if_then_else_M (EQ_M (f [Mvar 1]) (Mvar 1)) (N n5) (pi2 (dec (f [Mvar 1]) (sk n2)))) (N n))  (pk n1) (rs (N n4)))  ; msg (N n')])).
apply ENCCCA2 with (n:=1) (t''' := (pi2 (dec (f [Mvar 1]) (sk n2)))) (t'':= (N n5)) (t:= f[ Mvar 1]) (u:= (pair (sk n1) (N n5))) (u':= (pair (sk n6) (N n5))) (u'':= O) (n1:= n2) (n2:=n3) (n3:= n3)  (l:=   [msg (Mvar 1); msg (enc (pair (if_then_else_M (EQ_M (f [Mvar 1]) (Mvar 1)) (N n5) (pi2 (dec (f [Mvar 1]) (sk n2)))) (N n))  (pk n1) (rs (N n4))) ; msg (N n')]).
simpl.
repeat rewrite H3.
 repeat rewrite <- beq_nat_refl. 

simpl. 
 repeat (try split; try reflexivity).   repeat rewrite <- beq_nat_refl.  simpl.
reflexivity. inversion H. repeat rewrite H3. simpl. reflexivity. 
inversion H. repeat rewrite H3. simpl. reflexivity.
rewrite H0 in TT.
rewrite H1 in TT.
simpl in TT.
rewrite <- tdecfx in TT.
rewrite <- udecfx  in TT.
(******************Assumption on lengths*********************************)
assert(HT: (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n))) # (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)))).
apply len_regular.
split. reflexivity.

assert(t1 : lnonce # ( L (N n))).
rewrite ln with (n:=n).


reflexivity.
rewrite <- t1.
rewrite ln with (n:= n7).
reflexivity.

rewrite EQmsg in HT.


assert(TTT: ( submsg_mylist 1 (if_then_else_M (EQ_M (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)))  (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)))) (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)) (pk n1) (rs (N n4))) O)   [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))); msg (Mvar 1) ; msg (N n)]) ~ (submsg_mylist 1 (if_then_else_M (EQ_M (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)))  (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)))) (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4))) O) [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))); msg (Mvar 1) ; msg (N n)])).

apply ENCCCA2 with (n:=1) (t'':= (Mvar 1)) (t''' := (Mvar 1)) (t:= (Mvar 1)) (u:= (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n))) (u':=  (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7))) (u'':= O) (n1:= n1) (n2:=n4) (n3:= n4)  (l:=  [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))); msg (Mvar 1) ; msg (N n)]).
simpl. 
inversion H.
 rewrite <- Nat.eqb_sym.
 repeat rewrite H3. simpl. 

 repeat (try split; try reflexivity). 
rewrite HT in TTT.
repeat rewrite IFTRUE_M in TTT.
simpl in TTT.
assert(t1t6n7: [msg (enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n)] ~  [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4))); msg (N n)]).
apply EQI_trans with (ml2:= [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n)]).
assumption.

assumption.
rewrite H0 in UU.
rewrite H1 in UU.
simpl in UU.
rewrite <- udecfx in UU.
rewrite <- tdecfx in UU.

assert(UUU: ( submsg_mylist 1 (if_then_else_M (EQ_M (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)))  (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)))) (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)) (pk n1) (rs (N n4))) O)   [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))); msg (Mvar 1) ; msg (N n')]) ~ (submsg_mylist 1 (if_then_else_M (EQ_M (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)))  (L (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)))) (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4))) O) [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))); msg (Mvar 1) ; msg (N n')])).

apply ENCCCA2 with (n:=1) (t''' := (Mvar 1)) (t'':= (Mvar 1)) (t:= (Mvar 1)) (u:= (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n))) (u':=  (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7))) (u'':= O) (n1:= n1) (n2:=n4) (n3:= n4)  (l:=  [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))); msg (Mvar 1) ; msg (N n')]).
simpl.
inversion H.
 rewrite <- Nat.eqb_sym.
 repeat rewrite H3. simpl. 

 repeat (try split; try reflexivity). 
rewrite HT in UUU.
repeat rewrite IFTRUE_M in UUU.
simpl in UUU.
assert(u1u6n7: [msg (enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n')] ~  [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4))); msg (N n')]).
apply EQI_trans with (ml2:= [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n')]).
assumption.

assumption.
assert(Final :  [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4))); msg (N n)] ~  [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4))); msg (N n')]).

pose proof( FRESHIND_rs 2 n n'   [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4)))]  [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4)))]).
simpl in H3.
inversion H; clear H.
inversion H5; clear H5.
inversion H6; clear H6.
inversion H7; clear H7.
inversion H8; clear H8.
inversion H9; clear H9.
inversion H10; clear H10.
inversion H11; clear H11.
inversion H12; clear H12.
inversion H13; clear H13.
inversion H14; clear H14.
inversion H15; clear H15.

inversion H16; clear H16.
inversion H17; clear H17.
rewrite H, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H18 in H3.
simpl in H3.

assert( true = true /\ true = true /\ true = true /\ [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4)))] ~ [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4)))]). 
repeat (try split; try reflexivity).
apply H3 in H17. apply RESTR_swap with (p1:=1) (p2:=2) in H17. unfold swap_mylist in H17. simpl in H17. apply RESTR_swap with (p1:=2) (p2:=3) in H17. unfold swap_mylist in H17. simpl in H17.
assumption.

assert(result :  [msg (enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n)] ~  [msg (enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n')]).
apply EQI_trans with (ml2:=  [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4))); msg (N n)]).
assumption.
apply EQI_trans with (ml2:=  [msg (enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3)));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk n6) (N n5)) (pk n2) (rs (N n3))]) (sk n2))) (N n7)) (pk n1) (rs (N n4))); msg (N n')]).
assumption. symmetry in u1u6n7. assumption. assumption.
Qed.