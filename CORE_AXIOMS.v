Load "IND_MORPHISMS".

 

(***********Indistinguishability Axioms*******************************************)
(************************************************************************************)
 

(*********************FUNCApp***************************************************)
(*******************************************************************************)

 Section  Core_Axioms.
Variable fmb4 : message -> message -> message -> message -> Bool.
Variable fm: message.
Variable fb: Bool.
Variable f1 : message  -> message.
Variable f2b : message  -> message -> Bool.
Variable f2m : message ->  message -> message.
Variable f3b: message -> message -> message -> Bool.
Variable f3bm: Bool -> message -> message -> message.
Variable f3m : message -> message -> message -> message .
Variable f4b: message -> message -> message -> message -> Bool.
Variable f4m: message -> message -> message -> message -> message.
Variable g2: Bool -> Bool -> Bool.
Variable g3 : Bool -> Bool -> Bool -> Bool.
 (*************************************************************************************************)
Axiom FUNCApp_att4: forall (p1 p2 p3 p4 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol (fmb4 (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos  p2 ml1)) (ostomsg (getelt_at_pos  p3 ml1)) (ostomsg (getelt_at_pos  p4 ml1)))] )
 ~ (ml2 ++ [ bol (fmb4 (ostomsg (getelt_at_pos  p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos  p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ).

Axiom FUNCApp_fm: forall  {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  fm] )
 ~ (ml2 ++ [ msg fm] ).
Axiom FUNCApp_fb: forall  {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  fb] )
 ~ (ml2 ++ [ bol fb] ).

Axiom FUNCApp_f1: forall (p:nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f1 (ostomsg (getelt_at_pos p ml1)))] ) ~ (ml2 ++ [ msg  (f1 (ostomsg (getelt_at_pos p ml2)))] ).


Axiom FUNCApp_f2b: forall (p1 p2 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (f2b (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)))] ) ~ (ml2 ++ [ bol  (f2b (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)))] ).

Axiom FUNCApp_f2m: forall (p1 p2 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f2m (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)))] ) ~ (ml2 ++ [ msg (f2m (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)))] ).


 Axiom FUNCApp_f3b: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (f3b (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ bol  (f3b (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ).

 Axiom FUNCApp_f3bm: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f3bm (ostobol (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ msg  (f3bm (ostobol (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ).

 Axiom FUNCApp_f3m: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f3m (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ msg  (f3m (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ).

Axiom FUNCApp_f4b: forall (p1 p2 p3 p4 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (f4b (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)) (ostomsg (getelt_at_pos p4 ml1)))] ) ~ (ml2 ++  [ bol  (f4b (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ).

Axiom FUNCApp_f4m: forall (p1 p2 p3 p4 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f4m (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)) (ostomsg (getelt_at_pos p4 ml1)))] ) ~ (ml2 ++  [ msg  (f4m (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ).
Axiom FUNCApp_g2: forall (p1 p2 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (g2 (ostobol (getelt_at_pos p1 ml1)) (ostobol (getelt_at_pos p2 ml1)))] ) ~ (ml2 ++ [ bol  (g2 (ostobol (getelt_at_pos p1 ml2)) (ostobol (getelt_at_pos p2 ml2)))] ).


 Axiom FUNCApp_g3: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (g3 (ostobol (getelt_at_pos p1 ml1)) (ostobol (getelt_at_pos p2 ml1)) (ostobol (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ bol  (g3 (ostobol (getelt_at_pos p1 ml2)) (ostobol (getelt_at_pos p2 ml2)) (ostobol (getelt_at_pos p3 ml2)))] ).
Axiom FUNCApp_sublist:  forall (m n:nat) {n1} (ml1 ml2:mylist n1), (ml1 ~ ml2) -> (ml1 ++ [msg (f  (sublist m n (conv_mylist_listm ml1)))]) ~ (ml2 ++ [msg (f (sublist m n (conv_mylist_listm ml2)))]).

(**************************************************************************************************)
Axiom FUNCApp_const: forall (n m :nat) (ml1 ml2: mylist n) (a: mylist m), (ml1 ~ ml2) -> (ml1 ++ (const  a ml1 )) ~ (ml2 ++ (const a ml2)).

Axiom FUNCApp_appelt:  forall (n p :nat) (ml1 ml2: mylist n), (ml1 ~ ml2) -> (ml1 ++ [getelt_at_pos  p ml1]  ) ~ (ml2 ++ [getelt_at_pos  p ml2]).

Axiom FUNCApp_EQ_M: forall (p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) -> (ml1 ++ ([ bol (EQ_M_at_pos  p1 p2 ml1) ])) ~ (ml2 ++ ([ bol (EQ_M_at_pos  p1 p2 ml2)])).
(**
Axiom FUNCApp_EQ_M1: forall (p p1 p2  :nat) {n}(ml1 ml2 :mylist n), (ml1 ~ ml2) -> (@insert_at_pos p  ( bol (EQ_M_at_pos (msg O) p1 p2 ml1)) n  ml1) ~ (@insert_at_pos p ( bol (EQ_M_at_pos (msg O) p1 p2 ml2)) n ml2). **)
Axiom FUNCApp_EQ_B: forall ( p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) ->  (ml1 ++  [ bol (EQ_B_at_pos  p1 p2 ml1)])  ~ (ml2 ++  [ bol (EQ_B_at_pos  p1 p2 ml2)])  .

(**Axiom FUNCApp_EQ_B1: forall ( p p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) ->  (@insert_at_pos p  ( bol (EQ_B_at_pos (bol TRue) p1 p2 ml1)) n  ml1)  ~ (@insert_at_pos p  ( bol (EQ_B_at_pos (bol TRue) p1 p2 ml1)) n  ml2) .**)

Axiom FUNCApp_negpos: forall (p :nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) -> (ml1 ++ (neg_at_pos p ml1)) ~ (ml2 ++ (neg_at_pos p ml2)).

Axiom FUNCApp_ifmnespair : forall ( p1 p2 p3 p4 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> (ml1 ++ [msg (ifm_nespair  p1 p2 p3 p4 ml1)]) ~(ml2 ++ [msg (ifm_nespair  p1 p2 p3 p4 ml2)]).

Axiom FUNCApp_ifmpair: forall ( p1 p2 p3 p4  : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> (ml1 ++ [msg (ifm_pair  p1 p2 p3 p4 ml1)]) ~ (ml2 ++ [ msg (ifm_pair p1 p2 p3 p4 ml2)]). 

(*Axiom FUNCApp_expatpos: forall (n p p1 p2 p3 : nat) (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( app_elt_pos (msg (exp_at_pos (msg O) p1 p2 p3  ml1)) p ml1 ) ~ ( app_elt_pos (msg (exp_at_pos (msg O) p1 p2 p3  ml2)) p ml2 ) .  *)

Axiom FUNCApp_expatpos: forall (p1 p2 p3 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( ml1 ++ [msg (exp_at_pos  p1 p2 p3  ml1)]) ~ ( ml2 ++ [msg (exp_at_pos  p1 p2 p3  ml2)]) .
(**
Axiom FUNCApp_expatpos1: forall (p p1 p2 p3 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( @insert_at_pos p  (msg (exp_at_pos (msg O) p1 p2 p3  ml1)) n ml1 ) ~ ( @insert_at_pos p  (msg (exp_at_pos (msg O) p1 p2 p3  ml2)) n ml2 ).
**)



Axiom FUNCApp_att : forall {n} (ml1 ml2: mylist n) (l1 l2 :list message ), (ml1 ~ ml2) -> ([msg (f l1)] ++ ml1) ~ ([msg (f l2)] ++ ml2).

Axiom FUNCApp_reveal:  forall ( p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (reveal_at_pos p ml1)] ++ml1   ) ~ ([msg (reveal_at_pos p ml2)] ++ml2 ).

Axiom FUNCApp_to:  forall (p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (to_at_pos p ml1)] ++ ml1)  ~ ([msg (to_at_pos p ml2)] ++ ml2).

Axiom FUNCApp_act:  forall (p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (act_at_pos p ml1)] ++ ml1)  ~ ([msg (act_at_pos p ml2)] ++ ml2).

Axiom FUNCApp_new : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg new ] ++ ml1) ~ ([msg new ] ++ ml2).
Axiom FUNCApp_O : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ( ml1 ++ [msg O]) ~ (ml2 ++ [msg O]).
Axiom FUNCApp_acc : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ( ml1 ++ [msg acc]) ~ (ml2 ++ [msg acc]).
Axiom FUNCApp_session : forall ( m: nat ) {n} (ml1 ml2 : mylist m) , (ml1 ~ ml2) -> ([msg (i n) ] ++ ml1) ~ ([msg (i n) ] ++ ml2).
(**
Axiom FUNCApp_andB1: forall (p p1 p2:nat)  {n}(ml1 ml2: mylist n), (ml1 ~ ml2) ->  (@insert_at_pos p  ( bol (andB_at_pos (msg O) p1 p2 ml1)) n  ml1)  ~ (@insert_at_pos p  ( bol (andB_at_pos (msg O) p1 p2 ml1)) n  ml2) .
**)
Axiom FUNCApp_andB : forall (p1 p2 :nat) {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> (ml1 ++ [bol (andB_at_pos p1 p2 ml1)]) ~  (ml2 ++ [bol (andB_at_pos p1 p2 ml2)]).
Axiom FUNCApp_notB : forall (p :nat) {m} (ml1 ml2:mylist m), (ml1 ~ ml2) -> (ml1 ++ [bol (notB_at_pos  p ml1)]) ~ (ml2 ++ [bol (notB_at_pos p ml2)]).
Axiom FUNCApp_m : forall (p :nat) {m} (ml1 ml2:mylist m), (ml1 ~ ml2) -> ( [ msg (m_at_pos  p ml1)] ++ ml1) ~  (  [msg (m_at_pos  p ml2) ] ++ ml2).
(**
Axiom FUNCApp_exptrm : forall (p n n1:nat) {m} (ml1 ml2:mylist m), (ml1~ml2) -> ((occexp_in_mylist n n1 ml1) = true) ->  ((occexp_in_mylist n n1 ml2) = true)  -> (@insert_at_pos p ( msg (exp (G n) (g n) (r n1))) m ml1) ~ (@insert_at_pos p ( msg (exp (G n) (g n) (r n1))) m ml2).
**)
Axiom FUNCApp_elt :   forall (p p1  :nat) {m} (ml1 ml2:mylist m), (ml1~ml2) ->  (ml1 ++ [getelt_at_pos  p1 ml1 ] ) ~ (ml2 ++ [  getelt_at_pos p1 ml2]).
(*******************************add closed term at pos p***************************************)

Axiom FUNCApp_os : forall (p n :nat) (t: oursum) (ml1 ml2:mylist n),  
                     ml1 ~ ml2 -> (clos_os t = true) -> (@insert_at_pos p t n ml1) ~ (@insert_at_pos p t n ml2).


(*******************RESTR******************************************************)
(******************************************************************************)

(****************** Ind closed under projections ****************)
Axiom RESTR_proj : forall ( p :nat) {m} (ml1 ml2 :mylist m), ml1 ~ ml2 -> (proj_at_pos p ml1) ~ (proj_at_pos p ml2).
(****************** Ind closed under permutations ****************)
Axiom RESTR_swap : forall (p1 p2 : nat) {n} (ml1 ml2 : mylist n), ml1~ ml2 -> (swap_mylist p1 p2 ml1) ~ (swap_mylist p1 p2 ml2).



Axiom FUNCApp_dropls: forall {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> (droplastsec ml1) ~ (droplastsec ml2).
(**
Axiom FUNCApp_droplt: forall {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> (droplast3rd ml1) ~ (droplast3rd ml2).

Axiom RESTR_Drop: forall (n :nat)  (ml1 ml2 : mylist n) , ml1 ~ ml2 ->  (dropone ml1) ~ (dropone ml2).
Axiom RESTR1 : forall (n m:nat)  (l1 l1' : mylist n) (l2 l2': mylist m) (x y: oursum), (l1 ++ [x] ++l2) ~ (l1'++ [y]++l2') -> (l1 ++ l2) ~ (l1'++l2').
**)
(********************Ind closed under permutations **********************)
(**

Axiom RESTR_SWAP : forall (p1 p2 : nat) {n} (ml1 ml2 : mylist n), ml1~ ml2 -> (swap_mylist p1 p2 ml1) ~ (swap_mylist p1 p2 ml2).
Axiom RESTR_rev: forall (n:nat) (ml1 ml2: mylist n) , ml1 ~ ml2 -> (reverse ml1) ~ (reverse ml2).
Axiom RESTR2 : forall (n1 n2 n3 :nat) (l1 l1' : mylist n1) (l2 l2' : mylist n2) (l3 l3' : mylist n3) (x1 x2 y1 y2 : oursum), (l1 ++ [x1] ++ l2 ++ [x2] ++ l3) ~ (l1' ++ [y1] ++ l2' ++ [y2] ++ l3') ->
 (l1 ++ [x2] ++ l2 ++ [x1] ++ l3) ~ (l1' ++ [y2] ++ l2' ++ [y1] ++ l3').
**)
(********************************************************************************)
Axiom TFDIST: not ([bol TRue]~[bol FAlse]).


(*****Axioms for if_then_else *****************)

(**IFSAME**)


Axiom IFSAME_M: forall (b:Bool) (x : message), (if_then_else_M b x x) # x.
Axiom IFSAME_B: forall (b:Bool) (b1 : Bool),  (if_then_else_B b b1 b1) ## b1.

(**IFEVAL**)

Axiom IFEVAL_B : forall (b1 b2 : Bool)(n:nat),  (if_then_else_B (Bvar n) b1 b2) ## (if_then_else_B (Bvar n) ([n := TRue] b1) ([n := FAlse] b2)).
Axiom IFEVAL_M : forall (t1 t2 : message) (n:nat),  (if_then_else_M (Bvar n) t1 t2) #(if_then_else_M (Bvar n) ((n := TRue) t1) ((n := FAlse) t2)).
Axiom IFEVAL_B' : forall (b b1 b2 : Bool),  (if_then_else_B b b1 b2) ## (if_then_else_B b (subbol_bol' b TRue b1) (subbol_bol' b FAlse b2)).
 
Axiom IFEVAL_M' : forall (b:Bool)(t1 t2  : message),  (if_then_else_M b t1 t2) #(if_then_else_M b (subbol_msg' b TRue t1) (subbol_msg' b FAlse t2)).


(**IFTRue**)

Axiom IFTRUE_M : forall (x y : message),  (if_then_else_M TRue x y) # x .
Axiom IFTRUE_B : forall (b1 b2 : Bool), (if_then_else_B TRue b1 b2) ## b1.


(**IFFAlse**)

Axiom IFFALSE_M: forall (x y : message), (if_then_else_M FAlse x y) # y.
Axiom IFFALSE_B: forall (b1 b2 : Bool),  (if_then_else_B FAlse b1 b2) ## b2.

(********************************************IFBRANCH******************************************)
(**********************************************************************************************)

Axiom IFBRANCH_M: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), (ml1 ++ [ bol b ; msg x] ) ~  ( ml2 ++ [ bol b'; msg x'])  ->  (ml1 ++ [bol b ; msg y ] ) ~( ml2 ++ [bol b' ; msg y'])
-> (ml1 ++ [bol b ;msg (if_then_else_M b x y)])~ ( ml2 ++ [bol b' ; msg (if_then_else_M b' x' y')]).

Axiom IFBRANCH_B: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(b1 b1' b2 b2':Bool), (ml1 ++ [bol b ;bol b1]) ~ ( ml2 ++ [bol b' ; bol b1'])  ->  (ml1 ++ [ bol b; bol b2]) ~( ml2 ++ [bol b'; bol b2'])
-> (ml1 ++ [ bol b ;bol (if_then_else_B b b1 b2)])~ (  ml2 ++ [bol b' ; bol (if_then_else_B b' b1' b2')] ).

(*******************************Axioms for Fresh names*****************************************)
(**********************************************************************************************)

Axiom FRESHNEQ: forall (n : nat) (m : message), ((clos_msg m) = true)/\ ( (Fresh [n] [msg m]) = true) ->[bol (EQ_M (N n) m)]~ [bol FAlse] .

Axiom FRESHIND: forall (n n1 n2:nat) (v w: mylist n), ((clos_mylist (v++w)) = true) /\ ( (Fresh [ n1] (v++w)) = true) /\ ( (Fresh [ n2] (v++w)) = true) /\  (v ~ w) <-> ((msg (r n1) ) +++ v) ~ (( msg (r n2)) +++w ) .
Axiom FRESHIND_rs : forall (n n1 n2:nat) (v w: mylist n), ((clos_mylist (v++w)) = true) /\ ( (Fresh [ n1] (v++w)) = true) /\ ( (Fresh [ n2] (v++w)) = true) /\  (v ~ w) <-> ((msg  (N n1)) +++ v) ~ (( msg  (N n2)) +++w ) .


(*****************************************************************************************************************************************************************)
(****Fresh [n;n1;n2;n3]-> [G(n); g(n);g(n)^(r (n1));g(n)^(r (n2)); g(n)^(r (n1))(r (n2))] ~[G(n); g(n);g(n)^(r (n1));g(n)^(r (n2)); g(n)^(r (n3))]*****************)

Axiom DDH : forall (n n1 n2 n3: nat),  (Fresh [ n ; n1 ;  n2  ; n3 ] []) = true-> 
[ msg (G n) ; msg (g n) ; msg (exp (G n) (g n) (r  n1)) ; msg (exp (G n) (g n) (r  n2)) ; msg (exp (G n) (exp (G n) (g n) (r  n1)) (r  n2))]
~ [msg (G n) ; msg (g n) ; msg (exp (G n) (g n) (r  n1)) ; msg (exp (G n) (g n) (r n2)) ; msg (exp (G n) (g n) (r n3))]  .

Goal (f [ (if_then_else_M TRue O O)]) # (f [ O]).
rewrite IFTRUE_M. reflexivity.  Qed. 
 Check f.
End Core_Axioms.


Eval compute in sublist 0 3 [ msg O; msg  (N 1); msg (N 2)].
Check f.