Load "tact_DH_2".

  
  
 

Theorem Pi1_Pi2'': phi5 #### phi35.
Proof.
unfold phi5, phi35.
unfold phi5.
  repeat unf_phi. 
  
assert(H: (ostomsg t15) # (ostomsg t35)).
simpl.
 
 repeat unf.
 unfold mx2rn2, mx3rn1.
 pose proof(andB_assoc).
rewrite andB_assoc with (b2:=  (EQ_M (m x2) (grn 1))) .
rewrite andB_comm with (b1 := (EQ_M (m x2) (grn 1))) (b2:= (EQ_M (m x3) (grn 2))).
rewrite  <- andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
rewrite <- andB_comm with (b1:= (EQ_M (m x2) (grn 1))). 

rewrite EQ_BRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl.

rewrite andB_comm with (b1 := (((((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                 (EQ_M (to x2) (i 2))) &
                                                (EQ_M (to x1) (i 1))) &
                                               (notb (EQ_M (act x3) new))) &
                                             (EQ_M (act x1) new)) &
                                                                    (EQ_M (m x2) (grn 1)))) .
 

rewrite EQ_BRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))) .
simpl.
rewrite <- commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (y:= (rr (N 2))) (x:= (rr (N 1))).
(**********************************(EQ_M (reveal x4) (i 2))***********************************************) 
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=   (EQ_M (to x3) (i 1))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=   ((EQ_M (to x3) (i 1)) &
                                         (EQ_M (to x2) (i 2)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=    (((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=    ((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x3) new)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=    (((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x3) new))) &
                                                                         (EQ_M (act x1) new))). 
rewrite <- andB_assoc with (b2:= (EQ_M (reveal x4) (i 2))).
rewrite  andB_comm with (b2:= (EQ_M (reveal x4) (i 2))).
rewrite andB_assoc with  (b1:= (EQ_M (reveal x4) (i 2))).

(******************(EQ_M (reveal x4) (i 1)) *************************)
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b3:=   (EQ_M (to x2) (i 2))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=   ((EQ_M (to x3) (i 1)) &
                                         (EQ_M (to x2) (i 2)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=    (((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=    ((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x3) new)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=    (((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                              (notb (EQ_M (act x3) new))) &
                                                                         (EQ_M (act x1) new))). 

rewrite <- andB_assoc with (b2:= (EQ_M (reveal x4) (i 1))).
rewrite  andB_comm with (b2:= (EQ_M (reveal x4) (i 1))).
rewrite andB_assoc with  (b2:= (EQ_M (m x3) (grn 2))).

(********************************************************************)

rewrite <- andB_assoc with (b1:= (EQ_M (m x3) (grn 2))) (b3:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b2:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b1:= (EQ_M (m x3) (grn 2))).
 
  
(**********************************************************************)
 

aply_breq_same.  
 repeat redg;  repeat rewrite IFTFb. 
aply_breq_same.  
 (*repeat aply_andB_elm.  *)

 repeat redg;  repeat rewrite IFTFb.


 repeat rewrite andB_elm'' with (b1:= (EQ_M (to x1) (i 1))) (b2:=  (EQ_M (act x1) new)).




 false_to_sesns_all. simpl. 
 repeat redg; repeat rewrite IFTFb.
 aply_breq. 
  aply_breq. 
 repeat redg; repeat rewrite IFTFb.
 aply_breq_same.
 aply_breq_same. 
repeat redg; repeat rewrite IFTFb.
 false_to_sesns_all; simpl. 
 aply_breq.
 repeat redg; repeat rewrite IFTFb.
repeat aply_andB_elm.
 false_to_sesns_all; simpl. 
repeat redg; repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
repeat redg; repeat rewrite IFTFb.
 aply_breq. 
false_to_sesns_all; simpl. 
repeat redg; repeat rewrite IFTFb.
aply_breq. 
repeat redg; repeat rewrite IFTFb.
aply_breq. 
 false_to_sesns_all; simpl. 
aply_breq. 
 repeat redg; repeat rewrite IFTFb.
   repeat aply_andB_elm. 

aply_breq.   
rewrite <- IFSAME_M with (b:= (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).


rewrite EQ_BRmsg_msg''' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))).  simpl. 
  unfold grn , G, g, r, x2.
aply_breq. 
repeat redg; repeat rewrite IFTFb. reflexivity. 
repeat redg; repeat rewrite IFTFb.  reflexivity.
aply_breq.
rewrite <- IFSAME_M with (b:= (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite EQ_BRmsg_msg''' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (if_then_else_M (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
         (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1))) O)).  simpl. 
 unfold grn , G, g, r, x2.
aply_breq. 
rewrite <- IFSAME_M with (b:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).
aply_breq. 
(*
repeat redg; repeat rewrite IFTFb.  reflexivity.
repeat redg; repeat rewrite IFTFb. reflexivity.
repeat redg; repeat rewrite IFTFb.  reflexivity.

aply_breq.

repeat redg; repeat rewrite IFTFb.
rewrite <- IFSAME_M with (b:=  (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
aply_breq. 
repeat redg; repeat rewrite IFTFb.
aply_breq.  *)
rewrite <- IFSAME_M with (b:=  (EQ_M (m (f mphi2))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite EQ_BRmsg_msg''' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl.

unfold x3, grn, G, g, r.
aply_breq.
rewrite commexp. reflexivity.
(********(EQ_M (to x1) (i 2))****************)
repeat redg; repeat rewrite IFTFb. reflexivity. 
 apply eqm in H. rewrite H. reflexivity. 

Qed.
