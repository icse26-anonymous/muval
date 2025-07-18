;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_tree_fun$ 0 )
(declare-sort A_tree$ 0)
(declare-fun select$ (A_tree$)Nat$)
(declare-fun selecta$ (A_tree$)A$)
(declare-fun leaf$ (Nat$ A$ )A_tree$)
(declare-fun selectb$ (A_tree$)Nat$)
(declare-fun selectc$ (A_tree$)A_tree$)
(declare-fun selectd$ (A_tree$)A_tree$)
(declare-fun innerNode$ (Nat$ A_tree$ A_tree$ )A_tree$)
(declare-fun a$ ()A$ )
(declare-fun b$ ()A$ )
(declare-fun t$ ()A_tree$ )
(declare-fun w_a$ ()Nat$ )
(declare-fun w_b$ ()Nat$ )
(declare-fun cost$ (A_tree$ )Nat$ )
(declare-fun freq$ (A_tree$ A$ )Nat$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun depth$ (A_tree$ A$ )Nat$ )
(declare-fun times$ (Nat$ Nat$ )Nat$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun weight$ (A_tree$ )Nat$ )
(declare-fun fun_app$ (A_a_tree_fun$ A$ )A_tree$ )
(declare-fun alphabet$ (A_tree$ )A_set$ )
(declare-fun consistent$ (A_tree$ )Bool )
(declare-fun swapLeaves$ (A_tree$ Nat$ A$ Nat$ )A_a_tree_fun$ )
(declare-fun uniteTrees$ (A_tree$ A_tree$ )A_tree$ )
(assert (! (not (ite (member$ a$ (alphabet$ t$ ))(ite (member$ b$ (alphabet$ t$ ))(= (plus$ (plus$ (cost$ (fun_app$ (swapLeaves$ t$ w_a$ a$ w_b$ )b$ ))(times$ (freq$ t$ a$ )(depth$ t$ a$ )))(times$ (freq$ t$ b$ )(depth$ t$ b$ )))(plus$ (plus$ (cost$ t$ )(times$ w_a$ (depth$ t$ b$ )))(times$ w_b$ (depth$ t$ a$ ))))(= (plus$ (cost$ (fun_app$ (swapLeaves$ t$ w_a$ a$ w_b$ )b$ ))(times$ (freq$ t$ a$ )(depth$ t$ a$ )))(plus$ (cost$ t$ )(times$ w_b$ (depth$ t$ a$ )))))(ite (member$ b$ (alphabet$ t$ ))(= (plus$ (cost$ (fun_app$ (swapLeaves$ t$ w_a$ a$ w_b$ )b$ ))(times$ (freq$ t$ b$ )(depth$ t$ b$ )))(plus$ (cost$ t$ )(times$ w_a$ (depth$ t$ b$ ))))(= (cost$ (fun_app$ (swapLeaves$ t$ w_a$ a$ w_b$ )b$ ))(cost$ t$ ))))):named a0 ))
(assert (! (consistent$ t$ ):named a1 ))
(assert (! (not (= a$ b$ )):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 Nat$ )(?v3 Nat$ ))(! (=> (not (member$ ?v0 (alphabet$ ?v1 )))(= (fun_app$ (swapLeaves$ ?v1 ?v2 ?v0 ?v3 )?v0 )?v1 )):pattern ((swapLeaves$ ?v1 ?v2 ?v0 ?v3 )))):named a3 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ ))(=> (consistent$ ?v0 )(= (fun_app$ (swapLeaves$ ?v0 (freq$ ?v0 ?v1 )?v1 (freq$ ?v0 ?v1 ))?v1 )?v0 ))):named a4 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ )(?v3 A$ )(?v4 Nat$ )(?v5 Nat$ ))(=> (and (consistent$ ?v0 )(and (not (= ?v1 ?v2 ))(not (= ?v1 ?v3 ))))(= (depth$ (fun_app$ (swapLeaves$ ?v0 ?v4 ?v2 ?v5 )?v3 )?v1 )(depth$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 Nat$ )(?v2 A$ )(?v3 Nat$ )(?v4 A$ ))(=> (consistent$ ?v0 )(consistent$ (fun_app$ (swapLeaves$ ?v0 ?v1 ?v2 ?v3 )?v4 )))):named a6 ))
(assert (! (forall ((?v0 A_tree$ ))(exists ((?v1 A$ ))(member$ ?v1 (alphabet$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ )(?v3 Nat$ )(?v4 Nat$ ))(=> (and (consistent$ ?v0 )(not (= ?v1 ?v2 )))(ite (member$ ?v1 (alphabet$ ?v0 ))(ite (member$ ?v2 (alphabet$ ?v0 ))(= (plus$ (plus$ (weight$ (fun_app$ (swapLeaves$ ?v0 ?v3 ?v1 ?v4 )?v2 ))(freq$ ?v0 ?v1 ))(freq$ ?v0 ?v2 ))(plus$ (plus$ (weight$ ?v0 )?v3 )?v4 ))(= (plus$ (weight$ (fun_app$ (swapLeaves$ ?v0 ?v3 ?v1 ?v4 )?v2 ))(freq$ ?v0 ?v1 ))(plus$ (weight$ ?v0 )?v4 )))(ite (member$ ?v2 (alphabet$ ?v0 ))(= (plus$ (weight$ (fun_app$ (swapLeaves$ ?v0 ?v3 ?v1 ?v4 )?v2 ))(freq$ ?v0 ?v2 ))(plus$ (weight$ ?v0 )?v3 ))(= (weight$ (fun_app$ (swapLeaves$ ?v0 ?v3 ?v1 ?v4 )?v2 ))(weight$ ?v0 )))))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree$ )(?v2 A$ ))(= (freq$ (uniteTrees$ ?v0 ?v1 )?v2 )(plus$ (freq$ ?v0 ?v2 )(freq$ ?v1 ?v2 )))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (plus$ (times$ ?v0 ?v1 )(plus$ (times$ ?v2 ?v1 )?v3 ))(plus$ (times$ (plus$ ?v0 ?v2 )?v1 )?v3 ))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (plus$ ?v0 ?v1 )?v2 )(plus$ (times$ ?v0 ?v2 )(times$ ?v1 ?v2 )))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ ?v0 (plus$ ?v1 ?v2 ))(plus$ (times$ ?v0 ?v1 )(times$ ?v0 ?v2 )))):named a14 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (= (plus$ (times$ ?v0 ?v1 )(times$ ?v2 ?v3 ))(plus$ (times$ ?v0 ?v3 )(times$ ?v2 ?v1 )))(or (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (plus$ (times$ ?v0 ?v1 )(plus$ (times$ ?v2 ?v1 )?v3 ))(plus$ (times$ (plus$ ?v0 ?v2 )?v1 )?v3 ))):named a16 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (plus$ ?v0 ?v1 )?v2 )(plus$ (times$ ?v0 ?v2 )(times$ ?v1 ?v2 )))):named a17 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (plus$ ?v0 ?v1 )?v2 )(plus$ (times$ ?v0 ?v2 )(times$ ?v1 ?v2 )))):named a18 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (plus$ (times$ ?v0 ?v1 )(times$ ?v2 ?v1 ))(times$ (plus$ ?v0 ?v2 )?v1 ))):named a19 ))
(check-sat )
;(get-unsat-core )
