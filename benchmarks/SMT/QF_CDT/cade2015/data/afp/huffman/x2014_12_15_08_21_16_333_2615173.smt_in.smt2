;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_nat_fun$ 0 )
(declare-datatypes ()((A_tree$ (leaf$ (select$ Nat$ )(selecta$ A$ ))(innerNode$ (selectb$ Nat$ )(selectc$ A_tree$ )(selectd$ A_tree$ )))))
(declare-fun a$ ()A$ )
(declare-fun b$ ()A$ )
(declare-fun t$ ()A_tree$ )
(declare-fun w_a$ ()Nat$ )
(declare-fun w_b$ ()Nat$ )
(declare-fun cost$ (A_tree$ )Nat$ )
(declare-fun freq$ (A_tree$ )A_nat_fun$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun weight$ (A_tree$ )Nat$ )
(declare-fun fun_app$ (A_nat_fun$ A$ )Nat$ )
(declare-fun less_eq$ (Nat$ Nat$ )Bool )
(declare-fun optimum$ (A_tree$ )Bool )
(declare-fun alphabet$ (A_tree$ )A_set$ )
(declare-fun swapSyms$ (A_tree$ A$ A$ )A_tree$ )
(declare-fun splitLeaf$ (A_tree$ Nat$ A$ Nat$ A$ )A_tree$ )
(declare-fun consistent$ (A_tree$ )Bool )
(declare-fun swapLeaves$ (A_tree$ Nat$ A$ Nat$ A$ )A_tree$ )
(declare-fun uniteTrees$ (A_tree$ A_tree$ )A_tree$ )
(declare-fun swapFourSyms$ (A_tree$ A$ A$ A$ A$ )A_tree$ )
(assert (! (not (= (cost$ (splitLeaf$ t$ w_a$ a$ w_b$ b$ ))(plus$ (plus$ (cost$ t$ )w_a$ )w_b$ ))):named a0 ))
(assert (! (consistent$ t$ ):named a1 ))
(assert (! (member$ a$ (alphabet$ t$ )):named a2 ))
(assert (! (= (fun_app$ (freq$ t$ )a$ )(plus$ w_a$ w_b$ )):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 Nat$ )(?v3 Nat$ )(?v4 A$ ))(! (=> (not (member$ ?v0 (alphabet$ ?v1 )))(= (splitLeaf$ ?v1 ?v2 ?v0 ?v3 ?v4 )?v1 )):pattern ((splitLeaf$ ?v1 ?v2 ?v0 ?v3 ?v4 )))):named a4 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 Nat$ )(?v3 A$ )(?v4 Nat$ ))(=> (and (consistent$ ?v0 )(not (member$ ?v1 (alphabet$ ?v0 ))))(consistent$ (splitLeaf$ ?v0 ?v2 ?v3 ?v4 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_tree$ ))(exists ((?v1 A$ ))(member$ ?v1 (alphabet$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ )(?v3 A$ )(?v4 A$ ))(=> (and (consistent$ ?v0 )(and (member$ ?v1 (alphabet$ ?v0 ))(and (member$ ?v2 (alphabet$ ?v0 ))(and (member$ ?v3 (alphabet$ ?v0 ))(member$ ?v4 (alphabet$ ?v0 ))))))(= (freq$ (swapFourSyms$ ?v0 ?v1 ?v2 ?v3 ?v4 ))(freq$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 Nat$ )(?v3 Nat$ )(?v4 A$ ))(=> (and (consistent$ ?v0 )(and (member$ ?v1 (alphabet$ ?v0 ))(= (fun_app$ (freq$ ?v0 )?v1 )(plus$ ?v2 ?v3 ))))(= (weight$ (splitLeaf$ ?v0 ?v2 ?v1 ?v3 ?v4 ))(weight$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ ))(=> (and (consistent$ ?v0 )(and (member$ ?v1 (alphabet$ ?v0 ))(member$ ?v2 (alphabet$ ?v0 ))))(= (freq$ (swapSyms$ ?v0 ?v1 ?v2 ))(freq$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree$ )(?v2 A$ ))(= (fun_app$ (freq$ (uniteTrees$ ?v0 ?v1 ))?v2 )(plus$ (fun_app$ (freq$ ?v0 )?v2 )(fun_app$ (freq$ ?v1 )?v2 )))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A$ )(?v3 A$ )(?v4 A$ ))(=> (and (member$ ?v0 (alphabet$ ?v1 ))(and (member$ ?v2 (alphabet$ ?v1 ))(and (member$ ?v3 (alphabet$ ?v1 ))(member$ ?v4 (alphabet$ ?v1 )))))(= (alphabet$ (swapFourSyms$ ?v1 ?v0 ?v2 ?v3 ?v4 ))(alphabet$ ?v1 )))):named a13 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ ))(=> (consistent$ ?v0 )(= (swapLeaves$ ?v0 (fun_app$ (freq$ ?v0 )?v1 )?v1 (fun_app$ (freq$ ?v0 )?v1 )?v1 )?v0 ))):named a14 ))
(assert (! (forall ((?v0 A_tree$ ))(= (optimum$ ?v0 )(forall ((?v1 A_tree$ ))(=> (and (consistent$ ?v1 )(and (= (alphabet$ ?v0 )(alphabet$ ?v1 ))(= (freq$ ?v0 )(freq$ ?v1 ))))(less_eq$ (cost$ ?v0 )(cost$ ?v1 )))))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a16 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a17 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ )(?v3 A$ )(?v4 A$ ))(=> (consistent$ ?v0 )(consistent$ (swapFourSyms$ ?v0 ?v1 ?v2 ?v3 ?v4 )))):named a18 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (less_eq$ (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(less_eq$ ?v1 ?v2 ))):named a19 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (less_eq$ (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(less_eq$ ?v0 ?v2 ))):named a20 ))
(check-sat )
;(get-unsat-core )
