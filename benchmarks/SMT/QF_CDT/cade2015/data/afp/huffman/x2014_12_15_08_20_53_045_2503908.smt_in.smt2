;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_nat_fun$ 0 )
(declare-sort A_a_tree_fun$ 0 )
(declare-datatypes ()((A_tree$ (leaf$ (select$ Nat$ )(selecta$ A$ ))(innerNode$ (selectb$ Nat$ )(selectc$ A_tree$ )(selectd$ A_tree$ )))))
(declare-fun a$ ()A$ )
(declare-fun b$ ()A$ )
(declare-fun c$ ()A$ )
(declare-fun d$ ()A$ )
(declare-fun t$ ()A_tree$ )
(declare-fun uu$ (A_tree$ A$ A$ Nat$ Nat$ )A_nat_fun$ )
(declare-fun freq$ (A_tree$ )A_nat_fun$ )
(declare-fun zero$ ()Nat$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_nat_fun$ A$ )Nat$ )
(declare-fun sibling$ (A_tree$ A$ )A$ )
(declare-fun alphabet$ (A_tree$ )A_set$ )
(declare-fun fun_app$a (A_a_tree_fun$ A$ )A_tree$ )
(declare-fun swapSyms$ (A_tree$ A$ )A_a_tree_fun$ )
(declare-fun consistent$ (A_tree$ )Bool )
(declare-fun swapLeaves$ (A_tree$ Nat$ A$ Nat$ )A_a_tree_fun$ )
(declare-fun swapFourSyms$ (A_tree$ A$ A$ A$ A$ )A_tree$ )
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ )(?v3 Nat$ )(?v4 Nat$ )(?v5 A$ ))(! (= (fun_app$ (uu$ ?v0 ?v1 ?v2 ?v3 ?v4 )?v5 )(ite (= ?v5 ?v1 )(ite (member$ ?v2 (alphabet$ ?v0 ))?v3 zero$ )(ite (= ?v5 ?v2 )(ite (member$ ?v1 (alphabet$ ?v0 ))?v4 zero$ )(fun_app$ (freq$ ?v0 )?v5 )))):pattern ((fun_app$ (uu$ ?v0 ?v1 ?v2 ?v3 ?v4 )?v5 )))):named a0 ))
(assert (! (not (= (freq$ (swapFourSyms$ t$ a$ b$ c$ d$ ))(freq$ t$ ))):named a1 ))
(assert (! (consistent$ t$ ):named a2 ))
(assert (! (member$ a$ (alphabet$ t$ )):named a3 ))
(assert (! (member$ b$ (alphabet$ t$ )):named a4 ))
(assert (! (member$ c$ (alphabet$ t$ )):named a5 ))
(assert (! (member$ d$ (alphabet$ t$ )):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A$ )(?v3 A$ )(?v4 A$ ))(=> (and (member$ ?v0 (alphabet$ ?v1 ))(and (member$ ?v2 (alphabet$ ?v1 ))(and (member$ ?v3 (alphabet$ ?v1 ))(member$ ?v4 (alphabet$ ?v1 )))))(= (alphabet$ (swapFourSyms$ ?v1 ?v0 ?v2 ?v3 ?v4 ))(alphabet$ ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ )(?v3 A$ )(?v4 A$ ))(=> (consistent$ ?v0 )(consistent$ (swapFourSyms$ ?v0 ?v1 ?v2 ?v3 ?v4 )))):named a8 ))
(assert (! (forall ((?v0 A_tree$ ))(exists ((?v1 A$ ))(member$ ?v1 (alphabet$ ?v0 )))):named a9 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ ))(=> (and (consistent$ ?v0 )(and (member$ ?v1 (alphabet$ ?v0 ))(member$ ?v2 (alphabet$ ?v0 ))))(= (freq$ (fun_app$a (swapSyms$ ?v0 ?v1 )?v2 ))(freq$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ ))(=> (consistent$ ?v0 )(= (fun_app$a (swapLeaves$ ?v0 (fun_app$ (freq$ ?v0 )?v1 )?v1 (fun_app$ (freq$ ?v0 )?v1 ))?v1 )?v0 ))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(! (=> (not (member$ ?v0 (alphabet$ ?v1 )))(= (fun_app$ (freq$ ?v1 )?v0 )zero$ )):pattern ((fun_app$ (freq$ ?v1 )?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ )(?v3 A$ )(?v4 A$ ))(! (= (swapFourSyms$ ?v0 ?v1 ?v2 ?v3 ?v4 )(ite (= ?v1 ?v4 )(fun_app$a (swapSyms$ ?v0 ?v2 )?v3 )(ite (= ?v2 ?v3 )(fun_app$a (swapSyms$ ?v0 ?v1 )?v4 )(fun_app$a (swapSyms$ (fun_app$a (swapSyms$ ?v0 ?v1 )?v3 )?v2 )?v4 )))):pattern ((swapFourSyms$ ?v0 ?v1 ?v2 ?v3 ?v4 )))):named a13 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ ))(! (=> (consistent$ ?v0 )(= (fun_app$a (swapSyms$ ?v0 ?v1 )?v1 )?v0 )):pattern ((swapSyms$ ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A$ ))(=> (and (member$ ?v0 (alphabet$ ?v1 ))(member$ ?v2 (alphabet$ ?v1 )))(= (alphabet$ (fun_app$a (swapSyms$ ?v1 ?v0 )?v2 ))(alphabet$ ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 Nat$ )(?v3 Nat$ ))(! (=> (not (member$ ?v0 (alphabet$ ?v1 )))(= (fun_app$a (swapLeaves$ ?v1 ?v2 ?v0 ?v3 )?v0 )?v1 )):pattern ((swapLeaves$ ?v1 ?v2 ?v0 ?v3 )))):named a16 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ )(?v3 Nat$ )(?v4 Nat$ ))(=> (and (consistent$ ?v0 )(not (= ?v1 ?v2 )))(= (freq$ (fun_app$a (swapLeaves$ ?v0 ?v3 ?v1 ?v4 )?v2 ))(uu$ ?v0 ?v1 ?v2 ?v3 ?v4 )))):named a17 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ ))(=> (consistent$ ?v0 )(consistent$ (fun_app$a (swapSyms$ ?v0 ?v1 )?v2 )))):named a18 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ ))(=> (consistent$ ?v0 )(= (sibling$ ?v0 (sibling$ ?v0 ?v1 ))?v1 ))):named a19 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 Nat$ )(?v2 A$ )(?v3 Nat$ )(?v4 A$ ))(=> (consistent$ ?v0 )(consistent$ (fun_app$a (swapLeaves$ ?v0 ?v1 ?v2 ?v3 )?v4 )))):named a20 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(! (=> (not (member$ ?v0 (alphabet$ ?v1 )))(= (sibling$ ?v1 ?v0 )?v0 )):pattern ((sibling$ ?v1 ?v0 )))):named a21 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ )(?v3 Nat$ )(?v4 Nat$ ))(=> (and (consistent$ ?v0 )(and (not (= (sibling$ ?v0 ?v1 )?v1 ))(not (= ?v2 ?v1 ))))(= (sibling$ (fun_app$a (swapLeaves$ ?v0 ?v3 ?v2 ?v4 )(sibling$ ?v0 ?v1 ))?v2 )?v1 ))):named a22 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A$ ))(=> (and (consistent$ ?v0 )(and (not (= (sibling$ ?v0 ?v1 )?v1 ))(not (= ?v2 ?v1 ))))(= (sibling$ (fun_app$a (swapSyms$ ?v0 ?v2 )(sibling$ ?v0 ?v1 ))?v2 )?v1 ))):named a23 ))
(check-sat )
;(get-unsat-core )
