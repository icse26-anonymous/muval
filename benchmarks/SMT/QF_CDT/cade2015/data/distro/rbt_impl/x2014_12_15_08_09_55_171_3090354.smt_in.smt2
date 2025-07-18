;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_b_prod_set$ 0 )
(declare-datatypes ()((Color$ (r$ )(b$ ))(A_b_rbt$ (empty$ )(branch$ (select$ Color$ )(selecta$ A_b_rbt$ )(selectb$ A$ )(selectc$ B$ )(selectd$ A_b_rbt$ )))(A_b_prod$ (pair$ (fst$ A$ )(snd$ B$ )))(A_b_prod_list$ (nil$ )(cons$ (hd$ A_b_prod$ )(tl$ A_b_prod_list$ )))))
(declare-fun a$ ()A_b_rbt$ )
(declare-fun c$ ()A_b_rbt$ )
(declare-fun d$ ()A_b_rbt$ )
(declare-fun k$ ()A$ )
(declare-fun l$ ()A_b_rbt$ )
(declare-fun s$ ()A$ )
(declare-fun v$ ()B$ )
(declare-fun x$ ()B$ )
(declare-fun y$ ()B$ )
(declare-fun b$a ()A_b_rbt$ )
(declare-fun ka$ ()A$ )
(declare-fun r$a ()A_b_rbt$ )
(declare-fun set$ (A_b_prod_list$ )A_b_prod_set$ )
(declare-fun inv1$ (A_b_rbt$ )Bool )
(declare-fun inv2$ (A_b_rbt$ )Bool )
(declare-fun member$ (A_b_prod$ A_b_prod_set$ )Bool )
(declare-fun bheight$ (A_b_rbt$ )Nat$ )
(declare-fun combine$ (A_b_rbt$ A_b_rbt$ )A_b_rbt$ )
(declare-fun entries$ (A_b_rbt$ )A_b_prod_list$ )
(assert (! (not (= (bheight$ (combine$ b$a c$ ))(bheight$ b$a ))):named a0 ))
(assert (! (inv1$ l$ ):named a1 ))
(assert (! (inv1$ r$a ):named a2 ))
(assert (! (inv2$ l$ ):named a3 ))
(assert (! (inv2$ r$a ):named a4 ))
(assert (! (inv1$ (branch$ b$ c$ s$ y$ d$ )):named a5 ))
(assert (! (inv1$ (branch$ b$ a$ ka$ x$ b$a )):named a6 ))
(assert (! (inv2$ (branch$ b$ c$ s$ y$ d$ )):named a7 ))
(assert (! (inv2$ (branch$ b$ a$ ka$ x$ b$a )):named a8 ))
(assert (! (= (bheight$ l$ )(bheight$ r$a )):named a9 ))
(assert (! (= (bheight$ (branch$ b$ a$ ka$ x$ b$a ))(bheight$ (branch$ b$ c$ s$ y$ d$ ))):named a10 ))
(assert (! (=> (and (inv2$ b$a )(and (inv2$ c$ )(and (= (bheight$ b$a )(bheight$ c$ ))(and (inv1$ b$a )(inv1$ c$ )))))(= (member$ (pair$ k$ v$ )(set$ (entries$ (combine$ b$a c$ ))))(or (member$ (pair$ k$ v$ )(set$ (entries$ b$a )))(member$ (pair$ k$ v$ )(set$ (entries$ c$ )))))):named a11 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A_b_rbt$ ))(=> (and (inv2$ ?v0 )(and (inv2$ ?v1 )(= (bheight$ ?v0 )(bheight$ ?v1 ))))(= (bheight$ (combine$ ?v0 ?v1 ))(bheight$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A_b_rbt$ ))(=> (and (inv2$ ?v0 )(and (inv2$ ?v1 )(= (bheight$ ?v0 )(bheight$ ?v1 ))))(inv2$ (combine$ ?v0 ?v1 )))):named a13 ))
(assert (! (forall ((?v0 Color$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ )(?v5 Color$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ ))(= (= (branch$ ?v0 ?v1 ?v2 ?v3 ?v4 )(branch$ ?v5 ?v6 ?v7 ?v8 ?v9 ))(and (= ?v0 ?v5 )(and (= ?v1 ?v6 )(and (= ?v2 ?v7 )(and (= ?v3 ?v8 )(= ?v4 ?v9 ))))))):named a14 ))
(assert (! (forall ((?v0 Color$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ ))(! (= (inv2$ (branch$ ?v0 ?v1 ?v2 ?v3 ?v4 ))(and (inv2$ ?v1 )(and (inv2$ ?v4 )(= (bheight$ ?v1 )(bheight$ ?v4 ))))):pattern ((branch$ ?v0 ?v1 ?v2 ?v3 ?v4 )))):named a15 ))
(check-sat )
;(get-unsat-core )
