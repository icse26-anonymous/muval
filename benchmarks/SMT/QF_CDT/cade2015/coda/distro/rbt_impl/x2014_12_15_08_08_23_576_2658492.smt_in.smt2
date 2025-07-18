;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_b_prod_set$ 0 )
(declare-sort A_b_prod$ 0)
(declare-sort A_b_prod_list$ 0)
(declare-sort Color$ 0)
(declare-sort A_b_rbt$ 0)
(declare-sort A_list$ 0)
(declare-fun fst$ (A_b_prod$)A$)
(declare-fun snd$ (A_b_prod$)B$)
(declare-fun pair$ (A$ B$ )A_b_prod$)
(declare-fun nil$ ()A_b_prod_list$)
(declare-fun hd$ (A_b_prod_list$)A_b_prod$)
(declare-fun tl$ (A_b_prod_list$)A_b_prod_list$)
(declare-fun cons$ (A_b_prod$ A_b_prod_list$ )A_b_prod_list$)
(declare-fun r$ ()Color$)
(declare-fun b$ ()Color$)
(declare-fun empty$ ()A_b_rbt$)
(declare-fun select$ (A_b_rbt$)Color$)
(declare-fun selecta$ (A_b_rbt$)A_b_rbt$)
(declare-fun selectb$ (A_b_rbt$)A$)
(declare-fun selectc$ (A_b_rbt$)B$)
(declare-fun selectd$ (A_b_rbt$)A_b_rbt$)
(declare-fun branch$ (Color$ A_b_rbt$ A$ B$ A_b_rbt$ )A_b_rbt$)
(declare-fun nil$a ()A_list$)
(declare-fun hd$a (A_list$)A$)
(declare-fun tl$a (A_list$)A_list$)
(declare-fun cons$a (A$ A_list$ )A_list$)
(declare-fun a$ ()A$ )
(declare-fun k$ ()A$ )
(declare-fun l$ ()A_b_rbt$ )
(declare-fun v$ ()B$ )
(declare-fun b$a ()B$ )
(declare-fun r$a ()A_b_rbt$ )
(declare-fun one$ ()Nat$ )
(declare-fun set$ (A_b_prod_list$ )A_b_prod_set$ )
(declare-fun inv1$ (A_b_rbt$ )Bool )
(declare-fun keys$ (A_b_rbt$ )A_list$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun set$a (A_list$ )A_set$ )
(declare-fun inv1l$ (A_b_rbt$ )Bool )
(declare-fun paint$ (Color$ A_b_rbt$ )A_b_rbt$ )
(declare-fun member$ (A_b_prod$ A_b_prod_set$ )Bool )
(declare-fun balance$ (A_b_rbt$ A$ B$ A_b_rbt$ )A_b_rbt$ )
(declare-fun bheight$ (A_b_rbt$ )Nat$ )
(declare-fun entries$ (A_b_rbt$ )A_b_prod_list$ )
(declare-fun member$a (A$ A_set$ )Bool )
(declare-fun balance_left$ (A_b_rbt$ A$ B$ A_b_rbt$ )A_b_rbt$ )
(assert (! (not (= (member$ (pair$ k$ v$ )(set$ (entries$ (balance_left$ l$ a$ b$a r$a ))))(or (member$ (pair$ k$ v$ )(set$ (entries$ l$ )))(or (and (= k$ a$ )(= v$ b$a ))(member$ (pair$ k$ v$ )(set$ (entries$ r$a ))))))):named a0 ))
(assert (! (inv1l$ l$ ):named a1 ))
(assert (! (inv1$ r$a ):named a2 ))
(assert (! (= (plus$ (bheight$ l$ )one$ )(bheight$ r$a )):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 B$ )(?v2 A$ )(?v3 B$ ))(= (= (pair$ ?v0 ?v1 )(pair$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 B$ )(?v2 A$ )(?v3 B$ ))(= (= (pair$ ?v0 ?v1 )(pair$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 B$ )(?v2 Color$ )(?v3 A_b_rbt$ ))(= (member$ (pair$ ?v0 ?v1 )(set$ (entries$ (paint$ ?v2 ?v3 ))))(member$ (pair$ ?v0 ?v1 )(set$ (entries$ ?v3 ))))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_rbt$ ))(= (member$a ?v0 (set$a (keys$ ?v1 )))(exists ((?v2 B$ ))(member$ (pair$ ?v0 ?v2 )(set$ (entries$ ?v1 )))))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 B$ )(?v2 A_b_rbt$ ))(=> (member$ (pair$ ?v0 ?v1 )(set$ (entries$ ?v2 )))(member$a ?v0 (set$a (keys$ ?v2 ))))):named a8 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ ))(=> (and (inv1l$ ?v0 )(inv1$ ?v1 ))(inv1l$ (balance_left$ ?v0 ?v2 ?v3 ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 B$ )(?v2 A_b_rbt$ )(?v3 A$ )(?v4 B$ )(?v5 A_b_rbt$ ))(= (member$ (pair$ ?v0 ?v1 )(set$ (entries$ (balance$ ?v2 ?v3 ?v4 ?v5 ))))(or (member$ (pair$ ?v0 ?v1 )(set$ (entries$ ?v2 )))(or (and (= ?v0 ?v3 )(= ?v1 ?v4 ))(member$ (pair$ ?v0 ?v1 )(set$ (entries$ ?v5 ))))))):named a10 ))
(assert (! (forall ((?v0 A_b_prod$ ))(=> (forall ((?v1 A$ )(?v2 B$ ))(=> (= ?v0 (pair$ ?v1 ?v2 ))false ))false )):named a11 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ ))(=> (and (inv1l$ ?v0 )(inv1l$ ?v1 ))(inv1$ (balance$ ?v0 ?v2 ?v3 ?v1 )))):named a12 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 Color$ ))(=> (inv1l$ ?v0 )(inv1l$ (paint$ ?v1 ?v0 )))):named a13 ))
(check-sat )
;(get-unsat-core )
