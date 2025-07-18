;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_b_prod_set$ 0 )
(declare-sort A_a_b_prod_fun$ 0 )
(declare-sort A_b_prod_a_fun$ 0 )
(declare-sort A_b_prod_a_b_prod_fun$ 0 )
(declare-sort A_b_prod$ 0)
(declare-sort A_b_prod_list$ 0)
(declare-sort Color$ 0)
(declare-sort A_b_rbt$ 0)
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
(declare-fun k$ ()A$ )
(declare-fun t$ ()A_b_rbt$ )
(declare-fun v$ ()B$ )
(declare-fun uu$ ()A_b_prod_a_fun$ )
(declare-fun set$ (A_b_prod_list$ )A_b_prod_set$ )
(declare-fun image$ (A_b_prod_a_fun$ A_b_prod_set$ )A_set$ )
(declare-fun image$a (A_a_b_prod_fun$ A_set$ )A_b_prod_set$ )
(declare-fun image$b (A_b_prod_a_b_prod_fun$ A_b_prod_set$ )A_b_prod_set$ )
(declare-fun image$c (A_a_fun$ A_set$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun entries$ (A_b_rbt$ )A_b_prod_list$ )
(declare-fun fun_app$ (A_b_prod_a_fun$ A_b_prod$ )A$ )
(declare-fun member$a (A_b_prod$ A_b_prod_set$ )Bool )
(declare-fun fun_app$a (A_a_b_prod_fun$ A$ )A_b_prod$ )
(declare-fun fun_app$b (A_b_prod_a_b_prod_fun$ A_b_prod$ )A_b_prod$ )
(declare-fun fun_app$c (A_a_fun$ A$ )A$ )
(assert (! (forall ((?v0 A_b_prod$ ))(! (= (fun_app$ uu$ ?v0 )(fst$ ?v0 )):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (not (member$ (fst$ (pair$ k$ v$ ))(image$ uu$ (set$ (entries$ t$ ))))):named a1 ))
(assert (! (forall ((?v0 A_b_prod$ )(?v1 A_a_b_prod_fun$ )(?v2 A_set$ ))(= (member$a ?v0 (image$a ?v1 ?v2 ))(exists ((?v3 A$ ))(and (member$ ?v3 ?v2 )(= ?v0 (fun_app$a ?v1 ?v3 )))))):named a2 ))
(assert (! (forall ((?v0 A_b_prod$ )(?v1 A_b_prod_a_b_prod_fun$ )(?v2 A_b_prod_set$ ))(= (member$a ?v0 (image$b ?v1 ?v2 ))(exists ((?v3 A_b_prod$ ))(and (member$a ?v3 ?v2 )(= ?v0 (fun_app$b ?v1 ?v3 )))))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_prod_a_fun$ )(?v2 A_b_prod_set$ ))(= (member$ ?v0 (image$ ?v1 ?v2 ))(exists ((?v3 A_b_prod$ ))(and (member$a ?v3 ?v2 )(= ?v0 (fun_app$ ?v1 ?v3 )))))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_fun$ )(?v2 A_set$ ))(= (member$ ?v0 (image$c ?v1 ?v2 ))(exists ((?v3 A$ ))(and (member$ ?v3 ?v2 )(= ?v0 (fun_app$c ?v1 ?v3 )))))):named a5 ))
(check-sat )
;(get-unsat-core )
