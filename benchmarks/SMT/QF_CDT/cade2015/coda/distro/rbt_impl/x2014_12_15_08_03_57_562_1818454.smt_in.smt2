;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_rbt_bool_fun$ 0 )
(declare-sort B_option$ 0)
(declare-sort Color$ 0)
(declare-sort A_b_rbt$ 0)
(declare-sort A_list$ 0)
(declare-fun none$ ()B_option$)
(declare-fun the$ (B_option$)B$)
(declare-fun some$ (B$ )B_option$)
(declare-fun r$ ()Color$)
(declare-fun b$ ()Color$)
(declare-fun empty$ ()A_b_rbt$)
(declare-fun select$ (A_b_rbt$)Color$)
(declare-fun selecta$ (A_b_rbt$)A_b_rbt$)
(declare-fun selectb$ (A_b_rbt$)A$)
(declare-fun selectc$ (A_b_rbt$)B$)
(declare-fun selectd$ (A_b_rbt$)A_b_rbt$)
(declare-fun branch$ (Color$ A_b_rbt$ A$ B$ A_b_rbt$ )A_b_rbt$)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun k$ ()A$ )
(declare-fun t$ ()A_b_rbt$ )
(declare-fun set$ (A_list$ )A_set$ )
(declare-fun keys$ (A_b_rbt$ )A_list$ )
(declare-fun less$ ()A_a_bool_fun_fun$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_b_rbt_bool_fun$ A_b_rbt$ )Bool )
(declare-fun lexordp$ (A_a_bool_fun_fun$ A_list$ A_list$ )Bool )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$b (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun lessThan$ (A_a_bool_fun_fun$ A$ )A_set$ )
(declare-fun rbt_less$ (A_a_bool_fun_fun$ A$ )A_b_rbt_bool_fun$ )
(declare-fun lexordp_eq$ (A_a_bool_fun_fun$ A_list$ A_list$ )Bool )
(declare-fun rbt_lookup$ (A_a_bool_fun_fun$ A_b_rbt$ A$ )B_option$ )
(declare-fun rbt_sorted$ (A_a_bool_fun_fun$ )A_b_rbt_bool_fun$ )
(declare-fun greaterThan$ (A_a_bool_fun_fun$ A$ )A_set$ )
(declare-fun greaterThanLessThan$ (A_a_bool_fun_fun$ A$ A$ )A_set$ )
(assert (! (not (= (rbt_lookup$ less$ t$ k$ )none$ )):named a0 ))
(assert (! (fun_app$ (rbt_less$ less$ k$ )t$ ):named a1 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$a (fun_app$b less$ ?v0 )?v1 )(= ?v1 ?v2 ))(fun_app$a (fun_app$b less$ ?v0 )?v2 ))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (= ?v0 ?v1 )(fun_app$a (fun_app$b less$ ?v1 )?v2 ))(fun_app$a (fun_app$b less$ ?v0 )?v2 ))):named a3 ))
(assert (! (forall ((?v0 A$ ))(! (= (rbt_lookup$ less$ empty$ ?v0 )none$ ):pattern ((rbt_lookup$ less$ empty$ ?v0 )))):named a4 ))
(assert (! (forall ((?v0 A_list$ ))(lexordp_eq$ less$ ?v0 ?v0 )):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(= (member$ ?v0 (greaterThanLessThan$ less$ ?v1 ?v2 ))(and (fun_app$a (fun_app$b less$ ?v1 )?v0 )(fun_app$a (fun_app$b less$ ?v0 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 A_list$ ))(=> (forall ((?v1 A$ ))(not (fun_app$a (fun_app$b less$ ?v1 )?v1 )))(not (lexordp$ less$ ?v0 ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ (rbt_less$ less$ ?v0 )empty$ )true ):pattern ((rbt_less$ less$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (member$ ?v0 (lessThan$ less$ ?v1 ))(fun_app$a (fun_app$b less$ ?v0 )?v1 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (member$ ?v0 (greaterThan$ less$ ?v1 ))(fun_app$a (fun_app$b less$ ?v1 )?v0 ))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 Color$ )(?v2 A_b_rbt$ )(?v3 A$ )(?v4 B$ )(?v5 A_b_rbt$ ))(! (= (fun_app$ (rbt_less$ less$ ?v0 )(branch$ ?v1 ?v2 ?v3 ?v4 ?v5 ))(and (fun_app$a (fun_app$b less$ ?v3 )?v0 )(and (fun_app$ (rbt_less$ less$ ?v0 )?v2 )(fun_app$ (rbt_less$ less$ ?v0 )?v5 )))):pattern ((fun_app$ (rbt_less$ less$ ?v0 )(branch$ ?v1 ?v2 ?v3 ?v4 ?v5 ))))):named a11 ))
(assert (! (forall ((?v0 B_option$ ))(=> (and (=> (= ?v0 none$ )false )(=> (not (= ?v0 none$ ))false ))false )):named a12 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ ))(! (= (rbt_lookup$ ?v0 empty$ ?v1 )none$ ):pattern ((rbt_lookup$ ?v0 empty$ ?v1 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_rbt$ ))(= (fun_app$ (rbt_less$ less$ ?v0 )?v1 )(forall ((?v2 A$ ))(=> (member$ ?v2 (set$ (keys$ ?v1 )))(fun_app$a (fun_app$b less$ ?v2 )?v0 ))))):named a14 ))
(assert (! (= (fun_app$ (rbt_sorted$ less$ )empty$ )true ):named a15 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(=> (lexordp$ less$ ?v0 ?v1 )(lexordp_eq$ less$ ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 Color$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ )(?v5 Color$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ ))(= (= (branch$ ?v0 ?v1 ?v2 ?v3 ?v4 )(branch$ ?v5 ?v6 ?v7 ?v8 ?v9 ))(and (= ?v0 ?v5 )(and (= ?v1 ?v6 )(and (= ?v2 ?v7 )(and (= ?v3 ?v8 )(= ?v4 ?v9 ))))))):named a17 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ ))(! (= (fun_app$ (rbt_sorted$ ?v0 )empty$ )true ):pattern ((rbt_sorted$ ?v0 )))):named a18 ))
(check-sat )
;(get-unsat-core )
