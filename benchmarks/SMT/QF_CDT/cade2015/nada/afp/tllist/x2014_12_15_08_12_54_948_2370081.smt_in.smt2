;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort C$ 0 )
(declare-sort A_set$ 0 )
(declare-sort B_set$ 0 )
(declare-sort C_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort C_bool_fun$ 0 )
(declare-sort C_a_b_tllist_fun$ 0 )
(declare-sort A_b_tllist_bool_fun$ 0 )
(declare-sort A_c_tllist_bool_fun$ 0 )
(declare-sort A_a_b_tllist_bool_fun_fun$ 0 )
(declare-sort A_a_c_tllist_bool_fun_fun$ 0 )
(declare-sort A_b_tllist$ 0)
(declare-sort A_c_tllist$ 0)
(declare-fun terminal$ (A_b_tllist$)B$)
(declare-fun tNil$ (B$ )A_b_tllist$)
(declare-fun thd$ (A_b_tllist$)A$)
(declare-fun ttl$ (A_b_tllist$)A_b_tllist$)
(declare-fun tCons$ (A$ A_b_tllist$ )A_b_tllist$)
(declare-fun terminal$a (A_c_tllist$)C$)
(declare-fun tNil$a (C$ )A_c_tllist$)
(declare-fun thd$a (A_c_tllist$)A$)
(declare-fun ttl$a (A_c_tllist$)A_c_tllist$)
(declare-fun tCons$a (A$ A_c_tllist$ )A_c_tllist$)
(declare-fun a$ ()A$ )
(declare-fun f$ ()C_a_b_tllist_fun$ )
(declare-fun tr$ ()A_c_tllist$ )
(declare-fun tset$ (A_c_tllist$ )A_set$ )
(declare-fun tset$a (A_b_tllist$ )A_set$ )
(declare-fun member$ (C$ C_set$ )Bool )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun member$a (B$ B_set$ )Bool )
(declare-fun member$b (A$ A_set$ )Bool )
(declare-fun tappend$ (A_c_tllist$ C_a_b_tllist_fun$ )A_b_tllist$ )
(declare-fun fun_app$a (C_a_b_tllist_fun$ C$ )A_b_tllist$ )
(declare-fun fun_app$b (A_c_tllist_bool_fun$ A_c_tllist$ )Bool )
(declare-fun fun_app$c (A_a_c_tllist_bool_fun_fun$ A$ )A_c_tllist_bool_fun$ )
(declare-fun fun_app$d (A_b_tllist_bool_fun$ A_b_tllist$ )Bool )
(declare-fun fun_app$e (A_a_b_tllist_bool_fun_fun$ A$ )A_b_tllist_bool_fun$ )
(declare-fun pred_tllist$ (A_bool_fun$ C_bool_fun$ A_c_tllist$ )Bool )
(declare-fun set2_tllist$ (A_c_tllist$ )C_set$ )
(declare-fun pred_tllist$a (A_bool_fun$ B_bool_fun$ A_b_tllist$ )Bool )
(declare-fun set2_tllist$a (A_b_tllist$ )B_set$ )
(assert (! (not (= (tappend$ (tCons$a a$ tr$ )f$ )(tCons$ a$ (tappend$ tr$ f$ )))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A_c_tllist$ )(?v2 A$ )(?v3 A_c_tllist$ ))(= (= (tCons$a ?v0 ?v1 )(tCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a1 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ )(?v3 A_b_tllist$ ))(= (= (tCons$ ?v0 ?v1 )(tCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a2 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 C_bool_fun$ )(?v2 A$ )(?v3 A_c_tllist$ ))(! (= (pred_tllist$ ?v0 ?v1 (tCons$a ?v2 ?v3 ))(and (fun_app$ ?v0 ?v2 )(pred_tllist$ ?v0 ?v1 ?v3 ))):pattern ((pred_tllist$ ?v0 ?v1 (tCons$a ?v2 ?v3 ))))):named a3 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_bool_fun$ )(?v2 A$ )(?v3 A_b_tllist$ ))(! (= (pred_tllist$a ?v0 ?v1 (tCons$ ?v2 ?v3 ))(and (fun_app$ ?v0 ?v2 )(pred_tllist$a ?v0 ?v1 ?v3 ))):pattern ((pred_tllist$a ?v0 ?v1 (tCons$ ?v2 ?v3 ))))):named a4 ))
(assert (! (forall ((?v0 C$ )(?v1 C_a_b_tllist_fun$ ))(! (= (tappend$ (tNil$a ?v0 )?v1 )(fun_app$a ?v1 ?v0 )):pattern ((tappend$ (tNil$a ?v0 )?v1 )))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_c_tllist$ ))(! (= (terminal$a (tCons$a ?v0 ?v1 ))(terminal$a ?v1 )):pattern ((tCons$a ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (terminal$ (tCons$ ?v0 ?v1 ))(terminal$ ?v1 )):pattern ((tCons$ ?v0 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_c_tllist$ ))(! (= (set2_tllist$ (tCons$a ?v0 ?v1 ))(set2_tllist$ ?v1 )):pattern ((tCons$a ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (set2_tllist$a (tCons$ ?v0 ?v1 ))(set2_tllist$a ?v1 )):pattern ((tCons$ ?v0 ?v1 )))):named a9 ))
(assert (! (forall ((?v0 C$ )(?v1 A_c_tllist$ )(?v2 A$ ))(=> (member$ ?v0 (set2_tllist$ ?v1 ))(member$ ?v0 (set2_tllist$ (tCons$a ?v2 ?v1 ))))):named a10 ))
(assert (! (forall ((?v0 B$ )(?v1 A_b_tllist$ )(?v2 A$ ))(=> (member$a ?v0 (set2_tllist$a ?v1 ))(member$a ?v0 (set2_tllist$a (tCons$ ?v2 ?v1 ))))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_c_tllist$ ))(! (= (thd$a (tCons$a ?v0 ?v1 ))?v0 ):pattern ((tCons$a ?v0 ?v1 )))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (thd$ (tCons$ ?v0 ?v1 ))?v0 ):pattern ((tCons$ ?v0 ?v1 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_c_tllist$ )(?v2 A_a_c_tllist_bool_fun_fun$ ))(=> (and (member$b ?v0 (tset$ ?v1 ))(and (forall ((?v3 A$ )(?v4 A_c_tllist$ ))(fun_app$b (fun_app$c ?v2 ?v3 )(tCons$a ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_c_tllist$ )(?v5 A$ ))(=> (and (member$b ?v5 (tset$ ?v4 ))(fun_app$b (fun_app$c ?v2 ?v5 )?v4 ))(fun_app$b (fun_app$c ?v2 ?v5 )(tCons$a ?v3 ?v4 ))))))(fun_app$b (fun_app$c ?v2 ?v0 )?v1 ))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A_a_b_tllist_bool_fun_fun$ ))(=> (and (member$b ?v0 (tset$a ?v1 ))(and (forall ((?v3 A$ )(?v4 A_b_tllist$ ))(fun_app$d (fun_app$e ?v2 ?v3 )(tCons$ ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_b_tllist$ )(?v5 A$ ))(=> (and (member$b ?v5 (tset$a ?v4 ))(fun_app$d (fun_app$e ?v2 ?v5 )?v4 ))(fun_app$d (fun_app$e ?v2 ?v5 )(tCons$ ?v3 ?v4 ))))))(fun_app$d (fun_app$e ?v2 ?v0 )?v1 ))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_c_tllist$ ))(=> (and (member$b ?v0 (tset$ ?v1 ))(and (forall ((?v2 A_c_tllist$ ))(=> (= ?v1 (tCons$a ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_c_tllist$ ))(=> (and (= ?v1 (tCons$a ?v2 ?v3 ))(member$b ?v0 (tset$ ?v3 )))false ))))false )):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(=> (and (member$b ?v0 (tset$a ?v1 ))(and (forall ((?v2 A_b_tllist$ ))(=> (= ?v1 (tCons$ ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_b_tllist$ ))(=> (and (= ?v1 (tCons$ ?v2 ?v3 ))(member$b ?v0 (tset$a ?v3 )))false ))))false )):named a17 ))
(assert (! (forall ((?v0 A$ )(?v1 A_c_tllist$ )(?v2 A$ ))(=> (member$b ?v0 (tset$ ?v1 ))(member$b ?v0 (tset$ (tCons$a ?v2 ?v1 ))))):named a18 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ ))(=> (member$b ?v0 (tset$a ?v1 ))(member$b ?v0 (tset$a (tCons$ ?v2 ?v1 ))))):named a19 ))
(assert (! (forall ((?v0 C$ )(?v1 C$ ))(= (= (tNil$a ?v0 )(tNil$a ?v1 ))(= ?v0 ?v1 ))):named a20 ))
(check-sat )
;(get-unsat-core )
