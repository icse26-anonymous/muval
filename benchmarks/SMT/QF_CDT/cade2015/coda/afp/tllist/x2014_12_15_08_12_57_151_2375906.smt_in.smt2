;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort B_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort B_a_b_tllist_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_b_tllist$ (tNil$ (terminal$ B$ ))(tCons$ (thd$ A$ )(ttl$ A_b_tllist$ )))))
(declare-fun uu$ ()B_a_b_tllist_fun$ )
(declare-fun xs$ ()A_b_tllist$ )
(declare-fun tmap$ (A_a_fun$ B_b_fun$ A_b_tllist$ )A_b_tllist$ )
(declare-fun member$ (B$ B_set$ )Bool )
(declare-fun fun_app$ (B_a_b_tllist_fun$ B$ )A_b_tllist$ )
(declare-fun tappend$ (A_b_tllist$ B_a_b_tllist_fun$ )A_b_tllist$ )
(declare-fun fun_app$a (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$b (B_b_bool_fun_fun$ B$ )B_bool_fun$ )
(declare-fun fun_app$c (B_b_fun$ B$ )B$ )
(declare-fun fun_app$d (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$e (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun pred_tllist$ (A_bool_fun$ B_bool_fun$ A_b_tllist$ )Bool )
(declare-fun set2_tllist$ (A_b_tllist$ )B_set$ )
(declare-fun tllist_all2$ (A_a_bool_fun_fun$ B_b_bool_fun_fun$ A_b_tllist$ A_b_tllist$ )Bool )
(assert (! (forall ((?v0 B$ ))(! (= (fun_app$ uu$ ?v0 )(tNil$ ?v0 )):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (not (= (tappend$ xs$ uu$ )xs$ )):named a1 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(= (= (tNil$ ?v0 )(tNil$ ?v1 ))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 B$ )(?v1 B_a_b_tllist_fun$ ))(! (= (tappend$ (tNil$ ?v0 )?v1 )(fun_app$ ?v1 ?v0 )):pattern ((tappend$ (tNil$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B$ ))(! (= (pred_tllist$ ?v0 ?v1 (tNil$ ?v2 ))(fun_app$a ?v1 ?v2 )):pattern ((pred_tllist$ ?v0 ?v1 (tNil$ ?v2 ))))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 B_a_b_tllist_fun$ ))(! (= (tappend$ (tCons$ ?v0 ?v1 )?v2 )(tCons$ ?v0 (tappend$ ?v1 ?v2 ))):pattern ((tappend$ (tCons$ ?v0 ?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 B$ ))(member$ ?v0 (set2_tllist$ (tNil$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B$ )(?v3 B$ ))(! (= (tllist_all2$ ?v0 ?v1 (tNil$ ?v2 )(tNil$ ?v3 ))(fun_app$a (fun_app$b ?v1 ?v2 )?v3 )):pattern ((tllist_all2$ ?v0 ?v1 (tNil$ ?v2 )(tNil$ ?v3 ))))):named a7 ))
(assert (! (forall ((?v0 B$ ))(! (= (ttl$ (tNil$ ?v0 ))(tNil$ ?v0 )):pattern ((tNil$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 B$ ))(! (= (terminal$ (tNil$ ?v0 ))?v0 ):pattern ((tNil$ ?v0 )))):named a9 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_b_fun$ )(?v2 A_b_tllist$ )(?v3 B$ ))(= (= (tmap$ ?v0 ?v1 ?v2 )(tNil$ ?v3 ))(exists ((?v4 B$ ))(and (= ?v2 (tNil$ ?v4 ))(= (fun_app$c ?v1 ?v4 )?v3 ))))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ )(?v3 A_b_tllist$ ))(= (= (tCons$ ?v0 ?v1 )(tCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a11 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 A$ )(?v3 A_b_tllist$ )(?v4 A$ )(?v5 A_b_tllist$ ))(! (= (tllist_all2$ ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$ ?v4 ?v5 ))(and (fun_app$d (fun_app$e ?v0 ?v2 )?v4 )(tllist_all2$ ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$ ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$ ?v4 ?v5 ))))):named a12 ))
(check-sat )
;(get-unsat-core )
