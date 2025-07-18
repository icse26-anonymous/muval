;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort B_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_b_tllist_b_fun$ 0 )
(declare-sort A_b_tllist_bool_fun$ 0 )
(declare-sort A_a_b_tllist_b_fun_fun$ 0 )
(declare-sort A_b_tllist_a_b_tllist_bool_fun_fun$ 0 )
(declare-sort A_b_tllist$ 0)
(declare-fun terminal$ (A_b_tllist$)B$)
(declare-fun tNil$ (B$ )A_b_tllist$)
(declare-fun thd$ (A_b_tllist$)A$)
(declare-fun ttl$ (A_b_tllist$)A_b_tllist$)
(declare-fun tCons$ (A$ A_b_tllist$ )A_b_tllist$)
(declare-fun x$ ()A_b_tllist$ )
(declare-fun uu$ ()B_b_fun$ )
(declare-fun uua$ ()A_a_b_tllist_b_fun_fun$ )
(declare-fun tmap$ (A_a_fun$ B_b_fun$ A_b_tllist$ )A_b_tllist$ )
(declare-fun member$ (B$ B_set$ )Bool )
(declare-fun fun_app$ (B_b_fun$ B$ )B$ )
(declare-fun is_TNil$ (A_b_tllist$ )Bool )
(declare-fun fun_app$a (A_a_b_tllist_b_fun_fun$ A$ )A_b_tllist_b_fun$ )
(declare-fun fun_app$b (A_b_tllist_b_fun$ A_b_tllist$ )B$ )
(declare-fun fun_app$c (A_b_tllist_bool_fun$ A_b_tllist$ )Bool )
(declare-fun fun_app$d (A_b_tllist_a_b_tllist_bool_fun_fun$ A_b_tllist$ )A_b_tllist_bool_fun$ )
(declare-fun terminal0$ ()A_b_tllist_b_fun$ )
(declare-fun case_tllist$ (B_b_fun$ A_a_b_tllist_b_fun_fun$ A_b_tllist$ )B$ )
(declare-fun set2_tllist$ (A_b_tllist$ )B_set$ )
(assert (! (forall ((?v0 B$ ))(! (= (fun_app$ uu$ ?v0 )?v0 ):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$a uua$ ?v0 )terminal0$ ):pattern ((fun_app$a uua$ ?v0 )))):named a1 ))
(assert (! (not (= (fun_app$b terminal0$ x$ )(terminal$ x$ ))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (terminal$ (tCons$ ?v0 ?v1 ))(fun_app$b terminal0$ ?v1 )):pattern ((tCons$ ?v0 ?v1 )))):named a3 ))
(assert (! (forall ((?v0 B$ ))(! (= (terminal$ (tNil$ ?v0 ))?v0 ):pattern ((tNil$ ?v0 )))):named a4 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(= (terminal$ ?v0 )(case_tllist$ uu$ uua$ ?v0 ))):named a5 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (is_TNil$ ?v0 )(= (tNil$ (terminal$ ?v0 ))?v0 ))):named a6 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (is_TNil$ ?v0 )(member$ (terminal$ ?v0 )(set2_tllist$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_b_tllist$ )(?v1 A_a_fun$ )(?v2 B_b_fun$ ))(=> (is_TNil$ ?v0 )(= (terminal$ (tmap$ ?v1 ?v2 ?v0 ))(fun_app$ ?v2 (terminal$ ?v0 ))))):named a8 ))
(assert (! (forall ((?v0 A_b_tllist$ )(?v1 A_b_tllist$ ))(=> (and (= (is_TNil$ ?v0 )(is_TNil$ ?v1 ))(and (=> (and (is_TNil$ ?v0 )(is_TNil$ ?v1 ))(= (terminal$ ?v0 )(terminal$ ?v1 )))(=> (and (not (is_TNil$ ?v0 ))(not (is_TNil$ ?v1 )))(and (= (thd$ ?v0 )(thd$ ?v1 ))(= (ttl$ ?v0 )(ttl$ ?v1 ))))))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_b_tllist_a_b_tllist_bool_fun_fun$ )(?v1 A_b_tllist$ )(?v2 A_b_tllist$ ))(=> (and (fun_app$c (fun_app$d ?v0 ?v1 )?v2 )(forall ((?v3 A_b_tllist$ )(?v4 A_b_tllist$ ))(=> (fun_app$c (fun_app$d ?v0 ?v3 )?v4 )(and (= (is_TNil$ ?v3 )(is_TNil$ ?v4 ))(and (=> (and (is_TNil$ ?v3 )(is_TNil$ ?v4 ))(= (terminal$ ?v3 )(terminal$ ?v4 )))(=> (and (not (is_TNil$ ?v3 ))(not (is_TNil$ ?v4 )))(and (= (thd$ ?v3 )(thd$ ?v4 ))(or (fun_app$c (fun_app$d ?v0 (ttl$ ?v3 ))(ttl$ ?v4 ))(= (ttl$ ?v3 )(ttl$ ?v4 ))))))))))(= ?v1 ?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_b_tllist_a_b_tllist_bool_fun_fun$ )(?v1 A_b_tllist$ )(?v2 A_b_tllist$ ))(=> (and (fun_app$c (fun_app$d ?v0 ?v1 )?v2 )(forall ((?v3 A_b_tllist$ )(?v4 A_b_tllist$ ))(=> (fun_app$c (fun_app$d ?v0 ?v3 )?v4 )(and (= (is_TNil$ ?v3 )(is_TNil$ ?v4 ))(and (=> (and (is_TNil$ ?v3 )(is_TNil$ ?v4 ))(= (terminal$ ?v3 )(terminal$ ?v4 )))(=> (and (not (is_TNil$ ?v3 ))(not (is_TNil$ ?v4 )))(and (= (thd$ ?v3 )(thd$ ?v4 ))(fun_app$c (fun_app$d ?v0 (ttl$ ?v3 ))(ttl$ ?v4 )))))))))(= ?v1 ?v2 ))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ )(?v3 A_b_tllist$ ))(= (= (tCons$ ?v0 ?v1 )(tCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a12 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(= (= (tNil$ ?v0 )(tNil$ ?v1 ))(= ?v0 ?v1 ))):named a13 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_b_fun$ )(?v2 A_b_tllist$ ))(= (is_TNil$ (tmap$ ?v0 ?v1 ?v2 ))(is_TNil$ ?v2 ))):named a14 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (not (is_TNil$ ?v0 ))(= (tCons$ (thd$ ?v0 )(ttl$ ?v0 ))?v0 ))):named a15 ))
(check-sat )
;(get-unsat-core )
