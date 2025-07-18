;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort B_set$ 0 )
(declare-sort Nat_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort Unit_b_fun$ 0 )
(declare-sort B_a_b_tllist_fun$ 0 )
(declare-sort A_b_tllist_bool_fun$ 0 )
(declare-sort A_a_b_tllist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_b_tllist$ (tNil$ (terminal$ B$ ))(tCons$ (thd$ A$ )(ttl$ A_b_tllist$ )))))
(declare-fun n$ ()Nat$ )
(declare-fun x$ ()A$ )
(declare-fun xs$ ()A_b_tllist$ )
(declare-fun tnth$ (A_b_tllist$ )Nat_a_fun$ )
(declare-fun tset$ (A_b_tllist$ )A_set$ )
(declare-fun member$ (B$ B_set$ )Bool )
(declare-fun fun_app$ (Nat_a_fun$ Nat$ )A$ )
(declare-fun member$a (A$ A_set$ )Bool )
(declare-fun tappend$ (A_b_tllist$ B_a_b_tllist_fun$ )A_b_tllist$ )
(declare-fun tfilter$ (Unit_b_fun$ A_bool_fun$ A_b_tllist$ )A_b_tllist$ )
(declare-fun case_nat$ (A$ Nat_a_fun$ Nat$ )A$ )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$b (A_b_tllist_bool_fun$ A_b_tllist$ )Bool )
(declare-fun fun_app$c (A_a_b_tllist_bool_fun_fun$ A$ )A_b_tllist_bool_fun$ )
(declare-fun tfilter$a (B$ A_bool_fun$ A_b_tllist$ )A_b_tllist$ )
(declare-fun pred_tllist$ (A_bool_fun$ B_bool_fun$ A_b_tllist$ )Bool )
(declare-fun set2_tllist$ (A_b_tllist$ )B_set$ )
(assert (! (not (= (fun_app$ (tnth$ (tCons$ x$ xs$ ))n$ )(case_nat$ x$ (tnth$ xs$ )n$ ))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ )(?v3 A_b_tllist$ ))(= (= (tCons$ ?v0 ?v1 )(tCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a1 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_bool_fun$ )(?v2 A$ )(?v3 A_b_tllist$ ))(! (= (pred_tllist$ ?v0 ?v1 (tCons$ ?v2 ?v3 ))(and (fun_app$a ?v0 ?v2 )(pred_tllist$ ?v0 ?v1 ?v3 ))):pattern ((pred_tllist$ ?v0 ?v1 (tCons$ ?v2 ?v3 ))))):named a2 ))
(assert (! (forall ((?v0 Unit_b_fun$ )(?v1 A_bool_fun$ )(?v2 A$ )(?v3 A_b_tllist$ ))(! (= (tfilter$ ?v0 ?v1 (tCons$ ?v2 ?v3 ))(ite (fun_app$a ?v1 ?v2 )(tCons$ ?v2 (tfilter$ ?v0 ?v1 ?v3 ))(tfilter$ ?v0 ?v1 ?v3 ))):pattern ((tfilter$ ?v0 ?v1 (tCons$ ?v2 ?v3 ))))):named a3 ))
(assert (! (forall ((?v0 B$ )(?v1 A_bool_fun$ )(?v2 A$ )(?v3 A_b_tllist$ ))(! (= (tfilter$a ?v0 ?v1 (tCons$ ?v2 ?v3 ))(ite (fun_app$a ?v1 ?v2 )(tCons$ ?v2 (tfilter$a ?v0 ?v1 ?v3 ))(tfilter$a ?v0 ?v1 ?v3 ))):pattern ((tfilter$a ?v0 ?v1 (tCons$ ?v2 ?v3 ))))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 B_a_b_tllist_fun$ ))(! (= (tappend$ (tCons$ ?v0 ?v1 )?v2 )(tCons$ ?v0 (tappend$ ?v1 ?v2 ))):pattern ((tappend$ (tCons$ ?v0 ?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (set2_tllist$ (tCons$ ?v0 ?v1 ))(set2_tllist$ ?v1 )):pattern ((tCons$ ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 B$ )(?v1 A_b_tllist$ )(?v2 A$ ))(=> (member$ ?v0 (set2_tllist$ ?v1 ))(member$ ?v0 (set2_tllist$ (tCons$ ?v2 ?v1 ))))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (thd$ (tCons$ ?v0 ?v1 ))?v0 ):pattern ((tCons$ ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (terminal$ (tCons$ ?v0 ?v1 ))(terminal$ ?v1 )):pattern ((tCons$ ?v0 ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A_a_b_tllist_bool_fun_fun$ ))(=> (and (member$a ?v0 (tset$ ?v1 ))(and (forall ((?v3 A$ )(?v4 A_b_tllist$ ))(fun_app$b (fun_app$c ?v2 ?v3 )(tCons$ ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_b_tllist$ )(?v5 A$ ))(=> (and (member$a ?v5 (tset$ ?v4 ))(fun_app$b (fun_app$c ?v2 ?v5 )?v4 ))(fun_app$b (fun_app$c ?v2 ?v5 )(tCons$ ?v3 ?v4 ))))))(fun_app$b (fun_app$c ?v2 ?v0 )?v1 ))):named a10 ))
(check-sat )
;(get-unsat-core )
