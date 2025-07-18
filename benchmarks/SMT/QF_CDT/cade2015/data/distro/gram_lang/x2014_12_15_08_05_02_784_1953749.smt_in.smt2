;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort N_bool_fun$ 0 )
(declare-sort T_dtree_sum_set$ 0 )
(declare-sort T_dtree_sum_bool_fun$ 0 )
(declare-datatypes ()((T_dtree_sum$ (inl$ (projl$ T$ ))(inr$ (projr$ Dtree$ )))))
(declare-fun ns$ ()N_set$ )
(declare-fun tr$ ()Dtree$ )
(declare-fun ns$a ()N_set$ )
(declare-fun nsa$ ()N_set$ )
(declare-fun tr1$ ()Dtree$ )
(declare-fun tr2$ ()Dtree$ )
(declare-fun cont$ (Dtree$ )T_dtree_sum_set$ )
(declare-fun ns_a$ ()N_set$ )
(declare-fun root$ (Dtree$ )N$ )
(declare-fun member$ (N$ N_set$ )Bool )
(declare-fun subtr2$ (N_set$ Dtree$ Dtree$ )Bool )
(declare-fun collect$ (T_dtree_sum_bool_fun$ )T_dtree_sum_set$ )
(declare-fun fun_app$ (T_dtree_sum_bool_fun$ T_dtree_sum$ )Bool )
(declare-fun less_eq$ (N_set$ N_set$ )Bool )
(declare-fun member$a (T_dtree_sum$ T_dtree_sum_set$ )Bool )
(declare-fun collect$a (N_bool_fun$ )N_set$ )
(declare-fun fun_app$a (N_bool_fun$ N$ )Bool )
(declare-fun less_eq$a (T_dtree_sum_set$ T_dtree_sum_set$ )Bool )
(assert (! (not (subtr2$ ns_a$ tr$ tr$ )):named a0 ))
(assert (! (member$ (root$ tr$ )nsa$ ):named a1 ))
(assert (! (less_eq$ nsa$ ns_a$ ):named a2 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ ))(=> (member$ (root$ ?v0 )?v1 )(subtr2$ ?v1 ?v0 ?v0 ))):named a3 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 Dtree$ ))(=> (and (member$ (root$ ?v0 )?v1 )(and (member$a (inr$ ?v0 )(cont$ ?v2 ))(subtr2$ ?v1 ?v2 ?v3 )))(subtr2$ ?v1 ?v0 ?v3 ))):named a4 ))
(assert (! (less_eq$ ns$ ns$a ):named a5 ))
(assert (! (subtr2$ ns$ tr1$ tr2$ ):named a6 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (subtr2$ ?v0 ?v1 ?v2 )(member$ (root$ ?v2 )?v0 ))):named a7 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (subtr2$ ?v0 ?v1 ?v2 )(member$ (root$ ?v1 )?v0 ))):named a8 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum_set$ ))(=> (forall ((?v2 T_dtree_sum$ ))(=> (member$a ?v2 ?v0 )(member$a ?v2 ?v1 )))(less_eq$a ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(=> (forall ((?v2 N$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 )))(less_eq$ ?v0 ?v1 ))):named a10 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum_set$ ))(=> (and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 ))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ ))(less_eq$a ?v0 ?v0 )):named a13 ))
(assert (! (forall ((?v0 N_set$ ))(less_eq$ ?v0 ?v0 )):named a14 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(= (subtr2$ ?v0 ?v1 ?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v3 )(member$ (root$ ?v3 )?v4 )))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 Dtree$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$ (root$ ?v3 )?v4 )(and (member$a (inr$ ?v3 )(cont$ ?v5 ))(subtr2$ ?v4 ?v5 ?v6 )))))))))):named a15 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (and (subtr2$ ?v0 ?v1 ?v2 )(and (forall ((?v3 Dtree$ )(?v4 N_set$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v3 )(member$ (root$ ?v3 )?v4 ))))false ))(forall ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 Dtree$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$ (root$ ?v3 )?v4 )(and (member$a (inr$ ?v3 )(cont$ ?v5 ))(subtr2$ ?v4 ?v5 ?v6 ))))))false ))))false )):named a16 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum_set$ ))(= (= ?v0 ?v1 )(and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 )))):named a17 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(= (= ?v0 ?v1 )(and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 )))):named a18 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum_set$ ))(= (less_eq$a ?v0 ?v1 )(forall ((?v2 T_dtree_sum$ ))(=> (member$a ?v2 ?v0 )(member$a ?v2 ?v1 ))))):named a19 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(= (less_eq$ ?v0 ?v1 )(forall ((?v2 N$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 ))))):named a20 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum_set$ ))(= (less_eq$a ?v0 ?v1 )(forall ((?v2 T_dtree_sum$ ))(=> (member$a ?v2 ?v0 )(member$a ?v2 ?v1 ))))):named a21 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(= (less_eq$ ?v0 ?v1 )(forall ((?v2 N$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 ))))):named a22 ))
(assert (! (forall ((?v0 T_dtree_sum_bool_fun$ )(?v1 T_dtree_sum_bool_fun$ ))(=> (forall ((?v2 T_dtree_sum$ ))(=> (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 )))(less_eq$a (collect$ ?v0 )(collect$ ?v1 )))):named a23 ))
(assert (! (forall ((?v0 N_bool_fun$ )(?v1 N_bool_fun$ ))(=> (forall ((?v2 N$ ))(=> (fun_app$a ?v0 ?v2 )(fun_app$a ?v1 ?v2 )))(less_eq$ (collect$a ?v0 )(collect$a ?v1 )))):named a24 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum_set$ ))(=> (and (= ?v0 ?v1 )(=> (and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 ))false ))false )):named a25 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(=> (and (= ?v0 ?v1 )(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))false ))false )):named a26 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum_set$ ))(=> (= ?v0 ?v1 )(less_eq$a ?v1 ?v0 ))):named a27 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(=> (= ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))):named a28 ))
(check-sat )
;(get-unsat-core )
