;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort T_dtree_sum_set$ 0 )
(declare-datatypes ()((T_dtree_sum$ (inl$ (projl$ T$ ))(inr$ (projr$ Dtree$ )))))
(declare-fun t$ ()T$ )
(declare-fun tr$ ()Dtree$ )
(declare-fun ns1$ ()N_set$ )
(declare-fun tr1$ ()Dtree$ )
(declare-fun cont$ (Dtree$ )T_dtree_sum_set$ )
(declare-fun inFr$ (N_set$ Dtree$ T$ )Bool )
(declare-fun root$ (Dtree$ )N$ )
(declare-fun insert$ (N$ N_set$ )N_set$ )
(declare-fun member$ (T_dtree_sum$ T_dtree_sum_set$ )Bool )
(declare-fun insert$a (T_dtree_sum$ T_dtree_sum_set$ )T_dtree_sum_set$ )
(declare-fun less_eq$ (T_dtree_sum_set$ T_dtree_sum_set$ )Bool )
(declare-fun member$a (N$ N_set$ )Bool )
(declare-fun less_eq$a (N_set$ N_set$ )Bool )
(assert (! (not (inFr$ (insert$ (root$ tr$ )ns1$ )tr$ t$ )):named a0 ))
(assert (! (member$ (inr$ tr1$ )(cont$ tr$ )):named a1 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum$ ))(less_eq$ ?v0 (insert$a ?v1 ?v0 ))):named a2 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N$ ))(less_eq$a ?v0 (insert$ ?v1 ?v0 ))):named a3 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ )(?v3 N_set$ ))(=> (and (inFr$ ?v0 ?v1 ?v2 )(less_eq$a ?v0 ?v3 ))(inFr$ ?v3 ?v1 ?v2 ))):named a4 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(= (inFr$ ?v0 ?v1 ?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 T$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v5 )(and (member$a (root$ ?v3 )?v4 )(member$ (inl$ ?v5 )(cont$ ?v3 )))))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 T$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$a (root$ ?v3 )?v4 )(and (member$ (inr$ ?v5 )(cont$ ?v3 ))(inFr$ ?v4 ?v5 ?v6 )))))))))):named a5 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_set$ ))(member$ ?v0 (insert$a ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 N$ )(?v1 N_set$ ))(member$a ?v0 (insert$ ?v0 ?v1 ))):named a7 ))
(check-sat )
;(get-unsat-core )
