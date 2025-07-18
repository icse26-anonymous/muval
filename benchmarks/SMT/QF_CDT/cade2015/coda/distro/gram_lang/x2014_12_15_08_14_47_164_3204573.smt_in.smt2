;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort N_dtree_fun$ 0 )
(declare-sort T_dtree_sum_set$ 0 )
(declare-sort N_list$ 0)
(declare-sort T_dtree_sum$ 0)
(declare-sort T_dtree_sum_list$ 0)
(declare-fun nil$ ()N_list$)
(declare-fun hd$ (N_list$)N$)
(declare-fun tl$ (N_list$)N_list$)
(declare-fun cons$ (N$ N_list$ )N_list$)
(declare-fun projl$ (T_dtree_sum$)T$)
(declare-fun inl$ (T$ )T_dtree_sum$)
(declare-fun projr$ (T_dtree_sum$)Dtree$)
(declare-fun inr$ (Dtree$ )T_dtree_sum$)
(declare-fun nil$a ()T_dtree_sum_list$)
(declare-fun hd$a (T_dtree_sum_list$)T_dtree_sum$)
(declare-fun tl$a (T_dtree_sum_list$)T_dtree_sum_list$)
(declare-fun cons$a (T_dtree_sum$ T_dtree_sum_list$ )T_dtree_sum_list$)
(declare-fun f$ ()N_dtree_fun$ )
(declare-fun n$ ()N$ )
(declare-fun t$ ()T$ )
(declare-fun n1$ ()N$ )
(declare-fun nl$ ()N_list$ )
(declare-fun ns$ ()N_set$ )
(declare-fun tr$ ()Dtree$ )
(declare-fun nl1$ ()N_list$ )
(declare-fun nl2$ ()N_list$ )
(declare-fun reg$ (N_dtree_fun$ Dtree$ )Bool )
(declare-fun set$ (N_list$ )N_set$ )
(declare-fun tr1$ ()Dtree$ )
(declare-fun cont$ (Dtree$ )T_dtree_sum_set$ )
(declare-fun last$ (N_list$ )N$ )
(declare-fun path$ (N_dtree_fun$ N_list$ )Bool )
(declare-fun set$a (T_dtree_sum_list$ )T_dtree_sum_set$ )
(declare-fun member$ (T_dtree_sum$ T_dtree_sum_set$ )Bool )
(declare-fun fun_app$ (N_dtree_fun$ N$ )Dtree$ )
(declare-fun less_eq$ (N_set$ N_set$ )Bool )
(declare-fun member$a (N$ N_set$ )Bool )
(declare-fun distinct$ (N_list$ )Bool )
(declare-fun less_eq$a (T_dtree_sum_set$ T_dtree_sum_set$ )Bool )
(assert (! (not (and (distinct$ nl1$ )(and (path$ f$ nl1$ )(and (= (fun_app$ f$ n1$ )(fun_app$ f$ n1$ ))(and (= tr1$ tr1$ )(and (less_eq$ (set$ nl1$ )(set$ nl1$ ))(member$ (inl$ t$ )(cont$ tr1$ )))))))):named a0 ))
(assert (! (path$ f$ nl1$ ):named a1 ))
(assert (! (distinct$ nl$ ):named a2 ))
(assert (! (member$ (inl$ t$ )(cont$ tr1$ )):named a3 ))
(assert (! (path$ f$ nl$ ):named a4 ))
(assert (! (not (member$a n$ (set$ nl1$ ))):named a5 ))
(assert (! (= nl1$ (cons$ n1$ nl2$ )):named a6 ))
(assert (! (reg$ f$ (fun_app$ f$ n1$ )):named a7 ))
(assert (! (less_eq$ (set$ nl$ )ns$ ):named a8 ))
(assert (! (= (hd$ nl1$ )n1$ ):named a9 ))
(assert (! (= (fun_app$ f$ (last$ nl$ ))tr1$ ):named a10 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(= (= (inl$ ?v0 )(inl$ ?v1 ))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(= (= (inl$ ?v0 )(inl$ ?v1 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum_set$ ))(=> (forall ((?v2 T_dtree_sum$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 )))(less_eq$a ?v0 ?v1 ))):named a13 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(=> (forall ((?v2 N$ ))(=> (member$a ?v2 ?v0 )(member$a ?v2 ?v1 )))(less_eq$ ?v0 ?v1 ))):named a14 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum_set$ ))(=> (and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 ))(= ?v0 ?v1 ))):named a15 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))(= ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ ))(less_eq$a ?v0 ?v0 )):named a17 ))
(assert (! (forall ((?v0 N_set$ ))(less_eq$ ?v0 ?v0 )):named a18 ))
(assert (! (forall ((?v0 T_dtree_sum_list$ )(?v1 T_dtree_sum_set$ ))(= (less_eq$a (set$a ?v0 )?v1 )(forall ((?v2 T_dtree_sum$ ))(=> (member$ ?v2 (set$a ?v0 ))(member$ ?v2 ?v1 ))))):named a19 ))
(assert (! (forall ((?v0 N_list$ )(?v1 N_set$ ))(= (less_eq$ (set$ ?v0 )?v1 )(forall ((?v2 N$ ))(=> (member$a ?v2 (set$ ?v0 ))(member$a ?v2 ?v1 ))))):named a20 ))
(assert (! (reg$ f$ tr$ ):named a21 ))
(check-sat )
;(get-unsat-core )
