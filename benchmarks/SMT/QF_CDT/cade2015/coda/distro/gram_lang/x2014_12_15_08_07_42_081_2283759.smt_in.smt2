;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort T_bool_fun$ 0 )
(declare-sort Dtree_bool_fun$ 0 )
(declare-sort T_dtree_sum_set$ 0 )
(declare-sort Dtree_T_bool_fun_fun$ 0 )
(declare-sort Dtree_dtree_bool_fun_fun$ 0 )
(declare-sort N_set_dtree_T_bool_fun_fun_fun$ 0 )
(declare-sort N_set_dtree_dtree_bool_fun_fun_fun$ 0 )
(declare-sort T_dtree_sum$ 0)
(declare-fun projl$ (T_dtree_sum$)T$)
(declare-fun inl$ (T$ )T_dtree_sum$)
(declare-fun projr$ (T_dtree_sum$)Dtree$)
(declare-fun inr$ (Dtree$ )T_dtree_sum$)
(declare-fun tr$ ()Dtree$ )
(declare-fun wf$ (Dtree$ )Bool )
(declare-fun tr$a ()Dtree$ )
(declare-fun cont$ (Dtree$ )T_dtree_sum_set$ )
(declare-fun inFr$ ()N_set_dtree_T_bool_fun_fun_fun$ )
(declare-fun node$ (N$ T_dtree_sum_set$ )Dtree$ )
(declare-fun root$ (Dtree$ )N$ )
(declare-fun inFr2$ ()N_set_dtree_T_bool_fun_fun_fun$ )
(declare-fun inItr$ (N_set$ Dtree$ N$ )Bool )
(declare-fun subtr$ ()N_set_dtree_dtree_bool_fun_fun_fun$ )
(declare-fun member$ (T_dtree_sum$ T_dtree_sum_set$ )Bool )
(declare-fun subtr2$ ()N_set_dtree_dtree_bool_fun_fun_fun$ )
(declare-fun fun_app$ (T_bool_fun$ T$ )Bool )
(declare-fun member$a (N$ N_set$ )Bool )
(declare-fun subtrOf$ (Dtree$ N$ )Dtree$ )
(declare-fun fun_app$a (Dtree_T_bool_fun_fun$ Dtree$ )T_bool_fun$ )
(declare-fun fun_app$b (N_set_dtree_T_bool_fun_fun_fun$ N_set$ )Dtree_T_bool_fun_fun$ )
(declare-fun fun_app$c (Dtree_bool_fun$ Dtree$ )Bool )
(declare-fun fun_app$d (Dtree_dtree_bool_fun_fun$ Dtree$ )Dtree_bool_fun$ )
(declare-fun fun_app$e (N_set_dtree_dtree_bool_fun_fun_fun$ N_set$ )Dtree_dtree_bool_fun_fun$ )
(assert (! (not (= (subtrOf$ tr$ (root$ tr$a ))tr$a )):named a0 ))
(assert (! (wf$ tr$ ):named a1 ))
(assert (! (member$ (inr$ tr$a )(cont$ tr$ )):named a2 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (fun_app$ (fun_app$a (fun_app$b inFr2$ ?v0 )?v1 )?v2 )(member$a (root$ ?v1 )?v0 ))):named a3 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ ))(=> (inItr$ ?v0 ?v1 ?v2 )(member$a (root$ ?v1 )?v0 ))):named a4 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ ))(=> (member$a (root$ ?v0 )?v1 )(inItr$ ?v1 ?v0 (root$ ?v0 )))):named a5 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (fun_app$ (fun_app$a (fun_app$b inFr$ ?v0 )?v1 )?v2 )(member$a (root$ ?v1 )?v0 ))):named a6 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 T$ ))(=> (not (member$a (root$ ?v0 )?v1 ))(not (fun_app$ (fun_app$a (fun_app$b inFr$ ?v1 )?v0 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (fun_app$c (fun_app$d (fun_app$e subtr2$ ?v0 )?v1 )?v2 )(member$a (root$ ?v2 )?v0 ))):named a8 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (fun_app$c (fun_app$d (fun_app$e subtr2$ ?v0 )?v1 )?v2 )(member$a (root$ ?v1 )?v0 ))):named a9 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ ))(=> (member$a (root$ ?v0 )?v1 )(fun_app$c (fun_app$d (fun_app$e subtr2$ ?v1 )?v0 )?v0 ))):named a10 ))
(assert (! (forall ((?v0 N$ )(?v1 T_dtree_sum_set$ ))(= (root$ (node$ ?v0 ?v1 ))?v0 )):named a11 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (fun_app$c (fun_app$d (fun_app$e subtr$ ?v0 )?v1 )?v2 )(member$a (root$ ?v2 )?v0 ))):named a12 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (fun_app$c (fun_app$d (fun_app$e subtr$ ?v0 )?v1 )?v2 )(member$a (root$ ?v1 )?v0 ))):named a13 ))
(assert (! (forall ((?v0 Dtree$ ))(= (node$ (root$ ?v0 )(cont$ ?v0 ))?v0 )):named a14 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (and (wf$ ?v0 )(and (member$ (inr$ ?v1 )(cont$ ?v0 ))(member$ (inr$ ?v2 )(cont$ ?v0 ))))(= (= (root$ ?v1 )(root$ ?v2 ))(= ?v1 ?v2 )))):named a15 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ ))(= (inItr$ ?v0 ?v1 ?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 (root$ ?v3 ))(member$a (root$ ?v3 )?v4 )))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 N$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$a (root$ ?v3 )?v4 )(and (member$ (inr$ ?v5 )(cont$ ?v3 ))(inItr$ ?v4 ?v5 ?v6 )))))))))):named a16 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(= (fun_app$c (fun_app$d (fun_app$e subtr$ ?v0 )?v1 )?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v3 )(member$a (root$ ?v3 )?v4 )))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 Dtree$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v5 )(and (= ?v2 ?v3 )(and (member$a (root$ ?v3 )?v4 )(and (fun_app$c (fun_app$d (fun_app$e subtr$ ?v4 )?v5 )?v6 )(member$ (inr$ ?v6 )(cont$ ?v3 ))))))))))):named a17 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(= (fun_app$c (fun_app$d (fun_app$e subtr2$ ?v0 )?v1 )?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v3 )(member$a (root$ ?v3 )?v4 )))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 Dtree$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$a (root$ ?v3 )?v4 )(and (member$ (inr$ ?v3 )(cont$ ?v5 ))(fun_app$c (fun_app$d (fun_app$e subtr2$ ?v4 )?v5 )?v6 )))))))))):named a18 ))
(assert (! (= inFr$ inFr2$ ):named a19 ))
(assert (! (= subtr$ subtr2$ ):named a20 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ )(?v3 Dtree$ ))(=> (and (fun_app$ (fun_app$a (fun_app$b inFr$ ?v0 )?v1 )?v2 )(fun_app$c (fun_app$d (fun_app$e subtr$ ?v0 )?v1 )?v3 ))(fun_app$ (fun_app$a (fun_app$b inFr$ ?v0 )?v3 )?v2 ))):named a21 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ )(?v3 Dtree$ ))(=> (and (fun_app$ (fun_app$a (fun_app$b inFr2$ ?v0 )?v1 )?v2 )(and (member$a (root$ ?v3 )?v0 )(member$ (inr$ ?v1 )(cont$ ?v3 ))))(fun_app$ (fun_app$a (fun_app$b inFr2$ ?v0 )?v3 )?v2 ))):named a22 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ ))(=> (and (inItr$ ?v0 ?v1 ?v2 )(and (forall ((?v3 Dtree$ )(?v4 N_set$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 (root$ ?v3 ))(member$a (root$ ?v3 )?v4 ))))false ))(forall ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 N$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$a (root$ ?v3 )?v4 )(and (member$ (inr$ ?v5 )(cont$ ?v3 ))(inItr$ ?v4 ?v5 ?v6 ))))))false ))))false )):named a23 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ )(?v3 Dtree$ ))(=> (and (inItr$ ?v0 ?v1 ?v2 )(fun_app$c (fun_app$d (fun_app$e subtr$ ?v0 )?v1 )?v3 ))(inItr$ ?v0 ?v3 ?v2 ))):named a24 ))
(check-sat )
;(get-unsat-core )
