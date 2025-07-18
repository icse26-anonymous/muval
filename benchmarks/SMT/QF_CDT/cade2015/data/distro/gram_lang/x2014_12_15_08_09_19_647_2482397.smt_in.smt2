;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort T_set$ 0 )
(declare-sort T_bool_fun$ 0 )
(declare-sort T_dtree_sum_set$ 0 )
(declare-sort Dtree_T_bool_fun_fun$ 0 )
(declare-sort N_set_dtree_T_bool_fun_fun_fun$ 0 )
(declare-datatypes ()((T_dtree_sum$ (inl$ (projl$ T$ ))(inr$ (projr$ Dtree$ )))))
(declare-fun fr$ (N_set$ Dtree$ )T_set$ )
(declare-fun ns$ ()N_set$ )
(declare-fun tr$ ()Dtree$ )
(declare-fun uu$ ()T_bool_fun$ )
(declare-fun wf$ (Dtree$ )Bool )
(declare-fun frr$ (N_set$ Dtree$ )T_set$ )
(declare-fun uua$ ()T_bool_fun$ )
(declare-fun uub$ (N_set$ Dtree$ )T_bool_fun$ )
(declare-fun cont$ (Dtree$ )T_dtree_sum_set$ )
(declare-fun inFr$ ()N_set_dtree_T_bool_fun_fun_fun$ )
(declare-fun root$ (Dtree$ )N$ )
(declare-fun inFr2$ ()N_set_dtree_T_bool_fun_fun_fun$ )
(declare-fun inFrr$ (N_set$ Dtree$ T$ )Bool )
(declare-fun inItr$ (N_set$ Dtree$ N$ )Bool )
(declare-fun insert$ (N$ N_set$ )N_set$ )
(declare-fun member$ (T_dtree_sum$ T_dtree_sum_set$ )Bool )
(declare-fun subtr2$ (N_set$ Dtree$ Dtree$ )Bool )
(declare-fun collect$ (T_bool_fun$ )T_set$ )
(declare-fun fun_app$ (T_bool_fun$ T$ )Bool )
(declare-fun member$a (T$ T_set$ )Bool )
(declare-fun member$b (N$ N_set$ )Bool )
(declare-fun subtrOf$ (Dtree$ N$ )Dtree$ )
(declare-fun fun_app$a (Dtree_T_bool_fun_fun$ Dtree$ )T_bool_fun$ )
(declare-fun fun_app$b (N_set_dtree_T_bool_fun_fun_fun$ N_set$ )Dtree_T_bool_fun_fun$ )
(declare-fun hsubst_c$ (Dtree$ Dtree$ )T_dtree_sum_set$ )
(assert (! (forall ((?v0 T$ ))(! (= (fun_app$ uua$ ?v0 )(exists ((?v1 Dtree$ ))(and (member$ (inr$ ?v1 )(cont$ tr$ ))(fun_app$ (fun_app$a (fun_app$b inFr$ ns$ )?v1 )?v0 )))):pattern ((fun_app$ uua$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 T$ ))(! (= (fun_app$ uu$ ?v0 )(exists ((?v1 Dtree$ ))(and (member$ (inr$ ?v1 )(cont$ tr$ ))(member$a ?v0 (collect$ (fun_app$a (fun_app$b inFr$ ns$ )?v1 )))))):pattern ((fun_app$ uu$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(! (= (fun_app$ (uub$ ?v0 ?v1 )?v2 )(exists ((?v3 Dtree$ ))(and (member$ (inr$ ?v3 )(cont$ ?v1 ))(member$a ?v2 (fr$ ?v0 ?v3 ))))):pattern ((fun_app$ (uub$ ?v0 ?v1 )?v2 )))):named a2 ))
(assert (! (not (= (collect$ uu$ )(collect$ uua$ ))):named a3 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(= (inFrr$ ?v0 ?v1 ?v2 )(exists ((?v3 Dtree$ ))(and (member$ (inr$ ?v3 )(cont$ ?v1 ))(fun_app$ (fun_app$a (fun_app$b inFr$ ?v0 )?v3 )?v2 ))))):named a4 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ ))(= (frr$ ?v0 ?v1 )(collect$ (uub$ ?v0 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ ))(! (= (fr$ ?v0 ?v1 )(collect$ (fun_app$a (fun_app$b inFr$ ?v0 )?v1 ))):pattern ((fr$ ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (not (= ?v0 ?v1 ))(not (= (inr$ ?v0 )(inr$ ?v1 ))))):named a10 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 T$ ))(=> (and (member$b (root$ ?v0 )?v1 )(and (member$ (inr$ ?v2 )(cont$ ?v0 ))(fun_app$ (fun_app$a (fun_app$b inFr$ ?v1 )?v2 )?v3 )))(fun_app$ (fun_app$a (fun_app$b inFr$ ?v1 )?v0 )?v3 ))):named a11 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (and (wf$ ?v0 )(member$ (inr$ ?v1 )(cont$ ?v0 )))(wf$ ?v1 ))):named a12 ))
(assert (! (= inFr$ inFr2$ ):named a13 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (and (wf$ ?v0 )(and (member$ (inr$ ?v1 )(cont$ ?v0 ))(member$ (inr$ ?v2 )(cont$ ?v0 ))))(= (= (root$ ?v1 )(root$ ?v2 ))(= ?v1 ?v2 )))):named a14 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (fun_app$ (fun_app$a (fun_app$b inFr2$ ?v0 )?v1 )?v2 )(member$b (root$ ?v1 )?v0 ))):named a15 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ )(?v3 Dtree$ ))(=> (and (fun_app$ (fun_app$a (fun_app$b inFr2$ ?v0 )?v1 )?v2 )(and (member$b (root$ ?v3 )?v0 )(member$ (inr$ ?v1 )(cont$ ?v3 ))))(fun_app$ (fun_app$a (fun_app$b inFr2$ ?v0 )?v3 )?v2 ))):named a16 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 T$ ))(=> (not (member$b (root$ ?v0 )?v1 ))(not (fun_app$ (fun_app$a (fun_app$b inFr$ ?v1 )?v0 )?v2 )))):named a17 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (fun_app$ (fun_app$a (fun_app$b inFr$ ?v0 )?v1 )?v2 )(member$b (root$ ?v1 )?v0 ))):named a18 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (and (wf$ ?v0 )(member$ (inr$ ?v1 )(cont$ ?v0 )))(= (subtrOf$ ?v0 (root$ ?v1 ))?v1 ))):named a19 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (and (= (root$ ?v0 )(root$ ?v1 ))(= (cont$ ?v0 )(cont$ ?v1 )))(= ?v0 ?v1 ))):named a20 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 N$ ))(=> (and (member$b (root$ ?v0 )?v1 )(and (member$ (inr$ ?v2 )(cont$ ?v0 ))(inItr$ ?v1 ?v2 ?v3 )))(inItr$ ?v1 ?v0 ?v3 ))):named a21 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ ))(=> (and (inItr$ ?v0 ?v1 ?v2 )(and (forall ((?v3 Dtree$ )(?v4 N_set$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 (root$ ?v3 ))(member$b (root$ ?v3 )?v4 ))))false ))(forall ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 N$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$b (root$ ?v3 )?v4 )(and (member$ (inr$ ?v5 )(cont$ ?v3 ))(inItr$ ?v4 ?v5 ?v6 ))))))false ))))false )):named a22 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ ))(= (inItr$ ?v0 ?v1 ?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 (root$ ?v3 ))(member$b (root$ ?v3 )?v4 )))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 N$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$b (root$ ?v3 )?v4 )(and (member$ (inr$ ?v5 )(cont$ ?v3 ))(inItr$ ?v4 ?v5 ?v6 )))))))))):named a23 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(! (= (hsubst_c$ ?v0 ?v1 )(ite (= (root$ ?v1 )(root$ ?v0 ))(cont$ ?v0 )(cont$ ?v1 ))):pattern ((hsubst_c$ ?v0 ?v1 )))):named a24 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 Dtree$ ))(=> (and (member$b (root$ ?v0 )?v1 )(and (member$ (inr$ ?v0 )(cont$ ?v2 ))(subtr2$ ?v1 ?v2 ?v3 )))(subtr2$ ?v1 ?v0 ?v3 ))):named a25 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 Dtree$ ))(=> (and (member$b (root$ ?v0 )?v1 )(and (member$ (inr$ ?v2 )(cont$ ?v0 ))(subtr2$ ?v1 ?v3 ?v2 )))(subtr2$ ?v1 ?v3 ?v0 ))):named a26 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (and (subtr2$ ?v0 ?v1 ?v2 )(and (forall ((?v3 Dtree$ )(?v4 N_set$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v3 )(member$b (root$ ?v3 )?v4 ))))false ))(forall ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 Dtree$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$b (root$ ?v3 )?v4 )(and (member$ (inr$ ?v3 )(cont$ ?v5 ))(subtr2$ ?v4 ?v5 ?v6 ))))))false ))))false )):named a27 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(= (subtr2$ ?v0 ?v1 ?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v3 )(member$b (root$ ?v3 )?v4 )))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 Dtree$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$b (root$ ?v3 )?v4 )(and (member$ (inr$ ?v3 )(cont$ ?v5 ))(subtr2$ ?v4 ?v5 ?v6 )))))))))):named a28 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ )(?v2 N_set$ )(?v3 T$ ))(=> (and (member$ (inr$ ?v0 )(cont$ ?v1 ))(fun_app$ (fun_app$a (fun_app$b inFr2$ ?v2 )?v0 )?v3 ))(fun_app$ (fun_app$a (fun_app$b inFr2$ (insert$ (root$ ?v1 )?v2 ))?v1 )?v3 ))):named a29 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ )(?v3 Dtree$ ))(=> (and (subtr2$ ?v0 ?v1 ?v2 )(subtr2$ ?v0 ?v2 ?v3 ))(subtr2$ ?v0 ?v1 ?v3 ))):named a30 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ ))(=> (member$b (root$ ?v0 )?v1 )(subtr2$ ?v1 ?v0 ?v0 ))):named a31 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (subtr2$ ?v0 ?v1 ?v2 )(member$b (root$ ?v1 )?v0 ))):named a32 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (subtr2$ ?v0 ?v1 ?v2 )(member$b (root$ ?v2 )?v0 ))):named a33 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ ))(=> (member$b (root$ ?v0 )?v1 )(inItr$ ?v1 ?v0 (root$ ?v0 )))):named a34 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ ))(=> (inItr$ ?v0 ?v1 ?v2 )(member$b (root$ ?v1 )?v0 ))):named a35 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ )(?v3 Dtree$ ))(=> (and (fun_app$ (fun_app$a (fun_app$b inFr$ ?v0 )?v1 )?v2 )(member$ (inr$ ?v1 )(cont$ ?v3 )))(fun_app$ (fun_app$a (fun_app$b inFr$ (insert$ (root$ ?v3 )?v0 ))?v3 )?v2 ))):named a36 ))
(check-sat )
;(get-unsat-core )
