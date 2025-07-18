;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort N_N_fun$ 0 )
(declare-sort Dtree_set$ 0 )
(declare-sort N_bool_fun$ 0 )
(declare-sort T_bool_fun$ 0 )
(declare-sort Dtree_N_fun$ 0 )
(declare-sort N_dtree_fun$ 0 )
(declare-sort Dtree_bool_fun$ 0 )
(declare-sort Dtree_dtree_fun$ 0 )
(declare-sort T_dtree_sum_set$ 0 )
(declare-sort N_T_dtree_sum_fun$ 0 )
(declare-sort T_dtree_sum_N_fun$ 0 )
(declare-sort Dtree_N_bool_fun_fun$ 0 )
(declare-sort Dtree_T_bool_fun_fun$ 0 )
(declare-sort T_dtree_sum_bool_fun$ 0 )
(declare-sort Dtree_T_dtree_sum_fun$ 0 )
(declare-sort T_dtree_sum_dtree_fun$ 0 )
(declare-sort Dtree_dtree_bool_fun_fun$ 0 )
(declare-sort Dtree_T_dtree_sum_set_fun$ 0 )
(declare-sort T_dtree_sum_T_dtree_sum_fun$ 0 )
(declare-sort N_set_dtree_T_bool_fun_fun_fun$ 0 )
(declare-sort Dtree_T_dtree_sum_set_fun_dtree_dtree_fun_fun$ 0 )
(declare-datatypes ()((T_dtree_sum$ (inl$ (projl$ T$ ))(inr$ (projr$ Dtree$ )))))
(declare-fun tr$ ()Dtree$ )
(declare-fun uu$ ()Dtree_T_dtree_sum_fun$ )
(declare-fun wf$ (Dtree$ )Bool )
(declare-fun tr$a ()Dtree$ )
(declare-fun tr0$ ()Dtree$ )
(declare-fun tra$ ()Dtree$ )
(declare-fun uua$ (Dtree_set$ )Dtree_bool_fun$ )
(declare-fun uub$ (T_dtree_sum_set$ )T_dtree_sum_bool_fun$ )
(declare-fun uuc$ (N_set$ )N_bool_fun$ )
(declare-fun cont$ (Dtree$ )T_dtree_sum_set$ )
(declare-fun inFr$ ()N_set_dtree_T_bool_fun_fun_fun$ )
(declare-fun root$ ()Dtree_N_fun$ )
(declare-fun tr1a$ ()Dtree$ )
(declare-fun image$ (Dtree_dtree_fun$ Dtree_set$ )Dtree_set$ )
(declare-fun inFr2$ ()N_set_dtree_T_bool_fun_fun_fun$ )
(declare-fun inFrr$ (N_set$ Dtree$ T$ )Bool )
(declare-fun inItr$ (N_set$ )Dtree_N_bool_fun_fun$ )
(declare-fun subtr$ (N_set$ )Dtree_dtree_bool_fun_fun$ )
(declare-fun finite$ (T_dtree_sum_set$ )Bool )
(declare-fun hsubst$ (Dtree$ )Dtree_dtree_fun$ )
(declare-fun inj_on$ (Dtree_N_fun$ Dtree_set$ )Bool )
(declare-fun member$ (T_dtree_sum$ T_dtree_sum_set$ )Bool )
(declare-fun subtr2$ (N_set$ )Dtree_dtree_bool_fun_fun$ )
(declare-fun unfold$ (Dtree_N_fun$ )Dtree_T_dtree_sum_set_fun_dtree_dtree_fun_fun$ )
(declare-fun vimage$ (Dtree_T_dtree_sum_fun$ T_dtree_sum_set$ )Dtree_set$ )
(declare-fun collect$ (Dtree_bool_fun$ )Dtree_set$ )
(declare-fun fun_app$ (Dtree_T_dtree_sum_fun$ Dtree$ )T_dtree_sum$ )
(declare-fun member$a (Dtree$ Dtree_set$ )Bool )
(declare-fun member$b (N$ N_set$ )Bool )
(declare-fun subtrOf$ (Dtree$ )N_dtree_fun$ )
(declare-fun vimage$a (T_dtree_sum_dtree_fun$ Dtree_set$ )T_dtree_sum_set$ )
(declare-fun vimage$b (N_dtree_fun$ Dtree_set$ )N_set$ )
(declare-fun vimage$c (Dtree_N_fun$ N_set$ )Dtree_set$ )
(declare-fun vimage$d (Dtree_dtree_fun$ Dtree_set$ )Dtree_set$ )
(declare-fun vimage$e (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum_set$ )T_dtree_sum_set$ )
(declare-fun vimage$f (T_dtree_sum_N_fun$ N_set$ )T_dtree_sum_set$ )
(declare-fun vimage$g (N_T_dtree_sum_fun$ T_dtree_sum_set$ )N_set$ )
(declare-fun vimage$h (N_N_fun$ N_set$ )N_set$ )
(declare-fun collect$a (N_bool_fun$ )N_set$ )
(declare-fun collect$b (T_dtree_sum_bool_fun$ )T_dtree_sum_set$ )
(declare-fun fun_app$a (T_dtree_sum_bool_fun$ T_dtree_sum$ )Bool )
(declare-fun fun_app$b (Dtree_bool_fun$ Dtree$ )Bool )
(declare-fun fun_app$c (N_bool_fun$ N$ )Bool )
(declare-fun fun_app$d (Dtree_dtree_fun$ Dtree$ )Dtree$ )
(declare-fun fun_app$e (Dtree_N_fun$ Dtree$ )N$ )
(declare-fun fun_app$f (Dtree_T_dtree_sum_set_fun$ Dtree$ )T_dtree_sum_set$ )
(declare-fun fun_app$g (N_dtree_fun$ N$ )Dtree$ )
(declare-fun fun_app$h (T_bool_fun$ T$ )Bool )
(declare-fun fun_app$i (Dtree_T_bool_fun_fun$ Dtree$ )T_bool_fun$ )
(declare-fun fun_app$j (N_set_dtree_T_bool_fun_fun_fun$ N_set$ )Dtree_T_bool_fun_fun$ )
(declare-fun fun_app$k (Dtree_N_bool_fun_fun$ Dtree$ )N_bool_fun$ )
(declare-fun fun_app$l (Dtree_dtree_bool_fun_fun$ Dtree$ )Dtree_bool_fun$ )
(declare-fun fun_app$m (Dtree_T_dtree_sum_set_fun_dtree_dtree_fun_fun$ Dtree_T_dtree_sum_set_fun$ )Dtree_dtree_fun$ )
(declare-fun fun_app$n (T_dtree_sum_dtree_fun$ T_dtree_sum$ )Dtree$ )
(declare-fun fun_app$o (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum$ )T_dtree_sum$ )
(declare-fun fun_app$p (T_dtree_sum_N_fun$ T_dtree_sum$ )N$ )
(declare-fun fun_app$q (N_T_dtree_sum_fun$ N$ )T_dtree_sum$ )
(declare-fun fun_app$r (N_N_fun$ N$ )N$ )
(declare-fun hsubst_c$ (Dtree$ )Dtree_T_dtree_sum_set_fun$ )
(declare-fun hsubst_r$ ()Dtree_N_fun$ )
(assert (! (forall ((?v0 Dtree$ ))(! (= (fun_app$ uu$ ?v0 )(inr$ ?v0 )):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum$ ))(! (= (fun_app$a (uub$ ?v0 )?v1 )(member$ ?v1 ?v0 )):pattern ((fun_app$a (uub$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 Dtree_set$ )(?v1 Dtree$ ))(! (= (fun_app$b (uua$ ?v0 )?v1 )(member$a ?v1 ?v0 )):pattern ((fun_app$b (uua$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N$ ))(! (= (fun_app$c (uuc$ ?v0 )?v1 )(member$b ?v1 ?v0 )):pattern ((fun_app$c (uuc$ ?v0 )?v1 )))):named a3 ))
(assert (! (not (exists ((?v0 Dtree$ ))(and (wf$ ?v0 )(= tr$ (fun_app$d (hsubst$ tr0$ )?v0 ))))):named a4 ))
(assert (! (exists ((?v0 Dtree$ ))(and (member$ (inr$ ?v0 )(cont$ tra$ ))(= (fun_app$d (hsubst$ tr0$ )?v0 )tr$ ))):named a5 ))
(assert (! (not (= (fun_app$e root$ tra$ )(fun_app$e root$ tr0$ ))):named a6 ))
(assert (! (wf$ tr$a ):named a7 ))
(assert (! (wf$ tr0$ ):named a8 ))
(assert (! (wf$ tra$ ):named a9 ))
(assert (! (exists ((?v0 Dtree$ ))(and (wf$ ?v0 )(= tr1a$ (fun_app$d (hsubst$ tr0$ )?v0 )))):named a10 ))
(assert (! (forall ((?v0 Dtree$ ))(=> (= (fun_app$e root$ ?v0 )(fun_app$e root$ tr0$ ))(= (fun_app$d (hsubst$ tr0$ )?v0 )(fun_app$d (hsubst$ tr0$ )tr0$ )))):named a11 ))
(assert (! (= tr1a$ (fun_app$d (hsubst$ tr0$ )tra$ )):named a12 ))
(assert (! (member$ (inr$ tr$ )(cont$ (fun_app$d (hsubst$ tr0$ )tra$ ))):named a13 ))
(assert (! (forall ((?v0 Dtree$ ))(= (fun_app$e root$ (fun_app$d (hsubst$ tr0$ )?v0 ))(fun_app$e root$ ?v0 ))):named a14 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (and (wf$ ?v0 )(and (member$ (inr$ ?v1 )(cont$ ?v0 ))(member$ (inr$ ?v2 )(cont$ ?v0 ))))(= (= (fun_app$e root$ ?v1 )(fun_app$e root$ ?v2 ))(= ?v1 ?v2 )))):named a15 ))
(assert (! (forall ((?v0 Dtree$ ))(! (= (fun_app$f (hsubst_c$ tr0$ )?v0 )(ite (= (fun_app$e root$ ?v0 )(fun_app$e root$ tr0$ ))(cont$ tr0$ )(cont$ ?v0 ))):pattern ((fun_app$f (hsubst_c$ tr0$ )?v0 )))):named a16 ))
(assert (! (=> (forall ((?v0 Dtree$ ))(=> (and (wf$ ?v0 )(= tr1a$ (fun_app$d (hsubst$ tr0$ )?v0 )))false ))false ):named a17 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (fun_app$e root$ (fun_app$d (hsubst$ ?v0 )?v1 ))(fun_app$e root$ ?v1 ))):named a18 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (= (fun_app$e root$ ?v0 )(fun_app$e root$ ?v1 ))(= (fun_app$d (hsubst$ ?v1 )?v0 )(fun_app$d (hsubst$ ?v1 )?v1 )))):named a19 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (and (wf$ ?v0 )(member$ (inr$ ?v1 )(cont$ ?v0 )))(wf$ ?v1 ))):named a20 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (and (wf$ ?v0 )(member$ (inr$ ?v1 )(cont$ ?v0 )))(= (fun_app$g (subtrOf$ ?v0 )(fun_app$e root$ ?v1 ))?v1 ))):named a21 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a22 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a23 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (and (= (fun_app$e root$ ?v0 )(fun_app$e root$ ?v1 ))(= (cont$ ?v0 )(cont$ ?v1 )))(= ?v0 ?v1 ))):named a24 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ )(?v3 Dtree$ ))(=> (and (fun_app$h (fun_app$i (fun_app$j inFr2$ ?v0 )?v1 )?v2 )(and (member$b (fun_app$e root$ ?v3 )?v0 )(member$ (inr$ ?v1 )(cont$ ?v3 ))))(fun_app$h (fun_app$i (fun_app$j inFr2$ ?v0 )?v3 )?v2 ))):named a25 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ ))(= (fun_app$c (fun_app$k (inItr$ ?v0 )?v1 )?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 (fun_app$e root$ ?v3 ))(member$b (fun_app$e root$ ?v3 )?v4 )))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 N$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$b (fun_app$e root$ ?v3 )?v4 )(and (member$ (inr$ ?v5 )(cont$ ?v3 ))(fun_app$c (fun_app$k (inItr$ ?v4 )?v5 )?v6 )))))))))):named a26 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ ))(=> (and (fun_app$c (fun_app$k (inItr$ ?v0 )?v1 )?v2 )(and (forall ((?v3 Dtree$ )(?v4 N_set$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 (fun_app$e root$ ?v3 ))(member$b (fun_app$e root$ ?v3 )?v4 ))))false ))(forall ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 N$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$b (fun_app$e root$ ?v3 )?v4 )(and (member$ (inr$ ?v5 )(cont$ ?v3 ))(fun_app$c (fun_app$k (inItr$ ?v4 )?v5 )?v6 ))))))false ))))false )):named a27 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 N$ ))(=> (and (member$b (fun_app$e root$ ?v0 )?v1 )(and (member$ (inr$ ?v2 )(cont$ ?v0 ))(fun_app$c (fun_app$k (inItr$ ?v1 )?v2 )?v3 )))(fun_app$c (fun_app$k (inItr$ ?v1 )?v0 )?v3 ))):named a28 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(! (= (fun_app$f (hsubst_c$ ?v0 )?v1 )(ite (= (fun_app$e root$ ?v1 )(fun_app$e root$ ?v0 ))(cont$ ?v0 )(cont$ ?v1 ))):pattern ((fun_app$f (hsubst_c$ ?v0 )?v1 )))):named a29 ))
(assert (! (inj_on$ root$ (vimage$ uu$ (cont$ (fun_app$d (hsubst$ tr0$ )tra$ )))):named a30 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 T$ ))(=> (and (member$b (fun_app$e root$ ?v0 )?v1 )(and (member$ (inr$ ?v2 )(cont$ ?v0 ))(fun_app$h (fun_app$i (fun_app$j inFr$ ?v1 )?v2 )?v3 )))(fun_app$h (fun_app$i (fun_app$j inFr$ ?v1 )?v0 )?v3 ))):named a31 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(= (fun_app$b (fun_app$l (subtr2$ ?v0 )?v1 )?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v3 )(member$b (fun_app$e root$ ?v3 )?v4 )))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 Dtree$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$b (fun_app$e root$ ?v3 )?v4 )(and (member$ (inr$ ?v3 )(cont$ ?v5 ))(fun_app$b (fun_app$l (subtr2$ ?v4 )?v5 )?v6 )))))))))):named a32 ))
(assert (! (= inFr$ inFr2$ ):named a33 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ )(?v3 Dtree$ ))(=> (and (fun_app$b (fun_app$l (subtr2$ ?v0 )?v1 )?v2 )(fun_app$b (fun_app$l (subtr2$ ?v0 )?v2 )?v3 ))(fun_app$b (fun_app$l (subtr2$ ?v0 )?v1 )?v3 ))):named a34 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ ))(=> (member$b (fun_app$e root$ ?v0 )?v1 )(fun_app$b (fun_app$l (subtr2$ ?v1 )?v0 )?v0 ))):named a35 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (fun_app$b (fun_app$l (subtr2$ ?v0 )?v1 )?v2 )(member$b (fun_app$e root$ ?v1 )?v0 ))):named a36 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (fun_app$b (fun_app$l (subtr2$ ?v0 )?v1 )?v2 )(member$b (fun_app$e root$ ?v2 )?v0 ))):named a37 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 T$ ))(=> (not (member$b (fun_app$e root$ ?v0 )?v1 ))(not (fun_app$h (fun_app$i (fun_app$j inFr$ ?v1 )?v0 )?v2 )))):named a38 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (fun_app$h (fun_app$i (fun_app$j inFr$ ?v0 )?v1 )?v2 )(member$b (fun_app$e root$ ?v1 )?v0 ))):named a39 ))
(assert (! (forall ((?v0 Dtree$ ))(=> (wf$ ?v0 )(inj_on$ root$ (vimage$ uu$ (cont$ ?v0 ))))):named a40 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ ))(=> (member$b (fun_app$e root$ ?v0 )?v1 )(fun_app$c (fun_app$k (inItr$ ?v1 )?v0 )(fun_app$e root$ ?v0 )))):named a41 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 N$ ))(=> (fun_app$c (fun_app$k (inItr$ ?v0 )?v1 )?v2 )(member$b (fun_app$e root$ ?v1 )?v0 ))):named a42 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (fun_app$h (fun_app$i (fun_app$j inFr2$ ?v0 )?v1 )?v2 )(member$b (fun_app$e root$ ?v1 )?v0 ))):named a43 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a44 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 Dtree$ ))(=> (and (member$b (fun_app$e root$ ?v0 )?v1 )(and (member$ (inr$ ?v0 )(cont$ ?v2 ))(fun_app$b (fun_app$l (subtr2$ ?v1 )?v2 )?v3 )))(fun_app$b (fun_app$l (subtr2$ ?v1 )?v0 )?v3 ))):named a45 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 Dtree$ ))(=> (and (member$b (fun_app$e root$ ?v0 )?v1 )(and (member$ (inr$ ?v2 )(cont$ ?v0 ))(fun_app$b (fun_app$l (subtr2$ ?v1 )?v3 )?v2 )))(fun_app$b (fun_app$l (subtr2$ ?v1 )?v3 )?v0 ))):named a46 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 Dtree$ ))(=> (and (fun_app$b (fun_app$l (subtr2$ ?v0 )?v1 )?v2 )(and (forall ((?v3 Dtree$ )(?v4 N_set$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v3 )(member$b (fun_app$e root$ ?v3 )?v4 ))))false ))(forall ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 Dtree$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$b (fun_app$e root$ ?v3 )?v4 )(and (member$ (inr$ ?v3 )(cont$ ?v5 ))(fun_app$b (fun_app$l (subtr2$ ?v4 )?v5 )?v6 ))))))false ))))false )):named a47 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(= (inFrr$ ?v0 ?v1 ?v2 )(exists ((?v3 Dtree$ ))(and (member$ (inr$ ?v3 )(cont$ ?v1 ))(fun_app$h (fun_app$i (fun_app$j inFr$ ?v0 )?v3 )?v2 ))))):named a48 ))
(assert (! (= (hsubst$ tr0$ )(fun_app$m (unfold$ hsubst_r$ )(hsubst_c$ tr0$ ))):named a49 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_dtree_fun$ )(?v2 Dtree_set$ ))(= (member$ ?v0 (vimage$a ?v1 ?v2 ))(member$a (fun_app$n ?v1 ?v0 )?v2 ))):named a50 ))
(assert (! (forall ((?v0 N$ )(?v1 N_dtree_fun$ )(?v2 Dtree_set$ ))(= (member$b ?v0 (vimage$b ?v1 ?v2 ))(member$a (fun_app$g ?v1 ?v0 )?v2 ))):named a51 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_N_fun$ )(?v2 N_set$ ))(= (member$a ?v0 (vimage$c ?v1 ?v2 ))(member$b (fun_app$e ?v1 ?v0 )?v2 ))):named a52 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_dtree_fun$ )(?v2 Dtree_set$ ))(= (member$a ?v0 (vimage$d ?v1 ?v2 ))(member$a (fun_app$d ?v1 ?v0 )?v2 ))):named a53 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_T_dtree_sum_fun$ )(?v2 T_dtree_sum_set$ ))(= (member$ ?v0 (vimage$e ?v1 ?v2 ))(member$ (fun_app$o ?v1 ?v0 )?v2 ))):named a54 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_N_fun$ )(?v2 N_set$ ))(= (member$ ?v0 (vimage$f ?v1 ?v2 ))(member$b (fun_app$p ?v1 ?v0 )?v2 ))):named a55 ))
(assert (! (forall ((?v0 N$ )(?v1 N_T_dtree_sum_fun$ )(?v2 T_dtree_sum_set$ ))(= (member$b ?v0 (vimage$g ?v1 ?v2 ))(member$ (fun_app$q ?v1 ?v0 )?v2 ))):named a56 ))
(assert (! (forall ((?v0 N$ )(?v1 N_N_fun$ )(?v2 N_set$ ))(= (member$b ?v0 (vimage$h ?v1 ?v2 ))(member$b (fun_app$r ?v1 ?v0 )?v2 ))):named a57 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_T_dtree_sum_fun$ )(?v2 T_dtree_sum_set$ ))(= (member$a ?v0 (vimage$ ?v1 ?v2 ))(member$ (fun_app$ ?v1 ?v0 )?v2 ))):named a58 ))
(assert (! (forall ((?v0 Dtree_N_fun$ )(?v1 Dtree$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= (fun_app$e ?v0 ?v1 )?v2 )(member$b ?v2 ?v3 ))(member$a ?v1 (vimage$c ?v0 ?v3 )))):named a59 ))
(assert (! (forall ((?v0 T_dtree_sum_dtree_fun$ )(?v1 T_dtree_sum$ )(?v2 Dtree$ )(?v3 Dtree_set$ ))(=> (and (= (fun_app$n ?v0 ?v1 )?v2 )(member$a ?v2 ?v3 ))(member$ ?v1 (vimage$a ?v0 ?v3 )))):named a60 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 N$ )(?v2 Dtree$ )(?v3 Dtree_set$ ))(=> (and (= (fun_app$g ?v0 ?v1 )?v2 )(member$a ?v2 ?v3 ))(member$b ?v1 (vimage$b ?v0 ?v3 )))):named a61 ))
(assert (! (forall ((?v0 Dtree_dtree_fun$ )(?v1 Dtree$ )(?v2 Dtree$ )(?v3 Dtree_set$ ))(=> (and (= (fun_app$d ?v0 ?v1 )?v2 )(member$a ?v2 ?v3 ))(member$a ?v1 (vimage$d ?v0 ?v3 )))):named a62 ))
(assert (! (forall ((?v0 T_dtree_sum_T_dtree_sum_fun$ )(?v1 T_dtree_sum$ )(?v2 T_dtree_sum$ )(?v3 T_dtree_sum_set$ ))(=> (and (= (fun_app$o ?v0 ?v1 )?v2 )(member$ ?v2 ?v3 ))(member$ ?v1 (vimage$e ?v0 ?v3 )))):named a63 ))
(assert (! (forall ((?v0 N_T_dtree_sum_fun$ )(?v1 N$ )(?v2 T_dtree_sum$ )(?v3 T_dtree_sum_set$ ))(=> (and (= (fun_app$q ?v0 ?v1 )?v2 )(member$ ?v2 ?v3 ))(member$b ?v1 (vimage$g ?v0 ?v3 )))):named a64 ))
(assert (! (forall ((?v0 T_dtree_sum_N_fun$ )(?v1 T_dtree_sum$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= (fun_app$p ?v0 ?v1 )?v2 )(member$b ?v2 ?v3 ))(member$ ?v1 (vimage$f ?v0 ?v3 )))):named a65 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= (fun_app$r ?v0 ?v1 )?v2 )(member$b ?v2 ?v3 ))(member$b ?v1 (vimage$h ?v0 ?v3 )))):named a66 ))
(assert (! (forall ((?v0 Dtree_T_dtree_sum_fun$ )(?v1 Dtree$ )(?v2 T_dtree_sum$ )(?v3 T_dtree_sum_set$ ))(=> (and (= (fun_app$ ?v0 ?v1 )?v2 )(member$ ?v2 ?v3 ))(member$a ?v1 (vimage$ ?v0 ?v3 )))):named a67 ))
(assert (! (forall ((?v0 Dtree_bool_fun$ )(?v1 Dtree_bool_fun$ ))(=> (forall ((?v2 Dtree$ ))(= (fun_app$b ?v0 ?v2 )(fun_app$b ?v1 ?v2 )))(= (collect$ ?v0 )(collect$ ?v1 )))):named a68 ))
(assert (! (forall ((?v0 N_bool_fun$ )(?v1 N_bool_fun$ ))(=> (forall ((?v2 N$ ))(= (fun_app$c ?v0 ?v2 )(fun_app$c ?v1 ?v2 )))(= (collect$a ?v0 )(collect$a ?v1 )))):named a69 ))
(assert (! (forall ((?v0 T_dtree_sum_bool_fun$ )(?v1 T_dtree_sum_bool_fun$ ))(=> (forall ((?v2 T_dtree_sum$ ))(= (fun_app$a ?v0 ?v2 )(fun_app$a ?v1 ?v2 )))(= (collect$b ?v0 )(collect$b ?v1 )))):named a70 ))
(assert (! (forall ((?v0 Dtree_set$ ))(= (collect$ (uua$ ?v0 ))?v0 )):named a71 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ ))(= (collect$b (uub$ ?v0 ))?v0 )):named a72 ))
(assert (! (forall ((?v0 N_set$ ))(= (collect$a (uuc$ ?v0 ))?v0 )):named a73 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_bool_fun$ ))(= (member$a ?v0 (collect$ ?v1 ))(fun_app$b ?v1 ?v0 ))):named a74 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_bool_fun$ ))(= (member$ ?v0 (collect$b ?v1 ))(fun_app$a ?v1 ?v0 ))):named a75 ))
(assert (! (forall ((?v0 N$ )(?v1 N_bool_fun$ ))(= (member$b ?v0 (collect$a ?v1 ))(fun_app$c ?v1 ?v0 ))):named a76 ))
(assert (! (forall ((?v0 Dtree$ ))(finite$ (fun_app$f (hsubst_c$ tr0$ )?v0 ))):named a77 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ ))(=> (and (wf$ ?v0 )(fun_app$b (fun_app$l (subtr$ ?v1 )?v2 )?v0 ))(inj_on$ root$ (vimage$ uu$ (cont$ ?v2 ))))):named a78 ))
(assert (! (forall ((?v0 Dtree$ ))(=> (not (= (fun_app$e root$ ?v0 )(fun_app$e root$ tr0$ )))(= (vimage$ uu$ (cont$ (fun_app$d (hsubst$ tr0$ )?v0 )))(image$ (hsubst$ tr0$ )(vimage$ uu$ (cont$ ?v0 )))))):named a79 ))
(check-sat )
;(get-unsat-core )
