;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort T_set$ 0 )
(declare-sort N_N_fun$ 0 )
(declare-sort N_T_fun$ 0 )
(declare-sort T_N_fun$ 0 )
(declare-sort T_T_fun$ 0 )
(declare-sort N_bool_fun$ 0 )
(declare-sort T_bool_fun$ 0 )
(declare-sort N_set_N_set_fun$ 0 )
(declare-sort T_dtree_sum_set$ 0 )
(declare-sort T_set_T_set_fun$ 0 )
(declare-sort N_T_dtree_sum_fun$ 0 )
(declare-sort T_T_dtree_sum_fun$ 0 )
(declare-sort T_dtree_sum_N_fun$ 0 )
(declare-sort T_dtree_sum_T_fun$ 0 )
(declare-sort Dtree_T_bool_fun_fun$ 0 )
(declare-sort T_dtree_sum_bool_fun$ 0 )
(declare-sort T_dtree_sum_T_dtree_sum_fun$ 0 )
(declare-sort T_dtree_sum_set_T_dtree_sum_set_fun$ 0 )
(declare-datatypes ()((T_dtree_sum$ (inl$ (projl$ T$ ))(inr$ (projr$ Dtree$ )))))
(declare-fun t$ ()T$ )
(declare-fun ns$ ()N_set$ )
(declare-fun tr$ ()Dtree$ )
(declare-fun uu$ ()T_T_dtree_sum_fun$ )
(declare-fun bot$ ()N_set$ )
(declare-fun tr0$ ()Dtree$ )
(declare-fun bot$a ()T_dtree_sum_set$ )
(declare-fun bot$b ()T_set$ )
(declare-fun cont$ (Dtree$ )T_dtree_sum_set$ )
(declare-fun inFr$ (N_set$ )Dtree_T_bool_fun_fun$ )
(declare-fun root$ (Dtree$ )N$ )
(declare-fun inFrr$ (N_set$ )Dtree_T_bool_fun_fun$ )
(declare-fun minus$ (N_set$ )N_set_N_set_fun$ )
(declare-fun hsubst$ (Dtree$ Dtree$ )Dtree$ )
(declare-fun insert$ (N$ N_set$ )N_set$ )
(declare-fun member$ (T$ T_set$ )Bool )
(declare-fun minus$a (T_dtree_sum_set$ )T_dtree_sum_set_T_dtree_sum_set_fun$ )
(declare-fun minus$b (T_set$ )T_set_T_set_fun$ )
(declare-fun vimage$ (T_T_dtree_sum_fun$ T_dtree_sum_set$ )T_set$ )
(declare-fun collect$ (T_dtree_sum_bool_fun$ )T_dtree_sum_set$ )
(declare-fun fun_app$ (T_T_dtree_sum_fun$ T$ )T_dtree_sum$ )
(declare-fun insert$a (T_dtree_sum$ T_dtree_sum_set$ )T_dtree_sum_set$ )
(declare-fun insert$b (T$ T_set$ )T_set$ )
(declare-fun member$a (N$ N_set$ )Bool )
(declare-fun member$b (T_dtree_sum$ T_dtree_sum_set$ )Bool )
(declare-fun vimage$a (T_dtree_sum_N_fun$ N_set$ )T_dtree_sum_set$ )
(declare-fun vimage$b (T_N_fun$ N_set$ )T_set$ )
(declare-fun vimage$c (N_T_dtree_sum_fun$ T_dtree_sum_set$ )N_set$ )
(declare-fun vimage$d (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum_set$ )T_dtree_sum_set$ )
(declare-fun vimage$e (N_T_fun$ T_set$ )N_set$ )
(declare-fun vimage$f (T_dtree_sum_T_fun$ T_set$ )T_dtree_sum_set$ )
(declare-fun vimage$g (T_T_fun$ T_set$ )T_set$ )
(declare-fun vimage$h (N_N_fun$ N_set$ )N_set$ )
(declare-fun collect$a (T_bool_fun$ )T_set$ )
(declare-fun collect$b (N_bool_fun$ )N_set$ )
(declare-fun fun_app$a (T_bool_fun$ T$ )Bool )
(declare-fun fun_app$b (Dtree_T_bool_fun_fun$ Dtree$ )T_bool_fun$ )
(declare-fun fun_app$c (N_set_N_set_fun$ N_set$ )N_set$ )
(declare-fun fun_app$d (T_dtree_sum_set_T_dtree_sum_set_fun$ T_dtree_sum_set$ )T_dtree_sum_set$ )
(declare-fun fun_app$e (T_set_T_set_fun$ T_set$ )T_set$ )
(declare-fun fun_app$f (N_T_dtree_sum_fun$ N$ )T_dtree_sum$ )
(declare-fun fun_app$g (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum$ )T_dtree_sum$ )
(declare-fun fun_app$h (T_T_fun$ T$ )T$ )
(declare-fun fun_app$i (N_T_fun$ N$ )T$ )
(declare-fun fun_app$j (T_dtree_sum_T_fun$ T_dtree_sum$ )T$ )
(declare-fun fun_app$k (T_N_fun$ T$ )N$ )
(declare-fun fun_app$l (N_N_fun$ N$ )N$ )
(declare-fun fun_app$m (T_dtree_sum_N_fun$ T_dtree_sum$ )N$ )
(declare-fun fun_app$n (T_dtree_sum_bool_fun$ T_dtree_sum$ )Bool )
(declare-fun fun_app$o (N_bool_fun$ N$ )Bool )
(declare-fun hsubst_c$ (Dtree$ Dtree$ )T_dtree_sum_set$ )
(assert (! (forall ((?v0 T$ ))(! (= (fun_app$ uu$ ?v0 )(inl$ ?v0 )):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (not (or (member$ t$ (vimage$ uu$ (cont$ tr0$ )))(or (fun_app$a (fun_app$b (inFrr$ (fun_app$c (minus$ ns$ )(insert$ (root$ tr0$ )bot$ )))tr0$ )t$ )(fun_app$a (fun_app$b (inFr$ (fun_app$c (minus$ ns$ )(insert$ (root$ tr0$ )bot$ )))tr$ )t$ )))):named a1 ))
(assert (! (forall ((?v0 Dtree$ ))(! (= (hsubst_c$ tr0$ ?v0 )(ite (= (root$ ?v0 )(root$ tr0$ ))(cont$ tr0$ )(cont$ ?v0 ))):pattern ((hsubst_c$ tr0$ ?v0 )))):named a2 ))
(assert (! (fun_app$a (fun_app$b (inFr$ ns$ )(hsubst$ tr0$ tr$ ))t$ ):named a3 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (fun_app$a (fun_app$b (inFr$ ?v0 )?v1 )?v2 )(member$a (root$ ?v1 )?v0 ))):named a4 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 T$ ))(=> (and (member$a (root$ ?v0 )?v1 )(member$b (inl$ ?v2 )(cont$ ?v0 )))(fun_app$a (fun_app$b (inFr$ ?v1 )?v0 )?v2 ))):named a5 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 T$ ))(=> (not (member$a (root$ ?v0 )?v1 ))(not (fun_app$a (fun_app$b (inFr$ ?v1 )?v0 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_set$ ))(= (insert$a ?v0 (fun_app$d (minus$a ?v1 )(insert$a ?v0 bot$a )))(insert$a ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 T$ )(?v1 T_set$ ))(= (insert$b ?v0 (fun_app$e (minus$b ?v1 )(insert$b ?v0 bot$b )))(insert$b ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 N$ )(?v1 N_set$ ))(= (insert$ ?v0 (fun_app$c (minus$ ?v1 )(insert$ ?v0 bot$ )))(insert$ ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 T_dtree_sum_N_fun$ ))(= (vimage$a ?v0 bot$ )bot$a )):named a10 ))
(assert (! (forall ((?v0 T_N_fun$ ))(= (vimage$b ?v0 bot$ )bot$b )):named a11 ))
(assert (! (forall ((?v0 N_T_dtree_sum_fun$ ))(= (vimage$c ?v0 bot$a )bot$ )):named a12 ))
(assert (! (forall ((?v0 T_dtree_sum_T_dtree_sum_fun$ ))(= (vimage$d ?v0 bot$a )bot$a )):named a13 ))
(assert (! (forall ((?v0 N_T_fun$ ))(= (vimage$e ?v0 bot$b )bot$ )):named a14 ))
(assert (! (forall ((?v0 T_dtree_sum_T_fun$ ))(= (vimage$f ?v0 bot$b )bot$a )):named a15 ))
(assert (! (forall ((?v0 T_T_fun$ ))(= (vimage$g ?v0 bot$b )bot$b )):named a16 ))
(assert (! (forall ((?v0 T_T_dtree_sum_fun$ ))(= (vimage$ ?v0 bot$a )bot$b )):named a17 ))
(assert (! (forall ((?v0 N_N_fun$ ))(= (vimage$h ?v0 bot$ )bot$ )):named a18 ))
(assert (! (forall ((?v0 T$ )(?v1 T_set$ )(?v2 T_set$ ))(=> (member$ ?v0 ?v1 )(= (fun_app$e (minus$b (insert$b ?v0 ?v2 ))?v1 )(fun_app$e (minus$b ?v2 )?v1 )))):named a19 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_set$ )(?v2 T_dtree_sum_set$ ))(=> (member$b ?v0 ?v1 )(= (fun_app$d (minus$a (insert$a ?v0 ?v2 ))?v1 )(fun_app$d (minus$a ?v2 )?v1 )))):named a20 ))
(assert (! (forall ((?v0 N$ )(?v1 N_set$ )(?v2 N_set$ ))(=> (member$a ?v0 ?v1 )(= (fun_app$c (minus$ (insert$ ?v0 ?v2 ))?v1 )(fun_app$c (minus$ ?v2 )?v1 )))):named a21 ))
(assert (! (forall ((?v0 T$ )(?v1 T_set$ )(?v2 T_set$ ))(=> (not (member$ ?v0 ?v1 ))(= (fun_app$e (minus$b ?v1 )(insert$b ?v0 ?v2 ))(fun_app$e (minus$b ?v1 )?v2 )))):named a22 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_set$ )(?v2 T_dtree_sum_set$ ))(=> (not (member$b ?v0 ?v1 ))(= (fun_app$d (minus$a ?v1 )(insert$a ?v0 ?v2 ))(fun_app$d (minus$a ?v1 )?v2 )))):named a23 ))
(assert (! (forall ((?v0 N$ )(?v1 N_set$ )(?v2 N_set$ ))(=> (not (member$a ?v0 ?v1 ))(= (fun_app$c (minus$ ?v1 )(insert$ ?v0 ?v2 ))(fun_app$c (minus$ ?v1 )?v2 )))):named a24 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ ))(= (fun_app$d (minus$a ?v0 )bot$a )?v0 )):named a25 ))
(assert (! (forall ((?v0 T_set$ ))(= (fun_app$e (minus$b ?v0 )bot$b )?v0 )):named a26 ))
(assert (! (forall ((?v0 N_set$ ))(= (fun_app$c (minus$ ?v0 )bot$ )?v0 )):named a27 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ ))(! (= (fun_app$d (minus$a ?v0 )?v0 )bot$a ):pattern ((minus$a ?v0 )))):named a28 ))
(assert (! (forall ((?v0 T_set$ ))(! (= (fun_app$e (minus$b ?v0 )?v0 )bot$b ):pattern ((minus$b ?v0 )))):named a29 ))
(assert (! (forall ((?v0 N_set$ ))(! (= (fun_app$c (minus$ ?v0 )?v0 )bot$ ):pattern ((minus$ ?v0 )))):named a30 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ ))(= (fun_app$d (minus$a bot$a )?v0 )bot$a )):named a31 ))
(assert (! (forall ((?v0 T_set$ ))(= (fun_app$e (minus$b bot$b )?v0 )bot$b )):named a32 ))
(assert (! (forall ((?v0 N_set$ ))(= (fun_app$c (minus$ bot$ )?v0 )bot$ )):named a33 ))
(assert (! (forall ((?v0 T$ ))(member$ ?v0 (insert$b ?v0 bot$b ))):named a34 ))
(assert (! (forall ((?v0 T_dtree_sum$ ))(member$b ?v0 (insert$a ?v0 bot$a ))):named a35 ))
(assert (! (forall ((?v0 N$ ))(member$a ?v0 (insert$ ?v0 bot$ ))):named a36 ))
(assert (! (forall ((?v0 Dtree$ ))(=> (= (root$ ?v0 )(root$ tr0$ ))(= (hsubst$ tr0$ ?v0 )(hsubst$ tr0$ tr0$ )))):named a37 ))
(assert (! (forall ((?v0 N$ )(?v1 N_T_dtree_sum_fun$ )(?v2 T_dtree_sum$ ))(= (member$a ?v0 (vimage$c ?v1 (insert$a ?v2 bot$a )))(= (fun_app$f ?v1 ?v0 )?v2 ))):named a38 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_T_dtree_sum_fun$ )(?v2 T_dtree_sum$ ))(= (member$b ?v0 (vimage$d ?v1 (insert$a ?v2 bot$a )))(= (fun_app$g ?v1 ?v0 )?v2 ))):named a39 ))
(assert (! (forall ((?v0 T$ )(?v1 T_T_fun$ )(?v2 T$ ))(= (member$ ?v0 (vimage$g ?v1 (insert$b ?v2 bot$b )))(= (fun_app$h ?v1 ?v0 )?v2 ))):named a40 ))
(assert (! (forall ((?v0 N$ )(?v1 N_T_fun$ )(?v2 T$ ))(= (member$a ?v0 (vimage$e ?v1 (insert$b ?v2 bot$b )))(= (fun_app$i ?v1 ?v0 )?v2 ))):named a41 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_T_fun$ )(?v2 T$ ))(= (member$b ?v0 (vimage$f ?v1 (insert$b ?v2 bot$b )))(= (fun_app$j ?v1 ?v0 )?v2 ))):named a42 ))
(assert (! (forall ((?v0 T$ )(?v1 T_T_dtree_sum_fun$ )(?v2 T_dtree_sum$ ))(= (member$ ?v0 (vimage$ ?v1 (insert$a ?v2 bot$a )))(= (fun_app$ ?v1 ?v0 )?v2 ))):named a43 ))
(assert (! (forall ((?v0 T$ )(?v1 T_N_fun$ )(?v2 N$ ))(= (member$ ?v0 (vimage$b ?v1 (insert$ ?v2 bot$ )))(= (fun_app$k ?v1 ?v0 )?v2 ))):named a44 ))
(assert (! (forall ((?v0 N$ )(?v1 N_N_fun$ )(?v2 N$ ))(= (member$a ?v0 (vimage$h ?v1 (insert$ ?v2 bot$ )))(= (fun_app$l ?v1 ?v0 )?v2 ))):named a45 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_N_fun$ )(?v2 N$ ))(= (member$b ?v0 (vimage$a ?v1 (insert$ ?v2 bot$ )))(= (fun_app$m ?v1 ?v0 )?v2 ))):named a46 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum$ )(?v2 T_dtree_sum_set$ ))(= (fun_app$d (minus$a ?v0 )(insert$a ?v1 ?v2 ))(fun_app$d (minus$a (fun_app$d (minus$a ?v0 )(insert$a ?v1 bot$a )))?v2 ))):named a47 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T$ )(?v2 T_set$ ))(= (fun_app$e (minus$b ?v0 )(insert$b ?v1 ?v2 ))(fun_app$e (minus$b (fun_app$e (minus$b ?v0 )(insert$b ?v1 bot$b )))?v2 ))):named a48 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N$ )(?v2 N_set$ ))(= (fun_app$c (minus$ ?v0 )(insert$ ?v1 ?v2 ))(fun_app$c (minus$ (fun_app$c (minus$ ?v0 )(insert$ ?v1 bot$ )))?v2 ))):named a49 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ )(?v1 T_dtree_sum$ )(?v2 T_dtree_sum_set$ ))(= (fun_app$d (minus$a ?v0 )(insert$a ?v1 ?v2 ))(fun_app$d (minus$a (fun_app$d (minus$a ?v0 )?v2 ))(insert$a ?v1 bot$a )))):named a50 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T$ )(?v2 T_set$ ))(= (fun_app$e (minus$b ?v0 )(insert$b ?v1 ?v2 ))(fun_app$e (minus$b (fun_app$e (minus$b ?v0 )?v2 ))(insert$b ?v1 bot$b )))):named a51 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N$ )(?v2 N_set$ ))(= (fun_app$c (minus$ ?v0 )(insert$ ?v1 ?v2 ))(fun_app$c (minus$ (fun_app$c (minus$ ?v0 )?v2 ))(insert$ ?v1 bot$ )))):named a52 ))
(assert (! (forall ((?v0 T$ ))(= (member$ ?v0 bot$b )false )):named a53 ))
(assert (! (forall ((?v0 T_dtree_sum$ ))(= (member$b ?v0 bot$a )false )):named a54 ))
(assert (! (forall ((?v0 N$ ))(= (member$a ?v0 bot$ )false )):named a55 ))
(assert (! (forall ((?v0 T_dtree_sum_bool_fun$ ))(= (= bot$a (collect$ ?v0 ))(forall ((?v1 T_dtree_sum$ ))(not (fun_app$n ?v0 ?v1 ))))):named a56 ))
(assert (! (forall ((?v0 T_bool_fun$ ))(= (= bot$b (collect$a ?v0 ))(forall ((?v1 T$ ))(not (fun_app$a ?v0 ?v1 ))))):named a57 ))
(assert (! (forall ((?v0 N_bool_fun$ ))(= (= bot$ (collect$b ?v0 ))(forall ((?v1 N$ ))(not (fun_app$o ?v0 ?v1 ))))):named a58 ))
(assert (! (forall ((?v0 T_set$ ))(= (forall ((?v1 T$ ))(not (member$ ?v1 ?v0 )))(= ?v0 bot$b ))):named a59 ))
(assert (! (forall ((?v0 T_dtree_sum_set$ ))(= (forall ((?v1 T_dtree_sum$ ))(not (member$b ?v1 ?v0 )))(= ?v0 bot$a ))):named a60 ))
(assert (! (forall ((?v0 N_set$ ))(= (forall ((?v1 N$ ))(not (member$a ?v1 ?v0 )))(= ?v0 bot$ ))):named a61 ))
(assert (! (forall ((?v0 T_dtree_sum_bool_fun$ ))(= (= (collect$ ?v0 )bot$a )(forall ((?v1 T_dtree_sum$ ))(not (fun_app$n ?v0 ?v1 ))))):named a62 ))
(assert (! (forall ((?v0 T_bool_fun$ ))(= (= (collect$a ?v0 )bot$b )(forall ((?v1 T$ ))(not (fun_app$a ?v0 ?v1 ))))):named a63 ))
(assert (! (forall ((?v0 N_bool_fun$ ))(= (= (collect$b ?v0 )bot$ )(forall ((?v1 N$ ))(not (fun_app$o ?v0 ?v1 ))))):named a64 ))
(assert (! (forall ((?v0 T$ )(?v1 T_set$ )(?v2 T$ ))(=> (=> (not (member$ ?v0 ?v1 ))(= ?v0 ?v2 ))(member$ ?v0 (insert$b ?v2 ?v1 )))):named a65 ))
(assert (! (forall ((?v0 N$ )(?v1 N_set$ )(?v2 N$ ))(=> (=> (not (member$a ?v0 ?v1 ))(= ?v0 ?v2 ))(member$a ?v0 (insert$ ?v2 ?v1 )))):named a66 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_set$ )(?v2 T_dtree_sum$ ))(=> (=> (not (member$b ?v0 ?v1 ))(= ?v0 ?v2 ))(member$b ?v0 (insert$a ?v2 ?v1 )))):named a67 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ )(?v2 T_set$ ))(= (member$ ?v0 (insert$b ?v1 ?v2 ))(or (= ?v0 ?v1 )(member$ ?v0 ?v2 )))):named a68 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ )(?v2 N_set$ ))(= (member$a ?v0 (insert$ ?v1 ?v2 ))(or (= ?v0 ?v1 )(member$a ?v0 ?v2 )))):named a69 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum$ )(?v2 T_dtree_sum_set$ ))(= (member$b ?v0 (insert$a ?v1 ?v2 ))(or (= ?v0 ?v1 )(member$b ?v0 ?v2 )))):named a70 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_set$ ))(= (insert$a ?v0 (insert$a ?v0 ?v1 ))(insert$a ?v0 ?v1 ))):named a71 ))
(assert (! (forall ((?v0 T$ )(?v1 T_set$ ))(= (insert$b ?v0 (insert$b ?v0 ?v1 ))(insert$b ?v0 ?v1 ))):named a72 ))
(assert (! (forall ((?v0 N$ )(?v1 N_set$ ))(= (insert$ ?v0 (insert$ ?v0 ?v1 ))(insert$ ?v0 ?v1 ))):named a73 ))
(check-sat )
;(get-unsat-core )
