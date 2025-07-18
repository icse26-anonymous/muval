;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort N_N_fun$ 0 )
(declare-sort Dtree_set$ 0 )
(declare-sort N_bool_fun$ 0 )
(declare-sort Dtree_N_fun$ 0 )
(declare-sort N_dtree_fun$ 0 )
(declare-sort T_N_sum_set$ 0 )
(declare-sort N_T_N_sum_fun$ 0 )
(declare-sort T_N_sum_N_fun$ 0 )
(declare-sort Dtree_bool_fun$ 0 )
(declare-sort Dtree_dtree_fun$ 0 )
(declare-sort T_N_sum_bool_fun$ 0 )
(declare-sort Dtree_T_N_sum_fun$ 0 )
(declare-sort T_N_sum_dtree_fun$ 0 )
(declare-sort T_N_sum_T_N_sum_fun$ 0 )
(declare-sort N_set_N_bool_fun_fun$ 0 )
(declare-sort Dtree_set_N_bool_fun_fun$ 0 )
(declare-sort N_set_dtree_bool_fun_fun$ 0 )
(declare-sort N_bool_fun_N_bool_fun_fun$ 0 )
(declare-sort N_set_T_N_sum_bool_fun_fun$ 0 )
(declare-sort T_N_sum_set_N_bool_fun_fun$ 0 )
(declare-sort Dtree_set_dtree_bool_fun_fun$ 0 )
(declare-sort Dtree_bool_fun_N_bool_fun_fun$ 0 )
(declare-sort N_bool_fun_dtree_bool_fun_fun$ 0 )
(declare-sort Dtree_set_T_N_sum_bool_fun_fun$ 0 )
(declare-sort T_N_sum_set_dtree_bool_fun_fun$ 0 )
(declare-sort N_bool_fun_T_N_sum_bool_fun_fun$ 0 )
(declare-sort T_N_sum_bool_fun_N_bool_fun_fun$ 0 )
(declare-sort T_N_sum_set_T_N_sum_bool_fun_fun$ 0 )
(declare-sort Dtree_bool_fun_dtree_bool_fun_fun$ 0 )
(declare-sort Dtree_bool_fun_T_N_sum_bool_fun_fun$ 0 )
(declare-sort T_N_sum_bool_fun_dtree_bool_fun_fun$ 0 )
(declare-sort T_N_sum_bool_fun_T_N_sum_bool_fun_fun$ 0 )
(declare-sort T_N_sum$ 0)
(declare-fun projl$ (T_N_sum$)T$)
(declare-fun inl$ (T$ )T_N_sum$)
(declare-fun projr$ (T_N_sum$)N$)
(declare-fun inr$ (N$ )T_N_sum$)
(declare-fun h$ (Dtree$ )N_dtree_fun$ )
(declare-fun x$ ()N$ )
(declare-fun uu$ ()N_T_N_sum_fun$ )
(declare-fun ftr$ (N$ )Dtree$ )
(declare-fun tns$ ()T_N_sum_set$ )
(declare-fun uua$ ()Dtree_bool_fun$ )
(declare-fun uub$ ()N_bool_fun$ )
(declare-fun uuc$ (T_N_sum_N_fun$ )N_bool_fun_T_N_sum_bool_fun_fun$ )
(declare-fun uud$ (T_N_sum_dtree_fun$ )Dtree_bool_fun_T_N_sum_bool_fun_fun$ )
(declare-fun uue$ (Dtree_T_N_sum_fun$ )T_N_sum_bool_fun_dtree_bool_fun_fun$ )
(declare-fun uuf$ (T_N_sum_T_N_sum_fun$ )T_N_sum_bool_fun_T_N_sum_bool_fun_fun$ )
(declare-fun uug$ (N_T_N_sum_fun$ )T_N_sum_bool_fun_N_bool_fun_fun$ )
(declare-fun uuh$ (N_N_fun$ )N_bool_fun_N_bool_fun_fun$ )
(declare-fun uui$ (Dtree_N_fun$ )N_bool_fun_dtree_bool_fun_fun$ )
(declare-fun uuj$ (N_dtree_fun$ )Dtree_bool_fun_N_bool_fun_fun$ )
(declare-fun uuk$ (Dtree_dtree_fun$ )Dtree_bool_fun_dtree_bool_fun_fun$ )
(declare-fun uul$ ()T_N_sum_T_N_sum_fun$ )
(declare-fun uum$ ()Dtree_dtree_fun$ )
(declare-fun uun$ ()N_N_fun$ )
(declare-fun uuo$ (T_N_sum_N_fun$ )N_set_T_N_sum_bool_fun_fun$ )
(declare-fun uup$ (T_N_sum_dtree_fun$ )Dtree_set_T_N_sum_bool_fun_fun$ )
(declare-fun uuq$ (T_N_sum_T_N_sum_fun$ )T_N_sum_set_T_N_sum_bool_fun_fun$ )
(declare-fun uur$ (N_N_fun$ )N_set_N_bool_fun_fun$ )
(declare-fun uus$ (N_dtree_fun$ )Dtree_set_N_bool_fun_fun$ )
(declare-fun uut$ (N_T_N_sum_fun$ )T_N_sum_set_N_bool_fun_fun$ )
(declare-fun uuu$ (Dtree_N_fun$ )N_set_dtree_bool_fun_fun$ )
(declare-fun uuv$ (Dtree_dtree_fun$ )Dtree_set_dtree_bool_fun_fun$ )
(declare-fun uuw$ (Dtree_T_N_sum_fun$ )T_N_sum_set_dtree_bool_fun_fun$ )
(declare-fun rcut$ (Dtree$ )Dtree$ )
(declare-fun root$ (Dtree$ )N$ )
(declare-fun member$ (N$ N_set$ )Bool )
(declare-fun vimage$ (N_T_N_sum_fun$ T_N_sum_set$ )N_set$ )
(declare-fun collect$ (Dtree_bool_fun$ )Dtree_set$ )
(declare-fun fun_app$ (Dtree_bool_fun$ Dtree$ )Bool )
(declare-fun member$a (Dtree$ Dtree_set$ )Bool )
(declare-fun member$b (T_N_sum$ T_N_sum_set$ )Bool )
(declare-fun vimage$a (T_N_sum_N_fun$ N_set$ )T_N_sum_set$ )
(declare-fun vimage$b (T_N_sum_dtree_fun$ Dtree_set$ )T_N_sum_set$ )
(declare-fun vimage$c (Dtree_T_N_sum_fun$ T_N_sum_set$ )Dtree_set$ )
(declare-fun vimage$d (T_N_sum_T_N_sum_fun$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun vimage$e (N_N_fun$ N_set$ )N_set$ )
(declare-fun vimage$f (Dtree_N_fun$ N_set$ )Dtree_set$ )
(declare-fun vimage$g (N_dtree_fun$ Dtree_set$ )N_set$ )
(declare-fun vimage$h (Dtree_dtree_fun$ Dtree_set$ )Dtree_set$ )
(declare-fun collect$a (N_bool_fun$ )N_set$ )
(declare-fun collect$b (T_N_sum_bool_fun$ )T_N_sum_set$ )
(declare-fun fun_app$a (N_bool_fun$ N$ )Bool )
(declare-fun fun_app$b (N_T_N_sum_fun$ N$ )T_N_sum$ )
(declare-fun fun_app$c (T_N_sum_bool_fun$ T_N_sum$ )Bool )
(declare-fun fun_app$d (T_N_sum_set_T_N_sum_bool_fun_fun$ T_N_sum_set$ )T_N_sum_bool_fun$ )
(declare-fun fun_app$e (T_N_sum_T_N_sum_fun$ T_N_sum$ )T_N_sum$ )
(declare-fun fun_app$f (Dtree_set_T_N_sum_bool_fun_fun$ Dtree_set$ )T_N_sum_bool_fun$ )
(declare-fun fun_app$g (T_N_sum_dtree_fun$ T_N_sum$ )Dtree$ )
(declare-fun fun_app$h (N_set_T_N_sum_bool_fun_fun$ N_set$ )T_N_sum_bool_fun$ )
(declare-fun fun_app$i (T_N_sum_N_fun$ T_N_sum$ )N$ )
(declare-fun fun_app$j (T_N_sum_set_dtree_bool_fun_fun$ T_N_sum_set$ )Dtree_bool_fun$ )
(declare-fun fun_app$k (Dtree_T_N_sum_fun$ Dtree$ )T_N_sum$ )
(declare-fun fun_app$l (Dtree_set_dtree_bool_fun_fun$ Dtree_set$ )Dtree_bool_fun$ )
(declare-fun fun_app$m (Dtree_dtree_fun$ Dtree$ )Dtree$ )
(declare-fun fun_app$n (N_set_dtree_bool_fun_fun$ N_set$ )Dtree_bool_fun$ )
(declare-fun fun_app$o (Dtree_N_fun$ Dtree$ )N$ )
(declare-fun fun_app$p (T_N_sum_set_N_bool_fun_fun$ T_N_sum_set$ )N_bool_fun$ )
(declare-fun fun_app$q (Dtree_set_N_bool_fun_fun$ Dtree_set$ )N_bool_fun$ )
(declare-fun fun_app$r (N_dtree_fun$ N$ )Dtree$ )
(declare-fun fun_app$s (N_set_N_bool_fun_fun$ N_set$ )N_bool_fun$ )
(declare-fun fun_app$t (N_N_fun$ N$ )N$ )
(declare-fun fun_app$u (T_N_sum_bool_fun_T_N_sum_bool_fun_fun$ T_N_sum_bool_fun$ )T_N_sum_bool_fun$ )
(declare-fun fun_app$v (Dtree_bool_fun_T_N_sum_bool_fun_fun$ Dtree_bool_fun$ )T_N_sum_bool_fun$ )
(declare-fun fun_app$w (N_bool_fun_T_N_sum_bool_fun_fun$ N_bool_fun$ )T_N_sum_bool_fun$ )
(declare-fun fun_app$x (T_N_sum_bool_fun_dtree_bool_fun_fun$ T_N_sum_bool_fun$ )Dtree_bool_fun$ )
(declare-fun fun_app$y (Dtree_bool_fun_dtree_bool_fun_fun$ Dtree_bool_fun$ )Dtree_bool_fun$ )
(declare-fun fun_app$z (N_bool_fun_dtree_bool_fun_fun$ N_bool_fun$ )Dtree_bool_fun$ )
(declare-fun hsubst_r$ (Dtree$ )N$ )
(declare-fun fun_app$aa (T_N_sum_bool_fun_N_bool_fun_fun$ T_N_sum_bool_fun$ )N_bool_fun$ )
(declare-fun fun_app$ab (Dtree_bool_fun_N_bool_fun_fun$ Dtree_bool_fun$ )N_bool_fun$ )
(declare-fun fun_app$ac (N_bool_fun_N_bool_fun_fun$ N_bool_fun$ )N_bool_fun$ )
(assert (! (forall ((?v0 Dtree$ ))(! (= (fun_app$ uua$ ?v0 )(exists ((?v1 N$ ))(and (member$ ?v1 (vimage$ uu$ tns$ ))(= ?v0 (ftr$ ?v1 ))))):pattern ((fun_app$ uua$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 N$ ))(! (= (fun_app$a uub$ ?v0 )(exists ((?v1 Dtree$ ))(and (member$a ?v1 (collect$ uua$ ))(= ?v0 (root$ ?v1 ))))):pattern ((fun_app$a uub$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 N$ ))(! (= (fun_app$b uu$ ?v0 )(inr$ ?v0 )):pattern ((fun_app$b uu$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$ )(?v1 T_N_sum_set$ )(?v2 T_N_sum$ ))(! (= (fun_app$c (fun_app$d (uuq$ ?v0 )?v1 )?v2 )(member$b (fun_app$e ?v0 ?v2 )?v1 )):pattern ((fun_app$c (fun_app$d (uuq$ ?v0 )?v1 )?v2 )))):named a3 ))
(assert (! (forall ((?v0 T_N_sum_dtree_fun$ )(?v1 Dtree_set$ )(?v2 T_N_sum$ ))(! (= (fun_app$c (fun_app$f (uup$ ?v0 )?v1 )?v2 )(member$a (fun_app$g ?v0 ?v2 )?v1 )):pattern ((fun_app$c (fun_app$f (uup$ ?v0 )?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 T_N_sum_N_fun$ )(?v1 N_set$ )(?v2 T_N_sum$ ))(! (= (fun_app$c (fun_app$h (uuo$ ?v0 )?v1 )?v2 )(member$ (fun_app$i ?v0 ?v2 )?v1 )):pattern ((fun_app$c (fun_app$h (uuo$ ?v0 )?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 Dtree_T_N_sum_fun$ )(?v1 T_N_sum_set$ )(?v2 Dtree$ ))(! (= (fun_app$ (fun_app$j (uuw$ ?v0 )?v1 )?v2 )(member$b (fun_app$k ?v0 ?v2 )?v1 )):pattern ((fun_app$ (fun_app$j (uuw$ ?v0 )?v1 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 Dtree_dtree_fun$ )(?v1 Dtree_set$ )(?v2 Dtree$ ))(! (= (fun_app$ (fun_app$l (uuv$ ?v0 )?v1 )?v2 )(member$a (fun_app$m ?v0 ?v2 )?v1 )):pattern ((fun_app$ (fun_app$l (uuv$ ?v0 )?v1 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 Dtree_N_fun$ )(?v1 N_set$ )(?v2 Dtree$ ))(! (= (fun_app$ (fun_app$n (uuu$ ?v0 )?v1 )?v2 )(member$ (fun_app$o ?v0 ?v2 )?v1 )):pattern ((fun_app$ (fun_app$n (uuu$ ?v0 )?v1 )?v2 )))):named a8 ))
(assert (! (forall ((?v0 N_T_N_sum_fun$ )(?v1 T_N_sum_set$ )(?v2 N$ ))(! (= (fun_app$a (fun_app$p (uut$ ?v0 )?v1 )?v2 )(member$b (fun_app$b ?v0 ?v2 )?v1 )):pattern ((fun_app$a (fun_app$p (uut$ ?v0 )?v1 )?v2 )))):named a9 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 Dtree_set$ )(?v2 N$ ))(! (= (fun_app$a (fun_app$q (uus$ ?v0 )?v1 )?v2 )(member$a (fun_app$r ?v0 ?v2 )?v1 )):pattern ((fun_app$a (fun_app$q (uus$ ?v0 )?v1 )?v2 )))):named a10 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N_set$ )(?v2 N$ ))(! (= (fun_app$a (fun_app$s (uur$ ?v0 )?v1 )?v2 )(member$ (fun_app$t ?v0 ?v2 )?v1 )):pattern ((fun_app$a (fun_app$s (uur$ ?v0 )?v1 )?v2 )))):named a11 ))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$ )(?v1 T_N_sum_bool_fun$ )(?v2 T_N_sum$ ))(! (= (fun_app$c (fun_app$u (uuf$ ?v0 )?v1 )?v2 )(fun_app$c ?v1 (fun_app$e ?v0 ?v2 ))):pattern ((fun_app$c (fun_app$u (uuf$ ?v0 )?v1 )?v2 )))):named a12 ))
(assert (! (forall ((?v0 T_N_sum_dtree_fun$ )(?v1 Dtree_bool_fun$ )(?v2 T_N_sum$ ))(! (= (fun_app$c (fun_app$v (uud$ ?v0 )?v1 )?v2 )(fun_app$ ?v1 (fun_app$g ?v0 ?v2 ))):pattern ((fun_app$c (fun_app$v (uud$ ?v0 )?v1 )?v2 )))):named a13 ))
(assert (! (forall ((?v0 T_N_sum_N_fun$ )(?v1 N_bool_fun$ )(?v2 T_N_sum$ ))(! (= (fun_app$c (fun_app$w (uuc$ ?v0 )?v1 )?v2 )(fun_app$a ?v1 (fun_app$i ?v0 ?v2 ))):pattern ((fun_app$c (fun_app$w (uuc$ ?v0 )?v1 )?v2 )))):named a14 ))
(assert (! (forall ((?v0 Dtree_T_N_sum_fun$ )(?v1 T_N_sum_bool_fun$ )(?v2 Dtree$ ))(! (= (fun_app$ (fun_app$x (uue$ ?v0 )?v1 )?v2 )(fun_app$c ?v1 (fun_app$k ?v0 ?v2 ))):pattern ((fun_app$ (fun_app$x (uue$ ?v0 )?v1 )?v2 )))):named a15 ))
(assert (! (forall ((?v0 Dtree_dtree_fun$ )(?v1 Dtree_bool_fun$ )(?v2 Dtree$ ))(! (= (fun_app$ (fun_app$y (uuk$ ?v0 )?v1 )?v2 )(fun_app$ ?v1 (fun_app$m ?v0 ?v2 ))):pattern ((fun_app$ (fun_app$y (uuk$ ?v0 )?v1 )?v2 )))):named a16 ))
(assert (! (forall ((?v0 Dtree_N_fun$ )(?v1 N_bool_fun$ )(?v2 Dtree$ ))(! (= (fun_app$ (fun_app$z (uui$ ?v0 )?v1 )?v2 )(fun_app$a ?v1 (fun_app$o ?v0 ?v2 ))):pattern ((fun_app$ (fun_app$z (uui$ ?v0 )?v1 )?v2 )))):named a17 ))
(assert (! (forall ((?v0 N_T_N_sum_fun$ )(?v1 T_N_sum_bool_fun$ )(?v2 N$ ))(! (= (fun_app$a (fun_app$aa (uug$ ?v0 )?v1 )?v2 )(fun_app$c ?v1 (fun_app$b ?v0 ?v2 ))):pattern ((fun_app$a (fun_app$aa (uug$ ?v0 )?v1 )?v2 )))):named a18 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 Dtree_bool_fun$ )(?v2 N$ ))(! (= (fun_app$a (fun_app$ab (uuj$ ?v0 )?v1 )?v2 )(fun_app$ ?v1 (fun_app$r ?v0 ?v2 ))):pattern ((fun_app$a (fun_app$ab (uuj$ ?v0 )?v1 )?v2 )))):named a19 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N_bool_fun$ )(?v2 N$ ))(! (= (fun_app$a (fun_app$ac (uuh$ ?v0 )?v1 )?v2 )(fun_app$a ?v1 (fun_app$t ?v0 ?v2 ))):pattern ((fun_app$a (fun_app$ac (uuh$ ?v0 )?v1 )?v2 )))):named a20 ))
(assert (! (forall ((?v0 T_N_sum$ ))(! (= (fun_app$e uul$ ?v0 )?v0 ):pattern ((fun_app$e uul$ ?v0 )))):named a21 ))
(assert (! (forall ((?v0 Dtree$ ))(! (= (fun_app$m uum$ ?v0 )?v0 ):pattern ((fun_app$m uum$ ?v0 )))):named a22 ))
(assert (! (forall ((?v0 N$ ))(! (= (fun_app$t uun$ ?v0 )?v0 ):pattern ((fun_app$t uun$ ?v0 )))):named a23 ))
(assert (! (not (member$ x$ (collect$a uub$ ))):named a24 ))
(assert (! (member$b (inr$ x$ )tns$ ):named a25 ))
(assert (! (forall ((?v0 T_N_sum_N_fun$ )(?v1 N_bool_fun$ ))(= (vimage$a ?v0 (collect$a ?v1 ))(collect$b (fun_app$w (uuc$ ?v0 )?v1 )))):named a26 ))
(assert (! (forall ((?v0 T_N_sum_dtree_fun$ )(?v1 Dtree_bool_fun$ ))(= (vimage$b ?v0 (collect$ ?v1 ))(collect$b (fun_app$v (uud$ ?v0 )?v1 )))):named a27 ))
(assert (! (forall ((?v0 Dtree_T_N_sum_fun$ )(?v1 T_N_sum_bool_fun$ ))(= (vimage$c ?v0 (collect$b ?v1 ))(collect$ (fun_app$x (uue$ ?v0 )?v1 )))):named a28 ))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$ )(?v1 T_N_sum_bool_fun$ ))(= (vimage$d ?v0 (collect$b ?v1 ))(collect$b (fun_app$u (uuf$ ?v0 )?v1 )))):named a29 ))
(assert (! (forall ((?v0 N_T_N_sum_fun$ )(?v1 T_N_sum_bool_fun$ ))(= (vimage$ ?v0 (collect$b ?v1 ))(collect$a (fun_app$aa (uug$ ?v0 )?v1 )))):named a30 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N_bool_fun$ ))(= (vimage$e ?v0 (collect$a ?v1 ))(collect$a (fun_app$ac (uuh$ ?v0 )?v1 )))):named a31 ))
(assert (! (forall ((?v0 Dtree_N_fun$ )(?v1 N_bool_fun$ ))(= (vimage$f ?v0 (collect$a ?v1 ))(collect$ (fun_app$z (uui$ ?v0 )?v1 )))):named a32 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 Dtree_bool_fun$ ))(= (vimage$g ?v0 (collect$ ?v1 ))(collect$a (fun_app$ab (uuj$ ?v0 )?v1 )))):named a33 ))
(assert (! (forall ((?v0 Dtree_dtree_fun$ )(?v1 Dtree_bool_fun$ ))(= (vimage$h ?v0 (collect$ ?v1 ))(collect$ (fun_app$y (uuk$ ?v0 )?v1 )))):named a34 ))
(assert (! (forall ((?v0 T_N_sum_set$ ))(= (vimage$d uul$ ?v0 )?v0 )):named a35 ))
(assert (! (forall ((?v0 Dtree_set$ ))(= (vimage$h uum$ ?v0 )?v0 )):named a36 ))
(assert (! (forall ((?v0 N_set$ ))(= (vimage$e uun$ ?v0 )?v0 )):named a37 ))
(assert (! (forall ((?v0 N$ )(?v1 N_N_fun$ )(?v2 N_set$ ))(= (member$ ?v0 (vimage$e ?v1 ?v2 ))(member$ (fun_app$t ?v1 ?v0 )?v2 ))):named a38 ))
(assert (! (forall ((?v0 N$ )(?v1 N_dtree_fun$ )(?v2 Dtree_set$ ))(= (member$ ?v0 (vimage$g ?v1 ?v2 ))(member$a (fun_app$r ?v1 ?v0 )?v2 ))):named a39 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_N_fun$ )(?v2 N_set$ ))(= (member$a ?v0 (vimage$f ?v1 ?v2 ))(member$ (fun_app$o ?v1 ?v0 )?v2 ))):named a40 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_dtree_fun$ )(?v2 Dtree_set$ ))(= (member$a ?v0 (vimage$h ?v1 ?v2 ))(member$a (fun_app$m ?v1 ?v0 )?v2 ))):named a41 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(= (member$a ?v0 (vimage$c ?v1 ?v2 ))(member$b (fun_app$k ?v1 ?v0 )?v2 ))):named a42 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_N_fun$ )(?v2 N_set$ ))(= (member$b ?v0 (vimage$a ?v1 ?v2 ))(member$ (fun_app$i ?v1 ?v0 )?v2 ))):named a43 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_dtree_fun$ )(?v2 Dtree_set$ ))(= (member$b ?v0 (vimage$b ?v1 ?v2 ))(member$a (fun_app$g ?v1 ?v0 )?v2 ))):named a44 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(= (member$b ?v0 (vimage$d ?v1 ?v2 ))(member$b (fun_app$e ?v1 ?v0 )?v2 ))):named a45 ))
(assert (! (forall ((?v0 N$ )(?v1 N_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(= (member$ ?v0 (vimage$ ?v1 ?v2 ))(member$b (fun_app$b ?v1 ?v0 )?v2 ))):named a46 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= (fun_app$t ?v0 ?v1 )?v2 )(member$ ?v2 ?v3 ))(member$ ?v1 (vimage$e ?v0 ?v3 )))):named a47 ))
(assert (! (forall ((?v0 Dtree_N_fun$ )(?v1 Dtree$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= (fun_app$o ?v0 ?v1 )?v2 )(member$ ?v2 ?v3 ))(member$a ?v1 (vimage$f ?v0 ?v3 )))):named a48 ))
(assert (! (forall ((?v0 T_N_sum_N_fun$ )(?v1 T_N_sum$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= (fun_app$i ?v0 ?v1 )?v2 )(member$ ?v2 ?v3 ))(member$b ?v1 (vimage$a ?v0 ?v3 )))):named a49 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 N$ )(?v2 Dtree$ )(?v3 Dtree_set$ ))(=> (and (= (fun_app$r ?v0 ?v1 )?v2 )(member$a ?v2 ?v3 ))(member$ ?v1 (vimage$g ?v0 ?v3 )))):named a50 ))
(assert (! (forall ((?v0 Dtree_dtree_fun$ )(?v1 Dtree$ )(?v2 Dtree$ )(?v3 Dtree_set$ ))(=> (and (= (fun_app$m ?v0 ?v1 )?v2 )(member$a ?v2 ?v3 ))(member$a ?v1 (vimage$h ?v0 ?v3 )))):named a51 ))
(assert (! (forall ((?v0 T_N_sum_dtree_fun$ )(?v1 T_N_sum$ )(?v2 Dtree$ )(?v3 Dtree_set$ ))(=> (and (= (fun_app$g ?v0 ?v1 )?v2 )(member$a ?v2 ?v3 ))(member$b ?v1 (vimage$b ?v0 ?v3 )))):named a52 ))
(assert (! (forall ((?v0 Dtree_T_N_sum_fun$ )(?v1 Dtree$ )(?v2 T_N_sum$ )(?v3 T_N_sum_set$ ))(=> (and (= (fun_app$k ?v0 ?v1 )?v2 )(member$b ?v2 ?v3 ))(member$a ?v1 (vimage$c ?v0 ?v3 )))):named a53 ))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$ )(?v1 T_N_sum$ )(?v2 T_N_sum$ )(?v3 T_N_sum_set$ ))(=> (and (= (fun_app$e ?v0 ?v1 )?v2 )(member$b ?v2 ?v3 ))(member$b ?v1 (vimage$d ?v0 ?v3 )))):named a54 ))
(assert (! (forall ((?v0 N_T_N_sum_fun$ )(?v1 N$ )(?v2 T_N_sum$ )(?v3 T_N_sum_set$ ))(=> (and (= (fun_app$b ?v0 ?v1 )?v2 )(member$b ?v2 ?v3 ))(member$ ?v1 (vimage$ ?v0 ?v3 )))):named a55 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a56 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a57 ))
(assert (! (forall ((?v0 Dtree$ ))(! (= (hsubst_r$ ?v0 )(root$ ?v0 )):pattern ((hsubst_r$ ?v0 )))):named a58 ))
(assert (! (forall ((?v0 T_N_sum_N_fun$ )(?v1 N_set$ ))(= (vimage$a ?v0 ?v1 )(collect$b (fun_app$h (uuo$ ?v0 )?v1 )))):named a59 ))
(assert (! (forall ((?v0 T_N_sum_dtree_fun$ )(?v1 Dtree_set$ ))(= (vimage$b ?v0 ?v1 )(collect$b (fun_app$f (uup$ ?v0 )?v1 )))):named a60 ))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$ )(?v1 T_N_sum_set$ ))(= (vimage$d ?v0 ?v1 )(collect$b (fun_app$d (uuq$ ?v0 )?v1 )))):named a61 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N_set$ ))(= (vimage$e ?v0 ?v1 )(collect$a (fun_app$s (uur$ ?v0 )?v1 )))):named a62 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 Dtree_set$ ))(= (vimage$g ?v0 ?v1 )(collect$a (fun_app$q (uus$ ?v0 )?v1 )))):named a63 ))
(assert (! (forall ((?v0 N_T_N_sum_fun$ )(?v1 T_N_sum_set$ ))(= (vimage$ ?v0 ?v1 )(collect$a (fun_app$p (uut$ ?v0 )?v1 )))):named a64 ))
(assert (! (forall ((?v0 Dtree_N_fun$ )(?v1 N_set$ ))(= (vimage$f ?v0 ?v1 )(collect$ (fun_app$n (uuu$ ?v0 )?v1 )))):named a65 ))
(assert (! (forall ((?v0 Dtree_dtree_fun$ )(?v1 Dtree_set$ ))(= (vimage$h ?v0 ?v1 )(collect$ (fun_app$l (uuv$ ?v0 )?v1 )))):named a66 ))
(assert (! (forall ((?v0 Dtree_T_N_sum_fun$ )(?v1 T_N_sum_set$ ))(= (vimage$c ?v0 ?v1 )(collect$ (fun_app$j (uuw$ ?v0 )?v1 )))):named a67 ))
(assert (! (forall ((?v0 Dtree$ ))(= (root$ (rcut$ ?v0 ))(root$ ?v0 ))):named a68 ))
(assert (! (forall ((?v0 N_bool_fun$ )(?v1 T_N_sum_N_fun$ )(?v2 T_N_sum_bool_fun$ ))(=> (forall ((?v3 T_N_sum$ ))(= (fun_app$a ?v0 (fun_app$i ?v1 ?v3 ))(fun_app$c ?v2 ?v3 )))(= (vimage$a ?v1 (collect$a ?v0 ))(collect$b ?v2 )))):named a69 ))
(assert (! (forall ((?v0 Dtree_bool_fun$ )(?v1 T_N_sum_dtree_fun$ )(?v2 T_N_sum_bool_fun$ ))(=> (forall ((?v3 T_N_sum$ ))(= (fun_app$ ?v0 (fun_app$g ?v1 ?v3 ))(fun_app$c ?v2 ?v3 )))(= (vimage$b ?v1 (collect$ ?v0 ))(collect$b ?v2 )))):named a70 ))
(assert (! (forall ((?v0 T_N_sum_bool_fun$ )(?v1 Dtree_T_N_sum_fun$ )(?v2 Dtree_bool_fun$ ))(=> (forall ((?v3 Dtree$ ))(= (fun_app$c ?v0 (fun_app$k ?v1 ?v3 ))(fun_app$ ?v2 ?v3 )))(= (vimage$c ?v1 (collect$b ?v0 ))(collect$ ?v2 )))):named a71 ))
(assert (! (forall ((?v0 T_N_sum_bool_fun$ )(?v1 T_N_sum_T_N_sum_fun$ )(?v2 T_N_sum_bool_fun$ ))(=> (forall ((?v3 T_N_sum$ ))(= (fun_app$c ?v0 (fun_app$e ?v1 ?v3 ))(fun_app$c ?v2 ?v3 )))(= (vimage$d ?v1 (collect$b ?v0 ))(collect$b ?v2 )))):named a72 ))
(assert (! (forall ((?v0 T_N_sum_bool_fun$ )(?v1 N_T_N_sum_fun$ )(?v2 N_bool_fun$ ))(=> (forall ((?v3 N$ ))(= (fun_app$c ?v0 (fun_app$b ?v1 ?v3 ))(fun_app$a ?v2 ?v3 )))(= (vimage$ ?v1 (collect$b ?v0 ))(collect$a ?v2 )))):named a73 ))
(assert (! (forall ((?v0 N_bool_fun$ )(?v1 N_N_fun$ )(?v2 N_bool_fun$ ))(=> (forall ((?v3 N$ ))(= (fun_app$a ?v0 (fun_app$t ?v1 ?v3 ))(fun_app$a ?v2 ?v3 )))(= (vimage$e ?v1 (collect$a ?v0 ))(collect$a ?v2 )))):named a74 ))
(assert (! (forall ((?v0 N_bool_fun$ )(?v1 Dtree_N_fun$ )(?v2 Dtree_bool_fun$ ))(=> (forall ((?v3 Dtree$ ))(= (fun_app$a ?v0 (fun_app$o ?v1 ?v3 ))(fun_app$ ?v2 ?v3 )))(= (vimage$f ?v1 (collect$a ?v0 ))(collect$ ?v2 )))):named a75 ))
(assert (! (forall ((?v0 Dtree_bool_fun$ )(?v1 N_dtree_fun$ )(?v2 N_bool_fun$ ))(=> (forall ((?v3 N$ ))(= (fun_app$ ?v0 (fun_app$r ?v1 ?v3 ))(fun_app$a ?v2 ?v3 )))(= (vimage$g ?v1 (collect$ ?v0 ))(collect$a ?v2 )))):named a76 ))
(assert (! (forall ((?v0 Dtree_bool_fun$ )(?v1 Dtree_dtree_fun$ )(?v2 Dtree_bool_fun$ ))(=> (forall ((?v3 Dtree$ ))(= (fun_app$ ?v0 (fun_app$m ?v1 ?v3 ))(fun_app$ ?v2 ?v3 )))(= (vimage$h ?v1 (collect$ ?v0 ))(collect$ ?v2 )))):named a77 ))
(assert (! (forall ((?v0 N$ )(?v1 N_N_fun$ )(?v2 N_set$ ))(=> (and (member$ ?v0 (vimage$e ?v1 ?v2 ))(forall ((?v3 N$ ))(=> (and (= (fun_app$t ?v1 ?v0 )?v3 )(member$ ?v3 ?v2 ))false )))false )):named a78 ))
(assert (! (forall ((?v0 N$ )(?v1 N_dtree_fun$ )(?v2 Dtree_set$ ))(=> (and (member$ ?v0 (vimage$g ?v1 ?v2 ))(forall ((?v3 Dtree$ ))(=> (and (= (fun_app$r ?v1 ?v0 )?v3 )(member$a ?v3 ?v2 ))false )))false )):named a79 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_N_fun$ )(?v2 N_set$ ))(=> (and (member$a ?v0 (vimage$f ?v1 ?v2 ))(forall ((?v3 N$ ))(=> (and (= (fun_app$o ?v1 ?v0 )?v3 )(member$ ?v3 ?v2 ))false )))false )):named a80 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_dtree_fun$ )(?v2 Dtree_set$ ))(=> (and (member$a ?v0 (vimage$h ?v1 ?v2 ))(forall ((?v3 Dtree$ ))(=> (and (= (fun_app$m ?v1 ?v0 )?v3 )(member$a ?v3 ?v2 ))false )))false )):named a81 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(=> (and (member$a ?v0 (vimage$c ?v1 ?v2 ))(forall ((?v3 T_N_sum$ ))(=> (and (= (fun_app$k ?v1 ?v0 )?v3 )(member$b ?v3 ?v2 ))false )))false )):named a82 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_N_fun$ )(?v2 N_set$ ))(=> (and (member$b ?v0 (vimage$a ?v1 ?v2 ))(forall ((?v3 N$ ))(=> (and (= (fun_app$i ?v1 ?v0 )?v3 )(member$ ?v3 ?v2 ))false )))false )):named a83 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_dtree_fun$ )(?v2 Dtree_set$ ))(=> (and (member$b ?v0 (vimage$b ?v1 ?v2 ))(forall ((?v3 Dtree$ ))(=> (and (= (fun_app$g ?v1 ?v0 )?v3 )(member$a ?v3 ?v2 ))false )))false )):named a84 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(=> (and (member$b ?v0 (vimage$d ?v1 ?v2 ))(forall ((?v3 T_N_sum$ ))(=> (and (= (fun_app$e ?v1 ?v0 )?v3 )(member$b ?v3 ?v2 ))false )))false )):named a85 ))
(assert (! (forall ((?v0 N$ )(?v1 N_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(=> (and (member$ ?v0 (vimage$ ?v1 ?v2 ))(forall ((?v3 T_N_sum$ ))(=> (and (= (fun_app$b ?v1 ?v0 )?v3 )(member$b ?v3 ?v2 ))false )))false )):named a86 ))
(assert (! (forall ((?v0 N$ )(?v1 N_N_fun$ )(?v2 N_set$ ))(=> (member$ ?v0 (vimage$e ?v1 ?v2 ))(member$ (fun_app$t ?v1 ?v0 )?v2 ))):named a87 ))
(assert (! (forall ((?v0 N$ )(?v1 N_dtree_fun$ )(?v2 Dtree_set$ ))(=> (member$ ?v0 (vimage$g ?v1 ?v2 ))(member$a (fun_app$r ?v1 ?v0 )?v2 ))):named a88 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_N_fun$ )(?v2 N_set$ ))(=> (member$a ?v0 (vimage$f ?v1 ?v2 ))(member$ (fun_app$o ?v1 ?v0 )?v2 ))):named a89 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_dtree_fun$ )(?v2 Dtree_set$ ))(=> (member$a ?v0 (vimage$h ?v1 ?v2 ))(member$a (fun_app$m ?v1 ?v0 )?v2 ))):named a90 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(=> (member$a ?v0 (vimage$c ?v1 ?v2 ))(member$b (fun_app$k ?v1 ?v0 )?v2 ))):named a91 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_N_fun$ )(?v2 N_set$ ))(=> (member$b ?v0 (vimage$a ?v1 ?v2 ))(member$ (fun_app$i ?v1 ?v0 )?v2 ))):named a92 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_dtree_fun$ )(?v2 Dtree_set$ ))(=> (member$b ?v0 (vimage$b ?v1 ?v2 ))(member$a (fun_app$g ?v1 ?v0 )?v2 ))):named a93 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(=> (member$b ?v0 (vimage$d ?v1 ?v2 ))(member$b (fun_app$e ?v1 ?v0 )?v2 ))):named a94 ))
(assert (! (forall ((?v0 N$ )(?v1 N_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(=> (member$ ?v0 (vimage$ ?v1 ?v2 ))(member$b (fun_app$b ?v1 ?v0 )?v2 ))):named a95 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_bool_fun$ ))(= (exists ((?v2 N$ ))(and (member$ ?v2 ?v0 )(fun_app$a ?v1 ?v2 )))(exists ((?v2 N$ ))(and (member$ ?v2 ?v0 )(fun_app$a ?v1 ?v2 ))))):named a96 ))
(assert (! (forall ((?v0 Dtree_set$ )(?v1 Dtree_bool_fun$ ))(= (exists ((?v2 Dtree$ ))(and (member$a ?v2 ?v0 )(fun_app$ ?v1 ?v2 )))(exists ((?v2 Dtree$ ))(and (member$a ?v2 ?v0 )(fun_app$ ?v1 ?v2 ))))):named a97 ))
(assert (! (forall ((?v0 T_N_sum_set$ )(?v1 T_N_sum_bool_fun$ ))(= (exists ((?v2 T_N_sum$ ))(and (member$b ?v2 ?v0 )(fun_app$c ?v1 ?v2 )))(exists ((?v2 T_N_sum$ ))(and (member$b ?v2 ?v0 )(fun_app$c ?v1 ?v2 ))))):named a98 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(=> (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a99 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N$ )(?v2 N_set$ ))(=> (member$ (fun_app$t ?v0 ?v1 )?v2 )(member$ ?v1 (vimage$e ?v0 ?v2 )))):named a100 ))
(assert (! (forall ((?v0 Dtree_N_fun$ )(?v1 Dtree$ )(?v2 N_set$ ))(=> (member$ (fun_app$o ?v0 ?v1 )?v2 )(member$a ?v1 (vimage$f ?v0 ?v2 )))):named a101 ))
(assert (! (forall ((?v0 T_N_sum_N_fun$ )(?v1 T_N_sum$ )(?v2 N_set$ ))(=> (member$ (fun_app$i ?v0 ?v1 )?v2 )(member$b ?v1 (vimage$a ?v0 ?v2 )))):named a102 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 N$ )(?v2 Dtree_set$ ))(=> (member$a (fun_app$r ?v0 ?v1 )?v2 )(member$ ?v1 (vimage$g ?v0 ?v2 )))):named a103 ))
(assert (! (forall ((?v0 Dtree_dtree_fun$ )(?v1 Dtree$ )(?v2 Dtree_set$ ))(=> (member$a (fun_app$m ?v0 ?v1 )?v2 )(member$a ?v1 (vimage$h ?v0 ?v2 )))):named a104 ))
(assert (! (forall ((?v0 T_N_sum_dtree_fun$ )(?v1 T_N_sum$ )(?v2 Dtree_set$ ))(=> (member$a (fun_app$g ?v0 ?v1 )?v2 )(member$b ?v1 (vimage$b ?v0 ?v2 )))):named a105 ))
(assert (! (forall ((?v0 Dtree_T_N_sum_fun$ )(?v1 Dtree$ )(?v2 T_N_sum_set$ ))(=> (member$b (fun_app$k ?v0 ?v1 )?v2 )(member$a ?v1 (vimage$c ?v0 ?v2 )))):named a106 ))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$ )(?v1 T_N_sum$ )(?v2 T_N_sum_set$ ))(=> (member$b (fun_app$e ?v0 ?v1 )?v2 )(member$b ?v1 (vimage$d ?v0 ?v2 )))):named a107 ))
(assert (! (forall ((?v0 N_T_N_sum_fun$ )(?v1 N$ )(?v2 T_N_sum_set$ ))(=> (member$b (fun_app$b ?v0 ?v1 )?v2 )(member$ ?v1 (vimage$ ?v0 ?v2 )))):named a108 ))
(assert (! (forall ((?v0 Dtree$ ))(! (= (rcut$ ?v0 )(fun_app$r (h$ ?v0 )(root$ ?v0 ))):pattern ((rcut$ ?v0 )))):named a109 ))
(check-sat )
;(get-unsat-core )
