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
(declare-sort N_set_set$ 0 )
(declare-sort T_set_set$ 0 )
(declare-sort N_bool_fun$ 0 )
(declare-sort T_bool_fun$ 0 )
(declare-sort N_T_set_fun$ 0 )
(declare-sort N_set_N_fun$ 0 )
(declare-sort T_N_sum_set$ 0 )
(declare-sort T_T_set_fun$ 0 )
(declare-sort T_set_N_fun$ 0 )
(declare-sort T_set_T_fun$ 0 )
(declare-sort N_set_set_set$ 0 )
(declare-sort T_N_sum_T_fun$ 0 )
(declare-sort T_T_N_sum_fun$ 0 )
(declare-sort T_set_set_set$ 0 )
(declare-sort N_set_bool_fun$ 0 )
(declare-sort T_set_bool_fun$ 0 )
(declare-sort T_N_sum_set_set$ 0 )
(declare-sort T_set_T_set_fun$ 0 )
(declare-sort T_N_sum_bool_fun$ 0 )
(declare-sort N_set_set_set_set$ 0 )
(declare-sort T_N_sum_T_set_fun$ 0 )
(declare-sort T_set_T_N_sum_fun$ 0 )
(declare-sort T_set_set_set_set$ 0 )
(declare-sort N_set_set_bool_fun$ 0 )
(declare-sort T_set_set_bool_fun$ 0 )
(declare-sort T_N_sum_T_N_sum_fun$ 0 )
(declare-sort T_N_sum_set_set_set$ 0 )
(declare-sort T_N_sum_set_bool_fun$ 0 )
(declare-sort N_T_N_sum_set_prod_set$ 0 )
(declare-sort N_T_N_sum_set_prod_set_set$ 0 )
(declare-sort N_T_N_sum_set_prod_bool_fun$ 0 )
(declare-sort N_T_N_sum_set_prod_set_set_set$ 0 )
(declare-sort N_T_N_sum_set_prod_set_bool_fun$ 0 )
(declare-datatypes ()((T_N_sum$ (inl$ (projl$ T$ ))(inr$ (projr$ N$ )))(N_T_N_sum_set_prod$ (pair$ (fst$ N$ )(snd$ T_N_sum_set$ )))))
(declare-fun k$ (N$ )T_set$ )
(declare-fun n$ ()N$ )
(declare-fun p$ ()N_T_N_sum_set_prod_set$ )
(declare-fun fr$ (N_set$ Dtree$ )T_set$ )
(declare-fun lr$ (N_set$ N$ )T_set_set$ )
(declare-fun ns$ ()N_set$ )
(declare-fun tr$ ()Dtree$ )
(declare-fun ts$ ()T_set$ )
(declare-fun uu$ ()T_T_N_sum_fun$ )
(declare-fun bot$ ()N_set$ )
(declare-fun sup$ (T_set$ )T_set_T_set_fun$ )
(declare-fun tns$ ()T_N_sum_set$ )
(declare-fun uua$ ()T_set_bool_fun$ )
(declare-fun uub$ (N_T_N_sum_set_prod_set$ )N_T_N_sum_set_prod_set_bool_fun$ )
(declare-fun uuc$ (T_N_sum_set$ )T_N_sum_set_bool_fun$ )
(declare-fun uud$ (N_set_set$ )N_set_set_bool_fun$ )
(declare-fun uue$ (T_set_set$ )T_set_set_bool_fun$ )
(declare-fun uuf$ (T$ )T_bool_fun$ )
(declare-fun uug$ (N_set$ )N_set_bool_fun$ )
(declare-fun uuh$ (T_N_sum$ )T_N_sum_bool_fun$ )
(declare-fun uui$ (N_T_N_sum_set_prod$ )N_T_N_sum_set_prod_bool_fun$ )
(declare-fun uuj$ (T_set$ )T_set_bool_fun$ )
(declare-fun uuk$ (N$ )N_bool_fun$ )
(declare-fun uul$ (N_T_N_sum_set_prod_set$ )N_T_N_sum_set_prod_set_bool_fun$ )
(declare-fun uum$ (T_N_sum_set$ )T_N_sum_set_bool_fun$ )
(declare-fun uun$ (N_set_set$ )N_set_set_bool_fun$ )
(declare-fun uuo$ (T_set_set$ )T_set_set_bool_fun$ )
(declare-fun uup$ (T$ )T_bool_fun$ )
(declare-fun uuq$ (N_set$ )N_set_bool_fun$ )
(declare-fun uur$ (T_N_sum$ )T_N_sum_bool_fun$ )
(declare-fun uus$ (N_T_N_sum_set_prod$ )N_T_N_sum_set_prod_bool_fun$ )
(declare-fun uut$ (T_set$ )T_set_bool_fun$ )
(declare-fun uuu$ (N$ )N_bool_fun$ )
(declare-fun bot$a ()T_set_set_set$ )
(declare-fun bot$b ()T_N_sum_set_set$ )
(declare-fun bot$c ()N_T_N_sum_set_prod_set_set$ )
(declare-fun bot$d ()N_set_set_set$ )
(declare-fun bot$e ()N_set_set$ )
(declare-fun bot$f ()T_set_set$ )
(declare-fun bot$g ()T_set$ )
(declare-fun bot$h ()T_N_sum_set$ )
(declare-fun bot$i ()N_T_N_sum_set_prod_set$ )
(declare-fun bot$j ()N_T_N_sum_set_prod_set_set_set$ )
(declare-fun bot$k ()T_N_sum_set_set_set$ )
(declare-fun bot$l ()N_set_set_set_set$ )
(declare-fun bot$m ()T_set_set_set_set$ )
(declare-fun sup$a (T_set_set$ )T_set$ )
(declare-fun sup$b (T_set_set_set_set$ )T_set_set_set$ )
(declare-fun sup$c (T_set_set_set$ T_set_set_set$ )T_set_set_set$ )
(declare-fun sup$d (T_N_sum_set_set_set$ )T_N_sum_set_set$ )
(declare-fun sup$e (T_N_sum_set_set$ T_N_sum_set_set$ )T_N_sum_set_set$ )
(declare-fun sup$f (N_T_N_sum_set_prod_set_set$ )N_T_N_sum_set_prod_set$ )
(declare-fun sup$g (N_T_N_sum_set_prod_set$ N_T_N_sum_set_prod_set$ )N_T_N_sum_set_prod_set$ )
(declare-fun sup$h (N_set_set_set$ )N_set_set$ )
(declare-fun sup$i (N_set_set$ N_set_set$ )N_set_set$ )
(declare-fun sup$j (T_N_sum_set_set$ )T_N_sum_set$ )
(declare-fun sup$k (T_N_sum_set$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun sup$l (T_set_set_set$ )T_set_set$ )
(declare-fun sup$m (T_set_set$ T_set_set$ )T_set_set$ )
(declare-fun sup$n (N_set_set$ )N_set$ )
(declare-fun sup$o (N_set$ N_set$ )N_set$ )
(declare-fun sup$p (N_T_N_sum_set_prod_set_set_set$ )N_T_N_sum_set_prod_set_set$ )
(declare-fun sup$q (N_set_set_set_set$ )N_set_set_set$ )
(declare-fun sup$r (T_set_set_set_set$ T_set_set_set_set$ )T_set_set_set_set$ )
(declare-fun sup$s (T_N_sum_set_set_set$ T_N_sum_set_set_set$ )T_N_sum_set_set_set$ )
(declare-fun sup$t (N_T_N_sum_set_prod_set_set$ N_T_N_sum_set_prod_set_set$ )N_T_N_sum_set_prod_set_set$ )
(declare-fun sup$u (N_set_set_set$ N_set_set_set$ )N_set_set_set$ )
(declare-fun minus$ (N_set$ N_set$ )N_set$ )
(declare-fun insert$ (N$ N_set$ )N_set$ )
(declare-fun member$ (T_N_sum$ T_N_sum_set$ )Bool )
(declare-fun minus$a (N_T_N_sum_set_prod_set_set$ N_T_N_sum_set_prod_set_set$ )N_T_N_sum_set_prod_set_set$ )
(declare-fun minus$b (T_N_sum_set_set$ T_N_sum_set_set$ )T_N_sum_set_set$ )
(declare-fun minus$c (N_set_set_set$ N_set_set_set$ )N_set_set_set$ )
(declare-fun minus$d (T_set_set_set$ T_set_set_set$ )T_set_set_set$ )
(declare-fun minus$e (T_set_set$ T_set_set$ )T_set_set$ )
(declare-fun minus$f (T_set$ )T_set_T_set_fun$ )
(declare-fun minus$g (N_set_set$ N_set_set$ )N_set_set$ )
(declare-fun minus$h (T_N_sum_set$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun minus$i (N_T_N_sum_set_prod_set$ N_T_N_sum_set_prod_set$ )N_T_N_sum_set_prod_set$ )
(declare-fun vimage$ (T_T_N_sum_fun$ T_N_sum_set$ )T_set$ )
(declare-fun collect$ (T_set_bool_fun$ )T_set_set$ )
(declare-fun fun_app$ (T_set_bool_fun$ T_set$ )Bool )
(declare-fun insert$a (T_set_set_set$ T_set_set_set_set$ )T_set_set_set_set$ )
(declare-fun insert$b (T_N_sum_set_set$ T_N_sum_set_set_set$ )T_N_sum_set_set_set$ )
(declare-fun insert$c (N_T_N_sum_set_prod_set$ N_T_N_sum_set_prod_set_set$ )N_T_N_sum_set_prod_set_set$ )
(declare-fun insert$d (N_set_set$ N_set_set_set$ )N_set_set_set$ )
(declare-fun insert$e (T_N_sum_set$ T_N_sum_set_set$ )T_N_sum_set_set$ )
(declare-fun insert$f (T_set_set$ T_set_set_set$ )T_set_set_set$ )
(declare-fun insert$g (N_set$ N_set_set$ )N_set_set$ )
(declare-fun insert$h (T_set$ T_set_set$ )T_set_set$ )
(declare-fun insert$i (T$ )T_set_T_set_fun$ )
(declare-fun insert$j (T_N_sum$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun insert$k (N_T_N_sum_set_prod$ N_T_N_sum_set_prod_set$ )N_T_N_sum_set_prod_set$ )
(declare-fun member$a (N_T_N_sum_set_prod$ N_T_N_sum_set_prod_set$ )Bool )
(declare-fun member$b (T_set$ T_set_set$ )Bool )
(declare-fun member$c (N$ N_set$ )Bool )
(declare-fun member$d (N_T_N_sum_set_prod_set$ N_T_N_sum_set_prod_set_set$ )Bool )
(declare-fun member$e (T_N_sum_set$ T_N_sum_set_set$ )Bool )
(declare-fun member$f (N_set_set$ N_set_set_set$ )Bool )
(declare-fun member$g (T_set_set$ T_set_set_set$ )Bool )
(declare-fun member$h (T$ T_set$ )Bool )
(declare-fun member$i (N_set$ N_set_set$ )Bool )
(declare-fun regular$ (Dtree$ )Bool )
(declare-fun vimage$a (T_T_fun$ )T_set_T_set_fun$ )
(declare-fun vimage$b (N_N_fun$ N_set$ )N_set$ )
(declare-fun vimage$c (T_set_T_fun$ T_set$ )T_set_set$ )
(declare-fun vimage$d (T_T_set_fun$ T_set_set$ )T_set$ )
(declare-fun vimage$e (T_N_sum_T_fun$ T_set$ )T_N_sum_set$ )
(declare-fun vimage$f (T_set_T_set_fun$ T_set_set$ )T_set_set$ )
(declare-fun vimage$g (T_set_T_N_sum_fun$ T_N_sum_set$ )T_set_set$ )
(declare-fun vimage$h (T_N_sum_T_set_fun$ T_set_set$ )T_N_sum_set$ )
(declare-fun vimage$i (T_N_sum_T_N_sum_fun$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun vimage$j (T_N_fun$ N_set$ )T_set$ )
(declare-fun vimage$k (N_T_fun$ T_set$ )N_set$ )
(declare-fun vimage$l (T_set_N_fun$ N_set$ )T_set_set$ )
(declare-fun vimage$m (N_set_N_fun$ N_set$ )N_set_set$ )
(declare-fun vimage$n (N_T_set_fun$ T_set_set$ )N_set$ )
(declare-fun collect$a (N_T_N_sum_set_prod_set_bool_fun$ )N_T_N_sum_set_prod_set_set$ )
(declare-fun collect$b (T_N_sum_set_bool_fun$ )T_N_sum_set_set$ )
(declare-fun collect$c (N_set_set_bool_fun$ )N_set_set_set$ )
(declare-fun collect$d (T_set_set_bool_fun$ )T_set_set_set$ )
(declare-fun collect$e (T_bool_fun$ )T_set$ )
(declare-fun collect$f (N_set_bool_fun$ )N_set_set$ )
(declare-fun collect$g (T_N_sum_bool_fun$ )T_N_sum_set$ )
(declare-fun collect$h (N_T_N_sum_set_prod_bool_fun$ )N_T_N_sum_set_prod_set$ )
(declare-fun collect$i (N_bool_fun$ )N_set$ )
(declare-fun fun_app$a (T_T_N_sum_fun$ T$ )T_N_sum$ )
(declare-fun fun_app$b (N_T_N_sum_set_prod_bool_fun$ N_T_N_sum_set_prod$ )Bool )
(declare-fun fun_app$c (T_N_sum_bool_fun$ T_N_sum$ )Bool )
(declare-fun fun_app$d (N_T_N_sum_set_prod_set_bool_fun$ N_T_N_sum_set_prod_set$ )Bool )
(declare-fun fun_app$e (T_N_sum_set_bool_fun$ T_N_sum_set$ )Bool )
(declare-fun fun_app$f (T_set_set_bool_fun$ T_set_set$ )Bool )
(declare-fun fun_app$g (N_set_set_bool_fun$ N_set_set$ )Bool )
(declare-fun fun_app$h (N_set_bool_fun$ N_set$ )Bool )
(declare-fun fun_app$i (T_bool_fun$ T$ )Bool )
(declare-fun fun_app$j (N_bool_fun$ N$ )Bool )
(declare-fun fun_app$k (T_set_T_set_fun$ T_set$ )T_set$ )
(assert (! (forall ((?v0 T_set$ ))(! (= (fun_app$ uua$ ?v0 )(exists ((?v1 N$ ))(and (= ?v0 (k$ ?v1 ))(member$ (inr$ ?v1 )tns$ )))):pattern ((fun_app$ uua$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 T$ ))(! (= (fun_app$a uu$ ?v0 )(inl$ ?v0 )):pattern ((fun_app$a uu$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$ )(?v1 N_T_N_sum_set_prod$ ))(! (= (fun_app$b (uui$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (uui$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum$ ))(! (= (fun_app$c (uuh$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$c (uuh$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$ )(?v1 N_T_N_sum_set_prod_set$ ))(! (= (fun_app$d (uub$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$d (uub$ ?v0 )?v1 )))):named a4 ))
(assert (! (forall ((?v0 T_N_sum_set$ )(?v1 T_N_sum_set$ ))(! (= (fun_app$e (uuc$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$e (uuc$ ?v0 )?v1 )))):named a5 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set$ ))(! (= (fun_app$f (uue$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$f (uue$ ?v0 )?v1 )))):named a6 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set$ ))(! (= (fun_app$g (uud$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$g (uud$ ?v0 )?v1 )))):named a7 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T_set$ ))(! (= (fun_app$ (uuj$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (uuj$ ?v0 )?v1 )))):named a8 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(! (= (fun_app$h (uug$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$h (uug$ ?v0 )?v1 )))):named a9 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(! (= (fun_app$i (uuf$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$i (uuf$ ?v0 )?v1 )))):named a10 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(! (= (fun_app$j (uuk$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$j (uuk$ ?v0 )?v1 )))):named a11 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$ )(?v1 N_T_N_sum_set_prod$ ))(! (= (fun_app$b (uus$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$b (uus$ ?v0 )?v1 )))):named a12 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum$ ))(! (= (fun_app$c (uur$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$c (uur$ ?v0 )?v1 )))):named a13 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$ )(?v1 N_T_N_sum_set_prod_set$ ))(! (= (fun_app$d (uul$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$d (uul$ ?v0 )?v1 )))):named a14 ))
(assert (! (forall ((?v0 T_N_sum_set$ )(?v1 T_N_sum_set$ ))(! (= (fun_app$e (uum$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$e (uum$ ?v0 )?v1 )))):named a15 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set$ ))(! (= (fun_app$f (uuo$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$f (uuo$ ?v0 )?v1 )))):named a16 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set$ ))(! (= (fun_app$g (uun$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$g (uun$ ?v0 )?v1 )))):named a17 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T_set$ ))(! (= (fun_app$ (uut$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$ (uut$ ?v0 )?v1 )))):named a18 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(! (= (fun_app$h (uuq$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$h (uuq$ ?v0 )?v1 )))):named a19 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(! (= (fun_app$i (uup$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$i (uup$ ?v0 )?v1 )))):named a20 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(! (= (fun_app$j (uuu$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$j (uuu$ ?v0 )?v1 )))):named a21 ))
(assert (! (not (and (= ts$ (fun_app$k (sup$ (vimage$ uu$ tns$ ))(sup$a (collect$ uua$ ))))(and (member$a (pair$ n$ tns$ )p$ )(forall ((?v0 N$ ))(=> (member$ (inr$ ?v0 )tns$ )(member$b (k$ ?v0 )(lr$ (minus$ ns$ (insert$ n$ bot$ ))?v0 ))))))):named a22 ))
(assert (! (member$c n$ ns$ ):named a23 ))
(assert (! (member$b ts$ (lr$ ns$ n$ )):named a24 ))
(assert (! (forall ((?v0 N$ ))(exists ((?v1 T_N_sum_set$ ))(member$a (pair$ ?v0 ?v1 )p$ ))):named a25 ))
(assert (! (= ts$ (fr$ ns$ tr$ )):named a26 ))
(assert (! (forall ((?v0 T_set_set_set$ )(?v1 T_set_set_set_set$ ))(= (sup$b (insert$a ?v0 ?v1 ))(sup$c ?v0 (sup$b ?v1 )))):named a27 ))
(assert (! (forall ((?v0 T_N_sum_set_set$ )(?v1 T_N_sum_set_set_set$ ))(= (sup$d (insert$b ?v0 ?v1 ))(sup$e ?v0 (sup$d ?v1 )))):named a28 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$ )(?v1 N_T_N_sum_set_prod_set_set$ ))(= (sup$f (insert$c ?v0 ?v1 ))(sup$g ?v0 (sup$f ?v1 )))):named a29 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set_set$ ))(= (sup$h (insert$d ?v0 ?v1 ))(sup$i ?v0 (sup$h ?v1 )))):named a30 ))
(assert (! (forall ((?v0 T_N_sum_set$ )(?v1 T_N_sum_set_set$ ))(= (sup$j (insert$e ?v0 ?v1 ))(sup$k ?v0 (sup$j ?v1 )))):named a31 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set_set$ ))(= (sup$l (insert$f ?v0 ?v1 ))(sup$m ?v0 (sup$l ?v1 )))):named a32 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set_set$ ))(= (sup$n (insert$g ?v0 ?v1 ))(sup$o ?v0 (sup$n ?v1 )))):named a33 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T_set_set$ ))(= (sup$a (insert$h ?v0 ?v1 ))(fun_app$k (sup$ ?v0 )(sup$a ?v1 )))):named a34 ))
(assert (! (forall ((?v0 T_set_set$ ))(= (sup$l (insert$f ?v0 bot$a ))?v0 )):named a35 ))
(assert (! (forall ((?v0 T_N_sum_set$ ))(= (sup$j (insert$e ?v0 bot$b ))?v0 )):named a36 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$ ))(= (sup$f (insert$c ?v0 bot$c ))?v0 )):named a37 ))
(assert (! (forall ((?v0 N_set_set$ ))(= (sup$h (insert$d ?v0 bot$d ))?v0 )):named a38 ))
(assert (! (forall ((?v0 N_set$ ))(= (sup$n (insert$g ?v0 bot$e ))?v0 )):named a39 ))
(assert (! (forall ((?v0 T_set$ ))(= (sup$a (insert$h ?v0 bot$f ))?v0 )):named a40 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$ )(?v1 N_T_N_sum_set_prod_set_set$ ))(= (insert$c ?v0 (minus$a ?v1 (insert$c ?v0 bot$c )))(insert$c ?v0 ?v1 ))):named a41 ))
(assert (! (forall ((?v0 T_N_sum_set$ )(?v1 T_N_sum_set_set$ ))(= (insert$e ?v0 (minus$b ?v1 (insert$e ?v0 bot$b )))(insert$e ?v0 ?v1 ))):named a42 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set_set$ ))(= (insert$d ?v0 (minus$c ?v1 (insert$d ?v0 bot$d )))(insert$d ?v0 ?v1 ))):named a43 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set_set$ ))(= (insert$f ?v0 (minus$d ?v1 (insert$f ?v0 bot$a )))(insert$f ?v0 ?v1 ))):named a44 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T_set_set$ ))(= (insert$h ?v0 (minus$e ?v1 (insert$h ?v0 bot$f )))(insert$h ?v0 ?v1 ))):named a45 ))
(assert (! (forall ((?v0 T$ )(?v1 T_set$ ))(= (fun_app$k (insert$i ?v0 )(fun_app$k (minus$f ?v1 )(fun_app$k (insert$i ?v0 )bot$g )))(fun_app$k (insert$i ?v0 )?v1 ))):named a46 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set_set$ ))(= (insert$g ?v0 (minus$g ?v1 (insert$g ?v0 bot$e )))(insert$g ?v0 ?v1 ))):named a47 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_set$ ))(= (insert$j ?v0 (minus$h ?v1 (insert$j ?v0 bot$h )))(insert$j ?v0 ?v1 ))):named a48 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$ )(?v1 N_T_N_sum_set_prod_set$ ))(= (insert$k ?v0 (minus$i ?v1 (insert$k ?v0 bot$i )))(insert$k ?v0 ?v1 ))):named a49 ))
(assert (! (forall ((?v0 N$ )(?v1 N_set$ ))(= (insert$ ?v0 (minus$ ?v1 (insert$ ?v0 bot$ )))(insert$ ?v0 ?v1 ))):named a50 ))
(assert (! (= (sup$p bot$j )bot$c ):named a51 ))
(assert (! (= (sup$d bot$k )bot$b ):named a52 ))
(assert (! (= (sup$q bot$l )bot$d ):named a53 ))
(assert (! (= (sup$b bot$m )bot$a ):named a54 ))
(assert (! (= (sup$l bot$a )bot$f ):named a55 ))
(assert (! (= (sup$h bot$d )bot$e ):named a56 ))
(assert (! (= (sup$j bot$b )bot$h ):named a57 ))
(assert (! (= (sup$f bot$c )bot$i ):named a58 ))
(assert (! (= (sup$n bot$e )bot$ ):named a59 ))
(assert (! (= (sup$a bot$f )bot$g ):named a60 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$ ))(= (collect$a (uub$ ?v0 ))(insert$c ?v0 bot$c ))):named a61 ))
(assert (! (forall ((?v0 T_N_sum_set$ ))(= (collect$b (uuc$ ?v0 ))(insert$e ?v0 bot$b ))):named a62 ))
(assert (! (forall ((?v0 N_set_set$ ))(= (collect$c (uud$ ?v0 ))(insert$d ?v0 bot$d ))):named a63 ))
(assert (! (forall ((?v0 T_set_set$ ))(= (collect$d (uue$ ?v0 ))(insert$f ?v0 bot$a ))):named a64 ))
(assert (! (forall ((?v0 T$ ))(= (collect$e (uuf$ ?v0 ))(fun_app$k (insert$i ?v0 )bot$g ))):named a65 ))
(assert (! (forall ((?v0 N_set$ ))(= (collect$f (uug$ ?v0 ))(insert$g ?v0 bot$e ))):named a66 ))
(assert (! (forall ((?v0 T_N_sum$ ))(= (collect$g (uuh$ ?v0 ))(insert$j ?v0 bot$h ))):named a67 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$ ))(= (collect$h (uui$ ?v0 ))(insert$k ?v0 bot$i ))):named a68 ))
(assert (! (forall ((?v0 T_set$ ))(= (collect$ (uuj$ ?v0 ))(insert$h ?v0 bot$f ))):named a69 ))
(assert (! (forall ((?v0 N$ ))(= (collect$i (uuk$ ?v0 ))(insert$ ?v0 bot$ ))):named a70 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$ ))(= (collect$a (uul$ ?v0 ))(insert$c ?v0 bot$c ))):named a71 ))
(assert (! (forall ((?v0 T_N_sum_set$ ))(= (collect$b (uum$ ?v0 ))(insert$e ?v0 bot$b ))):named a72 ))
(assert (! (forall ((?v0 N_set_set$ ))(= (collect$c (uun$ ?v0 ))(insert$d ?v0 bot$d ))):named a73 ))
(assert (! (forall ((?v0 T_set_set$ ))(= (collect$d (uuo$ ?v0 ))(insert$f ?v0 bot$a ))):named a74 ))
(assert (! (forall ((?v0 T$ ))(= (collect$e (uup$ ?v0 ))(fun_app$k (insert$i ?v0 )bot$g ))):named a75 ))
(assert (! (forall ((?v0 N_set$ ))(= (collect$f (uuq$ ?v0 ))(insert$g ?v0 bot$e ))):named a76 ))
(assert (! (forall ((?v0 T_N_sum$ ))(= (collect$g (uur$ ?v0 ))(insert$j ?v0 bot$h ))):named a77 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$ ))(= (collect$h (uus$ ?v0 ))(insert$k ?v0 bot$i ))):named a78 ))
(assert (! (forall ((?v0 T_set$ ))(= (collect$ (uut$ ?v0 ))(insert$h ?v0 bot$f ))):named a79 ))
(assert (! (forall ((?v0 N$ ))(= (collect$i (uuu$ ?v0 ))(insert$ ?v0 bot$ ))):named a80 ))
(assert (! (forall ((?v0 T$ )(?v1 N$ ))(= (= (inl$ ?v0 )(inr$ ?v1 ))false )):named a81 ))
(assert (! (forall ((?v0 N$ )(?v1 T$ ))(= (= (inr$ ?v0 )(inl$ ?v1 ))false )):named a82 ))
(assert (! (forall ((?v0 T_T_fun$ )(?v1 T_set$ )(?v2 T_set$ ))(= (fun_app$k (vimage$a ?v0 )(fun_app$k (sup$ ?v1 )?v2 ))(fun_app$k (sup$ (fun_app$k (vimage$a ?v0 )?v1 ))(fun_app$k (vimage$a ?v0 )?v2 )))):named a83 ))
(assert (! (forall ((?v0 T_T_N_sum_fun$ )(?v1 T_N_sum_set$ )(?v2 T_N_sum_set$ ))(= (vimage$ ?v0 (sup$k ?v1 ?v2 ))(fun_app$k (sup$ (vimage$ ?v0 ?v1 ))(vimage$ ?v0 ?v2 )))):named a84 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N_set$ )(?v2 N_set$ ))(= (vimage$b ?v0 (sup$o ?v1 ?v2 ))(sup$o (vimage$b ?v0 ?v1 )(vimage$b ?v0 ?v2 )))):named a85 ))
(assert (! (forall ((?v0 T_set_T_fun$ )(?v1 T_set$ )(?v2 T_set$ ))(= (vimage$c ?v0 (fun_app$k (sup$ ?v1 )?v2 ))(sup$m (vimage$c ?v0 ?v1 )(vimage$c ?v0 ?v2 )))):named a86 ))
(assert (! (forall ((?v0 T_T_set_fun$ )(?v1 T_set_set$ )(?v2 T_set_set$ ))(= (vimage$d ?v0 (sup$m ?v1 ?v2 ))(fun_app$k (sup$ (vimage$d ?v0 ?v1 ))(vimage$d ?v0 ?v2 )))):named a87 ))
(assert (! (forall ((?v0 T_N_sum_T_fun$ )(?v1 T_set$ )(?v2 T_set$ ))(= (vimage$e ?v0 (fun_app$k (sup$ ?v1 )?v2 ))(sup$k (vimage$e ?v0 ?v1 )(vimage$e ?v0 ?v2 )))):named a88 ))
(assert (! (forall ((?v0 T_set_T_set_fun$ )(?v1 T_set_set$ )(?v2 T_set_set$ ))(= (vimage$f ?v0 (sup$m ?v1 ?v2 ))(sup$m (vimage$f ?v0 ?v1 )(vimage$f ?v0 ?v2 )))):named a89 ))
(assert (! (forall ((?v0 T_set_T_N_sum_fun$ )(?v1 T_N_sum_set$ )(?v2 T_N_sum_set$ ))(= (vimage$g ?v0 (sup$k ?v1 ?v2 ))(sup$m (vimage$g ?v0 ?v1 )(vimage$g ?v0 ?v2 )))):named a90 ))
(assert (! (forall ((?v0 T_N_sum_T_set_fun$ )(?v1 T_set_set$ )(?v2 T_set_set$ ))(= (vimage$h ?v0 (sup$m ?v1 ?v2 ))(sup$k (vimage$h ?v0 ?v1 )(vimage$h ?v0 ?v2 )))):named a91 ))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$ )(?v1 T_N_sum_set$ )(?v2 T_N_sum_set$ ))(= (vimage$i ?v0 (sup$k ?v1 ?v2 ))(sup$k (vimage$i ?v0 ?v1 )(vimage$i ?v0 ?v2 )))):named a92 ))
(assert (! (forall ((?v0 T_set_set_set_set$ )(?v1 T_set_set_set_set$ ))(= (sup$b (sup$r ?v0 ?v1 ))(sup$c (sup$b ?v0 )(sup$b ?v1 )))):named a93 ))
(assert (! (forall ((?v0 T_N_sum_set_set_set$ )(?v1 T_N_sum_set_set_set$ ))(= (sup$d (sup$s ?v0 ?v1 ))(sup$e (sup$d ?v0 )(sup$d ?v1 )))):named a94 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set_set$ )(?v1 N_T_N_sum_set_prod_set_set$ ))(= (sup$f (sup$t ?v0 ?v1 ))(sup$g (sup$f ?v0 )(sup$f ?v1 )))):named a95 ))
(assert (! (forall ((?v0 N_set_set_set$ )(?v1 N_set_set_set$ ))(= (sup$h (sup$u ?v0 ?v1 ))(sup$i (sup$h ?v0 )(sup$h ?v1 )))):named a96 ))
(assert (! (forall ((?v0 T_N_sum_set_set$ )(?v1 T_N_sum_set_set$ ))(= (sup$j (sup$e ?v0 ?v1 ))(sup$k (sup$j ?v0 )(sup$j ?v1 )))):named a97 ))
(assert (! (forall ((?v0 T_set_set_set$ )(?v1 T_set_set_set$ ))(= (sup$l (sup$c ?v0 ?v1 ))(sup$m (sup$l ?v0 )(sup$l ?v1 )))):named a98 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set$ ))(= (sup$n (sup$i ?v0 ?v1 ))(sup$o (sup$n ?v0 )(sup$n ?v1 )))):named a99 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set$ ))(= (sup$a (sup$m ?v0 ?v1 ))(fun_app$k (sup$ (sup$a ?v0 ))(sup$a ?v1 )))):named a100 ))
(assert (! (forall ((?v0 N_N_fun$ ))(= (vimage$b ?v0 bot$ )bot$ )):named a101 ))
(assert (! (forall ((?v0 T_T_N_sum_fun$ ))(= (vimage$ ?v0 bot$h )bot$g )):named a102 ))
(assert (! (forall ((?v0 T_N_fun$ ))(= (vimage$j ?v0 bot$ )bot$g )):named a103 ))
(assert (! (forall ((?v0 N_T_fun$ ))(= (vimage$k ?v0 bot$g )bot$ )):named a104 ))
(assert (! (forall ((?v0 T_T_fun$ ))(= (fun_app$k (vimage$a ?v0 )bot$g )bot$g )):named a105 ))
(assert (! (forall ((?v0 T_set_N_fun$ ))(= (vimage$l ?v0 bot$ )bot$f )):named a106 ))
(assert (! (forall ((?v0 N_set_N_fun$ ))(= (vimage$m ?v0 bot$ )bot$e )):named a107 ))
(assert (! (forall ((?v0 N_T_set_fun$ ))(= (vimage$n ?v0 bot$f )bot$ )):named a108 ))
(assert (! (forall ((?v0 T_T_set_fun$ ))(= (vimage$d ?v0 bot$f )bot$g )):named a109 ))
(assert (! (forall ((?v0 T_set_T_fun$ ))(= (vimage$c ?v0 bot$g )bot$f )):named a110 ))
(assert (! (regular$ tr$ ):named a111 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$ ))(= (member$d ?v0 bot$c )false )):named a112 ))
(assert (! (forall ((?v0 T_N_sum_set$ ))(= (member$e ?v0 bot$b )false )):named a113 ))
(assert (! (forall ((?v0 N_set_set$ ))(= (member$f ?v0 bot$d )false )):named a114 ))
(assert (! (forall ((?v0 T_set_set$ ))(= (member$g ?v0 bot$a )false )):named a115 ))
(assert (! (forall ((?v0 T$ ))(= (member$h ?v0 bot$g )false )):named a116 ))
(assert (! (forall ((?v0 N_set$ ))(= (member$i ?v0 bot$e )false )):named a117 ))
(assert (! (forall ((?v0 T_N_sum$ ))(= (member$ ?v0 bot$h )false )):named a118 ))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$ ))(= (member$a ?v0 bot$i )false )):named a119 ))
(assert (! (forall ((?v0 T_set$ ))(= (member$b ?v0 bot$f )false )):named a120 ))
(assert (! (forall ((?v0 N$ ))(= (member$c ?v0 bot$ )false )):named a121 ))
(check-sat )
;(get-unsat-core )
