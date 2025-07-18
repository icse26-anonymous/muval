;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Nat$ 0 )
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
(declare-sort T_N_sum$ 0)
(declare-sort N_T_N_sum_set_prod$ 0)
(declare-fun projl$ (T_N_sum$)T$)
(declare-fun inl$ (T$ )T_N_sum$)
(declare-fun projr$ (T_N_sum$)N$)
(declare-fun inr$ (N$ )T_N_sum$)
(declare-fun fst$ (N_T_N_sum_set_prod$)N$)
(declare-fun snd$ (N_T_N_sum_set_prod$)T_N_sum_set$)
(declare-fun pair$ (N$ T_N_sum_set$ )N_T_N_sum_set_prod$)
(declare-fun k$ (N$ )T_set$ )
(declare-fun l$ (N_set$ N$ )T_set_set$ )
(declare-fun p$ ()N_T_N_sum_set_prod_set$ )
(declare-fun ll$ (N_set$ N$ )T_set_set$ )
(declare-fun na$ ()N$ )
(declare-fun uu$ ()T_T_N_sum_fun$ )
(declare-fun bot$ ()N_set$ )
(declare-fun nsa$ ()N_set$ )
(declare-fun sup$ (T_set$ )T_set_T_set_fun$ )
(declare-fun tns$ ()T_N_sum_set$ )
(declare-fun uua$ ()T_set_bool_fun$ )
(declare-fun uub$ (T_N_sum_set$ )T_N_sum_set_bool_fun$ )
(declare-fun uuc$ (N_set_set$ )N_set_set_bool_fun$ )
(declare-fun uud$ (T_set_set$ )T_set_set_bool_fun$ )
(declare-fun uue$ (T$ )T_bool_fun$ )
(declare-fun uuf$ (N_set$ )N_set_bool_fun$ )
(declare-fun uug$ (T_N_sum$ )T_N_sum_bool_fun$ )
(declare-fun uuh$ (T_set$ )T_set_bool_fun$ )
(declare-fun uui$ (N$ )N_bool_fun$ )
(declare-fun uuj$ (T_N_sum_set$ )T_N_sum_set_bool_fun$ )
(declare-fun uuk$ (N_set_set$ )N_set_set_bool_fun$ )
(declare-fun uul$ (T_set_set$ )T_set_set_bool_fun$ )
(declare-fun uum$ (T$ )T_bool_fun$ )
(declare-fun uun$ (N_set$ )N_set_bool_fun$ )
(declare-fun uuo$ (T_N_sum$ )T_N_sum_bool_fun$ )
(declare-fun uup$ (T_set$ )T_set_bool_fun$ )
(declare-fun uuq$ (N$ )N_bool_fun$ )
(declare-fun bot$a ()T_set_set_set$ )
(declare-fun bot$b ()T_N_sum_set_set$ )
(declare-fun bot$c ()N_set_set_set$ )
(declare-fun bot$d ()N_set_set$ )
(declare-fun bot$e ()T_set_set$ )
(declare-fun bot$f ()T_set$ )
(declare-fun bot$g ()T_N_sum_set$ )
(declare-fun bot$h ()T_N_sum_set_set_set$ )
(declare-fun bot$i ()N_set_set_set_set$ )
(declare-fun bot$j ()T_set_set_set_set$ )
(declare-fun card$ (N_set$ )Nat$ )
(declare-fun less$ (Nat$ Nat$ )Bool )
(declare-fun sup$a (T_set_set$ )T_set$ )
(declare-fun sup$b (T_set_set_set_set$ )T_set_set_set$ )
(declare-fun sup$c (T_set_set_set$ T_set_set_set$ )T_set_set_set$ )
(declare-fun sup$d (T_N_sum_set_set_set$ )T_N_sum_set_set$ )
(declare-fun sup$e (T_N_sum_set_set$ T_N_sum_set_set$ )T_N_sum_set_set$ )
(declare-fun sup$f (N_set_set_set$ )N_set_set$ )
(declare-fun sup$g (N_set_set$ N_set_set$ )N_set_set$ )
(declare-fun sup$h (T_N_sum_set_set$ )T_N_sum_set$ )
(declare-fun sup$i (T_N_sum_set$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun sup$j (T_set_set_set$ )T_set_set$ )
(declare-fun sup$k (T_set_set$ T_set_set$ )T_set_set$ )
(declare-fun sup$l (N_set_set$ )N_set$ )
(declare-fun sup$m (N_set$ N_set$ )N_set$ )
(declare-fun sup$n (N_set_set_set_set$ )N_set_set_set$ )
(declare-fun sup$o (T_set_set_set_set$ T_set_set_set_set$ )T_set_set_set_set$ )
(declare-fun sup$p (T_N_sum_set_set_set$ T_N_sum_set_set_set$ )T_N_sum_set_set_set$ )
(declare-fun sup$q (N_set_set_set$ N_set_set_set$ )N_set_set_set$ )
(declare-fun minus$ (N_set$ N_set$ )N_set$ )
(declare-fun insert$ (N$ N_set$ )N_set$ )
(declare-fun member$ (T_N_sum$ T_N_sum_set$ )Bool )
(declare-fun minus$a (T_N_sum_set_set$ T_N_sum_set_set$ )T_N_sum_set_set$ )
(declare-fun minus$b (N_set_set_set$ N_set_set_set$ )N_set_set_set$ )
(declare-fun minus$c (T_set_set_set$ T_set_set_set$ )T_set_set_set$ )
(declare-fun minus$d (T_set_set$ T_set_set$ )T_set_set$ )
(declare-fun minus$e (T_set$ )T_set_T_set_fun$ )
(declare-fun minus$f (N_set_set$ N_set_set$ )N_set_set$ )
(declare-fun minus$g (T_N_sum_set$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun vimage$ (T_T_N_sum_fun$ T_N_sum_set$ )T_set$ )
(declare-fun collect$ (T_set_bool_fun$ )T_set_set$ )
(declare-fun fun_app$ (T_set_bool_fun$ T_set$ )Bool )
(declare-fun insert$a (T_set_set_set$ T_set_set_set_set$ )T_set_set_set_set$ )
(declare-fun insert$b (T_N_sum_set_set$ T_N_sum_set_set_set$ )T_N_sum_set_set_set$ )
(declare-fun insert$c (N_set_set$ N_set_set_set$ )N_set_set_set$ )
(declare-fun insert$d (T_N_sum_set$ T_N_sum_set_set$ )T_N_sum_set_set$ )
(declare-fun insert$e (T_set_set$ T_set_set_set$ )T_set_set_set$ )
(declare-fun insert$f (N_set$ N_set_set$ )N_set_set$ )
(declare-fun insert$g (T_set$ T_set_set$ )T_set_set$ )
(declare-fun insert$h (T$ )T_set_T_set_fun$ )
(declare-fun insert$i (T_N_sum$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun less_eq$ (T_set_set$ T_set_set$ )Bool )
(declare-fun member$a (N_T_N_sum_set_prod$ N_T_N_sum_set_prod_set$ )Bool )
(declare-fun member$b (T_set$ T_set_set$ )Bool )
(declare-fun member$c (N$ N_set$ )Bool )
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
(declare-fun collect$a (T_N_sum_set_bool_fun$ )T_N_sum_set_set$ )
(declare-fun collect$b (N_set_set_bool_fun$ )N_set_set_set$ )
(declare-fun collect$c (T_set_set_bool_fun$ )T_set_set_set$ )
(declare-fun collect$d (T_bool_fun$ )T_set$ )
(declare-fun collect$e (N_set_bool_fun$ )N_set_set$ )
(declare-fun collect$f (T_N_sum_bool_fun$ )T_N_sum_set$ )
(declare-fun collect$g (N_bool_fun$ )N_set$ )
(declare-fun fun_app$a (T_T_N_sum_fun$ T$ )T_N_sum$ )
(declare-fun fun_app$b (T_N_sum_bool_fun$ T_N_sum$ )Bool )
(declare-fun fun_app$c (T_N_sum_set_bool_fun$ T_N_sum_set$ )Bool )
(declare-fun fun_app$d (T_set_set_bool_fun$ T_set_set$ )Bool )
(declare-fun fun_app$e (N_set_set_bool_fun$ N_set_set$ )Bool )
(declare-fun fun_app$f (N_set_bool_fun$ N_set$ )Bool )
(declare-fun fun_app$g (T_bool_fun$ T$ )Bool )
(declare-fun fun_app$h (N_bool_fun$ N$ )Bool )
(declare-fun fun_app$i (T_set_T_set_fun$ T_set$ )T_set$ )
(assert (! (forall ((?v0 T_set$ ))(! (= (fun_app$ uua$ ?v0 )(exists ((?v1 N$ ))(and (= ?v0 (k$ ?v1 ))(member$ (inr$ ?v1 )tns$ )))):pattern ((fun_app$ uua$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 T$ ))(! (= (fun_app$a uu$ ?v0 )(inl$ ?v0 )):pattern ((fun_app$a uu$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum$ ))(! (= (fun_app$b (uug$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (uug$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 T_N_sum_set$ )(?v1 T_N_sum_set$ ))(! (= (fun_app$c (uub$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$c (uub$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set$ ))(! (= (fun_app$d (uud$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$d (uud$ ?v0 )?v1 )))):named a4 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set$ ))(! (= (fun_app$e (uuc$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$e (uuc$ ?v0 )?v1 )))):named a5 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T_set$ ))(! (= (fun_app$ (uuh$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (uuh$ ?v0 )?v1 )))):named a6 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(! (= (fun_app$f (uuf$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$f (uuf$ ?v0 )?v1 )))):named a7 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(! (= (fun_app$g (uue$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$g (uue$ ?v0 )?v1 )))):named a8 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(! (= (fun_app$h (uui$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$h (uui$ ?v0 )?v1 )))):named a9 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum$ ))(! (= (fun_app$b (uuo$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$b (uuo$ ?v0 )?v1 )))):named a10 ))
(assert (! (forall ((?v0 T_N_sum_set$ )(?v1 T_N_sum_set$ ))(! (= (fun_app$c (uuj$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$c (uuj$ ?v0 )?v1 )))):named a11 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set$ ))(! (= (fun_app$d (uul$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$d (uul$ ?v0 )?v1 )))):named a12 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set$ ))(! (= (fun_app$e (uuk$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$e (uuk$ ?v0 )?v1 )))):named a13 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T_set$ ))(! (= (fun_app$ (uup$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$ (uup$ ?v0 )?v1 )))):named a14 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set$ ))(! (= (fun_app$f (uun$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$f (uun$ ?v0 )?v1 )))):named a15 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(! (= (fun_app$g (uum$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$g (uum$ ?v0 )?v1 )))):named a16 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(! (= (fun_app$h (uuq$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$h (uuq$ ?v0 )?v1 )))):named a17 ))
(assert (! (not (and (= (fun_app$i (sup$ (vimage$ uu$ tns$ ))(sup$a (collect$ uua$ )))(fun_app$i (sup$ (vimage$ uu$ tns$ ))(sup$a (collect$ uua$ ))))(and (member$a (pair$ na$ tns$ )p$ )(forall ((?v0 N$ ))(=> (member$ (inr$ ?v0 )tns$ )(member$b (k$ ?v0 )(l$ (minus$ nsa$ (insert$ na$ bot$ ))?v0 ))))))):named a18 ))
(assert (! (member$a (pair$ na$ tns$ )p$ ):named a19 ))
(assert (! (forall ((?v0 N$ ))(=> (member$ (inr$ ?v0 )tns$ )(member$b (k$ ?v0 )(ll$ (minus$ nsa$ (insert$ na$ bot$ ))?v0 )))):named a20 ))
(assert (! (member$c na$ nsa$ ):named a21 ))
(assert (! (forall ((?v0 N_set$ ))(=> (less$ (card$ ?v0 )(card$ nsa$ ))(forall ((?v1 N$ ))(less_eq$ (ll$ ?v0 ?v1 )(l$ ?v0 ?v1 ))))):named a22 ))
(assert (! (member$a (pair$ na$ tns$ )p$ ):named a23 ))
(assert (! (less$ (card$ (minus$ nsa$ (insert$ na$ bot$ )))(card$ nsa$ )):named a24 ))
(assert (! (forall ((?v0 N$ ))(=> (member$ (inr$ ?v0 )tns$ )(member$b (k$ ?v0 )(ll$ (minus$ nsa$ (insert$ na$ bot$ ))?v0 )))):named a25 ))
(assert (! (forall ((?v0 N$ ))(exists ((?v1 T_N_sum_set$ ))(member$a (pair$ ?v0 ?v1 )p$ ))):named a26 ))
(assert (! (forall ((?v0 T_set_set_set$ )(?v1 T_set_set_set_set$ ))(= (sup$b (insert$a ?v0 ?v1 ))(sup$c ?v0 (sup$b ?v1 )))):named a27 ))
(assert (! (forall ((?v0 T_N_sum_set_set$ )(?v1 T_N_sum_set_set_set$ ))(= (sup$d (insert$b ?v0 ?v1 ))(sup$e ?v0 (sup$d ?v1 )))):named a28 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set_set$ ))(= (sup$f (insert$c ?v0 ?v1 ))(sup$g ?v0 (sup$f ?v1 )))):named a29 ))
(assert (! (forall ((?v0 T_N_sum_set$ )(?v1 T_N_sum_set_set$ ))(= (sup$h (insert$d ?v0 ?v1 ))(sup$i ?v0 (sup$h ?v1 )))):named a30 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set_set$ ))(= (sup$j (insert$e ?v0 ?v1 ))(sup$k ?v0 (sup$j ?v1 )))):named a31 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set_set$ ))(= (sup$l (insert$f ?v0 ?v1 ))(sup$m ?v0 (sup$l ?v1 )))):named a32 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T_set_set$ ))(= (sup$a (insert$g ?v0 ?v1 ))(fun_app$i (sup$ ?v0 )(sup$a ?v1 )))):named a33 ))
(assert (! (forall ((?v0 T_set_set$ ))(= (sup$j (insert$e ?v0 bot$a ))?v0 )):named a34 ))
(assert (! (forall ((?v0 T_N_sum_set$ ))(= (sup$h (insert$d ?v0 bot$b ))?v0 )):named a35 ))
(assert (! (forall ((?v0 N_set_set$ ))(= (sup$f (insert$c ?v0 bot$c ))?v0 )):named a36 ))
(assert (! (forall ((?v0 N_set$ ))(= (sup$l (insert$f ?v0 bot$d ))?v0 )):named a37 ))
(assert (! (forall ((?v0 T_set$ ))(= (sup$a (insert$g ?v0 bot$e ))?v0 )):named a38 ))
(assert (! (forall ((?v0 T_N_sum_set$ )(?v1 T_N_sum_set_set$ ))(= (insert$d ?v0 (minus$a ?v1 (insert$d ?v0 bot$b )))(insert$d ?v0 ?v1 ))):named a39 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set_set$ ))(= (insert$c ?v0 (minus$b ?v1 (insert$c ?v0 bot$c )))(insert$c ?v0 ?v1 ))):named a40 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set_set$ ))(= (insert$e ?v0 (minus$c ?v1 (insert$e ?v0 bot$a )))(insert$e ?v0 ?v1 ))):named a41 ))
(assert (! (forall ((?v0 T_set$ )(?v1 T_set_set$ ))(= (insert$g ?v0 (minus$d ?v1 (insert$g ?v0 bot$e )))(insert$g ?v0 ?v1 ))):named a42 ))
(assert (! (forall ((?v0 T$ )(?v1 T_set$ ))(= (fun_app$i (insert$h ?v0 )(fun_app$i (minus$e ?v1 )(fun_app$i (insert$h ?v0 )bot$f )))(fun_app$i (insert$h ?v0 )?v1 ))):named a43 ))
(assert (! (forall ((?v0 N_set$ )(?v1 N_set_set$ ))(= (insert$f ?v0 (minus$f ?v1 (insert$f ?v0 bot$d )))(insert$f ?v0 ?v1 ))):named a44 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_set$ ))(= (insert$i ?v0 (minus$g ?v1 (insert$i ?v0 bot$g )))(insert$i ?v0 ?v1 ))):named a45 ))
(assert (! (forall ((?v0 N$ )(?v1 N_set$ ))(= (insert$ ?v0 (minus$ ?v1 (insert$ ?v0 bot$ )))(insert$ ?v0 ?v1 ))):named a46 ))
(assert (! (= (sup$d bot$h )bot$b ):named a47 ))
(assert (! (= (sup$n bot$i )bot$c ):named a48 ))
(assert (! (= (sup$b bot$j )bot$a ):named a49 ))
(assert (! (= (sup$j bot$a )bot$e ):named a50 ))
(assert (! (= (sup$f bot$c )bot$d ):named a51 ))
(assert (! (= (sup$h bot$b )bot$g ):named a52 ))
(assert (! (= (sup$l bot$d )bot$ ):named a53 ))
(assert (! (= (sup$a bot$e )bot$f ):named a54 ))
(assert (! (forall ((?v0 T_N_sum_set$ ))(= (collect$a (uub$ ?v0 ))(insert$d ?v0 bot$b ))):named a55 ))
(assert (! (forall ((?v0 N_set_set$ ))(= (collect$b (uuc$ ?v0 ))(insert$c ?v0 bot$c ))):named a56 ))
(assert (! (forall ((?v0 T_set_set$ ))(= (collect$c (uud$ ?v0 ))(insert$e ?v0 bot$a ))):named a57 ))
(assert (! (forall ((?v0 T$ ))(= (collect$d (uue$ ?v0 ))(fun_app$i (insert$h ?v0 )bot$f ))):named a58 ))
(assert (! (forall ((?v0 N_set$ ))(= (collect$e (uuf$ ?v0 ))(insert$f ?v0 bot$d ))):named a59 ))
(assert (! (forall ((?v0 T_N_sum$ ))(= (collect$f (uug$ ?v0 ))(insert$i ?v0 bot$g ))):named a60 ))
(assert (! (forall ((?v0 T_set$ ))(= (collect$ (uuh$ ?v0 ))(insert$g ?v0 bot$e ))):named a61 ))
(assert (! (forall ((?v0 N$ ))(= (collect$g (uui$ ?v0 ))(insert$ ?v0 bot$ ))):named a62 ))
(assert (! (forall ((?v0 T_N_sum_set$ ))(= (collect$a (uuj$ ?v0 ))(insert$d ?v0 bot$b ))):named a63 ))
(assert (! (forall ((?v0 N_set_set$ ))(= (collect$b (uuk$ ?v0 ))(insert$c ?v0 bot$c ))):named a64 ))
(assert (! (forall ((?v0 T_set_set$ ))(= (collect$c (uul$ ?v0 ))(insert$e ?v0 bot$a ))):named a65 ))
(assert (! (forall ((?v0 T$ ))(= (collect$d (uum$ ?v0 ))(fun_app$i (insert$h ?v0 )bot$f ))):named a66 ))
(assert (! (forall ((?v0 N_set$ ))(= (collect$e (uun$ ?v0 ))(insert$f ?v0 bot$d ))):named a67 ))
(assert (! (forall ((?v0 T_N_sum$ ))(= (collect$f (uuo$ ?v0 ))(insert$i ?v0 bot$g ))):named a68 ))
(assert (! (forall ((?v0 T_set$ ))(= (collect$ (uup$ ?v0 ))(insert$g ?v0 bot$e ))):named a69 ))
(assert (! (forall ((?v0 N$ ))(= (collect$g (uuq$ ?v0 ))(insert$ ?v0 bot$ ))):named a70 ))
(assert (! (forall ((?v0 T$ )(?v1 N$ ))(= (= (inl$ ?v0 )(inr$ ?v1 ))false )):named a71 ))
(assert (! (forall ((?v0 N$ )(?v1 T$ ))(= (= (inr$ ?v0 )(inl$ ?v1 ))false )):named a72 ))
(assert (! (forall ((?v0 T_T_fun$ )(?v1 T_set$ )(?v2 T_set$ ))(= (fun_app$i (vimage$a ?v0 )(fun_app$i (sup$ ?v1 )?v2 ))(fun_app$i (sup$ (fun_app$i (vimage$a ?v0 )?v1 ))(fun_app$i (vimage$a ?v0 )?v2 )))):named a73 ))
(assert (! (forall ((?v0 T_T_N_sum_fun$ )(?v1 T_N_sum_set$ )(?v2 T_N_sum_set$ ))(= (vimage$ ?v0 (sup$i ?v1 ?v2 ))(fun_app$i (sup$ (vimage$ ?v0 ?v1 ))(vimage$ ?v0 ?v2 )))):named a74 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N_set$ )(?v2 N_set$ ))(= (vimage$b ?v0 (sup$m ?v1 ?v2 ))(sup$m (vimage$b ?v0 ?v1 )(vimage$b ?v0 ?v2 )))):named a75 ))
(assert (! (forall ((?v0 T_set_T_fun$ )(?v1 T_set$ )(?v2 T_set$ ))(= (vimage$c ?v0 (fun_app$i (sup$ ?v1 )?v2 ))(sup$k (vimage$c ?v0 ?v1 )(vimage$c ?v0 ?v2 )))):named a76 ))
(assert (! (forall ((?v0 T_T_set_fun$ )(?v1 T_set_set$ )(?v2 T_set_set$ ))(= (vimage$d ?v0 (sup$k ?v1 ?v2 ))(fun_app$i (sup$ (vimage$d ?v0 ?v1 ))(vimage$d ?v0 ?v2 )))):named a77 ))
(assert (! (forall ((?v0 T_N_sum_T_fun$ )(?v1 T_set$ )(?v2 T_set$ ))(= (vimage$e ?v0 (fun_app$i (sup$ ?v1 )?v2 ))(sup$i (vimage$e ?v0 ?v1 )(vimage$e ?v0 ?v2 )))):named a78 ))
(assert (! (forall ((?v0 T_set_T_set_fun$ )(?v1 T_set_set$ )(?v2 T_set_set$ ))(= (vimage$f ?v0 (sup$k ?v1 ?v2 ))(sup$k (vimage$f ?v0 ?v1 )(vimage$f ?v0 ?v2 )))):named a79 ))
(assert (! (forall ((?v0 T_set_T_N_sum_fun$ )(?v1 T_N_sum_set$ )(?v2 T_N_sum_set$ ))(= (vimage$g ?v0 (sup$i ?v1 ?v2 ))(sup$k (vimage$g ?v0 ?v1 )(vimage$g ?v0 ?v2 )))):named a80 ))
(assert (! (forall ((?v0 T_N_sum_T_set_fun$ )(?v1 T_set_set$ )(?v2 T_set_set$ ))(= (vimage$h ?v0 (sup$k ?v1 ?v2 ))(sup$i (vimage$h ?v0 ?v1 )(vimage$h ?v0 ?v2 )))):named a81 ))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$ )(?v1 T_N_sum_set$ )(?v2 T_N_sum_set$ ))(= (vimage$i ?v0 (sup$i ?v1 ?v2 ))(sup$i (vimage$i ?v0 ?v1 )(vimage$i ?v0 ?v2 )))):named a82 ))
(assert (! (forall ((?v0 T_set_set_set_set$ )(?v1 T_set_set_set_set$ ))(= (sup$b (sup$o ?v0 ?v1 ))(sup$c (sup$b ?v0 )(sup$b ?v1 )))):named a83 ))
(assert (! (forall ((?v0 T_N_sum_set_set_set$ )(?v1 T_N_sum_set_set_set$ ))(= (sup$d (sup$p ?v0 ?v1 ))(sup$e (sup$d ?v0 )(sup$d ?v1 )))):named a84 ))
(assert (! (forall ((?v0 N_set_set_set$ )(?v1 N_set_set_set$ ))(= (sup$f (sup$q ?v0 ?v1 ))(sup$g (sup$f ?v0 )(sup$f ?v1 )))):named a85 ))
(assert (! (forall ((?v0 T_N_sum_set_set$ )(?v1 T_N_sum_set_set$ ))(= (sup$h (sup$e ?v0 ?v1 ))(sup$i (sup$h ?v0 )(sup$h ?v1 )))):named a86 ))
(assert (! (forall ((?v0 T_set_set_set$ )(?v1 T_set_set_set$ ))(= (sup$j (sup$c ?v0 ?v1 ))(sup$k (sup$j ?v0 )(sup$j ?v1 )))):named a87 ))
(assert (! (forall ((?v0 N_set_set$ )(?v1 N_set_set$ ))(= (sup$l (sup$g ?v0 ?v1 ))(sup$m (sup$l ?v0 )(sup$l ?v1 )))):named a88 ))
(assert (! (forall ((?v0 T_set_set$ )(?v1 T_set_set$ ))(= (sup$a (sup$k ?v0 ?v1 ))(fun_app$i (sup$ (sup$a ?v0 ))(sup$a ?v1 )))):named a89 ))
(assert (! (forall ((?v0 N_N_fun$ ))(= (vimage$b ?v0 bot$ )bot$ )):named a90 ))
(assert (! (forall ((?v0 T_T_N_sum_fun$ ))(= (vimage$ ?v0 bot$g )bot$f )):named a91 ))
(assert (! (forall ((?v0 T_N_fun$ ))(= (vimage$j ?v0 bot$ )bot$f )):named a92 ))
(assert (! (forall ((?v0 N_T_fun$ ))(= (vimage$k ?v0 bot$f )bot$ )):named a93 ))
(assert (! (forall ((?v0 T_T_fun$ ))(= (fun_app$i (vimage$a ?v0 )bot$f )bot$f )):named a94 ))
(assert (! (forall ((?v0 T_set_N_fun$ ))(= (vimage$l ?v0 bot$ )bot$e )):named a95 ))
(assert (! (forall ((?v0 N_set_N_fun$ ))(= (vimage$m ?v0 bot$ )bot$d )):named a96 ))
(assert (! (forall ((?v0 N_T_set_fun$ ))(= (vimage$n ?v0 bot$e )bot$ )):named a97 ))
(assert (! (forall ((?v0 T_T_set_fun$ ))(= (vimage$d ?v0 bot$e )bot$f )):named a98 ))
(assert (! (forall ((?v0 T_set_T_fun$ ))(= (vimage$c ?v0 bot$f )bot$e )):named a99 ))
(check-sat )
;(get-unsat-core )
