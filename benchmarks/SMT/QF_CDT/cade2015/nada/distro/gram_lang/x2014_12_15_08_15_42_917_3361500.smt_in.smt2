;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort T_set$ 0 )
(declare-sort N_N_fun$ 0 )
(declare-sort T_T_fun$ 0 )
(declare-sort Dtree_set$ 0 )
(declare-sort T_set_set$ 0 )
(declare-sort Dtree_N_fun$ 0 )
(declare-sort N_dtree_fun$ 0 )
(declare-sort T_N_sum_set$ 0 )
(declare-sort T_T_sum_set$ 0 )
(declare-sort N_T_N_sum_fun$ 0 )
(declare-sort T_N_sum_N_fun$ 0 )
(declare-sort T_T_T_sum_fun$ 0 )
(declare-sort Dtree_dtree_fun$ 0 )
(declare-sort N_set_N_set_fun$ 0 )
(declare-sort T_dtree_sum_set$ 0 )
(declare-sort T_set_N_sum_set$ 0 )
(declare-sort T_set_T_set_fun$ 0 )
(declare-sort T_set_T_sum_set$ 0 )
(declare-sort N_T_dtree_sum_fun$ 0 )
(declare-sort N_T_set_N_sum_fun$ 0 )
(declare-sort T_N_sum_dtree_fun$ 0 )
(declare-sort T_T_N_sum_sum_set$ 0 )
(declare-sort T_T_set_T_sum_fun$ 0 )
(declare-sort T_dtree_sum_N_fun$ 0 )
(declare-sort T_N_sum_T_N_sum_fun$ 0 )
(declare-sort T_T_sum_T_T_sum_fun$ 0 )
(declare-sort T_set_dtree_sum_set$ 0 )
(declare-sort Dtree_T_dtree_sum_fun$ 0 )
(declare-sort T_T_dtree_sum_sum_set$ 0 )
(declare-sort T_dtree_sum_dtree_fun$ 0 )
(declare-sort Dtree_set_dtree_set_fun$ 0 )
(declare-sort N_set_set_N_set_set_fun$ 0 )
(declare-sort T_N_sum_T_dtree_sum_fun$ 0 )
(declare-sort T_dtree_sum_T_N_sum_fun$ 0 )
(declare-sort T_set_set_T_set_set_fun$ 0 )
(declare-sort Dtree_T_set_dtree_sum_fun$ 0 )
(declare-sort T_N_sum_T_T_N_sum_sum_fun$ 0 )
(declare-sort T_T_N_sum_sum_T_N_sum_fun$ 0 )
(declare-sort T_dtree_sum_T_dtree_sum_fun$ 0 )
(declare-sort T_set_N_sum_T_set_N_sum_fun$ 0 )
(declare-sort T_set_T_sum_T_set_T_sum_fun$ 0 )
(declare-sort T_N_sum_T_T_dtree_sum_sum_fun$ 0 )
(declare-sort T_T_N_sum_sum_T_dtree_sum_fun$ 0 )
(declare-sort T_T_dtree_sum_sum_T_N_sum_fun$ 0 )
(declare-sort N_N_fun_T_N_sum_T_N_sum_fun_fun$ 0 )
(declare-sort T_set_N_sum_T_set_dtree_sum_fun$ 0 )
(declare-sort T_set_set_set_T_set_set_set_fun$ 0 )
(declare-sort T_T_dtree_sum_sum_T_dtree_sum_fun$ 0 )
(declare-sort T_dtree_sum_T_T_dtree_sum_sum_fun$ 0 )
(declare-sort T_T_N_sum_sum_T_T_dtree_sum_sum_fun$ 0 )
(declare-sort T_T_dtree_sum_sum_T_T_N_sum_sum_fun$ 0 )
(declare-sort Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$ 0 )
(declare-sort N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$ 0 )
(declare-sort Dtree_dtree_fun_T_dtree_sum_T_dtree_sum_fun_fun$ 0 )
(declare-sort T_N_sum$ 0)
(declare-sort T_dtree_sum$ 0)
(declare-sort T_T_N_sum_sum$ 0)
(declare-sort T_T_dtree_sum_sum$ 0)
(declare-sort T_T_sum$ 0)
(declare-sort T_set_T_sum$ 0)
(declare-sort T_set_dtree_sum$ 0)
(declare-sort T_set_N_sum$ 0)
(declare-sort T_set_T_N_sum_sum$ 0)
(declare-fun projl$ (T_N_sum$)T$)
(declare-fun inl$ (T$ )T_N_sum$)
(declare-fun projr$ (T_N_sum$)N$)
(declare-fun inr$ (N$ )T_N_sum$)
(declare-fun projl$a (T_dtree_sum$)T$)
(declare-fun inl$a (T$ )T_dtree_sum$)
(declare-fun projr$a (T_dtree_sum$)Dtree$)
(declare-fun inr$a (Dtree$ )T_dtree_sum$)
(declare-fun projl$b (T_T_N_sum_sum$)T$)
(declare-fun inl$b (T$ )T_T_N_sum_sum$)
(declare-fun projr$b (T_T_N_sum_sum$)T_N_sum$)
(declare-fun inr$b (T_N_sum$ )T_T_N_sum_sum$)
(declare-fun projl$c (T_T_dtree_sum_sum$)T$)
(declare-fun inl$c (T$ )T_T_dtree_sum_sum$)
(declare-fun projr$c (T_T_dtree_sum_sum$)T_dtree_sum$)
(declare-fun inr$c (T_dtree_sum$ )T_T_dtree_sum_sum$)
(declare-fun projl$d (T_T_sum$)T$)
(declare-fun inl$d (T$ )T_T_sum$)
(declare-fun projr$d (T_T_sum$)T$)
(declare-fun inr$d (T$ )T_T_sum$)
(declare-fun projl$e (T_set_T_sum$)T_set$)
(declare-fun inl$e (T_set$ )T_set_T_sum$)
(declare-fun projr$e (T_set_T_sum$)T$)
(declare-fun inr$e (T$ )T_set_T_sum$)
(declare-fun projl$f (T_set_dtree_sum$)T_set$)
(declare-fun inl$f (T_set$ )T_set_dtree_sum$)
(declare-fun projr$f (T_set_dtree_sum$)Dtree$)
(declare-fun inr$f (Dtree$ )T_set_dtree_sum$)
(declare-fun projl$g (T_set_N_sum$)T_set$)
(declare-fun inl$g (T_set$ )T_set_N_sum$)
(declare-fun projr$g (T_set_N_sum$)N$)
(declare-fun inr$g (N$ )T_set_N_sum$)
(declare-fun projl$h (T_set_T_N_sum_sum$)T_set$)
(declare-fun inl$h (T_set$ )T_set_T_N_sum_sum$)
(declare-fun projr$h (T_set_T_N_sum_sum$)T_N_sum$)
(declare-fun inr$h (T_N_sum$ )T_set_T_N_sum_sum$)
(declare-fun n$ ()N$ )
(declare-fun id$ ()T_T_fun$ )
(declare-fun ns$ ()N_set$ )
(declare-fun tr$ ()Dtree$ )
(declare-fun uu$ ()N_T_N_sum_fun$ )
(declare-fun ftr$ ()N_dtree_fun$ )
(declare-fun id$a ()T_set_T_set_fun$ )
(declare-fun id$b ()N_set_N_set_fun$ )
(declare-fun id$c ()N_set_set_N_set_set_fun$ )
(declare-fun id$d ()T_set_set_T_set_set_fun$ )
(declare-fun id$e ()T_set_set_set_T_set_set_set_fun$ )
(declare-fun id$f ()N_N_fun$ )
(declare-fun id$g ()Dtree_dtree_fun$ )
(declare-fun id$h ()Dtree_set_dtree_set_fun$ )
(declare-fun tns$ ()T_N_sum_set$ )
(declare-fun tr$a ()Dtree$ )
(declare-fun uua$ ()Dtree_T_dtree_sum_fun$ )
(declare-fun uub$ ()T_N_sum_T_T_N_sum_sum_fun$ )
(declare-fun uuc$ ()T_dtree_sum_T_T_dtree_sum_sum_fun$ )
(declare-fun uud$ ()T_T_T_sum_fun$ )
(declare-fun uue$ ()T_T_set_T_sum_fun$ )
(declare-fun uuf$ ()Dtree_T_set_dtree_sum_fun$ )
(declare-fun uug$ ()N_T_set_N_sum_fun$ )
(declare-fun cont$ (Dtree$ )T_dtree_sum_set$ )
(declare-fun node$ (N$ T_dtree_sum_set$ )Dtree$ )
(declare-fun root$ ()Dtree_N_fun$ )
(declare-fun image$ (T_dtree_sum_T_N_sum_fun$ T_dtree_sum_set$ )T_N_sum_set$ )
(declare-fun hsubst$ (Dtree$ )Dtree_dtree_fun$ )
(declare-fun image$a (T_N_sum_T_dtree_sum_fun$ T_N_sum_set$ )T_dtree_sum_set$ )
(declare-fun image$b (T_N_sum_T_N_sum_fun$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun image$c (N_N_fun$ )N_set_N_set_fun$ )
(declare-fun image$d (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum_set$ )T_dtree_sum_set$ )
(declare-fun image$e (Dtree_dtree_fun$ )Dtree_set_dtree_set_fun$ )
(declare-fun image$f (Dtree_N_fun$ Dtree_set$ )N_set$ )
(declare-fun image$g (N_dtree_fun$ N_set$ )Dtree_set$ )
(declare-fun image$h (T_T_dtree_sum_sum_T_T_N_sum_sum_fun$ T_T_dtree_sum_sum_set$ )T_T_N_sum_sum_set$ )
(declare-fun image$i (T_T_N_sum_sum_T_T_dtree_sum_sum_fun$ T_T_N_sum_sum_set$ )T_T_dtree_sum_sum_set$ )
(declare-fun image$j (T_T_sum_T_T_sum_fun$ T_T_sum_set$ )T_T_sum_set$ )
(declare-fun image$k (T_T_fun$ )T_set_T_set_fun$ )
(declare-fun image$l (T_set_T_sum_T_set_T_sum_fun$ T_set_T_sum_set$ )T_set_T_sum_set$ )
(declare-fun image$m (T_set_N_sum_T_set_dtree_sum_fun$ T_set_N_sum_set$ )T_set_dtree_sum_set$ )
(declare-fun image$n (T_set_N_sum_T_set_N_sum_fun$ T_set_N_sum_set$ )T_set_N_sum_set$ )
(declare-fun image$o (T_T_dtree_sum_sum_T_N_sum_fun$ T_T_dtree_sum_sum_set$ )T_N_sum_set$ )
(declare-fun image$p (T_T_N_sum_sum_T_N_sum_fun$ T_T_N_sum_sum_set$ )T_N_sum_set$ )
(declare-fun image$q (T_T_dtree_sum_sum_T_dtree_sum_fun$ T_T_dtree_sum_sum_set$ )T_dtree_sum_set$ )
(declare-fun image$r (T_T_N_sum_sum_T_dtree_sum_fun$ T_T_N_sum_sum_set$ )T_dtree_sum_set$ )
(declare-fun image$s (T_N_sum_T_T_dtree_sum_sum_fun$ T_N_sum_set$ )T_T_dtree_sum_sum_set$ )
(declare-fun image$t (T_dtree_sum_T_T_dtree_sum_sum_fun$ T_dtree_sum_set$ )T_T_dtree_sum_sum_set$ )
(declare-fun image$u (N_set_N_set_fun$ )N_set_set_N_set_set_fun$ )
(declare-fun image$v (T_set_set_T_set_set_fun$ )T_set_set_set_T_set_set_set_fun$ )
(declare-fun image$w (T_set_T_set_fun$ )T_set_set_T_set_set_fun$ )
(declare-fun image$x (N_T_dtree_sum_fun$ N_set$ )T_dtree_sum_set$ )
(declare-fun image$y (N_T_N_sum_fun$ N_set$ )T_N_sum_set$ )
(declare-fun image$z (T_dtree_sum_N_fun$ T_dtree_sum_set$ )N_set$ )
(declare-fun member$ (T_N_sum$ T_N_sum_set$ )Bool )
(declare-fun vimage$ (N_T_N_sum_fun$ T_N_sum_set$ )N_set$ )
(declare-fun fun_app$ (T_dtree_sum_T_T_dtree_sum_sum_fun$ T_dtree_sum$ )T_T_dtree_sum_sum$ )
(declare-fun image$aa (T_N_sum_N_fun$ T_N_sum_set$ )N_set$ )
(declare-fun map_sum$ (T_T_fun$ )Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$ )
(declare-fun member$a (T_dtree_sum$ T_dtree_sum_set$ )Bool )
(declare-fun member$b (T_T_dtree_sum_sum$ T_T_dtree_sum_sum_set$ )Bool )
(declare-fun member$c (T_T_N_sum_sum$ T_T_N_sum_sum_set$ )Bool )
(declare-fun member$d (N$ N_set$ )Bool )
(declare-fun member$e (T$ T_set$ )Bool )
(declare-fun vimage$a (Dtree_T_dtree_sum_fun$ T_dtree_sum_set$ )Dtree_set$ )
(declare-fun vimage$b (T_N_sum_T_T_N_sum_sum_fun$ T_T_N_sum_sum_set$ )T_N_sum_set$ )
(declare-fun vimage$c (T_dtree_sum_T_T_dtree_sum_sum_fun$ T_T_dtree_sum_sum_set$ )T_dtree_sum_set$ )
(declare-fun vimage$d (T_T_T_sum_fun$ T_T_sum_set$ )T_set$ )
(declare-fun vimage$e (T_T_set_T_sum_fun$ T_set_T_sum_set$ )T_set$ )
(declare-fun vimage$f (Dtree_T_set_dtree_sum_fun$ T_set_dtree_sum_set$ )Dtree_set$ )
(declare-fun vimage$g (N_T_set_N_sum_fun$ T_set_N_sum_set$ )N_set$ )
(declare-fun vimage$h (N_set_N_set_fun$ )N_set_set_N_set_set_fun$ )
(declare-fun vimage$i (T_set_set_T_set_set_fun$ )T_set_set_set_T_set_set_set_fun$ )
(declare-fun vimage$j (T_set_T_set_fun$ )T_set_set_T_set_set_fun$ )
(declare-fun vimage$k (N_N_fun$ )N_set_N_set_fun$ )
(declare-fun vimage$l (T_T_fun$ )T_set_T_set_fun$ )
(declare-fun vimage$m (N_T_dtree_sum_fun$ T_dtree_sum_set$ )N_set$ )
(declare-fun vimage$n (T_dtree_sum_N_fun$ N_set$ )T_dtree_sum_set$ )
(declare-fun vimage$o (T_N_sum_N_fun$ N_set$ )T_N_sum_set$ )
(declare-fun vimage$p (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum_set$ )T_dtree_sum_set$ )
(declare-fun vimage$q (T_dtree_sum_T_N_sum_fun$ T_N_sum_set$ )T_dtree_sum_set$ )
(declare-fun vimage$r (T_N_sum_T_dtree_sum_fun$ T_dtree_sum_set$ )T_N_sum_set$ )
(declare-fun vimage$s (T_N_sum_T_N_sum_fun$ T_N_sum_set$ )T_N_sum_set$ )
(declare-fun fun_app$a (T_N_sum_T_T_N_sum_sum_fun$ T_N_sum$ )T_T_N_sum_sum$ )
(declare-fun fun_app$b (Dtree_T_set_dtree_sum_fun$ Dtree$ )T_set_dtree_sum$ )
(declare-fun fun_app$c (Dtree_T_dtree_sum_fun$ Dtree$ )T_dtree_sum$ )
(declare-fun fun_app$d (T_T_set_T_sum_fun$ T$ )T_set_T_sum$ )
(declare-fun fun_app$e (T_T_T_sum_fun$ T$ )T_T_sum$ )
(declare-fun fun_app$f (N_T_set_N_sum_fun$ N$ )T_set_N_sum$ )
(declare-fun fun_app$g (N_T_N_sum_fun$ N$ )T_N_sum$ )
(declare-fun fun_app$h (Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$ Dtree_N_fun$ )T_dtree_sum_T_N_sum_fun$ )
(declare-fun fun_app$i (N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$ N_dtree_fun$ )T_N_sum_T_dtree_sum_fun$ )
(declare-fun fun_app$j (N_N_fun_T_N_sum_T_N_sum_fun_fun$ N_N_fun$ )T_N_sum_T_N_sum_fun$ )
(declare-fun fun_app$k (N_set_N_set_fun$ N_set$ )N_set$ )
(declare-fun fun_app$l (Dtree_dtree_fun_T_dtree_sum_T_dtree_sum_fun_fun$ Dtree_dtree_fun$ )T_dtree_sum_T_dtree_sum_fun$ )
(declare-fun fun_app$m (Dtree_set_dtree_set_fun$ Dtree_set$ )Dtree_set$ )
(declare-fun fun_app$n (T_set_T_set_fun$ T_set$ )T_set$ )
(declare-fun fun_app$o (N_N_fun$ N$ )N$ )
(declare-fun fun_app$p (Dtree_dtree_fun$ Dtree$ )Dtree$ )
(declare-fun fun_app$q (Dtree_N_fun$ Dtree$ )N$ )
(declare-fun fun_app$r (N_dtree_fun$ N$ )Dtree$ )
(declare-fun fun_app$s (T_dtree_sum_N_fun$ T_dtree_sum$ )N$ )
(declare-fun fun_app$t (T_N_sum_N_fun$ T_N_sum$ )N$ )
(declare-fun fun_app$u (T_dtree_sum_dtree_fun$ T_dtree_sum$ )Dtree$ )
(declare-fun fun_app$v (T_N_sum_dtree_fun$ T_N_sum$ )Dtree$ )
(declare-fun fun_app$w (N_T_dtree_sum_fun$ N$ )T_dtree_sum$ )
(declare-fun fun_app$x (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum$ )T_dtree_sum$ )
(declare-fun fun_app$y (T_dtree_sum_T_N_sum_fun$ T_dtree_sum$ )T_N_sum$ )
(declare-fun fun_app$z (T_N_sum_T_dtree_sum_fun$ T_N_sum$ )T_dtree_sum$ )
(declare-fun map_sum$a (T_T_fun$ )N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$ )
(declare-fun map_sum$b (T_T_fun$ )N_N_fun_T_N_sum_T_N_sum_fun_fun$ )
(declare-fun map_sum$c (T_T_fun$ )Dtree_dtree_fun_T_dtree_sum_T_dtree_sum_fun_fun$ )
(declare-fun map_sum$d (T_T_fun$ T_dtree_sum_T_N_sum_fun$ )T_T_dtree_sum_sum_T_T_N_sum_sum_fun$ )
(declare-fun map_sum$e (T_T_fun$ T_N_sum_T_dtree_sum_fun$ )T_T_N_sum_sum_T_T_dtree_sum_sum_fun$ )
(declare-fun map_sum$f (T_T_fun$ T_T_fun$ )T_T_sum_T_T_sum_fun$ )
(declare-fun map_sum$g (T_set_T_set_fun$ T_T_fun$ )T_set_T_sum_T_set_T_sum_fun$ )
(declare-fun map_sum$h (T_set_T_set_fun$ N_dtree_fun$ )T_set_N_sum_T_set_dtree_sum_fun$ )
(declare-fun map_sum$i (T_set_T_set_fun$ N_N_fun$ )T_set_N_sum_T_set_N_sum_fun$ )
(declare-fun map_sum$j (T_T_fun$ T_dtree_sum_N_fun$ )T_T_dtree_sum_sum_T_N_sum_fun$ )
(declare-fun map_sum$k (T_T_fun$ T_N_sum_N_fun$ )T_T_N_sum_sum_T_N_sum_fun$ )
(declare-fun map_sum$l (T_T_fun$ T_dtree_sum_dtree_fun$ )T_T_dtree_sum_sum_T_dtree_sum_fun$ )
(declare-fun map_sum$m (T_T_fun$ T_N_sum_dtree_fun$ )T_T_N_sum_sum_T_dtree_sum_fun$ )
(declare-fun map_sum$n (T_T_fun$ N_T_dtree_sum_fun$ )T_N_sum_T_T_dtree_sum_sum_fun$ )
(declare-fun map_sum$o (T_T_fun$ Dtree_T_dtree_sum_fun$ )T_dtree_sum_T_T_dtree_sum_sum_fun$ )
(declare-fun fun_app$aa (T_N_sum_T_N_sum_fun$ T_N_sum$ )T_N_sum$ )
(declare-fun fun_app$ab (T_T_fun$ T$ )T$ )
(declare-fun fun_app$ac (T_set_set_T_set_set_fun$ T_set_set$ )T_set_set$ )
(assert (! (forall ((?v0 T_dtree_sum$ ))(! (= (fun_app$ uuc$ ?v0 )(inr$c ?v0 )):pattern ((fun_app$ uuc$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 T_N_sum$ ))(! (= (fun_app$a uub$ ?v0 )(inr$b ?v0 )):pattern ((fun_app$a uub$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 Dtree$ ))(! (= (fun_app$b uuf$ ?v0 )(inr$f ?v0 )):pattern ((fun_app$b uuf$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 Dtree$ ))(! (= (fun_app$c uua$ ?v0 )(inr$a ?v0 )):pattern ((fun_app$c uua$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 T$ ))(! (= (fun_app$d uue$ ?v0 )(inr$e ?v0 )):pattern ((fun_app$d uue$ ?v0 )))):named a4 ))
(assert (! (forall ((?v0 T$ ))(! (= (fun_app$e uud$ ?v0 )(inr$d ?v0 )):pattern ((fun_app$e uud$ ?v0 )))):named a5 ))
(assert (! (forall ((?v0 N$ ))(! (= (fun_app$f uug$ ?v0 )(inr$g ?v0 )):pattern ((fun_app$f uug$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 N$ ))(! (= (fun_app$g uu$ ?v0 )(inr$ ?v0 )):pattern ((fun_app$g uu$ ?v0 )))):named a7 ))
(assert (! (not (= (vimage$ uu$ (image$ (fun_app$h (map_sum$ id$ )root$ )(image$a (fun_app$i (map_sum$a id$ )ftr$ )tns$ )))(vimage$ uu$ tns$ ))):named a8 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 T_N_sum_set$ ))(= (vimage$ uu$ (image$b (fun_app$j (map_sum$b id$ )?v0 )?v1 ))(fun_app$k (image$c ?v0 )(vimage$ uu$ ?v1 )))):named a9 ))
(assert (! (forall ((?v0 Dtree_dtree_fun$ )(?v1 T_dtree_sum_set$ ))(= (vimage$a uua$ (image$d (fun_app$l (map_sum$c id$ )?v0 )?v1 ))(fun_app$m (image$e ?v0 )(vimage$a uua$ ?v1 )))):named a10 ))
(assert (! (forall ((?v0 Dtree_N_fun$ )(?v1 T_dtree_sum_set$ ))(= (vimage$ uu$ (image$ (fun_app$h (map_sum$ id$ )?v0 )?v1 ))(image$f ?v0 (vimage$a uua$ ?v1 )))):named a11 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 T_N_sum_set$ ))(= (vimage$a uua$ (image$a (fun_app$i (map_sum$a id$ )?v0 )?v1 ))(image$g ?v0 (vimage$ uu$ ?v1 )))):named a12 ))
(assert (! (forall ((?v0 T_dtree_sum_T_N_sum_fun$ )(?v1 T_T_dtree_sum_sum_set$ ))(= (vimage$b uub$ (image$h (map_sum$d id$ ?v0 )?v1 ))(image$ ?v0 (vimage$c uuc$ ?v1 )))):named a13 ))
(assert (! (forall ((?v0 T_N_sum_T_dtree_sum_fun$ )(?v1 T_T_N_sum_sum_set$ ))(= (vimage$c uuc$ (image$i (map_sum$e id$ ?v0 )?v1 ))(image$a ?v0 (vimage$b uub$ ?v1 )))):named a14 ))
(assert (! (forall ((?v0 T_T_fun$ )(?v1 T_T_sum_set$ ))(= (vimage$d uud$ (image$j (map_sum$f id$ ?v0 )?v1 ))(fun_app$n (image$k ?v0 )(vimage$d uud$ ?v1 )))):named a15 ))
(assert (! (forall ((?v0 T_T_fun$ )(?v1 T_set_T_sum_set$ ))(= (vimage$e uue$ (image$l (map_sum$g id$a ?v0 )?v1 ))(fun_app$n (image$k ?v0 )(vimage$e uue$ ?v1 )))):named a16 ))
(assert (! (forall ((?v0 N_dtree_fun$ )(?v1 T_set_N_sum_set$ ))(= (vimage$f uuf$ (image$m (map_sum$h id$a ?v0 )?v1 ))(image$g ?v0 (vimage$g uug$ ?v1 )))):named a17 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 T_set_N_sum_set$ ))(= (vimage$g uug$ (image$n (map_sum$i id$a ?v0 )?v1 ))(fun_app$k (image$c ?v0 )(vimage$g uug$ ?v1 )))):named a18 ))
(assert (! (forall ((?v0 N$ )(?v1 N_N_fun$ )(?v2 T_N_sum_set$ ))(= (member$ (inr$ ?v0 )(image$b (fun_app$j (map_sum$b id$ )?v1 )?v2 ))(exists ((?v3 N$ ))(and (member$ (inr$ ?v3 )?v2 )(= (fun_app$o ?v1 ?v3 )?v0 ))))):named a19 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_dtree_fun$ )(?v2 T_dtree_sum_set$ ))(= (member$a (inr$a ?v0 )(image$d (fun_app$l (map_sum$c id$ )?v1 )?v2 ))(exists ((?v3 Dtree$ ))(and (member$a (inr$a ?v3 )?v2 )(= (fun_app$p ?v1 ?v3 )?v0 ))))):named a20 ))
(assert (! (forall ((?v0 N$ )(?v1 Dtree_N_fun$ )(?v2 T_dtree_sum_set$ ))(= (member$ (inr$ ?v0 )(image$ (fun_app$h (map_sum$ id$ )?v1 )?v2 ))(exists ((?v3 Dtree$ ))(and (member$a (inr$a ?v3 )?v2 )(= (fun_app$q ?v1 ?v3 )?v0 ))))):named a21 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_dtree_fun$ )(?v2 T_N_sum_set$ ))(= (member$a (inr$a ?v0 )(image$a (fun_app$i (map_sum$a id$ )?v1 )?v2 ))(exists ((?v3 N$ ))(and (member$ (inr$ ?v3 )?v2 )(= (fun_app$r ?v1 ?v3 )?v0 ))))):named a22 ))
(assert (! (forall ((?v0 N$ )(?v1 T_dtree_sum_N_fun$ )(?v2 T_T_dtree_sum_sum_set$ ))(= (member$ (inr$ ?v0 )(image$o (map_sum$j id$ ?v1 )?v2 ))(exists ((?v3 T_dtree_sum$ ))(and (member$b (inr$c ?v3 )?v2 )(= (fun_app$s ?v1 ?v3 )?v0 ))))):named a23 ))
(assert (! (forall ((?v0 N$ )(?v1 T_N_sum_N_fun$ )(?v2 T_T_N_sum_sum_set$ ))(= (member$ (inr$ ?v0 )(image$p (map_sum$k id$ ?v1 )?v2 ))(exists ((?v3 T_N_sum$ ))(and (member$c (inr$b ?v3 )?v2 )(= (fun_app$t ?v1 ?v3 )?v0 ))))):named a24 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 T_dtree_sum_dtree_fun$ )(?v2 T_T_dtree_sum_sum_set$ ))(= (member$a (inr$a ?v0 )(image$q (map_sum$l id$ ?v1 )?v2 ))(exists ((?v3 T_dtree_sum$ ))(and (member$b (inr$c ?v3 )?v2 )(= (fun_app$u ?v1 ?v3 )?v0 ))))):named a25 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 T_N_sum_dtree_fun$ )(?v2 T_T_N_sum_sum_set$ ))(= (member$a (inr$a ?v0 )(image$r (map_sum$m id$ ?v1 )?v2 ))(exists ((?v3 T_N_sum$ ))(and (member$c (inr$b ?v3 )?v2 )(= (fun_app$v ?v1 ?v3 )?v0 ))))):named a26 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 N_T_dtree_sum_fun$ )(?v2 T_N_sum_set$ ))(= (member$b (inr$c ?v0 )(image$s (map_sum$n id$ ?v1 )?v2 ))(exists ((?v3 N$ ))(and (member$ (inr$ ?v3 )?v2 )(= (fun_app$w ?v1 ?v3 )?v0 ))))):named a27 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 Dtree_T_dtree_sum_fun$ )(?v2 T_dtree_sum_set$ ))(= (member$b (inr$c ?v0 )(image$t (map_sum$o id$ ?v1 )?v2 ))(exists ((?v3 Dtree$ ))(and (member$a (inr$a ?v3 )?v2 )(= (fun_app$c ?v1 ?v3 )?v0 ))))):named a28 ))
(assert (! (= (vimage$h id$b )id$c ):named a29 ))
(assert (! (= (vimage$i id$d )id$e ):named a30 ))
(assert (! (= (vimage$j id$a )id$d ):named a31 ))
(assert (! (= (vimage$k id$f )id$b ):named a32 ))
(assert (! (= (vimage$l id$ )id$a ):named a33 ))
(assert (! (= (image$u id$b )id$c ):named a34 ))
(assert (! (= (image$v id$d )id$e ):named a35 ))
(assert (! (= (image$e id$g )id$h ):named a36 ))
(assert (! (= (image$w id$a )id$d ):named a37 ))
(assert (! (= (image$c id$f )id$b ):named a38 ))
(assert (! (= (image$k id$ )id$a ):named a39 ))
(assert (! (forall ((?v0 N$ )(?v1 N_N_fun$ )(?v2 T_N_sum_set$ ))(=> (member$ (inr$ ?v0 )(image$b (fun_app$j (map_sum$b id$ )?v1 )?v2 ))(exists ((?v3 N$ ))(and (member$ (inr$ ?v3 )?v2 )(= (fun_app$o ?v1 ?v3 )?v0 ))))):named a40 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree_dtree_fun$ )(?v2 T_dtree_sum_set$ ))(=> (member$a (inr$a ?v0 )(image$d (fun_app$l (map_sum$c id$ )?v1 )?v2 ))(exists ((?v3 Dtree$ ))(and (member$a (inr$a ?v3 )?v2 )(= (fun_app$p ?v1 ?v3 )?v0 ))))):named a41 ))
(assert (! (forall ((?v0 N$ )(?v1 Dtree_N_fun$ )(?v2 T_dtree_sum_set$ ))(=> (member$ (inr$ ?v0 )(image$ (fun_app$h (map_sum$ id$ )?v1 )?v2 ))(exists ((?v3 Dtree$ ))(and (member$a (inr$a ?v3 )?v2 )(= (fun_app$q ?v1 ?v3 )?v0 ))))):named a42 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_dtree_fun$ )(?v2 T_N_sum_set$ ))(=> (member$a (inr$a ?v0 )(image$a (fun_app$i (map_sum$a id$ )?v1 )?v2 ))(exists ((?v3 N$ ))(and (member$ (inr$ ?v3 )?v2 )(= (fun_app$r ?v1 ?v3 )?v0 ))))):named a43 ))
(assert (! (forall ((?v0 N$ )(?v1 T_dtree_sum_N_fun$ )(?v2 T_T_dtree_sum_sum_set$ ))(=> (member$ (inr$ ?v0 )(image$o (map_sum$j id$ ?v1 )?v2 ))(exists ((?v3 T_dtree_sum$ ))(and (member$b (inr$c ?v3 )?v2 )(= (fun_app$s ?v1 ?v3 )?v0 ))))):named a44 ))
(assert (! (forall ((?v0 N$ )(?v1 T_N_sum_N_fun$ )(?v2 T_T_N_sum_sum_set$ ))(=> (member$ (inr$ ?v0 )(image$p (map_sum$k id$ ?v1 )?v2 ))(exists ((?v3 T_N_sum$ ))(and (member$c (inr$b ?v3 )?v2 )(= (fun_app$t ?v1 ?v3 )?v0 ))))):named a45 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 T_dtree_sum_dtree_fun$ )(?v2 T_T_dtree_sum_sum_set$ ))(=> (member$a (inr$a ?v0 )(image$q (map_sum$l id$ ?v1 )?v2 ))(exists ((?v3 T_dtree_sum$ ))(and (member$b (inr$c ?v3 )?v2 )(= (fun_app$u ?v1 ?v3 )?v0 ))))):named a46 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 T_N_sum_dtree_fun$ )(?v2 T_T_N_sum_sum_set$ ))(=> (member$a (inr$a ?v0 )(image$r (map_sum$m id$ ?v1 )?v2 ))(exists ((?v3 T_N_sum$ ))(and (member$c (inr$b ?v3 )?v2 )(= (fun_app$v ?v1 ?v3 )?v0 ))))):named a47 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 N_T_dtree_sum_fun$ )(?v2 T_N_sum_set$ ))(=> (member$b (inr$c ?v0 )(image$s (map_sum$n id$ ?v1 )?v2 ))(exists ((?v3 N$ ))(and (member$ (inr$ ?v3 )?v2 )(= (fun_app$w ?v1 ?v3 )?v0 ))))):named a48 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 Dtree_T_dtree_sum_fun$ )(?v2 T_dtree_sum_set$ ))(=> (member$b (inr$c ?v0 )(image$t (map_sum$o id$ ?v1 )?v2 ))(exists ((?v3 Dtree$ ))(and (member$a (inr$a ?v3 )?v2 )(= (fun_app$c ?v1 ?v3 )?v0 ))))):named a49 ))
(assert (! (= tr$ (node$ n$ (image$a (fun_app$i (map_sum$a id$ )ftr$ )tns$ ))):named a50 ))
(assert (! (forall ((?v0 N$ )(?v1 N_N_fun$ )(?v2 N_set$ ))(= (member$d ?v0 (fun_app$k (vimage$k ?v1 )?v2 ))(member$d (fun_app$o ?v1 ?v0 )?v2 ))):named a51 ))
(assert (! (forall ((?v0 N$ )(?v1 N_T_dtree_sum_fun$ )(?v2 T_dtree_sum_set$ ))(= (member$d ?v0 (vimage$m ?v1 ?v2 ))(member$a (fun_app$w ?v1 ?v0 )?v2 ))):named a52 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_N_fun$ )(?v2 N_set$ ))(= (member$a ?v0 (vimage$n ?v1 ?v2 ))(member$d (fun_app$s ?v1 ?v0 )?v2 ))):named a53 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_N_fun$ )(?v2 N_set$ ))(= (member$ ?v0 (vimage$o ?v1 ?v2 ))(member$d (fun_app$t ?v1 ?v0 )?v2 ))):named a54 ))
(assert (! (forall ((?v0 N$ )(?v1 N_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(= (member$d ?v0 (vimage$ ?v1 ?v2 ))(member$ (fun_app$g ?v1 ?v0 )?v2 ))):named a55 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_T_dtree_sum_fun$ )(?v2 T_dtree_sum_set$ ))(= (member$a ?v0 (vimage$p ?v1 ?v2 ))(member$a (fun_app$x ?v1 ?v0 )?v2 ))):named a56 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(= (member$a ?v0 (vimage$q ?v1 ?v2 ))(member$ (fun_app$y ?v1 ?v0 )?v2 ))):named a57 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_T_dtree_sum_fun$ )(?v2 T_dtree_sum_set$ ))(= (member$ ?v0 (vimage$r ?v1 ?v2 ))(member$a (fun_app$z ?v1 ?v0 )?v2 ))):named a58 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_T_N_sum_fun$ )(?v2 T_N_sum_set$ ))(= (member$ ?v0 (vimage$s ?v1 ?v2 ))(member$ (fun_app$aa ?v1 ?v0 )?v2 ))):named a59 ))
(assert (! (forall ((?v0 T$ )(?v1 T_T_fun$ )(?v2 T_set$ ))(= (member$e ?v0 (fun_app$n (vimage$l ?v1 )?v2 ))(member$e (fun_app$ab ?v1 ?v0 )?v2 ))):named a60 ))
(assert (! (forall ((?v0 N_N_fun$ )(?v1 N$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= (fun_app$o ?v0 ?v1 )?v2 )(member$d ?v2 ?v3 ))(member$d ?v1 (fun_app$k (vimage$k ?v0 )?v3 )))):named a61 ))
(assert (! (forall ((?v0 T_dtree_sum_N_fun$ )(?v1 T_dtree_sum$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= (fun_app$s ?v0 ?v1 )?v2 )(member$d ?v2 ?v3 ))(member$a ?v1 (vimage$n ?v0 ?v3 )))):named a62 ))
(assert (! (forall ((?v0 T_N_sum_N_fun$ )(?v1 T_N_sum$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= (fun_app$t ?v0 ?v1 )?v2 )(member$d ?v2 ?v3 ))(member$ ?v1 (vimage$o ?v0 ?v3 )))):named a63 ))
(assert (! (forall ((?v0 N_T_dtree_sum_fun$ )(?v1 N$ )(?v2 T_dtree_sum$ )(?v3 T_dtree_sum_set$ ))(=> (and (= (fun_app$w ?v0 ?v1 )?v2 )(member$a ?v2 ?v3 ))(member$d ?v1 (vimage$m ?v0 ?v3 )))):named a64 ))
(assert (! (forall ((?v0 N_T_N_sum_fun$ )(?v1 N$ )(?v2 T_N_sum$ )(?v3 T_N_sum_set$ ))(=> (and (= (fun_app$g ?v0 ?v1 )?v2 )(member$ ?v2 ?v3 ))(member$d ?v1 (vimage$ ?v0 ?v3 )))):named a65 ))
(assert (! (forall ((?v0 T_dtree_sum_T_dtree_sum_fun$ )(?v1 T_dtree_sum$ )(?v2 T_dtree_sum$ )(?v3 T_dtree_sum_set$ ))(=> (and (= (fun_app$x ?v0 ?v1 )?v2 )(member$a ?v2 ?v3 ))(member$a ?v1 (vimage$p ?v0 ?v3 )))):named a66 ))
(assert (! (forall ((?v0 T_N_sum_T_dtree_sum_fun$ )(?v1 T_N_sum$ )(?v2 T_dtree_sum$ )(?v3 T_dtree_sum_set$ ))(=> (and (= (fun_app$z ?v0 ?v1 )?v2 )(member$a ?v2 ?v3 ))(member$ ?v1 (vimage$r ?v0 ?v3 )))):named a67 ))
(assert (! (forall ((?v0 T_dtree_sum_T_N_sum_fun$ )(?v1 T_dtree_sum$ )(?v2 T_N_sum$ )(?v3 T_N_sum_set$ ))(=> (and (= (fun_app$y ?v0 ?v1 )?v2 )(member$ ?v2 ?v3 ))(member$a ?v1 (vimage$q ?v0 ?v3 )))):named a68 ))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$ )(?v1 T_N_sum$ )(?v2 T_N_sum$ )(?v3 T_N_sum_set$ ))(=> (and (= (fun_app$aa ?v0 ?v1 )?v2 )(member$ ?v2 ?v3 ))(member$ ?v1 (vimage$s ?v0 ?v3 )))):named a69 ))
(assert (! (forall ((?v0 T_T_fun$ )(?v1 T$ )(?v2 T$ )(?v3 T_set$ ))(=> (and (= (fun_app$ab ?v0 ?v1 )?v2 )(member$e ?v2 ?v3 ))(member$e ?v1 (fun_app$n (vimage$l ?v0 )?v3 )))):named a70 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum$ ))(= (= (inr$h ?v0 )(inr$h ?v1 ))(= ?v0 ?v1 ))):named a71 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$f ?v0 )(inr$f ?v1 ))(= ?v0 ?v1 ))):named a72 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(= (= (inr$e ?v0 )(inr$e ?v1 ))(= ?v0 ?v1 ))):named a73 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(= (= (inr$d ?v0 )(inr$d ?v1 ))(= ?v0 ?v1 ))):named a74 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(= (= (inr$g ?v0 )(inr$g ?v1 ))(= ?v0 ?v1 ))):named a75 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum$ ))(= (= (inr$c ?v0 )(inr$c ?v1 ))(= ?v0 ?v1 ))):named a76 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum$ ))(= (= (inr$b ?v0 )(inr$b ?v1 ))(= ?v0 ?v1 ))):named a77 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a78 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$a ?v0 )(inr$a ?v1 ))(= ?v0 ?v1 ))):named a79 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum$ ))(= (= (inr$h ?v0 )(inr$h ?v1 ))(= ?v0 ?v1 ))):named a80 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$f ?v0 )(inr$f ?v1 ))(= ?v0 ?v1 ))):named a81 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(= (= (inr$e ?v0 )(inr$e ?v1 ))(= ?v0 ?v1 ))):named a82 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(= (= (inr$d ?v0 )(inr$d ?v1 ))(= ?v0 ?v1 ))):named a83 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(= (= (inr$g ?v0 )(inr$g ?v1 ))(= ?v0 ?v1 ))):named a84 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum$ ))(= (= (inr$c ?v0 )(inr$c ?v1 ))(= ?v0 ?v1 ))):named a85 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum$ ))(= (= (inr$b ?v0 )(inr$b ?v1 ))(= ?v0 ?v1 ))):named a86 ))
(assert (! (forall ((?v0 N$ )(?v1 N$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a87 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$a ?v0 )(inr$a ?v1 ))(= ?v0 ?v1 ))):named a88 ))
(assert (! (forall ((?v0 N$ ))(! (= (fun_app$o id$f ?v0 )?v0 ):pattern ((fun_app$o id$f ?v0 )))):named a89 ))
(assert (! (forall ((?v0 N_set$ ))(! (= (fun_app$k id$b ?v0 )?v0 ):pattern ((fun_app$k id$b ?v0 )))):named a90 ))
(assert (! (forall ((?v0 T_set_set$ ))(! (= (fun_app$ac id$d ?v0 )?v0 ):pattern ((fun_app$ac id$d ?v0 )))):named a91 ))
(assert (! (forall ((?v0 T_set$ ))(! (= (fun_app$n id$a ?v0 )?v0 ):pattern ((fun_app$n id$a ?v0 )))):named a92 ))
(assert (! (forall ((?v0 T$ ))(! (= (fun_app$ab id$ ?v0 )?v0 ):pattern ((fun_app$ab id$ ?v0 )))):named a93 ))
(assert (! (= (cont$ tr$ )(image$a (fun_app$i (map_sum$a id$ )ftr$ )tns$ )):named a94 ))
(assert (! (member$d n$ ns$ ):named a95 ))
(assert (! (forall ((?v0 N$ )(?v1 N_N_fun$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= ?v0 (fun_app$o ?v1 ?v2 ))(member$d ?v2 ?v3 ))(member$d ?v0 (fun_app$k (image$c ?v1 )?v3 )))):named a96 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 N_T_dtree_sum_fun$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= ?v0 (fun_app$w ?v1 ?v2 ))(member$d ?v2 ?v3 ))(member$a ?v0 (image$x ?v1 ?v3 )))):named a97 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 N_T_N_sum_fun$ )(?v2 N$ )(?v3 N_set$ ))(=> (and (= ?v0 (fun_app$g ?v1 ?v2 ))(member$d ?v2 ?v3 ))(member$ ?v0 (image$y ?v1 ?v3 )))):named a98 ))
(assert (! (forall ((?v0 N$ )(?v1 T_dtree_sum_N_fun$ )(?v2 T_dtree_sum$ )(?v3 T_dtree_sum_set$ ))(=> (and (= ?v0 (fun_app$s ?v1 ?v2 ))(member$a ?v2 ?v3 ))(member$d ?v0 (image$z ?v1 ?v3 )))):named a99 ))
(assert (! (forall ((?v0 N$ )(?v1 T_N_sum_N_fun$ )(?v2 T_N_sum$ )(?v3 T_N_sum_set$ ))(=> (and (= ?v0 (fun_app$t ?v1 ?v2 ))(member$ ?v2 ?v3 ))(member$d ?v0 (image$aa ?v1 ?v3 )))):named a100 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_dtree_sum_T_dtree_sum_fun$ )(?v2 T_dtree_sum$ )(?v3 T_dtree_sum_set$ ))(=> (and (= ?v0 (fun_app$x ?v1 ?v2 ))(member$a ?v2 ?v3 ))(member$a ?v0 (image$d ?v1 ?v3 )))):named a101 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_dtree_sum_T_N_sum_fun$ )(?v2 T_dtree_sum$ )(?v3 T_dtree_sum_set$ ))(=> (and (= ?v0 (fun_app$y ?v1 ?v2 ))(member$a ?v2 ?v3 ))(member$ ?v0 (image$ ?v1 ?v3 )))):named a102 ))
(assert (! (forall ((?v0 T_dtree_sum$ )(?v1 T_N_sum_T_dtree_sum_fun$ )(?v2 T_N_sum$ )(?v3 T_N_sum_set$ ))(=> (and (= ?v0 (fun_app$z ?v1 ?v2 ))(member$ ?v2 ?v3 ))(member$a ?v0 (image$a ?v1 ?v3 )))):named a103 ))
(assert (! (forall ((?v0 T_N_sum$ )(?v1 T_N_sum_T_N_sum_fun$ )(?v2 T_N_sum$ )(?v3 T_N_sum_set$ ))(=> (and (= ?v0 (fun_app$aa ?v1 ?v2 ))(member$ ?v2 ?v3 ))(member$ ?v0 (image$b ?v1 ?v3 )))):named a104 ))
(assert (! (forall ((?v0 T$ )(?v1 T_T_fun$ )(?v2 T$ )(?v3 T_set$ ))(=> (and (= ?v0 (fun_app$ab ?v1 ?v2 ))(member$e ?v2 ?v3 ))(member$e ?v0 (fun_app$n (image$k ?v1 )?v3 )))):named a105 ))
(assert (! (= (fun_app$q root$ tr$ )n$ ):named a106 ))
(assert (! (= tr$a (fun_app$p (hsubst$ tr$ )tr$ )):named a107 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (member$a (inr$a ?v0 )(cont$ ?v1 ))(member$ (inr$ (fun_app$q root$ ?v0 ))(image$ (fun_app$h (map_sum$ id$ )root$ )(cont$ ?v1 ))))):named a108 ))
(check-sat )
;(get-unsat-core )
