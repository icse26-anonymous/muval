;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_a_a_fun_fun$ 0 )
(declare-sort A_a_a_prod_fun$ 0 )
(declare-sort A_a_prod_a_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort A_a_fun_a_a_fun_fun$ 0 )
(declare-sort A_a_a_a_prod_fun_fun$ 0 )
(declare-sort A_a_a_prod_a_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_fun_fun$ 0 )
(declare-sort A_a_a_a_prod_prod_fun$ 0 )
(declare-sort A_a_a_prod_a_prod_fun$ 0 )
(declare-sort A_a_a_prod_prod_a_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_fun$ 0 )
(declare-sort A_a_prod_a_prod_a_fun$ 0 )
(declare-sort A_a_prod_stream_bool_fun$ 0 )
(declare-sort Nat_a_stream_bool_fun_fun$ 0 )
(declare-sort A_a_a_a_prod_prod_a_fun_fun$ 0 )
(declare-sort A_a_a_prod_a_a_prod_fun_fun$ 0 )
(declare-sort A_a_a_prod_a_prod_a_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_a_prod_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_a_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_a_fun$ 0 )
(declare-sort A_a_prod_a_prod_a_a_prod_fun$ 0 )
(declare-sort A_a_a_prod_prod_stream_bool_fun$ 0 )
(declare-sort A_a_prod_a_prod_stream_bool_fun$ 0 )
(declare-sort Nat_a_a_prod_stream_bool_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_a_a_prod_fun_fun$ 0 )
(declare-sort A_a_a_prod_prod_a_a_a_prod_prod_fun$ 0 )
(declare-sort A_a_prod_a_prod_a_a_prod_a_prod_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_stream_bool_fun$ 0 )
(declare-sort Nat_a_a_a_prod_prod_stream_bool_fun_fun$ 0 )
(declare-sort Nat_a_a_prod_a_prod_stream_bool_fun_fun$ 0 )
(declare-sort Nat_a_a_prod_a_a_prod_prod_stream_bool_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_fun_a_a_prod_a_a_prod_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun$ 0 )
(declare-sort A_a_a_prod_prod_a_a_a_prod_prod_fun_a_a_a_prod_prod_a_a_a_prod_prod_fun_fun$ 0 )
(declare-sort A_a_prod_a_prod_a_a_prod_a_prod_fun_a_a_prod_a_prod_a_a_prod_a_prod_fun_fun$ 0 )
(declare-sort A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun_a_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-datatypes ()((Nat_option$ (none$ )(some$ (the$ Nat$ )))(Enat$ (abs_enat$ (rep_enat$ Nat_option$ )))(A_a_prod$ (pair$ (fst$ A$ )(snd$ A$ )))))
(declare-sort A_a_prod_stream$ 0)
(declare-fun shd$a (A_a_prod_stream$)A_a_prod$)
(declare-fun stl$a (A_a_prod_stream$)A_a_prod_stream$)
(declare-fun sCons$a (A_a_prod$ A_a_prod_stream$ )A_a_prod_stream$)
(declare-datatypes ()((A_a_prod_a_prod$ (pair$a (fst$a A_a_prod$ )(snd$a A$ )))))
(declare-sort A_a_prod_a_prod_stream$ 0)
(declare-fun shd$b (A_a_prod_a_prod_stream$)A_a_prod_a_prod$)
(declare-fun stl$b (A_a_prod_a_prod_stream$)A_a_prod_a_prod_stream$)
(declare-fun sCons$b (A_a_prod_a_prod$ A_a_prod_a_prod_stream$ )A_a_prod_a_prod_stream$)
(declare-datatypes ()((A_a_a_prod_prod$ (pair$b (fst$b A$ )(snd$b A_a_prod$ )))))
(declare-sort A_a_a_prod_prod_stream$ 0)
(declare-fun shd$c (A_a_a_prod_prod_stream$)A_a_a_prod_prod$)
(declare-fun stl$c (A_a_a_prod_prod_stream$)A_a_a_prod_prod_stream$)
(declare-fun sCons$c (A_a_a_prod_prod$ A_a_a_prod_prod_stream$ )A_a_a_prod_prod_stream$)
(declare-datatypes ()((A_a_prod_a_a_prod_prod$ (pair$c (fst$c A_a_prod$ )(snd$c A_a_prod$ )))))
(declare-sort A_a_prod_a_a_prod_prod_stream$ 0)
(declare-fun shd$d (A_a_prod_a_a_prod_prod_stream$)A_a_prod_a_a_prod_prod$)
(declare-fun stl$d (A_a_prod_a_a_prod_prod_stream$)A_a_prod_a_a_prod_prod_stream$)
(declare-fun sCons$d (A_a_prod_a_a_prod_prod$ A_a_prod_a_a_prod_prod_stream$ )A_a_prod_a_a_prod_prod_stream$)
(declare-datatypes ()((A_a_a_prod_a_prod_prod$ (pair$d (fst$d A$ )(snd$d A_a_prod_a_prod$ )))))
(declare-sort A_a_a_prod_a_prod_prod_stream$ 0)
(declare-fun shd$e (A_a_a_prod_a_prod_prod_stream$)A_a_a_prod_a_prod_prod$)
(declare-fun stl$e (A_a_a_prod_a_prod_prod_stream$)A_a_a_prod_a_prod_prod_stream$)
(declare-fun sCons$e (A_a_a_prod_a_prod_prod$ A_a_a_prod_a_prod_prod_stream$ )A_a_a_prod_a_prod_prod_stream$)
(declare-datatypes ()((A_a_a_a_prod_prod_prod$ (pair$e (fst$e A$ )(snd$e A_a_a_prod_prod$ )))))
(declare-sort A_a_a_a_prod_prod_prod_stream$ 0)
(declare-fun shd$f (A_a_a_a_prod_prod_prod_stream$)A_a_a_a_prod_prod_prod$)
(declare-fun stl$f (A_a_a_a_prod_prod_prod_stream$)A_a_a_a_prod_prod_prod_stream$)
(declare-fun sCons$f (A_a_a_a_prod_prod_prod$ A_a_a_a_prod_prod_prod_stream$ )A_a_a_a_prod_prod_prod_stream$)
(declare-datatypes ()((A_a_prod_a_prod_a_prod$ (pair$f (fst$f A_a_prod_a_prod$ )(snd$f A$ )))))
(declare-sort A_a_prod_a_prod_a_prod_stream$ 0)
(declare-fun shd$g (A_a_prod_a_prod_a_prod_stream$)A_a_prod_a_prod_a_prod$)
(declare-fun stl$g (A_a_prod_a_prod_a_prod_stream$)A_a_prod_a_prod_a_prod_stream$)
(declare-fun sCons$g (A_a_prod_a_prod_a_prod$ A_a_prod_a_prod_a_prod_stream$ )A_a_prod_a_prod_a_prod_stream$)
(declare-datatypes ()((A_a_a_prod_prod_a_prod$ (pair$g (fst$g A_a_a_prod_prod$ )(snd$g A$ )))))
(declare-sort A_a_a_prod_prod_a_prod_stream$ 0)
(declare-fun shd$h (A_a_a_prod_prod_a_prod_stream$)A_a_a_prod_prod_a_prod$)
(declare-fun stl$h (A_a_a_prod_prod_a_prod_stream$)A_a_a_prod_prod_a_prod_stream$)
(declare-fun sCons$h (A_a_a_prod_prod_a_prod$ A_a_a_prod_prod_a_prod_stream$ )A_a_a_prod_prod_a_prod_stream$)
(declare-datatypes ()((A_a_a_prod_a_a_prod_prod_prod$ (pair$h (fst$h A$ )(snd$h A_a_prod_a_a_prod_prod$ )))))
(declare-sort A_a_a_prod_a_a_prod_prod_prod_stream$ 0)
(declare-fun shd$i (A_a_a_prod_a_a_prod_prod_prod_stream$)A_a_a_prod_a_a_prod_prod_prod$)
(declare-fun stl$i (A_a_a_prod_a_a_prod_prod_prod_stream$)A_a_a_prod_a_a_prod_prod_prod_stream$)
(declare-fun sCons$i (A_a_a_prod_a_a_prod_prod_prod$ A_a_a_prod_a_a_prod_prod_prod_stream$ )A_a_a_prod_a_a_prod_prod_prod_stream$)
(declare-datatypes ()((A_a_prod_a_a_prod_a_prod_prod$ (pair$i (fst$i A_a_prod$ )(snd$i A_a_prod_a_prod$ )))))
(declare-sort A_a_prod_a_a_prod_a_prod_prod_stream$ 0)
(declare-fun shd$j (A_a_prod_a_a_prod_a_prod_prod_stream$)A_a_prod_a_a_prod_a_prod_prod$)
(declare-fun stl$j (A_a_prod_a_a_prod_a_prod_prod_stream$)A_a_prod_a_a_prod_a_prod_prod_stream$)
(declare-fun sCons$j (A_a_prod_a_a_prod_a_prod_prod$ A_a_prod_a_a_prod_a_prod_prod_stream$ )A_a_prod_a_a_prod_a_prod_prod_stream$)
(declare-fun n$ ()Nat$ )
(declare-fun p$ ()A_stream_bool_fun$ )
(declare-fun ev$ (A_a_prod_a_a_prod_prod_stream_bool_fun$ )A_a_prod_a_a_prod_prod_stream_bool_fun$ )
(declare-fun alw$ (A_a_prod_a_a_prod_prod_stream_bool_fun$ )A_a_prod_a_a_prod_prod_stream_bool_fun$ )
(declare-fun ev$a (A_a_prod_a_prod_stream_bool_fun$ )A_a_prod_a_prod_stream_bool_fun$ )
(declare-fun ev$b (A_a_a_prod_prod_stream_bool_fun$ )A_a_a_prod_prod_stream_bool_fun$ )
(declare-fun ev$c (A_a_prod_stream_bool_fun$ )A_a_prod_stream_bool_fun$ )
(declare-fun ev$d (A_stream_bool_fun$ )A_stream_bool_fun$ )
(declare-fun alw$a (A_a_prod_a_prod_stream_bool_fun$ )A_a_prod_a_prod_stream_bool_fun$ )
(declare-fun alw$b (A_a_a_prod_prod_stream_bool_fun$ )A_a_a_prod_prod_stream_bool_fun$ )
(declare-fun alw$c (A_a_prod_stream_bool_fun$ )A_a_prod_stream_bool_fun$ )
(declare-fun alw$d (A_stream_bool_fun$ )A_stream_bool_fun$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun smap$ (A_a_fun$ A_stream$ )A_stream$ )
(declare-fun szip$ (A_stream$ A_stream$ )A_a_prod_stream$ )
(declare-fun wait$ (A_a_prod_a_a_prod_prod_stream_bool_fun$ A_a_prod_a_a_prod_prod_stream$ )Nat$ )
(declare-fun zero$ ()Nat$ )
(declare-fun ev_at$ (A_a_prod_a_a_prod_prod_stream_bool_fun$ )Nat_a_a_prod_a_a_prod_prod_stream_bool_fun_fun$ )
(declare-fun omega$ ()A_stream$ )
(declare-fun sdrop$ (Nat$ A_stream$ )A_stream$ )
(declare-fun smap$a (A_a_prod_a_fun$ A_a_prod_stream$ )A_stream$ )
(declare-fun smap$b (A_a_a_prod_fun$ A_stream$ )A_a_prod_stream$ )
(declare-fun smap$c (A_a_prod_a_a_prod_fun$ A_a_prod_stream$ )A_a_prod_stream$ )
(declare-fun smap$d (A_a_prod_a_prod_a_fun$ A_a_prod_a_prod_stream$ )A_stream$ )
(declare-fun smap$e (A_a_a_prod_prod_a_fun$ A_a_a_prod_prod_stream$ )A_stream$ )
(declare-fun smap$f (A_a_a_prod_a_prod_fun$ A_stream$ )A_a_prod_a_prod_stream$ )
(declare-fun smap$g (A_a_a_a_prod_prod_fun$ A_stream$ )A_a_a_prod_prod_stream$ )
(declare-fun smap$h (A_a_prod_a_a_prod_prod_a_fun$ A_a_prod_a_a_prod_prod_stream$ )A_stream$ )
(declare-fun smap$i (A_a_prod_a_prod_a_a_prod_fun$ A_a_prod_a_prod_stream$ )A_a_prod_stream$ )
(declare-fun smap2$ (A_a_a_fun_fun$ A_stream$ A_stream$ )A_stream$ )
(declare-fun szip$a (A_stream$ A_a_prod_stream$ )A_a_a_prod_prod_stream$ )
(declare-fun szip$b (A_a_prod_stream$ A_stream$ )A_a_prod_a_prod_stream$ )
(declare-fun szip$c (A_a_prod_stream$ A_a_prod_stream$ )A_a_prod_a_a_prod_prod_stream$ )
(declare-fun szip$d (A_stream$ A_a_prod_a_prod_stream$ )A_a_a_prod_a_prod_prod_stream$ )
(declare-fun szip$e (A_stream$ A_a_a_prod_prod_stream$ )A_a_a_a_prod_prod_prod_stream$ )
(declare-fun szip$f (A_a_prod_a_prod_stream$ A_stream$ )A_a_prod_a_prod_a_prod_stream$ )
(declare-fun szip$g (A_a_a_prod_prod_stream$ A_stream$ )A_a_a_prod_prod_a_prod_stream$ )
(declare-fun szip$h (A_stream$ A_a_prod_a_a_prod_prod_stream$ )A_a_a_prod_a_a_prod_prod_prod_stream$ )
(declare-fun szip$i (A_a_prod_stream$ A_a_prod_a_prod_stream$ )A_a_prod_a_a_prod_a_prod_prod_stream$ )
(declare-fun wait$a (A_a_prod_a_prod_stream_bool_fun$ A_a_prod_a_prod_stream$ )Nat$ )
(declare-fun wait$b (A_a_a_prod_prod_stream_bool_fun$ A_a_a_prod_prod_stream$ )Nat$ )
(declare-fun wait$c (A_a_prod_stream_bool_fun$ A_a_prod_stream$ )Nat$ )
(declare-fun wait$d (A_stream_bool_fun$ A_stream$ )Nat$ )
(declare-fun compow$ (Nat$ )A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun_a_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun_fun$ )
(declare-fun ev_at$a (A_a_prod_a_prod_stream_bool_fun$ )Nat_a_a_prod_a_prod_stream_bool_fun_fun$ )
(declare-fun ev_at$b (A_a_a_prod_prod_stream_bool_fun$ )Nat_a_a_a_prod_prod_stream_bool_fun_fun$ )
(declare-fun ev_at$c (A_a_prod_stream_bool_fun$ )Nat_a_a_prod_stream_bool_fun_fun$ )
(declare-fun ev_at$d (A_stream_bool_fun$ )Nat_a_stream_bool_fun_fun$ )
(declare-fun sdrop$a (Nat$ A_a_prod_stream$ )A_a_prod_stream$ )
(declare-fun sdrop$b (Nat$ A_a_prod_a_prod_stream$ )A_a_prod_a_prod_stream$ )
(declare-fun sdrop$c (Nat$ A_a_a_prod_prod_stream$ )A_a_a_prod_prod_stream$ )
(declare-fun sdrop$d (Nat$ A_a_prod_a_a_prod_prod_stream$ )A_a_prod_a_a_prod_prod_stream$ )
(declare-fun sdrop$e (Nat$ A_a_a_prod_a_prod_prod_stream$ )A_a_a_prod_a_prod_prod_stream$ )
(declare-fun sdrop$f (Nat$ A_a_a_a_prod_prod_prod_stream$ )A_a_a_a_prod_prod_prod_stream$ )
(declare-fun sdrop$g (Nat$ A_a_prod_a_prod_a_prod_stream$ )A_a_prod_a_prod_a_prod_stream$ )
(declare-fun sdrop$h (Nat$ A_a_a_prod_prod_a_prod_stream$ )A_a_a_prod_prod_a_prod_stream$ )
(declare-fun sdrop$i (Nat$ A_a_a_prod_a_a_prod_prod_prod_stream$ )A_a_a_prod_a_a_prod_prod_prod_stream$ )
(declare-fun sdrop$j (Nat$ A_a_prod_a_a_prod_a_prod_prod_stream$ )A_a_prod_a_a_prod_a_prod_prod_stream$ )
(declare-fun sfirst$ (A_stream_bool_fun$ A_stream$ )Enat$ )
(declare-fun smap2$a (A_a_a_prod_a_fun_fun$ A_stream$ A_a_prod_stream$ )A_stream$ )
(declare-fun smap2$b (A_a_prod_a_a_fun_fun$ A_a_prod_stream$ A_stream$ )A_stream$ )
(declare-fun smap2$c (A_a_a_a_prod_fun_fun$ A_stream$ A_stream$ )A_a_prod_stream$ )
(declare-fun smap2$d (A_a_prod_a_a_prod_a_fun_fun$ A_a_prod_stream$ A_a_prod_stream$ )A_stream$ )
(declare-fun smap2$e (A_a_a_prod_a_a_prod_fun_fun$ A_stream$ A_a_prod_stream$ )A_a_prod_stream$ )
(declare-fun smap2$f (A_a_prod_a_a_a_prod_fun_fun$ A_a_prod_stream$ A_stream$ )A_a_prod_stream$ )
(declare-fun smap2$g (A_a_prod_a_a_prod_a_a_prod_fun_fun$ A_a_prod_stream$ A_a_prod_stream$ )A_a_prod_stream$ )
(declare-fun smap2$h (A_a_a_prod_a_prod_a_fun_fun$ A_stream$ A_a_prod_a_prod_stream$ )A_stream$ )
(declare-fun smap2$i (A_a_a_a_prod_prod_a_fun_fun$ A_stream$ A_a_a_prod_prod_stream$ )A_stream$ )
(declare-fun compow$a (Nat$ )A_a_prod_a_prod_a_a_prod_a_prod_fun_a_a_prod_a_prod_a_a_prod_a_prod_fun_fun$ )
(declare-fun compow$b (Nat$ )A_a_a_prod_prod_a_a_a_prod_prod_fun_a_a_a_prod_prod_a_a_a_prod_prod_fun_fun$ )
(declare-fun compow$c (Nat$ )A_a_prod_a_a_prod_fun_a_a_prod_a_a_prod_fun_fun$ )
(declare-fun compow$d (Nat$ )A_a_fun_a_a_fun_fun$ )
(declare-fun fun_app$ (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$a (A_a_prod_a_a_prod_prod_stream_bool_fun$ A_a_prod_a_a_prod_prod_stream$ )Bool )
(declare-fun fun_app$b (Nat_a_a_prod_a_a_prod_prod_stream_bool_fun_fun$ Nat$ )A_a_prod_a_a_prod_prod_stream_bool_fun$ )
(declare-fun fun_app$c (A_a_prod_a_prod_stream_bool_fun$ A_a_prod_a_prod_stream$ )Bool )
(declare-fun fun_app$d (Nat_a_a_prod_a_prod_stream_bool_fun_fun$ Nat$ )A_a_prod_a_prod_stream_bool_fun$ )
(declare-fun fun_app$e (A_a_a_prod_prod_stream_bool_fun$ A_a_a_prod_prod_stream$ )Bool )
(declare-fun fun_app$f (Nat_a_a_a_prod_prod_stream_bool_fun_fun$ Nat$ )A_a_a_prod_prod_stream_bool_fun$ )
(declare-fun fun_app$g (A_a_prod_stream_bool_fun$ A_a_prod_stream$ )Bool )
(declare-fun fun_app$h (Nat_a_a_prod_stream_bool_fun_fun$ Nat$ )A_a_prod_stream_bool_fun$ )
(declare-fun fun_app$i (Nat_a_stream_bool_fun_fun$ Nat$ )A_stream_bool_fun$ )
(declare-fun fun_app$j (A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun$ A_a_prod_a_a_prod_prod$ )A_a_prod_a_a_prod_prod$ )
(declare-fun fun_app$k (A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun_a_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun_fun$ A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun$ )A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun$ )
(declare-fun fun_app$l (A_a_prod_a_prod_a_a_prod_a_prod_fun$ A_a_prod_a_prod$ )A_a_prod_a_prod$ )
(declare-fun fun_app$m (A_a_prod_a_prod_a_a_prod_a_prod_fun_a_a_prod_a_prod_a_a_prod_a_prod_fun_fun$ A_a_prod_a_prod_a_a_prod_a_prod_fun$ )A_a_prod_a_prod_a_a_prod_a_prod_fun$ )
(declare-fun fun_app$n (A_a_a_prod_prod_a_a_a_prod_prod_fun$ A_a_a_prod_prod$ )A_a_a_prod_prod$ )
(declare-fun fun_app$o (A_a_a_prod_prod_a_a_a_prod_prod_fun_a_a_a_prod_prod_a_a_a_prod_prod_fun_fun$ A_a_a_prod_prod_a_a_a_prod_prod_fun$ )A_a_a_prod_prod_a_a_a_prod_prod_fun$ )
(declare-fun fun_app$p (A_a_prod_a_a_prod_fun$ A_a_prod$ )A_a_prod$ )
(declare-fun fun_app$q (A_a_prod_a_a_prod_fun_a_a_prod_a_a_prod_fun_fun$ A_a_prod_a_a_prod_fun$ )A_a_prod_a_a_prod_fun$ )
(declare-fun fun_app$r (A_a_fun$ A$ )A$ )
(declare-fun fun_app$s (A_a_fun_a_a_fun_fun$ A_a_fun$ )A_a_fun$ )
(declare-fun siterate$ (A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun$ A_a_prod_a_a_prod_prod$ )A_a_prod_a_a_prod_prod_stream$ )
(declare-fun siterate$a (A_a_prod_a_prod_a_a_prod_a_prod_fun$ A_a_prod_a_prod$ )A_a_prod_a_prod_stream$ )
(declare-fun siterate$b (A_a_a_prod_prod_a_a_a_prod_prod_fun$ A_a_a_prod_prod$ )A_a_a_prod_prod_stream$ )
(declare-fun siterate$c (A_a_prod_a_a_prod_fun$ A_a_prod$ )A_a_prod_stream$ )
(declare-fun siterate$d (A_a_fun$ A$ )A_stream$ )
(assert (! (not (not (fun_app$ p$ (sdrop$ n$ omega$ )))):named a0 ))
(assert (! (less$ (enat$ n$ )(sfirst$ p$ omega$ )):named a1 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_fun_fun$ )(?v2 A_stream$ )(?v3 A_stream$ ))(= (sdrop$ ?v0 (smap2$ ?v1 ?v2 ?v3 ))(smap2$ ?v1 (sdrop$ ?v0 ?v2 )(sdrop$ ?v0 ?v3 )))):named a2 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_a_fun_fun$ )(?v2 A_stream$ )(?v3 A_a_prod_stream$ ))(= (sdrop$ ?v0 (smap2$a ?v1 ?v2 ?v3 ))(smap2$a ?v1 (sdrop$ ?v0 ?v2 )(sdrop$a ?v0 ?v3 )))):named a3 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_fun_fun$ )(?v2 A_a_prod_stream$ )(?v3 A_stream$ ))(= (sdrop$ ?v0 (smap2$b ?v1 ?v2 ?v3 ))(smap2$b ?v1 (sdrop$a ?v0 ?v2 )(sdrop$ ?v0 ?v3 )))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_a_prod_fun_fun$ )(?v2 A_stream$ )(?v3 A_stream$ ))(= (sdrop$a ?v0 (smap2$c ?v1 ?v2 ?v3 ))(smap2$c ?v1 (sdrop$ ?v0 ?v2 )(sdrop$ ?v0 ?v3 )))):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_prod_a_fun_fun$ )(?v2 A_a_prod_stream$ )(?v3 A_a_prod_stream$ ))(= (sdrop$ ?v0 (smap2$d ?v1 ?v2 ?v3 ))(smap2$d ?v1 (sdrop$a ?v0 ?v2 )(sdrop$a ?v0 ?v3 )))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_a_a_prod_fun_fun$ )(?v2 A_stream$ )(?v3 A_a_prod_stream$ ))(= (sdrop$a ?v0 (smap2$e ?v1 ?v2 ?v3 ))(smap2$e ?v1 (sdrop$ ?v0 ?v2 )(sdrop$a ?v0 ?v3 )))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_a_prod_fun_fun$ )(?v2 A_a_prod_stream$ )(?v3 A_stream$ ))(= (sdrop$a ?v0 (smap2$f ?v1 ?v2 ?v3 ))(smap2$f ?v1 (sdrop$a ?v0 ?v2 )(sdrop$ ?v0 ?v3 )))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_prod_a_a_prod_fun_fun$ )(?v2 A_a_prod_stream$ )(?v3 A_a_prod_stream$ ))(= (sdrop$a ?v0 (smap2$g ?v1 ?v2 ?v3 ))(smap2$g ?v1 (sdrop$a ?v0 ?v2 )(sdrop$a ?v0 ?v3 )))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_a_prod_a_fun_fun$ )(?v2 A_stream$ )(?v3 A_a_prod_a_prod_stream$ ))(= (sdrop$ ?v0 (smap2$h ?v1 ?v2 ?v3 ))(smap2$h ?v1 (sdrop$ ?v0 ?v2 )(sdrop$b ?v0 ?v3 )))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_a_prod_prod_a_fun_fun$ )(?v2 A_stream$ )(?v3 A_a_a_prod_prod_stream$ ))(= (sdrop$ ?v0 (smap2$i ?v1 ?v2 ?v3 ))(smap2$i ?v1 (sdrop$ ?v0 ?v2 )(sdrop$c ?v0 ?v3 )))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_stream$ )(?v2 A_stream$ ))(= (sdrop$a ?v0 (szip$ ?v1 ?v2 ))(szip$ (sdrop$ ?v0 ?v1 )(sdrop$ ?v0 ?v2 )))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_stream$ )(?v2 A_a_prod_stream$ ))(= (sdrop$c ?v0 (szip$a ?v1 ?v2 ))(szip$a (sdrop$ ?v0 ?v1 )(sdrop$a ?v0 ?v2 )))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_stream$ )(?v2 A_stream$ ))(= (sdrop$b ?v0 (szip$b ?v1 ?v2 ))(szip$b (sdrop$a ?v0 ?v1 )(sdrop$ ?v0 ?v2 )))):named a14 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_stream$ )(?v2 A_a_prod_stream$ ))(= (sdrop$d ?v0 (szip$c ?v1 ?v2 ))(szip$c (sdrop$a ?v0 ?v1 )(sdrop$a ?v0 ?v2 )))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_stream$ )(?v2 A_a_prod_a_prod_stream$ ))(= (sdrop$e ?v0 (szip$d ?v1 ?v2 ))(szip$d (sdrop$ ?v0 ?v1 )(sdrop$b ?v0 ?v2 )))):named a16 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_stream$ )(?v2 A_a_a_prod_prod_stream$ ))(= (sdrop$f ?v0 (szip$e ?v1 ?v2 ))(szip$e (sdrop$ ?v0 ?v1 )(sdrop$c ?v0 ?v2 )))):named a17 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_prod_stream$ )(?v2 A_stream$ ))(= (sdrop$g ?v0 (szip$f ?v1 ?v2 ))(szip$f (sdrop$b ?v0 ?v1 )(sdrop$ ?v0 ?v2 )))):named a18 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_prod_stream$ )(?v2 A_stream$ ))(= (sdrop$h ?v0 (szip$g ?v1 ?v2 ))(szip$g (sdrop$c ?v0 ?v1 )(sdrop$ ?v0 ?v2 )))):named a19 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_stream$ )(?v2 A_a_prod_a_a_prod_prod_stream$ ))(= (sdrop$i ?v0 (szip$h ?v1 ?v2 ))(szip$h (sdrop$ ?v0 ?v1 )(sdrop$d ?v0 ?v2 )))):named a20 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_stream$ )(?v2 A_a_prod_a_prod_stream$ ))(= (sdrop$j ?v0 (szip$i ?v1 ?v2 ))(szip$i (sdrop$a ?v0 ?v1 )(sdrop$b ?v0 ?v2 )))):named a21 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_stream_bool_fun$ )(?v1 Nat$ )(?v2 A_a_prod_a_a_prod_prod_stream$ ))(=> (fun_app$a (fun_app$b (ev_at$ ?v0 )?v1 )?v2 )(fun_app$a ?v0 (sdrop$d ?v1 ?v2 )))):named a22 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_stream_bool_fun$ )(?v1 Nat$ )(?v2 A_a_prod_a_prod_stream$ ))(=> (fun_app$c (fun_app$d (ev_at$a ?v0 )?v1 )?v2 )(fun_app$c ?v0 (sdrop$b ?v1 ?v2 )))):named a23 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_stream_bool_fun$ )(?v1 Nat$ )(?v2 A_a_a_prod_prod_stream$ ))(=> (fun_app$e (fun_app$f (ev_at$b ?v0 )?v1 )?v2 )(fun_app$e ?v0 (sdrop$c ?v1 ?v2 )))):named a24 ))
(assert (! (forall ((?v0 A_a_prod_stream_bool_fun$ )(?v1 Nat$ )(?v2 A_a_prod_stream$ ))(=> (fun_app$g (fun_app$h (ev_at$c ?v0 )?v1 )?v2 )(fun_app$g ?v0 (sdrop$a ?v1 ?v2 )))):named a25 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 Nat$ )(?v2 A_stream$ ))(=> (fun_app$ (fun_app$i (ev_at$d ?v0 )?v1 )?v2 )(fun_app$ ?v0 (sdrop$ ?v1 ?v2 )))):named a26 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_a_prod_a_a_prod_prod_stream$ ))(= (sdrop$d ?v0 (sdrop$d ?v1 ?v2 ))(sdrop$d (plus$ ?v1 ?v0 )?v2 ))):named a27 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_a_prod_a_prod_stream$ ))(= (sdrop$b ?v0 (sdrop$b ?v1 ?v2 ))(sdrop$b (plus$ ?v1 ?v0 )?v2 ))):named a28 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_a_a_prod_prod_stream$ ))(= (sdrop$c ?v0 (sdrop$c ?v1 ?v2 ))(sdrop$c (plus$ ?v1 ?v0 )?v2 ))):named a29 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_a_prod_stream$ ))(= (sdrop$a ?v0 (sdrop$a ?v1 ?v2 ))(sdrop$a (plus$ ?v1 ?v0 )?v2 ))):named a30 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_stream$ ))(= (sdrop$ ?v0 (sdrop$ ?v1 ?v2 ))(sdrop$ (plus$ ?v1 ?v0 )?v2 ))):named a31 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_fun$ )(?v2 A_stream$ ))(= (sdrop$ ?v0 (smap$ ?v1 ?v2 ))(smap$ ?v1 (sdrop$ ?v0 ?v2 )))):named a32 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_fun$ )(?v2 A_a_prod_stream$ ))(= (sdrop$ ?v0 (smap$a ?v1 ?v2 ))(smap$a ?v1 (sdrop$a ?v0 ?v2 )))):named a33 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_fun$ )(?v2 A_stream$ ))(= (sdrop$a ?v0 (smap$b ?v1 ?v2 ))(smap$b ?v1 (sdrop$ ?v0 ?v2 )))):named a34 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_prod_fun$ )(?v2 A_a_prod_stream$ ))(= (sdrop$a ?v0 (smap$c ?v1 ?v2 ))(smap$c ?v1 (sdrop$a ?v0 ?v2 )))):named a35 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_prod_a_fun$ )(?v2 A_a_prod_a_prod_stream$ ))(= (sdrop$ ?v0 (smap$d ?v1 ?v2 ))(smap$d ?v1 (sdrop$b ?v0 ?v2 )))):named a36 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_prod_a_fun$ )(?v2 A_a_a_prod_prod_stream$ ))(= (sdrop$ ?v0 (smap$e ?v1 ?v2 ))(smap$e ?v1 (sdrop$c ?v0 ?v2 )))):named a37 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_a_prod_fun$ )(?v2 A_stream$ ))(= (sdrop$b ?v0 (smap$f ?v1 ?v2 ))(smap$f ?v1 (sdrop$ ?v0 ?v2 )))):named a38 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_a_prod_prod_fun$ )(?v2 A_stream$ ))(= (sdrop$c ?v0 (smap$g ?v1 ?v2 ))(smap$g ?v1 (sdrop$ ?v0 ?v2 )))):named a39 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_prod_prod_a_fun$ )(?v2 A_a_prod_a_a_prod_prod_stream$ ))(= (sdrop$ ?v0 (smap$h ?v1 ?v2 ))(smap$h ?v1 (sdrop$d ?v0 ?v2 )))):named a40 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_prod_a_a_prod_fun$ )(?v2 A_a_prod_a_prod_stream$ ))(= (sdrop$a ?v0 (smap$i ?v1 ?v2 ))(smap$i ?v1 (sdrop$b ?v0 ?v2 )))):named a41 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_stream$ ))(! (= (sdrop$d zero$ ?v0 )?v0 ):pattern ((sdrop$d zero$ ?v0 )))):named a42 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_stream$ ))(! (= (sdrop$b zero$ ?v0 )?v0 ):pattern ((sdrop$b zero$ ?v0 )))):named a43 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_stream$ ))(! (= (sdrop$c zero$ ?v0 )?v0 ):pattern ((sdrop$c zero$ ?v0 )))):named a44 ))
(assert (! (forall ((?v0 A_a_prod_stream$ ))(! (= (sdrop$a zero$ ?v0 )?v0 ):pattern ((sdrop$a zero$ ?v0 )))):named a45 ))
(assert (! (forall ((?v0 A_stream$ ))(! (= (sdrop$ zero$ ?v0 )?v0 ):pattern ((sdrop$ zero$ ?v0 )))):named a46 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_prod_prod_stream$ ))(= (sdrop$d ?v0 (stl$d ?v1 ))(stl$d (sdrop$d ?v0 ?v1 )))):named a47 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_prod_stream$ ))(= (sdrop$b ?v0 (stl$b ?v1 ))(stl$b (sdrop$b ?v0 ?v1 )))):named a48 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_prod_stream$ ))(= (sdrop$c ?v0 (stl$c ?v1 ))(stl$c (sdrop$c ?v0 ?v1 )))):named a49 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_stream$ ))(= (sdrop$a ?v0 (stl$a ?v1 ))(stl$a (sdrop$a ?v0 ?v1 )))):named a50 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_stream$ ))(= (sdrop$ ?v0 (stl$ ?v1 ))(stl$ (sdrop$ ?v0 ?v1 )))):named a51 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_stream_bool_fun$ )(?v1 A_a_prod_a_a_prod_prod_stream$ ))(= (fun_app$a (ev$ ?v0 )?v1 )(exists ((?v2 Nat$ ))(fun_app$a ?v0 (sdrop$d ?v2 ?v1 ))))):named a52 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_stream_bool_fun$ )(?v1 A_a_prod_a_prod_stream$ ))(= (fun_app$c (ev$a ?v0 )?v1 )(exists ((?v2 Nat$ ))(fun_app$c ?v0 (sdrop$b ?v2 ?v1 ))))):named a53 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_stream_bool_fun$ )(?v1 A_a_a_prod_prod_stream$ ))(= (fun_app$e (ev$b ?v0 )?v1 )(exists ((?v2 Nat$ ))(fun_app$e ?v0 (sdrop$c ?v2 ?v1 ))))):named a54 ))
(assert (! (forall ((?v0 A_a_prod_stream_bool_fun$ )(?v1 A_a_prod_stream$ ))(= (fun_app$g (ev$c ?v0 )?v1 )(exists ((?v2 Nat$ ))(fun_app$g ?v0 (sdrop$a ?v2 ?v1 ))))):named a55 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(= (fun_app$ (ev$d ?v0 )?v1 )(exists ((?v2 Nat$ ))(fun_app$ ?v0 (sdrop$ ?v2 ?v1 ))))):named a56 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_stream_bool_fun$ )(?v1 A_a_prod_a_a_prod_prod_stream$ ))(= (fun_app$a (alw$ ?v0 )?v1 )(forall ((?v2 Nat$ ))(fun_app$a ?v0 (sdrop$d ?v2 ?v1 ))))):named a57 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_stream_bool_fun$ )(?v1 A_a_prod_a_prod_stream$ ))(= (fun_app$c (alw$a ?v0 )?v1 )(forall ((?v2 Nat$ ))(fun_app$c ?v0 (sdrop$b ?v2 ?v1 ))))):named a58 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_stream_bool_fun$ )(?v1 A_a_a_prod_prod_stream$ ))(= (fun_app$e (alw$b ?v0 )?v1 )(forall ((?v2 Nat$ ))(fun_app$e ?v0 (sdrop$c ?v2 ?v1 ))))):named a59 ))
(assert (! (forall ((?v0 A_a_prod_stream_bool_fun$ )(?v1 A_a_prod_stream$ ))(= (fun_app$g (alw$c ?v0 )?v1 )(forall ((?v2 Nat$ ))(fun_app$g ?v0 (sdrop$a ?v2 ?v1 ))))):named a60 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(= (fun_app$ (alw$d ?v0 )?v1 )(forall ((?v2 Nat$ ))(fun_app$ ?v0 (sdrop$ ?v2 ?v1 ))))):named a61 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_stream_bool_fun$ )(?v1 A_a_prod_a_a_prod_prod_stream$ )(?v2 Nat$ ))(=> (fun_app$a (alw$ ?v0 )?v1 )(fun_app$a (alw$ ?v0 )(sdrop$d ?v2 ?v1 )))):named a62 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_stream_bool_fun$ )(?v1 A_a_prod_a_prod_stream$ )(?v2 Nat$ ))(=> (fun_app$c (alw$a ?v0 )?v1 )(fun_app$c (alw$a ?v0 )(sdrop$b ?v2 ?v1 )))):named a63 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_stream_bool_fun$ )(?v1 A_a_a_prod_prod_stream$ )(?v2 Nat$ ))(=> (fun_app$e (alw$b ?v0 )?v1 )(fun_app$e (alw$b ?v0 )(sdrop$c ?v2 ?v1 )))):named a64 ))
(assert (! (forall ((?v0 A_a_prod_stream_bool_fun$ )(?v1 A_a_prod_stream$ )(?v2 Nat$ ))(=> (fun_app$g (alw$c ?v0 )?v1 )(fun_app$g (alw$c ?v0 )(sdrop$a ?v2 ?v1 )))):named a65 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(=> (fun_app$ (alw$d ?v0 )?v1 )(fun_app$ (alw$d ?v0 )(sdrop$ ?v2 ?v1 )))):named a66 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_prod_stream_bool_fun$ )(?v1 A_a_prod_a_a_prod_prod_stream$ ))(=> (fun_app$a (ev$ ?v0 )?v1 )(fun_app$a ?v0 (sdrop$d (wait$ ?v0 ?v1 )?v1 )))):named a67 ))
(assert (! (forall ((?v0 A_a_prod_a_prod_stream_bool_fun$ )(?v1 A_a_prod_a_prod_stream$ ))(=> (fun_app$c (ev$a ?v0 )?v1 )(fun_app$c ?v0 (sdrop$b (wait$a ?v0 ?v1 )?v1 )))):named a68 ))
(assert (! (forall ((?v0 A_a_a_prod_prod_stream_bool_fun$ )(?v1 A_a_a_prod_prod_stream$ ))(=> (fun_app$e (ev$b ?v0 )?v1 )(fun_app$e ?v0 (sdrop$c (wait$b ?v0 ?v1 )?v1 )))):named a69 ))
(assert (! (forall ((?v0 A_a_prod_stream_bool_fun$ )(?v1 A_a_prod_stream$ ))(=> (fun_app$g (ev$c ?v0 )?v1 )(fun_app$g ?v0 (sdrop$a (wait$c ?v0 ?v1 )?v1 )))):named a70 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(=> (fun_app$ (ev$d ?v0 )?v1 )(fun_app$ ?v0 (sdrop$ (wait$d ?v0 ?v1 )?v1 )))):named a71 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_prod_prod_a_a_prod_a_a_prod_prod_fun$ )(?v2 A_a_prod_a_a_prod_prod$ ))(= (sdrop$d ?v0 (siterate$ ?v1 ?v2 ))(siterate$ ?v1 (fun_app$j (fun_app$k (compow$ ?v0 )?v1 )?v2 )))):named a72 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_prod_a_a_prod_a_prod_fun$ )(?v2 A_a_prod_a_prod$ ))(= (sdrop$b ?v0 (siterate$a ?v1 ?v2 ))(siterate$a ?v1 (fun_app$l (fun_app$m (compow$a ?v0 )?v1 )?v2 )))):named a73 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_prod_prod_a_a_a_prod_prod_fun$ )(?v2 A_a_a_prod_prod$ ))(= (sdrop$c ?v0 (siterate$b ?v1 ?v2 ))(siterate$b ?v1 (fun_app$n (fun_app$o (compow$b ?v0 )?v1 )?v2 )))):named a74 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_prod_a_a_prod_fun$ )(?v2 A_a_prod$ ))(= (sdrop$a ?v0 (siterate$c ?v1 ?v2 ))(siterate$c ?v1 (fun_app$p (fun_app$q (compow$c ?v0 )?v1 )?v2 )))):named a75 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_fun$ )(?v2 A$ ))(= (sdrop$ ?v0 (siterate$d ?v1 ?v2 ))(siterate$d ?v1 (fun_app$r (fun_app$s (compow$d ?v0 )?v1 )?v2 )))):named a76 ))
(assert (! (forall ((?v0 A_a_prod_stream_bool_fun$ ))(= (alw$c (alw$c ?v0 ))(alw$c ?v0 ))):named a77 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ ))(= (alw$d (alw$d ?v0 ))(alw$d ?v0 ))):named a78 ))
(assert (! (forall ((?v0 A_a_prod_stream_bool_fun$ ))(= (ev$c (ev$c ?v0 ))(ev$c ?v0 ))):named a79 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ ))(= (ev$d (ev$d ?v0 ))(ev$d ?v0 ))):named a80 ))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$ )(?v1 A_a_prod_stream$ ))(= (stl$a (smap$c ?v0 ?v1 ))(smap$c ?v0 (stl$a ?v1 )))):named a81 ))
(assert (! (forall ((?v0 A_a_a_prod_fun$ )(?v1 A_stream$ ))(= (stl$a (smap$b ?v0 ?v1 ))(smap$b ?v0 (stl$ ?v1 )))):named a82 ))
(assert (! (forall ((?v0 A_a_prod_a_fun$ )(?v1 A_a_prod_stream$ ))(= (stl$ (smap$a ?v0 ?v1 ))(smap$a ?v0 (stl$a ?v1 )))):named a83 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ ))(= (stl$ (smap$ ?v0 ?v1 ))(smap$ ?v0 (stl$ ?v1 )))):named a84 ))
(assert (! (forall ((?v0 A_a_prod_stream_bool_fun$ )(?v1 A_a_prod_stream$ ))(! (= (fun_app$g (fun_app$h (ev_at$c ?v0 )zero$ )?v1 )(fun_app$g ?v0 ?v1 )):pattern ((fun_app$g (fun_app$h (ev_at$c ?v0 )zero$ )?v1 )))):named a85 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(! (= (fun_app$ (fun_app$i (ev_at$d ?v0 )zero$ )?v1 )(fun_app$ ?v0 ?v1 )):pattern ((fun_app$ (fun_app$i (ev_at$d ?v0 )zero$ )?v1 )))):named a86 ))
(check-sat )
;(get-unsat-core )
