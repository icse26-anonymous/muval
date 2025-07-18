;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_enat_fun$ 0 )
(declare-sort B_a_bool_fun_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-sort B_llist_bool_fun$ 0 )
(declare-sort B_llist_enat_fun$ 0 )
(declare-sort B_llist_b_llist_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort B_llist_b_llist_bool_fun_fun$ 0 )
(declare-sort B_b_prod_llist_b_b_prod_llist_fun$ 0 )
(declare-sort B_b_b_prod_prod_llist_b_b_b_prod_prod_llist_fun$ 0 )
(declare-sort B_b_prod_b_prod_llist_b_b_prod_b_prod_llist_fun$ 0 )
(declare-sort B_b_prod_b_b_prod_prod_llist_b_b_prod_b_b_prod_prod_llist_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-sort B_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun lNil$a ()B_llist$)
(declare-fun lhd$a (B_llist$)B$)
(declare-fun ltl$a (B_llist$)B_llist$)
(declare-fun lCons$a (B$ B_llist$ )B_llist$)
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-sort B_b_prod$ 0)
(declare-sort B_b_prod_b_b_prod_prod$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun fst$ (B_b_prod$)B$)
(declare-fun snd$ (B_b_prod$)B$)
(declare-fun pair$ (B$ B$ )B_b_prod$)
(declare-fun fst$a (B_b_prod_b_b_prod_prod$)B_b_prod$)
(declare-fun snd$a (B_b_prod_b_b_prod_prod$)B_b_prod$)
(declare-fun pair$a (B_b_prod$ B_b_prod$ )B_b_prod_b_b_prod_prod$)
(declare-sort B_b_prod_b_b_prod_prod_llist$ 0)
(declare-fun lNil$b ()B_b_prod_b_b_prod_prod_llist$)
(declare-fun lhd$b (B_b_prod_b_b_prod_prod_llist$)B_b_prod_b_b_prod_prod$)
(declare-fun ltl$b (B_b_prod_b_b_prod_prod_llist$)B_b_prod_b_b_prod_prod_llist$)
(declare-fun lCons$b (B_b_prod_b_b_prod_prod$ B_b_prod_b_b_prod_prod_llist$ )B_b_prod_b_b_prod_prod_llist$)
(declare-sort B_b_prod_b_prod$ 0)
(declare-fun fst$b (B_b_prod_b_prod$)B_b_prod$)
(declare-fun snd$b (B_b_prod_b_prod$)B$)
(declare-fun pair$b (B_b_prod$ B$ )B_b_prod_b_prod$)
(declare-sort B_b_prod_b_prod_llist$ 0)
(declare-fun lNil$c ()B_b_prod_b_prod_llist$)
(declare-fun lhd$c (B_b_prod_b_prod_llist$)B_b_prod_b_prod$)
(declare-fun ltl$c (B_b_prod_b_prod_llist$)B_b_prod_b_prod_llist$)
(declare-fun lCons$c (B_b_prod_b_prod$ B_b_prod_b_prod_llist$ )B_b_prod_b_prod_llist$)
(declare-sort B_b_b_prod_prod$ 0)
(declare-fun fst$c (B_b_b_prod_prod$)B$)
(declare-fun snd$c (B_b_b_prod_prod$)B_b_prod$)
(declare-fun pair$c (B$ B_b_prod$ )B_b_b_prod_prod$)
(declare-sort B_b_b_prod_prod_llist$ 0)
(declare-sort B_b_prod_llist$ 0)
(declare-fun lNil$d ()B_b_b_prod_prod_llist$)
(declare-fun lhd$d (B_b_b_prod_prod_llist$)B_b_b_prod_prod$)
(declare-fun ltl$d (B_b_b_prod_prod_llist$)B_b_b_prod_prod_llist$)
(declare-fun lCons$d (B_b_b_prod_prod$ B_b_b_prod_prod_llist$ )B_b_b_prod_prod_llist$)
(declare-fun lNil$e ()B_b_prod_llist$)
(declare-fun lhd$e (B_b_prod_llist$)B_b_prod$)
(declare-fun ltl$e (B_b_prod_llist$)B_b_prod_llist$)
(declare-fun lCons$e (B_b_prod$ B_b_prod_llist$ )B_b_prod_llist$)
(declare-sort B_b_b_prod_b_prod_prod$ 0)
(declare-fun fst$d (B_b_b_prod_b_prod_prod$)B$)
(declare-fun snd$d (B_b_b_prod_b_prod_prod$)B_b_prod_b_prod$)
(declare-fun pair$d (B$ B_b_prod_b_prod$ )B_b_b_prod_b_prod_prod$)
(declare-sort B_b_b_prod_b_prod_prod_llist$ 0)
(declare-fun lNil$f ()B_b_b_prod_b_prod_prod_llist$)
(declare-fun lhd$f (B_b_b_prod_b_prod_prod_llist$)B_b_b_prod_b_prod_prod$)
(declare-fun ltl$f (B_b_b_prod_b_prod_prod_llist$)B_b_b_prod_b_prod_prod_llist$)
(declare-fun lCons$f (B_b_b_prod_b_prod_prod$ B_b_b_prod_b_prod_prod_llist$ )B_b_b_prod_b_prod_prod_llist$)
(declare-sort B_b_b_b_prod_prod_prod$ 0)
(declare-fun fst$e (B_b_b_b_prod_prod_prod$)B$)
(declare-fun snd$e (B_b_b_b_prod_prod_prod$)B_b_b_prod_prod$)
(declare-fun pair$e (B$ B_b_b_prod_prod$ )B_b_b_b_prod_prod_prod$)
(declare-sort B_b_b_b_prod_prod_prod_llist$ 0)
(declare-fun lNil$g ()B_b_b_b_prod_prod_prod_llist$)
(declare-fun lhd$g (B_b_b_b_prod_prod_prod_llist$)B_b_b_b_prod_prod_prod$)
(declare-fun ltl$g (B_b_b_b_prod_prod_prod_llist$)B_b_b_b_prod_prod_prod_llist$)
(declare-fun lCons$g (B_b_b_b_prod_prod_prod$ B_b_b_b_prod_prod_prod_llist$ )B_b_b_b_prod_prod_prod_llist$)
(declare-sort B_b_prod_b_prod_b_prod$ 0)
(declare-fun fst$f (B_b_prod_b_prod_b_prod$)B_b_prod_b_prod$)
(declare-fun snd$f (B_b_prod_b_prod_b_prod$)B$)
(declare-fun pair$f (B_b_prod_b_prod$ B$ )B_b_prod_b_prod_b_prod$)
(declare-sort B_b_prod_b_prod_b_prod_llist$ 0)
(declare-fun lNil$h ()B_b_prod_b_prod_b_prod_llist$)
(declare-fun lhd$h (B_b_prod_b_prod_b_prod_llist$)B_b_prod_b_prod_b_prod$)
(declare-fun ltl$h (B_b_prod_b_prod_b_prod_llist$)B_b_prod_b_prod_b_prod_llist$)
(declare-fun lCons$h (B_b_prod_b_prod_b_prod$ B_b_prod_b_prod_b_prod_llist$ )B_b_prod_b_prod_b_prod_llist$)
(declare-sort B_b_b_prod_prod_b_prod$ 0)
(declare-fun fst$g (B_b_b_prod_prod_b_prod$)B_b_b_prod_prod$)
(declare-fun snd$g (B_b_b_prod_prod_b_prod$)B$)
(declare-fun pair$g (B_b_b_prod_prod$ B$ )B_b_b_prod_prod_b_prod$)
(declare-sort B_b_b_prod_prod_b_prod_llist$ 0)
(declare-fun lNil$i ()B_b_b_prod_prod_b_prod_llist$)
(declare-fun lhd$i (B_b_b_prod_prod_b_prod_llist$)B_b_b_prod_prod_b_prod$)
(declare-fun ltl$i (B_b_b_prod_prod_b_prod_llist$)B_b_b_prod_prod_b_prod_llist$)
(declare-fun lCons$i (B_b_b_prod_prod_b_prod$ B_b_b_prod_prod_b_prod_llist$ )B_b_b_prod_prod_b_prod_llist$)
(declare-sort B_b_b_prod_b_b_prod_prod_prod$ 0)
(declare-fun fst$h (B_b_b_prod_b_b_prod_prod_prod$)B$)
(declare-fun snd$h (B_b_b_prod_b_b_prod_prod_prod$)B_b_prod_b_b_prod_prod$)
(declare-fun pair$h (B$ B_b_prod_b_b_prod_prod$ )B_b_b_prod_b_b_prod_prod_prod$)
(declare-sort B_b_b_prod_b_b_prod_prod_prod_llist$ 0)
(declare-fun lNil$j ()B_b_b_prod_b_b_prod_prod_prod_llist$)
(declare-fun lhd$j (B_b_b_prod_b_b_prod_prod_prod_llist$)B_b_b_prod_b_b_prod_prod_prod$)
(declare-fun ltl$j (B_b_b_prod_b_b_prod_prod_prod_llist$)B_b_b_prod_b_b_prod_prod_prod_llist$)
(declare-fun lCons$j (B_b_b_prod_b_b_prod_prod_prod$ B_b_b_prod_b_b_prod_prod_prod_llist$ )B_b_b_prod_b_b_prod_prod_prod_llist$)
(declare-sort B_b_prod_b_b_prod_b_prod_prod$ 0)
(declare-fun fst$i (B_b_prod_b_b_prod_b_prod_prod$)B_b_prod$)
(declare-fun snd$i (B_b_prod_b_b_prod_b_prod_prod$)B_b_prod_b_prod$)
(declare-fun pair$i (B_b_prod$ B_b_prod_b_prod$ )B_b_prod_b_b_prod_b_prod_prod$)
(declare-sort B_b_prod_b_b_prod_b_prod_prod_llist$ 0)
(declare-fun lNil$k ()B_b_prod_b_b_prod_b_prod_prod_llist$)
(declare-fun lhd$k (B_b_prod_b_b_prod_b_prod_prod_llist$)B_b_prod_b_b_prod_b_prod_prod$)
(declare-fun ltl$k (B_b_prod_b_b_prod_b_prod_prod_llist$)B_b_prod_b_b_prod_b_prod_prod_llist$)
(declare-fun lCons$k (B_b_prod_b_b_prod_b_prod_prod$ B_b_prod_b_b_prod_b_prod_prod_llist$ )B_b_prod_b_b_prod_b_prod_prod_llist$)
(declare-fun p$ ()A_b_bool_fun_fun$ )
(declare-fun uu$ ()B_b_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()B_llist$ )
(declare-fun uua$ ()B_llist_b_llist_bool_fun_fun$ )
(declare-fun uub$ ()A_a_bool_fun_fun$ )
(declare-fun uuc$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun xs$a ()A_llist$ )
(declare-fun llcp$ (A_llist$ )A_llist_enat_fun$ )
(declare-fun lzip$ (B_llist$ B_llist$ )B_b_prod_llist$ )
(declare-fun plus$ (Enat$ Enat$ )Enat$ )
(declare-fun zero$ ()Enat$ )
(declare-fun ldrop$ (Enat$ )B_llist_b_llist_fun$ )
(declare-fun llcp$a (B_llist$ )B_llist_enat_fun$ )
(declare-fun ltake$ (Enat$ B_llist$ )B_llist$ )
(declare-fun lzip$a (B_llist$ B_b_prod_llist$ )B_b_b_prod_prod_llist$ )
(declare-fun lzip$b (B_b_prod_llist$ B_llist$ )B_b_prod_b_prod_llist$ )
(declare-fun lzip$c (B_b_prod_llist$ B_b_prod_llist$ )B_b_prod_b_b_prod_prod_llist$ )
(declare-fun lzip$d (B_llist$ B_b_prod_b_prod_llist$ )B_b_b_prod_b_prod_prod_llist$ )
(declare-fun lzip$e (B_llist$ B_b_b_prod_prod_llist$ )B_b_b_b_prod_prod_prod_llist$ )
(declare-fun lzip$f (B_b_prod_b_prod_llist$ B_llist$ )B_b_prod_b_prod_b_prod_llist$ )
(declare-fun lzip$g (B_b_b_prod_prod_llist$ B_llist$ )B_b_b_prod_prod_b_prod_llist$ )
(declare-fun lzip$h (B_llist$ B_b_prod_b_b_prod_prod_llist$ )B_b_b_prod_b_b_prod_prod_prod_llist$ )
(declare-fun lzip$i (B_b_prod_llist$ B_b_prod_b_prod_llist$ )B_b_prod_b_b_prod_b_prod_prod_llist$ )
(declare-fun ldrop$a (Enat$ )B_b_prod_b_b_prod_prod_llist_b_b_prod_b_b_prod_prod_llist_fun$ )
(declare-fun ldrop$b (Enat$ )B_b_prod_b_prod_llist_b_b_prod_b_prod_llist_fun$ )
(declare-fun ldrop$c (Enat$ )B_b_b_prod_prod_llist_b_b_b_prod_prod_llist_fun$ )
(declare-fun ldrop$d (Enat$ )B_b_prod_llist_b_b_prod_llist_fun$ )
(declare-fun ldrop$e (Enat$ B_b_b_prod_b_prod_prod_llist$ )B_b_b_prod_b_prod_prod_llist$ )
(declare-fun ldrop$f (Enat$ B_b_b_b_prod_prod_prod_llist$ )B_b_b_b_prod_prod_prod_llist$ )
(declare-fun ldrop$g (Enat$ B_b_prod_b_prod_b_prod_llist$ )B_b_prod_b_prod_b_prod_llist$ )
(declare-fun ldrop$h (Enat$ B_b_b_prod_prod_b_prod_llist$ )B_b_b_prod_prod_b_prod_llist$ )
(declare-fun ldrop$i (Enat$ B_b_b_prod_b_b_prod_prod_prod_llist$ )B_b_b_prod_b_b_prod_prod_prod_llist$ )
(declare-fun ldrop$j (Enat$ B_b_prod_b_b_prod_b_prod_prod_llist$ )B_b_prod_b_b_prod_b_prod_prod_llist$ )
(declare-fun fun_app$ (B_llist_bool_fun$ B_llist$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (Enat$ Enat$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun fun_app$a (B_llist_b_llist_bool_fun_fun$ B_llist$ )B_llist_bool_fun$ )
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$c (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$d (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$e (B_b_bool_fun_fun$ B$ )B_bool_fun$ )
(declare-fun fun_app$f (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$g (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$h (B_llist_b_llist_fun$ B_llist$ )B_llist$ )
(declare-fun fun_app$i (B_a_bool_fun_fun$ B$ )A_bool_fun$ )
(declare-fun fun_app$j (A_b_bool_fun_fun$ A$ )B_bool_fun$ )
(declare-fun fun_app$k (A_llist_enat_fun$ A_llist$ )Enat$ )
(declare-fun fun_app$l (B_llist_enat_fun$ B_llist$ )Enat$ )
(declare-fun fun_app$m (B_b_prod_b_b_prod_prod_llist_b_b_prod_b_b_prod_prod_llist_fun$ B_b_prod_b_b_prod_prod_llist$ )B_b_prod_b_b_prod_prod_llist$ )
(declare-fun fun_app$n (B_b_prod_b_prod_llist_b_b_prod_b_prod_llist_fun$ B_b_prod_b_prod_llist$ )B_b_prod_b_prod_llist$ )
(declare-fun fun_app$o (B_b_b_prod_prod_llist_b_b_b_prod_prod_llist_fun$ B_b_b_prod_prod_llist$ )B_b_b_prod_prod_llist$ )
(declare-fun fun_app$p (B_b_prod_llist_b_b_prod_llist_fun$ B_b_prod_llist$ )B_b_prod_llist$ )
(declare-fun lappend$a (B_llist$ B_llist$ )B_llist$ )
(declare-fun lfinite$a (B_llist$ )Bool )
(declare-fun llength$a (B_llist$ )Enat$ )
(declare-fun llist_all2$ (A_b_bool_fun_fun$ A_llist$ B_llist$ )Bool )
(declare-fun llist_all2$a (B_b_bool_fun_fun$ )B_llist_b_llist_bool_fun_fun$ )
(declare-fun llist_all2$b (A_a_bool_fun_fun$ )A_llist_a_llist_bool_fun_fun$ )
(declare-fun llist_all2$c (B_a_bool_fun_fun$ B_llist$ A_llist$ )Bool )
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(! (= (fun_app$ (fun_app$a uua$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (fun_app$a uua$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$b (fun_app$c uuc$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (fun_app$c uuc$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(! (= (fun_app$d (fun_app$e uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$d (fun_app$e uu$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (fun_app$f (fun_app$g uub$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$f (fun_app$g uub$ ?v0 )?v1 )))):named a3 ))
(assert (! (not (llist_all2$ p$ xs$ (fun_app$h (ldrop$ (llength$ xs$a ))ys$ ))):named a4 ))
(assert (! (lfinite$ xs$a ):named a5 ))
(assert (! (llist_all2$ p$ (lappend$ xs$a xs$ )ys$ ):named a6 ))
(assert (! (= (llist_all2$a uu$ )uua$ ):named a7 ))
(assert (! (= (llist_all2$b uub$ )uuc$ ):named a8 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ )(?v3 B_b_bool_fun_fun$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$a ?v0 )?v1 )?v2 )(forall ((?v4 B$ )(?v5 B$ ))(=> (fun_app$d (fun_app$e ?v0 ?v4 )?v5 )(fun_app$d (fun_app$e ?v3 ?v4 )?v5 ))))(fun_app$ (fun_app$a (llist_all2$a ?v3 )?v1 )?v2 ))):named a9 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_llist$ )(?v3 B_a_bool_fun_fun$ ))(=> (and (llist_all2$c ?v0 ?v1 ?v2 )(forall ((?v4 B$ )(?v5 A$ ))(=> (fun_app$f (fun_app$i ?v0 ?v4 )?v5 )(fun_app$f (fun_app$i ?v3 ?v4 )?v5 ))))(llist_all2$c ?v3 ?v1 ?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_a_bool_fun_fun$ ))(=> (and (fun_app$b (fun_app$c (llist_all2$b ?v0 )?v1 )?v2 )(forall ((?v4 A$ )(?v5 A$ ))(=> (fun_app$f (fun_app$g ?v0 ?v4 )?v5 )(fun_app$f (fun_app$g ?v3 ?v4 )?v5 ))))(fun_app$b (fun_app$c (llist_all2$b ?v3 )?v1 )?v2 ))):named a11 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B_llist$ )(?v3 A_b_bool_fun_fun$ ))(=> (and (llist_all2$ ?v0 ?v1 ?v2 )(forall ((?v4 A$ )(?v5 B$ ))(=> (fun_app$d (fun_app$j ?v0 ?v4 )?v5 )(fun_app$d (fun_app$j ?v3 ?v4 )?v5 ))))(llist_all2$ ?v3 ?v1 ?v2 ))):named a12 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (fun_app$b (fun_app$c (llist_all2$b ?v0 )?v1 )?v2 )(= (llength$ ?v1 )(llength$ ?v2 )))):named a13 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_llist$ ))(=> (llist_all2$c ?v0 ?v1 ?v2 )(= (llength$a ?v1 )(llength$ ?v2 )))):named a14 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ ))(=> (fun_app$ (fun_app$a (llist_all2$a ?v0 )?v1 )?v2 )(= (llength$a ?v1 )(llength$a ?v2 )))):named a15 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B_llist$ ))(=> (llist_all2$ ?v0 ?v1 ?v2 )(= (llength$ ?v1 )(llength$a ?v2 )))):named a16 ))
(assert (! (llist_all2$ p$ xs$a (ltake$ (llength$ xs$a )ys$ )):named a17 ))
(assert (! (= (plus$ (llength$ xs$a )(llength$ xs$ ))(llength$a ys$ )):named a18 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ ))(=> (fun_app$ (fun_app$a (llist_all2$a ?v0 )?v1 )?v2 )(= (lfinite$a ?v1 )(lfinite$a ?v2 )))):named a19 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_llist$ ))(=> (llist_all2$c ?v0 ?v1 ?v2 )(= (lfinite$a ?v1 )(lfinite$ ?v2 )))):named a20 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (fun_app$b (fun_app$c (llist_all2$b ?v0 )?v1 )?v2 )(= (lfinite$ ?v1 )(lfinite$ ?v2 )))):named a21 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B_llist$ ))(=> (llist_all2$ ?v0 ?v1 ?v2 )(= (lfinite$ ?v1 )(lfinite$a ?v2 )))):named a22 ))
(assert (! (less_eq$ (llength$ xs$ )(llength$a ys$ )):named a23 ))
(assert (! (less_eq$ (llength$ xs$a )(llength$a ys$ )):named a24 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ )(?v3 B_llist$ )(?v4 B_llist$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$a ?v0 )?v1 )?v2 )(=> (and (lfinite$a ?v1 )(lfinite$a ?v2 ))(fun_app$ (fun_app$a (llist_all2$a ?v0 )?v3 )?v4 )))(fun_app$ (fun_app$a (llist_all2$a ?v0 )(lappend$a ?v1 ?v3 ))(lappend$a ?v2 ?v4 )))):named a25 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_llist$ )(?v3 B_llist$ )(?v4 A_llist$ ))(=> (and (llist_all2$c ?v0 ?v1 ?v2 )(=> (and (lfinite$a ?v1 )(lfinite$ ?v2 ))(llist_all2$c ?v0 ?v3 ?v4 )))(llist_all2$c ?v0 (lappend$a ?v1 ?v3 )(lappend$ ?v2 ?v4 )))):named a26 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist$ )(?v4 A_llist$ ))(=> (and (fun_app$b (fun_app$c (llist_all2$b ?v0 )?v1 )?v2 )(=> (and (lfinite$ ?v1 )(lfinite$ ?v2 ))(fun_app$b (fun_app$c (llist_all2$b ?v0 )?v3 )?v4 )))(fun_app$b (fun_app$c (llist_all2$b ?v0 )(lappend$ ?v1 ?v3 ))(lappend$ ?v2 ?v4 )))):named a27 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B_llist$ )(?v3 A_llist$ )(?v4 B_llist$ ))(=> (and (llist_all2$ ?v0 ?v1 ?v2 )(=> (and (lfinite$ ?v1 )(lfinite$a ?v2 ))(llist_all2$ ?v0 ?v3 ?v4 )))(llist_all2$ ?v0 (lappend$ ?v1 ?v3 )(lappend$a ?v2 ?v4 )))):named a28 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (= (llength$ ?v0 )(llength$ ?v1 ))(= (= (lappend$ ?v0 ?v2 )(lappend$ ?v1 ?v3 ))(and (= ?v0 ?v1 )(=> (lfinite$ ?v0 )(= ?v2 ?v3 )))))):named a29 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ )(?v2 B_llist$ )(?v3 B_llist$ ))(=> (= (llength$a ?v0 )(llength$a ?v1 ))(= (= (lappend$a ?v0 ?v2 )(lappend$a ?v1 ?v3 ))(and (= ?v0 ?v1 )(=> (lfinite$a ?v0 )(= ?v2 ?v3 )))))):named a30 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$k (llcp$ ?v0 )?v0 )(llength$ ?v0 )):pattern ((llcp$ ?v0 )))):named a31 ))
(assert (! (forall ((?v0 B_llist$ ))(! (= (fun_app$l (llcp$a ?v0 )?v0 )(llength$a ?v0 )):pattern ((llcp$a ?v0 )))):named a32 ))
(assert (! (forall ((?v0 B_b_prod_b_b_prod_prod_llist$ ))(= (fun_app$m (ldrop$a zero$ )?v0 )?v0 )):named a33 ))
(assert (! (forall ((?v0 B_b_prod_b_prod_llist$ ))(= (fun_app$n (ldrop$b zero$ )?v0 )?v0 )):named a34 ))
(assert (! (forall ((?v0 B_b_b_prod_prod_llist$ ))(= (fun_app$o (ldrop$c zero$ )?v0 )?v0 )):named a35 ))
(assert (! (forall ((?v0 B_b_prod_llist$ ))(= (fun_app$p (ldrop$d zero$ )?v0 )?v0 )):named a36 ))
(assert (! (forall ((?v0 B_llist$ ))(= (fun_app$h (ldrop$ zero$ )?v0 )?v0 )):named a37 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_llist$ )(?v2 B_llist$ ))(= (fun_app$p (ldrop$d ?v0 )(lzip$ ?v1 ?v2 ))(lzip$ (fun_app$h (ldrop$ ?v0 )?v1 )(fun_app$h (ldrop$ ?v0 )?v2 )))):named a38 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_llist$ )(?v2 B_b_prod_llist$ ))(= (fun_app$o (ldrop$c ?v0 )(lzip$a ?v1 ?v2 ))(lzip$a (fun_app$h (ldrop$ ?v0 )?v1 )(fun_app$p (ldrop$d ?v0 )?v2 )))):named a39 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_b_prod_llist$ )(?v2 B_llist$ ))(= (fun_app$n (ldrop$b ?v0 )(lzip$b ?v1 ?v2 ))(lzip$b (fun_app$p (ldrop$d ?v0 )?v1 )(fun_app$h (ldrop$ ?v0 )?v2 )))):named a40 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_b_prod_llist$ )(?v2 B_b_prod_llist$ ))(= (fun_app$m (ldrop$a ?v0 )(lzip$c ?v1 ?v2 ))(lzip$c (fun_app$p (ldrop$d ?v0 )?v1 )(fun_app$p (ldrop$d ?v0 )?v2 )))):named a41 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_llist$ )(?v2 B_b_prod_b_prod_llist$ ))(= (ldrop$e ?v0 (lzip$d ?v1 ?v2 ))(lzip$d (fun_app$h (ldrop$ ?v0 )?v1 )(fun_app$n (ldrop$b ?v0 )?v2 )))):named a42 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_llist$ )(?v2 B_b_b_prod_prod_llist$ ))(= (ldrop$f ?v0 (lzip$e ?v1 ?v2 ))(lzip$e (fun_app$h (ldrop$ ?v0 )?v1 )(fun_app$o (ldrop$c ?v0 )?v2 )))):named a43 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_b_prod_b_prod_llist$ )(?v2 B_llist$ ))(= (ldrop$g ?v0 (lzip$f ?v1 ?v2 ))(lzip$f (fun_app$n (ldrop$b ?v0 )?v1 )(fun_app$h (ldrop$ ?v0 )?v2 )))):named a44 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_b_b_prod_prod_llist$ )(?v2 B_llist$ ))(= (ldrop$h ?v0 (lzip$g ?v1 ?v2 ))(lzip$g (fun_app$o (ldrop$c ?v0 )?v1 )(fun_app$h (ldrop$ ?v0 )?v2 )))):named a45 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_llist$ )(?v2 B_b_prod_b_b_prod_prod_llist$ ))(= (ldrop$i ?v0 (lzip$h ?v1 ?v2 ))(lzip$h (fun_app$h (ldrop$ ?v0 )?v1 )(fun_app$m (ldrop$a ?v0 )?v2 )))):named a46 ))
(assert (! (forall ((?v0 Enat$ )(?v1 B_b_prod_llist$ )(?v2 B_b_prod_b_prod_llist$ ))(= (ldrop$j ?v0 (lzip$i ?v1 ?v2 ))(lzip$i (fun_app$p (ldrop$d ?v0 )?v1 )(fun_app$n (ldrop$b ?v0 )?v2 )))):named a47 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 B_b_prod_b_b_prod_prod_llist$ ))(= (fun_app$m (ldrop$a ?v0 )(fun_app$m (ldrop$a ?v1 )?v2 ))(fun_app$m (ldrop$a (plus$ ?v0 ?v1 ))?v2 ))):named a48 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 B_b_prod_b_prod_llist$ ))(= (fun_app$n (ldrop$b ?v0 )(fun_app$n (ldrop$b ?v1 )?v2 ))(fun_app$n (ldrop$b (plus$ ?v0 ?v1 ))?v2 ))):named a49 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 B_b_b_prod_prod_llist$ ))(= (fun_app$o (ldrop$c ?v0 )(fun_app$o (ldrop$c ?v1 )?v2 ))(fun_app$o (ldrop$c (plus$ ?v0 ?v1 ))?v2 ))):named a50 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 B_b_prod_llist$ ))(= (fun_app$p (ldrop$d ?v0 )(fun_app$p (ldrop$d ?v1 )?v2 ))(fun_app$p (ldrop$d (plus$ ?v0 ?v1 ))?v2 ))):named a51 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 B_llist$ ))(= (fun_app$h (ldrop$ ?v0 )(fun_app$h (ldrop$ ?v1 )?v2 ))(fun_app$h (ldrop$ (plus$ ?v0 ?v1 ))?v2 ))):named a52 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$m (ldrop$a ?v0 )lNil$b )lNil$b ):pattern ((ldrop$a ?v0 )))):named a53 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$n (ldrop$b ?v0 )lNil$c )lNil$c ):pattern ((ldrop$b ?v0 )))):named a54 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$o (ldrop$c ?v0 )lNil$d )lNil$d ):pattern ((ldrop$c ?v0 )))):named a55 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$p (ldrop$d ?v0 )lNil$e )lNil$e ):pattern ((ldrop$d ?v0 )))):named a56 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$h (ldrop$ ?v0 )lNil$a )lNil$a ):pattern ((ldrop$ ?v0 )))):named a57 ))
(check-sat )
;(get-unsat-core )
