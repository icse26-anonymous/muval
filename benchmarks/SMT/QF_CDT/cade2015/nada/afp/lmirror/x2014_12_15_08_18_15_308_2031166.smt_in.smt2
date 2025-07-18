;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_b_fun$ 0 )
(declare-sort B_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort Enat_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_enat_fun$ 0 )
(declare-sort B_a_bool_fun_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-sort B_llist_bool_fun$ 0 )
(declare-sort B_llist_enat_fun$ 0 )
(declare-sort Enat_enat_bool_fun_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort A_llist_b_llist_bool_fun_fun$ 0 )
(declare-sort B_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort B_llist_b_llist_bool_fun_fun$ 0 )
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
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
(declare-fun p$ ()A_b_bool_fun_fun$ )
(declare-fun uu$ ()Enat_enat_bool_fun_fun$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun acca$ ()A_llist$ )
(declare-fun llcp$ (A_llist$ )A_llist_enat_fun$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun xs_a$ ()B_llist$ )
(declare-fun zero$ ()Nat$ )
(declare-fun acc_a$ ()B_llist$ )
(declare-fun llcp$a (B_llist$ )B_llist_enat_fun$ )
(declare-fun lmap$a (B_a_fun$ B_llist$ )A_llist$ )
(declare-fun lmap$b (A_b_fun$ A_llist$ )B_llist$ )
(declare-fun lmap$c (B_b_fun$ B_llist$ )B_llist$ )
(declare-fun fun_app$ (Enat_bool_fun$ Enat$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llength$ ()A_llist_enat_fun$ )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(declare-fun rel_fun$ (A_llist_a_llist_bool_fun_fun$ Enat_enat_bool_fun_fun$ A_llist_enat_fun$ A_llist_enat_fun$ )Bool )
(declare-fun fun_app$a (Enat_enat_bool_fun_fun$ Enat$ )Enat_bool_fun$ )
(declare-fun fun_app$b (A_llist_enat_fun$ A_llist$ )Enat$ )
(declare-fun fun_app$c (B_llist_enat_fun$ B_llist$ )Enat$ )
(declare-fun fun_app$d (B_llist_bool_fun$ B_llist$ )Bool )
(declare-fun fun_app$e (A_llist_b_llist_bool_fun_fun$ A_llist$ )B_llist_bool_fun$ )
(declare-fun fun_app$f (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$g (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$h (B_llist_a_llist_bool_fun_fun$ B_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$i (B_llist_b_llist_bool_fun_fun$ B_llist$ )B_llist_bool_fun$ )
(declare-fun fun_app$j (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$k (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$l (B_a_bool_fun_fun$ B$ )A_bool_fun$ )
(declare-fun fun_app$m (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$n (B_b_bool_fun_fun$ B$ )B_bool_fun$ )
(declare-fun fun_app$o (A_b_bool_fun_fun$ A$ )B_bool_fun$ )
(declare-fun lfinite$a (B_llist$ )Bool )
(declare-fun llength$a ()B_llist_enat_fun$ )
(declare-fun lprefix$a (B_llist$ B_llist$ )Bool )
(declare-fun rel_fun$a (B_llist_a_llist_bool_fun_fun$ Enat_enat_bool_fun_fun$ B_llist_enat_fun$ A_llist_enat_fun$ )Bool )
(declare-fun rel_fun$b (B_llist_b_llist_bool_fun_fun$ Enat_enat_bool_fun_fun$ B_llist_enat_fun$ B_llist_enat_fun$ )Bool )
(declare-fun rel_fun$c (A_llist_b_llist_bool_fun_fun$ Enat_enat_bool_fun_fun$ A_llist_enat_fun$ B_llist_enat_fun$ )Bool )
(declare-fun llist_all2$ (A_b_bool_fun_fun$ )A_llist_b_llist_bool_fun_fun$ )
(declare-fun ltakeWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun gen_llength$ (Nat$ )A_llist_enat_fun$ )
(declare-fun llist_all2$a (A_a_bool_fun_fun$ )A_llist_a_llist_bool_fun_fun$ )
(declare-fun llist_all2$b (B_a_bool_fun_fun$ )B_llist_a_llist_bool_fun_fun$ )
(declare-fun llist_all2$c (B_b_bool_fun_fun$ )B_llist_b_llist_bool_fun_fun$ )
(declare-fun lmirror_aux$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun ltakeWhile$a (B_bool_fun$ B_llist$ )B_llist$ )
(declare-fun gen_llength$a (Nat$ )B_llist_enat_fun$ )
(declare-fun lmirror_aux$a (B_llist$ B_llist$ )B_llist$ )
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(! (= (fun_app$ (fun_app$a uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (fun_app$a uu$ ?v0 )?v1 )))):named a0 ))
(assert (! (not (= (fun_app$b llength$ acca$ )(fun_app$c llength$a acc_a$ ))):named a1 ))
(assert (! (fun_app$d (fun_app$e (llist_all2$ p$ )acca$ )acc_a$ ):named a2 ))
(assert (! (lfinite$ acca$ ):named a3 ))
(assert (! (= (fun_app$b llength$ (lmirror_aux$ acca$ xsa$ ))(fun_app$c llength$a (lmirror_aux$a acc_a$ xs_a$ ))):named a4 ))
(assert (! (fun_app$d (fun_app$e (llist_all2$ p$ )(lmirror_aux$ acca$ xsa$ ))(lmirror_aux$a acc_a$ xs_a$ )):named a5 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (fun_app$f (fun_app$g (llist_all2$a ?v0 )?v1 )?v2 )(= (fun_app$b llength$ ?v1 )(fun_app$b llength$ ?v2 )))):named a6 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_llist$ ))(=> (fun_app$f (fun_app$h (llist_all2$b ?v0 )?v1 )?v2 )(= (fun_app$c llength$a ?v1 )(fun_app$b llength$ ?v2 )))):named a7 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ ))(=> (fun_app$d (fun_app$i (llist_all2$c ?v0 )?v1 )?v2 )(= (fun_app$c llength$a ?v1 )(fun_app$c llength$a ?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B_llist$ ))(=> (fun_app$d (fun_app$e (llist_all2$ ?v0 )?v1 )?v2 )(= (fun_app$b llength$ ?v1 )(fun_app$c llength$a ?v2 )))):named a9 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$b (llcp$ ?v0 )?v0 )(fun_app$b llength$ ?v0 )):pattern ((llcp$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 B_llist$ ))(! (= (fun_app$c (llcp$a ?v0 )?v0 )(fun_app$c llength$a ?v0 )):pattern ((llcp$a ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (fun_app$b llength$ (lmap$ ?v0 ?v1 ))(fun_app$b llength$ ?v1 ))):named a12 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_llist$ ))(= (fun_app$b llength$ (lmap$a ?v0 ?v1 ))(fun_app$c llength$a ?v1 ))):named a13 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_llist$ ))(= (fun_app$c llength$a (lmap$b ?v0 ?v1 ))(fun_app$b llength$ ?v1 ))):named a14 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_llist$ ))(= (fun_app$c llength$a (lmap$c ?v0 ?v1 ))(fun_app$c llength$a ?v1 ))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (lprefix$ ?v0 ?v1 )(= (fun_app$b llength$ ?v0 )(fun_app$b llength$ ?v1 )))(= ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(=> (and (lprefix$a ?v0 ?v1 )(= (fun_app$c llength$a ?v0 )(fun_app$c llength$a ?v1 )))(= ?v0 ?v1 ))):named a17 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (= (fun_app$b llength$ (ltakeWhile$ ?v0 ?v1 ))(fun_app$b llength$ ?v1 ))(= (ltakeWhile$ ?v0 ?v1 )?v1 ))):named a18 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_llist$ ))(= (= (fun_app$c llength$a (ltakeWhile$a ?v0 ?v1 ))(fun_app$c llength$a ?v1 ))(= (ltakeWhile$a ?v0 ?v1 )?v1 ))):named a19 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_bool_fun$ )(?v4 A_bool_fun$ ))(=> (and (fun_app$f (fun_app$g (llist_all2$a ?v0 )?v1 )?v2 )(forall ((?v5 A$ )(?v6 A$ ))(=> (fun_app$j (fun_app$k ?v0 ?v5 )?v6 )(= (fun_app$j ?v3 ?v5 )(fun_app$j ?v4 ?v6 )))))(= (fun_app$b llength$ (ltakeWhile$ ?v3 ?v1 ))(fun_app$b llength$ (ltakeWhile$ ?v4 ?v2 ))))):named a20 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_llist$ )(?v3 B_bool_fun$ )(?v4 A_bool_fun$ ))(=> (and (fun_app$f (fun_app$h (llist_all2$b ?v0 )?v1 )?v2 )(forall ((?v5 B$ )(?v6 A$ ))(=> (fun_app$j (fun_app$l ?v0 ?v5 )?v6 )(= (fun_app$m ?v3 ?v5 )(fun_app$j ?v4 ?v6 )))))(= (fun_app$c llength$a (ltakeWhile$a ?v3 ?v1 ))(fun_app$b llength$ (ltakeWhile$ ?v4 ?v2 ))))):named a21 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ )(?v3 B_bool_fun$ )(?v4 B_bool_fun$ ))(=> (and (fun_app$d (fun_app$i (llist_all2$c ?v0 )?v1 )?v2 )(forall ((?v5 B$ )(?v6 B$ ))(=> (fun_app$m (fun_app$n ?v0 ?v5 )?v6 )(= (fun_app$m ?v3 ?v5 )(fun_app$m ?v4 ?v6 )))))(= (fun_app$c llength$a (ltakeWhile$a ?v3 ?v1 ))(fun_app$c llength$a (ltakeWhile$a ?v4 ?v2 ))))):named a22 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B_llist$ )(?v3 A_bool_fun$ )(?v4 B_bool_fun$ ))(=> (and (fun_app$d (fun_app$e (llist_all2$ ?v0 )?v1 )?v2 )(forall ((?v5 A$ )(?v6 B$ ))(=> (fun_app$m (fun_app$o ?v0 ?v5 )?v6 )(= (fun_app$j ?v3 ?v5 )(fun_app$m ?v4 ?v6 )))))(= (fun_app$b llength$ (ltakeWhile$ ?v3 ?v1 ))(fun_app$c llength$a (ltakeWhile$a ?v4 ?v2 ))))):named a23 ))
(assert (! (= llength$ (gen_llength$ zero$ )):named a24 ))
(assert (! (= llength$a (gen_llength$a zero$ )):named a25 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ ))(rel_fun$ (llist_all2$a ?v0 )uu$ llength$ llength$ )):named a26 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ ))(rel_fun$a (llist_all2$b ?v0 )uu$ llength$a llength$ )):named a27 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ ))(rel_fun$b (llist_all2$c ?v0 )uu$ llength$a llength$a )):named a28 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ ))(rel_fun$c (llist_all2$ ?v0 )uu$ llength$ llength$a )):named a29 ))
(assert (! (forall ((?v0 B_llist$ ))(lprefix$a ?v0 ?v0 )):named a30 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a31 ))
(assert (! (forall ((?v0 B_llist$ ))(lprefix$a ?v0 ?v0 )):named a32 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a33 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_llist$ ))(= (lfinite$a (lmap$c ?v0 ?v1 ))(lfinite$a ?v1 ))):named a34 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_llist$ ))(= (lfinite$a (lmap$b ?v0 ?v1 ))(lfinite$ ?v1 ))):named a35 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_llist$ ))(= (lfinite$ (lmap$a ?v0 ?v1 ))(lfinite$a ?v1 ))):named a36 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (lfinite$ (lmap$ ?v0 ?v1 ))(lfinite$ ?v1 ))):named a37 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (lmirror_aux$ ?v0 ?v1 ))(and (lfinite$ ?v1 )(lfinite$ ?v0 )))):named a38 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(= (lfinite$a (lmirror_aux$a ?v0 ?v1 ))(and (lfinite$a ?v1 )(lfinite$a ?v0 )))):named a39 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (lprefix$ ?v0 ?v1 )(= (fun_app$b (llcp$ ?v1 )?v0 )(fun_app$b llength$ ?v0 ))):pattern ((fun_app$b (llcp$ ?v1 )?v0 )))):named a40 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(! (=> (lprefix$a ?v0 ?v1 )(= (fun_app$c (llcp$a ?v1 )?v0 )(fun_app$c llength$a ?v0 ))):pattern ((fun_app$c (llcp$a ?v1 )?v0 )))):named a41 ))
(check-sat )
;(get-unsat-core )
