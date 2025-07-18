;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort B_set$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort B_llist_set$ 0 )
(declare-sort B_llist_b_fun$ 0 )
(declare-sort B_llist_bool_fun$ 0 )
(declare-sort A_llist_b_llist_prod_set$ 0 )
(declare-sort A_llist_b_llist_prod_b_llist_fun$ 0 )
(declare-sort B_llist$ 0)
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()B_llist$)
(declare-fun lhd$ (B_llist$)B$)
(declare-fun ltl$ (B_llist$)B_llist$)
(declare-fun lCons$ (B$ B_llist$ )B_llist$)
(declare-fun lNil$a ()A_llist$)
(declare-fun lhd$a (A_llist$)A$)
(declare-fun ltl$a (A_llist$)A_llist$)
(declare-fun lCons$a (A$ A_llist$ )A_llist$)
(declare-datatypes ()((A_llist_b_llist_prod$ (pair$ (fst$ A_llist$ )(snd$ B_llist$ )))))
(declare-fun uu$ ()B_llist_b_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ya$ ()A_llist_b_llist_prod_set$ )
(declare-fun ys$ ()B_llist$ )
(declare-fun inf$ (B_llist_set$ B_llist_set$ )B_llist_set$ )
(declare-fun the$ (B_bool_fun$ )B$ )
(declare-fun uua$ ()A_llist_b_llist_prod_b_llist_fun$ )
(declare-fun uub$ ()B_llist_bool_fun$ )
(declare-fun uuc$ ()B_bool_fun$ )
(declare-fun uud$ (B$ )B_bool_fun$ )
(declare-fun uue$ (B$ )B_bool_fun$ )
(declare-fun inf$a (B_set$ B_set$ )B_set$ )
(declare-fun inf$b (A_llist_b_llist_prod_set$ A_llist_b_llist_prod_set$ )A_llist_b_llist_prod_set$ )
(declare-fun lSup$ (B_llist_set$ )B_llist$ )
(declare-fun image$ (B_llist_b_fun$ B_llist_set$ )B_set$ )
(declare-fun lnull$ (B_llist$ )Bool )
(declare-fun image$a (A_llist_b_llist_prod_b_llist_fun$ A_llist_b_llist_prod_set$ )B_llist_set$ )
(declare-fun member$ (B$ B_set$ )Bool )
(declare-fun collect$ (B_llist_bool_fun$ )B_llist_set$ )
(declare-fun fun_app$ (B_bool_fun$ B$ )Bool )
(declare-fun member$a (B_llist$ B_llist_set$ )Bool )
(declare-fun member$b (A_llist_b_llist_prod$ A_llist_b_llist_prod_set$ )Bool )
(declare-fun fun_app$a (B_llist_bool_fun$ B_llist$ )Bool )
(declare-fun fun_app$b (B_llist_b_fun$ B_llist$ )B$ )
(declare-fun fun_app$c (A_llist_b_llist_prod_b_llist_fun$ A_llist_b_llist_prod$ )B_llist$ )
(assert (! (forall ((?v0 B$ ))(! (= (fun_app$ uuc$ ?v0 )(member$ ?v0 (image$ uu$ (inf$ (image$a uua$ ya$ )(collect$ uub$ ))))):pattern ((fun_app$ uuc$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 B_llist$ ))(! (= (fun_app$a uub$ ?v0 )(not (lnull$ ?v0 ))):pattern ((fun_app$a uub$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 B_llist$ ))(! (= (fun_app$b uu$ ?v0 )(lhd$ ?v0 )):pattern ((fun_app$b uu$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_llist_b_llist_prod$ ))(! (= (fun_app$c uua$ ?v0 )(snd$ ?v0 )):pattern ((fun_app$c uua$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(! (= (fun_app$ (uud$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (uud$ ?v0 )?v1 )))):named a4 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(! (= (fun_app$ (uue$ ?v0 )?v1 )(= ?v1 ?v0 )):pattern ((fun_app$ (uue$ ?v0 )?v1 )))):named a5 ))
(assert (! (not (= (the$ uuc$ )(lhd$ ys$ ))):named a6 ))
(assert (! (not (lnull$ ys$ )):named a7 ))
(assert (! (member$ (lhd$ ys$ )(image$ uu$ (inf$ (image$a uua$ ya$ )(collect$ uub$ )))):named a8 ))
(assert (! (not (lnull$ (lSup$ (image$a uua$ ya$ )))):named a9 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_bool_fun$ ))(=> (and (=> (or (lnull$ ?v0 )(not (fun_app$ ?v1 (lhd$ ?v0 ))))false )(=> (and (not (lnull$ ?v0 ))(fun_app$ ?v1 (lhd$ ?v0 )))false ))false )):named a10 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a11 ))
(assert (! (forall ((?v0 B_llist_set$ ))(=> (and (=> (forall ((?v1 B_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$ ?v1 )))false )(=> (not (forall ((?v1 B_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$ ?v1 ))))false ))false )):named a12 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(=> (and (=> (and (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (or (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a13 ))
(assert (! (forall ((?v0 B_llist$ ))(=> (and (=> (lnull$ ?v0 )false )(=> (not (lnull$ ?v0 ))false ))false )):named a14 ))
(assert (! (forall ((?v0 B$ ))(= (the$ (uud$ ?v0 ))?v0 )):named a15 ))
(assert (! (forall ((?v0 B$ ))(= (the$ (uue$ ?v0 ))?v0 )):named a16 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B$ ))(=> (and (fun_app$ ?v0 ?v1 )(forall ((?v2 B$ ))(=> (fun_app$ ?v0 ?v2 )(= ?v2 ?v1 ))))(= (the$ ?v0 )?v1 ))):named a17 ))
(assert (! (member$b (pair$ xs$ ys$ )ya$ ):named a18 ))
(assert (! (forall ((?v0 B$ )(?v1 B_set$ )(?v2 B_set$ ))(= (member$ ?v0 (inf$a ?v1 ?v2 ))(and (member$ ?v0 ?v1 )(member$ ?v0 ?v2 )))):named a19 ))
(assert (! (forall ((?v0 A_llist_b_llist_prod$ )(?v1 A_llist_b_llist_prod_set$ )(?v2 A_llist_b_llist_prod_set$ ))(= (member$b ?v0 (inf$b ?v1 ?v2 ))(and (member$b ?v0 ?v1 )(member$b ?v0 ?v2 )))):named a20 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist_set$ )(?v2 B_llist_set$ ))(= (member$a ?v0 (inf$ ?v1 ?v2 ))(and (member$a ?v0 ?v1 )(member$a ?v0 ?v2 )))):named a21 ))
(assert (! (forall ((?v0 B$ )(?v1 B_set$ )(?v2 B_set$ ))(=> (and (member$ ?v0 ?v1 )(member$ ?v0 ?v2 ))(member$ ?v0 (inf$a ?v1 ?v2 )))):named a22 ))
(assert (! (forall ((?v0 A_llist_b_llist_prod$ )(?v1 A_llist_b_llist_prod_set$ )(?v2 A_llist_b_llist_prod_set$ ))(=> (and (member$b ?v0 ?v1 )(member$b ?v0 ?v2 ))(member$b ?v0 (inf$b ?v1 ?v2 )))):named a23 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist_set$ )(?v2 B_llist_set$ ))(=> (and (member$a ?v0 ?v1 )(member$a ?v0 ?v2 ))(member$a ?v0 (inf$ ?v1 ?v2 )))):named a24 ))
(assert (! (forall ((?v0 A_llist_b_llist_prod_set$ )(?v1 A_llist_b_llist_prod_set$ ))(= (inf$b (inf$b ?v0 ?v1 )?v1 )(inf$b ?v0 ?v1 ))):named a25 ))
(assert (! (forall ((?v0 B_set$ )(?v1 B_set$ ))(= (inf$a (inf$a ?v0 ?v1 )?v1 )(inf$a ?v0 ?v1 ))):named a26 ))
(assert (! (forall ((?v0 B_llist_set$ )(?v1 B_llist_set$ ))(= (inf$ (inf$ ?v0 ?v1 )?v1 )(inf$ ?v0 ?v1 ))):named a27 ))
(check-sat )
;(get-unsat-core )
