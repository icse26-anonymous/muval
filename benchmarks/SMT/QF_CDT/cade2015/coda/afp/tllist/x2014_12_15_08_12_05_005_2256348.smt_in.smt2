;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort C$ 0 )
(declare-sort D$ 0 )
(declare-sort A_set$ 0 )
(declare-sort C_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_b_fun$ 0 )
(declare-sort C_c_fun$ 0 )
(declare-sort C_d_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort C_bool_fun$ 0 )
(declare-sort D_bool_fun$ 0 )
(declare-sort A_b_prod_set$ 0 )
(declare-sort C_d_prod_set$ 0 )
(declare-sort A_a_b_prod_fun$ 0 )
(declare-sort A_b_prod_a_fun$ 0 )
(declare-sort C_c_d_prod_fun$ 0 )
(declare-sort C_d_prod_c_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort C_d_bool_fun_fun$ 0 )
(declare-sort A_b_prod_bool_fun$ 0 )
(declare-sort C_d_prod_bool_fun$ 0 )
(declare-sort A_c_tllist_bool_fun$ 0 )
(declare-sort A_b_prod_a_b_prod_fun$ 0 )
(declare-sort C_d_prod_c_d_prod_fun$ 0 )
(declare-sort A_b_prod_c_d_prod_tllist_set$ 0 )
(declare-sort A_b_prod_c_d_prod_tllist_bool_fun$ 0 )
(declare-sort A_b_prod_c_d_prod_tllist_a_c_tllist_fun$ 0 )
(declare-sort A_b_prod_c_d_prod_tllist_a_c_tllist_prod_set$ 0 )
(declare-sort A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ 0 )
(declare-sort A_c_tllist_a_b_prod_c_d_prod_tllist_bool_fun_fun$ 0 )
(declare-sort A_b_prod_c_d_prod_tllist_a_c_tllist_prod_bool_fun$ 0 )
(declare-sort C_d_prod_c_fun_a_b_prod_c_d_prod_tllist_a_c_tllist_fun_fun$ 0 )
(declare-sort A_b_prod$ 0)
(declare-sort C_d_prod$ 0)
(declare-fun fst$ (A_b_prod$)A$)
(declare-fun snd$ (A_b_prod$)B$)
(declare-fun pair$ (A$ B$ )A_b_prod$)
(declare-fun fst$a (C_d_prod$)C$)
(declare-fun snd$a (C_d_prod$)D$)
(declare-fun pair$a (C$ D$ )C_d_prod$)
(declare-codatatypes ()((A_b_prod_c_d_prod_tllist$ (tNil$ (terminal$ C_d_prod$ ))(tCons$ (thd$ A_b_prod$ )(ttl$ A_b_prod_c_d_prod_tllist$ )))(A_c_tllist$ (tNil$a (terminal$a C$ ))(tCons$a (thd$a A$ )(ttl$a A_c_tllist$ )))(A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))(A_b_prod_llist$ (lNil$a )(lCons$a (lhd$a A_b_prod$ )(ltl$a A_b_prod_llist$ )))))
(declare-sort A_b_prod_c_d_prod_tllist_a_c_tllist_prod$ 0)
(declare-fun fst$b (A_b_prod_c_d_prod_tllist_a_c_tllist_prod$)A_b_prod_c_d_prod_tllist$)
(declare-fun snd$b (A_b_prod_c_d_prod_tllist_a_c_tllist_prod$)A_c_tllist$)
(declare-fun pair$b (A_b_prod_c_d_prod_tllist$ A_c_tllist$ )A_b_prod_c_d_prod_tllist_a_c_tllist_prod$)
(declare-fun b$ ()C$ )
(declare-fun y$ ()A_b_bool_fun_fun$ )
(declare-fun ba$ ()D$ )
(declare-fun bb$ ()A_b_prod_llist$ )
(declare-fun uu$ ()A_b_prod_c_d_prod_tllist_bool_fun$ )
(declare-fun ya$ ()C_d_bool_fun_fun$ )
(declare-fun grp$ (A_b_prod_c_d_prod_tllist_set$ A_b_prod_c_d_prod_tllist_a_c_tllist_fun$ )A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )
(declare-fun uua$ ()A_b_prod_a_fun$ )
(declare-fun uub$ ()C_d_prod_c_fun$ )
(declare-fun uuc$ ()A_b_prod_a_b_prod_fun$ )
(declare-fun uud$ ()C_d_prod_c_d_prod_fun$ )
(declare-fun uue$ ()A_a_fun$ )
(declare-fun uuf$ ()C_c_fun$ )
(declare-fun uug$ (Bool A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )
(declare-fun uuh$ (Bool A_b_bool_fun_fun$ )A_b_bool_fun_fun$ )
(declare-fun uui$ (Bool C_d_bool_fun_fun$ )C_d_bool_fun_fun$ )
(declare-fun grp$a (A_set$ A_b_fun$ )A_b_bool_fun_fun$ )
(declare-fun grp$b (C_set$ C_d_fun$ )C_d_bool_fun_fun$ )
(declare-fun lmap$ (A_b_prod_a_fun$ A_b_prod_llist$ )A_llist$ )
(declare-fun lset$ (A_b_prod_llist$ )A_b_prod_set$ )
(declare-fun tmap$ (A_b_prod_a_fun$ )C_d_prod_c_fun_a_b_prod_c_d_prod_tllist_a_c_tllist_fun_fun$ )
(declare-fun tset$ (A_b_prod_c_d_prod_tllist$ )A_b_prod_set$ )
(declare-fun lmap$a (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun lmap$b (A_a_b_prod_fun$ A_llist$ )A_b_prod_llist$ )
(declare-fun lmap$c (A_b_prod_a_b_prod_fun$ A_b_prod_llist$ )A_b_prod_llist$ )
(declare-fun lset$a (A_llist$ )A_set$ )
(declare-fun tmap$a (A_a_fun$ C_c_fun$ A_c_tllist$ )A_c_tllist$ )
(declare-fun tmap$b (A_a_b_prod_fun$ C_c_d_prod_fun$ A_c_tllist$ )A_b_prod_c_d_prod_tllist$ )
(declare-fun tmap$c (A_b_prod_a_b_prod_fun$ C_d_prod_c_d_prod_fun$ A_b_prod_c_d_prod_tllist$ )A_b_prod_c_d_prod_tllist$ )
(declare-fun tset$a (A_c_tllist$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun collect$ (A_b_prod_bool_fun$ )A_b_prod_set$ )
(declare-fun fun_app$ (A_b_prod_c_d_prod_tllist_bool_fun$ A_b_prod_c_d_prod_tllist$ )Bool )
(declare-fun less_eq$ (A_b_prod_set$ A_b_prod_set$ )Bool )
(declare-fun member$a (C$ C_set$ )Bool )
(declare-fun member$b (A_b_prod$ A_b_prod_set$ )Bool )
(declare-fun member$c (C_d_prod$ C_d_prod_set$ )Bool )
(declare-fun member$d (A_b_prod_c_d_prod_tllist_a_c_tllist_prod$ A_b_prod_c_d_prod_tllist_a_c_tllist_prod_set$ )Bool )
(declare-fun member$e (A_b_prod_c_d_prod_tllist$ A_b_prod_c_d_prod_tllist_set$ )Bool )
(declare-fun collect$a (C_d_prod_bool_fun$ )C_d_prod_set$ )
(declare-fun collect$b (A_b_prod_c_d_prod_tllist_bool_fun$ )A_b_prod_c_d_prod_tllist_set$ )
(declare-fun collect$c (A_b_prod_c_d_prod_tllist_a_c_tllist_prod_bool_fun$ )A_b_prod_c_d_prod_tllist_a_c_tllist_prod_set$ )
(declare-fun fun_app$a (C_d_prod_c_fun$ C_d_prod$ )C$ )
(declare-fun fun_app$b (A_b_prod_a_fun$ A_b_prod$ )A$ )
(declare-fun fun_app$c (A_c_tllist_bool_fun$ A_c_tllist$ )Bool )
(declare-fun fun_app$d (A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ A_b_prod_c_d_prod_tllist$ )A_c_tllist_bool_fun$ )
(declare-fun fun_app$e (D_bool_fun$ D$ )Bool )
(declare-fun fun_app$f (C_d_bool_fun_fun$ C$ )D_bool_fun$ )
(declare-fun fun_app$g (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$h (A_b_bool_fun_fun$ A$ )B_bool_fun$ )
(declare-fun fun_app$i (C_d_prod_c_d_prod_fun$ C_d_prod$ )C_d_prod$ )
(declare-fun fun_app$j (A_b_prod_a_b_prod_fun$ A_b_prod$ )A_b_prod$ )
(declare-fun fun_app$k (C_c_fun$ C$ )C$ )
(declare-fun fun_app$l (A_a_fun$ A$ )A$ )
(declare-fun fun_app$m (A_c_tllist_a_b_prod_c_d_prod_tllist_bool_fun_fun$ A_c_tllist$ )A_b_prod_c_d_prod_tllist_bool_fun$ )
(declare-fun fun_app$n (C_d_prod_c_fun_a_b_prod_c_d_prod_tllist_a_c_tllist_fun_fun$ C_d_prod_c_fun$ )A_b_prod_c_d_prod_tllist_a_c_tllist_fun$ )
(declare-fun fun_app$o (C_c_d_prod_fun$ C$ )C_d_prod$ )
(declare-fun fun_app$p (A_b_prod_c_d_prod_tllist_a_c_tllist_fun$ A_b_prod_c_d_prod_tllist$ )A_c_tllist$ )
(declare-fun fun_app$q (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$r (C_bool_fun$ C$ )Bool )
(declare-fun fun_app$s (A_a_b_prod_fun$ A$ )A_b_prod$ )
(declare-fun fun_app$t (A_b_prod_c_d_prod_tllist_a_c_tllist_prod_bool_fun$ A_b_prod_c_d_prod_tllist_a_c_tllist_prod$ )Bool )
(declare-fun fun_app$u (A_b_prod_bool_fun$ A_b_prod$ )Bool )
(declare-fun fun_app$v (C_d_prod_bool_fun$ C_d_prod$ )Bool )
(declare-fun less_eq$a (C_d_prod_set$ C_d_prod_set$ )Bool )
(declare-fun case_prod$ (A_b_bool_fun_fun$ )A_b_prod_bool_fun$ )
(declare-fun conversep$ (A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )A_c_tllist_a_b_prod_c_d_prod_tllist_bool_fun_fun$ )
(declare-fun case_prod$a (C_d_bool_fun_fun$ )C_d_prod_bool_fun$ )
(declare-fun case_prod$b (A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )A_b_prod_c_d_prod_tllist_a_c_tllist_prod_bool_fun$ )
(declare-fun set2_tllist$ (A_b_prod_c_d_prod_tllist$ )C_d_prod_set$ )
(declare-fun set2_tllist$a (A_c_tllist$ )C_set$ )
(declare-fun tllist_of_llist$ (C$ A_llist$ )A_c_tllist$ )
(declare-fun tllist_of_llist$a (C_d_prod$ A_b_prod_llist$ )A_b_prod_c_d_prod_tllist$ )
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist$ ))(! (= (fun_app$ uu$ ?v0 )(and (less_eq$ (tset$ ?v0 )(collect$ (case_prod$ y$ )))(less_eq$a (set2_tllist$ ?v0 )(collect$a (case_prod$a ya$ ))))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 C_d_prod$ ))(! (= (fun_app$a uub$ ?v0 )(fst$a ?v0 )):pattern ((fun_app$a uub$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_b_prod$ ))(! (= (fun_app$b uua$ ?v0 )(fst$ ?v0 )):pattern ((fun_app$b uua$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 Bool )(?v1 A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )(?v2 A_b_prod_c_d_prod_tllist$ )(?v3 A_c_tllist$ ))(! (= (fun_app$c (fun_app$d (uug$ ?v0 ?v1 )?v2 )?v3 )(and ?v0 (fun_app$c (fun_app$d ?v1 ?v2 )?v3 ))):pattern ((fun_app$c (fun_app$d (uug$ ?v0 ?v1 )?v2 )?v3 )))):named a3 ))
(assert (! (forall ((?v0 Bool )(?v1 C_d_bool_fun_fun$ )(?v2 C$ )(?v3 D$ ))(! (= (fun_app$e (fun_app$f (uui$ ?v0 ?v1 )?v2 )?v3 )(and ?v0 (fun_app$e (fun_app$f ?v1 ?v2 )?v3 ))):pattern ((fun_app$e (fun_app$f (uui$ ?v0 ?v1 )?v2 )?v3 )))):named a4 ))
(assert (! (forall ((?v0 Bool )(?v1 A_b_bool_fun_fun$ )(?v2 A$ )(?v3 B$ ))(! (= (fun_app$g (fun_app$h (uuh$ ?v0 ?v1 )?v2 )?v3 )(and ?v0 (fun_app$g (fun_app$h ?v1 ?v2 )?v3 ))):pattern ((fun_app$g (fun_app$h (uuh$ ?v0 ?v1 )?v2 )?v3 )))):named a5 ))
(assert (! (forall ((?v0 C_d_prod$ ))(! (= (fun_app$i uud$ ?v0 )?v0 ):pattern ((fun_app$i uud$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_b_prod$ ))(! (= (fun_app$j uuc$ ?v0 )?v0 ):pattern ((fun_app$j uuc$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 C$ ))(! (= (fun_app$k uuf$ ?v0 )?v0 ):pattern ((fun_app$k uuf$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$l uue$ ?v0 )?v0 ):pattern ((fun_app$l uue$ ?v0 )))):named a9 ))
(assert (! (not (fun_app$ (fun_app$m (conversep$ (grp$ (collect$b uu$ )(fun_app$n (tmap$ uua$ )uub$ )))(tllist_of_llist$ b$ (lmap$ uua$ bb$ )))(tllist_of_llist$a (pair$a b$ ba$ )bb$ ))):named a10 ))
(assert (! (less_eq$ (lset$ bb$ )(collect$ (case_prod$ y$ ))):named a11 ))
(assert (! (fun_app$e (fun_app$f ya$ b$ )ba$ ):named a12 ))
(assert (! (forall ((?v0 C$ )(?v1 A_llist$ ))(= (tset$a (tllist_of_llist$ ?v0 ?v1 ))(lset$a ?v1 ))):named a13 ))
(assert (! (forall ((?v0 C_d_prod$ )(?v1 A_b_prod_llist$ ))(= (tset$ (tllist_of_llist$a ?v0 ?v1 ))(lset$ ?v1 ))):named a14 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 C_c_fun$ )(?v2 C$ )(?v3 A_llist$ ))(= (tmap$a ?v0 ?v1 (tllist_of_llist$ ?v2 ?v3 ))(tllist_of_llist$ (fun_app$k ?v1 ?v2 )(lmap$a ?v0 ?v3 )))):named a15 ))
(assert (! (forall ((?v0 A_a_b_prod_fun$ )(?v1 C_c_d_prod_fun$ )(?v2 C$ )(?v3 A_llist$ ))(= (tmap$b ?v0 ?v1 (tllist_of_llist$ ?v2 ?v3 ))(tllist_of_llist$a (fun_app$o ?v1 ?v2 )(lmap$b ?v0 ?v3 )))):named a16 ))
(assert (! (forall ((?v0 A_b_prod_a_fun$ )(?v1 C_d_prod_c_fun$ )(?v2 C_d_prod$ )(?v3 A_b_prod_llist$ ))(= (fun_app$p (fun_app$n (tmap$ ?v0 )?v1 )(tllist_of_llist$a ?v2 ?v3 ))(tllist_of_llist$ (fun_app$a ?v1 ?v2 )(lmap$ ?v0 ?v3 )))):named a17 ))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_fun$ )(?v1 C_d_prod_c_d_prod_fun$ )(?v2 C_d_prod$ )(?v3 A_b_prod_llist$ ))(= (tmap$c ?v0 ?v1 (tllist_of_llist$a ?v2 ?v3 ))(tllist_of_llist$a (fun_app$i ?v1 ?v2 )(lmap$c ?v0 ?v3 )))):named a18 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist_bool_fun$ )(?v1 A_b_prod_c_d_prod_tllist_a_c_tllist_prod$ ))(= (fun_app$ ?v0 (fst$b ?v1 ))(forall ((?v2 A_b_prod_c_d_prod_tllist$ )(?v3 A_c_tllist$ ))(=> (= ?v1 (pair$b ?v2 ?v3 ))(fun_app$ ?v0 ?v2 ))))):named a19 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_b_prod$ ))(= (fun_app$q ?v0 (fst$ ?v1 ))(forall ((?v2 A$ )(?v3 B$ ))(=> (= ?v1 (pair$ ?v2 ?v3 ))(fun_app$q ?v0 ?v2 ))))):named a20 ))
(assert (! (forall ((?v0 C_bool_fun$ )(?v1 C_d_prod$ ))(= (fun_app$r ?v0 (fst$a ?v1 ))(forall ((?v2 C$ )(?v3 D$ ))(=> (= ?v1 (pair$a ?v2 ?v3 ))(fun_app$r ?v0 ?v2 ))))):named a21 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist_bool_fun$ )(?v1 A_b_prod_c_d_prod_tllist_a_c_tllist_prod$ ))(= (fun_app$ ?v0 (fst$b ?v1 ))(not (exists ((?v2 A_b_prod_c_d_prod_tllist$ )(?v3 A_c_tllist$ ))(and (= ?v1 (pair$b ?v2 ?v3 ))(not (fun_app$ ?v0 ?v2 ))))))):named a22 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_b_prod$ ))(= (fun_app$q ?v0 (fst$ ?v1 ))(not (exists ((?v2 A$ )(?v3 B$ ))(and (= ?v1 (pair$ ?v2 ?v3 ))(not (fun_app$q ?v0 ?v2 ))))))):named a23 ))
(assert (! (forall ((?v0 C_bool_fun$ )(?v1 C_d_prod$ ))(= (fun_app$r ?v0 (fst$a ?v1 ))(not (exists ((?v2 C$ )(?v3 D$ ))(and (= ?v1 (pair$a ?v2 ?v3 ))(not (fun_app$r ?v0 ?v2 ))))))):named a24 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist$ ))(= (tmap$c uuc$ uud$ ?v0 )?v0 )):named a25 ))
(assert (! (forall ((?v0 A_c_tllist$ ))(= (tmap$a uue$ uuf$ ?v0 )?v0 )):named a26 ))
(assert (! (forall ((?v0 A_c_tllist$ )(?v1 A_c_tllist$ )(?v2 A_a_b_prod_fun$ )(?v3 A_a_b_prod_fun$ )(?v4 C_c_d_prod_fun$ )(?v5 C_c_d_prod_fun$ ))(=> (and (forall ((?v6 A$ )(?v7 A$ ))(=> (and (member$ ?v6 (tset$a ?v0 ))(and (member$ ?v7 (tset$a ?v1 ))(= (fun_app$s ?v2 ?v6 )(fun_app$s ?v3 ?v7 ))))(= ?v6 ?v7 )))(and (forall ((?v6 C$ )(?v7 C$ ))(=> (and (member$a ?v6 (set2_tllist$a ?v0 ))(and (member$a ?v7 (set2_tllist$a ?v1 ))(= (fun_app$o ?v4 ?v6 )(fun_app$o ?v5 ?v7 ))))(= ?v6 ?v7 )))(= (tmap$b ?v2 ?v4 ?v0 )(tmap$b ?v3 ?v5 ?v1 ))))(= ?v0 ?v1 ))):named a27 ))
(assert (! (forall ((?v0 A_c_tllist$ )(?v1 A_c_tllist$ )(?v2 A_a_fun$ )(?v3 A_a_fun$ )(?v4 C_c_fun$ )(?v5 C_c_fun$ ))(=> (and (forall ((?v6 A$ )(?v7 A$ ))(=> (and (member$ ?v6 (tset$a ?v0 ))(and (member$ ?v7 (tset$a ?v1 ))(= (fun_app$l ?v2 ?v6 )(fun_app$l ?v3 ?v7 ))))(= ?v6 ?v7 )))(and (forall ((?v6 C$ )(?v7 C$ ))(=> (and (member$a ?v6 (set2_tllist$a ?v0 ))(and (member$a ?v7 (set2_tllist$a ?v1 ))(= (fun_app$k ?v4 ?v6 )(fun_app$k ?v5 ?v7 ))))(= ?v6 ?v7 )))(= (tmap$a ?v2 ?v4 ?v0 )(tmap$a ?v3 ?v5 ?v1 ))))(= ?v0 ?v1 ))):named a28 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist$ )(?v1 A_b_prod_c_d_prod_tllist$ )(?v2 A_b_prod_a_b_prod_fun$ )(?v3 A_b_prod_a_b_prod_fun$ )(?v4 C_d_prod_c_d_prod_fun$ )(?v5 C_d_prod_c_d_prod_fun$ ))(=> (and (forall ((?v6 A_b_prod$ )(?v7 A_b_prod$ ))(=> (and (member$b ?v6 (tset$ ?v0 ))(and (member$b ?v7 (tset$ ?v1 ))(= (fun_app$j ?v2 ?v6 )(fun_app$j ?v3 ?v7 ))))(= ?v6 ?v7 )))(and (forall ((?v6 C_d_prod$ )(?v7 C_d_prod$ ))(=> (and (member$c ?v6 (set2_tllist$ ?v0 ))(and (member$c ?v7 (set2_tllist$ ?v1 ))(= (fun_app$i ?v4 ?v6 )(fun_app$i ?v5 ?v7 ))))(= ?v6 ?v7 )))(= (tmap$c ?v2 ?v4 ?v0 )(tmap$c ?v3 ?v5 ?v1 ))))(= ?v0 ?v1 ))):named a29 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist$ )(?v1 A_b_prod_c_d_prod_tllist$ )(?v2 A_b_prod_a_fun$ )(?v3 A_b_prod_a_fun$ )(?v4 C_d_prod_c_fun$ )(?v5 C_d_prod_c_fun$ ))(=> (and (forall ((?v6 A_b_prod$ )(?v7 A_b_prod$ ))(=> (and (member$b ?v6 (tset$ ?v0 ))(and (member$b ?v7 (tset$ ?v1 ))(= (fun_app$b ?v2 ?v6 )(fun_app$b ?v3 ?v7 ))))(= ?v6 ?v7 )))(and (forall ((?v6 C_d_prod$ )(?v7 C_d_prod$ ))(=> (and (member$c ?v6 (set2_tllist$ ?v0 ))(and (member$c ?v7 (set2_tllist$ ?v1 ))(= (fun_app$a ?v4 ?v6 )(fun_app$a ?v5 ?v7 ))))(= ?v6 ?v7 )))(= (fun_app$p (fun_app$n (tmap$ ?v2 )?v4 )?v0 )(fun_app$p (fun_app$n (tmap$ ?v3 )?v5 )?v1 ))))(= ?v0 ?v1 ))):named a30 ))
(assert (! (forall ((?v0 A_c_tllist$ )(?v1 A_a_b_prod_fun$ )(?v2 A_a_b_prod_fun$ )(?v3 C_c_d_prod_fun$ )(?v4 C_c_d_prod_fun$ ))(=> (and (forall ((?v5 A$ ))(=> (member$ ?v5 (tset$a ?v0 ))(= (fun_app$s ?v1 ?v5 )(fun_app$s ?v2 ?v5 ))))(forall ((?v5 C$ ))(=> (member$a ?v5 (set2_tllist$a ?v0 ))(= (fun_app$o ?v3 ?v5 )(fun_app$o ?v4 ?v5 )))))(= (tmap$b ?v1 ?v3 ?v0 )(tmap$b ?v2 ?v4 ?v0 )))):named a31 ))
(assert (! (forall ((?v0 A_c_tllist$ )(?v1 A_a_fun$ )(?v2 A_a_fun$ )(?v3 C_c_fun$ )(?v4 C_c_fun$ ))(=> (and (forall ((?v5 A$ ))(=> (member$ ?v5 (tset$a ?v0 ))(= (fun_app$l ?v1 ?v5 )(fun_app$l ?v2 ?v5 ))))(forall ((?v5 C$ ))(=> (member$a ?v5 (set2_tllist$a ?v0 ))(= (fun_app$k ?v3 ?v5 )(fun_app$k ?v4 ?v5 )))))(= (tmap$a ?v1 ?v3 ?v0 )(tmap$a ?v2 ?v4 ?v0 )))):named a32 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist$ )(?v1 A_b_prod_a_b_prod_fun$ )(?v2 A_b_prod_a_b_prod_fun$ )(?v3 C_d_prod_c_d_prod_fun$ )(?v4 C_d_prod_c_d_prod_fun$ ))(=> (and (forall ((?v5 A_b_prod$ ))(=> (member$b ?v5 (tset$ ?v0 ))(= (fun_app$j ?v1 ?v5 )(fun_app$j ?v2 ?v5 ))))(forall ((?v5 C_d_prod$ ))(=> (member$c ?v5 (set2_tllist$ ?v0 ))(= (fun_app$i ?v3 ?v5 )(fun_app$i ?v4 ?v5 )))))(= (tmap$c ?v1 ?v3 ?v0 )(tmap$c ?v2 ?v4 ?v0 )))):named a33 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist$ )(?v1 A_b_prod_a_fun$ )(?v2 A_b_prod_a_fun$ )(?v3 C_d_prod_c_fun$ )(?v4 C_d_prod_c_fun$ ))(=> (and (forall ((?v5 A_b_prod$ ))(=> (member$b ?v5 (tset$ ?v0 ))(= (fun_app$b ?v1 ?v5 )(fun_app$b ?v2 ?v5 ))))(forall ((?v5 C_d_prod$ ))(=> (member$c ?v5 (set2_tllist$ ?v0 ))(= (fun_app$a ?v3 ?v5 )(fun_app$a ?v4 ?v5 )))))(= (fun_app$p (fun_app$n (tmap$ ?v1 )?v3 )?v0 )(fun_app$p (fun_app$n (tmap$ ?v2 )?v4 )?v0 )))):named a34 ))
(assert (! (forall ((?v0 A_c_tllist$ )(?v1 A_c_tllist$ )(?v2 A_a_b_prod_fun$ )(?v3 A_a_b_prod_fun$ )(?v4 C_c_d_prod_fun$ )(?v5 C_c_d_prod_fun$ ))(=> (and (= ?v0 ?v1 )(and (forall ((?v6 A$ ))(=> (member$ ?v6 (tset$a ?v1 ))(= (fun_app$s ?v2 ?v6 )(fun_app$s ?v3 ?v6 ))))(forall ((?v6 C$ ))(=> (member$a ?v6 (set2_tllist$a ?v1 ))(= (fun_app$o ?v4 ?v6 )(fun_app$o ?v5 ?v6 ))))))(= (tmap$b ?v2 ?v4 ?v0 )(tmap$b ?v3 ?v5 ?v1 )))):named a35 ))
(assert (! (forall ((?v0 A_c_tllist$ )(?v1 A_c_tllist$ )(?v2 A_a_fun$ )(?v3 A_a_fun$ )(?v4 C_c_fun$ )(?v5 C_c_fun$ ))(=> (and (= ?v0 ?v1 )(and (forall ((?v6 A$ ))(=> (member$ ?v6 (tset$a ?v1 ))(= (fun_app$l ?v2 ?v6 )(fun_app$l ?v3 ?v6 ))))(forall ((?v6 C$ ))(=> (member$a ?v6 (set2_tllist$a ?v1 ))(= (fun_app$k ?v4 ?v6 )(fun_app$k ?v5 ?v6 ))))))(= (tmap$a ?v2 ?v4 ?v0 )(tmap$a ?v3 ?v5 ?v1 )))):named a36 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist$ )(?v1 A_b_prod_c_d_prod_tllist$ )(?v2 A_b_prod_a_b_prod_fun$ )(?v3 A_b_prod_a_b_prod_fun$ )(?v4 C_d_prod_c_d_prod_fun$ )(?v5 C_d_prod_c_d_prod_fun$ ))(=> (and (= ?v0 ?v1 )(and (forall ((?v6 A_b_prod$ ))(=> (member$b ?v6 (tset$ ?v1 ))(= (fun_app$j ?v2 ?v6 )(fun_app$j ?v3 ?v6 ))))(forall ((?v6 C_d_prod$ ))(=> (member$c ?v6 (set2_tllist$ ?v1 ))(= (fun_app$i ?v4 ?v6 )(fun_app$i ?v5 ?v6 ))))))(= (tmap$c ?v2 ?v4 ?v0 )(tmap$c ?v3 ?v5 ?v1 )))):named a37 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist$ )(?v1 A_b_prod_c_d_prod_tllist$ )(?v2 A_b_prod_a_fun$ )(?v3 A_b_prod_a_fun$ )(?v4 C_d_prod_c_fun$ )(?v5 C_d_prod_c_fun$ ))(=> (and (= ?v0 ?v1 )(and (forall ((?v6 A_b_prod$ ))(=> (member$b ?v6 (tset$ ?v1 ))(= (fun_app$b ?v2 ?v6 )(fun_app$b ?v3 ?v6 ))))(forall ((?v6 C_d_prod$ ))(=> (member$c ?v6 (set2_tllist$ ?v1 ))(= (fun_app$a ?v4 ?v6 )(fun_app$a ?v5 ?v6 ))))))(= (fun_app$p (fun_app$n (tmap$ ?v2 )?v4 )?v0 )(fun_app$p (fun_app$n (tmap$ ?v3 )?v5 )?v1 )))):named a38 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist_a_c_tllist_prod$ )(?v1 A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ ))(=> (forall ((?v2 A_b_prod_c_d_prod_tllist$ )(?v3 A_c_tllist$ ))(=> (= ?v0 (pair$b ?v2 ?v3 ))(fun_app$c (fun_app$d ?v1 ?v2 )?v3 )))(fun_app$t (case_prod$b ?v1 )?v0 ))):named a39 ))
(assert (! (forall ((?v0 A_b_prod$ )(?v1 A_b_bool_fun_fun$ ))(=> (forall ((?v2 A$ )(?v3 B$ ))(=> (= ?v0 (pair$ ?v2 ?v3 ))(fun_app$g (fun_app$h ?v1 ?v2 )?v3 )))(fun_app$u (case_prod$ ?v1 )?v0 ))):named a40 ))
(assert (! (forall ((?v0 C_d_prod$ )(?v1 C_d_bool_fun_fun$ ))(=> (forall ((?v2 C$ )(?v3 D$ ))(=> (= ?v0 (pair$a ?v2 ?v3 ))(fun_app$e (fun_app$f ?v1 ?v2 )?v3 )))(fun_app$v (case_prod$a ?v1 )?v0 ))):named a41 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )(?v1 A_b_prod_c_d_prod_tllist$ )(?v2 A_c_tllist$ ))(=> (fun_app$c (fun_app$d ?v0 ?v1 )?v2 )(fun_app$t (case_prod$b ?v0 )(pair$b ?v1 ?v2 )))):named a42 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A$ )(?v2 B$ ))(=> (fun_app$g (fun_app$h ?v0 ?v1 )?v2 )(fun_app$u (case_prod$ ?v0 )(pair$ ?v1 ?v2 )))):named a43 ))
(assert (! (forall ((?v0 C_d_bool_fun_fun$ )(?v1 C$ )(?v2 D$ ))(=> (fun_app$e (fun_app$f ?v0 ?v1 )?v2 )(fun_app$v (case_prod$a ?v0 )(pair$a ?v1 ?v2 )))):named a44 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )(?v1 A_b_prod_c_d_prod_tllist$ )(?v2 A_c_tllist$ ))(=> (fun_app$c (fun_app$d ?v0 ?v1 )?v2 )(fun_app$t (case_prod$b ?v0 )(pair$b ?v1 ?v2 )))):named a45 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A$ )(?v2 B$ ))(=> (fun_app$g (fun_app$h ?v0 ?v1 )?v2 )(fun_app$u (case_prod$ ?v0 )(pair$ ?v1 ?v2 )))):named a46 ))
(assert (! (forall ((?v0 C_d_bool_fun_fun$ )(?v1 C$ )(?v2 D$ ))(=> (fun_app$e (fun_app$f ?v0 ?v1 )?v2 )(fun_app$v (case_prod$a ?v0 )(pair$a ?v1 ?v2 )))):named a47 ))
(assert (! (forall ((?v0 A_b_prod_llist$ ))(= (lmap$c uuc$ ?v0 )?v0 )):named a48 ))
(assert (! (forall ((?v0 A_llist$ ))(= (lmap$a uue$ ?v0 )?v0 )):named a49 ))
(assert (! (forall ((?v0 Bool )(?v1 A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )(?v2 A_b_prod_c_d_prod_tllist_a_c_tllist_prod$ ))(= (fun_app$t (case_prod$b (uug$ ?v0 ?v1 ))?v2 )(and ?v0 (fun_app$t (case_prod$b ?v1 )?v2 )))):named a50 ))
(assert (! (forall ((?v0 Bool )(?v1 A_b_bool_fun_fun$ )(?v2 A_b_prod$ ))(= (fun_app$u (case_prod$ (uuh$ ?v0 ?v1 ))?v2 )(and ?v0 (fun_app$u (case_prod$ ?v1 )?v2 )))):named a51 ))
(assert (! (forall ((?v0 Bool )(?v1 C_d_bool_fun_fun$ )(?v2 C_d_prod$ ))(= (fun_app$v (case_prod$a (uui$ ?v0 ?v1 ))?v2 )(and ?v0 (fun_app$v (case_prod$a ?v1 )?v2 )))):named a52 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist_a_c_tllist_prod$ )(?v1 A_b_prod_c_d_prod_tllist_set$ )(?v2 A_b_prod_c_d_prod_tllist_a_c_tllist_fun$ ))(=> (member$d ?v0 (collect$c (case_prod$b (grp$ ?v1 ?v2 ))))(member$e (fst$b ?v0 )?v1 ))):named a53 ))
(assert (! (forall ((?v0 A_b_prod$ )(?v1 A_set$ )(?v2 A_b_fun$ ))(=> (member$b ?v0 (collect$ (case_prod$ (grp$a ?v1 ?v2 ))))(member$ (fst$ ?v0 )?v1 ))):named a54 ))
(assert (! (forall ((?v0 C_d_prod$ )(?v1 C_set$ )(?v2 C_d_fun$ ))(=> (member$c ?v0 (collect$a (case_prod$a (grp$b ?v1 ?v2 ))))(member$a (fst$a ?v0 )?v1 ))):named a55 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )(?v1 A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ ))(= (= (conversep$ ?v0 )(conversep$ ?v1 ))(= ?v0 ?v1 ))):named a56 ))
(assert (! (forall ((?v0 A_b_prod_c_d_prod_tllist_a_c_tllist_bool_fun_fun$ )(?v1 A_c_tllist$ )(?v2 A_b_prod_c_d_prod_tllist$ ))(! (= (fun_app$ (fun_app$m (conversep$ ?v0 )?v1 )?v2 )(fun_app$c (fun_app$d ?v0 ?v2 )?v1 )):pattern ((fun_app$ (fun_app$m (conversep$ ?v0 )?v1 )?v2 )))):named a57 ))
(check-sat )
;(get-unsat-core )
