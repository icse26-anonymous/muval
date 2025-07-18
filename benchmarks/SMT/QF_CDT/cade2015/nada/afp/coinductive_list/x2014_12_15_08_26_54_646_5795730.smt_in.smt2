;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort B_set$ 0 )
(declare-sort B_a_fun$ 0 )
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
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-sort B_list$ 0)
(declare-sort A_list$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun nil$ ()B_list$)
(declare-fun hd$ (B_list$)B$)
(declare-fun tl$ (B_list$)B_list$)
(declare-fun cons$ (B$ B_list$ )B_list$)
(declare-fun nil$a ()A_list$)
(declare-fun hd$a (A_list$)A$)
(declare-fun tl$a (A_list$)A_list$)
(declare-fun cons$a (A$ A_list$ )A_list$)
(declare-fun f$ ()B_a_fun$ )
(declare-fun xs$ ()B_llist$ )
(declare-fun lmap$ (B_a_fun$ B_llist$ )A_llist$ )
(declare-fun lset$ (B_llist$ )B_set$ )
(declare-fun ldrop$ (Enat$ B_llist$ )B_llist$ )
(declare-fun lset$a (A_llist$ )A_set$ )
(declare-fun ltake$ (Enat$ B_llist$ )B_llist$ )
(declare-fun ldrop$a (Enat$ A_llist$ )A_llist$ )
(declare-fun ldropn$ (Nat$ B_llist$ )B_llist$ )
(declare-fun ltake$a (Enat$ A_llist$ )A_llist$ )
(declare-fun member$ (B$ B_set$ )Bool )
(declare-fun ldropn$a (Nat$ A_llist$ )A_llist$ )
(declare-fun lprefix$ (B_llist$ B_llist$ )Bool )
(declare-fun member$a (A$ A_set$ )Bool )
(declare-fun distinct$ (B_list$ )Bool )
(declare-fun llist_of$ (B_list$ )B_llist$ )
(declare-fun lprefix$a (A_llist$ A_llist$ )Bool )
(declare-fun distinct$a (A_list$ )Bool )
(declare-fun ldistinct$ (B_llist$ )Bool )
(declare-fun llist_of$a (A_list$ )A_llist$ )
(declare-fun ldistinct$a (A_llist$ )Bool )
(assert (! (not (ldistinct$ xs$ )):named a0 ))
(assert (! (ldistinct$a (lmap$ f$ xs$ )):named a1 ))
(assert (! (= (ldistinct$ lNil$ )true ):named a2 ))
(assert (! (= (ldistinct$a lNil$a )true ):named a3 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 Nat$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ldropn$ ?v1 ?v0 )))):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ ))(=> (ldistinct$a ?v0 )(ldistinct$a (ldropn$a ?v1 ?v0 )))):named a5 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 Enat$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ldrop$ ?v1 ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Enat$ ))(=> (ldistinct$a ?v0 )(ldistinct$a (ldrop$a ?v1 ?v0 )))):named a7 ))
(assert (! (ldistinct$ lNil$ ):named a8 ))
(assert (! (ldistinct$a lNil$a ):named a9 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(=> (and (ldistinct$ ?v0 )(lprefix$ ?v1 ?v0 ))(ldistinct$ ?v1 ))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (ldistinct$a ?v0 )(lprefix$a ?v1 ?v0 ))(ldistinct$a ?v1 ))):named a11 ))
(assert (! (forall ((?v0 B_llist$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ltl$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (ldistinct$a ?v0 )(ldistinct$a (ltl$a ?v0 )))):named a13 ))
(assert (! (forall ((?v0 B_llist$ )(?v1 Enat$ ))(=> (ldistinct$ ?v0 )(ldistinct$ (ltake$ ?v1 ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Enat$ ))(=> (ldistinct$a ?v0 )(ldistinct$a (ltake$a ?v1 ?v0 )))):named a15 ))
(assert (! (forall ((?v0 B_list$ ))(= (ldistinct$ (llist_of$ ?v0 ))(distinct$ ?v0 ))):named a16 ))
(assert (! (forall ((?v0 A_list$ ))(= (ldistinct$a (llist_of$a ?v0 ))(distinct$a ?v0 ))):named a17 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ ))(! (= (ldistinct$ (lCons$ ?v0 ?v1 ))(and (not (member$ ?v0 (lset$ ?v1 )))(ldistinct$ ?v1 ))):pattern ((lCons$ ?v0 ?v1 )))):named a18 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (ldistinct$a (lCons$a ?v0 ?v1 ))(and (not (member$a ?v0 (lset$a ?v1 )))(ldistinct$a ?v1 ))):pattern ((lCons$a ?v0 ?v1 )))):named a19 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ ))(=> (and (not (member$ ?v0 (lset$ ?v1 )))(ldistinct$ ?v1 ))(ldistinct$ (lCons$ ?v0 ?v1 )))):named a20 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (and (not (member$a ?v0 (lset$a ?v1 )))(ldistinct$a ?v1 ))(ldistinct$a (lCons$a ?v0 ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$a ?v0 ?v0 )):named a22 ))
(assert (! (forall ((?v0 B_llist$ ))(lprefix$ ?v0 ?v0 )):named a23 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$a ?v0 ?v0 )):named a24 ))
(assert (! (forall ((?v0 B_llist$ ))(lprefix$ ?v0 ?v0 )):named a25 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a26 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ )(?v2 B$ )(?v3 B_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a27 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$a ?v0 )(llist_of$a ?v1 ))(= ?v0 ?v1 ))):named a28 ))
(assert (! (forall ((?v0 B_list$ )(?v1 B_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a29 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (lprefix$a (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(lprefix$a ?v1 ?v3 ))):pattern ((lprefix$a (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))))):named a30 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ )(?v2 B$ )(?v3 B_llist$ ))(! (= (lprefix$ (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(lprefix$ ?v1 ?v3 ))):pattern ((lprefix$ (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))))):named a31 ))
(check-sat )
;(get-unsat-core )
