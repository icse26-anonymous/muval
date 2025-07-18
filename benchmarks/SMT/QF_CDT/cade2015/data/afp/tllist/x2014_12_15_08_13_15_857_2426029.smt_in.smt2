;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_b_tllist$ 0)
(declare-sort A_llist$ 0)
(declare-fun terminal$ (A_b_tllist$)B$)
(declare-fun tNil$ (B$ )A_b_tllist$)
(declare-fun thd$ (A_b_tllist$)A$)
(declare-fun ttl$ (A_b_tllist$)A_b_tllist$)
(declare-fun tCons$ (A$ A_b_tllist$ )A_b_tllist$)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((Nat_option$ (none$ )(some$ (the$ Nat$ )))(Enat$ (abs_enat$ (rep_enat$ Nat_option$ )))))
(declare-fun a$ ()B$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun zs$ ()A_b_tllist$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun lfilter$ (A_bool_fun$ A_llist$ )A_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(declare-fun lappendt$ (A_llist$ A_b_tllist$ )A_b_tllist$ )
(declare-fun llist_of_tllist$ (A_b_tllist$ )A_llist$ )
(declare-fun tllist_of_llist$ (B$ A_llist$ )A_b_tllist$ )
(assert (! (not (= (= (tllist_of_llist$ a$ xs$ )(lappendt$ ys$ zs$ ))(exists ((?v0 A_llist$ )(?v1 B$ ))(and (= xs$ (lappend$ ys$ ?v0 ))(and (= zs$ (tllist_of_llist$ ?v1 ?v0 ))(=> (lfinite$ ys$ )(= a$ ?v1 ))))))):named a0 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ )(?v2 B$ )(?v3 A_llist$ ))(= (= (tllist_of_llist$ ?v0 ?v1 )(tllist_of_llist$ ?v2 ?v3 ))(and (= ?v1 ?v3 )(=> (lfinite$ ?v3 )(= ?v0 ?v2 ))))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 B$ )(?v3 B$ ))(=> (and (= ?v0 ?v1 )(=> (lfinite$ ?v1 )(= ?v2 ?v3 )))(= (tllist_of_llist$ ?v2 ?v0 )(tllist_of_llist$ ?v3 ?v1 )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (lappend$ ?v0 ?v1 ))(and (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (not (lfinite$ ?v0 ))(= (lappend$ ?v0 ?v1 )?v0 )):pattern ((lappend$ ?v0 ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_b_tllist$ ))(=> (lfinite$ ?v0 )(= (terminal$ (lappendt$ ?v0 ?v1 ))(terminal$ ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ ))(=> (lfinite$ ?v0 )(= (terminal$ (tllist_of_llist$ ?v1 ?v0 ))?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(! (= (lappendt$ lNil$ ?v0 )?v0 ):pattern ((lappendt$ lNil$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 B$ )(?v1 A_llist$ ))(= (llist_of_tllist$ (tllist_of_llist$ ?v0 ?v1 ))?v1 )):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lprefix$ (lappend$ ?v0 ?v1 )(lappend$ ?v0 ?v2 ))(=> (lfinite$ ?v0 )(lprefix$ ?v1 ?v2 )))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_bool_fun$ )(?v2 A_llist$ ))(=> (lfinite$ ?v0 )(= (lfilter$ ?v1 (lappend$ ?v0 ?v2 ))(lappend$ (lfilter$ ?v1 ?v0 )(lfilter$ ?v1 ?v2 ))))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (= (llength$ ?v0 )(llength$ ?v1 ))(= (= (lappend$ ?v0 ?v2 )(lappend$ ?v1 ?v3 ))(and (= ?v0 ?v1 )(=> (lfinite$ ?v0 )(= ?v2 ?v3 )))))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (member$ ?v0 (lset$ (lappend$ ?v1 ?v2 )))(or (member$ ?v0 (lset$ ?v1 ))(and (lfinite$ ?v1 )(member$ ?v0 (lset$ ?v2 )))))):named a13 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (and (= (lfilter$ ?v0 ?v1 )(lappend$ ?v2 ?v3 ))(lfinite$ ?v2 ))(exists ((?v4 A_llist$ )(?v5 A_llist$ ))(and (= ?v1 (lappend$ ?v4 ?v5 ))(and (lfinite$ ?v4 )(and (= ?v2 (lfilter$ ?v0 ?v4 ))(= ?v3 (lfilter$ ?v0 ?v5 )))))))):named a14 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a15 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a16 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (lfilter$ ?v0 (lfilter$ ?v0 ?v1 ))(lfilter$ ?v0 ?v1 ))):named a17 ))
(check-sat )
;(get-unsat-core )
