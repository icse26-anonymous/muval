;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort C$ 0 )
(declare-sort A_b_sp_nu$ 0 )
(declare-sort A_c_sp_nu$ 0 )
(declare-sort C_b_sp_nu$ 0 )
(declare-codatatypes ()((B_stream$ (sCons$ (shd$ B$ )(stl$ B_stream$ )))(A_stream$ (sCons$a (shd$a A$ )(stl$a A_stream$ )))(C_stream$ (sCons$b (shd$b C$ )(stl$b C_stream$ )))))
(declare-fun s$ ()A_stream$ )
(declare-fun sp$ ()C_b_sp_nu$ )
(declare-fun sp$a ()A_c_sp_nu$ )
(declare-fun run_nu$ (A_b_sp_nu$ A_stream$ )B_stream$ )
(declare-fun run_nu$a (C_b_sp_nu$ C_stream$ )B_stream$ )
(declare-fun run_nu$b (A_c_sp_nu$ A_stream$ )C_stream$ )
(declare-fun sp_nu_comp$ (C_b_sp_nu$ A_c_sp_nu$ )A_b_sp_nu$ )
(assert (! (not (= (run_nu$ (sp_nu_comp$ sp$ sp$a )s$ )(run_nu$a sp$ (run_nu$b sp$a s$ )))):named a0 ))
(check-sat )
;(get-unsat-core )
