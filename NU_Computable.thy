(*<*)
theory NU_Computable
  imports Nominal_Unification.NU
begin
(*>*)

definition rank_sred where
"rank_sred =
  measures [
    \<lambda>((eprobs, fprobs), s, B). card (vars_eprobs eprobs),
    \<lambda>((eprobs, fprobs), s, B). size_eprobs eprobs,
    \<lambda>((eprobs, fprobs), s, B). size_fprobs fprobs
  ]"


function (sequential) sred_fun :: "(problem_type \<times> substs \<times> bool) \<Rightarrow> (problem_type \<times> substs \<times> bool)" where
 "sred_fun (((Unit \<approx>? Unit) # xs, ys), s, B) = sred_fun ((xs,ys), s, B)" |
 "sred_fun (((Paar t1 t2 \<approx>? Paar s1 s2)#xs,ys), s, B) = sred_fun (((t1\<approx>?s1)#(t2\<approx>?s2)#xs,ys), s, B)" |
 "sred_fun (((Func F t1 \<approx>? Func G t2)#xs,ys), s, B) = (if F = G then
                                                        sred_fun(((t1\<approx>?t2)#xs,ys),s, B)         
                                                       else
                                                        (((Func F t1 \<approx>? Func G t2)#xs,ys), s, False))" |
 "sred_fun (((Abst a t1 \<approx>? Abst b t2)#xs,ys), s, B) = (if a = b then
                                                        sred_fun (((t1\<approx>?t2)#xs,ys), s, B)
                                                       else
                                                        sred_fun (((t1\<approx>?swap [(a,b)] t2)#xs,(a\<sharp>?t2)#ys), s, B))"|
 "sred_fun (((Atom a\<approx>?Atom b)#xs,ys), s, B) = (if a = b then
                                                sred_fun ((xs,ys), s, B)
                                               else
                                                (((Atom a \<approx>? Atom b)#xs,ys), s, False))" |
 "sred_fun (((Susp pi1 X\<approx>?Susp pi2 Y)#xs,ys), s, B) = (if X =Y then 
                                                        sred_fun ((xs,(map (\<lambda>a. a\<sharp>? Susp [] X) (ds_list pi1 pi2))@ys), s, B)
                                                       else
                                                        sred_fun (apply_subst [(X,swap (rev pi1) (Susp pi2 Y))] (xs,ys), [(X,swap (rev pi1) (Susp pi2 Y))] \<bullet> s, B))"|
 "sred_fun (((Susp pi X\<approx>?t)#xs,ys), s, B) = (if \<not> (occurs X t) then
                                              sred_fun (apply_subst [(X,swap (rev pi) t)] (xs,ys), [(X,swap (rev pi) t)] \<bullet> s, B)
                                             else
                                              (((Susp pi X\<approx>?t)#xs,ys), s, False))" |
 "sred_fun (((t\<approx>?Susp pi X)#xs,ys), s, B) = (if \<not> (occurs X t) then
                                              sred_fun (apply_subst [(X,swap (rev pi) t)] (xs,ys), [(X,swap (rev pi) t)] \<bullet> s, B)
                                             else
                                              (((t\<approx>?Susp pi X)#xs,ys), s, False))" |
 "sred_fun (([],ys), s, B) = (([], ys), s, B)" |
 "sred_fun ((e#xs, ys), s, B) = ((e#xs, ys), s, False)" 
  by pat_completeness auto

termination
proof(relation rank_sred, auto)
  show "wf rank_sred" 
    unfolding rank_sred_def by simp

  show "\<And>xs ys s B. (((xs, ys), s, B), ((Unit, Unit) # xs, ys), s, B) \<in> rank_sred"
    unfolding rank_sred_def by simp

  show "\<And>t1 t2 s1 s2 xs ys s B.
       ((((t1, s1) # (t2, s2) # xs, ys), s, B), ((Paar t1 t2, Paar s1 s2) # xs, ys), s, B) \<in> rank_sred"
    unfolding rank_sred_def vars_eprobs.simps size_eprobs.simps size_trm.simps vars_trm.simps
    by (simp add: Un_commute Un_left_commute)

  show "\<And>t1 G t2 xs ys s B.
       ((((t1, t2) # xs, ys), s, B), ((trm.Func G t1, trm.Func G t2) # xs, ys), s, B)
       \<in> rank_sred"
    unfolding rank_sred_def vars_eprobs.simps size_eprobs.simps size_trm.simps vars_trm.simps
    by simp

  show  "\<And>t1 b t2 xs ys s B.
       ((((t1, t2) # xs, ys), s, B), ((Abst b t1, Abst b t2) # xs, ys), s, B) \<in> rank_sred"
   unfolding rank_sred_def vars_eprobs.simps size_eprobs.simps size_trm.simps vars_trm.simps
   by simp

  show "\<And>a t1 b t2 xs ys s B.
       a \<noteq> b \<Longrightarrow>
       ((((t1, swap [(a, b)] t2) # xs, (a, t2) # ys), s, B), ((Abst a t1, Abst b t2) # xs, ys),
        s, B)
       \<in> rank_sred"
    sorry

  show "\<And>b xs ys s B. (((xs, ys), s, B), ((Atom b, Atom b) # xs, ys), s, B) \<in> rank_sred"
    unfolding rank_sred_def vars_eprobs.simps size_eprobs.simps size_trm.simps vars_trm.simps 
    by simp


  
qed






(*<*)
end
(*>*)